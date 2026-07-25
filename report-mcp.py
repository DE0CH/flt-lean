#!/usr/bin/env python3
"""Minimal MCP server: diagnostics + build, talking directly to one
flt-report-server instance's FIFOs (Deyao 2026-07-23: "just make mcp
accept an argument about where the server socket is, then start 13
servers in .mcp").

One process per worktree, selected via --socket-dir (the instance's
.report-server directory, holding req.fifo/resp.fifo/lock/state.json —
the argument IS the routing, not a project path to derive it from);
.mcp.json wires one server entry per worktree onto the matching
flt-report-server@<name> instance. The project path (for `build`'s cwd
and for resolving relative file_path args) is just --socket-dir's
parent directory.
"""
import argparse
import fcntl
import hashlib
import json
import os
import select
import subprocess
import sys
import time


class PipeLsp:
    """Content-Length-framed JSON-RPC over a flt-report-server instance's
    FIFOs (see flt-report-server@.service for the protocol contract: the
    server holds both FIFO ends O_RDWR, so client open/close never EOFs
    or SIGPIPEs it). One persistent connection held for this MCP server
    process's lifetime; each call flocks .report-server/lock so a second
    concurrent client on the same instance can't interleave on the byte
    stream.
    """

    def __init__(self, socket_dir):
        self.dir = socket_dir
        self.project_path = os.path.dirname(socket_dir)
        self.req_fifo = os.path.join(self.dir, "req.fifo")
        self.resp_fifo = os.path.join(self.dir, "resp.fifo")
        self.lock_file = os.path.join(self.dir, "lock")
        self.state_file = os.path.join(self.dir, "state.json")
        self.wfd = None
        self.rfd = None
        self.buf = b""
        self.req_seq = 0
        self.diags = {}
        # URIs for which THIS process actually received a
        # publishDiagnostics notification. `diags` alone cannot be trusted
        # as "clean": see the guard at the end of `diagnostics`.
        self.published = set()
        # uri -> content hash the ADOPTED (persisted) diagnostics belong to,
        # so an inherited payload is only trusted for the content it was
        # actually produced from.
        self.published_hashes = {}
        self.doc_versions = {}
        self.doc_hashes = {}
        self.initialized = False
        # identity of the server SESSION we last talked to, as the
        # (inode, mtime_ns) of state.json — see _ensure_initialized
        self.session_stat = None

    def _connect(self):
        if self.wfd is not None:
            return
        try:
            self.wfd = os.open(self.req_fifo, os.O_WRONLY | os.O_NONBLOCK)
        except OSError as exc:
            raise RuntimeError(
                f"flt-report-server not running for {self.project_path} "
                f"(systemctl --user start flt-report-server@<name>): {exc}"
            ) from exc
        os.set_blocking(self.wfd, True)
        self.rfd = os.open(self.resp_fifo, os.O_RDONLY)

    def _send(self, obj):
        data = json.dumps(obj).encode()
        msg = b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data
        while msg:
            n = os.write(self.wfd, msg)
            msg = msg[n:]

    def _dispatch(self, msg):
        method = msg.get("method")
        if method == "textDocument/publishDiagnostics":
            p = msg["params"]
            self.diags[p["uri"]] = p["diagnostics"]
            self.published.add(p["uri"])
        elif method is not None and "id" in msg:
            # server->client request (e.g. client/registerCapability) —
            # a minimal client answers null.
            self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})

    def _notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def _fill(self, deadline):
        wait = deadline - time.time()
        if wait <= 0:
            raise RuntimeError("report server did not respond in time")
        r, _, _ = select.select([self.rfd], [], [], wait)
        if not r:
            raise RuntimeError("report server did not respond in time")
        chunk = os.read(self.rfd, 1 << 16)
        if chunk == b"":
            raise RuntimeError("report server response pipe EOF")
        self.buf += chunk

    def _resync(self, deadline):
        """Drop stream garbage up to the next header marker. A client
        killed mid-call (session fork/limit kill) can leave a partial
        response frame in resp.fifo; the next reader would otherwise
        parse from mid-frame and wedge every later call. Responses with
        foreign request ids are already tolerated by _request's loop —
        this handles the byte-level half."""
        marker = b"Content-Length:"
        idx = self.buf.find(marker, 1)
        if idx == -1:
            self.buf = self.buf[-(len(marker) - 1):] if self.buf else b""
            self._fill(deadline)
        else:
            self.buf = self.buf[idx:]

    def _read_msg(self, deadline):
        while True:
            while b"\r\n\r\n" not in self.buf:
                self._fill(deadline)
            head, _, rest = self.buf.partition(b"\r\n\r\n")
            length = None
            for line in head.decode("ascii", "replace").split("\r\n"):
                if line.lower().startswith("content-length:"):
                    length = int(line.split(":", 1)[1].strip())
            if length is None:
                self._resync(deadline)
                continue
            self.buf = rest
            while len(self.buf) < length:
                self._fill(deadline)
            body, self.buf = self.buf[:length], self.buf[length:]
            try:
                return json.loads(body)
            except ValueError:
                # length lied (mid-body desync) — recover the same way
                self.buf = body + self.buf
                self._resync(deadline)

    def _request(self, method, params, timeout):
        self.req_seq += 1
        rid = f"{os.getpid()}.{self.req_seq}"
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        deadline = time.time() + timeout
        while True:
            msg = self._read_msg(deadline)
            self._dispatch(msg)
            if msg.get("id") == rid and "method" not in msg:
                if "error" in msg:
                    raise RuntimeError(f"report server: {method}: {msg['error']}")
                return msg.get("result")

    def _session_marker(self):
        """Identity of the server session = the INODE of state.json.

        Deliberately not the mtime: the file now also carries the shared
        open-document map (see _load_docs), so it is rewritten during
        normal operation, and an mtime-based identity would read every
        write as a server restart and drop the map. The unit's
        ExecStartPre `rm -f`s the file on every (re)start, so a new
        inode is exactly "the server restarted"."""
        try:
            st = os.stat(self.state_file)
            return (st.st_dev, st.st_ino)
        except FileNotFoundError:
            return None

    def _load_docs(self):
        """Adopt the open-document map recorded by whichever client
        opened these files in THIS server session.

        Why this exists (the 2026-07-25 collapse): `doc_versions` used to
        be per-PROCESS. Every orchestrator restart kills the client, and
        the fresh one saw version 0 for a file the server still had open
        — so it sent a second `didOpen`, and lake serve started a SECOND
        `lean --worker` for that file while the first kept running,
        undisturbed because nobody ever closed the document. Four session
        restarts left four rival elaborations of one file, each rebuilding
        the same olean and starving the others; the fleet reached 81
        concurrent `lake setup-file` builds. Sharing the map through
        state.json means a restarted client re-issues
        `waitForDiagnostics` against the version already in flight —
        attaching to the running elaboration instead of racing it."""
        try:
            with open(self.state_file, encoding="utf-8") as fh:
                docs = (json.load(fh) or {}).get("docs") or {}
        except (OSError, ValueError):
            return
        for uri, rec in docs.items():
            self.doc_versions.setdefault(uri, rec.get("version", 0))
            self.doc_hashes.setdefault(uri, rec.get("hash"))
            # Adopt the last published diagnostics too, not just the version.
            #
            # `publishDiagnostics` is a one-shot notification to whichever
            # client was attached when the server produced it. Without this,
            # a fresh client that attaches to an already-elaborated document
            # has an empty table and cannot tell "clean" from "never heard" —
            # which produced a false clean on a file with six sorries
            # (2026-07-25, reported independently by two agents). Persisting
            # the payload lets the attaching client return the REAL answer
            # instead of forcing a content edit to re-provoke a publish.
            #
            # Trust it only when the recorded hash matches what we are about
            # to elaborate; `diagnostics` re-checks this against the file it
            # just read before using the adopted value.
            if "diags" in rec:
                self.diags.setdefault(uri, rec["diags"])
                self.published_hashes[uri] = rec.get("hash")

    def _save_docs(self):
        """Persist the open-document map, preserving the init marker."""
        docs = {
            uri: {
                "version": v,
                "hash": self.doc_hashes.get(uri),
                **({"diags": self.diags[uri]} if uri in self.diags else {}),
            }
            for uri, v in self.doc_versions.items()
        }
        try:
            with open(self.state_file, "w", encoding="utf-8") as fh:
                json.dump({"report_mcp_initialized": True, "docs": docs}, fh)
        except OSError:
            return
        # keep our own session identity in step: the inode is unchanged by
        # a rewrite, but refresh anyway so a first write after init matches
        self.session_stat = self._session_marker()

    def _ensure_initialized(self, timeout):
        """Handshake is per SERVER SESSION, not per client process: the
        unit's ExecStartPre clears .report-server/state.json on every
        (re)start, so its presence means some earlier client (this
        process, another report-mcp.py instance, or progress-tree.py)
        already sent `initialize` — sending it twice errors ("No request
        handler found for 'initialize'"), lake serve accepts it once.

        The session identity is the (inode, mtime) of state.json, NOT a
        flag in this process: a long-running client that cached
        `initialized`/`doc_versions` across a server restart would send
        `didChange`/`waitForDiagnostics` for documents the fresh session
        never saw — the watchdog kills the server on the first such
        message and systemd crash-loops it (observed 2026-07-24 after
        the disk-quota restart). Whenever the marker is missing or
        differs from the one we last saw, ALL per-session client state
        is stale and must be reset. Must be called with self.lock_file
        already held (the check-then-initialize below is serialized by
        that lock across client processes)."""
        marker = self._session_marker()
        if marker is None or marker != self.session_stat:
            self.initialized = False
            self.doc_versions.clear()
            self.doc_hashes.clear()
            self.diags.clear()
            # the fifo fds may point at the dead server's pipes
            # ("response pipe EOF") — reopen against the new session
            if self.wfd is not None:
                for fd in (self.wfd, self.rfd):
                    try:
                        os.close(fd)
                    except OSError:
                        pass
                self.wfd = None
                self.rfd = None
                self.buf = b""
            self._connect()
        if marker is None:
            self._request(
                "initialize",
                {
                    "processId": os.getpid(),
                    "rootUri": "file://" + self.project_path,
                    "capabilities": {},
                    "trace": "off",
                },
                timeout,
            )
            self._notify("initialized", {})
            with open(self.state_file, "w", encoding="utf-8") as fh:
                json.dump({"report_mcp_initialized": True}, fh)
        self.session_stat = self._session_marker()
        self.initialized = True

    def diagnostics(self, abs_path, timeout=1800):
        """Sync `abs_path` with disk content and return diagnostics via
        lake serve's `textDocument/waitForDiagnostics` request, which
        blocks server-side until the given version has fully elaborated
        (no polling/settle heuristics needed).

        Retry-safety: a retried call with UNCHANGED on-disk content must
        NOT bump the document version — every didChange starts a fresh
        elaboration worker, so timeout-retry-polling on a slow file used
        to pile up concurrent multi-GB workers (observed 2026-07-24 on a
        ~21-min ModThree elaboration against the old 180 s default). An
        unchanged retry now re-issues waitForDiagnostics for the version
        already in flight, which is idempotent server-side."""
        uri = "file://" + abs_path
        with open(self.lock_file, "a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            self._connect()
            self._ensure_initialized(timeout)

            # adopt any document state left by a previous client process in
            # this same server session, so a restart attaches instead of
            # opening a rival copy of the file
            self._load_docs()

            text = open(abs_path, encoding="utf-8").read()
            content_hash = hashlib.sha256(text.encode()).hexdigest()
            version = self.doc_versions.get(uri, 0)
            if version == 0:
                version = 1
                self.doc_versions[uri] = version
                self.doc_hashes[uri] = content_hash
                self.diags.pop(uri, None)
                # belt-and-braces: if the shared map was lost but the server
                # still holds this document open, didClose retires that
                # worker so didOpen cannot produce a second one. Harmless
                # when the document is not open.
                self._notify(
                    "textDocument/didClose",
                    {"textDocument": {"uri": uri}},
                )
                self._notify(
                    "textDocument/didOpen",
                    {
                        "textDocument": {
                            "uri": uri,
                            "languageId": "lean4",
                            "version": version,
                            "text": text,
                        }
                    },
                )
            elif self.doc_hashes.get(uri) != content_hash:
                version += 1
                self.doc_versions[uri] = version
                self.doc_hashes[uri] = content_hash
                self.diags.pop(uri, None)
                self._notify(
                    "textDocument/didChange",
                    {
                        "textDocument": {"uri": uri, "version": version},
                        "contentChanges": [{"text": text}],
                    },
                )
            # unchanged content: keep the in-flight version, no notify

            self._save_docs()
            self._request(
                "textDocument/waitForDiagnostics",
                {"uri": uri, "version": version},
                timeout,
            )
            # Persist AGAIN now that the publish has arrived: the first save
            # runs before `waitForDiagnostics` and so cannot contain the
            # payload. This second write is what lets the next client process
            # in this server session return a real answer instead of an
            # unheard-empty one.
            if uri in self.published:
                self.published_hashes[uri] = self.doc_hashes.get(uri)
                self._save_docs()
            # FALSE-CLEAN GUARD (2026-07-25, after an agent was told a file
            # with five sorries had zero diagnostics).
            #
            # `publishDiagnostics` is a NOTIFICATION, delivered once, to
            # whichever client connection was attached at the time. When a
            # fresh client adopts an already-open document from the shared
            # map and the content is unchanged, no notify is sent and
            # `waitForDiagnostics` returns immediately — the version is long
            # since elaborated. But this process never heard the publish, so
            # `self.diags[uri]` is empty. Returning that empty list reads as
            # "compiles clean", which is the single most dangerous thing this
            # tool can say.
            #
            # An empty result is therefore only trustworthy if we actually
            # received a publish for this URI. Otherwise report UNKNOWN and
            # say how to force a real answer. We deliberately do NOT
            # self-heal by bumping the version: that would re-elaborate the
            # file on every client restart, i.e. 60+ concurrent rebuilds of
            # the largest modules in the fleet — the exact thundering herd
            # the shared map exists to prevent.
            if uri not in self.published and self.published_hashes.get(uri) == content_hash:
                # We did not hear the publish ourselves, but an earlier client
                # in this server session persisted the diagnostics it heard,
                # AND they were produced from exactly the content we just
                # elaborated. That is a real answer, not a guess.
                return {
                    "diagnostics": self.diags.get(uri, []),
                    "verified": True,
                    "source": "adopted from this server session's persisted publish",
                }
            if uri not in self.published:
                return {
                    "diagnostics": [],
                    "verified": False,
                    "reason": (
                        "UNKNOWN, not clean: this client process attached to a "
                        "document that was already open and fully elaborated in "
                        "this server session, so the diagnostics notification "
                        "was delivered to an earlier client and cannot be "
                        "replayed. An empty list here does NOT mean the file "
                        "compiles. To get a real answer, make an actual content "
                        "change (even adding a docstring line) and call again — "
                        "only new content starts new work and produces a fresh "
                        "publish."
                    ),
                }
            return {"diagnostics": self.diags.get(uri, []), "verified": True}


def build_mcp(socket_dir):
    from mcp.server.fastmcp import FastMCP

    project_path = os.path.dirname(socket_dir)
    mcp = FastMCP(f"report-lsp-{os.path.basename(project_path)}")
    lsp = PipeLsp(socket_dir)

    @mcp.tool()
    def diagnostics(file_path: str, timeout_seconds: int = 1800) -> dict:
        """Compiler diagnostics (errors/warnings/infos) for a Lean file in
        this worktree, via the resident flt-report-server instance. Pass
        an absolute path or one relative to this worktree's root.

        BLOCKS until the file's current on-disk version is fully
        elaborated. Big files genuinely take tens of minutes (ModThree is
        ~30k lines), and a cold `.lake` makes the first call rebuild the
        whole import cone — hours, not minutes. WAIT for it; do not poll,
        do not re-fire in parallel, and treat a client-side timeout as
        "still elaborating", because the server keeps working after the
        client gives up. Re-issuing after a timeout is safe and cheap: it
        attaches to the elaboration already in flight (shared per server
        session, so even a client restart attaches rather than starting a
        second one) and never restarts it. Only an actual content change
        starts new work.

        CHECK `verified`. `verified: true` means this call actually received
        the compiler's diagnostics, so an empty list really does mean the
        file is clean. `verified: false` means UNKNOWN — the document was
        already elaborated in this server session and the notification went
        to an earlier client, so an empty list proves nothing. In that case
        make a real content change and call again; do not record a
        `verified: false` result as a successful verification."""
        abs_path = (
            file_path
            if os.path.isabs(file_path)
            else os.path.abspath(os.path.join(project_path, file_path))
        )
        if not os.path.exists(abs_path):
            raise ValueError(f"file not found: {abs_path}")
        result = lsp.diagnostics(abs_path, timeout=timeout_seconds)
        return {"file_path": abs_path, **result}

    @mcp.tool()
    def build(clean: bool = False) -> dict:
        """Run `lake build` in this worktree. Slow — only when new imports
        are needed; diagnostics is the normal verification gate."""
        if clean:
            subprocess.run(["lake", "clean"], cwd=project_path, check=False)
        proc = subprocess.run(
            ["lake", "build"], cwd=project_path, capture_output=True, text=True
        )
        return {
            "returncode": proc.returncode,
            "stdout_tail": "\n".join(proc.stdout.splitlines()[-40:]),
            "stderr_tail": "\n".join(proc.stderr.splitlines()[-40:]),
        }

    return mcp


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--socket-dir",
        required=True,
        help="the flt-report-server instance's .report-server directory "
        "(holds req.fifo/resp.fifo/lock/state.json)",
    )
    args = ap.parse_args()
    build_mcp(os.path.abspath(args.socket_dir)).run()
