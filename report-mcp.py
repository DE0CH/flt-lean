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
        self.doc_versions = {}
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

    def _read_msg(self, deadline):
        while b"\r\n\r\n" not in self.buf:
            self._fill(deadline)
        head, _, self.buf = self.buf.partition(b"\r\n\r\n")
        length = None
        for line in head.decode("ascii", "replace").split("\r\n"):
            if line.lower().startswith("content-length:"):
                length = int(line.split(":", 1)[1].strip())
        if length is None:
            raise RuntimeError(f"malformed LSP header from report server: {head!r}")
        while len(self.buf) < length:
            self._fill(deadline)
        body, self.buf = self.buf[:length], self.buf[length:]
        return json.loads(body)

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
        try:
            st = os.stat(self.state_file)
            return (st.st_ino, st.st_mtime_ns)
        except FileNotFoundError:
            return None

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

    def diagnostics(self, abs_path, timeout=180):
        """Sync `abs_path` with disk content and return diagnostics via
        lake serve's `textDocument/waitForDiagnostics` request, which
        blocks server-side until the given version has fully elaborated
        (no polling/settle heuristics needed)."""
        uri = "file://" + abs_path
        with open(self.lock_file, "a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            self._connect()
            self._ensure_initialized(timeout)

            text = open(abs_path, encoding="utf-8").read()
            self.diags.pop(uri, None)
            version = self.doc_versions.get(uri, 0) + 1
            self.doc_versions[uri] = version
            if version == 1:
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
            else:
                self._notify(
                    "textDocument/didChange",
                    {
                        "textDocument": {"uri": uri, "version": version},
                        "contentChanges": [{"text": text}],
                    },
                )

            self._request(
                "textDocument/waitForDiagnostics",
                {"uri": uri, "version": version},
                timeout,
            )
            return self.diags.get(uri, [])


def build_mcp(socket_dir):
    from mcp.server.fastmcp import FastMCP

    project_path = os.path.dirname(socket_dir)
    mcp = FastMCP(f"report-lsp-{os.path.basename(project_path)}")
    lsp = PipeLsp(socket_dir)

    @mcp.tool()
    def diagnostics(file_path: str) -> dict:
        """Compiler diagnostics (errors/warnings/infos) for a Lean file in
        this worktree, via the resident flt-report-server instance. Pass
        an absolute path or one relative to this worktree's root."""
        abs_path = (
            file_path
            if os.path.isabs(file_path)
            else os.path.abspath(os.path.join(project_path, file_path))
        )
        if not os.path.exists(abs_path):
            raise ValueError(f"file not found: {abs_path}")
        return {"file_path": abs_path, "diagnostics": lsp.diagnostics(abs_path)}

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
