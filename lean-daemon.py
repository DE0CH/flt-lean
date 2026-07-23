#!/usr/bin/env python3
"""Thin LSP-client server for the FLT progress tooling.

The report backend is the LEAN LANGUAGE SERVER (Deyao, 2026-07-22,
final design): this process keeps ONE `lake serve` child alive and
speaks LSP (JSON-RPC over stdio) to it — exactly what the lean-lsp-mcp
bridge does, minus the MCP. Per query it (re)opens the census file
`ProgressCensus.lean` (whose generated header imports every tracked
module and whose `#eval` prints the whole census as one JSON object),
waits for elaboration, and returns the JSON that arrives as the
`#eval`'s info diagnostic. The socket interface below is unchanged —
the hook and progress-tree.py keep their query API.

  python3 lean-daemon.py --serve            # run the daemon (foreground)
  python3 lean-daemon.py --query '<json>'   # one query (autostarts daemon)
  python3 lean-daemon.py --stop             # shut the daemon down

Queries: {"cmd": "report", "names": [...]} and {"cmd": "sorries"} both
run the same census (names default to []); the response is the census
JSON verbatim — {"entries": [...], "sorried": [...], "root": {...}} —
so a "report" response also carries the sorried list and root status
(progress-tree.py uses that to make one query per generation).

DIVISION OF LABOR (Deyao's standing directives, absolute):
  * NOTHING here touches olean files or anything under .lake — no
    mtimes, no signatures, no existence checks, no lake subprocesses.
    Building and invalidation belong to the language server: on each
    query the census file is didClose'd and didOpen'd afresh, which
    makes the watchdog re-run the file's setup (rebuilding stale
    imports itself) and re-elaborate against the current dependency
    state.
  * NO fallbacks, NO self-recovery: if elaboration reports errors (a
    tracked module does not compile, the census file is broken, the
    setup failed), the query returns {"error": <the compiler's error
    text>} — the generator then crashes loudly with it, the Stop hook
    fails open. The only "recovery" is lazy respawn: a dead `lake
    serve` child (crash, kill -9) is respawned on the next query.
  * The broad except blocks in handle()/serve() are protocol ERROR
    TRANSPORT only — they forward the real exception text to the
    caller; they never substitute partial data.

The client is HAND-ROLLED (~100 lines): the `leanclient` package the
MCP bridge builds on is not installed in this environment, and our
flow needs exactly four verbs (initialize, didOpen, didClose,
waitForDiagnostics) — vendoring a package for that is more moving
parts than the protocol code itself.
"""

import importlib.util
import json
import os
import socket
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
SOCK = os.path.join(ROOT, ".lean-daemon.sock")
LOG = os.path.join(ROOT, ".lean-daemon.log")
CENSUS_LEAN = os.path.join(ROOT, "ProgressCensus.lean")
CENSUS_URI = "file://" + CENSUS_LEAN
LSP_STDERR = os.path.join(ROOT, ".lean-daemon-lsp-stderr")


def _progress_tree():
    """Import the (import-safe) progress-tree.py module for its census
    header/input helpers — single source of truth for both routes."""
    spec = importlib.util.spec_from_file_location(
        "progress_tree", os.path.join(ROOT, "progress-tree.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------- LSP client


class LspClient:
    """Minimal JSON-RPC/LSP client over one `lake serve` child."""

    def __init__(self, logfn):
        self._log = logfn
        self.proc = None
        self.req_id = 0
        self.version = 0
        self.opened = False
        self.diags = {}   # uri -> latest published diagnostics

    def alive(self):
        return self.proc is not None and self.proc.poll() is None

    def start(self):
        errfh = open(LSP_STDERR, "a", encoding="utf-8")
        self.proc = subprocess.Popen(
            ["lake", "serve"], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errfh)
        self.req_id = 0
        self.opened = False
        self.diags = {}
        t0 = time.time()
        self._request("initialize", {
            "processId": os.getpid(),
            "rootUri": "file://" + ROOT,
            "capabilities": {},
        })
        self._notify("initialized", {})
        self._log(f"lake serve up (initialize in {time.time() - t0:.1f}s, "
                  f"pid {self.proc.pid})")

    def stop(self):
        if self.proc is not None:
            try:
                self.proc.kill()
            except Exception:
                pass
            try:
                self.proc.wait(timeout=10)
            except Exception:
                pass
        self.proc = None
        self.opened = False

    # ---- wire

    def _send(self, obj):
        data = json.dumps(obj).encode()
        self.proc.stdin.write(
            b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n"
            + data)
        self.proc.stdin.flush()

    def _read_msg(self):
        """One framed message from the server (blocking); raises if the
        child died."""
        headers = b""
        while not headers.endswith(b"\r\n\r\n"):
            c = self.proc.stdout.read(1)
            if c == b"":
                raise RuntimeError(
                    "lake serve closed its stdout (crashed or killed)")
            headers += c
        length = None
        for line in headers.decode("ascii", "replace").split("\r\n"):
            if line.lower().startswith("content-length:"):
                length = int(line.split(":", 1)[1].strip())
        if length is None:
            raise RuntimeError(f"malformed LSP header: {headers!r}")
        body = b""
        while len(body) < length:
            chunk = self.proc.stdout.read(length - len(body))
            if chunk == b"":
                raise RuntimeError(
                    "lake serve closed its stdout mid-message")
            body += chunk
        return json.loads(body)

    def _dispatch(self, msg):
        method = msg.get("method")
        if method == "textDocument/publishDiagnostics":
            p = msg["params"]
            self.diags[p["uri"]] = p["diagnostics"]
        elif method is not None and "id" in msg:
            # server->client request: a minimal client answers null
            self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})

    def _request(self, method, params, timeout=3600):
        self.req_id += 1
        rid = self.req_id
        self._send({"jsonrpc": "2.0", "id": rid,
                    "method": method, "params": params})
        deadline = time.time() + timeout
        while time.time() < deadline:
            msg = self._read_msg()
            self._dispatch(msg)
            if msg.get("id") == rid and "method" not in msg:
                if "error" in msg:
                    raise RuntimeError(f"LSP {method}: {msg['error']}")
                return msg.get("result")
        raise RuntimeError(f"LSP {method} timed out after {timeout}s")

    def _notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    # ---- the one flow we need

    def census(self, timeout=3600):
        """didClose (if open) + didOpen the census file from disk, wait
        until the server finishes elaborating that version, and return
        its final diagnostics. The reopen is the invalidation protocol:
        the watchdog re-runs the file's setup (building stale imports
        itself) and elaborates against the current dependency state."""
        if self.opened:
            self._notify("textDocument/didClose",
                         {"textDocument": {"uri": CENSUS_URI}})
            self.opened = False
        text = open(CENSUS_LEAN, encoding="utf-8").read()
        self.version += 1
        self.diags.pop(CENSUS_URI, None)
        self._notify("textDocument/didOpen", {"textDocument": {
            "uri": CENSUS_URI, "languageId": "lean4",
            "version": self.version, "text": text}})
        self.opened = True
        self._request("textDocument/waitForDiagnostics",
                      {"uri": CENSUS_URI, "version": self.version},
                      timeout=timeout)
        return self.diags.get(CENSUS_URI, [])


# ----------------------------------------------------------------- daemon


class Daemon:
    def __init__(self):
        self.log = open(LOG, "a", encoding="utf-8")
        self.lsp = LspClient(self._log)

    def _log(self, msg):
        self.log.write(f"[{time.strftime('%F %T')}] {msg}\n")
        self.log.flush()

    def _handle(self, request):
        pt = _progress_tree()
        pt.regenerate_census_header()
        with open(pt.CENSUS_INPUT, "w", encoding="utf-8") as fh:
            json.dump({"names": list(request.get("names", [])),
                       "root": request.get("root", "fermat_last_theorem")},
                      fh)
        if not self.lsp.alive():
            self.lsp.stop()   # reap a dead child if any
            self._log("starting lake serve")
            self.lsp.start()
        t0 = time.time()
        diags = self.lsp.census()
        self._log(f"census elaborated in {time.time() - t0:.1f}s "
                  f"({len(diags)} diagnostics)")
        errors = [d for d in diags if d.get("severity") == 1]
        if errors:
            msgs = "\n".join(
                f"{CENSUS_LEAN}:{d['range']['start']['line'] + 1}: "
                f"{d['message']}" for d in errors[:10])
            raise RuntimeError(f"census elaboration failed:\n{msgs}")
        for d in diags:
            msg = d.get("message", "")
            k = msg.find("{")
            if k < 0:
                continue
            try:
                cand = json.loads(msg[k:])
            except ValueError:
                continue
            if isinstance(cand, dict) and "sorried" in cand:
                return cand
        raise RuntimeError(
            "census elaboration produced no JSON output "
            f"({len(diags)} diagnostics, none parseable)")

    def handle(self, request):
        """Protocol error TRANSPORT only: any failure is forwarded as
        {"error": <real exception text>} — never converted to partial
        data, never silently retried."""
        try:
            return self._handle(request)
        except Exception as exc:
            self._log(f"query failed: {exc!r}")
            return {"error": f"{type(exc).__name__}: {exc}"}

    def serve(self):
        try:
            os.unlink(SOCK)
        except OSError:
            pass
        srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        srv.bind(SOCK)
        srv.listen(4)
        self._log("daemon listening")
        while True:
            conn, _ = srv.accept()
            try:
                data = b""
                while not data.endswith(b"\n"):
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data += chunk
                if not data.strip():
                    continue
                request = json.loads(data)
                if request.get("cmd") == "shutdown":
                    conn.sendall(b'{"ok": true}\n')
                    conn.close()
                    break
                resp = self.handle(request)
                conn.sendall((json.dumps(resp) + "\n").encode())
            except Exception as exc:
                # error transport for connection-level failures
                self._log(f"connection error: {exc!r}")
                try:
                    conn.sendall(
                        (json.dumps({"error": str(exc)}) + "\n").encode())
                except Exception:
                    pass
            finally:
                try:
                    conn.close()
                except Exception:
                    pass
        self.lsp.stop()
        try:
            os.unlink(SOCK)
        except OSError:
            pass
        self._log("daemon stopped")


# ----------------------------------------------------------------- client


def _connect(timeout):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    s.connect(SOCK)
    return s


def _attempt(request, timeout):
    """One connect+send+receive round; raises OSError on any
    connection-level failure (absent daemon, stale socket, daemon shut
    down mid-conversation)."""
    s = _connect(timeout)
    with s:
        s.sendall((json.dumps(request) + "\n").encode())
        data = b""
        while not data.endswith(b"\n"):
            chunk = s.recv(65536)
            if not chunk:
                break
            data += chunk
    if not data.strip():
        raise OSError("daemon closed the connection without a response")
    return json.loads(data)


def query(request, autostart=True, timeout=3600):
    """Send one request to the daemon. If no daemon answers, spawn one,
    wait a bounded moment for its socket, then make a SINGLE attempt —
    any failure after that propagates (crash policy; no retry loops)."""
    try:
        return _attempt(request, timeout)
    except OSError:
        if not autostart:
            raise
        subprocess.Popen(
            [sys.executable, os.path.abspath(__file__), "--serve"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        deadline = time.time() + 15
        while time.time() < deadline:
            try:
                _connect(1).close()
                break
            except OSError:
                time.sleep(0.25)
        else:
            raise RuntimeError(
                "lean-daemon socket did not appear within 15s of spawn")
        return _attempt(request, timeout)


def main():
    if "--serve" in sys.argv:
        Daemon().serve()
    elif "--stop" in sys.argv:
        try:
            print(json.dumps(query({"cmd": "shutdown"}, autostart=False)))
        except OSError:
            print('{"ok": false, "note": "daemon not running"}')
    elif "--query" in sys.argv:
        req = json.loads(sys.argv[sys.argv.index("--query") + 1])
        print(json.dumps(query(req)))
    else:
        print(__doc__)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
