#!/usr/bin/env python3
"""Pump a worktree's local report FIFOs to a remote `lake serve` unix socket.

WHAT THIS IS FOR, and it is deliberately the only thing it does: let the MCP be
pointed at a Lean LSP on another machine WITHOUT restarting Claude Code.

report-mcp.py always talks to <worktree>/.report-server/{req,resp}.fifo and knows
nothing about which machine serves it. So a worker moves hosts by changing only
what sits behind those FIFOs; the MCP is untouched and Claude Code keeps running.
Rewiring is one line in ~/.flt-worker-host/<instance> plus a systemctl restart.

    MCP  <->  local req/resp FIFOs  <->  [this pump]  <->  ssh  <->
              socat  <->  remote lake.sock  <->  persistent lake serve
                                                 (flt-lake-socket@<instance>)

The local end must be FIFOs because that is what report-mcp.py speaks. The remote
end is a SOCKET, not FIFOs: a FIFO hands each byte to exactly one reader, and
keeping one from EOF-ing means holding it O_RDWR, which makes the writer a reader
too — so a request can be delivered back to the writer instead of to lake serve.
Chaining FIFO -> pipe -> FIFO across two hosts gave that four chances to bite and
it bit twice, silently (2026-07-25). Sockets are point-to-point.

BYTE COUNTERS ARE NOT OPTIONAL. The relay this replaced failed with total silence
and could not be diagnosed, because a break in any hop looked exactly like a break
in any other. Every direction is counted and logged.

Local FIFOs are opened O_RDWR so this process is always its own reader/writer:
client connect/disconnect cycles can never EOF or SIGPIPE the pump.

HANDSHAKE INVALIDATION, and why this pump owns it (learned the hard way
2026-07-25). Do NOT clear .report-server/state.json merely because this pump
restarted: the remote lake serve persists across reconnects, stays INITIALIZED,
and errors if sent `initialize` twice. But when the REMOTE unit restarts, the
marker becomes a lie in the other direction — the next client skips `initialize`
and sends `didChange` to a fresh watchdog, which dies with

    Cannot read LSP request: Expected JSON-RPC request, got: {didChange...}

taking lake serve with it, restarting the unit, dropping this ssh, and looping.
That is exactly what happened to 44 instances after the machines were migrated,
and it was invisible to clients: they saw only "response pipe EOF".

The old rule made clearing the marker the ORCHESTRATOR's manual job, which is
precisely the kind of step that gets skipped. So this pump does it instead: it
reads the remote unit's ActiveEnterTimestamp at startup and compares it with
`.report-server/remote-session`. Different value => a different lake serve
process => the marker (handshake AND open-document map, both of which describe
the old process) is deleted. Same value => the marker is kept untouched. One
extra ssh per pump start, and the invariant becomes self-healing.

Usage: flt-report-bridge.py <instance>
       (host from ~/.flt-worker-host/<instance>)
"""

import os
import subprocess
import sys
import threading
import time

HOME = "/home/chend"

# systemd --user exports the GPG agent's SSH_AUTH_SOCK, which does not hold the
# key; with BatchMode that fails as exit 255 and the unit restart-loops. Bypass
# agents entirely (diagnosed 2026-07-25).
SSH_OPTS = [
    "-o", "BatchMode=yes",
    "-o", "IdentityAgent=none",
    "-o", "IdentitiesOnly=yes",
    "-i", os.path.join(HOME, ".ssh", "id_ed25519"),
    "-o", "ConnectTimeout=10",
    "-o", "StrictHostKeyChecking=accept-new",
]


def log(msg):
    sys.stderr.write(f"flt-report-bridge: {msg}\n")
    sys.stderr.flush()


def sync_handshake_marker(host, inst, sockdir):
    """Drop the client-side LSP state if the remote lake serve is a NEW process.

    See the module docstring: a marker describing a dead server makes the next
    client skip `initialize`, which kills the fresh server on its first request.
    """
    try:
        r = subprocess.run(
            ["ssh", "-T", *SSH_OPTS, host,
             f"systemctl --user show -p ActiveEnterTimestamp --value "
             f"flt-lake-socket@{inst}"],
            capture_output=True, text=True, timeout=30)
        session = r.stdout.strip()
    except Exception as exc:
        log(f"{inst}: cannot read remote session id ({exc!r}); leaving marker alone")
        return
    if not session:
        log(f"{inst}: remote unit reports no start time; leaving marker alone")
        return

    marker = os.path.join(sockdir, "remote-session")
    try:
        previous = open(marker).read().strip()
    except OSError:
        previous = ""
    if previous == session:
        log(f"{inst}: remote session unchanged; keeping LSP state")
        return

    state = os.path.join(sockdir, "state.json")
    try:
        os.remove(state)
        log(f"{inst}: remote session changed ({previous or 'unknown'} -> {session}); "
            f"cleared state.json so the next client re-initializes")
    except FileNotFoundError:
        log(f"{inst}: remote session {session}; no state.json to clear")
    with open(marker, "w") as fh:
        fh.write(session + "\n")


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("usage: flt-report-bridge.py <instance>\n")
        return 2
    inst = sys.argv[1]
    sockdir = os.path.join(HOME, inst, ".report-server")

    try:
        host = open(os.path.join(HOME, ".flt-worker-host", inst)).read().strip()
    except OSError:
        host = ""
    if not host or host == "local":
        log(f"{inst}: no remote host in ~/.flt-worker-host/{inst}; nothing to do")
        return 1

    req, resp = (os.path.join(sockdir, n) for n in ("req.fifo", "resp.fifo"))
    for p in (req, resp):
        if not os.path.exists(p):
            log(f"{inst}: missing FIFO {p}")
            return 1

    sync_handshake_marker(host, inst, sockdir)

    req_fd = os.open(req, os.O_RDWR)    # O_RDWR: never EOF when a client leaves
    resp_fd = os.open(resp, os.O_RDWR)

    remote_sock = f"{inst}/.report-server/lake.sock"
    ssh = subprocess.Popen(
        ["ssh", "-T", *SSH_OPTS,
         # Hold the channel open through the multi-hour silences of a
         # single-threaded elaboration.
         "-o", "ServerAliveInterval=30",
         "-o", "ServerAliveCountMax=1000",
         host,
         f"exec socat - UNIX-CONNECT:{remote_sock}"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    log(f"{inst} -> {host}:{remote_sock} (ssh pid {ssh.pid}) pumping")
    counts = {"req": 0, "resp": 0}
    stop = threading.Event()

    def req_to_ssh():
        try:
            while not stop.is_set():
                b = os.read(req_fd, 65536)
                if not b:
                    break
                ssh.stdin.write(b)
                ssh.stdin.flush()
                counts["req"] += len(b)
                log(f"{inst}: req->ssh {len(b)}B (total {counts['req']}B)")
        except Exception as exc:
            log(f"{inst}: req->ssh ended: {exc!r}")
        finally:
            stop.set()

    def ssh_to_resp():
        try:
            while not stop.is_set():
                b = ssh.stdout.read1(65536)
                if not b:
                    break
                os.write(resp_fd, b)
                counts["resp"] += len(b)
                log(f"{inst}: ssh->resp {len(b)}B (total {counts['resp']}B)")
        except Exception as exc:
            log(f"{inst}: ssh->resp ended: {exc!r}")
        finally:
            stop.set()

    threading.Thread(target=req_to_ssh, daemon=True).start()
    threading.Thread(target=ssh_to_resp, daemon=True).start()

    # Heartbeat so a stalled tunnel is visible in the journal rather than silent.
    def heartbeat():
        while not stop.is_set():
            time.sleep(300)
            if not stop.is_set():
                log(f"{inst}: alive (req {counts['req']}B, resp {counts['resp']}B)")
    threading.Thread(target=heartbeat, daemon=True).start()

    rc = ssh.wait()
    stop.set()
    log(f"{inst}: ssh exited rc={rc} (req {counts['req']}B, resp {counts['resp']}B)")
    return 1 if rc != 0 else 0


if __name__ == "__main__":
    sys.exit(main())
