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

DO NOT clear .report-server/state.json when restarting this pump. The remote
lake serve persists across reconnects and therefore stays INITIALIZED; it errors
if sent `initialize` twice. Only a restart of the REMOTE unit invalidates the
handshake.

Usage: flt-report-bridge.py <instance>
       (host from ~/.flt-worker-host/<instance>)
"""

import os
import subprocess
import sys
import threading
import time

HOME = "/home/chend"


def log(msg):
    sys.stderr.write(f"flt-report-bridge: {msg}\n")
    sys.stderr.flush()


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

    req_fd = os.open(req, os.O_RDWR)    # O_RDWR: never EOF when a client leaves
    resp_fd = os.open(resp, os.O_RDWR)

    remote_sock = f"{inst}/.report-server/lake.sock"
    ssh = subprocess.Popen(
        ["ssh", "-T",
         "-o", "BatchMode=yes",
         "-o", "ServerAliveInterval=30",
         "-o", "ServerAliveCountMax=1000",
         # systemd --user exports the GPG agent's SSH_AUTH_SOCK, which does not
         # hold the key; with BatchMode that fails as exit 255 and the unit
         # restart-loops. Bypass agents entirely (diagnosed 2026-07-25).
         "-o", "IdentityAgent=none",
         "-o", "IdentitiesOnly=yes",
         "-i", os.path.join(HOME, ".ssh", "id_ed25519"),
         "-o", "ConnectTimeout=10",
         "-o", "StrictHostKeyChecking=accept-new",
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
