#!/usr/bin/env python3
"""Expose ONE persistent `lake serve` on a unix socket. Runs on the Lean host.

WHY A SOCKET AND NOT FIFOs (Deyao's call, 2026-07-25, after the FIFO relay
failed). A FIFO delivers each byte to exactly ONE reader. To stop a FIFO from
EOF-ing when a client disconnects you must hold it open O_RDWR — but then the
writer is also a reader, and the kernel may hand a request back to the writer
instead of to `lake serve`. Chaining FIFO -> pipe -> FIFO across two machines
gave four places for that ambiguity to bite, and it did, twice, silently. A unix
socket is point-to-point: bytes written by one end can only be read by the other.
There is no reader ambiguity to get wrong.

WHY THIS SCRIPT EXISTS RATHER THAN `socat UNIX-LISTEN:...,fork EXEC:'lake serve'`:
socat's `fork` spawns a NEW lake serve per connection, which throws away the warm
elaboration state that is the entire point of a resident server — hours of import
cone per worktree. This keeps ONE lake serve for the life of the process and lets
clients come and go around it.

LIFETIME. `lake serve` is a child of this process, and this process is a systemd
USER unit on the Lean host. So it survives ssh drops, bridge restarts, and
anything else stopping on the client side — exactly the property Deyao required.
A client disconnect is NOT an error: the socket goes back to accepting and
`lake serve` keeps its state.

CONSEQUENCE FOR THE LSP HANDSHAKE. Because `lake serve` persists across client
reconnects, it stays INITIALIZED. `lake serve` errors if sent `initialize` twice
("No request handler found for 'initialize'"), so a reconnecting client must NOT
re-handshake. That is why the local bridge unit must not delete
`.report-server/state.json` on restart — only a restart of THIS unit invalidates
the handshake, and clearing the marker is then the orchestrator's job.

Byte counters are logged per direction. They exist because the previous relay
failed silently and could not be diagnosed: with no counters, a break in any hop
looked identical to every other break. Never ship a relay without them.

Usage: flt-lake-socket.py <instance>     (cwd must be the worktree)
"""

import os
import socket
import subprocess
import sys
import threading

HOME = "/home/chend"


def log(msg):
    sys.stderr.write(f"flt-lake-socket: {msg}\n")
    sys.stderr.flush()


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("usage: flt-lake-socket.py <instance>\n")
        return 2
    inst = sys.argv[1]
    wt = os.path.join(HOME, inst)
    sockdir = os.path.join(wt, ".report-server")
    os.makedirs(sockdir, exist_ok=True)
    sockpath = os.path.join(sockdir, "lake.sock")

    if os.path.exists(sockpath):
        os.unlink(sockpath)

    lake = subprocess.Popen(
        ["lake", "serve", "--"], cwd=wt,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    log(f"{inst}: lake serve pid {lake.pid}; listening on {sockpath}")

    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(sockpath)
    os.chmod(sockpath, 0o600)
    srv.listen(1)

    # Guard: if lake serve dies, exit so systemd restarts the whole pair rather
    # than leaving a socket that accepts and then silently drops everything.
    def watch_lake():
        rc = lake.wait()
        log(f"{inst}: lake serve exited rc={rc}; exiting so systemd restarts")
        os._exit(1 if rc != 0 else 0)
    threading.Thread(target=watch_lake, daemon=True).start()

    while True:
        conn, _ = srv.accept()
        log(f"{inst}: client connected")
        counts = {"in": 0, "out": 0}
        done = threading.Event()

        def sock_to_lake():
            try:
                while True:
                    b = conn.recv(65536)
                    if not b:
                        break
                    lake.stdin.write(b)
                    lake.stdin.flush()
                    counts["in"] += len(b)
            except Exception as exc:
                log(f"{inst}: sock->lake ended: {exc!r}")
            finally:
                done.set()

        def lake_to_sock():
            try:
                while True:
                    b = lake.stdout.read1(65536)
                    if not b:
                        break
                    conn.sendall(b)
                    counts["out"] += len(b)
            except Exception as exc:
                log(f"{inst}: lake->sock ended: {exc!r}")
            finally:
                done.set()

        t1 = threading.Thread(target=sock_to_lake, daemon=True)
        t2 = threading.Thread(target=lake_to_sock, daemon=True)
        t1.start(); t2.start()
        done.wait()
        try:
            conn.close()
        except Exception:
            pass
        log(f"{inst}: client gone (in={counts['in']}B out={counts['out']}B); "
            f"lake serve still warm, accepting again")


if __name__ == "__main__":
    sys.exit(main())
