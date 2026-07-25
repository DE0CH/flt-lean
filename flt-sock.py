#!/usr/bin/env python3
"""Expose ONE long-lived child process on a unix socket, agent-managed.

    flt-sock.py <socket-path> [--idle SECONDS] -- <command> [args...]

Runs on the Lean host. Spawns <command> once, binds <socket-path>, and pumps
bytes between the connected client and the child until the client disconnects.
The child KEEPS RUNNING across connections, which is the whole point: the
expensive part is loading the import cone, and it is paid once per daemon, not
once per query.

WHO OWNS THIS (Deyao, 2026-07-25). The AGENT does — it starts the daemon in the
background when it needs one and stops it when done. There is no systemd unit,
no shared state file, no cross-process document map. The previous design had
all three, and every verification defect this project hit came from them: a
stale `lake setup-file` failure replayed as authoritative, a false clean from a
publish nobody heard, four rival elaborations of one file, clients wedged on
dead FIFO handles. A daemon owned by exactly one agent cannot have those bugs,
because there is no second client to disagree with.

TWO USES, ONE SCRIPT — the daemon is protocol-agnostic. It moves bytes and does
not parse them, so framing is the client's business:
  * `repl`      — JSON objects separated by blank lines (turn-by-turn proving)
  * `lake serve` — LSP, Content-Length framed
The client is whatever the agent likes; a unix socket needs no wrapper.

IDLE TIMEOUT is not a convenience, it is the memory fix. An agent that forgets
to stop its daemon used to leak a multi-GB `lean --worker` forever, and that
leak — not concurrency — is what drove this fleet's memory climb. With a
timeout, forgetting costs bounded memory and the explicit stop becomes an
optimisation rather than a correctness requirement. Default 30 minutes; the
clock runs only while NO client is connected, so a long elaboration never
trips it.

Exits when the child dies, when the idle timer fires, or on SIGTERM, and always
unlinks the socket on the way out so a stale path never masquerades as a live
daemon.
"""

import argparse
import os
import select
import signal
import socket
import subprocess
import sys
import time


def log(msg):
    sys.stderr.write(f"flt-sock: {msg}\n")
    sys.stderr.flush()


def main():
    # Split on the first standalone `--` ourselves. argparse.REMAINDER would
    # swallow our own options here, because it captures everything after the
    # first positional — so `<socket> --idle 5 -- cat` made "--idle" the
    # child command.
    argv = sys.argv[1:]
    if "--" in argv:
        cut = argv.index("--")
        own, cmd = argv[:cut], argv[cut + 1:]
    else:
        own, cmd = argv, []

    ap = argparse.ArgumentParser(
        usage="flt-sock.py <socket-path> [--idle SECONDS] -- <command> ...")
    ap.add_argument("socket_path")
    ap.add_argument("--idle", type=float, default=1800.0,
                    help="exit after this many seconds with no client "
                         "connected (default 1800; 0 disables)")
    args = ap.parse_args(own)

    if not cmd:
        ap.error("no child command given (use: <socket> -- <command> ...)")

    sock_path = os.path.abspath(args.socket_path)
    if os.path.exists(sock_path):
        # A leftover socket from a crashed daemon is not a live daemon.
        # Refuse only if something is actually listening on it.
        probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        live = False
        try:
            probe.connect(sock_path)
            live = True
        except OSError:
            live = False
        finally:
            probe.close()
        if live:
            log(f"a daemon is already listening on {sock_path}; refusing")
            return 3
        os.unlink(sock_path)

    child = subprocess.Popen(cmd, stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=None,
                             bufsize=0)
    log(f"child pid={child.pid}: {' '.join(cmd)}")

    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(sock_path)
    srv.listen(1)
    os.chmod(sock_path, 0o600)
    log(f"listening on {sock_path} (idle timeout "
        f"{'off' if args.idle <= 0 else f'{args.idle:g}s'})")

    stop = {"now": False}

    def onterm(_sig, _frm):
        stop["now"] = True
    signal.signal(signal.SIGTERM, onterm)
    signal.signal(signal.SIGINT, onterm)

    rc = 0
    idle_since = time.time()
    try:
        while not stop["now"]:
            if child.poll() is not None:
                log(f"child exited rc={child.returncode}; shutting down")
                rc = child.returncode or 0
                break
            timeout = 1.0
            ready, _, _ = select.select([srv], [], [], timeout)
            if not ready:
                if args.idle > 0 and time.time() - idle_since > args.idle:
                    log(f"idle for {args.idle:g}s with no client; exiting")
                    break
                continue
            conn, _ = srv.accept()
            log("client connected")
            _pump(conn, child)
            conn.close()
            idle_since = time.time()
            log("client disconnected; child still warm")
    finally:
        try:
            os.unlink(sock_path)
        except OSError:
            pass
        if child.poll() is None:
            child.terminate()
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                child.kill()
        log("daemon gone, socket unlinked")
    return rc


def _pump(conn, child):
    """Move bytes both ways until the client hangs up or the child dies.

    Deliberately no framing: this daemon does not know whether it is carrying
    LSP or REPL JSON, and does not need to. A client that wants a reply reads
    until it has seen a complete message BY ITS OWN protocol's rules.
    """
    conn.setblocking(False)
    cout = child.stdout
    while True:
        if child.poll() is not None:
            return
        ready, _, _ = select.select([conn, cout], [], [], 0.5)
        for src in ready:
            if src is conn:
                try:
                    data = conn.recv(65536)
                except (BlockingIOError, InterruptedError):
                    continue
                except OSError:
                    return
                if not data:
                    return  # client hung up; child stays alive
                try:
                    child.stdin.write(data)
                    child.stdin.flush()
                except (BrokenPipeError, OSError):
                    return
            else:
                data = os.read(cout.fileno(), 65536)
                if not data:
                    return  # child closed stdout
                try:
                    conn.sendall(data)
                except OSError:
                    return


if __name__ == "__main__":
    sys.exit(main())
