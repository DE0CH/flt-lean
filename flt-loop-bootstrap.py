#!/usr/bin/env python3
"""flt-loop-bootstrap.py -- build ~/.flt-loop from the stopped fleet.

One-time. Maps the files the old orchestrator kept onto the state the loop
expects, and stops. It does not start anything.

What maps cleanly:
    ~/.flt-merge-batch.inflight  -> inflight   (46 branches the killed merger
                                    claimed; row 9 restores them to the batch)
    ~/.flt-merge-batch           -> batch
    pool `batched`               -> awaiting_merge
    pool `free` / `ready`        -> free       (`ready` has no loop equivalent
                                    by design -- agents copy .lake themselves)
    ~/.flt-task-queue            -> queue1     (already `=== TASK ===` blocks
                                    carrying {{FLT_WORKTREE}} placeholders)
    ~/.flt-worker-host/*         -> worker_host

What needed a decision:
    pool `claimed` (47) -- agents Deyao killed. Their work is still in the
    worktrees but their conversations CANNOT be replayed: they were Agent-tool
    subagents of an orchestrator session, and their ids are agent ids, not
    resumable `claude --resume` session ids (checked: no session file matches).
    So each becomes a job record marked `takeover`, and its worktree keeps its
    uncommitted work. The replacement is told to read `git status`/`git diff`
    first and treat what it finds as a colleague's unfinished work. The asset
    being preserved is the WORK, which is on disk, not the transcript.

    Those records are written started-but-not-alive with no sentinel, which is
    already row 8's "agent died -> resume", so the loop restarts them itself
    rather than needing a special path.
"""
import json
import os
import pathlib
import shutil
import subprocess
import sys

HOME = pathlib.Path.home()
STATE = HOME / ".flt-loop"
REPO = HOME / "flt-lean"
POOL = HOME / ".flt-worktree-pool"
QUEUE = HOME / ".flt-task-queue"
BATCH = HOME / ".flt-merge-batch"
INFLIGHT = HOME / ".flt-merge-batch.inflight"
HOSTMAP = HOME / ".flt-worker-host"
SNAPSHOT = HOME / ".flt-release-lake" / "build"

sys.path.insert(0, str(REPO))
from flt_loop_rows import tok                                    # noqa: E402


def wr(p, t):
    p = pathlib.Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(t)


def rd(p, d=""):
    try:
        return pathlib.Path(p).read_text()
    except OSError:
        return d


def main():
    if STATE.exists():
        if "--force" not in sys.argv:
            raise SystemExit("%s exists; --force to rebuild" % STATE)
        shutil.rmtree(STATE)
    STATE.mkdir(parents=True)
    (STATE / "jobs").mkdir()
    subprocess.run(["git", "-C", str(STATE), "init", "-q"])

    sha = subprocess.run(["git", "-C", str(REPO), "rev-parse", "--short", "main"],
                         capture_output=True, text=True).stdout.strip()

    pool, claimed, batched = {}, [], []
    for ln in rd(POOL).splitlines():
        p = ln.split()
        if len(p) < 2:
            continue
        w, st = p[0], p[1]
        pool[w] = st
        if st == "claimed":
            claimed.append(w)
        elif st == "batched":
            batched.append(w)

    hostmap = {f.name: rd(f).strip() for f in HOSTMAP.iterdir()} if HOSTMAP.is_dir() else {}

    # workers: only non-derivable states are stored. `claimed` is derived from
    # a job record existing, so it must NOT be written here -- writing it would
    # put the same fact in two places, which is how the simulator first got a
    # worktree stuck.
    wr(STATE / "workers", "".join("%s awaiting_merge\n" % w for w in sorted(batched)))
    wr(STATE / "healthy", "".join("%s 1\n" % w for w in sorted(pool)))

    # rebaselined := main. Release 19 was fully processed before the shutdown,
    # so the loop has nothing to adopt; leaving it empty would make it think a
    # release had just landed with no merger to have produced it.
    wr(STATE / "rebaselined", sha)

    # queue1 unaudited: these 33 tasks were written against an older main and
    # nothing has checked them since. Marking them audited would skip the
    # merger's audit and dispatch stale targets -- the phantom-dispatch failure
    # this project keeps rediscovering.
    q = rd(QUEUE).strip()
    wr(STATE / "queue1", "AUDITED: none\n" + q + "\n")
    wr(STATE / "queue2", "")

    wr(STATE / "batch", rd(BATCH))
    if INFLIGHT.exists():
        wr(STATE / "inflight", rd(INFLIGHT))

    if SNAPSHOT.exists():
        # Deliberately NOT stamped at main: the snapshot on disk was built for
        # release 19 and main has moved since. Claiming it is current would
        # seed every agent with a .lake for the wrong main.
        wr(STATE / "snapshot.json", json.dumps({"sha": "stale-release-19"}))

    wr(STATE / "email.log", "")

    for w in sorted(claimed):
        t = tok()
        rec = {"kind": "agent", "worktree": w, "payload": "", "token": t,
               "retries": 0, "host": hostmap.get(w), "pid": None,
               "session": None, "takeover": True}
        wr(STATE / "jobs" / (w + ".json"), json.dumps(rec, indent=1))
        wr(STATE / "jobs" / (w + ".started"), t)

    subprocess.run(["git", "-C", str(STATE), "add", "-A"])
    subprocess.run(["git", "-C", str(STATE), "-c", "user.email=loop@flt",
                    "-c", "user.name=flt-loop", "commit", "-q", "-m",
                    "bootstrap from the stopped fleet at main %s" % sha])

    print("state:      %s" % STATE)
    print("main:       %s" % sha)
    print("workers:    %d total, %d awaiting_merge, %d takeover records"
          % (len(pool), len(batched), len(claimed)))
    print("queue1:     %d tasks, AUDITED: none" % (q.count("=== TASK ===") + 1 if q else 0))
    print("batch:      %d   inflight: %d"
          % (len(rd(BATCH).split()), len(rd(INFLIGHT).split())))


if __name__ == "__main__":
    main()
