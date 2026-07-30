#!/usr/bin/env python3
"""flt-loop.py -- the REAL loop. Same rules as the simulator, real fleet.

Transition rules live in flt_loop_rows.py and are shared with flt-loop-fs.py,
so the thing that was tested and the thing that runs cannot drift apart. What
differs here is only how the state is observed and how jobs are started:

  * `main` and `ancestor` are asked of the real /home/chend/flt-lean repo.
  * a job is a real `claude` process on a real worker host, started detached.
  * `alive` is a per-host sweep for the job's token, not a local /proc read.

$HOME is shared across every worker host, so the state directory is visible
from all of them -- which is what lets an agent write its own sentinel.

Run:  python3 flt-loop.py [--once] [--dry-run]
"""
import argparse
import concurrent.futures as cf
import json
import os
import pathlib
import shlex
import subprocess
import time

import flt_loop_rows
from flt_loop_rows import ROWS, evaluate

STATE = pathlib.Path.home() / ".flt-loop"
REPO = pathlib.Path.home() / "flt-lean"
HOSTMAP = pathlib.Path.home() / ".flt-worker-host"
SNAPSHOT = pathlib.Path.home() / ".flt-release-lake" / "build"
# The marker naming the sha those artifacts were built from. It lives BESIDE
# them, not in the state dir, for two reasons. It has exactly one writer (the
# merger, as its last act, after the publishing rename), so it cannot disagree
# with what is on disk. And it is not in a git repo a medic is invited to
# `diff its way back` through: a state-dir revert would resurrect a stale sha
# as if it were a fresh observation of the artifacts, which is the one lie the
# loop cannot survive -- every agent dispatched afterwards seeds its .lake from
# artifacts believed to be for a different main.
SNAPSHOT_SHA = pathlib.Path.home() / ".flt-release-lake" / "sha"
DOCTRINE = pathlib.Path.home() / ".flt-agent-doctrine.md"
CLAUDE = str(pathlib.Path.home() / ".local" / "bin" / "claude")
TICK = 10
HOST_REFRESH = 300          # seconds; a loadavg older than this is not useful
ALIVE_CACHE = 20            # seconds; one ssh sweep per host, not per job


# ---------------------------------------------------------------- primitives
def wr(path, text):
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w") as fh:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def rd(path, default=None):
    try:
        return pathlib.Path(path).read_text()
    except (FileNotFoundError, IsADirectoryError):
        return default


def rm(path):
    try:
        pathlib.Path(path).unlink()
    except (FileNotFoundError, IsADirectoryError):
        pass


def git_state(*a):
    return subprocess.run(["git", "-C", str(STATE), "-c", "user.email=loop@flt",
                           "-c", "user.name=flt-loop"] + list(a),
                          capture_output=True, text=True)


def git_repo(*a):
    return subprocess.run(["git", "-C", str(REPO)] + list(a),
                          capture_output=True, text=True)


def main_sha():
    return git_repo("rev-parse", "--short", "main").stdout.strip()


def canon_sha(v):
    """Canonical short sha, or the value verbatim if git cannot resolve it.

    Rows 10 and 12 compare `audited` and the snapshot sha against `main` with
    `==`, and `main` is `rev-parse --short`. The merger is asked for "the main
    sha you produced" and naturally writes all 40 characters, so release 20 --
    a complete, green, correct release -- read as UNAUDITED and the loop
    panicked on its own merge worker. Normalising the spelling here, in the one
    layer that can ask git what a sha means, keeps the guards' comparison exact
    rather than loosening them to a prefix test: a prefix test would be a
    second way to be wrong ("r2" is a prefix of "r20") and the guards are the
    last place to put an approximation.

    A value git does not recognise is returned unchanged, so a placeholder like
    `stale-release-19` still correctly compares unequal to main.
    """
    v = (v or "").strip()
    if not v:
        return v
    r = git_repo("rev-parse", "--short", "--verify", "-q", v + "^{commit}")
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else v


def is_ancestor(branch):
    if git_repo("rev-parse", "--verify", "-q", branch + "^{commit}").returncode:
        return False
    return git_repo("merge-base", "--is-ancestor", branch, "main").returncode == 0


def ssh(host, cmd, timeout=60):
    return subprocess.run(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10",
                           host, cmd], capture_output=True, text=True, timeout=timeout)


def email(subject, body):
    """Deyao asked to be told when things go wrong. One channel, no library."""
    try:
        subprocess.run(["mail", "-s", subject, "chendeyao001@proton.me"],
                       input=body, text=True, timeout=60)
    except Exception:
        pass
    with open(STATE / "email.log", "a") as fh:
        fh.write("%s | %s\n%s\n" % (time.strftime("%F %T"), subject, body))


# ------------------------------------------------------------- host metrics
def worker_hosts():
    out = {}
    if HOSTMAP.is_dir():
        for f in HOSTMAP.iterdir():
            v = rd(f, "")
            if v and v.strip():
                out[f.name] = v.strip()
    return out


def refresh_hosts(force=False):
    """Measured load per host, refreshed on a timer rather than every tick.

    An ssh fan-out is far too expensive to do at 10-second cadence, and a
    loadavg is a 1-minute average anyway -- sampling it faster than it moves
    buys nothing.
    """
    f = STATE / "hosts.json"
    if not force and f.exists() and time.time() - f.stat().st_mtime < HOST_REFRESH:
        try:
            return json.loads(f.read_text())
        except json.JSONDecodeError:
            pass
    hosts = sorted(set(worker_hosts().values()))
    probe = (r"""python3 -c 'import os,json;"""
             r"""m={l.split(":")[0]:int(l.split()[1]) for l in open("/proc/meminfo")};"""
             r"""l=float(open("/proc/loadavg").read().split()[0]);n=os.cpu_count();"""
             r"""print(json.dumps({"avail_gb":round(m["MemAvailable"]/1048576,1),"""
             r""""util":round(l/n,3),"ncpu":n}))'""")

    def one(h):
        try:
            r = ssh(h, probe, timeout=45)
            return h, json.loads(r.stdout.strip().splitlines()[-1])
        except Exception:
            return h, None

    out = {}
    with cf.ThreadPoolExecutor(max_workers=max(len(hosts), 1)) as ex:
        for h, d in ex.map(one, hosts):
            if d:
                out[h] = d
    if out:
        wr(f, json.dumps(out, indent=1))
    return out


# ------------------------------------------------------------- job liveness
_alive_cache = {"t": 0.0, "tokens": set()}
_anc_cache = {}


def live_tokens(force=False):
    """One sweep per host for `flt-job-<token>` tags.

    Identity is the token, never a command pattern -- the fleet shares these
    machines with other users, and a pattern match is how you conclude that
    somebody else's process is yours.
    """
    if not force and time.time() - _alive_cache["t"] < ALIVE_CACHE:
        return _alive_cache["tokens"]
    # MEDIC_HOST explicitly: it carries no worktree, so it is absent from the
    # worktree->host map and was never swept. The medic was therefore ALWAYS
    # observed dead -- harmless while it runs (SAFE MODE engages on the record,
    # not on aliveness) but it meant a medic that died could never be told from
    # one that was working, and SAFE MODE suspends every row below it. The loop
    # would have held forever, with the one job that can unstick it already
    # gone and no evidence of that anywhere in the state.
    hosts = sorted(set(worker_hosts().values()) | {flt_loop_rows.MEDIC_HOST})

    def one(h):
        try:
            r = ssh(h, "pgrep -a -u $USER . 2>/dev/null | grep -o 'flt-job-[0-9a-f]\\+' | sort -u",
                    timeout=40)
            return {t.replace("flt-job-", "") for t in r.stdout.split()}
        except Exception:
            return set()      # unreachable host: report nothing rather than dead

    tokens = set()
    with cf.ThreadPoolExecutor(max_workers=max(len(hosts), 1)) as ex:
        for s in ex.map(one, hosts):
            tokens |= s
    _alive_cache.update(t=time.time(), tokens=tokens)
    return tokens


# --------------------------------------------------------------- the prompt
PREAMBLE = """\
You are a %(kind)s in the flt-lean fleet, started by the loop (flt-loop.py).

INFRASTRUCTURE CHANGED ON 2026-07-30 -- READ THIS BEFORE ANYTHING ELSE
The orchestrator is no longer a Claude session. It is a Python state machine
whose entire state is on disk at %(state)s, evaluated every %(tick)ds. Nobody
is reading your messages. Consequences that change how you must work:

  * Your worktree is %(worktree)s on host %(host)s. Run lake ON THAT HOST --
    .lake is machine-local. The clean build of main is at %(snapshot)s; copy
    it in rather than building mathlib.
  * The per-worktree LSP/report servers are GONE, and any that were still
    running were stopped today. Verify with `lake build <Module>` and
    `lake env lean <file>` on the command line. There is no Lean MCP.
  * Read %(doctrine)s first.

HOW YOU FINISH -- THIS IS THE ONLY SIGNAL THE LOOP CAN SEE
Commit your work to your branch, then write this file, LAST, as your final act:

    %(sentinel)s

containing exactly one JSON object:

    {"token": "%(token)s", "panic": false, "why": "", "summary": "<one line>"}

  * `token` must be copied verbatim or the loop ignores the file.
  * `panic` is NOT a verdict on the mathematics. A proof that did not go
    through, a leaf that turned out to be FALSE AS STATED, a target already
    proven elsewhere -- all of those are `panic: false`, they are results, and
    a refutation with an explicit counterexample is a full success. Set
    `panic: true` only if you could not operate at all: no .lake where you
    were told to look, the worktree on a branch nobody claimed, a missing or
    torn tree. Put one sentence in `why`.
  * If you stop without writing it, the loop concludes you died and starts a
    replacement. Write it even when the news is bad.

YOUR TASK FOLLOWS.
------------------------------------------------------------------------------
"""

TAKEOVER = """\
NOTE -- YOU ARE TAKING OVER A WORKTREE THAT ALREADY HAS WORK IN IT.
A previous agent was working here and was stopped mid-task when the fleet was
shut down; its conversation cannot be replayed, but its work is still on disk.
Run `git -C %(worktree)s status --short` and `git -C %(worktree)s diff` FIRST.
Treat what you find as a colleague's unfinished work: read it, judge it, and
either finish it or explain in your commit why you replaced it. Do not delete
it unexamined, and do not assume it is wrong merely because it is unfamiliar.
------------------------------------------------------------------------------
"""


def compose(kind, name, j, s):
    head = PREAMBLE % {
        "kind": {"agent": "prover agent", "merger": "merge worker",
                 "medic": "loop medic"}[kind],
        "state": STATE, "tick": TICK, "worktree": pathlib.Path.home() / j["worktree"],
        "host": j.get("host"), "snapshot": SNAPSHOT, "doctrine": DOCTRINE,
        "sentinel": STATE / "jobs" / (name + ".sentinel"), "token": j["token"],
    }
    body = j["payload"] if isinstance(j["payload"], str) else json.dumps(j["payload"])
    if kind == "agent":
        if j.get("takeover"):
            head += TAKEOVER % {"worktree": pathlib.Path.home() / j["worktree"]}
        body = body.replace("{{FLT_WORKTREE}}", str(pathlib.Path.home() / j["worktree"]))
    elif kind == "merger":
        body = MERGER_TASK % {"inflight": ", ".join(j["payload"]) or "(nothing)",
                              "snapshot": SNAPSHOT, "state": STATE,
                              "snapshot_sha": SNAPSHOT_SHA}
    elif kind == "medic":
        body = MEDIC_TASK % {"reason": body, "state": STATE,
                             "src": pathlib.Path(__file__).resolve()}
    return head + body


MERGER_TASK = """\
You are the merge worker. You produce EVERY derived fact about main, and the
loop refuses your release if any is missing. Work in ~/flt-staging.

DO ALL FIVE, IN ORDER
 1. Merge these branches into main: %(inflight)s
    After EACH merge run `git diff --stat HEAD^1 HEAD`. A merge can report
    success and carry nothing -- and a dropped payload still builds. Empty for
    a branch that changed files means reset and re-merge. Decline a branch
    that will not reconcile and say so; declining is a result, not a panic.
 2. Build main clean and leave the artifacts at %(snapshot)s. Every agent
    dispatched after you copies its .lake from there, so a torn or stale one
    poisons all of them.
 3. Rewrite %(state)s/queue1: remaining queue1 first, then everything in
    %(state)s/queue2, then empty queue2. Tasks are free text separated by
    lines reading exactly `=== TASK ===`. Drop tasks whose leaf is already
    proven. Add tasks for open leaves nobody holds -- but a leaf a LIVE agent
    is working on is NOT unowned, and queueing it hands the same target to a
    second worker.
 4. Set queue1's first line to `AUDITED: <the main sha you produced>`.
 5. LAST, after the artifacts are in place: write that same sha into
    %(snapshot_sha)s -- the file contents are the sha and nothing else.

    That marker is how the loop learns which main the artifacts at
    %(snapshot)s belong to, and it CANNOT derive it any other way: a build
    directory does not say what it was built from. Without it the loop cannot
    adopt your release and cannot dispatch a single agent, however green your
    build is. Release 20 was complete, correct and green, and the loop
    panicked on it because this step did not exist.

    Write it LAST, after the publishing rename, so the marker never names a
    release whose artifacts are not yet on disk. If you declined branches or
    the build is not clean, do not write it -- an absent marker correctly says
    "there is no snapshot to dispatch against", and a wrong one seeds every
    agent in the fleet with a .lake for the wrong main.
"""

MEDIC_TASK = """\
The loop stopped and handed you the state at %(state)s. It is a git repo:
every tick is a commit, so `git log` is the transition trace and you can diff
your way back to the tick that broke things.

WHY THE LOOP STOPPED
  %(reason)s

YOUR AUTHORITY IS THE WHOLE LOOP
You run detached, reparented to init, and are NOT a child of the loop -- you
can kill the process that started you without bringing yourself down. So
repairing state on disk is the smallest thing you may do. You may also edit
the loop source (%(src)s) -- a state its table cannot express is a defect in
the table -- and start a replacement loop detached, killing the old one first
(one writer per state dir is enforced by a lock, so a replacement started
while the old pid lives will refuse). The fleet is untouched by any of this:
jobs are owned by their records, not by process lineage.

If you replace the loop, write your sentinel LAST. The new loop finds your
record, sees you alive, and holds in SAFE MODE until you finish.

Your sentinel takes an extra field: "go": true or false -- whether the loop
may resume. Both are emailed. GO is taken literally: the loop clears the panic
that produced you and returns to normal, so do not answer GO with the fault
still live. Put your explanation, for a human, in "why".
"""


# --------------------------------------------------------------- spawn
def do_spawn(s, name, j):
    """Start a real, detached claude process on the worker host."""
    host = j.get("host") or flt_loop_rows.MEDIC_HOST
    prompt = compose(j["kind"], name, j, s)
    wr(STATE / "jobs" / (name + ".prompt"), prompt)
    pf = STATE / "jobs" / (name + ".prompt")
    log = STATE / "joblogs" / (name + "-" + j["token"] + ".log")
    log.parent.mkdir(parents=True, exist_ok=True)
    wt = pathlib.Path.home() / j["worktree"]
    # exec -a puts the token in argv[0]; that tag IS the job's identity, and
    # the only thing the liveness sweep matches on.
    # Absolute path: a non-interactive ssh shell does not source the profile,
    # so `claude` is not on PATH there and the spawn dies with "command not
    # found" into a log nobody reads. $HOME is shared, so this resolves on
    # every worker host.
    inner = ("cd %s 2>/dev/null || cd %s; "
             "exec -a flt-job-%s %s --dangerously-skip-permissions "
             "-p \"$(cat %s)\""
             % (shlex.quote(str(wt)), shlex.quote(str(REPO)), j["token"],
                shlex.quote(CLAUDE), shlex.quote(str(pf))))
    cmd = ("setsid --fork nohup bash -c %s >%s 2>&1 </dev/null"
           % (shlex.quote(inner), shlex.quote(str(log))))
    try:
        ssh(host, cmd, timeout=45)
    except Exception as e:
        note = "spawn of %s on %s failed: %s" % (name, host, e)
        email("flt-loop: spawn failed", note)
    return (host, None, None)


flt_loop_rows.SPAWN = do_spawn


# --------------------------------------------------------------- state I/O
def _pairs(name):
    out = {}
    for ln in (rd(STATE / name, "") or "").splitlines():
        if ln.strip():
            k, _, v = ln.partition(" ")
            out[k] = v.strip()
    return out


def split_tasks(text):
    blocks, cur = [], []
    for ln in text.splitlines():
        if ln.strip() == "=== TASK ===":
            if any(x.strip() for x in cur):
                blocks.append("\n".join(cur).strip())
            cur = []
        else:
            cur.append(ln)
    if any(x.strip() for x in cur):
        blocks.append("\n".join(cur).strip())
    return blocks


def load():
    q1 = (rd(STATE / "queue1", "") or "").splitlines()
    aud = None
    if q1 and q1[0].startswith("AUDITED:"):
        v = q1[0].split(":", 1)[1].strip()
        aud = None if v in ("none", "") else canon_sha(v)
        q1 = q1[1:]
    tokens = live_tokens()
    jobs = {}
    for f in sorted((STATE / "jobs").glob("*.json")):
        n = f.stem
        try:
            j = json.loads(f.read_text())
        except json.JSONDecodeError:
            continue
        # Token-checked: a marker naming a different token belongs to a
        # previous incarnation of this record and is not evidence about this
        # one. Resume mints a new token precisely so the old marker goes inert.
        st = rd(STATE / "jobs" / (n + ".started"), "")
        j["started"] = bool(st) and st.strip() == j["token"]
        sen = rd(STATE / "jobs" / (n + ".sentinel"))
        j["sentinel"] = None
        if sen:
            try:
                d = json.loads(sen)
                if d.get("token") == j["token"]:
                    j["sentinel"] = d
            except json.JSONDecodeError:
                j["sentinel"] = None      # truncated = not finished
        j["alive"] = j["token"] in tokens
        j.setdefault("retries", 0)
        jobs[n] = j
    wh = worker_hosts()
    # An OBSERVATION of the artifacts on disk, read from the marker the merger
    # leaves beside them -- not loop state, so save() never writes it back.
    # Nothing wrote it at all until release 20 panicked: the merger's task text
    # said "leave the artifacts at <path>" and never mentioned the marker the
    # ADOPT guard demands, so row 10 could not fire and never once did in the
    # loop's whole history. The simulator hid it -- its fake merger sets
    # s["snapshot"] itself (flt-loop-fs.py, "s['snapshot'] = {'sha': s['main']}"),
    # so the ROWS were tested against a world that produced a fact the real
    # world had nobody to produce. Shared rules are not enough; the two
    # environments have to agree about who writes what.
    ssha = canon_sha(rd(SNAPSHOT_SHA, "") or "")
    snap = {"sha": ssha} if ssha and SNAPSHOT.is_dir() else None
    stored = _pairs("workers")
    sha = main_sha()
    # Only awaiting_merge branches can be ancestors that matter, and the answer
    # can only change when main moves -- so it is cached on the sha. Asking git
    # about all 400 worktrees every 10 seconds would be 40 subprocesses a
    # second to answer a question about 47 of them.
    anc = {}
    if _anc_cache.get("sha") != sha:
        _anc_cache.clear()
        _anc_cache["sha"] = sha
    for w in wh:
        if stored.get(w) == "awaiting_merge":
            if w not in _anc_cache:
                _anc_cache[w] = is_ancestor(w)
            anc[w] = _anc_cache[w]
        else:
            anc[w] = False
    return {
        "stop": (STATE / "STOP").exists(),
        "main": main_sha(),
        "rebaselined": canon_sha(rd(STATE / "rebaselined", "") or ""),
        "snapshot": snap,
        "queue1": {"audited": aud, "tasks": split_tasks("\n".join(q1))},
        "queue2": split_tasks(rd(STATE / "queue2", "") or ""),
        "batch": [b for b in (rd(STATE / "batch", "") or "").splitlines() if b.strip()],
        "inflight": ([b for b in (rd(STATE / "inflight") or "").splitlines() if b.strip()]
                     if (STATE / "inflight").exists() else None),
        "jobs": jobs,
        "workers": {w: (stored.get(w) or None) for w in wh},
        "worker_host": wh,
        "ancestor": anc,
        "healthy": {k: v == "1" for k, v in _pairs("healthy").items()},
        "hosts": refresh_hosts(),
        "log": [], "git": [], "email": [],
    }


def save(s):
    wr(STATE / "rebaselined", s["rebaselined"])
    wr(STATE / "queue1", "AUDITED: %s\n%s" % (
        s["queue1"]["audited"] or "none",
        "\n=== TASK ===\n".join(s["queue1"]["tasks"])))
    wr(STATE / "queue2", "\n=== TASK ===\n".join(s["queue2"]))
    wr(STATE / "batch", "".join(b + "\n" for b in s["batch"]))
    if s["inflight"] is None:
        rm(STATE / "inflight")
    else:
        wr(STATE / "inflight", "".join(b + "\n" for b in s["inflight"]))
    # NOT written: s["snapshot"]. It is an observation of ~/.flt-release-lake,
    # and the merger is its only writer. Mirroring it into the state repo would
    # give the loop a second, revertable copy of a fact about the world -- and
    # an inert file that still looks authoritative is a trap for the next
    # medic. `rebaselined` and the row-10 commit message already carry the
    # released sha into the transition trace.
    wr(STATE / "workers","".join("%s %s\n" % (w, st)
                                  for w, st in sorted(s["workers"].items()) if st))
    if s["stop"]:
        wr(STATE / "STOP", "halted\n")
    live = set(s["jobs"])
    for n, j in s["jobs"].items():
        # An explicit key list, so anything a row invents is dropped unless it
        # is named here -- a field that rows write and save() silently discards
        # reads as amnesia one tick later. Anything added to a job record must
        # be added here too.
        rec = {k: j.get(k) for k in ("kind", "worktree", "payload", "token",
                                     "retries", "host", "pid", "session",
                                     "takeover")}
        wr(STATE / "jobs" / (n + ".json"), json.dumps(rec, indent=1))
        if j["started"]:
            wr(STATE / "jobs" / (n + ".started"), j["token"])
        if j["sentinel"] is not None:
            d = dict(j["sentinel"]); d["token"] = j["token"]
            wr(STATE / "jobs" / (n + ".sentinel"), json.dumps(d))
    for f in (STATE / "jobs").glob("*"):
        if f.name.split(".")[0] not in live:
            rm(f)


def commit_state(msg):
    git_state("add", "-A")
    git_state("commit", "-q", "-m", msg[:2000])


def take_lock():
    lock = STATE / "loop.lock"
    prev = (rd(lock) or "").strip()
    if prev.isdigit() and int(prev) != os.getpid():
        try:
            cmd = pathlib.Path("/proc/%s/cmdline" % prev).read_bytes()
        except OSError:
            cmd = b""
        if b"flt-loop.py" in cmd:
            raise SystemExit("refusing to start: loop pid %s already owns %s"
                             % (prev, STATE))
    wr(lock, str(os.getpid()) + "\n")


IDLE, PANIC = 13, 14
# Rows whose action changes nothing. They must not commit, for the same reason
# idle does not: the state repo's whole value is that `git log` IS the
# transition trace, and a medic that takes an hour buries the tick that broke
# things under ~360 identical "SAFE MODE" commits. Measured: 20 of them in the
# 3.5 minutes before this line was written.
QUIET = (IDLE, 4)


def tick(dry=False):
    s = load()
    rows, firing = evaluate(s)
    label = next(l for i, l, _, _ in ROWS if i == firing)
    if dry:
        return firing, label, s, rows
    for rid, lbl, _, action in ROWS:
        if rid == firing:
            action(s)
            break
    for e in s["email"]:
        email("flt-loop: " + e.split(":")[0][:60], e)
    save(s)
    if firing not in QUIET:
        extra = " [%s]" % s["spawned"] if s.get("spawned") else ""
        commit_state(s["git"][0] if s["git"] else "row %d: %s%s" % (firing, label, extra))
    return firing, label, s, rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    if not (STATE / "rebaselined").exists():
        raise SystemExit("no state at %s -- run flt-loop-bootstrap.py first" % STATE)
    if a.dry_run:
        f, lbl, s, rows = tick(dry=True)
        print("would fire row %d: %s" % (f, lbl))
        for r in rows:
            # A guard returns its `why` unconditionally, so a row that MATCHED
            # but lost to an earlier row was printing its own failure text --
            # which reads as "this row does not apply" when the truth is the
            # opposite. That sent a medic chasing a contradiction between row 6
            # ("no agent finished") and row 13 ("8 agents finished").
            if r["fires"]:
                v = "FIRES"
            elif r["matched"]:
                v = "matched -- row %d fired first" % f
            else:
                v = r["why"][:70]
            print("  %-3s %-58s %s" % (r["id"], r["label"][:58], v))
        return
    take_lock()
    print("flt-loop running, pid %d, state %s" % (os.getpid(), STATE))
    while True:
        try:
            f, lbl, s, _ = tick()
            if f not in QUIET:
                print("%s row %-3d %s" % (time.strftime("%T"), f, lbl))
            if s.get("halted"):
                print("STOP -- exiting")
                return
        except Exception as e:
            email("flt-loop: tick raised", repr(e))
            time.sleep(30)
        if a.once:
            return
        time.sleep(TICK)


if __name__ == "__main__":
    main()
