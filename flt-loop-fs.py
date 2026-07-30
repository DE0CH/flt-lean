#!/usr/bin/env python3
"""flt-loop-fs.py -- the loop simulator, with state on a REAL filesystem.

The design claim is that the automaton's next step depends entirely on state
that lives on disk. `flt-loop-viz.py` asserts that; this one *tests* it, by
reloading the whole state from the directory before every single evaluation.
Nothing survives a tick in memory. If the claim were false, the machine would
lose its place.

It also exercises the two disciplines the real loop depends on and that are
easy to get subtly wrong on paper:

  * every write is `.tmp` -> fsync -> os.replace, so a crash never leaves a
    half-written file;
  * the state directory is a git repo, so `git log --oneline` IS the
    transition trace and a repair agent can diff its way back to the tick
    that broke things.

Run:  python3 flt-loop-fs.py [--dir /tmp/flt-loop-sim] [--port 8771]
"""
import argparse
import json
import os
import pathlib
import random
import shutil
import subprocess
from http.server import BaseHTTPRequestHandler, HTTPServer

import flt_loop_rows

DIR = pathlib.Path("/tmp/flt-loop-sim")


# --------------------------------------------------------------------------
# atomic primitives
# --------------------------------------------------------------------------
def wr(path, text):
    """Atomic write. The whole crash-safety story rests on this one function."""
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
    except FileNotFoundError:
        return default


def rm(path):
    try:
        pathlib.Path(path).unlink()
    except FileNotFoundError:
        pass


def git(*args):
    return subprocess.run(
        ["git", "-C", str(DIR), "-c", "user.email=loop@flt", "-c", "user.name=flt-loop"]
        + list(args), capture_output=True, text=True)


# --------------------------------------------------------------------------
# the CODE repo -- a real git repository standing in for flt-lean itself
# --------------------------------------------------------------------------
# Everything above this line is loop STATE. This is the thing the loop exists
# to change, and it is a genuine repo rather than a set of flags, because the
# predicates the loop turns on are git predicates. `ancestor` used to be a
# hand-edited file; a worker is freed exactly when its branch has landed on
# main, and asserting that with a flag tests nothing. Now it is a real
# `merge-base --is-ancestor`, agents really commit, and the merger really
# merges -- so a merge that silently carries nothing, or a branch that is an
# ancestor while its content is gone, is expressible here rather than being
# defined out of existence.
#
# It lives INSIDE the state dir but is git-ignored by it: two repos, one for
# what the loop knows and one for what it is working on.
def repo():
    return DIR / "repo"


def grepo(*args):
    return subprocess.run(
        ["git", "-C", str(repo()), "-c", "user.email=agent@flt",
         "-c", "user.name=flt-agent",
         # leaf names carry non-ASCII (the "·" successors), which git octal-
         # escapes in ls-tree output by default and would corrupt every name
         # read back out of the repo.
         "-c", "core.quotePath=false"] + list(args), capture_output=True, text=True)


def head_sha(ref="main"):
    return grepo("rev-parse", "--short", ref).stdout.strip()


def branch_exists(b):
    return grepo("rev-parse", "--verify", "-q", b + "^{commit}").returncode == 0


def is_ancestor(b):
    """The real predicate row 5 turns on."""
    return branch_exists(b) and grepo(
        "merge-base", "--is-ancestor", b, "main").returncode == 0


def leaf_path(name):
    return repo() / "leaves" / (name.replace("/", "_") + ".lean")


def seed_repo(tasks):
    repo().mkdir(parents=True)
    grepo("init", "-q")
    grepo("symbolic-ref", "HEAD", "refs/heads/main")
    (repo() / "leaves").mkdir()
    for t in tasks:
        wr(leaf_path(t), "theorem %s : True := by\n  sorry\n" % t)
    grepo("add", "-A")
    grepo("commit", "-q", "-m", "seed: %d open leaves" % len(tasks))


def agent_commit(branch, task, successors):
    """What a prover actually does: close its leaf, open the ones it cut."""
    grepo("checkout", "-q", branch)
    rm(leaf_path(task))
    for sc in successors:
        wr(leaf_path(sc), "theorem %s : True := by\n  sorry\n" % sc)
    grepo("add", "-A")
    grepo("commit", "-q", "-m",
          "%s: closed %s, opened %s" % (branch, task, ", ".join(successors)))
    grepo("checkout", "-q", "main")


def merge_branches(branches):
    """What the merge worker does. Returns the branches that actually landed."""
    grepo("checkout", "-q", "main")
    landed = []
    for b in branches:
        if not branch_exists(b):
            continue
        r = grepo("merge", "--no-ff", "-m", "merge %s" % b, b)
        if r.returncode == 0:
            landed.append(b)
        else:
            grepo("merge", "--abort")
    return landed


# --------------------------------------------------------------------------
# spawning: detached, adopted by record, never a child of the loop
# --------------------------------------------------------------------------
# These are REAL processes. The simulator could have kept `alive` as a flag,
# but the flag is what needs testing: the loop must be killable at any instant
# without disturbing a single job, and must re-adopt everything on restart
# from the records alone. Both are only true if the loop was never the parent.
#
# So a job is double-forked away (`setsid --fork`) and is reparented to init
# before it runs. It is therefore never reaped by us, never a zombie, and
# indifferent to our death.
#
# Identity is (pid, token), never a command pattern. A pid alone is
# insufficient because pids recycle, and matching on a pattern is how you kill
# somebody else's process that happens to share a substring -- so the token
# goes in argv[0] and is checked before the pid is believed or signalled.
# --------------------------------------------------------------------------
# prompts: an invariant half we author, and a variable half from the queue
# --------------------------------------------------------------------------
# Splitting these is not cosmetic. The invariant half is the CONTRACT -- what
# the job will find, what it must return, how it must behave -- and it has to
# be identical across every dispatch, because the loop's rows are written
# against it: the ADOPT guard demands the merger left a snapshot and an audit,
# and the panic row demands every job returns the binary field. If that text
# were retyped per task it would drift, and a row would start failing against
# jobs that were never told what they owed.
#
# The variable half is one line from the queue. Keeping it to that also keeps
# the queue editable by hand, which is the point of it being a text file.
#
# Composed at SPAWN and written to jobs/<n>.prompt, so the state repo records
# exactly what each job was told -- the medic's first question after a panic
# is usually "what did you actually ask it to do".
AGENT_DOCTRINE = """\
You are a prover agent in the flt-lean fleet.

WHAT YOU WILL FIND
  * Your worktree is at $WORKTREE on host $HOST, already fast-forwarded to
    main and checked out on the branch $WORKTREE.
  * A clean build of main is at $SNAPSHOT. COPY it into your worktree's .lake
    before building anything. Do not build mathlib from source.
  * Artifacts are machine-local: run lake ON $HOST, nowhere else.

HOW TO WORK
  * Develop against a throwaway scratch module importing only what you need,
    and do ONE final verify against the real file. Elaboration is
    single-threaded per file; this is the difference between a one-minute and
    a thirty-minute round trip.
  * A leaf may be FALSE AS STATED. Refuting one with an explicit
    counterexample and restating it correctly is a FULLY successful outcome.
  * Commit to your branch. Do not merge, do not touch another worktree.

HOW TO REPORT BACK
  * The leaves you closed, and the ones you opened, by name.
  * PANIC: true or false. This is NOT a verdict on the mathematics. A proof
    that did not go through, a leaf that turned out false, a target already
    proven elsewhere -- all of those are PANIC: false, they are results.
    PANIC: true means you could not operate at all: no .lake at the snapshot
    path, the worktree on a branch nobody claimed, a torn or missing tree.
    If you set it true, say in one sentence what was not where it should be.
"""

MERGER_DOCTRINE = """\
You are the merge worker. You produce EVERY derived fact about main, and the
loop will refuse your release if any of them is missing.

DO ALL FOUR, IN THIS ORDER
  1. Merge each branch in .inflight into main. After each merge run
     `git diff --stat HEAD^1 HEAD` -- a merge can report success and carry
     nothing, and a dropped payload builds perfectly. Empty for a branch that
     changed files means re-do it.
  2. Build main clean and leave the artifacts at $SNAPSHOT. Agents copy their
     .lake from there; a torn or stale one poisons every worker dispatched
     after you.
  3. Rewrite the queue: remaining queue1 first, then queue2, then empty
     queue2. Drop tasks whose leaf is no longer open. Add open leaves nobody
     holds -- but a leaf a LIVE agent is proving is NOT unowned, and queueing
     it hands the same target to a second worker.
  4. Stamp queue1 as audited at the main you produced.

REPORT
  * The branches that landed, and any you declined and why.
  * PANIC: true or false, same rule as the agents -- environment, never
    mathematics. Declining a branch is a result. A missing staging tree is a
    panic.
"""

MEDIC_DOCTRINE = """\
The loop has stopped and handed you the state. It is a git repo: `git log`
is the transition trace and every tick is a commit, so you can diff your way
back to the one that broke things.

The reason the loop could not continue is below. Repair the state on disk if
it is repairable.

RETURN
  * An explanation, for a human, of what went wrong and what you changed.
  * GO or NO-GO: whether the loop may resume. Both are emailed; NO-GO is the
    right answer when resuming would destroy evidence or repeat the fault.
"""


def compose_prompt(kind, j, name):
    body = {"agent": AGENT_DOCTRINE, "merger": MERGER_DOCTRINE,
            "medic": MEDIC_DOCTRINE}.get(kind, "")
    body = (body.replace("$WORKTREE", str(j.get("worktree")))
                .replace("$HOST", str(j.get("host")))
                .replace("$SNAPSHOT", str(DIR / "snapshot")))
    if kind == "agent":
        task = "\nYOUR TASK\n  Close this leaf: %s\n" % j["payload"]
    elif kind == "merger":
        task = ("\nYOUR BATCH\n  %s\n"
                % (", ".join(j["payload"]) if j["payload"]
                   else "(empty -- refresh the snapshot and audit only)"))
    else:
        task = "\nWHY THE LOOP STOPPED\n  %s\n" % j["payload"]
    return body + task


def _tag(token):
    return "flt-job-" + token


def spawn_detached(token, label):
    logdir = DIR / "joblogs"
    logdir.mkdir(parents=True, exist_ok=True)
    log = open(logdir / (token + ".log"), "a")
    subprocess.run(
        ["setsid", "--fork", "bash", "-c",
         'exec -a "%s" sleep 1000000' % _tag(token)],
        stdin=subprocess.DEVNULL, stdout=log, stderr=log)
    return find_pid(token)


def find_pid(token):
    """Adoption: locate a job by its token, owning nothing."""
    tag = _tag(token).encode()
    for d in pathlib.Path("/proc").iterdir():
        if not d.name.isdigit():
            continue
        try:
            if (d / "cmdline").read_bytes().split(b"\0")[0] == tag:
                return int(d.name)
        except (OSError, ValueError):
            continue
    return None


def proc_alive(pid, token):
    if not pid:
        return False
    try:
        cmd = pathlib.Path("/proc/%d/cmdline" % pid).read_bytes()
    except OSError:
        return False
    return cmd.split(b"\0")[0] == _tag(token).encode()


def kill_job(pid, token):
    """Signal only after the token confirms the pid is still ours."""
    if proc_alive(pid, token):
        try:
            os.kill(pid, 15)
        except OSError:
            pass


def do_spawn(s, name, j):
    wr(DIR / "jobs" / (name + ".prompt"), compose_prompt(j["kind"], j, name))
    pid = spawn_detached(j["token"], name)
    return (j["host"], pid,
            # stands in for the Claude transcript id -- what row 6 resumes from
            j["token"] + "-0000-4000-8000-" + j["token"] * 3)


def open_leaves():
    out = grepo("ls-tree", "--name-only", "main", "leaves/").stdout
    return sorted(pathlib.Path(x).stem for x in out.splitlines() if x.strip())


# --------------------------------------------------------------------------
# on-disk layout  <-> in-memory dict
# --------------------------------------------------------------------------
#   main              current release sha (stands in for `git rev-parse main`)
#   rebaselined       sha already reacted to
#   queue1            "AUDITED: <sha|none>" header, then one task per line
#   queue2            one task per line
#   batch             one branch per line
#   inflight          one branch per line   (absent = no claim outstanding)
#   snapshot.json     {"sha": ...}          (absent = no snapshot)
#   workers           "<wt> <state>" for NON-derivable states only
#   healthy/ancestor  "<wt> 0|1"
#   STOP              presence halts
#   jobs/<n>.json     the record;  .started / .sentinel written by the job
#   email.log         one line per notification


def seed():
    if DIR.exists():
        # Kill what we are about to forget. Wiping the records first would
        # orphan those processes PERMANENTLY -- adoption works by token, and
        # after the wipe no token survives to adopt them with. Every spawn
        # needs an owner, and the last owner has to release it.
        for f in sorted((DIR / "jobs").glob("*.json")) if (DIR / "jobs").exists() else []:
            try:
                rec = json.loads(f.read_text())
                kill_job(rec.get("pid"), rec["token"])
            except (OSError, ValueError, KeyError):
                pass
        shutil.rmtree(DIR)
    DIR.mkdir(parents=True)
    git("init", "-q")
    wr(DIR / ".gitignore", "repo/\n")
    tasks = ["exists_diffCharScalar", "exists_nat_eq_sum_breaks", "exists_isDiffChar"]
    seed_repo(tasks)
    sha = head_sha()
    # `main` is NOT a state file any more -- it is read from the repo, because
    # that is where it actually lives. `rebaselined` stays a file: it is the
    # loop's own memory of which sha it has already reacted to, which no repo
    # can answer.
    wr(DIR / "rebaselined", sha)
    wr(DIR / "queue1", "AUDITED: %s\n%s" % (sha, "".join(t + "\n" for t in tasks)))
    wr(DIR / "queue2", "")
    wr(DIR / "batch", "")
    wr(DIR / "snapshot.json", json.dumps({"sha": sha}))
    wr(DIR / "workers", "")
    wr(DIR / "healthy", "flt-lean-1 1\nflt-lean-2 1\nflt-lean-3 1\n")
    # The load distributor's input: which machines exist and how many jobs
    # each will carry. Capacity is per-host because a worktree's .lake is
    # machine-local -- a job can only run where its artifacts are.
    wr(DIR / "hosts", "nightcrawler 2\nrogue 1\n")
    wr(DIR / "email.log", "")
    (DIR / "jobs").mkdir()
    git("add", "-A")
    git("commit", "-q", "-m", "seed")


def _pairs(name):
    out = {}
    for ln in (rd(DIR / name, "") or "").splitlines():
        if ln.strip():
            k, v = ln.split()
            out[k] = v
    return out


def load():
    """Rebuild the ENTIRE state from disk. Called before every evaluation."""
    q1 = (rd(DIR / "queue1", "AUDITED: none\n") or "").splitlines()
    aud = None
    if q1 and q1[0].startswith("AUDITED:"):
        v = q1[0].split(":", 1)[1].strip()
        aud = None if v == "none" else v
        q1 = q1[1:]
    jobs = {}
    for f in sorted((DIR / "jobs").glob("*.json")):
        j = json.loads(f.read_text())
        n = f.stem
        j["started"] = (DIR / "jobs" / (n + ".started")).exists()
        # a marker whose token does not match the record is NOT a marker
        st = rd(DIR / "jobs" / (n + ".started"), "")
        if j["started"] and st.strip() != j["token"]:
            j["started"] = False
        sen = rd(DIR / "jobs" / (n + ".sentinel"))
        j["sentinel"] = None
        if sen:
            try:
                d = json.loads(sen)
                if d.get("token") == j["token"]:
                    j["sentinel"] = d
            except json.JSONDecodeError:
                j["sentinel"] = None          # truncated sentinel = not finished
        # Observed from the process table, not read from a marker we wrote.
        # A marker only records what we believed at the last tick; a job that
        # died in between would keep claiming to be alive, and the whole
        # died-vs-finished split rests on this being an observation.
        j["alive"] = proc_alive(j.get("pid"), j["token"])
        j.setdefault("retries", 0)
        jobs[n] = j
    snap = rd(DIR / "snapshot.json")
    return {
        "stop": (DIR / "STOP").exists(),
        "main": head_sha(),
        "rebaselined": (rd(DIR / "rebaselined", "") or "").strip(),
        "snapshot": json.loads(snap) if snap else None,
        "queue1": {"audited": aud, "tasks": [t for t in q1 if t.strip()]},
        "queue2": [t for t in (rd(DIR / "queue2", "") or "").splitlines() if t.strip()],
        "batch": [b for b in (rd(DIR / "batch", "") or "").splitlines() if b.strip()],
        "inflight": ([b for b in (rd(DIR / "inflight") or "").splitlines() if b.strip()]
                     if (DIR / "inflight").exists() else None),
        "jobs": jobs,
        "workers": {w: (_pairs("workers").get(w) or None)
                    for w in _pairs("healthy")},
        "healthy": {k: v == "1" for k, v in _pairs("healthy").items()},
        "hosts": {k: int(v) for k, v in _pairs("hosts").items()},
        # Asked of git, not of a file. A worker is freed when its branch has
        # really landed on main -- nothing else is evidence of that.
        "ancestor": {w: is_ancestor(w) for w in _pairs("healthy")},
        "log": [], "git": [], "email": [],
    }


def save(s):
    # `main` and `ancestor` are deliberately NOT written: both are answers the
    # repo gives, and writing them back would let the loop's opinion drift
    # away from the thing it describes.
    wr(DIR / "rebaselined", s["rebaselined"])
    wr(DIR / "queue1", "AUDITED: %s\n%s" % (s["queue1"]["audited"] or "none",
                                            "".join(t + "\n" for t in s["queue1"]["tasks"])))
    wr(DIR / "queue2", "".join(t + "\n" for t in s["queue2"]))
    wr(DIR / "batch", "".join(b + "\n" for b in s["batch"]))
    if s["inflight"] is None:
        rm(DIR / "inflight")
    else:
        wr(DIR / "inflight", "".join(b + "\n" for b in s["inflight"]))
    if s["snapshot"] is None:
        rm(DIR / "snapshot.json")
    else:
        wr(DIR / "snapshot.json", json.dumps(s["snapshot"]))
    wr(DIR / "workers", "".join(f"{w} {st}\n" for w, st in s["workers"].items() if st))
    wr(DIR / "ancestor", "".join("%s %d\n" % (k, v) for k, v in s["ancestor"].items()))
    if s["stop"]:
        wr(DIR / "STOP", "halted\n")
    live = set()
    for n, j in s["jobs"].items():
        live |= {n}
        rec = {k: j[k] for k in ("kind", "worktree", "payload", "token", "retries")}
        # Identity of the running thing. Null until row 7 spawns it -- that is
        # the whole point of recording before spawning, and it is what makes
        # an orphan diagnosable: a record with no pid was never started, a
        # record whose pid is gone died, and `session` is how a died agent is
        # resumed from its transcript rather than restarted from nothing.
        for k in ("host", "pid", "session"):
            rec[k] = j.get(k)
        wr(DIR / "jobs" / (n + ".json"), json.dumps(rec, indent=1))
        if j["started"]:
            wr(DIR / "jobs" / (n + ".started"), j["token"])
        if j["sentinel"] is not None:
            d = dict(j["sentinel"]); d["token"] = j["token"]
            wr(DIR / "jobs" / (n + ".sentinel"), json.dumps(d))
    for f in (DIR / "jobs").glob("*"):
        stem = f.name.split(".")[0]
        if stem not in live:
            rm(f)


def commit_fs(msg):
    git("add", "-A")
    git("commit", "-q", "-m", msg)


def gitlog(n=60):
    r = git("log", "--oneline", "-%d" % n)
    return [l for l in r.stdout.splitlines() if l.strip()]


# --------------------------------------------------------------------------
# rows -- identical logic to flt-loop-viz.py
# --------------------------------------------------------------------------
from flt_loop_rows import *          # noqa: F401,F403  -- the single source of truth
import flt_loop_rows as _R

# The rules describe spawning; the runtime performs it. Installing the hook
# here is what keeps flt_loop_rows.py free of I/O and therefore testable.
flt_loop_rows.SPAWN = do_spawn
evaluate, ROWS, mutate = _R.evaluate, _R.ROWS, _R.mutate


def tick():
    """load -> evaluate -> act -> save -> commit. Nothing persists in memory."""
    s = load()
    before = set(s["jobs"])
    rows, firing = evaluate(s)
    label = ""
    for rid, lbl, _, action in ROWS:
        if rid == firing:
            label = lbl
            action(s)
            break
    # A newly dispatched agent gets a real branch, cut from main at dispatch
    # -- the fleet's ff-only repoint. Forced, because the worktree may still
    # carry a branch from a previous task that has long since landed.
    for n in set(s["jobs"]) - before:
        j = s["jobs"][n]
        if j["kind"] == "agent":
            grepo("branch", "-f", j["worktree"], "main")
    for e in s["email"]:
        with open(DIR / "email.log", "a") as fh:
            fh.write(e + "\n")
    save(s)
    # Only IDLE is silent -- a history of "nothing happened" would bury the
    # history of what did. Everything else commits, PANIC especially: its
    # message is written by the row itself and must reach git before the
    # medic touches anything.
    if firing != 13:
        extra = f" [{s['spawned']}]" if s.get("spawned") else ""
        commit_fs(s["git"][0] if s["git"] else f"row {firing}: {label}{extra}")
    return firing, s


def mutate_fs(job, what):
    s = load()
    # Injections that correspond to real work land in the REPO first, and the
    # state is then read back from it -- rather than the state being asserted
    # and the repo left as decoration.
    if what == "release" or (what == "finish" and job == "merger"):
        # The merger does the WHOLE job now: merge, build, audit. Everything
        # below is work the loop used to sequence across three jobs and five
        # rows, and it is done here because the merger is the one agent that
        # already has the tree checked out at the new main.
        landed = merge_branches(list(s["inflight"] or []))
        s["main"] = head_sha()

        # The audit, done truthfully against the repo rather than asserted:
        # keep queued tasks whose leaf is still open (someone else may have
        # closed it on a branch that just landed), and adopt any open leaf
        # nobody has queued -- the unowned-leaf sweep, which is the only check
        # that finds work no agent ever reported.
        queued = s["queue1"]["tasks"] + s["queue2"]
        leaves = set(open_leaves())
        kept = [t for t in queued if t in leaves]
        dropped = [t for t in queued if t not in leaves]
        # A leaf a LIVE agent is working on is not unowned. Without this the
        # sweep re-queues exactly the leaves currently being proven, and the
        # next dispatch hands the same target to a second worker -- the
        # duplicate-cut failure, arrived at by an audit that was trying to
        # prevent it. Ownership is a live job with that payload, not a record
        # in any list.
        working = {j["payload"] for j in s["jobs"].values()
                   if j["kind"] == "agent" and j["alive"]}
        unowned = [l for l in sorted(leaves) if l not in set(kept) and l not in working]
        s["queue1"] = {"audited": s["main"], "tasks": kept + unowned}
        s["queue2"] = []
        s["snapshot"] = {"sha": s["main"]}

        m = s["jobs"].get("merger")
        if m:
            kill_job(m.get("pid"), m["token"])
            m["alive"] = False
            m["sentinel"] = {"released": s["main"], "merged": landed,
                             "snapshot": s["main"], "audited": s["main"],
                             "panic": False}
        s["inflight"] = None
        s["log"].append(
            "~  merger: merged %s -> %s; built snapshot; audited queue1 "
            "(kept %d, dropped %d already-closed, adopted %d unowned)"
            % (landed or "nothing", s["main"], len(kept), len(dropped), len(unowned)))
        s["git"].append("inject: merger delivered %s (landed %s)"
                        % (s["main"], ", ".join(landed) or "nothing"))
    elif what == "finish" and job in s["jobs"] and s["jobs"][job]["kind"] == "agent":
        j = s["jobs"][job]
        succ = [j["payload"] + "·a", j["payload"] + "·b"]
        agent_commit(j["worktree"], j["payload"], succ)
        kill_job(j.get("pid"), j["token"])
        j["alive"] = False
        j["sentinel"] = {"opened": succ, "panic": False}
        s["log"].append("~  %s committed on its branch: closed %s" % (job, j["payload"]))
    else:
        before = {n: j["alive"] for n, j in s["jobs"].items()}
        mutate(s, job, what)
        # any injection that stops a job stops the REAL one
        for n, j in s["jobs"].items():
            if before.get(n) and not j["alive"]:
                kill_job(j.get("pid"), j["token"])
    save(s)
    if s["git"]:
        commit_fs(s["git"][0])
    else:
        commit_fs("inject: %s%s" % (what, f" ({job})" if job else ""))


# --------------------------------------------------------------------------
# server
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html><html><head><meta charset="utf-8">
<title>flt-loop (filesystem)</title><style>
:root{--bg:#0f1115;--fg:#d8dee9;--dim:#5b6270;--ok:#7fd88f;--fire:#ffcc66;
      --bad:#e06c75;--card:#171a21;--line:#242833}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);
 font:13px/1.55 ui-monospace,Menlo,monospace}
header{padding:9px 15px;border-bottom:1px solid var(--line);display:flex;gap:10px;
 align-items:center;flex-wrap:wrap}
h1{font-size:13px;margin:0;font-weight:600}
button{background:#232833;color:var(--fg);border:1px solid var(--line);border-radius:5px;
 padding:4px 10px;cursor:pointer;font:inherit;font-size:12px}
button:hover{background:#2c3341}button.p{background:#2f4f3a;border-color:#3d6b4d}
.wrap{display:grid;grid-template-columns:280px 1fr 270px;gap:10px;padding:10px;align-items:start}
.card{background:var(--card);border:1px solid var(--line);border-radius:6px;padding:10px;margin-bottom:10px}
.card h2{font-size:10px;margin:0 0 8px;color:var(--dim);text-transform:uppercase;letter-spacing:.09em}
.row{display:flex;justify-content:space-between;gap:6px;padding:1px 0}
.k{color:var(--dim)}.v{text-align:right;word-break:break-all}
table{width:100%;border-collapse:collapse}td{padding:4px 5px;vertical-align:top;border-top:1px solid var(--line)}
tr.no{color:var(--dim)}tr.yes td{color:var(--ok)}
tr.fire td{background:#3a3016;color:var(--fire);font-weight:600}
.id{width:24px;text-align:right;color:var(--dim)}
.why{font-size:10.5px;color:var(--dim);font-style:italic}
.log div{padding:1px 0;border-bottom:1px solid var(--line);font-size:11px}
.chip{display:inline-block;padding:1px 5px;border-radius:4px;background:#232833;margin:1px 2px 1px 0;font-size:11px}
.chip.claimed{background:#2b3550;color:#9db4ff}
.chip.awaiting_merge{background:#4a3520;color:#e0a86c}
.chip.free{background:#26382c;color:#8fd8a0}
.j{border-top:1px solid var(--line);padding:4px 0;font-size:11px}
.j b{color:#9db4ff}.mut{color:var(--dim)}
.ctl{display:flex;gap:5px;align-items:center;padding:2px 0;font-size:11px}
.ctl label{color:var(--dim);flex:1}
.fs{display:grid;grid-template-columns:230px 1fr;gap:10px}
.fl div{padding:2px 5px;cursor:pointer;border-radius:4px;font-size:11.5px}
.fl div:hover{background:#232833}.fl div.sel{background:#2b3550;color:#9db4ff}
pre{margin:0;white-space:pre-wrap;word-break:break-all;font-size:11.5px;color:#c8d0dc;
 max-height:340px;overflow:auto}
</style></head><body>
<header><h1>flt-loop &mdash; filesystem simulator</h1>
<button class="p" onclick="step()">step</button>
<button onclick="run()" id="runbtn">auto</button>
<button onclick="post('/api/seed')">reseed</button>
<span class="mut" id="tick"></span><span class="mut" id="dir"></span></header>
<div class="wrap">
 <div>
  <div class="card"><h2>state (read from disk)</h2><div id="state"></div></div>
  <div class="card"><h2>inject</h2><div id="inject"></div></div>
 </div>
 <div>
  <div class="card"><h2>rows &mdash; first match fires</h2><table id="rows"></table></div>
  <div class="card"><h2>state directory</h2><div class="fs">
    <div class="fl" id="files"></div><pre id="filebody">select a file</pre></div></div>
 </div>
 <div>
  <div class="card"><h2>workers</h2><div id="workers"></div></div>
  <div class="card"><h2>jobs</h2><div id="jobs"></div></div>
  <div class="card"><h2>git log</h2><div class="log" id="git"></div></div>
  <div class="card"><h2>email.log</h2><div class="log" id="email"></div></div>
 </div>
</div>
<script>
let T=0,timer=null,sel=null;
const $=i=>document.getElementById(i);
const api=(p,b)=>fetch(p,b?{method:'POST',headers:{'Content-Type':'application/json'},
  body:JSON.stringify(b)}:{}).then(r=>r.json());
const kv=(k,v)=>`<div class="row"><span class="k">${k}</span><span class="v">${v}</span></div>`;

function render(d){
 const s=d.state;
 $('dir').textContent=d.dir;
 $('state').innerHTML=kv('main',s.main)+
  kv('rebaselined',s.rebaselined+(s.rebaselined===s.main?'':' <span style="color:#e06c75">stale</span>'))+
  kv('snapshot',s.snapshot?s.snapshot.sha+(s.snapshot.sha===s.main?'':' <span style="color:#e06c75">stale</span>'):'<span style="color:#e06c75">none</span>')+
  kv('queue1 AUDITED',s.queue1.audited??'<span style="color:#e06c75">none</span>')+
  kv('queue1',s.queue1.tasks.length)+kv('queue2',s.queue2.length)+
  kv('batch',s.batch.length)+kv('.inflight',s.inflight?s.inflight.length:'&mdash;');
 $('rows').innerHTML=d.rows.map(r=>`<tr class="${r.fires?'fire':(r.matched?'yes':'no')}">
   <td class="id">${r.id}</td><td>${r.label}${r.matched?'':`<div class="why">${r.why}</div>`}</td></tr>`).join('');
 $('workers').innerHTML=Object.entries(s.workers).map(([w,st])=>
   `<div class="row"><span class="k">${w}</span><span class="chip ${st}">${st}</span></div>`).join('');
 const js=Object.entries(s.jobs);
 $('jobs').innerHTML=js.length?js.map(([n,j])=>`<div class="j"><b>${n}</b> <span class="mut">${j.kind}</span><br>
   <span class="mut">${j.token} &middot; retries ${j.retries}</span><br>
   ${j.started?'started':'<span class="mut">not started</span>'} &middot;
   ${j.alive?'alive':'<span class="mut">dead</span>'} &middot;
   ${j.sentinel?'sentinel':'<span class="mut">no sentinel</span>'}
   <div class="ctl"><button onclick="mut('${n}','finish')">finish</button>
   <button onclick="mut('${n}','die')">die</button></div></div>`).join('')
   :'<span class="mut">none</span>';
 $('git').innerHTML=d.gitlog.map(g=>`<div>${g}</div>`).join('');
 $('email').innerHTML=d.email.length?d.email.map(e=>`<div style="color:#e06c75">${e}</div>`).join('')
   :'<span class="mut">none</span>';
 $('files').innerHTML=d.files.map(f=>`<div class="${f===sel?'sel':''}" onclick="openf('${f}')">${f}</div>`).join('');
 $('tick').textContent='tick '+T+(d.firing?'  → row '+d.firing:'');
 if(sel) openf(sel,true);
}
async function openf(f,quiet){sel=f;const d=await api('/api/file?p='+encodeURIComponent(f));
 $('filebody').textContent=d.body; if(!quiet){document.querySelectorAll('.fl div')
 .forEach(e=>e.classList.toggle('sel',e.textContent===f));}}
async function step(){const d=await api('/api/step',{});T++;render(d);}
async function mut(j,w){render(await api('/api/mutate',{job:j,what:w}));}
async function post(p){const d=await api(p,{});T=0;render(d);}
function run(){if(timer){clearInterval(timer);timer=null;$('runbtn').textContent='auto';}
 else{timer=setInterval(step,700);$('runbtn').textContent='stop';}}
$('inject').innerHTML=`
 <div class="ctl"><label>merger delivers (merge+build+audit)</label><button onclick="mut(null,'release')">go</button></div>
 <div class="ctl"><label>merger dies (no sentinel)</label><button onclick="mut(null,'merger_die')">go</button></div>
 <div class="ctl"><label>merger reports OK, main unmoved (illegal)</label><button onclick="mut(null,'merger_noop')">go</button></div>
 <div class="ctl"><label>corrupt: orphan .inflight</label><button onclick="mut(null,'corrupt')">go</button></div>
 <div class="ctl"><label>a job reports PANIC (broken .lake)</label><button onclick="mut(null,'job_panic')">go</button></div>
 <div class="ctl"><label>medic GO</label><button onclick="mut(null,'medic_go')">go</button></div>
 <div class="ctl"><label>medic NO-GO</label><button onclick="mut(null,'medic_nogo')">go</button></div>
 <div class="ctl"><label>STOP file</label><button onclick="mut(null,'stop')">go</button></div>`;
api('/api/state').then(render);
</script></body></html>"""


def take_lock():
    """One writer per state directory.

    Two loops on one directory interleave transitions: each loads, decides
    against a state the other is halfway through changing, and writes back --
    so a row fires twice, or fires against a state that never existed. Nothing
    else in this design defends against it, because every other guarantee is
    about a SINGLE writer crashing, not about two writers racing. It is easy to
    do by accident: leaving a server running and then starting a headless run
    against the same dir is enough, and the symptom looks like the machine
    spontaneously injecting events.

    A stale lock is stolen, not respected -- the loop is expected to be killed
    abruptly, so refusing to start after a crash would be worse than the race.
    """
    lock = DIR / "loop.lock"
    prev = rd(lock)
    if prev and prev.strip().isdigit():
        pid = int(prev.strip())
        try:
            cmd = pathlib.Path("/proc/%d/cmdline" % pid).read_bytes()
        except OSError:
            cmd = b""
        if b"flt-loop-fs.py" in cmd and pid != os.getpid():
            raise SystemExit(
                "refusing to start: loop pid %d already owns %s\n"
                "(stop it first, or use a different --dir)" % (pid, DIR))
    wr(lock, str(os.getpid()) + "\n")


def listing():
    out = []
    for f in sorted(DIR.rglob("*")):
        if ".git" in f.parts or f.is_dir() or f.name.endswith(".tmp"):
            continue
        out.append(str(f.relative_to(DIR)))
    return out


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, body, ctype="application/json"):
        b = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)

    def _payload(self, firing=None):
        s = load()
        rows, f = evaluate(s)
        return json.dumps({"state": s, "rows": rows, "firing": firing or f,
                           "gitlog": gitlog(), "files": listing(), "dir": str(DIR),
                           "email": [e for e in (rd(DIR / "email.log", "") or "").splitlines() if e]})

    def do_GET(self):
        if self.path.startswith("/api/file"):
            from urllib.parse import urlparse, parse_qs
            q = parse_qs(urlparse(self.path).query).get("p", [""])[0]
            tgt = (DIR / q).resolve()
            body = "(not found)"
            if str(tgt).startswith(str(DIR.resolve())) and tgt.is_file():
                body = tgt.read_text()
            self._send(json.dumps({"body": body}))
        elif self.path.startswith("/api/state"):
            self._send(self._payload())
        else:
            self._send(PAGE, "text/html; charset=utf-8")

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        body = json.loads(self.rfile.read(n) or "{}")
        if self.path.endswith("/step"):
            f, _ = tick()
            self._send(self._payload(f))
        elif self.path.endswith("/seed"):
            seed()
            self._send(self._payload())
        elif self.path.endswith("/mutate"):
            mutate_fs(body.get("job"), body.get("what"))
            self._send(self._payload())


def main():
    global DIR
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="/tmp/flt-loop-sim")
    ap.add_argument("--port", type=int, default=8771)
    ap.add_argument("--ticks", type=int, help="headless: run N ticks and exit")
    ap.add_argument("--reseed", action="store_true", help="wipe and reseed first")
    a = ap.parse_args()
    DIR = pathlib.Path(a.dir)
    # Seed ONLY if there is nothing there. A restart must resume from the
    # directory, not erase it -- the whole claim being tested is that the
    # state lives on disk, and a server that wipes on boot would refute it.
    # Keyed on `rebaselined`, NOT on `main`: main stopped being a state file
    # when it moved into the repo, so this guard was testing a path that can
    # no longer exist and silently reseeded on EVERY start -- wiping the state,
    # wiping the repo, and orphaning every job it had spawned.
    if a.reseed or not (DIR / "rebaselined").exists():
        seed()
    else:
        print("resuming existing state in", DIR)
    take_lock()
    if a.ticks:
        for _ in range(a.ticks):
            f, _ = tick()
            print("row", f)
        return
    print(f"flt-loop filesystem simulator on http://127.0.0.1:{a.port}   state: {DIR}")
    HTTPServer(("127.0.0.1", a.port), H).serve_forever()


if __name__ == "__main__":
    main()
