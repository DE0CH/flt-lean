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
import hashlib
import json
import os
import pathlib
import re
import shlex
import subprocess
import urllib.request
import sys
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
# The fleet's model, pinned. The quota probe deliberately keeps this too: it is
# a negligible cost and Deyao wants the probe answering the "will the API serve
# us" question on exactly the model the fleet uses, so a refusal it sees is a
# refusal the workers would see.
MODEL = "opus[1m]"
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


# Everything a build could possibly read. A commit that touches NONE of these
# cannot change a single olean, so it cannot invalidate a release -- which is
# the whole content of `lean_equiv` below.
LEAN_PATHS = ["Fermat", "Fermat.lean", "ProgressCensus.lean",
              "lakefile.lean", "lake-manifest.json", "lean-toolchain"]


def lean_equiv(sha, main):
    """Would a build of `main` differ from a build of `sha`?

    The loop used to ask `snapshot == main` and `audited == main` as raw string
    equality, which quietly asserts that every commit to main invalidates a
    release. CLAUDE.md says the opposite in as many words: a tooling commit
    cannot make the Lean build red, and the orchestrator is told to put tooling
    straight on main. So the two rules were in direct contradiction, and main
    wins -- tooling commits happen, several a day.

    The consequences were not subtle. Every tooling commit retroactively
    unadopted the current release: row 10 stopped matching, the finished
    merger's record was consumed by nobody, and the loop panicked. It happened
    to the previous medic (`main != rebaselined` held permanently from its own
    source commit onward) and then to me, from the very commit that repaired
    the first three faults -- which is how a fourth fault gets found. It also
    made row 11 declare the snapshot stale, so a commit that changed no Lean
    code at all would order a fresh 4.6 GB rebuild of the whole tree.

    So ask the question that actually matters. A sha is release-equivalent to
    main when it is an ancestor of main and the two agree on every path a build
    reads. The diff is the real test; the ancestry check only fixes the
    direction, so that a sibling branch with an identical `Fermat/` cannot be
    adopted as a release of main.
    """
    if not sha:
        return False
    if sha == main:
        return True
    if git_repo("rev-parse", "--verify", "-q", sha + "^{commit}").returncode:
        return False
    if git_repo("merge-base", "--is-ancestor", sha, main).returncode:
        return False
    return git_repo("diff", "--quiet", sha, main, "--", *LEAN_PATHS).returncode == 0


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


NOTIFY = str(pathlib.Path.home() / ".local" / "bin" / "notify")
# Homebrew's python -- which `/usr/bin/env python3` picks in a NON-interactive
# shell -- reports cafile=None and looks only in ~/homebrew/etc/openssl@3/certs,
# so it never sees the valid system bundle and every send died with
# CERTIFICATE_VERIFY_FAILED. Pointing at the real bundle fixes it with
# verification left ON; the same class of bug as `claude` not being on PATH.
CA_BUNDLE = "/etc/ssl/certs/ca-certificates.crt"


def notify(subject, body=""):
    """Tell Deyao. Uses the existing `notify` CLI -- it DMs him and pushes to
    his phone.

    This replaced a Discord client I had written myself, which was the wrong
    instinct: the working tool already existed, and building a second one meant
    a second thing to configure, to break, and to not notice was broken.

    Logged to notify.log FIRST, before any send. These messages report things
    nobody is watching for, so one that cannot be delivered must still exist
    somewhere. Exit codes from the CLI: 0 sent, 1 Discord refused, 2 not
    configured -- recorded so a silent failure is impossible to mistake for
    delivery.
    """
    try:
        with open(STATE / "notify.log", "a") as fh:
            fh.write("%s | %s\n%s\n" % (time.strftime("%F %T"), subject, body))
    except OSError:
        pass
    env = dict(os.environ, SSL_CERT_FILE=CA_BUNDLE)
    try:
        r = subprocess.run([NOTIFY, "--title", subject[:200], body[:3500]],
                           capture_output=True, text=True, timeout=60, env=env)
        if r.returncode != 0:
            with open(STATE / "notify.log", "a") as fh:
                fh.write("  !! notify exit %d: %s\n"
                         % (r.returncode, (r.stderr or r.stdout).strip()[:300]))
        return r.returncode == 0
    except Exception as e:
        try:
            with open(STATE / "notify.log", "a") as fh:
                fh.write("  !! notify failed: %r\n" % (e,))
        except OSError:
            pass
        return False


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

    {"token": "%(token)s",
     "queue":     ["<full text of a task for a future agent>", ...],
     "to_merger": ["<one thing the next merge worker must know>", ...],
     "to_medic":  ""}

NO HUMAN READS ANY OF THIS. NOBODY WILL FOLLOW UP.
Not the loop -- it is a Python state machine. Not a reviewer -- there is no
review step. Not Deyao -- he is not watching, and nothing you write reaches him.

THE CHAIN OF OWNERSHIP, since the top of it is not reachable from here:

    Deyao -> medic -> the loop -> the MERGE WORKER -> you

  * The MERGE WORKER owns the project and every decision in it while the loop
    is running correctly. Anything above your task -- a design choice, a
    conflict with another branch, a queued task you can see is now wrong --
    goes to it in `to_merger`, and it decides. That is the whole of your
    escalation path.
  * A MEDIC owns the loop, and only appears when the LOOP ITSELF is broken.
    `to_medic` summons one. It is not a way to reach anybody about your task.
  * DEYAO is reachable only by a medic's NO-GO verdict, only when the sole way
    forward is destructive or unsafe. Nothing you write can trigger one, and
    nothing you write reaches him.

So these do not exist as options, and produce nothing but a lost task:
"I cannot decide", "this needs a human", "flagging for review", "someone should
check this", "TODO: confirm", or leaving a choice open for later. Nobody will
make it. An unmade decision stays unmade forever and the work is thrown away.
Caveats addressed to a reader, questions, and requests for approval all go
nowhere.

WHEN YOU ARE GENUINELY UNCERTAIN, DECIDE ANYWAY. Take the best-supported option
on the evidence you have, do the work, and record what you assumed and what
would change your mind -- in the commit message, and in `to_merger` if it bears
on the merge. A decision made on stated assumptions can be checked and reversed
by whoever comes next; a question addressed to nobody cannot. If two readings
are equally defensible, pick one, say which and why, and move.

`to_medic` is not an escape hatch for hard mathematics or for uncertainty. It
means the LOOP is broken, and it summons a repair agent, not a person.

DO NOT WRITE A REPORT. There is no reader for one. The loop is a Python state
machine; it cannot read prose, cannot summarise, and cannot pass anything on
that is not addressed to a specific recipient. A summary field would be thrown
away, so anything you want acted on must go in one of the three lists below,
each of which is delivered to a named reader:

  * `token` -- copy it verbatim or the loop ignores the whole file.

  * `queue` -- tasks to be dispatched to future agents. Each entry is the FULL
    prompt text for that task, written the way you would want to receive it:
    name the declaration, the file, what is known, what was tried. Use
    {{FLT_WORKTREE}} where the worktree path belongs. These go into queue2 and
    are audited against main at the next release before anyone is sent at them.
    Leave the list empty if you opened nothing.

  * `to_merger` -- things the next merge worker must know: a branch that will
    conflict and how you would resolve it, a declaration you renamed or moved,
    a file you split, a leaf you proved that makes a queued task obsolete. It
    is the only channel to the merger; it does not read your commits.

  * `to_medic` -- ONE sentence, and only if the LOOP is broken. Setting it is a
    panic: the loop stops dispatching and hands the state to a repair agent. It
    is NOT a verdict on the mathematics. A proof that did not go through, a
    leaf that turned out to be FALSE AS STATED, a target already proven
    elsewhere -- all ordinary results, leave it "". A refutation with an
    explicit counterexample is a FULL SUCCESS. Set it only if you could not
    operate at all: no .lake where you were told to look, the worktree on a
    branch nobody claimed, a missing or torn tree.

A LESSON WORTH KEEPING GOES IN A FILE, NOT IN A MESSAGE
If you learned something that should outlive this task -- a trap in the build,
a fact about the fleet, a technique that worked -- edit CLAUDE.md or the memory
files in your worktree directly and commit it with your work. The merge worker
merges your branch into main, so the lesson lands where the next agent will
actually read it. A note to the merger is for THIS merge; an edit to CLAUDE.md
is for every agent after you.

If you stop without writing the sentinel, the loop concludes you died and
starts a replacement. Write it even when the news is bad.

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
        inbox = j.get("inbox") or []
        body = MERGER_TASK % {"inflight": ", ".join(j["payload"]) or "(nothing)",
                              "snapshot": SNAPSHOT, "state": STATE,
                              "snapshot_sha": SNAPSHOT_SHA,
                              "sentinel": STATE / "jobs" / (name + ".sentinel"),
                              "token": j["token"],
                              "inbox": "\n".join("  * " + m for m in inbox) or "  (none)"}
    elif kind == "medic":
        body = MEDIC_TASK % {"reason": body, "state": STATE,
                             "src": pathlib.Path(__file__).resolve()}
    return head + body


MERGER_TASK = """\
You are the merge worker. You produce EVERY derived fact about main, and the
loop refuses your release if any is missing. Work in ~/flt-staging.

YOU OWN THIS PROJECT AND EVERY DECISION IN IT
The chain is: Deyao -> medic -> the loop -> YOU -> the prover agents. While the
loop is running correctly you are the top of it. Not a person -- no human reads
any of this and nobody is waiting to approve anything.

Full ownership means full: the mathematics, the architecture, what gets merged,
what gets declined, what the queue should contain, what the tree should look
like. Workers defer decisions upward to you and they stop here. Nobody
arbitrates them later, so an unmade decision is not deferred, it is lost. Make
the call, act on it, and put what you decided and why in the commit message --
that message is the record, and the next merge worker reads it.

You may also edit CLAUDE.md, the doctrine and the memory files as part of a
merge. A lesson belongs in the tree where the next agent reads it, and you are
the one who can put it on main.

THE ONE THING YOU DO NOT OWN IS THE LOOP ITSELF
If the fault is in the machinery rather than the mathematics -- the transition
table cannot express the state, a row is wrong, the loop needs stopping or
restarting, the state on disk contradicts itself -- do NOT work around it. Set
"to_medic" in your sentinel to one sentence naming the fault. That halts
dispatch and summons a medic, which owns the loop the way you own the project.
Working around a broken loop hides it; the next merge worker inherits it.

NOTES ADDRESSED TO YOU BY THE AGENTS WHOSE BRANCHES YOU ARE MERGING
%(inbox)s
These are the only channel those agents have to you -- they are gone, and you
do not read their commits. Renames, splits, expected conflicts and now-obsolete
queued tasks show up here and nowhere else.

DO ALL FIVE, IN ORDER
 1. Merge these branches into main: %(inflight)s
    After EACH merge run `git diff --stat HEAD^1 HEAD`. A merge can report
    success and carry nothing -- and a dropped payload still builds. Empty for
    a branch that changed files means reset and re-merge. Decline a branch
    that will not reconcile and say so; declining is a result, not a panic.

    EVERY branch on that list must end up an ANCESTOR of the main you publish,
    and that is the loop's only receipt for it. A merge gives you one. So does
    a decline, PROVIDED you record it the way CLAUDE.md's class-7 section
    prescribes -- `git checkout HEAD -- <the files>`, then commit the merge, so
    the diff against the first parent is empty ON PURPOSE and the commit
    message says the payload was declined. `git merge --abort` and walking away
    is NOT a decline: it leaves no receipt.

    A branch you neither merge nor decline that way comes back to you, or to
    the next merge worker, next release -- the loop folds the remainder of your
    claim back into the batch. That is deliberate, and it is why running out of
    time is safe: merge what you can, publish, and the rest is queued again
    rather than lost. It used to be lost. A merger that merged 18 of 55
    branches and was killed before reporting had the other 37 silently
    discharged, and 78 worktrees' work was stranded that way in one day.
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

FINALLY, write your sentinel to %(sentinel)s as your last act:

    {"token": "%(token)s", "queue": [], "to_merger": [], "to_medic": ""}

  * `queue`     -- tasks for future agents, full prompt text each.
  * `to_merger` -- notes for the NEXT merge worker: what you declined and why,
                   a conflict you resolved in a way that will recur, a rename
                   that later branches will trip on.
  * `to_medic`  -- one sentence, ONLY for a fault in the loop itself. Declining
                   a branch, a red build, a leaf that turned out false: all
                   ordinary results of owning the project, leave it "".
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
the table. The fleet is untouched by any of this: jobs are owned by their
records, not by process lineage.

EDIT THE SOURCE AND JUST LEAVE IT THERE. Do NOT restart the loop by hand. The
tick after your record is consumed, the running loop notices the source changed,
runs `--dry-run` against it as a smoke test, and re-execs onto it -- same pid,
same lock, same loop.out. Your last edit is the one it adopts, so a fix you make
after a hand-restart would be missed, which is exactly the fault that produced
THIS medic: the previous one restarted the loop at 05:02:42, found a further
fault from its own commit, fixed it at 05:07:16 into the source of a process
five minutes into its run, and the old table panicked on the next tick for the
reason the new one no longer could. If the dry-run fails, the loop keeps the old
table and emails; check loop.out before assuming your edit was picked up.

Write your sentinel LAST, so the loop holds in SAFE MODE until you finish.

YOU OWN EVERYTHING RIGHT NOW
The chain is: Deyao -> YOU -> the loop -> the merge worker -> the prover
agents. While the loop runs correctly the merge worker owns the project. It is
not running correctly -- that is why you exist -- so all of it is yours until
you hand it back. Nobody is above you but Deyao, he is not watching, and there
is no review step. Decide and act.

Your ownership includes the machinery itself, which nobody below you may touch:
the transition table, flt-loop.py, the state on disk, the loop process, and any
job process on any worker host. If the right repair is to rewrite a row, kill
the loop and start a corrected one, or stop a runaway job, do it. A state the
table cannot express is a defect in the TABLE, not an event to be worked
around.

Your sentinel takes an extra field: "go": true or false.

GO -- the loop may resume. Taken literally: it clears the panic that produced
you and returns to normal, so do not answer GO with the fault still live.

NO-GO -- THE ONLY CHANNEL TO A HUMAN IN THIS ENTIRE SYSTEM. It halts everything
and fetches Deyao. Reserve it for the one case your ownership stops short of:
the only way forward is DESTRUCTIVE, IRREVERSIBLE or otherwise unsafe --
discarding work that cannot be recovered, force-moving a ref over commits that
exist nowhere else, deleting a worktree with uncommitted work in it, anything
you cannot undo if your diagnosis is wrong. That is his call, not yours, and it
is the only thing that is.

It is NOT for a hard problem, for uncertainty, or for a repair you would rather
have confirmed. Those are yours: make them on the best evidence available and
record what you assumed in "why".

Before answering NO-GO, DM him yourself as well:

    SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt notify --title "..." "..."

The verdict reaches him through the loop, but only once the loop reads your
sentinel; the DM reaches his phone immediately, and a NO-GO means everything is
stopped until he acts.

You may also act BEYOND what a verdict can express, and should when the
situation needs it: kill the loop process, stop job processes that are doing
damage, or leave the fleet halted deliberately. A verdict is a message; those
are actions, and some faults need the action rather than the message. Say in
"why" exactly what you stopped and what state you left behind, because whoever
resumes has only that to go on.

Put your explanation in "why" either way. Write it for someone who was not
here, because on a NO-GO that is exactly who reads it.
"""


# ------------------------------------------------------------------- quota
# The account's session limit is a real resource the loop must respect, and it
# cannot see it any other way: a refused spawn and a job that started and
# exited quickly look identical from outside. The ONE place the difference is
# visible is the job's own log, which carries the refusal verbatim along with
# the reset time.
#
# Twice on 2026-07-30 the loop spent hours relaunching into a wall -- ~17
# attempts a minute, ~500 in half an hour -- because nothing recorded that the
# door was shut. This makes "the door is shut, and until when" a piece of
# state, so the wait becomes a deliberate idle rather than a retry storm.
LIMIT_MARK = "session limit"


def parse_reset(text):
    """'resets 9:50pm (Europe/London)' -> epoch of the next such local time."""
    m = re.search(r"resets\s+(\d{1,2}):(\d{2})\s*([ap]m)", text, re.I)
    if not m:
        return time.time() + 3600           # unknown wording: wait an hour
    h, mi, ap = int(m.group(1)), int(m.group(2)), m.group(3).lower()
    h = h % 12 + (12 if ap == "pm" else 0)
    now = time.localtime()
    e = time.mktime((now.tm_year, now.tm_mon, now.tm_mday, h, mi, 0, 0, 0, -1))
    return e + 86400 if e <= time.time() else e


PROBE_EVERY = 300        # seconds between "is the door open yet" checks
CREDS = pathlib.Path.home() / ".claude" / ".credentials.json"


def creds_stamp():
    try:
        return int(CREDS.stat().st_mtime)
    except OSError:
        return 0


def probe_quota():
    """Ask the API, with the key currently on disk, whether it will serve us.

    NOT a timer. The refusal message carries a reset time, but that time
    describes whichever ACCOUNT was live when it was printed, and a rotator
    swaps ~/.claude/.credentials.json underneath us from a bank of accounts. So
    the deadline is unreliable in BOTH directions: it can expire while we are
    still refused, and -- what happened here -- remain in the future long after
    a rotation has already made us servable. The logs even disagreed with each
    other, 9:30pm against 9:50pm.

    Everywhere else this loop observes rather than believes: `ancestor` asks
    git, `alive` asks /proc, `main` asks the repo. This applies the same rule
    to the one place that was trusting a string.
    """
    result = STATE / "quota-probe.json"
    if result.exists():
        rm(result)
        rm(STATE / "quota-probe")
        return True
    st = STATE / "quota-probe"
    last = float((rd(st, "") or "0").strip() or 0)
    if time.time() - last < PROBE_EVERY:
        return False
    wr(st, str(time.time()))
    inner = ('exec -a flt-job-quotaprobe %s --dangerously-skip-permissions -p %s'
             % (shlex.quote(CLAUDE),
                shlex.quote('Write the file %s containing exactly {"ok":true} '
                            'and nothing else, then stop.' % result)))
    try:
        ssh(sorted(set(worker_hosts().values()))[0],
            "setsid --fork nohup bash -c %s >%s 2>&1 </dev/null"
            % (shlex.quote(inner),
               shlex.quote(str(STATE / "joblogs" / "quota-probe.log"))),
            timeout=30)
    except Exception:
        pass
    return False


def quota_until():
    """Are we currently refused? A fact to be re-checked, not a sentence to serve.

    The state file records only THAT we were refused and which credential was
    live at the time. It clears when a probe succeeds. A rotation (the
    credentials file changing underneath us) forces the next probe immediately
    rather than waiting out the interval, because a new account is the most
    likely reason the answer has changed.
    """
    v = rd(STATE / "quota-blocked")
    if not v:
        return None
    try:
        d = json.loads(v)
    except json.JSONDecodeError:
        rm(STATE / "quota-blocked")
        return None
    if d.get("creds") and d["creds"] != creds_stamp():
        rm(STATE / "quota-probe")          # rotated: probe now, do not wait
    if probe_quota():
        rm(STATE / "quota-blocked")
        notify("flt-loop: quota available again, resuming",
              "A probe with the credential now on disk was served, so the "
              "block was lifted on evidence. Spawning has resumed.")
        return None
    return d.get("since", 1)               # truthy == still blocked


def note_quota(reset_epoch, why):
    wr(STATE / "quota-blocked",
       json.dumps({"since": int(time.time()), "creds": creds_stamp(),
                   "log_said": int(reset_epoch)}))
    notify("flt-loop: quota exhausted, idling",
          "Spawning is being refused. The loop is IDLING rather than retrying, "
          "and probes every %ds with whatever credential is on disk -- the "
          "reset time in the message is only a hint, since the rotator can "
          "swap accounts underneath us.\n\n%s" % (PROBE_EVERY, why))


def refused(name, j):
    """Did this job's log say it was refused? Only asked about dead-looking jobs.

    The log is EVIDENCE, and evidence has to be consumed. A job refused an hour
    ago keeps "session limit" in its log forever, and a refusal does not change
    the job's token, so the same file is read again on every tick. That made
    the block un-clearable: a probe would lift it and the very same load() pass
    would re-arm it from a stale line -- both emails landed in the same second,
    21:55:57, and the fleet never resumed.

    So the file is moved aside once it has been acted on. The history is kept
    (renamed, not deleted) but it is out of the evidence path, and only a
    genuinely new refusal -- written by a fresh spawn attempt -- can block again.
    """
    log = STATE / "joblogs" / ("%s-%s.log" % (name, j["token"]))
    t = rd(log, "") or ""
    if LIMIT_MARK not in t:
        return None
    try:
        log.rename(log.with_suffix(".log.refused-%d" % time.time()))
    except OSError:
        rm(log)
    return t


# --------------------------------------------------------------- spawn
GRACE = 120     # seconds a freshly spawned job is presumed alive


def do_spawn(s, name, j):
    """Start a real, detached claude process on the worker host."""
    # Stamped BEFORE the ssh, so the grace period covers the launch itself.
    j["spawned_at"] = time.time()
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
    # --model is PINNED rather than inherited. Without it every job takes
    # whatever ~/.claude/settings.json happens to say, so a single edit to that
    # file silently re-models the entire fleet -- and the model would appear in
    # no job record, no prompt and no log, making the change invisible after
    # the fact. There is precedent for that divergence here: the monitor
    # already runs under its own CLAUDE_CONFIG_DIR with a different model.
    # Recorded on the job too, so what ran is auditable from the state alone.
    j["model"] = MODEL
    inner = ("cd %s 2>/dev/null || cd %s; "
             "exec -a flt-job-%s %s --model %s --dangerously-skip-permissions "
             "-p \"$(cat %s)\""
             % (shlex.quote(str(wt)), shlex.quote(str(REPO)), j["token"],
                shlex.quote(CLAUDE), shlex.quote(MODEL), shlex.quote(str(pf))))
    cmd = ("setsid --fork nohup bash -c %s >%s 2>&1 </dev/null"
           % (shlex.quote(inner), shlex.quote(str(log))))
    try:
        ssh(host, cmd, timeout=45)
    except Exception as e:
        note = "spawn of %s on %s failed: %s" % (name, host, e)
        notify("flt-loop: spawn failed", note)
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
        # A freshly spawned job is presumed alive until the grace period
        # expires. The liveness sweep is cached for ALIVE_CACHE seconds, so a
        # job spawned at T is otherwise judged against a token snapshot taken
        # BEFORE it existed -- it reads as dead on its very first tick, and
        # `died` (started, not alive, no sentinel) fires immediately.
        #
        # That is what was killing every merge worker: spawned, declared dead
        # ~12s later, record dropped, recreated, respawned -- seven times, with
        # no release possible and the batch growing the whole while. Agents hid
        # it because their death path respawns them, so the churn looked like
        # ordinary turnover.
        fresh = time.time() - (j.get("spawned_at") or 0) < GRACE
        j["alive"] = (j["token"] in tokens) or (j["started"] and fresh)
        # A job that is started, not alive and has no sentinel would be read as
        # DEAD and re-dispatched. Before believing that, ask its log whether it
        # ever got to run: a refusal is not a death, and treating it as one is
        # what produced the retry storm.
        if j["started"] and not j["alive"] and not j["sentinel"]:
            txt = refused(n, j)
            if txt:
                if not quota_until():
                    note_quota(parse_reset(txt), "%s (%s) was refused: %s"
                               % (n, j["kind"], txt.strip().splitlines()[0]))
                j["started"] = False       # unspawned again, retried after the block
                j["alive"] = False
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
        # Derived here, not in the rows: "is this release still current" is a
        # question about the git tree, and the rows are shared with a simulator
        # that has no tree. They get the answer, not the means of computing it.
        "snapshot_current": bool(snap) and lean_equiv(snap["sha"], sha),
        "audit_current": lean_equiv(aud, sha),
        "queue1": {"audited": aud, "tasks": split_tasks("\n".join(q1))},
        "queue2": split_tasks(rd(STATE / "queue2", "") or ""),
        # Messages agents addressed to the merge worker. They are held here
        # because an agent finishing and the next merger being created are
        # minutes to hours apart, and the agent is long gone by then.
        "merger_inbox": [l for l in (rd(STATE / "merger-inbox", "") or "").splitlines()
                         if l.strip()],
        "batch": [b for b in (rd(STATE / "batch", "") or "").splitlines() if b.strip()],
        "inflight": ([b for b in (rd(STATE / "inflight") or "").splitlines() if b.strip()]
                     if (STATE / "inflight").exists() else None),
        "jobs": jobs,
        "workers": {w: (stored.get(w) or None) for w in wh},
        "worker_host": wh,
        "ancestor": anc,
        "healthy": {k: v == "1" for k, v in _pairs("healthy").items()},
        "hosts": refresh_hosts(),
        "quota_until": quota_until(),
        "log": [], "git": [], "email": [],
    }


def save(s):
    wr(STATE / "rebaselined", s["rebaselined"])
    wr(STATE / "queue1", "AUDITED: %s\n%s" % (
        s["queue1"]["audited"] or "none",
        "\n=== TASK ===\n".join(s["queue1"]["tasks"])))
    wr(STATE / "queue2", "\n=== TASK ===\n".join(s["queue2"]))
    wr(STATE / "merger-inbox", "".join(m + "\n" for m in s["merger_inbox"]))
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
        # spawned_at MUST be here. do_spawn stamps it, but if it is not
        # persisted the record comes back with None, `now - 0` is always older
        # than GRACE, and every freshly spawned job is judged dead on its very
        # first tick -- spawn, "died", re-dispatch, spawn, every ~15s, which is
        # exactly the churn the grace period exists to stop.
        rec = {k: j.get(k) for k in ("kind", "worktree", "payload", "token",
                                     "retries", "host", "pid", "session",
                                     "takeover", "spawned_at", "model", "inbox")}
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


# ------------------------------------------------------------ source drift
# The loop's own source. A medic is explicitly invited to edit these files --
# "a state its table cannot express is a defect in the table" -- but Python
# read them once, at startup, so an edit changes nothing about the process that
# is running. That gap produced fault 5, and it is the worst-shaped fault yet
# because the transition trace LIES: `git log` in the state dir shows rows
# firing out of a table that no longer exists on disk, and the next medic reads
# a repaired guard, dry-runs it, watches it match, and cannot explain the panic.
#
# It happened exactly as designed to happen. The previous medic fixed faults
# 1-3, restarted the loop at 05:02:42, then found fault 4 from its own commit
# and fixed THAT at 05:07:16 -- into the source of a process that had been
# running for five minutes. Its GO was applied by the old code, which panicked
# on the next tick for precisely the reason the new code no longer can.
#
# So the loop picks its own repairs up. It cannot do this while a medic is in
# flight (a medic saves a file many times, and half of those states are
# incoherent) -- but the tick after the medic's record is consumed is exactly
# right: SAFE MODE means nothing operational ran on the stale table in between.
SOURCES = [pathlib.Path(__file__).resolve(),
           pathlib.Path(flt_loop_rows.__file__).resolve()]


def source_digest():
    """Digest of the source, or None if any of it does not compile.

    A digest of the BYTES would re-exec on a comment change, which is harmless
    but noisy; a digest that refuses to be taken while the tree does not parse
    is what keeps a mid-save file from being adopted. Cheap enough to do every
    tick: two files, a few tens of KB.
    """
    h = hashlib.sha256()
    for p in SOURCES:
        try:
            src = p.read_bytes()
            compile(src, str(p), "exec")
        except (OSError, SyntaxError):
            return None
        h.update(src)
    return h.hexdigest()


def adopt_source(startup_digest):
    """Re-exec onto edited source, if it survives a dry tick. Returns on refusal.

    Gated on a real `--dry-run` in a subprocess, not just on compiling. The
    failure this replaces is a silent one, and swapping it for "the loop dies
    on import of a source nobody ran" would only move the silence. A dry tick
    exercises load(), every guard, and the ssh sweep -- if that cannot complete,
    the edit is not ready and staying on the old table is the safer wrong.

    os.execv keeps the pid, so loop.lock stays valid and take_lock() sees its
    own number; it keeps fd 1 and 2, so the same loop.out carries on; and it
    keeps cwd, which is what makes the relative script path resolve.
    """
    now = source_digest()
    if now is None or now == startup_digest:
        return
    try:
        r = subprocess.run([sys.executable, str(SOURCES[0]), "--dry-run"],
                           cwd=str(REPO), capture_output=True, text=True,
                           timeout=300)
    except subprocess.TimeoutExpired:
        print("%s source changed but --dry-run did not finish in 300s; staying "
              "on the old table" % time.strftime("%T"))
        return
    if r.returncode:
        print("%s source changed but --dry-run FAILED; staying on the old "
              "table: %s" % (time.strftime("%T"), (r.stderr or "").strip()[-300:]))
        notify("flt-loop: edited source refused",
              "flt-loop source changed on disk but `--dry-run` exited %d, so the "
              "running loop did NOT adopt it and is still executing the source it "
              "started with. Fix the edit; the loop will pick it up on the next "
              "tick.\n\n%s" % (r.returncode, (r.stderr or "")[-3000:]))
        return
    print("%s source changed and dry-runs clean -> re-exec onto it"
          % time.strftime("%T"))
    commit_state("loop re-exec onto edited source (%s)" % now[:12])
    sys.stdout.flush()
    os.execv(sys.executable, [sys.executable, "-u", str(SOURCES[0])] + sys.argv[1:])


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
        notify("flt-loop: " + e.split(":")[0][:60], e)
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
    startup_digest = source_digest()
    print("flt-loop running, pid %d, state %s, source %s"
          % (os.getpid(), STATE, (startup_digest or "UNPARSEABLE")[:12]))
    while True:
        try:
            f, lbl, s, _ = tick()
            if f not in QUIET:
                print("%s row %-3d %s" % (time.strftime("%T"), f, lbl))
            if s.get("halted"):
                print("STOP -- exiting")
                return
            # AFTER the tick and only with no medic record: a medic's edits are
            # not coherent until it has finished, and SAFE MODE means nothing
            # operational is running on the stale table meanwhile. Does not
            # return if it re-execs.
            if "medic" not in s["jobs"]:
                adopt_source(startup_digest)
        except Exception as e:
            notify("flt-loop: tick raised", repr(e))
            time.sleep(30)
        if a.once:
            return
        time.sleep(TICK)


if __name__ == "__main__":
    main()
