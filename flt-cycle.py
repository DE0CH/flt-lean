#!/usr/bin/env python3
"""The release cycle, as one script. Single entry point for the whole flow.

THE MODEL (Deyao, 2026-07-26). Software-release shaped:

  * The MERGER is the only thing that merges, resolves conflicts, builds, and
    moves `main`. It is self-paced: the instant it finishes a batch it claims
    the next one. Nothing schedules it.
  * `main` moves only to a sha the merger has built GREEN. That commit is a
    RELEASE.
  * The ORCHESTRATOR never merges and never builds. It runs this script, and it
    HAND-EDITS THE QUEUE -- adding tasks when an agent finishes, and correcting
    the queue against reality when a release lands. That is its whole job.

Everything mechanical lives here so the orchestrator is not improvising a
sequence of git commands it can get subtly wrong. Every incident this fleet has
had came from hand-run steps drifting from the intended order.

    ORCHESTRATOR                          MERGER
    ------------                          ------
    done <wt>...    -> merge batch
    (hand-edit queue with new leaves)
                                          claim   -> takes the whole batch
                                          ...merges, resolves, builds green...
                                          release <sha> -> moves main
    preflight       -> everything accounted for?
    release         -> preflight, advance all,
                       seed the allocated,
                       print how many to
                       dispatch
    (hand-edit queue against the release)
    ...fire that many {{FLT_QUEUE_POP}} spawns...

Usage:
    python3 flt-cycle.py done flt-lean-42 [...]   # agent finished -> batch it
    python3 flt-cycle.py release [--dry-run]      # a release landed -> hand out
    python3 flt-cycle.py status
    python3 flt-cycle.py claim                    # MERGER: take the batch
    python3 flt-cycle.py batch-done               # MERGER: batch fully merged
"""
import argparse
import fcntl
import pathlib
import importlib.util
import os
import re
import subprocess
import sys

REPO = "/home/chend/flt-lean"
POOL = os.path.expanduser("~/.flt-worktree-pool")
QUEUE = os.path.expanduser("~/.flt-task-queue")
BATCH = os.path.expanduser("~/.flt-merge-batch")
INFLIGHT = BATCH + ".inflight"
HOOK = os.path.join(REPO, ".claude", "worktree-pool-hook.py")
MERGER_HOST = "nightcrawler"
MERGER_LAKE = "/scratch/chend-flt/flt-staging/.lake/build"
# Shared home volume, readable from every worker host. Home is only 67G and has
# filled up before, so this stays at exactly ONE copy (rsync --delete).
HOME_SEED = os.path.expanduser("~/.flt-release-lake/build")
SCRATCH = "/scratch/chend-flt"
# A donor is "seeded" if its Mathlib olean directory has real content. The
# threshold is deliberately low (the directory holds ~60-90 top-level entries);
# an earlier version of this check used `-gt 100` and so matched NOTHING, which
# is a reminder to compare against a measured number rather than a guessed one.
_MATHLIB_OLEANS = ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib"


def _ensure_packages_cmd(name: str) -> str:
    """Shell snippet: make sure {name} has mathlib oleans, copying host-locally.

    Runs ON the worker host. A no-op (fast `ls`) when packages are already
    there, so it is safe to call on every release for every worktree. If no
    donor exists on that host it FAILS loudly rather than leaving a worktree
    that looks `ready` but would spend two hours rebuilding mathlib -- an
    unseeded worktree is worse than an unavailable one.
    """
    d = f"{SCRATCH}/{name}"
    return (
        f'c=$(ls "{d}/{_MATHLIB_OLEANS}" 2>/dev/null | wc -l); '
        f'if [ "$c" -le 20 ]; then '
        f'  donor=""; '
        f'  for p in {SCRATCH}/flt-lean-* {SCRATCH}/flt-staging; do '
        f'    [ "$p" = "{d}" ] && continue; '
        f'    n=$(ls "$p/{_MATHLIB_OLEANS}" 2>/dev/null | wc -l); '
        f'    [ "$n" -gt 20 ] && {{ donor="$p"; break; }}; '
        f'  done; '
        f'  [ -z "$donor" ] && {{ echo "no mathlib donor on this host" >&2; exit 1; }}; '
        f'  cp -a "$donor/.lake/packages" "{d}/.lake/packages.tmp" && '
        f'  rm -rf "{d}/.lake/packages" && '
        f'  mv "{d}/.lake/packages.tmp" "{d}/.lake/packages"; '
        f'fi'
    )


LAST_RELEASE = os.path.expanduser("~/.flt-last-release")
MALFUNCTION_LOG = os.path.expanduser("~/.flt-malfunction-log")

# Worktrees with no live agent, safe to move under. `claimed`/`suspended` hold a
# live or resumable agent; `reclaiming` is draining and must not come back.
# `batched` = finished, work with the merger, awaiting release.
ADVANCEABLE = {"free", "retired", "ready", "batched"}


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def sh(host, script):
    return run(["ssh", "-o", "BatchMode=yes", host, script])


def load_hook():
    """Import the dispatch hook for its allocator.

    Reusing `pick_free` is deliberate: the capacity rules (free-CPU ranking, the
    25% per-host ceiling, the 10G RAM veto, the fleet-wide limit) were tuned
    against real incidents on shared departmental machines. A second copy here
    would drift from the one that actually hands out slots.
    """
    spec = importlib.util.spec_from_file_location("wpool", HOOK)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["wpool"] = mod
    spec.loader.exec_module(mod)
    return mod


def read_entries(fh):
    out = []
    for line in fh.read().splitlines():
        if line.strip():
            p = line.split()
            out.append((p[0], p[1], p[2:]))
    return out


def write_entries(fh, entries):
    fh.seek(0)
    fh.truncate()
    fh.write("".join(" ".join([n, s] + e) + "\n" for n, s, e in entries))
    fh.flush()
    os.fsync(fh.fileno())


def pool_names():
    try:
        with open(POOL) as fh:
            return {ln.split()[0] for ln in fh if ln.strip()}
    except FileNotFoundError:
        return set()


def read_lines(path):
    try:
        with open(path) as fh:
            return [ln.strip() for ln in fh if ln.strip()]
    except FileNotFoundError:
        return []


def queue_depth():
    try:
        with open(QUEUE) as fh:
            body = fh.read()
    except FileNotFoundError:
        return 0
    return body.count("\n=== TASK ===\n") + 1 if body.strip() else 0


def read_queue_tasks():
    try:
        with open(QUEUE) as fh:
            body = fh.read()
    except FileNotFoundError:
        return []
    return [t for t in body.split("\n=== TASK ===\n") if t.strip()]


def task_targets(task):
    """Names from the task's TARGET: block -- its first line up to a blank line.

    Deliberately NOT the whole prompt: task prompts name sibling leaves under
    'do not touch these', so a whole-prompt match reports phantom targets. That
    exact false positive once left 67 of 92 sorries looking unowned.
    """
    names = set()
    for line in task.splitlines():
        if not line.strip():
            if names:
                break
            continue
        if line.strip().startswith("TARGET"):
            names.update(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line))
        elif names:
            names.update(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line))
        else:
            continue
    return names


def deleted_floating_names():
    """Declarations the merger deleted as floating, from the malfunction log.

    A floating block is a MALFUNCTION (Deyao, 2026-07-26): it is deleted, not
    given a consumer, and any queued work aimed at it is DISCARDED rather than
    re-pointed. Nobody should spend a worker on a declaration that no longer
    exists and was never reachable from the root theorem.
    """
    names = set()
    for line in read_lines(MALFUNCTION_LOG):
        names.update(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line))
        # Tolerate unbackticked logs -- but only for tokens that actually LOOK
        # like Lean names. The old rule was "any identifier of 7+ chars", which
        # on a freeform prose log harvested `because`, `consumer`, `already`,
        # `deliberately` and sixty more English words as declaration names.
        # Requiring a `_` or a `.` costs nothing (essentially every declaration
        # in this tree has one) and removes the entire class.
        for tok in line.replace(",", " ").split():
            if (re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']{6,}", tok)
                    and "/" not in tok and ("_" in tok or "." in tok)):
                names.add(tok)

    # SURVIVOR FILTER (Deyao, 2026-07-26 -- caught by a --dry-run before it
    # destroyed anything). The harvest above is deliberately greedy, and the log
    # is freeform PROSE: it explains deletions, and explaining one names the
    # declarations AROUND it. One entry reads "...because their sole consumer
    # exists_tateParam was correctly re-sorried", and `exists_tateParam` is a
    # LIVE sorried leaf on main -- so the greedy harvest marked it deleted and
    # `prune_queue_for_floating` would have silently dropped its queued task,
    # leaving the leaf unowned and failing a later preflight for no visible
    # reason. Deleting queued work on a prose match is the worst kind of wrong:
    # invisible, and it removes the record of what was lost.
    #
    # The check that cannot be fooled: a DELETED declaration is not in the
    # source. Anything still declared in Fermat/ was not deleted, whatever the
    # log says about it. One scan of the tree, matched against declaration
    # headers only (not docstring prose, which is what caused the problem).
    if not names:
        return names
    alive, decl = set(), re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|"
        r"public\s+|scoped\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
        r"opaque|axiom)\s+([^\s({\[:]+)", re.M)
    try:
        for p in pathlib.Path(REPO, "Fermat").rglob("*.lean"):
            for m in decl.finditer(p.read_text(encoding="utf-8")):
                n = m.group(1)
                alive.add(n)
                alive.add(n.rsplit(".", 1)[-1])
    except OSError:
        return names          # cannot read the tree: keep the greedy answer
    return {n for n in names
            if n not in alive and n.rsplit(".", 1)[-1] not in alive}


def report_superseded_tasks():
    """Warn about queued tasks whose targets are all closed on the new release.

    (Deyao's model calls this "correcting the queue against the release"; it was
    done by eye and got it wrong twice on 2026-07-26, each time costing a worker
    a dispatch into nothing.)

    Three states per target name, and the middle one is what the eyeball check
    kept confusing:

      OPEN    -- a direct sorry on main. Real work.
      PROVEN  -- declared on main, not sorried. The task is superseded.
      ABSENT  -- not declared anywhere on main. Almost always a leaf created on
                 a branch still sitting in the merge batch, i.e. FUTURE work
                 that must be kept. Occasionally a leaf a release deleted.

    The rule that failed was "drop only if every target is PROVEN": a task whose
    targets are one PROVEN and one ABSENT survived it, and the ABSENT one turned
    out to be a cut main had *abandoned* rather than one it had not yet seen.
    So the honest signal is "no target is OPEN" -- that is a task with nothing to
    work on right now, whatever the reason.

    Deliberately REPORTS rather than deletes. ABSENT is genuinely ambiguous
    (unlanded vs. deleted) and only the orchestrator can tell the two apart by
    reading the branch; silently deleting queued work is the failure this file
    already carries one scar from.
    """
    tasks = read_queue_tasks()
    if not tasks:
        return
    decl = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|"
        r"public\s+|scoped\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|"
        r"opaque|axiom)\s+([^\s({\[:]+)", re.M)
    try:
        spec = importlib.util.spec_from_file_location(
            "flt_frontier", os.path.join(REPO, "flt-frontier.py"))
        fr = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(fr)
        declared, sorried = set(), set()
        for p in pathlib.Path(REPO, "Fermat").rglob("*.lean"):
            txt = p.read_text(encoding="utf-8")
            for m in decl.finditer(txt):
                n = m.group(1)
                declared.add(n)
                declared.add(n.rsplit(".", 1)[-1])
            for n, _ in fr.scan(p):
                sorried.add(n)
                sorried.add(n.rsplit(".", 1)[-1])
    except Exception as exc:                       # never block a release
        print(f"  (queue/frontier cross-check skipped: {exc!r})")
        return

    def state(n):
        b = n.rsplit(".", 1)[-1]
        if n in sorried or b in sorried:
            return "OPEN"
        if n in declared or b in declared:
            return "PROVEN"
        return "ABSENT"

    flagged = []
    for i, t in enumerate(tasks):
        tg = sorted(task_targets(t))
        if not tg:
            continue
        st = {n: state(n) for n in tg}
        if "OPEN" not in st.values():
            flagged.append((i, st))
    if not flagged:
        return
    print(f"  QUEUE CHECK: {len(flagged)} task(s) have NO open target on this "
          "release -- read the branch before dispatching them:")
    for i, st in flagged:
        for n, s in sorted(st.items()):
            print(f"    [task {i}] {s:<7} {n}")
    print("    PROVEN -> superseded, delete the task. "
          "ABSENT -> leaf not landed yet (keep) or deleted by a release (drop).")


def prune_queue_for_floating(dry_run=False):
    """Delete queued tasks whose target was deleted as floating. Returns names."""
    gone = deleted_floating_names()
    if not gone:
        return [], 0
    tasks = read_queue_tasks()
    keep, dropped = [], []
    for t in tasks:
        hit = task_targets(t) & gone
        if hit:
            dropped.append(sorted(hit))
        else:
            keep.append(t)
    if dropped and not dry_run:
        with open(QUEUE, "w") as fh:
            fh.write("\n=== TASK ===\n".join(keep))
            if keep:
                fh.write("\n")
    return dropped, len(keep)


# --------------------------------------------------------------------------
# preflight: is everything accounted for?
# --------------------------------------------------------------------------
def inflight_worktrees():
    """Worktree names with a live dispatch record, from ~/.flt-inflight.jsonl."""
    import json
    names = set()
    for ln in read_lines(os.path.expanduser("~/.flt-inflight.jsonl")):
        try:
            rec = json.loads(ln)
        except Exception:
            continue
        wt = rec.get("worktree") or ""
        if wt:
            names.add(os.path.basename(wt.rstrip("/")))
    return names


def cmd_preflight(args):
    """Refuse to start a cycle unless everything is accounted for.

    Three ways a cycle can silently lose work, all of which have happened here
    in one form or another. Each is cheap to detect and expensive to discover
    later, which is exactly the shape that belongs in a gate rather than in a
    habit:

      A. UNMERGED WORK WITH NO ROUTE HOME. A worktree branch holding commits
         that are not in `main`, not in the merge batch, and not held by a live
         agent. `flt-cycle.py release` fast-forwards idle worktrees, and a
         ff-only advance of a diverged branch FAILS -- so the work is not
         destroyed, but it is stranded and invisible, and the next dispatch into
         that slot hard-crashes the allocator. This is the check that would have
         caught the level-21 work that survived only on its own branch.

      B. STATE THAT DOES NOT MATCH REALITY. `claimed` with no inflight record
         means an agent finished and was never written down -- its work will
         never be batched. The converse, an inflight record on a `free`/`ready`
         slot, means a finished agent's record was never cleared, so ownership
         scans will keep crediting it with leaves nobody is working on.

      C. AN UNOWNED SORRY. The loop invariant is that every sorry has an owner
         at all times -- a live agent OR a queued task, since both mean it will
         not be forgotten. Starting a cycle with an unowned leaf means spending
         a whole release cycle without anyone on it.

    Exit 1 if anything blocks. `release` runs this first and refuses without
    --force, because a cycle started on bad accounting is a cycle spent.
    """
    blocking, warnings, fixups = [], [], []

    run(["git", "-C", REPO, "fetch", "origin", "--quiet"])
    with open(POOL) as fh:
        entries = read_entries(fh)
    batch = set(read_lines(BATCH)) | set(read_lines(INFLIGHT))
    live = inflight_worktrees()

    # ---- A. branch accounting -----------------------------------------------
    stranded = []
    for name, state, _ in entries:
        wt = os.path.expanduser(f"~/{name}")
        if not os.path.isdir(wt):
            continue
        exists = run(["git", "-C", REPO, "rev-parse", "--verify",
                      "--quiet", name])
        if exists.returncode != 0:
            continue
        anc = run(["git", "-C", REPO, "merge-base", "--is-ancestor",
                   name, "main"])
        if anc.returncode == 0:
            continue                       # released: fully accounted for
        if name in batch:
            continue                       # queued for the merger
        if state in ("claimed", "suspended") or name in live:
            # An agent is still working, or was stopped mid-task. It missed the
            # merge cutoff; its work goes into a later batch. Legitimate.
            continue
        n = run(["git", "-C", REPO, "rev-list", "--count",
                 f"main..{name}"]).stdout.strip()
        stranded.append((name, state, n))
    if stranded:
        blocking.append(
            f"{len(stranded)} worktree(s) hold unmerged work with no route home "
            "-- not in main, not batched, no live agent:")
        for name, state, n in stranded:
            blocking.append(f"    {name} [{state}] {n} commit(s) ahead of main"
                            f"   -> python3 flt-cycle.py done {name}")

    # ---- B. state consistency -----------------------------------------------
    for name, state, extra in entries:
        wt = os.path.expanduser(f"~/{name}")
        if not os.path.isdir(wt):
            continue
        has_rec = name in live
        # `reclaiming` is a claimed slot that retires when its agent finishes,
        # so it carries a live agent exactly as `claimed` does -- and a missing
        # record means the same defect. Excluding it would let a whole draining
        # cohort finish unrecorded, which is 25 slots at present.
        #
        # But the severity splits on whether the work actually got out, and the
        # two cases want opposite handling:
        if state in ("claimed", "reclaiming") and not has_rec:
            ahead = run(["git", "-C", REPO, "rev-list", "--count",
                         f"main..{name}"]).stdout.strip() or "0"
            if ahead == "0":
                # Work is already in main and the tree is clean: nothing was
                # lost, the slot is just still wearing a working state. That is
                # bookkeeping, not an incident -- correct it and carry on rather
                # than making a human clear it before every cycle. A gate that
                # blocks on harmless drift gets --force'd habitually, and then
                # it stops catching the real thing.
                fixups.append((name, state))
            else:
                blocking.append(
                    f"{name} is `{state}` with NO inflight record and {ahead} "
                    "commit(s) NOT in main -- its agent finished and was never "
                    "written down, so this work is invisible to the merger.  "
                    f"-> python3 flt-cycle.py done {name}")
        if state in ("free", "ready", "retired") and has_rec:
            blocking.append(
                f"{name} is `{state}` but still HAS an inflight record -- "
                "ownership scans will keep crediting it with leaves nobody is "
                "working on.  -> remove its line from ~/.flt-inflight.jsonl")
        if state == "batched" and name not in batch:
            # Same severity split as the `claimed`/`reclaiming` case above. A
            # slot whose branch is entirely in main was merged by the LAST
            # release and simply has not been advanced yet -- `batch-done`
            # clears the inflight file, so every slot of the shipped batch
            # lands here between the release and the next `release` run. That
            # is the normal steady state, not an incident, and blocking on it
            # made the gate fire on 23 slots at once right after Release 3.
            ahead = run(["git", "-C", REPO, "rev-list", "--count",
                         f"main..{name}"]).stdout.strip() or "0"
            if ahead == "0":
                fixups.append((name, state))
            else:
                blocking.append(
                    f"{name} is `batched` with {ahead} commit(s) NOT in main "
                    "and is NOT in the merge batch -- its work will never "
                    f"reach the merger.  -> python3 flt-cycle.py done {name}")
        if state == "suspended" and not extra:
            warnings.append(
                f"{name} is `suspended` with no transcript id -- its work "
                "cannot be resumed")
        if state in ("free", "ready"):
            dirty = run(["git", "-C", wt, "status", "--porcelain"])
            if dirty.stdout.strip():
                blocking.append(
                    f"{name} is `{state}` but its worktree is DIRTY -- "
                    "uncommitted work would be destroyed by the next dispatch")

    # ---- C. sorry ownership -------------------------------------------------
    r = run([sys.executable, os.path.join(REPO, "flt-unowned.py")], cwd=REPO)
    if r.returncode != 0:
        warnings.append(f"ownership scan failed: {r.stderr.strip()[:200]}")
    else:
        unowned = [n for n in r.stdout.split() if n.strip()]
        if unowned:
            blocking.append(
                f"{len(unowned)} direct sorry(s) have NO owner -- neither a "
                "live agent nor a queued task:")
            for n in unowned:
                blocking.append(f"    {n}")
            blocking.append(
                "    -> add a task to ~/.flt-task-queue for each "
                "(queueing IS ownership)")

    # ---- auto-correct harmless state drift ----------------------------------
    if fixups:
        fd = os.open(POOL, os.O_RDWR)
        with os.fdopen(fd, "r+") as pf:
            fcntl.flock(pf, fcntl.LOCK_EX)
            cur = read_entries(pf)
            byname = {n: s for n, s, _ in fixups and cur}
            new_entries = []
            for n, s, e in cur:
                for fn, fs in fixups:
                    if n == fn and s == fs:
                        # `reclaiming` retires (the slot is draining and must not
                        # come back); `claimed` returns to `free`.
                        s = "retired" if fs == "reclaiming" else "free"
                        print(f"FIXED {n}: {fs} -> {s} "
                              "(agent finished, work already in main)")
                        break
                new_entries.append((n, s, e))
            write_entries(pf, new_entries)

    # ---- verdict ------------------------------------------------------------
    for w in warnings:
        print(f"WARN  {w}")
    if blocking:
        print("\nPREFLIGHT FAILED -- not everything is accounted for:\n")
        for b in blocking:
            print(("  " + b) if not b.startswith("    ") else b)
        print("\nFix the above, or re-run `release --force` to proceed anyway.")
        return 1
    print("preflight OK: every branch accounted for, every state consistent, "
          "every sorry owned.")
    return 0


# --------------------------------------------------------------------------
# merge-time lint: a proof silently lost to a conflict resolution
# --------------------------------------------------------------------------
def _sorry_names_at(ref):
    """Direct-sorry names in the tree at `ref`, via the committed scanner.

    Extracts the source to a temp dir and runs flt-frontier.py there rather than
    reimplementing the scan. That scanner already handles the two traps that
    have each produced a wrong answer here: docstrings containing the word
    "sorry" (which once inflated a count to 144 against a true 85), and forward
    attribution (which twice mislabelled a proven declaration as open). At least
    four agents have rebuilt it from scratch and re-derived both.
    """
    import tempfile, shutil
    tmp = tempfile.mkdtemp(prefix="flt-regress-")
    try:
        tar = subprocess.run(["git", "-C", REPO, "archive", ref],
                             capture_output=True)
        if tar.returncode != 0:
            raise SystemExit(f"git archive {ref} failed")
        x = subprocess.run(["tar", "-x", "-C", tmp], input=tar.stdout,
                           capture_output=True)
        if x.returncode != 0:
            raise SystemExit(f"extract failed: {x.stderr.decode()[:200]}")
        shutil.copy(os.path.join(REPO, "flt-frontier.py"), tmp)
        r = subprocess.run([sys.executable, "flt-frontier.py", "--names"],
                           cwd=tmp, capture_output=True, text=True)
        if r.returncode != 0:
            raise SystemExit(f"scan at {ref} failed: {r.stderr[:200]}")
        return set(r.stdout.split())
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def cmd_regress(args):
    """Report declarations that went from PROVEN to SORRIED. MERGER: run this.

    A conflict resolution can keep a statement and drop its proof. The two sides
    have byte-identical signatures, so the merge looks clean, and it is
    INVISIBLE to every ancestry check -- `--is-ancestor` answers true whether or
    not the proof survived. It was found the only way it can be found: by
    comparing bodies. One proof (`archConv_continuousOn`) was lost this way and
    sat lost until an agent happened to notice.

    This is worse than a red build. A red build stops the release; a lost proof
    releases green, and the leaf silently rejoins the frontier -- so a worker is
    eventually dispatched to re-prove something that was already done.

    The invariant: nothing proven at `base` may be sorried now. New sorries are
    fine (a decomposition adds leaves); resurrected ones never are.
    """
    base = args.base or "main"
    # WHICH TREE we scan is the whole correctness of this check (fixed
    # 2026-07-26, after it silently reported success for a merger cycle).
    # `flt-frontier.py` takes its scan root from `__file__`, NOT from cwd — so
    # invoking REPO's copy scans REPO no matter where it is run from. Run from
    # the merger worktree it therefore compared main against main and printed
    # "97 -> 97, no proofs lost" regardless of what the merge had done: a gate
    # that cannot fail, which is worse than no gate.
    #
    # Fix: copy the scanner INTO the tree under test and run it there, exactly
    # as `_sorry_names_at` already does for the base revision.
    import shutil
    tree = os.path.abspath(args.tree or os.getcwd())
    if not os.path.isdir(os.path.join(tree, "Fermat")):
        raise SystemExit(
            f"{tree} is not a project tree (no Fermat/). Pass --tree, or run "
            "from the worktree you want checked.")
    scanner = os.path.join(tree, ".flt-frontier-check.py")
    shutil.copy(os.path.join(REPO, "flt-frontier.py"), scanner)
    try:
        r = run([sys.executable, scanner, "--names"], cwd=tree)
    finally:
        try:
            os.unlink(scanner)
        except OSError:
            pass
    if r.returncode != 0:
        raise SystemExit(f"scan of {tree} failed: {r.stderr[:200]}")
    after = set(r.stdout.split())
    print(f"scanned tree: {tree}")
    before = _sorry_names_at(base)

    lost = sorted(after - before)          # proven at base, sorried now
    gained = sorted(before - after)        # closed since base -- the good news
    print(f"vs {base}: {len(before)} -> {len(after)} direct sorries "
          f"({len(gained)} closed, {len(lost)} newly sorried)")
    if not lost:
        print("no proofs lost.")
        return 0
    print(f"\n{len(lost)} declaration(s) are sorried now but were NOT at {base}:")
    for n in lost:
        print(f"    {n}")
    print("\nEach is EITHER a genuinely new leaf from a decomposition (fine)")
    print("OR a proof dropped by a conflict resolution (a regression). Check the")
    print("branch that touched it: if its signature is unchanged and its body")
    print("became `sorry`, restore the proof before releasing.")
    return 1


# --------------------------------------------------------------------------
# merge-time lint: the namespace-shadowing trap
# --------------------------------------------------------------------------
def cmd_nscheck(args):
    """Flag declarations that create a nested copy of a ROOT namespace.

    One commit cost a full build cycle and produced 100 errors with no error
    anywhere near the cause, so this exists to catch that shape in a diff.

    `theorem IsLocalRing.of_henselianRing_of_isDomain` written INSIDE
    `namespace GaloisRepresentation.Modularity` has the real name
    `GaloisRepresentation.Modularity.IsLocalRing.of_henselianRing_of_isDomain`,
    which CREATES a nested namespace `...Modularity.IsLocalRing`. Lean's name
    resolution prefers the enclosing namespace over the root, so every
    `open IsLocalRing` elsewhere in that namespace silently rebinds to the
    nearly-empty nested one. In one file that made `maximalIdeal`,
    `ResidueField`, `jacobson_eq_maximalIdeal` and friends unknown identifiers;
    the declarations whose STATEMENTS used them then failed to elaborate, so
    every later reference to those reported "unknown identifier" too.

    What makes it worth a mechanical check rather than vigilance: it is GREEN in
    the author's own file and RED only in a different file that merely shares a
    namespace. The author has no reason to build that file, so nothing in their
    workflow can catch it. The fix is a `_root_.` prefix, with no statement
    change and no effect on existing references.

    Heuristic and deliberately noisy-but-cheap: report any declaration header
    whose name is dotted and whose first component is a known root namespace,
    when it appears inside a project `namespace`. Verify each hit by eye.
    """
    # --all scans the WHOLE TREE instead of a diff. The diff mode cannot see a
    # PRE-EXISTING bad declaration -- it only inspects added lines -- and two
    # live instances of this bug were sitting in the tree unflagged for exactly
    # that reason. Diff mode stays the default because it is the cheap
    # per-merge gate; --all is the audit.
    ref = "the whole tree" if getattr(args, "all", False) else (args.ref or "main")
    if getattr(args, "all", False):
        body = []
        for f in sorted((pathlib.Path(REPO) / "Fermat").rglob("*.lean")):
            rel = f.relative_to(REPO)
            ns = None
            for i, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
                if line.startswith("namespace "):
                    ns = line[len("namespace "):].strip()
                elif line.startswith("end ") and ns and line[4:].strip() == ns:
                    ns = None
                # only declarations INSIDE a namespace can shadow a root
                if ns:
                    body.append(f"+{line}\t{rel}:{i}:{ns}")
        diff_out = "\n".join(body)
    else:
        d = run(["git", "-C", REPO, "diff", "-U0", ref])
        if d.returncode != 0:
            raise SystemExit(f"git diff {ref} failed: {d.stderr.strip()}")
        diff_out = d.stdout

    class _D:
        stdout = diff_out
    diff = _D()
    # Root namespaces this project opens and could shadow. Mathlib roots that
    # are commonly `open`ed are the ones that actually bite.
    roots = {"IsLocalRing", "Ideal", "Polynomial", "Matrix", "Module", "Finset",
             "Submodule", "LinearMap", "RingHom", "AlgHom", "Set", "List",
             "Nat", "Int", "Rat", "Real", "Complex", "Filter", "Topology",
             "MeasureTheory", "Function", "Equiv", "Units", "Subgroup",
             "MonoidAlgebra", "AlgebraicGeometry", "CategoryTheory"}
    decl = re.compile(
        r"^\+\s*(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+|"
        r"noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure)\s+"
        r"([A-Za-z_][A-Za-z0-9_.']*)")
    hits = []
    for line in diff.stdout.splitlines():
        line, _, loc = line.partition("\t")
        m = decl.match(line)
        if not m:
            continue
        name = m.group(2)
        if "." not in name:
            continue
        head = name.split(".", 1)[0]
        if head in roots:
            hits.append((m.group(1), name + (f"   [{loc}]" if loc else "")))
    if not hits:
        print(f"nscheck vs {ref}: clean -- no root-namespace shadowing")
        return 0
    print(f"nscheck vs {ref}: {len(hits)} suspicious declaration(s).\n")
    for kind, name in hits:
        print(f"  {kind} {name}")
    print("\nEach of these creates a nested `<current-namespace>."
          f"{hits[0][1].split('.', 1)[0]}`-style namespace if it sits inside a")
    print("project `namespace`. Check whether it does; if so, prefix `_root_.`.")
    print("It will NOT show up in the author's own file -- only in siblings that")
    print("`open` the shadowed root.")
    return 1


# --------------------------------------------------------------------------
# orchestrator: an agent finished
# --------------------------------------------------------------------------
def cmd_done(args):
    """Record finished worktrees in the merge batch. NO MERGING HAPPENS HERE."""
    known = pool_names()
    for n in args.worktrees:
        if known and n not in known:
            # Hard failure: a typo here silently drops an agent's whole run and
            # nothing downstream would ever notice.
            raise SystemExit(f"{n} is not a pool worktree -- refusing to batch")

    fd = os.open(BATCH, os.O_RDWR | os.O_CREAT, 0o644)
    with os.fdopen(fd, "r+") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        have = {ln.strip() for ln in fh if ln.strip()}
        fh.seek(0, os.SEEK_END)
        for n in args.worktrees:
            if n in have:
                print(f"{n}: already batched")
                continue
            fh.write(n + "\n")
            have.add(n)
            print(f"batched {n}")
        fh.flush()
        os.fsync(fh.fileno())

    # The agent has FINISHED, so its dispatch record must go. Leaving it makes
    # every ownership scan credit a finished agent with the leaves its prompt
    # named -- which reads as "covered" and silently strands them for a whole
    # release cycle. This was found the honest way: a scan reported a leaf owned
    # by an agent that had just reported completion.
    import json as _json
    ipath = os.path.expanduser("~/.flt-inflight.jsonl")
    keep, dropped = [], 0
    for ln in read_lines(ipath):
        try:
            rec = _json.loads(ln)
        except Exception:
            continue
        if os.path.basename((rec.get("worktree") or "").rstrip("/")) in args.worktrees:
            dropped += 1
            continue
        keep.append(rec)
    if dropped:
        with open(ipath, "w") as fh:
            fh.write("".join(_json.dumps(r) + "\n" for r in keep))
        print(f"cleared {dropped} inflight record(s)")

    # Move the slot to `batched`: finished, work handed to the merger, NOT yet
    # released. Deliberately not `free` -- its branch is not an ancestor of main
    # until the merger cuts a release, and the dispatch hook hard-crashes on a
    # free-but-diverged slot. `release` promotes it once its work is in.
    fd = os.open(POOL, os.O_RDWR)
    with os.fdopen(fd, "r+") as pf:
        fcntl.flock(pf, fcntl.LOCK_EX)
        cur = read_entries(pf)
        out = []
        for n, s, e in cur:
            # `free`/`retired` included (2026-07-26): `done` is called on
            # whatever finished, and a worktree can already have been released
            # back to `free` by an earlier release while still holding NEW
            # unreleased commits. Leaving it `free` means the next dispatch
            # allocates it, and the ff-only advance then fails on its diverged
            # branch -- or worse, its uncommitted work is destroyed. Preflight
            # caught exactly that.
            if n in args.worktrees and s in ("claimed", "reclaiming",
                                             "free", "retired"):
                # `reclaiming` still retires rather than returning to the pool.
                out.append((n, "batched", e
                            + (["retire"] if s == "reclaiming" else [])))
                print(f"{n}: {s} -> batched")
            else:
                out.append((n, s, e))
        write_entries(pf, out)

    depth = len(read_lines(BATCH))
    print(f"merge batch depth: {depth}")
    print("NEXT: hand-edit the queue with any new leaves this agent reported.")
    return 0


# --------------------------------------------------------------------------
# merger: claim / finish a batch
# --------------------------------------------------------------------------
def cmd_claim(args):
    """Take the whole current batch, atomically. MERGER ONLY.

    Renaming is what makes this safe: an orchestrator `done` that races the
    claim either lands before the rename (in this batch) or recreates the file
    after it (in the next one). Nothing is lost and no batch is ever
    half-merged -- which matters because the merger resolves conflicts by hand,
    and a batch mutating underneath it would invalidate resolutions already
    made.
    """
    if os.path.exists(INFLIGHT):
        left = read_lines(INFLIGHT)
        if left:
            sys.stderr.write(
                f"resuming unfinished batch of {len(left)}; "
                "a previous claim did not complete\n")
            print("\n".join(left))
            return 0
        os.remove(INFLIGHT)
    if not os.path.exists(BATCH):
        return 0
    # O_RDWR, not O_RDONLY: $HOME is NFS, where flock() is emulated with POSIX
    # locks, and an exclusive lock on a read-only fd fails with EBADF.
    fd = os.open(BATCH, os.O_RDWR)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        names = read_lines(BATCH)
        if not names:
            return 0
        os.rename(BATCH, INFLIGHT)
    finally:
        os.close(fd)
    print("\n".join(names))
    return 0


def cmd_batch_done(args):
    if os.path.exists(INFLIGHT):
        os.remove(INFLIGHT)
        print("batch cleared")
    else:
        print("no batch in flight")
    return 0


# --------------------------------------------------------------------------
# orchestrator: a release landed
# --------------------------------------------------------------------------
def tag_release(head):
    """Tag the released sha `v<N>`, N incrementing from the highest existing tag.

    (Deyao, 2026-07-26.) A release was previously identified only by a sha in
    `~/.flt-last-release` -- a file, not a git object, so nothing in the repo
    itself recorded which commits had ever been green. `git branch -f main`
    moves under you, `main@{n}` reflog is local to one checkout, and a sha in a
    report is unsearchable weeks later. An annotated tag is the one identifier
    that is immutable, in the object store, replicated by `git push --tags`, and
    greppable (`git tag --contains <sha>` answers "which release shipped this?").

    Annotated, not lightweight: the tag object carries the date and message, so
    `git tag -n` alone is a release log.

    Never fails the release. Tagging is bookkeeping laid over work already done;
    a tag collision or a read-only object store must not strand a green build
    that every idle worker is waiting on.
    """
    try:
        existing = run(["git", "-C", REPO, "tag", "--list", "v[0-9]*"])
        nums = []
        for t in existing.stdout.split():
            if re.fullmatch(r"v\d+", t):
                nums.append(int(t[1:]))
        nums.sort()
        nxt = (nums[-1] if nums else 0) + 1
        tag = f"v{nxt}"
        prev = f"v{nums[-1]}" if nums else None

        # THE TAG MESSAGE IS THE CHANGELOG (Deyao, 2026-07-26: "i no longer have
        # a useful commit message anymore").
        #
        # `git log main` is ~45% bare "Merge branch 'flt-lean-N' into merger"
        # lines -- 87 of the 196 commits in v4..v5 -- because that is git's
        # default subject and the merger takes it. The real subjects live one
        # level down on the branches ("MazurTorsion: exists_… PROVEN over two
        # new bricks"), so the information is not lost, only buried under the
        # merge commits that carry none.
        #
        # So the annotation lists the NON-MERGE subjects of the range. That
        # makes `git tag -n999 v5` a release note and `git log v4..v5
        # --no-merges` the same view, without asking anyone to change how they
        # commit. Truncated at 200 entries: a tag object is not a database, and
        # the range is always reconstructible.
        body = [f"green release {tag}"]
        if prev:
            log = run(["git", "-C", REPO, "log", "--no-merges",
                       "--format=%s", f"{prev}..{head}"])
            subjects = [s for s in log.stdout.splitlines() if s.strip()]
            body.append("")
            body.append(f"{len(subjects)} non-merge commit(s) since {prev}.")
            body.append("")
            body += [f"  {s}" for s in subjects[:200]]
            if len(subjects) > 200:
                body.append(f"  … {len(subjects) - 200} more "
                            f"(git log --no-merges {prev}..{tag})")
        made = run(["git", "-C", REPO, "tag", "-a", tag, head,
                    "-m", "\n".join(body)])
        if made.returncode != 0:
            print(f"  (tag {tag} not created: "
                  f"{made.stderr.strip()[:120]} -- release continues)")
            return None
        print(f"  tagged {tag} -> {head[:12]}")
        return tag
    except Exception as exc:                       # never block the release
        print(f"  (tagging skipped: {exc!r} -- release continues)")
        return None


def cmd_release(args):
    """Advance everything (cheap), then seed only what the queue justifies.

    TWO PHASES, deliberately asymmetric, because their costs differ by four
    orders of magnitude:

      PHASE 1 -- ADVANCE EVERYTHING. A ff of an already-released branch moves a
      ref and rewrites source files: milliseconds. No reason to be selective.

      PHASE 2 -- SEED ONLY WHAT WILL RUN. `.lake/build` is ~1.8G. Seeding all
      ~90 idle worktrees to run a 5-task queue would move 160G to leave 85 of
      them untouched. So ask the allocator how many workers the QUEUE justifies
      and which machines can take them, and copy only there.

    Hence `free` and `ready` mean different things, and the difference is
    load-bearing:

      free   -- at the release, artifacts STALE. Never dispatched into: that
                hands the agent a from-source rebuild of the whole import cone.
      ready  -- at the release, artifacts seeded from the build that verified
                it. The only state the dispatch hook allocates from.
    """
    # Accounting BEFORE anything moves. A cycle started on bad accounting is a
    # cycle spent: stranded work stays invisible for another few hours, and an
    # unowned leaf goes a whole release with nobody on it.
    if not args.force and not args.dry_run:
        if cmd_preflight(args) != 0:
            print("\nrelease ABORTED by preflight. Nothing was moved.")
            return 1

    run(["git", "-C", REPO, "fetch", "origin", "--quiet"])
    head = run(["git", "-C", REPO, "rev-parse", "main"]).stdout.strip()
    prev = (read_lines(LAST_RELEASE) or [""])[0]
    print(f"release = main @ {head[:12]}"
          + (f"  (previous {prev[:12]})" if prev else ""))
    if prev == head and not args.force:
        print("main has not moved since the last release -- nothing to hand out.")
        print("(--force to re-run anyway)")
        return 0

    # NOT under --dry-run: a tag is a real, pushed, immutable ref, so creating
    # one is exactly the kind of side effect a dry run exists to avoid. Found
    # the honest way -- the first `release --dry-run` after the tagging change
    # minted a real `v4` and it had to be deleted by hand.
    if not args.dry_run:
        tag_release(head)

    hook = load_hook()

    fd = os.open(POOL, os.O_RDWR)
    with os.fdopen(fd, "r+") as pf:
        fcntl.flock(pf, fcntl.LOCK_EX)
        entries = read_entries(pf)

        # ---- PHASE 1 -------------------------------------------------------
        advanced, skipped = [], []
        for i, (name, state, extra) in enumerate(entries):
            if state not in ADVANCEABLE:
                continue
            wt = os.path.expanduser(f"~/{name}")
            if not os.path.isdir(wt):
                continue
            if args.dry_run:
                advanced.append(name)
                continue
            dirty = run(["git", "-C", wt, "status", "--porcelain"])
            if dirty.stdout.strip():
                skipped.append((name, "dirty -- left for inspection"))
                continue
            anc = run(["git", "-C", wt, "merge-base", "--is-ancestor",
                       name, "main"])
            if anc.returncode != 0:
                # Its work is not in this release: still batched, or the merger
                # dropped it. Either way that is a fact to surface, not to hide.
                skipped.append((name, "unreleased (not an ancestor of main)"))
                continue
            ff = run(["git", "-C", wt, "merge", "--ff-only", "main"])
            if ff.returncode != 0:
                skipped.append((name, ff.stderr.strip()[:90]))
                continue
            advanced.append(name)
            # Source moved, so artifacts are now stale: demote to `free` until
            # seeded. Never leave a worktree `ready` across a release.
            #
            # EXCEPT a slot that is draining (Deyao, 2026-07-26 — this was
            # silently resurrecting retired workers). `reclaiming` means "retire
            # this slot when its agent finishes"; `done` records that as the
            # `retire` marker on a `batched` entry, and it is THIS line that has
            # to honour it. Writing `free` unconditionally threw the decision
            # away twice over: a finished drainee came back as `free retire`
            # (state wrong, marker stranded), and an already-`retired` slot --
            # `retired` being in ADVANCEABLE so its source keeps up with main --
            # was reset to `free` at every release, so retirement never stuck at
            # all and the fleet quietly refilled to full size.
            if state == "retired" or "retire" in extra:
                entries[i] = (name, "retired", [x for x in extra
                                                if x != "retire"])
            else:
                entries[i] = (name, "free", extra)
        print(f"phase 1: advanced {len(advanced)}, left alone {len(skipped)}")
        for n, why in skipped[:12]:
            print(f"  skipped {n}: {why}")

        if args.advance_only:
            if not args.dry_run:
                write_entries(pf, entries)
            return 0

        # ---- PHASE 2 -------------------------------------------------------
        # Discard queued work aimed at declarations the merger deleted as
        # floating. A floating block is a malfunction, not a leaf: it is not
        # reachable from the root theorem, it has been deleted, and a worker
        # sent at it would hunt a declaration that no longer exists.
        dropped, remaining = prune_queue_for_floating()
        for names in dropped:
            print(f"  DISCARDED queued task targeting deleted floating "
                  f"block(s): {', '.join(names)}")
        if dropped:
            print(f"  queue: {len(dropped)} task(s) discarded, {remaining} left")

        report_superseded_tasks()

        depth = queue_depth()
        want = args.seed if args.seed is not None else depth
        print(f"phase 2: queue depth {depth}, seeding up to {want}")
        if want <= 0:
            if not args.dry_run:
                write_entries(pf, entries)
            print("nothing queued -- no artifacts copied, nothing to dispatch")
            return 0

        chosen = []
        for _ in range(want):
            # `free`, not `ready`: we are choosing what to PROMOTE. Marking each
            # pick immediately makes the next call see it as taken, and lets
            # `_spend` spread the batch across hosts instead of piling it onto
            # whichever machine measured best first.
            pick = hook.pick_free(entries, candidate_state="free")
            if pick is None:
                print(f"  allocator: no further capacity after {len(chosen)}")
                break
            chosen.append(pick)
            entries = [(n, "ready" if n == pick else s, e)
                       for n, s, e in entries]
        if not chosen:
            if not args.dry_run:
                write_entries(pf, entries)
            print("allocator returned nothing -- capacity exhausted or vetoed")
            return 0
        print(f"  chosen: {' '.join(chosen)}")

        if args.dry_run:
            print("[dry-run] would stage to home and seed the above")
            return 0

        # Stage into a SIBLING, verify, then swap. The old form rsynced
        # `--delete` straight into HOME_SEED from the merger's LIVE build dir --
        # and the merger is a running agent that nothing quiesces. `lake`
        # deletes an output before rebuilding it, so an rsync landing in that
        # window copies a module's `.trace` WITHOUT its `.olean`, and `--delete`
        # then propagates the absence: a torn snapshot DESTROYS the previous
        # good seed instead of being rejected.
        #
        # That is not hypothetical. On 2026-07-28 the seed carried
        # `Modularity/Interface.trace` plus all five `.hash` files and no
        # `Interface.olean` -- the single most expensive module in the tree
        # (~15k lines), so every worktree seeded from it paid a full Interface
        # elaboration on first build. No donor copy existed anywhere on any
        # host, because the good one had been deleted from the seed rather than
        # misplaced.
        #
        # A `.trace` with no `.olean` is the exact signature of the race, and it
        # is cheap to test for, so it is the completeness check: any module that
        # fails it means the snapshot was taken mid-build. Keep the old seed and
        # fail -- a stale complete seed costs one rebuild of what changed; a
        # torn one costs a full elaboration in every worktree it reaches.
        stage = HOME_SEED + ".staging"
        print(f"  staging {MERGER_HOST}:{MERGER_LAKE} -> {HOME_SEED}")
        res = sh(MERGER_HOST,
                 f"mkdir -p {stage} && "
                 f"rsync -a --delete {MERGER_LAKE}/ {stage}/ && "
                 f"torn=$(find {stage} -name '*.trace' | while read t; do "
                 f"  [ -f \"${{t%.trace}}.olean\" ] || echo \"${{t%.trace}}\"; "
                 f"done); "
                 f"if [ -n \"$torn\" ]; then "
                 f"  echo \"TORN SNAPSHOT -- trace without olean:\" >&2; "
                 f"  echo \"$torn\" | sed 's|.*/lean/||' >&2; "
                 f"  rm -rf {stage}; exit 1; "
                 f"fi; "
                 f"rm -rf {HOME_SEED}.old && "
                 f"if [ -d {HOME_SEED} ]; then mv {HOME_SEED} {HOME_SEED}.old; fi && "
                 f"mv {stage} {HOME_SEED} && "
                 f"rm -rf {HOME_SEED}.old && "
                 f"du -sh {HOME_SEED}")
        if res.returncode != 0:
            # Roll back to `free`: unseeded is not `ready`, and dispatching into
            # an unseeded worktree is worse than not dispatching at all.
            entries = [(n, "free" if n in chosen else s, e)
                       for n, s, e in entries]
            write_entries(pf, entries)
            raise SystemExit(f"staging to home FAILED: {res.stderr.strip()}")
        print(f"  {res.stdout.strip()}")

        seeded, failed = [], []
        for name in chosen:
            host = hook._host_of(name)
            if not host:
                failed.append((name, "no host mapping"))
                continue
            dest = f"{SCRATCH}/{name}/.lake/build"
            # `.lake/packages` (mathlib's oleans, ~7.4G) is NOT part of the
            # release seed and never has been: MERGER_LAKE points at
            # `.lake/build`. That was invisible while every pooled worktree had
            # been seeded by hand long ago -- but a worktree created by
            # `git worktree add` starts with an EMPTY `.lake`, so `lake build`
            # there compiles MATHLIB FROM SOURCE: ~2 hours, versus ~3 minutes of
            # local copy. 131 worktrees were in that state on 2026-07-28.
            #
            # packages depend only on the mathlib PIN, not on the release, so
            # they are seeded once per worktree from a donor on the SAME HOST
            # (disk-to-disk, no network) rather than shipped every release.
            r = sh(host, f"mkdir -p {dest} && "
                         f"rsync -a --delete {HOME_SEED}/ {dest}/ && "
                         + _ensure_packages_cmd(name))
            if r.returncode != 0:
                failed.append((name, r.stderr.strip()[:90]))
            else:
                seeded.append(name)
                print(f"  {name} ({host}): seeded")

        if failed:
            bad = {n for n, _ in failed}
            entries = [(n, "free" if n in bad else s, e) for n, s, e in entries]
        write_entries(pf, entries)

    with open(LAST_RELEASE, "w") as fh:
        fh.write(head + "\n")

    print(f"\nready {len(seeded)}, seed-failed {len(failed)}")
    for n, why in failed:
        print(f"  FAILED {n}: {why}")
    print(f"\nNEXT: correct the queue against this release, then fire "
          f"{len(seeded)} spawns with the {{{{FLT_QUEUE_POP}}}} sentinel.")
    return 1 if failed else 0


# --------------------------------------------------------------------------
def cmd_status(args):
    run(["git", "-C", REPO, "fetch", "origin", "--quiet"])
    head = run(["git", "-C", REPO, "rev-parse", "--short", "main"]).stdout.strip()
    prev = (read_lines(LAST_RELEASE) or [""])[0][:12]
    counts = {}
    for _, s, _ in read_entries(open(POOL)):
        counts[s] = counts.get(s, 0) + 1
    batch = read_lines(BATCH)
    inflight = read_lines(INFLIGHT)
    print(f"main (release)   : {head}   handed out: {prev or '(never)'}")
    print(f"pool             : " +
          "  ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    print(f"queue depth      : {queue_depth()}")
    print(f"merge batch      : {len(batch)} waiting"
          + (f", {len(inflight)} IN FLIGHT with the merger" if inflight else ""))
    if batch:
        print("  waiting: " + " ".join(batch))
    if inflight:
        print("  in flight: " + " ".join(inflight))
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("done", help="agent finished -> add to merge batch")
    p.add_argument("worktrees", nargs="+")
    p.set_defaults(fn=cmd_done)

    p = sub.add_parser("release", help="a release landed -> advance and seed")
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("--seed", type=int, help="override the queue-derived count")
    p.add_argument("--advance-only", action="store_true")
    p.add_argument("--force", action="store_true",
                   help="re-run even if main has not moved")
    p.set_defaults(fn=cmd_release)

    p = sub.add_parser("preflight",
                       help="is everything accounted for? (release runs this)")
    p.set_defaults(fn=cmd_preflight)

    p = sub.add_parser("regress",
                       help="MERGER: did a merge drop a proof? (proven -> sorried)")
    p.add_argument("base", nargs="?", help="base ref (default main)")
    p.add_argument("--tree", help="worktree to check (default: cwd)")
    p.set_defaults(fn=cmd_regress)

    p = sub.add_parser("nscheck",
                       help="MERGER: flag root-namespace shadowing in a diff")
    p.add_argument("ref", nargs="?", help="base ref (default main)")
    p.add_argument("--all", action="store_true",
                   help="audit the whole tree, not just a diff")
    p.set_defaults(fn=cmd_nscheck)

    p = sub.add_parser("claim", help="MERGER: take the batch atomically")
    p.set_defaults(fn=cmd_claim)

    p = sub.add_parser("batch-done", help="MERGER: batch fully merged")
    p.set_defaults(fn=cmd_batch_done)

    p = sub.add_parser("status")
    p.set_defaults(fn=cmd_status)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    raise SystemExit(main())
