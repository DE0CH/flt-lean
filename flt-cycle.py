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
    release         -> advance all,
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
LAST_RELEASE = os.path.expanduser("~/.flt-last-release")
MALFUNCTION_LOG = os.path.expanduser("~/.flt-malfunction-log")

# Worktrees with no live agent, safe to move under. `claimed`/`suspended` hold a
# live or resumable agent; `reclaiming` is draining and must not come back.
ADVANCEABLE = {"free", "retired", "ready"}


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
        # tolerate unbackticked logs: take dotted/underscored identifiers
        for tok in line.replace(",", " ").split():
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']{6,}", tok) and "/" not in tok:
                names.add(tok)
    return names


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
    run(["git", "-C", REPO, "fetch", "origin", "--quiet"])
    head = run(["git", "-C", REPO, "rev-parse", "main"]).stdout.strip()
    prev = (read_lines(LAST_RELEASE) or [""])[0]
    print(f"release = main @ {head[:12]}"
          + (f"  (previous {prev[:12]})" if prev else ""))
    if prev == head and not args.force:
        print("main has not moved since the last release -- nothing to hand out.")
        print("(--force to re-run anyway)")
        return 0

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

        print(f"  staging {MERGER_HOST}:{MERGER_LAKE} -> {HOME_SEED}")
        res = sh(MERGER_HOST,
                 f"mkdir -p {HOME_SEED} && "
                 f"rsync -a --delete {MERGER_LAKE}/ {HOME_SEED}/ && "
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
            r = sh(host, f"mkdir -p {dest} && "
                         f"rsync -a --delete {HOME_SEED}/ {dest}/")
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
