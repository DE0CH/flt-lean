#!/usr/bin/env python3
"""Direct sorries with no owner, resolved against all three ownership sources.

WHY THIS IS A SCRIPT. The loop invariant is that every sorry has an owner at all
times, and this check runs every ten minutes. Re-deriving it from prose each time
has produced a fresh false answer almost every run:

  * `json.dumps` on flt-owner's result raises `Object of type set is not JSON
    serializable`, silently reducing this to a TWO-source check;
  * a regex reading only the FIRST `TARGET:` block missed the second one in a
    prompt that had two (see below), hiding three live-owned leaves;
  * matching names literally missed `velu_map_add` against a TARGET block naming
    `WeierstrassCurve.velu_map_add`, because `flt-frontier.py` reports the name AS
    WRITTEN in source and that declaration sits inside `namespace WeierstrassCurve`.

Each of those reported live-owned work as unowned, which is the dangerous
direction: re-dispatching onto a leaf someone is holding has already caused a
collision in which one agent's worktree was reset under it.

THE THREE SOURCES, each wrong in a different direction:
  1. transcripts (flt-owner.load()) -- LAGS by minutes for fresh dispatches;
  2. ~/.flt-inflight.jsonl, TARGET blocks only -- prompts deliberately name
     sibling leaves under "do not touch these", so a whole-prompt grep invents
     owners (that once left 67 of 92 sorries reading as unowned);
  3. ~/.flt-task-queue -- a queued task IS ownership, and this is the easiest to
     forget because the queue is usually empty.

A leaf is unowned only if all three say so.

    python3 flt-unowned.py            # names, one per line
    python3 flt-unowned.py --verbose  # plus per-source counts and totals
"""

import importlib.util
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent
INFLIGHT = pathlib.Path("/home/chend/.flt-inflight.jsonl")
QUEUE = pathlib.Path("/home/chend/.flt-task-queue")

# ALL target blocks, not just the first: appending to a non-empty task queue
# without a leading `=== TASK ===` delimiter concatenates two tasks into one
# prompt, and that prompt then carries two TARGET blocks. That happened on
# 2026-07-25 and hid an entire task's worth of leaves.
TARGET_BLOCK = re.compile(r"TARGET[^\n]*:.*?(?:\n\s*\n|\Z)", re.S)
BACKTICKED = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")


def _mod(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def owned_names():
    """Union of every name any source claims, plus its bare last component.

    Both forms are kept because the two ends disagree by design: task prompts
    name leaves fully qualified, while flt-frontier.py reports them as written in
    source, which for a declaration inside `namespace Foo` is the bare name."""
    names = set()

    def add(n):
        names.add(n)
        names.add(n.rsplit(".", 1)[-1])

    # SOURCE 1 -- transcripts, RESTRICTED TO WORKTREES WHOSE AGENT IS STILL LIVE.
    #
    # The restriction is the whole correctness of this source (2026-07-26).
    # Transcripts persist forever, so `flt-owner.load()` keeps crediting an agent
    # with the leaves its prompt named LONG AFTER IT FINISHED -- and this scan's
    # only job is to answer "is anyone working on this right now?". Unrestricted,
    # it answers "did anyone ever" and reports a leaf as owned when nobody holds
    # it. That is the DANGEROUS direction: an unowned leaf that reads as covered
    # sits untouched for a whole release cycle with nobody dispatched at it.
    #
    # Found the hard way: with three agents freshly finished, this scan reported
    # ZERO unowned while `threeadicRealization_hasFlatProlongationAt_threePow`
    # had no owner in any source and two more were credited to agents that had
    # already reported completion.
    #
    # Liveness = the pool says an agent occupies the worktree. `batched` is
    # deliberately NOT live: the agent is gone and its work is with the merger,
    # so its leaves are up for grabs again.
    live = set()
    try:
        for ln in (pathlib.Path.home() / ".flt-worktree-pool").read_text().splitlines():
            f = ln.split()
            if len(f) >= 2 and f[1] in ("claimed", "reclaiming", "suspended"):
                live.add(f[0])
    except OSError:
        live = None                      # cannot tell: fall back to trusting all

    fo = _mod("flt_owner", "flt-owner.py")
    for wt, rec in fo.load().items():        # `names` is a SET -- union, never dumps
        if live is not None and wt not in live:
            continue
        for n in rec.get("names") or ():
            add(n)

    if INFLIGHT.exists():
        for line in INFLIGHT.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            try:
                prompt = json.loads(line).get("prompt", "")
            except ValueError:
                continue
            for block in TARGET_BLOCK.findall(prompt):
                for n in BACKTICKED.findall(block):
                    add(n)

    if QUEUE.exists():
        for block in TARGET_BLOCK.findall(QUEUE.read_text(encoding="utf-8")):
            for n in BACKTICKED.findall(block):
                add(n)
    return names


def _proven_in_batch(cands):
    """Of `cands` (name -> repo-relative path), those already PROVEN on a branch
    sitting in the merge batch.

    A fourth thing that counts as "not up for grabs" (2026-07-26), and it is not
    optional. Under the release model a finished agent's proof lives on its
    branch until the merger cuts a release, so on `main` the leaf still reads as
    a direct sorry while its agent is gone -- which makes it look UNOWNED when it
    is in fact DONE. Dispatching there re-proves work already waiting to land,
    and re-proving finished work is the commonest way this fleet wastes a worker.

    Scans each (branch, file) ONCE and caches. The naive shape -- rescan per
    (leaf, branch) -- re-parses multi-thousand-line files up to a hundred times
    and takes minutes, which matters because this runs on a ten-minute cron.
    """
    import subprocess, tempfile, os as _os
    batch = []
    for f in (".flt-merge-batch", ".flt-merge-batch.inflight"):
        fp = pathlib.Path.home() / f
        if fp.exists():
            batch += [l.strip() for l in fp.read_text().splitlines() if l.strip()]
    if not batch:
        return set()
    fr = _mod("flt_frontier", "flt-frontier.py")

    cache = {}                      # (branch, rel) -> set of names still sorried
    def open_on(br, rel):
        key = (br, rel)
        if key in cache:
            return cache[key]
        r = subprocess.run(["git", "-C", str(ROOT), "show", f"{br}:{rel}"],
                           capture_output=True, text=True)
        if r.returncode != 0:
            cache[key] = None       # file absent on that branch: says nothing
            return None
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as fh:
            fh.write(r.stdout)
            tmp = fh.name
        try:
            cache[key] = {n for n, _ in fr.scan(pathlib.Path(tmp))}
        finally:
            _os.unlink(tmp)
        return cache[key]

    done = set()
    for name, rel in cands.items():
        for br in batch:
            names = open_on(br, rel)
            if names is None:
                continue
            if name not in names:
                # present on that branch's tree and no longer sorried there
                done.add(name)
                break
    return done


def main():
    verbose = "--verbose" in sys.argv[1:]
    fr = _mod("flt_frontier", "flt-frontier.py")
    leaves, where = [], {}
    for p in sorted((ROOT / "Fermat").rglob("*.lean")):
        rel = str(p.relative_to(ROOT))
        for n, _ in fr.scan(p):
            leaves.append(n)
            where.setdefault(n, rel)
    owned = owned_names()
    unowned = [l for l in leaves
               if l not in owned and l.rsplit(".", 1)[-1] not in owned]
    if unowned:
        landed = _proven_in_batch({n: where[n] for n in unowned})
        if landed and verbose:
            print(f"proven on a batched branch, awaiting release: {len(landed)}")
            for n in sorted(landed):
                print(f"  (landed) {n}")
        unowned = [l for l in unowned if l not in landed]
    if verbose:
        print(f"direct sorries: {len(leaves)}   names claimed by some source: "
              f"{len(owned)}   UNOWNED: {len(unowned)}")
    for n in unowned:
        print(n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
