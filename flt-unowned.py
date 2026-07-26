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

    fo = _mod("flt_owner", "flt-owner.py")
    for rec in fo.load().values():          # `names` is a SET -- union, never dumps
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


def main():
    verbose = "--verbose" in sys.argv[1:]
    fr = _mod("flt_frontier", "flt-frontier.py")
    leaves = [n for p in sorted((ROOT / "Fermat").rglob("*.lean"))
              for n, _ in fr.scan(p)]
    owned = owned_names()
    unowned = [l for l in leaves
               if l not in owned and l.rsplit(".", 1)[-1] not in owned]
    if verbose:
        print(f"direct sorries: {len(leaves)}   names claimed by some source: "
              f"{len(owned)}   UNOWNED: {len(unowned)}")
    for n in unowned:
        print(n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
