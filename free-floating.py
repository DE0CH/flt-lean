#!/usr/bin/env python3
"""Free-floating-code detection: project declarations that no proof term
reachable from the root theorem `fermat_last_theorem` actually uses.

The sweep itself runs INSIDE ProgressCensus.lean's `runCensus` -- the
"floating" field of its JSON output, computed with ImportGraph's
`Name.transitivelyUsedConstants` (a vendored transitive dependency through
mathlib's own lakefile, not a hand-rolled BFS). This script is a thin
standalone entry point over that one query, and all it adds is the
keep-list post-filter below.

TRANSPORT. It reuses progress-tree.py's `run_census()`, which since
2026-07-25 is ONE `lake env lean ProgressCensus.lean` run over ssh on the
worktree's assigned host. There is no resident server, no `.report-server/`,
no LSP and no cache -- see progress-tree.py's module docstring for why that
design was deleted. Two consequences carry over unchanged:

  * each run pays the IMPORT LOAD of the whole project cone (minutes), so
    run this once per bookkeeping cycle, never in a loop; and
  * the tree must be BUILT, because the census reads oleans. This matters
    especially here: a module that fails to build contributes NO
    declarations at all, so everything it defines would be reported as
    floating. A partial census gives a WRONG floating answer, which is why
    neither this script nor run_census() has a degraded mode -- they answer
    fully or die with lake's real error.

A sorried body contributes no dependency edges, so material built bottom-up
for a still-sorried consumer reads as floating until the consumer's proof
skeleton is written to consume it. Reduce floaters by writing the consuming
proofs, top-down -- not by blind deletion sweeps, and never by `private`,
which hides from this check rather than satisfying it.
"""
import importlib.util
import json
import os
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
KEEP_PATH = os.path.join(ROOT, "free-floating-keep.json")


def _load_progress_tree():
    spec = importlib.util.spec_from_file_location(
        "progress_tree", os.path.join(ROOT, "progress-tree.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def compute():
    """Returns {"kept_invisible": [...], "floating": [...]}."""
    pt = _load_progress_tree()
    # CANONICAL census input (same names, same construction, as
    # progress-tree.py --census): the input json's bytes feed the
    # fingerprint line inside generated ProgressCensus.lean, so every
    # census route must produce identical input or each route's queries
    # dirty the generated file against the committed one.
    entries = json.load(open(os.path.join(ROOT, "progress-entries.json")))
    names = [e.get("fullname", e["name"]) for e in entries]
    resp = pt.run_census(names, root="fermat_last_theorem")
    raw = resp.get("floating")
    if raw is None:
        raise RuntimeError(
            "census response has no 'floating' field -- ProgressCensus.lean "
            "or progress-tree.py is out of sync with this script")

    keep = {}
    if os.path.exists(KEEP_PATH):
        with open(KEEP_PATH) as fh:
            try:
                keep_data = json.load(fh)
            except ValueError as exc:
                raise RuntimeError(
                    f"corrupt keep-list {KEEP_PATH}: {exc} -- fix or delete "
                    "it and rerun") from exc
        keep = {k: v for k, v in keep_data.items() if not k.startswith("_")}

    floating = []
    kept_invisible = []
    for entry in raw:
        if entry["name"] in keep:
            kept_invisible.append(entry)
        else:
            floating.append(entry)
    return {"kept_invisible": kept_invisible, "floating": floating}


def main() -> int:
    print(json.dumps(compute()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
