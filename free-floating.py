#!/usr/bin/env python3
"""Free-floating-code detection (Deyao, 2026-07-23: "get rid of the
caching and use the language server, the language server should
handle the caching for us").

The floating sweep runs INSIDE ProgressCensus.lean's runCensus (the
"floating" field of its JSON output) -- the same always-open,
warm-elaborated environment progress-tree.py's census already queries,
via the resident flt-report-server. No scratch file, no `lake env
lean` subprocess, no custom mtime-keyed cache: Lean's own incremental
elaboration IS the cache (progress-tree.py's STALENESS section --
unchanged source -> identity didChange -> diagnostics republished from
cached snapshots in seconds; verified empirically: ~30-40s after a
real source edit, 0.4s warm).

This script now only does the keep-list post-filter.
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
    resp = pt.run_census([], root="fermat_last_theorem")
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
