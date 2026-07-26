#!/usr/bin/env python3
"""Merge `main` into `staging` (Deyao, 2026-07-25, from a hand-drawn diagram).

TWO BRANCHES THAT DIVERGE AND REJOIN. `main` is the line; `staging` is the bulge.

  * `staging` ACCUMULATES. The orchestrator merges finished worker branches into
    it continuously and NEVER builds -- a full cone build costs hours, so
    building at integration would make the orchestrator the fleet's bottleneck.
    Dispatched agents fast-forward to staging, so a leaf a completion just
    created is immediately dispatchable.
  * `main` POINTS AT THE LAST GREEN BUILD, and nothing else ever moves it. The
    staging worker takes a staging commit into its own worktree, builds it, fixes
    whatever is red, regenerates the bookkeeping, and only then advances `main`
    to the commit it actually verified.
  * This script closes the loop: it merges main back into staging so the worker's
    build fixes and the regenerated PROGRESS.md reach the accumulation branch.

    orchestrator: worker branches -> staging      (continuous, never builds)
    worker:       staging -> build -> fix -> bookkeeping -> main = verified sha
    orchestrator: main -> staging                 (THIS SCRIPT)
    ... repeat

WHY THIS DIRECTION AND NOT THE OTHER. Merging staging into main would put unbuilt
commits on main, and main's entire value is that it is the last commit KNOWN to
compile -- it is what a human reads to see real progress, and the only branch
with a compiler's word behind it. Only the worker may advance it, and only to a
sha it has built. Conversely the fixes must not stay stranded on main: agents
fast-forward to staging, so without this merge every one of ~90 workers would
keep inheriting a red that had already been repaired.

    python3 flt-promote.py

Conflicts are NOT auto-resolved. The script stops and leaves the conflicted merge
in place -- resolving them is a judgement call about mathematics, and the design
assumes a best-effort resolution here followed by the compiler catching what only
a compiler can.
"""

import subprocess
import sys

ROOT = "/home/chend/flt-lean"   # checked out on `staging`
MESSAGE = (
    "Handback: merge verified main into staging\n\n"
    "Carries the staging worker's build fixes and the regenerated PROGRESS.md\n"
    "back into the accumulation branch. Dispatched agents fast-forward to\n"
    "staging, so without this they would keep inheriting reds that main has\n"
    "already had repaired."
)


def git(*args):
    return subprocess.run(["git", "-C", ROOT, *args],
                          capture_output=True, text=True)


def main():
    on = git("rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
    if on != "staging":
        print(f"refusing: {ROOT} is on '{on}', not 'staging'", file=sys.stderr)
        return 2
    dirty = git("status", "--porcelain").stdout.strip()
    if dirty:
        print("refusing: uncommitted changes -- a handback must start from a "
              f"clean tree:\n{dirty[:800]}", file=sys.stderr)
        return 2

    git("fetch", "origin", "--quiet")
    ahead = git("rev-list", "--count", "staging..main").stdout.strip() or "0"
    if ahead == "0":
        print("main -> staging: nothing to merge (main is already an ancestor)")
        return 0

    r = git("merge", "--no-ff", "-m", MESSAGE, "main")
    if r.returncode != 0:
        files = [x for x in git("diff", "--name-only",
                                "--diff-filter=U").stdout.splitlines() if x.strip()]
        print(f"main -> staging: CONFLICTED ({ahead} commits) in {len(files)} "
              f"file(s) -- merge left IN PLACE for you to resolve in {ROOT}:",
              file=sys.stderr)
        for f in files:
            print(f"    {f}", file=sys.stderr)
        print("Resolve, `git add -A && git commit`, push, then continue.",
              file=sys.stderr)
        return 1

    print(f"main -> staging: merged ({ahead} commits)")
    p = git("push", "origin", "staging")
    print("staging pushed" if p.returncode == 0
          else f"PUSH FAILED (merge stands):\n{(p.stdout + p.stderr)[:400]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
