## A LINE-NUMBER MISMATCH IN YOUR TASK PROMPT MEANS YOUR WORKTREE IS STALE — not that the leaf is gone

(2026-07-31, `flt-lean-23`.) A task named three leaves at `X1.lean:13442`, `:13465`,
`:14526`. The worktree's `X1.lean` was **10 390 lines long**, so two of the three names
did not appear in it at all. The obvious reading — "already proven, or renamed, or the
queue is stale" — is the wrong one and would have burned the whole dispatch.

`HEAD` was `9a2ca10d`, an ancestor of `main` but ~200 commits behind it; `main`'s
`X1.lean` is 16 605 lines and every line number in the prompt matched it EXACTLY. The
worktree had simply not been fast-forwarded at dispatch.

So the first thing to run in any worktree, before reading the target at all:

    git rev-parse HEAD; git rev-parse main
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

**The line numbers in a task prompt are a checksum on your checkout.** If they land on
the right declarations, your tree is current; if they land in the wrong place or the
names are missing, merge `main` and look again *before* concluding anything about the
leaf. This is the cheap, local version of the "MERGE `main` FIRST, then full build,
then believe it" rule above — and note that it fires in the direction that produces a
false "already done" report, which nothing downstream would catch.

Corollary for the `.lake`: the release snapshot at `~/.flt-release-lake` records the sha
it was built from in `~/.flt-release-lake/sha`. `git diff --name-only <that sha> main`
is one command and tells you whether the snapshot is exactly current for Lean purposes
— it was here (the only diffs were `flt-loop.py` and `flt_loop_rows.py`), so an
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
took 47 s and made `lake build` a 63 s no-rebuild verify instead of an hours-long one.

