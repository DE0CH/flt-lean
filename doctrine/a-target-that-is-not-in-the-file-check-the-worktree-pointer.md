## A TARGET THAT IS NOT IN THE FILE: check the worktree pointer BEFORE concluding anything

(2026-07-31, `flt-lean-360`.) The task prompt named a leaf at
`BinaryQuadraticForm.lean:4806`. The file in the worktree was **2486 lines**, and a
`grep` for the declaration over all of `Fermat/` returned nothing. Every reading
that suggests itself at that point is wrong and expensive: "already proven and
removed", "the queue entry is stale", "the leaf was renamed", "cut on an unmerged
branch". The actual cause was that **the worktree had not been advanced**: `HEAD`
sat on a merger commit one release behind, `main` was 71 files and 92k lines
ahead, and a plain `git merge --ff-only main` produced the 5411-line file with the
target at exactly the promised line.

So the first three commands in any task, before reading the target at all:

    git log -1 --format=%H          # where am I
    git rev-parse main             # where should I be
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

The dispatch hook is supposed to have done this, and normally has. It is cheap to
confirm and catastrophic to skip — a stale worktree makes a live leaf look deleted
and a fixed upstream look broken, and both misreadings produce a confident,
completely wasted report. This is the same "merge `main` FIRST" rule the triage
section below states for hard errors, applied one step earlier: to the question of
whether the target exists.

Note also that `lake` is **not on `PATH`** in an agent's non-login shell —
`lake: command not found`, exit `127`, which looks like a broken toolchain.
`export PATH="$HOME/.elan/bin:$PATH"` first, in every shell that runs it.

And one shell trap that cost two builds here: `pkill -f "lake build <Module>"`
also matches the *new* shell you are starting in the same command, because the
harness passes the whole command line through `bash -c 'eval …'`. Both the old and
the new build died with exit `144`. Do not pattern-kill on a string that your own
command line contains.

