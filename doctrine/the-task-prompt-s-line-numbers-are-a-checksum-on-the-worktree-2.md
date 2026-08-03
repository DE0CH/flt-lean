## THE TASK PROMPT'S LINE NUMBERS ARE A CHECKSUM ON THE WORKTREE, AND THEY CAUGHT A 704-COMMIT STALE ONE

(2026-07-31, `flt-lean-16`.) The prompt named three leaves in `X0.lean` at lines 34356,
34410, 34514. `grep` found the first two at 29033 and 29074 and the third **not at all**.
The worktree was on `9a2ca10d` — an ancestor of `main`, **704 commits and 92k lines
behind**, with `X0.lean` 17706 lines shorter than the one the task was written against.
`git status` was clean, the branch was a proper ancestor, `lake build` was green: by every
check an agent naturally runs, the worktree looked fine. It was simply *old*.

Nothing in the dispatch says this can happen. `CLAUDE.md`'s own dispatch section says a
worktree fast-forwards to `main` at dispatch, and the loop's `flt-cycle.py release` phase 1
advances every worktree — so an agent that trusts either statement will edit a file whose
declarations have moved, whose neighbours are missing, and whose `sorry` set is a snapshot
of some earlier release. Every one of the five invisibility classes above then fires at
once, and the resulting work is unmergeable rather than merely wrong.

**So make this the first thing you do, before reading the target file:**

    grep -n '<the target name>' <the file>        # must land ON the prompt's line number
    git log --oneline -1 main; git rev-list --count HEAD..main

A line-number mismatch of more than a few lines is not "the file drifted" — it is a stale
checkout until proven otherwise. `git rev-list --count HEAD..main` is the one-command
version and costs nothing. The repair is `git merge --ff-only main`, plus reseeding
`.lake` from the release snapshot (`rsync -a --delete ~/.flt-release-lake/build/
/scratch/chend-flt/flt-lean-N/.lake/build/`) — 2.3 G, about a minute, and without it the
first `lake build` rebuilds a large part of the tree against a mismatched olean set.

A leaf named in the prompt that does **not** appear in the file at all (here
`exists_gamma0GITPresentationOver_normalModuli_zmod`) is the loudest form of this signal.
Do not conclude it was renamed or already closed; check the freshness first. Both readings
lead to a sentinel reporting "already done", and one of them is a lie.

