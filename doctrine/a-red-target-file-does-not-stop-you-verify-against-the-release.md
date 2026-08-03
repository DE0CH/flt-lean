## A RED TARGET FILE DOES NOT STOP YOU — VERIFY AGAINST THE RELEASE OLEAN, AFTER A SIGNATURE DIFF
(2026-07-31, `flt-lean-394`, on `not_rationalModuli_of_selfIsogenous_oneSixtyNine` in
`X0.lean`.)  The target existed only on `merger`, and `X0.lean` on `merger` **does not
build** — release 27 inherited ~190 errors in it and did not publish (see
`tools/merge/RELEASE-27-HANDOVER.md`).  So `lake build` was unavailable, the
scratch-module trick was unavailable (it needs the target's own `.olean`), and the
obvious reading is "blocked, nothing to do".  It is not: a proof was written and
verified in **17 seconds** per round.
The shim is the one this file already documents, with one addition that is the whole
trick: **use the RELEASE SNAPSHOT's `X0.olean`, not your worktree's.**
`~/.flt-release-lake/build` is a *green* tree at `~/.flt-release-lake/sha`, so it has an
olean for a file that cannot be built today.
    rsync -a ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/
    lake env lean Fermat/Scratch394.lean        # imports the target module's olean
**The soundness condition is NOT optional and is NOT "the file is unchanged".**  Your
proof consumes a handful of declarations; what must hold is that each of THEIR
STATEMENTS is identical at the snapshot sha and at your HEAD.  That is a ten-line
script — extract each declaration's header up to its `:=`/`where` from
`git show <sha>:<path>` and from the working file, and compare — and it took seconds
for the nine names this proof used.  (One of them differed only by `:=` versus `:= by`,
i.e. in its PROOF; that is exactly the difference the check must tolerate and a naive
`git diff` will not.)  Write the result into the docstring: a proof verified this way
carries an assumption, and the next reader has to be able to re-check it.
Two mechanical traps, both of which cost a round:
* **A failed `lake build <Module>` leaves you with NO olean for that module** — lake
  deletes the target before elaborating, so a red build strictly destroys what you had.
  Re-`rsync` from the snapshot before reaching for the shim; do not assume the seeding
  you did an hour ago survived.
* **`stat` on the path through `$HOME` can lie for a minute after the rsync** (`$HOME`
  is NFS, `.lake` is a symlink into machine-local `/scratch`).  Check the file through
  `/scratch/...` directly before concluding the copy failed.
And the reason this is worth the trouble rather than reporting a blocker: the repair of
`X0.lean` is a multi-hour job that the merge worker had explicitly taken, in
`~/flt-staging`, on the same file.  **Doing it too would have been the worst available
duplication** — two editors on one 108 000-line file.  Check `~/.flt-loop/jobs/merger.json`
and `git -C ~/flt-staging log -1` before "helpfully" fixing the release blocker; the
handover document there tells you whether it is owned and what the method is.
