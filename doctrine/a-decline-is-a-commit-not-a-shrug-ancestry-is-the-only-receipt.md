## A DECLINE IS A COMMIT, NOT A SHRUG — ancestry is the only receipt for a branch

(2026-07-30, medic.) The loop hands a merge worker a list of branches and gets
no itemised answer back — a sentinel says `panic: false` and one line of prose.
So it has exactly one way to tell, per branch, whether that branch was dealt
with: **is it an ancestor of the main you published?** Everything the merger is
allowed to do produces one. A merge does. So does a DECLINE, *provided* it is
recorded the way the class-7 section above prescribes — `git checkout HEAD --
<the files>`, then commit the merge, so the diff against the first parent is
empty on purpose and the message says the payload was declined.

`git merge --abort` and moving on is not a decline. It leaves no receipt, and
the branch is indistinguishable from one you never reached.

That distinction used to cost the work. Adopting a release discharged the whole
claim on the strength of the release being *complete* — main moved, snapshot
and audit current — which says nothing about how much of the payload got
merged. A merger that merged 18 of its 55 branches and was killed before
reporting had the other 37 dropped in one assignment, their worktrees pinned in
`awaiting_merge` for ever, because a worker is freed only by its branch
BECOMING an ancestor of main and nothing was left to merge it. **78 worktrees —
one full day of the fleet's output — were stranded that way**, and nothing
noticed until an invariant check summed two numbers that had never been summed.

Row 10 now folds the unlanded remainder of a claim back into the batch, so a
merger running out of time is safe: merge what you can, publish, and the rest is
re-offered next release. But that only works if a decline is a decline. An
unrecorded one comes back to the next merge worker for ever.

General form, and this is the third time it has bitten in a week: **an
assignment to a field that holds a CLAIM ON WORK is a deletion of work.** Every
other hand-off in the loop is a fold or a move. Both leaks — `r11_action`'s
`.inflight = list(batch)` and `r7_action`'s `.inflight = None` — were single
assignments, and both were invisible because the state they produced is
indistinguishable from a state where the work never existed.

