## SEE THE MERGE BEFORE THE MERGE WORKER DOES — `git merge-tree`, from your own worktree

(2026-07-31, `flt-lean-182`.) Every rule above about rival cuts, class-6 dropped payloads and
class-7 interface splits is addressed to the merge worker, at the moment the merge happens. A
prover agent can see the *same* merge hours earlier, for free, and without touching anything:

    git merge-tree --write-tree --name-only HEAD merger    # exit 1 == conflicts; prints tree sha

It merges **in memory**. No working-tree change, no `.lake` disturbance, no conflicted state to
strand the worktree in if you are killed mid-way — which is exactly why this beats the obvious
`git merge --no-commit … ; git merge --abort`. The printed tree sha is browsable with
`git show <tree>:<path>`, so every class-7 check in this file can be run **on the merge that has
not happened yet**.

Do it whenever your branch touched a hot file, and read TWO things, because they fail in opposite
directions:

- **The files that CONFLICTED** are the safe half. Somebody will look at them.
- **The files that `Auto-merging` reported with no conflict are the dangerous half.** That is
  class 7 verbatim: my branch deleted `not_smooth_specMap_coordinateRing_of_singular` (130 lines)
  while `merger` had independently grown a *new call to it* 200 lines away. Too far apart to
  conflict, so `EllipticScheme.lean` auto-merged silently — and the check that settles it is not
  reading the diff but grepping the merged blob for the deleted name:

      git show <tree>:<path> | grep -n '<deletedName>'   # docstring hits only == safe

  Here it happened to resolve correctly (git took my region wholesale, call site and all). "Happened
  to" is the point: nothing would have said otherwise.

**Then check the reverse direction, which is the one nobody thinks of.** Your branch carries the
*old* `sorry` bodies of every leaf it did not touch. If `merger` proved one of them meanwhile,
does the merged tree keep the PROOF or your `sorry`? Grep the merged blob for the body, not the
name. (Both of mine were preserved — untouched regions take merger's side — but that is a fact to
verify, not to assume, and it is invisible from either side alone.)

### What to do when the merge shows your cut and `merger`'s are RIVALS

The `RIVAL CUTS` section above tells the merge worker how to choose. It does not say what the
prover on the other branch should do, and there is one action worth far more than a note: **fold
the loser's surviving information into the winner's docstring on YOUR side, so that "take HEAD" is
a LOSSLESS resolution.** Then say exactly that in `to_merger`.

`merger` had closed my target by NARROWING it to `[PerfectField k]`; my branch had deleted the
hypothesis outright, so mine strictly subsumes it and the conflict was pure docstring. But
merger's docstring held two facts mine did not — that narrowing to `CharZero` instead would have
REGRESSED `X1.lean`'s char-`p` chain, and why the declaration is kept as a thin wrapper (a
non-`public import` makes the upstream name invisible to its real consumer). Taking HEAD would
have silently dropped both. Ten minutes of docstring editing turned a decision requiring the merge
worker to re-derive the mathematics into a one-word one.

And check the loser's docstring for claims that have gone STALE before you copy them: merger's
said the chain was "down to ONE" leaf that had since been proven. Fold in what is durable, correct
what is not, and say which you did.

