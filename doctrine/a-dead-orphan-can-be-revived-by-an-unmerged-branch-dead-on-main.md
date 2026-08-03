## A DEAD ORPHAN CAN BE REVIVED BY AN UNMERGED BRANCH — "dead on main AND on merger" is not enough
(Same task, and it is what stopped this from being a four-declaration deletion.)
The standing rule for an open leaf with no consumer is to delete it.  The scan
that establishes "no consumer" is comment-stripped and tree-wide, and it is
correct — about the tree you can see.  A branch that has not merged can have
RE-POINTED a live consumer onto the orphan, which puts it back in the root cone
and makes the deletion a rival cut against landed work.
Here four declarations were resurrected by a merge after the 2026-07-31 recut
deleted them (`semmerge.py` propagates ADDITIONS and never DELETIONS, so any
branch forked before a deletion restores it).  Three were dead on `main`, dead on
`merger`, and dead in the tree.  **Two of them were also dead on every branch and
were deleted; the other two — `geomPic_divisible_place` and `geomPic_divisible` —
had been revived that morning by an unmerged branch that re-points
`exists_finiteIndex_divisible_pic` onto them, and deleting those would have
re-opened a closed chain.**
The evidence for the revival was not in any diff: it was in a `queue2` task
written by the reviving agent, which says in its STATUS NOTE that the leaf "was
DEAD … It was REVIVED on 2026-08-01".  So the two checks compose, and neither
alone is sufficient:
    # is it dead in the tree?
    grep -rn '<name>' --include=*.lean Fermat/    # comment-stripped; own decl only ⇒ dead
    # is somebody about to make it live again?
    grep -n '<name>' ~/.flt-loop/queue1 ~/.flt-loop/queue2 ~/.flt-loop/jobs/*.prompt
**When the two disagree, keep the declaration and say so in the deletion note.**
A kept orphan costs one dispatch; a deleted revival costs somebody's whole run
and a conflict the merge worker cannot adjudicate.  Write into the note what
would make it deletable again ("if that branch is declined, these go the same
way"), so the decision is recorded rather than re-derived.
Corollary about the prose: the recut's own docstring said the declarations had
been "DELETED", in three places, and had said so — falsely — since the first merge
after the recut.  **A docstring asserting that something was deleted is the
cheapest possible thing to check and among the least often checked**; one `grep -n
'^theorem <name>'` settles it, and a false one is exactly what makes an orphan
invisible.
