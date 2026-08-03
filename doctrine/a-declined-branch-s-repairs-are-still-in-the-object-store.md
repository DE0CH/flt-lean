## A DECLINED BRANCH'S REPAIRS ARE STILL IN THE OBJECT STORE — CHERRY-PICK THEM BY COMMIT, NOT BY HAND

(2026-07-31, release 30.  `X0.lean` went from ~136 errors to 39 in about twenty
minutes, and none of it was re-derived.)

`flt-lean-282` spent a whole run repairing `X0.lean` — five commits, five measured
rounds, 136 → 33 errors — and then correctly told the merge worker **not to take its
`X0.lean`**, because its branch was based on a `merger` that had since moved 294
commits and its line coordinates were stale.  Release 29 read that as "decline the
branch" and dropped the whole thing; the same wounds were still there for release 30.

**"Do not take my file" is not "do not take my work."**  A repair branch's commits are
in the shared object store for ever, and `git cherry-pick` re-derives the CONTENT
rather than the coordinates:

    git log --oneline <the declined branch>          # read the round titles
    git cherry-pick -X patience --no-commit <sha>    # one round at a time
    # resolve, verify, `git commit -C <sha>` so the original message survives

Measured here: of four X0 repair rounds, **rounds 4 and 5 applied CLEANLY** against a
tree 294 commits newer than their base, and rounds 2 and 3 conflicted in three hunks
each.  `-X patience` matters — these are large files where the default diff heuristic
aligns unrelated blocks.

**Every conflict was the same shape and it is the shape to expect: the merge worker's
own tree had ALREADY made the same repair by a different route.**  A dropped `open`
restored versus a dropped `open` restored; an orphaned markdown heading commented out
versus wrapped in a comment block; a duplicate declaration deleted versus deleted with
a note left behind.  So the default resolution is OURS, and the exceptions are the
hunks where ours is EMPTY and theirs is pure prose — take those, they are the
diagnosis somebody paid for.

**The one resolution that must not be automated**: a hunk where `ours` is a large block
and `theirs` is a three-line insertion is a MISALIGNMENT, not a choice.  Taking theirs
deletes the block; taking ours loses the fix.  Resolve to ours and then apply the
insertion by NAME — find the declaration the `open … in` was meant for and put it above
that declaration's docstring.  Two of the three real repairs in round 3 were this shape.

Two riders:

* **A repair commit's title is an index.**  "X0 round 3: two argument lists, the
  level-1/N Weierstrass split, the q=p narrowing, IsInitial and the
  ProjectiveLineOverField header" tells you, before you look at a single hunk, which of
  your errors it will fix and which of your own fixes will collide.  Write titles that
  way when you are the one repairing.
* **Cherry-pick even when you have already fixed some of it yourself.**  Two of round
  3's five repairs I had independently made an hour earlier; they showed up as
  conflicts I resolved to ours in seconds.  The cost of the overlap is far below the
  cost of re-deriving the three I had not found.

**And the general rule this is an instance of: before repairing anything in a giant
file, `git log -S` the failing identifier across ALL branches.**  In a fleet this size
somebody has usually been there already, and their work is one command away whether or
not their branch was merged.

