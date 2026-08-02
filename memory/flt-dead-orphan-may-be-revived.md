---
name: flt-dead-orphan-may-be-revived
description: "An open leaf with no consumer on main AND on merger can still be alive — an unmerged branch may have re-pointed a live consumer onto it, and the only evidence is in the queue."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e5e6036b-f625-4c08-a7f2-219be53bf781
  modified: 2026-08-01T15:20:48.051Z
---

The standing rule is that an open leaf nothing consumes should be deleted. The
comment-stripped tree-wide scan that establishes "no consumer" is correct about
the tree you can see. It is blind to a branch that has RE-POINTED a live consumer
onto the orphan, which puts it back in the root cone.

Measured 2026-08-01 in `ModularCurve/HyperellipticJacobian.lean`: four
declarations were resurrected by a merge after the 2026-07-31 recut deleted them
(`semmerge.py` propagates ADDITIONS and never DELETIONS, so any branch forked
before a deletion restores it). Two were dead everywhere and were deleted; the
other two (`geomPic_divisible_place`, `geomPic_divisible`) had been revived that
morning by an unmerged branch re-pointing `exists_finiteIndex_divisible_pic` onto
them. Deleting those would have re-opened a closed chain.

**Why:** a kept orphan costs one dispatch; a deleted revival costs somebody's
whole run and produces a delete-vs-modify conflict the merge worker cannot
adjudicate.

**How to apply:** run both checks and keep the declaration when they disagree.

    grep -rn '<name>' --include=*.lean Fermat/     # own decl only ⇒ dead in the tree
    grep -n '<name>' ~/.flt-loop/queue1 ~/.flt-loop/queue2

The revival is announced only in the reviving agent's queue task (a STATUS NOTE
saying the leaf "was DEAD … It was REVIVED on <date>"), never in a diff — see
[[flt-grep-the-queue-for-your-target]]. Record in the deletion note what would
make the kept ones deletable again, so the decision is written rather than
re-derived. Related: [[flt-both-rival-cuts-landed]],
[[flt-consumerless-leaf-is-dead-or-duplicate]].
