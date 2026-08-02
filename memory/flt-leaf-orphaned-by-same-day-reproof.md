---
name: flt-leaf-orphaned-by-same-day-reproof
description: "A leaf cut out of a consumer that is re-proven the same day by a rival route is orphaned at birth, and its docstring still claims the consumer rests on it."
metadata: 
  node_type: memory
  type: project
  originSessionId: 96129984-22e1-45db-988a-a24a8cee9822
  modified: 2026-08-02T11:52:33.785Z
---

The orphan classes in CLAUDE.md all need two branches. This one needs none — one
file, one day, two cuts of one consumer.

`MoretBailly.det_nTorsion_eq_cyclotomicExponent` was cut 2026-07-30 out of
`exists_weilPairing_mu_charZero`; the SAME DAY that consumer was re-proven over a
different leaf, so the cut was dead within hours. Three days later it still read
*"This is the ONE genuinely missing piece of mathematics in the whole archimedean
cluster"*, and a second docstring said the cluster "bottoms out" there. A
comment-stripped scan of `Fermat/` found **one** occurrence of the name — its own
declaration.

**Why:** every instrument agrees it is ordinary open work. It emits
`declaration uses 'sorry'`, a source scan finds the token, `own.py`/`leafstat.py`
correctly report it unowned, and the statement is true and audited. Only the
consumer count distinguishes it.

**How to apply:** the tell is a docstring sentence *"X below is now PROVEN over
this"* — a claim about `X`'s PROOF BODY, which a rival cut falsifies without
touching a character of it. Before working any leaf, `grep` the named consumer,
read its `by` block, and check your leaf's name is in it; independently count the
leaf's own consumers (own declaration + prose = dead). Seconds either way.

Repair when the orphan is a SPECIAL CASE of a live leaf: **prove it, do not delete
it first**. Proving is a one-hunk edit that conflicts with nobody in a 57 000-line
file with many concurrent editors; deleting is not, stays available afterwards, and
un-deleting does not. Queue the deletion, mark the duplicate in the docstring, and
correct the stale claim in place. See [[flt-delete-times-refactor-orphans-a-leaf]],
[[flt-consumerless-leaf-is-dead-or-duplicate]],
[[flt-both-docstrings-name-the-loser]].
