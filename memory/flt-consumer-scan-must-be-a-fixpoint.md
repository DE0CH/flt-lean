---
name: flt-consumer-scan-must-be-a-fixpoint
description: A one-hop consumer grep calls a dead leaf live; a rival cut orphans a whole subtree including proven lemmas
metadata: 
  node_type: memory
  type: project
  originSessionId: 84465f95-3de8-4eca-b83b-ebff4bbcc61b
  modified: 2026-08-01T22:53:19.527Z
---

Before proving a leaf, the standing check is a comment-stripped grep for its consumers. **One
hop is not enough.** In `ModularCurve/HyperellipticJacobian.lean` (2026-08-01, `flt-lean-385`)
a rival cut of `geomPic_descent` orphaned four leaves at once. Three returned a single code
hit — their own declaration — and one hop got those right. The fourth,
`geomPic_exists_const_of_ord_nonneg`, had an honest consumer `geomPic_degOf_eq_one`, which had
an honest consumer `geomPic_degHom_divAct`, **which had none**. Three declarations dead, two of
them PROVEN and therefore invisible to every sorry-scan.

Compute `dead := fixpoint { X : every consumer of X is dead }`, not `{ X : no consumer }`.

**Why:** a losing cut's assembly lemmas were written to serve that cut and nothing else, so
deadness propagates downward through proven code. A one-hop answer is wrong in the expensive
direction — it says LIVE.

**How to apply:** run the fixpoint before any mathematics. If the winner of the rival cut is
itself a `sorry`, there is no inline block to harvest, and the choice is DELETE or prove the
WINNER over the loser's leaves. Prefer the second when the loser's residue has names in the
literature — that is the test for "the loser was the better decomposition". Never prove a dead
leaf in passing: a proven declaration with no consumer is free-floating and gets swept.

Related: [[flt-consumerless-leaf-is-dead-or-duplicate]], [[flt-both-rival-cuts-landed]],
[[flt-both-docstrings-name-the-loser]], [[flt-closing-a-leaf-may-close-nothing]].
