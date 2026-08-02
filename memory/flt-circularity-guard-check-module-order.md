---
name: flt-circularity-guard-check-module-order
description: "A leaf's CIRCULARITY GUARD lists several banned theorems; module order decides which bans are real, and one is routinely over-broad."
metadata: 
  node_type: memory
  type: project
  originSessionId: 584f13b9-f495-48ab-b761-22fb23f35415
  modified: 2026-08-02T20:29:54.547Z
---

A CIRCULARITY GUARD in a leaf docstring is written as a LIST of banned theorems, which
is how a correct ban and an over-broad one come to share one sentence.

Measured 2026-08-02, `flt-lean-39`, `Modularity/Patching.lean`'s
`cocycleClass_eq_zero_of_eval₁_kerFix_eq_zero`: the guard banned both
`not_isIrreducible_of_isHardlyRamified_of_five_le` and
`IsHardlyRamified.mod_three_reducible`. The first is a real ban (proven over pillar α,
which is proven over that cluster). The second **cannot** be circular:
`mod_three_reducible` is in `HardlyRamified/ModThree.lean`, which `Patching.lean`
`public import`s, and Lean's module order is a hard guarantee that an imported module's
proofs cannot reach the importing one. The same discharge was already used twice in the
same file. Cost of the bundling: the `p = 3` horn sat recorded as "not available
non-circularly" for three days, which also meant the residual leaf could not carry the
`5 ≤ p` its own citation (Wiles 1.12 / Dickson) consumes.

**Why:** module order is checkable and permanent; "downstream of" in a guard is a claim
about the mathematics that the author did not re-derive per name.

**How to apply:** for each banned name, `grep -n 'import .*<its module>' <your module>`.
If your module imports it, a cycle is impossible and the ban needs a different
justification or must be dropped. If not, read what the banned theorem is proven OVER.
Then rewrite the guard to say which half is which — deleting it invites restoration of
the broad version. A PARTIAL discharge (kill one characteristic by emptiness, keep the
real content) is not the vacuous `exfalso` the guard exists to stop; say so explicitly.
Related: [[flt-cut-choice-reasons-are-hypotheses]], [[flt-route-failing-is-not-leaf-false]].
