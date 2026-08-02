---
name: flt-route-refuted-in-sibling-docstring
description: "A leaf's prescribed route is often refuted by name in a sibling docstring of the same file, which also names the theorem that closes the leaf — grep for correction markers before attempting any route."
metadata: 
  node_type: memory
  type: project
  originSessionId: c57a17c2-b180-4a08-a223-4801f3f1fd66
  modified: 2026-08-02T03:48:13.052Z
---

In flt-lean, a sorry leaf's docstring routinely prescribes a route and dismisses
the obvious one. Both claims are written **before anyone tries**, and the file
itself often already contains the refutation — in the docstring of a *sibling*
leaf that hit the same wall, climbed it, and recorded the lesson beside its own
declaration instead of propagating it.

Measured 2026-08-02 on `LowerRamificationData.iInf_gp_one_le_wildInertiaGroup`
(`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`): its
docstring prescribed "choose a TAME level, where `G_1` is trivial" and dismissed
the naive argument for needing `v_L(x) = 1`. Sixteen hundred lines below,
`exists_lowerRamificationData_phi_one_le`'s docstring says, in bold, that the
valuation-one requirement is "not NEEDED" and "not ACHIEVABLE", **and names
`LowerRamificationData.eq_one_of_smul_eq_mul_of_mem_gp_one` as the replacement**.
Both were written the same day. The leaf then closed in eleven lines.

**Why:** the two leaves' statements share no identifier (`⋂_D G_1 ≤ P_v` versus
`φ(1) ≤ ε`), so no name-based search relates them. The connection lives only in
prose.

**How to apply:** before attempting a route a docstring prescribes, run

    grep -n 'was WRONG\|is not NEEDED\|not ACHIEVABLE\|dead end\|ROUTE ACTUALLY USED\|does NOT close' <the file>

and read every hit whose subject is an object your route also names. Then expect
the replacement theorem to be declared BELOW you — structurally, because it was
written for the sibling that got there second — so the leaf is a
[[flt-declaration-order-leaves]] one and the repair is a hoist, not a proof. Say
so in the commit: a hoist and a proof are indistinguishable in the warning-set
delta. Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audit-recommended-axis-may-be-worse]], [[flt-leaf-above-its-own-solution]].
