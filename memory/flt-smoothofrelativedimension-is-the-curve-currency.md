---
name: flt-smoothofrelativedimension-is-the-curve-currency
description: "Every curve module in Fermat/FLT/Mathlib/AlgebraicGeometry demands SmoothOfRelativeDimension 1, and nothing in the tree produces it from a bare Smooth f — so a development carrying Smooth + topologicalKrullDim ≤ 1 is one missing bridge away from all of it"
metadata: 
  node_type: memory
  type: reference
  originSessionId: 8370b060-21e6-4a65-ba37-ef1ba036c62a
  modified: 2026-08-02T19:18:00.434Z
---

(2026-08-02, `flt-lean-29`, measured rather than recalled.)
`Fermat/FLT/Mathlib/AlgebraicGeometry/`'s curve machinery — `CurveGenus.lean`
(`IsCurveGenus`, `ell`, `rrSet`, `divisorDegree`, `exists_isCurveGenus`),
`CurveDivisorDegree.lean`, `CurveExtension.lean`, `CurveDimension.lean` — takes
`AlgebraicGeometry.SmoothOfRelativeDimension 1` as its hypothesis throughout.

**Nothing in the tree has it as a CONCLUSION from a bare `Smooth f`.**
`grep -rn 'SmoothOfRelativeDimension' Fermat/` returns only declarations that
already hold it as a hypothesis or as a structure field (`X0.lean`, `X1.lean`,
`WeilRestriction.lean`, `AffineLineExtension.lean`, `CurveDimension.lean`).
`CurveDimension.lean` runs the OTHER way (`[SmoothOfRelativeDimension 1] →`
dimension facts), and `smoothOfRelativeDimension_of_isDominant_of_smooth`
(`CurveExtension.lean`) needs relative dimension `n` on a dense open already.

**Why it matters:** `Modularity/MoretBailly.lean`'s whole §3.1 chain is stated
with `Smooth fX` plus `topologicalKrullDim ↥Xbar ≤ 1`, so it was cut off from all
of the above. The bridge is now the leaf
`smoothOfRelativeDimension_one_of_smooth_of_not_subsingleton` in that file
(cut 2026-08-02, stated with no `C`/`j`/`Z` so it can be hoisted).

**The non-degeneracy is not optional**: `Spec ℚ` is smooth, integral, of
`topologicalKrullDim 0 ≤ 1` and of relative dimension `0`. `¬ Subsingleton ↥X` is
the sharp form and is cheap to discharge (a nonempty open with nonempty
complement gives two distinct points).

**How to apply:** before costing a curve leaf whose hypotheses are `Smooth` +
a Krull-dimension bound, check whether the machinery you plan to cite wants
`SmoothOfRelativeDimension 1`; if it does, that bridge is on your critical path
and is a separate obligation. Related:
[[flt-theory-absence-claims-need-a-directory]].
