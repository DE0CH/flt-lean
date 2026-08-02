---
name: flt-power-series-are-their-coefficients
description: "Over FractionRing (PowerSeries k) the Tate-curve algebra needs no evalInt, no summability and no completeness — and the leaf usually wants \"not a constant\", not transcendence"
metadata: 
  node_type: memory
  type: project
  originSessionId: 910cfdd2-5402-4bd3-bd13-7abca3d03d17
  modified: 2026-08-02T20:30:03.774Z
---

(2026-08-02, `flt-lean-50`.) `TateParameter.lean`'s `evalInt` machinery — summability,
`valuation … < 1`, a complete nonarchimedean field — exists for evaluating the Tate series
at an element of a local field. A leaf stated over `ℚ((q)) = FractionRing (PowerSeries ℚ)`
needs **none of it**: there the series ARE the coefficients, so `a₄`, `a₆`, `Δ`, `c₄` are
the images of `TateCurve.{a₄Formal,a₆Formal,ΔFormal,c₄Formal}` under `ℤ⟦q⟧ → ℚ⟦q⟧ ↪ K`, and
every fact is an identity of power series pushed along an INJECTION. Ninety lines, first try
— against a development.

**Why:** `TateCurve.ΔFormal` is *defined* as the discriminant polynomial of the quintuple
`⟨1,0,0,a₄,a₆⟩`, so "mathlib's `Δ` of the Tate curve is the image of `ΔFormal`" is
`simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, map_*]; ring`, and likewise `c₄ = 1 - 48a₄`.
`coeff 1 ΔFormal = 1` makes `Δ` nonzero in the domain `ℚ⟦q⟧`, hence a unit of `K`, hence
`IsElliptic`.

**How to apply:** and this is the half that saves the most — **ask the consumer which
strength it needs.** The classical statement is that `j(Tate(q)) = 1/q + 744 + …` is
TRANSCENDENTAL over `ℚ`; what a consumer in this tree wants is discharged by *"`j` is not a
CONSTANT"*, because `mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries`
(`Mathlib/RingTheory/InvariantCoarseRing.lean`, PROVEN) already upgrades "not in the image
of `ℚ`" to "not algebraic over `ℚ`". Non-constancy is `Δ · j = c₄³` descended along the
injection plus one reading of constant coefficients (`0·c = 0` against `1³ = 1`). Same family
as [[flt-audit-lacks-x-is-about-x]]: the theory named in the docstring was not the theory the
statement needed.

Rider, when you then decompose: name the curve in the residual leaf
(`∃ d, IsWeierstrassModel d.ab tateCurveFractionRing`) rather than quantifying it
(`∃ d, ∃ W, … ∧ W.j ∉ range ℚ`) — otherwise the algebra you just proved has no consumer and
is free-floating. See [[flt-discharged-hypothesis-defeats-floating]].
