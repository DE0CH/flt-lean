---
name: flt-descend-makes-isisogeny-free
description: a leaf that must hand over an isogeny costs no geometry if the map is a DESCENT along [n] — IsRationalMap.descend plus IsRationalMap.isIsogeny do it
metadata:
  type: project
---

`WeierstrassCurve.IsIsogeny` (Fermat/FLT/EllipticCurve/Isogeny.lean) has three
fields and looks expensive to produce. Over `[IsAlgClosed F] [W.IsElliptic]` two
of them are already discharged for you by `IsRationalMap.isIsogeny` (PROVEN), so
the real obligation is only `IsRationalMap`. And that too is free whenever the
map you want is a DESCENT: `IsRationalMap.descend` (PROVEN, needs `[CharZero F]`)
says a `χ` with `χ ∘ π = ψ` is rational as soon as `π` is a rational surjection
and `ψ` is rational.

The idiom that triggers it: **`n • φ = σ` reads `φ ∘ [n] = σ`**, because `φ` is
additive. So "`φ = σ/n`" exhibits `φ` as a descent along `[n]`, which is rational
(`isRationalMap_mulByHom`) and surjective (`nsmul_surjective`). This is how
`isIsogeny_halfOfCmSqrt` in X0.lean gets `IsIsogeny` for `φ = (1 + ψ)/2` out of
`IsIsogeny ψ` and nothing else, which is what let the Deuring leaf be split into
two statements neither of which owes any geometry.

Companion fact, needed whenever you divide: the last division is a statement
about `End` being TORSION-FREE, not about points — `E(ℚ̄)` really does have
`4`-torsion. Discharge it on the MAP: `α`'s range lies in `E[n]`, finite by
`finite_nsmulKer`, and `eq_zero_of_finite_range` gives `α = 0`.

**Why:** the natural reading of "produce an endomorphism with `IsIsogeny`" is
"build the algebraic geometry", and that reading is what made the parent leaf
look like a uniformisation build.

**How to apply:** before costing a leaf that must produce an isogeny, ask whether
the map is `σ/n` for something already isogenous. If so the geometry is
bookkeeping. See [[flt-ring-has-no-division]] for the half of the same route that
is NOT bookkeeping.
