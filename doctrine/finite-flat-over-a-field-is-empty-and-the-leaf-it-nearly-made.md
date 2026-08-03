## "FINITE FLAT" OVER A FIELD IS EMPTY — and the leaf it nearly made false

(2026-07-31, caught before it was written down.) A leaf of the shape *"a closed
subscheme of a `ℚ̄`-scheme is determined by its `ℚ̄`-points"* is the residue of at
least three separate nodes in `ModularCurve/X0.lean`. The natural hypotheses to
copy across from the object at hand — a `CyclicSubgroupOfOrder`, whose fields are
`isClosedImmersion`, `isFinite`, `flat` — give a statement that is **FALSE**:

* over a FIELD every module is flat, so `IsFinite + Flat` says only "finite", and
  `A = 𝔸¹`, `C₁ = ` the origin, `C₂ = Spec ℚ̄[ε]` are two finite flat closed
  subschemes with the same `ℚ̄`-points (the only `Spec ℚ̄ ⟶ Spec ℚ̄[ε]` kills `ε`)
  that are not isomorphic.

Reducedness here does **not** come from flatness; it comes from Cartier's theorem,
which needs the GROUP structure — in this tree that is
`CyclicSubgroupOfOrder.etale_of_specQBase`, and the hypothesis to state is
`AlgebraicGeometry.Etale`, not `Flat`. Two further hypotheses are equally
load-bearing and equally easy to drop: `IsAlgClosed` (over `ℚ`,
`Spec ℚ[x]/(x²+1)` and `∅` have the same `ℚ`-points) and `IsClosedImmersion`
(`Spec K ⊔ Spec K` onto one point versus `Spec K`).

General form, and it is the cheap habit: **when a leaf says "determined by its
points", write down what happens at a NON-REDUCED subscheme, at a NON-CLOSED
point, and over a NON-ALGEBRAICALLY-CLOSED base, before you write the binders.**
Each of the three has a two-line counterexample, and each survives review, because
the hypotheses were copied verbatim from a structure where they were sufficient
*in combination with a field the leaf no longer mentions*.

