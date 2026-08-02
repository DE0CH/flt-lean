---
name: flt-eta-transformation-is-in-discriminant-lean
description: "The η transformation law under S is in mathlib's Discriminant.lean, not DedekindEta.lean — two audits searched the wrong file and closed the eta-quotient axis wrongly"
metadata: 
  node_type: memory
  type: project
  originSessionId: cfd8924c-c7a3-4996-a342-9e159300ce51
  modified: 2026-08-02T11:46:43.643Z
---

Two audits on `X0.lean`'s `x0HeckeCharpolyTable` leaves (2026-07-30, repeated
2026-07-31) concluded that the eta-quotient route is closed because
`Mathlib/NumberTheory/ModularForms/DedekindEta.lean` "stops at the ANALYTIC
properties of `η` (non-vanishing, differentiability, `logDeriv η = (πi/12)·E₂`)
and carries NO transformation law". **The first clause is true and the
conclusion does not follow: the transformation law is in the NEXT file.**

`Mathlib/NumberTheory/ModularForms/Discriminant.lean` at pin `a3364fa` has

* `ModularForm.eta_comp_eq_csqrt_I_inv` — `η(−1/z) = (√I)⁻¹·√z·η(z)` on `ℍ`,
  stated as a `Set.EqOn` over `upperHalfPlaneSet`;
* `eta_comp_eqOn_const_mul_csqrt_eta`, the `∃ c ≠ 0` form it is derived from;
* `discriminant_S_invariant` and `discriminant_T_invariant`, which are exactly
  the pattern for deriving `η(z+1) = e^{2πi/24}·η(z)` in a few lines from
  `eta`'s definition `𝕢 24 z * ∏'(1 − 𝕢-powers)`;
* `Δ` as a genuine `CuspForm 𝒮ℒ 12` (`coe_discriminant`), with `Δ = η²⁴` by
  definition (`discriminant`), so an eta quotient `f = ∏ η(δz)^{r_δ}` with
  `Σ r_δ = 4` satisfies `f²⁴ = ∏ Δ(δz)^{r_δ}` ON THE NOSE, no multiplier
  system anywhere.

That identity is the cheap half of the Ligozat route: for `γ ∈ Γ₀(N)` and
`δ ∣ N` one has `δ ∣ c`, so `Δ(δz)∣₁₂γ = Δ(δz)`, hence `(f∣₂γ)²⁴ = f²⁴` and
`f∣₂γ = ζ_γ·f` with `ζ_γ ∈ μ₂₄`. What remains is triviality of the character
`ζ : Γ₀(N) → μ₂₄` — the actual Ligozat congruences — and mathlib has no
generating set for `Γ₀(N)`, so that half IS still missing.

**APPLIED 2026-08-02 (`flt-lean-284`).** The false absence paragraph on
`exists_heckeMatrix_qCoeff_of_x0HeckeCharpolyTable` has been REPLACED in
`X0.lean` by a correction naming `eta_comp_eqOn_const_mul_csqrt_eta`,
`eta_comp_eq_csqrt_I_inv`, `discriminant_S_invariant`,
`discriminant_T_invariant` and `coe_discriminant`, and recording that what is
still missing is triviality of `ζ : Γ₀(N) → μ₂₄` (the Ligozat congruences),
for which the pin lacks a generating set for `Γ₀(N)`. So the axis is recorded
as HALF open. The twin paragraph on `finrank_cuspForm_of_x0HeckeCharpolyTable`
(the dimension leaf) was NOT touched and may still carry the wrong claim —
check it before re-deriving any of this.

**Why this matters:** an explicit spanning family at a level settles BOTH open
leaves of `x0HeckeCharpolyTable` there — `finrank_cuspForm_of_x0HeckeCharpolyTable`
(the dimension) and `exists_heckeMatrix_qCoeff_of_x0HeckeCharpolyTable` (the
Hecke matrix) — and it is the only axis of the five that was ever left open.

**The transferable lesson**: mathlib files are named for their SUBJECT, and a
lemma about `X` proven only because `Y` needed it lives in `Y`'s file. Grep the
whole `Mathlib/NumberTheory/ModularForms/` directory for the SYMBOL, not the
file named after it. Related: [[mathlib-states-point-facts-as-morphism-properties]],
[[flt-inventory-audits-understate-what-exists]],
[[flt-missing-machinery-may-be-downstream]].
