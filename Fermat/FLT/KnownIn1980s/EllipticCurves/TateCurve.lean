/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
-- `ValuationSubring.inertia_fixes_of_pow_eq_one` (step (b)), used in the
-- local unipotence assembly
import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.Henselian
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.LocalField.Basic
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
-- (was transitively supplied by the deleted ReductionBaseChange module)

/-!

# The Tate curve

Let `k` be a nonarchimedean local field and let `E/k` be an elliptic curve, given by a
minimal Weierstrass equation, with split multiplicative reduction. Tate's theory attaches
to `E` a canonical *Tate parameter*, an element `q = q(E)` of `k` with `0 < |q| < 1`, and
an isomorphism of groups `E(k) ≅ kˣ/qᶻ` (Tate's uniformisation), Galois-equivariantly
after base change to a separable closure.

These results are due to Tate, in a manuscript which
circulated from the early 1960s and was eventually published in 1995 as *A review of
non-Archimedean elliptic curves*. See also Roquette, *Analytic theory of elliptic
functions over local fields* (1970), and Silverman, *Advanced topics in the arithmetic
of elliptic curves*, V.3 and V.5, for textbook accounts.

VENDORING CHANGES (2026-07-16, Fermat project): the upstream FLT file states the
uniformisation as sorry-d *data* (`tateCurveEquiv`, `tateEquiv`,
`tateEquivSepClosure`), which would poison the meaning of every downstream statement
mentioning it (any property "of `tateEquiv`" would be a property of an arbitrary
`sorry`). Following the policy used for the Weil pairing
(`Fermat.FLT.EllipticCurve.WeilPairing.exists_weilPairing`), the data and its
satellite lemmas (`tateEquiv_baseChange`, `tateEquiv_galois`, `tatePoint`,
`tatePoint_baseChange`, `tatePoint_galois`, `tatePoint_mem_torsionBy_*`,
`weilPairing_tatePoint`) are replaced by ONE existential Prop node,
`exists_tateEquivSepClosure`: there exists a Galois-equivariant group isomorphism
`Ωˣ/qᶻ ≅ E(Ω)` over a separable closure `Ω`. This is the exact content consumers
need (the torsion-membership lemmas are formal consequences of any witness, and the
finite-level statements follow by restriction). The fully proven upstream material —
the Tate curve series, the valuation lemmas, the Tate parameter, and base-change
functoriality — is vendored verbatim. The upstream import of
`FLT.KnownIn1980s.EllipticCurves.WeilPairing` (sorry-d data) is dropped; the
Weil-pairing/uniformisation sign-coherence statement `weilPairing_tatePoint` is NOT
vendored (no current consumer; if one appears it must be stated as a *joint*
existential over both packages).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

/-! ### The Tate curve `E_q`

For `q` with `0 < |q| < 1` there is an explicit Weierstrass curve `E_q`, whose coefficients
are power series in `q` with integer coefficients, together with a uniformisation
`kˣ/qᶻ ≅ E_q(k)` given by explicit power series `X(u, q)`, `Y(u, q)` — all of it involving
no choices whatsoever, and commuting on the nose with every valuative morphism of fields.
The uniformisation of a general `E` with split multiplicative reduction is obtained by
transporting this one along an isomorphism `E_{q(E)} ≅ E` of Weierstrass curves
(`exists_variableChange_tateCurve` below), and *that* is the only choice in the theory:
there are exactly two such isomorphisms, differing by negation.
-/

section TateCurve

-- For the defining series we only need a topology on the field: this section makes sense
-- (and the series converge) over any field complete with respect to a rank 1
-- nonarchimedean valuation.
variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The coefficient `a₄(q) = -5s₃(q)` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₄ (q : k) : k :=
  -5 * ∑' n : ℕ, ((n + 1 : ℕ) : k) ^ 3 * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The coefficient `a₆(q) = -(5s₃(q) + 7s₅(q))/12` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)`; the integrality `12 ∣ 5n³ + 7n⁵` makes sense of the
division by `12` in every characteristic (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₆ (q : k) : k :=
  ∑' n : ℕ, -(((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12 : ℤ) : k) * q ^ (n + 1) /
    (1 - q ^ (n + 1))

/-- The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateCurve (q : k) : WeierstrassCurve k :=
  ⟨1, 0, 0, tateA₄ q, tateA₆ q⟩

end TateCurve

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the
-- evaluation at `j⁻¹` of an explicit integral power series. Here we state its
-- interaction with the valuation.

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
lemma WeierstrassCurve.tateParameter_eq {j : k} : WeierstrassCurve.tateParameter j =
    TateCurve.evalInt j⁻¹ TateCurve.jInvReverse := by
  rfl

/-- The Tate parameter of `j` has valuation exactly `|j|⁻¹`: the leading term `j⁻¹` of
the inverse series `q = j⁻¹ + 744j⁻² + ⋯` dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateParameter_eq {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) = (valuation k j)⁻¹ := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [map_zero] at hj
  have h := TateCurve.valuation_evalInt_eq j⁻¹ (inv_ne_zero hj0)
    (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj) TateCurve.constantCoeff_jInvReverse
    TateCurve.coeff_one_jInvReverse
  rw [WeierstrassCurve.tateParameter_eq, h, map_inv₀]

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 := by
  intro h
  have heq := valuation_tateParameter_eq hj
  rw [h, map_zero] at heq
  exact inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hj)) heq.symm

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 := by
  simpa [valuation_tateParameter_eq hj] using inv_lt_one_of_one_lt₀ hj

-- The next few lemmas transfer `mathlib`'s reduction-theoretic facts (stated for the adic
-- valuation of the discrete valuation ring `𝒪[k]`) to the canonical valuation of `k`,
-- through unit and maximal-ideal membership in `𝒪[k]`.

/-- An elliptic curve over `k` with bad (here multiplicative) reduction has discriminant of
valuation less than `1`: the discriminant of the integral model lies in the maximal ideal. -/
theorem WeierstrassCurve.valuation_Δ_lt_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.Δ < 1 := by
  have hbad := HasMultiplicativeReduction.badReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
  exact adicValuation_lt_one_iff.mp hbad

/-- An elliptic curve over `k` with multiplicative reduction has `c₄` of valuation exactly
`1`: `c₄` of the integral model is a unit of `𝒪[k]`. -/
theorem WeierstrassCurve.valuation_c₄_eq_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.c₄ = 1 := by
  have hmul := HasMultiplicativeReduction.multiplicativeReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
  exact adicValuation_eq_one_iff.mp hmul

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The discriminant of an elliptic curve has nonzero valuation. -/
theorem WeierstrassCurve.valuation_Δ_ne_zero (E : WeierstrassCurve k) [E.IsElliptic] :
    valuation k E.Δ ≠ 0 := by
  rw [(valuation k).ne_zero_iff, ← E.coe_Δ']
  exact Units.ne_zero _

/-- An elliptic curve over `k` with multiplicative reduction has `|j| = |c₄|³/|Δ| = |Δ|⁻¹`. -/
theorem WeierstrassCurve.valuation_j_eq (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.j = (valuation k E.Δ)⁻¹ := by
  rw [show E.j = (↑(E.Δ'⁻¹) : k) * E.c₄ ^ 3 from rfl, map_mul, map_pow,
    E.valuation_c₄_eq_one, one_pow, mul_one, Units.val_inv_eq_inv_val, map_inv₀, E.coe_Δ']

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j := by
  rw [E.valuation_j_eq]
  exact (one_lt_inv₀ (zero_lt_iff.mpr E.valuation_Δ_ne_zero)).mpr E.valuation_Δ_lt_one

/-- The Tate parameter of an elliptic curve `E`, given by a minimal Weierstrass equation with
split multiplicative reduction over a nonarchimedean local field `k`: the unique element
`q` of `k` with `0 < |q| < 1` such that `j(E) = j(q) = q⁻¹ + 744 + 196884q + ⋯`, defined
directly (with no appeal to choice) as `tateParameter E.j`, the inverse `j`-series
evaluated at `j(E)`. Equivalently, the unique `q` such that `E(k̄)` is Galois-equivariantly
isomorphic to `k̄ˣ/q^ℤ`. (The bare existence of an abstract isomorphism `E(k) ≅ kˣ/q^ℤ`
would not pin down `q`: already over `ℚ_p` the groups `ℚ_pˣ/p^ℤ` and `ℚ_pˣ/(p(1+p))^ℤ`
are isomorphic, even topologically.) -/
noncomputable def WeierstrassCurve.q (E : WeierstrassCurve k) [E.IsElliptic] : k :=
  tateParameter E.j

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation,
-- with split multiplicative reduction
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
  [E.IsMinimal 𝒪[k]]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

omit [E.IsMinimal 𝒪[k]] in
/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

/-- The Tate parameter as an element of `kˣ`. -/
noncomputable def WeierstrassCurve.qUnit : kˣ :=
  Units.mk0 E.q E.q_ne_zero

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement `∑_{n≥1} n³qⁿ/(1-qⁿ) = ∑_{n≥1} σ₃(n)qⁿ` for
`|q| < 1`: the defining series of `tateA₄` is the evaluation of the formal series
`a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧`. -/
theorem WeierstrassCurve.tateA₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalInt q TateCurve.a₄Formal := by
  have hF : ∀ n, PowerSeries.coeff n TateCurve.a₄Formal
      = ∑ d ∈ n.divisors, -5 * (d : ℤ) ^ 3 := by
    intro n
    rw [TateCurve.coeff_a₄Formal, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq _ hF]
  simp only [tateA₄]
  rw [← tsum_mul_left]
  exact tsum_congr fun m ↦ by push_cast; ring

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement for `tateA₆`, as for `tateA₄_eq_evalInt`; the
bookkeeping of the exact division by `12` uses `12 ∣ 5d³ + 7d⁵` termwise. -/
theorem WeierstrassCurve.tateA₆_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalInt q TateCurve.a₆Formal := by
  have h12 : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  set c : ℕ → ℤ := fun d ↦ -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) with hc
  -- the coefficients of `a₆Formal` are the divisor sums of `c`: the divisor sum commutes
  -- with the exact division by `12`
  have hF : ∀ N, PowerSeries.coeff N TateCurve.a₆Formal = ∑ d ∈ N.divisors, c d := by
    intro N
    rw [TateCurve.coeff_a₆Formal]
    symm
    simp only [hc]
    have hσ : ∑ d ∈ N.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5)
        = 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
      push_cast
      ring
    have hsum : (12 : ℤ) ∣ 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [← hσ]
      exact Finset.dvd_sum fun d _ ↦ h12 d
    have hterm : ∀ d ∈ N.divisors, -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) * 12
        = -(5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := fun d _ ↦ by
      rw [neg_mul, Int.ediv_mul_cancel (h12 d)]
    apply mul_right_cancel₀ (b := (12 : ℤ)) (by norm_num)
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm, neg_mul, Int.ediv_mul_cancel hsum,
      ← hσ, Finset.sum_neg_distrib]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq c hF]
  simp only [tateA₆]
  refine tsum_congr fun m ↦ ?_
  simp only [hc]
  push_cast
  ring

/-- The `a₄`-coefficient of the Tate curve has valuation less than `1`:
its defining series has vanishing constant term. -/
theorem WeierstrassCurve.valuation_tateA₄_lt_one (q : k)
    (hq : valuation k q < 1) : valuation k (tateA₄ q) < 1 := by
  rw [tateA₄_eq_evalInt q hq]
  calc valuation k (TateCurve.evalInt q TateCurve.a₄Formal)
      ≤ valuation k q ^ 1 := TateCurve.valuation_evalInt_le_pow q hq
        (fun m hm => by
          interval_cases m
          rw [TateCurve.coeff_a₄Formal]
          simp)
    _ = valuation k q := pow_one _
    _ < 1 := hq

/-- The `a₆`-coefficient of the Tate curve has valuation less than `1`. -/
theorem WeierstrassCurve.valuation_tateA₆_lt_one (q : k)
    (hq : valuation k q < 1) : valuation k (tateA₆ q) < 1 := by
  rw [tateA₆_eq_evalInt q hq]
  calc valuation k (TateCurve.evalInt q TateCurve.a₆Formal)
      ≤ valuation k q ^ 1 := TateCurve.valuation_evalInt_le_pow q hq
        (fun m hm => by
          interval_cases m
          rw [TateCurve.coeff_a₆Formal]
          simp)
    _ = valuation k q := pow_one _
    _ < 1 := hq

/-- The Tate curve as a Weierstrass curve over the ring of integers:
the coefficients `1, 0, 0, a₄(q), a₆(q)` are all integral. -/
noncomputable def WeierstrassCurve.tateCurveModel (q : k)
    (hq : valuation k q < 1) : WeierstrassCurve 𝒪[k] :=
  ⟨1, 0, 0, ⟨tateA₄ q, le_of_lt (valuation_tateA₄_lt_one q hq)⟩,
    ⟨tateA₆ q, le_of_lt (valuation_tateA₆_lt_one q hq)⟩⟩

/-- The base change of the integral Tate model is the Tate curve. -/
theorem WeierstrassCurve.tateCurveModel_baseChange (q : k)
    (hq : valuation k q < 1) :
    ((tateCurveModel q hq)⁄k) = tateCurve q := by
  ext <;> rfl

open PowerSeries in
/-- **Evaluation inverts formal units**: for a series with constant
coefficient `1`, the value of its formal inverse is the inverse of its
value (via `evalInt_mul` — the nonarchimedean Mertens theorem — and
`mul_invOfUnit`). -/
theorem TateCurve.evalInt_invOfUnit (q : k) (hq : valuation k q < 1)
    (F : ℤ⟦X⟧) (hF : PowerSeries.constantCoeff F = 1) :
    TateCurve.evalInt q (PowerSeries.invOfUnit F 1) =
      (TateCurve.evalInt q F)⁻¹ := by
  have hmul : F * PowerSeries.invOfUnit F 1 = 1 :=
    PowerSeries.mul_invOfUnit F 1 (by rw [hF]; rfl)
  have h1 : TateCurve.evalInt q F *
      TateCurve.evalInt q (PowerSeries.invOfUnit F 1) = 1 := by
    rw [← TateCurve.evalInt_mul q hq, hmul]
    rw [TateCurve.evalInt, tsum_eq_single 0 ?_]
    · simp
    · intro n hn
      simp [PowerSeries.coeff_one, hn]
  exact eq_inv_of_mul_eq_one_left
    (by rw [mul_comm] at h1; exact h1)

open scoped ArithmeticFunction.sigma in
/-- The integrality `12 ∣ 5σ₃(n) + 7σ₅(n)`: termwise, `12 ∣ 5d³ + 7d⁵`
(check mod `12` by `decide` on `ZMod 12`). -/
theorem TateCurve.dvd_five_sigma_three_add_seven_sigma_five (n : ℕ) :
    (12 : ℤ) ∣ 5 * σ 3 n + 7 * σ 5 n := by
  have hterm : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have h0 : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
    have h1 := h0 ((d : ℤ) : ZMod 12)
    have h2 : (((5 * d ^ 3 + 7 * d ^ 5 : ℤ)) : ZMod 12) = 0 := by
      push_cast
      exact h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  have hsum : (5 * σ 3 n + 7 * σ 5 n : ℤ) =
      ∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    · congr 1
      rw [ArithmeticFunction.sigma_apply]
      push_cast
      rfl
    · congr 1
      rw [ArithmeticFunction.sigma_apply]
      push_cast
      rfl
  rw [hsum]
  exact Finset.dvd_sum fun d _ => hterm (d : ℤ)



open PowerSeries in
/-- **The `c₄`-invariant of the Tate curve is the value of `c₄Formal`**
(PROVEN — the easy half of the `q`-expansion identities):
`c₄ = 1 − 48·a₄(q)` and `c₄Formal = 1 − 48·a₄Formal` term by term. -/
theorem WeierstrassCurve.c₄_tateCurve_eq_evalInt (q : k)
    (hq : valuation k q < 1) :
    (tateCurve q).c₄ = TateCurve.evalInt q TateCurve.c₄Formal := by
  have hc₄eq : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄]
    ring
  have hform : TateCurve.c₄Formal = 1 + (-48) * TateCurve.a₄Formal := by
    rw [TateCurve.c₄Formal, TateCurve.a₄Formal]
    ring
  -- evaluation of the constant series
  have h1 : TateCurve.evalInt q (1 : ℤ⟦X⟧) = 1 := by
    rw [TateCurve.evalInt, tsum_eq_single 0 ?_]
    · simp
    · intro n hn
      simp [PowerSeries.coeff_one, hn]
  -- evaluation of an integer multiple
  have hsc : TateCurve.evalInt q ((-48) * TateCurve.a₄Formal) =
      (-48 : k) * TateCurve.evalInt q TateCurve.a₄Formal := by
    rw [TateCurve.evalInt, TateCurve.evalInt, ← tsum_mul_left]
    congr 1
    funext n
    have hcoeff : PowerSeries.coeff n ((-48) * TateCurve.a₄Formal) =
        -48 * PowerSeries.coeff n TateCurve.a₄Formal := by
      have h0 : ((-48 : ℤ⟦X⟧)) * TateCurve.a₄Formal =
          (-48 : ℤ) • TateCurve.a₄Formal := by
        rw [zsmul_eq_mul]
        norm_num
      rw [h0, map_smul, smul_eq_mul]
    rw [hcoeff]
    push_cast
    ring
  rw [hc₄eq, tateA₄_eq_evalInt q hq, hform,
    TateCurve.evalInt_add (TateCurve.summable_evalInt q hq 1)
      (TateCurve.summable_evalInt q hq _), h1, hsc]
  ring

open Polynomial in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Tate curve has split multiplicative reduction** (Silverman,
ATAEC V.3.1(b)-adjacent, the reduction-type part): its coefficients
`a₄(q), a₆(q)` lie in the maximal ideal, so `c₄ = 1 − 48a₄ ≡ 1` (a
unit: Kraus–Laska minimality) while `Δ ∈ (a₄, a₆)` reduces to `0`; the
reduced curve is the nodal `y² + xy = x³`, whose node polynomial is
`X(X + 1)` — split. -/
theorem WeierstrassCurve.hasSplitMultiplicativeReduction_tateCurve
    (q : k) (hq : valuation k q < 1) :
    (tateCurve q).HasSplitMultiplicativeReduction 𝒪[k] := by
  classical
  have hA4 := valuation_tateA₄_lt_one q hq
  have hA6 := valuation_tateA₆_lt_one q hq
  -- `c₄` and `Δ` of the Tate curve, explicitly
  have hc₄eq : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄]
    ring
  have hΔeq : (tateCurve q).Δ =
      tateA₄ q * (tateA₄ q - 64 * (tateA₄ q) ^ 2 + 72 * tateA₆ q) +
      tateA₆ q * (-1 - 432 * tateA₆ q) := by
    simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  -- auxiliary bounds
  have h48v : valuation k (48 : k) ≤ 1 := by
    exact_mod_cast valuation_intCast_le_one (R := k) 48
  have h64v : valuation k (64 : k) ≤ 1 := by
    exact_mod_cast valuation_intCast_le_one (R := k) 64
  have h72v : valuation k (72 : k) ≤ 1 := by
    exact_mod_cast valuation_intCast_le_one (R := k) 72
  have h432v : valuation k (432 : k) ≤ 1 := by
    exact_mod_cast valuation_intCast_le_one (R := k) 432
  have hsmall : ∀ x y : k, valuation k x < 1 → valuation k y ≤ 1 →
      valuation k (x * y) < 1 := by
    intro x y hx hy
    rw [map_mul]
    calc valuation k x * valuation k y ≤ valuation k x * 1 :=
        mul_le_mul' le_rfl hy
      _ = valuation k x := mul_one _
      _ < 1 := hx
  have h48 : valuation k (48 * tateA₄ q) < 1 := by
    rw [map_mul]
    calc valuation k (48 : k) * valuation k (tateA₄ q)
        ≤ 1 * valuation k (tateA₄ q) := mul_le_mul' h48v le_rfl
      _ = valuation k (tateA₄ q) := one_mul _
      _ < 1 := hA4
  have hc₄K : valuation k (tateCurve q).c₄ = 1 := by
    rw [hc₄eq]
    exact Valuation.map_one_sub_of_lt (valuation k) h48
  have hΔK : valuation k (tateCurve q).Δ < 1 := by
    rw [hΔeq]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · refine hsmall _ _ hA4 ?_
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · refine le_trans (Valuation.map_sub _ _ _) (max_le (le_of_lt hA4) ?_)
        rw [map_mul, map_pow]
        exact mul_le_one' h64v (pow_le_one' (le_of_lt hA4) 2)
      · rw [map_mul]
        exact mul_le_one' h72v (le_of_lt hA6)
    · refine hsmall _ _ hA6 ?_
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · rw [Valuation.map_neg, Valuation.map_one]
      · rw [map_mul]
        exact mul_le_one' h432v (le_of_lt hA6)
  -- integrality and the adic conversions
  haveI hint : IsIntegral 𝒪[k] (tateCurve q) :=
    ⟨⟨tateCurveModel q hq, (tateCurveModel_baseChange q hq).symm⟩⟩
  have hc₄mem : (tateCurve q).c₄ ∈ (valuation k).integer := le_of_eq hc₄K
  have hΔmem : (tateCurve q).Δ ∈ (valuation k).integer := le_of_lt hΔK
  have hc₄adic : (IsDiscreteValuationRing.maximalIdeal
      𝒪[k]).valuation k ((tateCurve q).c₄) = 1 :=
    (ValuativeRel.adicValuation_eq_one_iff (K := k)
      (x := ⟨(tateCurve q).c₄, hc₄mem⟩)).mpr hc₄K
  have hΔadic : (IsDiscreteValuationRing.maximalIdeal
      𝒪[k]).valuation k ((tateCurve q).Δ) < 1 :=
    (ValuativeRel.adicValuation_lt_one_iff (K := k)
      (x := ⟨(tateCurve q).Δ, hΔmem⟩)).mpr hΔK
  -- residues of the coefficients vanish
  have hresA : (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
      (⟨tateA₄ q, le_of_lt hA4⟩ : 𝒪[k]) = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [IsLocalRing.mem_maximalIdeal]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hA4
  have hresB : (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
      (⟨tateA₆ q, le_of_lt hA6⟩ : 𝒪[k]) = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [IsLocalRing.mem_maximalIdeal]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hA6
  have hredmodel : (tateCurveModel q hq).map
      (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) =
      ⟨1, 0, 0, 0, 0⟩ := by
    ext
    · show (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 1 = 1
      exact map_one _
    · show (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 0 = 0
      exact map_zero _
    · show (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 0 = 0
      exact map_zero _
    · exact hresA
    · exact hresB
  -- assemble
  have hmin : IsMinimal 𝒪[k] (tateCurve q) :=
    isMinimal_of_valuation_c₄_eq_one (R := 𝒪[k]) (tateCurve q) hc₄adic
  have hmult : (tateCurve q).HasMultiplicativeReduction 𝒪[k] :=
    { toIsMinimal := hmin
      badReduction := hΔadic
      multiplicativeReduction := hc₄adic }
  refine { hmult with splitMultiplicativeReduction := ?_ }
  have hIM : (tateCurve q).integralModel 𝒪[k] = tateCurveModel q hq := by
    haveI : IsIntegral 𝒪[k] ((tateCurveModel q hq)⁄k) :=
      ⟨⟨tateCurveModel q hq, rfl⟩⟩
    have h0 := integralModel_baseChange (K := k) 𝒪[k] (tateCurveModel q hq)
    convert h0 using 2
    exact (tateCurveModel_baseChange q hq).symm
  rw [hIM]
  -- the reduced node polynomial is `X (X + 1)`
  have hc₄red : (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
      ((tateCurveModel q hq).c₄) = 1 := by
    rw [← WeierstrassCurve.map_c₄, hredmodel]
    show WeierstrassCurve.c₄ ⟨1, 0, 0, 0, 0⟩ = 1
    simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  have ha₁red : (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
      ((tateCurveModel q hq).a₁ * (tateCurveModel q hq).c₄) = 1 := by
    rw [map_mul, hc₄red]
    show (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 1 * 1 = 1
    rw [map_one, one_mul]
  have hconstred : (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
      (54 * (tateCurveModel q hq).b₆ -
        3 * (tateCurveModel q hq).b₂ * (tateCurveModel q hq).b₄ +
        (tateCurveModel q hq).a₂ * (tateCurveModel q hq).c₄) = 0 := by
    rw [map_add, map_sub, map_mul, map_mul, map_mul, map_mul,
      ← WeierstrassCurve.map_b₆, ← WeierstrassCurve.map_b₂,
      ← WeierstrassCurve.map_b₄, ← WeierstrassCurve.map_c₄, hredmodel]
    show (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 54 *
        WeierstrassCurve.b₆ ⟨1, 0, 0, 0, 0⟩ -
      (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k])) 3 *
        WeierstrassCurve.b₂ ⟨1, 0, 0, 0, 0⟩ *
        WeierstrassCurve.b₄ ⟨1, 0, 0, 0, 0⟩ +
      (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
        (tateCurveModel q hq).a₂ *
        WeierstrassCurve.c₄ ⟨1, 0, 0, 0, 0⟩ = 0
    have hb₆ : WeierstrassCurve.b₆ (⟨1, 0, 0, 0, 0⟩ :
        WeierstrassCurve (IsLocalRing.ResidueField 𝒪[k])) = 0 := by
      simp [WeierstrassCurve.b₆]
    have hb₄ : WeierstrassCurve.b₄ (⟨1, 0, 0, 0, 0⟩ :
        WeierstrassCurve (IsLocalRing.ResidueField 𝒪[k])) = 0 := by
      simp [WeierstrassCurve.b₄]
    have ha₂ : (tateCurveModel q hq).a₂ = 0 := rfl
    rw [hb₆, hb₄, ha₂, map_zero]
    ring
  have hpoly : (Polynomial.map (algebraMap 𝒪[k]
      (IsLocalRing.ResidueField 𝒪[k]))
      (Polynomial.C ((tateCurveModel q hq)).c₄ * Polynomial.X ^ 2 +
        Polynomial.C ((tateCurveModel q hq).a₁ *
          (tateCurveModel q hq).c₄) * Polynomial.X -
        Polynomial.C (54 * (tateCurveModel q hq).b₆ -
          3 * (tateCurveModel q hq).b₂ * (tateCurveModel q hq).b₄ +
          (tateCurveModel q hq).a₂ * (tateCurveModel q hq).c₄))) =
      Polynomial.X ^ 2 + Polynomial.X := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
      hc₄red, ha₁red, hconstred]
    simp
  rw [hpoly]
  -- `X² + X = X (X + 1)` splits
  have hfac : (Polynomial.X ^ 2 + Polynomial.X :
      Polynomial (IsLocalRing.ResidueField 𝒪[k])) =
      Polynomial.X * (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.C_1]
    ring
  rw [hfac]
  exact Polynomial.Splits.X.mul (Polynomial.Splits.X_add_C 1)

open PowerSeries in
/-- The constant coefficient of `c₄Formal` is `1`. -/
theorem TateCurve.constantCoeff_c₄Formal :
    PowerSeries.constantCoeff TateCurve.c₄Formal = 1 := by
  simp [TateCurve.c₄Formal, TateCurve.sInt]

open PowerSeries in
/-- **The formal discriminant identity**: the discriminant polynomial of
the formal Tate quintuple `⟨1, 0, 0, a₄Formal, a₆Formal⟩` equals
`ΔFormal`. Definitional after the 2026-07-18 refactor: `ΔFormal` *is*
defined (in `TateParameter.lean`) as this discriminant polynomial, its
classical description as the `η²⁴`-product `X·∏(1 − Xⁿ)²⁴` (Jacobi,
Silverman ATAEC V.3.1(b)) being consumed nowhere in the development —
only the coefficient facts `constantCoeff_ΔFormal`/`coeff_one_ΔFormal`,
now proven directly from the polynomial, were ever used. -/
theorem TateCurve.ΔFormal_eq :
    -TateCurve.a₆Formal + TateCurve.a₄Formal ^ 2 -
      64 * TateCurve.a₄Formal ^ 3 - 432 * TateCurve.a₆Formal ^ 2 +
      72 * TateCurve.a₄Formal * TateCurve.a₆Formal =
    TateCurve.ΔFormal :=
  rfl

open PowerSeries in
/-- Integer-scalar multiples pass through evaluation (extracted from
the `c₄`/`c₆` computations). -/
theorem TateCurve.evalInt_intCast_mul (q : k)
    (c : ℤ) (F : ℤ⟦X⟧) :
    TateCurve.evalInt q ((c : ℤ⟦X⟧) * F) =
      (c : k) * TateCurve.evalInt q F := by
  rw [TateCurve.evalInt, TateCurve.evalInt, ← tsum_mul_left]
  congr 1
  funext n
  have h0 : ((c : ℤ⟦X⟧)) * F = (c : ℤ) • F := by
    rw [zsmul_eq_mul]
  have hcoeff : PowerSeries.coeff n ((c : ℤ⟦X⟧) * F) =
      c * PowerSeries.coeff n F := by
    rw [h0, map_smul, smul_eq_mul]
  rw [hcoeff]
  push_cast
  ring

open PowerSeries in
/-- **The discriminant of the Tate curve is the value of `ΔFormal`**
(derived from the formal identity leaf by the evaluation ring
homomorphism): the discriminant of `y² + xy = x³ + a₄(q)x + a₆(q)` is
`q·∏(1 − qⁿ)²⁴`. -/
theorem WeierstrassCurve.Δ_tateCurve_eq_evalInt (q : k)
    (hq : valuation k q < 1) :
    (tateCurve q).Δ = TateCurve.evalInt q TateCurve.ΔFormal := by
  have hΔeq : (tateCurve q).Δ =
      -(tateA₆ q) + (tateA₄ q) ^ 2 - 64 * (tateA₄ q) ^ 3 -
        432 * (tateA₆ q) ^ 2 + 72 * (tateA₄ q) * (tateA₆ q) := by
    simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [hΔeq, ← TateCurve.ΔFormal_eq]
  -- push the evaluation through the polynomial combination
  set A : k := TateCurve.evalInt q TateCurve.a₄Formal with hA
  set B : k := TateCurve.evalInt q TateCurve.a₆Formal with hB
  have hA' : tateA₄ q = A := tateA₄_eq_evalInt q hq
  have hB' : tateA₆ q = B := tateA₆_eq_evalInt q hq
  have hexp : (-TateCurve.a₆Formal + TateCurve.a₄Formal ^ 2 -
      64 * TateCurve.a₄Formal ^ 3 - 432 * TateCurve.a₆Formal ^ 2 +
      72 * TateCurve.a₄Formal * TateCurve.a₆Formal) =
      ((-1 : ℤ) : ℤ⟦X⟧) * TateCurve.a₆Formal +
      TateCurve.a₄Formal ^ 2 +
      ((-64 : ℤ) : ℤ⟦X⟧) * TateCurve.a₄Formal ^ 3 +
      ((-432 : ℤ) : ℤ⟦X⟧) * TateCurve.a₆Formal ^ 2 +
      ((72 : ℤ) : ℤ⟦X⟧) * (TateCurve.a₄Formal * TateCurve.a₆Formal) := by
    push_cast
    ring
  rw [hexp]
  rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
    (TateCurve.summable_evalInt q hq _)]
  rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
    (TateCurve.summable_evalInt q hq _)]
  rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
    (TateCurve.summable_evalInt q hq _)]
  rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
    (TateCurve.summable_evalInt q hq _)]
  rw [TateCurve.evalInt_intCast_mul q, TateCurve.evalInt_intCast_mul q,
    TateCurve.evalInt_intCast_mul q, TateCurve.evalInt_intCast_mul q,
    TateCurve.evalInt_pow q hq, TateCurve.evalInt_pow q hq,
    TateCurve.evalInt_pow q hq, TateCurve.evalInt_mul q hq]
  rw [hA', hB', ← hA, ← hB]
  push_cast
  ring

open PowerSeries in
/-- **Evaluation commutes with formal substitution** (the
formal-to-convergent bridge anticipated by `TateParameter.lean`): for
`G` with vanishing constant term and `|x| < 1`, the value of the
composite `F ∘ G` is the value of `F` at the value of `G` — both sides
are limits of the same double series, rearranged by the nonarchimedean
Mertens/Fubini argument (note `|evalInt x G| ≤ |x| < 1` by
`valuation_evalInt_le_pow`, so the outer evaluation converges). -/
theorem TateCurve.evalInt_subst (x : k) (hx : valuation k x < 1)
    (G F : ℤ⟦X⟧) (hG : PowerSeries.constantCoeff G = 0) :
    TateCurve.evalInt x (PowerSeries.subst G F) =
      TateCurve.evalInt (TateCurve.evalInt x G) F := by
  classical
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : IsUniformAddGroup 𝒪[k] :=
    inferInstanceAs (IsUniformAddGroup 𝒪[k].toAddSubgroup)
  have hind : Topology.IsInducing ((↑) : 𝒪[k] → k) := ⟨rfl⟩
  have hφ : Continuous (Int.castRingHom 𝒪[k]) := continuous_of_discreteTopology
  -- the generalized `evalInt = eval₂Hom` identification (as in `evalInt_mul`)
  have key : ∀ (q : k) (hq : valuation k q < 1)
      (ha : PowerSeries.HasEval (⟨q, hq.le⟩ : 𝒪[k])) (H : ℤ⟦X⟧),
      TateCurve.evalInt q H = (PowerSeries.eval₂Hom hφ ha H : k) := by
    intro q hq ha H
    change (∑' n : ℕ, ((PowerSeries.coeff n H : ℤ) : k) * q ^ n) = _
    rw [PowerSeries.coe_eval₂Hom hφ ha]
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def] using (PowerSeries.hasSum_eval₂ hφ ha H).map
      (Subring.subtype 𝒪[k]).toAddMonoidHom continuous_subtype_val
  have hax : PowerSeries.HasEval (⟨x, hx.le⟩ : 𝒪[k]) :=
    hind.tendsto_nhds_iff.mpr (by
      simpa [Function.comp_def] using TateCurve.tendsto_pow_nhds_zero hx)
  -- the value of `G` at `x` is again in the open unit disc
  have hyval : valuation k (TateCurve.evalInt x G) < 1 := by
    refine lt_of_le_of_lt ?_ hx
    have h1 := TateCurve.valuation_evalInt_le_pow x hx (F := G) (M := 1)
      (fun m hm => by
        interval_cases m
        rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact hG)
    rwa [pow_one] at h1
  have hay : PowerSeries.HasEval (⟨TateCurve.evalInt x G, hyval.le⟩ : 𝒪[k]) :=
    hind.tendsto_nhds_iff.mpr (by
      simpa [Function.comp_def] using TateCurve.tendsto_pow_nhds_zero hyval)
  -- the `eval₂`-value of `G` is that point
  have hGpt : PowerSeries.eval₂Hom hφ hax G =
      (⟨TateCurve.evalInt x G, hyval.le⟩ : 𝒪[k]) := by
    apply Subtype.coe_injective
    exact (key x hx hax G).symm
  -- substitution compatibility at the `𝒪[k]`-level (mathlib's
  -- `MvPowerSeries.eval₂_subst`, with the discrete uniformity on `ℤ`)
  letI : UniformSpace ℤ := ⊥
  haveI : DiscreteUniformity ℤ := inferInstance
  have hsub : PowerSeries.eval₂Hom hφ hax (PowerSeries.subst G F) =
      PowerSeries.eval₂Hom hφ hay F := by
    have halg : (Int.castRingHom 𝒪[k]) = algebraMap ℤ 𝒪[k] :=
      (algebraMap_int_eq 𝒪[k]).symm
    have hsubstG : PowerSeries.HasSubst (G : MvPowerSeries Unit ℤ) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hG
    have h0 := MvPowerSeries.eval₂_subst (R := ℤ) (S := ℤ) (T := 𝒪[k])
      (σ := Unit) (τ := Unit)
      (a := fun _ : Unit => (G : MvPowerSeries Unit ℤ))
      hsubstG.const
      (b := fun _ : Unit => (⟨x, hx.le⟩ : 𝒪[k]))
      (PowerSeries.hasEval hax) F
    have hcoe1 := congrFun (PowerSeries.coe_eval₂Hom hφ hax)
      (PowerSeries.subst G F)
    have hcoe2 := congrFun (PowerSeries.coe_eval₂Hom hφ hay) F
    rw [hcoe1, hcoe2]
    show MvPowerSeries.eval₂ (Int.castRingHom 𝒪[k])
        (fun _ : Unit => (⟨x, hx.le⟩ : 𝒪[k]))
        (MvPowerSeries.subst (fun _ : Unit => (G : MvPowerSeries Unit ℤ)) F) =
      MvPowerSeries.eval₂ (Int.castRingHom 𝒪[k])
        (fun _ : Unit => (⟨TateCurve.evalInt x G, hyval.le⟩ : 𝒪[k])) F
    rw [halg]
    rw [h0]
    congr 1
    funext s
    have h1 : MvPowerSeries.eval₂ (algebraMap ℤ 𝒪[k])
        (fun _ : Unit => (⟨x, hx.le⟩ : 𝒪[k]))
        ((fun _ : Unit => (G : MvPowerSeries Unit ℤ)) s) =
        PowerSeries.eval₂ (algebraMap ℤ 𝒪[k]) (⟨x, hx.le⟩ : 𝒪[k]) G := rfl
    rw [h1, ← halg, ← congrFun (PowerSeries.coe_eval₂Hom hφ hax) G]
    exact hGpt
  -- conclude through the identifications
  rw [key x hx hax, key (TateCurve.evalInt x G) hyval hay, hsub]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] in
/-- **The `j`-invariant of the Tate curve** (derived from the
Δ-evaluation and substitution-evaluation leaves and the PROVEN
`c₄`-identity): the Tate curve of the Tate parameter of `E` is elliptic
with `j`-invariant `j(E)`. -/
theorem WeierstrassCurve.isElliptic_tateCurve_and_j :
    ∃ _ : (tateCurve E.q).IsElliptic, (tateCurve E.q).j = E.j := by
  have hq0 : E.q ≠ 0 := E.q_ne_zero
  have hq : valuation k E.q < 1 := E.valuation_q_lt_one
  -- the discriminant value and its nonvanishing
  have hΔ : (tateCurve E.q).Δ = TateCurve.evalInt E.q TateCurve.ΔFormal :=
    Δ_tateCurve_eq_evalInt E.q hq
  have hvΔ : valuation k ((tateCurve E.q).Δ) = valuation k E.q := by
    rw [hΔ]
    exact TateCurve.valuation_evalInt_eq E.q hq0 hq
      TateCurve.constantCoeff_ΔFormal TateCurve.coeff_one_ΔFormal
  have hΔne : (tateCurve E.q).Δ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvΔ
    exact hq0 ((valuation k).zero_iff.mp hvΔ.symm)
  haveI hell : (tateCurve E.q).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔne⟩
  refine ⟨hell, ?_⟩
  -- `c₄` is a unit
  have hc₄eq : (tateCurve E.q).c₄ = 1 - 48 * tateA₄ E.q := by
    simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄]
    ring
  have h48v : valuation k (48 : k) ≤ 1 := by
    exact_mod_cast valuation_intCast_le_one (R := k) 48
  have h48 : valuation k (48 * tateA₄ E.q) < 1 := by
    rw [map_mul]
    calc valuation k (48 : k) * valuation k (tateA₄ E.q)
        ≤ 1 * valuation k (tateA₄ E.q) := mul_le_mul' h48v le_rfl
      _ = valuation k (tateA₄ E.q) := one_mul _
      _ < 1 := valuation_tateA₄_lt_one E.q hq
  have hc₄K : valuation k (tateCurve E.q).c₄ = 1 := by
    rw [hc₄eq]
    exact Valuation.map_one_sub_of_lt (valuation k) h48
  have hc₄ne : (tateCurve E.q).c₄ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc₄K
    exact zero_ne_one hc₄K
  -- the value of `jInv` at `E.q` is `j(E_q)⁻¹`
  have hcc₄3 : PowerSeries.constantCoeff (TateCurve.c₄Formal ^ 3) = 1 := by
    rw [map_pow, TateCurve.constantCoeff_c₄Formal, one_pow]
  have hjinv : TateCurve.evalInt E.q TateCurve.jInv =
      ((tateCurve E.q).j)⁻¹ := by
    rw [TateCurve.jInv, TateCurve.evalInt_mul E.q hq,
      TateCurve.evalInt_invOfUnit E.q hq _ hcc₄3,
      TateCurve.evalInt_pow E.q hq, ← c₄_tateCurve_eq_evalInt E.q hq, ← hΔ]
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
      (tateCurve E.q).coe_Δ']
    rw [mul_inv, inv_inv]
  -- the composition: the value of `jInv` at the Tate parameter is `j(E)⁻¹`
  have hvjinv : valuation k (E.j)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ E.one_lt_valuation_j
  have hcomp : TateCurve.evalInt E.q TateCurve.jInv = (E.j)⁻¹ := by
    have hqdef : E.q = TateCurve.evalInt (E.j)⁻¹ TateCurve.jInvReverse := by
      rw [show E.q = WeierstrassCurve.tateParameter E.j from rfl,
        WeierstrassCurve.tateParameter_eq]
    rw [hqdef, ← TateCurve.evalInt_subst (E.j)⁻¹ hvjinv _ _
      TateCurve.constantCoeff_jInvReverse,
      TateCurve.jInv_subst_jInvReverse, TateCurve.evalInt_X]
  -- conclude by inverting
  have hjEne : E.j ≠ 0 := by
    intro h0
    have h1 := E.one_lt_valuation_j
    rw [h0, map_zero] at h1
    exact absurd h1 (not_lt.mpr zero_le)
  have hkey : ((tateCurve E.q).j)⁻¹ = (E.j)⁻¹ := by
    rw [← hjinv, hcomp]
  exact inv_injective hkey

/-- **Invariance of split multiplicative reduction under change of
Weierstrass coordinates**, phrased through the minimal model (mathlib's
`HasSplitMultiplicativeReduction` extends `IsMinimal`, a property of
the literal model, so `C • W` itself — generally neither integral nor
minimal — cannot carry the class; its minimal model can): if `W` has
split multiplicative reduction, then so does the minimal model of
`C • W` for any change of variables `C` over `k`. Derived from the
vendored uniqueness-of-minimal-models machinery: `W` and
`(C • W).minimal 𝒪[k]` are two minimal models of one `k`-isomorphism
class, related by the variable change
`((C • W).exists_isMinimal 𝒪[k]).choose * C`, so
`HasSplitMultiplicativeReduction.of_isMinimal_smul` (Silverman
VII.1.3(b): the connecting change has unit `u` and integral `r, s, t`,
under which the reduced node polynomial transforms by an affine
substitution and a unit-square scaling) transfers splitness. -/
theorem WeierstrassCurve.hasSplitMultiplicativeReduction_minimal_smul
    (W : WeierstrassCurve k) [W.IsElliptic]
    [W.HasSplitMultiplicativeReduction 𝒪[k]]
    (C : VariableChange k) :
    ((C • W).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] := by
  have hD : ((((C • W)).exists_isMinimal 𝒪[k]).choose * C) • W =
      (C • W).minimal 𝒪[k] := by
    rw [mul_smul]
    rfl
  exact WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul
    (R := 𝒪[k]) _ hD inferInstance

/-- **The split criterion over the local field** (the arithmetic core
of the descent half of Tate's theorem V.5.3, PROVEN by Hensel lifting
over `𝒪[k]` in both residue characteristics): a curve
with split multiplicative reduction over the nonarchimedean local
field `k` has `-c₄c₆ ∈ (kˣ)²`. Content (Silverman AEC App. A;
`-c₄c₆` is the discriminant of the node polynomial up to squares, and
its square class is the twisting class of the two tangent directions):
`c₄` and `c₆` of the integral model are units by multiplicative
reduction; for odd residue characteristic, splitness of the reduced
node polynomial means its discriminant `-c₄c₆` is a residue square
(`nodePoly_map_splits_iff_isSquare`), and Hensel lifts a unit with
square residue to a square of `k`; for residue characteristic `2`,
splitness is the Artin–Schreier condition
(`nodePoly_map_splits_iff_of_two_eq_zero`), whose solvability is
equivalent, by a 2-adic Hensel argument at the finite level
`-c₄c₆ ≡ (a₁c₄/c₄)²-adjusted squares mod 4·𝔪`, to `-c₄c₆` being a
square in `k`. -/
theorem WeierstrassCurve.isSquare_neg_c₄_mul_c₆_of_split
    (E : WeierstrassCurve k) [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    IsSquare (-(E.c₄ * E.c₆)) := by
  classical
  set I : WeierstrassCurve 𝒪[k] := E.integralModel 𝒪[k] with hIdef
  set φ : 𝒪[k] →+* IsLocalRing.ResidueField 𝒪[k] :=
    algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]) with hφdef
  -- it suffices to produce a square root of `-(I.c₄ * I.c₆)` in `𝒪[k]`
  suffices hcore : IsSquare (-(I.c₄ * I.c₆)) by
    obtain ⟨a, ha⟩ := hcore
    refine ⟨algebraMap 𝒪[k] k a, ?_⟩
    have hx : algebraMap 𝒪[k] k (-(I.c₄ * I.c₆)) = -(E.c₄ * E.c₆) := by
      rw [map_neg, map_mul, hIdef, WeierstrassCurve.integralModel_c₄_eq 𝒪[k] E,
        WeierstrassCurve.integralModel_c₆_eq 𝒪[k] E]
    rw [← hx, ha, map_mul]
  -- the splitting of the node polynomial over the residue field
  have hsplit : (I.nodePoly.map φ).Splits :=
    ‹E.HasSplitMultiplicativeReduction 𝒪[k]›.splitMultiplicativeReduction
  -- residues of `c₄` and `c₆` are nonzero
  have hres4 : φ I.c₄ ≠ 0 :=
    WeierstrassCurve.residue_integralModel_c₄_ne_zero E 𝒪[k]
  have hres6 : φ I.c₆ ≠ 0 :=
    WeierstrassCurve.residue_integralModel_c₆_ne_zero E 𝒪[k]
  -- the Henselian structure of `𝒪[k]` at its maximal ideal (via completeness;
  -- the adic-completeness instance lives in the uniform-space world)
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI hhens : HenselianRing 𝒪[k] (IsLocalRing.maximalIdeal 𝒪[k]) :=
    inferInstance
  by_cases h2 : (2 : IsLocalRing.ResidueField 𝒪[k]) = 0
  · -- residue characteristic 2: the Artin–Schreier route
    -- `b := a₁c₄` is a unit: its residue squares to `-c₄c₆ ≠ 0` as `4 = 0`
    have h4 : (4 : IsLocalRing.ResidueField 𝒪[k]) = 0 := by
      linear_combination (2 : IsLocalRing.ResidueField 𝒪[k]) * h2
    have hdiscr := WeierstrassCurve.map_splitPolynomial_discrim φ I
    have hbres : φ (I.a₁ * I.c₄) ≠ 0 := by
      intro h0
      refine neg_ne_zero.mpr (mul_ne_zero hres4 hres6) ?_
      rw [← map_mul, ← map_neg]
      calc φ (-(I.c₄ * I.c₆))
          = φ (I.a₁ * I.c₄) ^ 2 - 4 * φ I.c₄ *
            (-φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) := hdiscr.symm
        _ = 0 := by rw [h0, h4]; ring
    have hbunit : IsUnit (I.a₁ * I.c₄) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      exact hbres (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    obtain ⟨U, hU⟩ := hbunit
    -- the Artin–Schreier datum from the splitting
    obtain ⟨z, hz⟩ := (WeierstrassCurve.nodePoly_map_splits_iff_of_two_eq_zero
      h2 φ I hres4 hres6).mp hsplit
    obtain ⟨t₀, ht₀⟩ := Ideal.Quotient.mk_surjective z
    replace ht₀ : φ t₀ = z := ht₀
    -- normalize: `c := γ/b²` with `γ := c₄·K₀`, so that `z² + z = φ c`
    set γ : 𝒪[k] := I.c₄ * (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)
      with hγdef
    set c : 𝒪[k] := γ * ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) ^ 2 with hcdef
    have hUinv : ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (I.a₁ * I.c₄) = 1 := by
      rw [← hU]
      exact_mod_cast U.inv_mul
    have hneg : ∀ a : IsLocalRing.ResidueField 𝒪[k], -a = a := by
      intro a
      linear_combination (-a) * h2
    have hUφ : φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * φ (I.a₁ * I.c₄) = 1 := by
      rw [← map_mul, hUinv, map_one]
    have hzc : z ^ 2 + z = φ c := by
      calc z ^ 2 + z
          = (φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * φ (I.a₁ * I.c₄)) ^ 2 *
            (z ^ 2 + z) := by rw [hUφ]; ring
        _ = φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) ^ 2 *
            (φ (I.a₁ * I.c₄) ^ 2 * (z ^ 2 + z)) := by ring
        _ = φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) ^ 2 *
            (φ I.c₄ * -φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) := by
            rw [hz]
        _ = -(φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) ^ 2 *
            (φ I.c₄ * φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄))) := by
            ring
        _ = φ ((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) ^ 2 *
            (φ I.c₄ * φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) :=
            hneg _
        _ = φ c := by rw [hcdef, hγdef, map_mul, map_pow, map_mul]; ring
    -- Hensel: solve `t² + t = c` in `𝒪[k]`
    have hmonic : (Polynomial.X ^ 2 +
        (Polynomial.X - Polynomial.C c) : Polynomial 𝒪[k]).Monic := by
      have hdeg : (Polynomial.X - Polynomial.C c : Polynomial 𝒪[k]).degree
          < (2 : ℕ) := by
        rw [Polynomial.degree_X_sub_C]
        exact_mod_cast one_lt_two
      exact Polynomial.monic_X_pow_add hdeg
    have hev : (Polynomial.X ^ 2 +
        (Polynomial.X - Polynomial.C c) : Polynomial 𝒪[k]).eval t₀ ∈
        IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show φ ((Polynomial.X ^ 2 +
        (Polynomial.X - Polynomial.C c) : Polynomial 𝒪[k]).eval t₀) = 0
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, map_add, map_pow, map_sub, ht₀]
      linear_combination hzc
    have hder : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k]))
        ((Polynomial.X ^ 2 +
          (Polynomial.X - Polynomial.C c) : Polynomial 𝒪[k]).derivative.eval
          t₀)) := by
      have hval : φ ((Polynomial.X ^ 2 +
          (Polynomial.X - Polynomial.C c) :
          Polynomial 𝒪[k]).derivative.eval t₀) = 2 * z + 1 := by
        simp only [Polynomial.derivative_sub,
          Polynomial.derivative_X_pow, Polynomial.derivative_X,
          Polynomial.derivative_C, sub_zero, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one, map_add, map_mul,
          map_one, Nat.cast_ofNat]
        rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, ht₀, map_ofNat]
      show IsUnit (φ ((Polynomial.X ^ 2 +
        (Polynomial.X - Polynomial.C c) :
        Polynomial 𝒪[k]).derivative.eval t₀))
      rw [hval, show (2 : IsLocalRing.ResidueField 𝒪[k]) * z + 1 = 1 by
        rw [h2]; ring]
      exact isUnit_one
    obtain ⟨a, ha, -⟩ := hhens.is_henselian
      (Polynomial.X ^ 2 + (Polynomial.X - Polynomial.C c)) hmonic t₀ hev hder
    have hac : a ^ 2 + a = c := by
      have h1 : (Polynomial.X ^ 2 +
          (Polynomial.X - Polynomial.C c) : Polynomial 𝒪[k]).eval a = 0 := ha
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at h1
      linear_combination h1
    -- assemble the square root: `-(c₄c₆) = (a₁c₄·(1+2a))²`
    have hb2c : γ = c * (I.a₁ * I.c₄) ^ 2 := by
      calc γ = γ * ((((U⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (I.a₁ * I.c₄)) ^ 2) := by
            rw [hUinv]; ring
        _ = c * (I.a₁ * I.c₄) ^ 2 := by rw [hcdef]; ring
    have hraw := I.splitPolynomial_discrim
    refine ⟨(I.a₁ * I.c₄) * (1 + 2 * a), ?_⟩
    calc -(I.c₄ * I.c₆)
        = (I.a₁ * I.c₄) ^ 2 + 4 * γ := by rw [hγdef]; linear_combination -hraw
      _ = (I.a₁ * I.c₄) ^ 2 * (1 + 4 * c) := by rw [hb2c]; ring
      _ = (I.a₁ * I.c₄) ^ 2 * (1 + 4 * (a ^ 2 + a)) := by rw [hac]
      _ = ((I.a₁ * I.c₄) * (1 + 2 * a)) * ((I.a₁ * I.c₄) * (1 + 2 * a)) := by
          ring
  · -- odd residue characteristic: Hensel on `X² - x`
    haveI : NeZero (2 : IsLocalRing.ResidueField 𝒪[k]) := ⟨h2⟩
    obtain ⟨z, hz⟩ := (WeierstrassCurve.nodePoly_map_splits_iff_isSquare
      φ I hres4).mp hsplit
    obtain ⟨t₀, ht₀⟩ := Ideal.Quotient.mk_surjective z
    replace ht₀ : φ t₀ = z := ht₀
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero, map_neg, map_mul] at hz
      exact mul_ne_zero hres4 hres6 (neg_eq_zero.mp hz)
    have hmonic : (Polynomial.X ^ 2 -
        Polynomial.C (-(I.c₄ * I.c₆)) : Polynomial 𝒪[k]).Monic :=
      Polynomial.monic_X_pow_sub_C _ (by norm_num)
    have hev : (Polynomial.X ^ 2 -
        Polynomial.C (-(I.c₄ * I.c₆)) : Polynomial 𝒪[k]).eval t₀ ∈
        IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show φ ((Polynomial.X ^ 2 -
        Polynomial.C (-(I.c₄ * I.c₆)) : Polynomial 𝒪[k]).eval t₀) = 0
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, map_sub, map_pow, ht₀]
      linear_combination -hz
    have hder : IsUnit ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k]))
        ((Polynomial.X ^ 2 -
          Polynomial.C (-(I.c₄ * I.c₆)) :
          Polynomial 𝒪[k]).derivative.eval t₀)) := by
      have hval : φ ((Polynomial.X ^ 2 -
          Polynomial.C (-(I.c₄ * I.c₆)) :
          Polynomial 𝒪[k]).derivative.eval t₀) = 2 * z := by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
          Polynomial.derivative_C, sub_zero, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          map_mul, Nat.cast_ofNat]
        rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, ht₀, map_ofNat]
      show IsUnit (φ ((Polynomial.X ^ 2 -
        Polynomial.C (-(I.c₄ * I.c₆)) :
        Polynomial 𝒪[k]).derivative.eval t₀))
      rw [hval, isUnit_iff_ne_zero]
      exact mul_ne_zero h2 hz0
    obtain ⟨a, ha, -⟩ := hhens.is_henselian
      (Polynomial.X ^ 2 - Polynomial.C (-(I.c₄ * I.c₆))) hmonic t₀ hev hder
    refine ⟨a, ?_⟩
    have h1 : (Polynomial.X ^ 2 -
        Polynomial.C (-(I.c₄ * I.c₆)) : Polynomial 𝒪[k]).eval a = 0 := ha
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at h1
    linear_combination -h1

/-- **Quadratic scaling twists between split curves are trivial**
(the arithmetic core of the descent half of Tate's theorem V.5.3,
derived from the split criterion): if the short Weierstrass curve
`y² = x³ + Ax + B` and its scaling twist `y² = x³ + w²Ax + w³B` both
have split multiplicative reduction over the nonarchimedean local
field `k` — phrased through their minimal models, since the short
equations themselves need not be minimal — then `w` is a square in
`k`. Derivation: the square class of `-c₄c₆` is invariant under
change of Weierstrass coordinates (`c₄`, `c₆` scale by `u⁻⁴`, `u⁻⁶`,
so `-c₄c₆` scales by the square `(u⁻⁵)²`), and the split criterion
makes `-c₄c₆` of both minimal models squares; since
`-c₄c₆` of the scaled short model is `w⁵` times that of the first,
and these are nonzero (`c₄`, `c₆` of a multiplicative-reduction
integral model are units), `w⁵` — hence `w` — is a square. -/
theorem WeierstrassCurve.isSquare_of_scaled_split
    (A B w : k) (hw : w ≠ 0)
    [i₁ : ((⟨0, 0, 0, A, B⟩ :
        WeierstrassCurve k).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k]]
    [i₂ : ((⟨0, 0, 0, w ^ 2 * A, w ^ 3 * B⟩ :
        WeierstrassCurve k).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k]] :
    IsSquare w := by
  set S : WeierstrassCurve k := ⟨0, 0, 0, A, B⟩ with hSdef
  set S' : WeierstrassCurve k := ⟨0, 0, 0, w ^ 2 * A, w ^ 3 * B⟩ with hS'def
  -- the square class of `-c₄c₆` transfers from a variable change
  have htrans : ∀ (T : VariableChange k) (W : WeierstrassCurve k),
      IsSquare (-((T • W).c₄ * (T • W).c₆)) → IsSquare (-(W.c₄ * W.c₆)) := by
    rintro T W ⟨r, hr⟩
    refine ⟨(T.u : k) ^ 5 * r, ?_⟩
    have huu : ((T.u⁻¹ : kˣ) : k) * (T.u : k) = 1 := by
      exact_mod_cast T.u.inv_mul
    rw [WeierstrassCurve.variableChange_c₄,
      WeierstrassCurve.variableChange_c₆] at hr
    calc -(W.c₄ * W.c₆)
        = (((T.u⁻¹ : kˣ) : k) * (T.u : k)) ^ 10 * -(W.c₄ * W.c₆) := by
          rw [huu]; ring
      _ = (T.u : k) ^ 10 *
          -(((T.u⁻¹ : kˣ) : k) ^ 4 * W.c₄ * (((T.u⁻¹ : kˣ) : k) ^ 6 * W.c₆)) := by
          ring
      _ = (T.u : k) ^ 10 * (r * r) := by rw [← hr]
      _ = ((T.u : k) ^ 5 * r) * ((T.u : k) ^ 5 * r) := by ring
  -- the split criterion applied to the two minimal models, transferred down
  have hsq₁ : IsSquare (-(S.c₄ * S.c₆)) :=
    htrans _ S ((S.minimal 𝒪[k]).isSquare_neg_c₄_mul_c₆_of_split)
  have hsq₂ : IsSquare (-(S'.c₄ * S'.c₆)) :=
    htrans _ S' ((S'.minimal 𝒪[k]).isSquare_neg_c₄_mul_c₆_of_split)
  -- `c₄`, `c₆` of the first curve are nonzero (units of the minimal model)
  have hc₄M : (S.minimal 𝒪[k]).c₄ ≠ 0 := by
    intro h0
    have h1 := WeierstrassCurve.integralModel_c₄_eq 𝒪[k] (S.minimal 𝒪[k])
    rw [h0] at h1
    have h2 : (WeierstrassCurve.integralModel 𝒪[k] (S.minimal 𝒪[k])).c₄ = 0 :=
      IsFractionRing.injective 𝒪[k] k (by rw [h1, map_zero])
    exact WeierstrassCurve.residue_integralModel_c₄_ne_zero (S.minimal 𝒪[k])
      𝒪[k] (by rw [h2, map_zero])
  have hc₆M : (S.minimal 𝒪[k]).c₆ ≠ 0 := by
    intro h0
    have h1 := WeierstrassCurve.integralModel_c₆_eq 𝒪[k] (S.minimal 𝒪[k])
    rw [h0] at h1
    have h2 : (WeierstrassCurve.integralModel 𝒪[k] (S.minimal 𝒪[k])).c₆ = 0 :=
      IsFractionRing.injective 𝒪[k] k (by rw [h1, map_zero])
    exact WeierstrassCurve.residue_integralModel_c₆_ne_zero (S.minimal 𝒪[k])
      𝒪[k] (by rw [h2, map_zero])
  have hc₄S : S.c₄ ≠ 0 := by
    intro h0
    refine hc₄M ?_
    rw [show S.minimal 𝒪[k] = (S.exists_isMinimal 𝒪[k]).choose • S from rfl,
      WeierstrassCurve.variableChange_c₄, h0, mul_zero]
  have hc₆S : S.c₆ ≠ 0 := by
    intro h0
    refine hc₆M ?_
    rw [show S.minimal 𝒪[k] = (S.exists_isMinimal 𝒪[k]).choose • S from rfl,
      WeierstrassCurve.variableChange_c₆, h0, mul_zero]
  -- the `c`-invariants of the two short models
  have hc₄Sval : S.c₄ = -48 * A := by
    show (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).c₄ = -48 * A
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hc₆Sval : S.c₆ = -864 * B := by
    show (⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).c₆ = -864 * B
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring
  have hc₄S'val : S'.c₄ = -48 * (w ^ 2 * A) := by
    show (⟨0, 0, 0, w ^ 2 * A, w ^ 3 * B⟩ : WeierstrassCurve k).c₄ =
      -48 * (w ^ 2 * A)
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hc₆S'val : S'.c₆ = -864 * (w ^ 3 * B) := by
    show (⟨0, 0, 0, w ^ 2 * A, w ^ 3 * B⟩ : WeierstrassCurve k).c₆ =
      -864 * (w ^ 3 * B)
    simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring
  -- assemble: `w⁵·(-c₄c₆ of S) = -c₄c₆ of S'` and both are squares
  obtain ⟨r₁, hr₁⟩ := hsq₁
  obtain ⟨r₂, hr₂⟩ := hsq₂
  have hr₁0 : r₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero, neg_eq_zero, mul_eq_zero] at hr₁
    exact hr₁.elim hc₄S hc₆S
  refine ⟨r₂ / (w ^ 2 * r₁), ?_⟩
  rw [div_mul_div_comm, eq_div_iff
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hw) hr₁0)
      (mul_ne_zero (pow_ne_zero 2 hw) hr₁0))]
  -- goal: `w·(w²r₁)² = r₂²`, i.e. `w⁵·r₁² = r₂²`
  have hrel : w ^ 5 * -(S.c₄ * S.c₆) = -(S'.c₄ * S'.c₆) := by
    rw [hc₄Sval, hc₆Sval, hc₄S'val, hc₆S'val]
    ring
  rw [hr₁, hr₂] at hrel
  linear_combination hrel

/-- **Split multiplicative curves with equal `j` are isomorphic**
(the descent half of Tate's theorem V.5.3, derived from the two leaves
above): two elliptic curves over `k` (of characteristic zero), both
with split multiplicative reduction, and with the same `j`-invariant,
differ by a change of Weierstrass coordinates over `k` itself.
Derivation: put both curves in short normal form `y² = x³ + Aᵢx + Bᵢ`
(char `k` = 0); split multiplicative reduction transfers to the
minimal models of the short equations by the invariance leaf;
`Aᵢ ≠ 0` since `Aᵢ = 0` forces `j = 0`, and `Bᵢ ≠ 0` since `Bᵢ = 0`
forces `j = 1728`, both contradicting `|j| > 1`;
equal `j` gives `A₁³B₂² = A₂³B₁²`, so `w := B₂A₁/(B₁A₂)` satisfies
`A₂ = w²A₁`, `B₂ = w³B₁` — the second short model is the scaling twist
of the first by `w`; both being split, the arithmetic-core leaf makes
`w = v²` a square, and scaling by `v⁻¹` is a change of variables over
`k` carrying the first short model to the second. -/
theorem WeierstrassCurve.exists_variableChange_of_j_eq_of_split
    [CharZero k]
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    [W₁.HasSplitMultiplicativeReduction 𝒪[k]]
    [W₂.HasSplitMultiplicativeReduction 𝒪[k]]
    (hj : W₁.j = W₂.j) :
    ∃ C : VariableChange k, C • W₁ = W₂ := by
  haveI h2 : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  haveI h3 : Invertible (3 : k) := invertibleOfNonzero three_ne_zero
  obtain ⟨C₁, hC₁⟩ := W₁.exists_variableChange_isShortNF
  obtain ⟨C₂, hC₂⟩ := W₂.exists_variableChange_isShortNF
  -- the `j`-invariants of the short models agree, and exceed `1` in valuation
  have hj' : (C₁ • W₁).j = (C₂ • W₂).j := by
    rw [WeierstrassCurve.variableChange_j, WeierstrassCurve.variableChange_j, hj]
  have hjv₁ : 1 < valuation k (C₁ • W₁).j := by
    rw [WeierstrassCurve.variableChange_j]
    exact W₁.one_lt_valuation_j
  have hjv₂ : 1 < valuation k (C₂ • W₂).j := by
    rw [WeierstrassCurve.variableChange_j]
    exact W₂.one_lt_valuation_j
  -- notation for the short coefficients
  set A₁ := (C₁ • W₁).a₄ with hA₁def
  set B₁ := (C₁ • W₁).a₆ with hB₁def
  set A₂ := (C₂ • W₂).a₄ with hA₂def
  set B₂ := (C₂ • W₂).a₆ with hB₂def
  -- the discriminants are nonzero and `j = Δ⁻¹c₄³`
  have hΔ : ∀ (W : WeierstrassCurve k) [W.IsElliptic], W.Δ ≠ 0 := by
    intro W _ h0
    have h1 := W.valuation_Δ_ne_zero
    rw [h0, map_zero] at h1
    exact h1 rfl
  have hjeq : ∀ (W : WeierstrassCurve k) [W.IsElliptic],
      W.j = (W.Δ)⁻¹ * W.c₄ ^ 3 := by
    intro W _
    rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl,
      Units.val_inv_eq_inv_val, W.coe_Δ']
  -- `Aᵢ ≠ 0`: otherwise `c₄ = -48Aᵢ = 0`, so `j = 0`, contradicting `1 < |j|`
  have hA0 : ∀ (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF],
      1 < valuation k W.j → W.a₄ ≠ 0 := by
    intro W _ _ hjv h0
    have hj0 : W.j = 0 := by
      rw [hjeq W, W.c₄_of_isShortNF, h0, mul_zero, zero_pow (by norm_num),
        mul_zero]
    rw [hj0, map_zero] at hjv
    exact absurd hjv (not_lt.mpr zero_le_one)
  have hA₁0 : A₁ ≠ 0 := hA0 (C₁ • W₁) hjv₁
  have hA₂0 : A₂ ≠ 0 := hA0 (C₂ • W₂) hjv₂
  -- `Bᵢ ≠ 0`: otherwise `j = 1728`, contradicting `1 < |j|`
  have hB0 : ∀ (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF],
      1 < valuation k W.j → W.a₄ ≠ 0 → W.a₆ ≠ 0 := by
    intro W _ _ hjv hA h0
    have hΔW : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := W.Δ_of_isShortNF
    have hj1728 : W.j = 1728 := by
      rw [hjeq W, W.c₄_of_isShortNF, hΔW, h0]
      field_simp
      ring
    rw [hj1728, show ((1728 : k)) = ((1728 : ℤ) : k) by norm_num] at hjv
    exact absurd (lt_of_lt_of_le hjv (valuation_intCast_le_one 1728))
      (lt_irrefl _)
  have hB₁0 : B₁ ≠ 0 := hB0 (C₁ • W₁) hjv₁ hA₁0
  have hB₂0 : B₂ ≠ 0 := hB0 (C₂ • W₂) hjv₂ hA₂0
  -- the cross-multiplied `j`-equation
  have hcross : (C₁ • W₁).c₄ ^ 3 * (C₂ • W₂).Δ =
      (C₂ • W₂).c₄ ^ 3 * (C₁ • W₁).Δ := by
    have h1 := hjeq (C₁ • W₁)
    have h2 := hjeq (C₂ • W₂)
    rw [h1, h2, inv_mul_eq_div, inv_mul_eq_div,
      div_eq_div_iff (hΔ (C₁ • W₁)) (hΔ (C₂ • W₂))] at hj'
    exact hj'
  -- extract the fundamental relation `A₁³B₂² = A₂³B₁²`
  have hkey : A₁ ^ 3 * B₂ ^ 2 = A₂ ^ 3 * B₁ ^ 2 := by
    rw [(C₁ • W₁).c₄_of_isShortNF, (C₂ • W₂).c₄_of_isShortNF,
      (C₁ • W₁).Δ_of_isShortNF, (C₂ • W₂).Δ_of_isShortNF,
      ← hA₁def, ← hB₁def, ← hA₂def, ← hB₂def] at hcross
    have h27 : ((27 : k) * ((-48 : k) ^ 3 * (-16 : k))) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h27
    linear_combination hcross
  -- the twisting scalar
  set w := (B₂ * A₁) / (B₁ * A₂) with hwdef
  have hw0 : w ≠ 0 :=
    div_ne_zero (mul_ne_zero hB₂0 hA₁0) (mul_ne_zero hB₁0 hA₂0)
  have hA₂w : A₂ = w ^ 2 * A₁ := by
    rw [hwdef, div_pow, div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero 2 (mul_ne_zero hB₁0 hA₂0))]
    linear_combination -hkey
  have hB₂w : B₂ = w ^ 3 * B₁ := by
    rw [hwdef, div_pow, div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero 3 (mul_ne_zero hB₁0 hA₂0))]
    linear_combination -B₁ * B₂ * hkey
  -- identify the short models with the explicit quintuples
  have hS₁eq : (C₁ • W₁) = (⟨0, 0, 0, A₁, B₁⟩ : WeierstrassCurve k) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · exact (C₁ • W₁).a₁_of_isShortNF
    · exact (C₁ • W₁).a₂_of_isShortNF
    · exact (C₁ • W₁).a₃_of_isShortNF
    · rfl
    · rfl
  have hS₂eq : (C₂ • W₂) =
      (⟨0, 0, 0, w ^ 2 * A₁, w ^ 3 * B₁⟩ : WeierstrassCurve k) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · exact (C₂ • W₂).a₁_of_isShortNF
    · exact (C₂ • W₂).a₂_of_isShortNF
    · exact (C₂ • W₂).a₃_of_isShortNF
    · exact hA₂w
    · exact hB₂w
  haveI hs₁ : ((C₁ • W₁).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] :=
    W₁.hasSplitMultiplicativeReduction_minimal_smul C₁
  haveI hs₂ : ((C₂ • W₂).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] :=
    W₂.hasSplitMultiplicativeReduction_minimal_smul C₂
  haveI i₁ : (((⟨0, 0, 0, A₁, B₁⟩ : WeierstrassCurve k)).minimal
      𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] := hS₁eq ▸ hs₁
  haveI i₂ : (((⟨0, 0, 0, w ^ 2 * A₁, w ^ 3 * B₁⟩ :
      WeierstrassCurve k)).minimal 𝒪[k]).HasSplitMultiplicativeReduction 𝒪[k] :=
    hS₂eq ▸ hs₂
  -- the arithmetic core: `w` is a square
  obtain ⟨v, hv⟩ := WeierstrassCurve.isSquare_of_scaled_split A₁ B₁ w hw0
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [hv, mul_zero])
  -- scaling by `v⁻¹` carries the first short model to the second
  set Cv : VariableChange k := ⟨(Units.mk0 v hv0)⁻¹, 0, 0, 0⟩ with hCvdef
  have hCv : Cv • (C₁ • W₁) = C₂ • W₂ := by
    rw [hS₁eq, hS₂eq]
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      simp only [WeierstrassCurve.variableChange_def, hCvdef, hv, inv_inv,
        Units.val_mk0] <;>
      field_simp <;>
      ring
  exact ⟨C₂⁻¹ * (Cv * C₁), by
    rw [mul_smul, mul_smul, hCv, inv_smul_smul]⟩

omit [E.IsMinimal 𝒪[k]] in
/-- Tate's theorem (Silverman, ATAEC V.5.3, derived from the two leaves
above and the PROVEN reduction type of the Tate curve): an elliptic
curve with split multiplicative reduction is isomorphic, by a change of
Weierstrass coordinates, to the Tate curve of its Tate parameter. -/
theorem WeierstrassCurve.exists_variableChange_tateCurve [CharZero k] :
    ∃ C : VariableChange k, C • tateCurve E.q = E := by
  obtain ⟨hell, hj⟩ := E.isElliptic_tateCurve_and_j
  haveI := hell
  haveI := hasSplitMultiplicativeReduction_tateCurve E.q E.valuation_q_lt_one
  exact WeierstrassCurve.exists_variableChange_of_j_eq_of_split
    (tateCurve E.q) E hj

/-! ### Functoriality

Now let `l` be a second nonarchimedean local field and let `k → l` be a morphism of fields
inducing the valuative relation on `k` from the one on `l` (the `ValuativeExtension`
hypothesis). The compatibility hypothesis is what makes the morphism continuous, hence
commute with the power series defining Tate's theory; it is automatic for `k`-embeddings
between algebraic extensions of `k` (by uniqueness of extensions of valuations over the
complete field `k`), but not for arbitrary abstract field morphisms.
-/

variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

-- The base change of E is elliptic. (Mathlib has this instance for `E.map f`, but
-- `WeierstrassCurve.baseChange` is a non-reducible `def`, so instance search cannot
-- see through it.)


-- The base change of `E` to `l` is still given by a minimal Weierstrass equation. This uses the
-- multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by itself is not
-- preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not over
-- `ℚ_p(p^{1/6})`. See `WeierstrassCurve.isMinimal_baseChange` in `ReductionBaseChange`.

-- and it still has split multiplicative reduction, via
-- `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange` in `ReductionBaseChange`
-- (from which the preceding `IsMinimal` also follows by class-parent projection).



