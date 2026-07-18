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
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.LocalField.Basic
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import Fermat.FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

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
/-- The formal `c₆`-series of the Tate curve: `c₆(q) = −(1 − 504·s₅)`,
the classical (negated) normalized Eisenstein series of weight `6`. -/
noncomputable def TateCurve.c₆Formal : ℤ⟦X⟧ := -(1 - 504 * TateCurve.sInt 5)

open PowerSeries in
open scoped ArithmeticFunction.sigma in
/-- **The `c₆`-invariant of the Tate curve is the value of `c₆Formal`**
(PROVEN — the second easy `q`-expansion identity):
`c₆ = −1 + 72·a₄(q) − 864·a₆(q)`, and at each coefficient the exact
division in `a₆Formal` cancels: `864·((5σ₃ + 7σ₅)/12) = 72·(5σ₃ + 7σ₅)`
by the integrality above, leaving `504·σ₅`. -/
theorem WeierstrassCurve.c₆_tateCurve_eq_evalInt (q : k)
    (hq : valuation k q < 1) :
    (tateCurve q).c₆ = TateCurve.evalInt q TateCurve.c₆Formal := by
  have hc₆eq : (tateCurve q).c₆ = -1 + 72 * tateA₄ q - 864 * tateA₆ q := by
    simp only [tateCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring
  -- the corresponding formal identity, coefficientwise
  have hform : TateCurve.c₆Formal =
      -1 + 72 * TateCurve.a₄Formal - 864 * TateCurve.a₆Formal := by
    ext n
    rw [TateCurve.c₆Formal]
    simp only [map_neg, map_sub, map_add, PowerSeries.coeff_one]
    have h72 : PowerSeries.coeff n ((72 : ℤ⟦X⟧) * TateCurve.a₄Formal) =
        72 * PowerSeries.coeff n TateCurve.a₄Formal := by
      have h0 : ((72 : ℤ⟦X⟧)) * TateCurve.a₄Formal =
          (72 : ℤ) • TateCurve.a₄Formal := by
        rw [zsmul_eq_mul]
        norm_num
      rw [h0, map_smul, smul_eq_mul]
    have h864 : PowerSeries.coeff n ((864 : ℤ⟦X⟧) * TateCurve.a₆Formal) =
        864 * PowerSeries.coeff n TateCurve.a₆Formal := by
      have h0 : ((864 : ℤ⟦X⟧)) * TateCurve.a₆Formal =
          (864 : ℤ) • TateCurve.a₆Formal := by
        rw [zsmul_eq_mul]
        norm_num
      rw [h0, map_smul, smul_eq_mul]
    have h504 : PowerSeries.coeff n ((504 : ℤ⟦X⟧) * TateCurve.sInt 5) =
        504 * PowerSeries.coeff n (TateCurve.sInt 5) := by
      have h0 : ((504 : ℤ⟦X⟧)) * TateCurve.sInt 5 =
          (504 : ℤ) • TateCurve.sInt 5 := by
        rw [zsmul_eq_mul]
        norm_num
      rw [h0, map_smul, smul_eq_mul]
    rw [h72, h864, h504, TateCurve.coeff_a₄Formal, TateCurve.coeff_a₆Formal]
    have hcoeffs5 : PowerSeries.coeff n (TateCurve.sInt 5) = (σ 5 n : ℤ) := by
      rw [TateCurve.sInt, PowerSeries.coeff_mk]
    rw [hcoeffs5]
    have hdvd := TateCurve.dvd_five_sigma_three_add_seven_sigma_five n
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]
    rw [Int.mul_ediv_cancel_left c (by norm_num : (12 : ℤ) ≠ 0)]
    rcases eq_or_ne n 0 with rfl | hn
    · have hσ30 : ((σ 3) (0 : ℕ) : ℤ) = 0 := by simp
      have hσ50 : ((σ 5) (0 : ℕ) : ℤ) = 0 := by simp
      have hc0 : c = 0 := by
        have h12c : 5 * ((σ 3) (0 : ℕ) : ℤ) +
            7 * ((σ 5) (0 : ℕ) : ℤ) = 12 * c := hc
        rw [hσ30, hσ50] at h12c
        omega
      rw [hσ30, hσ50, hc0]
      ring
    · have h12c : 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) = 12 * c := hc
      linarith [h12c]
  rw [hc₆eq, tateA₄_eq_evalInt q hq, tateA₆_eq_evalInt q hq, hform]
  -- evaluate the formal combination
  have hneg1 : TateCurve.evalInt q (-1 : ℤ⟦X⟧) = -1 := by
    rw [TateCurve.evalInt, tsum_eq_single 0 ?_]
    · simp
    · intro n hn
      simp [PowerSeries.coeff_one, hn]
  have hsc : ∀ (c : ℤ) (F : ℤ⟦X⟧), TateCurve.evalInt q ((c : ℤ⟦X⟧) * F) =
      (c : k) * TateCurve.evalInt q F := by
    intro c F
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
  rw [show (-1 + 72 * TateCurve.a₄Formal - 864 * TateCurve.a₆Formal :
      ℤ⟦X⟧) = (-1 : ℤ⟦X⟧) + (((72 : ℤ) : ℤ⟦X⟧) * TateCurve.a₄Formal +
      ((-864 : ℤ) : ℤ⟦X⟧) * TateCurve.a₆Formal) from by push_cast; ring]
  rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _),
    TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _),
    hneg1, hsc, hsc]
  push_cast
  ring

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
set_option warn.sorry false in
/-- **Evaluation commutes with formal substitution** (sorry node — the
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

set_option warn.sorry false in
/-- **Invariance of split multiplicative reduction under change of
Weierstrass coordinates** (sorry node): if `W` has split multiplicative
reduction, so does `C • W` for any change of variables `C` over `k`.
Content: the reduction type and the splitting field of the two tangent
directions at the node are intrinsic to the `k`-isomorphism class —
minimal integral models of `W` and `C • W` differ by a variable change
with unit scaling `u` and integral `r, s, t`, under which the reduced
node polynomial changes by a linear substitution and a unit square
scaling, preserving whether it splits over the residue field. -/
theorem WeierstrassCurve.HasSplitMultiplicativeReduction.smul
    (W : WeierstrassCurve k) [W.HasSplitMultiplicativeReduction 𝒪[k]]
    (C : VariableChange k) :
    (C • W).HasSplitMultiplicativeReduction 𝒪[k] :=
  sorry

set_option warn.sorry false in
/-- **Quadratic scaling twists between split curves are trivial**
(sorry node — the arithmetic core of the descent half of Tate's
theorem V.5.3): if the short Weierstrass curve `y² = x³ + Ax + B` and
its scaling twist `y² = x³ + w²Ax + w³B` both have split multiplicative
reduction over the nonarchimedean local field `k`, then `w` is a
square in `k`. Content: for `w` of odd valuation the twist is by a
ramified quadratic extension and has additive reduction; for `w` a
unit-nonsquare it is the unramified quadratic twist, which flips the
Galois action on the two tangent directions at the node, making the
reduction nonsplit (cf. the converse construction
`exists_quadraticTwist_hasSplitMultiplicativeReduction`). -/
theorem WeierstrassCurve.isSquare_of_scaled_split
    (A B w : k) (hw : w ≠ 0)
    [(⟨0, 0, 0, A, B⟩ : WeierstrassCurve k).HasSplitMultiplicativeReduction 𝒪[k]]
    [(⟨0, 0, 0, w ^ 2 * A, w ^ 3 * B⟩ :
        WeierstrassCurve k).HasSplitMultiplicativeReduction 𝒪[k]] :
    IsSquare w :=
  sorry

/-- **Split multiplicative curves with equal `j` are isomorphic**
(the descent half of Tate's theorem V.5.3, derived from the two leaves
above): two elliptic curves over `k` (of characteristic zero), both
with split multiplicative reduction, and with the same `j`-invariant,
differ by a change of Weierstrass coordinates over `k` itself.
Derivation: put both curves in short normal form `y² = x³ + Aᵢx + Bᵢ`
(char `k` = 0); split multiplicative reduction transfers to the short
models by the invariance leaf; `Aᵢ ≠ 0` since `c₄ = -48Aᵢ` is a unit,
`Bᵢ ≠ 0` since `Bᵢ = 0` forces `j = 1728`, contradicting `|j| > 1`;
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
  haveI hs₁ : (C₁ • W₁).HasSplitMultiplicativeReduction 𝒪[k] :=
    WeierstrassCurve.HasSplitMultiplicativeReduction.smul W₁ C₁
  haveI hs₂ : (C₂ • W₂).HasSplitMultiplicativeReduction 𝒪[k] :=
    WeierstrassCurve.HasSplitMultiplicativeReduction.smul W₂ C₂
  -- the `j`-invariants of the short models agree
  have hj' : (C₁ • W₁).j = (C₂ • W₂).j := by
    rw [WeierstrassCurve.variableChange_j, WeierstrassCurve.variableChange_j, hj]
  -- notation for the short coefficients
  set A₁ := (C₁ • W₁).a₄ with hA₁def
  set B₁ := (C₁ • W₁).a₆ with hB₁def
  set A₂ := (C₂ • W₂).a₄ with hA₂def
  set B₂ := (C₂ • W₂).a₆ with hB₂def
  -- `c₄` is a unit for split multiplicative reduction, so `Aᵢ ≠ 0`
  have hc₄ : ∀ (W : WeierstrassCurve k) [W.IsElliptic]
      [W.HasSplitMultiplicativeReduction 𝒪[k]], W.c₄ ≠ 0 := by
    intro W _ _ h0
    have h1 := W.valuation_c₄_eq_one
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hA₁0 : A₁ ≠ 0 := by
    intro h0
    exact hc₄ (C₁ • W₁) (by rw [(C₁ • W₁).c₄_of_isShortNF, ← hA₁def, h0, mul_zero])
  have hA₂0 : A₂ ≠ 0 := by
    intro h0
    exact hc₄ (C₂ • W₂) (by rw [(C₂ • W₂).c₄_of_isShortNF, ← hA₂def, h0, mul_zero])
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
  -- `Bᵢ ≠ 0`: otherwise `j = 1728`, contradicting `1 < |j|`
  have hB0 : ∀ (W : WeierstrassCurve k) [W.IsElliptic]
      [W.HasSplitMultiplicativeReduction 𝒪[k]] [W.IsShortNF],
      W.a₄ ≠ 0 → W.a₆ ≠ 0 := by
    intro W _ _ _ hA h0
    have hΔW : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := W.Δ_of_isShortNF
    have hj1728 : W.j = 1728 := by
      rw [hjeq W, W.c₄_of_isShortNF, hΔW, h0]
      field_simp
      ring
    have hlt := W.one_lt_valuation_j
    rw [hj1728, show ((1728 : k)) = ((1728 : ℤ) : k) by norm_num] at hlt
    exact absurd (lt_of_lt_of_le hlt (valuation_intCast_le_one 1728))
      (lt_irrefl _)
  have hB₁0 : B₁ ≠ 0 := hB0 (C₁ • W₁) hA₁0
  have hB₂0 : B₂ ≠ 0 := hB0 (C₂ • W₂) hA₂0
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
  haveI i₁ :
      (⟨0, 0, 0, A₁, B₁⟩ : WeierstrassCurve k).HasSplitMultiplicativeReduction
        𝒪[k] := hS₁eq ▸ hs₁
  haveI i₂ : (⟨0, 0, 0, w ^ 2 * A₁, w ^ 3 * B₁⟩ :
      WeierstrassCurve k).HasSplitMultiplicativeReduction 𝒪[k] := hS₂eq ▸ hs₂
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
instance : (E.baseChange l).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k l)).IsElliptic

/-- The construction of the Tate curve commutes on the nose with any valuative morphism:
its coefficients are power series in `q` with *integer* coefficients, and the partial
sums converge at matching rates on both sides (`TateCurve.evalInt_map`).

On the hypothesis `|q| < 1`: the coefficient series `tateA₄`, `tateA₆` are `tsum`s, which
take *junk values* outside the open unit disc, and every consumer feeds this lemma a Tate
parameter, which lies strictly inside the disc (`valuation_q_lt_one`). So the hypothesis
is free in practice, and keeps the statement the honest identity of convergent series
that it is in Silverman. -/
theorem WeierstrassCurve.tateCurve_baseChange (q : k) (hq : valuation k q < 1) :
    (tateCurve q)⁄l = tateCurve (algebraMap k l q) := by
  have hq' : valuation l (algebraMap k l q) < 1 := TateCurve.valuation_algebraMap_lt_one hq
  have h4 : algebraMap k l (tateA₄ q) = tateA₄ (algebraMap k l q) := by
    rw [tateA₄_eq_evalInt q hq, tateA₄_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  have h6 : algebraMap k l (tateA₆ q) = tateA₆ (algebraMap k l q) := by
    rw [tateA₆_eq_evalInt q hq, tateA₆_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  ext <;> simp [WeierstrassCurve.baseChange, tateCurve, h4, h6]

-- The base change of `E` to `l` is still given by a minimal Weierstrass equation. This uses the
-- multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by itself is not
-- preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not over
-- `ℚ_p(p^{1/6})`. See `WeierstrassCurve.isMinimal_baseChange` in `ReductionBaseChange`.
instance : (E.baseChange l).IsMinimal 𝒪[l] :=
  E.isMinimal_baseChange

-- and it still has split multiplicative reduction, via
-- `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange` in `ReductionBaseChange`
-- (from which the preceding `IsMinimal` also follows by class-parent projection).
instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l] :=
  E.hasSplitMultiplicativeReduction_baseChange

/-- The Tate parameter series commutes with valuative extensions: it is the evaluation of
an integral power series at `j⁻¹`, so this is a direct instance of `evalInt_map`. -/
theorem WeierstrassCurve.tateParameter_map {j : k} (hj : 1 < valuation k j) :
    tateParameter (algebraMap k l j) = algebraMap k l (tateParameter j) := by
  have hjinv : valuation k j⁻¹ < 1 := by
    simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj
  simp_rw [WeierstrassCurve.tateParameter_eq, TateCurve.evalInt_map j⁻¹ hjinv, map_inv₀]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_baseChange : (E.baseChange l).q = algebraMap k l E.q := by
  rw [show (E.baseChange l).q = tateParameter (E.baseChange l).j from rfl,
    show E.q = tateParameter E.j from rfl,
    show (E.baseChange l).j = algebraMap k l E.j from E.map_j (algebraMap k l),
    tateParameter_map E.one_lt_valuation_j]

/-! ### Tate's uniformisation over a separable closure

Passing to the limit over the finite subextensions of a separable closure `Ω` of `k`, the
finite-level uniformisations `E(l) ≅ lˣ/qᶻ` glue to a Galois-equivariant uniformisation
`E(Ω) ≅ Ωˣ/qᶻ`. The `N`-torsion of `Ωˣ/qᶻ` is generated by the `N`-th roots of unity and
(the classes of) the `N`-th roots of `q`, so the uniformisation identifies the `N`-torsion
of `E` explicitly: this is how one computes the Galois representations attached to `E`.

The statement below is an existential Prop (see the vendoring note in the module
docstring): the isomorphism is pinned down mathematically only up to a sign (the choice
of one of the two isomorphisms `E_{q(E)} ≅ E`), and no consumer needs a canonical
choice — only existence of an equivariant one.
-/

-- Now let `Ω` be a separable closure of `k`. It is not itself a nonarchimedean local field
-- (it is not complete), so it does not fit the framework above; but `E(Ω)` is the union of
-- the `E(l)` over the finite subextensions `l/k` of `Ω`, and Tate's theory applies to each.
variable (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]

-- the base change of E to Ω is elliptic (same remark as for `l` above)
instance : (E.baseChange Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k Ω)).IsElliptic

/-- The image of the Tate parameter in a separable closure `Ω` of `k`, as a unit. (`Ω` is
not a nonarchimedean local field, so this is not literally `(E.baseChange Ω).qUnit`.) -/
noncomputable def WeierstrassCurve.qUnitSepClosure : Ωˣ :=
  Units.map (algebraMap k Ω).toMonoidHom E.qUnit

-- `DecidableEq Ω` is needed for the group law on `(E⁄Ω).Point`
variable [DecidableEq Ω]

set_option warn.sorry false in
/-- **Tate's uniformisation of the TATE CURVE over a separable closure**
(sorry node — the choice-free core of the uniformisation): for a unit
`q` of `k` with `|q| < 1`, the points of the Tate curve `E_q` over a
separable closure `Ω` are `Ωˣ/q^ℤ`, Galois-equivariantly ON THE NOSE —
the isomorphism is given by the explicit series `X(u, q)`, `Y(u, q)`
(whose Weierstrass equation is `TateCurve.weierstrass_equation`,
PROVEN), so it involves no choices and commutes with every `k`-algebra
endomorphism of `Ω`. `E(Ω)` is the directed union of the `E(l)` over
finite subextensions `l/k` (each a nonarchimedean local field, where
the series converge); the uniformisations glue by the same
choice-freeness. -/
theorem WeierstrassCurve.exists_tateCurveEquivSepClosure (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    ∃ e : Additive (Ωˣ ⧸ Subgroup.zpowers
        (Units.map (algebraMap k Ω).toMonoidHom q)) ≃+
      (((tateCurve ((q : k) : k))⁄Ω)).Point,
      ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
        WeierstrassCurve.Affine.Point.map (W' := tateCurve ((q : k) : k))
            σ.toAlgHom (e (Additive.ofMul ↑u)) =
          e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) :=
  sorry

omit [E.IsMinimal 𝒪[k]] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Tate's uniformisation theorem over a separable closure** (derived
2026-07-17 from the choice-free Tate-curve uniformisation above and
Tate's theorem `exists_variableChange_tateCurve`): for `E/k`
an elliptic curve, in minimal Weierstrass form, with split multiplicative reduction
over a nonarchimedean local field `k`, and `Ω` a separable closure of `k`, there is a
group isomorphism `Ωˣ/q(E)ᶻ ≅ E(Ω)` that is equivariant for the natural actions of
`Gal(Ω/k)` on both sides (Silverman, ATAEC V.3.1 + V.5.3: glue the finite-level
uniformisations `E(l) ≅ lˣ/qᶻ` over the finite subextensions `l/k` of `Ω`; the
`k`-linearity of every `σ ∈ Gal(Ω/k)` makes the sign choice `σ`-stable, cf.
`tateEquiv_galois` in the upstream FLT file). Stated as an existential Prop because
the isomorphism is canonical only up to negation. -/
theorem WeierstrassCurve.exists_tateEquivSepClosure [CharZero k] :
    ∃ e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point,
      ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
        WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
          e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) := by
  classical
  obtain ⟨C, hC⟩ := E.exists_variableChange_tateCurve
  obtain ⟨e₀, he₀⟩ := WeierstrassCurve.exists_tateCurveEquivSepClosure (k := k) Ω
    E.qUnit E.valuation_q_lt_one
  -- the `Ω`-stage curve equality behind the variable change
  have hEq : (E⁄Ω) = (C.baseChange Ω) •
      ((tateCurve ((E.qUnit : k) : k))⁄Ω) := by
    conv_lhs => rw [← hC]
    exact (baseChange_smul_baseChange _ _ _).symm
  haveI hTell : (((tateCurve ((E.qUnit : k) : k))⁄Ω)).IsElliptic := by
    haveI h1 : ((C.baseChange Ω) •
        ((tateCurve ((E.qUnit : k) : k))⁄Ω)).IsElliptic := by
      rw [← hEq]
      infer_instance
    have h2 : ((C.baseChange Ω)⁻¹ • ((C.baseChange Ω) •
        ((tateCurve ((E.qUnit : k) : k))⁄Ω))).IsElliptic := inferInstance
    rw [inv_smul_smul] at h2
    exact h2
  let Ψ : ((E⁄Ω)).Point ≃+ (((tateCurve ((E.qUnit : k) : k))⁄Ω)).Point :=
    (Affine.Point.equivOfEq hEq).trans
      (Affine.Point.equivVariableChange
        ((tateCurve ((E.qUnit : k) : k))⁄Ω) (C.baseChange Ω))
  have hΨapp : ∀ R : ((E⁄Ω)).Point, Ψ R =
      (Affine.Point.equivVariableChange
        ((tateCurve ((E.qUnit : k) : k))⁄Ω) (C.baseChange Ω))
      ((Affine.Point.equivOfEq hEq) R) := fun R => rfl
  refine ⟨e₀.trans Ψ.symm, ?_⟩
  intro σ u
  -- σ fixes the base-changed variable-change data (it is `k`-rational)
  have hσu : σ.toAlgHom (((C.baseChange Ω).u : Ω)) = ((C.baseChange Ω).u : Ω) := by
    simp only [VariableChange.baseChange, VariableChange.map, Units.coe_map,
      MonoidHom.coe_coe]
    exact σ.toAlgHom.commutes _
  have hσr : σ.toAlgHom (C.baseChange Ω).r = (C.baseChange Ω).r := by
    simp only [VariableChange.baseChange, VariableChange.map]
    exact σ.toAlgHom.commutes _
  have hσs : σ.toAlgHom (C.baseChange Ω).s = (C.baseChange Ω).s := by
    simp only [VariableChange.baseChange, VariableChange.map]
    exact σ.toAlgHom.commutes _
  have hσt : σ.toAlgHom (C.baseChange Ω).t = (C.baseChange Ω).t := by
    simp only [VariableChange.baseChange, VariableChange.map]
    exact σ.toAlgHom.commutes _
  -- equivariance of `Ψ` under `σ`
  have h12 : ∀ Q : ((E⁄Ω)).Point,
      Ψ (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom Q) =
      WeierstrassCurve.Affine.Point.map (W' := tateCurve ((E.qUnit : k) : k))
        σ.toAlgHom (Ψ Q) := by
    intro Q
    rw [hΨapp, hΨapp]
    cases Q with
    | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
    | some x y hxy =>
      rw [WeierstrassCurve.Affine.Point.map_some,
        WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.equivOfEq_some,
        WeierstrassCurve.Affine.Point.equivVariableChange_some,
        WeierstrassCurve.Affine.Point.equivVariableChange_some,
        WeierstrassCurve.Affine.Point.map_some]
      refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
      · simp only [map_add, map_mul, map_pow, hσu, hσr]
      · simp only [map_add, map_mul, map_pow, hσu, hσs, hσt]
  have h12' : ∀ R : (((tateCurve ((E.qUnit : k) : k))⁄Ω)).Point,
      Ψ.symm (WeierstrassCurve.Affine.Point.map
        (W' := tateCurve ((E.qUnit : k) : k)) σ.toAlgHom R) =
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (Ψ.symm R) := by
    intro R
    apply Ψ.injective
    rw [Ψ.apply_symm_apply, h12, Ψ.apply_symm_apply]
  show WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom
      (Ψ.symm (e₀ (Additive.ofMul ↑u))) =
      Ψ.symm (e₀ (Additive.ofMul
        ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
  rw [← h12', he₀]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- `N`-th roots of unity give `N`-torsion points of `E` under ANY Tate
uniformization (PROVEN — a formal consequence of the group-isomorphism
property, stated for the witnesses of `exists_tateEquivSepClosure`):
`N • [ζ] = [ζ^N] = [1] = 0`, and `e` transports annihilation. -/
theorem WeierstrassCurve.mem_torsionBy_of_mem_rootsOfUnity
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    {N : ℕ} {ζ : Ωˣ} (hζ : ζ ∈ rootsOfUnity N Ω) :
    e (Additive.ofMul ↑ζ) ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point (N : ℤ) := by
  have hζN : ζ ^ N = 1 := hζ
  have hann : ((N : ℤ)) • (Additive.ofMul
      (↑ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) = 0 := by
    rw [← ofMul_zpow, ← QuotientGroup.mk_zpow, zpow_natCast, hζN,
      QuotientGroup.mk_one, ofMul_one]
  refine (Submodule.mem_torsionBy_iff _ _).mpr ?_
  rw [← map_zsmul e, hann, map_zero]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- `N`-th roots of the Tate parameter give `N`-torsion points of `E`
under ANY Tate uniformization (PROVEN, as above): `N • [r] = [r^N] = [q]
= 0` since `q` generates the subgroup that is quotiented out. -/
theorem WeierstrassCurve.mem_torsionBy_of_pow_eq
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    {N : ℕ} {r : Ωˣ} (hr : r ^ N = E.qUnitSepClosure Ω) :
    e (Additive.ofMul ↑r) ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point (N : ℤ) := by
  have hann : ((N : ℤ)) • (Additive.ofMul
      (↑r : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) = 0 := by
    rw [← ofMul_zpow, ← QuotientGroup.mk_zpow, zpow_natCast, hr]
    rw [show ((E.qUnitSepClosure Ω : Ωˣ) :
        Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _), ofMul_one]
  refine (Submodule.mem_torsionBy_iff _ _).mpr ?_
  rw [← map_zsmul e, hann, map_zero]

/-- **Representatives of torsion in the Tate quotient** (PROVEN — pure
group theory): every `N`-torsion class of `Gˣ/q^ℤ` is represented by an
element whose `N`-th power is an integer power of `q`. This is step (a)
of the derivation of the multiplicative-reduction inertia statements
from `exists_tateEquivSepClosure`. -/
theorem exists_rep_pow_eq_zpow_of_torsion {G : Type*} [CommGroup G]
    (q : G) {N : ℕ} (t : Additive (G ⧸ Subgroup.zpowers q))
    (ht : ((N : ℤ)) • t = 0) :
    ∃ (u : G) (a : ℤ),
      Additive.ofMul ((u : G ⧸ Subgroup.zpowers q)) = t ∧ u ^ N = q ^ a := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul t)
  have h1 : ((u : G ⧸ Subgroup.zpowers q)) ^ N = 1 := by
    have h2 := congrArg Additive.toMul ht
    rw [toMul_zsmul, toMul_zero, zpow_natCast] at h2
    rw [hu]
    exact h2
  have h3 : (u ^ N : G) ∈ Subgroup.zpowers q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h3
  exact ⟨u, a, by rw [hu, ofMul_toMul], ha.symm⟩

/-- **The inertia-difference of a Tate-parameter root is a root of
unity** (PROVEN): if `σ` fixes `u^N`, then `σ(u)·u⁻¹` is an `N`-th root
of unity. Step (c) of the multiplicative-reduction derivation: for a
torsion representative `u` with `u^N = q_E^a`, every `σ ∈ Gal(Ω/k)`
fixes `u^N` (the Tate parameter comes from the base field), so `σ`
moves `u` by at most an `N`-th root of unity. -/
theorem map_mul_inv_mem_rootsOfUnity_of_pow_fixed
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ) {N : ℕ}
    (hfix : Units.map σ.toAlgHom.toRingHom.toMonoidHom (u ^ N) = u ^ N) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom u * u⁻¹ ∈
      rootsOfUnity N Ω := by
  rw [mem_rootsOfUnity]
  calc (Units.map σ.toAlgHom.toRingHom.toMonoidHom u * u⁻¹) ^ N
      = Units.map σ.toAlgHom.toRingHom.toMonoidHom (u ^ N) * (u ^ N)⁻¹ := by
        rw [mul_pow, map_pow, inv_pow]
    _ = 1 := by rw [hfix, mul_inv_cancel]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]
  [DecidableEq Ω] in
/-- Every `k`-automorphism of `Ω` fixes the Tate parameter (PROVEN): it
comes from the base field. -/
theorem WeierstrassCurve.map_qUnitSepClosure_eq (σ : Ω ≃ₐ[k] Ω) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.qUnitSepClosure Ω) =
      E.qUnitSepClosure Ω := by
  apply Units.ext
  show σ ((algebraMap k Ω) E.q) = (algebraMap k Ω) E.q
  exact σ.commutes E.q

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]
  [DecidableEq Ω] in
/-- Every `k`-automorphism of `Ω` fixes all integer powers of the Tate
parameter (PROVEN). -/
theorem WeierstrassCurve.map_zpow_qUnitSepClosure_eq (σ : Ω ≃ₐ[k] Ω)
    (a : ℤ) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.qUnitSepClosure Ω ^ a) =
      E.qUnitSepClosure Ω ^ a := by
  rw [map_zpow, E.map_qUnitSepClosure_eq]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]
  [DecidableEq Ω] in
/-- **Integer powers of the Tate parameter are distinct** (PROVEN): the
Tate parameter has valuation strictly less than `1` in the base field,
so `a ↦ q^a` is injective — the class group `Ωˣ/q^ℤ` is a genuine
`ℤ`-quotient. -/
theorem WeierstrassCurve.qUnitSepClosure_zpow_injective :
    Function.Injective (fun a : ℤ => E.qUnitSepClosure Ω ^ a) := by
  intro a b hab
  -- descend to `k` along the injective algebra map
  have h1 : E.qUnit ^ a = E.qUnit ^ b := by
    have h2 : Units.map (algebraMap k Ω).toMonoidHom (E.qUnit ^ a) =
        Units.map (algebraMap k Ω).toMonoidHom (E.qUnit ^ b) := by
      rw [map_zpow, map_zpow]
      exact hab
    apply Units.ext
    have h3 := congrArg Units.val h2
    exact (algebraMap k Ω).injective h3
  -- valuation freeness in `k`
  have h4 := congrArg (fun w : kˣ => valuation k ((w : k))) h1
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    map_zpow₀, map_zpow₀] at h4
  exact zpow_right_injective₀
    (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr E.q_ne_zero))
    (ne_of_lt E.valuation_q_lt_one) h4

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] [Algebra.IsSeparable k Ω] in
/-- **The Tate valuation-exponent quotient on `p`-torsion** (PROVEN
over any uniformization witness): the `p`-torsion of a Tate-uniformized
curve surjects `Galois-invariantly` onto `ℤ/p` by the exponent of the
Tate parameter in the `p`-th power of any representative — the
quotient of the filtration `0 → μ_p → E[p] → ℤ/p → 0`. Since every
`k`-automorphism fixes the Tate parameter, the quotient carries the
TRIVIAL `Gal(Ω/k)`-action; this is the split-case content of the
tame-quotient condition at `2`. Surjectivity requires a `p`-th root of
the Tate parameter, which exists in the separably closed `Ω` when
`p ≠ 0` there. -/
theorem WeierstrassCurve.exists_tateTorsionQuotient
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
        e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
    {p : ℕ} (hp : p ≠ 0) (hpΩ : ((p : ℕ) : Ω) ≠ 0) :
    ∃ π : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ) →+ ZMod p,
      Function.Surjective π ∧
      ∀ (σ : Ω ≃ₐ[k] Ω)
        (P Q : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ)),
        (Q : ((E⁄Ω)).Point) =
          WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom
            (P : ((E⁄Ω)).Point) →
        π Q = π P := by
  classical
  -- torsion transfers to the quotient side
  have htors : ∀ P : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ),
      ((p : ℕ) : ℤ) • (e.symm (P : ((E⁄Ω)).Point)) = 0 := fun P => by
    rw [← map_zsmul e.symm,
      (show ((p : ℕ) : ℤ) • (P : ((E⁄Ω)).Point) = 0 from P.2), map_zero]
  -- choose a representative and exponent for each torsion point
  choose u a hu ha using fun P : AddSubgroup.torsionBy ((E⁄Ω)).Point
      ((p : ℕ) : ℤ) =>
    exists_rep_pow_eq_zpow_of_torsion (E.qUnitSepClosure Ω)
      (e.symm (P : ((E⁄Ω)).Point)) (htors P)
  -- the exponent is independent of the representative, mod `p`
  have hindep : ∀ (P : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ))
      (v : Ωˣ) (b : ℤ),
      Additive.ofMul ((v : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        e.symm (P : ((E⁄Ω)).Point) →
      v ^ p = E.qUnitSepClosure Ω ^ b →
      ((b : ZMod p)) = ((a P : ZMod p)) := by
    intro P v b hv hvb
    have h1 : ((u P : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        ((v : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) :=
      Additive.ofMul.injective ((hu P).trans hv.symm)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp h1)
    -- `v = u P * q^m`
    have h2 : v = u P * E.qUnitSepClosure Ω ^ m := by
      rw [hm]
      group
    have h3 : E.qUnitSepClosure Ω ^ b =
        E.qUnitSepClosure Ω ^ (a P + m * (p : ℤ)) := by
      rw [← hvb, h2, mul_pow, ha P, ← zpow_natCast
        (E.qUnitSepClosure Ω ^ m) p, ← zpow_mul, ← zpow_add]
    have h4 : b = a P + m * (p : ℤ) :=
      E.qUnitSepClosure_zpow_injective Ω h3
    rw [h4]
    push_cast
    simp
  -- the exponent function and its additivity
  have hadd : ∀ P Q : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ),
      ((a (P + Q) : ZMod p)) = ((a P : ZMod p)) + ((a Q : ZMod p)) := by
    intro P Q
    have hclass : Additive.ofMul (((u P * u Q : Ωˣ) :
        Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        e.symm ((P + Q : AddSubgroup.torsionBy ((E⁄Ω)).Point
          ((p : ℕ) : ℤ)) : ((E⁄Ω)).Point) := by
      rw [show ((P + Q : AddSubgroup.torsionBy ((E⁄Ω)).Point
          ((p : ℕ) : ℤ)) : ((E⁄Ω)).Point) =
          (P : ((E⁄Ω)).Point) + (Q : ((E⁄Ω)).Point) from rfl,
        map_add e.symm, ← hu P, ← hu Q, QuotientGroup.mk_mul, ofMul_mul]
    have hpow : (u P * u Q) ^ p =
        E.qUnitSepClosure Ω ^ (a P + a Q) := by
      rw [mul_pow, ha P, ha Q, ← zpow_add]
    have := hindep (P + Q) (u P * u Q) (a P + a Q) hclass hpow
    rw [← this]
    push_cast
    ring
  let π : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ) →+ ZMod p :=
    AddMonoidHom.mk' (fun P => ((a P : ZMod p))) hadd
  refine ⟨π, ?_, ?_⟩
  · -- surjectivity: a `p`-th root of the Tate parameter has exponent `1`
    have hq0 : (algebraMap k Ω) E.q ≠ 0 := by
      simp only [map_ne_zero]
      exact E.q_ne_zero
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root
      (Polynomial.X ^ p - Polynomial.C ((algebraMap k Ω) E.q))
      (by
        rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
        exact_mod_cast Nat.pos_of_ne_zero hp |>.ne')
      (Polynomial.separable_X_pow_sub_C _ hpΩ hq0)
    have hxpow : x ^ p = (algebraMap k Ω) E.q := by
      have h1 := hx
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h1
      exact h1
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp] at hxpow
      exact hq0 hxpow.symm
    set xu : Ωˣ := Units.mk0 x hx0 with hxu
    have hxupow : xu ^ p = E.qUnitSepClosure Ω ^ (1 : ℤ) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_one]
      exact hxpow
    -- the corresponding torsion point
    have htor : ((p : ℕ) : ℤ) • (e (Additive.ofMul ((xu :
        Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))))) = 0 := by
      rw [← map_zsmul e, ← ofMul_zpow, ← QuotientGroup.mk_zpow,
        zpow_natCast, hxupow]
      rw [show ((E.qUnitSepClosure Ω ^ (1 : ℤ) :
          Ωˣ) : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = 1 from
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem _
          (Subgroup.mem_zpowers _) _), ofMul_one, map_zero]
    set P₁ : AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ) :=
      ⟨e (Additive.ofMul ((xu : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω)))), htor⟩ with hP₁
    have hπ1 : π P₁ = 1 := by
      have hclass : Additive.ofMul ((xu : Ωˣ ⧸ Subgroup.zpowers
          (E.qUnitSepClosure Ω))) = e.symm ((P₁ :
          ((E⁄Ω)).Point)) := by
        rw [hP₁]
        exact (e.symm_apply_apply _).symm
      have := hindep P₁ xu 1 hclass hxupow
      rw [show π P₁ = ((a P₁ : ZMod p)) from rfl, ← this]
      norm_num
    -- `1` generates `ZMod p`
    haveI : NeZero p := ⟨hp⟩
    intro c
    refine ⟨c.val • P₁, ?_⟩
    rw [map_nsmul, hπ1, nsmul_eq_mul, mul_one, ZMod.natCast_val,
      ZMod.cast_id]
  · -- Galois invariance: `σ`-images have the same exponent
    intro σ P Q hQ
    have hclass : Additive.ofMul
        ((Units.map σ.toAlgHom.toRingHom.toMonoidHom (u P) :
          Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        e.symm ((Q : ((E⁄Ω)).Point)) := by
      apply e.injective
      rw [e.apply_symm_apply, ← he, hQ]
      congr 1
      rw [hu P, e.apply_symm_apply]
    have hpow : (Units.map σ.toAlgHom.toRingHom.toMonoidHom (u P)) ^ p =
        E.qUnitSepClosure Ω ^ (a P) := by
      rw [← map_pow, ha P, map_zpow_qUnitSepClosure_eq]
    exact (hindep Q _ _ hclass hpow).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- **Local unipotence of inertia on Tate torsion** (PROVEN 2026-07-17,
assembling steps (a), (b), (c) over ANY witness of the uniformization):
given a Galois-equivariant Tate uniformization `e` of `E` over `Ω` and
a valuation subring `A` of `Ω` whose residue characteristic does not
divide `p`, every element of the inertia subgroup of `A` acts
unipotently on the `p`-torsion: `σ(σP) − σP − σP + P = 0`. The torsion
class is represented by `u` with `u^p = q_E^a` (step (a)); every
`k`-automorphism fixes `q_E^a`, so `σ(u)/u =: ζ` is a `p`-th root of
unity (step (c)) and `σP − P = e[ζ]`; inertia fixes `ζ` (step (b)), so
a second application of `σ − 1` kills `e[ζ]`. -/
theorem WeierstrassCurve.tate_inertia_unipotent
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
        e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
    (A : ValuationSubring Ω) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (P : ((E⁄Ω)).Point)
    (hP : P ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P) -
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P -
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P + P = 0 := by
  classical
  -- pull the torsion class back through `e`
  set t : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) :=
    e.symm P with ht
  have hPt : e t = P := e.apply_symm_apply P
  have httor : ((p : ℕ) : ℤ) • t = 0 := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    rw [ht, ← map_zsmul e.symm, h1, map_zero]
  obtain ⟨u, a, hut, hupow⟩ :=
    exists_rep_pow_eq_zpow_of_torsion (E.qUnitSepClosure Ω) t httor
  -- `σ` moves `u` by the root of unity `ζ`
  have hfixpow : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom
      (u ^ p) = u ^ p := by
    rw [hupow]
    exact E.map_zpow_qUnitSepClosure_eq Ω (σ : Ω ≃ₐ[k] Ω) a
  have hζmem : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u
      * u⁻¹ ∈ rootsOfUnity p Ω :=
    map_mul_inv_mem_rootsOfUnity_of_pow_fixed (σ : Ω ≃ₐ[k] Ω) u hfixpow
  set ζ : Ωˣ := Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u
    * u⁻¹ with hζ
  -- inertia fixes `ζ`
  have hζpow : (ζ : Ω) ^ p = 1 := by
    have h1 : ζ ^ p = 1 := hζmem
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hσζ : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom ζ =
      ζ := by
    apply Units.ext
    show (σ : Ω ≃ₐ[k] Ω) (ζ : Ω) = (ζ : Ω)
    exact A.inertia_fixes_of_pow_eq_one hp hchar σ hσ hζpow
  -- `σP = P + e[ζ]`
  have hσu : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u =
      ζ * u := by
    rw [hζ, inv_mul_cancel_right]
  have hstep : ∀ Q : ((E⁄Ω)).Point,
      Q = e (Additive.ofMul (↑u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) →
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom Q =
      e (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := by
    intro Q hQ
    rw [hQ, he (σ : Ω ≃ₐ[k] Ω) u, hσu]
  have hPu : P = e (Additive.ofMul (↑u : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) := by
    rw [hut, hPt]
  have hσP : WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P =
      e (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := hstep P hPu
  -- `σ(σP) = σP + e[σζ] − ... = e[ζ·ζ·u]`? — apply equivariance again
  have hσσP : WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom
      (WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P) =
      e (Additive.ofMul (↑(ζ * (ζ * u)) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := by
    rw [hσP, he (σ : Ω ≃ₐ[k] Ω) (ζ * u)]
    congr 2
    rw [map_mul, hσζ, hσu]
  -- assemble in the additive quotient
  have h₂ : (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) =
      Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
      Additive.ofMul ((u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) := by
    rw [QuotientGroup.mk_mul, ofMul_mul]
  have h₁ : (Additive.ofMul (↑(ζ * (ζ * u)) : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) =
      Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
      (Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
       Additive.ofMul ((u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)))) := by
    rw [QuotientGroup.mk_mul, ofMul_mul, h₂]
  rw [hσσP, hσP, hPu, h₁, h₂, map_add, map_add]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- **Local triviality of inertia on Tate torsion when the parameter is
a `p`-th power up to units** (steps (a)+(b′)+(d) over any witness of
the uniformization): if `q_E · w⁻ᵖ` is a unit of the valuation subring
`A` (with nonzero residue) for some `w ∈ kˣ`, then every inertia
element FIXES the `p`-torsion pointwise. The torsion class is
represented by `u` with `uᵖ = q_Eᵃ`; then `x := u·w⁻ᵃ` satisfies
`xᵖ = (q_E·w⁻ᵖ)ᵃ`, a `σ`-fixed unit constant of `A`, so inertia fixes
`x` (`inertia_fixes_of_pow_eq`), hence `u`, hence the point. -/
theorem WeierstrassCurve.tate_inertia_trivial
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
        e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
    (A : ValuationSubring Ω) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (w : kˣ)
    (hcA : algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)) ∈ A)
    (hcres : IsLocalRing.residue A
      (⟨algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)), hcA⟩ : A) ≠ 0)
    (P : ((E⁄Ω)).Point)
    (hP : P ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P = P := by
  classical
  set t : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) :=
    e.symm P with ht
  have hPt : e t = P := e.apply_symm_apply P
  have httor : ((p : ℕ) : ℤ) • t = 0 := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    rw [ht, ← map_zsmul e.symm, h1, map_zero]
  obtain ⟨u, a, hut, hupow⟩ :=
    exists_rep_pow_eq_zpow_of_torsion (E.qUnitSepClosure Ω) t httor
  -- the recentred representative `x := u · wΩ⁻ᵃ` and its constant power
  set wΩ : Ωˣ := Units.map (algebraMap k Ω).toMonoidHom w with hwΩ
  have h1 : (u * wΩ⁻¹ ^ a) ^ (p : ℤ) =
      (Units.map (algebraMap k Ω).toMonoidHom (E.qUnit * w⁻¹ ^ p)) ^ a := by
    calc (u * wΩ⁻¹ ^ a) ^ (p : ℤ)
        = u ^ (p : ℤ) * (wΩ⁻¹ ^ a) ^ (p : ℤ) := mul_zpow _ _ _
      _ = u ^ p * (wΩ⁻¹ ^ a) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ a) ^ (p : ℤ) := by rw [hupow]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ (p : ℤ)) ^ a := by
          rw [← zpow_mul, ← zpow_mul, mul_comm a ((p : ℤ))]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ p) ^ a := by rw [zpow_natCast]
      _ = (E.qUnitSepClosure Ω * wΩ⁻¹ ^ p) ^ a := (mul_zpow _ _ _).symm
      _ = (Units.map (algebraMap k Ω).toMonoidHom (E.qUnit * w⁻¹ ^ p)) ^ a := by
          congr 1
          rw [map_mul, map_pow, map_inv, ← hwΩ]
          rfl
  have hxpow : ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) ^ p =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    calc ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) ^ p
        = (((u * wΩ⁻¹ ^ a) ^ p : Ωˣ) : Ω) :=
          (Units.val_pow_eq_pow_val _ _).symm
      _ = (((u * wΩ⁻¹ ^ a) ^ (p : ℤ) : Ωˣ) : Ω) := by rw [zpow_natCast]
      _ = (((Units.map (algebraMap k Ω).toMonoidHom
            (E.qUnit * w⁻¹ ^ p)) ^ a : Ωˣ) : Ω) := by rw [h1]
      _ = ((Units.map (algebraMap k Ω).toMonoidHom
            (E.qUnit * w⁻¹ ^ p) : Ωˣ) : Ω) ^ a :=
          Units.val_zpow_eq_zpow_val _ _
      _ = (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := rfl
  -- the constant power is `σ`-fixed (it comes from the base field)
  have hσc : (σ : Ω ≃ₐ[k] Ω)
      ((algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a) =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    rw [map_zpow₀]
    congr 1
    exact (σ : Ω ≃ₐ[k] Ω).commutes _
  -- the constant is a unit of `A`, so its integer powers stay in `A`
  have hcunit : IsUnit (⟨algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)),
      hcA⟩ : A) := by
    by_contra hnu
    exact hcres (Ideal.Quotient.eq_zero_iff_mem.mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hcoe : (((hcunit.unit ^ a : Aˣ) : A) : Ω) =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    calc (((hcunit.unit ^ a : Aˣ) : A) : Ω)
        = ((Units.map A.subtype.toMonoidHom (hcunit.unit ^ a) : Ωˣ) : Ω) := rfl
      _ = (((Units.map A.subtype.toMonoidHom hcunit.unit) ^ a : Ωˣ) : Ω) := by
          rw [map_zpow]
      _ = ((Units.map A.subtype.toMonoidHom hcunit.unit : Ωˣ) : Ω) ^ a :=
          Units.val_zpow_eq_zpow_val _ _
      _ = (((hcunit.unit : A) : Ω)) ^ a := rfl
      _ = (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
          rw [hcunit.unit_spec]
  have hcApow : (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a ∈ A :=
    hcoe ▸ SetLike.coe_mem _
  have hcrespow : IsLocalRing.residue A
      (⟨(algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a, hcApow⟩ : A) ≠
      0 := by
    rw [show (⟨(algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a,
        hcApow⟩ : A) = ((hcunit.unit ^ a : Aˣ) : A) from Subtype.ext hcoe.symm]
    exact ((hcunit.unit ^ a).isUnit.map (IsLocalRing.residue A)).ne_zero
  -- inertia fixes the recentred representative (step (b′))
  have hfix : (σ : Ω ≃ₐ[k] Ω) ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) =
      ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) :=
    A.inertia_fixes_of_pow_eq hp hchar σ hσ hcApow hcrespow hσc hxpow
  -- `σ` fixes `wΩ` (it comes from the base field), hence fixes `u`
  have hσw : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom wΩ =
      wΩ := by
    apply Units.ext
    show (σ : Ω ≃ₐ[k] Ω) ((wΩ : Ωˣ) : Ω) = ((wΩ : Ωˣ) : Ω)
    exact (σ : Ω ≃ₐ[k] Ω).commutes w
  have h5 : (u * wΩ⁻¹ ^ a) * wΩ ^ a = u := by
    rw [inv_zpow, inv_mul_cancel_right]
  have hσu : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u =
      u := by
    rw [← h5, map_mul, map_zpow, hσw]
    congr 1
    apply Units.ext
    exact hfix
  -- conclude: the point itself is fixed
  rw [← hPt, ← hut, he (σ : Ω ≃ₐ[k] Ω) u, hσu]
