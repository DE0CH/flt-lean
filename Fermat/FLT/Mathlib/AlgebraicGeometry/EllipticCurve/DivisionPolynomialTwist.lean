/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

open Polynomial

/-!
# Division polynomials under a change of Weierstrass coordinates

Mathlib's `WeierstrassCurve.preΨ'` has a `map` law (`map_preΨ'`) and a base-change law
(`baseChange_preΨ'`), and **nothing** for `WeierstrassCurve.variableChange` — checked against
the pin on 2026-07-28 and again on 2026-07-30.  This file supplies that missing law in the
form the arithmetic of `Fermat/FLT/ModularCurve/X0.lean` needs it, and derives from it the
transfer of a monic rational factor of `Ψ_q` between two curves with the same `j`-invariant.

## The shape of the law, and why it is stated with `w = u²` rather than with `u`

A change of coordinates `(u, r, s, t)` acts on `x` by `x = u²x' + r`, and `ψ_n` picks up
`u^-(n²-1)`.  So for the univariate `preΨ' n` — which is `ψ_n` for odd `n` and `ψ_n/ψ₂` for
even `n` — the law is

> `(preΨ' n of the new curve) (X) = u^-w · (preΨ' n of the old curve) (u²X + r)`,
> `w = n² - 1` for odd `n` and `w = n² - 4` for even `n`.

Both weights are **even**, so the law only ever involves `u²` — and that matters, because the
application is over `ℚ`, where two curves with the same `j` are quadratic twists and the `u`
relating them is a square root of a rational number, hence typically irrational.  Every
statement below is therefore phrased in terms of `w = u²` and `r` alone; `u` never appears.
`edsWeight n` is `w/2`, the exponent of `u² = w`.

## Main statements

* `edsWeight`, `preNormEDS'_scale` : the purely algebraic core.  Scaling the three seeds of a
  normalised elliptic divisibility sequence by `α^6, α^4, α^6` scales its `n`-th term by
  `α^(edsWeight n)`.  No elliptic curves, no substitution — just the EDS recursion.
* `WeierstrassCurve.preΨ'_comp_linear` : the law above, with the three seed identities
  (`Ψ₂Sq`, `Ψ₃`, `preΨ₄` at weights `3, 4, 6`) as hypotheses.
* `WeierstrassCurve.preΨ'_comp_variableChange_of_u_eq_one` : the seed identities hold for any
  change of coordinates with `u = 1`, in particular for `toShortNF`.
* `WeierstrassCurve.preΨ'_comp_of_isShortNF` : and for the scaling twist `(A, B) ↦ (w²A, w³B)`
  between two short normal forms.
* `WeierstrassCurve.exists_monic_dvd_preΨ'_of_j_eq` : the arithmetic consequence — over a field
  of characteristic zero, a monic factor of `preΨ' q` of degree `n` transports to any curve
  with the same `j`-invariant, provided `j ∉ {0, 1728}`.

## `j ≠ 0` and `j ≠ 1728` are load-bearing

At `j = 0` the curves with that `j` are the *sextic* twists `y² = x³ + d`, and the
substitution relating `y² = x³ + 1` to `y² = x³ + 2` is `x ↦ 2^(1/3)x`, which is not defined
over the base field; their `Ψ_q` genuinely have different rational factorisation types.  Same
at `j = 1728` with quartic twists.  Formally, the two hypotheses are exactly what makes
`a₄ ≠ 0` and `a₆ ≠ 0` in the short normal form, which is what the scaling twist needs.
-/

namespace EllipticDivisionPolynomialTwist

/-- Half the weight with which `preΨ' n` scales under a change of coordinates: `edsWeight n` is
`(n² - 1)/2` for odd `n` and `(n² - 4)/2` for even `n`.  Its first values are
`0, 0, 0, 4, 6, 12, 16, 24, 30`.

Written with `n / 2` so that the two truncated subtractions that appear (at `n = 0` and
`n = 2`, where the honest value of `n² - 4` is negative) are harmless: both give `0`, which is
the right answer, since `preΨ' 0 = 0` and `preΨ' 2 = 1` scale trivially. -/
def edsWeight (n : ℕ) : ℕ :=
  if Even n then 2 * (n / 2 - 1) * (n / 2 + 1) else 2 * (n / 2) * (n / 2 + 1)

@[simp] lemma edsWeight_zero : edsWeight 0 = 0 := by decide
@[simp] lemma edsWeight_one : edsWeight 1 = 0 := by decide
@[simp] lemma edsWeight_two : edsWeight 2 = 0 := by decide
@[simp] lemma edsWeight_three : edsWeight 3 = 4 := by decide
@[simp] lemma edsWeight_four : edsWeight 4 = 6 := by decide

/-- `2 * edsWeight n` is `n² - 4` for even `n` and `n² - 1` for odd `n`, stated without
subtraction.  This is the only fact about `edsWeight` that the recursion identities below
need, and it holds for every `n ≠ 0`. -/
lemma two_mul_edsWeight (n : ℕ) (hn : n ≠ 0) :
    2 * edsWeight n + (if Even n then 4 else 1) = n * n := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [if_pos (even_two_mul _), edsWeight, if_pos (even_two_mul _),
      Nat.mul_div_cancel_left _ (two_pos), Nat.add_sub_cancel]
    ring
  · subst hk
    have hodd : ¬ Even (2 * k + 1) := by simp [parity_simps]
    rw [if_neg hodd, edsWeight, if_neg hodd, Nat.mul_add_div two_pos]
    norm_num
    ring

lemma edsWeight_rec_even₁ (m : ℕ) :
    2 * edsWeight (m + 2) + edsWeight (m + 3) + edsWeight (m + 5) = edsWeight (2 * (m + 3)) := by
  have h1 := two_mul_edsWeight (m + 2) (by omega)
  have h2 := two_mul_edsWeight (m + 3) (by omega)
  have h3 := two_mul_edsWeight (m + 5) (by omega)
  have h4 := two_mul_edsWeight (2 * (m + 3)) (by omega)
  rw [if_pos (even_two_mul _)] at h4
  rcases Nat.even_or_odd m with hm | hm
  · rw [if_pos (hm.add (by decide : Even 2))] at h1
    rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 3)))] at h2
    rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 5)))] at h3
    linarith
  · rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_even (by decide : Even 2)))] at h1
    rw [if_pos (hm.add_odd (by decide : Odd 3))] at h2
    rw [if_pos (hm.add_odd (by decide : Odd 5))] at h3
    linarith

lemma edsWeight_rec_even₂ (m : ℕ) :
    edsWeight (m + 1) + edsWeight (m + 3) + 2 * edsWeight (m + 4) = edsWeight (2 * (m + 3)) := by
  have h1 := two_mul_edsWeight (m + 1) (by omega)
  have h2 := two_mul_edsWeight (m + 3) (by omega)
  have h3 := two_mul_edsWeight (m + 4) (by omega)
  have h4 := two_mul_edsWeight (2 * (m + 3)) (by omega)
  rw [if_pos (even_two_mul _)] at h4
  rcases Nat.even_or_odd m with hm | hm
  · rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 1)))] at h1
    rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 3)))] at h2
    rw [if_pos (hm.add (by decide : Even 4))] at h3
    linarith
  · rw [if_pos (hm.add_odd (by decide : Odd 1))] at h1
    rw [if_pos (hm.add_odd (by decide : Odd 3))] at h2
    rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_even (by decide : Even 4)))] at h3
    linarith

lemma edsWeight_rec_odd₁ (m : ℕ) (hm : Even m) :
    edsWeight (m + 4) + 3 * edsWeight (m + 2) + 6 = edsWeight (2 * (m + 2) + 1) := by
  have h1 := two_mul_edsWeight (m + 4) (by omega)
  have h2 := two_mul_edsWeight (m + 2) (by omega)
  have h3 := two_mul_edsWeight (2 * (m + 2) + 1) (by omega)
  rw [if_neg (by simp [parity_simps])] at h3
  rw [if_pos (hm.add (by decide : Even 4))] at h1
  rw [if_pos (hm.add (by decide : Even 2))] at h2
  linarith

lemma edsWeight_rec_odd₂ (m : ℕ) (hm : Even m) :
    edsWeight (m + 1) + 3 * edsWeight (m + 3) = edsWeight (2 * (m + 2) + 1) := by
  have h1 := two_mul_edsWeight (m + 1) (by omega)
  have h2 := two_mul_edsWeight (m + 3) (by omega)
  have h3 := two_mul_edsWeight (2 * (m + 2) + 1) (by omega)
  rw [if_neg (by simp [parity_simps])] at h3
  rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 1)))] at h1
  rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_odd (by decide : Odd 3)))] at h2
  linarith

lemma edsWeight_rec_odd₁' (m : ℕ) (hm : Odd m) :
    edsWeight (m + 4) + 3 * edsWeight (m + 2) = edsWeight (2 * (m + 2) + 1) := by
  have h1 := two_mul_edsWeight (m + 4) (by omega)
  have h2 := two_mul_edsWeight (m + 2) (by omega)
  have h3 := two_mul_edsWeight (2 * (m + 2) + 1) (by omega)
  rw [if_neg (by simp [parity_simps])] at h3
  rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_even (by decide : Even 4)))] at h1
  rw [if_neg (Nat.not_even_iff_odd.mpr (hm.add_even (by decide : Even 2)))] at h2
  linarith

lemma edsWeight_rec_odd₂' (m : ℕ) (hm : Odd m) :
    edsWeight (m + 1) + 3 * edsWeight (m + 3) + 6 = edsWeight (2 * (m + 2) + 1) := by
  have h1 := two_mul_edsWeight (m + 1) (by omega)
  have h2 := two_mul_edsWeight (m + 3) (by omega)
  have h3 := two_mul_edsWeight (2 * (m + 2) + 1) (by omega)
  rw [if_neg (by simp [parity_simps])] at h3
  rw [if_pos (hm.add_odd (by decide : Odd 1))] at h1
  rw [if_pos (hm.add_odd (by decide : Odd 3))] at h2
  linarith

/-- **Scaling the seeds of a normalised elliptic divisibility sequence.**  If the three seeds
`b, c, d` are scaled by `α^6, α^4, α^6`, then the `n`-th term is scaled by `α^(edsWeight n)`.

This is the whole content of the transformation law of the division polynomials under a change
of Weierstrass coordinates: the substitution part is a ring homomorphism and so passes through
`preNormEDS'` for free (`map_preNormEDS'`), and what is left is exactly this scaling.

Note that `α` is an arbitrary ring element — no invertibility is needed, because every weight
that occurs is a genuine natural number. -/
theorem preNormEDS'_scale {R : Type*} [CommRing R] (b c d α : R) (n : ℕ) :
    preNormEDS' (α ^ 6 * b) (α ^ 4 * c) (α ^ 6 * d) n
      = α ^ edsWeight n * preNormEDS' b c d n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | even m ih =>
    rw [preNormEDS'_even, preNormEDS'_even, ih (m + 1) (by omega), ih (m + 2) (by omega),
      ih (m + 3) (by omega), ih (m + 4) (by omega), ih (m + 5) (by omega),
      ← edsWeight_rec_even₁ m, mul_sub]
    congr 1
    · ring
    · rw [edsWeight_rec_even₁ m, ← edsWeight_rec_even₂ m]
      ring
  | odd m ih =>
    rw [preNormEDS'_odd, preNormEDS'_odd, ih (m + 1) (by omega), ih (m + 2) (by omega),
      ih (m + 3) (by omega), ih (m + 4) (by omega)]
    rcases Nat.even_or_odd m with hm | hm
    · rw [if_pos hm, if_pos hm, if_pos hm, if_pos hm, ← edsWeight_rec_odd₁ m hm, mul_sub]
      congr 1
      · ring
      · rw [edsWeight_rec_odd₁ m hm, ← edsWeight_rec_odd₂ m hm]
        ring
    · have hm' : ¬ Even m := Nat.not_even_iff_odd.mpr hm
      rw [if_neg hm', if_neg hm', if_neg hm', if_neg hm', ← edsWeight_rec_odd₁' m hm, mul_sub]
      congr 1
      · ring
      · rw [edsWeight_rec_odd₁' m hm, ← edsWeight_rec_odd₂' m hm]
        ring

end EllipticDivisionPolynomialTwist

namespace WeierstrassCurve

open EllipticDivisionPolynomialTwist

variable {R : Type*} [CommRing R]

/-- **The transformation law of `preΨ'` under the substitution `x ↦ wx + r`**, from the same
law on the three seeds `Ψ₂Sq`, `Ψ₃`, `preΨ₄` at weights `3, 4, 6`.

The three hypotheses are what an actual change of coordinates supplies; see
`preΨ'_comp_variableChange_of_u_eq_one` and `preΨ'_comp_of_isShortNF` for the two instances
this file uses.  Splitting the statement this way is what keeps `u` out of it: the seeds are
polynomials in the `b`-invariants, which transform through `u²` alone. -/
theorem preΨ'_comp_linear (W W' : WeierstrassCurve R) (w r : R)
    (h₂ : W.Ψ₂Sq.comp (C w * X + C r) = C w ^ 3 * W'.Ψ₂Sq)
    (h₃ : W.Ψ₃.comp (C w * X + C r) = C w ^ 4 * W'.Ψ₃)
    (h₄ : W.preΨ₄.comp (C w * X + C r) = C w ^ 6 * W'.preΨ₄) (n : ℕ) :
    (W.preΨ' n).comp (C w * X + C r) = C w ^ edsWeight n * W'.preΨ' n := by
  have hcomp : ∀ p : R[X],
      p.comp (C w * X + C r) = eval₂RingHom (C : R →+* R[X]) (C w * X + C r) p := fun _ ↦ rfl
  have g₂ : eval₂RingHom (C : R →+* R[X]) (C w * X + C r) (W.Ψ₂Sq ^ 2)
      = (C w) ^ 6 * W'.Ψ₂Sq ^ 2 := by
    rw [map_pow, ← hcomp, h₂]; ring
  have g₃ : eval₂RingHom (C : R →+* R[X]) (C w * X + C r) W.Ψ₃ = (C w) ^ 4 * W'.Ψ₃ := by
    rw [← hcomp, h₃]
  have g₄ : eval₂RingHom (C : R →+* R[X]) (C w * X + C r) W.preΨ₄ = (C w) ^ 6 * W'.preΨ₄ := by
    rw [← hcomp, h₄]
  rw [preΨ', hcomp, map_preNormEDS', g₂, g₃, g₄, preNormEDS'_scale, preΨ']

/-- The three seed identities for a change of coordinates with `u = 1`: there the substitution
is the translation `x ↦ x + r` and there is no scaling at all. -/
theorem preΨ'_comp_variableChange_of_u_eq_one (W : WeierstrassCurve R) (V : VariableChange R)
    (hu : V.u = 1) (n : ℕ) :
    (W.preΨ' n).comp (C (1 : R) * X + C V.r) = (V • W).preΨ' n := by
  have hu' : ((V.u⁻¹ : Rˣ) : R) = 1 := by rw [hu]; simp
  -- Unfolding to the `aᵢ` rather than stopping at the `bᵢ` is not cosmetic: the identity for
  -- `preΨ₄` is NOT a formal consequence of the four `bᵢ` transformation laws, because it uses
  -- `4b₈ = b₂b₆ - b₄²` (mathlib's `b_relation`), which `ring` cannot see.  At the level of the
  -- `aᵢ` every seed identity is a genuine polynomial identity.
  have h₂ : W.Ψ₂Sq.comp (C (1 : R) * X + C V.r) = C (1 : R) ^ 3 * (V • W).Ψ₂Sq := by
    simp only [Ψ₂Sq, b₂, b₄, b₆, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, hu', add_comp, mul_comp, pow_comp,
      X_comp, C_comp, ofNat_comp, Nat.cast_ofNat, map_ofNat, C_1, C_add, C_mul,
      C_sub, C_pow, one_pow, one_mul]
    ring
  have h₃ : W.Ψ₃.comp (C (1 : R) * X + C V.r) = C (1 : R) ^ 4 * (V • W).Ψ₃ := by
    simp only [Ψ₃, b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, hu', add_comp, sub_comp, mul_comp, pow_comp,
      X_comp, C_comp, ofNat_comp, Nat.cast_ofNat, map_ofNat, C_1, C_add, C_mul,
      C_sub, C_pow, one_pow, one_mul]
    ring
  have h₄ : W.preΨ₄.comp (C (1 : R) * X + C V.r) = C (1 : R) ^ 6 * (V • W).preΨ₄ := by
    simp only [preΨ₄, b₂, b₄, b₆, b₈, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, hu', add_comp, sub_comp, mul_comp, pow_comp,
      X_comp, C_comp, ofNat_comp, Nat.cast_ofNat, map_ofNat, C_1, C_add, C_mul,
      C_sub, C_pow, one_pow, one_mul]
    ring
  simpa using preΨ'_comp_linear W (V • W) 1 V.r h₂ h₃ h₄ n

/-- The three seed identities for the **scaling twist** between two short normal forms: if
`W : y² = x³ + Ax + B` and `W' : y² = x³ + A'x + B'` with `A = w²A'` and `B = w³B'`, then
substituting `x ↦ wx` into the seeds of `W` gives the seeds of `W'` up to the weights.

Over a field this is precisely the quadratic twist by `w`, and `w` need not be a square: the
substitution `x ↦ wx` on `x`-coordinates is defined over the base field even though the
corresponding change of Weierstrass coordinates `(u, 0, 0, 0)`, `u² = w`, is not. -/
theorem preΨ'_comp_of_isShortNF (W W' : WeierstrassCurve R) [W.IsShortNF] [W'.IsShortNF]
    (w : R) (ha₄ : W.a₄ = w ^ 2 * W'.a₄) (ha₆ : W.a₆ = w ^ 3 * W'.a₆) (n : ℕ) :
    (W.preΨ' n).comp (C w * X + C 0) = C w ^ edsWeight n * W'.preΨ' n := by
  have h₂ : W.Ψ₂Sq.comp (C w * X + C 0) = C w ^ 3 * W'.Ψ₂Sq := by
    simp only [Ψ₂Sq, b₂, b₄, b₆, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF, ha₄, ha₆,
      add_comp, mul_comp, pow_comp, X_comp, C_comp, zero_comp,
      ofNat_comp, Nat.cast_ofNat, map_ofNat, C_0, C_add, C_mul,
      C_pow, mul_zero, add_zero]
    ring
  have h₃ : W.Ψ₃.comp (C w * X + C 0) = C w ^ 4 * W'.Ψ₃ := by
    simp only [Ψ₃, b₂, b₄, b₆, b₈, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF, ha₄, ha₆,
      add_comp, sub_comp, mul_comp, pow_comp, X_comp, C_comp, zero_comp,
      ofNat_comp, Nat.cast_ofNat, map_ofNat, C_0, C_add, C_mul, C_sub,
      C_pow, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  have h₄ : W.preΨ₄.comp (C w * X + C 0) = C w ^ 6 * W'.preΨ₄ := by
    simp only [preΨ₄, b₂, b₄, b₆, b₈, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF, ha₄, ha₆,
      add_comp, sub_comp, mul_comp, pow_comp, X_comp, C_comp, zero_comp,
      ofNat_comp, Nat.cast_ofNat, map_ofNat, C_0, C_add, C_mul, C_sub,
      C_pow, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  exact preΨ'_comp_linear W W' w 0 h₂ h₃ h₄ n

/-- `toShortNF` is a change of coordinates with `u = 1`: it is a translation of `x` and a shear
of `y`, and rescales nothing.  (Both factors of its definition have `u = 1`, and `u` is
multiplicative.) -/
@[simp] lemma u_toShortNF (W : WeierstrassCurve R) [Invertible (2 : R)] [Invertible (3 : R)] :
    (W.toShortNF).u = 1 := by
  simp [toShortNF, VariableChange.mul_def, toCharNeTwoNF]

end WeierstrassCurve

namespace Polynomial

/-- **Transporting a monic divisor along `x ↦ ax + b`.**  Composition with a linear polynomial
is a ring endomorphism of `F[X]` preserving degrees, so it carries a monic degree-`n` divisor of
`P` to a degree-`n` divisor of `P.comp (aX + b)`, which is monic after dividing by `aⁿ`. -/
theorem exists_monic_dvd_comp {F : Type*} [Field F] {n : ℕ} (P g : F[X]) {a b : F}
    (ha : a ≠ 0) (hg : g.Monic) (hdeg : g.natDegree = n) (hdvd : g ∣ P) :
    ∃ h : F[X], h.Monic ∧ h.natDegree = n ∧ h ∣ P.comp (C a * X + C b) := by
  have hlin : (C a * X + C b).natDegree = 1 := natDegree_linear ha
  have hlc : (C a * X + C b).leadingCoeff = a := leadingCoeff_linear ha
  have hqdeg : (g.comp (C a * X + C b)).natDegree = n := by
    rw [natDegree_comp, hlin, hdeg, mul_one]
  have hqlc : (g.comp (C a * X + C b)).leadingCoeff = a ^ n := by
    rw [leadingCoeff_comp (by rw [hlin]; exact one_ne_zero), hg.leadingCoeff, hlc, hdeg, one_mul]
  have hq0 : g.comp (C a * X + C b) ≠ 0 := fun h ↦ by
    rw [h, leadingCoeff_zero] at hqlc
    exact pow_ne_zero n ha hqlc.symm
  refine ⟨g.comp (C a * X + C b) * C (g.comp (C a * X + C b)).leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hq0, ?_, ?_⟩
  · rw [natDegree_mul_leadingCoeff_inv _ hq0, hqdeg]
  · obtain ⟨k, hk⟩ := hdvd
    refine ⟨k.comp (C a * X + C b) * C (g.comp (C a * X + C b)).leadingCoeff, ?_⟩
    rw [hk, mul_comp, hqlc]
    have hcc : (C ((a ^ n)⁻¹ : F)) * (C (a ^ n) : F[X]) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero n ha), C_1]
    linear_combination (-(g.comp (C a * X + C b) * k.comp (C a * X + C b))) * hcc

end Polynomial

namespace WeierstrassCurve

open EllipticDivisionPolynomialTwist

variable {F : Type*} [Field F]

/-- **The scaling relation between two short models with the same `j`-invariant.**  From
`A³B'² = A'³B²` with all four of `A, B, A', B'` nonzero, the scalar `w = BA'/(B'A)` satisfies
`A = w²A'` and `B = w³B'`.

The same computation appears inside
`WeierstrassCurve.exists_variableChange_of_j_eq_of_split`
(`Fermat/FLT/KnownIn1980s/EllipticCurves/TateCurve.lean`); it is isolated here because it is
pure algebra, and because that consumer goes on to prove `w` is a square, which is exactly what
is **not** available in the present generality. -/
theorem exists_scaling_of_cross {A B A' B' : F} (hA : A ≠ 0) (hB' : B' ≠ 0)
    (hkey : A ^ 3 * B' ^ 2 = A' ^ 3 * B ^ 2) :
    ∃ w : F, A = w ^ 2 * A' ∧ B = w ^ 3 * B' := by
  refine ⟨B * A' / (B' * A), ?_, ?_⟩
  · rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 (mul_ne_zero hB' hA))]
    linear_combination hkey
  · rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 (mul_ne_zero hB' hA))]
    linear_combination B * B' * hkey

/-- **A monic factor of `preΨ' q` transports along an equality of `j`-invariants.**

Over a field of characteristic zero, put both curves in short normal form (a change of
coordinates with `u = 1`, so `preΨ'` only gets translated); equal `j` outside `{0, 1728}` makes
the two short models `y² = x³ + Ax + B` and `y² = x³ + A'x + B'` scaling twists of one another,
`A = w²A'`, `B = w³B'`; and `x ↦ wx` is defined over the base field even when `w` is not a
square, which is what makes the conclusion rational rather than merely geometric.

This is the formal content of the remark that TWIST-INVARIANCE is not an extra hypothesis: no
hypothesis relating `E` and `E'` beyond `E.j = E'.j` is available or needed. -/
theorem exists_monic_dvd_preΨ'_of_j_eq [CharZero F] {q n : ℕ} (E E' : WeierstrassCurve F)
    [E.IsElliptic] [E'.IsElliptic] (hjj : E.j = E'.j) (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728)
    (f : Polynomial F) (hf : f.Monic) (hdeg : f.natDegree = n) (hdvd : f ∣ E.preΨ' q) :
    ∃ g : Polynomial F, g.Monic ∧ g.natDegree = n ∧ g ∣ E'.preΨ' q := by
  haveI h2 : Invertible (2 : F) := invertibleOfNonzero (by norm_num : (2 : F) ≠ 0)
  haveI h3 : Invertible (3 : F) := invertibleOfNonzero (by norm_num : (3 : F) ≠ 0)
  -- the two short models
  haveI hS : (E.toShortNF • E).IsShortNF := E.toShortNF_spec
  haveI hS' : (E'.toShortNF • E').IsShortNF := E'.toShortNF_spec
  set S := E.toShortNF • E with hSdef
  set S' := E'.toShortNF • E' with hS'def
  -- `j` is a variable-change invariant, so the short models inherit the three `j`-hypotheses
  have hjS : S.j = E.j := variableChange_j ..
  have hjS' : S'.j = E'.j := variableChange_j ..
  -- the discriminant of a short model is `-16(4A³ + 27B²)`, and it is nonzero
  have hΔ : ∀ (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF],
      4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
    intro W _ _ h0
    have := W.isUnit_Δ.ne_zero
    rw [W.Δ_of_isShortNF, h0, mul_zero] at this
    exact this rfl
  -- `A ≠ 0` from `j ≠ 0`, and `B ≠ 0` from `j ≠ 1728`
  have hcube : ∀ x : F, x = 0 → x ^ 3 = 0 := fun x hx ↦ by subst hx; simp
  have hA : ∀ (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF], W.j ≠ 0 → W.a₄ ≠ 0 := by
    intro W _ _ hj h0
    exact hj (by rw [W.j_of_isShortNF, hcube _ h0, mul_zero, zero_div])
  have hB : ∀ (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF],
      W.j ≠ 0 → W.j ≠ 1728 → W.a₆ ≠ 0 := by
    intro W _ _ hj hj' h0
    refine hj' ?_
    have h4 : (4 : F) * W.a₄ ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 (hA W hj))
    rw [W.j_of_isShortNF, h0]
    rw [show (0 : F) ^ 2 = 0 by simp, mul_zero, add_zero, div_eq_iff h4]
    ring
  have hA₁ : S.a₄ ≠ 0 := hA S (by rw [hjS]; exact hj0)
  have hB₂ : S'.a₆ ≠ 0 := hB S' (by rw [hjS', ← hjj]; exact hj0) (by rw [hjS', ← hjj]; exact hj1728)
  -- the cross-multiplied `j`-equation
  have hkey : S.a₄ ^ 3 * S'.a₆ ^ 2 = S'.a₄ ^ 3 * S.a₆ ^ 2 := by
    have hj' : S.j = S'.j := by rw [hjS, hjS', hjj]
    rw [S.j_of_isShortNF, S'.j_of_isShortNF, div_eq_div_iff (hΔ S) (hΔ S')] at hj'
    apply mul_left_cancel₀ (show (27 : F) * 6912 ≠ 0 by norm_num)
    linear_combination hj'
  obtain ⟨w, hw₄, hw₆⟩ := exists_scaling_of_cross hA₁ hB₂ hkey
  have hw : w ≠ 0 := by
    rintro rfl
    rw [show (0 : F) ^ 2 = 0 by simp, zero_mul] at hw₄
    exact hA₁ hw₄
  -- step 1: transport `f` from `E` to its short model `S`
  obtain ⟨g₁, hg₁m, hg₁d, hg₁⟩ :=
    Polynomial.exists_monic_dvd_comp (E.preΨ' q) f (one_ne_zero (α := F)) hf hdeg hdvd
  rw [preΨ'_comp_variableChange_of_u_eq_one E E.toShortNF (u_toShortNF E) q] at hg₁
  -- step 2: transport across the scaling twist `S → S'`
  obtain ⟨g₂, hg₂m, hg₂d, hg₂⟩ :=
    Polynomial.exists_monic_dvd_comp (S.preΨ' q) g₁ hw hg₁m hg₁d hg₁
  rw [preΨ'_comp_of_isShortNF S S' w hw₄ hw₆ q] at hg₂
  have hg₂' : g₂ ∣ S'.preΨ' q := by
    refine hg₂.trans ⟨C ((w ^ edsWeight q)⁻¹), ?_⟩
    have hc : (C w : F[X]) ^ edsWeight q * C ((w ^ edsWeight q)⁻¹) = 1 := by
      rw [← C_pow, ← C_mul, mul_inv_cancel₀ (pow_ne_zero _ hw), C_1]
    linear_combination (-(S'.preΨ' q)) * hc
  -- step 3: transport back from `S'` to `E'`
  have huinv : (E'.toShortNF⁻¹ : VariableChange F).u = 1 := by
    rw [show (E'.toShortNF⁻¹ : VariableChange F).u = (E'.toShortNF).u⁻¹ from rfl,
      u_toShortNF, inv_one]
  have hback : (E'.toShortNF⁻¹ : VariableChange F) • S' = E' := by
    rw [hS'def, inv_smul_smul]
  obtain ⟨g₃, hg₃m, hg₃d, hg₃⟩ :=
    Polynomial.exists_monic_dvd_comp (S'.preΨ' q) g₂ (one_ne_zero (α := F)) hg₂m hg₂d hg₂'
  rw [preΨ'_comp_variableChange_of_u_eq_one S' E'.toShortNF⁻¹ huinv q, hback] at hg₃
  exact ⟨g₃, hg₃m, hg₃d, hg₃⟩

end WeierstrassCurve

end
