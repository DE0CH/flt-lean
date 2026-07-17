/-
InvariantDerivation.lean — own work for the Fermat project.

The Hamiltonian derivation `D := F_Y ⬝ ∂_X − F_X ⬝ ∂_Y` on the bivariate
polynomial ring of the universal Weierstrass curve. It kills the curve
polynomial `F` identically (`D F = F_Y F_X − F_X F_Y = 0`), hence
descends to the universal coordinate ring `Buniv` and extends to the
universal function field `Kuniv` by the quotient rule. On `y`-free
functions it is `ψ₂ ⬝ d/dx`, i.e. differentiation along the invariant
differential `ω = dx/ψ₂` — the engine for the Wronskian identity
`Φₙ′ΨSqₙ − ΦₙΨSqₙ′ = n ⬝ preΨ₂ₙ` behind `separable_preΨ'`.
-/
module

public import Fermat.FLT.EllipticCurve.TautologicalPoint

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

/-- `∂/∂X` on `ℤ[A₁,…,A₅][X][Y]`: the coefficientwise derivative with
respect to the inner variable. -/
noncomputable def dX :
    Derivation (MvPolynomial (Fin 5) ℤ)
      ((MvPolynomial (Fin 5) ℤ)[X][Y]) ((MvPolynomial (Fin 5) ℤ)[X][Y]) :=
  PolynomialModule.equivPolynomialSelf.toLinearMap.compDer
    (Polynomial.derivative'.mapCoeffs)

set_option backward.isDefEq.respectTransparency false in
lemma dX_apply (P : (MvPolynomial (Fin 5) ℤ)[X][Y]) :
    dX P = PolynomialModule.equivPolynomialSelf
      (Polynomial.derivative'.mapCoeffs P) := rfl

/-- `∂/∂Y` on `ℤ[A₁,…,A₅][X][Y]`: the derivative in the outer
variable. -/
noncomputable def dY :
    Derivation (MvPolynomial (Fin 5) ℤ)
      ((MvPolynomial (Fin 5) ℤ)[X][Y]) ((MvPolynomial (Fin 5) ℤ)[X][Y]) :=
  Polynomial.derivative'.restrictScalars (MvPolynomial (Fin 5) ℤ)

set_option backward.isDefEq.respectTransparency false in
lemma dX_coeff (P : (MvPolynomial (Fin 5) ℤ)[X][Y]) (i : ℕ) :
    (dX P).coeff i = Polynomial.derivative (P.coeff i) := by
  rw [dX_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma dY_apply (P : (MvPolynomial (Fin 5) ℤ)[X][Y]) :
    dY P = Polynomial.derivative P := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma dX_C (p : (MvPolynomial (Fin 5) ℤ)[X]) :
    dX (Polynomial.C p) = Polynomial.C (Polynomial.derivative p) := by
  rw [← Polynomial.monomial_zero_left, dX_apply,
    Derivation.mapCoeffs_monomial]
  ext i
  simp [PolynomialModule.equivPolynomialSelf,
    PolynomialModule.coeff_single, Polynomial.coeff_C]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma dX_Y :
    dX (Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, dX_apply,
    Derivation.mapCoeffs_monomial]
  ext i
  simp [PolynomialModule.equivPolynomialSelf]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma dY_C (p : (MvPolynomial (Fin 5) ℤ)[X]) :
    dY (Polynomial.C p) = 0 := by
  simp [dY, Derivation.restrictScalars_apply, Polynomial.derivative']

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma dY_Y :
    dY (Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) = 1 := by
  simp [dY, Derivation.restrictScalars_apply, Polynomial.derivative']

/-- **The Hamiltonian derivation** `D := F_Y ⬝ ∂_X − F_X ⬝ ∂_Y` of the
universal Weierstrass curve. -/
noncomputable def Dham :
    Derivation (MvPolynomial (Fin 5) ℤ)
      ((MvPolynomial (Fin 5) ℤ)[X][Y]) ((MvPolynomial (Fin 5) ℤ)[X][Y]) :=
  Wuniv.toAffine.polynomialY • dX + (-Wuniv.toAffine.polynomialX) • dY

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma Dham_C (p : (MvPolynomial (Fin 5) ℤ)[X]) :
    Dham (Polynomial.C p) =
      Wuniv.toAffine.polynomialY * Polynomial.C (Polynomial.derivative p) := by
  simp [Dham, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma Dham_Y :
    Dham (Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) =
      -Wuniv.toAffine.polynomialX := by
  simp [Dham, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The Hamiltonian derivation kills the curve polynomial. -/
lemma Dham_polynomial : Dham Wuniv.toAffine.polynomial = 0 := by
  have happ : Dham Wuniv.toAffine.polynomial =
      Wuniv.toAffine.polynomialY * dX Wuniv.toAffine.polynomial +
        (-Wuniv.toAffine.polynomialX) * dY Wuniv.toAffine.polynomial := by
    simp [Dham, smul_eq_mul]
  set p₁ : (MvPolynomial (Fin 5) ℤ)[X] :=
    Polynomial.C Wuniv.a₁ * Polynomial.X + Polynomial.C Wuniv.a₃ with hp₁
  set p₀ : (MvPolynomial (Fin 5) ℤ)[X] :=
    Polynomial.X ^ 3 + Polynomial.C Wuniv.a₂ * Polynomial.X ^ 2 +
      Polynomial.C Wuniv.a₄ * Polynomial.X + Polynomial.C Wuniv.a₆ with hp₀
  have hFdec : Wuniv.toAffine.polynomial =
      Polynomial.X ^ 2 + Polynomial.C p₁ * Polynomial.X +
        Polynomial.C (-p₀) := by
    rw [Affine.polynomial, hp₁, hp₀]
    C_simp
    ring
  have e2 : dX (Polynomial.X ^ 2 + Polynomial.C p₁ * Polynomial.X +
        Polynomial.C (-p₀)) =
      dX (Polynomial.X ^ 2 + Polynomial.C p₁ * Polynomial.X) +
        dX (Polynomial.C (-p₀)) :=
    Derivation.map_add dX _ _
  have e2' : dX (Polynomial.X ^ 2 + Polynomial.C p₁ * Polynomial.X) =
      dX (Polynomial.X ^ 2) + dX (Polynomial.C p₁ * Polynomial.X) :=
    Derivation.map_add dX _ _
  have e3 : dX ((Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) ^ 2) =
      (2 : ℕ) • ((Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) ^ 1) •
        dX Polynomial.X :=
    Derivation.leibniz_pow dX Polynomial.X 2
  have e4 : dX (Polynomial.C p₁ * Polynomial.X) =
      Polynomial.C p₁ • dX Polynomial.X +
        Polynomial.X • dX (Polynomial.C p₁) :=
    Derivation.leibniz dX (Polynomial.C p₁) Polynomial.X
  have hdX : dX Wuniv.toAffine.polynomial =
      Polynomial.C (Polynomial.derivative p₁) * Polynomial.X +
        Polynomial.C (Polynomial.derivative (-p₀)) := by
    rw [hFdec, e2, e2', e3, e4, dX_Y, dX_C, dX_C]
    simp only [smul_eq_mul, smul_zero, mul_zero, zero_add]
    ring
  have hdY : dY Wuniv.toAffine.polynomial =
      2 * Polynomial.X + Polynomial.C p₁ := by
    rw [dY_apply, hFdec]
    simp [Polynomial.derivative_pow]
    rw [show (Polynomial.C (2 : (MvPolynomial (Fin 5) ℤ)[X]) :
      (MvPolynomial (Fin 5) ℤ)[X][Y]) = 2 from map_ofNat _ 2]
  have hd₁ : Polynomial.derivative p₁ = Polynomial.C Wuniv.a₁ := by
    rw [hp₁]
    simp
  have hd₀ : Polynomial.derivative p₀ =
      Polynomial.C 3 * Polynomial.X ^ 2 +
        Polynomial.C (2 * Wuniv.a₂) * Polynomial.X +
        Polynomial.C Wuniv.a₄ := by
    rw [hp₀]
    simp [Polynomial.derivative_pow]
    C_simp
    ring1
  have hX : Wuniv.toAffine.polynomialX =
      Polynomial.C (Polynomial.C Wuniv.a₁) * Polynomial.X -
        Polynomial.C (Polynomial.C 3 * Polynomial.X ^ 2 +
          Polynomial.C (2 * Wuniv.a₂) * Polynomial.X +
          Polynomial.C Wuniv.a₄) := by
    rw [Affine.polynomialX]
  have hY : Wuniv.toAffine.polynomialY =
      2 * Polynomial.X + Polynomial.C (Polynomial.C Wuniv.a₁ *
        Polynomial.X + Polynomial.C Wuniv.a₃) := by
    rw [Affine.polynomialY]
    C_simp
  have hd₀n : Polynomial.derivative (-p₀) =
      -(Polynomial.C 3 * Polynomial.X ^ 2 +
        Polynomial.C (2 * Wuniv.a₂) * Polynomial.X +
        Polynomial.C Wuniv.a₄) := by
    rw [Polynomial.derivative_neg, hd₀]
  rw [happ, hdX, hdY, hX, hY, hd₁, hd₀n, hp₁]
  C_simp
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The quotient map onto the universal coordinate ring as an algebra
homomorphism over `ℤ[A₁,…,A₅]`. -/
noncomputable def mkAlgHom :
    (MvPolynomial (Fin 5) ℤ)[X][Y] →ₐ[MvPolynomial (Fin 5) ℤ] Buniv :=
  { CoordinateRing.mk Wuniv with commutes' := fun _ => rfl }

set_option backward.isDefEq.respectTransparency false in
lemma mkAlgHom_apply (P : (MvPolynomial (Fin 5) ℤ)[X][Y]) :
    mkAlgHom P = CoordinateRing.mk Wuniv P := rfl

set_option backward.isDefEq.respectTransparency false in
lemma mkAlgHom_surjective : Function.Surjective mkAlgHom :=
  AdjoinRoot.mk_surjective

set_option backward.isDefEq.respectTransparency false in
lemma mkAlgHom_ker_stable :
    ∀ P, mkAlgHom P = 0 → mkAlgHom (Dham P) = 0 := by
  intro P hP
  rw [mkAlgHom_apply, AdjoinRoot.mk_eq_zero] at hP
  obtain ⟨g, rfl⟩ := hP
  have hleib : Dham (Wuniv.toAffine.polynomial * g) =
      Wuniv.toAffine.polynomial • Dham g + g • Dham Wuniv.toAffine.polynomial :=
    Derivation.leibniz Dham _ _
  rw [hleib, Dham_polynomial, smul_zero, add_zero, smul_eq_mul,
    mkAlgHom_apply, map_mul]
  rw [show CoordinateRing.mk Wuniv Wuniv.toAffine.polynomial = 0 from
    AdjoinRoot.mk_self]
  ring

/-- **The universal invariant derivation on the coordinate ring**: the
Hamiltonian derivation descended along the quotient map. -/
noncomputable def DB : Derivation (MvPolynomial (Fin 5) ℤ) Buniv Buniv :=
  Derivation.liftOfSurjective mkAlgHom_surjective
    (d := Dham) mkAlgHom_ker_stable

set_option backward.isDefEq.respectTransparency false in
/-- The defining property of `DB`. -/
lemma DB_mk (P : (MvPolynomial (Fin 5) ℤ)[X][Y]) :
    DB (CoordinateRing.mk Wuniv P) = CoordinateRing.mk Wuniv (Dham P) :=
  Derivation.liftOfSurjective_apply mkAlgHom_surjective mkAlgHom_ker_stable P

/-! ## The extension to the universal function field

No fraction-field extension of derivations exists in mathlib, so we
hand-roll the quotient rule: every `z : Kuniv` has a representation
`z ⬝ s̄ = ā` with `s ≠ 0`, and `DK z := (D̄B a − z ⬝ D̄B s)/s̄` is
independent of the representation by the Leibniz rule. -/

set_option backward.isDefEq.respectTransparency false in
lemma exists_rep (z : Kuniv) : ∃ (a s : Buniv), s ≠ 0 ∧
    z * algebraMap Buniv Kuniv s = algebraMap Buniv Kuniv a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors Buniv) z
  exact ⟨a, s.1, nonZeroDivisors.ne_zero s.2, h⟩

/-- **The invariant derivation on the universal function field**,
extended from `DB` by the quotient rule. -/
noncomputable def DK (z : Kuniv) : Kuniv :=
  (algebraMap Buniv Kuniv (DB (exists_rep z).choose) -
      z * algebraMap Buniv Kuniv
        (DB (exists_rep z).choose_spec.choose)) /
    algebraMap Buniv Kuniv (exists_rep z).choose_spec.choose

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Representation-independence of the quotient rule. -/
lemma DK_welldef {z : Kuniv} {a s a' s' : Buniv} (hs : s ≠ 0)
    (hs' : s' ≠ 0)
    (h : z * algebraMap Buniv Kuniv s = algebraMap Buniv Kuniv a)
    (h' : z * algebraMap Buniv Kuniv s' = algebraMap Buniv Kuniv a') :
    (algebraMap Buniv Kuniv (DB a) -
        z * algebraMap Buniv Kuniv (DB s)) / algebraMap Buniv Kuniv s =
      (algebraMap Buniv Kuniv (DB a') -
        z * algebraMap Buniv Kuniv (DB s')) / algebraMap Buniv Kuniv s' := by
  have hinj := IsFractionRing.injective Buniv Kuniv
  have hcross : a * s' = a' * s := by
    apply hinj
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have h1 : DB (a * s') = a • DB s' + s' • DB a :=
    Derivation.leibniz DB a s'
  have h2 : DB (a' * s) = a' • DB s + s • DB a' :=
    Derivation.leibniz DB a' s
  have h3 := congrArg DB hcross
  rw [h1, h2] at h3
  simp only [smul_eq_mul] at h3
  have hsK : algebraMap Buniv Kuniv s ≠ 0 := fun hc =>
    hs (by simpa using hinj (hc.trans (map_zero _).symm))
  have hs'K : algebraMap Buniv Kuniv s' ≠ 0 := fun hc =>
    hs' (by simpa using hinj (hc.trans (map_zero _).symm))
  rw [div_eq_div_iff hsK hs'K]
  have hleibK := congrArg (algebraMap Buniv Kuniv) h3
  simp only [map_add, map_mul] at hleibK
  linear_combination hleibK +
    algebraMap Buniv Kuniv (DB s') * h -
    algebraMap Buniv Kuniv (DB s) * h'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The characterizing property of `DK`: independence of the chosen
representation. -/
lemma DK_spec {z : Kuniv} {a s : Buniv} (hs : s ≠ 0)
    (h : z * algebraMap Buniv Kuniv s = algebraMap Buniv Kuniv a) :
    DK z = (algebraMap Buniv Kuniv (DB a) -
        z * algebraMap Buniv Kuniv (DB s)) /
      algebraMap Buniv Kuniv s := by
  obtain ⟨hs₀, h₀⟩ := (exists_rep z).choose_spec.choose_spec
  exact DK_welldef hs₀ hs h₀ h

set_option backward.isDefEq.respectTransparency false in
/-- `DK` restricted to the coordinate ring is `DB`. -/
lemma DK_algebraMap (b : Buniv) :
    DK (algebraMap Buniv Kuniv b) = algebraMap Buniv Kuniv (DB b) := by
  have h : algebraMap Buniv Kuniv b * algebraMap Buniv Kuniv (1 : Buniv) =
      algebraMap Buniv Kuniv b := by
    rw [map_one, mul_one]
  rw [DK_spec one_ne_zero h, Derivation.map_one_eq_zero, map_zero,
    mul_zero, sub_zero, map_one, div_one]

set_option backward.isDefEq.respectTransparency false in
lemma algebraMap_Kuniv_ne_zero {b : Buniv} (hb : b ≠ 0) :
    algebraMap Buniv Kuniv b ≠ 0 := fun hc => hb (by
  simpa using IsFractionRing.injective Buniv Kuniv
    (hc.trans (map_zero (algebraMap Buniv Kuniv)).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The division-free form of the quotient rule. -/
lemma DK_rel {z : Kuniv} {a s : Buniv} (hs : s ≠ 0)
    (h : z * algebraMap Buniv Kuniv s = algebraMap Buniv Kuniv a) :
    DK z * algebraMap Buniv Kuniv s +
      z * algebraMap Buniv Kuniv (DB s) =
        algebraMap Buniv Kuniv (DB a) := by
  rw [DK_spec hs h, div_mul_eq_mul_div, div_add' _ _ _
    (algebraMap_Kuniv_ne_zero hs), div_eq_iff (algebraMap_Kuniv_ne_zero hs)]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Additivity of `DK`. -/
lemma DK_add (z w : Kuniv) : DK (z + w) = DK z + DK w := by
  obtain ⟨a, s, hs, h⟩ := exists_rep z
  obtain ⟨b, t, ht, h'⟩ := exists_rep w
  have hst : s * t ≠ 0 := mul_ne_zero hs ht
  have hrep : (z + w) * algebraMap Buniv Kuniv (s * t) =
      algebraMap Buniv Kuniv (a * t + b * s) := by
    rw [map_mul, map_add, map_mul, map_mul]
    linear_combination algebraMap Buniv Kuniv t * h +
      algebraMap Buniv Kuniv s * h'
  have R0 := DK_rel hst hrep
  have R1 := DK_rel hs h
  have R2 := DK_rel ht h'
  have e1 : DB (a * t + b * s) = DB (a * t) + DB (b * s) :=
    Derivation.map_add DB _ _
  have e2 : DB (a * t) = a • DB t + t • DB a := Derivation.leibniz DB a t
  have e3 : DB (b * s) = b • DB s + s • DB b := Derivation.leibniz DB b s
  have e4 : DB (s * t) = s • DB t + t • DB s := Derivation.leibniz DB s t
  rw [e1, e2, e3, e4] at R0
  simp only [smul_eq_mul, map_add, map_mul] at R0 R1 R2
  have key : (DK (z + w) - DK z - DK w) *
      (algebraMap Buniv Kuniv s * algebraMap Buniv Kuniv t) = 0 := by
    linear_combination R0 - algebraMap Buniv Kuniv t * R1 -
      algebraMap Buniv Kuniv s * R2 -
      algebraMap Buniv Kuniv (DB t) * h -
      algebraMap Buniv Kuniv (DB s) * h'
  rcases mul_eq_zero.mp key with hzero | hzero
  · linear_combination hzero
  · exact absurd hzero (mul_ne_zero (algebraMap_Kuniv_ne_zero hs)
      (algebraMap_Kuniv_ne_zero ht))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The Leibniz rule for `DK`. -/
lemma DK_mul (z w : Kuniv) : DK (z * w) = z * DK w + w * DK z := by
  obtain ⟨a, s, hs, h⟩ := exists_rep z
  obtain ⟨b, t, ht, h'⟩ := exists_rep w
  have hst : s * t ≠ 0 := mul_ne_zero hs ht
  have hrep : (z * w) * algebraMap Buniv Kuniv (s * t) =
      algebraMap Buniv Kuniv (a * b) := by
    rw [map_mul, map_mul]
    linear_combination (w * algebraMap Buniv Kuniv t) * h +
      algebraMap Buniv Kuniv a * h'
  have R0 := DK_rel hst hrep
  have R1 := DK_rel hs h
  have R2 := DK_rel ht h'
  have e1 : DB (a * b) = a • DB b + b • DB a := Derivation.leibniz DB a b
  have e4 : DB (s * t) = s • DB t + t • DB s := Derivation.leibniz DB s t
  rw [e1, e4] at R0
  simp only [smul_eq_mul, map_add, map_mul] at R0 R1 R2
  have key : (DK (z * w) - z * DK w - w * DK z) *
      (algebraMap Buniv Kuniv s * algebraMap Buniv Kuniv t) = 0 := by
    linear_combination R0 - z * algebraMap Buniv Kuniv s * R2 -
      w * algebraMap Buniv Kuniv t * R1 -
      algebraMap Buniv Kuniv (DB b) * h -
      algebraMap Buniv Kuniv (DB a) * h'
  rcases mul_eq_zero.mp key with hzero | hzero
  · linear_combination hzero
  · exact absurd hzero (mul_ne_zero (algebraMap_Kuniv_ne_zero hs)
      (algebraMap_Kuniv_ne_zero ht))

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma DK_zero : DK 0 = 0 := by
  have h := DK_add 0 0
  rw [add_zero] at h
  linear_combination -h

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma DK_one : DK 1 = 0 := by
  have h := DK_mul 1 1
  rw [mul_one, one_mul] at h
  linear_combination -h

set_option backward.isDefEq.respectTransparency false in
lemma DK_sub (z w : Kuniv) : DK (z - w) = DK z - DK w := by
  have hneg : DK (-w) = -DK w := by
    have h := DK_add w (-w)
    rw [add_neg_cancel, DK_zero] at h
    linear_combination -h
  rw [sub_eq_add_neg, DK_add, hneg, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
/-- The quotient rule for `DK`. -/
lemma DK_div (u v : Kuniv) (hv : v ≠ 0) :
    DK (u / v) = (DK u * v - u * DK v) / v ^ 2 := by
  have hu : u / v * v = u := div_mul_cancel₀ u hv
  have h := DK_mul (u / v) v
  rw [hu] at h
  rw [eq_div_iff (pow_ne_zero 2 hv)]
  linear_combination (-v) * h - DK v * hu

set_option backward.isDefEq.respectTransparency false in
lemma DK_sq (z : Kuniv) : DK (z ^ 2) = 2 * z * DK z := by
  have h := DK_mul z z
  rw [← sq] at h
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
/-- `DK` kills the coefficient constants `a₁, …, a₆`. -/
lemma DK_coeffHom (p : MvPolynomial (Fin 5) ℤ) : DK (coeffHom p) = 0 := by
  have hrepr : coeffHom p = algebraMap Buniv Kuniv
      (CoordinateRing.mk Wuniv (Polynomial.C (Polynomial.C p))) := rfl
  rw [hrepr, DK_algebraMap, DB_mk]
  rw [show Dham (Polynomial.C (Polynomial.C p)) = 0 by
    rw [Dham_C]
    simp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The base derivative**: `DK(x) = ψ₂(x, y) = 2y + a₁x + a₃` at the
tautological point — the normalization `dx/ω = ψ₂` of the invariant
differential. -/
lemma DK_tautX : DK tautX =
    2 * tautY + coeffHom (MvPolynomial.X 0) * tautX +
      coeffHom (MvPolynomial.X 2) := by
  have hrepr : tautX = algebraMap Buniv Kuniv
      (CoordinateRing.mk Wuniv (Polynomial.C Polynomial.X)) := rfl
  rw [hrepr, DK_algebraMap, DB_mk]
  rw [show Dham (Polynomial.C Polynomial.X) =
      Wuniv.toAffine.polynomialY by
    rw [Dham_C]
    simp]
  have harg : Wuniv.toAffine.polynomialY =
      2 * Polynomial.X +
        Polynomial.C (Polynomial.C Wuniv.a₁) *
          Polynomial.C Polynomial.X +
        Polynomial.C (Polynomial.C Wuniv.a₃) := by
    rw [Affine.polynomialY]
    C_simp
    ring
  rw [harg]
  simp only [map_add, map_mul, map_ofNat]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The companion base derivative: `DK(y) = −F_X(x, y)` at the
tautological point. -/
lemma DK_tautY : DK tautY =
    -(coeffHom (MvPolynomial.X 0) * tautY -
      (3 * tautX ^ 2 + 2 * coeffHom (MvPolynomial.X 1) * tautX +
        coeffHom (MvPolynomial.X 3))) := by
  have hrepr : tautY = algebraMap Buniv Kuniv
      (CoordinateRing.mk Wuniv Polynomial.X) := rfl
  rw [hrepr, DK_algebraMap, DB_mk]
  rw [show Dham (Polynomial.X : (MvPolynomial (Fin 5) ℤ)[X][Y]) =
      -Wuniv.toAffine.polynomialX from Dham_Y]
  have harg : -Wuniv.toAffine.polynomialX =
      -(Polynomial.C (Polynomial.C Wuniv.a₁) * Polynomial.X -
        (3 * Polynomial.C Polynomial.X ^ 2 +
          2 * Polynomial.C (Polynomial.C Wuniv.a₂) *
            Polynomial.C Polynomial.X +
          Polynomial.C (Polynomial.C Wuniv.a₄))) := by
    rw [Affine.polynomialX]
    C_simp
  rw [harg]
  simp only [map_neg, map_sub, map_add, map_mul, map_pow, map_ofNat]
  rfl

end PsiSumCompanion
