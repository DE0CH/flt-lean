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

end PsiSumCompanion
