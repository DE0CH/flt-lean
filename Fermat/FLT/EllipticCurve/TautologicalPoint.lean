/-
TautologicalPoint.lean — own work for the Fermat project.

The tautological point of the universal Weierstrass curve: base-change
`Wuniv` (generic `a`-coefficients over `ℤ[A₁, …, A₅]`) to the fraction
field `Kuniv` of its coordinate ring; the images of `X` and `Y` give a
NONSINGULAR point. Division-polynomial values at this point are the
images of the division polynomials themselves, and they are all
nonzero (`mk_Ψ_univ_ne_zero`), so the whole proven multiplication
machinery (x-formulas, trackings) applies at the generic point; y-free
polynomial identities verified there pull back to `ℤ[A][X]` along the
`{1, Y}`-basis injectivity. This is the engine for the composition
identities `(C)` behind `separable_preΨ'`.
-/
module

public import Fermat.FLT.EllipticCurve.UniversalCurve
import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

/-- The universal coordinate ring `ℤ[A][X, Y]/(Weierstrass)`. -/
noncomputable abbrev Buniv : Type _ := Wuniv.toAffine.CoordinateRing

/-- The universal function field: the fraction field of the universal
coordinate ring (a domain since `ℤ[A]` is). -/
noncomputable abbrev Kuniv : Type _ := FractionRing Buniv

/-- The coefficient specialisation `ℤ[A] → Kuniv`. -/
noncomputable def coeffHom : MvPolynomial (Fin 5) ℤ →+* Kuniv :=
  (algebraMap Buniv Kuniv).comp <|
    (CoordinateRing.mk Wuniv).comp <|
      (Polynomial.C : (MvPolynomial (Fin 5) ℤ)[X] →+* _).comp
        (Polynomial.C : MvPolynomial (Fin 5) ℤ →+* _)

/-- The universal curve over its own function field. -/
noncomputable def WK : WeierstrassCurve Kuniv := Wuniv.map coeffHom

/-- The tautological `x`-coordinate. -/
noncomputable def tautX : Kuniv :=
  algebraMap Buniv Kuniv (CoordinateRing.mk Wuniv (Polynomial.C Polynomial.X))

/-- The tautological `y`-coordinate. -/
noncomputable def tautY : Kuniv :=
  algebraMap Buniv Kuniv (CoordinateRing.mk Wuniv Polynomial.X)

set_option backward.isDefEq.respectTransparency false in
/-- The tautological point satisfies the Weierstrass equation. -/
theorem taut_equation : WK.toAffine.Equation tautX tautY := by
  rw [Affine.equation_iff]
  have h : (algebraMap Buniv Kuniv) (CoordinateRing.mk Wuniv
      (Polynomial.X ^ 2 + Polynomial.C (Polynomial.C Wuniv.a₁ *
        Polynomial.X + Polynomial.C Wuniv.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C Wuniv.a₂ *
        Polynomial.X ^ 2 + Polynomial.C Wuniv.a₄ * Polynomial.X +
        Polynomial.C Wuniv.a₆))) = 0 := by
    show (algebraMap Buniv Kuniv) (CoordinateRing.mk Wuniv
      Wuniv.toAffine.polynomial) = 0
    rw [AdjoinRoot.mk_self, map_zero]
  simp only [map_add, map_sub, map_mul, map_pow] at h
  show tautY ^ 2 + WK.a₁ * tautX * tautY + WK.a₃ * tautY =
    tautX ^ 3 + WK.a₂ * tautX ^ 2 + WK.a₄ * tautX + WK.a₆
  simp only [WK, WeierstrassCurve.map, coeffHom, RingHom.coe_comp,
    Function.comp_apply, tautX, tautY] at h ⊢
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
/-- The universal discriminant is nonzero (evaluate at `y² + y = x³`,
where `Δ = -27`). -/
theorem Δ_univ_ne_zero : Wuniv.Δ ≠ 0 := by
  intro hc
  have h := congrArg (MvPolynomial.eval
    (fun i : Fin 5 => if i = 2 then (1 : ℤ) else 0)) hc
  rw [map_zero] at h
  rw [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈] at h
  simp only [Wuniv, map_add, map_sub, map_mul, map_pow, map_ofNat,
    MvPolynomial.eval_X] at h
  norm_num [Fin.ext_iff] at h

set_option backward.isDefEq.respectTransparency false in
/-- `coeffHom` is injective (constants embed through the
`{1, Y}`-basis and the fraction field). -/
theorem coeffHom_injective : Function.Injective coeffHom := by
  intro s t hst
  have h0 : coeffHom (s - t) = 0 := by rw [map_sub, hst, sub_self]
  have hB : CoordinateRing.mk Wuniv (Polynomial.C (Polynomial.C (s - t)))
      = 0 := by
    apply IsFractionRing.injective Buniv Kuniv
    rw [map_zero]
    exact h0
  have hsmul : (Polynomial.C (s - t)) •
      (1 : Wuniv.toAffine.CoordinateRing) +
      (0 : (MvPolynomial (Fin 5) ℤ)[X]) •
        CoordinateRing.mk Wuniv Polynomial.X = 0 := by
    simp only [CoordinateRing.smul, mul_one, map_zero, zero_mul,
      add_zero]
    exact hB
  have := (CoordinateRing.smul_basis_eq_zero hsmul).1
  have hzero : s - t = 0 := by
    have hcoeff := congrArg (fun g => Polynomial.coeff g 0) this
    simpa using hcoeff
  exact sub_eq_zero.mp hzero

set_option backward.isDefEq.respectTransparency false in
/-- The base-changed universal curve has nonzero discriminant. -/
theorem WK_Δ_ne_zero : WK.Δ ≠ 0 := by
  intro hc
  rw [WK, WeierstrassCurve.map_Δ] at hc
  exact Δ_univ_ne_zero (coeffHom_injective (by rwa [map_zero]))

set_option backward.isDefEq.respectTransparency false in
/-- **The tautological point is nonsingular.** -/
theorem taut_nonsingular : WK.toAffine.Nonsingular tautX tautY :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero WK_Δ_ne_zero).mp
    taut_equation

end PsiSumCompanion
