/-
TautMultiplication.lean — own work for the Fermat project.

The proven multiplication machinery (`TorsionCard`) instantiated at
the tautological point of the universal curve: `n • (tautX, tautY)` is
affine and satisfies the `x`-formula, with all division-polynomial
denominators nonzero. This is the engine that derives the composition
identities `(C)` behind `separable_preΨ'` as generic-point facts, to
be pulled back to `ℤ[A][X]` along `taut_evalEval_mk`.
-/
module

public import Fermat.FLT.EllipticCurve.TautologicalPoint
import Fermat.FLT.EllipticCurve.TorsionCard
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Points

@[expose] public section

namespace PsiSumCompanion

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

noncomputable instance : DecidableEq Kuniv := Classical.decEq _

set_option backward.isDefEq.respectTransparency false in
/-- The tautological point on the (identity-)base-changed curve. -/
theorem tautNS' : (WK⁄Kuniv).toAffine.Nonsingular tautX tautY :=
  WK_baseChange_self.symm ▸ taut_nonsingular

set_option backward.isDefEq.respectTransparency false in
/-- Division-polynomial values at the tautological point are nonzero
(base-changed form). -/
theorem taut_psi_ne_zero' {n : ℤ} (hn : n ≠ 0) :
    (((WK⁄Kuniv).ψ n).evalEval tautX tautY : Kuniv) ≠ 0 :=
  WK_baseChange_self.symm ▸ taut_psi_ne_zero hn

set_option backward.isDefEq.respectTransparency false in
/-- `ΨSq`-values at the tautological point are nonzero. -/
theorem taut_ΨSq_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (((WK⁄Kuniv).ΨSq n).eval tautX : Kuniv) ≠ 0 := by
  intro hc
  apply taut_psi_ne_zero' hn
  have hbridge : ((WK⁄Kuniv).ψ n).evalEval tautX tautY ^ 2 =
      ((WK⁄Kuniv).ΨSq n).eval tautX := by
    rw [← WeierstrassCurve.evalEval_Ψ_sq n tautNS'.1,
      WeierstrassCurve.evalEval_ψ n tautNS'.1]
  exact pow_eq_zero_iff two_ne_zero |>.mp (hbridge.trans hc)

set_option backward.isDefEq.respectTransparency false in
/-- **The multiplication formula at the tautological point**: for
`n ≠ 0`, `n • (tautX, tautY)` is an affine point whose `x`-coordinate
satisfies `x' ⬝ ΨSqₙ(tautX) = Φₙ(tautX)`. -/
theorem taut_smul_formula {n : ℤ} (hn : n ≠ 0) :
    ∃ (x' y' : Kuniv) (h' : (WK⁄Kuniv).toAffine.Nonsingular x' y'),
      n • (Affine.Point.some tautX tautY tautNS' : (WK⁄Kuniv).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((WK⁄Kuniv).ΨSq n).eval tautX =
        ((WK⁄Kuniv).Φ n).eval tautX :=
  TorsionCard.exists_smul_some_eq WK hn tautNS' (taut_ΨSq_ne_zero hn)

set_option backward.isDefEq.respectTransparency false in
/-- **The composition cross-identity at the tautological point**
(value level): there is an affine point `(xₙ, yₙ) = n • taut` with
`xₙ ⬝ ΨSqₙ(tX) = Φₙ(tX)`, and the `m`-multiplication formula composed
through it gives `Φₘₙ(tX) ⬝ ΨSqₘ(xₙ) = ΨSqₘₙ(tX) ⬝ Φₘ(xₙ)`. -/
theorem taut_cross {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ (xn yn : Kuniv) (_ : (WK⁄Kuniv).toAffine.Nonsingular xn yn),
      xn * ((WK⁄Kuniv).ΨSq n).eval tautX = ((WK⁄Kuniv).Φ n).eval tautX ∧
      ((WK⁄Kuniv).Φ (m * n)).eval tautX * ((WK⁄Kuniv).ΨSq m).eval xn =
        ((WK⁄Kuniv).ΨSq (m * n)).eval tautX *
          ((WK⁄Kuniv).Φ m).eval xn := by
  obtain ⟨xn, yn, hns, hsmuln, hxn⟩ := taut_smul_formula hn
  obtain ⟨X2, Y2, H2, hsmulmn, hXmn⟩ :=
    taut_smul_formula (mul_ne_zero hm hn)
  have hcomp : m • (Affine.Point.some xn yn hns : (WK⁄Kuniv).Point) =
      Affine.Point.some X2 Y2 H2 := by
    rw [← hsmuln, smul_smul]
    exact hsmulmn
  have hne : (((WK⁄Kuniv).ΨSq m).eval xn : Kuniv) ≠ 0 := by
    intro hc
    have h0 : m • (Affine.Point.some xn yn hns : (WK⁄Kuniv).Point) = 0 :=
      (TorsionCard.smul_some_eq_zero_iff WK hm hns).mpr hc
    rw [hcomp] at h0
    exact Affine.Point.some_ne_zero H2 h0
  obtain ⟨x', y', h'', hsmulm, hxm⟩ :=
    TorsionCard.exists_smul_some_eq WK hm hns hne
  rw [hcomp] at hsmulm
  obtain ⟨hxx, -⟩ := Affine.Point.some.inj hsmulm.symm
  subst hxx
  refine ⟨xn, yn, hns, hxn, ?_⟩
  linear_combination (-(((WK⁄Kuniv).ΨSq m).eval xn : Kuniv)) * hXmn +
    (((WK⁄Kuniv).ΨSq (m * n)).eval tautX : Kuniv) * hxm

set_option backward.isDefEq.respectTransparency false in
/-- **The `m = 2` composition cross-identity, denominators cleared**:
with `Fₙ, Sₙ` the `Φ, ΨSq`-values at `tautX`,
`Φ₂ₙ(tX) ⬝ (4Fₙ³Sₙ + b₂Fₙ²Sₙ² + 2b₄FₙSₙ³ + b₆Sₙ⁴)
  = ΨSq₂ₙ(tX) ⬝ (Fₙ⁴ − b₄Fₙ²Sₙ² − 2b₆FₙSₙ³ − b₈Sₙ⁴)`. -/
theorem taut_cross_two {n : ℤ} (hn : n ≠ 0) :
    ((WK⁄Kuniv).Φ (2 * n)).eval tautX *
        (4 * ((WK⁄Kuniv).Φ n).eval tautX ^ 3 *
            ((WK⁄Kuniv).ΨSq n).eval tautX +
          (WK⁄Kuniv).b₂ * ((WK⁄Kuniv).Φ n).eval tautX ^ 2 *
            ((WK⁄Kuniv).ΨSq n).eval tautX ^ 2 +
          2 * (WK⁄Kuniv).b₄ * ((WK⁄Kuniv).Φ n).eval tautX *
            ((WK⁄Kuniv).ΨSq n).eval tautX ^ 3 +
          (WK⁄Kuniv).b₆ * ((WK⁄Kuniv).ΨSq n).eval tautX ^ 4) =
      ((WK⁄Kuniv).ΨSq (2 * n)).eval tautX *
        (((WK⁄Kuniv).Φ n).eval tautX ^ 4 -
          (WK⁄Kuniv).b₄ * ((WK⁄Kuniv).Φ n).eval tautX ^ 2 *
            ((WK⁄Kuniv).ΨSq n).eval tautX ^ 2 -
          2 * (WK⁄Kuniv).b₆ * ((WK⁄Kuniv).Φ n).eval tautX *
            ((WK⁄Kuniv).ΨSq n).eval tautX ^ 3 -
          (WK⁄Kuniv).b₈ * ((WK⁄Kuniv).ΨSq n).eval tautX ^ 4) := by
  obtain ⟨xn, yn, -, hxn, hcross⟩ := taut_cross two_ne_zero hn
  rw [WeierstrassCurve.ΨSq_two, WeierstrassCurve.Φ_two,
    WeierstrassCurve.Ψ₂Sq] at hcross
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hcross
  have hSn : (((WK⁄Kuniv).ΨSq n).eval tautX : Kuniv) ≠ 0 :=
    taut_ΨSq_ne_zero hn
  have hxn' : xn =
      ((WK⁄Kuniv).Φ n).eval tautX / ((WK⁄Kuniv).ΨSq n).eval tautX :=
    (eq_div_iff hSn).mpr hxn
  rw [hxn'] at hcross
  field_simp at hcross
  linear_combination hcross

set_option backward.isDefEq.respectTransparency false in
/-- **The universal `m = 2` composition cross-identity**: in
`ℤ[A₁,…,A₅][X]`, for every `n ≠ 0`,
`Φ₂ₙ ⬝ Ψ₂Sqʰᵒᵐ(Φₙ, ΨSqₙ) = ΨSq₂ₙ ⬝ Φ₂ʰᵒᵐ(Φₙ, ΨSqₙ)`, where the
homogenized duplication polynomials are the explicit quartics. Proven
by evaluating at the tautological point and pulling back along the
`y`-free embedding. -/
theorem univ_cross_two {n : ℤ} (hn : n ≠ 0) :
    Wuniv.Φ (2 * n) *
        (4 * Wuniv.Φ n ^ 3 * Wuniv.ΨSq n +
          Polynomial.C Wuniv.b₂ * Wuniv.Φ n ^ 2 * Wuniv.ΨSq n ^ 2 +
          2 * Polynomial.C Wuniv.b₄ * Wuniv.Φ n * Wuniv.ΨSq n ^ 3 +
          Polynomial.C Wuniv.b₆ * Wuniv.ΨSq n ^ 4) =
      Wuniv.ΨSq (2 * n) *
        (Wuniv.Φ n ^ 4 -
          Polynomial.C Wuniv.b₄ * Wuniv.Φ n ^ 2 * Wuniv.ΨSq n ^ 2 -
          2 * Polynomial.C Wuniv.b₆ * Wuniv.Φ n * Wuniv.ΨSq n ^ 3 -
          Polynomial.C Wuniv.b₈ * Wuniv.ΨSq n ^ 4) := by
  have h : ((WK.Φ (2 * n)).eval tautX : Kuniv) *
      (4 * (WK.Φ n).eval tautX ^ 3 * (WK.ΨSq n).eval tautX +
        WK.b₂ * (WK.Φ n).eval tautX ^ 2 * (WK.ΨSq n).eval tautX ^ 2 +
        2 * WK.b₄ * (WK.Φ n).eval tautX * (WK.ΨSq n).eval tautX ^ 3 +
        WK.b₆ * (WK.ΨSq n).eval tautX ^ 4) =
      (WK.ΨSq (2 * n)).eval tautX *
        ((WK.Φ n).eval tautX ^ 4 -
          WK.b₄ * (WK.Φ n).eval tautX ^ 2 * (WK.ΨSq n).eval tautX ^ 2 -
          2 * WK.b₆ * (WK.Φ n).eval tautX * (WK.ΨSq n).eval tautX ^ 3 -
          WK.b₈ * (WK.ΨSq n).eval tautX ^ 4) :=
    WK_baseChange_self ▸ taut_cross_two hn
  have h2 : (((Wuniv.map coeffHom).Φ (2 * n)).eval tautX : Kuniv) *
      (4 * ((Wuniv.map coeffHom).Φ n).eval tautX ^ 3 *
          ((Wuniv.map coeffHom).ΨSq n).eval tautX +
        (Wuniv.map coeffHom).b₂ *
          ((Wuniv.map coeffHom).Φ n).eval tautX ^ 2 *
          ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 2 +
        2 * (Wuniv.map coeffHom).b₄ *
          ((Wuniv.map coeffHom).Φ n).eval tautX *
          ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 3 +
        (Wuniv.map coeffHom).b₆ *
          ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 4) =
      ((Wuniv.map coeffHom).ΨSq (2 * n)).eval tautX *
        (((Wuniv.map coeffHom).Φ n).eval tautX ^ 4 -
          (Wuniv.map coeffHom).b₄ *
            ((Wuniv.map coeffHom).Φ n).eval tautX ^ 2 *
            ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 2 -
          2 * (Wuniv.map coeffHom).b₆ *
            ((Wuniv.map coeffHom).Φ n).eval tautX *
            ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 3 -
          (Wuniv.map coeffHom).b₈ *
            ((Wuniv.map coeffHom).ΨSq n).eval tautX ^ 4) := h
  simp only [WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈,
    taut_eval_C_mk] at h2
  have hb : ∀ p : MvPolynomial (Fin 5) ℤ, coeffHom p =
      algebraMap Buniv Kuniv
        (CoordinateRing.mk Wuniv (Polynomial.C (Polynomial.C p))) :=
    fun p => rfl
  rw [hb, hb, hb, hb] at h2
  apply taut_C_injective
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  linear_combination h2

set_option backward.isDefEq.respectTransparency false in
/-- **The `m = 2` composition cross-identity over any commutative
ring**: `Φ₂ₙ ⬝ Ψ₂Sqʰᵒᵐ(Φₙ, ΨSqₙ) = ΨSq₂ₙ ⬝ Φ₂ʰᵒᵐ(Φₙ, ΨSqₙ)`, by
specializing the universal identity. -/
theorem cross_two {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {n : ℤ} (hn : n ≠ 0) :
    W.Φ (2 * n) *
        (4 * W.Φ n ^ 3 * W.ΨSq n +
          Polynomial.C W.b₂ * W.Φ n ^ 2 * W.ΨSq n ^ 2 +
          2 * Polynomial.C W.b₄ * W.Φ n * W.ΨSq n ^ 3 +
          Polynomial.C W.b₆ * W.ΨSq n ^ 4) =
      W.ΨSq (2 * n) *
        (W.Φ n ^ 4 -
          Polynomial.C W.b₄ * W.Φ n ^ 2 * W.ΨSq n ^ 2 -
          2 * Polynomial.C W.b₆ * W.Φ n * W.ΨSq n ^ 3 -
          Polynomial.C W.b₈ * W.ΨSq n ^ 4) := by
  set σ : MvPolynomial (Fin 5) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hmap : Wuniv.map σ = W := by
    simp only [Wuniv, WeierstrassCurve.map, MvPolynomial.eval₂Hom_X', σ]
    rfl
  have hb2 : σ Wuniv.b₂ = W.b₂ := by
    rw [← WeierstrassCurve.map_b₂, hmap]
  have hb4 : σ Wuniv.b₄ = W.b₄ := by
    rw [← WeierstrassCurve.map_b₄, hmap]
  have hb6 : σ Wuniv.b₆ = W.b₆ := by
    rw [← WeierstrassCurve.map_b₆, hmap]
  have hb8 : σ Wuniv.b₈ = W.b₈ := by
    rw [← WeierstrassCurve.map_b₈, hmap]
  have h := congrArg (Polynomial.map σ) (univ_cross_two hn)
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_C,
    ← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq, hmap,
    hb2, hb4, hb6, hb8] at h
  exact h

end PsiSumCompanion
