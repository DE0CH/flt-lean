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

end PsiSumCompanion
