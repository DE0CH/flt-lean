import Fermat.FLT.FreyCurve.MazurTorsion

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine

namespace Try292

variable {F : Type} [Field F] [DecidableEq F]

/-- A change of variables is given by rational functions in the coordinates:
`x ↦ u²x + r` and `y ↦ u³y + u²sx + t`. -/
theorem isRationalMap_mapVariableChange (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.IsRationalMap (WeierstrassCurve.Affine.Point.mapVariableChange W C) := by
  refine ⟨Polynomial.C ((C.u : F) ^ 2) * X + Polynomial.C C.r, 1,
    Polynomial.C ((C.u : F) ^ 3),
    Polynomial.C ((C.u : F) ^ 2 * C.s) * X + Polynomial.C C.t, 1,
    one_ne_zero, one_ne_zero, ?_⟩
  rintro (_ | ⟨x, y, h⟩) hP
  · exact absurd rfl hP
  · constructor
    · simp [WeierstrassCurve.Affine.Point.mapVariableChange,
        WeierstrassCurve.Affine.Point.mapVariableChangeFun_some]
    · simp only [WeierstrassCurve.Affine.Point.mapVariableChange,
        WeierstrassCurve.Affine.Point.mapVariableChangeFun_some, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, veluPointY_some, veluPointX_some, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
        mul_one]
      ring

/-- A change of variables is an ISOGENY: rational, bijective on points. -/
theorem isIsogeny_mapVariableChange (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.IsIsogeny (WeierstrassCurve.Affine.Point.mapVariableChange W C) where
  isRationalMap := isRationalMap_mapVariableChange W C
  surjective _ := (WeierstrassCurve.Affine.Point.equivVariableChange W C).surjective
  finite_ker _ := by
    have h : (AddMonoidHom.ker (WeierstrassCurve.Affine.Point.mapVariableChange W C) :
        Set (C • W).toAffine.Point) = {0} := by
      ext P
      simp only [Set.mem_singleton_iff, SetLike.mem_coe, AddMonoidHom.mem_ker]
      refine ⟨fun hc => WeierstrassCurve.Affine.Point.mapVariableChangeFun_injective W C ?_,
        fun hc => by rw [hc, map_zero]⟩
      show WeierstrassCurve.Affine.Point.mapVariableChangeFun W C P
        = WeierstrassCurve.Affine.Point.mapVariableChangeFun W C 0
      rw [WeierstrassCurve.Affine.Point.mapVariableChangeFun_zero]
      exact hc
    rw [h]; exact Set.finite_singleton _

end Try292

/-- Transport along an equality of curves is an isogeny. -/
theorem isIsogeny_equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    WeierstrassCurve.IsIsogeny
      (WeierstrassCurve.Affine.Point.equivOfEq h).toAddMonoidHom where
  isRationalMap := by
    subst h
    refine ⟨X, 1, 1, 0, 1, one_ne_zero, one_ne_zero, ?_⟩
    rintro (_ | ⟨x, y, hns⟩) hP
    · exact absurd rfl hP
    · simp [WeierstrassCurve.Affine.Point.equivOfEq]
  surjective _ := (WeierstrassCurve.Affine.Point.equivOfEq h).surjective
  finite_ker _ := by
    have hk : (AddMonoidHom.ker (WeierstrassCurve.Affine.Point.equivOfEq h).toAddMonoidHom :
        Set V.toAffine.Point) = {0} := by
      ext P
      simp only [Set.mem_singleton_iff, SetLike.mem_coe, AddMonoidHom.mem_ker]
      exact ⟨fun hc => (WeierstrassCurve.Affine.Point.equivOfEq h).injective
          (by rw [map_zero]; exact hc),
        fun hc => by rw [hc, map_zero]⟩
    rw [hk]; exact Set.finite_singleton _
