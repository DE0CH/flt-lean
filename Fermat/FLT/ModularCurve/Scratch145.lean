module

public import Fermat.FLT.ModularCurve.X0
public import Mathlib.Algebra.DualNumber

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Fermat

namespace Scratch145

/-- `Spec ℚ[ε]`, `ε² = 0`. -/
noncomputable abbrev SpecD : Scheme.{0} := Spec (CommRingCat.of (DualNumber ℚ))

/-- the structure morphism `Spec ℚ[ε] ⟶ Spec ℚ` -/
noncomputable def dualStr : SpecD ⟶ SpecQ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (DualNumber ℚ)))

/-- the augmentation section `Spec ℚ ⟶ Spec ℚ[ε]`, `ε ↦ 0` -/
noncomputable def dualAug : SpecQ ⟶ SpecD :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom ℚ ℚ ℚ : DualNumber ℚ →ₐ[ℚ] ℚ).toRingHom)

theorem dualAug_comp : dualAug ≫ dualStr = 𝟙 SpecQ := by
  rw [dualAug, dualStr, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of ℚ)
  ext x
  rfl

/-- **The tangent space of an abelian scheme over `ℚ` at the origin**, as the
kernel of `J(ℚ[ε]) → J(ℚ)`. -/
def tangentAtZero {J : Scheme.{0}} {jstr : J ⟶ SpecQ} (ab : AbelianSchemeStruct jstr) :
    Set (RelPoint jstr dualStr) :=
  {x | RelPoint.pre dualAug dualAug_comp x = ab.zero (𝟙 SpecQ)}

/-- it is a subGROUP of `J(ℚ[ε])` -/
noncomputable def tangentSubgroup {J : Scheme.{0}} {jstr : J ⟶ SpecQ}
    (ab : AbelianSchemeStruct jstr) :
    letI := ab.addCommGroup dualStr
    AddSubgroup (RelPoint jstr dualStr) :=
  letI := ab.addCommGroup dualStr
  { carrier := tangentAtZero ab
    add_mem' := by
      intro a b ha hb
      show RelPoint.pre dualAug dualAug_comp (ab.add a b) = ab.zero (𝟙 SpecQ)
      rw [ab.pre_add]
      show ab.add (RelPoint.pre dualAug dualAug_comp a) (RelPoint.pre dualAug dualAug_comp b) = _
      rw [ha, hb]
      exact ab.zero_add _
    zero_mem' := ab.pre_zero dualAug dualAug_comp
    neg_mem' := by
      intro a ha
      show RelPoint.pre dualAug dualAug_comp (ab.neg a) = ab.zero (𝟙 SpecQ)
      have h := ab.pre_add dualAug dualAug_comp (ab.neg a) a
      rw [ab.neg_add, ab.pre_zero] at h
      show _ = ab.zero (𝟙 SpecQ)
      have ha' : RelPoint.pre dualAug dualAug_comp a = ab.zero (𝟙 SpecQ) := ha
      rw [ha', ab.add_comm, ab.zero_add] at h
      exact h.symm }

/-- **an endomorphism of `J` over `ℚ` acts on the tangent space** -/
theorem tangent_post_mem {J : Scheme.{0}} {jstr : J ⟶ SpecQ}
    (ab : AbelianSchemeStruct jstr) (u : J ⟶ J) (hu : u ≫ jstr = jstr)
    (hadd : IsAdditiveOn ab ab u hu) (x : RelPoint jstr dualStr)
    (hx : x ∈ tangentAtZero ab) : RelPoint.post u hu x ∈ tangentAtZero ab := by
  have hcomm : RelPoint.pre dualAug dualAug_comp (RelPoint.post u hu x)
      = RelPoint.post u hu (RelPoint.pre dualAug dualAug_comp x) :=
    Subtype.ext (Category.assoc _ _ _).symm
  show RelPoint.pre dualAug dualAug_comp (RelPoint.post u hu x) = ab.zero (𝟙 SpecQ)
  rw [hcomm]
  have hx' : RelPoint.pre dualAug dualAug_comp x = ab.zero (𝟙 SpecQ) := hx
  rw [hx']
  -- an additive map sends `0` to `0`
  have h0 := hadd (ab.zero (𝟙 SpecQ)) (ab.zero (𝟙 SpecQ))
  rw [ab.zero_add] at h0
  letI := ab.addCommGroup (𝟙 SpecQ)
  have h1 : RelPoint.post u hu (ab.zero (𝟙 SpecQ))
      + RelPoint.post u hu (ab.zero (𝟙 SpecQ))
      = 0 + RelPoint.post u hu (ab.zero (𝟙 SpecQ)) := by
    rw [zero_add]; exact h0.symm
  exact add_right_cancel h1

end Scratch145

end Fermat
