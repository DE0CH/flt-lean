import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.CategoryTheory.Monoidal.Functor

universe u

open CategoryTheory Limits MonoidalCategory Functor Functor.LaxMonoidal

namespace PresheafOfModules

open PresheafOfModules.Monoidal

variable {C : Type u} [SmallCategory C] {S T : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ T)

/-- the RingCat-level morphism -/
noncomputable abbrev toRingHom :
    (S ⋙ forget₂ CommRingCat RingCat) ⟶ (T ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
/-- `μ` for restriction of scalars of presheaves of modules. -/
noncomputable def rsMu (A B : PresheafOfModules.{u} (T ⋙ forget₂ _ _)) :
    (restrictScalars (toRingHom α)).obj A ⊗ (restrictScalars (toRingHom α)).obj B ⟶
      (restrictScalars (toRingHom α)).obj (A ⊗ B) where
  app X := μ (ModuleCat.restrictScalars ((toRingHom α).app X).hom) (A.obj X) (B.obj X)
  naturality {X Y} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    dsimp
    erw [tensorObj_map_tmul, ModuleCat.restrictScalars_μ_tmul,
      ModuleCat.restrictScalars_μ_tmul, tensorObj_map_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- `ε` for restriction of scalars of presheaves of modules. -/
noncomputable def rsEps :
    𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶
      (restrictScalars (toRingHom α)).obj (𝟙_ (PresheafOfModules.{u} (T ⋙ forget₂ _ _))) where
  app X := ε (ModuleCat.restrictScalars ((toRingHom α).app X).hom)
  naturality {X Y} f := by
    ext
    dsimp
    erw [unit_map_one, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    rw [map_one, map_one]
    exact (unit_map_one (R := T ⋙ forget₂ CommRingCat RingCat) f).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of scalars of presheaves of modules is lax monoidal.** -/
noncomputable instance restrictScalarsLaxMonoidal :
    (restrictScalars (toRingHom α)).LaxMonoidal where
  ε := rsEps α
  μ A B := rsMu α A B
  μ_natural_left f X' := by
    ext1 X
    exact μ_natural_left (ModuleCat.restrictScalars ((toRingHom α).app X).hom) (f.app X) (X'.obj X)
  μ_natural_right X' f := by
    ext1 X
    exact μ_natural_right (ModuleCat.restrictScalars ((toRingHom α).app X).hom) (X'.obj X) (f.app X)
  associativity A B D := by
    ext1 X
    exact associativity (ModuleCat.restrictScalars ((toRingHom α).app X).hom)
      (A.obj X) (B.obj X) (D.obj X)
  left_unitality A := by
    ext1 X
    exact left_unitality (ModuleCat.restrictScalars ((toRingHom α).app X).hom) (A.obj X)
  right_unitality A := by
    ext1 X
    exact right_unitality (ModuleCat.restrictScalars ((toRingHom α).app X).hom) (A.obj X)

section Pushforward

variable {D : Type u} [SmallCategory D] {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)

/-- The `RingCat`-level morphism of presheaves of rings attached to `φ`. -/
noncomputable abbrev toRingHom' :
    (S ⋙ forget₂ CommRingCat RingCat) ⟶ F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

noncomputable instance pushforwardLaxMonoidal :
    (pushforward.{u} (toRingHom' φ)).LaxMonoidal :=
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙
    restrictScalars (toRingHom (T := F.op ⋙ R) φ)).LaxMonoidal)

noncomputable instance pullbackOplaxMonoidal :
    (pullback.{u} (toRingHom' φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (toRingHom' φ)).leftAdjointOplaxMonoidal

instance pullbackPreservesColimits :
    PreservesColimitsOfSize.{u, u} (pullback.{u} (toRingHom' φ)) :=
  (pullbackPushforwardAdjunction.{u} (toRingHom' φ)).leftAdjoint_preservesColimits

open Functor.OplaxMonoidal MonoidalCategory in
/-- `δ` of the pullback, as a natural transformation in the FIRST variable. -/
noncomputable def deltaNatLeft (Q : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorRight Q ⋙ pullback.{u} (toRingHom' φ)) ⟶
      (pullback.{u} (toRingHom' φ) ⋙ tensorRight ((pullback.{u} (toRingHom' φ)).obj Q)) where
  app P := δ (pullback.{u} (toRingHom' φ)) P Q
  naturality _ _ f := (δ_natural_left _ f Q).symm

open Functor.OplaxMonoidal MonoidalCategory in
/-- `δ` of the pullback, as a natural transformation in the SECOND variable. -/
noncomputable def deltaNatRight (P : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorLeft P ⋙ pullback.{u} (toRingHom' φ)) ⟶
      (pullback.{u} (toRingHom' φ) ⋙ tensorLeft ((pullback.{u} (toRingHom' φ)).obj P)) where
  app Q := δ (pullback.{u} (toRingHom' φ)) P Q
  naturality _ _ f := (δ_natural_right _ P f).symm

end Pushforward

end PresheafOfModules

section Generators

open PresheafOfModules

universe w

/-- A natural transformation between two colimit-preserving functors out of a category of
presheaves of modules is an isomorphism as soon as it is one on the free presheaves of modules
on representable presheaves of types. -/
lemma isIso_app_of_freeYoneda {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {𝒟 : Type w} [Category.{u} 𝒟] {L L' : PresheafOfModules.{u} R ⥤ 𝒟}
    (τ : L ⟶ L')
    [PreservesColimitsOfSize.{u, u} L] [PreservesColimitsOfSize.{u, u} L']
    (h : ∀ (X : C), IsIso (τ.app ((free R).obj (yoneda.obj X))))
    (M : PresheafOfModules.{u} R) : IsIso (τ.app M) := by
  have hcop : ∀ (N : PresheafOfModules.{u} R), IsIso (τ.app N.freeYonedaCoproduct) := by
    intro N
    haveI : IsIso (Functor.whiskerLeft
        (Discrete.functor (Elements.freeYoneda (M := N))) τ) := by
      rw [NatTrans.isIso_iff_isIso_app]
      rintro ⟨m⟩
      exact h _
    exact isIso_app_coconePt_of_preservesColimit _ τ (colimit.cocone _) (colimit.isColimit _)
  haveI : IsIso (Functor.whiskerLeft (parallelPair M.toFreeYonedaCoproduct 0) τ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro (_ | _)
    · exact hcop _
    · exact hcop _
  haveI := preservesSmallestColimits_of_preservesColimits L
  haveI := preservesSmallestColimits_of_preservesColimits L'
  exact isIso_app_coconePt_of_preservesColimit _ τ _
    M.isColimitFreeYonedaCoproductsCokernelCofork

open PresheafOfModules Functor.OplaxMonoidal MonoidalCategory in
/-- **The presheaf pullback is strong monoidal as soon as it is so on free presheaves of
modules on representables.**  This is the reduction of the leaf to its base case. -/
lemma isIso_pullback_delta {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)
    (hbase : ∀ (U U' : C), IsIso (δ (pullback.{u} (toRingHom' φ))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))))
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (δ (pullback.{u} (toRingHom' φ)) P Q) := by
  have step1 : ∀ (U : C) (Q' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      IsIso (δ (pullback.{u} (toRingHom' φ))
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) Q') := fun U Q' ↦
    isIso_app_of_freeYoneda (deltaNatRight φ _) (fun U' ↦ hbase U U') Q'
  exact isIso_app_of_freeYoneda (deltaNatLeft φ Q) (fun U ↦ step1 U Q) P

end Generators

section Scheme

open AlgebraicGeometry PresheafOfModules

noncomputable instance presheafOfModulesMonoidal (Z : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} Z.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat)))

noncomputable abbrev presheafModPullback {Z W : Scheme.{u}} (h : W ⟶ Z) :
    PresheafOfModules.{u} Z.ringCatSheaf.obj ⥤ PresheafOfModules.{u} W.ringCatSheaf.obj :=
  PresheafOfModules.pullback.{u} (Scheme.Hom.toRingCatSheafHom h).hom

example {Z W : Scheme.{u}} (h : W ⟶ Z) :
    presheafModPullback h = PresheafOfModules.pullback.{u} (toRingHom' h.c) := rfl

noncomputable instance {Z W : Scheme.{u}} (h : W ⟶ Z) :
    (presheafModPullback h).OplaxMonoidal :=
  inferInstanceAs ((PresheafOfModules.pullback.{u} (toRingHom' h.c)).OplaxMonoidal)

open Functor.OplaxMonoidal in
/-- BASE CASE (the only thing left). -/
theorem isIso_delta_freeYoneda {Z W : Scheme.{u}} (h : W ⟶ Z) (U U' : Z.Opens) :
    IsIso (δ (presheafModPullback h)
      ((PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U))
      ((PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U'))) :=
  sorry

open Functor.OplaxMonoidal in
theorem nonempty_presheafModPullback_tensor {Z W : Scheme.{u}} (h : W ⟶ Z)
    (P Q : PresheafOfModules.{u} Z.ringCatSheaf.obj) :
    Nonempty ((presheafModPullback h).obj (P ⊗ Q) ≅
      (presheafModPullback h).obj P ⊗ (presheafModPullback h).obj Q) := by
  refine ⟨@asIso _ _ _ _ (δ (presheafModPullback h) P Q) ?_⟩
  exact isIso_pullback_delta h.c (isIso_delta_freeYoneda h) P Q

end Scheme
