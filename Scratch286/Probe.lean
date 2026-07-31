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

end Generators
