/-
Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean — own work for the
Fermat project (not vendored from the FLT project).

# Monoidality of the pullback of PRESHEAVES of modules

Let `F : C ⥤ D` be a functor between small categories, `R : Dᵒᵖ ⥤ CommRingCat`,
`S : Cᵒᵖ ⥤ CommRingCat` presheaves of commutative rings, and `φ : S ⟶ F.op ⋙ R` a
morphism of presheaves of rings.  Mathlib gives
`PresheafOfModules.pullback φ : PresheafOfModules S ⥤ PresheafOfModules R` as the left
adjoint of `PresheafOfModules.pushforward φ`, and gives a monoidal structure on each
category of presheaves of modules — but says nothing about how the two interact.

This module supplies the interaction, in three steps.

1. **`PresheafOfModules.restrictScalarsLaxMonoidal`** — restriction of scalars along a
   morphism of presheaves of *commutative* rings is LAX monoidal.  Everything in sight
   is sectionwise (`PresheafOfModules.Monoidal` defines `⊗` object-by-object and mathlib
   proves `tensorHom_app`, `associator_hom_app`, … are the `ModuleCat` ones), so the
   whole structure is transported from `ModuleCat.instLaxMonoidalRestrictScalars`.

2. **`PresheafOfModules.pullbackOplaxMonoidal`** — hence `pushforward φ` is lax monoidal
   (it is `pushforward₀OfCommRingCat`, which mathlib knows is *strong* monoidal, followed
   by `restrictScalars`), hence its left adjoint `pullback φ` is OPLAX monoidal by
   `Adjunction.leftAdjointOplaxMonoidal`.  This produces the canonical comparison
   `δ (pullback φ) P Q : (pullback φ).obj (P ⊗ Q) ⟶ (pullback φ).obj P ⊗ (pullback φ).obj Q`,
   natural in both variables.

3. **`isIso_pullback_delta`** — `δ` is invertible everywhere as soon as it is invertible on
   the free presheaves of modules on representables.  This is a two-variable dévissage:
   `- ⊗ Q` and `P ⊗ -` preserve colimits (mathlib instances on `tensorLeft`/`tensorRight`),
   `pullback φ` preserves colimits (left adjoint), and every presheaf of modules is a
   cokernel of a map between coproducts of `(free S).obj (yoneda.obj X)`
   (`PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork`).

**What is NOT here, and why.**  `δ` is *not* invertible on generators for an arbitrary
`F`: for `F` collapsing two objects `x, y` of a discrete `C` onto one object of `D`, with
constant ring `k`, `(pullback M)(a) = M x ⊕ M y`, so `pullback M ⊗ pullback N` has four
summands where `pullback (M ⊗ N)` has two.  What makes the generator case true on a site
of opens is that `Opens.map` preserves binary meets, so that
`free (yoneda U) ⊗ free (yoneda U') ≅ free (yoneda (U ⊓ U'))` on BOTH sides and the two
answers agree.  That is a hypothesis about the site, and it is supplied by the caller —
see `Fermat.isIso_presheafModPullback_delta_freeYoneda` in
`Fermat/FLT/ModularCurve/RelativePicard.lean`.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Functor

@[expose] public section

universe u w

open CategoryTheory Limits MonoidalCategory Functor Functor.LaxMonoidal

namespace PresheafOfModules

open PresheafOfModules.Monoidal

section RestrictScalars

variable {C : Type u} [SmallCategory C] {S T : Cᵒᵖ ⥤ CommRingCat.{u}} (α : S ⟶ T)

/-- The morphism of presheaves of `RingCat`-rings underlying a morphism of presheaves of
commutative rings. -/
noncomputable abbrev commRingCatToRingCatHom :
    (S ⋙ forget₂ CommRingCat RingCat) ⟶ (T ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
/-- The tensorator `μ` for restriction of scalars of presheaves of modules: sectionwise,
mathlib's `μ (ModuleCat.restrictScalars _)`, i.e. `m₁ ⊗ₜ m₂ ↦ m₁ ⊗ₜ m₂`. -/
noncomputable def restrictScalarsMu (A B : PresheafOfModules.{u} (T ⋙ forget₂ _ _)) :
    (restrictScalars (commRingCatToRingCatHom α)).obj A ⊗
        (restrictScalars (commRingCatToRingCatHom α)).obj B ⟶
      (restrictScalars (commRingCatToRingCatHom α)).obj (A ⊗ B) where
  app X := μ (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
    (A.obj X) (B.obj X)
  naturality {X Y} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    dsimp
    erw [tensorObj_map_tmul, ModuleCat.restrictScalars_μ_tmul,
      ModuleCat.restrictScalars_μ_tmul, tensorObj_map_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit `ε` for restriction of scalars of presheaves of modules: sectionwise `α`. -/
noncomputable def restrictScalarsEps :
    𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ⟶
      (restrictScalars (commRingCatToRingCatHom α)).obj
        (𝟙_ (PresheafOfModules.{u} (T ⋙ forget₂ _ _))) where
  app X := ε (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
  naturality {X Y} f := by
    ext
    dsimp
    erw [unit_map_one, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
    rw [map_one, map_one]
    exact (unit_map_one (R := T ⋙ forget₂ CommRingCat RingCat) f).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Restriction of scalars of presheaves of modules is lax monoidal.**

Every coherence condition is checked one section at a time, where it is mathlib's
`ModuleCat.instLaxMonoidalRestrictScalars`. -/
noncomputable instance restrictScalarsLaxMonoidal :
    (restrictScalars (commRingCatToRingCatHom α)).LaxMonoidal where
  ε := restrictScalarsEps α
  μ A B := restrictScalarsMu α A B
  μ_natural_left f X' := by
    ext1 X
    exact μ_natural_left (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
      (f.app X) (X'.obj X)
  μ_natural_right X' f := by
    ext1 X
    exact μ_natural_right (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
      (X'.obj X) (f.app X)
  associativity A B D := by
    ext1 X
    exact associativity (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
      (A.obj X) (B.obj X) (D.obj X)
  left_unitality A := by
    ext1 X
    exact left_unitality (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
      (A.obj X)
  right_unitality A := by
    ext1 X
    exact right_unitality (ModuleCat.restrictScalars ((commRingCatToRingCatHom α).app X).hom)
      (A.obj X)

end RestrictScalars

section Pullback

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The `RingCat`-level morphism of presheaves of rings attached to a morphism `φ` of
presheaves of commutative rings.  This is the shape `PresheafOfModules.pullback` wants. -/
noncomputable abbrev ringCatHomOfCommRingCatHom :
    (S ⋙ forget₂ CommRingCat RingCat) ⟶ F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat) :=
  Functor.whiskerRight φ (forget₂ CommRingCat RingCat)

/-- **The pushforward of presheaves of modules is lax monoidal.**

`pushforward φ` is by definition `pushforward₀OfCommRingCat F R ⋙ restrictScalars φ`; the
first factor is strong monoidal in mathlib and the second is lax monoidal above. -/
noncomputable instance pushforwardLaxMonoidal :
    (pushforward.{u} (ringCatHomOfCommRingCatHom φ)).LaxMonoidal :=
  inferInstanceAs ((pushforward₀OfCommRingCat F R ⋙
    restrictScalars (commRingCatToRingCatHom (T := F.op ⋙ R) φ)).LaxMonoidal)

/-- **The pullback of presheaves of modules is oplax monoidal** — the left adjoint of a lax
monoidal functor.  This is where the comparison map `δ` comes from; it is NOT invertible
for a general `F` (see the module docstring). -/
noncomputable instance pullbackOplaxMonoidal :
    (pullback.{u} (ringCatHomOfCommRingCatHom φ)).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).leftAdjointOplaxMonoidal

instance pullbackPreservesColimits :
    PreservesColimitsOfSize.{u, u} (pullback.{u} (ringCatHomOfCommRingCatHom φ)) :=
  (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).leftAdjoint_preservesColimits

open Functor.OplaxMonoidal in
/-- `δ` of the pullback, read as a natural transformation in the FIRST variable. -/
noncomputable def pullbackDeltaNatLeft (Q : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorRight Q ⋙ pullback.{u} (ringCatHomOfCommRingCatHom φ)) ⟶
      (pullback.{u} (ringCatHomOfCommRingCatHom φ) ⋙
        tensorRight ((pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj Q)) where
  app P := δ (pullback.{u} (ringCatHomOfCommRingCatHom φ)) P Q
  naturality _ _ f := (δ_natural_left _ f Q).symm

open Functor.OplaxMonoidal in
/-- `δ` of the pullback, read as a natural transformation in the SECOND variable. -/
noncomputable def pullbackDeltaNatRight (P : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorLeft P ⋙ pullback.{u} (ringCatHomOfCommRingCatHom φ)) ⟶
      (pullback.{u} (ringCatHomOfCommRingCatHom φ) ⋙
        tensorLeft ((pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj P)) where
  app Q := δ (pullback.{u} (ringCatHomOfCommRingCatHom φ)) P Q
  naturality _ _ f := (δ_natural_right _ P f).symm

end Pullback

end PresheafOfModules

section Generators

open PresheafOfModules

/-- **A natural transformation between colimit-preserving functors out of a category of
presheaves of modules is invertible as soon as it is invertible on the free presheaves of
modules on representables.**

Two applications of `Limits.isIso_app_coconePt_of_preservesColimit`: first to the coproduct
`M.freeYonedaCoproduct`, then to the cokernel cofork
`M.freeYonedaCoproductsCokernelCofork`, which mathlib proves is a colimit. -/
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
/-- **The comparison `δ` for the pullback of presheaves of modules is invertible as soon as
it is invertible on free presheaves of modules on representables.**

The dévissage runs in two variables: first the second variable, with the first held at a
`free (yoneda U)`, then the first variable with the second arbitrary. -/
lemma isIso_pullback_delta {C D : Type u} [SmallCategory C] [SmallCategory D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)
    (hbase : ∀ (U U' : C), IsIso (δ (pullback.{u} (ringCatHomOfCommRingCatHom φ))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))))
    (P Q : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (δ (pullback.{u} (ringCatHomOfCommRingCatHom φ)) P Q) := by
  have step1 : ∀ (U : C) (Q' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      IsIso (δ (pullback.{u} (ringCatHomOfCommRingCatHom φ))
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) Q') := fun U Q' ↦
    isIso_app_of_freeYoneda (pullbackDeltaNatRight φ _) (fun U' ↦ hbase U U') Q'
  exact isIso_app_of_freeYoneda (pullbackDeltaNatLeft φ Q) (fun U ↦ step1 U Q) P

end Generators
