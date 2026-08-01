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

4. **`isIso_pullback_delta_freeYoneda_of_prod`** (added 2026-08-01) — the GENERATOR case,
   under the only hypothesis that makes it true: that `V` is a binary product of `U` and
   `U'` in `C` **and that `F` carries it to a binary product of `F U` and `F U'`**.  Both
   are asked for in the cheapest usable form, as bijectivity of
   `g ↦ (g ≫ ι, g ≫ ι')` on hom-sets.  Together with 3 this closes
   "the pullback of presheaves of modules is strong monoidal" whenever `F` preserves
   binary products.

**Why the product hypothesis is exactly the right one, and why `δ` is NOT invertible on
generators for an arbitrary `F`.**  For `F` collapsing two objects `x, y` of a discrete
`C` onto one object of `D`, with constant ring `k`, `(pullback M)(a) = M x ⊕ M y`, so
`pullback M ⊗ pullback N` has four summands where `pullback (M ⊗ N)` has two — and that
`F` does not preserve the (empty) products in sight.  What makes the generator case true
is the sectionwise identity
`free (yoneda U) ⊗ free (yoneda U') ≅ free (yoneda V)` for `V = U ⨯ U'`, which holds on
BOTH sides once `F V = F U ⨯ F U'`, so the two answers agree.  On a site of opens both
hypotheses are free, `U ⊓ U'` being the product and `Opens.map` preserving binary meets —
see `Fermat.isIso_presheafModPullback_delta_freeYoneda` in
`Fermat/FLT/ModularCurve/RelativePicard.lean`.

**The route, since none of it is a formal consequence of the adjunction.**  Write
`L := pullback φ`, `Pf := pushforward φ`, `adj : L ⊣ Pf`.  `δ` cannot be computed on
elements — `pullback` is a partial left adjoint and has no formula — so everything goes
through the TRANSPOSE `adj.homEquiv δ = (unit ⊗ₘ unit) ≫ μ Pf`, which can.  Then
`isIso_of_coyoneda_map_bijective` reduces invertibility of `δ` to bijectivity of
`g ↦ δ ≫ g` on every `N`, `Adjunction.homEquiv_naturality_right` turns that into
`g ↦ (adj.homEquiv δ) ≫ Pf.map g`, and `freeYonedaEquiv` identifies BOTH hom-sets with
`N.obj (op (F V))`.  What is left is a single element identity
(`freeYonedaEquiv_homEquiv_delta`) that does not mention `N` at all.
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

namespace PresheafOfModules

open Opposite PresheafOfModules.Monoidal

section FreeYoneda

variable {C : Type u} [SmallCategory C]

/-- A morphism of presheaves of modules all of whose components are isomorphisms is an
isomorphism.  (`PresheafOfModules.isoMk` builds the inverse; the point is only that the
naturality obligation is the given morphism's own.) -/
lemma isIso_of_isIso_app {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{u} R}
    (f : M₁ ⟶ M₂) (h : ∀ X, IsIso (f.app X)) : IsIso f :=
  -- NOT a `have`: that would forget the value of `e` and break `e.hom = f` (see CLAUDE.md).
  letI e : M₁ ≅ M₂ :=
    isoMk (fun X => @asIso _ _ _ _ (f.app X) (h X)) (fun _ _ g => f.naturality g)
  ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

set_option backward.isDefEq.respectTransparency false in
/-- The transition maps of `(free R).obj (yoneda.obj Z)` on generators. -/
lemma freeObj_yoneda_map_freeMk {R : Cᵒᵖ ⥤ RingCat.{u}} {X Y Z : C} (g : X ⟶ Y) (s : Y ⟶ Z) :
    ((free R).obj (yoneda.obj Z)).map g.op (ModuleCat.freeMk s) = ModuleCat.freeMk (g ≫ s) := by
  simp [free]
  erw [ModuleCat.freeDesc_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `freeYonedaEquiv.symm c` evaluated at a general generator `freeMk g`, not merely at
`freeMk (𝟙 _)` as in mathlib's `freeYonedaEquiv_symm_app`. -/
lemma freeYonedaEquiv_symm_app_freeMk {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{u} R}
    {X Y : C} (c : M.obj (op X)) (g : Y ⟶ X) :
    (freeYonedaEquiv.symm c).app (op Y) (ModuleCat.freeMk g) = M.map g.op c := by
  simp [freeYonedaEquiv, freeHomEquiv, yonedaEquiv, freeObjDesc]
  erw [ModuleCat.freeDesc_apply]
  rfl

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {U U' V : C} (ι : V ⟶ U) (ι' : V ⟶ U')

/-- The comparison `free (yoneda V) ⟶ free (yoneda U) ⊗ free (yoneda U')` attached to a
cone `(ι, ι')`: the generator of the source goes to `freeMk ι ⊗ₜ freeMk ι'`. -/
noncomputable def freeYonedaTensorHom :
    (free (S ⋙ forget₂ _ _)).obj (yoneda.obj V) ⟶
      (free (S ⋙ forget₂ _ _)).obj (yoneda.obj U) ⊗
        (free (S ⋙ forget₂ _ _)).obj (yoneda.obj U') :=
  freeYonedaEquiv.symm (ModuleCat.freeMk ι ⊗ₜ ModuleCat.freeMk ι')

set_option backward.isDefEq.respectTransparency false in
lemma freeYonedaTensorHom_app_freeMk (X : C) (g : X ⟶ V) :
    (freeYonedaTensorHom (S := S) ι ι').app (op X) (ModuleCat.freeMk g) =
      ModuleCat.freeMk (g ≫ ι) ⊗ₜ ModuleCat.freeMk (g ≫ ι') := by
  rw [freeYonedaTensorHom, freeYonedaEquiv_symm_app_freeMk]
  erw [tensorObj_map_tmul]
  rw [freeObj_yoneda_map_freeMk, freeObj_yoneda_map_freeMk]
  rfl

variable (hprod : ∀ X : C, Function.Bijective (fun g : X ⟶ V => (g ≫ ι, g ≫ ι')))

include hprod in
set_option backward.isDefEq.respectTransparency false in
/-- **`free (yoneda −)` carries a binary product to a tensor product.**  Sectionwise this
is `ModuleCat.FreeMonoidal.μIso` — the free-module functor `Type u ⥤ ModuleCat R` is
already monoidal in mathlib — composed with `free` of the product bijection, so no
`Finsupp` combinatorics is needed. -/
lemma isIso_freeYonedaTensorHom : IsIso (freeYonedaTensorHom (S := S) ι ι') := by
  refine isIso_of_isIso_app _ (fun X => ?_)
  obtain ⟨Y₀⟩ := X
  haveI : IsIso (↾(fun g : Y₀ ⟶ V => (g ≫ ι, g ≫ ι'))) :=
    (bijective_iff_isIso_ofHom _).1 (hprod Y₀)
  have key : (freeYonedaTensorHom (S := S) ι ι').app (op Y₀) ≫
      (ModuleCat.FreeMonoidal.μIso ((S ⋙ forget₂ CommRingCat RingCat).obj (op Y₀))
        ((yoneda.obj U).obj (op Y₀)) ((yoneda.obj U').obj (op Y₀))).hom =
      (ModuleCat.free ((S ⋙ forget₂ CommRingCat RingCat).obj (op Y₀))).map
        (↾(fun g : Y₀ ⟶ V => (g ≫ ι, g ≫ ι'))) := by
    refine ModuleCat.free_hom_ext (fun g => ?_)
    show (ModuleCat.FreeMonoidal.μIso _ _ _).hom
      ((freeYonedaTensorHom (S := S) ι ι').app (op Y₀) (ModuleCat.freeMk g)) = _
    rw [freeYonedaTensorHom_app_freeMk,
      ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk]
    erw [ModuleCat.free_map_apply]
    rfl
  haveI : IsIso ((freeYonedaTensorHom (S := S) ι ι').app (op Y₀) ≫
      (ModuleCat.FreeMonoidal.μIso ((S ⋙ forget₂ CommRingCat RingCat).obj (op Y₀))
        ((yoneda.obj U).obj (op Y₀)) ((yoneda.obj U').obj (op Y₀))).hom) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right _
    (ModuleCat.FreeMonoidal.μIso ((S ⋙ forget₂ CommRingCat RingCat).obj (op Y₀))
      ((yoneda.obj U).obj (op Y₀)) ((yoneda.obj U').obj (op Y₀))).hom

end FreeYoneda

section PullbackFreeYoneda

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The image of `freeMk (𝟙 U)` under the unit of `pullback φ ⊣ pushforward φ`, read as a
section of `(pullback φ) (free S (yoneda U))` over `F U` — the two types agree on the
nose, `pushforward` being precomposition with `F.op` followed by restriction of scalars. -/
noncomputable def pullbackFreeYonedaElt (U : C) :
    ((pullback.{u} φ).obj ((free S).obj (yoneda.obj U))).obj (op (F.obj U)) :=
  freeYonedaEquiv
    (M := (pushforward.{u} φ).obj ((pullback.{u} φ).obj ((free S).obj (yoneda.obj U))))
    (X := U)
    ((pullbackPushforwardAdjunction.{u} φ).unit.app ((free S).obj (yoneda.obj U)))

/-- The comparison map `free R (yoneda (F U)) ⟶ (pullback φ) (free S (yoneda U))`.  It is
an isomorphism (`isIso_pullbackFreeYonedaHom`); this is the content of mathlib's
`pushforwardCompCoyonedaFreeYonedaCorepresentableBy`, but produced as an explicit map
rather than through `CorepresentableBy.uniqueUpToIso`, because the explicit formula is
what the generator case below has to compute with. -/
noncomputable def pullbackFreeYonedaHom (U : C) :
    (free R).obj (yoneda.obj (F.obj U)) ⟶
      (pullback.{u} φ).obj ((free S).obj (yoneda.obj U)) :=
  freeYonedaEquiv.symm (pullbackFreeYonedaElt φ U)

lemma freeYonedaEquiv_pullbackFreeYonedaHom_comp (U : C) (N : PresheafOfModules.{u} R)
    (g : (pullback.{u} φ).obj ((free S).obj (yoneda.obj U)) ⟶ N) :
    freeYonedaEquiv (pullbackFreeYonedaHom φ U ≫ g) =
      freeYonedaEquiv (M := (pushforward.{u} φ).obj N) (X := U)
        ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ g) := by
  rw [freeYonedaEquiv_comp, pullbackFreeYonedaHom, Equiv.apply_symm_apply,
    pullbackFreeYonedaElt, Adjunction.homEquiv_unit, freeYonedaEquiv_comp]
  rfl

/-- **The pullback of a free presheaf of modules on a representable is free on the image
representable.**  Both `(free R).obj (yoneda.obj (F.obj U))` and
`(pullback φ).obj ((free S).obj (yoneda.obj U))` corepresent `N ↦ N.obj (op (F.obj U))`,
and `pullbackFreeYonedaHom` is the induced map. -/
instance isIso_pullbackFreeYonedaHom (U : C) : IsIso (pullbackFreeYonedaHom φ U) := by
  refine isIso_of_coyoneda_map_bijective _ (fun N => ?_)
  have : (fun (g : (pullback.{u} φ).obj ((free S).obj (yoneda.obj U)) ⟶ N) =>
      freeYonedaEquiv (pullbackFreeYonedaHom φ U ≫ g)) =
        ⇑(((pullbackPushforwardAdjunction.{u} φ).homEquiv _ N).trans
          (freeYonedaEquiv (M := (pushforward.{u} φ).obj N) (X := U))) := by
    funext g
    exact freeYonedaEquiv_pullbackFreeYonedaHom_comp φ U N g
  have hb : Function.Bijective (fun (g : (pullback.{u} φ).obj ((free S).obj (yoneda.obj U)) ⟶ N) =>
      freeYonedaEquiv (pullbackFreeYonedaHom φ U ≫ g)) := by
    rw [this]; exact Equiv.bijective _
  exact (Equiv.comp_bijective _ freeYonedaEquiv).mp hb

end PullbackFreeYoneda

/-- In a THIN category (a preorder), a cone `(h1, h2)` over `U, U'` with vertex `V` is a
binary product as soon as every pair of maps into `U` and `U'` factors through `V` at all:
injectivity is free from thinness, and no compatibility has to be checked.  This is how
both product hypotheses of `isIso_pullback_delta_freeYoneda_of_prod` are discharged on a
site of opens. -/
lemma bijective_hom_of_thin {P : Type u} [Preorder P] {U U' V : P}
    (h1 : V ⟶ U) (h2 : V ⟶ U') (hinf : ∀ W : P, (W ⟶ U) → (W ⟶ U') → (W ⟶ V)) (W : P) :
    Function.Bijective (fun g : W ⟶ V => (g ≫ h1, g ≫ h2)) := by
  refine ⟨fun a b _ => Subsingleton.elim _ _, ?_⟩
  rintro ⟨a, b⟩
  exact ⟨hinf W a b, Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

/-- Precomposition with an isomorphism, as an equivalence of hom-sets.

Mathlib's `Iso.homCongr e (Iso.refl _)` is the same map up to a trailing `≫ 𝟙`, which is
enough to break the `rfl`s the proof below relies on; hence the private copy. -/
def precompHomEquiv {𝒜 : Type*} [Category* 𝒜] {X X' Y : 𝒜} (e : X ≅ X') :
    (X' ⟶ Y) ≃ (X ⟶ Y) where
  toFun g := e.hom ≫ g
  invFun f := e.inv ≫ f
  left_inv g := by simp
  right_inv f := by simp

section GeneratorCase

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

set_option backward.isDefEq.respectTransparency false in
/-- **The tensorator of `pushforward φ` is the identity on elements.**  `pushforward₀` is
strong monoidal with `μIso _ _ = Iso.refl _` (mathlib's `PushforwardZeroMonoidal`), so the
whole of `μ (pushforward φ)` is `ModuleCat.restrictScalars`'s tensorator, i.e. the
base-change comparison `m₁ ⊗_{S X} m₂ ↦ m₁ ⊗_{R (F X)} m₂`. -/
lemma pushforward_μ_app_tmul
    (A B : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (X : Cᵒᵖ)
    (a : ((pushforward.{u} (ringCatHomOfCommRingCatHom φ)).obj A).obj X)
    (b : ((pushforward.{u} (ringCatHomOfCommRingCatHom φ)).obj B).obj X) :
    (μ (pushforward.{u} (ringCatHomOfCommRingCatHom φ)) A B).app X (a ⊗ₜ b) =
      (a ⊗ₜ b : (A ⊗ B).obj (F.op.obj X)) := by
  show ((μ (restrictScalars (commRingCatToRingCatHom (T := F.op ⋙ R) φ))
      ((pushforward₀OfCommRingCat F R).obj A) ((pushforward₀OfCommRingCat F R).obj B) ≫
    (restrictScalars (commRingCatToRingCatHom (T := F.op ⋙ R) φ)).map
      (μ (pushforward₀OfCommRingCat F R) A B)).app X) (a ⊗ₜ b) = _
  rw [comp_app]
  show _ = _
  erw [ModuleCat.restrictScalars_μ_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The unit of `pullback ⊣ pushforward` on a general generator `freeMk j`, by naturality
from its value `pullbackFreeYonedaElt` at `freeMk (𝟙 U)`. -/
lemma pullbackPushforwardAdjunction_unit_app_freeMk (U : C) {W : C} (j : W ⟶ U) :
    ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))).app (op W)
      (ModuleCat.freeMk j) =
    (((pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))).map (F.map j).op
      (pullbackFreeYonedaElt (ringCatHomOfCommRingCatHom φ) U)) := by
  have h := naturality_apply
    ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))) j.op
    (ModuleCat.freeMk (𝟙 U))
  -- `(𝟭 _).obj` is `rfl`-equal to the bare object and NOT syntactically equal to it.
  simp only [Functor.id_obj] at h
  rw [freeObj_yoneda_map_freeMk, Category.comp_id] at h
  exact h

variable {U U' V : C} (ι : V ⟶ U) (ι' : V ⟶ U')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **THE ELEMENT IDENTITY THE GENERATOR CASE COMES DOWN TO**, and the only step in which
anything is computed.  Transposing `δ` across the adjunction turns it into
`(unit ⊗ₘ unit) ≫ μ (pushforward φ)`, which — unlike `δ` — evaluates on elements; both
sides are then `(pullback φ (free S (yoneda U))).map (F.map ι).op (unit's value at 𝟙 U)`
tensored with its `U'` counterpart, so the identity holds essentially by `rfl`. -/
lemma freeYonedaEquiv_homEquiv_delta :
    freeYonedaEquiv (M := (pushforward.{u} (ringCatHomOfCommRingCatHom φ)).obj
        ((pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗
        (pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U')))) (X := V)
      (freeYonedaTensorHom (S := S) ι ι' ≫
        (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).homEquiv _ _
          (Functor.OplaxMonoidal.δ (pullback.{u} (ringCatHomOfCommRingCatHom φ))
            ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
            ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U')))) =
    freeYonedaEquiv (X := F.obj V)
      (freeYonedaTensorHom (S := R) (F.map ι) (F.map ι') ≫
        (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U ⊗ₘ
          pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U')) := by
  rw [freeYonedaEquiv_comp, freeYonedaEquiv_comp]
  rw [show (freeYonedaEquiv (freeYonedaTensorHom (S := S) ι ι')) =
      ModuleCat.freeMk ι ⊗ₜ ModuleCat.freeMk ι' from Equiv.apply_symm_apply _ _]
  rw [show (freeYonedaEquiv (freeYonedaTensorHom (S := R) (F.map ι) (F.map ι'))) =
      ModuleCat.freeMk (F.map ι) ⊗ₜ ModuleCat.freeMk (F.map ι') from Equiv.apply_symm_apply _ _]
  rw [show ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).homEquiv _ _
        (Functor.OplaxMonoidal.δ (pullback.{u} (ringCatHomOfCommRingCatHom φ))
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U')))) =
      ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗ₘ
        (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))) ≫
      μ (pushforward.{u} (ringCatHomOfCommRingCatHom φ)) _ _ from Equiv.apply_symm_apply _ _]
  rw [comp_app]
  show (μ (pushforward.{u} (ringCatHomOfCommRingCatHom φ)) _ _).app (op V)
      ((((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗ₘ
        (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
          ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))).app (op V))
        (ModuleCat.freeMk ι ⊗ₜ ModuleCat.freeMk ι')) = _
  -- `Monoidal.tensorHom_app` and `ModuleCat.MonoidalCategory.tensorHom_tmul` are both
  -- `rfl`, but `rw`/`erw` pick the wrong instantiation here; spell the step out.
  rw [show (((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗ₘ
      (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))).app (op V))
        (ModuleCat.freeMk ι ⊗ₜ ModuleCat.freeMk ι') =
      ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))).app (op V)
          (ModuleCat.freeMk ι) ⊗ₜ
      ((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).unit.app
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))).app (op V)
          (ModuleCat.freeMk ι') from rfl]
  rw [pullbackPushforwardAdjunction_unit_app_freeMk,
    pullbackPushforwardAdjunction_unit_app_freeMk, pushforward_μ_app_tmul]
  rw [show ((pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U ⊗ₘ
        pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U').app (op (F.obj V)))
        (ModuleCat.freeMk (F.map ι) ⊗ₜ ModuleCat.freeMk (F.map ι')) =
      (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U).app (op (F.obj V))
          (ModuleCat.freeMk (F.map ι)) ⊗ₜ
      (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U').app (op (F.obj V))
          (ModuleCat.freeMk (F.map ι')) from rfl]
  rw [pullbackFreeYonedaHom, pullbackFreeYonedaHom,
    freeYonedaEquiv_symm_app_freeMk, freeYonedaEquiv_symm_app_freeMk]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **THE GENERATOR CASE OF "THE PULLBACK OF PRESHEAVES OF MODULES IS STRONG MONOIDAL"**:
`δ` is invertible on `free (yoneda U)` and `free (yoneda U')` as soon as `U` and `U'` have
a binary product `V` in `C` which `F` carries to a binary product of `F U` and `F U'`.

Both hypotheses are stated as bijectivity of `g ↦ (g ≫ ι, g ≫ ι')`, which is what a
binary product is and which is what a thin site supplies for free
(`bijective_hom_of_thin`).  With `isIso_pullback_delta` this gives strong monoidality of
`pullback φ` outright whenever `F` preserves binary products. -/
theorem isIso_pullback_delta_freeYoneda_of_prod
    (hprod : ∀ X : C, Function.Bijective (fun g : X ⟶ V => (g ≫ ι, g ≫ ι')))
    (hprodF : ∀ Y : D, Function.Bijective
      (fun g : Y ⟶ F.obj V => (g ≫ F.map ι, g ≫ F.map ι'))) :
    IsIso (Functor.OplaxMonoidal.δ (pullback.{u} (ringCatHomOfCommRingCatHom φ))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))) := by
  haveI hZ : IsIso (freeYonedaTensorHom (S := S) ι ι') := isIso_freeYonedaTensorHom ι ι' hprod
  haveI hW : IsIso (freeYonedaTensorHom (S := R) (F.map ι) (F.map ι')) :=
    isIso_freeYonedaTensorHom _ _ hprodF
  haveI hβ : IsIso (freeYonedaTensorHom (S := R) (F.map ι) (F.map ι') ≫
      (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U ⊗ₘ
        pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U')) := inferInstance
  refine isIso_of_coyoneda_map_bijective _ (fun N => ?_)
  -- Both hom-sets are identified with `N.obj (op (F V))`, the first across the adjunction.
  have hΨ : Function.Bijective (fun h : (pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
      (((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U'))) ⟶ N =>
      show N.obj (op (F.obj V)) from
        freeYonedaEquiv (M := (pushforward.{u} (ringCatHomOfCommRingCatHom φ)).obj N) (X := V)
          (freeYonedaTensorHom (S := S) ι ι' ≫
            (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).homEquiv _ _ h)) :=
    Equiv.bijective
      (((pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).homEquiv _ N).trans
        ((precompHomEquiv (asIso (freeYonedaTensorHom (S := S) ι ι'))).trans freeYonedaEquiv))
  have hΦ : Function.Bijective (fun g : (pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U)) ⊗
      (pullback.{u} (ringCatHomOfCommRingCatHom φ)).obj
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U')) ⟶ N =>
      freeYonedaEquiv (M := N) (X := F.obj V)
        ((freeYonedaTensorHom (S := R) (F.map ι) (F.map ι') ≫
          (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U ⊗ₘ
            pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U')) ≫ g)) :=
    Equiv.bijective
      ((precompHomEquiv (asIso (freeYonedaTensorHom (S := R) (F.map ι) (F.map ι') ≫
        (pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U ⊗ₘ
          pullbackFreeYonedaHom (ringCatHomOfCommRingCatHom φ) U')))).trans freeYonedaEquiv)
  refine (hΨ.of_comp_iff' _).mp ?_
  convert hΦ using 2 with g
  show freeYonedaEquiv (freeYonedaTensorHom (S := S) ι ι' ≫
      (pullbackPushforwardAdjunction.{u} (ringCatHomOfCommRingCatHom φ)).homEquiv _ _ (_ ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right, ← Category.assoc, freeYonedaEquiv_comp,
    freeYonedaEquiv_comp]
  exact congrArg _ (freeYonedaEquiv_homEquiv_delta φ ι ι')

end GeneratorCase

end PresheafOfModules
