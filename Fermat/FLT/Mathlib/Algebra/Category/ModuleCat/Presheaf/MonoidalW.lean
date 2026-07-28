/-
Copyright (c) 2026 The Fermat project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Tensoring preserves local isomorphisms of presheaves of modules

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a site `(C, J)`.
The category `PresheafOfModules (R ⋙ forget₂ _ _)` is symmetric monoidal, and this
file proves that the class of morphisms which become isomorphisms after
sheafification — equivalently (mathlib's `GrothendieckTopology.WEqualsLocallyBijective`)
the LOCALLY BIJECTIVE ones — is stable under `X ⊗ -`.  This is
[Stacks 01LA]; it is what makes `MorphismProperty.IsMonoidal (J.W.inverseImage
(PresheafOfModules.toPresheaf _))` hold, and hence what puts a monoidal structure on
sheaves of modules by `CategoryTheory.LocalizedMonoidal`.

## The argument

Mathlib proves the analogous `GrothendieckTopology.W.whiskerLeft` for
`Cᵒᵖ ⥤ A` with `A` monoidal CLOSED (`Mathlib/CategoryTheory/Sites/Monoidal.lean`),
and separately for a site with enough points
(`Mathlib/CategoryTheory/Sites/Point/IsMonoidalW.lean`).  Neither applies here:
`PresheafOfModules` has no `MonoidalClosed` instance at this pin, and the
enough-points instance concerns the `ℤ`-linear tensor product of
`Cᵒᵖ ⥤ AddCommGrpCat`, not the `R`-linear one.

So the proof here is elementary and works for an arbitrary site.

* LOCAL SURJECTIVITY (`isLocallySurjective_whiskerLeft`) is an induction on
  tensors: a pure tensor `x ⊗ n` lifts wherever `n` does, and finitely many
  covering sieves may be intersected.

* LOCAL INJECTIVITY (`isLocallyInjective_whiskerLeft`) is the real content — it
  is not formal, because `X ⊗ -` is only right exact.  The input is the
  EQUATIONAL CRITERION FOR VANISHING in the form `exists_relations` below:
  if `∑ᵢ xᵢ ⊗ φ(yᵢ) = 0` in `M ⊗_R N₂` then, after enlarging the family by
  finitely many further elements of `M` paired with `0`, the vanishing is
  witnessed by an explicit finite system of relations
  `φ(qₛ) = ∑ⱼ aₛⱼ wⱼ`, `∑ₛ aₛⱼ pₛ = 0`.
  Given that, one covers `U` first so that every `wⱼ` lifts through `g` (local
  surjectivity), then further so that `qₛ - ∑ⱼ aₛⱼ vⱼ` dies (local
  injectivity); on that cover `∑ₛ pₛ ⊗ qₛ = ∑ⱼ (∑ₛ aₛⱼ pₛ) ⊗ vⱼ = 0`.

Mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` needs the `mᵢ`
to GENERATE `M`, which is exactly what is unavailable here; `exists_relations`
is the general form, proved by the same route (a free presentation of `M`
indexed by `Fin k ⊕ M`, so that no two members of the original family are
identified).
-/

@[expose] public section

open CategoryTheory Opposite MonoidalCategory Limits
open scoped TensorProduct

universe v u u₁ v₁

namespace Fermat.SheafificationMonoidal

open LinearMap Function

variable {R₀ : Type u} [CommRing R₀] {M N₁ N₂ : Type u}
  [AddCommGroup M] [Module R₀ M] [AddCommGroup N₁] [Module R₀ N₁]
  [AddCommGroup N₂] [Module R₀ N₂]

/-- **General equational criterion for vanishing.**  If `∑ᵢ xᵢ ⊗ φ(yᵢ) = 0` in
`M ⊗[R₀] N₂`, then the expression `∑ᵢ xᵢ ⊗ yᵢ` can be rewritten as `∑ₛ pₛ ⊗ qₛ`
in such a way that the vanishing is witnessed by an explicit finite system of
relations: `φ(qₛ) = ∑ⱼ aₛⱼ • wⱼ` and `∑ₛ aₛⱼ • pₛ = 0`.

This is mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` with its
hypothesis `Submodule.span R (Set.range m) = ⊤` removed — the price is that the
family `(pₛ)` is larger than `(xᵢ)`, and that the criterion is stated relative to
a linear map `φ` (which is how it gets used: `φ` is a locally bijective morphism
of presheaves of modules, evaluated on a section). -/
theorem exists_relations {k : ℕ} (x : Fin k → M) (y : Fin k → N₁) (φ : N₁ →ₗ[R₀] N₂)
    (h : ∑ i, x i ⊗ₜ[R₀] φ (y i) = (0 : M ⊗[R₀] N₂)) :
    ∃ (κ : Type u) (_ : Fintype κ) (μ : Type u) (_ : Fintype μ)
      (p : κ → M) (q : κ → N₁) (a : κ → μ → R₀) (w : μ → N₂),
      (∑ i, x i ⊗ₜ[R₀] y i = ∑ s, p s ⊗ₜ[R₀] q s) ∧
      (∀ s, φ (q s) = ∑ j, a s j • w j) ∧
      (∀ j, ∑ s, a s j • p s = 0) := by
  classical
  set I : Type u := Fin k ⊕ M with hI
  set v : I → M := Sum.elim x id with hv
  set G : (I →₀ R₀) →ₗ[R₀] M := Finsupp.linearCombination R₀ v with hG
  have hGsingle : ∀ t : I, G (Finsupp.single t (1 : R₀)) = v t := by
    intro t; simp [hG]
  have hGsurj : Surjective G := by
    intro z
    exact ⟨Finsupp.single (Sum.inr z) 1, by rw [hGsingle]; rfl⟩
  set en : (I →₀ R₀) ⊗[R₀] N₂ := ∑ i, Finsupp.single (Sum.inl i) (1 : R₀) ⊗ₜ[R₀] φ (y i) with hen
  have hker : en ∈ ker (rTensor N₂ G) := by
    simp only [mem_ker, hen, map_sum, rTensor_tmul, hGsingle]
    simpa [hv] using h
  have hexact0 : Exact (ker G).subtype G := G.exact_subtype_ker_map
  have hexact : Exact (rTensor N₂ (ker G).subtype) (rTensor N₂ G) :=
    rTensor_exact (M := ↥(ker G)) N₂ hexact0 hGsurj
  have hmem : en ∈ range (rTensor N₂ (ker G).subtype) := by
    rw [← hexact.linearMap_ker_eq]; exact hker
  obtain ⟨kn, hkn⟩ := hmem
  obtain ⟨ma, rfl⟩ := TensorProduct.exists_finset kn
  have hkn' : ∑ j ∈ ma, ((j.1 : I →₀ R₀)) ⊗ₜ[R₀] j.2 = en := by
    rw [← hkn]; simp [map_sum]
  -- the finite index set of "extra" generators
  have hcomp : ∀ t : I, ∑ j ∈ ma, ((j.1 : I →₀ R₀)) t • j.2
      = Sum.elim (fun i => φ (y i)) (fun _ => (0 : N₂)) t := by
    intro t
    have hb := congrArg (fun z => TensorProduct.finsuppScalarLeft R₀ N₂ I z t) hkn'
    simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
      TensorProduct.finsuppScalarLeft_apply_tmul_apply, hen] at hb
    rw [hb]
    cases t with
    | inl i₀ =>
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb2
        have hne : (Sum.inl b : I) ≠ Sum.inl i₀ := fun hc => hb2 (Sum.inl_injective hc)
        simp [hne]
      · simp
    | inr z => simp
  have hGapply : ∀ f : I →₀ R₀, G f = ∑ t ∈ f.support, f t • v t := by
    intro f; rw [hG, Finsupp.linearCombination_apply, Finsupp.sum]
  set T : Finset I :=
    (Finset.univ.image (Sum.inl : Fin k → I)) ∪ ma.biUnion (fun j => ((j.1 : I →₀ R₀)).support)
    with hT
  refine ⟨{t : I // t ∈ T}, inferInstance, {j : (↥(ker G) × N₂) // j ∈ ma}, inferInstance,
    fun s => v s.1, fun s => Sum.elim y (fun _ => (0 : N₁)) s.1,
    fun s j => ((j.1.1 : I →₀ R₀)) s.1, fun j => j.1.2, ?_, ?_, ?_⟩
  · rw [Finset.sum_coe_sort T (fun t => v t ⊗ₜ[R₀] Sum.elim y (fun _ => (0 : N₁)) t)]
    rw [← Finset.sum_subset (s₁ := Finset.univ.image (Sum.inl : Fin k → I)) (by
      rw [hT]; exact Finset.subset_union_left) (by
      intro t _ htn
      have : ∀ i, t ≠ Sum.inl i := by
        intro i hi; exact htn (by simp [hi])
      cases t with
      | inl i => exact absurd rfl (this i)
      | inr z => simp)]
    rw [Finset.sum_image (by intro a _ b _ h; exact Sum.inl_injective h)]
    rfl
  · intro s
    rw [Finset.sum_coe_sort ma (fun j => ((j.1 : I →₀ R₀)) s.1 • j.2)]
    rw [hcomp s.1]
    cases h' : (s.1 : I) with
    | inl i => simp [h']
    | inr z => simp [h']
  · intro j
    rw [Finset.sum_coe_sort T (fun t => ((j.1.1 : I →₀ R₀)) t • v t)]
    rw [← Finset.sum_subset (s₁ := ((j.1.1 : I →₀ R₀)).support) (by
      rw [hT]
      refine Finset.Subset.trans ?_ Finset.subset_union_right
      exact Finset.subset_biUnion_of_mem
        (fun (i : ↥(ker G) × N₂) => ((i.1 : I →₀ R₀)).support) j.2) (by
      intro t _ htn
      simp only [Finsupp.mem_support_iff, ne_eq, not_not] at htn
      simp [htn])]
    rw [← hGapply]
    exact j.1.1.2

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (J : GrothendieckTopology C)

variable {J}

lemma tensorObj_map_apply (P Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (f : U ⟶ V) (m : P.obj U) (n : Q.obj U) :
    (P ⊗ Q).map f (m ⊗ₜ n) = P.map f m ⊗ₜ Q.map f n := rfl

theorem isLocallySurjective_whiskerLeft
    (X : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {Y₁ Y₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : Y₁ ⟶ Y₂)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (X ◁ g)) where
  imageSieve_mem {U} t := by
    induction t using TensorProduct.induction_on with
    | zero =>
        refine J.superset_covering ?_ (J.top_mem U)
        rintro V h -
        exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
    | tmul x n =>
        refine J.superset_covering ?_
          (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map g) n)
        rintro V h ⟨m, hm⟩
        refine ⟨X.map h.op x ⊗ₜ m, ?_⟩
        show X.map h.op x ⊗ₜ (g.app (op V) m) = (X ⊗ Y₂).map h.op (x ⊗ₜ n)
        rw [tensorObj_map_apply]
        exact congrArg _ hm
    | add t₁ t₂ h₁ h₂ =>
        refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
        rintro V h ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩
        exact ⟨m₁ + m₂, by rw [map_add, hm₁, hm₂]; exact (map_add _ _ _).symm⟩

/-- A finite family of covering sieves is refined by a single covering sieve. -/
lemma finset_inter_mem {ι : Type*} (s : Finset ι) {U : C} (S : ι → Sieve U)
    (h : ∀ i ∈ s, S i ∈ J U) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), T f → ∀ i ∈ s, S i f := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨⊤, J.top_mem U, by simp⟩
  | insert b s hb ih =>
      obtain ⟨T, hT, hT'⟩ := ih (fun i hi => h i (by simp [hi]))
      refine ⟨S b ⊓ T, J.intersection_covering (h b (by simp)) hT, ?_⟩
      rintro V f ⟨hf1, hf2⟩ i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hf1
      · exact hT' f hf2 i hi

variable (J) in
lemma key_equalizerSieve
    (X : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {Y₁ Y₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : Y₁ ⟶ Y₂)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map g)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map g)]
    {U : C} (t : (X ⊗ Y₁).obj (op U))
    (ht : (X ◁ g).app (op U) t = 0) :
    Presheaf.equalizerSieve (F := (PresheafOfModules.toPresheaf _).obj (X ⊗ Y₁))
      (X := op U) t 0 ∈ J U := by
  classical
  obtain ⟨k, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  have ht' : LinearMap.lTensor (X.obj (op U)) (g.app (op U)).hom (∑ j, x j ⊗ₜ y j) = 0 := ht
  rw [map_sum] at ht'
  simp only [LinearMap.lTensor_tmul] at ht'
  obtain ⟨κ, hκ, μ, hμ, p, q, a, w, hsum, hφ, hrel⟩ :=
    exists_relations x y (g.app (op U)).hom ht'
  have hws : ∀ j : μ, Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g) (w j) ∈ J U :=
    fun j => Presheaf.imageSieve_mem (U := op U) J
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g) (w j)
  obtain ⟨T, hT, hT'⟩ := finset_inter_mem (J := J) (Finset.univ : Finset μ) _ (fun j _ => hws j)
  refine J.transitive hT _ ?_
  intro V f hf
  have hpre : ∀ j : μ, Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g) (w j) f :=
    fun j => hT' f hf j (Finset.mem_univ j)
  have hv0 : ∀ j : μ, ∃ vj : Y₁.obj (op V),
      (g.app (op V)).hom vj = Y₂.restrictₛₗ f.op (w j) := by
    intro j
    refine ⟨Presheaf.localPreimage ((PresheafOfModules.toPresheaf
      (R ⋙ forget₂ CommRingCat RingCat)).map g) (w j) f (hpre j), ?_⟩
    exact Presheaf.app_localPreimage ((PresheafOfModules.toPresheaf
      (R ⋙ forget₂ CommRingCat RingCat)).map g) (w j) f (hpre j)
  choose v hv using hv0
  set d : κ → Y₁.obj (op V) := fun s =>
    Y₁.restrictₛₗ f.op (q s) -
      ∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j) • v j with hddef
  have hd : ∀ s, (g.app (op V)).hom (d s) = 0 := by
    intro s
    have e1 : (g.app (op V)).hom (Y₁.restrictₛₗ f.op (q s))
        = ∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j) •
            Y₂.restrictₛₗ f.op (w j) := by
      have hnat := PresheafOfModules.naturality_apply g f.op (q s)
      have e0 : (g.app (op V)).hom (Y₁.restrictₛₗ f.op (q s))
          = Y₂.restrictₛₗ f.op ((g.app (op U)).hom (q s)) := hnat
      rw [e0, hφ s, map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_smulₛₗ (Y₂.restrictₛₗ f.op) _ _)
    have e2 : (g.app (op V)).hom
        (∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j) • v j)
        = ∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j) •
            Y₂.restrictₛₗ f.op (w j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, hv j])
    rw [hddef]
    simp only [map_sub, e1, e2, sub_self]
  obtain ⟨T2, hT2, hT2'⟩ := finset_inter_mem (J := J) (Finset.univ : Finset κ)
    (fun s => Presheaf.equalizerSieve
      (F := (PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).obj Y₁)
      (X := op V) (d s) 0)
    (fun s _ => Presheaf.equalizerSieve_mem (X := op V) J
      ((PresheafOfModules.toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g) (d s) 0
      ((hd s).trans (map_zero _).symm))
  refine J.superset_covering ?_ hT2
  intro W hw hhw
  have hzero : ∀ s : κ, Y₁.restrictₛₗ hw.op (d s) = 0 := by
    intro s
    have h1 : Y₁.restrictₛₗ hw.op (d s) = Y₁.restrictₛₗ hw.op 0 :=
      hT2' hw hhw s (Finset.mem_univ s)
    rw [h1, map_zero]
  have hopcomp : (hw ≫ f).op = f.op ≫ hw.op := rfl
  have hq : ∀ s, Y₁.restrictₛₗ (hw ≫ f).op (q s)
      = ∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map (hw ≫ f).op).hom (a s j) •
          Y₁.restrictₛₗ hw.op (v j) := by
    intro s
    have h3 : Y₁.restrictₛₗ (hw ≫ f).op (q s)
        = Y₁.restrictₛₗ hw.op (Y₁.restrictₛₗ f.op (q s)) := by
      simp only [PresheafOfModules.restrictₛₗ_apply]
      exact PresheafOfModules.map_comp_apply Y₁ f.op hw.op (q s)
    have h5 : Y₁.restrictₛₗ hw.op (Y₁.restrictₛₗ f.op (q s))
        = Y₁.restrictₛₗ hw.op
            (∑ j, ((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j) • v j) := by
      have h6 := hzero s
      simp only [hddef] at h6
      rw [map_sub, sub_eq_zero] at h6
      exact h6
    rw [h3, h5, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smulₛₗ]
    congr 1
    have hfun : ((R ⋙ forget₂ CommRingCat RingCat).map (hw ≫ f).op).hom (a s j)
        = ((R ⋙ forget₂ CommRingCat RingCat).map hw.op).hom
            (((R ⋙ forget₂ CommRingCat RingCat).map f.op).hom (a s j)) := by
      rw [hopcomp, Functor.map_comp]
      rfl
    rw [hfun]
  have hmain : (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (∑ i, x i ⊗ₜ y i) = 0 := by
    have hcong : (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (∑ i, x i ⊗ₜ y i)
        = (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (∑ s, p s ⊗ₜ q s) :=
      congrArg (fun z => (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op z) hsum
    have hms : (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (∑ s, p s ⊗ₜ q s)
        = ∑ s, (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (p s ⊗ₜ q s) :=
      map_sum ((X ⊗ Y₁).restrictₛₗ (hw ≫ f).op) _ _
    have hstep : (X ⊗ Y₁).restrictₛₗ (hw ≫ f).op (∑ i, x i ⊗ₜ y i)
        = ∑ s, (X.restrictₛₗ (hw ≫ f).op (p s)) ⊗ₜ (Y₁.restrictₛₗ (hw ≫ f).op (q s)) :=
      hcong.trans (hms.trans (Finset.sum_congr rfl (fun s _ => rfl)))
    rw [hstep]
    calc ∑ s, (X.restrictₛₗ (hw ≫ f).op (p s)) ⊗ₜ[_] (Y₁.restrictₛₗ (hw ≫ f).op (q s))
        = ∑ s, ∑ j, (((R ⋙ forget₂ CommRingCat RingCat).map (hw ≫ f).op).hom (a s j) •
            X.restrictₛₗ (hw ≫ f).op (p s)) ⊗ₜ (Y₁.restrictₛₗ hw.op (v j)) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [hq s, TensorProduct.tmul_sum]
          exact Finset.sum_congr rfl (fun j _ => by
            rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul'])
      _ = ∑ j, (∑ s, ((R ⋙ forget₂ CommRingCat RingCat).map (hw ≫ f).op).hom (a s j) •
            X.restrictₛₗ (hw ≫ f).op (p s)) ⊗ₜ (Y₁.restrictₛₗ hw.op (v j)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun j _ => (TensorProduct.sum_tmul _ _ _).symm)
      _ = 0 := by
          refine Finset.sum_eq_zero (fun j _ => ?_)
          have hz : ∑ s, ((R ⋙ forget₂ CommRingCat RingCat).map (hw ≫ f).op).hom (a s j) •
              X.restrictₛₗ (hw ≫ f).op (p s)
              = X.restrictₛₗ (hw ≫ f).op (∑ s, a s j • p s) := by
            rw [map_sum]
            exact Finset.sum_congr rfl (fun s _ => (map_smulₛₗ _ _ _).symm)
          rw [hz, hrel j, map_zero, TensorProduct.zero_tmul]
  exact hmain.trans (map_zero _).symm

theorem isLocallyInjective_whiskerLeft
    (X : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {Y₁ Y₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : Y₁ ⟶ Y₂)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map g)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map (X ◁ g)) where
  equalizerSieve_mem {U} t₁ t₂ h := by
    let u₁ : (X ⊗ Y₁).obj U := t₁
    let u₂ : (X ⊗ Y₁).obj U := t₂
    have h' : (X ◁ g).app U u₁ = (X ◁ g).app U u₂ := h
    have hsub : (X ◁ g).app U (u₁ - u₂) = 0 := by
      rw [map_sub, h', sub_self]
    have hkey := key_equalizerSieve J X g (U := U.unop) (u₁ - u₂) hsub
    refine J.superset_covering ?_ hkey
    intro V f hf
    have hf' : (X ⊗ Y₁).restrictₛₗ f.op (u₁ - u₂) = (X ⊗ Y₁).restrictₛₗ f.op 0 := hf
    rw [map_sub, map_zero, sub_eq_zero] at hf'
    exact hf'

/-- **Tensoring preserves local isomorphisms** ([Stacks 01LA]): if `g` becomes an
isomorphism after sheafification, so does `X ◁ g`. -/
theorem W_whiskerLeft [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (X : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {Y₁ Y₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} {g : Y₁ ⟶ Y₂}
    (hg : J.W ((PresheafOfModules.toPresheaf _).map g)) :
    J.W ((PresheafOfModules.toPresheaf _).map (X ◁ g)) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hg ⊢
  obtain ⟨h₁, h₂⟩ := hg
  exact ⟨isLocallyInjective_whiskerLeft X g, isLocallySurjective_whiskerLeft X g⟩

end Fermat.SheafificationMonoidal
