/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Fermat.FLT.Mathlib.AlgebraicGeometry.InvariantQuotient

/-!
# Base change of an invariant ring extension along a FLAT extension of scalars

Let `G` be a finite group acting by `k`-algebra automorphisms on a commutative ring `A`, let
`B ⊆ A` be the invariant subring (`Algebra.IsInvariant B A G` together with injectivity of
`algebraMap B A`), and let `k → K` be a **flat** extension of scalars.  Then

* `B ⊗[k] K` is the invariant subring of `A ⊗[k] K` for the base-changed action
  (`Fermat.InvariantBaseChange.isInvariant_tensor`), and
* consequently `Spec (B ⊗[k] K)` is a categorical quotient of `Spec (A ⊗[k] K)` by `G`.

The second statement is packaged in the form the modular-curve development needs it, namely
`Fermat.InvariantBaseChange.exists_unique_of_isPullback`: the two spectra are described only by
the property of being pullbacks of `Spec A ⟶ Spec k ⟵ Spec K` and `Spec B ⟶ Spec k ⟵ Spec K`,
the quotient map and the group action only by their two projections.  So a consumer that has a
GIT presentation over `Spec k` and a fibre-product description of its base change never has to
mention a tensor product at all.

## Why flatness

Invariants are the kernel of the FINITE diagram `A → ∏_{σ ∈ G} A`, `a ↦ (σ • a - a)_σ`; i.e.
`0 → B → A → ∏_{σ ∈ G} A` is exact (`Algebra.IsInvariant` gives that a fixed element comes from
`B`, `smul_algebraMap` the converse, and injectivity of `algebraMap B A` left exactness).
Tensoring with a flat module preserves that exactness (`Module.Flat.rTensor_exact`), and
`(∏_{σ ∈ G} A) ⊗_k K ≅ ∏_{σ ∈ G} (A ⊗_k K)` because `G` is finite
(`TensorProduct.piRight`), so `B ⊗_k K = (A ⊗_k K)^G`.

At a NON-flat extension the statement is false; Katz–Mazur Remark (8.1.7) has explicit
counterexamples in the modular setting.  Flatness is consumed in exactly one place, the
`Module.Flat.rTensor_exact` call inside `isInvariant_tensor`.

## Implementation note

`bcAction` and `bcAlgebra` are `def`s, NOT instances: as instances they would be attempted on
every `MulSemiringAction _ (_ ⊗[_] _)` and `Algebra (_ ⊗[_] _) (_ ⊗[_] _)` goal in the whole
import cone, and neither of their side conditions is determined by the goal.  They are
introduced with `letI` where they are needed.
-/

@[expose] public section

open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Fermat.InvariantBaseChange

/-! ### The action of `G` on `A` by `k`-algebra automorphisms -/

section Tower

/-- **The deck group fixes the base ring pointwise** — derived from `SMulCommClass G B A` and a
scalar tower `k → B → A`, which is the shape a GIT presentation supplies. -/
theorem smulCommClass_of_isScalarTower (k B A : Type) [CommRing k] [CommRing B] [CommRing A]
    [Algebra k B] [Algebra B A] [Algebra k A] [IsScalarTower k B A]
    (G : Type) [Group G] [MulSemiringAction G A] [SMulCommClass G B A] :
    SMulCommClass G k A where
  smul_comm σ c a := by
    have hfix : σ • (algebraMap k A c) = algebraMap k A c := by
      rw [IsScalarTower.algebraMap_apply k B A, smul_algebraMap]
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]

end Tower

section Action

variable (k : Type) {A : Type} (K : Type) [CommRing k] [CommRing A] [CommRing K]
  [Algebra k A] [Algebra k K]
  (G : Type) [Group G] [MulSemiringAction G A] [SMulCommClass G k A]

variable {K} in
/-- Each `σ : G` acts on `A` as a `k`-algebra automorphism, because it fixes `k` pointwise. -/
def algAut (σ : G) : A ≃ₐ[k] A :=
  AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv G A σ) fun c => smul_algebraMap σ c

@[simp] theorem algAut_apply (σ : G) (a : A) : algAut k G σ a = σ • a := rfl

/-- The base change `σ ⊗ 1` of the action of `σ : G` to `A ⊗[k] K`. -/
noncomputable def bcAut (σ : G) : (A ⊗[k] K) ≃ₐ[k] (A ⊗[k] K) :=
  Algebra.TensorProduct.congr (algAut k G σ) (AlgEquiv.refl (R := k) (A₁ := K))

@[simp] theorem bcAut_tmul (σ : G) (a : A) (κ : K) :
    bcAut k K G σ (a ⊗ₜ[k] κ) = (σ • a) ⊗ₜ[k] κ := by
  simp [bcAut]

/-- The base-changed action of `G` on `A ⊗[k] K`, as a homomorphism to the ring automorphisms. -/
noncomputable def bcRingAut : G →* RingAut (A ⊗[k] K) where
  toFun σ := (bcAut k K G σ).toRingEquiv
  map_one' := by
    refine RingEquiv.ext fun x => ?_
    induction x with
    | zero => simp
    | tmul a κ => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' σ τ := by
    refine RingEquiv.ext fun x => ?_
    induction x with
    | zero => simp
    | tmul a κ => simp [mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The base-changed action of `G` on `A ⊗[k] K`. -/
@[reducible] noncomputable def bcAction : MulSemiringAction G (A ⊗[k] K) :=
  MulSemiringAction.compHom (A ⊗[k] K) (bcRingAut (A := A) k K G)

theorem bcAction_smul (σ : G) (x : A ⊗[k] K) :
    letI := bcAction (A := A) k K G
    σ • x = bcAut k K G σ x := rfl

end Action

/-! ### The invariant subring base-changes -/

section Tensor

variable (k : Type) {B A : Type} (K : Type) [CommRing k] [CommRing B] [CommRing A] [CommRing K]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra k K]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G k A]
  [SMulCommClass G B A]

/-- The base change `B ⊗[k] K → A ⊗[k] K` of the invariant-subring inclusion. -/
noncomputable def bcInclusion : (B ⊗[k] K) →ₐ[k] (A ⊗[k] K) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k B A) (AlgHom.id k K)

@[simp] theorem bcInclusion_tmul (b : B) (κ : K) :
    bcInclusion (A := A) k K (b ⊗ₜ[k] κ) = (algebraMap B A b) ⊗ₜ[k] κ := by
  simp [bcInclusion]

/-- The algebra structure of `A ⊗[k] K` over `B ⊗[k] K`. -/
@[reducible] noncomputable def bcAlgebra : Algebra (B ⊗[k] K) (A ⊗[k] K) :=
  (bcInclusion (B := B) (A := A) k K).toRingHom.toAlgebra

theorem bcAlgebra_algebraMap (y : B ⊗[k] K) :
    letI := bcAlgebra (B := B) (A := A) k K
    algebraMap (B ⊗[k] K) (A ⊗[k] K) y = bcInclusion (B := B) (A := A) k K y := rfl

/-- The invariant-subring inclusion, as a `k`-linear map. -/
noncomputable def inclLinear : B →ₗ[k] A :=
  (Algebra.linearMap B A).restrictScalars k

@[simp] theorem inclLinear_apply (b : B) : inclLinear (A := A) k b = algebraMap B A b := rfl

/-- `bcInclusion` is the base change of `inclLinear` — the bridge between the algebra language
the statement is in and the linear-algebra language flatness is available in. -/
theorem bcInclusion_eq_rTensor (y : B ⊗[k] K) :
    bcInclusion (B := B) (A := A) k K y = LinearMap.rTensor K (inclLinear (A := A) k) y := by
  induction y with
  | zero => simp
  | tmul b κ => rw [bcInclusion_tmul, LinearMap.rTensor_tmul, inclLinear_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- **The difference map whose kernel is the ring of invariants.** -/
noncomputable def diffMap : A →ₗ[k] (G → A) :=
  LinearMap.pi fun σ => (algAut k G σ).toLinearMap - LinearMap.id

omit [Finite G] [SMulCommClass G B A] in
@[simp] theorem diffMap_apply (a : A) (σ : G) : diffMap (A := A) k G a σ = σ • a - a := rfl

omit [Finite G] in
/-- `0 → B → A → ∏_{σ ∈ G} A` is exact at `A`. -/
theorem exact_inclLinear_diffMap [Algebra.IsInvariant B A G] :
    Function.Exact (inclLinear (B := B) (A := A) k) (diffMap (A := A) k G) := by
  intro a
  constructor
  · intro h
    have hfix : ∀ σ : G, σ • a = a := fun σ => by
      have h1 := congrFun h σ
      rw [diffMap_apply] at h1
      exact sub_eq_zero.mp h1
    obtain ⟨b, hb⟩ := Algebra.IsInvariant.isInvariant (A := B) (B := A) (G := G) a hfix
    exact ⟨b, hb⟩
  · rintro ⟨b, rfl⟩
    funext σ
    rw [diffMap_apply, inclLinear_apply, smul_algebraMap, sub_self]
    rfl

omit [Finite G] [SMulCommClass G B A] in
/-- The base change of `σ - 1` computes `σ • x - x` on `A ⊗[k] K`. -/
theorem rTensor_sub_id_apply (σ : G) (x : A ⊗[k] K) :
    letI := bcAction (A := A) k K G
    LinearMap.rTensor K ((algAut k G σ).toLinearMap - LinearMap.id) x = σ • x - x := by
  letI := bcAction (A := A) k K G
  induction x with
  | zero => simp
  | tmul a κ =>
      rw [LinearMap.rTensor_tmul, bcAction_smul k K G σ (a ⊗ₜ[k] κ), bcAut_tmul]
      show ((σ • a) - a) ⊗ₜ[k] κ = _
      rw [TensorProduct.sub_tmul]
  | add x y hx hy =>
      rw [map_add, hx, hy, smul_add]
      abel

omit [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G k A]
  [SMulCommClass G B A] in
/-- Tensoring a finite product with `K` on the right is detected by the projections: an element
killed by every projection is zero. -/
theorem eq_zero_of_forall_proj [Fintype G] [DecidableEq G]
    (y : (G → A) ⊗[k] K)
    (hy : ∀ σ : G, LinearMap.rTensor K (LinearMap.proj σ : (G → A) →ₗ[k] A) y = 0) :
    y = 0 := by
  set e : ((G → A) ⊗[k] K) ≃ₗ[k] (G → (K ⊗[k] A)) :=
    (TensorProduct.comm k (G → A) K).trans (TensorProduct.piRight k k K (fun _ : G => A)) with he
  have hcomp : ∀ (z : (G → A) ⊗[k] K) (σ : G),
      e z σ = TensorProduct.comm k A K
        (LinearMap.rTensor K (LinearMap.proj σ : (G → A) →ₗ[k] A) z) := by
    intro z σ
    induction z with
    | zero => simp
    | tmul m κ => simp [he]
    | add z w hz hw => simp only [map_add, Pi.add_apply, hz, hw]
  refine e.injective ?_
  rw [map_zero]
  funext σ
  rw [hcomp, hy σ, map_zero]
  rfl

/-- **THE INVARIANT SUBRING BASE-CHANGES ALONG A FLAT EXTENSION OF SCALARS.** -/
theorem isInvariant_tensor [Algebra.IsInvariant B A G] [Module.Flat k K] :
    letI := bcAction (A := A) k K G
    letI := bcAlgebra (B := B) (A := A) k K
    Algebra.IsInvariant (B ⊗[k] K) (A ⊗[k] K) G := by
  classical
  letI := bcAction (A := A) k K G
  letI := bcAlgebra (B := B) (A := A) k K
  haveI : Fintype G := Fintype.ofFinite G
  refine ⟨fun x hx => ?_⟩
  -- `x` is killed by the base change of the difference map …
  have hzero : LinearMap.rTensor K (diffMap (A := A) k G) x = 0 := by
    refine eq_zero_of_forall_proj k K G _ fun σ => ?_
    rw [← LinearMap.rTensor_comp_apply]
    have hproj : (LinearMap.proj σ : (G → A) →ₗ[k] A) ∘ₗ (diffMap (A := A) k G)
        = (algAut k G σ).toLinearMap - LinearMap.id := by
      ext a
      simp
    rw [show (LinearMap.proj σ : (G → A) →ₗ[k] A).comp (diffMap (A := A) k G)
        = (algAut k G σ).toLinearMap - LinearMap.id from hproj,
      rTensor_sub_id_apply k K G σ x, hx σ, sub_self]
  -- … hence lies in the image of the base change of the inclusion, by flatness.
  obtain ⟨y, hy⟩ := (Module.Flat.rTensor_exact (R := k) K
    (exact_inclLinear_diffMap (B := B) (A := A) k G) x).mp hzero
  exact ⟨y, by rw [bcAlgebra_algebraMap k K y, bcInclusion_eq_rTensor k K y, hy]⟩

omit [Finite G] in
theorem smulCommClass_tensor :
    letI := bcAction (A := A) k K G
    letI := bcAlgebra (B := B) (A := A) k K
    SMulCommClass G (B ⊗[k] K) (A ⊗[k] K) := by
  letI := bcAction (A := A) k K G
  letI := bcAlgebra (B := B) (A := A) k K
  refine ⟨fun σ r x => ?_⟩
  have hfix : bcAut k K G σ (bcInclusion (B := B) (A := A) k K r)
      = bcInclusion (B := B) (A := A) k K r := by
    induction r with
    | zero => simp
    | tmul b κ => rw [bcInclusion_tmul, bcAut_tmul, smul_algebraMap]
    | add r s hr hs => simp only [map_add, hr, hs]
  rw [Algebra.smul_def, Algebra.smul_def, bcAction_smul, map_mul, bcAlgebra_algebraMap, hfix]
  rfl

theorem injective_bcInclusion [Module.Flat k K]
    (hinj : Function.Injective (algebraMap B A)) :
    Function.Injective (bcInclusion (B := B) (A := A) k K) := by
  have h : Function.Injective (LinearMap.rTensor K (inclLinear (B := B) (A := A) k)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K) _ hinj
  intro y z hyz
  refine h ?_
  rw [← bcInclusion_eq_rTensor k K y, ← bcInclusion_eq_rTensor k K z]
  exact hyz

end Tensor

/-! ### The scheme-level statement -/

section Geometry

/-- `Spec (A ⊗[k] K)`, with the two inclusions, is a pullback of `Spec A ⟶ Spec k ⟵ Spec K`. -/
theorem isPullback_spec_tensor (k A K : Type) [CommRing k] [CommRing A] [CommRing K]
    [Algebra k A] [Algebra k K] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] K)))
      (Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K))))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso k A K).symm ?_ ?_
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    show (algebraMap k A c) ⊗ₜ[k] (1 : K) = (1 : A) ⊗ₜ[k] (algebraMap k K c)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · exact pullbackSpecIso_inv_fst k A K
  · exact pullbackSpecIso_inv_snd k A K

variable (k : Type) {B A : Type} (K : Type) [CommRing k] [CommRing B] [CommRing A] [CommRing K]
  [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A] [Algebra k K]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G k A]
  [SMulCommClass G B A]

/-- **GIT COMMUTES WITH A FLAT BASE CHANGE**, stated with no tensor product in sight.

`XA` and `XB` are the base changes of `Spec A` and `Spec B` along `Spec K ⟶ Spec k`, described
only by the universal property of the fibre product; `π` is the base change of the quotient map
`Spec (B → A)` and `act σ` the base change of `Spec σ`, each pinned by its two projections.  The
conclusion is that `π` is still a categorical quotient by `G`, for an ARBITRARY target `Y'`. -/
theorem exists_unique_of_isPullback [Algebra.IsInvariant B A G] [Module.Flat k K]
    (hinj : Function.Injective (algebraMap B A))
    {XA XB Y' : Scheme.{0}}
    {fA : XA ⟶ Spec (CommRingCat.of A)} {gA : XA ⟶ Spec (CommRingCat.of K)}
    (hA : IsPullback fA gA (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {fB : XB ⟶ Spec (CommRingCat.of B)} {gB : XB ⟶ Spec (CommRingCat.of K)}
    (hB : IsPullback fB gB (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (π : XA ⟶ XB)
    (hπf : π ≫ fB = fA ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)))
    (hπg : π ≫ gB = gA)
    (act : G → (XA ⟶ XA))
    (hactf : ∀ σ : G, act σ ≫ fA
      = fA ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A σ)))
    (hactg : ∀ σ : G, act σ ≫ gA = gA)
    (φ : XA ⟶ Y') (hφ : ∀ σ : G, act σ ≫ φ = φ) :
    ∃! ψ : XB ⟶ Y', π ≫ ψ = φ := by
  classical
  letI := bcAction (A := A) k K G
  letI := bcAlgebra (B := B) (A := A) k K
  haveI := isInvariant_tensor (B := B) (A := A) k K G
  haveI := smulCommClass_tensor (B := B) (A := A) k K G
  -- identify both fibre products with `Spec` of a tensor product
  obtain ⟨iA, hiAf, hiAg⟩ : ∃ i : Spec (CommRingCat.of (A ⊗[k] K)) ≅ XA,
      i.hom ≫ fA = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] K)) ∧
      i.hom ≫ gA = Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K))) :=
    ⟨(isPullback_spec_tensor k A K).isoIsPullback _ _ hA,
      IsPullback.isoIsPullback_hom_fst _ _ _ _, IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  obtain ⟨iB, hiBf, hiBg⟩ : ∃ i : Spec (CommRingCat.of (B ⊗[k] K)) ≅ XB,
      i.hom ≫ fB = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K)) ∧
      i.hom ≫ gB = Spec.map (CommRingCat.ofHom
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : K →ₐ[k] B ⊗[k] K))) :=
    ⟨(isPullback_spec_tensor k B K).isoIsPullback _ _ hB,
      IsPullback.isoIsPullback_hom_fst _ _ _ _, IsPullback.isoIsPullback_hom_snd _ _ _ _⟩
  -- `π` IS the base change of the quotient map
  have hquot : iA.hom ≫ π
      = Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[k] K) (A ⊗[k] K))) ≫ iB.hom := by
    refine hB.hom_ext ?_ ?_
    · rw [Category.assoc, hπf, ← Category.assoc, hiAf, Category.assoc, hiBf,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    · rw [Category.assoc, hπg, hiAg, Category.assoc, hiBg, ← Spec.map_comp]
      congr 1
      ext κ
      show (1 : A) ⊗ₜ[k] κ = algebraMap (B ⊗[k] K) (A ⊗[k] K) ((1 : B) ⊗ₜ[k] κ)
      rw [bcAlgebra_algebraMap, bcInclusion_tmul, map_one]
  -- `act σ` IS the base change of `Spec σ`
  have hactσ : ∀ σ : G, iA.hom ≫ act σ
      = Spec.map (CommRingCat.ofHom
          (MulSemiringAction.toRingHom G (A ⊗[k] K) σ)) ≫ iA.hom := by
    intro σ
    refine hA.hom_ext ?_ ?_
    · rw [Category.assoc, hactf, ← Category.assoc, hiAf, Category.assoc, hiAf,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    · rw [Category.assoc, hactg, hiAg, Category.assoc, hiAg, ← Spec.map_comp]
      congr 1
      ext κ
      show (1 : A) ⊗ₜ[k] κ = σ • ((1 : A) ⊗ₜ[k] κ)
      rw [bcAction_smul, bcAut_tmul, smul_one]
  -- the algebra, at the base-changed triple
  have hinj' : Function.Injective (algebraMap (B ⊗[k] K) (A ⊗[k] K)) :=
    injective_bcInclusion k K hinj
  obtain ⟨ψ₀, hψ₀, huniq⟩ := InvariantQuotient.exists_unique_of_isInvariant
    (B := B ⊗[k] K) (A := A ⊗[k] K) G hinj' (iA.hom ≫ φ) (fun σ => by
      rw [← Category.assoc, ← hactσ σ, Category.assoc, hφ σ])
  refine ⟨iB.inv ≫ ψ₀, ?_, ?_⟩
  · have hcomp : iA.hom ≫ π ≫ iB.inv ≫ ψ₀ = iA.hom ≫ φ := by
      rw [← Category.assoc, hquot, Category.assoc, Iso.hom_inv_id_assoc, hψ₀]
    exact (cancel_epi iA.hom).mp hcomp
  · intro ψ' hψ'
    have hstep : Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[k] K) (A ⊗[k] K)))
        ≫ (iB.hom ≫ ψ') = iA.hom ≫ φ := by
      rw [← Category.assoc, ← hquot, Category.assoc, hψ']
    have hE := huniq (iB.hom ≫ ψ') hstep
    rw [← hE, Iso.inv_hom_id_assoc]

end Geometry

end Fermat.InvariantBaseChange
