/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# The local criterion of flatness

Let `A` be a commutative ring, `J ⊆ A` an ideal, and `M` an `A`-module.  Assume

* `M ⧸ J M` is flat over `A ⧸ J`, and
* `Tor₁^A(A ⧸ J, M) = 0`, written without derived functors as injectivity of `J ⊗[A] M → M`.

Then for every `A`-module `Z`, every submodule `Y ≤ Z` and every `k` with `J ^ k • Z ≤ Y`, the
map `Y ⊗[A] M → Z ⊗[A] M` is injective
(`Module.Flat.rTensor_subtype_injective_of_pow_smul_top_le`).  Two consequences:

* if `J ^ N = ⊥` then `M` is flat over `A` — the local criterion of flatness for a **nilpotent**
  ideal, [Stacks 00MK] / [Stacks 051C], Matsumura *Commutative Ring Theory* 22.1/22.3
  (`Module.Flat.of_flat_quotient_of_pow_eq_bot`);
* for every ideal `𝔞 ⊇ J ^ k`, `𝔞 ⊗[A] M → M` is injective — the homological half of the
  Noetherian local criterion, Stacks 10.99.6 (`Module.Flat.rTensor_ideal_subtype_injective`).

**No separatedness and no Artin–Rees are involved**, and no Noetherian, finiteness or locality
hypothesis is used anywhere.

## The proof, and why it is not the textbook one

**There is no usable `Tor` at this pin** (checked 2026-07-27).
`Mathlib/CategoryTheory/Monoidal/Tor.lean` does define `Tor C n` as the left derived functor of
the tensor product, but the file is 60 lines long and its own module docstring says "For now we
have almost nothing to say about it!": there are exactly two lemmas, both of the form "higher
`Tor` of a projective vanishes".  In particular there is **no long exact sequence**:
`Mathlib/CategoryTheory/Abelian/LeftDerived.lean` constructs `Functor.leftDerived` and
`NatTrans.leftDerived` and stops — grepping it for `ShortComplex.ShortExact` returns nothing.
So the two-step argument of [Stacks 00MK] (`Tor₁(N, M) = 0` first for `A ⧸ J`-modules `N`, then
for all `N` by dévissage along `J ^ i N`) cannot be transcribed.

The argument below replaces it by an **elementary dévissage that never leaves the category of
modules**, using only right-exactness of the tensor product (`rTensor_exact`) and the
"flat implies preserves injections" half of flatness.  The four steps are:

1. `rTensor_injective_of_quotTensor_flat`: tensoring an injection of `A ⧸ J`-modules with `M`
   over `A` stays injective.  This is flatness of `M ⧸ JM` over `A ⧸ J` read through the
   base-change cancellation `X ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] M) ≃ X ⊗[A] M`
   (`TensorProduct.AlgebraTensorModule.cancelBaseChange`).
2. `rTensor_smulTop_subtype_injective`: for a **flat** `F`, `(J • ⊤ : Submodule A F) ⊗ M → F ⊗ M`
   is injective.  Here `J • ⊤_F` is the range of `J ⊗[A] F → F`, which is injective because `F`
   is flat, and the tensor reshuffle `(J ⊗ F) ⊗ M ≃ (J ⊗ M) ⊗ F` turns the claim into
   `rTensor F` applied to the hypothesis `J ⊗ M ↪ M`, again injective because `F` is flat.
3. `rTensor_subtype_injective_of_smul_top_le_flat`: for `F` flat and `J • ⊤_F ≤ K`,
   `K ⊗ M → F ⊗ M` is injective.  A three-term chase on `J • ⊤_F ≤ K ≤ F`: the top quotient
   `K ⧸ J•⊤_F ↪ F ⧸ J•⊤_F` is an injection of `A ⧸ J`-modules (step 1), the bottom piece is
   step 2, and right-exactness glues them.  **This is the step that would classically be
   `Tor₁(F ⧸ K, M) = 0` for `F ⧸ K` killed by `J`**, and it is where both hypotheses are spent.
4. `rTensor_subtype_injective_of_smul_top_le`: the same statement with `F` replaced by an
   arbitrary module `Z`, obtained from step 3 by a **presentation comparison** which is a pure
   diagram chase: choose the free module `F = Z →₀ A` with its canonical surjection `φ` onto
   `Z`, put `K = φ⁻¹(Y)`; then `K ↠ Y`, `ker φ ≤ K`, and step 3 plus right-exactness of
   `- ⊗ M` along `ker φ ↪ F ↠ Z` identify the two kernels.  No Schanuel, no horseshoe, no
   connecting map.

The induction on `k` (`rTensor_subtype_injective_of_pow_smul_top_le`) then runs on the two-step
filtration `Y ≤ Y ⊔ J ^ k • Z ≤ Z`, whose lower layer is killed by `J`.

## Faithfulness note on the shape of `of_flat_quotient_of_pow_eq_bot`

It is stated for an `A`-ALGEBRA `B` rather than for a bare `A`-module `M` for one reason only:
`Algebra (A ⧸ J) (B ⧸ J.map (algebraMap A B))` is an instance
(`Ideal.Quotient.algebraQuotientMapQuotient`), whereas `Module (A ⧸ J) (M ⧸ J • ⊤)` is not, so
the module form cannot even be *stated* without carrying a scalar action by hand.  The general
`A`-module statements above are therefore phrased with the flatness hypothesis in the form
`Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M)`, which carries its own instances; the algebra form is
recovered through `Module.Flat.flat_quotTensor_of_flat`.

`htor` is written in the shape of `Module.Flat.iff_lift_lsmul_comp_subtype_injective`, i.e. as
injectivity of `TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype) : J ⊗[A] B → B`,
which is precisely `Tor₁^A(A ⧸ J, B) = 0` spelled without derived functors.

[Stacks 00MK]: https://stacks.math.columbia.edu/tag/00MK
[Stacks 051C]: https://stacks.math.columbia.edu/tag/051C
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Module.Flat

section LocalCriterion

variable {A : Type u} [CommRing A] {J : Ideal A}
variable {M : Type v} [AddCommGroup M] [Module A M]

/-- An `A`-linear map between two `A ⧸ J`-modules is automatically `A ⧸ J`-linear, because
`A → A ⧸ J` is surjective. -/
def quotLinearMap {X Y : Type*}
    [AddCommGroup X] [Module A X] [Module (A ⧸ J) X] [IsScalarTower A (A ⧸ J) X]
    [AddCommGroup Y] [Module A Y] [Module (A ⧸ J) Y] [IsScalarTower A (A ⧸ J) Y]
    (f : X →ₗ[A] Y) : X →ₗ[A ⧸ J] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
      map_smul]

@[simp]
lemma quotLinearMap_apply {X Y : Type*}
    [AddCommGroup X] [Module A X] [Module (A ⧸ J) X] [IsScalarTower A (A ⧸ J) X]
    [AddCommGroup Y] [Module A Y] [Module (A ⧸ J) Y] [IsScalarTower A (A ⧸ J) Y]
    (f : X →ₗ[A] Y) (x : X) : quotLinearMap (J := J) f x = f x := rfl

/-- Transport of the flatness hypothesis: an `A ⧸ J`-module `Q` receiving an `A`-linear
surjection from `M` with kernel `J • ⊤` *is* `(A ⧸ J) ⊗[A] M`. -/
noncomputable def quotTensorEquivOfSurjective {Q : Type*} [AddCommGroup Q] [Module A Q]
    [Module (A ⧸ J) Q] [IsScalarTower A (A ⧸ J) Q]
    (q : M →ₗ[A] Q) (hq : Function.Surjective q)
    (hker : J • (⊤ : Submodule A M) = LinearMap.ker q) :
    (A ⧸ J) ⊗[A] M ≃ₗ[A ⧸ J] Q :=
  let e : (A ⧸ J) ⊗[A] M ≃ₗ[A] Q :=
    (TensorProduct.quotTensorEquivQuotSMul M J) ≪≫ₗ (Submodule.quotEquivOfEq _ _ hker) ≪≫ₗ
      (LinearMap.quotKerEquivOfSurjective q hq)
  { quotLinearMap (J := J) e.toLinearMap with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- Transport of the flatness hypothesis, see `quotTensorEquivOfSurjective`. -/
theorem flat_quotTensor_of_flat {Q : Type*} [AddCommGroup Q] [Module A Q]
    [Module (A ⧸ J) Q] [IsScalarTower A (A ⧸ J) Q]
    (q : M →ₗ[A] Q) (hq : Function.Surjective q)
    (hker : J • (⊤ : Submodule A M) = LinearMap.ker q)
    (h : Module.Flat (A ⧸ J) Q) : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M) :=
  haveI := h
  Module.Flat.of_linearEquiv (quotTensorEquivOfSurjective q hq hker)

/-- Tensoring with `M` over `A` sends a linear equivalence to an injection. -/
theorem rTensor_equiv_injective {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) :
    Function.Injective (LinearMap.rTensor M e.toLinearMap) := by
  have key : ∀ w : X ⊗[A] M,
      LinearMap.rTensor M e.symm.toLinearMap (LinearMap.rTensor M e.toLinearMap w) = w := by
    intro w
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from by ext x; simp,
      LinearMap.rTensor_id, LinearMap.id_apply]
  intro z z' hz
  rw [← key z, ← key z', hz]

/-- Tensoring with `M` over `A` sends a linear equivalence to a surjection. -/
theorem rTensor_equiv_surjective {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) :
    Function.Surjective (LinearMap.rTensor M e.toLinearMap) := by
  intro w
  refine ⟨LinearMap.rTensor M e.symm.toLinearMap w, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from by ext x; simp,
    LinearMap.rTensor_id, LinearMap.id_apply]

/-- **Step 1.**  Flatness of `M ⧸ JM` over `A ⧸ J`, in the form the dévissage uses: tensoring an
injection of `A ⧸ J`-modules with `M` **over `A`** keeps it injective.

The proof is the base-change cancellation `X ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] M) ≃ X ⊗[A] M`. -/
theorem rTensor_injective_of_quotTensor_flat
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    {X Y : Type*}
    [AddCommGroup X] [Module A X] [Module (A ⧸ J) X] [IsScalarTower A (A ⧸ J) X]
    [AddCommGroup Y] [Module A Y] [Module (A ⧸ J) Y] [IsScalarTower A (A ⧸ J) Y]
    (f : X →ₗ[A] Y) (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor M f) := by
  haveI := hflat
  set fq : X →ₗ[A ⧸ J] Y := quotLinearMap (J := J) f with hfqdef
  have h1 : Function.Injective (LinearMap.rTensor ((A ⧸ J) ⊗[A] M) fq) :=
    Module.Flat.rTensor_preserves_injective_linearMap fq hf
  set eX := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) X M with heX
  set eY := TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ J) (A ⧸ J) Y M with heY
  have hsq : ∀ z : X ⊗[A ⧸ J] ((A ⧸ J) ⊗[A] M),
      LinearMap.rTensor M f (eX z) = eY (LinearMap.rTensor ((A ⧸ J) ⊗[A] M) fq z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp [hz, hz']
    | tmul x w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp [TensorProduct.tmul_add, hw, hw']
      | tmul c m =>
        simp only [heX, heY, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          LinearMap.rTensor_tmul]
        exact congrArg (· ⊗ₜ[A] m) (map_smul fq c x)
  intro z z' h
  obtain ⟨w, rfl⟩ := eX.surjective z
  obtain ⟨w', rfl⟩ := eX.surjective z'
  rw [hsq, hsq] at h
  exact congrArg eX (h1 (eY.injective h))

/-- Reshuffling helper: if `rTensor M f` is injective and `F` is flat, then
`rTensor M (rTensor F f)` is injective. -/
theorem rTensor_rTensor_injective {X Y F : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup F] [Module A F] [Module.Flat A F]
    (f : X →ₗ[A] Y) (hf : Function.Injective (LinearMap.rTensor M f)) :
    Function.Injective (LinearMap.rTensor M (LinearMap.rTensor F f)) := by
  have hFf : Function.Injective (LinearMap.rTensor F (LinearMap.rTensor M f)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  set eX : (X ⊗[A] F) ⊗[A] M ≃ₗ[A] (X ⊗[A] M) ⊗[A] F :=
    (TensorProduct.assoc A X F M) ≪≫ₗ
      (TensorProduct.congr (LinearEquiv.refl A X) (TensorProduct.comm A F M)) ≪≫ₗ
      (TensorProduct.assoc A X M F).symm with heX
  set eY : (Y ⊗[A] F) ⊗[A] M ≃ₗ[A] (Y ⊗[A] M) ⊗[A] F :=
    (TensorProduct.assoc A Y F M) ≪≫ₗ
      (TensorProduct.congr (LinearEquiv.refl A Y) (TensorProduct.comm A F M)) ≪≫ₗ
      (TensorProduct.assoc A Y M F).symm with heY
  have hsq : (eY.toLinearMap ∘ₗ LinearMap.rTensor M (LinearMap.rTensor F f))
      = LinearMap.rTensor F (LinearMap.rTensor M f) ∘ₗ eX.toLinearMap := by
    ext x g m
    simp [heX, heY]
  intro z z' h
  have h1 : LinearMap.rTensor F (LinearMap.rTensor M f) (eX z)
      = LinearMap.rTensor F (LinearMap.rTensor M f) (eX z') := by
    have e1 := LinearMap.congr_fun hsq z
    have e2 := LinearMap.congr_fun hsq z'
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at e1 e2
    rw [← e1, ← e2, h]
  exact eX.injective (hFf h1)

/-- **Step 2.**  For a flat module `F`, the inclusion `J • ⊤ ≤ F` stays injective after tensoring
with `M`, provided `J ⊗[A] M → M` is injective. -/
theorem rTensor_smulTop_subtype_injective
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Flat A F] :
    Function.Injective (LinearMap.rTensor M (J • (⊤ : Submodule A F)).subtype) := by
  classical
  set μ : (J : Submodule A A) ⊗[A] F →ₗ[A] F :=
    (TensorProduct.lid A F).toLinearMap ∘ₗ LinearMap.rTensor F J.subtype with hμ
  have hμapply : ∀ (j : J) (g : F), μ (j ⊗ₜ[A] g) = (j : A) • g := by
    intro j g; simp [hμ]
  have hμinj : Function.Injective μ :=
    (TensorProduct.lid A F).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap J.subtype Subtype.val_injective)
  have hrange : LinearMap.range μ = J • (⊤ : Submodule A F) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul j g => simpa [hμapply] using Submodule.smul_mem_smul j.2 Submodule.mem_top
      | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    · rw [Submodule.smul_le]
      intro r hr g _
      exact ⟨(⟨r, hr⟩ : J) ⊗ₜ[A] g, by simp [hμapply]⟩
  set σ : (J : Submodule A A) ⊗[A] F ≃ₗ[A] (J • (⊤ : Submodule A F) : Submodule A F) :=
    (LinearEquiv.ofInjective μ hμinj) ≪≫ₗ (LinearEquiv.ofEq _ _ hrange) with hσ
  have hσapply : ∀ y, ((σ y : F)) = μ y := fun _ => rfl
  have hμM : Function.Injective (LinearMap.rTensor M μ) := by
    have h1 : Function.Injective (LinearMap.rTensor M (LinearMap.rTensor F J.subtype)) :=
      rTensor_rTensor_injective (M := M) (F := F) J.subtype htor
    have hcomp : LinearMap.rTensor M μ
        = LinearMap.rTensor M (TensorProduct.lid A F).toLinearMap ∘ₗ
            LinearMap.rTensor M (LinearMap.rTensor F J.subtype) := by
      rw [← LinearMap.rTensor_comp]
    rw [hcomp]
    exact (rTensor_equiv_injective (M := M) (TensorProduct.lid A F)).comp h1
  intro z z' h
  obtain ⟨w, rfl⟩ := (rTensor_equiv_surjective (M := M) σ) z
  obtain ⟨w', rfl⟩ := (rTensor_equiv_surjective (M := M) σ) z'
  have hσcomp : (J • (⊤ : Submodule A F)).subtype ∘ₗ σ.toLinearMap = μ :=
    LinearMap.ext hσapply
  have key : ∀ y, LinearMap.rTensor M (J • (⊤ : Submodule A F)).subtype
      (LinearMap.rTensor M σ.toLinearMap y) = LinearMap.rTensor M μ y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hσcomp]
  rw [key, key] at h
  exact congrArg _ (hμM h)

/-- **Step 3.**  The local criterion over a **flat** module: if `J • ⊤ ≤ K ≤ F` with `F` flat,
then `K ⊗[A] M → F ⊗[A] M` is injective.

Classically this is `Tor₁^A(F ⧸ K, M) = 0` for the `J`-killed module `F ⧸ K`; it is where both
hypotheses are spent. -/
theorem rTensor_subtype_injective_of_smul_top_le_flat
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Flat A F]
    {K : Submodule A F} (hK : J • (⊤ : Submodule A F) ≤ K) :
    Function.Injective (LinearMap.rTensor M K.subtype) := by
  classical
  set S : Submodule A F := J • (⊤ : Submodule A F) with hS
  set S' : Submodule A K := Submodule.comap K.subtype S with hS'
  have htorY : Module.IsTorsionBySet A (F ⧸ S) (J : Set A) := by
    intro x a
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective S x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  have htorX : Module.IsTorsionBySet A (K ⧸ S') (J : Set A) := by
    intro x a
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective S' x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show ((a : A) • (g : F)) ∈ S
    exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  letI : Module (A ⧸ J) (F ⧸ S) := htorY.module
  letI : Module (A ⧸ J) (K ⧸ S') := htorX.module
  haveI : IsScalarTower A (A ⧸ J) (F ⧸ S) := htorY.isScalarTower
  haveI : IsScalarTower A (A ⧸ J) (K ⧸ S') := htorX.isScalarTower
  set g : (K : Submodule A F) →ₗ[A] (F ⧸ S) := S.mkQ ∘ₗ K.subtype with hg
  have hgker : LinearMap.ker g = S' := by
    ext x
    simp [hg, hS', Submodule.Quotient.mk_eq_zero]
  set f : (K ⧸ S') →ₗ[A] (F ⧸ S) := S'.liftQ g (le_of_eq hgker.symm) with hf
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hgker)
  have hfM : Function.Injective (LinearMap.rTensor M f) :=
    rTensor_injective_of_quotTensor_flat hflat f hfinj
  rw [injective_iff_map_eq_zero]
  intro ζ hζ
  have h1 : LinearMap.rTensor M S'.mkQ ζ = 0 := by
    refine (injective_iff_map_eq_zero _).mp hfM _ ?_
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show f ∘ₗ S'.mkQ = S.mkQ ∘ₗ K.subtype from by ext x; simp [hf, hg],
      LinearMap.rTensor_comp, LinearMap.comp_apply, hζ, map_zero]
  have hex : Function.Exact (LinearMap.rTensor M S'.subtype) (LinearMap.rTensor M S'.mkQ) :=
    _root_.rTensor_exact M (LinearMap.exact_subtype_mkQ S') (Submodule.mkQ_surjective S')
  obtain ⟨θ, hθ⟩ := (hex ζ).mp h1
  set ε : (S' : Submodule A K) ≃ₗ[A] (S : Submodule A F) := Submodule.comapSubtypeEquivOfLe hK
    with hε
  have h2 : LinearMap.rTensor M S.subtype (LinearMap.rTensor M ε.toLinearMap θ) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show S.subtype ∘ₗ ε.toLinearMap = K.subtype ∘ₗ S'.subtype from by ext x; rfl,
      LinearMap.rTensor_comp, LinearMap.comp_apply, hθ, hζ]
  have h3 : LinearMap.rTensor M ε.toLinearMap θ = 0 :=
    (injective_iff_map_eq_zero _).mp (rTensor_smulTop_subtype_injective (M := M) htor) _ h2
  have h4 : θ = 0 := rTensor_equiv_injective (M := M) ε (by rw [h3, map_zero])
  rw [← hθ, h4, map_zero]

/-- **Step 4, abstract form.**  The local criterion transported from a flat module `F` to an
arbitrary module `Z` along any surjection `φ : F ↠ Z`.

This is the presentation comparison, and it is a pure diagram chase: with `K = φ⁻¹(Y)` one has
`K ↠ Y` and `ker φ ≤ K`, and right-exactness of `- ⊗ M` along `ker φ ↪ F ↠ Z` identifies the
kernel of `Y ⊗ M → Z ⊗ M` with the image of `ker φ ⊗ M`, which step 3 kills.

`φ` is kept abstract on purpose: instantiating it at `Finsupp.linearCombination` *inside* the
proof makes unification chase `Finsupp` internals, which the module system does not expose. -/
theorem rTensor_subtype_injective_of_surjective
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    {Z F : Type*} [AddCommGroup Z] [Module A Z] [AddCommGroup F] [Module A F] [Module.Flat A F]
    (φ : F →ₗ[A] Z) (hφ : Function.Surjective φ)
    {Y : Submodule A Z} (h : J • (⊤ : Submodule A Z) ≤ Y) :
    Function.Injective (LinearMap.rTensor M Y.subtype) := by
  classical
  set K : Submodule A F := Submodule.comap φ Y with hKdef
  have hSK : J • (⊤ : Submodule A F) ≤ K := by
    rw [Submodule.smul_le]
    intro r hr x _
    show φ (r • x) ∈ Y
    rw [map_smul]
    exact h (Submodule.smul_mem_smul hr Submodule.mem_top)
  have hKinj := rTensor_subtype_injective_of_smul_top_le_flat hflat htor hSK
  set φK : (K : Submodule A F) →ₗ[A] (Y : Submodule A Z) :=
    (φ ∘ₗ K.subtype).codRestrict Y (fun x => x.2) with hφKdef
  have hφKsurj : Function.Surjective φK := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨⟨x, hy⟩, Subtype.ext rfl⟩
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨ζ, rfl⟩ := LinearMap.rTensor_surjective M hφKsurj ξ
  have h0 : LinearMap.rTensor M φ (LinearMap.rTensor M K.subtype ζ) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show φ ∘ₗ K.subtype = Y.subtype ∘ₗ φK from by ext x; rfl,
      LinearMap.rTensor_comp, LinearMap.comp_apply]
    exact hξ
  have hex : Function.Exact (LinearMap.rTensor M (LinearMap.ker φ).subtype)
      (LinearMap.rTensor M φ) :=
    _root_.rTensor_exact M (LinearMap.exact_subtype_ker_map φ) hφ
  obtain ⟨η, hη⟩ := (hex _).mp h0
  have hkK : LinearMap.ker φ ≤ K := by
    intro x hx
    show φ x ∈ Y
    rw [show φ x = 0 from hx]
    exact Y.zero_mem
  have h1 : LinearMap.rTensor M K.subtype (LinearMap.rTensor M (Submodule.inclusion hkK) η)
      = LinearMap.rTensor M K.subtype ζ := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      show K.subtype ∘ₗ Submodule.inclusion hkK = (LinearMap.ker φ).subtype from by ext x; rfl,
      hη]
  rw [← hKinj h1, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
    show φK ∘ₗ Submodule.inclusion hkK = 0 from by
      ext x
      exact LinearMap.mem_ker.mp x.2,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

/-- **Step 4.**  The local criterion over an arbitrary module: if `J • ⊤ ≤ Y ≤ Z` then
`Y ⊗[A] M → Z ⊗[A] M` is injective.  Free modules exist, so this is step 4' at the canonical
free presentation `Z →₀ A ↠ Z`. -/
theorem rTensor_subtype_injective_of_smul_top_le
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    {Z : Type u} [AddCommGroup Z] [Module A Z] {Y : Submodule A Z}
    (h : J • (⊤ : Submodule A Z) ≤ Y) :
    Function.Injective (LinearMap.rTensor M Y.subtype) :=
  haveI : Module.Flat A (Z →₀ A) := Module.Flat.of_free
  rTensor_subtype_injective_of_surjective hflat htor (Finsupp.linearCombination A (id : Z → Z))
    (Finsupp.linearCombination_surjective A Function.surjective_id) h

/-- **The local criterion of flatness, filtered form.**  If `J ^ k • Z ≤ Y ≤ Z` then
`Y ⊗[A] M → Z ⊗[A] M` is injective. -/
theorem rTensor_subtype_injective_of_pow_smul_top_le
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype)) :
    ∀ (k : ℕ) {Z : Type u} [AddCommGroup Z] [Module A Z] {Y : Submodule A Z},
      J ^ k • (⊤ : Submodule A Z) ≤ Y → Function.Injective (LinearMap.rTensor M Y.subtype) := by
  intro k
  induction k with
  | zero =>
    intro Z _ _ Y h
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, top_le_iff] at h
    subst h
    exact rTensor_equiv_injective (M := M) (Submodule.topEquiv (R := A) (M := Z))
  | succ n ih =>
    intro Z _ _ Y h
    set W : Submodule A Z := Y ⊔ (J ^ n • (⊤ : Submodule A Z)) with hW
    have hYW : Y ≤ W := le_sup_left
    have hWinj : Function.Injective (LinearMap.rTensor M W.subtype) := ih le_sup_right
    have hJW : J • W ≤ Y := by
      rw [hW, Submodule.smul_sup]
      refine sup_le Submodule.smul_le_right ?_
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ']
      exact h
    have hstep : Function.Injective
        (LinearMap.rTensor M (Submodule.comap W.subtype Y).subtype) := by
      refine rTensor_subtype_injective_of_smul_top_le hflat htor (Z := W) ?_
      rw [Submodule.smul_le]
      intro r hr x _
      show ((r : A) • (x : Z)) ∈ Y
      exact hJW (Submodule.smul_mem_smul hr x.2)
    have hmaps : W.subtype ∘ₗ ((Submodule.comap W.subtype Y).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe hYW).symm.toLinearMap) = Y.subtype :=
      LinearMap.ext fun x => rfl
    have hcomp : LinearMap.rTensor M Y.subtype
        = (LinearMap.rTensor M W.subtype) ∘ₗ
            ((LinearMap.rTensor M (Submodule.comap W.subtype Y).subtype) ∘ₗ
            (LinearMap.rTensor M (Submodule.comapSubtypeEquivOfLe hYW).symm.toLinearMap)) := by
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, hmaps]
    rw [hcomp]
    exact hWinj.comp
      (hstep.comp (rTensor_equiv_injective (M := M) (Submodule.comapSubtypeEquivOfLe hYW).symm))

/-- **The homological half of the local criterion of flatness** (Stacks 10.99.6): for every
ideal `𝔞 ⊇ J ^ k`, the multiplication map `𝔞 ⊗[A] M → M` is injective. -/
theorem rTensor_ideal_subtype_injective
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    (k : ℕ) {𝔞 : Ideal A} (h : J ^ k ≤ 𝔞) :
    Function.Injective (LinearMap.rTensor M 𝔞.subtype) :=
  rTensor_subtype_injective_of_pow_smul_top_le hflat htor k (Z := A) (Y := 𝔞) (by simpa using h)

/-- **The local criterion of flatness for a nilpotent ideal**, module form. -/
theorem of_pow_eq_bot
    (hflat : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] M))
    (htor : Function.Injective (LinearMap.rTensor M J.subtype))
    (N : ℕ) (hJnil : J ^ N = ⊥) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro 𝔞
  exact rTensor_ideal_subtype_injective hflat htor N (by rw [hJnil]; exact bot_le)

end LocalCriterion

/-- **THE LOCAL CRITERION OF FLATNESS FOR A NILPOTENT IDEAL** ([Stacks 00MK] / [Stacks 051C],
Matsumura *Commutative Ring Theory* 22.1/22.3).

`J ^ N = ⊥`, `B ⧸ JB` flat over `A ⧸ J`, and `J ⊗[A] B → B` injective (which is
`Tor₁^A(A ⧸ J, B) = 0` written without derived functors) together force `B` flat over `A`.

**PROVEN 2026-07-27** by the elementary dévissage described in the module docstring, over the
general module-theoretic statement `Module.Flat.of_pow_eq_bot`; no `Tor` and no long exact
sequence are used, because the pin has neither.

Consumed by `Fermat.flat_quotientMap_pow_of_flat_quotientMap`
(`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`), which is the nilpotent half of the
one-element local criterion `Fermat.flat_of_flat_quotient_isSMulRegular`. -/
theorem of_flat_quotient_of_pow_eq_bot {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (J : Ideal A) (N : ℕ) (hJnil : J ^ N = ⊥)
    (hflat : Module.Flat (A ⧸ J) (B ⧸ Ideal.map (algebraMap A B) J))
    (htor : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype))) :
    Module.Flat A B := by
  have hlift : TensorProduct.lift ((LinearMap.lsmul A B).comp J.subtype)
      = (TensorProduct.lid A B).toLinearMap ∘ₗ LinearMap.rTensor B J.subtype := by
    ext x b
    simp
  rw [hlift] at htor
  have htor' : Function.Injective (LinearMap.rTensor B J.subtype) := by
    intro z z' hz
    exact htor (by simpa using congrArg (TensorProduct.lid A B) hz)
  have hker : J • (⊤ : Submodule A B)
      = LinearMap.ker (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) J)).toLinearMap := by
    rw [Ideal.smul_top_eq_map]
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have hflat' : Module.Flat (A ⧸ J) ((A ⧸ J) ⊗[A] B) :=
    flat_quotTensor_of_flat (J := J)
      (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) J)).toLinearMap
      Ideal.Quotient.mk_surjective hker hflat
  exact of_pow_eq_bot hflat' htor' N hJnil

end Module.Flat
