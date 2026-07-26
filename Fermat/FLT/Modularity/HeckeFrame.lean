/-
Modularity/HeckeFrame.lean — own work for the Fermat project (not
vendored from the FLT project).

# The rank-two Hecke frame `(F ⊗ₖ T)²`

This module isolates, in a completely general and geometry-free
setting, the linear algebra that the modular Tate module of `J₀(M)`
contributes to `ModularTateModuleData` (`Modularity/Interface.lean`).

The classical input it replaces is this. Let `𝕋_ℚ` be the rational
Hecke algebra of level `M`. Mazur (*Modular curves and the Eisenstein
ideal*, ch. II) and Ribet (*Invent. Math.* 100 (1990), §2) show that
`H₁(X₀(M); ℚ)` is FREE OF RANK TWO over `𝕋_ℚ`, and the Tate-module
comparison then gives

  `V_p(J₀(M)) ⊗_{ℚ_p} ℚ̄_p  ≅  (𝕋_ℚ ⊗_ℚ ℚ̄_p)²`

as a module over `𝕋_ℚ ⊗_ℚ ℚ̄_p`. So — up to a `𝕋`-linear isomorphism,
along which everything else in the package transports — the underlying
Hecke module of the geometric package is not an unknown at all: it is
the free rank-two module over the base-changed Hecke algebra, with the
Hecke operators acting by multiplication.

Naming it is what makes the geometric leaf CUTTABLE. A tower of
`Nonempty` sub-packages over an existentially quantified carrier is
unsound (see the junk counterexample in the seventh-decomposition note
in `Interface.lean`); the remedy applied there to the Hecke algebra
`T` — replace the existential by a concrete definition — is applied
here to the Galois module `Vp`. Every field of `ModularTateModuleData`
that does not mention the Galois action or the Weil pairing then
becomes a THEOREM about `(F ⊗ₖ T)²` rather than a hypothesis, and the
residue of the geometric leaf is exactly the arithmetic: the Galois
action, the Eichler–Shimura congruence, the twisted Weil pairing and
Ribet irreducibility.

## Contents

* `frameAction` — the action of `T` on `(F ⊗ₖ T)²` by multiplication
  through `1 ⊗ t`, as a ring map into `End_F`;
* `adjoin_includeRight_eq_top` — base change of a generating set:
  if `S` generates `T` over `k` then `1 ⊗ S` generates `F ⊗ₖ T`
  over `F`;
* `adjoin_frameAction_eq_range` — hence the `F`-subalgebra generated
  by the operators `frameAction s`, `s ∈ S`, is exactly the
  multiplication algebra of `F ⊗ₖ T`;
* `frame_span` / `frame_indep` — freeness of rank two over it;
* `linearIndependent_one_tmul` — a `k`-independent family in `T`
  stays `F`-independent after base change (this is `padic_indep`);
* `linearIndependent_frameAction` — and stays independent inside
  `End_F`.

Everything here is elementary and none of it mentions modular forms,
so it is deliberately stated over an arbitrary field extension
`k ⊆ F` and an arbitrary `k`-algebra `T`, and lives in its own small
module rather than inside the very large `Interface.lean`.
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

namespace GaloisRepresentation.Modularity

open scoped TensorProduct

section HeckeFrame

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]
variable {T : Type*} [Ring T] [Algebra k T]

variable (k F T) in
/-- **The rank-two Hecke frame**: `(F ⊗ₖ T)²`, written as
`Fin 2 → F ⊗ₖ T`. This is the concrete model of
`V_p(J₀(M)) ⊗ ℚ̄_p` supplied by freeness of `H₁(X₀(M); ℚ)` of rank two
over the Hecke algebra. -/
abbrev HeckeFrame : Type _ := Fin 2 → F ⊗[k] T

variable (k F T) in
/-- **The action of `T` on the frame**: `t` acts by multiplication by
`1 ⊗ t` in each coordinate. This is the `padic` field of
`ModularTateModuleData` at the concrete carrier. -/
noncomputable def frameAction : T →+* Module.End F (HeckeFrame k F T) :=
  ((Algebra.lsmul F F (HeckeFrame k F T) :
      (F ⊗[k] T) →ₐ[F] Module.End F (HeckeFrame k F T)).toRingHom).comp
    (Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T).toRingHom

/-- Multiplication by a fixed element of `F ⊗ₖ T`, as an `F`-algebra
map into the endomorphisms of the frame; `frameAction t` is
`frameMul (1 ⊗ t)` by definition. -/
noncomputable abbrev frameMul :
    (F ⊗[k] T) →ₐ[F] Module.End F (HeckeFrame k F T) :=
  Algebra.lsmul F F (HeckeFrame k F T)

/-- The first member of the standard frame. -/
noncomputable abbrev frameBasis₁ : HeckeFrame k F T := Pi.single 0 1

/-- The second member of the standard frame. -/
noncomputable abbrev frameBasis₂ : HeckeFrame k F T := Pi.single 1 1

theorem frameMul_frameBasis₁ (r : F ⊗[k] T) :
    frameMul (k := k) (F := F) (T := T) r frameBasis₁ = Pi.single 0 r := by
  classical
  funext i
  fin_cases i <;>
    simp [frameMul, frameBasis₁, Algebra.lsmul_apply]

theorem frameMul_frameBasis₂ (r : F ⊗[k] T) :
    frameMul (k := k) (F := F) (T := T) r frameBasis₂ = Pi.single 1 r := by
  classical
  funext i
  fin_cases i <;>
    simp [frameMul, frameBasis₂, Algebra.lsmul_apply]

/-- **Freeness, existence half**: every element of the frame is
`r · e₁ + s · e₂`. -/
theorem frame_span (x : HeckeFrame k F T) :
    x = frameMul (k := k) (F := F) (T := T) (x 0) frameBasis₁
      + frameMul (k := k) (F := F) (T := T) (x 1) frameBasis₂ := by
  classical
  rw [frameMul_frameBasis₁, frameMul_frameBasis₂]
  funext i
  fin_cases i <;> simp

/-- **Freeness, uniqueness half**. -/
theorem frame_indep {r s : F ⊗[k] T}
    (h : frameMul (k := k) (F := F) (T := T) r frameBasis₁
        + frameMul (k := k) (F := F) (T := T) s frameBasis₂ = 0) :
    r = 0 ∧ s = 0 := by
  classical
  rw [frameMul_frameBasis₁, frameMul_frameBasis₂] at h
  constructor
  · have := congrArg (fun v => v 0) h
    simpa [Pi.single_apply] using this
  · have := congrArg (fun v => v 1) h
    simpa [Pi.single_apply] using this

/-- Multiplication on the frame is faithful. -/
theorem frameMul_injective :
    Function.Injective (frameMul (k := k) (F := F) (T := T)) := by
  classical
  intro r s hrs
  have h := congrArg (fun f => f frameBasis₁) hrs
  simp only [frameMul_frameBasis₁] at h
  have := congrArg (fun v => v 0) h
  simpa [Pi.single_apply] using this

/-- **Base change of a generating set**: if `S` generates `T` as a
`k`-algebra then `1 ⊗ S` generates `F ⊗ₖ T` as an `F`-algebra. -/
theorem adjoin_includeRight_eq_top (S : Set T) (hS : Algebra.adjoin k S = ⊤) :
    Algebra.adjoin F
        ((Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T) '' S) = ⊤ := by
  classical
  set A : Subalgebra F (F ⊗[k] T) :=
    Algebra.adjoin F ((Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T) '' S) with hA
  -- every `1 ⊗ t` lies in `A`
  have hall : ∀ t : T, (1 : F) ⊗ₜ[k] t ∈ A := by
    have hsub : Algebra.adjoin k S ≤
        Subalgebra.comap (Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T)
          (A.restrictScalars k) := by
      refine Algebra.adjoin_le ?_
      intro t ht
      exact Algebra.subset_adjoin ⟨t, ht, rfl⟩
    intro t
    have : t ∈ Subalgebra.comap
        (Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T)
        (A.restrictScalars k) := hsub (hS ▸ Algebra.mem_top)
    simpa using this
  -- hence every pure tensor lies in `A`
  have hpure : ∀ (c : F) (t : T), c ⊗ₜ[k] t ∈ A := by
    intro c t
    have h1 : (c : F) • ((1 : F) ⊗ₜ[k] t) = c ⊗ₜ[k] t := by
      simp [TensorProduct.smul_tmul']
    exact h1 ▸ Submodule.smul_mem A.toSubmodule c (hall t)
  -- and pure tensors span
  refine eq_top_iff.mpr ?_
  intro x _
  have hspan : Submodule.span k {t : F ⊗[k] T | ∃ m n, m ⊗ₜ[k] n = t} = ⊤ :=
    TensorProduct.span_tmul_eq_top k F T
  have hx : x ∈ Submodule.span k {t : F ⊗[k] T | ∃ m n, m ⊗ₜ[k] n = t} := by
    rw [hspan]; trivial
  refine Submodule.span_induction (p := fun y _ => y ∈ A) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨c, t, rfl⟩; exact hpure c t
  · exact zero_mem A
  · intro y z _ _ hy hz; exact add_mem hy hz
  · intro c y _ hy
    have : (algebraMap k F c) • y = c • y := by
      simp [algebraMap_smul]
    exact this ▸ Submodule.smul_mem A.toSubmodule (algebraMap k F c) hy

/-- **The Hecke subalgebra of the frame is the multiplication
algebra**: if `S` generates `T` over `k`, the `F`-subalgebra of
`End_F` generated by the operators `frameAction s`, `s ∈ S`, is the
whole multiplication algebra of `F ⊗ₖ T`. -/
theorem adjoin_frameAction_eq_range (S : Set T) (hS : Algebra.adjoin k S = ⊤) :
    Algebra.adjoin F ((fun t => frameAction k F T t) '' S) =
      (frameMul (k := k) (F := F) (T := T)).range := by
  classical
  have himg : (fun t => frameAction k F T t) '' S =
      (frameMul (k := k) (F := F) (T := T)) ''
        ((Algebra.TensorProduct.includeRight : T →ₐ[k] F ⊗[k] T) '' S) := by
    rw [← Set.image_comp]
    rfl
  rw [himg, Algebra.adjoin_image, adjoin_includeRight_eq_top S hS, Algebra.map_top]

/-- **Base change preserves linear independence**: a `k`-independent
family in `T` stays `F`-independent in `F ⊗ₖ T`. -/
theorem linearIndependent_one_tmul {ι : Type*} (x : ι → T)
    (hx : LinearIndependent k x) :
    LinearIndependent F (fun i => (1 : F) ⊗ₜ[k] x i) := by
  classical
  set I : Set T := hx.linearIndepOn_id.extend (Set.subset_univ _) with hI
  set b : Module.Basis I k T := Module.Basis.extend hx.linearIndepOn_id with hb
  set b' : Module.Basis I F (F ⊗[k] T) := b.baseChange F with hb'
  have hmem : ∀ i : ι, x i ∈ I := fun i =>
    hx.linearIndepOn_id.subset_extend _ (Set.mem_range_self i)
  set v' : ι → I := fun i => ⟨x i, hmem i⟩ with hv'def
  have hbval : ∀ j : I, b j = (j : T) := fun j => Module.Basis.extend_apply_self _ j
  have hv' : b' ∘ v' = fun i => (1 : F) ⊗ₜ[k] x i := by
    funext i
    simp [hb', v', Module.Basis.baseChange_apply, hbval]
  have h_inj : Function.Injective v' := by
    intro i j hij
    exact hx.injective (congrArg Subtype.val hij)
  rw [← hv']
  exact b'.linearIndependent.comp _ h_inj

/-- **`padic_indep` at the frame**: a `k`-independent family in `T`
gives an `F`-independent family of endomorphisms of the frame. -/
theorem linearIndependent_frameAction {ι : Type*} (x : ι → T)
    (hx : LinearIndependent k x) :
    LinearIndependent F (fun i => frameAction k F T (x i)) := by
  classical
  have h1 : LinearIndependent F (fun i => (1 : F) ⊗ₜ[k] x i) :=
    linearIndependent_one_tmul x hx
  have := h1.map' (frameMul (k := k) (F := F) (T := T)).toLinearMap
    (LinearMap.ker_eq_bot.mpr frameMul_injective)
  exact this

end HeckeFrame

end GaloisRepresentation.Modularity
