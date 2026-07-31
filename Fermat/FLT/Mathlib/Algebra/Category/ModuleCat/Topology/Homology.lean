/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Claude
-/
module

public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Fermat.FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Descending bilinear pairings along cokernels of topological modules

This file carries the bilinear half of the reference project's
`FLT/Mathlib/Algebra/Category/ModuleCat/Topology/Homology.lean`:

* `TopModuleCat.cokerDescCLM`: descend a continuous linear map along cokernel projections on
  both sides;
* `TopModuleCat.cokerDescBilinear`: descend a bilinear pairing, bundled as a morphism into the
  internal hom, along cokernel projections in all three slots.

It is what turns the cup product on cocycles into a cup product on cohomology.

## Why the import points at `ContCohomology.Basic`

The universal property `TopModuleCat.cokerDesc` and `cokerπ_eq_zero_iff` that these
constructions rest on were vendored on 2026-07-27 into
`Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` rather than
into a file mirroring the reference project's layout, because that was the only consumer at
the time. Rather than move them — which would rewrite a file other worktrees may be editing —
this file imports them from where they are. When this material goes upstream, `cokerDesc`,
`cokerCongr`, `cyclesIsoKer` and `homologyIsoCoker` belong here and the ContCohomology file
should keep only `bdryKer`/`cohomologyIsoQuot`.

## Provenance

Vendored VERBATIM from `~/cs/FLT` (author Edison Xie); absent from our mathlib pin `a3364fa`
(re-checked 2026-07-31: `grep -rn "cokerDescBilinear\|homOfBilinear" Mathlib/` is empty).

Material destined for `Mathlib.Algebra.Category.ModuleCat.Topology.Homology`.
-/

@[expose] public section

universe u v

namespace TopModuleCat

open CategoryTheory Limits

variable {k : Type u} [CommRing k] [TopologicalSpace k]

section Coker

variable {M N N' P : TopModuleCat.{v} k}

lemma isOpenQuotientMap_cokerπ (φ : M ⟶ N) : IsOpenQuotientMap ⇑(cokerπ φ).hom :=
  Submodule.isOpenQuotientMap_mkQ _

lemma cokerπ_surjective' (φ : M ⟶ N) (q : ↥(coker φ)) : ∃ y, cokerπ φ y = q :=
  cokerπ_surjective φ q

section DescBilinear

variable {M₂ N₂ M₃ N₃ : TopModuleCat.{v} k}

/-- Descend a continuous linear map along cokernel projections on both sides. -/
noncomputable def cokerDescCLM (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (u : ↥N₂ →L[k] ↥N₃)
    (h : ∀ y, cokerπ φ₃ (u (φ₂ y)) = 0) :
    ↥(coker φ₂) →L[k] ↥(coker φ₃) :=
  (cokerDesc φ₂ (ofHom ((cokerπ φ₃).hom ∘L u))
    (ConcreteCategory.hom_ext _ _ fun y ↦ h y)).hom

@[simp]
lemma cokerDescCLM_apply (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (u : ↥N₂ →L[k] ↥N₃)
    (h : ∀ y, cokerπ φ₃ (u (φ₂ y)) = 0) (y : ↥N₂) :
    cokerDescCLM φ₂ φ₃ u h (cokerπ φ₂ y) = cokerπ φ₃ (u y) :=
  congr($(cokerπ_cokerDesc φ₂ (ofHom ((cokerπ φ₃).hom ∘L u))
    (ConcreteCategory.hom_ext _ _ fun z ↦ h z)) y)

variable {N₁ : TopModuleCat.{v} k}

/-- The descended family of continuous linear maps has jointly continuous uncurried form. -/
lemma continuous_cokerDescCLM_uncurry (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃)
    (F : ↥N₁ → (↥N₂ →L[k] ↥N₃)) (h : ∀ σ y, cokerπ φ₃ (F σ (φ₂ y)) = 0)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2) :
    Continuous fun p : ↥N₁ × ↥(coker φ₂) ↦ cokerDescCLM φ₂ φ₃ (F p.1) (h p.1) p.2 :=
  ((IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_cokerπ φ₂)).continuous_comp_iff).1
    ((cokerπ φ₃).hom.continuous.comp hF)

/-- Descend a bilinear pairing, bundled as a morphism into the internal hom, along cokernel
projections in all three slots. -/
noncomputable def cokerDescBilinear {M₁ : TopModuleCat.{v} k}
    (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (F : N₁ ⟶ linHom N₂ N₃)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2)
    (h₁ : ∀ (y : ↥M₁) (τ : ↥N₂), cokerπ φ₃ (F (φ₁ y) τ) = 0)
    (h₂ : ∀ (σ : ↥N₁) (y : ↥M₂), cokerπ φ₃ (F σ (φ₂ y)) = 0) :
    coker φ₁ ⟶ linHom (coker φ₂) (coker φ₃) :=
  cokerDesc φ₁
    (homOfBilinear (fun σ ↦ cokerDescCLM φ₂ φ₃ (F σ) (h₂ σ))
      (fun σ σ' q ↦ by
        obtain ⟨y, rfl⟩ := cokerπ_surjective' φ₂ q
        rw [cokerDescCLM_apply, cokerDescCLM_apply, cokerDescCLM_apply, map_add, add_apply,
          map_add])
      (fun c σ q ↦ by
        obtain ⟨y, rfl⟩ := cokerπ_surjective' φ₂ q
        rw [cokerDescCLM_apply, cokerDescCLM_apply, map_smul, smul_apply, map_smul])
      (continuous_cokerDescCLM_uncurry φ₂ φ₃ F h₂ hF))
    (ConcreteCategory.hom_ext _ _ fun y ↦ ContinuousLinearMap.ext fun q ↦ by
      obtain ⟨τ, rfl⟩ := cokerπ_surjective' φ₂ q
      exact h₁ y τ)

@[simp]
lemma cokerDescBilinear_apply {M₁ : TopModuleCat.{v} k}
    (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (F : N₁ ⟶ linHom N₂ N₃)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2)
    (h₁ : ∀ (y : ↥M₁) (τ : ↥N₂), cokerπ φ₃ (F (φ₁ y) τ) = 0)
    (h₂ : ∀ (σ : ↥N₁) (y : ↥M₂), cokerπ φ₃ (F σ (φ₂ y)) = 0)
    (σ : ↥N₁) (τ : ↥N₂) :
    cokerDescBilinear φ₁ φ₂ φ₃ F hF h₁ h₂ (cokerπ φ₁ σ) (cokerπ φ₂ τ) =
      cokerπ φ₃ (F σ τ) := rfl

end DescBilinear

end Coker

end TopModuleCat
