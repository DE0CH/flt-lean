/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Claude
-/
module

public import Fermat.FLT.Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Fermat.FLT.Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Complements on the coinduced resolutions computing continuous group cohomology

This file develops the API for the standard (coinduced) resolutions that the cup product
needs.

## Main definitions

* `ContRepresentation.resolutionCLM ρ2 ρ3 u i`: the functorial extension of a (not necessarily
  equivariant) continuous linear map `u : M2 →L[k] M3` to the `i`-th level of the standard
  resolutions.
* `ContRepresentation.resolutionXCast X h`: transport between two levels of the standard
  resolution along an equality of indices, as a continuous linear map.
* `ContRepresentation.invariantsObjIHom ρ2 ρ3 n r`: the comparison morphism from the invariants
  of the internal hom of two levels of the coinduced resolutions to the internal hom of the
  corresponding homogeneous cochains.

## Provenance and pin-drift audit

Vendored from `~/cs/FLT`, file
`FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` (author Edison Xie),
lines 1–200 — the half of that file which our 2026-07-27 port did NOT take, because
`cohomologyIsoQuot` does not need it and the cup product does. The half that WAS taken lives
in `Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`; the two
are disjoint, so there is no duplicate declaration between them.

**ONE proof change against our pin `a3364fa` / toolchain `v4.32.0-rc1`.** The reference uses
the `lia` tactic in `resolutionXCast_apply` and `d_hom_resolutionXCast`; the 2026-07-27 audit
flagged it as possibly absent from our toolchain and dodged the question by not vendoring
these lemmas. Both goals are linear arithmetic over `ℕ`, so `omega` discharges them, and that
is what is written here. Nothing else needed adjusting.

Material destined for `Mathlib.RepresentationTheory.Homological.ContCohomology.Basic`.
-/

@[expose] public section

universe u v w

open CategoryTheory ContinuousLinearMap.CompactOpen

namespace ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

open TopRep

section Resolution

variable {M2 M3 : Type (max v w)}
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ2 : ContRepresentation k G M2) (ρ3 : ContRepresentation k G M3)

/-- The functorial extension of a continuous linear map `u : M2 →L[k] M3` (not necessarily
equivariant) to the `i`-th level of the standard resolutions, applying `u` pointwise under the
iterated `C(G, ·)`. -/
def resolutionCLM (u : M2 →L[k] M3) :
    (i : ℕ) → resolutionX (of ρ2) i →L[k] resolutionX (of ρ3) i
  | 0 => u
  | i + 1 => (resolutionCLM u i).compLeftContinuous k G

@[simp]
lemma resolutionCLM_zero_apply (u : M2 →L[k] M3) (v : M2) :
    resolutionCLM ρ2 ρ3 u 0 v = u v := rfl

@[simp]
lemma resolutionCLM_succ_apply (u : M2 →L[k] M3) (i : ℕ)
    (F : resolutionX (of ρ2) (i + 1)) (g : G) :
    resolutionCLM ρ2 ρ3 u (i + 1) F g = resolutionCLM ρ2 ρ3 u i (F g) := rfl

lemma resolutionCLM_add (u w : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (u + w) i = resolutionCLM ρ2 ρ3 u i + resolutionCLM ρ2 ρ3 w i := by
  induction i with
  | zero => rfl
  | succ i ih => ext F g; exact congr($(ih) (F g))

lemma resolutionCLM_smul (c : k) (u : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (c • u) i = c • resolutionCLM ρ2 ρ3 u i := by
  induction i with
  | zero => rfl
  | succ i ih => ext F g; exact congr($(ih) (F g))

/-- Conjugating `u : M2 →L[k] M3` by the representations corresponds to conjugating
`resolutionCLM u` by the coinduced actions on the resolutions. -/
lemma resolutionCLM_conj (h : G) (u : M2 →L[k] M3) (i : ℕ) :
    resolutionCLM ρ2 ρ3 (ρ3 h ∘L u ∘L ρ2 h⁻¹) i =
      (resolutionX (of ρ3) i).ρ h ∘L resolutionCLM ρ2 ρ3 u i ∘L
        (resolutionX (of ρ2) i).ρ h⁻¹ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext F g
    change resolutionCLM ρ2 ρ3 (ρ3 h ∘L u ∘L ρ2 h⁻¹) i (F g) =
      (resolutionX (of ρ3) i).ρ h (resolutionCLM ρ2 ρ3 u i
        ((resolutionX (of ρ2) i).ρ h⁻¹ (F ((h⁻¹)⁻¹ * (h⁻¹ * g)))))
    rw [inv_inv, mul_inv_cancel_left]
    exact congr($(ih) (F g))

/-- Transport between two levels of the standard resolution along an equality of indices, as a
continuous linear map. -/
def resolutionXCast (X : TopRep k G) {i j : ℕ} (h : i = j) :
    ↥(resolutionX X i) →L[k] ↥(resolutionX X j) :=
  h ▸ ContinuousLinearMap.id k ↥(resolutionX X i)

lemma resolutionXCast_apply (X : TopRep k G) {i j : ℕ} (h : i + 1 = j + 1)
    (F : ↥(resolutionX X (i + 1))) (x : G) :
    resolutionXCast X h F x = resolutionXCast X (by omega : i = j) (F x) := by
  obtain rfl : i = j := by omega
  rfl

lemma resolutionXCast_trans (X : TopRep k G) {i j l : ℕ} (h1 : i = j) (h2 : j = l)
    (y : ↥(resolutionX X i)) :
    resolutionXCast X h2 (resolutionXCast X h1 y) = resolutionXCast X (h1.trans h2) y := by
  subst h1; subst h2; rfl

lemma d_hom_resolutionXCast (X : TopRep k G) {i j : ℕ} (h : i = j) (y : ↥(resolutionX X i)) :
    (d X j).hom (resolutionXCast X h y) =
      resolutionXCast X (by omega : i + 1 = j + 1) ((d X i).hom y) := by
  subst h; rfl

/-- The zeroth differential of the standard resolution is the constant-function embedding. -/
lemma d_hom_zero (X : TopRep k G) (v : ↥X) :
    (d X 0).hom v = ContinuousMap.const G v := rfl

/-- The pointwise formula for the differentials of the standard resolution. -/
lemma d_hom_succ_apply (X : TopRep k G) (i : ℕ) (F : ↥(resolutionX X (i + 1))) (x : G) :
    (d X (i + 1)).hom F x = F - (d X i).hom (F x) := rfl

/-- The differentials of the standard resolutions are compatible with the functorial extension
`resolutionCLM` of a continuous linear map. -/
lemma resolutionCLM_comp_d (u : M2 →L[k] M3) (i : ℕ) (y : ↥(resolutionX (of ρ2) i)) :
    (d (of ρ3) i).hom (resolutionCLM ρ2 ρ3 u i y) =
      resolutionCLM ρ2 ρ3 u (i + 1) ((d (of ρ2) i).hom y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    ext x : 1
    calc (d (of ρ3) (i + 1)).hom (resolutionCLM ρ2 ρ3 u (i + 1) y) x
        = resolutionCLM ρ2 ρ3 u (i + 1) y -
            (d (of ρ3) i).hom (resolutionCLM ρ2 ρ3 u i (y x)) := by
          rw [d_hom_succ_apply, resolutionCLM_succ_apply]
      _ = resolutionCLM ρ2 ρ3 u (i + 1) y -
            resolutionCLM ρ2 ρ3 u (i + 1) ((d (of ρ2) i).hom (y x)) := by rw [ih]
      _ = resolutionCLM ρ2 ρ3 u (i + 1) (y - (d (of ρ2) i).hom (y x)) := (map_sub _ _ _).symm
      _ = resolutionCLM ρ2 ρ3 u (i + 1 + 1) ((d (of ρ2) (i + 1)).hom y) x := by
          rw [resolutionCLM_succ_apply, d_hom_succ_apply, map_sub]

/-- The comparison morphism from the invariants of the internal hom of two levels of the
coinduced resolutions to the internal hom of the corresponding homogeneous cochains, restricting
an equivariant continuous linear map to the invariants on both sides. -/
abbrev invariantsObjIHom (n r : ℕ) : (invariantsFunctor k G).obj
    (((of ρ2).resolution'.X n).iHom ((of ρ3).resolution'.X r)) ⟶
    ((of ρ2).homogeneousCochains.X n).linHom ((of ρ3).homogeneousCochains.X r) :=
  TopModuleCat.ofHom {
    toFun := fun ⟨F, hF⟩ ↦ F.restrict fun x hx g ↦ by
      have h1 : ((of ρ3).resolution'.X r).ρ g (F (((of ρ2).resolution'.X n).ρ g⁻¹ x)) = F x :=
        congr($(hF g) x)
      rwa [hx g⁻¹] at h1
    map_add' _ _ := by ext x; rfl
    map_smul' _ _ := by ext x; rfl
    cont := by
      refine continuous_induced_rng.2 ?_
      refine (ContinuousMap.isInducing_postcomp
        (⟨_, continuous_subtype_val⟩ :
          C(((of ρ3).resolution'.X r).ρ.invariants, (of ρ3).resolution'.X r))
        Topology.IsInducing.subtypeVal).continuous_iff.2 ?_
      have hι : Continuous fun F : ↥((of ρ2).resolution'.X n) →L[k] ↥((of ρ3).resolution'.X r) ↦
          (⟨F.toFun, F.cont⟩ : C((of ρ2).resolution'.X n, (of ρ3).resolution'.X r)) :=
        continuous_induced_dom
      exact (ContinuousMap.continuous_precomp
        (⟨_, continuous_subtype_val⟩ :
          C(((of ρ2).resolution'.X n).ρ.invariants, (of ρ2).resolution'.X n))).comp
        (hι.comp continuous_subtype_val) }

/-- Applying an `eqToHom` reindexing morphism between internal homs of resolution levels to
elements is transport along the index equality. -/
lemma eqToHom_iHom_apply (A : TopRep k G) {i j : ℕ} (h : i = j)
    (pf : A.iHom (resolutionX (.of ρ3) i) = A.iHom (resolutionX (.of ρ3) j))
    (Φ : ↥(A.iHom (resolutionX (.of ρ3) i))) (τ : ↥A) :
    (eqToHom pf) Φ τ = resolutionXCast (.of ρ3) h (Φ τ) := by
  subst h
  rfl

end Resolution

end ContRepresentation
