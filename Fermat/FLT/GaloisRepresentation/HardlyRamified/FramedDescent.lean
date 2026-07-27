/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix

/-!
# Framed descent: rebuilding a framed representation over a subring

Two purely FORMAL steps of Carayol's Théorème 1, stated over a VARIABLE base
number field and factored out of both `HardlyRamified/HilbertModularity.lean`
and `HardlyRamified/Deformation.lean`.

* `exists_framedGaloisRep_toMatrix'_map_eq_of_forall_mem` — a family of
  matrices over `B` that is unital, multiplicative, continuous entrywise and
  has all its entries in a subring `C ⊆ B` IS the entrywise image of a genuine
  `FramedGaloisRep F C (Fin 2)`.
* `exists_conj_baseChange_of_matrix` — an invertible `E` over `B`
  intertwining the `ψ`-image of a framed representation over `R` with one over
  `B` exhibits the base change `ρ ⊗ B` as the second, after the change of
  framing given by `E`.

Neither statement involves any arithmetic, any local condition or any trace
subring: they are the plumbing that turns Carayol's matrix-level conclusion
into the `∃ ρ' ∃ e` shape the deformation files use.

## Why this module exists

Both lemmas were written twice — hard-coded to `ℚ` in `Deformation.lean` and
in an `F`-variable copy in `HilbertModularity.lean` — because
`Deformation.lean` `public import`s `HilbertModularity.lean` and so cannot be
imported back from it. Nothing in either statement or proof mentions the base
field beyond carrying it as a parameter, so the copies are removed by putting
the `F`-variable versions HERE, upstream of both. The `ℚ`-level call sites
instantiate `F := ℚ` by unification and are otherwise untouched.

The module deliberately imports only `GaloisRep.lean` and mathlib, so it adds
nothing to the import cone of either consumer.
-/

@[expose] public section

open scoped NumberField

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- **A matrix-valued representation with entries in a subring descends to
that subring** (PROVEN 2026-07-26).

A family of matrices `Φ : Γ F → M₂(B)` that is unital, multiplicative,
continuous entrywise, and whose entries all lie in a subring `C ⊆ B`, is the
entrywise image of a genuine `FramedGaloisRep F C (Fin 2)`.

Proof. The entrywise corestriction `G g := ⟨Φ g i j, _⟩` is a monoid
homomorphism into `M₂(C)` because `Matrix.map` along the injective inclusion
`C.subtype` reflects both the unit and the product. Continuity is the only
delicate point, because `GaloisRep` demands continuity INTO `Module.End C (C²)`
for the MODULE topology, which is the FINEST topology making the module
topological — so maps into it are not continuous for free. It is obtained by
factoring through matrices: `M₂(C)` carries the module topology, being a finite
product of copies of `C`, so the `C`-linear `Matrix.toLin'` out of it is
automatically continuous. -/
theorem exists_framedGaloisRep_toMatrix'_map_eq_of_forall_mem
    {F : Type*} [Field F] [NumberField F]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (C : Subring B)
    (Φ : Γ F → Matrix (Fin 2) (Fin 2) B)
    (hcont : ∀ i j, Continuous fun g => Φ g i j)
    (hone : Φ 1 = 1)
    (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h)
    (hmem : ∀ g i j, Φ g i j ∈ C) :
    ∃ τ : FramedGaloisRep F C (Fin 2),
      ∀ g, (LinearMap.toMatrix' (τ g)).map C.subtype = Φ g := by
  classical
  letI := moduleTopology C (Module.End C (Fin 2 → C))
  haveI hMT : IsModuleTopology C (Module.End C (Fin 2 → C)) := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End C (Fin 2 → C)) :=
    IsModuleTopology.toContinuousAdd C (Module.End C (Fin 2 → C))
  haveI : IsModuleTopology C (Matrix (Fin 2) (Fin 2) C) :=
    inferInstanceAs (IsModuleTopology C (Fin 2 → Fin 2 → C))
  -- entrywise corestriction of `Φ` to `C`
  set G : Γ F → Matrix (Fin 2) (Fin 2) C :=
    fun g => Matrix.of fun i j => (⟨Φ g i j, hmem g i j⟩ : C)
  have hGmap : ∀ g, (G g).map C.subtype = Φ g := by
    intro g; ext i j; rfl
  -- `Matrix.map` along the injective inclusion is injective
  have hinj : Function.Injective
      (fun M : Matrix (Fin 2) (Fin 2) C => M.map C.subtype) := by
    intro M N hMN
    ext i j
    exact congrFun (congrFun hMN i) j
  have hGone : G 1 = 1 := by
    refine hinj ?_
    show (G 1).map C.subtype = (1 : Matrix (Fin 2) (Fin 2) C).map C.subtype
    rw [hGmap, hone, Matrix.map_one C.subtype (map_zero _) (map_one _)]
  have hGmul : ∀ g h, G (g * h) = G g * G h := by
    intro g h
    refine hinj ?_
    show (G (g * h)).map C.subtype = ((G g) * (G h)).map C.subtype
    rw [hGmap, hmul, Matrix.map_mul, hGmap, hGmap]
  have hGcont : Continuous G := by
    refine continuous_matrix fun i j => ?_
    exact continuous_induced_rng.mpr (hcont i j)
  have htolin : Continuous
      (Matrix.toLin' (R := C) (m := Fin 2) (n := Fin 2)) :=
    IsModuleTopology.continuous_of_linearMap
      (Matrix.toLin' (R := C) (m := Fin 2) (n := Fin 2)).toLinearMap
  refine ⟨⟨⟨⟨fun g => Matrix.toLin' (G g), ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show Matrix.toLin' (G 1) = 1
    rw [hGone, Matrix.toLin'_one]
    rfl
  · intro g h
    show Matrix.toLin' (G (g * h)) = Matrix.toLin' (G g) * Matrix.toLin' (G h)
    rw [hGmul, Matrix.toLin'_mul]
    rfl
  · exact htolin.comp hGcont
  · intro g
    show (LinearMap.toMatrix' (Matrix.toLin' (G g))).map C.subtype = Φ g
    rw [LinearMap.toMatrix'_toLin']
    exact hGmap g

open scoped TensorProduct Matrix in
/-- **A conjugating matrix turns a base change into a change of framing**
(PROVEN 2026-07-26).

If `E` is an invertible matrix over `B` intertwining the `ψ`-image of a framed
representation `ρ` over `R` with a framed representation `σ` over `B`, then the
base change `ρ ⊗ B` is `σ` after the change of framing given by `E`. -/
theorem exists_conj_baseChange_of_matrix
    {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (ψ : R →+* B) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep F R (Fin 2)) (σ : FramedGaloisRep F B (Fin 2))
    (E : Matrix (Fin 2) (Fin 2) B) (hE : IsUnit E.det)
    (hconj : ∀ g : Γ F,
      E * (LinearMap.toMatrix' (ρ g)).map ⇑ψ =
        (LinearMap.toMatrix' (σ g)) * E) :
    letI : Algebra R B := ψ.toAlgebra
    letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
      (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
    ∃ e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B),
      (ρ.baseChange B).conj e = σ := by
  letI : Algebra R B := ψ.toAlgebra
  letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  haveI : Invertible E := Matrix.invertibleOfIsUnitDet E hE
  set e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B) :=
    (TensorProduct.piScalarRight R B B (Fin 2)).trans
      (Matrix.toLinearEquiv' E inferInstance) with he
  -- the scalar action of `R` on `B` is `ψ`
  have hsmul : ∀ (r : R) (b : B), r • b = ψ r * b := fun r b => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  -- `e` on a simple tensor is `E` applied to the `ψ`-image, scaled by `b`
  have hetmul : ∀ (b : B) (w : Fin 2 → R),
      e (b ⊗ₜ[R] w) = b • (E *ᵥ (fun j => ψ (w j))) := by
    intro b w
    rw [he]
    show E *ᵥ (TensorProduct.piScalarRight R B B (Fin 2) (b ⊗ₜ[R] w)) = _
    rw [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rw [show (fun j => w j • b) = b • (fun j => ψ (w j)) from by
      funext j
      rw [hsmul]
      show ψ (w j) * b = b * ψ (w j)
      rw [mul_comm]]
    exact Matrix.mulVec_smul E b _
  refine ⟨e, GaloisRep.ext fun g => ?_⟩
  rw [GaloisRep.conj_apply]
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply_apply]
  -- the identity on simple tensors, extended by linearity
  have key : ∀ x : B ⊗[R] (Fin 2 → R),
      e ((ρ.baseChange B) g x) = σ g (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b w =>
      rw [GaloisRep.baseChange_tmul, hetmul, hetmul]
      have hmap : (fun j => ψ ((ρ g w) j)) =
          (LinearMap.toMatrix' (ρ g)).map ⇑ψ *ᵥ (fun j => ψ (w j)) := by
        funext i
        rw [show (ρ g w) = LinearMap.toMatrix' (ρ g) *ᵥ w from
          (LinearMap.toMatrix'_mulVec (ρ g) w).symm]
        exact RingHom.map_mulVec ψ (LinearMap.toMatrix' (ρ g)) w i
      rw [hmap, Matrix.mulVec_mulVec]
      rw [show σ g (b • (E *ᵥ (fun j => ψ (w j)))) =
          b • (LinearMap.toMatrix' (σ g) *ᵥ (E *ᵥ (fun j => ψ (w j)))) from by
        rw [map_smul, ← LinearMap.toMatrix'_mulVec (σ g)]]
      rw [Matrix.mulVec_mulVec, hconj g]
  rw [key (e.symm v), LinearEquiv.apply_symm_apply]

end GaloisRepresentation
