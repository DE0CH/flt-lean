/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree
-- `mod_three` (the mod-3 classification), consumed by the derivation of
-- `exists_frobenius_triangular` below
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- `LinearMap.det_baseChange`, used in the determinant transfer of
-- `exists_residual_isHardlyRamified`

/-!
# 3-adic hardly ramified representations

Three-adic input results for the analysis of hardly ramified families:
properties of `R`-linear representations on a finite `ℤ_[3]`-module which
are hardly ramified at 3.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

open scoped TensorProduct

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

-- TODO -- make some API for "I have a rank 1 quotient where Galois acts trivially"
-- e.g. this implies trace(Frob_p) is (1+p)

set_option warn.sorry false in
/-- **The residue package** (sorry node): a local, topological,
module-finite `ℤ₃`-algebra `R` has a residue field `kk` — finite, of
characteristic `3`, discrete — with a surjective continuous
`ℤ₃`-algebra map `R → kk` whose kernel is the (open) maximal ideal, and
base change along it preserves the rank. Content: `kk := R ⧸ 𝔪` with the
quotient instances; finiteness from module-finiteness over `ℤ₃` and
`𝔪 ⊇ 3R`; openness of `𝔪` from the module topology. -/
theorem exists_residue_package {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) :
    ∃ (kk : Type u) (_ : Field kk) (_ : Finite kk) (_ : Algebra ℤ_[3] kk)
      (_ : TopologicalSpace kk) (_ : DiscreteTopology kk)
      (_ : IsTopologicalRing kk) (_ : Algebra R kk)
      (_ : ContinuousSMul R kk) (_ : IsScalarTower ℤ_[3] R kk),
      Function.Surjective (algebraMap R kk) ∧
      IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ∧
      RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R ∧
      Module.rank kk (kk ⊗[R] V) = 2 :=
  sorry

set_option warn.sorry false in
/-- **Flatness transfers to the residue field** (sorry node): if `ρ` is
flat at `3` in the open-ideal sense, its base change to the residue
field (the quotient by the open maximal ideal) is flat at `3`. Content:
the open ideals of the discrete field `kk` are `⊥` and `⊤`; the `⊥` case
is the `I = 𝔪` instance of `ρ.IsFlatAt` transported along
`kk ≅ R ⧸ 𝔪` and base-change composition. -/
theorem isFlatAt_baseChange_residue {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R)
    {ρ : GaloisRep ℚ R V}
    (hflat : ρ.IsFlatAt Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :
    (ρ.baseChange kk).IsFlatAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **Tameness at `2` transfers to the residue field** (sorry node): the
rank-1 tame quadratic quotient of `ρ` at `2` base-changes to one for the
residual representation. Content: `π ⊗ 1 : kk ⊗ V → kk ⊗ R ≅ kk` and the
pushforward of `δ` along the residue map; the three conditions transfer
by the diagram chase on simple tensors. -/
theorem isTameAtTwo_baseChange_residue {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    {ρ : GaloisRep ℚ R V}
    (htame : ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Γ ℚ_[2], ∀ v : V,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Γ ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (kk ⊗[R] V) →ₗ[kk] kk) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] kk kk),
      ∀ g : Γ ℚ_[2], ∀ v : kk ⊗[R] V,
        π ((ρ.baseChange kk).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Γ ℚ_[2], δ g' * δ g' = 1) :=
  sorry

/-- **Residual hardly-ramifiedness** (DERIVED 2026-07-18 from the
residue package and the flatness/tameness transfer leaves; the
determinant and unramifiedness conditions are proven here directly —
`LinearMap.det_baseChange` and the base-change instance of
`IsUnramifiedAt`): the reduction of a 3-adic hardly ramified
representation modulo the maximal ideal is mod-3 hardly ramified over
the residue field. -/
theorem exists_residual_isHardlyRamified {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (kk : Type u) (_ : Field kk) (_ : Finite kk) (_ : Algebra ℤ_[3] kk)
      (_ : TopologicalSpace kk) (_ : DiscreteTopology kk)
      (_ : IsTopologicalRing kk) (_ : Algebra R kk)
      (_ : ContinuousSMul R kk)
      (_ : Function.Surjective (algebraMap R kk))
      (hVbar : Module.rank kk (kk ⊗[R] V) = 2),
      IsHardlyRamified (show Odd 3 by decide) hVbar (ρ.baseChange kk) := by
  obtain ⟨kk, hField, hFinite, hA3, hTop, hDisc, hTR, hAR, hCS, hST,
    hsurj, hopen, hker, hrank⟩ := exists_residue_package V hV
  letI := hField
  letI := hFinite
  letI := hA3
  letI := hTop
  letI := hDisc
  letI := hTR
  letI := hAR
  letI := hCS
  letI := hST
  refine ⟨kk, hField, hFinite, hA3, hTop, hDisc, hTR, hAR, hCS, hsurj,
    hrank, ?_⟩
  constructor
  · -- the determinant condition maps along the residue map
    intro g
    have hdet : (ρ.baseChange kk).det g =
        algebraMap R kk (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange kk) g) = _
      rw [show ((ρ.baseChange kk) g : Module.End kk (kk ⊗[R] V)) =
        LinearMap.baseChange kk (ρ g) from rfl, LinearMap.det_baseChange]
      rfl
    rw [hdet, hρ.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro p hp hpp
    letI : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      hρ.isUnramified p hp hpp
    infer_instance
  · -- flatness at 3 (sorried transfer leaf)
    exact isFlatAt_baseChange_residue kk hopen hker hρ.isFlat
  · -- tameness at 2 (sorried transfer leaf)
    exact isTameAtTwo_baseChange_residue kk hsurj hρ.isTameAtTwo

set_option warn.sorry false in
/-- **Ordinarity lifting from the residual trivial quotient** (sorry
node — the deformation-theoretic heart of B6c): if the residual
representation admits an equivariant surjection onto the trivial
1-dimensional representation (the output of the mod-3 classification
`mod_three`), then the stable-line structure lifts 3-adically: at every
good prime `p ≥ 5` there is a basis of `V` in which the local Frobenius
acts by `[[p, *], [0, 1]]`. Content: the ordinary deformation argument
(the unramified rank-1 quotient lifts through the complete local ring,
by flatness at 3 and the connected-étale sequence), the diagonal
character is `det ρ` = the 3-adic cyclotomic character
(`IsHardlyRamified.det`), and the cyclotomic character takes the value
`p` at an arithmetic Frobenius at `p ≠ 3`. -/
theorem exists_frobenius_triangular_of_residual_trivial_quotient
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (π : (kk ⊗[R] V) →ₗ[kk] kk) (hπsurj : Function.Surjective π)
    (hπequiv : ∀ g : Γ ℚ, ∀ w : kk ⊗[R] V,
      π ((ρ.baseChange kk) g w) = π w)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    letI v := hp.toHeightOneSpectrumRingOfIntegersRat
    ∃ (b : Module.Basis (Fin 2) R V) (c : R),
      LinearMap.toMatrix b b (ρ.toLocal v (Frob v)) =
        !![(p : R), c; 0, 1] :=
  sorry

/-- **The Frobenius triangularity of a 3-adic hardly ramified
representation at good odd primes** (DERIVED 2026-07-18 by chaining the
residual reduction, the mod-3 classification `mod_three` of
`ModThree.lean`, and the ordinarity lifting): for `p ≥ 5`, there is a
basis of `V` in which the local Frobenius at `p` acts by the triangular
matrix `[[p, *], [0, 1]]` — eigenvalues `p` and `1`. -/
theorem exists_frobenius_triangular {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    letI v := hp.toHeightOneSpectrumRingOfIntegersRat
    ∃ (b : Module.Basis (Fin 2) R V) (c : R),
      LinearMap.toMatrix b b (ρ.toLocal v (Frob v)) =
        !![(p : R), c; 0, 1] := by
  obtain ⟨kk, hField, hFinite, hA3, hTop, hDisc, hTR, hAR, hCS, hsurj,
    hVbar, hHR⟩ := exists_residual_isHardlyRamified V hV hρ
  letI := hField
  letI := hFinite
  letI := hA3
  letI := hTop
  letI := hDisc
  letI := hTR
  letI := hAR
  letI := hCS
  obtain ⟨π, hπsurj, hπequiv⟩ := mod_three (kk ⊗[R] V) hVbar hHR
  exact exists_frobenius_triangular_of_residual_trivial_quotient V hV hρ kk
    hsurj π hπsurj hπequiv p hp hp5

/-- **B6c** (DERIVED 2026-07-18 from the Frobenius triangularity node): a
3-adic hardly ramified representation has `trace(Frob_p) = 1 + p` for all
primes `p ≥ 5` — the trace of the triangular matrix `[[p, *], [0, 1]]` is
`p + 1`, read off through `LinearMap.trace_eq_matrix_trace`. -/
theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (hp : Nat.Prime p) (_hp5 : 5 ≤ p),
      letI v := hp.toHeightOneSpectrumRingOfIntegersRat -- p as a finite place of ℚ
      (ρ.toLocal v (Frob v)).trace _ _ = 1 + p := by
  intro p hp hp5
  obtain ⟨b, c, hb⟩ := exists_frobenius_triangular V hV hρ p hp hp5
  rw [LinearMap.trace_eq_matrix_trace R b, hb, Matrix.trace_fin_two]
  simp [add_comm]

end GaloisRepresentation.IsHardlyRamified
