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
import Mathlib.Topology.Algebra.Ring.Compact
-- `IsLocalRing.isOpen_maximalIdeal` and
-- `IsLocalRing.finite_residueField_of_compactSpace`, used in the residue
-- package

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
      Module.rank kk (kk ⊗[R] V) = 2 := by
  -- `3` is in the maximal ideal of `ℤ₃`
  have h3Z : (3 : ℤ_[3]) ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PadicInt.not_isUnit_iff]
    have h : ‖((3 : ℕ) : ℤ_[3])‖ = ((3 : ℕ) : ℝ)⁻¹ := PadicInt.norm_p
    have h2 : ((3 : ℕ) : ℤ_[3]) = (3 : ℤ_[3]) := by norm_cast
    rw [h2] at h
    rw [h]
    norm_num
  -- `3` is not a unit in `R`: otherwise `R = 3R` and Nakayama over `ℤ₃`
  -- forces `R = 0`, contradicting nontriviality of the local ring.
  have h3mem : (3 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h3u
    have h3R : (algebraMap ℤ_[3] R) 3 = (3 : R) := by
      rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_cast, map_natCast]
      norm_cast
    have htop : (⊤ : Submodule ℤ_[3] R) ≤
        (IsLocalRing.maximalIdeal ℤ_[3]) • (⊤ : Submodule ℤ_[3] R) := by
      intro r _
      obtain ⟨u, hu⟩ := h3u.exists_right_inv
      have hr : r = (3 : ℤ_[3]) • (u * r) := by
        rw [Algebra.smul_def, h3R, ← mul_assoc, hu, one_mul]
      rw [hr]
      exact Submodule.smul_mem_smul h3Z trivial
    have hbot : (⊤ : Submodule ℤ_[3] R) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal ℤ_[3]) ⊤
        (Module.finite_def.mp inferInstance) htop
        (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have h01 : (1 : R) = 0 := by
      have hmem : (1 : R) ∈ (⊤ : Submodule ℤ_[3] R) := trivial
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    exact one_ne_zero h01
  -- `R` is a Noetherian ring (module-finite over the Noetherian `ℤ₃`)
  haveI hNoeth : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  -- `R` is compact Hausdorff: transport along a `ℤ₃`-basis, since linear
  -- maps between module-topology modules are continuous both ways
  let bR := Module.Free.chooseBasis ℤ_[3] R
  let eR : R ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    bR.equivFun
  have hcont₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcont₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let hom : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  haveI : CompactSpace R := hom.symm.compactSpace
  haveI : T2Space R := hom.symm.symm.isEmbedding.t2Space
  -- openness of the maximal ideal and finiteness of the residue field
  have hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) :=
    IsLocalRing.isOpen_maximalIdeal R
  haveI hfinres : Finite (IsLocalRing.ResidueField R) :=
    IsLocalRing.finite_residueField_of_compactSpace
  -- the residue field with the discrete topology
  letI : TopologicalSpace (IsLocalRing.ResidueField R) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField R) := ⟨rfl⟩
  haveI : IsTopologicalRing (IsLocalRing.ResidueField R) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_mul := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  letI algZ3 : Algebra ℤ_[3] (IsLocalRing.ResidueField R) :=
    ((algebraMap R (IsLocalRing.ResidueField R)).comp
      (algebraMap ℤ_[3] R)).toAlgebra
  haveI hST : IsScalarTower ℤ_[3] R (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  -- the residue map is continuous (the open kernel makes it locally
  -- constant), hence the scalar action is continuous
  have hresid_cont : Continuous (algebraMap R (IsLocalRing.ResidueField R)) := by
    refine continuous_def.mpr fun s _ => ?_
    have : (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' s =
        ⋃ y ∈ s, (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' {y} := by
      ext r
      simp
    rw [this]
    refine isOpen_biUnion fun y hy => ?_
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : R,
        algebraMap R (IsLocalRing.ResidueField R) r₀ = y := by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective y
    have hcoset : (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' {y} =
        (fun x => r₀ + x) '' ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
      ext r
      constructor
      · intro hr
        refine ⟨r - r₀, ?_, by ring⟩
        have h1 : algebraMap R (IsLocalRing.ResidueField R) (r - r₀) = 0 := by
          rw [map_sub]
          have h2 : algebraMap R (IsLocalRing.ResidueField R) r = y := hr
          have h3 : algebraMap R (IsLocalRing.ResidueField R) r₀ = y := hr₀
          rw [h2, h3, sub_self]
        rwa [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq,
          IsLocalRing.ker_residue] at h1
      · rintro ⟨m, hm, rfl⟩
        have h1 : algebraMap R (IsLocalRing.ResidueField R) m = 0 := by
          rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq,
            IsLocalRing.ker_residue]
          exact hm
        show algebraMap R (IsLocalRing.ResidueField R) (r₀ + m) = y
        rw [map_add, h1, add_zero, hr₀]
    rw [hcoset]
    exact (Homeomorph.addLeft r₀).isOpenMap _ hopen
  haveI hCS : ContinuousSMul R (IsLocalRing.ResidueField R) := by
    constructor
    have : (fun p : R × IsLocalRing.ResidueField R => p.1 • p.2) =
        (fun p : IsLocalRing.ResidueField R × IsLocalRing.ResidueField R =>
          p.1 * p.2) ∘ (fun p : R × IsLocalRing.ResidueField R =>
          (algebraMap R (IsLocalRing.ResidueField R) p.1, p.2)) := by
      funext p
      simp [Algebra.smul_def]
    rw [this]
    exact continuous_of_discreteTopology.comp
      ((hresid_cont.comp continuous_fst).prodMk continuous_snd)
  refine ⟨IsLocalRing.ResidueField R, inferInstance, hfinres, algZ3,
    inferInstance, inferInstance, inferInstance, inferInstance, hCS, hST,
    (by rw [IsLocalRing.ResidueField.algebraMap_eq]
        exact IsLocalRing.residue_surjective), hopen,
    (by rw [IsLocalRing.ResidueField.algebraMap_eq]
        exact IsLocalRing.ker_residue), ?_⟩
  -- the rank transfers along the base change
  rw [Module.rank_baseChange, hV]
  simp

set_option warn.sorry false in
/-- **Degenerate flatness over the trivial quotient** (sorry node): a Galois
representation on a subsingleton module has a flat prolongation at `3` — the
trivial group scheme `Spec 𝒪ᵥ` works, its geometric points being the single
algebra map matched with the single element of the space. -/
theorem hasFlatProlongationAt_of_subsingleton {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    [Subsingleton M'] (ρ' : GaloisRep ℚ A' M') :
    ρ'.HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **The residual space identification** (sorry node): the double base
change `(kk ⧸ ⊥) ⊗_kk (kk ⊗_R V)` is `Γ ℚ₃`-equivariantly isomorphic to
`(R ⧸ 𝔪) ⊗_R V` — the quotient-by-`⊥` collapses, and `kk ≅ R ⧸ 𝔪` along the
(surjective, kernel-`𝔪`) residue map transports the coefficients. Content:
tensor associativity/collapse plus transport along the ring isomorphism
induced by `hsurj`/`hker` (`RingHom.quotientKerEquivOfSurjective`). -/
theorem flat_space_equiv_residue {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R)
    {ρ : GaloisRep ℚ R V} :
    ∃ e : ((((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space ≃+
      ((ρ.baseChange (R ⧸ IsLocalRing.maximalIdeal R)).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space),
      ∀ (g : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
        (x : (((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space),
        e (g • x) = g • e x :=
  sorry

/-- **Flatness transfers to the residue field** (DERIVED 2026-07-18 from the
space identification and the degenerate-flatness leaf, through
`HasFlatProlongationAt.of_equiv`): the ideals of the discrete field `kk` are
`⊥` and `⊤`; the `⊥` case is the `I = 𝔪` instance of `ρ.IsFlatAt`
transported along the equivariant space isomorphism, and the `⊤` case is
degenerate. -/
theorem isFlatAt_baseChange_residue {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R)
    {ρ : GaloisRep ℚ R V}
    (hflat : ρ.IsFlatAt Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :
    (ρ.baseChange kk).IsFlatAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat := by
  constructor
  intro I hI
  rcases Ideal.eq_bot_or_top I with rfl | rfl
  · -- `I = ⊥`: transport the `𝔪`-instance of `hflat` along the space iso
    obtain ⟨e, he⟩ := flat_space_equiv_residue kk hsurj hker (ρ := ρ)
    refine (hflat.cond (IsLocalRing.maximalIdeal R) hopen).of_equiv _ e.symm ?_
    intro g x
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]
  · -- `I = ⊤`: the trivial quotient ring, degenerate flatness
    letI : Subsingleton (kk ⧸ (⊤ : Ideal kk)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    letI : Subsingleton ((kk ⧸ (⊤ : Ideal kk)) ⊗[kk] (kk ⊗[R] V)) :=
      Module.subsingleton (kk ⧸ (⊤ : Ideal kk)) _
    exact hasFlatProlongationAt_of_subsingleton _

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
    (_hsurj : Function.Surjective (algebraMap R kk))
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
        (∀ g' : Γ ℚ_[2], δ g' * δ g' = 1) := by
  obtain ⟨π, hπsurj, δ, h⟩ := htame
  -- the canonical identification `kk ⊗[R] R ≃ₗ[kk] kk`
  let e : (kk ⊗[R] R) ≃ₗ[kk] kk := TensorProduct.AlgebraTensorModule.rid R kk kk
  -- the base-changed projection and character
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange kk π, ?_,
    (δ.baseChange kk).conj e, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · intro g w
    refine ⟨?_, ?_, ?_⟩
    · -- equivariance, by linearity on simple tensors
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have h1 := (h g v).1
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [show ((ρ.baseChange kk).map (algebraMap ℚ ℚ_[2])) g (c ⊗ₜ v) =
          c ⊗ₜ ((ρ.map (algebraMap ℚ ℚ_[2])) g v) from rfl,
          LinearMap.baseChange_tmul, h1,
          GaloisRep.conj_apply, LinearMap.baseChange_tmul]
        rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.rid_symm_apply,
          show ((δ.baseChange kk) g : Module.End kk (kk ⊗[R] R)) =
            LinearMap.baseChange kk (δ g) from rfl,
          LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [show (δ g) (π v) = π v • (δ g) 1 from by
          conv_lhs => rw [show (π v : R) = π v • (1 : R) from by
            rw [smul_eq_mul, mul_one]]
          rw [map_smul]]
        simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
          mul_comm]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    · -- unramifiedness: the kernel only grows under base change + conj
      intro σ hσ
      have hδσ : δ σ = 1 := (h 1 0).2.1 hσ
      have : (δ.baseChange kk).conj e σ = 1 := by
        rw [GaloisRep.conj_apply]
        rw [show (δ.baseChange kk) σ =
          LinearMap.baseChange kk (δ σ) from rfl, hδσ]
        refine LinearMap.ext fun c => ?_
        simp
      exact this
    · -- the quadratic condition transfers through the monoid hom
      intro g'
      have hsq : δ g' * δ g' = 1 := (h 1 0).2.2 g'
      calc (δ.baseChange kk).conj e g' * (δ.baseChange kk).conj e g'
          = (δ.baseChange kk).conj e (g' * g') := (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply]
            rw [show (δ.baseChange kk) (g' * g') =
              LinearMap.baseChange kk (δ (g' * g')) from rfl,
              map_mul δ, hsq]
            refine LinearMap.ext fun c => ?_
            simp

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
    exact isFlatAt_baseChange_residue kk hsurj hopen hker hρ.isFlat
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
