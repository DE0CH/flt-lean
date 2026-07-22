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

/-- **Degenerate flatness over the trivial quotient** (sorry node): a Galois
representation on a subsingleton module has a flat prolongation at `3` — the
trivial group scheme `Spec 𝒪ᵥ` works, its geometric points being the single
algebra map matched with the single element of the space. -/
theorem hasFlatProlongationAt_of_subsingleton {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    [Subsingleton M'] (ρ' : GaloisRep ℚ A' M') :
    ρ'.HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  set v := Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat with hv
  set Kv := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v with hKv
  set Ov := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
    with hOv
  -- every `Kᵥ`-algebra map out of `Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ ≅ Kᵥ` is the canonical one
  haveI hsub : Subsingleton (Kv ⊗[Ov] Ov →ₐ[Kv] AlgebraicClosure Kv) := by
    constructor
    intro f g
    have hcomp : ∀ h : Kv ⊗[Ov] Ov →ₐ[Kv] AlgebraicClosure Kv,
        h = ((h.comp (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).comp
          (Algebra.TensorProduct.rid Ov Kv Kv).toAlgHom) := by
      intro h
      ext
    rw [hcomp f, hcomp g]
    congr 1
    exact AlgHom.ext fun x =>
      ((f.comp (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).commutes
        x).trans
        ((g.comp
          (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).commutes x).symm
  haveI hspace : Subsingleton (ρ'.toLocal v).Space :=
    inferInstanceAs (Subsingleton M')
  refine ⟨Ov, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, ?_, ?_⟩
  · -- étale generic fibre: base change of the étale identity
    exact inferInstance
  · -- the zero equivariant map into the subsingleton space
    exact
      { toFun := fun _ => 0
        map_smul' := fun g x => (smul_zero g).symm
        map_zero' := rfl
        map_add' := fun a b => (add_zero (0 : M')).symm }
  · constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      refine ⟨Additive.ofMul ((Algebra.ofId Kv (AlgebraicClosure Kv)).comp
        (Algebra.TensorProduct.rid Ov Kv Kv).toAlgHom), ?_⟩
      exact Subsingleton.elim _ y

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
        e (g • x) = g • e x := by
  classical
  -- the coefficient identification `kk ⧸ ⊥ ≃+* R ⧸ 𝔪`
  let ψ₂ : R ⧸ RingHom.ker (algebraMap R kk) ≃+* kk :=
    RingHom.quotientKerEquivOfSurjective hsurj
  let φ : (kk ⧸ (⊥ : Ideal kk)) ≃+* (R ⧸ IsLocalRing.maximalIdeal R) :=
    (RingEquiv.quotientBot kk).trans
      (ψ₂.symm.trans (Ideal.quotEquivOfEq hker))
  have hφalg : ∀ r : R,
      φ (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r) =
        algebraMap R (R ⧸ IsLocalRing.maximalIdeal R) r := by
    intro r
    have h1 : (RingEquiv.quotientBot kk)
        (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r) = algebraMap R kk r := rfl
    have h2 : ψ₂ (Ideal.Quotient.mk _ r) = algebraMap R kk r := rfl
    have h3 : ψ₂.symm (algebraMap R kk r) = Ideal.Quotient.mk _ r := by
      rw [← h2, RingEquiv.symm_apply_apply]
    show (Ideal.quotEquivOfEq hker) (ψ₂.symm ((RingEquiv.quotientBot kk)
      (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r))) = _
    rw [h1, h3]
    rfl
  -- the `R`-linear form of `φ`
  let φlin : (kk ⧸ (⊥ : Ideal kk)) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R) :=
    { φ.toAddEquiv with
      map_smul' := fun r x => by
        show φ (r • x) = r • φ x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφalg] }
  -- assemble: cancel the middle base change, then transport coefficients
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R kk
    (kk ⧸ (⊥ : Ideal kk)) (kk ⧸ (⊥ : Ideal kk)) V
  let e₂ := TensorProduct.congr φlin (LinearEquiv.refl R V)
  refine ⟨e₁.toAddEquiv.trans e₂.toAddEquiv, ?_⟩
  intro g x
  show (e₁.toAddEquiv.trans e₂.toAddEquiv)
      ((((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) g x) =
    (((ρ.baseChange (R ⧸ IsLocalRing.maximalIdeal R)).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) g)
      ((e₁.toAddEquiv.trans e₂.toAddEquiv) x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [show (c ⊗ₜ[kk] (0 : kk ⊗[R] V)) =
        (0 : (kk ⧸ (⊥ : Ideal kk)) ⊗[kk] (kk ⊗[R] V)) from
        TensorProduct.tmul_zero _ _]
      simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add]
      simp only [map_add, ha, hb]
    | tmul d v => rfl

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

/-- **The one-step equivariant lift** (sorry node — the deep arithmetic
core, Serre §5.4/Fontaine, at a single level of the maximal-adic
filtration): an `R`-linear functional on `V` which is Galois-equivariant
modulo `𝔪 ^ (n + 1)` and residually nonvanishing at the marked vector
`v₀` (a vector where the residual trivial-quotient functional `π` is
nonzero) can be corrected to a functional equivariant modulo
`𝔪 ^ (n + 2)`, still residually nonvanishing at `v₀`. Recorded route:
the defect `g ↦ f ∘ ρ g - f` takes values in `Hom(V, 𝔪ⁿ⁺¹)` and,
reduced modulo `𝔪ⁿ⁺²`, is a `1`-cocycle for the contragredient residual
action on `Hom(V̄, 𝔪ⁿ⁺¹/𝔪ⁿ⁺²)` — the residual dual is an extension of
the inverse mod-3 cyclotomic character `ω⁻¹ = ω` by the trivial
character. The hardly ramified conditions (flat at `3`, tame quadratic
at `2`, unramified elsewhere) place its class in the corresponding
Selmer group, which vanishes by Serre's computation for `p = 3` (the
class number of `ℚ(ζ₃)` is `1`; the unit contributions die against the
local conditions at `3` and `2`). A coboundary witness is a correction
`h : V →ₗ[R] R` with values in `𝔪ⁿ⁺¹`; then `f' = f - h` is equivariant
modulo `𝔪ⁿ⁺²` and `f' v₀ = f v₀ - h v₀ ∉ 𝔪` since `h v₀ ∈ 𝔪ⁿ⁺¹ ≤ 𝔪`. -/
theorem exists_equivariant_functional_lift_step
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
    (v₀ : V) (hv₀ : π ((1 : kk) ⊗ₜ[R] v₀) ≠ 0)
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R) :
    ∃ f' : V →ₗ[R] R,
      (∀ (g : Γ ℚ) (v : V),
        f' (ρ g v) - f' v ∈ IsLocalRing.maximalIdeal R ^ (n + 2)) ∧
      f' v₀ ∉ IsLocalRing.maximalIdeal R := by
  sorry

/-- **The equivariant functional lift** (DERIVED 2026-07-22 from the
one-step lift leaf `exists_equivariant_functional_lift_step`; the
level-by-level system is assembled here WITHOUT a compatibility
requirement, by compactness): the residual trivial-quotient functional
lifts through the complete local coefficient ring to a Galois-equivariant
`R`-linear functional on `V` that survives in the residue field. Proof
shape: (i) pick `v₀` with `π (1 ⊗ v₀) ≠ 0` (possible since `π` is onto
and simple tensors generate); (ii) the base approximation is the
coordinate lift of `π` through a basis of `V`, equivariant modulo `𝔪` by
`hπequiv`; (iii) induction with the one-step leaf gives, for every `n`,
a functional equivariant modulo `𝔪ⁿ⁺¹` and residually nonvanishing at
`v₀`; (iv) `R` is compact (finite free over `ℤ₃`, module topology), the
approximants at level `n` form a nonempty closed subset of the compact
coordinate square `R²` (each `𝔪ⁿ⁺¹` is finitely generated, hence a
compact — closed — subset; the nonvanishing locus at `v₀` is closed
since `𝔪` is open), and the sets are nested, so the intersection is
nonempty; (v) a functional in the intersection is equivariant exactly,
by Krull's intersection theorem `⨅ n, 𝔪ⁿ = ⊥`. Note the conclusion is
deliberately weak — no surjectivity and no compatibility with `π` is
demanded, only equivariance plus residual nonvanishing at a single
vector; the consumer upgrades this to a split surjection by the
local-ring unit argument. -/
theorem exists_equivariant_functional_residually_nonzero
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
      π ((ρ.baseChange kk) g w) = π w) :
    ∃ πR : V →ₗ[R] R, (∀ (g : Γ ℚ) (v : V), πR (ρ g v) = πR v) ∧
      ∃ v : V, algebraMap R kk (πR v) ≠ 0 := by
  classical
  -- the kernel of the residue map is the maximal ideal
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  -- the marked vector: `π` cannot vanish on the image of `V`
  have hv₀ex : ∃ v₀ : V, π ((1 : kk) ⊗ₜ[R] v₀) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ w : kk ⊗[R] V, π w = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have hc : c ⊗ₜ[R] v = c • ((1 : kk) ⊗ₜ[R] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hc, map_smul, hcon v, smul_zero]
      | add x y hx hy => rw [map_add, hx, hy, add_zero]
    obtain ⟨w, hw⟩ := hπsurj 1
    exact one_ne_zero (α := kk) (by rw [← hw]; exact hall w)
  obtain ⟨v₀, hv₀⟩ := hv₀ex
  -- a basis of `V`
  have hfinrank : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by rw [hV]; norm_num)
  let b : Module.Basis (Fin 2) R V := Module.finBasisOfFinrankEq R V hfinrank
  -- the base approximation: a coordinate lift of `π` through `b`
  have hlift : ∀ i : Fin 2,
      ∃ r : R, algebraMap R kk r = π ((1 : kk) ⊗ₜ[R] b i) := fun i => hsurj _
  choose rlift hrlift using hlift
  let f₀ : V →ₗ[R] R := ∑ i, rlift i • b.coord i
  -- the reduction of `f₀` computes `π` on the image of `V`
  have hkey : ∀ v : V, algebraMap R kk (f₀ v) = π ((1 : kk) ⊗ₜ[R] v) := by
    intro v
    have hexp : f₀ v = ∑ i, rlift i * b.repr v i := by
      show (∑ i, rlift i • b.coord i) v = _
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => by
        rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr v]
    rw [hexp, map_sum, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsm : (1 : kk) ⊗ₜ[R] (b.repr v i • b i)
        = algebraMap R kk (b.repr v i) • ((1 : kk) ⊗ₜ[R] b i) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
        ← Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]
    rw [map_mul, hrlift i, hsm, map_smul, smul_eq_mul]
    exact mul_comm _ _
  -- level-by-level approximation, assembled by induction from the leaf
  have approx : ∀ n : ℕ, ∃ f : V →ₗ[R] R,
      (∀ (g : Γ ℚ) (v : V),
        f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1)) ∧
      f v₀ ∉ IsLocalRing.maximalIdeal R := by
    intro n
    induction n with
    | zero =>
      refine ⟨f₀, fun g v => ?_, fun hmem => ?_⟩
      · rw [zero_add, pow_one, ← hker, RingHom.mem_ker, map_sub, hkey, hkey,
          show (1 : kk) ⊗ₜ[R] (ρ g v) = (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] v)
            from rfl,
          hπequiv g, sub_self]
      · rw [← hker, RingHom.mem_ker, hkey] at hmem
        exact hv₀ hmem
    | succ n ih =>
      obtain ⟨f, hfeq, hfv⟩ := ih
      exact exists_equivariant_functional_lift_step V hV hρ kk hsurj π
        hπsurj hπequiv v₀ hv₀ n f hfeq hfv
  -- compactness of `R`: transport along a `ℤ₃`-basis
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
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  -- the functionals, coordinatized over the compact square `R²`
  let F : (Fin 2 → R) → (V →ₗ[R] R) := fun a => ∑ i, a i • b.coord i
  have hFapply : ∀ (a : Fin 2 → R) (v : V),
      F a v = ∑ i, a i * b.repr v i := by
    intro a v
    show (∑ i, a i • b.coord i) v = _
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hFcont : ∀ v : V, Continuous fun a : Fin 2 → R => F a v := by
    intro v
    have hrw : (fun a : Fin 2 → R => F a v)
        = fun a : Fin 2 → R => ∑ i, a i * b.repr v i :=
      funext fun a => hFapply a v
    rw [hrw]
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul continuous_const
  have hFrep : ∀ f : V →ₗ[R] R, F (fun i => f (b i)) = f := by
    intro f
    refine b.ext fun j => ?_
    rw [hFapply]
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  -- the nested closed sets of approximate solutions
  let S : ℕ → Set (Fin 2 → R) := fun n =>
    {a | (∀ (g : Γ ℚ) (v : V), F a (ρ g v) - F a v ∈
        IsLocalRing.maximalIdeal R ^ (n + 1)) ∧
      F a v₀ ∉ IsLocalRing.maximalIdeal R}
  have hSclosed : ∀ n : ℕ, IsClosed (S n) := by
    intro n
    have h1 : IsClosed {a : Fin 2 → R | ∀ (g : Γ ℚ) (v : V),
        F a (ρ g v) - F a v ∈ IsLocalRing.maximalIdeal R ^ (n + 1)} := by
      have hrw : {a : Fin 2 → R | ∀ (g : Γ ℚ) (v : V),
          F a (ρ g v) - F a v ∈ IsLocalRing.maximalIdeal R ^ (n + 1)}
          = ⋂ (g : Γ ℚ), ⋂ (v : V),
            (fun a : Fin 2 → R => F a (ρ g v) - F a v) ⁻¹'
              ((IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) : Set R) := by
        ext a
        simp [Set.mem_iInter]
      rw [hrw]
      exact isClosed_iInter fun g => isClosed_iInter fun v =>
        IsClosed.preimage ((hFcont _).sub (hFcont v))
          (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
    have h2 : IsClosed
        {a : Fin 2 → R | F a v₀ ∉ IsLocalRing.maximalIdeal R} := by
      have hrw : {a : Fin 2 → R | F a v₀ ∉ IsLocalRing.maximalIdeal R}
          = (fun a : Fin 2 → R => F a v₀) ⁻¹'
            (((IsLocalRing.maximalIdeal R : Ideal R) : Set R))ᶜ := rfl
      rw [hrw]
      exact IsClosed.preimage (hFcont v₀)
        (isClosed_compl_iff.mpr (IsLocalRing.isOpen_maximalIdeal R))
    exact h1.inter h2
  have hSnonempty : ∀ n : ℕ, (S n).Nonempty := by
    intro n
    obtain ⟨f, hfeq, hfv⟩ := approx n
    refine ⟨fun i => f (b i), fun g v => ?_, ?_⟩
    · rw [hFrep f]
      exact hfeq g v
    · rw [hFrep f]
      exact hfv
  have hSnested : ∀ n : ℕ, S (n + 1) ⊆ S n := by
    intro n a ha
    exact ⟨fun g v => Ideal.pow_le_pow_right (by omega) (ha.1 g v), ha.2⟩
  obtain ⟨alim, halim⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      hSnested hSnonempty ((hSclosed 0).isCompact) hSclosed
  have hmem : ∀ n : ℕ, alim ∈ S n := fun n => Set.mem_iInter.mp halim n
  -- Krull intersection: the limit functional is exactly equivariant
  have hKrull : (⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i) = (⊥ : Ideal R) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
      (Ideal.IsMaximal.ne_top inferInstance)
  refine ⟨F alim, fun g v => ?_, v₀, fun h0 => ?_⟩
  · have hx : F alim (ρ g v) - F alim v ∈
        (⨅ i : ℕ, IsLocalRing.maximalIdeal R ^ i) := by
      rw [Submodule.mem_iInf]
      intro i
      cases i with
      | zero =>
        rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      | succ m => exact (hmem m).1 g v
    rw [hKrull, Submodule.mem_bot] at hx
    exact sub_eq_zero.mp hx
  · exact (hmem 0).2 (hker ▸ RingHom.mem_ker.mpr h0)

/-- **The global triangular form** (DERIVED 2026-07-22 from the
equivariant-functional-lift leaf; Step A's surjectivity upgrade — the
kernel of `R → kk` is the maximal ideal since `kk` is a field and `R` is
local, so residual nonvanishing makes the functional hit a unit — and
Step B's adapted basis — the kernel of the split surjection is finite
flat over the local `R`, hence free of rank `2 - 1 = 1` — are proven
here directly): given the residual trivial-quotient surjection, the
WHOLE representation is triangular in a suitable basis — an extension of
the trivial character by a character `χ` (which the determinant
condition identifies with the cyclotomic character). -/
theorem exists_global_triangular_of_residual_trivial_quotient
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
      π ((ρ.baseChange kk) g w) = π w) :
    ∃ (b : Module.Basis (Fin 2) R V) (χ : Γ ℚ →* R) (cc : Γ ℚ → R),
      ∀ g : Γ ℚ, LinearMap.toMatrix b b (ρ g) = !![χ g, cc g; 0, 1] := by
  classical
  -- **Step A** (DERIVED from the equivariant-functional-lift leaf): the
  -- residual trivial quotient lifts through the complete local ring `R`
  -- to an integral equivariant surjection onto the trivial representation.
  -- The upgrade from residual nonvanishing to surjectivity: the kernel of
  -- `R → kk` is a maximal ideal (`kk` is a field), hence THE maximal ideal
  -- (`R` is local), so a residually nonzero value is a unit.
  have hA : ∃ πR : V →ₗ[R] R, Function.Surjective πR ∧
      ∀ (g : Γ ℚ) (v : V), πR (ρ g v) = πR v := by
    obtain ⟨πR, hequiv, v₀, hv₀⟩ :=
      exists_equivariant_functional_residually_nonzero V hV hρ kk hsurj
        π hπsurj hπequiv
    have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (RingHom.ker_isMaximal_of_surjective _ hsurj)
    have hunit : IsUnit (πR v₀) := by
      by_contra hnu
      have hmem : πR v₀ ∈ IsLocalRing.maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
      rw [← hker, RingHom.mem_ker] at hmem
      exact hv₀ hmem
    refine ⟨πR, fun s => ?_, hequiv⟩
    obtain ⟨u, hu⟩ := hunit
    refine ⟨(s * (↑u⁻¹ : R)) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul, ← hu, mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨πR, hπRsurj, hπRequiv⟩ := hA
  -- **Step B** (linear algebra over the local ring `R`): a basis adapted to
  -- the split exact sequence `0 → ker πR → V → R → 0` — the kernel of the
  -- split surjection is finite flat over the local `R`, hence free, of
  -- rank `2 - 1 = 1`.
  have hB : ∃ b : Module.Basis (Fin 2) R V,
      LinearMap.ker πR = Submodule.span R {b 0} ∧ πR (b 1) = 1 := by
    obtain ⟨e₁, he₁⟩ := hπRsurj 1
    haveI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
    haveI : IsNoetherian R V := isNoetherian_of_isNoetherianRing_of_finite R V
    set N : Submodule R V := LinearMap.ker πR with hN
    -- the projection of `V` onto the kernel, along `e₁`
    let prV : V →ₗ[R] V :=
      LinearMap.id - (LinearMap.toSpanSingleton R V e₁).comp πR
    have hprmem : ∀ v : V, prV v ∈ N := fun v => by
      simp [prV, N, LinearMap.mem_ker, he₁]
    let pr : V →ₗ[R] N := prV.codRestrict N hprmem
    have hpr : ∀ x : N, pr x = x := fun x => Subtype.ext (by
      show prV (x : V) = (x : V)
      have hx : πR (x : V) = 0 := LinearMap.mem_ker.mp x.2
      simp [prV, hx])
    -- the kernel is a finite flat module over the local ring `R`, hence free
    haveI : Module.Flat R N :=
      Module.Flat.of_retract N.subtype pr (LinearMap.ext hpr)
    haveI : Module.Free R N := Module.free_of_flat_of_isLocalRing
    -- the rank count: `V ≃ₗ N × R` gives `finrank N = 1`
    let eVNR : V ≃ₗ[R] N × R :=
      LinearMap.equivProdOfSurjectiveOfIsCompl pr πR
        (LinearMap.range_eq_of_proj hpr) (LinearMap.range_eq_top.mpr hπRsurj)
        ((LinearMap.isCompl_of_proj hpr).symm)
    have hfinrank : Module.finrank R N = 1 := by
      have h2 : Module.finrank R V = 2 :=
        Module.finrank_eq_of_rank_eq (by rw [hV]; norm_num)
      have h3 := eVNR.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self, h2] at h3
      omega
    let bN : Module.Basis (Fin 1) R N := Module.finBasisOfFinrankEq R N hfinrank
    -- assemble the basis of `V` via `mkFinCons`
    have hli : ∀ c : R, ∀ x ∈ N, c • e₁ + x = 0 → c = 0 := by
      intro c x hx hcx
      have h0 := congrArg πR hcx
      simpa [he₁, LinearMap.mem_ker.mp hx] using h0
    have hsp : ∀ z : V, ∃ c : R, z + c • e₁ ∈ N := by
      intro z
      exact ⟨-(πR z), by simp [N, LinearMap.mem_ker, he₁]⟩
    let b' : Module.Basis (Fin 2) R V := Module.Basis.mkFinCons e₁ bN hli hsp
    have hb'0 : b' 0 = e₁ := by
      simp [b', Module.Basis.coe_mkFinCons]
    have hb'1 : b' 1 = (bN 0 : V) := by
      have h1 := congrFun (Module.Basis.coe_mkFinCons e₁ bN hli hsp) (Fin.succ 0)
      rw [Fin.cons_succ] at h1
      exact h1
    refine ⟨b'.reindex (Equiv.swap 0 1), ?_, ?_⟩
    · -- the kernel is spanned by `b 0 = ↑(bN 0)`
      rw [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left,
        hb'1]
      calc N = Submodule.map N.subtype ⊤ := (Submodule.map_subtype_top N).symm
        _ = Submodule.map N.subtype (Submodule.span R (Set.range ⇑bN)) := by
            rw [Module.Basis.span_eq]
        _ = Submodule.span R (⇑N.subtype '' Set.range ⇑bN) :=
            (Submodule.span_image _).symm
        _ = Submodule.span R {(bN 0 : V)} := by
            rw [Set.range_unique, Set.image_singleton]
            rfl
    · rw [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right,
        hb'0]
      exact he₁
  obtain ⟨b, hkerspan, hb1⟩ := hB
  -- `b 0` lies in the kernel
  have hb0 : πR (b 0) = 0 := by
    have hmem : b 0 ∈ LinearMap.ker πR := by
      rw [hkerspan]; exact Submodule.mem_span_singleton_self _
    exact LinearMap.mem_ker.mp hmem
  -- coefficients on the basis vector `b 0` are unique
  have hcoeff : ∀ r r' : R, r • b 0 = r' • b 0 → r = r' := by
    intro r r' h
    have h0 := congrArg (fun v => b.repr v 0) h
    simpa using h0
  -- the line `R • b 0 = ker πR` is Galois-stable: the eigenvalue exists
  have hstab : ∀ g : Γ ℚ, ∃ r : R, ρ g (b 0) = r • b 0 := by
    intro g
    have hmem : ρ g (b 0) ∈ LinearMap.ker πR := by
      rw [LinearMap.mem_ker, hπRequiv g (b 0), hb0]
    rw [hkerspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩
  choose χ₀ hχ₀ using hstab
  -- the off-diagonal coefficient: `ρ g (b 1) - b 1` is in the kernel
  have hccex : ∀ g : Γ ℚ, ∃ r : R, ρ g (b 1) = r • b 0 + b 1 := by
    intro g
    have hmem : ρ g (b 1) - b 1 ∈ LinearMap.ker πR := by
      rw [LinearMap.mem_ker, map_sub, hπRequiv g (b 1), sub_self]
    rw [hkerspan, Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, by rw [hr]; abel⟩
  choose cc hcc using hccex
  -- multiplicativity of the eigenvalue system
  have hmul : ∀ g h : Γ ℚ, χ₀ (g * h) = χ₀ g * χ₀ h := by
    intro g h
    apply hcoeff
    calc χ₀ (g * h) • b 0 = ρ (g * h) (b 0) := (hχ₀ (g * h)).symm
      _ = ρ g (ρ h (b 0)) := by rw [map_mul]; rfl
      _ = ρ g (χ₀ h • b 0) := by rw [hχ₀ h]
      _ = χ₀ h • ρ g (b 0) := map_smul _ _ _
      _ = χ₀ h • (χ₀ g • b 0) := by rw [hχ₀ g]
      _ = (χ₀ g * χ₀ h) • b 0 := by rw [smul_smul, mul_comm]
  have hone : χ₀ 1 = 1 := by
    apply hcoeff
    rw [← hχ₀ 1, map_one, one_smul]
    rfl
  refine ⟨b, ⟨⟨χ₀, hone⟩, hmul⟩, cc, fun g => ?_⟩
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hχ₀ g, hcc g, Module.Basis.repr_self]

/-- **Ordinarity lifting from the residual trivial quotient** (DERIVED
2026-07-18 from the global triangular form and the cyclotomic-at-Frobenius
leaf): the local Frobenius matrix is the global triangular form evaluated
at the image of the arithmetic Frobenius, and its diagonal character value
is `p` by the determinant condition (`IsHardlyRamified.det` +
`Matrix.det_fin_two` on the triangular matrix). -/
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
        !![(p : R), c; 0, 1] := by
  obtain ⟨b, χ, cc, hb⟩ :=
    exists_global_triangular_of_residual_trivial_quotient V hV hρ kk hsurj
      π hπsurj hπequiv
  -- the determinant reads off the diagonal character
  have hAll : ∀ g : Γ ℚ, ρ.det g = χ g := fun g => by
    show LinearMap.det (ρ g) = χ g
    rw [← LinearMap.det_toMatrix b, hb g]
    simp [Matrix.det_fin_two]
  have key : ∀ X : Γ ℚ, χ X = (p : R) →
      ∃ c, LinearMap.toMatrix b b (ρ X) = !![(p : R), c; 0, 1] :=
    fun X hX => ⟨cc X, by rw [hb X, hX]⟩
  simp only [GaloisRep.toLocal_apply]
  refine ⟨b, ?_⟩
  refine key _ ?_
  rw [← hAll, hρ.det]
  convert cyclotomicCharacter_adicArithFrob (R := R) p hp hp5 using 4
  -- the two spellings differ only in the (subsingleton) `Algebra ℚ _` instance
  congr 1
  congr 1
  congr 1
  exact Subsingleton.elim _ _

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
