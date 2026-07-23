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
public import Mathlib.RingTheory.DedekindDomain.Different
-- `differentIdeal` (appears in the STATEMENTS of the Minkowski and
-- ramification strata of the trivial-component leaf), and
-- `dvd_differentIdeal_iff` for the ramification stratum
import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- `NumberField.absNorm_differentIdeal`, the discriminant–different
-- bridge of the Minkowski stratum
import Mathlib.FieldTheory.Galois.Infinite
-- `InfiniteGalois.fixingSubgroup_fixedField` / `isOpen_iff_finite` /
-- `normal_iff_isGalois`: the finite-quotient stratum of the
-- Minkowski assembly
import Mathlib.FieldTheory.IsAlgClosed.Basic
-- the `IsAlgClosure.normal` instance (`Normal ℚ ℚ̄`)
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- the `AlgebraicClosure.isAlgebraic` instance
import Mathlib.FieldTheory.Separable
-- the `Algebra.IsSeparable.of_integral` instance (char-0 separability)
import Mathlib.Topology.Algebra.OpenSubgroup
-- `Subgroup.isOpen_mono`, `Subgroup.isClosed_of_isOpen`
import Mathlib.NumberTheory.RamificationInertia.Galois
-- `Ideal.card_inertia_eq_ramificationIdxIn`, the ramification stratum
import Mathlib.NumberTheory.RamificationInertia.Unramified
-- `Ideal.isUnramifiedAt_iff_map_eq` and friends, the ramification
-- stratum

/-!
# 3-adic hardly ramified representations

Three-adic input results for the analysis of hardly ramified families:
properties of `R`-linear representations on a finite `ℤ_[3]`-module which
are hardly ramified at 3.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

-- The project import closure registers `DivisionRing.toRatAlgebra` in a
-- position where it shadows the canonical `Algebra ℚ` instances on the
-- algebraic closure and on adic completions (all `Algebra ℚ` structures
-- are equal — `Subsingleton (Algebra ℚ _)` — but the instances keyed on
-- the canonical ones become unfindable). Boost the canonical instances
-- locally so the Minkowski-assembly statements elaborate consistently
-- with `GaloisRep.toLocal` and the `AlgebraicClosure` instance suite.
attribute [local instance 2000] AlgebraicClosure.instAlgebra
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

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

/-- **Ideal-filtration transport for functionals** (helper, proven): an
`R`-linear functional with all values in an ideal `I` maps `J • ⊤` into
`J * I` — by induction on the generators `j • v` of the smul submodule. -/
theorem linearMap_apply_mem_mul_of_forall_mem {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {I J : Ideal R} (h : V →ₗ[R] R) (hval : ∀ v : V, h v ∈ I)
    {x : V} (hx : x ∈ J • (⊤ : Submodule R V)) :
    h x ∈ J * I := by
  refine Submodule.smul_induction_on hx (fun r hr v _ => ?_)
    fun y z hy hz => ?_
  · rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_mul hr (hval v)
  · rw [map_add]
    exact Ideal.add_mem _ hy hz

/-- **Residual scalar transport** (helper, proven): in `kk ⊗[R] V` the
element `1 ⊗ (r • w)` is the residue of `r` acting on `1 ⊗ w`. -/
theorem one_tmul_smul {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (kk : Type*) [CommRing kk] [Algebra R kk] (r : R) (w : V) :
    (1 : kk) ⊗ₜ[R] (r • w) = algebraMap R kk r • ((1 : kk) ⊗ₜ[R] w) := by
  rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- **Residual vanishing detects the maximal-adic filtration** (helper,
proven): an element of `V` whose image `1 ⊗ u` vanishes in the residual
space `kk ⊗[R] V` lies in `𝔪V`. Coordinates along a base-changed basis:
the residual coordinates are the residues of the coordinates, and the
kernel of the (surjective) structure map `R → kk` is the maximal ideal
since `kk` is a field and `R` is local. -/
theorem mem_maximalIdeal_smul_top_of_one_tmul_eq_zero {R : Type u}
    [CommRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type*) [Field kk] [Algebra R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    {u : V} (hu : (1 : kk) ⊗ₜ[R] u = 0) :
    u ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
  classical
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  let bV := Module.Free.chooseBasis R V
  have hcoord : ∀ i, bV.repr u i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    have h1 := Module.Basis.baseChange_repr_tmul kk bV (1 : kk) u i
    rw [hu] at h1
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, Algebra.smul_def,
      mul_one] at h1
    rw [← hker, RingHom.mem_ker]
    exact h1.symm
  have hsum : u = ∑ i, bV.repr u i • bV i := (bV.sum_repr u).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem_smul (hcoord i) trivial

/-- **The residually adapted basis** (helper, proven): given the residual
trivial-quotient functional `π` and a vector `v₀` with `π (1 ⊗ v₀) ≠ 0`,
there is an `R`-basis `(w₀, v₀)` of `V` whose first vector residually
spans the line `ker π`. Content: a nonzero vector of the rank-1 kernel
of `π` lifts to `V` (the residue map `V → kk ⊗ V` is onto since `R → kk`
is); the pair is residually a basis, so it generates `V` by Nakayama,
and generators of the right cardinality of a free module over the
Noetherian local `R` form a basis by the surjective-endomorphism trick. -/
theorem exists_residual_adapted_basis {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R] [Module.Free ℤ_[3] R]
    [IsLocalRing R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2)
    (kk : Type u) [Field kk] [Algebra R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (π : (kk ⊗[R] V) →ₗ[kk] kk) (hπsurj : Function.Surjective π)
    (v₀ : V) (hv₀ : π ((1 : kk) ⊗ₜ[R] v₀) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) R V,
      π ((1 : kk) ⊗ₜ[R] b 0) = 0 ∧ (1 : kk) ⊗ₜ[R] b 0 ≠ 0 ∧ b 1 = v₀ := by
  classical
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  haveI : IsNoetherian R V := isNoetherian_of_isNoetherianRing_of_finite R V
  haveI : Module.Finite kk (kk ⊗[R] V) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R V).baseChange kk)
  -- the residual space is 2-dimensional over `kk`
  have hfr : Module.finrank kk (kk ⊗[R] V) = 2 :=
    Module.finrank_eq_of_rank_eq
      (by rw [Module.rank_baseChange, hV]; simp)
  -- rank-nullity: the kernel of `π` is a line
  have hker1 : Module.finrank kk (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπsurj, finrank_top, Module.finrank_self,
      hfr] at h
    omega
  -- a nonzero residual kernel vector
  have hne : (LinearMap.ker π : Submodule kk (kk ⊗[R] V)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker1
    exact one_ne_zero hker1.symm
  obtain ⟨z, hzmem, hzne⟩ := (Submodule.ne_bot_iff _).mp hne
  -- every residual vector is `1 ⊗ (some vector of V)`
  have hone_tmul_surj : ∀ z' : kk ⊗[R] V, ∃ w : V, (1 : kk) ⊗ₜ[R] w = z' := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
    | tmul cc v =>
      obtain ⟨r, hr⟩ := hsurj cc
      exact ⟨r • v, by
        rw [one_tmul_smul, hr, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one]⟩
    | add x y hx hy =>
      obtain ⟨wx, hwx⟩ := hx
      obtain ⟨wy, hwy⟩ := hy
      exact ⟨wx + wy, by rw [TensorProduct.tmul_add, hwx, hwy]⟩
  obtain ⟨w₀, hw₀⟩ := hone_tmul_surj z
  have hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0 := by
    rw [hw₀]
    exact LinearMap.mem_ker.mp hzmem
  have hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0 := by
    rw [hw₀]
    exact hzne
  -- the pair is residually linearly independent
  have hli : LinearIndependent kk
      ![(1 : kk) ⊗ₜ[R] w₀, (1 : kk) ⊗ₜ[R] v₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h0 := congrArg π hst
      simp only [map_add, map_smul, map_zero, hw₀π, smul_eq_mul, mul_zero,
        zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hv₀
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right hw₀ne
  -- hence residually a basis: everything is a combination of the pair
  have hcard : Fintype.card (Fin 2) = Module.finrank kk (kk ⊗[R] V) := by
    rw [hfr, Fintype.card_fin]
  have hBres : ∀ z' : kk ⊗[R] V, ∃ x y : kk,
      z' = x • ((1 : kk) ⊗ₜ[R] w₀) + y • ((1 : kk) ⊗ₜ[R] v₀) := by
    intro z'
    set Bres : Module.Basis (Fin 2) kk (kk ⊗[R] V) :=
      basisOfLinearIndependentOfCardEqFinrank hli hcard with hBresDef
    refine ⟨Bres.repr z' 0, Bres.repr z' 1, ?_⟩
    have hz := Bres.sum_repr z'
    rw [Fin.sum_univ_two] at hz
    have h0 : Bres 0 = (1 : kk) ⊗ₜ[R] w₀ := by
      rw [hBresDef, coe_basisOfLinearIndependentOfCardEqFinrank]
      simp
    have h1 : Bres 1 = (1 : kk) ⊗ₜ[R] v₀ := by
      rw [hBresDef, coe_basisOfLinearIndependentOfCardEqFinrank]
      simp
    rw [h0, h1] at hz
    exact hz.symm
  -- Nakayama: the pair generates `V`
  set N : Submodule R V := Submodule.span R {w₀, v₀} with hN
  have hsup : ∀ v : V,
      v ∈ N ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro v
    obtain ⟨x, y, hxy⟩ := hBres ((1 : kk) ⊗ₜ[R] v)
    obtain ⟨r, hr⟩ := hsurj x
    obtain ⟨r', hr'⟩ := hsurj y
    have hu : r • w₀ + r' • v₀ ∈ N :=
      Submodule.add_mem _
        (Submodule.smul_mem _ r (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ r' (Submodule.subset_span (by simp)))
    have hdiff : v - (r • w₀ + r' • v₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
      refine mem_maximalIdeal_smul_top_of_one_tmul_eq_zero kk hsurj ?_
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_add, one_tmul_smul,
        one_tmul_smul, hr, hr', ← hxy, sub_self]
    have hv : v = (r • w₀ + r' • v₀) + (v - (r • w₀ + r' • v₀)) := by abel
    rw [hv]
    exact Submodule.add_mem_sup hu hdiff
  have hNtop : N = ⊤ := by
    have hle : (⊤ : Submodule R (V ⧸ N)) ≤
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R (V ⧸ N)) := by
      intro q _
      obtain ⟨v, rfl⟩ := N.mkQ_surjective q
      obtain ⟨u, hu, m, hm, huv⟩ := Submodule.mem_sup.mp (hsup v)
      have hu0 : N.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hu
      have hqm : N.mkQ v = N.mkQ m := by
        rw [← huv, map_add, hu0, zero_add]
      rw [hqm]
      have hmap : N.mkQ m ∈ Submodule.map N.mkQ
          ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) :=
        Submodule.mem_map_of_mem hm
      rw [Submodule.map_smul''] at hmap
      exact Submodule.smul_mono le_rfl le_top hmap
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) ⊤ (Module.finite_def.mp inferInstance) hle
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    rw [eq_top_iff]
    intro v _
    have hv : N.mkQ v ∈ (⊤ : Submodule R (V ⧸ N)) := trivial
    rw [hbot, Submodule.mem_bot] at hv
    exact (Submodule.Quotient.mk_eq_zero N).mp hv
  -- the pair is a basis: image of a basis under a bijective endomorphism
  have hfinrank : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by rw [hV]; norm_num)
  set bF : Module.Basis (Fin 2) R V := Module.finBasisOfFinrankEq R V hfinrank
    with hbF
  set T : V →ₗ[R] V :=
    (LinearMap.toSpanSingleton R V w₀).comp (bF.coord 0) +
      (LinearMap.toSpanSingleton R V v₀).comp (bF.coord 1) with hT
  have hTapp : ∀ v : V, T v = bF.repr v 0 • w₀ + bF.repr v 1 • v₀ := by
    intro v
    rw [hT]
    simp [LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply]
  have hT0 : T (bF 0) = w₀ := by
    rw [hTapp, Module.Basis.repr_self]
    simp
  have hT1 : T (bF 1) = v₀ := by
    rw [hTapp, Module.Basis.repr_self]
    simp
  have hTsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hNtop, hN, Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨bF 0, hT0⟩
    · exact ⟨bF 1, hT1⟩
  have hTinj : Function.Injective T :=
    IsNoetherian.injective_of_surjective_endomorphism T hTsurj
  refine ⟨bF.map (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩), ?_, ?_, ?_⟩
  · rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hT0]
    exact hw₀π
  · rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hT0]
    exact hw₀ne
  · rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hT1]

/-- **The residual matrix entries** (helper, proven): relative to a
residually adapted pair `(w₀, v₀)` — with `w₀` residually spanning
`ker π` — the `π`-equivariance of the residual representation forces
`ρ g w₀ ≡ a g • w₀` and `ρ g v₀ ≡ v₀ + c g • w₀` modulo `𝔪V`: the
reduction of `ρ` is triangular in this pair, with a diagonal entry `a`
(residually the mod-3 cyclotomic character, by the determinant
condition — not needed at this level) and an off-diagonal entry `c`. -/
theorem exists_residual_matrix_entries {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (kk : Type u) [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (π : (kk ⊗[R] V) →ₗ[kk] kk) (hπsurj : Function.Surjective π)
    (hπequiv : ∀ g : Γ ℚ, ∀ w : kk ⊗[R] V,
      π ((ρ.baseChange kk) g w) = π w)
    (w₀ v₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0) :
    ∃ a c : Γ ℚ → R, ∀ g : Γ ℚ,
      ρ g w₀ - a g • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) ∧
      ρ g v₀ - (v₀ + c g • w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
  classical
  haveI : Module.Finite kk (kk ⊗[R] V) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R V).baseChange kk)
  have hfr : Module.finrank kk (kk ⊗[R] V) = 2 :=
    Module.finrank_eq_of_rank_eq
      (by rw [Module.rank_baseChange, hV]; simp)
  have hker1 : Module.finrank kk (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπsurj, finrank_top, Module.finrank_self,
      hfr] at h
    omega
  -- `ker π` is the residual line spanned by `1 ⊗ w₀`
  have hkerspan : (LinearMap.ker π : Submodule kk (kk ⊗[R] V)) =
      Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr hw₀π
    · rw [hker1, finrank_span_singleton hw₀ne]
  -- residual kernel vectors are congruent to multiples of `w₀` mod `𝔪V`
  have key : ∀ u : V, π ((1 : kk) ⊗ₜ[R] u) = 0 →
      ∃ r : R, u - r • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro u hu
    have humem : (1 : kk) ⊗ₜ[R] u ∈
        Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀} := by
      rw [← hkerspan]
      exact LinearMap.mem_ker.mpr hu
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp humem
    obtain ⟨r, hr⟩ := hsurj x
    refine ⟨r, mem_maximalIdeal_smul_top_of_one_tmul_eq_zero kk hsurj ?_⟩
    rw [TensorProduct.tmul_sub, one_tmul_smul, hr, hx, sub_self]
  -- residual equivariance of `π` against the integral action
  have hres : ∀ (g : Γ ℚ) (v : V),
      π ((1 : kk) ⊗ₜ[R] (ρ g v)) = π ((1 : kk) ⊗ₜ[R] v) := by
    intro g v
    rw [show (1 : kk) ⊗ₜ[R] (ρ g v) =
      (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] v) from rfl, hπequiv]
  have H : ∀ g : Γ ℚ, ∃ r r' : R,
      (ρ g w₀ - r • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) ∧
      (ρ g v₀ - (v₀ + r' • w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) := by
    intro g
    obtain ⟨r, hrmem⟩ := key (ρ g w₀) (by rw [hres g w₀]; exact hw₀π)
    have hv' : π ((1 : kk) ⊗ₜ[R] (ρ g v₀ - v₀)) = 0 := by
      rw [TensorProduct.tmul_sub, map_sub, hres g v₀, sub_self]
    obtain ⟨r', hr'mem⟩ := key (ρ g v₀ - v₀) hv'
    refine ⟨r, r', hrmem, ?_⟩
    have hre : ρ g v₀ - (v₀ + r' • w₀) = (ρ g v₀ - v₀) - r' • w₀ := by abel
    rw [hre]
    exact hr'mem
  choose a c hac using H
  exact ⟨a, c, hac⟩

/-- **Linear endomorphisms preserve the maximal-adic filtration** (helper,
proven): a linear endomorphism maps `J • ⊤` into `J • ⊤`. -/
theorem apply_mem_smul_top {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (T : V →ₗ[R] V) {J : Ideal R} {x : V}
    (hx : x ∈ J • (⊤ : Submodule R V)) :
    T x ∈ J • (⊤ : Submodule R V) := by
  refine Submodule.smul_induction_on hx (fun r hr v _ => ?_)
    fun y z hy hz => ?_
  · rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- **The maximal-adic filtration vanishes residually** (helper, proven):
the converse of `mem_maximalIdeal_smul_top_of_one_tmul_eq_zero` — an
element of `𝔪V` has vanishing image `1 ⊗ u` in `kk ⊗[R] V`. -/
theorem one_tmul_eq_zero_of_mem_maximalIdeal_smul_top {R : Type u}
    [CommRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (kk : Type*) [Field kk] [Algebra R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    {u : V} (hu : u ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) :
    (1 : kk) ⊗ₜ[R] u = 0 := by
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  refine Submodule.smul_induction_on hu (fun r hr v _ => ?_)
    fun y z hy hz => ?_
  · have hr0 : algebraMap R kk r = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hr
    rw [one_tmul_smul, hr0, zero_smul]
  · rw [TensorProduct.tmul_add, hy, hz, add_zero]

/-- **Scalar extraction along a residually nonzero vector** (helper,
proven): if `r • w₀ ∈ 𝔪V` and `w₀` is residually nonzero then
`r ∈ 𝔪` — residually `r̄ • w̄₀ = 0` with `w̄₀ ≠ 0` over the field `kk`. -/
theorem mem_maximalIdeal_of_smul_mem_smul_top {R : Type u}
    [CommRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (kk : Type*) [Field kk] [Algebra R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    {w₀ : V} (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0) {r : R}
    (hr : r • w₀ ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) :
    r ∈ IsLocalRing.maximalIdeal R := by
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  have h0 := one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj hr
  rw [one_tmul_smul] at h0
  rcases smul_eq_zero.mp h0 with h | h
  · rw [← hker, RingHom.mem_ker]
    exact h
  · exact absurd h hw₀ne

/-- **`3` lies in the maximal ideal** (helper, proven): in a (nonzero)
local module-finite `ℤ₃`-algebra, `3` is a non-unit — otherwise
`R = 3R` and Nakayama over `ℤ₃` forces `R = 0`. (Extracted from the
proof of `exists_residue_package`.) -/
theorem three_mem_maximalIdeal {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R] [IsLocalRing R] :
    (3 : R) ∈ IsLocalRing.maximalIdeal R := by
  have h3Z : (3 : ℤ_[3]) ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PadicInt.not_isUnit_iff]
    have h : ‖((3 : ℕ) : ℤ_[3])‖ = ((3 : ℕ) : ℝ)⁻¹ := PadicInt.norm_p
    have h2 : ((3 : ℕ) : ℤ_[3]) = (3 : ℤ_[3]) := by norm_cast
    rw [h2] at h
    rw [h]
    norm_num
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

/-- **Nontriviality of the mod-3 cyclotomic character** (proven): some
element of `Γ ℚ` moves the cube roots of unity — `ζ₃ ∉ ℚ`, since a
rational `q` with `q³ = 1` has `q = 1` (`q² + q + 1 > 0`), while `ℚ̄`
has a primitive cube root of unity fixed by nobody's leave. Any such
element is a "residual complex conjugation" for the ω-analysis: the
mod-3 cyclotomic character takes its only other value `-1` there. -/
theorem exists_cyclotomicCharacterModL_three_ne_one :
    ∃ σ : Γ ℚ, cyclotomicCharacterModL 3 σ ≠ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3
  -- if the character were trivial, every automorphism would fix `ζ`
  have hfix : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      σ ζ = ζ := by
    intro σ
    have h1 : cyclotomicCharacterModL 3 σ = 1 := hall σ
    have h2 := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) σ) hζ.toRootsOfUnity.2
    rw [show modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
        (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
          (AlgebraicClosure ℚ) σ) = cyclotomicCharacterModL 3 σ from rfl,
      h1] at h2
    have hcoe : ((hζ.toRootsOfUnity : (AlgebraicClosure ℚ)ˣ) :
        AlgebraicClosure ℚ) = ζ := by
      simp [IsPrimitiveRoot.toRootsOfUnity]
    have hval : (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 := rfl
    rw [hval, pow_one, hcoe] at h2
    exact h2
  -- so `ζ` would be rational
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  obtain ⟨q, hq⟩ := Set.mem_range.mp <| IntermediateField.mem_bot.mp <|
    (InfiniteGalois.mem_bot_iff_fixed ζ).mpr hfix
  have hq3 : q ^ 3 = 1 := by
    have h3 : algebraMap ℚ (AlgebraicClosure ℚ) (q ^ 3) = 1 := by
      rw [map_pow, hq]
      exact hζ.pow_eq_one
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by rw [h3, map_one])
  have hqne : q ≠ 1 := by
    intro h1
    apply hζ.ne_one (by norm_num)
    rw [← hq, h1, map_one]
  -- but a rational cube root of unity is `1`
  have hfactor : (q - 1) * (q ^ 2 + q + 1) = 0 := by linear_combination hq3
  rcases mul_eq_zero.mp hfactor with h | h
  · exact hqne (by linarith [sub_eq_zero.mp h])
  · nlinarith [sq_nonneg (2 * q + 1)]

/-- **The residual twist is the mod-3 cyclotomic character** (sorry node
— the determinant identification; Serre, Duke 1987, §5.4): along the
residually adapted pair `(w₀, v₀)`, the reduction of `ρ` is triangular
with trivial quotient character (`hπequiv`), so its determinant is
residually the diagonal entry `a`; but the determinant is the 3-adic
cyclotomic character (`hρ.det`), whose reduction is the mod-3 cyclotomic
character ω. Hence `a ≡ ω mod 𝔪`, stated here value-by-value against
the two elements of `(ZMod 3)ˣ`: `a g ≡ 1` on the kernel of ω and
`a g ≡ -1` off it. Route for the proof: compute `det (ρ̄ g)` on the
residual basis `(1 ⊗ w₀, 1 ⊗ v₀)` (triangular, diagonal `(ā g, 1)`),
transfer the determinant along base change
(`LinearMap.det_baseChange`), and reduce `hρ.det` through
`algebraMap R kk` using the compatibility of the 3-adic and mod-3
cyclotomic characters (`PadicInt.toZModPow`-reduction of
`cyclotomicCharacter`, cf. `cyclotomicCharacter.toZModPow_toFun`). -/
theorem residual_twist_eq_cyclotomicCharacterModL
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (g : Γ ℚ) :
    (cyclotomicCharacterModL 3 g = 1 →
      a g - 1 ∈ IsLocalRing.maximalIdeal R) ∧
    (cyclotomicCharacterModL 3 g ≠ 1 →
      a g + 1 ∈ IsLocalRing.maximalIdeal R) := by
  sorry

/-- **The ω-defect dies on the cyclotomic kernel** (sorry node — the
arithmetic core of the ω-component; Serre, Duke 1987, §5.4,
`sources/serre1987duke-ocr.txt`): the restriction of the defect
`d : g ↦ f (ρ g w₀) - f w₀` to the kernel of the mod-3 cyclotomic
character — the fixing subgroup of `ℚ(ζ₃)` — lands in `𝔪ⁿ⁺²`. On that
kernel the twist `a` is residually trivial, so `d` is modulo `𝔪ⁿ⁺²` an
honest homomorphism `Γ_{ℚ(ζ₃)} → 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` (untwisted: the ω-twist
trivializes over `ℚ(ζ₃)`), and its vanishing is exactly the vanishing
of the restricted cohomology class. Route (Serre's unit computation for
`p = 3`): the homomorphism cuts out an abelian `3`-elementary extension
of `ℚ(ζ₃)`; the hardly ramified conditions of `hρ` make it unramified
outside `3` (unramified places and the tame-at-2 argument as in the
trivial component) and place the Kummer radical at `3` inside the units
of `ℤ[ζ₃]` modulo cubes subject to Fontaine's flatness bound
(`hρ.isFlat`); `ℚ(ζ₃)` has class number `1` and its units `±1, ±ζ₃,
±ζ₃²` are excluded by the flat local condition at `3`, so the extension
is trivial and the homomorphism vanishes. -/
theorem omega_defect_vanishes_on_cyclotomicKernel
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (hamul : ∀ g h : Γ ℚ,
      a (g * h) - a g * a h ∈ IsLocalRing.maximalIdeal R)
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (hcoc : ∀ g h : Γ ℚ,
      (f (ρ (g * h) w₀) - f w₀)
        - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (g : Γ ℚ) (hg : cyclotomicCharacterModL 3 g = 1) :
    f (ρ g w₀) - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  sorry

/-- **The ω-twisted cocycle vanishing** (sorry node — the arithmetic core
of the ω-component; Serre, Duke 1987, §5.4,
`sources/serre1987duke-ocr.txt`; Neukirch for the class-field inputs):
the function `d : g ↦ f (ρ g w₀) - f w₀` has values in `𝔪ⁿ⁺¹` and is,
modulo `𝔪ⁿ⁺²`, an `a`-twisted `1`-cocycle (hypothesis `hcoc`, PROVEN by
the consumer from the residual triangular shape) for the residually
multiplicative twist `a` (hypothesis `hamul`) — residually the mod-3
cyclotomic character `ω`, by the determinant condition of `hρ`. The
claim is that `d` is a twisted coboundary one level deeper: some
`s ∈ 𝔪ⁿ⁺¹` has `d g + (a g - 1) s ∈ 𝔪ⁿ⁺²` for all `g`. Route: modulo
`𝔪ⁿ⁺²` this is a class in `H¹(Γ ℚ, ω ⊗ M)` for the finite module
`M = 𝔪ⁿ⁺¹/𝔪ⁿ⁺²`; the local restrictions of `d` — computed from its
defect origin and the hardly ramified conditions of `hρ` (flat at `3`,
tame quadratic at `2`, unramified elsewhere) — place the class in
Serre's Selmer group, which vanishes: `ℚ(ζ₃)` has class number `1`, and
its units `±1, ±ζ₃, ±ζ₃²` are excluded by the local condition at `3`
(Serre's unit computation for `p = 3`, inflation-restriction to
`Gal(ℚ(ζ₃))` and Kummer theory over `ℚ(ζ₃)`). -/
theorem exists_omega_cocycle_coboundary
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (hamul : ∀ g h : Γ ℚ,
      a (g * h) - a g * a h ∈ IsLocalRing.maximalIdeal R)
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (hcoc : ∀ g h : Γ ℚ,
      (f (ρ (g * h) w₀) - f w₀)
        - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2)) :
    ∃ s ∈ IsLocalRing.maximalIdeal R ^ (n + 1),
      ∀ g : Γ ℚ,
        (f (ρ g w₀) - f w₀) + (a g - 1) * s ∈
          IsLocalRing.maximalIdeal R ^ (n + 2) := by
  -- the two arithmetic inputs: the ω-identification of the twist and the
  -- vanishing of the defect on the cyclotomic kernel
  have hid := fun g => residual_twist_eq_cyclotomicCharacterModL V hV hρ kk
    hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha g
  have hres := fun g hg => omega_defect_vanishes_on_cyclotomicKernel V hV hρ
    kk hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha hamul n f hf hfv₀
    hcoc g hg
  -- a residual complex conjugation
  obtain ⟨σ, hσ⟩ := exists_cyclotomicCharacterModL_three_ne_one
  have hσm : a σ + 1 ∈ IsLocalRing.maximalIdeal R := (hid σ).2 hσ
  -- `a σ - 1 ≡ -2` is a unit (`2` is invertible 3-adically)
  have hone : (1 : R) ∉ IsLocalRing.maximalIdeal R := fun h1 =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  have hu : IsUnit (a σ - 1) := by
    by_contra hnu
    have hm : a σ - 1 ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    refine hone ?_
    have hsum := Submodule.sub_mem _ (three_mem_maximalIdeal (R := R))
      (Submodule.sub_mem _ hσm hm)
    have h31 : (3 : R) - ((a σ + 1) - (a σ - 1)) = 1 := by ring
    rwa [h31] at hsum
  have huu : (↑hu.unit⁻¹ : R) * (a σ - 1) = 1 := by
    have h := hu.unit.inv_mul
    rwa [hu.unit_spec] at h
  -- the correction scalar
  have hdσm : f (ρ σ w₀) - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 1) :=
    hf σ w₀
  refine ⟨-(↑hu.unit⁻¹ * (f (ρ σ w₀) - f w₀)),
    Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hdσm), fun g => ?_⟩
  by_cases hg : cyclotomicCharacterModL 3 g = 1
  · -- on the cyclotomic kernel both summands lie in `𝔪ⁿ⁺²`
    refine Submodule.add_mem _ (hres g hg) ?_
    have h1 := Ideal.mul_mem_mul ((hid g).1 hg)
      (Submodule.neg_mem _ (Ideal.mul_mem_left _ (↑hu.unit⁻¹ : R) hdσm))
    rwa [← pow_succ'] at h1
  · -- off the kernel: reduce to `σ` through the kernel element `g σ⁻¹`
    have hgσ : cyclotomicCharacterModL 3 (g * σ⁻¹) = 1 := by
      have htwo : ∀ x y : (ZMod 3)ˣ, x ≠ 1 → y ≠ 1 → x * y⁻¹ = 1 := by
        decide
      rw [map_mul, map_inv]
      exact htwo _ _ hg hσ
    have hd' : f (ρ (g * σ⁻¹) w₀) - f w₀ ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := hres _ hgσ
    have hcoc' := hcoc (g * σ⁻¹) σ
    rw [inv_mul_cancel_right] at hcoc'
    have hgm : a g + 1 ∈ IsLocalRing.maximalIdeal R := (hid g).2 hg
    have hsplit : (f (ρ g w₀) - f w₀)
          + (a g - 1) * -(↑hu.unit⁻¹ * (f (ρ σ w₀) - f w₀))
        = ((f (ρ g w₀) - f w₀)
            - (a σ * (f (ρ (g * σ⁻¹) w₀) - f w₀)
              + (f (ρ σ w₀) - f w₀)))
          + a σ * (f (ρ (g * σ⁻¹) w₀) - f w₀)
          + ↑hu.unit⁻¹ * (((a σ + 1) - (a g + 1)) * (f (ρ σ w₀) - f w₀))
        := by linear_combination (-(f (ρ σ w₀) - f w₀)) * huu
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.add_mem _ hcoc'
      (Ideal.mul_mem_left _ _ hd')) (Ideal.mul_mem_left _ _ ?_)
    have h2 := Ideal.mul_mem_mul (Submodule.sub_mem _ hσm hgm) hdσm
    rwa [← pow_succ'] at h2

/-- **The ω-component Selmer vanishing** (DERIVED 2026-07-22 from the
twisted-cocycle leaf `exists_omega_cocycle_coboundary`; the twisted
cocycle identity and the residual multiplicativity of the twist `a` are
PROVEN here from the residual triangular shape — Serre, Duke 1987,
§5.4, `sources/serre1987duke-ocr.txt`; Neukirch for the class-field
inputs): along a residually adapted vector `w₀` spanning the ω-line
`ker π̄` of the residual representation, the defect
`g ↦ f (ρ g w₀) - f w₀` of the approximately equivariant functional `f`
is, modulo `𝔪ⁿ⁺²`, a `1`-cocycle of `Γ ℚ` valued in the ω-isotypic
component of `Hom(V̄, 𝔪ⁿ⁺¹/𝔪ⁿ⁺²)` — the twist is the diagonal entry `a`,
residually the mod-3 cyclotomic character `ω` by the determinant
condition of `hρ`. The hardly ramified local conditions (flat at `3`,
tame quadratic at `2`, unramified elsewhere) place its class in the
Selmer group `H¹_{Serre}(ℚ, ω ⊗ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²)`, which vanishes because
`ℚ(ζ₃)` has class number `1` and its units `±1, ±ζ₃` are excluded by
the local conditions at `3` (Serre's unit computation for `p = 3`). The
witness of the vanishing class is a correction scalar `s ∈ 𝔪ⁿ⁺¹` — the
value `h w₀` of the sought coboundary — with
`(f (ρ g w₀) - f w₀) + (a g - 1) s ∈ 𝔪ⁿ⁺²` for every `g`. -/
theorem exists_omega_component_coboundary
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R) :
    ∃ s ∈ IsLocalRing.maximalIdeal R ^ (n + 1),
      ∀ g : Γ ℚ,
        (f (ρ g w₀) - f w₀) + (a g - 1) * s ∈
          IsLocalRing.maximalIdeal R ^ (n + 2) := by
  -- the twist is residually multiplicative
  have hamul : ∀ g h : Γ ℚ,
      a (g * h) - a g * a h ∈ IsLocalRing.maximalIdeal R := by
    intro g h
    refine mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne ?_
    have hexp : (a (g * h) - a g * a h) • w₀
        = -(ρ (g * h) w₀ - a (g * h) • w₀)
          + (a h • (ρ g w₀ - a g • w₀) + ρ g (ρ h w₀ - a h • w₀)) := by
      rw [show ρ (g * h) w₀ = ρ g (ρ h w₀) from by rw [map_mul]; rfl,
        map_sub, map_smul]
      module
    rw [hexp]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (ha (g * h)))
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (ha g))
        (apply_mem_smul_top (ρ g : V →ₗ[R] V) (ha h)))
  -- the defect along `w₀` is an `a`-twisted cocycle modulo `𝔪ⁿ⁺²`
  have hcoc : ∀ g h : Γ ℚ,
      (f (ρ (g * h) w₀) - f w₀)
        - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g h
    have hsplit : (f (ρ (g * h) w₀) - f w₀)
          - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
        = ((f.comp (ρ g : V →ₗ[R] V)) - f) (ρ h w₀ - a h • w₀) := by
      rw [show ρ (g * h) w₀ = ρ g (ρ h w₀) from by rw [map_mul]; rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
        map_smul, smul_eq_mul]
      ring
    rw [hsplit]
    have hDv : ∀ v : V,
        ((f.comp (ρ g : V →ₗ[R] V)) - f) v
          ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
      intro v
      simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using hf g v
    have h2 := linearMap_apply_mem_mul_of_forall_mem _ hDv (ha h)
    rwa [← pow_succ'] at h2
  exact exists_omega_cocycle_coboundary V hV hρ kk hsurj π hπsurj hπequiv
    v₀ hv₀ w₀ hw₀π hw₀ne a ha hamul n f hf hfv₀ hcoc

/-- **Linear functionals preserve ideal filtrations** (helper, proven):
an `R`-linear functional maps `J • ⊤` into `J`. -/
theorem linearMap_apply_mem_of_mem_smul_top {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] R) {J : Ideal R} {x : V}
    (hx : x ∈ J • (⊤ : Submodule R V)) : f x ∈ J := by
  refine Submodule.smul_induction_on hx (fun r hr v _ => ?_)
    fun y z hy hz => ?_
  · rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  · rw [map_add]
    exact Ideal.add_mem _ hy hz

open NumberField in
/-- **Classification of the finite places of `ℚ`** (helper, proven):
every height-one prime of `𝓞 ℚ` is the place attached to a rational
prime number — transport along `Rat.ringOfIntegersEquiv` and take the
positive generator of the corresponding prime of `ℤ`. -/
theorem exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (p : ℕ) (hp : p.Prime),
      v = hp.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  set w : IsDedekindDomain.HeightOneSpectrum ℤ :=
    (Rat.ringOfIntegersEquiv.symm.heightOneSpectrum).symm v with hwdef
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal w.asIdeal).principal
  have hqne : q ≠ 0 := by
    intro h0
    refine w.ne_bot ?_
    rw [hq, h0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hqprime : Prime q := by
    have hp := w.isPrime
    rw [hq] at hp
    exact (Ideal.span_singleton_prime hqne).mp hp
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hqprime, ?_⟩
  have hw : w = (Int.prime_iff_natAbs_prime.mp hqprime).toHeightOneSpectrumInt := by
    ext1
    rw [hq]
    show Ideal.span {q} = Ideal.span {(q.natAbs : ℤ)}
    rw [Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs q
  calc v = (Rat.ringOfIntegersEquiv.symm.heightOneSpectrum) w :=
      (Equiv.apply_symm_apply _ v).symm
    _ = _ := by rw [hw]; rfl

open NumberField in
/-- **Minkowski's theorem, different-ideal form** (proven): a number
field whose different ideal over `ℤ` is the unit ideal has absolute
discriminant `1` (`NumberField.absNorm_differentIdeal`), hence — by the
Hermite–Minkowski bound `NumberField.abs_discr_gt_two` — is `ℚ`
itself. -/
theorem finrank_eq_one_of_differentIdeal_eq_top
    (K : Type*) [Field K] [NumberField K]
    (h : differentIdeal ℤ (𝓞 K) = ⊤) :
    Module.finrank ℚ K = 1 := by
  by_contra hne
  have h1 : 1 < Module.finrank ℚ K := by
    have h0 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have h2 := NumberField.abs_discr_gt_two (K := K) h1
  have h3 : (differentIdeal ℤ (𝓞 K)).absNorm = 1 := by
    rw [h, Ideal.absNorm_top]
  have h4 : (NumberField.discr K).natAbs = 1 :=
    (NumberField.absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)).symm.trans h3
  rw [Int.abs_eq_natAbs, h4] at h2
  norm_num at h2

open NumberField in
/-- **Everywhere-trivial inertia gives trivial different ideal** (PROVEN
2026-07-23 — the ramification stratum): for a finite Galois subextension
`L/ℚ` of `ℚ̄`, if every nonzero prime of `𝓞 L` has trivial inertia in
`Gal(L/ℚ)`, then the different ideal of `𝓞 L` over `ℤ` is the unit
ideal. A prime `Q` dividing the different would be ramified
(`dvd_differentIdeal_iff`, over the separable fraction-field extension
in characteristic zero); but its ramification index is the order of
its inertia group (`Ideal.card_inertia_eq_ramificationIdxIn` together
with `Ideal.ramificationIdxIn_eq_ramificationIdx` and
`Ideal.ramificationIdx_eq_one_iff`, applied to the `Gal(L/ℚ)`-action
on `𝓞 L` over `ℤ` — the `IsGaloisGroup` instance is assembled here,
with invariants computed through `IsGalois.mem_bot_iff_fixed` and
`IsIntegrallyClosed.isIntegral_iff`), which is `1` by hypothesis. The
different ideal is nonzero (`differentIdeal_ne_bot`), so having no
prime divisor it is the unit ideal. -/
theorem differentIdeal_eq_top_of_forall_inertia_eq_bot
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [Normal ℚ L]
    (h : ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q ≠ ⊥ →
      Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    differentIdeal ℤ (𝓞 L) = ⊤ := by
  classical
  by_contra hne
  -- a maximal (hence prime, nonzero) divisor of the different ideal
  obtain ⟨Q, hQmax, hQle⟩ := Ideal.exists_le_maximal _ hne
  haveI hQprime : Q.IsPrime := hQmax.isPrime
  have hQne : Q ≠ ⊥ := by
    intro h0
    rw [h0, le_bot_iff] at hQle
    exact differentIdeal_ne_bot hQle
  -- the fraction-field extension is separable (characteristic zero)
  letI : Algebra (FractionRing ℤ) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra _ _
  haveI hsep : Algebra.IsSeparable (FractionRing ℤ) (FractionRing (𝓞 L)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv ℤ ℚ).symm.toRingEquiv
      (FractionRing.algEquiv (𝓞 L) L).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv ℤ ℚ).symm
      (FractionRing.algEquiv (𝓞 L) L).symm x
  -- `Q` divides the different ideal, so it must be ramified …
  have hdvd : Q ∣ differentIdeal ℤ (𝓞 L) := Ideal.dvd_iff_le.mpr hQle
  rw [dvd_differentIdeal_iff] at hdvd
  refine hdvd ?_
  -- … but its ramification index is the order of its trivial inertia group
  have hp0 : Q.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQne
  haveI : (Q.under ℤ).IsPrime := Ideal.IsPrime.under ℤ Q
  -- the residue field of `ℤ` under `Q` is finite, hence perfect
  obtain ⟨z, hz⟩ := (IsPrincipalIdealRing.principal (Q.under ℤ)).principal
  have hzne : z ≠ 0 := by
    rintro rfl
    apply hp0
    rw [hz]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  haveI : NeZero z.natAbs := ⟨Int.natAbs_ne_zero.mpr hzne⟩
  haveI : Finite (ℤ ⧸ Q.under ℤ) := by
    rw [hz]
    exact Finite.of_equiv _ (Int.quotientSpanEquivZMod z).symm.toEquiv
  -- `Gal(L/ℚ)` is a Galois group of `𝓞 L` over `ℤ` (invariants transfer
  -- from `𝓞 ℚ` along `Rat.ringOfIntegersEquiv`)
  haveI : IsGaloisGroup (L ≃ₐ[ℚ] L) ℤ (𝓞 L) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    constructor
    intro x hx
    -- the underlying field element is Galois-fixed, hence rational
    have hfixL : ∀ e : L ≃ₐ[ℚ] L, e (x : L) = (x : L) := fun e =>
      congrArg (algebraMap (𝓞 L) L) (hx e)
    haveI : IsGalois ℚ L := ⟨⟩
    have hbot : (x : L) ∈ (⊥ : IntermediateField ℚ L) :=
      (IsGalois.mem_bot_iff_fixed _).mpr hfixL
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
    -- the rational number is integral over `ℤ`, hence an integer
    have hqint : IsIntegral ℤ q := by
      rw [← isIntegral_algebraMap_iff (B := L)
        (algebraMap ℚ L).injective, hq]
      exact x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
    refine ⟨m, NumberField.RingOfIntegers.ext ?_⟩
    show algebraMap (𝓞 L) L (algebraMap ℤ (𝓞 L) m) = (x : L)
    rw [← hq, ← hm, ← IsScalarTower.algebraMap_apply ℤ (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply ℤ ℚ L]
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := L ≃ₐ[ℚ] L) (Q.under ℤ) Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under ℤ) Q (L ≃ₐ[ℚ] L)]
    at hcard
  rw [← Ideal.ramificationIdx_eq_one_iff, ← hcard, h Q hQprime hQne,
    Subgroup.card_bot]

open NumberField in
/-- **Local inertia covers finite-level inertia** (sorry node — the
decomposition stratum): for a finite Galois subextension `L/ℚ` of `ℚ̄`
and a nonzero prime `Q` of `𝓞 L`, if the conjugates of the images in
`Γ ℚ` of all the local inertia subgroups restrict trivially to `L`,
then the inertia group of `Q` in `Gal(L/ℚ)` is trivial. Content: the
restriction `Γ ℚᵥ → Gal(L/ℚ)` at the place `v` of `ℚ` under `Q` maps
`localInertiaGroup v` ONTO the inertia group of the embedded prime
(the surjectivity direction of the local–global inertia comparison; the
containment direction is `map_mem_inertiaSubgroup_of_mem_localInertiaGroup`
of `LocalInertiaFixedField`, and the finite-level cardinality identity
`|I| = e` is `card_inertia_finite_level` there), and the primes of
`𝓞 L` over `v` are a single `Gal(L/ℚ)`-orbit, so a general `Q` is
handled by the conjugation in `hloc`. -/
theorem inertia_eq_bot_of_forall_localInertia_restrictNormalHom
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [Normal ℚ L]
    (hloc : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
      (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
      (τ : Γ ℚ), σ ∈ localInertiaGroup v →
      AlgEquiv.restrictNormalHom L
        (τ * Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
          σ * τ⁻¹) = 1)
    (Q : Ideal (𝓞 L)) (hQp : Q.IsPrime) (hQ : Q ≠ ⊥) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  sorry

open NumberField in
/-- **Homomorphisms of `Γ ℚ` trivial on all local inertia are trivial**
(DERIVED — the Minkowski assembly, 2026-07-23): a homomorphism `φ` of
`Γ ℚ` with open kernel killing the image of every local inertia
subgroup is trivial. The open normal kernel cuts out a finite Galois
subextension `L/ℚ` (`InfiniteGalois.fixingSubgroup_fixedField`,
`isOpen_iff_finite`, `normal_iff_isGalois`); triviality on the
conjugated local inertia images makes every inertia group of
`Gal(L/ℚ)` trivial (decomposition stratum), hence the different ideal
of `𝓞 L` is the unit ideal (ramification stratum), hence `L = ℚ` by
Minkowski (`finrank_eq_one_of_differentIdeal_eq_top`), i.e. the kernel
is everything. -/
theorem monoidHom_eq_one_of_forall_localInertia
    {A : Type*} [Group A] (φ : (Γ ℚ) →* A)
    (hopen : IsOpen (φ.ker : Set (Γ ℚ)))
    (hin : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
      (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      σ ∈ localInertiaGroup v →
      φ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
        σ) = 1)
    (g : Γ ℚ) : φ g = 1 := by
  classical
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  have hnormal : (φ.ker).Normal := φ.normal_ker
  have hclosed : IsClosed (φ.ker : Set (Γ ℚ)) :=
    Subgroup.isClosed_of_isOpen _ hopen
  -- the finite Galois subextension cut out by the kernel
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField
      (φ.ker : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
    with hLdef
  have hfix : L.fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨φ.ker, hclosed⟩
  haveI hfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hopen)
  haveI hgal : IsGalois ℚ L :=
    (InfiniteGalois.normal_iff_isGalois L).mp (by rw [hfix]; exact hnormal)
  haveI : Normal ℚ L := hgal.to_normal
  -- every inertia group of `Gal(L/ℚ)` is trivial
  have hinertia : ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q ≠ ⊥ →
      Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    intro Q hQp hQ
    refine inertia_eq_bot_of_forall_localInertia_restrictNormalHom L
      ?_ Q hQp hQ
    intro v σ τ hσ
    have h1 : Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
        σ ∈ φ.ker := φ.mem_ker.mpr (hin v σ hσ)
    have h2 : τ * Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
        σ * τ⁻¹ ∈ L.fixingSubgroup := by
      rw [hfix]
      exact hnormal.conj_mem _ h1 τ
    rw [← IntermediateField.restrictNormalHom_ker L] at h2
    exact h2
  -- Minkowski forces the extension to be trivial
  have hdiff := differentIdeal_eq_top_of_forall_inertia_eq_bot L hinertia
  have hrank := finrank_eq_one_of_differentIdeal_eq_top L hdiff
  have hbot : L = ⊥ := IntermediateField.finrank_eq_one_iff.mp hrank
  have hker : g ∈ φ.ker := by
    rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top g
  exact φ.mem_ker.mp hker

/-- **Openness of the congruence subgroup** (sorry node — the continuity
stratum): the set of `g ∈ Γ ℚ` acting trivially modulo `𝔪ᵏ` is open.
Route: `ρ` is continuous into `End V` with the `R`-module topology; the
congruence condition is a union of translates of the subgroup
`𝔪ᵏ • ⊤ ⊆ End V`, which is open because it contains `3ᵏ • ⊤` and
`End V` is topologically a finite free `ℤ₃`-module (transitivity of the
module topology along `ℤ₃ → R → End V`, then coordinates: `3ᵏℤ₃` is
open in `ℤ₃`, e.g. by `PadicInt.norm_le_pow_iff_mem_span_pow`). -/
theorem isOpen_setOf_forall_sub_mem_pow_smul
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (k : ℕ) :
    IsOpen {g : Γ ℚ | ∀ x : V, ρ g x - x ∈
      (IsLocalRing.maximalIdeal R ^ k) • (⊤ : Submodule R V)} := by
  sorry

/-- **Approximate homomorphisms die on inertia at `2`** (sorry node —
the tame stratum): a function `T` on `Γ ℚ` with values in `𝔪ⁿ⁺¹` which
is a homomorphism modulo `𝔪ⁿ⁺²` and has open congruence kernel kills
the local inertia at `2`. Content (local Kronecker–Weber / tame
conjugation): modulo `𝔪ⁿ⁺²` the target is a `3`-torsion group
(`3 ∈ 𝔪`, `three_mem_maximalIdeal`), and the abelianized inertia of
`ℚ₂` is `ℤ₂ˣ`, a pro-`2` group: the wild part is pro-`2` and dies by
continuity; a tame generator `t` satisfies `F t F⁻¹ = t²·(wild)` for an
arithmetic Frobenius `F` (`Field.AbsoluteGaloisGroup.adicArithFrob`),
so its image `x` in the abelian `3`-torsion quotient satisfies
`x = 2x`, i.e. `x = 0` (`2 ≡ -1 mod 3` is invertible). No hypothesis on
`ρ` is needed — this is a fact about `Γ ℚ₂` and `3`-torsion targets. -/
theorem hom_vanishes_on_localInertia_at_two
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (n : ℕ) (T : Γ ℚ → R)
    (hT : ∀ g : Γ ℚ, T g ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hThom : ∀ g h : Γ ℚ,
      T (g * h) - (T g + T h) ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (hTopen : IsOpen {g : Γ ℚ |
      T g ∈ IsLocalRing.maximalIdeal R ^ (n + 2)})
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :
    T (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
      IsLocalRing.maximalIdeal R ^ (n + 2) := by
  sorry

/-- **The corrected trivial component dies on inertia at `3`** (sorry
node — the flat stratum; Fontaine): for `σ` in the local inertia at
`3`, the corrected trivial component
`T : g ↦ (f (ρ g v₀) - f v₀) + c g * s` lands in `𝔪ⁿ⁺²`. This is the
peu-ramifié input: modulo `𝔪ⁿ⁺²` the corrected defect along the
trivial-quotient direction is a homomorphism cutting out a
`3`-elementary abelian extension, and the flatness of `ρ` at `3`
(`hρ.isFlat`, through the congruence filtration of the flat
prolongation) forces the extension of the trivial character by itself
inside the corresponding graded piece to be finite flat over `ℤ₃`,
hence unramified (Fontaine's bound: a finite flat elementary
`3`-group scheme extension of `μ`-type by étale-type over `ℤ₃` has
étale trivial-by-trivial graded piece). -/
theorem trivial_component_vanishes_on_localInertia_at_three
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (c : Γ ℚ → R)
    (hc : ∀ g : Γ ℚ, ρ g v₀ - (v₀ + c g • w₀) ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (hcmul : ∀ g h : Γ ℚ,
      c (g * h) - (c g + a g * c h) ∈ IsLocalRing.maximalIdeal R)
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (s : R) (hs : s ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hsA : ∀ g : Γ ℚ,
      (f (ρ g w₀) - f w₀) + (a g - 1) * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2))
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :
    (f (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) v₀)
      - f v₀)
      + c (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 2) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The approximate-homomorphism vanishing** (DERIVED 2026-07-23 —
assembled from the Minkowski machine; Serre, Duke 1987, §5.4,
`sources/serre1987duke-ocr.txt`): the corrected trivial component
`T : g ↦ (f (ρ g v₀) - f v₀) + c g * s` has values in `𝔪ⁿ⁺¹` and is,
modulo `𝔪ⁿ⁺²`, a homomorphism `Γ ℚ → 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` (hypothesis `hhom`,
PROVEN by the consumer: the twist term of the cocycle identity on this
graded piece is cancelled by the ω-correction `hsA`, using the
residual multiplicativity `hcmul` of the off-diagonal entry). The
claim is that `T` lands in `𝔪ⁿ⁺²` outright. PROOF (this node): `T`
descends to a homomorphism `φ : Γ ℚ →* R/𝔪ⁿ⁺²` whose kernel contains
the open congruence subgroup of `ρ` at level `n + 2`
(`isOpen_setOf_forall_sub_mem_pow_smul`, the continuity leaf), and
which kills every local inertia subgroup — at `p ∉ {2, 3}` outright
from `hρ.isUnramified` (PROVEN here: `ρ` is trivial on inertia, so the
defect is `0` and the off-diagonal entry is residually `0`), at `2` by
the tame leaf `hom_vanishes_on_localInertia_at_two`, at `3` by the
flat leaf `trivial_component_vanishes_on_localInertia_at_three`. The
Minkowski assembly `monoidHom_eq_one_of_forall_localInertia` then
forces `φ = 1`, i.e. `T ≡ 0 mod 𝔪ⁿ⁺²`. -/
theorem trivial_component_hom_vanishes
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (c : Γ ℚ → R)
    (hc : ∀ g : Γ ℚ, ρ g v₀ - (v₀ + c g • w₀) ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (hcmul : ∀ g h : Γ ℚ,
      c (g * h) - (c g + a g * c h) ∈ IsLocalRing.maximalIdeal R)
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (s : R) (hs : s ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hsA : ∀ g : Γ ℚ,
      (f (ρ g w₀) - f w₀) + (a g - 1) * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2))
    (hhom : ∀ g h : Γ ℚ,
      ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
        - (((f (ρ g v₀) - f v₀) + c g * s)
          + ((f (ρ h v₀) - f v₀) + c h * s))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2)) :
    ∀ g : Γ ℚ,
      (f (ρ g v₀) - f v₀) + c g * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- the corrected trivial component descends to a homomorphism into the
  -- quotient `R ⧸ 𝔪ⁿ⁺²`
  have hhom' : ∀ g h : Γ ℚ,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2))
          ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2))
            ((f (ρ g v₀) - f v₀) + c g * s)
          + Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2))
            ((f (ρ h v₀) - f v₀) + c h * s) := by
    intro g h
    rw [← map_add, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hhom g h
  set φ : (Γ ℚ) →* Multiplicative
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2))
        ((f (ρ g v₀) - f v₀) + c g * s)))
      (fun g h => by rw [hhom' g h, ofAdd_add]) with hφdef
  have hφeq : ∀ g : Γ ℚ, (φ g = 1 ↔
      (f (ρ g v₀) - f v₀) + c g * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2)) := by
    intro g
    rw [hφdef]
    simp only [MonoidHom.mk'_apply, ofAdd_eq_one,
      Ideal.Quotient.eq_zero_iff_mem]
  -- the congruence subgroup of `ρ` at level `n + 2`
  set U : Subgroup (Γ ℚ) :=
    { carrier := {g : Γ ℚ | ∀ x : V, ρ g x - x ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)}
      one_mem' := fun x => by
        rw [map_one, Module.End.one_apply, sub_self]
        exact Submodule.zero_mem _
      mul_mem' := fun {g h} hg hh x => by
        have hsplit : ρ (g * h) x - x
            = (ρ g) ((ρ h) x - x) + ((ρ g) x - x) := by
          rw [show ρ (g * h) x = ρ g (ρ h x) from by rw [map_mul]; rfl,
            map_sub]
          abel
        rw [hsplit]
        exact Submodule.add_mem _
          (apply_mem_smul_top (ρ g : V →ₗ[R] V) (hh x)) (hg x)
      inv_mem' := fun {g} hg x => by
        have hfix : (ρ g⁻¹) ((ρ g) x) = x := by
          rw [show (ρ g⁻¹) ((ρ g) x) = ((ρ g⁻¹) * (ρ g)) x from rfl,
            ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        have hsplit : ρ g⁻¹ x - x = -((ρ g⁻¹) ((ρ g) x - x)) := by
          rw [map_sub, hfix]
          abel
        rw [hsplit]
        exact Submodule.neg_mem _
          (apply_mem_smul_top (ρ g⁻¹ : V →ₗ[R] V) (hg x)) } with hUdef
  have hUopen : IsOpen (U : Set (Γ ℚ)) :=
    isOpen_setOf_forall_sub_mem_pow_smul V ρ (n + 2)
  have hUle : U ≤ φ.ker := by
    intro g hg
    replace hg : ∀ x : V, ρ g x - x ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := hg
    rw [MonoidHom.mem_ker, hφeq g]
    have h1 : f (ρ g v₀) - f v₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      rw [← map_sub]
      exact linearMap_apply_mem_of_mem_smul_top f (hg v₀)
    have hcg : c g ∈ IsLocalRing.maximalIdeal R := by
      refine mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne ?_
      have h2 : c g • w₀ = (ρ g v₀ - v₀) - (ρ g v₀ - (v₀ + c g • w₀)) := by
        abel
      rw [h2]
      refine Submodule.sub_mem _ ?_ (hc g)
      exact Submodule.smul_mono_left
        (Ideal.pow_le_self (by omega)) (hg v₀)
    have h3 : c g * s ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h4 := Ideal.mul_mem_mul hcg hs
      rwa [← pow_succ'] at h4
    exact Submodule.add_mem _ h1 h3
  have hkeropen : IsOpen (φ.ker : Set (Γ ℚ)) :=
    Subgroup.isOpen_mono hUle hUopen
  -- values in `𝔪ⁿ⁺¹` and openness of the congruence kernel, for the
  -- tame leaf at `2`
  have hT1 : ∀ g : Γ ℚ, (f (ρ g v₀) - f v₀) + c g * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 1) := fun g =>
    Submodule.add_mem _ (hf g v₀) (Ideal.mul_mem_left _ _ hs)
  have hTopen : IsOpen {g : Γ ℚ | (f (ρ g v₀) - f v₀) + c g * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 2)} := by
    have hset : {g : Γ ℚ | (f (ρ g v₀) - f v₀) + c g * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2)} = (φ.ker : Set (Γ ℚ)) := by
      ext g
      rw [Set.mem_setOf_eq, SetLike.mem_coe, MonoidHom.mem_ker, hφeq g]
    rw [hset]
    exact hkeropen
  -- the inertia conditions, place by place
  have hin : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ))
      (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      σ ∈ localInertiaGroup v →
      φ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
        σ) = 1 := by
    intro v σ hσ
    obtain ⟨p, hp, rfl⟩ :=
      exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat v
    rw [hφeq]
    by_cases hp2 : p = 2
    · subst hp2
      exact hom_vanishes_on_localInertia_at_two n _ hT1 hhom hTopen σ hσ
    by_cases hp3 : p = 3
    · subst hp3
      exact trivial_component_vanishes_on_localInertia_at_three V hV hρ kk
        hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha c hc hcmul n f hf
        hfv₀ s hs hsA σ hσ
    · haveI hunr : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
        hρ.isUnramified p hp ⟨hp2, hp3⟩
      have hone : (ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat) σ
          = 1 := by
        have hker := GaloisRep.IsUnramifiedAt.localInertiaGroup_le
          (ρ := ρ) (v := hp.toHeightOneSpectrumRingOfIntegersRat) hσ
        simpa [GaloisRep.ker, MonoidHom.mem_ker] using hker
      have hone' : ρ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
        rw [GaloisRep.toLocal_apply] at hone
        exact hone
      have h1 : f (ρ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) v₀) - f v₀ = 0 := by
        rw [hone', Module.End.one_apply, sub_self]
      have hcg : c (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
          IsLocalRing.maximalIdeal R := by
        refine mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne ?_
        have h2 := hc (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ)
        rw [hone', Module.End.one_apply] at h2
        have h3 : v₀ - (v₀ + c (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hp.toHeightOneSpectrumRingOfIntegersRat)) σ) • w₀)
            = -(c (Field.absoluteGaloisGroup.map
              (algebraMap ℚ
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                  hp.toHeightOneSpectrumRingOfIntegersRat)) σ) • w₀) := by
          abel
        rw [h3] at h2
        simpa using Submodule.neg_mem _ h2
      rw [h1, zero_add]
      have h4 := Ideal.mul_mem_mul hcg hs
      rwa [← pow_succ'] at h4
  -- the Minkowski machine closes the node
  intro g
  rw [← hφeq g]
  exact monoidHom_eq_one_of_forall_localInertia φ hkeropen hin g

/-- **The trivial-component Selmer vanishing** (DERIVED 2026-07-22 from
the approximate-homomorphism leaf `trivial_component_hom_vanishes`; the
homomorphism property of the corrected trivial component and the
residual multiplicativity of the off-diagonal entry `c` are PROVEN here
from the residual triangular shape and the ω-correction — Serre, Duke
1987, §5.4): once the ω-component of the defect has been corrected by
`s` (hypothesis `hsA`), the trivial component
`g ↦ (f (ρ g v₀) - f v₀) + c g * s` — the corrected defect evaluated
along the residual trivial-quotient direction `v₀` — is a homomorphism
modulo `𝔪ⁿ⁺²` and vanishes by the leaf (everywhere-unramifiedness from
the hardly ramified conditions, then Minkowski). -/
theorem trivial_component_defect_vanishes
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
    (w₀ : V) (hw₀π : π ((1 : kk) ⊗ₜ[R] w₀) = 0)
    (hw₀ne : (1 : kk) ⊗ₜ[R] w₀ ≠ 0)
    (a : Γ ℚ → R)
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (c : Γ ℚ → R)
    (hc : ∀ g : Γ ℚ, ρ g v₀ - (v₀ + c g • w₀) ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    (n : ℕ) (f : V →ₗ[R] R)
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (s : R) (hs : s ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hsA : ∀ g : Γ ℚ,
      (f (ρ g w₀) - f w₀) + (a g - 1) * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2)) :
    ∀ g : Γ ℚ,
      (f (ρ g v₀) - f v₀) + c g * s ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := by
  -- the off-diagonal entry is residually a twisted crossed homomorphism
  have hcmul : ∀ g h : Γ ℚ,
      c (g * h) - (c g + a g * c h) ∈ IsLocalRing.maximalIdeal R := by
    intro g h
    refine mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne ?_
    have hexp : (c (g * h) - (c g + a g * c h)) • w₀
        = -(ρ (g * h) v₀ - (v₀ + c (g * h) • w₀))
          + ((ρ g v₀ - (v₀ + c g • w₀))
            + (c h • (ρ g w₀ - a g • w₀)
              + ρ g (ρ h v₀ - (v₀ + c h • w₀)))) := by
      rw [show ρ (g * h) v₀ = ρ g (ρ h v₀) from by rw [map_mul]; rfl,
        map_sub, map_add, map_smul]
      module
    rw [hexp]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (hc (g * h)))
      (Submodule.add_mem _ (hc g)
        (Submodule.add_mem _ (Submodule.smul_mem _ _ (ha g))
          (apply_mem_smul_top (ρ g : V →ₗ[R] V) (hc h))))
  -- the corrected trivial component is a homomorphism modulo `𝔪ⁿ⁺²`
  have hhom : ∀ g h : Γ ℚ,
      ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
        - (((f (ρ g v₀) - f v₀) + c g * s)
          + ((f (ρ h v₀) - f v₀) + c h * s))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g h
    have hsplit : ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
          - (((f (ρ g v₀) - f v₀) + c g * s)
            + ((f (ρ h v₀) - f v₀) + c h * s))
        = c h * ((f (ρ g w₀) - f w₀) + (a g - 1) * s)
          + (((f.comp (ρ g : V →ₗ[R] V)) - f) (ρ h v₀ - (v₀ + c h • w₀))
            + (c (g * h) - (c g + a g * c h)) * s) := by
      rw [show ρ (g * h) v₀ = ρ g (ρ h v₀) from by rw [map_mul]; rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
        map_add, map_smul, smul_eq_mul]
      ring
    rw [hsplit]
    refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ (hsA g))
      (Submodule.add_mem _ ?_ ?_)
    · have hDv : ∀ v : V,
          ((f.comp (ρ g : V →ₗ[R] V)) - f) v
            ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
        intro v
        simpa only [LinearMap.sub_apply, LinearMap.comp_apply] using hf g v
      have h2 := linearMap_apply_mem_mul_of_forall_mem _ hDv (hc h)
      rwa [← pow_succ'] at h2
    · have h2 := Ideal.mul_mem_mul (hcmul g h) hs
      rwa [← pow_succ'] at h2
  exact trivial_component_hom_vanishes V hV hρ kk hsurj π hπsurj hπequiv
    v₀ hv₀ w₀ hw₀π hw₀ne a ha c hc hcmul n f hf hfv₀ s hs hsA hhom

/-- **The coboundary form of the one-level obstruction** (sorry node —
the deep arithmetic core, Serre §5.4/Fontaine): for an `R`-linear
functional `f` on `V` which is Galois-equivariant modulo `𝔪 ^ (n + 1)`,
the defect `(g, v) ↦ f (ρ g v) - f v` — a `1`-cocycle on `Γ ℚ` valued
in `Hom(V, 𝔪ⁿ⁺¹)`, reduced modulo `𝔪ⁿ⁺²` a cocycle for the
contragredient residual action on `Hom(V̄, 𝔪ⁿ⁺¹/𝔪ⁿ⁺²)` — is a
coboundary modulo `𝔪ⁿ⁺²`: there is a correction functional `h` with
values in `𝔪ⁿ⁺¹` whose coboundary cancels the defect one level deeper.
Recorded route: the residual dual `V̄*` is an extension of the inverse
mod-3 cyclotomic character `ω⁻¹ = ω` by the trivial character (the
trivial quotient `π` dualizes to the trivial sub). The hardly ramified
conditions (flat at `3`, tame quadratic at `2`, unramified elsewhere)
place the class of the defect cocycle in the Selmer group of
`V̄* ⊗ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` with local conditions "finite flat at `3`, tame at
`2`, unramified outside `{2, 3}`", and that Selmer group vanishes by
Serre's computation for `p = 3`: its graded pieces are Selmer groups of
the trivial character and of `ω`, killed by the class number `1` of `ℚ`
resp. `ℚ(ζ₃)` and the unit computations against the local conditions.
A witness for the vanishing class is the correction `h`. -/
theorem exists_equivariant_defect_coboundary
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
    ∃ h : V →ₗ[R] R,
      (∀ v : V, h v ∈ IsLocalRing.maximalIdeal R ^ (n + 1)) ∧
      (∀ (g : Γ ℚ) (v : V),
        (f (ρ g v) - f v) + (h (ρ g v) - h v) ∈
          IsLocalRing.maximalIdeal R ^ (n + 2)) := by
  classical
  -- Stratum 1 (proven): the residually adapted basis `(w₀, v₀)`
  obtain ⟨b, hb0π, hb0ne, hb1⟩ :=
    exists_residual_adapted_basis V hV kk hsurj π hπsurj v₀ hv₀
  -- Stratum 2 (proven): the residual triangular entries along this basis
  obtain ⟨a, c, hac⟩ :=
    exists_residual_matrix_entries hV kk hsurj π hπsurj hπequiv (b 0) v₀
      hb0π hb0ne
  -- Stratum 3 (leaf): the ω-component correction scalar `s`
  obtain ⟨s, hs, hsA⟩ :=
    exists_omega_component_coboundary V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ (b 0) hb0π hb0ne a (fun g => (hac g).1) n f hf hfv₀
  -- Stratum 4 (leaf): with this correction the trivial component vanishes
  have hsB :=
    trivial_component_defect_vanishes V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ (b 0) hb0π hb0ne a (fun g => (hac g).1) c (fun g => (hac g).2)
      n f hf hfv₀ s hs hsA
  -- the correction functional: `s` times the coordinate along `w₀`
  have hval : ∀ v : V,
      (s • b.coord 0) v ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
    intro v
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hs
  refine ⟨s • b.coord 0, hval, fun g v => ?_⟩
  -- the corrected defect, packaged as a linear map in `v`
  have hLapp : ∀ w : V,
      (f (ρ g w) - f w) + ((s • b.coord 0) (ρ g w) - (s • b.coord 0) w)
        = (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
            - (f + s • b.coord 0)) w := by
    intro w
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply]
    ring
  -- the two basis-vector cases, on clean goals
  have hcase0 : (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
        - (f + s • b.coord 0)) (b 0)
      ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    -- at `b 0`: the ω-component condition plus the `𝔪V`-error
    have hrw : (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
          - (f + s • b.coord 0)) (b 0)
        = ((f (ρ g (b 0)) - f (b 0)) + (a g - 1) * s)
          + (s • b.coord 0) (ρ g (b 0) - a g • b 0) := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, map_sub, map_smul, LinearMap.smul_apply,
        Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul]
      ring
    rw [hrw]
    refine Submodule.add_mem _ (hsA g) ?_
    have h2 := linearMap_apply_mem_mul_of_forall_mem (s • b.coord 0)
      hval ((hac g).1)
    rwa [← pow_succ'] at h2
  have hcase1 : (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
        - (f + s • b.coord 0)) (b 1)
      ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    -- at `b 1 = v₀`: the trivial-component condition plus the error
    rw [show b 1 = v₀ from hb1]
    have hrw : (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
          - (f + s • b.coord 0)) v₀
        = ((f (ρ g v₀) - f v₀) + c g * s)
          + (s • b.coord 0) (ρ g v₀ - (v₀ + c g • b 0)) := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, map_sub, map_add, map_smul,
        LinearMap.smul_apply, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul]
      ring
    rw [hrw]
    refine Submodule.add_mem _ (hsB g) ?_
    have h2 := linearMap_apply_mem_mul_of_forall_mem (s • b.coord 0)
      hval ((hac g).2)
    rwa [← pow_succ'] at h2
  have hmem : ∀ w : V,
      (((f + s • b.coord 0).comp (ρ g : V →ₗ[R] V))
          - (f + s • b.coord 0)) w
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro w
    have hw : w ∈ Submodule.span R (Set.range b) := by
      rw [b.span_eq]
      trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hcase0
      · exact hcase1
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_left _ r hx
  have h3 := hmem v
  rw [← hLapp v] at h3
  exact h3

/-- **The one-step equivariant lift** (DERIVED 2026-07-22 from the
coboundary leaf `exists_equivariant_defect_coboundary`): an `R`-linear
functional on `V` which is Galois-equivariant modulo `𝔪 ^ (n + 1)` and
residually nonvanishing at the marked vector `v₀` (a vector where the
residual trivial-quotient functional `π` is nonzero) can be corrected
to a functional equivariant modulo `𝔪 ^ (n + 2)`, still residually
nonvanishing at `v₀`. The correction is `f' = f + h` for a coboundary
witness `h` valued in `𝔪ⁿ⁺¹`: the new defect is the old defect plus the
coboundary of `h`, which lies in `𝔪ⁿ⁺²` by the leaf, and
`f' v₀ = f v₀ + h v₀ ∉ 𝔪` since `h v₀ ∈ 𝔪ⁿ⁺¹ ≤ 𝔪`. -/
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
  obtain ⟨h, hval, hcob⟩ :=
    exists_equivariant_defect_coboundary V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ n f hf hfv₀
  refine ⟨f + h, fun g v => ?_, fun hmem => ?_⟩
  · have hsplit : (f + h) (ρ g v) - (f + h) v
        = (f (ρ g v) - f v) + (h (ρ g v) - h v) := by
      rw [LinearMap.add_apply, LinearMap.add_apply]
      ring
    rw [hsplit]
    exact hcob g v
  · have hh : h v₀ ∈ IsLocalRing.maximalIdeal R :=
      Ideal.pow_le_self (Nat.succ_ne_zero n) (hval v₀)
    have hfv : f v₀ = (f + h) v₀ - h v₀ := by
      rw [LinearMap.add_apply]
      ring
    exact hfv₀ (hfv ▸ Submodule.sub_mem _ hmem hh)

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
