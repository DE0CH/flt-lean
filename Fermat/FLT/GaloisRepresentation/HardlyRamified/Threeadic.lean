/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

-- Was reached transitively through `ModThree.lean`'s `public import` of it until
-- 2026-07-27, when that edge was removed to take `MazurTorsion` off the critical
-- path (see `GaloisRepresentation/SubQuotCharacter.lean`).  Named explicitly here.
public import Fermat.FLT.FreyCurve.MazurTorsion
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.Deformations.RepresentationTheory.ArtinConductor
-- `wildInertiaGroup` (and `tameFixingSubgroup` behind it), which appear in
-- the STATEMENTS of the tameness leaf
-- `exists_localInertia_generator_of_wildInertia_trivial` and of
-- `wildInertia_fixes_connected_threeTorsion_of_hopf_package` below (the
-- latter PROVEN since 2026-07-27 over
-- `exists_coprime_three_exponent_localInertia_connected_threeTorsion`,
-- which is the Raynaud leaf and does NOT mention the wild inertia). Also
-- `exists_pow_eq_of_mem_wildInertiaGroup`, consumed in that proof. The
-- module imports only `GaloisRep`, which is already in this cone, so the
-- import adds exactly one module to it.
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
import Fermat.FLT.FreyCurve.InertiaCardTransport
-- `inertia_card_dvd_of_card_map_localInertiaGroup_dvd`, the quantitative
-- local-to-global inertia transport of the Kummer-core discriminant route
import Mathlib.Analysis.Real.Pi.Bounds
-- `Real.pi_gt_three`, closing the Minkowski contradiction of the
-- Kummer core at degree `6`
import Fermat.FLT.DedekindDomain.ResidueCardinality
-- `natCard_residue_quotient_toHeightOneSpectrum`, identifying the
-- Frobenius exponent at `2` with `q = 2` in the tame stratum
import Mathlib.Algebra.Module.ZMod
-- `AddCommGroup.zmodModule`, the `ZMod 3`-structure on the graded piece
-- `𝔪ⁿ⁺¹ ⧸ 𝔪ⁿ⁺²` in the Kummer-core reduction
import Mathlib.LinearAlgebra.Dual.Lemmas
-- `Module.forall_dual_apply_eq_zero_iff`, separating points of the
-- graded piece by `ZMod 3`-functionals in the Kummer-core reduction
import Fermat.FLT.GroupScheme.ConnectedEtale
-- `OortTate.displacement_point_apply_idempotent_eq_one` (the étale half of
-- the connected–étale dichotomy) and
-- `Bialgebra.exists_connected_counit_idempotent` (the connected counit
-- idempotent of a finite flat Hopf order), both consumed by
-- `inertia_displacement_apply_connected_idempotent_eq_one` below and by the
-- two Hopf-package cores that hand its conclusion to their Raynaud leaves.
-- (`ModThree` imports this module non-publicly, so it is not re-exported and
-- must be imported here directly.)
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
-- `vendored_one_eq_convOne` / `vendored_mul_eq_convMul` (the vendored
-- bare-hom convolution monoid is mathlib's `WithConv` monoid) and
-- `liftEquiv_symm_convOne` / `liftEquiv_symm_convMul` (the tensor-hom
-- adjunction is a convolution monoid map): proof-body use in the
-- connected-locus block below. `ModThree` imports this module
-- non-publicly, so it is not re-exported either.

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

/-- **The residue package** (PROVEN; label corrected 2026-07-25 — the
proof below is complete, the stale `sorry node` marker had been
harvested into phantom dispatches): a local, topological,
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
    refine isOpen_biUnion fun y _ => ?_
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

/-- **Degenerate flatness over the trivial quotient** (PROVEN; label
corrected 2026-07-25): a Galois
representation on a subsingleton module has a flat prolongation at `3` — the
trivial group scheme `Spec 𝒪ᵥ` works, its geometric points being the single
algebra map matched with the single element of the space. -/
theorem hasFlatProlongationAt_of_subsingleton {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    [Subsingleton M'] (ρ' : GaloisRep ℚ A' M') :
    ρ'.HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  set v := Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat
  set Kv := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
  set Ov := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
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
        map_smul' := fun g _ => (smul_zero g).symm
        map_zero' := rfl
        map_add' := fun _ _ => (add_zero (0 : M')).symm }
  · constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      refine ⟨Additive.ofMul ((Algebra.ofId Kv (AlgebraicClosure Kv)).comp
        (Algebra.TensorProduct.rid Ov Kv Kv).toAlgHom), ?_⟩
      exact Subsingleton.elim _ y

/-- **The residual space identification** (PROVEN; label corrected
2026-07-25): the double base
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

/-- **Tameness at `2` transfers to the residue field** (PROVEN; label
corrected 2026-07-25): the
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

/-- **Mod-3 reduction of the 3-adic cyclotomic character, kernel case**
(PROVEN 2026-07-23 — the reduction compatibility): on the kernel of the
mod-3 cyclotomic character the 3-adic cyclotomic character is
`≡ 1 mod 3`. Route: `cyclotomicCharacter.toZModPow` (at level `3¹`)
identifies the reduction of the 3-adic character with
`modularCyclotomicCharacter`, which is `cyclotomicCharacterModL 3`
(definitional); the hypothesis makes that reduction `1`, and
`PadicInt.ker_toZModPow` converts the vanishing of `χ - 1` into
span-membership. -/
theorem cyclotomicCharacter_sub_one_mem_span_three (g : Γ ℚ)
    (hg : cyclotomicCharacterModL 3 g = 1) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
      ℤ_[3]ˣ) : ℤ_[3]) - 1 ∈ Ideal.span ({(3 : ℤ_[3])} : Set ℤ_[3]) := by
  have hker : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
      ℤ_[3]ˣ) : ℤ_[3]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := 3) 1) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero,
      cyclotomicCharacter.toZModPow]
    have h2 : modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ)
          (3 ^ 1))
        g.toRingEquiv = cyclotomicCharacterModL 3 g := rfl
    rw [h2, hg]
    rfl
  rwa [PadicInt.ker_toZModPow, pow_one] at hker

/-- **Mod-3 reduction of the 3-adic cyclotomic character, non-kernel
case** (PROVEN 2026-07-23 — the reduction compatibility): off the
kernel of the mod-3 cyclotomic character — where the character takes
its only other value `-1` in `(ZMod 3)ˣ` — the 3-adic cyclotomic
character is `≡ -1 mod 3`. Same route as the kernel case, with the
two-element group `(ZMod 3)ˣ` forcing the value `-1`. -/
theorem cyclotomicCharacter_add_one_mem_span_three (g : Γ ℚ)
    (hg : cyclotomicCharacterModL 3 g ≠ 1) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
      ℤ_[3]ˣ) : ℤ_[3]) + 1 ∈ Ideal.span ({(3 : ℤ_[3])} : Set ℤ_[3]) := by
  have hcases : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide
  have hneg : cyclotomicCharacterModL 3 g = -1 :=
    (hcases _).resolve_left hg
  have hker : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
      ℤ_[3]ˣ) : ℤ_[3]) + 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := 3) 1) := by
    rw [RingHom.mem_ker, map_add, map_one, cyclotomicCharacter.toZModPow]
    have h2 : modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ)
          (3 ^ 1))
        g.toRingEquiv = cyclotomicCharacterModL 3 g := rfl
    rw [h2, hneg]
    decide
  rwa [PadicInt.ker_toZModPow, pow_one] at hker

/-- **The residual determinant is the diagonal entry** (PROVEN 2026-07-23
— the determinant computation of the triangular reduction): along the
residually adapted pair `(w₀, v₀)` — with `w₀` residually spanning the
line `ker π` and the quotient character trivial (`hπequiv`) — the
determinant of `ρ g` is residually the diagonal entry `a g`. Route:
`(w₀, v₀)` is an `R`-basis of `V` (residually independent by
`hv₀`/`hw₀ne`, hence a basis by the Nakayama argument of
`exists_residual_adapted_basis`); in the base-changed basis the matrix
of `(ρ.baseChange kk) g` is triangular with diagonal `(ā g, 1)` (the
`1` from `hπequiv`), so `LinearMap.det_baseChange` computes the
reduction of `det (ρ g)` as `ā g`, and `ker (algebraMap R kk) = 𝔪`
(kernel of a surjection onto a field over the local `R`) converts the
residual identity into membership. -/
theorem det_sub_residual_a_mem_maximalIdeal
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
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
    ρ.det g - a g ∈ IsLocalRing.maximalIdeal R := by
  classical
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  -- the residually adapted basis `(b 0, b 1) = (u₀, v₀)`
  obtain ⟨b, hb0π, hb0ne, hb1⟩ :=
    exists_residual_adapted_basis V hV kk hsurj π hπsurj v₀ hv₀
  set bb : Module.Basis (Fin 2) kk (kk ⊗[R] V) := b.baseChange kk with hbbdef
  have hbb0 : bb 0 = (1 : kk) ⊗ₜ[R] b 0 := Module.Basis.baseChange_apply kk b 0
  have hbb1 : bb 1 = (1 : kk) ⊗ₜ[R] b 1 := Module.Basis.baseChange_apply kk b 1
  -- the residual endomorphism is the base change of `ρ g`
  have hT : ((ρ.baseChange kk) g : Module.End kk (kk ⊗[R] V)) =
      LinearMap.baseChange kk (ρ g) := by
    refine Module.Basis.ext bb fun i => ?_
    rw [show bb i = (1 : kk) ⊗ₜ[R] (b i) from
        Module.Basis.baseChange_apply kk b i,
      LinearMap.baseChange_tmul]
    exact GaloisRep.baseChange_tmul ρ g 1 (b i)
  -- determinant transfer along base change
  have hdet : LinearMap.det ((ρ.baseChange kk) g : Module.End kk (kk ⊗[R] V)) =
      algebraMap R kk (ρ.det g) := by
    rw [hT, LinearMap.det_baseChange, GaloisRep.det_apply]
  -- the matrix of the residual endomorphism
  set M2 : Matrix (Fin 2) (Fin 2) kk :=
    LinearMap.toMatrix bb bb ((ρ.baseChange kk) g) with hM2
  have hentry : ∀ i j, M2 i j =
      bb.repr ((ρ.baseChange kk) g (bb j)) i := fun i j =>
    LinearMap.toMatrix_apply bb bb _ i j
  have hdet2 : LinearMap.det ((ρ.baseChange kk) g : Module.End kk (kk ⊗[R] V)) =
      M2.det := (LinearMap.det_toMatrix bb _).symm
  -- the kernel of `π` is the residual line through `1 ⊗ b 0`
  haveI : Module.Finite kk (kk ⊗[R] V) := Module.Finite.of_basis bb
  have hfr : Module.finrank kk (kk ⊗[R] V) = 2 := by
    rw [Module.finrank_eq_card_basis bb, Fintype.card_fin]
  have hker1 : Module.finrank kk (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπsurj, finrank_top, Module.finrank_self,
      hfr] at h
    omega
  have hkerspan : (LinearMap.ker π : Submodule kk (kk ⊗[R] V)) =
      Submodule.span kk {(1 : kk) ⊗ₜ[R] b 0} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr hb0π
    · rw [hker1, finrank_span_singleton hb0ne]
  -- the residual endomorphism preserves the line, with eigenvalue `x0`
  have hDb0mem : (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] b 0) ∈
      Submodule.span kk {(1 : kk) ⊗ₜ[R] b 0} := by
    rw [← hkerspan, LinearMap.mem_ker, hπequiv g]
    exact hb0π
  obtain ⟨x0, hx0⟩ := Submodule.mem_span_singleton.mp hDb0mem
  -- lower-left entry vanishes
  have hM10 : M2 1 0 = 0 := by
    rw [hentry 1 0, hbb0, ← hx0, map_smul, ← hbb0, Module.Basis.repr_self]
    simp
  -- lower-right entry is `1` (the trivial quotient character)
  have hM11 : M2 1 1 = 1 := by
    have hsum1 := bb.sum_repr ((ρ.baseChange kk) g (bb 1))
    rw [Fin.sum_univ_two] at hsum1
    have hπ1 := hπequiv g (bb 1)
    rw [← hsum1, map_add, map_smul, map_smul] at hπ1
    have hπbb0 : π (bb 0) = 0 := by rw [hbb0]; exact hb0π
    have hπbb1ne : π (bb 1) ≠ 0 := by rw [hbb1, hb1]; exact hv₀
    rw [hπbb0, smul_zero, zero_add, smul_eq_mul] at hπ1
    have h2 : (bb.repr ((ρ.baseChange kk) g (bb 1)) 1 - 1) * π (bb 1) = 0 := by
      rw [sub_mul, one_mul, hπ1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · rw [hentry 1 1]
      exact sub_eq_zero.mp h
    · exact absurd h hπbb1ne
  -- the eigenvalue is residually `a g`, through the `w₀`-line
  have hw₀mem : (1 : kk) ⊗ₜ[R] w₀ ∈
      Submodule.span kk {(1 : kk) ⊗ₜ[R] b 0} := by
    rw [← hkerspan]
    exact LinearMap.mem_ker.mpr hw₀π
  obtain ⟨y0, hy0⟩ := Submodule.mem_span_singleton.mp hw₀mem
  have hy0ne : y0 ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hy0
    exact hw₀ne hy0.symm
  have hDw₀ : (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] w₀) =
      algebraMap R kk (a g) • ((1 : kk) ⊗ₜ[R] w₀) := by
    have h0 : (1 : kk) ⊗ₜ[R] (ρ g w₀ - a g • w₀) = 0 :=
      one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj (ha g)
    rw [TensorProduct.tmul_sub, sub_eq_zero, one_tmul_smul] at h0
    calc (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] w₀)
        = (1 : kk) ⊗ₜ[R] (ρ g w₀) := GaloisRep.baseChange_tmul ρ g 1 w₀
      _ = algebraMap R kk (a g) • ((1 : kk) ⊗ₜ[R] w₀) := h0
  have hxa : x0 = algebraMap R kk (a g) := by
    have h1 : (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] w₀) =
        y0 • ((ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] b 0)) := by
      rw [← map_smul, hy0]
    rw [hDw₀, ← hy0, ← hx0, smul_smul, smul_smul] at h1
    have h3 : algebraMap R kk (a g) * y0 = y0 * x0 :=
      smul_left_injective kk hb0ne h1
    have h4 : y0 * (algebraMap R kk (a g) - x0) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 hy0ne
    · exact (sub_eq_zero.mp h5).symm
  -- upper-left entry is residually `a g`
  have hM00 : M2 0 0 = algebraMap R kk (a g) := by
    rw [hentry 0 0, hbb0, ← hx0, map_smul, ← hbb0, Module.Basis.repr_self,
      ← hxa]
    simp
  -- assemble the determinant and read off the congruence
  have hdetval : algebraMap R kk (ρ.det g) = algebraMap R kk (a g) := by
    rw [← hdet, hdet2, Matrix.det_fin_two, hM00, hM11, hM10, mul_one,
      mul_zero, sub_zero]
  rw [← hker, RingHom.mem_ker, map_sub, hdetval, sub_self]

/-- **The residual twist is the mod-3 cyclotomic character** (DERIVED
2026-07-23 from the three leaves above — the determinant identification;
Serre, Duke 1987, §5.4): along the
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
  -- the determinant is residually the diagonal entry `a`
  have hdet_a : ρ.det g - a g ∈ IsLocalRing.maximalIdeal R :=
    det_sub_residual_a_mem_maximalIdeal V hV kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne a ha g
  -- span-membership in `ℤ₃` transports into the maximal ideal of `R`
  have htrans : ∀ x : ℤ_[3], x ∈ Ideal.span ({(3 : ℤ_[3])} : Set ℤ_[3]) →
      algebraMap ℤ_[3] R x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
    have h3 : algebraMap ℤ_[3] R (3 : ℤ_[3]) = (3 : R) := by
      rw [show (3 : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) by norm_cast, map_natCast]
      norm_cast
    rw [← hy, map_mul, h3]
    exact Ideal.mul_mem_left _ _ three_mem_maximalIdeal
  constructor
  · intro h1
    have hchi := htrans _ (cyclotomicCharacter_sub_one_mem_span_three g h1)
    rw [map_sub, map_one, ← hρ.det g] at hchi
    have heq : a g - 1 = (ρ.det g - 1) - (ρ.det g - a g) := by ring
    rw [heq]
    exact Ideal.sub_mem _ hchi hdet_a
  · intro h1
    have hchi := htrans _ (cyclotomicCharacter_add_one_mem_span_three g h1)
    rw [map_add, map_one, ← hρ.det g] at hchi
    have heq : a g + 1 = (ρ.det g + 1) - (ρ.det g - a g) := by ring
    rw [heq]
    exact Ideal.sub_mem _ hchi hdet_a

/-- **Openness of the congruence subgroup** (PROVEN 2026-07-23 — the
continuity stratum): the set of `g ∈ Γ ℚ` acting trivially modulo `𝔪ᵏ`
is open. `ρ` is continuous into `End V` with the `R`-module topology;
along a basis of `V` the congruence condition is a finite intersection
of conditions "matrix entry lies in a translate of `𝔪ᵏ`", each an open
condition: the entry functionals are `R`-linear hence continuous
(`IsModuleTopology.continuous_of_linearMap`), and `𝔪ᵏ ⊆ R` is open by
`IsLocalRing.isOpen_maximalIdeal_pow` (`R` is a compact Hausdorff
Noetherian topological ring — transport along a `ℤ₃`-basis). -/
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
  classical
  letI := moduleTopology R (Module.End R V)
  haveI : IsModuleTopology R (Module.End R V) := ⟨rfl⟩
  -- `R` is a compact Hausdorff Noetherian topological ring, so `𝔪ᵏ` is
  -- open (`IsLocalRing.isOpen_maximalIdeal_pow`)
  haveI hNoeth : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  let eR : R ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    (Module.Free.chooseBasis ℤ_[3] R).equivFun
  have hcont₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcont₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let homR : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  haveI : CompactSpace R := homR.symm.compactSpace
  haveI : T2Space R := homR.symm.symm.isEmbedding.t2Space
  have hIk : IsOpen ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) :=
    IsLocalRing.isOpen_maximalIdeal_pow R k
  -- coordinates along a basis of `V` detect the congruence condition
  let b := Module.Free.chooseBasis R V
  have hmem : ∀ y : V,
      y ∈ (IsLocalRing.maximalIdeal R ^ k) • (⊤ : Submodule R V)
      ↔ ∀ j, b.repr y j ∈ IsLocalRing.maximalIdeal R ^ k := by
    intro y
    constructor
    · intro hy j
      refine Submodule.smul_induction_on hy (fun r hr v _ => ?_)
        fun v w hv hw => ?_
      · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · rw [map_add, Finsupp.add_apply]
        exact Ideal.add_mem _ hv hw
    · intro hy
      have hrepr := b.sum_repr y
      rw [← hrepr]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem_smul (hy j) trivial
  -- the congruence set is the `ρ`-preimage of an open set of matrix type
  have hset : {g : Γ ℚ | ∀ x : V, ρ g x - x ∈
        (IsLocalRing.maximalIdeal R ^ k) • (⊤ : Submodule R V)}
      = ⇑ρ ⁻¹' (⋂ (i) (j),
          ((b.coord j).comp (LinearMap.applyₗ (b i))) ⁻¹'
            {r : R | r - b.repr (b i) j ∈
              IsLocalRing.maximalIdeal R ^ k}) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_iInter,
      LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      Module.Basis.coord_apply]
    constructor
    · intro hg i j
      have h1 := (hmem _).mp (hg (b i)) j
      rwa [map_sub, Finsupp.sub_apply] at h1
    · intro hg x
      have hbase : ∀ i, ρ g (b i) - b i ∈
          (IsLocalRing.maximalIdeal R ^ k) • (⊤ : Submodule R V) := by
        intro i
        rw [hmem]
        intro j
        have h1 := hg i j
        rw [map_sub, Finsupp.sub_apply]
        exact h1
      set D : V →ₗ[R] V := (ρ g : V →ₗ[R] V) - LinearMap.id
      have happly : ∀ v, D v = ρ g v - v := fun v => rfl
      have hx : ρ g x - x = ∑ i, b.repr x i • (ρ g (b i) - b i) :=
        calc ρ g x - x
            = D x := (happly x).symm
          _ = D (∑ i, b.repr x i • b i) := by rw [Module.Basis.sum_repr]
          _ = ∑ i, b.repr x i • (D (b i)) := by
              rw [map_sum]
              simp_rw [map_smul]
          _ = ∑ i, b.repr x i • (ρ g (b i) - b i) := by simp_rw [happly]
      rw [hx]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (hbase i)
  rw [hset]
  refine (ContinuousMonoidHom.continuous_toFun ρ).isOpen_preimage _ ?_
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (IsModuleTopology.continuous_of_linearMap _).isOpen_preimage _ ?_
  have htr : {r : R | r - b.repr (b i) j ∈ IsLocalRing.maximalIdeal R ^ k}
      = (fun r : R => r - b.repr (b i) j) ⁻¹'
        ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := rfl
  rw [htr]
  exact (continuous_sub_right _).isOpen_preimage _ hIk

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

/-- **An almost-invariant functional is invariant one level deeper on
`𝔪 • ⊤`** (helper, PROVEN 2026-07-25): if `f (T v) - f v ∈ 𝔪ⁿ⁺¹` for
every `v`, then for `m ∈ 𝔪 • (⊤ : Submodule R V)` the same difference
lands in `𝔪ⁿ⁺²`, because `f (T (r • v)) - f (r • v) = r * (f (T v) - f v)`
and `r ∈ 𝔪`. This is the reason the `ω`-defect below is a cocycle
modulo `𝔪ⁿ⁺²` and not merely modulo `𝔪ⁿ⁺¹`. -/
theorem linearMap_sub_mem_pow_succ_of_mem_smul_top
    {R : Type u} [CommRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {n : ℕ} {f : V →ₗ[R] R} (T : V →ₗ[R] V)
    (hT : ∀ v : V, f (T v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    {m : V} (hm : m ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) :
    f (T m) - f m ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  refine Submodule.smul_induction_on hm (fun r hr v _ => ?_) fun x y hx hy => ?_
  · have h1 : f (T (r • v)) - f (r • v) = r * (f (T v) - f v) := by
      simp only [map_smul, smul_eq_mul]; ring
    rw [h1]
    have h3 := Ideal.mul_mem_mul hr (hT v)
    rwa [← pow_succ'] at h3
  · have h2 : f (T (x + y)) - f (x + y) = (f (T x) - f x) + (f (T y) - f y) := by
      simp only [map_add]; ring
    rw [h2]
    exact Ideal.add_mem _ hx hy

/-- **The `ω`-defect is an `ω`-twisted cocycle modulo `𝔪ⁿ⁺²`** (PROVEN
2026-07-25): writing `d g = f (ρ g w₀) - f w₀` for the defect of the
almost-invariant functional `f` along the almost-eigenvector `w₀`,

`d (g * h) ≡ a h * d g + d h    (mod 𝔪ⁿ⁺²)`.

Proof: `ρ (g * h) w₀ = ρ g (ρ h w₀)` and `ρ h w₀ = a h • w₀ + m` with
`m := ρ h w₀ - a h • w₀ ∈ 𝔪 • ⊤` by `ha`; expanding, the difference
`d (g * h) - (a h * d g + d h)` is exactly `f (ρ g m) - f m`, which lies
in `𝔪ⁿ⁺²` by `linearMap_sub_mem_pow_succ_of_mem_smul_top`.

The twisting function is `a`, whose residue is the mod-3 cyclotomic
character `ω` (`residual_twist_eq_cyclotomicCharacterModL`) — which is
what makes the conclusion of `omega_defect_coboundary_of_hopf_package`
an honest `ω`-coboundary condition rather than a shape coincidence. -/
theorem omega_defect_cocycle
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {ρ : GaloisRep ℚ R V} {a : Γ ℚ → R} {w₀ : V}
    (ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V))
    {n : ℕ} {f : V →ₗ[R] R}
    (hf : ∀ (g : Γ ℚ) (v : V),
      f (ρ g v) - f v ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (g h : Γ ℚ) :
    (f (ρ (g * h) w₀) - f w₀)
        - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
      ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  have hstep := linearMap_sub_mem_pow_succ_of_mem_smul_top (ρ g) (hf g) (ha h)
  have hmul : ρ (g * h) w₀ = ρ g (ρ h w₀) := by rw [map_mul]; rfl
  have hexp : (f (ρ (g * h) w₀) - f w₀)
        - (a h * (f (ρ g w₀) - f w₀) + (f (ρ h w₀) - f w₀))
      = f (ρ g (ρ h w₀ - a h • w₀)) - f (ρ h w₀ - a h • w₀) := by
    rw [hmul]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hexp]
  exact hstep

/-- **An `ω`-twisted cocycle vanishing on the cyclotomic kernel is an
`ω`-coboundary** (PROVEN 2026-07-25 — the entire non-finite-flat half of
`omega_defect_coboundary_of_hopf_package` below): let `d` take values in
`𝔪ⁿ⁺¹`, satisfy the `ω`-twisted cocycle identity modulo `𝔪ⁿ⁺²`, and let
the twisting function `a` be residually `ω` in the two-sided form
supplied by `residual_twist_eq_cyclotomicCharacterModL` (`ha1`: `a g ≡ 1`
when `ω g = 1`; `ha2`: `a g ≡ -1` otherwise). If `d` vanishes modulo
`𝔪ⁿ⁺²` on `S ∩ ker ω`, then `d` is an `ω`-coboundary on the whole of `S`.

Why this is elementary rather than arithmetic: `ω` takes values in
`(ZMod 3)ˣ`, a group of order `2`, and `2` is a UNIT of `R` (`3 ∈ 𝔪` by
`three_mem_maximalIdeal`, so `2 = 3 - 1 ∉ 𝔪`). So `d` factors through a
group of order dividing `2` acting on a `3`-torsion graded piece, and
`H¹` of a group whose order is invertible vanishes. Explicitly: if `ω` is
trivial on `S` take `lam = 0`; otherwise choose `σ₀ ∈ S` with `ω σ₀ ≠ 1`,
note that `a σ₀ - 1` is then a unit, and take
`lam = -(a σ₀ - 1)⁻¹ * d σ₀`.

**CUT AUDIT (2026-07-25).** Together with `omega_defect_cocycle` this
shows the coboundary conclusion of
`omega_defect_coboundary_of_hopf_package` is EQUIVALENT to its own
`ker ω` specialisation, which is the statement of the consumer
`omega_defect_vanishes_of_hopf_package`: the consumer's proof is the
forward direction, and this theorem supplies the converse. So the split
between those two declarations moves no mathematics. All of the
remaining content is the single `ker ω` vanishing statement — that is
where the finite-flat/Raynaud input enters, and that is where the
surviving `sorry` now sits. -/
theorem exists_coboundary_of_cocycle_of_vanishing_on_cyclotomicKernel
    {R : Type u} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [IsLocalRing R]
    {H : Type*} [Group H] (e : H →* Γ ℚ) (S : Subgroup H)
    (n : ℕ) (a d : Γ ℚ → R)
    (hd : ∀ g : Γ ℚ, d g ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hcoc : ∀ g h : Γ ℚ,
      d (g * h) - (a h * d g + d h) ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (ha1 : ∀ g : Γ ℚ, cyclotomicCharacterModL 3 g = 1 →
      a g - 1 ∈ IsLocalRing.maximalIdeal R)
    (ha2 : ∀ g : Γ ℚ, cyclotomicCharacterModL 3 g ≠ 1 →
      a g + 1 ∈ IsLocalRing.maximalIdeal R)
    (hker : ∀ σ ∈ S, cyclotomicCharacterModL 3 (e σ) = 1 →
      d (e σ) ∈ IsLocalRing.maximalIdeal R ^ (n + 2)) :
    ∃ lam : R, lam ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ∧
      ∀ σ ∈ S, d (e σ) + (a (e σ) - 1) * lam
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- `2` is a unit of `R`: `3 ∈ 𝔪` and `(3 : R) - 2 = 1`
  have h2 : (2 : R) ∉ IsLocalRing.maximalIdeal R := by
    intro h
    have h3 : (3 : R) ∈ IsLocalRing.maximalIdeal R := three_mem_maximalIdeal
    have h4 := Ideal.sub_mem _ h3 h
    have h5 : (3 : R) - 2 = 1 := by norm_num
    rw [h5] at h4
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one _).mpr h4)
  -- so the residual value `-1` of `a` makes `a - 1` a unit
  have hne : ∀ x : R, x + 1 ∈ IsLocalRing.maximalIdeal R →
      x - 1 ∉ IsLocalRing.maximalIdeal R := by
    intro x hx hx'
    refine h2 ?_
    have h6 := Ideal.sub_mem _ hx hx'
    have h7 : (x + 1) - (x - 1) = (2 : R) := by ring
    rwa [h7] at h6
  by_cases hall : ∃ σ ∈ S, cyclotomicCharacterModL 3 (e σ) ≠ 1
  · obtain ⟨σ₀, hσ₀S, hσ₀ω⟩ := hall
    have hu : IsUnit (a (e σ₀) - 1) := by
      have h8 := hne _ (ha2 _ hσ₀ω)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h8
      exact h8
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    have hlam : -(u * d (e σ₀)) ∈ IsLocalRing.maximalIdeal R ^ (n + 1) :=
      Submodule.neg_mem _ (Ideal.mul_mem_left _ _ (hd _))
    refine ⟨-(u * d (e σ₀)), hlam, fun σ hσ => ?_⟩
    by_cases hσω : cyclotomicCharacterModL 3 (e σ) = 1
    · -- on the cyclotomic kernel both summands die separately
      have hA := hker σ hσ hσω
      have hB : (a (e σ) - 1) * -(u * d (e σ₀))
          ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
        have h9 := Ideal.mul_mem_mul (ha1 _ hσω) hlam
        rwa [← pow_succ'] at h9
      exact Ideal.add_mem _ hA hB
    · -- off it, `ω σ = ω σ₀` because `(ZMod 3)ˣ` has order `2`
      have hval : ∀ x y : (ZMod 3)ˣ, x ≠ 1 → y ≠ 1 → x = y := by decide
      have heq : cyclotomicCharacterModL 3 (e σ) = cyclotomicCharacterModL 3 (e σ₀) :=
        hval _ _ hσω hσ₀ω
      have hτS : σ * σ₀⁻¹ ∈ S := S.mul_mem hσ (S.inv_mem hσ₀S)
      have hτω : cyclotomicCharacterModL 3 (e (σ * σ₀⁻¹)) = 1 := by
        simp [map_mul, map_inv, heq]
      have hτ := hker _ hτS hτω
      have hmul : e (σ * σ₀⁻¹) * e σ₀ = e σ := by
        rw [map_mul, map_inv]; group
      have hcoc' := hcoc (e (σ * σ₀⁻¹)) (e σ₀)
      rw [hmul] at hcoc'
      -- the cocycle identity transports the value at `σ₀` to the value at `σ`
      have hA : d (e σ) - d (e σ₀) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
        have h10 : a (e σ₀) * d (e (σ * σ₀⁻¹))
            ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := Ideal.mul_mem_left _ _ hτ
        have h11 : d (e σ) - d (e σ₀)
            = (d (e σ) - (a (e σ₀) * d (e (σ * σ₀⁻¹)) + d (e σ₀)))
              + a (e σ₀) * d (e (σ * σ₀⁻¹)) := by ring
        rw [h11]
        exact Ideal.add_mem _ hcoc' h10
      have hB : a (e σ) - a (e σ₀) ∈ IsLocalRing.maximalIdeal R := by
        have h12 := Ideal.sub_mem _ (ha2 _ hσω) (ha2 _ hσ₀ω)
        have h13 : (a (e σ) + 1) - (a (e σ₀) + 1) = a (e σ) - a (e σ₀) := by ring
        rwa [h13] at h12
      have hC : (a (e σ) - a (e σ₀)) * -(u * d (e σ₀))
          ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
        have h14 := Ideal.mul_mem_mul hB hlam
        rwa [← pow_succ'] at h14
      -- and `lam` was chosen to annihilate the value at `σ₀` exactly
      have hD : d (e σ₀) + (a (e σ₀) - 1) * -(u * d (e σ₀)) = 0 := by
        have h15 : (a (e σ₀) - 1) * -(u * d (e σ₀))
            = -((a (e σ₀) - 1) * u * d (e σ₀)) := by ring
        rw [h15, hu']
        ring
      have h16 : d (e σ) + (a (e σ) - 1) * -(u * d (e σ₀))
          = (d (e σ) - d (e σ₀)) + (a (e σ) - a (e σ₀)) * -(u * d (e σ₀))
            + (d (e σ₀) + (a (e σ₀) - 1) * -(u * d (e σ₀))) := by ring
      rw [h16, hD, add_zero]
      exact Ideal.add_mem _ hA hC
  · -- `ω` is trivial on `S`: the zero coboundary already works
    have hall' : ∀ σ ∈ S, cyclotomicCharacterModL 3 (e σ) = 1 := by
      intro σ hσ
      by_contra hc
      exact hall ⟨σ, hσ, hc⟩
    refine ⟨0, Submodule.zero_mem _, fun σ hσ => ?_⟩
    simpa using hker σ hσ (hall' σ hσ)


local notation "𝔭₃" => Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat
local notation "𝒪₃ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
  Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat
local notation "ℚ₃ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
  Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat
local notation "ℚ₃ᵥᵃˡᵍ" => AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
  Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Inertia displacements are connected, through a Hopf package**
(PROVEN 2026-07-25 — the étale half of the connected–étale dichotomy,
transported through an arbitrary flat-prolongation package at `3`): if
the geometric points of the generic fibre of a finite flat Hopf order
`G` over `𝒪ᵥ ≅ ℤ₃` are `Γ ℚ₃ᵥ`-equivariantly identified with the space
of a Galois representation `ρ'` by a bijection `fG`, then for every
local inertia element `σ` at `3` and every vector `m`, the point of the
displacement `ρ'(σ)m - m` takes the value `1` on any counit-one
idempotent `e₀` — i.e. every inertia displacement lies in the CONNECTED
part of the model.

Proof: the identification turns the trivial rewriting
`(ρ'(σ)m - m) + m = ρ'(σ)m` into the convolution identity
`δ ⋆ φ = σ • φ` between the point `φ` of `m` and the point `δ` of the
displacement (`map_add`/`map_smul` of the equivariant bijection, read
through `Additive.toMul`), which is exactly the hypothesis of the
PROVEN generic-place lemma
`OortTate.displacement_point_apply_idempotent_eq_one`: the value of `δ`
on `e₀` is an idempotent of a field congruent to `1` modulo the maximal
ideal of the integral closure, hence `1`. Conceptually: the étale
quotient of the model has unramified points, so inertia displacements
die in it.

This is step (2) of the recorded route of BOTH Hopf-package cores
below, and it is handed to their Raynaud leaves
(`omega_defect_coboundary_of_hopf_package` and
`invariant_functional_defect_vanishes_of_hopf_package`) as the
hypothesis `hconn`, so that what those leaves still owe is only the
CLASSIFICATION content. -/
theorem inertia_displacement_apply_connected_idempotent_eq_one
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Finite 𝒪₃ᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (σ : Γ ℚ₃ᵥ) (hσ : σ ∈ localInertiaGroup 𝔭₃)
    (m : N) :
    (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((ρ'.toLocal 𝔭₃) σ m - m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
  classical
  set g := Equiv.ofBijective fG hfG
  have hfs : ∀ x : (ρ'.toLocal 𝔭₃).Space, fG (g.symm x) = x :=
    fun x => g.apply_symm_apply x
  set d : N := (ρ'.toLocal 𝔭₃) σ m - m with hd
  -- the displacement point multiplies the point of `m` into its translate
  have hXd : g.symm d + g.symm m = σ • g.symm m := by
    apply g.injective
    show fG (g.symm d + g.symm m) = fG (σ • g.symm m)
    rw [map_add fG, map_smul fG, hfs, hfs]
    show d + m = (ρ'.toLocal 𝔭₃) σ m
    rw [hd, sub_add_cancel]
  have hDφ : Additive.toMul (g.symm d) * Additive.toMul (g.symm m) =
      σ • Additive.toMul (g.symm m) := by
    have h1 := congrArg Additive.toMul hXd
    have h2 : Additive.toMul (σ • g.symm m) =
        σ • Additive.toMul (g.symm m) := rfl
    rw [toMul_add, h2] at h1
    exact h1
  exact OortTate.displacement_point_apply_idempotent_eq_one 𝔭₃ G e₀ he₀ hε₀ σ hσ
    (Additive.toMul (g.symm m)) (Additive.toMul (g.symm d)) hDφ

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **An inertia-fixed connected point of ANY `3`-power order is the
identity** (PROVEN 2026-07-26 — the `3`-power-torsion generalisation of
the Raynaud leaf `inertiaFixed_connected_point_eq_one_at_three`, which
is stated only for points killed by `3`).

The generalisation is what the CONGRUENCE levels need: the module of a
Hopf package at the ideal `𝔪ⁿ⁺²` is killed by `3ⁿ⁺²` and NOT by `3`,
so the order-`3` form of the leaf sees only the socle `𝔪ⁿ⁺¹ · M` and is
useless above the residual level.

Proof: descending induction on the exponent. The connected locus is a
SUBMONOID of the convolution group — `convMul_apply_one_of_comul_absorbs`
says two points with value `1` on `e₀` convolve to one, which is exactly
the comultiplication absorption `Δe₀ · (e₀ ⊗ e₀) = e₀ ⊗ e₀` of a
connected counit idempotent — and `σ • (-)` is a monoid map for
convolution (`smul_pow'` of the `MulDistribMulAction` on the bare-hom
monoid), so `φ ^ 3` is again connected and inertia-fixed while its order
drops by one power of `3`. Unwinding to order `3` hands the point to the
order-`3` leaf. No new group-scheme input enters: the ramification
content is entirely inside `inertiaFixed_connected_point_eq_one_at_three`
(`e = 1 < 2 = p − 1`, so the kernel of reduction over `𝒪ⁿʳ` is
torsion-free at `3`). -/
theorem inertiaFixed_connected_point_eq_one_at_three_of_threePow
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G] [Module.Finite 𝒪₃ᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (N : ℕ) (φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1)
    (hord : φ ^ (3 ^ N) = 1)
    (hfix : ∀ σ ∈ localInertiaGroup 𝔭₃, σ • φ = φ) :
    φ = 1 := by
  -- the connected locus is closed under convolution
  have hmulconn : ∀ ψ χ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ,
      ψ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → χ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (ψ * χ) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro ψ χ hψ hχ
    have hψ' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm ψ e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hψ
    have hχ' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm χ e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hχ
    show (ψ * χ) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1
    rw [← AlgHom.liftEquiv_symm_apply, vendored_mul_eq_convMul,
      liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hψ' hχ'
  induction N generalizing φ with
  | zero =>
    rw [pow_zero, pow_one] at hord
    exact hord
  | succ N ih =>
    -- the cube is again connected and inertia-fixed, with order `3 ^ N`
    have hp3 : φ ^ 3 = φ * φ * φ := by rw [pow_succ, pow_succ, pow_one]
    have h3conn : (φ ^ 3) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
      rw [hp3]
      exact hmulconn _ _ (hmulconn _ _ hφe hφe) hφe
    have h3fix : ∀ σ ∈ localInertiaGroup 𝔭₃, σ • (φ ^ 3) = φ ^ 3 := by
      intro σ hσ
      rw [smul_pow', hfix σ hσ]
    have h3ord : (φ ^ 3) ^ (3 ^ N) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hord
    have hcube : φ ^ 3 = 1 := ih _ h3conn h3ord h3fix
    rw [hp3] at hcube
    exact inertiaFixed_connected_point_eq_one_at_three G e₀ he₀ hε₀ hprim₀
      hcomul₀ φ hφe hcube hfix

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **An inertia-fixed vector of the connected part vanishes, at ANY
congruence level** (PROVEN 2026-07-26 — the module-level reading of
`inertiaFixed_connected_point_eq_one_at_three_of_threePow` through a
Hopf package, and the exact analogue of the residual clause (ii) of
`exists_connectedEtale_subgroup_of_hopf_package`, which is available
only for a `3`-torsion coefficient FIELD): if the geometric points of
the generic fibre of a finite flat Hopf order `G` over `𝒪ᵥ ≅ ℤ₃` are
`Γ ℚ₃ᵥ`-equivariantly identified with the space of `ρ'` by `fG`, then a
vector `m` killed by `3 ^ N`, whose point is CONNECTED (value `1` on the
counit idempotent `e₀`) and which is fixed by the whole local inertia at
`3`, is `0`.

Proof: `fG` is additive, so `fG⁻¹` carries `3 ^ N • m = 0` to
`φ ^ (3 ^ N) = 1` for the point `φ` of `m` (`toMul_nsmul`), and carries
inertia-fixedness of `m` to inertia-fixedness of `φ`; the point is then
the convolution unit by the theorem above, and `m = fG 0 = 0`. -/
theorem inertiaFixed_connected_vector_eq_zero_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ' : GaloisRep ℚ A M)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G] [Module.Finite 𝒪₃ᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (N : ℕ) (m : M)
    (hm3 : (3 ^ N : ℕ) • m = 0)
    (hmconn : (Additive.toMul ((Equiv.ofBijective fG hfG).symm m))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1)
    (hmfix : ∀ σ ∈ localInertiaGroup 𝔭₃, (ρ'.toLocal 𝔭₃) σ m = m) :
    m = 0 := by
  classical
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : M, fG (g.symm x) = x :=
    fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : M,
      g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : M) = 0 := by
    apply g.injective
    show fG (g.symm (0 : M)) = fG 0
    rw [map_zero fG, hfs]
  have hgs_nsmul : ∀ (j : ℕ) (x : M),
      g.symm (j • x) = j • g.symm x := by
    intro j x
    induction j with
    | zero => rw [zero_nsmul, zero_nsmul, hgs_zero]
    | succ j ih => rw [succ_nsmul, succ_nsmul, hgs_add, ih]
  -- the point of `m` is killed by `3 ^ N` in the convolution group
  have hord : (Additive.toMul (g.symm m)) ^ (3 ^ N : ℕ) = 1 := by
    have h0 : (3 ^ N : ℕ) • g.symm m = 0 := by
      rw [← hgs_nsmul, hm3, hgs_zero]
    have h1 := congrArg Additive.toMul h0
    rwa [toMul_nsmul, toMul_zero] at h1
  -- and it is inertia-fixed
  have hfixφ : ∀ σ ∈ localInertiaGroup 𝔭₃,
      σ • Additive.toMul (g.symm m) = Additive.toMul (g.symm m) := by
    intro σ hσ
    have h1 : σ • g.symm m = g.symm m := by
      apply g.injective
      show fG (σ • g.symm m) = fG (g.symm m)
      rw [map_smul fG, hfs]
      show (ρ'.toLocal 𝔭₃) σ m = m
      exact hmfix σ hσ
    have h2 : Additive.toMul (σ • g.symm m) =
        σ • Additive.toMul (g.symm m) := rfl
    rw [← h2, h1]
  have hone := inertiaFixed_connected_point_eq_one_at_three_of_threePow G e₀ he₀
    hε₀ hprim₀ hcomul₀ N (Additive.toMul (g.symm m)) hmconn hord hfixφ
  have hX : g.symm m = 0 := by
    have h1 : Additive.toMul (g.symm m) =
        Additive.toMul (0 : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) := by
      rw [toMul_zero]
      exact hone
    exact Additive.toMul.injective h1
  have h2 := congrArg g hX
  rwa [g.apply_symm_apply, show g 0 = fG 0 from rfl, map_zero fG] at h2

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected–étale inertia subgroup of a Hopf package at `3`, at a
congruence level** (PROVEN 2026-07-26 — the exact analogue of ModThree's
`exists_connectedEtale_subgroup_of_hopf_package` with the `3`-torsion
coefficient FIELD replaced by any coefficient module killed by a POWER of
`3`, which is what every congruence level `𝔪ⁿ⁺²` is): the space carries
an additive subgroup `U` — the vectors whose point is connected — such
that (i) every inertia displacement lies in `U`, and (ii) `U` contains no
nonzero inertia-fixed vector.

Two things change relative to the residual statement and both are handled
here: negation, which the residual proof gets from `-u = u + u` in
characteristic `3`, is instead `-u = (3 ^ N − 1) • u`; and clause (ii)
needs the `3`-power-torsion Raynaud leaf above rather than its order-`3`
form.

`hconn` is (i) verbatim, supplied upstream by
`inertia_displacement_apply_connected_idempotent_eq_one`; the content
here is that the connected locus is a SUBGROUP and that (ii) survives to
all congruence levels. -/
theorem exists_connectedEtale_subgroup_at_three_of_threePowTorsion
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ' : GaloisRep ℚ A M)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G] [Module.Finite 𝒪₃ᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (N : ℕ) (hNtors : ∀ m : M, (3 ^ N : ℕ) • m = 0)
    (hconn : ∀ σ ∈ localInertiaGroup 𝔭₃, ∀ m : M,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((ρ'.toLocal 𝔭₃) σ m - m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ U : AddSubgroup M,
      (∀ σ ∈ localInertiaGroup 𝔭₃, ∀ m : M,
        (ρ'.toLocal 𝔭₃) σ m - m ∈ U) ∧
      (∀ u ∈ U, (∀ σ ∈ localInertiaGroup 𝔭₃,
        (ρ'.toLocal 𝔭₃) σ u = u) → u = 0) := by
  classical
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : M, fG (g.symm x) = x :=
    fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : M,
      g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : M) = 0 := by
    apply g.injective
    show fG (g.symm (0 : M)) = fG 0
    rw [map_zero fG, hfs]
  -- the connected locus contains `0`
  have hPzero : (Additive.toMul (g.symm (0 : M)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- and is closed under addition
  have hPadd : ∀ x y : M,
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm y)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- hence under natural multiples, and so under negation (`3 ^ N` kills)
  have hPnsmul : ∀ (j : ℕ) (x : M),
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (j • x))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro j x hx
    induction j with
    | zero => rw [zero_nsmul]; exact hPzero
    | succ j ih => rw [succ_nsmul]; exact hPadd _ _ ih hx
  have hPneg : ∀ x : M,
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (-x))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x hx
    have hneg : -x = (3 ^ N - 1 : ℕ) • x := by
      have h1 : (3 ^ N - 1 : ℕ) • x + x = 0 := by
        have h2 : (3 ^ N - 1 : ℕ) • x + (1 : ℕ) • x = ((3 ^ N - 1) + 1 : ℕ) • x :=
          (add_nsmul x _ _).symm
        rw [one_nsmul] at h2
        rw [h2, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
        exact hNtors x
      exact neg_eq_of_add_eq_zero_left h1
    rw [hneg]
    exact hPnsmul _ _ hx
  refine ⟨{
      carrier := {u : M |
        (Additive.toMul (g.symm u)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1}
      zero_mem' := hPzero
      add_mem' := fun hx hy => hPadd _ _ hx hy
      neg_mem' := fun hx => hPneg _ hx }, hconn, ?_⟩
  intro u hu hufix
  exact inertiaFixed_connected_vector_eq_zero_of_hopf_package ρ' G e₀ he₀ hε₀
    hprim₀ hcomul₀ fG hfG N u (hNtors u) hu hufix

/-- **`1` is the only cube root of unity in `ℤ_[3]`** (helper, proven).

`y³ = 1` gives `(y-1)((y-1)² + 3(y-1) + 3) = 0`; if `y ≠ 1` the second
factor vanishes, and reducing it mod `3` (`PadicInt.toZMod`) gives
`(y-1)‾² = 0`, so `y - 1 ∈ 𝔪 = (3)`, say `y - 1 = 3s`. Substituting,
`3 · (3s² + 3s + 1) = 0`, and `ℤ_[3]` is a domain with `3 ≠ 0`, so
`3s² + 3s + 1 = 0` — which reduces mod `3` to `1 = 0`.

Stated for a general prime `p` with a hypothesis `p = 3` so that it can be
applied at `primesEquiv v` without any `Fact`-instance cast. -/
theorem padicInt_eq_one_of_pow_three {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    (y : ℤ_[p]) (hy : y ^ 3 = 1) : y = 1 := by
  subst hp3
  by_contra hne
  have ht : y - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hfac : (y - 1) * ((y - 1) ^ 2 + 3 * (y - 1) + 3) = 0 := by
    linear_combination hy
  have hq : (y - 1) ^ 2 + 3 * (y - 1) + 3 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left ht
  have hcast : ((3 : ℕ) : ℤ_[3]) = (3 : ℤ_[3]) := by norm_cast
  have h3 : (PadicInt.toZMod (p := 3)) 3 = 0 := by
    rw [← hcast, map_natCast, ZMod.natCast_self]
  have h1 : (PadicInt.toZMod (p := 3) (y - 1)) ^ 2 = 0 := by
    have h := congrArg (PadicInt.toZMod (p := 3)) hq
    simp only [map_add, map_mul, map_pow, map_zero, h3, zero_mul, add_zero] at h
    exact h
  have h2 : PadicInt.toZMod (p := 3) (y - 1) = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp h1
  have hmem : y - 1 ∈ Ideal.span {((3 : ℕ) : ℤ_[3])} := by
    rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact h2
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [hcast] at hs
  have hy1 : y - 1 = 3 * s := by rw [← hs]; ring
  rw [hy1] at hq
  have hkey : (3 : ℤ_[3]) * (3 * s ^ 2 + 3 * s + 1) = 0 := by linear_combination hq
  have h3ne : (3 : ℤ_[3]) ≠ 0 := by norm_num
  have hkey2 : 3 * s ^ 2 + 3 * s + 1 = 0 := (mul_eq_zero.mp hkey).resolve_left h3ne
  have hcontra := congrArg (PadicInt.toZMod (p := 3)) hkey2
  simp only [map_add, map_mul, map_pow, map_one, map_zero, h3, zero_mul] at hcontra
  exact one_ne_zero hcontra

/-- **`1` is the only cube root of unity in `ℚ_[3]`** (helper, proven):
`‖x‖³ = 1` forces `‖x‖ = 1`, so `x` lies in `ℤ_[3]`, where
`padicInt_eq_one_of_pow_three` applies. -/
theorem padic_eq_one_of_pow_three {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    (x : ℚ_[p]) (hx : x ^ 3 = 1) : x = 1 := by
  have hnorm : ‖x‖ = 1 := by
    have h : ‖x‖ ^ 3 = 1 := by rw [← norm_pow, hx, norm_one]
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1)]
  obtain ⟨y, hy⟩ : ∃ y : ℤ_[p], (y : ℚ_[p]) = x := ⟨⟨x, le_of_eq hnorm⟩, rfl⟩
  have hy3 : y ^ 3 = 1 := by
    apply PadicInt.ext
    rw [PadicInt.coe_pow, PadicInt.coe_one, hy]
    exact hx
  rw [← hy, padicInt_eq_one_of_pow_three hp3 y hy3, PadicInt.coe_one]

/-- **`ζ₃ ∉ ℚ₃ᵥ`** (helper, proven): the completion of `ℚ` at the place
of `3` contains no primitive cube root of unity — equivalently, its only
cube root of unity is `1`.

Route: mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`
identifies `ℚ₃ᵥ` with `ℚ_[primesEquiv 𝔭₃]`, and
`natGenerator_toHeightOneSpectrum` says `primesEquiv 𝔭₃ = 3`; the
`Fact`-instance mismatch that this normally provokes is avoided by
stating `padic_eq_one_of_pow_three` over a general `p` with `p = 3` as a
hypothesis, so the two `Padic` instances never have to be identified. -/
theorem adicCompletionThree_eq_one_of_pow_three (q : ℚ₃ᵥ) (hq : q ^ 3 = 1) :
    q = 1 := by
  haveI hfp : Fact ((Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).2⟩
  have hp3 : ((Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) : ℕ) = 3 := by
    show Rat.HeightOneSpectrum.natGenerator _ = 3
    exact natGenerator_toHeightOneSpectrum Nat.prime_three
  let E := Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat
  have h1 : (E q) ^ 3 = 1 := by rw [← map_pow, hq, map_one]
  have h2 : E q = 1 := padic_eq_one_of_pow_three hp3 _ h1
  have h4 : E.symm (E q) = E.symm 1 := by rw [h2]
  rwa [ContinuousAlgEquiv.symm_apply_apply, map_one] at h4

/-- **Triviality of `ω` at `σ` means `σ` fixes the cube roots of unity**
(helper, proven): the defining specification of
`modularCyclotomicCharacter` reads `σ ζ = ζ ^ (ω σ).val`, and `ω σ = 1`
has `val = 1`. (This is the step that
`exists_cyclotomicCharacterModL_three_ne_one` above performs inline; it is
factored out here because the LOCAL statement below needs it at the
element `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g`.) -/
theorem fix_primitiveRoot_of_cyclotomicCharacterModL_three_eq_one
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3)
    (σ : Γ ℚ) (hσ : cyclotomicCharacterModL 3 σ = 1) : σ ζ = ζ := by
  have h2 := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
    (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
      (AlgebraicClosure ℚ) σ) hζ.toRootsOfUnity.2
  rw [show modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) σ) = cyclotomicCharacterModL 3 σ from rfl,
    hσ] at h2
  have hcoe : ((hζ.toRootsOfUnity : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) = ζ := by
    simp [IsPrimitiveRoot.toRootsOfUnity]
  have hval : (((1 : (ZMod 3)ˣ) : ZMod 3)).val = 1 := rfl
  rw [hval, pow_one, hcoe] at h2
  exact h2

/-- **The mod-3 cyclotomic character is nontrivial on the decomposition
group at `3`** (PROVEN 2026-07-26; cut 2026-07-26 while repairing the
connected–étale cut below; see the FAITHFULNESS REPAIR note there).

`ω = cyclotomicCharacterModL 3` cuts out `ℚ(ζ₃) = ℚ(√-3)`, in which the
prime `3` RAMIFIES; equivalently `ζ₃ ∉ ℚ₃`, because `ℚ₃(ζ₃)/ℚ₃` is
(totally, tamely) ramified of degree `φ(3) = 2`. So the restriction of
`ω` to the decomposition group at `3` — indeed already to the inertia
group at `3` — is nontrivial.

This is the ONLY thing the two consumers of the connected–étale leaf
below — `omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale`
and `invariant_functional_defect_vanishes_of_hopf_package` — need that a
purely local-at-`3` connected–étale statement cannot give them: each
must evaluate the diagonal entry of the connected line at some `g₀`
with `ω g₀ ≠ 1`, and after the repair `g₀` has to come from `Γ ℚ₃ᵥ`
rather than from `Γ ℚ` (`exists_cyclotomicCharacterModL_three_ne_one`,
which is proven above but produces a GLOBAL element).

Proof, in the shape of `exists_cyclotomicCharacterModL_three_ne_one`
but over `ℚ₃ᵥ`: if `ω` were trivial on the image of `Γ ℚ₃ᵥ` then a
primitive cube root of unity `ζ ∈ ℚᵃˡᵍ` would be fixed by every
`Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g`
(`fix_primitiveRoot_of_cyclotomicCharacterModL_three_eq_one`), hence — by
`Field.absoluteGaloisGroup.lift_map`, which says
`AlgebraicClosure.map f ∘ map f g = g ∘ AlgebraicClosure.map f` — its image
`ζ' := AlgebraicClosure.map (algebraMap ℚ ℚ₃ᵥ) ζ` would be fixed by the
WHOLE of `Γ ℚ₃ᵥ`, so `ζ' ∈ ℚ₃ᵥ` by infinite Galois theory
(`InfiniteGalois.mem_bot_iff_fixed`). But `ℚ₃ᵥ` has no primitive cube root
of unity (`adicCompletionThree_eq_one_of_pow_three` above: a `q ∈ ℤ₃` with
`q³ = 1` reduces to a cube root of `1` in `𝔽₃`, i.e. to `1`, so `q = 1 + 3a`
and `q³ - 1 = 9a(1 + 3a + 3a²) = 0` forces `a = 0` since `1 + 3a + 3a²` is a
unit), and `ζ' ≠ 1` because `AlgebraicClosure.map` is injective. -/
theorem exists_local_cyclotomicCharacterModL_three_ne_one :
    ∃ g : Γ ℚ₃ᵥ,
      cyclotomicCharacterModL 3
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g) ≠ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3
  -- every element of the decomposition group at `3` fixes the image of `ζ`
  have hfix : ∀ g : Γ ℚ₃ᵥ,
      g (AlgebraicClosure.map (algebraMap ℚ ℚ₃ᵥ) ζ) =
        AlgebraicClosure.map (algebraMap ℚ ℚ₃ᵥ) ζ := by
    intro g
    have h1 := fix_primitiveRoot_of_cyclotomicCharacterModL_three_eq_one hζ
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g) (hall g)
    have h2 := Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ₃ᵥ) g ζ
    rw [h1] at h2
    exact h2.symm
  -- hence it lies in `ℚ₃ᵥ` itself
  haveI : Algebra.IsIntegral ℚ₃ᵥ (AlgebraicClosure ℚ₃ᵥ) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsGalois ℚ₃ᵥ (AlgebraicClosure ℚ₃ᵥ) := ⟨⟩
  obtain ⟨q, hq⟩ := Set.mem_range.mp <| IntermediateField.mem_bot.mp <|
    (InfiniteGalois.mem_bot_iff_fixed
      (AlgebraicClosure.map (algebraMap ℚ ℚ₃ᵥ) ζ)).mpr hfix
  have hq3 : q ^ 3 = 1 := by
    have h3 : algebraMap ℚ₃ᵥ (AlgebraicClosure ℚ₃ᵥ) (q ^ 3) = 1 := by
      rw [map_pow, hq, ← map_pow, hζ.pow_eq_one, map_one]
    exact (algebraMap ℚ₃ᵥ (AlgebraicClosure ℚ₃ᵥ)).injective (by rw [h3, map_one])
  have hqne : q ≠ 1 := by
    intro h1
    apply hζ.ne_one (by norm_num)
    apply (AlgebraicClosure.map (algebraMap ℚ ℚ₃ᵥ)).injective
    rw [map_one, ← hq, h1, map_one]
  -- but `ℚ₃ᵥ` has no primitive cube root of unity
  exact hqne (adicCompletionThree_eq_one_of_pow_three q hq3)

/-- **The mod-3 cyclotomic character is RAMIFIED at `3`** (PROVEN
2026-07-26): some element of the LOCAL INERTIA group at `3` is off the
kernel of `ω`. This is the inertia-level strengthening of
`exists_local_cyclotomicCharacterModL_three_ne_one` just above, which
only produces an element of the DECOMPOSITION group; the Raynaud steps
(3) and (4) below both need the inertia form, because an unramified
twist is invisible to inertia and a decomposition-group witness would
therefore carry no information about the connected part.

Mathematically this is `ℚ₃(ζ₃)/ℚ₃` being (totally, tamely) ramified of
degree `φ(3) = 2` — equivalently `ζ₃ ∉ ℚ₃ⁿʳ`, in contrast to
`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup` below, which
says `ω` is UNRAMIFIED at every `p ≠ 3`.

Route: the witness is ModThree's PROVEN
`exists_localInertia_three_not_fix_primitiveRoot` (an inertia element at
`3` fixing no primitive cube root of unity, assembled there from the
finite-level leaf `exists_finite_level_inertia_swap_three` by the
compactness lifting `exists_mem_localInertiaGroup_restrictNormalHom_eq`);
`fix_primitiveRoot_of_cyclotomicCharacterModL_three_eq_one` above turns
`ω σ = 1` into `σ ζ = ζ`, which that witness forbids.

INSTANCE NOTE. `ModThree` spells the structure map `ℚ → ℚ₃ᵥ` through
`DivisionRing.toRatAlgebra` while this file — which boosts
`instAlgebraAdicCompletion` to priority `2000` at the top of the
namespace — spells it through `instAlgebraAdicCompletion`. The two
`Algebra ℚ ℚ₃ᵥ` structures are EQUAL but not syntactically so
(`Subsingleton (Algebra ℚ _)`, i.e. `algebraRat.subsingleton`), so the
bridge is an explicit `Subsingleton.elim` rewrite — the same idiom as
`Interface.lean`'s `hinst`. -/
theorem exists_localInertia_cyclotomicCharacterModL_three_ne_one :
    ∃ σ ∈ localInertiaGroup 𝔭₃,
      cyclotomicCharacterModL 3
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) ≠ 1 := by
  obtain ⟨σ, hσ, hmove⟩ := exists_localInertia_three_not_fix_primitiveRoot
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3
  have hinst : (DivisionRing.toRatAlgebra : Algebra ℚ ℚ₃ᵥ) =
      IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ 𝔭₃ :=
    Subsingleton.elim _ _
  refine ⟨σ, hσ, fun h => hmove ζ hζ ?_⟩
  rw [hinst]
  exact fix_primitiveRoot_of_cyclotomicCharacterModL_three_eq_one hζ _ h

/-- **The `J`-adic filtration vanishes in the congruence quotient**
(helper, proven): an element of `J • V` has vanishing image
`1 ⊗ z` in `(R ⧸ J) ⊗[R] V`. This is the congruence-level analogue of
`one_tmul_eq_zero_of_mem_maximalIdeal_smul_top` above (which is the
RESIDUAL case `J = 𝔪`, over the residue FIELD); the Raynaud assembly
below needs it at `J = 𝔪ⁿ⁺²`, where the coefficient ring is the
artinian quotient `R ⧸ 𝔪ⁿ⁺²` rather than a field. -/
theorem one_tmul_quotient_eq_zero_of_mem_smul_top {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] (J : Ideal R)
    {z : V} (hz : z ∈ J • (⊤ : Submodule R V)) :
    (1 : R ⧸ J) ⊗ₜ[R] z = 0 := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) fun y w hy hw => ?_
  · rw [one_tmul_smul, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  · rw [TensorProduct.tmul_add, hy, hw, add_zero]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The geometric points of the generic fibre are FINITE** (PROVEN
2026-07-27, one instance step): `Module.Finite 𝒪ᵥ G` base-changes to
`Module.Finite ℚ₃ᵥ (ℚ₃ᵥ ⊗ G)`, `Module.Free` is automatic over the
field `ℚ₃ᵥ`, and mathlib's `Module.Finite.algHom` then makes the set of
`ℚ₃ᵥ`-points valued in the domain `ℚ₃ᵥᵃˡᵍ` finite.

This is stated as its own declaration ONLY for a performance reason,
and the reason is worth recording. Every neighbouring declaration in
this file runs under `backward.isDefEq.respectTransparency false`, and
under that option this instance search does not terminate inside the
heartbeat budget — it was measured to exhaust 2·10⁶ heartbeats twice,
once at `whnf` and once at `isDefEq`, while the same search costs
almost nothing at default transparency. Isolating it here lets the
consumers keep the option they need for their own `show`/`rw` steps. -/
theorem finite_points_of_hopf_order
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)] :
    Finite (Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) :=
  inferInstanceAs (Finite (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ))

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Every vector of a Hopf package has POSITIVE FINITE additive
order** (PROVEN 2026-07-27): the geometric point set is finite by
`finite_points_of_hopf_order` above, `fG` transports finiteness across
the bijection to the space, and `addOrderOf` of an element of a finite
`AddCommGroup` is positive and kills it.

Note the order is taken in `N`, NOT in the point group: the points
form only a MONOID under convolution as far as the instance graph is
concerned (no `AddLeftCancelMonoid (Additive …)` instance exists), so
`addOrderOf_pos` is unavailable there, while `N` is an `AddCommGroup`
and supplies it immediately. Transporting finiteness rather than the
order statement is what makes this one line. -/
theorem exists_pos_nsmul_eq_zero_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG) (z : N) :
    ∃ n : ℕ, 0 < n ∧ (n : ℕ) • z = 0 := by
  haveI : Finite (Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) := finite_points_of_hopf_order G
  haveI : Finite N := Finite.of_equiv _ (Equiv.ofBijective fG hfG)
  exact ⟨addOrderOf z, addOrderOf_pos z, addOrderOf_nsmul_eq_zero z⟩

/-- **NAKAYAMA IN THE CONVOLUTION FILTRATION, PRIME-TO-`p` FORM**
(PROVEN 2026-07-27): if a point `c` of the convolution ring
`WithConv (G →ₗ[R] A)` over a LOCAL ring `A` satisfies `c ^ m = 1` for
an `m` that is a UNIT of `A`, and its displacement `c − 1` takes its
values in the maximal ideal, then `c = 1`.

This is the exact prime-to-`p` mirror of
`OortTate.eq_convOne_of_convPow_prime_eq_one`, and the comparison is
the point of the statement. That lemma does the `p`-part: it must
fight the fact that `p` is a NONUNIT, which costs it the hypotheses
`IsDomain A`, `Odd p`, `(p : A) ≠ 0` and the value condition
`c − 1 ∈ (p)` — the absolute unramifiedness `e = 1` — and it spends
Raynaud's bound `𝔞 ^ p ≤ (p)·𝔞²` to cancel `p` in the domain. Here `m`
is invertible, so ALL of that disappears: no domain hypothesis, no
primality, no oddness, and NO RAMIFICATION INPUT WHATEVER.

PROOF. Write `d := c − 1` and `𝔞 := span (range d.ofConv)`. The
first-order expansion `OortTate.exists_convPow_rem` gives
`c ^ m = 1 + m·d + r` with `r` valued in `𝔞²`; against `c ^ m = 1` this
is `m·d + r = 0`, so every value `m · d(x)` lies in `𝔞²`. Multiplying
by `m⁻¹` — legitimate exactly because `m` is a unit, and this is the
one step the `p`-part cannot take — puts `d(x)` itself in `𝔞²`, i.e.
`𝔞 ≤ 𝔞·𝔞`. Since `𝔞` is finitely generated (`OortTate.fg_span_range`,
which is where `Module.Finite R G` is spent) and contained in the
maximal ideal, hence in the Jacobson radical of the local ring `A`,
Nakayama (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) gives
`𝔞 = ⊥`, so `d = 0` and `c = 1`. -/
theorem eq_convOne_of_convPow_natCast_isUnit
    {R G A : Type*} [CommRing R] [AddCommMonoid G] [Module R G] [Coalgebra R G]
    [CommRing A] [Algebra R A] [Module.Finite R G] [IsLocalRing A]
    {m : ℕ} (hm : IsUnit ((m : ℕ) : A))
    (c : WithConv (G →ₗ[R] A)) (hcm : c ^ m = 1)
    (hmax : ∀ x, (c - 1).ofConv x ∈ IsLocalRing.maximalIdeal A) :
    c = 1 := by
  classical
  have hd : ∀ x, (c - 1).ofConv x ∈ Ideal.span (Set.range (c - 1).ofConv) :=
    fun x => Ideal.subset_span ⟨x, rfl⟩
  obtain ⟨r, hr, hcmr⟩ := OortTate.exists_convPow_rem c hd m
  -- `c ^ m = 1` turns the first-order expansion into `m·d + r = 0`
  have hkey : (m : ℕ) • (c - 1) + r = 0 := by
    have h : (1 : WithConv (G →ₗ[R] A)) + ((m : ℕ) • (c - 1) + r) = 1 + 0 := by
      rw [add_zero, ← add_assoc]
      exact hcmr.symm.trans hcm
    exact add_left_cancel h
  -- so `m · d(x) ∈ 𝔞²`, and `m` cancels because it is a unit
  have hsq : ∀ x : G, (c - 1).ofConv x ∈ Ideal.span (Set.range (c - 1).ofConv) ^ 2 := by
    intro x
    have h0 : ((m : ℕ) • (c - 1)).ofConv x + r.ofConv x = 0 := by
      have h1 := congrArg (fun f : WithConv (G →ₗ[R] A) => f.ofConv x) hkey
      simpa only [WithConv.ofConv_add, WithConv.ofConv_zero, LinearMap.add_apply,
        LinearMap.zero_apply] using h1
    have h2 : ((m : ℕ) • (c - 1)).ofConv x = ((m : ℕ) : A) * (c - 1).ofConv x := by
      rw [WithConv.ofConv_smul, LinearMap.smul_apply, nsmul_eq_mul]
    have hmm : ((m : ℕ) : A) * (c - 1).ofConv x ∈
        Ideal.span (Set.range (c - 1).ofConv) ^ 2 := by
      rw [← h2, eq_neg_of_add_eq_zero_left h0]
      exact Submodule.neg_mem _ (hr x)
    obtain ⟨u, hu⟩ := hm
    have h3 : (c - 1).ofConv x = (↑u⁻¹ : A) * (((m : ℕ) : A) * (c - 1).ofConv x) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h3]
    exact Ideal.mul_mem_left _ _ hmm
  -- Nakayama
  have hle : Ideal.span (Set.range (c - 1).ofConv) ≤
      Ideal.span (Set.range (c - 1).ofConv) • Ideal.span (Set.range (c - 1).ofConv) := by
    rw [Ideal.smul_eq_mul, ← sq, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    exact hsq x
  have hjac : Ideal.span (Set.range (c - 1).ofConv) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmax x
  have hbot : Ideal.span (Set.range (c - 1).ofConv) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ (OortTate.fg_span_range _) hle hjac
  have hzero : c - 1 = 0 := by
    apply WithConv.ofConv_injective
    ext x
    have hx := hd x
    rw [hbot, Ideal.mem_bot] at hx
    simpa using hx
  exact sub_eq_zero.mp hzero

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **A CONNECTED point of order PRIME TO `3` is the identity** (PROVEN
2026-07-27): a geometric point `φ` of the generic fibre of a
module-finite Hopf order `G` over `𝒪ᵥ ≅ ℤ₃`, taking the value `1` on a
PRIMITIVE counit-one idempotent `e₀`, and satisfying `φ ^ m = 1` for
some `m` not divisible by `3`, is the convolution unit.

This is the point-level statement behind
`connected_vector_threePow_torsion_of_hopf_package` below, and the
prime-to-`3` mirror of the proven
`OortTate.eq_one_of_inertia_invariant_of_reduction_counit`. Note what
is ABSENT relative to that lemma: there is no inertia hypothesis, no
`Odd p`, and no use of `e = 1`. The whole ramification content of the
`p`-part is replaced here by the single observation that `m` is a UNIT
of the integral closure.

PROOF, in three moves, all of them transcriptions of existing proven
material.

1. CONNECTEDNESS is spent exactly once:
   `OortTate.point_sub_counit_mem_maximalIdeal` (which consumes `he₀`,
   `hε₀`, `hprim₀` and `hφe`) says the point reduces to the counit, so
   the displacement `c − 1` of the corresponding element `c` of the
   convolution ring over `𝒪̄` takes its values in `𝔪 𝒪̄`.
2. `m` IS A UNIT of `𝒪̄`: were it a nonunit it would lie in `𝔪 𝒪̄`, and
   `OortTate.dvd_of_natCast_mem_maximalIdeal` (Bézout against `3`,
   over `OortTate.natCast_mem_maximalIdeal_integralClosure`) would give
   `3 ∣ m`, contradicting `hm3`.
3. `φ ^ m = 1` is transported to `c ^ m = 1` through
   `OortTate.liftEquiv_symm_vendored_pow`, `OortTate.comp_convPow` and
   `AlgHom.toLinearMap_convPow` — the same plumbing as in
   `OortTate.eq_one_of_inertia_invariant_of_reduction_counit` — and
   `eq_convOne_of_convPow_natCast_isUnit` above finishes.

FAITHFULNESS. `hprim₀` is essential and is spent in move 1: without it
`e₀ = 1` is admissible, the "connected locus" is everything, and the
constant group scheme `ℤ/5` over `𝒪ᵥ` refutes the statement with
`m = 5`. -/
theorem connected_point_eq_one_of_pow_coprime_three
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G] [Module.Finite 𝒪₃ᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1)
    {m : ℕ} (hm3 : ¬ (3 ∣ m)) (hord : φ ^ m = 1) :
    φ = 1 := by
  classical
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Algebra.IsIntegral 𝒪₃ᵥ G := Algebra.IsIntegral.of_finite 𝒪₃ᵥ G
  -- STEP 1: connectedness — the point reduces to the counit
  have hred : ∀ g : G, φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] g) -
      algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) g) ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) ℚ₃ᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ)) := fun g =>
    OortTate.point_sub_counit_mem_maximalIdeal 𝔭₃ G e₀ he₀ hε₀ hprim₀ φ hφe g
  -- the point, read inside the integral closure
  set χ : G →ₐ[𝒪₃ᵥ] ℚ₃ᵥᵃˡᵍ := (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm φ
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪₃ᵥ) a).map χ
  set χI : G →ₐ[𝒪₃ᵥ] IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ :=
    AlgHom.codRestrict χ (integralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) hint
  set ι : IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ →ₐ[𝒪₃ᵥ] ℚ₃ᵥᵃˡᵍ :=
    { algebraMap (IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) ℚ₃ᵥᵃˡᵍ with
      commutes' := fun _ => rfl }
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext h
  have hιχ : ι.comp χI = χ := AlgHom.ext fun _ => rfl
  set c : WithConv (G →ₗ[𝒪₃ᵥ] IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) :=
    WithConv.toConv χI.toLinearMap with hc
  have hdval : ∀ g : G, ι ((c - 1).ofConv g) =
      φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] g) -
        algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) g) := by
    intro g
    rw [WithConv.ofConv_sub, LinearMap.sub_apply, map_sub]
    congr 1
  have hmax : ∀ g : G, (c - 1).ofConv g ∈
      IsLocalRing.maximalIdeal (IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hred g
    have hgm : ι ((c - 1).ofConv g) = ι y := by rw [hdval g, ← hyeq]; rfl
    rwa [hιinj hgm]
  -- STEP 2: `m` is a unit of `𝒪̄`
  have hunit : IsUnit ((m : ℕ) : IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) := by
    by_contra hnu
    exact hm3 (OortTate.dvd_of_natCast_mem_maximalIdeal (p := 3) m
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)))
  -- STEP 3: `φ ^ m = 1`, transported to the convolution ring over `𝒪̄`
  have hχp : (WithConv.toConv χ) ^ m = (1 : WithConv (G →ₐ[𝒪₃ᵥ] ℚ₃ᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    have h := OortTate.liftEquiv_symm_vendored_pow (R := 𝒪₃ᵥ) (S := ℚ₃ᵥ) (H := G)
      (L := ℚ₃ᵥᵃˡᵍ) φ m
    rw [hord, vendored_one_eq_convOne, liftEquiv_symm_convOne] at h
    exact h.symm
  have hχIp : (WithConv.toConv χI) ^ m =
      (1 : WithConv (G →ₐ[𝒪₃ᵥ] IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun a => hιinj ?_
    have h := OortTate.comp_convPow ι (WithConv.toConv χI) m
    rw [WithConv.ofConv_toConv, hιχ, hχp] at h
    have h2 := congrArg (fun f : G →ₐ[𝒪₃ᵥ] ℚ₃ᵥᵃˡᵍ => f a) h
    simpa [OortTate.comp_convOne ι] using h2
  have hcp : c ^ m = 1 := by
    have h := AlgHom.toLinearMap_convPow (WithConv.toConv χI) m
    rw [hχIp, AlgHom.toLinearMap_convOne] at h
    exact h.symm
  have hc1 : c = 1 := eq_convOne_of_convPow_natCast_isUnit hunit c hcp hmax
  -- and back to `φ`
  apply (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm.injective
  rw [vendored_one_eq_convOne, liftEquiv_symm_convOne]
  refine AlgHom.ext fun a => ?_
  have h : χI a = (1 : WithConv (G →ₗ[𝒪₃ᵥ] IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ)).ofConv a := by
    have h0 := congrArg (fun f : WithConv (G →ₗ[𝒪₃ᵥ] IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ) =>
      f.ofConv a) hc1
    rw [hc] at h0
    exact h0
  calc ((AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm φ) a
      = ι (χI a) := rfl
    _ = ι (algebraMap 𝒪₃ᵥ (IntegralClosure 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ)
          (Coalgebra.counit (R := 𝒪₃ᵥ) a)) := by
        rw [h, LinearMap.convOne_apply]
    _ = algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) a) := ι.commutes _
    _ = (1 : WithConv (G →ₐ[𝒪₃ᵥ] ℚ₃ᵥᵃˡᵍ)).ofConv a := (AlgHom.convOne_apply a).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected part is `3`-PRIMARY** (PROVEN 2026-07-27; cut the
same day out of
`exists_localInertia_no_fixed_connected_vector_of_hopf_package`
below, which is PROVEN over it together with the tameness leaf
`exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
just after it).

Content: every CONNECTED vector — every `z` whose point takes the value
`1` at the connected counit idempotent `e₀` — is killed by SOME power of
`3`. Nothing about inertia, nothing about ramification: this is the
ORDER statement alone, and it is the half of the parent leaf that the
Raynaud classification does NOT supply.

WHY THE PARENT NEEDS IT, AND WHY IT IS NOT FREE. The proven
`inertiaFixed_connected_vector_eq_zero_of_hopf_package` above carries a
`3`-power-torsion hypothesis `hm3 : (3 ^ N) • m = 0`, and the parent
leaf carries none. The gap is exactly this statement. It is NOT
formal: `N` is finite (see below), so every vector has finite additive
order, but a priori that order may have a prime-to-`3` part, and a
nonzero connected vector of order coprime to `3` would refute the
parent leaf outright — every hypothesis of the parent is blind to it,
since `inertiaFixed_connected_vector_eq_zero_of_hopf_package` cannot
see it and the tameness leaf only constrains WHICH `σ` acts freely.

MATHEMATICAL CONTENT. `hprim₀` pins `e₀ G` as the connected component
of the identity of the finite flat `𝒪ᵥ`-group scheme `Spec G`
(`𝒪ᵥ ≅ ℤ₃` is henselian local, so connected components of `Spec G`
correspond to primitive idempotents of `G`, and `hε₀` picks the one
through the identity section). A CONNECTED finite flat group scheme
over a base of residue characteristic `3` has `3`-power order — its
special fibre is infinitesimal — so its geometric points form a
`3`-group. Equivalently, and this is the form to prove: a point of the
connected component reduces to the counit
(`OortTate.point_sub_counit_mem_maximalIdeal`, PROVEN, and it spends
exactly `he₀`/`hε₀`/`hprim₀`), i.e. lies in the KERNEL OF REDUCTION,
and the kernel of reduction has no nontrivial prime-to-`3` torsion.

THE ROUTE BELOW WAS FOLLOWED AS WRITTEN, and it is recorded here
unchanged because it is an accurate account of the proof. Three
declarations were added above to carry it:
`finite_points_of_hopf_order` and
`exists_pos_nsmul_eq_zero_of_hopf_package` (finiteness, hence a finite
additive order `n` for `z`), `eq_convOne_of_convPow_natCast_isUnit`
(the prime-to-`p` Nakayama, generic in `R`, `G`, `A`), and
`connected_point_eq_one_of_pow_coprime_three` (its point-level
instance at `3`). Only two adjustments to the sketch were needed. The
`3`-adic splitting `n = 3 ^ a · m` is taken from mathlib's
`Nat.exists_eq_pow_mul_and_not_dvd` rather than from `Nat.factorization`
(the `ord_proj`/`ord_compl` lemma names named below do not exist at
this pin). And the additive order is taken in `N`, not in the point
group: the points carry no `AddLeftCancelMonoid` instance, so
`addOrderOf_pos` is unavailable there — see
`exists_pos_nsmul_eq_zero_of_hopf_package`.

ROUTE FOR A PROVER — the prime-to-`3` half is ELEMENTARY, by Nakayama
in the convolution filtration, and the pieces are already in
`Fermat/FLT/GroupScheme/ConnectedEtale.lean`. Let `z` be connected of
finite additive order `n = 3 ^ a * m` with `gcd (m, 3) = 1`; the
connected locus is closed under `ℕ`-multiples
(`convMul_apply_one_of_comul_absorbs`, as re-performed in the parent's
glue below), so `w := (3 ^ a) • z` is connected of order dividing `m`.
Write `c := φ_w` in the convolution ring `WithConv (G →ₗ[𝒪ᵥ] 𝒪̄)` and
`d := c - 1`, `𝔞 := span (range d.ofConv)`. Then:

* `d` is valued in the maximal ideal of `𝒪̄`, by
  `OortTate.point_sub_counit_mem_maximalIdeal` — this is where
  connectedness is spent;
* `c ^ m = 1` expands binomially to `m • d = -∑_{i≥2} C(m,i) • d ^ i`,
  whose values lie in `𝔞 ^ 2` by `OortTate.convPow_apply_mem_pow`;
* `m` is a UNIT of `𝒪̄`: `3` lies in the maximal ideal
  (`OortTate.natCast_mem_maximalIdeal_integralClosure`) and
  `gcd (m, 3) = 1` gives `a * m + b * 3 = 1`, so `m ∈ 𝔪` would force
  `1 ∈ 𝔪`;
* hence `𝔞 ⊆ 𝔞 ^ 2 ⊆ 𝔞`, and `𝔞` is FINITELY GENERATED
  (`OortTate.fg_span_range`, which is where `Module.Finite 𝒪ᵥ G` is
  spent) and contained in the maximal ideal of the LOCAL ring `𝒪̄`, so
  Nakayama gives `𝔞 = 0`, i.e. `d = 0` and `w = 0`.

So `(3 ^ a) • z = 0` and `k := a` works. Note this is the exact
prime-to-`3` mirror of the PROVEN
`OortTate.eq_convOne_of_convPow_prime_eq_one`, which does the `p`-part
at `e = 1` and needs Raynaud's bound; the prime-to-`p` part needs no
ramification input at all, only that `m` is invertible. The
`AlgHom`-to-`WithConv` transport is the same plumbing as in
`OortTate.eq_one_of_inertia_invariant_of_reduction_counit`
(`AlgHom.liftEquiv`, `vendored_mul_eq_convMul`, `liftEquiv_symm_convMul`).

FINITENESS, which the route above assumes and which is genuinely
available: `Module.Finite 𝒪ᵥ G` base-changes to
`Module.Finite ℚ₃ᵥ (ℚ₃ᵥ ⊗ G)`, mathlib's instance `Finite (S →ₐ[R] K)`
then makes the geometric point set FINITE, and `fG` transports that to
the space. So `addOrderOf z` is positive and the decomposition
`n = 3 ^ a * m` is legitimate.

`hprim₀` IS ESSENTIAL — WITHOUT IT THE STATEMENT IS FALSE, and the
witness is the same one recorded on the parent: `e₀ = 1` satisfies
`he₀`, `hε₀` and `hcomul₀` and makes the "connected locus" all of `M`;
for the CONSTANT group scheme `G = ℤ/5` over `𝒪ᵥ` the points then form
a group of order `5`, killed by no power of `3`. Primitivity is what
pins `e₀ G` as the identity component and makes the leaf true. Do not
drop or underscore it.

FAITHFULNESS. The conclusion is a VALUE-level statement about a vector
(its additive order), with no quantifier over `Γ` at all, no element of
`G`, no coordinate and no normal form. So the leaf is on the true side
of the development's `𝒪ᵥ`-descent rule, and it is twist-blind: an
unramified twist `μ₃ ⊗ ψ` changes WHICH vectors are connected, not the
order of the connected group.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 1.1 and 3.3.2; Tate, *Finite flat group schemes*, §1 and §4, in
Cornell–Silverman–Stevens (connected–étale sequence over a henselian
base); Fontaine, *Il n'y a pas de variété abélienne sur `ℤ`*, §1. -/
theorem connected_vector_threePow_torsion_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (z : N)
    (hz : (Additive.toMul ((Equiv.ofBijective fG hfG).symm z))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ k : ℕ, (3 ^ k : ℕ) • z = 0 := by
  classical
  set g := Equiv.ofBijective fG hfG
  have hfs : ∀ x : N, fG (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
  have hgs_nsmul : ∀ (j : ℕ) (x : N), g.symm (j • x) = j • g.symm x := by
    intro j x
    induction j with
    | zero => rw [zero_nsmul, zero_nsmul, hgs_zero]
    | succ j ih => rw [succ_nsmul, succ_nsmul, hgs_add, ih]
  -- the connected locus contains `0` …
  have hPzero : (Additive.toMul (g.symm (0 : N)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- … is closed under addition (comultiplication absorption) …
  have hPadd : ∀ x y : N,
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm y)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- … hence under natural multiples
  have hPnsmul : ∀ (j : ℕ) (x : N),
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (j • x))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro j x hx
    induction j with
    | zero => rw [zero_nsmul]; exact hPzero
    | succ j ih => rw [succ_nsmul]; exact hPadd _ _ ih hx
  -- FINITENESS: `z` has a positive finite additive order `n`
  obtain ⟨n, hnpos, hnz⟩ := exists_pos_nsmul_eq_zero_of_hopf_package ρ' G fG hfG z
  -- split off the `3`-part: `n = 3 ^ a · m` with `m` prime to `3`
  obtain ⟨a, mm, hmm3, hnfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hnpos.ne' 3 (by norm_num)
  refine ⟨a, ?_⟩
  -- `w := 3 ^ a • z` is connected and killed by the prime-to-`3` part `m`
  have hwconn : (Additive.toMul (g.symm ((3 ^ a : ℕ) • z)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := hPnsmul _ _ hz
  have hw3 : (mm : ℕ) • ((3 ^ a : ℕ) • z) = 0 := by
    rw [smul_smul, mul_comm, ← hnfac]
    exact hnz
  -- so its point has order dividing `m`, hence is the convolution unit
  have hord : (Additive.toMul (g.symm ((3 ^ a : ℕ) • z))) ^ (mm : ℕ) = 1 := by
    have h0 : (mm : ℕ) • g.symm ((3 ^ a : ℕ) • z) = 0 := by
      rw [← hgs_nsmul, hw3, hgs_zero]
    have h1 := congrArg Additive.toMul h0
    rwa [toMul_nsmul, toMul_zero] at h1
  have hone := connected_point_eq_one_of_pow_coprime_three G e₀ he₀ hε₀ hprim₀
    _ hwconn hmm3 hord
  have hX : g.symm ((3 ^ a : ℕ) • z) = 0 := by
    refine Additive.toMul.injective ?_
    rw [toMul_zero]
    exact hone
  have h2 := congrArg g hX
  rwa [g.apply_symm_apply, show g 0 = fG 0 from rfl, map_zero fG] at h2

/-- **The TAME QUOTIENT is PROCYCLIC: every finite quotient of local
inertia that kills wild inertia is CYCLIC** (PROVEN 2026-07-27 over the
single leaf `exists_localInertia_generator_mod_pow_wildInertiaGroup` in
`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`; it
was cut 2026-07-27 out of
`exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
below, which is PROVEN over it together with the Raynaud tameness leaf
`wildInertia_fixes_connected_threeTorsion_of_hopf_package` just after
it).

Content, in the shape a consumer needs it: whenever local inertia at a
finite place `v` acts on a FINITE type `X` (the action given as a bare
family of maps `act` with `act 1 = id` and `act (a * b) = act a ∘ act
b`) and WILD inertia acts trivially, there is ONE `σ ∈ I_v` whose
action GENERATES: every `τ ∈ I_v` acts as an iterate of `act σ`.

This is pure local Galois theory: there is no Galois representation, no
group scheme, no Hopf package, nothing `3`-adic and nothing about the
number field `K` beyond `v` being a finite place. It is stated
generically in `K` and `v` and is reusable anywhere the development
needs "the tame quotient is procyclic" in usable form.

MATHEMATICAL CONTENT. `hwild` says the action factors through
`I_v / P_v`, the TAME quotient, and Serre, *Corps Locaux* IV §2 /
Neukirch II.7.11 identify that quotient with
`lim_{(n, ℓ) = 1} μ_n(k̄_v) ≅ ∏_{ℓ ≠ ℓ_v} ℤ_ℓ`, which is PROCYCLIC.
Since `X` is finite, the image of `I_v` in the permutation group of `X`
is a FINITE group, and a finite quotient of `∏_ℓ ℤ_ℓ` is cyclic; taking
`σ` above a generator of that image gives the conclusion, because in a
finite cyclic group every element is a non-negative power of a
generator and `act (σ ^ n) = (act σ)^[n]` by `hone`/`hmul`.

HOW IT IS PROVED HERE, AND WHERE THE ARITHMETIC WENT. Everything
formal is discharged in this file and the arithmetic sits in exactly one
place, hoisted out of this cluster to
`Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean`,
beside `wildInertiaGroup` itself where it is reusable:

* `exists_localInertia_generator_mod_pow_wildInertiaGroup` — **the one
  remaining SORRY LEAF**: for every `n ≠ 0` a single `σ ∈ I_v` with
  every `τ ∈ I_v` equal to `σ ^ k · ρ ^ n · w`, `ρ ∈ I_v`, `w ∈ P_v`.
  That is `Q / Qⁿ` cyclic for `Q := I_v / P_v`, the finite-layer form of
  procyclicity;
* `exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker` — PROVEN over
  it, by Lagrange: any homomorphism from `I_v` onto a FINITE group,
  killing `P_v`, has cyclic image generated by the image of one
  inertia element, with non-negative exponents.

The proof below is then pure packaging: the family `act` with `hone`
and `hmul` is exactly the data of a group homomorphism
`φ : I_v →* Equiv.Perm X` (each `act a` is a bijection with inverse
`act a⁻¹`), `X` finite makes `φ.range` finite, `hwild` says `P_v` is in
its kernel, and the corollary supplies `σ` with `φ τ = φ σ ^ k`; an
induction turns `φ σ ^ k` back into `(act σ)^[k]`.

ONE OBLIGATION NOBODY HAS: CONTINUITY. It is not needed anywhere on this
route, and chasing it is the obvious way to lose a day here, because
**every ABSTRACT finite quotient of `∏_ℓ ℤ_ℓ` is already cyclic**: such
a quotient `H` is abelian and killed by `n := |H|`, so the surjection
factors through
`(∏_ℓ ℤ_ℓ) / n · (∏_ℓ ℤ_ℓ) = ∏_ℓ (ℤ_ℓ / n ℤ_ℓ) = ∏_{ℓ ∣ n} ℤ / ℓ^{v_ℓ n}
≅ ℤ / n`, using that multiplication by `n` on a product is
coordinatewise and that `ℤ_ℓ` is uniquely `q`-divisible for `q ≠ ℓ`.
So `H` is a quotient of a cyclic group. No topology, no profinite
completion, no open-subgroup argument. This is why the corollary above
takes a bare `MonoidHom` into a bare `Finite` group, and it is what lets
a consumer hand over an action given as a raw family of maps.

What genuinely remains — inside that single leaf — is the
identification of the tame quotient itself, against
**`wildInertiaGroup`**, which is `localInertiaGroup v ⊓
tameFixingSubgroup v` with `tameFixingSubgroup` spelled through
GENERATORS (`σ` fixes every `x` integral over `𝒪ᵥ` with `x ^ n ∈ 𝒪ᵥ`
for `n` prime to the residue characteristic) precisely so that no theory
of the maximal tame extension is presupposed — see its docstring in
`Deformations/RepresentationTheory/ArtinConductor.lean`. The route is
Kummer theory over `Kᵥⁿʳ`: a finite quotient of `I_v` killing `P_v`
corresponds to a finite subextension of `Kᵥᵗᵃᵐᵉ / Kᵥⁿʳ`, which is
`Kᵥⁿʳ(π^{1/e})` for some `e` prime to the residue characteristic, with
Galois group `≅ μ_e(k̄_v)` — cyclic. `~/cs/FLT` was grepped for
tame-quotient material on 2026-07-27 and has none to vendor: its only
`tame` hits are `localTameAbelianInertiaGroup` (whose own docstring
calls it "somewhat cheating" and carries a `TODO: show that this is
indeed the right group`) and unrelated `PGL₂` files.

FAITHFULNESS. The conclusion quantifies over `localInertiaGroup v`
only, never over `Γ Kᵥ`, so it is on the true side of the
development's inertia-vs-`Γ` rule; widening `σ, τ` to the whole
decomposition group would make it FALSE, since the decomposition
quotient `I_v` extends by the (also procyclic) unramified quotient but
the extension need not be cyclic. The `Finite X` hypothesis is
ESSENTIAL and not cosmetic: `I_v / P_v` is procyclic but not cyclic, so
without finiteness of the image no single `σ` can have every `τ` as an
integer power of it — `1 ∈ ẑ` does not generate `ẑ` as an abstract
group.

CHECK THAT WOULD REFUTE THIS: exhibit a finite `X`, an action of `I_v`
trivial on `P_v`, and two elements of `I_v` whose actions generate a
non-cyclic subgroup of `Equiv.Perm X` — e.g. an `S₃` or a Klein
four-group image. The `S₃` configuration recorded on the consumer below
is exactly such an attempt, and it fails because its unipotent generator
has order `3 = p`, so it is wildly ramified.

Serre, *Corps Locaux* IV §2 and *Propriétés galoisiennes…*, Invent.
Math. 15 (1972), §1.3 (the tame quotient and the fundamental
characters); Neukirch, *Algebraic Number Theory*, II.7.11. -/
theorem exists_localInertia_generator_of_wildInertia_trivial
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {X : Type*} [Finite X]
    (act : (localInertiaGroup v) → X → X)
    (hone : ∀ x : X, act 1 x = x)
    (hmul : ∀ (a b : localInertiaGroup v) (x : X), act (a * b) x = act a (act b x))
    (hwild : ∀ π : localInertiaGroup v,
      (π : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) ∈ wildInertiaGroup v →
      ∀ x : X, act π x = x) :
    ∃ σ : localInertiaGroup v, ∀ τ : localInertiaGroup v, ∃ n : ℕ,
      ∀ x : X, act τ x = (act σ)^[n] x := by
  -- `act` with `hone`/`hmul` IS a group homomorphism into `Equiv.Perm X`:
  -- each `act a` is a bijection, with inverse `act a⁻¹`.
  obtain ⟨φ, hφ⟩ : ∃ φ : localInertiaGroup v →* Equiv.Perm X,
      ∀ (a : localInertiaGroup v) (x : X), φ a x = act a x :=
    ⟨{ toFun := fun a ↦ ⟨act a, act a⁻¹,
          fun x ↦ by rw [← hmul, inv_mul_cancel, hone],
          fun x ↦ by rw [← hmul, mul_inv_cancel, hone]⟩
       map_one' := Equiv.ext hone
       map_mul' := fun a b ↦ Equiv.ext (hmul a b) }, fun _ _ ↦ rfl⟩
  -- `X` is finite, so the image is a FINITE group killing wild inertia:
  -- procyclicity of the tame quotient gives a generator of that image.
  obtain ⟨σ, hσ⟩ := exists_localInertia_pow_eq_of_wildInertiaGroup_le_ker v
    φ.rangeRestrict φ.rangeRestrict_surjective (fun π hπ ↦ by
      ext x
      simpa [hφ] using hwild π hπ x)
  refine ⟨σ, fun τ ↦ ?_⟩
  obtain ⟨k, hk⟩ := hσ (φ.rangeRestrict τ)
  have hk' : (φ σ) ^ k = φ τ := by
    simpa using congrArg Subtype.val hk
  refine ⟨k, fun x ↦ ?_⟩
  -- and a power of the permutation `φ σ` is an iterate of `act σ`.
  have hiter : ∀ (m : ℕ) (y : X), ((φ σ) ^ m) y = (act σ)^[m] y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
        intro y
        rw [pow_succ, Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply, hφ]
  rw [← hφ τ x, ← hk', hiter]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **RAYNAUD AT `e = 1 < p − 1`, ELEMENT FORM: NO LOCAL-INERTIA ELEMENT
ACTS WITH ORDER `3` ON THE CONNECTED `3`-TORSION** (SORRY LEAF, cut
2026-07-27 out of
`exists_coprime_three_exponent_localInertia_connected_threeTorsion`
immediately below, which is now PROVEN over it and over nothing else).

Content: if `σ ∈ I₃` and `σ ^ 3` already fixes every connected
`3`-torsion geometric point of the generic fibre, then `σ` fixes every
one of them itself. Equivalently: the image of `I₃` in the permutation
group of the (finite) connected `3`-torsion socle has NO ELEMENT OF
ORDER `3`.

**THIS IS THE ENTIRE FINITE-FLAT INPUT OF THE `3`-adic hardly-ramified
cluster, and it is now the only declaration in it that spends
`e = 1 < p − 1 = 2`.** The mathematics — Raynaud's classification, the
two PARI/GP computations that bracket the statement, the `n = 2` trap,
the inventory of `OortTate` machinery already available, and the check
that would refute it — is carried IN FULL by the docstring of
`exists_coprime_three_exponent_localInertia_connected_threeTorsion`
immediately below, and a prover should read that first. Only what is
specific to THIS form is recorded here.

WHAT THE CUT DISCHARGED, AND WHY IT IS FREE. The parent's `∃ n` shape
is unchanged and is still what consumers see; all that moved out of the
mathematics is the group-theoretic bookkeeping, none of which carries
any arithmetic:

* the connected `3`-torsion socle is FINITE
  (`finite_points_of_hopf_order`, which is what the `Algebra.Etale`
  instance is for);
* it is `Γ ℚ₃ᵥ`-STABLE — `(τ • φ) ^ 3 = τ • φ ^ 3 = τ • 1 = 1` by
  `MulDistribMulAction`, and `(τ • φ) (1 ⊗ e₀) = τ (φ (1 ⊗ e₀)) = 1`
  because the action is postcomposition — so it is a `SubMulAction` and
  carries a permutation representation `perm : Γ ℚ₃ᵥ →* Equiv.Perm S`;
* `H := perm '' I₃` is a finite subgroup of `Equiv.Perm S`, and
  `n := Nat.card H` is an exponent for it (`pow_card_eq_one'`);
* CAUCHY (`exists_prime_orderOf_dvd_card'`) turns `3 ∣ Nat.card H` into
  an element of order exactly `3` in `H`, which is `perm σ` for some
  `σ ∈ I₃` — and that is precisely what this leaf forbids.

**THE INHERITED NOTE THAT THIS DIRECTION IS "STRICTLY HARDER TO REACH
FROM THE CLASSIFICATION" IS CORRECTED — the cut is provably free.** The
parent's docstring used to argue that the `∃ n` form is what Raynaud
produces and that the Cauchy-equivalent no-order-`3` form "would make
the next owner's job worse". The second half does not survive contact
with the implication: **the `∃ n` statement IMPLIES this one in two
lines** — if the permutation `p` induced by `σ` satisfies `p ^ 3 = 1`
and `p ^ n = 1` with `3 ∤ n`, then `orderOf p` divides `gcd 3 n = 1`,
so `p = 1`. Hence ANY route to the `∃ n` form is also a route to this
one, and proving this leaf is at most as hard as proving what it
replaced; the parent below shows it is also enough. What the `∃ n` form
genuinely does own — that it is the shape Raynaud's theorem produces,
the image of tame inertia landing in `μ_{3^r − 1}` — is preserved,
because the parent still STATES it and consumers still see it.

Every hypothesis is underscore-prefixed because the body is `sorry`;
they are all genuinely needed and a real proof must consume them. In
particular `hprim₀`/`hcomul₀` (the connectedness of `e₀`) cannot be
dropped: the good-ORDINARY-reduction computation on `11a1` recorded
below refutes the `e₀`-free statement.

---

**ROUTE AUDIT, 2026-07-27 (this leaf's owner; the leaf is still OPEN
and nothing below is proven here).** The parent's inventory ends with
"what is genuinely missing is the higher-rank case", which reads as
"all of Raynaud" and sent this owner at the whole classification.
That is too coarse. Five findings, each refutable by a named check.

**(1) THE CONTENT BEGINS AT SOCLE ORDER `9`, and the good-ORDINARY
case of the intended application needs NO finite-flat input.** Write
`S := {φ | φ ^ 3 = 1 ∧ φ (1 ⊗ e₀) = 1}` for the connected socle (the
parent below builds it as a `SubMulAction`). Suppose `σ • φ ≠ φ` for
some `φ ∈ S`. Then `1`, `φ`, `σ • φ`, `σ ^ 2 • φ` are FOUR DISTINCT
elements of `S`:

* `φ ≠ 1` because `σ • 1 = 1`, and `σ • φ ≠ 1 ≠ σ ^ 2 • φ` because
  `σ •` is injective;
* `σ ^ 2 • φ = φ` would give `σ • φ = σ ^ 3 • φ = φ` using `_hcube`;
* `σ • φ = σ ^ 2 • φ` would give `φ = σ • φ` by injectivity.

So a violation forces `4 ≤ Nat.card S`. For `E / ℚ₃` with good
ORDINARY reduction the connected socle `E[3]⁰(ℚ̄₃)` has exactly `3`
elements, so this leaf is VACUOUSLY in range there: the `11a1`
computation recorded below is not merely a bracket, it is a case that
connectedness has already removed. The whole finite-flat content of
this leaf lives at socle order `≥ 9`, i.e. in the SUPERSINGULAR and
higher-rank regime.

**(2) THE CYCLIC-ORBIT CASE IS UNCONDITIONAL — no arithmetic, two
lines.** If `σ • φ = φ ^ m` for some `m : ℕ`, then
`σ ^ 3 • φ = φ ^ (m ^ 3)` by `MulDistribMulAction`
(`σ • φ ^ k = (σ • φ) ^ k`, iterated), so `_hcube` gives
`φ ^ (m ^ 3) = φ`; with `φ ^ 3 = 1` that is `3 ∣ m ^ 3 - 1`, and
Fermat's little theorem `m ^ 3 ≡ m [MOD 3]` upgrades it to `3 ∣ m - 1`,
whence `φ ^ m = φ`. Three consequences:

* the entire content of this leaf is points that are moved OUT of their
  own cyclic subgroup `⟨φ⟩`;
* this is why `37a1` is NOT a counterexample even though inertia does
  move points out of `⟨φ⟩` there — its inertia image is `𝔽₉ˣ ≅ ℤ/8`
  and `gcd(3, 8) = 1`, so no `σ` satisfies `_hcube` nontrivially;
* **restating this leaf as "`∀ φ ∈ S, ∃ m, σ • φ = φ ^ m`" is an
  EQUIVALENCE, not a decomposition.** Do not cut there. (It is also one
  underscore away from the shape that was REFUTED as
  `exists_inertia_scalar_on_connected_locus_of_hopf_package`: quantified
  over all `τ ∈ I₃` rather than over the single `σ` with `_hcube`, it is
  FALSE in the supersingular case.)

**(3) THE MACHINERY THE INVENTORY ABOVE CALLS MISSING IS LARGELY
PRESENT, and it is not the `OortTate` cyclotomic node.** Two clusters,
neither in this file's import cone today, both checkable with one grep.
**And the cone-growth objection is nil, measured 2026-07-27**: this
file's cone is `60` project modules; `FlatPointsGroup.lean`'s own cone
is `33`, of which `32` are already here, so importing it adds exactly
ONE module; `ShortExact.lean` adds two and `CartierDual.lean` one.

* `Fermat/FLT/Deformations/RepresentationTheory/FlatPointsGroup.lean`
  carries RAYNAUD'S CLOSURE on the representation-free carrier
  `IsFlatPointsGroupAt v X` ("`X` is `Γ Kᵥ`-equivariantly the geometric
  point group of the generic fibre of a finite flat `𝒪ᵥ`-Hopf algebra
  with étale generic fibre"): `IsFlatPointsGroupAt.of_injective`
  (schematic closure of an equivariant SUBGROUP),
  `.of_surjective`, `.prod`, `.pi` — all PROVEN. So "the schematic
  closure of a `Γ`-stable subgroup of the socle is again a finite flat
  Hopf order" does NOT have to be built.
* `Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` carries
  `HopfAlgebra.IsMultiplicativeType R A` (*defined* as "the Cartier
  dual is étale"), `etale_of_isShortExact` and — the one that matters —
  **`isMultiplicativeType_of_isShortExact`, PROVEN**: an extension of
  multiplicative type by multiplicative type is of multiplicative type.

**(4) THE ROUTE, and exactly how far it reaches.** With (1)–(3) the
attack is Cartier duality, not the Raynaud normal form:

  a. `_hcube` plus `σ • φ ≠ φ` gives a UNIPOTENT configuration: in
     `char 3`, `(σ - 1) ^ 3 = σ ^ 3 - 1 = 0` on the socle, so `σ` acts
     unipotently and nontrivially, and `φ`, `(σ - 1) φ` span a
     `σ`-stable subgroup of order exactly `9` (if `(σ - 1) φ = c φ`
     then `(1 + c) ^ 3 = 1` in `𝔽₃` forces `c = 0`).
  b. Take a `Γ ℚ₃ᵥ`-stable filtration of the socle and push it through
     `IsFlatPointsGroupAt.of_injective` / `.of_surjective` to a short
     exact sequence of finite flat Hopf orders.
  c. If every graded piece is of MULTIPLICATIVE TYPE, then so is the
     whole (`isMultiplicativeType_of_isShortExact`), its Cartier dual is
     étale hence UNRAMIFIED, and inertia acts on the socle by the SCALAR
     `χ(σ)` — which is never a nontrivial unipotent. Contradiction with
     (a).
  d. Graded pieces of order `3` ARE of multiplicative type: a connected
     finite flat group scheme of order `p` over `ℤ₃` is `μ₃` up to
     unramified twist (Oort–Tate with `v(a) + v(b) = 1` and `v(a) > 0`
     forcing `v(a) = 1`), and its dual is the corresponding twist of
     `ℤ/3`, which is étale. This is the *dual-side* statement and it is
     TRUE, unlike the coordinate-side statement `exists_muType_closure`
     that was refuted by exactly those twists — cf. the development's
     rule that VALUES descend from `𝒪^nr` while COORDINATES do not.

  **How far it reaches, stated honestly: step (c) covers precisely the
  case where the socle admits a `Γ`-stable filtration with graded pieces
  of order `3`.** It does NOT cover the supersingular piece: for
  `E = 37a1` the socle is `𝔽₉` with `I₃` acting irreducibly through
  `𝔽₉ˣ`, so its only `Γ`-stable filtration is trivial and `E[3]` is
  self-dual, hence connected-dual, hence NOT of multiplicative type. The
  residue after this route is therefore the sharper leaf **"an extension
  of one connected simple killed-by-`3` object by another, over
  `e = 1 < p − 1`, carries no wild inertia"** — which is a bounded
  statement about `Ext¹` in the flat category, not the whole
  classification. (Note the supersingular case itself is free by (2):
  there `gcd(3, 8) = 1`.)

**(5) TWO THINGS NOT TO DO.**

* **The wild/tame split is a NET LOSS.** It is tempting to cut this leaf
  into "`P₃` acts trivially on the socle" (Raynaud) plus "the tame
  quotient is uniquely `3`-divisible" (pure local Galois theory, in the
  idiom of `exists_localInertia_generator_mod_pow_wildInertiaGroup`); the
  assembly is four lines, since `σ = θ ^ 3 · w` makes cubing SURJECTIVE
  hence injective on the finite image. But the arithmetic half is not
  made one step easier, a brand-new obligation is created, and the
  `∃ n` parent below plus
  `wildInertia_fixes_connected_threeTorsion_of_hopf_package` become a
  detour around a statement that would then imply them directly. Refuting
  check: find a proof of "`P₃` acts trivially" that does not also prove
  this leaf.
* **COCOMMUTATIVITY IS NOT ASSUMED HERE, AND EVERY STEP OF (4) NEEDS
  IT.** `G` is a bare `HopfAlgebra 𝒪₃ᵥ G`, i.e. an affine group scheme
  that is not assumed COMMUTATIVE; the convolution structure on
  `ℚ₃ᵥ ⊗ G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ` (`Deformations/RepresentationTheory/Etale.lean`)
  is only a `Monoid`, so the socle `S` is not known to be a GROUP, let
  alone an `𝔽₃`-vector space. Raynaud's classification is for commutative
  group schemes, `ShortExact.lean` carries `[IsCocomm R A]` throughout,
  and `IsFlatPointsGroupAt` takes an `AddCommGroup`. The eventual
  consumer has commutativity for free — in
  `wildInertia_fixes_connected_threeTorsion_of_hopf_package` below, `fG`
  is a BIJECTION from `Additive (points)` onto an `AddCommGroup` — so the
  repair is to thread `[IsCocomm 𝒪₃ᵥ G]` (or the weaker
  `CommMonoid (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)`) through this leaf and the
  `∃ n` parent. That is a CUT-LEVEL repair spanning three declarations
  and was deliberately not made here; it should be made by whoever
  attacks (4), since without it step (a) cannot even be stated.

**AXIS SEARCHED.** This audit ranged over: permutation/group-theoretic
cuts (exhausted by the parent, and (2) shows the natural remaining one is
an equivalence); the `OortTate` cyclotomic node (blocked — its `hstab`
hypothesis is exactly the refuted scalar leaf); the wild/tame Galois
split (net loss, above); and Fontaine's ramification bound (computed
insufficient: for `n = 1`, `e = 1`, `p = 3` it kills `u > 3/2`, while a
`ℤ/3`-extension of `ℚ₃ⁿʳ` has upper break exactly `1 ≤ 3/2` — the bound
permits precisely the configuration that must be excluded). NOT searched,
and the axis that (4) opens: the Cartier-duality/`IsMultiplicativeType`
route, and the `Ext¹` residue named at the end of (4).

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5 and 3.4.3; Fontaine, *Il n'y a pas de variété
abélienne sur `ℤ`*, §1; Serre, *Propriétés galoisiennes…*, Invent.
Math. 15 (1972), §1.11; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem smul_eq_of_pow_three_smul_eq_localInertia_connected_threeTorsion
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (_he₀ : IsIdempotentElem e₀)
    (_hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (_hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (_hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    {σ : Γ ℚ₃ᵥ} (_hσ : σ ∈ localInertiaGroup 𝔭₃)
    (_hcube : ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ, φ ^ (3 : ℕ) = 1 →
      φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → (σ ^ (3 : ℕ)) • φ = φ) :
    ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ, φ ^ (3 : ℕ) = 1 →
      φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → σ • φ = φ :=
  sorry

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud at `e = 1 < p − 1`: LOCAL INERTIA acts on the connected
`3`-torsion through a finite quotient of order PRIME TO `3`** (was a
SORRY LEAF cut 2026-07-27 out of
`wildInertia_fixes_connected_threeTorsion_of_hopf_package` just below,
which is PROVEN over it; PROVEN in turn the same day over the single
element-form leaf
`smul_eq_of_pow_three_smul_eq_localInertia_connected_threeTorsion`
immediately above, which now carries all of the finite-flat input).

Content: there is ONE exponent `n`, PRIME TO `3`, such that `σ ^ n`
fixes EVERY connected `3`-torsion geometric point of the generic fibre,
for every `σ ∈ I₃`. Equivalently — and this is the reading to keep in
mind — the image of local inertia in the permutation group of the
(finite) connected `3`-torsion socle is a finite group of order prime
to `3`, i.e. **the action is TAME**.

THIS IS THE ENTIRE FINITE-FLAT INPUT OF THE `3`-adic hardly-ramified
cluster: `e = 1 < p − 1 = 2` is spent HERE and nowhere else in it —
since 2026-07-27, one declaration further down, in the element-form
leaf above. Nothing else above and nothing below does.

**THE PROOF, in four moves, none of which touches the classification.**

1. FINITENESS. The geometric point set of the generic fibre is finite
   (`finite_points_of_hopf_order`, which is what the `Algebra.Etale`
   instance is for), hence so is the subset
   `S := {φ | φ ^ 3 = 1 ∧ φ (1 ⊗ e₀) = 1}` of connected `3`-torsion
   points.
2. STABILITY. `S` is `Γ ℚ₃ᵥ`-stable: the action is postcomposition, so
   `(τ • φ) (1 ⊗ e₀) = τ (φ (1 ⊗ e₀)) = τ 1 = 1`, and
   `(τ • φ) ^ 3 = τ • φ ^ 3 = τ • 1 = 1` by `MulDistribMulAction`. So
   `S` is a `SubMulAction` and `MulAction.toPermHom` gives a
   permutation representation `perm : Γ ℚ₃ᵥ →* Equiv.Perm S`.
3. THE EXPONENT. `H := (localInertiaGroup 𝔭₃).map perm` is a subgroup
   of the finite group `Equiv.Perm S`, and `n := Nat.card H` kills it
   (`pow_card_eq_one'`); unwinding `perm (σ ^ n) = 1` is exactly
   `(σ ^ n) • φ = φ` for every `φ ∈ S`.
4. `3 ∤ n`. If `3 ∣ Nat.card H`, CAUCHY
   (`exists_prime_orderOf_dvd_card'`) produces an element of order
   exactly `3` in `H`; it is `perm σ` for some `σ ∈ I₃`, and
   `(perm σ) ^ 3 = 1` says `σ ^ 3` fixes every connected `3`-torsion
   point. The element-form leaf above then makes `σ` itself act
   trivially, i.e. `perm σ = 1`, contradicting `orderOf … = 3`.

Note what this does NOT do: it produces no bound on `n` and no
classification. `n` is simply the order of the image, which is what the
statement asserts to be prime to `3`; all the arithmetic sits in step 4
and is deferred whole to the leaf.

WHY THIS SHAPE — WHAT THE CUT OF 2026-07-27 REMOVED, AND WHAT IT
DELIBERATELY DID NOT. Two pieces were peeled off the previous statement
of `wildInertia_fixes_connected_threeTorsion_of_hopf_package`, and
NEITHER of them carried any finite-flat content:

* the HOPF PACKAGE. `ρ'`, `N`, `A`, `fG`, `hfG` are gone. They only
  transported the statement from geometric points to vectors of a
  Galois representation, which is `map_add`/`map_smul` of an
  equivariant bijection — done in the consumer below by the same three
  moves as `inertiaFixed_connected_vector_eq_zero_of_hopf_package`.
  What remains here is a PURE finite-flat-group-scheme statement in the
  idiom of `Fermat/FLT/GroupScheme/ConnectedEtale.lean`'s `OortTate`
  namespace, so a prover can work entirely inside that machinery;
* the WILD-TO-TAME CONVERSION. The old statement quantified over
  `wildInertiaGroup 𝔭₃`; this one quantifies over all of
  `localInertiaGroup 𝔭₃` and produces a prime-to-`3` exponent instead.
  The passage back is `exists_pow_eq_of_mem_wildInertiaGroup`
  (`ArtinConductor.lean`): `P₃` is pro-`3`, so every `π ∈ P₃` is an
  `n`-th power `θ ^ n` of some `θ ∈ P₃` whenever `3 ∤ n`, and then
  `π • φ = (θ ^ n) • φ = φ`. That is where "wild = pro-`3`" belongs; it
  is somebody else's leaf (`coprime_card_quotient_wildInertiaGroup`)
  and it should not be re-proved inside a Raynaud argument.

What was NOT peeled off is the classification itself. The `∃ n` form is
the shape Raynaud's theorem actually PRODUCES (the image of tame
inertia lands in `μ_{3^r − 1}`), which is why THIS statement is written
that way and why consumers still see it that way.

**CORRECTION 2026-07-27, and it is what made the cut above possible.**
This paragraph used to continue "…rather than the equivalent 'the image
has no element of order `3`': the latter is Cauchy-equivalent but
strictly harder to reach from the classification, and would make the
next owner's job worse." The second half is **false**, and acting on it
would have kept the group-theoretic bookkeeping welded to the
arithmetic. The `∃ n` statement IMPLIES the no-order-`3` statement in
two lines — if the permutation induced by `σ` has cube the identity and
also `n`-th power the identity with `3 ∤ n`, its order divides
`gcd 3 n = 1` — so the element form is at most as hard to reach from
the classification as this one, by ANY route, and the four-move proof
recorded above shows it is also sufficient. The `∃ n` form is kept
exactly where it belongs: in the STATEMENT a consumer reads.

MATHEMATICAL CONTENT. The connected `3`-torsion socle is the geometric
point group of the schematic closure, inside `Spec (e₀ G)`, of the
`3`-torsion of the generic fibre: a finite flat `𝒪ᵥ`-group scheme
KILLED BY `3` over a base with `e = 1 < p − 1 = 2`. Raynaud (Bull. SMF
102 (1974), 3.3.2–3.3.5 and 3.4.3) classifies these: the action of
inertia is through products of fundamental characters `∏ ψᵢ ^ nᵢ` with
`nᵢ ≤ e = 1`, and fundamental characters are TAME — they factor through
`I₃ / P₃`, whose finite quotients all have order prime to `3` (the tame
quotient is `∏_{ℓ ≠ 3} ℤ_ℓ`). Taking `n` to be the order of the image
of `I₃` in the permutation group of the socle — finite because the
point set is (`finite_points_of_hopf_order`, which is what the
`Algebra.Etale` instance is for) — gives the statement.

**DO NOT AIM AT `n = 2`: THE PURELY CYCLOTOMIC ANSWER IS FALSE, AND
THIS IS COMPUTED (PARI/GP, 2026-07-27).** The order-`p` machinery in
`OortTate` (`inertia_character_trivial_or_cyclotomic`,
`connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter`) gives
`σ • φ = φ ^ χ(σ)` when `⟨φ⟩` is inertia-stable, whence `n = 2` since
`(ℤ/3)ˣ` has order `2`. That case is real but it is NOT the general
one: `E = 37a1 = [0,0,1,−1,0]` has conductor `37` (good reduction at
`3`) and `a₃ = −3 ≡ 0 (mod 3)`, so it is SUPERSINGULAR at `3`; its
formal group has height `2`, so `E[3]` is CONNECTED in its entirety and
every hypothesis here holds with `e₀` the whole component. Tame inertia
then acts through the LEVEL-`2` fundamental characters, i.e. through
`𝔽₉ˣ ≅ ℤ/8`, and the computation confirms it:

    E = ellinit([0,0,1,-1,0]);   K = nfinit(nfsplitting(elldivpol(E,3)));
    poldegree(K.pol)             \\ 24
    [ [pr.e, pr.f] | pr <- idealprimedec(K,3) ]   \\ [[4,2],[4,2],[4,2]]

`e = 4` on the `x`-coordinate field (so `e ∈ {4, 8}` on `ℚ(E[3])`,
which is at most quadratic over it) — PRIME TO `3`, hence tame, exactly
as this leaf asserts, but with `n = 8` and not `n = 2`. A proof that
concludes `σ • φ = φ ^ χ(σ)` in general is therefore WRONG, and the
correct input is tameness alone.

**CONNECTEDNESS IS ESSENTIAL AND THE `e₀`-FREE FORM IS FALSE — do not
"simplify" this leaf by dropping `e₀`, `he₀`, `hε₀`, `hprim₀`,
`hcomul₀`.** The tempting stronger statement is "inertia acts tamely on
ALL of `M[3]`". It is refuted by GOOD ORDINARY REDUCTION at `3`: for
`E / ℚ₃` with good ordinary reduction, `E[3]` IS finite flat over `ℤ₃`
(so every hypothesis of the dropped form holds, with `e = 1 < p − 1`),
yet `ρ_{E,3} |_{I₃}` is `[[ω, *], [0, 1]]` with the extension class `*`
a Kummer class of a `3`-adic UNIT, and `ℚ₃(ζ₃, u^{1/3})` is wildly
ramified for `u` a unit that is not a cube modulo `λ³`
(`λ = ζ₃ − 1`, `v_λ(3) = 2`). What Raynaud bounds in that situation is
only the SEMISIMPLIFICATION; Fontaine's ramification bound for
`n = 1, e = 1, p = 3` is `u > e (n + 1/(p − 1)) = 3/2`, which permits a
wild break in `(0, 3/2]` and the ordinary curve realises one. The
connected part `E[3]⁰ = Ê[3] ≅ μ₃ ⊗ ψ` is rank one and tame — the
wildness lives entirely in the EXTENSION, which the connectedness
hypothesis removes.

THE REFUTATION IS COMPUTED, NOT ASSERTED (PARI/GP, re-run 2026-07-27
alongside the supersingular check above). `E = 11a1 =
[0,−1,1,−10,−20]` has conductor `11` (good reduction at `3`) and
`a₃ = −1 ≢ 0 (mod 3)` (ORDINARY at `3`), hence `E[3]` is a finite flat
`ℤ₃`-group scheme killed by `3` with `e = 1 < p − 1`. Its `3`-division
field ramifies at `3` with `e = 6`, and `3 ∣ 6`, i.e. WILDLY.
Re-runnable in seconds:

    E = ellinit([0,-1,1,-10,-20]);  P = elldivpol(E,3);
    K = nfinit(nfsplitting(P));     idealprimedec(K,3)
    \\ degree 24, four primes above 3, each with e = 6, f = 1

(The `x`-coordinate field suffices: `ℚ(E[3])` is at most a quadratic
extension of it, so it cannot introduce or remove a factor of `3` in
`e`.) Note how sharply the two computations bracket this leaf: same
prime, same `e = 1`, same "finite flat killed by `3`" — `e = 6` (wild)
without connectedness, `e = 4` (tame) with it. Anyone tempted to
restate this leaf without `e₀` should run both first.

WHY THE CONNECTED CASE IS NEVERTHELESS TAME. The graded pieces of a
connected `G⁰` killed by `3` over `ℤ₃` are the connected SIMPLE objects
— `μ₃` up to unramified twist, and the higher Raynaud
`𝔽_{3^r}`-vector-space schemes whose inertia action is by level-`r`
fundamental characters — all of them tame. The extensions do not
reintroduce wildness: for an iterated extension of `μ₃`-types the
Cartier dual is an extension of étale by étale, hence étale, hence
UNRAMIFIED, and `G⁰(K̄) ≅ (G⁰)^∨(K̄)^∨ ⊗ μ₃` is then `ω ⊗ unramified`.

**THE DUALITY ROUTE IS NO LONGER ABSENT — the older note here saying
the grep "matches only docstrings" is STALE.**
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean` builds
Cartier duality for finite flat commutative group schemes, sorry-free
(biduality, the dual Hopf structure, `finrank_cartierDual`), and
`.../HopfAlgebra/ShortExact.lean` adds `CartierDual.map`,
`HopfAlgebra.IsShortExact` and `etale_of_isShortExact`.

**CORRECTED 2026-07-27 — this paragraph named the wrong leaf and called
it owned; both halves were wrong.** `HopfAlgebra.IsShortExact.cartierDual`
(exactness of duality) is **PROVEN**, a four-field assembly, as is
`etale_of_isShortExact`; nothing on that route is owned. The leaves that
ARE open in `ShortExact.lean`, all four of them unowned until 2026-07-27,
are `Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation`
(`:238`), `HopfAlgebra.IsShortExact.exists_linearRetraction` (`:564`),
`.ker_cartierDual_le` (`:628`) and `.faithfullyFlat_cartierDual` (`:648`).
The reason the note went stale invisibly is worth knowing: that whole
`HopfAlgebra` cluster was an UNREACHABLE ISLAND — five modules that no
module in `Fermat.lean`'s import closure imported, so `lake build` never
compiled them and neither the sorry-warning set nor the census could see
their leaves; the cause was structural (the files lacked `module`
headers, and a `module` file cannot import a non-`module` one, so the
import was not expressible). Repaired in `1492cecb`; the cluster builds
green. Re-run `grep -rn 'cartierDual' Fermat/` and check the current
sorry set before believing any statement in this paragraph.

WHAT ELSE IS ALREADY BUILT AND SHOULD BE READ FIRST. In
`ConnectedEtale.lean`'s `OortTate` namespace, all PROVEN:
`point_sub_counit_mem_maximalIdeal` (connectedness ⇒ the point reduces
to the counit), `displacement_span_eq_span_zeta_sub_one` (Raynaud's
valuation computation for an order-`3` inertia-stable point: the
displacement ideal is exactly `(ζ₃ − 1)`),
`inertia_character_trivial_or_cyclotomic`,
`not_inertia_character_trivial_of_connected`,
`connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter`,
`mem_span_natCast_of_inertia_invariant` (where `e = 1` is spent
elsewhere), and the convolution-filtration toolkit
(`exists_convPow_rem`, `fg_span_range`, `convPow_apply_mem_pow`). The
RANK-ONE case of this leaf is essentially assembled from those, with
`n = 2`; what is genuinely missing is the higher-rank case, i.e. the
level-`r` fundamental characters.

**SHARPENED 2026-07-27 — read the ROUTE AUDIT on the element-form leaf
above before acting on the sentence just written.** "The higher-rank
case" reads as "all of Raynaud" and is too coarse: the socles of order
`≤ 3` are free, the cyclic-orbit case is free, the schematic closure of
a `Γ`-stable subgroup already exists
(`IsFlatPointsGroupAt.of_injective`, `FlatPointsGroup.lean`), and the
extension step already exists and is PROVEN
(`isMultiplicativeType_of_isShortExact`, `ShortExact.lean`). The audit
also records a COCOMMUTATIVITY gap that spans this statement too.

WHAT DEFEATS THE `S₃` CONFIGURATION, MECHANICALLY. For `A = 𝔽₃²` with
`I` acting through a copy of `S₃` by `σ ↦ [[1,1],[0,1]]` and
`τ ↦ diag(−1,1)` one has `A^I = 0` while EVERY single element fixes a
nonzero vector, so no derivation of the downstream consumer from
`(M⁰)^{I₃} = 0` alone can exist. This leaf is what rules the
configuration out: `[[1,1],[0,1]]` has order `3 = p`, so that image has
order divisible by `3`, which is exactly what is forbidden here. Any
proof of this leaf must therefore spend `e < p − 1`; a proof that does
not is wrong.

FAITHFULNESS. The conclusion is a VALUE-level statement about geometric
points; the quantifier `σ ∈ localInertiaGroup 𝔭₃` is over INERTIA and
is not widened to `Γ ℚ₃ᵥ` — widening it would make the leaf FALSE, since
the unramified quotient contributes Frobenius, whose order on the socle
is `f`-related and can perfectly well be divisible by `3`. No element of
`G`, no coordinate and no normal form appears, so the leaf is on the
true side of the development's `𝒪ᵥ`-descent rule and blind to the
`p − 1` unramified twists `μ₃ ⊗ ψ` that killed `exists_muType_closure`:
a twist changes WHICH points are connected, not how tamely inertia
moves them. The connected `3`-torsion point set IS `Γ ℚ₃ᵥ`-stable
(`(σ • φ) (1 ⊗ e₀) = σ (φ (1 ⊗ e₀)) = 1` and
`(σ • φ) ^ 3 = σ • φ ^ 3 = 1`), so the statement is not quietly empty.

CHECK THAT WOULD REFUTE THIS: exhibit a finite flat `ℤ₃`-Hopf order `G`
killed by `3` with a primitive counit-one idempotent `e₀`, and a
`σ ∈ I₃` whose action on the connected `3`-torsion points has order
divisible by `3` — equivalently, a connected finite flat `ℤ₃`-group
scheme killed by `3` whose points generate a wildly ramified extension.
The two `gp` runs above are the two nearest misses: `11a1` produces
wildness but only on the FULL (non-connected) `3`-torsion, and `37a1`
produces a genuinely connected `E[3]` whose ramification is tame.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5 and 3.4.3; Fontaine, *Il n'y a pas de variété
abélienne sur `ℤ`*, §1 (the ramification bound); Serre, *Propriétés
galoisiennes…*, Invent. Math. 15 (1972), §1.11 (fundamental characters
and the procyclic tame quotient); Tate, *Finite flat group schemes*,
§4, in Cornell–Silverman–Stevens. -/
theorem exists_coprime_three_exponent_localInertia_connected_threeTorsion
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀) :
    ∃ n : ℕ, ¬ (3 ∣ n) ∧
      ∀ σ ∈ localInertiaGroup 𝔭₃, ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ,
        φ ^ (3 : ℕ) = 1 → φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → (σ ^ n) • φ = φ := by
  classical
  -- STEP 1. the geometric point set is FINITE
  haveI hfinA : Finite (Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) :=
    finite_points_of_hopf_order G
  haveI hfin : Finite (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) :=
    Finite.of_equiv _ (Additive.toMul (α := ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ))
  -- STEP 2. the connected `3`-torsion points, as a `Γ`-STABLE subset
  set S : SubMulAction (Γ ℚ₃ᵥ) (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) :=
    { carrier := {φ | φ ^ (3 : ℕ) = 1 ∧ φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1}
      smul_mem' := by
        rintro τ φ ⟨h3, he⟩
        refine ⟨(smul_pow' τ φ 3).symm.trans (by rw [h3, smul_one]), ?_⟩
        show τ (φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀)) = 1
        rw [he, map_one] }
  have hmemS : ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ,
      φ ∈ S ↔ (φ ^ (3 : ℕ) = 1 ∧ φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) := fun _ => Iff.rfl
  haveI hfinS : Finite ↥S := Subtype.finite
  -- STEP 3. the PERMUTATION REPRESENTATION of `Γ ℚ₃ᵥ` on that finite set,
  -- and the image `H` of the local inertia inside it
  set perm : Γ ℚ₃ᵥ →* Equiv.Perm ↥S := MulAction.toPermHom (Γ ℚ₃ᵥ) ↥S with hperm
  set H : Subgroup (Equiv.Perm ↥S) := (localInertiaGroup 𝔭₃).map perm
  haveI hfinH : Finite ↥H := Subtype.finite
  -- `perm g = 1` says exactly that `g` fixes every connected `3`-torsion point
  have hperm_eq_one : ∀ g : Γ ℚ₃ᵥ, perm g = 1 →
      ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ, φ ^ (3 : ℕ) = 1 →
        φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → g • φ = φ := by
    intro g hg φ h3 he
    have hmem : φ ∈ S := (hmemS φ).mpr ⟨h3, he⟩
    have := congrArg (fun p : Equiv.Perm ↥S => (p ⟨φ, hmem⟩ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) hg
    simpa [hperm, MulAction.toPermHom] using this
  refine ⟨Nat.card ↥H, ?_, ?_⟩
  · -- STEP 4. `3 ∤ |H|`: CAUCHY would give an inertia element acting with
    -- order exactly `3`, which the Raynaud leaf above forbids
    intro hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 hdvd
    obtain ⟨σ, hσI, hσx⟩ := Subgroup.mem_map.mp x.2
    -- `x ^ 3 = 1`, so `σ ^ 3` fixes every connected `3`-torsion point
    have hx3 : (x : Equiv.Perm ↥S) ^ (3 : ℕ) = 1 := by
      have h : x ^ (3 : ℕ) = 1 := by
        have h0 := pow_orderOf_eq_one x
        rwa [hx] at h0
      simpa using congrArg (Subgroup.subtype H) h
    have hcube : ∀ φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ, φ ^ (3 : ℕ) = 1 →
        φ ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 → (σ ^ (3 : ℕ)) • φ = φ := by
      refine hperm_eq_one _ ?_
      rw [map_pow, hσx]
      exact hx3
    -- the leaf then says `σ` itself acts trivially, i.e. `x = 1`
    have hfix := smul_eq_of_pow_three_smul_eq_localInertia_connected_threeTorsion
      G e₀ he₀ hε₀ hprim₀ hcomul₀ hσI hcube
    have hx1 : x = 1 := by
      refine Subtype.ext ?_
      rw [← hσx]
      refine Equiv.ext fun φ => Subtype.ext ?_
      show σ • (φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) = (φ : ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)
      exact hfix _ ((hmemS _).mp φ.2).1 ((hmemS _).mp φ.2).2
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · -- STEP 5. `σ ^ |H|` acts trivially: `perm σ` lies in the finite group `H`
    intro σ hσ φ h3 he
    refine hperm_eq_one _ ?_ φ h3 he
    rw [map_pow]
    have hmem : perm σ ∈ H := Subgroup.mem_map_of_mem _ hσ
    have := pow_card_eq_one' (G := ↥H) (x := ⟨perm σ, hmem⟩)
    exact_mod_cast congrArg (Subgroup.subtype H) this

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud at `e = 1 < p − 1`: the CONNECTED `3`-torsion is TAMELY
ramified** (PROVEN 2026-07-27 over the single leaf
`exists_coprime_three_exponent_localInertia_connected_threeTorsion` just
above, into which it was decomposed on that date, together with the
PROVEN-modulo-its-own-leaf `exists_pow_eq_of_mem_wildInertiaGroup`; it
was itself a SORRY LEAF, cut 2026-07-27 out of
`exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
below, which is PROVEN over it together with the procyclicity leaf
`exists_localInertia_generator_of_wildInertia_trivial` just above).

Content: WILD inertia at `3` acts TRIVIALLY on every CONNECTED vector
killed by `3` — every `w` with `3 • w = 0` whose point takes the value
`1` at the connected counit idempotent `e₀`.

This is the Hopf-package reading of the leaf above, and **it spends no
finite-flat input of its own**: everything Raynaud is in that leaf, and
everything about the wild inertia being pro-`3` is in
`exists_pow_eq_of_mem_wildInertiaGroup`. The docstring of the leaf above
carries the mathematics, the two `gp` computations that bracket it
(`11a1` wild without connectedness, `37a1` tame with it), the reason
`n = 2` is the WRONG target, and the inventory of `OortTate` machinery
already available.

PROOF, in two moves, neither of which touches the classification.

1. THE PRO-`3` MOVE. The leaf hands over an exponent `n` with `3 ∤ n`.
   Since `𝔭₃` has residue characteristic `3`, `3 ∤ n` is exactly
   `(n : 𝓞 ℚ) ∉ 𝔭₃.asIdeal`
   (`Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal`), so
   `exists_pow_eq_of_mem_wildInertiaGroup` produces `θ ∈ P₃` with
   `θ ^ n = π`. As `P₃ ≤ I₃`
   (`wildInertiaGroup_le_localInertiaGroup`), the leaf applies to `θ`
   and gives `π • φ = (θ ^ n) • φ = φ` for the point `φ` of `w`.
2. THE TRANSPORT. `fG` is additive and `Γ ℚ₃ᵥ`-equivariant, so
   `fG⁻¹` carries `3 • w = 0` to `φ ^ 3 = 1` (`toMul_nsmul`), the
   connectedness hypothesis is `φ (1 ⊗ e₀) = 1` verbatim, and
   `π • φ = φ` transports back to `ρ'(π) w = w` by `map_smul`. These
   are the same three moves as
   `inertiaFixed_connected_vector_eq_zero_of_hopf_package` above.

`hprim₀` and `hcomul₀` are passed straight through to the leaf, where
they are the connectedness of `e₀`; they are not used here. Note the
inherited paragraph "`hprim₀` IS ESSENTIAL — WITHOUT IT THE STATEMENT
IS FALSE", offering the constant group scheme `ℤ/3` with `e₀ = 1`, was
never a refutation of this statement (its own witness concedes the
conclusion): it refutes the PARENT
`exists_localInertia_no_fixed_connected_vector_of_hopf_package`, not
this. The real reason connectedness cannot be dropped is the good
ORDINARY reduction computation recorded on the leaf above.

FAITHFULNESS. The conclusion is a VALUE-level statement about vectors;
the quantifier `π ∈ wildInertiaGroup 𝔭₃` is over (wild) INERTIA and is
not widened to `Γ`, and no element of `G`, no coordinate and no normal
form appears. So the statement is on the true side of the development's
`𝒪ᵥ`-descent rule and blind to the `p − 1` unramified twists `μ₃ ⊗ ψ`
that killed `exists_muType_closure`: a twist changes WHICH vectors are
connected, not whether wild inertia moves them.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5 and 3.4.3; Fontaine, *Il n'y a pas de variété
abélienne sur `ℤ`*, §1 (the ramification bound); Serre, *Propriétés
galoisiennes…*, Invent. Math. 15 (1972), §1.11; Tate, *Finite flat
group schemes*, §4, in Cornell–Silverman–Stevens. -/
theorem wildInertia_fixes_connected_threeTorsion_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG) :
    ∀ π ∈ wildInertiaGroup 𝔭₃, ∀ w : N, (3 : ℕ) • w = 0 →
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm w))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (ρ'.toLocal 𝔭₃) π w = w := by
  classical
  obtain ⟨n, hn3, hfix⟩ :=
    exists_coprime_three_exponent_localInertia_connected_threeTorsion G e₀ he₀ hε₀
      hprim₀ hcomul₀
  -- `n` is prime to the residue characteristic `3`
  have hnv : ((n : ℕ) : NumberField.RingOfIntegers ℚ) ∉
      (Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).asIdeal := by
    rw [Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal, map_natCast]
    intro h
    exact hn3 (by exact_mod_cast h)
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : N, fG (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
  have hgs_nsmul : ∀ (j : ℕ) (x : N), g.symm (j • x) = j • g.symm x := by
    intro j x
    induction j with
    | zero => rw [zero_nsmul, zero_nsmul, hgs_zero]
    | succ j ih => rw [succ_nsmul, succ_nsmul, hgs_add, ih]
  intro π hπ w hw3 hwc
  -- `P₃` is pro-`3`, so `π` is an `n`-th power INSIDE `P₃`
  obtain ⟨θ, hθ, hθn⟩ := exists_pow_eq_of_mem_wildInertiaGroup 𝔭₃ hnv hπ
  have hθI : θ ∈ localInertiaGroup 𝔭₃ := wildInertiaGroup_le_localInertiaGroup 𝔭₃ hθ
  -- the point of `w` is killed by `3` in the convolution group
  have hord : (Additive.toMul (g.symm w)) ^ (3 : ℕ) = 1 := by
    have h0 : (3 : ℕ) • g.symm w = 0 := by rw [← hgs_nsmul, hw3, hgs_zero]
    have h1 := congrArg Additive.toMul h0
    rwa [toMul_nsmul, toMul_zero] at h1
  have hfixφ := hfix θ hθI (Additive.toMul (g.symm w)) hord hwc
  rw [hθn] at hfixφ
  have h1 : π • g.symm w = g.symm w := by
    apply Additive.toMul.injective
    show Additive.toMul (π • g.symm w) = Additive.toMul (g.symm w)
    have h2 : Additive.toMul (π • g.symm w) = π • Additive.toMul (g.symm w) := rfl
    rw [h2, hfixφ]
  have h3 : fG (π • g.symm w) = fG (g.symm w) := congrArg fG h1
  rw [map_smul fG, hfs] at h3
  exact h3

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud TAMENESS at `e = 1 < p − 1`: local inertia acts on the
connected `3`-torsion through a CYCLIC quotient** (PROVEN 2026-07-27
over the two leaves `exists_localInertia_generator_of_wildInertia_trivial`
and `wildInertia_fixes_connected_threeTorsion_of_hopf_package` just
above, into which it was decomposed on that date; it was itself a SORRY
LEAF, cut 2026-07-27 out of
`exists_localInertia_no_fixed_connected_vector_of_hopf_package` below,
which is PROVEN over it together with the order leaf
`connected_vector_threePow_torsion_of_hopf_package` just above).

Content: there is ONE `σ ∈ localInertiaGroup 𝔭₃` whose fixed locus on
the connected `3`-torsion is contained in the fixed locus of EVERY
`τ ∈ localInertiaGroup 𝔭₃` — i.e. the image of `σ` GENERATES the image
of local inertia in the automorphism group of the connected socle.

THIS IS THE ENTIRE CLASSIFICATION CONTENT OF THE PARENT, and it is
stated in the smallest form that carries it: only `3`-torsion vectors,
and only the containment of fixed loci. Everything else the parent
needs — closure of the connected locus under `ℕ`-multiples, the
Nakayama descent from `3 ^ k`-torsion to the socle, and the passage
from "fixed by all of `I₃`" to `0` — is discharged below over the
PROVEN `inertiaFixed_connected_vector_eq_zero_of_hopf_package`.

THE DECOMPOSITION OF 2026-07-27, and why it is along the right seam.
The recorded route below has exactly two inputs, and they come from
completely different subjects and fail for different reasons, so they
are now two leaves with independent owners:

* the FINITE-FLAT input, "wild inertia acts trivially on the connected
  `3`-torsion", is `wildInertia_fixes_connected_threeTorsion_of_hopf_package`
  — this is the declaration that spends `e = 1 < p − 1 = 2`, and it is
  Raynaud and nothing else. Its docstring records the refutation of the
  tempting `e₀`-free generalisation (good ORDINARY reduction at `3`
  realises a wild break), so the connectedness hypothesis is now known
  to be load-bearing rather than merely inherited;
* the LOCAL-FIELD input, "the tame quotient is procyclic, so its finite
  quotients are cyclic", is
  `exists_localInertia_generator_of_wildInertia_trivial` — stated
  generically in `K` and `v`, with no representation, no group scheme
  and nothing `3`-adic in it, and therefore reusable across the whole
  development. Its docstring also discharges the continuity obligation a
  prover would otherwise chase: every ABSTRACT finite quotient of
  `∏_ℓ ℤ_ℓ` is already cyclic.

PROOF (what is discharged HERE, and it is all of the non-classification,
non-local-field content). The connected locus `C` is closed under `0`
and `+` (counit-one and comultiplication absorption, through
`convMul_apply_one_of_comul_absorbs`) and every inertia displacement
lies in it (`inertia_displacement_apply_connected_idempotent_eq_one`),
so `C` is INERTIA-STABLE — `ρ'(τ) x = (ρ'(τ) x − x) + x`. The geometric
point set is FINITE (`Module.Finite 𝒪ᵥ G` base-changes to
`Module.Finite ℚ₃ᵥ (ℚ₃ᵥ ⊗ G)` and mathlib's instance `Finite (S →ₐ[R] K)`
applies; `fG` transports it to the space), so the socle
`S = {x | 3 • x = 0 ∧ x ∈ C}` is a FINITE inertia-stable set. That makes
`S` a legitimate `X` for the procyclicity leaf, whose `hwild` hypothesis
is exactly the Raynaud leaf. It returns `σ` with every `τ` acting as an
ITERATE of `act σ`, and `Function.iterate_fixed` turns `σ`-fixedness
into fixedness by that iterate, hence by `τ`. No Raynaud input and no
tame-quotient theory enter here.

WHY TAMENESS AND NOT ω-ISOTYPY. An earlier framing of the parent
attributed the defeat of the `S₃` counterexample below to "Raynaud's
ω-isotypy at `e = 1`". That is WRONG as stated and must not be
reinstated: supersingular `E[3]/ℚ₃` has good reduction and `e = 1`, yet
tame inertia acts there through the LEVEL-2 fundamental characters (of
order `8`), so the connected part is not ω-isotypic in general. The
correct input is tameness alone — which still yields cyclicity, since
the nonsplit-Cartan image `𝔽₉ˣ ≅ ℤ/8` is cyclic and its generators act
without fixed vectors. This is also why the parent is stated as
fixed-point-freeness rather than as a scalar action: a scalar-action
leaf would have been FALSE.

WHAT DEFEATS THE `S₃` COUNTEREXAMPLE, MECHANICALLY. For `A = 𝔽₃²` with
`I` acting through a copy of `S₃` by `σ ↦ [[1,1],[0,1]]` and
`τ ↦ diag(−1,1)` one has `A^I = 0` while EVERY single element fixes a
nonzero vector — so no derivation of the parent from
`(M⁰)^{I₃} = 0` alone can exist. This leaf is refuted by that
configuration too, and correctly so: `S₃` is NOT cyclic. What rules the
configuration out over `ℤ₃` is exactly what this leaf asserts —
`[[1,1],[0,1]]` has order `3`, so that image is wildly ramified, which
`e = 1 < p − 1` forbids. Any proof of this leaf must therefore spend
`e < p − 1`; a proof that does not is wrong. That obligation now lands
squarely on `wildInertia_fixes_connected_threeTorsion_of_hopf_package`,
which is where the assembly below draws its only finite-flat input;
the assembly itself spends none of it and is correspondingly unable to
manufacture it.

CHECKS THAT WOULD REFUTE THE OBSTRUCTION RECORD, BOTH RE-RUN 2026-07-27
(state them, do not just believe them): (i) exhibit a derivation of the
conclusion from `(M⁰)^{I₃} = 0` alone — it must contend with the `S₃`
configuration, and the decomposition below does NOT attempt one: it
takes tameness as an explicit leaf; (ii) find a Cartier-duality
development in the tree transporting the proven "no unramified sub"
half to this one — **CHECK (ii) HAS NOW FIRED (2026-07-27, at
integration): the earlier sentence here, that the grep "still matches
only docstrings", is STALE.**
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean` builds Cartier
duality for finite flat commutative group schemes, sorry-free, and
`.../HopfAlgebra/ShortExact.lean` adds its functoriality
(`CartierDual.map`) plus the short-exactness definition
(`HopfAlgebra.IsShortExact`) the transport needs.  The duality route is
therefore no longer ABSENT; it is available in principle, and the whole
cluster is now IN THE ROOT IMPORT CONE (wired in at `1492cecb` through
`HardlyRamified/Family.lean`, which `public import`s `ShortExact` and
`CartierDualExamples`) — until then those five modules were never
compiled at all, so nothing in this paragraph had ever been checked by
the compiler.

RE-CHECKED 2026-07-27 AFTER THE WIRING, and the "ONE named open leaf"
count above is STALE in two ways.  `HopfAlgebra.IsShortExact.cartierDual`
is itself **PROVEN** (`ShortExact.lean:669`), as a four-field assembly;
what is open is THREE sub-leaves it consumes, none of them owned:

* `HopfAlgebra.IsShortExact.exists_linearRetraction` (`ShortExact.lean:564`)
  — the normal-basis splitting; `surjective_cartierDual_map` is proven from it;
* `HopfAlgebra.IsShortExact.ker_cartierDual_le` (`ShortExact.lean:628`)
  — the hard half of the dual kernel condition (`le_ker_cartierDual` is proven);
* `HopfAlgebra.IsShortExact.faithfullyFlat_cartierDual` (`ShortExact.lean:648`)
  — the deepest, classically `Ext¹(G'', 𝔾ₘ) = 0`.

Plus `Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation`
(`ShortExact.lean:238`), which `etale_of_isShortExact` consumes.  If they land
it would most likely close
`wildInertia_fixes_connected_threeTorsion_of_hopf_package` directly,
since the duality argument for the connected case is written out there.
Re-run `python3 flt-frontier.py | grep -A6 HopfAlgebra/ShortExact` before
believing this list; it is a dated claim like every other one here.

`hprim₀`: KEEP IT, BUT THE INHERITED JUSTIFICATION WAS WRONG (corrected
2026-07-27 while proving this leaf). The previous version of this
paragraph read "`hprim₀` IS ESSENTIAL — WITHOUT IT THE STATEMENT IS
FALSE" and offered the constant group scheme `G = ℤ/3` with `e₀ = 1` as
the witness — but it then conceded in the same sentence that "the
conclusion holds vacuously for that `G`", which is precisely NOT a
refutation. The witness refutes the PARENT
(`exists_localInertia_no_fixed_connected_vector_of_hopf_package`, where
`M` unramified makes fixed-point-freeness impossible), and it was
copied down to this leaf where fixed-locus CONTAINMENT survives it
untouched. Nothing in the cut is affected — `hprim₀` is genuinely
consumed here, since it is passed straight through to the Raynaud leaf
`wildInertia_fixes_connected_threeTorsion_of_hopf_package`, whose OWN
docstring carries the real reason connectedness cannot be dropped (good
ORDINARY reduction at `3`). So: do not drop or underscore `hprim₀`, and
do not reinstate the refuted justification for it.

FAITHFULNESS. The conclusion is a VALUE-level statement about vectors,
both quantifiers `σ, τ ∈ localInertiaGroup 𝔭₃` are over INERTIA and
neither is widened to `Γ`, and no element of `G`, no coordinate and no
normal form appears. So the leaf is on the true side of the
development's `𝒪ᵥ`-descent rule and blind to the `p − 1` unramified
twists `μ₃ ⊗ ψ` that killed `exists_muType_closure`: a twist changes
WHICH vectors are connected, not whether one inertia element's fixed
locus contains the others'.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5 and 3.4.3; Serre, *Propriétés galoisiennes…*,
Invent. Math. 15 (1972), §1.11 (fundamental characters and the
procyclic tame quotient); Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG) :
    ∃ σ ∈ localInertiaGroup 𝔭₃, ∀ τ ∈ localInertiaGroup 𝔭₃, ∀ w : N,
      (3 : ℕ) • w = 0 →
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm w))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (ρ'.toLocal 𝔭₃) σ w = w → (ρ'.toLocal 𝔭₃) τ w = w := by
  classical
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : N, fG (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
  -- the connected locus
  set C : Set N := {x : N |
    (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1} with hC
  have hCzero : (0 : N) ∈ C := by
    show (Additive.toMul (g.symm (0 : N))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  have hCadd : ∀ x y : N, x ∈ C → y ∈ C → x + y ∈ C := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    show (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- every inertia displacement is connected …
  have hCdisp : ∀ τ ∈ localInertiaGroup 𝔭₃, ∀ y : N,
      (ρ'.toLocal 𝔭₃) τ y - y ∈ C := fun τ hτ y =>
    inertia_displacement_apply_connected_idempotent_eq_one ρ' G e₀ he₀ hε₀ fG hfG
      τ hτ y
  -- … hence the connected locus is INERTIA-STABLE, since
  -- `ρ'(τ) x = (ρ'(τ) x − x) + x`
  have hCstab : ∀ τ ∈ localInertiaGroup 𝔭₃, ∀ x : N, x ∈ C →
      (ρ'.toLocal 𝔭₃) τ x ∈ C := by
    intro τ hτ x hx
    have h := hCadd _ _ (hCdisp τ hτ x) hx
    rwa [sub_add_cancel] at h
  -- the geometric point set is finite, hence so is the space
  haveI : Finite (Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) :=
    inferInstanceAs (Finite (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ))
  haveI : Finite N := Finite.of_equiv _ g
  -- the connected `3`-torsion socle: a FINITE, inertia-stable set, on which
  -- the wild inertia acts trivially by the Raynaud leaf
  set S : Set N := {x : N | (3 : ℕ) • x = 0 ∧ x ∈ C} with hS
  have hSstab : ∀ (τ : localInertiaGroup 𝔭₃) (x : N), x ∈ S →
      (ρ'.toLocal 𝔭₃) (τ : Γ ℚ₃ᵥ) x ∈ S := by
    intro τ x hx
    refine ⟨?_, hCstab _ τ.2 x hx.2⟩
    rw [← map_nsmul, hx.1, map_zero]
  set act : (localInertiaGroup 𝔭₃) → S → S :=
    fun τ x => ⟨(ρ'.toLocal 𝔭₃) (τ : Γ ℚ₃ᵥ) x.1, hSstab τ x.1 x.2⟩ with hact
  have hone : ∀ x : S, act 1 x = x := by
    intro x
    apply Subtype.ext
    show (ρ'.toLocal 𝔭₃) ((1 : localInertiaGroup 𝔭₃) : Γ ℚ₃ᵥ) x.1 = x.1
    rw [OneMemClass.coe_one, map_one]
    rfl
  have hmul : ∀ (a b : localInertiaGroup 𝔭₃) (x : S),
      act (a * b) x = act a (act b x) := by
    intro a b x
    apply Subtype.ext
    show (ρ'.toLocal 𝔭₃) ((a * b : localInertiaGroup 𝔭₃) : Γ ℚ₃ᵥ) x.1
        = (ρ'.toLocal 𝔭₃) (a : Γ ℚ₃ᵥ) ((ρ'.toLocal 𝔭₃) (b : Γ ℚ₃ᵥ) x.1)
    rw [Subgroup.coe_mul, map_mul]
    rfl
  have hwild : ∀ π : localInertiaGroup 𝔭₃,
      (π : Γ ℚ₃ᵥ) ∈ wildInertiaGroup 𝔭₃ → ∀ x : S, act π x = x := by
    intro π hπ x
    apply Subtype.ext
    exact wildInertia_fixes_connected_threeTorsion_of_hopf_package ρ' G e₀ he₀ hε₀
      hprim₀ hcomul₀ fG hfG _ hπ x.1 x.2.1 x.2.2
  -- procyclicity of the tame quotient hands over the generator
  obtain ⟨σ, hgen⟩ :=
    exists_localInertia_generator_of_wildInertia_trivial 𝔭₃ act hone hmul hwild
  refine ⟨(σ : Γ ℚ₃ᵥ), σ.2, ?_⟩
  intro τ hτ w hw3 hwc hwfix
  have hwS : w ∈ S := ⟨hw3, hwc⟩
  obtain ⟨n, hn⟩ := hgen ⟨τ, hτ⟩
  have hfixS : act σ ⟨w, hwS⟩ = ⟨w, hwS⟩ := Subtype.ext hwfix
  have hiter : (act σ)^[n] ⟨w, hwS⟩ = ⟨w, hwS⟩ :=
    Function.iterate_fixed hfixS n
  have hfin := hn ⟨w, hwS⟩
  rw [hiter] at hfin
  exact congrArg Subtype.val hfin

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud at `e = 1 < p − 1`: a SINGLE inertia element already
detects the connected part** (PROVEN 2026-07-27 over the two leaves
`connected_vector_threePow_torsion_of_hopf_package` and
`exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
just above, into which it was decomposed on that date; it was itself a
SORRY LEAF, cut 2026-07-27 out of
`connected_locus_mem_displacement_closure_of_hopf_package` below, which
is PROVEN over it — and with it the whole `R`-stability chain
`connected_locus_smul_of_hopf_package_aux` /
`connected_locus_smul_of_hopf_package`).

Content: there is ONE `σ` in the local inertia group at `3` fixing no
nonzero CONNECTED vector — no nonzero `z` whose point takes the value
`1` at the connected counit idempotent `e₀`.

HOW THIS DIFFERS FROM THE PROVEN HALF, AND WHERE THE DIFFERENCE NOW
LIVES. `inertiaFixed_connected_vector_eq_zero_of_hopf_package` above
already says a connected vector fixed by ALL of `I₃` (and killed by a
power of `3`) vanishes, i.e. `(M⁰)^{I₃} = 0`. This statement says a
single, suitably chosen `σ` suffices — `(M⁰)^{σ} = 0` — and carries no
torsion hypothesis. Those are TWO independent gaps, and the
decomposition of 2026-07-27 separates them:

* the QUANTIFIER SWAP, "for all `σ`" inside the hypothesis to "for one
  `σ`", is the classification input and is now
  `exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
  — stated only on the `3`-torsion socle, which is where Raynaud's
  hypothesis "killed by `p`" actually holds;
* the MISSING TORSION HYPOTHESIS is now
  `connected_vector_threePow_torsion_of_hopf_package`, a pure statement
  about the ORDER of a connected vector with no ramification content
  whatever, and one whose route (Nakayama in the convolution
  filtration) is elementary.

Everything joining them is PROVEN here: closure of the connected locus
under `ℕ`-multiples, and the descending induction that pushes a
`3 ^ k`-torsion vector down to the socle, one power at a time, killing
it there with the proven all-of-`I₃` lemma. Splitting this way matters
because the two halves fail for different reasons: a nonzero connected
vector of order prime to `3` would refute the statement while every
tameness input still held.

WHAT THE CONSUMER'S PROOF CONTRIBUTES, so that this leaf is only the
finite-flat content. Write `M⁰` for the connected locus and
`d := ρ'(σ) · − ·` for the displacement map at `σ`.

* `M⁰` is closed under `0` and `+` (counit-one and comultiplication
  absorption, through `convMul_apply_one_of_comul_absorbs`), hence
  under `ℕ`-multiples.
* The geometric point set is FINITE: `Module.Finite 𝒪ᵥ G` base-changes
  to `Module.Finite ℚ₃ᵥ (ℚ₃ᵥ ⊗ G)` and mathlib's instance
  `Finite (S →ₐ[R] K)` applies; `fG` transports finiteness to the
  space. Finiteness gives `M⁰` closure under NEGATION for free
  (`-x = (addOrderOf x - 1) • x`), hence under subtraction.
* `d` maps `M⁰` INTO `M⁰`, by the proven
  `inertia_displacement_apply_connected_idempotent_eq_one`.
* `d` is INJECTIVE on `M⁰` by exactly this leaf: `d x = d y` gives
  `ρ'(σ)(x − y) = x − y` with `x − y` connected, so `x = y`.
* Injective + finite ⟹ SURJECTIVE (`Finite.injective_iff_surjective`).

So every connected `z` is a SINGLE displacement `ρ'(σ) y − y`, and the
`AddSubmonoid.closure` of the consumer collapses to `subset_closure`.
Note this is strictly stronger than the consumer needs, and it is what
makes the reduction cheap: no sum, no closure induction, no coefficient
ring.

PROOF (what is discharged HERE, and it is all of the non-classification
content). Take `σ` from the tameness leaf. The connected locus is
closed under `0` and `+` — counit-one and comultiplication absorption,
through `convMul_apply_one_of_comul_absorbs`, exactly as in
`exists_connectedEtale_subgroup_at_three_of_threePowTorsion` above —
hence under `ℕ`-multiples. Given a connected `σ`-fixed `z`, the order
leaf supplies `k` with `3 ^ k • z = 0`, and we descend on `k`: the
vector `w := 3 ^ k • z` is again connected (`ℕ`-multiple), again
`σ`-fixed (`map_nsmul`), and is killed by `3`, so the tameness leaf
upgrades its `σ`-fixedness to fixedness by ALL of `I₃`, and the PROVEN
`inertiaFixed_connected_vector_eq_zero_of_hopf_package` (at exponent
`1`) gives `w = 0`. That is `3 ^ k • z = 0` with the exponent dropped
by one, and the induction hypothesis finishes. So no Raynaud input and
no coefficient ring enter here.

WHY `(M⁰)^{I₃} = 0` ALONE CANNOT PROVE THIS, AND WHAT DEFEATS THE
COUNTEREXAMPLE. For `A = 𝔽₃²` with `I` acting through a copy of `S₃` by
`σ ↦ [[1,1],[0,1]]` and `τ ↦ diag(−1,1)` one has `A^I = 0` while EVERY
single element of that image fixes a nonzero vector — so the conclusion
here fails for it, and no derivation from the proven half alone can
exist. What rules it out over `ℤ₃` is TAMENESS: the unipotent
`[[1,1],[0,1]]` has order `3`, so that image is wildly ramified, which
`e = 1 < p − 1` forbids. That obstruction, the refuting checks it
comes with, and the `S₃` configuration are now recorded on
`exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package`
above, which is the declaration that must spend `e < p − 1`; the
assembly here spends none of it and is correspondingly unable to
manufacture it.

CHECKS THAT WOULD REFUTE THIS OBSTRUCTION RECORD (state them, do not
just believe them): (i) exhibit a derivation of `(M⁰)^{σ} = 0` for some
single `σ` from `(M⁰)^{I₃} = 0` alone — it must contend with the `S₃`
configuration above; (ii) find a Cartier-duality development in the
tree transporting the proven "no unramified sub" half to this one —
**THIS CHECK HAS NOW FIRED (2026-07-27) and the sentence it replaces was
stale: the grep no longer returns nothing.**
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean` builds Cartier
duality for finite flat commutative group schemes, sorry-free, and
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` adds its
functoriality (`CartierDual.map`) together with the definition of a short
exact sequence (`HopfAlgebra.IsShortExact`) that the transport needs. So the
duality route is no longer ABSENT; and since `1492cecb` the whole cluster is
in the ROOT IMPORT CONE, wired in through `HardlyRamified/Family.lean` — before
that those five modules were never compiled, so no claim made about them here
had ever been checked by the compiler.

RE-CHECKED 2026-07-27 AFTER THE WIRING: the "ONE named open leaf" count this
paragraph used to carry is STALE.  `HopfAlgebra.IsShortExact.cartierDual` is
itself PROVEN (`ShortExact.lean:669`) as a four-field assembly; what is open
is three unowned sub-leaves it consumes —
`IsShortExact.exists_linearRetraction` (`ShortExact.lean:564`),
`IsShortExact.ker_cartierDual_le` (`:628`) and
`IsShortExact.faithfullyFlat_cartierDual` (`:648`) — together with
`Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation`
(`:238`), which `etale_of_isShortExact` consumes.  That is still a different —
and much smaller — obstruction than the one recorded here, and the next owner
of this leaf should weigh it afresh rather than treating the duality route as
nonexistent.  Re-run
`python3 flt-frontier.py | grep -A6 HopfAlgebra/ShortExact` before believing
the list; it is a dated claim like every other one here.

`hprim₀` IS ESSENTIAL — WITHOUT IT THE STATEMENT IS FALSE. The
idempotent `e₀ = 1` satisfies `he₀`, `hε₀` and `hcomul₀` and makes the
"connected locus" all of `M`; for the CONSTANT group scheme
`G = ℤ/3` over `𝒪ᵥ` the module `M` is unramified, so EVERY `σ ∈ I₃`
fixes EVERY vector and no `σ` can satisfy the conclusion. Primitivity
of `e₀` — supplied by consumers as minimality, through
`mul_eq_zero_or_mul_eq_of_minimal` — is what pins `e₀ G` as the
connected component of the identity and makes the leaf true. Do not
drop or underscore it.

FAITHFULNESS. The conclusion is a VALUE-level statement about vectors:
the quantifier `σ ∈ localInertiaGroup 𝔭₃` is over INERTIA and is not
widened to `Γ`, and no element of `G`, no coordinate and no normal form
appears. So the leaf is on the true side of the development's
`𝒪ᵥ`-descent rule and blind to the `p − 1` unramified twists `μ₃ ⊗ ψ`
that killed `exists_muType_closure`: a twist changes WHICH vectors are
connected, not whether one inertia element moves all of them.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5 and 3.4.3; Tate, *Finite flat group schemes*, §4,
in Cornell–Silverman–Stevens; Fontaine, *Il n'y a pas de variété
abélienne sur `ℤ`*, §1. -/
theorem exists_localInertia_no_fixed_connected_vector_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG) :
    ∃ σ ∈ localInertiaGroup 𝔭₃, ∀ z : N,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm z))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (ρ'.toLocal 𝔭₃) σ z = z → z = 0 := by
  classical
  set g := Equiv.ofBijective fG hfG
  have hfs : ∀ x : N, fG (g.symm x) = x :=
    fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N,
      g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
  -- the connected locus contains `0` …
  have hPzero : (Additive.toMul (g.symm (0 : N)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- … and is closed under addition …
  have hPadd : ∀ x y : N,
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm y)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- … hence under natural multiples
  have hPnsmul : ∀ (j : ℕ) (x : N),
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (j • x))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro j x hx
    induction j with
    | zero => rw [zero_nsmul]; exact hPzero
    | succ j ih => rw [succ_nsmul]; exact hPadd _ _ ih hx
  obtain ⟨σ, hσ, hgen⟩ :=
    exists_localInertia_generates_on_connected_threeTorsion_of_hopf_package
      ρ' G e₀ he₀ hε₀ hprim₀ hcomul₀ fG hfG
  refine ⟨σ, hσ, ?_⟩
  -- descending induction on the `3`-power exponent: each step pushes the
  -- vector one power closer to the socle, where the tameness leaf turns
  -- `σ`-fixedness into fixedness by all of `I₃` and the proven
  -- all-of-`I₃` lemma kills it
  have key : ∀ (k : ℕ) (x : N),
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (ρ'.toLocal 𝔭₃) σ x = x → (3 ^ k : ℕ) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x _ _ hx
      rwa [pow_zero, one_smul] at hx
    | succ k ih =>
      intro x hxconn hxfix hx
      have hstep : (3 : ℕ) • ((3 ^ k : ℕ) • x) = 0 := by
        rw [smul_smul, show (3 : ℕ) * 3 ^ k = 3 ^ (k + 1) by ring]
        exact hx
      have hwconn : (Additive.toMul (g.symm ((3 ^ k : ℕ) • x)))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := hPnsmul _ _ hxconn
      have hwfix : (ρ'.toLocal 𝔭₃) σ ((3 ^ k : ℕ) • x) = (3 ^ k : ℕ) • x := by
        rw [map_nsmul, hxfix]
      have hwall : ∀ τ ∈ localInertiaGroup 𝔭₃,
          (ρ'.toLocal 𝔭₃) τ ((3 ^ k : ℕ) • x) = (3 ^ k : ℕ) • x :=
        fun τ hτ => hgen τ hτ _ hstep hwconn hwfix
      have hw0 : (3 ^ k : ℕ) • x = 0 :=
        inertiaFixed_connected_vector_eq_zero_of_hopf_package ρ' G e₀ he₀ hε₀
          hprim₀ hcomul₀ fG hfG 1 _ (by rwa [pow_one]) hwconn hwall
      exact ih x hxconn hxfix hw0
  intro z hzconn hzfix
  obtain ⟨k, hk⟩ :=
    connected_vector_threePow_torsion_of_hopf_package ρ' G e₀ he₀ hε₀ hprim₀
      hcomul₀ fG hfG z hzconn
  exact key k z hzconn hzfix hk

/-- **Raynaud at `e = 1 < p − 1`: the connected locus is GENERATED BY
INERTIA DISPLACEMENTS** (PROVEN 2026-07-27 over the single leaf
`exists_localInertia_no_fixed_connected_vector_of_hopf_package` above;
was itself a SORRY LEAF, cut 2026-07-27 out of
`connected_locus_smul_of_hopf_package` below, which is PROVEN over it
through the abstract-coefficient glue
`connected_locus_smul_of_hopf_package_aux`).

Content: every CONNECTED point — every `z` whose point takes the value
`1` at the connected counit idempotent `e₀` — lies in the additive
submonoid generated by the inertia displacements `ρ'(σ) y − y`, for
`σ` in the local inertia group at `3` and `y` arbitrary.

The reverse inclusion is already PROVEN:
`inertia_displacement_apply_connected_idempotent_eq_one` above says
every displacement is connected, and the connected locus is closed
under `0` and `+` (the `hPzero`/`hPadd` steps of
`exists_connectedEtale_subgroup_at_three_of_threePowTorsion` above,
re-performed in the glue). So this leaf is exactly the EQUALITY
`M⁰ = ⟨displacements⟩`, stated in the only direction a consumer needs.

WHY THIS IS THE RIGHT CUT — IT REMOVES THE COEFFICIENT RING ENTIRELY.
`M/⟨displacements⟩` is the maximal UNRAMIFIED quotient of `M`, so the
statement says exactly: *the connected part has no nonzero unramified
quotient*. That is a pure `Γ ℚ₃ᵥ`-module assertion about a single
subgroup — no `R`, no module structure, no functoriality, no morphisms
of schemes anywhere. Its consumer's `R`-stability is then FORMAL,
because the displacement submonoid is automatically stable under any
endomorphism commuting with the Galois action:
`a • (ρ'(σ) y − y) = ρ'(σ) (a • y) − a • y` is again a displacement.
Full faithfulness is therefore spent here and only here, and in the
shape "connected ⟹ no unramified quotient" rather than the much
heavier "every `Γ`-endomorphism of the generic fibre extends to the
model".

PROOF — THE STATEMENT COLLAPSES TO A SINGLE DISPLACEMENT. Everything
below is formal once the leaf above supplies one inertia element `σ`
fixing no nonzero connected vector. The displacement map
`d := ρ'(σ) · − ·` sends the connected locus `M⁰` INTO `M⁰`
(`inertia_displacement_apply_connected_idempotent_eq_one` above), and
it is INJECTIVE there: `d x = d y` gives `ρ'(σ)(x − y) = x − y` with
`x − y` connected — `M⁰` is closed under `0`, `+`, `ℕ`-multiples and,
because the geometric point set is FINITE, under negation
(`-x = (addOrderOf x - 1) • x`) — so the leaf forces `x = y`.
Finiteness comes for free: `Module.Finite 𝒪ᵥ G` base-changes to
`Module.Finite ℚ₃ᵥ (ℚ₃ᵥ ⊗ G)`, mathlib's instance
`Finite (S →ₐ[R] K)` applies, and `fG` transports it to the space.
Injective plus finite gives SURJECTIVE
(`Finite.injective_iff_surjective`), so each connected `z` is a SINGLE
displacement `ρ'(σ) y − y` and `AddSubmonoid.subset_closure` finishes.
No sum, no closure induction, and no coefficient ring enter.

`hprim₀` IS ESSENTIAL — WITHOUT IT THE STATEMENT IS FALSE, and the
witness is the same one recorded on the leaf above: `e₀ = 1` satisfies
`he₀`, `hε₀` and `hcomul₀`, and makes the "connected locus" all of `M`;
for the CONSTANT group scheme `G = ℤ/3` over `𝒪ᵥ` the module `M` is
unramified, so every displacement vanishes and the displacement
submonoid is `0 ⊊ M`. Primitivity of `e₀` — supplied by consumers as
minimality, through `mul_eq_zero_or_mul_eq_of_minimal` — is what pins
`e₀ G` as the connected component of the identity. It reaches the proof
below through the leaf, which is where the `S₃` counterexample, the
`ω`-isotypy discussion, the refuting checks and the Raynaud route are
now recorded.

FAITHFULNESS. The conclusion is a VALUE-level membership: the vector
whose point takes the value `1` at the `𝒪ᵥ`-rational idempotent `e₀`
is a sum of inertia displacements OF VECTORS. No element of `G`, no
coordinate, no normal form, and no `Γ`-wide rationality appears
anywhere, and the quantifier `σ ∈ localInertiaGroup 𝔭₃` is over
INERTIA and is not widened to `Γ`. So the leaf is on the true side of
the development's `𝒪ᵥ`-descent rule and blind to the `p − 1`
unramified twists `μ₃ ⊗ ψ` that killed `exists_muType_closure`: a twist
changes WHICH vectors the displacements are, not whether they span the
connected locus.

Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.2–3.3.5; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens; Fontaine, *Il n'y a pas de variété abélienne
sur `ℤ`*, §1. -/
theorem connected_locus_mem_displacement_closure_of_hopf_package
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (z : N)
    (hz : (Additive.toMul ((Equiv.ofBijective fG hfG).symm z))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    z ∈ AddSubmonoid.closure
      {d : N | ∃ σ ∈ localInertiaGroup 𝔭₃, ∃ y : N,
        d = (ρ'.toLocal 𝔭₃) σ y - y} := by
  classical
  obtain ⟨σ, hσ, hfix⟩ :=
    exists_localInertia_no_fixed_connected_vector_of_hopf_package
      ρ' G e₀ he₀ hε₀ hprim₀ hcomul₀ fG hfG
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : N, fG (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
    rfl
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
    rfl
  -- the connected locus
  set C : Set N := {x : N |
    (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1} with hC
  have hCzero : (0 : N) ∈ C := by
    show (Additive.toMul (g.symm (0 : N))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  have hCadd : ∀ x y : N, x ∈ C → y ∈ C → x + y ∈ C := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    show (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- every inertia displacement is connected
  have hCdisp : ∀ τ ∈ localInertiaGroup 𝔭₃, ∀ y : N,
      (ρ'.toLocal 𝔭₃) τ y - y ∈ C := fun τ hτ y =>
    inertia_displacement_apply_connected_idempotent_eq_one ρ' G e₀ he₀ hε₀ fG hfG
      τ hτ y
  -- the geometric point set is finite, hence so is the space
  haveI : Finite (Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ)) :=
    inferInstanceAs (Finite (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ))
  haveI : Finite N := Finite.of_equiv _ g
  -- the connected locus is closed under `ℕ`-multiples, hence under negation
  have hCnsmul : ∀ (m : ℕ) (x : N), x ∈ C → m • x ∈ C := by
    intro m x hx
    induction m with
    | zero => simpa using hCzero
    | succ m ih => rw [succ_nsmul]; exact hCadd _ _ ih hx
  have hCneg : ∀ x : N, x ∈ C → -x ∈ C := by
    intro x hx
    have hpos : 0 < addOrderOf x := addOrderOf_pos x
    have hz0 : addOrderOf x • x = 0 := addOrderOf_nsmul_eq_zero x
    have hsplit : (addOrderOf x - 1) • x + x = 0 := by
      rw [← succ_nsmul, Nat.sub_add_cancel hpos]
      exact hz0
    have hneg : -x = (addOrderOf x - 1) • x := by
      rw [eq_comm, ← add_eq_zero_iff_eq_neg]
      exact hsplit
    rw [hneg]
    exact hCnsmul _ _ hx
  have hCsub : ∀ x y : N, x ∈ C → y ∈ C → x - y ∈ C := by
    intro x y hx hy
    rw [sub_eq_add_neg]
    exact hCadd _ _ hx (hCneg _ hy)
  -- the displacement map is an injective self-map of the connected locus
  let F : C → C := fun x => ⟨(ρ'.toLocal 𝔭₃) σ x.1 - x.1, hCdisp σ hσ x.1⟩
  have hFinj : Function.Injective F := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have h' : (ρ'.toLocal 𝔭₃) σ x - x = (ρ'.toLocal 𝔭₃) σ y - y :=
      congrArg Subtype.val h
    have hd : (ρ'.toLocal 𝔭₃) σ (x - y) = x - y := by
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp h'
    exact Subtype.ext (sub_eq_zero.mp (hfix (x - y) (hCsub x y hx hy) hd))
  -- hence surjective, so `z` is a SINGLE displacement
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hFinj ⟨z, hz⟩
  exact AddSubmonoid.subset_closure ⟨σ, hσ, y.1, (congrArg Subtype.val hy).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected locus is stable under the coefficient ring**
(PROVEN 2026-07-27 over the single leaf
`connected_locus_mem_displacement_closure_of_hopf_package` above) — the
abstract-coefficient form of `connected_locus_smul_of_hopf_package`
below, which is its instance at
`A := R ⧸ 𝔪ⁿ⁺²`, `N := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V`.

It is stated over an ARBITRARY coefficient ring `A` and module `N`
deliberately, for the reason recorded in the fleet doctrine: `GaloisRep`
and its FunLike hide a `moduleTopology A (Module.End A N)`, which stays
opaque at an abstract `N` and gets unfolded at a concrete one, so the
concrete form costs tens of seconds per step where the abstract form
costs nothing. Everything below is formal.

PROOF. Write `M⁰` for the connected locus and `P` for the additive
submonoid generated by the inertia displacements `ρ'(σ) y − y`.

* `P ⊆ M⁰`: each generator is connected
  (`inertia_displacement_apply_connected_idempotent_eq_one` above), and
  `M⁰` contains `0` and is closed under `+` — the counit-one and
  comultiplication-absorption steps, through
  `convMul_apply_one_of_comul_absorbs`, exactly as in
  `exists_connectedEtale_subgroup_at_three_of_threePowTorsion` above.
  Closure induction then covers all of `P`.
* `P` is `A`-stable: `a • (ρ'(σ) y − y) = ρ'(σ) (a • y) − a • y`
  because `ρ'(σ)` is `A`-linear, so a scalar multiple of a displacement
  is again a DISPLACEMENT, not merely a combination of them — which is
  why the additive submonoid needs no `A`-span to be a submodule.
* `M⁰ ⊆ P` is the leaf.

Composing the three gives `a • M⁰ ⊆ a • P ⊆ P ⊆ M⁰`. Note the middle
step is where full faithfulness WOULD have been spent in the naive
route ("multiplication by `a` extends to an endomorphism of the model,
which preserves the connected component"); here it costs nothing,
because the leaf has already paid for it in a coefficient-free form. -/
theorem connected_locus_smul_of_hopf_package_aux
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (ρ' : GaloisRep ℚ A N)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      ((ρ'.toLocal 𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (a : A) (z : N)
    (hz : (Additive.toMul ((Equiv.ofBijective fG hfG).symm z))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    (Additive.toMul ((Equiv.ofBijective fG hfG).symm (a • z)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
  classical
  set g := Equiv.ofBijective fG hfG with hg
  have hfs : ∀ x : N, fG (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgs_add : ∀ x y : N, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    apply g.injective
    show fG (g.symm (x + y)) = fG (g.symm x + g.symm y)
    rw [map_add fG, hfs, hfs, hfs]
  have hgs_zero : g.symm (0 : N) = 0 := by
    apply g.injective
    show fG (g.symm (0 : N)) = fG 0
    rw [map_zero fG, hfs]
  -- the connected locus contains `0`
  have hPzero : (Additive.toMul (g.symm (0 : N)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    rw [hgs_zero, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- and is closed under addition
  have hPadd : ∀ x y : N,
      (Additive.toMul (g.symm x)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm y)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (g.symm (x + y))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x y hx hy
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm x)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul (g.symm y)) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    rw [hgs_add, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  -- every element of the displacement submonoid is connected
  have hPclosure : ∀ z' ∈ AddSubmonoid.closure
      {d : N | ∃ σ ∈ localInertiaGroup 𝔭₃, ∃ y : N,
        d = (ρ'.toLocal 𝔭₃) σ y - y},
      (Additive.toMul (g.symm z')) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro z' hz'
    refine AddSubmonoid.closure_induction ?_ hPzero
      (fun x y _ _ hx hy => hPadd x y hx hy) hz'
    rintro d ⟨σ, hσ, y, rfl⟩
    exact inertia_displacement_apply_connected_idempotent_eq_one ρ' G e₀ he₀ hε₀
      fG hfG σ hσ y
  -- the displacement submonoid is stable under the `A`-action, because a
  -- scalar multiple of a displacement is again a DISPLACEMENT
  have hPsmul : ∀ z' ∈ AddSubmonoid.closure
      {d : N | ∃ σ ∈ localInertiaGroup 𝔭₃, ∃ y : N,
        d = (ρ'.toLocal 𝔭₃) σ y - y},
      a • z' ∈ AddSubmonoid.closure
        {d : N | ∃ σ ∈ localInertiaGroup 𝔭₃, ∃ y : N,
          d = (ρ'.toLocal 𝔭₃) σ y - y} := by
    intro z' hz'
    refine AddSubmonoid.closure_induction ?_ ?_ ?_ hz'
    · rintro d ⟨σ, hσ, y, rfl⟩
      refine AddSubmonoid.subset_closure ⟨σ, hσ, a • y, ?_⟩
      rw [smul_sub, map_smul]
    · rw [smul_zero]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [smul_add]
      exact add_mem hx hy
  exact hPclosure _ (hPsmul _
    (connected_locus_mem_displacement_closure_of_hopf_package ρ' G e₀ he₀ hε₀
      hprim₀ hcomul₀ fG hfG z hz))

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud full faithfulness at `e = 1 < p − 1`: the connected locus
is an `R`-SUBMODULE** (PROVEN 2026-07-27 over the single leaf
`connected_locus_mem_displacement_closure_of_hopf_package` above,
through the abstract-coefficient glue
`connected_locus_smul_of_hopf_package_aux`; was itself a SORRY LEAF,
cut 2026-07-26 out of `exists_connected_line_of_hopf_package` below,
which is PROVEN over this node together with its rank sibling
`connected_locus_le_line_of_hopf_package`).

WHAT THE PROOF BELOW CONTRIBUTES, so that the leaf is only the
finite-flat content. The displacement submonoid
`P := ⟨ρ'(σ) y − y : σ ∈ I₃⟩` is automatically stable under the
coefficient action, because `a • (ρ'(σ) y − y) = ρ'(σ) (a • y) − a • y`
is again a DISPLACEMENT — so no `A`-span is needed and no functoriality
of the model is invoked. Together with the PROVEN inclusion
`P ⊆ M⁰` (`inertia_displacement_apply_connected_idempotent_eq_one`
above plus closure of `M⁰` under `0`/`+`), the whole of `R`-stability
reduces to the reverse inclusion `M⁰ ⊆ P`, which is the leaf. In
particular full faithfulness is no longer needed in its functorial
form: what remains is the coefficient-free assertion that the connected
part has no nonzero unramified quotient.

Content: if the point of `1 ⊗ x` takes the value `1` on the connected
counit idempotent `e₀`, then so does the point of `1 ⊗ (r • x)`, for
every `r : R`. Equivalently: the connected locus `M⁰ ⊆ M` — which
`exists_connectedEtale_subgroup_at_three_of_threePowTorsion` above
already exhibits as an additive SUBGROUP — is closed under the
`R`-action, hence is an `R ⧸ 𝔪ⁿ⁺²`-submodule of `M`.

ROUTE (the classical one, for orientation; the Lean proof takes the
displacement route above instead). Multiplication by `r` is an
endomorphism of the `Γ ℚ₃ᵥ`-module `M`, i.e. of the geometric points of
the generic fibre `Spec (ℚ₃ᵥ ⊗ G)`. **Raynaud's full faithfulness at
`e = 1 < p − 1 = 2`** (Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5;
Tate, *Finite flat group schemes*, §4, Cornell–Silverman–Stevens) says
the generic-fibre functor from finite flat `𝒪ᵥ`-group schemes to
`Γ ℚ₃ᵥ`-modules is FULLY FAITHFUL when the absolute ramification index
of `𝒪ᵥ ≅ ℤ₃` is `e = 1 < p − 1`; so that endomorphism extends to an
endomorphism of the model `Spec G` over `𝒪ᵥ`. A morphism of schemes
carries the connected component of the identity into the connected
component of the identity, so it preserves `M⁰`, which is exactly the
assertion. Note that `e = 1` is genuinely used: over a base with
`e ≥ p − 1` the functor is no longer full (the `p − 1` unramified
twists `μ_p ⊗ ψ` become distinguishable only over `𝒪ᵥ`, and
prolongations stop being unique), which is the same input that
`mem_span_natCast_of_inertia_invariant`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`) spends — that is the
proof to read first.

FAITHFULNESS. The conclusion is a VALUE-level identity over `𝒪ᵥ`: it
asserts that a certain point takes the value `1` at the `𝒪ᵥ`-rational
idempotent `e₀`, and never asks for an element of `G`, for a coordinate,
or for `Γ`-wide rationality. It is therefore on the true side of the
development's `𝒪ᵥ`-descent rule and blind to the unramified twists that
killed `exists_muType_closure`: a twist changes WHICH line the connected
locus is, not whether it is stable under `R`. -/
theorem connected_locus_smul_of_hopf_package
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (r : R) (x : V)
    (hx : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (r • x))))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
  classical
  -- the connected counit idempotent is primitive, and its comultiplication
  -- absorbs `e₀ ⊗ e₀` — the two forms the connected-locus block wants
  have hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀ :=
    fun y hy => mul_eq_zero_or_mul_eq_of_minimal he₀ hε₀ hmin₀ y hy
  have hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) =
      e₀ ⊗ₜ[𝒪₃ᵥ] e₀ := by
    rwa [Bialgebra.comulAlgHom_apply] at habs₀
  -- `1 ⊗ (r • x)` is the scalar multiple of `1 ⊗ x` by the image of `r` in
  -- the congruence quotient, so the abstract-coefficient form applies
  have htmul : (1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (r • x) =
      (algebraMap R (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) r) •
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x) := by
    rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
  rw [htmul]
  exact connected_locus_smul_of_hopf_package_aux
    (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
    hprim₀ hcomul₀ fG hfG _ _ hx

/-- **Cyclicity from a surjective displacement operator** (helper,
PROVEN 2026-07-27; PURE LOCAL ALGEBRA — no finite-flat input, no
`IsLocalRing`, no finiteness, no nilpotence).

Setting: `D : V →ₗ[R] V` an endomorphism, `N ⊆ V` a submodule with
`D V ⊆ N`, `I` an ideal, `p ∈ V` a vector with `N ⊆ R ∙ p + I • V`. The
hypothesis `hDsurj` says `D` is SURJECTIVE on `N` modulo `Iᵏ • V`. The
conclusion is that `N` becomes CYCLIC modulo `Iᵏ • V`, generated by the
single vector `D p`.

WHY SURJECTIVITY OF `D` ON `N` IS THE RIGHT INPUT, and why the naive
Nakayama argument it replaces is FALSE. One would like to argue: `N` has
residually one-dimensional image, so by Nakayama `N` is generated by any
residually nonzero member. That is wrong — residual one-dimensionality
controls `N ⧸ (N ∩ I • V)` whereas Nakayama needs `N ⧸ I • N`, and the
two differ. Over `A = ℤ⧸9` with `V = A²` the submodule
`N = A · (1,0) + A · (0,3)` has residual image the LINE `kk · (1,0)` and
contains the residually nonzero `(1,0)`, yet `(0,3)` is not an
`A`-multiple of `(1,0)`. That `N` is exactly `D V` for `D = [[1,0],[0,0]]`
— and `D` is NOT surjective on it (`D N = A · (1,0) ⊊ N`), which is
precisely what this hypothesis excludes.

ROUTE. Given `z ∈ N`, pick `y ∈ N` with `z ≡ D y` mod `Iᵏ • V`, and
write `y = α • p + m` with `m ∈ I • V`. Then
`D y = α • D p + D m`, and `D m ∈ I • N` because `D` carries `I • V`
into `I • (D V) ⊆ I • N` (`Submodule.map_smul''`). Hence
`N ≤ T ⊔ I • N` for `T := R ∙ (D p) ⊔ Iᵏ • ⊤`. Iterating that inclusion
gives `N ≤ T ⊔ Iʲ • N` for every `j`, and at `j = k` the tail is
absorbed: `Iᵏ • N ≤ Iᵏ • ⊤ ≤ T`. So no nilpotence of `I` and no
finite generation of `N` are needed — the `Iᵏ • ⊤` summand already
sitting in `T` is what closes the induction. -/
theorem le_span_singleton_sup_smul_pow_of_displacement_surjective
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    (I : Ideal R) (k : ℕ) (N : Submodule R V) (D : V →ₗ[R] V) (p : V)
    (hDN : ∀ y : V, D y ∈ N)
    (hNp : N ≤ Submodule.span R {p} ⊔ I • (⊤ : Submodule R V))
    (hDsurj : ∀ z ∈ N, ∃ y ∈ N,
      z - D y ∈ I ^ k • (⊤ : Submodule R V)) :
    N ≤ Submodule.span R {D p} ⊔ I ^ k • (⊤ : Submodule R V) := by
  -- `D` carries `I • ⊤` into `I • N`, because `D` lands in `N`
  have hDIN : ∀ m : V, m ∈ I • (⊤ : Submodule R V) → D m ∈ I • N := by
    intro m hm
    have h1 : D m ∈ Submodule.map D (I • (⊤ : Submodule R V)) :=
      Submodule.mem_map_of_mem hm
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl
      (Submodule.map_le_iff_le_comap.2 fun y _ => hDN y) h1
  -- the one-step inclusion `N ≤ T ⊔ I • N`
  have hstep : N ≤ (Submodule.span R {D p} ⊔ I ^ k • (⊤ : Submodule R V)) ⊔
      I • N := by
    intro z hz
    obtain ⟨y, hyN, hzy⟩ := hDsurj z hz
    obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 (hNp hyN)
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hs
    have hy : y = α • p + m := by rw [hα, hsm]
    have hDy : D y = α • D p + D m := by rw [hy, map_add, map_smul]
    have hzsplit : z = (α • D p + (z - D y)) + D m := by rw [hDy]; abel
    rw [hzsplit]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (hDIN m hm))
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton.2 ⟨α, rfl⟩))
      (Submodule.mem_sup_right hzy)
  -- iterate: `N ≤ T ⊔ Iʲ • N` for every `j`, then absorb the tail at `j = k`
  have key : ∀ j : ℕ, N ≤ (Submodule.span R {D p} ⊔
      I ^ k • (⊤ : Submodule R V)) ⊔ I ^ j • N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      have h1 : I ^ j • N ≤ I ^ j • ((Submodule.span R {D p} ⊔
          I ^ k • (⊤ : Submodule R V)) ⊔ I • N) :=
        Submodule.smul_mono le_rfl hstep
      have h2 : I ^ j • ((Submodule.span R {D p} ⊔
          I ^ k • (⊤ : Submodule R V)) ⊔ I • N) =
          I ^ j • (Submodule.span R {D p} ⊔ I ^ k • (⊤ : Submodule R V)) ⊔
          I ^ j • (I • N) := Submodule.smul_sup _ _ _
      have h3 : I ^ j • (I • N) = I ^ (j + 1) • N := by
        rw [pow_succ, Submodule.mul_smul]
      refine h1.trans ?_
      rw [h2, h3]
      exact sup_le (le_sup_of_le_left Submodule.smul_le_right) le_sup_right
  refine (key k).trans (sup_le le_rfl ?_)
  exact le_trans (Submodule.smul_mono le_rfl le_top) le_sup_right

/-- **The congruence quotient detects the `J`-adic filtration** (helper,
PROVEN 2026-07-27): the CONVERSE of
`one_tmul_quotient_eq_zero_of_mem_smul_top` above — an element of a
finite free `V` whose image `1 ⊗ u` vanishes in `(R ⧸ J) ⊗[R] V` lies in
`J • V`. Same coordinate argument as the residual
`mem_maximalIdeal_smul_top_of_one_tmul_eq_zero` above, with
`RingHom.ker (Ideal.Quotient.mk J) = J` in place of the residue-field
kernel computation, so no locality and no field is needed. -/
theorem mem_smul_top_of_one_tmul_quotient_eq_zero {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (J : Ideal R) {u : V}
    (hu : (1 : R ⧸ J) ⊗ₜ[R] u = 0) :
    u ∈ J • (⊤ : Submodule R V) := by
  classical
  let bV := Module.Free.chooseBasis R V
  have hcoord : ∀ i, bV.repr u i ∈ J := by
    intro i
    have h1 := Module.Basis.baseChange_repr_tmul (R ⧸ J) bV (1 : R ⧸ J) u i
    rw [hu] at h1
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, Algebra.smul_def,
      mul_one] at h1
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    rw [← Ideal.Quotient.algebraMap_eq]
    exact h1.symm
  have hsum : u = ∑ i, bV.repr u i • bV i := (bV.sum_repr u).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) trivial

/-- **The congruence reduction `V → (R ⧸ J) ⊗[R] V` is SURJECTIVE**
(helper, PROVEN 2026-07-27): every element of `(R ⧸ J) ⊗[R] V` is of the
form `1 ⊗ w`. A pure tensor `s ⊗ x` is `1 ⊗ (r • x)` for any lift `r` of
`s`, and sums are absorbed by `tmul_add`. This is what lets a statement
about the congruence quotient be pulled back to `V` itself. -/
theorem exists_one_tmul_quotient {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] (J : Ideal R)
    (t : (R ⧸ J) ⊗[R] V) : ∃ w : V, t = (1 : R ⧸ J) ⊗ₜ[R] w := by
  classical
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
  | tmul s x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      refine ⟨r • x, ?_⟩
      have hst : (r • (1 : R ⧸ J)) ⊗ₜ[R] x = (1 : R ⧸ J) ⊗ₜ[R] (r • x) :=
        TensorProduct.smul_tmul r 1 x
      rw [← hst, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  | add x y hx hy =>
      obtain ⟨wx, rfl⟩ := hx
      obtain ⟨wy, rfl⟩ := hy
      exact ⟨wx + wy, (TensorProduct.tmul_add _ _ _).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **A connected vector lies in every displacement-stable submodule of
`V`** (PROVEN 2026-07-27; the `V`-level transport of
`connected_locus_mem_displacement_closure_of_hopf_package` above, which
lives on `M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V`).

This is the `hclosure` half of
`exists_inertia_scalar_on_connected_locus_of_hopf_package` below, and it
carries NO finite-flat content beyond the leaf it transports: given a
submodule `W ⊆ V` that contains `𝔪ⁿ⁺² • ⊤` and every inertia
displacement `ρ(τ) w − w`, every connected `z : V` lies in `W`.

PROOF. `connected_locus_mem_displacement_closure_of_hopf_package`
applied to `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` puts `1 ⊗ z` in the additive
closure of the displacements of `M`. The reduction `q : V → M`,
`w ↦ 1 ⊗ w`, is SURJECTIVE (`exists_one_tmul_quotient` above), so every
generator of that closure is `q (ρ(τ) u − u)` — by
`GaloisRep.toLocal_apply` and `GaloisRep.baseChange_tmul` — hence lies
in `q '' W`; and `q '' W` is closed under `0` and `+`. So `1 ⊗ z = 1 ⊗ w`
for some `w ∈ W`, whence `z − w ∈ ker q = 𝔪ⁿ⁺² • ⊤ ≤ W`
(`mem_smul_top_of_one_tmul_quotient_eq_zero` above) and `z ∈ W`.

Note the hypothesis `𝔪ⁿ⁺² • ⊤ ≤ W` is exactly what pays for the kernel
of `q`, and the displacement hypothesis is what makes the generators
land in the image — neither can be dropped.

FAITHFULNESS. The conclusion is a membership in a submodule of `V`
modulo `𝔪ⁿ⁺²`, i.e. a VALUE-level statement, and the inertia quantifier
is over `localInertiaGroup 𝔭₃` throughout — it is never widened to
`Γ ℚ₃ᵥ`, and no element of `G` and no coordinate is ever produced. -/
theorem connected_locus_mem_of_displacement_stable_of_hopf_package
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (W : Submodule R V)
    (hWle : (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) ≤ W)
    (hWdisp : ∀ τ ∈ localInertiaGroup 𝔭₃, ∀ w : V,
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) τ) w - w ∈ W)
    (z : V)
    (hz : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] z)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    z ∈ W := by
  classical
  have hprim₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = 0 ∨ y * e₀ = e₀ :=
    fun y hy => mul_eq_zero_or_mul_eq_of_minimal he₀ hε₀ hmin₀ y hy
  have hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) =
      e₀ ⊗ₜ[𝒪₃ᵥ] e₀ := by
    rwa [Bialgebra.comulAlgHom_apply] at habs₀
  have hmem := connected_locus_mem_displacement_closure_of_hopf_package
    (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
    hprim₀ hcomul₀ fG hfG _ hz
  have hind : ∀ t ∈ AddSubmonoid.closure
      {d : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V |
        ∃ σ ∈ localInertiaGroup 𝔭₃,
          ∃ y : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
          d = ((ρ.baseChange
            (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃) σ y - y},
      ∃ w ∈ W, t = (1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] w := by
    intro t ht
    refine AddSubmonoid.closure_induction ?_
      ⟨0, W.zero_mem, (TensorProduct.tmul_zero _ _).symm⟩ ?_ ht
    · rintro d ⟨τ, hτ, y, rfl⟩
      obtain ⟨u, rfl⟩ := exists_one_tmul_quotient
        (IsLocalRing.maximalIdeal R ^ (n + 2)) y
      refine ⟨ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) τ) u - u,
        hWdisp τ hτ u, ?_⟩
      rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
        ← TensorProduct.tmul_sub]
    · rintro x y _ _ ⟨wx, hwx, rfl⟩ ⟨wy, hwy, rfl⟩
      exact ⟨wx + wy, W.add_mem hwx hwy, (TensorProduct.tmul_add _ _ _).symm⟩
  obtain ⟨w, hw, heq⟩ := hind _ hmem
  have hzero : (1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (z - w)
      = 0 := by
    rw [TensorProduct.tmul_sub, ← heq, sub_self]
  have hzw : z - w ∈ W :=
    hWle (mem_smul_top_of_one_tmul_quotient_eq_zero _ hzero)
  have hsplit : z = (z - w) + w := by abel
  rw [hsplit]
  exact W.add_mem hzw hw

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **FLAT IMPLIES ORDINARY at `3`: the multiplicative line `L`, the
inertia scalar on it, and the triviality of inertia on `V ⧸ L`**
(SORRY LEAF — hoisted 2026-07-27 out of the `hordinary` step of
`exists_inertia_scalar_on_connected_locus_of_hopf_package` below, which
is now PROVEN over it together with the PROVEN transport
`connected_locus_mem_of_displacement_stable_of_hopf_package` above. It
is the SOLE remaining arithmetic input of that node.)

Statement: there are a submodule `L ⊆ V` and a scalar `c : R` with

1. `ρ g₀ y ≡ c • y mod 𝔪ⁿ⁺²V` for every `y ∈ L`, where `g₀` is the image
   of the given `σ ∈ I₃` in `Γ ℚ`; and
2. `ρ τ̃ w ≡ w mod L + 𝔪ⁿ⁺²V` for every `w : V` and every `τ ∈ I₃` —
   i.e. inertia is trivial on `V ⧸ L`.

CLAUSE (2) IS NOT DECORATIVE, and dropping it makes the pair USELESS
rather than merely weaker: `L = 0` satisfies (1) with any `c`
whatsoever. It is (2) that pins `L` down, and it is (2) that the
consumer spends, through the displacement-stability transport above.

ROUTE (Wiles, *Modular elliptic curves and Fermat's Last Theorem*,
Ann. of Math. 141 (1995), ch. 1 §1, prop. 1.1; Ramakrishna, Compositio
87 (1993); Darmon–Diamond–Taylor §3). The residual package `hV`, `hρ`,
`π`, `w₀`, `v₀`, `hσω` makes `ρ̄|_{D₃}` an extension of the trivial
character by `ω` — reducible with DISTINCT characters, i.e. `3`-
DISTINGUISHED ORDINARY (`residual_twist_eq_cyclotomicCharacterModL`
above gives `a = ω`, and `hσω` says `ω ≠ 1` on `I₃`). Every congruence
quotient `ρ ⧸ 𝔪ⁿ⁺²` admits the finite flat model `G`, so FLAT IMPLIES
ORDINARY: `ρ|_{D₃}` has a free rank-`1` `R`-summand `L ⊆ V`, stable
under `D₃`, on which `D₃` acts by `χ_cyc · ε` with `ε` UNRAMIFIED, and
`D₃` acts on `V ⧸ L` by an unramified character. Restricted to INERTIA
the unramified twists disappear: the action on `L` is `χ_cyc` alone, so
`c := χ_cyc σ ∈ ℤ₃ˣ ⊆ Rˣ`, and the action on `V ⧸ L` is trivial, which
is (2).

WHY THE RESIDUAL PACKAGE MAY NOT BE DROPPED — the FALSITY AUDIT
recorded on the consumer below applies verbatim to THIS leaf, since it
is where those hypotheses are spent. Without them, `E ⧸ ℚ` with GOOD
SUPERSINGULAR reduction at `3` (`3 ∣ a₃`), `R = ℤ₃`, `V = T₃E`, `n = 0`
satisfies every remaining hypothesis, and `I₃` acts on `E[3]` through
the level-`2` fundamental characters of `𝔽₉ˣ` (Serre, Invent. Math. 15
(1972), §1.11 prop. 12) — a nonsplit Cartan, so NO line is stable and
no `L` exists. `3`-distinguished ordinariness is precisely what
excludes it. Compare `OortTate.exists_muType_coordinate`'s `hstab`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`), whose docstring records
the same counterexample against the same missing hypothesis; producing
`hstab` out of the residual package is the crux here.

FAITHFULNESS. Both clauses are VALUE-level congruences in `V`, and both
inertia quantifiers range over `localInertiaGroup 𝔭₃` only — NEVER over
`Γ ℚ₃ᵥ`. That is not a weakening but the true form: over the full
decomposition group the connected character is `χ_cyc · ε` with `ε` an
unramified twist, and clause (2) is outright FALSE for `τ` a Frobenius
lift whenever the étale quotient's unramified character is nontrivial.
No element of `G`, no coordinate and no `Γ`-wide rationality is asked
for, so the leaf is on the true side of the `𝒪ᵥ`-descent rule and blind
to the `p − 1` unramified twists `μ₃ ⊗ ψ` that killed
`exists_muType_closure`.

**The check that would refute it**: exhibit a `3`-distinguished ordinary
residual `ρ̄` admitting a finite flat lift whose connected part is not of
multiplicative type. Flat-implies-ordinary says there is none; such a
curve would refute Wiles ch. 1 prop. 1.1. -/
theorem exists_ordinary_line_of_flat_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (σ : Γ ℚ₃ᵥ) (hσ : σ ∈ localInertiaGroup 𝔭₃)
    (hσω : cyclotomicCharacterModL 3
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) ≠ 1) :
    ∃ (L : Submodule R V) (c : R),
      (∀ y ∈ L,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) y - c • y ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) ∧
      (∀ τ ∈ localInertiaGroup 𝔭₃, ∀ w : V,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) τ) w - w ∈
          L ⊔ (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local inertia acts on the connected locus by a SCALAR** (cut
2026-07-27 out of
`connected_locus_displacement_surjective_of_hopf_package` just below,
which is PROVEN over it. **REFUTED IN ITS FIRST FORM AND RESTATED
2026-07-27** — see the FALSITY AUDIT below; the conclusion is unchanged,
the hypothesis list is not.

**DECOMPOSED 2026-07-27 (flt-lean-65): the two sorried `have`s are gone,
and ONE of them is now PROVEN.** What were `hordinary` and `hclosure`
are now the two named top-level declarations above, and this node is
pure glue over them:

* `exists_ordinary_line_of_flat_hopf_package` — flat-implies-ordinary,
  the SOLE remaining leaf of this cluster;
* `connected_locus_mem_of_displacement_stable_of_hopf_package` —
  **PROVEN**, the `V`-level transport of
  `connected_locus_mem_displacement_closure_of_hopf_package`, together
  with its two new helpers `mem_smul_top_of_one_tmul_quotient_eq_zero`
  and `exists_one_tmul_quotient`.)

For `σ ∈ I₃` with image `g₀` in `Γ ℚ` there is a SINGLE scalar `c : R`
such that `ρ g₀` acts on the WHOLE connected locus as multiplication by
`c`, modulo `𝔪ⁿ⁺²V`.

**NOTHING IS CLAIMED ABOUT `c`** — in particular the statement does NOT
say `c ≡ ω σ` residually, and it does NOT say `c − 1` is a unit. Those
are DERIVED in the consumer below out of the residual matrix entries
(`exists_residual_matrix_entries` and
`residual_twist_eq_cyclotomicCharacterModL` above), by evaluating the
scalar action on the connected vector `p := ρ g₀ w₀ − w₀`: residually
`p ≡ (a g₀ − 1) • w₀` and `ρ g₀ p ≡ (a g₀ − 1) a g₀ • w₀`, so
`(a g₀ − 1)(a g₀ − c) • w₀ ∈ 𝔪V`; since `w₀` is residually nonzero and
`a g₀ − 1` is a unit, `c ≡ a g₀ ≡ −1 mod 𝔪`. That derivation stays in
the consumer and is untouched by the repair below: the residual data now
reappears among THIS leaf's hypotheses because the finite-flat half
needs it, not because the identification of `c` moved here.

# FALSITY AUDIT (2026-07-27) — the first form of this leaf was FALSE

The leaf was first cut as the "pure Raynaud input", carrying ONLY `ρ`,
`n`, the Hopf package `G`/`fG`/`e₀` and `σ ∈ I₃`, with `hV`, `hρ`, `kk`,
`π`, `v₀`, `w₀` and `hσω` all dropped. **In that form it is false**, and
its own docstring named the check that refutes it:

> exhibit a finite flat `ℤ₃`-group scheme with étale generic fibre whose
> connected geometric points carry a local-inertia action that is not
> scalar.

Such a scheme exists at `e = 1`. Take `E ⧸ ℚ` with GOOD SUPERSINGULAR
reduction at `3` (equivalently `3 ∣ a₃`, i.e. `a₃ ∈ {−3, 0, 3}` — an
infinite family), and put `R = ℤ₃`, `V = T₃E`, `n = 0`, so that
`M = V ⧸ 𝔪²V = E[9]`, with `G = 𝒪(E[9])` the coordinate ring of the
`9`-torsion of the abelian scheme over `ℤ₃`. Then every hypothesis of
the old form holds:

* `G` is a finite flat `𝒪₃ᵥ = ℤ₃`-Hopf algebra of rank `81` with étale
  generic fibre (characteristic `0`), and `fG` is the tautological
  Galois-equivariant bijection `E[9](ℚ̄₃) ≅ M`;
* `E` is supersingular, so `E[9]` has trivial étale quotient, `G ⊗ 𝔽₃`
  is a LOCAL ring, and `G` is `3`-torsion-free — hence `0` and `1` are
  the only idempotents of `G`. So `e₀ = 1` satisfies `he₀`, `hε₀`,
  `hmin₀` and `habs₀`, and the connected locus is ALL of `M`, since
  every `ℚ₃ᵥ`-algebra map sends `1 ↦ 1`;
* but `I₃` acts on `E[3]` through the LEVEL-2 fundamental characters
  `θ, θ³` of `𝔽₉ˣ` (Serre, *Propriétés galoisiennes des points d'ordre
  fini*, Invent. Math. 15 (1972), §1.11 prop. 12): the image of `I₃` in
  `GL(E[3])` is a nonsplit Cartan subgroup of order `8`, whose scalars
  form the subgroup of order `2`. So some `σ ∈ I₃` acts non-scalarly
  already modulo `3`, a fortiori modulo `9`.

Hence no `c` exists, and the old statement is false. The defective step
in the old ROUTE is "at `e = 1 < p − 1` the connected part `G⁰` is of
MULTIPLICATIVE type": Raynaud at `e < p − 1` gives UNIQUENESS OF
PROLONGATIONS and full faithfulness, NOT that connected implies
multiplicative. This project already records the very same
counterexample one file away — the docstring of
`OortTate.exists_muType_coordinate`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`) says of its own
one-dimensionality hypothesis `hstab`: "`hstab` is NOT redundant — for
the `p`-torsion of a supersingular elliptic curve over `ℤ_p` tame
inertia acts through the level-`2` fundamental characters, no line is
stable, no `μ_p` sits inside the model". The old form of this leaf had
no analogue of `hstab`, which is exactly what it was missing.

# THE REPAIR: the residual package is back, and it is what excludes the supersingular counterexample

`hV`, `hρ`, `kk`, `hsurj`, `π`, `hπsurj`, `hπequiv`, `v₀`, `hv₀`, `w₀`,
`hw₀π`, `hw₀ne` and `hσω` are restored. All thirteen are already in
scope at the single call site below, so the consumer's proof changes
only in its argument list.

What they buy: `hπequiv` makes the residual representation `ρ̄` an
extension of the TRIVIAL character by a character `a`; `hV` together
with `hρ` forces `det ρ̄ = ω`, hence `a = ω`
(`residual_twist_eq_cyclotomicCharacterModL` above); and `hσω` says
`ω ≠ 1` on `I₃`. So `ρ̄|_{D₃}` is reducible with DISTINCT characters —
it is `3`-DISTINGUISHED ORDINARY — whereas a supersingular `ρ̄|_{I₃}` is
irreducible. The counterexample is excluded by the very hypotheses that
were dropped.

ROUTE (corrected). `ρ̄|_{D₃}` is `3`-distinguished ordinary and every
`ρ ⧸ 𝔪ⁿ⁺²` admits the finite flat model `G`, so by FLAT IMPLIES ORDINARY
(Wiles, *Modular elliptic curves and Fermat's Last Theorem*, Ann. of
Math. 141 (1995), ch. 1 §1, prop. 1.1; Ramakrishna, Compositio 87
(1993); Darmon–Diamond–Taylor §3) the representation `ρ|_{D₃}` is
ORDINARY: there is a free rank-`1` `R`-summand `L ⊆ V`, stable under
`D₃`, on which `D₃` acts by `χ_cyc · ε` with `ε` UNRAMIFIED, and with
`D₃` acting on `V ⧸ L` by an unramified character. Restricted to
INERTIA the action on `L` is `χ_cyc` alone, so
`c := χ_cyc σ ∈ ℤ₃ˣ ⊆ Rˣ` is the scalar asked for. Finally `G⁰` is the
multiplicative part of the model and `G ⧸ G⁰` is étale, so —
prolongations being unique at `e = 1 < p − 1 = 2` — the connected locus
of `M` is exactly the image of `L`.

Those are two genuinely separate inputs, and the body below is CUT along
exactly that line. Since 2026-07-27 both are top-level declarations
above rather than sorried `have`s:

1. `exists_ordinary_line_of_flat_hopf_package` — ORDINARITY (OPEN): `∃ L : Submodule R V, ∃ c : R` with
   `ρ g₀ y − c • y ∈ 𝔪ⁿ⁺² • ⊤` for `y ∈ L`, and
   `ρ (τ̃) w − w ∈ L ⊔ 𝔪ⁿ⁺² • ⊤` for every `w : V` and every
   `τ ∈ I₃` (inertia trivial on `V ⧸ L`). This is flat-implies-ordinary
   and it is where the residual package is spent.
2. `connected_locus_mem_of_displacement_stable_of_hopf_package` —
   CONNECTED-ÉTALE (**PROVEN 2026-07-27**): every connected vector lies
   in any submodule `W` that contains `𝔪ⁿ⁺² • ⊤` and all the inertia
   displacements. Applied at `W := L ⊔ 𝔪ⁿ⁺² • ⊤` with the second clause
   of (1).

(2) is stated in that quantified form on purpose, for two
reasons. First, it makes the second clause of (1) genuinely CONSUMED
rather than decorative — and without it (2) would be FALSE, since
`L = 0` satisfies (1)'s first clause with any `c`. Second, in that form
it is not a Raynaud statement at all but a transport of
`connected_locus_mem_displacement_closure_of_hopf_package` above (which
already says a connected vector lies in the `AddSubmonoid` closure of
the inertia displacements) from `M` down to `V`, across the surjection
`x ↦ 1 ⊗ x` whose kernel is `𝔪ⁿ⁺² • ⊤` — hence the `𝔪ⁿ⁺² • ⊤ ≤ W`
hypothesis — and that is exactly how it was proven, so (1) is now the
whole of the cluster's remaining content.

The assembly itself is three lines — write `x = y + m` with `y ∈ L` and
`m ∈ 𝔪ⁿ⁺² • ⊤`, and kill the tail with `apply_mem_smul_top`.

DEGENERATE CASES ARE FINE: if `G` is étale then `M⁰ = 0` and any `c`
works; if `G` is connected then `M⁰ = M` and `c = χ_cyc σ` acts on
everything.

FAITHFULNESS. The quantifier is over `localInertiaGroup 𝔭₃` and NOT over
`Γ ℚ₃ᵥ`, deliberately: over the full decomposition group the connected
character is `χ_cyc · ε` with `ε` an unramified twist, and no single
scalar works. Inertia-only conclusions are twist-blind, which is why
this form is the true one. The conclusion is a VALUE-level congruence in
`V` modulo `𝔪ⁿ⁺²V` — never an element of `G`, never a coordinate, never
`Γ`-wide rationality — so it is on the true side of the development's
`𝒪ᵥ`-descent rule and blind to the `p − 1` unramified twists `μ₃ ⊗ ψ`
that killed `exists_muType_closure`.

WHAT IS ALREADY AVAILABLE and must NOT be re-proven here: the connected
locus is an `R`-submodule (`connected_locus_smul_of_hopf_package`
above), every inertia displacement is connected
(`inertia_displacement_apply_connected_idempotent_eq_one` above), and
`mem_span_natCast_of_inertia_invariant`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`) already spends the
`e = 1 < p − 1` input.
`OortTate.connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter`
(same file, PROVEN over `exists_muType_coordinate`) is the
multiplicative-type input in its usable form — but note it needs
`hord : φ ^ 3 = 1`, so it speaks about the `3`-TORSION of `M` only and
not about `M = V ⧸ 𝔪ⁿ⁺²V` itself, and it needs `hstab`. Producing
`hstab` out of the residual package is the crux of step (1).

**The check that would refute the REPAIRED statement**: exhibit a
`3`-distinguished ordinary residual `ρ̄` admitting a finite flat lift
whose connected part is not of multiplicative type. Flat-implies-
ordinary says there is none; such a curve would refute Wiles ch. 1
prop. 1.1.

Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Oort–Tate, *Group schemes of
prime order*; Serre, Invent. Math. 15 (1972), §1.11 prop. 12; Wiles,
Ann. of Math. 141 (1995), ch. 1 prop. 1.1; Tate, *Finite flat group
schemes*, §4, in Cornell–Silverman–Stevens. -/
theorem exists_inertia_scalar_on_connected_locus_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (σ : Γ ℚ₃ᵥ) (hσ : σ ∈ localInertiaGroup 𝔭₃)
    (hσω : cyclotomicCharacterModL 3
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) ≠ 1) :
    ∃ c : R, ∀ x : V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) x - c • x ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
  classical
  -- ## (1) FLAT IMPLIES ORDINARY (the SOLE remaining leaf,
  -- ## `exists_ordinary_line_of_flat_hopf_package` above): the multiplicative
  -- ## line `L`, the scalar `c` by which inertia acts on it, and the
  -- ## triviality of the inertia action on `V ⧸ L` that pins `L` down
  obtain ⟨L, c, hLc, hLquot⟩ := exists_ordinary_line_of_flat_hopf_package
    V hV hρ kk hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG
    e₀ he₀ hε₀ hmin₀ habs₀ σ hσ hσω
  -- ## (2) CONNECTED-ÉTALE (PROVEN,
  -- ## `connected_locus_mem_of_displacement_stable_of_hopf_package` above): a
  -- ## connected vector lies in every submodule that contains `𝔪ⁿ⁺² • ⊤` and
  -- ## all the inertia displacements — the transport of
  -- ## `connected_locus_mem_displacement_closure_of_hopf_package` from `M`
  -- ## down to `V` along `x ↦ 1 ⊗ x`
  -- ## assembly: split `x = y + m` along `L ⊔ 𝔪ⁿ⁺² • ⊤` and absorb the tail
  refine ⟨c, fun x hx => ?_⟩
  have hxmem : x ∈ L ⊔
      (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) :=
    connected_locus_mem_of_displacement_stable_of_hopf_package ρ n G fG hfG
      e₀ he₀ hε₀ hmin₀ habs₀ _ le_sup_right hLquot x hx
  obtain ⟨y, hyL, m, hm, hym⟩ := Submodule.mem_sup.1 hxmem
  have hxy : x = y + m := hym.symm
  have hmm : ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) m - c • m ∈
      (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) :=
    Submodule.sub_mem _
      (apply_mem_smul_top (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ)) hm)
      (Submodule.smul_mem _ c hm)
  have hsplit : ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) x - c • x =
      (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) y - c • y) +
      (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) m - c • m) := by
    rw [hxy, map_add, smul_add]; abel
  rw [hsplit]
  exact Submodule.add_mem _ (hLc y hyL) hmm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The inertia displacement is SURJECTIVE on the connected locus**
(PROVEN 2026-07-27 over the single leaf
`exists_inertia_scalar_on_connected_locus_of_hopf_package` just above;
was itself a SORRY LEAF, cut 2026-07-27 out of
`connected_locus_cyclic_of_hopf_package` just below, which is now PROVEN
over it together with the pure local algebra
`le_span_singleton_sup_smul_pow_of_displacement_surjective` above).

This is the ENTIRE finite-flat content of the cyclicity node. With
`σ ∈ I₃` such that `ω σ ≠ 1`, `g₀` its image in `Γ ℚ` and
`d := ρ g₀ − 1`, the assertion is that `d` maps the connected locus
`M⁰ ⊆ M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` ONTO itself: every connected `z` is
`d y` for some connected `y`, modulo `𝔪ⁿ⁺²V`.

ROUTE (Raynaud). At `e = 1 < p − 1 = 2` the connected part `G⁰` of the
finite flat `𝒪ᵥ ≅ ℤ₃`-group scheme `G` is of MULTIPLICATIVE type
(Raynaud's classification of schemes of type `(p,…,p)` together with
uniqueness of prolongations; Oort–Tate at each layer). Hence local
inertia acts on `M⁰` by a CHARACTER `χ`, so `d` acts on `M⁰` as the
scalar `χ g₀ − 1`. That scalar is a UNIT: `χ ≡ ω` residually, and
`ω g₀ ≠ 1` with `3 ∈ 𝔪` gives `χ g₀ ≡ −1`, so `χ g₀ − 1 ≡ 1 mod 𝔪`.
A unit scalar is invertible on `M⁰`, in particular surjective — which is
exactly this statement. (Only surjectivity is asked for; the consumer
does not need injectivity, and asking for less keeps the leaf smaller.)

**WHAT THE ASSEMBLY BELOW CONTRIBUTES (2026-07-27), so that the
remaining leaf is ONLY the multiplicative-type input.** The finite-flat
half is isolated in
`exists_inertia_scalar_on_connected_locus_of_hopf_package` above, which
produces a bare scalar `c` with `ρ g₀ x ≡ c • x` on the connected locus
and claims NOTHING about `c`. Everything else is written out here and is
residual linear algebra plus one division:

* `c ≡ a g₀ mod 𝔪`, hence `c − 1` is a UNIT. This is DERIVED, not
  assumed: `p := ρ g₀ w₀ − w₀` is connected
  (`inertia_displacement_apply_connected_idempotent_eq_one`) and
  residually `p ≡ (a g₀ − 1) • w₀`
  (`exists_residual_matrix_entries`), so applying the scalar action to
  `p` and comparing with `ρ g₀ p ≡ (a g₀ − 1) a g₀ • w₀` gives
  `(a g₀ − 1)(a g₀ − c) • w₀ ∈ 𝔪V`; `w₀` is residually nonzero
  (`mem_maximalIdeal_of_smul_mem_smul_top`) and `a g₀ − 1` is a unit
  (`residual_twist_eq_cyclotomicCharacterModL` gives `a g₀ ≡ −1`, and
  `three_mem_maximalIdeal` makes `−2 ≡ 1`), so `a g₀ − c ∈ 𝔪` and
  `c − 1 ≡ a g₀ − 1` is a unit;
* the witness is then simply `y := (c − 1)⁻¹ • z`, connected because the
  connected locus is an `R`-submodule
  (`connected_locus_smul_of_hopf_package` above), and
  `ρ g₀ y − y ≡ (c − 1) • y = z` by the scalar action again.

So `hV`, `hρ`, `kk`, `π`, `hπsurj`, `hπequiv`, `v₀`, `hv₀`, `w₀` and
`hσω` are all genuinely spent HERE.

CORRECTION (2026-07-27). An earlier version of this paragraph added
"and none of them is carried into the remaining leaf". That is no longer
true, and the leaf above says why: WITHOUT the residual package the
scalar statement is FALSE — the `9`-torsion of a supersingular-at-`3`
elliptic curve is connected with a non-scalar inertia action. The
residual data is therefore passed to the leaf as well; it is spent
TWICE, once here to identify `c` with `a g₀`, and once there to force
`ρ̄|_{D₃}` to be `3`-distinguished ordinary. The derivation of
`c ≡ a g₀ ≡ −1` below is unchanged, and the leaf still claims nothing
about `c`.

**WHY THIS AND NOT `M⁰ ≠ M`.** The route previously recorded on the
consumer owed only `M⁰ ≠ M`, with Nakayama finishing from any residually
nonzero member. That inference is FALSE, with an explicit counterexample
computed in the docstring of `connected_locus_cyclic_of_hopf_package`
below (`N = A·(1,0) + A·(0,3) ⊆ A²` over `A = ℤ⧸9`): the module there
satisfies `M⁰ ≠ M`, residual one-dimensionality, `(M⁰)^{I} = 0`,
inertia trivial on `M/M⁰` and surjective determinant, yet is not cyclic.
What that module FAILS is precisely the present hypothesis — for the
inertia generator `[[2,0],[0,1]]` one has `d = [[1,0],[0,0]]` and
`d N = A·(1,0) ⊊ N`. So this leaf is the sharp separator, and the
inversion is what makes the node provable: `M⁰ ≠ M` now comes out as a
BY-PRODUCT of the consumer's argument rather than being needed as input.

**The check that would refute this obstruction**: exhibit a proof of the
consumer's conclusion from the four facts its old docstring lists (`M⁰`
an `R`-submodule, `M⁰` residually inside `ker π`, `ker π` residually a
line, `(M⁰)^{I₃} = 0`) — the `ℤ⧸9` module above satisfies all four and
is not cyclic, so no such proof exists.

WHAT IS ALREADY AVAILABLE and must NOT be re-proven here: every inertia
displacement is connected
(`inertia_displacement_apply_connected_idempotent_eq_one` above, i.e.
`d M ⊆ M⁰` — the OTHER inclusion, which is the étale half and is free),
the connected locus is an `R`-submodule
(`connected_locus_smul_of_hopf_package` above, plus additivity through
`convMul_apply_one_of_comul_absorbs`), it has no nonzero inertia-fixed
vector (`exists_connectedEtale_subgroup_at_three_of_threePowTorsion`),
and `mem_span_natCast_of_inertia_invariant`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`) already spends the
`e = 1 < p − 1` input — that is the proof to read first.
`OortTate.exists_muType_coordinate` (same file, PROVEN) is the closest
existing statement of the multiplicative-type input; note its `hstab`
hypothesis (`σ • φ` is a POWER of `φ`) is the genuinely expensive part.

FAITHFULNESS. The quantifier is over `localInertiaGroup 𝔭₃` and NOT over
`Γ ℚ₃ᵥ`, deliberately: over the full decomposition group the connected
character is `ω · ψ` with `ψ` an unramified twist, and `χ g₀ − 1` need
not be a unit there. Inertia-only conclusions are twist-blind, which is
why this form is the true one. The conclusion is a VALUE-level
congruence in `V` modulo `𝔪ⁿ⁺²V` — never an element of `G`, never a
coordinate, never `Γ`-wide rationality — so it is on the true side of
the development's `𝒪ᵥ`-descent rule and blind to the `p − 1` unramified
twists `μ₃ ⊗ ψ` that killed `exists_muType_closure`.

HYPOTHESIS NOTE (settled 2026-07-27). Every hypothesis is used by the
proof below: the residual data `hV`/`hρ`/`kk`/`π`/`v₀`/`w₀` and `hσω`
are spent identifying the abstract scalar `c` of the leaf above with
`a g₀ ≡ ω g₀ ≡ −1`, which is what makes `c − 1` a unit. Nothing needs
underscore-prefixing.

Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Oort–Tate, *Group schemes of
prime order*; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem connected_locus_displacement_surjective_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (σ : Γ ℚ₃ᵥ) (hσ : σ ∈ localInertiaGroup 𝔭₃)
    (hσω : cyclotomicCharacterModL 3
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) ≠ 1)
    (z : V)
    (hz : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] z)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ y : V,
      ((Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] y)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) ∧
      z - (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) y - y) ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
  classical
  set g₀ : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ with hg₀
  -- ## the Raynaud input: inertia acts on the connected locus by a scalar `c`
  obtain ⟨c, hc⟩ := exists_inertia_scalar_on_connected_locus_of_hopf_package
    V hV hρ kk hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG
    e₀ he₀ hε₀ hmin₀ habs₀ σ hσ hσω
  rw [← hg₀] at hc
  -- ## the residual matrix entries along the `w₀`-line
  obtain ⟨a, _c₁, hac⟩ := exists_residual_matrix_entries hV kk hsurj π hπsurj
    hπequiv w₀ v₀ hw₀π hw₀ne
  have ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := fun g => (hac g).1
  -- `a g₀ ≡ −1 mod 𝔪`, hence `a g₀ − 1 ≡ 1 mod 𝔪` is a UNIT (`3 ∈ 𝔪`)
  have hαmem : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R :=
    (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne a ha g₀).2 hσω
  have hunit : IsUnit (a g₀ - 1) := by
    have h1 : (a g₀ - 1) - 1 ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (a g₀ - 1) - 1 = (a g₀ + 1) - 3 := by ring
      rw [h2]
      exact Submodule.sub_mem _ hαmem three_mem_maximalIdeal
    have h3 : a g₀ - 1 ∉ IsLocalRing.maximalIdeal R := by
      intro hmem
      have h4 := Submodule.sub_mem _ hmem h1
      simp only [sub_sub_cancel] at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h4 isUnit_one)
    exact IsLocalRing.notMem_maximalIdeal.mp h3
  -- ## `p := ρ g₀ w₀ − w₀` is CONNECTED, and residually `p ≡ (a g₀ − 1) • w₀`
  have hpconn : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
      ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (ρ g₀ w₀ - w₀))))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    have h := inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG σ hσ ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] w₀)
    rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      ← TensorProduct.tmul_sub, ← hg₀] at h
    exact h
  have hpw₀ : (ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have h1 : (ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀ = ρ g₀ w₀ - a g₀ • w₀ := by
      rw [sub_smul, one_smul]; abel
    rw [h1]
    exact ha g₀
  -- ## identify `c` residually with `a g₀`, by evaluating the scalar action
  -- ## on the connected vector `p`
  have hA : ρ g₀ (ρ g₀ w₀ - w₀) - (a g₀ - 1) • ρ g₀ w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have h := apply_mem_smul_top (ρ g₀) hpw₀
    rwa [map_sub, map_smul] at h
  have hB : (a g₀ - 1) • ρ g₀ w₀ - ((a g₀ - 1) * a g₀) • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have h := Submodule.smul_mem
      ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) (a g₀ - 1) (ha g₀)
    rwa [smul_sub, smul_smul] at h
  have hC : c • (ρ g₀ w₀ - w₀) - (c * (a g₀ - 1)) • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have h := Submodule.smul_mem
      ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V)) c hpw₀
    rwa [smul_sub, smul_smul] at h
  have hD₂ : ρ g₀ (ρ g₀ w₀ - w₀) - c • (ρ g₀ w₀ - w₀) ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) (hc _ hpconn)
  have hkey : ((a g₀ - 1) * (a g₀ - c)) • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have hid : ((a g₀ - 1) * (a g₀ - c)) • w₀ =
        (c • (ρ g₀ w₀ - w₀) - (c * (a g₀ - 1)) • w₀)
          - (ρ g₀ (ρ g₀ w₀ - w₀) - (a g₀ - 1) • ρ g₀ w₀)
          + (ρ g₀ (ρ g₀ w₀ - w₀) - c • (ρ g₀ w₀ - w₀))
          - ((a g₀ - 1) • ρ g₀ w₀ - ((a g₀ - 1) * a g₀) • w₀) := by
      have hcoef : (a g₀ - 1) * (a g₀ - c) =
          (a g₀ - 1) * a g₀ - c * (a g₀ - 1) := by ring
      rw [hcoef, sub_smul]
      abel
    rw [hid]
    exact Submodule.sub_mem _
      (Submodule.add_mem _ (Submodule.sub_mem _ hC hA) hD₂) hB
  have hprod : (a g₀ - 1) * (a g₀ - c) ∈ IsLocalRing.maximalIdeal R :=
    mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne hkey
  have hcm : a g₀ - c ∈ IsLocalRing.maximalIdeal R := by
    by_contra hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr
      (hunit.mul (IsLocalRing.notMem_maximalIdeal.mp hmem))) hprod
  have hcunit : IsUnit (c - 1) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmem => ?_
    refine (IsLocalRing.notMem_maximalIdeal.mpr hunit) ?_
    have h5 : a g₀ - 1 = (c - 1) + (a g₀ - c) := by ring
    rw [h5]
    exact Submodule.add_mem _ hmem hcm
  -- ## divide by the unit `c − 1`: the witness is `(c − 1)⁻¹ • z`
  obtain ⟨u, hu⟩ := hcunit
  have hinv : (↑u⁻¹ : R) * (c - 1) = 1 := by rw [← hu]; exact u.inv_mul
  have hyconn : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
      ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R]
        ((↑u⁻¹ : R) • z)))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 :=
    connected_locus_smul_of_hopf_package ρ n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
      (↑u⁻¹ : R) z hz
  refine ⟨(↑u⁻¹ : R) • z, hyconn, ?_⟩
  have hy1 : (c - 1) • ((↑u⁻¹ : R) • z) = z := by
    rw [smul_smul, mul_comm, hinv, one_smul]
  have heq : z - (ρ g₀ ((↑u⁻¹ : R) • z) - (↑u⁻¹ : R) • z) =
      -(((c - 1) • ((↑u⁻¹ : R) • z)) - z)
        - (ρ g₀ ((↑u⁻¹ : R) • z) - c • ((↑u⁻¹ : R) • z)) := by
    rw [sub_smul, one_smul]
    abel
  rw [heq, hy1, sub_self, neg_zero, zero_sub]
  exact Submodule.neg_mem _ (hc _ hyconn)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected locus is a CYCLIC `R`-module** (PROVEN 2026-07-27
over the single leaf
`connected_locus_displacement_surjective_of_hopf_package` above, through
the pure local algebra
`le_span_singleton_sup_smul_pow_of_displacement_surjective`; was itself
a SORRY LEAF, cut 2026-07-27 out of
`connected_locus_le_line_of_hopf_package` just below, which is PROVEN
over it).

Content: some vector `w` generates the connected locus — every connected
`x` is congruent to an `R`-multiple of `w` modulo `𝔪ⁿ⁺²V`. No claim is
made about `w` (it may vanish residually; the consumer below upgrades
any residually nonzero connected vector into a generator, which is pure
local algebra and is written out there).

**WHY THIS CUT, AND A ROUTE CORRECTION TO THE CONSUMER'S OLD DOCSTRING**
(2026-07-27). The previous route recorded on the consumer said that the
only thing owed was `M⁰ ≠ M`, after which "Nakayama over the local ring
`R` makes the submodule cyclic on any residually nonzero member". **That
last step is FALSE as stated, and the gap is exactly this leaf.**

Counterexample to the step (not to the leaf): take `A := R ⧸ 𝔪ⁿ⁺² = ℤ⧸9`,
`M := A²`, and `N := A · (1,0) + A · (0,3)`. Then `N` is an `A`-submodule
of `M`, it is PROPER (`M / N ≅ ℤ⧸3 ≠ 0`, so `M⁰ ≠ M` holds), its image
in `M ⧸ 𝔫M` is the LINE `kk · (1,0)`, and `w₁ := (1,0) ∈ N` is
residually nonzero — every hypothesis the old route quotes. Yet
`(0,3) ∈ N` is not in `A · (1,0)`, so the conclusion fails. The defect is
that residual one-dimensionality is a statement about `N ⧸ (N ∩ 𝔫M)`,
whereas Nakayama needs `N ⧸ 𝔫N`; here `N ⧸ 𝔫N` is TWO-dimensional. The
same module also survives `N^{I} = 0` and `I` acting trivially on `M/N`
(take the inertia image generated by `[[2,0],[0,1]]` and `[[2,1],[0,1]]`
over `ℤ⧸9`: their fixed submodules of `N` are `{(0,3b)}` and
`{(−3b,3b)}`, meeting in `0`), and it has surjective determinant onto
`(ℤ⧸9)ˣ`, so `hρ` does not exclude it either. **So no combination of the
facts listed as "already available" implies cyclicity**; the finite-flat
input has to be spent here.

**WHAT THE ASSEMBLY BELOW CONTRIBUTES (2026-07-27), so that the leaf is
only the finite-flat content.** Everything except the surjectivity of
`d := ρ g₀ − 1` on `M⁰` is written out here:

* `M⁰` is an `R`-SUBMODULE of `V` — `0` and `+` from
  `convMul_apply_one_of_comul_absorbs` (the same block that
  `exists_connectedEtale_subgroup_at_three_of_threePowTorsion` uses),
  scalars from `connected_locus_smul_of_hopf_package` above;
* `d V ⊆ M⁰`, from
  `inertia_displacement_apply_connected_idempotent_eq_one`;
* `M⁰ ⊆ R ∙ p + 𝔪V` for `p := d w₀`, which is the RESIDUAL rank-one
  statement and is pure residual linear algebra: `π` is `Γ ℚ`-invariant,
  so `π (1 ⊗ d y) = 0` for every `y`, and `ker π̄` is the line `kk · w̄₀`
  (the `finrank` computation from `exists_residual_matrix_entries`);
  meanwhile `p ≡ (a g₀ − 1) • w₀` with `a g₀ − 1` a UNIT
  (`residual_twist_eq_cyclotomicCharacterModL` gives `a g₀ ≡ −1`, and
  `three_mem_maximalIdeal` makes `−2 ≡ 1`), so `w₀` and `p` span the same
  residual line;
* the Nakayama iteration, in
  `le_span_singleton_sup_smul_pow_of_displacement_surjective` above.

The generator produced is `w := d (d w₀) = d p`, i.e. the SECOND inertia
displacement of `w₀` — one `d` more than the generator
`exists_connected_line_of_hopf_package` below picks, and the extra `d`
is exactly what converts "`M⁰ ⊆ R ∙ p + 𝔪V`" into "`M⁰ = R ∙ d p`" by
pushing the `𝔪V` error term into `𝔪 · M⁰`. Note the route also avoids
the direct-sum decomposition `M = M⁰ ⊕ ker d` and the freeness of `M⁰`
mentioned below: surjectivity of `d` on `M⁰` alone suffices, and no
injectivity, no projectivity and no nilpotence of `𝔪` is used.

What DOES exclude it is the Hopf package itself, and that is the content
of the leaf above: `N` here admits the quotient `(a, 3b) ↦ b̄` with TRIVIAL
inertia action, i.e. an unramified — hence étale, at `e = 1 < p − 1`,
by uniqueness of prolongations — quotient of the CONNECTED part `G⁰`,
which must be trivial. Equivalently `M⁰` is a free rank-`≤ 1`
`A`-module. The clean route to that: with `σ ∈ I₃` such that `ω σ ≠ 1`
and `d := ρ' g₀ − 1`, Raynaud's classification makes `G⁰` of
multiplicative type, so `σ` acts on `M⁰` by `χ σ` and `d` is INVERTIBLE
on `M⁰` (`χ σ − 1 ≡ ω σ − 1 ≢ 0 mod 𝔪`); since `d (M) ⊆ M⁰` always
(`inertia_displacement_apply_connected_idempotent_eq_one`), that forces
`M⁰ = d (M)` and `M = M⁰ ⊕ ker d`, so `M⁰` is a direct summand of the
free rank-`2` module `M`, hence free, of rank `1` because residually
`d̄ = [[a − 1, c], [0, 0]]` has rank exactly one in the basis `(w₀, v₀)`.
Note this route yields `M⁰ ≠ M` as a BY-PRODUCT rather than needing it
as an input.

**The check that would refute this obstruction**: exhibit a proof of the
consumer's conclusion from the four facts its old docstring lists (`M⁰`
an `R`-submodule, `M⁰` residually inside `ker π`, `ker π` residually a
line, `(M⁰)^{I₃} = 0`) — or a proof that the `ℤ⧸9` module above fails
one of them. Neither is possible: the module satisfies all four, as
computed above.

FAITHFULNESS. The conclusion is a VALUE-level congruence in `V` modulo
`𝔪ⁿ⁺²V`, never an element of `G` and never `Γ`-wide rationality of a
coordinate, so it is on the true side of the `𝒪ᵥ`-descent rule. The
hypotheses `π`/`hπequiv` are ESSENTIAL and must not be dropped in any
restatement: without a nontrivial unramified quotient character the
statement is FALSE — `G = μ₉ × μ₉` is connected, so `M⁰ = M` is free of
rank `2` and not cyclic.

Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Oort–Tate, *Group schemes of
prime order*; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem connected_locus_cyclic_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀) :
    ∃ w : V, ∀ x : V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      ∃ r : R, x - r • w ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
  classical
  -- an inertia element at `3` off the kernel of `ω`
  obtain ⟨σ, hσ, hσω⟩ := exists_localInertia_cyclotomicCharacterModL_three_ne_one
  set g₀ : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ with hg₀
  -- the residual `w₀`-line and its diagonal entry `a`
  obtain ⟨a, _c, hac⟩ := exists_residual_matrix_entries hV kk hsurj π hπsurj hπequiv
    w₀ v₀ hw₀π hw₀ne
  have ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := fun g => (hac g).1
  -- `a g₀ ≡ −1 mod 𝔪`, hence `a g₀ − 1 ≡ 1 mod 𝔪` is a UNIT (`3 ∈ 𝔪`)
  have hαmem : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R :=
    (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne a ha g₀).2 hσω
  have hunit : IsUnit (a g₀ - 1) := by
    have h1 : (a g₀ - 1) - 1 ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (a g₀ - 1) - 1 = (a g₀ + 1) - 3 := by ring
      rw [h2]
      exact Submodule.sub_mem _ hαmem three_mem_maximalIdeal
    have h3 : a g₀ - 1 ∉ IsLocalRing.maximalIdeal R := by
      intro hmem
      have h4 := Submodule.sub_mem _ hmem h1
      simp only [sub_sub_cancel] at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h4 isUnit_one)
    exact IsLocalRing.notMem_maximalIdeal.mp h3
  obtain ⟨u, hu⟩ := hunit
  -- ## the connected locus is an `R`-submodule of `V`
  have hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) =
      e₀ ⊗ₜ[𝒪₃ᵥ] e₀ := by rwa [Bialgebra.comulAlgHom_apply] at habs₀
  have hfs : ∀ zz : (((ρ.baseChange
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃).Space),
      fG ((Equiv.ofBijective fG hfG).symm zz) = zz :=
    fun zz => (Equiv.ofBijective fG hfG).apply_symm_apply zz
  have hPzero : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
      ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (0 : V))))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    have hz0 : (Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (0 : V)) = 0 := by
      apply (Equiv.ofBijective fG hfG).injective
      show fG _ = fG 0
      rw [hfs, map_zero fG, TensorProduct.tmul_zero]
    rw [hz0, toMul_zero, ← AlgHom.liftEquiv_symm_apply,
      vendored_one_eq_convOne, liftEquiv_symm_convOne]
    show algebraMap 𝒪₃ᵥ ℚ₃ᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪₃ᵥ) e₀) = 1
    rw [hε₀, map_one]
  have hPadd : ∀ x y : V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] y)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (x + y))))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro x y hx hy
    have hsplit : (Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (x + y)) =
        (Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x) +
        (Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] y) := by
      apply (Equiv.ofBijective fG hfG).injective
      show fG _ = fG _
      rw [hfs, map_add fG, hfs, hfs, TensorProduct.tmul_add]
    have hx' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x))) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hx
    have hy' : (AlgHom.liftEquiv 𝒪₃ᵥ ℚ₃ᵥ G ℚ₃ᵥᵃˡᵍ).symm
        (Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] y))) e₀ = 1 := by
      rw [AlgHom.liftEquiv_symm_apply]; exact hy
    rw [hsplit, toMul_add, ← AlgHom.liftEquiv_symm_apply,
      vendored_mul_eq_convMul, liftEquiv_symm_convMul]
    exact convMul_apply_one_of_comul_absorbs e₀ hcomul₀ _ _ hx' hy'
  obtain ⟨N, hmemN⟩ : ∃ N : Submodule R V, ∀ x : V, x ∈ N ↔
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 :=
    ⟨{ carrier := {x : V | (Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1}
       add_mem' := fun hx hy => hPadd _ _ hx hy
       zero_mem' := hPzero
       smul_mem' := fun r x hx =>
         connected_locus_smul_of_hopf_package ρ n G fG hfG e₀ he₀ hε₀ hmin₀
           habs₀ r x hx }, fun _ => Iff.rfl⟩
  -- ## every inertia displacement is connected: `d V ⊆ M⁰`
  obtain ⟨D, hDapp⟩ : ∃ D : V →ₗ[R] V, ∀ y : V, D y = ρ g₀ y - y :=
    ⟨(ρ g₀ : V →ₗ[R] V) - LinearMap.id, fun y => by
      simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq]⟩
  have hDN : ∀ y : V, D y ∈ N := by
    intro y
    rw [hmemN, hDapp]
    have h := inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG σ hσ ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] y)
    rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      ← TensorProduct.tmul_sub, ← hg₀] at h
    exact h
  -- ## the residual line: `ker π̄ = kk · w̄₀`
  haveI : Module.Finite kk (kk ⊗[R] V) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R V).baseChange kk)
  have hfr : Module.finrank kk (kk ⊗[R] V) = 2 :=
    Module.finrank_eq_of_rank_eq (by rw [Module.rank_baseChange, hV]; simp)
  have hker1 : Module.finrank kk (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπsurj, finrank_top, Module.finrank_self,
      hfr] at h
    omega
  have hkerspan : (LinearMap.ker π : Submodule kk (kk ⊗[R] V)) =
      Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr hw₀π
    · rw [hker1, finrank_span_singleton hw₀ne]
  have hkey : ∀ uu : V, π ((1 : kk) ⊗ₜ[R] uu) = 0 →
      ∃ r : R, uu - r • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro uu huu
    have humem : (1 : kk) ⊗ₜ[R] uu ∈
        Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀} := by
      rw [← hkerspan]
      exact LinearMap.mem_ker.mpr huu
    obtain ⟨xx, hxx⟩ := Submodule.mem_span_singleton.mp humem
    obtain ⟨r, hrr⟩ := hsurj xx
    refine ⟨r, mem_maximalIdeal_smul_top_of_one_tmul_eq_zero kk hsurj ?_⟩
    rw [TensorProduct.tmul_sub, one_tmul_smul, hrr, hxx, sub_self]
  have hres : ∀ (g : Γ ℚ) (v : V),
      π ((1 : kk) ⊗ₜ[R] (ρ g v)) = π ((1 : kk) ⊗ₜ[R] v) := by
    intro g v
    rw [show (1 : kk) ⊗ₜ[R] (ρ g v) =
      (ρ.baseChange kk) g ((1 : kk) ⊗ₜ[R] v) from rfl, hπequiv]
  -- `p := d w₀` is residually the UNIT multiple `(a g₀ − 1) • w₀`
  have hpw₀ : (ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have h1 : (ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀ = ρ g₀ w₀ - a g₀ • w₀ := by
      rw [sub_smul, one_smul]; abel
    rw [h1]
    exact ha g₀
  have hinv : (↑u⁻¹ : R) * (a g₀ - 1) = 1 := by rw [← hu]; exact u.inv_mul
  -- ## the residual rank-one statement: `d V ⊆ R ∙ p + 𝔪V`
  have hE : ∀ y : V, ∃ α : R,
      (ρ g₀ y - y) - α • (ρ g₀ w₀ - w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro y
    have hπ0 : π ((1 : kk) ⊗ₜ[R] (ρ g₀ y - y)) = 0 := by
      rw [TensorProduct.tmul_sub, map_sub, hres g₀ y, sub_self]
    obtain ⟨r, hr⟩ := hkey _ hπ0
    refine ⟨r * (↑u⁻¹ : R), ?_⟩
    -- scale the residual identity for `p` by `r · u⁻¹`
    have h2 : (r * (↑u⁻¹ : R)) • ((ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      Submodule.smul_mem _ _ hpw₀
    have h3 : (r * (↑u⁻¹ : R)) • ((ρ g₀ w₀ - w₀) - (a g₀ - 1) • w₀) =
        (r * (↑u⁻¹ : R)) • (ρ g₀ w₀ - w₀) - r • w₀ := by
      rw [smul_sub, smul_smul, mul_assoc, hinv, mul_one]
    rw [h3] at h2
    have h4 : (ρ g₀ y - y) - (r * (↑u⁻¹ : R)) • (ρ g₀ w₀ - w₀) =
        ((ρ g₀ y - y) - r • w₀) -
          ((r * (↑u⁻¹ : R)) • (ρ g₀ w₀ - w₀) - r • w₀) := by abel
    rw [h4]
    exact Submodule.sub_mem _ hr h2
  -- ## the finite-flat leaf: `d` is surjective on `M⁰`
  have hleaf : ∀ zz ∈ N, ∃ y ∈ N,
      zz - (ρ g₀ y - y) ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
    intro zz hzz
    obtain ⟨y, hy1, hy2⟩ :=
      connected_locus_displacement_surjective_of_hopf_package V hV hρ kk hsurj
        π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
        σ hσ hσω zz ((hmemN zz).1 hzz)
    rw [← hg₀] at hy2
    exact ⟨y, (hmemN y).2 hy1, hy2⟩
  -- ## hence `M⁰ ⊆ R ∙ p + 𝔪V`
  have hNp : N ≤ Submodule.span R {ρ g₀ w₀ - w₀} ⊔
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro zz hzz
    obtain ⟨y, _, hy2⟩ := hleaf zz hzz
    obtain ⟨α, hα2⟩ := hE y
    have h1 : zz = α • (ρ g₀ w₀ - w₀) +
        (((ρ g₀ y - y) - α • (ρ g₀ w₀ - w₀)) + (zz - (ρ g₀ y - y))) := by abel
    rw [h1]
    refine Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton.2 ⟨α, rfl⟩))
      (Submodule.mem_sup_right (Submodule.add_mem _ hα2 ?_))
    exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) hy2
  -- ## the Nakayama iteration: `M⁰` is generated by `d p = d (d w₀)`
  have hfinal : N ≤ Submodule.span R {D (ρ g₀ w₀ - w₀)} ⊔
      (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) :=
    le_span_singleton_sup_smul_pow_of_displacement_surjective
      (IsLocalRing.maximalIdeal R) (n + 2) N D (ρ g₀ w₀ - w₀) hDN hNp
      (fun zz hzz => by
        obtain ⟨y, hy1, hy2⟩ := hleaf zz hzz
        exact ⟨y, hy1, by rw [hDapp]; exact hy2⟩)
  refine ⟨D (ρ g₀ w₀ - w₀), ?_⟩
  intro x hx
  obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 (hfinal ((hmemN x).2 hx))
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hs
  refine ⟨r, ?_⟩
  have h1 : x - r • D (ρ g₀ w₀ - w₀) = m := by rw [← hsm, ← hr]; abel
  rw [h1]
  exact hm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected locus has rank at MOST one** (PROVEN 2026-07-27 over
the single leaf `connected_locus_cyclic_of_hopf_package` just above; was
itself a SORRY LEAF, cut 2026-07-26 out of
`exists_connected_line_of_hopf_package` below,
together with its full-faithfulness sibling
`connected_locus_smul_of_hopf_package` above).

Content: given ANY connected vector `w₁` that is residually nonzero,
every connected vector `x` is congruent to an `R`-multiple of `w₁`
modulo `𝔪ⁿ⁺²V`. Combined with the sibling (which gives the reverse
inclusion) this says the connected locus is exactly the image of the
line `R · w₁`.

WHAT THE ASSEMBLY BELOW CONTRIBUTES. All of the finite-flat content now
sits in `connected_locus_cyclic_of_hopf_package` above, which produces
SOME generator `w` of the connected locus. What is written out here is
the residual normalisation, and it is pure local algebra: applying that
leaf to the given connected `w₁` gives `w₁ ≡ r₁ • w`, and `r₁` must be a
UNIT — otherwise `w₁ ∈ 𝔪V` and `1 ⊗ w₁ = 0`, contradicting `hw₁ne`. So
`w₁` generates the same line as `w`, and the multiplier for an arbitrary
connected `x` is `r · r₁⁻¹`.

**ROUTE CORRECTION (2026-07-27) — the previous route recorded here was
WRONG, and believing it costs a cycle.** It said the only thing owed was
`M⁰ ≠ M`, "Nakayama over the local ring `R` then makes the submodule
cyclic on any residually nonzero member". That inference is FALSE: over
`A = ℤ⧸9` the submodule `N = A·(1,0) + A·(0,3)` of `M = A²` is proper,
has residual image the LINE `kk·(1,0)`, contains the residually nonzero
`(1,0)`, satisfies `N^{I} = 0` with `I` trivial on `M/N`, and has
surjective determinant — yet `(0,3) ∈ N` is not an `A`-multiple of
`(1,0)`. Residual one-dimensionality controls `N ⧸ (N ∩ 𝔪M)`, while
Nakayama needs `N ⧸ 𝔪N`. The full computation, and the finite-flat input
that really does exclude it (`M⁰` is of multiplicative type, so
`ρ g₀ − 1` is invertible on it and `M⁰` is a direct SUMMAND), are in the
docstring of `connected_locus_cyclic_of_hopf_package` above.

WHAT IS ALREADY AVAILABLE and must NOT be re-proven: the connected locus
is an additive subgroup with no nonzero inertia-fixed vector
(`exists_connectedEtale_subgroup_at_three_of_threePowTorsion`), every
inertia displacement is connected
(`inertia_displacement_apply_connected_idempotent_eq_one`), and the
connected locus is `Γ ℚ₃ᵥ`-stable (the `hstable` argument written out in
`exists_connected_line_generator_of_hopf_package` below). Those give
`M/M⁰` unramified and `(M⁰)^{I₃} = 0` — and, per the correction above,
they do NOT suffice even together with `M⁰ ≠ M`.

FAITHFULNESS. The conclusion is a VALUE-level membership over `𝒪ᵥ`
(a congruence in `V` modulo `𝔪ⁿ⁺²V`), never an element of `G` and never
`Γ`-wide rationality of a coordinate, so it is on the true side of the
`𝒪ᵥ`-descent rule. Note the hypothesis `hw₁ne` is essential: without
residual nonvanishing of `w₁` the statement is FALSE (take `w₁ = 0`,
whose `R`-line is `0`, while the connected locus is not — see
`exists_connected_line_of_hopf_package` below, which produces a
residually nonzero connected vector unconditionally).

Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Oort–Tate, *Group schemes of
prime order*; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem connected_locus_le_line_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (w₁ : V) (hw₁ne : (1 : kk) ⊗ₜ[R] w₁ ≠ 0)
    (hw₁conn : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] w₁)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1)
    (x : V)
    (hx : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ r : R, x - r • w₁ ∈
      (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
  classical
  -- the finite-flat content: the connected locus is generated by a single `w`
  obtain ⟨w, hw⟩ := connected_locus_cyclic_of_hopf_package V hV hρ kk hsurj π
    hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
  obtain ⟨r₁, hr₁⟩ := hw w₁ hw₁conn
  obtain ⟨r, hr⟩ := hw x hx
  have hpowle : (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) ≤
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  -- `r₁` is a UNIT: otherwise `w₁ ∈ 𝔪V`, contradicting `hw₁ne`
  have hunit : IsUnit r₁ := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    refine hw₁ne (one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj ?_)
    have hmem2 : (w₁ - r₁ • w) + r₁ • w ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      Submodule.add_mem _ (hpowle hr₁) (Submodule.smul_mem_smul hmem trivial)
    have heq : (w₁ - r₁ • w) + r₁ • w = w₁ := by abel
    rwa [heq] at hmem2
  obtain ⟨u, hu⟩ := hunit
  -- so `w₁` generates the same line as `w`, with multiplier `r · r₁⁻¹`
  have hsr : (r * (↑u⁻¹ : R)) * r₁ = r := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  refine ⟨r * (↑u⁻¹ : R), ?_⟩
  have key : x - (r * (↑u⁻¹ : R)) • w₁ =
      (x - r • w) - (r * (↑u⁻¹ : R)) • (w₁ - r₁ • w) := by
    rw [smul_sub, smul_smul, hsr]
    abel
  rw [key]
  exact Submodule.sub_mem _ hr (Submodule.smul_mem _ _ hr₁)

/-- **Raynaud step (3): the connected locus is a residually nonzero
cyclic line** (PROVEN 2026-07-26 over the two leaves
`connected_locus_smul_of_hopf_package` (Raynaud full faithfulness) and
`connected_locus_le_line_of_hopf_package` (rank at most one) just above;
was itself a SORRY LEAF, cut 2026-07-26 out of
`exists_connected_line_generator_of_hopf_package` just below, which is
now PROVEN over this leaf together with its step-(4) sibling
`exists_localInertia_moves_connected_point_of_hopf_package`).

This is the FINITE-FLAT half of the old single Raynaud leaf, and the
half that spends the absolute unramifiedness of `ℤ₃`. Nothing residual,
nothing about `w₀`, nothing about `π` enters the CONCLUSION: it says
only that the connected locus
`M⁰ = {x | (point of 1 ⊗ x)(1 ⊗ e₀) = 1} ⊆ M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V`
is the image of a single vector's `R`-line, and that this generator does
not vanish residually (i.e. the connected part has rank EXACTLY one, not
zero).

ROUTE. Multiplication by a scalar of `R` is an endomorphism of the
generic fibre `Spec (ℚ₃ᵥ ⊗ G)`; **Raynaud's full faithfulness at
`e = 1 < p − 1 = 2`** (Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5)
extends it to the finite flat model `Spec G` over `𝒪ᵥ ≅ ℤ₃`, so it
carries the connected component of the identity into itself. Hence `M⁰`
is an `R ⧸ 𝔪ⁿ⁺²`-SUBMODULE of `M`, not merely the additive subgroup
that `exists_connectedEtale_subgroup_at_three_of_threePowTorsion` above
already provides. Its rank is `1` rather than `0` or `2`: a rank-`2`
connected (multiplicative-type) model would force
`det ρ̄ |ᵢₙₑᵣₜᵢₐ = ω²` and a rank-`0` one (étale model) `det ρ̄ |ᵢₙₑᵣₜᵢₐ = 1`,
while `det ρ̄ = ω` is ramified at `3` and `ω ≠ ω²` because `ω ≠ 1` on
inertia. `mem_span_natCast_of_inertia_invariant`
(`Fermat/FLT/GroupScheme/ConnectedEtale.lean`) spends the same
absolute-unramifiedness input and is the proof to read first.

**WHAT THE ASSEMBLY BELOW CONTRIBUTES (2026-07-26), so that the two
leaves are only the finite-flat content.** The two halves of the route
above are exactly the two leaves — `connected_locus_smul_of_hopf_package`
is the full-faithfulness half (`M⁰` is an `R`-submodule) and
`connected_locus_le_line_of_hopf_package` the rank half (`M⁰` is at most
a line). Everything else is written out below and costs no flat theory:

* the GENERATOR is produced outright, with no classification input. Take
  `σ ∈ I₃` with `ω σ ≠ 1`
  (`exists_localInertia_cyclotomicCharacterModL_three_ne_one` above) and
  set `w₁ := ρ σ w₀ − w₀`. It is CONNECTED because it is an inertia
  displacement (`inertia_displacement_apply_connected_idempotent_eq_one`,
  the étale half of the dichotomy), and it is residually NONZERO because
  residually `w₁ ≡ (a σ − 1) • w₀` with `a ≡ ω` by
  `residual_twist_eq_cyclotomicCharacterModL`, so `a σ ≡ −1` and
  `a σ − 1 ≡ 1 mod 𝔪` is a UNIT (`3 ∈ 𝔪`, the one place `p = 3` is
  spent). This is why the leaves do NOT have to establish rank `≥ 1`:
  the ramifiedness of `ω` at `3` already exhibits a connected vector
  outside `𝔪V`.
* the `⟸` direction of the displayed `↔` is the full-faithfulness leaf
  applied to `w₁`, plus the fact that `𝔪ⁿ⁺²V` is invisible in the
  congruence quotient (`one_tmul_quotient_eq_zero_of_mem_smul_top`).
* the `⟹` direction is the rank leaf verbatim.

So of the three things the old single leaf owed — `R`-stability, rank
`≥ 1`, rank `≤ 1` — the middle one is now PROVEN here and only the
outer two remain open.

FAITHFULNESS. The conclusion asks for a VALUE-level identity over
`𝒪ᵥ` — the connected locus, defined by the value `1` at the
`𝒪ᵥ`-rational idempotent `e₀`, coincides with an `R`-line of `V` — and
never for an element of `G` or for `Γ`-rationality of a coordinate. It
is therefore on the true side of the development's `𝒪ᵥ`-descent rule,
and blind to the `p − 1` unramified twists `μ_p ⊗ ψ` that killed
`exists_muType_closure`: a twist changes WHICH line, not whether the
connected locus is one.

Tate, *Finite flat group schemes*, §4, in Cornell–Silverman–Stevens;
Fontaine, *Il n'y a pas de variété abélienne sur `ℤ`*, §1. -/
theorem exists_connected_line_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀) :
    ∃ w₁ : V, (1 : kk) ⊗ₜ[R] w₁ ≠ 0 ∧
      ∀ x : V,
        ((Additive.toMul ((Equiv.ofBijective fG hfG).symm
            ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 ↔
        ∃ r : R, x - r • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) := by
  classical
  -- an inertia element at `3` off the kernel of `ω`
  obtain ⟨σ, hσ, hσω⟩ := exists_localInertia_cyclotomicCharacterModL_three_ne_one
  set g₀ : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ with hg₀
  -- the residual `w₀`-line and its diagonal entry `a`
  obtain ⟨a, _c, hac⟩ := exists_residual_matrix_entries hV kk hsurj π hπsurj hπequiv
    w₀ v₀ hw₀π hw₀ne
  have ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := fun g => (hac g).1
  -- `a g₀ ≡ −1 mod 𝔪`, hence `a g₀ − 1 ≡ 1 mod 𝔪` is a UNIT (`3 ∈ 𝔪`)
  have hα : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R :=
    (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne a ha g₀).2 hσω
  have hunit : IsUnit (a g₀ - 1) := by
    have h1 : (a g₀ - 1) - 1 ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (a g₀ - 1) - 1 = (a g₀ + 1) - 3 := by ring
      rw [h2]
      exact Submodule.sub_mem _ hα three_mem_maximalIdeal
    have h3 : a g₀ - 1 ∉ IsLocalRing.maximalIdeal R := by
      intro hmem
      have h4 := Submodule.sub_mem _ hmem h1
      simp only [sub_sub_cancel] at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h4 isUnit_one)
    exact IsLocalRing.notMem_maximalIdeal.mp h3
  -- the generator: the inertia displacement of `w₀`, residually `(a g₀ − 1) • w₀`
  have hw₁ne : (1 : kk) ⊗ₜ[R] (ρ g₀ w₀ - w₀) ≠ 0 := by
    intro h0
    have hmem := mem_maximalIdeal_smul_top_of_one_tmul_eq_zero kk hsurj h0
    have hsm : (a g₀ - 1) • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
      have h1 : (a g₀ - 1) • w₀ = (ρ g₀ w₀ - w₀) - (ρ g₀ w₀ - a g₀ • w₀) := by
        rw [sub_smul, one_smul]; abel
      rw [h1]
      exact Submodule.sub_mem _ hmem (ha g₀)
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit)
      (mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne hsm)
  refine ⟨ρ g₀ w₀ - w₀, hw₁ne, ?_⟩
  -- the displacement is a CONNECTED point of the model
  have hw₁conn : (Additive.toMul ((Equiv.ofBijective fG hfG).symm
      ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] (ρ g₀ w₀ - w₀))))
      ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    have h := inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG σ hσ ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] w₀)
    rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      ← TensorProduct.tmul_sub, ← hg₀] at h
    exact h
  intro x
  constructor
  · -- rank at most one
    exact connected_locus_le_line_of_hopf_package V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
      (ρ g₀ w₀ - w₀) hw₁ne hw₁conn x
  · -- the line is connected: `R`-stability (full faithfulness) plus the fact
    -- that `𝔪ⁿ⁺²V` is invisible in the congruence quotient
    rintro ⟨r, hr⟩
    have h0 : (1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x =
        (1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R]
          (r • (ρ g₀ w₀ - w₀)) := by
      have h1 := one_tmul_quotient_eq_zero_of_mem_smul_top
        (IsLocalRing.maximalIdeal R ^ (n + 2)) hr
      rwa [TensorProduct.tmul_sub, sub_eq_zero] at h1
    rw [h0]
    exact connected_locus_smul_of_hopf_package ρ n G fG hfG e₀ he₀ hε₀
      hmin₀ habs₀ r (ρ g₀ w₀ - w₀) hw₁conn

/-- **Raynaud step (4): the connected part is RAMIFIED at `3`** (PROVEN
2026-07-26, INDEPENDENTLY of its step-(3) sibling; was a SORRY LEAF cut
2026-07-26 out of
`exists_connected_line_generator_of_hopf_package` just below, together
with its step-(3) sibling `exists_connected_line_of_hopf_package` above).

Some point of the connected locus is moved RESIDUALLY by some element of
the local inertia group at `3`. Equivalently: local inertia does not act
trivially on `M⁰ ⊗ kk`.

WHY THIS IS THE WHOLE OF STEP (4). The consumer below needs to know that
the connected line reduces onto the `w₀`-line, i.e. `π (1 ⊗ w₁) = 0`.
That is derived there, not assumed: the line is `Γ ℚ₃ᵥ`-stable (step (1)
of the old route, now real Lean in the consumer, from the
`𝒪ᵥ`-rationality of `e₀` and the `Γ ℚ₃ᵥ`-equivariance of `fG`), so it
carries a diagonal entry `E`; if the generator did NOT lie residually in
`ker π` then `hπequiv` would force `Ē g = 1` for EVERY `g` in the
decomposition group at `3`, in particular on inertia — which is exactly
what this leaf forbids. So "connected ⇒ ramified" is all that is
missing, and the ω-isotypic bookkeeping of the old route is subsumed by
it.

ROUTE AS PROVEN (2026-07-26). The recorded route below expected this
leaf to spend the Oort–Tate classification of the connected part as a
`μ₃`-type line. **It does not have to**, and the shorter route is the
one written: the WITNESS is already in the tree, and the moved point is
the inertia displacement of `w₀` itself.

Take `σ ∈ I₃` with `ω σ ≠ 1`
(`exists_localInertia_cyclotomicCharacterModL_three_ne_one` above — the
inertia-level ramifiedness of `ω`, i.e. `ℚ₃(ζ₃)/ℚ₃` totally tamely
ramified of degree `φ(3) = 2`, and the mirror image of
`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup` below, which
proves `ω` UNRAMIFIED at every `p ≠ 3`), write `g₀` for its image in
`Γ ℚ`, and take `x := ρ g₀ w₀ − w₀`. Then:

* `x` is CONNECTED for free — it is an inertia displacement, and
  `inertia_displacement_apply_connected_idempotent_eq_one` above says
  every inertia displacement takes the value `1` on `e₀` (that is the
  étale half of the connected–étale dichotomy: the étale quotient has
  unramified points, so displacements die in it). No classification
  input is consumed here.
* `x` is moved AGAIN by the same `σ`. Residually the `w₀`-line is
  `Γ ℚ`-stable with diagonal entry `a` (`exists_residual_matrix_entries`)
  and `a ≡ ω` (`residual_twist_eq_cyclotomicCharacterModL`, the
  determinant identification), so `ω g₀ ≠ 1` gives `a g₀ ≡ −1 mod 𝔪`,
  hence `a g₀ − 1 ≡ 1 mod 𝔪` is a UNIT — this is the one place `p = 3`
  is spent, since `3 ∈ 𝔪` makes `−2 ≡ 1`. Modulo `𝔪V` therefore
  `x ≡ (a g₀ − 1) • w₀` and `ρ g₀ x − x ≡ (a g₀ − 1)² • w₀`, a UNIT
  multiple of the residually nonzero `w₀`, so it is NOT in `𝔪V`. The
  two `𝔪V`-corrections are absorbed because `ρ g₀` preserves `𝔪V`
  (`apply_mem_smul_top`).

So step (4) needs NO Oort–Tate/Raynaud input at all: it is the residual
determinant plus the already-proven étale half. The finite-flat content
of the cut therefore sits ENTIRELY in step (3)'s two leaves
(`connected_locus_smul_of_hopf_package`,
`connected_locus_le_line_of_hopf_package`) — a redistribution worth
recording, since the original cut expected both steps to owe
classification.

HYPOTHESIS AUDIT. `_hmin₀` (minimality of `e₀`) and `_habs₀` (comul
absorption) are UNUSED and underscore-prefixed so this is mechanically
visible. That is not vacuity: the conclusion has real content, and both
would be needed by the longer classification route. They are kept in the
signature so the consumer's call site does not have to change, and
because any future strengthening of this leaf will want them.

FAITHFULNESS. The quantifier is over `localInertiaGroup 𝔭₃` and NOT
over `Γ ℚ₃ᵥ`, deliberately: over the full decomposition group the
connected character is `ω · ψ` with `ψ` an unramified twist, and the
statement would be FALSE for `ψ = ω⁻¹` — this is the development's
signature error (a `localInertiaGroup` quantifier widened to `Γ`) in the
exact place where it would bite. Inertia-only conclusions are
twist-blind, which is why this form is the true one. The conclusion asks
only for a VALUE-level non-membership over `𝒪ᵥ`, never for an element of
`G`.

Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Oort–Tate, *Group schemes of
prime order*; Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens. -/
theorem exists_localInertia_moves_connected_point_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (_hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (_habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀) :
    ∃ σ ∈ localInertiaGroup 𝔭₃, ∃ x : V,
      ((Additive.toMul ((Equiv.ofBijective fG hfG).symm
          ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
        ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) ∧
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) x - x ∉
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
  classical
  -- an inertia element at `3` off the kernel of `ω`
  obtain ⟨σ, hσ, hσω⟩ := exists_localInertia_cyclotomicCharacterModL_three_ne_one
  set g₀ : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ with hg₀
  -- the residual `w₀`-line and its diagonal entry `a`
  obtain ⟨a, _c, hac⟩ := exists_residual_matrix_entries hV kk hsurj π hπsurj hπequiv
    w₀ v₀ hw₀π hw₀ne
  have ha : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := fun g => (hac g).1
  -- `a g₀ ≡ −1 mod 𝔪`, hence `a g₀ − 1 ≡ 1 mod 𝔪` is a UNIT (`3 ∈ 𝔪`)
  have hα : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R :=
    (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne a ha g₀).2 hσω
  have hunit : IsUnit (a g₀ - 1) := by
    have h1 : (a g₀ - 1) - 1 ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (a g₀ - 1) - 1 = (a g₀ + 1) - 3 := by ring
      rw [h2]
      exact Submodule.sub_mem _ hα three_mem_maximalIdeal
    have h3 : a g₀ - 1 ∉ IsLocalRing.maximalIdeal R := by
      intro hmem
      have h4 := Submodule.sub_mem _ hmem h1
      simp only [sub_sub_cancel] at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h4 isUnit_one)
    exact IsLocalRing.notMem_maximalIdeal.mp h3
  refine ⟨σ, hσ, ρ g₀ w₀ - w₀, ?_, ?_⟩
  · -- the displacement is a CONNECTED point of the model
    have h := inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG σ hσ ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] w₀)
    rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      ← TensorProduct.tmul_sub, ← hg₀] at h
    exact h
  · -- residually the displacement is `(a g₀ − 1) • w₀`, and `ρ g₀` moves it again
    intro hmem
    have hy : ρ g₀ w₀ - a g₀ • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := ha g₀
    have hsplit : ρ g₀ (ρ g₀ w₀ - w₀) - (ρ g₀ w₀ - w₀) =
        ((a g₀ - 1) * (a g₀ - 1)) • w₀ +
          ((a g₀ - 1) • (ρ g₀ w₀ - a g₀ • w₀)
            + (ρ g₀ (ρ g₀ w₀ - a g₀ • w₀) - (ρ g₀ w₀ - a g₀ • w₀))) := by
      simp only [map_sub, map_smul]
      module
    have hcorr : ((a g₀ - 1) • (ρ g₀ w₀ - a g₀ • w₀)
        + (ρ g₀ (ρ g₀ w₀ - a g₀ • w₀) - (ρ g₀ w₀ - a g₀ • w₀))) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ hy)
        (Submodule.sub_mem _ (apply_mem_smul_top _ hy) hy)
    have hsq : ((a g₀ - 1) * (a g₀ - 1)) • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
      have h1 : ((a g₀ - 1) * (a g₀ - 1)) • w₀ =
          (ρ g₀ (ρ g₀ w₀ - w₀) - (ρ g₀ w₀ - w₀))
            - ((a g₀ - 1) • (ρ g₀ w₀ - a g₀ • w₀)
              + (ρ g₀ (ρ g₀ w₀ - a g₀ • w₀) - (ρ g₀ w₀ - a g₀ • w₀))) := by
        rw [hsplit]; abel
      rw [h1]
      exact Submodule.sub_mem _ hmem hcorr
    have hmem2 : (a g₀ - 1) * (a g₀ - 1) ∈ IsLocalRing.maximalIdeal R :=
      mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne hsq
    exact (IsLocalRing.notMem_maximalIdeal.mpr (hunit.mul hunit)) hmem2

/-- **The connected part of the flat package at `3` is a line, generated
by a lift of `w₀`** (PROVEN 2026-07-26 over the two Raynaud leaves
`exists_connected_line_of_hopf_package` (step (3)) and
`exists_localInertia_moves_connected_point_of_hopf_package` (step (4))
just above; was itself a SORRY LEAF, cut 2026-07-26 out of
`exists_connectedEtale_line_of_hopf_package` just below, which is
PROVEN over it).

**WHAT THE ASSEMBLY BELOW CONTRIBUTES, so that the two leaves are only
the finite-flat content.** Given the connected locus as an `R`-line
(step (3)) and the ramifiedness of the connected part (step (4)),
everything else is elementary and is written out below:

* the connected locus is `Γ ℚ₃ᵥ`-STABLE, because `e₀` is `𝒪ᵥ`-rational
  and the Galois action on points is post-composition — so the line
  carries a diagonal entry `E` (this is the same `hstable` argument the
  consumer below performs, needed here one level earlier);
* hence, if the generator did NOT reduce into `ker π`, then `hπequiv`
  would give `Ē g · π (1 ⊗ w₁) = π (1 ⊗ w₁)` with `π (1 ⊗ w₁) ≠ 0`,
  forcing `Ē g = 1` for EVERY `g` in the decomposition group at `3`, in
  particular for the inertia element supplied by step (4) — which is
  precisely what that leaf forbids. So `π (1 ⊗ w₁) = 0`;
* `ker π` is a `kk`-line (rank–nullity in the 2-dimensional residual
  space) containing the nonzero `1 ⊗ w₀`, so the generator is a nonzero
  `kk`-multiple of `1 ⊗ w₀`; the multiplier lifts to a UNIT of the local
  ring `R` (its residue is nonzero), and rescaling by that unit
  normalises `w₁ ≡ w₀ mod 𝔪V` without changing the line `R · w₁`.

Statement. `M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` is the space of the congruence
quotient `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)`, `Γ ℚ₃ᵥ`-equivariantly identified by
`fG` with the geometric points of the generic fibre of the finite flat
Hopf order `G` over `𝒪ᵥ ≅ ℤ₃`; a point is CONNECTED when it takes the
value `1` on the connected counit idempotent `e₀`. The claim is that the
connected locus `M⁰ ⊆ M` is exactly the image of a free rank-one line
`R · w₁`, whose generator can be normalised to `w₁ ≡ w₀ mod 𝔪V`.
(The `x ↦ 1 ⊗ x` presentation is harmless: `V → (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` is
surjective with kernel `𝔪ⁿ⁺² • ⊤`, so the displayed `↔` says precisely
`M⁰ = image of R · w₁`.)

FAITHFULNESS. The conclusion asks only for VALUES and an inertia-only
comparison over `𝒪ᵥ` — never for an element of `G`, never for
`Γ`-rationality of a coordinate — so it is on the true side of the
development's `𝒪ᵥ`-descent rule, and the unramified twists that killed
`exists_muType_closure` are invisible to it: they are absorbed by the
inertia-only form of step (4). The `Γ`-stability that the consumer
needs is LOCAL at `3` (see that node's faithfulness note) and is
derived, not assumed, here.

Tate, *Finite flat group schemes*, §4, in Cornell–Silverman–Stevens;
Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102 (1974),
3.3.2–3.3.5; Fontaine, *Il n'y a pas de variété abélienne sur `ℤ`*,
§1. -/
theorem exists_connected_line_generator_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G] [HopfAlgebra 𝒪₃ᵥ G] [Module.Flat 𝒪₃ᵥ G]
    [Module.Finite 𝒪₃ᵥ G] [Algebra.Etale ℚ₃ᵥ (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G)]
    (fG : Additive (ℚ₃ᵥ ⊗[𝒪₃ᵥ] G →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ) →+[Γ ℚ₃ᵥ]
      (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        𝔭₃).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀) :
    ∃ w₁ : V,
      w₁ - w₀ ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) ∧
      ∀ x : V,
        ((Additive.toMul ((Equiv.ofBijective fG hfG).symm
            ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] x)))
          ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 ↔
        ∃ r : R, x - r • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) := by
  classical
  -- Raynaud step (3): the connected locus is a residually nonzero cyclic line
  obtain ⟨w₁, hw₁ne, hline⟩ :=
    exists_connected_line_of_hopf_package V hV hρ kk hsurj π hπsurj hπequiv
      v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
  -- Raynaud step (4): local inertia at `3` moves some connected point
  obtain ⟨σ, -, x₀, hx₀conn, hx₀move⟩ :=
    exists_localInertia_moves_connected_point_of_hopf_package V hV hρ kk hsurj
      π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
  have hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ hsurj)
  have hpowle : (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) ≤
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  -- (i) inertia moves the GENERATOR of the line residually: any connected
  -- point is `r • w₁` up to `𝔪ⁿ⁺²V`, and `ρ σ` preserves `𝔪V`
  have hmove : ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁ - w₁ ∉
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    intro hmem
    refine hx₀move ?_
    obtain ⟨r, hr⟩ := (hline x₀).1 hx₀conn
    have hsplit : ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) x₀ - x₀ =
        (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) (x₀ - r • w₁)
          - (x₀ - r • w₁))
        + r • (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁ - w₁) := by
      simp only [map_sub, map_smul, smul_sub]
      abel
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ (hpowle hr)) ?_
    · exact hpowle (apply_mem_smul_top _ hr)
    · exact Submodule.smul_of_tower_mem _ _ hmem
  -- the generator is itself a connected point
  set gG := Equiv.ofBijective fG hfG
  have hfs : ∀ y, fG (gG.symm y) = y := fun y => gG.apply_symm_apply y
  have hw₁conn :
      (Additive.toMul (gG.symm ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))
          ⊗ₜ[R] w₁))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 :=
    (hline w₁).2 ⟨1, by rw [one_smul, sub_self]; exact Submodule.zero_mem _⟩
  -- the connected locus is `Γ ℚ₃ᵥ`-stable, because `e₀` is `𝒪ᵥ`-rational and
  -- the Galois action on points is post-composition
  have hstable : ∀ (g : Γ ℚ₃ᵥ)
      (m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V),
      (Additive.toMul (gG.symm m)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (gG.symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
          g m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro g m hm
    have hsym : gG.symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
          g m) = g • gG.symm m := by
      apply gG.injective
      show fG (gG.symm _) = fG (g • gG.symm m)
      rw [map_smul fG, hfs, hfs]
      rfl
    rw [hsym]
    have hact : Additive.toMul (g • gG.symm m) =
        (g.toAlgHom : ℚ₃ᵥᵃˡᵍ →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ).comp
          (Additive.toMul (gG.symm m)) := AlgHom.ext fun _ => rfl
    rw [hact, AlgHom.comp_apply, hm, map_one]
  -- (ii) hence the line has a diagonal entry at every `g : Γ ℚ₃ᵥ`
  have hE : ∀ g : Γ ℚ₃ᵥ, ∃ r : R,
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g) w₁ - r • w₁ ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
    intro g
    refine (hline _).1 ?_
    have h1 := hstable g _ hw₁conn
    rwa [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul] at h1
  -- (iii) the generator reduces into `ker π`: otherwise `hπequiv` forces the
  -- diagonal entry to be residually `1` at the inertia element of step (4)
  have hw₁π : π ((1 : kk) ⊗ₜ[R] w₁) = 0 := by
    by_contra hne
    obtain ⟨r, hr⟩ := hE σ
    have hr' := hpowle hr
    have h0 : (1 : kk) ⊗ₜ[R]
        (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁ - r • w₁) = 0 :=
      one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj hr'
    rw [TensorProduct.tmul_sub, one_tmul_smul, sub_eq_zero] at h0
    have hinv : π ((1 : kk) ⊗ₜ[R]
        (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁)) =
        π ((1 : kk) ⊗ₜ[R] w₁) := by
      have h := hπequiv (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ)
        ((1 : kk) ⊗ₜ[R] w₁)
      rwa [GaloisRep.baseChange_tmul] at h
    rw [h0, map_smul, smul_eq_mul] at hinv
    have hz : (algebraMap R kk r - 1) * π ((1 : kk) ⊗ₜ[R] w₁) = 0 := by
      rw [sub_mul, one_mul, hinv, sub_self]
    have hr1 : algebraMap R kk r = 1 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hne
    refine hmove ?_
    have hsplit : ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁ - w₁ =
        (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) σ) w₁ - r • w₁)
          + (r - 1) • w₁ := by
      rw [sub_smul, one_smul]; abel
    rw [hsplit]
    refine Submodule.add_mem _ hr' (Submodule.smul_mem_smul ?_ trivial)
    rw [← hker, RingHom.mem_ker, map_sub, hr1, map_one, sub_self]
  -- (iv) `ker π` is a `kk`-line spanned by `1 ⊗ w₀` (rank–nullity in the
  -- 2-dimensional residual space), so the generator is a unit multiple of `w₀`
  haveI : Module.Finite kk (kk ⊗[R] V) :=
    Module.Finite.of_basis ((Module.Free.chooseBasis R V).baseChange kk)
  have hfr : Module.finrank kk (kk ⊗[R] V) = 2 :=
    Module.finrank_eq_of_rank_eq (by rw [Module.rank_baseChange, hV]; simp)
  have hker1 : Module.finrank kk (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπsurj, finrank_top, Module.finrank_self,
      hfr] at h
    omega
  have hspan : (Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀}) = LinearMap.ker π := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hw₀π
    · rw [finrank_span_singleton hw₀ne, hker1]
  have hw₁mem : ((1 : kk) ⊗ₜ[R] w₁) ∈ Submodule.span kk {(1 : kk) ⊗ₜ[R] w₀} := by
    rw [hspan]
    exact hw₁π
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hw₁mem
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc'
    exact hw₁ne hc'.symm
  obtain ⟨r₀, hr₀⟩ := hsurj c
  have hr₀unit : IsUnit r₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker, hr₀]
    exact hcne
  obtain ⟨u, hu⟩ := hr₀unit
  -- rescaling by that unit normalises the generator without moving the line
  refine ⟨(↑u⁻¹ : R) • w₁, ?_, ?_⟩
  · refine mem_maximalIdeal_smul_top_of_one_tmul_eq_zero kk hsurj ?_
    rw [TensorProduct.tmul_sub, one_tmul_smul, ← hc', smul_smul]
    have hone : algebraMap R kk (↑u⁻¹ : R) * c = 1 := by
      rw [← hr₀, ← hu, ← map_mul]
      norm_num
    rw [hone, one_smul, sub_self]
  · intro y
    rw [hline y]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r * (u : R), ?_⟩
      have hu1 : (r * (u : R)) * (↑u⁻¹ : R) = r := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      rwa [smul_smul, hu1]
    · rintro ⟨r, hr⟩
      exact ⟨r * (↑u⁻¹ : R), by rwa [mul_smul]⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The connected–étale line of the flat package at `3`** (PROVEN
2026-07-26 over the single Raynaud leaf
`exists_connected_line_generator_of_hopf_package` just above; was a SORRY
LEAF, cut 2026-07-25 out of the invariant-functional node
`invariant_functional_defect_vanishes_of_hopf_package` below. It now
carries the WHOLE finite-flat/Fontaine content of that node, and it
mentions no functional at all: it is a statement about `ρ` and its
model alone, so the ω-sibling `omega_defect_coboundary_of_hopf_package`
can consume it too.

**MOVED UP 2026-07-26**, from below `hom_vanishes_on_localInertia_at_two`
to here, because that anticipated ω-consumption became real: it is what
proves `omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale`
just below, and Lean needs it declared first. So this leaf is now the
SHARED finite-flat input of BOTH the ω-defect and the
invariant-functional strata; its ROUTE AUDIT — recorded in the ω-node's
docstring — names what it still owes, namely the classification of the
connected part as a `μ₃`-type line and, for `n ≥ 1`, the schematic
closure of a Galois-stable subgroup as a finite flat closed subgroup
scheme. Tate, *Finite flat group schemes*, §4, in
Cornell–Silverman–Stevens; Raynaud, *Schémas en groupes de type
`(p, …, p)`*, Bull. SMF 102 (1974), 3.3.2–3.3.5; Fontaine, *Il n'y a
pas de variété abélienne sur `ℤ`*, §1.)

**FAITHFULNESS REPAIR, 2026-07-26 — the Galois-stability clause was
`Γ ℚ`-WIDE and is now local at `3`.** As first cut, the second bullet
asserted `ρ g w₁ - E g • w₁ ∈ 𝔪ⁿ⁺²V` for every `g : Γ ℚ`. That is the
development's signature error in its most expensive form: a
`Γ ℚ₃ᵥ`-quantifier widened to all of `Γ`.

* Every input of this leaf that carries finite-flat content is LOCAL at
  `3`: the Hopf algebra `G` lives over `𝒪₃ᵥ`, the idempotent `e₀` is
  `𝒪₃ᵥ`-rational, and the identification `fG` of geometric points is
  `→+[Γ ℚ₃ᵥ]`-equivariant. The connected part `M⁰` it produces is
  therefore `Γ ℚ₃ᵥ`-stable and nothing more; the "Intended proof" below
  never produces anything global either.
* The `Γ ℚ`-wide form is not merely unproven here, it is *unprovable
  here without circularity*: a `Γ ℚ`-stable line in `V/𝔪ⁿ⁺²V` for every
  `n` IS the global reducibility of `ρ`, i.e. the conclusion
  `exists_global_triangular_of_residual_trivial_quotient` at the very
  bottom of this file, which is reached only through the Selmer/Odlyzko
  material (`exists_omega_component_coboundary`,
  `discr_factorization_le_of_forall_inertia_card_dvd`) and through this
  leaf's own consumers. Local flat data at `3` cannot see that
  obstruction: the same Hopf package exists over a base field where the
  corresponding Selmer group does NOT vanish and the analogous `ρ` is
  irreducible.
* It is not FALSE, since `ρ` is in the end globally triangular — which
  is exactly why the error is dangerous: the leaf looked provable and
  would have quietly re-derived the file's main theorem from nothing.

The clause is now stated over `Γ ℚ₃ᵥ`, restricted along
`Field.absoluteGaloisGroup.map`. BOTH consumers were repaired to match
(`omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale` just
below and `invariant_functional_defect_vanishes_of_hopf_package` further
down): each takes its residual (`mod 𝔪`) diagonal entry for the whole of
`Γ ℚ` from a source needing no flat theory (`exists_residual_matrix_entries`,
resp. the hypothesis `a`/`ha`), and takes its distinguished element `g₀`
with `ω g₀ ≠ 1` from `exists_local_cyclotomicCharacterModL_three_ne_one`
above instead of from the global `exists_cyclotomicCharacterModL_three_ne_one`.

Given an EXPLICIT finite flat Hopf algebra `G` over `𝒪ᵥ ≅ ℤ₃` with
étale generic fibre whose geometric points are `Γ ℚ₃ᵥ`-equivariantly
identified with the space `M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` of the congruence
quotient `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)`, the connected–étale sequence of
`Spec G` splits `M` at level `𝔪ⁿ⁺²`:

* a vector `w₁ ≡ w₀ mod 𝔪V` generates the connected part `M⁰`, and
  the line `R · w₁` is `Γ ℚ₃ᵥ`-STABLE modulo `𝔪ⁿ⁺²V` — stable under
  the DECOMPOSITION GROUP AT `3` only, see the faithfulness note above
  — with diagonal entry `E : Γ ℚ₃ᵥ → R`;
* the local inertia at `3` acts TRIVIALLY on the étale quotient
  `M/M⁰`: `ρ σ v₀ ≡ v₀` modulo `R · w₁ + 𝔪ⁿ⁺²V` for every `σ` in
  `localInertiaGroup 3`.

Steps (1) and (2) are now HYPOTHESES, not obligations (2026-07-26,
after merging the rival cut of the consumer): `e₀` with
`he₀`/`hε₀`/`hmin₀`/`habs₀` is the connected counit idempotent as
`Bialgebra.exists_connected_counit_idempotent` produces it, and
`hconn` — PROVEN upstream in
`inertia_displacement_apply_connected_idempotent_eq_one` — says every
inertia displacement at this `σ` is connected, i.e. the étale quotient
has unramified points. So what remains owed below is only (3) and (4):
the identification of `M⁰` with a Galois-stable free line reducing onto
the `w₀`-line.

PROOF, as written below. (1) The connected locus `M⁰ ⊆ M` — the points
`φ` with `φ (1 ⊗ e₀) = 1`, i.e. the geometric points of the connected
component of the identity — is `Γ ℚ₃ᵥ`-STABLE because `e₀` is
`𝒪ᵥ`-rational: `fG` is `Γ ℚ₃ᵥ`-equivariant, `g • φ` is `g.toAlgHom.comp φ`
(this is exactly the rewriting
`displacement_point_apply_idempotent_eq_one` performs), so
`(g • φ) (1 ⊗ e₀) = g (φ (1 ⊗ e₀)) = g 1 = 1`. That is `hstable` below.
(2) `hconn` (equivalently `displacement_point_apply_idempotent_eq_one`,
ibid., PROVEN, and supplied by
`inertia_displacement_apply_connected_idempotent_eq_one`) says the
inertia displacement `(σ ∘ φ) ⋆ φ⁻¹` of ANY point lands in `M⁰`; applied
to the point of `1 ⊗ v₀` and read through the rfl-lemmas
`GaloisRep.toLocal_apply` / `GaloisRep.baseChange_tmul`, it gives the
third bullet the moment `M⁰` is identified with the `w₁`-line. (3) and
(4) — that `M⁰` IS that line, free of rank one over `R ⧸ 𝔪ⁿ⁺²` by
Raynaud's full faithfulness at `e = 1 < p − 1 = 2`, and residually the
`w₀`-line by ordinarity — are the content of the single leaf
`exists_connected_line_generator_of_hopf_package` above, whose docstring
carries the full route for both. Given it, the second bullet is (1)
applied to the connected point `1 ⊗ w₁`, with `E g` read off from the
line membership by choice (no continuity or multiplicativity of `E` is
asserted, and none is used downstream).

The hypothesis `_hσ` is unused by this assembly: everything the
inertia-membership of `σ` contributes enters through `hconn`, which is
its consequence. It is retained in the signature because it is what
makes the third bullet TRUE — a caller instantiating `σ` outside inertia
could not supply `hconn`. -/
theorem exists_connectedEtale_line_of_hopf_package
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
    (n : ℕ)
    (G : Type) [CommRing G]
    [HopfAlgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange
          (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
    (_hσ : σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (hconn : ∀ m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
          𝔭₃) σ m - m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ w₁ : V,
      w₁ - w₀ ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) ∧
      (∃ E : Γ ℚ₃ᵥ → R, ∀ g : Γ ℚ₃ᵥ,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g) w₁ - E g • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) ∧
      (∃ c : R, ρ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) v₀
        - (v₀ + c • w₁) ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)) := by
  classical
  -- the Raynaud content: the connected locus IS a line, generated by a
  -- lift of `w₀` (steps (3) and (4) of the route)
  obtain ⟨w₁, hw₁, hline⟩ :=
    exists_connected_line_generator_of_hopf_package V hV hρ kk hsurj π
      hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG e₀ he₀ hε₀ hmin₀ habs₀
  set gG := Equiv.ofBijective fG hfG with hgG
  have hfs : ∀ x, fG (gG.symm x) = x := fun x => gG.apply_symm_apply x
  -- the generator of the line is itself a connected point
  have hw₁conn :
      (Additive.toMul (gG.symm ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))
          ⊗ₜ[R] w₁))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 :=
    (hline w₁).2 ⟨1, by rw [one_smul, sub_self]; exact Submodule.zero_mem _⟩
  -- step (1): the connected locus is `Γ ℚ₃ᵥ`-stable, because `e₀` is
  -- `𝒪ᵥ`-rational and the Galois action on points is post-composition
  have hstable : ∀ (g : Γ ℚ₃ᵥ)
      (m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V),
      (Additive.toMul (gG.symm m)) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 →
      (Additive.toMul (gG.symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
          g m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1 := by
    intro g m hm
    have hsym : gG.symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
          g m) = g • gG.symm m := by
      apply gG.injective
      show fG (gG.symm _) = fG (g • gG.symm m)
      rw [map_smul fG, hfs, hfs]
      rfl
    rw [hsym]
    have hact : Additive.toMul (g • gG.symm m) =
        (g.toAlgHom : ℚ₃ᵥᵃˡᵍ →ₐ[ℚ₃ᵥ] ℚ₃ᵥᵃˡᵍ).comp
          (Additive.toMul (gG.symm m)) := AlgHom.ext fun _ => rfl
    rw [hact, AlgHom.comp_apply, hm, map_one]
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · -- the diagonal entry of the `Γ ℚ₃ᵥ`-stable line
    have hkey : ∀ g : Γ ℚ₃ᵥ, ∃ r : R,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ₃ᵥ) g) w₁ - r • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
      intro g
      refine (hline _).1 ?_
      have h1 := hstable g _ hw₁conn
      rwa [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul] at h1
    exact ⟨fun g => (hkey g).choose, fun g => (hkey g).choose_spec⟩
  · -- step (2): local inertia acts trivially on the étale quotient
    have h3 := hconn ((1 : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗ₜ[R] v₀)
    rw [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
      ← TensorProduct.tmul_sub] at h3
    obtain ⟨c, hc⟩ := (hline _).1 h3
    exact ⟨c, by rw [← sub_sub]; exact hc⟩

/-- **The ω-defect dies on the cyclotomic kernel of the local inertia at
`3`** (PROVEN 2026-07-26 over the connected–étale line leaf
`exists_connectedEtale_line_of_hopf_package`, which was MOVED UP this
file — it was declared far below, after
`hom_vanishes_on_localInertia_at_two` — so that this node can consume it;
the node itself was cut 2026-07-26 out of
`omega_defect_coboundary_of_hopf_package` below).

**PROOF (2026-07-26).** The `U`/`hUdisp`/`hUfix` hypotheses are NOT used
— the ROUTE AUDIT below proves that they cannot suffice — and the proof
goes back through `hρ.isFlat`, exactly as that audit demands. `𝔪ⁿ⁺²` is
OPEN (compactness and Hausdorffness of `R` transported along a
`ℤ₃`-basis, as in `omega_defect_vanishes_on_localInertia_at_three`), so
`hρ.isFlat.cond` hands over the finite flat model of
`ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` at `3`;
`Bialgebra.exists_connected_counit_idempotent` supplies its connected
counit idempotent `e₀`, and
`inertia_displacement_apply_connected_idempotent_eq_one` the
connectedness of the inertia displacements. That is precisely the input
of `exists_connectedEtale_line_of_hopf_package`, which returns a
generator `w₁ ≡ w₀ mod 𝔪V` of the connected line together with its
diagonal entry `E`, i.e. `ρ g w₁ ≡ E g • w₁ mod 𝔪ⁿ⁺²V` for every
`g ∈ Γ ℚ₃ᵥ` — the DECOMPOSITION GROUP AT `3` only, per that leaf's
faithfulness note. Writing `d g = f (ρ g w₀) − f w₀`:

* wherever the connected line has an entry `e` at `g`, `e − a g ∈ 𝔪`:
  the two triangularisations along `w₁` and along `w₀` agree modulo
  `𝔪V` because `w₁ − w₀ ∈ 𝔪V` (and `ρ g` and the scalars preserve
  `𝔪V`), and `w₁` is residually nonzero, so
  `mem_maximalIdeal_of_smul_mem_smul_top` extracts the scalar. The
  residual entry `a` itself is global input (`ha`) and costs no flat
  theory.
* `f w₁ ∈ 𝔪ⁿ⁺¹`. At an element `g₀` with `ω g₀ ≠ 1` — one exists in the
  decomposition group at `3` by
  `exists_local_cyclotomicCharacterModL_three_ne_one`, which is where it
  has to come from now that the line is only locally stable; the global
  `exists_cyclotomicCharacterModL_three_ne_one` is of no use here —
  `residual_twist_eq_cyclotomicCharacterModL` gives `a g₀ + 1 ∈ 𝔪`,
  hence `E g₀ − 1 ≡ −2 mod 𝔪` is a UNIT (`3 ∈ 𝔪` while `1 ∉ 𝔪`, so `2`
  is a unit — this is the one place `p = 3 > 2` is spent). Stability of
  the line and `hf g₀ w₁` give `(E g₀ − 1) * f w₁ ∈ 𝔪ⁿ⁺¹`.
* `d σ ≡ (E σ − 1) * f w₁ mod 𝔪ⁿ⁺²`, because `w₀ = w₁ − (w₁ − w₀)` and
  the correction `f (ρ σ (w₁ − w₀)) − f (w₁ − w₀)` lies in `𝔪ⁿ⁺²` by
  `linearMap_sub_mem_pow_succ_of_mem_smul_top`.
* Finally `ω σ = 1` gives `a σ − 1 ∈ 𝔪`, hence `E σ − 1 ∈ 𝔪`, and
  `𝔪 · 𝔪ⁿ⁺¹ = 𝔪ⁿ⁺²` closes it.

This is the ω-sibling of
`invariant_functional_defect_vanishes_of_hopf_package` below, which runs
the same moves for the `v₀`-defect of an invariant functional — as the
connected–étale line leaf's own docstring anticipated ("it mentions no
functional at all … so the ω-sibling can consume it too"). The
difference: there BOTH invariance hypotheses are available and give
`Φ w₁ ∈ 𝔪ⁿ⁺²` outright, whereas `hf` alone only gives
`f w₁ ∈ 𝔪ⁿ⁺¹`, and the missing power of `𝔪` is supplied by
`E σ − 1 ∈ 𝔪` — which is exactly what restricting to `ker ω` buys, and
why THIS node is a `ker ω` statement while its sibling is not.

**HYPOTHESIS AUDIT.** Four hypotheses are UNUSED and underscore-prefixed
so that this is mechanically visible: `_hUdisp`, `_hUfix` (the
connected–étale subgroup data, which the ROUTE AUDIT below proves cannot
suffice — they are kept only so that the consumer's call site does not
have to change) and `_hfv₀` (the proof never needs `f v₀` to be a unit:
the unit it actually spends is `E g₀ − 1`, at an element OFF the
cyclotomic kernel). `U` itself is still named because the types of
`_hUdisp`/`_hUfix` mention it.

Everything below is the record of the cut as it stood while this node
was open. Its ROUTE AUDIT is still correct and still binding, but it now
applies to `exists_connectedEtale_line_of_hopf_package` rather than to
this node: the classification content it names is what that leaf owes.

This is the whole remaining content of BOTH that theorem and its
consumer `omega_defect_vanishes_of_hopf_package`: by
`exists_coboundary_of_cocycle_of_vanishing_on_cyclotomicKernel` the
coboundary conclusion is equivalent to its own `ker ω` specialisation,
which is this statement.

`U` is the group of geometric points of the connected part `G⁰` of the
finite flat prolongation at level `𝔪ⁿ⁺²`, with (i) `hUdisp`, every
inertia displacement is connected — the étale quotient `G/G⁰` has
unramified points — and (ii) `hUfix`, the connected part has no nonzero
inertia-fixed vector — the kernel of reduction over the absolutely
unramified `𝒪ⁿʳ` is torsion-free at `3`, `e = 1 < 2 = p − 1`. Both are
PROVEN upstream (`inertia_displacement_apply_connected_idempotent_eq_one`
and `exists_connectedEtale_subgroup_at_three_of_threePowTorsion`) and
discharged by the consumer below.

**ROUTE AUDIT (2026-07-26) — what is still missing, and a proof that
`U` alone cannot supply it.** Fix an `R`-basis `(v₀, w₀)` of `V` (the two
vectors ARE a basis: `hw₀ne`/`hw₀π`/`hv₀` make their images a `kk`-basis
of `kk ⊗ V`, and `V` is free of rank `2`), and write the matrix of `ρ` in
it as `ρ g v₀ = α g · v₀ + γ g · w₀`, `ρ g w₀ = β g · v₀ + A g · w₀`, so
that `hπequiv` gives `α g ≡ 1`, `ha` gives `β g ∈ 𝔪`, and
`residual_twist_eq_cyclotomicCharacterModL` gives `A g ≡ ω g` — all
modulo `𝔪`. Then

  `d g = f (ρ g w₀) − f w₀ = β g · f v₀ + (A g − 1) · f w₀`,

and, `f v₀` being a unit, the conclusion here is EXACTLY the
proportionality

  `β σ · (A σ₁ − 1) ≡ (A σ − 1) · β σ₁    (mod 𝔪ⁿ⁺²)`,

for `σ` in `ker ω ∩ I₃` and any fixed `σ₁ ∈ I₃` off `ker ω`. That is the
splitting of the extension `0 → ℤ/3 ⊗ (𝔪ⁿ⁺¹⧸𝔪ⁿ⁺²) → E → μ₃ → 0` of the
ORIENTATION AUDIT below — the class `β` measured against the `μ₃`-line —
i.e. `Ext¹_{fl,ℤ₃}(μ₃, ℤ/3) = 0`.

The audit's point is that `hUdisp` + `hUfix` are provably NOT enough, so
a prover must go back through `hρ.isFlat`: they are both satisfied by
`U = ⊤` together with `Mᴵ³ = 0` (no nonzero inertia-fixed vector at all),
a configuration that constrains `β` not at all, and which the arithmetic
hypotheses do not exclude — residually it only asks that the extension
`0 → kk(ω) → V̄ → kk → 0` be *très ramifié*. What excludes it is that
`G⁰` is a finite flat SUBGROUP SCHEME whose graded pieces are of
`μ₃`-type, and hence cannot surject onto the trivial residual quotient
cut out by `π`. Concretely the two inputs `U` cannot see are:

* the CLASSIFICATION of the connected part (`U` is a `μ`-type line, not
  just some subgroup) — upstream this exists only for points killed by
  `3` and carrying an inertia-stable cyclic span
  (`OortTate.exists_muType_coordinate`, whose `hstab` is genuinely
  needed; the displacements `σ w̄₀ − w̄₀` do NOT span an inertia-stable
  cyclic group), and
* the SCHEMATIC CLOSURE of a Galois-stable subgroup of the generic fibre
  as a finite flat closed subgroup scheme, which is what turns the
  SUBQUOTIENT `E` above into a group scheme one may classify. The tree
  does not have it in any form. For `n = 0` the subquotient is a genuine
  SUBGROUP (`𝔪 · M` is killed by `3` when `𝔪² · M = 0`) and the closure
  is not needed; for `n ≥ 1` it is, because over `R = ℤ₃` one has
  `M[3] = 𝔪ⁿ⁺¹ M`, on which every statement below is already trivial.

So this leaf is NOT a repackaging of the group-scheme facts already in
the tree: it needs new theory, and the named prerequisite is the
schematic closure. -/
theorem omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale
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
    (_hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (U : AddSubgroup ((R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V))
    (_hUdisp : ∀ σ ∈ localInertiaGroup 𝔭₃,
      ∀ m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
      ((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
        σ m - m ∈ U)
    (_hUfix : ∀ u ∈ U, (∀ σ ∈ localInertiaGroup 𝔭₃,
        ((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal 𝔭₃)
          σ u = u) → u = 0)
    (σ : Γ ℚ₃ᵥ) (hσ : σ ∈ localInertiaGroup 𝔭₃)
    (hσω : cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) :
    f (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀)
      - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- the image of `σ` in the global Galois group
  set σ' : Γ ℚ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ with hσ'def
  -- `𝔪ⁿ⁺²` is OPEN: transport compactness along a `ℤ₃`-basis
  haveI hNoeth : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  let eR : R ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    (Module.Free.chooseBasis ℤ_[3] R).equivFun
  have hcont₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcont₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let homR : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  haveI : CompactSpace R := homR.symm.compactSpace
  haveI : T2Space R := homR.symm.symm.isEmbedding.t2Space
  have hIopen : IsOpen
      ((IsLocalRing.maximalIdeal R ^ (n + 2) : Ideal R) : Set R) :=
    IsLocalRing.isOpen_maximalIdeal_pow R (n + 2)
  -- the finite flat model of the congruence quotient at `3`
  have hflat : (ρ.baseChange
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
    hρ.isFlat.cond (IsLocalRing.maximalIdeal R ^ (n + 2)) hIopen
  obtain ⟨G, i1, i2, i3, i4, i5, fG, hfG⟩ := hflat
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  -- its connected counit idempotent
  obtain ⟨e₀, he₀, hε₀, hmin₀, habs₀⟩ :=
    Bialgebra.exists_connected_counit_idempotent (A := 𝒪₃ᵥ) (G := G)
  -- the connected–étale line of the model: a generator `w₁ ≡ w₀ mod 𝔪V`
  -- spanning a `Γ ℚ₃ᵥ`-stable line modulo `𝔪ⁿ⁺²V`, with diagonal entry `E`
  -- (the leaf's stability clause is LOCAL at `3`, see its faithfulness note)
  obtain ⟨w₁, hw₁, ⟨E, hE⟩, -⟩ :=
    exists_connectedEtale_line_of_hopf_package V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG σ hσ e₀ he₀ hε₀ hmin₀ habs₀
      (fun m => inertia_displacement_apply_connected_idempotent_eq_one
        (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
        fG hfG σ hσ m)
  -- `w₁` is residually nonzero, like `w₀`
  have hw₁ne : (1 : kk) ⊗ₜ[R] w₁ ≠ 0 := by
    have h0 : (1 : kk) ⊗ₜ[R] (w₁ - w₀) = 0 :=
      one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj hw₁
    rw [TensorProduct.tmul_sub, sub_eq_zero] at h0
    rw [h0]
    exact hw₀ne
  -- the deeper congruence sublattice sits inside `𝔪V`
  have hmle : (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) ≤
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
    Submodule.smul_le.2 fun r hr v _ =>
      Submodule.smul_mem_smul (Ideal.pow_le_self (by omega) hr) trivial
  -- the two triangularisations agree residually, wherever the connected line
  -- HAS a diagonal entry. Since the leaf's stability clause is local at `3`,
  -- this is parametrised by the entry `e` rather than by `E` itself; the
  -- residual entry `a` is global input (`ha`) and needs no flat theory.
  have hEa : ∀ (g : Γ ℚ) (e : R),
      ρ g w₁ - e • w₁ ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) →
      e - a g ∈ IsLocalRing.maximalIdeal R := by
    intro g e he
    refine mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₁ne ?_
    have hexp : (e - a g) • w₁ =
        ((ρ g w₀ - a g • w₀) + (ρ g (w₁ - w₀) - a g • (w₁ - w₀)))
          - (ρ g w₁ - e • w₁) := by
      simp only [map_sub, sub_smul, smul_sub]
      abel
    rw [hexp]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (ha g) ?_) (hmle he)
    exact Submodule.sub_mem _ (apply_mem_smul_top (ρ g) hw₁)
      (Submodule.smul_mem _ _ hw₁)
  -- the residual identification of the twist `a` with `ω`
  have hres := fun g : Γ ℚ =>
    residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha g
  -- off the cyclotomic kernel the diagonal entry is `≡ -1`, so `entry - 1`
  -- is a unit: `2` is invertible because `3 ∈ 𝔪`. The distinguished element
  -- must come from the DECOMPOSITION GROUP AT `3`, where the connected line
  -- has an entry at all, so it is produced by
  -- `exists_local_cyclotomicCharacterModL_three_ne_one` and not by the global
  -- `exists_cyclotomicCharacterModL_three_ne_one`.
  obtain ⟨g₀, Eg₀, hg₀, hEg₀⟩ :
      ∃ (g : Γ ℚ) (e : R), cyclotomicCharacterModL 3 g ≠ 1 ∧
        ρ g w₁ - e • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
    obtain ⟨g, hg⟩ := exists_local_cyclotomicCharacterModL_three_ne_one
    exact ⟨_, E g, hg, hE g⟩
  have hunit : IsUnit (Eg₀ - 1) := by
    have hnot : Eg₀ - 1 ∉ IsLocalRing.maximalIdeal R := by
      intro hmem
      have h1 : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R := (hres g₀).2 hg₀
      have h2 : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
        have h3 : ((Eg₀ - a g₀) - (Eg₀ - 1)) + (a g₀ + 1) = (2 : R) := by ring
        rw [← h3]
        exact Ideal.add_mem _
          (Ideal.sub_mem _ (hEa g₀ Eg₀ hEg₀) hmem) h1
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have h4 : (3 : R) - (2 : R) = 1 := by norm_num
        rw [← h4]
        exact Ideal.sub_mem _ three_mem_maximalIdeal h2
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h3
      exact h3 isUnit_one
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hnot
  -- the functional is deep on the connected line
  have hfw₁ : f w₁ ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
    have hz : f (ρ g₀ w₁ - Eg₀ • w₁) ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) :=
      linearMap_apply_mem_of_mem_smul_top f hEg₀
    have hkey : (Eg₀ - 1) * f w₁ ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
      have hexp : (Eg₀ - 1) * f w₁ =
          (f (ρ g₀ w₁) - f w₁) - f (ρ g₀ w₁ - Eg₀ • w₁) := by
        rw [map_sub, map_smul, smul_eq_mul]
        ring
      rw [hexp]
      exact Ideal.sub_mem _ (hf g₀ w₁) (Ideal.pow_le_pow_right (by omega) hz)
    obtain ⟨u, hu⟩ := hunit
    have heq : f w₁ = (↑u⁻¹ : R) * ((Eg₀ - 1) * f w₁) := by
      rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hkey
  -- on the cyclotomic kernel the diagonal entry is `≡ 1`. `σ` itself lies in
  -- `Γ ℚ₃ᵥ`, so the leaf's LOCAL entry is defined there and `E σ` is it.
  have hEσ' : ρ σ' w₁ - E σ • w₁ ∈
      (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := hE σ
  have hEσ : E σ - 1 ∈ IsLocalRing.maximalIdeal R := by
    have h1 : a σ' - 1 ∈ IsLocalRing.maximalIdeal R := (hres σ').1 hσω
    have h2 : E σ - 1 = (E σ - a σ') + (a σ' - 1) := by ring
    rw [h2]
    exact Ideal.add_mem _ (hEa σ' (E σ) hEσ') h1
  -- the defect follows the line
  have hgoal : f (ρ σ' w₀) - f w₀ =
      (f (ρ σ' w₁) - f w₁) - (f (ρ σ' (w₁ - w₀)) - f (w₁ - w₀)) := by
    simp only [map_sub]
    ring
  rw [hgoal]
  refine Ideal.sub_mem _ ?_
    (linearMap_sub_mem_pow_succ_of_mem_smul_top (ρ σ') (hf σ') hw₁)
  have hz : f (ρ σ' w₁ - E σ • w₁) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) :=
    linearMap_apply_mem_of_mem_smul_top f hEσ'
  have hexp : f (ρ σ' w₁) - f w₁ =
      f (ρ σ' w₁ - E σ • w₁) + (E σ - 1) * f w₁ := by
    rw [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hexp]
  refine Ideal.add_mem _ hz ?_
  have h4 := Ideal.mul_mem_mul hEσ hfw₁
  rwa [← pow_succ'] at h4

/-- **The ω-defect is an `ω`-coboundary on the local inertia at `3`**
(sorry node, isolated 2026-07-25 out of the ω-defect Hopf-package core
below — the finite-flat/Raynaud content in its sharp, UNCONDITIONAL
form; Fontaine, Raynaud 1974, and the Fontaine/Raynaud material in
Cornell–Silverman–Stevens): given an EXPLICIT finite flat Hopf algebra
`G` over `𝒪ᵥ ≅ ℤ₃` with étale generic fibre whose geometric points are
`Γ ℚ₃ᵥ`-equivariantly identified with the space `(R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` of
the congruence quotient `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)`, there is a SINGLE
`lam ∈ 𝔪ⁿ⁺¹` such that on the WHOLE local inertia at `3` the ω-defect
`d σ = f (ρ σ w₀) - f w₀` is the `ω`-twisted coboundary
`-(a σ - 1) * lam` modulo `𝔪ⁿ⁺²`.

Intended proof (steps (1)–(4) of the core below, run to their sharp
conclusion): (1) transport the `R ⧸ 𝔪ⁿ⁺²`-module structure of
`M := (R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` across the package bijection `fG`, so `M`
with its local Galois action is the group of geometric points of the
generic fibre of the finite flat `ℤ₃`-group scheme `Spec G`; (2) the
cyclic Galois submodule of `M` generated by the image of `w₀` (stable
modulo each congruence level by `ha` and the residual triangular
shape) has a schematic closure `H ⊆ Spec G`, a finite flat closed
subgroup scheme whose graded pieces along the `𝔪`-filtration are of
multiplicative (`μ₃`-)type — the residual `w₀`-character `a mod 𝔪` is
the mod-3 cyclotomic `ω` and Raynaud's order-`3` classification over
`ℤ₃` (`e = 1 < 2 = p - 1`) has exactly the `ℤ/3`-forms (étale,
unramified points) and the `μ₃`-forms (connected); (3) on the graded
piece `𝔪ⁿ⁺¹/𝔪ⁿ⁺²` the assignment `σ ↦ d σ` is an `ω`-twisted cocycle
(the twist is `ha` plus the residual multiplicativity of `a`) whose
class is the generic-fibre class of the extension of the `μ₃`-type
piece (the `w₀`-line) by the étale-type piece (the trivial `v₀`-quotient
coordinate cut out by `f`) inside `Spec G`; (4) every finite flat
extension `E` of `μ₃`-type by étale-type over `ℤ₃` splits: its
connected component `E⁰` meets the étale sub trivially
(connected ∩ étale = 1) and maps onto the `μ₃`-part (the cokernel of
`E⁰ → μ₃` is simultaneously a quotient of the connected `μ₃` and a
subquotient of the étale `E/E⁰`, hence trivial), so `E⁰ → μ₃` is an
isomorphism providing a splitting. A splitting of an `ω`-twisted
extension is EXACTLY a vector `lam` of the graded piece with
`d σ ≡ -(a σ - 1) * lam`, which is the statement here.

Note the shape: this is precisely the hypothesis `hsA` that the
trivial-component stratum consumes downstream, and the `ker ω`
statement of the consumer below is its specialisation at `a σ ≡ 1`.

CONNECTED–ÉTALE HALF ALREADY SUPPLIED (2026-07-25, reconciling the two
rival cuts of this node): the connected counit idempotent `e₀` of the
Hopf order — with `hmin₀`/`habs₀` characterising it as the coordinate
ring of the identity component, exactly as
`Bialgebra.exists_connected_counit_idempotent` produces it — and
`hconn`, the statement that EVERY inertia displacement is connected, are
hypotheses here rather than obligations. `hconn` is PROVEN upstream in
`inertia_displacement_apply_connected_idempotent_eq_one` and discharged
by the consumer below. So step (2) of the route above is DONE, and what
this leaf still owes is only steps (2b)–(4), the Raynaud CLASSIFICATION
content.

**STATUS 2026-07-26 (updated later the same day).** This theorem is
SORRY-FREE in itself, and so is its
`omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale` leaf
above, which was PROVEN by going back through `hρ.isFlat` and consuming
`exists_connectedEtale_line_of_hopf_package` — the shared connected–étale
line leaf, now declared above this block. So the whole remaining content
of this stratum sits in THAT leaf, and the ROUTE AUDIT recorded in the
ω-node's docstring (what is missing, and a proof that the
connected–étale SUBGROUP alone cannot supply it) is what that leaf owes.
Proved
already: `omega_defect_cocycle` (the defect really is an `ω`-twisted
cocycle modulo `𝔪ⁿ⁺²` — step (3)'s cocycle claim),
`exists_coboundary_of_cocycle_of_vanishing_on_cyclotomicKernel` (such a
cocycle is a coboundary as soon as it vanishes on `ker ω`, because `ω`
has order `2` and `2` is a unit of `R`), and — new on 2026-07-26 — the
CONGRUENCE-LEVEL connected–étale sequence of the model:
`inertiaFixed_connected_point_eq_one_at_three_of_threePow` (the Raynaud
leaf at any `3`-power order, not just order `3`),
`inertiaFixed_connected_vector_eq_zero_of_hopf_package` and
`exists_connectedEtale_subgroup_at_three_of_threePowTorsion` (the
analogue of ModThree's `exists_connectedEtale_subgroup_of_hopf_package`
over a coefficient module killed by a power of `3` rather than by `3`).
So step (2b) — "`G⁰` absorbs the inertia displacements and meets the
inertia-fixed vectors trivially" — is DONE at level `𝔪ⁿ⁺²`, and what
the leaf still owes is only the CLASSIFICATION of `G⁰` as a `μ₃`-type
line, whose named prerequisite is the schematic closure of a
Galois-stable subgroup as a finite flat closed subgroup scheme.

**ORIENTATION AUDIT (2026-07-25) — this is the true/false hinge of
step (4), so it must be stated explicitly rather than left to the phrase
"extension of `μ₃`-type by étale-type".** The extension that carries the
defect is the schematic closure of the Galois submodule generated by
`w₀`. Its SUB is the higher-filtration piece cut out by `f`, on which
Galois acts trivially — étale, `ℤ/3`-type; its QUOTIENT is the residual
`w₀`-line, on which Galois acts by `ω` — multiplicative, `μ₃`-type. So
the object is `0 → ℤ/3 → E → μ₃ → 0`, and it is `Ext¹(μ₃, ℤ/3) = 0` over
`ℤ₃` — precisely the connected–étale argument written in step (4) — that
kills it. The OPPOSITE orientation `0 → μ₃ → V̄ → ℤ/3 → 0` (the residual
representation itself) has `Ext¹ ≅ ℤ₃ˣ/(ℤ₃ˣ)³ ≅ ℤ/3 ≠ 0`: Serre's *peu
ramifié* classes, which are nonzero and stay nonzero on inertia (for
`u ∈ ℤ₃ˣ` not a cube, `ℚ₃(u^{1/3})/ℚ₃` is totally ramified). Both
extensions live in the same group `H¹(ℚ₃, kk(ω))`; only the
group-scheme structure distinguishes them, so the statement here would
be FALSE if the two roles were swapped. (The same contrast is recorded
independently downstream at `Modularity/Interface.lean:14809`.) -/
theorem omega_defect_coboundary_of_hopf_package
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
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (G : Type) [CommRing G]
    [HopfAlgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange
          (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (hconn : ∀ σ ∈ localInertiaGroup 𝔭₃,
      ∀ m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
          𝔭₃) σ m - m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    ∃ lam : R, lam ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ∧
      ∀ σ ∈ localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
        (f (ρ (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀)
          - f w₀)
          + (a (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) - 1)
            * lam
          ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  -- the two-sided residual identification of the twisting function `a`
  -- with the mod-3 cyclotomic character `ω`
  have hres := fun g : Γ ℚ =>
    residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha g
  -- the connected counit idempotent is primitive, and its comultiplication
  -- absorbs `e₀ ⊗ e₀` — the two forms the connected-locus block wants
  have hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀ :=
    fun x hx => mul_eq_zero_or_mul_eq_of_minimal he₀ hε₀ hmin₀ x hx
  have hcomul₀ : Coalgebra.comul (R := 𝒪₃ᵥ) e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) =
      e₀ ⊗ₜ[𝒪₃ᵥ] e₀ := by
    rwa [Bialgebra.comulAlgHom_apply] at habs₀
  -- the congruence quotient is killed by `3 ^ (n + 2)`, since `3 ∈ 𝔪`
  have hNtors : ∀ m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
      (3 ^ (n + 2) : ℕ) • m = 0 := by
    have hann : ∀ r : R, r ∈ IsLocalRing.maximalIdeal R ^ (n + 2) →
        ∀ u : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V, r • u = 0 := by
      intro r hr u
      induction u using TensorProduct.induction_on with
      | zero => rw [smul_zero]
      | tmul x w =>
        rw [TensorProduct.smul_tmul']
        have hx0 : r • x = 0 := by
          rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
            show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2)) r = 0
              from Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
        rw [hx0, TensorProduct.zero_tmul]
      | add x y hx hy => rw [smul_add, hx, hy, add_zero]
    intro m
    have hcast : ((3 ^ (n + 2) : ℕ) : R) • m = (3 ^ (n + 2) : ℕ) • m :=
      Nat.cast_smul_eq_nsmul R _ m
    rw [← hcast]
    refine hann _ ?_ m
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow
      (by exact_mod_cast (three_mem_maximalIdeal : (3 : R) ∈ _)) _
  -- the connected–étale subgroup of the model at level `𝔪 ^ (n + 2)`: the
  -- points of `G⁰`, absorbing every inertia displacement (`hconn`) and
  -- containing no nonzero inertia-fixed vector (the Raynaud leaf)
  obtain ⟨U, hUdisp, hUfix⟩ :=
    exists_connectedEtale_subgroup_at_three_of_threePowTorsion
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      hprim₀ hcomul₀ fG hfG (n + 2) hNtors hconn
  -- the remaining finite-flat (Raynaud) CLASSIFICATION content
  have hker : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 →
      f (ρ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀)
        - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) :=
    fun σ hσ hσω =>
      omega_defect_vanishes_on_cyclotomicKernel_of_connectedEtale V hV hρ kk
        hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha n f hf hfv₀ U hUdisp
        hUfix σ hσ hσω
  exact exists_coboundary_of_cocycle_of_vanishing_on_cyclotomicKernel
    (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
    (localInertiaGroup Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    n a (fun g => f (ρ g w₀) - f w₀) (fun g => hf g w₀)
    (fun g h => omega_defect_cocycle ha hf g h)
    (fun g hg => (hres g).1 hg) (fun g hg => (hres g).2 hg) hker

/-- **The ω-defect Hopf-package core at `3`** (DECOMPOSED 2026-07-25
into the splitting leaf `omega_defect_coboundary_of_hopf_package`
above — the finite-flat/Raynaud content; the `ker ω` specialisation is
PROVEN here from the residual determinant identification
`residual_twist_eq_cyclotomicCharacterModL`: `ω σ = 1` forces
`a σ - 1 ∈ 𝔪`, so the coboundary term `(a σ - 1) * lam` lies in
`𝔪 · 𝔪ⁿ⁺¹ = 𝔪ⁿ⁺²` and the defect follows it there. Fontaine,
Raynaud 1974, and the Fontaine/Raynaud material in
Cornell–Silverman–Stevens): given an EXPLICIT finite flat Hopf
algebra `G` over `𝒪ᵥ ≅ ℤ₃` with étale generic fibre whose geometric
points are `Γ ℚ₃ᵥ`-equivariantly identified with the space
`(R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` of the congruence quotient
`ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` (the witness packaged by
`GaloisRep.HasFlatProlongationAt`, extracted by the consumer from
`hρ.isFlat` at the open ideal `𝔪ⁿ⁺²`), the ω-defect
`d σ = f (ρ σ w₀) - f w₀` lands in `𝔪ⁿ⁺²` for every `σ` in the local
inertia at `3` whose image lies in the mod-3 cyclotomic kernel.
The finite-flat content — steps (1)–(4): schematic closure of the
`w₀`-line, Raynaud's `e = 1 < p − 1` classification, the extension
class on the graded piece `𝔪ⁿ⁺¹/𝔪ⁿ⁺²`, and the splitting of every
`μ₃`-by-étale extension over `ℤ₃` — now lives in the leaf above. -/
theorem omega_defect_vanishes_of_hopf_package
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
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (G : Type) [CommRing G]
    [HopfAlgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange
          (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    (hσω : cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) :
    f (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀)
      - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  -- the image of `σ` in the global Galois group
  set σ' : Γ ℚ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ with hσ'
  -- the connected counit idempotent of the Hopf order
  obtain ⟨e₀, he₀, hε₀, hmin₀, habs₀⟩ :=
    Bialgebra.exists_connected_counit_idempotent (A := 𝒪₃ᵥ) (G := G)
  -- the splitting of the `ω`-by-trivial extension on the whole inertia, with
  -- the connected–étale half discharged upstream
  obtain ⟨lam, hlam, hsplit⟩ := omega_defect_coboundary_of_hopf_package V hV hρ
    kk hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha n f hf hfv₀ G fG hfG
    e₀ he₀ hε₀ hmin₀ habs₀
    (fun τ hτ m => inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG τ hτ m)
  have h1 := hsplit σ hσ
  rw [← hσ'] at h1
  -- the residual diagonal entry is the mod-3 cyclotomic character, so the
  -- coboundary term dies at level `n + 2` on the cyclotomic kernel
  have h2 : a σ' - 1 ∈ IsLocalRing.maximalIdeal R :=
    (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha σ').1 hσω
  have h3 : (a σ' - 1) * lam ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have h4 := Ideal.mul_mem_mul h2 hlam
    rwa [← pow_succ'] at h4
  have heq : f (ρ σ' w₀) - f w₀ =
      ((f (ρ σ' w₀) - f w₀) + (a σ' - 1) * lam) - (a σ' - 1) * lam := by ring
  rw [heq]
  exact Ideal.sub_mem _ h1 h3

set_option backward.isDefEq.respectTransparency false in
/-- **The ω-defect dies on the local inertia at `3`** (DECOMPOSED
2026-07-24 into the Hopf-package core
`omega_defect_vanishes_of_hopf_package` above — the
finite-flat/Fontaine content; the flatness-to-package assembly is
PROVEN here): for `σ` in the local inertia at `3` whose image lies in
the cyclotomic kernel, the defect `d σ = f (ρ σ w₀) - f w₀` lands in
`𝔪ⁿ⁺²`. Assembly: `𝔪ⁿ⁺²` is OPEN (`IsLocalRing.isOpen_maximalIdeal_pow`
after transporting compactness and Hausdorffness along a `ℤ₃`-basis,
exactly as in the continuity stratum
`isOpen_setOf_forall_sub_mem_pow_smul`), so `hρ.isFlat.cond` provides
the finite flat prolongation of `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` at `3`;
unpacking the `GaloisRep.HasFlatProlongationAt` witness hands the
explicit Hopf package to the core. -/
theorem omega_defect_vanishes_on_localInertia_at_three
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
    (hfv₀ : f v₀ ∉ IsLocalRing.maximalIdeal R)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    (hσω : cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) :
    f (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀)
      - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- `𝔪ⁿ⁺²` is open: transport compactness along a `ℤ₃`-basis
  haveI hNoeth : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  let eR : R ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    (Module.Free.chooseBasis ℤ_[3] R).equivFun
  have hcont₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcont₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let homR : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  haveI : CompactSpace R := homR.symm.compactSpace
  haveI : T2Space R := homR.symm.symm.isEmbedding.t2Space
  have hIopen : IsOpen
      ((IsLocalRing.maximalIdeal R ^ (n + 2) : Ideal R) : Set R) :=
    IsLocalRing.isOpen_maximalIdeal_pow R (n + 2)
  -- the finite flat prolongation at the congruence level `n + 2`
  have hflat : (ρ.baseChange
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
    hρ.isFlat.cond (IsLocalRing.maximalIdeal R ^ (n + 2)) hIopen
  -- unpack the Hopf package and hand it to the core
  obtain ⟨G, i1, i2, i3, i4, i5, fG, hfG⟩ := hflat
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  exact omega_defect_vanishes_of_hopf_package V hV hρ kk hsurj π hπsurj
    hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha n f hf hfv₀ G fG hfG σ hσ hσω

/-- **The mod-3 cyclotomic character is unramified outside `3`**
(PROVEN 2026-07-24 — `ℚ(ζ₃)/ℚ` is unramified at every `p ≠ 3`): the
image in `Γ ℚ` of the local inertia group at a prime `p ≠ 3` lies in
the kernel of the mod-3 cyclotomic character. Route:
`localInertiaGroup` consists of
the automorphisms acting trivially modulo the maximal ideal `𝔪` of the
integral closure of `𝒪ᵥ` in `ℚ̄ᵥ`; the chosen embedding
`ι : ℚ̄ →ₐ ℚ̄ᵥ` underlying `Field.absoluteGaloisGroup.map`
(`IsAlgClosed.lift`, compatibility `AlgHom.restrictNormal_commutes` —
see `Field.absoluteGaloisGroup.mapAux`) sends a primitive cube root
`ζ` to a primitive cube root `ι ζ`, integral over `𝒪ᵥ`; `σ` permutes
the primitive cube roots `{ι ζ, (ι ζ)²}`, and `σ (ι ζ) = (ι ζ)²`
would put `(ι ζ)² - ι ζ = -ι ζ · (1 - ι ζ)` in `𝔪` with `ι ζ` a
unit, hence `1 - ι ζ ∈ 𝔪`; but `(1 - ζ)(1 - ζ²) = 3` is a unit of
`𝒪ᵥ` for `p ≠ 3` (`isUnit_natCast_adicCompletionIntegers`), so
`1 - ι ζ` is a unit — contradiction. Hence `σ` fixes `ι ζ`, so
`map σ` fixes `ζ`, and `modularCyclotomicCharacter.unique` evaluates
the character to `1` (compare `cyclotomicCharacterModL_eq_one` in
`Chebotarev.lean`). -/
theorem cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 3)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hp.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat) :
    cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
  classical
  revert σ hσ
  set v := hp.toHeightOneSpectrumRingOfIntegersRat
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v :=
    algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f
  intro σ hσ
  -- a primitive cube root of unity in `ℚ̄` and its image downstairs
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3
  have hη : IsPrimitiveRoot (ι ζ) 3 := hζ.map_of_injective ι.injective
  -- the inertia element fixes `ζ`
  have hfix : Field.absoluteGaloisGroup.map f σ ζ = ζ := by
    have hmapζ3 : (Field.absoluteGaloisGroup.map f σ ζ) ^ 3 = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, hi3, hiζ⟩ := hζ.eq_pow_of_pow_eq_one hmapζ3
    interval_cases i
    · -- `map f σ ζ = 1` would force `ζ = 1`
      rw [pow_zero] at hiζ
      exact absurd ((Field.absoluteGaloisGroup.map f σ).injective
        (by rw [map_one, ← hiζ])) (hζ.ne_one (by norm_num))
    · rw [pow_one] at hiζ
      exact hiζ.symm
    · -- `map f σ ζ = ζ²`: `σ` moves `ι ζ` to its square, which the
      -- inertia congruence forbids since `(1 - ζ)(1 - ζ²) = 3` is a
      -- `v`-adic unit for `p ≠ 3`
      exfalso
      haveI hVR : ValuationRing (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
        valuationRing_integralClosure v
      haveI hLoc : IsLocalRing (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
        inferInstance
      have hση : σ (ι ζ) = ι ζ * ι ζ := by
        have hL := Field.absoluteGaloisGroup.lift_map f σ ζ
        rw [← hiζ] at hL
        rw [← hL, pow_two, map_mul]
      -- move into the integral closure of `𝒪ᵥ`
      have hint : IsIntegral
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (ι ζ) := by
        refine ⟨Polynomial.X ^ 3 - Polynomial.C 1,
          Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
        simp [hη.pow_eq_one]
      set x : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
        ⟨ι ζ, hint⟩ with hx
      set j := algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) with hj
      have hjinj : Function.Injective j := fun a b h => Subtype.ext h
      have hjx : j x = ι ζ := rfl
      -- `x` is a unit: `x³ = 1`
      have hx3 : x * x * x = 1 := by
        apply hjinj
        rw [map_mul, map_mul, map_one, hjx]
        linear_combination hη.pow_eq_one
      have hxunit : IsUnit x :=
        IsUnit.of_mul_eq_one (x * x) (by rw [← mul_assoc]; exact hx3)
      -- the inertia congruence: `x·(x - 1) = σ • x - x ∈ 𝔪`
      have hfac : x * (x - 1) ∈ IsLocalRing.maximalIdeal
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
        have h2 : σ • x - x ∈ IsLocalRing.maximalIdeal
            (IntegralClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
              (AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) :=
          (AddSubgroup.mem_inertia.mp hσ) x
        have hsmul : σ • x = x * x := by
          apply hjinj
          have h1 : j (σ • x) = σ (ι ζ) := by
            show (σ • x).1 = σ (ι ζ)
            rw [IntegralClosure.coe_smul]
            rfl
          rw [h1, hση, map_mul, hjx]
        rw [hsmul] at h2
        have hring : x * x - x = x * (x - 1) := by ring
        rwa [hring] at h2
      -- primality peels off the unit factor
      have hx1 : x - 1 ∈ IsLocalRing.maximalIdeal
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
        rcases (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_or_mem
          hfac with h | h
        · exact absurd hxunit
            (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp h))
        · exact h
      -- `3 = (1 - x)(1 - x²)` lands in `𝔪` …
      have h3eq : (((3 : ℕ)) : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
          = (1 - x) * (1 - x * x) := by
        apply hjinj
        rw [map_natCast, map_mul, map_sub, map_sub, map_one, map_mul, hjx]
        have hsum : 1 + ι ζ + ι ζ * ι ζ = 0 := by
          have h := hη.geom_sum_eq_zero (by norm_num)
          rw [Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, Finset.sum_range_zero] at h
          rw [pow_zero, pow_one] at h
          linear_combination h
        have hcube : (ι ζ) ^ 3 = 1 := hη.pow_eq_one
        push_cast
        linear_combination hsum - hcube
      have h3mem : (((3 : ℕ)) : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∈
          IsLocalRing.maximalIdeal _ := by
        rw [h3eq]
        refine Ideal.mul_mem_right _ _ ?_
        have hneg : (1 : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)))
            - x = -(x - 1) := by ring
        rw [hneg]
        exact neg_mem hx1
      -- … but `3` is a unit of `𝒪ᵥ` for `p ≠ 3`
      have h3unit : IsUnit (((3 : ℕ)) : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
        have h1 := isUnit_natCast_adicCompletionIntegers
          Nat.prime_three hp (Ne.symm hne)
        have h2 := h1.map (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
        rwa [map_natCast] at h2
      exact (mem_nonunits_iff.mp
        ((IsLocalRing.mem_maximalIdeal _).mp h3mem)) h3unit
  -- `map f σ` fixes every cube root of unity, so the character is `1`
  have hone : (1 : ZMod 3) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) (Field.absoluteGaloisGroup.map f σ)) := by
    refine modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) _ _
      fun t ht => ?_
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    have ht3 : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    obtain ⟨i, hi3, hiζ⟩ := hζ.eq_pow_of_pow_eq_one ht3
    show Field.absoluteGaloisGroup.map f σ
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [← hiζ, map_pow, hfix]
  have hid : modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) (Field.absoluteGaloisGroup.map f σ))
      = cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map f σ) := rfl
  refine Units.ext ?_
  rw [← hid, ← hone]
  rfl

open NumberField in
set_option backward.isDefEq.respectTransparency false in
/-- **The discriminant exponent from an inertia-order bound** (PROVEN
2026-07-24 — the per-prime glue of the Kummer-core discriminant route,
the generalization of `ModThree`'s `kernel_field_discr_two_exponent`
glue from `(p, m) = (2, 3)` to any tame pair): for a Galois number
field `K`, a rational prime `p` and a modulus `m` with `p ∤ m`, if the
inertia group of every prime `Q` of `𝓞 K` over `p` has order dividing
`m`, then the ramification at `p` is tame with `e(Q∣p) ∣ m`, the
different exponent is at most `e − 1`
(`not_pow_ramificationIdx_dvd_differentIdeal`), and any weights `a, b`
with `a·(e−1) ≤ b·e` for all `e ∣ m` give `a·v_p(d_K) ≤ b·[K:ℚ]`
through the norm bookkeeping
`discr_factorization_le_of_forall_differentIdeal_pow_dvd`. The
inertia order is converted to `e(Q∣p)` by mathlib's inertia
dictionary (`Ideal.card_inertia_eq_ramificationIdxIn`) against the
`IsGaloisGroup` instance assembled as in
`differentIdeal_eq_top_of_forall_inertia_eq_bot`. -/
theorem discr_factorization_le_of_forall_inertia_card_dvd
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime) (m a b : ℕ) (hpm : ¬ p ∣ m)
    (hab : ∀ e : ℕ, e ∣ m → a * (e - 1) ≤ b * e)
    (hI : ∀ Q : Ideal (𝓞 K), Q.IsPrime → ((p : 𝓞 K) ∈ Q) →
      Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ m) :
    a * (NumberField.discr K).natAbs.factorization p ≤
      b * Module.finrank ℚ K := by
  classical
  refine discr_factorization_le_of_forall_differentIdeal_pow_dvd K p hp a b ?_
  intro Q hQprime hQmem d hd
  haveI := hQprime
  -- the instance pack of the inertia dictionary (as in `MazurTorsion`)
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := 𝓞 K) K
  have hqZ : Prime (((p : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hne : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hsp : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hqZ
  haveI hlies : Q.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQprime.ne_top hqZ).mpr (by exact_mod_cast hQmem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmaxZ : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurjZ : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ))
        ((Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxZ)
  haveI : Finite ((Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurjZ
  -- `Gal(K/ℚ)` is a Galois group of `𝓞 K` over `ℤ`
  haveI : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (𝓞 K) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    constructor
    intro x hx
    -- the underlying field element is Galois-fixed, hence rational
    have hfixL : ∀ g : K ≃ₐ[ℚ] K, g (x : K) = (x : K) := fun g =>
      congrArg (algebraMap (𝓞 K) K) (hx g)
    have hbot : (x : K) ∈ (⊥ : IntermediateField ℚ K) :=
      (IsGalois.mem_bot_iff_fixed _).mpr hfixL
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
    -- the rational number is integral over `ℤ`, hence an integer
    have hqint : IsIntegral ℤ q := by
      rw [← isIntegral_algebraMap_iff (B := K)
        (algebraMap ℚ K).injective, hq]
      exact x.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
    refine ⟨n, NumberField.RingOfIntegers.ext ?_⟩
    show algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) n) = (x : K)
    rw [← hq, ← hn, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K,
      ← IsScalarTower.algebraMap_apply ℤ ℚ K]
  -- `e(Q∣p) = |I(Q)|` divides `m`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (K ≃ₐ[ℚ] K)) (Ideal.span {((p : ℕ) : ℤ)}) Q
  have hem : Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q ∣ m := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
        (Ideal.span {((p : ℕ) : ℤ)}) Q hne,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx
        (Ideal.span {((p : ℕ) : ℤ)}) Q (K ≃ₐ[ℚ] K), ← hcard]
    exact hI Q hQprime hQmem
  -- the tame bound: `d < e`
  have htame : ¬ ((p : ℕ) ∣ Ideal.ramificationIdx'
      (Ideal.span {((p : ℕ) : ℤ)}) Q) := fun hpe => hpm (hpe.trans hem)
  have hnot := not_pow_ramificationIdx_dvd_differentIdeal K p hp
    Q hQprime hQmem htame
  have hdlt : d < Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q := by
    by_contra hge
    push Not at hge
    exact hnot ((pow_dvd_pow Q hge).trans hd)
  -- arithmetic: `a·d ≤ a·(e−1) ≤ b·e`
  calc a * d
      ≤ a * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q - 1) :=
        Nat.mul_le_mul_left a (by omega)
    _ ≤ b * Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q :=
        hab _ hem

/-- **The global Kummer core over `ℚ(ζ₃)`, subgroup form** (PROVEN;
label corrected 2026-07-25 — proven by the degree-`6` Minkowski
contradiction, commit `8fe04b3`
— Serre's unit computation, Duke 1987, §5.4, in its CFT-free
discriminant packaging): an open NORMAL subgroup `S ≤ Γ ℚ` contained
in the cyclotomic kernel `ker ω`, with `ker ω ⧸ S` of exponent `3`
(`hcube`) and order `≤ 3` (`hpair`: any two kernel elements are
dependent modulo `S`), containing the image of the local inertia at
every prime `p ∉ {2, 3}` (`hunrS`) and the kernel part of the local
inertia at `3` (`hthreeS`), contains the whole cyclotomic kernel. NO
condition at `2` is imposed, and none is needed.

Hypothesis necessity: `hcube` is ESSENTIAL, not bookkeeping — the
fixing subgroup of `ℚ(ζ₃, i)` satisfies every other hypothesis
(normal, open, inside `ker ω` with quotient `ℤ/2` — `hpair` holds for
any cyclic quotient — unramified outside `2`, and its inertia at `3`
meets the kernel trivially) yet does not contain `ker ω`; `|disc| =
144` at degree `4` clears the Minkowski bound. Exponent `3` pins the
quotient to `ℤ/3` and the degree to `6`, where Minkowski bites.

Recommended route (reuses the PROVEN Minkowski machinery below, see
`monoidHom_eq_one_of_forall_localInertia` and its strata): if some
kernel element avoids `S`, then `[ker ω : S] = 3` (`hpair` + `hcube`)
and `[Γ ℚ : S] = 6` (`exists_cyclotomicCharacterModL_three_ne_one`).
The fixed field `L` of `S` (`InfiniteGalois.fixingSubgroup_fixedField`,
`isOpen_iff_finite`, `normal_iff_isGalois`) is Galois of degree `6`
over `ℚ`, totally imaginary (it contains `ℚ(ζ₃)`, the fixed field of
`ker ω`), with `Gal(L/ℚ) ≅ Γ ℚ ⧸ S`. Inertia of `L/ℚ`: trivial at
`p ∉ {2, 3}` (`hunrS`, plus normality for the conjugates — mirror the
per-prime content of `inertia_eq_bot_of_forall_localInertia_restrictNormalHom`);
at `3` it meets `Gal(L/ℚ(ζ₃))` trivially (`hthreeS`), so it has order
`≤ 2` — tame at `3`, different exponent `≤ 1`, discriminant
contribution `≤ 3³`; at `2` it lies inside `Gal(L/ℚ(ζ₃))` of order
`3` (`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup` at
`p = 2`), so it is cyclic of order dividing `3` — tame at `2`,
different exponent `≤ 2`, discriminant contribution `≤ 2⁴`. The
order bounds at `2` and `3` transfer from the local groups to
`Ideal.inertia` at finite level through the surjectivity
`exists_mem_localInertiaGroup_restrictNormalHom_eq` of
`LocalInertiaFixedField` (with the embedded-prime plumbing of
`MazurTorsion`), and the different-ideal exponents through the tame
bound; `NumberField.absNorm_differentIdeal` then gives
`|disc L| ≤ 3³·2⁴ = 432`, contradicting the sharp Hermite–Minkowski
bound `√|d| ≥ (n^n/n!)·(π/4)^{r₂}`, i.e. `|d| ≥ 985` at `n = 6`,
`r₂ = 3`. (The pin's ready-made `NumberField.abs_discr_ge`, with
constant `(4/9)·(3π/4)^n ≈ 76` at `n = 6`, is NOT sufficient — derive
the `r₂`-sensitive bound from
`NumberField.exists_ne_zero_mem_ringOfIntegers_of_norm_le` exactly as
in that lemma's own proof.)

Classical alternative (Serre's original Kummer computation, for the
record, with the SIGN AUDIT of 2026-07-24 correcting the eigenspace
bookkeeping recorded on earlier versions of this node, which had the
two eigenspaces swapped): `S` cuts out an abelian exponent-`3`
extension `N/F`, `F = ℚ(ζ₃)`, unramified outside `{2, 3}` and with
trivial inertia at `λ = 1 - ζ₃`; Kummer theory over `F` (class number
`1`, units `±ζ₃^k`) puts its radical inside `⟨[ζ₃], [λ], [2]⟩ ≤
F^×/(F^×)³`; the Kummer pairing `ψ_a(g) = g(∛a)/∛a` satisfies
`χ_{τ(a)}(g) = -χ_a(τ⁻¹ g τ)` (the outer `τ` inverts `μ₃`), so an
`ω`-anti-equivariant character has `τ`-FIXED radical — check on
`Gal(ℚ(ζ₃, ∛2)/ℚ) ≅ S₃`, where transpositions invert the
`A₃`-characters and `[2]` is `τ`-fixed, and on `ℚ(ζ₉)`, whose
character is conjugation-INVARIANT with `τ[ζ₃] = -[ζ₃]`. The
`τ`-fixed subgroup of the radical group is `⟨[ζ₃·λ], [2]⟩`
(`τ[λ] = [λ] + 2[ζ₃]`, `τ[2] = [2]`), and the `λ`-inertia condition
kills both generators: `v_λ(ζ₃λ) = 1 ≢ 0 mod 3` forces ramification
at `λ`, and `F(∛2)/F` is wildly `λ`-ramified (`x³ - 2` is Eisenstein
at `3` after `x ↦ x - 1`). This route needs local Kummer/unit-filtration
theory absent from the pin; the discriminant route above is preferred. -/
theorem cyclotomicKernel_le_of_open_normal_of_local_conditions
    (S : Subgroup (Γ ℚ)) (hSopen : IsOpen (S : Set (Γ ℚ)))
    (hSnormal : S.Normal)
    (hSker : ∀ s ∈ S, cyclotomicCharacterModL 3 s = 1)
    (hcube : ∀ g : Γ ℚ, cyclotomicCharacterModL 3 g = 1 → g ^ 3 ∈ S)
    (hpair : ∀ g h : Γ ℚ, cyclotomicCharacterModL 3 g = 1 →
      cyclotomicCharacterModL 3 h = 1 →
      g ∈ S ∨ h ∈ S ∨ g⁻¹ * h ∈ S ∨ g * h ∈ S)
    (hunrS : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 →
      ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat),
        σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat →
        Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ ∈ S)
    (hthreeS : ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat),
      σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat →
      cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 →
      Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ ∈ S)
    (g : Γ ℚ) (hg : cyclotomicCharacterModL 3 g = 1) :
    g ∈ S := by
  classical
  by_contra hgS
  haveI := hSnormal
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  have hclosed : IsClosed (S : Set (Γ ℚ)) :=
    Subgroup.isClosed_of_isOpen _ hSopen
  -- the finite Galois subextension cut out by `S`
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField
      (S : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
  have hfix : L.fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨S, hclosed⟩
  haveI hfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hSopen)
  haveI hgal : IsGalois ℚ L :=
    (InfiniteGalois.normal_iff_isGalois L).mp (by rw [hfix]; exact hSnormal)
  haveI : Normal ℚ L := hgal.to_normal
  haveI : NumberField L := ⟨⟩
  -- the quotient map cutting out `L`
  set u : (Γ ℚ) →* (Γ ℚ) ⧸ S := QuotientGroup.mk' S
  have hfixu : L.fixingSubgroup = u.ker := by
    rw [hfix, QuotientGroup.ker_mk']
  -- `Gal(L/ℚ) ≅ Γ ℚ ⧸ S`
  have hkerL : (AlgEquiv.restrictNormalHom L :
      (Γ ℚ) →* (L ≃ₐ[ℚ] L)).ker = S := by
    rw [← hfix]
    exact IntermediateField.restrictNormalHom_ker L
  have hquot : ((Γ ℚ) ⧸ S) ≃* (L ≃ₐ[ℚ] L) :=
    (QuotientGroup.quotientMulEquivOfEq hkerL.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)))
  -- `ω` descends to the quotient
  set ω : ((Γ ℚ) ⧸ S) →* (ZMod 3)ˣ :=
    QuotientGroup.lift S (cyclotomicCharacterModL 3) hSker
  have hωu : ∀ x : Γ ℚ, ω (u x) = cyclotomicCharacterModL 3 x :=
    fun x => rfl
  -- the class of `g` has order `3` in the quotient
  set gb : (Γ ℚ) ⧸ S := u g with hgbdef
  have hgb1 : gb ≠ 1 := fun h => hgS ((QuotientGroup.eq_one_iff g).mp h)
  have hgb3 : gb ^ 3 = 1 := by
    rw [hgbdef, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hcube g hg)
  have hgb2 : gb ^ 2 ≠ 1 := by
    intro h2
    apply hgb1
    calc gb = (gb ^ 2)⁻¹ * gb ^ 3 := by group
      _ = 1 := by rw [h2, hgb3, inv_one, one_mul]
  -- the kernel of `ω` on the quotient is exactly `{1, gb, gb⁻¹}`
  have hkerset : (ω.ker : Set ((Γ ℚ) ⧸ S)) = {1, gb, gb⁻¹} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective S x
      have hy : cyclotomicCharacterModL 3 y = 1 := by
        rw [← hωu y]; exact hx
      rcases hpair g y hg hy with h | h | h | h
      · exact absurd h hgS
      · left; exact (QuotientGroup.eq_one_iff y).mpr h
      · right; left
        have h1 : u (g⁻¹ * y) = 1 := (QuotientGroup.eq_one_iff _).mpr h
        rw [map_mul, map_inv] at h1
        exact (inv_mul_eq_one.mp h1).symm
      · right; right
        have h1 : u (g * y) = 1 := (QuotientGroup.eq_one_iff _).mpr h
        rw [map_mul] at h1
        exact (mul_eq_one_iff_inv_eq.mp h1).symm
    · rintro (rfl | rfl | rfl)
      · exact map_one ω
      · rw [hgbdef, hωu]; exact hg
      · rw [map_inv, hgbdef, hωu, hg, inv_one]
  have hkercard : Nat.card ω.ker = 3 := by
    have h1 : Nat.card ω.ker = (ω.ker : Set ((Γ ℚ) ⧸ S)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1, hkerset]
    refine Set.ncard_eq_three.mpr ⟨1, gb, gb⁻¹, fun h => hgb1 h.symm,
      fun h => hgb1 (by rw [← inv_inv gb, ← h, inv_one]), ?_, rfl⟩
    intro h
    apply hgb2
    rw [sq]
    nth_rewrite 2 [h]
    rw [mul_inv_cancel]
  -- the range of `ω` on the quotient is all of `(ZMod 3)ˣ`, of order `2`
  have hcard_units : Nat.card ((ZMod 3)ˣ) = 2 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hrange2 : Nat.card ω.range = 2 := by
    have hdvd : Nat.card ω.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card ω.range
      rwa [hcard_units] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      obtain ⟨σ, hσ⟩ := exists_cyclotomicCharacterModL_three_ne_one
      have hbot : ω.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem : ω (u σ) ∈ ω.range := ⟨u σ, rfl⟩
      rw [hbot, Subgroup.mem_bot, hωu] at hmem
      exact hσ hmem
    · exact h1
  -- so the quotient has order `6` and `[L : ℚ] = 6`
  have hcard6 : Nat.card ((Γ ℚ) ⧸ S) = 6 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ω.ker
    have h2 : Nat.card ((((Γ ℚ) ⧸ S)) ⧸ ω.ker) = Nat.card ω.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ω).toEquiv
    rw [h2, hrange2, hkercard] at h1
    omega
  have hdeg : Module.finrank ℚ L = 6 := by
    rw [← IsGalois.card_aut_eq_finrank ℚ L, ← Nat.card_congr hquot.toEquiv]
    exact hcard6
  -- `L` is totally complex: a real place would give a complex
  -- conjugation in `S`, whose 3-adic cyclotomic character is `−1`,
  -- contradicting `ω = 1` on `S` through the mod-3 reduction
  haveI htc : NumberField.IsTotallyComplex L := by
    by_contra hK
    obtain ⟨c, hcfix, hcχ⟩ :=
      exists_conj_fixingSubgroup_of_not_isTotallyComplex L hK
    have hcS : c ∈ S := by rw [← hfix]; exact hcfix
    have hmem := cyclotomicCharacter_sub_one_mem_span_three c (hSker c hcS)
    rw [hcχ] at hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    have happ := congrArg (PadicInt.toZMod (p := 3)) he
    rw [map_mul, map_sub, map_neg, map_one] at happ
    have h3 : (PadicInt.toZMod (p := 3)) 3 = 0 := by
      rw [show ((3 : ℤ_[3])) = (((3 : ℕ) : ℤ_[3])) by norm_num, map_natCast]
      decide
    rw [h3, mul_zero] at happ
    exact absurd happ (by decide)
  -- inertia orders of `Gal(L/ℚ)`: trivial away from `2, 3`
  have hIq : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
      (((q : ℕ) : NumberField.RingOfIntegers L) ∈ Q) →
      Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) ∣ 1 := by
    intro q hq hq2 hq3 Q hQ hQmem
    refine inertia_card_dvd_of_card_map_localInertiaGroup_dvd L u hfixu hq
      Q hQ hQmem 1 ?_
    rw [Nat.dvd_one, Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hy
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    -- bridge the divergent `Algebra ℚ ℚᵥ` spellings (the transport's
    -- statement was elaborated with `DivisionRing.toRatAlgebra`)
    have halg : (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) =
        (DivisionRing.toRatAlgebra) := Subsingleton.elim _ _
    exact halg ▸ hunrS q hq hq2 hq3 σ hσ
  -- inertia order divides `2` at `3` (`hthreeS`: the kernel part of the
  -- local inertia at `3` dies in the quotient, so `ω` is injective there)
  have hI3 : ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
      (((3 : ℕ) : NumberField.RingOfIntegers L) ∈ Q) →
      Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) ∣ 2 := by
    intro Q hQ hQmem
    refine inertia_card_dvd_of_card_map_localInertiaGroup_dvd L u hfixu
      Nat.prime_three Q hQ hQmem 2 ?_
    have hkey : ∀ x : (Γ ℚ) ⧸ S,
        x ∈ Subgroup.map u (Subgroup.map (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
          (localInertiaGroup
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →
        ω x = 1 → x = 1 := by
      intro x hx hωx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hy
      rw [hωu] at hωx
      exact (QuotientGroup.eq_one_iff _).mpr (hthreeS σ hσ hωx)
    rw [← hcard_units]
    refine Subgroup.card_dvd_of_injective (ω.comp (Subgroup.subtype _)) ?_
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hx2 : (x : (Γ ℚ) ⧸ S) ∈ Subgroup.map u (Subgroup.map
        (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) := by
      -- bridge the divergent `Algebra ℚ ℚᵥ` spellings
      have halg : (DivisionRing.toRatAlgebra : Algebra ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) =
          IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
            (NumberField.RingOfIntegers ℚ) ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
        Subsingleton.elim _ _
      exact halg ▸ x.2
    exact Subtype.ext (hkey _ hx2 hx)
  -- inertia order divides `3` at `2` (`ω` kills the local inertia at `2`)
  have hI2 : ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
      (((2 : ℕ) : NumberField.RingOfIntegers L) ∈ Q) →
      Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) ∣ 3 := by
    intro Q hQ hQmem
    refine inertia_card_dvd_of_card_map_localInertiaGroup_dvd L u hfixu
      Nat.prime_two Q hQ hQmem 3 ?_
    rw [← hkercard]
    refine Subgroup.card_dvd_of_le ?_
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MonoidHom.mem_ker, hωu]
    -- bridge the divergent `Algebra ℚ ℚᵥ` spellings
    have halg : (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) =
        (DivisionRing.toRatAlgebra) := Subsingleton.elim _ _
    exact halg ▸ cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup
      Nat.prime_two (by norm_num) σ hσ
  -- the discriminant bounds: `v₂ ≤ 4`, `v₃ ≤ 3`, nothing else
  have hd2 : 3 * (NumberField.discr L).natAbs.factorization 2 ≤
      2 * Module.finrank ℚ L :=
    discr_factorization_le_of_forall_inertia_card_dvd L 2 Nat.prime_two 3 3 2
      (by norm_num)
      (fun e he => by
        have h1 : e ≤ 3 := Nat.le_of_dvd (by norm_num) he
        omega)
      hI2
  have hd3 : 2 * (NumberField.discr L).natAbs.factorization 3 ≤
      1 * Module.finrank ℚ L :=
    discr_factorization_le_of_forall_inertia_card_dvd L 3 Nat.prime_three 2 2 1
      (by norm_num)
      (fun e he => by
        have h1 : e ≤ 2 := Nat.le_of_dvd (by norm_num) he
        omega)
      hI3
  have hfac0 : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 →
      (NumberField.discr L).natAbs.factorization q = 0 := by
    intro q hq hq2 hq3
    have h := discr_factorization_le_of_forall_inertia_card_dvd L q hq 1 1 0
      (fun hdv => hq.ne_one (Nat.dvd_one.mp hdv))
      (fun e he => by
        have h1 : e = 1 := Nat.dvd_one.mp he
        omega)
      (hIq q hq hq2 hq3)
    omega
  -- `|d_L| = 2^{v₂}·3^{v₃} ≤ 2⁴·3³ = 432`
  have hD0 : NumberField.discr L ≠ 0 := NumberField.discr_ne_zero L
  have hN0 : (NumberField.discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  have hsupp : (NumberField.discr L).natAbs.factorization.support ⊆
      ({2, 3} : Finset ℕ) := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization _ ▸ hq)
    by_contra hq23
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq23
    push Not at hq23
    exact (Finsupp.mem_support_iff.mp hq) (hfac0 q hqp hq23.1 hq23.2)
  have hNeq : (NumberField.discr L).natAbs =
      2 ^ (NumberField.discr L).natAbs.factorization 2 *
        3 ^ (NumberField.discr L).natAbs.factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod_of_support_subset _ hsupp (· ^ ·)
      (fun i _ => pow_zero i), Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
  have hle432 : (NumberField.discr L).natAbs ≤ 432 := by
    rw [hdeg] at hd2 hd3
    calc (NumberField.discr L).natAbs
        = 2 ^ (NumberField.discr L).natAbs.factorization 2 *
          3 ^ (NumberField.discr L).natAbs.factorization 3 := hNeq
      _ ≤ 2 ^ 4 * 3 ^ 3 :=
          Nat.mul_le_mul
            (Nat.pow_le_pow_right (by norm_num) (by omega))
            (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 432 := by norm_num
  -- Minkowski at degree `6`, totally complex: `|d_L| ≥ 6¹²/((4/π)⁶·(6!)²)`,
  -- which exceeds `432` since `π > 3`
  have hmink := NumberField.abs_discr_ge_of_isTotallyComplex (K := L)
  rw [hdeg] at hmink
  have hub : ((|NumberField.discr L| : ℤ) : ℝ) ≤ 432 := by
    have h1 : |NumberField.discr L| ≤ (432 : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle432
    exact_mod_cast h1
  have hC : ((4 : ℝ) / Real.pi) ^ 6 * (Nat.factorial 6 : ℝ) ^ 2 ≤
      4096 / 729 * 518400 := by
    have h1 : ((4 : ℝ) / Real.pi) ^ 6 ≤ 4096 / 729 := by
      calc ((4 : ℝ) / Real.pi) ^ 6 ≤ (4 / 3) ^ 6 := by
            gcongr
            exact Real.pi_gt_three.le
        _ = 4096 / 729 := by norm_num
    calc ((4 : ℝ) / Real.pi) ^ 6 * (Nat.factorial 6 : ℝ) ^ 2
        = ((4 : ℝ) / Real.pi) ^ 6 * 518400 := by
          norm_num [Nat.factorial]
      _ ≤ 4096 / 729 * 518400 := by
          have h2 : (0 : ℝ) ≤ 518400 := by norm_num
          exact mul_le_mul_of_nonneg_right h1 h2
  have hCpos : (0 : ℝ) < ((4 : ℝ) / Real.pi) ^ 6 *
      (Nat.factorial 6 : ℝ) ^ 2 := by
    positivity
  rw [div_le_iff₀ hCpos] at hmink
  -- `6¹² ≤ |d_L|·C ≤ 432·(4096/729·518400) = 1258291200 < 6¹² = 2176782336`
  have hprod : ((|NumberField.discr L| : ℤ) : ℝ) *
      (((4 : ℝ) / Real.pi) ^ 6 * (Nat.factorial 6 : ℝ) ^ 2) ≤
      432 * (4096 / 729 * 518400) :=
    mul_le_mul hub hC hCpos.le (by norm_num)
  have h612 : ((6 : ℕ) : ℝ) ^ (2 * 6) = 2176782336 := by norm_num
  rw [h612] at hmink
  linarith [hmink, hprod]

/-- **The global Kummer core over `ℚ(ζ₃)`, character form** (DERIVED
2026-07-24 from the subgroup form
`cyclotomicKernel_le_of_open_normal_of_local_conditions`): a
`ZMod 3`-valued character of the cyclotomic kernel `ker ω ≤ Γ ℚ` — an
honest homomorphism on the kernel, `ω`-ANTI-equivariant under
conjugation from outside the kernel, killed by an open normal subgroup
`U` of `Γ ℚ`, killed by the local inertia at every prime `p ∉ {2, 3}`,
and killed by the kernel part of the local inertia at `3` — vanishes
on the whole kernel. Reduction: `S := {x | ω x = 1 ∧ χ x = 0}` is a
subgroup (the homomorphism property), normal in `Γ ℚ` (conjugation
inside the kernel by the homomorphism property, outside by the
anti-equivariance), and open (it contains `U ⊓ ker ω`, and `ker ω` is
open by `continuous_cyclotomicCharacterModL`); the kernel quotient has
exponent `3` (`3 • a = 0` in `ZMod 3`) and any two kernel elements are
dependent modulo `S` (any two elements of `ZMod 3` are dependent); the
inertia conditions land in `S` using
`cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup` for the
`ω`-part outside `{3}`. The arithmetic content and its route live on
the subgroup form. -/
theorem cyclotomicKernel_threeTorsion_character_vanishes
    (χ : Γ ℚ → ZMod 3)
    (hhom : ∀ g h : Γ ℚ, cyclotomicCharacterModL 3 g = 1 →
      cyclotomicCharacterModL 3 h = 1 → χ (g * h) = χ g + χ h)
    (hconj : ∀ τ g : Γ ℚ, cyclotomicCharacterModL 3 τ ≠ 1 →
      cyclotomicCharacterModL 3 g = 1 → χ (τ * g * τ⁻¹) = -χ g)
    (U : Subgroup (Γ ℚ)) (hUopen : IsOpen (U : Set (Γ ℚ)))
    (_hUnormal : U.Normal)
    (hUχ : ∀ u ∈ U, χ u = 0)
    (hunr : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 →
      ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat),
        σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat →
        χ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (hthree : ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat),
      σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat →
      cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 →
      χ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (g : Γ ℚ) (hg : cyclotomicCharacterModL 3 g = 1) :
    χ g = 0 := by
  classical
  -- elementary consequences of the homomorphism property
  have hχone : χ 1 = 0 := by
    have h := hhom 1 1 (map_one _) (map_one _)
    rw [one_mul] at h
    exact left_eq_add.mp h
  have hχinv : ∀ x : Γ ℚ, cyclotomicCharacterModL 3 x = 1 →
      χ x⁻¹ = -χ x := by
    intro x hx
    have hxinv : cyclotomicCharacterModL 3 x⁻¹ = 1 := by
      rw [map_inv, hx, inv_one]
    have h := hhom x x⁻¹ hx hxinv
    rw [mul_inv_cancel, hχone] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  -- the kernel-and-kernel subgroup
  set S : Subgroup (Γ ℚ) :=
    { carrier := {x : Γ ℚ | cyclotomicCharacterModL 3 x = 1 ∧ χ x = 0}
      one_mem' := ⟨map_one _, hχone⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨by rw [map_mul, ha.1, hb.1, one_mul],
          by rw [hhom a b ha.1 hb.1, ha.2, hb.2, add_zero]⟩
      inv_mem' := fun {a} ha =>
        ⟨by rw [map_inv, ha.1, inv_one],
          by rw [hχinv a ha.1, ha.2, neg_zero]⟩ }
  have hmemS : ∀ x : Γ ℚ,
      x ∈ S ↔ cyclotomicCharacterModL 3 x = 1 ∧ χ x = 0 :=
    fun _ => Iff.rfl
  -- `S` is normal: inside the kernel by the homomorphism property,
  -- outside by the anti-equivariance
  have hSnormal : S.Normal := by
    constructor
    intro x hx τ
    rw [hmemS] at hx ⊢
    by_cases hτ : cyclotomicCharacterModL 3 τ = 1
    · have hτinv : cyclotomicCharacterModL 3 τ⁻¹ = 1 := by
        rw [map_inv, hτ, inv_one]
      have hτx : cyclotomicCharacterModL 3 (τ * x) = 1 := by
        rw [map_mul, hτ, hx.1, one_mul]
      refine ⟨by rw [map_mul, hτx, hτinv, one_mul], ?_⟩
      have h2 := hhom (τ * x) τ⁻¹ hτx hτinv
      have h1 := hhom τ x hτ hx.1
      calc χ (τ * x * τ⁻¹) = χ τ + χ x + χ τ⁻¹ := by rw [h2, h1]
        _ = χ τ + χ τ⁻¹ := by rw [hx.2, add_zero]
        _ = χ τ + -χ τ := by rw [hχinv τ hτ]
        _ = 0 := add_neg_cancel _
    · refine ⟨?_, by rw [hconj τ x hτ hx.1, hx.2, neg_zero]⟩
      rw [map_mul, map_mul, map_inv, hx.1, mul_one, mul_inv_cancel]
  -- `S` is open: it contains `U ⊓ ker ω`, and `ker ω` is open
  have hSopen : IsOpen (S : Set (Γ ℚ)) := by
    refine Subgroup.isOpen_mono
      (H₁ := U ⊓ (cyclotomicCharacterModL 3).ker) ?_ ?_
    · rintro x ⟨hxU, hxK⟩
      exact (hmemS x).mpr ⟨MonoidHom.mem_ker.mp hxK, hUχ x hxU⟩
    · rw [Subgroup.coe_inf]
      refine hUopen.inter ?_
      have h1 : (((cyclotomicCharacterModL 3).ker : Subgroup (Γ ℚ)) :
            Set (Γ ℚ))
          = (fun x : Γ ℚ =>
              ((cyclotomicCharacterModL 3 x : (ZMod 3)ˣ) : ZMod 3)) ⁻¹'
            {(1 : ZMod 3)} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
          Set.mem_singleton_iff]
        constructor
        · intro h
          rw [h]
          rfl
        · intro h
          exact Units.ext h
      rw [h1]
      exact (continuous_cyclotomicCharacterModL 3).isOpen_preimage _
        (isOpen_discrete _)
  -- the kernel quotient has exponent `3` and any two kernel elements
  -- are dependent modulo `S`
  have hcube : ∀ x : Γ ℚ, cyclotomicCharacterModL 3 x = 1 → x ^ 3 ∈ S := by
    intro x hx
    have hxx : cyclotomicCharacterModL 3 (x * x) = 1 := by
      rw [map_mul, hx, one_mul]
    refine (hmemS _).mpr ⟨by rw [map_pow, hx, one_pow], ?_⟩
    have hpow : x ^ 3 = x * x * x := by rw [pow_succ, pow_two]
    have hall : ∀ a : ZMod 3, a + a + a = 0 := by decide
    rw [hpow, hhom (x * x) x hxx hx, hhom x x hx hx]
    exact hall (χ x)
  have hpair : ∀ x y : Γ ℚ, cyclotomicCharacterModL 3 x = 1 →
      cyclotomicCharacterModL 3 y = 1 →
      x ∈ S ∨ y ∈ S ∨ x⁻¹ * y ∈ S ∨ x * y ∈ S := by
    intro x y hx hy
    have hxinv : cyclotomicCharacterModL 3 x⁻¹ = 1 := by
      rw [map_inv, hx, inv_one]
    have hdec : ∀ a b : ZMod 3, a = 0 ∨ b = 0 ∨ b = a ∨ a + b = 0 := by
      decide
    rcases hdec (χ x) (χ y) with h | h | h | h
    · exact Or.inl ((hmemS x).mpr ⟨hx, h⟩)
    · exact Or.inr (Or.inl ((hmemS y).mpr ⟨hy, h⟩))
    · refine Or.inr (Or.inr (Or.inl ((hmemS _).mpr
        ⟨by rw [map_mul, hxinv, hy, one_mul], ?_⟩)))
      rw [hhom x⁻¹ y hxinv hy, hχinv x hx, h]
      exact neg_add_cancel _
    · refine Or.inr (Or.inr (Or.inr ((hmemS _).mpr
        ⟨by rw [map_mul, hx, hy, one_mul], ?_⟩)))
      rw [hhom x y hx hy]
      exact h
  -- apply the subgroup form
  exact ((hmemS g).mp
    (cyclotomicKernel_le_of_open_normal_of_local_conditions S hSopen
      hSnormal (fun s hs => ((hmemS s).mp hs).1) hcube hpair
      (fun p hp hp2 hp3 σ hσ => (hmemS _).mpr
        ⟨cyclotomicCharacterModL_eq_one_of_mem_localInertiaGroup hp hp3 σ hσ,
          hunr p hp hp2 hp3 σ hσ⟩)
      (fun σ hσ hσω => (hmemS _).mpr ⟨hσω, hthree σ hσ hσω⟩)
      g hg)).2

/-- **The global Kummer core over `ℚ(ζ₃)`** (DERIVED 2026-07-24 from
the character form `cyclotomicKernel_threeTorsion_character_vanishes`):
an approximate homomorphism `d` on the cyclotomic kernel `ker ω ≤ Γ ℚ`
valued in `𝔪ⁿ⁺¹` — a homomorphism modulo `𝔪ⁿ⁺²` on the kernel,
`ω`-ANTI-equivariant under conjugation from outside the kernel
(`hdconj`: conjugating by `τ` with `ω τ = -1` negates `d` mod `𝔪ⁿ⁺²`),
killed by an open normal subgroup, killed by the local inertia at every
prime `p ∉ {2, 3}`, and killed by the cyclotomic-kernel part of the
local inertia at `3` — vanishes modulo `𝔪ⁿ⁺²` on the whole kernel. NO
local condition at `2` is required. Reduction: the graded piece
`𝔪ⁿ⁺¹ ⧸ 𝔪ⁿ⁺²` is a `ZMod 3`-vector space (`3 ∈ 𝔪`,
`three_mem_maximalIdeal`); for every `ZMod 3`-functional `φ` on it the
composite `g ↦ φ [d g]` satisfies the hypotheses of the character form
verbatim, hence vanishes on the kernel; functionals separate points
(`Module.forall_dual_apply_eq_zero_iff`), so `[d g] = 0`, i.e.
`d g ∈ 𝔪ⁿ⁺²`. The arithmetic content — Serre's unit computation, with
the corrected (2026-07-24) eigenspace bookkeeping — is recorded on the
character form. -/
theorem cyclotomicKernel_defect_vanishes_of_local_conditions
    {R : Type u} [CommRing R]
    [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (n : ℕ) (d : Γ ℚ → R)
    (hd1 : ∀ g : Γ ℚ, d g ∈ IsLocalRing.maximalIdeal R ^ (n + 1))
    (hdhom : ∀ g h : Γ ℚ, cyclotomicCharacterModL 3 g = 1 →
      cyclotomicCharacterModL 3 h = 1 →
      d (g * h) - (d g + d h) ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (hdconj : ∀ τ g : Γ ℚ, cyclotomicCharacterModL 3 τ ≠ 1 →
      cyclotomicCharacterModL 3 g = 1 →
      d (τ * g * τ⁻¹) + d g ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (U : Subgroup (Γ ℚ)) (hUopen : IsOpen (U : Set (Γ ℚ)))
    (hUnormal : U.Normal)
    (hUd : ∀ u ∈ U, d u ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (hunr : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 →
      ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat),
        σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat →
        d (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
          IsLocalRing.maximalIdeal R ^ (n + 2))
    (hthree : ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat),
      σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat →
      cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 →
      d (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
        IsLocalRing.maximalIdeal R ^ (n + 2))
    (g : Γ ℚ) (hg : cyclotomicCharacterModL 3 g = 1) :
    d g ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- the graded piece `𝔪ⁿ⁺¹ ⧸ 𝔪ⁿ⁺²`
  set M : Submodule R R := (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)
  set N : Submodule R ↥M := Submodule.comap M.subtype
    (IsLocalRing.maximalIdeal R ^ (n + 2) : Ideal R)
  have hmemN : ∀ x : ↥M, x ∈ N ↔
      (x : R) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := fun _ => Iff.rfl
  -- `3` kills the quotient (`3 ∈ 𝔪`), making it a `ZMod 3`-vector space
  have htor : ∀ x : ↥M ⧸ N, (3 : ℕ) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have hmem : y + y + y ∈ N := by
      rw [hmemN]
      have h1 : ((y + y + y : ↥M) : R) = (3 : R) * (y : R) := by
        push_cast
        ring
      rw [h1]
      have hy : (y : R) ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := y.2
      have h2 := Ideal.mul_mem_mul three_mem_maximalIdeal hy
      rw [← pow_succ'] at h2
      exact h2
    have h3 : (3 : ℕ) • (Submodule.Quotient.mk y : ↥M ⧸ N)
        = Submodule.Quotient.mk (y + y + y) := by
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add]
      abel
    rw [h3, Submodule.Quotient.mk_eq_zero]
    exact hmem
  letI : Module (ZMod 3) (↥M ⧸ N) := AddCommGroup.zmodModule htor
  -- vanishing of the class in `N` from `𝔪ⁿ⁺²`-membership
  have hmk0 : ∀ g' : Γ ℚ, d g' ∈ IsLocalRing.maximalIdeal R ^ (n + 2) →
      (Submodule.Quotient.mk ⟨d g', hd1 g'⟩ : ↥M ⧸ N) = 0 := by
    intro g' hgm
    rw [Submodule.Quotient.mk_eq_zero, hmemN]
    exact hgm
  -- every `ZMod 3`-functional kills the class of `d g` …
  have hdual : ∀ φ : Module.Dual (ZMod 3) (↥M ⧸ N),
      φ (Submodule.Quotient.mk ⟨d g, hd1 g⟩) = 0 := by
    intro φ
    refine cyclotomicKernel_threeTorsion_character_vanishes
      (fun g' => φ (Submodule.Quotient.mk ⟨d g', hd1 g'⟩)) ?_ ?_ U hUopen
      hUnormal ?_ ?_ ?_ g hg
    · -- homomorphism on the kernel
      intro g' h hg' hh
      have h1 : (Submodule.Quotient.mk ⟨d (g' * h), hd1 (g' * h)⟩ : ↥M ⧸ N)
          = Submodule.Quotient.mk ⟨d g', hd1 g'⟩
            + Submodule.Quotient.mk ⟨d h, hd1 h⟩ := by
        rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hmemN]
        exact hdhom g' h hg' hh
      simp only [h1, map_add]
    · -- anti-equivariance under outside conjugation
      intro τ g' hτ hg'
      have h1 : (Submodule.Quotient.mk
            ⟨d (τ * g' * τ⁻¹), hd1 (τ * g' * τ⁻¹)⟩ : ↥M ⧸ N)
          = -Submodule.Quotient.mk ⟨d g', hd1 g'⟩ := by
        rw [← Submodule.Quotient.mk_neg, Submodule.Quotient.eq,
          sub_neg_eq_add, hmemN]
        exact hdconj τ g' hτ hg'
      simp only [h1, map_neg]
    · -- killed by the open normal subgroup
      intro u hu
      rw [hmk0 u (hUd u hu), map_zero]
    · -- killed by inertia outside `{2, 3}`
      intro p hp hp2 hp3 σ hσ
      rw [hmk0 _ (hunr p hp hp2 hp3 σ hσ), map_zero]
    · -- killed by the kernel part of inertia at `3`
      intro σ hσ hσω
      rw [hmk0 _ (hthree σ hσ hσω), map_zero]
  -- … and functionals separate points
  have hzero := (Module.forall_dual_apply_eq_zero_iff (ZMod 3)
    (Submodule.Quotient.mk (p := N) ⟨d g, hd1 g⟩)).mp hdual
  rw [Submodule.Quotient.mk_eq_zero, hmemN] at hzero
  exact hzero

set_option backward.isDefEq.respectTransparency false in
/-- **The ω-defect dies on the cyclotomic kernel** (DERIVED 2026-07-23
from the Fontaine stratum at `3` and the global Kummer core — the
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
    (_hamul : ∀ g h : Γ ℚ,
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
  classical
  -- the residual identification of the twist with `ω`
  have hid := fun g' => residual_twist_eq_cyclotomicCharacterModL V hV hρ kk
    hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha g'
  -- the defect
  set d : Γ ℚ → R := fun g' => f (ρ g' w₀) - f w₀ with hddef
  -- (i) values in `𝔪ⁿ⁺¹`
  have hd1 : ∀ g' : Γ ℚ, d g' ∈ IsLocalRing.maximalIdeal R ^ (n + 1) :=
    fun g' => hf g' w₀
  -- (ii) homomorphism modulo `𝔪ⁿ⁺²` on the cyclotomic kernel
  have hdhom : ∀ g' h : Γ ℚ, cyclotomicCharacterModL 3 g' = 1 →
      cyclotomicCharacterModL 3 h = 1 →
      d (g' * h) - (d g' + d h) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g' h _ hh
    have h1 := hcoc g' h
    have h2 : (a h - 1) * d g' ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h3 := Ideal.mul_mem_mul ((hid h).1 hh) (hd1 g')
      rwa [← pow_succ'] at h3
    have heq : d (g' * h) - (d g' + d h)
        = (d (g' * h) - (a h * d g' + d h)) + (a h - 1) * d g' := by
      rw [hddef]; ring
    rw [heq]
    exact Submodule.add_mem _ h1 h2
  -- (iii) `ω`-anti-equivariance under outside conjugation
  have hdconj : ∀ τ g' : Γ ℚ, cyclotomicCharacterModL 3 τ ≠ 1 →
      cyclotomicCharacterModL 3 g' = 1 →
      d (τ * g' * τ⁻¹) + d g' ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro τ g' hτ hg'
    -- the two cocycle identities
    have hA := hcoc τ g'
    have hB := hcoc (τ * g' * τ⁻¹) τ
    rw [inv_mul_cancel_right] at hB
    -- the small products
    have hC : (a g' - 1) * d τ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h3 := Ideal.mul_mem_mul ((hid g').1 hg') (hd1 τ)
      rwa [← pow_succ'] at h3
    have hE : (a τ + 1) * d (τ * g' * τ⁻¹) ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h3 := Ideal.mul_mem_mul ((hid τ).2 hτ) (hd1 (τ * g' * τ⁻¹))
      rwa [← pow_succ'] at h3
    -- assemble
    have heq : d (τ * g' * τ⁻¹) + d g'
        = (a τ + 1) * d (τ * g' * τ⁻¹)
          - (d (τ * g') - (a g' * d τ + d g'))
          + (d (τ * g') - (a τ * d (τ * g' * τ⁻¹) + d τ))
          - (a g' - 1) * d τ := by
      rw [hddef]; ring
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.add_mem _
      (Submodule.sub_mem _ hE hA) hB) hC
  -- (iv) the open normal congruence subgroup at level `n + 2`
  set U : Subgroup (Γ ℚ) :=
    { carrier := {g' : Γ ℚ | ∀ x : V, ρ g' x - x ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V)}
      one_mem' := fun x => by
        rw [map_one, Module.End.one_apply, sub_self]
        exact Submodule.zero_mem _
      mul_mem' := fun {g'} {h} hg' hh x => by
        have hsplit : ρ (g' * h) x - x
            = (ρ g') ((ρ h) x - x) + ((ρ g') x - x) := by
          rw [show ρ (g' * h) x = ρ g' (ρ h x) from by rw [map_mul]; rfl,
            map_sub]
          abel
        rw [hsplit]
        exact Submodule.add_mem _
          (apply_mem_smul_top (ρ g' : V →ₗ[R] V) (hh x)) (hg' x)
      inv_mem' := fun {g'} hg' x => by
        have hfixx : (ρ g'⁻¹) ((ρ g') x) = x := by
          rw [show (ρ g'⁻¹) ((ρ g') x) = ((ρ g'⁻¹) * (ρ g')) x from rfl,
            ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        have hsplit : ρ g'⁻¹ x - x = -((ρ g'⁻¹) ((ρ g') x - x)) := by
          rw [map_sub, hfixx]
          abel
        rw [hsplit]
        exact Submodule.neg_mem _
          (apply_mem_smul_top (ρ g'⁻¹ : V →ₗ[R] V) (hg' x)) }
  have hUopen : IsOpen (U : Set (Γ ℚ)) :=
    isOpen_setOf_forall_sub_mem_pow_smul V ρ (n + 2)
  have hUnormal : U.Normal := by
    constructor
    intro u hu τ x
    have hconj : ρ (τ * u * τ⁻¹) x - x
        = (ρ τ) ((ρ u) ((ρ τ⁻¹) x) - (ρ τ⁻¹) x) := by
      have h1 : ρ (τ * u * τ⁻¹) x = ρ τ (ρ u (ρ τ⁻¹ x)) := by
        rw [show (τ * u * τ⁻¹ : Γ ℚ) = τ * (u * τ⁻¹) from by group,
          map_mul, map_mul]
        rfl
      have h2 : (ρ τ) ((ρ τ⁻¹) x) = x := by
        rw [show (ρ τ) ((ρ τ⁻¹) x) = ((ρ τ) * (ρ τ⁻¹)) x from rfl,
          ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [h1, map_sub, h2]
    rw [hconj]
    exact apply_mem_smul_top (ρ τ : V →ₗ[R] V) (hu ((ρ τ⁻¹) x))
  have hUd : ∀ u ∈ U, d u ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro u hu
    replace hu : ∀ x : V, ρ u x - x ∈
        (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := hu
    show f (ρ u w₀) - f w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2)
    rw [← map_sub]
    exact linearMap_apply_mem_of_mem_smul_top f (hu w₀)
  -- (v) vanishing on inertia outside `{2, 3}`
  have hunr : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 →
      ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat),
        σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat →
        d (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
          IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro p hp hp2 hp3 σ hσ
    haveI hunramified : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      hρ.isUnramified p hp ⟨hp2, hp3⟩
    have hone : (ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat) σ = 1 := by
      have hker := GaloisRep.IsUnramifiedAt.localInertiaGroup_le
        (ρ := ρ) (v := hp.toHeightOneSpectrumRingOfIntegersRat) hσ
      simpa [GaloisRep.ker, MonoidHom.mem_ker] using hker
    have hone' : ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
      rw [GaloisRep.toLocal_apply] at hone
      exact hone
    show f (ρ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat)) σ) w₀) - f w₀ ∈
      IsLocalRing.maximalIdeal R ^ (n + 2)
    rw [hone', Module.End.one_apply, sub_self]
    exact Submodule.zero_mem _
  -- (vi) the Fontaine stratum at `3`
  have hthree : ∀ σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat),
      σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat →
      cyclotomicCharacterModL 3 (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 →
      d (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro σ hσ hσω
    exact omega_defect_vanishes_on_localInertia_at_three V hV hρ kk hsurj
      π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha n f hf hfv₀ σ hσ hσω
  -- the global Kummer core closes the node
  exact cyclotomicKernel_defect_vanishes_of_local_conditions n d hd1 hdhom
    hdconj U hUopen hUnormal hUd hunr hthree g hg

/-- **The ω-twisted cocycle vanishing** (PROVEN; label corrected
2026-07-25 — the arithmetic core
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
    (Rat.ringOfIntegersEquiv.symm.heightOneSpectrum).symm v
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

set_option backward.isDefEq.respectTransparency false in
open NumberField in
/-- **Local inertia covers finite-level inertia** (PROVEN 2026-07-23 —
the decomposition stratum, derived from MazurTorsion's
`inertia_eq_bot_of_le_fixingSubgroup` with `τ = 1`): for a finite Galois subextension `L/ℚ` of `ℚ̄`
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
  classical
  haveI := hQp
  haveI : NumberField L := ⟨⟩
  haveI : IsGalois ℚ L := ⟨⟩
  -- the rational prime under `Q`
  have hp0 : Q.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ
  haveI : (Q.under ℤ).IsPrime := Ideal.IsPrime.under ℤ Q
  obtain ⟨z, hz⟩ := (IsPrincipalIdealRing.principal (Q.under ℤ)).principal
  have hzne : z ≠ 0 := by
    rintro rfl
    apply hp0
    rw [hz]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hzprime : Prime z := by
    have hp := ‹(Q.under ℤ).IsPrime›
    rw [hz] at hp
    exact (Ideal.span_singleton_prime hzne).mp hp
  have hq : z.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hzprime
  -- `q ∈ Q` for the positive generator `q = z.natAbs`
  have hzmem : z ∈ Q.under ℤ := hz ▸ Ideal.mem_span_singleton_self z
  have hnatmem : ((z.natAbs : ℤ)) ∈ Q.under ℤ := by
    have habs : ((z.natAbs : ℤ)) = z ∨ ((z.natAbs : ℤ)) = -z := by omega
    rcases habs with h | h
    · rwa [h]
    · rw [h]
      exact (Ideal.under ℤ Q).neg_mem hzmem
  have hQmem : ((z.natAbs : ℕ) : 𝓞 L) ∈ Q := by
    rw [← map_natCast (algebraMap ℤ (𝓞 L)) z.natAbs]
    exact Ideal.mem_comap.mp hnatmem
  -- reduce to the MazurTorsion transport node: the image of the local
  -- inertia at `q` fixes `L` pointwise (the `τ = 1` case of `hloc`)
  refine inertia_eq_bot_of_le_fixingSubgroup L hq ?_ Q hQmem
  have hle' : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup := by
    rintro g ⟨σ, hσ, rfl⟩
    have h1 := hloc hq.toHeightOneSpectrumRingOfIntegersRat σ 1 hσ
    rw [one_mul, inv_one, mul_one] at h1
    have hcoe : (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom σ =
        Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ := rfl
    rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker, hcoe]
    exact h1
  -- bridge the divergent `Algebra ℚ` spellings (MazurTorsion's statement
  -- was elaborated with `DivisionRing.toRatAlgebra`; this file boosts the
  -- canonical instances) — all `Algebra ℚ` structures are equal
  convert hle' using 2
  congr!
  exact Subsingleton.elim _ _

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

open NumberField in
set_option backward.isDefEq.respectTransparency false in
/-- **Local inertia restricts into finite-level inertia** (PROVEN
2026-07-23 — helper for the tame stratum): for a finite normal
subextension `N/Kᵥ` of `Kᵥᵃˡᵍ` and `σ` in the full local inertia
group, the restriction of `σ` to `N` lies in the inertia subgroup of
the maximal ideal of `𝒪_N = IntegralClosure 𝒪ᵥ N` inside
`Gal(N/Kᵥ)`. Same two ingredients as the intermediate-level
restriction lemma of `LocalInertiaFixedField`
(`restrictNormalHom_mem_inertia_intermediate`):
`AlgEquiv.restrictNormal_commutes` transports the difference into the
big integral closure, where it lies in `𝔪` by the DEFINING property of
`localInertiaGroup`, and maximal-ideal membership descends along the
integral-closure inclusion because `𝒪_N` is local. -/
theorem restrictNormalHom_mem_inertia_of_mem_localInertiaGroup
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (N : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
    [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]
    [Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) N]
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
    (hσ : σ ∈ localInertiaGroup v) :
    AlgEquiv.restrictNormalHom N σ ∈
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)).inertia
      (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v] N) := by
  -- the integral closure of `𝒪ᵥ` in `N` maps into the big integral closure
  letI : Algebra
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :=
    ((algebraMap N (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
      (algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N) N)).toAlgebra
  letI : Algebra
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) :=
    (RingHom.codRestrict
      (algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
      (integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
      (fun x => (Algebra.IsIntegral.isIntegral
          (R := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) x).map
        ((IsScalarTower.toAlgHom (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            N (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
          (IsScalarTower.toAlgHom (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
            N)))).toAlgebra
  rw [AddSubgroup.mem_inertia]
  intro x
  -- transport the difference into the big integral closure
  have hcomm : algebraMap
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
      ((AlgEquiv.restrictNormalHom N σ) • x - x) =
      σ • (algebraMap
          (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) x) -
        algebraMap
          (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) x := by
    rw [map_sub]
    congr 1
    apply Subtype.ext
    show algebraMap N (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        (algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
          N ((AlgEquiv.restrictNormalHom N σ) • x)) =
      σ • (algebraMap N
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        (algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N) N x))
    exact AlgEquiv.restrictNormal_commutes σ N
      (algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N) N x)
  have hbig : algebraMap
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))
      ((AlgEquiv.restrictNormalHom N σ) • x - x) ∈
      IsLocalRing.maximalIdeal
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) := by
    rw [hcomm]
    exact hσ _
  -- descend the membership along the local inclusion
  have hproper : (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))).comap
      (algebraMap
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) ≠ ⊤ := by
    intro htop
    have h1 : (1 : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N) ∈
        (IsLocalRing.maximalIdeal
          (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))).comap
        (algebraMap
          (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v) N)
          (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) :=
      htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  rw [Submodule.mem_toAddSubgroup]
  exact IsLocalRing.le_maximalIdeal hproper (Ideal.mem_comap.mpr hbig)

/-- **Irreducibility is preserved by ring actions** (helper, proven):
a group element acting by ring automorphisms maps irreducibles to
irreducibles — units transport both ways along `g` and `g⁻¹`. -/
theorem irreducible_smul {S : Type*} [CommRing S] {G : Type*} [Group G]
    [MulSemiringAction G S] (g : G) {x : S} (hx : Irreducible x) :
    Irreducible (g • x) := by
  have hsmul_unit : ∀ (g' : G) {y : S}, IsUnit y → IsUnit (g' • y) := by
    intro g' y hy
    obtain ⟨v, rfl⟩ := hy
    refine isUnit_iff_exists_inv.mpr ⟨g' • ((↑v⁻¹ : Sˣ) : S), ?_⟩
    rw [← smul_mul']
    rw [show ((v : S) * ((↑v⁻¹ : Sˣ) : S)) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
    exact smul_one g'
  constructor
  · intro h
    have h1 := hsmul_unit g⁻¹ h
    rw [inv_smul_smul] at h1
    exact hx.not_isUnit h1
  · intro b c hbc
    have hx' : x = (g⁻¹ • b) * (g⁻¹ • c) := by
      have h1 := congrArg (fun y => g⁻¹ • y) hbc
      simpa only [inv_smul_smul, smul_mul'] using h1
    rcases hx.isUnit_or_isUnit hx' with h | h
    · left
      have h1 := hsmul_unit g h
      rwa [smul_inv_smul] at h1
    · right
      have h1 := hsmul_unit g h
      rwa [smul_inv_smul] at h1

/-- **Tame conjugation kills the uniformizer twist** (PROVEN — the
generic DVR form of the tame stratum at residue cardinality `q = 2`):
in a discrete valuation domain `S` with a group acting by ring
automorphisms, if `t` is an inertia element (`t • x ≡ x mod 𝔪` for
all `x`), and `F` commutes with `t` and satisfies the `q = 2`
Frobenius congruence `F • x ≡ x² mod 𝔪`, then for every irreducible
`ϖ` the twist unit `u = (t • ϖ)/ϖ` is `≡ 1 mod 𝔪`, i.e.
`t • ϖ - ϖ ∈ 𝔪²`. Applying `F` to `t • ϖ = ϖ·u` and comparing with
`t` applied to `F • ϖ = ϖ·w` gives `w·(F • u) = u·(t • w)`; modulo
`𝔪` this reads `w·u² = u·w` with `u, w` units outside the prime `𝔪`,
so `u ≡ 1`. -/
theorem smul_irreducible_sub_mem_pow_two_of_frob
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {G : Type*} [Group G] [MulSemiringAction G S]
    {t F : G} (hcomm : F * t = t * F)
    (ht : ∀ x : S, t • x - x ∈ IsLocalRing.maximalIdeal S)
    (hF : ∀ x : S, F • x - x ^ 2 ∈ IsLocalRing.maximalIdeal S)
    {ϖ : S} (hϖ : Irreducible ϖ) :
    t • ϖ - ϖ ∈ IsLocalRing.maximalIdeal S ^ 2 := by
  classical
  -- the twist units against `t` and `F`
  obtain ⟨u, hu⟩ :=
    IsDiscreteValuationRing.associated_of_irreducible S hϖ
      (irreducible_smul t hϖ)
  obtain ⟨w, hw⟩ :=
    IsDiscreteValuationRing.associated_of_irreducible S hϖ
      (irreducible_smul F hϖ)
  -- commutation `F • (t • ϖ) = t • (F • ϖ)`, expanded through the units
  have hkey : ϖ * (↑w * (F • (↑u : S))) = ϖ * (↑u * (t • (↑w : S))) := by
    have h1 : F • (t • ϖ) = t • (F • ϖ) := by
      rw [← mul_smul, ← mul_smul, hcomm]
    rw [← hu, ← hw, smul_mul', smul_mul', ← hu, ← hw] at h1
    calc ϖ * (↑w * (F • (↑u : S)))
        = ϖ * ↑w * (F • (↑u : S)) := by ring
      _ = ϖ * ↑u * (t • (↑w : S)) := h1
      _ = ϖ * (↑u * (t • (↑w : S))) := by ring
  have hcancel : (↑w : S) * (F • (↑u : S)) = ↑u * (t • (↑w : S)) :=
    mul_left_cancel₀ hϖ.ne_zero hkey
  -- modulo `𝔪`: `u·w·(u - 1) ∈ 𝔪`
  have hm : (↑u : S) * ↑w * (↑u - 1) ∈ IsLocalRing.maximalIdeal S := by
    have hA : (↑u : S) * (t • (↑w : S) - ↑w) ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_left _ _ (ht ↑w)
    have hB : (↑w : S) * (F • (↑u : S) - ↑u ^ 2) ∈
        IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_left _ _ (hF ↑u)
    have h0 : (↑w : S) * (F • (↑u : S)) - ↑u * (t • (↑w : S)) = 0 :=
      sub_eq_zero.mpr hcancel
    have heq : (↑u : S) * ↑w * (↑u - 1)
        = ((↑u : S) * (t • (↑w : S) - ↑w))
          - ((↑w : S) * (F • (↑u : S) - ↑u ^ 2))
          + ((↑w : S) * (F • (↑u : S)) - ↑u * (t • (↑w : S))) := by
      ring
    rw [heq, h0, add_zero]
    exact Submodule.sub_mem _ hA hB
  -- units survive the prime `𝔪`
  have hprime := (IsLocalRing.maximalIdeal.isMaximal S).isPrime
  have hunit : ∀ v : Sˣ, (↑v : S) ∉ IsLocalRing.maximalIdeal S := by
    intro v hv
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hv v.isUnit)
  have hu1 : (↑u : S) - 1 ∈ IsLocalRing.maximalIdeal S := by
    rcases hprime.mem_or_mem hm with h | h
    · rcases hprime.mem_or_mem h with h' | h'
      · exact absurd h' (hunit u)
      · exact absurd h' (hunit w)
    · exact h
  -- conclude
  have hdiff : t • ϖ - ϖ = ϖ * ((↑u : S) - 1) := by
    rw [← hu]; ring
  rw [hdiff, sq]
  exact Ideal.mul_mem_mul
    ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hu1

/-- **Order-3 inertia elements fix the uniformizer** (PROVEN — the
generic DVR form of the wild stratum at residue characteristic `2`):
if `t³ = 1`, `3` is a unit in the discrete valuation domain `S`, `t`
is an inertia element, and the twist of an irreducible `ϖ` is already
trivial modulo `𝔪²` (the tame-conjugation output), then `t • ϖ = ϖ`
on the nose. Otherwise `a := t • ϖ - ϖ` is a nonzero multiple
`ϖⁿ·u` with `n ≥ 2`, the graded bound `ϖ^(n+1) ∣ t • a - a` holds
(binomial/geometric-sum estimates: `2n - 1 ≥ n + 1`), and telescoping
`t³ • ϖ = ϖ` gives `ϖ^(n+1) ∣ 3a`; since `3` is a unit this forces
`ϖ^(n+1) ∣ ϖⁿ`, contradicting `n + 1 > n`. -/
theorem smul_irreducible_eq_of_sub_mem_pow_two_of_cube
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {G : Type*} [Group G] [MulSemiringAction G S]
    {t : G} (ht : ∀ x : S, t • x - x ∈ IsLocalRing.maximalIdeal S)
    (ht3 : t ^ 3 = 1) (h3u : IsUnit (3 : S))
    {ϖ : S} (hϖ : Irreducible ϖ)
    (hsq : t • ϖ - ϖ ∈ IsLocalRing.maximalIdeal S ^ 2) :
    t • ϖ = ϖ := by
  classical
  by_contra hne
  have hane : t • ϖ - ϖ ≠ 0 := sub_ne_zero.mpr hne
  set a : S := t • ϖ - ϖ with ha
  obtain ⟨n, hn⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible hane hϖ
  obtain ⟨u, hu⟩ := hn.symm
  -- `hu : ϖ ^ n * ↑u = a`
  have hdvd_a : ϖ ^ 2 ∣ a := by
    have h1 := hsq
    rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at h1
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : ϖ ^ 2 ∣ ϖ ^ n := by
      have h2 := hdvd_a
      rw [← hu] at h2
      exact (Units.dvd_mul_right).mp h2
    have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h1
    omega
  have hϖa : ϖ ∣ a := by
    rw [← hu]
    exact Dvd.dvd.mul_right (dvd_pow_self ϖ (by omega)) _
  have htϖ : t • ϖ = ϖ + a := by rw [ha]; ring
  have hϖadd : ϖ ∣ ϖ + a := dvd_add dvd_rfl hϖa
  -- the graded bound `ϖ^(n+1) ∣ t • a - a`
  have hstep : ϖ ^ (n + 1) ∣ t • a - a := by
    have hta : t • a = (ϖ + a) ^ n * (t • (↑u : S)) := by
      conv_lhs => rw [← hu]
      rw [smul_mul', smul_pow', htϖ]
    have hdecomp : t • a - a
        = (ϖ + a) ^ n * (t • (↑u : S) - ↑u)
          + ((ϖ + a) ^ n - ϖ ^ n) * ↑u := by
      rw [hta]
      linear_combination hu
    rw [hdecomp]
    refine dvd_add ?_ ?_
    · have h1 : ϖ ^ n ∣ (ϖ + a) ^ n := pow_dvd_pow_of_dvd hϖadd n
      have h2 : ϖ ∣ (t • (↑u : S) - ↑u) := by
        have h3 := ht ↑u
        rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h3
      have h4 : ϖ ^ (n + 1) = ϖ ^ n * ϖ := by ring
      rw [h4]
      exact mul_dvd_mul h1 h2
    · have hgeom := geom_sum₂_mul (ϖ + a) ϖ n
      rw [add_sub_cancel_left] at hgeom
      rw [← hgeom]
      have hsum : ϖ ^ (n - 1) ∣
          (∑ i ∈ Finset.range n, (ϖ + a) ^ i * ϖ ^ (n - 1 - i)) := by
        refine Finset.dvd_sum fun i hi => ?_
        have hi' : i < n := Finset.mem_range.mp hi
        have h1 : ϖ ^ i ∣ (ϖ + a) ^ i := pow_dvd_pow_of_dvd hϖadd i
        have h2 : ϖ ^ (n - 1) = ϖ ^ i * ϖ ^ (n - 1 - i) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h2]
        exact mul_dvd_mul h1 dvd_rfl
      have ha' : ϖ ^ n ∣ a := ⟨↑u, hu.symm⟩
      calc ϖ ^ (n + 1)
          ∣ ϖ ^ (n - 1) * ϖ ^ n := by
            rw [← pow_add]
            exact pow_dvd_pow ϖ (by omega)
        _ ∣ (∑ i ∈ Finset.range n, (ϖ + a) ^ i * ϖ ^ (n - 1 - i)) * a :=
            mul_dvd_mul hsum ha'
        _ ∣ (∑ i ∈ Finset.range n, (ϖ + a) ^ i * ϖ ^ (n - 1 - i)) * a
              * ↑u := dvd_mul_right _ _
  -- pushing forward along `t` preserves the divisibility
  have hpush : ∀ y : S, ϖ ^ (n + 1) ∣ y → ϖ ^ (n + 1) ∣ t • y := by
    intro y hy
    obtain ⟨c, rfl⟩ := hy
    rw [smul_mul', smul_pow', htϖ]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hϖadd (n + 1)) _
  -- telescoping `t³ = 1`
  have hcube : t • (t • (t • ϖ)) = ϖ := by
    rw [← mul_smul, ← mul_smul]
    rw [show t * t * t = t ^ 3 from by rw [pow_succ, pow_two], ht3,
      one_smul]
  have hLHS : t • (t • (t • ϖ)) = ϖ + a + t • a + t • (t • a) := by
    rw [htϖ, smul_add, htϖ, smul_add, smul_add, htϖ]
  have h3a : (3 : S) * a
      = -((2 : S) * (t • a - a) + (t • (t • a) - t • a)) := by
    have h0 := hLHS.symm.trans hcube
    linear_combination h0
  have hdvd3a : ϖ ^ (n + 1) ∣ (3 : S) * a := by
    rw [h3a]
    refine dvd_neg.mpr (dvd_add (Dvd.dvd.mul_left hstep 2) ?_)
    have h1 : t • (t • a) - t • a = t • (t • a - a) := (smul_sub t _ _).symm
    rw [h1]
    exact hpush _ hstep
  have hdvda : ϖ ^ (n + 1) ∣ a := (h3u.dvd_mul_left).mp hdvd3a
  have hfin : ϖ ^ (n + 1) ∣ ϖ ^ n := by
    have h1 := hdvda
    rw [← hu] at h1
    exact (Units.dvd_mul_right).mp h1
  have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hfin
  omega

/-- **Fixing all irreducibles fixes everything** (helper, proven): in a
discrete valuation domain, a ring action fixing every irreducible fixes
every element — units are quotients of irreducibles (`ϖ·v` is again
irreducible), and every nonzero element is a unit multiple of a power
of an irreducible. -/
theorem smul_eq_self_of_forall_irreducible_smul_eq
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {G : Type*} [Group G] [MulSemiringAction G S]
    {t : G} (hfix : ∀ ϖ : S, Irreducible ϖ → t • ϖ = ϖ) (x : S) :
    t • x = x := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · exact smul_zero t
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  obtain ⟨u, hu⟩ := hn.symm
  -- units are fixed
  have hufix : ∀ v : Sˣ, t • (↑v : S) = ↑v := by
    intro v
    have hass : Associated ϖ (ϖ * ↑v) := ⟨v, rfl⟩
    have hirr := hass.irreducible hϖ
    have h1 := hfix _ hirr
    rw [smul_mul', hfix ϖ hϖ] at h1
    exact mul_left_cancel₀ hϖ.ne_zero h1
  rw [← hu, smul_mul', smul_pow', hfix ϖ hϖ, hufix u]

open NumberField in
set_option backward.isDefEq.respectTransparency false in
/-- **The residue field of `ℚ₂`'s completed integers has `2` elements**
(PROVEN — transported from the big-integral-closure residue count
`natCard_residue_quotient_toHeightOneSpectrum` along the identification
of the contracted maximal ideal with `𝔪 𝒪ᵥ`). -/
theorem natCard_quotient_maximalIdeal_two :
    Nat.card ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) = 2 := by
  have h := natCard_residue_quotient_toHeightOneSpectrum Nat.prime_two
  have hunder : ((IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)))).under
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) =
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under _ _)
  rwa [hunder] at h

open NumberField in
/-- **Finite-level tame core at `2`** (PROVEN; label corrected
2026-07-25 — the arithmetic
content of the tame stratum): a finite Galois subextension `N/ℚ₂` of
`ℚ₂ᵃˡᵍ` whose Galois group is abelian of exponent `3` is unramified —
the inertia subgroup of the maximal ideal of `𝒪_N` is trivial.
Route: `|G| = 3^k` (Cauchy), so `e = |I|` (finite-level `|I| = e`,
`card_inertia_finite_level`) is a power of `3`, odd — the extension is
tamely ramified. For `t ∈ I` and a uniformizer `ϖ` of the DVR `𝒪_N`,
write `t(ϖ) = ϖ·u_t`; the residue `θ(t) = ū_t ∈ k_Nˣ` satisfies
`θ(F t F⁻¹) = θ(t)²` for an arithmetic Frobenius `F` at `𝔪_N`
(`IsArithFrobAt.exists_of_isInvariant`; the residue cardinality of
`𝒪ᵥ` at `2` is `2`, `natCard_residue_quotient_toHeightOneSpectrum`);
commutativity gives `θ(t) = θ(t)²`, so `θ(t) = 1`, i.e.
`t(ϖ) ≡ ϖ mod 𝔪²`. Then `t = 1`: otherwise, over the fixed field
`T = N^⟨t⟩` the extension is totally ramified of degree `3`
(`card_inertia_intermediate`), so `N = T(ϖ)`, and with
`a := t(ϖ) - ϖ ≠ 0` of valuation `j ≥ 2` one has `t(a) ≡ a mod 𝔪^{j+1}`
and hence `ϖ = t³(ϖ) ≡ ϖ + 3a mod 𝔪^{j+1}`; since `3` is a unit in
`𝒪_N` (residue characteristic `2`), `a ∈ 𝔪^{j+1}` — contradiction. -/
theorem finiteLevel_inertia_eq_bot_of_exponent_three_at_two
    (N : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)))
    [FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N]
    [IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N]
    (hcomm : ∀ g h : (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] N),
      g * h = h * g)
    (h3 : ∀ g : (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] N),
      g ^ 3 = 1) :
    (IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N)).inertia
      (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] N) = ⊥ := by
  classical
  -- instance assembly: fraction ring, invariants, finite residue
  haveI : IsFractionRing (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) N :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N _
  haveI : Module.Finite
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) :=
    IsIntegralClosure.finite
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N _
  haveI := hasFiniteQuotients_adicCompletionIntegers
    Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
  haveI : Ring.HasFiniteQuotients (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) :=
    Ring.HasFiniteQuotients.of_module_finite
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) _
  haveI : Finite ((IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) ⧸
      IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N)) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (IsDiscreteValuationRing.not_a_field _)
  haveI : (IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  -- an arithmetic Frobenius at the maximal ideal
  obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
    (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] N)
    (IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N))
  -- the Frobenius exponent is `2`
  have hunder : IsLocalRing.maximalIdeal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) =
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N)).under
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
    Ideal.LiesOver.over
  have hq : Nat.card
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N)).under
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) = 2 := by
    rw [← hunder]
    exact natCard_quotient_maximalIdeal_two
  have hF2 : ∀ x : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N,
      F • x - x ^ 2 ∈ IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) := by
    intro x
    have h1 := hF x
    rwa [hq] at h1
  -- `3` is a unit (`2`-adically)
  have h3uv : IsUnit ((3 : ℕ) :
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) := by
    by_contra h3n
    have h3m : ((3 : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) ∈
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      (IsLocalRing.mem_maximalIdeal _).mpr h3n
    haveI : Finite
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      inferInstanceAs (Finite (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)))
    haveI : Fintype
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      Fintype.ofFinite _
    have h2zero : ((2 : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) = 0 := by
      have h1 := Nat.cast_card_eq_zero
        ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
      rwa [← Nat.card_eq_fintype_card,
        natCard_quotient_maximalIdeal_two] at h1
    have h3q : ((3 : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) = 0 := by
      have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr h3m
      rwa [map_natCast] at h1
    have h32 : ((3 : ℕ) :
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) ⧸
        IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) =
        ((2 : ℕ) : _) + 1 := by
      push_cast
      ring
    rw [h32, h2zero, zero_add] at h3q
    exact one_ne_zero h3q
  have h3u : IsUnit ((3 : ℕ) : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) := by
    have h1 := h3uv.map (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N))
    rwa [map_natCast] at h1
  -- every inertia element is trivial
  rw [Subgroup.eq_bot_iff_forall]
  intro t htI
  have ht : ∀ x : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N,
      t • x - x ∈ IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) := by
    intro x
    have h1 := (AddSubgroup.mem_inertia).mp htI x
    rwa [Submodule.mem_toAddSubgroup] at h1
  have ht3u : ((3 : ℕ) : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) = (3 :
      IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) := by
    norm_cast
  have hfix : ∀ ϖ : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N,
      Irreducible ϖ → t • ϖ = ϖ := by
    intro ϖ hϖ
    refine smul_irreducible_eq_of_sub_mem_pow_two_of_cube ht (h3 t)
      (ht3u ▸ h3u) hϖ ?_
    exact smul_irreducible_sub_mem_pow_two_of_frob (hcomm F t) ht hF2 hϖ
  have hallO := smul_eq_self_of_forall_irreducible_smul_eq hfix
  -- extend the triviality to the fraction field `N`
  have hb : ∀ w : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N,
      t (algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) N w)
      = algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) N (t • w) :=
    fun w => rfl
  refine AlgEquiv.ext fun z => ?_
  obtain ⟨x, y, -, hz⟩ := IsFractionRing.div_surjective
    (A := IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) N) z
  rw [← hz, AlgEquiv.one_apply, map_div₀, hb x, hb y, hallO x, hallO y]

/-- **Exponent-3 characters of `Γ ℚ` die on inertia at `2`** (DERIVED
2026-07-23 from the finite-level tame core and the restriction helper —
the tame stratum, group form): a homomorphism `φ` from `Γ ℚ` to an
abelian group of exponent `3` with open kernel kills the image of the
local inertia at `2`. The composite `ψ = φ ∘ map` on `Γ ℚ₂` has open
normal kernel, cutting out a finite Galois subextension `N/ℚ₂`
(`InfiniteGalois.fixingSubgroup_fixedField`); lifting elements of
`Gal(N/ℚ₂)` along the restriction and pushing the relations through
`ψ` shows `Gal(N/ℚ₂)` is abelian of exponent `3` (the target `A` is),
so the finite-level tame core makes `N/ℚ₂` unramified; the restriction
of `σ` lies in the finite-level inertia (the restriction helper),
hence is trivial, i.e. `σ` fixes `N`, i.e. `ψ σ = 1`. -/
theorem threeTorsion_monoidHom_vanishes_on_localInertia_at_two
    {A : Type*} [CommGroup A] (φ : (Γ ℚ) →* A)
    (hopen : IsOpen ((φ.ker : Subgroup (Γ ℚ)) : Set (Γ ℚ)))
    (h3 : ∀ x : Γ ℚ, φ x ^ 3 = 1)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :
    φ (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
  classical
  -- the composite character of `Γ ℚ₂`
  set ψ : (Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) →* A :=
    φ.comp (Field.absoluteGaloisGroup.map
      (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
    with hψdef
  show ψ σ = 1
  -- its kernel is open, normal, closed
  have hψopen : IsOpen ((ψ.ker : Subgroup _) : Set (Γ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) := by
    have hpre : ((ψ.ker : Subgroup _) : Set (Γ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) =
        (Field.absoluteGaloisGroup.map
          (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) ⁻¹'
          ((φ.ker : Subgroup (Γ ℚ)) : Set (Γ ℚ)) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, hψdef,
        MonoidHom.coe_comp, Function.comp_apply]
      rfl
    rw [hpre]
    exact (ContinuousMonoidHom.continuous_toFun _).isOpen_preimage _ hopen
  have hψnormal : (ψ.ker).Normal := ψ.normal_ker
  have hψclosed : IsClosed ((ψ.ker : Subgroup _) : Set (Γ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) :=
    Subgroup.isClosed_of_isOpen _ hψopen
  -- ambient Galois instances over `ℚ₂`
  haveI : Algebra.IsIntegral
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
    Algebra.IsAlgebraic.isIntegral
  haveI : IsGalois
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) := ⟨⟩
  -- the finite Galois subextension cut out by the kernel
  set L : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
    IntermediateField.fixedField
      (ψ.ker : Subgroup
        ((AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) ≃ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))))
  have hfix : L.fixingSubgroup = ψ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨ψ.ker, hψclosed⟩
  haveI hfd : FiniteDimensional
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hψopen)
  haveI hgal : IsGalois
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) L :=
    (InfiniteGalois.normal_iff_isGalois L).mp (by rw [hfix]; exact hψnormal)
  haveI : Normal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) L :=
    hgal.to_normal
  -- membership in `ψ.ker` is detected by the restriction to `L`
  have hdetect : ∀ g : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat),
      (AlgEquiv.restrictNormalHom L g = 1 ↔ ψ g = 1) := by
    intro g
    constructor
    · intro hg
      have hmem : g ∈ L.fixingSubgroup := by
        rw [← IntermediateField.restrictNormalHom_ker L]
        exact MonoidHom.mem_ker.mpr hg
      rw [hfix] at hmem
      exact MonoidHom.mem_ker.mp hmem
    · intro hg
      have hmem : g ∈ L.fixingSubgroup := by
        rw [hfix]
        exact MonoidHom.mem_ker.mpr hg
      rw [← IntermediateField.restrictNormalHom_ker L] at hmem
      exact MonoidHom.mem_ker.mp hmem
  -- relations transfer to `Gal(L/ℚ₂)` along lifts
  have hsurj : ∀ g : (L ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] L),
      ∃ g' : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat),
      AlgEquiv.restrictNormalHom L g' = g := fun g =>
    AlgEquiv.restrictNormalHom_surjective
      (F := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
      (K₁ := L)
      (E := AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) g
  have hLcomm : ∀ g h : (L ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] L), g * h = h * g := by
    intro g h
    obtain ⟨g', rfl⟩ := hsurj g
    obtain ⟨h', rfl⟩ := hsurj h
    have hcommutator : ψ (g' * h' * (g'⁻¹ * h'⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have : ψ g' * ψ h' * ((ψ g')⁻¹ * (ψ h')⁻¹) = 1 := by
        rw [mul_comm (ψ g') (ψ h'), mul_assoc, ← mul_assoc (ψ g'),
          mul_inv_cancel, one_mul, mul_inv_cancel]
      exact this
    have h1 := (hdetect _).mpr hcommutator
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : (AlgEquiv.restrictNormalHom L g') * (AlgEquiv.restrictNormalHom L h')
        = ((AlgEquiv.restrictNormalHom L h') * (AlgEquiv.restrictNormalHom L g')) := by
      have h3 := congrArg (· * ((AlgEquiv.restrictNormalHom L h') *
        (AlgEquiv.restrictNormalHom L g'))) h1
      simpa [mul_assoc] using h3
    exact h2
  have hL3 : ∀ g : (L ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat] L), g ^ 3 = 1 := by
    intro g
    obtain ⟨g', rfl⟩ := hsurj g
    have hcube : ψ (g' ^ 3) = 1 := by
      rw [map_pow]
      exact h3 (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) g')
    have h1 := (hdetect _).mpr hcube
    rwa [map_pow] at h1
  -- the finite-level tame core: `L/ℚ₂` is unramified
  have hbot := finiteLevel_inertia_eq_bot_of_exponent_three_at_two L hLcomm hL3
  -- the restriction of `σ` is a finite-level inertia element, hence trivial
  have hmem := restrictNormalHom_mem_inertia_of_mem_localInertiaGroup
    Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat L σ hσ
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (hdetect σ).mp hmem

/-- **Approximate homomorphisms die on inertia at `2`** (DERIVED
2026-07-23 from the group-form leaf above — the tame stratum): a
function `T` on `Γ ℚ` with values in `𝔪ⁿ⁺¹` which is a homomorphism
modulo `𝔪ⁿ⁺²` and has open congruence kernel kills the local inertia
at `2`. Modulo `𝔪ⁿ⁺²` the function is an honest homomorphism into the
additive group of `R ⧸ 𝔪ⁿ⁺²` whose image is `3`-torsion (`3 ∈ 𝔪`,
`three_mem_maximalIdeal`, so `3·T g ∈ 𝔪·𝔪ⁿ⁺¹ = 𝔪ⁿ⁺²`) with open
kernel (`hTopen`); the group-form leaf applies. No hypothesis on
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
  classical
  -- `T 1` is already congruent to `0`
  have hT1 : T 1 ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have h := hThom 1 1
    rw [mul_one, show T 1 - (T 1 + T 1) = -(T 1) by ring] at h
    exact neg_mem_iff.mp h
  -- the induced honest homomorphism into the additive group of `R ⧸ 𝔪ⁿ⁺²`
  let φ : (Γ ℚ) →* Multiplicative
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) :=
    { toFun := fun g => Multiplicative.ofAdd
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2)) (T g))
      map_one' := by
        have h0 : Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal R ^ (n + 2)) (T 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hT1
        simp only [h0, ofAdd_zero]
      map_mul' := fun g h => by
        have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2))
            (T (g * h) - (T g + T h)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (hThom g h)
        rw [map_sub, map_add, sub_eq_zero] at h0
        simpa [← ofAdd_add] using congrArg Multiplicative.ofAdd h0 }
  -- membership in the kernel is the congruence condition
  have hφker : ∀ g : Γ ℚ, φ g = 1 ↔
      T g ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g
    rw [show φ g = Multiplicative.ofAdd
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2)) (T g))
        from rfl,
      ofAdd_eq_one, Ideal.Quotient.eq_zero_iff_mem]
  -- the kernel is open
  have hopen : IsOpen ((φ.ker : Subgroup (Γ ℚ)) : Set (Γ ℚ)) := by
    have hset : ((φ.ker : Subgroup (Γ ℚ)) : Set (Γ ℚ)) =
        {g : Γ ℚ | T g ∈ IsLocalRing.maximalIdeal R ^ (n + 2)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq,
        hφker g]
    rw [hset]
    exact hTopen
  -- the image is `3`-torsion: `3·T g ∈ 𝔪·𝔪ⁿ⁺¹ = 𝔪ⁿ⁺²`
  have h3 : ∀ x : Γ ℚ, φ x ^ 3 = 1 := by
    intro x
    have hmem : (3 : ℕ) • T x ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      rw [nsmul_eq_mul]
      have h1 : ((3 : ℕ) : R) * T x ∈
          IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R ^ (n + 1) :=
        Ideal.mul_mem_mul
          (by rw [Nat.cast_ofNat]; exact three_mem_maximalIdeal) (hT x)
      rwa [← pow_succ'] at h1
    have h0 : (3 : ℕ) • (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal R ^ (n + 2)) (T x)) = 0 := by
      rw [← map_nsmul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [show φ x = Multiplicative.ofAdd
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 2)) (T x))
        from rfl,
      ← ofAdd_nsmul, h0, ofAdd_zero]
  -- the group-form leaf kills the inertia image
  exact (hφker _).mp
    (threeTorsion_monoidHom_vanishes_on_localInertia_at_two φ hopen h3 σ hσ)


/-- **An invariant functional's `v₀`-defect is unramified at `3`**
(PROVEN 2026-07-25 from the connected–étale leaf
`exists_connectedEtale_line_of_hopf_package` above, which now holds
all of the finite-flat content; the functional-side argument is
PROVEN here and is short. Fontaine, Raynaud 1974, and the
Fontaine/Raynaud material in Cornell–Silverman–Stevens): given an
EXPLICIT finite flat Hopf algebra `G` over `𝒪ᵥ ≅ ℤ₃` with étale
generic fibre whose geometric points are `Γ ℚ₃ᵥ`-equivariantly
identified with the space `(R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` of the congruence
quotient `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)`, and an `R`-linear functional `Φ`
on `V` which is Galois-invariant modulo `𝔪ⁿ⁺²` BOTH on the congruence
sublattice `𝔪V` (`hΦm`) AND on the residual sub-line `R w₀` (`hΦw`),
the `v₀`-defect `D g = Φ (ρ g v₀) - Φ v₀` vanishes at the image of a
local inertia element at `3`.

CONNECTED–ÉTALE HALF ALREADY SUPPLIED (2026-07-25, reconciling the two
rival cuts of this node): the connected counit idempotent `e₀` of the
Hopf order — with `hmin₀`/`habs₀` characterising it as the coordinate
ring of the identity component, exactly as
`Bialgebra.exists_connected_counit_idempotent` produces it — and
`hconn`, the statement that every inertia displacement at this `σ` is
connected, are hypotheses here rather than obligations. `hconn` is
PROVEN upstream in
`inertia_displacement_apply_connected_idempotent_eq_one` and discharged
by the consumer below. Both are consumed here by being handed to
`exists_connectedEtale_line_of_hopf_package`, so what the tree still
owes is only the identification of the connected part with a
Galois-stable line — the étale-by-étale classification and the
unramifiedness of the points.

Proof (residue characteristic `3 > 2`), in three moves once the
connected–étale leaf has produced the generator `w₁ ≡ w₀ mod 𝔪V` of
the connected line, its diagonal entry `E`, and the unramifiedness of
the étale quotient.

(1) REPAIRED 2026-07-26, following the faithfulness repair of the leaf
(whose stability clause is local at `3`, not `Γ ℚ`-wide). The residual
diagonal entry `a` along `w₀` for the whole of `Γ ℚ` comes from
`exists_residual_matrix_entries`, which needs only `hπequiv` and no
finite-flat input at all; `residual_twist_eq_cyclotomicCharacterModL`
applies to `a`. The distinguished element `g₀` with `ω g₀ ≠ 1` is now
taken from `exists_local_cyclotomicCharacterModL_three_ne_one`, so that
it lies in the DECOMPOSITION GROUP AT `3`, where the leaf's diagonal
entry `E` is defined; `ω` is ramified at `3`, so such an element exists.
`E g₀` is a residual diagonal entry along `w₀` as well: `𝔪ⁿ⁺² ≤ 𝔪`, and
`w₁ − w₀ ∈ 𝔪V` is carried into `𝔪V` both by `ρ g₀`
(`apply_mem_smul_top`) and by the scalar `E g₀`, so
`ρ g₀ w₀ − E g₀ • w₀ ∈ 𝔪V`; subtracting the same statement for `a g₀`
and extracting the scalar along the residually nonzero `w₀`
(`mem_maximalIdeal_of_smul_mem_smul_top`) gives `a g₀ − E g₀ ∈ 𝔪`, hence
`E g₀ + 1 ∈ 𝔪`. Since `3 ∈ 𝔪` (`three_mem_maximalIdeal`) while
`1 ∉ 𝔪`, the residue characteristic is `3` and `2` is a UNIT; so
`E g₀ − 1 = (E g₀ + 1) − 2` is a unit too. This is the one place the
oddness of the residual character is spent, and it is why the argument
is specific to `p = 3 > 2`.

(2) `Φ w₁ ∈ 𝔪ⁿ⁺²`. The two invariance hypotheses combine into
invariance along `w₁`: `Φ (ρ g₀ w₁) − Φ w₁` is the sum of
`Φ (ρ g₀ w₀) − Φ w₀` (`hΦw`) and `Φ (ρ g₀ z) − Φ z` for
`z = w₁ − w₀ ∈ 𝔪V` (`hΦm`), so it lies in `𝔪ⁿ⁺²`. On the other hand
the stability of the line gives `Φ (ρ g₀ w₁) − E g₀ * Φ w₁ ∈ 𝔪ⁿ⁺²`
(`linearMap_apply_mem_of_mem_smul_top`). Subtracting,
`(E g₀ − 1) * Φ w₁ ∈ 𝔪ⁿ⁺²`, and `E g₀ − 1` is a unit by (1).

(3) The defect follows the line into `𝔪ⁿ⁺²`: unramifiedness of the
étale quotient gives `c` with
`ρ σ v₀ − (v₀ + c • w₁) ∈ 𝔪ⁿ⁺²V`, so
`Φ (ρ σ v₀) − Φ v₀ − c * Φ w₁ ∈ 𝔪ⁿ⁺²`, and `c * Φ w₁ ∈ 𝔪ⁿ⁺²` by (2).

Note that the `v₀`-defect is never shown to be a homomorphism here:
that route (presenting the trivial-by-trivial extension as a Galois
quotient of `M` and calling it étale-by-étale) needs the quotient to
be realised by a finite flat group scheme, i.e. Raynaud's
subquotient-closure, whereas the route above needs only the
connected–étale sequence of `M` itself. -/
theorem invariant_functional_defect_vanishes_of_hopf_package
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
    (n : ℕ) (Φ : V →ₗ[R] R)
    (hΦm : ∀ (g : Γ ℚ) (x : V),
      x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) →
      Φ (ρ g x) - Φ x ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (hΦw : ∀ g : Γ ℚ,
      Φ (ρ g w₀) - Φ w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (G : Type) [CommRing G]
    [HopfAlgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange
          (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
    (σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪₃ᵥ) e₀ = (1 : 𝒪₃ᵥ))
    (hmin₀ : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪₃ᵥ) y = (1 : 𝒪₃ᵥ) → y = e₀)
    (habs₀ : Bialgebra.comulAlgHom 𝒪₃ᵥ G e₀ * (e₀ ⊗ₜ[𝒪₃ᵥ] e₀) = e₀ ⊗ₜ[𝒪₃ᵥ] e₀)
    (hconn : ∀ m : (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2))) ⊗[R] V,
      (Additive.toMul ((Equiv.ofBijective fG hfG).symm
        (((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
          𝔭₃) σ m - m))) ((1 : ℚ₃ᵥ) ⊗ₜ[𝒪₃ᵥ] e₀) = 1) :
    Φ (ρ (Field.absoluteGaloisGroup.map
        (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) v₀)
      - Φ v₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
  classical
  -- the image of `σ` in the global Galois group
  set σ' : Γ ℚ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ with hσ'
  -- the connected–étale splitting of the flat package
  obtain ⟨w₁, hw₁, ⟨E, hE⟩, c, hc⟩ :=
    exists_connectedEtale_line_of_hopf_package V hV hρ kk hsurj π hπsurj
      hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n G fG hfG σ hσ e₀ he₀ hε₀ hmin₀ habs₀
      hconn
  -- (1a) the residual diagonal entry along `w₀`, for the WHOLE of `Γ ℚ`.
  -- No finite-flat input is needed for this: `ker π` is the residual line
  -- spanned by `w₀`, and `hπequiv` makes it Galois-stable modulo `𝔪`.
  obtain ⟨a, _c, hac⟩ :=
    exists_residual_matrix_entries hV kk hsurj π hπsurj hπequiv w₀ v₀
      hw₀π hw₀ne
  have hEa : ∀ g : Γ ℚ, ρ g w₀ - a g • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := fun g => (hac g).1
  -- (1b) an element of the DECOMPOSITION GROUP AT `3` where the mod-3
  -- cyclotomic character is nontrivial, packaged with the diagonal entry of
  -- the connected line there. The flat package only ever sees `Γ ℚ₃ᵥ`, so
  -- the distinguished element has to be produced locally
  -- (`exists_local_cyclotomicCharacterModL_three_ne_one`); the global
  -- `exists_cyclotomicCharacterModL_three_ne_one` is of no use here.
  obtain ⟨g₀, Eg₀, hg₀, hEg₀⟩ :
      ∃ (g : Γ ℚ) (e : R), cyclotomicCharacterModL 3 g ≠ 1 ∧
        ρ g w₁ - e • w₁ ∈
          (IsLocalRing.maximalIdeal R ^ (n + 2)) • (⊤ : Submodule R V) := by
    obtain ⟨g, hg⟩ := exists_local_cyclotomicCharacterModL_three_ne_one
    exact ⟨_, E g, hg, hE g⟩
  -- (1c) `Eg₀` is a residual diagonal entry along `w₀` as well as along `w₁`,
  -- so it agrees with `a g₀` modulo `𝔪`
  have hEw₀ : ρ g₀ w₀ - Eg₀ • w₀ ∈
      (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
    have hle : IsLocalRing.maximalIdeal R ^ (n + 2) ≤
        IsLocalRing.maximalIdeal R := Ideal.pow_le_self (by omega)
    have h1 : ρ g₀ w₁ - Eg₀ • w₁ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      Submodule.smul_mono_left hle hEg₀
    have h2 : ρ g₀ (w₁ - w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      apply_mem_smul_top (ρ g₀) hw₁
    have h3 : Eg₀ • (w₁ - w₀) ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      Submodule.smul_mem _ _ hw₁
    have heq : ρ g₀ w₀ - Eg₀ • w₀ =
        (ρ g₀ w₁ - Eg₀ • w₁) - (ρ g₀ (w₁ - w₀) - Eg₀ • (w₁ - w₀)) := by
      simp only [map_sub, smul_sub]
      abel
    rw [heq]
    exact Submodule.sub_mem _ h1 (Submodule.sub_mem _ h2 h3)
  have hdiff : a g₀ - Eg₀ ∈ IsLocalRing.maximalIdeal R := by
    have hsm : (a g₀ - Eg₀) • w₀ ∈
        (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) := by
      have heq : (a g₀ - Eg₀) • w₀ =
          (ρ g₀ w₀ - Eg₀ • w₀) - (ρ g₀ w₀ - a g₀ • w₀) := by
        rw [sub_smul]
        abel
      rw [heq]
      exact Submodule.sub_mem _ hEw₀ (hEa g₀)
    exact mem_maximalIdeal_of_smul_mem_smul_top kk hsurj hw₀ne hsm
  have hE₀ : Eg₀ + 1 ∈ IsLocalRing.maximalIdeal R := by
    have ha₀ : a g₀ + 1 ∈ IsLocalRing.maximalIdeal R :=
      (residual_twist_eq_cyclotomicCharacterModL V hV hρ kk hsurj π hπsurj
        hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a hEa g₀).2 hg₀
    have heq : Eg₀ + 1 = (a g₀ + 1) - (a g₀ - Eg₀) := by ring
    rw [heq]
    exact Submodule.sub_mem _ ha₀ hdiff
  -- the residue characteristic is `3`, so `2` is a unit
  have h2R : (2 : R) ∉ IsLocalRing.maximalIdeal R := by
    intro h2
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have hrw : (1 : R) = 3 - 2 := by norm_num
      rw [hrw]
      exact Submodule.sub_mem _ three_mem_maximalIdeal h2
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1
  obtain ⟨u, hu⟩ : IsUnit (Eg₀ - 1) := by
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmem => h2R ?_
    have hrw : (2 : R) = (Eg₀ + 1) - (Eg₀ - 1) := by ring
    rw [hrw]
    exact Submodule.sub_mem _ hE₀ hmem
  -- (2) the functional kills the connected generator at level `n + 2`
  have hstab : Φ (ρ g₀ w₁) - Eg₀ * Φ w₁ ∈
      IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have h := linearMap_apply_mem_of_mem_smul_top Φ hEg₀
    simpa only [map_sub, map_smul, smul_eq_mul] using h
  have hinv : Φ (ρ g₀ w₁) - Φ w₁ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have hz : Φ (ρ g₀ (w₁ - w₀)) - Φ (w₁ - w₀) ∈
        IsLocalRing.maximalIdeal R ^ (n + 2) := hΦm g₀ (w₁ - w₀) hw₁
    have heq : Φ (ρ g₀ w₁) - Φ w₁ =
        (Φ (ρ g₀ w₀) - Φ w₀) + (Φ (ρ g₀ (w₁ - w₀)) - Φ (w₁ - w₀)) := by
      simp only [map_sub]
      ring
    rw [heq]
    exact Ideal.add_mem _ (hΦw g₀) hz
  have hΦw₁ : Φ w₁ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have hmul : (Eg₀ - 1) * Φ w₁ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have heq : (Eg₀ - 1) * Φ w₁ =
          (Φ (ρ g₀ w₁) - Φ w₁) - (Φ (ρ g₀ w₁) - Eg₀ * Φ w₁) := by ring
      rw [heq]
      exact Ideal.sub_mem _ hinv hstab
    have hrw : Φ w₁ = ((u⁻¹ : Rˣ) : R) * ((Eg₀ - 1) * Φ w₁) := by
      rw [← mul_assoc, ← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mul]
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hmul
  -- (3) the étale quotient is unramified, so the defect follows `Φ w₁`
  rw [← hσ'] at hc
  have hcΦ := linearMap_apply_mem_of_mem_smul_top Φ hc
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at hcΦ
  have heq : Φ (ρ σ' v₀) - Φ v₀ =
      (Φ (ρ σ' v₀) - (Φ v₀ + c * Φ w₁)) + c * Φ w₁ := by ring
  rw [heq]
  exact Ideal.add_mem _ hcΦ (Ideal.mul_mem_left _ _ hΦw₁)

/-- **The trivial-component Hopf-package core at `3`** (DECOMPOSED
2026-07-25 into the invariant-functional leaf
`invariant_functional_defect_vanishes_of_hopf_package` above — the
finite-flat/Fontaine content; the CORRECTED FUNCTIONAL and all the
`a`/`c`/`s` bookkeeping are PROVEN here. The corrected functional is
`Φ := f + s · y`, where `y : V →ₗ[R] R` is any functional normalised
at `w₀` (`y w₀ = 1`; it exists because `w₀ ∉ 𝔪V`, so some coordinate
of `w₀` along a basis is a unit). Then: `Φ` is Galois-invariant modulo
`𝔪ⁿ⁺²` on `𝔪V`, because `f`'s defect is `𝔪ⁿ⁺¹`-valued and hence
`𝔪 · 𝔪ⁿ⁺¹ = 𝔪ⁿ⁺²`-valued on `𝔪V` (`linearMap_apply_mem_mul_of_forall_mem`)
while `s · (y-defect)` lies in `𝔪ⁿ⁺¹ · 𝔪`; and `Φ` is Galois-invariant
modulo `𝔪ⁿ⁺²` on the `w₀`-line, because `y (ρ g w₀) ≡ a g` by `ha` and
the ω-correction `hsA` is exactly the statement that
`(f (ρ g w₀) - f w₀) + (a g - 1) * s` dies at level `n + 2`. Finally
`y (ρ σ v₀) - y v₀ ≡ c σ` by `hc`, so the leaf's conclusion
`Φ (ρ σ v₀) - Φ v₀ ∈ 𝔪ⁿ⁺²` is the goal `(f (ρ σ v₀) - f v₀) + c σ * s
∈ 𝔪ⁿ⁺²` up to an `𝔪ⁿ⁺¹ · 𝔪` error. Fontaine, Raynaud 1974, and the
Fontaine/Raynaud material in Cornell–Silverman–Stevens): given an
EXPLICIT finite flat Hopf
algebra `G` over `𝒪ᵥ ≅ ℤ₃` with étale generic fibre whose geometric
points are `Γ ℚ₃ᵥ`-equivariantly identified with the space
`(R ⧸ 𝔪ⁿ⁺²) ⊗[R] V` of the congruence quotient
`ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` (the witness packaged by
`GaloisRep.HasFlatProlongationAt`, unpacked by the consumer from its
hypothesis `hflat`), and the corrected trivial component
`T : g ↦ (f (ρ g v₀) - f v₀) + c g * s` — an honest homomorphism
modulo `𝔪ⁿ⁺²` (hypothesis `hThom`, PROVEN upstream from the
ω-correction `hsA` and the residual multiplicativity of `c`) with
values in `𝔪ⁿ⁺¹` (hypothesis `hT1`) — the value of `T` at the image
of a local inertia element at `3` lands in `𝔪ⁿ⁺²`. The finite-flat
content — the connected–étale sequence over the henselian `ℤ₃`, the
étale-by-étale corner, and the unramifiedness of the points of a
finite étale group scheme — now lives in the leaf above, applied to
the corrected functional `Φ`. -/
theorem trivial_component_vanishes_of_hopf_package
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
        IsLocalRing.maximalIdeal R ^ (n + 2))
    (hT1 : ∀ g : Γ ℚ, (f (ρ g v₀) - f v₀) + c g * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 1))
    (hThom : ∀ g h : Γ ℚ,
      ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
        - (((f (ρ g v₀) - f v₀) + c g * s)
          + ((f (ρ h v₀) - f v₀) + c h * s))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (G : Type) [CommRing G]
    [HopfAlgebra (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Flat (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Module.Finite (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) G]
    [Algebra.Etale (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G)]
    (fG : Additive ((IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ⊗[
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] G →ₐ[
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) →+[
        Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)]
      (((ρ.baseChange
          (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).toLocal
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat).Space))
    (hfG : Function.Bijective fG)
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
  classical
  -- the image of `σ` in the global Galois group
  set σ' : Γ ℚ := Field.absoluteGaloisGroup.map
    (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ with hσ'
  -- `w₀` is not in `𝔪V`, so some basis coordinate of it is a unit and
  -- there is a functional normalised at `w₀`
  have hwnot : w₀ ∉ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
    fun hmem => hw₀ne (one_tmul_eq_zero_of_mem_maximalIdeal_smul_top kk hsurj hmem)
  obtain ⟨y, hyw₀⟩ : ∃ y : V →ₗ[R] R, y w₀ = 1 := by
    let bV := Module.Free.chooseBasis R V
    have hex : ∃ i, bV.repr w₀ i ∉ IsLocalRing.maximalIdeal R := by
      by_contra hcon
      have hcon' : ∀ i, bV.repr w₀ i ∈ IsLocalRing.maximalIdeal R := by
        intro i
        by_contra hi
        exact hcon ⟨i, hi⟩
      refine hwnot ?_
      have hsum : w₀ = ∑ i, bV.repr w₀ i • bV i := (bV.sum_repr w₀).symm
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hcon' i) trivial
    obtain ⟨i₀, hi₀⟩ := hex
    obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hi₀
    refine ⟨((u⁻¹ : Rˣ) : R) • bV.coord i₀, ?_⟩
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← hu]
    exact u.inv_mul
  -- the corrected functional
  set Φ : V →ₗ[R] R := f + s • y with hΦdef
  have hΦapp : ∀ x : V, Φ x = f x + s * y x := by
    intro x
    simp only [hΦdef, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  -- `Φ` is Galois-invariant modulo `𝔪ⁿ⁺²` on the congruence sublattice
  have hΦm : ∀ (g : Γ ℚ) (x : V),
      x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) →
      Φ (ρ g x) - Φ x ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g x hx
    have hfx : f (ρ g x) - f x ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      set Dg : V →ₗ[R] R := f.comp (ρ g) - f with hDg
      have hDapp : ∀ w : V, Dg w = f (ρ g w) - f w := fun w => rfl
      have hDval : ∀ w : V, Dg w ∈ IsLocalRing.maximalIdeal R ^ (n + 1) := by
        intro w
        rw [hDapp w]
        exact hf g w
      have hD := linearMap_apply_mem_mul_of_forall_mem Dg hDval hx
      rw [hDapp x, ← pow_succ'] at hD
      exact hD
    have hgx : ρ g x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R V) :=
      apply_mem_smul_top (ρ g) hx
    have hsy : s * (y (ρ g x) - y x) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h1 := Ideal.mul_mem_mul hs (Ideal.sub_mem _
        (linearMap_apply_mem_of_mem_smul_top y hgx)
        (linearMap_apply_mem_of_mem_smul_top y hx))
      rwa [← pow_succ] at h1
    have heq : Φ (ρ g x) - Φ x = (f (ρ g x) - f x) + s * (y (ρ g x) - y x) := by
      rw [hΦapp, hΦapp]; ring
    rw [heq]
    exact Ideal.add_mem _ hfx hsy
  -- `Φ` is Galois-invariant modulo `𝔪ⁿ⁺²` on the residual sub-line: this
  -- is exactly what the ω-correction `hsA` says
  have hΦw : ∀ g : Γ ℚ,
      Φ (ρ g w₀) - Φ w₀ ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
    intro g
    have hya : y (ρ g w₀) - a g ∈ IsLocalRing.maximalIdeal R := by
      have h1 : y (ρ g w₀ - a g • w₀) ∈ IsLocalRing.maximalIdeal R :=
        linearMap_apply_mem_of_mem_smul_top y (ha g)
      rwa [map_sub, map_smul, hyw₀, smul_eq_mul, mul_one] at h1
    have h2 : s * (y (ρ g w₀) - a g) ∈ IsLocalRing.maximalIdeal R ^ (n + 2) := by
      have h3 := Ideal.mul_mem_mul hs hya
      rwa [← pow_succ] at h3
    have heq : Φ (ρ g w₀) - Φ w₀ =
        ((f (ρ g w₀) - f w₀) + (a g - 1) * s) + s * (y (ρ g w₀) - a g) := by
      rw [hΦapp, hΦapp, hyw₀]; ring
    rw [heq]
    exact Ideal.add_mem _ (hsA g) h2
  -- the connected counit idempotent of the Hopf order
  obtain ⟨e₀, he₀, hε₀, hmin₀, habs₀⟩ :=
    Bialgebra.exists_connected_counit_idempotent (A := 𝒪₃ᵥ) (G := G)
  -- the finite-flat leaf kills the `v₀`-defect of `Φ` on the inertia at `3`,
  -- with the connected–étale half discharged upstream
  have hmain := invariant_functional_defect_vanishes_of_hopf_package V hV hρ kk
    hsurj π hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne n Φ hΦm hΦw G fG hfG σ hσ
    e₀ he₀ hε₀ hmin₀ habs₀
    (fun m => inertia_displacement_apply_connected_idempotent_eq_one
      (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))) G e₀ he₀ hε₀
      fG hfG σ hσ m)
  rw [← hσ'] at hmain
  -- read the conclusion back in the `f`/`c` spelling
  have hyc : y (ρ σ' v₀) - (y v₀ + c σ') ∈ IsLocalRing.maximalIdeal R := by
    have h1 : y (ρ σ' v₀ - (v₀ + c σ' • w₀)) ∈ IsLocalRing.maximalIdeal R :=
      linearMap_apply_mem_of_mem_smul_top y (hc σ')
    rwa [map_sub, map_add, map_smul, hyw₀, smul_eq_mul, mul_one] at h1
  have h3 : s * (c σ' - (y (ρ σ' v₀) - y v₀)) ∈
      IsLocalRing.maximalIdeal R ^ (n + 2) := by
    have hmem : c σ' - (y (ρ σ' v₀) - y v₀) ∈ IsLocalRing.maximalIdeal R := by
      have hneg : c σ' - (y (ρ σ' v₀) - y v₀) =
          -(y (ρ σ' v₀) - (y v₀ + c σ')) := by ring
      rw [hneg]
      exact Submodule.neg_mem _ hyc
    have h4 := Ideal.mul_mem_mul hs hmem
    rwa [← pow_succ] at h4
  have heq2 : (f (ρ σ' v₀) - f v₀) + c σ' * s =
      (Φ (ρ σ' v₀) - Φ v₀) + s * (c σ' - (y (ρ σ' v₀) - y v₀)) := by
    rw [hΦapp, hΦapp]; ring
  rw [heq2]
  exact Ideal.add_mem _ hmain h3

set_option backward.isDefEq.respectTransparency false in
/-- **The flat-prolongation core of the trivial component at `3`**
(DECOMPOSED 2026-07-24 into the Hopf-package core
`trivial_component_vanishes_of_hopf_package` above — the
finite-flat/Fontaine content; the package-unpacking assembly is
PROVEN here): given the finite flat prolongation of
`ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` at `3` (hypothesis `hflat` — the
single-level consequence of `hρ.isFlat` at the open ideal `𝔪ⁿ⁺²`),
and the corrected trivial component
`T : g ↦ (f (ρ g v₀) - f v₀) + c g * s` — an honest homomorphism
modulo `𝔪ⁿ⁺²` (hypothesis `hThom`, PROVEN by the consumer from the
ω-correction `hsA` and the residual multiplicativity `hcmul`) with
values in `𝔪ⁿ⁺¹` — the value of `T` at the image of a local inertia
element at `3` lands in `𝔪ⁿ⁺²`. Assembly: unpack the
`GaloisRep.HasFlatProlongationAt` existential of `hflat` and hand
the explicit Hopf package to the core. -/
theorem flat_prolongation_trivial_component_vanishes
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
        IsLocalRing.maximalIdeal R ^ (n + 2))
    (hT1 : ∀ g : Γ ℚ, (f (ρ g v₀) - f v₀) + c g * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 1))
    (hThom : ∀ g h : Γ ℚ,
      ((f (ρ (g * h) v₀) - f v₀) + c (g * h) * s)
        - (((f (ρ g v₀) - f v₀) + c g * s)
          + ((f (ρ h v₀) - f v₀) + c h * s))
        ∈ IsLocalRing.maximalIdeal R ^ (n + 2))
    (hflat : (ρ.baseChange
        (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
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
  -- unpack the Hopf package and hand it to the core
  obtain ⟨G, i1, i2, i3, i4, i5, fG, hfG⟩ := hflat
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  exact trivial_component_vanishes_of_hopf_package V hV hρ kk hsurj π
    hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha c hc n f hf hfv₀ s hs hsA
    hT1 hThom G fG hfG σ hσ

/-- **The corrected trivial component dies on inertia at `3`** (DERIVED
2026-07-23 from the single-level flat-prolongation core — the flat
stratum; Fontaine): for `σ` in the local inertia at `3`, the corrected
trivial component `T : g ↦ (f (ρ g v₀) - f v₀) + c g * s` lands in
`𝔪ⁿ⁺²`. The glue derives the homomorphism property of `T` modulo
`𝔪ⁿ⁺²` (the twist term of the cocycle identity is cancelled by the
ω-correction `hsA` against the residual multiplicativity `hcmul`),
proves `𝔪ⁿ⁺²` is OPEN (`IsLocalRing.isOpen_maximalIdeal_pow` after
transporting compactness along a `ℤ₃`-basis), extracts the finite flat
prolongation of `ρ.baseChange (R ⧸ 𝔪ⁿ⁺²)` at `3` from `hρ.isFlat`,
and hands everything to the core. -/
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
  classical
  -- values of the corrected trivial component in `𝔪ⁿ⁺¹`
  have hT1 : ∀ g : Γ ℚ, (f (ρ g v₀) - f v₀) + c g * s ∈
      IsLocalRing.maximalIdeal R ^ (n + 1) := fun g =>
    Submodule.add_mem _ (hf g v₀) (Ideal.mul_mem_left _ _ hs)
  -- the corrected trivial component is a homomorphism modulo `𝔪ⁿ⁺²`
  have hThom : ∀ g h : Γ ℚ,
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
  -- `𝔪ⁿ⁺²` is open: transport compactness along a `ℤ₃`-basis
  haveI hNoeth : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[3] R
  let eR : R ≃ₗ[ℤ_[3]] (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    (Module.Free.chooseBasis ℤ_[3] R).equivFun
  have hcont₁ : Continuous eR :=
    IsModuleTopology.continuous_of_linearMap eR.toLinearMap
  have hcont₂ : Continuous eR.symm :=
    IsModuleTopology.continuous_of_linearMap eR.symm.toLinearMap
  let homR : R ≃ₜ (Module.Free.ChooseBasisIndex ℤ_[3] R → ℤ_[3]) :=
    { toEquiv := eR.toEquiv
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  haveI : CompactSpace R := homR.symm.compactSpace
  haveI : T2Space R := homR.symm.symm.isEmbedding.t2Space
  have hIopen : IsOpen
      ((IsLocalRing.maximalIdeal R ^ (n + 2) : Ideal R) : Set R) :=
    IsLocalRing.isOpen_maximalIdeal_pow R (n + 2)
  -- the finite flat prolongation at the congruence level `n + 2`
  have hflat : (ρ.baseChange
      (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 2)))).HasFlatProlongationAt
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat :=
    hρ.isFlat.cond (IsLocalRing.maximalIdeal R ^ (n + 2)) hIopen
  -- the single-level core closes the node
  exact flat_prolongation_trivial_component_vanishes V hV hρ kk hsurj π
    hπsurj hπequiv v₀ hv₀ w₀ hw₀π hw₀ne a ha c hc n f hf hfv₀ s hs hsA
    hT1 hThom hflat σ hσ

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
          (apply_mem_smul_top (ρ g⁻¹ : V →ₗ[R] V) (hg x)) }
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

/-- **The coboundary form of the one-level obstruction** (PROVEN; label
corrected 2026-07-25 —
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
    set N : Submodule R V := LinearMap.ker πR
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
  obtain ⟨b, hkerspan, _⟩ := hB
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
