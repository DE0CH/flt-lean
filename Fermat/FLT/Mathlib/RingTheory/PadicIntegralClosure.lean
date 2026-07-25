/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Algebra

/-!
# The `p`-adic ring-of-integers hull of a module-finite `ℤ_p`-algebra

Upstream layer shared by `Fermat/FLT/Modularity/Interface.lean` (the Ribet-cut
leaf `exists_padicIntegers_dvr_hull`) and
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean` (the concrete
coefficient-ring instance suite). Nothing here mentions Galois
representations: it is pure `p`-adic commutative algebra.

## Main results

* `isIntegral_padicInt_of_spectralNorm_le_one`: an element of an algebraic
  extension of `ℚ_p` of spectral norm at most `1` is integral over `ℤ_p`.
* `isScalarTower_padicInt_of_continuousSMul`: a topological presentation of a
  module-topology `ℤ_p`-algebra `R` inside `ℚ̄_p` automatically commutes with
  the canonical `ℤ_p → ℚ_p → ℚ̄_p`, because `ℕ` is dense in `ℤ_p`.
* `finiteDimensional_padic_fractionRing`: the fraction field of a
  module-finite `ℤ_p`-domain is a finite extension of `ℚ_p`.
* `exists_padicIntegers_dvr_hull_of_continuousSMul`: such an `R` maps to the
  ring of integers `O` of a finite extension of `ℚ_p`, compatibly with both
  structure maps; `O` is a module-finite local `ℤ_p`-algebra carrying the
  module topology and is a discrete valuation ring.
-/

@[expose] public section

universe u

/-- **Spectral-norm integrality over `ℤ_ℓ`** (PROVEN): an element of an
algebraic extension of `ℚ_ℓ` with spectral norm at most `1` is integral
over `ℤ_ℓ` — its monic minimal polynomial over `ℚ_ℓ` has coefficients
of norm at most `1`, which lift termwise to `ℤ_ℓ`. (The `ℤ_ℓ`-avatar of
`isIntegral_of_spectralNorm_le_one` in `AbsoluteGaloisGroup.lean`,
which is stated for the `Valued.v.integer` subring of an abstractly
valued base field and so does not directly apply to `ℤ_[ℓ]`.) -/
lemma isIntegral_padicInt_of_spectralNorm_le_one {ℓ : ℕ} [Fact ℓ.Prime]
    {M : Type*} [Field M] [Algebra ℚ_[ℓ] M] [Algebra.IsAlgebraic ℚ_[ℓ] M]
    [Algebra ℤ_[ℓ] M] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] M]
    {x : M} (hx : spectralNorm ℚ_[ℓ] M x ≤ 1) : IsIntegral ℤ_[ℓ] x := by
  have hlift : minpoly ℚ_[ℓ] x ∈ Polynomial.lifts (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i => ?_
    have hterm := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at hterm
    split_ifs at hterm with h
    · conv_rhs at hterm =>
        rw [← Real.one_rpow (1 / ((minpoly ℚ_[ℓ] x).natDegree - i : ℝ))]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at hterm
      exact ⟨⟨(minpoly ℚ_[ℓ] x).coeff i, hterm⟩, rfl⟩
    · obtain h | h := (le_of_not_gt h).eq_or_lt
      · refine ⟨1, ?_⟩
        rw [map_one, ← h]
        exact ((minpoly.monic
          (Algebra.IsAlgebraic.isAlgebraic x).isIntegral).coeff_natDegree).symm
      · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt h]⟩
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[ℓ], hP, minpoly.aeval]

/-- The canonical structure map `ℤ_ℓ → ℚ̄_ℓ` is continuous (PROVEN glue:
it factors as `ℤ_ℓ ⊆ ℚ_ℓ → ℚ̄_ℓ`, and `ℚ̄_ℓ` is a normed `ℚ_ℓ`-algebra). -/
theorem continuous_algebraMap_padicInt_algebraicClosure {ℓ : ℕ} [Fact ℓ.Prime] :
    Continuous (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])]
  exact (continuous_algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp continuous_subtype_val

/-- `ℚ̄_ℓ` is a topological `ℤ_ℓ`-module (PROVEN glue). Deliberately NOT an
`instance`: this module is imported by the 18k-line `Modularity/Interface.lean`
and everything downstream of it, and a new global instance there is a
gratuitous perturbation of instance resolution. The one consumer below
introduces it with `haveI`. -/
theorem continuousSMul_padicInt_algebraicClosure {ℓ : ℕ} [Fact ℓ.Prime] :
    ContinuousSMul ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
  continuousSMul_of_algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])
    continuous_algebraMap_padicInt_algebraicClosure

/-- The canonical structure map `ℤ_ℓ → ℚ̄_ℓ` is injective (PROVEN glue). -/
theorem algebraMap_padicInt_algebraicClosure_injective {ℓ : ℕ} [Fact ℓ.Prime] :
    Function.Injective (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ])) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])]
  exact (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).injective.comp
    (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])

/-- **The scalar tower comes free from continuity** (PROVEN): a `ℤ_ℓ`-algebra
`R` carrying the `ℤ_ℓ`-module topology and presented as a *topological*
`ℚ̄_ℓ`-algebra has its two structure maps `ℤ_ℓ → R → ℚ̄_ℓ` and
`ℤ_ℓ → ℚ_ℓ → ℚ̄_ℓ` equal: both are continuous ring maps out of `ℤ_ℓ`, they
agree on the image of `ℕ` (any ring map does), and that image is dense
(`PadicInt.denseRange_natCast`) in the Hausdorff target. -/
theorem isScalarTower_padicInt_of_continuousSMul {ℓ : ℕ} [Fact ℓ.Prime]
    {R : Type*} [CommRing R] [Algebra ℤ_[ℓ] R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsModuleTopology ℤ_[ℓ] R]
    [Algebra R (AlgebraicClosure ℚ_[ℓ])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[ℓ])] :
    IsScalarTower ℤ_[ℓ] R (AlgebraicClosure ℚ_[ℓ]) := by
  have hZR : Continuous (algebraMap ℤ_[ℓ] R) := continuous_algebraMap ℤ_[ℓ] R
  have hRQ : Continuous (algebraMap R (AlgebraicClosure ℚ_[ℓ])) :=
    continuous_algebraMap R (AlgebraicClosure ℚ_[ℓ])
  have hagree : Set.EqOn
      (fun z : ℤ_[ℓ] => algebraMap R (AlgebraicClosure ℚ_[ℓ]) (algebraMap ℤ_[ℓ] R z))
      (algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))
      (Set.range (Nat.cast : ℕ → ℤ_[ℓ])) := by
    rintro _ ⟨n, rfl⟩
    simp only [map_natCast]
  have hfun : (fun z : ℤ_[ℓ] => algebraMap R (AlgebraicClosure ℚ_[ℓ]) (algebraMap ℤ_[ℓ] R z))
      = algebraMap ℤ_[ℓ] (AlgebraicClosure ℚ_[ℓ]) :=
    Continuous.ext_on PadicInt.denseRange_natCast (hRQ.comp hZR)
      continuous_algebraMap_padicInt_algebraicClosure hagree
  exact IsScalarTower.of_algebraMap_eq fun z => (congrFun hfun z).symm

/-- **The fraction field of a module-finite `ℤ_p`-domain is a finite extension
of `ℚ_p`** (PROVEN): a finite `ℤ_p`-spanning set of `R` has, in `F`, a
`ℚ_p`-algebra span `A = ℚ_p[image of R]` which is finite over `ℚ_p`
(`Algebra.finite_adjoin_of_finite_of_isIntegral`, the generators being
integral) and a domain, hence a FIELD (`isField_of_isIntegral_of_isField'`);
every element of `F` is a ratio of elements of the image of `R`
(`IsFractionRing.div_surjective`), so `A` is all of `F`. -/
theorem finiteDimensional_padic_fractionRing {p : ℕ} [Fact p.Prime]
    {R : Type*} [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R]
    {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
    [Algebra ℤ_[p] F] [IsScalarTower ℤ_[p] R F]
    [Algebra ℚ_[p] F] [IsScalarTower ℤ_[p] ℚ_[p] F] :
    FiniteDimensional ℚ_[p] F := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[p]) (M := R)
  have hint : ∀ x ∈ algebraMap R F '' Set.range s, IsIntegral ℚ_[p] x := by
    rintro x ⟨r, -, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) r).map
      (IsScalarTower.toAlgHom ℤ_[p] R F)).tower_top
  set A : Subalgebra ℚ_[p] F := Algebra.adjoin ℚ_[p] (algebraMap R F '' Set.range s) with hA
  haveI hAfin : Module.Finite ℚ_[p] A :=
    hA ▸ Algebra.finite_adjoin_of_finite_of_isIntegral ((Set.finite_range s).image _) hint
  have hmemA : ∀ r : R, algebraMap R F r ∈ A := by
    intro r
    have hr : r ∈ Submodule.span ℤ_[p] (Set.range s) := by rw [hs]; trivial
    induction hr using Submodule.span_induction with
    | mem x hx => exact hA ▸ Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
    | smul c x _ hx =>
        have hc : algebraMap R F (c • x)
            = algebraMap ℚ_[p] F (algebraMap ℤ_[p] ℚ_[p] c) * algebraMap R F x := by
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] R F,
            IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] F]
        rw [hc]
        exact mul_mem (A.algebraMap_mem _) hx
  have hAfield : IsField A := isField_of_isIntegral_of_isField' (Field.toIsField ℚ_[p])
  have hall : ∀ x : F, x ∈ A := by
    intro x
    obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) (K := F) x
    have hbne : algebraMap R F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    obtain ⟨y, hy⟩ := hAfield.mul_inv_cancel
      (a := (⟨algebraMap R F b, hmemA b⟩ : A)) (by simpa [Subtype.ext_iff] using hbne)
    have hcoe : algebraMap R F b * (y : F) = 1 := by
      simpa using congrArg (fun z : A => (z : F)) hy
    rw [← hx, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hcoe]
    exact mul_mem (hmemA a) y.2
  exact Module.Finite.of_surjective A.val.toLinearMap fun x => ⟨⟨x, hall x⟩, rfl⟩

/-- **The `p`-adic ring-of-integers hull, injective case** (PROVEN): a
module-finite `ℤ_p`-domain `R` embedded in `ℚ̄_p` over `ℤ_p` sits inside the
ring of integers `O` of a finite extension of `ℚ_p`.

`O` is `integralClosure ℤ_p (Frac R)` — deliberately the integral closure in
the ABSTRACT fraction field, which lives in the same universe as `R`, rather
than in an intermediate field of `ℚ̄_p/ℚ_p`; that also lets `O` carry the
`ℤ_p`-module topology by fiat, so no compactness argument is needed. `O` is
module-finite over `ℤ_p` by `IsIntegralClosure.finite`, a valuation ring by
the spectral-norm dichotomy transported along the embedding (hence LOCAL for
free), and a discrete valuation ring by
`IsDiscreteValuationRing.TFAE … .out 1 0`, `O` being Noetherian, local, a
domain and not a field (a field would force `ℤ_p` to be one). -/
theorem exists_padicIntegers_dvr_hull_of_injective {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R]
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p])]
    (hinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p]))) :
    ∃ (O : Type u) (_ : CommRing O) (_ : Algebra ℤ_[p] O)
      (_ : IsDomain O) (_ : Module.Finite ℤ_[p] O)
      (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
      (_ : IsLocalRing O) (_ : IsModuleTopology ℤ_[p] O)
      (_ : IsDiscreteValuationRing O)
      (_ : Algebra O (AlgebraicClosure ℚ_[p]))
      (_ : ContinuousSMul O (AlgebraicClosure ℚ_[p]))
      (ι : R →+* O),
      Function.Injective (algebraMap O (AlgebraicClosure ℚ_[p])) ∧
      (∀ x : ℤ_[p], ι (algebraMap ℤ_[p] R x) = algebraMap ℤ_[p] O x) ∧
      (∀ r : R, algebraMap O (AlgebraicClosure ℚ_[p]) (ι r) =
        algebraMap R (AlgebraicClosure ℚ_[p]) r) := by
  classical
  haveI hCSZQ : ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
    continuousSMul_padicInt_algebraicClosure
  -- Step 1: the fraction field `F = Frac R`, as a `ℤ_p`- and `ℚ_p`-algebra.
  have hRFinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hZRinj : Function.Injective (algebraMap ℤ_[p] R) := by
    intro a b hab
    refine algebraMap_padicInt_algebraicClosure_injective (ℓ := p) ?_
    rw [IsScalarTower.algebraMap_apply ℤ_[p] R (AlgebraicClosure ℚ_[p]),
      IsScalarTower.algebraMap_apply ℤ_[p] R (AlgebraicClosure ℚ_[p]), hab]
  have hZFinj : Function.Injective (algebraMap ℤ_[p] (FractionRing R)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] R (FractionRing R)]
    exact hRFinj.comp hZRinj
  letI algQF : Algebra ℚ_[p] (FractionRing R) :=
    (IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) hZFinj).toAlgebra
  haveI twZQF : IsScalarTower ℤ_[p] ℚ_[p] (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun z => (IsFractionRing.lift_algebraMap hZFinj z).symm
  haveI hFDF : FiniteDimensional ℚ_[p] (FractionRing R) :=
    finiteDimensional_padic_fractionRing (R := R) (F := FractionRing R)
  -- Step 2: the embedding `Φ : F → ℚ̄_p`, a `ℤ_p`-algebra map.
  have hφZ : ∀ z : ℤ_[p],
      IsFractionRing.lift (A := R) (K := FractionRing R) hinj
          (algebraMap ℤ_[p] (FractionRing R) z)
        = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) z := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℤ_[p] R (FractionRing R) z,
      IsFractionRing.lift_algebraMap hinj,
      ← IsScalarTower.algebraMap_apply ℤ_[p] R (AlgebraicClosure ℚ_[p])]
  let Φ : FractionRing R →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] :=
    { toRingHom := IsFractionRing.lift (A := R) (K := FractionRing R) hinj
      commutes' := hφZ }
  have hΦR : ∀ r : R, Φ (algebraMap R (FractionRing R) r)
      = algebraMap R (AlgebraicClosure ℚ_[p]) r := IsFractionRing.lift_algebraMap hinj
  have hΦinj : Function.Injective Φ :=
    (Φ : FractionRing R →+* AlgebraicClosure ℚ_[p]).injective
  -- Step 3: `O`, the integral closure of `ℤ_p` in `F`.
  haveI hMFO : Module.Finite ℤ_[p] ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] (FractionRing R) _
  haveI hNO : IsNoetherianRing ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] (FractionRing R) _
  letI topO : TopologicalSpace ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    moduleTopology ℤ_[p] _
  haveI hMTO : IsModuleTopology ℤ_[p] ↥(integralClosure ℤ_[p] (FractionRing R)) := ⟨rfl⟩
  haveI hTRO : IsTopologicalRing ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    IsModuleTopology.isTopologicalRing ℤ_[p] _
  -- Step 4: the spectral-norm dichotomy makes `O` a valuation ring, hence local.
  haveI hVRO : ValuationRing ↥(integralClosure ℤ_[p] (FractionRing R)) := by
    refine ValuationSubring.instValuationRingSubtypeMem
      ⟨(integralClosure ℤ_[p] (FractionRing R)).toSubring, ?_⟩
    intro x
    rcases le_total ‖Φ x‖ 1 with h | h
    · exact Or.inl ((isIntegral_algHom_iff Φ hΦinj).mp
        (isIntegral_padicInt_of_spectralNorm_le_one (by simpa using h)))
    · refine Or.inr ((isIntegral_algHom_iff Φ hΦinj).mp
        (isIntegral_padicInt_of_spectralNorm_le_one ?_))
      have hinv : ‖Φ x⁻¹‖ ≤ 1 := by
        rw [map_inv₀, norm_inv]
        exact inv_le_one_of_one_le₀ h
      simpa using hinv
  haveI hLocO : IsLocalRing ↥(integralClosure ℤ_[p] (FractionRing R)) := inferInstance
  -- Step 5: `O` is not a field, so the TFAE upgrades it to a DVR.
  have hZOinj : Function.Injective
      (algebraMap ℤ_[p] ↥(integralClosure ℤ_[p] (FractionRing R))) := by
    intro a b hab
    exact hZFinj (congrArg
      (Subtype.val (p := fun x => x ∈ integralClosure ℤ_[p] (FractionRing R))) hab)
  have hnf : ¬ IsField ↥(integralClosure ℤ_[p] (FractionRing R)) := fun hfield =>
    IsDiscreteValuationRing.not_isField ℤ_[p]
      (isField_of_isIntegral_of_isField hZOinj hfield)
  haveI hDVRO : IsDiscreteValuationRing ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 0).mp hVRO
  -- Step 6: the embedding of `O` into `ℚ̄_p`, continuous by module topology.
  letI algOQ : Algebra ↥(integralClosure ℤ_[p] (FractionRing R)) (AlgebraicClosure ℚ_[p]) :=
    ((Φ : FractionRing R →+* AlgebraicClosure ℚ_[p]).comp
      (algebraMap ↥(integralClosure ℤ_[p] (FractionRing R)) (FractionRing R))).toAlgebra
  haveI twZOQ : IsScalarTower ℤ_[p] ↥(integralClosure ℤ_[p] (FractionRing R))
      (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq fun z => (Φ.commutes z).symm
  have hcontOQ : Continuous (algebraMap ↥(integralClosure ℤ_[p] (FractionRing R))
      (AlgebraicClosure ℚ_[p])) :=
    IsModuleTopology.continuous_of_linearMap
      (IsScalarTower.toAlgHom ℤ_[p] ↥(integralClosure ℤ_[p] (FractionRing R))
        (AlgebraicClosure ℚ_[p])).toLinearMap
  haveI hCSOQ : ContinuousSMul ↥(integralClosure ℤ_[p] (FractionRing R))
      (AlgebraicClosure ℚ_[p]) := continuousSMul_of_algebraMap _ _ hcontOQ
  -- Step 7: `R` lands in `O`.
  have hintRF : ∀ r : R,
      algebraMap R (FractionRing R) r ∈ integralClosure ℤ_[p] (FractionRing R) :=
    fun r => (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) r).map
      (IsScalarTower.toAlgHom ℤ_[p] R (FractionRing R))
  let ιA : R →ₐ[ℤ_[p]] ↥(integralClosure ℤ_[p] (FractionRing R)) :=
    AlgHom.codRestrict (IsScalarTower.toAlgHom ℤ_[p] R (FractionRing R)) _ hintRF
  refine ⟨↥(integralClosure ℤ_[p] (FractionRing R)), inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    (ιA : R →+* ↥(integralClosure ℤ_[p] (FractionRing R))), ?_, ?_, ?_⟩
  · exact fun a b hab => Subtype.ext (hΦinj hab)
  · exact fun x => ιA.commutes x
  · exact fun r => hΦR r

/-- **The `p`-adic ring-of-integers hull** (PROVEN): a module-finite
`ℤ_p`-algebra `R` carrying the `ℤ_p`-module topology and presented as a
topological `ℚ̄_p`-algebra maps to the ring of integers `O` of a finite
extension of `ℚ_p`, compatibly with both structure maps.

No injectivity or scalar-tower hypothesis is needed: continuity plus the
density of `ℕ` in `ℤ_p` forces the tower
(`isScalarTower_padicInt_of_continuousSMul`), and dividing by the kernel of
`R → ℚ̄_p` — a prime ideal, missing `ℤ_p` because `ℤ_p → ℚ̄_p` is injective —
reduces to `exists_padicIntegers_dvr_hull_of_injective`. -/
theorem exists_padicIntegers_dvr_hull_of_continuousSMul {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])] :
    ∃ (O : Type u) (_ : CommRing O) (_ : Algebra ℤ_[p] O)
      (_ : IsDomain O) (_ : Module.Finite ℤ_[p] O)
      (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
      (_ : IsLocalRing O) (_ : IsModuleTopology ℤ_[p] O)
      (_ : IsDiscreteValuationRing O)
      (_ : Algebra O (AlgebraicClosure ℚ_[p]))
      (_ : ContinuousSMul O (AlgebraicClosure ℚ_[p]))
      (ι : R →+* O),
      Function.Injective (algebraMap O (AlgebraicClosure ℚ_[p])) ∧
      (∀ x : ℤ_[p], ι (algebraMap ℤ_[p] R x) = algebraMap ℤ_[p] O x) ∧
      (∀ r : R, algebraMap O (AlgebraicClosure ℚ_[p]) (ι r) =
        algebraMap R (AlgebraicClosure ℚ_[p]) r) := by
  classical
  haveI htw : IsScalarTower ℤ_[p] R (AlgebraicClosure ℚ_[p]) :=
    isScalarTower_padicInt_of_continuousSMul
  haveI hker : (RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p]))).IsPrime :=
    RingHom.ker_isPrime _
  haveI hMFQ : Module.Finite ℤ_[p]
      (R ⧸ RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p]))) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ ℤ_[p]
        (RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p])))).toLinearMap
      Ideal.Quotient.mk_surjective
  letI algQuot : Algebra (R ⧸ RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p])))
      (AlgebraicClosure ℚ_[p]) :=
    (RingHom.kerLift (algebraMap R (AlgebraicClosure ℚ_[p]))).toAlgebra
  haveI twQuot : IsScalarTower ℤ_[p]
      (R ⧸ RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p])))
      (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] R (AlgebraicClosure ℚ_[p]) z]
      exact (RingHom.kerLift_mk _ (algebraMap ℤ_[p] R z)).symm
  obtain ⟨O, hCR, hAlg, hDom, hMF, hTop, hTR, hLoc, hMT, hDVR, hAQ, hCS, ι, h1, h2, h3⟩ :=
    exists_padicIntegers_dvr_hull_of_injective
      (R := R ⧸ RingHom.ker (algebraMap R (AlgebraicClosure ℚ_[p])))
      (RingHom.kerLift_injective (algebraMap R (AlgebraicClosure ℚ_[p])))
  refine ⟨O, hCR, hAlg, hDom, hMF, hTop, hTR, hLoc, hMT, hDVR, hAQ, hCS,
    ι.comp (Ideal.Quotient.mk _), h1, ?_, ?_⟩
  · exact fun x => h2 x
  · intro r
    rw [RingHom.comp_apply, h3 (Ideal.Quotient.mk _ r)]
    exact RingHom.kerLift_mk _ r
