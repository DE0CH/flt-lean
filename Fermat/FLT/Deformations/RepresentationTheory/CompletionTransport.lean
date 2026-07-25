/-
Deformations/RepresentationTheory/CompletionTransport.lean — own work for the
Fermat project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.DedekindDomain.AdicValuation
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Functoriality of adic completions, and transport of inertia and Frobenius

`GaloisRepTransport.lean` needs to compare the local Galois data (inertia
subgroups, arithmetic Frobenii) attached to a place `w` of `L` with the data
attached to a place `v` of `K` "below" it, along a ring hom `K →+* L` of number
fields. All of that rests on a single missing piece of functoriality: the
induced map of ADIC COMPLETIONS `K_v →+* L_w`, which this mathlib pin does not
have. This module builds it and derives the Galois consequences.

The construction is deliberately quantitative-free where it can be. The one
quantitative input is:

* `IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_le_one` — if the ideal
  of `v` pulls back from the ideal of `w`, then `w(ψ x) ≤ v(x)` for every `x` in
  the valuation ring of `v`. This uses only that an `x` with `v x ≤ 1` is a
  fraction `a/s` with `s ∉ v` (`exists_primeCompl_mul_eq_of_integer`) and a
  comparison of `intValuation`s read off from
  `intValuation_le_pow_iff_mem`. In particular NO ramification index and no
  factorisation-counting argument is needed — which is what the reference
  project `~/cs/FLT` uses for the same purpose (`intValuation_comap`,
  `valuation_comap`, `adicValued.continuous_algebraMap`), and what this module
  deliberately avoids.

From that:

* `WithVal.uniformContinuous_map_of_le` — such a `ψ` is uniformly continuous for
  the two valuation topologies (using that a `HeightOneSpectrum` valuation is
  surjective onto `ℤᵐ⁰`, so that arbitrarily small basis elements exist);
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionMap` — hence extends to
  `K_v →+* L_w`, compatibly with `K → K_v` and `L → L_w`;
* `…adicCompletionMap_mem_integers` — and is LOCAL: it maps `𝒪_v` into `𝒪_w`,
  because `𝒪_v` is the closure of `A` in `K_v`
  (`closureAlgebraMapIntegers_eq_integers`);
* `Field.absoluteGaloisGroup.map_mem_localInertiaGroup` — so the induced map
  `Γ L_w → Γ K_v` carries inertia at `w` into inertia at `v`;
* `Field.absoluteGaloisGroup.isArithFrobAt_map` — and carries an arithmetic
  Frobenius at `w` to an arithmetic Frobenius at `v`, PROVIDED the two residue
  cardinalities agree (`natCard_under_maximalIdeal` computes each of them as the
  residue cardinality of the place downstairs).

The mechanism behind the last two is one reflection principle: the integral
closure of `𝒪_v` in `K_vᵃˡᵍ` is a LOCAL ring, so an element whose image lies in
the maximal ideal upstairs is a non-unit, hence lies in the maximal ideal
downstairs (`Field.absoluteGaloisGroup.mem_maximalIdeal_of_icMap`).
-/

@[expose] public section

open IsDedekindDomain
open scoped NumberField WithZero

/-! ### A comparison principle in `ℤᵐ⁰` -/

/-- **Reading off an inequality in `ℤᵐ⁰` from the ideal filtration** (PROVEN):
an element `x ≤ 1` of `ℤᵐ⁰` is determined by the set of `n : ℕ` with
`x ≤ exp (-n)`, so a `y` satisfying all the constraints that `x` does satisfies
`y ≤ x`. This is what converts the ideal-theoretic statement
`a ∈ v ^ n → φ a ∈ w ^ n` into the valuation inequality
`w (φ a) ≤ v a`. -/
lemma WithZero.le_of_forall_exp_le {x y : ℤᵐ⁰} (hx : x ≤ 1)
    (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ)) → y ≤ WithZero.exp (-(n : ℤ))) : y ≤ x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne y 0 with rfl | hy0
    · exact le_rfl
    · exfalso
      lift y to ℤ using hy0 with m
      have hm := h ((-m).toNat + 1) zero_le
      rw [WithZero.exp_le_exp] at hm
      have h1 : -m ≤ ((-m).toNat : ℤ) := Int.self_le_toNat _
      push_cast at hm
      exact absurd h1 (by omega)
  · obtain ⟨k, hk⟩ := IsDedekindDomain.HeightOneSpectrum.exists_ofAdd_natCast_of_le_one hx0 hx
    have hxk : x = WithZero.exp (-(k : ℤ)) := hk.symm
    rw [hxk]
    exact h k (le_of_eq hxk)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Comparison of `intValuation`s along a ring hom -/

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]

omit [IsDedekindDomain A] [IsDedekindDomain B] in
/-- **Powers of the ideal are respected** (PROVEN): if `v` pulls back from `w`
along `φ`, then `φ` maps `v ^ n` into `w ^ n`. -/
lemma map_mem_asIdeal_pow (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (φ : A →+* B)
    (hmem : v.asIdeal ≤ Ideal.comap φ w.asIdeal) (n : ℕ) {a : A} (ha : a ∈ v.asIdeal ^ n) :
    φ a ∈ w.asIdeal ^ n := by
  have hle : v.asIdeal ^ n ≤ Ideal.comap φ (w.asIdeal ^ n) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr hmem) n
  exact hle ha

/-- **The `w`-adic valuation of `φ a` is at most the `v`-adic valuation of `a`**
(PROVEN), for `a` in the Dedekind domain and `v` pulled back from `w`. -/
lemma intValuation_map_le (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (φ : A →+* B)
    (hmem : v.asIdeal ≤ Ideal.comap φ w.asIdeal) (a : A) :
    w.intValuation (φ a) ≤ v.intValuation a := by
  refine WithZero.le_of_forall_exp_le (v.intValuation_le_one a) fun n hn => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem] at hn ⊢
  exact map_mem_asIdeal_pow v w φ hmem n hn

/-! ### Comparison of the valuations on the fraction fields -/

variable {K L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]

/-- **The valuation inequality on the fraction fields** (PROVEN): if the ideal of
`v` is the pullback of the ideal of `w` along `φ : A →+* B`, and `ψ : K →+* L`
extends `φ`, then `w (ψ x) ≤ v x` for every `x` in the valuation ring of `v`.

Proof: write `x = a / s` with `s ∉ v` (`exists_primeCompl_mul_eq_of_integer`).
Then `v x = v a` and, since `φ s ∉ w`, also `w (ψ x) = w (φ a)`; and
`w (φ a) ≤ v a` is `intValuation_map_le`. -/
lemma valuation_map_le_of_le_one (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (φ : A →+* B) (ψ : K →+* L)
    (hcomm : ∀ a : A, ψ (algebraMap A K a) = algebraMap B L (φ a))
    (hmem : v.asIdeal ≤ Ideal.comap φ w.asIdeal)
    (hcompl : ∀ s : A, s ∉ v.asIdeal → φ s ∉ w.asIdeal)
    (x : K) (hx : v.valuation K x ≤ 1) :
    w.valuation L (ψ x) ≤ v.valuation K x := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x hx
  have hd1 : v.valuation K (algebraMap A K (d : A)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_eq_one_iff_mem_primeCompl _).mpr d.2
  have hwd1 : w.valuation L (algebraMap B L (φ (d : A))) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (w.intValuation_eq_one_iff_mem_primeCompl _).mpr (hcompl _ d.2)
  have hvx : v.valuation K x = v.intValuation n := by
    have h := congrArg (v.valuation K) hnd
    rwa [map_mul, hd1, mul_one, HeightOneSpectrum.valuation_of_algebraMap] at h
  have hwx : w.valuation L (ψ x) = w.intValuation (φ n) := by
    have h := congrArg (fun y => w.valuation L (ψ y)) hnd
    simp only [map_mul, hcomm] at h
    rwa [hwd1, mul_one, HeightOneSpectrum.valuation_of_algebraMap] at h
  rw [hvx, hwx]
  exact intValuation_map_le v w φ hmem n

end IsDedekindDomain.HeightOneSpectrum

/-! ### Uniform continuity of a valuation-decreasing ring hom -/

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ in
/-- **A valuation-decreasing ring hom is uniformly continuous** (PROVEN) between
the valuation-topology type synonyms, provided the source valuation is
surjective onto `ℤᵐ⁰` (which a `HeightOneSpectrum` valuation is,
`valuation_surjective`).

Given a basis element `γ` downstream, take `t := min (embedding γ) 1` — nonzero,
`≤ 1`, and `≤ embedding γ` — and pull it back to some `x₀` with `v x₀ = t` by
surjectivity. Then `v x < t ≤ 1` forces `w (ψ x) ≤ v x < t ≤ embedding γ`. -/
lemma WithVal.uniformContinuous_map_of_le {K L : Type*} [Field K] [Field L]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰) (hv : Function.Surjective v)
    (ψ : K →+* L) (hψ : ∀ x : K, v x ≤ 1 → w (ψ x) ≤ v x) :
    UniformContinuous (WithVal.map v w ψ) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero (WithVal v) ℤᵐ⁰).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal w) ℤᵐ⁰)).mpr ?_
  rintro γ -
  have hc0 : embedding γ.1 ≠ 0 := embedding_unit_ne_zero γ
  have ht0 : min (embedding γ.1) 1 ≠ 0 := by
    rcases min_cases (embedding γ.1) (1 : ℤᵐ⁰) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp [hc0]
  obtain ⟨x₀, hx₀⟩ := hv (min (embedding γ.1) 1)
  have hval₀ : Valued.v (WithVal.toVal v x₀) = min (embedding γ.1) 1 := by
    rw [WithVal.valued_toVal]; exact hx₀
  have hδ0 : Valued.v.restrict (WithVal.toVal v x₀) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hval₀]; exact ht0
  refine ⟨Units.mk0 _ hδ0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hval₀] at hx
  have h2 : Valued.v x ≤ 1 := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
  have hxv : Valued.v x = v x.ofVal := (WithVal.apply_ofVal (v := v) x).symm
  have hgoal : Valued.v (WithVal.map v w ψ x) = w (ψ x.ofVal) := rfl
  rw [hgoal]
  calc w (ψ x.ofVal) ≤ v x.ofVal := hψ _ (hxv ▸ h2)
    _ = Valued.v x := hxv.symm
    _ < min (embedding γ.1) 1 := hx
    _ ≤ embedding γ.1 := min_le_left _ _

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### The induced map of adic completions -/

section Completion

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
variable {K L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
variable (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (ψ : K →+* L)
  (hψ : UniformContinuous (WithVal.map (v.valuation K) (w.valuation L) ψ))

/-- **The map of adic completions** induced by a uniformly continuous ring hom of
the fraction fields: complete `ψ` and transport across the wrapper
`adicCompletion.equiv`. -/
noncomputable def adicCompletionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (WithVal.map (v.valuation K) (w.valuation L) ψ)
      hψ.continuous).comp (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom)

/-- **The square `K → K_v → L_w` versus `K → L → L_w` commutes** (PROVEN). -/
lemma adicCompletionMap_coe (x : K) :
    adicCompletionMap v w ψ hψ (algebraMap K (v.adicCompletion K) x)
      = algebraMap L (w.adicCompletion L) (ψ x) := by
  have h1 : (HeightOneSpectrum.adicCompletion.equiv K v) (algebraMap K (v.adicCompletion K) x)
      = ((WithVal.toVal (v.valuation K) x : WithVal (v.valuation K)) :
          (v.valuation K).Completion) := rfl
  simp only [adicCompletionMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, UniformSpace.Completion.mapRingHom_coe hψ.continuous]
  rfl

lemma adicCompletionMap_continuous : Continuous (adicCompletionMap v w ψ hψ) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v))

/-- **The map of completions is LOCAL** (PROVEN): it maps `𝒪_v` into `𝒪_w`.
`𝒪_v` is the closure of the image of `A` (`closureAlgebraMapIntegers_eq_integers`),
the map is continuous and sends that image into the image of `B`, and `𝒪_w` is
the closure of the latter. -/
lemma adicCompletionMap_mem_integers (φ : A →+* B)
    (hcomm : ∀ a : A, ψ (algebraMap A K a) = algebraMap B L (φ a))
    {x : v.adicCompletion K} (hx : x ∈ v.adicCompletionIntegers K) :
    adicCompletionMap v w ψ hψ x ∈ w.adicCompletionIntegers L := by
  have hx' : x ∈ closure (algebraMap A (v.adicCompletion K)).range := by
    rw [HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers]; exact hx
  have himg : (adicCompletionMap v w ψ hψ) ''
      (algebraMap A (v.adicCompletion K)).range ⊆
      (algebraMap B (w.adicCompletion L)).range := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨φ a, ?_⟩
    rw [IsScalarTower.algebraMap_apply A K (v.adicCompletion K) a,
      adicCompletionMap_coe, hcomm,
      ← IsScalarTower.algebraMap_apply B L (w.adicCompletion L)]
  have h1 := (image_closure_subset_closure_image
    (adicCompletionMap_continuous v w ψ hψ)) ⟨x, hx', rfl⟩
  have h2 := closure_mono himg h1
  rwa [HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers] at h2

end Completion

/-! ### The residue cardinality of the `IsArithFrobAt` specification -/

/-- **The exponent in `IsArithFrobAt` at `v` is the residue cardinality of `v`**
(PROVEN): the contraction to `𝒪_v` of the maximal ideal of the integral closure
of `𝒪_v` in `K_vᵃˡᵍ` is the maximal ideal of `𝒪_v` (it is maximal, by
integrality, and `𝒪_v` is local), whose residue field is `𝓞_K / v`
(`ResidueFieldEquivCompletionResidueField`). -/
lemma natCard_under_maximalIdeal {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (↥(v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))).under ↥(v.adicCompletionIntegers K))
      = Nat.card ((𝓞 K) ⧸ v.asIdeal) := by
  have hunder : (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K)))).under ↥(v.adicCompletionIntegers K)
      = IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K) :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under _ _)
  rw [hunder]
  exact (Nat.card_congr
    (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv).symm

end IsDedekindDomain.HeightOneSpectrum

/-! ### Finiteness of the places above a finite set of places -/

namespace IsDedekindDomain.HeightOneSpectrum

/-- **Only finitely many places of `L` lie above a finite set of places of `K`**
(PROVEN): for each `v` the places above it inject, through `asIdeal`, into
`Ideal.primesOver v.asIdeal (𝓞 L)`, which is finite; take the (finite) union
over `S`. This is the finiteness that the reference project `~/cs/FLT` obtains
from `tendsTo_comap_cofinite`. -/
lemma finite_setOf_under_mem {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) ∈ S}.Finite := by
  classical
  have key : ∀ v : HeightOneSpectrum (𝓞 K),
      {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_
      (fun x _ y _ h => HeightOneSpectrum.ext h)
    refine Set.Finite.subset (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)) ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  exact Set.Finite.subset (Set.Finite.biUnion S.finite_toSet (fun v _ => key v))
    (fun w hw => Set.mem_biUnion hw rfl)

end IsDedekindDomain.HeightOneSpectrum

/-! ### Transfer of inertia and Frobenius along a local ring hom of completions -/

namespace Field.absoluteGaloisGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable (φ : v.adicCompletion K →+* w.adicCompletion L)
variable (hφ : ∀ x ∈ v.adicCompletionIntegers K, φ x ∈ w.adicCompletionIntegers L)

include hφ in
/-- `φ` restricted to the rings of integers of the two completions. -/
noncomputable def intMap :
    ↥(v.adicCompletionIntegers K) →+* ↥(w.adicCompletionIntegers L) :=
  ((φ.comp (v.adicCompletionIntegers K).toSubring.subtype).codRestrict
    (w.adicCompletionIntegers L).toSubring (fun x => hφ x.1 x.2))

include hφ in
/-- **Integrality is preserved** (PROVEN): the chosen embedding of algebraic
closures over a LOCAL `φ` carries elements integral over `𝒪_v` to elements
integral over `𝒪_w`. -/
lemma isIntegral_algebraicClosureMap {x : AlgebraicClosure (v.adicCompletion K)}
    (hx : IsIntegral ↥(v.adicCompletionIntegers K) x) :
    IsIntegral ↥(w.adicCompletionIntegers L) (AlgebraicClosure.map φ x) := by
  refine IsIntegral.map_of_comp_eq (intMap v w φ hφ) (AlgebraicClosure.map φ) ?_ hx
  ext y
  show algebraMap ↥(w.adicCompletionIntegers L) (AlgebraicClosure (w.adicCompletion L))
      (intMap v w φ hφ y) =
    AlgebraicClosure.map φ
      (algebraMap ↥(v.adicCompletionIntegers K) (AlgebraicClosure (v.adicCompletion K)) y)
  rw [IsScalarTower.algebraMap_apply ↥(v.adicCompletionIntegers K) (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)),
    AlgebraicClosure.map_algebraMap,
    IsScalarTower.algebraMap_apply ↥(w.adicCompletionIntegers L) (w.adicCompletion L)
      (AlgebraicClosure (w.adicCompletion L))]
  rfl

include hφ in
/-- The induced ring hom of the integral closures in the algebraic closures. -/
noncomputable def icMap :
    IntegralClosure ↥(v.adicCompletionIntegers K) (AlgebraicClosure (v.adicCompletion K)) →+*
      IntegralClosure ↥(w.adicCompletionIntegers L)
        (AlgebraicClosure (w.adicCompletion L)) where
  toFun x := ⟨AlgebraicClosure.map φ x.1, isIntegral_algebraicClosureMap v w φ hφ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

lemma icMap_coe (x : IntegralClosure ↥(v.adicCompletionIntegers K)
    (AlgebraicClosure (v.adicCompletion K))) :
    (icMap v w φ hφ x).1 = AlgebraicClosure.map φ x.1 := rfl

/-- **The reflection principle** (PROVEN): the integral closure of `𝒪_v` in
`K_vᵃˡᵍ` is a LOCAL ring, so an element whose image lies in the maximal ideal
upstairs is a non-unit, hence lies in the maximal ideal downstairs. This is the
one mechanism behind both the inertia and the Frobenius transfer. -/
lemma mem_maximalIdeal_of_icMap
    {z : IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))}
    (hz : icMap v w φ hφ z ∈ IsLocalRing.maximalIdeal
      (IntegralClosure ↥(w.adicCompletionIntegers L)
        (AlgebraicClosure (w.adicCompletion L)))) :
    z ∈ IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))) := by
  rw [IsLocalRing.mem_maximalIdeal] at hz ⊢
  exact fun hu => hz (hu.map (icMap v w φ hφ))

/-- **Equivariance** (PROVEN): `icMap` intertwines the action of `σ ∈ Γ L_w`
upstairs with that of `Field.absoluteGaloisGroup.map φ σ ∈ Γ K_v` downstairs.
This is exactly `Field.absoluteGaloisGroup.lift_map`, read on integral
closures. -/
lemma icMap_smul (σ : Field.absoluteGaloisGroup (w.adicCompletion L))
    (z : IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))) :
    icMap v w φ hφ (Field.absoluteGaloisGroup.map φ σ • z) = σ • icMap v w φ hφ z := by
  apply Subtype.ext
  rw [icMap_coe, IntegralClosure.coe_smul, IntegralClosure.coe_smul, icMap_coe]
  exact Field.absoluteGaloisGroup.lift_map φ σ z.1

include hφ in
/-- **Inertia goes down** (PROVEN): if `φ : K_v →+* L_w` is local, the induced
map `Γ L_w → Γ K_v` carries `localInertiaGroup w` into `localInertiaGroup v`. -/
lemma map_mem_localInertiaGroup (ι : Field.absoluteGaloisGroup (w.adicCompletion L))
    (hι : ι ∈ localInertiaGroup w) :
    Field.absoluteGaloisGroup.map φ ι ∈ localInertiaGroup v := by
  intro z
  refine mem_maximalIdeal_of_icMap v w φ hφ ?_
  rw [map_sub, icMap_smul]
  exact hι (icMap v w φ hφ z)

include hφ in
/-- **Arithmetic Frobenius goes down** (PROVEN): if `φ : K_v →+* L_w` is local
and the two residue cardinalities agree, then the image in `Γ K_v` of the
arithmetic Frobenius at `w` is an arithmetic Frobenius at `v`. -/
lemma isArithFrobAt_map
    (hq : Nat.card (↥(v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))).under ↥(v.adicCompletionIntegers K)) =
      Nat.card (↥(w.adicCompletionIntegers L) ⧸
        (IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers L)
          (AlgebraicClosure (w.adicCompletion L)))).under ↥(w.adicCompletionIntegers L))) :
    IsArithFrobAt ↥(v.adicCompletionIntegers K)
      (Field.absoluteGaloisGroup.map φ (Field.AbsoluteGaloisGroup.adicArithFrob w))
      (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
        (AlgebraicClosure (v.adicCompletion K)))) := by
  intro z
  refine mem_maximalIdeal_of_icMap v w φ hφ ?_
  have key : icMap v w φ hφ
      (Field.absoluteGaloisGroup.map φ (Field.AbsoluteGaloisGroup.adicArithFrob w) • z -
        z ^ Nat.card (↥(v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
            (AlgebraicClosure (v.adicCompletion K)))).under ↥(v.adicCompletionIntegers K))) ∈
      IsLocalRing.maximalIdeal (IntegralClosure ↥(w.adicCompletionIntegers L)
        (AlgebraicClosure (w.adicCompletion L))) := by
    rw [map_sub, map_pow, icMap_smul, hq]
    exact Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob w (icMap v w φ hφ z)
  exact key

end Field.absoluteGaloisGroup

/-! ### The local inertia group is normal -/

namespace Field.absoluteGaloisGroup

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- **The maximal ideal is Galois-stable** (PROVEN): the Galois group acts by
ring automorphisms of the (local) integral closure, and a ring automorphism
preserves non-units. -/
lemma smul_mem_maximalIdeal (σ : Field.absoluteGaloisGroup (v.adicCompletion K))
    {z : IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))}
    (hz : z ∈ IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K)))) :
    σ • z ∈ IsLocalRing.maximalIdeal (IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))) := by
  rw [IsLocalRing.mem_maximalIdeal] at hz ⊢
  intro hu
  refine hz ?_
  have h1 := hu.map (MulSemiringAction.toRingHom
    (Field.absoluteGaloisGroup (v.adicCompletion K))
    (IntegralClosure ↥(v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))) σ⁻¹)
  simpa only [MulSemiringAction.toRingHom_apply, inv_smul_smul] using h1

/-- **`localInertiaGroup` is normal** (PROVEN): conjugation moves the defining
congruence by a Galois automorphism, and the maximal ideal is Galois-stable. -/
lemma conj_mem_localInertiaGroup (σ ι : Field.absoluteGaloisGroup (v.adicCompletion K))
    (hι : ι ∈ localInertiaGroup v) : σ * ι * σ⁻¹ ∈ localInertiaGroup v := by
  intro z
  have h1 : (σ * ι * σ⁻¹) • z - z = σ • (ι • (σ⁻¹ • z) - σ⁻¹ • z) := by
    rw [smul_sub, smul_smul, smul_smul, smul_inv_smul]
  rw [h1]
  exact smul_mem_maximalIdeal v σ (hι (σ⁻¹ • z))

end Field.absoluteGaloisGroup

end
