/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

-- the inertia dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup`
-- (the `MazurTorsion` bridge from a `Subgroup.map … ≤ fixingSubgroup`
-- inclusion to unramifiedness of every prime above `q`), together with
-- `localInertiaGroup` and `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`.
public import Fermat.FLT.FreyCurve.MazurTorsion
-- proof-only: `discreteTopology_moduleTopology`, used to see the finite
-- endomorphism monoid `End_A(A²)` as a discrete topological space so that
-- the kernel of a continuous representation is open.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `IsHardlyRamified`, `rank_finTwoFun`, `GaloisRep.IsUnramifiedAt`.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- `IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd`,
-- the tame-plus-wild assembly turning a uniform per-prime different-exponent
-- bound into a bound on the discriminant exponent. This is the ONE project
-- dependency of the different-ideal development below.
-- REPOINTED 2026-07-28 (release-15 integration): this was
-- `public import …HardlyRamified.ModThree`, for exactly two names —
-- `discr_factorization_le_of_forall_differentIdeal_pow_dvd` and
-- `not_pow_ramificationIdx_dvd_differentIdeal`.  Both now live in the
-- Mathlib-only shim below, so the 66 000-line `ModThree` (~680 s of
-- single-threaded elaboration, the most expensive module in the tree) is no
-- longer on this module's critical path.  The old CIRCULARITY GUARD note is
-- moot and stronger than it needs to be: this shim's import cone is `Mathlib`
-- only, so no project cycle is expressible through it.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.DifferentIdeal
-- Serre's wild different bound and the discriminant-exponent bound
-- `exists_discr_factorization_le_of_finrank_le`, HOISTED out of this file on
-- 2026-07-28 into a strict `Mathlib`-cone module so that
-- `Fermat/FLT/ModularCurve/X0.lean` — which is UPSTREAM of this file, through
-- `FreyCurve/MazurTorsion` — can consume it in the weak Mordell-Weil chain.
-- Same namespace `GaloisRepresentation`, so every reference below is
-- unqualified and unchanged.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.DiscrExponent
-- Hermite's theorem `NumberField.finite_of_discr_bdd`.
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
-- `NumberField.not_dvd_discr_iff_forall_mem`.
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- the infinite Galois correspondence: `InfiniteGalois.fixingSubgroup_fixedField`,
-- `InfiniteGalois.isOpen_iff_finite`, `InfiniteGalois.normal_iff_isGalois`,
-- `InfiniteGalois.normalAutEquivQuotient`.
public import Mathlib.FieldTheory.Galois.Infinite
-- `Subgroup.isClosed_of_isOpen`.
public import Mathlib.Topology.Algebra.OpenSubgroup
-- `Subgroup.index_eq_card`, `Subgroup.finite_quotient_of_finiteIndex`,
-- `Subgroup.finiteIndex_of_finite_quotient`.
public import Mathlib.GroupTheory.Index
-- `Nat.prod_factorization_pow_eq_self`, `Nat.support_factorization`.
public import Mathlib.Data.Nat.Factorization.Defs
-- `IsDedekindDomain.HeightOneSpectrum.intValuation` and its `WithZero.exp`-valued
-- API, the `Q`-adic order used in the wild different-exponent bound
-- `differentIdeal_exponent_le_wild`.
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- `Ideal.ramificationIdx_le_finrank`, consumed by
-- `exists_discr_factorization_le_of_finrank_le`. Explicit and PUBLIC because as
-- of 2026-07-26 it no longer arrives transitively as a public name: the module
-- system re-exports only public imports.
public import Mathlib.NumberTheory.RamificationInertia.Basic
-- `IsLocalRing.maximalIdeal`, `IsLocalRing.ResidueField`,
-- `IsLocalRing.map_maximalIdeal_of_surjective`, `IsLocalRing.local_hom_TFAE` —
-- reaching this cone only through private imports otherwise, which reads as
-- `Unknown identifier maximalIdeal`.
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
-- The four inputs to `trace_quotient_pow_eq_of_mem_cofactor` below (the trace
-- bookkeeping of Serre's wild different bound).  All PUBLIC: the names are used
-- in proof bodies, and a private import would make them unavailable there when
-- the privacy sits in an intermediate module.
-- `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, the algebra isomorphism
-- `B ⧸ I·B ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B` that carries the base change of the trace.
public import Mathlib.RingTheory.TensorProduct.Quotient
-- `Algebra.TensorProduct.instFree`: `A ⊗[R] M` is free over `A` when `M` is free
-- over `R`.  This is what makes `𝓞_K ⧸ q^k𝓞_K` free over `ℤ/q^k`.
public import Mathlib.RingTheory.TensorProduct.Free
-- `LinearMap.trace_baseChange`.
public import Mathlib.LinearAlgebra.Trace
-- `Module.free_of_flat_of_isLocalRing`: over the local ring `ℤ/q^k`, the direct
-- summands `𝓞_K ⧸ Q^{e·k}` and `𝓞_K ⧸ J` of a free module are themselves free.
public import Mathlib.RingTheory.LocalRing.Module
-- `Module.Projective.of_split`, for those two summands.
public import Mathlib.Algebra.Module.Projective
-- `Algebra.trace_eq_of_algEquiv`, `Algebra.trace_apply`, `Algebra.trace_prod_apply`,
-- `Algebra.trace_surjective`.
public import Mathlib.RingTheory.Trace.Basic
-- The five inputs to the finite-local-ring core of the trace witness
-- (`exists_subalgebra_free_finrank_eq_residualTrace_surjective` below).  All PUBLIC:
-- the names are used in proof bodies, and a private import would make them unavailable
-- there when the privacy sits in an intermediate module.
-- `HenselianRing`, `IsAdicComplete.henselianRing` — the Newton iteration that lifts a
-- residue-field generator through the nilpotent maximal ideal.
public import Mathlib.RingTheory.Henselian
-- `Field.exists_primitive_element`, `IntermediateField.adjoin.finrank`,
-- `IntermediateField.finrank_top'`,
-- `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic`.
public import Mathlib.FieldTheory.PrimitiveElement
-- `PerfectField.ofFinite` and the `Algebra.IsSeparable` instance over a perfect base:
-- this is what makes the residue extension of finite fields separable.
public import Mathlib.FieldTheory.Perfect
-- `Polynomial.lifts_and_degree_eq_and_monic`, `Polynomial.lifts_iff_coeff_lifts` —
-- the monic lift of the minimal polynomial along `Z ↠ κ_Z`.
public import Mathlib.Algebra.Polynomial.Lifts
-- `PowerBasis.mem_span_pow'`, the division-by-a-monic membership criterion behind
-- `adjoin_singleton_le_span_pow`.
public import Mathlib.RingTheory.PowerBasis

/-!
# Hermite–Minkowski finiteness for hardly ramified representations

This module isolates the **restricted-ramification finiteness** statement

  `finite_setOf_isHardlyRamified` :
    over a finite discrete local coefficient ring `A` there are only
    finitely many hardly ramified representations of `Γ ℚ` on `A²`,

together with the Hermite–Minkowski chain that proves it:

* `finite_setOf_galoisRep_isUnramifiedAt` — a representation into the
  finite discrete monoid `End_A(A²)` is determined by its (open, normal,
  bounded-index) kernel plus a function on the finite quotient;
* `finite_setOf_subgroup_inertiaAt_le` — by the infinite Galois
  correspondence the candidate kernels are the fixing subgroups of finite
  Galois subfields `K ⊆ ℚᵃˡᵍ` of bounded degree, inertia-trivial away
  from `{2, p}`;
* `finite_setOf_intermediateField_inertiaAt_le` — such fields have
  discriminant divisible only by `2` and `p`
  (`not_dvd_discr_of_inertiaTrivialAt`) with exponents bounded by the
  degree, so Hermite's theorem `NumberField.finite_of_discr_bdd` leaves
  finitely many of them;
* bottoming out in the single arithmetic leaf
  `exists_discr_factorization_le_of_finrank_le` — the
  discriminant-exponent bound in terms of the degree.

## Why this module exists

The chain was originally developed inside `Fermat/FLT/Modularity/Patching.lean`.
It is consumed at two places in two different import cones:

* by `Patching.lean` itself, at `A = k[ε]`, as Schlessinger's H3 for the
  hardly ramified deformation functor; and
* by `Fermat/FLT/GaloisRepresentation/HardlyRamified/Deformation.lean`, as the
  H3 stratum `finite_setOf_isHardlyRamified_frames` of the Schlessinger cut of
  `exists_isStrictlyUniversalOnFiniteFrames`.

`Deformation.lean` cannot import `Patching.lean`: `Patching.lean` imports
`Modularity/KhareWintenberger.lean`, which consumes pillar α — which is what
the `Deformation.lean` leaves prove. That is a genuine cycle and Lean rejects
it; it is exactly what `Deformation.lean`'s circularity guard exists for.

The chain itself, however, uses **nothing** from Khare–Wintenberger — only the
`MazurTorsion` inertia dictionary, the infinite Galois correspondence and
mathlib's discriminant theory. So it belongs upstream of both consumers, which
is this module: sitting under `HardlyRamified/`, above `Deformation.lean`,
with an import cone free of `Modularity/*`, `Family.lean` and `Lift.lean`.

CIRCULARITY GUARD (inherited by every consumer): this module imports no
`Modularity/*`, no `Family.lean` and no `Lift.lean`, and nothing here is
discharged through the odd-prime dichotomy
`not_isIrreducible_of_isHardlyRamified_of_five_le` (which is proven over
pillar α). Neither is a temptation: the statements below carry no
irreducibility hypothesis.

DEDUPE FOLLOW-UP — DONE. `Patching.lean`'s verbatim copy of this chain, in
namespace `GaloisRepresentation.Modularity`, has been deleted: the block from
the `InertiaTrivialAt` section docstring through `finite_setOf_isHardlyRamified`
is gone and that file now `import`s this module. Every reference inside
`namespace GaloisRepresentation.Modularity` resolves outward to the copy here,
unqualified and unchanged.

One knock-on: `rank_finTwoFun` used to be duplicated in
`HardlyRamified/Deformation.lean` and `Modularity/Patching.lean`, and BOTH are
downstream of this module, so neither could serve `finite_setOf_isHardlyRamified`
below. Both copies were deleted and the single declaration moved UPSTREAM into
`HardlyRamified/Defs.lean`, keeping the full name
`GaloisRepresentation.rank_finTwoFun`.
-/

@[expose] public section

namespace GaloisRepresentation

open IsDedekindDomain

/-!
### The Hermite–Minkowski decomposition of the restricted-ramification
finiteness leaf (2026-07-24)

A hardly ramified representation over the finite discrete coefficient
ring `A` is a continuous homomorphism of `Γ ℚ` into the FINITE
discrete monoid `End_A(A²)`, unramified outside `{2, p}`.  Its kernel
is an open normal subgroup of index at most `#End_A(A²)` containing
the image of every local inertia group away from `{2, p}`, and the
representation is determined by its kernel `N` together with a
function on the finite quotient `Γ ℚ ⧸ N`
(`finite_setOf_galoisRep_isUnramifiedAt`).  By the infinite Galois
correspondence the candidate kernels are exactly the fixing subgroups
of finite Galois subfields `K ⊆ ℚᵃˡᵍ` of bounded degree on which every
local inertia away from `{2, p}` acts trivially
(`finite_setOf_subgroup_inertiaAt_le`), and there are finitely many
such fields (`finite_setOf_intermediateField_inertiaAt_le`): their
discriminants are divisible only by `2` and `p`
(`not_dvd_discr_of_inertiaTrivialAt`, through the PROVEN inertia
dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup` of
`MazurTorsion`), with exponents bounded in terms of the degree alone
(`exists_discr_factorization_le_of_finrank_le`, PROVEN 2026-07-25 over
the WILD half of the different-exponent bound
`differentIdeal_exponent_le_wild`, itself PROVEN 2026-07-26 over the
single sorried leaf of the cut, the local Eisenstein presentation
`exists_eisensteinDerivative_dvd_of_wild`), so the fields have
bounded discriminant and mathlib's Hermite theorem
`NumberField.finite_of_discr_bdd` applies.
-/

/-- **Triviality of the inertia at a rational prime `q` on a subgroup
of `Γ ℚ`**: every element of the local inertia group at `q`, pushed
into `Γ ℚ` along the (chosen-embedding) map of absolute Galois groups,
lies in `N`.  For `N = K.fixingSubgroup` this says exactly that the
finite Galois subfield `K ⊆ ℚᵃˡᵍ` is unramified at `q` (through the
PROVEN dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup` of
`MazurTorsion`, reached by `not_dvd_discr_of_inertiaTrivialAt`); for
`N` the kernel of a representation it is exactly
`GaloisRep.IsUnramifiedAt`.  Stated in this pointwise form — rather
than as `Subgroup.map … ≤ N` — so that both sides read off
definitionally: the `Subgroup.map` spelling the `MazurTorsion`
dictionary consumes is rebuilt where needed. -/
def InertiaTrivialAt {q : ℕ} (hq : q.Prime)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ)) : Prop :=
  ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
    (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) σ ∈ N
/-- **Unramified fields have coprime discriminant** (PROVEN — the
inertia-to-discriminant transport of the Hermite–Minkowski cut): if
the inertia at a prime `q` fixes the finite Galois subfield
`K ⊆ ℚᵃˡᵍ` pointwise, then `q` does not divide the discriminant of
`K`.  Chain: the pointwise hypothesis is repackaged as the image
inclusion `Subgroup.map … ≤ K.fixingSubgroup`; every prime of `𝓞 K`
over `q` is then unramified by the PROVEN inertia dictionary
`isUnramifiedAt_of_inertia_le_fixingSubgroup` (`MazurTorsion`), and a
prime unramified in every prime above it does not divide the
discriminant (mathlib's `NumberField.not_dvd_discr_iff_forall_mem`).
This is the ρ-free core of `ModThree.lean`'s
`kernel_field_not_dvd_discr`. -/
theorem not_dvd_discr_of_inertiaTrivialAt
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] {q : ℕ} (hq : q.Prime)
    (hfix : InertiaTrivialAt hq K.fixingSubgroup) :
    ¬ ((q : ℤ) ∣ NumberField.discr K) := by
  have hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ K.fixingSubgroup := by
    rintro g ⟨σ, hσ, rfl⟩
    exact hfix σ hσ
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  rw [NumberField.not_dvd_discr_iff_forall_mem K
    (NumberField.RingOfIntegers K) hqZ]
  intro P hP hmem
  haveI := hP
  exact isUnramifiedAt_of_inertia_le_fixingSubgroup K hq hle P
    (by exact_mod_cast hmem)

/-- **Hermite–Minkowski for fields unramified outside `{2, p}`**
(PROVEN over the discriminant-exponent leaf — the field-side
finiteness of the Hermite–Minkowski cut): there are finitely many
finite Galois subfields of `ℚᵃˡᵍ` of degree at most `n` on which the
global inertia at every prime `q ∉ {2, p}` acts trivially.  Proof: the
discriminant of such a field is divisible only by `2` and `p`
(`not_dvd_discr_of_inertiaTrivialAt`), with exponents bounded by
constants `C₂`, `C_p` depending only on `n`
(`exists_discr_factorization_le_of_finrank_le`), so
`|d_K| = 2^{v₂}·p^{v_p} ≤ 2^{C₂}·p^{C_p}` and mathlib's Hermite
theorem `NumberField.finite_of_discr_bdd` finishes. -/
theorem finite_setOf_intermediateField_inertiaAt_le (p n : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    {K : IntermediateField ℚ (AlgebraicClosure ℚ) |
      ∃ _ : FiniteDimensional ℚ K,
        IsGalois ℚ K ∧ Module.finrank ℚ K ≤ n ∧
        ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
          InertiaTrivialAt hq K.fixingSubgroup}.Finite := by
  classical
  obtain ⟨C2, hC2⟩ :=
    exists_discr_factorization_le_of_finrank_le 2 n Nat.prime_two
  obtain ⟨Cp, hCp⟩ :=
    exists_discr_factorization_le_of_finrank_le p n hp
  refine Set.Finite.subset
    ((NumberField.finite_of_discr_bdd (AlgebraicClosure ℚ)
      (2 ^ C2 * p ^ Cp)).image Subtype.val) ?_
  rintro K ⟨hfd, hgal, hrank, hinert⟩
  haveI := hfd
  haveI hNF : NumberField K := @NumberField.mk _ _ inferInstance hfd
  haveI := hgal
  refine ⟨⟨K, hfd⟩, ?_, rfl⟩
  show |NumberField.discr K| ≤ ((2 ^ C2 * p ^ Cp : ℕ) : ℤ)
  have hD0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hN0 : (NumberField.discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  -- every prime factor of `|d_K|` is `2` or `p`
  have hfac : ∀ q : ℕ, q.Prime → q ∣ (NumberField.discr K).natAbs →
      q = 2 ∨ q = p := by
    intro q hq hqN
    by_contra hne
    push Not at hne
    refine not_dvd_discr_of_inertiaTrivialAt K hq
      (hinert q hq hne.1 hne.2) ?_
    have h1 : (((NumberField.discr K).natAbs : ℤ)) ∣ NumberField.discr K := by
      rw [Int.natCast_natAbs]
      exact (abs_dvd _ _).mpr dvd_rfl
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hqN) h1
  -- the factorization `|d_K| = 2^{v₂}·p^{v_p}`
  have hsupp : (NumberField.discr K).natAbs.factorization.support ⊆
      ({2, p} : Finset ℕ) := by
    intro q hqmem
    rw [Nat.support_factorization] at hqmem
    rcases hfac q (Nat.prime_of_mem_primeFactors hqmem)
      (Nat.dvd_of_mem_primeFactors hqmem) with h | h <;> simp [h]
  have hNeq : (NumberField.discr K).natAbs =
      2 ^ (NumberField.discr K).natAbs.factorization 2 *
        p ^ (NumberField.discr K).natAbs.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod_of_support_subset _ hsupp (· ^ ·)
      (fun i _ => pow_zero i), Finset.prod_pair (Ne.symm hp2)]
  -- the two exponent bounds
  have hkey : (NumberField.discr K).natAbs ≤ 2 ^ C2 * p ^ Cp := by
    rw [hNeq]
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (hC2 K hfd hrank))
      (Nat.pow_le_pow_right hp.pos (hCp K hfd hrank))
  have habs : |NumberField.discr K| =
      (((NumberField.discr K).natAbs : ℤ)) := (Int.natCast_natAbs _).symm
  rw [habs]
  exact_mod_cast hkey

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of open normal subgroups of bounded index unramified
outside `{2, p}`** (PROVEN — the Galois-correspondence step of the
Hermite–Minkowski cut; "`G_{ℚ,{2,p}}` is small"): there are finitely
many open normal subgroups `N ≤ Γ ℚ` of index at most `n` containing
the global inertia at every prime `q ∉ {2, p}`.  Proof: every such `N`
is closed (`Subgroup.isClosed_of_isOpen`), hence by the infinite
Galois correspondence it is the fixing subgroup of its fixed field
`K = ℚᵃˡᵍ^N` (`InfiniteGalois.fixingSubgroup_fixedField`), which is
finite-dimensional (`InfiniteGalois.isOpen_iff_finite`), Galois over
`ℚ` (`InfiniteGalois.normal_iff_isGalois`), of degree
`[K : ℚ] = #(Γ ℚ ⧸ N) = index N ≤ n`
(`InfiniteGalois.normalAutEquivQuotient`,
`IsGalois.card_aut_eq_finrank`), and inertia-trivial away from
`{2, p}`; so the set injects into the finite field set of
`finite_setOf_intermediateField_inertiaAt_le` via `fixingSubgroup`. -/
theorem finite_setOf_subgroup_inertiaAt_le (p n : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    {N : Subgroup (Field.absoluteGaloisGroup ℚ) |
      N.Normal ∧ IsOpen (N : Set (Field.absoluteGaloisGroup ℚ)) ∧
      N.FiniteIndex ∧ N.index ≤ n ∧
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        InertiaTrivialAt hq N}.Finite := by
  classical
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  refine Set.Finite.subset
    ((finite_setOf_intermediateField_inertiaAt_le p n hp hp2).image
      fun K => K.fixingSubgroup) ?_
  rintro N ⟨hnorm, hopen, hFI, hidx, hinert⟩
  have hclosed : IsClosed (N : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen N hopen
  have hfix : (IntermediateField.fixedField (E := AlgebraicClosure ℚ)
      N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hclosed⟩
  haveI hfd : FiniteDimensional ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hopen)
  haveI hgalK : IsGalois ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) :=
    (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hfix]; exact hnorm)
  haveI hnorm' := hnorm
  have hcard : Module.finrank ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) =
      Nat.card (Field.absoluteGaloisGroup ℚ ⧸ N) := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      (⟨N, hclosed⟩ : ClosedSubgroup
        (Field.absoluteGaloisGroup ℚ))).toEquiv).symm
  have hrank : Module.finrank ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) ≤ n := by
    rw [hcard, ← Subgroup.index_eq_card N]
    exact hidx
  refine ⟨_, ⟨hfd, hgalK, hrank, ?_⟩, hfix⟩
  intro q hq hq2 hqp
  rw [hfix]
  exact hinert q hq hq2 hqp

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of continuous representations unramified outside
`{2, p}`** (PROVEN — the representations-to-subgroups bookkeeping of
the Hermite–Minkowski cut): over a finite discrete coefficient ring
`A` there are finitely many `Γ ℚ`-representations on `A²` unramified
outside `{2, p}`.  Proof: the endomorphism monoid `E = End_A(A²)` is
finite and discrete, so the kernel of a representation is an open
normal subgroup whose quotient injects into `E` (index at most `#E`),
containing the global inertia away from `{2, p}`
(`GaloisRep.IsUnramifiedAt` transported along
`GaloisRep.toLocal_apply`); the finitely many candidate kernels
(`finite_setOf_subgroup_inertiaAt_le`) each carry finitely many
representations, a representation being determined by the function
`Γ ℚ ⧸ N → E` it induces on `Quotient.out` representatives. -/
theorem finite_setOf_galoisRep_isUnramifiedAt.{uA} (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    {ρ : GaloisRep ℚ A (Fin 2 → A) |
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat}.Finite := by
  classical
  haveI hfinE : Finite (Module.End A (Fin 2 → A)) :=
    Finite.of_injective
      (fun f => (f : (Fin 2 → A) → (Fin 2 → A))) DFunLike.coe_injective
  -- the kernel subgroup of a representation
  let kerOf : GaloisRep ℚ A (Fin 2 → A) →
      Subgroup (Field.absoluteGaloisGroup ℚ) := fun ρ =>
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  -- membership in `kerOf ρ` is triviality of `ρ`
  have hmem : ∀ (ρ : GaloisRep ℚ A (Fin 2 → A))
      (g : Field.absoluteGaloisGroup ℚ), g ∈ kerOf ρ ↔ ρ g = 1 :=
    fun _ _ => Iff.rfl
  -- a representation is recovered on `Quotient.out` representatives
  have hout : ∀ (ρ : GaloisRep ℚ A (Fin 2 → A))
      (N : Subgroup (Field.absoluteGaloisGroup ℚ)), kerOf ρ = N →
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ρ (QuotientGroup.mk (s := N) g).out = ρ g := by
    intro ρ N hN g
    subst hN
    have h1 : ((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g ∈ kerOf ρ :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    have h2 : ρ (((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g) = 1 :=
      (hmem ρ _).mp h1
    have h3 : ρ (QuotientGroup.mk (s := kerOf ρ) g).out *
        ρ (((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g) = ρ g := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [h2, mul_one] at h3
    exact h3
  -- the induced map on the finite quotient is injective
  have hinj : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      Function.Injective
        (fun x : Field.absoluteGaloisGroup ℚ ⧸ kerOf ρ => ρ x.out) := by
    intro ρ x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hxy' : ρ (QuotientGroup.mk (s := kerOf ρ) a).out =
        ρ (QuotientGroup.mk (s := kerOf ρ) b).out := hxy
    rw [hout ρ (kerOf ρ) rfl, hout ρ (kerOf ρ) rfl] at hxy'
    refine (QuotientGroup.eq).mpr ((hmem ρ _).mpr ?_)
    have e1 : ρ (a⁻¹ * b) = ρ a⁻¹ * ρ b := map_mul ρ _ _
    rw [e1, ← hxy', ← map_mul, inv_mul_cancel, map_one]
  -- kernels are open, normal, of index at most `#E`
  have hopenker : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      IsOpen ((kerOf ρ : Subgroup (Field.absoluteGaloisGroup ℚ)) :
        Set (Field.absoluteGaloisGroup ℚ)) := by
    intro ρ
    letI := moduleTopology A (Module.End A (Fin 2 → A))
    haveI : Module.Finite A (Module.End A (Fin 2 → A)) :=
      Module.Finite.of_finite
    haveI : DiscreteTopology (Module.End A (Fin 2 → A)) :=
      discreteTopology_moduleTopology _ _
    have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρ g :=
      ContinuousMonoidHom.continuous_toFun ρ
    exact (isOpen_discrete
      ({1} : Set (Module.End A (Fin 2 → A)))).preimage hcont
  have hnormal : ∀ ρ : GaloisRep ℚ A (Fin 2 → A), (kerOf ρ).Normal := by
    intro ρ
    refine ⟨fun x hx g => ?_⟩
    show ρ (g * x * g⁻¹) = 1
    rw [map_mul, map_mul, (hx : ρ x = 1), mul_one, ← map_mul,
      mul_inv_cancel, map_one]
  have hfinquot : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      Finite (Field.absoluteGaloisGroup ℚ ⧸ kerOf ρ) :=
    fun ρ => Finite.of_injective _ (hinj ρ)
  have hidx : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      (kerOf ρ).index ≤ Nat.card (Module.End A (Fin 2 → A)) := by
    intro ρ
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective _ (hinj ρ)
  -- unramifiedness puts the global inertia inside the kernel
  have hinertker : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      (∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) →
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        InertiaTrivialAt hq (kerOf ρ) := by
    intro ρ hρ q hq hq2 hqp σ hσ
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ q hq hq2 hqp).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    refine (hmem ρ _).mpr ?_
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- assemble: finitely many kernels, finitely many maps per kernel
  have h𝒩fin := finite_setOf_subgroup_inertiaAt_le p
    (Nat.card (Module.End A (Fin 2 → A))) hp hp2
  refine Set.Finite.subset (h𝒩fin.biUnion
    (t := fun N => {ρ : GaloisRep ℚ A (Fin 2 → A) | kerOf ρ = N})
    fun N hN => ?_) ?_
  · -- the fiber over a fixed kernel injects into `Γ ℚ ⧸ N → E`
    haveI : N.FiniteIndex := hN.2.2.1
    haveI : Finite (Field.absoluteGaloisGroup ℚ ⧸ N) :=
      Subgroup.finite_quotient_of_finiteIndex
    refine Set.Finite.of_finite_image (f := fun ρ =>
      fun x : Field.absoluteGaloisGroup ℚ ⧸ N => ρ x.out)
      (Set.toFinite _) ?_
    intro ρ₁ hρ₁ ρ₂ hρ₂ hF
    have key : ∀ g, ρ₁ g = ρ₂ g := by
      intro g
      have e1 := hout ρ₁ N hρ₁ g
      have e2 := hout ρ₂ N hρ₂ g
      have e3 : ρ₁ (QuotientGroup.mk (s := N) g).out =
          ρ₂ (QuotientGroup.mk (s := N) g).out :=
        congrFun hF (QuotientGroup.mk (s := N) g)
      rw [← e1, e3, e2]
    exact GaloisRep.ext key
  · intro ρ hρ
    haveI := hfinquot ρ
    exact Set.mem_biUnion
      ⟨hnormal ρ, hopenker ρ, Subgroup.finiteIndex_of_finite_quotient,
        hidx ρ, hinertker ρ hρ⟩ rfl

/-- **Restricted-ramification finiteness leaf** (DECOMPOSED 2026-07-24
along the Hermite–Minkowski cut above — PROVEN over the
discriminant-exponent statement `exists_discr_factorization_le_of_finrank_le`,
itself PROVEN 2026-07-25 over the wild different-exponent bound
`differentIdeal_exponent_le_wild`, itself PROVEN 2026-07-26 over the
single sorried leaf of the cut, the local Eisenstein presentation
`exists_eisensteinDerivative_dvd_of_wild`;
the arithmetic finiteness input of the FOUNDER cut, and the only
number-theoretic content of Schlessinger's H3 for the hardly ramified
problem): over a FINITE discrete local coefficient `ℤ_p`-algebra `A`,
there are only finitely many hardly ramified representations
`G_ℚ → GL₂(A)`.

Mathematical content (Hermite–Minkowski; Serre, *Galois cohomology*,
II §6, "`G_S` is small"; Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Thm. 10.9.x; Diamond–Darmon–Taylor, *Fermat's Last
Theorem* (1995), §2): a hardly ramified representation is continuous
into the finite discrete group of automorphisms of `A²` and unramified
outside `{2, p}` (`IsHardlyRamified.isUnramified`), so its kernel is
open and its fixed field is a number field of degree
`≤ |GL₂(A)|` unramified outside `{2, p}`.  Ramification bounded to a
fixed finite set of primes bounds the discriminant in terms of the
degree (the exponent of a prime in the different is bounded by
`e - 1 + e·v(e)`), and by the Hermite–Minkowski theorem there are only
finitely many number fields of bounded degree and bounded
discriminant; each supports finitely many homomorphisms of its (finite)
Galois group into the finite `GL₂(A)`.  Equivalently: the Galois group
`G_{ℚ,{2,p}}` of the maximal extension unramified outside `{2,p,∞}` is
a *small* profinite group — it has finitely many open subgroups of
each index — so the set of continuous homomorphisms into any fixed
finite group is finite; the hardly ramified set injects into it.

Both-ways audit: the statement quantifies over an abstract finite
coefficient ring and asserts a plain classical finiteness — true
outright, no vacuity needed.  Consumed by the pillar assembly at
`A = k[ε]` (through `Set.Finite.subset`, the tangent lifts being among
the hardly ramified representations); stated over a general finite
coefficient ring because the same finiteness at every Artinian level
is what the future proof of the deformation-theoretic core leaf will
consume when building the universal ring as a limit. -/
theorem finite_setOf_isHardlyRamified.{uA} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime]
    {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[p] A] [Finite A] [DiscreteTopology A] :
    {ρ : GaloisRep ℚ A (Fin 2 → A) |
      IsHardlyRamified hpodd (rank_finTwoFun A) ρ}.Finite := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  exact (finite_setOf_galoisRep_isUnramifiedAt p hp hp2 (A := A)).subset
    fun ρ hρ q hq hq2 hqp => hρ.isUnramified q hq ⟨hq2, hqp⟩

end GaloisRepresentation
