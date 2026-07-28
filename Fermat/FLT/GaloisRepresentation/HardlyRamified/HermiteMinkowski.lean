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

/-- **(M4) Ultrametric sums: pairwise distinct term valuations force
the valuation of the sum to be the extremal one** (PROVEN 2026-07-26).
For a valuation `v` on a commutative ring with values in a linearly
ordered commutative group with zero, if the terms of a finite sum have
*pairwise distinct* valuations then `v (∑ i ∈ t, f i)` is the supremum
of the `v (f i)` — in the multiplicative normalisation of `Valuation`,
"supremum" is the *smallest order*, i.e. Serre's `v(Σ) = min v(xᵢ)`.

This is the last of the four missing ingredients (M1)–(M4) recorded in
the route of `differentIdeal_exponent_le_wild` below; mathlib has the
two-term case `Valuation.map_add_of_distinct_val` but not the finite-sum
one.  Proof: induction on the (nonempty) index set, using that the
supremum over the tail is *attained* (`Finset.exists_mem_eq_sup'`), so
the head's valuation differs from it and the two-term lemma applies. -/
theorem valuation_sum_eq_sup'_of_pairwise_ne {R Γ₀ ι : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    {t : Finset ι} (ht : t.Nonempty) (f : ι → R)
    (hne : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → v (f i) ≠ v (f j)) :
    v (∑ i ∈ t, f i) = t.sup' ht fun i => v (f i) := by
  revert hne
  induction ht using Finset.Nonempty.cons_induction with
  | singleton a => intro _; simp
  | cons a s h hs ih =>
      intro hne
      have hne' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) ≠ v (f j) := fun i hi j hj hij =>
        hne i (Finset.mem_cons_of_mem hi) j (Finset.mem_cons_of_mem hj) hij
      obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup' hs fun i => v (f i)
      have hab : a ≠ b := fun hh => h (hh ▸ hb)
      have hdist : v (f a) ≠ v (∑ i ∈ s, f i) := by
        rw [ih hne', hbeq]
        exact hne a (Finset.mem_cons_self a s) b (Finset.mem_cons_of_mem hb) hab
      rw [Finset.sum_cons, Finset.sup'_cons, v.map_add_of_distinct_val hdist, ih hne']

/-- **(M4) The form actually consumed: one term bounds the sum**
(PROVEN 2026-07-26).  Same hypothesis as
`valuation_sum_eq_sup'_of_pairwise_ne`, but distinctness is only
required among the terms of *nonzero* valuation (equivalently, the
nonzero terms — the hypothesis `hker` says the valuation has trivial
kernel, which holds for the adic valuation of a Dedekind domain).  That
weakening is essential: the derivative of an Eisenstein polynomial
routinely has several *vanishing* coefficients, so several terms of the
sum are literally `0` and their valuations coincide.  Conclusion, in
additive language: `ord (∑ f i) ≤ ord (f i₀)` for every index `i₀`. -/
theorem valuation_term_le_valuation_sum {R Γ₀ ι : Type*} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (hker : ∀ x : R, v x = 0 → x = 0)
    {t : Finset ι} (f : ι → R) {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hne : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → v (f i) ≠ 0 → v (f j) ≠ 0 → v (f i) ≠ v (f j)) :
    v (f i₀) ≤ v (∑ i ∈ t, f i) := by
  classical
  rcases eq_or_ne (v (f i₀)) 0 with h0 | h0
  · rw [h0]; exact zero_le
  have hsum : ∑ i ∈ t.filter (fun i => v (f i) ≠ 0), f i = ∑ i ∈ t, f i :=
    Finset.sum_filter_of_ne fun x _ hx hv => hx (hker (f x) hv)
  have hi₀' : i₀ ∈ t.filter (fun i => v (f i) ≠ 0) := Finset.mem_filter.mpr ⟨hi₀, h0⟩
  have hne' : ∀ i ∈ t.filter (fun i => v (f i) ≠ 0), ∀ j ∈ t.filter (fun i => v (f i) ≠ 0),
      i ≠ j → v (f i) ≠ v (f j) := by
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    exact hne i hi.1 j hj.1 hij hi.2 hj.2
  rw [← hsum, valuation_sum_eq_sup'_of_pairwise_ne v ⟨i₀, hi₀'⟩ f hne']
  exact Finset.le_sup' (fun i => v (f i)) hi₀'

/-- **The `Q`-adic order of a rational integer is `e · v_q(m)`**
(PROVEN 2026-07-26): for a prime `Q` of `𝓞_K` above the rational prime
`q`, with ramification index `e = e(Q∣q)`, every nonzero natural number
`m` satisfies `ord_Q(m) = e · v_q(m)`.

This is the arithmetic input that makes the distinct-valuations
argument of `differentIdeal_exponent_le_wild` work: it says the
valuations of rational integers all lie in `e·ℤ`, so the term
`i·a_i·π^{i−1}` of `g'(π)` has `Q`-order congruent to `i−1` mod `e`.
It also supplies the *value* of the extremal term, `ord_Q(e·π^{e−1}) =
e·v_q(e) + e − 1`, which is exactly the bound being proven.

Proof: write `m = q^k·m'` with `q ∤ m'`
(`Nat.ordProj_mul_ordCompl_eq_self`).  Bézout for the coprime pair
`(q, m')` shows `m' ∉ Q` (otherwise `1 ∈ Q`), so `ord_Q(m') = 0`; and
`ord_Q(q) = e` because the exact factorization
`q·𝓞_K = Q^e·J` with `Q ⊔ J = ⊤` (`Ideal.eq_prime_pow_mul_coprime`
together with the `normalizedFactors`-count characterization of `e`)
gives `Q^e ∣ (q)` and, by cancellation in the ideal monoid,
`Q^{e+1} ∤ (q)`. -/
theorem intValuation_natCast_eq_exp_ramificationIdx
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (m : ℕ) (hm : m ≠ 0) :
    v.intValuation (m : NumberField.RingOfIntegers K)
      = WithZero.exp (-((Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal *
          m.factorization q : ℕ) : ℤ)) := by
  classical
  set R := NumberField.RingOfIntegers K
  set Q := v.asIdeal
  have hQ : Q.IsPrime := v.isPrime
  have hQ0 : Q ≠ ⊥ := v.ne_bot
  set e := Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q with hedef
  -- the exact factorization of `q·𝓞_K`
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQ.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hmap0 : (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ R) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan0
  haveI hQmax : Q.IsMaximal := hQ.isMaximal hQ0
  obtain ⟨J, hsup, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 Q
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    hmap0 hQ hQ0, ← hedef] at hfac
  have hspanq : Ideal.span {(q : R)} = (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ R) := by
    rw [Ideal.map_span]
    congr 1
    simp
  -- `Q ^ e ∣ (q)` and `¬ Q ^ (e+1) ∣ (q)`
  have hdvd : Q ^ e ∣ Ideal.span {(q : R)} := by
    rw [hspanq, hfac]; exact Dvd.intro _ rfl
  have hnotdvd : ¬ Q ^ (e + 1) ∣ Ideal.span {(q : R)} := by
    rw [hspanq, hfac, pow_succ]
    intro hcon
    have hQJ : Q ∣ J := (mul_dvd_mul_iff_left (pow_ne_zero e hQ0)).mp hcon
    have : Q ⊔ J = Q := sup_eq_left.mpr (Ideal.le_of_dvd hQJ)
    rw [hsup] at this
    exact hQ.ne_top this.symm
  -- hence `ord_Q (q) = e`
  have hqne : (q : R) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := R)).mpr hq.ne_zero
  have hvq : v.intValuation (q : R) = WithZero.exp (-(e : ℤ)) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, v.intValuation (q : R) = WithZero.exp (-(n : ℤ)) := by
      rw [v.intValuation_if_neg hqne]
      exact ⟨_, rfl⟩
    have h1 : e ≤ n := by
      have := (v.intValuation_le_pow_iff_dvd (q : R) e).mpr hdvd
      rw [hn, WithZero.exp_le_exp] at this
      omega
    have h2 : n ≤ e := by
      by_contra hcon
      apply hnotdvd
      rw [← v.intValuation_le_pow_iff_dvd, hn, WithZero.exp_le_exp]
      push_cast
      omega
    rw [hn]
    congr 2
    omega
  -- the `q`-free part has `Q`-order zero
  set k := m.factorization q
  set m' := m / q ^ k
  have hmfac : q ^ k * m' = m := Nat.ordProj_mul_ordCompl_eq_self m q
  have hnd : ¬ q ∣ m' := Nat.not_dvd_ordCompl hq hm
  have hm'mem : (m' : R) ∉ Q := by
    intro hcon
    have hcop : Nat.Coprime q m' := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
    obtain ⟨u, w, huw⟩ : ∃ u w : ℤ, u * (q : ℤ) + w * (m' : ℤ) = 1 := by
      refine ⟨Nat.gcdA q m', Nat.gcdB q m', ?_⟩
      have := Nat.gcd_eq_gcd_ab q m'
      rw [hcop] at this
      push_cast at this ⊢
      linarith [this]
    have hone : (1 : R) ∈ Q := by
      have hq' : ((u : R) * (q : R) + (w : R) * (m' : R)) ∈ Q :=
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hcon)
      have hcast : ((u : R) * (q : R) + (w : R) * (m' : R)) = 1 := by
        have h2 : ((u * (q : ℤ) + w * (m' : ℤ) : ℤ) : R) = ((1 : ℤ) : R) := by rw [huw]
        rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
          Int.cast_one] at h2
        exact h2
      rwa [hcast] at hq'
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  have hvm' : v.intValuation (m' : R) = 1 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hm'mem
  -- put the two halves together
  have hcast : ((m : ℕ) : R) = (q : R) ^ k * (m' : R) := by
    rw [← hmfac, Nat.cast_mul, Nat.cast_pow]
  rw [hcast, map_mul, map_pow, hvq, hvm', mul_one, ← WithZero.exp_nsmul]
  congr 1
  push_cast
  ring

/-- **The value group of an adic valuation is discrete** (PROVEN
2026-07-26): a value strictly below `exp (-M)` is at most
`exp (-(M+1))`.  Used to turn the strict approximation supplied by
mathlib's `exists_intValuation_mul_sub_lt` into a gain of one full unit
of `Q`-order at each step of the digit expansion below. -/
theorem le_exp_neg_succ_of_lt_exp_neg {u : WithZero (Multiplicative ℤ)} {M : ℤ}
    (h : u < WithZero.exp (-M)) : u ≤ WithZero.exp (-(M + 1)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · lift u to ℤ using hu with a
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/-- **The integer Eisenstein digit expansion at a prime of residue
degree one** (PROVEN 2026-07-26 — step 2 of the elementary global route
recorded on `differentIdeal_exponent_le_wild_of_residueDegreeOne`).

Let `Q = v` be a height-one prime of a Dedekind domain `R`, let `x` be a
uniformizer at `Q` (`ord_Q x = 1`), let `P` be a *rational integer* with
`ord_Q P = e`, and suppose every element of `R` is congruent mod `Q` to
a rational integer (`hres`; for `R = 𝓞_K` and `P = q` this says exactly
that the residue degree `f(Q∣q)` is `1`).  Then for every precision `M`
there are integers `c 0, …, c (e−1)` with

  `ord_Q (x ^ e − ∑_{i < e} c i · x ^ i) ≥ M`.

Proof: the ordinary digit expansion in the discrete valuation `ord_Q`.
At precision `M` write `M = e·k + r` with `r < e`; then `P^k · x^r` has
`Q`-order exactly `M`, so mathlib's `exists_intValuation_mul_sub_lt`
produces `y ∈ R` with `ord_Q (z − y·P^k·x^r) > M`, and `hres` replaces
`y` by a rational integer `c` at the cost of a term of order `≥ M + 1`.
The digit `c·P^k` is again a rational integer, so the accumulated
coefficients stay in `ℤ` — which is the whole point, and is exactly
what fails when the residue degree exceeds one. -/
theorem exists_intCoeff_eisenstein_approx {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {e : ℕ} (he : 0 < e) {x : R} {P : ℤ}
    (hx : v.intValuation x = WithZero.exp (-1 : ℤ))
    (hp : v.intValuation ((P : ℤ) : R) = WithZero.exp (-(e : ℤ)))
    (hres : ∀ y : R, ∃ c : ℤ, y - (c : R) ∈ v.asIdeal) (M : ℕ) :
    ∃ c : ℕ → ℤ, v.intValuation (x ^ e - ∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
      ≤ WithZero.exp (-(M : ℤ)) := by
  classical
  induction M with
  | zero =>
      refine ⟨fun _ => 0, ?_⟩
      simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero, Nat.cast_zero,
        neg_zero, WithZero.exp_zero]
      exact v.intValuation_le_one _
  | succ M ih =>
      obtain ⟨c, hz⟩ := ih
      have hr : M % e < e := Nat.mod_lt _ he
      have hkr : e * (M / e) + M % e = M := Nat.div_add_mod M e
      have hvw : v.intValuation (((P ^ (M / e) : ℤ) : R) * x ^ (M % e))
          = WithZero.exp (-(M : ℤ)) := by
        have hkrZ : (e : ℤ) * ((M / e : ℕ) : ℤ) + ((M % e : ℕ) : ℤ) = (M : ℤ) := by
          exact_mod_cast hkr
        rw [Int.cast_pow, map_mul, map_pow, map_pow, hx, hp, ← WithZero.exp_nsmul,
          ← WithZero.exp_nsmul, ← WithZero.exp_add]
        congr 1
        simp only [nsmul_eq_mul]
        linear_combination -hkrZ
      have hle : v.intValuation (x ^ e - ∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
          ≤ v.intValuation (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)) := by rw [hvw]; exact hz
      obtain ⟨y, hy⟩ := v.exists_intValuation_mul_sub_lt hle (Multiplicative.ofAdd (-(M : ℤ)))
      have hy' : v.intValuation ((x ^ e - ∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
          - y * (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)))
          ≤ WithZero.exp (-((M : ℤ) + 1)) := by
        refine le_exp_neg_succ_of_lt_exp_neg ?_
        simpa [WithZero.exp] using hy
      obtain ⟨cy, hcy⟩ := hres y
      have hcyv : v.intValuation (y - (cy : R)) ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
        rw [v.intValuation_le_pow_iff_mem]
        simpa using hcy
      refine ⟨Function.update c (M % e) (c (M % e) + cy * P ^ (M / e)), ?_⟩
      have hsum : ∑ i ∈ Finset.range e,
          ((Function.update c (M % e) (c (M % e) + cy * P ^ (M / e)) i : ℤ) : R) * x ^ i
          = (∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
              + (cy : R) * (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)) := by
        rw [Finset.sum_congr rfl (g := fun i => ((c i : ℤ) : R) * x ^ i
          + (if i = M % e then ((cy * P ^ (M / e) : ℤ) : R) * x ^ i else 0)) ?_]
        · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range e) (M % e)]
          simp only [Finset.mem_range, hr, if_true]
          push_cast
          ring
        · intro i _
          by_cases hir : i = M % e
          · subst hir; rw [Function.update_self, if_pos rfl]; push_cast; ring
          · rw [Function.update_of_ne hir, if_neg hir]; ring
      rw [hsum]
      have hsplit : x ^ e - ((∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
            + (cy : R) * (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)))
          = ((x ^ e - ∑ i ∈ Finset.range e, ((c i : ℤ) : R) * x ^ i)
              - y * (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)))
            + (y - (cy : R)) * (((P ^ (M / e) : ℤ) : R) * x ^ (M % e)) := by ring
      rw [hsplit]
      refine le_trans (v.intValuation.map_add _ _) (max_le ?_ ?_)
      · exact_mod_cast hy'
      · rw [map_mul, hvw]
        calc v.intValuation (y - (cy : R)) * WithZero.exp (-(M : ℤ))
            ≤ WithZero.exp (-(1 : ℤ)) * WithZero.exp (-(M : ℤ)) := by
              gcongr
              simpa using hcyv
          _ = WithZero.exp (-((M : ℤ) + 1)) := by rw [← WithZero.exp_add]; congr 1; ring

/-- **A uniformizer at `Q` that is a unit at every other prime above
`q`** (PROVEN 2026-07-26 — step 1a of the elementary global route
recorded on `differentIdeal_exponent_le_wild_of_residueDegreeOne`).

No approximation theorem is needed: mathlib's coprime splitting
`Ideal.eq_prime_pow_mul_coprime` writes `q·𝓞_K = Q^n · J` with
`Q ⊔ J = ⊤`, and `J` is contained in every prime `P ∣ q` other than `Q`
(a prime containing `Q^n·J` contains `Q^n` — hence `Q`, hence equals `Q`
by maximality — or contains `J`).  Picking `i ∈ Q²`, `j ∈ J` with
`i + j = 1` and a uniformizer `π`, the element `x₀ = π·j + i` has
`ord_Q x₀ = 1` (because `ord_Q(π j) = 1 < 2 ≤ ord_Q i`, by the ultrametric
equality for distinct valuations) and is `≡ 1` modulo every other prime
above `q`, since `j` lies in all of them.
-/
theorem exists_uniformizer_avoiding_other_primes
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ x₀ : NumberField.RingOfIntegers K, v.intValuation x₀ = WithZero.exp (-1 : ℤ) ∧
      ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsPrime → P ≠ v.asIdeal →
        (q : NumberField.RingOfIntegers K) ∈ P → x₀ ∉ P := by
  classical
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hmap0 : (Ideal.span {((q : ℕ) : ℤ)}).map
      (algebraMap ℤ (NumberField.RingOfIntegers K)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hspan0
  obtain ⟨J, hsup, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 v.asIdeal
  obtain ⟨n, hfac⟩ : ∃ n : ℕ, (Ideal.span {((q : ℕ) : ℤ)}).map
      (algebraMap ℤ (NumberField.RingOfIntegers K)) = v.asIdeal ^ n * J := ⟨_, hfac⟩
  have hspanq : Ideal.span {(q : NumberField.RingOfIntegers K)}
      = (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
    rw [Ideal.map_span]
    congr 1
    simp
  have hcop : IsCoprime (v.asIdeal ^ 2) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp hcop
  have hjnot : j ∉ v.asIdeal := by
    intro hjm
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      rw [← hij]
      exact Ideal.add_mem _ (Ideal.pow_le_self (by norm_num) hi) hjm
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hvπj : v.intValuation (π * j) = WithZero.exp (-1 : ℤ) := by
    rw [map_mul, hπ, HeightOneSpectrum.intValuation_eq_one_iff.mpr hjnot, mul_one]
  have hvi : v.intValuation i ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem i 2).mpr hi
  have hlt : v.intValuation i < v.intValuation (π * j) := by
    rw [hvπj]
    refine lt_of_le_of_lt hvi ?_
    rw [WithZero.exp_lt_exp]
    norm_num
  refine ⟨π * j + i, by rw [v.intValuation.map_add_eq_of_lt_left hlt, hvπj], ?_⟩
  intro P hP hPne hqP hmemP
  haveI : P.IsPrime := hP
  -- `J ≤ P`
  have hJP : J ≤ P := by
    have hle : v.asIdeal ^ n * J ≤ P := by
      rw [← hfac, ← hspanq, Ideal.span_le, Set.singleton_subset_iff]
      exact hqP
    rcases hP.mul_le.mp hle with hpow | hJ
    · exfalso
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero, Ideal.one_eq_top] at hpow
        exact hP.ne_top (top_le_iff.mp hpow)
      · have hQP : v.asIdeal ≤ P :=
          (Ideal.IsPrime.pow_le_iff (I := v.asIdeal) (P := P) hpos.ne').mp hpow
        exact hPne (((v.isPrime.isMaximal v.ne_bot).eq_of_le hP.ne_top hQP)).symm
    · exact hJ
  have hjP : j ∈ P := hJP hj
  have h1 : (1 : NumberField.RingOfIntegers K) ∈ P := by
    have : (1 : NumberField.RingOfIntegers K) = (π * j + i) - π * j + (1 - i) := by ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.sub_mem _ hmemP (Ideal.mul_mem_left _ _ hjP)) ?_
    have : (1 : NumberField.RingOfIntegers K) - i = j := by rw [← hij]; ring
    rw [this]; exact hjP
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- **Adjusting an element by a multiple of `q²` to make it a
generator of `K/ℚ`** (PROVEN 2026-07-26 — step 1b of the same route).

Fix a primitive element `θ ∈ 𝓞_K` (obtained from
`Field.exists_primitive_element` over `ℚ` and cleared of denominators by
`IsAlgebraic.exists_integral_multiple`, which applies to `ℤ` through
`IsFractionRing.isAlgebraic_iff`).  The elements
`x_N = x₀ + m^{N+2}·θ`, `N : ℕ`, all differ from `x₀` by an element of
`(m²)`; since `K/ℚ` is finite separable there are only finitely many
intermediate fields (`Field.finite_intermediateField_of_exists_primitive_element`),
so two of the fields `ℚ(x_{N₁})`, `ℚ(x_{N₂})` coincide.  Their common
value `F` then contains `(m^{N₁+2} − m^{N₂+2})·θ` with a nonzero
*rational* scalar, hence contains `θ`, hence is all of `K` — so
`ℚ(x_{N₁}) = K` and `x_{N₁}` is the required generator.  (Note the
scalar must be rational for this step, which is why the increment is a
power of a natural number rather than of an arbitrary ring element.)
-/
theorem exists_generator_sub_mem_span_sq
    (K : Type*) [Field K] [NumberField K]
    (x₀ : NumberField.RingOfIntegers K) (m : ℕ) (hm : 1 < m) :
    ∃ x : NumberField.RingOfIntegers K,
      x - x₀ ∈ Ideal.span {((m : NumberField.RingOfIntegers K)) ^ 2} ∧
      Algebra.adjoin ℚ {(algebraMap (NumberField.RingOfIntegers K) K x)} = ⊤ := by
  classical
  -- a primitive element of `K/ℚ` lying in `𝓞 K`
  obtain ⟨α, hα⟩ := _root_.Field.exists_primitive_element ℚ K
  have halgZ : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨d, hd0, hdint⟩ := halgZ.exists_integral_multiple
  set θ' : K := (d : K) * α with hθ'def
  have hθ'int : IsIntegral ℤ θ' := by simpa [hθ'def, zsmul_eq_mul] using hdint
  have hcast : algebraMap ℚ K ((d : ℚ)) = (d : K) := map_intCast _ d
  have h3 : (algebraMap ℚ K (((d : ℚ))⁻¹)) * θ' = α := by
    rw [hθ'def, ← mul_assoc, ← hcast, ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hd0 : ((d : ℚ)) ≠ 0), map_one, one_mul]
  have hθ'top : IntermediateField.adjoin ℚ {θ'} = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hα]
    refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    rw [← h3]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self ℚ θ')
  obtain ⟨θ, hθ⟩ : ∃ θ : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K θ = θ' :=
    ⟨⟨θ', hθ'int⟩, rfl⟩
  -- pigeonhole over the finitely many intermediate fields
  haveI : Finite (IntermediateField ℚ K) :=
    _root_.Field.finite_intermediateField_of_exists_primitive_element ℚ K ⟨α, hα⟩
  set f : ℕ → IntermediateField ℚ K := fun N =>
    IntermediateField.adjoin ℚ
      {algebraMap (NumberField.RingOfIntegers K) K (x₀ + (m : NumberField.RingOfIntegers K) ^ (N + 2) * θ)}
    with hfdef
  obtain ⟨N₁, N₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x₀ + (m : NumberField.RingOfIntegers K) ^ (N₁ + 2) * θ, ?_, ?_⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨(m : NumberField.RingOfIntegers K) ^ N₁ * θ, ?_⟩
    ring
  · -- the adjoined field is everything
    have hmem₁ : algebraMap (NumberField.RingOfIntegers K) K
        (x₀ + (m : NumberField.RingOfIntegers K) ^ (N₁ + 2) * θ) ∈ f N₁ :=
      IntermediateField.mem_adjoin_simple_self _ _
    have hmem₂ : algebraMap (NumberField.RingOfIntegers K) K
        (x₀ + (m : NumberField.RingOfIntegers K) ^ (N₂ + 2) * θ) ∈ f N₁ := by
      rw [heq]; exact IntermediateField.mem_adjoin_simple_self _ _
    set c : ℚ := (m : ℚ) ^ (N₁ + 2) - (m : ℚ) ^ (N₂ + 2) with hcdef
    have hcne : c ≠ 0 := by
      rw [hcdef, sub_ne_zero]
      intro hcon
      have hpow : (m : ℕ) ^ (N₁ + 2) = (m : ℕ) ^ (N₂ + 2) := by exact_mod_cast hcon
      exact hne (Nat.add_right_cancel (Nat.pow_right_injective hm hpow))
    have hdiff : algebraMap ℚ K c * θ' =
        algebraMap (NumberField.RingOfIntegers K) K
          (x₀ + (m : NumberField.RingOfIntegers K) ^ (N₁ + 2) * θ) -
        algebraMap (NumberField.RingOfIntegers K) K
          (x₀ + (m : NumberField.RingOfIntegers K) ^ (N₂ + 2) * θ) := by
      rw [hcdef, ← hθ]
      push_cast
      ring
    have hθmem : θ' ∈ f N₁ := by
      have : θ' = algebraMap ℚ K c⁻¹ * (algebraMap ℚ K c * θ') := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcne, map_one, one_mul]
      rw [this, hdiff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (sub_mem hmem₁ hmem₂)
    have htop : f N₁ = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hθ'top]
      exact IntermediateField.adjoin_simple_le_iff.mpr hθmem
    have hint : IsAlgebraic ℚ (algebraMap (NumberField.RingOfIntegers K) K
        (x₀ + (m : NumberField.RingOfIntegers K) ^ (N₁ + 2) * θ)) :=
      Algebra.IsAlgebraic.isAlgebraic _
    have hsub := congrArg IntermediateField.toSubalgebra htop
    rwa [hfdef, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hsub

/-- **The constant coefficient of the minimal polynomial has `Q`-order
exactly `e`** (PROVEN 2026-07-26 — step 1c of the same route).

Let `x` generate `K/ℚ`, be a uniformizer at `Q`, and be a unit at every
other prime above `q`.  Then `ord_Q((minpoly ℤ x).coeff 0) = e`.

Proof.  The residue-degree-one hypothesis `hres` makes `𝓞_K ⧸ Q` a
quotient of `Fin q`, so `absNorm Q ≤ q`; and `absNorm Q` is a power of a
rational prime lying in `Q`, which must be `q` by Bézout — so
`absNorm Q = q`.  Writing `(x) = Q·I`, multiplicativity of `absNorm`
gives `absNorm (x) = q · absNorm I`, and `q ∤ absNorm I`: otherwise
`Ideal.exists_isMaximal_dvd_of_dvd_absNorm'` produces a maximal `P ∣ I`
above `q`, which is either `Q` (forcing `Q² ∣ (x)`, contradicting
`ord_Q x = 1`) or another prime above `q` containing `x`, contradicting
`hother`.  So `v_q(absNorm (x)) = 1`.  Finally the constant coefficient
of `minpoly ℤ x` is `± N_{K/ℚ}(x)` — transport the power basis
`ℚ⟮x⟯ ≃ₐ[ℚ] K` and apply `PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
together with `Algebra.coe_norm_int` and
`minpoly.isIntegrallyClosed_eq_field_fractions` — so its absolute value
is `absNorm (x)`, and `intValuation_natCast_eq_exp_ramificationIdx`
converts `v_q = 1` into `ord_Q = e`.
-/
theorem intValuation_coeff_zero_minpoly
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hres : ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (x : NumberField.RingOfIntegers K)
    (hgen : Algebra.adjoin ℚ {(algebraMap (NumberField.RingOfIntegers K) K x)} = ⊤)
    (hx : v.intValuation x = WithZero.exp (-1 : ℤ))
    (hother : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsPrime → P ≠ v.asIdeal →
      (q : NumberField.RingOfIntegers K) ∈ P → x ∉ P) :
    v.intValuation (((minpoly ℤ x).coeff 0 : ℤ) : NumberField.RingOfIntegers K)
      = WithZero.exp (-((Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal : ℕ) : ℤ)) := by
  classical
  haveI hQmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  -- (C1) the residue degree is one, so `absNorm Q = q`
  obtain ⟨p, n, hn, hpQ, hp, hPnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  have hpq : p = q := by
    by_contra hcon
    have hgcd : Nat.gcd p q = 1 := (Nat.coprime_primes hp hq).mpr hcon
    have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hgcd)
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      have h2 : ((a : NumberField.RingOfIntegers K)) * ((p : ℕ) : NumberField.RingOfIntegers K)
          + ((b : NumberField.RingOfIntegers K)) * ((q : ℕ) : NumberField.RingOfIntegers K)
          = 1 := by
        have h3 := congrArg (fun t : ℤ => ((t : NumberField.RingOfIntegers K))) hab
        push_cast at h3
        simpa using h3
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpQ) (Ideal.mul_mem_left _ _ hmem)
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hsurj : Function.Surjective
      (fun i : Fin q => Ideal.Quotient.mk v.asIdeal ((i : ℕ) : NumberField.RingOfIntegers K)) := by
    intro z
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨c, hc⟩ := hres y0
    have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
    have hnn : (0 : ℤ) ≤ c % (q : ℤ) := Int.emod_nonneg c (by exact_mod_cast hq.ne_zero)
    have hlt : (c % (q : ℤ)).toNat < q := by
      have h1 : c % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos c hq0
      omega
    refine ⟨⟨(c % (q : ℤ)).toNat, hlt⟩, ?_⟩
    refine Ideal.Quotient.eq.mpr ?_
    have hcast : ((((c % (q : ℤ)).toNat : ℕ)) : NumberField.RingOfIntegers K)
        = ((c % (q : ℤ) : ℤ) : NumberField.RingOfIntegers K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    have hmoddef : c % (q : ℤ) = c - (q : ℤ) * (c / (q : ℤ)) := Int.emod_def c (q : ℤ)
    have hdecomp : ((c % (q : ℤ) : ℤ) : NumberField.RingOfIntegers K)
        = (c : NumberField.RingOfIntegers K)
          - (q : NumberField.RingOfIntegers K) * ((c / (q : ℤ) : ℤ) : NumberField.RingOfIntegers K) := by
      rw [hmoddef, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    show ((((c % (q : ℤ)).toNat : ℕ)) : NumberField.RingOfIntegers K) - y0 ∈ v.asIdeal
    rw [hcast, hdecomp]
    have hrw : (c : NumberField.RingOfIntegers K)
          - (q : NumberField.RingOfIntegers K) * ((c / (q : ℤ) : ℤ) : NumberField.RingOfIntegers K)
          - y0
        = -(y0 - (c : NumberField.RingOfIntegers K))
          - (q : NumberField.RingOfIntegers K)
            * ((c / (q : ℤ) : ℤ) : NumberField.RingOfIntegers K) := by ring
    rw [hrw]
    exact Ideal.sub_mem _ (neg_mem hc) (Ideal.mul_mem_right _ _ hmem)
  have hfin : Ideal.absNorm v.asIdeal ≤ q := by
    have hcard : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≤ Nat.card (Fin q) :=
      Nat.card_le_card_of_surjective _ hsurj
    simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hcard
  rw [hpq] at hPnorm
  have hn1 : n = 1 := by
    have hle : q ^ n ≤ q ^ 1 := by rw [pow_one, ← hPnorm]; exact hfin
    have hnn := (Nat.pow_le_pow_iff_right hq.one_lt).mp hle
    omega
  have habsQ : Ideal.absNorm v.asIdeal = q := by rw [hPnorm, hn1, pow_one]
  -- (C2) the `q`-part of the absolute norm of `x` is exactly one
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [WithZero.exp_ne_zero.symm] at hx
  have hQdvd : v.asIdeal ∣ Ideal.span {x} := by
    have hd := (v.intValuation_le_pow_iff_dvd x 1).mp (by rw [hx]; norm_num)
    rwa [pow_one] at hd
  obtain ⟨I, hI⟩ := hQdvd
  have hIbot : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot] at hI
    exact hx0 (by simpa [Ideal.span_singleton_eq_bot] using hI)
  have hIabs0 : Ideal.absNorm I ≠ 0 := fun h => hIbot (Ideal.absNorm_eq_zero_iff.mp h)
  have habsx : (Ideal.span {x}).absNorm = q * Ideal.absNorm I := by
    rw [hI, _root_.map_mul, habsQ]
  have hnd : ¬ (q ∣ Ideal.absNorm I) := by
    intro hdvd
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq I hdvd
    have hqP : (q : NumberField.RingOfIntegers K) ∈ P := by
      have h0 : ((q : ℤ)) ∈ P.under ℤ := by rw [hPunder]; exact Ideal.mem_span_singleton_self _
      rw [Ideal.mem_under] at h0
      simpa using h0
    have hxP : x ∈ P := by
      have hdvdx : P ∣ Ideal.span {x} := by rw [hI]; exact hPdvd.mul_left _
      exact Ideal.le_of_dvd hdvdx (Ideal.mem_span_singleton_self x)
    by_cases hPQ : P = v.asIdeal
    · rw [hPQ] at hPdvd
      have h2 : v.asIdeal ^ 2 ∣ Ideal.span {x} := by
        rw [hI, sq]; exact mul_dvd_mul_left _ hPdvd
      have hle2 := (v.intValuation_le_pow_iff_dvd x 2).mpr h2
      rw [hx, WithZero.exp_le_exp] at hle2
      norm_num at hle2
    · exact hother P hPmax.isPrime hPQ hqP hxP
  -- (C3) the constant coefficient of the minimal polynomial is, up to sign, the norm
  set y : K := algebraMap (NumberField.RingOfIntegers K) K x with hydef
  have hyint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have htopIF : IntermediateField.adjoin ℚ {y} = ⊤ := by
    refine IntermediateField.toSubalgebra_injective ?_
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hyint.isAlgebraic, hgen]
    rfl
  have hpbgen : ((IntermediateField.adjoin.powerBasis hyint).map
      ((IntermediateField.equivOfEq htopIF).trans IntermediateField.topEquiv)).gen = y := rfl
  have hnormQ : Algebra.norm ℚ y = (-1) ^ ((IntermediateField.adjoin.powerBasis hyint).map
      ((IntermediateField.equivOfEq htopIF).trans IntermediateField.topEquiv)).dim *
      (minpoly ℚ y).coeff 0 := by
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      ((IntermediateField.adjoin.powerBasis hyint).map
        ((IntermediateField.equivOfEq htopIF).trans IntermediateField.topEquiv))
    rwa [hpbgen] at hpb
  have hminpoly : minpoly ℚ y = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ K (Algebra.IsIntegral.isIntegral x)
  have hcoeffQ : (minpoly ℚ y).coeff 0 = (((minpoly ℤ x).coeff 0 : ℤ) : ℚ) := by
    rw [hminpoly, Polynomial.coeff_map]
    simp
  have hnormcoe : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ y := Algebra.coe_norm_int x
  have hnormZ : Algebra.norm ℤ x = (-1) ^ ((IntermediateField.adjoin.powerBasis hyint).map
      ((IntermediateField.equivOfEq htopIF).trans IntermediateField.topEquiv)).dim *
      (minpoly ℤ x).coeff 0 := by
    have hQeq : ((Algebra.norm ℤ x : ℤ) : ℚ)
        = ((((-1) ^ ((IntermediateField.adjoin.powerBasis hyint).map
            ((IntermediateField.equivOfEq htopIF).trans IntermediateField.topEquiv)).dim *
            (minpoly ℤ x).coeff 0 : ℤ)) : ℚ) := by
      rw [hnormcoe, hnormQ, hcoeffQ]
      push_cast
      ring
    exact_mod_cast hQeq
  have hcoeffabs : ((minpoly ℤ x).coeff 0).natAbs = (Ideal.span {x}).absNorm := by
    rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_mul]
    simp
  -- assembly
  have hne0 : ((minpoly ℤ x).coeff 0).natAbs ≠ 0 := by
    rw [hcoeffabs, habsx]
    exact Nat.mul_ne_zero hq.ne_zero hIabs0
  have hfact : (((minpoly ℤ x).coeff 0).natAbs).factorization q = 1 := by
    rw [hcoeffabs, habsx, Nat.factorization_mul hq.ne_zero hIabs0]
    simp [hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hnd]
  have hhelp := intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem _ hne0
  rw [hfact, mul_one] at hhelp
  rcases Int.natAbs_eq ((minpoly ℤ x).coeff 0) with heq | heq
  · rw [heq, Int.cast_natCast]
    exact hhelp
  · rw [heq, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
    exact hhelp

/-- **A global generator of `K/ℚ` that is a uniformizer at `Q`**
(PROVEN 2026-07-26 — step 1 of the elementary global route recorded on
`differentIdeal_exponent_le_wild_of_residueDegreeOne`; standard
algebraic number theory, no local fields).

Produces `x ∈ 𝓞_K` with `ℚ(x) = K`, `ord_Q x = 1`, and the constant
coefficient of its minimal polynomial of `Q`-order exactly `e`.

Assembled from the three steps above: `exists_uniformizer_avoiding_other_primes`
supplies `x₀` with `ord_Q x₀ = 1` that is a unit at the other primes over
`q`; `exists_generator_sub_mem_span_sq` moves it by an element of `(q²)`
to make it a generator, which changes neither the `Q`-order (the
increment has `Q`-order `≥ 2`) nor the behaviour at the other primes
above `q` (the increment lies in each of them); and
`intValuation_coeff_zero_minpoly` computes the constant coefficient.
-/
theorem exists_generator_uniformizer_at (K : Type*) [Field K] [NumberField K]
    (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hres : ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal) :
    ∃ x : NumberField.RingOfIntegers K,
      Algebra.adjoin ℚ {(algebraMap (NumberField.RingOfIntegers K) K x)} = ⊤ ∧
      v.intValuation x = WithZero.exp (-1 : ℤ) ∧
      v.intValuation (((minpoly ℤ x).coeff 0 : ℤ) : NumberField.RingOfIntegers K)
        = WithZero.exp (-(e : ℤ)) := by
  obtain ⟨x₀, hx₀, hother₀⟩ := exists_uniformizer_avoiding_other_primes K q hq v
  obtain ⟨x, hsub, hgen⟩ := exists_generator_sub_mem_span_sq K x₀ q hq.one_lt
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hsub
  have hz : x = x₀ + w * (q : NumberField.RingOfIntegers K) ^ 2 := by rw [hw]; ring
  have hmem2 : w * (q : NumberField.RingOfIntegers K) ^ 2 ∈ v.asIdeal ^ 2 :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hmem 2)
  have hvz : v.intValuation (w * (q : NumberField.RingOfIntegers K) ^ 2)
      ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 2).mpr hmem2
  have hlt : v.intValuation (w * (q : NumberField.RingOfIntegers K) ^ 2)
      < v.intValuation x₀ := by
    rw [hx₀]
    refine lt_of_le_of_lt hvz ?_
    rw [WithZero.exp_lt_exp]
    norm_num
  have hx : v.intValuation x = WithZero.exp (-1 : ℤ) := by
    rw [hz, v.intValuation.map_add_eq_of_lt_left hlt, hx₀]
  have hother : ∀ P : Ideal (NumberField.RingOfIntegers K), P.IsPrime → P ≠ v.asIdeal →
      (q : NumberField.RingOfIntegers K) ∈ P → x ∉ P := by
    intro P hP hPne hqP hxP
    have hzP : w * (q : NumberField.RingOfIntegers K) ^ 2 ∈ P :=
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hqP 2 (by norm_num))
    have hx₀P : x₀ ∈ P := by
      have hx₀eq : x₀ = x - w * (q : NumberField.RingOfIntegers K) ^ 2 := by rw [hz]; ring
      rw [hx₀eq]
      exact Ideal.sub_mem _ hxP hzP
    exact hother₀ P hP hPne hqP hx₀P
  refine ⟨x, hgen, hx, ?_⟩
  rw [he]
  exact intValuation_coeff_zero_minpoly K q hq v hmem hres x hgen hx hother

open _root_.Polynomial in
/-- **From an integer Eisenstein approximation to Serre's bound**
(PROVEN 2026-07-26 — steps 3–6 of the elementary global route recorded on
`differentIdeal_exponent_le_wild_of_residueDegreeOne`; polynomial
division and valuation bookkeeping only, no local fields).

Given the good generator `x` of `exists_generator_uniformizer_at` and an
integer-coefficient approximate Eisenstein relation
`ord_Q (x^e − ∑_{i<e} c_i x^i) ≥ M` from
`exists_intCoeff_eisenstein_approx`, with `M` large compared with `d`
and `e`, Serre's bound follows.

Route as carried out, writing `F = minpoly ℤ x`,
`g = X^e − ∑_{i<e} C (c i)·X^i` (monic of degree `e`), `H = F /ₘ g` and
`Rm = F %ₘ g` (degree `< e`):

* *The rigidity input.*  `ord_Q (a) ∈ e·ℤ` for every RATIONAL INTEGER
  `a ≠ 0` (`intValuation_natCast_eq_exp_ramificationIdx`), so the terms
  `a_i·x^i` of a sum with integer coefficients and `i < e` have
  `Q`-orders `e·v_q(a_i) + i` that are PAIRWISE DISTINCT — they have
  distinct residues mod `e`.  This is the whole content of the leaf: it
  is what "the digits are rational integers" buys, and it is exactly
  what fails for digits merely of order in `e·ℤ` (see the refutation
  recorded on `exists_generator_uniformizer_at`'s sibling).
  `valuation_term_le_valuation_sum` then bounds every single term by the
  sum.
* `aeval_derivative_mem_differentIdeal` (mathlib) gives
  `𝔡_{𝓞_K/ℤ} ∣ (F'(x))`, hence `d ≤ ord_Q (F'(x))` from `hd`.
* `F(x) = 0` and `ord_Q (g(x)) ≥ M` give `ord_Q (Rm(x)) ≥ M`; the
  rigidity input forces `ord_Q (Rm_i·x^i) ≥ M` for every `i < e`,
  whence `ord_Q (Rm_i·x^{i−1}) ≥ M − 1` and `ord_Q (Rm'(x)) ≥ M − 1`.
* *The cofactor is a `Q`-unit.*  `x ∈ Q` and `ord_Q (x^e − ∑ c_i x^i) > 0`
  give `∑ c_i x^i ∈ Q`, and all terms with `i ≥ 1` are in `Q`, so the
  rational integer `c_0` lies in `Q`; being a rational integer its order
  is then `≥ e`, i.e. `ord_Q (g(0)) ≥ e`.  Comparing with
  `F(0) = g(0)·H(0) + Rm(0)`, where `ord_Q (F(0)) = e` (`hc0`) and
  `ord_Q (Rm(0)) ≥ M > e`, gives `ord_Q (g(0)·H(0)) = e` and hence
  `ord_Q (H(0)) = 0`; then `ord_Q (H(x)) = 0` because `H(x) − H(0) ∈ (x) ⊆ Q`.
* *Conclusion.*  `F' = Rm' + g'H + gH'`, and the three terms other than
  `g'(x)H(x)` have order `≥ min (d, M−1, M) = d`, so `ord_Q (g'(x)) ≥ d`.
  Finally the same distinct-residues argument applied to
  `g'(x) = ∑_{i<e} (i+1)·g_{i+1}·x^i`, whose `i = e−1` term is
  `e·x^{e−1}`, gives `ord_Q (g'(x)) ≤ e·v_q(e) + e − 1`.  Hence
  `d ≤ e − 1 + e·v_q(e)`. -/
theorem differentIdeal_exponent_le_of_intEisenstein_approx
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (x : NumberField.RingOfIntegers K)
    (hgen : Algebra.adjoin ℚ {(algebraMap (NumberField.RingOfIntegers K) K x)} = ⊤)
    (hx : v.intValuation x = WithZero.exp (-1 : ℤ))
    (hc0 : v.intValuation (((minpoly ℤ x).coeff 0 : ℤ) : NumberField.RingOfIntegers K)
      = WithZero.exp (-(e : ℤ)))
    (c : ℕ → ℤ) (M : ℕ)
    (happrox : v.intValuation (x ^ e - ∑ i ∈ Finset.range e,
      ((c i : ℤ) : NumberField.RingOfIntegers K) * x ^ i) ≤ WithZero.exp (-(M : ℤ)))
    (d : ℕ) (hdM : d + 2 * e + 2 ≤ M)
    (hd : v.asIdeal ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ e - 1 + e * e.factorization q := by
  classical
  -- ## 0. Preliminaries
  have hker : ∀ y, v.intValuation y = 0 → y = 0 := by
    intro y hy
    by_contra hy0
    exact v.intValuation_ne_zero y hy0 hy
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he0 : 0 < e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0)
  -- ## 1. valuations of rational integers lie in `e·ℤ`
  have hnat : ∀ m : ℕ, m ≠ 0 →
      v.intValuation (m : NumberField.RingOfIntegers K)
        = WithZero.exp (-((e * m.factorization q : ℕ) : ℤ)) := by
    intro m hm
    rw [he]
    exact intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem m hm
  have hZval : ∀ a : ℤ, a ≠ 0 → ∃ k : ℕ,
      v.intValuation (a : NumberField.RingOfIntegers K)
        = WithZero.exp (-((e * k : ℕ) : ℤ)) := by
    intro a ha
    obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) ∨ a = -(n : ℤ) := ⟨a.natAbs, Int.natAbs_eq a⟩
    rcases hn with rfl | rfl
    · exact ⟨n.factorization q, by push_cast; exact hnat n (by exact_mod_cast ha)⟩
    · refine ⟨n.factorization q, ?_⟩
      have hcast : ((-(n : ℤ) : ℤ) : NumberField.RingOfIntegers K)
          = -((n : ℕ) : NumberField.RingOfIntegers K) := by push_cast; ring
      rw [hcast, Valuation.map_neg]
      exact hnat n (by simpa using ha)
  have hxpow : ∀ i : ℕ, v.intValuation (x ^ i) = WithZero.exp (-(i : ℤ)) := by
    intro i
    rw [map_pow, hx, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hterm : ∀ (a : ℤ) (i : ℕ), a ≠ 0 → ∃ k : ℕ,
      v.intValuation ((a : NumberField.RingOfIntegers K) * x ^ i)
        = WithZero.exp (-((e * k : ℕ) : ℤ) - (i : ℤ)) := by
    intro a i ha
    obtain ⟨k, hk⟩ := hZval a ha
    refine ⟨k, ?_⟩
    rw [map_mul, hk, hxpow, ← WithZero.exp_add]
    exact congrArg WithZero.exp (by ring)
  have hmodkey : ∀ (k₁ k₂ i j : ℕ), i < e → j < e →
      -((e * k₁ : ℕ) : ℤ) - (i : ℤ) = -((e * k₂ : ℕ) : ℤ) - (j : ℤ) → i = j := by
    intro k₁ k₂ i j hi hj h
    have h' : e * k₁ + i = e * k₂ + j := by
      have h2 : ((e * k₁ + i : ℕ) : ℤ) = ((e * k₂ + j : ℕ) : ℤ) := by push_cast at h ⊢; linarith
      exact_mod_cast h2
    rcases le_total k₁ k₂ with hk | hk
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [Nat.mul_add] at h'
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [Nat.mul_zero, Nat.add_zero] at h'; omega
      · exfalso
        have hle : e ≤ e * m := Nat.le_mul_of_pos_right e hm
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [Nat.mul_add] at h'
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [Nat.mul_zero, Nat.add_zero] at h'; omega
      · exfalso
        have hle : e ≤ e * m := Nat.le_mul_of_pos_right e hm
        omega
  have hpairwise : ∀ (b : ℕ → ℤ),
      ∀ i ∈ Finset.range e, ∀ j ∈ Finset.range e, i ≠ j →
        v.intValuation ((b i : NumberField.RingOfIntegers K) * x ^ i) ≠ 0 →
        v.intValuation ((b j : NumberField.RingOfIntegers K) * x ^ j) ≠ 0 →
        v.intValuation ((b i : NumberField.RingOfIntegers K) * x ^ i)
          ≠ v.intValuation ((b j : NumberField.RingOfIntegers K) * x ^ j) := by
    intro b i hi j hj hij hn1 hn2 heq
    have hbi : b i ≠ 0 := by intro h0; rw [h0] at hn1; simp at hn1
    have hbj : b j ≠ 0 := by intro h0; rw [h0] at hn2; simp at hn2
    obtain ⟨k₁, hk₁⟩ := hterm (b i) i hbi
    obtain ⟨k₂, hk₂⟩ := hterm (b j) j hbj
    rw [hk₁, hk₂, WithZero.exp_inj] at heq
    exact hij (hmodkey k₁ k₂ i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) heq)
  -- ## 2. the approximating Eisenstein polynomial `g`
  set p : Polynomial ℤ := ∑ i ∈ Finset.range e, C (c i) * X ^ i with hp
  have hpdeg : p.degree < (e : ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe e)).mpr ?_
    intro i hi
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le i (c i))
      (by exact_mod_cast Finset.mem_range.mp hi)
  have hpcoeff : ∀ n : ℕ, e ≤ n → p.coeff n = 0 := by
    intro n hn
    rw [hp, finsetSum_coeff]
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [coeff_C_mul, coeff_X_pow, if_neg (by have := Finset.mem_range.mp hi; omega), mul_zero]
  have hpcoeff0 : p.coeff 0 = c 0 := by
    rw [hp, finsetSum_coeff, Finset.sum_eq_single 0]
    · simp
    · intro i _ hne
      rw [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hne), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr he0) h
  set g : Polynomial ℤ := X ^ e - p with hgdef
  have hgdeg : g.degree = (e : ℕ) := by
    rw [hgdef, degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  have hgnd : g.natDegree = e := natDegree_eq_of_degree_eq_some hgdeg
  have hgcoeff : g.coeff e = 1 := by
    rw [hgdef, coeff_sub, coeff_X_pow, if_pos rfl, hpcoeff e le_rfl, sub_zero]
  have hgmonic : g.Monic := by
    have hlc : g.leadingCoeff = 1 := by rw [Polynomial.leadingCoeff, hgnd, hgcoeff]
    exact hlc
  have hgcoeff0 : g.coeff 0 = -c 0 := by
    rw [hgdef, coeff_sub, coeff_X_pow, if_neg (by omega), hpcoeff0, zero_sub]
  have hgaeval : aeval x g = x ^ e - ∑ i ∈ Finset.range e,
      ((c i : ℤ) : NumberField.RingOfIntegers K) * x ^ i := by
    rw [hgdef, hp]
    simp
  have hgx : v.intValuation (aeval x g) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [hgaeval]; exact happrox
  -- ## 3. division of the minimal polynomial by `g`
  set F : Polynomial ℤ := minpoly ℤ x with hFdef
  set H : Polynomial ℤ := F /ₘ g with hHdef
  set Rm : Polynomial ℤ := F %ₘ g with hRmdef
  have hdivide : Rm + g * H = F := modByMonic_add_div F g
  have hRmdeg : Rm.natDegree < e := by
    rcases eq_or_ne Rm 0 with h0 | h0
    · simp [h0, he0]
    · have h1 : Rm.degree < g.degree := degree_modByMonic_lt F hgmonic
      rw [hgdeg] at h1
      exact (natDegree_lt_iff_degree_lt h0).mpr h1
  have hFx : aeval x F = 0 := minpoly.aeval ℤ x
  have hRmx : v.intValuation (aeval x Rm) ≤ WithZero.exp (-(M : ℤ)) := by
    have h2 := congrArg (Polynomial.aeval x) hdivide
    rw [map_add, map_mul] at h2
    have h1 : aeval x Rm + aeval x g * aeval x H = 0 := h2.trans hFx
    have h3 : aeval x Rm = -(aeval x g * aeval x H) := by linear_combination h1
    rw [h3, Valuation.map_neg, map_mul]
    refine le_trans (mul_le_mul' hgx (v.intValuation_le_one _)) ?_
    rw [mul_one]
  have hRmsum : aeval x Rm = ∑ i ∈ Finset.range e,
      ((Rm.coeff i : ℤ) : NumberField.RingOfIntegers K) * x ^ i := by
    rw [aeval_eq_sum_range' hRmdeg]
    exact Finset.sum_congr rfl fun i _ => by rw [zsmul_eq_mul]
  have hRmcoeff : ∀ i, i < e →
      v.intValuation ((Rm.coeff i : NumberField.RingOfIntegers K) * x ^ i)
        ≤ WithZero.exp (-(M : ℤ)) := by
    intro i hi
    have h1 := valuation_term_le_valuation_sum v.intValuation hker
      (fun j => ((Rm.coeff j : ℤ) : NumberField.RingOfIntegers K) * x ^ j)
      (Finset.mem_range.mpr hi) (hpairwise (fun j => Rm.coeff j))
    rw [← hRmsum] at h1
    exact h1.trans hRmx
  -- ## 4. the shifted bound on the remainder's derivative
  have hshift : ∀ j : ℕ, j + 1 ≤ e →
      v.intValuation ((Rm.coeff (j + 1) : NumberField.RingOfIntegers K) * x ^ j)
        ≤ WithZero.exp (-(M : ℤ) + 1) := by
    intro j hj
    rcases eq_or_lt_of_le hj with hje | hje
    · have hzero : Rm.coeff (j + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hzero]
      simp
    · have hkey : v.intValuation ((Rm.coeff (j + 1) : NumberField.RingOfIntegers K) * x ^ j)
          * WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-(M : ℤ)) := by
        have h4 := hRmcoeff (j + 1) hje
        rw [pow_succ, ← mul_assoc, map_mul, hx] at h4
        exact h4
      have h5 := mul_le_mul_left hkey (WithZero.exp (1 : ℤ))
      rwa [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one,
        ← WithZero.exp_add] at h5
  have hRmderiv : v.intValuation (aeval x (derivative Rm)) ≤ WithZero.exp (-(M : ℤ) + 1) := by
    have hdnd : (derivative Rm).natDegree < e :=
      lt_of_le_of_lt (natDegree_derivative_le Rm) (by omega)
    rw [aeval_eq_sum_range' hdnd]
    refine Valuation.map_sum_le _ ?_
    intro i hi
    have hi' : i < e := Finset.mem_range.mp hi
    rw [zsmul_eq_mul, coeff_derivative]
    have hrw : (((Rm.coeff (i + 1) * ((i : ℤ) + 1) : ℤ)) : NumberField.RingOfIntegers K) * x ^ i
        = (((i : ℤ) + 1 : ℤ) : NumberField.RingOfIntegers K)
          * ((Rm.coeff (i + 1) : NumberField.RingOfIntegers K) * x ^ i) := by
      push_cast; ring
    rw [hrw, map_mul]
    refine le_trans (mul_le_mul' (v.intValuation_le_one _) (hshift i (by omega))) ?_
    rw [one_mul]
  -- ## 5. the extremal term of `g'(x)`
  have hgdnd : (derivative g).natDegree < e := by
    have h1 := natDegree_derivative_le g
    rw [hgnd] at h1
    omega
  have hgderivsum : aeval x (derivative g) = ∑ i ∈ Finset.range e,
      (((derivative g).coeff i : ℤ) : NumberField.RingOfIntegers K) * x ^ i := by
    rw [aeval_eq_sum_range' hgdnd]
    exact Finset.sum_congr rfl fun i _ => by rw [zsmul_eq_mul]
  have hlead : (derivative g).coeff (e - 1) = (e : ℤ) := by
    rw [coeff_derivative, show e - 1 + 1 = e from by omega, hgcoeff, one_mul]
    have hc : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    rw [hc]; ring
  have hextremal : WithZero.exp (-((e * e.factorization q : ℕ) : ℤ) - ((e : ℤ) - 1))
      ≤ v.intValuation (aeval x (derivative g)) := by
    have h1 := valuation_term_le_valuation_sum v.intValuation hker
      (fun i => (((derivative g).coeff i : ℤ) : NumberField.RingOfIntegers K) * x ^ i)
      (Finset.mem_range.mpr (show e - 1 < e by omega))
      (hpairwise (fun i => (derivative g).coeff i))
    rw [← hgderivsum] at h1
    refine le_trans (le_of_eq ?_) h1
    have hEcast : (((e : ℤ)) : NumberField.RingOfIntegers K)
        = ((e : ℕ) : NumberField.RingOfIntegers K) := by push_cast; ring
    rw [hlead, map_mul, hEcast, hnat e (by omega), hxpow, ← WithZero.exp_add]
    congr 1
    have hc : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    rw [hc]; ring
  -- ## 6. the cofactor `H` is a `Q`-unit
  have hxQ : x ∈ v.asIdeal := by
    have h1 := (v.intValuation_le_pow_iff_mem x 1).mp (by rw [hx]; simp)
    simpa using h1
  have hsumQ : (∑ i ∈ Finset.range e,
      ((c i : ℤ) : NumberField.RingOfIntegers K) * x ^ i) ∈ v.asIdeal := by
    have h1 : x ^ e - ∑ i ∈ Finset.range e,
        ((c i : ℤ) : NumberField.RingOfIntegers K) * x ^ i ∈ v.asIdeal := by
      have h2 := (v.intValuation_le_pow_iff_mem _ 1).mp
        (le_trans happrox (by rw [WithZero.exp_le_exp]; push_cast; omega))
      simpa using h2
    have h3 : x ^ e ∈ v.asIdeal := v.asIdeal.pow_mem_of_mem hxQ e he0
    have h4 := Ideal.sub_mem _ h3 h1
    simpa using h4
  have hc0Q : ((c 0 : ℤ) : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
    have hsplit : ∑ i ∈ Finset.range e, ((c i : ℤ) : NumberField.RingOfIntegers K) * x ^ i
        = (∑ i ∈ Finset.range (e - 1),
            ((c (i + 1) : ℤ) : NumberField.RingOfIntegers K) * x ^ (i + 1))
          + ((c 0 : ℤ) : NumberField.RingOfIntegers K) := by
      conv_lhs => rw [show e = (e - 1) + 1 from by omega]
      rw [Finset.sum_range_succ']
      simp
    have hQsum : (∑ i ∈ Finset.range (e - 1),
        ((c (i + 1) : ℤ) : NumberField.RingOfIntegers K) * x ^ (i + 1)) ∈ v.asIdeal :=
      Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (v.asIdeal.pow_mem_of_mem hxQ _ (by omega))
    have h5 := Ideal.sub_mem _ hsumQ hQsum
    rw [hsplit] at h5
    simpa using h5
  have hgc0val : v.intValuation ((c 0 : NumberField.RingOfIntegers K))
      ≤ WithZero.exp (-(e : ℤ)) := by
    rcases eq_or_ne (c 0) 0 with h0 | h0
    · rw [h0]; simp
    · obtain ⟨k, hk⟩ := hZval (c 0) h0
      rw [hk, WithZero.exp_le_exp]
      have hk1 : 1 ≤ k := by
        by_contra hcon
        have hk0 : k = 0 := by omega
        subst hk0
        rw [Nat.mul_zero] at hk
        simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero] at hk
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp hk) hc0Q
      have h2 : e ≤ e * k := by
        calc e = e * 1 := (mul_one e).symm
          _ ≤ e * k := Nat.mul_le_mul_left e hk1
      exact neg_le_neg (by exact_mod_cast h2)
  have hRm0 : v.intValuation ((Rm.coeff 0 : NumberField.RingOfIntegers K))
      ≤ WithZero.exp (-(M : ℤ)) := by
    have h1 := hRmcoeff 0 he0
    simpa using h1
  have hcoeff0 : F.coeff 0 = Rm.coeff 0 + g.coeff 0 * H.coeff 0 := by
    conv_lhs => rw [← hdivide]
    rw [coeff_add, mul_coeff_zero]
  have hgH0 : v.intValuation (((g.coeff 0 * H.coeff 0 : ℤ) : NumberField.RingOfIntegers K))
      = WithZero.exp (-(e : ℤ)) := by
    have h1 : ((g.coeff 0 * H.coeff 0 : ℤ) : NumberField.RingOfIntegers K)
        = ((F.coeff 0 : ℤ) : NumberField.RingOfIntegers K)
          - ((Rm.coeff 0 : ℤ) : NumberField.RingOfIntegers K) := by
      rw [hcoeff0]; push_cast; ring
    have hlt : v.intValuation ((Rm.coeff 0 : NumberField.RingOfIntegers K))
        < v.intValuation ((F.coeff 0 : NumberField.RingOfIntegers K)) := by
      rw [hc0]
      exact lt_of_le_of_lt hRm0 (by rw [WithZero.exp_lt_exp]; omega)
    rw [h1, Valuation.map_sub_eq_of_lt_left _ hlt, hc0]
  have hH0 : v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K)) = 1 := by
    have hmul : ((g.coeff 0 * H.coeff 0 : ℤ) : NumberField.RingOfIntegers K)
        = ((g.coeff 0 : ℤ) : NumberField.RingOfIntegers K)
          * ((H.coeff 0 : ℤ) : NumberField.RingOfIntegers K) := by push_cast; ring
    rw [hmul, map_mul] at hgH0
    have hg0le : v.intValuation ((g.coeff 0 : NumberField.RingOfIntegers K))
        ≤ WithZero.exp (-(e : ℤ)) := by
      rw [hgcoeff0, show (((-c 0 : ℤ)) : NumberField.RingOfIntegers K)
        = -((c 0 : ℤ) : NumberField.RingOfIntegers K) by push_cast; ring, Valuation.map_neg]
      exact hgc0val
    have h1 : WithZero.exp (-(e : ℤ))
        ≤ WithZero.exp (-(e : ℤ)) * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K)) := by
      calc WithZero.exp (-(e : ℤ))
            = v.intValuation ((g.coeff 0 : NumberField.RingOfIntegers K))
              * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K)) := hgH0.symm
        _ ≤ WithZero.exp (-(e : ℤ))
              * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K)) :=
            mul_le_mul_left hg0le _
    have h2 : WithZero.exp (-(e : ℤ))
        * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K))
        ≤ WithZero.exp (-(e : ℤ)) := by
      calc WithZero.exp (-(e : ℤ))
            * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K))
          ≤ WithZero.exp (-(e : ℤ)) * 1 := mul_le_mul_right (v.intValuation_le_one _) _
        _ = WithZero.exp (-(e : ℤ)) := mul_one _
    have h3 : WithZero.exp (-(e : ℤ))
        * v.intValuation ((H.coeff 0 : NumberField.RingOfIntegers K))
        = WithZero.exp (-(e : ℤ)) * 1 := by rw [mul_one]; exact le_antisymm h2 h1
    exact mul_left_cancel₀ (by simp) h3
  have hHx : v.intValuation (aeval x H) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro hcon
    have h4 : ((H.coeff 0 : ℤ) : NumberField.RingOfIntegers K)
        = aeval x H - x * aeval x H.divX := by
      have h2 := congrArg (Polynomial.aeval x) (X_mul_divX_add H)
      rw [map_add, map_mul, aeval_X, aeval_C] at h2
      rw [← h2]
      simp [algebraMap_int_eq]
    have h3 : ((H.coeff 0 : ℤ) : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      rw [h4]
      exact Ideal.sub_mem _ hcon (Ideal.mul_mem_right _ _ hxQ)
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp hH0) h3
  -- ## 7. mathlib's different bound, and the assembly
  have hdiffbound : v.intValuation (aeval x (derivative F)) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [v.intValuation_le_pow_iff_mem]
    refine Ideal.le_of_dvd hd ?_
    rw [hFdef]
    exact aeval_derivative_mem_differentIdeal ℤ ℚ K x hgen
  have hFderiv : derivative F = derivative Rm + (derivative g * H + g * derivative H) := by
    conv_lhs => rw [← hdivide]
    rw [derivative_add, derivative_mul]
  have hgderivH : v.intValuation (aeval x (derivative g) * aeval x H)
      ≤ WithZero.exp (-(d : ℤ)) := by
    have h2 := congrArg (Polynomial.aeval x) hFderiv
    rw [map_add, map_add, map_mul, map_mul] at h2
    have hsplit : aeval x (derivative g) * aeval x H
        = aeval x (derivative F) - aeval x (derivative Rm)
          - aeval x g * aeval x (derivative H) := by rw [h2]; ring
    rw [hsplit]
    have hb1 : v.intValuation (aeval x (derivative Rm)) ≤ WithZero.exp (-(d : ℤ)) :=
      hRmderiv.trans (by rw [WithZero.exp_le_exp]; omega)
    have hb2 : v.intValuation (aeval x g * aeval x (derivative H))
        ≤ WithZero.exp (-(d : ℤ)) := by
      rw [map_mul]
      refine le_trans (mul_le_mul' hgx (v.intValuation_le_one _)) ?_
      rw [mul_one, WithZero.exp_le_exp]
      omega
    exact Valuation.map_sub_le _ (Valuation.map_sub_le _ hdiffbound hb1) hb2
  have hgderivbound : v.intValuation (aeval x (derivative g)) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [map_mul, hHx, mul_one] at hgderivH
    exact hgderivH
  have hfinal := le_trans hextremal hgderivbound
  rw [WithZero.exp_le_exp] at hfinal
  obtain ⟨A, hA⟩ : ∃ A, e * e.factorization q = A := ⟨_, rfl⟩
  rw [hA] at hfinal ⊢
  omega

/-- **The wild different bound when the residue degree is one** (PROVEN
2026-07-26 over `differentIdeal_exponent_le_of_intEisenstein_approx`,
now the only remaining leaf of the elementary global route;
`exists_generator_uniformizer_at` was PROVEN 2026-07-26 over the three
steps `exists_uniformizer_avoiding_other_primes`,
`exists_generator_sub_mem_span_sq` and `intValuation_coeff_zero_minpoly`,
and the digit expansion `exists_intCoeff_eisenstein_approx` is proven
above).

Hypothesis `hres` says that every element of `𝓞_K` is congruent mod `Q`
to a rational integer, i.e. `𝓞_K/Q = 𝔽_q`, i.e. the residue degree
`f(Q∣q)` is `1`.  Conclusion: Serre's bound `d ≤ e − 1 + e·v_q(e)`.

**This case admits a completely ELEMENTARY GLOBAL proof — no local
fields, no completions, no `differentIdeal` localization theory.**  The
route was worked out and checked mathematically on 2026-07-26; it
eliminates (M1), (M2) and (M3) outright for `f = 1`, and it is the
recommended attack:

1. *Choose the generator.*  By approximation in `𝓞_K` pick `x` with
   `ord_Q x = 1` and `x ∉ Q'` for every other prime `Q'` above `q`;
   then correct it to a generator of `K/ℚ` by replacing `x` with
   `x + q^N·θ` for a primitive `θ` — the valuation conditions survive
   because `ord_Q (q^N θ) ≥ Ne ≥ 2 > 1` (note `e ≥ q ≥ 2` in the wild
   case) and `ord_{Q'} (q^N θ) ≥ 1 > 0`.  Some `N` works by pigeonhole:
   `K/ℚ` is finite separable, so `Finite (IntermediateField ℚ K)`
   (mathlib, `IntermediateField.finite_of_exists_primitive_element`),
   and if `x + q^{N₁}θ` and `x + q^{N₂}θ` lie in the SAME proper
   subfield `F` then `(q^{N₁} − q^{N₂})θ ∈ F`, so `θ ∈ F` and `F = K`.
2. *Eisenstein relation with INTEGER coefficients.*  Because `f = 1`,
   the digit expansion of `x^e` in the discrete valuation `ord_Q` can
   be taken with digits in `ℤ`: given `z` with `ord_Q z = k·e + r`
   (`r < e`), the element `q^k x^r` has the same order, so
   `z/(q^k x^r)` is a unit whose residue lies in `𝔽_q = ℤ/q`, and
   subtracting `c·q^k·x^r` for an integer `c` raises the order.  This
   yields, for every precision `M`, integers `c_0,…,c_{e−1}` with
   `ord_Q (x^e − ∑_{i<e} c_i x^i) ≥ M`; and `g := X^e − ∑ c_i X^i` is
   automatically *Eisenstein*, since `ord_Q (c_i x^i) = e·v_q(c_i) + i`
   are pairwise distinct mod `e`, so their minimum `e` is attained
   uniquely, forcing `v_q(c_0) = 1` and `v_q(c_i) ≥ 1`.
3. *mathlib supplies the different.*  `aeval_derivative_mem_differentIdeal`
   gives `𝔡_{𝓞_K/ℤ} ∣ (F'(x))` for `F = minpoly ℤ x` (no conductor
   hypothesis needed in this direction), hence `d ≤ ord_Q (F'(x))`.
4. *Divide.*  `F = g·H + R` in `ℤ[X]` (`g` monic).  From `F(x) = 0` and
   `ord_Q (g(x)) ≥ M` one gets `ord_Q (R(x)) ≥ M`; `R` has degree `< e`
   and integer coefficients, so the same distinct-residues argument
   forces `q^{⌈(M−e+1)/e⌉} ∣ R`.
5. *The other factor is a `Q`-unit.*  `F ≡ X^e·H̄ (mod q)` and
   `x ≡ 0 (mod Q)`, so `ord_Q H(x) = 0` iff `q ∤ H(0)`; and
   `v_q(F(0)) = v_q(N_{K/ℚ}(x)) = ∑_{Q'∣q} f_{Q'}·ord_{Q'}(x) = 1` by
   step 1 and `f = 1` (`Ideal.absNorm_span_singleton` plus
   multiplicativity of `absNorm`), while `v_q(g(0)) = 1`, so
   `v_q(H(0)) = 0`.
6. *Conclude.*  `F'(x) = g'(x)H(x) + g(x)H'(x) + R'(x)`; the last two
   terms have order `≥ M − e`, and `ord_Q (g'(x)) ≤ e·v_q(e) + e − 1`
   by `valuation_term_le_valuation_sum` exactly as in
   `differentIdeal_exponent_le_wild`.  Taking `M` large gives
   `d ≤ ord_Q (F'(x)) = ord_Q (g'(x)) ≤ e − 1 + e·v_q(e)`.

Both-ways audit: an inequality between natural numbers, the `f = 1`
instance of a classical theorem; no vacuity concerns (the hypothesis
`hres` is satisfied by e.g. `K = ℚ(√2)`, `q = 2`, where the bound is
sharp: `e = 2`, `v_2(2) = 1`, `d = 3 = 1 + 2`). -/
theorem differentIdeal_exponent_le_wild_of_residueDegreeOne
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hres : ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (d : ℕ) (hd : v.asIdeal ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ e - 1 + e * e.factorization q := by
  classical
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he0 : 0 < e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0)
  obtain ⟨x, hgen, hx, hc0⟩ := exists_generator_uniformizer_at K q hq v hmem hres e he
  have hp : v.intValuation (((q : ℤ) : NumberField.RingOfIntegers K))
      = WithZero.exp (-(e : ℤ)) := by
    have h1 := intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem q hq.ne_zero
    rw [hq.factorization_self, mul_one, ← he] at h1
    rw [show (((q : ℤ) : NumberField.RingOfIntegers K))
      = ((q : ℕ) : NumberField.RingOfIntegers K) by push_cast; ring]
    exact h1
  obtain ⟨c, hc⟩ := exists_intCoeff_eisenstein_approx v he0 hx hp hres (d + 2 * e + 2)
  exact differentIdeal_exponent_le_of_intEisenstein_approx K q hq v hmem e he x hgen hx hc0 c
    (d + 2 * e + 2) hc d le_rfl hd

/-- **`Q^{e·k} ∩ ℤ = (q^k)`** (PROVEN 2026-07-27).

The contraction to `ℤ` of the `Q`-primary ideal `Q^{e·k}` is exactly
`q^k·ℤ`.  Immediate from `intValuation_natCast_eq_exp_ramificationIdx`
above — `ord_Q(a) = e·v_q(|a|)` for a rational integer `a` — together
with `e > 0`: `a ∈ Q^{e·k}` iff `e·k ≤ e·v_q(|a|)` iff `k ≤ v_q(|a|)`
iff `q^k ∣ a`.  No hypothesis on `k` is needed (at `k = 0` both sides
are `⊤`).

**Why this ideal and not `Ideal.span {(q : ℤ)^k}` is what the two cuts
below are stated over.**  mathlib's only *global* instance putting a
`R ⧸ p`-algebra structure on a quotient `B ⧸ P` is
`Ideal.quotientAlgebra` (`Mathlib/RingTheory/Ideal/Quotient/Operations.lean:742`),
and it is indexed by `p = P.comap (algebraMap R B)` — the general
`Ideal.Quotient.algebraQuotientOfLEComap` (`:730`) is an `abbrev`, not
an instance, so writing the base as `ℤ ⧸ Ideal.span {(q:ℤ)^k}` would
force a `letI` into the *statements* of the cuts.  Stating them over
the contraction keeps every instance automatic; this lemma is the
bridge back to the span form that the consumer needs. -/
theorem comap_pow_ramificationIdx_eq_span
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ) :
    (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K))
      = Ideal.span {((q : ℤ)) ^ k} := by
  classical
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he0 : 0 < e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0)
  ext a
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  rw [show algebraMap ℤ (NumberField.RingOfIntegers K) a = (a : NumberField.RingOfIntegers K) from
    rfl, ← v.intValuation_le_pow_iff_mem]
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  · have hva : v.intValuation (a : NumberField.RingOfIntegers K)
        = v.intValuation ((a.natAbs : ℕ) : NumberField.RingOfIntegers K) := by
      rcases Int.natAbs_eq a with h | h
      · have hc : (a : NumberField.RingOfIntegers K)
            = (((a.natAbs : ℕ) : ℤ) : NumberField.RingOfIntegers K) :=
          congrArg (Int.cast : ℤ → NumberField.RingOfIntegers K) h
        rw [hc, Int.cast_natCast]
      · have hc : (a : NumberField.RingOfIntegers K)
            = ((-((a.natAbs : ℕ) : ℤ) : ℤ) : NumberField.RingOfIntegers K) :=
          congrArg (Int.cast : ℤ → NumberField.RingOfIntegers K) h
        rw [hc, Int.cast_neg, Int.cast_natCast]
        exact Valuation.map_neg _ _
    have hna : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
    rw [hva, intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem a.natAbs hna, ← he,
      WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le, Nat.mul_le_mul_left_iff he0,
      ← Nat.Prime.pow_dvd_iff_le_factorization hq hna,
      show ((q : ℤ)) ^ k = (((q ^ k : ℕ)) : ℤ) by push_cast; ring,
      ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]

open scoped _root_.TensorProduct in
/-- **Base change of the trace along `A ↠ A ⧸ I`** (PROVEN 2026-07-27),
for `B` free and finite over `A` and an ARBITRARY ideal `I` — no
maximality, no local hypothesis on `A`.

`Tr_{B/A}(y) mod I = Tr_{(B/IB)/(A/I)}(ȳ)`.

**This is the general form that `Algebra.trace_quotient_mk`
(`Mathlib/RingTheory/Trace/Quotient.lean:40`) is NOT.**  That lemma is
stated only for `p = IsLocalRing.maximalIdeal R`, because the quotient
basis it uses (`Module.basisQuotient`,
`Mathlib/RingTheory/LocalRing/Quotient.lean:85`) is built under
`attribute [local instance] Ideal.Quotient.field` and counts `finrank`
over a field.  Taking `R = ℤ/q^k` does NOT rescue it: `ℤ/q^k` is local,
but its maximal ideal is `(q)`, so the lemma reduces mod `q`, not mod
`q^k`.

The repair is much cheaper than rebuilding `basisQuotient`: mathlib
already has the algebra isomorphism
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`,
`B ⧸ I·B ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B`, under which left multiplication by
`ȳ` becomes the base change of left multiplication by `y`; then
`LinearMap.trace_baseChange` is exactly the statement. -/
theorem trace_quotient_map_of_free {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (I : Ideal A) (y : B) :
    Algebra.trace (A ⧸ I) (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk _ y)
      = Ideal.Quotient.mk I (Algebra.trace A B y) := by
  have hmul : (Algebra.lmul (A ⧸ I) ((A ⧸ I) ⊗[A] B) (1 ⊗ₜ[A] y) : _ →ₗ[A ⧸ I] _)
      = LinearMap.baseChange (A ⧸ I) (Algebra.lmul A B y) := by
    ext z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [← Algebra.trace_eq_of_algEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I) (Ideal.Quotient.mk _ y),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.trace_apply, hmul,
    LinearMap.trace_baseChange, Algebra.trace_apply, Ideal.Quotient.algebraMap_eq]

/-- **CRT, plus the trace of a product algebra at an element supported on
one factor** (PROVEN 2026-07-27).

If the extension `I·B` of the contraction `I = P ∩ A` factors as `P · Q`
with `P` and `Q` coprime, then for `x ∈ Q` the trace of `x` over `A`,
read mod `I`, is computed entirely in the single factor `B ⧸ P`.

`A ⧸ I` is required to be LOCAL, and that hypothesis is doing real work
here even though the conclusion never mentions it: `Algebra.trace_prod_apply`
needs both factors FREE over the base, and freeness of `B ⧸ P` is obtained
by `Module.free_of_flat_of_isLocalRing` from its being a direct summand
(hence projective, hence flat) of the free module `B ⧸ I·B`.  Over a
non-local base only projectivity would survive, and the trace of a
projective-but-not-free factor is not computed by
`Algebra.trace_prod_apply`. -/
theorem trace_quotient_of_coprime_factor {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B]
    (P Q : Ideal B) (hcop : IsCoprime P Q)
    [IsLocalRing (A ⧸ P.comap (algebraMap A B))]
    (hmap : (P.comap (algebraMap A B)).map (algebraMap A B) = P * Q)
    (x : B) (hx : x ∈ Q) :
    Ideal.Quotient.mk (P.comap (algebraMap A B)) (Algebra.trace A B x)
      = Algebra.trace (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) (Ideal.Quotient.mk P x) := by
  letI : Algebra (A ⧸ P.comap (algebraMap A B)) (B ⧸ Q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (by rw [hmap]; exact Ideal.mul_le_left))
  haveI : IsScalarTower A (A ⧸ P.comap (algebraMap A B)) (B ⧸ Q) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower A (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) := .of_algebraMap_eq' rfl
  letI ecrt : (B ⧸ (P.comap (algebraMap A B)).map (algebraMap A B))
      ≃ₐ[A ⧸ P.comap (algebraMap A B)] ((B ⧸ P) × (B ⧸ Q)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd P Q hcop)
      commutes' := Quotient.ind fun _ ↦ rfl }
  haveI : Module.Finite A (B ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A P).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite A (B ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A Q).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) :=
    Module.Finite.of_restrictScalars_finite A _ _
  haveI : Module.Finite (A ⧸ P.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A _ _
  haveI : Module.Free (A ⧸ P.comap (algebraMap A B))
      (B ⧸ (P.comap (algebraMap A B)).map (algebraMap A B)) :=
    Module.Free.of_equiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
        (P.comap (algebraMap A B))).symm.toLinearEquiv
  haveI : Module.Free (A ⧸ P.comap (algebraMap A B)) ((B ⧸ P) × (B ⧸ Q)) :=
    Module.Free.of_equiv ecrt.toLinearEquiv
  haveI : Module.Projective (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) :=
    Module.Projective.of_split
      (LinearMap.inl (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) (B ⧸ Q))
      (LinearMap.fst (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) (B ⧸ Q))
      (LinearMap.fst_comp_inl _ _ _)
  haveI : Module.Projective (A ⧸ P.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.Projective.of_split
      (LinearMap.inr (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) (B ⧸ Q))
      (LinearMap.snd (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) (B ⧸ Q))
      (LinearMap.snd_comp_inr _ _ _)
  haveI : Module.Free (A ⧸ P.comap (algebraMap A B)) (B ⧸ P) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (A ⧸ P.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.free_of_flat_of_isLocalRing
  have hex : ecrt (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk P x, 0) := by
    refine Prod.ext rfl ?_
    show Ideal.Quotient.mk Q x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  rw [← trace_quotient_map_of_free (P.comap (algebraMap A B)) x,
    ← Algebra.trace_eq_of_algEquiv ecrt (Ideal.Quotient.mk _ x), hex, Algebra.trace_prod_apply]
  simp

/-- `2 ≤ q^k` for `q` prime and `k ≥ 1`, in `ℤ`. -/
theorem two_le_intCast_pow_of_prime (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k) :
    (2 : ℤ) ≤ (q : ℤ) ^ k := by
  have h1 : 2 ≤ q ^ k := by
    calc 2 ≤ q := hq.two_le
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk
  exact_mod_cast h1

/-- `(q^k)` is a proper ideal of `ℤ` for `q` prime and `k ≥ 1`. -/
theorem span_intCast_pow_ne_top (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k) :
    (Ideal.span {(q : ℤ) ^ k} : Ideal ℤ) ≠ ⊤ := by
  have h2 := two_le_intCast_pow_of_prime q hq k hk
  rw [Ne, Ideal.span_singleton_eq_top, Int.isUnit_iff]
  omega

/-- **`ℤ/q^k` is a local ring** (PROVEN 2026-07-27), for `q` prime and
`k ≥ 1`.  Stated over an ideal `I` together with `I = (q^k)` rather than
over the span directly, so that a caller holding the contraction
`(Q^{e·k}) ∩ ℤ` in that form can install the instance for exactly the
type appearing in its goal, with no `Ideal.quotEquivOfEq` transport.

`k ≥ 1` is necessary and not cosmetic: at `k = 0` the ring is trivial,
and `IsLocalRing` demands `Nontrivial`. -/
theorem isLocalRing_int_quotient_of_eq_span (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : 0 < k)
    (I : Ideal ℤ) (hI : I = Ideal.span {(q : ℤ) ^ k}) : IsLocalRing (ℤ ⧸ I) := by
  subst hI
  haveI : Nontrivial (ℤ ⧸ Ideal.span {(q : ℤ) ^ k}) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_intCast_pow_ne_top q hq k hk)
  have hqk : ((q : ℤ) ^ k).natAbs = q ^ k := by simp
  -- an integer prime to `q` becomes a unit mod `q^k`
  have key : ∀ n : ℤ, ¬ ((q : ℤ) ∣ n) →
      IsUnit (Ideal.Quotient.mk (Ideal.span {(q : ℤ) ^ k}) n) := by
    intro n hn
    have hnd : ¬ q ∣ n.natAbs := by
      intro hc
      exact hn (Int.natAbs_dvd_natAbs.mp (by simpa using hc))
    have hcop : IsCoprime ((q : ℤ) ^ k) n := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, hqk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnd)
    obtain ⟨u, w, huw⟩ := hcop
    have hz : Ideal.Quotient.mk (Ideal.span {(q : ℤ) ^ k}) ((q : ℤ) ^ k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have hmul : Ideal.Quotient.mk (Ideal.span {(q : ℤ) ^ k}) n * Ideal.Quotient.mk _ w = 1 := by
      calc Ideal.Quotient.mk (Ideal.span {(q : ℤ) ^ k}) n * Ideal.Quotient.mk _ w
          = Ideal.Quotient.mk _ (u * (q : ℤ) ^ k + w * n) := by
            rw [map_add, map_mul, map_mul, hz, mul_zero, zero_add, mul_comm]
        _ = 1 := by rw [huw, map_one]
    exact isUnit_iff_exists.mpr ⟨_, hmul, by rw [mul_comm]; exact hmul⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_cases hn : (q : ℤ) ∣ n
  · right
    have hrw : (1 : ℤ ⧸ Ideal.span {(q : ℤ) ^ k}) - Ideal.Quotient.mk _ n
        = Ideal.Quotient.mk _ (1 - n) := by rw [map_sub, map_one]
    rw [hrw]
    refine key _ fun hc => ?_
    have hd1 : (q : ℤ) ∣ 1 := by
      have := dvd_add hc hn
      simpa using this
    have h1 : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos hd1
    have h2 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
    omega
  · exact Or.inl (key _ hn)

/-- **CUT 1 of the trace witness: base change to `ℤ/q^k`, then CRT**
(PROVEN 2026-07-27; cut 2026-07-27 out of
`exists_intTrace_not_mem_span_of_ramificationIdx` below, which is
PROVEN over this together with `exists_mem_cofactor_trace_quotient_ne_zero`).

For `x` in the cofactor `J` of `Q^{e·k}` in `q^k·𝓞_K`, the rational
integer `Tr_{K/ℚ}(x)`, reduced modulo `q^k`, is computed by the trace
of the image of `x` in the SINGLE finite ring `𝓞_K/Q^{e·k}` over
`ℤ/q^k`.

**This leaf carries no arithmetic — it is trace bookkeeping.**  The
three steps, and the mathlib input for each:

1. *Base change of the trace along `ℤ ↠ ℤ/q^k`* — `trace_quotient_map_of_free`
   above, proven for an ARBITRARY ideal of an arbitrary base.

   The route originally planned here (rebuild `Module.basisQuotient`
   without fields, out of `Algebra.TensorProduct.basis` and
   `TensorProduct.quotTensorEquivQuotSMul` upgraded by
   `LinearEquiv.extendScalarsOfSurjective`, then copy
   `Algebra.trace_quotient_mk`'s matrix proof) turned out to be
   unnecessary.  mathlib already carries the ALGEBRA isomorphism
   `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`
   (`Mathlib/RingTheory/TensorProduct/Quotient.lean:72`),
   `B ⧸ I·B ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B`; under it, multiplication by `x̄`
   IS the base change of multiplication by `x`, and
   `LinearMap.trace_baseChange` closes it.  Five lines, no basis.

   The note under `exists_intTrace_not_mem_span_of_ramificationIdx`
   below is CORRECT and stays: `Algebra.trace_quotient_mk` genuinely
   does not apply, and taking its base to be the local ring `ℤ/q^k`
   does not rescue it — the maximal ideal of `ℤ/q^k` is `(q)`, so that
   lemma reduces mod `q`, not mod `q^k`.

2. *CRT.*  `q^k·𝓞_K = Q^{e·k}·J` with `Q^{e·k}` and `J` COPRIME — `J`
   is prime to `Q` because `ord_Q(q^k) = e·k` exactly
   (`intValuation_natCast_eq_exp_ramificationIdx`), so `Q ∤ J` and, `Q`
   being maximal, `Q^{e·k} ⊔ J = ⊤`.  Hence
   `𝓞_K/q^k𝓞_K ≅ (𝓞_K/Q^{e·k}) × (𝓞_K/J)` as `ℤ/q^k`-algebras
   (`Ideal.quotientInfRingEquivPiQuotient`, or
   `Ideal.quotientMulEquivQuotientProd` for the two-factor case).

3. *The trace of a product algebra, at an element supported on one
   factor.*  Both factors are free over `ℤ/q^k` (direct summands of a
   free module over the artinian local ring `ℤ/q^k`), and
   `Tr_{(S×T)/Z}(s, t) = Tr_{S/Z}(s) + Tr_{T/Z}(t)` by taking the
   product basis (`Algebra.trace_eq_matrix_trace`, block-diagonal
   matrix).  For `x ∈ J` the second coordinate is `0`, so only the
   first term survives.  Transport along the CRT isomorphism with
   `Algebra.trace_eq_of_equiv_equiv` (used at
   `Mathlib/RingTheory/Trace/Quotient.lean:79`).

FAITHFULNESS: an equation between two elements of `ℤ/q^k`, both sides
genuinely defined; nothing here is vacuous.  The hypothesis `hx` is
load-bearing (step 3), and so is `hJ` (steps 2 and 3). -/
theorem trace_quotient_pow_eq_of_mem_cofactor
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ)
    (J : Ideal (NumberField.RingOfIntegers K))
    (hJ : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
      = v.asIdeal ^ (e * k) * J)
    (x : NumberField.RingOfIntegers K) (hx : x ∈ J) :
    Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))
        (Algebra.trace ℤ (NumberField.RingOfIntegers K) x)
      = Algebra.trace
          (ℤ ⧸ (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
          (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
          (Ideal.Quotient.mk _ x) := by
  classical
  have hIspan : ∀ m : ℕ, ((v.asIdeal ^ (e * m)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) = Ideal.span {(q : ℤ) ^ m} :=
    fun m => comap_pow_ramificationIdx_eq_span K q hq v hmem e he m
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the base ring is `ℤ ⧸ ⊤`, which is trivial, so both sides agree
    haveI : Subsingleton (ℤ ⧸ (v.asIdeal ^ (e * 0)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K))) := by
      rw [Ideal.Quotient.subsingleton_iff, hIspan 0]
      simp
    exact Subsingleton.elim _ _
  -- from here on `k ≥ 1`
  haveI hloc : IsLocalRing (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) :=
    isLocalRing_int_quotient_of_eq_span q hq k hk _ (hIspan k)
  -- the extension of the contraction back to `𝓞_K` is `q^k·𝓞_K = Q^{e·k}·J`
  have hmap : ((v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K))).map
        (algebraMap ℤ (NumberField.RingOfIntegers K))
      = v.asIdeal ^ (e * k) * J := by
    rw [hIspan k, Ideal.map_span, ← hJ]
    norm_num
  -- `J` is prime to `Q`, because `ord_Q(q^k)` is EXACTLY `e·k`
  have hnotle : ¬ (J ≤ v.asIdeal) := by
    intro hle
    have h1 : (q : NumberField.RingOfIntegers K) ^ k ∈ v.asIdeal ^ (e * k + 1) := by
      have hle' : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
          ≤ v.asIdeal ^ (e * k + 1) := by
        rw [hJ, pow_succ]
        exact Ideal.mul_mono_right hle
      exact hle' (Ideal.mem_span_singleton_self _)
    -- raise to the `e`-th power so the exponent becomes a multiple of `e`
    -- and `comap_pow_ramificationIdx_eq_span` applies
    have h2 : ((q : NumberField.RingOfIntegers K) ^ k) ^ e ∈ v.asIdeal ^ (e * (k * e + 1)) := by
      have := Ideal.pow_mem_pow h1 e
      rwa [← pow_mul, show (e * k + 1) * e = e * (k * e + 1) by ring] at this
    have h3 : (q : ℤ) ^ (k * e) ∈ Ideal.span {(q : ℤ) ^ (k * e + 1)} := by
      rw [← hIspan (k * e + 1), Ideal.mem_comap,
        show algebraMap ℤ (NumberField.RingOfIntegers K) ((q : ℤ) ^ (k * e))
          = ((q : NumberField.RingOfIntegers K) ^ k) ^ e by push_cast [← pow_mul]; ring]
      exact h2
    rw [Ideal.mem_span_singleton] at h3
    have h5 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
    have h6 : (0 : ℤ) < (q : ℤ) ^ (k * e) := pow_pos (by omega) _
    have h4 : (q : ℤ) ^ (k * e + 1) ≤ (q : ℤ) ^ (k * e) := Int.le_of_dvd h6 h3
    rw [pow_succ] at h4
    nlinarith
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hsup : v.asIdeal ⊔ J = ⊤ := by
    by_contra hne
    exact hnotle (le_trans le_sup_right (hmax.eq_of_le hne le_sup_left).ge)
  have hcop : IsCoprime (v.asIdeal ^ (e * k)) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  exact trace_quotient_of_coprime_factor (A := ℤ) (B := NumberField.RingOfIntegers K)
    (v.asIdeal ^ (e * k)) J hcop hmap x hx

/-- **`Q^{e·k}` and its cofactor `J` are comaximal** (PROVEN 2026-07-27).

`q^k·𝓞_K = Q^{e·k}·J` forces `Q ∤ J`: otherwise `J ≤ Q`, so
`(q^k) ≤ Q^{e·k}·Q = Q^{e·k+1}`, contradicting `ord_Q(q^k) = e·k`
exactly (`intValuation_natCast_eq_exp_ramificationIdx`).  `Q` being
maximal, `Q ∤ J` is `Q^{e·k} ⊔ J = ⊤`.

This is what makes the reduction map `J → 𝓞_K/Q^{e·k}` SURJECTIVE — the
step that pulls a witness produced inside the finite ring back into the
cofactor in `exists_mem_cofactor_trace_quotient_ne_zero` below, and the
step 2/step 6 assertion that both cuts' docstrings appeal to.

No hypothesis on `k` is needed: at `k = 0` the factorization reads
`⊤ = ⊤ · J`, so `J = ⊤` and the sup is `⊤` anyway. -/
theorem sup_pow_ramificationIdx_cofactor_eq_top
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ)
    (J : Ideal (NumberField.RingOfIntegers K))
    (hJ : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
      = v.asIdeal ^ (e * k) * J) :
    v.asIdeal ^ (e * k) ⊔ J = ⊤ := by
  classical
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI : M.IsPrime := hM.isPrime
  have hvM : v.asIdeal ≤ M := Ideal.IsPrime.le_of_pow_le (le_trans le_sup_left hle)
  haveI hQmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hMv : M = v.asIdeal := ((hQmax.eq_of_le hM.ne_top hvM)).symm
  have hJv : J ≤ v.asIdeal := hMv ▸ le_trans le_sup_right hle
  have hmemq : (q : NumberField.RingOfIntegers K) ^ k ∈ v.asIdeal ^ (e * k + 1) := by
    have h1 : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
        ≤ v.asIdeal ^ (e * k + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono le_rfl hJv
    exact h1 (Ideal.mem_span_singleton_self _)
  rw [← v.intValuation_le_pow_iff_mem] at hmemq
  rw [show (q : NumberField.RingOfIntegers K) ^ k
      = ((q ^ k : ℕ) : NumberField.RingOfIntegers K) by push_cast; ring,
    intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem (q ^ k)
      (pow_ne_zero k hq.ne_zero), ← he] at hmemq
  rw [Nat.Prime.factorization_pow hq, Finsupp.single_eq_same, WithZero.exp_le_exp] at hmemq
  omega

attribute [local instance] Ideal.Quotient.field in
/-- **A finite free algebra over a LOCAL ring whose residual trace is
surjective has an element of unit trace** (PROVEN 2026-07-27).

Steps 5→6 of the wild-different argument, isolated from everything
arithmetic and stated for arbitrary `Zb`, `A` because nothing in it is
about number fields.

If `A` is finite free over the local ring `Zb` and
`Tr_{(A/𝔪A)/(Zb/𝔪)}` is surjective, pick `ā` of residual trace `1`.
`Algebra.trace_quotient_mk` says the residual trace is the reduction of
`Tr_{A/Zb}`, so any lift `a` has `Tr_{A/Zb}(a) ∉ 𝔪`, i.e.
`Tr_{A/Zb}(a)` is a unit of `Zb`.

**Why `trace_quotient_mk` is legitimate HERE and not one step earlier.**
It is stated only for `p = IsLocalRing.maximalIdeal R`, and this
statement quantifies over exactly that ideal — so at `Zb = ℤ/q^k` it
reduces mod `𝔪 = (q)`, which is the residue-field computation wanted.
It is NOT a route to the mod-`q^k` reduction of cut 1: locality of the
base does not make it apply to a non-maximal ideal, and a note claiming
otherwise was wrong.  Cut 1's passage `ℤ → ℤ/q^k` is closed instead by
`trace_quotient_map_of_free` above, via
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and
`LinearMap.trace_baseChange`, for an arbitrary ideal and with no basis.

This is exactly the half of the old step 5 that is NOT about the
construction of the unramified subring, and separating it is what
leaves `exists_unramifiedSubalgebra_finrank_eq_isUnit_trace` below with
purely constructive content. -/
theorem exists_isUnit_trace_of_residualTrace_surjective
    (Zb A : Type*) [CommRing Zb] [IsLocalRing Zb] [CommRing A] [Algebra Zb A]
    [Module.Free Zb A] [Module.Finite Zb A]
    (hsurj : Function.Surjective (Algebra.trace (Zb ⧸ IsLocalRing.maximalIdeal Zb)
      (A ⧸ Ideal.map (algebraMap Zb A) (IsLocalRing.maximalIdeal Zb)))) :
    ∃ a : A, IsUnit (Algebra.trace Zb A a) := by
  classical
  obtain ⟨y, hy⟩ := hsurj 1
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  rw [Algebra.trace_quotient_mk] at hy
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at hy
  exact zero_ne_one hy

/-- **The `q`-part of `Q^{e·k}` is `Q^e`: `(q) ⊔ Q^{e·k} = Q^e`** (PROVEN
2026-07-27).

Equivalently `𝓞_K/Q^{e·k}` modulo `q` is `𝓞_K/Q^e`, which is the one piece of
Dedekind-domain arithmetic the finite-ring core below needs: it is what pins
the residual dimension of `S/qS` — and hence `finrank_A S` — to `e`.

Proof: `v_Q(q) = e` exactly (`intValuation_natCast_eq_exp_ramificationIdx`
above, with `q.factorization q = 1`), so `q ∈ Q^e \ Q^{e+1}` and mathlib's
`Ideal.eq_prime_pow_of_succ_lt_of_le` gives the base case
`(q) ⊔ Q^{e+1} = Q^e`.  Multiplying that identity by `Q^m` and using
`Q^m · (q) ≤ (q)` pushes the exponent down one step at a time, giving
`Q^e ≤ (q) ⊔ Q^{e+m}` for every `m`; take `m = e·k − e ≥ 0`.  No hypothesis
beyond `k ≠ 0` is needed. -/
theorem span_sup_pow_ramificationIdx_eq_pow
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ) (hk : k ≠ 0) :
    Ideal.span {(q : NumberField.RingOfIntegers K)} ⊔ v.asIdeal ^ (e * k)
      = v.asIdeal ^ e := by
  classical
  set R := NumberField.RingOfIntegers K with hR
  set Q := v.asIdeal with hQdef
  haveI hQp : Q.IsPrime := v.isPrime
  have hQ0 : Q ≠ ⊥ := v.ne_bot
  have hval : v.intValuation ((q : ℕ) : R) = WithZero.exp (-(e : ℤ)) := by
    rw [intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem q hq.ne_zero, ← he]
    congr 2
    simp [hq.factorization_self]
  have hmemQe : (q : R) ∈ Q ^ e := by
    rw [← v.intValuation_le_pow_iff_mem, hval]
  have hnotmem : (q : R) ∉ Q ^ (e + 1) := by
    rw [← v.intValuation_le_pow_iff_mem, hval, WithZero.exp_le_exp]
    push_cast
    omega
  have hspanle : Ideal.span {(q : R)} ≤ Q ^ e :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmemQe)
  have hbase : Ideal.span {(q : R)} ⊔ Q ^ (e + 1) = Q ^ e := by
    refine Ideal.eq_prime_pow_of_succ_lt_of_le hQ0 (lt_of_le_of_ne le_sup_right ?_)
      (sup_le hspanle (Ideal.pow_succ_lt_pow hQ0 e).le)
    intro hcon
    exact hnotmem (hcon ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have key : ∀ m : ℕ, Q ^ e ≤ Ideal.span {(q : R)} ⊔ Q ^ (e + m) := by
    intro m
    induction m with
    | zero => rw [Nat.add_zero]; exact le_sup_right
    | succ m ih =>
      refine ih.trans (sup_le le_sup_left ?_)
      calc Q ^ (e + m) = Q ^ m * Q ^ e := by rw [← pow_add, Nat.add_comm]
        _ = Q ^ m * (Ideal.span {(q : R)} ⊔ Q ^ (e + 1)) := by rw [hbase]
        _ = Q ^ m * Ideal.span {(q : R)} ⊔ Q ^ m * Q ^ (e + 1) := Ideal.mul_sup _ _ _
        _ ≤ Ideal.span {(q : R)} ⊔ Q ^ (e + (m + 1)) := by
            refine sup_le_sup Ideal.mul_le_left ?_
            rw [← pow_add]
            exact Ideal.pow_le_pow_right (by omega)
  refine le_antisymm (sup_le hspanle (Ideal.pow_le_pow_right ?_)) ?_
  · exact Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hk)
  · have h := key (e * k - e)
    rwa [show e + (e * k - e) = e * k from by
      have : e ≤ e * k := Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hk)
      omega] at h

/-- **`R ⧸ Q^n` is a local ring when `Q` is maximal and `n ≠ 0`** (PROVEN
2026-07-27).

The nonunits are exactly the classes of elements of `Q`
(`Ideal.Quotient.isUnit_mk_pow_iff_notMem`), and those are closed under
addition, so `IsLocalRing.of_nonunits_add` applies.  Mathlib has no instance
for this. -/
theorem isLocalRing_quotient_pow_of_isMaximal {R : Type*} [CommRing R] (Q : Ideal R)
    [hQ : Q.IsMaximal] (n : ℕ) (hn : n ≠ 0) : IsLocalRing (R ⧸ Q ^ n) := by
  haveI : Nontrivial (R ⧸ Q ^ n) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    intro htop
    exact hQ.ne_top (top_le_iff.mp (htop ▸ Ideal.pow_le_self hn))
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [mem_nonunits_iff, Ideal.Quotient.isUnit_mk_pow_iff_notMem Q hn, not_not] at hx hy
  rw [← map_add, mem_nonunits_iff, Ideal.Quotient.isUnit_mk_pow_iff_notMem Q hn, not_not]
  exact Ideal.add_mem _ hx hy

/-- **The maximal ideal of `R ⧸ Q^n` is the image of `Q`** (PROVEN
2026-07-27).  `Q` is maximal and contains `ker (mk (Q^n)) = Q^n`, so its image
is maximal, hence *the* maximal ideal. -/
theorem maximalIdeal_quotient_pow_eq_map {R : Type*} [CommRing R] (Q : Ideal R)
    [hQ : Q.IsMaximal] (n : ℕ) (hn : n ≠ 0) [IsLocalRing (R ⧸ Q ^ n)] :
    IsLocalRing.maximalIdeal (R ⧸ Q ^ n) = Ideal.map (Ideal.Quotient.mk (Q ^ n)) Q := by
  refine (IsLocalRing.eq_maximalIdeal ?_).symm
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_self hn

/-- **The maximal ideal of `ℤ/q^k` is `(q)`** (PROVEN 2026-07-27).  Stated over
an ideal plus a proof that it IS `(q^k)`, matching
`isLocalRing_int_quotient_of_eq_span` above, so that it applies directly to the
contraction `(Q^{e·k}) ∩ ℤ` with no `Ideal.quotEquivOfEq` transport. -/
theorem maximalIdeal_int_quotient_pow_eq_span (q : ℕ) (hq : q.Prime) (k : ℕ) (hk : k ≠ 0)
    (I : Ideal ℤ) (hI : I = Ideal.span {(q : ℤ) ^ k}) [IsLocalRing (ℤ ⧸ I)] :
    IsLocalRing.maximalIdeal (ℤ ⧸ I) = Ideal.span {Ideal.Quotient.mk I ((q : ℕ) : ℤ)} := by
  haveI hqp : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hmax : (Ideal.span {((q : ℕ) : ℤ)}).IsMaximal := by
    refine (Ideal.span_singleton_prime ?_).mpr hqp |>.isMaximal ?_
    · exact_mod_cast hq.ne_zero
    · simpa [Ideal.span_singleton_eq_bot] using (by exact_mod_cast hq.ne_zero : ((q : ℕ) : ℤ) ≠ 0)
  refine (IsLocalRing.eq_maximalIdeal ?_).symm
  have hmapspan : Ideal.map (Ideal.Quotient.mk I) (Ideal.span {((q : ℕ) : ℤ)})
      = Ideal.span {Ideal.Quotient.mk I ((q : ℕ) : ℤ)} := by
    rw [Ideal.map_span]; simp
  rw [← hmapspan]
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
  rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
  exact dvd_pow_self _ hk

section FiniteLocalRingCore

open _root_.IsLocalRing _root_.Polynomial

/-- `|Fin n → R| = |R| ^ n`. -/
theorem natCard_fun_fin (R : Type*) [Finite R] (n : ℕ) :
    Nat.card (Fin n → R) = Nat.card R ^ n := by
  simp [Nat.card_pi]

/-- `Nat.card` form of `Module.card_eq_pow_finrank`. -/
theorem natCard_eq_pow_finrank (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [Finite K]
    [Finite V] : Nat.card V = Nat.card K ^ Module.finrank K V := by
  haveI := Fintype.ofFinite K
  haveI := Fintype.ofFinite V
  simpa [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K := K) (V := V)

/-- A module spanned by `n` elements over a finite ring has at most `|R| ^ n` elements. -/
theorem card_le_pow_of_span_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite R] {n : ℕ} (g : Fin n → M) (hspan : Submodule.span R (Set.range g) = ⊤) :
    Nat.card M ≤ Nat.card R ^ n := by
  classical
  have hsurj : Function.Surjective (fun c : Fin n → R => ∑ i, c i • g i) := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range g) := by rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun R).mp hy
  simpa [natCard_fun_fin] using Nat.card_le_card_of_surjective _ hsurj

/-- **Equality of cardinalities upgrades a spanning family of `n` elements to a basis.**
The surjection `R ^ n ↠ M` it gives is a bijection between finite sets of equal size, hence
an isomorphism.  This is what converts the counting argument below into freeness. -/
theorem free_finrank_of_span_of_card_eq {R M : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Finite R] {n : ℕ} (g : Fin n → M)
    (hspan : Submodule.span R (Set.range g) = ⊤) (hcard : Nat.card M = Nat.card R ^ n) :
    Module.Free R M ∧ Module.Finite R M ∧ Module.finrank R M = n := by
  classical
  have hsurj : Function.Surjective (Fintype.linearCombination R g) := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range g) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    exact ⟨c, by simpa [Fintype.linearCombination_apply] using hc⟩
  have hbij : Function.Bijective (Fintype.linearCombination R g) :=
    (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by rw [natCard_fun_fin, hcard]⟩
  let e : (Fin n → R) ≃ₗ[R] M := LinearEquiv.ofBijective _ hbij
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e,
    by rw [← e.finrank_eq, Module.finrank_fin_fun]⟩

/-- **Minimal generators over a finite local ring** (Nakayama).  A finite module `M` over a
finite local ring `R` is spanned by `n` elements, where `|M ⧸ 𝔪 M| = |κ| ^ n`; i.e. `n` is the
`κ`-dimension of `M ⧸ 𝔪 M`.  Uses mathlib's `IsLocalRing.map_mkQ_eq_top`. -/
theorem exists_span_eq_top_card_quot_eq_pow (R M : Type*) [CommRing R] [IsLocalRing R] [Finite R]
    [AddCommGroup M] [Module R M] [Finite M] :
    ∃ (n : ℕ) (g : Fin n → M), Submodule.span R (Set.range g) = ⊤ ∧
      Nat.card (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) = Nat.card (ResidueField R) ^ n := by
  classical
  letI : Module (ResidueField R) (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M)))
  letI : IsScalarTower R (ResidueField R) (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (M ⧸ maximalIdeal R • (⊤ : Submodule R M)))
  haveI : Finite (ResidueField R) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (M ⧸ (maximalIdeal R • ⊤ : Submodule R M)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective (maximalIdeal R • ⊤))
  set V := M ⧸ (maximalIdeal R • ⊤ : Submodule R M) with hV
  set n := Module.finrank (ResidueField R) V with hn
  let b := Module.finBasis (ResidueField R) V
  let g : Fin n → M := fun i => Function.surjInv
    (Submodule.Quotient.mk_surjective (maximalIdeal R • ⊤ : Submodule R M)) (b i)
  have hgb : ∀ i, (Submodule.mkQ (maximalIdeal R • ⊤ : Submodule R M)) (g i) = b i := fun i =>
    Function.surjInv_eq _ _
  refine ⟨n, g, ?_, ?_⟩
  · rw [← IsLocalRing.map_mkQ_eq_top]
    rw [Submodule.map_span, ← Set.range_comp]
    have hcomp : ((Submodule.mkQ (maximalIdeal R • ⊤ : Submodule R M)) ∘ g) = ⇑b := by
      funext i; exact hgb i
    rw [hcomp, ← Submodule.restrictScalars_span R (ResidueField R) Ideal.Quotient.mk_surjective,
      b.span_eq]
    exact Submodule.restrictScalars_top R (ResidueField R) V
  · exact natCard_eq_pow_finrank (ResidueField R) V

/-- **A ring is adically complete for a nilpotent ideal.**  `I ^ N = 0` makes the `I`-adic
filtration eventually `⊥`, so `IsHausdorff` and `IsPrecomplete` are immediate.  Composed with
`IsAdicComplete.henselianRing` this is what makes a finite local ring Henselian without any
completeness hypothesis. -/
theorem isAdicComplete_of_isNilpotent {R : Type*} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) : IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  have hbot : ∀ m : ℕ, N ≤ m → (I ^ m • (⊤ : Submodule R R)) = ⊥ := by
    intro m hm
    have h1 : I ^ m ≤ I ^ N := Ideal.pow_le_pow_right hm
    rw [hN, Ideal.zero_eq_bot] at h1
    rw [le_bot_iff.mp h1, Submodule.bot_smul]
  haveI hh : IsHausdorff I R := by
    constructor
    intro x hx
    have h1 := hx N
    rw [hbot N le_rfl] at h1
    simpa using SModEq.sub_mem.mp h1
  haveI hp : IsPrecomplete I R := by
    constructor
    intro g hg
    refine ⟨g N, fun n => ?_⟩
    rcases le_or_gt n N with hn | hn
    · exact hg hn
    · have h1 := hg hn.le
      rw [hbot N le_rfl] at h1
      have h2 : g N = g n := by simpa [sub_eq_zero] using SModEq.sub_mem.mp h1
      rw [h2]
  exact ⟨⟩

variable {Z S : Type*} [CommRing Z] [CommRing S] [Algebra Z S]

/-- In a subalgebra of a **finite** ring, being a unit is detected in the ambient ring: if
`x ∈ A` is a unit of `S` then multiplication by `x` is injective on the finite set `A`, hence
surjective, so `x` already has an inverse inside `A`. -/
theorem isUnit_subalgebra_iff [Finite S] (A : Subalgebra Z S) (x : A) :
    IsUnit x ↔ IsUnit (x : S) := by
  constructor
  · exact fun hx => hx.map (A.val : A →+* S)
  · intro hx
    haveI : Finite A := Subtype.finite
    have hinj : Function.Injective (fun y : A => x * y) := by
      intro y z hyz
      have h1 : (x : S) * (y : S) = (x : S) * (z : S) := by
        exact_mod_cast congrArg (fun w : A => (w : S)) hyz
      exact Subtype.ext (hx.mul_right_injective h1)
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) 1
    exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

/-- **A subalgebra of a finite local ring is local**, with maximal ideal the contraction of
`𝔪_S` (see `isUnit_subalgebra_iff`).  No nilpotence is needed. -/
theorem isLocalRing_subalgebra [IsLocalRing S] [Finite S] (A : Subalgebra Z S) :
    IsLocalRing A := by
  haveI : Nontrivial A := inferInstance
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_subalgebra_iff] at ha hb ⊢
  have ha' : (a : S) ∈ maximalIdeal S := (mem_maximalIdeal _).mpr ha
  have hb' : (b : S) ∈ maximalIdeal S := (mem_maximalIdeal _).mpr hb
  have : ((a + b : A) : S) ∈ maximalIdeal S := by
    push_cast
    exact Ideal.add_mem _ ha' hb'
  exact (mem_maximalIdeal _).mp this

/-- If `ω` is a root of a monic polynomial of degree `d`, then `R[ω]` is spanned as an
`R`-module by `1, ω, …, ω ^ (d - 1)` (divide by the monic polynomial). -/
theorem adjoin_singleton_le_span_pow {R M : Type*} [CommRing R] [CommRing M] [Algebra R M]
    [Nontrivial R] {ω : M} {h : R[X]} (hm : h.Monic) (hroot : aeval ω h = 0) :
    Subalgebra.toSubmodule (Algebra.adjoin R {ω})
      ≤ Submodule.span R (Set.range fun i : Fin h.natDegree => ω ^ (i : ℕ)) := by
  rintro y hy
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := hy
  refine PowerBasis.mem_span_pow'.mpr ⟨p %ₘ h, ?_, ?_⟩
  · exact (degree_modByMonic_lt _ hm).trans_le degree_le_natDegree
  · conv_lhs => rw [← modByMonic_add_div p h]
    simp [hroot]

/-- **The Henselian lift of a residue-field generator** (PROVEN 2026-07-28).

`κ_S / κ_Z` is an extension of finite fields, hence separable, so it has a primitive element
`ω̄` whose minimal polynomial `μ` has degree `f = [κ_S : κ_Z]` and is separable.  Lift `μ` to a
monic `h ∈ Z[X]` of the same degree (`Polynomial.lifts_and_degree_eq_and_monic` along the
surjection `Z ↠ κ_Z`) and lift `ω̄` to any `ω₀ ∈ S`.  Then `h(ω₀) ∈ 𝔪_S` and `h'(ω₀)` is a unit,
and `S` is Henselian at `𝔪_S` because `𝔪_S` is nilpotent
(`isAdicComplete_of_isNilpotent` + `IsAdicComplete.henselianRing`), so Newton iteration produces
`ω ∈ S` with `h(ω) = 0` and `ω ≡ ω₀`.

The subalgebra is `A = Z[ω]`, spanned over `Z` by `1, ω, …, ω ^ (f - 1)`
(`adjoin_singleton_le_span_pow`), and `A ↠ κ_S` because the image is a subring containing the
image of `κ_Z` and `ω̄`, which generate `κ_S`. -/
theorem exists_subalgebra_span_pow_residue_surjective
    (Z S : Type*) [CommRing Z] [CommRing S] [Algebra Z S]
    [IsLocalRing Z] [IsLocalRing S] [Finite Z] [Finite S]
    [IsLocalHom (algebraMap Z S)]
    (hnil : IsNilpotent (maximalIdeal S)) :
    ∃ (A : Subalgebra Z S)
      (g : Fin (Module.finrank (ResidueField Z) (ResidueField S)) → A),
      Submodule.span Z (Set.range g) = ⊤ ∧
      ∀ x : ResidueField S, ∃ a : A, residue S (a : S) = x := by
  classical
  haveI : Finite (ResidueField Z) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (ResidueField S) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : FiniteDimensional (ResidueField Z) (ResidueField S) := Module.Finite.of_finite
  haveI : PerfectField (ResidueField Z) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (ResidueField Z) (ResidueField S) := inferInstance
  obtain ⟨wbar, hwbar⟩ := Field.exists_primitive_element (ResidueField Z) (ResidueField S)
  have hint : IsIntegral (ResidueField Z) wbar := Algebra.IsIntegral.isIntegral wbar
  set μ := minpoly (ResidueField Z) wbar with hμdef
  have hμmonic : μ.Monic := minpoly.monic hint
  have hμdeg : μ.natDegree = Module.finrank (ResidueField Z) (ResidueField S) := by
    rw [← IntermediateField.adjoin.finrank hint, hwbar]
    exact IntermediateField.finrank_top'
  have hμsep : μ.Separable := Algebra.IsSeparable.isSeparable _ wbar
  have hμaeval : aeval wbar μ = 0 := minpoly.aeval _ _
  obtain ⟨hp, hpmap, hpdeg, hpmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (f := residue Z) (p := μ)
    ((Polynomial.lifts_iff_coeff_lifts μ).mpr fun n => residue_surjective (μ.coeff n)) hμmonic
  have hpnat : hp.natDegree = Module.finrank (ResidueField Z) (ResidueField S) := by
    rw [natDegree_eq_of_degree_eq hpdeg, hμdeg]
  obtain ⟨w₀, hw₀⟩ := residue_surjective (R := S) wbar
  haveI : IsAdicComplete (maximalIdeal S) S := isAdicComplete_of_isNilpotent hnil
  haveI : HenselianRing S (maximalIdeal S) := IsAdicComplete.henselianRing S _
  set H := hp.map (algebraMap Z S) with hHdef
  have hHmonic : H.Monic := hpmonic.map _
  have hcomp : ((residue S).comp (algebraMap Z S))
      = (algebraMap (ResidueField Z) (ResidueField S)).comp (residue Z) := by
    ext z; rfl
  have key : ∀ q : Z[X], residue S ((q.map (algebraMap Z S)).eval w₀)
      = aeval wbar (q.map (residue Z)) := by
    intro q
    rw [← Polynomial.eval₂_at_apply (residue S) w₀, ← Polynomial.eval_map, Polynomial.map_map,
      hcomp, hw₀, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map]
  have hHeval : H.eval w₀ ∈ maximalIdeal S := by
    have h1 : residue S (H.eval w₀) = 0 := by
      rw [hHdef, key hp, hpmap]; exact hμaeval
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h1
  have hHderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal S) ((derivative H).eval w₀)) := by
    have h1 : residue S ((derivative H).eval w₀) = aeval wbar (derivative μ) := by
      rw [hHdef, Polynomial.derivative_map, key (derivative hp), ← Polynomial.derivative_map, hpmap]
    show IsUnit (residue S ((derivative H).eval w₀))
    rw [h1]
    exact (hμsep.aeval_derivative_ne_zero hμaeval).isUnit
  obtain ⟨w, hwroot, hwmem⟩ := HenselianRing.is_henselian H hHmonic w₀ hHeval hHderiv
  have hresw : residue S w = wbar := by
    have h1 : residue S (w - w₀) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hwmem
    rw [map_sub, sub_eq_zero] at h1
    rw [h1, hw₀]
  have hroot : aeval w hp = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hHdef]
    exact hwroot
  set A : Subalgebra Z S := Algebra.adjoin Z {w} with hAdef
  have hwA : w ∈ A := Algebra.self_mem_adjoin_singleton Z w
  refine ⟨A, fun i => ⟨w ^ (i : ℕ), A.pow_mem hwA _⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hspanS : y ∈ Submodule.span Z
        (Set.range fun i : Fin (Module.finrank (ResidueField Z) (ResidueField S)) =>
          w ^ (i : ℕ)) := by
      have h1 := adjoin_singleton_le_span_pow hpmonic hroot hy
      rwa [hpnat] at h1
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Z).mp hspanS
    refine (Submodule.mem_span_range_iff_exists_fun Z).mpr ⟨c, ?_⟩
    apply Subtype.ext
    push_cast
    exact hc
  · intro x
    have hxadj : x ∈ Algebra.adjoin (ResidueField Z) ({wbar} : Set (ResidueField S)) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hwbar]
      trivial
    induction hxadj using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨⟨w, hwA⟩, hresw⟩
    | algebraMap c =>
        obtain ⟨z, rfl⟩ := residue_surjective (R := Z) c
        exact ⟨algebraMap Z A z, rfl⟩
    | add p q hp hq ihp ihq =>
        obtain ⟨a, ha⟩ := ihp
        obtain ⟨b, hb⟩ := ihq
        exact ⟨a + b, by push_cast; rw [map_add, ha, hb]⟩
    | mul p q hp hq ihp ihq =>
        obtain ⟨a, ha⟩ := ihp
        obtain ⟨b, hb⟩ := ihq
        exact ⟨a * b, by push_cast; rw [map_mul, ha, hb]⟩

/-- A bigger submodule (possibly over a *different* ring — only the carriers are compared)
has a smaller quotient. -/
theorem card_quot_le_card_quot {R R' M : Type*} [Ring R] [Ring R'] [AddCommGroup M]
    [Module R M] [Module R' M] [Finite M] (N : Submodule R M) (N' : Submodule R' M)
    (h : ∀ x, x ∈ N → x ∈ N') : Nat.card (M ⧸ N') ≤ Nat.card (M ⧸ N) := by
  classical
  haveI : Finite (M ⧸ N) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective N)
  have hsurj : Function.Surjective
      (fun q : M ⧸ N => (Submodule.Quotient.mk (Quotient.out q) : M ⧸ N')) := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N' y
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    refine (Submodule.Quotient.eq N').mpr (h _ ?_)
    exact (Submodule.Quotient.eq N).mp (Quotient.out_eq _)
  exact Nat.card_le_card_of_surjective _ hsurj

/-- **Residual trace surjectivity for finite rings.**  If `p` and `pA` are maximal then
`A ⧸ pA` is a finite extension of the finite — hence perfect — field `Z ⧸ p`, so it is
separable and mathlib's `Algebra.trace_surjective` applies.

Stated separately from the consumer below because the `Field` instances on the two quotients
have to be introduced *before* the statement's `Algebra` instance is fixed; introducing them
inside a proof whose goal already mentions an abbreviated ideal makes instance search fail. -/
theorem trace_surjective_of_map_isMaximal {Z A : Type*} [CommRing Z] [CommRing A] [Algebra Z A]
    [Finite Z] [Finite A] (p : Ideal Z) [hp : p.IsMaximal]
    (hmax : (Ideal.map (algebraMap Z A) p).IsMaximal) :
    Function.Surjective (Algebra.trace (Z ⧸ p) (A ⧸ Ideal.map (algebraMap Z A) p)) := by
  haveI := hmax
  letI : Field (Z ⧸ p) := Ideal.Quotient.field p
  letI : Field (A ⧸ Ideal.map (algebraMap Z A) p) := Ideal.Quotient.field _
  haveI : Finite (Z ⧸ p) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (A ⧸ Ideal.map (algebraMap Z A) p) :=
    Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : PerfectField (Z ⧸ p) := PerfectField.ofFinite
  exact Algebra.trace_surjective _ _

end FiniteLocalRingCore

open _root_.IsLocalRing in
/-- **CUT 2a-i of the trace witness: THE FINITE-LOCAL-RING CORE — an
unramified subalgebra of a finite local algebra over a finite local ring**
(PROVEN 2026-07-28; cut 2026-07-27 out of
`exists_unramifiedSubalgebra_finrank_eq_isUnit_trace` below, which is PROVEN
over it).

**This is the entire remaining mathematical content of Serre's wild different
bound, and NOTHING in it is about number fields.**  The number theory — that
`𝓞_K/Q^{e·k}` is a finite local ring with nilpotent maximal ideal, that its
residue field is `𝓞_K/Q`, that its cardinality is `|κ|^{e·k}`, that reducing
it mod `q` gives `𝓞_K/Q^e` of cardinality `|κ|^e`, and that `ℤ/q^k` is local
with residue field `𝔽_q` — is all discharged in the consumer, from
`span_sup_pow_ramificationIdx_eq_pow`, `cardQuot_pow_of_prime` and the three
local-ring lemmas above.

## WHAT THE HYPOTHESES SAY, AT THE INSTANCE `Z = ℤ/q^k`, `S = 𝓞_K/Q^{e·k}`

* `hnil` — `𝔪_S` is nilpotent (`𝔪_S^{e·k} = 0`).  This is what makes `S`
  Henselian without any completeness hypothesis.
* `hcard1` — `|S/𝔪_Z S| = |κ_S|^e`, i.e. `S/qS = 𝓞_K/Q^e`.  This is the ONLY
  place `e` enters, and it is what forces `finrank_A S = e`.
* `hcard2` — `|S| = |κ_S|^{e·k}`.
* `hcard3` — `|Z| = |κ_Z|^k`.

## THE CONSTRUCTION AS ACTUALLY CARRIED OUT

Write `f = [κ_S : κ_Z]`, so `|κ_S| = |κ_Z|^f` and `|Z| = |κ_Z|^k`.

1. *An unramified subring.*  `exists_subalgebra_span_pow_residue_surjective`
   above: `h ∈ Z[X]` monic of degree `f` reducing to the minimal polynomial of
   a primitive element `ω̄` of `κ_S / κ_Z`, Henselian lift `ω` of `ω̄`
   (`𝔪_S` NILPOTENT ⟹ `IsAdicComplete` ⟹ `HenselianRing`), and
   `A = Algebra.adjoin Z {ω}` — a `Subalgebra`, which is what makes
   `Algebra ↥A S` and `IsScalarTower Z ↥A S` automatic and is why the statement
   is phrased with `Subalgebra` rather than an abstract intermediate ring.
   That leaf delivers exactly two things: a `Z`-spanning family of `f` elements
   of `A`, and surjectivity of `A → κ_S`.
2. *Both freeness statements come out of ONE counting collapse.*  This replaces
   the valuation argument for injectivity of `Z[X]/(h) → S` that an earlier
   version of this plan called for; that argument is not available here, since
   `Z` is an arbitrary finite local ring and `𝔪_Z` need not be principal.
   Instead:
   * `A` is local (`isLocalRing_subalgebra`; only finiteness is needed, no
     nilpotence) with `𝔪_A` the contraction of `𝔪_S`, and `|κ_A| = |κ_S|`;
   * `|A| ≤ |Z|^f` from the `f` spanning elements;
   * Nakayama (`exists_span_eq_top_card_quot_eq_pow`) makes `S` spanned by `n`
     elements over `A` with `|κ_S|^n = |S/𝔪_A S| ≤ |S/𝔪_Z S| = |κ_S|^e`, so
     `n ≤ e` and `|S| ≤ |A|^n ≤ |A|^e`;
   * hence `|κ_Z|^{kfe} = |S| ≤ |A|^n ≤ |A|^e ≤ (|Z|^f)^e = |κ_Z|^{kfe}`, and
     every inequality in that chain is an equality.  So `|A| = |Z|^f`,
     `|S| = |A|^e` and `n = e`, and `free_finrank_of_span_of_card_eq` turns each
     of the two spanning families into a basis.  **This is what replaces local
     monogenicity `𝓞_L = W[π]`** — freeness is all the classical argument ever
     used, and freeness is free.
3. *`𝔪_Z A = 𝔪_A` is an OUTPUT, not an input.*  `A ⧸ 𝔪_Z A` is spanned over
   `κ_Z` by the images of the same `f` elements, so it has at most `|κ_Z|^f`
   elements; it also surjects onto `A ⧸ 𝔪_A = κ_S`, which has exactly that many.
   Equality forces `𝔪_Z A = 𝔪_A`, hence `𝔪_Z A` maximal.
4. *Residual trace surjectivity.*  `A/𝔪_Z A` and `Z/𝔪_Z` are then finite fields,
   the former perfect-base-separable over the latter, so
   `trace_surjective_of_map_isMaximal` (mathlib's `Algebra.trace_surjective`)
   applies.

FAITHFULNESS: not vacuous — `finrank ↥A S = e` and the residual surjectivity
are genuine assertions about a genuinely constructed `A`, `he0` is load-bearing
(it is what makes `x ↦ x^e` injective in the collapse of step 2), and the
cardinality hypotheses are exactly what the proof of freeness by counting
consumes.

REDUNDANCY NOTE (2026-07-28, correcting the previous line of this paragraph):
`hk0` is **not** used.  It is not needed, because `k = 0` already contradicts
`hcard3` — it would give `|Z| = 1`, and `Z` is local hence nontrivial.  The
hypothesis is kept so that the consumer
`exists_unramifiedSubalgebra_finrank_eq_isUnit_trace` below need not change; it
is underscore-prefixed so the redundancy is mechanically visible. -/
theorem exists_subalgebra_free_finrank_eq_residualTrace_surjective
    (Z S : Type*) [CommRing Z] [CommRing S] [Algebra Z S]
    [IsLocalRing Z] [IsLocalRing S] [Finite Z] [Finite S]
    [IsLocalHom (algebraMap Z S)]
    (hnil : IsNilpotent (IsLocalRing.maximalIdeal S))
    (e k : ℕ) (he0 : e ≠ 0) (_hk0 : k ≠ 0)
    (hcard1 : Nat.card (S ⧸ Ideal.map (algebraMap Z S) (IsLocalRing.maximalIdeal Z))
      = Nat.card (IsLocalRing.ResidueField S) ^ e)
    (hcard2 : Nat.card S = Nat.card (IsLocalRing.ResidueField S) ^ (e * k))
    (hcard3 : Nat.card Z = Nat.card (IsLocalRing.ResidueField Z) ^ k) :
    ∃ A : Subalgebra Z S,
      Module.Free Z A ∧ Module.Finite Z A ∧
      Module.Free A S ∧ Module.Finite A S ∧
      Module.finrank A S = e ∧
      Function.Surjective (Algebra.trace (Z ⧸ IsLocalRing.maximalIdeal Z)
        (A ⧸ Ideal.map (algebraMap Z A) (IsLocalRing.maximalIdeal Z))) := by
  classical
  haveI : Finite (ResidueField Z) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (ResidueField S) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : FiniteDimensional (ResidueField Z) (ResidueField S) := Module.Finite.of_finite
  set f := Module.finrank (ResidueField Z) (ResidueField S) with hfdef
  have hkS : Nat.card (ResidueField S) = Nat.card (ResidueField Z) ^ f :=
    natCard_eq_pow_finrank _ _
  obtain ⟨A, g, hspanA, hsurjA⟩ := exists_subalgebra_span_pow_residue_surjective Z S hnil
  haveI : Finite A := Subtype.finite
  haveI hAloc : IsLocalRing A := isLocalRing_subalgebra A
  have hmA : ∀ x : A, x ∈ maximalIdeal A ↔ (x : S) ∈ maximalIdeal S := by
    intro x
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_subalgebra_iff, ← mem_nonunits_iff,
      ← mem_maximalIdeal]
  -- `A ↠ κ_S` has kernel `𝔪_A`, so `|κ_A| = |κ_S|`
  set φ : A →+* ResidueField S := (residue S).comp (A.val : A →+* S) with hφdef
  have hφsurj : Function.Surjective φ := fun x => hsurjA x
  have hzero : ∀ y : S, residue S y = 0 ↔ y ∈ maximalIdeal S :=
    fun y => Ideal.Quotient.eq_zero_iff_mem
  have hker : RingHom.ker φ = maximalIdeal A := by
    ext x
    rw [RingHom.mem_ker, hφdef]
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hzero]
    exact (hmA x).symm
  have hresA : Nat.card (ResidueField A) = Nat.card (ResidueField S) :=
    Nat.card_congr (((Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hφsurj)).toEquiv)
  -- minimal generators of `S` over `A`
  obtain ⟨n, gg, hspanS, hcardV⟩ := exists_span_eq_top_card_quot_eq_pow A S
  have hcoe : ∀ z : Z, ((algebraMap Z A z : A) : S) = algebraMap Z S z := fun z => rfl
  have hsub : ∀ x : S, x ∈ Ideal.map (algebraMap Z S) (maximalIdeal Z) →
      x ∈ (maximalIdeal A • ⊤ : Submodule A S) := by
    intro x hx
    have hx' : x ∈ (maximalIdeal Z • (⊤ : Submodule Z S)) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro z hz s _
      have hz' : (algebraMap Z A z) ∈ maximalIdeal A := by
        rw [hmA, hcoe]
        refine (mem_maximalIdeal _).mpr fun hu => ?_
        exact (mem_maximalIdeal z).mp hz (isUnit_of_map_unit (algebraMap Z S) z hu)
      rw [← IsScalarTower.algebraMap_smul (↥A) z s]
      exact Submodule.smul_mem_smul hz' Submodule.mem_top
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  have hquotle : Nat.card (S ⧸ (maximalIdeal A • ⊤ : Submodule A S))
      ≤ Nat.card (S ⧸ Ideal.map (algebraMap Z S) (maximalIdeal Z)) :=
    card_quot_le_card_quot _ _ hsub
  have hcs2 : 2 ≤ Nat.card (ResidueField S) := by
    have := Finite.one_lt_card (α := ResidueField S)
    omega
  have hne : n ≤ e := by
    have h1 : Nat.card (ResidueField S) ^ n ≤ Nat.card (ResidueField S) ^ e := by
      rw [← hcard1, ← hresA, ← hcardV]; exact hquotle
    exact (Nat.pow_le_pow_iff_right hcs2).mp h1
  -- the two upper bounds
  have hAle : Nat.card A ≤ Nat.card Z ^ f := card_le_pow_of_span_eq_top g hspanA
  have hSle : Nat.card S ≤ Nat.card A ^ n := card_le_pow_of_span_eq_top gg hspanS
  haveI : Nontrivial A := inferInstance
  have hcA2 : 2 ≤ Nat.card A := by have := Finite.one_lt_card (α := A); omega
  have hSval : Nat.card S = (Nat.card Z ^ f) ^ e := by
    rw [hcard2, hkS, hcard3, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  -- the counting chain collapses
  have hchain : Nat.card S ≤ Nat.card A ^ e := hSle.trans (Nat.pow_le_pow_right (by omega) hne)
  have hchain2 : Nat.card A ^ e ≤ Nat.card S := by
    rw [hSval]; exact Nat.pow_le_pow_left hAle e
  have hAe : Nat.card A ^ e = Nat.card S := le_antisymm hchain2 hchain
  have hcA : Nat.card A = Nat.card Z ^ f := by
    refine Nat.pow_left_injective he0 ?_
    show Nat.card A ^ e = (Nat.card Z ^ f) ^ e
    rw [hAe, hSval]
  have hSA : Nat.card S = Nat.card A ^ n := le_antisymm hSle (by
    rw [← hAe]; exact Nat.pow_le_pow_right (by omega) hne)
  have hnE : n = e := Nat.pow_right_injective hcA2 (by
    show Nat.card A ^ n = Nat.card A ^ e
    rw [← hSA, hAe])
  subst hnE
  obtain ⟨hfreeZ, hfinZ, -⟩ := free_finrank_of_span_of_card_eq g hspanA hcA
  obtain ⟨hfreeA, hfinA, hrank⟩ := free_finrank_of_span_of_card_eq gg hspanS hSA
  refine ⟨A, hfreeZ, hfinZ, hfreeA, hfinA, hrank, ?_⟩
  -- the residual trace: first `𝔪_Z A = 𝔪_A`
  set I : Ideal A := Ideal.map (algebraMap Z A) (maximalIdeal Z) with hIdef
  have hIle : I ≤ maximalIdeal A := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, hmA, hcoe]
    refine (mem_maximalIdeal _).mpr fun hu => ?_
    exact (mem_maximalIdeal z).mp hz (isUnit_of_map_unit (algebraMap Z S) z hu)
  haveI : Finite (A ⧸ I) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (Z ⧸ maximalIdeal Z) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have hspanQ : Submodule.span (Z ⧸ maximalIdeal Z)
      (Set.range fun i => (Ideal.Quotient.mk I (g i) : A ⧸ I)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha : a ∈ Submodule.span Z (Set.range g) := by rw [hspanA]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Z).mp ha
    refine (Submodule.mem_span_range_iff_exists_fun (Z ⧸ maximalIdeal Z)).mpr
      ⟨fun i => Ideal.Quotient.mk (maximalIdeal Z) (c i), ?_⟩
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  have hQle : Nat.card (A ⧸ I) ≤ Nat.card (Z ⧸ maximalIdeal Z) ^ f :=
    card_le_pow_of_span_eq_top _ hspanQ
  have hQge : Nat.card (A ⧸ maximalIdeal A) ≤ Nat.card (A ⧸ I) :=
    card_quot_le_card_quot I (maximalIdeal A) fun x hx => hIle hx
  have hQeq : Nat.card (A ⧸ I) = Nat.card (A ⧸ maximalIdeal A) := by
    refine le_antisymm ?_ hQge
    calc Nat.card (A ⧸ I) ≤ Nat.card (Z ⧸ maximalIdeal Z) ^ f := hQle
      _ = Nat.card (ResidueField S) := hkS.symm
      _ = Nat.card (A ⧸ maximalIdeal A) := hresA.symm
  have hIeq : I = maximalIdeal A := by
    refine le_antisymm hIle fun x hx => ?_
    have hfsurj : Function.Surjective (Ideal.Quotient.factor hIle) := by
      intro y
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk I a, by rw [← ha]; rfl⟩
    have hbij := (Nat.bijective_iff_surjective_and_card _).mpr ⟨hfsurj, hQeq⟩
    have h0 : Ideal.Quotient.factor hIle (Ideal.Quotient.mk I x) =
        Ideal.Quotient.factor hIle (0 : A ⧸ I) := by
      rw [map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hx
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (hbij.1 h0)
  haveI : (maximalIdeal Z).IsMaximal := maximalIdeal.isMaximal Z
  have hImax : (Ideal.map (algebraMap Z ↥A) (maximalIdeal Z)).IsMaximal := by
    rw [← hIdef, hIeq]; exact maximalIdeal.isMaximal A
  exact trace_surjective_of_map_isMaximal (maximalIdeal Z) hImax

attribute [local instance] Ideal.Quotient.field in
/-- **CUT 2a of the trace witness: the unramified subalgebra
`A ⊆ 𝓞_K/Q^{e·k}`, free of rank `f` over `ℤ/q^k`, over which
`S = 𝓞_K/Q^{e·k}` is free of rank `e`** (PROVEN 2026-07-27 over the
finite-local-ring core
`exists_subalgebra_free_finrank_eq_residualTrace_surjective` above; cut
2026-07-27 out of `exists_mem_cofactor_trace_quotient_ne_zero` below,
which is PROVEN over it).

**All the number theory is discharged HERE; nothing arithmetic is left.**
This proof establishes, for `Z = ℤ/q^k` and `S = 𝓞_K/Q^{e·k}`:

* `S` is a finite local ring (`isLocalRing_quotient_pow_of_isMaximal`,
  `Ring.HasFiniteQuotients.finiteQuotient`) whose maximal ideal is the image
  of `Q` (`maximalIdeal_quotient_pow_eq_map`) and is therefore NILPOTENT;
* `Z` is a finite local ring (`isLocalRing_int_quotient_of_eq_span` and
  `comap_pow_ramificationIdx_eq_span` above) with maximal ideal `(q)`
  (`maximalIdeal_int_quotient_pow_eq_span`), so `algebraMap Z S` is a local
  homomorphism;
* `|Z| = q^k`, `|κ_Z| = q`, `|S| = |κ_S|^{e·k}` and — the only genuinely
  arithmetic input — `|S/qS| = |κ_S|^e`, because `(q) ⊔ Q^{e·k} = Q^e`
  (`span_sup_pow_ramificationIdx_eq_pow` above), with the cardinalities of
  the `Q`-power quotients coming from mathlib's `cardQuot_pow_of_prime`.

The construction of `A` itself — the Henselian lift of a residue-field
generator, freeness of `A` over `Z` by the valuation argument, freeness of
`S` over `A` by Nakayama plus counting, and the residual trace surjectivity
from separability of `κ_S/κ_Z` — is the finite-local-ring core above, where
the full plan is recorded.

FAITHFULNESS: not vacuous — `finrank ↥A S = e` and the residual
surjectivity are both genuine assertions about a genuinely constructed
`A`, and `hk0` is load-bearing (at `k = 0` the ring `S` is trivial and
no subalgebra has `finrank ↥A S = e > 0`). -/
theorem exists_unramifiedSubalgebra_finrank_eq_isUnit_trace
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ) (hk0 : k ≠ 0) :
    ∃ A : Subalgebra
        (ℤ ⧸ (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)),
      Module.Free (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K))) A ∧
      Module.Finite (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K))) A ∧
      Module.Free A (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) ∧
      Module.Finite A (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) ∧
      Module.finrank A (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) = e ∧
      ∃ a : A, IsUnit (Algebra.trace (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K))) A a) := by
  classical
  have hcomap := comap_pow_ramificationIdx_eq_span K q hq v hmem e he k
  haveI hloc : IsLocalRing (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) :=
    isLocalRing_int_quotient_of_eq_span q hq k (Nat.pos_of_ne_zero hk0) _ hcomap
  -- `e ≠ 0`
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hene0 : e ≠ 0 := by
    rw [he]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0
  have hn0 : e * k ≠ 0 := Nat.mul_ne_zero hene0 hk0
  haveI hQmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI hSloc : IsLocalRing (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) :=
    isLocalRing_quotient_pow_of_isMaximal _ _ hn0
  have hQpow0 : v.asIdeal ^ (e * k) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero (e * k) (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  haveI hSfin : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) :=
    Ring.HasFiniteQuotients.finiteQuotient hQpow0
  have hZeq : (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K))
      = Ideal.span {((q ^ k : ℕ) : ℤ)} := by
    rw [hcomap]
    norm_cast
  haveI hqk0 : NeZero (q ^ k) := ⟨pow_ne_zero k hq.ne_zero⟩
  haveI hZfin : Finite (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) :=
    Finite.of_equiv (ZMod (q ^ k))
      ((Int.quotientSpanNatEquivZMod (q ^ k)).symm.trans
        (Ideal.quotEquivOfEq hZeq.symm)).toEquiv
  -- the maximal ideals of the two quotients
  have hmZ : IsLocalRing.maximalIdeal (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))
      = Ideal.span {Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K))) ((q : ℕ) : ℤ)} :=
    maximalIdeal_int_quotient_pow_eq_span q hq k hk0 _ hcomap
  have hmS : IsLocalRing.maximalIdeal (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
      = Ideal.map (Ideal.Quotient.mk (v.asIdeal ^ (e * k))) v.asIdeal :=
    maximalIdeal_quotient_pow_eq_map _ _ hn0
  -- the structure map on integer casts
  have hcast : ∀ m : ℤ,
      algebraMap (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K)))
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
        (Ideal.Quotient.mk _ m)
        = Ideal.Quotient.mk (v.asIdeal ^ (e * k)) ((m : ℤ) : NumberField.RingOfIntegers K) := by
    intro m
    rw [eq_intCast (Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K)))) m, map_intCast, map_intCast]
  have hqS : algebraMap (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
      (Ideal.Quotient.mk _ ((q : ℕ) : ℤ))
      = Ideal.Quotient.mk (v.asIdeal ^ (e * k)) ((q : ℕ) : NumberField.RingOfIntegers K) := by
    rw [hcast]
    norm_cast
  have hqnu : ¬ IsUnit (Ideal.Quotient.mk (v.asIdeal ^ (e * k))
      ((q : ℕ) : NumberField.RingOfIntegers K)) := by
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem v.asIdeal hn0]
    exact fun hc => hc hmem
  haveI hlh : IsLocalHom (algebraMap (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K)))
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))) := by
    refine ⟨fun {a} ha => ?_⟩
    by_contra hna
    have hmem' : a ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hna)
    rw [hmZ, Ideal.mem_span_singleton] at hmem'
    obtain ⟨c, rfl⟩ := hmem'
    rw [map_mul, hqS] at ha
    exact hqnu (isUnit_of_mul_isUnit_left ha)
  -- nilpotence of the maximal ideal of `S`
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))) := by
    refine ⟨e * k, ?_⟩
    rw [hmS, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  -- cardinalities
  have hcq : ∀ m : ℕ, Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ m)
      = Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) ^ m := by
    intro m
    have h := cardQuot_pow_of_prime (P := v.asIdeal) v.ne_bot (i := m)
    rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
  have hres : Nat.card (IsLocalRing.ResidueField
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)))
      = Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
    Nat.card_congr ((Ideal.quotEquivOfEq hmS).toEquiv.trans
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn0)).toEquiv)
  have hcard2 : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
      = Nat.card (IsLocalRing.ResidueField
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))) ^ (e * k) := by
    rw [hres]
    exact hcq (e * k)
  have hmapq : Ideal.map (algebraMap (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)))
      (IsLocalRing.maximalIdeal (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K))))
      = Ideal.map (Ideal.Quotient.mk (v.asIdeal ^ (e * k)))
        (Ideal.span {((q : ℕ) : NumberField.RingOfIntegers K)}) := by
    rw [hmZ, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, hqS]
  have hcard1 : Nat.card ((NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) ⧸
        Ideal.map (algebraMap (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K)))
          (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)))
        (IsLocalRing.maximalIdeal (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K)))))
      = Nat.card (IsLocalRing.ResidueField
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))) ^ e := by
    rw [hres, ← hcq e]
    refine Nat.card_congr ((Ideal.quotEquivOfEq hmapq).toEquiv.trans
      ((DoubleQuot.quotQuotEquivQuotSup (v.asIdeal ^ (e * k))
        (Ideal.span {((q : ℕ) : NumberField.RingOfIntegers K)})).toEquiv.trans
      (Ideal.quotEquivOfEq ?_).toEquiv))
    rw [sup_comm]
    exact span_sup_pow_ramificationIdx_eq_pow K q hq v hmem e he k hk0
  have hZcard : Nat.card (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) = q ^ k := by
    rw [Nat.card_congr ((Ideal.quotEquivOfEq hZeq).toEquiv.trans
      (Int.quotientSpanNatEquivZMod (q ^ k)).toEquiv)]
    exact Nat.card_zmod _
  have hZres : Nat.card (IsLocalRing.ResidueField (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K)))) = q := by
    have hspanmap : Ideal.span {Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K))) ((q : ℕ) : ℤ)}
        = Ideal.map (Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
          (algebraMap ℤ (NumberField.RingOfIntegers K)))) (Ideal.span {((q : ℕ) : ℤ)}) := by
      rw [Ideal.map_span, Set.image_singleton]
    have hsup : (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K))
        ⊔ Ideal.span {((q : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by
      rw [sup_eq_right, hcomap, Ideal.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
      exact dvd_pow_self _ hk0
    exact (Nat.card_congr ((Ideal.quotEquivOfEq (hmZ.trans hspanmap)).toEquiv.trans
      ((DoubleQuot.quotQuotEquivQuotSup _ _).toEquiv.trans
        ((Ideal.quotEquivOfEq hsup).toEquiv.trans
          (Int.quotientSpanNatEquivZMod q).toEquiv)))).trans (Nat.card_zmod _)
  have hcard3 : Nat.card (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K)))
      = Nat.card (IsLocalRing.ResidueField (ℤ ⧸ (v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))) ^ k := by
    rw [hZcard, hZres]
  obtain ⟨A, hf1, hfin1, hf2, hfin2, hrank, hsurjt⟩ :=
    exists_subalgebra_free_finrank_eq_residualTrace_surjective _ _ hnil e k hene0 hk0
      hcard1 hcard2 hcard3
  haveI := hf1
  haveI := hfin1
  exact ⟨A, hf1, hfin1, hf2, hfin2, hrank,
    exists_isUnit_trace_of_residualTrace_surjective _ _ hsurjt⟩

/-- **CUT 2 of the trace witness: the trace form of the finite local
ring `𝓞_K/Q^{e·k}` over `ℤ/q^k` is not identically zero, witnessed
inside the cofactor `J`** (PROVEN 2026-07-27 over
`exists_unramifiedSubalgebra_finrank_eq_isUnit_trace`,
`sup_pow_ramificationIdx_cofactor_eq_top` and
`comap_pow_ramificationIdx_eq_span` above; cut 2026-07-27 out of
`exists_intTrace_not_mem_span_of_ramificationIdx` below).

**This is the whole mathematical content of Serre's wild different
bound.**  Everything else in the chain is bookkeeping.

## THE STATEMENT IS EXACTLY "TRACE NONZERO", AND THAT IS WHY `k` IS `v_q(e)+1`

The consumer needs `v_q(Tr x) ≤ v_q(e)`.  With `k = v_q(e) + 1` that
is literally `q^k ∤ Tr x`, i.e. `Tr x ≠ 0` in `ℤ/q^k`.  So no
"exactly `v_q(e)`" claim is needed anywhere — nonvanishing is the
whole target, and the hypothesis `hk` enters the proof only through
`(e : ℤ/q^k) ≠ 0`, which is `v_q(e) = k − 1 < k`.

## HOW IT IS PROVEN — steps 4, 5' and 6 here, steps 1–3 in the cut above

Write `S = 𝓞_K/Q^{e·k}`, `Z = ℤ/q^k`, `κ = 𝓞_K/Q = 𝔽_{q^f}`.  `S` is a
finite local ring with nilpotent maximal ideal and `q^k = 0`; it is
free of rank `e·f` over `Z`.

Steps 1–3 and the residue-field half of step 5 — the unramified
subalgebra `A ⊆ S`, free of rank `f` over `Z`, over which `S` is free
of rank `e` by counting, and whose residual trace is surjective — are
the SORRY LEAF `exists_unramifiedSubalgebra_finrank_eq_isUnit_trace`
above, where the construction plan, the `IsAdicComplete` gap and the
`Algebra.FormallySmooth.lift` route around it are recorded in full.
The rest is proven here:

4. *Trace tower.*  `Algebra.trace_trace`
   (`Mathlib/RingTheory/Trace/Defs.lean:138`, hypotheses exactly
   `Free`+`Finite` at both levels) and `Algebra.trace_algebraMap`
   (`Defs.lean:111`) give
   `Tr_{S/Z}(a) = (finrank_A S)·Tr_{A/Z}(a) = e·Tr_{A/Z}(a)` for
   `a ∈ A`.  Because `A` is carried as a `Subalgebra Z S` rather than
   as an abstract intermediate ring, `Algebra ↥A S` and
   `IsScalarTower Z ↥A S` are found by instance search — that choice
   is what turns this step into a three-line rewrite, and it is why
   the cut above is phrased with `Subalgebra`.
5'. *Unit trace from residual trace.*  `Z` is a LOCAL ring
   (`isLocalRing_int_quotient_of_eq_span` above, applied directly to
   the contraction via `comap_pow_ramificationIdx_eq_span`), and its
   maximal ideal is `(q)`, so `Algebra.trace_quotient_mk` reduces the
   trace MOD `q` — which is exactly the residue-field statement this
   step wants.  That is
   `exists_isUnit_trace_of_residualTrace_surjective` above, already
   applied inside the cut.
6. *Conclusion.*  `Tr_{S/Z}(a) = e·Tr_A(a) ≠ 0` in `Z` because
   `(e : Z) ≠ 0` — that is `hk`, via `q^k ∤ e`
   (`Nat.Prime.pow_dvd_iff_le_factorization`, using `e ≠ 0` from
   `ramificationIdx'_ne_zero_of_liesOver`) — and `Tr_A(a)` is a unit,
   so `IsUnit.mul_left_eq_zero` finishes.  The witness is pulled back
   into `J` because `J ⊔ Q^{e·k} = ⊤`
   (`sup_pow_ramificationIdx_cofactor_eq_top` above), which makes
   `J → 𝓞_K → S` surjective: from `p + j = 1` with `p ∈ Q^{e·k}`,
   `j ∈ J`, the element `y·j` lies in `J` and reduces to `ȳ`.

## WHAT DOES NOT APPLY, CHECKED — DO NOT SPEND A CYCLE REDISCOVERING IT

`Algebra.trace_quotient_eq_of_isDedekindDomain` and
`Algebra.trace_quotient_mk` at base `ℤ`, and `Module.basisQuotient`
(`Mathlib/RingTheory/LocalRing/Quotient.lean:85`), all require the base
ideal to be MAXIMAL.  At step 5 the base `Z = ℤ/q^k` IS local, so
`trace_quotient_mk` *does* apply there — it is only the passage from
`ℤ` to `ℤ/q^k` (cut 1, step 1) where maximality fails.

FAITHFULNESS: not vacuous — the conclusion asserts a nonvanishing, and
the extremal witness is NOT `1` (whose trace `e·f` is useless when
`q ∣ f`) but an element of the unramified subring with unit residue
trace.  Sanity-checked on `K = ℚ(√2,√5)`, `q = 2`, `e = f = 2`, `k = 2`,
where `x = (1+√5)/2` is a unit at the unique prime above `2` with
`Tr_{K/ℚ}(x) = 2`, so `v_2(Tr x) = 1 = v_2(e) < k`, matching the sharp
`d = 3 = e − 1 + e·v_2(e)`. -/
theorem exists_mem_cofactor_trace_quotient_ne_zero
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ) (hk : k = e.factorization q + 1)
    (J : Ideal (NumberField.RingOfIntegers K))
    (hJ : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
      = v.asIdeal ^ (e * k) * J) :
    ∃ x : NumberField.RingOfIntegers K, x ∈ J ∧
      Algebra.trace
        (ℤ ⧸ (v.asIdeal ^ (e * k)).comap (algebraMap ℤ (NumberField.RingOfIntegers K)))
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k))
        (Ideal.Quotient.mk _ x) ≠ 0 := by
  classical
  have hk0 : k ≠ 0 := by omega
  -- `e ≠ 0`: the ramification index of a prime lying over `q` is positive
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hene0 : e ≠ 0 := by
    rw [he]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0
  -- step 6's arithmetic: `(e : ℤ/q^k) ≠ 0`, which is exactly `v_q(e) = k − 1 < k`
  have hecast : ((e : ℕ) : ℤ ⧸ (v.asIdeal ^ (e * k)).comap
      (algebraMap ℤ (NumberField.RingOfIntegers K))) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk ((v.asIdeal ^ (e * k)).comap
        (algebraMap ℤ (NumberField.RingOfIntegers K)))) e, Ne,
      Ideal.Quotient.eq_zero_iff_mem, comap_pow_ramificationIdx_eq_span K q hq v hmem e he k,
      Ideal.mem_span_singleton]
    intro hdvd
    have hdvd' : (q : ℕ) ^ k ∣ e := by
      have h2 : ((q ^ k : ℕ) : ℤ) ∣ ((e : ℕ) : ℤ) := by push_cast at hdvd ⊢; exact hdvd
      exact_mod_cast h2
    rw [Nat.Prime.pow_dvd_iff_le_factorization hq hene0] at hdvd'
    omega
  haveI hnt : Nontrivial (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k)) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    intro htop
    have h1 : v.asIdeal ^ (e * k) ≤ v.asIdeal := Ideal.pow_le_self (Nat.mul_ne_zero hene0 hk0)
    rw [htop, top_le_iff] at h1
    exact v.isPrime.ne_top h1
  -- every residue class of `S = 𝓞_K/Q^{e·k}` is represented inside the cofactor `J`
  have hsup := sup_pow_ramificationIdx_cofactor_eq_top K q hq v hmem e he k J hJ
  have hlift : ∀ s : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e * k),
      ∃ x : NumberField.RingOfIntegers K, x ∈ J ∧ Ideal.Quotient.mk _ x = s := by
    intro s
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal ^ (e * k) ⊔ J := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨p, hp, j, hj, hpj⟩ := Submodule.mem_sup.mp h1
    refine ⟨y * j, Ideal.mul_mem_left J y hj, ?_⟩
    have hp0 : Ideal.Quotient.mk (v.asIdeal ^ (e * k)) p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hp
    have hj1 : Ideal.Quotient.mk (v.asIdeal ^ (e * k)) j = 1 := by
      have hcg := congrArg (Ideal.Quotient.mk (v.asIdeal ^ (e * k))) hpj
      simpa [hp0] using hcg
    rw [map_mul, hj1, mul_one]
  -- the finite-ring core, then step 4's trace tower `Tr_{S/Z} a = e · Tr_{A/Z} a`
  obtain ⟨A, hf1, hfin1, hf2, hfin2, hrank, a, hu⟩ :=
    exists_unramifiedSubalgebra_finrank_eq_isUnit_trace K q hq v hmem e he k hk0
  obtain ⟨x, hxJ, hxa⟩ := hlift (algebraMap A _ a)
  refine ⟨x, hxJ, ?_⟩
  rw [hxa, ← Algebra.trace_trace (S := A), Algebra.trace_algebraMap, hrank, map_nsmul,
    nsmul_eq_mul]
  intro hcon
  exact hecast (hu.mul_left_eq_zero.mp hcon)

/-- **The trace witness for Serre's different bound** (PROVEN 2026-07-27
over the two cuts `trace_quotient_pow_eq_of_mem_cofactor` (trace
bookkeeping: base change plus CRT) and
`exists_mem_cofactor_trace_quotient_ne_zero` (the finite-ring content),
with `comap_pow_ramificationIdx_eq_span` as the bridge; cut 2026-07-27
out of `differentIdeal_exponent_le_wild_of_residueDegreeGtOne`
below, which is PROVEN over it).

With `k = v_q(e) + 1` and `J` the cofactor of `Q^{e·k}` in `q^k·𝓞_K`,
there is an `x ∈ J` — i.e. an `x` divisible by `Q'^{e_{Q'}·k}` at every
prime `Q' ∣ q` other than `Q`, with no condition at `Q` itself — whose
trace has `v_q(Tr_{K/ℚ} x) ≤ v_q(e)`.

## WHY THIS IS THE WHOLE CONTENT

By mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem` this leaf is
EQUIVALENT to Serre's bound `d ≤ e − 1 + e·v_q(e)` at `Q` (see the
consumer's docstring for the reduction, which is now proven).  It is
stated with NO wildness and NO residue-degree hypothesis because it is
true, and needed, in every case — the `f = 1` and tame cases of the
bound are already proven above by other routes, but this statement
covers them too.

The equivalence also fixes the exact shape of any proof: the trace map
`Tr : 𝓞_K → ℤ` composed with reduction mod `q^k` factors through
`𝓞_K/q^k𝓞_K ≅ ∏_{Q'∣q} 𝓞_K/Q'^{e_{Q'}k}` (CRT), and `x ∈ J` says
exactly that `x` is supported on the `Q`-factor.  So the leaf says:
**the trace form of the finite ring `S = 𝓞_K/Q^{e·k}` over `ℤ/q^k` is
not identically zero.**  There is no room for a cheaper reformulation.

## THE PROOF PLAN — NOW OWNED BY THE TWO CUTS ABOVE

**Retained here for context only, and now doubly superseded: as of
2026-07-27 steps 4–6 are PROVEN inside
`exists_mem_cofactor_trace_quotient_ne_zero` above, and the LIVE
version of steps 1–3 — the only part still open — is the docstring of
`exists_unramifiedSubalgebra_finrank_eq_isUnit_trace` above.  EDIT THAT
ONE.**  Steps 1–6 below are its steps 1–6; the CRT and base-change
bookkeeping they gesture at is the separate leaf
`trace_quotient_pow_eq_of_mem_cofactor`.

(Derived 2026-07-27.  This supersedes BOTH routes recorded on the
consumer before that date — the trace-dual route's "hard case needs
Serre's (M2) over the maximal unramified subring" and the base-change
route to `ℚ(ζ_{q^f−1})`.  Neither is needed: no completions, no local
fields, no Teichmüller theory beyond finite abelian groups, and — the
point — no local monogenicity `𝓞_L = W[π]`.)

Write `S = 𝓞_K/Q^{e·k}`, a finite local ring with residue field
`k(Q) = 𝔽_{q^f}` and with `q^k = 0` in it; `|S| = q^{efk}`, so `S` is
free of rank `e·f` over `ℤ/q^k` (it is a direct factor of the free
module `𝓞_K/q^k𝓞_K`, hence projective, hence free over the local
artinian ring `ℤ/q^k`, and the rank is forced by counting).

1. *An unramified subring `A ⊆ S`.*  Let `h ∈ ℤ[X]` be monic of degree
   `f` with `h mod q` the minimal polynomial of a generator `ω̄` of
   `k(Q)` over `𝔽_q`.  `h mod q` is separable, so `h'(ω₀)` is a unit in
   `S` for any lift `ω₀` of `ω̄`; `S` is local with NILPOTENT maximal
   ideal, hence Henselian, so Newton iteration terminates and produces
   `ω ∈ S` with `h(ω) = 0` and `ω ≡ ω₀`.  Put
   `A = (ℤ/q^k)[X]/(h) → S`, `X ↦ ω`.

   *The one mathlib gap, and it is small.*  Henselianity is reached by
   `IsAdicComplete.henselianRing` (`Mathlib/RingTheory/Henselian.lean`),
   but the pin has **no `IsAdicComplete I R` instance for a NILPOTENT
   `I`** — only for `ℤ_[p]`, power series, Witt vectors and complete
   Noetherian local rings.  Supplying it is a few lines and it is the
   whole of the gap: `IsHausdorff` is `⋂ Iⁿ = 0`, and for
   `IsPrecomplete` a compatible sequence `f` has limit `f N` where
   `I^N = 0` (for `n ≤ N` compatibility gives it; for `n > N` the
   modulus is `0`, so `f n = f N` on the nose).  **Check before
   building it**: `grep -rn "IsAdicComplete" .lake/packages/mathlib`
   for a nilpotent/artinian instance added since this note.

   *A fallback for the lift itself, if Hensel is awkward: pure finite
   group theory.*  `|S^×| = q^{f(ek−1)}·m` with `m = q^f − 1`, so for
   `u ∈ S^×` any lift of a generator of `k(Q)^×` and `a = f(ek−1)`, the
   element `ω = u^{q^a}` satisfies `ω^m = 1` and still reduces to a
   generator (`q^a` is coprime to `m`).  This gives the Teichmüller
   element with no Newton iteration — but note it does NOT by itself
   give the monic degree-`f` relation that makes `A` free of rank `f`,
   which is why Hensel is the primary route and this is only a fallback
   for step 1's first half.
2. *`A` is free of rank `f` over `ℤ/q^k` and the map is injective.*
   Freeness is by construction (quotient by a monic of degree `f`).
   For injectivity suppose `∑_{j<f} c_j ω^j = 0` with `c_j ∈ ℤ/q^k` not
   all `0`; let `μ = min_j v_q(c_j) < k` and write `c_j = q^μ b_j`.
   Then `∑ b_j ω^j` reduces to `∑ b̄_j ω̄^j ≠ 0` in `k(Q)` by
   `𝔽_q`-independence of `1, ω̄, …, ω̄^{f−1}`, so it is a UNIT of `S`,
   whence `q^μ = 0` in `S`, i.e. `e·μ ≥ e·k`, i.e. `μ ≥ k` —
   contradiction.
3. *`S` is free of rank `e` over `A`, BY COUNTING.*  `𝔪_A = qA` and
   `S/qS = 𝓞_K/(Q^{e·k} + q𝓞_K) = 𝓞_K/Q^e`, of `k(Q)`-dimension `e`,
   so Nakayama gives a surjection `A^e ↠ S`; and
   `|A^e| = (q^{kf})^e = q^{efk} = |S|`, so it is bijective.  **This is
   what replaces local monogenicity**: freeness is all the argument
   ever used, and freeness is free.
4. *The trace tower.*  `Tr_{S/(ℤ/q^k)} = Tr_{A/(ℤ/q^k)} ∘ Tr_{S/A}`
   (`Algebra.trace_trace`), and for `a ∈ A` one has
   `Tr_{S/A}(a) = e·a` (`Algebra.trace_algebraMap`, rank `e`).
5. *A unit trace upstairs.*  `A` is free of rank `f` over `ℤ/q^k` with
   `A/qA = k(Q)`, and a basis reduces to a basis, so
   `Tr_{A/(ℤ/q^k)} mod q = Tr_{k(Q)/𝔽_q}`, which is surjective because
   `k(Q)/𝔽_q` is separable.  Pick `a ∈ A` with `Tr_A(a)` a unit.
6. *Conclusion.*  `Tr_{S/(ℤ/q^k)}(a) = e·Tr_A(a)` has `q`-adic
   valuation exactly `v_q(e) = k − 1 < k`, so it is NONZERO in
   `ℤ/q^k`.  Lift `a` to `x ∈ 𝓞_K` supported on the `Q`-factor (CRT),
   and `v_q(Tr_{K/ℚ} x) = v_q(e)`.

Step 6 is also the sanity check the old docstring was missing: the
extremal witness is not `1` (whose trace is `e·f`, useless when
`q ∣ f`) but an element of the unramified subring with unit residue
trace, and the factor `e` comes from `Tr_{S/A}(1) = e` alone.  On the
worked instance `K = ℚ(√2,√5)`, `q = 2`, `e = f = 2`, `k = 2`, one may
take `x = (1+√5)/2`: it is a unit at the unique prime above `2`, and
`Tr_{K/ℚ}((1+√5)/2) = 2`, so `v_2(Tr x) = 1 = v_2(e) < k` — matching
`d = 3 = e − 1 + e·v_2(e)`, the sharp case.

## MATHLIB INPUTS ALREADY LOCATED

All checked to exist in our pin on 2026-07-27, with exact signatures:

* `not_dvd_differentIdeal_of_intTrace_not_mem` — the consumer's handle.
* `Algebra.intTrace_eq_trace [Module.Free A B] : intTrace A B = trace A B`
  (`Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean:307`).
  `𝓞_K` is free over `ℤ`, so the leaf's `Algebra.intTrace` is just
  `Algebra.trace ℤ 𝓞_K`; do this first, it removes a whole layer.
* `Algebra.trace_trace [Module.Free R S] [Module.Finite R S]
  [Module.Free S T] [Module.Finite S T]`
  (`Mathlib/RingTheory/Trace/Defs.lean:138`) — step 4.  Note the
  hypotheses are exactly `Free`+`Finite` at both levels, which is
  precisely what steps 2 and 3 supply.
* `Algebra.trace_algebraMap [StrongRankCondition R] [Module.Free R S] :
  trace R S (algebraMap R S x) = finrank R S • x`
  (`Trace/Defs.lean:111`) — step 4's `Tr_{S/A}(a) = e·a`.
* `LinearMap.trace_baseChange` (`Mathlib/LinearAlgebra/Trace.lean:387`)
  for the reduction of the trace mod `q^k`.

**And one thing that does NOT apply, checked**: `Trace/Quotient.lean`'s
`Algebra.trace_quotient_eq_of_isDedekindDomain` and
`Algebra.trace_quotient_mk`, and `Module.basisQuotient`
(`Mathlib/RingTheory/LocalRing/Quotient.lean:85`), all require the base
ideal to be MAXIMAL (`basisQuotient` is built under
`attribute [local instance] Ideal.Quotient.field`), so none of them is
available at `p = (q^k)`.  Reduce the trace from a `ℤ`-basis with
`Algebra.trace_eq_matrix_trace`, or via `LinearMap.trace_baseChange`
along `ℤ → ℤ/q^k`, instead.  Do not spend a cycle rediscovering this.

CRT splitting: `Ideal.quotientInfRingEquivPiQuotient`. -/
theorem exists_intTrace_not_mem_span_of_ramificationIdx
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (k : ℕ) (hk : k = e.factorization q + 1)
    (J : Ideal (NumberField.RingOfIntegers K))
    (hJ : Ideal.span {(q : NumberField.RingOfIntegers K) ^ k}
      = v.asIdeal ^ (e * k) * J) :
    ∃ x : NumberField.RingOfIntegers K, x ∈ J ∧
      Algebra.intTrace ℤ (NumberField.RingOfIntegers K) x
        ∉ Ideal.span {((q : ℤ) ^ k)} := by
  classical
  obtain ⟨x, hxJ, hne⟩ :=
    exists_mem_cofactor_trace_quotient_ne_zero K q hq v hmem e he k hk J hJ
  refine ⟨x, hxJ, ?_⟩
  intro hcon
  refine hne ?_
  rw [← trace_quotient_pow_eq_of_mem_cofactor K q hq v hmem e he k J hJ x hxJ,
    Ideal.Quotient.eq_zero_iff_mem,
    comap_pow_ramificationIdx_eq_span K q hq v hmem e he k]
  rw [Algebra.intTrace_eq_trace] at hcon
  exact hcon

-- `hwild` and `hres` are unused: the leaf this is proven over is the
-- general statement of Serre's bound.  See the docstring below.
set_option linter.unusedVariables false in
/-- **The different-exponent bound at a WILD prime of residue degree
`> 1`** (PROVEN 2026-07-27 over `exists_intTrace_not_mem_span_of_ramificationIdx`
above; Serre, *Corps Locaux* III §6 Prop. 13).

`Q^d ∣ 𝔡_{K/ℚ}` implies `d ≤ e − 1 + e·v_q(e)`, for a prime `Q` of
`𝓞_K` above `q` with `q ∣ e` (wild) and `𝓞_K/Q ≠ 𝔽_q` (`f > 1`).

This was the LAST arithmetic leaf of the Hermite–Minkowski cut of
`finite_setOf_isHardlyRamified`; since 2026-07-27 the cluster's single
open node is instead `exists_intTrace_not_mem_span_of_ramificationIdx`
above.  Every other case of Serre's bound, and everything downstream of
it, is proven:

* `q ∤ e` (tame, any `f`) — `ModThree.lean`'s
  `IsHardlyRamified.not_pow_ramificationIdx_dvd_differentIdeal`,
  consumed in `differentIdeal_exponent_le` below;
* `f = 1` (any ramification) —
  `differentIdeal_exponent_le_wild_of_residueDegreeOne` above, by an
  elementary global route with digits in `ℤ`;
* the Eisenstein packaging and the valuation arithmetic — the four
  theorems below.

## THE 2026-07-26 GENERATOR CUT IS REVERTED (same day)

For part of 2026-07-26 this theorem was PROVEN over
`exists_generator_minpolyDerivative_le_of_wild`, itself proven over
two further leaves `exists_generator_conductor_notLE` (local
monogenicity at `Q`) and `differentIdeal_exponent_le_serre`.  All
three declarations are now DELETED, for two independent reasons.

**1. The cut was a net loss.**  By mathlib's
`conductor_mul_differentIdeal`, `(F'(x)) = 𝔠(x)·𝔡`, so
`ord_Q (F'(x)) = ord_Q 𝔠(x) + d`.  The bound is ATTAINED (measurement
below), so demanding a generator with
`ord_Q (F'(x)) ≤ e − 1 + e·v_q(e)` FORCES `ord_Q 𝔠(x) = 0` — i.e. the
generator-shaped leaf implied BOTH this inequality AND local
monogenicity at `Q`, strictly more than the tree needs.  The
local-field theory the cut was made to avoid ((M1), the different
under localization) had merely been swapped for other local-field
theory ((M4), monogenicity of a complete DVR extension); it was
relocated, not removed.

**2. `differentIdeal_exponent_le_serre` re-stated an already-proven
theorem.**  Its statement was `differentIdeal_exponent_le` below,
verbatim up to the `HeightOneSpectrum`-versus-`Ideal` packaging — and
that theorem is PROVEN, over this leaf.  So the cut introduced a fresh
`sorry` UNDERNEATH its own consequence.  No Lean cycle resulted (the
leaf was sorried outright and the build stayed green), but it was
circular bookkeeping and it inflated the frontier by one.

## REFUTED: THE UNIFORMIZER / APPROXIMATE-TEICHMÜLLER ROUTE

Measured in PARI/GP on `K = ℚ(√2,√5)`, `q = 2`, the unique prime `Q`
above `2`, `e = f = 2`, different `Q³·(prime over 5)`; so `d = 3` and
the bound `e − 1 + e·v_2(e) = 3` is SHARP.  Exhaustive search over the
box `[−3,3]⁴` of integral-basis coordinates:

* over ALL generators, `min ord_Q (F'(x)) = 3` — the bound, ATTAINED;
* over generators with `ord_Q x = 1` (a UNIFORMIZER),
  `min ord_Q (F'(x)) = 5 = d + e·(f−1)`;
* over generators with `ord_Q x = 0` (a `Q`-UNIT),
  `min ord_Q (F'(x)) = 3`.

So NO uniformizer generator can meet the bound when `f > 1`:
`ord_Q 𝔠(x) = e(f−1) > 0` for every one of them.  That kills the
recorded "replace the digit ring `ℤ` by `A = ℤ[u]` for an approximate
Teichmüller lift `u`, then run steps 3–6 of the `f = 1` route" attack
at three separate points:

* its generator is a uniformizer by construction
  (`exists_generator_uniformizer_at`);
* structurally, with `x = π` a uniformizer `ord_Q F(0) = e·f` while
  `ord_Q g(0) = e` for the degree-`e` Eisenstein approximant `g`, so
  the cofactor `H = F /ₘ g` has `ord_Q H(0) = e(f−1) ≠ 0`, and the
  `f = 1` proof's step "the cofactor is a `Q`-unit" — the step that
  converts `ord_Q F'(x)` into `ord_Q g'(π)` — fails by exactly the
  measured deficit;
* at the CORRECT generator `x = u + π` (a `Q`-unit) the `f = 1`
  route's RIGIDITY input dies too: it needs the terms `a_i x^i`,
  `i < e`, to have pairwise distinct `Q`-orders mod `e`, which holds
  because `ord_Q x = 1`; at a `Q`-unit every such term has order
  `≡ 0 (mod e)` and the distinct-residues argument is vacuous.

The old note's "the extra work is the passage from `π` to `x = u + π`"
is not extra work — it is the whole obstruction.

Do NOT retry the digit-expansion attack refuted on
`exists_eisensteinDerivative_dvd_of_wild` below either (`K = ℚ(√2)`,
`q = 2`, `π = √2`, `a₁ = 2`, `a₀ = −2−2√2`): coefficients of `Q`-order
in `e·ℤ` are strictly weaker than coefficients in the maximal
unramified subring.

**One salvaged observation, corrected.**  `A = ℤ[u]` needs an
approximate Teichmüller lift for the RING but NOT for the ℤ-MODULE:
for ANY lifts `w₀,…,w_{f−1} ∈ 𝓞_K` of an `𝔽_q`-basis of `𝓞_K/Q`, the
ℤ-module `D = ℤw₀ + ⋯ + ℤw_{f−1}` already surjects onto `𝓞_K/Q` and
has `ord_Q` EXACTLY in `e·ℤ` on `D ∖ {0}` (write `a = q^μ b` with `μ`
minimal; `b̄ ≠ 0` by independence, so `ord_Q a = e·μ`) — no Hensel
lifting, no precision loss.  Products leave `D`, which is why the RING
genuinely needs the Teichmüller condition, and why the polynomial
division of the `f = 1` route cannot be run inside `D`.

## THE TRACE-DUAL ROUTE, CARRIED OUT (2026-07-27)

The route recorded here on 2026-07-26 as "to try next" turned out to
need NO new theory whatsoever, because mathlib carries a sharper handle
than `differentialIdeal_le_iff`:
`not_dvd_differentIdeal_of_intTrace_not_mem` in
`Mathlib/RingTheory/DedekindDomain/Different.lean`.  For ANY ideal `p`
of `A` — **primality is not required, and that is exactly what makes
`p = (q^k)` admissible** — and any factorization `P·J = p·B`, it says

  `(∃ x ∈ J, Tr_{B/A}(x) ∉ p)  →  ¬ P ∣ 𝔡_{B/A}`.

Take `A = ℤ`, `B = 𝓞_K`, `k = v_q(e) + 1`, `p = (q^k)`, `P = Q^{e·k}`,
and `J` the cofactor of `Q^{e·k}` in `q^k·𝓞_K` (it exists because
`ord_Q q = e`, by `intValuation_natCast_eq_exp_ramificationIdx` above).
Then `¬ Q^{e·k} ∣ 𝔡` together with `hd : Q^d ∣ 𝔡` forces
`d < e·k = e·v_q(e) + e`, i.e. exactly `d ≤ e − 1 + e·v_q(e)`.  No
fractional ideals, no explicit `y = u/q^{v_q(e)+1}`, no
`differentialIdeal_le_iff` bookkeeping — the mathlib lemma absorbs all
of it.  What is left is the trace witness, which is now the sole leaf
`exists_intTrace_not_mem_span_of_ramificationIdx` above; the elementary
finite-ring proof of THAT is written out on its own docstring, and it
needs neither local fields, nor Serre's (M2), nor local monogenicity.

**Two hypotheses of this theorem are unused, and that is not vacuity.**
The leaf above is the general statement, so `hwild` and `hres` are
never consumed here.  The conclusion is still the full classical bound;
what has gone away is the CASE SPLIT, which was an artefact of the
earlier generator/digit-expansion routes and not of the mathematics.
`differentIdeal_exponent_le` below still assembles the three cases as
before, so nothing downstream changes.

## THE SECOND ROUTE (BASE CHANGE TO `ℚ(ζ_{q^f−1})`) IS RETIRED

It was: let `F₀ = ℚ(ζ_m)`, `m = q^f − 1`, `E = K·F₀`, `Q̃ ∣ Q`,
`𝔓 = Q̃ ∩ 𝓞_{F₀}`; then `e(Q̃∣Q) = f(Q̃∣Q) = 1`, so `e(Q̃∣𝔓) = e` and
`f(Q̃∣𝔓) = 1`, and two applications of
`differentIdeal_eq_differentIdeal_mul_differentIdeal` with
`not_dvd_differentIdeal_iff` killing the unramified factors reduce to
the `f = 1` case over `𝓞_{F₀}`.  The route is correct but its price —
generalizing the whole `f = 1` chain from base `ℤ` to a base where `𝔓`
need not be principal, plus constructing the compositum — is now
strictly wasted work: the trace route above closes the leaf with a
mathlib lemma and a finite-ring argument.  Recorded here so nobody
re-derives it.

Both-ways audit: an inequality between natural numbers, the wild
`f > 1` instance of a classical theorem.  Not vacuous — the bound is
ATTAINED at `K = ℚ(√2,√5)`, `q = 2`, where `e = f = 2` and `d = 3`, a
genuine wild `f > 1` instance, so the two hypotheses do not empty the
statement; and not stronger than needed — `differentIdeal_exponent_le`
below is exactly this bound with the three proven cases filled in. -/
theorem differentIdeal_exponent_le_wild_of_residueDegreeGtOne
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hwild : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (hres : ¬ ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (d : ℕ) (hd : v.asIdeal ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ e - 1 + e * e.factorization q := by
  classical
  set R := NumberField.RingOfIntegers K with hR
  set Q := v.asIdeal with hQ
  set k := e.factorization q + 1 with hkdef
  -- `ord_Q (q) = e`, hence `e ≥ 1`
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he1 : 1 ≤ e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0)
  have hordq : v.intValuation ((q : ℕ) : R) = WithZero.exp (-(e : ℤ)) := by
    have h1 := intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem q hq.ne_zero
    rwa [hq.factorization_self, mul_one, ← he] at h1
  -- `Q ^ (e·k) ∣ (q^k)`, giving the cofactor `J`
  have hmemek : ((q : ℕ) : R) ^ k ∈ Q ^ (e * k) := by
    have h1 : ((q : ℕ) : R) ∈ Q ^ e := by
      rw [← v.intValuation_le_pow_iff_mem, hordq]
    have h2 := Ideal.pow_mem_pow h1 k
    rwa [← pow_mul] at h2
  have hdvd : Q ^ (e * k) ∣ Ideal.span {((q : ℕ) : R) ^ k} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hmemek
  obtain ⟨J, hJ⟩ := hdvd
  obtain ⟨x, hxJ, hxtr⟩ :=
    exists_intTrace_not_mem_span_of_ramificationIdx K q hq v hmem e he k hkdef J hJ
  -- transport the factorization to the shape mathlib wants
  have hmapeq : Q ^ (e * k) * J
      = Ideal.map (algebraMap ℤ R) (Ideal.span {((q : ℤ) ^ k)}) := by
    rw [← hJ, Ideal.map_span]
    congr 1
    simp
  have hnd : ¬ Q ^ (e * k) ∣ differentIdeal ℤ R :=
    not_dvd_differentIdeal_of_intTrace_not_mem ℤ (Q ^ (e * k)) J hmapeq x hxJ hxtr
  by_contra hcon
  rw [Nat.not_le] at hcon
  refine hnd (dvd_trans (pow_dvd_pow Q ?_) hd)
  have hek : e * k = e * e.factorization q + e := by rw [hkdef]; ring
  omega

/-- **The local Eisenstein presentation of the different at a wild
prime of residue degree `> 1`** (PROVEN 2026-07-26 over
`differentIdeal_exponent_le_wild_of_residueDegreeGtOne` above, which is
itself PROVEN since 2026-07-27 over the trace-witness leaf
`exists_intTrace_not_mem_span_of_ramificationIdx` — the cluster's only
remaining sorry).
Statement identical to `exists_eisensteinDerivative_dvd_of_wild` below,
with the extra hypothesis `hres` that `𝓞_K/Q ≠ 𝔽_q`, i.e.
`f(Q∣q) > 1`.

The proof is the observation — already used by the `f = 1` branch of
`exists_eisensteinDerivative_dvd_of_wild` — that this statement is
EQUIVALENT to the numerical bound `d ≤ e − 1 + e·v_q(e)`: given the
bound, the trivial witness (`π` any uniformizer, `a = (0,…,0,1)`)
collapses the sum to `e·π^{e−1}`, whose `Q`-order is exactly
`e·v_q(e) + e − 1 ≥ d`.  So the Eisenstein packaging carries no content
beyond the inequality, and the cut of 2026-07-26 moves the node onto
the inequality, where the missing mathematics actually lives.  (This is
also why the digit-expansion attack refuted on
`exists_eisensteinDerivative_dvd_of_wild` could satisfy every clause of
this statement and still fail: the clauses are not the content.)

Where the `f = 1` route breaks, for the record: step 2 of
`differentIdeal_exponent_le_wild_of_residueDegreeOne` (the
integer-coefficient digit expansion) uses `𝓞_K/Q = 𝔽_q` to pick each
digit in `ℤ`; for `f > 1` the digits must come from the maximal
unramified subring `𝓞_{L₀}`, which has no *exact* global avatar.  The
approximate-avatar route is REFUTED; the routes that remain open are
recorded on `differentIdeal_exponent_le_wild_of_residueDegreeGtOne`
above, the trace-dual one being the most promising. -/
theorem exists_eisensteinDerivative_dvd_of_wild_of_residueDegreeGtOne
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hwild : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (hres : ¬ ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (d : ℕ) (hd : v.asIdeal ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    ∃ π : NumberField.RingOfIntegers K, ∃ a : ℕ → NumberField.RingOfIntegers K,
      v.intValuation π = WithZero.exp (-1 : ℤ) ∧
      a e = 1 ∧
      (∀ i, 0 < i → i < e → v.intValuation (a i) = 0 ∨
        ∃ c : ℕ, v.intValuation (a i) = WithZero.exp (-((e * c : ℕ) : ℤ))) ∧
      v.asIdeal ^ d ∣ Ideal.span {∑ j ∈ Finset.range e,
        ((j + 1 : ℕ) : NumberField.RingOfIntegers K) * a (j + 1) * π ^ j} := by
  classical
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he0 : 0 < e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0)
  have hbound :=
    differentIdeal_exponent_le_wild_of_residueDegreeGtOne K q hq v hmem hwild hres e he d hd
  -- The bound is all there is: the trivial witness `a = (0, …, 0, 1)`
  -- collapses the sum to `e·π^{e−1}`, of `Q`-order `e·v_q(e) + e − 1`.
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨π, Function.update (fun _ : ℕ => (0 : NumberField.RingOfIntegers K)) e 1, hπ,
    Function.update_self _ _ _, ?_, ?_⟩
  · intro i _ hie
    left
    rw [Function.update_of_ne (by omega)]
    simp
  · have hsum : ∑ j ∈ Finset.range e,
        ((j + 1 : ℕ) : NumberField.RingOfIntegers K)
          * Function.update (fun _ : ℕ => (0 : NumberField.RingOfIntegers K)) e 1 (j + 1)
          * π ^ j
        = ((e : ℕ) : NumberField.RingOfIntegers K) * π ^ (e - 1) := by
      rw [Finset.sum_eq_single (e - 1)]
      · rw [Nat.sub_add_cancel he0, Function.update_self, mul_one]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        rw [Function.update_of_ne (by omega)]
        simp
      · intro hcon
        exact absurd (Finset.mem_range.mpr (by omega)) hcon
    rw [hsum, ← v.intValuation_le_pow_iff_dvd]
    have hve : v.intValuation ((e : ℕ) : NumberField.RingOfIntegers K)
        = WithZero.exp (-((e * e.factorization q : ℕ) : ℤ)) := by
      rw [intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem e (by omega), ← he]
    rw [map_mul, map_pow, hve, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      WithZero.exp_le_exp]
    have hcast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
      have h1 : 1 ≤ e := he0
      push_cast [Nat.cast_sub h1]
      ring
    have hd' : (d : ℤ) ≤ ((e - 1 : ℕ) : ℤ) + (e : ℤ) * (e.factorization q : ℤ) := by
      exact_mod_cast hbound
    rw [hcast] at hd'
    rw [nsmul_eq_mul, hcast]
    push_cast
    linarith

/-- **(M1)+(M2)+(M3) The local Eisenstein presentation of the different
at a wild prime** (PROVEN 2026-07-26 over the two residue-degree cases
`differentIdeal_exponent_le_wild_of_residueDegreeOne` and
`exists_eisensteinDerivative_dvd_of_wild_of_residueDegreeGtOne` above;
it inherits its position under `differentIdeal_exponent_le_wild`, hence
under the whole Hermite–Minkowski cut of
`finite_setOf_isHardlyRamified`).

Statement: at a prime `Q` of `𝓞_K` over the rational prime `q`, with
`e = e(Q∣q)`, if `Q^d ∣ 𝔡_{K/ℚ}` then there are a uniformizer `π ∈ 𝓞_K`
at `Q` (`ord_Q π = 1`) and "coefficients" `a : ℕ → 𝓞_K` with `a e = 1`,
each `a i` for `0 < i < e` having `Q`-order in `e·ℤ` (or being zero at
`Q`), such that

  `Q^d ∣ (g'(π))`,  where  `g'(π) = Σ_{j<e} (j+1)·a_{j+1}·π^j`.

This is precisely Serre, *Corps Locaux* I §6 Prop. 18 + III §6 Prop. 12
transported back to the global ring, i.e. the bundle (M1)–(M3) of the
route recorded on `differentIdeal_exponent_le_wild`:

* **(M1) `differentIdeal` under localization/completion** — that
  `ord_Q 𝔡_{𝓞_K/ℤ}` is the different exponent of the local extension
  `ℤ_q → 𝓞_{K_Q}`.  mathlib has the different only for a *global*
  Dedekind pair and nothing relating it to one prime; this is the gate
  on everything else and the first thing to build.
* **(M2) the maximal unramified subextension** `ℚ_q ⊆ L₀ ⊆ K_Q`, with
  `K_Q/L₀` totally ramified of degree `e`; the tower formula
  `differentIdeal_eq_differentIdeal_mul_differentIdeal` together with
  "unramified ⟺ does not divide the different"
  (`not_dvd_differentIdeal_iff`) discards the `L₀/ℚ_q` factor.  This is
  what makes the coefficients' orders lie in `e·ℤ`: they come from
  `𝓞_{L₀}`, on which `ord_Q` takes values in `e·ℤ`.
* **(M3) monogenicity of a totally ramified extension of DVRs**
  (Serre I §6 Prop. 18): `𝓞_{K_Q} = 𝓞_{L₀}[π]` for any uniformizer `π`,
  whose minimal polynomial `g` over `𝓞_{L₀}` is Eisenstein of degree
  `e`, and `𝔡 = (g'(π))` by `conductor_mul_differentIdeal` with unit
  conductor.  Nakayama suffices — completeness is not needed — since
  `𝓞_{K_Q}/𝔪_{L₀}𝓞_{K_Q}` is generated by `π̄` over the (common)
  residue field.

Finally the data are pushed back to `𝓞_K` by approximation: `ord_Q`
only sees a bounded number of `Q`-adic digits, so `π` and the `a_i` may
be taken in `𝓞_K` without changing any of the orders involved.

Faithfulness: the statement is *equivalent in strength* to the wild
bound — a prover of it must do the local work — but it is the honest
joint, because everything downstream of it (the three lines of
valuation arithmetic) is proven in
`differentIdeal_exponent_le_wild` below.  It is not vacuous: `a e = 1`
pins the extremal term to `e·π^{e−1}`, whose `Q`-order is exactly
`e·v_q(e) + e − 1`, so no junk witness can satisfy the last clause.

**REFUTED ATTACK — READ THIS BEFORE TRYING THE OBVIOUS ONE
(2026-07-26).**  The natural attempt is to build `π` and the `a_i` by a
`Q`-adic *digit expansion*: pick a uniformizer `π`, and peel digits off
`π^e` using mathlib's `exists_intValuation_mul_sub_lt`, recording each
digit as `y·q^k` (so its order `e·k` automatically lies in `e·ℤ`, which
is all the third clause above asks for).  That construction is easy —
it was written and machine-checked — and it **does not prove this
leaf**: the coefficients it produces satisfy every stated clause but
can violate the last one.

Explicit counterexample (verified in PARI/GP).  `K = ℚ(√2)`, `q = 2`,
`Q = (√2)`, `e = 2`, `f = 1`; the different is `Q^3`, so `d = 3` is
admissible.  Take `π = √2`, `a₂ = 1`, `a₁ = 2`, `a₀ = −2 − 2√2`.  Then
`ord_Q a₁ = ord_Q a₀ = 2 ∈ 2ℤ`, `ord_Q π = 1`, and the associated
`g = X² + 2X − 2 − 2√2` even satisfies `g(π) = 0` **exactly** — so this
is a perfect Eisenstein-shaped relation by every criterion in the
statement — yet `g'(π) = 2 + 2√2` has `ord_Q = 2 < 3 = d`, so
`Q^d ∤ (g'(π))`.  The good witness is `a₀ = −2, a₁ = 0`, giving
`g = X² − 2` and `ord_Q g'(π) = 3`.

Moral: "coefficients of `Q`-order in `e·ℤ`" is strictly weaker than
"coefficients in the maximal unramified subring", and only the latter
makes `ord_Q g'(π)` equal to the different exponent.  (M2) is therefore
not a convenience — it is the whole content, and any route that skips
it is wrong rather than merely incomplete.  The `f = 1` case escapes
because there the unramified subring is `ℤ_q`, whose global avatar `ℤ`
does exist; see
`differentIdeal_exponent_le_wild_of_residueDegreeOne`. -/
theorem exists_eisensteinDerivative_dvd_of_wild
    (K : Type*) [Field K] [NumberField K] (q : ℕ) (hq : q.Prime)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmem : (q : NumberField.RingOfIntegers K) ∈ v.asIdeal)
    (hwild : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (e : ℕ) (he : e = Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) v.asIdeal)
    (d : ℕ) (hd : v.asIdeal ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    ∃ π : NumberField.RingOfIntegers K, ∃ a : ℕ → NumberField.RingOfIntegers K,
      v.intValuation π = WithZero.exp (-1 : ℤ) ∧
      a e = 1 ∧
      (∀ i, 0 < i → i < e → v.intValuation (a i) = 0 ∨
        ∃ c : ℕ, v.intValuation (a i) = WithZero.exp (-((e * c : ℕ) : ℤ))) ∧
      v.asIdeal ^ d ∣ Ideal.span {∑ j ∈ Finset.range e,
        ((j + 1 : ℕ) : NumberField.RingOfIntegers K) * a (j + 1) * π ^ j} := by
  classical
  by_cases hres : ∀ y : NumberField.RingOfIntegers K,
      ∃ c : ℤ, y - (c : NumberField.RingOfIntegers K) ∈ v.asIdeal
  swap
  · exact exists_eisensteinDerivative_dvd_of_wild_of_residueDegreeGtOne
      K q hq v hmem hwild hres e he d hd
  -- Residue degree one.  The bound holds, so the *trivial* witness
  -- `a = (0, …, 0, 1)` works: the sum collapses to `e·π^{e−1}`, whose
  -- `Q`-order is exactly `e·v_q(e) + e − 1 ≥ d`.
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff v.isPrime.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have he0 : 0 < e := by
    rw [he]
    exact Nat.pos_of_ne_zero
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal hspan0)
  have hbound :=
    differentIdeal_exponent_le_wild_of_residueDegreeOne K q hq v hmem hres e he d hd
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨π, Function.update (fun _ : ℕ => (0 : NumberField.RingOfIntegers K)) e 1, hπ,
    Function.update_self _ _ _, ?_, ?_⟩
  · intro i _ hie
    left
    rw [Function.update_of_ne (by omega)]
    simp
  · have hsum : ∑ j ∈ Finset.range e,
        ((j + 1 : ℕ) : NumberField.RingOfIntegers K)
          * Function.update (fun _ : ℕ => (0 : NumberField.RingOfIntegers K)) e 1 (j + 1)
          * π ^ j
        = ((e : ℕ) : NumberField.RingOfIntegers K) * π ^ (e - 1) := by
      rw [Finset.sum_eq_single (e - 1)]
      · rw [Nat.sub_add_cancel he0, Function.update_self, mul_one]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        rw [Function.update_of_ne (by omega)]
        simp
      · intro hcon
        exact absurd (Finset.mem_range.mpr (by omega)) hcon
    rw [hsum, ← v.intValuation_le_pow_iff_dvd]
    have hve : v.intValuation ((e : ℕ) : NumberField.RingOfIntegers K)
        = WithZero.exp (-((e * e.factorization q : ℕ) : ℤ)) := by
      rw [intValuation_natCast_eq_exp_ramificationIdx K q hq v hmem e (by omega), ← he]
    rw [map_mul, map_pow, hve, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      WithZero.exp_le_exp]
    have hcast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by
      have h1 : 1 ≤ e := he0
      push_cast [Nat.cast_sub h1]
      ring
    have hd' : (d : ℤ) ≤ ((e - 1 : ℕ) : ℤ) + (e : ℤ) * (e.factorization q : ℤ) := by
      exact_mod_cast hbound
    rw [hcast] at hd'
    rw [nsmul_eq_mul, hcast]
    push_cast
    linarith

/-- **The WILD different-exponent bound at a prime** (PROVEN 2026-07-26
over the single leaf `exists_eisensteinDerivative_dvd_of_wild`, which
inherits its position as the *single* arithmetic leaf of the
Hermite–Minkowski cut of `finite_setOf_isHardlyRamified`; Serre,
*Corps Locaux* III §6 Prop. 13, wild half): for a number field `K`, a
rational prime `q` and a prime `Q` of `𝓞_K` over `q` whose
ramification index `e = e(Q∣q)` is divisible by `q`, every `d` with
`Q^d ∣ 𝔡_{K/ℚ}` satisfies `d ≤ e − 1 + e·v_q(e)`.

Note `v_Q(q) = e`, so `e − 1 + e·v_q(e)` is Serre's `e − 1 + v_Q(e)`
verbatim; the bound is SHARP (attained by `ℚ(2^{1/4})` at `q = 2`,
where `e = 4`, `v_2(e) = 2` and `d = 11 = 3 + 8`; also by `ℚ(√2)` at
`q = 2`, `d = 3 = 1 + 2`).  Checked numerically against PARI/GP over
701 (field, prime-above-`q`) pairs of degrees 2–6 at `q ≤ 7`: no
violation, 293 of them sharp.

The TAME half — `q ∤ e`, where the bound reads `d ≤ e − 1` — is PROVEN
in `ModThree.lean` as `not_pow_ramificationIdx_dvd_differentIdeal`
(mathlib supplies the matching lower half
`pow_sub_one_dvd_differentIdeal`) and is discharged here in
`differentIdeal_exponent_le`; only the wild case is left open, which is
why this leaf carries `hwild` as a hypothesis.

The cut of 2026-07-26 splits the classical proof into the part that
needs local-field theory mathlib does not have and the part that is
pure valuation arithmetic, and PROVES the second part here:

* the local half — reaching an Eisenstein presentation of the
  different at `Q` — is the leaf
  `exists_eisensteinDerivative_dvd_of_wild` above, which bundles
  Serre's (M1) localization/completion of `differentIdeal`, (M2) the
  maximal unramified subextension, and (M3) monogenicity of a totally
  ramified extension of DVRs.  Its docstring records the route.
* the arithmetic half is the proof below, over the PROVEN
  `valuation_term_le_valuation_sum` (Serre's (M4), the ultrametric
  distinct-valuations lemma) and the PROVEN
  `intValuation_natCast_eq_exp_ramificationIdx` (`ord_Q(m) = e·v_q(m)`
  for a rational integer `m`).

Concretely, with `g = X^e + a_{e−1}X^{e−1} + ⋯ + a_0` Eisenstein over
the maximal unramified subring, every nonzero value of `ord_Q` on that
subring lies in `e·ℤ` (total ramification), and so does `ord_Q` of a
rational integer, so
`ord_Q(i·a_i·π^{i−1}) ≡ i − 1 (mod e)` for `1 ≤ i ≤ e`: the `e`
summands of `g'(π) = e·π^{e−1} + Σ_{i<e} i·a_i·π^{i−1}` have PAIRWISE
DISTINCT orders, whence `ord_Q(g'(π))` is their minimum, which is at
most the `i = e` term `ord_Q(e·π^{e−1}) = e·v_q(e) + e − 1`.  (Terms
whose coefficient vanishes are dropped first — that is exactly why
`valuation_term_le_valuation_sum` only demands distinctness among the
terms of nonzero valuation.)

Alternative route, entirely inside the material already PROVEN in
`ModThree.lean` but only for the Galois case, and needing its own
missing piece: for `K/ℚ` Galois,
`le_sum_card_inertia_pow_of_pow_dvd_differentIdeal` gives
`d ≤ Σ_{i<N}(#G_i − 1)` as soon as `G_N = 1`, so all that is missing
is **(M5) a bound on the last ramification jump** — `G_i = 1` for
`i > e/(q−1)`, say `(Q^(m+1)).inertia = ⊥` for `m = [K:ℚ]`.  (M5) is
essentially equivalent to this leaf, so it is not a cheaper target;
and reducing a general `K` to its Galois closure would additionally
need **(M6)** the tower discriminant formula
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
(mathlib has it) together with a degree bound
`[normalClosure ℚ K : ℚ] ≤ n!` (mathlib does not).

Both-ways audit: an inequality between natural numbers attached to a
number field, classically true as cited and numerically corroborated
above; no representation-theoretic hypotheses, no vacuity concerns —
the conclusion genuinely constrains `𝔡_{K/ℚ}` (its failure would make
`v_q(discr K)` unbounded on fields of bounded degree, contradicting
the sharp cases listed). -/
theorem differentIdeal_exponent_le_wild (K : Type*) [Field K]
    [NumberField K] (q : ℕ) (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (q : NumberField.RingOfIntegers K) ∈ Q)
    (hwild : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q)
    (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
      Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := by
  classical
  set R := NumberField.RingOfIntegers K
  have hpZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQ.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hmap0 : (Ideal.span {((q : ℕ) : ℤ)}).map (algebraMap ℤ R) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan0
  have hQ0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hmap0
    (Ideal.map_le_of_le_comap (Q.over_def (Ideal.span {((q : ℕ) : ℤ)})).le)
  set v : HeightOneSpectrum R := ⟨Q, hQ, hQ0⟩
  have hvQ : v.asIdeal = Q := rfl
  set e := Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q with hedef
  have he0 : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
  obtain ⟨π, a, hπ, hae, hacoef, hgd⟩ :=
    exists_eisensteinDerivative_dvd_of_wild K q hq v (hvQ ▸ hmem) (hvQ ▸ hwild) e
      (hvQ ▸ hedef) d (hvQ ▸ hd)
  set F : ℕ → R := fun j => ((j + 1 : ℕ) : R) * a (j + 1) * π ^ j with hFdef
  have hgd' : Q ^ d ∣ Ideal.span {∑ j ∈ Finset.range e, F j} := hgd
  have hFval : ∀ j : ℕ, v.intValuation (F j) =
      v.intValuation (((j + 1 : ℕ)) : R) * v.intValuation (a (j + 1)) *
        (v.intValuation π) ^ j := by
    intro j; simp only [hFdef, map_mul, map_pow]
  have hexpπ : ∀ j : ℕ, (v.intValuation π) ^ j = WithZero.exp (-(j : ℤ)) := by
    intro j
    rw [hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hje : (e - 1) + 1 = e := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero he0)
  -- the extremal term `e·π^{e−1}`, of `Q`-order `e·v_q(e) + e − 1`
  have hlast : v.intValuation (F (e - 1)) =
      WithZero.exp (-((e * e.factorization q + (e - 1) : ℕ) : ℤ)) := by
    have h1 := intValuation_natCast_eq_exp_ramificationIdx K q hq v (hvQ ▸ hmem) ((e - 1) + 1)
      (Nat.succ_ne_zero _)
    rw [hvQ, ← hedef, hje] at h1
    have h2 : v.intValuation (a e) = 1 := by rw [hae]; exact map_one _
    rw [hFval, hje, h1, h2, mul_one, hexpπ, ← WithZero.exp_add]
    congr 1
    rw [Nat.cast_add]
    ring
  -- every term of `g'(π)` has `Q`-order `≡ j (mod e)`
  have hterm : ∀ j, j < e → v.intValuation (F j) = 0 ∨
      ∃ c : ℕ, v.intValuation (F j) = WithZero.exp (-((e * c + j : ℕ) : ℤ)) := by
    intro j hj
    have h1 := intValuation_natCast_eq_exp_ramificationIdx K q hq v (hvQ ▸ hmem) (j + 1)
      (Nat.succ_ne_zero _)
    rw [hvQ, ← hedef] at h1
    by_cases hjq : j + 1 = e
    · right
      refine ⟨e.factorization q, ?_⟩
      rw [hjq] at h1
      have h2 : v.intValuation (a e) = 1 := by rw [hae]; exact map_one _
      rw [hFval, hjq, h1, h2, mul_one, hexpπ, ← WithZero.exp_add]
      congr 1
      rw [Nat.cast_add]
      ring
    · have hjlt : j + 1 < e := lt_of_le_of_ne (Nat.succ_le_of_lt hj) hjq
      rcases hacoef (j + 1) (Nat.succ_pos j) hjlt with h0 | ⟨c, hc⟩
      · left
        rw [hFval, h0, mul_zero, zero_mul]
      · right
        refine ⟨(j + 1).factorization q + c, ?_⟩
        rw [hFval, h1, hc, hexpπ, ← WithZero.exp_add, ← WithZero.exp_add]
        congr 1
        push_cast
        ring
  -- distinct residues mod `e` ⟹ pairwise distinct orders
  have hne : ∀ i ∈ Finset.range e, ∀ j ∈ Finset.range e, i ≠ j →
      v.intValuation (F i) ≠ 0 → v.intValuation (F j) ≠ 0 →
      v.intValuation (F i) ≠ v.intValuation (F j) := by
    intro i hi j hj hij hi0 hj0
    rw [Finset.mem_range] at hi hj
    rcases hterm i hi with h | ⟨c, hc⟩
    · exact absurd h hi0
    rcases hterm j hj with h' | ⟨c', hc'⟩
    · exact absurd h' hj0
    rw [hc, hc']
    intro hcon
    rw [WithZero.exp_inj, neg_inj] at hcon
    have hnat : (e * c + i : ℕ) = (e * c' + j : ℕ) := by exact_mod_cast hcon
    have := congrArg (fun n : ℕ => n % e) hnat
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact hij this
  -- assemble
  have hker : ∀ x : R, v.intValuation x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    exact v.intValuation_ne_zero x hx0 hx
  have hsum_le : v.intValuation (F (e - 1)) ≤ v.intValuation (∑ j ∈ Finset.range e, F j) :=
    valuation_term_le_valuation_sum v.intValuation hker F
      (Finset.mem_range.mpr (Nat.pred_lt he0)) hne
  have hdvd_le : v.intValuation (∑ j ∈ Finset.range e, F j) ≤ WithZero.exp (-(d : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd _ d).mpr hgd'
  rw [hlast] at hsum_le
  have hfin := le_trans hsum_le hdvd_le
  rw [WithZero.exp_le_exp] at hfin
  have hM : d ≤ e * e.factorization q + (e - 1) := by
    have h := neg_le_neg_iff.mp hfin
    exact_mod_cast h
  exact le_trans hM (le_of_eq (Nat.add_comm _ _))

/-- **The different-exponent bound at a prime** (PROVEN over the wild
leaf — Serre, *Corps Locaux* III §6 Prop. 13 in full): for a prime `Q`
of `𝓞_K` over the rational prime `q` with ramification index `e`,
every `d` with `Q^d ∣ 𝔡_{K/ℚ}` satisfies `d ≤ e − 1 + e·v_q(e)`.  The
tame case `q ∤ e` is `ModThree.lean`'s PROVEN
`not_pow_ramificationIdx_dvd_differentIdeal` (`¬ Q^e ∣ 𝔡`, so `d < e`,
and `v_q(e) = 0` makes the bound exactly `e − 1`); the wild case is
`differentIdeal_exponent_le_wild`. -/
theorem differentIdeal_exponent_le (K : Type*) [Field K]
    [NumberField K] (q : ℕ) (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (q : NumberField.RingOfIntegers K) ∈ Q) (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
      Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := by
  by_cases hw : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q
  · exact differentIdeal_exponent_le_wild K q hq Q hQ hmem hw d hd
  · have hnot := IsHardlyRamified.not_pow_ramificationIdx_dvd_differentIdeal
      K q hq Q hQ hmem hw
    have hlt : d < Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by
      by_contra hge
      exact hnot (dvd_trans (pow_dvd_pow Q (not_lt.mp hge)) hd)
    exact le_trans (Nat.le_pred_of_lt hlt) (Nat.le_add_right _ _)

/-- **Discriminant-exponent bound by the degree** (PROVEN 2026-07-25
over the wild different-exponent bound
`differentIdeal_exponent_le_wild`, which since 2026-07-26 is itself
PROVEN over the local Eisenstein leaf
`exists_eisensteinDerivative_dvd_of_wild` — the arithmetic leaf of the
Hermite–Minkowski cut of `finite_setOf_isHardlyRamified`): for a fixed
prime `q` and degree bound `n`, the exponent of `q` in the
discriminant of a number field of degree at most `n` is bounded by a
constant depending only on `q` and `n`; here `C = (n + 1)·n` works.

Proof (pure bookkeeping over the two per-prime inputs, no new
arithmetic): `ModThree.lean`'s PROVEN
`discr_factorization_le_of_forall_differentIdeal_pow_dvd` turns a
uniform per-prime bound `d_Q ≤ b·e_Q` into
`v_q(discr K) ≤ b·[K:ℚ]`; the per-prime bound is
`differentIdeal_exponent_le`, `d_Q ≤ e − 1 + e·v_q(e)`, together with
`e ≤ [K:ℚ] ≤ n` (mathlib's `Ideal.ramificationIdx_le_finrank`, through
the fundamental identity) and `v_q(e) < e ≤ n`
(`Nat.factorization_lt`), giving `b = n + 1`.  The constant `C` is
existentially quantified, so any correct route may sharpen it.

Both-ways audit: a plain universally quantified inequality about
number fields with an existential bound — classically true outright as
cited; no representation-theoretic hypotheses, no vacuity concerns.
Consumed by `finite_setOf_intermediateField_inertiaAt_le` at
`q ∈ {2, p}`. -/
theorem exists_discr_factorization_le_of_finrank_le (q n : ℕ)
    (hq : q.Prime) :
    ∃ C : ℕ, ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ))
      (hfd : FiniteDimensional ℚ K), Module.finrank ℚ K ≤ n →
      haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
      (NumberField.discr K).natAbs.factorization q ≤ C := by
  refine ⟨(n + 1) * n, fun K hfd hrank => ?_⟩
  haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
  have hqZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hspanMax : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      hqZ).isMaximal hspan0)
  -- the uniform per-prime different-exponent bound `d_Q ≤ (n + 1)·e_Q`
  have key : ∀ Q : Ideal (NumberField.RingOfIntegers K), Q.IsPrime →
      ((q : NumberField.RingOfIntegers K) ∈ Q) → ∀ d : ℕ,
      Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) →
      1 * d ≤ (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by
    intro Q hQ hmem d hd
    haveI := hQ
    haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
      (Ideal.liesOver_span_iff hQ.ne_top hqZ).mpr (by exact_mod_cast hmem)
    have he0 : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
    have hen : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≤ n :=
      le_trans (Ideal.ramificationIdx_le_finrank
        (S := NumberField.RingOfIntegers K) (K := ℚ) (L := K) Q) hrank
    have hv : (Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q).factorization q
        ≤ n := le_of_lt (lt_of_lt_of_le (Nat.factorization_lt q he0) hen)
    have hser := differentIdeal_exponent_le K q hq Q hQ hmem d hd
    calc 1 * d = d := one_mul d
      _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
          Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
            (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := hser
      _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q +
          Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q * n :=
        Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left _ hv)
      _ = (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by ring
  have hmain := IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd
    K q hq 1 (n + 1) key
  calc (NumberField.discr K).natAbs.factorization q
      = 1 * (NumberField.discr K).natAbs.factorization q := (one_mul _).symm
    _ ≤ (n + 1) * Module.finrank ℚ K := hmain
    _ ≤ (n + 1) * n := Nat.mul_le_mul_left _ hrank

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
