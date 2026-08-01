/-
NumberField/ArtinIdealMap.lean — own work for the Fermat project (not vendored
from the FLT project).
-/
module

public import Fermat.FLT.NumberField.HilbertClassFieldNormal
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# The Artin map of a GIVEN everywhere-unramified abelian extension

`Fermat/FLT/NumberField/UnramifiedClassFieldExistence.lean` carries
`exists_hilbertClassField_artinIso`, which CONSTRUCTS the Hilbert class field and its
Artin isomorphism. Its consumer in `Fermat/FLT/Modularity/Interface.lean` needs the same
theorem with the field handed in as a HYPOTHESIS — an abelian extension `L/K` unramified
at every finite prime with `#Gal(L/K) = h_K` — and phrased through the subtype

    {σ : M ≃ₐ[ℚ] M // ∀ z : CF, σ (jj z) = jj z}

so that no `Algebra CF ↥M` instance occurs in its statement. This file is that bridge.

## Main results

* `NumberField.isUnramifiedAtInfinitePlaces_of_isTotallyComplex` — over a totally complex
  base every infinite place of every extension is unramified. One line over
  `InfinitePlace.isUnramified_iff`, and it is what makes the cyclotomic hypothesis of the
  consumer do its work; see the audit correction below.
* `NumberField.isUnramifiedAt_of_forall_inertia_trivial` — trivial inertia at every
  nonzero prime implies unramified. This is `HilbertClassFieldNormal.lean`'s
  `isUnramifiedAt_of_inertia_trivial` with the two `IntermediateField` wrappers removed;
  the proof is that one verbatim.
* `NumberField.exists_artinClassGroupEquiv` — **the Artin isomorphism for a given `L`.**
  The first half of `exists_hilbertClassField_artinIso`'s proof, with `L` a hypothesis
  instead of a construction: RECIPROCITY (`exists_classGroupHom_eq_frobAt`) gives the
  homomorphism, CHEBOTAREV (`closure_frobAt_eq_top`) makes it surjective, and `hcard`
  turns surjective into bijective.
* `NumberField.natCard_quotient_under_eq_of_forall_pow` — the residue-field cardinality
  form of `ArtinSymbol.lean`'s `inertiaDeg_eq_one_of_forall_pow_natCard`. This is the
  step that upgrades an arithmetic Frobenius over `ℤ` to one over `𝓞 K`, and it is the
  whole of the "the degree-one condition is OBTAINED rather than assumed" paragraph in
  the consumer's docstring.
* `NumberField.exists_artinIdealMap_of_forall_inertia_trivial` — the consumer-shaped
  statement, in the `jj : CF →ₐ[ℚ] M` model with no `Algebra CF M` instance in sight.

## AUDIT CORRECTION (2026-07-31): the cyclotomic hypothesis of the consumer is NOT inert

`exists_artinIdealMap_of_unramifiedAbelian_normal` in `Modularity/Interface.lean` carries
`IsCyclotomicExtension {p} ℚ CF` under a docstring paragraph headed
"**`IsCyclotomicExtension {p} ℚ CF` is INERT here** and may be ignored: Artin reciprocity
holds over an arbitrary number field, so a prover who finds it easier may prove the
general statement and specialise."

**The general statement over an arbitrary number field is FALSE.** Reciprocity at modulus
`1` — the assertion that the Artin map kills the PRINCIPAL ideals, which is the consumer's
second clause — needs `L/K` unramified at the INFINITE places as well; without it the
Artin map kills only the totally positive principal ideals and factors through the NARROW
class group. Concretely, take `K` real quadratic with `Cl(𝓞 K) ≅ ℤ/2` and
`Cl⁺(𝓞 K) ≅ (ℤ/2)²`, write `Cl⁺ = ⟨s, t⟩` with `⟨t⟩ = ker(Cl⁺ ↠ Cl)`, and let `L` be the
class field of `⟨s⟩`. Then `L/K` is abelian, unramified at every FINITE prime, and
`#Gal(L/K) = 2 = h_K`, so every hypothesis of the consumer holds; but primes `𝔭, 𝔮` with
narrow classes `1` and `s` have the same Frobenius while their WIDE classes differ, which
refutes the second clause.

What rescues the consumer is exactly the hypothesis its docstring calls inert: for `p` an
odd prime `ℚ(ζ_p)` is TOTALLY COMPLEX, so there are no real places to ramify and
`IsUnramifiedAtInfinitePlaces` is automatic; and for `p = 2` we have `CF = ℚ`, whose class
number is `1`, so `hcard` forces `Gal(M/CF)` trivial and
`IsUnramifiedAtInfinitePlaces_of_odd_card_aut` applies. Both branches are discharged in
the consumer, which is why this file's main theorem takes the disjunction

    IsTotallyComplex CF ∨ Odd (Nat.card (ClassGroup (𝓞 CF)))

rather than an `IsUnramifiedAtInfinitePlaces` instance (which cannot even be *stated*
there, the statement carrying no `Algebra CF M`).

## Why the mathematics is not duplicated

Everything genuinely arithmetic is consumed from
`Fermat/FLT/NumberField/ArtinSymbol.lean`: `exists_classGroupHom_eq_frobAt` (RECIPROCITY)
and `closure_frobAt_eq_top` (CHEBOTAREV). Both are that file's own leaves, separately
owned, and NOTHING here re-proves either. The point of this file is that the consumer in
`Interface.lean` — an 85 000-line module that elaborates for the better part of an hour —
should not carry a second reciprocity development, which is what its own docstring warned
against ("price generalizing that value group before writing a second reciprocity
development").
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NumberField

section Archimedean

/-- **OVER A TOTALLY COMPLEX BASE EVERY INFINITE PLACE IS UNRAMIFIED** (PROVEN
2026-07-31).

`InfinitePlace.isUnramified_iff` reads `IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap
(algebraMap k K))`, and the right disjunct holds for every `w` as soon as `k` is totally
complex. This is the only thing the cyclotomic hypothesis of
`exists_artinIdealMap_of_unramifiedAbelian_normal` is for; see the module docstring. -/
theorem isUnramifiedAtInfinitePlaces_of_isTotallyComplex
    (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [IsTotallyComplex k] : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ => InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))⟩

end Archimedean

section InertiaConverse

/-- **TRIVIAL INERTIA AT EVERY NONZERO PRIME ⟹ UNRAMIFIED**, for an abstract Galois
extension of number fields (PROVEN 2026-07-31).

`Fermat/FLT/NumberField/HilbertClassFieldNormal.lean` proves this for
`K : IntermediateField ℚ ℚ̄` and `N : IntermediateField K ℚ̄`; the proof uses nothing about
the two wrappers, so it is repeated here verbatim at the generality the consumer needs
(where the base is `CF` with an `Algebra CF M` introduced inside the proof by `letI`, and
so is not an intermediate field of anything). Chain: `Ideal.card_inertia_eq_ramificationIdxIn`
with the inertia group killed by `hin`, then `Ideal.ramificationIdxIn_eq_ramificationIdx`
and `Ideal.ramificationIdx_eq_one_iff.mp`. -/
theorem isUnramifiedAt_of_forall_inertia_trivial
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (hin : ∀ (Q : Ideal (𝓞 L)), Q.IsPrime → Q ≠ ⊥ →
      ∀ τ : L ≃ₐ[K] L, (∀ x : 𝓞 L, τ • x - x ∈ Q) → τ = 1)
    (Q : Ideal (𝓞 L)) (hQp : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) Q := by
  classical
  haveI := hQp
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  set q : Ideal (𝓞 K) := Q.under (𝓞 K) with hq
  haveI : Q.LiesOver q := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[K] L)) q Q
  have hbot : Q.inertia (L ≃ₐ[K] L) = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => hin Q hQp hQ0 τ (fun x => hτ x)
  rw [hbot] at hcard
  have h1 : Ideal.ramificationIdxIn q (𝓞 L) = 1 := by
    rw [← hcard]; simp
  have h2 : Q.ramificationIdx (𝓞 K) = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q Q (L ≃ₐ[K] L)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

end InertiaConverse

section ArtinIso

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **THE ARTIN ISOMORPHISM OF A GIVEN EVERYWHERE-UNRAMIFIED ABELIAN EXTENSION OF DEGREE
`h_K`** (PROVEN 2026-07-31 over `ArtinSymbol.lean`'s two leaves and nothing else).

This is the first half of `exists_hilbertClassField_artinIso`, with `L` a HYPOTHESIS
rather than a construction and with the counting hypothesis in the exact form
`#Gal(L/K) = h_K` instead of the inequality that theorem obtains from the existence leaf.
The dictionary clause is not reproduced: no consumer of this file needs it.

* RECIPROCITY (`exists_classGroupHom_eq_frobAt`) gives `φ : Cl(𝓞 K) →* Gal(L/K)` with
  `φ [Q ∩ 𝓞 K] = frobAt K L Q`;
* CHEBOTAREV (`closure_frobAt_eq_top`) says the Frobenius elements generate `Gal(L/K)`,
  which makes `φ` surjective;
* `hcard` turns surjective into bijective.

`IsUnramifiedAtInfinitePlaces K L` is load-bearing and is RECIPROCITY's hypothesis, not a
technicality: see the module docstring for the real quadratic counterexample. -/
theorem exists_artinClassGroupEquiv [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (hcard : Nat.card (L ≃ₐ[K] L) = Nat.card (ClassGroup (𝓞 K))) :
    ∃ Art : ClassGroup (𝓞 K) ≃* (L ≃ₐ[K] L),
      ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsMaximal) (J : (Ideal (𝓞 K))⁰),
        (J : Ideal (𝓞 K)) = Q.under (𝓞 K) → Art (ClassGroup.mk0 J) = frobAt K L Q := by
  classical
  obtain ⟨φ, hfrob⟩ := exists_classGroupHom_eq_frobAt K L habel hunr
  have hunder : ∀ (Q : Ideal (𝓞 L)), Q.IsMaximal → Q.under (𝓞 K) ≠ ⊥ := by
    intro Q hQ
    exact Ideal.under_ne_bot (𝓞 K)
      (Ideal.bot_lt_of_maximal Q (NumberField.RingOfIntegers.not_isField L)).ne'
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.1 (top_le_iff.1 ?_)
    rw [← closure_frobAt_eq_top K L]
    refine (Subgroup.closure_le _).2 ?_
    rintro σ ⟨Q, hQ, -, rfl⟩
    exact ⟨ClassGroup.mk0 ⟨Q.under (𝓞 K), mem_nonZeroDivisors_of_ne_zero (hunder Q hQ)⟩,
      hfrob Q hQ _ rfl⟩
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).2 ⟨hsurj, hcard.symm⟩
  exact ⟨MulEquiv.ofBijective φ hbij, hfrob⟩

/-- **THE RESIDUE DEGREE IS ONE, IN CARDINALITY FORM** (PROVEN 2026-07-31).

`ArtinSymbol.lean`'s `inertiaDeg_eq_one_of_forall_pow_natCard` concludes
`q.inertiaDeg (𝓞 k) = 1`; what a Frobenius argument consumes is the equality of residue
CARDINALITIES, because `IsArithFrobAt` mentions the base only through the exponent
`Nat.card (𝓞 k ⧸ q.under (𝓞 k))`. `Ideal.cardQuot_pow_inertiaDeg` is the bridge. -/
theorem natCard_quotient_under_eq_of_forall_pow
    (k F : Type*) [Field k] [NumberField k] [Field F] [NumberField F] [Algebra k F]
    (q : Ideal (𝓞 F)) [q.IsMaximal]
    (h : ∀ z : 𝓞 F ⧸ q, z ^ (Nat.card (𝓞 k ⧸ q.under (𝓞 k))) = z) :
    Nat.card (𝓞 F ⧸ q) = Nat.card (𝓞 k ⧸ q.under (𝓞 k)) := by
  classical
  have hf := inertiaDeg_eq_one_of_forall_pow_natCard k F q h
  haveI : q.LiesOver (q.under (𝓞 k)) := ⟨rfl⟩
  have hpow := Ideal.cardQuot_pow_inertiaDeg (q.under (𝓞 k)) q
  rw [hf, pow_one] at hpow
  simpa [Submodule.cardQuot_apply] using hpow.symm

end ArtinIso

section Consumer

/-- skeleton -/
theorem exists_artinIdealMap_of_forall_inertia_trivial
    (CF : Type*) [Field CF] [NumberField CF]
    (M : Type*) [Field M] [NumberField M] [Algebra ℚ M] [IsGalois ℚ M]
    (jj : CF →ₐ[ℚ] M)
    (harch : IsTotallyComplex CF ∨ Odd (Nat.card (ClassGroup (𝓞 CF))))
    (hab : ∀ σ ρ : M ≃ₐ[ℚ] M, (∀ z : CF, σ (jj z) = jj z) →
      (∀ z : CF, ρ (jj z) = jj z) → σ * ρ = ρ * σ)
    (hunr : ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q ≠ ⊥ → ∀ σ : M ≃ₐ[ℚ] M,
      (∀ z : CF, σ (jj z) = jj z) → (∀ x : 𝓞 M, σ • x - x ∈ Q) → σ = 1)
    (hcard : Nat.card {σ : M ≃ₐ[ℚ] M // ∀ z : CF, σ (jj z) = jj z} =
      Nat.card (ClassGroup (𝓞 CF))) :
    ∃ art : (Ideal (𝓞 CF))⁰ → (M ≃ₐ[ℚ] M),
      (∀ (I : (Ideal (𝓞 CF))⁰) (z : CF), art I (jj z) = jj z) ∧
      (∀ I J : (Ideal (𝓞 CF))⁰, art I = art J →
        ClassGroup.mk0 I = ClassGroup.mk0 J) ∧
      (∀ Q : Ideal (𝓞 M), Q.IsPrime → ∀ σ : M ≃ₐ[ℚ] M,
        IsArithFrobAt (𝓞 ℚ) σ Q →
        (∀ z : CF, σ (jj z) = jj z) →
        ∀ I : (Ideal (𝓞 CF))⁰,
          Ideal.comap (NumberField.RingOfIntegers.mapRingHom (jj : CF →+* M)) Q =
            (I : Ideal (𝓞 CF)) →
          art I = σ) := by
  classical
  letI : Algebra CF M := jj.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ CF M := IsScalarTower.of_algebraMap_eq fun x => (jj.commutes x).symm
  haveI : FiniteDimensional CF M := FiniteDimensional.right ℚ CF M
  haveI : Normal CF M := Normal.tower_top_of_normal ℚ CF M
  haveI : IsGalois CF M := ⟨⟩
  let galEquiv : (M ≃ₐ[CF] M) ≃ {σ : M ≃ₐ[ℚ] M // ∀ z : CF, σ (jj z) = jj z} :=
    { toFun := fun τ => ⟨τ.restrictScalars ℚ, fun z => τ.commutes z⟩
      invFun := fun σ => { σ.1 with commutes' := σ.2 }
      left_inv := fun τ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  have habel : ∀ a b : M ≃ₐ[CF] M, a * b = b * a := by
    intro a b
    have h := hab (a.restrictScalars ℚ) (b.restrictScalars ℚ)
      (fun z => a.commutes z) (fun z => b.commutes z)
    ext x
    exact congrArg (fun f : M ≃ₐ[ℚ] M => f x) h
  have hin : ∀ (Q : Ideal (𝓞 M)), Q.IsPrime → Q ≠ ⊥ →
      ∀ τ : M ≃ₐ[CF] M, (∀ x : 𝓞 M, τ • x - x ∈ Q) → τ = 1 := by
    intro Q hQp hQ0 τ hτ
    have h := hunr Q hQp hQ0 (τ.restrictScalars ℚ) (fun z => τ.commutes z) (fun x => hτ x)
    ext x
    exact congrArg (fun f : M ≃ₐ[ℚ] M => f x) h
  have hunrCF : ∀ (Q : Ideal (𝓞 M)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 CF) Q := fun Q hQp hQ0 =>
    isUnramifiedAt_of_forall_inertia_trivial CF M hin Q hQp hQ0
  have hcardCF : Nat.card (M ≃ₐ[CF] M) = Nat.card (ClassGroup (𝓞 CF)) := by
    rw [Nat.card_congr galEquiv]; exact hcard
  haveI : IsUnramifiedAtInfinitePlaces CF M := by
    rcases harch with h | h
    · haveI := h
      exact isUnramifiedAtInfinitePlaces_of_isTotallyComplex CF M
    · exact IsUnramifiedAtInfinitePlaces_of_odd_card_aut (by rw [hcardCF]; exact h)
  obtain ⟨Art, hArt⟩ := exists_artinClassGroupEquiv CF M habel hunrCF hcardCF
  refine ⟨fun I => (galEquiv (Art (ClassGroup.mk0 I))).1,
    fun I z => (galEquiv (Art (ClassGroup.mk0 I))).2 z, ?_, ?_⟩
  · intro I J hIJ
    exact Art.injective (galEquiv.injective (Subtype.ext hIJ))
  · intro Q hQp σ hfrobσ hσfix I hI
    haveI := hQp
    have hI0 : (I : Ideal (𝓞 CF)) ≠ ⊥ := by
      simpa using mem_nonZeroDivisors_iff_ne_zero.mp I.2
    have hunder : (I : Ideal (𝓞 CF)) = Q.under (𝓞 CF) := hI.symm
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply hI0
      rw [hunder]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 CF) (𝓞 M))
    haveI : Q.IsMaximal := hQp.isMaximal hQ0
    have hres : ∀ z : 𝓞 CF ⧸ Q.under (𝓞 CF),
        z ^ (Nat.card (𝓞 ℚ ⧸ (Q.under (𝓞 CF)).under (𝓞 ℚ))) = z := by
      intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [Ideal.under_under]
      have h1 : σ • (algebraMap (𝓞 CF) (𝓞 M) y) -
          (algebraMap (𝓞 CF) (𝓞 M) y) ^ (Nat.card (𝓞 ℚ ⧸ Ideal.under (𝓞 ℚ) Q)) ∈ Q :=
        hfrobσ _
      have h2 : σ • (algebraMap (𝓞 CF) (𝓞 M) y) = algebraMap (𝓞 CF) (𝓞 M) y := by
        refine RingOfIntegers.ext ?_
        rw [coe_smul_ringOfIntegers]
        exact hσfix (y : CF)
      rw [h2] at h1
      rw [← map_pow, Ideal.Quotient.eq]
      refine Ideal.mem_comap.mpr ?_
      rw [map_sub, map_pow]
      have h3 := Q.neg_mem h1
      rwa [neg_sub] at h3
    have hNcard : Nat.card (𝓞 CF ⧸ Q.under (𝓞 CF)) = Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) := by
      have h := natCard_quotient_under_eq_of_forall_pow ℚ CF (Q.under (𝓞 CF)) hres
      rwa [Ideal.under_under] at h
    have hfrobCF : IsArithFrobAt (𝓞 CF) (galEquiv.symm ⟨σ, hσfix⟩) Q := by
      intro x
      rw [hNcard]
      exact hfrobσ x
    have huniq : galEquiv.symm ⟨σ, hσfix⟩ = frobAt CF M Q := by
      have hmem := IsArithFrobAt.mul_inv_mem_inertia hfrobCF (isArithFrobAt_frobAt CF M Q)
      exact mul_inv_eq_one.mp
        (hin Q hQp hQ0 (galEquiv.symm ⟨σ, hσfix⟩ * (frobAt CF M Q)⁻¹) (fun x => hmem x))
    have hArtI : Art (ClassGroup.mk0 I) = frobAt CF M Q := hArt Q ‹_› I hunder
    show ((galEquiv (Art (ClassGroup.mk0 I))).1 : M ≃ₐ[ℚ] M) = σ
    rw [hArtI, ← huniq, Equiv.apply_symm_apply]

end Consumer

end NumberField
