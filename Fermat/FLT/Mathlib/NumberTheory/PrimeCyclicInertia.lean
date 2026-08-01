module

/-
PrimeCyclicInertia.lean — own work for the Fermat project.

# A place of `F^D` realised by no place of `F^C` is INERT in `F^C/F^D`

This module carries the **arithmetic half** of one prime-degree cyclic step of
Arthur–Clozel solvable base change, peeled off the automorphic leaf
`exists_baseChangeHeckeField_of_prime_cyclic_step_of_inert`
(`Fermat/FLT/Modularity/KhareWintenberger.lean`).

That leaf's docstring named this peel as "the natural NEXT CUT", correctly
describing it as "ordinary ramification theory (`Ideal.sum_ramification_inertia`)
[needing] no automorphic input", and declined it "only because peeling it
requires the `L/M` tower instances, which this statement deliberately does not
carry".  **That cost estimate is right about the instances and wrong about
where they have to live**: the tower `F^D ⊆ F^C` is definable inside the PROOF,
so the statement below mentions only `Subgroup (Φ ≃ₐ[ℚ] Φ)` and the two fixed
fields, exactly the vocabulary the leaf already uses, and every instance is
introduced by `letI`/`haveI` in the proof body.  So no consumer pays for them.

## The two theorems

* `Fermat.absNorm_eq_pow_of_ne` — the general fact, in mathlib vocabulary: for a
  Galois extension `L/K` of number fields of PRIME degree `p`, a prime `v` of
  `𝓞 L` over `w` whose residue cardinality differs from that of `w` has
  `N v = N w ^ p`.  The residue degree `f` divides `p` because `e·f·g = p` for a
  Galois extension (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`,
  the fundamental identity), and `f ≠ 1` is exactly the hypothesis, so `f = p`.
  Note the argument never needs `e = 1` or `g = 1` separately, and never needs
  `N w ≥ 2`: `f = 1` contradicts the hypothesis on the nose.

  **Galois is load-bearing and cannot be dropped.**  Without it the fundamental
  identity is only `∑_{v | w} e_v f_v = p`, which at `p = 5` is satisfied by two
  primes with `(e, f) = (1, 2)` and `(1, 3)` — both have `f ≥ 2` and neither has
  `f = p`.  It is the uniformity of `f` across `v | w`, i.e. transitivity of the
  Galois action on the primes above `w`, that forces `g = 1`.

* `Fermat.exists_absNorm_eq_pow_of_prime_index` — the same statement in the
  fixed-field vocabulary of the descent step, with the finite exceptional set
  produced.  `S` is the set of places of `F^D` lying UNDER a place of `SL`; that
  is what makes the chosen `v` avoid `SL`, and it is why an exceptional set is
  needed at all.

## Why `IsGalois (F^D) (F^C)` is available

`C ≤ D` gives `F^D ≤ F^C` (`IntermediateField.fixedField_le`), and
`IntermediateField.extendScalars` presents `F^C` as an intermediate field of
`Φ/F^D` — with, crucially, `↥(extendScalars h)` DEFEQ to `↥(fixedField C)`, so
the algebra structure transfers by `inferInstanceAs` and the statement never has
to mention `extendScalars`.  Normality is then
`IntermediateField.normal_iff_forall_map_le'` plus the standard conjugation
argument: a `Φ ≃ₐ[F^D] Φ` restricts to an element of `D`
(`IntermediateField.fixingSubgroup_fixedField`), and `(C.subgroupOf D).Normal`
makes `σ⁻¹ τ σ ∈ C` for `τ ∈ C`, so `σ` preserves `fixedField C`.  The degree is
`Nat.card D / Nat.card C = p` by `IntermediateField.finrank_fixedField_eq_card`
twice, the tower formula, and Lagrange.

Separability is free (characteristic zero), so `Normal` upgrades to `IsGalois`.
-/

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace Fermat

open NumberField Ideal IntermediateField

/-- **A prime of prime-degree Galois extension whose residue cardinality moves is
INERT.**  For `L/K` Galois of prime degree `p` and `v` a prime of `𝓞 L` over `w`,
`N v ≠ N w` forces `N v = N w ^ p`.

The residue degree `f = inertiaDeg` satisfies `g · (e · f) = p` by the
fundamental identity for a Galois extension, so `f ∣ p`; `f = 1` would give
`N v = N w`, so `f = p`. -/
theorem absNorm_eq_pow_of_ne {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] {p : ℕ} (hp : p.Prime)
    (hdeg : Module.finrank K L = p)
    (w : Ideal (𝓞 K)) [w.IsPrime]
    (v : Ideal (𝓞 L)) [v.IsPrime] [v.LiesOver w]
    (hne : absNorm v ≠ absNorm w) : absNorm v = absNorm w ^ p := by
  have hpow : absNorm w ^ v.inertiaDeg (𝓞 K) = absNorm v :=
    Ideal.absNorm_pow_inertiaDeg w v
  have hefg := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    w (𝓞 L) (L ≃ₐ[K] L)
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have hin : Ideal.inertiaDegIn w (𝓞 L) = v.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDegIn_eq_inertiaDeg w v (L ≃ₐ[K] L)
  rw [hcard, hin] at hefg
  have hdvd : v.inertiaDeg (𝓞 K) ∣ p :=
    ⟨(w.primesOver (𝓞 L)).ncard * w.ramificationIdxIn (𝓞 L), by rw [← hefg]; ring⟩
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | hpp
  · exact absurd (by rw [← hpow, h1, pow_one]) hne
  · rw [← hpow, hpp]

set_option synthInstance.maxHeartbeats 1000000 in
open scoped Classical in
/-- **THE PLACE CLAUSE OF ONE PRIME-DEGREE CYCLIC DESCENT STEP.**

Let `Φ/ℚ` be Galois, `C ≤ D` subgroups of `Gal(Φ/ℚ)` with `C` normal in `D` of
prime index `p`, so that `L = Φ^C` is cyclic of degree `p` over `M = Φ^D`.  Then
outside a finite set of places of `M` — namely those lying under `SL` — a place
`w` whose residue cardinality is realised by NO place of `L` off `SL` has a place
`v ∉ SL` above it with `N v = N w ^ p`.

This is the second conjunct of
`exists_baseChangeHeckeField_of_prime_cyclic_step_of_inert`, and it is what makes
that leaf a pure Arthur–Clozel citation once discharged. -/
theorem exists_absNorm_eq_pow_of_prime_index
    {Φ : Type*} [Field Φ] [NumberField Φ] [IsGalois ℚ Φ]
    {C D : Subgroup (Φ ≃ₐ[ℚ] Φ)} (hCD : C ≤ D)
    (hnormal : (C.subgroupOf D).Normal)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card (↥D ⧸ C.subgroupOf D) = p)
    (SL : Finset (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(fixedField C)))) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(fixedField D))),
      ∀ w ∉ S,
        (∀ v ∉ SL, absNorm v.asIdeal ≠ absNorm w.asIdeal) →
        ∃ v, v ∉ SL ∧ absNorm v.asIdeal = absNorm w.asIdeal ^ p := by
  letI : Algebra ↥(fixedField D) ↥(fixedField C) :=
    inferInstanceAs (Algebra ↥(fixedField D) ↥(extendScalars (fixedField_le hCD)))
  haveI : IsScalarTower ↥(fixedField D) ↥(fixedField C) Φ :=
    inferInstanceAs (IsScalarTower ↥(fixedField D) ↥(extendScalars (fixedField_le hCD)) Φ)
  haveI hgΦ : IsGalois ↥(fixedField D) Φ :=
    IsGalois.tower_top_of_isGalois ℚ ↥(fixedField D) Φ
  -- NORMALITY of `fixedField C` over `fixedField D`.
  haveI hNML : Normal ↥(fixedField D) ↥(fixedField C) := by
    have key : Normal ↥(fixedField D) ↥(extendScalars (fixedField_le hCD)) := by
      rw [IntermediateField.normal_iff_forall_map_le']
      intro σ y hy
      obtain ⟨x, hx, rfl⟩ := hy
      show σ x ∈ fixedField C
      refine (IntermediateField.mem_fixedField_iff C _).2 fun τ hτ => ?_
      set σ' : Φ ≃ₐ[ℚ] Φ := σ.restrictScalars ℚ with hσ'
      have hσD : σ' ∈ D := by
        rw [← IntermediateField.fixingSubgroup_fixedField D,
          IntermediateField.mem_fixingSubgroup_iff]
        intro z hz
        exact σ.commutes ⟨z, hz⟩
      have hconj : σ'⁻¹ * τ * σ' ∈ C := by
        have h := hnormal.conj_mem ⟨τ, hCD hτ⟩ ((Subgroup.mem_subgroupOf).2 hτ)
          ⟨σ'⁻¹, D.inv_mem hσD⟩
        simpa using (Subgroup.mem_subgroupOf).1 h
      have hfix := (IntermediateField.mem_fixedField_iff C x).1 hx _ hconj
      have hg : τ * σ' = σ' * (σ'⁻¹ * τ * σ') := by group
      have h3 : (τ * σ') x = σ' x := by rw [hg, AlgEquiv.mul_apply, hfix]
      have h2 : τ (σ' x) = σ' x := by rwa [AlgEquiv.mul_apply] at h3
      rw [hσ'] at h2
      exact h2
    exact key
  haveI : IsGalois ↥(fixedField D) ↥(fixedField C) := ⟨⟩
  -- DEGREE `p`, by the Galois correspondence and Lagrange.
  have hfr : Module.finrank ↥(fixedField D) ↥(fixedField C) = p := by
    have h1 : Module.finrank ↥(fixedField C) Φ = Nat.card ↥C := finrank_fixedField_eq_card C
    have h2 : Module.finrank ↥(fixedField D) Φ = Nat.card ↥D := finrank_fixedField_eq_card D
    haveI : Module.Free ↥(fixedField D) ↥(fixedField C) := Module.Free.of_divisionRing _ _
    haveI : Module.Free ↥(fixedField C) Φ := Module.Free.of_divisionRing _ _
    have ht : Module.finrank ↥(fixedField D) ↥(fixedField C) *
        Module.finrank ↥(fixedField C) Φ = Module.finrank ↥(fixedField D) Φ :=
      Module.finrank_mul_finrank _ _ _
    have hlag : Nat.card ↥(C.subgroupOf D) * (C.subgroupOf D).index = Nat.card ↥D :=
      Subgroup.card_mul_index _
    have hidx : (C.subgroupOf D).index = p := hcard
    have hCC : Nat.card ↥(C.subgroupOf D) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCD).toEquiv
    rw [h1, h2] at ht
    rw [hidx, hCC] at hlag
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    have hlag' : p * Nat.card ↥C = Nat.card ↥D := by rw [← hlag]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos (ht.trans hlag'.symm)
  -- THE PLACE ARGUMENT: exclude the places under `SL`, then take any place above.
  refine ⟨SL.image (fun v =>
    { asIdeal := v.asIdeal.under (NumberField.RingOfIntegers ↥(fixedField D))
      isPrime := inferInstance
      ne_bot := Ideal.under_ne_bot _ v.ne_bot }), ?_⟩
  intro w hw hinert
  obtain ⟨⟨v0, hv0⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver w.asIdeal
      (NumberField.RingOfIntegers ↥(fixedField C))))
  haveI : v0.IsPrime := hv0.1
  haveI : v0.LiesOver w.asIdeal := hv0.2
  set v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(fixedField C)) :=
    ⟨v0, hv0.1, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot v0⟩ with hv
  have hvnotin : v ∉ SL := by
    intro hmem
    refine hw (Finset.mem_image.2 ⟨v, hmem, ?_⟩)
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (Ideal.LiesOver.over (A := NumberField.RingOfIntegers ↥(fixedField D))
      (B := NumberField.RingOfIntegers ↥(fixedField C))).symm
  exact ⟨v, hvnotin, absNorm_eq_pow_of_ne hp hfr w.asIdeal v0 (hinert v hvnotin)⟩

end Fermat
