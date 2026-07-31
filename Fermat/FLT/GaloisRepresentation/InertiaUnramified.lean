/-
InertiaUnramified.lean — own work for the Fermat project (not vendored
from the FLT project).

**The inertia-to-discriminant dictionary over `ℚ`**: if the image in
`Γ_ℚ` of the local inertia group at a rational prime `q` fixes a finite
Galois subfield `L ⊆ ℚᵃˡᵍ` pointwise, then every prime of `𝓞 L` above
`q` is unramified over `ℤ`, and `q ∤ discr L`.

HOISTED 2026-07-31, VERBATIM, out of two files at once:

* `Fermat/FLT/GaloisRepresentation/MinkowskiUnramified.lean` — the four
  theorems `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`,
  `inertia_eq_bot_of_exists_prime_over`,
  `inertia_eq_bot_of_le_fixingSubgroup` and
  `isUnramifiedAt_of_inertia_le_fixingSubgroup`;
* `Fermat/FLT/GaloisRepresentation/HardlyRamified/HermiteMinkowski.lean` —
  the predicate `GaloisRepresentation.InertiaTrivialAt` and the
  discriminant transport `GaloisRepresentation.not_dvd_discr_of_inertiaTrivialAt`
  that consumes it.

**Why.**  `ModularCurve/X0.lean` needs exactly this dictionary, for the
Néron–Ogg–Shafarevich cut of the weak Mordell–Weil chain: the leaf
`exists_ramificationSet_geomPtField` is stated about discriminants and
what the geometry produces is inertia acting trivially on a division
point.  Both source files are DOWNSTREAM of `X0.lean` —
`MinkowskiUnramified` only because it `public import`s
`GaloisRepresentation/Chebotarev.lean` (13 500 lines) for an unrelated
declaration further down the same file (`isOpen_setOf_galoisRep_eq_one`,
which needs `discreteTopology_moduleTopology`), and `HermiteMinkowski`
because it imports `MazurTorsion`.  The block hoisted here depends on
NONE of that: it needs only the local inertia-fixed-field node, the
`Nat.Prime → HeightOneSpectrum ℤ` bridge, and mathlib.  Splitting it out
costs `X0.lean`'s import cone one module (`LocalInertiaFixedField`,
1752 lines) instead of four (16 160 lines, Chebotarev included).

This is the same repair the 2026-07-28 hoist of
`HardlyRamified/HermiteMinkowski.lean`'s different-ideal development into
`HardlyRamified/DiscrExponent.lean` performed, for the same reason and by
the same rule: a node stranded below its consumer is a missing module
boundary, not a missing theorem.

Every NAME and STATEMENT is unchanged, so all downstream use sites keep
resolving without edits; the two source files now `public import` this
one.
-/

module

-- `localInertiaGroup`, `Field.absoluteGaloisGroup.map` and `lift_map`.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- The local inertia-fixed-field node
-- (`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`): `e(M/ℚ_q) = 1`
-- for finite subextensions of `ℚ_qᵃˡᵍ` fixed by the local inertia.
public import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat` and
-- `maximalIdeal_adicCompletionIntegers_eq_span`.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- Going-up prime lifting, used in the transitivity step.
public import Mathlib.RingTheory.Ideal.GoingUp
-- `Ideal.inertia` and `Ideal.card_inertia_eq_ramificationIdxIn`.
public import Mathlib.NumberTheory.RamificationInertia.Galois
-- `NumberField.not_dvd_discr_iff_forall_mem`.
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

-- The block lived inside `MazurTorsion.lean`'s `@[expose] public section`
-- before its first hoist; replicating that here is what keeps this hoist a
-- no-op for consumers — without it the declarations would not be exported.
@[expose] public section

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski surjectivity transport** (DERIVED 2026-07-16 from the
local inertia-fixed-field node
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`): if the image
in `G_ℚ` of the local inertia group at `q` fixes the finite Galois
extension `L/ℚ` pointwise, then SOME prime `Q₀` of `𝓞 L` above `q` has
trivial ideal-inertia in `Gal(L/ℚ)`. Construction: the chosen embedding
`ι : ℚᵃˡᵍ → (ℚ_q)ᵃˡᵍ` (the one underlying `absoluteGaloisGroup.map`)
carries `L` into the finite subextension `M := ℚ_q(ι(L))`, which the
hypothesis and `lift_map` place inside the fixed field of the local
inertia; the local node then makes `q` a uniformizer of the integral
closure `𝒪_M`. Pulling the maximal ideal of `𝒪_M` back along
`ι : 𝓞 L → 𝒪_M` yields a prime `Q₀ ∋ q` with `e(Q₀|q) = 1` (if `e ≥ 2`
then `q ∈ Q₀²`, so `q ∈ 𝔪_M² = (q²)`, making `q` a unit of `𝒪_M` —
absurd), and `#I(Q₀) = e = 1` closes by
`card_inertia_eq_ramificationIdxIn`. No decomposition-group theory or
henselian lifting is used. -/
theorem exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup) :
    ∃ (Q₀ : Ideal (NumberField.RingOfIntegers L)) (_ : Q₀.IsPrime)
      (_ : (q : NumberField.RingOfIntegers L) ∈ Q₀),
      Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  classical
  -- the chosen embedding of algebraic closures underlying the map of
  -- absolute Galois groups
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat :=
    algebraMap ℚ _
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map f
  -- a finite generating set for `L/ℚ`
  obtain ⟨s, hs⟩ := L.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType ℚ L))
  have hL : L = IntermediateField.adjoin ℚ ↑s :=
    IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
  -- the image field `M := ℚ_q(ι(s)) = ℚ_q(ι(L))`
  set M : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IntermediateField.adjoin _ (ι '' ↑s) with hM
  -- `ι` carries all of `L` into `M`
  have hsub : ∀ x ∈ L, ι x ∈ M := by
    intro x hx
    rw [hL] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | algebraMap c =>
        rw [AlgebraicClosure.map_algebraMap]
        exact M.algebraMap_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  -- `M/ℚ_q` is finite: it is generated by the finite set `ι '' s` of
  -- integral (= algebraic) elements
  haveI hfdM : FiniteDimensional
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    haveI : Finite (ι '' (↑s : Set (AlgebraicClosure ℚ))) :=
      (s.finite_toSet.image ι).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      fun x _ => Algebra.IsIntegral.isIntegral x
  -- the hypothesis places `M` inside the fixed field of the local inertia
  have hMfix : M ≤ IntermediateField.fixedField
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hM, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    -- `σ (ι y) = ι ((map f σ) y) = ι y` by `lift_map` and the hypothesis
    have hmem : (Field.absoluteGaloisGroup.map f) σ ∈ L.fixingSubgroup :=
      hle (Subgroup.mem_map_of_mem _ hσ)
    have hfixy : (Field.absoluteGaloisGroup.map f σ) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff L ((Field.absoluteGaloisGroup.map f) σ)).mp
        hmem y (hL ▸ IntermediateField.subset_adjoin _ _ hy)
    calc σ (ι y) = ι ((Field.absoluteGaloisGroup.map f σ) y) :=
          (Field.absoluteGaloisGroup.lift_map f σ y).symm
      _ = ι y := by rw [hfixy]
  -- the local node: `q` generates the maximal ideal of `𝒪_M`
  have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat M hMfix
  have hspan : IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) =
      Ideal.span {(q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)} := by
    rw [← hmax, maximalIdeal_adicCompletionIntegers_eq_span hq, Ideal.map_span,
      Set.image_singleton, map_natCast]
  -- the ring homomorphism `ψ : L → M` induced by `ι`
  let ψ : L →+* M :=
    { toFun := fun y => ⟨ι (y : AlgebraicClosure ℚ), hsub _ y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  -- `ψ` carries the ring of integers of `L` into `𝒪_M`
  have hψint : ∀ x : NumberField.RingOfIntegers L,
      ψ (algebraMap (NumberField.RingOfIntegers L) L x) ∈
        integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers L) L x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    -- promote `ψ` to a `ℤ`-algebra homomorphism with the AMBIENT `ℤ`-algebra
    -- structures (all ring homs from `ℤ` agree, so `commutes'` is by
    -- uniqueness of `ℤ →+* ·`)
    let ψℤ : L →ₐ[ℤ] M :=
      { toRingHom := ψ
        commutes' := fun n => by
          rw [RingHom.eq_intCast' (algebraMap ℤ L), RingHom.eq_intCast' (algebraMap ℤ M)]
          exact map_intCast ψ n }
    have h2 : IsIntegral ℤ (ψ (algebraMap (NumberField.RingOfIntegers L) L x)) :=
      h1.map ψℤ
    -- pass from `ℤ`-integrality to `𝒪ᵥ`-integrality by pushing the monic
    -- witness through `ℤ → 𝒪ᵥ` (instance-agnostic: all ring homs from `ℤ`
    -- agree)
    obtain ⟨p, hp, hpeval⟩ := h2
    refine ⟨p.map (Int.castRingHom
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M).comp
        (Int.castRingHom
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
      (algebraMap ℤ M)]
    exact hpeval
  let φ : NumberField.RingOfIntegers L →+*
      IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M :=
    (ψ.comp (algebraMap (NumberField.RingOfIntegers L) L)).codRestrict
      (integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) hψint
  -- the embedding prime: the pullback of the maximal ideal of `𝒪_M`
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), Ideal.IsPrime.comap φ, ?_, ?_⟩
  · -- `q` lands in the pullback: `φ q = q ∈ 𝔪_M = (q)`
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  -- inertia is trivial: `#I(Q₀) = e(Q₀|q) = 1`
  have hQ₀mem : (q : NumberField.RingOfIntegers L) ∈
      Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  haveI hQ₀prime : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).IsPrime :=
    Ideal.IsPrime.comap φ
  -- instance pack for `card_inertia_eq_ramificationIdxIn` (mirrors the
  -- inertia dictionary proof below)
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).LiesOver
      (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff hQ₀prime.ne_top hqZ).mpr (by exact_mod_cast hQ₀mem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmaxZ : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurjZ : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxZ)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurjZ
  -- the ramification index (old spelling) is `1`
  have hple : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
      (Ideal.span {((q : ℤ))}) ≤ Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact_mod_cast hQ₀mem
  have he1 : Ideal.ramificationIdx' (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) = 1 := by
    by_contra hne1
    have hsq := (Ideal.ramificationIdx'_ne_one_iff hple).mp hne1
    -- then `q ∈ Q₀²`, so `φ q = q ∈ 𝔪_M² = (q²)`, making `q` a unit
    have hqQ2 : (q : NumberField.RingOfIntegers L) ∈
        (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 := by
      refine hsq ?_
      have : algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.span {((q : ℤ))}) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      simpa using this
    have hcomap2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 ≤
        Ideal.comap φ ((IsLocalRing.maximalIdeal _) ^ 2) := by
      rw [pow_two, pow_two]
      exact Ideal.mul_le.mpr fun r hr t ht => Ideal.mem_comap.mpr
        (by rw [map_mul]; exact Ideal.mul_mem_mul hr ht)
    have hφq := Ideal.mem_comap.mp (hcomap2 hqQ2)
    rw [map_natCast, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hφq
    obtain ⟨c, hc⟩ := hφq
    -- `q ≠ 0` in `𝒪_M` (its image in `(ℚ_q)ᵃˡᵍ` is `q ≠ 0` by char zero)
    haveI : CharZero (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      charZero_of_injective_algebraMap (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) _).injective
    have hq0 : ((q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun z => (algebraMap M (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ((algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) M) z))) h0
      simp only [map_natCast, map_zero] at h1
      exact Nat.cast_ne_zero.mpr hq.ne_zero h1
    -- cancel one factor of `q`: `q · c = 1`
    have hcancel : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) * c = 1 := by
      have hmul : (q : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) *
          ((q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * c) =
          (q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * 1 := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc.symm
      exact mul_left_cancel₀ hq0 hmul
    -- but `q` lies in the proper maximal ideal — contradiction
    have hqmem : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [hspan]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hqmem
        (isUnit_iff_exists.mpr ⟨c, hcancel, by rwa [mul_comm] at hcancel⟩))
  -- bridge to the `Module.length` spelling and conclude via
  -- `#I(Q₀) = e = 1`
  have h2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) hne]
    exact he1
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _))
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _)) (L ≃ₐ[ℚ] L), h2] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugacy propagation of trivial inertia** (PROVEN 2026-07-16): if ONE
prime of `𝓞 L` above `q` has trivial ideal-inertia in `Gal(L/ℚ)`, then
EVERY prime above `q` does. Classical: `Gal(L/ℚ)` acts transitively on
the primes above `q` (`Ideal.IsInvariant.orbit_eq_primesOver` /
going-up), and inertia groups at conjugate primes are conjugate
(`I(g • Q) = g I(Q) g⁻¹`), so triviality propagates along the orbit. -/
theorem inertia_eq_bot_of_exists_prime_over
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (Q₀ : Ideal (NumberField.RingOfIntegers L)) [Q₀.IsPrime]
    (hQ₀mem : (q : NumberField.RingOfIntegers L) ∈ Q₀)
    (hQ₀ : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  haveI hlies₀ : Q₀.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q₀.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQ₀mem)
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI := IsGaloisGroup.of_isFractionRing (L ≃ₐ[ℚ] L) ℤ
    (NumberField.RingOfIntegers L) ℚ L
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (Ideal.span {((q : ℤ))}) Q₀ Q ((L ≃ₐ[ℚ] L))
  rw [← hσ]
  rw [Subgroup.eq_bot_iff_forall] at hQ₀ ⊢
  intro g hg
  have hconj : σ⁻¹ * g * σ ∈ Q₀.inertia (L ≃ₐ[ℚ] L) := by
    intro y
    have h1 := hg (σ • y)
    rw [Submodule.mem_toAddSubgroup,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h1
    rw [Submodule.mem_toAddSubgroup]
    have h2 : σ⁻¹ • (g • σ • y - σ • y) = (σ⁻¹ * g * σ) • y - y := by
      rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul]
    rwa [h2] at h1
  have h3 : σ⁻¹ * g * σ = 1 := hQ₀ _ hconj
  have h4 : g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
  rw [h4, h3, mul_one, mul_inv_cancel]

/-- **The inertia transport** (DERIVED 2026-07-16 from the two nodes
above): the image of `localInertiaGroup q` fixing `L` pointwise
trivializes the global ideal-inertia at EVERY prime above `q` — the
embedding-determined prime has trivial inertia by the surjectivity
node, and conjugacy propagates it. -/
theorem inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  obtain ⟨Q₀, hQ₀p, hQ₀mem, hQ₀⟩ :=
    exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup L hq hle
  exact inertia_eq_bot_of_exists_prime_over L hq Q₀ hQ₀mem hQ₀ Q hQmem

set_option backward.isDefEq.respectTransparency false in
/-- **The inertia dictionary** (DERIVED 2026-07-16 from the transport
node above): if the image in `G_ℚ` of the local inertia group at `q`
fixes the finite Galois extension `L/ℚ` pointwise, then every prime of
`𝓞 L` above `q` is unramified over `ℤ`. Chain: the transport node
trivializes the global ideal-inertia `Q.inertia Gal(L/ℚ)`; its
cardinality IS the ramification index
(`card_inertia_eq_ramificationIdxIn`); `ramificationIdxIn` transfers to
the specific prime; and `ramificationIdx_eq_one_iff` converts `e = 1`
to `Algebra.IsUnramifiedAt` (the `PerfectField` side condition comes
from finiteness of the residue field, via the fraction-ring bridge and
`maximal_ideal_iff_isField_quotient`). -/
theorem isUnramifiedAt_of_inertia_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Algebra.IsUnramifiedAt ℤ Q := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurj : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurj
  -- `e = |inertia| = |⊥| = 1`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))}) Q
  rw [inertia_eq_bot_of_le_fixingSubgroup L hq hle Q hQmem] at hcard
  have h1 : Ideal.ramificationIdxIn (Ideal.span {((q : ℤ))})
      (NumberField.RingOfIntegers L) = 1 := by
    rw [← hcard]
    simp
  have h2 : Q.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
      (Ideal.span {((q : ℤ))}) Q (L ≃ₐ[ℚ] L)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

namespace GaloisRepresentation

open IsDedekindDomain

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

end GaloisRepresentation
