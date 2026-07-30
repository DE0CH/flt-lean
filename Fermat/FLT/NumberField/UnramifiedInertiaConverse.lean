/-
UnramifiedInertiaConverse.lean — own work for the Fermat project.

**The CONVERSE of the inertia dictionary**: "unramified ⟹ local inertia acts
trivially", relative to an arbitrary intermediate base field.

`Fermat/FLT/GaloisRepresentation/MinkowskiUnramified.lean` proves the FORWARD
direction over `ℚ` (`isUnramifiedAt_of_inertia_le_fixingSubgroup`) and
`HardlyRamified/HilbertModularity.lean` proves it over a base number field
(`isUnramifiedAt_of_hilbertInertiaTrivialAt`).  Neither supplies this
direction, which is what `Fermat/FLT/Modularity/Interface.lean`'s
`localInertia_le_fixingSubgroup_of_isUnramifiedAt_muSubfield` needs.

It lives in its own module rather than in `Interface.lean` for the reason
recorded there about `UnramifiedClassFieldBound.lean`: `Interface.lean`
elaborates for the better part of an hour on one core and none of this
material needs any of it.
-/

module

-- `localInertiaGroup`, `Field.absoluteGaloisGroup.map` and `lift_map`.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat` and
-- `maximalIdeal_adicCompletionIntegers_eq_span`.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `Ideal.inertia` and `Ideal.card_inertia_eq_ramificationIdxIn`.
public import Mathlib.NumberTheory.RamificationInertia.Galois
-- `Ring.HasFiniteQuotients.finiteQuotient`, for finiteness of the residue field
-- below (the `PerfectField` side condition of the counting lemma).
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
-- `Ideal.under_ne_bot`.
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

open NumberField IsDedekindDomain

namespace NumberField

/-- **Unramified ⟹ trivial ideal-inertia** (the counting half of the converse
dictionary): if a nonzero prime `Q` of `𝓞 L` is unramified over `𝓞 K` for a
finite Galois extension `L/K` of number fields, its ideal-inertia subgroup in
`Gal(L/K)` is trivial.

`|I(Q)| = e(Q | Q ∩ 𝓞 K)` is `Ideal.card_inertia_eq_ramificationIdxIn`, whose
`PerfectField` side condition comes from finiteness of the residue field of the
prime below; `Ideal.ramificationIdx_eq_one_iff` turns unramifiedness into
`e = 1`. This is the exact reverse of the last two steps of
`MinkowskiUnramified.lean`'s `isUnramifiedAt_of_inertia_le_fixingSubgroup`. -/
theorem inertia_eq_bot_of_isUnramifiedAt
    (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (Q : Ideal (𝓞 L)) [hQp : Q.IsPrime] (hQ : Q ≠ ⊥)
    (hunr : Algebra.IsUnramifiedAt (𝓞 K) Q) :
    Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  set p : Ideal (𝓞 K) := Q.under (𝓞 K) with hpdef
  haveI hpprime : p.IsPrime := inferInstance
  haveI hlies : Q.LiesOver p := ⟨rfl⟩
  -- the residue field of `p` is finite, hence perfect
  have hpne : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hQ
  haveI hmaxp : p.IsMaximal := hpprime.isMaximal_of_ne_bot hpne
  haveI : Finite (𝓞 K ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hpne
  have hsurj : Function.Surjective (algebraMap (𝓞 K ⧸ p) p.ResidueField) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxp)
  haveI : Finite p.ResidueField := Finite.of_surjective _ hsurj
  have he1 : Q.ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one_iff.mpr hunr
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[K] L)) p Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p Q (L ≃ₐ[K] L), he1] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

/-- **THE CONVERSE OF THE INERTIA DICTIONARY, RELATIVE TO AN INTERMEDIATE BASE
FIELD `K`**: if `L₀/K` is finite Galois and unramified at every nonzero prime,
then an element `g ∈ Γℚ` that fixes `K` pointwise and acts on `ℚ̄` through a
LOCAL INERTIA element at some prime — i.e. there is a ring embedding
`j : ℚ̄ → (ℚ_ℓ)ᵃˡᵍ` with `j ∘ g = n ∘ j` for `n ∈ localInertiaGroup ℓ` — fixes
`L₀` pointwise.

**The embedding is a PARAMETER, and that is what makes the conjugates come for
free.** The consumer needs the statement for `g = σ · map(n) · σ⁻¹`, and
`Field.absoluteGaloisGroup.lift_map` gives `ι (map(n) y) = n (ι y)` only for the
one embedding `ι = AlgebraicClosure.map (algebraMap ℚ ℚ_ℓ)` underlying `map`.
Taking `j := ι ∘ σ⁻¹` turns the conjugated element into the un-conjugated
hypothesis:
`j (σ map(n) σ⁻¹ y) = ι (map(n) (σ⁻¹ y)) = n (ι (σ⁻¹ y)) = n (j y)`.
So no transport of unramifiedness along `σ` is needed — which is the expensive
route, since `σ` moves `K` by an automorphism and ramification would have to be
carried across it.

**Route.** `j` carries `𝓞 L₀` into the integral closure `𝒪̄` of `𝒪ᵥ` in
`(ℚ_ℓ)ᵃˡᵍ` (an algebraic integer stays integral), so
`Q₀ := j⁻¹(𝔪 𝒪̄) ∩ 𝓞 L₀` is a prime of `𝓞 L₀`; it is nonzero because it
contains `ℓ` (the maximal ideal of `𝒪̄` contracts to that of the local ring
`𝒪ᵥ`, which is `(ℓ)`). Membership in `localInertiaGroup` says exactly that `n`
is trivial modulo `𝔪 𝒪̄`, so for `x ∈ 𝓞 L₀` we get
`j (g x) − j x = n (j x) − j x ∈ 𝔪 𝒪̄`, i.e. `g · x − x ∈ Q₀`: the restriction
of `g` to `L₀` lies in `Q₀.inertia Gal(L₀/K)`. `hunr` makes that inertia group
trivial (`inertia_eq_bot_of_isUnramifiedAt` above), so the restriction is the
identity — which is what `g ∈ L₀.fixingSubgroup` says.

**`IsGalois K L₀` is LOAD-BEARING and cannot be dropped.** It is used twice and
for different reasons: `Normal K L₀` is what makes `g` (which fixes `K`, hence
is a `K`-automorphism of `ℚ̄`) STABILIZE `L₀`, without which "the restriction of
`g` to `L₀`" is not an automorphism of `L₀` at all and `Q₀.inertia Gal(L₀/K)`
does not mention it; and finiteness of `Gal(L₀/K)` is what makes
`|I(Q₀)| = e(Q₀)` meaningful. The hypothesis is not a strengthening in practice:
the one consumer in `Modularity/Interface.lean` obtains its `L₀` from
`exists_transport_unramifiedAbelian_to_muSubfield`, which HANDS IT `IsGalois`
along with the unramifiedness, and was simply discarding it.

**Nothing is assumed at the infinite places, and nothing is needed**: this
direction only discards archimedean information. That asymmetry is why the leaf
is stated with an inertia-only hypothesis (see the standing rule that over a
local base, inertia-only conclusions are twist-blind).

**The check that would refute it**: a finite Galois `L₀/K`, unramified over
`𝓞 K` at every nonzero prime, together with `g`, `n`, `j` as above and an
element of `L₀` that `g` moves. -/
theorem fixingSubgroup_of_localInertia_of_isUnramifiedAt
    (K L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ L₀]
    (hKle : K ≤ L₀)
    [IsGalois K (IntermediateField.extendScalars hKle)]
    (hunr : ∀ (Q : Ideal (𝓞 (IntermediateField.extendScalars hKle))) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (n : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat))
    (hn : n ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat)
    (g : Field.absoluteGaloisGroup ℚ)
    (j : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat))
    (hj : ∀ y : AlgebraicClosure ℚ, j (g y) = n (j y))
    (hmem : g ∈ K.fixingSubgroup) :
    g ∈ L₀.fixingSubgroup := by
  classical
  haveI : NumberField (K : Type _) := ⟨⟩
  haveI : NumberField (L₀ : Type _) := ⟨⟩
  set E : IntermediateField (K : Type _) (AlgebraicClosure ℚ) :=
    IntermediateField.extendScalars hKle with hE
  -- `E` and `L₀` have the same carrier, so the `ℚ`-finiteness transfers by `defeq`
  haveI hfdQE : FiniteDimensional ℚ (E : Type _) := ‹FiniteDimensional ℚ (L₀ : Type _)›
  haveI hfdE : FiniteDimensional (K : Type _) (E : Type _) :=
    FiniteDimensional.right ℚ (K : Type _) (E : Type _)
  haveI : NumberField (E : Type _) := ⟨⟩
  -- (1) `j` carries the algebraic integers of `L₀` into the integral closure of `𝒪ᵥ`
  have hint : ∀ x : 𝓞 (E : Type _),
      j (algebraMap (E : Type _) (AlgebraicClosure ℚ)
          (algebraMap (𝓞 (E : Type _)) (E : Type _) x)) ∈
        integralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)) := by
    intro x
    -- the composite `↥E → ℚ̄ → (ℚ_ℓ)ᵃˡᵍ` as a `ℤ`-algebra map (all ring maps out of
    -- `ℤ` agree, so `commutes'` is uniqueness of `ℤ →+* ·`)
    let Ψ : (E : Type _) →ₐ[ℤ] AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat) :=
      { toRingHom := j.comp (algebraMap (E : Type _) (AlgebraicClosure ℚ))
        commutes' := fun m => by
          rw [RingHom.eq_intCast' (algebraMap ℤ (E : Type _)),
            RingHom.eq_intCast' (algebraMap ℤ (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hℓ.toHeightOneSpectrumRingOfIntegersRat)))]
          exact map_intCast (j.comp (algebraMap (E : Type _) (AlgebraicClosure ℚ))) m }
    have h1 : IsIntegral ℤ (algebraMap (𝓞 (E : Type _)) (E : Type _) x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    have h2 : IsIntegral ℤ (j (algebraMap (E : Type _) (AlgebraicClosure ℚ)
        (algebraMap (𝓞 (E : Type _)) (E : Type _) x))) := h1.map Ψ
    -- push the monic witness along `ℤ → 𝒪ᵥ`
    obtain ⟨P, hP, hPeval⟩ := h2
    refine ⟨P.map (Int.castRingHom
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat)), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat))).comp
        (Int.castRingHom
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)))
      (algebraMap ℤ (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)))]
    exact hPeval
  -- the induced map on rings of integers, and the prime it determines
  set φ : 𝓞 (E : Type _) →+*
      IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((j.comp (algebraMap (E : Type _) (AlgebraicClosure ℚ))).comp
      (algebraMap (𝓞 (E : Type _)) (E : Type _))).codRestrict _ hint with hφ
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)))).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  set Q₀ : Ideal (𝓞 (E : Type _)) :=
    Ideal.comap φ (IsLocalRing.maximalIdeal _) with hQ₀
  haveI hQ₀p : Q₀.IsPrime := Ideal.IsPrime.comap φ
  -- (2) `Q₀ ≠ ⊥`, because it contains `ℓ`: the maximal ideal of the integral
  -- closure contracts to that of the LOCAL ring `𝒪ᵥ`, which is `(ℓ)`
  have hQ₀ne : Q₀ ≠ ⊥ := by
    have hmaxcomap : (Ideal.comap
        (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hℓ.toHeightOneSpectrumRingOfIntegersRat)
          (IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hℓ.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hℓ.toHeightOneSpectrumRingOfIntegersRat))))
        (IsLocalRing.maximalIdeal _)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    have hlOv : ((ℓ : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat) ∈ IsLocalRing.maximalIdeal _ := by
      rw [maximalIdeal_adicCompletionIntegers_eq_span hℓ]
      exact Ideal.mem_span_singleton_self _
    rw [← hmaxcomap.eq_of_le (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (IsLocalRing.le_maximalIdeal hmaxcomap.ne_top), Ideal.mem_comap,
      map_natCast] at hlOv
    have hmem' : ((ℓ : ℕ) : 𝓞 (E : Type _)) ∈ Q₀ := by
      rw [hQ₀, Ideal.mem_comap, map_natCast]
      exact hlOv
    intro h0
    rw [h0, Ideal.mem_bot] at hmem'
    exact (Nat.cast_ne_zero.mpr hℓ.ne_zero) hmem'
  -- (3) `g`, as a `K`-automorphism of `ℚ̄`, restricts to `E`
  set G : AlgebraicClosure ℚ ≃ₐ[(K : Type _)] AlgebraicClosure ℚ :=
    IntermediateField.fixingSubgroupEquiv K ⟨g, hmem⟩ with hG
  have hGapp : ∀ y : AlgebraicClosure ℚ, G y = g y := fun _ => rfl
  haveI : Normal (K : Type _) (E : Type _) := IsGalois.to_normal
  set ρ : (E : Type _) ≃ₐ[(K : Type _)] (E : Type _) :=
    AlgEquiv.restrictNormalHom (E : Type _) G with hρ
  have hρapp : ∀ w : (E : Type _),
      algebraMap (E : Type _) (AlgebraicClosure ℚ) (ρ w) =
        g (algebraMap (E : Type _) (AlgebraicClosure ℚ) w) := by
    intro w
    have hcm := AlgEquiv.restrictNormal_commutes G (E : Type _) w
    rw [show AlgEquiv.restrictNormal G (E : Type _)
        = AlgEquiv.restrictNormalHom (E : Type _) G from rfl] at hcm
    rw [hρ, hcm, hGapp]
  -- (4) the restriction lies in the ideal-inertia at `Q₀`: `j` intertwines `g`
  -- with `n`, and `n` is trivial modulo the maximal ideal
  have hinert : ρ ∈ Q₀.inertia ((E : Type _) ≃ₐ[(K : Type _)] (E : Type _)) := by
    intro x
    have hbase : n • φ x - φ x ∈ IsLocalRing.maximalIdeal _ := by
      have h := hn (φ x)
      rwa [Submodule.mem_toAddSubgroup] at h
    have hcoe : φ (ρ • x) = n • φ x := by
      apply Subtype.ext
      show j (algebraMap (E : Type _) (AlgebraicClosure ℚ)
          (algebraMap (𝓞 (E : Type _)) (E : Type _) (ρ • x))) = _
      have hact : algebraMap (𝓞 (E : Type _)) (E : Type _) (ρ • x)
          = ρ (algebraMap (𝓞 (E : Type _)) (E : Type _) x) := rfl
      rw [hact, hρapp, hj]
      rfl
    rw [Submodule.mem_toAddSubgroup, hQ₀, Ideal.mem_comap, map_sub, hcoe]
    exact hbase
  -- (5) that inertia group is trivial, so `ρ = 1`
  have hbot : Q₀.inertia ((E : Type _) ≃ₐ[(K : Type _)] (E : Type _)) = ⊥ :=
    inertia_eq_bot_of_isUnramifiedAt (K : Type _) (E : Type _) Q₀ hQ₀ne
      (hunr Q₀ hQ₀p hQ₀ne)
  have hρ1 : ρ = 1 := by
    rw [Subgroup.eq_bot_iff_forall] at hbot
    exact hbot ρ hinert
  -- (6) hence `g` fixes `L₀ = E` pointwise
  refine (IntermediateField.mem_fixingSubgroup_iff _ g).mpr ?_
  intro x hx
  have hxE : x ∈ E := hx
  have := hρapp ⟨x, hxE⟩
  rw [hρ1] at this
  simpa using this.symm

/-- **THE CONVERSE DICTIONARY IN THE SHAPE THE CONSUMER NEEDS**: a `Γℚ`-CONJUGATE
of a local inertia element at `ℓ`, if it fixes `K` pointwise, fixes every finite
Galois `L₀/K` that is unramified at every nonzero prime.

This is the theorem above applied with `j := ι ∘ σ⁻¹`, where
`ι = AlgebraicClosure.map (algebraMap ℚ ℚ_ℓ)` is the embedding underlying
`Field.absoluteGaloisGroup.map`. That choice is what makes the conjugation free:
`ι (σ⁻¹ (σ · map(n) · σ⁻¹) y) = ι (map(n) (σ⁻¹ y)) = n (ι (σ⁻¹ y))` by
`Field.absoluteGaloisGroup.lift_map`, so the intertwining hypothesis holds with
no hypothesis on `σ` at all — in particular `K` need NOT be normal over `ℚ`, and
no ramification data has to be transported along `σ`.

Kept in this module rather than in `Modularity/Interface.lean` so that the whole
argument iterates in seconds; the consumer there is a bare `exact`. -/
theorem fixingSubgroup_of_conj_localInertia_of_isUnramifiedAt
    (K L₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ L₀]
    (hKle : K ≤ L₀)
    [IsGalois K (IntermediateField.extendScalars hKle)]
    (hunr : ∀ (Q : Ideal (𝓞 (IntermediateField.extendScalars hKle))) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (n : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat))
    (σ : Field.absoluteGaloisGroup ℚ)
    (hn : n ∈ localInertiaGroup hℓ.toHeightOneSpectrumRingOfIntegersRat)
    (hmem : σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹ ∈ K.fixingSubgroup) :
    σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹ ∈ L₀.fixingSubgroup := by
  -- `σ.symm` rather than `σ⁻¹`: the inverse of `Field.absoluteGaloisGroup`'s own
  -- group structure does not reduce to `AlgEquiv.symm` for `simp`, so keeping the
  -- embedding phrased with `symm` is what lets the cancellation close.
  refine fixingSubgroup_of_localInertia_of_isUnramifiedAt K L₀ hKle hunr ℓ hℓ n hn _
    ((AlgebraicClosure.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hℓ.toHeightOneSpectrumRingOfIntegersRat))).comp
      (σ.symm : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.toRingHom)
    (fun y => ?_) hmem
  -- `ι (σ.symm ((σ · map(n) · σ⁻¹) y)) = ι (map(n) (σ.symm y)) = n (ι (σ.symm y))`
  have hconj : ∀ z : AlgebraicClosure ℚ,
      (σ * Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)) n * σ⁻¹) z
      = σ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hℓ.toHeightOneSpectrumRingOfIntegersRat)) n (σ.symm z)) := by
    intro z
    simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgEquiv.coe_toAlgHom, RingHom.coe_coe]
  rw [hconj y, AlgEquiv.symm_apply_apply]
  exact Field.absoluteGaloisGroup.lift_map _ n _

end NumberField
