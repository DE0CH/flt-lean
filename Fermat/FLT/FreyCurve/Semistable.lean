/-
Semistable.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyCurve.torsion_isUnramified_of_good` (unramifiedness
of the mod-`p` Frey torsion representation at good primes) into two
faithful nodes:

* `FreyPackage.freyCurve_hasGoodReduction_of_not_dvd` (sorry node): the
  **arithmetic** — at an odd prime `q ∤ abc` the Frey curve has good
  reduction over the localization `ℤ_(q)` (its equation is `q`-integral
  and its discriminant `(abc)^{2p}/2⁸` is a `q`-adic unit, so the
  equation is already minimal at `q` with unit discriminant).

* `WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction` (sorry node):
  the **local-global glue** — for any elliptic curve over `ℚ` with good
  reduction at the place `q ≠ p`, the mod-`p` torsion representation is
  unramified at `q` in the `GaloisRep.IsUnramifiedAt` sense. This node
  is to be closed against the vendored Néron–Ogg–Shafarevich node
  (`WeierstrassCurve.torsion_unramified_of_good_reduction`, in
  `KnownIn1980s/EllipticCurves/GoodReduction.lean`, stated for an
  arbitrary DVR `R` with fraction field `k` and an arbitrary valuation
  subring of `kˢᵉᵖ` above `R` — here `R = ℤ_(q)`, `k = ℚ`,
  `kˢᵉᵖ = AlgebraicClosure ℚ`); what remains on top of it is the
  dictionary between `localInertiaGroup q ≤ ker (ρ.toLocal q)` and the
  triviality of the `𝒪`-inertia action on the torsion points, for the
  valuation subring `𝒪` of `ℚ̄` induced by the chosen embedding
  `ℚ̄ ↪ ℚ̄_q`.

The localization `ℤ_(q) = Localization.AtPrime v.asIdeal` (for
`v = hq.toHeightOneSpectrumRingOfIntegersRat`) is a DVR with fraction
field `ℚ`; the instances wiring this up (the `Algebra _ ℚ` structure,
the scalar tower, `IsFractionRing`, `IsDiscreteValuationRing`) are not
found by synthesis in mathlib, so they are provided as named instances
below. They must be *public* (not `local`): the statements of the nodes
mention them, so every consumer needs the same instances in scope.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Valuation.Integral
import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
-- `quadraticTwist` itself, PUBLIC because the unramified-quadratic-descent
-- leaf of the nonsplit package is STATED with it
public import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists
-- the unit-`c₄` Kraus–Laska minimality criterion, for the multiplicative case
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
-- the local-field instance package for `adicCompletion ℚ v` (the
-- `ValuativeRel`/`𝒪[·]` vocabulary of the completion-transfer lemma)
public import Fermat.FLT.Mathlib.NumberTheory.Padics.LocalField
-- the adic-vs-canonical valuation bridges over `𝒪[K]`
public import Fermat.FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic
-- `exists_tateEquivSepClosure` and the PROVEN `tate_inertia_unipotent`,
-- consumed by the split-case unipotence assembly
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateSepClosure
-- `isUnit_natCast_adicCompletionIntegers` (a prime `p ≠ q` is a unit of
-- `ℤ_qˆ`), input to the residue-characteristic fact at the local
-- valuation subring
import Fermat.FLT.GaloisRepresentation.Chebotarev
-- the vendored Néron–Ogg–Shafarevich node, consumed by the
-- good-reduction unramifiedness glue; PUBLIC because the
-- multiplicative-reduction pointwise node is STATED in its
-- `ValuationSubring.inertiaSubgroup` language
public import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
-- the embedded valuation subring, its `h𝒪`-compatibility, and the
-- inertia spelling bridge (all PROVEN), consumed by the same glue;
-- PUBLIC because the unipotence leaf is STATED with `localInertiaGroup`
public import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- the vendored finite-flat leaf and the shared flat transport node,
-- consumed by the flatness glue; the convolution monoid and the
-- tensor-product Hopf instance are needed to STATE the peu-ramifiée
-- leaf, hence public
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
-- standard étale pairs and finite products of étale algebras, consumed
-- by the étale-generic-fibre proof of the Kummer Hopf algebra; PUBLIC
-- because the presentation equivalence is STATED with the pair's Ring
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Etale.Pi
-- finite Galois theory (`normalClosure`, `IsGalois`), consumed by the
-- finite-factorization glue of `exists_galoisModulePackage`; PUBLIC
-- because the finite-Galois core leaf is STATED with `IsGalois`
public import Mathlib.FieldTheory.Galois.Basic
-- split Galois descent for the twisted constant group scheme: the
-- normal basis theorem and the Dedekind-matrix inversion feed the
-- spanning half, tensor finiteness feeds the dimension count
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open IsDedekindDomain

/-- The `Algebra ℤ_(v) ℚ` structure on the localization of `𝓞 ℚ` at a
finite place: the fraction-field embedding, via
`IsLocalization.localizationAlgebraOfSubmonoidLe` (the prime complement
is contained in the nonzerodivisors). Not found by instance synthesis in
mathlib; needed to even state `HasGoodReduction` over the localization. -/
noncomputable instance instAlgebraLocalizationAtPrimeRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Algebra (Localization.AtPrime v.asIdeal) ℚ :=
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime v.asIdeal) ℚ
    v.asIdeal.primeCompl (nonZeroDivisors _)
    v.asIdeal.primeCompl_le_nonZeroDivisors

/-- The compatibility `𝓞 ℚ → ℤ_(v) → ℚ` of the algebra structure above
with the two localization maps. -/
instance instIsScalarTowerLocalizationAtPrimeRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsScalarTower (NumberField.RingOfIntegers ℚ) (Localization.AtPrime v.asIdeal) ℚ :=
  IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime v.asIdeal) ℚ v.asIdeal.primeCompl (nonZeroDivisors _)
    v.asIdeal.primeCompl_le_nonZeroDivisors

/-- `ℚ` is the fraction field of the localization `ℤ_(v)`. -/
instance instIsFractionRingLocalizationAtPrimeRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsFractionRing (Localization.AtPrime v.asIdeal) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl
    (Localization.AtPrime v.asIdeal) ℚ

/-- The localization of the Dedekind domain `𝓞 ℚ` at a finite place is a
discrete valuation ring (`IsDedekindDomainDvr`). -/
instance instIsDiscreteValuationRingLocalizationAtPrimeRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) := by
  haveI hdom : IsDomain (NumberField.RingOfIntegers ℚ) := inferInstance
  exact @IsDedekindDomainDvr.is_dvr_at_nonzero_prime (NumberField.RingOfIntegers ℚ)
    _ hdom _ v.asIdeal v.ne_bot v.isPrime

/-- Membership of an integer in the height-one prime of `𝓞 ℚ` attached to a
prime number `q`: `m ∈ v_q` iff `q ∣ m`. (The `intCast` companion of
`natCast_mem_toHeightOneSpectrum_iff` in `Chebotarev.lean`; both unfold
the definition `v_q = comap (𝓞 ℚ ≃+* ℤ) (span {q})`.) -/
lemma intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff {q : ℕ} (hq : q.Prime) (m : ℤ) :
    (m : NumberField.RingOfIntegers ℚ) ∈ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ↔ (q : ℤ) ∣ m := by
  have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm) (Ideal.span {(q : ℤ)}) := rfl
  rw [h1, Ideal.mem_comap, map_intCast, Ideal.mem_span_singleton, Int.cast_id]

/-- An integer `m` not divisible by `q` becomes a unit in the localization
`ℤ_(q) = Localization.AtPrime v_q`: its image in `𝓞 ℚ` lies in the prime
complement, and localization inverts the prime complement. -/
lemma isUnit_intCast_localizationAtPrime {q : ℕ} (hq : q.Prime) {m : ℤ}
    (hndvd : ¬((q : ℤ) ∣ m)) :
    IsUnit ((m : Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) := by
  have hcompl : ((m : NumberField.RingOfIntegers ℚ)) ∈
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal.primeCompl := fun hmem =>
    hndvd ((intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff hq m).mp hmem)
  have h := (IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
    ((m : NumberField.RingOfIntegers ℚ))).mpr hcompl
  rwa [map_intCast] at h

open WeierstrassCurve in
/-- **Good reduction of the Frey curve away from `2p`** (PROVEN
2026-07-16): at an odd prime `q` not dividing `abc`, the Frey curve
`y² + xy = x³ + ((b^p-1-a^p)/4)x² - (a^p b^p/16)x` has good reduction
over the localization `ℤ_(q)`: its coefficients are `q`-integral (they
are integers — the divisions by `4` and `16` are exact, via the integral
model `freyCurveInt` and `FreyCurve.map`), and its discriminant
`(abc)^{2p}/2⁸` is the image of a unit of `ℤ_(q)` (numerator and
denominator are both prime to `q`), so the adic valuation of the
discriminant is `1` — which is maximal among integral models, giving
minimality, and is the definition of good reduction. -/
theorem FreyPackage.freyCurve_hasGoodReduction_of_not_dvd (P : FreyPackage)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hndvd : ¬((q : ℤ) ∣ P.a * P.b * P.c)) :
    P.freyCurve.HasGoodReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
  set R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
  -- `q`-integrality: every coefficient of the Frey equation is an integer
  haveI hInt : IsIntegral R P.freyCurve := by
    rw [← FreyCurve.map P]
    refine isIntegral_of_exists_lift R ?_ ?_ ?_ ?_ ?_ <;>
      exact ⟨_, (map_intCast (algebraMap R ℚ) _).trans
        (eq_intCast (algebraMap ℤ ℚ) _).symm⟩
  -- `q ∤ 2`
  have h2 : ¬((q : ℤ) ∣ (2 : ℤ)) := by
    intro h
    have hq2' : q ∣ 2 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2')
  -- the discriminant is the image of a unit of `ℤ_(q)`
  have hu1 : IsUnit ((P.a * P.b * P.c : ℤ) : R) :=
    isUnit_intCast_localizationAtPrime hq hndvd
  have hu2 : IsUnit (((2 : ℤ) : R)) := isUnit_intCast_localizationAtPrime hq h2
  have hΔeq : P.freyCurve.Δ = algebraMap R ℚ
      ((((P.a * P.b * P.c : ℤ) : R)) ^ (2 * P.p) * (↑hu2.unit⁻¹ : R) ^ 8) := by
    rw [FreyCurve.Δ, map_mul, map_pow, map_intCast, map_pow, map_units_inv,
      IsUnit.unit_spec, map_intCast]
    push_cast
    rw [div_eq_mul_inv, inv_pow]
  have hval : IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (IsDiscreteValuationRing.maximalIdeal R) P.freyCurve.Δ = 1 := by
    have hmem : P.freyCurve.Δ ∈ MonoidHom.mker
        ((IsDiscreteValuationRing.maximalIdeal R).valuation ℚ) := by
      rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid]
      exact Submonoid.mem_map.mpr
        ⟨_, (hu1.pow _).mul ((hu2.unit⁻¹).isUnit.pow 8), hΔeq.symm⟩
    exact MonoidHom.mem_mker.mp hmem
  -- minimality: the valuation of the discriminant is `1`, the maximum
  -- possible among integral models
  refine { val_Δ_maximal := ⟨?_, fun C _ _ => ?_⟩, goodReduction := hval }
  · simpa using hInt
  · have hle : (valuation_Δ_aux R (C • P.freyCurve) : WithZero (Multiplicative ℤ)) ≤ 1 :=
      (valuation_Δ_aux R (C • P.freyCurve)).2
    have h1 : (valuation_Δ_aux R ((1 : VariableChange ℚ) • P.freyCurve) :
        WithZero (Multiplicative ℤ)) = 1 := by
      rw [one_smul, valuation_Δ_aux_eq_of_isIntegral R P.freyCurve, hval]
    exact Subtype.coe_le_coe.mp (le_of_le_of_eq hle h1.symm)

open WeierstrassCurve in
/-- **Multiplicative reduction of the Frey curve at odd bad primes**
(PROVEN 2026-07-16): at an odd prime `q ∣ abc`, the Frey curve has
multiplicative reduction over `ℤ_(q)`: the equation is `q`-integral;
`c₄ = c^{2p} - (ab)^p` is prime to `q` (by pairwise coprimality exactly
one of `ab`, `c` is divisible by `q`, so the difference is not), giving
`v(c₄) = 1` — whence minimality by the unit-`c₄` Kraus–Laska criterion
(`isMinimal_of_valuation_c₄_eq_one`) — while `Δ = (abc)^{2p}/2⁸` lies in
the maximal ideal, giving `v(Δ) < 1`. -/
theorem FreyPackage.freyCurve_hasMultiplicativeReduction_of_dvd (P : FreyPackage)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : (q : ℤ) ∣ P.a * P.b * P.c) :
    P.freyCurve.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
  set R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal with hR
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  -- `q`-integrality: every coefficient of the Frey equation is an integer
  haveI hInt : IsIntegral R P.freyCurve := by
    rw [← FreyCurve.map P]
    refine isIntegral_of_exists_lift R ?_ ?_ ?_ ?_ ?_ <;>
      exact ⟨_, (map_intCast (algebraMap R ℚ) _).trans
        (eq_intCast (algebraMap ℤ ℚ) _).symm⟩
  -- exactly one of `ab`, `c` is divisible by `q`
  have hxor : Xor ((q : ℤ) ∣ P.a * P.b) ((q : ℤ) ∣ P.c) := by
    rw [xor_iff_not_iff, iff_iff_and_or_not_and_not]
    rintro (⟨hab, hc⟩ | ⟨hab, hc⟩)
    · rw [hqZ.dvd_mul] at hab
      apply hqZ.not_dvd_one
      cases hab with
      | inl ha => rw [← P.hgcdac]; exact dvd_gcd ha hc
      | inr hb => rw [← P.hgcdbc]; exact dvd_gcd hb hc
    · rw [hqZ.dvd_mul] at hdvd
      exact hdvd.rec hab hc
  -- `q` does not divide the integer `c^{2p} - (ab)^p`
  have hc₄ndvd : ¬((q : ℤ) ∣ P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) := by
    have h2p0 : 2 * P.p ≠ 0 := mul_ne_zero two_ne_zero P.hp0
    cases hxor with
    | inl h =>
      rw [dvd_sub_left (dvd_pow h.1 P.hp0), hqZ.dvd_pow_iff_dvd h2p0]
      exact h.2
    | inr h =>
      rw [dvd_sub_right (dvd_pow h.1 h2p0), hqZ.dvd_pow_iff_dvd P.hp0]
      exact h.2
  -- `v(c₄) = 1`: `c₄` is the image of a unit of `ℤ_(q)`
  have hc₄cast : P.freyCurve.c₄ =
      ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p : ℤ) : ℚ) := by
    rw [FreyCurve.c₄']
    push_cast
    ring
  have huc₄ : IsUnit ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p : ℤ) : R) :=
    isUnit_intCast_localizationAtPrime hq hc₄ndvd
  have hvalc₄ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (IsDiscreteValuationRing.maximalIdeal R) P.freyCurve.c₄ = 1 := by
    have hmem : P.freyCurve.c₄ ∈ MonoidHom.mker
        ((IsDiscreteValuationRing.maximalIdeal R).valuation ℚ) := by
      rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid]
      exact Submonoid.mem_map.mpr
        ⟨_, huc₄, (hc₄cast.trans (map_intCast (algebraMap R ℚ) _).symm).symm⟩
    exact MonoidHom.mem_mker.mp hmem
  -- `v(Δ) < 1`: `Δ` is the image of an element of the maximal ideal
  have h2 : ¬((q : ℤ) ∣ (2 : ℤ)) := by
    intro h
    have hq2' : q ∣ 2 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2')
  have hu2 : IsUnit (((2 : ℤ) : R)) := isUnit_intCast_localizationAtPrime hq h2
  have hΔeq : P.freyCurve.Δ = algebraMap R ℚ
      ((((P.a * P.b * P.c : ℤ) : R)) ^ (2 * P.p) * (↑hu2.unit⁻¹ : R) ^ 8) := by
    rw [FreyCurve.Δ, map_mul, map_pow, map_intCast, map_pow, map_units_inv,
      IsUnit.unit_spec, map_intCast]
    push_cast
    rw [div_eq_mul_inv, inv_pow]
  have habcmem : ((P.a * P.b * P.c : ℤ) : R) ∈ IsLocalRing.maximalIdeal R := by
    have h1 : ((P.a * P.b * P.c : ℤ) : NumberField.RingOfIntegers ℚ) ∈
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
      (intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff hq _).mpr hdvd
    have h2' := (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ((P.a * P.b * P.c : ℤ) : NumberField.RingOfIntegers ℚ)).mpr h1
    rwa [map_intCast] at h2'
  have hΔmem : (((P.a * P.b * P.c : ℤ) : R)) ^ (2 * P.p) * (↑hu2.unit⁻¹ : R) ^ 8 ∈
      IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ habcmem _ (mul_pos (by norm_num) P.hppos))
  have hvalΔ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (IsDiscreteValuationRing.maximalIdeal R) P.freyCurve.Δ < 1 := by
    rw [hΔeq]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal R) _).mpr hΔmem
  -- assemble: minimality is the unit-`c₄` Kraus–Laska criterion
  exact { toIsMinimal := isMinimal_of_valuation_c₄_eq_one (R := R) P.freyCurve hvalc₄
          badReduction := hvalΔ
          multiplicativeReduction := hvalc₄ }

open WeierstrassCurve in
/-- **Multiplicative reduction of the Frey curve at `2`** (PROVEN
2026-07-16): the Frey model
`y² + xy = x³ + ((b^p-1-a^p)/4)x² - (a^p b^p/16)x` — chosen precisely to
be semistable at `2` — has multiplicative reduction over `ℤ_(2)`: the
equation is `2`-integral; `c₄ = c^{2p} - (ab)^p` is odd (`a ≡ 3 mod 4`
makes `a` odd, `b` is even, so `c` is odd and `(ab)^p` is even), giving
`v(c₄) = 1` and minimality by the unit-`c₄` Kraus–Laska criterion; and
`Δ = (abc)^{2p}/2⁸ = 2^{2p-8}·(ab'c)^{2p}` (where `b = 2b'`) lies in the
maximal ideal since `2p > 8`. -/
theorem FreyPackage.freyCurve_hasMultiplicativeReduction_at_two (P : FreyPackage) :
    P.freyCurve.HasMultiplicativeReduction
      (Localization.AtPrime Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
  set R := Localization.AtPrime Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal
  have h2Z : Prime (2 : ℤ) := Int.prime_two
  -- `2`-integrality: every coefficient of the Frey equation is an integer
  haveI hInt : IsIntegral R P.freyCurve := by
    rw [← FreyCurve.map P]
    refine isIntegral_of_exists_lift R ?_ ?_ ?_ ?_ ?_ <;>
      exact ⟨_, (map_intCast (algebraMap R ℚ) _).trans
        (eq_intCast (algebraMap ℤ ℚ) _).symm⟩
  -- parities: `b` even, `a` odd, `c` odd
  have hb2 : (2 : ℤ) ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).mp P.hb2
  have ha4' : P.a % 4 = 3 := by
    have h := (ZMod.intCast_eq_intCast_iff P.a 3 4).mp (by exact_mod_cast P.ha4)
    simpa [Int.ModEq] using h
  have ha_odd : ¬((2 : ℤ) ∣ P.a) := by omega
  have hc_odd : ¬((2 : ℤ) ∣ P.c) := by
    intro h
    have h1 : (2 : ℤ) ∣ P.c ^ P.p := dvd_pow h P.hp0
    have h2 : (2 : ℤ) ∣ P.b ^ P.p := dvd_pow hb2 P.hp0
    have h3 : (2 : ℤ) ∣ P.a ^ P.p := by
      have hFLT := P.hFLT
      have : P.a ^ P.p = P.c ^ P.p - P.b ^ P.p := by linarith
      rw [this]
      exact dvd_sub h1 h2
    exact ha_odd (h2Z.dvd_of_dvd_pow h3)
  -- `c₄ = c^{2p} - (ab)^p` is odd
  have hc₄ndvd : ¬((2 : ℤ) ∣ P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) := by
    intro h
    have hab : (2 : ℤ) ∣ (P.a * P.b) ^ P.p :=
      dvd_pow (Dvd.dvd.mul_left hb2 P.a) P.hp0
    have hcpow : (2 : ℤ) ∣ P.c ^ (2 * P.p) := (dvd_sub_left hab).mp h
    exact hc_odd (h2Z.dvd_of_dvd_pow hcpow)
  -- `v(c₄) = 1`
  have hc₄cast : P.freyCurve.c₄ =
      ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p : ℤ) : ℚ) := by
    rw [FreyCurve.c₄']
    push_cast
    ring
  have huc₄ : IsUnit ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p : ℤ) : R) :=
    isUnit_intCast_localizationAtPrime Nat.prime_two hc₄ndvd
  have hvalc₄ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (IsDiscreteValuationRing.maximalIdeal R) P.freyCurve.c₄ = 1 := by
    have hmem : P.freyCurve.c₄ ∈ MonoidHom.mker
        ((IsDiscreteValuationRing.maximalIdeal R).valuation ℚ) := by
      rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid]
      exact Submonoid.mem_map.mpr
        ⟨_, huc₄, (hc₄cast.trans (map_intCast (algebraMap R ℚ) _).symm).symm⟩
    exact MonoidHom.mem_mker.mp hmem
  -- `v(Δ) < 1`: with `b = 2b'`, `Δ = 2^{2p-8}·(ab'c)^{2p}` and `2p > 8`
  obtain ⟨b', hb'⟩ := hb2
  have h2p8 : 8 ≤ 2 * P.p := by
    have := P.hp5
    omega
  have hΔeq2 : P.freyCurve.Δ = algebraMap R ℚ
      ((((2 : ℤ) : R)) ^ (2 * P.p - 8) * (((P.a * b' * P.c : ℤ) : R)) ^ (2 * P.p)) := by
    rw [FreyCurve.Δ, map_mul, map_pow, map_pow, map_intCast, map_intCast, hb']
    push_cast
    rw [show (P.a : ℚ) * (2 * (b' : ℚ)) * (P.c : ℚ)
        = 2 * ((P.a : ℚ) * (b' : ℚ) * (P.c : ℚ)) by ring, mul_pow,
      show (2 : ℚ) ^ (2 * P.p) = 2 ^ (2 * P.p - 8) * 2 ^ 8 by
        rw [← pow_add]; congr 1; omega]
    field_simp
  have h2mem : (((2 : ℤ) : R)) ∈ IsLocalRing.maximalIdeal R := by
    have h1 : ((2 : ℤ) : NumberField.RingOfIntegers ℚ) ∈
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
      (intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff Nat.prime_two _).mpr
        (by norm_num)
    have h2' := (IsLocalization.AtPrime.to_map_mem_maximal_iff
      R Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ((2 : ℤ) : NumberField.RingOfIntegers ℚ)).mpr h1
    rwa [map_intCast] at h2'
  have hΔmem : (((2 : ℤ) : R)) ^ (2 * P.p - 8) *
      (((P.a * b' * P.c : ℤ) : R)) ^ (2 * P.p) ∈ IsLocalRing.maximalIdeal R := by
    have hpos : 0 < 2 * P.p - 8 := by
      have := P.hp5
      omega
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ h2mem _ hpos)
  have hvalΔ : IsDedekindDomain.HeightOneSpectrum.valuation ℚ
      (IsDiscreteValuationRing.maximalIdeal R) P.freyCurve.Δ < 1 := by
    rw [hΔeq2]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal R) _).mpr hΔmem
  exact { toIsMinimal := isMinimal_of_valuation_c₄_eq_one (R := R) P.freyCurve hvalc₄
          badReduction := hvalΔ
          multiplicativeReduction := hvalc₄ }

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The `v`-adic valuation of `ℚ` is equivalent to the maximal-ideal
valuation of its localization** (PROVEN — the dictionary between the
two spellings of the same place): the place `v_q` of `ℚ` and the
maximal ideal of `ℤ_(q) = Localization.AtPrime v_q` induce equivalent
valuations on `ℚ`. Both `≤ 1`-conditions say that `q` does not divide
the denominator (`Rat.valuation_le_one_iff_den` on either side, with
`IsLocalization.AtPrime.to_map_mem_maximal_iff` translating maximal-
ideal membership of the denominator through the localization). This is
the bridge between the `HasMultiplicativeReduction ℤ_(q)` data of the
tree and the completed valuation of `adicCompletion ℚ v_q`
(`valuedAdicCompletion_eq_valuation'`). -/
theorem isEquiv_valuation_maximalIdeal_localization {q : ℕ} (hq : q.Prime) :
    (hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ).IsEquiv
      ((IsDiscreteValuationRing.maximalIdeal
        (Localization.AtPrime
          hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Rat.valuation_le_one_iff_den, Rat.valuation_le_one_iff_den]
  constructor
  · intro h hmem
    apply h
    have h2 : algebraMap (NumberField.RingOfIntegers ℚ)
        (Localization.AtPrime
          hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
        ((x.den : NumberField.RingOfIntegers ℚ)) ∈
        IsLocalRing.maximalIdeal
          (Localization.AtPrime
            hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
      rw [map_natCast]
      exact hmem
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ((x.den : NumberField.RingOfIntegers ℚ))).mp h2
  · intro h hmem
    apply h
    have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal
      ((x.den : NumberField.RingOfIntegers ℚ))).mpr hmem
    rwa [map_natCast] at h2

open ValuativeRel IsDedekindDomain WithZero WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Multiplicative reduction transfers to the completion** (PROVEN —
step (B) of the Tate-multiplicative plumbing): an elliptic curve over
`ℚ` with multiplicative reduction over `ℤ_(q)` has multiplicative
reduction over the ring of integers of the completed field
`adicCompletion ℚ v_q`. The chase: coefficients and `c₄`, `Δ` move
along `algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)` with `Valued.v ∘ algebraMap = hq.toHeightOneSpectrumRingOfIntegersRat`-adic
valuation (`valuedAdicCompletion_eq_valuation'`); the `ℤ_(q)`-side
maximal-ideal valuation converts to the `hq.toHeightOneSpectrumRingOfIntegersRat`-adic valuation by the
PROVEN dictionary (`isEquiv_valuation_maximalIdeal_localization`); the
`(HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)`-side `Valued.v` converts to the canonical valuation
(`ValuativeRel.isEquiv`) and back to the maximal-ideal-adic form
(`adicValuation_eq_one_iff`/`_lt_one_iff`); minimality over `𝒪[HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat]`
is the unit-`c₄` Kraus–Laska criterion. -/
theorem hasMultiplicativeReduction_adicCompletion {q : ℕ} (hq : q.Prime)
    (E : WeierstrassCurve ℚ)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).HasMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] := by
  classical
  -- the valuation of a `(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))`-image is the `hq.toHeightOneSpectrumRingOfIntegersRat`-adic valuation
  have hval : ∀ x : ℚ, (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) =
      hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x := by
    have hcoe : ∀ x : ℚ, (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) x =
        ({ toCompletion := ↑((WithVal.equiv (HeightOneSpectrum.valuation ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)).symm x) } :
          HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) := by
      intro x
      have hhom := Subsingleton.elim
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ((({ toFun := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
             map_one' := rfl
             map_mul' := fun _ _ => rfl
             map_zero' := rfl
             map_add' := fun _ _ => rfl } :
            (HeightOneSpectrum.valuation ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat).Completion →+*
            HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat).comp
          (UniformSpace.Completion.coeRingHom)).comp
          ((WithVal.equiv (HeightOneSpectrum.valuation ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)).symm.toRingHom))
      rw [hhom]
      rfl
    intro x
    rw [hcoe x]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      hq.toHeightOneSpectrumRingOfIntegersRat x
  -- the two `ℚ`-side valuations are equivalent
  have hdict := isEquiv_valuation_maximalIdeal_localization hq
  -- the two `(HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)`-side valuations are equivalent
  have hKeq : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) :=
    ValuativeRel.isEquiv _ _
  -- `≤ 1`-transfer chain, `ℚ`-side maximal-ideal form to `(HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)` canonical
  have hle : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x ≤ 1 →
      ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) ≤ 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x ≤ 1 :=
      (Valuation.isEquiv_iff_val_le_one.mp hdict).mpr hx
    have h2 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) ≤ 1 := by
      rw [hval]
      exact h1
    exact (Valuation.isEquiv_iff_val_le_one.mp hKeq).mpr h2
  -- the same chains at `= 1` and `< 1`
  have heq1 : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x = 1 →
      ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) = 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x = 1 :=
      (Valuation.isEquiv_iff_val_eq_one.mp hdict).mpr hx
    have h2 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) = 1 := by
      rw [hval]
      exact h1
    exact (Valuation.isEquiv_iff_val_eq_one.mp hKeq).mpr h2
  have hlt1 : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x < 1 →
      ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) < 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x < 1 :=
      (Valuation.isEquiv_iff_val_lt_one.mp hdict).mpr hx
    have h2 : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) < 1 := by
      rw [hval]
      exact h1
    exact (Valuation.isEquiv_iff_val_lt_one.mp hKeq).mpr h2
  -- integrality of the mapped curve
  have hRint : IsIntegral (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E := by
    have h1 := (HasMultiplicativeReduction.toIsMinimal
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (W := E)).val_Δ_maximal.1
    simp only [one_smul] at h1
    exact h1
  have hcoeff : ∀ x : ℚ, x ∈ Set.range (algebraMap (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ) →
      ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) x) ≤ 1 := by
    rintro x ⟨r, rfl⟩
    exact hle _ (IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) r)
  haveI hKint : IsIntegral 𝒪[HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat] (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    refine isIntegral_of_exists_lift 𝒪[HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat]
      ⟨⟨(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) E.a₁, ?_⟩, ?_⟩ ⟨⟨(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) E.a₂, ?_⟩, ?_⟩ ⟨⟨(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) E.a₃, ?_⟩, ?_⟩
      ⟨⟨(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) E.a₄, ?_⟩, ?_⟩ ⟨⟨(algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) E.a₆, ?_⟩, ?_⟩
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₁,
      integralModel_a₁_eq (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₂,
      integralModel_a₂_eq (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₃,
      integralModel_a₃_eq (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₄,
      integralModel_a₄_eq (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₆,
      integralModel_a₆_eq (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
  -- `c₄` has canonical valuation `1` upstairs
  have hc₄R : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ E.c₄ = 1 :=
    HasMultiplicativeReduction.multiplicativeReduction
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) (W := E)
  have hc₄K : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).c₄) = 1 := by
    rw [WeierstrassCurve.map_c₄]
    exact heq1 _ hc₄R
  -- back to the maximal-ideal-adic form over `𝒪[HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat]`
  have hc₄mem : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).c₄ ∈ (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)).integer := by
    rw [Valuation.mem_integer_iff, hc₄K]
  have hc₄adic : (IsDiscreteValuationRing.maximalIdeal
      (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)).integer).valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).c₄) = 1 := by
    have h1 := (ValuativeRel.adicValuation_eq_one_iff
      (K := (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) (x := ⟨(E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).c₄, hc₄mem⟩)).mpr
    exact h1 hc₄K
  -- discriminant strictly small upstairs
  have hΔR : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ E.Δ < 1 :=
    HasMultiplicativeReduction.badReduction
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) (W := E)
  have hΔK : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).Δ) < 1 := by
    rw [WeierstrassCurve.map_Δ]
    exact hlt1 _ hΔR
  have hΔmem : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).Δ ∈ (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)).integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_lt hΔK
  have hΔadic : (IsDiscreteValuationRing.maximalIdeal
      (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)).integer).valuation (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat) ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).Δ) < 1 := by
    have h1 := (ValuativeRel.adicValuation_lt_one_iff
      (K := (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat)) (x := ⟨(E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))).Δ, hΔmem⟩)).mpr
    exact h1 hΔK
  exact { toIsMinimal := isMinimal_of_valuation_c₄_eq_one
            (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat]) (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ hq.toHeightOneSpectrumRingOfIntegersRat))) hc₄adic
          badReduction := hΔadic
          multiplicativeReduction := hc₄adic }

open ValuativeRel IsDedekindDomain WithZero WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Multiplicative reduction transfers to the `p`-adic field** (the
step-(B) analogue targeting mathlib's `ℚ_[q]`, for the tame-at-`2`
interface): an elliptic curve over `ℚ` with multiplicative reduction
over `ℤ_(q)` has multiplicative reduction over the ring of integers of
`ℚ_[q]`. All valuation conversions are `IsEquiv`-chains: maximal-ideal
form to the `v_q`-adic valuation
(`isEquiv_valuation_maximalIdeal_localization`), to mathlib's
`Rat.padicValuation` (`valuation_equiv_padicValuation`, with the
generator identification `natGenerator_toHeightOneSpectrum`), to
`Padic.mulValuation` by the LITERAL comap identity
(`comap_mulValuation_eq_padicValuation`), to the canonical valuation of
`ℚ_[q]` (`ValuativeRel.isEquiv`). -/
theorem hasMultiplicativeReduction_padic {q : ℕ} (hq : q.Prime)
    (E : WeierstrassCurve ℚ)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    haveI : Fact q.Prime := ⟨hq⟩
    (E.map (algebraMap ℚ ℚ_[q])).HasMultiplicativeReduction 𝒪[ℚ_[q]] := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  -- the equivalence chain, condition by condition
  have hdict := isEquiv_valuation_maximalIdeal_localization hq
  have hQeq : (hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ).IsEquiv
      (Rat.padicValuation q) := by
    have h0 := Rat.HeightOneSpectrum.valuation_equiv_padicValuation
      (R := NumberField.RingOfIntegers ℚ) hq.toHeightOneSpectrumRingOfIntegersRat
    have hgen : ((Rat.HeightOneSpectrum.primesEquiv
        hq.toHeightOneSpectrumRingOfIntegersRat : Nat.Primes) : ℕ) = q :=
      GaloisRepresentation.natGenerator_toHeightOneSpectrum hq
    simpa only [hgen] using h0
  have hKeq : (ValuativeRel.valuation ℚ_[q]).IsEquiv
      (Padic.mulValuation (p := q)) := ValuativeRel.isEquiv _ _
  have hcast : (algebraMap ℚ ℚ_[q]) = (Rat.castHom ℚ_[q]) :=
    Subsingleton.elim _ _
  have hpt : ∀ x : ℚ, Padic.mulValuation ((algebraMap ℚ ℚ_[q]) x) =
      Rat.padicValuation q x := by
    intro x
    rw [hcast]
    exact congrFun (congrArg (fun v : Valuation ℚ ℤᵐ⁰ => (v : ℚ → ℤᵐ⁰))
      (Padic.comap_mulValuation_eq_padicValuation (p := q))) x
  have hle : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x ≤ 1 →
      ValuativeRel.valuation ℚ_[q] ((algebraMap ℚ ℚ_[q]) x) ≤ 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x ≤ 1 :=
      (Valuation.isEquiv_iff_val_le_one.mp hdict).mpr hx
    have h2 : Rat.padicValuation q x ≤ 1 :=
      (Valuation.isEquiv_iff_val_le_one.mp hQeq).mp h1
    have h3 : Padic.mulValuation ((algebraMap ℚ ℚ_[q]) x) ≤ 1 := by
      rw [hpt]
      exact h2
    exact (Valuation.isEquiv_iff_val_le_one.mp hKeq).mpr h3
  have heq1 : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x = 1 →
      ValuativeRel.valuation ℚ_[q] ((algebraMap ℚ ℚ_[q]) x) = 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x = 1 :=
      (Valuation.isEquiv_iff_val_eq_one.mp hdict).mpr hx
    have h2 : Rat.padicValuation q x = 1 :=
      (Valuation.isEquiv_iff_val_eq_one.mp hQeq).mp h1
    have h3 : Padic.mulValuation ((algebraMap ℚ ℚ_[q]) x) = 1 := by
      rw [hpt]
      exact h2
    exact (Valuation.isEquiv_iff_val_eq_one.mp hKeq).mpr h3
  have hlt1 : ∀ x : ℚ,
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ x < 1 →
      ValuativeRel.valuation ℚ_[q] ((algebraMap ℚ ℚ_[q]) x) < 1 := by
    intro x hx
    have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x < 1 :=
      (Valuation.isEquiv_iff_val_lt_one.mp hdict).mpr hx
    have h2 : Rat.padicValuation q x < 1 :=
      (Valuation.isEquiv_iff_val_lt_one.mp hQeq).mp h1
    have h3 : Padic.mulValuation ((algebraMap ℚ ℚ_[q]) x) < 1 := by
      rw [hpt]
      exact h2
    exact (Valuation.isEquiv_iff_val_lt_one.mp hKeq).mpr h3
  -- integrality of the mapped curve
  have hRint : IsIntegral (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E := by
    have h1 := (HasMultiplicativeReduction.toIsMinimal
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (W := E)).val_Δ_maximal.1
    simp only [one_smul] at h1
    exact h1
  have hcoeff : ∀ x : ℚ, x ∈ Set.range (algebraMap (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ) →
      ValuativeRel.valuation ℚ_[q] ((algebraMap ℚ ℚ_[q]) x) ≤ 1 := by
    rintro x ⟨r, rfl⟩
    exact hle _ (IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) r)
  haveI hKint : IsIntegral 𝒪[ℚ_[q]] (E.map (algebraMap ℚ ℚ_[q])) := by
    refine isIntegral_of_exists_lift 𝒪[ℚ_[q]]
      ⟨⟨(algebraMap ℚ ℚ_[q]) E.a₁, ?_⟩, ?_⟩
      ⟨⟨(algebraMap ℚ ℚ_[q]) E.a₂, ?_⟩, ?_⟩
      ⟨⟨(algebraMap ℚ ℚ_[q]) E.a₃, ?_⟩, ?_⟩
      ⟨⟨(algebraMap ℚ ℚ_[q]) E.a₄, ?_⟩, ?_⟩
      ⟨⟨(algebraMap ℚ ℚ_[q]) E.a₆, ?_⟩, ?_⟩
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₁,
      integralModel_a₁_eq (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₂,
      integralModel_a₂_eq (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₃,
      integralModel_a₃_eq (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₄,
      integralModel_a₄_eq (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
    case _ => exact hcoeff _ ⟨(integralModel (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E).a₆,
      integralModel_a₆_eq (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) E⟩
    case _ => exact rfl
  -- `c₄` and `Δ` conditions upstairs
  have hc₄R : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ E.c₄ = 1 :=
    HasMultiplicativeReduction.multiplicativeReduction
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (W := E)
  have hc₄K : ValuativeRel.valuation ℚ_[q]
      ((E.map (algebraMap ℚ ℚ_[q])).c₄) = 1 := by
    rw [WeierstrassCurve.map_c₄]
    exact heq1 _ hc₄R
  have hc₄mem : (E.map (algebraMap ℚ ℚ_[q])).c₄ ∈
      (ValuativeRel.valuation ℚ_[q]).integer := by
    rw [Valuation.mem_integer_iff, hc₄K]
  have hc₄adic : (IsDiscreteValuationRing.maximalIdeal
      (ValuativeRel.valuation ℚ_[q]).integer).valuation ℚ_[q]
      ((E.map (algebraMap ℚ ℚ_[q])).c₄) = 1 := by
    have h1 := (ValuativeRel.adicValuation_eq_one_iff
      (K := ℚ_[q]) (x := ⟨(E.map (algebraMap ℚ ℚ_[q])).c₄, hc₄mem⟩)).mpr
    exact h1 hc₄K
  have hΔR : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
      hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ E.Δ < 1 :=
    HasMultiplicativeReduction.badReduction
      (R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      (W := E)
  have hΔK : ValuativeRel.valuation ℚ_[q]
      ((E.map (algebraMap ℚ ℚ_[q])).Δ) < 1 := by
    rw [WeierstrassCurve.map_Δ]
    exact hlt1 _ hΔR
  have hΔmem : (E.map (algebraMap ℚ ℚ_[q])).Δ ∈
      (ValuativeRel.valuation ℚ_[q]).integer := by
    rw [Valuation.mem_integer_iff]
    exact le_of_lt hΔK
  have hΔadic : (IsDiscreteValuationRing.maximalIdeal
      (ValuativeRel.valuation ℚ_[q]).integer).valuation ℚ_[q]
      ((E.map (algebraMap ℚ ℚ_[q])).Δ) < 1 := by
    have h1 := (ValuativeRel.adicValuation_lt_one_iff
      (K := ℚ_[q]) (x := ⟨(E.map (algebraMap ℚ ℚ_[q])).Δ, hΔmem⟩)).mpr
    exact h1 hΔK
  exact { toIsMinimal := isMinimal_of_valuation_c₄_eq_one
            (R := 𝒪[ℚ_[q]]) (E.map (algebraMap ℚ ℚ_[q])) hc₄adic
          badReduction := hΔadic
          multiplicativeReduction := hc₄adic }

/-- The tower `ℚ → ℚ_[q] → ℚ_[q]ᵃˡᵍ` algebra structure on the `p`-adic
algebraic closure (the `ℚ_[q]`-analogue of `algebraRatAlgClosureAdic`,
used consistently by the tame-at-`2` transport lemmas so that the two
spellings of the closure-stage base change are definitionally equal
curves). Not an instance: installed with `letI` per statement. -/
@[reducible] noncomputable def algebraRatAlgClosurePadic (q : ℕ)
    [Fact q.Prime] : Algebra ℚ (AlgebraicClosure ℚ_[q]) :=
  ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp
    (algebraMap ℚ ℚ_[q])).toAlgebra

/-- A classical decidable-equality instance on the `p`-adic algebraic
closure (needed for the group law on points). -/
noncomputable instance instDecidableEqAlgClosurePadic (q : ℕ)
    [Fact q.Prime] : DecidableEq (AlgebraicClosure ℚ_[q]) :=
  Classical.typeDecidableEq _

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The chosen embedding `ℚ̄ → ℚ_[q]ᵃˡᵍ` as a `ℚ`-algebra homomorphism
over the tower (`algebraRatAlgClosurePadic`); the `ℚ_[q]`-analogue of
`algClosureEmbeddingRat`. -/
noncomputable def algClosureEmbeddingPadic (q : ℕ) [Fact q.Prime] :
    letI := algebraRatAlgClosurePadic q
    ((AlgebraicClosure ℚ) →ₐ[ℚ] (AlgebraicClosure ℚ_[q])) :=
  letI := algebraRatAlgClosurePadic q
  { AlgebraicClosure.map (algebraMap ℚ ℚ_[q]) with
    commutes' := fun r => by
      have h1 := AlgebraicClosure.map_algebraMap (algebraMap ℚ ℚ_[q]) r
      exact h1 }

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The action of a local Galois element on the `p`-adic algebraic
closure, as a `ℚ`-algebra homomorphism over the tower; the
`ℚ_[q]`-analogue of `algClosureSigmaRat`. -/
noncomputable def algClosureSigmaPadic (q : ℕ) [Fact q.Prime]
    (σ : Field.absoluteGaloisGroup ℚ_[q]) :
    letI := algebraRatAlgClosurePadic q
    ((AlgebraicClosure ℚ_[q]) →ₐ[ℚ] (AlgebraicClosure ℚ_[q])) :=
  letI := algebraRatAlgClosurePadic q
  { ((σ : (AlgebraicClosure ℚ_[q]) ≃ₐ[ℚ_[q]]
      (AlgebraicClosure ℚ_[q])).toAlgHom.toRingHom) with
    commutes' := fun r =>
      (σ : (AlgebraicClosure ℚ_[q]) ≃ₐ[ℚ_[q]]
        (AlgebraicClosure ℚ_[q])).commutes ((algebraMap ℚ ℚ_[q]) r) }

open WeierstrassCurve in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Equivariance of the `p`-adic point transport** (the
`ℚ_[q]`-analogue of `point_map_algClosureEmbeddingRat_comm`): `σ` after
the transport equals the transport after the global image of `σ`; both
sides reduce to `Field.absoluteGaloisGroup.lift_map` by
`Point.map_map`. -/
theorem point_map_algClosureEmbeddingPadic_comm (q : ℕ) [Fact q.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (σ : Field.absoluteGaloisGroup ℚ_[q])
    (P : ((E)⁄(AlgebraicClosure ℚ)).Point) :
    letI := algebraRatAlgClosurePadic q
    WeierstrassCurve.Affine.Point.map (W' := E) (algClosureEmbeddingPadic q)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[q])) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) =
    WeierstrassCurve.Affine.Point.map (W' := E) (algClosureSigmaPadic q σ)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingPadic q) P) := by
  letI := algebraRatAlgClosurePadic q
  rw [WeierstrassCurve.Affine.Point.map_map,
    WeierstrassCurve.Affine.Point.map_map]
  have hhomeq : (algClosureEmbeddingPadic q).comp
      (((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[q])) σ :
        AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom =
      (algClosureSigmaPadic q σ).comp (algClosureEmbeddingPadic q) := by
    apply AlgHom.ext
    intro x
    exact Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ_[q]) σ x
  rw [hhomeq]


open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The residue characteristic of the local valuation subring**
(PROVEN): a prime `p ≠ q` is nonzero in the residue field of the
integral closure of `ℤ_qˆ` in `ℚ_qᵃˡᵍ`. Content: `p` is a unit of
`ℤ_qˆ` (`isUnit_natCast_adicCompletionIntegers`, PROVEN), its
valuation-subring image is a unit (the inverse is integral, being an
`ℤ_qˆ`-element), and units have nonzero residue. This discharges the
`hchar`-hypothesis of `tate_inertia_unipotent` at `A =
localValuationSubring v_q` for the `p`-torsion, `p ≠ q`. -/
theorem natCast_residueField_localValuationSubring_ne_zero
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ((p : ℕ) : IsLocalRing.ResidueField
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0 := by
  classical
  -- every `ℤ_qˆ`-element is integral in the algebraic closure
  have hmem : ∀ z : (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat),
      ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) (z : _)) ∈
        localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro z
    show IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) _
    rw [show ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) (z : _)) =
      (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) z from
      (IsScalarTower.algebraMap_apply _ _ _ z).symm]
    exact isIntegral_algebraMap
  -- the integral-closure inclusion as a ring homomorphism
  let j : (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+*
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    { toFun := fun z => ⟨_, hmem z⟩
      map_one' := Subtype.ext (by push_cast; rfl)
      map_mul' := fun a b => Subtype.ext (by push_cast; rfl)
      map_zero' := Subtype.ext (by push_cast; rfl)
      map_add' := fun a b => Subtype.ext (by push_cast; rfl) }
  -- `p` is a unit of `ℤ_qˆ`, hence of the subring, hence of the residue field
  have hunitA : IsUnit ((p : ℕ) : localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat) := by
    have h1 := (GaloisRepresentation.isUnit_natCast_adicCompletionIntegers
      hp hq hne).map j
    rwa [map_natCast] at h1
  have h2 := hunitA.map (IsLocalRing.residue
    (localValuationSubring (K := ℚ) hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [map_natCast] at h2
  exact h2.ne_zero


set_option backward.isDefEq.respectTransparency false in
/-- **The `v_q`-adic valuation of an integer prime to `q` is `1`**:
the integer avoids the prime, so its `intValuation` is `1`. -/
lemma valuation_intCast_eq_one_of_not_dvd {q : ℕ} (hq : q.Prime) {n : ℤ}
    (hn : ¬ (q : ℤ) ∣ n) :
    hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ ((n : ℤ) : ℚ) = 1 := by
  rw [show ((n : ℤ) : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
      ((n : ℤ) : NumberField.RingOfIntegers ℚ) from (map_intCast _ n).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff,
    intCast_mem_toHeightOneSpectrumRingOfIntegersRat_iff hq]
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-- **The reduced-fraction dictionary at `q`**: a nonzero rational whose
`q`-adic `padicValRat` vanishes has `v_q`-adic valuation `1`. In lowest
terms the numerator and denominator have EQUAL `q`-multiplicities, and
coprimality forces both to vanish; then numerator and denominator each
have valuation `1`. -/
lemma valuation_eq_one_of_padicValRat_eq_zero {q : ℕ} (hq : q.Prime)
    {x : ℚ} (hx : x ≠ 0) (h : padicValRat q x = 0) :
    hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hnum0 : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hden0 : x.den ≠ 0 := x.den_nz
  -- equal `q`-multiplicities of numerator and denominator
  have hkey : padicValNat q x.num.natAbs = padicValNat q x.den := by
    have h1 : (padicValInt q x.num : ℤ) - (padicValNat q x.den : ℤ) = 0 := h
    have h2 : padicValInt q x.num = padicValNat q x.num.natAbs := rfl
    omega
  have hcop : Nat.gcd x.num.natAbs x.den = 1 := x.reduced
  -- `q` divides neither the numerator nor the denominator
  have hnd : ¬ q ∣ x.num.natAbs := by
    intro hdvd
    have h1 : 1 ≤ padicValNat q x.num.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum0) hdvd
    have h2 : q ∣ x.den := dvd_of_one_le_padicValNat (by omega)
    have h3 : q ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd hdvd h2
    rw [hcop] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.mp h3)
  have hdd : ¬ q ∣ x.den := by
    intro hdvd
    have h1 : 1 ≤ padicValNat q x.den :=
      one_le_padicValNat_of_dvd hden0 hdvd
    have h2 : q ∣ x.num.natAbs := dvd_of_one_le_padicValNat (by omega)
    have h3 : q ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd h2 hdvd
    rw [hcop] at h3
    exact hq.one_lt.ne' (Nat.dvd_one.mp h3)
  -- integer-cast divisibility forms
  have hnd' : ¬ (q : ℤ) ∣ x.num := by
    intro hdvd
    have h4 := Int.natAbs_dvd_natAbs.mpr hdvd
    rw [Int.natAbs_natCast] at h4
    exact hnd h4
  have hdd' : ¬ (q : ℤ) ∣ (x.den : ℤ) := by
    intro hdvd
    exact hdd (Int.ofNat_dvd.mp hdvd)
  -- assemble along `x = num / den`
  have hx' : x = ((x.num : ℤ) : ℚ) / (((x.den : ℤ) : ℚ)) := by
    push_cast
    exact (Rat.num_div_den x).symm
  rw [hx', map_div₀, valuation_intCast_eq_one_of_not_dvd hq hnd',
    valuation_intCast_eq_one_of_not_dvd hq hdd', div_one]

open IsDedekindDomain WithZero in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The completed valuation restricted along `algebraMap ℚ` is the
`v_q`-adic valuation** (the `hval` bridge of step (B), extracted for
reuse): the algebra map into the completion is the canonical coercion,
so `valuedAdicCompletion_eq_valuation'` applies. -/
theorem valued_algebraMap_adicCompletion_eq {q : ℕ} (hq : q.Prime) (x : ℚ) :
    (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰)
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) x) =
      hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ x := by
  have hcoe : (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) x =
      ({ toCompletion := ↑((WithVal.equiv (HeightOneSpectrum.valuation ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)).symm x) } :
        HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) := by
    have hhom := Subsingleton.elim
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
      ((({ toFun := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
           map_one' := rfl
           map_mul' := fun _ _ => rfl
           map_zero' := rfl
           map_add' := fun _ _ => rfl } :
          (HeightOneSpectrum.valuation ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat).Completion →+*
          HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat).comp
        (UniformSpace.Completion.coeRingHom)).comp
        ((WithVal.equiv (HeightOneSpectrum.valuation ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)).symm.toRingHom))
    rw [hhom]
    rfl
  rw [hcoe]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    hq.toHeightOneSpectrumRingOfIntegersRat x

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Completed integers land in the local valuation subring** (the
`hmem` step of the residue-characteristic lemma, extracted for reuse):
an element of `𝒪[ℚ_qˆ]` is integral over `𝒪[ℚ_qˆ]` in the local
algebraic closure. -/
theorem algebraMap_mem_localValuationSubring_of_integer {q : ℕ}
    (hq : q.Prime)
    (x : HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (hx : x ∈ HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) :
    (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) x ∈
      localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat := by
  show IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) _
  rw [show (algebraMap (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) x =
    (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) (⟨x, hx⟩ :
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) from
    (IsScalarTower.algebraMap_apply _ _ _ (⟨x, hx⟩ :
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)).symm]
  exact isIntegral_algebraMap

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Units of the completed integers have nonzero residue in the local
valuation subring** (the C2 unit-transport, extracted for reuse): a unit
of `𝒪[ℚ_qˆ]` stays a unit along the integral-closure inclusion into
`localValuationSubring v_q`, and units of a local ring have nonzero
residue. -/
theorem residue_localValuationSubring_ne_zero_of_isUnit {q : ℕ}
    (hq : q.Prime)
    (x : HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (hx : x ∈ HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (hu : IsUnit (⟨x, hx⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    (hmem : (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) x ∈
      localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat) :
    IsLocalRing.residue (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (⟨_, hmem⟩ : localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat) ≠ 0 := by
  classical
  -- the integral-closure inclusion as a ring homomorphism (C2 pattern)
  let j : (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) →+*
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    { toFun := fun z => ⟨_,
        algebraMap_mem_localValuationSubring_of_integer hq z.1 z.2⟩
      map_one' := Subtype.ext (by push_cast; rfl)
      map_mul' := fun a b => Subtype.ext (by push_cast; rfl)
      map_zero' := Subtype.ext (by push_cast; rfl)
      map_add' := fun a b => Subtype.ext (by push_cast; rfl) }
  have h1 : (⟨_, hmem⟩ : localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat) = j ⟨x, hx⟩ :=
    Subtype.ext rfl
  rw [h1]
  exact ((hu.map j).map (IsLocalRing.residue
    (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat))).ne_zero

open IsDedekindDomain ValuativeRel WithZero in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The canonical-valuation integers sit inside the completed integers
(the two spellings of the ring of integers of `ℚ_qˆ`, bridged by the
`Valued`/canonical valuation equivalence). -/
theorem mem_adicCompletionIntegers_of_mem_integer {q : ℕ} (hq : q.Prime)
    {x : HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat}
    (hx : x ∈ 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]) :
    x ∈ HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat := by
  have hKeq : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) :=
    ValuativeRel.isEquiv _ _
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (Valuation.isEquiv_iff_val_le_one.mp hKeq).mp
    ((Valuation.mem_integer_iff _ _).mp hx)

open IsDedekindDomain ValuativeRel WithZero in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The completed integers sit inside the canonical-valuation integers
(the reverse inclusion of the spelling bridge). -/
theorem mem_integer_of_mem_adicCompletionIntegers {q : ℕ} (hq : q.Prime)
    {x : HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat}
    (hx : x ∈ HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) :
    x ∈ 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat] := by
  have hKeq : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) :=
    ValuativeRel.isEquiv _ _
  rw [Valuation.mem_integer_iff]
  exact (Valuation.isEquiv_iff_val_le_one.mp hKeq).mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

open IsDedekindDomain ValuativeRel WithZero Polynomial in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Inertia fixes every embedding of an unramified extension**
(the local content of the nonsplit twist transfer): let `L/ℚ_qˆ` be a
field extension generated by `θ` whose monic minimal-polynomial lift
`Q` over the ring of integers has SEPARABLE residue reduction (the
unramifiedness witness produced by
`exists_quadraticTwist_hasSplitMultiplicativeReduction`). Then every
element of the inertia subgroup at the local valuation subring fixes
the image of any `ℚ_qˆ`-embedding `ι : L → ℚ_qᵃˡᵍ` pointwise. The
image `ι θ` is an integral root of `Q`; the master root-fixing lemma
(`inertia_fixes_root_of_separable_residue`) applies since inertia
fixes residues and the reduction is separable; `θ` generates, so the
whole embedding is fixed. -/
theorem inertia_fixes_algHom_of_unramified_gen {q : ℕ} (hq : q.Prime)
    {L : Type*} [Field L]
    [Algebra (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) L]
    (θ : L)
    (hθtop : Algebra.adjoin (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ({θ} : Set L) = ⊤)
    (Q : Polynomial 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat])
    (hQm : Q.Monic)
    (hθQ : Polynomial.aeval θ (Q.map (algebraMap
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = 0)
    (hQsep : (Q.map (IsLocalRing.residue
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat])).Separable)
    (σ : (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (ι : L →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))
    (y : L) :
    (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) (ι y) = ι y := by
  classical
  -- the coefficient-inclusion hom `𝒪[ℚ_qˆ] →+* A`
  have hmemA : ∀ z : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat],
      (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
        (z : HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) ∈
      localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat := fun z =>
    algebraMap_mem_localValuationSubring_of_integer hq _
      (mem_adicCompletionIntegers_of_mem_integer hq z.2)
  let j₂ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat] →+*
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    { toFun := fun z => ⟨_, hmemA z⟩
      map_one' := Subtype.ext (by push_cast; rfl)
      map_mul' := fun a b => Subtype.ext (by push_cast; rfl)
      map_zero' := Subtype.ext (by push_cast; rfl)
      map_add' := fun a b => Subtype.ext (by push_cast; rfl) }
  -- `j₂` is local: nonunits land in the maximal ideal
  have hints : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰).Integers
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    Valuation.valuationSubring.integers _
  have hj₂m : ∀ m : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat],
      m ∈ IsLocalRing.maximalIdeal _ →
      j₂ m ∈ IsLocalRing.maximalIdeal _ := by
    intro m hm
    rw [IsLocalRing.mem_maximalIdeal] at hm ⊢
    intro hunit
    apply hm
    by_cases hm0 : (m : HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) = 0
    · exfalso
      have hz : j₂ m = 0 := Subtype.ext (by
        show (algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) _) (m : _) = 0
        rw [hm0, map_zero])
      rw [hz] at hunit
      exact not_isUnit_zero hunit
    · -- the inverse of the image is integral, so the inverse descends
      obtain ⟨u, hu⟩ := hunit
      have huv : ((u : (localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat)) :
          AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) =
          (algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) _)
            (m : HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) := by
        rw [hu]
        rfl
      have hmul : ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) _)
          (m : HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) *
          (((u⁻¹ : (localValuationSubring (K := ℚ)
            hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
            (localValuationSubring (K := ℚ)
              hq.toHeightOneSpectrumRingOfIntegersRat)) :
          AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) = 1 := by
        have h0 : ((u : (localValuationSubring (K := ℚ)
            hq.toHeightOneSpectrumRingOfIntegersRat)) *
            ((u⁻¹ : (localValuationSubring (K := ℚ)
              hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
              (localValuationSubring (K := ℚ)
                hq.toHeightOneSpectrumRingOfIntegersRat)) :
            (localValuationSubring (K := ℚ)
              hq.toHeightOneSpectrumRingOfIntegersRat)) = 1 := u.mul_inv
        calc ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) _)
              (m : HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) *
              (((u⁻¹ : (localValuationSubring (K := ℚ)
                hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
                (localValuationSubring (K := ℚ)
                  hq.toHeightOneSpectrumRingOfIntegersRat)) :
              AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))
            = ((((u : (localValuationSubring (K := ℚ)
                hq.toHeightOneSpectrumRingOfIntegersRat)) *
                ((u⁻¹ : (localValuationSubring (K := ℚ)
                  hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
                  (localValuationSubring (K := ℚ)
                    hq.toHeightOneSpectrumRingOfIntegersRat)) :
                (localValuationSubring (K := ℚ)
                  hq.toHeightOneSpectrumRingOfIntegersRat))) :
              AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) := by
              rw [← huv]
              rfl
          _ = (((1 : (localValuationSubring (K := ℚ)
                hq.toHeightOneSpectrumRingOfIntegersRat))) :
              AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat)) := by rw [h0]
          _ = 1 := rfl
      have hainv : (((u⁻¹ : (localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          (localValuationSubring (K := ℚ)
            hq.toHeightOneSpectrumRingOfIntegersRat)) :
          AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) =
          ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) _)
            ((m : HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹)) := by
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_right hmul
      -- integrality of the inverse, descended along the tower embedding
      have hint : IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
          ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))
            ((m : HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹)) := by
        rw [← hainv]
        exact ((u⁻¹ : (localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          (localValuationSubring (K := ℚ)
            hq.toHeightOneSpectrumRingOfIntegersRat)).2
      have hint2 : IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
          ((m : HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹) := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom
          (HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (FaithfulSMul.algebraMap_injective _ _)]
        exact hint
      have hmeminv : ((m : HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹) ∈
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat] :=
        mem_integer_of_mem_adicCompletionIntegers hq
          (hints.mem_of_integral hint2)
      exact ⟨⟨m, ⟨_, hmeminv⟩,
        Subtype.ext (mul_inv_cancel₀ hm0),
        Subtype.ext (inv_mul_cancel₀ hm0)⟩, rfl⟩
  -- the induced residue-field hom and separability of the reduction
  let φ := Ideal.Quotient.lift
    (IsLocalRing.maximalIdeal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat])
    ((IsLocalRing.residue (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat)).comp j₂)
    (fun m hm => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hj₂m m hm))
  have hfactor : (IsLocalRing.residue (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat)).comp j₂ =
      φ.comp (IsLocalRing.residue 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) := by
    apply RingHom.ext
    intro z
    rfl
  have hsepA : ((Q.map j₂).map (IsLocalRing.residue
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat))).Separable := by
    rw [Polynomial.map_map, hfactor, ← Polynomial.map_map]
    exact hQsep.map
  -- the image of `θ` is an integral root
  have haevalx : Polynomial.aeval (ι θ) (Q.map (algebraMap
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hθQ, map_zero]
  let j₀ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat] →+*
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    { toFun := fun z => ⟨(z : _),
        mem_adicCompletionIntegers_of_mem_integer hq z.2⟩
      map_one' := Subtype.ext (by push_cast; rfl)
      map_mul' := fun a b => Subtype.ext (by push_cast; rfl)
      map_zero' := Subtype.ext (by push_cast; rfl)
      map_add' := fun a b => Subtype.ext (by push_cast; rfl) }
  have hxA : (ι θ) ∈ localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat := by
    show IsIntegral (HeightOneSpectrum.adicCompletionIntegers ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) (ι θ)
    refine ⟨Q.map j₀, hQm.map _, ?_⟩
    ·
      rw [← Polynomial.eval_map, Polynomial.map_map]
      have hcomp : ((algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).comp j₀) =
          ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).comp
            (algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat]
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))) := by
        apply RingHom.ext
        intro z
        exact (IsScalarTower.algebraMap_apply
          (HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) _)
      rw [hcomp, ← Polynomial.map_map, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      exact haevalx
  -- root equation over `A`
  have hroot : (Q.map j₂).eval (⟨ι θ, hxA⟩ : localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat) = 0 := by
    apply Subtype.ext
    have h1 : ((((Q.map j₂).eval (⟨ι θ, hxA⟩ : localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)) :
        localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat) :
        AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) =
        ((Q.map j₂).map (localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat).subtype).eval (ι θ) := by
      conv_rhs => rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply (p := Q.map j₂)
        ((localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat).subtype)
        (⟨ι θ, hxA⟩ : localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat)).symm
    show ((((Q.map j₂).eval (⟨ι θ, hxA⟩ : localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat)) :
        localValuationSubring (K := ℚ)
          hq.toHeightOneSpectrumRingOfIntegersRat) : AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) =
      (((0 : localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)) : AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
    rw [h1, Polynomial.map_map]
    have hcomp2 : ((localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat).subtype.comp j₂) =
        ((algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).comp
          (algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
            (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) := by
      apply RingHom.ext
      intro z
      rfl
    rw [hcomp2, ← Polynomial.map_map, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact haevalx
  -- coefficients come from the base field
  have hcoeff : ∀ i, (((Q.map j₂).coeff i : localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat) :
      AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ∈
      Set.range (algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) := by
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨((Q.coeff i : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]) :
      HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat), rfl⟩
  -- the master root-fixing lemma fixes `ι θ`
  have hθfix := (localValuationSubring (K := ℚ)
    hq.toHeightOneSpectrumRingOfIntegersRat).inertia_fixes_root_of_separable_residue
    σ hσ (Q.map j₂) hcoeff hsepA hxA hroot
  -- `θ` generates: the embedding is fixed pointwise
  have hle : Algebra.adjoin (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ({θ} : Set L) ≤
      AlgHom.equalizer
        (((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom.comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hθfix
  rw [hθtop] at hle
  exact hle (Algebra.mem_top)

open IsDedekindDomain ValuativeRel WithZero WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Tate parameter is a unit times a `p`-th power when
`p ∣ v_q(j)`** (the step-(d) witness): for the completed base change
with split multiplicative reduction, if `p` divides the `q`-adic
valuation of `j(E)`, there is `w ∈ ℚ_qˆˣ` with `q_E · w⁻ᵖ` a UNIT of
the completed integers. The witness is the image of the rational
`q^(−m)` with `v_q(j) = p·m`: then `j · (q^(−m))ᵖ` has `padicValRat`
zero, hence `v_q`-adic valuation `1` (the reduced-fraction dictionary),
and `|q_E| = |j|⁻¹` (`valuation_tateParameter_eq`) makes the recentred
parameter a unit. -/
theorem exists_unit_qUnit_mul_inv_pow_isUnit {q : ℕ} (hq : q.Prime)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic] {p : ℕ}
    [hsplit : X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]]
    {jQ : ℚ} (hXj : X.j = algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) jQ)
    (hj : (p : ℤ) ∣ padicValRat q jQ) :
    ∃ (w : (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)ˣ)
      (hmem : ((X.qUnit * w⁻¹ ^ p :
          (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) ∈
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat),
      IsUnit (⟨_, hmem⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, hm⟩ := hj
  -- the `j`-invariant is nonzero (its valuation upstairs exceeds `1`)
  have hj0 : jQ ≠ 0 := by
    intro h0
    have h1 := WeierstrassCurve.one_lt_valuation_j X
    rw [hXj, h0, map_zero, map_zero] at h1
    exact absurd h1 (not_lt.mpr zero_le)
  have hq0 : ((q : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  -- the rational recentring unit `r = q^(−m)`
  set r : ℚˣ := (Units.mk0 (q : ℚ) hq0) ^ (-m) with hr
  have hrval : ((r : ℚˣ) : ℚ) = (q : ℚ) ^ (-m : ℤ) := by
    rw [hr, Units.val_zpow_eq_zpow_val]
    rfl
  have hr0 : ((r : ℚˣ) : ℚ) ≠ 0 := Units.ne_zero r
  -- the recentred rational has `padicValRat` zero
  have hy0 : jQ * ((r : ℚˣ) : ℚ) ^ p ≠ 0 :=
    mul_ne_zero hj0 (pow_ne_zero _ hr0)
  have hval0 : padicValRat q (jQ * ((r : ℚˣ) : ℚ) ^ p) = 0 := by
    rw [padicValRat.mul hj0 (pow_ne_zero _ hr0), padicValRat.pow _,
      hrval, padicValRat.zpow, padicValRat.self hq.one_lt, mul_one, hm]
    ring
  -- hence `v_q`-adic valuation `1`, transported to the completion
  have hQQ : hq.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ
      (jQ * ((r : ℚˣ) : ℚ) ^ p) = 1 :=
    valuation_eq_one_of_padicValRat_eq_zero hq hy0 hval0
  have hKeq : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰) :=
    ValuativeRel.isEquiv _ _
  have hy1 : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        (jQ * ((r : ℚˣ) : ℚ) ^ p)) = 1 :=
    (Valuation.isEquiv_iff_val_eq_one.mp hKeq).mpr
      (by rw [valued_algebraMap_adicCompletion_eq hq]; exact hQQ)
  -- expand into the two factors
  have hy2 : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) jQ) *
      (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
        ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) ((r : ℚˣ) : ℚ))) ^ p
      = 1 := by
    rw [← hy1, map_mul, map_pow, map_mul, map_pow]
  -- the completed recentring unit
  set w : (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)ˣ :=
    Units.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)).toMonoidHom r
  -- the recentred Tate parameter has canonical valuation `1`
  have hcoe : ((X.qUnit * w⁻¹ ^ p :
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) =
      WeierstrassCurve.tateParameter
        X.j *
      (((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) ((r : ℚˣ) : ℚ))⁻¹) ^ p := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    rfl
  have hq1 : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      ((X.qUnit * w⁻¹ ^ p :
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
    rw [hcoe, map_mul, map_pow, map_inv₀,
      WeierstrassCurve.valuation_tateParameter_eq
        (WeierstrassCurve.one_lt_valuation_j X),
      hXj, inv_pow, ← mul_inv, inv_eq_one]
    exact hy2
  -- transfer to `Valued.v` and conclude with the unit criterion
  have hVc : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰)
      ((X.qUnit * w⁻¹ ^ p :
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) = 1 :=
    (Valuation.isEquiv_iff_val_eq_one.mp hKeq).mp hq1
  have hmem : ((X.qUnit * w⁻¹ ^ p :
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) ∈
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hVc
  have hints : (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) ℤᵐ⁰).Integers
      (HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    Valuation.valuationSubring.integers _
  exact ⟨w, hmem, hints.isUnit_iff_valuation_eq_one.mpr hVc⟩

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The tower `ℚ → ℚ_qˆ → Ω` algebra structure on the local algebraic
closure, used CONSISTENTLY throughout the transport lemmas so that the
two spellings of the `Ω`-stage base change — `E⁄Ω` and `(E⁄ℚ_qˆ)⁄Ω` —
are definitionally equal curves. (Not an instance: it would clash with
the ambient `ℚ`-algebra structure; each statement installs it with
`letI`.) -/
@[reducible] noncomputable def algebraRatAlgClosureAdic
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Algebra ℚ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
  ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))).comp
    (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))).toAlgebra

/-- A classical decidable-equality instance on the local algebraic
closures, mirroring the global one in `Torsion.lean` (needed for the
group law on `(E⁄Ω)`-points). -/
noncomputable instance instDecidableEqAlgClosureAdicCompletionRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    DecidableEq (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) :=
  Classical.typeDecidableEq _

/-- **The chosen embedding of algebraic closures, as a `ℚ`-algebra
homomorphism** (PROVEN — step (C3) packaging): `AlgebraicClosure.map`
along `ℚ → ℚ_qˆ` is `ℚ`-linear, the base square closing by uniqueness
of ring homomorphisms out of `ℚ`. -/
noncomputable def algClosureEmbeddingRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    letI := algebraRatAlgClosureAdic v
    ((AlgebraicClosure ℚ) →ₐ[ℚ]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) :=
  letI := algebraRatAlgClosureAdic v
  { AlgebraicClosure.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ v)) with
    commutes' := fun r => by
      have h1 := AlgebraicClosure.map_algebraMap
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)) r
      exact h1 }

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The action of a local Galois element on the local algebraic
closure, packaged as a `ℚ`-algebra homomorphism over the TOWER
structure (`algebraRatAlgClosureAdic`): `σ` is `ℚ_qˆ`-linear, hence
fixes the tower images of `ℚ`. -/
noncomputable def algClosureSigmaRat
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ v)) :
    letI := algebraRatAlgClosureAdic v
    ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) →ₐ[ℚ]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))) :=
  letI := algebraRatAlgClosureAdic v
  { ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ v]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        v))).toAlgHom.toRingHom) with
    commutes' := fun r =>
      (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ v]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          v))).commutes (algebraMap ℚ
            (HeightOneSpectrum.adicCompletion ℚ v) r) }

open IsDedekindDomain WeierstrassCurve in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Equivariance of the point transport** (step (C3)): transporting a
`ℚ̄`-point along the chosen embedding and then acting by `σ` equals
acting first by the mapped global element; `Point.map_map` on both
sides reduces this to `Field.absoluteGaloisGroup.lift_map`. All
`Ω`-stage structure is over the TOWER `ℚ`-algebra
(`algebraRatAlgClosureAdic`). -/
theorem point_map_algClosureEmbeddingRat_comm
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ v))
    (P : ((E)⁄(AlgebraicClosure ℚ)).Point) :
    letI := algebraRatAlgClosureAdic v
    WeierstrassCurve.Affine.Point.map (W' := E) (algClosureEmbeddingRat v)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (HeightOneSpectrum.adicCompletion ℚ v))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) =
    WeierstrassCurve.Affine.Point.map (W' := E) (algClosureSigmaRat v σ)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat v) P) := by
  letI := algebraRatAlgClosureAdic v
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map]
  have hhomeq : (algClosureEmbeddingRat v).comp
      (((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ v))) σ :
        AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom =
      (algClosureSigmaRat v σ).comp (algClosureEmbeddingRat v) := by
    apply AlgHom.ext
    intro x
    exact Field.absoluteGaloisGroup.lift_map
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)) σ x
  rw [hhomeq]

open IsDedekindDomain WeierstrassCurve ValuativeRel in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Pointwise unipotence in the split case** (step (C5),
consuming the Tate-uniformization leaf): if the completed base change
has SPLIT multiplicative reduction, every element of the local inertia
group acts unipotently on the `p`-torsion of `E(ℚ̄)`. Assembly: the
uniformization witness (`exists_tateEquivSepClosure` at
`k = adicCompletion ℚ v_q`, gateway instances) feeds the PROVEN
`tate_inertia_unipotent` at the local valuation subring ((C1) supplies
decomposition/inertia membership, (C2) the residue characteristic);
the resulting equation over the local closure pulls back to `E(ℚ̄)`
along the equivariant embedding ((C3)) by `Point.map` injectivity. -/
theorem torsion_unipotent_of_split_multiplicative_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [hsplit : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]] :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (WeierstrassCurve.Affine.Point.map
            (((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P +
        P = 0 := by
  classical
  letI := algebraRatAlgClosureAdic hq.toHeightOneSpectrumRingOfIntegersRat
  intro σ hσ P hP
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
  -- transport the point along the chosen embedding
  have hP' : WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P ∈
      AddSubgroup.torsionBy
        ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P = 0
    rw [← map_zsmul, h1, map_zero]
  -- the decomposition-subgroup element carried by `σ`
  let σd : (localValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    ⟨(σ : _ ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] _),
      mem_decompositionSubgroup_localValuationSubring _ _⟩
  -- the local unipotence at the transported point
  have hloc := WeierstrassCurve.tate_inertia_unipotent
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) e he
    (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
    (Fact.out : p.Prime).ne_zero
    (natCast_residueField_localValuationSubring_ne_zero
      (Fact.out : p.Prime) hq (fun h => hqp h.symm))
    σd
    (mem_inertiaSubgroup_localValuationSubring _ _ hσ)
    (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P)
    hP'
  -- pull the equation back along the injective equivariant embedding
  apply WeierstrassCurve.Affine.Point.map_injective
    (f := algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat)
  simp only [map_sub, map_add, map_zero]
  simp only [point_map_algClosureEmbeddingRat_comm]
  have hbb : ∀ Q : ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point,
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureSigmaRat hq.toHeightOneSpectrumRingOfIntegersRat σ) Q =
      (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (((σd : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toAlgHom))
          (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).Point from Q)) := by
    intro Q
    cases Q with
    | zero => rfl
    | some x y h => rfl
  simp only [hbb]
  exact hloc

open IsDedekindDomain WeierstrassCurve ValuativeRel in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Pointwise inertia-TRIVIALITY in the split case** (the step-(C5)
analogue for `p ∣ v_q(j)`, consuming the Tate-uniformization leaf): if
the completed base change has SPLIT multiplicative reduction and `p`
divides the `q`-adic valuation of `j(E)`, every element of the local
inertia group FIXES the `p`-torsion of `E(ℚ̄)` pointwise. Assembly: the
uniformization witness feeds `tate_inertia_trivial` at the local
valuation subring with the step-(d) witness
(`exists_unit_qUnit_mul_inv_pow_isUnit` transported by the extracted
unit-residue lemmas); the resulting fixed-point equation over the local
closure pulls back to `E(ℚ̄)` along the equivariant embedding. -/
theorem torsion_trivial_of_split_multiplicative_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [hsplit : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]]
    (hj : (p : ℤ) ∣ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P := by
  classical
  letI := algebraRatAlgClosureAdic hq.toHeightOneSpectrumRingOfIntegersRat
  intro σ hσ P hP
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
  -- transport the point along the chosen embedding
  have hP' : WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P ∈
      AddSubgroup.torsionBy
        ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P = 0
    rw [← map_zsmul, h1, map_zero]
  -- the decomposition-subgroup element carried by `σ`
  let σd : (localValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    ⟨(σ : _ ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] _),
      mem_decompositionSubgroup_localValuationSubring _ _⟩
  -- the step-(d) witness and its transport to the local valuation subring
  obtain ⟨w, hmemw, hunitw⟩ :=
    exists_unit_qUnit_mul_inv_pow_isUnit hq
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) (p := p)
      (WeierstrassCurve.map_j _ _) hj
  have hcA := algebraMap_mem_localValuationSubring_of_integer hq _ hmemw
  have hcres := residue_localValuationSubring_ne_zero_of_isUnit hq _ hmemw
    hunitw hcA
  -- the local triviality at the transported point
  have hloc := WeierstrassCurve.tate_inertia_trivial
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) e he
    (localValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
    (Fact.out : p.Prime).ne_zero
    (natCast_residueField_localValuationSubring_ne_zero
      (Fact.out : p.Prime) hq (fun h => hqp h.symm))
    σd
    (mem_inertiaSubgroup_localValuationSubring _ _ hσ)
    w hcA hcres
    (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P)
    hP'
  -- pull the equation back along the injective equivariant embedding
  apply WeierstrassCurve.Affine.Point.map_injective
    (f := algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat)
  simp only [point_map_algClosureEmbeddingRat_comm]
  have hbb : ∀ Q : ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point,
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureSigmaRat hq.toHeightOneSpectrumRingOfIntegersRat σ) Q =
      (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (((σd : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toAlgHom))
          (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).Point from Q)) := by
    intro Q
    cases Q with
    | zero => rfl
    | some x y h => rfl
  simp only [hbb]
  exact hloc

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Local inertia-unipotence in the nonsplit case** (the LOCAL
twist-transfer content, isolated from the `ℚ̄`-pullback glue
which is proven below): a local curve over `ℚ_qˆ` with NONSPLIT
multiplicative reduction still has unipotent inertia on its
`p`-torsion over the local algebraic closure. Content: the unramified
quadratic twist (`exists_quadraticTwist_hasSplitMultiplicativeReduction`)
has split reduction, so its minimal model satisfies
`tate_inertia_unipotent` over any uniformization witness; the twist
isomorphism over the UNRAMIFIED quadratic extension `L` is
inertia-fixed (`quadraticTwistPointEquiv_galois` with trivial quadratic
character), so the unipotence equation transports along the equivariant
point equivalence and the minimal-model variable change. -/
theorem WeierstrassCurve.tate_inertia_unipotent_of_nonsplit {q : ℕ}
    (hq : q.Prime)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    [X.IsElliptic]
    [X.HasMultiplicativeReduction 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]]
    (hnonsplit : ¬ X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat])
    {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0)
    (σ : (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)
    (hP : P ∈ AddSubgroup.torsionBy
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := X)
        ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := X)
          ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P) -
      WeierstrassCurve.Affine.Point.map (W' := X)
        ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P -
      WeierstrassCurve.Affine.Point.map (W' := X)
        ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P + P = 0 := by
  classical
  obtain ⟨L, _, _, _, _, hsplit', θL, Q, hQm, hθtop, hθQ, hQsep⟩ :=
    WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction
      (E := X) (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) hnonsplit
  set Tw : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := X.quadraticTwist L
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := Tw.minimal
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]
  set Cb : WeierstrassCurve.VariableChange (AlgebraicClosure
    (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((Tw.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]).choose.baseChange
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) with hCbdef
  set σΩ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) with hσΩdef
  haveI hMtsplit : Mt.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] := hsplit'
  haveI hTwell : Tw.IsElliptic :=
    inferInstanceAs ((X.quadraticTwist L).IsElliptic)
  haveI hMtell : Mt.IsElliptic :=
    inferInstanceAs (((Tw.exists_isMinimal
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).IsElliptic)
  haveI hTwΩell : (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).IsElliptic :=
    inferInstanceAs ((Tw.map (algebraMap (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic)
  letI algLΩ : Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      (R := HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) (S := L)).toAlgebra
  haveI : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        (R := HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (S := L)).commutes x).symm)
  have hfixL : ∀ y : L,
      σΩ (algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) y) =
      algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) y :=
    fun y => inertia_fixes_algHom_of_unramified_gen hq θL hθtop Q hQm hθQ hQsep
      σ hσ (IsAlgClosed.lift) y
  have hEq : (Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) =
      Cb • (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :=
    (WeierstrassCurve.baseChange_smul_baseChange _ _ _).symm
  let Φ : ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point) ≃+
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).Point) :=
    ((WeierstrassCurve.Affine.Point.equivOfEq hEq).trans
      (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)).trans
      (X.quadraticTwistPointEquiv L (AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
  have hσu : σΩ.toAlgHom ((Cb.u : AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) =
      (Cb.u : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact σΩ.toAlgHom.commutes _
  have hσr : σΩ.toAlgHom Cb.r = Cb.r := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hσs : σΩ.toAlgHom Cb.s = Cb.s := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hσt : σΩ.toAlgHom Cb.t = Cb.t := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hcomm : ∀ Qt : ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point),
      Φ (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt) =
      WeierstrassCurve.Affine.Point.map (W' := X) σΩ.toAlgHom (Φ Qt) := by
    intro Qt
    have h12 : (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
          (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt)) =
        WeierstrassCurve.Affine.Point.map (W' := Tw) σΩ.toAlgHom
          ((WeierstrassCurve.Affine.Point.equivVariableChange
            (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
            ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt)) := by
      cases Qt with
      | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
      | some x y hxy =>
        rw [WeierstrassCurve.Affine.Point.map_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.map_some]
        refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
        · simp only [map_add, map_mul, map_pow, hσu, hσr]
        · simp only [map_add, map_mul, map_pow, hσu, hσs, hσt]
    show (X.quadraticTwistPointEquiv L (AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
        ((WeierstrassCurve.Affine.Point.equivVariableChange
          (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
          ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
            (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt))) = _
    rw [h12]
    have hχ : quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) L
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ = 1 :=
      (quadraticCharacter_eq_one_iff _ _ _ _).mpr hfixL
    have h3 := X.quadraticTwistPointEquiv_galois L
      (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ
      ((WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt))
    rw [hχ, Units.val_one, one_zsmul] at h3
    exact h3
  have hPmtor : Φ.symm P ∈ AddSubgroup.torsionBy _ ((p : ℕ) : ℤ) := by
    show ((p : ℕ) : ℤ) • Φ.symm P = 0
    rw [← map_zsmul Φ.symm, (show ((p : ℕ) : ℤ) • P = 0 from hP), map_zero]
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := Mt)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
  have hloc := WeierstrassCurve.tate_inertia_unipotent (E := Mt)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) e he
    (localValuationSubring (K := ℚ) hq.toHeightOneSpectrumRingOfIntegersRat)
    hp hchar σ hσ (Φ.symm P) hPmtor
  have hφ := congrArg Φ hloc
  rw [map_add, map_sub, map_sub, map_zero] at hφ
  rw [← hσΩdef] at hφ
  simp only [hcomm] at hφ
  rw [Φ.apply_symm_apply] at hφ
  exact hφ


open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Local inertia-triviality in the nonsplit case** (the LOCAL
twist-transfer content of the triviality statement, isolated from
the `ℚ̄`-pullback glue): a local curve over `ℚ_qˆ` with NONSPLIT
multiplicative reduction whose `j`-invariant is rational with `q`-adic
valuation divisible by `p` has inertia acting trivially on its
`p`-torsion over the local algebraic closure. Content: as the
unipotent analogue, via the unramified quadratic twist and
`tate_inertia_trivial` (the twist has the SAME `j`-invariant, so the
step-(d) witness applies to its minimal model). -/
theorem WeierstrassCurve.tate_inertia_trivial_of_nonsplit {q : ℕ}
    (hq : q.Prime)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
    [X.IsElliptic]
    [X.HasMultiplicativeReduction 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]]
    (hnonsplit : ¬ X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat])
    {p : ℕ} (hp : p ≠ 0)
    {jQ : ℚ} (hXj : X.j = algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) jQ)
    (hj : (p : ℤ) ∣ padicValRat q jQ)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField
      (localValuationSubring (K := ℚ)
        hq.toHeightOneSpectrumRingOfIntegersRat)) ≠ 0)
    (σ : (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (hσ : σ ∈ (localValuationSubring (K := ℚ)
      hq.toHeightOneSpectrumRingOfIntegersRat).inertiaSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
    (P : ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))).Point)
    (hP : P ∈ AddSubgroup.torsionBy
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := X)
      ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))).toAlgHom P = P := by
  classical
  obtain ⟨L, _, _, _, _, hsplit', θL, Q, hQm, hθtop, hθQ, hQsep⟩ :=
    WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction
      (E := X) (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) hnonsplit
  set Tw : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := X.quadraticTwist L
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := Tw.minimal
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]
  set Cb : WeierstrassCurve.VariableChange (AlgebraicClosure
    (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    ((Tw.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat]).choose.baseChange
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) with hCbdef
  set σΩ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
      ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) with hσΩdef
  haveI hMtsplit : Mt.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] := hsplit'
  haveI hTwell : Tw.IsElliptic :=
    inferInstanceAs ((X.quadraticTwist L).IsElliptic)
  haveI hMtell : Mt.IsElliptic :=
    inferInstanceAs (((Tw.exists_isMinimal
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).IsElliptic)
  haveI hTwΩell : (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).IsElliptic :=
    inferInstanceAs ((Tw.map (algebraMap (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)))).IsElliptic)
  -- the minimal twist has the SAME rational `j`-image
  have hMtj : Mt.j = algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) jQ := by
    have h1 : Mt.j = ((Tw.exists_isMinimal
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).j := rfl
    have h2 : Tw.j = (X.quadraticTwist L).j := rfl
    rw [h1, WeierstrassCurve.variableChange_j, h2,
      WeierstrassCurve.j_quadraticTwist, hXj]
  letI algLΩ : Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    (IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
      (R := HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) (S := L)).toAlgebra
  haveI : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
        (R := HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)
        (S := L)).commutes x).symm)
  have hfixL : ∀ y : L,
      σΩ (algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) y) =
      algebraMap L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) y :=
    fun y => inertia_fixes_algHom_of_unramified_gen hq θL hθtop Q hQm hθQ hQsep
      σ hσ (IsAlgClosed.lift) y
  have hEq : (Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))) =
      Cb • (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) :=
    (WeierstrassCurve.baseChange_smul_baseChange _ _ _).symm
  let Φ : ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point) ≃+
      ((X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).Point) :=
    ((WeierstrassCurve.Affine.Point.equivOfEq hEq).trans
      (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)).trans
      (X.quadraticTwistPointEquiv L (AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
  have hσu : σΩ.toAlgHom ((Cb.u : AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) =
      (Cb.u : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact σΩ.toAlgHom.commutes _
  have hσr : σΩ.toAlgHom Cb.r = Cb.r := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hσs : σΩ.toAlgHom Cb.s = Cb.s := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hσt : σΩ.toAlgHom Cb.t = Cb.t := by
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact σΩ.toAlgHom.commutes _
  have hcomm : ∀ Qt : ((Mt⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point),
      Φ (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt) =
      WeierstrassCurve.Affine.Point.map (W' := X) σΩ.toAlgHom (Φ Qt) := by
    intro Qt
    have h12 : (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
          (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt)) =
        WeierstrassCurve.Affine.Point.map (W' := Tw) σΩ.toAlgHom
          ((WeierstrassCurve.Affine.Point.equivVariableChange
            (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
            ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt)) := by
      cases Qt with
      | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
      | some x y hxy =>
        rw [WeierstrassCurve.Affine.Point.map_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.map_some]
        refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
        · simp only [map_add, map_mul, map_pow, hσu, hσr]
        · simp only [map_add, map_mul, map_pow, hσu, hσs, hσt]
    show (X.quadraticTwistPointEquiv L (AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)))
        ((WeierstrassCurve.Affine.Point.equivVariableChange
          (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
          ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
            (WeierstrassCurve.Affine.Point.map (W' := Mt) σΩ.toAlgHom Qt))) = _
    rw [h12]
    have hχ : quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) L
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ = 1 :=
      (quadraticCharacter_eq_one_iff _ _ _ _).mpr hfixL
    have h3 := X.quadraticTwistPointEquiv_galois L
      (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) σΩ
      ((WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt))
    rw [hχ, Units.val_one, one_zsmul] at h3
    exact h3
  -- the step-(d) witness for the minimal twist and its transport
  obtain ⟨w, hmemw, hunitw⟩ :=
    exists_unit_qUnit_mul_inv_pow_isUnit hq Mt (p := p) hMtj hj
  have hcA := algebraMap_mem_localValuationSubring_of_integer hq _ hmemw
  have hcres := residue_localValuationSubring_ne_zero_of_isUnit hq _ hmemw
    hunitw hcA
  have hPmtor : Φ.symm P ∈ AddSubgroup.torsionBy _ ((p : ℕ) : ℤ) := by
    show ((p : ℕ) : ℤ) • Φ.symm P = 0
    rw [← map_zsmul Φ.symm, (show ((p : ℕ) : ℤ) • P = 0 from hP), map_zero]
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)
    (E := Mt)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))
  have hloc := WeierstrassCurve.tate_inertia_trivial (E := Mt)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)) e he
    (localValuationSubring (K := ℚ) hq.toHeightOneSpectrumRingOfIntegersRat)
    hp hchar σ hσ w hcA hcres (Φ.symm P) hPmtor
  have hφ := congrArg Φ hloc
  rw [← hσΩdef] at hφ
  rw [hcomm, Φ.apply_symm_apply] at hφ
  exact hφ

open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Pointwise inertia-triviality, nonsplit case** (assembled from the
LOCAL nonsplit node `tate_inertia_trivial_of_nonsplit` by the same
`ℚ̄`-pullback glue as the split case; the `j`-hypothesis feeds the
local node through `map_j`). -/
theorem WeierstrassCurve.torsion_trivial_of_nonsplit_multiplicative_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j)
    (hnonsplit : ¬ (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P := by
  classical
  letI := algebraRatAlgClosureAdic hq.toHeightOneSpectrumRingOfIntegersRat
  haveI := hasMultiplicativeReduction_adicCompletion hq E
  intro σ hσ P hP
  have hP' : WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P ∈
      AddSubgroup.torsionBy
        ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P = 0
    rw [← map_zsmul, h1, map_zero]
  let σd : (localValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    ⟨(σ : _ ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] _),
      mem_decompositionSubgroup_localValuationSubring _ _⟩
  have hloc := WeierstrassCurve.tate_inertia_trivial_of_nonsplit hq
    (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    hnonsplit
    (Fact.out : p.Prime).ne_zero
    (WeierstrassCurve.map_j _ _)
    hj
    (natCast_residueField_localValuationSubring_ne_zero
      (Fact.out : p.Prime) hq (fun h => hqp h.symm))
    σd
    (mem_inertiaSubgroup_localValuationSubring _ _ hσ)
    (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P)
    hP'
  apply WeierstrassCurve.Affine.Point.map_injective
    (f := algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat)
  simp only [point_map_algClosureEmbeddingRat_comm]
  have hbb : ∀ Q : ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point,
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureSigmaRat hq.toHeightOneSpectrumRingOfIntegersRat σ) Q =
      (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (((σd : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toAlgHom))
          (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).Point from Q)) := by
    intro Q
    cases Q with
    | zero => rfl
    | some x y h => rfl
  simp only [hbb]
  exact hloc

open scoped WeierstrassCurve.Affine in
open ValuativeRel IsDedekindDomain in
/-- **Pointwise inertia-triviality on torsion at multiplicative primes
with `p ∣ v_q(j)`** (assembled from the split case and the nonsplit
leaf by the split/nonsplit case split, exactly as the unipotence
statement): for an elliptic curve over `ℚ` with multiplicative
reduction at `q ≠ p` whose `j`-invariant has `q`-adic valuation
divisible by `p`, the image of every local inertia element FIXES the
`p`-torsion pointwise. This is the local input to the unramifiedness
glue `isUnramifiedAt_of_hasMultiplicativeReduction`. -/
theorem WeierstrassCurve.torsion_trivial_of_multiplicative_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P := by
  classical
  haveI := hasMultiplicativeReduction_adicCompletion hq E
  by_cases hsp : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
  · haveI := hsp
    exact torsion_trivial_of_split_multiplicative_adic E hq hqp hj
  · exact WeierstrassCurve.torsion_trivial_of_nonsplit_multiplicative_adic
      E hq hqp hj hsp


open ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Pointwise inertia-unipotence, nonsplit case** (assembled from the
LOCAL nonsplit node `tate_inertia_unipotent_of_nonsplit` by the same
`ℚ̄`-pullback glue as the split case: transport the point along the
equivariant embedding, apply the local statement at the decomposition
element, and pull back by `Point.map` injectivity). -/
theorem WeierstrassCurve.torsion_unipotent_of_nonsplit_multiplicative_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hnonsplit : ¬ (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]) :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (WeierstrassCurve.Affine.Point.map
            (((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P +
        P = 0 := by
  classical
  letI := algebraRatAlgClosureAdic hq.toHeightOneSpectrumRingOfIntegersRat
  haveI := hasMultiplicativeReduction_adicCompletion hq E
  intro σ hσ P hP
  have hP' : WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P ∈
      AddSubgroup.torsionBy
        ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    show ((p : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.map (W' := E)
      (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P = 0
    rw [← map_zsmul, h1, map_zero]
  let σd : (localValuationSubring
      hq.toHeightOneSpectrumRingOfIntegersRat).decompositionSubgroup
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    ⟨(σ : _ ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat] _),
      mem_decompositionSubgroup_localValuationSubring _ _⟩
  have hloc := WeierstrassCurve.tate_inertia_unipotent_of_nonsplit hq
    (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))
    hnonsplit
    (Fact.out : p.Prime).ne_zero
    (natCast_residueField_localValuationSubring_ne_zero
      (Fact.out : p.Prime) hq (fun h => hqp h.symm))
    σd
    (mem_inertiaSubgroup_localValuationSubring _ _ hσ)
    (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat) P)
    hP'
  apply WeierstrassCurve.Affine.Point.map_injective
    (f := algClosureEmbeddingRat hq.toHeightOneSpectrumRingOfIntegersRat)
  simp only [map_sub, map_add, map_zero]
  simp only [point_map_algClosureEmbeddingRat_comm]
  have hbb : ∀ Q : ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).Point,
      WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureSigmaRat hq.toHeightOneSpectrumRingOfIntegersRat σ) Q =
      (show ((E)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).Point from
        WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
          (((σd : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))
              ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toAlgHom))
          (show ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
              (HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))).Point from Q)) := by
    intro Q
    cases Q with
    | zero => rfl
    | some x y h => rfl
  simp only [hbb]
  exact hloc

open scoped WeierstrassCurve.Affine in
open ValuativeRel in
/-- **Pointwise inertia-unipotence on torsion at multiplicative primes**
(sorry node — the TATE-THEORETIC content, WITHOUT the `p ∣ v_q(j)`
hypothesis and with the conclusion weakened to unipotence; `q = 2` is
allowed — the unramified quadratic twist to split reduction exists at
`2` as well; quantified over the LOCAL inertia group and its image in
`Γ ℚ`, the form every consumer actually needs, avoiding the
decomposition-surjectivity question of the valuation-subring form):
for an elliptic curve over `ℚ` with multiplicative reduction at
`q ≠ p`, the image of every local inertia element acts unipotently on
the `p`-torsion: `σ(σP) − σP − σP + P = 0`. Content: Tate's uniformization presents
`E[p]` inside `ℚ̄_qˣ/q_Eᶻ` as generated by `μ_p` (fixed by inertia, as
`q ≠ p`) and a `p`-th root of the Tate parameter, moved by inertia at
most by a `p`-th root of unity — so `(σ − 1)` maps `E[p]` into the
`μ_p`-part and kills it. -/
theorem WeierstrassCurve.torsion_unipotent_of_multiplicative_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (WeierstrassCurve.Affine.Point.map
            (((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
              AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P -
        WeierstrassCurve.Affine.Point.map
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))) σ :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P +
        P = 0 := by
  classical
  haveI := hasMultiplicativeReduction_adicCompletion hq E
  by_cases hsp : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat]
  · haveI := hsp
    exact torsion_unipotent_of_split_multiplicative_adic E hq hqp
  · exact WeierstrassCurve.torsion_unipotent_of_nonsplit_multiplicative_adic
      E hq hqp hsp

open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local-global glue for the Tate curve at multiplicative primes**
(assembled from the pointwise triviality above, by the SAME transport
as the good-reduction case): an elliptic curve over `ℚ` with
multiplicative reduction at the place `q ≠ p` whose `j`-invariant
has `q`-adic valuation divisible by `p` has unramified mod-`p` torsion
representation at `q`. -/
theorem WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (_hq2 : q ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j) :
    (E.galoisRep p hp).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  constructor
  intro σ hσ
  have htriv := WeierstrassCurve.torsion_trivial_of_multiplicative_reduction
    E hq hqp hj
  show ((E.galoisRep p hp).toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  have hP : (P : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) ∈
      AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point
        ((p : ℕ) : ℤ) := by
    have h1 := P.2
    rw [Submodule.mem_torsionBy_iff] at h1
    show ((p : ℕ) : ℤ) • (P : ((E.map (algebraMap ℚ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) = 0
    exact_mod_cast h1
  have h2 := htriv σ hσ P.1 hP
  convert h2 using 2
  · exact congrArg (fun f : ℚ →+* (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) =>
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (((Field.absoluteGaloisGroup.map f) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
        ((show (E⁄(AlgebraicClosure ℚ)).Point from P.1))))
      (Subsingleton.elim _ _)
  · rfl

open TensorProduct in
open scoped WeierstrassCurve.Affine in
/-- **The DVR finite-flat torsion package** — the `∃`-shape shared by
the vendored good-reduction leaf `torsion_flat_of_good_reduction`, the
peu-ramifiée node below, and both sides of its local/descent
decomposition: a commutative Hopf algebra `H` over `R`, finite flat as
an `R`-module, with étale generic fibre `K ⊗[R] H`, whose group of
`Ksep`-points (under convolution) is `Gal(Ksep/K)`-equivariantly
isomorphic to the `n`-torsion of `E(Ksep)`. Naming the shape once as a
`Prop` lets the peu-ramifiée decomposition below quote it at TWO
different DVRs (the completed integers `𝒪[adicCompletion ℚ v_p]` for
the local Tate/Kummer content, the localization `ℤ_(p)` for the
descended global package) without restating the package. -/
def WeierstrassCurve.TorsionFlatPackage
    (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]
    (E : WeierstrassCurve K) (n : ℕ)
    (Ksep : Type*) [Field Ksep] [Algebra K Ksep] [DecidableEq Ksep] : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H)
    (_ : Module.Finite R H) (_ : Module.Flat R H)
    (_ : Algebra.Etale K (K ⊗[R] H))
    (f : Additive (WithConv ((K ⊗[R] H) →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (n : ℤ)),
    ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : (K ⊗[R] H) →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
        (E⁄Ksep).Point) =
        WeierstrassCurve.Affine.Point.map σ.toAlgHom
          (f (Additive.ofMul (WithConv.toConv φ)))

/-! #### The twisted constant group scheme of a finite Galois module

For a finite Galois extension `L/K` inside `Ω` and a finite abelian
group `A` with an action `ρ' : Gal(L/K) →* End A`, the twisted constant
group scheme attached to `ρ'` has Hopf algebra of functions the
`K`-algebra of `Gal(L/K)`-equivariant functions `A → L`. The DATA
(subalgebra, pullback structure maps, comultiplication through the
tensor-comparison isomorphism, counit through the fixed-field
identification, antipode) is constructed here; the AXIOMS and the
points computation are the sorried `galDesc*` leaves. -/

section GaloisDescentHopf

open TensorProduct

variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]
variable (L : IntermediateField K Ω)

/-- The `K`-subalgebra of `Gal(L/K)`-equivariant functions `B → L`, for
an arbitrary (set-level) action `act` of the Galois group on `B`:
`h (act g b) = g (h b)`. -/
def galDescSubalgebra (B : Type) (act : (↥L ≃ₐ[K] ↥L) → B → B) :
    Subalgebra K (B → ↥L) where
  carrier := {h | ∀ (g : ↥L ≃ₐ[K] ↥L) (b : B), h (act g b) = g (h b)}
  mul_mem' := fun {x y} hx hy g b => by
    simp only [Pi.mul_apply, map_mul, hx g b, hy g b]
  one_mem' := fun g b => by simp only [Pi.one_apply, map_one]
  add_mem' := fun {x y} hx hy g b => by
    simp only [Pi.add_apply, map_add, hx g b, hy g b]
  zero_mem' := fun g b => by simp only [Pi.zero_apply, map_zero]
  algebraMap_mem' := fun k g b => by
    simp only [Pi.algebraMap_apply, AlgEquiv.commutes]

/-- Membership in the equivariant subalgebra, unfolded. -/
theorem mem_galDescSubalgebra_iff {B : Type} {act : (↥L ≃ₐ[K] ↥L) → B → B}
    {h : B → ↥L} :
    h ∈ galDescSubalgebra K Ω L B act ↔ ∀ g b, h (act g b) = g (h b) :=
  Iff.rfl

/-- Pullback of equivariant functions along an equivariant map of
`Gal(L/K)`-sets: precomposition with `φ : B → C` carries equivariant
functions on `C` to equivariant functions on `B`, as a `K`-algebra
homomorphism. -/
def galDescPullback {B C : Type} (actB : (↥L ≃ₐ[K] ↥L) → B → B)
    (actC : (↥L ≃ₐ[K] ↥L) → C → C) (φ : B → C)
    (hφ : ∀ g b, φ (actB g b) = actC g (φ b)) :
    ↥(galDescSubalgebra K Ω L C actC) →ₐ[K] ↥(galDescSubalgebra K Ω L B actB) where
  toFun h := ⟨fun b => (h : C → ↥L) (φ b), fun g b => by
    show (h : C → ↥L) (φ (actB g b)) = g ((h : C → ↥L) (φ b))
    rw [hφ g b]
    exact h.2 g (φ b)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-! ##### Split Galois descent for the equivariant-function algebras

For the finite Galois group `Gal(L/K)` acting on an arbitrary type `B`
(set-level action), the equivariant subalgebra
`H_B = galDescSubalgebra K Ω L B act ⊆ (B → L)` satisfies classical
Galois descent in split form; the pieces proven here feed the sorried
`galDesc*` leaves below:

* `galDesc_linearIndependent` — a `K`-linearly independent family of
  equivariant functions stays `L`-linearly independent in `B → L`
  (minimal-relation argument on the Galois translates of a relation);
* `galDesc_mem_span` — every function `B → L` is an `L`-linear
  combination of equivariant functions (average the translates of `f`
  against a normal basis; the Dedekind matrix `(g (nb j))_{g,j}` is
  invertible because distinct algebra maps are `L`-linearly
  independent);
* `galDesc_finrank` — hence `dim_K H_B = |B|` for finite `B` (the
  split base-change map `L ⊗[K] H_B → (B → L)` is bijective);
* `galDescProdHom_bijective` — the tensor-comparison map
  `H_B ⊗[K] H_C → H_{B×C}` is bijective (injective by linear
  disjointness, surjective by the dimension count). -/

section GalDescCore

variable {B C : Type}

/-- **Linear disjointness of equivariant functions** (the injectivity
half of split Galois descent): a `K`-linearly independent family in the
equivariant subalgebra stays `L`-linearly independent as functions
`B → L`. Minimal-relation argument: normalize a shortest nontrivial
`L`-relation to have a coefficient `1`, subtract its Galois translates
(which are again relations, by equivariance of the functions), conclude
all coefficients are Galois-fixed, hence in `K` — contradiction. -/
theorem galDesc_linearIndependent [FiniteDimensional K ↥L] [IsGalois K ↥L]
    (act : (↥L ≃ₐ[K] ↥L) → B → B) {ι : Type*}
    {v : ι → ↥(galDescSubalgebra K Ω L B act)} (hv : LinearIndependent K v) :
    LinearIndependent ↥L fun i => (v i : B → ↥L) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀s, hi₀⟩ := hne
    set c' : ι → ↥L := fun i => (c i₀)⁻¹ * c i with hc'def
    have hrel : ∑ i ∈ s, c' i • (v i : B → ↥L) = 0 := by
      have h1 := congrArg (fun f : B → ↥L => (c i₀)⁻¹ • f) hc
      simpa [Finset.smul_sum, smul_smul, hc'def] using h1
    have hc'i₀ : c' i₀ = 1 := by
      simp only [hc'def]
      exact inv_mul_cancel₀ hi₀
    have hrelg : ∀ g : ↥L ≃ₐ[K] ↥L,
        ∑ i ∈ s, g (c' i) • (v i : B → ↥L) = 0 := by
      intro g
      have h0 : ∀ b : B, ∑ i ∈ s, c' i * (v i : B → ↥L) (act g⁻¹ b) = 0 := by
        intro b
        have h2 := congrFun hrel (act g⁻¹ b)
        simpa using h2
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc ∑ i ∈ s, g (c' i) * (v i : B → ↥L) b
          = ∑ i ∈ s, g (c' i) * g ((v i : B → ↥L) (act g⁻¹ b)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [(v i).2 g⁻¹ b, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = g (∑ i ∈ s, c' i * (v i : B → ↥L) (act g⁻¹ b)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => (map_mul g _ _).symm
        _ = 0 := by rw [h0 b, map_zero]
    have hfix : ∀ (g : ↥L ≃ₐ[K] ↥L) (i : ι), i ∈ s → g (c' i) = c' i := by
      intro g i hi
      have h3 : ∑ j ∈ s, (g (c' j) - c' j) • (v j : B → ↥L) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hrelg g, hrel, sub_zero]
      have h4 : ∑ j ∈ s.erase i₀, (g (c' j) - c' j) • (v j : B → ↥L) = 0 := by
        rwa [← Finset.add_sum_erase _ _ hi₀s, hc'i₀, map_one, sub_self, zero_smul,
          zero_add] at h3
      have h5 := ih (s.erase i₀) (Finset.erase_ssubset hi₀s) _ h4
      rcases eq_or_ne i i₀ with rfl | hne'
      · rw [hc'i₀, map_one]
      · exact sub_eq_zero.mp (h5 i (Finset.mem_erase.mpr ⟨hne', hi⟩))
    have hK : ∀ i : ι, ∃ k : K, i ∈ s → algebraMap K ↥L k = c' i := by
      intro i
      by_cases hi : i ∈ s
      · have hmem : c' i ∈ Set.range (algebraMap K ↥L) := by
          rw [IsGalois.mem_range_algebraMap_iff_fixed]
          exact fun g => hfix g i hi
        exact ⟨hmem.choose, fun _ => hmem.choose_spec⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose k hk using hK
    have hrelK : ∑ i ∈ s, k i • v i = 0 := by
      have hcoe : ((∑ i ∈ s, k i • v i : ↥(galDescSubalgebra K Ω L B act)) :
          B → ↥L) = ∑ i ∈ s, c' i • (v i : B → ↥L) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [SetLike.val_smul, ← hk i hi, algebraMap_smul]
      exact Subtype.ext (by rw [hcoe, hrel]; rfl)
    have h6 := linearIndependent_iff'.mp hv s k hrelK i₀ hi₀s
    rw [← hk i₀ hi₀s, h6, map_zero] at hc'i₀
    exact zero_ne_one hc'i₀

/-- **Spanning by equivariant functions** (the surjectivity half of
split Galois descent): every function `B → L` is an `L`-linear
combination of equivariant ones. For `c : L` the averaged function
`b ↦ ∑ g, g (c · f (act g⁻¹ b))` is equivariant; running `c` through a
normal basis of `L/K` and inverting the Dedekind matrix `(g (nb j))`
recovers `f` itself as a combination of averages. -/
theorem galDesc_mem_span [FiniteDimensional K ↥L] [IsGalois K ↥L]
    (act : (↥L ≃ₐ[K] ↥L) → B → B)
    (hone : ∀ b, act 1 b = b)
    (hmul : ∀ g₁ g₂ b, act (g₁ * g₂) b = act g₁ (act g₂ b)) (f : B → ↥L) :
    f ∈ Submodule.span ↥L (galDescSubalgebra K Ω L B act : Set (B → ↥L)) := by
  classical
  have havg : ∀ c : ↥L,
      (fun b => ∑ g : ↥L ≃ₐ[K] ↥L, g (c * f (act g⁻¹ b))) ∈
        galDescSubalgebra K Ω L B act := by
    intro c
    refine (mem_galDescSubalgebra_iff K Ω L).mpr fun g₀ b => ?_
    have hstep : ∀ g : ↥L ≃ₐ[K] ↥L,
        (g₀ * g) (c * f (act (g₀ * g)⁻¹ (act g₀ b))) = g₀ (g (c * f (act g⁻¹ b))) := by
      intro g
      have hact : act (g₀ * g)⁻¹ (act g₀ b) = act g⁻¹ b := by
        rw [← hmul, mul_inv_rev, inv_mul_cancel_right]
      rw [hact, AlgEquiv.mul_apply]
    calc (fun b => ∑ g : ↥L ≃ₐ[K] ↥L, g (c * f (act g⁻¹ b))) (act g₀ b)
        = ∑ g : ↥L ≃ₐ[K] ↥L, (g₀ * g) (c * f (act (g₀ * g)⁻¹ (act g₀ b))) :=
          (Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => rfl).symm
      _ = ∑ g : ↥L ≃ₐ[K] ↥L, g₀ (g (c * f (act g⁻¹ b))) :=
          Finset.sum_congr rfl fun g _ => hstep g
      _ = g₀ ((fun b => ∑ g : ↥L ≃ₐ[K] ↥L, g (c * f (act g⁻¹ b))) b) :=
          (map_sum g₀ _ _).symm
  set nb : Module.Basis (↥L ≃ₐ[K] ↥L) K ↥L := IsGalois.normalBasis K ↥L
  set M : Matrix (↥L ≃ₐ[K] ↥L) (↥L ≃ₐ[K] ↥L) ↥L :=
    Matrix.of fun g j => g (nb j) with hM
  have hMinj : Function.Injective M.vecMul := by
    have hli : LinearIndependent ↥L
        fun g : ↥L ≃ₐ[K] ↥L => (g : ↥L →ₐ[K] ↥L).toLinearMap :=
      (linearIndependent_toLinearMap K ↥L ↥L).comp
        (fun g : ↥L ≃ₐ[K] ↥L => (g : ↥L →ₐ[K] ↥L))
        AlgEquiv.coe_toAlgHom_injective
    have hker : ∀ z : (↥L ≃ₐ[K] ↥L) → ↥L, M.vecMul z = 0 → z = 0 := by
      intro z hz
      have hzero : (∑ g : ↥L ≃ₐ[K] ↥L, z g • (g : ↥L →ₐ[K] ↥L).toLinearMap)
          = (0 : ↥L →ₗ[K] ↥L) := by
        refine nb.ext fun j => ?_
        have hj : ∑ g : ↥L ≃ₐ[K] ↥L, z g * g (nb j) = 0 := by
          have h1 := congrFun hz j
          simpa [Matrix.vecMul, dotProduct, hM] using h1
        simpa using hj
      funext g
      exact Fintype.linearIndependent_iff.mp hli z hzero g
    intro x y hxy
    have hxy' : Matrix.vecMul x M = Matrix.vecMul y M := hxy
    have hsub := hker (x - y) (by rw [Matrix.sub_vecMul, hxy', sub_self])
    exact sub_eq_zero.mp hsub
  obtain ⟨d, hd⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.vecMul_injective_iff_isUnit.mp hMinj)) (Pi.single 1 1)
  have hfeq : f = ∑ j : ↥L ≃ₐ[K] ↥L,
      d j • fun b => ∑ g : ↥L ≃ₐ[K] ↥L, g (nb j * f (act g⁻¹ b)) := by
    funext b
    have hpt : ∀ g j : ↥L ≃ₐ[K] ↥L,
        d j * g (nb j * f (act g⁻¹ b)) = M g j * d j * g (f (act g⁻¹ b)) := by
      intro g j
      rw [map_mul, hM, Matrix.of_apply]
      ring
    have hRHS : (∑ j : ↥L ≃ₐ[K] ↥L, d j • fun b' =>
        ∑ g : ↥L ≃ₐ[K] ↥L, g (nb j * f (act g⁻¹ b'))) b
        = ∑ g : ↥L ≃ₐ[K] ↥L, M.mulVec d g * g (f (act g⁻¹ b)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc ∑ j : ↥L ≃ₐ[K] ↥L, d j * ∑ g : ↥L ≃ₐ[K] ↥L, g (nb j * f (act g⁻¹ b))
          = ∑ j : ↥L ≃ₐ[K] ↥L, ∑ g : ↥L ≃ₐ[K] ↥L, d j * g (nb j * f (act g⁻¹ b)) :=
            Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        _ = ∑ g : ↥L ≃ₐ[K] ↥L, ∑ j : ↥L ≃ₐ[K] ↥L, d j * g (nb j * f (act g⁻¹ b)) :=
            Finset.sum_comm
        _ = ∑ g : ↥L ≃ₐ[K] ↥L, ∑ j : ↥L ≃ₐ[K] ↥L, M g j * d j * g (f (act g⁻¹ b)) :=
            Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun j _ => hpt g j
        _ = ∑ g : ↥L ≃ₐ[K] ↥L, (∑ j : ↥L ≃ₐ[K] ↥L, M g j * d j) * g (f (act g⁻¹ b)) :=
            Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
        _ = ∑ g : ↥L ≃ₐ[K] ↥L, M.mulVec d g * g (f (act g⁻¹ b)) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            congr 1
    rw [hRHS, hd]
    simp [Pi.single_apply, ite_mul, hone]
  rw [hfeq]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (havg (nb j)))

/-- The equivariant subalgebra of a finite `Gal(L/K)`-set is a
finite-dimensional `K`-space (a subspace of the finite-dimensional
`B → L`; generic-`act` version of `galDescAlg_finite` below). -/
theorem galDesc_module_finite [FiniteDimensional K ↥L] [Finite B]
    (act : (↥L ≃ₐ[K] ↥L) → B → B) :
    Module.Finite K ↥(galDescSubalgebra K Ω L B act) := by
  classical
  haveI := Fintype.ofFinite B
  haveI : Module.Finite K (B → ↥L) := Module.Finite.pi
  exact FiniteDimensional.finiteDimensional_submodule
    (Subalgebra.toSubmodule (galDescSubalgebra K Ω L B act))

/-- **The dimension count of split descent**: the equivariant-function
algebra of a finite `Gal(L/K)`-set `B` has `K`-dimension `|B|` — the
split base-change map `θ : L ⊗[K] H_B → (B → L)`, `l ⊗ h ↦ l·h`, is
bijective (injective by `galDesc_linearIndependent` on a basis,
surjective by `galDesc_mem_span`), and `dim_L (B → L) = |B|`. -/
theorem galDesc_finrank [FiniteDimensional K ↥L] [IsGalois K ↥L] [Finite B]
    (act : (↥L ≃ₐ[K] ↥L) → B → B)
    (hone : ∀ b, act 1 b = b)
    (hmul : ∀ g₁ g₂ b, act (g₁ * g₂) b = act g₁ (act g₂ b)) :
    Module.finrank K ↥(galDescSubalgebra K Ω L B act) = Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  haveI : Module.Finite K ↥(galDescSubalgebra K Ω L B act) :=
    galDesc_module_finite K Ω L act
  set θ : ↥L ⊗[K] ↥(galDescSubalgebra K Ω L B act) →ₗ[↥L] (B → ↥L) :=
    ((Subalgebra.toSubmodule (galDescSubalgebra K Ω L B act)).subtype).liftBaseChange
      ↥L with hθ
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    set β := Module.finBasis K ↥(galDescSubalgebra K Ω L B act)
    have hLI := galDesc_linearIndependent K Ω L act β.linearIndependent
    have hcoeff : ∀ i, (β.baseChange ↥L).repr t i = 0 := by
      have hθt : ∑ i, (β.baseChange ↥L).repr t i • (β i : B → ↥L) = 0 := by
        have hsum : θ (∑ i, (β.baseChange ↥L).repr t i • β.baseChange ↥L i)
            = ∑ i, (β.baseChange ↥L).repr t i • (β i : B → ↥L) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, Module.Basis.baseChange_apply, hθ,
            LinearMap.liftBaseChange_tmul, one_smul]
          rfl
        rw [← hsum, Module.Basis.sum_repr, ht]
      exact fun i => Fintype.linearIndependent_iff.mp hLI _ hθt i
    rw [← Module.Basis.sum_repr (β.baseChange ↥L) t]
    simp [hcoeff]
  have hsurj : Function.Surjective θ := by
    intro f
    have hle : Submodule.span ↥L (galDescSubalgebra K Ω L B act : Set (B → ↥L)) ≤
        LinearMap.range θ := by
      rw [Submodule.span_le]
      intro x hx
      exact ⟨(1 : ↥L) ⊗ₜ[K] ⟨x, hx⟩, by
        rw [hθ, LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
    exact LinearMap.mem_range.mp (hle (galDesc_mem_span K Ω L act hone hmul f))
  have hfr := (LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_pi] at hfr
  rw [Nat.card_eq_fintype_card]
  exact hfr

/-- The tensor-comparison map of a pair of `Gal(L/K)`-sets:
`h ⊗ k ↦ ((b, c) ↦ h b · k c)`, an algebra map into the equivariant
functions on `B × C` (with the componentwise action). The comparison
map `galDescTensorHom` of the twisted constant group scheme is its
instance at `B = C = A`. -/
noncomputable def galDescProdHom (actB : (↥L ≃ₐ[K] ↥L) → B → B)
    (actC : (↥L ≃ₐ[K] ↥L) → C → C) :
    (↥(galDescSubalgebra K Ω L B actB) ⊗[K] ↥(galDescSubalgebra K Ω L C actC))
      →ₐ[K] ↥(galDescSubalgebra K Ω L (B × C) fun g x => (actB g x.1, actC g x.2)) :=
  Algebra.TensorProduct.productMap
    (galDescPullback K Ω L (fun g x => (actB g x.1, actC g x.2)) actB Prod.fst
      fun _ _ => rfl)
    (galDescPullback K Ω L (fun g x => (actB g x.1, actC g x.2)) actC Prod.snd
      fun _ _ => rfl)

theorem galDescProdHom_tmul_apply (actB : (↥L ≃ₐ[K] ↥L) → B → B)
    (actC : (↥L ≃ₐ[K] ↥L) → C → C)
    (h : ↥(galDescSubalgebra K Ω L B actB)) (k : ↥(galDescSubalgebra K Ω L C actC))
    (x : B × C) :
    (galDescProdHom K Ω L actB actC (h ⊗ₜ[K] k) : (B × C) → ↥L) x
      = (h : B → ↥L) x.1 * (k : C → ↥L) x.2 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Bijectivity of the tensor-comparison map** (the descent core):
`H_B ⊗[K] H_C → H_{B×C}` is bijective for finite `Gal(L/K)`-sets.
Injectivity: expand along a basis of `H_C`; the coefficient functions
vanish because a `K`-basis of `H_C` stays `L`-linearly independent
(`galDesc_linearIndependent`). Surjectivity: both sides have
`K`-dimension `|B|·|C|` (`galDesc_finrank`). -/
theorem galDescProdHom_bijective [FiniteDimensional K ↥L] [IsGalois K ↥L]
    [Finite B] [Finite C]
    (actB : (↥L ≃ₐ[K] ↥L) → B → B) (actC : (↥L ≃ₐ[K] ↥L) → C → C)
    (honeB : ∀ b, actB 1 b = b)
    (hmulB : ∀ g₁ g₂ b, actB (g₁ * g₂) b = actB g₁ (actB g₂ b))
    (honeC : ∀ c, actC 1 c = c)
    (hmulC : ∀ g₁ g₂ c, actC (g₁ * g₂) c = actC g₁ (actC g₂ c)) :
    Function.Bijective (galDescProdHom K Ω L actB actC) := by
  classical
  haveI : Module.Finite K ↥(galDescSubalgebra K Ω L B actB) :=
    galDesc_module_finite K Ω L actB
  haveI : Module.Finite K ↥(galDescSubalgebra K Ω L C actC) :=
    galDesc_module_finite K Ω L actC
  haveI : Module.Finite K
      ↥(galDescSubalgebra K Ω L (B × C) fun g x => (actB g x.1, actC g x.2)) :=
    galDesc_module_finite K Ω L _
  have hinj : Function.Injective (galDescProdHom K Ω L actB actC) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    set γ := Module.finBasis K ↥(galDescSubalgebra K Ω L C actC)
    obtain ⟨w, rfl⟩ : ∃ w : Fin (Module.finrank K ↥(galDescSubalgebra K Ω L C actC))
        → ↥(galDescSubalgebra K Ω L B actB), t = ∑ i, w i ⊗ₜ[K] γ i := by
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul h k =>
        refine ⟨fun i => γ.repr k i • h, ?_⟩
        conv_lhs => rw [← Module.Basis.sum_repr γ k]
        rw [TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
      | add t₁ t₂ h₁ h₂ =>
        obtain ⟨w₁, rfl⟩ := h₁
        obtain ⟨w₂, rfl⟩ := h₂
        refine ⟨w₁ + w₂, ?_⟩
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (TensorProduct.add_tmul _ _ _).symm
    have hLI := galDesc_linearIndependent K Ω L actC γ.linearIndependent
    have hpt : ∀ (b : B) (cc : C),
        ∑ i, ((w i : B → ↥L) b) * ((γ i : C → ↥L) cc) = 0 := by
      intro b cc
      have h1 := congrArg
        (fun F : ↥(galDescSubalgebra K Ω L (B × C)
            fun g x => (actB g x.1, actC g x.2)) => (F : (B × C) → ↥L) (b, cc)) ht
      simpa [map_sum, galDescProdHom_tmul_apply] using h1
    have hw : ∀ i, w i = 0 := by
      intro i
      apply Subtype.ext
      funext b
      have hrel : ∑ j, ((w j : B → ↥L) b) • (γ j : C → ↥L) = 0 := by
        funext cc
        simpa using hpt b cc
      exact Fintype.linearIndependent_iff.mp hLI _ hrel i
    simp [hw]
  refine ⟨hinj, ?_⟩
  have hfr : Module.finrank K
      (↥(galDescSubalgebra K Ω L B actB) ⊗[K] ↥(galDescSubalgebra K Ω L C actC))
      = Module.finrank K
        ↥(galDescSubalgebra K Ω L (B × C) fun g x => (actB g x.1, actC g x.2)) := by
    rw [Module.finrank_tensorProduct,
      galDesc_finrank K Ω L actB honeB hmulB,
      galDesc_finrank K Ω L actC honeC hmulC,
      galDesc_finrank K Ω L (fun g (x : B × C) => (actB g x.1, actC g x.2))
        (fun x => by simp [honeB, honeC])
        (fun g₁ g₂ x => by simp [hmulB, hmulC]),
      Nat.card_prod]
  have hsurjlin := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K)
    (V := ↥(galDescSubalgebra K Ω L B actB) ⊗[K] ↥(galDescSubalgebra K Ω L C actC))
    (V₂ := ↥(galDescSubalgebra K Ω L (B × C) fun g x => (actB g x.1, actC g x.2)))
    hfr (f := (galDescProdHom K Ω L actB actC).toLinearMap)).mp
    (by simpa using hinj)
  simpa using hsurjlin

/-- Postcomposition with an algebra map distributes over
`Algebra.TensorProduct.lift` into a commutative target (toolkit for the
Hopf-axiom computations below). -/
theorem galDesc_comp_lift {R A₁ A₂ S T : Type*} [CommSemiring R]
    [Semiring A₁] [Algebra R A₁] [Semiring A₂] [Algebra R A₂]
    [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (f : A₁ →ₐ[R] S) (g : A₂ →ₐ[R] S) :
    φ.comp (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _)
      = Algebra.TensorProduct.lift (φ.comp f) (φ.comp g)
          fun _ _ => Commute.all _ _ :=
  Algebra.TensorProduct.ext' fun x y => by
    simp [Algebra.TensorProduct.lift_tmul]

/-- The lift of three algebra maps into a commutative target regroups
along the associator (toolkit for the coassociativity leaf below). -/
theorem galDesc_lift_assoc {R A₁ A₂ A₃ S : Type*} [CommSemiring R]
    [Semiring A₁] [Algebra R A₁] [Semiring A₂] [Algebra R A₂]
    [Semiring A₃] [Algebra R A₃] [CommSemiring S] [Algebra R S]
    (f : A₁ →ₐ[R] S) (g : A₂ →ₐ[R] S) (h : A₃ →ₐ[R] S) :
    (Algebra.TensorProduct.lift f
        (Algebra.TensorProduct.lift g h fun _ _ => Commute.all _ _)
        fun _ _ => Commute.all _ _).comp
      (Algebra.TensorProduct.assoc R R R A₁ A₂ A₃).toAlgHom
      = Algebra.TensorProduct.lift
          (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _) h
          fun _ _ => Commute.all _ _ := by
  apply Algebra.TensorProduct.ext'
  intro u c
  induction u using TensorProduct.induction_on with
  | zero => simp [TensorProduct.zero_tmul]
  | tmul x y =>
    simp [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul,
      mul_assoc]
  | add u₁ u₂ h₁ h₂ =>
    rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂]

/-- Evaluation of an equivariant function at a point of `B`, valued in
`L` — the separating functional for the Hopf-axiom computations. -/
def galDescEvalL (act : (↥L ≃ₐ[K] ↥L) → B → B) (b : B) :
    ↥(galDescSubalgebra K Ω L B act) →ₐ[K] ↥L :=
  (Pi.evalAlgHom K (fun _ : B => ↥L) b).comp (galDescSubalgebra K Ω L B act).val

/-- Evaluating the tensor-comparison map at a point of `B × C` is the
lift of the two evaluations. -/
theorem galDescEvalL_comp_prodHom (actB : (↥L ≃ₐ[K] ↥L) → B → B)
    (actC : (↥L ≃ₐ[K] ↥L) → C → C) (b : B) (c : C) :
    (galDescEvalL K Ω L (fun g x => (actB g x.1, actC g x.2)) (b, c)).comp
        (galDescProdHom K Ω L actB actC)
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L actB b)
          (galDescEvalL K Ω L actC c) fun _ _ => Commute.all _ _ :=
  Algebra.TensorProduct.ext' fun h k => by
    rw [Algebra.TensorProduct.lift_tmul]
    exact galDescProdHom_tmul_apply K Ω L actB actC h k (b, c)

end GalDescCore

variable (A : Type) [AddCommGroup A]
variable (ρ' : (↥L ≃ₐ[K] ↥L) →* AddMonoid.End A)

/-- The carrier of the twisted constant group scheme's Hopf algebra:
`Gal(L/K)`-equivariant functions `A → L`. -/
abbrev GalDescAlg : Type :=
  ↥(galDescSubalgebra K Ω L A fun g a => ρ' g a)

/-- Equivariant functions on `A × A` (with the diagonal action), the
target of the tensor-comparison isomorphism. -/
abbrev GalDescAlg₂ : Type :=
  ↥(galDescSubalgebra K Ω L (A × A) fun g x => (ρ' g x.1, ρ' g x.2))

/-- Pullback along the first projection `A × A → A`. -/
def galDescFst : GalDescAlg K Ω L A ρ' →ₐ[K] GalDescAlg₂ K Ω L A ρ' :=
  galDescPullback K Ω L (fun g x => (ρ' g x.1, ρ' g x.2)) (fun g a => ρ' g a)
    Prod.fst (fun _ _ => rfl)

/-- Pullback along the second projection `A × A → A`. -/
def galDescSnd : GalDescAlg K Ω L A ρ' →ₐ[K] GalDescAlg₂ K Ω L A ρ' :=
  galDescPullback K Ω L (fun g x => (ρ' g x.1, ρ' g x.2)) (fun g a => ρ' g a)
    Prod.snd (fun _ _ => rfl)

/-- Pullback along the addition `A × A → A` — the group law of the
twisted constant group scheme, before identification of the tensor
square. -/
def galDescAdd : GalDescAlg K Ω L A ρ' →ₐ[K] GalDescAlg₂ K Ω L A ρ' :=
  galDescPullback K Ω L (fun g x => (ρ' g x.1, ρ' g x.2)) (fun g a => ρ' g a)
    (fun x => x.1 + x.2) (fun g x => (map_add (ρ' g) x.1 x.2).symm)

/-- Pullback along the negation `A → A` — the antipode of the twisted
constant group scheme. -/
def galDescAntipode : GalDescAlg K Ω L A ρ' →ₐ[K] GalDescAlg K Ω L A ρ' :=
  galDescPullback K Ω L (fun g a => ρ' g a) (fun g a => ρ' g a)
    (fun a => -a) (fun g a => (map_neg (ρ' g) a).symm)

/-- The tensor-comparison map `H ⊗[K] H → H₂`: `h₁ ⊗ h₂` acts as the
two-variable function `(a, b) ↦ h₁(a)·h₂(b)`. -/
noncomputable def galDescTensorHom :
    (GalDescAlg K Ω L A ρ') ⊗[K] (GalDescAlg K Ω L A ρ') →ₐ[K]
      GalDescAlg₂ K Ω L A ρ' :=
  Algebra.TensorProduct.productMap (galDescFst K Ω L A ρ') (galDescSnd K Ω L A ρ')

/-- **Galois descent for the tensor square** (PROVEN — the descent
core of the finite-quotient package): the comparison map
`H ⊗[K] H → H₂`, `h₁ ⊗ h₂ ↦ ((a,b) ↦ h₁(a)·h₂(b))`, is bijective. Both
sides have `K`-dimension `|A|²` and the map is injective by linear
disjointness of equivariant functions — the instance at `B = C = A` of
the split-descent core `galDescProdHom_bijective` above. -/
theorem galDescTensorHom_bijective [FiniteDimensional K ↥L] [IsGalois K ↥L]
    [Finite A] :
    Function.Bijective (galDescTensorHom K Ω L A ρ') :=
  galDescProdHom_bijective K Ω L (fun g a => ρ' g a) (fun g a => ρ' g a)
    (fun b => by rw [map_one]; rfl)
    (fun g₁ g₂ b => by rw [map_mul]; rfl)
    (fun b => by rw [map_one]; rfl)
    (fun g₁ g₂ b => by rw [map_mul]; rfl)

variable [FiniteDimensional K ↥L] [IsGalois K ↥L] [Finite A]

/-- The tensor-comparison isomorphism `H ⊗[K] H ≃ H₂` (from the sorried
bijectivity leaf). -/
noncomputable def galDescTensorEquiv :
    ((GalDescAlg K Ω L A ρ') ⊗[K] (GalDescAlg K Ω L A ρ')) ≃ₐ[K]
      GalDescAlg₂ K Ω L A ρ' :=
  AlgEquiv.ofBijective (galDescTensorHom K Ω L A ρ')
    (galDescTensorHom_bijective K Ω L A ρ')

/-- The comultiplication of the twisted constant group scheme: pull
back along the addition, then identify the equivariant functions on
`A × A` with the tensor square. -/
noncomputable def galDescComul :
    GalDescAlg K Ω L A ρ' →ₐ[K]
      (GalDescAlg K Ω L A ρ') ⊗[K] (GalDescAlg K Ω L A ρ') :=
  ((galDescTensorEquiv K Ω L A ρ').symm.toAlgHom).comp (galDescAdd K Ω L A ρ')

/-- The tensor comparison inverts the comultiplication back to the
pullback along the addition: `μ ∘ Δ = add*`. -/
theorem galDescTensorHom_comp_comul :
    (galDescTensorHom K Ω L A ρ').comp (galDescComul K Ω L A ρ')
      = galDescAdd K Ω L A ρ' :=
  AlgHom.ext fun h =>
    (galDescTensorEquiv K Ω L A ρ').apply_symm_apply (galDescAdd K Ω L A ρ' h)

/-- **Evaluations compose with the comultiplication as addition of the
evaluation points**: `(ev_x ⊗ ev_y) ∘ Δ = ev_{x+y}` — the computational
heart of all remaining Hopf-axiom leaves. -/
theorem galDesc_lift_evalL_comp_comul (x y : A) :
    (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y)
        fun _ _ => Commute.all _ _).comp (galDescComul K Ω L A ρ')
      = galDescEvalL K Ω L (fun g a => ρ' g a) (x + y) := by
  have h1 : Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
      (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
      = (galDescEvalL K Ω L (fun g x => (ρ' g x.1, ρ' g x.2)) (x, y)).comp
          (galDescTensorHom K Ω L A ρ') :=
    (galDescEvalL_comp_prodHom K Ω L (fun g a => ρ' g a)
      (fun g a => ρ' g a) x y).symm
  rw [h1, AlgHom.comp_assoc, galDescTensorHom_comp_comul]
  exact AlgHom.ext fun h => rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Elements of the triple tensor `H ⊗ (H ⊗ H)` are separated by the
triple evaluations `ev_a ⊗ (ev_b ⊗ ev_c)`: the comparison maps into the
equivariant functions on `A × (A × A)` are injective, and equivariant
functions are separated pointwise. -/
theorem galDescTensor₃_ext
    {x y : GalDescAlg K Ω L A ρ' ⊗[K]
      (GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ')}
    (hxy : ∀ a b c : A,
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
        (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) b)
          (galDescEvalL K Ω L (fun g a => ρ' g a) c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) x
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
        (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) b)
          (galDescEvalL K Ω L (fun g a => ρ' g a) c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) y) :
    x = y := by
  classical
  have hval : ∀ (t : GalDescAlg K Ω L A ρ' ⊗[K]
      (GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ')) (a b c : A),
      (galDescProdHom K Ω L (fun g a => ρ' g a) (fun g x => (ρ' g x.1, ρ' g x.2))
        ((Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
          (galDescTensorHom K Ω L A ρ')) t) : A × (A × A) → ↥L) (a, (b, c))
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
        (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) b)
          (galDescEvalL K Ω L (fun g a => ρ' g a) c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) t := by
    intro t a b c
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul h u =>
      have hE : ((galDescTensorHom K Ω L A ρ' u : GalDescAlg₂ K Ω L A ρ') :
          A × A → ↥L) (b, c)
          = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) b)
            (galDescEvalL K Ω L (fun g a => ρ' g a) c)
            (fun _ _ => Commute.all _ _) u :=
        DFunLike.congr_fun (galDescEvalL_comp_prodHom K Ω L (fun g a => ρ' g a)
          (fun g a => ρ' g a) b c) u
      calc (galDescProdHom K Ω L (fun g a => ρ' g a)
            (fun g x => (ρ' g x.1, ρ' g x.2))
            ((Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
              (galDescTensorHom K Ω L A ρ')) (h ⊗ₜ[K] u)) : A × (A × A) → ↥L)
            (a, (b, c))
          = (h : A → ↥L) a *
              ((galDescTensorHom K Ω L A ρ' u : GalDescAlg₂ K Ω L A ρ') :
                A × A → ↥L) (b, c) := rfl
        _ = (h : A → ↥L) a *
              Algebra.TensorProduct.lift
                (galDescEvalL K Ω L (fun g a => ρ' g a) b)
                (galDescEvalL K Ω L (fun g a => ρ' g a) c)
                (fun _ _ => Commute.all _ _) u := by rw [hE]
        _ = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
              (Algebra.TensorProduct.lift
                (galDescEvalL K Ω L (fun g a => ρ' g a) b)
                (galDescEvalL K Ω L (fun g a => ρ' g a) c)
                fun _ _ => Commute.all _ _)
              (fun _ _ => Commute.all _ _) (h ⊗ₜ[K] u) := by
            rw [Algebra.TensorProduct.lift_tmul]
            rfl
    | add t₁ t₂ ih₁ ih₂ =>
      simp [map_add, ih₁, ih₂]
  have hmapinj : Function.Injective
      ⇑(Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
        (galDescTensorHom K Ω L A ρ')) := by
    have h1 := Module.Flat.lTensor_preserves_injective_linearMap
      (M := GalDescAlg K Ω L A ρ') (galDescTensorHom K Ω L A ρ').toLinearMap
      (galDescTensorHom_bijective K Ω L A ρ').injective
    exact h1
  have hprodinj := (galDescProdHom_bijective K Ω L (fun g a => ρ' g a)
    (fun g x => (ρ' g x.1, ρ' g x.2))
    (fun b => by rw [map_one]; rfl)
    (fun g₁ g₂ b => by rw [map_mul]; rfl)
    (fun p => by rw [map_one]; rfl)
    (fun g₁ g₂ p => by rw [map_mul]; rfl)).injective
  apply hmapinj
  apply hprodinj
  apply Subtype.ext
  funext p
  obtain ⟨a, bc⟩ := p
  obtain ⟨b, c⟩ := bc
  rw [hval x a b c, hval y a b c]
  exact hxy a b c

omit [Finite A] in
/-- The value at `0` of an equivariant function is Galois-fixed, hence
lies in the base field (PROVEN — `IsGalois.mem_range_algebraMap_iff_fixed`). -/
theorem galDesc_apply_zero_mem_range (h : GalDescAlg K Ω L A ρ') :
    (h : A → ↥L) 0 ∈ Set.range (algebraMap K ↥L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro g
  have h2 := h.2 g 0
  simp only [map_zero] at h2
  exact h2.symm

/-- The counit of the twisted constant group scheme: evaluation at the
identity point `0 ∈ A`, landing in `K` by the fixed-field
identification. -/
noncomputable def galDescCounit : GalDescAlg K Ω L A ρ' →ₐ[K] K where
  toFun h := (galDesc_apply_zero_mem_range K Ω L A ρ' h).choose
  map_one' := by
    apply (algebraMap K ↥L).injective
    rw [(galDesc_apply_zero_mem_range K Ω L A ρ' 1).choose_spec, map_one]
    rfl
  map_mul' x y := by
    apply (algebraMap K ↥L).injective
    rw [map_mul, (galDesc_apply_zero_mem_range K Ω L A ρ' (x * y)).choose_spec,
      (galDesc_apply_zero_mem_range K Ω L A ρ' x).choose_spec,
      (galDesc_apply_zero_mem_range K Ω L A ρ' y).choose_spec]
    rfl
  map_zero' := by
    apply (algebraMap K ↥L).injective
    rw [(galDesc_apply_zero_mem_range K Ω L A ρ' 0).choose_spec, map_zero]
    rfl
  map_add' x y := by
    apply (algebraMap K ↥L).injective
    rw [map_add, (galDesc_apply_zero_mem_range K Ω L A ρ' (x + y)).choose_spec,
      (galDesc_apply_zero_mem_range K Ω L A ρ' x).choose_spec,
      (galDesc_apply_zero_mem_range K Ω L A ρ' y).choose_spec]
    rfl
  commutes' r := by
    apply (algebraMap K ↥L).injective
    rw [(galDesc_apply_zero_mem_range K Ω L A ρ'
      (algebraMap K (GalDescAlg K Ω L A ρ') r)).choose_spec]
    rfl

omit [Finite A] in
/-- The defining property of the counit: its image in `L` is the value
of the equivariant function at `0`. -/
theorem galDescCounit_algebraMap (h : GalDescAlg K Ω L A ρ') :
    algebraMap K ↥L (galDescCounit K Ω L A ρ' h) = (h : A → ↥L) 0 :=
  (galDesc_apply_zero_mem_range K Ω L A ρ' h).choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Coassociativity of the twisted comultiplication** (PROVEN —
after composing with the injective tensor comparison into functions on
`A × (A × A)`, both sides are pullback along `(a,b,c) ↦ a+b+c`;
elementwise, all triple evaluations agree by `add_assoc`). -/
theorem galDescComul_coassoc :
    (Algebra.TensorProduct.assoc K K K (GalDescAlg K Ω L A ρ')
      (GalDescAlg K Ω L A ρ') (GalDescAlg K Ω L A ρ')).toAlgHom.comp
      ((Algebra.TensorProduct.map (galDescComul K Ω L A ρ')
        (AlgHom.id K (GalDescAlg K Ω L A ρ'))).comp (galDescComul K Ω L A ρ')) =
    (Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
      (galDescComul K Ω L A ρ')).comp (galDescComul K Ω L A ρ') := by
  classical
  apply AlgHom.ext
  intro h
  apply galDescTensor₃_ext K Ω L A ρ'
  intro a b c
  simp only [AlgHom.coe_comp, Function.comp_apply]
  have hΔ : ∀ (x y : A) (t : GalDescAlg K Ω L A ρ'),
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
        (galDescComul K Ω L A ρ' t) = (t : A → ↥L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galDesc_lift_evalL_comp_comul K Ω L A ρ' x y) t
  have h1 := DFunLike.congr_fun (galDesc_lift_assoc
    (galDescEvalL K Ω L (fun g a => ρ' g a) a)
    (galDescEvalL K Ω L (fun g a => ρ' g a) b)
    (galDescEvalL K Ω L (fun g a => ρ' g a) c))
    ((Algebra.TensorProduct.map (galDescComul K Ω L A ρ')
      (AlgHom.id K (GalDescAlg K Ω L A ρ'))) (galDescComul K Ω L A ρ' h))
  simp only [AlgHom.coe_comp, Function.comp_apply] at h1
  rw [h1]
  have hleft : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      Algebra.TensorProduct.lift
        (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
          (galDescEvalL K Ω L (fun g a => ρ' g a) b) fun _ _ => Commute.all _ _)
        (galDescEvalL K Ω L (fun g a => ρ' g a) c) (fun _ _ => Commute.all _ _)
        ((Algebra.TensorProduct.map (galDescComul K Ω L A ρ')
          (AlgHom.id K (GalDescAlg K Ω L A ρ'))) u)
      = Algebra.TensorProduct.lift
          (galDescEvalL K Ω L (fun g a => ρ' g a) (a + b))
          (galDescEvalL K Ω L (fun g a => ρ' g a) c)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_id, id_eq]
      rw [hΔ a b p]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  have hright : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
        (Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) b)
          (galDescEvalL K Ω L (fun g a => ρ' g a) c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _)
        ((Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
          (galDescComul K Ω L A ρ')) u)
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) a)
          (galDescEvalL K Ω L (fun g a => ρ' g a) (b + c))
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_id, id_eq]
      rw [hΔ b c q]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  rw [hleft (galDescComul K Ω L A ρ' h), hright (galDescComul K Ω L A ρ' h),
    hΔ (a + b) c h, hΔ a (b + c) h, add_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Left counit axiom for the twisted comultiplication** (PROVEN —
evaluation of the first tensor factor at `0` collapses the pullback
along addition to the identity: pointwise, `h (0 + z) = h z`). -/
theorem galDescComul_rTensor_counit :
    (Algebra.TensorProduct.map (galDescCounit K Ω L A ρ')
      (AlgHom.id K (GalDescAlg K Ω L A ρ'))).comp (galDescComul K Ω L A ρ') =
    ((Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).symm :
      GalDescAlg K Ω L A ρ' →ₐ[K] K ⊗[K] GalDescAlg K Ω L A ρ') := by
  classical
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).injective
  show (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ'))
      ((Algebra.TensorProduct.map (galDescCounit K Ω L A ρ')
        (AlgHom.id K (GalDescAlg K Ω L A ρ'))) (galDescComul K Ω L A ρ' h))
    = (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ'))
      ((Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).symm h)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : GalDescAlg K Ω L A ρ'),
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
        (galDescComul K Ω L A ρ' t) = (t : A → ↥L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galDesc_lift_evalL_comp_comul K Ω L A ρ' x y) t
  have hval : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      ((Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ'))
        ((Algebra.TensorProduct.map (galDescCounit K Ω L A ρ')
          (AlgHom.id K (GalDescAlg K Ω L A ρ'))) u) : A → ↥L) z
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) 0)
          (galDescEvalL K Ω L (fun g a => ρ' g a) z)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        AlgHom.coe_id, id_eq, Algebra.TensorProduct.lift_tmul]
      rw [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def,
        galDescCounit_algebraMap]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  rw [hval (galDescComul K Ω L A ρ' h), hΔ 0 z h, zero_add]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Right counit axiom for the twisted comultiplication** (PROVEN —
symmetric to the left axiom: pointwise, `h (z + 0) = h z`). -/
theorem galDescComul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
      (galDescCounit K Ω L A ρ')).comp (galDescComul K Ω L A ρ') =
    ((Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ')).symm :
      GalDescAlg K Ω L A ρ' →ₐ[K] GalDescAlg K Ω L A ρ' ⊗[K] K) := by
  classical
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ')).injective
  show (Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ'))
      ((Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
        (galDescCounit K Ω L A ρ')) (galDescComul K Ω L A ρ' h))
    = (Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ'))
      ((Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ')).symm h)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : GalDescAlg K Ω L A ρ'),
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
        (galDescComul K Ω L A ρ' t) = (t : A → ↥L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galDesc_lift_evalL_comp_comul K Ω L A ρ' x y) t
  have hval : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      ((Algebra.TensorProduct.rid K K (GalDescAlg K Ω L A ρ'))
        ((Algebra.TensorProduct.map (AlgHom.id K (GalDescAlg K Ω L A ρ'))
          (galDescCounit K Ω L A ρ')) u) : A → ↥L) z
      = Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) z)
          (galDescEvalL K Ω L (fun g a => ρ' g a) 0)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        AlgHom.coe_id, id_eq, Algebra.TensorProduct.lift_tmul]
      rw [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def,
        galDescCounit_algebraMap]
      exact mul_comm _ _
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  rw [hval (galDescComul K Ω L A ρ' h), hΔ z 0 h, add_zero]

/-- The bialgebra structure of the twisted constant group scheme; the
axioms are the three sorried leaves above. -/
noncomputable instance galDescBialgebra : Bialgebra K (GalDescAlg K Ω L A ρ') :=
  Bialgebra.ofAlgHom (galDescComul K Ω L A ρ') (galDescCounit K Ω L A ρ')
    (galDescComul_coassoc K Ω L A ρ')
    (galDescComul_rTensor_counit K Ω L A ρ')
    (galDescComul_lTensor_counit K Ω L A ρ')

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Left antipode axiom** (PROVEN — after the tensor comparison,
`m ∘ (S ⊗ id) ∘ Δ` is pullback along `a ↦ (-a) + a = 0`, the unit of
the convolution; pointwise, `h (-z + z) = h 0`). -/
theorem galDesc_mul_antipode_rTensor_comul :
    ((Algebra.TensorProduct.lift (galDescAntipode K Ω L A ρ')
      (AlgHom.id K (GalDescAlg K Ω L A ρ')) fun _ => Commute.all _).comp
      (Bialgebra.comulAlgHom K (GalDescAlg K Ω L A ρ'))) =
    (Algebra.ofId K (GalDescAlg K Ω L A ρ')).comp
      (Bialgebra.counitAlgHom K (GalDescAlg K Ω L A ρ')) := by
  classical
  apply AlgHom.ext
  intro h
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : GalDescAlg K Ω L A ρ'),
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
        (galDescComul K Ω L A ρ' t) = (t : A → ↥L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galDesc_lift_evalL_comp_comul K Ω L A ρ' x y) t
  have hval : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      ((Algebra.TensorProduct.lift (galDescAntipode K Ω L A ρ')
        (AlgHom.id K (GalDescAlg K Ω L A ρ')) fun _ => Commute.all _) u
        : A → ↥L) z
      = Algebra.TensorProduct.lift
          (galDescEvalL K Ω L (fun g a => ρ' g a) (-z))
          (galDescEvalL K Ω L (fun g a => ρ' g a) z)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq]
      rw [MulMemClass.coe_mul, Pi.mul_apply]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  show ((Algebra.TensorProduct.lift (galDescAntipode K Ω L A ρ')
      (AlgHom.id K (GalDescAlg K Ω L A ρ')) fun _ => Commute.all _)
      (galDescComul K Ω L A ρ' h) : A → ↥L) z
    = ((Algebra.ofId K (GalDescAlg K Ω L A ρ'))
      (galDescCounit K Ω L A ρ' h) : A → ↥L) z
  rw [hval (galDescComul K Ω L A ρ' h), hΔ (-z) z h, neg_add_cancel]
  exact (galDescCounit_algebraMap K Ω L A ρ' h).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Right antipode axiom** (PROVEN — symmetric to the left axiom:
pointwise, `h (z + -z) = h 0`). -/
theorem galDesc_mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (AlgHom.id K (GalDescAlg K Ω L A ρ'))
      (galDescAntipode K Ω L A ρ') fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom K (GalDescAlg K Ω L A ρ')) =
    (Algebra.ofId K (GalDescAlg K Ω L A ρ')).comp
      (Bialgebra.counitAlgHom K (GalDescAlg K Ω L A ρ')) := by
  classical
  apply AlgHom.ext
  intro h
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : GalDescAlg K Ω L A ρ'),
      Algebra.TensorProduct.lift (galDescEvalL K Ω L (fun g a => ρ' g a) x)
        (galDescEvalL K Ω L (fun g a => ρ' g a) y) (fun _ _ => Commute.all _ _)
        (galDescComul K Ω L A ρ' t) = (t : A → ↥L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galDesc_lift_evalL_comp_comul K Ω L A ρ' x y) t
  have hval : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
      ((Algebra.TensorProduct.lift (AlgHom.id K (GalDescAlg K Ω L A ρ'))
        (galDescAntipode K Ω L A ρ') fun _ _ => Commute.all _ _) u
        : A → ↥L) z
      = Algebra.TensorProduct.lift
          (galDescEvalL K Ω L (fun g a => ρ' g a) z)
          (galDescEvalL K Ω L (fun g a => ρ' g a) (-z))
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq]
      rw [MulMemClass.coe_mul, Pi.mul_apply]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  show ((Algebra.TensorProduct.lift (AlgHom.id K (GalDescAlg K Ω L A ρ'))
      (galDescAntipode K Ω L A ρ') fun _ _ => Commute.all _ _)
      (galDescComul K Ω L A ρ' h) : A → ↥L) z
    = ((Algebra.ofId K (GalDescAlg K Ω L A ρ'))
      (galDescCounit K Ω L A ρ' h) : A → ↥L) z
  rw [hval (galDescComul K Ω L A ρ' h), hΔ z (-z) h, add_neg_cancel]
  exact (galDescCounit_algebraMap K Ω L A ρ' h).symm

/-- The Hopf structure of the twisted constant group scheme: the
antipode is pullback along negation; the axioms are the two sorried
leaves above. -/
noncomputable instance galDescHopfAlgebra :
    HopfAlgebra K (GalDescAlg K Ω L A ρ') :=
  HopfAlgebra.ofAlgHom (galDescAntipode K Ω L A ρ')
    (galDesc_mul_antipode_rTensor_comul K Ω L A ρ')
    (galDesc_mul_antipode_lTensor_comul K Ω L A ρ')

/-- The equivariant function algebra is finite-dimensional over `K`
(PROVEN — a subspace of the finite-dimensional `A → L`). -/
instance galDescAlg_finite : Module.Finite K (GalDescAlg K Ω L A ρ') := by
  haveI : Module.Finite K (A → ↥L) := Module.Finite.pi
  exact FiniteDimensional.finiteDimensional_submodule
    (Subalgebra.toSubmodule (galDescSubalgebra K Ω L A fun g a => ρ' g a))

/-- **Étaleness of the generic fibre** (PROVEN — the equivariant
subalgebra is definitionally the `galoisEquivariantAlgebra` of
`Fermat.FLT.KnownIn1980s.EllipticCurves.Flat`, whose étaleness over the
base field is proven there via separable annihilators; the redundant
base change `K ⊗[K] H` transfers along `Algebra.TensorProduct.lid`). -/
theorem galDescAlg_etale [CharZero K] :
    Algebra.Etale K (K ⊗[K] GalDescAlg K Ω L A ρ') := by
  haveI : Algebra.Etale K (GalDescAlg K Ω L A ρ') :=
    galoisEquivariantAlgebra_etale (Ω := Ω) L ρ'
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).symm

/-- Evaluation at a point `a : A`: an `Ω`-point of the twisted constant
group scheme. -/
noncomputable def galDescPoint (a : A) : GalDescAlg K Ω L A ρ' →ₐ[K] Ω :=
  (L.val.comp (Pi.evalAlgHom K (fun _ : A => ↥L) a)).comp
    (galDescSubalgebra K Ω L A fun g a => ρ' g a).val

/-- Evaluation at `a : A` through the redundant base change
`K ⊗[K] H`. -/
noncomputable def galDescPointT (a : A) :
    (K ⊗[K] GalDescAlg K Ω L A ρ') →ₐ[K] Ω :=
  (galDescPoint K Ω L A ρ' a).comp
    (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).toAlgHom

/-- **The points of the twisted constant group scheme** (sorry node —
the Galois-sets side of the correspondence): evaluation is a bijection
from `A` onto the `Ω`-points. Injective because equivariant functions
separate the orbits (indicator functions) and the points of one orbit
(a generator of `Fix(Stab)` moved by every non-stabilizing `g`);
surjective because a `K`-point of `H ≅ ∏ Fix(Stab)` factors through one
component field, whose `|orbit|` embeddings into `Ω` are the
evaluations at the orbit's points (count: `dim_K H = |A|` in the étale
case). PROVEN — the evaluation family is definitionally the
`galoisEquivariantEval` family of
`Fermat.FLT.KnownIn1980s.EllipticCurves.Flat`, whose injectivity
(separating equivariant functions) and surjectivity (kernel comparison
plus `IsSepClosed.lift`) are proven there; in characteristic zero the
algebraic closure is a separable closure, and the redundant base change
only composes with the `lid` equivalence. -/
theorem galDescPointT_bijective [CharZero K] [IsAlgClosure K Ω] :
    Function.Bijective (galDescPointT K Ω L A ρ') := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  have hbr : galDescPoint K Ω L A ρ' = galoisEquivariantEval (Ω := Ω) L ρ' := by
    funext a
    exact AlgHom.ext fun h => (IntermediateField.algebraMap_apply _ _).symm
  have hbij1 : Function.Bijective (galDescPoint K Ω L A ρ') := by
    rw [hbr]
    exact ⟨galoisEquivariantEval_injective L ρ',
      galoisEquivariantEval_surjective L ρ'⟩
  have hcompbij : Function.Bijective
      (fun φ : GalDescAlg K Ω L A ρ' →ₐ[K] Ω =>
        φ.comp (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).toAlgHom) := by
    constructor
    · intro φ ψ hφψ
      apply AlgHom.ext
      intro x
      have h1 := congrArg (fun F : (K ⊗[K] GalDescAlg K Ω L A ρ') →ₐ[K] Ω =>
        F ((Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).symm x)) hφψ
      simpa using h1
    · intro χ
      refine ⟨χ.comp
        (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).symm.toAlgHom, ?_⟩
      apply AlgHom.ext
      intro x
      simp
  exact hcompbij.comp hbij1

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Evaluation turns addition into convolution** (PROVEN — the
convolution of `ev_a` and `ev_b` is evaluation of the pulled-back
addition at `(a, b)`, i.e. `ev_{a+b}`, through the tensor-comparison
isomorphism: `(ev_a ⊗ ev_b) ∘ Δ = ev_{a+b}` transported along the
redundant base change, whose comultiplication acts on `r ⊗ h` through
`Δ h` and the middle four-term exchange). -/
theorem galDescPointT_conv (a b : A) :
    WithConv.toConv (galDescPointT K Ω L A ρ' (a + b)) =
      WithConv.toConv (galDescPointT K Ω L A ρ' a) *
        WithConv.toConv (galDescPointT K Ω L A ρ' b) := by
  classical
  have hptΔ : (Algebra.TensorProduct.lift (galDescPoint K Ω L A ρ' a)
      (galDescPoint K Ω L A ρ' b) fun _ _ => Commute.all _ _).comp
      (galDescComul K Ω L A ρ') = galDescPoint K Ω L A ρ' (a + b) := by
    have h5 : Algebra.TensorProduct.lift (galDescPoint K Ω L A ρ' a)
        (galDescPoint K Ω L A ρ' b) (fun _ _ => Commute.all _ _)
        = L.val.comp (Algebra.TensorProduct.lift
            (galDescEvalL K Ω L (fun g a => ρ' g a) a)
            (galDescEvalL K Ω L (fun g a => ρ' g a) b)
            fun _ _ => Commute.all _ _) :=
      (galDesc_comp_lift L.val (galDescEvalL K Ω L (fun g a => ρ' g a) a)
        (galDescEvalL K Ω L (fun g a => ρ' g a) b)).symm
    rw [h5, AlgHom.comp_assoc, galDesc_lift_evalL_comp_comul]
    exact AlgHom.ext fun h => rfl
  have hmain : galDescPointT K Ω L A ρ' (a + b)
      = (Algebra.TensorProduct.lmul' K (S := Ω)).comp
        ((Algebra.TensorProduct.map (galDescPointT K Ω L A ρ' a)
          (galDescPointT K Ω L A ρ' b)).comp
          (Bialgebra.comulAlgHom K (K ⊗[K] GalDescAlg K Ω L A ρ'))) := by
    apply Algebra.TensorProduct.ext'
    intro r h
    have hcomul : (Bialgebra.comulAlgHom K (K ⊗[K] GalDescAlg K Ω L A ρ'))
        (r ⊗ₜ[K] h)
        = TensorProduct.AlgebraTensorModule.tensorTensorTensorComm K K K K K K
            (GalDescAlg K Ω L A ρ') (GalDescAlg K Ω L A ρ')
            (((1 : K) ⊗ₜ[K] r) ⊗ₜ[K] galDescComul K Ω L A ρ' h) := by
      rw [show (Bialgebra.comulAlgHom K (K ⊗[K] GalDescAlg K Ω L A ρ'))
          (r ⊗ₜ[K] h) = Coalgebra.comul (R := K) (r ⊗ₜ[K] h) from rfl,
        TensorProduct.comul_tmul]
      rfl
    have httc : ∀ u : GalDescAlg K Ω L A ρ' ⊗[K] GalDescAlg K Ω L A ρ',
        (Algebra.TensorProduct.lmul' K (S := Ω))
          ((Algebra.TensorProduct.map (galDescPointT K Ω L A ρ' a)
            (galDescPointT K Ω L A ρ' b))
            (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm K K K K K K
              (GalDescAlg K Ω L A ρ') (GalDescAlg K Ω L A ρ')
              (((1 : K) ⊗ₜ[K] r) ⊗ₜ[K] u)))
        = algebraMap K Ω r *
            Algebra.TensorProduct.lift (galDescPoint K Ω L A ρ' a)
              (galDescPoint K Ω L A ρ' b) (fun _ _ => Commute.all _ _) u := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul p q =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
          Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
          Algebra.TensorProduct.lift_tmul]
        have hpa : galDescPointT K Ω L A ρ' a ((1 : K) ⊗ₜ[K] p)
            = galDescPoint K Ω L A ρ' a p := by
          simp [galDescPointT]
        have hpb : galDescPointT K Ω L A ρ' b (r ⊗ₜ[K] q)
            = algebraMap K Ω r * galDescPoint K Ω L A ρ' b q := by
          simp [galDescPointT, Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
        rw [hpa, hpb]
        ring
      | add u₁ u₂ ih₁ ih₂ =>
        simp only [TensorProduct.tmul_add, map_add, ih₁, ih₂]
        ring
    show galDescPointT K Ω L A ρ' (a + b) (r ⊗ₜ[K] h)
      = (Algebra.TensorProduct.lmul' K (S := Ω))
        ((Algebra.TensorProduct.map (galDescPointT K Ω L A ρ' a)
          (galDescPointT K Ω L A ρ' b))
          ((Bialgebra.comulAlgHom K (K ⊗[K] GalDescAlg K Ω L A ρ'))
            (r ⊗ₜ[K] h)))
    rw [hcomul, httc (galDescComul K Ω L A ρ' h)]
    have hfin := DFunLike.congr_fun hptΔ h
    simp only [AlgHom.coe_comp, Function.comp_apply] at hfin
    rw [hfin]
    simp [galDescPointT, Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
  rw [AlgHom.convMul_def]
  exact congrArg WithConv.toConv hmain

omit [FiniteDimensional K ↥L] [Finite A] in
/-- **Galois equivariance of evaluation** (PROVEN — `σ ∘ ev_a` is
evaluation at `ρ'(σ|_L) a`, by equivariance of the functions and
`AlgEquiv.restrictNormal_commutes`). -/
theorem galDescPointT_equivariant (σ : Ω ≃ₐ[K] Ω) (a : A) :
    (σ.toAlgHom).comp (galDescPointT K Ω L A ρ' a) =
      galDescPointT K Ω L A ρ'
        (ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) a) := by
  have hcore : (σ.toAlgHom).comp (galDescPoint K Ω L A ρ' a) =
      galDescPoint K Ω L A ρ'
        (ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) a) := by
    apply AlgHom.ext
    intro h
    show σ (((h : A → ↥L) a : ↥L) : Ω) =
      (((h : A → ↥L) (ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) a) :
        ↥L) : Ω)
    rw [h.2 (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) a]
    exact (AlgEquiv.restrictNormal_commutes σ ↥L ((h : A → ↥L) a)).symm
  show (σ.toAlgHom.comp (galDescPoint K Ω L A ρ' a)).comp
      (Algebra.TensorProduct.lid K (GalDescAlg K Ω L A ρ')).toAlgHom =
    galDescPointT K Ω L A ρ'
      (ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) a)
  rw [hcore]
  rfl

end GaloisDescentHopf

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The finite-étale package of a discrete Galois module over a
characteristic-zero field** (DECOMPOSED 2026-07-23 into the `galDesc*`
leaves above — the étale-algebras/Galois-sets correspondence, WITH group
structure; the only curve-independent leaf of
the peu-ramifiée decomposition): for a finite abelian group `A` with an
action of `Gal(Ω/K)` that is *discrete* (every point is fixed by the
fixing subgroup of some finite subextension), there is a finite étale
`K`-Hopf algebra whose `Ω`-points are `Gal(Ω/K)`-equivariantly
isomorphic to `A`. Content (Grothendieck's Galois theory of étale
`K`-algebras): `H` is the algebra of equivariant functions `A → Ω`;
evaluation at orbit representatives identifies `H` with
`∏_{orbits O} Fix(Stab O)`, a product of finite subextensions, hence
finite étale of `K`-dimension `|A|`; the comultiplication is the
pullback of the addition `A × A → A` through the analogous descent
identification of `H ⊗[K] H` with the equivariant functions on `A × A`;
the `Ω`-points of `H` are the evaluations at the elements of `A`,
equivariantly by construction. Stated with the redundant base change
`K ⊗[K] H` to match the component shape of
`WeierstrassCurve.TorsionFlatPackage` verbatim.

The assembly below instantiates `H := GalDescAlg K Ω L A ρ'` (the
equivariant-function model above, with its Hopf structure REAL CODE and
its axioms/points the sorried leaves `galDescTensorHom_bijective`,
`galDescComul_coassoc`, `galDescComul_rTensor_counit`,
`galDescComul_lTensor_counit`, `galDesc_mul_antipode_rTensor_comul`,
`galDesc_mul_antipode_lTensor_comul`, `galDescAlg_etale`,
`galDescPointT_bijective`, `galDescPointT_conv`; equivariance of
evaluation is PROVEN) and wraps the evaluation bijection into the
required `AddEquiv`. -/
theorem exists_galoisModulePackage_of_finiteQuotient
    (K : Type) [Field K] [CharZero K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : Type) [AddCommGroup A] [Finite A]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (ρ' : (L ≃ₐ[K] L) →* AddMonoid.End A) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra K H)
      (_ : Module.Finite K H) (_ : Module.Flat K H)
      (_ : Algebra.Etale K (K ⊗[K] H))
      (f : Additive (WithConv ((K ⊗[K] H) →ₐ[K] Ω)) ≃+ A),
      ∀ (σ : Ω ≃ₐ[K] Ω) (φ : (K ⊗[K] H) →ₐ[K] Ω),
        f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
          ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ)
            (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  have hbij := galDescPointT_bijective K Ω L A ρ'
  let e0 : A ≃ ((K ⊗[K] GalDescAlg K Ω L A ρ') →ₐ[K] Ω) :=
    Equiv.ofBijective _ hbij
  have he0 : ∀ a : A, e0 a = galDescPointT K Ω L A ρ' a := fun _ => rfl
  let f : Additive (WithConv ((K ⊗[K] GalDescAlg K Ω L A ρ') →ₐ[K] Ω)) ≃+ A :=
    { toFun := fun x => e0.symm (WithConv.ofConv (Additive.toMul x))
      invFun := fun a => Additive.ofMul (WithConv.toConv (e0 a))
      left_inv := fun x => by
        show Additive.ofMul (WithConv.toConv
          (e0 (e0.symm (WithConv.ofConv (Additive.toMul x))))) = x
        rw [Equiv.apply_symm_apply]
        rfl
      right_inv := fun a => e0.symm_apply_apply a
      map_add' := fun x y => by
        apply e0.injective
        rw [Equiv.apply_symm_apply]
        have h := galDescPointT_conv K Ω L A ρ'
          (e0.symm (WithConv.ofConv (Additive.toMul x)))
          (e0.symm (WithConv.ofConv (Additive.toMul y)))
        have h2 := congrArg WithConv.ofConv h
        rw [WithConv.ofConv_toConv] at h2
        show WithConv.ofConv (Additive.toMul (x + y)) =
          galDescPointT K Ω L A ρ'
            (e0.symm (WithConv.ofConv (Additive.toMul x)) +
              e0.symm (WithConv.ofConv (Additive.toMul y)))
        rw [h2,
          show galDescPointT K Ω L A ρ'
              (e0.symm (WithConv.ofConv (Additive.toMul x))) =
            WithConv.ofConv (Additive.toMul x) from e0.apply_symm_apply _,
          show galDescPointT K Ω L A ρ'
              (e0.symm (WithConv.ofConv (Additive.toMul y))) =
            WithConv.ofConv (Additive.toMul y) from e0.apply_symm_apply _]
        rfl }
  refine ⟨GalDescAlg K Ω L A ρ', inferInstance, inferInstance, inferInstance,
    inferInstance, galDescAlg_etale K Ω L A ρ', f, ?_⟩
  intro σ φ
  show e0.symm (σ.toAlgHom.comp φ) =
    ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) (e0.symm φ)
  apply e0.injective
  rw [Equiv.apply_symm_apply]
  have h := galDescPointT_equivariant K Ω L A ρ' σ (e0.symm φ)
  rw [show galDescPointT K Ω L A ρ' (e0.symm φ) = φ from e0.apply_symm_apply φ] at h
  rw [he0]
  exact h

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The finite-étale package of a Galois module killed by a finite
Galois fixing subgroup** (DERIVED 2026-07-22 from the finite-quotient
core leaf above): a `Gal(Ω/K)`-action killed by `Gal(Ω/L)` descends to
a genuine `Gal(L/K)`-action along the restriction epimorphism
`AlgEquiv.restrictNormalHom` (well-defined by the kernel hypothesis,
multiplicative by surjectivity of restriction), and the finite-quotient
package for the descended action is the required package — its
equivariance transports back through the factorization. -/
theorem exists_galoisModulePackage_of_finiteGalois
    (K : Type) [Field K] [CharZero K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : Type) [AddCommGroup A] [Finite A]
    (ρ : (Ω ≃ₐ[K] Ω) →* AddMonoid.End A)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (hker : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup → ρ σ = 1) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra K H)
      (_ : Module.Finite K H) (_ : Module.Flat K H)
      (_ : Algebra.Etale K (K ⊗[K] H))
      (f : Additive (WithConv ((K ⊗[K] H) →ₐ[K] Ω)) ≃+ A),
      ∀ (σ : Ω ≃ₐ[K] Ω) (φ : (K ⊗[K] H) →ₐ[K] Ω),
        f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
          ρ σ (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  -- restriction to the finite Galois quotient is surjective
  have hsur : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  choose sec hsec using hsur
  -- `ρ` kills every automorphism restricting to the identity of `L`
  have hker' : ∀ η : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L η = 1 → ρ η = 1 := by
    intro η hη
    refine hker η ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      fun x hx => ?_)
    exact ((AlgEquiv.restrictNormal_eq_one_iff L η).mp hη) x hx
  -- `ρ` factors through the restriction
  have hfac : ∀ σ τ : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ =
        AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L τ →
      ρ σ = ρ τ := by
    intro σ τ h
    have h1 : ρ (σ * τ⁻¹) = 1 :=
      hker' _ (by rw [map_mul, map_inv, h, mul_inv_cancel])
    calc ρ σ = ρ ((σ * τ⁻¹) * τ) := by rw [inv_mul_cancel_right]
      _ = ρ (σ * τ⁻¹) * ρ τ := map_mul ρ _ _
      _ = ρ τ := by rw [h1, one_mul]
  -- the descended finite-group action
  let ρ' : (L ≃ₐ[K] L) →* AddMonoid.End A :=
    { toFun := fun g => ρ (sec g)
      map_one' := by
        rw [hfac (sec 1) 1 (by rw [hsec, map_one]), map_one]
      map_mul' := fun g h => by
        rw [hfac (sec (g * h)) (sec g * sec h)
          (by rw [hsec, map_mul, hsec, hsec]), map_mul] }
  have hρ' : ∀ σ : Ω ≃ₐ[K] Ω,
      ρ' (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ) = ρ σ :=
    fun σ => hfac (sec (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L σ))
      σ (hsec _)
  obtain ⟨H, i1, i2, i3, i4, i5, f, hf⟩ :=
    exists_galoisModulePackage_of_finiteQuotient K Ω A L ρ'
  refine ⟨H, i1, i2, i3, i4, i5, f, fun σ φ => ?_⟩
  rw [hf σ φ, hρ']

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The finite-étale package of a discrete Galois module** (DERIVED
2026-07-22 from the finite-Galois core leaf above): the discreteness
hypothesis is upgraded to a SINGLE finite Galois subextension through
which the whole action factors — the compositum of the pointwise
fields `L_a` is finite-dimensional (`A` is finite), and its normal
closure is finite Galois over `K` (separability is automatic in
characteristic zero); an automorphism fixing it fixes every `L_a`,
hence acts trivially on `A`. -/
theorem exists_galoisModulePackage
    (K : Type) [Field K] [CharZero K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : Type) [AddCommGroup A] [Finite A]
    (ρ : (Ω ≃ₐ[K] Ω) →* AddMonoid.End A)
    (hdisc : ∀ a : A, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup → ρ σ a = a) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra K H)
      (_ : Module.Finite K H) (_ : Module.Flat K H)
      (_ : Algebra.Etale K (K ⊗[K] H))
      (f : Additive (WithConv ((K ⊗[K] H) →ₐ[K] Ω)) ≃+ A),
      ∀ (σ : Ω ≃ₐ[K] Ω) (φ : (K ⊗[K] H) →ₐ[K] Ω),
        f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
          ρ σ (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  -- choose the pointwise fixing fields
  choose La hLafd hLafix using hdisc
  haveI : ∀ a : A, FiniteDimensional K (La a) := hLafd
  -- their compositum is finite-dimensional since `A` is finite
  haveI hL0 : FiniteDimensional K
      (⨆ a : A, La a : IntermediateField K Ω) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  -- its normal closure is finite Galois over `K` (char 0)
  have hker : ∀ σ : Ω ≃ₐ[K] Ω,
      σ ∈ (IntermediateField.normalClosure K
        (⨆ a : A, La a : IntermediateField K Ω) Ω).fixingSubgroup → ρ σ = 1 := by
    intro σ hσ
    refine AddMonoidHom.ext fun a => ?_
    have hσa : σ ∈ (La a).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
      exact ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ) x
        ((IntermediateField.le_normalClosure _)
          ((le_iSup (fun a : A => (La a : IntermediateField K Ω)) a) hx))
    exact hLafix a σ hσa
  exact exists_galoisModulePackage_of_finiteGalois K Ω A ρ
    (IntermediateField.normalClosure K
      (⨆ a : A, La a : IntermediateField K Ω) Ω) hker

open TensorProduct in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The global generic-fibre torsion package** (DERIVED 2026-07-22
from the discrete-Galois-module package `exists_galoisModulePackage`):
over `R = K = ℚ` the `p`-torsion of any elliptic curve is the group of
`ℚ̄`-points of a finite étale `ℚ`-Hopf algebra, globally
Galois-equivariantly — no local input and no flatness content
(`ℚ` is a field). The glue proven here: the `p`-torsion is finite
(`n_torsion_finite`), the Galois action on it is by additive
automorphisms (the ambient `DistribMulAction` restricted to the torsion
subgroup), and the action is discrete (a torsion point is fixed by the
fixing subgroup of the finite extension generated by its two
coordinates — the same argument as the continuity of `galoisRep`). -/
theorem WeierstrassCurve.torsionFlatPackage_global
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.TorsionFlatPackage ℚ ℚ E p (AlgebraicClosure ℚ) := by
  classical
  -- the `p`-torsion subgroup is finite
  haveI hTfin : Finite (AddSubgroup.torsionBy
      (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) := by
    haveI hfin' : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
      WeierstrassCurve.n_torsion_finite _ (Fact.out : p.Prime).pos
    exact Finite.of_equiv _
      { toFun := fun (x : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) =>
          (⟨x.1, by
            have h1 := x.2
            rw [Submodule.mem_torsionBy_iff] at h1
            show ((p : ℕ) : ℤ) • x.1 = 0
            exact_mod_cast h1⟩ :
            AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ))
        invFun := fun x => ⟨x.1, by
          rw [Submodule.mem_torsionBy_iff]
          have h0 : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
          exact_mod_cast h0⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- stability of the torsion subgroup under the ambient Galois action
  have hmem : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (t : (E⁄(AlgebraicClosure ℚ)).Point),
      t ∈ AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ) →
      σ • t ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ) := by
    intro σ t ht
    have h0 : ((p : ℕ) : ℤ) • t = 0 := ht
    show ((p : ℕ) : ℤ) • (σ • t) = 0
    have h1 := map_zsmul (DistribMulAction.toAddMonoidEnd
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ((E⁄(AlgebraicClosure ℚ)).Point) σ) ((p : ℕ) : ℤ) t
    rw [h0, map_zero] at h1
    exact h1.symm
  -- the Galois action on the torsion subgroup, as a monoid hom into
  -- additive endomorphisms
  let ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      AddMonoid.End (AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) :=
    { toFun := fun σ =>
        { toFun := fun t => ⟨σ • t.1, hmem σ t.1 t.2⟩
          map_zero' := Subtype.ext (smul_zero σ)
          map_add' := fun s t => Subtype.ext (smul_add σ s.1 t.1) }
      map_one' := AddMonoidHom.ext fun t => Subtype.ext (one_smul _ t.1)
      map_mul' := fun σ τ =>
        AddMonoidHom.ext fun t => Subtype.ext (mul_smul σ τ t.1) }
  -- discreteness: a torsion point is fixed by the fixing subgroup of the
  -- finite extension generated by its coordinates
  have hdisc : ∀ t : AddSubgroup.torsionBy
      (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ L.fixingSubgroup → ρ σ t = t := by
    rintro ⟨t, ht⟩
    cases t with
    | zero =>
      exact ⟨⊥, inferInstance, fun σ _ => Subtype.ext rfl⟩
    | some x y hxy =>
      refine ⟨IntermediateField.adjoin ℚ {x, y},
        IntermediateField.finiteDimensional_adjoin fun z _ =>
          (Algebra.IsAlgebraic.isAlgebraic z).isIntegral, fun σ hσ => ?_⟩
      have hx : (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) x = x :=
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ) x
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert x {y}))
      have hy : (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) y = y :=
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ) y
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem x rfl))
      refine Subtype.ext ?_
      show WeierstrassCurve.Affine.Point.map (W' := E)
        (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) (.some x y hxy) =
          .some x y hxy
      rw [WeierstrassCurve.Affine.Point.map_some]
      simp only [hx, hy]
  obtain ⟨H, i1, i2, i3, i4, i5, f, hf⟩ :=
    exists_galoisModulePackage ℚ (AlgebraicClosure ℚ)
      (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ))
      ρ hdisc
  exact ⟨H, i1, i2, i3, i4, i5, f,
    fun σ φ => congrArg Subtype.val (hf σ φ)⟩

/-! #### The explicit Kummer Hopf algebra `∏_{i<p} R[x]/(xᵖ − uⁱ)`

For a commutative ring `R` and a unit `u : Rˣ`, the Kummer group scheme
attached to `u` (the extension of `ℤ/p` by `μ_p` classified by `u`) has
Hopf algebra of functions `∏_{i<p} R[x]/(xᵖ − uⁱ)`: its points over an
`R`-algebra `S` are the pairs `(i, t)` with `tᵖ = uⁱ` (`i` selects the
factor supporting the point, `t` is the value of `x` there), multiplying
by `(i,s)·(j,t) = (i+j−pε, s·t·u^{−ε})` (`ε` the carry of `i+j` past
`p`), with identity `(0,1)` and inverse `(i,t)⁻¹ = (−i, u^{pε_i−i}·t⁻¹)`.
The structure maps are assembled componentwise: maps INTO the product
via `AlgHom.pi`, out of each `AdjoinRoot` component via
`AdjoinRoot.liftAlgHom`, and the tensor square is distributed into
componentwise tensors by `Algebra.TensorProduct.piRight`. The DATA is
constructed here; the Hopf-algebra AXIOMS (coassociativity, counit,
antipode) are the sorried `kummer*` leaves below, consumed by the
`Bialgebra.ofAlgHom`/`HopfAlgebra.ofAlgHom` instances. -/

section KummerHopf

open Polynomial

variable (R : Type) [CommRing R] (p : ℕ) (u : Rˣ)

/-- The `i`-th component `R[x]/(xᵖ − u^{i.val})` of the Kummer Hopf
algebra: the coordinate ring of the locus of points `(i, t)`,
`tᵖ = uⁱ`. -/
abbrev KummerComponent (i : ZMod p) : Type :=
  AdjoinRoot ((Polynomial.X : Polynomial R) ^ p - Polynomial.C ((u : R) ^ i.val))

/-- The Kummer Hopf-algebra carrier `∏_{i<p} R[x]/(xᵖ − uⁱ)`. -/
abbrev KummerAlg : Type := ∀ i : ZMod p, KummerComponent R p u i

/-- The adjoined root `x` of the `i`-th Kummer component. -/
noncomputable def kummerRoot (i : ZMod p) : KummerComponent R p u i :=
  AdjoinRoot.root _

/-- The defining relation of the `i`-th Kummer component:
`xᵖ = u^{i.val}` (PROVEN). -/
theorem kummerRoot_pow_p (i : ZMod p) :
    kummerRoot R p u i ^ p =
      algebraMap R (KummerComponent R p u i) ((u : R) ^ i.val) := by
  have h := AdjoinRoot.eval₂_root
    ((Polynomial.X : Polynomial R) ^ p - Polynomial.C ((u : R) ^ i.val))
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

instance kummerComponent_free [NeZero p] (i : ZMod p) :
    Module.Free R (KummerComponent R p u i) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis'
    (Polynomial.monic_X_pow_sub_C _ (NeZero.ne p))).basis

instance kummerComponent_finite [NeZero p] (i : ZMod p) :
    Module.Finite R (KummerComponent R p u i) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis'
    (Polynomial.monic_X_pow_sub_C _ (NeZero.ne p))).basis

/-- **The Kummer counit** — evaluation at the identity point `(0, 1)`:
project to the `0`-th component and send the root to `1`. -/
noncomputable def kummerCounit [NeZero p] : KummerAlg R p u →ₐ[R] R :=
  (AdjoinRoot.liftAlgHom _ (Algebra.ofId R R) 1 (by
      simp [ZMod.val_zero])).comp
    (Pi.evalAlgHom R (KummerComponent R p u) (0 : ZMod p))

/-- The image of the root under the antipode: on points the inverse of
`(i, t)` is `(−i, c·t⁻¹)` with `c = u^{ε_i}` (`ε_i = 0` for `i = 0`,
else `1`), and `t⁻¹ = u^{−i}·t^{p−1}`; so the pullback of the root of
the `(−i)`-th component is `u^{ε_i}·u^{−i.val}·xᵖ⁻¹` in the `i`-th
component. -/
noncomputable def kummerAntipodeRoot (i : ZMod p) : KummerComponent R p u i :=
  algebraMap R (KummerComponent R p u i)
      ((u : R) ^ (if i = 0 then 0 else 1) * ((u⁻¹ : Rˣ) : R) ^ i.val) *
    kummerRoot R p u i ^ (p - 1)

/-- The antipode root satisfies the defining relation of the `(−i)`-th
component (PROVEN — the units-exponent computation
`(u^{ε}·u^{−v})ᵖ·u^{v(p−1)} = u^{(−i).val}`, `v = i.val`). -/
theorem kummerAntipodeRoot_relation [NeZero p] (i : ZMod p) :
    ((Polynomial.X : Polynomial R) ^ p -
      Polynomial.C ((u : R) ^ (-i).val)).eval₂
      (Algebra.ofId R (KummerComponent R p u i)) (kummerAntipodeRoot R p u i) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero]
  show kummerAntipodeRoot R p u i ^ p =
    algebraMap R (KummerComponent R p u i) ((u : R) ^ (-i).val)
  rw [kummerAntipodeRoot, mul_pow, ← pow_mul, pow_mul', kummerRoot_pow_p]
  rw [← map_pow, ← map_pow, ← map_mul]
  congr 1
  -- the `Rˣ`-level exponent identity, transported to `R`
  have hU : ((u ^ (if i = 0 then 0 else 1) * u⁻¹ ^ i.val) ^ p *
      (u ^ i.val) ^ (p - 1) : Rˣ) = u ^ (-i).val := by
    simp only [inv_pow, mul_pow]
    simp only [← zpow_natCast, ← zpow_neg, ← zpow_mul, ← zpow_add]
    congr 1
    have hvlt : i.val < p := ZMod.val_lt i
    have h1 : (1 : ℕ) ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    have hneg := ZMod.neg_val i
    by_cases hi : i = 0
    · simp only [hi, if_pos, ZMod.val_zero] at hneg ⊢
      simp
    · rw [if_neg hi] at hneg ⊢
      rw [hneg]
      push_cast [Nat.cast_sub hvlt.le, Nat.cast_sub h1]
      ring
  have hR := congrArg (Units.val) hU
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hR

/-- The `i`-th component of the antipode: the algebra map
`R[x]/(xᵖ − u^{(−i).val}) → R[x]/(xᵖ − u^{i.val})` classifying the
point-inversion `(i,t) ↦ (−i, u^{ε_i}·t⁻¹)`. -/
noncomputable def kummerAntipodeComponent [NeZero p] (i : ZMod p) :
    KummerComponent R p u (-i) →ₐ[R] KummerComponent R p u i :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R (KummerComponent R p u i))
    (kummerAntipodeRoot R p u i) (kummerAntipodeRoot_relation R p u i)

/-- **The Kummer antipode** — the pullback of point-inversion,
componentwise (`S(h)ᵢ = Sᵢ(h₋ᵢ)`). -/
noncomputable def kummerAntipode [NeZero p] : KummerAlg R p u →ₐ[R] KummerAlg R p u :=
  AlgHom.pi fun i => (kummerAntipodeComponent R p u i).comp
    (Pi.evalAlgHom R (KummerComponent R p u) (-i))

/-- The image of the root under comultiplication in the `(i,j)`-tensor
block: the pullback of the root of the `(i+j)`-th component along the
multiplication `(i,s)·(j,t) = (i+j−pε, s·t·u^{−ε})` is
`(x ⊗ x)·u^{−ε}`, `ε` the carry. -/
noncomputable def kummerComulRoot (i j : ZMod p) :
    TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j) :=
  TensorProduct.tmul R (kummerRoot R p u i) (kummerRoot R p u j) *
    algebraMap R _ (((u⁻¹ : Rˣ) : R) ^ (if i.val + j.val < p then 0 else 1))

/-- The comultiplication root satisfies the defining relation of the
`(i+j)`-th component (PROVEN — `(u^{v_i+v_j})·u^{−pε} = u^{(i+j).val}`
by the `ZMod.val_add` carry arithmetic). -/
theorem kummerComulRoot_relation [NeZero p] (i j : ZMod p) :
    ((Polynomial.X : Polynomial R) ^ p -
      Polynomial.C ((u : R) ^ (i + j).val)).eval₂
      (Algebra.ofId R (TensorProduct R (KummerComponent R p u i)
        (KummerComponent R p u j)))
      (kummerComulRoot R p u i j) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero]
  show kummerComulRoot R p u i j ^ p = algebraMap R _ ((u : R) ^ (i + j).val)
  rw [kummerComulRoot, mul_pow, ← map_pow, Algebra.TensorProduct.tmul_pow,
    kummerRoot_pow_p, kummerRoot_pow_p]
  have htmul : TensorProduct.tmul R
      (algebraMap R (KummerComponent R p u i) ((u : R) ^ i.val))
      (algebraMap R (KummerComponent R p u j) ((u : R) ^ j.val)) =
      algebraMap R (TensorProduct R (KummerComponent R p u i)
        (KummerComponent R p u j)) ((u : R) ^ i.val * (u : R) ^ j.val) := by
    have hsplit : TensorProduct.tmul R
        (algebraMap R (KummerComponent R p u i) ((u : R) ^ i.val))
        (algebraMap R (KummerComponent R p u j) ((u : R) ^ j.val)) =
        (TensorProduct.tmul R
          (algebraMap R (KummerComponent R p u i) ((u : R) ^ i.val)) 1) *
        (TensorProduct.tmul R 1
          (algebraMap R (KummerComponent R p u j) ((u : R) ^ j.val))) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul]
  rw [htmul, ← map_mul]
  congr 1
  -- the `Rˣ`-level carry identity, transported to `R`
  have hU : ((u ^ i.val * u ^ j.val) *
      (u⁻¹ ^ (if i.val + j.val < p then 0 else 1)) ^ p : Rˣ) = u ^ (i + j).val := by
    simp only [inv_pow]
    rw [← pow_add, ← zpow_natCast u (i.val + j.val), ← zpow_natCast u ((i + j).val),
      ← zpow_natCast (u ^ ((if i.val + j.val < p then 0 else 1) : ℕ)),
      ← zpow_natCast u (if i.val + j.val < p then 0 else 1), ← zpow_mul, ← zpow_neg,
      ← zpow_add]
    congr 1
    have hadd := ZMod.val_add i j
    have hilt : i.val < p := ZMod.val_lt i
    have hjlt : j.val < p := ZMod.val_lt j
    by_cases hlt : i.val + j.val < p
    · rw [if_pos hlt]
      rw [Nat.mod_eq_of_lt hlt] at hadd
      omega
    · rw [if_neg hlt]
      have hsub : (i.val + j.val) % p = i.val + j.val - p := by
        rw [Nat.mod_eq_sub_mod (le_of_not_gt hlt), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hadd
      omega
  have hR := congrArg (Units.val) hU
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hR

/-- The `(i,j)`-component of the comultiplication: the algebra map
`R[x]/(xᵖ − u^{(i+j).val}) → A_i ⊗ A_j` classifying the group law. -/
noncomputable def kummerComulComponent [NeZero p] (i j : ZMod p) :
    KummerComponent R p u (i + j) →ₐ[R]
      TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j) :=
  AdjoinRoot.liftAlgHom _
    (Algebra.ofId R (TensorProduct R (KummerComponent R p u i)
      (KummerComponent R p u j)))
    (kummerComulRoot R p u i j) (kummerComulRoot_relation R p u i j)

/-- The tensor square of the Kummer algebra distributed into
componentwise tensor blocks (PROVEN — two applications of
`Algebra.TensorProduct.piRight` and commutativity of the tensor
product). -/
noncomputable def kummerTensorEquiv [NeZero p] :
    TensorProduct R (KummerAlg R p u) (KummerAlg R p u) ≃ₐ[R]
      ∀ j : ZMod p, ∀ i : ZMod p,
        TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j) :=
  (Algebra.TensorProduct.piRight R R (KummerAlg R p u)
    (KummerComponent R p u)).trans
    (AlgEquiv.piCongrRight fun j =>
      (Algebra.TensorProduct.comm R (KummerAlg R p u)
        (KummerComponent R p u j)).trans
        ((Algebra.TensorProduct.piRight R R (KummerComponent R p u j)
          (KummerComponent R p u)).trans
          (AlgEquiv.piCongrRight fun i =>
            Algebra.TensorProduct.comm R (KummerComponent R p u j)
              (KummerComponent R p u i))))

/-- **The Kummer comultiplication** — the pullback of the group law,
assembled blockwise (`Δ(h)_{(i,j)} = Δ_{ij}(h_{i+j})`) and transported
through the tensor-block distribution `kummerTensorEquiv`. -/
noncomputable def kummerComul [NeZero p] :
    KummerAlg R p u →ₐ[R] TensorProduct R (KummerAlg R p u) (KummerAlg R p u) :=
  ((kummerTensorEquiv R p u).symm.toAlgHom).comp
    (AlgHom.pi fun j => AlgHom.pi fun i =>
      (kummerComulComponent R p u i j).comp
        (Pi.evalAlgHom R (KummerComponent R p u) (i + j)))

/-- Transport between Kummer components along an index equality
(the components at propositionally equal indices, e.g. `0 + c` and `c`,
are equal but not definitionally so). -/
noncomputable def kummerCast {i i' : ZMod p} (h : i = i') :
    KummerComponent R p u i →ₐ[R] KummerComponent R p u i' :=
  h ▸ AlgHom.id R (KummerComponent R p u i)

/-- The cast transport fixes the adjoined root (PROVEN by `subst`). -/
theorem kummerCast_root {i i' : ZMod p} (h : i = i') :
    kummerCast R p u h (kummerRoot R p u i) = kummerRoot R p u i' := by
  subst h
  rfl

/-- Evaluating a one-component element at a propositionally equal index
(PROVEN by `subst`): `(Pi.single c a) i' = kummerCast h a` whenever
`c = i'`. -/
theorem kummerSingle_apply_of_eq {c i' : ZMod p} (h : c = i')
    (a : KummerComponent R p u c) :
    (Pi.single c a : KummerAlg R p u) i' = kummerCast R p u h a := by
  subst h
  rw [Pi.single_eq_same]
  rfl

/-- The counit kills the components away from the identity component
(PROVEN): `ε(single i a) = 0` for `i ≠ 0`. -/
theorem kummerCounit_single_of_ne [NeZero p] {i : ZMod p} (hi : i ≠ 0)
    (a : KummerComponent R p u i) :
    kummerCounit R p u (Pi.single i a) = 0 := by
  simp only [kummerCounit, AlgHom.comp_apply]
  rw [show (Pi.evalAlgHom R (KummerComponent R p u) (0 : ZMod p))
      (Pi.single i a) = (Pi.single i a : KummerAlg R p u) 0 from rfl,
    Pi.single_eq_of_ne (Ne.symm hi), map_zero]

/-- The counit sends the identity-component unit to `1` (PROVEN). -/
theorem kummerCounit_single_zero_one [NeZero p] :
    kummerCounit R p u (Pi.single (0 : ZMod p) 1) = 1 := by
  simp only [kummerCounit, AlgHom.comp_apply]
  rw [show (Pi.evalAlgHom R (KummerComponent R p u) (0 : ZMod p))
      (Pi.single (0 : ZMod p) 1) =
      (Pi.single (0 : ZMod p) 1 : KummerAlg R p u) 0 from rfl,
    Pi.single_eq_same, map_one]

/-- The counit sends the identity-component root to `1` (PROVEN —
evaluation of the identity point `(0, 1)` at the coordinate `x`). -/
theorem kummerCounit_single_zero_root [NeZero p] :
    kummerCounit R p u (Pi.single (0 : ZMod p) (kummerRoot R p u 0)) = 1 := by
  simp only [kummerCounit, AlgHom.comp_apply]
  rw [show (Pi.evalAlgHom R (KummerComponent R p u) (0 : ZMod p))
      (Pi.single (0 : ZMod p) (kummerRoot R p u 0)) =
      (Pi.single (0 : ZMod p) (kummerRoot R p u 0) : KummerAlg R p u) 0 from rfl,
    Pi.single_eq_same]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- One-component polynomials in the root, rewritten through the
one-component idempotent (PROVEN): `single i (q(x)) = eᵢ · q(single i x)`
— the unit discrepancy of the non-unital inclusion is absorbed by the
idempotent `eᵢ = single i 1`. -/
theorem kummerSingle_aeval (i : ZMod p) (q : Polynomial R) :
    (Pi.single i (Polynomial.aeval (kummerRoot R p u i) q) : KummerAlg R p u) =
      Pi.single i 1 *
        Polynomial.aeval (Pi.single i (kummerRoot R p u i) : KummerAlg R p u) q := by
  induction q using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, Pi.single_add, hf, hg, map_add, mul_add]
  | monomial k r =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.single_eq_same, one_mul]
      rfl
    · simp only [Pi.mul_apply, Pi.single_eq_of_ne hj, zero_mul]

/-- **Extensionality for algebra maps out of the Kummer algebra**
(PROVEN): two `R`-algebra maps out of `∏_{i<p} R[x]/(xᵖ − uⁱ)` agree
as soon as they agree on the component idempotents `single i 1` and
the component roots `single i x`. Every element decomposes as
`h = ∑ᵢ eᵢ·h` with `eᵢ·h = single i (h i)` a one-component polynomial
in the root, which `kummerSingle_aeval` rewrites into the generators. -/
theorem kummerAlg_algHom_ext [NeZero p] {B : Type} [CommRing B] [Algebra R B]
    {f g : KummerAlg R p u →ₐ[R] B}
    (hone : ∀ i, f (Pi.single i 1) = g (Pi.single i 1))
    (hroot : ∀ i, f (Pi.single i (kummerRoot R p u i)) =
      g (Pi.single i (kummerRoot R p u i))) :
    f = g := by
  classical
  apply AlgHom.ext
  intro h
  -- decompose into one-component pieces
  have hdec : h = ∑ i : ZMod p, Pi.single i (h i) :=
    (Finset.univ_sum_single h).symm
  rw [hdec, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- each piece is a polynomial in the root
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective (h i)
  have hq' : Polynomial.aeval (kummerRoot R p u i) q = h i :=
    (AdjoinRoot.aeval_eq q).trans hq
  rw [← hq', kummerSingle_aeval, map_mul, map_mul,
    hone i, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
    hroot i]

/-- The tensor-block distribution on a tensor of one-component
elements (PROVEN — chase the `piRight`/`comm` chain on pure
tensors). -/
theorem kummerTensorEquiv_single [NeZero p] (i j : ZMod p)
    (x : KummerComponent R p u i) (y : KummerComponent R p u j) :
    kummerTensorEquiv R p u
        (TensorProduct.tmul R (Pi.single i x) (Pi.single j y)) =
      Pi.single j (Pi.single i (TensorProduct.tmul R x y)) := by
  classical
  rw [kummerTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.piRight_tmul]
  have h1 : (fun j' => TensorProduct.tmul R
      (Pi.single i x : KummerAlg R p u)
      ((Pi.single j y : KummerAlg R p u) j')) =
      Pi.single j (TensorProduct.tmul R
        (Pi.single i x : KummerAlg R p u) y) := by
    funext j'
    by_cases hj : j' = j
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj,
        TensorProduct.tmul_zero]
  rw [h1]
  funext j'
  rw [AlgEquiv.piCongrRight_apply]
  by_cases hj : j' = j
  · subst hj
    rw [Pi.single_eq_same, Pi.single_eq_same]
    rw [AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
      AlgEquiv.trans_apply, Algebra.TensorProduct.piRight_tmul]
    have h2 : (fun i' => TensorProduct.tmul R y
        ((Pi.single i x : KummerAlg R p u) i')) =
        Pi.single i (TensorProduct.tmul R y x) := by
      funext i'
      by_cases hi : i' = i
      · subst hi
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi,
          TensorProduct.tmul_zero]
    rw [h2]
    funext i'
    rw [AlgEquiv.piCongrRight_apply]
    by_cases hi : i' = i
    · subst hi
      rw [Pi.single_eq_same, Pi.single_eq_same,
        Algebra.TensorProduct.comm_tmul]
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, map_zero]
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]

/-- The inverse tensor-block distribution on doubly-one-component
elements (PROVEN from the forward computation by injectivity and
linearity). -/
theorem kummerTensorEquiv_symm_single [NeZero p] (i j : ZMod p)
    (T : TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j)) :
    (kummerTensorEquiv R p u).symm (Pi.single j (Pi.single i T)) =
      (TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) j)) T := by
  induction T using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, Pi.single_zero, Pi.single_zero, map_zero]
  | tmul x y =>
    apply (kummerTensorEquiv R p u).injective
    rw [AlgEquiv.apply_symm_apply, TensorProduct.map_tmul]
    exact (kummerTensorEquiv_single R p u i j x y).symm
  | add s t hs ht =>
    rw [map_add, Pi.single_add, Pi.single_add, map_add, hs, ht]

/-- The comultiplication, expanded as the double sum of its
tensor-block components (PROVEN): `Δ(h) = ∑_{i,j} (ιᵢ ⊗ ιⱼ)(Δᵢⱼ(h_{i+j}))`
with `ιᵢ` the one-component inclusions. -/
theorem kummerComul_apply_eq_sum [NeZero p] (h : KummerAlg R p u) :
    kummerComul R p u h =
      ∑ j : ZMod p, ∑ i : ZMod p,
        (TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
          (LinearMap.single R (KummerComponent R p u) j))
        (kummerComulComponent R p u i j (h (i + j))) := by
  classical
  rw [kummerComul, AlgHom.comp_apply]
  have hD : (AlgHom.pi fun j => AlgHom.pi fun i =>
      (kummerComulComponent R p u i j).comp
        (Pi.evalAlgHom R (KummerComponent R p u) (i + j))) h =
      ∑ j : ZMod p, ∑ i : ZMod p, Pi.single j (Pi.single i
        (kummerComulComponent R p u i j (h (i + j)))) := by
    funext j₀
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j₀ (fun j _ hj => Finset.sum_eq_zero fun i _ => by
        rw [Pi.single_eq_of_ne (Ne.symm hj)])
      (fun hj => absurd (Finset.mem_univ j₀) hj)]
    simp only [Pi.single_eq_same]
    exact (Finset.univ_sum_single _).symm
  rw [hD, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact kummerTensorEquiv_symm_single R p u i j _

/-- The comultiplication block on the root (PROVEN — `liftAlgHom` on
the adjoined root). -/
theorem kummerComulComponent_root [NeZero p] (i j : ZMod p) :
    kummerComulComponent R p u i j (kummerRoot R p u (i + j)) =
      kummerComulRoot R p u i j :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The comultiplication root has no carry when the left index is `0`
(PROVEN). -/
theorem kummerComulRoot_zero_left [NeZero p] (c : ZMod p) :
    kummerComulRoot R p u 0 c =
      TensorProduct.tmul R (kummerRoot R p u 0) (kummerRoot R p u c) := by
  rw [kummerComulRoot, if_pos (show (0 : ZMod p).val + c.val < p by
    rw [ZMod.val_zero, zero_add]; exact ZMod.val_lt c), pow_zero, map_one,
    mul_one]

/-- The comultiplication root has no carry when the right index is `0`
(PROVEN). -/
theorem kummerComulRoot_zero_right [NeZero p] (c : ZMod p) :
    kummerComulRoot R p u c 0 =
      TensorProduct.tmul R (kummerRoot R p u c) (kummerRoot R p u 0) := by
  rw [kummerComulRoot, if_pos (show c.val + (0 : ZMod p).val < p by
    rw [ZMod.val_zero, add_zero]; exact ZMod.val_lt c), pow_zero, map_one,
    mul_one]

/-- Applying `ε ⊗ id` kills the tensor blocks whose left index is not
`0` (PROVEN by tensor induction). -/
theorem kummer_rTensor_kill [NeZero p] {i : ZMod p} (hi : i ≠ 0) (j : ZMod p)
    (T : TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j)) :
    (Algebra.TensorProduct.map (kummerCounit R p u)
      (AlgHom.id R (KummerAlg R p u)))
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) j)) T) = 0 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) i) x =
        Pi.single i x from rfl,
      kummerCounit_single_of_ne R p u hi, TensorProduct.zero_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]

/-- Applying `id ⊗ ε` kills the tensor blocks whose right index is not
`0` (PROVEN by tensor induction). -/
theorem kummer_lTensor_kill [NeZero p] (i : ZMod p) {j : ZMod p} (hj : j ≠ 0)
    (T : TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j)) :
    (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
      (kummerCounit R p u))
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) j)) T) = 0 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) j) y =
        Pi.single j y from rfl,
      kummerCounit_single_of_ne R p u hj, TensorProduct.tmul_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]

/-- The defining relation between values and carries of `ZMod`
addition (PROVEN): `a.val + b.val = (a+b).val + p·carry(a,b)`. -/
theorem kummer_val_add_carry [NeZero p] (a b : ZMod p) :
    a.val + b.val = (a + b).val +
      p * (if a.val + b.val < p then 0 else 1) := by
  rw [ZMod.val_add]
  by_cases h : a.val + b.val < p
  · rw [if_pos h, Nat.mod_eq_of_lt h, Nat.mul_zero, Nat.add_zero]
  · rw [if_neg h, Nat.mul_one]
    have ha : a.val < p := ZMod.val_lt a
    have hb : b.val < p := ZMod.val_lt b
    rw [Nat.mod_eq_sub_mod (le_of_not_gt h), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The carry cocycle identity** (PROVEN — both sides count the
`p`-overflows of `α.val + β.val + γ.val`): the coassociativity of the
Kummer comultiplication reduces to this. -/
theorem kummer_carry_assoc [NeZero p] (α β γ : ZMod p) :
    ((if (α + β).val + γ.val < p then 0 else 1) +
      (if α.val + β.val < p then 0 else 1) : ℕ) =
    (if α.val + (β + γ).val < p then 0 else 1) +
      (if β.val + γ.val < p then 0 else 1) := by
  have h1 := kummer_val_add_carry p (α + β) γ
  have h2 := kummer_val_add_carry p α β
  have h3 := kummer_val_add_carry p α (β + γ)
  have h4 := kummer_val_add_carry p β γ
  have hassoc : (α + β + γ).val = (α + (β + γ)).val := by rw [add_assoc]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  -- combine the four relations and cancel `p`
  refine Nat.eq_of_mul_eq_mul_left hp ?_
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- The comultiplication on a one-component element, collapsed to the
single sum over the second index (PROVEN — the inner sum survives only
at `i = c − j`, where the component evaluation is the `kummerCast`
transport). -/
theorem kummerComul_single [NeZero p] (c : ZMod p)
    (a : KummerComponent R p u c) :
    kummerComul R p u (Pi.single c a) =
      ∑ j : ZMod p,
        (TensorProduct.map (LinearMap.single R (KummerComponent R p u) (c - j))
          (LinearMap.single R (KummerComponent R p u) j))
        (kummerComulComponent R p u (c - j) j
          (kummerCast R p u (sub_add_cancel c j).symm a)) := by
  classical
  rw [kummerComul_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_eq_single (c - j) (fun i _ hi => ?_)
    (fun hmem => absurd (Finset.mem_univ _) hmem)).trans ?_
  · by_cases hij : i + j = c
    · exact absurd (eq_sub_of_add_eq hij) hi
    · rw [Pi.single_eq_of_ne hij, map_zero, map_zero]
  · rw [kummerSingle_apply_of_eq R p u (sub_add_cancel c j).symm]

/-- The comultiplication on a one-component unit, fully evaluated
(PROVEN): `Δ(e_c) = ∑ⱼ e_{c−j} ⊗ e_j`. -/
theorem kummerComul_single_one_eq [NeZero p] (c : ZMod p) :
    kummerComul R p u (Pi.single c 1) =
      ∑ j : ZMod p, TensorProduct.tmul R
        (Pi.single (c - j) 1 : KummerAlg R p u)
        (Pi.single j 1 : KummerAlg R p u) := by
  rw [kummerComul_single]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_one, map_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul]
  rfl

/-- The comultiplication on a one-component root, fully evaluated
(PROVEN): `Δ(single_c x) = ∑ⱼ u^{−carry} • (single_{c−j} x ⊗ single_j x)`. -/
theorem kummerComul_single_root_eq [NeZero p] (c : ZMod p) :
    kummerComul R p u (Pi.single c (kummerRoot R p u c)) =
      ∑ j : ZMod p,
        (((u⁻¹ : Rˣ) : R) ^ (if (c - j).val + j.val < p then 0 else 1)) •
        TensorProduct.tmul R
          (Pi.single (c - j) (kummerRoot R p u (c - j)) : KummerAlg R p u)
          (Pi.single j (kummerRoot R p u j) : KummerAlg R p u) := by
  rw [kummerComul_single]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kummerCast_root, kummerComulComponent_root, kummerComulRoot, mul_comm,
    ← Algebra.smul_def, map_smul, TensorProduct.map_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Coassociativity of the Kummer comultiplication** (PROVEN
2026-07-22 — pure algebra on the explicit model: on generators both
sides expand to triple sums of one-component blocks; the reindexing
`(j, j') ↦ (j' + j, j)` matches them up, with the scalar bookkeeping
reducing to the carry cocycle identity `kummer_carry_assoc`). -/
theorem kummerComul_coassoc [NeZero p] :
    (Algebra.TensorProduct.assoc R R R (KummerAlg R p u) (KummerAlg R p u)
        (KummerAlg R p u)).toAlgHom.comp
      ((Algebra.TensorProduct.map (kummerComul R p u)
        (AlgHom.id R (KummerAlg R p u))).comp (kummerComul R p u))
      = (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
        (kummerComul R p u)).comp (kummerComul R p u) := by
  classical
  refine kummerAlg_algHom_ext R p u
    (B := TensorProduct R (KummerAlg R p u)
      (TensorProduct R (KummerAlg R p u) (KummerAlg R p u)))
    (fun c => ?_) (fun c => ?_)
  · -- generator `e_c`
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      kummerComul_single_one_eq, map_sum, map_sum, map_sum]
    have hL : ∀ j : ZMod p,
        (Algebra.TensorProduct.assoc R R R (KummerAlg R p u) (KummerAlg R p u)
          (KummerAlg R p u)).toAlgHom
          ((Algebra.TensorProduct.map (kummerComul R p u)
            (AlgHom.id R (KummerAlg R p u)))
            (TensorProduct.tmul R (Pi.single (c - j) 1) (Pi.single j 1))) =
        ∑ j' : ZMod p, TensorProduct.tmul R
          (Pi.single (c - j - j') 1 : KummerAlg R p u)
          (TensorProduct.tmul R (Pi.single j' 1 : KummerAlg R p u)
            (Pi.single j 1 : KummerAlg R p u)) := by
      intro j
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        kummerComul_single_one_eq, TensorProduct.sum_tmul, map_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [AlgEquiv.coe_toAlgHom]
      exact Algebra.TensorProduct.assoc_tmul (R := R) (S := R) (T := R)
        (A := KummerAlg R p u) (C := KummerAlg R p u) (D := KummerAlg R p u)
        _ _ _
    have hR : ∀ j : ZMod p,
        (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
          (kummerComul R p u))
          (TensorProduct.tmul R (Pi.single (c - j) 1) (Pi.single j 1)) =
        ∑ j' : ZMod p, TensorProduct.tmul R
          (Pi.single (c - j) 1 : KummerAlg R p u)
          (TensorProduct.tmul R (Pi.single (j - j') 1 : KummerAlg R p u)
            (Pi.single j' 1 : KummerAlg R p u)) := by
      intro j
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        kummerComul_single_one_eq, TensorProduct.tmul_sum]
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j,
      ← Finset.sum_product', ← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv
      ⟨fun x => (x.2 + x.1, x.1), fun y => (y.2, y.1 - y.2),
        fun x => Prod.ext rfl (add_sub_cancel_right _ _),
        fun y => Prod.ext (sub_add_cancel _ _) rfl⟩ _ _ fun x => ?_
    obtain ⟨J, J'⟩ := x
    show TensorProduct.tmul R (Pi.single (c - J - J') 1 : KummerAlg R p u)
        (TensorProduct.tmul R (Pi.single J' 1 : KummerAlg R p u)
          (Pi.single J 1 : KummerAlg R p u)) =
      TensorProduct.tmul R (Pi.single (c - (J' + J)) 1 : KummerAlg R p u)
        (TensorProduct.tmul R (Pi.single (J' + J - J) 1 : KummerAlg R p u)
          (Pi.single J 1 : KummerAlg R p u))
    have h2 : c - (J' + J) = c - J - J' := by ring
    rw [h2, add_sub_cancel_right]
  · -- generator `single_c root`
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      kummerComul_single_root_eq, map_sum, map_sum, map_sum]
    have hL : ∀ j : ZMod p,
        (Algebra.TensorProduct.assoc R R R (KummerAlg R p u) (KummerAlg R p u)
          (KummerAlg R p u)).toAlgHom
          ((Algebra.TensorProduct.map (kummerComul R p u)
            (AlgHom.id R (KummerAlg R p u)))
            ((((u⁻¹ : Rˣ) : R) ^ (if (c - j).val + j.val < p then 0 else 1)) •
              TensorProduct.tmul R
                (Pi.single (c - j) (kummerRoot R p u (c - j)))
                (Pi.single j (kummerRoot R p u j)))) =
        ∑ j' : ZMod p,
          (((u⁻¹ : Rˣ) : R) ^ ((if (c - j).val + j.val < p then 0 else 1) +
            (if (c - j - j').val + j'.val < p then 0 else 1))) •
          TensorProduct.tmul R
            (Pi.single (c - j - j') (kummerRoot R p u (c - j - j')) :
              KummerAlg R p u)
            (TensorProduct.tmul R
              (Pi.single j' (kummerRoot R p u j') : KummerAlg R p u)
              (Pi.single j (kummerRoot R p u j) : KummerAlg R p u)) := by
      intro j
      rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        kummerComul_single_root_eq, TensorProduct.sum_tmul, map_smul, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← TensorProduct.smul_tmul', map_smul, AlgEquiv.coe_toAlgHom,
        Algebra.TensorProduct.assoc_tmul, smul_smul, ← pow_add]
    have hR : ∀ j : ZMod p,
        (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
          (kummerComul R p u))
          ((((u⁻¹ : Rˣ) : R) ^ (if (c - j).val + j.val < p then 0 else 1)) •
            TensorProduct.tmul R
              (Pi.single (c - j) (kummerRoot R p u (c - j)))
              (Pi.single j (kummerRoot R p u j))) =
        ∑ j' : ZMod p,
          (((u⁻¹ : Rˣ) : R) ^ ((if (c - j).val + j.val < p then 0 else 1) +
            (if (j - j').val + j'.val < p then 0 else 1))) •
          TensorProduct.tmul R
            (Pi.single (c - j) (kummerRoot R p u (c - j)) : KummerAlg R p u)
            (TensorProduct.tmul R
              (Pi.single (j - j') (kummerRoot R p u (j - j')) : KummerAlg R p u)
              (Pi.single j' (kummerRoot R p u j') : KummerAlg R p u)) := by
      intro j
      rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        kummerComul_single_root_eq, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [TensorProduct.tmul_smul, smul_smul, ← pow_add]
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j,
      ← Finset.sum_product', ← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv
      ⟨fun x => (x.2 + x.1, x.1), fun y => (y.2, y.1 - y.2),
        fun x => Prod.ext rfl (add_sub_cancel_right _ _),
        fun y => Prod.ext (sub_add_cancel _ _) rfl⟩ _ _ fun x => ?_
    obtain ⟨J, J'⟩ := x
    show (((u⁻¹ : Rˣ) : R) ^ ((if (c - J).val + J.val < p then 0 else 1) +
        (if (c - J - J').val + J'.val < p then 0 else 1))) •
        TensorProduct.tmul R
          (Pi.single (c - J - J') (kummerRoot R p u (c - J - J')) :
            KummerAlg R p u)
          (TensorProduct.tmul R
            (Pi.single J' (kummerRoot R p u J') : KummerAlg R p u)
            (Pi.single J (kummerRoot R p u J) : KummerAlg R p u)) =
      (((u⁻¹ : Rˣ) : R) ^ ((if (c - (J' + J)).val + (J' + J).val < p then 0
          else 1) +
        (if (J' + J - J).val + J.val < p then 0 else 1))) •
        TensorProduct.tmul R
          (Pi.single (c - (J' + J)) (kummerRoot R p u (c - (J' + J))) :
            KummerAlg R p u)
          (TensorProduct.tmul R
            (Pi.single (J' + J - J) (kummerRoot R p u (J' + J - J)) :
              KummerAlg R p u)
            (Pi.single J (kummerRoot R p u J) : KummerAlg R p u))
    have h2 : c - (J' + J) = c - J - J' := by ring
    rw [h2, add_sub_cancel_right]
    have hcarry := kummer_carry_assoc p (c - J - J') J' J
    rw [sub_add_cancel] at hcarry
    rw [hcarry]

/-- **Left counit axiom for the Kummer bialgebra** (PROVEN 2026-07-22
— `(ε ⊗ id) ∘ Δ = lid⁻¹`: on the generators, the double block sum of
the comultiplication collapses to the `(0, c)` block — the other
blocks are killed by the one-component evaluation or by the counit —
and the `(0, c)` block has no carry). -/
theorem kummerComul_rTensor_counit [NeZero p] :
    (Algebra.TensorProduct.map (kummerCounit R p u)
      (AlgHom.id R (KummerAlg R p u))).comp (kummerComul R p u)
      = (Algebra.TensorProduct.lid R (KummerAlg R p u)).symm := by
  classical
  have hsum : ∀ (c : ZMod p) (a : KummerComponent R p u c),
      (Algebra.TensorProduct.map (kummerCounit R p u)
        (AlgHom.id R (KummerAlg R p u)))
        (kummerComul R p u (Pi.single c a)) =
      (Algebra.TensorProduct.map (kummerCounit R p u)
        (AlgHom.id R (KummerAlg R p u)))
        ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) 0)
          (LinearMap.single R (KummerComponent R p u) c))
          (kummerComulComponent R p u 0 c
            (kummerCast R p u (zero_add c).symm a))) := by
    intro c a
    rw [kummerComul_apply_eq_sum, map_sum]
    refine (Finset.sum_eq_single c (fun j _ hj => ?_)
      (fun hc => absurd (Finset.mem_univ c) hc)).trans ?_
    · rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hij : i + j = c
      · exact kummer_rTensor_kill R p u
          (fun h0 => hj (by rwa [h0, zero_add] at hij)) j _
      · rw [Pi.single_eq_of_ne hij, map_zero, map_zero, map_zero]
    · rw [map_sum]
      refine (Finset.sum_eq_single 0 (fun i _ hi => ?_)
        (fun h0 => absurd (Finset.mem_univ _) h0)).trans ?_
      · by_cases hic : i + c = c
        · exact absurd (add_eq_right.mp hic) hi
        · rw [Pi.single_eq_of_ne hic, map_zero, map_zero, map_zero]
      · rw [kummerSingle_apply_of_eq R p u (zero_add c).symm a]
  refine kummerAlg_algHom_ext R p u (fun c => ?_) (fun c => ?_)
  · rw [AlgHom.comp_apply, hsum c 1, map_one, map_one,
      Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) 0)
        (1 : KummerComponent R p u 0) =
        (Pi.single (0 : ZMod p) 1 : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) c)
        (1 : KummerComponent R p u c) =
        (Pi.single c 1 : KummerAlg R p u) from rfl,
      kummerCounit_single_zero_one, AlgHom.id_apply]
    apply (Algebra.TensorProduct.lid R (KummerAlg R p u)).injective
    rw [Algebra.TensorProduct.lid_tmul, one_smul]
    exact ((Algebra.TensorProduct.lid R
      (KummerAlg R p u)).apply_symm_apply _).symm
  · rw [AlgHom.comp_apply, hsum c (kummerRoot R p u c), kummerCast_root,
      kummerComulComponent_root, kummerComulRoot_zero_left,
      TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) 0)
        (kummerRoot R p u 0) =
        (Pi.single (0 : ZMod p) (kummerRoot R p u 0) : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) c)
        (kummerRoot R p u c) =
        (Pi.single c (kummerRoot R p u c) : KummerAlg R p u) from rfl,
      kummerCounit_single_zero_root, AlgHom.id_apply]
    apply (Algebra.TensorProduct.lid R (KummerAlg R p u)).injective
    rw [Algebra.TensorProduct.lid_tmul, one_smul]
    exact ((Algebra.TensorProduct.lid R
      (KummerAlg R p u)).apply_symm_apply _).symm

/-- **Right counit axiom for the Kummer bialgebra** (PROVEN 2026-07-22
— `(id ⊗ ε) ∘ Δ = rid⁻¹`, symmetric to the left axiom: the double
block sum collapses to the `(c, 0)` block). -/
theorem kummerComul_lTensor_counit [NeZero p] :
    (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
      (kummerCounit R p u)).comp (kummerComul R p u)
      = (Algebra.TensorProduct.rid R R (KummerAlg R p u)).symm := by
  classical
  have hsum : ∀ (c : ZMod p) (a : KummerComponent R p u c),
      (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
        (kummerCounit R p u))
        (kummerComul R p u (Pi.single c a)) =
      (Algebra.TensorProduct.map (AlgHom.id R (KummerAlg R p u))
        (kummerCounit R p u))
        ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) c)
          (LinearMap.single R (KummerComponent R p u) 0))
          (kummerComulComponent R p u c 0
            (kummerCast R p u (add_zero c).symm a))) := by
    intro c a
    rw [kummerComul_apply_eq_sum, map_sum]
    refine (Finset.sum_eq_single 0 (fun j _ hj => ?_)
      (fun h0 => absurd (Finset.mem_univ _) h0)).trans ?_
    · rw [map_sum]
      exact Finset.sum_eq_zero fun i _ => kummer_lTensor_kill R p u i hj _
    · rw [map_sum]
      refine (Finset.sum_eq_single c (fun i _ hi => ?_)
        (fun hc => absurd (Finset.mem_univ _) hc)).trans ?_
      · by_cases hic : i + 0 = c
        · exact absurd (by rwa [add_zero] at hic) hi
        · rw [Pi.single_eq_of_ne hic, map_zero, map_zero, map_zero]
      · rw [kummerSingle_apply_of_eq R p u (add_zero c).symm a]
  refine kummerAlg_algHom_ext R p u (fun c => ?_) (fun c => ?_)
  · rw [AlgHom.comp_apply, hsum c 1, map_one, map_one,
      Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) c)
        (1 : KummerComponent R p u c) =
        (Pi.single c 1 : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) 0)
        (1 : KummerComponent R p u 0) =
        (Pi.single (0 : ZMod p) 1 : KummerAlg R p u) from rfl,
      kummerCounit_single_zero_one, AlgHom.id_apply]
    apply (Algebra.TensorProduct.rid R R (KummerAlg R p u)).injective
    rw [Algebra.TensorProduct.rid_tmul, one_smul]
    exact ((Algebra.TensorProduct.rid R R
      (KummerAlg R p u)).apply_symm_apply _).symm
  · rw [AlgHom.comp_apply, hsum c (kummerRoot R p u c), kummerCast_root,
      kummerComulComponent_root, kummerComulRoot_zero_right,
      TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      show (LinearMap.single R (KummerComponent R p u) c)
        (kummerRoot R p u c) =
        (Pi.single c (kummerRoot R p u c) : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) 0)
        (kummerRoot R p u 0) =
        (Pi.single (0 : ZMod p) (kummerRoot R p u 0) : KummerAlg R p u) from rfl,
      kummerCounit_single_zero_root, AlgHom.id_apply]
    apply (Algebra.TensorProduct.rid R R (KummerAlg R p u)).injective
    rw [Algebra.TensorProduct.rid_tmul, one_smul]
    exact ((Algebra.TensorProduct.rid R R
      (KummerAlg R p u)).apply_symm_apply _).symm

/-- The Kummer bialgebra structure: comultiplication and counit are the
algebra maps classifying the group law and the identity point; the
axioms are the three sorried leaves above. -/
noncomputable instance kummerBialgebra [NeZero p] : Bialgebra R (KummerAlg R p u) :=
  Bialgebra.ofAlgHom (kummerComul R p u) (kummerCounit R p u)
    (kummerComul_coassoc R p u)
    (kummerComul_rTensor_counit R p u)
    (kummerComul_lTensor_counit R p u)

/-- The antipode on a one-component element supported at a negated
index (PROVEN — cast-free by phrasing the index as `-j`):
`S(single₋ⱼ x) = singleⱼ(Sⱼ x)`. -/
theorem kummerAntipode_single_neg [NeZero p] (j : ZMod p)
    (x : KummerComponent R p u (-j)) :
    kummerAntipode R p u (Pi.single (-j) x) =
      Pi.single j (kummerAntipodeComponent R p u j x) := by
  funext i'
  simp only [kummerAntipode, AlgHom.pi_apply, AlgHom.comp_apply]
  rw [show (Pi.evalAlgHom R (KummerComponent R p u) (-i'))
    (Pi.single (-j) x) = (Pi.single (-j) x : KummerAlg R p u) (-i') from rfl]
  by_cases hij : i' = j
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (fun h' => hij (neg_injective h')), map_zero,
      Pi.single_eq_of_ne hij]

/-- The antipode of a one-component element is supported at the negated
index (PROVEN). -/
theorem kummerAntipode_single_support [NeZero p] {i i' : ZMod p}
    (h : i' ≠ -i) (x : KummerComponent R p u i) :
    kummerAntipode R p u (Pi.single i x) i' = 0 := by
  simp only [kummerAntipode, AlgHom.pi_apply, AlgHom.comp_apply]
  rw [show (Pi.evalAlgHom R (KummerComponent R p u) (-i'))
    (Pi.single i x) = (Pi.single i x : KummerAlg R p u) (-i') from rfl]
  rw [Pi.single_eq_of_ne (fun h' : -i' = i => h (by rw [← h', neg_neg])),
    map_zero]

/-- The antipode block on the root (PROVEN — `liftAlgHom` on the
adjoined root). -/
theorem kummerAntipodeComponent_root [NeZero p] (i : ZMod p) :
    kummerAntipodeComponent R p u i (kummerRoot R p u (-i)) =
      kummerAntipodeRoot R p u i :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The carry of the diagonal comultiplication block `(−j, j)` is the
identity-component indicator (PROVEN). -/
theorem kummer_neg_val_carry [NeZero p] (j : ZMod p) :
    (if (-j).val + j.val < p then 0 else 1) =
      (if j = 0 then (0 : ℕ) else 1) := by
  by_cases hj : j = 0
  · subst hj
    have h0 : (-(0 : ZMod p)).val + (0 : ZMod p).val < p := by
      rw [neg_zero, ZMod.val_zero, add_zero]
      exact Nat.pos_of_ne_zero (NeZero.ne p)
    rw [if_pos h0, if_pos rfl]
  · have h1 : ¬((-j).val + j.val < p) := by
      rw [ZMod.neg_val, if_neg hj, Nat.sub_add_cancel (ZMod.val_lt j).le]
      exact lt_irrefl p
    rw [if_neg h1, if_neg hj]

/-- The carry of the diagonal comultiplication block `(i, −i)` is the
identity-component indicator (PROVEN). -/
theorem kummer_val_neg_carry [NeZero p] (i : ZMod p) :
    (if i.val + (-i).val < p then 0 else 1) =
      (if i = 0 then (0 : ℕ) else 1) := by
  rw [Nat.add_comm]
  exact kummer_neg_val_carry p i

/-- `μ ∘ (S ⊗ id)` kills the off-diagonal tensor blocks (PROVEN by
tensor induction: the antipode factor is supported at the negated
index, so the product of one-component elements vanishes). -/
theorem kummer_antipode_rTensor_kill [NeZero p] {i j : ZMod p}
    (h : i + j ≠ 0)
    (T : TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j)) :
    (Algebra.TensorProduct.lift (kummerAntipode R p u)
      (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) j)) T) = 0 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      show (LinearMap.single R (KummerComponent R p u) i) x =
        (Pi.single i x : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) j) y =
        (Pi.single j y : KummerAlg R p u) from rfl,
      AlgHom.id_apply]
    funext k
    rw [Pi.mul_apply]
    by_cases hk : k = j
    · subst hk
      rw [kummerAntipode_single_support R p u
        (fun h' : k = -i => h (by rw [h', add_neg_cancel])) x, zero_mul]
      exact (Pi.zero_apply k).symm
    · rw [Pi.single_eq_of_ne hk, mul_zero]
      exact (Pi.zero_apply k).symm
  | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]

/-- `μ ∘ (id ⊗ S)` kills the off-diagonal tensor blocks (PROVEN,
mirror image). -/
theorem kummer_antipode_lTensor_kill [NeZero p] {i j : ZMod p}
    (h : i + j ≠ 0)
    (T : TensorProduct R (KummerComponent R p u i) (KummerComponent R p u j)) :
    (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
      (kummerAntipode R p u) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) j)) T) = 0 := by
  induction T using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      show (LinearMap.single R (KummerComponent R p u) i) x =
        (Pi.single i x : KummerAlg R p u) from rfl,
      show (LinearMap.single R (KummerComponent R p u) j) y =
        (Pi.single j y : KummerAlg R p u) from rfl,
      AlgHom.id_apply]
    funext k
    rw [Pi.mul_apply]
    by_cases hk : k = i
    · subst hk
      rw [kummerAntipode_single_support R p u
        (fun h' : k = -j => h (by rw [h', neg_add_cancel])) y, mul_zero]
      exact (Pi.zero_apply k).symm
    · rw [Pi.single_eq_of_ne hk, zero_mul]
      exact (Pi.zero_apply k).symm
  | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]

/-- The diagonal `(−j, j)` block of `μ ∘ (S ⊗ id) ∘ Δ` on the unit
(PROVEN): `S(e₋ⱼ)·eⱼ = eⱼ`. -/
theorem kummer_antipode_rTensor_diag_one [NeZero p] (j : ZMod p) :
    (Algebra.TensorProduct.lift (kummerAntipode R p u)
      (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) (-j))
        (LinearMap.single R (KummerComponent R p u) j))
        (kummerComulComponent R p u (-j) j
          (kummerCast R p u (neg_add_cancel j).symm 1))) = Pi.single j 1 := by
  rw [map_one, map_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul,
    show (LinearMap.single R (KummerComponent R p u) (-j))
      (1 : KummerComponent R p u (-j)) =
      (Pi.single (-j) 1 : KummerAlg R p u) from rfl,
    show (LinearMap.single R (KummerComponent R p u) j)
      (1 : KummerComponent R p u j) =
      (Pi.single j 1 : KummerAlg R p u) from rfl,
    AlgHom.id_apply, kummerAntipode_single_neg, map_one, ← Pi.single_mul,
    one_mul]

/-- The diagonal `(−j, j)` block of `μ ∘ (S ⊗ id) ∘ Δ` on the root
(PROVEN — the peu-ramifiée unit bookkeeping `S(x)·x = u^{εⱼ}` cancels
against the carry `u^{−εⱼ}` of the diagonal block). -/
theorem kummer_antipode_rTensor_diag_root [NeZero p] (j : ZMod p) :
    (Algebra.TensorProduct.lift (kummerAntipode R p u)
      (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) (-j))
        (LinearMap.single R (KummerComponent R p u) j))
        (kummerComulComponent R p u (-j) j
          (kummerCast R p u (neg_add_cancel j).symm
            (kummerRoot R p u 0)))) = Pi.single j 1 := by
  rw [kummerCast_root, kummerComulComponent_root, kummerComulRoot,
    kummer_neg_val_carry, mul_comm, ← Algebra.smul_def, map_smul, map_smul,
    TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
    show (LinearMap.single R (KummerComponent R p u) (-j))
      (kummerRoot R p u (-j)) =
      (Pi.single (-j) (kummerRoot R p u (-j)) : KummerAlg R p u) from rfl,
    show (LinearMap.single R (KummerComponent R p u) j)
      (kummerRoot R p u j) =
      (Pi.single j (kummerRoot R p u j) : KummerAlg R p u) from rfl,
    AlgHom.id_apply, kummerAntipode_single_neg, kummerAntipodeComponent_root,
    ← Pi.single_mul, kummerAntipodeRoot, mul_assoc, ← pow_succ,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)),
    kummerRoot_pow_p, ← map_mul, mul_assoc, ← mul_pow, Units.inv_mul,
    one_pow, mul_one, ← Pi.single_smul, Algebra.smul_def, ← map_mul,
    ← mul_pow, Units.inv_mul, one_pow, map_one]

/-- The diagonal `(i, −i)` block of `μ ∘ (id ⊗ S) ∘ Δ` on the unit
(PROVEN). -/
theorem kummer_antipode_lTensor_diag_one [NeZero p] (i : ZMod p) :
    (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
      (kummerAntipode R p u) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) (-i)))
        (kummerComulComponent R p u i (-i)
          (kummerCast R p u (add_neg_cancel i).symm 1))) = Pi.single i 1 := by
  rw [map_one, map_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul,
    show (LinearMap.single R (KummerComponent R p u) i)
      (1 : KummerComponent R p u i) =
      (Pi.single i 1 : KummerAlg R p u) from rfl,
    show (LinearMap.single R (KummerComponent R p u) (-i))
      (1 : KummerComponent R p u (-i)) =
      (Pi.single (-i) 1 : KummerAlg R p u) from rfl,
    AlgHom.id_apply, kummerAntipode_single_neg, map_one, ← Pi.single_mul,
    one_mul]

/-- The diagonal `(i, −i)` block of `μ ∘ (id ⊗ S) ∘ Δ` on the root
(PROVEN, mirror image). -/
theorem kummer_antipode_lTensor_diag_root [NeZero p] (i : ZMod p) :
    (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
      (kummerAntipode R p u) fun _ _ => Commute.all _ _)
      ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
        (LinearMap.single R (KummerComponent R p u) (-i)))
        (kummerComulComponent R p u i (-i)
          (kummerCast R p u (add_neg_cancel i).symm
            (kummerRoot R p u 0)))) = Pi.single i 1 := by
  rw [kummerCast_root, kummerComulComponent_root, kummerComulRoot,
    kummer_val_neg_carry, mul_comm, ← Algebra.smul_def, map_smul, map_smul,
    TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
    show (LinearMap.single R (KummerComponent R p u) i)
      (kummerRoot R p u i) =
      (Pi.single i (kummerRoot R p u i) : KummerAlg R p u) from rfl,
    show (LinearMap.single R (KummerComponent R p u) (-i))
      (kummerRoot R p u (-i)) =
      (Pi.single (-i) (kummerRoot R p u (-i)) : KummerAlg R p u) from rfl,
    AlgHom.id_apply, kummerAntipode_single_neg, kummerAntipodeComponent_root,
    ← Pi.single_mul, kummerAntipodeRoot, mul_left_comm, ← pow_succ',
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)),
    kummerRoot_pow_p, ← map_mul, mul_assoc, ← mul_pow, Units.inv_mul,
    one_pow, mul_one, ← Pi.single_smul, Algebra.smul_def, ← map_mul,
    ← mul_pow, Units.inv_mul, one_pow, map_one]

/-- **The antipode axiom, right form** (PROVEN 2026-07-22 — `μ ∘ (S ⊗
id) ∘ Δ = η ∘ ε` on the explicit model: for a generator supported at
`c ≠ 0` every block dies — off the fibre `i+j = c` by the
one-component evaluation, on it because the antipode factor sits at
`−i ≠ j` — matching `ε = 0`; for `c = 0` the diagonal blocks `(−j, j)`
survive and sum to `∑ⱼ eⱼ = 1 = η(ε)`). -/
theorem kummerAntipode_rTensor [NeZero p] :
    ((Algebra.TensorProduct.lift (kummerAntipode R p u)
        (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom R (KummerAlg R p u)))
      = (Algebra.ofId R (KummerAlg R p u)).comp
        (Bialgebra.counitAlgHom R (KummerAlg R p u)) := by
  classical
  have hcm : Bialgebra.comulAlgHom R (KummerAlg R p u) = kummerComul R p u :=
    AlgHom.ext fun _ => rfl
  have hct : Bialgebra.counitAlgHom R (KummerAlg R p u) = kummerCounit R p u :=
    AlgHom.ext fun _ => rfl
  rw [hcm, hct]
  have hoff : ∀ (c : ZMod p) (a : KummerComponent R p u c), c ≠ 0 →
      (Algebra.TensorProduct.lift (kummerAntipode R p u)
        (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
        (kummerComul R p u (Pi.single c a)) = 0 := by
    intro c a hc
    rw [kummerComul_apply_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hij : i + j = c
    · exact kummer_antipode_rTensor_kill R p u (by rw [hij]; exact hc) _
    · rw [Pi.single_eq_of_ne hij, map_zero, map_zero, map_zero]
  have hdiag : ∀ (a : KummerComponent R p u 0),
      (∀ j : ZMod p, (Algebra.TensorProduct.lift (kummerAntipode R p u)
        (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
        ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) (-j))
          (LinearMap.single R (KummerComponent R p u) j))
          (kummerComulComponent R p u (-j) j
            (kummerCast R p u (neg_add_cancel j).symm a))) = Pi.single j 1) →
      (Algebra.TensorProduct.lift (kummerAntipode R p u)
        (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
        (kummerComul R p u (Pi.single 0 a)) = 1 := by
    intro a hblock
    rw [kummerComul_apply_eq_sum, map_sum]
    have hj : ∀ j : ZMod p,
        (Algebra.TensorProduct.lift (kummerAntipode R p u)
          (AlgHom.id R (KummerAlg R p u)) fun _ _ => Commute.all _ _)
          (∑ i : ZMod p,
            (TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
              (LinearMap.single R (KummerComponent R p u) j))
            (kummerComulComponent R p u i j
              ((Pi.single (0 : ZMod p) a : KummerAlg R p u) (i + j)))) =
        Pi.single j 1 := by
      intro j
      rw [map_sum]
      refine (Finset.sum_eq_single (-j) (fun i _ hi => ?_)
        (fun hmem => absurd (Finset.mem_univ _) hmem)).trans ?_
      · by_cases hij : i + j = 0
        · exact absurd (eq_neg_of_add_eq_zero_left hij) hi
        · rw [Pi.single_eq_of_ne hij, map_zero, map_zero, map_zero]
      · rw [kummerSingle_apply_of_eq R p u (neg_add_cancel j).symm]
        exact hblock j
    rw [Finset.sum_congr rfl fun j _ => hj j]
    exact Finset.univ_sum_single 1
  refine kummerAlg_algHom_ext R p u (fun c => ?_) (fun c => ?_)
  · by_cases hc : c = 0
    · subst hc
      rw [AlgHom.comp_apply, AlgHom.comp_apply, kummerCounit_single_zero_one,
        map_one]
      exact hdiag 1 fun j => kummer_antipode_rTensor_diag_one R p u j
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        kummerCounit_single_of_ne R p u hc, map_zero]
      exact hoff c 1 hc
  · by_cases hc : c = 0
    · subst hc
      rw [AlgHom.comp_apply, AlgHom.comp_apply, kummerCounit_single_zero_root,
        map_one]
      exact hdiag (kummerRoot R p u 0)
        fun j => kummer_antipode_rTensor_diag_root R p u j
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        kummerCounit_single_of_ne R p u hc, map_zero]
      exact hoff c (kummerRoot R p u c) hc

/-- **The antipode axiom, left form** (PROVEN 2026-07-22 — mirror
image: the surviving diagonal blocks are `(i, −i)` after commuting the
double sum). -/
theorem kummerAntipode_lTensor [NeZero p] :
    ((Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
        (kummerAntipode R p u) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom R (KummerAlg R p u)))
      = (Algebra.ofId R (KummerAlg R p u)).comp
        (Bialgebra.counitAlgHom R (KummerAlg R p u)) := by
  classical
  have hcm : Bialgebra.comulAlgHom R (KummerAlg R p u) = kummerComul R p u :=
    AlgHom.ext fun _ => rfl
  have hct : Bialgebra.counitAlgHom R (KummerAlg R p u) = kummerCounit R p u :=
    AlgHom.ext fun _ => rfl
  rw [hcm, hct]
  have hoff : ∀ (c : ZMod p) (a : KummerComponent R p u c), c ≠ 0 →
      (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
        (kummerAntipode R p u) fun _ _ => Commute.all _ _)
        (kummerComul R p u (Pi.single c a)) = 0 := by
    intro c a hc
    rw [kummerComul_apply_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hij : i + j = c
    · exact kummer_antipode_lTensor_kill R p u (by rw [hij]; exact hc) _
    · rw [Pi.single_eq_of_ne hij, map_zero, map_zero, map_zero]
  have hdiag : ∀ (a : KummerComponent R p u 0),
      (∀ i : ZMod p, (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
        (kummerAntipode R p u) fun _ _ => Commute.all _ _)
        ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
          (LinearMap.single R (KummerComponent R p u) (-i)))
          (kummerComulComponent R p u i (-i)
            (kummerCast R p u (add_neg_cancel i).symm a))) = Pi.single i 1) →
      (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
        (kummerAntipode R p u) fun _ _ => Commute.all _ _)
        (kummerComul R p u (Pi.single 0 a)) = 1 := by
    intro a hblock
    rw [kummerComul_apply_eq_sum, map_sum]
    simp only [map_sum]
    rw [Finset.sum_comm]
    have hi : ∀ i : ZMod p,
        (∑ j : ZMod p,
          (Algebra.TensorProduct.lift (AlgHom.id R (KummerAlg R p u))
            (kummerAntipode R p u) fun _ _ => Commute.all _ _)
            ((TensorProduct.map (LinearMap.single R (KummerComponent R p u) i)
              (LinearMap.single R (KummerComponent R p u) j))
            (kummerComulComponent R p u i j
              ((Pi.single (0 : ZMod p) a : KummerAlg R p u) (i + j))))) =
        Pi.single i 1 := by
      intro i
      refine (Finset.sum_eq_single (-i) (fun j _ hj => ?_)
        (fun hmem => absurd (Finset.mem_univ _) hmem)).trans ?_
      · by_cases hij : i + j = 0
        · exact absurd (eq_neg_of_add_eq_zero_right hij) hj
        · rw [Pi.single_eq_of_ne hij, map_zero, map_zero, map_zero]
      · rw [kummerSingle_apply_of_eq R p u (add_neg_cancel i).symm]
        exact hblock i
    rw [Finset.sum_congr rfl fun i _ => hi i]
    exact Finset.univ_sum_single 1
  refine kummerAlg_algHom_ext R p u (fun c => ?_) (fun c => ?_)
  · by_cases hc : c = 0
    · subst hc
      rw [AlgHom.comp_apply, AlgHom.comp_apply, kummerCounit_single_zero_one,
        map_one]
      exact hdiag 1 fun i => kummer_antipode_lTensor_diag_one R p u i
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        kummerCounit_single_of_ne R p u hc, map_zero]
      exact hoff c 1 hc
  · by_cases hc : c = 0
    · subst hc
      rw [AlgHom.comp_apply, AlgHom.comp_apply, kummerCounit_single_zero_root,
        map_one]
      exact hdiag (kummerRoot R p u 0)
        fun i => kummer_antipode_lTensor_diag_root R p u i
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        kummerCounit_single_of_ne R p u hc, map_zero]
      exact hoff c (kummerRoot R p u c) hc

/-- The Kummer Hopf algebra: the antipode is the pullback of
point-inversion; the antipode axioms are the two sorried leaves
above. -/
noncomputable instance kummerHopfAlgebra [NeZero p] :
    HopfAlgebra R (KummerAlg R p u) :=
  HopfAlgebra.ofAlgHom (kummerAntipode R p u)
    (kummerAntipode_rTensor R p u)
    (kummerAntipode_lTensor R p u)

end KummerHopf

/-! #### The generic fibre of the Kummer algebra is étale

Over a characteristic-zero field `K` containing the coefficient ring
`O`, each Kummer component base-changes to the standard étale algebra
of the pair `⟨xᵖ − uⁱ, 1⟩` — the Bézout condition
`f'·(d·x) − f·(d·p) = 1`, `d = (p·uⁱ)⁻¹`, is witnessed explicitly —
and the tensor product distributes over the finite product. -/

section KummerEtale

open Polynomial

variable (O : Type) [CommRing O] (K : Type) [Field K] [CharZero K] [Algebra O K]
variable (p : ℕ) [NeZero p] (u : Oˣ)

/-- The standard étale presentation `⟨xᵖ − uⁱ, 1⟩` of the generic fibre
of a Kummer component (PROVEN — explicit Bézout witness). -/
noncomputable def kummerStdPair (i : ZMod p) : StandardEtalePair K where
  f := (Polynomial.X : Polynomial K) ^ p -
    Polynomial.C (algebraMap O K ((u : O) ^ i.val))
  monic_f := Polynomial.monic_X_pow_sub_C _ (NeZero.ne p)
  g := 1
  cond := by
    have hc0 : algebraMap O K ((u : O) ^ i.val) ≠ 0 :=
      (((u ^ i.val).isUnit.map (algebraMap O K)).ne_zero)
    have hp0 : ((p : K)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    have hpc : (p : K) * algebraMap O K ((u : O) ^ i.val) ≠ 0 :=
      mul_ne_zero hp0 hc0
    refine ⟨Polynomial.C (((p : K) * algebraMap O K ((u : O) ^ i.val))⁻¹) *
      Polynomial.X,
      -(Polynomial.C (((p : K) * algebraMap O K ((u : O) ^ i.val))⁻¹) *
        Polynomial.C (p : K)),
      1, ?_⟩
    have h1 : Polynomial.derivative ((Polynomial.X : Polynomial K) ^ p -
        Polynomial.C (algebraMap O K ((u : O) ^ i.val))) =
        Polynomial.C ((p : ℕ) : K) * Polynomial.X ^ (p - 1) := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
        Polynomial.derivative_X_pow]
    rw [h1]
    have h2 : (Polynomial.X : Polynomial K) ^ p =
        Polynomial.X ^ (p - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (NeZero.ne p))]
    rw [h2]
    have h4 : (Polynomial.C (((p : K) * algebraMap O K ((u : O) ^ i.val))⁻¹) *
        Polynomial.C (p : K) *
        Polynomial.C (algebraMap O K ((u : O) ^ i.val)) : Polynomial K) = 1 := by
      rw [← Polynomial.C_mul, ← Polynomial.C_mul, mul_assoc,
        inv_mul_cancel₀ hpc, Polynomial.C_1]
    linear_combination h4

noncomputable local instance kummerStdPairAlgebra (i : ZMod p) :
    Algebra O ((kummerStdPair O K p u i).Ring) :=
  ((algebraMap K ((kummerStdPair O K p u i).Ring)).comp
    (algebraMap O K)).toAlgebra

local instance kummerStdPairTower (i : ZMod p) :
    IsScalarTower O K ((kummerStdPair O K p u i).Ring) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The defining relation of the pair's `X` in `O`-coefficients
(PROVEN): the input to the component-side lift. -/
theorem kummerStdPair_relation (i : ZMod p) :
    ((Polynomial.X : Polynomial O) ^ p -
      Polynomial.C ((u : O) ^ i.val)).eval₂
      (Algebra.ofId O ((kummerStdPair O K p u i).Ring))
      ((kummerStdPair O K p u i).X) = 0 := by
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero]
  have h1 : Polynomial.aeval ((kummerStdPair O K p u i).X)
      (kummerStdPair O K p u i).f = 0 :=
    (kummerStdPair O K p u i).hasMap_X.1
  rw [show (kummerStdPair O K p u i).f =
      (Polynomial.X : Polynomial K) ^ p -
        Polynomial.C (algebraMap O K ((u : O) ^ i.val)) from rfl] at h1
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    sub_eq_zero] at h1
  rw [h1, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply O K]
  rfl

/-- The `O`-algebra map from a Kummer component to the standard étale
model, sending the root to the pair's `X` (PROVEN data). -/
noncomputable def kummerStdPairComponentHom (i : ZMod p) :
    KummerComponent O p u i →ₐ[O] (kummerStdPair O K p u i).Ring :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId O ((kummerStdPair O K p u i).Ring))
    ((kummerStdPair O K p u i).X) (kummerStdPair_relation O K p u i)

/-- The base-changed root satisfies the pair's equations (PROVEN). -/
theorem kummerStdPair_hasMap (i : ZMod p) :
    (kummerStdPair O K p u i).HasMap
      (TensorProduct.tmul O (1 : K) (kummerRoot O p u i)) := by
  constructor
  · rw [show (kummerStdPair O K p u i).f =
      (Polynomial.X : Polynomial K) ^ p -
        Polynomial.C (algebraMap O K ((u : O) ^ i.val)) from rfl]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      sub_eq_zero]
    rw [Algebra.TensorProduct.tmul_pow, one_pow, kummerRoot_pow_p,
      ← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply O K]
    conv_rhs => rw [← map_pow, ← map_pow]
  · rw [show (kummerStdPair O K p u i).g = 1 from rfl, map_one]
    exact isUnit_one

/-- **The generic fibre of a Kummer component is standard étale**
(PROVEN — the two universal-property lifts are mutually inverse). -/
noncomputable def kummerStdPairEquiv (i : ZMod p) :
    (kummerStdPair O K p u i).Ring ≃ₐ[K]
      TensorProduct O K (KummerComponent O p u i) := by
  refine AlgEquiv.ofAlgHom
    ((kummerStdPair O K p u i).lift
      (TensorProduct.tmul O (1 : K) (kummerRoot O p u i))
      (kummerStdPair_hasMap O K p u i))
    (Algebra.TensorProduct.lift (Algebra.ofId K _)
      (kummerStdPairComponentHom O K p u i) fun _ _ => Commute.all _ _)
    ?_ ?_
  · -- `lift ∘ tensorLift = id` on the tensor product
    have hcomp : (((kummerStdPair O K p u i).lift
        (TensorProduct.tmul O (1 : K) (kummerRoot O p u i))
        (kummerStdPair_hasMap O K p u i)).restrictScalars O).comp
        (kummerStdPairComponentHom O K p u i) =
        Algebra.TensorProduct.includeRight := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply]
      rw [show (kummerStdPairComponentHom O K p u i)
        (AdjoinRoot.root _) = (kummerStdPair O K p u i).X from
        AdjoinRoot.liftAlgHom_root _ _ _ _]
      exact (kummerStdPair O K p u i).lift_X
        (TensorProduct.tmul O (1 : K) (kummerRoot O p u i))
        (kummerStdPair_hasMap O K p u i)
    refine Algebra.TensorProduct.ext' fun a b => ?_
    rw [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul,
      AlgHom.id_apply]
    have hb : ((kummerStdPair O K p u i).lift
        (TensorProduct.tmul O (1 : K) (kummerRoot O p u i))
        (kummerStdPair_hasMap O K p u i))
        ((kummerStdPairComponentHom O K p u i) b) =
        TensorProduct.tmul O (1 : K) b := by
      have := congrArg (fun φ => φ b) hcomp
      simpa using this
    rw [hb]
    have ha : ((kummerStdPair O K p u i).lift
        (TensorProduct.tmul O (1 : K) (kummerRoot O p u i))
        (kummerStdPair_hasMap O K p u i)) ((Algebra.ofId K _) a) =
        TensorProduct.tmul O a 1 := by
      rw [Algebra.ofId_apply, AlgHom.commutes]
      rfl
    rw [ha, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · -- `tensorLift ∘ lift = id` on the standard étale model
    refine StandardEtalePair.hom_ext ?_
    rw [AlgHom.comp_apply, StandardEtalePair.lift_X,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **The generic fibre of the Kummer algebra is étale** (PROVEN —
étale for each standard-étale factor, stable under finite products and
transport along the tensor-product distribution). -/
theorem kummerAlg_etale :
    Algebra.Etale K (TensorProduct O K (KummerAlg O p u)) := by
  haveI he : ∀ i : ZMod p,
      Algebra.Etale K (TensorProduct O K (KummerComponent O p u i)) :=
    fun i => Algebra.Etale.of_equiv (kummerStdPairEquiv O K p u i)
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.piRight O K K (KummerComponent O p u)).symm

end KummerEtale

/-! #### The `Ω`-points of the Kummer algebra

For a field extension `Ω` of the fraction field `K`, an `Ω`-point of
the generic fibre of the Kummer algebra is a component index `i`
together with a `p`-th root of `uⁱ` in `Ω`: a `K`-algebra map out of
the product factors through exactly one component (its values on the
component idempotents are orthogonal idempotents of the field `Ω`
summing to `1`), and on that component it is evaluation at a root of
`xᵖ − uⁱ`. Under the convolution product of the Hopf structure the
points compose by the carry law `(i,s)·(j,t) = (i+j, s·t·u^{−ε})`;
with a recentring witness `u = Q·w⁻ᵖ` the assignment `(i,t) ↦ [wⁱ·t]`
is a Galois-equivariant isomorphism onto the `p`-torsion of
`Ωˣ/Qᶻ`. -/

section KummerPoints

variable (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
variable (p : ℕ) [NeZero p] (u : Rˣ)

/-- Evaluation of the `i`-th Kummer component at a `p`-th root `t` of
`uⁱ` in `Ω` (PROVEN data): the `R`-algebra map classifying the point. -/
noncomputable def kummerComponentPointEval (i : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    KummerComponent R p u i →ₐ[R] Ω :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R Ω) t (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ht]
    rfl)

omit [NeZero p] in
/-- The component evaluation on the adjoined root (PROVEN). -/
theorem kummerComponentPointEval_root (i : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    kummerComponentPointEval R Ω p u i t ht (kummerRoot R p u i) = t :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The `Ω`-point of the generic fibre of the Kummer algebra attached
to a component index `i` and a `p`-th root `t` of `uⁱ` (PROVEN data):
project to the `i`-th component and evaluate at `t`. -/
noncomputable def kummerPointHom (i : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω :=
  Algebra.TensorProduct.lift (Algebra.ofId K Ω)
    ((kummerComponentPointEval R Ω p u i t ht).comp
      (Pi.evalAlgHom R (KummerComponent R p u) i))
    fun _ _ => Commute.all _ _

omit [NeZero p] in
/-- The point `(i, t)` on a tensor `1 ⊗ h` (PROVEN — the master value
formula): evaluate the `i`-th coordinate of `h` at `t`. -/
theorem kummerPointHom_tmul_one (i : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) (h : KummerAlg R p u) :
    kummerPointHom R K Ω p u i t ht (TensorProduct.tmul R (1 : K) h) =
      kummerComponentPointEval R Ω p u i t ht (h i) := by
  rw [kummerPointHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

omit [NeZero p] in
/-- The point `(i, t)` on the component idempotents (PROVEN):
`φ(eⱼ) = δᵢⱼ`. -/
theorem kummerPointHom_single_one (i j : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    kummerPointHom R K Ω p u i t ht
        (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) =
      if j = i then 1 else 0 := by
  rw [kummerPointHom_tmul_one]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, map_one, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

omit [NeZero p] in
/-- The point `(i, t)` on the component roots (PROVEN):
`φ(single j x) = δᵢⱼ·t`. -/
theorem kummerPointHom_single_root (i j : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    kummerPointHom R K Ω p u i t ht
        (TensorProduct.tmul R (1 : K)
          (Pi.single j (kummerRoot R p u j) : KummerAlg R p u)) =
      if j = i then t else 0 := by
  rw [kummerPointHom_tmul_one]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, if_pos rfl]
    exact kummerComponentPointEval_root R Ω p u j t ht
  · rw [Pi.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

/-- **Extensionality for `Ω`-points** (PROVEN): two `K`-algebra maps
out of the generic fibre of the Kummer algebra agree as soon as they
agree on the component idempotents and the component roots. -/
theorem kummerPointHom_ext
    {φ ψ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω}
    (hone : ∀ i : ZMod p,
      φ (TensorProduct.tmul R (1 : K) (Pi.single i 1 : KummerAlg R p u)) =
      ψ (TensorProduct.tmul R (1 : K) (Pi.single i 1 : KummerAlg R p u)))
    (hroot : ∀ i : ZMod p,
      φ (TensorProduct.tmul R (1 : K)
        (Pi.single i (kummerRoot R p u i) : KummerAlg R p u)) =
      ψ (TensorProduct.tmul R (1 : K)
        (Pi.single i (kummerRoot R p u i) : KummerAlg R p u))) :
    φ = ψ := by
  have hrest : (φ.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight :
        KummerAlg R p u →ₐ[R] TensorProduct R K (KummerAlg R p u)) =
      (ψ.restrictScalars R).comp
        (Algebra.TensorProduct.includeRight :
          KummerAlg R p u →ₐ[R] TensorProduct R K (KummerAlg R p u)) :=
    kummerAlg_algHom_ext R p u (fun i => hone i) (fun i => hroot i)
  refine Algebra.TensorProduct.ext' fun a b => ?_
  have h1 : (TensorProduct.tmul R a b : TensorProduct R K (KummerAlg R p u)) =
      a • TensorProduct.tmul R (1 : K) b := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : φ (TensorProduct.tmul R (1 : K) b) =
      ψ (TensorProduct.tmul R (1 : K) b) := by
    have h3 := congrArg (fun χ : KummerAlg R p u →ₐ[R] Ω => χ b) hrest
    simpa using h3
  rw [h1, map_smul, map_smul, h2]

set_option maxHeartbeats 1000000 in
/-- **Every `Ω`-point is a component-root evaluation** (PROVEN): the
values of `φ` on the component idempotents are orthogonal idempotents
of the field `Ω` summing to `1`, so exactly one of them equals `1`;
`φ` is the evaluation of that component at its root value. -/
theorem exists_kummerPointHom_eq
    (φ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω) :
    ∃ (i : ZMod p) (t : Ω) (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)),
      φ = kummerPointHom R K Ω p u i t ht := by
  classical
  -- the idempotent values
  have horth : ∀ j k : ZMod p, j ≠ k →
      φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) *
      φ (TensorProduct.tmul R (1 : K) (Pi.single k 1 : KummerAlg R p u)) = 0 := by
    intro j k hjk
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hz : (Pi.single j 1 * Pi.single k 1 : KummerAlg R p u) = 0 := by
      funext l
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hl : l = j
      · subst hl
        rw [Pi.single_eq_of_ne hjk, mul_zero]
      · rw [Pi.single_eq_of_ne hl, zero_mul]
    rw [hz, TensorProduct.tmul_zero, map_zero]
  have hsum : ∑ j : ZMod p,
      φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) = 1 := by
    have h1 : (1 : KummerAlg R p u) = ∑ j : ZMod p, Pi.single j 1 := by
      funext l
      rw [Finset.sum_apply,
        Finset.sum_eq_single l
          (fun j _ hj => Pi.single_eq_of_ne (Ne.symm hj) 1)
          (fun hl => absurd (Finset.mem_univ l) hl),
        Pi.single_eq_same]
      rfl
    calc ∑ j : ZMod p,
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u))
        = φ (TensorProduct.tmul R (1 : K)
            (∑ j : ZMod p, (Pi.single j 1 : KummerAlg R p u))) := by
          rw [TensorProduct.tmul_sum, map_sum]
      _ = 1 := by
          rw [← h1, ← Algebra.TensorProduct.one_def, map_one]
  have h01 : ∀ j : ZMod p,
      φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) = 0 ∨
      φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) = 1 := by
    intro j
    have hidem :
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) *
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) =
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) := by
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      congr 1
      funext l
      rw [Pi.mul_apply]
      by_cases hl : l = j
      · subst hl
        rw [Pi.single_eq_same, one_mul]
      · rw [Pi.single_eq_of_ne hl, zero_mul]
    have hfac :
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) *
        (φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) - 1) = 0 := by
      rw [mul_sub, hidem, mul_one, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hexists : ∃ i : ZMod p,
      φ (TensorProduct.tmul R (1 : K) (Pi.single i 1 : KummerAlg R p u)) = 1 := by
    by_contra hno
    push Not at hno
    have hall : ∀ j : ZMod p,
        φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) = 0 :=
      fun j => (h01 j).resolve_right (hno j)
    rw [Finset.sum_congr rfl (fun j _ => hall j), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hei⟩ := hexists
  have hzero : ∀ j : ZMod p, j ≠ i →
      φ (TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u)) = 0 := by
    intro j hj
    rcases h01 j with h | h
    · exact h
    · exfalso
      have hcontra := horth j i hj
      rw [h, hei, one_mul] at hcontra
      exact one_ne_zero hcontra
  -- the root value
  have hroot0 : ∀ j : ZMod p, j ≠ i →
      φ (TensorProduct.tmul R (1 : K)
        (Pi.single j (kummerRoot R p u j) : KummerAlg R p u)) = 0 := by
    intro j hj
    have hsplit : (Pi.single j (kummerRoot R p u j) : KummerAlg R p u) =
        Pi.single j 1 * Pi.single j (kummerRoot R p u j) := by
      funext l
      rw [Pi.mul_apply]
      by_cases hl : l = j
      · subst hl
        rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
      · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, zero_mul]
    rw [hsplit,
      show TensorProduct.tmul R (1 : K)
          (Pi.single j 1 * Pi.single j (kummerRoot R p u j) : KummerAlg R p u) =
        TensorProduct.tmul R (1 : K) (Pi.single j 1 : KummerAlg R p u) *
        TensorProduct.tmul R (1 : K)
          (Pi.single j (kummerRoot R p u j) : KummerAlg R p u) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      map_mul, hzero j hj, zero_mul]
  have ht : (φ (TensorProduct.tmul R (1 : K)
      (Pi.single i (kummerRoot R p u i) : KummerAlg R p u))) ^ p =
      algebraMap R Ω ((u : R) ^ i.val) := by
    have hsp : (Pi.single i (kummerRoot R p u i) : KummerAlg R p u) ^ p =
        Pi.single i (kummerRoot R p u i ^ p) := by
      funext l
      rw [Pi.pow_apply]
      by_cases hl : l = i
      · subst hl
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl,
          zero_pow (NeZero.ne p)]
    have hsm : (Pi.single i (algebraMap R (KummerComponent R p u i)
        ((u : R) ^ i.val)) : KummerAlg R p u) =
        ((u : R) ^ i.val) • (Pi.single i 1 : KummerAlg R p u) := by
      rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul]
    calc (φ (TensorProduct.tmul R (1 : K)
        (Pi.single i (kummerRoot R p u i) : KummerAlg R p u))) ^ p
        = φ ((TensorProduct.tmul R (1 : K)
            (Pi.single i (kummerRoot R p u i) : KummerAlg R p u)) ^ p) :=
          (map_pow φ _ p).symm
      _ = φ (TensorProduct.tmul R (1 : K)
            ((Pi.single i (kummerRoot R p u i) : KummerAlg R p u) ^ p)) := by
          rw [Algebra.TensorProduct.tmul_pow, one_pow]
      _ = φ (TensorProduct.tmul R (1 : K)
            (((u : R) ^ i.val) • (Pi.single i 1 : KummerAlg R p u))) := by
          rw [hsp, kummerRoot_pow_p, hsm]
      _ = algebraMap R Ω ((u : R) ^ i.val) := by
          rw [TensorProduct.tmul_smul,
            ← algebraMap_smul K ((u : R) ^ i.val), map_smul, hei,
            Algebra.smul_def, mul_one]
          exact (IsScalarTower.algebraMap_apply R K Ω ((u : R) ^ i.val)).symm
  refine ⟨i, _, ht, ?_⟩
  refine kummerPointHom_ext R K Ω p u (fun j => ?_) (fun j => ?_)
  · rw [kummerPointHom_single_one]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl, hei]
    · rw [if_neg h, hzero j h]
  · rw [kummerPointHom_single_root]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl]
    · rw [if_neg h, hroot0 j h]

omit [NeZero p] in
/-- The point data is determined by the point (PROVEN — read off the
generator values). -/
theorem kummerPointHom_inj {i i' : ZMod p} {t t' : Ω}
    {ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)}
    {ht' : t' ^ p = algebraMap R Ω ((u : R) ^ i'.val)}
    (h : kummerPointHom R K Ω p u i t ht = kummerPointHom R K Ω p u i' t' ht') :
    i = i' ∧ t = t' := by
  have h1 := congrArg
    (fun χ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω =>
      χ (TensorProduct.tmul R (1 : K) (Pi.single i 1 : KummerAlg R p u))) h
  rw [kummerPointHom_single_one, kummerPointHom_single_one, if_pos rfl] at h1
  have hii : i = i' := by
    by_contra hne
    rw [if_neg hne] at h1
    exact one_ne_zero h1
  subst hii
  refine ⟨rfl, ?_⟩
  have h2 := congrArg
    (fun χ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω =>
      χ (TensorProduct.tmul R (1 : K)
        (Pi.single i (kummerRoot R p u i) : KummerAlg R p u))) h
  rwa [kummerPointHom_single_root, kummerPointHom_single_root,
    if_pos rfl, if_pos rfl] at h2

/-- The carried product root is a `p`-th root of `u^{(i+j).val}`
(PROVEN — the units-level carry identity). -/
theorem kummerPointMul_relation (i j : ZMod p) (s t : Ω)
    (hs : s ^ p = algebraMap R Ω ((u : R) ^ i.val))
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ j.val)) :
    (s * t * algebraMap R Ω (((u⁻¹ : Rˣ) : R) ^
        (if i.val + j.val < p then 0 else 1))) ^ p =
      algebraMap R Ω ((u : R) ^ (i + j).val) := by
  rw [mul_pow, mul_pow, hs, ht, ← map_pow, ← pow_mul, ← map_mul, ← map_mul]
  congr 1
  have hU : (u ^ i.val * u ^ j.val *
      u⁻¹ ^ ((if i.val + j.val < p then 0 else 1) * p) : Rˣ) =
      u ^ (i + j).val := by
    have hc := kummer_val_add_carry p i j
    by_cases hlt : i.val + j.val < p
    · rw [if_pos hlt] at hc ⊢
      rw [Nat.mul_zero, Nat.add_zero] at hc
      rw [Nat.zero_mul, pow_zero, mul_one, ← pow_add, hc]
    · rw [if_neg hlt] at hc ⊢
      rw [Nat.mul_one] at hc
      rw [Nat.one_mul, ← pow_add, hc, pow_add, mul_assoc, inv_pow,
        mul_inv_cancel, mul_one]
  have hR := congrArg (Units.val) hU
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hR

omit [NeZero p] in
/-- The point `(i, t)` on a scaled component root (PROVEN):
`φ(single j (r·x)) = δᵢⱼ·r̄·t`. -/
theorem kummerPointHom_single_smul_root (i j : ZMod p) (r : R) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    kummerPointHom R K Ω p u i t ht
        (TensorProduct.tmul R (1 : K)
          (Pi.single j (r • kummerRoot R p u j) : KummerAlg R p u)) =
      if j = i then algebraMap R Ω r * t else 0 := by
  rw [kummerPointHom_tmul_one]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, if_pos rfl, map_smul,
      kummerComponentPointEval_root, Algebra.smul_def]
  · rw [Pi.single_eq_of_ne (Ne.symm h), map_zero, if_neg h]

set_option maxHeartbeats 1000000 in
/-- The base-changed comultiplication on a one-component idempotent
(PROVEN): `Δ(1 ⊗ e_c) = ∑ⱼ (1 ⊗ e_{c−j}) ⊗ (1 ⊗ e_j)`. -/
theorem kummerBaseComul_single_one (c : ZMod p) :
    Coalgebra.comul (R := K)
        (TensorProduct.tmul R (1 : K) (Pi.single c 1 : KummerAlg R p u)) =
      ∑ j : ZMod p,
        TensorProduct.tmul K
          (TensorProduct.tmul R (1 : K)
            (Pi.single (c - j) 1 : KummerAlg R p u))
          (TensorProduct.tmul R (1 : K)
            (Pi.single j 1 : KummerAlg R p u)) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply,
    show Coalgebra.comul (R := R) (Pi.single c 1 : KummerAlg R p u) =
      kummerComul R p u (Pi.single c 1) from rfl,
    kummerComul_single_one_eq, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

set_option maxHeartbeats 1000000 in
/-- The base-changed comultiplication on a one-component root (PROVEN):
`Δ(1 ⊗ single_c x) = ∑ⱼ (1 ⊗ single_{c−j}(u^{−ε}·x)) ⊗ (1 ⊗ single_j x)`
with the carry scalar folded into the left leg. -/
theorem kummerBaseComul_single_root (c : ZMod p) :
    Coalgebra.comul (R := K)
        (TensorProduct.tmul R (1 : K)
          (Pi.single c (kummerRoot R p u c) : KummerAlg R p u)) =
      ∑ j : ZMod p,
        TensorProduct.tmul K
          (TensorProduct.tmul R (1 : K)
            (Pi.single (c - j)
              ((((u⁻¹ : Rˣ) : R) ^
                (if (c - j).val + j.val < p then 0 else 1)) •
                kummerRoot R p u (c - j)) : KummerAlg R p u))
          (TensorProduct.tmul R (1 : K)
            (Pi.single j (kummerRoot R p u j) : KummerAlg R p u)) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply,
    show Coalgebra.comul (R := R)
        (Pi.single c (kummerRoot R p u c) : KummerAlg R p u) =
      kummerComul R p u (Pi.single c (kummerRoot R p u c)) from rfl,
    kummerComul_single_root_eq]
  have hterm : ∀ j : ZMod p,
      ((((u⁻¹ : Rˣ) : R) ^ (if (c - j).val + j.val < p then 0 else 1)) •
        TensorProduct.tmul R
          (Pi.single (c - j) (kummerRoot R p u (c - j)) : KummerAlg R p u)
          (Pi.single j (kummerRoot R p u j) : KummerAlg R p u)) =
      TensorProduct.tmul R
        (Pi.single (c - j)
          ((((u⁻¹ : Rˣ) : R) ^
            (if (c - j).val + j.val < p then 0 else 1)) •
            kummerRoot R p u (c - j)) : KummerAlg R p u)
        (Pi.single j (kummerRoot R p u j) : KummerAlg R p u) := by
    intro j
    rw [TensorProduct.smul_tmul', Pi.single_smul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

set_option maxHeartbeats 1000000 in
/-- **The convolution identity is the identity point `(0, 1)`**
(PROVEN — the counit of the base change evaluates the identity
point). -/
theorem kummerPointHom_conv_one :
    (1 : WithConv (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)) =
      WithConv.toConv (kummerPointHom R K Ω p u 0 1 (by
        rw [one_pow, ZMod.val_zero, pow_zero, map_one])) := by
  apply WithConv.ext
  refine kummerPointHom_ext R K Ω p u (fun c => ?_) (fun c => ?_)
  · rw [AlgHom.convOne_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply,
      show Coalgebra.counit (R := R) (Pi.single c 1 : KummerAlg R p u) =
        kummerCounit R p u (Pi.single c 1) from rfl,
      kummerPointHom_single_one]
    by_cases hc : c = 0
    · subst hc
      rw [kummerCounit_single_zero_one, if_pos rfl, one_smul, map_one]
    · rw [kummerCounit_single_of_ne R p u hc, if_neg hc, zero_smul, map_zero]
  · rw [AlgHom.convOne_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply,
      show Coalgebra.counit (R := R)
          (Pi.single c (kummerRoot R p u c) : KummerAlg R p u) =
        kummerCounit R p u (Pi.single c (kummerRoot R p u c)) from rfl,
      kummerPointHom_single_root]
    by_cases hc : c = 0
    · subst hc
      rw [kummerCounit_single_zero_root, if_pos rfl, one_smul, map_one]
    · rw [kummerCounit_single_of_ne R p u hc, if_neg hc, zero_smul, map_zero]

set_option maxHeartbeats 2000000 in
/-- **The convolution product of two points is the carried point
product** (PROVEN — evaluate both sides on the component idempotents
and roots through the base-changed comultiplication): the explicit
model realizes the group law `(i,s)·(j,t) = (i+j, s·t·u^{−ε})`. -/
theorem kummerPointHom_conv_mul (i j : ZMod p) (s t : Ω)
    (hs : s ^ p = algebraMap R Ω ((u : R) ^ i.val))
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ j.val)) :
    WithConv.toConv (kummerPointHom R K Ω p u i s hs) *
      WithConv.toConv (kummerPointHom R K Ω p u j t ht) =
      WithConv.toConv (kummerPointHom R K Ω p u (i + j)
        (s * t * algebraMap R Ω (((u⁻¹ : Rˣ) : R) ^
          (if i.val + j.val < p then 0 else 1)))
        (kummerPointMul_relation R Ω p u i j s t hs ht)) := by
  apply WithConv.ext
  refine kummerPointHom_ext R K Ω p u (fun c => ?_) (fun c => ?_)
  · -- the component idempotents
    rw [AlgHom.convMul_apply, kummerBaseComul_single_one, map_sum,
      Finset.sum_congr rfl (fun j' _ => by
        rw [Algebra.TensorProduct.lift_tmul, kummerPointHom_single_one,
          kummerPointHom_single_one]),
      Finset.sum_eq_single j
        (fun j' _ hj' => by rw [if_neg hj', mul_zero])
        (fun hj => absurd (Finset.mem_univ j) hj),
      if_pos rfl, mul_one, kummerPointHom_single_one]
    by_cases hc : c = i + j
    · subst hc
      rw [if_pos (add_sub_cancel_right i j), if_pos rfl]
    · rw [if_neg (fun h : c - j = i => hc (sub_eq_iff_eq_add.mp h)),
        if_neg hc]
  · -- the component roots
    rw [AlgHom.convMul_apply, kummerBaseComul_single_root, map_sum,
      Finset.sum_congr rfl (fun j' _ => by
        rw [Algebra.TensorProduct.lift_tmul,
          kummerPointHom_single_smul_root, kummerPointHom_single_root]),
      Finset.sum_eq_single j
        (fun j' _ hj' => by rw [if_neg hj', mul_zero])
        (fun hj => absurd (Finset.mem_univ j) hj),
      if_pos rfl, kummerPointHom_single_root]
    by_cases hc : c = i + j
    · subst hc
      rw [add_sub_cancel_right, if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg (fun h : c - j = i => hc (sub_eq_iff_eq_add.mp h)),
        zero_mul, if_neg hc]

/-- Composition with a Galois automorphism transports the point
`(i, t)` to `(i, σt)` (PROVEN — `σ` fixes the generator values' index
structure and moves the root value). -/
theorem kummerPointHom_comp_algEquiv (σ : Ω ≃ₐ[K] Ω) (i : ZMod p) (t : Ω)
    (ht : t ^ p = algebraMap R Ω ((u : R) ^ i.val)) :
    σ.toAlgHom.comp (kummerPointHom R K Ω p u i t ht) =
      kummerPointHom R K Ω p u i (σ t) (by
        rw [← map_pow, ht, IsScalarTower.algebraMap_apply R K Ω]
        exact σ.commutes _) := by
  refine kummerPointHom_ext R K Ω p u (fun j => ?_) (fun j => ?_)
  · rw [AlgHom.comp_apply, kummerPointHom_single_one,
      kummerPointHom_single_one, apply_ite σ.toAlgHom, map_one, map_zero]
  · rw [AlgHom.comp_apply, kummerPointHom_single_root,
      kummerPointHom_single_root, apply_ite σ.toAlgHom, map_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The points of the Kummer algebra are the `p`-torsion of `Ωˣ/Qᶻ`**
(PROVEN for any field extension `Ω/K` and recentring witness
`u = Q·w⁻ᵖ` with `Q` of infinite order): the classification of the
points, the carry group law of the convolution product, and the
assignment `(i,t) ↦ [wⁱ·t]` assemble into a group isomorphism onto the
`p`-torsion of `Ωˣ/Qᶻ`, equivariant for every `K`-automorphism of `Ω`
(stated through unit representatives). -/
theorem exists_kummerPointsEquiv (Q w : Kˣ)
    (hQ : ∀ n : ℤ, Q ^ n = 1 → n = 0)
    (hu : algebraMap R K ((u : Rˣ) : R) = ((Q * w⁻¹ ^ p : Kˣ) : K)) :
    ∃ (f : Additive (WithConv (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)) ≃+
        AddSubgroup.torsionBy (Additive (Ωˣ ⧸ Subgroup.zpowers
          (Units.map (algebraMap K Ω).toMonoidHom Q))) ((p : ℕ) : ℤ)),
      ∀ (σ : Ω ≃ₐ[K] Ω)
        (φ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω) (u' : Ωˣ),
        ((f (Additive.ofMul (WithConv.toConv φ)) :
            AddSubgroup.torsionBy (Additive (Ωˣ ⧸ Subgroup.zpowers
              (Units.map (algebraMap K Ω).toMonoidHom Q))) ((p : ℕ) : ℤ)) :
          Additive (Ωˣ ⧸ Subgroup.zpowers
            (Units.map (algebraMap K Ω).toMonoidHom Q))) =
          Additive.ofMul ↑u' →
        ((f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
            AddSubgroup.torsionBy (Additive (Ωˣ ⧸ Subgroup.zpowers
              (Units.map (algebraMap K Ω).toMonoidHom Q))) ((p : ℕ) : ℤ)) :
          Additive (Ωˣ ⧸ Subgroup.zpowers
            (Units.map (algebraMap K Ω).toMonoidHom Q))) =
          Additive.ofMul
            ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u') := by
  classical
  -- images of the recentring data in `Ωˣ`
  set Qb : Ωˣ := Units.map (algebraMap K Ω).toMonoidHom Q
  set wb : Ωˣ := Units.map (algebraMap K Ω).toMonoidHom w
  set ub : Ωˣ := Units.map (algebraMap R Ω).toMonoidHom u
  -- the recentring identity in `Ωˣ`
  have hubQ : ub = Qb * wb⁻¹ ^ p := by
    apply Units.ext
    show algebraMap R Ω ((u : Rˣ) : R) = ((Qb * wb⁻¹ ^ p : Ωˣ) : Ω)
    rw [IsScalarTower.algebraMap_apply R K Ω, hu, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow,
      map_inv₀, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    rfl
  have hwp : wb ^ p * ub = Qb := by
    rw [hubQ, mul_comm Qb (wb⁻¹ ^ p), ← mul_assoc, ← mul_pow,
      mul_inv_cancel, one_pow, one_mul]
  -- `Q` has infinite order in `Ωˣ`
  have hQb_inf : ∀ n : ℤ, Qb ^ n = 1 → n = 0 := by
    intro n hn
    refine hQ n (Units.ext ?_)
    have h1 : ((Q ^ n : Kˣ) : K) = 1 := by
      apply (algebraMap K Ω).injective
      rw [map_one]
      calc algebraMap K Ω ((Q ^ n : Kˣ) : K)
          = ((Units.map (algebraMap K Ω).toMonoidHom (Q ^ n) : Ωˣ) : Ω) := rfl
        _ = ((Qb ^ n : Ωˣ) : Ω) := by rw [map_zpow]
        _ = 1 := by rw [hn, Units.val_one]
    rw [Units.val_one]
    exact h1
  -- point data of every hom, by the classification
  have hclass := fun φ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω =>
    exists_kummerPointHom_eq R K Ω p u φ
  choose idx rt hrt heq using hclass
  have hne : ∀ φ, rt φ ≠ 0 := by
    intro φ h0
    have h1 := hrt φ
    rw [h0, zero_pow (NeZero.ne p)] at h1
    exact (IsUnit.map (algebraMap R Ω)
      (u.isUnit.pow (idx φ).val)).ne_zero h1.symm
  -- the unit attached to a point, and its `p`-th power
  set U : (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω) → Ωˣ := fun φ =>
    wb ^ (idx φ).val * Units.mk0 (rt φ) (hne φ) with hU_def
  have hUp : ∀ φ, U φ ^ p = Qb ^ (idx φ).val := by
    intro φ
    have hmk : (Units.mk0 (rt φ) (hne φ)) ^ p = ub ^ (idx φ).val := by
      apply Units.ext
      show rt φ ^ p = ((ub ^ (idx φ).val : Ωˣ) : Ω)
      rw [Units.val_pow_eq_pow_val, hrt φ, map_pow]
      rfl
    rw [hU_def]
    show (wb ^ (idx φ).val * Units.mk0 (rt φ) (hne φ)) ^ p = Qb ^ (idx φ).val
    rw [mul_pow, hmk, ← pow_mul, mul_comm (idx φ).val p, pow_mul, ← mul_pow,
      hwp]
  -- the class map to `Ωˣ/Qᶻ`
  set cl : (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω) →
      Ωˣ ⧸ Subgroup.zpowers Qb := fun φ => QuotientGroup.mk (U φ) with hcl_def
  have hcl_torsion : ∀ φ, ((p : ℕ) : ℤ) • Additive.ofMul (cl φ) = 0 := by
    intro φ
    have h1 : cl φ ^ (p : ℕ) = 1 := by
      rw [hcl_def]
      show (QuotientGroup.mk (U φ) : Ωˣ ⧸ Subgroup.zpowers Qb) ^ (p : ℕ) = 1
      have h2 : (QuotientGroup.mk (U φ ^ p) :
          Ωˣ ⧸ Subgroup.zpowers Qb) = 1 := by
        rw [hUp φ, QuotientGroup.eq_one_iff]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers Qb) (idx φ).val
      exact h2
    rw [← ofMul_zpow, zpow_natCast, h1]
    rfl
  -- the point data of a convolution product
  have hdata_mul : ∀ a b :
      WithConv (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω),
      idx ((a * b).ofConv) = idx a.ofConv + idx b.ofConv ∧
      rt ((a * b).ofConv) = rt a.ofConv * rt b.ofConv *
        algebraMap R Ω (((u⁻¹ : Rˣ) : R) ^
          (if (idx a.ofConv).val + (idx b.ofConv).val < p then 0 else 1)) := by
    intro a b
    have hab : a * b = WithConv.toConv (kummerPointHom R K Ω p u
        (idx a.ofConv + idx b.ofConv)
        (rt a.ofConv * rt b.ofConv * algebraMap R Ω (((u⁻¹ : Rˣ) : R) ^
          (if (idx a.ofConv).val + (idx b.ofConv).val < p then 0 else 1)))
        (kummerPointMul_relation R Ω p u _ _ _ _ (hrt a.ofConv)
          (hrt b.ofConv))) := by
      conv_lhs => rw [← WithConv.toConv_ofConv a, ← WithConv.toConv_ofConv b,
        heq a.ofConv, heq b.ofConv]
      exact kummerPointHom_conv_mul R K Ω p u _ _ _ _ (hrt a.ofConv)
        (hrt b.ofConv)
    have h3 : (a * b).ofConv = kummerPointHom R K Ω p u
        (idx a.ofConv + idx b.ofConv)
        (rt a.ofConv * rt b.ofConv * algebraMap R Ω (((u⁻¹ : Rˣ) : R) ^
          (if (idx a.ofConv).val + (idx b.ofConv).val < p then 0 else 1)))
        (kummerPointMul_relation R Ω p u _ _ _ _ (hrt a.ofConv)
          (hrt b.ofConv)) := by
      rw [hab]
    exact kummerPointHom_inj R K Ω p u
      (((heq ((a * b).ofConv)).symm.trans h3))
  -- the inverse image of `u` as a unit value
  have hui : algebraMap R Ω ((u⁻¹ : Rˣ) : R) = (((ub : Ωˣ) : Ω))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    rfl
  -- multiplicativity of the class map through the carry
  have hcl_mul : ∀ a b :
      WithConv (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω),
      cl ((a * b).ofConv) = cl a.ofConv * cl b.ofConv := by
    intro a b
    obtain ⟨hi, hr⟩ := hdata_mul a b
    have hval := kummer_val_add_carry p (idx a.ofConv) (idx b.ofConv)
    -- the carried unit identity
    have hmk : Units.mk0 (rt ((a * b).ofConv)) (hne ((a * b).ofConv)) =
        Units.mk0 (rt a.ofConv) (hne a.ofConv) *
          Units.mk0 (rt b.ofConv) (hne b.ofConv) *
        ub⁻¹ ^ (if (idx a.ofConv).val + (idx b.ofConv).val < p
          then 0 else 1) := by
      apply Units.ext
      show rt ((a * b).ofConv) = _
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val, hr, map_pow, hui]
      rfl
    have hUab : U ((a * b).ofConv) *
        Qb ^ (if (idx a.ofConv).val + (idx b.ofConv).val < p then 0 else 1) =
        U a.ofConv * U b.ofConv := by
      rw [hU_def]
      show wb ^ (idx ((a * b).ofConv)).val *
          Units.mk0 (rt ((a * b).ofConv)) (hne ((a * b).ofConv)) * Qb ^ _ =
        (wb ^ (idx a.ofConv).val * Units.mk0 (rt a.ofConv) (hne a.ofConv)) *
        (wb ^ (idx b.ofConv).val * Units.mk0 (rt b.ofConv) (hne b.ofConv))
      rw [hmk, hi]
      by_cases hlt : (idx a.ofConv).val + (idx b.ofConv).val < p
      · rw [if_pos hlt, Nat.mul_zero, Nat.add_zero] at hval
        rw [if_pos hlt, pow_zero, pow_zero, mul_one, mul_one]
        conv_rhs => rw [mul_mul_mul_comm, ← pow_add, hval]
      · rw [if_neg hlt, Nat.mul_one] at hval
        rw [if_neg hlt, pow_one, pow_one]
        conv_rhs => rw [mul_mul_mul_comm, ← pow_add, hval]
        rw [pow_add, ← hwp, mul_mul_mul_comm, inv_mul_cancel_right]
    rw [hcl_def]
    show (QuotientGroup.mk (U ((a * b).ofConv)) :
        Ωˣ ⧸ Subgroup.zpowers Qb) =
      QuotientGroup.mk (U a.ofConv) * QuotientGroup.mk (U b.ofConv)
    rw [← QuotientGroup.mk_mul, ← hUab]
    apply (QuotientGroup.eq).mpr
    rw [inv_mul_cancel_left]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers Qb) _
  -- the class map is injective on points
  have hcl_inj : ∀ φ ψ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω,
      cl φ = cl ψ → φ = ψ := by
    intro φ ψ hcl
    have h2 : (U φ)⁻¹ * U ψ ∈ Subgroup.zpowers Qb := (QuotientGroup.eq).mp hcl
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h2
    have hUeq : U ψ = U φ * Qb ^ m := by
      rw [hm, mul_inv_cancel_left]
    have h3 : Qb ^ (((idx ψ).val : ℤ)) =
        Qb ^ ((((idx φ).val : ℕ) : ℤ) + m * (p : ℤ)) := by
      rw [zpow_natCast, ← hUp ψ, hUeq, mul_pow, hUp φ, zpow_add,
        zpow_natCast, zpow_mul, zpow_natCast]
    have h4 : Qb ^ ((((idx ψ).val : ℕ) : ℤ) -
        ((((idx φ).val : ℕ) : ℤ) + m * (p : ℤ))) = 1 := by
      rw [zpow_sub, h3, mul_inv_cancel]
    have h5 := hQb_inf _ h4
    have hival_lt : (((idx ψ).val : ℕ) : ℤ) < (p : ℤ) := by
      exact_mod_cast ZMod.val_lt (idx ψ)
    have hival_lt' : (((idx φ).val : ℕ) : ℤ) < (p : ℤ) := by
      exact_mod_cast ZMod.val_lt (idx φ)
    have hival_nonneg : (0 : ℤ) ≤ (((idx ψ).val : ℕ) : ℤ) :=
      Int.natCast_nonneg _
    have hival_nonneg' : (0 : ℤ) ≤ (((idx φ).val : ℕ) : ℤ) :=
      Int.natCast_nonneg _
    have hppos : (0 : ℤ) < (p : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    have hidx : idx ψ = idx φ := by
      rw [hm0, zero_mul, add_zero] at h5
      have h6 : (idx ψ).val = (idx φ).val := by omega
      have h7 : (((idx ψ).val : ℕ) : ZMod p) = (((idx φ).val : ℕ) : ZMod p) := by
        rw [h6]
      rwa [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id]
        at h7
    have hUeq' : U ψ = U φ := by
      rw [hUeq, hm0, zpow_zero, mul_one]
    have hrt_eq : rt ψ = rt φ := by
      have h7 := congrArg (fun z : Ωˣ => (z : Ω)) hUeq'
      simp only [hU_def] at h7
      rw [hidx, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_mk0, Units.val_mk0] at h7
      exact mul_left_cancel₀
        (pow_ne_zero _ (Units.ne_zero wb)) h7
    have hpteq : kummerPointHom R K Ω p u (idx φ) (rt φ) (hrt φ) =
        kummerPointHom R K Ω p u (idx ψ) (rt ψ) (hrt ψ) := by
      refine kummerPointHom_ext R K Ω p u (fun j => ?_) (fun j => ?_)
      · rw [kummerPointHom_single_one, kummerPointHom_single_one, hidx]
      · rw [kummerPointHom_single_root, kummerPointHom_single_root, hidx,
          hrt_eq]
    rw [heq φ, heq ψ, hpteq]
  -- the identity point has trivial class
  have hcl_one : cl ((1 : WithConv
      (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)).ofConv) = 1 := by
    have hone : ((1 : WithConv
        (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)).ofConv) =
        kummerPointHom R K Ω p u 0 1 (by
          rw [one_pow, ZMod.val_zero, pow_zero, map_one]) := by
      rw [kummerPointHom_conv_one R K Ω p u]
    have hd := kummerPointHom_inj R K Ω p u ((heq _).symm.trans hone)
    have hU1 : U ((1 : WithConv
        (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)).ofConv) = 1 := by
      simp only [hU_def]
      rw [hd.1, ZMod.val_zero, pow_zero, one_mul]
      apply Units.ext
      rw [Units.val_mk0, hd.2, Units.val_one]
    rw [hcl_def]
    show (QuotientGroup.mk (U ((1 : WithConv
        (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)).ofConv)) :
      Ωˣ ⧸ Subgroup.zpowers Qb) = 1
    rw [hU1]
    rfl
  -- the additive hom to the torsion subgroup
  set F : Additive (WithConv (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)) →+
      AddSubgroup.torsionBy (Additive (Ωˣ ⧸ Subgroup.zpowers Qb))
        ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨Additive.ofMul (cl (Additive.toMul x).ofConv),
        hcl_torsion (Additive.toMul x).ofConv⟩
      map_zero' := Subtype.ext (by
        show Additive.ofMul (cl ((1 : WithConv
          (TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω)).ofConv)) = 0
        rw [hcl_one]
        exact ofMul_one)
      map_add' := fun a b => Subtype.ext (congrArg Additive.ofMul
        (hcl_mul (Additive.toMul a) (Additive.toMul b))) }
  -- injectivity, through the point classification
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h1 : cl (Additive.toMul x).ofConv = cl (Additive.toMul y).ofConv := by
      have h2 := congrArg (fun z : AddSubgroup.torsionBy
          (Additive (Ωˣ ⧸ Subgroup.zpowers Qb)) ((p : ℕ) : ℤ) =>
        (z : Additive (Ωˣ ⧸ Subgroup.zpowers Qb))) hxy
      exact Additive.ofMul.injective h2
    have h3 := hcl_inj _ _ h1
    have h4 : Additive.toMul x = Additive.toMul y := by
      rw [← WithConv.toConv_ofConv (Additive.toMul x),
        ← WithConv.toConv_ofConv (Additive.toMul y), h3]
    exact Additive.toMul.injective h4
  -- surjectivity: recentre a torsion class to a point
  have hFsurj : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hxp : Additive.toMul x ^ (p : ℕ) = 1 := by
      have h1 : ((p : ℕ) : ℤ) • x = 0 := hx
      have h2 := congrArg Additive.toMul h1
      rw [toMul_zsmul, zpow_natCast] at h2
      exact h2
    have h3 : v ^ (p : ℕ) ∈ Subgroup.zpowers Qb := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk (v ^ (p : ℕ)) : Ωˣ ⧸ Subgroup.zpowers Qb) = 1
      rw [QuotientGroup.mk_pow, hv]
      exact hxp
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h3
    set i : ZMod p := ((a : ℤ) : ZMod p) with hi_def
    have hival : ((i.val : ℕ) : ℤ) = a % (p : ℤ) := by
      rw [hi_def]
      exact ZMod.val_intCast a
    have hdiv : (p : ℤ) * (a / (p : ℤ)) + ((i.val : ℕ) : ℤ) = a := by
      rw [hival]
      exact Int.mul_ediv_add_emod a (p : ℤ)
    set m : ℤ := a / (p : ℤ)
    set tu : Ωˣ := v * (wb ^ i.val)⁻¹ * (Qb ^ m)⁻¹ with htu_def
    have htu_p : tu ^ (p : ℕ) = ub ^ i.val := by
      have hz : Qb ^ a * (Qb ^ ((p : ℤ) * m))⁻¹ = Qb ^ ((i.val : ℕ) : ℤ) := by
        rw [← zpow_neg, ← zpow_add]
        congr 1
        linarith [hdiv]
      calc tu ^ (p : ℕ)
          = v ^ (p : ℕ) * ((wb ^ i.val)⁻¹) ^ (p : ℕ) *
            ((Qb ^ m)⁻¹) ^ (p : ℕ) := by
            rw [htu_def, mul_pow, mul_pow]
        _ = Qb ^ a * (wb ^ (i.val * p))⁻¹ * (Qb ^ ((p : ℤ) * m))⁻¹ := by
            rw [← ha, inv_pow, ← pow_mul, inv_pow,
              ← zpow_natCast (Qb ^ m) p, ← zpow_mul, mul_comm m (p : ℤ)]
        _ = Qb ^ ((i.val : ℕ) : ℤ) * (wb ^ (i.val * p))⁻¹ := by
            rw [mul_right_comm, hz]
        _ = ub ^ i.val := by
            rw [zpow_natCast, hubQ, mul_pow, inv_pow, inv_pow, ← pow_mul,
              Nat.mul_comm p i.val]
    have htu_el : ((tu : Ωˣ) : Ω) ^ p = algebraMap R Ω ((u : R) ^ i.val) := by
      have h5 : (((tu ^ (p : ℕ) : Ωˣ)) : Ω) = ((ub ^ i.val : Ωˣ) : Ω) :=
        congrArg Units.val htu_p
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h5
      rw [h5, map_pow]
      rfl
    refine ⟨Additive.ofMul (WithConv.toConv
      (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el)), ?_⟩
    apply Subtype.ext
    show Additive.ofMul (cl (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω)
      htu_el)) = x
    have hd := kummerPointHom_inj R K Ω p u
      (heq (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el))
    have hUψ : U (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el) =
        v * (Qb ^ m)⁻¹ := by
      have hmk0 : Units.mk0
          (rt (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el))
          (hne (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el)) = tu :=
        Units.ext hd.2.symm
      simp only [hU_def]
      rw [hmk0, ← hd.1, htu_def]
      have hcomm : v * (wb ^ i.val)⁻¹ * (Qb ^ m)⁻¹ =
          (wb ^ i.val)⁻¹ * (v * (Qb ^ m)⁻¹) := by
        rw [mul_comm v ((wb ^ i.val)⁻¹), mul_assoc]
      rw [hcomm, mul_inv_cancel_left]
    have hclψ : cl (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω) htu_el) =
        Additive.toMul x := by
      rw [hcl_def]
      show (QuotientGroup.mk (U (kummerPointHom R K Ω p u i ((tu : Ωˣ) : Ω)
        htu_el)) : Ωˣ ⧸ Subgroup.zpowers Qb) = Additive.toMul x
      rw [hUψ, ← hv]
      apply (QuotientGroup.eq).mpr
      have h6 : (v * (Qb ^ m)⁻¹)⁻¹ * v = Qb ^ m := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      rw [h6]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers Qb) m
    rw [hclψ]
    exact ofMul_toMul x
  -- Galois automorphisms fix the recentring data and move the root value
  have hSfix : ∀ (σ : Ω ≃ₐ[K] Ω) (k : Kˣ),
      Units.map σ.toAlgHom.toRingHom.toMonoidHom
        (Units.map (algebraMap K Ω).toMonoidHom k) =
      Units.map (algebraMap K Ω).toMonoidHom k := by
    intro σ k
    apply Units.ext
    show σ.toAlgHom (algebraMap K Ω (k : K)) = algebraMap K Ω (k : K)
    exact σ.toAlgHom.commutes _
  have hSU : ∀ (σ : Ω ≃ₐ[K] Ω)
      (φ : TensorProduct R K (KummerAlg R p u) →ₐ[K] Ω),
      Units.map σ.toAlgHom.toRingHom.toMonoidHom (U φ) =
        U (σ.toAlgHom.comp φ) := by
    intro σ φ
    have hcomp : σ.toAlgHom.comp φ = kummerPointHom R K Ω p u (idx φ)
        (σ (rt φ)) (by
          rw [← map_pow, hrt φ, IsScalarTower.algebraMap_apply R K Ω]
          exact σ.commutes _) := by
      conv_lhs => rw [heq φ]
      exact kummerPointHom_comp_algEquiv R K Ω p u σ (idx φ) (rt φ) (hrt φ)
    have hd := kummerPointHom_inj R K Ω p u
      ((heq (σ.toAlgHom.comp φ)).symm.trans hcomp)
    apply Units.ext
    simp only [hU_def]
    show σ.toAlgHom (((wb ^ (idx φ).val * Units.mk0 (rt φ) (hne φ) :
        Ωˣ)) : Ω) =
      ((wb ^ (idx (σ.toAlgHom.comp φ)).val *
        Units.mk0 (rt (σ.toAlgHom.comp φ)) (hne (σ.toAlgHom.comp φ)) :
        Ωˣ) : Ω)
    rw [Units.val_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, hd.1, Units.val_mk0, Units.val_mk0]
    congr 1
    · congr 1
      exact σ.toAlgHom.commutes (w : K)
    · show σ.toAlgHom (rt φ) = rt (σ.toAlgHom.comp φ)
      rw [hd.2]
      rfl
  -- assemble the equivalence and its equivariance
  refine ⟨AddEquiv.ofBijective F ⟨hFinj, hFsurj⟩, ?_⟩
  intro σ φ u' hrep
  have h1 : Additive.ofMul (cl φ) = Additive.ofMul
      ((QuotientGroup.mk u' : Ωˣ ⧸ Subgroup.zpowers Qb)) := hrep
  have hclφ : cl φ = QuotientGroup.mk u' := Additive.ofMul.injective h1
  have h2 : (U φ)⁻¹ * u' ∈ Subgroup.zpowers Qb := by
    apply (QuotientGroup.eq).mp
    exact hclφ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h2
  have hu' : u' = U φ * Qb ^ m := by
    rw [hm, mul_inv_cancel_left]
  have hgoal : cl (σ.toAlgHom.comp φ) = QuotientGroup.mk
      (Units.map σ.toAlgHom.toRingHom.toMonoidHom u') := by
    rw [hu', map_mul, map_zpow, hSU σ φ, hSfix σ Q, hcl_def]
    show (QuotientGroup.mk (U (σ.toAlgHom.comp φ)) :
        Ωˣ ⧸ Subgroup.zpowers Qb) =
      QuotientGroup.mk (U (σ.toAlgHom.comp φ) * Qb ^ m)
    apply (QuotientGroup.eq).mpr
    rw [inv_mul_cancel_left]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers Qb) m
  exact congrArg Additive.ofMul hgoal

end KummerPoints

open TensorProduct ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Étale generic fibre of the Kummer algebra** (DERIVED 2026-07-23
from the generic `kummerAlg_etale`: over the characteristic-zero
completed field each Kummer component base-changes to the standard
étale algebra of the pair `⟨xᵖ − uⁱ, 1⟩`, and étaleness passes through
the finite product and the tensor distribution). -/
theorem kummerAlg_etale_adic {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (u : (𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])ˣ) :
    haveI : NeZero p := ⟨hp'.ne_zero⟩
    Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]]
        (KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat] p u)) := by
  haveI : NeZero p := ⟨hp'.ne_zero⟩
  haveI : CharZero (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) :=
    charZero_of_injective_algebraMap
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)).injective)
  exact kummerAlg_etale
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
    (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) p u

open TensorProduct ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The points of the Kummer algebra are the `p`-torsion of
`Ωˣ/Qᶻ`** (sorry node — the remaining core of the split Kummer leaf,
now against the EXPLICIT model): a `K`-point of the generic fibre of
`KummerAlg 𝒪 p u` is a component index `i` together with a `p`-th root
`t` of `uⁱ` in `Ω` (`AdjoinRoot.liftAlgHom` classification of maps out
of each component, projected along the product decomposition); sending
`(i, t) ↦ [wⁱ·t]` is a group isomorphism onto the `p`-torsion of
`Ωˣ/Qᶻ` — a homomorphism by the carry computation `wⁱ·s·wʲ·t·q^{−ε} ≡
w^{i+j−pε}·(s·t·u^{−ε})`, injective because `v(w) ≠ 1` forces `i = 0`
then `t = 1`, surjective because `vᵖ = Qᵃ` recentres to
`(a mod p, v·w^{−a}·Q^{−⌊a/p⌋})` — and it is Galois-equivariant
because `w` and `u` lie in `K`. Equivariance is stated through unit
representatives as in `exists_kummerTorsionPackage`. -/
theorem exists_kummerAlg_pointsEquiv {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (Q w : (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ)
    (_hQ : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((Q : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) < 1)
    (u : (𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])ˣ)
    (_hu : (((u : 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)) =
      ((Q * w⁻¹ ^ p : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)) :
    haveI : NeZero p := ⟨hp'.ne_zero⟩
    ∃ (f : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]]
          (KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat] p u))
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
        AddSubgroup.torsionBy (Additive
          ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
          Subgroup.zpowers (Units.map (algebraMap
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
          ((p : ℕ) : ℤ)),
      ∀ (σ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))
        (φ : ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]]
          (KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat] p u))
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
        (u' : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ),
        ((f (Additive.ofMul (WithConv.toConv φ)) :
          AddSubgroup.torsionBy (Additive
            ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
            ((p : ℕ) : ℤ)) :
          Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q))) =
          Additive.ofMul ↑u' →
        ((f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          AddSubgroup.torsionBy (Additive
            ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
            ((p : ℕ) : ℤ)) :
          Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q))) =
          Additive.ofMul
            ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u') := by
  haveI : NeZero p := ⟨hp'.ne_zero⟩
  -- `Q` has infinite order: its valuation is strictly below `1`
  have hQinf : ∀ n : ℤ, Q ^ n = 1 → n = 0 := by
    intro n hn
    by_contra hn0
    have hv1 : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
        ((Q : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ^ n = 1 := by
      have h2 : ((Q ^ n : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
        rw [hn, Units.val_one]
      have h3 := congrArg (ValuativeRel.valuation
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)) h2
      rw [map_one, Units.val_zpow_eq_zpow_val, map_zpow₀] at h3
      exact h3
    rcases lt_trichotomy n 0 with hneg | h0 | hpos
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
      have hk0 : k ≠ 0 := by omega
      rw [hk, zpow_neg, zpow_natCast, inv_eq_one] at hv1
      exact absurd hv1 (ne_of_lt (pow_lt_one₀ zero_le _hQ hk0))
    · exact hn0 h0
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.natAbs, by omega⟩
      have hk0 : k ≠ 0 := by omega
      rw [hk, zpow_natCast] at hv1
      exact absurd hv1 (ne_of_lt (pow_lt_one₀ zero_le _hQ hk0))
  exact exists_kummerPointsEquiv
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
    (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
    p u Q w hQinf _hu

open TensorProduct ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Kummer torsion package** (the CURVE-FREE local Kummer content
of the split multiplicative case, extracted 2026-07-22 from
`torsionFlatPackage_of_split_adic`; DERIVED later the same day from the
explicit model: the skeleton below instantiates `H := KummerAlg 𝒪 p u`
with its PROVEN Hopf structure (all five axioms), PROVEN
finiteness/freeness/flatness and PROVEN étale generic fibre
(`kummerAlg_etale_adic`), leaving as the SINGLE sorried leaf the points
computation `exists_kummerAlg_pointsEquiv`; no elliptic curve appears —
the statement is pure Kummer theory of the completed local field):
given `Q ∈ ℚ_pˆˣ` of valuation `< 1` together with a recentring
witness `w` making `u = Q·w⁻ᵖ` a UNIT of the completed integers, the
`p`-torsion of `Ω̂ˣ/Qᶻ` is, Galois-equivariantly, the group of
`Ω̂`-points of (the generic fibre of) a finite flat `𝒪`-Hopf algebra.
Content: the `p`-torsion of `Ω̂ˣ/Qᶻ` is `⟨ζ_p, w·u^{1/p}⟩` — an
extension of `ℤ/p` by `μ_p`, *peu ramifiée* because `u` is a unit; the
model is the explicit Kummer group scheme with Hopf algebra
`∏_{i<p} 𝒪[x]/(xᵖ − uⁱ)` (finite free of rank `p²`, étale generic
fibre in characteristic zero), whose `Ω̂`-points `(i, t) ↦ [wⁱ·t]`
(where `tᵖ = uⁱ`) are exactly the `p²` torsion classes — injectively
because `v(w) ≠ 1`, surjectively because `vᵖ = Qᵃ` forces
`v ≡ wᵃ·t mod Qᶻ` with `tᵖ = uᵃ` — equivariantly because `w, u ∈ ℚ_pˆ`
are Galois-fixed. Equivariance is stated through representatives: if
`f φ` is the class of `u'`, then `f (σ ∘ φ)` is the class of
`σ u'`. -/
theorem exists_kummerTorsionPackage {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (Q w : (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ)
    (hQ : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((Q : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) < 1)
    (hmem : (((Q * w⁻¹ ^ p :
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)) ∈
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
    (hunit : IsUnit (⟨_, hmem⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) :
    ∃ (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H)
      (_ : Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H)
      (_ : Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H)
      (_ : Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] H))
      (f : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] H)
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
        AddSubgroup.torsionBy (Additive
          ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
          Subgroup.zpowers (Units.map (algebraMap
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
          ((p : ℕ) : ℤ)),
      ∀ (σ : AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))
        (φ : ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] H)
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
        (u : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ),
        ((f (Additive.ofMul (WithConv.toConv φ)) :
          AddSubgroup.torsionBy (Additive
            ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
            ((p : ℕ) : ℤ)) :
          Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q))) =
          Additive.ofMul ↑u →
        ((f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          AddSubgroup.torsionBy (Additive
            ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q)))
            ((p : ℕ) : ℤ)) :
          Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
            Subgroup.zpowers (Units.map (algebraMap
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom Q))) =
          Additive.ofMul
            ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u) := by
  classical
  haveI : NeZero p := ⟨hp'.ne_zero⟩
  -- the recentred parameter as a unit of the valuative integer ring
  -- (spelling transport `adicCompletionIntegers → 𝒪[ℚ_pˆ]` on the
  -- element and on its inverse)
  obtain ⟨vu, hvu⟩ := hunit
  have hval : ((vu : HeightOneSpectrum.adicCompletionIntegers ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) :
      HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) =
      ((Q * w⁻¹ ^ p : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hvu]
  have hxmem : ((Q * w⁻¹ ^ p : (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ∈
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] :=
    mem_integer_of_mem_adicCompletionIntegers hp' hmem
  have hymem : (((vu⁻¹ : (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) :
      HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ∈
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] :=
    mem_integer_of_mem_adicCompletionIntegers hp'
      ((vu⁻¹ : (HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat).2
  have hxy : ((Q * w⁻¹ ^ p : (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) *
      (((vu⁻¹ : (HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
    rw [← hval]
    exact congrArg Subtype.val (Units.mul_inv vu)
  have hyx : (((vu⁻¹ : (HeightOneSpectrum.adicCompletionIntegers ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
      HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) :
      HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) *
      ((Q * w⁻¹ ^ p : (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) = 1 := by
    rw [← hval]
    exact congrArg Subtype.val (Units.inv_mul vu)
  let u₀ : (𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])ˣ :=
    { val := ⟨_, hxmem⟩
      inv := ⟨_, hymem⟩
      val_inv := Subtype.ext hxy
      inv_val := Subtype.ext hyx }
  -- the explicit Kummer Hopf model with its points computation
  obtain ⟨f, hf⟩ := exists_kummerAlg_pointsEquiv hp' Q w hQ u₀ rfl
  haveI hcompfin : ∀ i : ZMod p, Module.Finite
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (KummerComponent 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀ i) := fun i =>
    kummerComponent_finite _ p u₀ i
  haveI hcompfree : ∀ i : ZMod p, Module.Free
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (KummerComponent 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀ i) := fun i =>
    kummerComponent_free _ p u₀ i
  haveI hfin : Module.Finite
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀) := Module.Finite.pi
  haveI hfree : Module.Free
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀) :=
    Module.Free.pi 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
      (KummerComponent 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀)
  exact ⟨KummerAlg 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] p u₀,
    inferInstance, inferInstance, hfin, Module.Flat.of_free,
    kummerAlg_etale_adic hp' u₀, f, hf⟩

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The split Kummer package** (DERIVED 2026-07-22 from the
curve-free Kummer leaf `exists_kummerTorsionPackage` and the PROVEN
uniformization `exists_tateEquivSepClosure`): for the completed base
change with split multiplicative reduction and a recentring witness
`w'` making `u = q_E·w'⁻ᵖ` a UNIT of the completed integers, the
`p`-torsion carries a `TorsionFlatPackage` over `𝒪[ℚ_pˆ]`. Glue proven
here: the Kummer leaf provides the finite flat Hopf model whose
`Ω̂`-points are the `p`-torsion of `Ω̂ˣ/q_Eᶻ`; the uniformization
restricts to an equivariant isomorphism from that torsion onto `E[p]`
(an `AddEquiv` maps `p`-torsion onto `p`-torsion), and equivariance
composes through a chosen unit representative of each class. -/
theorem WeierstrassCurve.torsionFlatPackage_of_split_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime] (_hp2 : p ≠ 2)
    [hsplit : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] :
    ∀ (w' : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ)
        (hmem : (((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).qUnit * w'⁻¹ ^ p :
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
            HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ∈
          HeightOneSpectrum.adicCompletionIntegers ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat),
        IsUnit (⟨_, hmem⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) →
        WeierstrassCurve.TorsionFlatPackage
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
          p
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  intro w' hmem hunit
  -- the curve-free Kummer package at the recentred Tate parameter
  obtain ⟨H, i1, i2, i3, i4, i5, f0, hf0⟩ :=
    exists_kummerTorsionPackage hp'
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).qUnit w'
      (WeierstrassCurve.valuation_q_lt_one
        (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))))
      hmem hunit
  -- the uniformization witness
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
    (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)))
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
  -- the uniformization restricted to the `p`-torsion subgroups
  let eT : AddSubgroup.torsionBy (Additive
        ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
        Subgroup.zpowers (Units.map (algebraMap
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
          (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).qUnit)))
        ((p : ℕ) : ℤ) ≃+
      AddSubgroup.torsionBy ((E.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨e x.1, by
        have hx : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        show ((p : ℕ) : ℤ) • e x.1 = 0
        rw [← map_zsmul, hx, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have hy : ((p : ℕ) : ℤ) • y.1 = 0 := y.2
        show ((p : ℕ) : ℤ) • e.symm y.1 = 0
        rw [← map_zsmul e.symm ((p : ℕ) : ℤ) y.1, hy, map_zero]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  refine ⟨H, i1, i2, i3, i4, i5, f0.trans eT, ?_⟩
  intro σ φ
  -- a unit representative of the Kummer class of `φ`
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective
    (Additive.toMul (f0 (Additive.ofMul (WithConv.toConv φ))).1)
  have hux : ((f0 (Additive.ofMul (WithConv.toConv φ))).1 :
      Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
        Subgroup.zpowers (Units.map (algebraMap
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
          (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).qUnit))) =
      Additive.ofMul ↑u := by
    rw [hu, ofMul_toMul]
  -- Kummer equivariance at the representative
  have hstep := hf0 σ φ u hux
  -- unfold the composite at both sides and close with the
  -- uniformization equivariance
  show e (f0 (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))).1 =
    WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (e (f0 (Additive.ofMul (WithConv.toConv φ))).1)
  rw [hstep, hux]
  exact (he σ u).symm

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The split Kummer package, local form** (PROVEN 2026-07-23 by the
same assembly as `torsionFlatPackage_of_split_adic` — the proof never
uses globality of the curve — stated for an arbitrary local curve so
that it applies to the minimal model of the quadratic twist in the
nonsplit case). -/
theorem WeierstrassCurve.torsionFlatPackage_of_split_adic'
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic]
    [hsplit : X.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] :
    ∀ (w' : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ)
      (hmem : ((X.qUnit * w'⁻¹ ^ p :
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ∈
        HeightOneSpectrum.adicCompletionIntegers ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat),
      IsUnit (⟨_, hmem⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) →
      WeierstrassCurve.TorsionFlatPackage
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        X p
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  intro w' hmem hunit
  -- the curve-free Kummer package at the recentred Tate parameter
  obtain ⟨H, i1, i2, i3, i4, i5, f0, hf0⟩ :=
    exists_kummerTorsionPackage hp' X.qUnit w'
      (WeierstrassCurve.valuation_q_lt_one X) hmem hunit
  -- the uniformization witness
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
    (E := X)
    (Ω := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
  -- the uniformization restricted to the `p`-torsion subgroups
  let eT : AddSubgroup.torsionBy (Additive
        ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
        Subgroup.zpowers (Units.map (algebraMap
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
          X.qUnit)))
        ((p : ℕ) : ℤ) ≃+
      AddSubgroup.torsionBy (X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨e x.1, by
        have hx : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        show ((p : ℕ) : ℤ) • e x.1 = 0
        rw [← map_zsmul, hx, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have hy : ((p : ℕ) : ℤ) • y.1 = 0 := y.2
        show ((p : ℕ) : ℤ) • e.symm y.1 = 0
        rw [← map_zsmul e.symm ((p : ℕ) : ℤ) y.1, hy, map_zero]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  refine ⟨H, i1, i2, i3, i4, i5, f0.trans eT, ?_⟩
  intro σ φ
  -- a unit representative of the Kummer class of `φ`
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective
    (Additive.toMul (f0 (Additive.ofMul (WithConv.toConv φ))).1)
  have hux : ((f0 (Additive.ofMul (WithConv.toConv φ))).1 :
      Additive ((AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))ˣ ⧸
        Subgroup.zpowers (Units.map (algebraMap
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
          X.qUnit))) =
      Additive.ofMul ↑u := by
    rw [hu, ofMul_toMul]
  -- Kummer equivariance at the representative
  have hstep := hf0 σ φ u hux
  -- unfold the composite at both sides and close with the
  -- uniformization equivariance
  show e (f0 (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))).1 =
    WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (e (f0 (Additive.ofMul (WithConv.toConv φ))).1)
  rw [hstep, hux]
  exact (he σ u).symm

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Package transport along a variable change** (PROVEN 2026-07-23 —
a `VariableChange` over the base field induces a Galois-equivariant
group isomorphism of points over the algebraic closure
(`Affine.Point.equivVariableChangeBaseChange` with its `_galois`
equivariance: the coefficients of the change of variables are fixed by
the Galois action), so a `TorsionFlatPackage` for `C • Y` yields one
for `Y` by composing the points identification; the Hopf model is
unchanged). -/
theorem WeierstrassCurve.torsionFlatPackage_of_variableChange
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (Y : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) [Y.IsElliptic]
    (C : WeierstrassCurve.VariableChange (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) :
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (C • Y) p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) →
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      Y p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  intro hpkg
  obtain ⟨H, i1, i2, i3, i4, i5, f0, hf0⟩ := hpkg
  -- the Galois-equivariant point identification induced by `C`
  let e : ((C • Y)⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point ≃+
      (Y⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).toAffine.Point :=
    WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange Y C
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
  have he := WeierstrassCurve.Affine.Point.equivVariableChangeBaseChange_galois Y C
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
  -- the point identification restricted to the `p`-torsion subgroups
  let eT : AddSubgroup.torsionBy ((C • Y)⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) ≃+
      AddSubgroup.torsionBy (Y⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨e x.1, by
        have hx : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        show ((p : ℕ) : ℤ) • e x.1 = 0
        rw [← map_zsmul, hx, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have hy : ((p : ℕ) : ℤ) • y.1 = 0 := y.2
        show ((p : ℕ) : ℤ) • e.symm y.1 = 0
        rw [← map_zsmul e.symm ((p : ℕ) : ℤ) y.1, hy, map_zero]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  refine ⟨H, i1, i2, i3, i4, i5, f0.trans eT, ?_⟩
  intro σ φ
  show e (f0 (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))).1 =
    WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (e (f0 (Additive.ofMul (WithConv.toConv φ))).1)
  rw [hf0 σ φ]
  exact he σ ((f0 (Additive.ofMul (WithConv.toConv φ))).1)

open TensorProduct ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The quadratic twist of a local Hopf model** (sorry node — the
curve-free core of the unramified quadratic descent, isolated so that
the character bookkeeping against the curve identification is PROVEN
glue): given a finite flat Hopf algebra `H` over the completed
integers `𝒪` with étale generic fibre, and an UNRAMIFIED quadratic
separable extension `L/ℚ_pˆ` (witnessed by a generator `θL` rooting a
monic integral polynomial `Q` with separable residue), there is a
finite flat `𝒪`-Hopf algebra `H'` — the `χ`-twist of `H`, concretely
the invariants of `𝒪_L ⊗ H` under the character-twisted involution
`τ ⊗ S` (`τ` the conjugation of `𝒪_L/𝒪`, `S` the antipode; a direct
summand hence finite flat because the odd residue characteristic
`p ≠ 2` makes `2` invertible) — whose `Ω̂`-point convolution group is
identified with that of `H` by an equivalence `θ` intertwining the
postcomposition Galois actions UP TO the quadratic character `χ` of
`L/ℚ_pˆ`. -/
theorem exists_quadraticTwist_hopfModel
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime] (hp2 : p ≠ 2)
    (L : Type) [Field L]
    [Algebra (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsQuadraticExtension (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsSeparable (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))]
    [IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))]
    (θL : L)
    (Q : Polynomial 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])
    (hQm : Q.Monic)
    (hθtop : Algebra.adjoin (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ({θL} : Set L) = ⊤)
    (hθQ : Polynomial.aeval θL
      (Q.map (algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))) = 0)
    (hQsep : (Q.map (IsLocalRing.residue
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat])).Separable)
    (H : Type) [CommRing H]
    [HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] H)] :
    ∃ (H' : Type) (_ : CommRing H')
      (_ : HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H')
      (_ : Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H')
      (_ : Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] H')
      (_ : Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] H'))
      (θ : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] H') →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
        Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] H) →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))))),
      ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)))
          (φ : ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] H') →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))),
        (quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) L
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)) σ = 1 →
          θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
            Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
              (WithConv.ofConv (Additive.toMul
                (θ (Additive.ofMul (WithConv.toConv φ)))))))) ∧
        (quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) L
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)) σ = -1 →
          θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) +
            Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
              (WithConv.ofConv (Additive.toMul
                (θ (Additive.ofMul (WithConv.toConv φ))))))) = 0) := by
  sorry

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Unramified quadratic descent of the Hopf model** (DECOMPOSED
2026-07-23 — the curve-free twisted-model construction is the sorried
leaf `exists_quadraticTwist_hopfModel` above; the character
bookkeeping against the curve identification is PROVEN glue here):
given a finite flat `𝒪`-Hopf algebra `H` with étale generic fibre
whose `Ω̂`-points are identified with the `p`-torsion of `X`
EQUIVARIANTLY UP TO the quadratic character `χ` of the UNRAMIFIED
quadratic extension `L/ℚ_pˆ` (witnessed by a generator `θL` that is a
root of a monic integral polynomial `Q` with separable residue),
there is an honest `TorsionFlatPackage` for `X`. Proven here: the
twisted model's points identification `θ` (equivariant up to `χ`)
composed with the given `χ`-twisted curve identification `f` is
HONESTLY equivariant, because the two characters multiply to
`χ² = 1`. -/
theorem WeierstrassCurve.torsionFlatPackage_of_quadraticCharacter_twist
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime] (hp2 : p ≠ 2)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic]
    (L : Type) [Field L]
    [Algebra (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsQuadraticExtension (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsSeparable (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))]
    [IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))]
    (θL : L)
    (Q : Polynomial 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])
    (hQm : Q.Monic)
    (hθtop : Algebra.adjoin (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ({θL} : Set L) = ⊤)
    (hθQ : Polynomial.aeval θL
      (Q.map (algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))) = 0)
    (hQsep : (Q.map (IsLocalRing.residue
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat])).Separable)
    (H : Type) [CommRing H]
    [HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] H]
    [Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] H)]
    (f : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] H) →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
      AddSubgroup.torsionBy (X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ))
    (hf : ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
        (φ : ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] H) →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
          (quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) L
              (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)) σ : ℤ) •
            WeierstrassCurve.Affine.Point.map σ.toAlgHom
              (f (Additive.ofMul (WithConv.toConv φ)))) :
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      X p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  -- the twisted Hopf model with its up-to-character points equivalence
  -- (sorried leaf)
  obtain ⟨H', cH', hopfH', finH', flatH', etH', θ, hθ⟩ :=
    exists_quadraticTwist_hopfModel hp' hp2 L θL Q hQm hθtop hθQ hQsep H
  letI := cH'
  letI := hopfH'
  letI := finH'
  letI := flatH'
  refine ⟨H', cH', hopfH', finH', flatH', etH', θ.trans f, ?_⟩
  intro σ φ
  -- the untwisted image point of `φ` under `θ`
  let ψ : ((HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]] H) →ₐ[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) :=
    WithConv.ofConv (Additive.toMul (θ (Additive.ofMul (WithConv.toConv φ))))
  have hψ : Additive.ofMul (WithConv.toConv ψ) =
      θ (Additive.ofMul (WithConv.toConv φ)) := by
    show Additive.ofMul (WithConv.toConv (WithConv.ofConv (Additive.toMul
      (θ (Additive.ofMul (WithConv.toConv φ)))))) =
      θ (Additive.ofMul (WithConv.toConv φ))
    rw [WithConv.toConv_ofConv, ofMul_toMul]
  obtain ⟨hθ1, hθm1⟩ := hθ σ φ
  show ((f (θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))) :
      AddSubgroup.torsionBy (X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) :
      (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
    WeierstrassCurve.Affine.Point.map σ.toAlgHom
      (f (θ (Additive.ofMul (WithConv.toConv φ))))
  rcases Int.units_eq_one_or (quadraticCharacter
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) σ) with hε | hε
  · -- trivial character: the twist relation is honest equivariance
    have h1 : θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp ψ)) := hθ1 hε
    rw [h1, hf σ ψ, hε, Units.val_one, one_smul, hψ]
  · -- character `-1`: the twist relation and the curve identification
    -- each contribute one inversion
    have h2 : θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) +
        Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp ψ)) = 0 := hθm1 hε
    have h3 : f (θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))) =
        -f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp ψ))) := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← map_add, h2, map_zero]
    have h4 : ((-f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp ψ))) :
        AddSubgroup.torsionBy (X⁄(AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) :
        (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
        -((f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp ψ))) :
          AddSubgroup.torsionBy (X⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)) :
          (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) :=
      map_neg ((AddSubgroup.torsionBy
        (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point
        ((p : ℕ) : ℤ)).subtype) _
    rw [h3, h4, hf σ ψ, hε, Units.val_neg, Units.val_one, neg_smul, one_smul,
      neg_neg, hψ]

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Unramified quadratic descent of the torsion package**
(DECOMPOSED 2026-07-23 — the twist point-equivalence transport is
PROVEN glue; the descent core is the sorried leaf
`torsionFlatPackage_of_quadraticCharacter_twist` above): if `L/ℚ_pˆ`
is a quadratic separable extension that is UNRAMIFIED (witnessed by a
generator `θL` that is a root of a monic integral polynomial `Q` with
separable residue), then a `TorsionFlatPackage` for the quadratic
twist `X.quadraticTwist L` yields one for `X` itself. Proven here:
fixing an embedding `L ↪ Ω̂` (`IsAlgClosed.lift`), the twist
isomorphism on points (`quadraticTwistPointEquiv`) restricts to the
`p`-torsion subgroups, and composing the twist package's points
identification with it yields an identification onto the `p`-torsion
of `X` that is equivariant up to the quadratic character
(`quadraticTwistPointEquiv_galois`) — the hypothesis shape of the
descent leaf. -/
theorem WeierstrassCurve.torsionFlatPackage_of_unramified_quadraticTwist
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime] (hp2 : p ≠ 2)
    (X : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) [X.IsElliptic]
    (L : Type) [Field L]
    [Algebra (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsQuadraticExtension (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    [Algebra.IsSeparable (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L]
    (θL : L)
    (Q : Polynomial 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat])
    (hQm : Q.Monic)
    (hθtop : Algebra.adjoin (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ({θL} : Set L) = ⊤)
    (hθQ : Polynomial.aeval θL
      (Q.map (algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))) = 0)
    (hQsep : (Q.map (IsLocalRing.residue
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat])).Separable) :
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (X.quadraticTwist L) p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) →
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      X p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  intro hpkg
  -- fix an embedding of `L` into the local algebraic closure, over
  -- the base field
  letI algLΩ : Algebra L (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)) :=
    (IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
      (R := HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) (S := L)).toAlgebra
  haveI : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) L
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
        (R := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (S := L)).commutes x).symm)
  obtain ⟨H, i1, i2, i3, i4, i5, f0, hf0⟩ := hpkg
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  -- the twist point identification over the algebraic closure
  let qe : ((X.quadraticTwist L)⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ≃+
      (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).Point :=
    X.quadraticTwistPointEquiv L (AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
  -- restricted to the `p`-torsion subgroups
  let qeT : AddSubgroup.torsionBy ((X.quadraticTwist L)⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) ≃+
      AddSubgroup.torsionBy (X⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨qe x.1, by
        have hx : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        show ((p : ℕ) : ℤ) • qe x.1 = 0
        rw [← map_zsmul, hx, map_zero]⟩
      invFun := fun y => ⟨qe.symm y.1, by
        have hy : ((p : ℕ) : ℤ) • y.1 = 0 := y.2
        show ((p : ℕ) : ℤ) • qe.symm y.1 = 0
        rw [← map_zsmul qe.symm ((p : ℕ) : ℤ) y.1, hy, map_zero]⟩
      left_inv := fun x => Subtype.ext (qe.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (qe.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (map_add qe x.1 y.1) }
  -- the composed points identification is equivariant up to the
  -- quadratic character (`quadraticTwistPointEquiv_galois`)
  have hft : ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))
      (φ : ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] H) →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))),
      ((f0.trans qeT) (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
        (X⁄(AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
        (quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) L
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)) σ : ℤ) •
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            ((f0.trans qeT) (Additive.ofMul (WithConv.toConv φ))) := by
    intro σ φ
    show qe (f0 (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))).1 =
      (quadraticCharacter (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) L
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)) σ : ℤ) •
        WeierstrassCurve.Affine.Point.map σ.toAlgHom
          (qe (f0 (Additive.ofMul (WithConv.toConv φ))).1)
    rw [hf0 σ φ]
    exact X.quadraticTwistPointEquiv_galois L (AlgebraicClosure
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) σ
      ((f0 (Additive.ofMul (WithConv.toConv φ))).1)
  -- the descent core (sorried leaf)
  exact WeierstrassCurve.torsionFlatPackage_of_quadraticCharacter_twist
    hp' hp2 X L θL Q hQm hθtop hθQ hQsep H (f0.trans qeT) hft

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The nonsplit twist package** (DECOMPOSED 2026-07-23 — the
NONSPLIT-CASE local content, hoisted out of
`torsion_flat_of_multiplicative_reduction` as a standalone node): the
quadratic unramified twist to split reduction
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`) has the same
`j`-invariant, so its minimal model gets the recentring witness
(`exists_unit_qUnit_mul_inv_pow_isUnit`, via `variableChange_j` and
`j_quadraticTwist`) and the PROVEN local split package
`torsionFlatPackage_of_split_adic'`; the package transports back along
the minimal variable change (sorried leaf
`torsionFlatPackage_of_variableChange`) and descends along the
unramified quadratic extension (sorried leaf
`torsionFlatPackage_of_unramified_quadraticTwist`). -/
theorem WeierstrassCurve.torsionFlatPackage_of_nonsplit_adic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime] (hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat p E.j) :
    ¬(E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] →
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
  classical
  intro hns
  haveI := hasMultiplicativeReduction_adicCompletion hp' E
  -- the unramified quadratic twist with split reduction, with its
  -- unramifiedness witness `(θL, Q)`
  obtain ⟨L, _, _, _, _, hsplit', θL, Q, hQm, hθtop, hθQ, hQsep⟩ :=
    WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction
      (E := E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]) hns
  set Tw : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) :=
    (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))).quadraticTwist L
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) :=
    Tw.minimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
  haveI hMtsplit : Mt.HasSplitMultiplicativeReduction
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat] := hsplit'
  haveI hTwell : Tw.IsElliptic :=
    inferInstanceAs (((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))).quadraticTwist L).IsElliptic)
  haveI hMtell : Mt.IsElliptic :=
    inferInstanceAs (((Tw.exists_isMinimal
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).IsElliptic)
  -- the minimal twist has the SAME rational `j`-image
  have hMtj : Mt.j = algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) E.j := by
    have h1 : Mt.j = ((Tw.exists_isMinimal
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]).choose • Tw).j := rfl
    have h2 : Tw.j = ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))).quadraticTwist L).j := rfl
    rw [h1, WeierstrassCurve.variableChange_j, h2,
      WeierstrassCurve.j_quadraticTwist]
    exact WeierstrassCurve.map_j _ _
  -- the recentring witness for the minimal twist, from `p ∣ v_p(j)`
  obtain ⟨w, hmemw, hunitw⟩ :=
    exists_unit_qUnit_mul_inv_pow_isUnit hp' Mt (p := p) hMtj hj
  -- the PROVEN local split package for the minimal twist
  have hMtpkg : WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      Mt p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) :=
    WeierstrassCurve.torsionFlatPackage_of_split_adic' hp' Mt w hmemw hunitw
  -- transport along the minimal variable change (sorried leaf)
  have hTwpkg : WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      Tw p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) :=
    WeierstrassCurve.torsionFlatPackage_of_variableChange hp' Tw
      (Tw.exists_isMinimal 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]).choose hMtpkg
  -- unramified quadratic descent (sorried leaf)
  exact WeierstrassCurve.torsionFlatPackage_of_unramified_quadraticTwist
    hp' hp2 (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))) L θL Q hQm hθtop hθQ hQsep
    hTwpkg

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Reconstruction of finite étale bialgebras from their Galois
sets** (sorry node — the fully-faithful half of the étale/Galois-sets
correspondence, curve-free and completion-free): two finite étale
bialgebras `A`, `B` over a characteristic-zero field `K` whose
`Ω`-point convolution monoids are identified `Gal(Ω/K)`-equivariantly
are isomorphic as `K`-bialgebras (contravariantly: the points
equivalence `pts A ≃ pts B` yields `B ≃ₐc A`). Content
(Grothendieck's Galois theory, the reconstruction direction dual to
`exists_galoisModulePackage`): evaluation identifies a finite étale
`K`-algebra with the equivariant functions on its finite point set,
compatibly with the convolution structure, and an equivariant
identification of point sets identifies the equivariant function
bialgebras. -/
theorem exists_bialgEquiv_of_equivariant_pointsEquiv
    (K : Type) [Field K] [CharZero K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : Type) [CommRing A] [Bialgebra K A] [Module.Finite K A]
    [Algebra.Etale K A]
    (B : Type) [CommRing B] [Bialgebra K B] [Module.Finite K B]
    [Algebra.Etale K B]
    (θ : Additive (WithConv (A →ₐ[K] Ω)) ≃+ Additive (WithConv (B →ₐ[K] Ω)))
    (hθ : ∀ (σ : Ω ≃ₐ[K] Ω) (φ : A →ₐ[K] Ω),
      θ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
          (WithConv.ofConv (Additive.toMul
            (θ (Additive.ofMul (WithConv.toConv φ)))))))) :
    Nonempty (B ≃ₐc[K] A) := by
  sorry

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The global-to-local points transport** (sorry node — the
embedding half of the adic comparison): a GLOBAL equivariant points
identification for the finite `ℚ`-Hopf algebra `Hg` induces, through
the chosen embedding `ℚ̄ ↪ Ω̂` (`algClosureEmbeddingRat`), a LOCAL
equivariant identification of the `Ω̂`-point convolution group of the
base change `ℚ_pˆ ⊗[ℚ] Hg` with the `p`-torsion of the base-changed
curve. Content: `Ω̂`-points of the base change are `ℚ̄`-points of
`ℚ ⊗ Hg` (`AlgHom.liftEquiv` twice and `algHomEquivOfFinite`, the
`dvrPointsEquiv` pattern of `FlatProlongation`), compatibly with
convolution and with the restriction of local Galois elements to
global ones; and the `p`-torsion of `E(ℚ̄)` maps isomorphically onto
the `p`-torsion of `E(Ω̂)` along `Point.map (algClosureEmbeddingRat)`
(torsion points upstairs are algebraic over `ℚ`, hence land in the
embedded closure by `mem_range_algebraicClosureMap_of_isIntegral`),
equivariantly by `point_map_algClosureEmbeddingRat_comm`. -/
theorem WeierstrassCurve.exists_localPointsEquiv_of_globalPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime]
    (Hg : Type) [CommRing Hg] [HopfAlgebra ℚ Hg] [Module.Finite ℚ Hg]
    (fg : Additive (WithConv ((ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+
      AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ))
    (hfg : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (φ : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ),
        (fg (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          (E⁄(AlgebraicClosure ℚ)).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (fg (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ (fgl : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
        →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
      AddSubgroup.torsionBy ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ)),
      ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))
            ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)))
          (φ : ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
            →ₐ[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))),
        (fgl (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (fgl (Additive.ofMul (WithConv.toConv φ))) := by
  sorry

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The adic étale/Galois-sets comparison** (DECOMPOSED 2026-07-23
into the two sorried leaves above — the GENERIC-FIBRE comparison half
of the lattice gluing): the two étale `ℚ_pˆ`-bialgebras `ℚ_pˆ ⊗_ℚ Hg`
and `ℚ_pˆ ⊗_𝒪 H_loc` are isomorphic as `ℚ_pˆ`-BIALGEBRAS. The two
halves: `exists_localPointsEquiv_of_globalPackage` turns the global
identification `fg`/`hfg` into a local one for `ℚ_pˆ ⊗[ℚ] Hg` through
the chosen embedding `ℚ̄ ↪ Ω̂`, and
`exists_bialgEquiv_of_equivariant_pointsEquiv` (reconstruction)
upgrades the resulting equivariant identification of the two point
convolution groups — PROVEN glue here: composing with `fl.symm` and
transporting equivariance through injectivity — to a `ℚ_pˆ`-bialgebra
isomorphism. -/
theorem WeierstrassCurve.exists_adic_bialgEquiv_of_torsion_packages
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime]
    (Hg : Type) [CommRing Hg] [HopfAlgebra ℚ Hg] [Module.Finite ℚ Hg]
    [Algebra.Etale ℚ (ℚ ⊗[ℚ] Hg)]
    (fg : Additive (WithConv ((ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+
      AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ))
    (hfg : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (φ : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ),
        (fg (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          (E⁄(AlgebraicClosure ℚ)).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (fg (Additive.ofMul (WithConv.toConv φ))))
    (Hl : Type) [CommRing Hl]
    [HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    [Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    [Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    [Algebra.Etale (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)]
    (fl : Additive (WithConv (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))) ≃+
      AddSubgroup.torsionBy ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))).Point ((p : ℕ) : ℤ))
    (hfl : ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
        (φ : ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))),
        (fl (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          ((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))⁄(AlgebraicClosure
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (fl (Additive.ofMul (WithConv.toConv φ)))) :
    Nonempty (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
      ≃ₐc[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)) := by
  classical
  -- the local points identification for the base-changed global
  -- algebra (sorried leaf)
  obtain ⟨fgl, hfgl⟩ :=
    WeierstrassCurve.exists_localPointsEquiv_of_globalPackage E hp' Hg fg hfg
  -- characteristic zero of the completed field, for the reconstruction
  haveI : CharZero (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) :=
    charZero_of_injective_algebraMap
      ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)).injective)
  -- étaleness of `Hg` itself, hence of its completed base change
  haveI hEtHg0 : Algebra.Etale ℚ Hg :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.lid ℚ Hg)
  -- the composed points identification, equivariant on the nose
  have hθeq : ∀ (σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))
        ≃ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)))
      (φ : ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat))),
      (fl.trans fgl.symm) (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
          (WithConv.ofConv (Additive.toMul ((fl.trans fgl.symm)
            (Additive.ofMul (WithConv.toConv φ))))))) := by
    intro σ φ
    have hψ : Additive.ofMul (WithConv.toConv (WithConv.ofConv (Additive.toMul
        ((fl.trans fgl.symm) (Additive.ofMul (WithConv.toConv φ)))))) =
        (fl.trans fgl.symm) (Additive.ofMul (WithConv.toConv φ)) := by
      rw [WithConv.toConv_ofConv, ofMul_toMul]
    show fgl.symm (fl (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ)))) =
      Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
        (WithConv.ofConv (Additive.toMul ((fl.trans fgl.symm)
          (Additive.ofMul (WithConv.toConv φ)))))))
    apply fgl.injective
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [hfl σ φ, hfgl σ (WithConv.ofConv (Additive.toMul ((fl.trans fgl.symm)
      (Additive.ofMul (WithConv.toConv φ))))), hψ]
    have h3 : fgl ((fl.trans fgl.symm) (Additive.ofMul (WithConv.toConv φ))) =
        fl (Additive.ofMul (WithConv.toConv φ)) := by
      show fgl (fgl.symm (fl (Additive.ofMul (WithConv.toConv φ)))) =
        fl (Additive.ofMul (WithConv.toConv φ))
      rw [AddEquiv.apply_symm_apply]
    rw [h3]
  -- reconstruction (sorried leaf) upgrades the points identification
  -- to a bialgebra isomorphism
  exact exists_bialgEquiv_of_equivariant_pointsEquiv
    (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat)
    (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat))
    ((HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
    ((HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
    (fl.trans fgl.symm) hθeq

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Hopf order from a closed full lattice** (sorry node — the
abstract half of the lattice intersection, free of the comparison
isomorphism and of the completion): an `ℤ_(p)`-subalgebra `H₀ ⊆ Hg` of
a finite-dimensional étale `ℚ`-Hopf algebra that is finite over
`ℤ_(p)`, FULL (every element of `Hg` has a nonzero `ℤ_(p)`-multiple
in `H₀`), and closed under the costructure maps (comultiplication
lands in the additive span of split tensors of `H₀`-elements, counit
values are integral, the antipode preserves `H₀`) is a finite flat
`ℤ_(p)`-Hopf algebra whose generic fibre is `Hg` as a `ℚ`-bialgebra.
Content: finite plus torsion-free over the DVR gives free, hence
flat; freeness makes `H₀ ⊗[ℤ_(p)] H₀ → Hg ⊗[ℚ] Hg` injective, so the
comultiplication corestricts to `H₀` and the Hopf axioms restrict
from `Hg`; fullness makes `ℚ ⊗[ℤ_(p)] H₀ → Hg` bijective,
transporting étaleness and giving the generic-fibre bialgebra
identification. -/
theorem exists_hopfOrder_of_latticeClosure
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (Hg : Type) [CommRing Hg] [HopfAlgebra ℚ Hg] [Module.Finite ℚ Hg]
    [Algebra.Etale ℚ (ℚ ⊗[ℚ] Hg)]
    [Algebra (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg]
    [IsScalarTower (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ Hg]
    (H₀ : Subalgebra (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg)
    (hfin : Module.Finite (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H₀)
    (hfull : ∀ x : Hg, ∃ r : Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal, r ≠ 0 ∧ r • x ∈ H₀)
    (hcomul : ∀ x ∈ H₀, Coalgebra.comul (R := ℚ) x ∈
      AddSubmonoid.closure (Set.image2 (fun a b : Hg => a ⊗ₜ[ℚ] b)
        (H₀ : Set Hg) (H₀ : Set Hg)))
    (hcounit : ∀ x ∈ H₀, Coalgebra.counit (R := ℚ) x ∈
      Set.range (algebraMap (Localization.AtPrime
        hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ))
    (hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode ℚ x ∈ H₀) :
    ∃ (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Finite
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Flat
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Algebra.Etale ℚ
        (ℚ ⊗[Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)),
      Nonempty
        ((ℚ ⊗[Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
          ≃ₐc[ℚ] (ℚ ⊗[ℚ] Hg)) := by
  sorry

open TensorProduct ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The lattice intersection** (DECOMPOSED 2026-07-23 — the abstract
Hopf-order construction is the sorried leaf
`exists_hopfOrder_of_latticeClosure` above; the lattice itself is REAL
CODE here): given a finite-dimensional `ℚ`-Hopf algebra `Hg` with
étale generic fibre, a finite flat Hopf algebra `H_loc` over the
completed integers `𝒪 = ℤ_pˆ`, and a `ℚ_pˆ`-BIALGEBRA isomorphism `ψ`
of their base changes, the lattice `H := {x ∈ Hg : ψ(1 ⊗ x) ∈ H_loc}`
is a finite flat Hopf algebra over the DVR `ℤ_(p) = ℚ ∩ ℤ_p` with
generic fibre `Hg`. Proven here: `H` is an `ℤ_(p)`-subalgebra (the
lattice `𝒪_L`-image of `H_loc` is a subring, and `ℤ_(p)`-scalars land
in it by `algebraMap_localization_mem_adicCompletionIntegers`); its
finiteness, fullness, and costructure closure remain as sorried
leaves feeding the abstract construction. -/
theorem exists_hopfOrder_of_adic_bialgEquiv
    {p : ℕ} (hp' : p.Prime) [Fact p.Prime]
    (Hg : Type) [CommRing Hg] [HopfAlgebra ℚ Hg] [Module.Finite ℚ Hg]
    [Algebra.Etale ℚ (ℚ ⊗[ℚ] Hg)]
    (Hl : Type) [CommRing Hl]
    [HopfAlgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    [Module.Finite 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    [Module.Flat 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat] Hl]
    (ψ : ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
      ≃ₐc[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)) :
    ∃ (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Finite
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Flat
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Algebra.Etale ℚ
        (ℚ ⊗[Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)),
      Nonempty
        ((ℚ ⊗[Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
          ≃ₐc[ℚ] (ℚ ⊗[ℚ] Hg)) := by
  classical
  -- the `ℤ_(p)`-algebra structure on `Hg`, through `ℚ`
  letI algRHg : Algebra (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg :=
    ((algebraMap ℚ Hg).comp (algebraMap (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ)).toAlgebra
  haveI towRHg : IsScalarTower (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ Hg :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the comparison map, as a `ℚ_pˆ`-algebra homomorphism
  let Ψ : ((HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
      →ₐ[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) := ψ.toBialgHom
  -- the `𝒪`-lattice: the image of `Hl` in its own base change
  let Λ : Subalgebra 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]
      ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) :=
    (Algebra.TensorProduct.includeRight
      (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat])
      (A := HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hl)).range
  -- the `ℤ_(p)`-scalars of `Hg` land in the lattice
  have halg : ∀ r : Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal,
      Ψ (Algebra.TensorProduct.includeRight
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg r)) ∈ Λ := by
    intro r
    -- the scalar is integral in the completion
    have hint : algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r) ∈
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat] := by
      have h0 := algebraMap_localization_mem_adicCompletionIntegers
        hp'.toHeightOneSpectrumRingOfIntegersRat r
      -- bridge the two (equal) `ℚ`-algebra structures on the completion
      have hpt : algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          (algebraMap (Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r) =
          @algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) _ _
            (HeightOneSpectrum.instAlgebraAdicCompletion
              (NumberField.RingOfIntegers ℚ) ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r) :=
        RingHom.congr_fun (Subsingleton.elim _ _) _
      rw [hpt]
      exact mem_integer_of_mem_adicCompletionIntegers hp' h0
    -- the image of the scalar under `Ψ ∘ includeRight`
    have h1 : Algebra.TensorProduct.includeRight (R := ℚ)
        (A := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg)
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg r) =
        algebraMap ℚ ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r) :=
      (Algebra.TensorProduct.includeRight (R := ℚ)
        (A := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg)).commutes
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r)
    have h2 : Ψ (algebraMap ℚ ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r)) =
        algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
          (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r)) :=
      Ψ.commutes (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r))
    rw [h1, h2]
    -- the integral scalar times `1` is an `includeRight`-image
    refine ⟨(⟨_, hint⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
      hp'.toHeightOneSpectrumRingOfIntegersRat]) • (1 : Hl), ?_⟩
    show (1 : HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]]
        ((⟨_, hint⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]) • (1 : Hl)) =
      algebraMap (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          (algebraMap (Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ r))
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      mul_one]
    rfl
  -- the lattice-intersection subalgebra `H₀ = Hg ∩ ψ⁻¹(Hl)`
  let H₀ : Subalgebra (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg :=
    { carrier := {x : Hg |
        Ψ (Algebra.TensorProduct.includeRight x) ∈ Λ}
      mul_mem' := fun {a b} ha hb => by
        show Ψ (Algebra.TensorProduct.includeRight (a * b)) ∈ Λ
        rw [map_mul, map_mul]
        exact Λ.mul_mem ha hb
      one_mem' := by
        show Ψ (Algebra.TensorProduct.includeRight (1 : Hg)) ∈ Λ
        rw [map_one, map_one]
        exact Λ.one_mem
      add_mem' := fun {a b} ha hb => by
        show Ψ (Algebra.TensorProduct.includeRight (a + b)) ∈ Λ
        rw [map_add, map_add]
        exact Λ.add_mem ha hb
      zero_mem' := by
        show Ψ (Algebra.TensorProduct.includeRight (0 : Hg)) ∈ Λ
        rw [map_zero, map_zero]
        exact Λ.zero_mem
      algebraMap_mem' := halg }
  -- FINITENESS leaf (sorry node): `H₀` is finite over the DVR `ℤ_(p)`
  -- (a torsion-free `ℤ_(p)`-submodule of `Hg` commensurable with a
  -- lattice: it embeds into the finite `𝒪`-module `Hl` after clearing
  -- denominators)
  have hfin : Module.Finite (Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H₀ := by
    sorry
  -- FULLNESS (PROVEN): every element of `Hg` has a nonzero
  -- `ℤ_(p)`-multiple in `H₀` — clear denominators by a `p`-power,
  -- since `p` is strictly inside the unit disc of the completion and
  -- its powers shrink any completion element into the integers
  -- (`exists_pow_valuation_lt`, rank one)
  have hfull : ∀ x : Hg, ∃ r : Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal, r ≠ 0 ∧ r • x ∈ H₀ := by
    -- the adic valuation of `p` at its own place is `< 1`
    have hadic : hp'.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ
        ((p : ℕ) : ℚ) < 1 := by
      rw [show (((p : ℕ) : ℚ)) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
          (((p : ℕ) : NumberField.RingOfIntegers ℚ)) from (map_natCast _ _).symm,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
        Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal hp',
        map_natCast]
    -- transferred to the canonical valuation of the completion
    have hKeq : (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)).IsEquiv
        (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          (WithZero (Multiplicative ℤ))) :=
      ValuativeRel.isEquiv _ _
    have hplt : ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) < 1 := by
      refine (Valuation.isEquiv_iff_val_lt_one.mp hKeq).mpr ?_
      rw [valued_algebraMap_adicCompletion_eq hp']
      exact hadic
    -- powers of `p` clear the denominator of any completion element
    have hclear : ∀ k : HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat,
        ∃ n : ℕ, (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n * k ∈
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat] := by
      intro k
      rcases eq_or_ne (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) k) 0 with hk0 | hk0
      · refine ⟨0, ?_⟩
        rw [pow_zero, one_mul, Valuation.mem_integer_iff]
        exact le_of_eq_of_le hk0 zero_le_one
      · obtain ⟨N, hN⟩ := ValuativeRel.exists_pow_valuation_lt
          (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) hplt
          (Units.mk0 (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) k)⁻¹ (inv_ne_zero hk0))
        refine ⟨N, ?_⟩
        rw [Valuation.mem_integer_iff, map_mul, map_pow]
        calc ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ N *
            ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) k
            ≤ (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) k)⁻¹ *
              ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) k :=
            mul_le_mul_left (le_of_lt hN) _
          _ = 1 := inv_mul_cancel₀ hk0
    -- powers of `p` lie in the lattice
    have hpowΛ : ∀ n : ℕ,
        algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
          ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) ∈
          Λ := by
      intro n
      have hmemn : (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n ∈
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat] := by
        rw [Valuation.mem_integer_iff, map_pow]
        exact pow_le_one' (le_of_lt hplt) n
      refine ⟨(⟨_, hmemn⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]) • (1 : Hl), ?_⟩
      show (1 : HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]]
          ((⟨_, hmemn⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]) • (1 : Hl)) =
        algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
          ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n)
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        mul_one]
      rfl
    -- denominator clearing inside the base-changed lattice
    have hclearT : ∀ z : (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl,
        ∃ n : ℕ, algebraMap (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
          ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) * z ∈
          Λ := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
        refine ⟨0, ?_⟩
        rw [mul_zero]
        exact Λ.zero_mem
      | tmul k h =>
        obtain ⟨n, hn⟩ := hclear k
        refine ⟨n, ⟨(⟨_, hn⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]) • h, ?_⟩⟩
        show (1 : HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]]
            ((⟨_, hn⟩ : 𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]) • h) =
          algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ((HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
            ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) *
            (k ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] h)
        rw [show algebraMap (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ((HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
              ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) *
              (k ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat]] h) =
            ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n * k)
              ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat]] h from by
          rw [show algebraMap (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ((HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat)
                  ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                    hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
                ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) =
              ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n)
                ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat]] (1 : Hl) from rfl,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul],
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
          mul_one]
        rfl
      | add y z hy hz =>
        obtain ⟨n₁, h₁⟩ := hy
        obtain ⟨n₂, h₂⟩ := hz
        refine ⟨n₁ + n₂, ?_⟩
        have hsplit : algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ((HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
            ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^
              (n₁ + n₂)) * (y + z) =
            algebraMap (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ((HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
              ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n₂) *
              (algebraMap (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ((HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat)
                  ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                    hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
                ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat)
                  ((p : ℕ) : ℚ)) ^ n₁) * y) +
            algebraMap (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ((HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
              ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n₁) *
              (algebraMap (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ((HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat)
                  ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                    hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
                ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat)
                  ((p : ℕ) : ℚ)) ^ n₂) * z) := by
          rw [pow_add, map_mul, mul_add]
          ring
        rw [hsplit]
        exact Λ.add_mem (Λ.mul_mem (hpowΛ n₂) h₁) (Λ.mul_mem (hpowΛ n₁) h₂)
    -- assemble: `r = p^n` for the clearing exponent of `ψ(1 ⊗ x)`
    intro x
    obtain ⟨n, hn⟩ := hclearT (Ψ (Algebra.TensorProduct.includeRight x))
    refine ⟨((p : ℕ) : Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n, ?_, ?_⟩
    · -- nonzero: its image in `ℚ` is `p ^ n ≠ 0`
      intro h0
      have h1 : algebraMap (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
          (((p : ℕ) : Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n) = 0 := by
        rw [h0, map_zero]
      rw [map_pow, map_natCast] at h1
      exact pow_ne_zero n (Nat.cast_ne_zero.mpr hp'.ne_zero) h1
    · -- membership: the scalar factors out through `Ψ ∘ includeRight`
      show Ψ (Algebra.TensorProduct.includeRight
        ((((p : ℕ) : Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n) • x)) ∈ Λ
      rw [Algebra.smul_def, map_mul, map_mul]
      have hscal : Ψ (Algebra.TensorProduct.includeRight
          (algebraMap (Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg
            (((p : ℕ) : Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n))) =
          algebraMap (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ((HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
            ((algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ((p : ℕ) : ℚ)) ^ n) := by
        have hstep1 : Algebra.TensorProduct.includeRight (R := ℚ)
            (A := HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) Hg
              (((p : ℕ) : Localization.AtPrime
                hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n)) =
            algebraMap ℚ ((HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
              (((p : ℕ) : Localization.AtPrime
                hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n)) :=
          (Algebra.TensorProduct.includeRight (R := ℚ)
            (A := HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg)).commutes
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
              (((p : ℕ) : Localization.AtPrime
                hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n))
        have hstep2 : Ψ (algebraMap ℚ ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
              (((p : ℕ) : Localization.AtPrime
                hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n))) =
            algebraMap (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
              ((HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
                  hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
              (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)
                (algebraMap (Localization.AtPrime
                  hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
                  (((p : ℕ) : Localization.AtPrime
                    hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n))) :=
          Ψ.commutes (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            (algebraMap (Localization.AtPrime
              hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ
              (((p : ℕ) : Localization.AtPrime
                hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ^ n)))
        rw [hstep1, hstep2, map_pow, map_natCast, map_pow]
      rw [hscal]
      exact hn
  -- COMULTIPLICATION leaf (sorry node): `Δ(H₀)` lies in the additive
  -- span of split tensors of `H₀`-elements (`ψ` matches the two
  -- comultiplications and `Hl` is a Hopf `𝒪`-algebra)
  have hcomul : ∀ x ∈ H₀, Coalgebra.comul (R := ℚ) x ∈
      AddSubmonoid.closure (Set.image2 (fun a b : Hg => a ⊗ₜ[ℚ] b)
        (H₀ : Set Hg) (H₀ : Set Hg)) := by
    sorry
  -- COUNIT (PROVEN): counit values on `H₀` are integral — the
  -- comparison map preserves counits, the lattice's counit values are
  -- `𝒪`-integral, and a rational that is integral in the completion
  -- lies in `ℤ_(p)` (`mem_integers_of_valuation_le_one` at the DVR,
  -- whose unique height-one prime is its maximal ideal)
  have hcounit : ∀ x ∈ H₀, Coalgebra.counit (R := ℚ) x ∈
      Set.range (algebraMap (Localization.AtPrime
        hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ) := by
    intro x hx
    obtain ⟨h, hh⟩ := hx
    -- the comparison map preserves the `ℚ_pˆ`-linear counits
    have h1 : Coalgebra.counit (R := HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Ψ (Algebra.TensorProduct.includeRight x)) =
        Coalgebra.counit (R := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg) x) :=
      CoalgHomClass.counit_comp_apply ψ.toBialgHom
        (Algebra.TensorProduct.includeRight x)
    -- the counit of the base change on `1 ⊗ x` is the scalar `ε(x)`
    have h2 : Coalgebra.counit (R := HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg) x) =
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Coalgebra.counit (R := ℚ) x) := by
      rw [Algebra.TensorProduct.includeRight_apply,
        congr($(Bialgebra.TensorProduct.counit_eq_algHom_toLinearMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) Hg)
        ((1 : HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗ₜ[ℚ] x))]
      simp
    -- the counit of the lattice element is `𝒪`-integral
    have h3 : Coalgebra.counit (R := HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Algebra.TensorProduct.includeRight
          (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat])
          (A := HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hl) h) =
        algebraMap 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Coalgebra.counit (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]) h) := by
      rw [Algebra.TensorProduct.includeRight_apply,
        congr($(Bialgebra.TensorProduct.counit_eq_algHom_toLinearMap
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) Hl)
        ((1 : HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗ₜ[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] h))]
      simp [Algebra.algebraMap_eq_smul_one]
    -- hence the rational `ε(x)` is integral in the completion
    have hh' : Algebra.TensorProduct.includeRight
        (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat])
        (A := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hl) h =
        Ψ (Algebra.TensorProduct.includeRight x) := hh
    have h4 : algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Coalgebra.counit (R := ℚ) x) ∈
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat] := by
      rw [← h2, ← h1, ← hh', h3]
      exact SetLike.coe_mem _
    -- transfer to the `v_p`-adic valuation of `ℚ`
    have h5 : hp'.toHeightOneSpectrumRingOfIntegersRat.valuation ℚ
        (Coalgebra.counit (R := ℚ) x) ≤ 1 := by
      have h6 := mem_adicCompletionIntegers_of_mem_integer hp' h4
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        valued_algebraMap_adicCompletion_eq hp'] at h6
      exact h6
    -- transfer to the maximal-ideal valuation of the DVR `ℤ_(p)`
    have h7 : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
        hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)).valuation ℚ
        (Coalgebra.counit (R := ℚ) x) ≤ 1 :=
      (Valuation.isEquiv_iff_val_le_one.mp
        (isEquiv_valuation_maximalIdeal_localization hp')).mp h5
    -- the DVR has a unique height-one prime
    have huniq : ∀ w : HeightOneSpectrum (Localization.AtPrime
        hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal),
        w = IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) := by
      intro w
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal w.ne_bot)
    -- conclude by the fraction-field integrality criterion
    obtain ⟨r, hr⟩ :=
      IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        (R := Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) (K := ℚ)
        (Coalgebra.counit (R := ℚ) x) (fun w => by rw [huniq w]; exact h7)
    exact ⟨r, hr⟩
  -- ANTIPODE (PROVEN): the antipode preserves `H₀` — the comparison
  -- map intertwines the antipodes (both composites are convolution
  -- inverses of `Ψ`, and inverses in the convolution monoid are
  -- unique), and the base-change antipodes preserve
  -- `includeRight`-images
  have hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode ℚ x ∈ H₀ := by
    -- the flipped antipode cancel law on the target
    have hidS : WithConv.toConv (AlgHom.id (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)) *
        WithConv.toConv (HopfAlgebra.antipodeAlgHom
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)) = 1 := by
      apply WithConv.ofConv_injective
      apply AlgHom.toLinearMap_injective
      apply WithConv.toConv_injective
      rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne,
        HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_id]
      exact LinearMap.id_mul_antipode
    -- postcomposing the convolution unit with the comparison map
    have hpost1 : Ψ.comp ((1 : WithConv (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
        →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg))).ofConv) =
        (1 : WithConv (((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl))).ofConv := by
      refine AlgHom.ext fun z => ?_
      rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
      exact Ψ.commutes _
    -- precomposing the convolution unit with the comparison map
    have hpre1 : ((1 : WithConv (((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)
        →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl))).ofConv).comp
        (ψ.toBialgHom : ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)) =
        (1 : WithConv (((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
          →ₐ[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl))).ofConv := by
      refine AlgHom.ext fun z => ?_
      rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
      exact congrArg _ (CoalgHomClass.counit_comp_apply ψ.toBialgHom z)
    -- `Ψ ∘ S` is a left convolution inverse of `Ψ`
    have hab : WithConv.toConv (Ψ.comp (HopfAlgebra.antipodeAlgHom
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg))) *
        WithConv.toConv Ψ = 1 := by
      have h1 := AlgHom.comp_convMul_distrib Ψ
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)))
        (WithConv.toConv (AlgHom.id (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)))
      rw [AlgHom.antipode_id_cancel, hpost1] at h1
      have h2 := congrArg WithConv.toConv h1
      rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv,
        WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.comp_id] at h2
      exact h2.symm
    -- `S ∘ Ψ` is a right convolution inverse of `Ψ`
    have hbc : WithConv.toConv Ψ *
        WithConv.toConv ((HopfAlgebra.antipodeAlgHom
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)).comp Ψ) = 1 := by
      have h1 := AlgHom.convMul_comp_bialgHom_distrib
        (WithConv.toConv (AlgHom.id (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)))
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          ((HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
            ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)))
        ψ.toBialgHom
      rw [hidS, hpre1] at h1
      have h2 := congrArg WithConv.toConv h1
      rw [WithConv.toConv_ofConv, WithConv.toConv_ofConv,
        WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.id_comp] at h2
      exact h2.symm
    -- uniqueness of convolution inverses: `Ψ` intertwines the antipodes
    have key : Ψ.comp (HopfAlgebra.antipodeAlgHom
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)) =
        (HopfAlgebra.antipodeAlgHom (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl)).comp Ψ :=
      WithConv.toConv_injective (left_inv_eq_right_inv hab hbc)
    have hnat : ∀ y : ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg),
        Ψ (HopfAlgebra.antipode (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) y) =
        HopfAlgebra.antipode (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (Ψ y) := fun y =>
      congrArg (fun F : ((HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat) ⊗[ℚ] Hg)
        →ₐ[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
        ((HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
          ⊗[𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]] Hl) => F y) key
    intro x hx
    obtain ⟨h, hh⟩ := hx
    have hh' : Algebra.TensorProduct.includeRight
        (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat])
        (A := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hl) h =
        Ψ (Algebra.TensorProduct.includeRight x) := hh
    -- the base-change antipodes act through the right tensor factor
    have hincS : Algebra.TensorProduct.includeRight (R := ℚ)
        (A := HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg)
        (HopfAlgebra.antipode ℚ x) = HopfAlgebra.antipode
        (HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Algebra.TensorProduct.includeRight (R := ℚ)
          (A := HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hg) x) := by
      rw [Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeRight_apply,
        TensorProduct.antipode_def,
        TensorProduct.AlgebraTensorModule.map_tmul, HopfAlgebra.antipode_one]
    have hTincS : HopfAlgebra.antipode (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
        (Algebra.TensorProduct.includeRight
          (R := 𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat])
          (A := HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) (B := Hl) h) =
        Algebra.TensorProduct.includeRight
        (HopfAlgebra.antipode 𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat] h) := by
      rw [Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeRight_apply,
        TensorProduct.antipode_def,
        TensorProduct.AlgebraTensorModule.map_tmul, HopfAlgebra.antipode_one]
    show Ψ (Algebra.TensorProduct.includeRight
      (HopfAlgebra.antipode ℚ x)) ∈ Λ
    rw [hincS, hnat (Algebra.TensorProduct.includeRight x), ← hh', hTincS]
    exact ⟨_, rfl⟩
  -- the abstract Hopf-order construction (sorried leaf)
  exact exists_hopfOrder_of_latticeClosure hp' Hg H₀ hfin hfull hcomul
    hcounit hantipode

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The lattice-intersection Hopf order** (DECOMPOSED 2026-07-23 —
the core of the localization gluing, split into its two halves with
the destructuring glue PROVEN here): given the COMPONENTS of a global
generic-fibre package (an étale `ℚ`-Hopf algebra `Hg` whose `ℚ̄`-points
are equivariantly the `p`-torsion) and a local completed-integers
package, there is a finite flat `ℤ_(p)`-Hopf algebra whose generic
fibre is `Hg` as a `ℚ`-BIALGEBRA. The two sorried halves above:
`exists_adic_bialgEquiv_of_torsion_packages` (the étale/Galois-sets
comparison of the two `ℚ_pˆ`-bialgebras through their equivariantly
identified `Ω̂`-points, riding `algClosureEmbeddingRat`) and
`exists_hopfOrder_of_adic_bialgEquiv` (the curve-free lattice
intersection `H := Hg ∩ H_loc` over `ℤ_(p) = ℚ ∩ ℤ_p`). -/
theorem WeierstrassCurve.exists_hopfOrder_of_adicPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime]
    (Hg : Type) [CommRing Hg] [HopfAlgebra ℚ Hg] [Module.Finite ℚ Hg]
    [Algebra.Etale ℚ (ℚ ⊗[ℚ] Hg)]
    (fg : Additive (WithConv ((ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+
      AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ))
    (hfg : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (φ : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ),
        (fg (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          (E⁄(AlgebraicClosure ℚ)).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (fg (Additive.ofMul (WithConv.toConv φ))))
    (hl : WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))) :
    ∃ (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Finite
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Flat
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Algebra.Etale ℚ
        (ℚ ⊗[Localization.AtPrime
          hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)),
      Nonempty
        ((ℚ ⊗[Localization.AtPrime
            hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
          ≃ₐc[ℚ] (ℚ ⊗[ℚ] Hg)) := by
  classical
  obtain ⟨Hl, cl, hopfl, finl, flatl, etl, fl, hfl⟩ := hl
  letI := cl
  letI := hopfl
  letI := finl
  letI := flatl
  letI := etl
  -- the generic-fibre comparison (sorried leaf)
  obtain ⟨ψ⟩ := WeierstrassCurve.exists_adic_bialgEquiv_of_torsion_packages
    E hp' Hg fg hfg Hl fl hfl
  -- the lattice intersection (sorried leaf)
  exact exists_hopfOrder_of_adic_bialgEquiv hp' Hg Hl ψ

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The lattice-intersection descent** (DECOMPOSED 2026-07-23 — the
gluing leaf, hoisted out of `torsion_flat_of_multiplicative_reduction`
as a standalone implication): a global generic-fibre package and a
local completed-integers package glue to a package over
`ℤ_(p) = ℚ ∩ ℤ_p`. The Hopf-order core is the single sorried leaf
`exists_hopfOrder_of_adicPackage` above; PROVEN here is the transport
of the whole package structure along the generic-fibre bialgebra
isomorphism it provides: étaleness is carried by the iso, the
`ℚ̄`-points equivalence composes with precomposition by the iso — a
morphism of the convolution monoids by
`AlgHom.convMul_comp_bialgHom_distrib` — and Galois equivariance is
associativity of composition. -/
theorem WeierstrassCurve.torsionFlatPackage_localization_of_packages
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime] :
    WeierstrassCurve.TorsionFlatPackage ℚ ℚ E p (AlgebraicClosure ℚ) →
    WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) →
    WeierstrassCurve.TorsionFlatPackage
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
      ℚ E p (AlgebraicClosure ℚ) := by
  classical
  intro hg hl
  obtain ⟨Hg, cg, hopfg, fing, _flatg, etg, fg, hfg⟩ := hg
  letI := cg
  letI := hopfg
  letI := fing
  letI := etg
  -- the Hopf-order core (sorried leaf)
  obtain ⟨H, cH, hopfH, finH, flatH, etH, ⟨e⟩⟩ :=
    WeierstrassCurve.exists_hopfOrder_of_adicPackage E hp' Hg fg hfg hl
  letI := cH
  letI := hopfH
  -- the coerced generic-fibre comparison maps
  let c : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ] (ℚ ⊗[Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) := e.symm.toBialgHom
  let c' : (ℚ ⊗[Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ]
      (ℚ ⊗[ℚ] Hg) := e.toBialgHom
  have hcc' : ∀ φ : (ℚ ⊗[Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ]
      AlgebraicClosure ℚ, (φ.comp c).comp c' = φ := by
    intro φ
    apply AlgHom.ext
    intro z
    show φ (e.symm (e z)) = φ z
    rw [BialgEquiv.symm_apply_apply]
  have hc'c : ∀ ψ : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ,
      (ψ.comp c').comp c = ψ := by
    intro ψ
    apply AlgHom.ext
    intro z
    show ψ (e (e.symm z)) = ψ z
    rw [BialgEquiv.apply_symm_apply]
  -- precomposition with the comparison map, as an isomorphism of the
  -- convolution monoids (`convMul_comp_bialgHom_distrib`)
  let mulE : WithConv ((ℚ ⊗[Localization.AtPrime
        hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ]
        AlgebraicClosure ℚ) ≃*
      WithConv ((ℚ ⊗[ℚ] Hg) →ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toFun := fun u => WithConv.toConv ((WithConv.ofConv u).comp c)
      invFun := fun v => WithConv.toConv ((WithConv.ofConv v).comp c')
      left_inv := fun u => by
        dsimp only
        rw [WithConv.ofConv_toConv, hcc', WithConv.toConv_ofConv]
      right_inv := fun v => by
        dsimp only
        rw [WithConv.ofConv_toConv, hc'c, WithConv.toConv_ofConv]
      map_mul' := fun u v => by
        rw [show (WithConv.ofConv (u * v)).comp c =
            AlgHom.comp (u * v).ofConv
              (e.symm.toBialgHom : (ℚ ⊗[ℚ] Hg) →ₐ[ℚ]
                (ℚ ⊗[Localization.AtPrime
                  hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H))
            from rfl,
          AlgHom.convMul_comp_bialgHom_distrib u v e.symm.toBialgHom,
          WithConv.toConv_ofConv] }
  refine ⟨H, cH, hopfH, finH, flatH, etH,
    (MulEquiv.toAdditive mulE).trans fg, ?_⟩
  intro σ φ
  have happ : ∀ ψ : (ℚ ⊗[Localization.AtPrime
      hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H) →ₐ[ℚ]
      AlgebraicClosure ℚ,
      (MulEquiv.toAdditive mulE) (Additive.ofMul (WithConv.toConv ψ)) =
        Additive.ofMul (WithConv.toConv (ψ.comp c)) := fun ψ => rfl
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, happ, happ,
    show (σ.toAlgHom.comp φ).comp c = σ.toAlgHom.comp (φ.comp c) from
      AlgHom.comp_assoc σ.toAlgHom φ c]
  exact hfg σ (φ.comp c)

open TensorProduct ValuativeRel IsDedekindDomain in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The peu-ramifiée finite-flat package at multiplicative primes**
(sorry node — the TATE-THEORETIC content, stated in the SAME
DVR-package shape as the vendored good-reduction leaf so that the
shared transport `GaloisRep.isFlatAt_of_dvr_package` applies
verbatim): for an elliptic curve over `ℚ` with multiplicative
reduction at the odd place `p` whose `j`-invariant has `p`-adic
valuation divisible by `p`, the `p`-torsion prolongs to a finite flat
group scheme over `ℤ_(p)`. Content: the Tate parameter is a `p`-th
power times a unit (`p ∣ v_p(j) = -v_p(q_E)`), so the Tate-curve
extension `0 → μ_p → E[p] → ℤ/p → 0` over `ℚ_p` is *peu ramifiée* in
the sense of Serre, and such extensions prolong to finite flat group
schemes over `ℤ_p`.

DECOMPOSED (2026-07-22) into two sorried leaves with the assembly
written and compiling:

* `hloc` — the LOCAL leaf: the same `TorsionFlatPackage` over the
  COMPLETED integers `𝒪[adicCompletion ℚ v_p]` for the base-changed
  curve, with local (`Gal(ℚ̄_pˆ/ℚ_pˆ)`) equivariance. This is the pure
  Tate/Kummer content, to be proven with the `TateSepClosure`
  uniformization machinery (`exists_tateEquivSepClosure`; the
  reduction instance transfers by
  `hasMultiplicativeReduction_adicCompletion`). Split case: `p ∣
  v_p(q_E) = -v_p(j)` writes the Tate parameter as `u·π^{pm}` with `u`
  a unit, so `E[p] = ⟨ζ_p, q^{1/p}⟩` is a *peu-ramifiée* extension of
  `ℤ/p` by `μ_p`, and the finite flat model is the explicit Kummer
  group scheme `∐_{i<p} Spec 𝒪[x]/(x^p − uⁱ)` (Hopf algebra
  `∏_{i<p} 𝒪[x]/(x^p − uⁱ)`, finite free of rank `p²`, étale generic
  fibre in characteristic zero). Nonsplit case: the quadratic
  unramified twist of the split model (unramified descent preserves
  finite flatness).

* `hdesc` — the DESCENT leaf: a package over the completed integers
  descends to `ℤ_(p) = ℚ ∩ ℤ_p` with GLOBALLY equivariant points. The
  generic fibre is the global torsion algebra (the étale `ℚ`-algebra
  of functions on the finite Galois set `E[p](ℚ̄)`, whose `ℚ̄`-points
  are globally equivariantly `E[p]` — no local input needed there);
  the model is the lattice intersection of this algebra with the local
  Hopf model inside its completed base change (finite flat because
  finitely generated torsion-free over the DVR `ℤ_(p)`, a Hopf order
  because both intersectands are); the local-vs-global points
  comparison rides the chosen embedding `ℚ̄ ↪ ℚ̄_p` exactly as in
  layer C of `FlatProlongation`
  (`algHomEquivOfFinite`/`mem_range_algebraicClosureMap_of_isIntegral`)
  together with the torsion-point transport `algClosureEmbeddingRat`
  already used by the unramifiedness glue in this file.

FURTHER DECOMPOSED (2026-07-22), assemblies written and compiling;
four sorried sub-leaves remain:

* `hloc` is split by `by_cases` on split multiplicative reduction of
  the completed base change, consuming the PROVEN recentring witness
  `exists_unit_qUnit_mul_inv_pow_isUnit` (`q_E·w⁻ᵖ ∈ 𝒪ˣ` from
  `p ∣ v_p(j)`): `hsplitpkg` (the explicit Kummer Hopf model
  `∏_{i<p} 𝒪[x]/(xᵖ − uⁱ)` with equivariant points via
  `exists_tateEquivSepClosure`) and `hnonsplitpkg` (unramified
  quadratic-twist descent of the split model).

* `hdesc` factors through `hglobal` (the generic-fibre package
  `TorsionFlatPackage ℚ ℚ E p ℚ̄` — Galois descent of the split
  torsion algebra, no local input) and `hlattice` (the
  lattice-intersection gluing
  `TorsionFlatPackage ℚ ℚ → TorsionFlatPackage 𝒪[ℚ_pˆ] ℚ_pˆ →
  TorsionFlatPackage ℤ_(p) ℚ`). -/
theorem WeierstrassCurve.torsion_flat_of_multiplicative_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime)
    [Fact p.Prime] (hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat p E.j) :
    ∃ (H : Type) (_ : CommRing H)
      (_ : HopfAlgebra
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Finite
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Module.Flat
        (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
      (_ : Algebra.Etale ℚ
        (ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H))
      (f : Additive (WithConv
        ((ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
          →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+
        AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (φ : (ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
          →ₐ[ℚ] AlgebraicClosure ℚ),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
          (E⁄(AlgebraicClosure ℚ)).Point) =
          WeierstrassCurve.Affine.Point.map σ.toAlgHom
            (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  -- LOCAL leaf (sorry node): the peu-ramifiée package over the
  -- COMPLETED integers — the pure Tate/Kummer content
  have hloc : WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
    by_cases hsp : (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
        𝒪[HeightOneSpectrum.adicCompletion ℚ
          hp'.toHeightOneSpectrumRingOfIntegersRat]
    · haveI := hsp
      -- the recentring witness (PROVEN, the step-(d) lemma above): from
      -- `p ∣ v_p(j)` the Tate parameter is a `p`-th power times a unit,
      -- `q_E · w⁻ᵖ ∈ 𝒪ˣ`
      obtain ⟨w, hmemw, hunitw⟩ :=
        exists_unit_qUnit_mul_inv_pow_isUnit hp'
          (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat))) (p := p)
          (WeierstrassCurve.map_j _ _) hj
      -- SPLIT KUMMER leaf (sorry node): with the Tate parameter
      -- recentred to a unit `u = q_E·w'⁻ᵖ` of the completed integers,
      -- the uniformization `exists_tateEquivSepClosure` presents
      -- `E[p] ⊂ Ω̂ˣ/q_Eᶻ` as `⟨ζ_p, w'·u^{1/p}⟩`, a *peu-ramifiée*
      -- extension of `ℤ/p` by `μ_p`; the finite flat model is the
      -- explicit Kummer group scheme with Hopf algebra
      -- `∏_{i<p} 𝒪[x]/(xᵖ − uⁱ)` (finite free of rank `p²`, étale
      -- generic fibre in characteristic zero), whose `Ω̂`-points are
      -- the `p²` torsion points `ζ_p^j·(w'·u^{1/p})^i` equivariantly
      have hsplitpkg : ∀ (w' : (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ)
          (hmem : (((E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).qUnit * w'⁻¹ ^ p :
              (HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat)ˣ) :
              HeightOneSpectrum.adicCompletion ℚ
                hp'.toHeightOneSpectrumRingOfIntegersRat) ∈
            HeightOneSpectrum.adicCompletionIntegers ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat),
          IsUnit (⟨_, hmem⟩ : HeightOneSpectrum.adicCompletionIntegers ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat) →
          WeierstrassCurve.TorsionFlatPackage
            𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
            (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)))
            p
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
        exact WeierstrassCurve.torsionFlatPackage_of_split_adic E hp' hp2
      exact hsplitpkg w hmemw hunitw
    · -- NONSPLIT TWIST leaf (sorry node): the quadratic unramified
      -- twist to split reduction
      -- (`exists_quadraticTwist_hasSplitMultiplicativeReduction`, as in
      -- `tate_inertia_unipotent_of_nonsplit` above) has the same
      -- `j`-invariant, so the split leaf provides its package;
      -- unramified quadratic descent of the Hopf model (the twisted
      -- form is the invariants of the base-changed model under the
      -- Galois-twisted involution, a finite flat Hopf order because
      -- the extension is unramified) yields the package for `E` itself
      have hnonsplitpkg :
          ¬(E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
            𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat] →
          WeierstrassCurve.TorsionFlatPackage
            𝒪[HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat]
            (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)
            (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)))
            p
            (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
              hp'.toHeightOneSpectrumRingOfIntegersRat)) := by
        exact WeierstrassCurve.torsionFlatPackage_of_nonsplit_adic E hp' hp2 hj
      exact hnonsplitpkg hsp
  -- DESCENT leaf (sorry node): the completed-integers package descends
  -- to `ℤ_(p)` with globally equivariant points
  have hdesc : WeierstrassCurve.TorsionFlatPackage
      𝒪[HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat]
      (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)
      (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)))
      p
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
        hp'.toHeightOneSpectrumRingOfIntegersRat)) →
      ∃ (H : Type) (_ : CommRing H)
        (_ : HopfAlgebra
          (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
        (_ : Module.Finite
          (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
        (_ : Module.Flat
          (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) H)
        (_ : Algebra.Etale ℚ
          (ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H))
        (f : Additive (WithConv
          ((ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
            →ₐ[ℚ] AlgebraicClosure ℚ)) ≃+
          AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)),
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (φ : (ℚ ⊗[Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal] H)
            →ₐ[ℚ] AlgebraicClosure ℚ),
          (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
            (E⁄(AlgebraicClosure ℚ)).Point) =
            WeierstrassCurve.Affine.Point.map σ.toAlgHom
              (f (Additive.ofMul (WithConv.toConv φ))) := by
    intro hl
    -- GLOBAL GENERIC-FIBRE leaf (sorry node): the package over `ℚ`
    -- itself (`R = K = ℚ`, flatness trivial) — the étale `ℚ`-Hopf
    -- algebra of Galois-equivariant functions on the finite Galois set
    -- `E[p](ℚ̄)` (Galois descent of the split algebra
    -- `Maps(E[p](ℚ̄), ℚ̄)`), whose `ℚ̄`-points are globally
    -- equivariantly the `p`-torsion; no local input
    have hglobal : WeierstrassCurve.TorsionFlatPackage ℚ ℚ E p
        (AlgebraicClosure ℚ) := by
      exact WeierstrassCurve.torsionFlatPackage_global E p
    -- LATTICE-INTERSECTION leaf (sorry node): a global generic-fibre
    -- package and a local completed-integers package glue to a package
    -- over `ℤ_(p) = ℚ ∩ ℤ_p`: the model is the intersection of the
    -- global algebra with the local Hopf model inside its completed
    -- base change (finite flat because finitely generated torsion-free
    -- over the DVR `ℤ_(p)`, a Hopf order because both intersectands
    -- are); the local-vs-global points comparison rides the chosen
    -- embedding `ℚ̄ ↪ ℚ̄_p` (`algClosureEmbeddingRat`,
    -- `algHomEquivOfFinite`/`mem_range_algebraicClosureMap_of_isIntegral`
    -- as in layer C of `FlatProlongation`)
    have hlattice : WeierstrassCurve.TorsionFlatPackage ℚ ℚ E p
          (AlgebraicClosure ℚ) →
        WeierstrassCurve.TorsionFlatPackage
          𝒪[HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat]
          (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)
          (E.map (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)))
          p
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
            hp'.toHeightOneSpectrumRingOfIntegersRat)) →
        WeierstrassCurve.TorsionFlatPackage
          (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)
          ℚ E p (AlgebraicClosure ℚ) := by
      exact WeierstrassCurve.torsionFlatPackage_localization_of_packages E hp'
    exact hlattice hglobal hl
  exact hdesc hloc

open TensorProduct in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local-global glue for flatness at multiplicative primes**
(DERIVED 2026-07-17 from the peu-ramifiée leaf above and the shared
flat transport, by the same assembly as the good-reduction case). -/
theorem WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime) (hp : 0 < p)
    [Fact p.Prime] (hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat p E.j) :
    (E.galoisRep p hp).IsFlatAt hp'.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, hf⟩ :=
    WeierstrassCurve.torsion_flat_of_multiplicative_reduction E hp' hp2 hj
  letI := hCR
  letI := hHopf
  letI := hFin
  letI := hFlat
  letI := hEt
  haveI : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    WeierstrassCurve.n_torsion_finite _ hp
  haveI : Module.Finite (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Module.Finite.of_finite
  let e : (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) ≃+
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine (E.galoisRep p hp).isFlatAt_of_dvr_package hp' H (f.trans e) ?_
  intro σ φ
  apply Subtype.ext
  exact hf σ φ

/-- **`p` is nonzero in the residue field of `ℤ_(q)` for `q ≠ p`**
(PROVEN 2026-07-16): `p` is a unit of the localization (its integer
representative is prime to `q`), and units have nonzero residue. This
discharges the `NeZero (n : ResidueField R)` hypothesis of the vendored
Néron–Ogg–Shafarevich and finite-flat-prolongation nodes in the glue
nodes below. -/
theorem neZero_natCast_residueField {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hqp : q ≠ p) :
    NeZero ((p : ℕ) : IsLocalRing.ResidueField
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) := by
  have hndvd : ¬((q : ℤ) ∣ (p : ℤ)) := by
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast h))
  have hu : IsUnit ((p : ℤ) :
      Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :=
    isUnit_intCast_localizationAtPrime hq hndvd
  refine ⟨?_⟩
  have h1 : (((p : ℕ)) : IsLocalRing.ResidueField
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) =
      IsLocalRing.residue _ (((p : ℤ) :
        Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) := by
    rw [map_intCast]
    norm_cast
  rw [h1]
  exact (hu.map (IsLocalRing.residue _)).ne_zero

open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local-global glue for Néron–Ogg–Shafarevich** (DERIVED
2026-07-17 from the vendored NOS node): an elliptic curve over `ℚ`
with good reduction at the place `q ≠ p` has unramified mod-`p`
torsion representation at `q`, in the `GaloisRep.IsUnramifiedAt` sense.
Assembly: instantiate `torsion_unramified_of_good_reduction` with
`R = ℤ_(q)`, `𝒪` the embedded valuation subring (its `h𝒪` is
`embeddedValuationSubring_comap_toSubring`); the image of a local
inertia element lies in `𝒪.inertiaSubgroup ℚ` by the spelling bridge,
and the NOS conclusion is precisely the pointwise fixing statement
that `ker`-membership unfolds to (the Galois action on torsion is the
ambient `Point.map`). Remaining `sorryAx` comes ONLY from the NOS node
itself. -/
theorem WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    (hodd : Odd p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasGoodReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (E.galoisRep p hp).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  constructor
  intro σ hσ
  haveI : NeZero ((p : ℕ) : IsLocalRing.ResidueField
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)) :=
    neZero_natCast_residueField hq (Fact.out : p.Prime) hqp
  have hNOS := WeierstrassCurve.torsion_unramified_of_good_reduction
    (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ E p
    (AlgebraicClosure ℚ)
    (embeddedValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
    (Fact.out : p.Prime) hodd
    (embeddedValuationSubring_comap_toSubring
      hq.toHeightOneSpectrumRingOfIntegersRat)
  have hmem := map_mem_inertiaSubgroup_of_mem_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat σ hσ
  -- the endomorphism is the identity on the `p`-torsion
  show ((E.galoisRep p hp).toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  -- the underlying point is fixed, which is the NOS conclusion
  have hP : (P : ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) ∈
      AddSubgroup.torsionBy
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point
        ((p : ℕ) : ℤ) := by
    have h1 := P.2
    rw [Submodule.mem_torsionBy_iff] at h1
    show ((p : ℕ) : ℤ) • (P : ((E.map (algebraMap ℚ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) = 0
    exact_mod_cast h1
  exact hNOS _ hmem P.1 hP

open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local-global glue for flatness at good primes** (DERIVED
2026-07-17 from the vendored finite-flat leaf and the shared flat
transport): an elliptic curve over `ℚ` with good reduction at the
place `p` has flat mod-`p` torsion representation at `p`. The vendored
leaf `torsion_flat_of_good_reduction` provides the DVR package over
`ℤ_(p)`; the shared transport node
`GaloisRep.isFlatAt_of_dvr_package` carries it to `IsFlatAt`. The
remaining `sorryAx` flows only through those two tracked nodes. -/
theorem WeierstrassCurve.isFlatAt_of_hasGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime) (hp : 0 < p)
    [Fact p.Prime]
    [E.HasGoodReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (E.galoisRep p hp).IsFlatAt hp'.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, hf⟩ :=
    WeierstrassCurve.torsion_flat_of_good_reduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ E p
      (AlgebraicClosure ℚ)
  letI := hCR
  letI := hHopf
  letI := hFin
  letI := hFlat
  letI := hEt
  -- the space of the representation is finite free over `ZMod p`
  haveI : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    WeierstrassCurve.n_torsion_finite _ hp
  haveI : Module.Finite (ZMod p)
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    Module.Finite.of_finite
  -- the identity-underlying bridge between the two torsion spellings
  let e : (AddSubgroup.torsionBy (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) ≃+
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine (E.galoisRep p hp).isFlatAt_of_dvr_package hp' H (f.trans e) ?_
  intro σ φ
  apply Subtype.ext
  exact hf σ φ

