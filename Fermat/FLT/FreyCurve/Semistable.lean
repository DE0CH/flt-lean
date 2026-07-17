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
-- the unit-`c₄` Kraus–Laska minimality criterion, for the multiplicative case
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
-- the local-field instance package for `adicCompletion ℚ v` (the
-- `ValuativeRel`/`𝒪[·]` vocabulary of the completion-transfer lemma)
public import Fermat.FLT.Mathlib.NumberTheory.Padics.LocalField
-- the adic-vs-canonical valuation bridges over `𝒪[K]`
public import Fermat.FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic
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
  set R := Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal with hR
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
  refine { val_Δ_maximal := ⟨?_, fun C hC _ => ?_⟩, goodReduction := hval }
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
    with hR
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

open scoped WeierstrassCurve.Affine in
set_option warn.sorry false in
/-- **Pointwise inertia-triviality on torsion at multiplicative primes**
(sorry node — the TATE-THEORETIC content, stated in the same
valuation-subring language as the vendored Néron–Ogg–Shafarevich node
so that the PROVEN transport machinery applies verbatim): for an
elliptic curve over `ℚ` with multiplicative reduction at the odd place
`q ≠ p` whose `j`-invariant has `q`-adic valuation divisible by `p`,
every element of the inertia subgroup at a valuation subring of `ℚ̄`
lying over `ℤ_(q)` fixes the `p`-torsion pointwise. Content: after the
unramified quadratic twist making the reduction split
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`, vendored
PROVEN), Tate's uniformization (`exists_tateEquivSepClosure`) presents
`E[p]` inside `ℚ̄_qˣ/q_E^ℤ` as generated by `μ_p` (unramified, as
`q ≠ p`) and a `p`-th root of the Tate parameter `q_E`; since
`p ∣ v_q(j) = -v_q(q_E)`, the parameter is a `p`-th power times a unit,
so the root can be chosen with inertia acting trivially. -/
theorem WeierstrassCurve.torsion_unramified_of_multiplicative_reduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hq2 : q ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j)
    (𝒪 : ValuationSubring (AlgebraicClosure ℚ))
    (h𝒪 : (𝒪.comap (algebraMap ℚ (AlgebraicClosure ℚ))).toSubring =
      (algebraMap (Localization.AtPrime
        hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) ℚ).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup ℚ,
      ∀ P ∈ AddSubgroup.torsionBy
        (E⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ),
      WeierstrassCurve.Affine.Point.map
        ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P = P :=
  sorry

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

open IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
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
    (AlgebraicClosure ℚ) →ₐ[ℚ]
      (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v)) :=
  { AlgebraicClosure.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ v)) with
    commutes' := fun r => by
      have h1 := AlgebraicClosure.map_algebraMap
        (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)) r
      exact h1.trans (congrFun (congrArg DFunLike.coe (Subsingleton.elim
        ((algebraMap (HeightOneSpectrum.adicCompletion ℚ v)
          (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))).comp
          (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)))
        (algebraMap ℚ (AlgebraicClosure
          (HeightOneSpectrum.adicCompletion ℚ v))))) r) }

open IsDedekindDomain WeierstrassCurve in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Equivariance of the point transport** (PROVEN — step (C3)): for
`σ` in the local absolute Galois group, transporting a `ℚ̄`-point along
the chosen embedding and then acting by `σ` is the same as acting first
by the mapped global element. `Point.map_map` on both sides reduces
this to the field-level equivariance
`Field.absoluteGaloisGroup.lift_map`. -/
theorem point_map_algClosureEmbeddingRat_comm
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (σ : Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion ℚ v))
    (P : ((E)⁄(AlgebraicClosure ℚ)).Point) :
    WeierstrassCurve.Affine.Point.map (W' := E) (algClosureEmbeddingRat v)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (HeightOneSpectrum.adicCompletion ℚ v))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom P) =
    WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ v]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          v))).toAlgHom.restrictScalars ℚ)
      (WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingRat v) P) := by
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map]
  have hhomeq : (algClosureEmbeddingRat v).comp
      (((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (HeightOneSpectrum.adicCompletion ℚ v))) σ :
        AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom =
      ((σ : (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ v))
          ≃ₐ[HeightOneSpectrum.adicCompletion ℚ v]
        (AlgebraicClosure (HeightOneSpectrum.adicCompletion ℚ
          v))).toAlgHom.restrictScalars ℚ).comp
        (algClosureEmbeddingRat v) := by
    apply AlgHom.ext
    intro x
    exact Field.absoluteGaloisGroup.lift_map
      (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v)) σ x
  rw [hhomeq]

open scoped WeierstrassCurve.Affine in
set_option warn.sorry false in
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
        P = 0 :=
  sorry

open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Local-global glue for the Tate curve at multiplicative primes**
(DERIVED 2026-07-17 from the pointwise node above, by the SAME proven
transport as the good-reduction case): an elliptic curve over `ℚ` with
multiplicative reduction at the odd place `q ≠ p` whose `j`-invariant
has `q`-adic valuation divisible by `p` has unramified mod-`p` torsion
representation at `q`. -/
theorem WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hq2 : q ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j) :
    (E.galoisRep p hp).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  constructor
  intro σ hσ
  have hNOS := WeierstrassCurve.torsion_unramified_of_multiplicative_reduction
    E hq hqp hq2 hj
    (embeddedValuationSubring hq.toHeightOneSpectrumRingOfIntegersRat)
    (embeddedValuationSubring_comap_toSubring
      hq.toHeightOneSpectrumRingOfIntegersRat)
  have hmem := map_mem_inertiaSubgroup_of_mem_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat σ hσ
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
  exact hNOS _ hmem P.1 hP

open TensorProduct in
open scoped WeierstrassCurve.Affine in
set_option warn.sorry false in
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
schemes over `ℤ_p`. -/
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
            (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

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

