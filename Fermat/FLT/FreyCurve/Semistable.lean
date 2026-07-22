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
      hq.toHeightOneSpectrumRingOfIntegersRat)).toMonoidHom r with hw
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
    hq.toHeightOneSpectrumRingOfIntegersRat) := X.quadraticTwist L with hTwdef
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := Tw.minimal
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat] with hMtdef
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
    hq.toHeightOneSpectrumRingOfIntegersRat) := X.quadraticTwist L with hTwdef
  set Mt : WeierstrassCurve (HeightOneSpectrum.adicCompletion ℚ
    hq.toHeightOneSpectrumRingOfIntegersRat) := Tw.minimal
    𝒪[HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat] with hMtdef
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
  already used by the unramifiedness glue in this file. -/
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
    sorry
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
    sorry
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

