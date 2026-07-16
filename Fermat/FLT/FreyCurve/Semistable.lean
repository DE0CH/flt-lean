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

set_option warn.sorry false in
/-- **Local-global glue for the Tate curve at multiplicative primes**
(sorry node): an elliptic curve over `ℚ` with multiplicative reduction at
the odd place `q ≠ p` whose `j`-invariant has `q`-adic valuation
divisible by `p` has unramified mod-`p` torsion representation at `q`.
The mathematical content: after the unramified quadratic twist making
the reduction split
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`, vendored
PROVEN), Tate's uniformization (`exists_tateEquivSepClosure`) presents
`E[p]` inside `ℚ̄_qˣ/q_E^ℤ` as generated by `μ_p` (unramified, as
`q ≠ p`) and a `p`-th root of the Tate parameter `q_E`; since
`p ∣ v_q(j) = -v_q(q_E)`, the parameter is a `p`-th power times a unit,
so the root can be chosen with inertia acting trivially. -/
theorem WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hq2 : q ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat q E.j) :
    (E.galoisRep p hp).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **Local-global glue for flatness at multiplicative primes** (sorry
node): an elliptic curve over `ℚ` with multiplicative reduction at the
odd place `p` whose `j`-invariant has `p`-adic valuation divisible by
`p` has flat mod-`p` torsion representation at `p`. The mathematical
content: the Tate parameter is a `p`-th power times a unit
(`p ∣ v_p(j) = -v_p(q_E)`), so the Tate-curve extension
`0 → μ_p → E[p] → ℤ/p → 0` over `ℚ_p` is *peu ramifiée* in the sense of
Serre, and such extensions prolong to finite flat group schemes over
`ℤ_p`. -/
theorem WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime) (hp : 0 < p)
    [Fact p.Prime] (hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hj : (p : ℤ) ∣ padicValRat p E.j) :
    (E.galoisRep p hp).IsFlatAt hp'.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **Local-global glue for Néron–Ogg–Shafarevich** (sorry node): an
elliptic curve over `ℚ` with good reduction at the place `q ≠ p` has
unramified mod-`p` torsion representation at `q`, in the
`GaloisRep.IsUnramifiedAt` sense (`localInertiaGroup q` is killed by
`ρ.toLocal q`). To be closed against the vendored NOS node
`WeierstrassCurve.torsion_unramified_of_good_reduction` (with
`R = ℤ_(q)`, `k = ℚ`, `kˢᵉᵖ = AlgebraicClosure ℚ`, and `𝒪` the
valuation subring induced by the embedding `ℚ̄ ↪ ℚ̄_q` fixed by
`GaloisRep.toLocal`); the residual content is the inertia dictionary
described in the module docstring, plus `NeZero (p : 𝔽_q)` from
`q ≠ p`. -/
theorem WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    [E.HasGoodReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (E.galoisRep p hp).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **Local-global glue for flatness at good primes** (sorry node): an
elliptic curve over `ℚ` with good reduction at the place `p` has flat
mod-`p` torsion representation at `p`, in the `GaloisRep.IsFlatAt` sense.
To be closed against the vendored finite-flat-prolongation node
`WeierstrassCurve.torsion_flat_of_good_reduction`
(`KnownIn1980s/EllipticCurves/Flat.lean`, stated for an arbitrary DVR:
the `p`-torsion of a curve with good reduction prolongs to a finite flat
group scheme, presented as a Hopf algebra with étale generic fibre and
equivariant points isomorphism — exactly the `HasFlatProlongationAt`
package); what remains on top of it is transporting that package along
`ℤ_(p) → ℤ_p = 𝒪ᵥ` and the identification of the local torsion with
`(ρ.toLocal p).Space`. -/
theorem WeierstrassCurve.isFlatAt_of_hasGoodReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp' : p.Prime) (hp : 0 < p)
    [Fact p.Prime]
    [E.HasGoodReduction
      (Localization.AtPrime hp'.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (E.galoisRep p hp).IsFlatAt hp'.toHeightOneSpectrumRingOfIntegersRat :=
  sorry
