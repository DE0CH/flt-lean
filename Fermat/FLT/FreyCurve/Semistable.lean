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

set_option warn.sorry false in
/-- **Good reduction of the Frey curve away from `2p`** (sorry node): at
an odd prime `q` not dividing `abc`, the Frey curve
`y² + xy = x³ + ((b^p-1-a^p)/4)x² - (a^p b^p/16)x` has good reduction
over the localization `ℤ_(q)`: its coefficients are `q`-integral (the
divisions by `4` and `16` only involve the prime `2`), and its
discriminant `(abc)^{2p}/2⁸` is a `q`-adic unit, so the equation is
minimal at `q` (no integral change of variables can raise a unit
valuation) with elliptic reduction. -/
theorem FreyPackage.freyCurve_hasGoodReduction_of_not_dvd (P : FreyPackage)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hndvd : ¬((q : ℤ) ∣ P.a * P.b * P.c)) :
    P.freyCurve.HasGoodReduction
      (Localization.AtPrime hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal) :=
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
