/-
Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean — own work for the
Fermat project (not vendored from the FLT project).

# The ring of invariants of a Dedekind domain under a finite group

This module is the commutative-algebra half of "the coarse space of a
Katz–Mazur atlas is a smooth geometrically connected curve": everything about
`Spec (A^G)` that can be said without mentioning a moduli problem.

Its consumer is `Fermat/FLT/ModularCurve/X0.lean`, where `A` is the coordinate
ring of the rigidified moduli scheme `𝔐([Γ₀(N)], [Γ(n)])`, `G = GL₂(ℤ/n)` is
the deck group and `B = A^G` is the coordinate ring of `Y_0(N)`.  Nothing here
knows that; the statements are about an arbitrary finite group acting on an
arbitrary Dedekind domain of finite type over a field.

## The classical statement

Let `k` be a field, `S` a Dedekind domain of finite type over `k`, `G` a finite
group acting on `S` by `k`-algebra automorphisms, and `R = S^G` its ring of
invariants.  Then `R` is again a Dedekind domain of finite type over `k`, with
the same Krull dimension as `S`.  The three inputs are:

1. **Noether's theorem on invariants** — `R` is of finite type over `k`.  The
   proof here is the Artin–Tate one: `S` is integral over `R`
   (`Algebra.IsInvariant.isIntegral`, mathlib) and of finite type over `R`,
   hence module-finite over `R`, and `Algebra.fg_of_fg_of_fg` (mathlib's
   Artin–Tate lemma, Atiyah–Macdonald 7.8) concludes.
2. **Invariants of a normal domain are normal** — Matsumura §23, or
   Bourbaki *Commutative Algebra* V §1.9.  This is
   `isIntegrallyClosed_of_isInvariant`.
3. **Krull dimension is unchanged by a finite group quotient** — because `S` is
   integral over `R`, going up and incomparability make
   `PrimeSpectrum S → PrimeSpectrum R` a surjection that reflects and preserves
   strict inclusions.  Here only the one-dimensional case is needed, so it is
   proven directly from `Ring.DimensionLEOne` plus lying over.

Regularity is then free: mathlib has `[IsDedekindDomain R] : IsRegularRing R`.

## Geometric integrality

The second half of the consumer's needs is that `B ⊗[ℚ] K` is a domain for every
field extension `K/ℚ`.  The pieces live here:

* `isDomain_tensorProduct_of_algebraicClosure_eq_bot` — the field-theoretic
  statement that a field extension `L/k` over a PERFECT `k` with `k`
  algebraically closed in `L` is a *regular* extension, i.e. `L ⊗[k] K` is a
  domain for every `K/k`.  (The hypothesis was `CharZero k` until 2026-07-28; it
  was weakened to `PerfectField k`, which is what the ALGEBRAIC half actually
  uses and what the characteristic-`p` consumer over `𝔽_p` needs — see
  `isDomain_tensorProduct_of_isAlgebraic_mem_bot`'s use in
  `ModularCurve/X0.lean` over `k = ZMod p`.  `CharZero ⟹ PerfectField` is an
  instance, so no call site changed.)  PROVEN for `K/k` **algebraic**, and
  reduced in general to the finitely generated subextensions of `K`.

  The transcendental case
  (`isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`)
  is **PROVEN in characteristic zero** (2026-07-29) via
  `isDomain_tensorProduct_of_isTranscendenceBasis`, whose only new mathematical
  input is `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` —
  *purely transcendental base change preserves "algebraically closed in"*.  The
  one remaining LEAF of this module is that same case in **positive
  characteristic**: the char-0 route does not survive the `PerfectField`
  weakening, because it applies the algebraic half over `Fk = k(ι)`, and a
  rational function field in characteristic `p` is **not** perfect (and the
  specialisation argument additionally needs `k` infinite).  See the leaf's own
  docstring.

* `isDomain_tensorProduct_of_injective` — the transfer from the fraction field
  down to the ring, which is just flatness of a field over a field (PROVEN).

## Contents

* `Algebra.IsInvariant.finiteType_of_isInvariant` — Noether (PROVEN)
* `Algebra.IsInvariant.isIntegrallyClosed_of_isInvariant` — normality (PROVEN)
* `Algebra.IsInvariant.dimensionLEOne_of_isInvariant` — dimension ≤ 1 (PROVEN)
* `Algebra.IsInvariant.ringKrullDim_eq_one_of_isInvariant` — dimension = 1 (PROVEN)
* `Algebra.IsInvariant.isDedekindDomain_of_isInvariant` — assembly (PROVEN)
* `Algebra.IsInvariant.isRegularRing_of_isInvariant` — the packaged conclusion
  the modular-curve consumer asks for (PROVEN)
* `algebraicClosure_fractionRing_eq_bot` — `k` is algebraically closed in
  `Frac B` as soon as it is algebraically closed in the normal domain `B` (PROVEN)
* `minpoly_map_eq_of_algebraicClosure_eq_bot` — minimal polynomials over `k`
  stay irreducible over `L` (PROVEN); the heart of the regularity argument
* `linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot`,
  `linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot` — linear
  disjointness of an algebraic intermediate field from `L` (PROVEN)
* `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot` — the
  algebraic half of regularity (PROVEN)
* `isDomain_tensorProduct_of_forall_adjoin_finset` — reduction to finitely
  generated subextensions of `K` (PROVEN)
* `isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`
  — the transcendental half, for a finitely generated subextension
  (PROVEN in characteristic zero; LEAF in characteristic `p`)
* `isDomain_tensorProduct_of_isTranscendenceBasis` — the transcendental half in
  full generality, `[CharZero k]` (PROVEN)
* `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` — purely
  transcendental base change preserves "algebraically closed in" (PROVEN)
* `isDomain_tensorProduct_of_algebraicClosure_eq_bot` — regular extensions
  (PROVEN over the transcendental leaf)
* `isDomain_tensorProduct_of_injective` — descent to a subring (PROVEN)
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Maps
-- `mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries` at the end of this file
-- needs the `UniqueFactorizationMonoid`/`IsDiscreteValuationRing` structure of `k⟦X⟧`
-- and `PowerSeries.isUnit_iff_constantCoeff`.
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section

open scoped TensorProduct

namespace Algebra.IsInvariant

/-! ### Noether's theorem on invariants -/

/-- **Noether's theorem on invariants** (PROVEN): the invariants of a
finite-type algebra under a finite group are again of finite type.

The proof is Artin–Tate.  `S` is integral over `R = S^G` because `G` is finite
(`Algebra.IsInvariant.isIntegral`, mathlib), and `S` is of finite type over `R`
because it is of finite type over `k`; an integral algebra of finite type is
module-finite, so `Algebra.fg_of_fg_of_fg` applies to the tower `k ⊆ R ⊆ S`. -/
theorem finiteType_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.FiniteType k R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg k R S ‹Algebra.FiniteType k S›.out ‹Module.Finite R S›.fg_top hinj⟩

/-! ### Invariants of a normal domain are normal -/

/-- **Invariants of an integrally closed domain are integrally closed**
(PROVEN) — Matsumura §23, Bourbaki *Commutative Algebra* V §1.9.

Write `K = Frac R`, `L = Frac S`.  Because `R → S` is injective and `S` is a
domain, `K` embeds in `L` as a subfield (`FractionRing.liftAlgebra`), and the
`G`-action on `S` extends to `L` (`IsFractionRing.mulSemiringAction`) fixing the
image of `K` pointwise — each element of `K` is a quotient of elements of `R`,
and `G` fixes `R` by `SMulCommClass G R S`.

Now let `x ∈ K` be integral over `R`.  Then its image `z ∈ L` is integral over
`S`, so `z = algebraMap S L s` for some `s ∈ S` because `S` is integrally
closed; `z` is `G`-fixed, hence so is `s`, hence `s` lies in the image of `R` by
`Algebra.IsInvariant`; and that preimage maps to `x` because `K → L` is
injective.  That is exactly the criterion `isIntegrallyClosed_iff`. -/
theorem isIntegrallyClosed_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [IsDomain S] [IsIntegrallyClosed S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsIntegrallyClosed R := by
  letI := IsFractionRing.mulSemiringAction G S (FractionRing S)
  haveI := IsFractionRing.smulDistribClass G S (FractionRing S)
  haveI hRL : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (IsFractionRing.injective S (FractionRing S)).comp hinj
  haveI : FaithfulSMul R (FractionRing S) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hRL
  letI := FractionRing.liftAlgebra R (FractionRing S)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have hKL : Function.Injective (algebraMap (FractionRing R) (FractionRing S)) :=
    (algebraMap (FractionRing R) (FractionRing S)).injective
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr ?_
  intro x hx
  set z : FractionRing S := algebraMap (FractionRing R) (FractionRing S) x with hz
  have hzR : IsIntegral R z := hx.map (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing S))
  have hzS : IsIntegral S z := hzR.tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzS
  have hfix : ∀ g : G, g • z = z := by
    intro g
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hmap : ∀ r : R, g • (algebraMap R (FractionRing S) r)
        = algebraMap R (FractionRing S) r := by
      intro r
      rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
      simp [← algebraMap.coe_smul', smul_algebraMap]
    rw [hz]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
      ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]
    rw [show g • (algebraMap R (FractionRing S) a / algebraMap R (FractionRing S) b)
        = (g • algebraMap R (FractionRing S) a) / (g • algebraMap R (FractionRing S) b) from
      map_div₀ (MulSemiringAction.toRingHom G (FractionRing S) g) _ _, hmap, hmap]
  have key : ∀ (g : G) (t : S), algebraMap S (FractionRing S) (g • t)
      = g • algebraMap S (FractionRing S) t := by
    intro g t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_distrib_smul, smul_one]
  have hsfix : ∀ g : G, g • s = s := by
    intro g
    apply IsFractionRing.injective S (FractionRing S)
    rw [key g s, hs, hfix g]
  obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := R) (B := S) (G := G) s hsfix
  refine ⟨y, ?_⟩
  apply hKL
  rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
    IsScalarTower.algebraMap_eq R S (FractionRing S)]
  simp only [RingHom.coe_comp, Function.comp_apply, hy, hs, hz]

/-! ### Krull dimension -/

/-- **A finite group quotient does not raise the dimension above one** (PROVEN).

A nonzero prime `p` of `R` lies under some prime `Q` of `S` (lying over, valid
because `S` is integral over `R` and `R → S` is injective), that `Q` is nonzero
because its contraction is, hence maximal since `dim S ≤ 1`, and the
contraction of a maximal ideal along an integral extension is maximal. -/
theorem dimensionLEOne_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain S] [Ring.DimensionLEOne S]
    (hinj : Function.Injective (algebraMap R S)) :
    Ring.DimensionLEOne R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  refine ⟨fun {p} hp0 hp => ?_⟩
  haveI := hp
  have hcomapbot : (⊥ : Ideal S).comap (algebraMap R S) = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hinj (by simpa using h), fun h => by simp [h]⟩
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := R) (S := S) p
      (by rw [RingHom.ker_eq_comap_bot, hcomapbot]; exact bot_le)
  haveI := hQ
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp0 (by rw [← hQc, hcomapbot])
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ hQ0
  exact hQc ▸ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) Q

/-- **The Krull dimension is unchanged** (PROVEN, in the only case needed).

`≤` is `dimensionLEOne_of_isInvariant`.  `≥` holds because contraction along an
integral extension is strictly monotone on primes
(`Ideal.IsIntegral.comap_lt_comap`), so it embeds a chain of `Spec S` into a
chain of `Spec R`. -/
theorem ringKrullDim_eq_one_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain S] [Ring.DimensionLEOne S]
    (hinj : Function.Injective (algebraMap R S)) (hdim : ringKrullDim S = (1 : ℕ)) :
    ringKrullDim R = (1 : ℕ) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI := dimensionLEOne_of_isInvariant R S G hinj
  refine le_antisymm (Ring.krullDimLE_iff.mp inferInstance) ?_
  rw [← hdim]
  refine Order.krullDim_le_of_strictMono
    (fun Q : PrimeSpectrum S => (⟨Q.asIdeal.comap (algebraMap R S), inferInstance⟩ :
      PrimeSpectrum R)) ?_
  intro Q Q' h
  exact Ideal.IsIntegral.comap_lt_comap h

/-! ### The packaged conclusion -/

/-- **The invariants of a Dedekind domain of finite type over a field form a
Dedekind domain of finite type over that field** (PROVEN) — the assembly of the
three inputs above.

`IsNoetherianRing R` is not an extra input: it follows from
`Algebra.FiniteType k R` by the Hilbert basis theorem. -/
theorem isDedekindDomain_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDedekindDomain S] (hinj : Function.Injective (algebraMap R S)) :
    IsDomain R ∧ IsDedekindDomain R ∧ Algebra.FiniteType k R := by
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R S) hinj
  haveI hft : Algebra.FiniteType k R := finiteType_of_isInvariant k R S G hinj
  haveI hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI hic : IsIntegrallyClosed R := isIntegrallyClosed_of_isInvariant R S G hinj
  haveI hd1 : Ring.DimensionLEOne R := dimensionLEOne_of_isInvariant R S G hinj
  haveI : IsDedekindRing R := { hnoeth, hd1, hic with }
  exact ⟨hdom, inferInstance, hft⟩

/-- **The coarse ring of a one-dimensional Dedekind presentation is a regular
finite-type domain of Krull dimension one** (PROVEN).

This is the exact package the modular-curve consumer
`isRegularRing_coarseRing_of_gamma0GITPresentation` asks for; `IsRegularRing`
comes from mathlib's instance `[IsDedekindDomain R] : IsRegularRing R`. -/
theorem isRegularRing_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDedekindDomain S] (hinj : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim S = (1 : ℕ)) :
    IsDomain R ∧ IsRegularRing R ∧ Algebra.FiniteType k R ∧ ringKrullDim R = (1 : ℕ) := by
  obtain ⟨hdom, hded, hft⟩ := isDedekindDomain_of_isInvariant k R S G hinj
  haveI := hdom
  haveI := hded
  exact ⟨hdom, inferInstance, hft, ringKrullDim_eq_one_of_isInvariant R S G hinj hdim⟩

end Algebra.IsInvariant

/-! ### Regular field extensions and geometric integrality -/

/-- **`k` is algebraically closed in `Frac B` as soon as it is algebraically
closed in the normal domain `B`** (PROVEN).

An element of `Frac B` algebraic over the field `k` is integral over `k`, hence
integral over `B`; as `B` is integrally closed in its fraction field it comes
from an element of `B`, which is then algebraic over `k` and so lies in the
image of `k` by hypothesis.

The `k`-algebra structure on `FractionRing B` is the one mathlib already
supplies for a localization, and it is compatible with `Algebra k B` by the
ambient `IsScalarTower k B (FractionRing B)` instance, so it is not a choice. -/
theorem algebraicClosure_fractionRing_eq_bot
    (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [IsIntegrallyClosed B]
    (h : ∀ x : B, IsAlgebraic k x → x ∈ (⊥ : Subalgebra k B)) :
    algebraicClosure k (FractionRing B) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [mem_algebraicClosure_iff'] at hx
  have hxB : IsIntegral B x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxB
  have hy : IsAlgebraic k y :=
    ((isIntegral_algebraMap_iff
      (IsFractionRing.injective B (FractionRing B))).mp hx).isAlgebraic
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (h y hy)
  rw [IntermediateField.mem_bot]
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply k B (FractionRing B), hc]⟩

/-- **Minimal polynomials over `k` stay irreducible over `L` when `k` is
algebraically closed in `L`** (PROVEN).

This is the heart of the regularity argument.  Let `M/L/k` be a tower of fields
and `x : M` integral over `k`.  Then `minpoly L x` divides `(minpoly k x).map`,
so by Stacks 00H6 (`Polynomial.isIntegral_coeff_of_dvd`) every coefficient of
`minpoly L x` is integral over `k` — and it lies in `L`, hence in
`algebraicClosure k L = ⊥`, i.e. in `k`.  So `minpoly L x` descends to a monic
`q : k[X]` killing `x`, whence `minpoly k x ∣ q`; and `q ∣ minpoly k x` because
their images under the injective map `k[X] → L[X]` divide one another.  Both are
monic, so they agree.

Concretely: `[L(x) : L] = [k(x) : k]`, which is exactly the linear
disjointness of `k(x)` and `L` over `k`. -/
theorem minpoly_map_eq_of_algebraicClosure_eq_bot
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M] [Algebra L M]
    [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥) {x : M} (hx : IsIntegral k x) :
    minpoly L x = (minpoly k x).map (algebraMap k L) := by
  have hxL : IsIntegral L x := hx.tower_top
  have hdvd : minpoly L x ∣ (minpoly k x).map (algebraMap k L) :=
    minpoly.dvd_map_of_isScalarTower k L x
  have hcoe : ∀ i, (minpoly L x).coeff i ∈ Set.range (algebraMap k L) := by
    intro i
    have hint : IsIntegral k ((minpoly L x).coeff i) :=
      Polynomial.isIntegral_coeff_of_dvd (minpoly k x) (minpoly L x)
        (minpoly.monic hx) (minpoly.monic hxL) hdvd i
    have hmem : (minpoly L x).coeff i ∈ algebraicClosure k L := mem_algebraicClosure_iff'.mpr hint
    rw [hbot, IntermediateField.mem_bot] at hmem
    exact hmem
  obtain ⟨q, hq1, -, hq3⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts (f := algebraMap k L) (minpoly L x)).mpr hcoe)
    (minpoly.monic hxL)
  have haeval : (Polynomial.aeval x) q = 0 := by
    have h0 := minpoly.aeval L x
    rw [← hq1, Polynomial.aeval_map_algebraMap] at h0
    exact h0
  have hdvd2 : minpoly k x ∣ q := minpoly.dvd k x haeval
  have hdvd3 : q ∣ minpoly k x := by
    rw [← Polynomial.map_dvd_map' (algebraMap k L), hq1]
    exact hdvd
  have heq : q = minpoly k x :=
    Polynomial.eq_of_monic_of_associated hq3 (minpoly.monic hx)
      (associated_of_dvd_dvd hdvd3 hdvd2)
  rw [← hq1, heq]

/-- **A finite-dimensional intermediate field is linearly disjoint from `L`**
(PROVEN).

`k` is perfect, so `A/k` is separable and has a primitive element `α`, and
`A` has the `k`-basis `1, α, …, α^{d-1}` with `d = deg (minpoly k α)`.  By
`minpoly_map_eq_of_algebraicClosure_eq_bot` the minimal polynomial of `α` over
`L` still has degree `d`, so those powers stay `L`-linearly independent inside
`M`; that is `IntermediateField.LinearDisjoint.of_basis_left`. -/
theorem linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot
    {k L M : Type*} [Field k] [PerfectField k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [FiniteDimensional k A] : A.LinearDisjoint L := by
  let pb : PowerBasis k A := Field.powerBasisOfFiniteOfSeparable k A
  set β : M := (pb.gen : M) with hβ
  have hint : IsIntegral k β := (Algebra.IsIntegral.isIntegral (R := k) pb.gen).map A.val
  have hmp : minpoly k β = minpoly k pb.gen := minpoly.algHom_eq A.val A.val.injective pb.gen
  have hdeg : (minpoly L β).natDegree = pb.dim := by
    rw [minpoly_map_eq_of_algebraicClosure_eq_bot hbot hint, Polynomial.natDegree_map, hmp,
      pb.natDegree_minpoly]
  have hLI : LinearIndependent L (fun i : Fin pb.dim => β ^ (i : ℕ)) :=
    (linearIndependent_pow (K := L) β).comp (finCongr hdeg.symm) (finCongr hdeg.symm).injective
  refine IntermediateField.LinearDisjoint.of_basis_left pb.basis ?_
  have hval : ⇑A.val ∘ pb.basis = fun i : Fin pb.dim => β ^ (i : ℕ) := by
    funext i
    show ((pb.basis i : A) : M) = β ^ (i : ℕ)
    rw [pb.coe_basis, hβ]
    push_cast
    ring
  rw [hval]
  exact hLI

/-- **An algebraic intermediate field is linearly disjoint from `L`** (PROVEN).

Linear independence is a statement about finite subfamilies, and every finite
subfamily of a `k`-basis of `A` lies in the finite-dimensional intermediate
field it generates; apply
`linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot` there.  This is
the colimit step of the classical argument, done at the level of linear
independence rather than of tensor products, which avoids having to build the
directed colimit of the `L ⊗[k] A₀`. -/
theorem linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot
    {k L M : Type*} [Field k] [PerfectField k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [Algebra.IsAlgebraic k A] : A.LinearDisjoint L := by
  classical
  let a := Module.Free.chooseBasis k A
  refine IntermediateField.LinearDisjoint.of_basis_left a ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  set T : Set M := (fun j => ((a j : A) : M)) '' (s : Set _) with hT
  haveI : Finite T := (s.finite_toSet.image _)
  have hTint : ∀ x ∈ T, IsIntegral k x := by
    rintro _ ⟨j, -, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := k) (a j)).map A.val
  set A₀ : IntermediateField k M := IntermediateField.adjoin k T with hA₀
  haveI : FiniteDimensional k A₀ := IntermediateField.finiteDimensional_adjoin hTint
  have hld0 : A₀.LinearDisjoint L :=
    linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot hbot A₀
  have hmem : ∀ j ∈ s, ((a j : A) : M) ∈ A₀ := fun j hj =>
    IntermediateField.subset_adjoin k T ⟨j, hj, rfl⟩
  let b : {j // j ∈ s} → A₀ := fun j => ⟨((a j.1 : A) : M), hmem j.1 j.2⟩
  have hbM : LinearIndependent k (fun j : {j // j ∈ s} => ((a j.1 : A) : M)) := by
    have h1 : LinearIndependent k (fun j : {j // j ∈ s} => a j.1) :=
      a.linearIndependent.comp _ Subtype.val_injective
    exact h1.map' A.val.toLinearMap (LinearMap.ker_eq_bot.mpr A.val.injective)
  have hb : LinearIndependent k b := LinearIndependent.of_comp A₀.val.toLinearMap hbM
  have hbL' : LinearIndependent L (fun j : {j // j ∈ s} => ((a j.1 : A) : M)) :=
    hld0.linearIndependent_left hb
  have hsum' : ∑ j : {j // j ∈ s}, g j.1 • ((a j.1 : A) : M) = 0 := by
    rw [Finset.sum_coe_sort s (fun j => g j • ((a j : A) : M))]
    exact hsum
  exact Fintype.linearIndependent_iff.mp hbL' (fun j => g j.1) hsum' ⟨i, hi⟩

/-- **The algebraic half of regularity** (PROVEN).

If `k` is algebraically closed in `L` (characteristic zero) and `K/k` is
algebraic, then `L ⊗[k] K` is a domain.  Embed `K` into an algebraic closure `M`
of `L` (possible because `K/k` is algebraic), apply
`linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot` to the image, and
conclude with `IntermediateField.LinearDisjoint.isDomain'`. -/
theorem isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    IsDomain (L ⊗[k] K) := by
  set M := AlgebraicClosure L with hM
  let fa : K →ₐ[k] M := IsAlgClosed.lift
  haveI : Algebra.IsAlgebraic k fa.fieldRange := (AlgEquiv.ofInjectiveField fa).isAlgebraic
  have hld : (fa.fieldRange).LinearDisjoint L :=
    linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot hbot _
  have hld2 : (fa.fieldRange).LinearDisjoint ((IsScalarTower.toAlgHom k L M).fieldRange) := by
    rw [IntermediateField.linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]
    rw [IntermediateField.linearDisjoint_iff] at hld
    exact hld
  haveI : IsDomain (K ⊗[k] L) := IntermediateField.LinearDisjoint.isDomain' hld2
  exact (Algebra.TensorProduct.comm k L K).toMulEquiv.isDomain

set_option maxSynthPendingDepth 2 in
/-- **Being a domain after `⊗[k] K` is detected on the finitely generated
subextensions of `K`** (PROVEN).

`L ⊗[k] K` is the directed union of the `L ⊗[k] k(S)` over finite `S ⊆ K`: every
element of a tensor product is a finite sum of pure tensors, so it comes from
one of them, and each transition map is injective because `L` is flat over the
field `k`.  So a product of two nonzero elements can be tested inside a single
`L ⊗[k] k(S)`.

This runs the colimit step at the level of *elements* rather than by building a
directed colimit of algebras, which is why it needs no colimit API at all.

`maxSynthPendingDepth` has to be raised by one: deciding
`NoZeroDivisors (L ⊗[k] ↥(adjoin k S))` from the supplied `IsDomain` requires
Lean to discharge the pending `Semiring (L ⊗[k] ↥(adjoin k S))` obligation
through the tensor-product-of-intermediate-field tower, which is one layer
deeper than the default budget.  This is an elaborator budget, not a resource
bump masking a failure: the proof term is unchanged. -/
theorem isDomain_tensorProduct_of_forall_adjoin_finset
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (K : Type*) [Field K] [Algebra k K]
    (H : ∀ S : Finset K, IsDomain (L ⊗[k] (IntermediateField.adjoin k (S : Set K)))) :
    IsDomain (L ⊗[k] K) := by
  classical
  haveI : Nontrivial (L ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k L K
      (algebraMap k L).injective (algebraMap k K).injective
  set ψ : ∀ S : Finset K, L ⊗[k] (IntermediateField.adjoin k (S : Set K)) →ₐ[k] L ⊗[k] K :=
    fun S => Algebra.TensorProduct.map (AlgHom.id k L)
      (IntermediateField.adjoin k (S : Set K)).val with hψ
  have hψinj : ∀ S : Finset K, Function.Injective (ψ S) := by
    intro S
    have hcoe : ∀ z, ψ S z =
        LinearMap.lTensor L (IntermediateField.adjoin k (S : Set K)).val.toLinearMap z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hψ]
      | add u v hu hv => simp [map_add, hu, hv]
    have hlt : Function.Injective
        (LinearMap.lTensor L (IntermediateField.adjoin k (S : Set K)).val.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _
        (IntermediateField.adjoin k (S : Set K)).val.injective
    intro u v huv
    exact hlt (by rw [← hcoe, ← hcoe, huv])
  have hmono : ∀ (S T : Finset K), S ⊆ T → Set.range (ψ S) ⊆ Set.range (ψ T) := by
    intro S T h
    have hle : IntermediateField.adjoin k (S : Set K) ≤ IntermediateField.adjoin k (T : Set K) :=
      IntermediateField.adjoin.mono k _ _ (by exact_mod_cast h)
    have key : ∀ z, ψ T (Algebra.TensorProduct.map (AlgHom.id k L)
        (IntermediateField.inclusion hle) z) = ψ S z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [hψ]
      | add u v hu hv => simp [map_add, hu, hv]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, key z⟩
  have hmem : ∀ x : L ⊗[k] K, ∃ S : Finset K, x ∈ Set.range (ψ S) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨∅, 0, map_zero _⟩
    | tmul a b =>
        refine ⟨{b}, a ⊗ₜ ⟨b, IntermediateField.subset_adjoin k _ (by simp)⟩, ?_⟩
        simp [hψ]
    | add u v hu hv =>
        obtain ⟨S₁, hS₁⟩ := hu
        obtain ⟨S₂, hS₂⟩ := hv
        obtain ⟨a, ha⟩ := hmono S₁ (S₁ ∪ S₂) Finset.subset_union_left hS₁
        obtain ⟨b, hb⟩ := hmono S₂ (S₁ ∪ S₂) Finset.subset_union_right hS₂
        exact ⟨S₁ ∪ S₂, a + b, by rw [map_add, ha, hb]⟩
  have main : ∀ a b : L ⊗[k] K, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    obtain ⟨S₁, hS₁⟩ := hmem a
    obtain ⟨S₂, hS₂⟩ := hmem b
    obtain ⟨x, hx⟩ := hmono S₁ (S₁ ∪ S₂) Finset.subset_union_left hS₁
    obtain ⟨y, hy⟩ := hmono S₂ (S₁ ∪ S₂) Finset.subset_union_right hS₂
    have hzero : ψ (S₁ ∪ S₂) (x * y) = 0 := by rw [map_mul, hx, hy, hab]
    have h0 : x * y = 0 := hψinj _ (by rw [hzero, map_zero])
    haveI := H (S₁ ∪ S₂)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (by rw [← hx, h, map_zero])
    · exact Or.inr (by rw [← hy, h, map_zero])
  haveI : NoZeroDivisors (L ⊗[k] K) := ⟨fun {a b} h => main a b h⟩
  exact {}

/-- **Geometric integrality descends from the fraction field to the ring**
(PROVEN).

If `B` is a `k`-algebra which embeds in a `k`-algebra `L` and `L ⊗[k] K` is a
domain, then so is `B ⊗[k] K`: over a field every module is flat, so
`B ⊗[k] K → L ⊗[k] K` is injective, and a subring of a domain is a domain. -/
theorem isDomain_tensorProduct_of_injective
    (k B L K : Type*) [Field k] [CommRing B] [CommRing L] [CommRing K]
    [Algebra k B] [Algebra k L] [Algebra k K]
    (f : B →ₐ[k] L) (hf : Function.Injective f) [IsDomain (L ⊗[k] K)] :
    IsDomain (B ⊗[k] K) := by
  have hcoe : ∀ x : B ⊗[k] K, Algebra.TensorProduct.map f (AlgHom.id k K) x
      = LinearMap.rTensor K f.toLinearMap x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hrt : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  have hinj : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k K)) := by
    intro x y hxy
    refine hrt ?_
    rw [← hcoe x, ← hcoe y]
    exact hxy
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.map f (AlgHom.id k K)).toRingHom hinj

/-! ### Purely transcendental base change preserves "algebraically closed in"

This section supplies the one genuinely new piece of mathematics behind the
transcendental half of regularity, Bourbaki *Algebra* V §17 / EGA IV 4.6.1 /
Stacks `04KM`:

> if `k` is algebraically closed in `L` and `k` is infinite, then `k(T)` is
> algebraically closed in `L(T)` for any family `T` of indeterminates.

The proof is elementary and avoids separating transcendence bases entirely.  An
element of `L(T)` algebraic over `k(T)` has a nonzero multiple by `c ∈ k[T]`
that is *integral* over `k[T]`; that multiple is then integral over `L[T]`,
which is a UFD hence integrally closed in `L(T)`, so it is a polynomial
`β ∈ L[T]` satisfying a MONIC equation over `k[T]`.  Specialising the
indeterminates at an arbitrary `k`-point makes `β(v) ∈ L` integral over `k`,
hence an element of `k`.  A polynomial over `L` whose values at every `k`-point
lie in `k` has all its coefficients in `k` — separate the offending coefficient
from `k · 1` by a `k`-linear functional and apply `MvPolynomial.funext`, which
is where `k` infinite is used.  So `β ∈ k[T]` and the original element is
`β / c ∈ k(T)`.

*The check that would refute the claim that `Infinite k` is needed*: a finite
`k` with `k` algebraically closed in some `L ⊋ k` — impossible for a different
reason (finite fields have no such `L` inside a separable closure), but the
VALUES argument really does fail over a finite field: `X^q - X` vanishes at
every `k`-point of `𝔸¹` without being zero.
-/

namespace RegularExtension

open MvPolynomial

variable {σ k L : Type*}

/-- Coefficientwise image of a function `f : L → k` sending `0` to `0`. -/
noncomputable def coeffMapFun [CommRing k] [CommRing L] (f : L → k) (β : MvPolynomial σ L) :
    MvPolynomial σ k :=
  ∑ m ∈ β.support, monomial m (f (coeff m β))

theorem coeff_coeffMapFun [CommRing k] [CommRing L] {f : L → k} (hf0 : f 0 = 0)
    (β : MvPolynomial σ L) (m : σ →₀ ℕ) :
    coeff m (coeffMapFun f β) = f (coeff m β) := by
  classical
  by_cases hm : m ∈ β.support
  · simp only [coeffMapFun, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp only [if_neg hb]
    · intro h; exact absurd hm h
  · simp only [coeffMapFun, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hm, hf0]
    · intro b hb
      have hbm : b ≠ m := fun h => hm (h ▸ hb)
      simp [hbm]

/-- Evaluation at a `k`-point is `k`-linear in the coefficients, so it commutes with
`coeffMapFun` applied to a `k`-linear functional. -/
theorem eval_coeffMapFun [CommRing k] [CommRing L] [Algebra k L]
    (φ : L →ₗ[k] k) (β : MvPolynomial σ L) (v : σ → k) :
    eval v (coeffMapFun φ β) = φ (eval (fun i => algebraMap k L (v i)) β) := by
  classical
  rw [coeffMapFun, map_sum, eval_eq, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial]
  have hprod : ∏ i ∈ m.support, algebraMap k L (v i) ^ m i
      = algebraMap k L (∏ i ∈ m.support, v i ^ m i) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
  rw [hprod, mul_comm (coeff m β), ← Algebra.smul_def, map_smul, smul_eq_mul, Finsupp.prod,
    mul_comm]

theorem mem_range_map_of_forall_coeff [Field k] [CommRing L] [Nontrivial L] [Algebra k L]
    (β : MvPolynomial σ L) (h : ∀ m, coeff m β ∈ Set.range (algebraMap k L)) :
    β ∈ Set.range (MvPolynomial.map (algebraMap k L)) := by
  classical
  have hinj : Function.Injective (algebraMap k L) := (algebraMap k L).injective
  have hg0 : Function.invFun (algebraMap k L) 0 = 0 := by
    have := Function.leftInverse_invFun hinj 0
    simpa using this
  refine ⟨coeffMapFun (Function.invFun (algebraMap k L)) β, ?_⟩
  ext m
  rw [coeff_map, coeff_coeffMapFun hg0]
  exact Function.invFun_eq (h m)

/-- **A polynomial over `L` whose values at every `k`-point lie in `k` has coefficients
in `k`** (PROVEN; `k` infinite is load-bearing — over `𝔽_q` the polynomial `X^q - X`
vanishes identically on `k`-points).

Separate an offending coefficient from the line `k · 1` by a `k`-linear functional `φ`
with `φ 1 = 0`; then `coeffMapFun φ β` is a polynomial over `k` vanishing at every
`k`-point, hence zero by `MvPolynomial.funext`, contradicting `φ (coeff m β) ≠ 0`. -/
theorem mem_range_map_of_forall_eval_mem [Field k] [Field L] [Algebra k L] [Infinite k]
    (β : MvPolynomial σ L)
    (h : ∀ v : σ → k, eval (fun i => algebraMap k L (v i)) β ∈ Set.range (algebraMap k L)) :
    β ∈ Set.range (MvPolynomial.map (algebraMap k L)) := by
  classical
  refine mem_range_map_of_forall_coeff β fun m => ?_
  by_contra hmem
  set W : Submodule k L := LinearMap.range (Algebra.linearMap k L) with hWdef
  have hmemW : coeff m β ∉ W := by
    intro hc
    exact hmem (by simpa [hWdef, Algebra.linearMap_apply] using hc)
  obtain ⟨φ, hφ, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmemW inferInstance
  have hkill : ∀ x ∈ W, φ x = 0 := by
    intro x hx
    have hx' : φ x ∈ Submodule.map φ W := Submodule.mem_map_of_mem hx
    rw [hφW, Submodule.mem_bot] at hx'
    exact hx'
  have hzero : coeffMapFun φ β = 0 := by
    refine MvPolynomial.funext fun v => ?_
    rw [eval_coeffMapFun, map_zero]
    refine hkill _ ?_
    obtain ⟨c, hc⟩ := h v
    exact ⟨c, by simpa [Algebra.linearMap_apply] using hc⟩
  have hc := coeff_coeffMapFun (f := (φ : L → k)) (by simp) β m
  rw [hzero] at hc
  exact hφ (by simpa using hc.symm)

/-- **`MvPolynomial σ k` is integrally closed in `MvPolynomial σ L`** when `k` is
algebraically closed in `L` and infinite (PROVEN).

Specialise the monic equation at an arbitrary `k`-point: the value `β(v) ∈ L` is then
integral over `k`, hence lies in `k`; now apply the values lemma above. -/
theorem mem_range_map_of_monic_eval₂_eq_zero [Field k] [Field L] [Algebra k L] [Infinite k]
    (hbot : ∀ y : L, IsIntegral k y → y ∈ Set.range (algebraMap k L))
    (β : MvPolynomial σ L) (p : Polynomial (MvPolynomial σ k)) (hp : p.Monic)
    (hz : Polynomial.eval₂ (MvPolynomial.map (algebraMap k L)) β p = 0) :
    β ∈ Set.range (MvPolynomial.map (algebraMap k L)) := by
  refine mem_range_map_of_forall_eval_mem β fun v => ?_
  refine hbot _ ⟨p.map (MvPolynomial.eval v), hp.map _, ?_⟩
  have hcomp : (MvPolynomial.eval (fun i => algebraMap k L (v i))).comp
      (MvPolynomial.map (algebraMap k L))
      = (algebraMap k L).comp (MvPolynomial.eval v) := by
    apply MvPolynomial.ringHom_ext <;> simp
  have h2 := congrArg (MvPolynomial.eval (fun i => algebraMap k L (v i))) hz
  rw [map_zero, Polynomial.hom_eval₂, hcomp] at h2
  rw [Polynomial.eval₂_map]
  exact h2

variable {Fk FL : Type*}

/-- **PURELY TRANSCENDENTAL BASE CHANGE PRESERVES "ALGEBRAICALLY CLOSED IN"** (PROVEN):
`k(σ)` is algebraically closed in `L(σ)` whenever `k` is algebraically closed in `L`
and `k` is infinite.  This is the one step of the transcendental half of regularity
that mathlib does not supply in any form (checked 2026-07-28: no statement in the pin
concludes `algebraicClosure (RatFunc k) _ = ⊥`). -/
theorem algebraicClosure_eq_bot_of_mvPolynomial
    [Field k] [Field L] [Algebra k L] [Infinite k]
    (hbot : ∀ y : L, IsIntegral k y → y ∈ Set.range (algebraMap k L))
    [Field Fk] [Field FL]
    [Algebra (MvPolynomial σ k) (MvPolynomial σ L)]
    (hPQ : ∀ q : MvPolynomial σ k, algebraMap (MvPolynomial σ k) (MvPolynomial σ L) q
      = MvPolynomial.map (algebraMap k L) q)
    [Algebra (MvPolynomial σ k) Fk] [IsFractionRing (MvPolynomial σ k) Fk]
    [Algebra (MvPolynomial σ L) FL] [IsFractionRing (MvPolynomial σ L) FL]
    [Algebra Fk FL] [Algebra (MvPolynomial σ k) FL]
    [IsScalarTower (MvPolynomial σ k) Fk FL]
    [IsScalarTower (MvPolynomial σ k) (MvPolynomial σ L) FL] :
    algebraicClosure Fk FL = ⊥ := by
  refine le_antisymm (fun α hα => ?_) bot_le
  rw [mem_algebraicClosure_iff'] at hα
  have halgP : IsAlgebraic (MvPolynomial σ k) α :=
    (IsFractionRing.isAlgebraic_iff (MvPolynomial σ k) Fk FL).mpr hα.isAlgebraic
  obtain ⟨c, hc0, hcint⟩ := halgP.exists_integral_multiple
  have h1 : IsIntegral (MvPolynomial σ L) (c • α) := hcint.tower_top
  have hinjQFL : Function.Injective (algebraMap (MvPolynomial σ L) FL) :=
    IsFractionRing.injective _ _
  obtain ⟨β, hβ⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : IsIntegral (MvPolynomial σ k) β := by
    refine (isIntegral_algebraMap_iff hinjQFL).mp ?_
    rw [hβ]; exact hcint
  obtain ⟨p, hp, hpz⟩ := h2
  have hpz' : Polynomial.eval₂ (MvPolynomial.map (algebraMap k L)) β p = 0 := by
    rw [← hpz]
    exact Polynomial.eval₂_congr (RingHom.ext fun q => (hPQ q).symm) rfl rfl
  obtain ⟨γ, hγ⟩ := mem_range_map_of_monic_eval₂_eq_zero hbot β p hp hpz'
  have h3 : algebraMap (MvPolynomial σ k) FL γ = c • α := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) (MvPolynomial σ L) FL, hPQ, hγ, hβ]
  rw [IntermediateField.mem_bot]
  have hcmem : c ∈ nonZeroDivisors (MvPolynomial σ k) := mem_nonZeroDivisors_of_ne_zero hc0
  have hcne : algebraMap (MvPolynomial σ k) FL c ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) Fk FL]
    have h1' : algebraMap (MvPolynomial σ k) Fk c ≠ 0 := by
      simpa using (IsFractionRing.to_map_eq_zero_iff (R := MvPolynomial σ k) (K := Fk)).not.mpr hc0
    intro h
    exact h1' ((algebraMap Fk FL).injective (by rw [h, map_zero]))
  refine ⟨IsLocalization.mk' Fk γ ⟨c, hcmem⟩, ?_⟩
  have hap := congrArg (algebraMap Fk FL) (IsLocalization.mk'_spec Fk γ ⟨c, hcmem⟩)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h3,
    Algebra.smul_def] at hap
  refine mul_left_cancel₀ hcne ?_
  rw [mul_comm]
  exact hap

/-! #### Plumbing: `L` is linearly disjoint from `k(σ)` over `k` inside `L(σ)` -/

/-- `MvPolynomial σ k ⊗[k] L ≃ MvPolynomial σ L`, as a `MvPolynomial σ k`-algebra
(mathlib's `MvPolynomial.algebraTensorAlgEquiv` is the same map read as an
`L`-algebra equivalence, which is the wrong base for the base-change cancellation
below). -/
noncomputable def mvTensorEquiv [Field k] [Field L] [Algebra k L]
    [Algebra (MvPolynomial σ k) (MvPolynomial σ L)]
    [IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ L)]
    (hPQ : ∀ q : MvPolynomial σ k, algebraMap (MvPolynomial σ k) (MvPolynomial σ L) q
      = MvPolynomial.map (algebraMap k L) q) :
    (MvPolynomial σ k) ⊗[k] L ≃ₐ[MvPolynomial σ k] MvPolynomial σ L := by
  refine AlgEquiv.ofBijective (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ k) _)
    (IsScalarTower.toAlgHom k L (MvPolynomial σ L)) (fun _ _ => Commute.all _ _)) ?_
  have key : ∀ z : (MvPolynomial σ k) ⊗[k] L,
      (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ k) (MvPolynomial σ L))
        (IsScalarTower.toAlgHom k L (MvPolynomial σ L)) (fun _ _ => Commute.all _ _)) z
      = (MvPolynomial.algebraTensorAlgEquiv k L)
          ((Algebra.TensorProduct.comm k (MvPolynomial σ k) L) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul q l =>
        simp [MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.ofId_apply, hPQ,
          Algebra.smul_def, mul_comm]
    | add u v hu hv => simp [map_add, hu, hv]
  rw [show ((Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ k) (MvPolynomial σ L))
        (IsScalarTower.toAlgHom k L (MvPolynomial σ L)) (fun _ _ => Commute.all _ _)) :
          (MvPolynomial σ k) ⊗[k] L → MvPolynomial σ L)
      = (MvPolynomial.algebraTensorAlgEquiv k L) ∘
          (Algebra.TensorProduct.comm k (MvPolynomial σ k) L) from funext key]
  exact (MvPolynomial.algebraTensorAlgEquiv k L).bijective.comp
    (Algebra.TensorProduct.comm k (MvPolynomial σ k) L).bijective

@[simp] theorem mvTensorEquiv_tmul [Field k] [Field L] [Algebra k L]
    [Algebra (MvPolynomial σ k) (MvPolynomial σ L)]
    [IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ L)]
    (hPQ : ∀ q : MvPolynomial σ k, algebraMap (MvPolynomial σ k) (MvPolynomial σ L) q
      = MvPolynomial.map (algebraMap k L) q)
    (q : MvPolynomial σ k) (l : L) :
    mvTensorEquiv hPQ (q ⊗ₜ l) = algebraMap (MvPolynomial σ k) (MvPolynomial σ L) q
      * algebraMap L (MvPolynomial σ L) l := by
  simp [mvTensorEquiv, Algebra.ofId_apply]

/-- **`L` and the purely transcendental extension `k(σ)` are linearly disjoint over `k`
inside `L(σ)`** (PROVEN): the multiplication map `k(σ) ⊗[k] L → L(σ)` is injective.

`k(σ) ⊗[k] L ≅ L[σ] ⊗[k[σ]] k(σ)` is the localization of `L[σ]` at the nonzero elements
of `k[σ]`, a submonoid of the nonzerodivisors of `L[σ]`; so it is a domain with fraction
field `L(σ)`, and the map to `L(σ)` is the (injective) map of a fraction ring. -/
theorem injective_lift_fractionRing_mvPolynomial [Field k] [Field L] [Algebra k L]
    [Field Fk] [Field FL]
    [Algebra (MvPolynomial σ k) (MvPolynomial σ L)]
    (hPQ : ∀ q : MvPolynomial σ k, algebraMap (MvPolynomial σ k) (MvPolynomial σ L) q
      = MvPolynomial.map (algebraMap k L) q)
    [Algebra (MvPolynomial σ k) Fk] [IsFractionRing (MvPolynomial σ k) Fk]
    [Algebra (MvPolynomial σ L) FL] [IsFractionRing (MvPolynomial σ L) FL]
    [Algebra k Fk] [IsScalarTower k (MvPolynomial σ k) Fk]
    [IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ L)]
    [Algebra k FL] [Algebra L FL] [IsScalarTower k L FL]
    [IsScalarTower L (MvPolynomial σ L) FL]
    [IsScalarTower k (MvPolynomial σ L) FL]
    [Algebra Fk FL] [Algebra (MvPolynomial σ k) FL]
    [IsScalarTower (MvPolynomial σ k) Fk FL] [IsScalarTower k Fk FL]
    [IsScalarTower (MvPolynomial σ k) (MvPolynomial σ L) FL] :
    Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId Fk FL)
      (IsScalarTower.toAlgHom k L FL) (fun _ _ => Commute.all _ _)) := by
  letI aTFL : Algebra ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL :=
    (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ L) FL)
      (IsScalarTower.toAlgHom (MvPolynomial σ k) Fk FL)
      (fun _ _ => Commute.all _ _)).toRingHom.toAlgebra
  haveI towT : IsScalarTower (MvPolynomial σ L) ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL :=
    IsScalarTower.of_algebraMap_eq (R := MvPolynomial σ L)
      (S := (MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) (A := FL) (fun c => by
        show _ = (Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ L) FL)
          (IsScalarTower.toAlgHom (MvPolynomial σ k) Fk FL) (fun _ _ => Commute.all _ _)) _
        simp [Algebra.TensorProduct.algebraMap_apply])
  have hle : Algebra.algebraMapSubmonoid (MvPolynomial σ L) (nonZeroDivisors (MvPolynomial σ k))
      ≤ nonZeroDivisors (MvPolynomial σ L) := by
    rintro _ ⟨c, hc, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [hPQ]
    exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hc)
      (MvPolynomial.map_injective _ (algebraMap k L).injective (by simpa using h))
  haveI : IsDomain ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) hle
  haveI : IsFractionRing ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid (MvPolynomial σ L) (nonZeroDivisors (MvPolynomial σ k))) _ _
  have key : ∀ z : Fk ⊗[k] L,
      Algebra.TensorProduct.lift (Algebra.ofId Fk FL) (IsScalarTower.toAlgHom k L FL)
        (fun _ _ => Commute.all _ _) z
      = algebraMap ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL
          ((Algebra.TensorProduct.comm (MvPolynomial σ k) Fk (MvPolynomial σ L))
            ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := Fk) (A₁ := Fk))
              (mvTensorEquiv hPQ))
              ((Algebra.TensorProduct.cancelBaseChange k (MvPolynomial σ k) Fk Fk L).symm z))) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul f l =>
        rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
        show _ = algebraMap ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL
          ((Algebra.TensorProduct.comm (MvPolynomial σ k) Fk (MvPolynomial σ L)) _)
        simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
          AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
          Algebra.TensorProduct.comm_tmul, RingHom.algebraMap_toAlgebra,
          Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, IsScalarTower.coe_toAlgHom',
          mvTensorEquiv_tmul, map_one, one_mul]
        show _ = Algebra.TensorProduct.lift (Algebra.ofId (MvPolynomial σ L) FL)
          (IsScalarTower.toAlgHom (MvPolynomial σ k) Fk FL) (fun _ _ => Commute.all _ _)
          ((algebraMap L (MvPolynomial σ L)) l ⊗ₜ[MvPolynomial σ k] f)
        rw [Algebra.TensorProduct.lift_tmul]
        simp only [Algebra.ofId_apply, IsScalarTower.coe_toAlgHom',
          MvPolynomial.algebraMap_eq]
        rw [mul_comm, ← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply L (MvPolynomial σ L) FL]
    | add u v hu hv => simp [map_add, hu, hv]
  intro a b hab
  have hchain : Function.Injective (fun z : Fk ⊗[k] L =>
      (Algebra.TensorProduct.comm (MvPolynomial σ k) Fk (MvPolynomial σ L))
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := Fk) (A₁ := Fk)) (mvTensorEquiv hPQ))
          ((Algebra.TensorProduct.cancelBaseChange k (MvPolynomial σ k) Fk Fk L).symm z))) :=
    fun u v huv =>
      (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial σ k) Fk Fk L).symm.injective
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := Fk) (A₁ := Fk))
          (mvTensorEquiv hPQ)).injective
          ((Algebra.TensorProduct.comm (MvPolynomial σ k) Fk (MvPolynomial σ L)).injective huv))
  refine hchain ?_
  refine IsFractionRing.injective ((MvPolynomial σ L) ⊗[MvPolynomial σ k] Fk) FL ?_
  rw [← key, ← key]
  exact hab

end RegularExtension

/-- **A field extension in which the base field is algebraically closed is regular —
the general case, in characteristic zero** (PROVEN 2026-07-29).

`[CharZero k]` is load-bearing here and cannot be weakened to `[PerfectField k]`: the
proof applies the algebraic half over the rational function field `Fk = k(ι)`, which is
imperfect in characteristic `p`, and the specialisation argument behind
`RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` needs `Infinite k`.

`k` has characteristic zero and is algebraically closed in `L`; `K/k` is an ARBITRARY
field extension, presented by a transcendence basis `x : ι → K`.  Then `L ⊗[k] K` is a
domain.

The argument, with `P := k[ι]`, `Q := L[ι]`, `Fk := k(ι)`, `FL := L(ι)`:

* `K` is algebraic over `Fk` (`IsTranscendenceBasis`), and `Fk` is algebraically closed
  in `FL` (`RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial`, the one new piece
  of mathematics), so `FL ⊗[Fk] K` is a domain by the ALGEBRAIC case
  `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot`;
* `Fk ⊗[k] L → FL` is injective
  (`RegularExtension.injective_lift_fractionRing_mvPolynomial`: `Fk ⊗[k] L` is the
  localization of `Q` at the nonzero elements of `P`), so `(Fk ⊗[k] L) ⊗[Fk] K` is a
  domain by `isDomain_tensorProduct_of_injective`;
* and `(Fk ⊗[k] L) ⊗[Fk] K ≅ K ⊗[k] L ≅ L ⊗[k] K` by base-change cancellation.

No transcendence basis of `K` needs to be finite, and no separating transcendence basis
is needed: the specialisation argument behind the crux replaces both. -/
theorem isDomain_tensorProduct_of_isTranscendenceBasis
    {k L K : Type*} [Field k] [CharZero k] [Field L] [Algebra k L] [Field K] [Algebra k K]
    (hbot : algebraicClosure k L = ⊥)
    {ι : Type*} {x : ι → K} (hx : IsTranscendenceBasis k x) :
    IsDomain (L ⊗[k] K) := by
  haveI : Infinite k := inferInstance
  letI aPkPL : Algebra (MvPolynomial ι k) (MvPolynomial ι L) :=
    MvPolynomial.algebraMvPolynomial
  have hPQ : ∀ q : MvPolynomial ι k,
      algebraMap (MvPolynomial ι k) (MvPolynomial ι L) q = MvPolynomial.map (algebraMap k L) q :=
    fun q => rfl
  haveI tow1 : IsScalarTower k (MvPolynomial ι k) (MvPolynomial ι L) :=
    IsScalarTower.of_algebraMap_eq (fun c => by simp)
  have hinjPkFL : Function.Injective
      (algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι L))) := by
    intro a b hab
    apply MvPolynomial.map_injective _ (algebraMap k L).injective
    apply IsFractionRing.injective (MvPolynomial ι L) (FractionRing (MvPolynomial ι L))
    rw [← hPQ, ← hPQ, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact hab
  letI aFkFL : Algebra (FractionRing (MvPolynomial ι k)) (FractionRing (MvPolynomial ι L)) :=
    (IsFractionRing.lift hinjPkFL).toAlgebra
  haveI tow3 : IsScalarTower (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
      (FractionRing (MvPolynomial ι L)) :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsFractionRing.lift_algebraMap hinjPkFL c).symm)
  haveI towkFkFL : IsScalarTower k (FractionRing (MvPolynomial ι k))
      (FractionRing (MvPolynomial ι L)) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι L)),
      IsScalarTower.algebraMap_apply (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
        (FractionRing (MvPolynomial ι L)),
      ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))]
  have hcrux : algebraicClosure (FractionRing (MvPolynomial ι k))
      (FractionRing (MvPolynomial ι L)) = ⊥ :=
    RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial
      (fun y hy => by
        have := hbot ▸ (mem_algebraicClosure_iff' (F := k) (E := L) (x := y)).mpr hy
        simpa [IntermediateField.mem_bot] using this) hPQ
  letI aPkK : Algebra (MvPolynomial ι k) K :=
    (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] K).toRingHom.toAlgebra
  have hxinj : Function.Injective (algebraMap (MvPolynomial ι k) K) :=
    algebraicIndependent_iff_injective_aeval.mp hx.1
  haveI towkPkK : IsScalarTower k (MvPolynomial ι k) K :=
    IsScalarTower.of_algebraMap_eq (fun c => by simp [RingHom.algebraMap_toAlgebra])
  letI aFkK : Algebra (FractionRing (MvPolynomial ι k)) K :=
    (IsFractionRing.lift hxinj).toAlgebra
  haveI towPkFkK : IsScalarTower (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) K :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsFractionRing.lift_algebraMap hxinj c).symm)
  haveI towkFkK : IsScalarTower k (FractionRing (MvPolynomial ι k)) K := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) K,
      IsScalarTower.algebraMap_apply (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) K,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))]
  haveI algPkK : Algebra.IsAlgebraic (MvPolynomial ι k) K := by
    haveI := hx.isAlgebraic
    refine Algebra.IsAlgebraic.of_ringHom_of_comp_eq (R := MvPolynomial ι k) (A := K)
      (S := ↥(Algebra.adjoin k (Set.range x))) (B := K)
      hx.1.aevalEquiv.toAlgHom.toRingHom (RingHom.id K)
      hx.1.aevalEquiv.surjective Function.injective_id (RingHom.ext fun p => ?_)
    simp [RingHom.algebraMap_toAlgebra, hx.1.algebraMap_aevalEquiv p]
  haveI algFkK : Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K :=
    Algebra.IsAlgebraic.extendScalars (R := MvPolynomial ι k)
      (S := FractionRing (MvPolynomial ι k)) (A := K)
      (IsFractionRing.injective (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)))
  haveI : CharZero (FractionRing (MvPolynomial ι k)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (FractionRing (MvPolynomial ι k))).injective
  haveI hD : IsDomain ((FractionRing (MvPolynomial ι L)) ⊗[FractionRing (MvPolynomial ι k)] K) :=
    isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot
      (FractionRing (MvPolynomial ι k)) (FractionRing (MvPolynomial ι L)) hcrux K
  have hmu := RegularExtension.injective_lift_fractionRing_mvPolynomial (k := k) (L := L) (σ := ι)
      (Fk := FractionRing (MvPolynomial ι k)) (FL := FractionRing (MvPolynomial ι L)) hPQ
  haveI : IsDomain (((FractionRing (MvPolynomial ι k)) ⊗[k] L)
      ⊗[FractionRing (MvPolynomial ι k)] K) :=
    isDomain_tensorProduct_of_injective (FractionRing (MvPolynomial ι k))
      ((FractionRing (MvPolynomial ι k)) ⊗[k] L)
      (FractionRing (MvPolynomial ι L)) K _ hmu
  haveI d1 : IsDomain (K ⊗[FractionRing (MvPolynomial ι k)]
      ((FractionRing (MvPolynomial ι k)) ⊗[k] L)) :=
    (Algebra.TensorProduct.comm (FractionRing (MvPolynomial ι k))
      ((FractionRing (MvPolynomial ι k)) ⊗[k] L) K).symm.toMulEquiv.isDomain
  haveI d2 : IsDomain (K ⊗[k] L) :=
    (Algebra.TensorProduct.cancelBaseChange k (FractionRing (MvPolynomial ι k))
      (FractionRing (MvPolynomial ι k)) K L).symm.toMulEquiv.isDomain
  exact (Algebra.TensorProduct.comm k L K).toMulEquiv.isDomain


/-- **The transcendental half of regularity, for a finitely generated subextension**
(**PROVEN 2026-07-29**; opened as a sorry leaf 2026-07-27).

`k` is algebraically closed in `L`, the characteristic is zero, `S` is a finite subset
of a field extension `K/k`, and the subfield `k(S)` it generates is not algebraic over
`k`.  Then `L ⊗[k] k(S)` is a domain.

## How it was closed, and how the route differs from the one first documented

The original plan (Bourbaki *Algebra* V §17, EGA IV 4.6.1, Stacks `04KM`) was: choose a
finite SEPARATING transcendence basis `T ⊆ S`, note `L ⊗[k] k(T) ⊆ L(T)`, prove
`k(T)` algebraically closed in `L(T)`, and finish with the algebraic case over `k(T)`.
The middle bullet — regularity is stable under purely transcendental base change — was
correctly identified there as "the one step that genuinely needs new mathematics", and
that is what `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` now supplies.

Two of the surrounding requirements turned out to be UNNECESSARY, and dropping them is
what made the leaf tractable:

* **No separating transcendence basis, and no separability argument at all.** The proof
  of the crux is a specialisation argument: an element of `L(T)` algebraic over `k(T)`
  has a `k[T]`-multiple integral over `k[T]`, which lands in `L[T]` because `L[T]` is a
  UFD, hence integrally closed in `L(T)`; evaluating its monic equation at a `k`-point
  makes the value integral over `k`, hence an element of `k`; and a polynomial over `L`
  all of whose values at `k`-points lie in `k` has all coefficients in `k`.  Only `k`
  INFINITE is used, which `CharZero k` supplies.
* **No finiteness of `T`.** Everything is phrased over `MvPolynomial ι k` for an
  arbitrary index type, so the general statement for an arbitrary `K/k` is proved
  directly (`isDomain_tensorProduct_of_isTranscendenceBasis`) and this finitely
  generated case is an instance of it.  In particular the `Finset` reduction
  `isDomain_tensorProduct_of_forall_adjoin_finset` is no longer needed for this proof,
  though it is kept: it is a correct and independently useful statement.

`_hna` is retained for interface stability — the proof does not use it, and indeed the
conclusion holds for every `S`, algebraic or not.

**Faithfulness note.**  `PerfectField k` is load-bearing throughout this section
(the hypothesis read `CharZero k` until 2026-07-28, and this note said
characteristic zero was what was load-bearing; it is not — perfection is, and
that is strictly weaker.  `PerfectField.ofCharZero` is an instance, so no `ℚ`
call site changed, while the char-`p` consumers in `ModularCurve/X0.lean` over
`k = ZMod p` need exactly the weaker form, `ZMod p` being perfect by
`PerfectField.ofFinite`.)
Over an IMPERFECT base the statement is FALSE with only "algebraically closed in":
for `k = 𝔽_p(u,v)` and `L` the function field of `y^p = u x^p + v`, the field `k`
*is* algebraically closed in `L`, yet `L ⊗[k] k^{1/p}` has a nonzero nilpotent
(the curve becomes `w^p = v` after adjoining `u^{1/p}`), so `L/k` is not
separable and `L ⊗[k] K` is not a domain for `K = k^{1/p}`.  Perfection is used
here to supply the primitive element in
`linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot`, through
mathlib's instance `Algebra.IsSeparable K L` for `[PerfectField K]` with
`L/K` algebraic (`Mathlib/FieldTheory/Perfect.lean`).

**MERGE NOTE, release 18.**  Characteristic zero enters the *transcendental*
route TWICE and neither use survives the `PerfectField` weakening:

* through `Infinite k` in the specialisation argument — over `𝔽_q` the
  polynomial `X^q - X` vanishes at every `k`-point without being zero, so
  `mem_range_map_of_forall_eval_mem` (which carries `[Infinite k]`) fails; and
* through the algebraic half applied over `Fk = k(ι)` inside
  `isDomain_tensorProduct_of_isTranscendenceBasis`, which needs
  `PerfectField Fk`.  A rational function field in characteristic `p` is
  **not** perfect, so that step is unavailable even for infinite `k`.

So this leaf is now **PROVEN in characteristic zero** and **OPEN in positive
characteristic**.  The statement itself is believed true in both (over a
perfect base, "algebraically closed in" is exactly regularity); only the route
is char-0.  The char-`p` case is what a prover should attack — a separability
/ linear-disjointness argument over `k(ι)^{1/p^∞}`, not the specialisation
argument. -/
theorem isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] (S : Finset K)
    (_hna : ¬ Algebra.IsAlgebraic k (IntermediateField.adjoin k (S : Set K))) :
    IsDomain (L ⊗[k] (IntermediateField.adjoin k (S : Set K))) := by
  by_cases hchar : CharZero k
  · haveI := hchar
    obtain ⟨t, ht⟩ :=
      exists_isTranscendenceBasis k (A := ↥(IntermediateField.adjoin k (S : Set K)))
    exact isDomain_tensorProduct_of_isTranscendenceBasis hbot ht
  · -- Positive characteristic: OPEN.  See the merge note above.
    sorry

/-- **A field extension in which the base field is algebraically closed is
regular** (PROVEN over
`isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`).

`L ⊗[k] K` is a domain for every field extension `K/k`, when `k` has
characteristic zero and is algebraically closed in `L`.  Reduce to the finitely
generated subextensions `k(S)` of `K`, then split each of those into the
algebraic case (PROVEN) and the transcendental case (the leaf). -/
theorem isDomain_tensorProduct_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] :
    IsDomain (L ⊗[k] K) := by
  classical
  refine isDomain_tensorProduct_of_forall_adjoin_finset k L K (fun S => ?_)
  by_cases halg : Algebra.IsAlgebraic k (IntermediateField.adjoin k (S : Set K))
  · haveI := halg
    exact isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot k L hbot _
  · exact isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot
      k L hbot K S halg

/-- **The fraction field of a normal domain in which the base field is
algebraically closed is a regular extension** (PROVEN over
`isDomain_tensorProduct_of_algebraicClosure_eq_bot`).

`k` being algebraically closed *in `B`* is the same as `k` being algebraically
closed *in `Frac B`* when `B` is integrally closed
(`algebraicClosure_fractionRing_eq_bot`), and a field extension `L/k` with `k`
algebraically closed in `L` is **regular** in characteristic zero, i.e.
`L ⊗[k] K` is a domain for every field extension `K/k`.

Together with `isDomain_tensorProduct_of_injective` above this is exactly
"geometrically integral", which is what an affine geometric-connectedness
criterion needs. -/
theorem isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot
    (k B : Type*) [Field k] [PerfectField k] [CommRing B] [IsDomain B] [Algebra k B]
    [IsIntegrallyClosed B]
    (h : ∀ x : B, IsAlgebraic k x → x ∈ (⊥ : Subalgebra k B))
    (K : Type*) [Field K] [Algebra k K] :
    IsDomain (FractionRing B ⊗[k] K) :=
  isDomain_tensorProduct_of_algebraicClosure_eq_bot k (FractionRing B)
    (algebraicClosure_fractionRing_eq_bot k B h) K

/-- **A normal domain in which the base field is algebraically closed is
geometrically integral** (PROVEN over
`isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot`).

`B ⊗[k] K` embeds into `Frac B ⊗[k] K` because `K` is flat over the field `k`,
and the latter is a domain by the leaf.  This is the form the affine
geometric-connectedness criterion
`AlgebraicGeometry.geometricallyConnected_specMap_algebraMap_of_forall_isDomain`
consumes. -/
theorem isDomain_tensorProduct_of_isAlgebraic_mem_bot
    (k B : Type*) [Field k] [PerfectField k] [CommRing B] [IsDomain B] [Algebra k B]
    [IsIntegrallyClosed B]
    (h : ∀ x : B, IsAlgebraic k x → x ∈ (⊥ : Subalgebra k B))
    (K : Type*) [Field K] [Algebra k K] :
    IsDomain (B ⊗[k] K) := by
  haveI : IsDomain (FractionRing B ⊗[k] K) :=
    isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot k B h K
  exact isDomain_tensorProduct_of_injective k B (FractionRing B) K
    (IsScalarTower.toAlgHom k B (FractionRing B)) (IsFractionRing.injective B (FractionRing B))

/-! ### A coefficient field of a valuation-like ring is algebraically closed in the
fraction field

Added 2026-07-30 for `Fermat/FLT/ModularCurve/X0.lean`'s q-expansion route to
`isAlgebraic_coarseRing_of_gamma0GITPresentation`.  The point of the abstraction is
that the modular input there (an embedding of the coarse ring into `k((q))`) is
separated from the field theory, which is entirely general and is proven here. -/

/-- **A COEFFICIENT FIELD IS ALGEBRAICALLY CLOSED IN THE FRACTION FIELD** (PROVEN
2026-07-30).

Let `R` be an integrally closed domain with fraction field `L`, and `k ⊆ R` a subfield
such that *every* `z : R` can be translated by a constant into the non-units — the
hypothesis `hres`.  Then every `x : L` algebraic over `k` already lies in `k`.

`hres` is exactly "the residue field of `R` is `k`" for a local `R`, stated in the one
form the proof consumes so that no `IsLocalRing` instance is needed: for `R = k⟦X⟧` it
is `c := constantCoeff z` together with `PowerSeries.isUnit_iff_constantCoeff`, and that
is the only instance used in this development
(`mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries` below).

The argument in three steps, none of which needs a valuation:

* `x` is integral over `k`, hence over `R`, hence lies in `R` — this is the ONLY place
  `IsIntegrallyClosed R` is used, and it is what replaces the usual "`v x = 0`"
  computation.  Write `x = algebraMap R L z`.
* Take `c` from `hres z`.  If `x ≠ algebraMap k L c` then `(x - c)⁻¹` is again algebraic
  over `k` (a field is closed under inverses of nonzero algebraic elements), so by the
  same step it too comes from `R`, say from `w`.
* `(z - algebraMap k R c) * w = 1` in `R` by injectivity of `R → L`, so
  `z - algebraMap k R c` is a UNIT — contradicting `hres`.  Hence `x = c`.

**Faithfulness.** `hres` cannot be dropped and cannot be weakened to "some `z` has such
a `c`": with `k = ℚ` and `R = ℚ(i)⟦X⟧` (a DVR, integrally closed, containing `ℚ`), the
conclusion is FALSE — `i ∈ R ⊆ L` is algebraic over `ℚ` and is not in the image of `ℚ`
— and what fails is precisely `hres` at `z = i`, since `i - c` is a unit for every
rational `c`.  So `hres` is carrying the whole arithmetic content, as it must. -/
theorem mem_range_algebraMap_of_isAlgebraic_of_forall_exists_not_isUnit
    {k R L : Type*} [Field k] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Algebra k R] [Algebra k L]
    [IsScalarTower k R L]
    (hres : ∀ z : R, ∃ c : k, ¬ IsUnit (z - algebraMap k R c))
    {x : L} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k L) := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.isIntegral.tower_top (A := R))
  obtain ⟨c, hc⟩ := hres z
  refine ⟨c, ?_⟩
  by_contra hne
  have hxc : x - algebraMap k L c ≠ 0 := fun h => hne (by linear_combination -h)
  have halg : IsAlgebraic k (x - algebraMap k L c) := hx.sub (isAlgebraic_algebraMap c)
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp (halg.inv.isIntegral.tower_top (A := R))
  refine hc ⟨⟨z - algebraMap k R c, w, ?_, ?_⟩, rfl⟩ <;>
    · have hinj : Function.Injective (algebraMap R L) := IsFractionRing.injective R L
      apply hinj
      rw [map_mul, map_sub, hz, map_one, ← IsScalarTower.algebraMap_apply, hw]
      first
        | rw [mul_inv_cancel₀ hxc]
        | rw [inv_mul_cancel₀ hxc]

/-- **`k` IS ALGEBRAICALLY CLOSED IN `k((q))`** (PROVEN 2026-07-30), the formal-Laurent
field being presented as `FractionRing k⟦X⟧`.

This is the field-theoretic half of the q-expansion principle: a modular function whose
q-expansion is a CONSTANT Laurent series is a constant, and more precisely an element of
`k((q))` that is algebraic over `k` is already in `k`.

**Why `FractionRing (PowerSeries k)` and not `LaurentSeries k`**, which is the same field
and the more readable name: `LaurentSeries k = HahnSeries ℤ k` carries an
`SMul k (HahnSeries ℤ k)` (`HahnSeries.instSMul`, coefficientwise) that is NOT the one
underlying the `Algebra k (HahnSeries ℤ k)` instance synthesis actually picks
(`HahnSeries.powerSeriesAlgebra ℤ k`, whose `smul` is `algebraMap c * ·`).  They are
propositionally equal, but `IsScalarTower k k⟦X⟧ (LaurentSeries k)` then does **not**
synthesize, and discharging it by hand runs `whnf` past 200 000 heartbeats — measured
2026-07-30, so raising `maxHeartbeats` is not the fix.  `FractionRing k⟦X⟧` has none of
this: `Algebra k (FractionRing k⟦X⟧)`, the scalar tower, `IsFractionRing` and `Field` all
synthesize immediately.

A consumer that prefers `LaurentSeries k` can transport along
`IsLocalization.algEquiv` for the two fraction fields of `k⟦X⟧` (mathlib's
`instIsFractionRing : IsFractionRing k⟦X⟧ k⸨X⸩`); the resulting equivalence is
`k⟦X⟧`-linear, hence automatically compatible with `algebraMap k ·` on both sides, which
factors through `k⟦X⟧`. -/
theorem mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries
    {k : Type*} [Field k] {x : FractionRing (PowerSeries k)} (hx : IsAlgebraic k x) :
    x ∈ Set.range (algebraMap k (FractionRing (PowerSeries k))) := by
  refine mem_range_algebraMap_of_isAlgebraic_of_forall_exists_not_isUnit
    (R := PowerSeries k) (fun z => ?_) hx
  refine ⟨PowerSeries.constantCoeff z, ?_⟩
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

end
