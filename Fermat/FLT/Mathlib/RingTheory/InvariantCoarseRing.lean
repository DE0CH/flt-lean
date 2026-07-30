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
   proven directly from `Ring.KrullDimLE 1` plus lying over.

Regularity is then free: mathlib has `[IsDedekindDomain R] : IsRegularRing R`.

## `S` NEED NOT BE A DOMAIN (2026-07-30)

All three inputs were originally stated with `[IsDomain S]`.  They are not, and the
hypothesis was blocking the `𝔽_p` half of the modular-curve consumer: over `𝔽_p` the
rigidified moduli scheme is a finite PRODUCT of smooth affine curves (Frobenius need not
permute the Weil-pairing components transitively), so `IsDomain A` is FALSE there while
everything actually used about `A` — reduced, normal, of Krull dimension one, of finite
type — still holds.  See the CUT-OBSTRUCTION AUDIT and its RESOLUTION on
`isRegularRing_coarseRing_of_gamma0AtlasOver_zmod` in `ModularCurve/X0.lean`.

Three things had to change, and none of them is a one-line substitution:

* `Ring.DimensionLEOne S` had to become `Ring.KrullDimLE 1 S`.  The former is
  UNSATISFIABLE for a product of curves (`⊥ × k[x]` is a nonzero non-maximal prime of
  `k[x] × k[x]`), so a bare deletion of `[IsDomain S]` would have left a vacuous hypothesis.
* `[IsDomain R]` had to be ADDED where it used to come free from `[IsDomain S]` and
  injectivity.  It is genuinely load-bearing — see the counterexample on
  `dimensionLEOne_of_isInvariant` — and the modular consumer has it, as the separate leaf
  `isDomain_of_gamma0AtlasOver_zmod`.
* the normality argument had to move from `Frac S` to the TOTAL quotient ring, which needed
  a domain-free `G`-action on it (`IsFractionRing.totalMulSemiringAction` below; mathlib's
  is stated for fields only, gratuitously) and a proof that nonzero elements of `R` are
  non-zero-divisors in `S` (`nonZeroDivisors_le_comap_of_isInvariant`, from `[IsReduced S]`
  and transitivity of `G` on primes over a fixed prime).

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
  was **PROVEN in characteristic zero** (2026-07-29) via
  `isDomain_tensorProduct_of_isTranscendenceBasis`, whose only new mathematical
  input is `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` —
  *purely transcendental base change preserves "algebraically closed in"* — and
  is now **PROVEN in positive characteristic too** (2026-07-30), so this module
  has **no `sorry` left**.  The char-0 route does not survive the `PerfectField`
  weakening (it applies the algebraic half over the imperfect `Fk = k(ι)`, and the
  specialisation argument behind its crux additionally needs `k` infinite), so the
  char-`p` branch replaces both steps:

  - `RegularExtension.mem_range_map_of_monic_eval₂_eq_zero'` proves the crux by a
    LEADING-COEFFICIENT argument against an arbitrary `MonomialOrder`, with no
    hypothesis on the characteristic or the cardinality of `k`; and
  - `isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot` is the
    algebraic half with `[Algebra.IsSeparable k K]` in place of `[PerfectField k]`,
    which is what lets it be applied over `k(ι)` — the separability coming from a
    SEPARATING transcendence basis, i.e. from mathlib's MacLane theorem
    `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`.

  See the leaf's own docstring for the audit.

* `isDomain_tensorProduct_of_injective` — the transfer from the fraction field
  down to the ring, which is just flatness of a field over a field (PROVEN).

## Contents

* `IsFractionRing.totalMulSemiringAction`, `IsFractionRing.totalSMulDistribClass` —
  mathlib's `IsFractionRing.mulSemiringAction`/`smulDistribClass` without their
  unnecessary `Field` hypotheses (PROVEN)
* `Algebra.IsInvariant.finiteType_of_isInvariant` — Noether (PROVEN)
* `Algebra.IsInvariant.nonZeroDivisors_le_comap_of_isInvariant` — a nonzero invariant is a
  non-zero-divisor upstairs, for `S` reduced (PROVEN)
* `Algebra.IsInvariant.isIntegrallyClosed_of_isInvariant` — normality (PROVEN)
* `Algebra.IsInvariant.dimensionLEOne_of_isInvariant` — dimension ≤ 1 (PROVEN)
* `Algebra.IsInvariant.ringKrullDim_eq_one_of_isInvariant` — dimension = 1 (PROVEN)
* `Algebra.IsInvariant.isDedekindDomain_of_isInvariant` — assembly, `S` a Dedekind
  domain (PROVEN)
* `Algebra.IsInvariant.isRegularRing_of_isInvariant` — the packaged conclusion
  the `ℚ` modular-curve consumer asks for (PROVEN)
* `Algebra.IsInvariant.isDedekindDomain_of_isInvariant_of_isReduced`,
  `Algebra.IsInvariant.isRegularRing_of_isInvariant_of_isReduced` — the same two with `S`
  merely reduced, normal and of Krull dimension one, which is what the `𝔽_p` consumer has
  (PROVEN)
* `algebraicClosure_fractionRing_eq_bot` — `k` is algebraically closed in
  `Frac B` as soon as it is algebraically closed in the normal domain `B` (PROVEN)
* `minpoly_map_eq_of_algebraicClosure_eq_bot` — minimal polynomials over `k`
  stay irreducible over `L` (PROVEN); the heart of the regularity argument
* `linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot`,
  `linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot` — linear
  disjointness of an algebraic intermediate field from `L` (PROVEN)
* `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot` — the
  algebraic half of regularity (PROVEN)
* `linearDisjoint_of_finiteDimensional_of_isSeparable_of_algebraicClosure_eq_bot`,
  `linearDisjoint_of_isSeparable_of_algebraicClosure_eq_bot`,
  `isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot` — the same three
  with `[Algebra.IsSeparable k _]` in place of `[PerfectField k]`, which is what makes
  them usable over an imperfect base such as `k(ι)` in characteristic `p` (PROVEN)
* `isDomain_tensorProduct_of_forall_adjoin_finset` — reduction to finitely
  generated subextensions of `K` (PROVEN)
* `isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`
  — the transcendental half, for a finitely generated subextension (PROVEN in every
  characteristic: char 0 since 2026-07-29, char `p` since 2026-07-30)
* `isDomain_tensorProduct_of_isTranscendenceBasis` — the transcendental half in
  full generality, `[CharZero k]` (PROVEN)
* `isDomain_tensorProduct_of_algebraicIndependent_of_isSeparable` — the transcendental
  half over a SEPARATING transcendence basis, in any characteristic (PROVEN)
* `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial` — purely
  transcendental base change preserves "algebraically closed in" (PROVEN, `k` infinite)
* `RegularExtension.mem_range_map_of_monic_eval₂_eq_zero'`,
  `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial'` — the same crux for a base
  of ANY cardinality, by a monomial-order leading-coefficient argument in place of the
  specialisation argument (PROVEN)
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
-- `IntermediateField.isSeparable_adjoin_iff_isSeparable`, used to descend separability to
-- the finite subextension in `linearDisjoint_of_isAlgebraic_of_isSeparable`.
public import Mathlib.FieldTheory.SeparableClosure
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
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.SeparablyGenerated

@[expose] public section

open scoped TensorProduct MonomialOrder

/-! ### The `G`-action on a TOTAL quotient ring

Mathlib's `IsFractionRing.mulSemiringAction` and `IsFractionRing.smulDistribClass` are
stated with `[Field K] [Field L]`, i.e. only for a DOMAIN.  Neither proof uses the
hypothesis: both go through `IsFractionRing.ringEquivOfRingEquivHom`, which is stated for
an arbitrary `CommRing` with `[IsFractionRing A L]` and therefore applies verbatim to the
total quotient ring `Localization (nonZeroDivisors A)` of a ring with zero divisors.

These two restatements are what let `isIntegrallyClosed_of_isInvariant` below drop
`[IsDomain S]`: its argument runs inside `Frac S`, and for a non-domain `S` that has to be
the total quotient ring. -/

namespace IsFractionRing

variable (G A L : Type*) [Group G] [CommRing A] [MulSemiringAction G A]
  [CommRing L] [Algebra A L] [IsFractionRing A L]

/-- **`IsFractionRing.mulSemiringAction` without the `Field` hypotheses** (PROVEN): a
`MulSemiringAction G A` extends to the TOTAL quotient ring of `A`.  Same definition as
mathlib's, whose `[Field K] [Field L]` binders are not used by
`ringEquivOfRingEquivHom`. -/
@[implicit_reducible]
noncomputable def totalMulSemiringAction : MulSemiringAction G L :=
  MulSemiringAction.compHom L
    ((IsFractionRing.ringEquivOfRingEquivHom A L).comp (MulSemiringAction.toRingEquiv G A))

/-- The extended action is compatible with `A ⊆ L` (PROVEN). -/
theorem totalMulSemiringAction_smul_algebraMap (g : G) (a : A) :
    letI := totalMulSemiringAction G A L
    g • (algebraMap A L a) = algebraMap A L (g • a) := by
  letI := totalMulSemiringAction G A L
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

/-- **`IsFractionRing.smulDistribClass` without the `Field` hypotheses** (PROVEN). -/
theorem totalSMulDistribClass :
    letI := totalMulSemiringAction G A L
    SMulDistribClass G A L := by
  letI := totalMulSemiringAction G A L
  refine ⟨fun g b x ↦ ?_⟩
  rw [Algebra.smul_def', Algebra.smul_def', smul_mul']
  congr 1
  exact totalMulSemiringAction_smul_algebraMap G A L g b

end IsFractionRing

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

open scoped Pointwise in
/-- **A nonzero invariant is a NON-ZERO-DIVISOR upstairs** (PROVEN 2026-07-30) — the
input that lets the normality argument below run over a non-domain `S`.

`Frac R → Frac S` exists only if every nonzero `r ∈ R` becomes a non-zero-divisor in `S`,
and for `S` with zero divisors that is not automatic from injectivity of `R → S`.  It IS
automatic here, and the reason is `Algebra.IsInvariant` — transitivity of `G` on the primes
over a given prime of `R`:

*if `r · s = 0` with `s ≠ 0`, pick (S reduced) a minimal prime `Q` of `S` with `s ∉ Q`;
then `r ∈ Q`, so `p := Q ∩ R ≠ ⊥`.  Lying over gives a prime `Q₀` of `S` over `⊥` and going
up a prime `Q' ⊇ Q₀` over `p`; `Algebra.IsInvariant.exists_smul_of_under_eq` supplies
`g ∈ G` with `g • Q' = Q`, and then `g • Q₀ ⊆ Q` is a prime over `⊥` strictly below `Q` —
contradicting minimality of `Q`.*

**`[IsReduced S]` is REQUIRED and the statement is FALSE without it.**  Witness:
`S = k[u,v]/(v², uv)`, `G = ZMod 2` acting by `v ↦ -v` (char `k ≠ 2`), `R = S^G = k[u]`.
Every other hypothesis holds — `R` is a domain, `R → S` is injective, `S = R ⊕ R·v` is
module-finite hence integral, and the `G`-fixed elements are exactly `k[u]` — yet
`u ≠ 0` in `R` and `u · v = 0` in `S` with `v ≠ 0`.

**`[IsDomain R]` is REQUIRED** for the obvious reason: `nonZeroDivisors R` is read as
"`≠ 0`" nowhere else, and with `R = S` and `G` trivial the statement is the tautology that
a non-zero-divisor is a non-zero-divisor, which is *not* what is proven here. -/
theorem nonZeroDivisors_le_comap_of_isInvariant (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [IsReduced S]
    (hinj : Function.Injective (algebraMap R S)) :
    nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hinj
  intro r hr
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff]
  suffices key : ∀ s : S, s * algebraMap R S r = 0 → s = 0 from
    ⟨fun x hx => key x (by rwa [mul_comm]), key⟩
  intro s hs
  by_contra hs0
  -- a minimal prime `Q` of `S` avoiding `s`
  obtain ⟨J, hJp, hsJ⟩ : ∃ J : Ideal S, J.IsPrime ∧ s ∉ J := by
    by_contra hcon
    push Not at hcon
    refine hs0 (IsNilpotent.eq_zero ?_)
    rw [← mem_nilradical, nilradical_eq_sInf]
    exact Ideal.mem_sInf.mpr fun J hJ => hcon J hJ
  haveI : J.IsPrime := hJp
  obtain ⟨Q, hQmin, hQJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := J) bot_le
  haveI hQp : Q.IsPrime := hQmin.1.1
  have hsQ : s ∉ Q := fun h => hsJ (hQJ h)
  -- `r` lands in `Q`, so `Q` lies over a NONZERO prime `p` of `R`
  have hrQ : algebraMap R S r ∈ Q := ((hQp.mem_or_mem (hs ▸ Q.zero_mem)).resolve_left hsQ)
  set p : Ideal R := Q.comap (algebraMap R S) with hp
  haveI hpp : p.IsPrime := Ideal.comap_isPrime _ _
  have hrp : r ∈ p := Ideal.mem_comap.mpr hrQ
  have hp0 : p ≠ ⊥ := fun h => hr0 (Ideal.mem_bot.mp (h ▸ hrp))
  -- lying over `⊥`, then going up to `p`
  obtain ⟨Q₀, -, hQ₀p, hQ₀c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) (⊥ : Ideal R) (⊥ : Ideal S)
      (by simp [← RingHom.ker_eq_comap_bot, hker])
  haveI := hQ₀p
  obtain ⟨Q', hQ₀Q', hQ'p, hQ'c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (R := R) (S := S) p Q₀
      (by rw [hQ₀c]; exact bot_le)
  haveI := hQ'p
  -- `G` is transitive on the primes over `p`, so a prime over `⊥` sits below `Q` as well
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q' Q
    (by rw [Ideal.under_def, Ideal.under_def, hQ'c])
  haveI : (g • Q₀).IsPrime := hQ₀p.smul g
  have hle : g • Q₀ ≤ Q := hg ▸ smul_mono_right g hQ₀Q'
  have hc0 : (g • Q₀).comap (algebraMap R S) = ⊥ := by
    rw [← Ideal.under_def, Ideal.under_smul, Ideal.under_def, hQ₀c]
  exact hp0 (le_bot_iff.mp (hc0 ▸ Ideal.comap_mono (hQmin.2 ⟨inferInstance, bot_le⟩ hle)))

/-- **Invariants of an integrally closed ring are integrally closed**
(PROVEN) — Matsumura §23, Bourbaki *Commutative Algebra* V §1.9.

**`[IsDomain S]` was dropped 2026-07-30** (it was there until then, and the CUT-OBSTRUCTION
AUDIT on `isRegularRing_coarseRing_of_gamma0AtlasOver_zmod` in `ModularCurve/X0.lean`
correctly identified it as the obstruction to the `𝔽_p` coarse-space leaf: over `𝔽_p` the
rigidified moduli ring is a finite PRODUCT of smooth curves, because Frobenius need not
permute the Weil-pairing components transitively).  `IsIntegrallyClosed S` is meaningful for
any `CommRing` — mathlib reads it as `IsIntegralClosure S S (FractionRing S)` with
`FractionRing S = Localization (nonZeroDivisors S)`, the TOTAL quotient ring — so only the
proof had to move, not the statement.

Write `K = Frac R` (a field: `R` is a domain) and `L = Frac S` (the total quotient ring).
Two things replace what `[IsDomain S]` used to supply:

* the `G`-action on `L`, which is `IsFractionRing.totalMulSemiringAction` above rather than
  mathlib's field-only `IsFractionRing.mulSemiringAction`;
* the map `K → L`, which is `IsLocalization.map` over `hnzd` rather than
  `FractionRing.liftAlgebra` (that one needs `L` to be a FIELD, and injectivity of
  `R → L` is genuinely not enough: a nonzero `r ∈ R` must become a UNIT in `L`, i.e. a
  non-zero-divisor in `S`).  `hnzd` is `nonZeroDivisors_le_comap_of_isInvariant` above
  whenever `S` is reduced.

The argument itself is unchanged: `x ∈ K` integral over `R` has image `z ∈ L` integral over
`S`, so `z = algebraMap S L s` because `S` is integrally closed; `z` is `G`-fixed, hence so
is `s`, hence `s` lies in the image of `R` by `Algebra.IsInvariant`; and that preimage maps
to `x` because `K → L` is injective.

One step DID have to change shape.  `G` fixing the image of `K` pointwise was proven by
writing `x = a/b` and pushing `g` through the division — which needs `L` to be a field.  It
is now the universal property, `IsLocalization.ringHom_ext`: two ring maps `K → L` agreeing
on `R` are equal, and `g ∘ (K → L)` agrees with `K → L` on `R` because `G` fixes `R`. -/
theorem isIntegrallyClosed_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [IsIntegrallyClosed S]
    (hinj : Function.Injective (algebraMap R S))
    (hnzd : nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S)) :
    IsIntegrallyClosed R := by
  letI := IsFractionRing.totalMulSemiringAction G S (FractionRing S)
  haveI := IsFractionRing.totalSMulDistribClass G S (FractionRing S)
  haveI hSL : Function.Injective (algebraMap S (FractionRing S)) :=
    IsLocalization.injective _ le_rfl
  haveI : Nontrivial S := hinj.nontrivial
  letI : Algebra (FractionRing R) (FractionRing S) :=
    (IsLocalization.map (FractionRing S) (algebraMap R S) hnzd).toAlgebra
  haveI htower : IsScalarTower R (FractionRing R) (FractionRing S) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap R (FractionRing S) x
        = IsLocalization.map (FractionRing S) (algebraMap R S) hnzd
            (algebraMap R (FractionRing R) x)
      rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply R S (FractionRing S)]
  have hKL : Function.Injective (algebraMap (FractionRing R) (FractionRing S)) :=
    (algebraMap (FractionRing R) (FractionRing S)).injective
  -- `G` fixes the image of `Frac R` pointwise
  have hmap : ∀ (g : G) (r : R), g • (algebraMap R (FractionRing S) r)
      = algebraMap R (FractionRing S) r := by
    intro g r
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    simp [← algebraMap.coe_smul', smul_algebraMap]
  have hfixK : ∀ (g : G) (x : FractionRing R),
      g • (algebraMap (FractionRing R) (FractionRing S) x)
        = algebraMap (FractionRing R) (FractionRing S) x := by
    intro g x
    have hext : (MulSemiringAction.toRingHom G (FractionRing S) g).comp
        (algebraMap (FractionRing R) (FractionRing S))
          = algebraMap (FractionRing R) (FractionRing S) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simpa [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]
        using hmap g r
    exact congrArg (fun (f : FractionRing R →+* FractionRing S) => f x) hext
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr ?_
  intro x hx
  set z : FractionRing S := algebraMap (FractionRing R) (FractionRing S) x with hz
  have hzR : IsIntegral R z := hx.map (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing S))
  have hzS : IsIntegral S z := hzR.tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzS
  have hsfix : ∀ g : G, g • s = s := by
    intro g
    apply hSL
    rw [← IsFractionRing.totalMulSemiringAction_smul_algebraMap G S (FractionRing S) g s, hs, hz,
      hfixK g x]
  obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := R) (B := S) (G := G) s hsfix
  refine ⟨y, ?_⟩
  apply hKL
  rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
    IsScalarTower.algebraMap_eq R S (FractionRing S)]
  simp only [RingHom.coe_comp, Function.comp_apply, hy, hs, hz]

/-! ### Krull dimension -/

/-- **A finite group quotient does not raise the dimension above one** (PROVEN).

**`[IsDomain S]` was dropped 2026-07-30**, together with the strengthening of
`[Ring.DimensionLEOne S]` to `[Ring.KrullDimLE 1 S]`, which is what the statement needs
once `S` may have zero divisors.  `[IsDomain R]` is taken instead; every former call site
had it, since it followed from `[IsDomain S]` and `hinj`.

**`Ring.DimensionLEOne S` is the WRONG hypothesis for a non-domain `S`, not merely a
weaker one: for the intended `S` it is UNSATISFIABLE.**  It reads "every prime `≠ ⊥` is
maximal", and in `k[x] × k[x]` — a product of two smooth affine curves, which is exactly
the shape of the rigidified moduli ring over `𝔽_p` — the prime `⊥ × k[x]` is nonzero and
not maximal.  So a naive "delete `[IsDomain S]`" would have produced a lemma with a
vacuous hypothesis.  `Ring.KrullDimLE 1 S` (`= Order.KrullDimLE 1 (PrimeSpectrum S)`) is
the right notion and does hold for that product.  The two agree on domains: mathlib has
`Ring.DimensionLEOne R → Ring.KrullDimLE 1 R` as a low-priority instance.

**`[IsDomain R]` is REQUIRED and the statement is FALSE without it.**  Witness: `R = S =
k[x] × k[x]` with `G` trivial.  Then `Ring.KrullDimLE 1 S` holds, `algebraMap R S = id` is
injective, `Algebra.IsInvariant R S G` is trivially true, and the conclusion
`Ring.DimensionLEOne R` fails at `⊥ × k[x]` exactly as above.

The proof is the going-up one.  If a nonzero prime `p` of `R` were not maximal, `⊥ < p < m`
would be a chain of length two in `Spec R` (`⊥` is prime because `R` is a domain — this is
where `[IsDomain R]` enters), and lying over plus going up
(`Ideal.exists_ideal_over_prime_of_isIntegral`, which carries NO domain hypothesis, and
`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`) lift it to a chain `Q₀ < Q₁ < Q₂`
in `Spec S`, contradicting `Ring.KrullDimLE 1 S`. -/
theorem dimensionLEOne_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [Ring.KrullDimLE 1 S]
    (hinj : Function.Injective (algebraMap R S)) :
    Ring.DimensionLEOne R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hinj
  refine ⟨fun {p} hp0 hp => ?_⟩
  haveI := hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  haveI := hm
  rcases eq_or_lt_of_le hpm with rfl | hpltm
  · exact hm
  exfalso
  -- lift `⊥ < p < m` to a chain `Q₀ < Q₁ < Q₂` in `Spec S`
  obtain ⟨Q₀, -, hQ₀p, hQ₀c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) (⊥ : Ideal R) (⊥ : Ideal S)
      (by simp [← RingHom.ker_eq_comap_bot, hker])
  haveI := hQ₀p
  obtain ⟨Q₁, hQ₀₁, hQ₁p, hQ₁c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (R := R) (S := S) p Q₀
      (by rw [hQ₀c]; exact bot_le)
  haveI := hQ₁p
  obtain ⟨Q₂, hQ₁₂, hQ₂p, hQ₂c⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (R := R) (S := S) m Q₁
      (by rw [hQ₁c]; exact hpm)
  haveI := hQ₂p
  have h01 : Q₀ < Q₁ := lt_of_le_of_ne hQ₀₁ (by rintro rfl; rw [hQ₀c] at hQ₁c; exact hp0 hQ₁c.symm)
  have h12 : Q₁ < Q₂ := lt_of_le_of_ne hQ₁₂ (by
    rintro rfl; rw [hQ₁c] at hQ₂c; exact hpltm.ne hQ₂c)
  rcases Ring.krullDimLE_one_iff.mp ‹Ring.KrullDimLE 1 S› Q₁ hQ₁p with hmin | hmax
  · exact absurd (hmin.2 ⟨hQ₀p, bot_le⟩ h01.le) (not_le_of_gt h01)
  · exact h12.ne (hmax.eq_of_le hQ₂p.ne_top h12.le)

/-- **The Krull dimension is unchanged** (PROVEN, in the only case needed).

`≤` is `dimensionLEOne_of_isInvariant`.  `≥` holds because contraction along an
integral extension is strictly monotone on primes
(`Ideal.IsIntegral.comap_lt_comap`, which carries NO domain hypothesis — it is stated above
`variable [IsDomain A]` in `Mathlib/RingTheory/Ideal/GoingUp.lean`), so it embeds a chain of
`Spec S` into a chain of `Spec R`.

**`[IsDomain S]` was dropped 2026-07-30**; see `dimensionLEOne_of_isInvariant` for why the
replacement is `[IsDomain R] [Ring.KrullDimLE 1 S]` and not a bare deletion. -/
theorem ringKrullDim_eq_one_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [Ring.KrullDimLE 1 S]
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
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)
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

/-! ### The same package when `S` is NOT a domain

This is the version the `𝔽_p` coarse-space leaf
`isRegularRing_coarseRing_of_gamma0AtlasOver_zmod` (`ModularCurve/X0.lean`) needs, and the
reason the three lemmas above were generalised.  Over `ℚ` the rigidified moduli scheme
`𝔐([Γ₀(N)], [Γ(n)])` is integral, because `Gal(ℚ(ζ_n)/ℚ)` permutes its geometric components
— indexed by the Weil pairing — transitively.  Over `𝔽_p` that group is generated by the
single Frobenius `ζ ↦ ζ^p`, whose orbits have size `ord_n(p)`, so `A` is a PRODUCT of
`φ(n)/ord_n(p)` smooth affine curves.  `IsDomain A` is then false (explicitly: `n = 3`,
`p = 7`, where `2³ ≡ 1 mod 7` so both primitive cube roots are `𝔽_7`-rational and there are
two components), and with it `IsDedekindDomain A`.

What survives is exactly what is asked for below: `A` reduced, integrally closed in its
TOTAL quotient ring, and of Krull dimension one.  `IsDomain B` is NOT derived here — it is
false in general for the pair `(R, S)` as hypothesised, and in the modular application it is
the separate input `isDomain_of_gamma0AtlasOver_zmod` (Deligne–Rapoport IV.5.5), which
holds because `det : GL₂(ℤ/n) → (ℤ/n)ˣ` is surjective and so `G` permutes the components
transitively even when Frobenius does not. -/

/-- **The invariants of a REDUCED normal ring of dimension one form a Dedekind domain**
(PROVEN 2026-07-30), given that they form a domain.

`isDedekindDomain_of_isInvariant` with `[IsDedekindDomain S]` weakened to the three
conditions that survive for a finite product of Dedekind domains: `[IsReduced S]`,
`[IsIntegrallyClosed S]` (which mathlib reads in the TOTAL quotient ring, so it is the
correct notion here and is *true* of such a product) and `[Ring.KrullDimLE 1 S]`.

`[IsDomain R]` replaces the `IsDomain R` that used to come free from `[IsDomain S]` and
`hinj`; it cannot be derived and it is genuinely needed — see the counterexample on
`dimensionLEOne_of_isInvariant`.  It is also exactly what the modular consumer has. -/
theorem isDedekindDomain_of_isInvariant_of_isReduced (k R S : Type*) [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDomain R] [IsReduced S] [IsIntegrallyClosed S] [Ring.KrullDimLE 1 S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsDedekindDomain R ∧ Algebra.FiniteType k R := by
  haveI hft : Algebra.FiniteType k R := finiteType_of_isInvariant k R S G hinj
  haveI hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI hic : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isInvariant R S G hinj
      (nonZeroDivisors_le_comap_of_isInvariant R S G hinj)
  haveI hd1 : Ring.DimensionLEOne R := dimensionLEOne_of_isInvariant R S G hinj
  haveI : IsDedekindRing R := { hnoeth, hd1, hic with }
  exact ⟨inferInstance, hft⟩

/-- **The coarse ring of a REDUCED normal presentation of dimension one is a regular
finite-type domain of Krull dimension one** (PROVEN 2026-07-30) — the non-domain analogue
of `isRegularRing_of_isInvariant`, and the exact package the `𝔽_p` modular-curve consumer
asks for.

`Ring.KrullDimLE 1 S` is not a separate binder: it is `Ring.krullDimLE_iff.mpr hdim.le`. -/
theorem isRegularRing_of_isInvariant_of_isReduced (k R S : Type*) [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDomain R] [IsReduced S] [IsIntegrallyClosed S]
    (hinj : Function.Injective (algebraMap R S)) (hdim : ringKrullDim S = (1 : ℕ)) :
    IsRegularRing R ∧ Algebra.FiniteType k R ∧ ringKrullDim R = (1 : ℕ) := by
  haveI : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr (le_of_eq hdim)
  obtain ⟨hded, hft⟩ := isDedekindDomain_of_isInvariant_of_isReduced k R S G hinj
  haveI := hded
  exact ⟨inferInstance, hft, ringKrullDim_eq_one_of_isInvariant R S G hinj hdim⟩

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

/-- **A finite-dimensional SEPARABLE intermediate field is linearly disjoint from `L`**
(PROVEN; generalized from `[PerfectField k]` to `[Algebra.IsSeparable k A]` on 2026-07-30).

`A/k` is finite separable, so it has a primitive element `α`, and `A` has the `k`-basis
`1, α, …, α^{d-1}` with `d = deg (minpoly k α)`.  By
`minpoly_map_eq_of_algebraicClosure_eq_bot` the minimal polynomial of `α` over
`L` still has degree `d`, so those powers stay `L`-linearly independent inside
`M`; that is `IntermediateField.LinearDisjoint.of_basis_left`.

WHY THE HYPOTHESIS MOVED FROM `k` TO `A`, and why it matters downstream.  `PerfectField k`
entered this proof at exactly ONE point — `Field.powerBasisOfFiniteOfSeparable k A`, whose
real requirement is `Algebra.IsSeparable k A` — and perfection of `k` is a strictly stronger
way to get it (`PerfectField k` + `A/k` algebraic ⟹ `Algebra.IsSeparable k A`, an instance).
The stronger form is unavailable exactly where the transcendental half needs it: the
rational function field `k(ι)` is IMPERFECT in characteristic `p`, so
`isDomain_tensorProduct_of_isTranscendenceBasis` — which applies the algebraic half over
`Fk = k(ι)` — could not be run in characteristic `p` at all.  With the hypothesis on `A` it
can, provided `K/Fk` is separable, i.e. provided `ι` is a SEPARATING transcendence basis.
See the merge note on
`isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`. -/
theorem linearDisjoint_of_finiteDimensional_of_isSeparable
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [FiniteDimensional k A] [Algebra.IsSeparable k A] :
    A.LinearDisjoint L := by
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

/-- **An algebraic SEPARABLE intermediate field is linearly disjoint from `L`** (PROVEN;
generalized from `[PerfectField k]` to `[Algebra.IsSeparable k A]` on 2026-07-30).

Linear independence is a statement about finite subfamilies, and every finite
subfamily of a `k`-basis of `A` lies in the finite-dimensional intermediate
field it generates; apply
`linearDisjoint_of_finiteDimensional_of_isSeparable` there.  This is
the colimit step of the classical argument, done at the level of linear
independence rather than of tensor products, which avoids having to build the
directed colimit of the `L ⊗[k] A₀`.

Separability descends to the finite subextension for free: `A₀` is generated by finitely
many elements of `A`, each separable over `k`, and
`IntermediateField.isSeparable_adjoin_iff_isSeparable` turns that into
`Algebra.IsSeparable k A₀`. -/
theorem linearDisjoint_of_isAlgebraic_of_isSeparable
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [Algebra.IsAlgebraic k A] [Algebra.IsSeparable k A] :
    A.LinearDisjoint L := by
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
  have hTsep : ∀ x ∈ T, IsSeparable k x := by
    rintro _ ⟨j, -, rfl⟩
    show Polynomial.Separable (minpoly k ((a j : A) : M))
    rw [← IntermediateField.minpoly_eq]
    exact Algebra.IsSeparable.isSeparable k (a j)
  set A₀ : IntermediateField k M := IntermediateField.adjoin k T with hA₀
  haveI : FiniteDimensional k A₀ := IntermediateField.finiteDimensional_adjoin hTint
  haveI : Algebra.IsSeparable k A₀ :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable k M).mpr hTsep
  have hld0 : A₀.LinearDisjoint L :=
    linearDisjoint_of_finiteDimensional_of_isSeparable hbot A₀
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

/-- **The algebraic half of regularity, in the form that has no hypothesis on `k`**
(PROVEN 2026-07-30).

If `k` is algebraically closed in `L` and `K/k` is algebraic and SEPARABLE, then `L ⊗[k] K`
is a domain.  Embed `K` into an algebraic closure `M` of `L` (possible because `K/k` is
algebraic), apply `linearDisjoint_of_isAlgebraic_of_isSeparable` to the image, and conclude
with `IntermediateField.LinearDisjoint.isDomain'`.

This is the form the characteristic-`p` route needs, where the base is the imperfect
rational function field `k(ι)` and separability comes from `ι` being a SEPARATING
transcendence basis rather than from the base being perfect.  Over a perfect `k` the
separability hypothesis is automatic, which is
`isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot` just below. -/
theorem isDomain_tensorProduct_of_isAlgebraic_of_isSeparable
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] :
    IsDomain (L ⊗[k] K) := by
  set M := AlgebraicClosure L with hM
  let fa : K →ₐ[k] M := IsAlgClosed.lift
  haveI : Algebra.IsAlgebraic k fa.fieldRange := (AlgEquiv.ofInjectiveField fa).isAlgebraic
  haveI : Algebra.IsSeparable k fa.fieldRange :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField fa)
  have hld : (fa.fieldRange).LinearDisjoint L :=
    linearDisjoint_of_isAlgebraic_of_isSeparable hbot _
  have hld2 : (fa.fieldRange).LinearDisjoint ((IsScalarTower.toAlgHom k L M).fieldRange) := by
    rw [IntermediateField.linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]
    rw [IntermediateField.linearDisjoint_iff] at hld
    exact hld
  haveI : IsDomain (K ⊗[k] L) := IntermediateField.LinearDisjoint.isDomain' hld2
  exact (Algebra.TensorProduct.comm k L K).toMulEquiv.isDomain

/-! ### The algebraic half for a SEPARABLE extension

`PerfectField k` enters the three theorems above only to supply a primitive element, i.e.
only through the *separability* of the algebraic extension being tensored in.  Taking that
separability as a hypothesis instead is what makes the algebraic half usable over an
IMPERFECT base — and the base that matters is a rational function field `k(ι)` in
characteristic `p`, which is never perfect.  That is one of the two obstructions that kept
`isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot` open in
characteristic `p` (PROVEN 2026-07-30); the other was `Infinite k` in the crux, removed in
`RegularExtension.mem_range_map_of_monic_eval₂_eq_zero'`.

The three statements below are the `[PerfectField k]` ones with `[PerfectField k]` traded for
`[Algebra.IsSeparable k _]`.  They are strictly more general (over a perfect base every
algebraic extension is separable), and the older ones are kept unchanged because their call
sites — and the characteristic-zero route through
`isDomain_tensorProduct_of_isTranscendenceBasis` — supply perfection rather than
separability. -/

/-- **A finite-dimensional SEPARABLE intermediate field is linearly disjoint from `L`**
(PROVEN).

Identical to `linearDisjoint_of_finiteDimensional_of_algebraicClosure_eq_bot` except that the
primitive element comes from the hypothesis `Algebra.IsSeparable k A` rather than from
`PerfectField k`. -/
theorem linearDisjoint_of_finiteDimensional_of_isSeparable_of_algebraicClosure_eq_bot
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [FiniteDimensional k A] [Algebra.IsSeparable k A] :
    A.LinearDisjoint L := by
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

/-- **A SEPARABLE intermediate field is linearly disjoint from `L`** (PROVEN).

The colimit step of `linearDisjoint_of_isAlgebraic_of_algebraicClosure_eq_bot`, with
separability in place of perfection.  The one new ingredient is that the finite subextension
`A₀ = k(T)` generated by a finite subfamily of a `k`-basis of `A` is again separable over `k`:
`A₀ ≤ A ≤ separableClosure k M`, by `le_separableClosure_iff`. -/
theorem linearDisjoint_of_isSeparable_of_algebraicClosure_eq_bot
    {k L M : Type*} [Field k] [Field L] [Field M] [Algebra k L] [Algebra k M]
    [Algebra L M] [IsScalarTower k L M] (hbot : algebraicClosure k L = ⊥)
    (A : IntermediateField k M) [Algebra.IsSeparable k A] : A.LinearDisjoint L := by
  classical
  let a := Module.Free.chooseBasis k A
  refine IntermediateField.LinearDisjoint.of_basis_left a ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi
  set T : Set M := (fun j => ((a j : A) : M)) '' (s : Set _)
  haveI : Finite T := (s.finite_toSet.image _)
  have hTsub : T ⊆ (A : Set M) := by
    rintro _ ⟨j, -, rfl⟩
    exact (a j).2
  have hTint : ∀ x ∈ T, IsIntegral k x := by
    rintro _ ⟨j, -, rfl⟩
    exact (Algebra.IsSeparable.isIntegral k (a j)).map A.val
  set A₀ : IntermediateField k M := IntermediateField.adjoin k T with hA₀
  haveI : FiniteDimensional k A₀ := IntermediateField.finiteDimensional_adjoin hTint
  haveI : Algebra.IsSeparable k A₀ := by
    rw [← le_separableClosure_iff k M A₀, hA₀]
    exact le_trans (IntermediateField.adjoin_le_iff.mpr hTsub) (le_separableClosure k M A)
  have hld0 : A₀.LinearDisjoint L :=
    linearDisjoint_of_finiteDimensional_of_isSeparable_of_algebraicClosure_eq_bot hbot A₀
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

/-- **The algebraic half of regularity, for a SEPARABLE extension `K/k`** (PROVEN).

If `k` is algebraically closed in `L` and `K/k` is separable algebraic, then `L ⊗[k] K` is a
domain.  Same proof as `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot`, with
`AlgEquiv.Algebra.isSeparable` transporting separability to the image of `K` in an algebraic
closure of `L`. -/
theorem isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsSeparable k K] :
    IsDomain (L ⊗[k] K) := by
  set M := AlgebraicClosure L with hM
  let fa : K →ₐ[k] M := IsAlgClosed.lift
  haveI : Algebra.IsSeparable k fa.fieldRange :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField fa)
  have hld : (fa.fieldRange).LinearDisjoint L :=
    linearDisjoint_of_isSeparable_of_algebraicClosure_eq_bot hbot _
  have hld2 : (fa.fieldRange).LinearDisjoint ((IsScalarTower.toAlgHom k L M).fieldRange) := by
    rw [IntermediateField.linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]
    rw [IntermediateField.linearDisjoint_iff] at hld
    exact hld
  haveI : IsDomain (K ⊗[k] L) := IntermediateField.LinearDisjoint.isDomain' hld2
  exact (Algebra.TensorProduct.comm k L K).toMulEquiv.isDomain

/-- **The algebraic half of regularity** (PROVEN).

If `k` is PERFECT and algebraically closed in `L`, and `K/k` is algebraic, then `L ⊗[k] K`
is a domain.  Over a perfect base every algebraic extension is separable
(`Algebra.IsSeparable` is an instance there), so this is
`isDomain_tensorProduct_of_isAlgebraic_of_isSeparable` with its hypothesis discharged. -/
theorem isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    IsDomain (L ⊗[k] K) :=
  isDomain_tensorProduct_of_isAlgebraic_of_isSeparable k L hbot K

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

/-! #### The same integral closure statement WITHOUT `Infinite k`, by a monomial order

The specialisation argument above needs `k` infinite, and that is a real obstruction over a
finite field: `X^q - X` vanishes at every `k`-point without being zero.  This section replaces
it by a LEADING-COEFFICIENT argument, which is characteristic-free and cardinality-free, and
therefore covers the `𝔽_q` case that the modular-curve consumer over `ZMod p` needs.

Fix any monomial order `mo` on `σ` (mathlib's `MonomialOrder`, e.g. `MonomialOrder.lex` for a
finite `σ`).  Let `β ∈ L[σ]` satisfy a monic equation `∑ᵢ aᵢ βⁱ = 0` with `aᵢ ∈ k[σ]`, and let
`M` be the largest of the monomials `deg aᵢ + i · deg β`.  Reading off the coefficient of `M`
kills every term of smaller degree and leaves

  `∑_{i ∈ T} lc(aᵢ) · lc(β)ⁱ = 0`,   `T = {i : deg aᵢ + i · deg β = M} ≠ ∅`,

a NONZERO polynomial relation for `lc β` over `k` (nonzero because `lc aᵢ ≠ 0` for `i ∈ T`, and
`T` contains the index at which the maximum is attained, chosen among the `i` with `aᵢ ≠ 0`).
So `lc β` is algebraic over `k`, hence lies in `k`; subtracting its leading term from `β`
leaves an element that is still integral over `k[σ]` and has strictly smaller support, and an
induction on the size of the support finishes.

*The check that would refute this*: it must not prove `MvPolynomial σ k` integrally closed in
`MvPolynomial σ L` for an `L` in which `k` is NOT algebraically closed — and indeed `hbot` is
used exactly once, to put the algebraic element `lc β` into `k`.  Read with `L = k(b)` for `b`
transcendental and `σ = {t}`: `β = b·t` is not integral over `k[t]`, and the argument says why
— a monic equation for it would make `b` algebraic over `k`. -/

/-- Monomial degree is unchanged by a coefficientwise field extension (the support is). -/
theorem degree_map_eq [Field k] [Field L] [Algebra k L] (mo : MonomialOrder σ)
    (a : MvPolynomial σ k) :
    mo.degree (MvPolynomial.map (algebraMap k L) a) = mo.degree a := by
  classical
  unfold MonomialOrder.degree
  rw [MvPolynomial.support_map_of_injective a (algebraMap k L).injective]

/-- Leading coefficients commute with a coefficientwise field extension. -/
theorem leadingCoeff_map_eq [Field k] [Field L] [Algebra k L] (mo : MonomialOrder σ)
    (a : MvPolynomial σ k) :
    mo.leadingCoeff (MvPolynomial.map (algebraMap k L) a)
      = algebraMap k L (mo.leadingCoeff a) := by
  unfold MonomialOrder.leadingCoeff
  rw [degree_map_eq mo a, MvPolynomial.coeff_map]

/-- **Coefficient extraction at the maximal monomial degree** (PROVEN).  If `M` bounds
`deg (A i) + i · deg β` for every `i` with `A i ≠ 0`, then the coefficient of `M` in
`∑ i ∈ s, A i * β ^ i` is `∑ lc (A i) * lc β ^ i` over the indices attaining `M`: the other
terms have monomial degree `≺ M` and so do not contribute. -/
theorem coeff_sum_mul_pow {R : Type*} [CommRing R] [DecidableEq (σ →₀ ℕ)]
    (mo : MonomialOrder σ)
    (β : MvPolynomial σ R) (A : ℕ → MvPolynomial σ R) (s : Finset ℕ) (M : σ →₀ ℕ)
    (hmax : ∀ i ∈ s, A i ≠ 0 → mo.degree (A i) + i • mo.degree β ≼[mo] M) :
    MvPolynomial.coeff M (∑ i ∈ s, A i * β ^ i)
      = ∑ i ∈ s.filter (fun i => mo.degree (A i) + i • mo.degree β = M),
          mo.leadingCoeff (A i) * mo.leadingCoeff β ^ i := by
  classical
  rw [MvPolynomial.coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hdi : mo.degree (A i) + i • mo.degree β = M
  · rw [if_pos hdi, ← hdi, mo.coeff_mul_of_add_of_degree_le le_rfl (mo.degree_pow_le i),
      MonomialOrder.coeff_pow_nsmul_degree, ← MonomialOrder.leadingCoeff]
  · rw [if_neg hdi]
    by_cases hA : A i = 0
    · rw [hA, zero_mul, MvPolynomial.coeff_zero]
    have h1 : mo.degree (A i * β ^ i) ≼[mo] mo.degree (A i) + i • mo.degree β := by
      refine le_trans mo.degree_mul_le ?_
      rw [map_add, map_add]
      exact add_le_add le_rfl (mo.degree_pow_le (f := β) i)
    have h2 : mo.degree (A i) + i • mo.degree β ≺[mo] M :=
      lt_of_le_of_ne (hmax i hi hA) fun h => hdi (mo.toSyn.injective h)
    exact mo.coeff_eq_zero_of_lt (lt_of_le_of_lt h1 h2)

/-- **The leading coefficient of an integral element is ALGEBRAIC over the base field**
(PROVEN) — the step that replaces the specialisation argument, and the only place where a
monomial order is used.

If `β : MvPolynomial σ L` satisfies a monic equation over `MvPolynomial σ k`, then
`mo.leadingCoeff β` is algebraic over `k`, for every monomial order `mo`.  No hypothesis on
`k` beyond being a field: in particular `k` may be finite. -/
theorem isAlgebraic_leadingCoeff_of_monic_eval₂_eq_zero [Field k] [Field L] [Algebra k L]
    (mo : MonomialOrder σ)
    (β : MvPolynomial σ L) (p : Polynomial (MvPolynomial σ k)) (hp : p.Monic)
    (hz : Polynomial.eval₂ (MvPolynomial.map (algebraMap k L)) β p = 0) :
    IsAlgebraic k (mo.leadingCoeff β) := by
  classical
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.map (algebraMap k L) (p.coeff i) * β ^ i = 0 := by
    rw [← hz, Polynomial.eval₂_eq_sum_range]
  have hnT : p.natDegree ∈ (Finset.range (p.natDegree + 1)).filter (fun i => p.coeff i ≠ 0) := by
    refine Finset.mem_filter.mpr ⟨Finset.self_mem_range_succ _, ?_⟩
    rw [hp.coeff_natDegree]
    exact one_ne_zero
  obtain ⟨i₁, hi₁mem, hi₁⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.range (p.natDegree + 1)).filter (fun i => p.coeff i ≠ 0)) ⟨_, hnT⟩
    (fun i => mo.toSyn (mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i))
      + i • mo.degree β))
  have hi₁range : i₁ ∈ Finset.range (p.natDegree + 1) := (Finset.mem_filter.mp hi₁mem).1
  have hi₁ne : p.coeff i₁ ≠ 0 := (Finset.mem_filter.mp hi₁mem).2
  have hmax : ∀ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.map (algebraMap k L) (p.coeff i) ≠ 0 →
      mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i)) + i • mo.degree β ≼[mo]
        mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i₁)) + i₁ • mo.degree β := by
    intro i hi hne
    have hne' : p.coeff i ≠ 0 := fun h => hne (by rw [h, map_zero])
    have := Finset.le_sup' (f := fun i => mo.toSyn
      (mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i)) + i • mo.degree β))
      (s := (Finset.range (p.natDegree + 1)).filter (fun i => p.coeff i ≠ 0))
      (Finset.mem_filter.mpr ⟨hi, hne'⟩)
    rw [hi₁] at this
    exact this
  have hzero := coeff_sum_mul_pow mo β (fun i => MvPolynomial.map (algebraMap k L) (p.coeff i))
    (Finset.range (p.natDegree + 1))
    (mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i₁)) + i₁ • mo.degree β) hmax
  rw [hsum, MvPolynomial.coeff_zero] at hzero
  refine ⟨∑ i ∈ (Finset.range (p.natDegree + 1)).filter
      (fun i => mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i)) + i • mo.degree β
        = mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i₁)) + i₁ • mo.degree β),
    Polynomial.monomial i (mo.leadingCoeff (p.coeff i)), ?_, ?_⟩
  · have hi₁filter : i₁ ∈ (Finset.range (p.natDegree + 1)).filter
        (fun i => mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i)) + i • mo.degree β
          = mo.degree (MvPolynomial.map (algebraMap k L) (p.coeff i₁)) + i₁ • mo.degree β) :=
      Finset.mem_filter.mpr ⟨hi₁range, rfl⟩
    intro hQ
    have hc := congrArg (fun q : Polynomial k => q.coeff i₁) hQ
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single_of_mem i₁ hi₁filter
      (fun j _ hj => by rw [Polynomial.coeff_monomial, if_neg hj]),
      Polynomial.coeff_monomial, if_pos rfl] at hc
    exact (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hi₁ne) hc
  · rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hzero.symm
    rw [Polynomial.aeval_monomial, leadingCoeff_map_eq mo (p.coeff i)]

/-- **`MvPolynomial σ k` is integrally closed in `MvPolynomial σ L`** when `k` is algebraically
closed in `L` — with NO hypothesis on the cardinality of `k` (PROVEN 2026-07-30).

This is `mem_range_map_of_monic_eval₂_eq_zero` with `[Infinite k]` traded for a monomial order
on `σ`.  Induction on the size of the support of `β`: the leading coefficient is algebraic over
`k` by `isAlgebraic_leadingCoeff_of_monic_eval₂_eq_zero`, hence lies in `k` by `hbot`, so the
leading term is defined over `k`; subtracting it leaves an element integral over
`MvPolynomial σ k` with strictly smaller support. -/
theorem mem_range_map_of_monic_eval₂_eq_zero' [Field k] [Field L] [Algebra k L]
    (mo : MonomialOrder σ)
    (hbot : ∀ y : L, IsIntegral k y → y ∈ Set.range (algebraMap k L))
    (β : MvPolynomial σ L) (p : Polynomial (MvPolynomial σ k)) (hp : p.Monic)
    (hz : Polynomial.eval₂ (MvPolynomial.map (algebraMap k L)) β p = 0) :
    β ∈ Set.range (MvPolynomial.map (algebraMap k L)) := by
  classical
  letI : Algebra (MvPolynomial σ k) (MvPolynomial σ L) := MvPolynomial.algebraMvPolynomial
  have halg : (algebraMap (MvPolynomial σ k) (MvPolynomial σ L) : _ →+* _)
      = MvPolynomial.map (algebraMap k L) := RingHom.algebraMap_toAlgebra _
  suffices H : ∀ (n : ℕ) (γ : MvPolynomial σ L), γ.support.card ≤ n →
      IsIntegral (MvPolynomial σ k) γ →
      γ ∈ Set.range (MvPolynomial.map (algebraMap k L)) by
    exact H β.support.card β le_rfl ⟨p, hp, by rw [halg]; exact hz⟩
  intro n
  induction n with
  | zero =>
      intro γ hcard _
      have hγ : γ = 0 := by
        rw [← MvPolynomial.support_eq_empty]
        exact Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      exact ⟨0, by rw [hγ, map_zero]⟩
  | succ n ih =>
      intro γ hcard hint
      by_cases hγ : γ = 0
      · exact ⟨0, by rw [hγ, map_zero]⟩
      obtain ⟨q, hq, hqz⟩ := id hint
      have hqz' : Polynomial.eval₂ (MvPolynomial.map (algebraMap k L)) γ q = 0 := by
        rw [← halg]; exact hqz
      obtain ⟨c, hc⟩ := hbot _
        (isAlgebraic_leadingCoeff_of_monic_eval₂_eq_zero mo γ q hq hqz').isIntegral
      have hmono : MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)
          = MvPolynomial.map (algebraMap k L) (MvPolynomial.monomial (mo.degree γ) c) := by
        rw [MvPolynomial.map_monomial, hc]
      have hintmono : IsIntegral (MvPolynomial σ k)
          (MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)) := by
        rw [hmono, ← halg]
        exact isIntegral_algebraMap
      have hint' : IsIntegral (MvPolynomial σ k)
          (γ - MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)) :=
        hint.sub hintmono
      have hcoeffeq : MvPolynomial.coeff (mo.degree γ)
          (γ - MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)) = 0 := by
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl,
          ← MonomialOrder.leadingCoeff, sub_self]
      have hcoeffne : ∀ m, m ≠ mo.degree γ → MvPolynomial.coeff m
          (γ - MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ))
          = MvPolynomial.coeff m γ := by
        intro m hm
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
          if_neg (fun h : mo.degree γ = m => hm h.symm), sub_zero]
      have hsupp : (γ - MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)).support
          ⊆ γ.support.erase (mo.degree γ) := by
        intro m hm
        rw [MvPolynomial.mem_support_iff] at hm
        refine Finset.mem_erase.mpr ⟨fun hmeq => hm (hmeq ▸ hcoeffeq), ?_⟩
        refine MvPolynomial.mem_support_iff.mpr ?_
        rw [← hcoeffne m (fun hmeq => hm (hmeq ▸ hcoeffeq))]
        exact hm
      have hcard' : (γ - MvPolynomial.monomial (mo.degree γ) (mo.leadingCoeff γ)).support.card
          ≤ n := by
        have h1 := Finset.card_le_card hsupp
        rw [Finset.card_erase_of_mem (mo.degree_mem_support hγ)] at h1
        have h2 : 1 ≤ γ.support.card :=
          Finset.card_pos.mpr ⟨_, mo.degree_mem_support hγ⟩
        omega
      obtain ⟨δ, hδ⟩ := ih _ hcard' hint'
      refine ⟨δ + MvPolynomial.monomial (mo.degree γ) c, ?_⟩
      rw [map_add, hδ, ← hmono]
      ring

/-- **PURELY TRANSCENDENTAL BASE CHANGE PRESERVES "ALGEBRAICALLY CLOSED IN", in ANY
characteristic and for a base of ANY cardinality** (PROVEN 2026-07-30).

`algebraicClosure_eq_bot_of_mvPolynomial` with `[Infinite k]` traded for a monomial order on
`σ`; the proof is the same, over `mem_range_map_of_monic_eval₂_eq_zero'`. -/
theorem algebraicClosure_eq_bot_of_mvPolynomial'
    [Field k] [Field L] [Algebra k L] (mo : MonomialOrder σ)
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
  obtain ⟨γ, hγ⟩ := mem_range_map_of_monic_eval₂_eq_zero' mo hbot β p hp hpz'
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


/-- **A field extension in which the base field is algebraically closed is regular — the case
of a SEPARATING transcendence basis, in ANY characteristic** (PROVEN 2026-07-30).

`k` is algebraically closed in `L`; `x : ι → K` is algebraically independent over `k` and `K` is
SEPARABLE over the subfield `k(x)` it generates (a *separating* transcendence basis — no
maximality is needed, only separability of what is left).  Then `L ⊗[k] K` is a domain.

This is `isDomain_tensorProduct_of_isTranscendenceBasis` with characteristic zero removed at
both of the places it entered:

* the crux is `RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial'`, whose
  leading-coefficient argument needs no `Infinite k`; and
* the algebraic half over `Fk = k(ι)` is
  `isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot`, which asks for
  separability of `K/Fk` rather than perfection of `Fk` — and `k(ι)` is never perfect in
  characteristic `p`.

`mo` is any monomial order on `ι`; for a finite `ι` take `MonomialOrder.lex`.  Its only role is
to pick out a leading coefficient, and the conclusion does not depend on the choice.

`Algebra.IsSeparable ↥(IntermediateField.adjoin k (Set.range x)) K` is supplied by mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField` (MacLane: a finitely generated
extension of a PERFECT field is separably generated) — which is where the perfection of `k`
that this development really needs is spent. -/
theorem isDomain_tensorProduct_of_algebraicIndependent_of_isSeparable
    {k L K : Type*} [Field k] [Field L] [Algebra k L] [Field K] [Algebra k K]
    (hbot : algebraicClosure k L = ⊥)
    {ι : Type*} (mo : MonomialOrder ι) {x : ι → K} (hai : AlgebraicIndependent k x)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k (Set.range x)) K] :
    IsDomain (L ⊗[k] K) := by
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
    RegularExtension.algebraicClosure_eq_bot_of_mvPolynomial' mo
      (fun y hy => by
        have := hbot ▸ (mem_algebraicClosure_iff' (F := k) (E := L) (x := y)).mpr hy
        simpa [IntermediateField.mem_bot] using this) hPQ
  letI aPkK : Algebra (MvPolynomial ι k) K :=
    (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] K).toRingHom.toAlgebra
  have hxinj : Function.Injective (algebraMap (MvPolynomial ι k) K) :=
    algebraicIndependent_iff_injective_aeval.mp hai
  haveI towkPkK : IsScalarTower k (MvPolynomial ι k) K :=
    IsScalarTower.of_algebraMap_eq (fun c => by simp [RingHom.algebraMap_toAlgebra])
  letI aFkK : Algebra (FractionRing (MvPolynomial ι k)) K := (IsFractionRing.lift hxinj).toAlgebra
  haveI towPkFkK : IsScalarTower (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) K :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsFractionRing.lift_algebraMap hxinj c).symm)
  haveI towkFkK : IsScalarTower k (FractionRing (MvPolynomial ι k)) K := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) K,
      IsScalarTower.algebraMap_apply (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) K,
      ← IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))]
  haveI sepFkK : Algebra.IsSeparable (FractionRing (MvPolynomial ι k)) K := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (hai.aevalEquivField.symm.toRingEquiv) (RingEquiv.refl K) (RingHom.ext fun y => ?_)
    show algebraMap (FractionRing (MvPolynomial ι k)) K (hai.aevalEquivField.symm y) = (y : K)
    rw [RingHom.algebraMap_toAlgebra]
    exact hai.lift_reprField y
  haveI hD : IsDomain ((FractionRing (MvPolynomial ι L)) ⊗[FractionRing (MvPolynomial ι k)] K) :=
    isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot
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
(**PROVEN 2026-07-29** in characteristic zero, **PROVEN 2026-07-30** in positive
characteristic; opened as a sorry leaf 2026-07-27).

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
`linearDisjoint_of_finiteDimensional_of_isSeparable`, through
mathlib's instance `Algebra.IsSeparable K L` for `[PerfectField K]` with
`L/K` algebraic (`Mathlib/FieldTheory/Perfect.lean`).

**MERGE NOTE, release 18** (and how the two obstructions it names were removed,
2026-07-30).  Characteristic zero entered the *transcendental* route TWICE, and
neither use survives the `PerfectField` weakening:

* through `Infinite k` in the specialisation argument — over `𝔽_q` the
  polynomial `X^q - X` vanishes at every `k`-point without being zero, so
  `mem_range_map_of_forall_eval_mem` (which carries `[Infinite k]`) fails; and
* through the algebraic half applied over `Fk = k(ι)` inside
  `isDomain_tensorProduct_of_isTranscendenceBasis`, which needs
  `PerfectField Fk`.  A rational function field in characteristic `p` is
  **not** perfect, so that step is unavailable even for infinite `k`.

Both are gone, and neither needed `k(ι)^{1/p^∞}`:

* the specialisation argument is replaced by a LEADING-COEFFICIENT argument,
  `RegularExtension.mem_range_map_of_monic_eval₂_eq_zero'` — read off the coefficient of the
  largest monomial in a monic equation and the leading coefficient of `β` satisfies a nonzero
  polynomial over `k`, so it is algebraic, hence in `k`; induct on the support.  This is
  characteristic-free AND cardinality-free, so it covers `𝔽_q`;
* the algebraic half is applied in the form
  `isDomain_tensorProduct_of_isSeparable_of_algebraicClosure_eq_bot`, which asks for
  `Algebra.IsSeparable Fk K` instead of `PerfectField Fk`.  That separability is exactly what
  a SEPARATING transcendence basis provides, and mathlib's
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` (MacLane) provides one for any
  finitely generated extension of a perfect field — which is why `S` being a `Finset` matters
  and why the perfection of `k` is genuinely load-bearing here rather than incidental.

So this leaf is **PROVEN in every characteristic**.  The characteristic-zero branch below is
kept on its original route (`isDomain_tensorProduct_of_isTranscendenceBasis`, which needs no
separating basis and no finiteness of the basis); the positive-characteristic branch goes
through `isDomain_tensorProduct_of_algebraicIndependent_of_isSeparable`.  Either branch would
do for both cases; the split is a deliberate no-op on the char-0 proof term. -/
theorem isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] (S : Finset K)
    (_hna : ¬ Algebra.IsAlgebraic k (IntermediateField.adjoin k (S : Set K))) :
    IsDomain (L ⊗[k] (IntermediateField.adjoin k (S : Set K))) := by
  classical
  by_cases hchar : CharZero k
  · haveI := hchar
    obtain ⟨t, ht⟩ :=
      exists_isTranscendenceBasis k (A := ↥(IntermediateField.adjoin k (S : Set K)))
    exact isDomain_tensorProduct_of_isTranscendenceBasis hbot ht
  · -- Positive characteristic: a separating transcendence basis (MacLane), then the
    -- characteristic-free transcendental half.  `hchar` itself is not used — the branch is
    -- valid for every `k`.
    haveI hEFT : Algebra.EssFiniteType k ↥(IntermediateField.adjoin k (S : Set K)) :=
      IntermediateField.essFiniteType_iff.mpr ⟨S, rfl⟩
    obtain ⟨s, hsb, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k
      ↥(IntermediateField.adjoin k (S : Set K))
    haveI : Fintype ↥s := FinsetCoe.fintype s
    -- reindex the basis by `Fin (card s)`, which carries a monomial order
    have hai : AlgebraicIndependent k
        (fun i : Fin (Fintype.card ↥s) =>
          (((Fintype.equivFin ↥s).symm i : ↥s) : ↥(IntermediateField.adjoin k (S : Set K)))) :=
      hsb.1.comp _ (Fintype.equivFin ↥s).symm.injective
    have hrange : Set.range (fun i : Fin (Fintype.card ↥s) =>
        (((Fintype.equivFin ↥s).symm i : ↥s) : ↥(IntermediateField.adjoin k (S : Set K))))
        = (s : Set ↥(IntermediateField.adjoin k (S : Set K))) := by
      rw [show (fun i : Fin (Fintype.card ↥s) =>
          (((Fintype.equivFin ↥s).symm i : ↥s) : ↥(IntermediateField.adjoin k (S : Set K))))
          = (Subtype.val ∘ (Fintype.equivFin ↥s).symm) from rfl,
        Set.range_comp, ((Fintype.equivFin ↥s).symm.surjective).range_eq, Set.image_univ,
        Subtype.range_coe]
    haveI : Algebra.IsSeparable
        ↥(IntermediateField.adjoin k (Set.range (fun i : Fin (Fintype.card ↥s) =>
          (((Fintype.equivFin ↥s).symm i : ↥s) : ↥(IntermediateField.adjoin k (S : Set K))))))
        ↥(IntermediateField.adjoin k (S : Set K)) := hrange ▸ hsep
    exact isDomain_tensorProduct_of_algebraicIndependent_of_isSeparable hbot
      (MonomialOrder.lex (σ := Fin (Fintype.card ↥s))) hai

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
