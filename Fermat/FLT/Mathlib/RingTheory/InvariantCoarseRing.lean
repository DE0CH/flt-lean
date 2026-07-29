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
  was weakened to `PerfectField k`, which is what the argument actually uses and
  what the characteristic-`p` consumer over `𝔽_p` needs.  `CharZero ⟹
  PerfectField` is an instance, so no call site changed.)  PROVEN for `K/k` **algebraic**, and reduced in
  general to the finitely generated subextensions of `K`; the one LEAF of this
  module is the transcendental case for a finitely generated `k(S)`
  (`isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot`).
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
  — the transcendental half, for a finitely generated subextension (LEAF)
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

/-- **The transcendental half of regularity, for a finitely generated
subextension** (sorry leaf).

`k` is algebraically closed in `L`, the characteristic is zero, `S` is a finite
subset of a field extension `K/k`, and the subfield `k(S)` it generates is *not*
algebraic over `k`.  The conclusion `IsDomain (L ⊗[k] k(S))` is true for every
`S`; this leaf isolates exactly what
`isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot` (the
algebraic case, PROVEN) and `isDomain_tensorProduct_of_forall_adjoin_finset`
(the reduction to finitely generated subextensions, PROVEN) do not already
cover, so that the hypotheses record what is left rather than duplicating a
proven statement.

**The classical argument, for whoever closes it** (Bourbaki *Algebra* V §17,
EGA IV 4.6.1, Stacks 04KM).  Write `F := k(S)`.  In characteristic zero `F/k` is
separably generated: there is a *finite* transcendence basis `T ⊆ S` with `F/k(T)`
finite separable.  Then

* `L ⊗[k] k(T)` is a domain — it is the localization of the polynomial ring
  `L[T]` at the nonzero elements of `k[T]`, hence a subring of the rational
  function field `L(T)`;
* `k(T)` is algebraically closed in `Frac (L ⊗[k] k(T)) = L(T)`, because `k` is
  algebraically closed in `L`.  **This is the one step that genuinely needs new
  mathematics**: it is the statement that regularity is stable under purely
  transcendental base change;
* `L ⊗[k] F ≅ (L ⊗[k] k(T)) ⊗[k(T)] F` embeds into `L(T) ⊗[k(T)] F` by flatness
  of the field extension `F/k(T)`, and the latter is a domain by
  `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot` applied to
  the pair `(k(T), L(T))` and the algebraic extension `F/k(T)`.

So the mathematical residue is the middle bullet plus the tensor-associativity
plumbing; the algebraic case above is already available as the last step, and
the finiteness of `T` here means no colimit is needed inside this leaf either.

*The check that would refute the claim that this is all that is missing*: find a
statement in the pin whose conclusion is `algebraicClosure (RatFunc k) _ = ⊥`,
or an `IsDomain` result for `L ⊗[k] RatFunc k`.  Neither existed at
`2ead1a48`.

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
`L/K` algebraic (`Mathlib/FieldTheory/Perfect.lean`). -/
theorem isDomain_tensorProduct_adjoin_finset_of_not_isAlgebraic_of_algebraicClosure_eq_bot
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    (hbot : algebraicClosure k L = ⊥)
    (K : Type*) [Field K] [Algebra k K] (S : Finset K)
    (hna : ¬ Algebra.IsAlgebraic k (IntermediateField.adjoin k (S : Set K))) :
    IsDomain (L ⊗[k] (IntermediateField.adjoin k (S : Set K))) :=
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

Together with `isDomain_tensorProduct_of_injective` below this is exactly
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

end
