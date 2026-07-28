/-
Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean — own work
for the Fermat project (not vendored from the FLT project).

# Sufficient criteria for `GeometricallyConnected` and `SmoothOfRelativeDimension`

Mathlib's `Geometrically/*` files and `Morphisms/Smooth.lean` are, at the pin,
**purely consequential**: every lemma about `GeometricallyConnected` and about
`SmoothOfRelativeDimension` either *uses* the class or transports it (base
change, restriction, fibres, composition).  Neither file contains a single way
to *construct* one from ring-theoretic data.  That was checked on 2026-07-27:

    grep -rln "GeometricallyConnected"  .lake/packages/mathlib/Mathlib/
      -- one file: AlgebraicGeometry/Geometrically/Connected.lean
    grep -rn  "SmoothOfRelativeDimension" .lake/packages/mathlib/Mathlib/
      -- one file: AlgebraicGeometry/Morphisms/Smooth.lean, no dimension theory

*The check that would refute either claim*: the same two greps returning a
second file.

This module supplies the missing constructors for the **affine over a field**
case, which is the only case this development needs, and states them about a
ring so that a consumer can discharge them by commutative algebra.

## Contents

* `geometricallyConnected_of_geometricallyIrreducible` — the missing
  `GeometricallyIrreducible ⟹ GeometricallyConnected` implication (PROVEN).
* `geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace` — for an
  affine `Spec B ⟶ Spec R`, geometric connectedness is exactly connectedness of
  `Spec (B ⊗[R] K)` for every field extension `K/R` (PROVEN, via
  `pullbackSpecIso`).
* `geometricallyConnected_specMap_algebraMap_of_forall_isDomain` — the usable
  corollary: `B ⊗[R] K` a domain for every field `K` over `R` suffices, because
  the spectrum of a domain is irreducible (PROVEN).
* `smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` — *regular +
  finite type over a perfect field ⟹ smooth*, with the relative dimension read
  off the Krull dimension (**PROVEN 2026-07-28** over
  `Algebra.Smooth.of_isRegularRing_of_perfectField`, i.e. over Stacks `056S`,
  and over the pure dimension leaf below).
* `smoothOfRelativeDimension_specMap_algebraMap_of_smooth` — what is LEFT of the
  previous item once regularity and perfectness have been consumed: for a
  **smooth** finite-type domain over ANY field, the relative dimension is the
  Krull dimension (LEAF; no perfectness, no regularity, pure dimension theory).

## Why the connectedness criterion has to go through the function field

The cheap classical criterion — connected plus a rational point, EGA IV 4.5.13 —
is **mathematically** unavailable in the intended application: the consumer is
`Y_0(N)`, whose set of `ℚ`-points is empty for most `N`, and proving that
emptiness is the whole point of `Fermat/FLT/ModularCurve/X0.lean`.  So the
criterion offered here is the tensor-product one, which is the algebraic form of
"`R` is algebraically closed in `Frac B`".
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.PerfectClosure
public import Fermat.FLT.Mathlib.RingTheory.Smooth.RegularLocal
-- (restored at the release-12 integration: these were dropped when an import-block
-- conflict was resolved to one SIDE instead of as a UNION.  Every one is needed by a
-- proof that is already in this file.)
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

/-! ### Commutative-algebra input: regularity, smoothness, and the rank of `Ω`

The two `sorry` leaves of this file both live here, in ring-theoretic form.  The
scheme-level statement at the end of the file is then *assembled* from them with
no further mathematical content.
-/

namespace Algebra

/-! #### **A regular local ring essentially of finite type over a perfect field is
formally smooth over it** (sorry leaf, opened 2026-07-27).

This is the local form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), equivalently Matsumura *Commutative Ring Theory* §28, and it is
the single piece of this file's development that mathlib does not supply in any
form.

## What mathlib has, checked 2026-07-27

1. `IsRegularLocalRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), and
   `IsRegularRing` as "every localization at a prime is regular local".
2. The local Jacobian criterion
   `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
   (`Mathlib/RingTheory/Smooth/Local.lean`): for a presentation `0 → I → P → A → 0`
   with `P` formally smooth over the base and `Ω[P⁄R]` finite free, `A` is
   formally smooth iff `κ ⊗ I/I² → κ ⊗ Ω[P⁄R]` is injective.
3. `Algebra.FormallySmooth.of_perfectField` (`Mathlib/RingTheory/Smooth/Field.lean`):
   a field extension essentially of finite type over a perfect field is formally
   smooth.  That is this statement at the GENERIC point, and it is as far as
   mathlib's `Scheme.Hom.dense_smoothLocus_of_perfectField` gets as well.

*The check that would refute this*: `grep -rn "IsRegularRing"` over
`Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/` returning anything —
at this pin it returns nothing in either.

## The intended route

Present `A = P/I` with `P` a localization of a polynomial ring at a prime, so
that ingredient 2 applies, and prove injectivity of `κ ⊗ I/I² → κ ⊗ Ω[P⁄K]` by
counting: `dim_κ (I/I² ⊗ κ) = μ(I) ≥ ht I = dim P - dim A` always, and regularity
of `A` together with separability of `κ/K` (automatic over a perfect field) forces
equality.  The separability of the residue field is exactly where `PerfectField K`
enters, and it is genuinely needed — see the faithfulness note on the theorem at
the end of this file for the standard counterexample over an imperfect field.

## Faithfulness

Both hypotheses are load-bearing.  `EssFiniteType K A` cannot be dropped (formal
smoothness of a general regular local `K`-algebra is false — a complete local ring
such as `K⟦t⟧` is regular but not formally smooth over `K` for the discrete
topology), and `PerfectField K` cannot be dropped (same counterexample as below). -/
-- (`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` is declared in
-- `Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, which this module `public
-- import`s, and it is PROVEN there over the single leaf
-- `Algebra.injective_lTensor_residueField_kerInclusion`.  Two branches wrote the same
-- statement into two files, one importing the other -- the release-6 defect class -- so the
-- SORRIED copy that stood here has been deleted.  The surviving form takes `K` and `R`
-- IMPLICITLY; the docstring above is retained for its faithfulness note.)

/-- **A regular ring of finite type over a perfect field is formally smooth over
it** (PROVEN 2026-07-27 over `FormallySmooth.of_isRegularLocalRing_of_perfectField`).

`Algebra.smoothLocus_eq_univ_iff` turns formal smoothness of `B` into formal
smoothness of every `Bₚ`, and `IsRegularRing` is *defined* as regularity of every
`Bₚ`, so the two match up point by point.  The only work is producing
`EssFiniteType K Bₚ`, which is `EssFiniteType.of_isLocalization` composed with
`EssFiniteType K B`. -/
theorem FormallySmooth.of_isRegularRing_of_perfectField
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] :
    Algebra.FormallySmooth K B := by
  haveI : Algebra.FinitePresentation K B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  show Algebra.FormallySmooth K (Localization.AtPrime p.asIdeal)
  haveI : Algebra.EssFiniteType B (Localization.AtPrime p.asIdeal) :=
    .of_isLocalization _ p.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType K (Localization.AtPrime p.asIdeal) := .comp _ B _
  exact FormallySmooth.of_isRegularLocalRing_of_perfectField (K := K)

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **The rank of the module of Kähler differentials of a finitely generated field
extension of a perfect field is its transcendence degree** (PROVEN 2026-07-27).

Mathlib computes `Ω` for a polynomial ring (`KaehlerDifferential.mvPolynomialBasis`)
and has the whole separably-generated theory
(`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), but nowhere
connects them: `grep -rn "trdeg" Mathlib/RingTheory/Kaehler/` is empty at this pin,
and so is the reverse grep for `Ω[` over `Mathlib/FieldTheory/`.

The proof is a chain of three base changes along formally étale maps, each of
which multiplies the rank by nothing:

    K[s]  ⟶  Algebra.adjoin K s  ⟶  IntermediateField.adjoin K s  ⟶  L
          ≃                     localization                  separable algebraic

`KaehlerDifferential.isBaseChange_of_formallyEtale` turns each arrow into a base
change of `Ω`, and `IsBaseChange.rank_eq` — which needs only that the target has no
zero divisors and receives the source faithfully — reads the rank back unchanged.
The left-hand end is `KaehlerDifferential.mvPolynomialBasis`, of rank `#s`; the
right-hand end is `Ω[L⁄K]`; and `#s = trdeg K L` because `s` is a transcendence
basis.

`PerfectField K` is load-bearing and is used exactly once, to produce a
*separating* transcendence basis: over an imperfect field the third arrow can fail
to be separable and the rank strictly exceeds the transcendence degree (e.g.
`L = K(t^{1/p})` over `K = 𝔽_p(t)`, where `trdeg = 0` but `Ω[L⁄K]` is
one-dimensional). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_perfectField
    (K L : Type u) [Field K] [PerfectField K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hrange : Set.range (Subtype.val : {x // x ∈ s} → L) = (s : Set L) := Subtype.range_coe
  set P := MvPolynomial {x // x ∈ s} K with hP
  set A := Algebra.adjoin K (s : Set L) with hA
  set E := IntermediateField.adjoin K (s : Set L) with hE
  -- `L` is formally étale over `E`, because `L/E` is separable algebraic.
  haveI : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  haveI : FaithfulSMul E L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap E L).injective
  have h1 : Module.rank L Ω[L⁄K] = Module.rank E Ω[E⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K E L).rank_eq
  -- `E` is the fraction field of `A`, hence formally étale over it.
  haveI : Algebra.FormallyEtale A E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  haveI : FaithfulSMul A E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective E le_rfl)
  have h2 : Module.rank E Ω[E⁄K] = Module.rank A Ω[A⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K A E).rank_eq
  -- `A` is a polynomial ring on the transcendence basis.
  have hAeq : Algebra.adjoin K (Set.range (Subtype.val : {x // x ∈ s} → L)) = A := by
    rw [hrange]
  let e : P ≃ₐ[K] A := hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hAeq)
  letI : Algebra P A := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  haveI : Algebra.FormallyEtale P A :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl)
  haveI : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr e.injective
  have h3 : Module.rank A Ω[A⁄K] = Module.rank P Ω[P⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K P A).rank_eq
  have h4 : Module.rank P Ω[P⁄K] = Cardinal.mk {x // x ∈ s} :=
    (KaehlerDifferential.mvPolynomialBasis K {x // x ∈ s}).mk_eq_rank''.symm
  have h5 : Cardinal.mk {x // x ∈ s} = Algebra.trdeg K L := by
    simpa using hs.lift_cardinalMk_eq_trdeg
  rw [h1, h2, h3, h4, h5]

end Algebra

/-- **An injective integral ring extension preserves the Krull dimension**
(sorry leaf, opened 2026-07-27).

Stacks `00OK` (`dim S ≤ dim R`, by incomparability) together with `00OJ`
(`dim R ≤ dim S`, by lying over and going up).  This is the only gap left in the
dimension half of this file, and it is stated in full mathlib generality rather
than for the finite-type case that needs it, because that is what it is.

## What the pin has, checked 2026-07-27

Both halves of the argument are present as statements about a *single* prime; only
the passage to chains is missing.

* Incomparability: `Ideal.IsIntegral.comap_lt_comap` — for `I < J` primes of `S`,
  `comap I < comap J`.  So `PrimeSpectrum.comap (algebraMap R S)` is strictly
  monotone and `Order.krullDim_le_of_strictMono` gives `dim S ≤ dim R` directly.
* Lying over and going up: `Ideal.exists_ideal_over_prime_of_isIntegral` and
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` (the latter takes a
  prime `I` of `S` with `comap I ≤ P` and produces `Q ≥ I` over `P`).  Turning a
  chain `p₀ < ⋯ < p_n` of `R` into a chain of `S` is an induction on the chain
  using the second, i.e. an `RelSeries`/`LTSeries` induction; that induction is the
  work, and **mathlib says so itself** — the comment above
  `exists_ideal_over_prime_of_isIntegral_of_isPrime` reads *"TODO: Version of
  going-up theorem with arbitrary length chains (by induction on this)?  Not sure
  how best to write an ascending chain in Lean"*.

A dead end worth recording so it is not re-explored: the `≥` direction does **not**
follow from `Order.krullDim_le_of_strictComono_and_surj` even though
`Algebra.IsIntegral.comap_surjective` supplies its surjectivity hypothesis, because
`PrimeSpectrum.comap` is not strictly comonotone.  Counterexample: `R = k[x]`,
`S = k[x] × k[x]`, `q₁ = 0 × k[x]`, `q₂ = k[x] × (x)`; then
`comap q₁ = (0) < (x) = comap q₂` while `q₁ ⊄ q₂` (as `(0,1) ∈ q₁ \ q₂`).  So the
lifted chain really has to be built step by step, each prime chosen above the
previous one.

*The check that would refute this*: `grep -rn "krullDim" Mathlib/RingTheory/Ideal/GoingUp.lean`
or `grep -rn "IsIntegral" Mathlib/RingTheory/KrullDimension/` returning anything —
both are empty at this pin.

## Faithfulness

Injectivity is load-bearing on both sides: without it take `R` any ring and
`S = 0`, which is integral over `R` with `ringKrullDim S = ⊥ ≠ ringKrullDim R`. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R :=
  sorry

namespace Algebra

/-- **Krull dimension equals transcendence degree for a finite-type domain over a
field** (PROVEN 2026-07-27 over `ringKrullDim_eq_of_isIntegral_of_injective`).

This is the fundamental theorem of dimension theory for affine varieties
(Stacks `00OS`/`00P0`, Matsumura §14, Eisenbud Thm. A).  Mathlib does not have it,
but it does have both ingredients apart from the one leaf above:

* Noether normalisation, as `exists_finite_inj_algHom_of_fg`
  (`Mathlib/RingTheory/NoetherNormalization.lean`): an injective
  `K[X₁,…,X_s] →ₐ[K] B` making `B` a finite module.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing` plus
  `ringKrullDim_eq_zero_of_field`, giving `ringKrullDim K[X₁,…,X_s] = s`.
* `IsTranscendenceBasis.mvPolynomial` (the variables are a transcendence basis of
  the polynomial ring) and `IsTranscendenceBasis.algebraMap_comp` (a transcendence
  basis survives an algebraic extension), applied twice: once along
  `K[X₁,…,X_s] → B`, which is integral, and once along `B → Frac B`.

So `trdeg K (Frac B) = s = ringKrullDim B`, the middle equality being the leaf.

## Faithfulness

`IsDomain B` is load-bearing: `Frac B` does not exist without it, and for a
reducible finite-type algebra `ringKrullDim` records only the largest component
while no single transcendence degree exists.  `Algebra.FiniteType K B` is
load-bearing: for `B = K(t)` (not of finite type) the dimension is `0` and the
transcendence degree is `1`.  `PerfectField K` is *not* needed here — this
statement is characteristic-free — and is deliberately absent from the hypotheses. -/
theorem trdeg_fractionRing_eq_of_ringKrullDim
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    Algebra.trdeg K (FractionRing B) = n := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg K B
  letI : Algebra (MvPolynomial (Fin s) K) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) B := hgfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
  haveI : FaithfulSMul B (FractionRing B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B _)
  -- the Krull dimension of `B` is the number of normalising variables
  have hdimP : ringKrullDim (MvPolynomial (Fin s) K) = (s : ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hns : (n : WithBot ℕ∞) = (s : ℕ∞) := by
    rw [← hdim, ringKrullDim_eq_of_isIntegral_of_injective _ B hginj, hdimP]
  -- the normalising variables are a transcendence basis of `Frac B`
  have hb1 : IsTranscendenceBasis K
      (algebraMap (MvPolynomial (Fin s) K) B ∘ (MvPolynomial.X : Fin s → _)) :=
    (IsTranscendenceBasis.mvPolynomial (Fin s) K).algebraMap_comp
  haveI : Algebra.IsAlgebraic B (FractionRing B) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  have hb2 := hb1.algebraMap_comp (A := FractionRing B)
  have hcard : (s : Cardinal.{u}) = Algebra.trdeg K (FractionRing B) := by
    simpa using hb2.lift_cardinalMk_eq_trdeg
  rw [← hcard]
  have : n = s := by exact_mod_cast hns
  simp [this]

/-- **The module of Kähler differentials of a finite-type domain over a perfect
field has rank the Krull dimension** (PROVEN 2026-07-27 over the two results above).

`Ω[B⁄K]` and `Ω[Frac B⁄K]` have the same rank, because `Frac B` is a localization of
`B`, hence formally étale over it, so `Ω` base-changes; then the rank at the generic
point is the transcendence degree, which is the dimension. -/
theorem rank_kaehlerDifferential_eq_of_ringKrullDim
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    Module.rank B Ω[B⁄K] = n := by
  haveI : Algebra.FormallyEtale B (FractionRing B) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType B (FractionRing B) := .of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType K (FractionRing B) := .comp K B _
  rw [← (KaehlerDifferential.isBaseChange_of_formallyEtale K B (FractionRing B)).rank_eq,
    rank_kaehlerDifferential_eq_trdeg_of_perfectField K (FractionRing B),
    trdeg_fractionRing_eq_of_ringKrullDim K B n hdim]

end Algebra

namespace AlgebraicGeometry

/-! ### Geometric connectedness -/

/-- **A geometrically irreducible morphism is geometrically connected**
(PROVEN 2026-07-27).

Mathlib has both classes and every stability property of each, but not this
implication between them, even though it is immediate from
`IrreducibleSpace ⟹ ConnectedSpace` fibre by fibre. -/
theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [h : GeometricallyIrreducible f] : GeometricallyConnected f := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_isClosedUnderIsomorphisms] at h
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  haveI := h K y
  infer_instance

/-- **Geometric connectedness of an affine scheme over an affine base, read on
the ring** (PROVEN 2026-07-27).

`Spec B ⟶ Spec R` is geometrically connected as soon as `Spec (B ⊗[R] K)` is a
connected space for every field `K` that is an `R`-algebra.  This is exactly
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` combined with
`pullbackSpecIso`, which identifies the pullback along `Spec K ⟶ Spec R` with
`Spec (B ⊗[R] K)`.

The hypothesis is *equivalent* to the conclusion — no strength is lost — but the
lemma is stated as an implication because that is the direction a prover needs.
-/
theorem geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      ConnectedSpace (PrimeSpectrum (B ⊗[R] K))) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap R B))) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact (pullbackSpecIso R B K).hom.homeomorph.connectedSpace_iff.mpr (h K)

/-- **A geometrically integral affine ring gives a geometrically connected
morphism** (PROVEN 2026-07-27).

The usable form of the criterion above: the spectrum of a domain is irreducible
(`PrimeSpectrum.irreducibleSpace`), hence connected, so it is enough that
`B ⊗[R] K` be a domain for every field extension. -/
theorem geometricallyConnected_specMap_algebraMap_of_forall_isDomain
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (B ⊗[R] K)) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap R B))) := by
  refine geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace R B ?_
  intro K _ _
  haveI := h K
  infer_instance

/-! ### Smoothness of an affine curve over a perfect field -/

/-- **THE RELATIVE DIMENSION OF A SMOOTH AFFINE VARIETY IS ITS KRULL DIMENSION**
(sorry leaf, opened 2026-07-28 as the residue of
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` after Stacks
`056S` was discharged onto
`Algebra.Smooth.of_isRegularRing_of_perfectField`).

**There is no perfectness and no regularity left in this statement**, and that
is the point of the cut: everything characteristic-theoretic has been consumed
by `Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, and what remains is
pure dimension theory over an arbitrary field.

TRUE and classical.  `Smooth K B` gives a cover of `Spec B` by basic opens
`D(t)` with `B_t` standard smooth over `K`
(`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`), and
`Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` turns
"relative dimension `n`" on such a chart into `Module.rank B_t Ω[B_t⁄K] = n`.
So the whole content is:

* for a smooth finite-type algebra over a field, `rank Ω[B⁄K] = dim B` — the
  smooth case of "the module of differentials of a variety has rank equal to its
  dimension"; and
* `IsDomain B` is what makes that rank CONSTANT: `dim B_t = dim B` for every
  `t ≠ 0` because `B` and `B_t` are finite-type domains with the same fraction
  field, hence the same transcendence degree, hence the same dimension.

*Refute it with*: a smooth finite-type `K`-DOMAIN whose relative dimension over
`K` differs from `ringKrullDim`.  There is none.  Note `IsDomain` cannot be
dropped — see the faithfulness note on the consumer below — and `t = 0` must be
excluded from the cover when the proof is written, since `Localization.Away 0`
is the zero ring. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] (n : ℕ) (_hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) :=
  sorry

/-- **Regular + finite type over a perfect field ⟹ smooth of relative dimension
the Krull dimension** (**PROVEN 2026-07-28**; opened as a sorry leaf 2026-07-27).

This is the ring form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), together with the identification of the relative dimension: for
an *integral* finite-type algebra over a field the local dimensions are all
equal to `ringKrullDim`, so a single `n` governs every point.

## How it was closed, and what moved where

The `056S` half — the only half in which `PerfectField` and `IsRegularRing`
appear — is now `Algebra.Smooth.of_isRegularRing_of_perfectField` in
`Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, a module with **no
`Fermat` imports** that states the underlying commutative algebra ONCE:

> a regular local ring essentially of finite type over a perfect field is
> formally smooth over that field

(`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField`), together with
its global corollary for regular rings.  The local-to-global passage is free at
this pin: `Algebra.smoothLocus_eq_univ_iff` makes `FormallySmooth K B`
equivalent to formal smoothness of every localization `B_𝔭`, and `IsRegularRing`
is by definition regularity of every `B_𝔭`, so the two definitions meet
pointwise with no covering argument.  That module in turn rests on a single
named leaf, `Algebra.injective_lTensor_residueField_kerInclusion`, which is the
first of the two arrows of the local Jacobian criterion's injectivity and
mentions no field, no perfectness and no module of differentials: for a
surjection `P ↠ S` of regular local rings, `I/𝔪_P I → 𝔪_P/𝔪_P²` is injective.
The second arrow — the one where `PerfectField` is used — is PROVEN there, by
reading mathlib's own criterion at the residue field.

What is left HERE is `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`
above: pure dimension theory, no perfectness, no regularity.  The paragraph
below headed "What blocks it in the pin" is retained as the historical record of
why this leaf was opened; item 3 and the closing paragraph are now DISCHARGED.

## Why this leaf is worth having stated here

Two open nodes of this development want exactly this bridge, and neither can be
closed without it:

* `Fermat/FLT/ModularCurve/X0.lean`'s
  `smoothOfRelativeDimension_of_gamma0GITPresentation`, where `B = A^G` is the
  ring of invariants of the Katz–Mazur rigidified moduli scheme and the whole
  point of the GIT presentation is that the coarse space is `Spec B`;
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`'s
  `smoothOfRelativeDimension_one_fromNormalization`, which is the *scheme* form
  of the same statement (normal + dimension one + perfect base ⟹ smooth) and is
  described there as "the deepest" of that file's leaves.

Proving it once here serves both.  A consumer of the scheme form can obtain it
from this one on an affine cover; the two are deliberately not merged in this
release because `CurveCompactification.lean` has a different owner.

## What blocks it in the pin, checked 2026-07-27 (now localised in the two leaves)

Mathlib has all three ingredients and no link between them.

1. `IsRegularRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), with
   `[IsDedekindDomain R] : IsRegularRing R` — so the dimension-one case of the
   hypothesis is available from normality for free.
2. `Algebra.Smooth`, `Algebra.smoothLocus`, and the local Jacobian criterion
   `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
   (`Mathlib/RingTheory/Smooth/Local.lean`).
3. `Algebra.FormallySmooth.of_perfectField`
   (`Mathlib/RingTheory/Smooth/Field.lean`), which gives formal smoothness of a
   *field* extension essentially of finite type over a perfect field — i.e. the
   statement at the GENERIC point only.  That is also as far as mathlib's own
   `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` and
   `Scheme.Hom.dense_smoothLocus_of_perfectField` get: the smooth locus is dense,
   never all of `X`.

*The check that would refute this*: `grep -rn "IsRegularRing"` over
`Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/` returning anything
— at this pin it returns nothing in either.

The missing step is therefore smoothness at the CLOSED points, i.e. formal
smoothness of a regular local ring essentially of finite type over a perfect
field.  In characteristic zero every residue field is separable over the base,
so the Jacobian criterion of ingredient 2 applies once `dim_k m/m² = dim` is
converted into injectivity of `k ⊗ I/I² → k ⊗ Ω[P/K]`; that conversion is the
whole content and it is not in the pin.  That step, and it alone, is now the leaf
`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField`.

A *second* thing was missing and had not been noticed when this leaf was first
stated: mathlib's `SmoothOfRelativeDimension` is a statement about the RANK of
`Ω`, so identifying the relative dimension with `ringKrullDim` needs "dimension =
transcendence degree", which is also absent from the pin.  That reduces, by
Noether normalisation, to the second leaf
`ringKrullDim_eq_of_isIntegral_of_injective`.  The bridge between the two — that
the rank of `Ω` of a finitely generated field extension of a perfect field *is*
the transcendence degree — is proven above.

## Faithfulness

`IsDomain B` is load-bearing and must not be dropped: without it a regular ring
can have components of different dimensions (`B = K × K[x]`), `ringKrullDim B`
records only the largest, and no single relative dimension exists — the
statement would be false at the points of the small component.

`PerfectField K` is load-bearing too, and this is not a formalisation artefact.

**COUNTEREXAMPLE CORRECTED (2026-07-28).**  This paragraph used to cite the curve
`y ^ p = t * x ^ p + t` (`t ∈ k \ k ^ p`) as "regular and not smooth".  That
witness is INVALID: in characteristic `p`, `t * x ^ p + t = t * (x + 1) ^ p`, so
after `u = x + 1` the equation reads `y ^ p = t * u ^ p`, whose defining
polynomial lies in `𝔪 ²` at the `k`-rational point `u = y = 0` — the local ring
there has `dim_k 𝔪 / 𝔪 ² = 2` in dimension one, so the curve is NOT regular (its
integral closure is the strictly larger `k (t ^ (1 / p)) [u]`).  It is also not
geometrically reduced, being `(y - t ^ (1 / p) * (x + 1)) ^ p = 0` over `k̄`.

The correct witness is the classical **quasi-elliptic** curve, which exists only
in characteristics `2` and `3`: over `k = 𝔽₃ (t)` take `B = k [x, y] / (y ² - x ³ - t)`.
It is a finite-type domain of Krull dimension one, and it is REGULAR — in
characteristic `3` the partials are `∂ / ∂ y = 2 y` and `∂ / ∂ x = - 3 x ² = 0`, so
the only candidate singular point is `y = 0`, `x ³ = - t`, a single closed point
with residue field `k (t ^ (1 / 3))`, where the maximal ideal `(y, x ³ + t)` equals
`(y)` because `x ³ + t = y ²`; a one-dimensional local ring with principal maximal
ideal is a DVR.  It is NOT smooth there: over `k̄`, `x ³ + t = (x + t ^ (1 / 3)) ³`,
so the base change is the cuspidal cubic.  Machine-checked in `Magma`: genus `1`
over `𝔽₃ (t)`, genus `0` after the purely inseparable base change `t = s ³`, a drop
of `(p - 1) / 2` as Tate's genus-change theorem permits at `p = 3`.

`ℚ` is perfect, so the modular application is unaffected. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) :=
  haveI := Algebra.Smooth.of_isRegularRing_of_perfectField K B
  smoothOfRelativeDimension_specMap_algebraMap_of_smooth K B n hdim

end AlgebraicGeometry
