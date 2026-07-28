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
  Krull dimension (**PROVEN 2026-07-28**; no perfectness, no regularity, pure
  dimension theory), over `Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth`
  and the one leaf below.
* `Algebra.linearIndepOn_pow_of_formallySmooth` — **the only leaf left in this
  file**: MacLane's criterion for a formally smooth field extension (Matsumura
  Thm. 26.9, Stacks `07P2`+`030W`).  It is a statement about FIELDS ONLY, with no
  finiteness, no schemes and no differentials in it; mathlib proves the converse
  implication and flags this one as its own `TODO`.
* `ringKrullDim_eq_of_isIntegral_of_injective` — an injective integral ring
  extension preserves the Krull dimension, Stacks `00OJ`+`00OK` (**PROVEN
  2026-07-28**, by an `RelSeries.inductionOn'` lift of chains — this is the
  arbitrary-length going-up theorem mathlib records as a TODO of its own).

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
public import Mathlib.RingTheory.Ideal.GoingUp
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

The scheme section at the end is now sorry-free: everything there is *assembled* with
no further mathematical content.  The one remaining leaf of the whole file is
`Algebra.linearIndepOn_pow_of_formallySmooth` below — MacLane's criterion for a
formally smooth field extension — which is what removes `PerfectField` from the
dimension theory.  (`ringKrullDim_eq_of_isIntegral_of_injective` and
`FormallySmooth.of_isRegularRing_of_perfectField`, the earlier leaves here, were
PROVEN 2026-07-27/28.)
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
/-- **The rank of the module of Kähler differentials of a SEPARABLY GENERATED field
extension is its transcendence degree** (PROVEN 2026-07-27 for a perfect base;
generalised 2026-07-28 to take the separating transcendence basis as a hypothesis,
so that the perfect-field and the formally-smooth cases share one proof).

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

Separable generation is load-bearing and is used exactly once, for the third arrow:
without it that arrow can fail to be separable and the rank strictly exceeds the
transcendence degree (e.g. `L = K(t^{1/p})` over `K = 𝔽_p(t)`, where `trdeg = 0`
but `Ω[L⁄K]` is one-dimensional). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_exists_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (h : ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set L)) L) :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L := by
  obtain ⟨s, hs, hsep⟩ := h
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

/-- **The rank of the module of Kähler differentials of a finitely generated field
extension of a perfect field is its transcendence degree** (PROVEN 2026-07-27; since
2026-07-28 a one-line corollary of the separably-generated form above, over
mathlib's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_perfectField
    (K L : Type u) [Field K] [PerfectField K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L :=
  rank_kaehlerDifferential_eq_trdeg_of_exists_isSeparable K L
    (exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L)

/-! #### **MacLane's criterion for a formally smooth field extension** (sorry leaf,
opened 2026-07-28).

This is the ONE piece of mathematics that
`smoothOfRelativeDimension_specMap_algebraMap_of_smooth` needs and that neither
mathlib, nor `~/cs/FLT`, nor this project supplies: the direction

> a formally smooth field extension is *separable* in MacLane's sense

of Matsumura *Commutative Ring Theory* Thm. 26.9 (= Stacks `07P2` "`K → L` formally
smooth ⟺ `L/K` separable", combined with `030W` "(2) ⇒ (1)").

## What mathlib has, checked 2026-07-28

`Mathlib/FieldTheory/SeparablyGenerated.lean` proves exactly the CONVERSE half of the
TFAE it advertises, and says so in its own header ("Main result: (2) ⇒ (1)") and in a
`TODO: show that this is an if and only if` on
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`.
Its hypothesis is precisely the statement below, so the leaf plugs straight into it —
that is why the leaf is stated in the linear-independence form rather than as
"separably generated". `Mathlib/RingTheory/Smooth/Field.lean` has only the other
direction as well (`FormallySmooth.of_algebraicIndependent_of_isSeparable`).

*The check that would refute this*: `grep -rn "FormallySmooth" Mathlib/FieldTheory/`
returning anything — at this pin it is empty.

## The intended route, and the two sub-gaps it opens

1. **Formal smoothness gives extension of derivations.** For an `L`-module `M` and a
   derivation `D : K → M` over the prime field, the trivial square-zero extension
   `C = L ⊕ M` becomes a `K`-algebra by `k ↦ (k, D k)`, and `C ↠ L` is then a
   `K`-algebra surjection with square-zero kernel.  Lifting `id : L → L` along it is
   exactly a derivation `L → M` restricting to `D` on `K`.
2. **`p`-independence detects `K ^ p`.** If `a ∈ K \ K ^ p` there is a derivation
   `D : K → K` with `D a ≠ 0` (extend `{a}` to a `p`-basis).  Mathlib has **no**
   `p`-basis theory at this pin (`grep -rn "pBasis" Mathlib/` is empty), so this is
   the larger of the two sub-gaps.

Given both: take a relation `∑ aᵢ xᵢ ^ p = 0` with `aᵢ ∈ K` not all zero and with
MINIMAL support, normalised so that `a₁ = 1`.  Any derivation `D' : L → L` kills every
`xᵢ ^ p`, so `0 = D' (∑ aᵢ xᵢ ^ p) = ∑ (D aᵢ) xᵢ ^ p` is a relation of strictly smaller
support (its first coefficient is `D 1 = 0`), whence `D aᵢ = 0` for all `i` and all
`D`, whence every `aᵢ = cᵢ ^ p` by 2.  Then `(∑ cᵢ xᵢ) ^ p = ∑ aᵢ xᵢ ^ p = 0`, so
`∑ cᵢ xᵢ = 0` with `c₁ = 1`, contradicting the `K`-linear independence of the `xᵢ`.

## Faithfulness

`Algebra.FormallySmooth K L` is load-bearing and no finiteness hypothesis is needed:
Matsumura 26.9 is an equivalence for arbitrary field extensions.  The statement is NOT
vacuous — over an imperfect `K` it genuinely fails without smoothness, e.g.
`K = 𝔽_p(t)`, `L = K(t ^ (1 / p))`, where `{1, t ^ (1 / p)}` is `K`-linearly
independent while its `p`-th powers `{1, t}` are not. -/
theorem linearIndepOn_pow_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.FormallySmooth K L]
    (p : ℕ) (hp : p.Prime) [ExpChar K p] (s : Finset L)
    (hs : LinearIndepOn K _root_.id (s : Set L)) :
    LinearIndepOn K (· ^ p) (s : Set L) :=
  sorry

/-- **A formally smooth field extension essentially of finite type is separably
generated** (PROVEN 2026-07-28 over the leaf above).

Characteristic zero is free: a field of characteristic zero is perfect
(`PerfectField.ofCharZero`), so mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField` applies and formal
smoothness is not used at all.  In characteristic `p` the leaf above supplies the
hypothesis of
`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`
verbatim. -/
theorem exists_isTranscendenceBasis_and_isSeparable_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] [Algebra.FormallySmooth K L] :
    ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set L)) L := by
  rcases CharP.exists' K with h0 | ⟨p, hp, hpK⟩
  · haveI := h0
    exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  · haveI := hpK
    haveI : ExpChar K p := .prime hp.out
    haveI : CharP L p := .of_ringHom_of_ne_zero (algebraMap K L) p hp.out.ne_zero
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (fun s hs ↦ linearIndepOn_pow_of_formallySmooth K L p hp.out s hs)

/-- **The rank of `Ω` of a formally smooth field extension is its transcendence
degree** (PROVEN 2026-07-28).  The imperfect-base analogue of
`rank_kaehlerDifferential_eq_trdeg_of_perfectField`, and the reason the leaf above is
worth having: it is what removes `PerfectField` from the dimension theory. -/
theorem rank_kaehlerDifferential_eq_trdeg_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] [Algebra.FormallySmooth K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L :=
  rank_kaehlerDifferential_eq_trdeg_of_exists_isSeparable K L
    (exists_isTranscendenceBasis_and_isSeparable_of_formallySmooth K L)

end Algebra

/-- **An injective integral ring extension preserves the Krull dimension**
(opened as a sorry leaf 2026-07-27; **PROVEN 2026-07-28**).

Stacks `00OK` (`dim S ≤ dim R`, by incomparability) together with `00OJ`
(`dim R ≤ dim S`, by lying over and going up).  It is stated in full mathlib
generality rather than for the finite-type case that needs it, because that is
what it is.  Mathlib flags the chain form of going-up as a TODO of its own — see
below — so this fills that gap.

## The proof

Both halves of the argument are present in the pin as statements about a *single*
prime; the content added here is the passage to chains.

* `≤` (Stacks `00OK`): incomparability, `Ideal.IsIntegral.comap_lt_comap` — for
  `I < J` primes of `S`, `comap I < comap J`.  So `PrimeSpectrum.comap
  (algebraMap R S)` is strictly monotone and `Order.krullDim_le_of_strictMono`
  gives `dim S ≤ dim R` in one line.  (Injectivity is not needed here.)
* `≥` (Stacks `00OJ`): every `LTSeries (PrimeSpectrum R)` is lifted to an
  `LTSeries (PrimeSpectrum S)` of the *same length* lying over it, by
  `RelSeries.inductionOn'` — the induction principle that builds a series from a
  singleton by repeated `snoc`, which is exactly the shape of a going-up
  argument.  The singleton case is lying over,
  `Ideal.exists_ideal_over_prime_of_isIntegral` applied with `I = ⊥` (this is
  where injectivity enters, as `RingHom.ker (algebraMap R S) = ⊥ ≤ P`); the
  `snoc` case is going up,
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`, which produces
  `Q ≥ q.last` over the next prime `x` of the chain.  Strictness of the new step
  is *not* given by that lemma and has to be argued: `q.last ≤ Q` and the two
  contract to `p.last < x`, so they cannot be equal.  Then
  `Order.LTSeries.length_le_krullDim` on the lifted series bounds each length in
  the supremum defining `krullDim (PrimeSpectrum R)`.

Mathlib asks for precisely this: the comment above
`exists_ideal_over_prime_of_isIntegral_of_isPrime` reads *"TODO: Version of
going-up theorem with arbitrary length chains (by induction on this)?  Not sure
how best to write an ascending chain in Lean"*.  The answer is `LTSeries`, and
`RelSeries.inductionOn'` is the induction it asks for.

A dead end worth recording so it is not re-explored: the `≥` direction does **not**
follow from `Order.krullDim_le_of_strictComono_and_surj` even though
`Algebra.IsIntegral.comap_surjective` supplies its surjectivity hypothesis, because
`PrimeSpectrum.comap` is not strictly comonotone.  Counterexample: `R = k[x]`,
`S = k[x] × k[x]`, `q₁ = 0 × k[x]`, `q₂ = k[x] × (x)`; then
`comap q₁ = (0) < (x) = comap q₂` while `q₁ ⊄ q₂` (as `(0,1) ∈ q₁ \ q₂`).  So the
lifted chain really has to be built step by step, each prime chosen above the
previous one — which is what the `snoc` case does.

## Faithfulness

Injectivity is load-bearing: without it take `R` any ring and `S = 0`, which is
integral over `R` with `ringKrullDim S = ⊥ ≠ ringKrullDim R`.  It is used exactly
once, in the lying-over step. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp h
  refine le_antisymm ?_ ?_
  · -- `00OK`: incomparability makes `comap` strictly monotone.
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro x y hxy
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
    exact Ideal.IsIntegral.comap_lt_comap hxy
  · -- `00OJ`: lying over and going up lift a chain of `R` to a chain of `S` of the same length.
    have key : ∀ p : LTSeries (PrimeSpectrum R), ∃ q : LTSeries (PrimeSpectrum S),
        q.length = p.length ∧ PrimeSpectrum.comap (algebraMap R S) q.last = p.last := by
      intro p
      induction p using RelSeries.inductionOn' with
      | singleton x =>
          -- lying over
          obtain ⟨Q, -, hQp, hQc⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal S)
              (by simp [← RingHom.ker_eq_comap_bot, hker])
          refine ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, ?_⟩
          rw [RelSeries.last_singleton]
          exact PrimeSpectrum.ext hQc
      | snoc p x hx ih =>
          -- going up, one step
          obtain ⟨q, hlen, hcomap⟩ := ih
          have hlt : p.last.asIdeal < x.asIdeal := PrimeSpectrum.asIdeal_lt_asIdeal _ _ |>.mpr hx
          have hle : q.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
            have : (PrimeSpectrum.comap (algebraMap R S) q.last).asIdeal ≤ x.asIdeal := by
              rw [hcomap]; exact hlt.le
            exact this
          obtain ⟨Q, hQge, hQp, hQc⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal q.last.asIdeal hle
          -- the new prime is *strictly* above the old one, because their contractions differ
          have hrel : q.last < (⟨Q, hQp⟩ : PrimeSpectrum S) := by
            rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
            refine lt_of_le_of_ne hQge fun hEq => ?_
            have h1 : (PrimeSpectrum.comap (algebraMap R S) q.last).asIdeal = x.asIdeal := by
              show q.last.asIdeal.comap (algebraMap R S) = x.asIdeal
              rw [hEq]; exact hQc
            rw [hcomap] at h1
            exact absurd h1 hlt.ne
          refine ⟨q.snoc ⟨Q, hQp⟩ hrel, by simp [hlen], ?_⟩
          simp only [RelSeries.last_snoc]
          exact PrimeSpectrum.ext hQc
    rw [ringKrullDim, ringKrullDim, Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨q, hlen, -⟩ := key p
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim q

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

/-- **The module of Kähler differentials of a SMOOTH finite-type domain over ANY field
has rank the Krull dimension** (PROVEN 2026-07-28).

The imperfect-base analogue of `rank_kaehlerDifferential_eq_of_ringKrullDim`, and the
whole commutative-algebra content of
`smoothOfRelativeDimension_specMap_algebraMap_of_smooth`.  Same two steps as there:
`Frac B` is a localization of `B`, hence formally étale over it, so `Ω` base-changes
and the rank is read at the generic point; and there the rank is the transcendence
degree, which is the Krull dimension.  What replaces `PerfectField K` is that
`Frac B` is *formally smooth* over `K` — it is a localization of the smooth algebra
`B` — so `rank_kaehlerDifferential_eq_trdeg_of_formallySmooth` applies. -/
theorem rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.Smooth K B]
    (n : ℕ) (hdim : ringKrullDim B = n) :
    Module.rank B Ω[B⁄K] = n := by
  haveI : Algebra.FormallyEtale B (FractionRing B) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType B (FractionRing B) := .of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType K (FractionRing B) := .comp K B _
  haveI : Algebra.FormallySmooth K (FractionRing B) := .comp K B _
  haveI : FaithfulSMul B (FractionRing B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B _)
  rw [← (KaehlerDifferential.isBaseChange_of_formallyEtale K B (FractionRing B)).rank_eq,
    rank_kaehlerDifferential_eq_trdeg_of_formallySmooth K (FractionRing B),
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
(**PROVEN 2026-07-28**; opened as a sorry leaf earlier the same day as the residue of
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
dropped — see the faithfulness note on the consumer below.

## How it was proven

`HasRingHomProperty.Spec_iff` turns the goal into the ring-level property
`Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap K B)`, i.e. a cover of
`Spec B` by basic opens on each of which `B_t` is standard smooth of relative
dimension `n`.  The cover is
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`, **with `0` removed from it** —
`Localization.Away 0` is the zero ring, where no relative dimension is defined; the
removal is free because `0` contributes nothing to `Ideal.span`.

On each chart `IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` reduces
the relative dimension to `Module.rank B_t Ω[B_t⁄K] = n`.  That rank does not depend
on the chart: `B → B_t` is a localization, hence formally étale, so `Ω`
base-changes and `IsBaseChange.rank_eq` reads the rank back unchanged as
`Module.rank B Ω[B⁄K]` — which is `n` by
`Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth`.  This is exactly the
"`IsDomain B` is what makes the rank constant" step above: it enters as
`NoZeroDivisors B_t` and `FaithfulSMul B B_t`, both of which need `t ≠ 0`. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) := by
  have hrank : Module.rank B Ω[B⁄K] = n :=
    Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth K B n hdim
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  show RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap K B)
  obtain ⟨s, hs, hss⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K B
  refine ⟨s \ {0}, ?_, ?_⟩
  · -- dropping `0` from the cover changes nothing: it is not a generator of anything
    refine le_antisymm le_top ?_
    rw [← hs, Ideal.span_le]
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    · exact Ideal.subset_span ⟨hx, hx0⟩
  · rintro t ⟨ht, ht0'⟩
    have ht0 : t ≠ 0 := by simpa using ht0'
    haveI : Algebra.IsStandardSmooth K (Localization.Away t) := hss t ht
    haveI : IsDomain (Localization.Away t) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht0)
    haveI : FaithfulSMul B (Localization.Away t) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr
        (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht0))
    haveI : Algebra.FormallyEtale B (Localization.Away t) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
    show RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap B (Localization.Away t)).comp (algebraMap K B))
    rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n,
      (KaehlerDifferential.isBaseChange_of_formallyEtale K B (Localization.Away t)).rank_eq,
      hrank]

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

What was left HERE — `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`
above, pure dimension theory with no perfectness and no regularity — is PROVEN as
of 2026-07-28, modulo the single field-theoretic leaf
`Algebra.linearIndepOn_pow_of_formallySmooth`.  The paragraph below headed "What
blocks it in the pin" is retained as the historical record of why this leaf was
opened; item 3 and the closing paragraph are now DISCHARGED.

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
