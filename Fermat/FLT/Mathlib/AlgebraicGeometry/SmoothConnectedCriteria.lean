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

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

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
named leaf, `Algebra.injective_cotangentComplexBaseChange_of_isRegularLocalRing`
— the injectivity in the local Jacobian criterion — whose classical two-step
proof is written out there.

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

## What blocks it in the pin, checked 2026-07-27

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
whole content and it is not in the pin.

## Faithfulness

`IsDomain B` is load-bearing and must not be dropped: without it a regular ring
can have components of different dimensions (`B = K × K[x]`), `ringKrullDim B`
records only the largest, and no single relative dimension exists — the
statement would be false at the points of the small component.

`PerfectField K` is load-bearing too, and this is not a formalisation artefact:
over an imperfect field of characteristic `p` the curve `y ^ p = t * x ^ p + t`
(`t ∈ k \ k ^ p`) is regular and not smooth.  `ℚ` is perfect, so the modular
application is unaffected. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) :=
  haveI := Algebra.Smooth.of_isRegularRing_of_perfectField K B
  smoothOfRelativeDimension_specMap_algebraMap_of_smooth K B n hdim

end AlgebraicGeometry
