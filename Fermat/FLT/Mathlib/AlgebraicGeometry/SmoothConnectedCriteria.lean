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
  off the Krull dimension (LEAF; see its docstring).

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

/-- **Regular + finite type over a perfect field ⟹ smooth of relative dimension
the Krull dimension** (sorry leaf, opened 2026-07-27).

This is the ring form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), together with the identification of the relative dimension: for
an *integral* finite-type algebra over a field the local dimensions are all
equal to `ringKrullDim`, so a single `n` governs every point.

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
  sorry

end AlgebraicGeometry
