/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Smooth morphisms are geometrically reduced

A smooth morphism of schemes is geometrically reduced: every base change of it
to a field has reduced total space.  This is the scheme-theoretic packaging of
the single classical fact

    a scheme smooth over a field is reduced

and it is **absent from the mathlib pin** — see the audit in the docstring of
`Algebra.Smooth.isReduced_of_isField` below, which is the one open leaf of this
file.

## Main results

* `Algebra.Smooth.isReduced_of_isField` — *(open leaf)* a smooth algebra over a
  field is reduced.  This is the entire mathematical content.
* `RingHom.Smooth.isReduced_of_isField` — the `RingHom` restatement.
* `AlgebraicGeometry.isReduced_of_smooth_over_field` — a scheme smooth over a
  field is reduced (proven from the leaf by an affine cover).
* `AlgebraicGeometry.GeometricallyReduced.of_smooth` — `Smooth f →
  GeometricallyReduced f` (proven from the previous item, since `Smooth` is
  stable under base change).

## Why this file exists

`GeometricallyReduced` is the hypothesis mathlib's
`AlgebraicGeometry/Geometrically/Reduced.lean` asks for in

    instance [GeometricallyReduced g] [Flat g] [IsReduced X]
      [IsLocallyNoetherian X] : IsReduced (pullback f g)

which is how reducedness of an iterated fibre product is obtained.  Mathlib
defines the class and proves it stable under base change, but **nothing in
mathlib ever instantiates it** except from itself; in particular there is no
route from smoothness.  Supplying that route once, in this generality, is
strictly less work than any parochial substitute, and it is immediately
reusable: all the base-change instances downstream of `GeometricallyReduced`
come for free.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

/-- **A smooth algebra over a field is reduced** (sorry leaf — a general gap in
the mathlib pin, with no elliptic-curve or even scheme-theoretic content).

TRUE and classical: a smooth `K`-algebra is regular (Jacobian criterion), and a
regular ring is reduced.  Both halves are missing here, and this is the whole
mathematical content of `AlgebraicGeometry.GeometricallyReduced.of_smooth`.

## ABSENCE AUDIT (2026-07-27, and the checks that would refute it)

Each bullet names the grep that refutes it, so the next owner re-runs a command
rather than a survey.

* `grep -rn 'IsReduced\|IsRegularLocalRing\|IsRegularRing\|IsDomain'
  Mathlib/RingTheory/Smooth/ Mathlib/RingTheory/Etale/` is **empty**.  So no
  file in the smooth/étale ring-theory development says anything at all about
  reducedness, regularity or domains.  In particular
  `RingTheory/Smooth/Local.lean` contains only the three
  `FormallySmooth.iff_injective_*` cotangent criteria, and
  `RingTheory/Smooth/StandardSmooth.lean` and `StandardSmoothCotangent.lean`
  prove freeness of `Ω` and vanishing of `H¹` of the cotangent complex, never a
  ring-theoretic property of the algebra.
* `grep -rln 'IsRegularLocalRing\|IsRegularRing' Mathlib/` returns exactly two
  files, `RingTheory/RegularLocalRing/{Defs,Polynomial}.lean`.  That development
  has `IsRegularLocalRing`, `IsRegularRing`, the DVR and Dedekind instances, and
  `MvPolynomial.isRegularRing_of_isRegularRing` — but **no `IsRegularLocalRing →
  IsDomain`** and no connection to smoothness or formal smoothness whatsoever.
  So even "smooth ⟹ regular" would not finish the job at this pin.
* There is **no perfect-field shortcut**, although the base here is `ℚ`.
  `Mathlib/RingTheory/Smooth/Field.lean` runs the *other* way: it proves
  separably generated field extensions are formally smooth
  (`Algebra.FormallySmooth.of_perfectField`), never that a formally smooth
  algebra is reduced.  And `PerfectField` does not occur in
  `RingTheory/Nilpotent/GeometricallyReduced.lean` or in any
  `AlgebraicGeometry/Geometrically/*.lean`, so the characteristic-zero
  identification of "reduced" with "geometrically reduced" is unavailable too.
* The converse direction *is* present, which is why a search can look
  deceptively successful: `AlgebraicGeometry/Group/Smooth.lean` proves
  `smooth_of_grpObj [GeometricallyReduced f] : Smooth f` (Cartier).  That is
  Cartier's theorem, and it consumes exactly the hypothesis this file produces;
  it cannot be run backwards.

## WHY IT IS NOT SOFT — do not look for a lifting-property proof

Formal smoothness alone does not visibly force reducedness, and the obvious
attempt fails in a way worth recording, because it is the first thing anyone
tries.  Let `N` be the nilradical (nilpotent, as `A` is noetherian) and apply
the lifting property to `B = A`, `J = N`: it produces a `K`-algebra
endomorphism `σ : A → A` with `π ∘ σ = π`, i.e. `σ ≡ id (mod N)`.  Nothing
about that contradicts `N ≠ 0`.  The content really does sit in the Jacobian
criterion — a standard-smooth presentation `K[x₁…x_n] ⧸ (f₁…f_c)` with an
invertible `c × c` Jacobian minor — via the fact that `f₁, …, f_c` is then a
regular sequence.  That is genuinely new commutative algebra at this pin.

## ROUTE, for whoever takes this leaf

1. Reduce to the local case (`IsReduced` is a local property).
2. Get a standard-smooth presentation.  `Algebra.Smooth → Locally
   IsStandardSmooth` is available as
   `RingHom.smooth_iff_locally_isStandardSmooth`, so this step is *not* a gap.
3. The genuinely missing step is the Jacobian criterion proper: the `c`
   equations of a submersive presentation form a regular sequence, hence the
   quotient is a complete intersection in a regular ring, hence regular, hence
   a domain locally.  Mathlib has `SubmersivePresentation` and
   `Extension.H1Cotangent` vanishing (`StandardSmoothCotangent.lean`) as
   inputs, and `MvPolynomial.isRegularRing_of_isRegularRing` for the ambient
   ring; what is absent is any bridge from those to `IsRegularLocalRing`, and
   `IsRegularLocalRing → IsDomain` on top of it. -/
theorem Algebra.Smooth.isReduced_of_isField {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hR : IsField R) [Algebra.Smooth R S] : IsReduced S :=
  sorry

/-- **A smooth ring homomorphism out of a field has reduced target** — the
`RingHom` restatement of `Algebra.Smooth.isReduced_of_isField`, which is the
shape the scheme-theoretic `HasRingHomProperty` API produces. -/
theorem RingHom.Smooth.isReduced_of_isField {R S : Type u} [CommRing R] [CommRing S]
    {φ : R →+* S} (hR : IsField R) (hφ : φ.Smooth) : IsReduced S := by
  letI := φ.toAlgebra
  haveI : Algebra.Smooth R S := hφ
  exact Algebra.Smooth.isReduced_of_isField hR

namespace AlgebraicGeometry

/-- **A scheme smooth over a field is reduced.**

PROVEN from `RingHom.Smooth.isReduced_of_isField` by an affine cover: each
`X.affineCover.X i` is affine, the composite `X.affineCover.f i ≫ f` is smooth
(open immersions are smooth of relative dimension `0`), and
`HasRingHomProperty.appTop` turns that into `RingHom.Smooth` of the map
`Γ(Spec K, ⊤) ⟶ Γ(X.affineCover.X i, ⊤)`.  The source of that map is a field by
transport along `Scheme.ΓSpecIso`, so the leaf applies and gives the ring-level
reducedness, whence `isReduced_of_isAffine_isReduced` and
`IsReduced.of_openCover`. -/
theorem isReduced_of_smooth_over_field {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] : IsReduced X := by
  haveI hK : _root_.IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  haveI : ∀ i, IsReduced (X.affineCover.X i) := by
    intro i
    haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      RingHom.Smooth.isReduced_of_isField hK
        (HasRingHomProperty.appTop (@Smooth) (X.affineCover.f i ≫ f) inferInstance)
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ X.affineCover

/-- **Smooth morphisms are geometrically reduced.**

PROVEN from `isReduced_of_smooth_over_field`: `geometrically IsReduced f` asks,
for every field `K`, every `y : Spec K ⟶ Y` and every pullback square over
`(f, y)`, that the total space be reduced — and the second leg of such a square
is a base change of `f`, hence smooth, hence has reduced source.

This is not registered as an `instance`: mathlib already carries the converse
`AlgebraicGeometry.smooth_of_grpObj [GeometricallyReduced f] : Smooth f` for
group schemes, and keeping both directions out of instance search avoids any
risk of a loop. -/
theorem GeometricallyReduced.of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f where
  geometrically_isReduced := by
    intro K _ y Z fst snd h
    haveI : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    exact isReduced_of_smooth_over_field snd

end AlgebraicGeometry
