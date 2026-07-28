/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# The SECOND Bosma–Lenstra addition law, over an arbitrary commutative ring

Mathlib's `WeierstrassCurve.Projective.addXYZ` is the Bosma–Lenstra addition law
of the line `Z = 0`; this module supplies the law of the line `Y = 0`
(`add2X`, `add2Y`, `add2Z`, `add2XYZ`) together with what makes the PAIR of laws
complete: at every pair of points at least one of the two is non-degenerate.

## Companion module — and why it is a SIBLING, not a parent

The ring-level statement for the FIRST law,
`WeierstrassCurve.Projective.equation_addXYZ`
(`W.Equation P → W.Equation Q → W.Equation (W.addXYZ P Q)` over any
`[CommRing R]`), lives in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveEquationAdd.lean`.

It was SPLIT OUT of this file at the release-10 integration (2026-07-28) and
**nothing here uses it**.  Elaboration is single-threaded per file, and this
file carried two independent multi-minute `linear_combination`/`ring1`
normalisations — `equation_addXYZ` and
`add2Y_neg_left_ne_zero_of_dblZ_eq_zero` below — so they were paid in SERIES on
one core, **4173 s together**, which put this file at the head of the whole
build's critical path.  As two sibling modules, both imported by their single
consumer `ModularCurve/EllipticScheme.lean`, they elaborate concurrently.

**So do not merge the two files back together, and do not make either import
the other.**  Their being siblings is the point.

## Why the ring-level statements are needed at all

`Fermat.ProjCoords` (`Fermat/FLT/ModularCurve/EllipticScheme.lean`) is a
trivialised `Proj`-coordinate datum over an arbitrary `Γ(X, ⊤)`, where `P z`
is emphatically not a unit — that is the whole point of using it to glue the
group law of the projective Weierstrass model.  So the field-level statements
in the pin cannot be used, and no base change rescues them.
-/

@[expose] public section

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve R} {P Q : Fin 3 → R}

/-! ## The SECOND Bosma-Lenstra addition law -- the line `Y = 0`

Bosma-Lenstra (*Complete systems of two addition laws for elliptic curves*,
J. Number Theory **53** (1995), Theorem 2) give a 1-to-1 correspondence between
LINES in `P²` and addition laws of bidegree `(2, 2)` on a Weierstrass model, under
which `(P, Q)` is exceptional for the law of the line `L` exactly when `P - Q`
lies on `L`.  Mathlib's `addXYZ` is the law of the line `Z = 0`, which meets the
curve only at `O = [0 : 1 : 0]` (with multiplicity `3`): its exceptional set is
the DIAGONAL, which is what `addXYZ_self` records.

The law defined here is the law of the line `Y = 0`.  Since `O` has `Y = 1 ≠ 0`,
the two lines meet the curve in DISJOINT sets, so the two laws form a COMPLETE
SYSTEM: at every geometric point of `E × E` at least one of them is
non-degenerate.  That is the only reason a second law is needed anywhere in this
development, and it is exactly what `Fermat.exists_projMulOfCoords` consumes to
glue the group law -- together with the two special values proved below, which
are the halves of `hunit` and `hinv` that the standard law cannot supply.

## Where these polynomials come from, and how to regenerate them

They were COMPUTED, not copied: the published closed forms (Renes-Costello-Batina,
*Complete addition formulas for prime order elliptic curves*, §3) are for the
SHORT Weierstrass model `y² = x³ + ax + b`, and no source to hand carries the
general `a₁, …, a₆` form.  The derivation is three lines of divisor bookkeeping:

* `A_L / A_{Z=0}` is the function `ℓ / z` evaluated at `P - Q`;
* a representative of `P - Q` is `addXYZ P (neg Q)`, so for `L : Y = 0` that
  ratio is `addY P (neg Q) / addZ P (neg Q)`;
* hence `add2• P Q * addZ P (neg Q) = add• P Q * addY P (neg Q)` modulo
  `(W(P), W(Q))`, and the left factor is recovered by a `lift` in `Singular`.

Concretely, in `ℚ[X₁,Y₁,Z₁,X₂,Y₂,Z₂,a₁,a₂,a₃,a₄,a₆]` with
`nY₂ := -Y₂ - a₁*X₂ - a₃*Z₂`, `D := addZ P (X₂, nY₂, Z₂)` and
`N := addY P (X₂, nY₂, Z₂)`:

    ideal J = D, W1, W2;  matrix T = lift(J, addX*N);  T[1,1]

is `add2X`, and likewise for `Y` and `Z`.  The output was checked to be
bihomogeneous of bidegree `(2, 2)`, to satisfy the Weierstrass equation modulo
`(W(P), W(Q))`, and to be proportional to `addXYZ` modulo the same ideal; and
specialising `a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b` reproduces Renes-Costello-
Batina's published formulas exactly, up to the global sign `-1` (irrelevant
projectively).  The transcription into Lean below was checked mechanically, by
parsing it back into `Singular` and differencing against the computed output.

## Completeness is NOT a small certificate -- do not go looking for one

The saturation exponent was probed: `(X₁,Y₁,Z₁)ⁿ * (X₂,Y₂,Z₂)ⁿ` is NOT contained
in `(addX, addY, addZ, add2X, add2Y, add2Z, W(P), W(Q))` for any `n ≤ 6`, even
though the variety of that ideal is exactly the two irrelevant cones (its `dim`
is `7`, which is the right answer, so completeness itself is confirmed).  A
ring-level "the six forms generate the unit ideal" statement would therefore need
one `linear_combination` per monomial pair -- hundreds of them.  The
non-degeneracy dichotomy the gluing actually consumes is stated over a FIELD in
`EllipticScheme.lean`, where it is a finite case analysis.
-/

variable (W') in
/-- The `X`-coordinate of the second Bosma-Lenstra addition law, i.e. the law of
the line `Y = 0`.  See the section docstring for the derivation. -/
def add2X (P Q : Fin 3 → R) : R :=
  P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 + P 2 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₃ ^ 3
    - P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄
    - P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ ^ 2 * W'.a₄ + P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 3 * W'.a₆
    + P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₆ + P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ ^ 2 * W'.a₃
    + 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₃ ^ 2 + P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ ^ 2
    + P 2 ^ 2 * Q 1 * Q 2 * W'.a₂ * W'.a₃ ^ 2 + P 1 * P 2 * Q 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2
    + P 2 ^ 2 * Q 0 * Q 2 * W'.a₃ ^ 3 + P 0 * P 2 * Q 2 ^ 2 * W'.a₃ ^ 3
    - P 2 ^ 2 * Q 1 * Q 2 * W'.a₁ * W'.a₃ * W'.a₄ - P 1 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄
    - P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₄ ^ 2 - P 2 ^ 2 * Q 2 ^ 2 * W'.a₃ * W'.a₄ ^ 2
    + P 2 ^ 2 * Q 1 * Q 2 * W'.a₁ ^ 2 * W'.a₆ + P 1 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₆
    + 4 * P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₆
    + 4 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₃ * W'.a₆ - P 0 * P 1 * Q 0 ^ 2 * W'.a₁ ^ 2
    + P 0 ^ 2 * Q 0 ^ 2 * W'.a₁ * W'.a₂ - P 1 * P 2 * Q 0 ^ 2 * W'.a₁ * W'.a₃
    + P 0 ^ 2 * Q 1 * Q 2 * W'.a₁ * W'.a₃ + P 0 * P 2 * Q 0 ^ 2 * W'.a₂ * W'.a₃
    + 2 * P 0 * P 2 * Q 1 * Q 2 * W'.a₃ ^ 2 + P 0 * P 1 * Q 2 ^ 2 * W'.a₃ ^ 2
    + P 0 * P 2 * Q 0 ^ 2 * W'.a₁ * W'.a₄ + 2 * P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₄
    + P 2 ^ 2 * Q 0 ^ 2 * W'.a₃ * W'.a₄ + 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₃ * W'.a₄
    - P 2 ^ 2 * Q 1 * Q 2 * W'.a₄ ^ 2 - P 1 * P 2 * Q 2 ^ 2 * W'.a₄ ^ 2
    + 6 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₆ + 3 * P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₆
    + 4 * P 2 ^ 2 * Q 1 * Q 2 * W'.a₂ * W'.a₆ + 4 * P 1 * P 2 * Q 2 ^ 2 * W'.a₂ * W'.a₆
    + 6 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₃ * W'.a₆ + 3 * P 0 * P 2 * Q 2 ^ 2 * W'.a₃ * W'.a₆
    - P 1 ^ 2 * Q 0 ^ 2 * W'.a₁ - 2 * P 0 * P 1 * Q 0 * Q 1 * W'.a₁ + P 0 * P 1 * Q 0 ^ 2 * W'.a₂
    + P 0 ^ 2 * Q 0 * Q 1 * W'.a₂ - 2 * P 1 * P 2 * Q 0 * Q 1 * W'.a₃
    - P 1 ^ 2 * Q 0 * Q 2 * W'.a₃ + P 1 * P 2 * Q 0 ^ 2 * W'.a₄
    + 2 * P 0 * P 2 * Q 0 * Q 1 * W'.a₄ + 2 * P 0 * P 1 * Q 0 * Q 2 * W'.a₄
    + P 0 ^ 2 * Q 1 * Q 2 * W'.a₄ + 3 * P 2 ^ 2 * Q 0 * Q 1 * W'.a₆
    + 6 * P 1 * P 2 * Q 0 * Q 2 * W'.a₆ + 6 * P 0 * P 2 * Q 1 * Q 2 * W'.a₆
    + 3 * P 0 * P 1 * Q 2 ^ 2 * W'.a₆ - P 1 ^ 2 * Q 0 * Q 1 - P 0 * P 1 * Q 1 ^ 2

variable (W') in
/-- The `Y`-coordinate of the second Bosma-Lenstra addition law. -/
def add2Y (P Q : Fin 3 → R) : R :=
  -P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2
    - P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ ^ 3
    + P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄
    + P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ - P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 4 * W'.a₆
    - P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₆
    - P 1 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2
    - P 2 ^ 2 * Q 0 * Q 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 - P 0 * P 2 * Q 2 ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2
    + P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ ^ 3 + P 2 ^ 2 * Q 2 ^ 2 * W'.a₃ ^ 4
    + P 1 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄
    + P 2 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
    + P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
    - P 2 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ + P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₄ ^ 2
    + 2 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 - P 1 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 3 * W'.a₆
    - P 2 ^ 2 * Q 0 * Q 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆
    - 5 * P 0 * P 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆
    - 4 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆
    - P 2 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆
    + 2 * P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₂ * W'.a₃
    - 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₂ * W'.a₃ ^ 2 - P 0 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2
    + P 1 * P 2 * Q 2 ^ 2 * W'.a₃ ^ 3 - P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ ^ 2 * W'.a₄
    + 4 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₃ * W'.a₄
    + 2 * P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ + 2 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₃ ^ 2 * W'.a₄
    + P 0 * P 2 * Q 2 ^ 2 * W'.a₃ ^ 2 * W'.a₄ + P 1 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₄ ^ 2
    + P 2 ^ 2 * Q 0 * Q 2 * W'.a₂ * W'.a₄ ^ 2 + P 0 * P 2 * Q 2 ^ 2 * W'.a₂ * W'.a₄ ^ 2
    + P 2 ^ 2 * Q 2 ^ 2 * W'.a₄ ^ 3 - 6 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ ^ 2 * W'.a₆
    - 3 * P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₆ - 4 * P 1 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₆
    - 4 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₂ ^ 2 * W'.a₆ - 4 * P 0 * P 2 * Q 2 ^ 2 * W'.a₂ ^ 2 * W'.a₆
    - 3 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₃ * W'.a₆
    + 3 * P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₆ + 6 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₃ ^ 2 * W'.a₆
    - 4 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₄ * W'.a₆ - P 0 * P 1 * Q 0 ^ 2 * W'.a₁ * W'.a₂
    + P 0 ^ 2 * Q 0 ^ 2 * W'.a₂ ^ 2 + P 1 * P 2 * Q 0 ^ 2 * W'.a₂ * W'.a₃
    + 2 * P 0 * P 1 * Q 0 * Q 2 * W'.a₂ * W'.a₃ - 3 * P 0 ^ 2 * Q 0 * Q 2 * W'.a₃ ^ 2
    - P 1 * P 2 * Q 0 ^ 2 * W'.a₁ * W'.a₄ - 2 * P 0 * P 1 * Q 0 * Q 2 * W'.a₁ * W'.a₄
    + P 0 * P 2 * Q 0 ^ 2 * W'.a₂ * W'.a₄ + P 0 ^ 2 * Q 0 * Q 2 * W'.a₂ * W'.a₄
    + 2 * P 1 * P 2 * Q 0 * Q 2 * W'.a₃ * W'.a₄ + P 0 * P 1 * Q 2 ^ 2 * W'.a₃ * W'.a₄
    + P 2 ^ 2 * Q 0 ^ 2 * W'.a₄ ^ 2 + 4 * P 0 * P 2 * Q 0 * Q 2 * W'.a₄ ^ 2
    + P 0 ^ 2 * Q 2 ^ 2 * W'.a₄ ^ 2 - 6 * P 1 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₆
    - 3 * P 0 * P 1 * Q 2 ^ 2 * W'.a₁ * W'.a₆ - 3 * P 2 ^ 2 * Q 0 ^ 2 * W'.a₂ * W'.a₆
    - 12 * P 0 * P 2 * Q 0 * Q 2 * W'.a₂ * W'.a₆ - 3 * P 0 ^ 2 * Q 2 ^ 2 * W'.a₂ * W'.a₆
    + 3 * P 1 * P 2 * Q 2 ^ 2 * W'.a₃ * W'.a₆ + 3 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₄ * W'.a₆
    + 3 * P 0 * P 2 * Q 2 ^ 2 * W'.a₄ * W'.a₆ + 9 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₆ ^ 2
    - P 1 ^ 2 * Q 0 * Q 1 * W'.a₁ + 3 * P 0 * P 1 * Q 0 ^ 2 * W'.a₃ - P 1 ^ 2 * Q 1 * Q 2 * W'.a₃
    - 3 * P 0 ^ 2 * Q 0 ^ 2 * W'.a₄ - 9 * P 0 * P 2 * Q 0 ^ 2 * W'.a₆
    - 9 * P 0 ^ 2 * Q 0 * Q 2 * W'.a₆ - P 1 ^ 2 * Q 1 ^ 2

variable (W') in
/-- The `Z`-coordinate of the second Bosma-Lenstra addition law. -/
def add2Z (P Q : Fin 3 → R) : R :=
  -P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ ^ 3 - 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ ^ 2 * W'.a₃
    - P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ - P 2 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₃ ^ 2
    - 2 * P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₃ ^ 2 - P 2 ^ 2 * Q 2 ^ 2 * W'.a₃ ^ 3
    - 2 * P 0 * P 1 * Q 0 * Q 2 * W'.a₁ ^ 2 - P 0 ^ 2 * Q 1 * Q 2 * W'.a₁ ^ 2
    - P 0 * P 2 * Q 0 ^ 2 * W'.a₁ * W'.a₂ - 2 * P 0 ^ 2 * Q 0 * Q 2 * W'.a₁ * W'.a₂
    - 2 * P 1 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₃ - 2 * P 0 * P 2 * Q 1 * Q 2 * W'.a₁ * W'.a₃
    - 2 * P 0 * P 1 * Q 2 ^ 2 * W'.a₁ * W'.a₃ - P 2 ^ 2 * Q 0 ^ 2 * W'.a₂ * W'.a₃
    - 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₂ * W'.a₃ - P 2 ^ 2 * Q 1 * Q 2 * W'.a₃ ^ 2
    - 2 * P 1 * P 2 * Q 2 ^ 2 * W'.a₃ ^ 2 - 2 * P 0 * P 2 * Q 0 * Q 2 * W'.a₁ * W'.a₄
    - P 0 ^ 2 * Q 2 ^ 2 * W'.a₁ * W'.a₄ - 2 * P 2 ^ 2 * Q 0 * Q 2 * W'.a₃ * W'.a₄
    - P 0 * P 2 * Q 2 ^ 2 * W'.a₃ * W'.a₄ - 3 * P 0 * P 2 * Q 2 ^ 2 * W'.a₁ * W'.a₆
    - 3 * P 2 ^ 2 * Q 2 ^ 2 * W'.a₃ * W'.a₆ - 3 * P 0 ^ 2 * Q 0 ^ 2 * W'.a₁
    - P 1 ^ 2 * Q 0 * Q 2 * W'.a₁ - 2 * P 0 * P 1 * Q 1 * Q 2 * W'.a₁
    - P 1 * P 2 * Q 0 ^ 2 * W'.a₂ - 2 * P 0 * P 2 * Q 0 * Q 1 * W'.a₂
    - 2 * P 0 * P 1 * Q 0 * Q 2 * W'.a₂ - P 0 ^ 2 * Q 1 * Q 2 * W'.a₂
    - 3 * P 0 * P 2 * Q 0 ^ 2 * W'.a₃ - 2 * P 1 * P 2 * Q 1 * Q 2 * W'.a₃
    - P 1 ^ 2 * Q 2 ^ 2 * W'.a₃ - P 2 ^ 2 * Q 0 * Q 1 * W'.a₄ - 2 * P 1 * P 2 * Q 0 * Q 2 * W'.a₄
    - 2 * P 0 * P 2 * Q 1 * Q 2 * W'.a₄ - P 0 * P 1 * Q 2 ^ 2 * W'.a₄
    - 3 * P 2 ^ 2 * Q 1 * Q 2 * W'.a₆ - 3 * P 1 * P 2 * Q 2 ^ 2 * W'.a₆ - 3 * P 0 * P 1 * Q 0 ^ 2
    - 3 * P 0 ^ 2 * Q 0 * Q 1 - P 1 * P 2 * Q 1 ^ 2 - P 1 ^ 2 * Q 1 * Q 2

variable (W') in
/-- The coordinates of a representative of `P + Q` given by the SECOND
Bosma-Lenstra addition law, the one of the line `Y = 0`.

It returns `![0, 0, 0]` exactly when `P - Q` meets the line `Y = 0`, i.e. on the
three translates of the diagonal by the points of `E ∩ {Y = 0}` -- a set DISJOINT
from the diagonal, which is where `addXYZ` degenerates. -/
noncomputable def add2XYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![add2X W' P Q, add2Y W' P Q, add2Z W' P Q]

lemma add2XYZ_X (P Q : Fin 3 → R) : add2XYZ W' P Q 0 = add2X W' P Q := rfl

lemma add2XYZ_Y (P Q : Fin 3 → R) : add2XYZ W' P Q 1 = add2Y W' P Q := rfl

lemma add2XYZ_Z (P Q : Fin 3 → R) : add2XYZ W' P Q 2 = add2Z W' P Q := rfl

lemma add2X_smul (P Q : Fin 3 → R) (u v : R) :
    add2X W' (u • P) (v • Q) = (u * v) ^ 2 * add2X W' P Q := by
  simp only [add2X, smul_fin3_ext]
  ring1

lemma add2Y_smul (P Q : Fin 3 → R) (u v : R) :
    add2Y W' (u • P) (v • Q) = (u * v) ^ 2 * add2Y W' P Q := by
  simp only [add2Y, smul_fin3_ext]
  ring1

lemma add2Z_smul (P Q : Fin 3 → R) (u v : R) :
    add2Z W' (u • P) (v • Q) = (u * v) ^ 2 * add2Z W' P Q := by
  simp only [add2Z, smul_fin3_ext]
  ring1

/-- **The second law is bihomogeneous of bidegree `(2, 2)`** (PROVEN, `ring`). -/
lemma add2XYZ_smul (P Q : Fin 3 → R) (u v : R) :
    add2XYZ W' (u • P) (v • Q) = (u * v) ^ 2 • add2XYZ W' P Q := by
  rw [add2XYZ, add2X_smul, add2Y_smul, add2Z_smul, smul_fin3, add2XYZ_X, add2XYZ_Y, add2XYZ_Z]

lemma add2X_of_infty_left (Q : Fin 3 → R) :
    add2X W' ![0, 1, 0] Q = negY W' Q * Q 0 := by
  simp only [add2X, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma add2Y_of_infty_left (Q : Fin 3 → R) :
    add2Y W' ![0, 1, 0] Q = negY W' Q * Q 1 := by
  simp only [add2Y, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma add2Z_of_infty_left (Q : Fin 3 → R) :
    add2Z W' ![0, 1, 0] Q = negY W' Q * Q 2 := by
  simp only [add2Z, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

/-- **The second law computes the UNIT LAW at the point at infinity** (PROVEN,
`ring`): `add2XYZ O Q = negY Q • Q`, with NO curve equation used.

This is the half of `hunit` that the standard law cannot supply.  `addXYZ` gives
`addXYZ O Q = (Q z) • Q` (`addXYZ_of_Z_eq_zero_left`), a legitimate rescaling of
`Q` only where `Q z` is a unit -- and it says NOTHING at `Q = O`.  Here the scalar
is `negY Q`, the `Y`-coordinate of `-Q`, which is a unit exactly where `Q z` is
not: at `Q = ![0, Q y, 0]` it is `-Q y`, a unit by non-degeneracy.  The two
together cover every point, which is the content of completeness at `P = O`. -/
lemma add2XYZ_of_infty_left (Q : Fin 3 → R) :
    add2XYZ W' ![0, 1, 0] Q = negY W' Q • Q := by
  rw [add2XYZ, add2X_of_infty_left, add2Y_of_infty_left, add2Z_of_infty_left, smul_fin3]

lemma add2X_neg (P : Fin 3 → R) : add2X W' P ![P 0, negY W' P, P 2] = 0 := by
  simp only [add2X, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma add2Z_neg (P : Fin 3 → R) : add2Z W' P ![P 0, negY W' P, P 2] = 0 := by
  simp only [add2Z, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

/-- **The second law sends `(P, -P)` to the point at infinity** (PROVEN, `ring`):
`add2XYZ P (-P) = add2Y P (-P) • ![0, 1, 0]`, and the two vanishing coordinates
vanish IDENTICALLY, with no curve equation used.

This is the half of `hinv` that the standard law cannot supply.  Mathlib's
`addXYZ_neg` gives `addXYZ P (-P) = -dblZ P • ![0, 1, 0]` with
`dblZ P = P z * (P y - negY P) ^ 3`, which degenerates on the `2`-torsion
(`P y = negY P`) and at `P z = 0`; the scalar here is a unit exactly there. -/
lemma add2XYZ_neg (P : Fin 3 → R) :
    add2XYZ W' P ![P 0, negY W' P, P 2] =
      add2Y W' P ![P 0, negY W' P, P 2] • ![0, 1, 0] := by
  rw [add2XYZ, add2X_neg, add2Z_neg, smul_fin3]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-! ### The two laws in the argument order `(−P, P)` and at `(O, Q)`

The value lemmas above are stated in the argument orders mathlib uses,
`addXYZ P (−P)` and `add2XYZ P (−P)`.  The gluing in `EllipticScheme.lean`
consumes them in the OPPOSITE order — `hinv` reads `m(−P, P) = O`, so the
first component of the pair is `−P` — and the standard law's unit clause is
consumed at `(O, Q)`.  Both re-orderings are recorded here as `ring`
identities rather than derived at the point of use, so that no consumer has
to redo them.

`neg` is mathlib's negation triple `![P x, negY P, P z]`
(`Projective/Point.lean`, imported here for it and for `addXYZ_neg`). -/

/-- **The standard law computes the UNIT LAW away from `Z = 0`** (PROVEN,
`ring`): `addXYZ O Q = Q z • Q`, with NO curve equation used.

This is the companion of `add2XYZ_of_infty_left`: the two scalars are `Q z`
and `negY Q`, and over a field one of them is always a unit — at `Q z = 0`
non-degeneracy forces `Q y` to be a unit and `negY Q = −Q y`.  Mathlib's
`addXYZ_of_Z_eq_zero_left` is the same identity but assumes
`[NoZeroDivisors R]` and the curve equation, because it derives `P x = 0`
from `P z = 0`; here `P = ![0, 1, 0]` has `P x = 0` on the nose, so the
identity is unconditional. -/
lemma addX_of_infty_left (Q : Fin 3 → R) : addX W' ![0, 1, 0] Q = Q 2 * Q 0 := by
  simp only [addX, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma addZ_of_infty_left (Q : Fin 3 → R) : addZ W' ![0, 1, 0] Q = Q 2 * Q 2 := by
  simp only [addZ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma addY_of_infty_left (Q : Fin 3 → R) : addY W' ![0, 1, 0] Q = Q 2 * Q 1 := by
  simp only [addY, addX, negAddY, addZ, negY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring1

/-- **`addXYZ O Q = Q z • Q`** (PROVEN, `ring`), unconditionally. -/
lemma addXYZ_of_infty_left (Q : Fin 3 → R) : addXYZ W' ![0, 1, 0] Q = Q 2 • Q := by
  rw [addXYZ, addX_of_infty_left, addY_of_infty_left, addZ_of_infty_left, smul_fin3]

/-- **The Weierstrass equation is invariant under negation**, over an
arbitrary commutative ring (PROVEN, `ring`).

Mathlib has `Affine.equation_neg` in affine coordinates and
`Projective.nonsingular_neg` over a FIELD, but not the projective
ring-level `Equation` statement, which is what a `ProjCoords` datum needs
in order to be negated. -/
lemma equation_neg (hP : Equation W' P) : Equation W' (neg W' P) := by
  rw [equation_iff] at hP ⊢
  simp only [neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination hP

lemma add2X_neg_left (P : Fin 3 → R) : add2X W' (neg W' P) P = 0 := by
  simp only [add2X, neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

lemma add2Z_neg_left (P : Fin 3 → R) : add2Z W' (neg W' P) P = 0 := by
  simp only [add2Z, neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

/-- **The second law sends `(−P, P)` to the point at infinity** (PROVEN,
`ring`) — `add2XYZ_neg` in the argument order the gluing consumes.  As
there, the two vanishing coordinates vanish IDENTICALLY, with no curve
equation used. -/
lemma add2XYZ_neg_left (P : Fin 3 → R) :
    add2XYZ W' (neg W' P) P = add2Y W' (neg W' P) P • ![0, 1, 0] := by
  rw [add2XYZ, add2X_neg_left, add2Z_neg_left, smul_fin3]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- **At the point at infinity the second law's scalar is `−(P y) ^ 4`**
(PROVEN, `ring`) — the easy half of the `hinv` dichotomy.  When `P z = 0`
the curve equation forces `P x = 0`, so non-degeneracy makes `P y` a unit
and this scalar is a unit, whereas `dblZ P = P z * (…) ^ 3` vanishes. -/
lemma add2Y_neg_left_of_Z_eq_zero (P : Fin 3 → R) (hx : P 0 = 0) (hz : P 2 = 0) :
    add2Y W' (neg W' P) P = -(P 1) ^ 4 := by
  simp only [add2Y, neg, negY, hx, hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring1

/-- **`addXYZ (−P) P = dblZ P • ![0, 1, 0]`** (PROVEN from mathlib's
`addXYZ_neg` and antisymmetry) — the standard law's `hinv` clause in the
argument order the gluing consumes. -/
lemma addXYZ_neg_left (hP : Equation W' P) :
    addXYZ W' (neg W' P) P = dblZ W' P • ![0, 1, 0] := by
  have hc : addXYZ W' (neg W' P) P = (-1 : R) • addXYZ W' P (neg W' P) := by
    rw [addXYZ, addXYZ, smul_fin3]
    refine funext fun i => ?_
    fin_cases i
    · show addX W' (neg W' P) P = -1 * addX W' P (neg W' P)
      simp only [addX, neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring1
    · show addY W' (neg W' P) P = -1 * addY W' P (neg W' P)
      simp only [addY, addX, negAddY, addZ, negY, neg, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring1
    · show addZ W' (neg W' P) P = -1 * addZ W' P (neg W' P)
      simp only [addZ, neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring1
  rw [hc, addXYZ_neg hP, smul_smul]
  congr 1
  ring1

/-! ### The `hinv` dichotomy over a field

`hinv` reads `m(−P, P) = O`, and it is discharged by whichever of the two laws
is non-degenerate at `(−P, P)`.  The two scalars are `dblZ P` (standard law)
and `add2Y (−P) P` (second law), and the content of this section is that over a
field they cannot both vanish — **provided the discriminant is a unit**.

## THE DISCRIMINANT HYPOTHESIS IS NECESSARY, NOT A CONVENIENCE

Computed in `Singular`, 2026-07-27, and this is what forced `[E.IsElliptic]`
onto `projMulCoords_inv` in `EllipticScheme.lean`.  Write

* `W = Y²Z + a₁XYZ + a₃YZ² − X³ − a₂X²Z − a₄XZ² − a₆Z³` (the curve),
* `T = 2Y + a₁X + a₃Z` (which is `P y − negY P`, so `T = 0` is the
  `2`-torsion condition that makes `dblZ` vanish off `Z = 0`),
* `g = add2Y (−P) P`.

Then the elimination ideal of `(W, T, g) : Z^∞` in the coefficient space
`ℚ[a₁, a₂, a₃, a₄, a₆]` is **exactly `⟨Δ²⟩`** — not merely contained in it.
So for every SINGULAR Weierstrass curve there is a point, defined over some
field of characteristic zero, with `Z ≠ 0` at which BOTH laws degenerate at
`(−P, P)`; the statement is therefore not provable by any local argument
without `IsUnit Δ`, and a leaf asserting it for an arbitrary
`E : WeierstrassCurve ℚ` would be asking for something false-shaped.

## The certificate, and how to regenerate it

`Δ² · Z⁶ ∈ (W, T, g)` and `Z⁶` is minimal (`Z⁵` is not in the ideal, and
`Δ·Zⁿ` is in it for no `n ≤ 8`).  The straight `lift` of `32 Δ² Z⁶` against
`(W, T, g)` has cofactors of 420, 919 and 91 monomials; that is avoided here by
eliminating `Y` first, which is legitimate because `2` is a unit (`Γ(Spec K, ⊤)`
is a `ℚ`-algebra).  Substituting `Y = −(a₁X + a₃Z)/2` gives the binary forms

    Wt = 4W − Z·T²  =  −(4X³ + b₂X²Z + 2b₄XZ² + b₆Z³),
    ft = 16g − T·h  (a binary quartic in `X, Z`, 42 monomials),

and the certificate becomes `32 Δ² Z⁶ = A·Wt + C·ft` with `A` of 252 and `C` of
79 monomials — one order of magnitude smaller, and split over three `ring1`
calls rather than one.  Regenerate with

    ideal I = Wt, ft;  matrix M = lift(I, 32*D^2*Z1^6);

after building `Wt`, `ft` and `h = (16g − ft)/T` by the `map` substitution.
This is why the lemma lives in THIS module and not in `EllipticScheme.lean`:
the `ring1` calls are large, and that file is edited concurrently. -/

-- The `linear_combination` for `hkey` is the `Δ² Z⁶` certificate above: 252- and
-- 79-monomial cofactors against a 7- and a 42-monomial generator, with `Δ²`
-- itself expanding to some 200 monomials.  This is the same budget the file
-- already grants `equation_addXYZ`, and for the same reason — the identity is
-- verified externally in `Singular`, so what is being paid for is arithmetic,
-- not a search.
set_option maxHeartbeats 4000000 in
theorem add2Y_neg_left_ne_zero_of_dblZ_eq_zero (hR : _root_.IsField R) (h2 : IsUnit (2 : R))
    (hD : IsUnit W'.Δ) (hP : Equation W' P) (hPs : Ideal.span (Set.range P) = ⊤)
    (hd : dblZ W' P = 0) : add2Y W' (neg W' P) P ≠ 0 := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  haveI : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨a', ha'⟩ := hR.mul_inv_cancel ha
      refine Or.inr ?_
      calc b = a' * (a * b) := by rw [← mul_assoc, mul_comm a' a, ha', one_mul]
        _ = 0 := by rw [hab, mul_zero]
  intro hg
  have hW := (equation_iff P).mp hP
  have hz : P 2 = 0 := by
    by_contra hz
    have hd' : P 2 * (P 1 - negY W' P) ^ 3 = 0 := hd
    have ht : P 1 - negY W' P = 0 := by
      rcases mul_eq_zero.mp hd' with h | h
      · exact absurd h hz
      · exact pow_eq_zero_iff three_ne_zero |>.mp h
    have hT : 2 * P 1 + W'.a₁ * P 0 + W'.a₃ * P 2 = 0 := by
      simp only [negY] at ht
      linear_combination ht
    have hgg :
        P 1 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 - 2 * P 0 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      - P 1 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄
      + 2 * P 0 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
      - P 2 ^ 4 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ + P 2 ^ 4 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2
      + P 1 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₆ - 2 * P 0 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆
      - P 2 ^ 4 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ - P 0 ^ 3 * P 1 * W'.a₁ ^ 3
      + P 0 ^ 4 * W'.a₁ ^ 2 * W'.a₂ - 3 * P 0 ^ 2 * P 1 * P 2 * W'.a₁ ^ 2 * W'.a₃
      - 3 * P 0 * P 1 * P 2 ^ 2 * W'.a₁ * W'.a₃ ^ 2
      - 6 * P 0 ^ 2 * P 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2 - 2 * P 1 * P 2 ^ 3 * W'.a₃ ^ 3
      + 2 * P 0 ^ 3 * P 2 * W'.a₁ ^ 2 * W'.a₄
      + 6 * P 0 ^ 2 * P 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ - P 1 * P 2 ^ 3 * W'.a₁ * W'.a₄ ^ 2
      + 2 * P 0 * P 2 ^ 3 * W'.a₂ * W'.a₄ ^ 2 + P 2 ^ 4 * W'.a₄ ^ 3
      + 4 * P 1 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₆ - 8 * P 0 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₆
      + 6 * P 0 * P 2 ^ 3 * W'.a₁ * W'.a₃ * W'.a₆ + 3 * P 2 ^ 4 * W'.a₃ ^ 2 * W'.a₆
      - 4 * P 2 ^ 4 * W'.a₂ * W'.a₄ * W'.a₆ - 3 * P 0 ^ 2 * P 1 ^ 2 * W'.a₁ ^ 2
      + P 0 ^ 3 * P 1 * W'.a₁ * W'.a₂ + P 0 ^ 4 * W'.a₂ ^ 2 - 3 * P 0 ^ 4 * W'.a₁ * W'.a₃
      - 6 * P 0 * P 1 ^ 2 * P 2 * W'.a₁ * W'.a₃ - 3 * P 0 ^ 2 * P 1 * P 2 * W'.a₂ * W'.a₃
      - 6 * P 0 ^ 3 * P 2 * W'.a₃ ^ 2 - 3 * P 1 ^ 2 * P 2 ^ 2 * W'.a₃ ^ 2
      + 3 * P 0 ^ 2 * P 1 * P 2 * W'.a₁ * W'.a₄ + 2 * P 0 ^ 3 * P 2 * W'.a₂ * W'.a₄
      - 3 * P 0 * P 1 * P 2 ^ 2 * W'.a₃ * W'.a₄ + 6 * P 0 ^ 2 * P 2 ^ 2 * W'.a₄ ^ 2
      + 9 * P 0 * P 1 * P 2 ^ 2 * W'.a₁ * W'.a₆ - 18 * P 0 ^ 2 * P 2 ^ 2 * W'.a₂ * W'.a₆
      - 3 * P 1 * P 2 ^ 3 * W'.a₃ * W'.a₆ + 6 * P 0 * P 2 ^ 3 * W'.a₄ * W'.a₆
      + 9 * P 2 ^ 4 * W'.a₆ ^ 2 - 3 * P 0 * P 1 ^ 3 * W'.a₁ - 3 * P 0 ^ 3 * P 1 * W'.a₃
      - 3 * P 1 ^ 3 * P 2 * W'.a₃ - 3 * P 0 ^ 4 * W'.a₄ - 18 * P 0 ^ 3 * P 2 * W'.a₆
      - P 1 ^ 4 = 0 := by
      rw [← hg]
      simp only [add2Y, neg, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring1
    have hWt :
        - P 0 ^ 2 * P 2 * W'.a₁ ^ 2 - 2 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ - P 2 ^ 3 * W'.a₃ ^ 2
      - 4 * P 0 ^ 2 * P 2 * W'.a₂ - 4 * P 0 * P 2 ^ 2 * W'.a₄ - 4 * P 2 ^ 3 * W'.a₆
      - 4 * P 0 ^ 3 = 0 := by
      linear_combination 4 * hW - P 2 * (2 * P 1 + W'.a₁ * P 0 + W'.a₃ * P 2) * hT
    have hft :
        - 8 * P 0 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2
      - 8 * P 2 ^ 4 * W'.a₁ * W'.a₂ * W'.a₃ ^ 3
      + 8 * P 0 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄
      + 8 * P 2 ^ 4 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ - 8 * P 0 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₆
      - 8 * P 2 ^ 4 * W'.a₁ ^ 3 * W'.a₃ * W'.a₆ + P 0 ^ 4 * W'.a₁ ^ 4
      + 4 * P 0 ^ 3 * P 2 * W'.a₁ ^ 3 * W'.a₃
      + 6 * P 0 ^ 2 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2
      - 32 * P 0 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₃ ^ 2 + 12 * P 0 * P 2 ^ 3 * W'.a₁ * W'.a₃ ^ 3
      + 9 * P 2 ^ 4 * W'.a₃ ^ 4 + 32 * P 0 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
      - 16 * P 2 ^ 4 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ + 8 * P 0 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₄ ^ 2
      + 24 * P 2 ^ 4 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2
      - 64 * P 0 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆
      - 32 * P 2 ^ 4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆
      - 16 * P 2 ^ 4 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ + 8 * P 0 ^ 4 * W'.a₁ ^ 2 * W'.a₂
      + 16 * P 0 ^ 3 * P 2 * W'.a₁ * W'.a₂ * W'.a₃
      - 72 * P 0 ^ 2 * P 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2 + 8 * P 0 ^ 3 * P 2 * W'.a₁ ^ 2 * W'.a₄
      + 96 * P 0 ^ 2 * P 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄
      + 24 * P 0 * P 2 ^ 3 * W'.a₃ ^ 2 * W'.a₄ + 32 * P 0 * P 2 ^ 3 * W'.a₂ * W'.a₄ ^ 2
      + 16 * P 2 ^ 4 * W'.a₄ ^ 3 - 72 * P 0 ^ 2 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₆
      - 128 * P 0 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₆ + 48 * P 0 * P 2 ^ 3 * W'.a₁ * W'.a₃ * W'.a₆
      + 72 * P 2 ^ 4 * W'.a₃ ^ 2 * W'.a₆ - 64 * P 2 ^ 4 * W'.a₂ * W'.a₄ * W'.a₆
      + 16 * P 0 ^ 4 * W'.a₂ ^ 2 - 24 * P 0 ^ 4 * W'.a₁ * W'.a₃
      - 72 * P 0 ^ 3 * P 2 * W'.a₃ ^ 2 + 32 * P 0 ^ 3 * P 2 * W'.a₂ * W'.a₄
      + 96 * P 0 ^ 2 * P 2 ^ 2 * W'.a₄ ^ 2 - 288 * P 0 ^ 2 * P 2 ^ 2 * W'.a₂ * W'.a₆
      + 96 * P 0 * P 2 ^ 3 * W'.a₄ * W'.a₆ + 144 * P 2 ^ 4 * W'.a₆ ^ 2
      - 48 * P 0 ^ 4 * W'.a₄ - 288 * P 0 ^ 3 * P 2 * W'.a₆ = 0 := by
      linear_combination 16 * hgg -
        (8 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 - 8 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄
      + 8 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₆ - P 0 ^ 3 * W'.a₁ ^ 3
      - 3 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₃ - 3 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ ^ 2
      - 9 * P 2 ^ 3 * W'.a₃ ^ 3 - 8 * P 2 ^ 3 * W'.a₁ * W'.a₄ ^ 2
      + 32 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₆ - 14 * P 0 ^ 2 * P 1 * W'.a₁ ^ 2
      + 8 * P 0 ^ 3 * W'.a₁ * W'.a₂ - 28 * P 0 * P 1 * P 2 * W'.a₁ * W'.a₃
      - 24 * P 0 ^ 2 * P 2 * W'.a₂ * W'.a₃ - 14 * P 1 * P 2 ^ 2 * W'.a₃ ^ 2
      + 24 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₄ - 24 * P 0 * P 2 ^ 2 * W'.a₃ * W'.a₄
      + 72 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₆ - 24 * P 2 ^ 3 * W'.a₃ * W'.a₆
      - 20 * P 0 * P 1 ^ 2 * W'.a₁ - 24 * P 0 ^ 3 * W'.a₃ - 20 * P 1 ^ 2 * P 2 * W'.a₃
      - 8 * P 1 ^ 3) * hT
    have hkey : (32 : R) * W'.Δ ^ 2 * P 2 ^ 6 = 0 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      linear_combination
        (- 8 * P 2 ^ 3 * W'.a₁ ^ 10 * W'.a₂ * W'.a₃ ^ 2 + 8 * P 2 ^ 3 * W'.a₁ ^ 11 * W'.a₃ * W'.a₄
      - 8 * P 2 ^ 3 * W'.a₁ ^ 12 * W'.a₆ + P 0 ^ 3 * W'.a₁ ^ 12
      + 3 * P 0 ^ 2 * P 2 * W'.a₁ ^ 11 * W'.a₃ + 3 * P 0 * P 2 ^ 2 * W'.a₁ ^ 10 * W'.a₃ ^ 2
      - 160 * P 2 ^ 3 * W'.a₁ ^ 8 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      + 9 * P 2 ^ 3 * W'.a₁ ^ 9 * W'.a₃ ^ 3
      + 160 * P 2 ^ 3 * W'.a₁ ^ 9 * W'.a₂ * W'.a₃ * W'.a₄
      + 8 * P 2 ^ 3 * W'.a₁ ^ 10 * W'.a₄ ^ 2 - 192 * P 2 ^ 3 * W'.a₁ ^ 10 * W'.a₂ * W'.a₆
      + 24 * P 0 ^ 3 * W'.a₁ ^ 10 * W'.a₂ + 60 * P 0 ^ 2 * P 2 * W'.a₁ ^ 9 * W'.a₂ * W'.a₃
      - 28 * P 0 * P 2 ^ 2 * W'.a₁ ^ 8 * W'.a₂ * W'.a₃ ^ 2
      - 1280 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₂ ^ 3 * W'.a₃ ^ 2
      + 608 * P 2 ^ 3 * W'.a₁ ^ 7 * W'.a₂ * W'.a₃ ^ 3
      + 6 * P 0 ^ 2 * P 2 * W'.a₁ ^ 10 * W'.a₄
      + 88 * P 0 * P 2 ^ 2 * W'.a₁ ^ 9 * W'.a₃ * W'.a₄
      + 1280 * P 2 ^ 3 * W'.a₁ ^ 7 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄
      - 446 * P 2 ^ 3 * W'.a₁ ^ 8 * W'.a₃ ^ 2 * W'.a₄
      + 160 * P 2 ^ 3 * W'.a₁ ^ 8 * W'.a₂ * W'.a₄ ^ 2
      - 76 * P 0 * P 2 ^ 2 * W'.a₁ ^ 10 * W'.a₆
      - 1920 * P 2 ^ 3 * W'.a₁ ^ 8 * W'.a₂ ^ 2 * W'.a₆
      + 500 * P 2 ^ 3 * W'.a₁ ^ 9 * W'.a₃ * W'.a₆ + 240 * P 0 ^ 3 * W'.a₁ ^ 8 * W'.a₂ ^ 2
      - 72 * P 0 ^ 3 * W'.a₁ ^ 9 * W'.a₃
      + 480 * P 0 ^ 2 * P 2 * W'.a₁ ^ 7 * W'.a₂ ^ 2 * W'.a₃
      - 198 * P 0 ^ 2 * P 2 * W'.a₁ ^ 8 * W'.a₃ ^ 2
      - 928 * P 0 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      - 5120 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 4 * W'.a₃ ^ 2
      - 104 * P 0 * P 2 ^ 2 * W'.a₁ ^ 7 * W'.a₃ ^ 3
      + 6432 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₂ ^ 2 * W'.a₃ ^ 3
      - 482 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₃ ^ 4
      + 120 * P 0 ^ 2 * P 2 * W'.a₁ ^ 8 * W'.a₂ * W'.a₄
      + 1408 * P 0 * P 2 ^ 2 * W'.a₁ ^ 7 * W'.a₂ * W'.a₃ * W'.a₄
      + 5120 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄
      - 4352 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄
      + 88 * P 0 * P 2 ^ 2 * W'.a₁ ^ 8 * W'.a₄ ^ 2
      + 1280 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₂ ^ 2 * W'.a₄ ^ 2
      - 1392 * P 2 ^ 3 * W'.a₁ ^ 7 * W'.a₃ * W'.a₄ ^ 2
      - 1520 * P 0 * P 2 ^ 2 * W'.a₁ ^ 8 * W'.a₂ * W'.a₆
      - 10240 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₂ ^ 3 * W'.a₆
      + 8000 * P 2 ^ 3 * W'.a₁ ^ 7 * W'.a₂ * W'.a₃ * W'.a₆
      + 1000 * P 2 ^ 3 * W'.a₁ ^ 8 * W'.a₄ * W'.a₆ + 1280 * P 0 ^ 3 * W'.a₁ ^ 6 * W'.a₂ ^ 3
      - 1152 * P 0 ^ 3 * W'.a₁ ^ 7 * W'.a₂ * W'.a₃
      + 1920 * P 0 ^ 2 * P 2 * W'.a₁ ^ 5 * W'.a₂ ^ 3 * W'.a₃
      - 2592 * P 0 ^ 2 * P 2 * W'.a₁ ^ 6 * W'.a₂ * W'.a₃ ^ 2
      - 6528 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ ^ 3 * W'.a₃ ^ 2
      - 10240 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 5 * W'.a₃ ^ 2
      + 3296 * P 0 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₂ * W'.a₃ ^ 3
      + 24576 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ ^ 3 * W'.a₃ ^ 3
      - 11864 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ * W'.a₃ ^ 4 - 144 * P 0 ^ 3 * W'.a₁ ^ 8 * W'.a₄
      + 960 * P 0 ^ 2 * P 2 * W'.a₁ ^ 6 * W'.a₂ ^ 2 * W'.a₄
      - 576 * P 0 ^ 2 * P 2 * W'.a₁ ^ 7 * W'.a₃ * W'.a₄
      + 8448 * P 0 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄
      + 10240 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ ^ 4 * W'.a₃ * W'.a₄
      - 4752 * P 0 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₃ ^ 2 * W'.a₄
      - 9408 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₄
      + 6080 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₃ ^ 3 * W'.a₄
      + 1408 * P 0 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₂ * W'.a₄ ^ 2
      + 5120 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 3 * W'.a₄ ^ 2
      - 16704 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₂ * W'.a₃ * W'.a₄ ^ 2
      - 928 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₄ ^ 3 - 216 * P 0 ^ 2 * P 2 * W'.a₁ ^ 8 * W'.a₆
      - 12160 * P 0 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₂ ^ 2 * W'.a₆
      - 30720 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 4 * W'.a₆
      + 4128 * P 0 * P 2 ^ 2 * W'.a₁ ^ 7 * W'.a₃ * W'.a₆
      + 48000 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆
      - 9936 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₃ ^ 2 * W'.a₆
      + 16000 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₂ * W'.a₄ * W'.a₆
      + 3840 * P 0 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 4
      - 6912 * P 0 ^ 3 * W'.a₁ ^ 5 * W'.a₂ ^ 2 * W'.a₃
      + 3840 * P 0 ^ 2 * P 2 * W'.a₁ ^ 3 * W'.a₂ ^ 4 * W'.a₃
      + 1728 * P 0 ^ 3 * W'.a₁ ^ 6 * W'.a₃ ^ 2
      - 12096 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      - 18688 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 4 * W'.a₃ ^ 2
      - 8192 * P 2 ^ 3 * W'.a₂ ^ 6 * W'.a₃ ^ 2
      + 4320 * P 0 ^ 2 * P 2 * W'.a₁ ^ 5 * W'.a₃ ^ 3
      + 31360 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ ^ 2 * W'.a₃ ^ 3
      + 32000 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ ^ 3
      - 312 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₃ ^ 4
      - 44640 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 4
      + 7056 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₃ ^ 5 - 2304 * P 0 ^ 3 * W'.a₁ ^ 6 * W'.a₂ * W'.a₄
      + 3840 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₂ ^ 3 * W'.a₄
      - 6912 * P 0 ^ 2 * P 2 * W'.a₁ ^ 5 * W'.a₂ * W'.a₃ * W'.a₄
      + 22528 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄
      + 8192 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 5 * W'.a₃ * W'.a₄
      - 29760 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄
      + 19456 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₃ ^ 2 * W'.a₄
      - 5632 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ ^ 3 * W'.a₄
      - 576 * P 0 ^ 2 * P 2 * W'.a₁ ^ 6 * W'.a₄ ^ 2
      + 8448 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₄ ^ 2
      + 10240 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 4 * W'.a₄ ^ 2
      - 13632 * P 0 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₃ * W'.a₄ ^ 2
      - 66816 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ ^ 2
      + 33216 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₃ ^ 2 * W'.a₄ ^ 2
      - 11136 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ * W'.a₄ ^ 3
      - 3456 * P 0 ^ 2 * P 2 * W'.a₁ ^ 6 * W'.a₂ * W'.a₆
      - 48640 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ ^ 3 * W'.a₆
      - 49152 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 5 * W'.a₆
      + 49536 * P 0 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₂ * W'.a₃ * W'.a₆
      + 128000 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ ^ 3 * W'.a₃ * W'.a₆
      - 89280 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆
      + 8256 * P 0 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₄ * W'.a₆
      + 96000 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆
      - 29952 * P 2 ^ 3 * W'.a₁ ^ 5 * W'.a₃ * W'.a₄ * W'.a₆
      - 4896 * P 2 ^ 3 * W'.a₁ ^ 6 * W'.a₆ ^ 2 + 6144 * P 0 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 5
      - 18432 * P 0 ^ 3 * W'.a₁ ^ 3 * W'.a₂ ^ 3 * W'.a₃
      + 3072 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₂ ^ 5 * W'.a₃
      + 13824 * P 0 ^ 3 * W'.a₁ ^ 4 * W'.a₂ * W'.a₃ ^ 2
      - 23040 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₃ ^ 2
      - 19456 * P 0 * P 2 ^ 2 * W'.a₂ ^ 5 * W'.a₃ ^ 2
      + 27648 * P 0 ^ 2 * P 2 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ ^ 3
      + 66048 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ ^ 3
      - 63936 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 4
      - 19584 * P 2 ^ 3 * W'.a₂ ^ 3 * W'.a₃ ^ 4
      + 39744 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ ^ 5
      - 13824 * P 0 ^ 3 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₄
      + 7680 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 4 * W'.a₄
      + 6912 * P 0 ^ 3 * W'.a₁ ^ 5 * W'.a₃ * W'.a₄
      - 27648 * P 0 ^ 2 * P 2 * W'.a₁ ^ 3 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄
      + 22528 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ * W'.a₄
      + 15552 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₃ ^ 2 * W'.a₄
      - 9984 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₄
      + 64000 * P 2 ^ 3 * W'.a₂ ^ 4 * W'.a₃ ^ 2 * W'.a₄
      + 61440 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ ^ 3 * W'.a₄
      - 119808 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ ^ 3 * W'.a₄
      + 2592 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₃ ^ 4 * W'.a₄
      - 6912 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₄ ^ 2
      + 22528 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₄ ^ 2
      + 8192 * P 2 ^ 3 * W'.a₂ ^ 5 * W'.a₄ ^ 2
      - 109056 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ * W'.a₄ ^ 2
      - 89088 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ * W'.a₄ ^ 2
      + 102912 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ ^ 2
      - 9088 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₄ ^ 3
      - 44544 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ ^ 3
      + 54272 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄ ^ 3
      - 20736 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₆
      - 97280 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 4 * W'.a₆
      - 32768 * P 2 ^ 3 * W'.a₂ ^ 6 * W'.a₆
      + 10368 * P 0 ^ 2 * P 2 * W'.a₁ ^ 5 * W'.a₃ * W'.a₆
      + 198144 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆
      + 128000 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ * W'.a₆
      - 63936 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₃ ^ 2 * W'.a₆
      - 237312 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₆
      + 67968 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₃ ^ 3 * W'.a₆
      + 99072 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₄ * W'.a₆
      + 256000 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₄ * W'.a₆
      - 239616 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆
      - 29952 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₄ ^ 2 * W'.a₆
      - 58752 * P 2 ^ 3 * W'.a₁ ^ 4 * W'.a₂ * W'.a₆ ^ 2 + 4096 * P 0 ^ 3 * W'.a₂ ^ 6
      - 18432 * P 0 ^ 3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃
      + 27648 * P 0 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      - 13824 * P 0 ^ 2 * P 2 * W'.a₂ ^ 4 * W'.a₃ ^ 2
      - 13824 * P 0 ^ 3 * W'.a₁ ^ 3 * W'.a₃ ^ 3
      + 41472 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ ^ 3
      - 31104 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₃ ^ 4
      - 17280 * P 0 * P 2 ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 4
      + 25920 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ ^ 5 - 15552 * P 2 ^ 3 * W'.a₃ ^ 6
      - 36864 * P 0 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₄
      + 6144 * P 0 ^ 2 * P 2 * W'.a₂ ^ 5 * W'.a₄
      + 55296 * P 0 ^ 3 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ * W'.a₄
      - 36864 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ * W'.a₄
      + 82944 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄
      + 132096 * P 0 * P 2 ^ 2 * W'.a₂ ^ 3 * W'.a₃ ^ 2 * W'.a₄
      - 221184 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * W'.a₄
      + 79488 * P 2 ^ 3 * W'.a₂ * W'.a₃ ^ 4 * W'.a₄ + 6912 * P 0 ^ 3 * W'.a₁ ^ 4 * W'.a₄ ^ 2
      - 27648 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ ^ 2
      + 22528 * P 0 * P 2 ^ 2 * W'.a₂ ^ 4 * W'.a₄ ^ 2
      + 20736 * P 0 ^ 2 * P 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄ ^ 2
      - 218112 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ ^ 2
      + 294912 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ ^ 2
      - 119808 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₄ ^ 2
      - 34560 * P 2 ^ 3 * W'.a₁ * W'.a₃ ^ 3 * W'.a₄ ^ 2
      - 72704 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ ^ 3
      - 59392 * P 2 ^ 3 * W'.a₂ ^ 3 * W'.a₄ ^ 3
      + 217088 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ ^ 3
      + 27136 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₄ ^ 4
      - 55296 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₆
      - 77824 * P 0 * P 2 ^ 2 * W'.a₂ ^ 5 * W'.a₆
      + 82944 * P 0 ^ 2 * P 2 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ * W'.a₆
      + 264192 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ * W'.a₆
      - 290304 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆
      - 156672 * P 2 ^ 3 * W'.a₂ ^ 3 * W'.a₃ ^ 2 * W'.a₆
      + 317952 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * W'.a₆
      + 20736 * P 0 ^ 2 * P 2 * W'.a₁ ^ 4 * W'.a₄ * W'.a₆
      + 396288 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆
      + 256000 * P 2 ^ 3 * W'.a₂ ^ 4 * W'.a₄ * W'.a₆
      - 221184 * P 0 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄ * W'.a₆
      - 479232 * P 2 ^ 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ * W'.a₆
      + 89856 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * W'.a₆
      - 239616 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ ^ 2 * W'.a₆
      - 17280 * P 0 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₆ ^ 2
      - 235008 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆ ^ 2
      + 158976 * P 2 ^ 3 * W'.a₁ ^ 3 * W'.a₃ * W'.a₆ ^ 2
      - 36864 * P 0 ^ 3 * W'.a₂ ^ 4 * W'.a₄
      + 110592 * P 0 ^ 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄
      - 82944 * P 0 ^ 3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄
      + 82944 * P 0 ^ 2 * P 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₄
      - 124416 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₃ ^ 3 * W'.a₄
      + 51840 * P 0 * P 2 ^ 2 * W'.a₃ ^ 4 * W'.a₄
      + 55296 * P 0 ^ 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ ^ 2
      - 36864 * P 0 ^ 2 * P 2 * W'.a₂ ^ 3 * W'.a₄ ^ 2
      + 82944 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ ^ 2
      - 221184 * P 0 * P 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ ^ 2
      + 13824 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₄ ^ 3
      - 145408 * P 0 * P 2 ^ 2 * W'.a₂ ^ 2 * W'.a₄ ^ 3
      + 466944 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 3
      - 23040 * P 2 ^ 3 * W'.a₃ ^ 2 * W'.a₄ ^ 3 + 108544 * P 2 ^ 3 * W'.a₂ * W'.a₄ ^ 4
      - 55296 * P 0 ^ 2 * P 2 * W'.a₂ ^ 4 * W'.a₆
      + 165888 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₆
      - 124416 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₆
      - 138240 * P 0 * P 2 ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * W'.a₆
      + 207360 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ ^ 3 * W'.a₆
      - 186624 * P 2 ^ 3 * W'.a₃ ^ 4 * W'.a₆
      + 165888 * P 0 ^ 2 * P 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ * W'.a₆
      + 528384 * P 0 * P 2 ^ 2 * W'.a₂ ^ 3 * W'.a₄ * W'.a₆
      - 884736 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆
      + 635904 * P 2 ^ 3 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * W'.a₆
      - 221184 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₄ ^ 2 * W'.a₆
      - 479232 * P 2 ^ 3 * W'.a₂ ^ 2 * W'.a₄ ^ 2 * W'.a₆
      - 138240 * P 2 ^ 3 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * W'.a₆
      - 138240 * P 0 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ ^ 2
      - 313344 * P 2 ^ 3 * W'.a₂ ^ 3 * W'.a₆ ^ 2
      + 635904 * P 2 ^ 3 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ ^ 2
      + 317952 * P 2 ^ 3 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ ^ 2
      + 110592 * P 0 ^ 3 * W'.a₂ ^ 2 * W'.a₄ ^ 2
      - 165888 * P 0 ^ 3 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2
      - 124416 * P 0 ^ 2 * P 2 * W'.a₃ ^ 2 * W'.a₄ ^ 2
      + 55296 * P 0 ^ 2 * P 2 * W'.a₂ * W'.a₄ ^ 3 + 233472 * P 0 * P 2 ^ 2 * W'.a₄ ^ 4
      + 331776 * P 0 ^ 2 * P 2 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆
      - 497664 * P 0 ^ 2 * P 2 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆
      + 414720 * P 0 * P 2 ^ 2 * W'.a₃ ^ 2 * W'.a₄ * W'.a₆
      - 884736 * P 0 * P 2 ^ 2 * W'.a₂ * W'.a₄ ^ 2 * W'.a₆
      - 92160 * P 2 ^ 3 * W'.a₄ ^ 3 * W'.a₆ - 276480 * P 0 * P 2 ^ 2 * W'.a₂ ^ 2 * W'.a₆ ^ 2
      + 414720 * P 0 * P 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₆ ^ 2
      - 746496 * P 2 ^ 3 * W'.a₃ ^ 2 * W'.a₆ ^ 2
      + 1271808 * P 2 ^ 3 * W'.a₂ * W'.a₄ * W'.a₆ ^ 2 - 110592 * P 0 ^ 3 * W'.a₄ ^ 3
      - 497664 * P 0 ^ 2 * P 2 * W'.a₄ ^ 2 * W'.a₆
      + 829440 * P 0 * P 2 ^ 2 * W'.a₄ * W'.a₆ ^ 2 - 995328 * P 2 ^ 3 * W'.a₆ ^ 3) * hWt +
        (P 0 * P 2 * W'.a₁ ^ 10 + P 2 ^ 2 * W'.a₁ ^ 9 * W'.a₃ + 20 * P 0 * P 2 * W'.a₁ ^ 8 * W'.a₂
      + 16 * P 2 ^ 2 * W'.a₁ ^ 7 * W'.a₂ * W'.a₃ + 2 * P 2 ^ 2 * W'.a₁ ^ 8 * W'.a₄
      + 4 * P 0 ^ 2 * W'.a₁ ^ 8 + 160 * P 0 * P 2 * W'.a₁ ^ 6 * W'.a₂ ^ 2
      - 52 * P 0 * P 2 * W'.a₁ ^ 7 * W'.a₃ + 96 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₂ ^ 2 * W'.a₃
      - 50 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₃ ^ 2 + 32 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₂ * W'.a₄
      + 64 * P 0 ^ 2 * W'.a₁ ^ 6 * W'.a₂ + 640 * P 0 * P 2 * W'.a₁ ^ 4 * W'.a₂ ^ 3
      - 624 * P 0 * P 2 * W'.a₁ ^ 5 * W'.a₂ * W'.a₃
      + 256 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ ^ 3 * W'.a₃
      - 344 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₃ ^ 2 - 104 * P 0 * P 2 * W'.a₁ ^ 6 * W'.a₄
      + 192 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ ^ 2 * W'.a₄
      - 256 * P 2 ^ 2 * W'.a₁ ^ 5 * W'.a₃ * W'.a₄ + 56 * P 2 ^ 2 * W'.a₁ ^ 6 * W'.a₆
      + 384 * P 0 ^ 2 * W'.a₁ ^ 4 * W'.a₂ ^ 2 + 1280 * P 0 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 4
      - 192 * P 0 ^ 2 * W'.a₁ ^ 5 * W'.a₃ - 2496 * P 0 * P 2 * W'.a₁ ^ 3 * W'.a₂ ^ 2 * W'.a₃
      + 256 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ + 744 * P 0 * P 2 * W'.a₁ ^ 4 * W'.a₃ ^ 2
      - 352 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2
      + 592 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ ^ 3 - 1248 * P 0 * P 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₄
      + 512 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 3 * W'.a₄
      - 2048 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃ * W'.a₄
      - 256 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₄ ^ 2 + 672 * P 2 ^ 2 * W'.a₁ ^ 4 * W'.a₂ * W'.a₆
      + 1024 * P 0 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 3 + 1024 * P 0 * P 2 * W'.a₂ ^ 5
      - 1536 * P 0 ^ 2 * W'.a₁ ^ 3 * W'.a₂ * W'.a₃
      - 3328 * P 0 * P 2 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃
      + 3264 * P 0 * P 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2
      + 896 * P 2 ^ 2 * W'.a₂ ^ 3 * W'.a₃ ^ 2 - 1728 * P 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ ^ 3
      - 384 * P 0 ^ 2 * W'.a₁ ^ 4 * W'.a₄ - 4992 * P 0 * P 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄
      + 512 * P 2 ^ 2 * W'.a₂ ^ 4 * W'.a₄ + 2688 * P 0 * P 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₄
      - 4096 * P 2 ^ 2 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄
      + 5280 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄
      - 2048 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ ^ 2 + 288 * P 0 * P 2 * W'.a₁ ^ 4 * W'.a₆
      + 2688 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆
      - 1728 * P 2 ^ 2 * W'.a₁ ^ 3 * W'.a₃ * W'.a₆ + 1024 * P 0 ^ 2 * W'.a₂ ^ 4
      - 3072 * P 0 ^ 2 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 2304 * P 0 ^ 2 * W'.a₁ ^ 2 * W'.a₃ ^ 2
      + 1152 * P 0 * P 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 - 1728 * P 0 * P 2 * W'.a₁ * W'.a₃ ^ 3
      + 864 * P 2 ^ 2 * W'.a₃ ^ 4 - 3072 * P 0 ^ 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄
      - 6656 * P 0 * P 2 * W'.a₂ ^ 3 * W'.a₄
      + 10752 * P 0 * P 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
      - 3456 * P 2 ^ 2 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄
      + 2688 * P 0 * P 2 * W'.a₁ ^ 2 * W'.a₄ ^ 2 - 4096 * P 2 ^ 2 * W'.a₂ ^ 2 * W'.a₄ ^ 2
      + 12288 * P 2 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2
      + 2304 * P 0 * P 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ + 3584 * P 2 ^ 2 * W'.a₂ ^ 3 * W'.a₆
      - 6912 * P 2 ^ 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆
      - 3456 * P 2 ^ 2 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ - 6144 * P 0 ^ 2 * W'.a₂ ^ 2 * W'.a₄
      + 9216 * P 0 ^ 2 * W'.a₁ * W'.a₃ * W'.a₄ - 3456 * P 0 * P 2 * W'.a₃ ^ 2 * W'.a₄
      + 10752 * P 0 * P 2 * W'.a₂ * W'.a₄ ^ 2 + 8192 * P 2 ^ 2 * W'.a₄ ^ 3
      + 4608 * P 0 * P 2 * W'.a₂ ^ 2 * W'.a₆ - 6912 * P 0 * P 2 * W'.a₁ * W'.a₃ * W'.a₆
      + 6912 * P 2 ^ 2 * W'.a₃ ^ 2 * W'.a₆ - 13824 * P 2 ^ 2 * W'.a₂ * W'.a₄ * W'.a₆
      + 9216 * P 0 ^ 2 * W'.a₄ ^ 2 - 13824 * P 0 * P 2 * W'.a₄ * W'.a₆
      + 13824 * P 2 ^ 2 * W'.a₆ ^ 2) * hft
    have h32 : IsUnit ((32 : R) * W'.Δ ^ 2) := by
      refine IsUnit.mul ?_ (hD.pow 2)
      have h := h2.pow 5
      norm_num at h
      exact h
    exact hz (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp (h32.mul_right_eq_zero.mp hkey))
  have hx : P 0 = 0 := X_eq_zero_of_Z_eq_zero hP hz
  have hy : P 1 ≠ 0 := by
    intro h1
    have hle : Ideal.span (Set.range P) ≤ ⊥ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hx, h1, hz]
    rw [hPs] at hle
    exact one_ne_zero (Ideal.mem_bot.mp (hle Submodule.mem_top))
  rw [add2Y_neg_left_of_Z_eq_zero _ hx hz] at hg
  exact hy (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp (neg_eq_zero.mp hg))

/-- **At `(−P, P)` one of the two laws is a UNIT multiple of `![0, 1, 0]`**
(PROVEN over a field with `2` and `Δ` units) — the exact input `hinv` needs, and
the reason `projMulCoords_inv` carries `[E.IsElliptic]`. -/
theorem exists_units_smul_neg_left (hR : _root_.IsField R) (h2 : IsUnit (2 : R))
    (hD : IsUnit W'.Δ) (hP : Equation W' P) (hPs : Ideal.span (Set.range P) = ⊤) :
    (∃ u : Rˣ, addXYZ W' (neg W' P) P = (u : R) • ![0, 1, 0]) ∨
      (∃ u : Rˣ, add2XYZ W' (neg W' P) P = (u : R) • ![0, 1, 0]) := by
  have hunit : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha =>
    isUnit_iff_exists_inv.mpr (hR.mul_inv_cancel ha)
  by_cases hd : dblZ W' P = 0
  · refine Or.inr ⟨(hunit _ (add2Y_neg_left_ne_zero_of_dblZ_eq_zero hR h2 hD hP hPs hd)).unit, ?_⟩
    rw [add2XYZ_neg_left, IsUnit.unit_spec]
  · refine Or.inl ⟨(hunit _ hd).unit, ?_⟩
    rw [addXYZ_neg_left hP, IsUnit.unit_spec]

/-- **At `(O, Q)` one of the two laws is a UNIT rescaling of `Q`** (PROVEN over a
field) — the exact input `hunit` needs.  No discriminant hypothesis is required
here, unlike at `(−P, P)`: the two scalars are `Q z` and `negY Q`, and where
`Q z = 0` the curve equation forces `Q x = 0`, so non-degeneracy makes `Q y` a
unit and `negY Q = −Q y`. -/
theorem exists_units_smul_infty_left (hR : _root_.IsField R) (hQ : Equation W' Q)
    (hQs : Ideal.span (Set.range Q) = ⊤) :
    (∃ u : Rˣ, addXYZ W' ![0, 1, 0] Q = (u : R) • Q) ∨
      (∃ u : Rˣ, add2XYZ W' ![0, 1, 0] Q = (u : R) • Q) := by
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  have hunit : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha =>
    isUnit_iff_exists_inv.mpr (hR.mul_inv_cancel ha)
  haveI : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨a', ha'⟩ := hR.mul_inv_cancel ha
      refine Or.inr ?_
      calc b = a' * (a * b) := by rw [← mul_assoc, mul_comm a' a, ha', one_mul]
        _ = 0 := by rw [hab, mul_zero]
  by_cases hz : Q 2 = 0
  · have hx : Q 0 = 0 := X_eq_zero_of_Z_eq_zero hQ hz
    have hy : Q 1 ≠ 0 := by
      intro h1
      have hle : Ideal.span (Set.range Q) ≤ ⊥ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [hx, h1, hz]
      rw [hQs] at hle
      exact one_ne_zero (Ideal.mem_bot.mp (hle Submodule.mem_top))
    have hneg : negY W' Q = -Q 1 := by
      show -Q 1 - W'.a₁ * Q 0 - W'.a₃ * Q 2 = -Q 1
      rw [hx, hz]; ring1
    refine Or.inr ⟨(hunit _ (neg_ne_zero.mpr hy)).unit, ?_⟩
    rw [add2XYZ_of_infty_left, IsUnit.unit_spec, hneg]
  · refine Or.inl ⟨(hunit _ hz).unit, ?_⟩
    rw [addXYZ_of_infty_left, IsUnit.unit_spec]

/-- **The second triple again satisfies the Weierstrass equation** (sorry node).

Exactly what `equation_addXYZ` proves for the standard law, for the law of the
line `Y = 0`.  It was VERIFIED in `Singular` -- `W(add2X, add2Y, add2Z)` reduces
to `0` modulo `(W(P), W(Q))` -- so the statement is TRUE; what is missing is only
the Lean-side certificate.

*Cost warning, and it is why this is a leaf rather than a `linear_combination`.*
Both sides are bihomogeneous of bidegree `(6, 6)`, the same shape as
`equation_addXYZ`, whose `ring1` already takes about four and a half minutes with
cofactors of 130 and 186 monomials.  The second law's coefficients are markedly
denser (56, 74 and 43 monomials against mathlib's 18, 18 and 12), so the cofactors
here must be expected to be several times larger again.  Whoever closes this
should budget a long `ring1`, and should consider splitting the identity by
bidegree so that no single `ring1` sees the whole thing. -/
theorem equation_add2XYZ (hP : Equation W' P) (hQ : Equation W' Q) :
    Equation W' (add2XYZ W' P Q) :=
  sorry

/-- **The two addition laws are PROPORTIONAL** (sorry node) -- they compute the
same point of `P²` wherever both are non-degenerate.

Verified in `Singular`: each of the three cross-differences reduces to `0` modulo
`(W(P), W(Q))`.  This is what makes the glued morphism well defined on the overlap
of the two pieces of the cover, via `ProjCoords.toHom_smul` with the transition
unit `add2Z / addZ`.  Only the `X`/`Z` and `Y`/`Z` cross-differences are stated;
the `X`/`Y` one follows from them wherever `addZ` is a unit, and is not needed. -/
theorem add2X_mul_addZ (hP : Equation W' P) (hQ : Equation W' Q) :
    add2X W' P Q * addZ W' P Q = add2Z W' P Q * addX W' P Q :=
  sorry

/-- **The `Y`/`Z` half of the proportionality of the two addition laws**
(sorry node); see `add2X_mul_addZ`. -/
theorem add2Y_mul_addZ (hP : Equation W' P) (hQ : Equation W' Q) :
    add2Y W' P Q * addZ W' P Q = add2Z W' P Q * addY W' P Q :=
  sorry

end WeierstrassCurve.Projective

end
