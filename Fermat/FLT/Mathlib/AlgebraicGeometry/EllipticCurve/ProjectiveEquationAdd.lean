/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# The FIRST chord–tangent addition law preserves the Weierstrass equation

`WeierstrassCurve.Projective.equation_addXYZ` —
`W.Equation P → W.Equation Q → W.Equation (W.addXYZ P Q)` over any `[CommRing R]`.

Mathlib's `addXYZ` is defined over an arbitrary commutative ring, but the fact
that it lands back on the curve is proved there only over a FIELD, and only
after dividing by `P z * Q z` (`Projective/Point.lean`'s `nonsingular_add`,
which routes through the affine model and therefore needs `P z` and `Q z`
invertible).  The ring-level statement is absent from the pin, and
`Fermat.ProjCoords` (`ModularCurve/EllipticScheme.lean`) needs exactly it: it
is a trivialised `Proj`-coordinate datum over an arbitrary `Γ(X, ⊤)`, where
`P z` is emphatically not a unit.

## Implementation notes

The proof is a single `linear_combination` against the two curve equations,
with cofactors computed in `Singular`: reduce `W(addX, addY, addZ)` modulo
`(W(P), W(Q))` in `ℚ(a₁, …, a₆)[Px, Py, Pz, Qx, Qy, Qz]`, where the two
generators have coprime leading terms (`-Px³` and `-Qx³`) and so already form
a Gröbner basis, then `lift` to read off the cofactors.  They come out with
**130 and 186 monomials** and — this is the part that makes the statement true
over an arbitrary ring rather than only over a ℚ-algebra — with **no
denominators in the `aᵢ`**, i.e. they lie in `ℤ[a₁, …, a₆][P, Q]`.

Both sides are bihomogeneous of bidegree `(6, 6)`, so `ring1` is normalising a
large polynomial.  **That is a genuine cost of the computation, not a resource
bump hiding a defect.**

## Why this is its own module (integration, 2026-07-28)

It was split out of `ProjectiveAddition.lean`, which holds the SECOND
Bosma–Lenstra law and which uses `equation_addXYZ` **nowhere**.  Elaboration is
single-threaded per file, and that file carried two independent multi-minute
`ring1`/`linear_combination` normalisations — this one and
`add2Y_neg_left_ne_zero_of_dblZ_eq_zero` — so they were paid in SERIES on one
core, 4173 s together at the release-10 measurement, which put the pair at the
head of the whole build's critical path.  As two sibling modules, both imported
by their single consumer `ModularCurve/EllipticScheme.lean`, they elaborate
concurrently and the path pays only the larger of the two.

**So do not merge this back into `ProjectiveAddition.lean`, and do not make
either module import the other.**  Their being siblings is the point.
-/

@[expose] public section

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve R} {P Q : Fin 3 → R}

set_option maxHeartbeats 4000000 in
/-- **The chord–tangent triple again satisfies the Weierstrass equation**,
over an arbitrary commutative ring (PROVEN).

`W(addX P Q, addY P Q, addZ P Q) = A · W(P) + B · W(Q)` with `A`, `B` in
`ℤ[a₁, …, a₆][P, Q]`; see the module docstring for how the two cofactors were
obtained and verified. -/
theorem equation_addXYZ (hP : Equation W' P) (hQ : Equation W' Q) :
    Equation W' (addXYZ W' P Q) := by
  rw [equation_iff] at hP hQ ⊢
  simp only [addXYZ_X, addXYZ_Y, addXYZ_Z, addY, negY_eq, addX, negAddY, addZ]
  linear_combination
    (9 * P 0 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 ^ 4 + (-3 * W'.a₁ ^ 2 + 3 * W'.a₂) * P 2 ^ 3 * Q 0 ^ 2 * Q 1 ^ 4 +
      (-3 * W'.a₁) * P 2 ^ 3 * Q 0 * Q 1 ^ 5 - P 2 ^ 3 * Q 1 ^ 6 + (-36 * W'.a₁) * P 0 ^ 2 *
      P 2 * Q 0 ^ 2 * Q 1 ^ 3 * Q 2 + 36 * P 0 * P 1 * P 2 * Q 0 ^ 2 * Q 1 ^ 3 * Q 2 + (6 *
      W'.a₁ ^ 3 - 36 * W'.a₁ * W'.a₂ + 36 * W'.a₃) * P 0 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 ^ 3 * Q 2 +
      (-12 * W'.a₁ ^ 2 + 12 * W'.a₂) * P 1 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 ^ 3 * Q 2 + (4 * W'.a₁ ^ 3 *
      W'.a₂ - 6 * W'.a₁ ^ 2 * W'.a₃ - 12 * W'.a₁ * W'.a₂ ^ 2 + 12 * W'.a₁ * W'.a₄ + 12 *
      W'.a₂ * W'.a₃) * P 2 ^ 3 * Q 0 ^ 2 * Q 1 ^ 3 * Q 2 - 27 * P 0 ^ 2 * P 2 * Q 0 * Q 1 ^ 4 *
      Q 2 + (21 * W'.a₁ ^ 2 - 12 * W'.a₂) * P 0 * P 2 ^ 2 * Q 0 * Q 1 ^ 4 * Q 2 + (-15 *
      W'.a₁) * P 1 * P 2 ^ 2 * Q 0 * Q 1 ^ 4 * Q 2 + (-W'.a₁ ^ 4 + 9 * W'.a₁ ^ 2 * W'.a₂ -
      12 * W'.a₁ * W'.a₃ - 3 * W'.a₂ ^ 2 + 6 * W'.a₄) * P 2 ^ 3 * Q 0 * Q 1 ^ 4 * Q 2 + (15 *
      W'.a₁) * P 0 * P 2 ^ 2 * Q 1 ^ 5 * Q 2 - 6 * P 1 * P 2 ^ 2 * Q 1 ^ 5 * Q 2 + (-W'.a₁ ^ 3 +
      6 * W'.a₁ * W'.a₂ - 6 * W'.a₃) * P 2 ^ 3 * Q 1 ^ 5 * Q 2 + (9 * W'.a₁ ^ 2) * P 0 ^ 3 *
      Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 + (-45 * W'.a₁) * P 0 ^ 2 * P 1 * Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 +
      36 * P 0 * P 1 ^ 2 * Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 + (24 * W'.a₁ ^ 2 * W'.a₂ - 45 *
      W'.a₁ * W'.a₃ - 21 * W'.a₂ ^ 2 + 63 * W'.a₄) * P 0 ^ 2 * P 2 * Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 +
      (12 * W'.a₁ ^ 3 - 60 * W'.a₁ * W'.a₂ + 90 * W'.a₃) * P 0 * P 1 * P 2 * Q 0 ^ 2 * Q 1 ^ 2 *
      Q 2 ^ 2 + (-15 * W'.a₁ ^ 2 + 12 * W'.a₂) * P 1 ^ 2 * P 2 * Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 +
      (27 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 30 * W'.a₁ ^ 2 * W'.a₄ - 54 * W'.a₁ * W'.a₂ * W'.a₃ - 18 *
      W'.a₂ ^ 3 + 60 * W'.a₂ * W'.a₄ + 36 * W'.a₃ ^ 2 - 54 * W'.a₆) * P 0 * P 2 ^ 2 * Q 0 ^ 2 *
      Q 1 ^ 2 * Q 2 ^ 2 + (9 * W'.a₁ ^ 3 * W'.a₂ - 15 * W'.a₁ ^ 2 * W'.a₃ - 27 * W'.a₁ *
      W'.a₂ ^ 2 + 36 * W'.a₁ * W'.a₄ + 30 * W'.a₂ * W'.a₃) * P 1 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 ^ 2 *
      Q 2 ^ 2 + (10 * W'.a₁ ^ 2 * W'.a₂ ^ 3 - 21 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ + 9 * W'.a₁ ^ 2 *
      W'.a₆ - 21 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 24 * W'.a₁ * W'.a₃ * W'.a₄ - 5 * W'.a₂ ^ 4 +
      21 * W'.a₂ ^ 2 * W'.a₄ + 12 * W'.a₂ * W'.a₃ ^ 2 - 18 * W'.a₂ * W'.a₆ - 12 * W'.a₄ ^ 2) *
      P 2 ^ 3 * Q 0 ^ 2 * Q 1 ^ 2 * Q 2 ^ 2 + (27 * W'.a₁) * P 0 ^ 3 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 -
      54 * P 0 ^ 2 * P 1 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 + (-12 * W'.a₁ ^ 3 + 30 * W'.a₁ * W'.a₂ -
      81 * W'.a₃) * P 0 ^ 2 * P 2 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 + (54 * W'.a₁ ^ 2 - 12 * W'.a₂) *
      P 0 * P 1 * P 2 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 + (-24 * W'.a₁) * P 1 ^ 2 * P 2 * Q 0 * Q 1 ^ 3 *
      Q 2 ^ 2 + (-15 * W'.a₁ ^ 3 * W'.a₂ + 33 * W'.a₁ ^ 2 * W'.a₃ + 27 * W'.a₁ * W'.a₂ ^ 2 -
      72 * W'.a₁ * W'.a₄ - 30 * W'.a₂ * W'.a₃) * P 0 * P 2 ^ 2 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 +
      (-3 * W'.a₁ ^ 4 + 24 * W'.a₁ ^ 2 * W'.a₂ - 42 * W'.a₁ * W'.a₃ - 6 * W'.a₂ ^ 2 + 24 *
      W'.a₄) * P 1 * P 2 ^ 2 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 + (-6 * W'.a₁ ^ 3 * W'.a₂ ^ 2 + 7 *
      W'.a₁ ^ 3 * W'.a₄ + 15 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ + 8 * W'.a₁ * W'.a₂ ^ 3 - 30 *
      W'.a₁ * W'.a₂ * W'.a₄ - 12 * W'.a₁ * W'.a₃ ^ 2 + 18 * W'.a₁ * W'.a₆ - 9 * W'.a₂ ^ 2 *
      W'.a₃ + 24 * W'.a₃ * W'.a₄) * P 2 ^ 3 * Q 0 * Q 1 ^ 3 * Q 2 ^ 2 + 27 * P 0 ^ 3 * Q 1 ^ 4 *
      Q 2 ^ 2 + (-12 * W'.a₁ ^ 2 + 18 * W'.a₂) * P 0 ^ 2 * P 2 * Q 1 ^ 4 * Q 2 ^ 2 + (42 *
      W'.a₁) * P 0 * P 1 * P 2 * Q 1 ^ 4 * Q 2 ^ 2 - 12 * P 1 ^ 2 * P 2 * Q 1 ^ 4 * Q 2 ^ 2 +
      (-15 * W'.a₁ ^ 2 * W'.a₂ + 42 * W'.a₁ * W'.a₃ + 15 * W'.a₂ ^ 2 - 33 * W'.a₄) * P 0 * P 2 ^ 2 *
      Q 1 ^ 4 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 3 + 18 * W'.a₁ * W'.a₂ - 27 * W'.a₃) * P 1 * P 2 ^ 2 *
      Q 1 ^ 4 * Q 2 ^ 2 + (-W'.a₁ ^ 3 * W'.a₃ - 6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 6 * W'.a₁ ^ 2 *
      W'.a₄ + 18 * W'.a₁ * W'.a₂ * W'.a₃ + 4 * W'.a₂ ^ 3 - 12 * W'.a₂ * W'.a₄ - 12 * W'.a₃ ^ 2 +
      9 * W'.a₆) * P 2 ^ 3 * Q 1 ^ 4 * Q 2 ^ 2 + (6 * W'.a₁ * W'.a₂ ^ 2 - 18 * W'.a₁ *
      W'.a₄) * P 0 ^ 3 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (12 * W'.a₁ ^ 2 * W'.a₂ - 36 * W'.a₁ *
      W'.a₃ - 6 * W'.a₂ ^ 2 + 18 * W'.a₄) * P 0 ^ 2 * P 1 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (6 *
      W'.a₁ ^ 3 - 12 * W'.a₁ * W'.a₂ + 36 * W'.a₃) * P 0 * P 1 ^ 2 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 +
      (-6 * W'.a₁ ^ 2) * P 1 ^ 3 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (18 * W'.a₁ * W'.a₂ ^ 3 - 60 *
      W'.a₁ * W'.a₂ * W'.a₄ + 54 * W'.a₁ * W'.a₆ - 24 * W'.a₂ ^ 2 * W'.a₃ + 72 * W'.a₃ *
      W'.a₄) * P 0 ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (24 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 36 *
      W'.a₁ ^ 2 * W'.a₄ - 48 * W'.a₁ * W'.a₂ * W'.a₃ - 12 * W'.a₂ ^ 3 + 48 * W'.a₂ * W'.a₄ +
      36 * W'.a₃ ^ 2 - 108 * W'.a₆) * P 0 * P 1 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (6 * W'.a₁ ^ 3 *
      W'.a₂ - 12 * W'.a₁ ^ 2 * W'.a₃ - 12 * W'.a₁ * W'.a₂ ^ 2 + 24 * W'.a₁ * W'.a₄ + 12 *
      W'.a₂ * W'.a₃) * P 1 ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (18 * W'.a₁ * W'.a₂ ^ 4 -
      78 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ + 72 * W'.a₁ * W'.a₂ * W'.a₆ + 48 * W'.a₁ * W'.a₄ ^ 2 -
      24 * W'.a₂ ^ 3 * W'.a₃ + 84 * W'.a₂ * W'.a₃ * W'.a₄ - 108 * W'.a₃ * W'.a₆) * P 0 * P 2 ^ 2 *
      Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (12 * W'.a₁ ^ 2 * W'.a₂ ^ 3 - 30 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ +
      18 * W'.a₁ ^ 2 * W'.a₆ - 24 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 36 * W'.a₁ * W'.a₃ * W'.a₄ -
      6 * W'.a₂ ^ 4 + 30 * W'.a₂ ^ 2 * W'.a₄ + 12 * W'.a₂ * W'.a₃ ^ 2 - 36 * W'.a₂ * W'.a₆ -
      24 * W'.a₄ ^ 2) * P 1 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 * Q 2 ^ 3 + (6 * W'.a₁ * W'.a₂ ^ 5 -
      32 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ + 30 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ + 36 * W'.a₁ * W'.a₂ *
      W'.a₄ ^ 2 - 36 * W'.a₁ * W'.a₄ * W'.a₆ - 8 * W'.a₂ ^ 4 * W'.a₃ + 36 * W'.a₂ ^ 2 *
      W'.a₃ * W'.a₄ - 36 * W'.a₂ * W'.a₃ * W'.a₆ - 24 * W'.a₃ * W'.a₄ ^ 2) * P 2 ^ 3 * Q 0 ^ 2 *
      Q 1 * Q 2 ^ 3 + (-3 * W'.a₁ ^ 2 * W'.a₂ + 27 * W'.a₁ * W'.a₃ + 9 * W'.a₂ ^ 2 - 27 *
      W'.a₄) * P 0 ^ 3 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 + (-12 * W'.a₁ ^ 3 - 3 * W'.a₁ * W'.a₂ - 81 *
      W'.a₃) * P 0 ^ 2 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 + (33 * W'.a₁ ^ 2 + 24 * W'.a₂) * P 0 *
      P 1 ^ 2 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 + (-12 * W'.a₁) * P 1 ^ 3 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 +
      (-15 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 48 * W'.a₁ ^ 2 * W'.a₄ + 33 * W'.a₁ * W'.a₂ * W'.a₃ + 3 *
      W'.a₂ ^ 3 - 21 * W'.a₂ * W'.a₄ - 54 * W'.a₃ ^ 2 + 108 * W'.a₆) * P 0 ^ 2 * P 2 * Q 0 *
      Q 1 ^ 2 * Q 2 ^ 3 + (-18 * W'.a₁ ^ 3 * W'.a₂ + 54 * W'.a₁ ^ 2 * W'.a₃ + 18 * W'.a₁ *
      W'.a₂ ^ 2 - 120 * W'.a₁ * W'.a₄ + 6 * W'.a₂ * W'.a₃) * P 0 * P 1 * P 2 * Q 0 * Q 1 ^ 2 *
      Q 2 ^ 3 + (-3 * W'.a₁ ^ 4 + 15 * W'.a₁ ^ 2 * W'.a₂ - 42 * W'.a₁ * W'.a₃ + 24 * W'.a₄) *
      P 1 ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 + (-15 * W'.a₁ ^ 2 * W'.a₂ ^ 3 + 63 * W'.a₁ ^ 2 *
      W'.a₂ * W'.a₄ - 45 * W'.a₁ ^ 2 * W'.a₆ + 33 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ - 108 * W'.a₁ *
      W'.a₃ * W'.a₄ + 3 * W'.a₂ ^ 4 - 33 * W'.a₂ ^ 2 * W'.a₄ - 12 * W'.a₂ * W'.a₃ ^ 2 + 36 *
      W'.a₂ * W'.a₆ + 60 * W'.a₄ ^ 2) * P 0 * P 2 ^ 2 * Q 0 * Q 1 ^ 2 * Q 2 ^ 3 + (-9 *
      W'.a₁ ^ 3 * W'.a₂ ^ 2 + 15 * W'.a₁ ^ 3 * W'.a₄ + 24 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ + 9 *
      W'.a₁ * W'.a₂ ^ 3 - 54 * W'.a₁ * W'.a₂ * W'.a₄ - 24 * W'.a₁ * W'.a₃ ^ 2 + 54 * W'.a₁ *
      W'.a₆ - 9 * W'.a₂ ^ 2 * W'.a₃ + 60 * W'.a₃ * W'.a₄) * P 1 * P 2 ^ 2 * Q 0 * Q 1 ^ 2 *
      Q 2 ^ 3 + (-5 * W'.a₁ ^ 2 * W'.a₂ ^ 4 + 27 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ - 21 *
      W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 18 * W'.a₁ ^ 2 * W'.a₄ ^ 2 + 11 * W'.a₁ * W'.a₂ ^ 3 *
      W'.a₃ - 48 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ + 36 * W'.a₁ * W'.a₃ * W'.a₆ + W'.a₂ ^ 5 -
      11 * W'.a₂ ^ 3 * W'.a₄ - 6 * W'.a₂ ^ 2 * W'.a₃ ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₆ + 24 *
      W'.a₂ * W'.a₄ ^ 2 + 24 * W'.a₃ ^ 2 * W'.a₄ - 36 * W'.a₄ * W'.a₆) * P 2 ^ 3 * Q 0 * Q 1 ^ 2 *
      Q 2 ^ 3 + (-W'.a₁ ^ 3 - 9 * W'.a₁ * W'.a₂ + 54 * W'.a₃) * P 0 ^ 3 * Q 1 ^ 3 * Q 2 ^ 3 +
      (-15 * W'.a₁ ^ 2 - 18 * W'.a₂) * P 0 ^ 2 * P 1 * Q 1 ^ 3 * Q 2 ^ 3 + (24 * W'.a₁) * P 0 *
      P 1 ^ 2 * Q 1 ^ 3 * Q 2 ^ 3 - 8 * P 1 ^ 3 * Q 1 ^ 3 * Q 2 ^ 3 + (-15 * W'.a₁ ^ 2 *
      W'.a₃ - 15 * W'.a₁ * W'.a₂ ^ 2 + 33 * W'.a₁ * W'.a₄ + 27 * W'.a₂ * W'.a₃) * P 0 ^ 2 *
      P 2 * Q 1 ^ 3 * Q 2 ^ 3 + (-18 * W'.a₁ ^ 2 * W'.a₂ + 78 * W'.a₁ * W'.a₃ + 12 * W'.a₂ ^ 2 -
      60 * W'.a₄) * P 0 * P 1 * P 2 * Q 1 ^ 3 * Q 2 ^ 3 + (-3 * W'.a₁ ^ 3 + 12 * W'.a₁ *
      W'.a₂ - 36 * W'.a₃) * P 1 ^ 2 * P 2 * Q 1 ^ 3 * Q 2 ^ 3 + (-15 * W'.a₁ ^ 2 * W'.a₂ *
      W'.a₃ - 15 * W'.a₁ * W'.a₂ ^ 3 + 48 * W'.a₁ * W'.a₂ * W'.a₄ + 24 * W'.a₁ * W'.a₃ ^ 2 -
      54 * W'.a₁ * W'.a₆ + 36 * W'.a₂ ^ 2 * W'.a₃ - 96 * W'.a₃ * W'.a₄) * P 0 * P 2 ^ 2 * Q 1 ^ 3 *
      Q 2 ^ 3 + (-3 * W'.a₁ ^ 3 * W'.a₃ - 9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 12 * W'.a₁ ^ 2 * W'.a₄ +
      36 * W'.a₁ * W'.a₂ * W'.a₃ + 6 * W'.a₂ ^ 3 - 24 * W'.a₂ * W'.a₄ - 36 * W'.a₃ ^ 2 + 36 *
      W'.a₆) * P 1 * P 2 ^ 2 * Q 1 ^ 3 * Q 2 ^ 3 + (W'.a₁ ^ 3 * W'.a₆ - 6 * W'.a₁ ^ 2 *
      W'.a₂ ^ 2 * W'.a₃ + 6 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ - 5 * W'.a₁ * W'.a₂ ^ 4 + 21 * W'.a₁ *
      W'.a₂ ^ 2 * W'.a₄ + 12 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 - 24 * W'.a₁ * W'.a₂ * W'.a₆ - 12 *
      W'.a₁ * W'.a₄ ^ 2 + 11 * W'.a₂ ^ 3 * W'.a₃ - 36 * W'.a₂ * W'.a₃ * W'.a₄ - 8 * W'.a₃ ^ 3 +
      36 * W'.a₃ * W'.a₆) * P 2 ^ 3 * Q 1 ^ 3 * Q 2 ^ 3 + (W'.a₂ ^ 4 - 6 * W'.a₂ ^ 2 * W'.a₄ +
      9 * W'.a₄ ^ 2) * P 0 ^ 3 * Q 0 ^ 2 * Q 2 ^ 4 + (3 * W'.a₁ * W'.a₂ ^ 3 - 12 * W'.a₁ *
      W'.a₂ * W'.a₄ + 27 * W'.a₁ * W'.a₆ - 3 * W'.a₂ ^ 2 * W'.a₃ + 9 * W'.a₃ * W'.a₄) * P 0 ^ 2 *
      P 1 * Q 0 ^ 2 * Q 2 ^ 4 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 6 * W'.a₁ ^ 2 * W'.a₄ - 6 *
      W'.a₁ * W'.a₂ * W'.a₃ + 9 * W'.a₃ ^ 2) * P 0 * P 1 ^ 2 * Q 0 ^ 2 * Q 2 ^ 4 + (W'.a₁ ^ 3 *
      W'.a₂ - 3 * W'.a₁ ^ 2 * W'.a₃) * P 1 ^ 3 * Q 0 ^ 2 * Q 2 ^ 4 + (3 * W'.a₂ ^ 5 - 21 *
      W'.a₂ ^ 3 * W'.a₄ + 27 * W'.a₂ ^ 2 * W'.a₆ + 36 * W'.a₂ * W'.a₄ ^ 2 - 81 * W'.a₄ *
      W'.a₆) * P 0 ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 4 + (6 * W'.a₁ * W'.a₂ ^ 4 - 30 * W'.a₁ *
      W'.a₂ ^ 2 * W'.a₄ + 36 * W'.a₁ * W'.a₂ * W'.a₆ + 24 * W'.a₁ * W'.a₄ ^ 2 - 6 * W'.a₂ ^ 3 *
      W'.a₃ + 24 * W'.a₂ * W'.a₃ * W'.a₄ - 54 * W'.a₃ * W'.a₆) * P 0 * P 1 * P 2 * Q 0 ^ 2 *
      Q 2 ^ 4 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 3 - 9 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ + 9 * W'.a₁ ^ 2 *
      W'.a₆ - 6 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 12 * W'.a₁ * W'.a₃ * W'.a₄ + 3 * W'.a₂ * W'.a₃ ^ 2) *
      P 1 ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 4 + (3 * W'.a₂ ^ 6 - 24 * W'.a₂ ^ 4 * W'.a₄ + 30 *
      W'.a₂ ^ 3 * W'.a₆ + 54 * W'.a₂ ^ 2 * W'.a₄ ^ 2 - 108 * W'.a₂ * W'.a₄ * W'.a₆ - 24 *
      W'.a₄ ^ 3 + 81 * W'.a₆ ^ 2) * P 0 * P 2 ^ 2 * Q 0 ^ 2 * Q 2 ^ 4 + (3 * W'.a₁ * W'.a₂ ^ 5 -
      18 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ + 21 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ + 24 * W'.a₁ * W'.a₂ *
      W'.a₄ ^ 2 - 36 * W'.a₁ * W'.a₄ * W'.a₆ - 3 * W'.a₂ ^ 4 * W'.a₃ + 15 * W'.a₂ ^ 2 *
      W'.a₃ * W'.a₄ - 18 * W'.a₂ * W'.a₃ * W'.a₆ - 12 * W'.a₃ * W'.a₄ ^ 2) * P 1 * P 2 ^ 2 *
      Q 0 ^ 2 * Q 2 ^ 4 + (W'.a₂ ^ 7 - 9 * W'.a₂ ^ 5 * W'.a₄ + 11 * W'.a₂ ^ 4 * W'.a₆ + 25 *
      W'.a₂ ^ 3 * W'.a₄ ^ 2 - 51 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ - 20 * W'.a₂ * W'.a₄ ^ 3 + 27 *
      W'.a₂ * W'.a₆ ^ 2 + 36 * W'.a₄ ^ 2 * W'.a₆) * P 2 ^ 3 * Q 0 ^ 2 * Q 2 ^ 4 + (-W'.a₁ *
      W'.a₂ ^ 3 + 6 * W'.a₁ * W'.a₂ * W'.a₄ - 27 * W'.a₁ * W'.a₆ + 9 * W'.a₂ ^ 2 * W'.a₃ -
      27 * W'.a₃ * W'.a₄) * P 0 ^ 3 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 24 *
      W'.a₁ ^ 2 * W'.a₄ - 6 * W'.a₁ * W'.a₂ * W'.a₃ - 6 * W'.a₂ * W'.a₄ - 27 * W'.a₃ ^ 2 +
      54 * W'.a₆) * P 0 ^ 2 * P 1 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 * W'.a₁ ^ 3 * W'.a₂ + 21 *
      W'.a₁ ^ 2 * W'.a₃ - 24 * W'.a₁ * W'.a₄ + 24 * W'.a₂ * W'.a₃) * P 0 * P 1 ^ 2 * Q 0 * Q 1 *
      Q 2 ^ 4 + (-W'.a₁ ^ 4 - 12 * W'.a₁ * W'.a₃) * P 1 ^ 3 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 *
      W'.a₁ * W'.a₂ ^ 4 + 33 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ - 36 * W'.a₁ * W'.a₂ * W'.a₆ - 60 *
      W'.a₁ * W'.a₄ ^ 2 + 3 * W'.a₂ ^ 3 * W'.a₃ - 24 * W'.a₂ * W'.a₃ * W'.a₄ + 135 * W'.a₃ *
      W'.a₆) * P 0 ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 4 + (-6 * W'.a₁ ^ 2 * W'.a₂ ^ 3 + 42 *
      W'.a₁ ^ 2 * W'.a₂ * W'.a₄ - 54 * W'.a₁ ^ 2 * W'.a₆ + 12 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ -
      96 * W'.a₁ * W'.a₃ * W'.a₄ - 12 * W'.a₂ ^ 2 * W'.a₄ + 6 * W'.a₂ * W'.a₃ ^ 2 - 36 *
      W'.a₂ * W'.a₆ + 48 * W'.a₄ ^ 2) * P 0 * P 1 * P 2 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 * W'.a₁ ^ 3 *
      W'.a₂ ^ 2 + 9 * W'.a₁ ^ 3 * W'.a₄ + 9 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ - 12 * W'.a₁ * W'.a₂ *
      W'.a₄ - 15 * W'.a₁ * W'.a₃ ^ 2 + 36 * W'.a₁ * W'.a₆ + 24 * W'.a₃ * W'.a₄) * P 1 ^ 2 *
      P 2 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 * W'.a₁ * W'.a₂ ^ 5 + 36 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ -
      39 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ - 84 * W'.a₁ * W'.a₂ * W'.a₄ ^ 2 + 144 * W'.a₁ * W'.a₄ *
      W'.a₆ + 3 * W'.a₂ ^ 4 * W'.a₃ - 39 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 18 * W'.a₂ * W'.a₃ *
      W'.a₆ + 84 * W'.a₃ * W'.a₄ ^ 2) * P 0 * P 2 ^ 2 * Q 0 * Q 1 * Q 2 ^ 4 + (-3 * W'.a₁ ^ 2 *
      W'.a₂ ^ 4 + 24 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ - 24 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 24 *
      W'.a₁ ^ 2 * W'.a₄ ^ 2 + 6 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ - 42 * W'.a₁ * W'.a₂ * W'.a₃ *
      W'.a₄ + 54 * W'.a₁ * W'.a₃ * W'.a₆ - 6 * W'.a₂ ^ 3 * W'.a₄ - 3 * W'.a₂ ^ 2 * W'.a₃ ^ 2 +
      6 * W'.a₂ ^ 2 * W'.a₆ + 24 * W'.a₂ * W'.a₄ ^ 2 + 24 * W'.a₃ ^ 2 * W'.a₄ - 72 * W'.a₄ *
      W'.a₆) * P 1 * P 2 ^ 2 * Q 0 * Q 1 * Q 2 ^ 4 + (-W'.a₁ * W'.a₂ ^ 6 + 13 * W'.a₁ *
      W'.a₂ ^ 4 * W'.a₄ - 14 * W'.a₁ * W'.a₂ ^ 3 * W'.a₆ - 39 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ ^ 2 +
      66 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ + 20 * W'.a₁ * W'.a₄ ^ 3 - 27 * W'.a₁ * W'.a₆ ^ 2 +
      W'.a₂ ^ 5 * W'.a₃ - 14 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄ + 15 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ +
      36 * W'.a₂ * W'.a₃ * W'.a₄ ^ 2 - 72 * W'.a₃ * W'.a₄ * W'.a₆) * P 2 ^ 3 * Q 0 * Q 1 * Q 2 ^ 4 +
      (3 * W'.a₁ ^ 2 * W'.a₄ - 9 * W'.a₁ * W'.a₂ * W'.a₃ - W'.a₂ ^ 3 + 9 * W'.a₂ * W'.a₄ +
      27 * W'.a₃ ^ 2 - 54 * W'.a₆) * P 0 ^ 3 * Q 1 ^ 2 * Q 2 ^ 4 + (-12 * W'.a₁ ^ 2 * W'.a₃ -
      3 * W'.a₁ * W'.a₂ ^ 2 + 21 * W'.a₁ * W'.a₄ - 27 * W'.a₂ * W'.a₃) * P 0 ^ 2 * P 1 * Q 1 ^ 2 *
      Q 2 ^ 4 + (-3 * W'.a₁ ^ 2 * W'.a₂ + 42 * W'.a₁ * W'.a₃ + 12 * W'.a₄) * P 0 * P 1 ^ 2 *
      Q 1 ^ 2 * Q 2 ^ 4 + (-W'.a₁ ^ 3 - 12 * W'.a₃) * P 1 ^ 3 * Q 1 ^ 2 * Q 2 ^ 4 + (18 *
      W'.a₁ ^ 2 * W'.a₆ - 15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 39 * W'.a₁ * W'.a₃ * W'.a₄ - 3 *
      W'.a₂ ^ 4 + 18 * W'.a₂ ^ 2 * W'.a₄ + 9 * W'.a₂ * W'.a₃ ^ 2 - 18 * W'.a₂ * W'.a₆ - 21 *
      W'.a₄ ^ 2) * P 0 ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 4 + (-18 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ - 6 *
      W'.a₁ * W'.a₂ ^ 3 + 24 * W'.a₁ * W'.a₂ * W'.a₄ + 42 * W'.a₁ * W'.a₃ ^ 2 - 72 * W'.a₁ *
      W'.a₆ + 18 * W'.a₂ ^ 2 * W'.a₃ - 78 * W'.a₃ * W'.a₄) * P 0 * P 1 * P 2 * Q 1 ^ 2 * Q 2 ^ 4 +
      (-3 * W'.a₁ ^ 3 * W'.a₃ - 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 6 * W'.a₁ ^ 2 * W'.a₄ + 18 *
      W'.a₁ * W'.a₂ * W'.a₃ - 27 * W'.a₃ ^ 2 + 36 * W'.a₆) * P 1 ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 4 +
      (15 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 15 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ + 48 * W'.a₁ * W'.a₂ *
      W'.a₃ * W'.a₄ - 54 * W'.a₁ * W'.a₃ * W'.a₆ - 3 * W'.a₂ ^ 5 + 21 * W'.a₂ ^ 3 * W'.a₄ +
      21 * W'.a₂ ^ 2 * W'.a₃ ^ 2 - 42 * W'.a₂ ^ 2 * W'.a₆ - 36 * W'.a₂ * W'.a₄ ^ 2 - 60 *
      W'.a₃ ^ 2 * W'.a₄ + 126 * W'.a₄ * W'.a₆) * P 0 * P 2 ^ 2 * Q 1 ^ 2 * Q 2 ^ 4 + (3 *
      W'.a₁ ^ 3 * W'.a₆ - 9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ + 12 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ -
      3 * W'.a₁ * W'.a₂ ^ 4 + 15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ + 18 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 -
      36 * W'.a₁ * W'.a₂ * W'.a₆ - 12 * W'.a₁ * W'.a₄ ^ 2 + 9 * W'.a₂ ^ 3 * W'.a₃ - 36 *
      W'.a₂ * W'.a₃ * W'.a₄ - 12 * W'.a₃ ^ 3 + 90 * W'.a₃ * W'.a₆) * P 1 * P 2 ^ 2 * Q 1 ^ 2 *
      Q 2 ^ 4 + (6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆ - 6 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ - 5 *
      W'.a₁ * W'.a₂ ^ 4 * W'.a₃ + 21 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ - 30 * W'.a₁ *
      W'.a₂ * W'.a₃ * W'.a₆ - 12 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 - W'.a₂ ^ 6 + 8 * W'.a₂ ^ 4 *
      W'.a₄ + 7 * W'.a₂ ^ 3 * W'.a₃ ^ 2 - 14 * W'.a₂ ^ 3 * W'.a₆ - 18 * W'.a₂ ^ 2 * W'.a₄ ^ 2 -
      24 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ + 48 * W'.a₂ * W'.a₄ * W'.a₆ + 36 * W'.a₃ ^ 2 * W'.a₆ +
      8 * W'.a₄ ^ 3 - 27 * W'.a₆ ^ 2) * P 2 ^ 3 * Q 1 ^ 2 * Q 2 ^ 4 + (W'.a₂ ^ 3 * W'.a₄ - 9 *
      W'.a₂ ^ 2 * W'.a₆ - 3 * W'.a₂ * W'.a₄ ^ 2 + 27 * W'.a₄ * W'.a₆) * P 0 ^ 3 * Q 0 * Q 2 ^ 5 +
      (3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ + 9 * W'.a₁ * W'.a₂ * W'.a₆ - 12 * W'.a₁ * W'.a₄ ^ 2 -
      3 * W'.a₂ * W'.a₃ * W'.a₄ + 27 * W'.a₃ * W'.a₆) * P 0 ^ 2 * P 1 * Q 0 * Q 2 ^ 5 + (3 *
      W'.a₁ ^ 2 * W'.a₂ * W'.a₄ - 9 * W'.a₁ ^ 2 * W'.a₆ - 12 * W'.a₁ * W'.a₃ * W'.a₄ + 6 *
      W'.a₂ * W'.a₃ ^ 2) * P 0 * P 1 ^ 2 * Q 0 * Q 2 ^ 5 + (W'.a₁ ^ 3 * W'.a₄ - 3 * W'.a₁ *
      W'.a₃ ^ 2) * P 1 ^ 3 * Q 0 * Q 2 ^ 5 + (3 * W'.a₂ ^ 4 * W'.a₄ - 3 * W'.a₂ ^ 3 * W'.a₆ -
      18 * W'.a₂ ^ 2 * W'.a₄ ^ 2 + 27 * W'.a₂ * W'.a₄ * W'.a₆ + 24 * W'.a₄ ^ 3 - 81 * W'.a₆ ^ 2) *
      P 0 ^ 2 * P 2 * Q 0 * Q 2 ^ 5 + (6 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ - 6 * W'.a₁ * W'.a₂ ^ 2 *
      W'.a₆ - 24 * W'.a₁ * W'.a₂ * W'.a₄ ^ 2 + 72 * W'.a₁ * W'.a₄ * W'.a₆ - 6 * W'.a₂ ^ 2 *
      W'.a₃ * W'.a₄ - 18 * W'.a₂ * W'.a₃ * W'.a₆ + 24 * W'.a₃ * W'.a₄ ^ 2) * P 0 * P 1 * P 2 *
      Q 0 * Q 2 ^ 5 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ - 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 6 *
      W'.a₁ ^ 2 * W'.a₄ ^ 2 - 6 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ + 18 * W'.a₁ * W'.a₃ * W'.a₆ +
      6 * W'.a₃ ^ 2 * W'.a₄) * P 1 ^ 2 * P 2 * Q 0 * Q 2 ^ 5 + (3 * W'.a₂ ^ 5 * W'.a₄ - 3 *
      W'.a₂ ^ 4 * W'.a₆ - 21 * W'.a₂ ^ 3 * W'.a₄ ^ 2 + 45 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ + 36 *
      W'.a₂ * W'.a₄ ^ 3 - 108 * W'.a₄ ^ 2 * W'.a₆) * P 0 * P 2 ^ 2 * Q 0 * Q 2 ^ 5 + (3 *
      W'.a₁ * W'.a₂ ^ 4 * W'.a₄ - 3 * W'.a₁ * W'.a₂ ^ 3 * W'.a₆ - 15 * W'.a₁ * W'.a₂ ^ 2 *
      W'.a₄ ^ 2 + 30 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ + 12 * W'.a₁ * W'.a₄ ^ 3 - 27 * W'.a₁ *
      W'.a₆ ^ 2 - 3 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄ + 3 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ + 12 * W'.a₂ *
      W'.a₃ * W'.a₄ ^ 2 - 36 * W'.a₃ * W'.a₄ * W'.a₆) * P 1 * P 2 ^ 2 * Q 0 * Q 2 ^ 5 +
      (W'.a₂ ^ 6 * W'.a₄ - W'.a₂ ^ 5 * W'.a₆ - 8 * W'.a₂ ^ 4 * W'.a₄ ^ 2 + 17 * W'.a₂ ^ 3 *
      W'.a₄ * W'.a₆ + 18 * W'.a₂ ^ 2 * W'.a₄ ^ 3 - 9 * W'.a₂ ^ 2 * W'.a₆ ^ 2 - 48 * W'.a₂ *
      W'.a₄ ^ 2 * W'.a₆ - 8 * W'.a₄ ^ 4 + 54 * W'.a₄ * W'.a₆ ^ 2) * P 2 ^ 3 * Q 0 * Q 2 ^ 5 +
      (9 * W'.a₁ * W'.a₂ * W'.a₆ - 3 * W'.a₁ * W'.a₄ ^ 2 - W'.a₂ ^ 3 * W'.a₃ + 9 * W'.a₂ *
      W'.a₃ * W'.a₄ - 54 * W'.a₃ * W'.a₆) * P 0 ^ 3 * Q 1 * Q 2 ^ 5 + (9 * W'.a₁ ^ 2 * W'.a₆ -
      3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 15 * W'.a₁ * W'.a₃ * W'.a₄ - 9 * W'.a₂ * W'.a₃ ^ 2 +
      18 * W'.a₂ * W'.a₆ - 6 * W'.a₄ ^ 2) * P 0 ^ 2 * P 1 * Q 1 * Q 2 ^ 5 + (-3 * W'.a₁ ^ 2 *
      W'.a₂ * W'.a₃ + 15 * W'.a₁ * W'.a₃ ^ 2 - 36 * W'.a₁ * W'.a₆ + 12 * W'.a₃ * W'.a₄) * P 0 *
      P 1 ^ 2 * Q 1 * Q 2 ^ 5 + (-W'.a₁ ^ 3 * W'.a₃ - 6 * W'.a₃ ^ 2) * P 1 ^ 3 * Q 1 * Q 2 ^ 5 +
      (15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ - 45 * W'.a₁ * W'.a₄ * W'.a₆ - 3 * W'.a₂ ^ 4 * W'.a₃ +
      18 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ - 9 * W'.a₂ * W'.a₃ * W'.a₆ - 24 * W'.a₃ * W'.a₄ ^ 2) *
      P 0 ^ 2 * P 2 * Q 1 * Q 2 ^ 5 + (18 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 6 * W'.a₁ * W'.a₂ ^ 3 *
      W'.a₃ + 24 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ - 90 * W'.a₁ * W'.a₃ * W'.a₆ + 6 * W'.a₂ ^ 2 *
      W'.a₃ ^ 2 - 12 * W'.a₂ ^ 2 * W'.a₆ - 24 * W'.a₃ ^ 2 * W'.a₄ + 36 * W'.a₄ * W'.a₆) * P 0 *
      P 1 * P 2 * Q 1 * Q 2 ^ 5 + (3 * W'.a₁ ^ 3 * W'.a₆ - 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ +
      6 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ + 6 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 - 12 * W'.a₁ * W'.a₂ *
      W'.a₆ - 6 * W'.a₃ ^ 3 + 36 * W'.a₃ * W'.a₆) * P 1 ^ 2 * P 2 * Q 1 * Q 2 ^ 5 + (15 *
      W'.a₁ * W'.a₂ ^ 3 * W'.a₆ - 48 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ + 27 * W'.a₁ * W'.a₆ ^ 2 -
      3 * W'.a₂ ^ 5 * W'.a₃ + 21 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄ - 48 * W'.a₂ ^ 2 * W'.a₃ *
      W'.a₆ - 36 * W'.a₂ * W'.a₃ * W'.a₄ ^ 2 + 144 * W'.a₃ * W'.a₄ * W'.a₆) * P 0 * P 2 ^ 2 *
      Q 1 * Q 2 ^ 5 + (9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆ - 12 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ -
      3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ + 15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ - 36 * W'.a₁ *
      W'.a₂ * W'.a₃ * W'.a₆ - 12 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 + 3 * W'.a₂ ^ 3 * W'.a₃ ^ 2 - 6 *
      W'.a₂ ^ 3 * W'.a₆ - 12 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ + 24 * W'.a₂ * W'.a₄ * W'.a₆ + 36 *
      W'.a₃ ^ 2 * W'.a₆ - 54 * W'.a₆ ^ 2) * P 1 * P 2 ^ 2 * Q 1 * Q 2 ^ 5 + (5 * W'.a₁ *
      W'.a₂ ^ 4 * W'.a₆ - 21 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ + 18 * W'.a₁ * W'.a₂ *
      W'.a₆ ^ 2 + 12 * W'.a₁ * W'.a₄ ^ 2 * W'.a₆ - W'.a₂ ^ 6 * W'.a₃ + 8 * W'.a₂ ^ 4 * W'.a₃ *
      W'.a₄ - 17 * W'.a₂ ^ 3 * W'.a₃ * W'.a₆ - 18 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ ^ 2 + 60 *
      W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆ + 8 * W'.a₃ * W'.a₄ ^ 3 - 54 * W'.a₃ * W'.a₆ ^ 2) * P 2 ^ 3 *
      Q 1 * Q 2 ^ 5 + (W'.a₂ ^ 3 * W'.a₆ - 9 * W'.a₂ * W'.a₄ * W'.a₆ + W'.a₄ ^ 3 + 27 *
      W'.a₆ ^ 2) * P 0 ^ 3 * Q 2 ^ 6 + (3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ - 9 * W'.a₁ * W'.a₄ *
      W'.a₆ + 9 * W'.a₂ * W'.a₃ * W'.a₆ - 3 * W'.a₃ * W'.a₄ ^ 2) * P 0 ^ 2 * P 1 * Q 2 ^ 6 +
      (3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 18 * W'.a₁ * W'.a₃ * W'.a₆ + 3 * W'.a₃ ^ 2 * W'.a₄) *
      P 0 * P 1 ^ 2 * Q 2 ^ 6 + (W'.a₁ ^ 3 * W'.a₆ - W'.a₃ ^ 3) * P 1 ^ 3 * Q 2 ^ 6 + (3 *
      W'.a₂ ^ 4 * W'.a₆ - 18 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ + 27 * W'.a₄ ^ 2 * W'.a₆) * P 0 ^ 2 *
      P 2 * Q 2 ^ 6 + (6 * W'.a₁ * W'.a₂ ^ 3 * W'.a₆ - 24 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ +
      54 * W'.a₁ * W'.a₆ ^ 2 - 6 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ + 18 * W'.a₃ * W'.a₄ * W'.a₆) *
      P 0 * P 1 * P 2 * Q 2 ^ 6 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆ - 6 * W'.a₁ ^ 2 * W'.a₄ *
      W'.a₆ - 6 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ + 9 * W'.a₃ ^ 2 * W'.a₆) * P 1 ^ 2 * P 2 * Q 2 ^ 6 +
      (3 * W'.a₂ ^ 5 * W'.a₆ - 21 * W'.a₂ ^ 3 * W'.a₄ * W'.a₆ + 27 * W'.a₂ ^ 2 * W'.a₆ ^ 2 +
      36 * W'.a₂ * W'.a₄ ^ 2 * W'.a₆ - 81 * W'.a₄ * W'.a₆ ^ 2) * P 0 * P 2 ^ 2 * Q 2 ^ 6 +
      (3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₆ - 15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ + 18 * W'.a₁ *
      W'.a₂ * W'.a₆ ^ 2 + 12 * W'.a₁ * W'.a₄ ^ 2 * W'.a₆ - 3 * W'.a₂ ^ 3 * W'.a₃ * W'.a₆ +
      12 * W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆ - 27 * W'.a₃ * W'.a₆ ^ 2) * P 1 * P 2 ^ 2 * Q 2 ^ 6 +
      (W'.a₂ ^ 6 * W'.a₆ - 8 * W'.a₂ ^ 4 * W'.a₄ * W'.a₆ + 10 * W'.a₂ ^ 3 * W'.a₆ ^ 2 + 18 *
      W'.a₂ ^ 2 * W'.a₄ ^ 2 * W'.a₆ - 36 * W'.a₂ * W'.a₄ * W'.a₆ ^ 2 - 8 * W'.a₄ ^ 3 * W'.a₆ +
      27 * W'.a₆ ^ 3) * P 2 ^ 3 * Q 2 ^ 6) * hP +
    (- 27 * P 0 ^ 3 * P 1 ^ 2 * P 2 * Q 0 ^ 3 + (9 * W'.a₁ * W'.a₂ - 27 * W'.a₃) * P 0 ^ 3 * P 1 *
      P 2 ^ 2 * Q 0 ^ 3 + (-9 * W'.a₁ ^ 2 - 27 * W'.a₂) * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0 ^ 3 +
      (2 * W'.a₂ ^ 3 - 9 * W'.a₂ * W'.a₄ + 27 * W'.a₆) * P 0 ^ 3 * P 2 ^ 3 * Q 0 ^ 3 + (3 *
      W'.a₁ * W'.a₂ ^ 2 + 18 * W'.a₁ * W'.a₄ - 27 * W'.a₂ * W'.a₃) * P 0 ^ 2 * P 1 * P 2 ^ 3 *
      Q 0 ^ 3 + (-6 * W'.a₁ ^ 2 * W'.a₂ - 9 * W'.a₂ ^ 2) * P 0 * P 1 ^ 2 * P 2 ^ 3 * Q 0 ^ 3 +
      (W'.a₁ ^ 3) * P 1 ^ 3 * P 2 ^ 3 * Q 0 ^ 3 + (W'.a₂ ^ 4 - 3 * W'.a₂ ^ 2 * W'.a₄ + 27 *
      W'.a₂ * W'.a₆ - 9 * W'.a₄ ^ 2) * P 0 ^ 2 * P 2 ^ 4 * Q 0 ^ 3 + (-W'.a₁ * W'.a₂ ^ 3 +
      12 * W'.a₁ * W'.a₂ * W'.a₄ - 9 * W'.a₂ ^ 2 * W'.a₃) * P 0 * P 1 * P 2 ^ 4 * Q 0 ^ 3 +
      (-3 * W'.a₁ ^ 2 * W'.a₄ - W'.a₂ ^ 3) * P 1 ^ 2 * P 2 ^ 4 * Q 0 ^ 3 + (W'.a₂ ^ 3 *
      W'.a₄ + 9 * W'.a₂ ^ 2 * W'.a₆ - 6 * W'.a₂ * W'.a₄ ^ 2) * P 0 * P 2 ^ 5 * Q 0 ^ 3 + (3 *
      W'.a₁ * W'.a₄ ^ 2 - W'.a₂ ^ 3 * W'.a₃) * P 1 * P 2 ^ 5 * Q 0 ^ 3 + (W'.a₂ ^ 3 * W'.a₆ -
      W'.a₄ ^ 3) * P 2 ^ 6 * Q 0 ^ 3 + 54 * P 0 ^ 4 * P 1 * P 2 * Q 0 ^ 2 * Q 1 + (-9 *
      W'.a₁ * W'.a₂ + 27 * W'.a₃) * P 0 ^ 4 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 + (9 * W'.a₁ ^ 2 + 72 *
      W'.a₂) * P 0 ^ 3 * P 1 * P 2 ^ 2 * Q 0 ^ 2 * Q 1 + (-9 * W'.a₁) * P 0 ^ 2 * P 1 ^ 2 *
      P 2 ^ 2 * Q 0 ^ 2 * Q 1 + (-9 * W'.a₁ * W'.a₂ ^ 2 - 9 * W'.a₁ * W'.a₄ + 36 * W'.a₂ *
      W'.a₃) * P 0 ^ 3 * P 2 ^ 3 * Q 0 ^ 2 * Q 1 + (6 * W'.a₁ ^ 2 * W'.a₂ + 9 * W'.a₁ *
      W'.a₃ + 24 * W'.a₂ ^ 2 + 36 * W'.a₄) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 0 ^ 2 * Q 1 + (3 *
      W'.a₁ ^ 3 - 6 * W'.a₁ * W'.a₂) * P 0 * P 1 ^ 2 * P 2 ^ 3 * Q 0 ^ 2 * Q 1 + (6 * W'.a₁ ^ 2) *
      P 1 ^ 3 * P 2 ^ 3 * Q 0 ^ 2 * Q 1 + (-3 * W'.a₁ * W'.a₂ ^ 3 - 6 * W'.a₁ * W'.a₂ *
      W'.a₄ - 27 * W'.a₁ * W'.a₆ + 12 * W'.a₂ ^ 2 * W'.a₃ + 18 * W'.a₃ * W'.a₄) * P 0 ^ 2 *
      P 2 ^ 4 * Q 0 ^ 2 * Q 1 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 6 * W'.a₁ ^ 2 * W'.a₄ + 6 *
      W'.a₁ * W'.a₂ * W'.a₃ + 24 * W'.a₂ * W'.a₄) * P 0 * P 1 * P 2 ^ 4 * Q 0 ^ 2 * Q 1 + (3 *
      W'.a₁ ^ 2 * W'.a₃ + 3 * W'.a₁ * W'.a₂ ^ 2 - 12 * W'.a₁ * W'.a₄) * P 1 ^ 2 * P 2 ^ 4 *
      Q 0 ^ 2 * Q 1 + (-3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ - 18 * W'.a₁ * W'.a₂ * W'.a₆ + 3 *
      W'.a₁ * W'.a₄ ^ 2 + 12 * W'.a₂ * W'.a₃ * W'.a₄) * P 0 * P 2 ^ 5 * Q 0 ^ 2 * Q 1 + (3 *
      W'.a₁ * W'.a₂ ^ 2 * W'.a₃ - 6 * W'.a₁ * W'.a₃ * W'.a₄ + 6 * W'.a₄ ^ 2) * P 1 * P 2 ^ 5 *
      Q 0 ^ 2 * Q 1 + (-3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ + 3 * W'.a₃ * W'.a₄ ^ 2) * P 2 ^ 6 * Q 0 ^ 2 *
      Q 1 - 27 * P 0 ^ 5 * P 2 * Q 0 * Q 1 ^ 2 + (-45 * W'.a₂) * P 0 ^ 4 * P 2 ^ 2 * Q 0 * Q 1 ^ 2 +
      (-9 * W'.a₁) * P 0 ^ 3 * P 1 * P 2 ^ 2 * Q 0 * Q 1 ^ 2 - 9 * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 *
      Q 0 * Q 1 ^ 2 + (6 * W'.a₁ ^ 2 * W'.a₂ - 18 * W'.a₁ * W'.a₃ - 21 * W'.a₂ ^ 2 - 27 *
      W'.a₄) * P 0 ^ 3 * P 2 ^ 3 * Q 0 * Q 1 ^ 2 + (-6 * W'.a₁ ^ 3 - 6 * W'.a₁ * W'.a₂ - 9 *
      W'.a₃) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 0 * Q 1 ^ 2 + (3 * W'.a₁ ^ 2 - 6 * W'.a₂) * P 0 *
      P 1 ^ 2 * P 2 ^ 3 * Q 0 * Q 1 ^ 2 + (12 * W'.a₁) * P 1 ^ 3 * P 2 ^ 3 * Q 0 * Q 1 ^ 2 +
      (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 6 * W'.a₁ ^ 2 * W'.a₄ - 12 * W'.a₁ * W'.a₂ * W'.a₃ - 3 *
      W'.a₂ ^ 3 - 18 * W'.a₂ * W'.a₄ - 9 * W'.a₃ ^ 2 - 27 * W'.a₆) * P 0 ^ 2 * P 2 ^ 4 * Q 0 *
      Q 1 ^ 2 + (-3 * W'.a₁ ^ 3 * W'.a₂ - 3 * W'.a₁ ^ 2 * W'.a₃ + 3 * W'.a₁ * W'.a₂ ^ 2 - 12 *
      W'.a₁ * W'.a₄ - 6 * W'.a₂ * W'.a₃) * P 0 * P 1 * P 2 ^ 4 * Q 0 * Q 1 ^ 2 + (-3 * W'.a₁ ^ 2 *
      W'.a₂ + 12 * W'.a₁ * W'.a₃ + 3 * W'.a₂ ^ 2 - 12 * W'.a₄) * P 1 ^ 2 * P 2 ^ 4 * Q 0 * Q 1 ^ 2 +
      (3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ + 9 * W'.a₁ ^ 2 * W'.a₆ - 6 * W'.a₁ * W'.a₃ * W'.a₄ - 3 *
      W'.a₂ ^ 2 * W'.a₄ - 6 * W'.a₂ * W'.a₃ ^ 2 - 18 * W'.a₂ * W'.a₆) * P 0 * P 2 ^ 5 * Q 0 *
      Q 1 ^ 2 + (-3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ + 3 * W'.a₁ * W'.a₃ ^ 2 + 3 * W'.a₂ ^ 2 *
      W'.a₃ - 12 * W'.a₃ * W'.a₄) * P 1 * P 2 ^ 5 * Q 0 * Q 1 ^ 2 + (3 * W'.a₁ ^ 2 * W'.a₂ *
      W'.a₆ - 3 * W'.a₂ ^ 2 * W'.a₆ - 3 * W'.a₃ ^ 2 * W'.a₄) * P 2 ^ 6 * Q 0 * Q 1 ^ 2 + (18 *
      W'.a₁) * P 0 ^ 4 * P 2 ^ 2 * Q 1 ^ 3 + (24 * W'.a₁ * W'.a₂) * P 0 ^ 3 * P 2 ^ 3 * Q 1 ^ 3 +
      (-12 * W'.a₁ ^ 2) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 1 ^ 3 + (-6 * W'.a₁) * P 0 * P 1 ^ 2 *
      P 2 ^ 3 * Q 1 ^ 3 + 8 * P 1 ^ 3 * P 2 ^ 3 * Q 1 ^ 3 + (-W'.a₁ ^ 3 * W'.a₂ + 3 * W'.a₁ ^ 2 *
      W'.a₃ + 6 * W'.a₁ * W'.a₂ ^ 2 + 18 * W'.a₁ * W'.a₄) * P 0 ^ 2 * P 2 ^ 4 * Q 1 ^ 3 +
      (W'.a₁ ^ 4 - 6 * W'.a₁ ^ 2 * W'.a₂ - 6 * W'.a₁ * W'.a₃) * P 0 * P 1 * P 2 ^ 4 * Q 1 ^ 3 +
      (W'.a₁ ^ 3 - 6 * W'.a₁ * W'.a₂ + 12 * W'.a₃) * P 1 ^ 2 * P 2 ^ 4 * Q 1 ^ 3 + (-W'.a₁ ^ 3 *
      W'.a₄ + 6 * W'.a₁ * W'.a₂ * W'.a₄ + 3 * W'.a₁ * W'.a₃ ^ 2 + 18 * W'.a₁ * W'.a₆) * P 0 *
      P 2 ^ 5 * Q 1 ^ 3 + (W'.a₁ ^ 3 * W'.a₃ - 6 * W'.a₁ * W'.a₂ * W'.a₃ + 6 * W'.a₃ ^ 2) *
      P 1 * P 2 ^ 5 * Q 1 ^ 3 + (-W'.a₁ ^ 3 * W'.a₆ + 6 * W'.a₁ * W'.a₂ * W'.a₆ + W'.a₃ ^ 3) *
      P 2 ^ 6 * Q 1 ^ 3 + 27 * P 0 ^ 4 * P 1 ^ 2 * Q 0 ^ 2 * Q 2 + (-18 * W'.a₁ * W'.a₂ + 54 *
      W'.a₃) * P 0 ^ 4 * P 1 * P 2 * Q 0 ^ 2 * Q 2 + (9 * W'.a₁ ^ 2 + 9 * W'.a₂) * P 0 ^ 3 *
      P 1 ^ 2 * P 2 * Q 0 ^ 2 * Q 2 + (9 * W'.a₁) * P 0 ^ 2 * P 1 ^ 3 * P 2 * Q 0 ^ 2 * Q 2 +
      (-6 * W'.a₂ ^ 3 + 27 * W'.a₂ * W'.a₄ - 81 * W'.a₆) * P 0 ^ 4 * P 2 ^ 2 * Q 0 ^ 2 * Q 2 +
      (-6 * W'.a₁ * W'.a₂ ^ 2 - 27 * W'.a₁ * W'.a₄ + 45 * W'.a₂ * W'.a₃) * P 0 ^ 3 * P 1 * P 2 ^ 2 *
      Q 0 ^ 2 * Q 2 + (3 * W'.a₁ ^ 2 * W'.a₂ - 9 * W'.a₁ * W'.a₃ + 3 * W'.a₂ ^ 2 - 36 *
      W'.a₄) * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0 ^ 2 * Q 2 + (3 * W'.a₁ ^ 3 + 6 * W'.a₁ *
      W'.a₂) * P 0 * P 1 ^ 3 * P 2 ^ 2 * Q 0 ^ 2 * Q 2 + (3 * W'.a₁ ^ 2) * P 1 ^ 4 * P 2 ^ 2 *
      Q 0 ^ 2 * Q 2 + (-4 * W'.a₂ ^ 4 + 15 * W'.a₂ ^ 2 * W'.a₄ - 81 * W'.a₂ * W'.a₆ + 18 *
      W'.a₄ ^ 2) * P 0 ^ 3 * P 2 ^ 3 * Q 0 ^ 2 * Q 2 + (-12 * W'.a₁ * W'.a₂ * W'.a₄ + 27 *
      W'.a₁ * W'.a₆ + 15 * W'.a₂ ^ 2 * W'.a₃ - 18 * W'.a₃ * W'.a₄) * P 0 ^ 2 * P 1 * P 2 ^ 3 *
      Q 0 ^ 2 * Q 2 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 12 * W'.a₁ ^ 2 * W'.a₄ - 6 * W'.a₁ *
      W'.a₂ * W'.a₃ + 3 * W'.a₂ ^ 3 - 24 * W'.a₂ * W'.a₄) * P 0 * P 1 ^ 2 * P 2 ^ 3 * Q 0 ^ 2 *
      Q 2 + (6 * W'.a₁ ^ 2 * W'.a₃ + 3 * W'.a₁ * W'.a₂ ^ 2 - 6 * W'.a₁ * W'.a₄) * P 1 ^ 3 *
      P 2 ^ 3 * Q 0 ^ 2 * Q 2 + (-W'.a₂ ^ 5 + 3 * W'.a₂ ^ 3 * W'.a₄ - 27 * W'.a₂ ^ 2 * W'.a₆ +
      9 * W'.a₂ * W'.a₄ ^ 2) * P 0 ^ 2 * P 2 ^ 4 * Q 0 ^ 2 * Q 2 + (W'.a₁ * W'.a₂ ^ 4 - 9 *
      W'.a₁ * W'.a₂ ^ 2 * W'.a₄ + 18 * W'.a₁ * W'.a₂ * W'.a₆ + 15 * W'.a₁ * W'.a₄ ^ 2 + 3 *
      W'.a₂ ^ 3 * W'.a₃ - 12 * W'.a₂ * W'.a₃ * W'.a₄) * P 0 * P 1 * P 2 ^ 4 * Q 0 ^ 2 * Q 2 +
      (-9 * W'.a₁ ^ 2 * W'.a₆ + 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ - 12 * W'.a₁ * W'.a₃ * W'.a₄ +
      W'.a₂ ^ 4 - 6 * W'.a₂ ^ 2 * W'.a₄ + 3 * W'.a₄ ^ 2) * P 1 ^ 2 * P 2 ^ 4 * Q 0 ^ 2 * Q 2 +
      (-W'.a₂ ^ 4 * W'.a₄ - 3 * W'.a₂ ^ 3 * W'.a₆ + 6 * W'.a₂ ^ 2 * W'.a₄ ^ 2 - 6 * W'.a₄ ^ 3) *
      P 0 * P 2 ^ 5 * Q 0 ^ 2 * Q 2 + (-3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ + 18 * W'.a₁ * W'.a₄ *
      W'.a₆ + W'.a₂ ^ 4 * W'.a₃ - 6 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 6 * W'.a₃ * W'.a₄ ^ 2) * P 1 *
      P 2 ^ 5 * Q 0 ^ 2 * Q 2 + (-W'.a₂ ^ 4 * W'.a₆ + 6 * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ - 9 *
      W'.a₄ ^ 2 * W'.a₆) * P 2 ^ 6 * Q 0 ^ 2 * Q 2 - 54 * P 0 ^ 5 * P 1 * Q 0 * Q 1 * Q 2 +
      (18 * W'.a₁ * W'.a₂ - 54 * W'.a₃) * P 0 ^ 5 * P 2 * Q 0 * Q 1 * Q 2 + (-54 * W'.a₂) *
      P 0 ^ 4 * P 1 * P 2 * Q 0 * Q 1 * Q 2 + 18 * P 0 ^ 2 * P 1 ^ 3 * P 2 * Q 0 * Q 1 * Q 2 +
      (24 * W'.a₁ * W'.a₂ ^ 2 - 72 * W'.a₂ * W'.a₃) * P 0 ^ 4 * P 2 ^ 2 * Q 0 * Q 1 * Q 2 +
      (6 * W'.a₁ ^ 2 * W'.a₂ - 18 * W'.a₂ ^ 2 + 18 * W'.a₄) * P 0 ^ 3 * P 1 * P 2 ^ 2 * Q 0 *
      Q 1 * Q 2 + (-12 * W'.a₁ ^ 3 - 12 * W'.a₁ * W'.a₂ + 18 * W'.a₃) * P 0 ^ 2 * P 1 ^ 2 *
      P 2 ^ 2 * Q 0 * Q 1 * Q 2 + (12 * W'.a₂) * P 0 * P 1 ^ 3 * P 2 ^ 2 * Q 0 * Q 1 * Q 2 +
      (12 * W'.a₁) * P 1 ^ 4 * P 2 ^ 2 * Q 0 * Q 1 * Q 2 + (16 * W'.a₁ * W'.a₂ ^ 3 - 18 *
      W'.a₁ * W'.a₂ * W'.a₄ + 54 * W'.a₁ * W'.a₆ - 30 * W'.a₂ ^ 2 * W'.a₃ - 18 * W'.a₃ *
      W'.a₄) * P 0 ^ 3 * P 2 ^ 3 * Q 0 * Q 1 * Q 2 + (-6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 36 *
      W'.a₁ ^ 2 * W'.a₄ - 6 * W'.a₁ * W'.a₂ * W'.a₃ - 6 * W'.a₂ ^ 3 + 24 * W'.a₂ * W'.a₄ +
      18 * W'.a₃ ^ 2 + 54 * W'.a₆) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 0 * Q 1 * Q 2 + (-6 * W'.a₁ ^ 3 *
      W'.a₂ - 6 * W'.a₁ * W'.a₂ ^ 2 - 6 * W'.a₁ * W'.a₄ + 12 * W'.a₂ * W'.a₃) * P 0 * P 1 ^ 2 *
      P 2 ^ 3 * Q 0 * Q 1 * Q 2 + (-6 * W'.a₁ ^ 2 * W'.a₂ + 30 * W'.a₁ * W'.a₃ + 6 * W'.a₂ ^ 2 -
      12 * W'.a₄) * P 1 ^ 3 * P 2 ^ 3 * Q 0 * Q 1 * Q 2 + (4 * W'.a₁ * W'.a₂ ^ 4 + 36 *
      W'.a₁ * W'.a₂ * W'.a₆ - 24 * W'.a₁ * W'.a₄ ^ 2 - 6 * W'.a₂ ^ 3 * W'.a₃ - 6 * W'.a₂ *
      W'.a₃ * W'.a₄) * P 0 ^ 2 * P 2 ^ 4 * Q 0 * Q 1 * Q 2 + (-4 * W'.a₁ ^ 2 * W'.a₂ ^ 3 +
      18 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ - 6 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 6 * W'.a₁ * W'.a₃ *
      W'.a₄ - 6 * W'.a₂ ^ 2 * W'.a₄ + 12 * W'.a₂ * W'.a₃ ^ 2 + 36 * W'.a₂ * W'.a₆ + 24 *
      W'.a₄ ^ 2) * P 0 * P 1 * P 2 ^ 4 * Q 0 * Q 1 * Q 2 + (-6 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ -
      4 * W'.a₁ * W'.a₂ ^ 3 + 12 * W'.a₁ * W'.a₂ * W'.a₄ + 12 * W'.a₁ * W'.a₃ ^ 2 - 36 *
      W'.a₁ * W'.a₆ + 12 * W'.a₂ ^ 2 * W'.a₃ - 30 * W'.a₃ * W'.a₄) * P 1 ^ 2 * P 2 ^ 4 * Q 0 *
      Q 1 * Q 2 + (4 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ + 12 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ - 12 *
      W'.a₁ * W'.a₂ * W'.a₄ ^ 2 - 18 * W'.a₁ * W'.a₄ * W'.a₆ - 6 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ +
      12 * W'.a₃ * W'.a₄ ^ 2) * P 0 * P 2 ^ 5 * Q 0 * Q 1 * Q 2 + (6 * W'.a₁ ^ 2 * W'.a₂ *
      W'.a₆ - 4 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ + 12 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ - 18 *
      W'.a₁ * W'.a₃ * W'.a₆ + 6 * W'.a₂ ^ 2 * W'.a₃ ^ 2 - 6 * W'.a₂ ^ 2 * W'.a₆ - 12 * W'.a₃ ^ 2 *
      W'.a₄ + 36 * W'.a₄ * W'.a₆) * P 1 * P 2 ^ 5 * Q 0 * Q 1 * Q 2 + (4 * W'.a₁ * W'.a₂ ^ 3 *
      W'.a₆ - 12 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ - 6 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ + 18 *
      W'.a₃ * W'.a₄ * W'.a₆) * P 2 ^ 6 * Q 0 * Q 1 * Q 2 + 27 * P 0 ^ 6 * Q 1 ^ 2 * Q 2 +
      (-9 * W'.a₁ ^ 2 + 45 * W'.a₂) * P 0 ^ 5 * P 2 * Q 1 ^ 2 * Q 2 + (27 * W'.a₁) * P 0 ^ 4 *
      P 1 * P 2 * Q 1 ^ 2 * Q 2 - 27 * P 0 ^ 3 * P 1 ^ 2 * P 2 * Q 1 ^ 2 * Q 2 + (-27 *
      W'.a₁ ^ 2 * W'.a₂ + 36 * W'.a₁ * W'.a₃ + 33 * W'.a₂ ^ 2 - 9 * W'.a₄) * P 0 ^ 4 * P 2 ^ 2 *
      Q 1 ^ 2 * Q 2 + (9 * W'.a₁ ^ 3 + 42 * W'.a₁ * W'.a₂ - 27 * W'.a₃) * P 0 ^ 3 * P 1 * P 2 ^ 2 *
      Q 1 ^ 2 * Q 2 + (-30 * W'.a₁ ^ 2 - 30 * W'.a₂) * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 1 ^ 2 *
      Q 2 + (-30 * W'.a₁) * P 0 * P 1 ^ 3 * P 2 ^ 2 * Q 1 ^ 2 * Q 2 + 12 * P 1 ^ 4 * P 2 ^ 2 *
      Q 1 ^ 2 * Q 2 + (-21 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 9 * W'.a₁ ^ 2 * W'.a₄ + 42 * W'.a₁ *
      W'.a₂ * W'.a₃ + 19 * W'.a₂ ^ 3 - 30 * W'.a₂ * W'.a₄ + 27 * W'.a₆) * P 0 ^ 3 * P 2 ^ 3 *
      Q 1 ^ 2 * Q 2 + (12 * W'.a₁ ^ 3 * W'.a₂ - 15 * W'.a₁ ^ 2 * W'.a₃ + 3 * W'.a₁ * W'.a₂ ^ 2 +
      66 * W'.a₁ * W'.a₄ - 30 * W'.a₂ * W'.a₃) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 1 ^ 2 * Q 2 +
      (3 * W'.a₁ ^ 4 - 3 * W'.a₁ ^ 2 * W'.a₂ - 48 * W'.a₁ * W'.a₃ - 15 * W'.a₂ ^ 2 + 12 *
      W'.a₄) * P 0 * P 1 ^ 2 * P 2 ^ 3 * Q 1 ^ 2 * Q 2 + (3 * W'.a₁ ^ 3 - 18 * W'.a₁ * W'.a₂ +
      36 * W'.a₃) * P 1 ^ 3 * P 2 ^ 3 * Q 1 ^ 2 * Q 2 + (-6 * W'.a₁ ^ 2 * W'.a₂ ^ 3 - 9 *
      W'.a₁ ^ 2 * W'.a₂ * W'.a₄ - 18 * W'.a₁ ^ 2 * W'.a₆ + 12 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ +
      24 * W'.a₁ * W'.a₃ * W'.a₄ + 4 * W'.a₂ ^ 4 + 3 * W'.a₂ ^ 2 * W'.a₄ - 3 * W'.a₂ * W'.a₃ ^ 2 +
      18 * W'.a₂ * W'.a₆ - 36 * W'.a₄ ^ 2) * P 0 ^ 2 * P 2 ^ 4 * Q 1 ^ 2 * Q 2 + (6 * W'.a₁ ^ 3 *
      W'.a₂ ^ 2 - 9 * W'.a₁ ^ 3 * W'.a₄ + 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ - 4 * W'.a₁ * W'.a₂ ^ 3 +
      30 * W'.a₁ * W'.a₂ * W'.a₄ - 21 * W'.a₁ * W'.a₃ ^ 2 + 18 * W'.a₁ * W'.a₆ - 15 * W'.a₂ ^ 2 *
      W'.a₃ + 12 * W'.a₃ * W'.a₄) * P 0 * P 1 * P 2 ^ 4 * Q 1 ^ 2 * Q 2 + (3 * W'.a₁ ^ 3 *
      W'.a₃ + 6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 6 * W'.a₁ ^ 2 * W'.a₄ - 30 * W'.a₁ * W'.a₂ * W'.a₃ -
      4 * W'.a₂ ^ 3 + 12 * W'.a₂ * W'.a₄ + 27 * W'.a₃ ^ 2 - 36 * W'.a₆) * P 1 ^ 2 * P 2 ^ 4 *
      Q 1 ^ 2 * Q 2 + (-6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₄ - 15 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ +
      6 * W'.a₁ ^ 2 * W'.a₄ ^ 2 + 12 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ + 18 * W'.a₁ * W'.a₃ *
      W'.a₆ + 4 * W'.a₂ ^ 3 * W'.a₄ + 15 * W'.a₂ ^ 2 * W'.a₆ - 12 * W'.a₂ * W'.a₄ ^ 2 - 6 *
      W'.a₃ ^ 2 * W'.a₄ - 36 * W'.a₄ * W'.a₆) * P 0 * P 2 ^ 5 * Q 1 ^ 2 * Q 2 + (-3 * W'.a₁ ^ 3 *
      W'.a₆ + 6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₃ - 6 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ - 12 * W'.a₁ *
      W'.a₂ * W'.a₃ ^ 2 + 18 * W'.a₁ * W'.a₂ * W'.a₆ - 4 * W'.a₂ ^ 3 * W'.a₃ + 12 * W'.a₂ *
      W'.a₃ * W'.a₄ + 6 * W'.a₃ ^ 3 - 36 * W'.a₃ * W'.a₆) * P 1 * P 2 ^ 5 * Q 1 ^ 2 * Q 2 +
      (-6 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * W'.a₆ + 6 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ + 12 * W'.a₁ *
      W'.a₂ * W'.a₃ * W'.a₆ + 4 * W'.a₂ ^ 3 * W'.a₆ - 12 * W'.a₂ * W'.a₄ * W'.a₆ - 9 * W'.a₃ ^ 2 *
      W'.a₆) * P 2 ^ 6 * Q 1 ^ 2 * Q 2 + (9 * W'.a₁ * W'.a₂ - 27 * W'.a₃) * P 0 ^ 5 * P 1 *
      Q 0 * Q 2 ^ 2 + (18 * W'.a₂) * P 0 ^ 4 * P 1 ^ 2 * Q 0 * Q 2 ^ 2 + (-18 * W'.a₁) * P 0 ^ 3 *
      P 1 ^ 3 * Q 0 * Q 2 ^ 2 - 9 * P 0 ^ 2 * P 1 ^ 4 * Q 0 * Q 2 ^ 2 + (6 * W'.a₂ ^ 3 - 27 *
      W'.a₂ * W'.a₄ + 81 * W'.a₆) * P 0 ^ 5 * P 2 * Q 0 * Q 2 ^ 2 + (3 * W'.a₁ * W'.a₂ ^ 2 -
      9 * W'.a₂ * W'.a₃) * P 0 ^ 4 * P 1 * P 2 * Q 0 * Q 2 ^ 2 + (9 * W'.a₁ ^ 2 * W'.a₂ - 9 *
      W'.a₁ * W'.a₃ + 3 * W'.a₂ ^ 2 + 36 * W'.a₄) * P 0 ^ 3 * P 1 ^ 2 * P 2 * Q 0 * Q 2 ^ 2 +
      (-6 * W'.a₁ ^ 3 - 9 * W'.a₁ * W'.a₂ - 9 * W'.a₃) * P 0 ^ 2 * P 1 ^ 3 * P 2 * Q 0 * Q 2 ^ 2 +
      (-3 * W'.a₁ ^ 2 - 6 * W'.a₂) * P 0 * P 1 ^ 4 * P 2 * Q 0 * Q 2 ^ 2 + (3 * W'.a₁) * P 1 ^ 5 *
      P 2 * Q 0 * Q 2 ^ 2 + (6 * W'.a₂ ^ 4 - 27 * W'.a₂ ^ 2 * W'.a₄ + 81 * W'.a₂ * W'.a₆) *
      P 0 ^ 4 * P 2 ^ 2 * Q 0 * Q 2 ^ 2 + (6 * W'.a₁ * W'.a₂ ^ 3 - 24 * W'.a₁ * W'.a₂ *
      W'.a₄ - 27 * W'.a₁ * W'.a₆ - 6 * W'.a₂ ^ 2 * W'.a₃ + 45 * W'.a₃ * W'.a₄) * P 0 ^ 3 * P 1 *
      P 2 ^ 2 * Q 0 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 + 30 * W'.a₁ ^ 2 * W'.a₄ - 9 *
      W'.a₁ * W'.a₂ * W'.a₃ - 3 * W'.a₂ ^ 3 + 21 * W'.a₂ * W'.a₄ - 9 * W'.a₃ ^ 2 - 27 *
      W'.a₆) * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 3 * W'.a₂ + 3 *
      W'.a₁ ^ 2 * W'.a₃ - 6 * W'.a₁ * W'.a₂ ^ 2 + 18 * W'.a₁ * W'.a₄ - 6 * W'.a₂ * W'.a₃) *
      P 0 * P 1 ^ 3 * P 2 ^ 2 * Q 0 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 2 * W'.a₂ + 12 * W'.a₁ * W'.a₃ -
      3 * W'.a₄) * P 1 ^ 4 * P 2 ^ 2 * Q 0 * Q 2 ^ 2 + (4 * W'.a₂ ^ 5 - 22 * W'.a₂ ^ 3 *
      W'.a₄ + 36 * W'.a₂ ^ 2 * W'.a₆ + 21 * W'.a₂ * W'.a₄ ^ 2 - 27 * W'.a₄ * W'.a₆) * P 0 ^ 3 *
      P 2 ^ 3 * Q 0 * Q 2 ^ 2 + (12 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ - 9 * W'.a₁ * W'.a₂ * W'.a₆ -
      48 * W'.a₁ * W'.a₄ ^ 2 - 6 * W'.a₂ ^ 3 * W'.a₃ + 33 * W'.a₂ * W'.a₃ * W'.a₄) * P 0 ^ 2 *
      P 1 * P 2 ^ 3 * Q 0 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 2 * W'.a₂ ^ 3 + 15 * W'.a₁ ^ 2 * W'.a₂ *
      W'.a₄ - 9 * W'.a₁ ^ 2 * W'.a₆ - 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ - 3 * W'.a₂ ^ 4 + 18 *
      W'.a₂ ^ 2 * W'.a₄ - 6 * W'.a₂ * W'.a₃ ^ 2 - 18 * W'.a₂ * W'.a₆ - 24 * W'.a₄ ^ 2) * P 0 *
      P 1 ^ 2 * P 2 ^ 3 * Q 0 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ - 3 * W'.a₁ *
      W'.a₂ ^ 3 + 12 * W'.a₁ * W'.a₂ * W'.a₄ + 12 * W'.a₁ * W'.a₃ ^ 2 - 18 * W'.a₁ * W'.a₆ +
      3 * W'.a₂ ^ 2 * W'.a₃ - 12 * W'.a₃ * W'.a₄) * P 1 ^ 3 * P 2 ^ 3 * Q 0 * Q 2 ^ 2 +
      (W'.a₂ ^ 6 - 4 * W'.a₂ ^ 4 * W'.a₄ + 12 * W'.a₂ ^ 3 * W'.a₆ - 6 * W'.a₂ ^ 2 * W'.a₄ ^ 2 -
      27 * W'.a₂ * W'.a₄ * W'.a₆ + 24 * W'.a₄ ^ 3) * P 0 ^ 2 * P 2 ^ 4 * Q 0 * Q 2 ^ 2 +
      (-W'.a₁ * W'.a₂ ^ 5 + 10 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ - 3 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ -
      24 * W'.a₁ * W'.a₂ * W'.a₄ ^ 2 + 18 * W'.a₁ * W'.a₄ * W'.a₆ - 3 * W'.a₂ ^ 4 * W'.a₃ +
      15 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ - 12 * W'.a₃ * W'.a₄ ^ 2) * P 0 * P 1 * P 2 ^ 4 * Q 0 *
      Q 2 ^ 2 + (3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ - 3 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ + 12 * W'.a₁ *
      W'.a₂ * W'.a₃ * W'.a₄ - 36 * W'.a₁ * W'.a₃ * W'.a₆ - W'.a₂ ^ 5 + 7 * W'.a₂ ^ 3 * W'.a₄ +
      3 * W'.a₂ ^ 2 * W'.a₃ ^ 2 - 9 * W'.a₂ ^ 2 * W'.a₆ - 12 * W'.a₂ * W'.a₄ ^ 2 - 12 *
      W'.a₃ ^ 2 * W'.a₄ + 18 * W'.a₄ * W'.a₆) * P 1 ^ 2 * P 2 ^ 4 * Q 0 * Q 2 ^ 2 + (W'.a₂ ^ 5 *
      W'.a₄ + 3 * W'.a₂ ^ 4 * W'.a₆ - 7 * W'.a₂ ^ 3 * W'.a₄ ^ 2 - 9 * W'.a₂ ^ 2 * W'.a₄ *
      W'.a₆ + 12 * W'.a₂ * W'.a₄ ^ 3) * P 0 * P 2 ^ 5 * Q 0 * Q 2 ^ 2 + (3 * W'.a₁ * W'.a₂ ^ 3 *
      W'.a₆ - 12 * W'.a₁ * W'.a₂ * W'.a₄ * W'.a₆ + 27 * W'.a₁ * W'.a₆ ^ 2 - W'.a₂ ^ 5 *
      W'.a₃ + 7 * W'.a₂ ^ 3 * W'.a₃ * W'.a₄ - 12 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ - 12 * W'.a₂ *
      W'.a₃ * W'.a₄ ^ 2 + 36 * W'.a₃ * W'.a₄ * W'.a₆) * P 1 * P 2 ^ 5 * Q 0 * Q 2 ^ 2 +
      (W'.a₂ ^ 5 * W'.a₆ - 7 * W'.a₂ ^ 3 * W'.a₄ * W'.a₆ + 9 * W'.a₂ ^ 2 * W'.a₆ ^ 2 + 12 *
      W'.a₂ * W'.a₄ ^ 2 * W'.a₆ - 27 * W'.a₄ * W'.a₆ ^ 2) * P 2 ^ 6 * Q 0 * Q 2 ^ 2 + (-9 *
      W'.a₁ * W'.a₂ + 27 * W'.a₃) * P 0 ^ 6 * Q 1 * Q 2 ^ 2 + (-9 * W'.a₁ ^ 2 - 18 * W'.a₂) *
      P 0 ^ 5 * P 1 * Q 1 * Q 2 ^ 2 + (36 * W'.a₁) * P 0 ^ 4 * P 1 ^ 2 * Q 1 * Q 2 ^ 2 +
      (-21 * W'.a₁ * W'.a₂ ^ 2 + 27 * W'.a₁ * W'.a₄ + 36 * W'.a₂ * W'.a₃) * P 0 ^ 5 * P 2 *
      Q 1 * Q 2 ^ 2 + (-24 * W'.a₁ ^ 2 * W'.a₂ + 27 * W'.a₁ * W'.a₃ - 72 * W'.a₄) * P 0 ^ 4 *
      P 1 * P 2 * Q 1 * Q 2 ^ 2 + (9 * W'.a₁ ^ 3 + 57 * W'.a₁ * W'.a₂ - 27 * W'.a₃) * P 0 ^ 3 *
      P 1 ^ 2 * P 2 * Q 1 * Q 2 ^ 2 + (-15 * W'.a₁ ^ 2 + 6 * W'.a₂) * P 0 ^ 2 * P 1 ^ 3 * P 2 *
      Q 1 * Q 2 ^ 2 + (-21 * W'.a₁) * P 0 * P 1 ^ 4 * P 2 * Q 1 * Q 2 ^ 2 + 6 * P 1 ^ 5 * P 2 *
      Q 1 * Q 2 ^ 2 + (-30 * W'.a₁ * W'.a₂ ^ 3 + 78 * W'.a₁ * W'.a₂ * W'.a₄ - 54 * W'.a₁ *
      W'.a₆ + 33 * W'.a₂ ^ 2 * W'.a₃ - 45 * W'.a₃ * W'.a₄) * P 0 ^ 4 * P 2 ^ 2 * Q 1 * Q 2 ^ 2 +
      (-12 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 36 * W'.a₁ ^ 2 * W'.a₄ + 54 * W'.a₁ * W'.a₂ * W'.a₃ +
      18 * W'.a₂ ^ 3 - 90 * W'.a₂ * W'.a₄ - 27 * W'.a₃ ^ 2) * P 0 ^ 3 * P 1 * P 2 ^ 2 * Q 1 *
      Q 2 ^ 2 + (15 * W'.a₁ ^ 3 * W'.a₂ - 30 * W'.a₁ ^ 2 * W'.a₃ + 15 * W'.a₁ * W'.a₂ ^ 2 +
      45 * W'.a₁ * W'.a₄ - 21 * W'.a₂ * W'.a₃) * P 0 ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 1 * Q 2 ^ 2 +
      (3 * W'.a₁ ^ 4 + 6 * W'.a₁ ^ 2 * W'.a₂ - 48 * W'.a₁ * W'.a₃ - 12 * W'.a₂ ^ 2 + 48 *
      W'.a₄) * P 0 * P 1 ^ 3 * P 2 ^ 2 * Q 1 * Q 2 ^ 2 + (3 * W'.a₁ ^ 3 - 12 * W'.a₁ * W'.a₂ +
      27 * W'.a₃) * P 1 ^ 4 * P 2 ^ 2 * Q 1 * Q 2 ^ 2 + (-20 * W'.a₁ * W'.a₂ ^ 4 + 54 *
      W'.a₁ * W'.a₂ ^ 2 * W'.a₄ - 63 * W'.a₁ * W'.a₂ * W'.a₆ + 27 * W'.a₁ * W'.a₄ ^ 2 + 28 *
      W'.a₂ ^ 3 * W'.a₃ - 75 * W'.a₂ * W'.a₃ * W'.a₄ + 27 * W'.a₃ * W'.a₆) * P 0 ^ 3 * P 2 ^ 3 *
      Q 1 * Q 2 ^ 2 + (6 * W'.a₁ ^ 2 * W'.a₂ ^ 3 - 54 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ + 27 *
      W'.a₁ ^ 2 * W'.a₆ + 12 * W'.a₁ * W'.a₂ ^ 2 * W'.a₃ + 63 * W'.a₁ * W'.a₃ * W'.a₄ + 6 *
      W'.a₂ ^ 4 - 12 * W'.a₂ ^ 2 * W'.a₄ - 21 * W'.a₂ * W'.a₃ ^ 2 + 18 * W'.a₂ * W'.a₆ - 48 *
      W'.a₄ ^ 2) * P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 1 * Q 2 ^ 2 + (9 * W'.a₁ ^ 3 * W'.a₂ ^ 2 - 15 *
      W'.a₁ ^ 3 * W'.a₄ + 9 * W'.a₁ * W'.a₂ ^ 3 - 12 * W'.a₁ * W'.a₂ * W'.a₄ - 30 * W'.a₁ *
      W'.a₃ ^ 2 + 36 * W'.a₁ * W'.a₆ - 33 * W'.a₂ ^ 2 * W'.a₃ + 84 * W'.a₃ * W'.a₄) * P 0 *
      P 1 ^ 2 * P 2 ^ 3 * Q 1 * Q 2 ^ 2 + (3 * W'.a₁ ^ 3 * W'.a₃ + 9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 -
      12 * W'.a₁ ^ 2 * W'.a₄ - 30 * W'.a₁ * W'.a₂ * W'.a₃ - 6 * W'.a₂ ^ 3 + 24 * W'.a₂ *
      W'.a₄ + 36 * W'.a₃ ^ 2 - 36 * W'.a₆) * P 1 ^ 3 * P 2 ^ 3 * Q 1 * Q 2 ^ 2 + (-5 * W'.a₁ *
      W'.a₂ ^ 5 + 6 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ - 33 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ + 36 *
      W'.a₁ * W'.a₂ * W'.a₄ ^ 2 + 9 * W'.a₁ * W'.a₄ * W'.a₆ + 7 * W'.a₂ ^ 4 * W'.a₃ - 3 *
      W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 27 * W'.a₂ * W'.a₃ * W'.a₆ - 60 * W'.a₃ * W'.a₄ ^ 2) * P 0 ^ 2 *
      P 2 ^ 4 * Q 1 * Q 2 ^ 2 + (5 * W'.a₁ ^ 2 * W'.a₂ ^ 4 - 30 * W'.a₁ ^ 2 * W'.a₂ ^ 2 *
      W'.a₄ + 24 * W'.a₁ ^ 2 * W'.a₄ ^ 2 + 8 * W'.a₁ * W'.a₂ ^ 3 * W'.a₃ - 6 * W'.a₁ * W'.a₂ *
      W'.a₃ * W'.a₄ + 54 * W'.a₁ * W'.a₃ * W'.a₆ + 6 * W'.a₂ ^ 3 * W'.a₄ - 21 * W'.a₂ ^ 2 *
      W'.a₃ ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₆ - 24 * W'.a₂ * W'.a₄ ^ 2 + 48 * W'.a₃ ^ 2 * W'.a₄) *
      P 0 * P 1 * P 2 ^ 4 * Q 1 * Q 2 ^ 2 + (-3 * W'.a₁ ^ 3 * W'.a₆ + 9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 *
      W'.a₃ - 12 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ + 5 * W'.a₁ * W'.a₂ ^ 4 - 21 * W'.a₁ * W'.a₂ ^ 2 *
      W'.a₄ - 18 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 + 30 * W'.a₁ * W'.a₂ * W'.a₆ + 12 * W'.a₁ *
      W'.a₄ ^ 2 - 13 * W'.a₂ ^ 3 * W'.a₃ + 48 * W'.a₂ * W'.a₃ * W'.a₄ + 12 * W'.a₃ ^ 3 - 90 *
      W'.a₃ * W'.a₆) * P 1 ^ 2 * P 2 ^ 4 * Q 1 * Q 2 ^ 2 + (-5 * W'.a₁ * W'.a₂ ^ 4 * W'.a₄ -
      15 * W'.a₁ * W'.a₂ ^ 3 * W'.a₆ + 21 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ ^ 2 + 30 * W'.a₁ *
      W'.a₂ * W'.a₄ * W'.a₆ - 12 * W'.a₁ * W'.a₄ ^ 3 - 27 * W'.a₁ * W'.a₆ ^ 2 + 7 * W'.a₂ ^ 3 *
      W'.a₃ * W'.a₄ + 21 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ - 24 * W'.a₂ * W'.a₃ * W'.a₄ ^ 2 - 36 *
      W'.a₃ * W'.a₄ * W'.a₆) * P 0 * P 2 ^ 5 * Q 1 * Q 2 ^ 2 + (-9 * W'.a₁ ^ 2 * W'.a₂ ^ 2 *
      W'.a₆ + 12 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ + 5 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ - 21 * W'.a₁ *
      W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 36 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ + 12 * W'.a₁ * W'.a₃ *
      W'.a₄ ^ 2 - 7 * W'.a₂ ^ 3 * W'.a₃ ^ 2 + 6 * W'.a₂ ^ 3 * W'.a₆ + 24 * W'.a₂ * W'.a₃ ^ 2 *
      W'.a₄ - 24 * W'.a₂ * W'.a₄ * W'.a₆ - 36 * W'.a₃ ^ 2 * W'.a₆ + 54 * W'.a₆ ^ 2) * P 1 *
      P 2 ^ 5 * Q 1 * Q 2 ^ 2 + (-5 * W'.a₁ * W'.a₂ ^ 4 * W'.a₆ + 21 * W'.a₁ * W'.a₂ ^ 2 *
      W'.a₄ * W'.a₆ - 18 * W'.a₁ * W'.a₂ * W'.a₆ ^ 2 - 12 * W'.a₁ * W'.a₄ ^ 2 * W'.a₆ + 7 *
      W'.a₂ ^ 3 * W'.a₃ * W'.a₆ - 24 * W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆ + 27 * W'.a₃ * W'.a₆ ^ 2) *
      P 2 ^ 6 * Q 1 * Q 2 ^ 2 + (-2 * W'.a₂ ^ 3 + 9 * W'.a₂ * W'.a₄ - 27 * W'.a₆) * P 0 ^ 6 *
      Q 2 ^ 3 + (9 * W'.a₁ * W'.a₄ - 9 * W'.a₂ * W'.a₃) * P 0 ^ 5 * P 1 * Q 2 ^ 3 + (-6 *
      W'.a₁ ^ 2 * W'.a₂ + 18 * W'.a₁ * W'.a₃ + 3 * W'.a₂ ^ 2) * P 0 ^ 4 * P 1 ^ 2 * Q 2 ^ 3 +
      (-6 * W'.a₁ * W'.a₂) * P 0 ^ 3 * P 1 ^ 3 * Q 2 ^ 3 + (3 * W'.a₁ ^ 2 - 3 * W'.a₂) * P 0 ^ 2 *
      P 1 ^ 4 * Q 2 ^ 3 + (3 * W'.a₁) * P 0 * P 1 ^ 5 * Q 2 ^ 3 + P 1 ^ 6 * Q 2 ^ 3 + (-4 *
      W'.a₂ ^ 4 + 21 * W'.a₂ ^ 2 * W'.a₄ - 27 * W'.a₂ * W'.a₆ - 18 * W'.a₄ ^ 2) * P 0 ^ 5 *
      P 2 * Q 2 ^ 3 + (-8 * W'.a₁ * W'.a₂ ^ 3 + 36 * W'.a₁ * W'.a₂ * W'.a₄ - 27 * W'.a₁ *
      W'.a₆ + 3 * W'.a₂ ^ 2 * W'.a₃ - 36 * W'.a₃ * W'.a₄) * P 0 ^ 4 * P 1 * P 2 * Q 2 ^ 3 +
      (-3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 9 * W'.a₁ ^ 2 * W'.a₄ + 21 * W'.a₁ * W'.a₂ * W'.a₃ +
      W'.a₂ ^ 3 + 3 * W'.a₂ * W'.a₄ + 27 * W'.a₆) * P 0 ^ 3 * P 1 ^ 2 * P 2 * Q 2 ^ 3 + (2 *
      W'.a₁ ^ 3 * W'.a₂ - 12 * W'.a₁ ^ 2 * W'.a₃ + 3 * W'.a₁ * W'.a₂ ^ 2 - 21 * W'.a₁ *
      W'.a₄ - 3 * W'.a₂ * W'.a₃) * P 0 ^ 2 * P 1 ^ 3 * P 2 * Q 2 ^ 3 + (W'.a₁ ^ 4 + 3 *
      W'.a₁ ^ 2 * W'.a₂ - 6 * W'.a₁ * W'.a₃ - 6 * W'.a₄) * P 0 * P 1 ^ 4 * P 2 * Q 2 ^ 3 +
      (W'.a₁ ^ 3 + 6 * W'.a₃) * P 1 ^ 5 * P 2 * Q 2 ^ 3 + (-6 * W'.a₂ ^ 5 + 38 * W'.a₂ ^ 3 *
      W'.a₄ - 36 * W'.a₂ ^ 2 * W'.a₆ - 57 * W'.a₂ * W'.a₄ ^ 2 + 81 * W'.a₄ * W'.a₆) * P 0 ^ 4 *
      P 2 ^ 2 * Q 2 ^ 3 + (-6 * W'.a₁ * W'.a₂ ^ 4 + 18 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ - 54 *
      W'.a₁ * W'.a₂ * W'.a₆ + 27 * W'.a₁ * W'.a₄ ^ 2 + 10 * W'.a₂ ^ 3 * W'.a₃ - 42 * W'.a₂ *
      W'.a₃ * W'.a₄ + 27 * W'.a₃ * W'.a₆) * P 0 ^ 3 * P 1 * P 2 ^ 2 * Q 2 ^ 3 + (3 * W'.a₁ ^ 2 *
      W'.a₂ ^ 3 - 21 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ + 45 * W'.a₁ ^ 2 * W'.a₆ + 3 * W'.a₁ *
      W'.a₂ ^ 2 * W'.a₃ + 21 * W'.a₁ * W'.a₃ * W'.a₄ + 3 * W'.a₂ ^ 4 - 18 * W'.a₂ ^ 2 *
      W'.a₄ - 3 * W'.a₂ * W'.a₃ ^ 2 + 18 * W'.a₂ * W'.a₆ + 30 * W'.a₄ ^ 2) * P 0 ^ 2 * P 1 ^ 2 *
      P 2 ^ 2 * Q 2 ^ 3 + (3 * W'.a₁ ^ 3 * W'.a₂ ^ 2 - 7 * W'.a₁ ^ 3 * W'.a₄ - 3 * W'.a₁ ^ 2 *
      W'.a₂ * W'.a₃ + 6 * W'.a₁ * W'.a₂ ^ 3 - 24 * W'.a₁ * W'.a₂ * W'.a₄ - 6 * W'.a₁ * W'.a₃ ^ 2 +
      36 * W'.a₁ * W'.a₆ - 6 * W'.a₂ ^ 2 * W'.a₃ + 12 * W'.a₃ * W'.a₄) * P 0 * P 1 ^ 3 * P 2 ^ 2 *
      Q 2 ^ 3 + (W'.a₁ ^ 3 * W'.a₃ + 3 * W'.a₁ ^ 2 * W'.a₂ ^ 2 - 6 * W'.a₁ ^ 2 * W'.a₄ - 6 *
      W'.a₁ * W'.a₂ * W'.a₃ + 12 * W'.a₃ ^ 2 - 9 * W'.a₆) * P 1 ^ 4 * P 2 ^ 2 * Q 2 ^ 3 +
      (-4 * W'.a₂ ^ 6 + 26 * W'.a₂ ^ 4 * W'.a₄ - 38 * W'.a₂ ^ 3 * W'.a₆ - 36 * W'.a₂ ^ 2 *
      W'.a₄ ^ 2 + 117 * W'.a₂ * W'.a₄ * W'.a₆ - 18 * W'.a₄ ^ 3 - 27 * W'.a₆ ^ 2) * P 0 ^ 3 *
      P 2 ^ 3 * Q 2 ^ 3 + (-12 * W'.a₁ * W'.a₂ ^ 3 * W'.a₄ + 6 * W'.a₁ * W'.a₂ ^ 2 * W'.a₆ +
      48 * W'.a₁ * W'.a₂ * W'.a₄ ^ 2 - 117 * W'.a₁ * W'.a₄ * W'.a₆ + 6 * W'.a₂ ^ 4 * W'.a₃ -
      24 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 27 * W'.a₂ * W'.a₃ * W'.a₆ + 6 * W'.a₃ * W'.a₄ ^ 2) *
      P 0 ^ 2 * P 1 * P 2 ^ 3 * Q 2 ^ 3 + (3 * W'.a₁ ^ 2 * W'.a₂ ^ 4 - 18 * W'.a₁ ^ 2 *
      W'.a₂ ^ 2 * W'.a₄ + 15 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ + 18 * W'.a₁ ^ 2 * W'.a₄ ^ 2 + 3 *
      W'.a₁ * W'.a₂ ^ 3 * W'.a₃ - 6 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ + 36 * W'.a₁ * W'.a₃ *
      W'.a₆ + 3 * W'.a₂ ^ 5 - 21 * W'.a₂ ^ 3 * W'.a₄ - 6 * W'.a₂ ^ 2 * W'.a₃ ^ 2 + 27 *
      W'.a₂ ^ 2 * W'.a₆ + 36 * W'.a₂ * W'.a₄ ^ 2 + 12 * W'.a₃ ^ 2 * W'.a₄ - 72 * W'.a₄ *
      W'.a₆) * P 0 * P 1 ^ 2 * P 2 ^ 3 * Q 2 ^ 3 + (-W'.a₁ ^ 3 * W'.a₆ + 3 * W'.a₁ ^ 2 *
      W'.a₂ ^ 2 * W'.a₃ - 6 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ + 3 * W'.a₁ * W'.a₂ ^ 4 - 15 * W'.a₁ *
      W'.a₂ ^ 2 * W'.a₄ - 6 * W'.a₁ * W'.a₂ * W'.a₃ ^ 2 + 18 * W'.a₁ * W'.a₂ * W'.a₆ + 12 *
      W'.a₁ * W'.a₄ ^ 2 - 3 * W'.a₂ ^ 3 * W'.a₃ + 12 * W'.a₂ * W'.a₃ * W'.a₄ + 8 * W'.a₃ ^ 3 -
      36 * W'.a₃ * W'.a₆) * P 1 ^ 3 * P 2 ^ 3 * Q 2 ^ 3 + (-W'.a₂ ^ 7 + 5 * W'.a₂ ^ 5 *
      W'.a₄ - 13 * W'.a₂ ^ 4 * W'.a₆ + 3 * W'.a₂ ^ 3 * W'.a₄ ^ 2 + 27 * W'.a₂ ^ 2 * W'.a₄ *
      W'.a₆ - 28 * W'.a₂ * W'.a₄ ^ 3 - 27 * W'.a₂ * W'.a₆ ^ 2 + 54 * W'.a₄ ^ 2 * W'.a₆) * P 0 ^ 2 *
      P 2 ^ 4 * Q 2 ^ 3 + (W'.a₁ * W'.a₂ ^ 6 - 11 * W'.a₁ * W'.a₂ ^ 4 * W'.a₄ + 4 * W'.a₁ *
      W'.a₂ ^ 3 * W'.a₆ + 33 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ ^ 2 - 30 * W'.a₁ * W'.a₂ * W'.a₄ *
      W'.a₆ - 20 * W'.a₁ * W'.a₄ ^ 3 - 27 * W'.a₁ * W'.a₆ ^ 2 + 3 * W'.a₂ ^ 5 * W'.a₃ - 18 *
      W'.a₂ ^ 3 * W'.a₃ * W'.a₄ + 33 * W'.a₂ ^ 2 * W'.a₃ * W'.a₆ + 24 * W'.a₂ * W'.a₃ *
      W'.a₄ ^ 2 - 72 * W'.a₃ * W'.a₄ * W'.a₆) * P 0 * P 1 * P 2 ^ 4 * Q 2 ^ 3 + (-3 * W'.a₁ ^ 2 *
      W'.a₂ ^ 2 * W'.a₆ + 6 * W'.a₁ ^ 2 * W'.a₄ * W'.a₆ + 3 * W'.a₁ * W'.a₂ ^ 4 * W'.a₃ - 15 *
      W'.a₁ * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ + 24 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ + 12 * W'.a₁ *
      W'.a₃ * W'.a₄ ^ 2 + W'.a₂ ^ 6 - 8 * W'.a₂ ^ 4 * W'.a₄ - 3 * W'.a₂ ^ 3 * W'.a₃ ^ 2 + 10 *
      W'.a₂ ^ 3 * W'.a₆ + 18 * W'.a₂ ^ 2 * W'.a₄ ^ 2 + 12 * W'.a₂ * W'.a₃ ^ 2 * W'.a₄ - 36 *
      W'.a₂ * W'.a₄ * W'.a₆ - 36 * W'.a₃ ^ 2 * W'.a₆ - 8 * W'.a₄ ^ 3 + 27 * W'.a₆ ^ 2) * P 1 ^ 2 *
      P 2 ^ 4 * Q 2 ^ 3 + (-W'.a₂ ^ 6 * W'.a₄ - 3 * W'.a₂ ^ 5 * W'.a₆ + 8 * W'.a₂ ^ 4 *
      W'.a₄ ^ 2 + 11 * W'.a₂ ^ 3 * W'.a₄ * W'.a₆ - 18 * W'.a₂ ^ 2 * W'.a₄ ^ 3 - 27 * W'.a₂ ^ 2 *
      W'.a₆ ^ 2 + 8 * W'.a₄ ^ 4 + 54 * W'.a₄ * W'.a₆ ^ 2) * P 0 * P 2 ^ 5 * Q 2 ^ 3 + (-3 *
      W'.a₁ * W'.a₂ ^ 4 * W'.a₆ + 15 * W'.a₁ * W'.a₂ ^ 2 * W'.a₄ * W'.a₆ - 18 * W'.a₁ *
      W'.a₂ * W'.a₆ ^ 2 - 12 * W'.a₁ * W'.a₄ ^ 2 * W'.a₆ + W'.a₂ ^ 6 * W'.a₃ - 8 * W'.a₂ ^ 4 *
      W'.a₃ * W'.a₄ + 13 * W'.a₂ ^ 3 * W'.a₃ * W'.a₆ + 18 * W'.a₂ ^ 2 * W'.a₃ * W'.a₄ ^ 2 -
      48 * W'.a₂ * W'.a₃ * W'.a₄ * W'.a₆ - 8 * W'.a₃ * W'.a₄ ^ 3 + 54 * W'.a₃ * W'.a₆ ^ 2) *
      P 1 * P 2 ^ 5 * Q 2 ^ 3 + (-W'.a₂ ^ 6 * W'.a₆ + 8 * W'.a₂ ^ 4 * W'.a₄ * W'.a₆ - 10 *
      W'.a₂ ^ 3 * W'.a₆ ^ 2 - 18 * W'.a₂ ^ 2 * W'.a₄ ^ 2 * W'.a₆ + 36 * W'.a₂ * W'.a₄ *
      W'.a₆ ^ 2 + 8 * W'.a₄ ^ 3 * W'.a₆ - 27 * W'.a₆ ^ 3) * P 2 ^ 6 * Q 2 ^ 3) * hQ

end WeierstrassCurve.Projective

end
