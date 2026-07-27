/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# The chord–tangent addition law preserves the Weierstrass equation

Mathlib's `WeierstrassCurve.Projective.addXYZ` is defined over an arbitrary
commutative ring, but the fact that it lands back on the curve is proved there
only over a FIELD, and only after dividing by `P z * Q z`
(`Projective/Point.lean`'s `nonsingular_add`, which routes through the affine
model and therefore needs `P z` and `Q z` invertible).  The ring-level
statement is absent from the pin.

This module supplies it:

* `WeierstrassCurve.Projective.equation_addXYZ` —
  `W.Equation P → W.Equation Q → W.Equation (W.addXYZ P Q)` over any
  `[CommRing R]`.

## Why the ring-level statement is needed

`Fermat.ProjCoords` (`Fermat/FLT/ModularCurve/EllipticScheme.lean`) is a
trivialised `Proj`-coordinate datum over an arbitrary `Γ(X, ⊤)`, where `P z`
is emphatically not a unit — that is the whole point of using it to glue the
group law of the projective Weierstrass model.  So the field-level statement
cannot be used, and no base change rescues it.

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
large polynomial; it takes about four and a half minutes and needs the
heartbeat bump below.  **That is a genuine cost of the computation, not a
resource bump hiding a defect** — and it is exactly why this lives in its own
module: `EllipticScheme.lean` is edited constantly by several agents at once,
and a four-minute `ring1` in it would be paid on every one of their rebuilds.
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
