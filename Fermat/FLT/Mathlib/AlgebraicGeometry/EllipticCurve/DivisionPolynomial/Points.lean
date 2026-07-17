/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata

Vendored (2026-07-17) from the mathlib branch `EllipticCurve.Torsion`
(github.com/Multramate/mathlib4), sorry-free portion only: the
evaluation bridges between the bivariate division polynomials
`ψ₂, Ψ, ψ, φ : R[X][Y]` and their univariate companions
`Ψ₂Sq, ΨSq, Φ : R[X]` at a point of the curve. These factor the
evaluation through the coordinate ring (`AdjoinRoot.evalEval`), where
the congruences `mk_ψ₂_sq`, `mk_Ψ_sq`, `mk_ψ`, `mk_φ` hold.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Evaluation of division polynomials at points of the curve

For `(x, y)` satisfying the Weierstrass equation of `W`:
* `WeierstrassCurve.evalEval_ψ₂_sq`: `ψ₂(x,y)² = Ψ₂Sq(x)`;
* `WeierstrassCurve.evalEval_Ψ_sq`: `Ψₙ(x,y)² = ΨSqₙ(x)`;
* `WeierstrassCurve.evalEval_ψ`: `ψₙ(x,y) = Ψₙ(x,y)`;
* `WeierstrassCurve.evalEval_φ`: `φₙ(x,y) = Φₙ(x)`.
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

lemma evalEval_ψ₂_sq {x y : R} (h : W.toAffine.Equation x y) :
    W.ψ₂.evalEval x y ^ 2 = W.Ψ₂Sq.eval x := by
  rw [← AdjoinRoot.evalEval_mk h, ← map_pow, Affine.CoordinateRing.mk_ψ₂_sq,
    AdjoinRoot.evalEval_mk h, evalEval_C]

lemma evalEval_Ψ_sq (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.Ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  rw [← AdjoinRoot.evalEval_mk h, ← map_pow, Affine.CoordinateRing.mk_Ψ_sq,
    AdjoinRoot.evalEval_mk h, evalEval_C]

lemma evalEval_ψ (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
  rw [← AdjoinRoot.evalEval_mk h, Affine.CoordinateRing.mk_ψ, AdjoinRoot.evalEval_mk h]

lemma evalEval_φ (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [← AdjoinRoot.evalEval_mk h, Affine.CoordinateRing.mk_φ, AdjoinRoot.evalEval_mk h,
    evalEval_C]

end WeierstrassCurve
