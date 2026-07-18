/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Michael Stoll, Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Fermat.FLT.Mathlib.FieldTheory.Galois.Basic

/-!
# Galois descent for Weierstrass curve data

Proposed new Mathlib file `Mathlib.AlgebraicGeometry.EllipticCurve.GaloisDescent`: a change of
variables (or a point) over a separable quadratic extension `L/K` fixed by `Gal(L/K)` descends
to `K`.
-/

@[expose] public section

open Algebra.IsQuadraticExtension

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]



end WeierstrassCurve

end
