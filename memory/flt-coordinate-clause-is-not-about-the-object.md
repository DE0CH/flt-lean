---
name: flt-coordinate-clause-is-not-about-the-object
description: "a leaf clause naming a coordinate (first direction, 0th column) of a structure the leaf itself chooses is almost always free — restate it intrinsically before believing any 'these cannot be arranged separately' warning attached to it"
metadata:
  node_type: memory
  type: project
---

2026-07-31, `MoretBailly.lean`, `exists_basisPlane_irreducible_planeSection`.

The leaf asked for an irreducible plane section AND for `h_d(u₁) ≠ 0`, where
`u₁` is the FIRST DIRECTION of the frame the leaf itself produces. Its docstring
and the task prompt both warned in capitals that the two clauses "genuinely have
to be arranged by one choice of plane rather than sequentially", with a real
witness (`h = X 1 ^ 2 - X 0`, `W = span(e₀, e₂)`: good for irreducibility while
`h_d ≡ 0` on it).

The warning is true **about the plane** and was read as if it were also about the
frame. It is not. `h_d(u₁) ≠ 0` for SOME frame of the plane is exactly the
intrinsic condition `(planeSection h v u₁ u₂).totalDegree = d`: the degree-`d`
part of the section is a binary form, and a nonzero binary form over an infinite
field misses some direction. Proving that implication took ~60 lines over lemmas
already in the file, and deleted a whole obligation from the remaining leaf.

**Why:** the group that moves the coordinate — here the invertible `2 × 2` frame
changes, acting through `irreducible_planeSection_of_det_ne_zero` and
`totalDegree_planeSection_of_det_ne_zero` — was already in the file, and every
hypothesis in sight was invariant under it. When that is so, the coordinate is
free and only the intrinsic conditions can conflict.

**How to apply:** when a leaf's conclusion mentions a coordinate of a structure it
is itself choosing (a first basis vector, a distinguished index, column `0`, a
matrix at all), look for the intrinsic restatement BEFORE accepting folklore
attached to the coordinate version. Related: extending a linearly independent pair
to an invertible matrix is `Module.Basis.extend` + `Module.Basis.indexEquiv`
against `Pi.basisFun` + two transpositions + `Basis.toMatrix_mul_toMatrix_flip` —
~50 lines and NO determinant computation — so a matrix in a leaf's conclusion is
packaging that belongs in the glue. See [[flt-cleaner-statement-harder-proof]] and
[[flt-two-leaves-may-be-one]].
