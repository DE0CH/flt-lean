## A CLAUSE THAT NAMES A COORDINATE IS NOT A CLAUSE ABOUT THE OBJECT — restate it intrinsically

(2026-07-31, `MoretBailly.lean`, same Bertini cluster as the section below.)

`exists_basisPlane_irreducible_planeSection` asked for a plane whose section is irreducible
**and** for `h_d(u₁) ≠ 0`, where `u₁` is the FIRST DIRECTION of the frame the leaf itself
chooses. Its docstring, and the task prompt built from it, both warned in capitals that the
two clauses "genuinely have to be arranged by one choice of plane rather than sequentially",
and backed the warning with a real witness (`h = X 1 ^ 2 - X 0`, `W = span(e₀, e₂)`: good for
irreducibility, `h_d ≡ 0` on it). The warning is TRUE and the witness is REAL — and it is
about the PLANE. What it invited, and what cost the leaf its shape, is the reading that a
GOOD plane can still be spoiled by a bad choice of `u₁` inside it.

It cannot. `h_d(u₁) ≠ 0` for some frame of the plane is exactly the INTRINSIC condition
"the section has total degree `d`": the degree-`d` part of the section is a binary form, and
a nonzero binary form over an infinite field misses some direction. Restating the clause that
way and proving the implication took ~60 lines over lemmas the file already had
(`homogeneousComponent_totalDegree_ne_zero`, `exists_eval_ne_zero_of_ne_zero`,
`coeff_single_planeSection_eq_eval_homogeneousComponent` read twice, `planeSection_comp`), and
it deleted a whole obligation from the remaining leaf.

**So the rule: when a leaf's clause mentions a coordinate of a structure the leaf is itself
choosing — a first basis vector, a distinguished index, the `0`th column — look for the
intrinsic statement on the structure before accepting any "these cannot be separated" folklore
attached to it.** What genuinely cannot be separated is the intrinsic conditions; the
coordinates are almost always free, because the group that moves them acts by invertible
substitutions and every hypothesis in sight is invariant under it. In this file that group was
sitting there already, as `irreducible_planeSection_of_det_ne_zero` and
`totalDegree_planeSection_of_det_ne_zero`.

Corollary for reviewers of a decomposition: an existential leaf whose conclusion mentions a
MATRIX is carrying packaging. Extending a linearly independent pair to an invertible matrix is
`Module.Basis.extend` + `Module.Basis.indexEquiv` against `Pi.basisFun` + two transpositions to
put the two vectors at indices `0, 1`, and then `Module.Basis.toMatrix_mul_toMatrix_flip` gives
invertibility **with no determinant computation at all**. That is ~50 lines and it belongs in
the glue, never in the mathematical leaf.

