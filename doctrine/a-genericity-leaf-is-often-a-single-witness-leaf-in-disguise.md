## A GENERICITY LEAF IS OFTEN A SINGLE-WITNESS LEAF IN DISGUISE — check the direction

(2026-07-31, `MoretBailly.lean`.) Half the hard leaves in this development are of the form
"the GENERIC member of a family has property P": irreducible over the algebraic closure of
the parameter field, geometrically integral, nonsingular, dimension-preserving. The reflex
is to prove them by generic-fibre reasoning, which drags in `FractionRing`,
`AlgebraicClosure`, Gauss, and a base field nobody wants to compute in.

**Ask first whether the implication you actually need runs the OTHER way: does ONE good
`K`-rational member force the generic one?** Very often it does, and that direction is the
CHEAP one, because a factorisation (or a relation, or a degeneracy) over the generic fibre
has coefficients INTEGRAL over the parameter ring whenever the family is MONIC in one
variable — so it descends to a finite extension, and a maximal ideal over the chosen point
has residue field `K` again when `K = K̄`. Push the generic object through that residue map
and it specialises, contradicting the good member.

Concretely, `exists_basisPlane_irreducible_familyPlaneSection` (Schmidt Thm 3D step 2) was
a leaf asking for irreducibility over `\overline{K(y_0 … y_n)}`. It is now PROVEN over a
leaf that says only "some honest plane section of `h` is an irreducible two-variable
polynomial over `K`" — same leaf count, no fraction fields left in the statement. The
bridge is `irreducible_map_of_irreducible_eval_unit`, ~250 lines, over three mathlib bricks
none of which this project had used before:

* `Polynomial.isIntegral_coeff_of_dvd` (stacks 00H6) — the coefficients of a MONIC factor
  of a monic polynomial are integral over the base ring. No field, no fraction ring, no
  integrally-closed hypothesis; this is the whole engine.
* `Ideal.exists_ideal_over_maximal_of_isIntegral` — lying over, to reach the chosen point.
* `IsAlgClosed.ringHom_bijective_of_isIntegral` — the Nullstellensatz form: an integral
  extension field of an algebraically closed field is that field.

Two riders learned the same day. **Monicity is not a technicality — without it the
criterion is FALSE**: `(y·s + 1)(s + t)` is reducible over `K(y)` while its fibre at
`y = 0` is irreducible. And in this development monicity is usually already present under
another name — here it is exactly the leading-form clause `h_d(u₁) ≠ 0` that the leaf was
carrying anyway. **Look for the monicity you already have before concluding the route is
closed.**

For two-variable work specifically: `MvPolynomial.finSuccEquiv`,
`MvPolynomial.finSuccEquiv_coeff_coeff`, `MvPolynomial.natDegree_finSuccEquiv` and
`MvPolynomial.isIntegral_iff_isIntegral_coeff` are enough to move between
`MvPolynomial (Fin 2) R` and `(MvPolynomial (Fin 1) R)[X]` in both directions; "total
degree `≤ d` and the `s^d`-coefficient is a unit" is the usable spelling of "monic of
degree `d` in `s`".

