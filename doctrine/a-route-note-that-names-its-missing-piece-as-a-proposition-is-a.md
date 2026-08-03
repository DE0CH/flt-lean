## A ROUTE NOTE THAT NAMES ITS MISSING PIECE AS A *PROPOSITION* IS A GIFT — BUILD IT, AND THE LEAF RECUTS ITSELF
(2026-08-02, `flt-lean-210`, on
`exists_gamma0Datum_specQ_isBaseChangeOf_specPt_of_weierstrassQForm` in `X0.lean`.)
This file already records that a survey naming ONE missing item is usually right, while one
naming a body of THEORY is usually decoration.  Here is the sharpest instance yet, and it is
worth copying because the docstring did the design work and nobody had cashed it:
> *a `VariableChange` induces an isomorphism of affine Weierstrass curves — i.e.
> `IsWeierstrassModel ab (C • W) → IsWeierstrassModel ab W` — is NOT in the tree, in either
> direction … So the honest further cut of this leaf is that one lemma, stated over an
> arbitrary `CommRing R` with no moduli vocabulary in it: the `R`-algebra map
> `R[C • W] → R[W]` induced by the substitution, its inverse from `C⁻¹`, and `Spec` of the
> pair.*
Every clause re-checked (mathlib relates `variableChange` to `Equation`, `Nonsingular`, `j` and
`Point`, and **never** to `CoordinateRing`).  Building exactly the three things it names —
~230 lines — closed the gap, and then the leaf RECUT ITSELF: with the transport available, the
auxiliary `ℚ̄`-model `W` and the change of variables `Cv` can be deleted from the statement,
because the consumer carries `ι` over to `E⁄ℚ̄` and carries `ι'` back along the SAME
isomorphism.  Three hypotheses gone, `1 → 1` on the count, and the residue is the arithmetic.
**The generalisable shape, and it is the reason to prefer this over attacking the leaf.**  A
leaf of the form *"produce an object over a curve `W`, given that `W` is a form of a rational
`E`"* is carrying TWO things: the arithmetic (descent) and a coordinate transport between `W`
and `E⁄ℚ̄`.  The transport is a fixed cost that does not depend on the arithmetic, it is
mathlib-shaped, and paying it once deletes it from every sibling.  **Ask which half of a leaf
is a change of coordinates before pricing the whole.**
### The technique: clear the units OUT of `variableChange_aᵢ`, then one `linear_combination`
The identity that has to be proved is, in `R[X][Y]`,
    W.polynomial (u²x + r, u³y + u²sx + t)  =  u⁶ · (C • W).polynomial (x, y).
Doing it directly fights `C.u⁻¹`, which appears in all five `variableChange_aᵢ`.  Multiply
each one through instead:
    ↑C.u   * (C • W).a₁ = W.a₁ + 2 C.s
    ↑C.u^2 * (C • W).a₂ = W.a₂ - C.s W.a₁ + 3 C.r - C.s^2
    ↑C.u^3 * (C • W).a₃ = W.a₃ + C.r W.a₁ + 2 C.t
    ↑C.u^4 * (C • W).a₄ = W.a₄ - C.s W.a₃ + 2 C.r W.a₂ - (C.t + C.r C.s) W.a₁ + 3 C.r^2 - 2 C.s C.t
    ↑C.u^6 * (C • W).a₆ = W.a₆ + C.r W.a₄ + C.r^2 W.a₂ + C.r^3 - C.t W.a₃ - C.t^2 - C.r C.t W.a₁
each of which is `rw [variableChange_aᵢ]` plus
`linear_combination <RHS> * pow_mul_pow_eq_one k C.u.mul_inv` and contains **no inverse at
all**.  Map them into the coordinate ring, put the defining relation of `(C • W)`'s coordinate
ring beside them, and the whole substitution identity is ONE `linear_combination` with the
coefficients read off the monomials:
    u⁶ · hrel  −  u⁵xy · e₁  +  u⁴x² · e₂  −  u³y · e₃  +  u²x · e₄  +  e₆
Nothing here is special to Weierstrass equations; **whenever a group of units acts on a
presentation by scaling the coefficients, clearing the units first turns the compatibility into
an inverse-free `linear_combination`.**
### Four traps, each of which cost a round, and all four are `ring`/`rw` seeing different atoms
* **`simp only [Affine.polynomial]` unfolds the polynomial INSIDE `AdjoinRoot.of (…)` and
  `AdjoinRoot.root (…)` as well**, so the goal's atoms stop matching the hypothesis's and
  `ring` reports two visibly-equal sides as unequal.  Cure: state the expansion as its own
  lemma (`eval₂_polynomial_eq`, over an arbitrary `φ : R →+* S`) where the unfolding is local,
  and `rw` it.  The same discipline applies to any `simp` that unfolds a definition appearing
  in a TYPE INDEX.
* **`algebraMap R T (u ^ 2)` and `(algebraMap R T u) ^ 2` are different atoms to `ring`**, and
  `simp only [map_pow]` reported "no progress" on the goal that displayed the first.  Cure:
  write the DEFINITION in the already-normalised form; do not try to normalise afterwards.
* **`IsIso (Spec.map f)` fails to synthesize when the goal's objects are stated through a
  `def`** — here `weierstrassAffine W ⟶ weierstrassAffine V` rather than
  `Spec (of W.CR) ⟶ Spec (of V.CR)`.  It IS an instance at the unfolded types.  Cure:
  `haveI hiso : IsIso (Spec.map …) := inferInstance` (elaborated at the `Spec` types) and then
  `exact hiso`; and `show` the `Spec`-shaped goal before any `rw [← Spec.map_comp]`, which
  otherwise fails with *"target expression is not type-correct under the `instances`
  transparency level"*.
* **`rw [h]` on a goal mentioning `W.j` is a MOTIVE error**, because `WeierstrassCurve.j` takes
  the `IsElliptic` instance as an argument.  Cure: a three-line congruence lemma
  (`weierstrassCurve_j_congr : V = V' → V.j = V'.j`, by `subst h; rfl` — `IsElliptic` is a
  `Prop`, so proof irrelevance closes it).  Reach for this on any invariant whose definition
  consumes a class instance.
### And take the target as a VARIABLE with an equation, not as `C • W`
Every declaration in the new block takes `hV : C • W = V` with `V` a variable, so that `subst`
is available inside the proofs and no transport is needed at the call site — the consumer needs
the map at `V = E⁄ℚ̄` given `Cv • W = E⁄ℚ̄`, and a `C • W`-shaped conclusion would have had to be
moved there.  Same device as `RelPoint.transport` and
`WeierstrassCurve.Affine.Point.equivOfEq`, and it is what makes the two directions of the
transport ONE statement: apply it at `C := C⁻¹`, `W := C • W`, using `inv_smul_smul`.
