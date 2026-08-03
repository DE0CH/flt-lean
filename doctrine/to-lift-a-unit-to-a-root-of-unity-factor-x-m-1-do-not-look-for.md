## TO LIFT A UNIT TO A ROOT OF UNITY, FACTOR `X^M − 1` — DO NOT LOOK FOR HENSEL
(2026-08-01, `flt-lean-164`, `Modularity/Interface.lean`, closing the Teichmüller
half of Stickelberger's congruence.) A leaf packaged over a BARE valuation — here
`v : AlgebraicClosure CF → WithTop ℚ` with only `v 0 = ⊤`, `v 1 = 0`,
multiplicativity and the ultrametric inequality — looks like it cannot support any
lifting statement: there is no ring of integers, no maximal ideal, no completion,
and therefore nothing for a Hensel lemma to act on. The leaf's own docstring said
so and spent a screen constructing the residue field `R/m` by hand so that a
counting argument (`μ_M ↪ (R/m)ˣ` injective, both subgroups of order `M`, a field
has at most one) could produce the lift.
**None of that is needed, and the substitute is three lines of algebra.** To find
an `M`-th root of unity `ζ` with `v (ζ·w − 1) > 0`, given `v w = 0` and
`v (w^M − 1) > 0`, put `y := w⁻¹` and use that `X^M − 1` SPLITS over an
algebraically closed field:
    y^M − 1 = ∏_{ζ : roots} (y − ζ),   so   0 < v (y^M − 1) = ∑_ζ v (y − ζ)
and a product whose valuation is positive has a FACTOR of positive valuation —
by contraposition, `v (∏) ≤ 0` whenever every `v (y − ζ) ≤ 0`. That factor is the
lift. No residue field is constructed, no subgroup is counted, no approximation is
iterated, and the only mathlib inputs are `IsAlgClosed.splits`,
`Polynomial.splits_iff_card_roots` and
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`.
**The generalisable form: a lifting statement in a valued field is a statement
about a PRODUCT FORMULA whenever the object to be lifted is a root of a polynomial
that splits.** Hensel is the tool when you must lift along an approximation; when
the target set is the root set of a split polynomial, the factorisation gives it
outright. Ask which of the two situations you are in before pricing anything —
the docstring here priced the wrong one and the cost differed by a whole
development.
Two riders from the same run, both worth having before you start:
* **`MulChar.ofRootOfUnity` is in the pin** (`Mathlib/NumberTheory/MulChar/Lemmas.lean`),
  with `ofRootOfUnity_spec`: given a generator `g` of `Mˣ` and
  `ζ ∈ rootsOfUnity (Fintype.card Mˣ) R`, it BUILDS the multiplicative character
  sending `g ↦ ζ`. So "construct a character of a finite field from a root of
  unity" is one call, not a search through `zmodEquivZPowers` /
  `mulEquivOfCyclicCardEq` / hand-rolled discrete logarithms. `MulChar.eq_iff`
  (agreement on a generator) and `MulChar.ext` (agreement on units) are the two
  extensionality principles beside it.
* **"a root of unity of order prime to `ℓ` that is congruent to `1` IS `1`" needs
  no product over the roots of unity.** The cheap proof is the GEOMETRIC SUM: if
  `ξ^d = 1` and `ξ ≠ 1` then `∑_{i<d} ξ^i = 0` (`geom_sum_mul`), while each
  `ξ^i ≡ 1` gives `∑_{i<d} ξ^i ≡ d`, so `v(d) > 0` — contradicting `ℓ ∤ d`. The
  route through `∏_{η≠1}(1 − η) = d` needs a differentiated product formula and
  is strictly more work.
