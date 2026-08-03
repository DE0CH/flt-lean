## A CLAUSE A DOCSTRING CALLS FREE IS OFTEN AN UNPROVEN PREMISE OF THREE OTHER DOCSTRINGS
(Same run.) `exists_plane_irreducible_planeSection` carried `LinearIndependent K ![u₁, u₂]`
as a third conclusion, with the note that it *"follows from the other two clauses … but no
construction of a genuine `2`-plane has to work for it, so it is asked for rather than
re-derived. A prover who has a plane has it."* That reasoning is correct, and it is a reason
not to bother — which is why nobody did, for two days.
Bothering was worth it, and NOT because the leaf got weaker (it did, and that alone is
marginal). The underlying fact — a section along a parametrisation with DEPENDENT directions
is a univariate polynomial in a linear form, hence reducible once its degree is `≥ 2` — is
asserted as prose in **three** other docstrings in the same file: `planeSection`'s, where it
is the reason the averaging identity may quantify over ALL triples, and the "DEGENERATE
TRIPLES ARE NOT EXCLUDED" paragraph of `exists_bertiniNoetherWitness` **and** of
`exists_bertiniNoetherWitness_of_three_le`, where it is the reason the Noether forms need not
dodge them. Three load-bearing prose claims, one proof, ~150 lines
(`not_irreducible_planeSection_of_not_linearIndependent`).
**So the test is not "does the leaf need it" but "how many docstrings ASSUME it".** One
`grep` for a distinctive phrase of the claim (`univariate polynomial in a linear form` here)
answers it. A fact repeated in three docstrings is load-bearing three times over and is
exactly the kind of thing a later audit will take on trust.
The technique, since it recurs for anything about `planeSection`: a dependent pair is
`(l₁ • w, l₂ • w)`; complete `(l₁, l₂)` to an invertible `2 × 2` frame, and `planeSection_comp`
exhibits the section as an INVERTIBLE substitution applied to `planeSection h v w 0`, which is
`MvPolynomial.rename` of a one-variable polynomial. Factor there
(`exists_eq_linear_of_irreducible_of_unique`) and push the factorisation forward: `rename`
preserves total degree when the map has a retraction, and `planeSection` at a nonzero
determinant does too, so both factors stay non-units. Mathlib has
`totalDegree_rename_le` and `totalDegree_renameEquiv` but **no injective-`rename` degree
lemma**; `Fin 1 ↪ Fin 2` is not an `Equiv`, and the retraction is what supplies the missing
inequality (`totalDegree_rename_eq_of_leftInverse`, added here).
