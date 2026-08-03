## A LEAF CAN CONTAIN ANOTHER LEAF — count what the STATEMENT forces, not what the proof needs

(2026-07-31, found while auditing three `ModularCurve/X0.lean` leaves.) Every leaf in this tree
carries a `WHAT IS MISSING` inventory. **That inventory is a hypothesis about the intended proof,
and it can be silently incomplete** — because it lists the theory the author had in mind, while
what the leaf actually owes is fixed by its STATEMENT.

`exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` listed exactly one missing input, the
Eichler–Shimura congruence relation. Unfolding its two conjuncts and counting cardinalities shows
it also CONTAINS `finrank_cuspForm_eq_x0Genus`, a separate open leaf 700 lines below it in the
same file: `IsEichlerShimuraTransform` forces `card {nonzero entries of β} = 2 · card a` (pair
entries have product `ℓ ≠ 0`, so none is zero), `IsWeilEigenvalues` forces that same count to be
`2g`, and `IsCharRootMultiset` forces `card a = finrank` (two polynomial functions agreeing at
every `c ∈ ℂ` are the same polynomial, so the degrees match). Hence `finrank = g`. An owner sent
at the first leaf with only Deligne–Rapoport in hand reaches the last step and cannot finish.

**The technique, which is cheap and general:** for a leaf whose datum is an existential over a
structured predicate, unfold each predicate and count what it pins — cardinalities, degrees,
supports, which entries are forced nonzero — on both sides of the conclusion. Where two
independent predicates pin the SAME quantity, their agreement is an equation the leaf asserts,
and that equation may be somebody else's leaf.

**Why nothing else catches it.** It is not a sorry, not an error, not an unimported module, not a
release-window artefact. The two leaves are in one file, both visible to `lake build`, both in the
census, neither owned by the other's owner. The dependency exists only in the mathematics of the
two statements, so only reading them together reveals it — and the frontier scan that builds task
lists reads them apart. **Dispatch order matters when it is found: prove the contained leaf first,
or the two together, and never send one owner at each.**

Corollary for the `WHAT IS MISSING` convention: treat those lists the way this file already tells
you to treat "still open, owned elsewhere" claims — as a hypothesis to check, never a fact. Adding
a found dependency to the docstring is worth a commit on its own; it is the only place the next
owner will look.

