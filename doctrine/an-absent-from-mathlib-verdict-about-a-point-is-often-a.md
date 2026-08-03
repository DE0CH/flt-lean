## AN "ABSENT FROM MATHLIB" VERDICT ABOUT A **POINT** IS OFTEN A VOCABULARY MISS
(2026-07-31, `flt-lean-349`, and it had cost two prior audits a cycle each.) Two audits on
`card_compl_range_le_card_divisors` (`ModularCurve/X0.lean`) deferred the same re-cut because it
needed *a closed point of a finite-type `k`-scheme has `Module.Finite k κ(p)`*, and mathlib "has
nothing packaging that at the scheme level (grepped 2026-07-31)". The second priced it as a
four-step chain of curve theory: `Y ≠ ∅` from integrality → `X` irreducible → the generic point
lies in `Y` → a non-generic point of an integral curve is closed → Zariski's lemma. **None of the
four was needed and the whole obligation was twenty lines**, over
`AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType` and
`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` (`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`,
both stacks 01TB) plus `LocallyOfFiniteType.jacobsonSpace`.
**Why the grep missed it, and this generalises.** Mathlib's AG library states facts about a POINT
as properties of the canonical morphism out of it (`X.fromSpecResidueField p`, `Hom.residueDegree`),
and states those as *equivalences between `MorphismProperty`s*. A search in the mathematician's
vocabulary — "closed point", "residue field", "finite over the base" — therefore returns nothing,
and the absence claim reads as verified. Before concluding a point-level scheme fact must be built,
grep `Mathlib/AlgebraicGeometry/Morphisms/*.lean` for the canonical morphism and for `_iff_`-shaped
lemmas between morphism properties.
**Second lever from the same task: a topological argument can delete the geometry outright.** An
open set is stable under generisation, so "the generic point lies in `Y`" became "`closure {p}` is
disjoint from `Y`, hence sits inside the FINITE complement" plus `JacobsonSpace` — no
irreducibility, no integrality, no dimension, no nonemptiness of `Y`. When a chain of geometric
hypotheses is being assembled only to locate the generic point, check first whether finiteness of
the complement already does it.
