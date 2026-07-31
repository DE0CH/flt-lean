---
name: flt-a-leaf-can-contain-a-leaf
description: A leaf's WHAT IS MISSING list is about the intended proof; unfolding its predicates and counting cardinalities can show it contains another open leaf in the same file
metadata:
  type: project
---

Found 2026-07-31 in `Fermat/FLT/ModularCurve/X0.lean`.
`exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` listed exactly one
missing input (the Eichler–Shimura congruence relation). Counting what its
STATEMENT forces shows it also contains `finrank_cuspForm_eq_x0Genus`, a
separate open leaf 700 lines below: `IsEichlerShimuraTransform` pins
`card {nonzero entries of β} = 2 · card a` (pair entries have product
`ℓ ≠ 0`), `IsWeilEigenvalues` pins that same count to `2g`, and
`IsCharRootMultiset` pins `card a = finrank` (two polynomial functions equal
at every `c ∈ ℂ` are the same polynomial). So `finrank = g`.

**Why:** the `WHAT IS MISSING` convention records the theory the author had in
mind, not the obligation the statement creates. Nothing mechanical sees the
gap — both leaves compile, both are in the census, neither owner's records
mention the other; the dependency lives only in the mathematics of the two
statements, and a frontier scan reads them apart. See
[[flt-dispatch-consumer-lists-are-unverified]] for the same shape one level up.

**How to apply:** for any leaf whose datum is an existential over a structured
predicate, unfold every predicate and count what it pins — cardinalities,
degrees, supports, which entries are forced nonzero — on both sides of the
conclusion. Where two independent predicates pin the same quantity, their
agreement is an equation the leaf asserts, and it may be somebody else's leaf.
When found: prove the contained leaf first, or both together; never dispatch
one owner at each. Write the finding into the docstring, which is the only
place the next owner looks.
