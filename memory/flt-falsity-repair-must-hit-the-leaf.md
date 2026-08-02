---
name: flt-falsity-repair-must-hit-the-leaf
description: "A hypothesis added to a refuted leaf's CONSUMERS instead of the leaf is dead weight — the refutation passes through; check by deleting it in a scratch"
metadata: 
  node_type: memory
  type: project
  originSessionId: 5c08f4eb-4e85-4b2c-bfe7-4aec11461c52
  modified: 2026-08-01T11:18:33.078Z
---

(2026-08-01, `flt-lean-305`, `HopfAlgebra/ShortExact.lean`.) When a leaf is refuted
and the repair is a new hypothesis, the hypothesis must go on the LEAF. Applied to the
chain's consumers instead it discharges nothing: the derivations between leaf and
consumers only forward it, so the counterexample passes straight through and the leaf
stays FALSE.

`exists_lift_ker_le_span_cartierDual` was refuted 2026-07-31 (`ℤ[√-5]`) and repaired with
`[IsLocalRing R]`. The module header said "it and the four statements above it in the chain
now carry it"; the instance landed on the five statements BELOW. The file's single open leaf
`exists_lift_span_sup_jacobson_cartierDual` was therefore false for a day.

**Why:** an unused instance binder on a theorem emits no linter warning, so the build is
green, the warning set is one leaf, and the frontier/ownership/duplicate scans are all
correct. Nothing reports it.

**How to apply:** whenever a falsity repair adds a hypothesis to more than one declaration,
restate each consumer in a scratch with the hypothesis DELETED and its proof copied verbatim.
If it compiles, the hypothesis is dead there and the refutation is still live above it. Cost
here: two consumers, 8 seconds. Then repair at the TOP of the chain and say which declarations
you touched — "the chain now carries X" is not checkable.

**The docstring tell:** an EQUIVALENCE claim beside a refuted sibling. This leaf said
"equivalent … hence neither stronger nor weaker than `exists_basis_cartierDual` for any base"
— true, and exactly the transport carrying the refutation into the leaf. Equivalence is a
two-way street for counterexamples. On refuting anything, grep its neighbourhood for
"equivalent".

Frontier `1 → 1`: nothing proven, but a false leaf became a true one. Same family as
[[flt-decomposition-drops-a-hypothesis]] and [[flt-leaf-hypotheses-are-a-superset]].
