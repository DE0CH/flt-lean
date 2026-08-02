---
name: flt-route-inductive-step-is-often-formal
description: "A leaf's Route paragraph of the form \"X for cyclic, extended to abelian by induction\" splits into a FORMAL step and a DEEP base case — perform the step"
metadata: 
  node_type: memory
  type: project
  originSessionId: 7e6ea76e-7052-425e-a259-4631f2a36535
  modified: 2026-08-02T19:42:32.959Z
---

(2026-08-01, `flt-lean-382`, `NumberField/UnramifiedClassFieldExistence.lean`.) A mature
leaf's **Route** paragraph routinely reads *"X for CYCLIC extensions, extended to abelian by
induction along a cyclic subextension using multiplicativity of Y in towers"*. The two halves
have very different prices, and the induction half is frequently **pure formal bookkeeping
with no arithmetic in it** — performable today, without touching the mathematics.

Here the whole dévissage of the second fundamental inequality (cyclic subgroup, its fixed
field, inheritance of both unramifiedness hypotheses in both directions, induction on the
degree) came to ~200 lines and compiled essentially first try, leaving the CYCLIC case as the
only leaf. Count `1 → 1`; what left the leaf is the entire reduction.

**Why:** the discriminating test is whether the chained quantity is an INDEX / RANK / DEGREE
whose multiplicativity is a statement about a *named group homomorphism*. If so,
`Subgroup.index_map` (`(H.map f).index = (H ⊔ f.ker).index * f.range.index`) plus antitonicity
of the index does the whole estimate in five lines and the rest is instance plumbing.

**How to apply:** read the Route paragraph for a phrase like "extended to … by induction" or
"multiplicativity in towers"; check the quantity is a group-theoretic index; then build the
missing functoriality (see [[flt-functoriality-via-surjinv]]) and perform the induction.

Beware the mirror trap: a recorded *"that dévissage does not work"* verdict may be about a
DIFFERENT quantity — see [[flt-devissage-verdict-names-a-quantity]].
