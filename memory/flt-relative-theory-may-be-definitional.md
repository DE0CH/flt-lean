---
name: flt-relative-theory-may-be-definitional
description: An audit's "needs a relative structure first, not even statable" dies if the defining clause never mentions the base; and composing the index deletes the transitivity theory
metadata:
  type: project
---

`ArtinConductor.lean`'s `gp_le_upperRamificationFiltration_sup_lvl` carried a
FAITHFULNESS AUDIT saying Herbrand-for-a-tower was "NOT available, and not even
STATABLE" without first building a relative `LowerRamificationData` for `L''/L`
and its own `φ`. Both halves were wrong, and both failures have a general form.

**Why:** `mem_gp` defines the filtration by an ELEMENTWISE valuation condition
(`unif ^ (i+1) ∣ σ • x − x` for level-fixed `x`) in which the base field never
occurs — so `G_i(L''/L) = D''.gp i ⊓ D.lvl` already, and Serre IV §1 Prop. 2 is
definitional here. And transitivity of `φ` existed only to turn Prop. 14's index
`ψ_{L''/L}(m)` into the consumer's `ψ_{D''}(φ_D m)`; stating the leaf with the
COMPOSED index already in it means the composite is never taken apart.

**How to apply:** before accepting "a relative/generalised structure is needed
first", read the structure's defining clause and check whether the missing thing
appears in it — an audit is authoritative about what it searched, not about what
it did not think to search ([[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]]). And when a leaf's index is a
composite of two functions, prefer the composed spelling: the uncomposed one
obliges you to prove the composition law, the composed one never forms the
pieces. Stating the leaf between two ARBITRARY objects rather than for a tower
additionally turned the refinement-compatibility lemma into a corollary instead
of a second leaf ([[flt-two-leaves-may-be-one]]).
