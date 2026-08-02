---
name: flt-price-a-repair-by-how-the-parameter-is-produced
description: "When a leaf is false because a free parameter disagrees with a canonical object, check whether that parameter is EXISTENTIALLY produced before choosing between \"pin it\" and \"twist the conclusion\"."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 35c4f4fb-4578-41ae-a895-fd3e1246e522
  modified: 2026-08-01T23:14:35.363Z
---

A FALSITY AUDIT that offers two repairs and recommends one is giving you a cost
comparison it did not check. The check that decides it: **how is the offending
parameter PRODUCED?**

`globalFrob_map_mul_inv_mem_of_isArithFrobAt` (`CyclotomicIdealSymbol.lean`) was
false because a free `ι : CF →ₐ[ℚ] ℚ̄` was mixed with the canonical embedding
inside `Field.absoluteGaloisGroup.map`. The audit priced *pin `ι`* as "a cascade"
and *twist the conclusion* as "keeps the interface", and chose the twist. Wrong
way round: `ι` is `obtain`ed from `exists_frobeniusIdeal_cyclotomic`, which
produces it EXISTENTIALLY and whose proof never uses anything about it — so
pinning cost one line there plus an UNUSED hypothesis threaded down eight
theorems, which weakens each and invalidates nothing. Changing a conclusion
invalidates every consumer.

**Why:** adding a hypothesis to a `∀`-quantified theorem cannot break anything
above it; changing a conclusion clause can break everything. So "N signatures
touched" is the wrong unit — count what has to be RE-READ, not re-signed.

**How to apply:** on any false-because-two-objects-disagree leaf, grep for where
each object comes from. If one is existentially produced anywhere up the chain,
pin it there. State the pin so it *determines* the object (here
`AlgebraicClosure.map` is injective, so the equation pins `ι` uniquely and the
counterexample becomes unstateable, not merely excluded). Keep the audit verbatim
underneath as the evidence for the hypothesis.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audit-recommended-axis-may-be-worse]], [[flt-cut-choice-reasons-are-hypotheses]].
Lean rider: swapping `set x := t` for `obtain ⟨x, hx⟩ := lemma` makes `x` opaque,
so a `rw` that closed by `rfl` may stop — `exact congrArg _ (hx …)` is the fix
([[lean-same-morphism-two-points-blocks-rw]]).
