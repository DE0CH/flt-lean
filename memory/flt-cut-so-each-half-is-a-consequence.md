---
name: flt-cut-so-each-half-is-a-consequence
description: Decompose a big ∃-leaf so each half is IMPLIED by the leaf (parameter-existential + transfer) — faithfulness then needs no judgement
metadata:
  type: project
---

When decomposing a leaf `∃ X, P₁ ∧ … ∧ Pₙ` that is proved *for a prescribed
parameter*, do not invent an interface for the intermediate object — cut so
that **each half is a consequence of the leaf itself**:

* **(i)** the same conclusion with the parameter EXISTENTIALLY quantified
  ("it holds for some `ρ₁`") — follows from the leaf at `ρ₁ := ρ₀`;
* **(ii)** the TRANSFER ("if it holds for `ρ₁` it holds for `ρ₀`") — follows
  from the leaf by discarding every hypothesis but the ones it already had.

Their conjunction implies the leaf back, so the cut is *equivalent* to it and
neither half can be false unless the leaf was. An interface cut has to be
JUDGED strong enough for the second half; this one does not.

**Why:** a wrongly-judged interface makes the second half FALSE, and a false
leaf can never be closed — see [[flt-leaf-names-wrong-half-as-hard]] and
CLAUDE.md's TWO INDIVIDUALLY-CORRECT REPAIRS section.

**How to apply:** used on `exists_splitHilbertBlumenthalCocycle_of_standardLevelModule`
(2026-07-31, `Modularity/MoretBailly.lean`) — half (i) is Rapoport's space for
a level module of its own choosing, half (ii) is the twist along
`σ ↦ ρ₀(σ) ρ₁(σ)⁻¹`. Two riders. **Do not fix the convenient parameter to a
NAMED one** (`ρ₁ := stdRep`) unless you can also prove the comparison of its
auxiliary data with the given one — quantifying it away is free, that
comparison was not. And **whatever in the transfer is not geometry, prove it
and hand it in as a hypothesis**: the group theory of `ρ₀ ρ₁⁻¹` compiled first
try in a 42 s scratch module, and passing it into the sorried half both makes
that half cheaper and keeps the proven work out of the free-floating set.
