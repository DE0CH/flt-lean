---
name: flt-drop-the-iso-from-an-annihilator
description: An annihilator defined through an existentially-supplied isomorphism should be defined without it; the iso has trivial kernel so the submodule is the same and becomes canonical
metadata:
  type: feedback
---

A pairing that lands in some group `T` together with a leaf asserting *there exists*
`inv : T ≃ₗ[k] k` making it nondegenerate invites the definition
`L^⊥ := {y | ∀ x ∈ L, inv (pairing x y) = 0}`. Define it as
`{y | ∀ x ∈ L, pairing x y = 0}` instead.

**Why:** `inv` is an equivalence, so `inv z = 0` iff `z = 0`, and the two submodules are
equal for every admissible `inv`. The version with `inv` depends on a choice extracted from
an existential — junk-valued exactly where that existential is an unproven leaf — while the
version without it is canonical and consumes no leaf at all. In `flt-lean-248` this took
`orthComplU` in `HardlyRamified/Deformation.lean` off `isLocalTateDual` entirely and reduced
the submodule proof to `map_zero`, `map_add`, `map_smul`.

**How to apply:** whenever a definition would consume a choice from an existential, ask what
the choice is used for. Used only in a slot where it is injective — an equivalence, a mono,
an embedding — it can be deleted. **The tell is a docstring that has to say "which one is
chosen does not matter": that sentence is a proof the choice is removable**, not a
reassurance that keeping it is harmless. Same family as
[[flt-existential-wrapper-that-pins-is-not-a-cut]].
