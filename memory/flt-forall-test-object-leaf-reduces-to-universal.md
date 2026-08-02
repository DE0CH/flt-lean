---
name: flt-forall-test-object-leaf-reduces-to-universal
description: A leaf quantified over all test schemes and all relative points reduces to ONE universal instance; pay the transport once and report the count as 1 to 1.
metadata: 
  node_type: memory
  type: project
  originSessionId: 0249561c-a1c5-4618-8aac-c15a62e9288c
  modified: 2026-08-01T20:13:31.460Z
---

(2026-08-01, `flt-lean-309`, `nonempty_cubeIdentity` in
`Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean`.)

A functor-of-points development states its hard leaves as `∀ {T'} {g : T' ⟶ T}
(x y z : RelPoint q g), <identity in Pic T'>`. That shape is **unattackable by the
mathematics the leaf needs** — seesaw and cohomology-and-base-change act on ONE
invertible sheaf on ONE scheme, not on a family of Picard-group identities.

**Why:** the reduction to the universal instance is a strict prerequisite of any
proof, so leaving the `∀` form open leaves a prover unable to start; and the
transport is pure bookkeeping that every successor would otherwise rebuild.

**How to apply:** build the representing object (`X ×_T X ×_T X` via `pullback`)
with its projections as relative points and a classifying morphism from
`pullback.lift`; transport with the structure's NATURALITY fields (`pre_add`,
`pre_zero`) plus `modPullbackCompIso` and `nonempty_modPullback_modTensorPic`.
Report it as `1 → 1` and say what is LEFT in the leaf, and say why the earlier
faithfulness audit transfers (here: the two forms are equivalent, both directions
in the file). See [[flt-a-leaf-can-be-atomic]] and
[[flt-closing-a-leaf-may-close-nothing]] for the accounting discipline.

Two Lean traps this cost: naming the OBJECT of a `pullback` with a `def` blocks
`rw [pullback.lift_fst]` (inline the object, name only the morphisms); and
`congrArg Subtype.val (by rw [...])` cannot elaborate — state the point-level
equation as its own typed `have` first.
