---
name: flt-cycle-hoist-strands-the-cut
description: "A cycle-breaking hoist that takes a leaf's STATEMENT upstream discards its proof and strands the cut's payload downstream, where nothing can reach it."
metadata: 
  node_type: memory
  type: project
  originSessionId: 99903b9d-f91a-46d3-bc4c-9b943dae14f7
  modified: 2026-08-02T11:44:59.631Z
---

(2026-08-02, `flt-lean-228`.) A release hoisted `nonempty_cubeModel_of_isAmpleSheaf_cube`
from `X0.lean` into the new `Modularity/AbelianCubeModel.lean` to break an import cycle,
carrying its STATEMENT and writing `sorry` for its body. One day earlier that parent had
been CUT into `exists_veryAmpleSystem_of_isAmpleSheaf` + `exists_cubeForms_of_veryAmpleSystem`
and PROVEN over them (`74f525c8`). The two halves and ~150 lines of proven apparatus stayed
in `X0.lean`, which IMPORTS the new module — so they were downstream of their only possible
consumer and unreachable forever. Frontier `1 → 3`, two of them free-floating, all three
looking like ordinary open work to every instrument.

**Why:** a hoist moves a statement; a PROOF's dependencies must move with it, and if they
live only downstream the hoist silently converts a theorem into a leaf and its inputs into
dead code. Nothing errors, the build stays green.

**Tell (one grep, before reading the target):** target has no code consumer, and its
docstring says "cut out of `P`" where `P` is in a module YOURS imports.

**Repair:** move apparatus + halves up beside `P`, paste the assembly recovered from the cut
commit. Scratch-test the block against the destination's cone FIRST (`public import` it,
block verbatim) — it settles feasibility and the `open` question in seconds. A one-line
`abbrev` the block needs (`SpecQ`) travels too; same namespace, so no call site changes.
Receipt: `Counter(before) − Counter(after)` over BOTH files lists only the notes and the
restored proof. Say `3 → 2, no mathematics done` in the commit.

Related: [[flt-cut-times-hoist-orphans-downstream]], [[flt-hoisted-leaf-orphaned-by-reproof]],
[[flt-delete-times-refactor-orphans-a-leaf]], [[flt-consumerless-leaf-is-dead-or-duplicate]].
