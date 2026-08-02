---
name: flt-leaf-names-the-module-holding-its-answer
description: "A leaf's \"what is missing\" paragraph can name the right module, give correct route pointers, and still be wrong — grep that module for the STRUCTURE the conclusion produces, not for the conclusion"
metadata: 
  node_type: memory
  type: project
  originSessionId: 2c082487-ec62-4f6e-8ab4-5a97e69a5ed7
  modified: 2026-08-01T13:08:46.440Z
---

2026-08-01, `flt-lean-147`. `MazurTorsion.lean`'s
`nonempty_isX0Compactification_of_isCompactificationY0` was cut 2026-07-31 with a
"WHY IT IS A LEAF RATHER THAN A PROOF" paragraph that named `X0.lean`, described
what `X0.lean` proves, gave two correct route pointers, and concluded "recovering
it means re-running those transfers". `X0.lean` had had the answer since
2026-07-27, and the leaf closed in **one line**, frontier 37 → 36 in that module.

**Why no grep found it: the answer was a COMPOSITION OF TWO declarations.**
`isX0Compactification_data_of_compactificationY0` (the missing clauses, as a
conjunction) plus `IsCompactificationY0.toX0Compactification` (the packaging).
Neither one's statement is the leaf's statement, so a grep for the conclusion
misses both. **Grep instead for the TARGET TYPE and the packaging constructor** —
a `to…`/`of…`/`…_data_…` name whose RESULT is the structure your leaf produces.
A leaf producing a bundled structure is nearly always already split that way,
because that is the shape some earlier consumer needed.

**Correct route pointers are an active harm here.** The ones given were exactly
the inputs the proven theorem itself consumes, so following them means
re-deriving it — and landing a duplicate statement, which no name-based scan
catches. Read a route pointer as *"what a proof would need"*, never as *"where to
look for the proof"*.

**Do not restate the composite upstream to make it more visible.** The downstream
file `public import`s the upstream one, so the same name there is a hard
`has already been declared`, and the same statement under a different name is
what `tools/merge/dupstmt.py` exists to find. Prove the leaf where it stands and
say in its docstring where the halves live.

Related: [[flt-inventory-audits-understate-what-exists]],
[[audit-lacks-x-is-about-x]], [[flt-audit-refuting-check-unrun]],
[[flt-two-leaves-may-be-one]].
