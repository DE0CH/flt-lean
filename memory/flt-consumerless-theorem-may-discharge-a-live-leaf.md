---
name: flt-consumerless-theorem-may-discharge-a-live-leaf
description: "Before deleting a consumerless PROVEN theorem, compute its orphan closure and check whether that closure proves an OPEN leaf elsewhere in the file"
metadata: 
  node_type: memory
  type: project
  originSessionId: 129e7482-4aa2-40ff-851e-489a4c9a5a7f
  modified: 2026-08-02T03:26:08.656Z
---

(2026-08-01, `flt-lean-71`, `HardlyRamified/HilbertModularity.lean`.) A deletion
task premised on "this PROVEN theorem has zero consumers, so it is free-floating"
can be half-right in a way that costs real work. The consumerless theorem is
often the ROOT of a chain, and the chain can be the complete proof of an OPEN
LEAF elsewhere in the same file. Deleting only the root relocates the
free-floating violation one level down and strands the discharge of a live
`sorry`.

Here: `finite_setOf_subgroup_hilbertInertiaAt_le_outside` had zero consumers, and
behind it sat three more proven declarations (~250 lines of Hermite–Minkowski
over `F`) whose only uses were inside each other. That chain proves, statement
for statement, the open leaf `finite_setOf_intermediateField_hilbertInertiaOutside`
declared 114 lines ABOVE it — the same set with the inertia clause in the file's
other spelling. Closing the leaf took a relocation plus four lines.

**The check: after confirming your target has no consumers, compute the ORPHAN
CLOSURE (fixpoint: what becomes consumerless once it goes), then ask whether the
closure's CONCLUSION matches an open leaf in the file. Match on the STATEMENT,
never the name** — these two shared no identifier, and the only textual link was
that both docstrings described the same classical theorem in prose.

Why it hid: DECLARATION ORDER. The leaf was declared above the block that proves
it, so the derivation was not expressible where the leaf stood and every reader
correctly concluded there was nothing to do there. See
[[flt-leaf-above-its-own-solution]] and [[flt-declaration-order-leaves]].

Three moves are available and only one leaves the file owing less: delete the
root (relocates the violation), delete the whole chain (merge-friendly, destroys
the discharge of a live leaf), or close the leaf over the chain. Take the third.

Related: [[flt-consumerless-leaf-is-dead-or-duplicate]] is the same shape for an
OPEN leaf; this is the PROVEN case, and it is the more dangerous one because the
free-floating rule actively invites the deletion. [[flt-orphan-helper-reusability-test]].
