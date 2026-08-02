---
name: flt-recut-drops-the-falsity-repair
description: A re-cut transcribes the leaf signature by hand and drops the hypothesis an earlier falsity repair added; the orphaned old leaf is the only surviving witness
metadata: 
  node_type: memory
  type: project
  originSessionId: 39b37a41-ef6e-4591-abfc-bc6646108eef
  modified: 2026-08-01T11:19:47.584Z
---

Re-cutting a node (split in two, prove one half, re-point the parent) writes the
new leaf's signature out BY HAND. That is where a hypothesis added by an earlier
FALSITY REPAIR gets dropped — it reads as decoration to whoever is concentrating
on the decomposition, because it is not what either half is *about*.

Measured 2026-08-01 in `ModThree.lean`: `287edc70` (07-30) repaired the Fontaine
presentation leaves by adding `hū3`; `5904e20a` (07-31) re-cut the node and
dropped `hū3` from the new leaf and the parent, re-instating a statement that had
been refuted the day before by a witness twenty lines above it.

**All four standing checks are silent by construction**: the false thing is a
`sorry` leaf (no build breaks); the names differ (duplicate scans blind); the
parent is PROVEN (frontier scans blind); the `sorry` count went UP, reading as
ordinary decomposition progress.

Two detectors:

1. **A DEAD BINDER at the top of the chain.** The declaration above the re-cut
   keeps its repaired binder and stops passing it, because the callee no longer
   takes it. Grep for a binder declared in a signature and consumed nowhere in
   the body; Lean's `unusedVariables` linter reports it on every green build.
2. **Diff the ORPHAN's binder list against the live leaf's.** A re-cut that does
   not delete the leaf it replaces leaves the correct signature in the file as
   the only record of the repair. The orphan is the witness, not just garbage.

For whoever re-cuts: **deleting the old leaf is part of the re-cut**, and before
deleting, diff its binders against the new one and justify every difference. Not
wanting to delete it means the two are not the same statement.

The repair is normally free — see [[flt-leaf-hypotheses-are-a-superset]]: the
hypothesis is already in the caller's hand. Here `hū3` is discharged at the top
by a `by_cases`, so restoring it was one binder on two declarations and one
argument at two call sites.

**Distinguish from [[flt-falsity-repair-must-hit-the-leaf]]** (same week, same
symptom, different cause): there the repair landed on the wrong declarations —
the consumers rather than the leaf — so it never stuck at all. Here it stuck
correctly and a LATER re-cut reverted it on the leaf while the top of the chain
kept its now-dead binder. The two together say a falsity repair needs re-checking
both when it is made *and* whenever anything downstream of it is re-cut; grep a
repaired binder's name before and after any decomposition of the chain it guards.

Related: [[flt-delete-times-refactor-orphans-a-leaf]] (the orphan class),
[[flt-consumerless-leaf-is-dead-or-duplicate]] (find it by grepping consumers),
[[flt-decomposition-drops-a-hypothesis]].
