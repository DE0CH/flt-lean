---
name: flt-downstream-copy-is-the-newer-one
description: In a cross-file duplicate left by a hoist, the DOWNSTREAM copy is systematically the newer and stronger one — so the obviously-correct repair (delete the copy in the importing file) is exactly the one that silently reverts proofs
metadata:
  type: project
---

A hoist moves declarations from a downstream module up into an upstream one and
deletes the originals. `semmerge.py` propagates a branch's ADDITIONS and not its
DELETIONS, so what lands is the upstream copies **beside** the surviving
downstream ones — `has already been declared`, which only `tools/merge/xdup.py`
sees, because no per-file check looks across an import cone.

The repair looks obvious: delete the copy in the file doing the importing. It is
right for most of them and **wrong in exactly the cases that matter**.

**Why:** after the hoist branch is cut, every other branch goes on editing the
copy its own call sites resolve to — the DOWNSTREAM one. The upstream copy is
frozen at the moment of the hoist. So by the time anyone notices, the downstream
copy is systematically the newer one. Measured 2026-07-31 on
`MazurTorsion.lean` vs `IsogenySignature.lean`/`X0.lean`: of 249 duplicated
names, 233 had identical bodies and **all 16 that differed had the downstream
copy newer** — 11 PROVEN downstream against a `sorry` upstream, and three with a
hypothesis the frozen upstream copy still demanded (`hq2 : q ≠ 2`). Deleting
blind would have reverted eleven proofs while the build went green, so nothing
downstream could ever have told.

**How to apply:** never delete a duplicate by name — compare BODIES first
(whitespace- and comment-normalised; `tools/merge/dedup_cross.py` does this and
prints the disagreements, which are the only part needing judgement). For each
disagreement ask three questions in order, because they decide whether the newer
body can simply be carried up (`tools/merge/transplant.py`) before the deletion:

1. does it name any declaration that exists ONLY downstream? (a hoist that
   continued after the first one always leaves helpers behind);
2. does it name one declared LATER in the upstream file? — a forward reference,
   so it needs a reorder, not a hoist;
3. does the SIGNATURE differ at type level? Then the upstream call sites break,
   and if those call sites are themselves in the duplicate set you have a
   coupled cluster, not an edit.

Only the ones clearing all three transplant. For the rest, keeping the upstream
`sorry` is honest — the proof is vouched, verbatim, in the parent commit — but
say so and give the line range, or the work is lost with the blob.

Two things to read BEFORE diagnosing any of this, both of which had the answer
already written down: the surviving copy's own docstring (a `## MERGE REPAIR`
heading means someone fixed this once and the fix landed as an addition beside
the damage), and `~/.flt-loop/jobs/merger.prompt`, which carries the previous
worker's per-file wound list and its prescriptions.

Related: [[flt-runaway-doc-comment]], [[flt-deletion-claims-are-not-deletions]],
[[flt-see-the-merge-before-the-merger]], [[flt-delete-times-refactor-orphans-a-leaf]].
