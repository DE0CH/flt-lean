---
name: flt-delete-times-refactor-orphans-a-leaf
description: A branch deleting a declaration and a branch refactoring it merge CLEANLY into an orphan sorry with no consumer; only a consumer grep catches it
metadata:
  type: project
---

On 2026-07-31 in `Fermat/FLT/ModularCurve/X0.lean`: one branch collapsed a cut,
deleting `exists_isAbelianWeilEigenvalues` and `prod_one_sub_eq_of_isJacobianOf`;
concurrently another split `exists_isAbelianWeilEigenvalues` into a proven assembly
over a new leaf `exists_isAbelianWeilEigenvalues_galoisField`. Both edits correct in
isolation, and they DO NOT CONFLICT — the new declaration sits at a line the deletion
never touched. The merge kept both, so the assembly vanished and its sub-leaf survived
as a `sorry` with zero consumers tree-wide, plus a docstring naming a deleted parent.
`−2 + 1` where `−2` was intended.

**Why:** every frontier instrument reports the orphan as an ordinary open leaf — it
emits a real `declaration uses 'sorry'` warning, holds a real `sorry` token, and lives
on the root's import closure. Compiler, `flt-frontier.py` and the census all agree, and
all three are wrong about what it is. Only the free-floating check (zero consumers)
separates a leaf from garbage. See [[flt-see-the-merge-before-the-merger]] for the
in-memory merge that would have shown it before the merge worker did.

**How to apply:** as a prover, `grep` the whole tree for consumers of your target
BEFORE proving it — zero consumers means the task is a deletion, not a proof, and
saying so is a full success. As an integrator, whenever a merge deletes a declaration,
grep for consumers of everything that declaration consumed; and before deleting one,
check `~/.flt-merge-batch` and the other worktrees' diffs for a refactor of it, which
will survive your deletion rather than conflict with it.
