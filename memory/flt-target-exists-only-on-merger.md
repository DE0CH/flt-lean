---
name: flt-target-exists-only-on-merger
description: When a dispatched leaf exists on `merger` but not on `main`, base the branch on `merger` and work — the "say so and stop" escape hatch throws the run away
metadata:
  type: feedback
---

The release-window doctrine ([[flt-see-the-merge-before-the-merger]]) covers one
direction — *your target is already PROVEN on `merger`*. The **mirror case** is
just as common and nothing covers it: the target **does not exist on `main` at
all**, because it was CUT on `merger` by a decomposition that has not been
released. Task prompts written from a decomposition note routinely name such a
leaf, and they often carry an escape hatch of the form *"if the declaration is
not in your tree, say so in the sentinel and stop"*.

**Why:** taking that hatch throws a whole agent-run away for a leaf that is
perfectly workable. Basing on `main` instead is worse — you would have to
re-create the declaration and its neighbours, which is a guaranteed conflict
with the tree that already has them, and a rival cut on top.

**How to apply:** `git merge merger` into your worktree branch and work there.
Your diff then applies to the tree the merge worker actually holds, so merging
back is trivial. Say in `to_merger` that the branch is merger-based and why —
the merge worker must not read the 800-commit ancestry as a mistake. Only stop
if the declaration is on neither `main` nor `merger` nor any batch branch.

Second, independent, and discovered the same way: **a red module anywhere in
your target's import cone makes your target unbuildable**, so `lake build` on it
is not available at all. Do not conclude the tree is broken and do not try to
fix the red module. Find the largest GREEN module that carries every definition
your statement mentions and verify the entire payload in a scratch module
importing that one; then transplant. The residual risk is only the target file's
own namespace / `open` / declaration-order context, which is a read, not a
build — say in `to_merger` that the payload is scratch-verified rather than
in-file verified. See [[flt-green-base-is-the-release-lake-sha]] for the seeding
half of the same problem.
