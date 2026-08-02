---
name: flt-cut-times-hoist-orphans-downstream
description: A cut made in file F plus a hoist of the cut's parent out of F leaves the halves DOWNSTREAM of their own consumer — unconsumable, and invisible to every scan.
metadata:
  type: project
---

(2026-08-02, `flt-lean-234`, `exists_cubeForms_of_veryAmpleSystem`.) Branch A cut a leaf
into two halves *in `X0.lean`*; branch B hoisted the parent into a new upstream module to
break an import cycle, taking its PRE-CUT body. Both merged cleanly — different files.
The halves then sat in a module that `public import`s their own consumer, so nothing in
the project could reach them, and the parent kept its `sorry` because a hoist cannot carry
a proof written against declarations it leaves behind. Three leaves counted where the
mathematics has two, for two days, and a dispatch was sent at one of them.

**Why:** a hoist copies a declaration as it stands on the hoisting branch, so it silently
reverts any concurrent re-proof of it — [[flt-delete-times-refactor-orphans-a-leaf]] with
the deletion replaced by a relocation.

**How to apply:** when `grep -rn '<target>' --include=*.lean Fermat/` returns only the
target's own declaration line and docstrings, do not stop at "consumerless" — ask *where
did the consumer GO*. Deleted ⇒ your leaf is garbage; MOVED ⇒ your leaf is misplaced, and
the repair is to move the ORPHAN up (never the consumer down: its position is what breaks
the cycle). Verify the move by reverse-substituting whatever had to be respelled upstream
and `difflib`-comparing against the original; announce the two file edits as ONE edit in
`to_merger` ([[flt-recut-leaves-stale-docstring]] class-7 split). See also
[[flt-consumerless-leaf-is-dead-or-duplicate]], [[flt-hoisted-leaf-orphaned-by-reproof]].
