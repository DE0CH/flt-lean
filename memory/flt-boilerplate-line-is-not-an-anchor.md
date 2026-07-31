---
name: flt-boilerplate-line-is-not-an-anchor
description: A scripted str.replace on an `omit ... in` / `set_option ... in` line silently edits every other declaration that carries the same boilerplate — 9 hits where 3 were intended
metadata:
  type: feedback
---

`omit [Finite k] [TopologicalSpace k] [DiscreteTopology k] in` appears **six**
times in `HardlyRamified/Deformation.lean`, byte-identical. A one-line
`s.replace(that_line, "")` written to undo three lines I had just added removed
all nine, stripping the `omit` from six unrelated proven lemmas. Nothing in the
diff summary looked wrong — the insertion count dominated — and the damage
surfaced only because `git diff --stat` reported deletions I had not authorised.

**Why:** attribute boilerplate (`omit … in`, `set_option … in`, `open scoped … in`,
`variable … in`) is *designed* to be repeated verbatim, so it is the worst
possible anchor for a textual edit. The repo's soft rule (prefer Write/Edit over
scripts) exists for exactly this: `Edit` refuses a non-unique `old_string`,
which would have caught it at zero cost.

**How to apply:** never key a scripted edit on a line that looks like
boilerplate. If a script really is the right tool, `assert
s.count(anchor) == 1` before every replace and check `git diff --stat` for
deletions afterwards — on an insert-only change it must read `0 deletions`.
Restoring the six lines needed a `git diff -U1 | grep -A2` pass to recover which
declaration each one had guarded, which is only possible because the tree was
committed-clean beforehand.
