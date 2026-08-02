---
name: flt-prompt-built-on-a-declined-payload
description: A task prompt can name machinery from a branch whose payload was DECLINED at merge — it is then an ancestor of main, on no branch, and `git log -m -S` is the only thing that says so.
metadata:
  type: project
---

A fourth way a prompt describes a tree you do not have, alongside
[[flt-target-exists-only-on-merger]], [[flt-held-release-leaf-only-on-merger]] and
[[flt-prompt-line-numbers-are-a-freshness-checksum]]: **the prompt's PREMISE was
declined at merge.** It is the only one of the four where merging something cannot
help.

Measured 2026-08-02, `flt-lean-55`, on `exists_dedekind_rigidifiedModuli` in
`X0.lean`. The task named five declarations (`SpecZinv`, `hom_ext_specZinv`,
`existsUnique_classify_of_isPullback`,
`exists_isAffine_rigidifiedModuliSchemeData_baseChange`, `…_zinv`) as PROVEN. All
five had **zero occurrences tree-wide**, while:

* `main` and `merger` were the same commit — release-window check says "current";
* the worktree was current after one fast-forward — staleness check passes;
* `git log --all -S SpecZinv` finds the creating commit `f2eaf03d`;
  `git merge-base --is-ancestor f2eaf03d main` says **YES**; and
  `git branch --contains f2eaf03d` lists **every branch in the pool**.

By ancestry present, by grep absent. **`-m` is what resolves it**, because the
removal is on one side of a merge:

    git log -m --oneline -S '<name>' --all -- <path>
    # 9bc0599c (from f2eaf03d) Merge flt-lean-366 -- X0.lean payload DECLINED, superseded by flt-lean-346

**Why:** the queue entry was written from the declined branch's own report, which
described its branch truthfully and could not know it would not be taken. Roughly one
branch per release is declined, so this recurs.

**How to apply:** run the `-m` log before merging anything when named machinery is
missing. Do NOT recover the declined code — it was superseded, so re-adding it is a
duplicate cut and usually free-floating besides; `git show <sha>` keeps it recoverable.
Read the "superseded by X" clause: it names the thing that makes the task unnecessary
(here a base-general family over an arbitrary ring with `n`, `N` invertible, strictly
subsuming the declined `ℤ[1/n]` descent). Then write the finding into the SURVIVING
leaf's docstring — the declined names are unqueryable, but the surviving leaf is still
open, so the task passes every existence filter and will be re-dispatched.

Related: [[flt-deletion-claims-are-not-deletions]] is the mirror (a docstring claims a
deletion that never happened); here a commit really did land and was really removed.
