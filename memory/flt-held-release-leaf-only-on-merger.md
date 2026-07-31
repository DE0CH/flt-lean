---
name: flt-held-release-leaf-only-on-merger
description: "A HELD release makes queue tasks name leaves that exist ONLY on merger — the worktree, main and the release all lack the declaration; redo the cut on main from `git show merger:<file>` rather than rebasing"
metadata:
  node_type: memory
  type: project
---

When a release is HELD (merger keeps `main` where it is because the tree is red),
the queue is still generated from **merger's** frontier and still dispatched. So a
task can name a declaration that does not exist in the worktree, on `main`, or in
the release snapshot — it exists only on `merger`, created by a cut made after the
hold.

Seen 2026-07-31 (`flt-lean-356`, target
`exists_nonConstant_qExpansion_gamma0GITPresentation` in `ModularCurve/X0.lean`):
zero occurrences of the name anywhere reachable; `git log -S` found it on `merger`
alone, two hours old, after release 31 was held with X0 red (39 errors).

**Why:** every ownership and frontier instrument in `CLAUDE.md` answers "is this
leaf open / owned" about a tree that does not contain the leaf. This is the mirror
of the release-window trap (a leaf already PROVEN on an unmerged branch) — see
[[flt-see-the-merge-before-the-merger]].

**How to apply:** first command when a named target is missing is
`git show merger:<the file> | grep -n <name>` — before concluding it was proven,
renamed, or never existed. Then **redo the cut on `main`**, copying merger's
declaration names, ORDER and docstrings verbatim (`git show merger:<file>` is the
source; the cut's commit message says which relocation it chose and why). Do NOT
rebase onto `merger` — it was 1448 commits ahead and red in the very file — and do
NOT `git cherry-pick` the cut commit, which arrives bundled with unrelated
relocations and conflicts. Note that a cut usually includes a HOIST (here
`isRegularRing_coarseRing_of_gamma0GITPresentation` moved ~250 lines up so the new
assembly could cite it); reproduce the move to the same place instead of
duplicating the proof inline. Tell the merge worker "take mine — it is your text
plus a proof".
