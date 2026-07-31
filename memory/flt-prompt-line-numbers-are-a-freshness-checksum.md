---
name: flt-prompt-line-numbers-are-a-freshness-checksum
description: A task prompt's TARGET line numbers must land on the declaration; a mismatch means the worktree is stale, not that the file drifted
metadata:
  type: feedback
---

A fleet task prompt names each target as `` `name` (path:LINE) ``. Those line numbers are
generated against `main` at dispatch time, so they are a free checksum on the worktree's
freshness. `grep -n '<name>' <file>` must land on the stated line.

On 2026-07-31 `flt-lean-16` was dispatched at three `X0.lean` leaves stated at lines 34356,
34410, 34514. Two were at 29033/29074 and the third was absent. The worktree sat on a
commit **704 behind `main`** — clean `git status`, branch a proper ancestor of `main`,
`lake build` green. Nothing else distinguished it from a fresh one.

**Why:** the loop's release step is supposed to advance every worktree, and `CLAUDE.md`'s
dispatch section says a worktree fast-forwards at dispatch. Neither had happened. An agent
that trusts either statement edits a file whose declarations have moved and whose `sorry`
set belongs to an earlier release; the work is then unmergeable, not merely wrong.

**How to apply:** before opening the target file, run
`git rev-list --count HEAD..main` (must be 0) and `grep -n` for one target name. Repair with
`git merge --ff-only main` plus
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`.
A target that does not appear in the file **at all** is the loudest form of this signal —
check freshness before concluding it was renamed or already proven, since both readings
produce a sentinel that says "already done".

Related: [[flt-home-is-nfs-stale-reads]] (a different staleness, same shape of wrong
conclusion), [[flt-ssh-build-needs-cd-and-elan-path]] (`lake` also needs
`export PATH=$HOME/.elan/bin:$PATH` in a non-interactive background Bash call, or it exits
127 with a log that has no `error` in it).
