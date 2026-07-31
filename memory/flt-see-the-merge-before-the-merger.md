---
name: flt-see-the-merge-before-the-merger
description: A prover can see its own merge hours early with `git merge-tree --write-tree`; the AUTO-MERGED files are the dangerous half, and the reverse direction (does merger's proof beat my stale sorry?) is the check nobody runs
metadata:
  type: project
---

`git merge-tree --write-tree --name-only HEAD merger` merges **in memory** — no
working-tree change, no `.lake` disturbance, and no conflicted state to strand the
worktree in if the agent is killed mid-way, which is why it beats
`git merge --no-commit …; git merge --abort`. Exit 1 means conflicts; it prints a
tree sha browsable with `git show <tree>:<path>`, so every class-7 interface-split
check in CLAUDE.md can be run on the merge that has not happened yet.

**Why:** every rule in CLAUDE.md about rival cuts, class-6 dropped payloads and
class-7 interface splits is addressed to the merge worker *at merge time*. A prover
holds the same information hours earlier and can make the merge decision cheap
instead of leaving it to be re-derived.

**How to apply:** run it whenever your branch touched a hot file, and read TWO
things, because they fail in opposite directions.

- The files that **CONFLICTED** are the safe half — somebody will look at them.
- The files `Auto-merging` reported with **no conflict** are the dangerous half.
  On `flt-lean-182` my branch had DELETED a 130-line theorem while `merger` grew
  new text 200 lines away — too far apart to conflict, so the file auto-merged
  silently. The check is not reading the diff but grepping the merged blob for the
  deleted NAME: `git show <tree>:<path> | grep -n '<deletedName>'`, docstring hits
  only == safe.
- **The reverse direction is the one nobody thinks of.** Your branch carries the
  *old* `sorry` bodies of every leaf it did not touch. If `merger` proved one
  meanwhile, does the merged tree keep the PROOF or your `sorry`? Grep the merged
  blob for the BODY, not the name. (Untouched regions took merger's side both
  times I checked — a fact to verify, not to assume, and invisible from either
  side alone.)

When the merge shows your cut and merger's are RIVALS, the action worth far more
than a note is: **fold the loser's surviving information into the winner's
docstring on YOUR side, so "take HEAD" is a LOSSLESS resolution**, then say exactly
that in `to_merger`. Check the loser's docstring for claims that have gone stale
before copying them, and say which you folded in and which you corrected.

Related: [[flt-lifting-obstruction-witnessed-upstairs]], [[flt-two-leaves-may-be-one]].
