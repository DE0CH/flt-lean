---
name: flt-grep-the-queue-for-your-target
description: "Before starting a leaf, grep ~/.flt-loop/queue1 and queue2 for its name — the diagnosis and often the prescribed fix are already written there by an agent who was just inside your file."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e5e6036b-f625-4c08-a7f2-219be53bf781
  modified: 2026-08-01T15:20:39.208Z
---

Every freshness check in CLAUDE.md looks at the TREE (worktree, `main`, `merger`,
other worktrees' diffs). None looks at the QUEUE. But `~/.flt-loop/queue2` is
written by prover agents who have just been inside your file, so it routinely
contains a task whose text *is* the answer to yours.

Measured 2026-08-01, `flt-lean-26`, target `geomPic_finite_torsion`: I re-derived
from git history and a consumer scan that the leaf was a dead orphan of a
superseded recut and a verbatim duplicate of `finite_torsion_pic_geom`. A
`queue2` entry written that morning said exactly that, named all four orphans
with line numbers, and prescribed the deletion.

**Why:** queue entries are the only record of work in flight that no branch shows
yet — including a leaf's own REVIVAL by an unmerged branch, which makes a
"dead, delete it" verdict wrong. See [[flt-dead-orphan-may-be-revived]].

**How to apply:** as the first command of any task, alongside the `merger` check —

    grep -n '<target>' ~/.flt-loop/queue1 ~/.flt-loop/queue2 ~/.flt-loop/jobs/*.prompt

Read the neighbouring `TARGET:` lines too; that is where a race with another
agent shows up. Same command detects a leaf queued twice
([[flt-queue-coverage-is-one-sided]]).
