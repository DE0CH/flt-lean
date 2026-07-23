---
name: flt-bookkeeping-cadence
description: "Deyao 2026-07-23 — bookkeeping runs as ONE periodic dispatched agent doing BOTH the free-floating check AND PROGRESS.md regeneration; its own runtime sets the period (relaunch on completion); integration of arriving work stays continuous"
metadata:
  node_type: memory
  type: feedback
---

Deyao (2026-07-23), after PROGRESS.md fell behind under continuous
integration: "when you dispatch agent for the free floating check, ask
it to update progress.md as well. so basically you have work arriving,
and then periodically (the time it takes to run free floating check and
updating progress.md gives you the period) you do the free floating
check and generating progress.md."

**Why:** the tracker/PROGRESS.md sync and the floating check are both
census-backed and both lag merges by design; running them as separate
uncoordinated steps left PROGRESS.md stale while floating checks ran
inline at every merge. One combined agent per cycle keeps both current
at the same cadence and self-paces: the cycle takes as long as it
takes, and that IS the period.

**How to apply:** maintain ONE bookkeeping task in flight (live or
queued) at a time, whose cycle is: census → sync progress-entries.json
(new/resolved sorried decls; wip flags) → regenerate PROGRESS.md
(progress-tree.py) → free-floating check → resolve/report floaters →
commit. When it completes: integrate (merge/free), then append the
next bookkeeping task to the END of ~/.flt-task-queue like every other
task (Deyao, 2026-07-23: no queue-jumping, ordinary FIFO). The
orchestrator no longer runs `free-floating.py` inline at every merge
(the post-merge reminder hook now reminds about re-queuing the
bookkeeping cycle instead); merging/freeing/dispatching arriving agent
work remains continuous and per-arrival, per
[[flt-fleet-13-worktree-protocol]].
