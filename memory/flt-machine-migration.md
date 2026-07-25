---
name: flt-machine-migration
description: "Deyao 2026-07-24 — how to move the whole fleet to another machine: stop workers first, parent cleans up, child reseeds scratch and restarts rotator/monitor"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 58c19df2-0ef6-4be6-abc8-2e0fb9663755
  modified: 2026-07-24T21:45:57.222Z
---

Deyao (2026-07-24, moving nightcrawler → mystique): the fleet is moved by
resuming from transcript on the new host. Drive it end-to-end when told
which host; survey candidates with `ssh <host> free -g` + `/proc/loadavg`
+ per-user RSS (the maths machines are shared; neighbours hold hundreds of
GB and are volatile).

**Order matters — stop the workers BEFORE resuming from transcript**, so
each worktree's on-disk state matches the transcript the child will resume
from. `TaskStop` every running agent, then proceed.

**Parent (old machine) cleans up:**
1. `TaskStop` all agents.
2. Commit any WIP in `/scratch` worktrees first — linked worktrees write
   objects into the NFS main repo, so a WIP commit survives the scratch
   deletion even though the worktree does not.
3. Stop every `flt-report-server@*` and `flt-report-server-scratch@*`
   instance — that is what actually frees the RAM (~944G for 13 active
   worktrees; memory lives in `lean --worker` children, ~20G per open big
   file, ~73G per working worktree).
4. Free the scratch disk too: `git worktree remove` the batch-2 trees and
   delete the scratch dir.
5. Stop the rotator here. **Only one rotator may run anywhere** — two
   refreshers on one account brick it (see `~/bin/ROTATOR.md`).

**Child (new machine) sets up:**
- `$HOME` is NFS, so the repo, batch-1 worktrees, `~/.flt-worktree-pool`,
  `~/.flt-task-queue`, `~/.claude` transcripts and the systemd unit FILES
  all follow. `/scratch` is machine-LOCAL and does not.
- Reseed batch 2: recreate `/scratch/chend-flt/flt-lean-14..26` and copy
  `.lake` from the home repo into the first one, then fan out
  scratch→scratch (one NFS copy ~5 min, each local copy ~20 s).
- Start the report-server instances there, then resume the batch-1 agents
  by id; batch-2 agents cannot continue (their worktrees are gone) — their
  tasks go back on the queue.
- **Restart the rotator AND the monitor on the new host** — both read the
  tmux pane, so they must point at the new session (`REFILL_TMUX`).

Related: [[flt-self-restart-by-forking]], [[flt-fleet-13-worktree-protocol]],
[[kill-recovery-just-resume]].
