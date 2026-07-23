---
name: flt-fleet-13-worktree-protocol
description: "Deyao 2026-07-23 — standing subagent-dispatch protocol over the fixed pool of 13 renamed worktrees (flt-lean-1..13) plus their per-instance systemd report servers"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
---

Deyao (2026-07-23):

"here's how you are going to use subagents, use a maximum of 13 subagents. each
using one of the worktree. once they are done, the orchestrator (you), merge it
into main, and then leave the folder alone. then before you dispatch a
subagent, find a free worktree, advance it's pointer to main (using --ff-only),
don't touch the .lake folder, the language server will take care of it.
remember that. then we are not going to worry about the nonsense about
managing server, or closing file etc, memory will increase but they will not
go to [in]finite over time."

**The protocol:**
1. Fixed pool: `flt-lean-1` .. `flt-lean-13` (worktrees under `$HOME`, each on its
   own numbered branch, each with its own `flt-report-server@flt-lean-N`
   systemd instance already running — see the template unit).
2. Max 13 concurrent subagents, one per worktree, 1:1.
3. Dispatch: pick a FREE worktree (no agent currently owns it), fast-forward
   its branch to main (`git -C <worktree> merge --ff-only main`) — do NOT
   touch `.lake`; the worktree's own `lake serve` instance rebuilds
   incrementally on its own.
4. On agent completion: orchestrator merges the agent's branch into main, then
   LEAVES the worktree folder alone — no reset, no re-ff, no cleanup beyond
   the merge itself. It just sits until the next dispatch cycle picks it up
   (step 3 ff's it forward then).
5. No managing per-agent LSP/server lifecycle (no closing files, no reaping,
   no memory-conservation tooling): "memory will increase but they will not
   go to infinite over time" — Deyao has explicitly accepted bounded growth
   here as fine, not a leak to manage.

**How to apply:** Every dispatch cycle: (a) integrate any just-finished agent's
branch into main from the main worktree; (b) select a free numbered worktree;
(c) `--ff-only` it to main; (d) dispatch the next agent scoped to that
worktree's absolute path; (e) never exceed 13 concurrent agents; (f) never
touch `.lake` or manage server/file lifecycle for memory reasons.
