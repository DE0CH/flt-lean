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
   systemd instance already running — see the template unit). Live allocation
   state lives in `~/.flt-worktree-pool`, one line per worktree: `<name>
   free` or `<name> claimed`.
2. Max 13 concurrent subagents, one per worktree, 1:1.
3. Dispatch: write `{{FLT_WORKTREE}}` as a literal placeholder in the agent's
   prompt wherever its worktree path is needed. `.claude/worktree-pool-hook.py`
   (a `PreToolUse` hook on the `Agent` tool) does the rest automatically: finds
   a `free` entry, checks it is git-clean and its branch is an ancestor of
   main, fast-forwards it to main (`--ff-only`), marks it `claimed`, and
   substitutes the real path for the placeholder via `updatedInput`. Never
   touch `.lake` — the worktree's own `lake serve` instance rebuilds
   incrementally on its own. No free worktree → the hook denies the tool call
   with "no free worktree available". A claimed worktree that turns out dirty
   or not an ancestor of main is NOT a normal condition and is NOT
   auto-corrected — the hook hard-crashes (full traceback to stderr, exit 2,
   tool call blocked), because that state means something beyond allocation
   went wrong and needs attention.
4. On agent completion: orchestrator merges the agent's branch into main, then
   hand-edits `~/.flt-worktree-pool` to set that worktree back to `free`
   (there is no reliable hook trigger for "the orchestrator finished merging",
   since `git merge` is just a Bash call among many — this step is the
   orchestrator's explicit responsibility, no script). Otherwise leave the
   worktree folder alone — no reset, no cleanup beyond the merge and the pool
   edit.
5. No managing per-agent LSP/server lifecycle (no closing files, no reaping,
   no memory-conservation tooling): "memory will increase but they will not
   go to infinite over time" — Deyao has explicitly accepted bounded growth
   here as fine, not a leak to manage.

**How to apply:** Every dispatch cycle: (a) integrate any just-finished agent's
branch into main from the main worktree, then hand-edit `~/.flt-worktree-pool`
to mark it `free`; (b) dispatch the next agent with `{{FLT_WORKTREE}}` in its
prompt and let the hook allocate/validate/ff/substitute; (c) never touch
`.lake` or manage server/file lifecycle for memory reasons.
