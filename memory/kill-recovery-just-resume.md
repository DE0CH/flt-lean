---
name: kill-recovery-just-resume
description: "Deyao 2026-07-23 — when agents are killed (usage limit, crash), JUST RESUME them (SendMessage). No salvage: no reverting uncommitted worktree state, no pre-merging branches. The transcript is the agent's state; the worktree is its scratch — both survive the kill untouched."
metadata:
  node_type: memory
  type: feedback
---

Deyao (2026-07-23), after I ran a "salvage-and-resume" procedure for the
third usage-limit fleet kill (revert uncommitted edits, merge committed
branches, then resume): "why do you do salvage-and-resume. you
literally just have to resume. all the state is the transcript, and
nothing is to be salvaged before you can resume where you left off."

**Why:** A kill interrupts only the in-flight API call. The agent's
transcript preserves its entire working context, and its worktree
preserves its files exactly as it left them — uncommitted edits
included. Resuming via SendMessage puts the agent back exactly where
it was. My salvage reverts DESTROYED the uncommitted state the
transcript still referenced, forcing every resumed agent to re-derive
work it had already done (this happened across three consecutive
kills). Pre-merging committed branches was merely unnecessary (the
completion-time merge handles it); the reverts were actively harmful.

**How to apply:** On any fleet kill: touch NOTHING in the worktrees,
merge nothing, then SendMessage each dead agent ("you were killed
mid-call; your worktree is exactly as you left it; continue").
Integration (merge, pool free, queue pop) happens only at an agent's
NORMAL completion, exactly as in [[flt-fleet-13-worktree-protocol]].

**Cross-restart detail (learned same day):** if the Claude Code
process itself restarted since the agents were spawned, the session id
changed and SendMessage reports "No transcript found" — the transcripts
still exist under the OLD session's directory
(`~/.claude/projects/<slug>/<old-session-id>/subagents/agent-<id>.jsonl`).
Copy them into the CURRENT session's `subagents/` directory and
SendMessage resumes them normally (verified 2026-07-23, 13/13
resumed).
