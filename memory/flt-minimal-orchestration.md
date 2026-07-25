---
name: flt-minimal-orchestration
description: Deyao 2026-07-25 — the orchestrator manages as little as possible; agents own their own environment including .lake. Managing more created the bugs that tripped agents all day.
metadata: 
  node_type: memory
  type: feedback
  originSessionId: eda93c26-088c-4639-b0f3-bf5ee7a16ed8
  modified: 2026-07-25T17:17:31.259Z
---

Deyao, 2026-07-25: "basically before we are managing too many things and it's
creating so many bugs and constantly tripping agents over."

**The orchestrator's job at dispatch is exactly three things:**
1. Advance the worktree's pointer to main.
2. Hand the agent a prompt — including the warning that **`.lake` may be stale
   and the agent may need to rebuild it**.
3. Nothing else.

**Agents own their own environment.** `.lake` included: an agent rebuilds it
when it needs to. The orchestrator does not seed it, refresh it, symlink it,
reap it, or reason about its freshness. This REVERSES the old CLAUDE.md rule
("never touch `.lake`"), which existed only because a systemd-managed
`lake serve` owned it.

**Why:** every fleet-wide outage on 2026-07-25 came from centrally-managed
shared state, not from the mathematics —
- a stale `lake setup-file` failure replayed with `verified: true` (six agents
  lost cycles; one concluded main was broken hours after it was fixed),
- a false clean from a `publishDiagnostics` nobody heard,
- four rival elaborations of one file after orchestrator restarts,
- clients wedged forever on dead FIFO handles after a server restart,
- a memory climb from documents opened and never closed, which forced a
  fleet-wide worker drain and cost four agents their work.

Each was a coordination bug in machinery the orchestrator built to be helpful.
None was a Lean problem. The pattern generalizes: **centrally managing a
resource an agent could own itself converts a private failure into a fleet-wide
one.**

**How to apply:**
- Prefer a fresh process that exits over a persistent one that must be managed
  ([[claude-is-a-pure-function]] — only disk has state).
- If a daemon is genuinely wanted (a warm REPL/LSP for turn-by-turn work), the
  AGENT starts and stops it, and it carries an idle timeout so forgetting costs
  bounded memory rather than unbounded.
- Before building any coordination mechanism, ask whether the agent could just
  do it itself. Usually yes ([[dont-invent-delegate-to-existing-tools]]).
- Warn in the prompt instead of pre-solving: "your `.lake` may be stale" beats
  a orchestrator-side freshness protocol that can be wrong.
