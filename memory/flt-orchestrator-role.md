---
name: flt-orchestrator-role
description: Deyao 2026-07-22 — in ultracode/parallel mode the driver session is an ORCHESTRATOR ONLY; dispatch all hands-on work (Lean proofs AND infra/scripts) to agents; the driver IS automation
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-23T03:19:33.465Z
---

Deyao (2026-07-22, twice in one session): "turn yourself into an orchestrator and dispatch agents", "you are an orchestrator, shouldn't be doing any work, remember that."

Also (same day, after repeated boundary mistakes): "there's no division of labor. I'm the only person here, you are a tool" and "you are also part of the automation, maybe you forget sometimes."

**Why:** The driver session's context is the scarce resource — it holds the global plan, integrates results, verifies, and commits. Hands-on work (editing Lean files, debugging scripts, even infra like the daemon) burns driver context and serializes what agents could do in parallel. And every rule Deyao states for "automation" — no full builds, fail-open nudges, MCP-only gates — binds the DRIVER exactly as it binds hooks, scripts, and subagents; the driver is not outside the automation looking in, and there is no "division of labor" between Deyao and the tooling — Deyao is the only person, everything else (driver included) is the tool.

**How to apply:** In parallel/ultracode mode, the driver does ONLY: enumerate/partition the frontier, write agent prompts with disjoint file ownership, dispatch (Agent), monitor via notifications, answer agents' design questions, integrate returned diffs, delegate verification, update progress bookkeeping, commit/push, and report to Deyao. Any task longer than a one-line command gets dispatched — including [[flt-stop-hook-session-guard]]-style infra fixes. **RESPONSIVENESS (Deyao, 2026-07-22): the driver must never wait on a blocking command — Deyao needs it responsive to talk to at all times.** Anything slow (regenerations, compiles, long queries) runs inside a dispatched agent — NOT as a background task; background Bash is banned entirely per [[orchestrator-sync-only-async-via-agents]] (Deyao, 2026-07-23: async was a source of bugs). Foreground tool calls stay in the seconds range. Before invoking anything, ask: "would this action be acceptable from a cron job, and does it return immediately?" — if either answer is no, dispatch or background it. Related: [[flt-continuous-loop-directives]], [[flt-no-lake-build-trust-mcp]], [[flt-stop-hook-is-a-nudge]].

**Design approval gate (Deyao, 2026-07-23):** "tell me the design first, i need to look at the design and approve it before you go about working on it because your design is not good a lot of the times." Infrastructure/architecture designs are presented to Deyao and approved BEFORE any implementation is dispatched.
