---
name: flt-orchestrator-role
description: Deyao 2026-07-22 — in ultracode/parallel mode the driver session is an ORCHESTRATOR ONLY; dispatch all hands-on work (Lean proofs AND infra/scripts) to agents; the driver IS automation
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-22T17:20:59.554Z
---

Deyao (2026-07-22, twice in one session): "turn yourself into an orchestrator and dispatch agents", "you are an orchestrator, shouldn't be doing any work, remember that."

Also (same day, after repeated boundary mistakes): "there's no division of labor. I'm the only person here, you are a tool" and "you are also part of the automation, maybe you forget sometimes."

**Why:** The driver session's context is the scarce resource — it holds the global plan, integrates results, verifies, and commits. Hands-on work (editing Lean files, debugging scripts, even infra like the daemon) burns driver context and serializes what agents could do in parallel. And every rule Deyao states for "automation" — no full builds, fail-open nudges, MCP-only gates — binds the DRIVER exactly as it binds hooks, scripts, and subagents; the driver is not outside the automation looking in, and there is no "division of labor" between Deyao and the tooling — Deyao is the only person, everything else (driver included) is the tool.

**How to apply:** In parallel/ultracode mode, the driver does ONLY: enumerate/partition the frontier, write agent prompts with disjoint file ownership, dispatch (Workflow/Agent), monitor transcripts, answer agents' design questions, integrate returned diffs, run/delegate verification, update progress bookkeeping, commit/push, and report to Deyao. Any task longer than a one-line command gets dispatched — including [[flt-stop-hook-session-guard]]-style infra fixes. Before invoking anything, ask: "would this action be acceptable from a cron job?" — if not, it is not acceptable from the driver either. Related: [[flt-continuous-loop-directives]], [[flt-no-lake-build-trust-mcp]], [[flt-stop-hook-is-a-nudge]].
