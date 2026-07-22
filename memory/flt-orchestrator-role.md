---
name: flt-orchestrator-role
description: Deyao 2026-07-22 — in ultracode/parallel mode the driver session is an ORCHESTRATOR ONLY; dispatch all hands-on work (Lean proofs AND infra/scripts) to agents
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-22T16:22:27.402Z
---

Deyao (2026-07-22, twice in one session): "turn yourself into an orchestrator and dispatch agents", "you are an orchestrator, shouldn't be doing any work, remember that."

**Why:** The driver session's context is the scarce resource — it holds the global plan, integrates results, verifies, and commits. Hands-on work (editing Lean files, debugging scripts, even infra like the daemon) burns driver context and serializes what agents could do in parallel.

**How to apply:** In parallel/ultracode mode, the driver does ONLY: enumerate/partition the frontier, write agent prompts with disjoint file ownership, dispatch (Workflow/Agent), monitor transcripts, answer agents' design questions, integrate returned diffs, run/delegate verification, update progress bookkeeping, commit/push, and report to Deyao. Any task longer than a one-line command gets dispatched — including [[flt-stop-hook-session-guard]]-style infra fixes. Related: [[flt-continuous-loop-directives]].
