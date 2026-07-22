---
name: flt-no-lake-build-trust-mcp
description: "Deyao 2026-07-21/22: nobody (orchestrator or agents) runs lake build — the lean-lsp MCP is the trusted, faster gate; lake build is Deyao's own extra insurance only"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 4f31fd20-64ff-4ddd-97fd-59258398c883
  modified: 2026-07-22T17:08:35.145Z
---

Deyao (2026-07-21, FLT loop): do NOT run `lake build` as the per-iteration
gate — trust the lean-lsp MCP entirely: if `lean_diagnostic_messages`
reports no errors, commit on that basis.

Reinforced 2026-07-22 (orchestrator/fleet mode): "no one should be using
lake build because the lean mcp is trusted and faster. only i should be
using lake build as an extra insurance but that's my job, not yours so
don't worry about it."

**Why:** MCP diagnostics come from the same Lean elaborator, minutes
faster (persistent server, no job graph); lake builds also churn oleans,
destabilizing the daemon and other agents.

**How to apply:** Orchestrator integration verification = MCP diagnostics
on merged files in main. Worktree agents (whose files the main-rooted MCP
cannot see) use `lake env lean <file>` single-file checks — the daemon's
own direct mechanism, not a build. NO full build is the orchestrator's to run — not via `lake build`, and not via the side door of MCP-opening the ROOT file (that triggers the full closure, i.e. a full build in disguise; Deyao 2026-07-22 corrected this twice). The division: per-file MCP diagnostics at integration (required verification anyway) incrementally rebuild just the touched files' import closures — that is the ONLY state-refresh automation performs; full-coverage builds are Deyao's manual insurance, and progress regeneration completes at those moments (the refuse-guard keeps partial views from rendering) ([[flt-stop-hook-session-guard]],
[[flt-stop-hook-is-a-nudge]], [[flt-orchestrator-role]]).
