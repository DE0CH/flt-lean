---
name: flt-no-lake-build-trust-mcp
description: "Deyao 2026-07-21: don't run lake build in loop iterations — trust lean-lsp MCP diagnostics entirely; lake build is too slow"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 4f31fd20-64ff-4ddd-97fd-59258398c883
---

Deyao (2026-07-21, FLT loop): do NOT run `lake build` as the per-iteration
gate before commits — it is too slow. Trust the lean-lsp MCP entirely: if
`lean_diagnostic_messages` reports no errors, everything is fine; commit on
that basis.

**Why:** the MCP diagnostics come from the same Lean elaborator; a clean
diagnostic pass is the same signal as a module build, minutes faster.

**How to apply:** iterate with `lean_goal`/`lean_diagnostic_messages`
(absolute paths), commit when diagnostics are clean. The Stop hook still
runs the full `lake build` itself as the final compiler-verified exit
check ([[flt-stop-hook-session-guard]]), so the root gate remains enforced
without manual builds.
