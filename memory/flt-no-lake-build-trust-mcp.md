---
name: flt-no-lake-build-trust-mcp
description: "Deyao 2026-07-21/22: the MCP is the verification gate for EVERYTHING — lake build (and lake env lean) banned for automation; every consumer gets an MCP door (per-worktree servers for agents, the detached report server for scripts)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 4f31fd20-64ff-4ddd-97fd-59258398c883
  modified: 2026-07-22T18:47:21.878Z
---

Deyao (2026-07-21, FLT loop): do NOT run `lake build` as the
per-iteration gate — trust the lean-lsp MCP entirely: if
`lean_diagnostic_messages` reports no errors, commit on that basis.

Reinforced 2026-07-22 (orchestrator/fleet mode): "no one should be
using lake build because the lean mcp is trusted and faster"; banned via
permissions.deny in .claude/settings.json with an explanation pointing
to the MCP. `lake env lean` banned too: "there shouldn't be a thing
that can't reach an MCP server."

**Why:** MCP diagnostics come from the same Lean elaborator, minutes
faster (persistent server, no job graph); build-system invocations
churn artifacts that destabilize other consumers. Every past exemption
("worktree agents can't reach the MCP", "headless scripts need a CLI
door") was an architecture gap to fix, not a reason to bypass the gate.

**How to apply:** Every consumer gets an MCP door: the driver uses the
main-repo lean-lsp server; each worktree agent uses a lean-lsp server
rooted at ITS worktree (registered per-worktree in .mcp.json — each
agent sees different sources, so each needs its own server); headless
scripts (Stop hook, progress generation) query the detached persistent
report server ([[scripts-get-a-server-not-mcp]]). Related:
[[flt-orchestrator-role]], [[flt-report-blocker-class]],
[[flt-stop-hook-is-a-nudge]].
