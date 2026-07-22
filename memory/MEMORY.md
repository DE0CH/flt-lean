# Memory index

- [FLT continuous-loop directives](flt-continuous-loop-directives.md) — Deyao 2026-07-16: top-down dependency tree, continuous tool-call loop (no wakeups, never stop after N iterations), no deferral: every sorry is an active frontier node
- [FLT PROGRESS.md is generated](flt-progress-md-is-generated.md) — edit progress-entries.json + run progress-tree.py; proven leaves auto-hide; never hand-edit the tree
- [No private-shielded floating work](flt-no-private-shielded-floating.md) — Deyao 2026-07-18: never use `private` to dodge the free-floating check; open the consumer sorry first, always top-down
- [Glue-first, no floating haves](flt-glue-first-no-floating-haves.md) — Deyao 2026-07-21/22: write the assembly first; sorry only against a stated goal; every have/let consumed (PreToolUse hook enforces)
- [Notify on μ-node completion](flt-notify-mu-node.md) — Deyao 2026-07-21: PushNotification when exists_weilPairing_mu is proven or abandoned
- [Stop-hook session guard](flt-stop-hook-session-guard.md) — the hook only drives the session id in .claude/stop-hook-session-id; successors must update it
- [No lake build; trust MCP](flt-no-lake-build-trust-mcp.md) — Deyao 2026-07-21: skip lake build in iterations, MCP diagnostics are the gate; the Stop hook still builds
- [Shared-terminal environment](shared-terminal-environment.md) — no docker/sudo, .venv, .env key, sources/, agent2 tmux pattern (since 2026-07-22)
- [Stop-hook restart pattern](stop-hook-tmux-restart.md) — hook disabled as `_DISABLED_Stop`; re-enable only via detached kill→rename→continue script
- [Orchestrator role in parallel mode](flt-orchestrator-role.md) — Deyao 2026-07-22: driver dispatches/integrates/commits only; all hands-on work goes to agents
