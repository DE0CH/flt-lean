# Memory index

- [FLT continuous-loop directives](flt-continuous-loop-directives.md) — Deyao 2026-07-16: top-down dependency tree, continuous tool-call loop (no wakeups, never stop after N iterations), no deferral: every sorry is an active frontier node
- [FLT PROGRESS.md is generated](flt-progress-md-is-generated.md) — edit progress-entries.json + run progress-tree.py; proven leaves auto-hide; never hand-edit the tree
- [No private-shielded floating work](flt-no-private-shielded-floating.md) — Deyao 2026-07-18: never use `private` to dodge the free-floating check; open the consumer sorry first, always top-down
- [Glue-first, no floating haves](flt-glue-first-no-floating-haves.md) — Deyao 2026-07-21/22: write the assembly first; sorry only against a stated goal; every have/let consumed (PreToolUse hook enforces)
- [Notify on μ-node completion](flt-notify-mu-node.md) — Deyao 2026-07-21: PushNotification when exists_weilPairing_mu is proven or abandoned
- [Stop-hook session guard](flt-stop-hook-session-guard.md) — the hook only drives the session id in .claude/stop-hook-session-id; successors must update it
- [No lake build; trust MCP](flt-no-lake-build-trust-mcp.md) — Deyao 2026-07-21/22: nobody runs lake build (MCP is the trusted gate; worktree agents use lake env lean); insurance builds are Deyao's job
- [Shared-terminal environment](shared-terminal-environment.md) — no docker/sudo, .venv, .env key, sources/, agent2 tmux pattern (since 2026-07-22)
- [Stop-hook restart pattern](stop-hook-tmux-restart.md) — hook disabled as `_DISABLED_Stop`; re-enable only via detached kill→rename→continue script
- [Orchestrator role in parallel mode](flt-orchestrator-role.md) — Deyao 2026-07-22: driver dispatches/integrates/commits only; all hands-on work goes to agents
- [Progress snapshot via worktree](flt-progress-snapshot-worktree.md) — Deyao 2026-07-22: regenerate PROGRESS.md from committed state in a secondary worktree at every agent-completion/milestone
- [Stop hook is a nudge](flt-stop-hook-is-a-nudge.md) — Deyao 2026-07-22: automatic back-to-work prompt, not a safety net; fail open, best-effort
- [Report blocker class](flt-report-blocker-class.md) — Deyao 2026-07-22: every wait/blockage report must name the blocker AND its class: trusted tool (fine) vs Claude automation (defect)
- [Atomic-snapshot fan-out seeding](flt-worktree-seed-artifacts.md) — Deyao 2026-07-22: seed .lake by atomic copy from the latest ZFS hourly autosnap (.zfs/snapshot); otherwise nothing touches olean files
- [Scripts get a server, not MCP](scripts-get-a-server-not-mcp.md) — Deyao: headless scripts that can't use MCP effectively get a thin persistent server; delegate loading/invalidation to standard tooling
- [Caller-directed script error policy](scripts-crash-dont-fallback.md) — Deyao 2026-07-22: Claude-called scripts crash loudly, no fallbacks; harness/Deyao-called scripts (Stop hook) need reasonable graceful fallbacks
