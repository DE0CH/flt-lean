# Memory index

- [W* top-down dependency tree](wstar-top-down-dependency-tree.md) — Deyao's 2026-07-16 directive: resolve Lean formalizations FLT-style, top-down, with a PROGRESS.md tree updated each iteration
- [W* continuous tool loop, no wakeup](wstar-continuous-tool-loop-no-wakeup.md) — Deyao 2026-07-16: never ScheduleWakeup; loop on "sorries left?" via tool calls until zero
- [W* no deferral, all sorries active](wstar-no-deferral-all-sorries-active.md) — Deyao 2026-07-16: nothing is "below" anything; never triage scope; every sorry is an active frontier node
- [FLT PROGRESS.md is generated](flt-progress-md-is-generated.md) — edit progress-entries.json + run progress-tree.py; proven leaves auto-hide; never hand-edit the tree
- [No private-shielded floating work](flt-no-private-shielded-floating.md) — Deyao 2026-07-18: never use `private` to dodge the free-floating check; open the consumer sorry first, always top-down
- [Sign FLT git commits](flt-sign-git-commits.md) — Deyao 2026-07-21: plain `git commit` (ssh-signing auto); never --no-gpg-sign again
- [Notify on μ-node completion](flt-notify-mu-node.md) — Deyao 2026-07-21: PushNotification when exists_weilPairing_mu is proven or abandoned
- [Stop-hook session guard](flt-stop-hook-session-guard.md) — the hook only drives the session id in .claude/stop-hook-session-id; successors must update it
- [No lake build; trust MCP](flt-no-lake-build-trust-mcp.md) — Deyao 2026-07-21: skip lake build in iterations, MCP diagnostics are the gate; the Stop hook still builds
- [Glue-first, no floating haves](flt-glue-first-no-floating-haves.md) — Deyao 2026-07-21/22: write the assembly first; sorry only against a stated goal; every have/let consumed (PreToolUse hook enforces)
- [Never delete Deyao's audit notes](never-delete-deyao-audit-notes.md) — Deyao 2026-07-21: notes questioning Claude's work stay byte-for-byte, even resolved
