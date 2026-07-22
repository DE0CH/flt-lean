---
name: flt-report-blocker-class
description: "Deyao 2026-07-22 — when anything is blocked/waiting, always state WHICH class the blocker is; trusted tools (language server/compiler) blocking is fine, Claude-automation (driver/agents) blocking is a defect"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T17:33:09.142Z
---

Deyao (2026-07-22): "you need to tell me clearly what blocked something, because what you and your agents do is buggy very very often (e.g. telling me about workers dirtying files etc), but other tools like the language server is not, so i need to know which one it is."

**Why:** Two reliability classes exist in this project. (a) Deterministic tooling — the language server, the Lean compiler, lake's on-demand builds, the daemon's imports — is trustworthy; waiting on it is normal and needs no intervention. (b) Claude-driven automation — the orchestrator and its agents — is frequently buggy (shared-tree file dirtying, half-applied edits, over-generalized rules). Deyao decides whether to intervene based on which class is responsible, so an unclassified "it's blocked/waiting" report is useless to him.

**How to apply:** Every report of a wait, blockage, refusal, or delay must name the blocking component AND its class explicitly, e.g. "blocked by the compile of X (trusted tool — fine, ETA minutes)" vs "blocked because agent Y broke Z (automation defect — being fixed by ...)". If the cause is unknown, say that and investigate before ending the report. Related: [[flt-orchestrator-role]], [[flt-report-blocker-class]] applies to Stop-hook nudges and agent reports relayed to Deyao as well.
