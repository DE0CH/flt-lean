---
name: flt-worktree-seed-artifacts
description: "SUPERSEDED (Deyao 2026-07-22, final): nothing in the codebase touches olean files AT ALL — the earlier seed-copying exception is withdrawn; worktrees start cold and the toolchain builds what it needs"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T19:51:42.914Z
---

FINAL RULE (Deyao, 2026-07-22, superseding this note's earlier seeding guidance and its later refinements): "nothing in our code base should touch olean files at all." No copying, no reading, no stat/mtime checks, no existence tests — by any script, agent instruction, or orchestrator command. The previously sanctioned seed-copy of `.lake` at worktree fan-out is WITHDRAWN.

**How to apply:** Fan-out = `git worktree add` + branch, nothing else; the language server / lake build whatever compiled state a worktree needs, on demand, when files are first opened (their job, their artifacts). Existing warm worktrees keep working (their `.lake` was built by the tooling in place — we just never touch it). The snapshot pipeline likewise must not copy `.lake`; its worktree's build state comes from the tooling running there. Historical context of the superseded seeding discussion is in git history of this file. Related: [[flt-no-lake-build-trust-mcp]], [[scripts-crash-dont-fallback]], [[flt-orchestrator-role]].
