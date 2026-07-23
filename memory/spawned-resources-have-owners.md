---
name: spawned-resources-have-owners
description: "Deyao 2026-07-23 — 'you are a computer program spawning children and didn't stop them when you don't need them anymore': every resource a dispatch causes to exist (workers, servers, processes, worktrees' warm state) is leaked unless its release is tied to the task's end"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T01:39:12.302Z
---

Deyao (2026-07-23, after ~87 GB of language-server workers lingered for finished agents): "that is a memory leak, you are leaking memory, you are a computer program spawning children and didn't stop them when you don't need them anymore."

**Why:** "Resident by design" describes a child's behavior, not the owner's responsibility. The orchestrator is a program; resources that its dispatches cause to exist (LSP file-workers, per-root servers, resident daemons, background processes) have no other owner. Abundant RAM merely postpones the symptom — the leak exists the moment a task ends without releasing what it held.

**How to apply:** Pair every spawn with a release point at dispatch time. Concretely in this project: the integration step for a finished agent includes reaping its worktree's LSP workers (kill by worktree path match — they respawn on demand if ever needed) and any per-agent processes; stopping a fleet wave includes sweeping all its worktrees' workers; session end includes checking `ps` for orphans of this session's making. If a resource should outlive its task, that is an explicit decision with a named new owner (e.g. the systemd report server), never a default. Related: [[flt-orchestrator-role]], [[dont-invent-delegate-to-existing-tools]].
