---
name: spawned-resources-have-owners
description: "Deyao 2026-07-23 — 'you are a computer program spawning children and didn't stop them when you don't need them anymore': every resource a dispatch causes to exist (workers, servers, processes, worktrees' warm state) is leaked unless its release is tied to the task's end"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T01:42:45.027Z
---

Deyao (2026-07-23, after ~87 GB of language-server workers lingered for finished agents): "that is a memory leak, you are leaking memory, you are a computer program spawning children and didn't stop them when you don't need them anymore."

**Why:** "Resident by design" describes a child's behavior, not the owner's responsibility. The orchestrator is a program; resources that its dispatches cause to exist (LSP file-workers, per-root servers, resident daemons, background processes) have no other owner. Abundant RAM merely postpones the symptom — the leak exists the moment a task ends without releasing what it held.

**How to apply (corrected by Deyao, same day: "it's one reliable and deterministic computer program against another that's buggy and random all the time"):** release must be enforced by DETERMINISTIC machinery, never by Claude remembering — "Claude will reap at integration" is not a mechanism, it is the unreliable program promising to behave. Concretely: worker lifecycle belongs to native toolchain limits or a systemd timer reaper (flt-worker-reaper); session-scoped processes belong to the harness/session lifetime; long-lived residents get a named systemd owner (e.g. flt-report-server). The GENERAL rule: any recurring obligation ("do X every time Y happens") must be executed by a hook, unit, timer, or the tool's own lifecycle — Claude's role is limited to one-off judgment calls that cannot be specified in advance. Related: [[flt-orchestrator-role]], [[dont-invent-delegate-to-existing-tools]].
