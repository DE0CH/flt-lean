---
name: scripts-get-a-server-not-mcp
description: "Deyao — scripts may have difficulty using MCP effectively (or it's hacky); in that case give scripts a separate persistent server they can talk to directly"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T18:39:40.061Z
---

Deyao (restated 2026-07-22): scripts (hooks, generators, cron-like processes) may not be able to use MCP tools effectively — MCP lives in the assistant's tool harness, and shoehorning script access to it is hacky. When headless consumers need a capability that interactive tools get from MCP, the right architecture is a SEPARATE PERSISTENT SERVER (detached background process, e.g. socket + JSON) that scripts query directly.

**Why:** Two consumer classes exist: harness-attached (me, agents — use MCP) and headless (Stop hook, progress-tree.py — cannot). A persistent server gives the headless class the same amortized-load benefit (e.g. the ~20s Lean environment import paid once, then millisecond queries) that the language server gives the MCP class.

**How to apply:** Keep the server SHELL thin (socket, resident state, the domain query code) and delegate everything the standard tooling already does — loading, cache invalidation, dependency building — to that tooling (e.g. reload = `lake lean <census file>`, letting lake handle freshness), because hand-rolled invalidation is where the 2026-07-22 daemon bugs all lived. The FLT instance: lean-daemon.py's socket+persistence is the right architecture; its freshness/materialization machinery was the wrong part. Related: [[flt-report-blocker-class]], [[flt-no-lake-build-trust-mcp]].
