---
name: dont-invent-delegate-to-existing-tools
description: "Deyao 2026-07-22/23 — Claude kept inventing infrastructure (protocols, freshness machinery, daemons, policies) where existing tools already did the job; the fix was always deleting the invention. Before building anything, name the existing tool that already does it."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T00:59:04.981Z
---

Deyao (2026-07-23, after a day of infra corrections): "not we. you invented, you kept inventing things."

The record of that day, each invention mine (Claude's), each correction Deyao's, each fix a deletion in favor of something that already existed:
- custom socket protocol + daemon between scripts and the compiler → scripts speak LSP framing directly to a detached `lake serve`;
- freshness scans / import-closure exclusion / force-bad sets / materialization orchestration → lake's content-hash incremental build and the language server's own invalidation;
- olean stash/restore across rebuilds → don't touch artifacts at all; the toolchain owns them;
- cache-fallback rendering of the progress tree → crash loudly with the compiler's error (the caller handles it);
- "fail-open" hook policy invented and then MISATTRIBUTED to Deyao → his actual words were only "it's a nudge, not a safety net"; policy questions got re-derived from the caller principle;
- hand-managed worktree seeding procedures → one atomic copy from the ZFS autosnap.

**Why:** Invented layers exist to translate between something Claude made up and something that already existed; they double the work (both sides still need the real interface) and concentrate all the bugs. Every incident traced to an invention; none traced to the existing tools.

**How to apply:** Before writing any infrastructure — a protocol, a cache, a freshness check, a recovery policy, a wrapper process — name the existing tool that already provides it (compiler, language server, lake, git, filesystem/snapshots, the harness). If one exists, use it directly, even when that looks less capable at first. Only build what provably has no existing owner, and say so explicitly when proposing it. And never attribute a design choice to Deyao that he did not state in words — quote him when recording policy. Related: [[flt-report-blocker-class]], [[scripts-crash-dont-fallback]], [[flt-no-lake-build-trust-mcp]], [[flt-orchestrator-role]].
