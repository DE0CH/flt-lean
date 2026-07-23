---
name: flt-worktree-seed-artifacts
description: "Deyao 2026-07-22 (current): fan-out seeds .lake by ATOMIC COPY from the latest ZFS hourly autosnap — the one sanctioned artifact touch; otherwise nothing in the codebase touches olean files (no reads, stats, existence checks)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-23T00:42:43.002Z
---

CURRENT RULE (Deyao, 2026-07-22, late-session final): "i want atomic copy, when you fan out, just atomic copy the .lake folder to the new work tree. that's it, that's for sure a consistent state the new compiler can use."

**THE RULE, one line: when seeding a new worktree, atomic-copy `.lake` — i.e. `LATEST=$(ls -d /home/chend/.zfs/snapshot/autosnap_* | sort | tail -1); cp -a "$LATEST/flt-lean/.lake" <new-worktree>/.lake`. Nothing else.**

**Why this is the atomic copy (investigated twice, 2026-07-22/23):** /home/chend is NFS on ZFS (`homes1:/tank/home/chend`). Client-side there is NO way to trigger a snapshot or reflink-clone (no `zfs` CLI, ssh to homes1 permission-denied, `cp --reflink` unsupported over NFS) — but the server takes HOURLY (+ daily) autosnaps, browsable read-only at `/home/chend/.zfs/snapshot/autosnap_*/`. Each autosnap IS an atomic, immutable, point-in-time image, so copying out of the newest one is an atomic copy in the sense that matters: the source cannot change mid-copy, and the captured state is crash-consistent (a mid-build capture is like a power-cut state, which the compiler reconciles by content hash). Worst case the seed is ≤1 h behind — incremental rebuild, never inconsistency. Plain `cp -a`, never hardlinks.

**Scope of the earlier "no olean touching" rule (still in force otherwise):** no script or agent reads, stats, fingerprints, or existence-checks olean files; building/invalidation belongs to the language server / lake. The atomic seed-copy at fan-out is the ONE sanctioned touch (it reads a frozen snapshot, not the live build tree, so it cannot race anything). Related: [[flt-no-lake-build-trust-mcp]], [[scripts-crash-dont-fallback]], [[flt-orchestrator-role]].
