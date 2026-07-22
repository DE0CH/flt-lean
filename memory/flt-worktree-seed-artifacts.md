---
name: flt-worktree-seed-artifacts
description: "Deyao 2026-07-22 (current): fan-out seeds .lake by ATOMIC COPY from the latest ZFS hourly autosnap — the one sanctioned artifact touch; otherwise nothing in the codebase touches olean files (no reads, stats, existence checks)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
  modified: 2026-07-22T23:59:10.183Z
---

CURRENT RULE (Deyao, 2026-07-22, late-session final): "i want atomic copy, when you fan out, just atomic copy the .lake folder to the new work tree. that's it, that's for sure a consistent state the new compiler can use."

**Mechanism (verified on this system):** /home/chend is NFS on ZFS (`homes1:/tank/home/chend`) with HOURLY autosnaps browsable at `/home/chend/.zfs/snapshot/autosnap_*_hourly/`. A snapshot is atomic and immutable — a mid-build state captured there is still crash-consistent the way a power-cut state is, which the compiler handles (content-hash reconcile). Fan-out seeding = `cp -a /home/chend/.zfs/snapshot/<latest hourly>/flt-lean/.lake <new-worktree>/.lake` (pick the newest autosnap; plain copy, never hardlinks). No ssh/zfs admin access is available (tested: permission denied) — the hourly autosnaps are the trigger-free source.

**Scope of the earlier "no olean touching" rule (still in force otherwise):** no script or agent reads, stats, fingerprints, or existence-checks olean files; building/invalidation belongs to the language server / lake. The atomic seed-copy at fan-out is the ONE sanctioned touch (it reads a frozen snapshot, not the live build tree, so it cannot race anything). Related: [[flt-no-lake-build-trust-mcp]], [[scripts-crash-dont-fallback]], [[flt-orchestrator-role]].
