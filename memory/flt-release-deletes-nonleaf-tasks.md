---
name: flt-release-deletes-nonleaf-tasks
description: "flt-cycle.py release silently deletes queued tasks that name no Lean declaration (relocations, reconciliations) — re-verify structural tasks after every release"
metadata: 
  node_type: memory
  type: project
  originSessionId: 0dcd9de4-e92b-4213-94e8-e5bca672954a
  modified: 2026-07-27T08:48:06.683Z
---

`python3 flt-cycle.py release` runs a queue-correction phase that harvests
declaration names from each queued task and drops tasks whose targets are
PROVEN on the new release. **A task that names no declaration has nothing to
match, and can be deleted.**

Observed 2026-07-27: the X0.lean section-relocation task — the single biggest
blocker on the merge batch, scheduled at queue position 2 — vanished during a
release. Its TARGET block named branches (`flt-lean-183`, `-181`, `-57`, `-140`)
rather than a Lean declaration. It had to be restored by hand.

**Why:** the vulnerable tasks are exactly the ones I write as orchestrator and
nobody else does — relocations, reconciliations of two branches that did
incompatible things to one declaration, hoists, and "check the gate and stop"
tasks. These are also the highest-value tasks in the queue, because they unblock
clusters rather than closing single leaves.

**How to apply:** after every `flt-cycle.py release`, re-check that structural
tasks survived, and re-check queue ORDER — position matters when a task must run
against a quiet file (see [[flt-x0-relocation-needs-quiet-main]]). Cheap check:

    grep -c "<distinctive phrase from the task>" ~/.flt-task-queue

Better: give every structural task a real Lean declaration in its TARGET line
even when the work is a move, so the correction phase can classify it.

Related: [[flt-bookkeeping-cadence]], [[flt-fleet-13-worktree-protocol]].

## Corollary (2026-07-27): `release` ALSO auto-tags — do not tag manually

`flt-cycle.py release` creates the `vN` tag itself. Tagging by hand as well produced **`v18` and `v19`
pointing at the same commit** (`2ed0b703`), so one green release consumed two version numbers. Neither
tag was deleted — a published tag is outward-facing and both point at a genuinely green release, so the
cost of the duplicate is cosmetic and the cost of deleting is not.

**Let the script own the tag.** Also note `git tag --list | tail` sorts lexicographically, so `v10` sits
between `v1` and `v2`; to find the real maximum use `git tag --list 'v*' | sed 's/^v//' | sort -n | tail -1`.
