---
name: flt-preflight-finds-unowned-leaves
description: "flt-cycle.py preflight is the ONLY check that finds sorries with no owner; run it between releases, not just at them"
metadata: 
  node_type: memory
  type: project
  originSessionId: 0dcd9de4-e92b-4213-94e8-e5bca672954a
  modified: 2026-07-27T12:39:27.549Z
---

`python3 flt-cycle.py preflight` finds **direct sorries that no live agent and no
queued task covers**. On 2026-07-27 it found **6** in one run and **18** in
another — none of which any completion report had mentioned.

**Why the notification path cannot catch these.** An agent reports the leaves it
*knows* it left. It misses (a) leaves its decomposition created but its report
did not enumerate, (b) anonymous sorried `have`s inside a body, which have no
name to report and no `TARGET:` line to own them, and (c) leaves stranded when a
predecessor's belief that "another owner has this" went stale. All three are
invisible to the merge/batch/queue loop, which only ever sees what agents say.

**So: run preflight between releases, not only as part of one.** It is cheap
relative to a release (no census), and the loop invariant — every sorry has an
owner at all times — is otherwise unenforced.

Two related gotchas, both hit the same day:

- Preflight also flags worktrees holding unmerged work with no route home, and
  suggests `flt-cycle.py done <wt>`. **That suggestion is wrong when the merger
  deliberately dropped the branch** as superseded — re-batching it resurrects
  stale content. Verify (declaration names absent from main, file sizes, base
  staleness), then tag `superseded/<branch>` and reset the branch to main
  instead. See [[flt-release-deletes-nonleaf-tasks]] for the sibling hazard.
- When queueing a batch of unowned leaves, **count them back**. Grouping 18
  leaves into 7 tasks silently dropped one; the next preflight caught it.

Related: [[flt-bookkeeping-cadence]], [[flt-fleet-13-worktree-protocol]].
