---
name: flt-decl-order-tangle-is-a-graph
description: A "the intended order is not recoverable from the text" verdict on a declaration-order tangle is wrong — the order is forced by the comment-stripped dependency graph plus whichever block cannot move
metadata:
  type: feedback
---

Release 31 declined `X0.lean`'s `Gamma0GITPresentationOver` cluster (six errors,
~24 interleaved declarations) as unrecoverable and prescribed `git log -m -S` to
find the relocation commit.  Every hit is a merge commit, so that route is a dead
end — and the order does not need recovering.

**Why:** scan each name for `DECL`/`USES` over comment-MASKED source, write the
edges, then run `flt-hoistcheck.py` on each candidate block to find the one with
nonzero HITS — the block that cannot move.  Everything else is then forced:
dependencies rise to just above it, consumers sink to just below it, in graph
order.  Five blocks, one arrangement, applied atomically with
`tools/merge/blockmove.py` (which enforces the sorted-line-multiset receipt).

**How to apply it:** the graph does not tell you SCOPE.  Grep the moved text for
names from any `open` it is leaving — in CODE, since docstrings give false
positives — and do a scope-aware walk for depth-0 `variable` lines in the jumped
region.  Those are the two ways a verified-pure move still fails to compile.

Related: [[flt-see-the-merge-before-the-merger]].
