---
name: flt-refactor-has-two-bases
description: A large mechanical refactor needs a green base to verify on and the merge worker's base to land on; when main and merger diverge those differ and the work is blocked
metadata:
  type: project
---

A mechanical refactor (block relocation, module split, cross-file hoist) has a
**verification base** — one where `lake build` is green — and a **merge base** —
the tree the merge worker is actually holding. Nothing makes those the same, and
when they are not, the refactor cannot be delivered however correct it is.

Measured 2026-07-31 on the `X0.lean` Mazur relocation: `main` was **868 commits**
behind `merger`, with `X0.lean` differing by `+43 356 / −17 099` (81 530 →
107 787 lines), so coordinates named on one side do not exist on the other; and
`merger`'s `X0.lean` **did not build** (release 27 withheld over it — see
`tools/merge/RELEASE-27-HANDOVER.md`). Verifiable only where it could not land;
landable only where it could not be verified.

**Why:** worktrees are dispatched off `main`, but branches are merged into
`merger`, and `merger` runs ahead by a whole release. A small diff survives that
gap; a five-thousand-line move does not.

**How to apply:** before starting any refactor bigger than a few hundred lines,
run `git rev-list --count main..merger` and
`git diff --stat main merger -- <the file>`. Seconds against hours. If they have
diverged, **ship the transform, not the diff** — a script whose anchors match by
CONTENT, are asserted unique, and whose declaration set is RECOMPUTED from source
each run, so it replays onto whatever base is current
(`flt-hoist-genusone.py` is the worked example; `flt-lean-123` hand-made the same
edit correctly and it was declined at release 22 purely on conflict volume).

Related: [[flt-see-the-merge-before-the-merger]] (merge in memory before the
merger does), [[flt-hoist-vs-concurrent-proof]] (a hoist and a concurrent proof
merge into a duplicate declaration).
