---
name: flt-hoist-vs-concurrent-proof
description: A hoist and a concurrent proof of the same leaf merge cleanly into a duplicate declaration; keep the hoisted location and move the proof
metadata:
  type: project
---

Relocating a leaf UPSTREAM (a hoist) and someone else PROVING it in place are
invisible to each other — both are uncommitted, so no branch diff and no
`~/.flt-inflight.jsonl` record shows the pair. Textual merge then puts the
declaration in **both** files: `has already been declared`, a hard error neither
diff predicts.

**Why:** a hoist changes a declaration's *location*; a proof changes its *body*.
Git merges those as unrelated edits to two different files.

**How to apply:** keep the hoisted LOCATION, move the PROOF into it, delete the
downstream copy. A statement conflicts; a proof transplants, since a hoist copies
the statement verbatim. Restoring the declaration downstream re-breaks whatever
upstream theorem the hoist existed to enable, and re-sorrying it upstream
manufactures a duplicate leaf. If a helper cannot move upstream, move it further
up (`Modularity/HeckeOperator.lean` is above `ModularCurve/X0.lean`) rather than
abandoning the hoist. Before any hoist, grep the *uncommitted diffs* of every
claimed worktree for the declaration NAME — the check in [[flt-preflight-finds-unowned-leaves]]'s
family, and `own.py`'s fourth check.

Observed 2026-07-31: `flt-lean-86` hoisted `relIndex_gamma0GL` and
`numCusps_le_order_qExpansion_norm` from `FreyCurve/MazurTorsion.lean` into
`ModularCurve/X0.lean` (to make `cuspForm_coe_eq_zero_of_ellipticSturm` provable)
while `flt-lean-104` held 369 uncommitted lines proving the second one in place.

Resolved the same day, once `flt-lean-104`'s work had reached `merger` (both
leaves PROVEN, ~1470 lines): the whole development was transplanted into
`X0.lean` at the hoisted location and `MazurTorsion.lean` kept only the one-line
corollary. **The transplant is always available**, because a hoist moves a
declaration UPSTREAM and its proof's import cone moves with it; the only blockers
are helpers defined downstream of the destination and missing `import`s. Frontier
went `−2` where either branch alone was `0`.

Two cheap checks make it safe: grep the destination for every declaration name the
moved block introduces (destinations here are 74 000 lines with their own
`Fermat.*` namespace), and stage the block in a throwaway module that `import`s the
destination — an `already declared` there IS the collision check, at scratch speed
rather than a 25-minute destination build.
