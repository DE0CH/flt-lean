---
name: flt-inlining-refactor-orphans-its-leaf
description: "A same-file refactor that inlines a proof orphans the leaf it was cut from; both docstrings keep naming it, and the repair is to invert the dependency, not to prove or delete"
metadata: 
  node_type: memory
  type: project
  originSessionId: b9e1f123-1df8-4c9e-83df-25fbbeb9fcc5
  modified: 2026-08-01T11:20:45.016Z
---

(2026-08-01, `flt-lean-283`, `natDegree_ΨSq_ne_zero_of_not_dvd` in
`EllipticCurve/HasseBound.lean`.) A leaf can be orphaned with **no merge and no
second branch**, by an ordinary refactor in one file: cut A splits parent `P`
into leaf `L` plus glue; cut B, a day later, builds machinery elsewhere in the
same file and rewrites `P`'s body to run it INLINE. Both edits are correct.
Together they leave `L` open with **zero code consumers**, while both `L`'s and
`P`'s docstrings still name `L` as the primitive.

**Detector**: grep the leaf's name comment-stripped and classify each hit. Own
declaration line + docstrings only ⇒ dead. Then read `P`'s **proof body** — if it
does not name `L`, that body IS the missing proof of `L`.

**Repair is neither obvious move.** Proving `L` standalone leaves free-floating
code (forbidden here); deleting `L` throws away a true, audited statement often
better to own than `P`. Instead **move `P`'s inlined body up onto `L` and
re-derive `P` over it**. The transplant is usually verbatim: the body consumes
only the hypothesis `by_contra` produced from `P`'s conclusion, and a proven
`iff` supplies the same thing from `L`'s. Frontier −1, no new leaf, both
docstrings true again.

**Rider**: `L`'s route note said "THE ROUTE IS UNCHANGED" and prescribed a whole
classical theory (Deuring, Hasse invariant) — written before the machinery that
closes `L` landed in the same file. Re-read the file's newest section headings
before costing anything off a route note. See [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-consumerless-leaf-is-dead-or-duplicate]], [[flt-delete-times-refactor-orphans-a-leaf]].
