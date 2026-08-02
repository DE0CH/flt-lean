---
name: flt-cut-docstring-states-the-rule-it-breaks
description: "A leaf's docstring can say \"so it can be stated UPSTREAM and imported\" while the leaf sits downstream of its consumer — check the import direction, then hoist rather than delete"
metadata: 
  node_type: memory
  type: project
  originSessionId: d5e130a0-be49-4db0-aebf-d97dcfdb9e66
  modified: 2026-08-01T21:42:46.577Z
---

A dead-looking leaf whose INTENDED consumer exists and is still open is usually
**upstream** of it, so Lean forbids the citation and both stand open for ever.
This is the seventh-invisibility-class sub-case whose repair is a HOIST, not a
deletion — deleting destroys a correct cut. Seen 2026-08-01 on
`exists_localInertia_subgroup_relIndex_dvd_twelve_of_padicValRat_j_nonneg`, cut into
`FreyCurve/MazurTorsion.lean` while its consumer
`not_five_dvd_relIndex_of_padicValRat_j_nonneg` lives in
`FreyCurve/IsogenySignature.lean`, which MazurTorsion `public import`s.

**Why:** the cut's own docstring said the leaf "can be stated and proved in an
UPSTREAM module and imported" — the architectural requirement — and then it was
written downstream. Every mathematical judgement in that paragraph was right; the
one architectural sentence is what nothing checks, and a grep for the leaf's name
returns only its own declaration, which reads as ordinary dead code.

**How to apply:** on any dispatched leaf, `grep -rn '<leaf>' --include=*.lean Fermat/`
for consumers; if zero, find the consumer NAMED in the docstring and run
`grep -n 'import Fermat.FLT.<consumer module>' <leaf's module>`. A hit means hoist the
leaf to just above its consumer and cash the cut in — here the consumer really was
four lines (`Subgroup.relIndex_mul_relIndex` plus `5 ∤ 12`), verified in 4 s. Hoist the
leaf's own remaining blockers in the same commit, with a `Counter(lines)`-unchanged
receipt. See [[flt-hoisted-leaf-orphaned-by-reproof]],
[[flt-consumerless-leaf-is-dead-or-duplicate]], [[flt-leaf-blocked-by-declaration-order]].
