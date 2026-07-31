---
name: flt-cycle-verdict-expires
description: An "impossible, genuine import cycle" verdict taken while the leaves under it were open describes their INTENDED proofs; re-measure against the branch where the proofs exist
metadata:
  type: project
---

A recorded verdict that a hoist is blocked by an import cycle is a claim about
the tree it was measured on. **An open leaf's body contributes no dependencies**,
so a cycle traced through a still-sorried declaration is a claim about its
*intended* proof, and the proof that eventually lands need not take that route.

Observed 2026-07-31. `flt-hoist-genusone.py` hoists only the genus-one branch
and records why: `_thirtySeven` and `_classNumberOne` reach
`exists_endMinpoly_of_stable_cyclic_mazurLevel` → Mazur's isogeny-character
descent → `exists_goodReductionModel_of_surjective` / `exists_neronExtension` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean`, which `public import`s
`X0.lean` — "a genuine import cycle, with no sorried link to cut it at". True
when written. **Ten of the eighteen leaves in the two namespaces closed within a
day**, and on `merger` the transitive source closure of the whole remaining
`MazurIsogenyPrimeJ` tail (197 seed, 224 closed) needs 27 declarations outside
it, all inside `MazurTorsion.lean`, **none reaching
`exists_abelianGoodReductionModel`** — so none reaching `NeronModel.lean`.

**Why:** it is the same decay as "still open, owned elsewhere" in a commit
message — a hypothesis about a frontier that then moved, preserved in a form
that cannot be updated. "There is no route" ages exactly as badly as "there is
still work here".

**How to apply:** re-measure a cycle claim against the branch where the proofs
EXIST (`git show merger:<file>` + a comment-stripped, isalnum-tokenised
transitive closure), never against the tree where the leaves are open. The real
blocker is usually smaller and unlooked-at: here it is
`Fermat.IsBaseChangeOfGamma1.{refl, comp, along_injective}` in `X1.lean` (which
also imports `X0.lean`), whose closure is **eleven declarations** / ~270 lines.

Related: [[flt-refactor-has-two-bases]], [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]].
