---
name: flt-weaken-the-leaf-to-an-inequality
description: "A leaf stating a numerical IDENTITY may polarise out of the INEQUALITY its route actually produces — weakening it deletes the sharpening step (separability, genericity) entirely"
metadata: 
  node_type: memory
  type: project
  originSessionId: bfa35f0c-b446-413a-b6e1-697360c724aa
  modified: 2026-07-31T07:04:44.493Z
---

When a leaf's conclusion is a numerical identity (a parallelogram law, a degree
count, a rank equality), ask whether its own prescribed route yields the identity
or only a one-sided bound. Fibre counts, root counts and dimension bounds are
one-sided by nature; the step that sharpens them is usually a separability,
flatness or genericity argument that is a whole development.

Measured 2026-07-31 on `EllipticCurve/IsogenyTrace.lean`'s only leaf,
`End.isXNormalForm_natDegree_parallelogram`: its `x`-coordinate route counts roots
of `A − X B`, so it gives `≤` and needs squarefreeness for `=`. But a
parallelogram identity POLARISES — `≤` for every pair, instantiated at the pair
`(φ+ψ, φ−ψ)` whose sum and difference are `[2]φ` and `[2]ψ`, returns the reverse
inequality from `deg [2] = 4`. Three lines. The leaf is now stated with `≤` and
the separability step is gone from the file.

**Why:** the sharpening step is invisible in the leaf's statement and is where the
cost is. Weakening the conclusion is also the ONE restatement whose earlier
faithfulness audit transfers (every counterexample to the weaker form refutes the
stronger), so it is cheap to land.

**How to apply:** before attacking such a leaf, (1) check whether the conclusion
polarises or otherwise self-sharpens; (2) restate it as the one-sided form the
route produces; (3) re-check WHICH hypotheses are still load-bearing — weakening
the conclusion makes some removable and leaves others fatal, and only that check is
real work; (4) say in the docstring that the audit transfers and why. The leaf
count does not move: judge by what is LEFT in the leaf, per
[[flt-leaf-cost-estimates-are-hypotheses]].
