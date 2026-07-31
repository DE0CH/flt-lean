---
name: flt-take-the-arithmetic-out-of-the-leaf
description: A leaf docstring saying a count is "deliberately left inside the leaf" is a task description; pin a ROUNDED constant with measured head-room, never the exact one
metadata:
  type: project
---

(2026-07-31, `flt-lean-41`, `exists_stepanovRationalLinearFormsField` in
`Modularity/Interface.lean`.) The `λ = 1` half of Schmidt III carried a section
note saying its dimension count *"is the arithmetic the `λ = 1` prover owes; it
is not hard, and it is deliberately left inside the leaf because the exact
equation count depends on how the elimination is organised."*

That sentence is a **task description**, not a design decision. It was cut out
and PROVEN (`stepanov_equationCountRational_lt_unknownCount`), leaving the leaf
with §§7–9 and nothing else. Leaf count unchanged, 1 → 1 — judge such a cut by
what is LEFT in the leaf, per [[flt-cut-the-derived-half-out-of-a-leaf]].

**The reason the count could be pinned here and NOT in the `λ = 2` sibling is
MEASURED, not stylistic.** The sibling's docstring declines to pin `B` because
"Schmidt's §§7–9 route need not land on exactly the jet-route count", and its
margin is a single unit — pinning there really would risk a FALSE leaf. The
`λ = 1` margin is a factor `2d`. So:

* pin a **ROUNDED** constant, never the exact one. Here Schmidt's honest count is
  `qM + d(2d−3)·M(M−1)/2` and the pinned budget is `qM + d(d−1)·M²`, which
  dominates it at every `M` and leaves `≥ d·M²/2` of head-room for the
  bookkeeping a displayed bound hides (reducing `Y^c·(aY^i)^{(ν)}` back to
  `deg_Y < d` costs `X`-degree, and Schmidt does not display that);
* **measure the ceiling before choosing the constant.** At `d = 2` the true
  ceiling is `c·M²` with `c ≲ 3.5`; `d(d−1) = 2` fits, `2d(d−1) = 4` is FALSE
  (`d = 2`, `M = 162`, `q = 115600`: 18832176 equations vs 18829027 unknowns).
  Say both numbers in the docstring, so the next owner can raise the constant
  knowingly instead of guessing;
* **write down what would refute the pin.** Adding a bound to an existential
  STRENGTHENS the leaf, so the earlier faithfulness audit does not transfer —
  re-run it and say so ([[flt-decomposition-drops-a-hypothesis]] is the same rule
  for hypotheses).

Two cheap mechanics that paid here. The docstring's own worked numerical point
(`32780` equations vs `40933` unknowns at `d = 2, M = 4, q = 8192`) **identified
the intended count exactly** — `32780 = qM + d(2d−3)M(M−1)/2` on the nose — which
is how the formula was recovered without the source. And the crude lower bound
`stepanovUnknownCount ≥ (#terms)·(min term)` is enough for `λ = 1` where the
sibling needs all three summations carried out exactly, **except that the `k`-sum
may not be crudified**: replacing `∑_{k<d}(K+1−k)` by `d(K+2−d)` loses
`≈ d²(d−1)Q/2`, which is the whole margin, and the bound is then false at
`d = 2, M = 4`.
