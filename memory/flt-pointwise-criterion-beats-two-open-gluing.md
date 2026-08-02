---
name: flt-pointwise-criterion-beats-two-open-gluing
description: "A route note prescribing \"glue a section on U to one on V\" is usually the expensive route; look for a POINTWISE criterion in the same file."
metadata: 
  node_type: memory
  type: project
  originSessionId: c676a19e-84e7-4cb5-898f-60f019c575a0
  modified: 2026-08-02T11:47:00.599Z
---

(2026-08-02, `flt-lean-158`, closing `nonneg_poleOrd_and_eq_zero_iff` in
`ModularCurve/PoleOrderValuation.lean`.)

That leaf's route note said: take the section on `U = A ∖ {O}`, take a section near `O`,
check they agree on the overlap (`AlgebraicGeometry.exists_res_eq_of_germ_eq`), glue
(`AlgebraicGeometry.exists_glue_of_agree`). Both lemmas exist and are proven; the route
works and it is the expensive one.

`AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_isInteger`, **in the same file**,
produces a section over `U` from a purely POINTWISE hypothesis — *for each `x ∈ U`, some
element of `𝒪_{X,x}` maps to `f` in `K(X)`*. At `U = ⊤` there are exactly two kinds of
point (in the chart: the germ of the chart function's own section; the one bad point: the
hypothesis). No overlap, no agreement check, no second open, no cocycle.

**Why the route's author missed it:** the pointwise lemma was written for a different
consumer and is named for that consumer, so a grep in the leaf's own vocabulary does not
find it. **The tell is that the route names TWO gluing lemmas** — a pointwise criterion
needs none.

**How to look:** grep the file the route already names for a lemma whose hypothesis is
quantified over POINTS rather than over a pair of opens.

Same family as [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-route-residue-is-the-cheap-route]]: a route note is written before anyone tries.
