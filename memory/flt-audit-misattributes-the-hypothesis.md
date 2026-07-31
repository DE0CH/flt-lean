---
name: flt-audit-misattributes-the-hypothesis
description: A leaf's own audit often credits one hypothesis with content that actually comes from another; separating the two IS the decomposition
metadata:
  type: project
---

A leaf docstring in this development usually explains *why* the statement is
true and *where each hypothesis is spent*. Those two explanations can disagree,
and when they do the leaf is usually cuttable for free.

`nonempty_modPullback_sectionIdeal` (RelativePicard.lean) is the worked case,
2026-07-31. Its 2026-07-29 audit said the flatness of the divisor over the base
"is the content of `isInvertibleSheaf_sectionIdeal` — an effective relative
Cartier divisor is flat over the base". That is false: invertibility of the
ideal is Cartier-ness and says nothing about flatness. Witness — `T = Spec k[s]`,
`Y = Spec k[s,t]`, `D = V(st)`: the ideal is invertible (`st` is a
nonzerodivisor) and `D` is not flat over `T`.

The flatness in fact came from a hypothesis the audit did not mention at all:
`x` is a SECTION, so `D_x ≅ T` over `T`. Once the two inputs were seen to be
independent, the leaf split with no mathematics left over — invertibility stayed
a leaf, flatness became a one-line `pullback.lift_snd`, and the residual
statement lost every mention of a curve.

**How to apply:** when a leaf resists, read its audit for a sentence of the form
"X is the content of Y". Check it. If X and Y are actually independent, that is
the cut line, and one of the two is usually already provable. See
[[flt-two-leaves-may-be-one]] for the dual failure (two leaves that are one) and
[[audit-searched-production-not-invariant]] for the other way audits go wrong.
