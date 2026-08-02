---
name: flt-size-a-port-by-base-specific-statements
description: "Price a base-generalisation port by counting declarations whose STATEMENT is base-specific, and split an avoidance device's cardinality role from its stability role."
metadata: 
  node_type: memory
  type: project
  originSessionId: 96129984-22e1-45db-988a-a24a8cee9822
  modified: 2026-08-02T11:52:45.353Z
---

A route note that prices a port at "8 500 lines, re-run the 94 assembly steps" is
unactionable. The measurement that is: strip comments, list top-level
declarations, take each one's text up to its first `:=`, and grep THAT for the
base-specific vocabulary.

Measured 2026-08-02 on `Fermat/FLT/EllipticCurve/WeilPairing.lean`: **21 of 49**
declarations mention `ZMod q`, `frobFixed`, `frobPeriod`, `frobAlgHom`,
`frobeniusTorsionEnd` or `Fact q.Prime` in their STATEMENT — including
`weilValueProp`, whose very type is `WeierstrassCurve (ZMod q) → …`, so no
instantiation reaches it.

**Why:** it both confirms the audit's verdict (the port is a rewrite, not a base
substitution) and hands the next owner a work list instead of a wall.

**How to apply:** run it before accepting or rejecting any "generalise the base"
task. And when an audit condemns an *avoidance/genericity device*, separate its
two roles — they generalise differently and only one is the obstruction:

* the CARDINALITY role ("pick a point whose abscissa avoids the finite subfield
  `F`") SURVIVES over any algebraically closed base with `F` finitely generated,
  because an algebraically closed field is never finitely generated over its prime
  field;
* the STABILITY role (`frobFixed q (…) ≤ F`, i.e. `F` is Frobenius-stable) has NO
  analogue: the auxiliary generic points are not algebraic over the base, so their
  `σ`-orbits need not lie in a finitely generated field.

Attack the stability clause first. Same family as
[[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-relocation-cost-and-payoff-differ]].
