---
name: flt-route-noun-declared-below
description: "A leaf's prescribed route can be unstatable at its own line because the VOCABULARY it needs is declared below — grep the nouns, and hoist the definition, not the theory"
metadata: 
  node_type: memory
  type: project
  originSessionId: 910cfdd2-5402-4bd3-bd13-7abca3d03d17
  modified: 2026-08-02T20:29:44.834Z
---

(2026-08-02, `flt-lean-50`, `exists_nonConstantClassify_gamma0Datum_fractionRingPowerSeries`
in `ModularCurve/X0.lean`.) The declaration-order leaf class
([[flt-leaf-blocked-by-declaration-order]], [[flt-declaration-order-leaves]]) is usually
stated about a THEOREM sitting below its consumer. The variant that is harder to see: the
**noun** the docstring's route mentions is below you, so the route cannot be *written down*
at all. Here `IsWeierstrassModel` — the file's only vocabulary for "`W` is the Weierstrass
model of this elliptic scheme" — was declared 2000 lines under the leaf whose route reads
"the datum's `j`-invariant would be a rational constant".

**Why:** every attempt to cut such a leaf along its own route ends in inlining a copy of the
missing definition into the residues, which is a duplicate cut in all but name and invisible
to `dupstmt.py` (it is a definition, not a statement).

**How to apply:** before any mathematics, list the OBJECTS the docstring's argument mentions
— `j`-invariant, Weierstrass model, coarse ring, the file's own `IsJElt`-style predicates —
and `grep -n` each one's declaration line against your own. Then hoist the DEFINITION, which
is small, never the theory it belongs to: three defs and 51 lines moved here, while the
`IsJElt` layer beside them (thousands of lines) stayed put. Prefer moving UP when the leaf's
consumer chain is long — this one was ~500 lines and would have had to travel with it. Take
the pure-move receipt from [[flt-pure-move-receipt]], and expect the "no scope boundary in
the jumped range" check to fire falsely on this tree, where docstring prose begins lines with
the word `section`.
