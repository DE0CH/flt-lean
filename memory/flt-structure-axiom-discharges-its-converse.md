---
name: flt-structure-axiom-discharges-its-converse
description: When a leaf's route demands something "on the nose", check whether a field of the structure already asserts it — you may owe only the up-to-a-factor existence statement
metadata:
  type: project
---

`GeomPic.below_surjective` (`ModularCurve/HyperellipticJacobian.lean`) was priced by
its own docstring as the valuation-extension theorem for a CONSTANT field extension —
produce a valuation on `F̄` restricting to `ord_v` **on the nose**, i.e. ramification
index `1`, which is Stichtenoth III.6.3(b) and is what the still-open sibling
`constFieldExt_exists_uniformizer` asks for. It was not needed: `ord_emb` is a FIELD
of `GeomPic`, asserting exactly that unramifiedness for every place. So producing any
place whose restriction is a positive MULTIPLE `e · ord_v` sufficed — the axiom reads
it back as `ord_{below w}`, and `ord_surjective` forces `e = 1`. The residue was
ordinary lying over in the two Dedekind towers the file already had, ~490 lines.

**Why:** a leaf's route is written by whoever CUT it, from the argument that builds
the object *from scratch*, before the structure's axioms were what they are now. It
is a hypothesis about cost, and the axioms are where the cost can already have been
paid — see [[flt-leaf-cost-estimates-are-hypotheses]] and
[[audit-searched-production-not-invariant]] for the same failure on other axes.

**How to apply:** when a route asks for an equality, a normalisation, an index equal
to `1`, or a canonical choice, list the structure's fields and ask which already
assert that of every inhabitant. If one does, you owe only the statement **up to the
ambiguity that axiom removes**, usually a much cheaper existence statement. Then say
explicitly which sibling leaf this does NOT close — here the producer
(`ConstFieldExt`, which carries no `ord_emb`) still owes the hard version, and a
reader who deletes it has broken the thing that discharges the axiom.

Corollary found the same day: grep the file for the leaf's CONCLUSION, spelled out,
not for its name. `Function.Surjective gp.below` found a second, independent cut of
the identical theorem (`geomPic_below_surjective`) that shared no identifier with the
first, so every sorry-scan counted one theorem twice. See
[[flt-two-leaves-may-be-one]].
