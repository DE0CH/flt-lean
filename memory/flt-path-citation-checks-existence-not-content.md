---
name: flt-path-citation-checks-existence-not-content
description: "A docstring citing a project module BY PATH has verified the module exists, not what is PROVEN in it — grep its theorem list before pricing anything it is cited for"
metadata: 
  node_type: memory
  type: project
  originSessionId: 5bd81d5b-fa73-4036-9474-e368db96dccd
  modified: 2026-08-02T19:18:24.826Z
---

2026-08-02, `flt-lean-224`, closing
`exists_nonconstant_toAbelianScheme_of_one_le_isCurveGenus` in `X0.lean`.

That leaf called its missing `K`-rational point *"the only delicate part of the
statement"* and, listing the Weil-restriction repair, wrote the parenthetical
*"(which this tree carries,
`Fermat/FLT/Mathlib/AlgebraicGeometry/WeilRestriction.lean`)"*. That module does
not "carry Weil restriction" — it carries the **finished theorem, PROVEN**, in
the applied form the leaf needs, and its own docstring names this leaf's sibling
as the consumer it was written for. The whole delicate part was one `import`
away for two days.

**Why this is not the ordinary absence-claim failure.** *"X is not in the pin"*
announces itself as a claim to re-check. A citation **by path** announces the
opposite: it reads as a check that was run, and the path is evidence the author
opened a file. What was verified is that the module EXISTS. Nothing in the
sentence is false; the inference is.

**How to act on it:** whenever a docstring names a project module by path,
`grep -n '^theorem' ` that module before pricing anything it is cited for. These
modules are small (300 lines, three declarations here) and the question it
answers — *which of these are PROVEN, and is one of them my statement?* — is not
the question the citation answered.

**The search that finds such a module is a grep for the CONCLUSION'S SHAPE over
the whole tree**, never for the leaf's own vocabulary: `Fermat/FLT/Mathlib/**` is
where earlier agents' general-purpose work lands, filed under the name of the
TECHNIQUE, so it matches neither the leaf's name nor its mathematics. Compute the
import closure before assuming the import is expensive — this one's whole
`Fermat`-closure was already inside `X0`'s, so it cost one module and could not
cycle.

**Why it is worth being alert to: BOTH halves of that leaf were already written.**
The nonconstancy half was a PROVEN assembly in the downstream sibling `X1.lean`,
uncitable but transcribable, because all eight of its inputs sat above the leaf's
own line — see [[flt-declaration-order-leaves]] for that arithmetic. Net: a
1 → 1 recut whose residue lost the base point, the Picard scheme, Abel–Jacobi and
the abelian variety.

Sibling case where the docstring named the right module and the answer was a
COMPOSITION of two declarations rather than one theorem:
[[flt-leaf-names-the-module-holding-its-answer]]. Related:
[[flt-inventory-audits-understate-what-exists]], [[audit-lacks-x-is-about-x]],
[[flt-leaf-cost-estimates-are-hypotheses]].
