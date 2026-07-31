---
name: flt-leaf-hypotheses-are-a-superset
description: A leaf's hypothesis list is often much wider than its proof needs; prove a helper with only what you use and apply it, leaving the leaf's signature alone
metadata:
  type: project
---

When one theorem is split into halves, this development's convention (stated in
`X0.lean`'s "BLR 7.4/5 SPLIT along the (a)/(b) axis" heading) is that **both halves
carry the IDENTICAL hypothesis list**, deliberately — trimming each half to what its
intended argument uses would be a claim about which hypothesis belongs where, and such
claims have been wrong here before. So the signature you are handed is an upper bound,
not a specification.

On 2026-07-31 both halves of that very split were proven, and both used a strict subset:

- `isProper_geometricallyConnected_of_neronModelSpread` used `abZJ genJ π hsurj nB
  spread hspread hsq` — not `abJ`, `abB`, `hgenJ`, `hπ`, `hadd`.
- `exists_abelianSchemeStruct_of_isProper_of_neronModelSpread` used only `nB abB hproper
  hconn` — none of the spread data at all.

**Why:** an unused hypothesis only weakens a theorem, so the leaf is still true and its
consumers still typecheck; and the assembly above already holds every one of them.

**How to apply:** prove a NAMED HELPER stated with exactly the hypotheses you consume,
then discharge the leaf by applying it. Do not edit the leaf's signature — that is a
change every caller sees, for no mathematical gain. Say in the leaf's docstring which
hypotheses turned out unused: the section heading here explicitly asked for that report
("if a prover needs `hsurj`, the (a)/(b) seam is in the wrong place"), and "needed
strictly less" is the answer that confirms the seam rather than the one that moves it.

Related: [[flt-cut-leftovers-close-sibling-leaves]], [[audit-searched-production-not-invariant]].
