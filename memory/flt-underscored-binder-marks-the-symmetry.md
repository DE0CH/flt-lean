---
name: flt-underscored-binder-marks-the-symmetry
description: "A hypothesis the conclusion never reads (this tree underscores them) tells you which symmetry the leaf's `∃!` is blind to — and that is usually where its documented route dies."
metadata: 
  node_type: memory
  type: project
  originSessionId: e8b5cd16-0972-48cb-9dfb-381e18a00360
  modified: 2026-08-02T09:04:31.166Z
---

For a leaf shaped `∃ M, ∀ …, ∃! m, Φ(m)`, list the hypotheses `Φ` does NOT
mention. This development marks exactly those with a leading underscore, so
the check is a read of the binder list, not of any proof.

Each unread hypothesis is a symmetry `Φ` cannot see, so the `∃!` pins `m`
only up to that symmetry — i.e. the represented functor is a QUOTIENT, while
the object a docstring names is normally the rigidified one. Blind to a
chosen base change ⟹ blind to `Aut`; blind to a chosen basis ⟹ blind to
`GL`; blind to a chosen uniformizer ⟹ blind to units.

Measured on `exists_isAffineHom_fullLevelModuli` (`ModularCurve/X1.lean`,
2026-08-02): `_bcd` was unread, the docstring's object (the clopen
independence locus) represents the rigidified functor, and at `N = 1, n = 3`
negation gives two distinct classifying maps. The STATEMENT survived — `M₀/Aut`
works — so the result was "route refuted, statement not", which is a different
report from "leaf false" and sends a prover somewhere different.

**Why:** the audits in this tree check the geometry of the named object and
not what the conclusion can observe about it, so this failure survives review.

**How to apply:** run the unread-binder check before costing any
`∃ object, universal property` leaf. When the symmetry is `Aut`, grep the file
for `rigid` — in a tower, non-rigidity is already recorded against whichever
step was cut first and is never propagated up ([[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audit-scoped-to-declaration-it-read]]). The repair is normally the
hypothesis killing the symmetry, which the sole call site already holds
([[flt-leaf-hypotheses-are-a-superset]]); then split the citation off from the
formalisation by adding the clause that READS the unread binder.
