---
name: flt-specialised-copy-means-generic-is-cheap
description: "A theorem the tree \"does not have\" often exists twice, specialised; grep for the mathlib proof technique, not the conclusion."
metadata: 
  node_type: memory
  type: project
  originSessionId: e310c690-bb00-4a16-aa88-80215cc05eda
  modified: 2026-08-02T20:28:33.689Z
---

(2026-08-02, `flt-lean-47`, closing `smoothOfRelativeDimension_sexticThirtySeven`.)
A leaf needed the Jacobian criterion for a plane hypersurface. Grepping the
CONCLUSION over `Fermat/` finds nothing, and "not in the tree" is the honest
report. It was wrong: the criterion existed **twice**, both specialised to a
Weierstrass chart (`isStandardSmoothOfRelativeDimension_projChartAway`, in
`ModularCurve/EllipticScheme.lean` and `Modularity/MoretBailly.lean`), stated about
`projChartPolynomial E i` / `ProjChartVar i` — so no grep in the consumer's
vocabulary hits them, and the `EllipticScheme` copy is unreachable anyway because
`X0.lean` imports it NON-publicly.

Neither proof used a single fact about a Weierstrass equation. Deleting the
elliptic-curve vocabulary was a mechanical port that compiled **first try in 16 s**
as `Fermat/FLT/Mathlib/RingTheory/Smooth/Hypersurface.lean` (mathlib-only imports,
so it cannot cycle and it iterates in seconds).

**Why:** a specialisation is written by whoever needed it, in their vocabulary, and
its docstring often even says "this is a piece of MATHLIB rather than of this
development" — while still being stated about their object. So the generic
statement is a rename away, and only a *technique*-level grep sees it.

**How to apply:** when a leaf needs a criterion the tree "does not have", grep for
the mathlib PROOF TECHNIQUE it would be built from (`PreSubmersivePresentation`,
`jacobiMatrix`, `SubmersivePresentation.ofAlgEquiv`, `ValuativeCriterion`,
`Presentation.naive`) rather than for the statement. A hit means the hard part is
already paid for. Then state the generic version in `Fermat/FLT/Mathlib/**` and
specialise at the call site.

Mirror of [[flt-inventory-audits-understate-what-exists]] (theorem present under
another NAME) — here it is present under another INSTANTIATION. See also
[[flt-nonpublic-import-duplicate-cut]] for why one copy was invisible.
