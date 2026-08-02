---
name: flt-field-base-lemma-spends-it-at-one-point
description: A lemma stated over a FIELD base usually consumes that hypothesis at exactly one named line; find it to locate which fibre of a DVR-base leaf is the real content.
metadata: 
  node_type: memory
  type: project
  originSessionId: d767c51e-cd73-49b7-945b-75c98ba16717
  modified: 2026-08-02T14:06:04.391Z
---

When a leaf over `Spec ℤ_(ℓ)` carries a docstring saying "the `ℚ`-side toolkit does not
apply", that is true and it is not the end of the analysis. **Open the `ℚ`-side lemma and
find the single line where its proof consumes "the base is a field."**

Measured 2026-08-02 (`flt-lean-324`, `geometricallyConnected_of_isX0NormalProperModel`):
`AlgebraicGeometry.denseRange_of_isPullback` — and hence
`geometricallyConnected_of_isSmoothCompactification`, three lines over it — spends it
ONLY at `haveI : UniversallyOpen y := universallyOpen_of_specField y`. Everything else is
base-agnostic. So all that is needed is *the projection of the base-changed curve is an
open map*, and that sorts the fibres: the generic point of `Spec ℤ_(ℓ)` is an OPEN
IMMERSION so the argument transfers verbatim, the special point is a CLOSED immersion so
it fails — and the failure is the citation (Igusa) itself.

**Why:** it converts "this is a citation over a DVR" into "half of it is free bookkeeping
and the other half is the theorem", which is a cut a successor can act on. The
companion glue is mechanical: `geometrically P` over a two-point base splits via a
ring-level dichotomy (`IsReductionBase`'s two axioms alone suffice) plus
`pullbackLeftPullbackSndIso` + `GeometricallyConnected.connectedSpace_of_subsingleton`.

**How to apply:** grep the field-base lemma's proof body for `field`, `IsAlgClosed`,
`specField`, `Subsingleton`; there is normally one hit. Then check, per fibre, whether the
property it supplies survives. See also
[[flt-declaration-order-leaves]] — a scratch module that imports the giant file CANNOT see
that a lemma you want is declared *below* your target, so `grep -n` the line numbers
before planning a proof.
