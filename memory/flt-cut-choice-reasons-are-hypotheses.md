---
name: flt-cut-choice-reasons-are-hypotheses
description: "A leaf's stated reason for taking the LOOSER cut ('that obligation is not cheap in the assembly') is a hypothesis; check whether the obligation is really about the opaque object"
metadata:
  type: project
---

`exists_weierstrassRingEquiv_of_abelianSchemeChart` (X1.lean, cut 2026-07-31) was
deliberately stated as a `RingEquiv` rather than in the tighter GENERATORS form. Its
docstring gave the reason explicitly: the generators form "would force the `IsDomain R`
/ `¬ IsField R` obligations into the ASSEMBLY, where `R` is opaque and they are not
cheap."

`R` really is opaque in the assembly. The inference was still wrong, because **neither
obligation is about `R`** — both are about the SCHEME `A` of which `Spec R` is an open
subscheme, and both were already proven in this tree:

* `IsDomain R` ← `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`) + mathlib's
  `isIntegral_of_isOpenImmersion` + `Scheme.ΓSpecIso`;
* `¬ IsField R` ← `infinite_of_smoothOfRelativeDimension_one` (same file): `A` is
  INFINITE, `_hrange` removes one point, a field has a one-point spectrum. The same
  count also supplies the `Nonempty (Spec R)` that integrality-transport needs, so it
  is not an extra hypothesis either.

Total: about fifteen lines, and the leaf shrank to pure Riemann–Roch.

**Why: the reason a leaf gives for its own shape is written by whoever cut it, at the
moment of cutting, and is exactly as unverified as a cost estimate.** The failure mode
here is specific and worth naming — *conflating "the object is opaque" with "the fact is
unavailable"*. An obligation phrased about an opaque `R` may be entailed by a fact about
a NON-opaque neighbour that the hypotheses tie `R` to. `_hopen`/`_hrange` are exactly
such ties, and they were already in the signature.

**How to apply:** when a leaf's docstring justifies the looser cut by an obligation it
did not want to carry, ask *which object is that obligation really about* before
accepting the shape. If the hypotheses identify the opaque object with a piece of
something already developed, grep that development first. Restating a leaf tighter is a
fully successful outcome even when the leaf's own mathematics is untouched — it is what
the next prover no longer has to know.

See [[flt-leaf-cost-estimates-are-hypotheses]] (the same "written before anyone tried"
shape, applied to a docstring's missing-lemma list),
[[flt-inventory-audits-understate-what-exists]] and
[[flt-missing-machinery-may-be-downstream]].
