---
name: flt-site-entry-is-a-preservation-property
description: "A leaf whose docstring says \"this is where the site enters\" is usually a PRESERVATION property of the functor — restating it that way deletes the site and makes the leaf mathlib-facing"
metadata: 
  node_type: memory
  type: project
  originSessionId: e2ca5e28-541b-49fb-b30b-ce28aa6348bd
  modified: 2026-08-01T20:16:04.311Z
---

(2026-08-01, `flt-lean-150`, `isIso_presheafModPullback_delta_freeYoneda` in
`ModularCurve/RelativePicard.lean`.) That leaf's docstring said, in capitals and after three
amendments, **"THIS IS EXACTLY WHERE THE SITE ENTERS, AND IT IS THE ONLY PLACE IT DOES"**, with a
correct counterexample one generality up and a route resting on "`Opens` is a POSET, so both
`Hom`-types are subsingletons".

**Why:** every clause was true and the conclusion was not. The hypothesis that makes it true is
that **`F` carries a binary product to a binary product** — and the counterexample is precisely a
functor that does not. Restated that way
(`PresheafOfModules.isIso_pullback_delta_freeYoneda_of_prod` in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean`) the development is
site-free; the poset is used only to produce two bijections
`(X ⟶ V) ≃ (X ⟶ U) × (X ⟶ U')`, and the site-specific residue is two lines
(`bijective_hom_of_thin`).

**How to apply:** when a route says "this is true because the site is a poset / discrete / has
meets", ask what property of `F` or `C` the counterexample actually violates, and state THAT.
Posets and `Opens` are where such witnesses are cheapest, so they are what a route reaches for — a
leaf phrased over them cannot be reused, cannot be handed to a mathlib-facing prover, and hides
which of its steps are formal. Same family as
[[flt-coordinate-clause-is-not-about-the-object]] and
[[flt-obstruction-names-wrong-thing]].

Three riders measured on the same leaf:

* **`ModuleCat.free : Type u ⥤ ModuleCat R` is ALREADY monoidal in the pin**
  (`ModuleCat.FreeMonoidal.μIso`, `μIso_hom_freeMk_tmul_freeMk`). So
  `free (yoneda U) ⊗ free (yoneda U') ≅ free (yoneda V)` needs no `Finsupp` case split and no
  `finsuppTensorFinsupp'`, and holds for ANY binary product. Check for a registered monoidal
  structure before doing `Finsupp` combinatorics.
* **A map with no formula becomes computable after TRANSPOSING it.** `δ` of a left adjoint's
  oplax structure is `(adj.homEquiv).symm ((unit ⊗ₘ unit) ≫ μ G)`; `PresheafOfModules.pullback`
  is an abstract partial left adjoint whose `δ` cannot be evaluated on elements, but
  `adj.homEquiv δ` can. `isIso_of_coyoneda_map_bijective` plus
  `Adjunction.homEquiv_naturality_right` then reduces `IsIso δ` to ONE element identity that does
  not mention the test object.
* **`μ (pushforward φ)` is the identity on elements** — mathlib gives `pushforward₀OfCommRingCat`
  the tensorator `Iso.refl _` (`PushforwardZeroMonoidal`), so it is all
  `ModuleCat.restrictScalars_μ_tmul`.
