## "THIS IS WHERE THE SITE ENTERS" IS USUALLY A PRESERVATION PROPERTY OF THE FUNCTOR — and stating it that way deletes the site
(2026-08-01, `flt-lean-150`, closing `isIso_presheafModPullback_delta_freeYoneda` in
`ModularCurve/RelativePicard.lean`.)  That leaf carried a careful, correct, three-times-amended
docstring saying **"THIS IS EXACTLY WHERE THE SITE ENTERS, AND IT IS THE ONLY PLACE IT DOES"**,
with a real counterexample showing the statement is FALSE one generality up (a functor
collapsing two objects of a discrete category makes `δ` compare `k²` with `k⁴`), and a route
built on "`Opens` is a POSET, so both `Hom`-types are subsingletons and both sides are `S(V)`
or `0`".  Every clause was true.  It is still not a fact about the site.
The hypothesis that makes the leaf true is that **`F` CARRIES A BINARY PRODUCT TO A BINARY
PRODUCT** — and the counterexample is exactly a functor that does not.  Stated that way
(`isIso_pullback_delta_freeYoneda_of_prod`, in
`Fermat/FLT/Mathlib/Algebra/Category/ModuleCat/Presheaf/PullbackMonoidal.lean`) the whole
development is site-free, the poset is used ONLY to produce the two bijections
`(X ⟶ V) ≃ (X ⟶ U) × (X ⟶ U')`, and the site-specific part of the final proof is **two lines**
(`bijective_hom_of_thin`, where injectivity is free from thinness and nothing has to be
checked).  Net: `−1` leaf and a mathlib-facing theorem that any future consumer over any site
can use.
**The check, and it is one question: a route written "this is true because the site is a
poset" has confused a WITNESS for the hypothesis with the hypothesis.**  Ask what property of
`F`/`C` the counterexample actually violates, and state THAT.  Posets, discrete categories and
`Opens` are where such witnesses are cheapest, so they are what a route reaches for — and a
leaf phrased over them cannot be reused, cannot be given to a mathlib-facing prover, and hides
which of its steps are formal.
Three things that made the proof cheap, each of which the route had priced higher:
* **`ModuleCat.free : Type u ⥤ ModuleCat R` IS ALREADY A MONOIDAL FUNCTOR IN THE PIN**
  (`ModuleCat.FreeMonoidal.μIso`, `μIso_hom_freeMk_tmul_freeMk`, `free_μ_freeMk_tmul_freeMk`).
  So `free (yoneda U) ⊗ free (yoneda U') ≅ free (yoneda V)` is `μIso` composed with `free` of
  the product bijection — no `Finsupp` case split, no `finsuppTensorFinsupp'`, and it holds for
  ANY binary product rather than only in a poset.  **Before doing combinatorics with `Finsupp`,
  check whether the free functor's monoidal structure is registered.**
* **A map with no formula becomes computable after TRANSPOSING it.**  `δ` of a left adjoint's
  oplax structure is `(adj.homEquiv).symm ((unit ⊗ₘ unit) ≫ μ G)`; `pullback` is an abstract
  partial left adjoint and `δ` cannot be evaluated on elements, but `adj.homEquiv δ` can.
  `isIso_of_coyoneda_map_bijective` + `Adjunction.homEquiv_naturality_right` turns
  `IsIso δ` into bijectivity of `g ↦ (adj.homEquiv δ) ≫ G.map g`, and then
  `PresheafOfModules.freeYonedaEquiv` identifies BOTH hom-sets with one section group.  What is
  left is a single element identity that does not mention the test object at all — and here it
  held by `rfl`.
* **`μ` of a pushforward of presheaves of modules is the identity on elements.**  Mathlib gives
  `pushforward₀OfCommRingCat` the tensorator `Iso.refl _` (`PushforwardZeroMonoidal`), so the
  whole of `μ (pushforward φ)` is `ModuleCat.restrictScalars`'s base-change comparison
  `m₁ ⊗ₜ m₂ ↦ m₁ ⊗ₜ m₂` (`ModuleCat.restrictScalars_μ_tmul`).
**And the Lean trap that cost four of the eight rounds: `rw`/`erw` on a `rfl`-lemma about
`⊗ₘ` picks the wrong redex.**  `PresheafOfModules.Monoidal.tensorHom_app` and
`ModuleCat.MonoidalCategory.tensorHom_tmul` are both proved `rfl` and both are stated with
`dsimp%`, so `rw` reports "did not find an occurrence" on a goal that displays the pattern, and
`erw` happily matches something else — here it unfolded `μ (pushforward φ)` into
`extendRestrictScalars` machinery and produced a half-page goal.  **Write the step as
`rw [show <the exact LHS> = <the exact RHS> from rfl]`**: the `rfl` proof forces the redex you
wrote, and nothing else can fire.  Same cure as the standing "printed pattern equals printed
target ⟹ use a defeq-checking tactic", with the extra twist that here you must ALSO pin which
subterm is being rewritten.
