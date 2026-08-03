## A ROUTE NOTE THAT PRICES A STEP AT "COMPLETENESS" OR "A LENGTH COUNT" IS USUALLY PRICING A UNIVERSAL PROPERTY IT DID NOT LOOK FOR
(2026-08-02, `flt-lean-357`, closing `pderiv_mem_sup_span_three_of_minimalPresentation`
— Fontaine's step 3 — in `HardlyRamified/ModThree.lean`.)  That leaf's docstring is a
careful, correct three-screen route, and **two of its four steps are priced at machinery
the proof does not use.**  Both over-pricings have the same shape and both are worth
checking on any leaf whose route mentions completions, lengths, ranks or dimensions.
* *"`Ω = Ω[B⁄𝒪] = B^h/Jac(P)` — an honest identification … `B` is FINITE over `𝒪₃ᵥ`, so
  the finite submodule `𝒪₃ᵥ[x₁,…,x_h]` is complete, hence closed, hence all of `B`."*
  True, and not needed.  The identification is a **UNIVERSAL PROPERTY**: the inverse map
  `Ω[B⁄𝒪] → B^h/Jac` is the `𝒪`-derivation `α f ↦ (α(∂f/∂Xⱼ))ⱼ`, well defined because
  the Jacobian row of an element of `ker α` is a combination of the rows of `P` (Leibniz
  plus `α (P i) = 0`), and `Derivation.liftKaehlerDifferential` does the rest.  No
  completion, no closure, no density.
* *"a length count over the finite-length `B̄` forces `J̄ac = 0`."*  Also true, also not
  needed.  What the argument uses is that the surjection `B̄^h ↠ Ω` **SPLITS** — flat +
  local gives free (`Module.free_of_flat_of_isLocalRing`) gives projective — so its
  kernel is a direct summand of `B̄^h` contained in `𝔪̄·B̄^h`, whence `K̄ = 𝔪̄·K̄` and
  Nakayama kills it.  Ranks, lengths and `κ`-dimensions never appear, and the hypothesis
  `hmin` is consumed once, as `α(∂Pᵢ/∂Xⱼ) ∈ 𝔪_B`.
**The generalisable check: when a route note reaches for a NUMERICAL invariant (length,
rank, dimension) to force a submodule to vanish, ask whether SPLITTING plus Nakayama does
it instead.**  It does whenever the quotient is projective, which over a local ring is
whenever it is flat and finitely generated — and "flat" is what such hypotheses usually
say.  Same for a completeness argument establishing that a presentation is surjective:
ask whether the map you want is the one an adjunction already gives you.
**And the third over-pricing, which is the one that decides whether the leaf is tractable
at all: A CHAIN RULE FOR POWER SERIES NEEDS NO CONVERGENCE.**  `α : 𝒪[[X]] →ₐ[𝒪] B` is an
arbitrary algebra map — no continuity is assumed or available — and yet
`d(α f) = ∑ⱼ α(∂f/∂Xⱼ)·d(α Xⱼ)` holds for every power series `f`.  What replaces
convergence is that some ideal `I` with `α (Xⱼ) ∈ I` annihilates the target: split
`f = truncTotal (n+1) f + tail`, the polynomial part is the ordinary chain rule by
`MvPolynomial.induction_on`, and both the tail and the tails of its derivatives land in
`Iⁿ` which kills `Ω` (`MvPowerSeries.mem_varsIdeal_pow`,
`map_mem_pow_of_mem_varsIdeal_pow` in `…/MvPowerSeries/VarsIdeal.lean` are exactly the
two estimates).  For a SURJECTIVE `α` onto a local ring the ideal is free: `𝔫` is the
Jacobson radical of `𝒪[[X]]`, so `1 - f·Xᵢ` is a unit, so `α (Xᵢ)` is a non-unit
(`MvPowerSeries.algHom_X_mem_maximalIdeal`).  **A leaf that says "`α` is an arbitrary
algebra map out of a power series ring, so nothing converges" is telling you to find the
ideal, not to add a hypothesis.**
Two riders on how the work was landed, both worth copying:
* **The leaf's statement mentioned `𝒪₃ᵥ` and `IsFontaineAlgebra`; its CONTENT mentions
  neither.**  The whole argument is now
  `MvPowerSeries.alpha_pderiv_mem_span_of_flat` in
  `Fermat/FLT/Mathlib/RingTheory/MvPowerSeries/Jacobian.lean`, over an arbitrary local
  `B`, an arbitrary surjective `α` and an arbitrary `p ∈ 𝔪_B`.  Iteration cost went from
  ~40 min (one `lake build` of the 78 000-line `ModThree.lean`) to **5 s**.  Read the
  leaf's PROOF SKETCH, not its statement, when deciding where the work belongs.
* **The residue is one sentence of the leaf's own audit.**  Everything the general theorem
  needs at `p = 3` — `3 ∈ 𝔪_B`, `hΩ` for the quotient, `𝔪_B ^ n ⊆ (3)`, the minimality
  clause — is proven in the glue; what is left is item 1 of the audit, *"`J = (ε)` with
  `ε` idempotent, so both `hΩ` and the flatness half of `hfon` pass to the factor `B`"*,
  and only its FLATNESS half.  Leaf count `1 → 1`; say so, because a `−1 +1` warning-set
  delta is indistinguishable from nothing having happened.
**The trick that makes that residue small, and it is reusable wherever an idempotent
quotient appears:** for `J = (ε)` with `ε` idempotent, the conormal map
`J/J² → (A/J) ⊗_A Ω[A⁄𝒪]` is ZERO, because `dε = d(ε²) = 2ε·dε` gives `(1−2ε)·dε = 0`
while `(1−2ε)² = 1` makes `1−2ε` a unit.  So
`Ω[(A/J)⁄𝒪] ≅ (A/J) ⊗_A Ω[A⁄𝒪]` on the nose, by
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` alone — no localisation
theory, no `IsLocalization`, no product decomposition of `A`.
