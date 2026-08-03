## AN INTERFACE WHOSE AXIOMS ARE ALL CATEGORICAL IDENTITIES IS INHABITED BY THE IDENTITY — AND ITS `∀ datum` CONSUMER IS THEN FALSE
(2026-08-02, `flt-lean-32`, `exists_splitModuliLevelAction` in `Modularity/MoretBailly.lean`.
The check is nine seconds and it should be the FIRST thing done at any leaf whose conclusion
is `Nonempty <structure>` or `∃ <structure>`.)
`SplitModuliLevelAction` bundles an action of `SL₂(k) × SL₂(kp)` on `X₀ ⊗ K` with five
axioms: `act_snd` (valued over the base), `act_one`, `act_mul`, and `act_baseAct` (the
`ρ₀`-conjugation semilinearity). Every one of them is an EQUATION BETWEEN MORPHISMS, and
**every one is satisfied by `act _ _ := 𝟙 _`** — `act_one` is `rfl`, the rest are
`Category.id_comp` / `Category.comp_id`. So the leaf's conclusion held with none of `D`,
`hlam`, `hfrp`, `hne`, `hpℓ`, `Λ`, `Λp`, `hmod` used at all.
**The test, and it takes one scratch round:** write the structure instance with every
morphism field the identity (or the zero map, or the constant function) and see whether it
elaborates. If it does, the interface has no clause pinning the object to what it MEANS,
and the leaf is vacuous. This is the same defect `Fermat.PolarizationStruct` in the same
file already records and repairs on its nondegeneracy field — *"without which the constant
ZERO MAP satisfies every other field over every datum"* — so the file had the precedent and
nobody had re-run it on the newer structure.
**THE DAMAGE IS NOT THE VACUOUS LEAF. IT IS THE `∀ <structure>` CONSUMER, WHICH IS FALSE.**
`exists_twistedFamily_of_isGaloisTwistForm` (Taylor's Lemma 4.4) quantified over an
ARBITRARY `act`, so it could be instantiated at the degenerate one; the degenerate action's
twisting cocycle is `fun _ => 𝟙 _` **by `rfl`**, so `isGaloisTwistForm_one` discharges its
`htw` at `X := X₀`, and its four shape hypotheses come out of `hmod`. What survives is the
assertion that `X₀` carries `ρbar`-equivariant level structures — the exact sentence that
theorem's own docstring, and its parent's, call FALSE for `ρbar ≇ ρ₀`.
**Both docstrings had audited the `∀`-over-TWISTS shape, at length, and neither had audited
the `∀`-over-ACTIONS shape.** That is the generalisable warning: when a leaf quantifies over
a piece of DATA supplied by a sibling leaf, the sibling's inhabitedness is a hypothesis about
the *whole* class of inhabitants, and a non-vacuity paragraph about some *other* quantifier
says nothing about it. Grep a `∀`-shaped leaf's binder list for structures produced elsewhere
and instantiate each at its degenerate witness.
### THE REPAIR THAT DOES NOT REQUIRE INVENTING AN INTERFACE
The mathematically primitive pin is "the action precomposes the universal level structures",
which needs the universal family, a comparison of two geometric fibres, and the level-structure
clauses transported across it — a large new interface, carrying the two-sided risk this file
already records (too weak ⇒ the `∀` consumer stays FALSE, silently; too strong ⇒ the `∃`
producer is unprovable). **Do not invent it. Make the producer produce the action TOGETHER
WITH the consumer's own conclusion, universally quantified over the consumer's data.**
    def IsTwistingModuliAction … (act : SplitModuliLevelAction …) : Prop :=
      ∀ <exactly the consumer's remaining binders>, <exactly the consumer's conclusion>
    -- leaf:     ∃ act, IsTwistingModuliAction … act        (was: Nonempty (…))
    -- consumer: … (hact : IsTwistingModuliAction … act) … := hact ρbar θ ρbarp … -- PROVEN
It cannot be too weak — it IS what the consumer consumes — and it cannot be too strong — it is
a statement the consumer's own author vouched for. Here it took **two leaves to one** (20 → 19
in that module, one closed, none opened), the consumer became a one-line application, and
`SplitModuliLevelAction` itself was left untouched, so `twistCocycle`,
`isQGaloisCocycle_twistCocycle` and `isOpen_kernel_twistCocycle` could not break.
Three riders:
* **The direction check is what licenses it.** Adding a conjunct to the conclusion
  STRENGTHENS the `∃` leaf and WEAKENS every `∀ act` consumer — which is what both need. Run
  it before any such repair; get it backwards and you have hidden the falsity instead of
  removing it.
* **Keep the degenerate witness as a PROVEN declaration, not as prose.** `trivialSplitModuli-
  LevelAction` and its `rfl` cocycle lemma are consumerless, exactly like the file's existing
  `isQGaloisCocycle_one` / `isGaloisTwistForm_one` non-vacuity lemmas — that is the precedent,
  and it is what stops the next reader re-deriving the refutation from a paragraph.
* **The old faithfulness audit is VOID and must be re-run against the composite**, per the
  standing rule; and say in the commit that the count moved by −1 with no mathematics done,
  because a leaf-count delta from a *faithfulness repair* is indistinguishable from a proof.
