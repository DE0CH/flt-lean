## A "RELATIVE THEORY IS NEEDED" VERDICT DIES IF THE DEFINITION NEVER MENTIONS THE BASE
(2026-07-31, `gp_le_upperRamificationFiltration_sup_lvl` in `ArtinConductor.lean`.) A
FAITHFULNESS AUDIT had decomposed that leaf into four steps and reported step 2 as "NOT
available, and **not even STATABLE**: it needs the ramification data of `L''/L`, while
`LowerRamificationData` is always relative to `Kᵥ` — the structure has no relative `φ`, and
building one is the real cost of this leaf." The task prompt built on that and called the
relative structure "the whole cost of this leaf … a multi-agent node".
It was not needed at all, for a reason visible in the structure's own defining field.
`mem_gp` reads
    σ ∈ gp i ↔ ∀ x, (∀ τ ∈ lvl, τ • x = x) → unif ^ (i+1) ∣ σ • x − x
— an ELEMENTWISE condition on the valuation in which the base field does not occur. So the
relative groups are already present: `G_i(L''/L) = G_i(L''/Kᵥ) ⊓ Gal(L''/L)`, i.e. literally
`D''.gp i ⊓ D.lvl`. What reads as Serre IV §1 Prop. 2 is here a definitional identity.
The second half is a restatement trick worth remembering on its own. Transitivity
`φ_{L''/Kᵥ} = φ_{L/Kᵥ} ∘ φ_{L''/L}` was step 3, and its ONLY job was to convert the index
`ψ_{L''/L}(m)` that Prop. 14 produces into the `ψ_{D''}(φ_D m)` the consumer wants. **State
the leaf with the composed index already in it and the composite is never taken apart**, so
step 3 vanishes and no relative `φ` is ever defined. Stating it between two ARBITRARY levels
rather than for a tower then made the refinement-compatibility lemma a COROLLARY instead of a
second leaf.
Net: one opaque leaf became two named ones (`gp_le_gp_psiNat_phi_sup_lvl`,
`iInf_gp_one_le_wildInertiaGroup`) with steps 1 and 4 — cofinality and a Cantor-intersection
compactness argument over the directed family of refinements — proven outright, in one run.
**The general check, which costs one `grep`:** before accepting "this needs a relative /
generalised structure first", read the DEFINING clause of the structure and ask whether the
thing you are told is missing actually appears in it. An audit's "not even statable" is a claim
about the API someone imagined, not about the definition. Same family as
[[flt-inventory-audits-understate-what-exists]] and
[[audit-searched-production-not-invariant]]: audits are reliable about what they searched for
and unreliable about what they did not think to.
Corollary for the index of a filtration: **an index written as a COMPOSITE is a choice, and
choosing the composed form can delete a whole theory.** The uncomposed form obliges you to
prove the composition law; the composed form never forms the pieces.
