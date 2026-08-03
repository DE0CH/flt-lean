## CUT AN `∃`-LEAF SO EACH HALF IS A *CONSEQUENCE* OF IT — then faithfulness needs no judgement
(2026-07-31, `exists_splitHilbertBlumenthalCocycle_of_standardLevelModule`.) The usual way to
decompose a big `∃ X, P₁ ∧ … ∧ Pₙ` is to name a new interface — "produce `X` with these
properties, then derive the rest" — and every such cut must be JUDGED strong enough for the second
half. When the judgement is wrong the second half is FALSE, and the sections above record what that
costs. The CUT-OBSTRUCTION AUDITs in this development exist precisely to make that judgement, and
they are expensive.
There is a cut that needs no judgement. Split so that **each half is implied by the leaf itself**
and their conjunction implies it back. Then neither half can be false unless the leaf was, the cut
is *equivalent* to the leaf rather than merely sufficient for it, and the whole faithfulness
argument is two lines checkable by eye.
The shape that produces it: the leaf proves something about a **prescribed parameter** — here a
level module `(ρ₀, Λ)` handed in from outside. Cut as
* **(i)** the same conclusion with the parameter EXISTENTIALLY quantified ("it holds for some
  `ρ₁`"), which follows from the leaf at `ρ₁ := ρ₀`;
* **(ii)** the TRANSFER ("if it holds for `ρ₁`, it holds for `ρ₀`"), which follows from the leaf
  by discarding every hypothesis but the ones the leaf already had.
(i) is the construction freed from having to hit a target it did not choose; (ii) is the twisting.
Assembly is `obtain` from (i), apply (ii). That is exactly the informal proof — "build it for the
canonical object, then twist" — turned into a mechanical decomposition instead of a design.
Two riders, both learned on the same leaf.
**Do not fix the convenient parameter to a NAMED one** unless you can also prove the comparison
between its auxiliary data and the given one. Fixing `ρ₁ := stdRep` from
`exists_standardLevelModule` would have left somebody owing a comparison of two nondegenerate
alternating `μ_ℓ`-valued forms on `k²` — biadditive `k × k → μ_ℓ` is an `r²`-dimensional family
against the `r`-dimensional family of the `φ ∘ det₂`, so it is not free. Quantifying the parameter
away costs nothing and deletes the obligation.
**Whatever in the transfer is not the hard subject, PROVE IT AND HAND IT IN.** The entire group
theory of `σ ↦ ρ₀(σ) ρ₁(σ)⁻¹` — nonabelian 1-cocycle identity, invertibility of the values, the
defining relation, EXACT preservation of the pairing (the `galRoot` twists on the two sides cancel;
no determinant argument needed), and triviality on the open normal `ker ρ₀ ⊓ ker ρ₁ ⊓ …` — went
through on the FIRST compile, in a scratch module, in 42 s. Half (ii) now receives it as a
hypothesis instead of owing it. That is also what keeps the proven work out of the free-floating
set: the sorried half's STATEMENT consumes it.
