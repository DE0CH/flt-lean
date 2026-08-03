## BUILD AN ISO FROM TWO ONE-WAY MAPS AND A MONO — never from a bijection of pieces
Same leaf, and it is worth separating because the leaf's route note prescribed the
expensive version.  The sketch said `u` is "the induced bijection of components",
which needs the two point sets matched up AND the matching proved bijective.  What
actually works: prove the one-directional lemma (*there is a map over `A`*) and run
it BOTH ways, getting `u ≫ j₂ = j₁` and `v ≫ j₁ = j₂`.  Then
`(u ≫ v) ≫ j₁ = u ≫ j₂ = j₁ = 𝟙 ≫ j₁`, and `j₁` is a mono, so `u ≫ v = 𝟙` by
`cancel_mono`; symmetrically for `v ≫ u`.  `IsIso u` is never constructed by hand and
no injectivity or surjectivity statement about points appears anywhere.
Two things follow that are worth copying.  The mono hypothesis (here
`IsClosedImmersion`) is consumed ONLY in that last step, so the one-directional lemma
should not assume it — which is what lets the same lemma serve both directions.  And
whenever a leaf's conclusion is `∃ u, IsIso u ∧ <compatibility>`, ask first whether the
compatibility plus a mono already forces the `IsIso`; in a category of schemes it
usually does, and it is strictly cheaper than any argument about the underlying sets.
