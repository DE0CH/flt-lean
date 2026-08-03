## `_o` IS NOT WHAT A ZARISKI-DESCENT LEAF RUNS ON — THERE IS NO CANONICAL MAP IN THE RIGIDIFIED DIRECTION
(Same task, and it corrects a route note two docstrings had carried in this file.) The standard
sketch for "`T ↦ Pic(X_T)/Pic(T)` is a Zariski sheaf" rigidifies along the section: put
`N := σ^*M` and show `M ≅ π^*σ^*M`. That is the right MATHEMATICS and the wrong shape for Lean,
for a reason that is visible before any proof is attempted: **`π^*σ^*M` is `(π ≫ σ)^*M`, and a
map from it to `M` would need a natural transformation `π ≫ σ ⟶ 𝟙`, which does not exist for
schemes.** So the rigidified route has no global morphism to test, and every step of it is a
gluing argument about local isomorphisms.
The counit `ε : π^*π_*M ⟶ M` of `Scheme.Modules.pullbackPushforwardAdjunction` is the ONLY
canonical global morphism in the situation, and once it is written down both remaining
obligations become local on the base and `isIso_of_locally_isIso` finishes them. So the leaf
consumes `_hpush` (`π_*𝒪 = 𝒪`, universally) and **not** the section — which also retires the
older claim, recorded twice in that file, that the glueing half needs `_o` "to kill a class in
`Br T`". With `N := π_*M` the local twists are not merely isomorphic on overlaps, they are the
restrictions of one sheaf, so no cocycle and no Brauer class arises.
**The generalisable question, asked before choosing a route: which of the candidate
constructions is the target of a CANONICAL MORPHISM?** In a category of sheaves the answer is
almost always the one produced by an adjunction unit or counit, and a construction that is only
"the obvious object" — a pullback along a section, a hand-glued limit — is a construction you
will have to build every comparison map for by hand.
And what the counit route then needs, which is what a successor should be dispatched at rather
than at the whole leaf: base change of `π_*` along an open immersion of the TARGET, the
Beck–Chevalley compatibility of the counit with it, and `π_*𝒪_Z ≅ 𝒪_T` as `𝒪_T`-MODULES out of
`HasTrivialPushforward` (which is a statement about the map of sheaves of RINGS and does not
hand you the module-level one). None of the three is at this pin; all three are stated in the
docstring of `exists_modPullback_of_locally_modPullback`.

