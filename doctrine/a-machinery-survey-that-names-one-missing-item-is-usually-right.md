## A MACHINERY SURVEY THAT NAMES *ONE* MISSING ITEM IS USUALLY RIGHT — CUT EXACTLY THAT

Same leaf, and it is the counterweight to the two sections above (a survey that ends in
"hoist X and generalise Y" being an artefact of the route, and four audits auditing a
docstring's anatomy). Those say surveys OVER-state. This one under-stated nothing:

`eq_two_or_eq_three_of_stableCyclic_of_autPoint_not_stable`'s docstring ended
"**GENUINELY MISSING, and the only thing that is**: `K ⊄ ℚ(μ_p)` for `p ≥ 5`". That was
exactly true. Cutting precisely that sentence as its own leaf
(`exists_galoisFixing_cyclotomic_not_isSquare`) and proving *everything else* closed the
node — and the residue is a statement about cyclotomic fields with **no elliptic curve in
it**, provable by someone who never reads `X0.lean`.

The discriminator between this case and the two bad ones is cheap and worth applying:
**does the survey name a specific PROPOSITION, or a body of THEORY to build?** "`K ⊄
ℚ(μ_p)` for `p ≥ 5`" is a proposition — state it, sorry it, prove the rest. "the
Eisenstein quotient, the Hecke algebra and reduction of an abelian variety" is a body of
theory, and that is the shape that turns out to be decoration. A survey naming one
proposition is a gift: the cut is already written.

Two facts the formalisation turned up that no survey predicted, both worth the habit of
re-reading hypotheses after the proof compiles: `hψ`, injectivity of the CM automorphism,
is **never used** (`hnot : ψ g ∉ ⟨g⟩` already gives `ψ g ≠ 0`, since `0 ∈ ⟨g⟩`); and `ψ`
is only ever an **additive** endomorphism, never an isogeny — additivity alone gives
`ψ(E[p]) ⊆ E[p]` and `ψ(k·g) = k·ψ(g)`, which is the whole of what the determinant
argument consumes.

