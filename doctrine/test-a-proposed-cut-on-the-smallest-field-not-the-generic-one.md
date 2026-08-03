## TEST A PROPOSED CUT ON THE SMALLEST FIELD, NOT THE GENERIC ONE

(2026-07-31, `exists_isAmpleSheaf_of_field`.) The obvious way to cut "an abelian variety is
projective" is to hand out the translation argument as its own leaf: *for every `z` there are
`K`-automorphisms `f₁ … f_k` of `X` with `z ∈ ⋂ fᵢ⁻¹(U)` and `⨂ fᵢ^*L ≅ L^{⊗k}`*, leaving only
formal bookkeeping above it. It reads as obviously true — it IS what Mumford's proof produces —
and **every version of it is FALSE**, for a reason no amount of thinking about the generic case
surfaces.

The witness is four lines of arithmetic. `E : y² + y = x³ + x + 1` over `𝔽₂` is nonsingular
(`Δ = −91`, odd) and has `E(𝔽₂) = {O}`: over `𝔽₂` the left side is `0` for both `y` and the right
side is `1` for both `x`, so there is no affine point. Take `U = E ∖ {O}` and `L = 𝒪((O))`. Any
`K`-automorphism `f` of the SCHEME `E` sends the `K`-point `O` to a `K`-point, hence to `O`, hence
is a group automorphism, hence `f ⁻¹ᵁ U = U`. So every section reachable from `s` by pullback
along automorphisms has non-vanishing locus exactly `U`, and `z = O` is in none of them. Over `ℚ`
the same argument kills it for any curve with trivial Mordell–Weil group.

**The generalisable rule: when a proposed sub-leaf quantifies over AUTOMORPHISMS, RATIONAL POINTS,
or anything else whose supply depends on the base field, instantiate it at `𝔽₂` before writing it
down.** Arguments written over `K̄` silently use Zariski-density of the closed points; the density
is invisible in the statement and is exactly what the cut drops. The smallest field is where a
cut dies, and the test costs a brute-force point count you can run in ten lines of Python (or
check by hand, as above) — far cheaper than dispatching an agent at a leaf that cannot be proven.

Corollary for the ROUTE, not just the cut: once the audit forecloses the cheap sub-leaf, the
docstring must say what the correct field-independent route IS, or the next agent re-derives the
same dead end. Here it is either base change to `K̄` plus faithfully-flat descent OF THE PROPERTY
(the sheaf itself is already defined over `K`, so nothing has to be descended but ampleness), or
staying over `K` and taking norms along `X_κ → X` with Chevalley's affineness theorem. Both are
recorded on the leaf.

