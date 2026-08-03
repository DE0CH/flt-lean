## A STRUCTURE THAT DOES NOT PIN ITS OWN LABELLING MAKES "∀ C" LEAVES FALSE
(2026-07-31, `flt-lean-212`, caught before the leaf was written.) `X0.lean`'s
`IsX0Compactification.CuspLocus` indexes the cusps of `X_0(N)` BY `N.divisors`:
a family `κ : N.divisors → (Spec (K d) ⟶ X)` with fields `degree` (residue
degree `φ(gcd(d, N/d))`), `cover`, `disj`, `ratPoint`. The obvious way to state
the Atkin–Lehner boundary action over it is
    ∀ C : hX.CuspLocus, ∀ d, w.base '' range (C.κ d).base = range (C.κ (N/d)).base
and that statement is **FALSE**, at every level whose divisors are not separated
by the degree. Every field of `CuspLocus` is invariant under precomposing `κ`
(and `K`) with a permutation `π` of `N.divisors` preserving `φ(gcd(d, N/d))`, so
a relabelled locus is again a lawful `CuspLocus` — and it induces the CONJUGATED
permutation `π⁻¹ ∘ (d ↦ N/d) ∘ π`, not `d ↦ N/d`. At `N = 65` all four divisors
have degree `1`, so the labelling is arbitrary and the leaf dies outright.
The faithful form is **existential over the structure**:
    ∃ C : hX.CuspLocus, ∀ d d', d * d' = N →
      w.base '' range (C.κ d).base = range (C.κ d').base
i.e. *the classical indexing exists and has the property* — which is what
Deligne–Rapoport and Ogg actually supply. Everything downstream of it here is
label-free (a fixed rational cusp lands in two disjoint `range`s), so nothing is
lost by weakening `∀ C` to `∃ C`.
**The general rule, because this is not about cusps.** Before stating a leaf as
"for every `S : SomeStructure`, the index `i` behaves thus", ask which
permutations of the index set every field of `SomeStructure` is invariant under.
Whatever they are, the leaf must not distinguish orbits they merge. The tell is a
structure whose fields are all *invariants* (degrees, covers, disjointness,
cardinalities) while the leaf asserts something about the *labels*. `∃ S` is
usually the repair, and it is usually also the honest reading of the literature.
**Corollary that paid for itself here**: making the arithmetic side condition an
invariant one folded two level-specific leaves into one. `w_N` fixes no rational
cusp whenever `∀ d ∈ rationalCuspDivisors N, d * d ≠ N` — at `65, 91` because a
squarefree `N > 1` is not a square, at `169` because the self-paired divisor `13`
carries `φ(13) = 12` conjugate cusps and so is not in `rationalCuspDivisors 169`.
The docstring of the `65, 91` leaf had recorded that `169` "genuinely cannot be
folded in"; it could, once the hypothesis was quantified over the RATIONAL cusp
divisors instead of over all divisors.
