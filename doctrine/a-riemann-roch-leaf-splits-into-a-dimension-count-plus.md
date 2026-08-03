## A RIEMANN–ROCH LEAF SPLITS INTO A DIMENSION COUNT PLUS ELEMENTARY ALGEBRA — and the dimensions already know the monomials are independent

(2026-08-01, `flt-lean-215`, on `exists_weierstrassGenerators_of_abelianSchemeChart`
in `ModularCurve/X1.lean`.)  A leaf whose docstring says "Riemann–Roch, Silverman
*AEC* III.3.1" reads as one indivisible citation.  It is not: the citation is a
DIMENSION COUNT (`dim_k L(n·[O]) = n` on a genus-one curve) followed by roughly two
hundred lines of linear algebra over that count, and the second half is provable
in full, today, with no geometry in it at all.  Split there and the count is the
only leaf left.

**The technique that makes the algebraic half cheap, and it is the transferable
part.**  The textbook argument proves the seven monomials `1, x, y, x², xy, y², x³`
LINEARLY DEPENDENT in the six-dimensional `L(6)`, then argues that `y²` and `x³`
must both occur.  Transcribed literally that needs `LinearIndependent` for a
`Fin 6 → R` family (a six-step peel through `Matrix.cons_val` lemmas),
`finrank_span_eq_card`, and a span-of-set-literal manipulation.  **All of it is
avoidable.**  Prove ONE lemma —

    L(n+1) = L(n) ⊔ k ∙ m   for ANY m with pole order exactly n+1

(from `finrank L(n) = n`, `finrank L(n+1) = n+1` and `m ∉ L(n)`, via
`Submodule.finrank_lt_finrank_of_lt` and `Submodule.eq_of_le_of_finrank_le`) — and
then ITERATE it downwards.  Five applications write every element of `L(5)` in the
basis `1, x, y, x², xy` by nested `Submodule.mem_sup` destructuring; a sixth at
`n+1 = 6` produces the relation for `y²` with the `x³` coefficient nonzero BY
CONSTRUCTION, because `y² ∉ L(5)`.  No linear independence is ever stated: **the
dimension count already knows the monomials are independent, and the sup
decomposition is how you spend that knowledge instead of re-deriving it.**

Two riders.  Axiomatise the pole order as a function `d : R → ℕ` with four clauses
(`d 0 = 0`; `d(rs) = d r + d s` off zero; `d(r+s) ≤ max`; `d r = 0 ↔ r` constant) —
`IsDomain R` is then a CONSEQUENCE, not a hypothesis, so the geometry leaf above
never has to supply it.  And the whole normalisation to `y² + a₁xy + a₃y = x³ + …`
is ONE substitution `x ↦ c₅x`, `y ↦ c₅y` with `c₅` the coefficient of `x³` — no
inverse, no cube root, and `linear_combination (algebraMap k R c₅)^2 * hrel` closes
it.  Work out that scaling on paper first; guessing it costs a round trip each time.

### THE WITNESS THAT FIXES THE SCOPE: a pole filtration does NOT see `Δ ≠ 0`

The same leaf's docstring ended *"a prover who has produced `x` and `y` out of
`L(3[O])` has the nondegeneracy in hand for free, since `|3·[O]|` is very ample
exactly when the model is nonsingular"*.  That is true of the GEOMETRY and **false
of the algebra**, and the difference decides whether `W.IsElliptic` is a step or a
leaf.  The coordinate ring of the CUSPIDAL cubic `y² = x³`, namely `k[t², t³]`,
satisfies every clause of the pole-degree axioms with `d(t^m) = m`, and has
`dim L(n) = #{m ≤ n : m ≠ 1} = n` for every `n ≥ 1` — the value semigroup `⟨2,3⟩`
omits exactly `1`, and a singular plane cubic has arithmetic genus one too.  So a
singular curve and a smooth one have INDISTINGUISHABLE pole filtrations, and no
argument from the dimension count can separate them.  What separates them is
NORMALITY (`k[t², t³]` is not integrally closed), i.e. the smoothness of the
ambient curve spent a SECOND time.

**Generalisable, and it is the standing "what else inhabits this predicate?" check
in a new suit:** when a decomposition hands one half a package of axioms, exhibit a
witness satisfying every axiom and ask which clauses of the conclusion still
follow.  Here the witness took ten minutes and it moved one conjunct out of a leaf
that could never have proven it — the alternative being a successor who spends a
run trying to derive `Δ ≠ 0` from a filtration that does not determine it.

