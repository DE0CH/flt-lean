## BUY A "THE IMAGE LANDS IN `H`" HYPOTHESIS BY PASSING TO A POWER — the normal core is the price
(2026-07-31, `flt-lean-129`, closing the `T`-primes half of
`exists_pow_forall_localInertiaGroup_mul_pow_cyclotomicCharacter_eq_of_unramified`
in `Modularity/Interface.lean`.)
A recurring shape here: a theorem is PROVEN under a hypothesis of the form *"the
image of the subgroup `I` under the character `δ` lands in the open subgroup
`H`"*, and the leaf that needs it cannot supply that hypothesis — the whole point
of the leaf being the primes where the image is NOT small. That reads as a wall,
and this leaf's own docstring priced it exactly so: *"the tame/wild analysis of
`exists_isOpen_subgroup_forall_localInertiaGroup_map_eq_one` run without its
'inertia image lands in `H`' hypothesis"*, i.e. as a redo of local ramification
theory.
**It is Lagrange, and it costs one paragraph.** `H` open in a COMPACT group has
finite index (`Subgroup.quotient_finite_of_isOpen`), so its NORMAL CORE has finite
index `N` (`Subgroup.finiteIndex_normalCore`), and `γ ^ N ∈ H.normalCore ≤ H` for
EVERY `γ` (`Subgroup.pow_index_mem`). So the character `δ(·)^N` — same continuity,
same multiplicativity, same nowhere-vanishing, and still a homomorphism because the
TARGET is commutative — satisfies the hypothesis UNCONDITIONALLY, and the original
proof runs verbatim with `δ` replaced by `δ(·)^N`. Here that was a ~60-line copy
with four lines changed, and it compiled first try.
**The trade, and it is the check to run before reaching for this:** the conclusion
weakens from `δ = 1` to `δ^N = 1`. So the move is available exactly when the
consumer needs FINITE ORDER rather than triviality. It did here — the leaf's
conclusion is an identity of `n`-th powers with `n` existentially quantified, so any
multiple absorbs `N`, and the glue takes `n := n_p · ∏_{q ∈ T} n_q`. **Ask what the
consumer's quantifier over the exponent is before pricing the hypothesis as
missing**; an `∃ n` in the conclusion is what makes a hypothesis about smallness
purchasable.
Two riders:
* **Keep BOTH theorems; neither implies the other, and a reviewer will otherwise
  delete one as a duplicate.** The strong form (`δ = 1`, under the hypothesis) is
  what a "finitely many BAD primes, trivial at the good ones" statement needs; the
  weak unconditional form is what a type-`A₀`-style statement needs AT the bad ones.
  A `p`-adically-valued Dirichlet character of conductor `q` separates them:
  finite-order and nontrivial on `I_q`, so it refutes the strong conclusion, satisfies
  the weak one, and — consistently — fails the strong form's hypothesis. Put that
  witness in the docstring.
* **The exponent must be uniform in the quantified element, and it is:** `N` depends
  on `δ` and the ambient group only, never on `σ`. A per-element exponent would be
  useless, and that is the thing to check first when this is applied to a family.
**And the shape of the win is worth naming separately: a leaf whose docstring lists
its residue as TWO pieces is a cut waiting to be performed, even when you cannot
touch either piece.** Here the docstring said "local algebraicity at `p`" AND "finite
order of the ramification at the primes of `T` other than `p`". Splitting on exactly
that sentence, proving the second piece, and leaving the first is `1` leaf in and `1`
leaf out — but the survivor now carries the single prime `p` instead of `insert p T`,
and `a`, `b`, `χ_cyc` and the whole `T`-bookkeeping are gone from it. The count does
not move; say so in the commit, and judge it by what is LEFT in the leaf.
