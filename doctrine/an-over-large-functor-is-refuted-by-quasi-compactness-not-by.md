## AN OVER-LARGE FUNCTOR IS REFUTED BY QUASI-COMPACTNESS, NOT BY DEFORMATION THEORY — and a docstring's SCOPING is load-bearing

(2026-07-31, `exists_ringHom_gamma0GITPresentationOver_of_atlas_charDvd`.) When a
level-structure predicate is under-committed, the moduli functor it defines is
too big and the usual instinct is that refuting representability needs a
tangent-space or deformation argument. **Look instead for a numerical invariant
that is upper-semicontinuous on the carrier and unbounded in the functor.** Here
`CyclicSubgroupOfOrder N` pins the *geometric point count* and never the *rank*,
so in characteristic `p` it also admits `C₀ × ker F^k` of rank `p^k · N` for
every `k`; and the rank of a finite morphism is bounded on a QUASI-COMPACT base
(Nakayama: a minimal generating set of the stalk lifts to a neighbourhood, so
`r ≤ r(x)` there; take a finite subcover). Unbounded invariant + quasi-compact
carrier = contradiction, in three lines, with no local freeness, no finite
presentation and no noetherian hypothesis.

The discrimination this buys is sharp and is the useful part: **representability
survives, affineness does not.** A leaf that merely asks for a representing
SCHEME can answer `⊔_{k} M_k` indexed by the invariant and is untouched; a leaf
that says that scheme is AFFINE — or, as here, hands you a `A : Type` with
`[CommRing A]` and demands `cover` through `Spec A` — is dead. So when an audit
records "the extra objects are separated by a locally constant rank, so a
representing object could be a disjoint union", it has already written down the
refutation of every affine statement in the cluster without noticing.

**And the root cause is a scoping sentence that stopped being true.**
`CyclicSubgroupOfOrder`'s docstring justified the substitution by Cartier's
theorem "over a base in which `N` is invertible — in particular over any
`ℚ`-scheme, **which is the only case the modular-curve layer evaluates**". That
was correct when written. An `𝔽_ℓ` layer was added months later, evaluated the
same structure in characteristic `p`, and nothing re-read the sentence — so an
entire branch (five theorems above one open leaf) rests on a refuted premise
while every frontier instrument reports it green. **A "the only case we
evaluate" clause in a definition's docstring is a HYPOTHESIS on the rest of the
development; when you add a layer at a new base, grep the definitions you
consume for that shape and re-check each one.** It costs minutes and it is the
only thing that catches this class, which is invisible to the compiler, to the
sorry count and to the census alike.

