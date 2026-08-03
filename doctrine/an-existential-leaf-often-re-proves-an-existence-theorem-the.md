## AN EXISTENTIAL LEAF OFTEN RE-PROVES AN EXISTENCE THEOREM THE SAME FILE ALREADY HAS
(2026-07-31, `X0.lean`.) `exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` asked a prover
to EXHIBIT a multiset reproducing the point counts of `X_0(N)_{𝔽_ℓ}` over every `𝔽_{ℓⁿ}`. Doing
that at all is **Weil rationality for a curve** — and `exists_isWeilEigenvalues` sat 680 lines
ABOVE it in the same file, proving exactly that over its own named leaf. The existential leaf was
carrying a whole classical theorem a second time, invisibly, because the redundancy is between a
CONCLUSION (`∃ β, IsWeilEigenvalues …`) and a HYPOTHESIS nobody had written down.
So: **when a leaf asks you to produce an object, grep the file above it for an existence theorem
for that same object before doing anything else.** The leaf's real content is usually only the
IDENTIFICATION — "the object you can already get is *this* one" — and splitting the existence off
is a provable reduction, not a repackaging: derive the old leaf from the new one plus the existing
existence theorem, and check the converse holds too, so you can state in the docstring that nothing
was made harder.
**BUT: check who consumes the DERIVATION before you reverse a cut.** The tempting move here was
shorter — sorry the universally-quantified `isEichlerShimuraTransform_x0` and derive the existential
from it. It is mathematically better (same delegation, one less statement). It is **wrong
mechanically**, and the reason generalises: a five-theorem "pinning" chain
(`multiset_eq_of_forall_pow_sum_eq` and friends) had **exactly one consumer in the tree** — the
proof that transports the EXISTENTIAL leaf's witness to an arbitrary multiset. Reversing the cut
deletes that proof's reason to exist and strands all five as free-floating code, which this project
forbids. The existential shape was load-bearing for ~200 lines of proven algebra, and nothing in
either statement says so.
The check is one grep per lemma in the block you are about to orphan:
    grep -rn '<lemma-name>' --include=*.lean . | grep -v '<the file>:'   # external consumers
    grep -n '<lemma-name>' <the file>                                    # internal, minus docstrings
A cut is only free to reverse when the derivation it deletes is not the sole consumer of anything.
