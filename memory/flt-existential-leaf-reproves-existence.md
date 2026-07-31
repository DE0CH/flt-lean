---
name: flt-existential-leaf-reproves-existence
description: "An `exists x, P x and Q x` leaf often re-proves an existence theorem the same file already has upstream; delegate it — but check who consumes the derivation before reversing the cut, because the existential shape can be the sole consumer of a proven lemma chain"
metadata:
  node_type: memory
  type: project
---

`exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` (`ModularCurve/X0.lean`)
asked a prover to EXHIBIT a multiset reproducing the point counts of
`X_0(N)_{𝔽_ℓ}` over every `𝔽_{ℓⁿ}`. Doing that at all is **Weil rationality for
a curve** — and `exists_isWeilEigenvalues` sat 680 lines above it in the same
file, proving exactly that over its own named leaf. The leaf had been carrying a
whole classical theorem a second time for three days, invisibly, because the
redundancy is between a CONCLUSION (`∃ β, IsWeilEigenvalues …`) and a HYPOTHESIS
nobody had written down. No frontier instrument can see that.

**Why:** an existence obligation reads as atomic, so nobody greps upward for the
object it demands. The leaf's real content is almost always only the
IDENTIFICATION — "the object you can already get is *this* one".

**How to apply:** when a leaf asks you to produce an object, grep the file above
it for an existence theorem for that same object BEFORE anything else. Then split
the existence off and check BOTH directions, so the docstring can state that
nothing was made harder: old leaf ⟸ new leaf + existing existence theorem, and
old leaf ⟹ new leaf. Here that turned a 3-line assembly out of the leaf and left
a strictly weaker one.

**The counter-rule, which decided the actual cut.** The shorter move was to sorry
the universally-quantified sibling (`isEichlerShimuraTransform_x0`) and derive the
existential from it. Mathematically better, mechanically wrong: the five-theorem
pinning chain (`multiset_eq_of_forall_pow_sum_eq`,
`exists_eq_replicate_zero_add`, `exists_eq_replicate_zero_add_of_pow_sum_eq`,
`IsEichlerShimuraTransform.of_pow_sum_eq`, `pow_sum_eq_of_isWeilEigenvalues`)
had **exactly one consumer in the tree** — the proof transporting the
EXISTENTIAL leaf's witness to an arbitrary multiset. Reversing the cut strands
all five as free-floating code. So an existential shape can be load-bearing for
~200 lines of proven algebra, and nothing in either statement says so; grep every
lemma of the block you are about to orphan before reversing a cut. See
[[flt-cut-leftovers-close-sibling-leaves]] and
[[flt-cleaner-statement-harder-proof]].
