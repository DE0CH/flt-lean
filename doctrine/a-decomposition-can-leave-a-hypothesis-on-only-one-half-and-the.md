## A DECOMPOSITION CAN LEAVE A HYPOTHESIS ON ONLY ONE HALF — and the child inherits the parent's audit, which then certifies nothing
(2026-07-31, `card_relPoint_not_liesIn_le_of_finite_toAffineLine`.) The rule above is about a leaf
restated TWICE. This is its decomposition analogue, and it is commoner, because decomposition is
the main move this development makes.
`card_relPoint_le_of_hasDoubleCoverOfAffineLine` was cut into two leaves along the `U` / `X ∖ U`
seam. The parent's degree hypothesis — the three-point clause `_hthree`, which is what makes
`deg φ ≤ 2` — was restated on the `U` half and **silently omitted from the complement half**,
whose conclusion is the bare bound `≤ 2`. That bound *is* the degree. So the complement leaf was
FALSE from the minute it was written.
Counterexample, and it is not exotic: `S = K = 𝔽₂`, `X = ℙ¹`, `U = ℙ¹ ∖ {0, 1, ∞}`, and
`φ = t + 1/t + 1/(t−1)`, whose polar divisor is `(0) + (1) + (∞)` so that `U = φ⁻¹(𝔸¹)` and `φ` is
finite of degree `3`. Every surviving hypothesis holds — proper, smooth of relative dimension `1`,
geometrically connected, `ι` an open immersion and dominant, `φ` finite over the base — and the
conclusion reads `3 ≤ 2`. Raise `#D` to raise the count arbitrarily.
**Why every ordinary check passed.** The child's docstring was the parent's audit, reproduced
verbatim and correctly — it even *cites* the degree, "at most `d ≤ 2` points". The prose was
true of the parent. It was not true of the child, because the hypothesis the prose depends on
had gone to the sibling. An audit reproduced onto a child certifies the PARENT's statement; it
carries no information about the child's, and its presence makes the child look checked.
**The mechanical check, and it is cheap: after any decomposition, diff each child's hypothesis
list against the parent's and justify every omission in writing.** "It is on the sibling" is a
valid justification only when the children are ALTERNATIVES; when they are CONJOINED — two halves
summed by the consumer, which is the usual shape here — a hypothesis the parent needed is needed
by whichever half uses it, and possibly by both. `_hthree` was needed by both.
**Corollary, a fast smell test for reviewers.** When a leaf's conclusion is a NUMERIC BOUND and no
hypothesis mentions the quantity that bound measures (a degree, a rank, a genus, a conductor), the
leaf is almost certainly false — look for the hypothesis on a sibling before looking for a proof.
The repair here was free, in the shape the section above predicts: the consumer already held
`hthree` from destructuring `HasDoubleCoverOfAffineLine` and was passing it to one child and
discarding it at the other.
