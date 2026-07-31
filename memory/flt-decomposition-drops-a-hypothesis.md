---
name: flt-decomposition-drops-a-hypothesis
description: A cut can leave a hypothesis on only one half; the child inherits the parent's audit, which then certifies nothing, so a numeric-bound leaf with no hypothesis about that quantity is usually false
metadata:
  type: project
---

When a node is decomposed, a hypothesis the parent needed can end up on only
ONE child while both children need it — and the child's docstring is usually
the parent's audit reproduced verbatim, so the leaf reads as fully checked
while being false.

`card_relPoint_not_liesIn_le_of_finite_toAffineLine` (`ModularCurve/X0.lean`,
cut 2026-07-28, refuted 2026-07-31) concluded `≤ 2` — which IS the degree of
`φ` — while the three-point clause `_hthree` that bounds that degree went to
the sibling only. Counterexample: `S = K = 𝔽₂`, `X = ℙ¹`,
`U = ℙ¹ ∖ {0, 1, ∞}`, `φ = t + 1/t + 1/(t−1)` (polar divisor `(0)+(1)+(∞)`,
so `U = φ⁻¹(𝔸¹)` and `φ` is finite of degree `3`); the conclusion reads
`3 ≤ 2`.

**Why:** an audit copied onto a child certifies the PARENT's statement. It
carries no information about the child's, and its presence makes the child
look audited. Same failure mode as [[flt-two-leaves-may-be-one]] in reverse —
there two leaves were secretly one, here one hypothesis was secretly two.

**How to apply:** after any decomposition, diff each child's hypothesis list
against the parent's and justify every omission in writing. "It is on the
sibling" is valid only when the children are ALTERNATIVES; when the consumer
SUMS them they are conjoined and may both need it. Fast smell test for
reviewers: a leaf whose conclusion is a NUMERIC BOUND and whose hypotheses
never mention the quantity that bound measures (degree, rank, genus,
conductor) is almost certainly false — look for the hypothesis on a sibling
before looking for a proof. The repair is usually free, because the consumer
already holds it (see [[audit-searched-production-not-invariant]]).
