---
name: flt-uniqueness-may-be-avoidable
description: A leaf that "needs the UNIQUENESS of X" usually does not — apply the theorem that PRODUCES X to the rival and compare the two inside the ring
metadata:
  type: project
---

When a docstring says a leaf is blocked on the **uniqueness** of some object,
check first whether the already-proven theorem that **produces** that object can
simply be applied to the rival, and the two compared algebraically. That is
almost always far cheaper, and it keeps the deep input where it already was.

**Why:** `exists_relSchemeEnd_of_endMinpoly_of_weierstrassModel`
(`Fermat/FLT/FreyCurve/MazurTorsion.lean`) carried a docstring prescribing
Mazur-level input — "at `p = 43, 67, 163` the Galois-stable order-`p` subgroup of
a CM curve is UNIQUE, and it is what a prover of LEAF 1 must supply". That
statement is true and close to circular here (the file is *proving* Mazur), and
it made the leaf look far deeper than it is.

It was never needed. `exists_endMinpoly_of_stable_cyclic_mazurLevel` — proven,
50 lines above, and already the place where `hp ∈ {43,67,163}` enters — takes a
Galois-stable cyclic subgroup of order `p` and returns an endomorphism `φ'` with
`φ'² − φ' + (p+1)/4 = 0` and `ker (2φ' − 1)` EQUAL to that subgroup. Applying it
to the rival subgroup produces a second root of the same quadratic, and then
`(φ − φ')(φ + φ' − 1) = (φ² − φ) − (φ'² − φ') = 0` (needs only that the two
commute, `End.mul_comm_charZero`) plus no zero divisors
(`MazurEndLattice.end_mul_ne_zero`) gives `φ = φ'` or `φ = 1 − φ'`; in the second
case `2φ − 1 = −(2φ' − 1)`, so the kernels agree. No uniqueness theorem is ever
formed.

**How to apply:** before costing a "we need uniqueness of X" audit, grep for the
existence theorem for X and read its conclusion. If it pins X by an EQUATION
(a kernel, a value, a normal form) rather than merely asserting existence, run
it on the rival and compare — the comparison is usually ring algebra. A second
symptom that this route is available: the leaf's own hypotheses already contain
one instance of X, so a rival instance is exactly what the existence theorem
consumes.

Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]], [[flt-two-leaves-may-be-one]].
