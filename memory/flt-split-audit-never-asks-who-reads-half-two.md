---
name: flt-split-audit-never-asks-who-reads-half-two
description: "A \"should this leaf be split into A ∧ B?\" audit prices the split and never asks whether B has a consumer; when it has none the answer is a deletion, not a split."
metadata: 
  node_type: memory
  type: project
  originSessionId: 04ad1576-4988-447a-b9a0-c3adf50d78c0
  modified: 2026-08-01T16:14:49.676Z
---

(2026-08-01, `flt-lean-27`, `X18.two_divisible_pic` / `X13.two_divisible_pic` in
`ModularCurve/HyperellipticJacobian.lean`.) `Pic = 2·Pic` for a finitely generated group IS
`rank = 0` **and** `#tors` odd. Two careful audits on 2026-07-30 asked whether to SPLIT it
into those two leaves, priced the second half as a fresh development (the 2-torsion theory
of hyperelliptic Jacobians from valuation axioms), and correctly answered no — twice.

**Neither asked who reads the second half.** Nothing did: the sole consumer `finite_pic`
gets `Finite` from `AddGroup.FG` (= `fg_pic`, PROVEN, immediately above) plus torsion
alone. So the resolution was a DELETION — weaken to `∀ z, ∃ n > 0, n • z = 0`, rename to
`torsion_pic`, rewire the one call site — not a split. Count unchanged 22 → 22; what
changed is that both leaves stopped owing `#J(ℚ)` odd, which would have to come through
`#J(𝔽ₚ)`, a quantity that file does not carry.

**Why:** "should `A ∧ B` be split?" is a question about the PROVER's convenience, and its
framing presupposes both halves are wanted. The question that finds this is **grep the
consumers and see which conjunct each reads.**

**How to apply:** on any leaf whose statement is a disguised conjunction (a divisibility
that bundles a parity, an equality that bundles a bound, an exact degree beside a
generator), read the call sites before reading the audits. Then:

- the leaf's justification for the stronger form is usually about the ROUTE ("it is the
  literal output of a 2-descent") — routes are not consumers; check the route still works
  over the weaker statement, usually one extra step;
- the lemma that made the stronger form cheap goes free-floating; delete it and record its
  statement plus `git show <sha>:<path>` on the replacement, with what would justify
  restoring it;
- weakening a CONCLUSION is the one restatement whose falsity audits transfer (a weakened
  conclusion cannot become false) — but say why, expect the NON-VACUITY witness to narrow,
  and re-derive the ATOMICITY verdict, since a weaker statement can admit a new cut.

Receipt for the count-neutral recut, for the commit message:
`git diff -U0 -- <file> | grep -E '^[+-].*sorry'` must show paired ±, one pair per leaf.

Related: [[flt-weaken-the-leaf-to-an-inequality]],
[[flt-overdetermined-degree-conjunct]], [[flt-closing-a-leaf-may-close-nothing]],
[[flt-atomicity-verdict-checks-hypotheses-only]].
