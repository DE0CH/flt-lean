---
name: flt-absent-chapter-vs-the-conclusion
description: "An 'absent chapter' in a leaf's cost list can be TRUE and IRRELEVANT — check it against the leaf's CONCLUSION, not against the author's intended proof; no grep can catch this one"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 8370b060-21e6-4a65-ba37-ef1ba036c62a
  modified: 2026-08-02T19:18:16.549Z
---

(2026-08-02, `flt-lean-29`, `exists_skolemBallDatum_of_genRelPic` in
`Modularity/MoretBailly.lean`.) A mature leaf's docstring listed five chapters a
prover still owed. Three survey rounds had produced it; every clause was true when
written. Two items were the wrong price, in two different ways:

* the **stale-absence** shape, already well covered: the §3.6 item said `deg` and
  `genus` "are not writable, and `genus` matches zero lines in all of `Mathlib/`" —
  true **of `Mathlib/`, which is what was grepped**, and false of `Fermat/` two days
  later when `CurveGenus.lean` landed with `IsCurveGenus`, `ell`, `divisorDegree`
  and the open leaf `exists_isCurveGenus`;
* the **new** shape, and **no grep can find it**: the §3.2 item said the symmetric
  power `X̄^{(d)}` is absent. Still true; **and irrelevant**, because the leaf's
  CONCLUSION parametrises by `Fin d → ℚ`, a bare affine space, and never mentions a
  scheme of divisors. Moret–Bailly needs `X̄^{(d)}` as a SCHEME so that `φ_d` is a
  morphism; a prover in divisor/function-field language needs only the coset
  `{f ∈ rrSet D : ord_z f = 0 on Z, f|_Z = α}` in `X̄.functionField`, and `rrSet`
  and `Scheme.ord` both exist. A chapter of the author's PROOF had been recorded as
  a chapter of the leaf's STATEMENT.

**Why:** an absence table is written by whoever declined to prove the leaf, from
the argument they had in mind. Its facts age; its ATTRIBUTION was never checked at
all.

**How to apply — two questions per item, and the second is the one nobody asks:**
(i) re-grep the absence in `Fermat/` as well as in the pin; (ii) **does the leaf's
CONCLUSION mention the missing object?** If not, ask what the conclusion actually
quantifies over and price THAT. Here that took the residue from five chapters to
two, and neither survivor is the one the list opened with.

Corollary for authors: per item, say whether it is needed to STATE the residue or
only to prove it your way. Those decay at completely different rates.

Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-smoothofrelativedimension-is-the-curve-currency]].
