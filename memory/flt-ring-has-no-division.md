---
name: flt-ring-has-no-division
description: "\"divide by 2 inside End\" is not a formality — it is the claim that the CM order is MAXIMAL, and it is false one conductor over"
metadata:
  type: project
---

`exists_cmEndomorphism_of_mem_isolatedCMJInvariants` (X0.lean) carried a route
audit saying its cheap route needs `ψ = √−p` and then "`φ = (1 + ψ)/2` follows by
division by `2` inside `End`", with the audit's ONE named gap being that
`E/⟨g⟩ ≅ E`. The audit was right about that gap and wrong that the rest was
formal, in both directions:

* `End W` is a `Subring (AddMonoid.End W.Point)` — **a ring, and a ring has no
  division.** Halving `1 + ψ` asserts `End(E_ℚ̄)` is the MAXIMAL order `O_{−p}`
  and not the conductor-`2` order `ℤ[√−p]`. Both contain an element of norm `p`
  and trace `0`, so `ψ` cannot tell them apart, and stated for an arbitrary curve
  the halving is **FALSE**: `qfbclassno(−4p) = 3` at `p = 11, 19, 43, 67, 163`
  alike. Only rationality of `j` excludes those three curves per prime —
  `polclass(−44)` is an irreducible cubic against `polclass(−11) = x + 32768`.
* The obligation the audit *did* name as unavoidable — `IsIsogeny` for the halved
  `φ` — is **free**; see [[flt-descend-makes-isisogeny-free]].

**Why:** an audit's named gap is where its author stopped looking, not where the
difficulty ends. The step a route calls formal is exactly the step nobody
re-derives, so a false one survives every later review — and here it would have
sent an owner at a "last mile" that is a second CM theorem.

**How to apply:** price EVERY step a cheap route calls formal, not just the one it
flags. Anything of the form "divide by `n` inside a ring of endomorphisms" is an
integrality/maximality claim: make it its own named leaf, carrying the hypothesis
that makes it true (here `E.j ∈ isolatedCMJInvariants`, which is therefore
load-bearing twice), and write the counterexample that shows the hypothesis
cannot be dropped. Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audits-search-production-not-invariant]].
