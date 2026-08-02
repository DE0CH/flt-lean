---
name: flt-finite-computation-count-the-counterexamples
description: "A sieve route ending \"which is a finite computation at the chosen ℓ\" asserts a universal statement over a finite set — count how many elements of that set refute it before believing the route"
metadata: 
  node_type: memory
  type: project
  originSessionId: b5de536e-00e4-4b69-a8e5-53aad99293c1
  modified: 2026-08-01T13:07:19.741Z
---

A reduction/sieve route in flt-lean almost always ends *"so it suffices that
`P(x̄)` holds in the special fibre, which is a finite computation at the chosen
`ℓ`"*. That sentence asserts two things: the REDUCTION (usually sound, and the
part its author checked) and that the residue is a UNIVERSAL statement over a
finite set (unsound as soon as one element of that set refutes it).

**Check the second half — it is two CAS numbers.** Count the finite set
(`#X(𝔽_ℓ) = ℓ + 1 − Tr T_ℓ` for a modular curve, one `mfheckemat` call), then
count how many of its elements the conclusion is false at. Nonzero means the
route silently needs a LOCUS restriction it never states, and excluding the
other locus is a new uncosted obligation.

**The counterexamples are predictably the CUSPS.** These sieves are applied to
statements true on the open part and false on the boundary — the restriction to
`strY` in the leaf's signature is the tell — and reduction carries the boundary
into the special fibre where no point count can distinguish it.

**FIRST, SIMPLIFY THE RESIDUE: a class equality on a curve of genus ≥ 1 is a
POINT equality.** Abel–Jacobi injectivity holds on the special fibre too, so
`[P̄] = [w̄ P̄]` is EQUIVALENT to `P̄ = w̄ P̄` — the "finite computation" is really
*does `P` reduce to a FIXED POINT of `w̄`*, which is a far more answerable
question. Fixed points of `w_N` are CM points of discriminant `−4N`, so their
`𝔽_ℓ`-rationality is one `factormod(polclass(-4N), ℓ)`.

Worked instance (2026-08-01, `ajMinusTorsion_eq_zero_x0OneTwentyFive`):
`#X_0(125)(𝔽_3) = 4`, of which **two are cusps** (`w` always swaps the two
rational cusps, so the universal form fails at EVERY `ℓ`). And `polclass(-500)`
stays a single degree-10 irreducible mod 3, so `w̄_125` fixes **no** point of
`X_0(125)(𝔽_3)` — all four are in swapped pairs, the sieve returns a nonzero
class for every rational point, and completing it would prove `Y_0(125)(ℚ) = ∅`,
the one route that cluster's vacuity audit forbids. The prime its docstring
called "the cheapest" is the one at which the route provably cannot work.

**Cross-check the CAS three ways before believing it decided a route:** here
the fixed-point count `10` came out of `h(−500)`, of Riemann–Hurwitz
`2g−2 = 2(2g⁺−2) + R`, and of the Lefschetz number
`#Fix(w̄ ∘ Frob_ℓ) = 1 + ℓ − Tr(w T_ℓ)`; and `r+2s = #X(𝔽_ℓ)`,
`r+s+i = #X⁺(𝔽_ℓ)`, `r+2i = #Fix` are three mutually checkable equations.

**The route's own recorded refuting check will PASS**, because it tests the half
its author doubted (here a torsion bound) and not the quantifier of the final
step. See [[flt-audit-refuting-check-unrun]]: this is one step further on — the
check was run, it passed, and it was the wrong check.

**Why:** a route that cannot close attracts repairs that cannot work; three
dispatches had been priced off this one.

**How to apply:** correct the route in the leaf's docstring rather than taking
the case-split cut it exposes, unless apparatus for BOTH halves already exists —
here the cut would have traded one leaf for a formal-immersion existential, a
two-point check, and a reduction datum at `(125, 3)` that is nowhere in the tree.
Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-audit-recommended-axis-may-be-worse]].
