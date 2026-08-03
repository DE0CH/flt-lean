## IN A CHAIN WHERE A FACTOR VANISHES AT ONE LINK, A VANISHING AT THE END IS NO EVIDENCE ABOUT A LINK
(2026-08-01, `flt-lean-238`, `tsum_coeff_ne_zero_atkinLehnerMinus_oneTwentyFive`.)
This file already records that *a counterexample must be checked against the hypothesis
it refutes*, and that the tell is a hedge inside the witness. Here is the harder variant,
where the witness is REAL, satisfies every hypothesis, and refutes a genuine theorem —
just not the one it is attached to.
That leaf's docstring carried, in bold, **"`_hw` MAY NOT BE DROPPED, and the witness is
orbit 2"**, on the ground that the two `w₁₂₅ = +1` embeddings have `L(f,1) = 0` to 57
digits. Every clause is TRUE. The inference is false, because `L` and the leaf's sum sit
at opposite ends of a chain with a vanishing factor in between:
    L(f,1) = 2π · cuspPeriod = (2π/√N) · (1 − ε) · ∫₁^∞ = (2π/√N)(1 − ε) · S
At `ε = +1` the factor `(1 − ε)` is what kills `L`; `S` is untouched. Computed, the two
PLUS embeddings have `S = 0.79714…` and `0.52567…` — nonzero, so the leaf is TRUE without
`_hw`, and at the twelve-term truncation the recorded bound `3/8` holds at all EIGHT
embeddings rather than only the six minus ones.
**The check is one line of algebra and nobody runs it: write down the chain from the
witness's fact to the leaf's conclusion, and look for a factor that vanishes strictly
between them.** If there is one, the witness is evidence about everything ABOVE that
factor and nothing below it. The failure is invisible to every audit discipline in this
file, because the audit's arithmetic is right, its witness is real, and the statement it
refutes is a theorem in the same cluster three declarations away.
Corollary on what to DO about it, which is not "delete the hypothesis": keeping `_hw`
costs a prover nothing, cannot make the leaf false, and halves the certification burden
from eight embeddings to six — so it stays, with the audit corrected in place and the
place it IS load-bearing (`cuspPeriod_ne_zero_…`, where the sign is the whole point)
named explicitly. See also the standing rule that a docstring inviting you to drop a
hypothesis from a sorry leaf is a trap; this is the same trap reached from the other side.
### The reusable cut: a "certify this convergent sum is nonzero" leaf splits head/tail
The whole ANALYTIC half of such a leaf is level-generic and provable today; only a lower
bound on finitely many explicit terms needs a certified basis. `‖aₙ‖ ≤ 2n` against a
weight carrying `1/n` cancels exactly, leaving a pure geometric majorant
(`2(n+1)·wₙ = (√N/π)·r^{n+1}`, `r = e^{-2π/√N}`), so the tail past term `K` is
`(√N/π)·r^{K+1}/(1−r)` with no arithmetic input at all. Count `1 → 1`; what leaves the
frontier is the summability, the truncation and the error control, and the residue is a
statement a certified-evaluation tool closes at every level at once. Report it as a RECUT
with the token count quoted (`37 → 37` here) — a `−1 +1` warning-set delta is otherwise
indistinguishable from one closure plus one unrelated disclosure.
**Transposing such a block to a level with IRRATIONAL `√N` costs only enclosures.** The
`169` sibling opens with the exact `√169 = 13` and every later constant is rational
arithmetic; at `125` the same chain runs through `√125 < 11.181` plus `Real.pi_gt_d6`,
and nothing else about the argument changes. Budget two extra bounding lemmas, not a
redesign — and note the crude `x + 1 ≤ eˣ` is enough for `r`, because the tail constant
is loose by an order of magnitude anyway.
