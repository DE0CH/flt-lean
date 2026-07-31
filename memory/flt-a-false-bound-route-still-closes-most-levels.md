---
name: flt-a-false-bound-route-still-closes-most-levels
description: "A norm-only route refuted for a leaf AS A WHOLE usually still closes most of its levels; measure per level before treating the route as dead"
metadata:
  type: feedback
---

A task prompt can carry a correct, measured refutation of an approach — "the
`tail < head` shape is FALSE here, do not restate the leaf that way" — and the
right response is still to **build that shape and measure it per level**, not to
abandon it.

`axisRestrict_one_ne_zero_of_isNewEigenformAt` (`g(i/√M) ≠ 0` at every divisor
of a Kenku level, `X0.lean`, 2026-07-31) came with exactly that warning, and it
was true: with the TRUE coefficients `∑_{n≥2} ‖bₙ‖x^{n-1} > 1` at `M = 35, 39,
63, 75`, so no bound on `‖bₙ‖` can ever close those. What the warning did not
say, because nobody had computed it, is that the same shape closes **fifteen of
the thirty-two divisors outright** with bounds already proven in the file, and
nine more with bounds also already proven (`norm_coeff_le_sqrt_of_dvd`) once the
majorant is made level-dependent. The leaf went from one bare `sorry` over all
divisors to `≤ 18` PROVEN plus a seventeen-level leaf carrying a per-level table
that says which levels are cheap and which genuinely need cancellation.

**Why:** a refutation of "X proves the leaf" is not a refutation of "X proves
part of the leaf", and for a leaf quantified over a finite parameter set those
are very different claims. The refuting witness lives at ONE parameter value.

**How to apply:** when a prompt or docstring refutes a bound-based route, write
the ~15 lines that evaluate the route's quantity at every parameter value before
doing anything else. Report the threshold and the per-level margins — that table
is the decomposition. Two further habits that paid here:

- **Cross-validate the majorant code against a table the file already carries.**
  Mine reproduced `frickeTailSum_tail_lt_head_of_mem_kenkuLargeDivisors`'s
  PARI/GP table at all 27 entries to three digits, which is what made it safe to
  write my own numbers into a docstring. See [[flt-leaf-cost-estimates-are-hypotheses]].
- **The sibling's threshold is not yours.** `frickeTailSum_tail_lt_head_of_le_thirty`
  reaches `M ≤ 30` because its series has a `1/n`; the same crude bound without
  it reaches only `M ≤ 13`, and `d(n)√n` on five explicit terms reaches `18`.
  A "do it like the sibling" instruction hides a factor-of-two difference in
  what the identical argument buys.
