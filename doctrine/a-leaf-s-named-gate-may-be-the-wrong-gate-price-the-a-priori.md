## A LEAF'S NAMED GATE MAY BE THE WRONG GATE — price the a-priori bounds first

(2026-07-31.) Three X0.lean docstrings agreed that
`tsum_coeff_ne_zero_atkinLehnerMinus_chabautySemiprimeLevel`,
its `169` sibling and `charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable` all needed
the same missing theory — "an explicit certified basis of `S₂(Γ₀(N))` with its
Atkin–Lehner decomposition" — and that whoever built it should expect to close all
three. At `65` and `91` that was **false**, and the leaf closed without any basis
over **Ramanujan–Petersson** (`a_p` real, `a_p² ≤ 4p`) plus what the eigenform
carrier already holds. One standard level-free theorem replaced a bespoke
computation good at exactly two levels.

**And the theorem was ALREADY IN THE FILE, as an open leaf 37000 lines above.**
The first attempt stated it as a NEW leaf (`exists_real_coeff_prime_sq_le_four_mul`),
built, went green, and was committed — a clean duplicate of
`realCoeff_norm_le_of_isWeightTwoEigenform`, whose two archimedean corollaries
(`norm_coeff_le_two_mul_sqrt_of_not_dvd`, `norm_coeff_le_sqrt_of_dvd`) and whose
`‖aₙ‖ ≤ 2n` consequence were all PROVEN and would have deleted a hundred lines of
the new proof. **Grep the file you are editing for the theory you are about to
state, by CONTENT and not by name** — "Ramanujan", "Deligne" and `2 * Real.sqrt`
each found it in seconds, and none of them was tried until after the commit.
Redoing it dropped the frontier by one instead of leaving it flat.

**The check costs one numerical experiment and belongs before any theory-building.**
Take the leaf's inequality, replace every unknown by its a-priori bound, and compute
the extremal value. Here the true minimum over the Deligne box is `+0.108` at `65`,
`+0.073` at `91`, `−0.0044` at `169` — so the same audit was RIGHT at `169` and
WRONG at the other two, and nothing but the arithmetic separates the cases. Do not
report "this needs theory X" without having priced the bounds you already have.

**Corollary: a failed TERMWISE bound is not a failed bound.** Term by term,
`|aₙ| ≤ d(n)√n` loses at `65` (`0.502` of negative mass against `0.459`). The whole
margin lives in the correlations the bound leaves standing — `a₄ = a₂² − 2 ≥ −2`
however extreme `a₂` gets, where termwise allows `−6`; and `a₆ = a₂a₃`, `a₁₀ = a₂a₅`,
`a₁₂ = a₄a₃` move WITH their factors. Grouping the sum to keep them turns a
six-variable box into a one-variable cubic. Look for the algebraic relations among
the unknowns before concluding the estimate is out of reach.

**Two Lean lessons from the same proof.** State a bound as `r² ≤ 4p` rather than
`|r| ≤ 2√p` when the consumer is `nlinarith` over rational intervals — same content,
no `Real.sqrt` anywhere. And **`nlinarith` times out in a context holding degree-12
polynomial hypotheses**: it preprocesses every hypothesis in scope and squares them
against each other. Every numeric side step had to move out into small private
helpers called with explicit arguments, leaving only `linarith` and explicit
`mul_le_mul_of_nonneg_right` terms inside the main proof.

