## AND THE OTHER DIRECTION: A FALSITY AUDIT DOES NOT DESCEND TO THE LEAVES CUT OUT OF IT
(2026-07-31.) The section above says a RESTATEMENT voids an audit. Decomposition has the
mirror failure: the audit gets copied DOWN onto the pieces and nobody re-derives it.
`tsum_coeff_ne_zero_atkinLehnerMinus_oneSixtyNine` and its sibling
`integral_Ioi_one_axisRestrict_ne_zero_atkinLehnerMinus_oneSixtyNine` both carried, verbatim,
**"`hw` MAY NOT BE DROPPED, and the witness is orbit `3`"**. Both were wrong, and the audit is
CORRECT where it was written — one level up, at
`cuspPeriod_ne_zero_atkinLehnerMinus_oneSixtyNine`, where `hw` really is what makes the period
nonzero. **A hypothesis that is load-bearing for a PRODUCT need not be load-bearing for either
FACTOR.** Here the product is `cuspPeriod = (1 − ε)/√N · ∫₁^∞`: at `ε = +1` the period vanishes
because the FIRST factor does, and the integral at orbit `3`'s three embeddings is
`0.927, 1.067, 0.502` — the named counterexample is not one, and the leaf is true for all eight
normalized eigenforms rather than only the five the hypothesis selects.
The leaf's own docstring contained the refutation and drew the opposite conclusion from it: "at
`ε = +1` the period is literally `0` **whatever this integral is**" — which says precisely that
`L(f,1) = 0` constrains nothing about the integral.
So: **when a node is CUT, every audit on it is a HYPOTHESIS about the pieces, not a fact carried
over.** Re-derive each hypothesis against the piece. And when an audit turns out to be inherited
rather than earned, say so in the docstring instead of quietly deleting it — a wrong audit that is
silently removed gets re-derived by the next agent from the same parent.
Corollary, and it cost one line of `gp`: **a leaf whose audit names a counterexample is worth
EVALUATING the counterexample on.** Orbit `3` was named in three docstrings across two files and
nobody had ever computed its value of the quantity actually in the statement.
=======

