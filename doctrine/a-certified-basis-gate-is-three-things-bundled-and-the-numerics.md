## A "CERTIFIED BASIS" GATE IS THREE THINGS BUNDLED, AND THE NUMERICS ARE PROVABLE TODAY
(2026-08-02, `flt-lean-364`, `norm_sum_range_ge_atkinLehnerMinus_oneSixtyNine` in
`ModularCurve/X0.lean`.)  That leaf's docstring named its own gate correctly — "an
explicit certified basis of `S2(Gamma0(169))^new`" — and three audits had re-verified
the arithmetic behind it.  All of that was right, and the leaf still contained **two
thirds of a proof nobody needs a modular-forms expert for**:
* a numerical estimate on twelve terms involving `pi` and `e^{-2 pi/13}`;
* the Hecke algebra reducing `a1 ... a12` to `a2, a3, a5, a7, a11`;
* the certified basis itself.
The first two are now PROVEN (axiom-clean) and the leaf is a statement about the VALUES
of five coefficients, with no weight, no sum and no norm in it.  Count unchanged, 1 to 1.
**So: when a leaf is gated on a citation, list what ELSE is inside it before reporting it
blocked.**  A leaf whose conclusion mixes a citation with an inequality over `Real.exp` is
two leaves, and the analytic one is ordinary work.
### Interval arithmetic in Lean is cheap if you bracket the TRANSCENDENTALS ONCE
`Real.exp_bound` (`|x| <= 1`, Taylor with an explicit remainder) and `Real.pi_gt_d6` /
`Real.pi_lt_d6` are all the pin needs.  The shape that worked, ~200 lines for twelve
weights:
1. rewrite the weight as `r^(m) / (u * m)` with `u = 2*pi/13` and `r = exp(-u)` — so
   there are exactly TWO transcendental quantities in the whole development;
2. bracket `u` from the `pi` bounds; bracket each power `u^k` separately with
   `pow_le_pow_left0` and hand the six as separate hypotheses to `linarith`.  **Do not
   give a degree-6 polynomial in a variable pinned to `2e-7` to `nlinarith`**;
3. bracket `r` with `Real.exp_bound` at `n = 7` (remainder `< 1.4e-6`);
4. every weight bracket is then `pow_le_pow_left0` plus `div_le_div0` plus one
   `norm_num`, and the analysis is paid once instead of twelve times.
**THE TRAP THAT COST TWO ROUNDS, and it will cost them again: derived constants must be
recomputed from the ROUNDED rationals you actually write in Lean.**  I computed the
brackets for `u^k` and for the weights from the exact `2*3.141592/13`, then wrote the
outward-rounded `4833218/10^7` into the statement — which is SMALLER, so every
`norm_num` side goal came back `unsolved goals |- False`.  Generate the Lean numerals and
the constants derived from them in ONE script, from the same `Fraction`s, and assert each
enclosure in Python before Lean ever sees it.  Done that way the numeric lemmas compiled
first try.
### PARAMETERISE A COEFFICIENT FAMILY BY `a_2` ITSELF, AND USE ITS RELATION TO REDUCE
Two moves that turn a table of algebraic numbers into three lines of Lean:
* **Re-root the minimal polynomial at the coefficient.**  Tables give the level-`169`
  minus orbit as `a2 = 1 - y` with `y^3 = y^2 + 2y - 1`.  Substituting `t = a2` makes the
  relation `t^3 = 2t^2 + t - 1` and every listed coefficient a POLYNOMIAL in `t`
  (`a3 = 2t - t^2`, `a5 = 2 + 2t - t^2`, `a7 = 3 - t^2`, `a11 = t^2 - 2t + 2`).  The leaf
  statement then mentions one real variable and no field extension.
* **Use the relation to REDUCE the goal, never to isolate the roots.**  The head sum has
  degree `4` in `t`; one `linear_combination <quotient> * ht` against the cubic rewrites
  it as `D0 + D1 t + D2 t^2`.  After that the ONLY thing needed about `t` is
  `-0.85 <= t <= 3`, and that follows from the cubic by two `nlinarith` calls
  (`by_contra`; `p` is monotone outside its critical points).  No root isolation, no
  Positivstellensatz certificate, no irrational constant anywhere.  Get the quotient from
  `sympy.div`; deriving it by hand is where an error will hide — mine dropped one term
  and the numeric check caught it.
With `D2 < 0` the quadratic is CONCAVE, so its minimum on the interval is at an endpoint
and `mul_nonneg` of the two endpoint slacks is the whole certificate.  Supply it as an
`nlinarith` hint; it does not find the product itself.
### Two smaller things
* **`linarith` is useless over `C`** — no order.  The Hecke relations
  (`a4 + 2 = a2^2` and friends, straight out of the `hecke` field) close with
  `linear_combination e8 + a 2 * e4`, and the failure mode is a bare
  `linarith failed to find a contradiction` on a goal that is a ring identity.
* **Verify the recut with the two-line receipt.**  `git diff | grep -E "^[+-] *sorry *$"`
  printing exactly one `+` and one `-` is the mechanical form of "count unchanged", and
  `#print axioms` on each discharged half — run from a SCRATCH that imports the module,
  which works at this pin — is what shows the numerics really are `[propext,
  Classical.choice, Quot.sound]` and that the surviving `sorryAx` enters only through the
  named leaf.
