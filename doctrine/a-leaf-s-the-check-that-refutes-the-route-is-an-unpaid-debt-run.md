## A LEAF'S "THE CHECK THAT REFUTES THE ROUTE" IS AN UNPAID DEBT — RUN IT, IT COSTS MINUTES

(2026-07-31.) Leaf docstrings here carry two refuting checks: one for the STATEMENT and one for
the ROUTE. The statement's check gets run — that discipline is well established. **The route's
check is written down and then almost never run**, because it looks like the author's problem
rather than the dispatcher's, and because a route recommendation reads with the same authority as
the falsity audit beside it. It is not the same thing: the audit was verified, the route was
guessed.

`ajMinusTorsion_eq_zero_x0OneTwentyFive` recommended, in bold, "`ℓ = 3` is the cheapest" — reduce
mod `3`, use `neronReduction_injective`, conclude from `[P̄] = [w̄ P̄]` in `J_0(125)(𝔽_3)`. **That
equality is false at `ℓ = 3`**, and finding out cost about ten minutes of PARI plus one moduli
count. `X_0(125)(𝔽_3)` has exactly four points — two rational cusps and two non-cuspidal ones —
and `w_125` SWAPS the non-cuspidal pair, so the class the route wants to be zero is not. Worse, it
fails structurally rather than at `3`: the naive one-prime test needs EVERY non-cuspidal
`𝔽_ℓ`-point to be `w`-fixed, hence to have CM by `ℚ(√−5)`, and nothing arranges that at any `ℓ`.

The leaf itself is fine — still true, vacuously. Only the route was wrong, and a route is exactly
what a successor spends its cycle on.

**Two things made this cheap, and both generalise.**

*Cross-check the count two ways that share no input.* `#X_0(125)(𝔽_3) = 4` came out of
Eichler–Shimura (`tr T_3 = 0`, so `3 + 1 − 0`) and, independently, out of counting moduli (two
`𝔽_3`-rational cusps of the ten, plus the two Frobenius eigen-lines of the single ordinary `j`
admitting a cyclic `125`-subgroup). Agreement between two such counts is what let me trust the
finer structural claim — which point is fixed by `w` — that neither count alone establishes.

*A CM/discriminant argument settles "is this point fixed" without a model of the curve.* The fixed
points of `w_N` are CM points of discriminant `−4N`; reduce that order at `ℓ` and compare with the
`a² − 4ℓ` available to `E/𝔽_ℓ`. Here `ℚ(√−5)` versus `{ℚ(√−2), ℚ(√−11)}` — disjoint, so no fixed
point is `𝔽_3`-rational at all. That is a two-line check and it answers a question that otherwise
looks like it needs divisor arithmetic on a genus-`8` curve.

**So: before dispatching at a leaf whose docstring names a route with a concrete parameter — a
prime, a level, a truncation bound — run the route's own refuting check first.** A negative comes
back as a corrected docstring and a correctly-scoped successor; the alternative is an agent that
discovers it after building the machinery. And when you withdraw a recommendation, DELETE the line
rather than appending a caveat under it: the next reader greps for the prime, not for the
paragraph.

