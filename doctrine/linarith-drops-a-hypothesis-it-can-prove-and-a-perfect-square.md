## `linarith` DROPS A HYPOTHESIS IT CAN PROVE — AND A PERFECT SQUARE UNDER `Real.sqrt` IS ONE

(2026-07-31, release 32, five errors in `X0.lean` that two previous handovers had
recorded as "genuine arithmetic".)

    example (b4 : ℝ) (h : b4 ≤ 3 * Real.sqrt 4) (s4 : Real.sqrt 4 < 2.00001)
        (a : (600003 : ℝ) / 100000 < b4) : False := by linarith   -- FAILS
    example (b2 : ℝ) (h : b2 ≤ 2 * Real.sqrt 2) (s2 : Real.sqrt 2 < 1.41422)
        (a : (282844 : ℝ) / 100000 < b2) : False := by linarith   -- succeeds

Both certificates are linear and exact (`3 · 2.00001 = 6.00003` on the nose, and
`2 · 1.41422 = 2.82844`).  The difference is that **`√4` is a perfect square, so
`norm_num` can decide `√4 < 2.00001` on its own** — `example : Real.sqrt 4 <
2.00001 := by norm_num` closes — and `linarith`'s own `norm_num` preprocessing
therefore DISCHARGES that hypothesis and DROPS it.  What is left is `b4 ≤ 3 · √4`
with `√4` an unbounded atom, and there is no certificate at all.

**The repair is to give the VALUE, not a bound**: `Real.sqrt 4 = 2` by
`rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)`, rewritten
into the hypothesis.  The bound is then not needed and the unused-variable linter
says so.  Expect this wherever a table of numeric square-root bounds is generated
uniformly over a range: the perfect squares in the range are the rows that fail,
and only those.

**THE METHOD IS WORTH MORE THAN THE FACT, because it separates two failures that
look identical.** A `linarith failed` on a goal whose hypotheses print correctly
is either (a) an atom mismatch — the standing "printed pattern equals printed
target" trap — or (b) a preprocessing effect like this one, where the atoms are
fine and a hypothesis is gone.  Nothing in the error message distinguishes them,
and I spent an hour on (a) before testing.  **Reproduce the failing goal in a
mathlib-only file, with the atoms written once so they are guaranteed shared.** If
it still fails, the cause is (b) and the hypotheses are in front of you; if it
closes, the cause is (a) and you need `set_option pp.explicit true` on the real
goal.  The probe costs one minute against a 13-minute elaboration of an
118 000-line file, and it can be run when the real file has no olean and no
scratch loop is available at all — which is exactly the situation a red giant
module puts you in.

