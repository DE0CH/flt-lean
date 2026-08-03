## A LEAF THAT ENUMERATES `N` EXPLICIT CASES UNDER A COST TABLE IS A WORK PARTITION — RECOMPUTE THE TABLE, THEN INTERSECT IT WITH DECLARATION ORDER

(2026-08-02, `flt-lean-258`, `axisRestrict_one_ne_zero_of_mem_kenkuDivisorsAboveEighteen`
in `ModularCurve/X0.lean`: seventeen explicit levels, seven of them closed, `1 → 1`.)

The commonest shape of a numerics leaf here is *"this holds at each of these `N`
explicit values"*, with a docstring table giving, per value, how much arithmetic input
it needs — and a sentence naming which rows are free. **That table is a decomposition
somebody has already designed and not performed.** Do not read it as background; read
it as the cut, and split the leaf along it.

Three things decide whether the split is real, in this order:

* **RECOMPUTE THE TABLE BEFORE ACTING ON IT.** Thirty lines of Python over the same
  multiplicative majorant reproduced all seventeen of this one's entries to every
  printed digit. That agreement is what licenses using the author's row-by-row verdicts
  without re-deriving each; a disagreement would have been the finding. It also gives
  you the numbers the Lean proof needs (thresholds, per-term bounds, head totals), which
  the docstring's rounded table does not.
* **THEN INTERSECT THE PARTITION WITH LEAN'S DECLARATION ORDER, because the cheapest
  rows by MATHEMATICS need not be the cheapest rows from your POSITION.** This
  docstring's item 2 said `42` and `54` "need exactly the Atkin–Lehner local values the
  sibling leaf already needs — so that input, which is owed once, pays twice". True, and
  unusable: `norm_coeff_le_one_of_sq_not_dvd_of_isNewEigenformAt` is proven ~900 lines
  BELOW the leaf, so those two rows are a RELOCATION before they are a proof and they
  stayed in the residue. The rows that were actually free were item 1's, whose only
  input (`norm_coeff_le_sqrt_of_dvd`) sits above.
* **WHEN A HELPER YOU NEED IS DECLARED BELOW YOU, CHECK WHETHER THE RAW STRUCTURE FIELD
  IT WRAPS IS ABOVE YOU.** The natural tool for `‖b_{pm}‖ ≤ ‖b_p‖·d(m)√m` is
  `norm_coeff_prime_mul_le` — also below. But it is a five-line wrapper on
  `IsWeightTwoEigenform.atkin`, which is a FIELD of a structure defined thousands of
  lines up, and `hb.atkin p hp hpM n hn : b (n * p) = b n * b p` is all four of the
  composite bounds needed. **That kept the whole edit a pure insertion at ONE site** in a
  119 000-line contended file — no hoist, no second edit region, nothing for a merge to
  split. Prefer a two-line use of the field to a one-line use of a wrapper you would
  have to move.

**Report it as `1 → 1` and say what left the leaf**, per the standing RECUT rule; the
receipt is that the comment-stripped `sorry` TOKEN count is unchanged (101 → 101 here)
while the warning set swaps one name for another.

Two smaller things measured on the same run, both reusable for any leaf of this family:

* **A LEVEL-INDEXED FAMILY SPLITS INTO FAR FEWER LEMMAS THAN IT HAS LEVELS, IF YOU GROUP
  BY WHICH PRIMES DIVIDE THE LEVEL AND NOT BY THE LEVEL.** Seven levels became THREE
  lemmas — `2 ∣ M ∧ M ≤ 30` (five levels), `6 ∣ M ∧ M ≤ 36` (one), `21 ∣ M ∧ M ≤ 21`
  (one) — because `x = e^{-2π/√M}` is increasing in `M`, so ONE rational threshold serves
  a whole group, and the coefficient bounds depend only on the prime set. Stating the
  last two by divisibility-plus-bound rather than by `M = 36` / `M = 21` also means no
  numeral ever has to be moved through `Real.sqrt`, which is where the `subst`-and-`rw`
  bookkeeping in the sibling level lemmas goes.
* **PIN AN IMPLICIT NUMERIC ARGUMENT THAT ONLY A LATER `?_` WOULD DETERMINE.** A harness
  `(hhead : ∑ … ≤ H) (hlt : H + rem < 1)` with `H` implicit, applied as
  `refine harness … ?_ (by norm_num)`, runs the `by norm_num` while `H` is still a
  metavariable and fails with a goal that looks like the top-level one. `(H := 0.945)`
  fixes it. Same family as the standing "printed pattern equals printed target" traps:
  the error names the wrong thing.

