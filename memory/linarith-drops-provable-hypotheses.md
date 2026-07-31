---
name: linarith-drops-provable-hypotheses
description: linarith's norm_num preprocessing DISCHARGES a hypothesis it can prove and drops it — for Real.sqrt of a perfect square this removes the only bound on the atom and the goal becomes unprovable
metadata:
  type: reference
---

`linarith` failed on `b4 ≤ 3 * √4`, `√4 < 2.00001`, `6.00003 < b4 ⊢ False` while
the same shape over `√2` closed.  Both certificates are linear and exact.  The
cause: `√4` is a perfect square, `norm_num` proves `√4 < 2.00001` outright, so
linarith's preprocessing discharges that hypothesis and DROPS it — leaving `√4`
an unbounded atom in the remaining one.

Repair: supply the VALUE. `Real.sqrt 4 = 2` by
`rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)`, rewritten
into the hypothesis; the bound is then unused.

**The general method matters more.** A `linarith failed` whose hypotheses print
correctly is either an ATOM MISMATCH or a PREPROCESSING effect, and the message
does not distinguish them.  Reproduce the goal in a mathlib-only file with the
atoms written once: if it still fails the cause is preprocessing; if it closes the
cause is atoms.  One minute, and it works when the real module has no olean.

Related: [[flt-two-abbrev-wrappers-one-leaf]] (printed-identical, not-equal terms).
