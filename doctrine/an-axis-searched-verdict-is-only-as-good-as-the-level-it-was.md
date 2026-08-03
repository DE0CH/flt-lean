## AN "AXIS SEARCHED" VERDICT IS ONLY AS GOOD AS THE LEVEL IT WAS TAKEN AT

(2026-07-31. Two leaves in `ModularCurve/X0.lean` closed the same afternoon, each
against an audit that had explicitly ruled its route out, and each audit's
FACTUAL clauses were true.)

Docstrings in this development carry `AXES SEARCHED` / `WHY THIS IS NOT A
COROLLARY OF X` verdicts, and they are load-bearing: the next owner reads them
and does not re-open what they close. Both failures below were failures of
INFERENCE from a correct observation, and both are cheap to detect.

**Pattern 1 — absence of a lemma about the OBJECT is not absence of the
IDENTITY.** `trace_heckeOpSq_x0OneSixtyNine` recorded that the banked-charpoly
route was closed off: "Mathlib at this pin has `Matrix.trace_eq_sum_roots_charpoly`
(first power sum only) with no counterpart for the second, so the charpoly route
would cost a triangularisation argument." Both clauses TRUE. But Newton's second
identity `Tr(M²) = (Tr M)² − 2e₂` does not need eigenvalues at all:
`Matrix.charpoly_coeff_eq_sum_minors` (which IS in the pin) gives `coeff (n−2)`
as the sum of the `2×2` principal minors, that sum is `∑_{i<j}(MᵢᵢMⱼⱼ − MᵢⱼMⱼᵢ)`,
and doubling it is `(Tr M)² − Tr(M²)` because the summand is symmetric with
vanishing diagonal. Any commutative ring, no splitting, ~120 lines.

The audit had searched for a lemma about the ROOTS and concluded from its
absence that the identity was unreachable. **Before believing "mathlib lacks
this", ask which OTHER presentation of the same quantity the pin does have** —
coefficients vs roots, minors vs eigenvalues, a recursion vs a closed form.

**Pattern 2 — "not a corollary of X" is a claim about X, and X may be an
ASSEMBLY.** `sumSq_isWeilEigenvalues_x0` said, correctly, that `Σ αᵢ²` is not a
function of `Σ αᵢ` and `∏(1 − αᵢ)` once `g ≥ 2`, so it could not be a corollary
of `isWeilEigenvalues_x0_eichlerShimura`. True — and that theorem is itself a
three-line assembly over `isEichlerShimuraTransform_x0`, which supplies the full
PAIRING, and a pairing determines EVERY power sum. The `(sum, product)` form was
a lossy read of a datum still sitting in the file one level down.

**So when a verdict names a theorem as the thing that is insufficient, open that
theorem's PROOF.** If it is `by exact ⟨h.foo, h.bar⟩` over some richer leaf, the
verdict is about the projection, not about what is available. In a development
that decomposes aggressively, yesterday's atomic leaf is today's assembly, and
the docstring recording the old cut does not update itself.

Both repairs cost nothing downstream: the closed leaves rest on leaves that
already existed (`finrank_cuspForm_of_x0HeckeCharpolyTable`,
`charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable`,
`isEichlerShimuraTransform_x0`), so the frontier went down by three with zero
new nodes. **A leaf that closes by re-reading an audit is the cheapest kind of
progress there is; budget a pass over the audit before budgeting a proof.**

