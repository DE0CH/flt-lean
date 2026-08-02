---
name: flt-prescribed-repair-names-the-wrong-declaration
description: "A docstring that prescribes \"add this conjunct to theorem X\" is usually right about the mathematics and wrong about X's declaration order and about whether X is the leaf"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: aeae1001-6478-4e83-8e67-a1929727137f
  modified: 2026-08-02T14:43:13.321Z
---

`exists_cuspLocus_atkinLehnerSwap` (X0.lean) carried a docstring naming its own
repair — carry the Atkin–Lehner action as a further conjunct of
`exists_cuspResidueIndexing` rather than re-asserting the cusp indexing — and the
repair was correct and worth a genuine −1 on the frontier. It was blocked twice
over by facts the docstring did not check: `IsAtkinLehner` was declared 41 000
lines BELOW the theorem the conjunct was to go on, so the conjunct was not
statable; and `exists_cuspResidueIndexing` is itself PROVEN, three wrappers above
the actual leaf, so putting a conjunct there would have added a `sorry` to a
proven theorem.

**Why:** These docstrings are written by whoever CUT the leaf, from the
mathematics, at a moment when the file's layout was someone else's problem. The
mathematical half ages well; the placement half was never checked at all, and
either failure alone makes the prescription unexecutable as written.

**How to apply:** Before starting a prescribed repair, run two `grep -n`s — the
line number of every name the new statement mentions against the line of the
declaration it is to be attached to, and the BODY of that declaration to see
whether it is the leaf or a wrapper. Then chase the wrapper chain down to the
`sorry` and put the conjunct there, forwarding it up through each proven wrapper.
A blocked order is a HOIST, and `flt-hoistcheck.py` prices it in seconds — do not
abandon the repair without measuring it.

See [[flt-leaf-blocked-by-declaration-order]],
[[flt-block-move-off-by-one-swallows-docstring]],
[[flt-leaf-cost-estimates-are-hypotheses]].
