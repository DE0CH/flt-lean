## AN EXPLICIT BINDER OF CLASS TYPE IS A LOCAL INSTANCE — load-bearing while invisible, and the only check is DELETION
(Same leaf.)  `(hS : Nontrivial (CuspForm (Gamma0GL N) 2))` is an ORDINARY
explicit binder, not `[...]`.  Lean 4 nevertheless collects every local
hypothesis of class type as a local instance, so `hS` is consumed by
`Module.finrank_pos` and **never appears by name anywhere in the proof.**
That combination is nasty in both directions and neither is caught by a linter:
* reading the proof body suggests the hypothesis is dead, so it invites deletion
  — and here deleting it yields `0 < N → 1 ≤ x0Genus N`, which is FALSE
  (`x0Genus 1 = 0`);
* `unusedVariables` does NOT flag it, because it genuinely is used.  So the
  linter's silence is not evidence of load-bearing either way.
**The check is to delete the binder and re-run the identical proof.**  It must
fail, and the failure is informative: here `failed to synthesize Nontrivial
(CuspForm (Gamma0GL N) 2)`.  That is a two-minute control in a scratch and it is
what converts "the hypothesis is presumably needed" into a fact.  Record the
control in the docstring — it is the non-vacuity argument, and the next reader
cannot re-derive it from the proof text.
Rider, and it is cheap: **when a faithfulness paragraph asserts numeric witnesses,
`decide` them.**  Both of this cluster's — `x0Genus 1 = 0` (so `hS` is
load-bearing) and `x0Genus 0 = 1` (so `hN` is not excluded by `hS`) — are
`decide`-computable in seconds, and confirming them is what makes the audit a
measurement rather than a restatement.
