---
name: flt-route-note-rerun-is-a-claim-about-a-statement
description: "A route note saying \"re-run construction C with X in place of Y\" is about C's mathematics, not C's Lean statement — read the binder list, the parameter is often already general"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 2ec279d1-f8df-4eb3-8c1e-8a3f863a3266
  modified: 2026-08-02T02:38:28.506Z
---

Route notes in flt-lean routinely read *"the only place the extra clause touches
the existing proof is step `C`; re-run it with `X` in place of `Y`"*. That is a
claim about the MATHEMATICS of `C`, written by whoever cut the leaf while
reasoning about the textbook. It is rarely a claim about the Lean declaration
that was cut out of `C`, and in this tree that declaration is often already
quantified over exactly the parameter you wanted to change.

**Why:** measured 2026-08-02 on `exists_relArtinAuxiliaryNumberField_ray_class`
(`ModThree.lean`). Its note priced the relative clause `M E₀ ∩ F(ζ_m) = F` as a
re-run of Childress 2.3–2.7 with `M E₀` in place of `M` — a new arithmetic leaf.
But `exists_badPrimes_mul_muFixer_eq_top_ray_class` is stated for an **arbitrary
open subgroup** `H ≤ Γ F`, and `ker χ ⊓ H₀` is one. Instantiating there IS the
relative clause. The whole leaf became glue, frontier `14 → 13`, no new leaf, no
new axiom dependency — and the "unramified in `M E₀`" side condition is what that
theorem's own proof arranges internally for whatever subgroup it is handed.

**How to apply:** when a note names a step to re-run, `grep -n "^theorem <that
name>" -A15` and read the binder list BEFORE costing anything. If the thing you
wanted to vary is already a binder, the re-run is an instantiation. The
generality was usually introduced for an unrelated reason (here: to serve at `F`
and at `ℚ` both) so its docstring will not mention your case and no keyword
search finds it — look for a lemma quantified over ONE object and try it at your
COMBINATION (`ker χ ⊓ H₀`) before hunting for a lemma about the combination.

Corollary on how to read such notes: a route note's claims about the SHAPE of the
argument are usually sound, and its claims about the COST of a named Lean step
are the perishable half. The same note's other half — *"`w ∈ H₀` is the single
fact to add, everything else is verbatim"* — was exactly right, and the missing
piece was a one-line `Subgroup.subset_closure` exporting `w ∈ H` alongside the
already-exported `f ∈ H`. Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].
