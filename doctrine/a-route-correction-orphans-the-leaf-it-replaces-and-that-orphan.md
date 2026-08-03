## A ROUTE CORRECTION ORPHANS THE LEAF IT REPLACES — AND THAT ORPHAN IS USUALLY THE MISSING HALF OF YOUR OWN ASSEMBLY
(2026-08-02, `flt-lean-384`, on `hasDoubleCoverOfAffineLine_of_constSmul_sectionIdeal`
in `ModularCurve/X0.lean`.  Closed the target outright, with no mathematics, in one
scratch round.)
This file already records that a DELETE × REFACTOR merge orphans a leaf, and that a
consumerless leaf is dead work.  There is a third way to manufacture one, it needs no
merge and no second agent, and the orphan it produces is *valuable* rather than dead:
> An author re-cuts a node — a "ROUTE CORRECTION" — and states the new leaf.  The
> OLD cut's residual leaf is left in the file, still `sorry`, still counted, and now
> with **no consumer**, because the parent was re-pointed at the new leaf.
`exists_toAffineLine_of_iso_sectionIdeal` was exactly that: cut on 2026-07-31, orphaned
the same day by the correction that introduced my target, and sitting one screen BELOW
it.  A comment-stripped scan of the whole tree returned **one** occurrence of the name —
its own declaration line.
**The orphan was not junk.  It was the sub-leaf my target needed**, and the only reasons
it could not be used were (a) it was stated over the OLD hypothesis (`_hiso : Nonempty (… ≅ …)`)
rather than the new one (`f`, `e`, `_hf`) and (b) Lean has no forward references and it was
declared below its would-be consumer.  Both are bookkeeping.  Restating it in the new
hypothesis form and moving it ABOVE the target made the target a five-line assembly over
it plus the already-sorry-free `isFinite_toAffineLine_of_isValuativelyFull`.
**So the first grep on any freshly-cut leaf is not for your target's consumers — it is for
a CONSUMERLESS SORRY LEAF IN THE SAME NEIGHBOURHOOD whose conclusion resembles yours.**
The tell is a declaration whose comment-stripped occurrence count is exactly one.  A leaf
cut within the last few days is the likeliest to have one beside it, because that is when
route corrections happen.
Three riders, each of which decided something here:
* **Check DECLARATION ORDER before concluding the orphan is unusable.**  `grep -n` the
  orphan and your target and compare the two line numbers.  "Below me" is not "unavailable"
  — it is "move it", and moving a leaf UP is the safe direction, since a `sorry` body has no
  dependencies to strand.  The only real check is whether anything between the two positions
  consumes it, which for a consumerless orphan is vacuous.
* **Restate rather than reuse, and say the two forms are equivalent IN WRITING.**  Taking
  `_hiso` and re-deriving `f` inside would have handed the next prover back the step the
  route correction had just removed.  The equivalence is one sentence each way
  (`exists_units_functionField_of_iso_sectionIdeal` forwards, `⟨e⟩` backwards) and it is what
  licenses the claim that the old faithfulness audit transfers verbatim.
* **FOLD the orphan's docstring in; do not let the rename eat it.**  The old one carried the
  witness construction, the `IsValuativelyFull` route and a three-part falsity audit that the
  survivor's docstring did not.  A rename that drops that is a silent loss no scan can see.
**Report the accounting, because it is unflattering and would otherwise be overstated.**  The
cluster went from two open leaves to one and NO mathematics was done: the residual obligation
is unchanged, and what was removed is a free-floating declaration plus a phantom frontier slot
that had already drawn one dispatch — mine.  Say "2 → 1, merge/route bookkeeping, no theorem
proved" in the commit, or the delta reads as a theory gap closing.
**And the cheap receipt that this is what happened, not something worse: the comment-stripped
`sorry`-TOKEN count and the build's `declaration uses 'sorry'` WARNING count must move by the
same amount.**  Here both were `101 → 100` on `X0.lean`.  Equal deltas is what rules out an
anonymous inner `sorry` having been swapped in for the named one.
### Corollary found on the way: two docstrings in one cluster can disagree about WHICH points are deleted
The route-correction paragraph said `U = X ∖ {x₁, x₂}`; the audit two declarations away said
`U = X ∖ {y₁, y₂}`.  Both cannot be right — it is a sign convention, fixed by the direction of
the `constSmul` equation — and nothing downstream depends on the answer, since the conclusion
is symmetric in the two divisors (`f⁻¹` witnesses the other one).  **Record such a
disagreement in the leaf's own docstring with the instruction to CORRECT the losing paragraph
rather than reconcile the two**, per this file's standing rule that a 50k-line module's
doctrine is not consistent with itself and the next reader hits whichever paragraph is nearer.
