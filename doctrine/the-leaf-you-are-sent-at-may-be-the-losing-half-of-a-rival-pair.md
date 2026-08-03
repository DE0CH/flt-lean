## THE LEAF YOU ARE SENT AT MAY BE THE LOSING HALF OF A RIVAL PAIR — READ THE CONSUMER'S PROOF BODY FIRST
(2026-08-02, `flt-lean-83`, `MazurTorsion.lean`. Cost: nothing, because the check ran
early; it would have cost the whole run and a construction of complex multiplication
had it not.)
The rival-cut sections above are written for the MERGE WORKER, at the moment two
branches collide. This is the same defect seen from the PROVER's chair, and it has a
different tell and a different first action.
`exists_isogenyCurve_classNumberOne` had two cuts, both open, both landed 2026-07-30:
`exists_kernelPolynomial_classNumberOne` (explicit `IsKernelPolynomial` certificates)
and `exists_cmEndomorphism_classNumberOne` (a square root of `[−p]` in `End(E_ℚ̄)`).
The consumer's proof kept the CM one, so the kernel-polynomial leaf had **zero
consumers** — and the queue dispatched an agent at the CM one, whose own docstring
correctly says the theory it needs exists nowhere.
**Every instrument reports this as two units of honest open work.** Both emit a
truthful `declaration uses 'sorry'`; both pass the three-part ownership test; the two
statements share **no identifier**, so `dupstmt.py` and `xdup.py` cannot pair them, and
`own.py`/`leafstat.py` are correct and useless. The only artefact that knows is the
CONSUMER'S PROOF BODY, which names exactly one of them.
**So the prover's first action, before reading the target at all, is one `grep`:**
    grep -n '<your target>' <the file>          # who cites it, in CODE not prose
    # then open the CONSUMER and read its `by` block: which leaf does it actually call?
    # then scan the consumer's NEIGHBOURS for a second leaf with the same conclusion
A leaf whose only occurrence is its own declaration is dead; a leaf whose consumer is
proven over *something else* is the losing half of a rival pair. Neither is a proof
task.
**The tie-break when neither statement implies the other is DISCHARGE COST, and it is
evidenced rather than argued: count the in-tree PRECEDENTS.** Here the kernel-polynomial
route had two (`GenusOneKernelPolynomials.lean` at `p ∈ {11,17,19}`,
`ThirtySevenKernelPolynomials.lean` at `p = 37`) plus a proven general bridge
(`WeierstrassCurve.exists_point_of_isKernelPolynomial`), so the re-point was a two-line
assembly copied verbatim from the sibling 70 lines above — **8 seconds in a scratch, first
try**. The CM route had none. "Which cut is mathematically deeper" is the wrong question;
the deeper one was the one that could not be finished.
**Deleting the loser is part of the job, not tidying.** Re-pointing the consumer orphans
the loser's whole formal block — here three PROVEN declarations whose only consumer was
that proof — and free-floating code is banned. Delete it, quote
`git show <commit>^:<path>` in the survivor's docstring, name the declarations that are
reusable, and say in the commit that **no mathematics was done**: a `−1` from merge
repair is indistinguishable from a closed theory gap unless you say so.
**Two receipts worth taking, both one command.** The `declaration uses 'sorry'` warning
set AND the comment-stripped `sorry` TOKEN count must move by the same amount (`37 → 36`
both ways here) — equal deltas is what rules out an anonymous inner sorry having been
swapped in. And run `parsecheck.py` on the file after any large block deletion; a
240-line cut can leave a docstring adjacent to a docstring, which is a parse error
thousands of lines away.
### Corollary: a leaf that demands SEVERAL levels at once cannot be closed by one agent
The surviving leaf asks for certificates at `p = 43, 67, 163` in one statement, and its
own docstring says a successor "who cannot make that level fit should cut the leaf by
LEVEL rather than silently produce two of three". Under the loop that is not advice, it
is a precondition: the dispatcher sends ONE agent per leaf, so a leaf no single run can
finish is never closed however tractable each part is. **When you meet a conjunctive
leaf whose parts differ by an order of magnitude in cost, cutting it by part is the
work** — count going up is the point, not a regression.
And **price the parts before assuming the smallest is first.** `IsKernelPolynomial`'s
`generates` field asks that `⟨m, −1⟩ = (ℤ/p)ˣ`, and `gen37.py` hardcodes `m = 2`.
Measured: `ord(2) = 14` of `42` at **`p = 43`**, so `m = 2` FAILS there and the generator
needs extending (to `m = 3`); `2` is a primitive root at both `p = 67` and `p = 163`, so
the existing generator applies unchanged. The level that looks cheapest — smallest
degree, smallest coefficients — is the only one of the three that needs a tooling change.
