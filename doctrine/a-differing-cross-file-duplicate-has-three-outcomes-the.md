## A DIFFERING CROSS-FILE DUPLICATE HAS THREE OUTCOMES — "the downstream copy is PROVEN" decides nothing
(2026-08-02, release 34, merge worker.)  `xdup.py` reported **62 qualified
duplicate pairs against a baseline of 0** — every one a hard
`environment already contains`, all of them the standing
semmerge-propagates-additions-never-deletions failure after a hoist.
`dedup_cross.py` deleted the 56 whose bodies AGREE and left **3 differing**
pairs for a decision.  The three needed three different answers, so the rule
this file already gives ("delete the DOWNSTREAM copy, body-compare first") is
necessary and not sufficient — body-comparison tells you a decision is owed and
not what it is.
**Classify a differing pair by sorry-status AND by what the downstream proof
RESTS ON:**
1. **downstream SORRIED, upstream PROVEN** — delete downstream.  Pure win, and
   it removes a sorry as well as a duplicate.
2. **downstream PROVEN, upstream SORRIED, downstream proof DELEGATES upstream** —
   delete downstream; **nothing is lost.**  The check is one walk of the
   upstream call graph: here `exists_inj_point_x0Model_of_relPointEquiv` is
   proven in `MazurTorsion` by `obtain … := exists_x0Model N hN h`, and in `X0`
   `exists_x0Model` transitively CONSUMES that very leaf — so the leaf cannot be
   proven that way upstream (circular) and the downstream copy is a delegation
   bottoming out in the upstream sorry.  That is
   [[flt-downstream-rival-cut-is-consumerless-by-construction]] met from the
   merge side.
3. **downstream PROVEN, upstream SORRIED, downstream "proof" is a RECUT over
   another sorry** — deleting it loses real design work.  **TRANSPLANT the whole
   recut upstream** — the helper leaf WITH its docstring, and the proof over it —
   in place of the upstream sorried copy, then delete downstream as an identical
   pair.  Here that was flt-lean-15's *the two odd-class cubics are one cubic
   under `(m,n,r) ↦ (4r,−2m,−n)`*, whose `_one` helper is itself a `sorry`: so
   MazurTorsion's copy was never a proof, it was a strictly smaller residual
   leaf, and the tree's sorry count is unchanged either way while the surviving
   leaf is the better one.
**The cheap discriminator between 2 and 3: grep the downstream proof's cited
names for a `sorry`.**  All-proven-and-upstream ⟹ case 1 or 2 (decide by whether
the cited theorem consumes your leaf).  Any cited name sorried ⟹ case 3,
transplant.
**And delete the UNION of the ranges, once.**  Deleting four blocks in reverse
order looked safe and was not: two of them shared a boundary line, so the second
deletion shifted the first and ate the NEXT docstring's `/--` opener, leaving an
unmatched `-/` 40 lines later.  `blocks.blocks` can also start a block INSIDE a
preceding docstring when one docstring documents two declarations — which is
what happened, and the file's own `/-!` note said so ("the two consumers below").
Compute each block's true bounds from the nearest preceding `/--`, take the
UNION as a set of line numbers, and delete in one pass.  Then re-run
`parsecheck.py` on the file: this class of self-inflicted wound is exactly what
it is for.
### A CHECKER THAT OVER-REPORTS COSTS A RELEASE TOO — verify the construct before repairing the source
Same release.  `parsecheck.py` reported a hard wound at `ModThree.lean:61359`,
a bare `by` in column 0.  `:=` at the end of one line and `by` at column 0 on
the next is **legal Lean 4** — three-line scratch, `EXIT=0` — so the tree was
correct and the checker was not.  This file says at length that a scan which
UNDER-reports is worse than none because it certifies; the mirror is just as
expensive, because the reflex is to edit the source and the source is right.
**Before repairing anything a structural checker calls broken, elaborate the
construct in isolation.**  One scratch, seconds.  Then fix the CHECKER and
RE-CALIBRATE against a known-green revision (`parsecheck.py --git <released sha>`
must still report zero) — and key the exemption as tightly as the legality
condition, here on the previous code line ending in `:=`/`=>`, so that a `by`
NOT preceded by one is still reported.  Adding `by` to the whitelist would have
silenced a real wound for ever.

