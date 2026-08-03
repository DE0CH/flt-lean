## A RE-CUT ORPHANS THE LOSER *IN ONE FILE, WITH NO MERGE INVOLVED* — and the parent's docstring goes on naming it
(2026-08-02, `flt-lean-264`, `ModularCurve/X0.lean`.  Frontier −1, no mathematics
done, and the leaf had been dead for two days.)
The duplicate-cut sections above are all about two BRANCHES cutting one node and a
merge landing both.  The same orphan is produced by **one author re-cutting one node
in one file on one day**, and then it is not a merge defect at all — it is simply
that a re-cut rewires the parent's PROOF and cannot rewire the parent's DOCSTRING.
`IsRelPicZeroOf.listSum_map_eq_of_listSum_aj_eq` was cut on 2026-07-30 over a leaf
`…_of_listSum_aj_eq_of_compactSpace`, and RE-CUT on 2026-07-31 over the strictly
better `listSum_map_eq_of_relPicEquiv_divisor` (Abel's theorem with `Pic⁰` removed
from the statement) plus a proven bridge.  The re-cut did not delete the loser.  From
then on:
* the old leaf had **exactly one comment-stripped occurrence in the whole tree — its
  own declaration**;
* it emitted `declaration uses 'sorry'`, was counted by every frontier scan, and
  passed every ownership check, so it was a live dispatch target that could never
  move the project;
* the parent's docstring still read *"PROVEN 2026-07-30, over the quasi-compact leaf
  above **and nothing else**"*, and the leaf's own docstring still read *"the general
  statement is PROVEN over this one just below"*.  **Both sentences were true when
  written and neither is checked by anything.**
**The detector is one line and it is already in this file for the merge case; it
applies verbatim with no merge in sight: when a PROVEN declaration's docstring names
the leaf it rests on, `grep` its PROOF BODY for that name.**  A docstring is written
once, at the cut; a re-cut edits the body.  Here the body says
`listSum_map_eq_of_relPicEquiv_divisor` and the docstring says something else, and
that mismatch is the whole finding.
**Then DELETE rather than delegate, but check which it is first.**  The rule recorded
above — do not delete a true audited statement, make it a corollary — assumes the
orphan's statement is not otherwise available.  Check: here the orphan was the live
theorem 30 lines below **plus an unused `[CompactSpace T]`**, i.e. strictly weaker
than something already in the file, so nothing was lost and a proven corollary would
have been free-floating (banned).  When the orphan is strictly weaker than a live
declaration, deletion is the right repair and the only cost is prose.
**And the prose cost is the real work: five docstrings in `X0.lean` and one in
`RelativePicard.lean` named the dead leaf**, including a leaf table, a route note on
its sibling, and the "what the Jacobian still owes" paragraph 23 000 lines away.
`grep` the dead name after deleting and fix every hit — an unrepaired hit is exactly
how the next agent re-cuts it.
