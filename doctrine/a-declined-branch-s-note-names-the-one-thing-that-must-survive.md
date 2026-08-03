## A DECLINED BRANCH'S NOTE NAMES THE ONE THING THAT MUST SURVIVE — READ IT BEFORE DECLINING

(Same release.) `flt-lean-357`'s headline payload was the removal of 249
cross-file duplicates from `MazurTorsion.lean`. By the time it reached the merge
worker that work was **entirely redundant**: the duplicates were gone, and
merger's copy of the file was 519 lines SHORTER than the branch's own
de-duplicated version. Its ArtinConductor, WeilPairingStageB, RelativePicard,
HyperellipticJacobian and X0 hunks were likewise all repairs merger had since
made by another route. Declining the whole Lean payload was right.

**It would also have silently reverted a proof**, and the branch said so, in one
sentence, in its handover:

> THE ONE EXCEPTION, and it must survive or my de-duplication silently reverts a
> proof: my transplant of `X0GenusOne.finrank_cuspForm_eq_one_of_x0Genus_eq_one`

That declaration was `sorry` on merger and had a three-line proof on the branch,
over a theorem 48 000 lines above it in the same file. Nothing in any diff, any
duplicate scan or any frontier count distinguishes it from the 17 000 redundant
lines around it.

**So a decline is not a diff-level decision.** Before `git checkout HEAD -- ` on
a branch's files, read its `to_merger` note for a sentence of the form *"this one
thing must survive"* and check that ONE thing by hand. Branch authors write it
precisely because they can see the merge coming and you cannot see their reason.
And when you decline, say in the commit message what you took and what would
change your mind — an empty-looking payload otherwise reads as the class-six
dropped-merge bug.

Rider on how to make the check cheap: the redundancy verdict itself was one
command per claim rather than a reading of 17 000 lines. `xdup.py`'s qualified
pass for the de-duplication; `grep` for the branch's own canary
(`GaloisRepresentation.globalValuationSubring`, declared once, in the upstream
module); `wc -l` on the three copies of the file. **Price a branch's payload
against the tree with the branch's OWN success criteria, not by reading its
diff.**
