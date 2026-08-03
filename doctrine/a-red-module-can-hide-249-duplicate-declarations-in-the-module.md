## A RED MODULE CAN HIDE 249 DUPLICATE DECLARATIONS IN THE MODULE BEHIND IT, FOR THREE RELEASES

(2026-07-31, release 28, found by running `tools/merge/xdup.py` and DIFFERENCING it
against the last GREEN release rather than against the previous merge base.)

`FreyCurve/MazurTorsion.lean` has not been compiled since release 25.  It is
downstream of `ModularCurve/X0.lean`, X0 has been red since release 25, and
`lake build` stops at the first red module in a cone — the SEVENTH invisibility
class this file already documents.  What that class does not say is how much can
accumulate behind one red module, and the answer here is **249 hard
`has already been declared` errors**:

    165   FreyCurve/IsogenySignature.lean  <->  FreyCurve/MazurTorsion.lean
     84   ModularCurve/X0.lean             <->  FreyCurve/MazurTorsion.lean

with `MazurTorsion.lean` `public import`ing both.  Every one is a build-stopping
error, and not one of them is visible to `lake build`, to the
`declaration uses 'sorry'` warning set, or to any frontier scan.

**The cause is a hoist that never deleted its source, and `git` proves it in two
commands.** At the last green release `7080929d`, `IsogenySignature.lean` declared
`GaloisRepresentation.globalValuationSubring` ZERO times, `MazurTorsion.lean`
declared it, and `MazurTorsion` did not import `IsogenySignature` at all.  Now both
declare it and the import is there.  `semmerge.py` propagates a branch's ADDITIONS
and never its DELETIONS, so no merge could have removed the originals.

Three things to carry:

* **Difference `xdup.py` against the last GREEN release, not against the previous
  merge base.** Release 27 differenced against its own base, got EMPTY, and
  concluded the tree was clean — correctly, and uselessly, because the duplicates
  predate that base.  A check whose baseline is itself broken certifies the
  breakage.  The green release is the only baseline that means anything.
* **A module nothing has built is not "probably fine".** Behind a red module, ALL
  the ordinary evidence is silent by construction, so the prior should be that it
  is broken in proportion to how long it has been dark and how much has merged.
  Elaborate it directly with the LEAN_PATH shim rather than waiting for the cone.
* **When you HOIST a block, the deletion of the source is part of the hoist**, and
  it is the half a declaration-level merge cannot carry for you.  Say in the branch
  report which declarations you removed from where; that note is the only thing
  standing between the hoist and this.

