## TWO COMPLEMENTARY FIELDS ADDED TO ONE STRUCTURE: A MERGE KEEPS ONE, AND SPLITS THE OTHER HALF THE OPPOSITE WAY

(2026-07-31, release 32, `ModularCurve/X1.lean`.  Three errors, one root cause, and it
was invisible for six releases.)

The class-7 interface split is usually described as *one edit* whose signature half and
call-site half land on opposite sides of a conflict boundary.  There is a sharper form
that arises when two branches each repair a DIFFERENT refuted `∀ P` theorem by the same
move — hoisting its citation onto the structure as a new field:

* `64651d82` (2026-07-30) added `Gamma1GITPresentation.smoothM`, Katz–Mazur 8.2.1, to
  repair `smoothCurve_A_of_gamma1GITPresentation`;
* `420bd322` (2026-07-31) added `Gamma1GITPresentation.transitiveM`,
  Deligne–Rapoport IV.5.5, to repair
  `transitiveMinimalPrimes_tensorProduct_of_gamma1GITPresentation`.

They are COMPLEMENTARY — different citations, different discharging leaves, disjoint
consumers — and `420bd322` forked before `64651d82`, so its copy of the structure had no
`smoothM`.  The merge took the STRUCTURE BODY from the later branch and lost `smoothM`
from **both** `Gamma1GITPresentation` and `Gamma1Rigidification`, along with the `hsm`
hypothesis of `nonempty_gamma1Rigidification_of_rigidifiedModuli` and its call-site
argument.

**The tell that identifies it in one screen, and it is the useful part: the damage is
SYMMETRIC and the two halves point at each other.**  The three errors were

    X1.lean:1694: `smoothM` is not a field of structure `Gamma1GITPresentation`
    X1.lean:1680: Fields missing: `transitiveM`
    X1.lean:7063: Invalid field `smoothM`

i.e. the STRUCTURE came from the `transitiveM` branch and one CONSTRUCTOR LITERAL came
from the `smoothM` branch — each side of the file is internally consistent with a
different parent.  A single dropped edit cannot produce that pattern; only two rival
copies of one declaration can.  When "X is not a field of S" and "fields missing: Y"
appear in the same module, do NOT start weakening either statement: `git log -S` both
field names, and if the two adding commits are incomparable, the repair is the UNION.

**And the union really is the repair — check it, do not assume it.**  Two fields added
to one structure are complementary iff they cite different theorems, are discharged by
different leaves, and have disjoint consumers.  Here all three held and both discharging
leaves (`smoothOfRelativeDimension_of_gamma1RigidifiedModuli`,
`transitiveOnGeometricComponents_of_gamma1RigidifiedModuli`) were still present and still
open, so restoring `smoothM` opened and closed nothing.  If instead one docstring said it
SUPERSEDES the other, the union would be the duplicated-hypothesis failure that release
24 recorded — the same shape, opposite resolution.  Both docstrings here said "carried
verbatim from `Gamma1Rigidification`", i.e. both were written as additions.

**WHY IT SURVIVED SIX RELEASES, and this is the standing lesson rather than the
instance.**  `X1.lean` is downstream of `X0.lean`; `X0` had been red since release 25;
`lake build` stops at the first red module in a cone.  So `X1` was not "fine", it was
UNSEEN — and merge damage had been accumulating in it, unreported, for six releases,
while every release handover truthfully said "every module except X0 builds".  That
sentence is always a statement about the modules `lake` REACHED.  **Behind a red module,
budget repair work in proportion to how long it has been dark**, and elaborate the
darkened modules directly with `lake env lean` against the previous release's oleans
rather than waiting for the cone.

