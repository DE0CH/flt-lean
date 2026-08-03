## A HOIST'S SOURCE AND DESTINATION SIT UNDER DIFFERENT NAMESPACES, SO NO DUPLICATE SCAN SEES THEM — DIFF THE TWO MODULES' NAME SETS DIRECTLY
(2026-08-02, `flt-lean-9`, found while reading `MoretBailly.lean` for the fusion above.)
CLAUDE.md already records "THE COMMONEST THING HIDING BEHIND A RED UPSTREAM: A HOIST THAT
NEVER DELETED ITS SOURCE", with `tools/merge/xdup.py` as the detector. That detector keys on
NAMES, and it has a blind spot that this instance sits squarely in: **a hoist routinely
RENAMES the namespace on the way**, so the qualified names differ and the qualified pass is
silent, while the last-component pass returns ~7000 tree-wide hits and buries the real ones.
`Modularity/MoretBailly.lean` carries two namespaces that are duplicates of
`Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveModelOverField.lean`'s `OverField`:
    ProjChartOverField      52541–53800   1259 lines   39 of 40 decls shared
    ProjConnectedOverField  53871–54953   1082 lines   69 of 71 decls shared
i.e. **~2341 lines of one of the slowest modules in the tree, duplicating a module it
already imports.** `ProjectiveModelOverField.lean` was CREATED on 2026-07-30 by hoisting
exactly these blocks out; the originals were never deleted, and MoretBailly still uses its
local copies (`ProjChartOverField.smoothOfRelativeDimension_projToSpec`,
`ProjChartOverField.projCoord`, …). Nothing reports it: no name collision, no `sorry`, no
error, and both copies compile.
**The check that does work costs seconds and needs no build: take the two modules you
suspect, extract their declaration NAME SETS (last component), and intersect.** Restricting
to ONE PAIR of modules is what removes the noise — a tree-wide last-component scan cannot
be read, and a two-module one is unambiguous. Run it on any module pair where one was
created by hoisting out of the other; the commit that created the new module names its
source.
**Then BODY-COMPARE before deleting, and expect DRIFT.** Here 94 of 108 shared declarations
were byte-identical comment-stripped, and **14 had drifted** — one of them,
`not_X_dvd_polynomial`, at a similarity of 0.396, because the upstream copy carries a
REPAIR the downstream one does not (the `ℚ` argument fails in characteristic two; the fix
evaluates in `F[t]` and reads off a coefficient, and the module header says so). So the
deletion is not mechanical: for each drifted pair somebody must decide which proof survives,
and taking the wrong one silently reverts a fix. A duplicate whose copies have drifted is a
DECISION, not a cleanup — which is exactly why it is worth finding early rather than at a
release.
