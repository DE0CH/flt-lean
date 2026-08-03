## WIRE A CONSUMERLESS `Fermat/FLT/Mathlib/...` MODULE INTO `Fermat.lean`, NOT INTO A CONSUMER

(2026-08-01, `flt-lean-64`, creating `Mathlib/AlgebraicGeometry/SpreadOutOverZ.lean`.)
CLAUDE.md's FOURTH invisibility class says a module unreachable from `Fermat.lean` is never
compiled, so its `sorry`s are invisible and it can rot silently. It does not say WHERE to
wire one in, and the natural instinct — import it from the module that will eventually
consume it — is the expensive and conflict-prone answer when, as is usual for a
mathlib-facing module cut ahead of its consumer, that consumer is `X0.lean` or another
contended giant you were explicitly told not to edit.

**`Fermat.lean` IS AN IMPORT INDEX — 24 lines, nothing but `import` — and several
`Fermat.FLT.Mathlib.*` modules are already wired in there and nowhere else**
(`RingTheory.GradedAlgebra.Quotient`, `RingTheory.RegularLocalNormal`,
`AlgebraicGeometry.EllipticCurve.ProjectiveModel`). It is the root, so **nothing imports
it**: adding a line costs re-elaborating one 33-line file and rebuilds nothing downstream,
where adding the same line to `NeronModel.lean` would have invalidated its 17-module
downstream cone. And it cannot collide with an owner, because the root has none.

Three checks before you add the line, all cheap:

* **name collisions tree-wide**, since a mathlib-facing module usually lands in the
  `AlgebraicGeometry` (or `RingTheory`) namespace beside thousands of existing names —
  `grep -rl "\bYourName\b"` over `Fermat/` and over `.lake/packages/mathlib/Mathlib/`, one
  pass per declaration. Cross-file duplicates are only an error once some module sees both,
  which is exactly what wiring in arranges;
* **the module-system header**: a non-`module` file may import a `module` one (the root
  already does), so the `module` / `public import` / `@[expose] public section` header is
  right and is not what blocks the edge;
* **say in the comment WHY it is wired at the root** and who the intended consumer is, or
  the next reader will "tidy" the import away.

**And then run the release build's own green test, which is NOT the usual one.**
`Fermat.lean` ends with `#assert_no_sorry fermat_last_theorem`, so a whole-project build
ALWAYS ends `EXIT=1` and NEVER prints `Build completed successfully`. The doctrine's
positive-terminator rule is right for a MODULE build and gives a false red here. The green
test for the root build is negative and has four parts:

    grep -q '^EXIT=1' $LOG                        # expected: the gate fires
    grep -q 'SORRY GATE FAILED' $LOG              # and it IS the gate
    grep -E 'error' $LOG | grep -v 'declaration uses' \
      | grep -vE 'SORRY GATE FAILED|Lean exited with code 1|^error: build failed' | wc -l   # == 0
    grep -oE '\[[0-9]+/[0-9]+\]' $LOG | tail -1   # must reach the FULL job count

The last line is not decoration: the first three are all satisfied by a build that died
early, because a build that never reached module 5000 has no errors in modules 5000–5704
either. **"No errors" and "no errors yet" are the same string.**

