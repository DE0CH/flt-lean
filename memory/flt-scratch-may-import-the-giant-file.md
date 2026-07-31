---
name: flt-scratch-may-import-the-giant-file
description: The scratch module should IMPORT the file you are editing, not reproduce a trimmed subset of its imports — 4 s vs 20 min, measured on TateModule.lean
metadata:
  type: project
---

The doctrine's scratch-module rule says "import only what you need", which reads
as an instruction to hand-trim an import list. That is the wrong lever and it
costs time to get right.

**The lever is not the import list — it is whether the file you are EDITING gets
re-elaborated.** Imports are `.olean` loads; the 22 868-line
`Modularity/TateModule.lean` loads in about a second. So the fastest scratch is
the maximal one:

    module
    public import Fermat.FLT.Modularity.TateModule
    @[expose] public section
    universe u
    open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial
    namespace Fermat
    -- new leaves as `sorry`, plus the assembly you are actually writing

Measured 2026-07-31 in `flt-lean-94`: `lake env lean` on that scratch was
**4.2 s** per iteration, against **~20 min** for `lake build` of `TateModule`
itself. Five iterations closed a 100-line proof; one final blocking build of the
real file confirmed it.

Two conditions make it work, and both were needed here:

* the target module's `.olean` must be current — `lake build <Module>` FIRST,
  after `git merge main`, exactly as the doctrine says;
* the scratch must reproduce the target's namespace and `open` context verbatim
  (`namespace Fermat`, the same four `open`s, `open _root_.NumberField in` on
  each declaration), or name resolution differs and the paste back fails.

A bonus: because the scratch imports the target, every helper the target already
proves is available by name with no import archaeology at all. That is what let
the assembly reuse `exists_nsmul_eq_geomFibrePt` and
`exists_pow_mul_not_le_of_isMaximal` without knowing which module defines them.

Delete the scratch before committing. Related: [[flt-cut-at-the-missing-object]].
