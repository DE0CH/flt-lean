## VERIFY BY EXTRACTION when the file's own cone will not build

(2026-07-31, `flt-lean-367`.) The scratch-module rule says "develop against a throwaway
module that imports only what you need". It has a stronger form that also works when the
target file **cannot be built at all** because something unrelated in its 161-import cone
is red: **copy the SECTION you are editing, verbatim, into a standalone file that imports
one module far below the damage, and elaborate that.**

Here `Fermat/FLT/Modularity/Interface.lean` is 90k lines and its cone was red in
`TateModule.lean` and `HyperellipticJacobian.lean`. Lines 57385–59018 — the whole
`section X0GoodReduction` — were copied into a file whose entire preamble is

    import Fermat.FLT.ModularCurve.X0
    import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveGenus
    namespace GaloisRepresentation.Modularity

and it elaborated with `EXIT=0`, zero errors, and exactly the intended `sorry` warnings.
Iteration cost went from a 20–35 minute failing `lake build` to **~4 minutes**.

Three things make it work, and all three are checkable:

* **Extract from the `section` line**, so the section's own `open`s and `variable`s come
  with it. Mis-scoping is otherwise the first error you get and it looks like a real one.
* **A section that uses no file-local declaration from outside itself extracts exactly.**
  For this one that was already known (`~/.flt-loop/FINDINGS-flt-lean-358-zeta-duplication.md`
  established it by a name-by-name scan), and a clean elaboration re-confirms it: any
  outside dependency shows up immediately as `Unknown identifier`. A first attempt that
  over-extracted by 1800 lines produced exactly nine such errors, all in the part that did
  reach outside — so the errors TELL YOU where to truncate.
* **The residual risk is name collision only.** Grep every new name tree-wide before
  committing; nothing else about the rest of the file can be affected by an addition.

One trap. An import that the real file gets TRANSITIVELY may be missing in the extraction
if the intermediate `.olean` is stale — `X0.olean` here was seeded from before
`CurveGenus.lean` existed, so `IsDivisorOn` was `Unknown identifier` in the extraction while
being perfectly in scope in `Interface.lean` itself. **Add the import directly rather than
concluding the name is unavailable**, and do not "fix" the real file on that evidence.

