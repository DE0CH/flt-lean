## VERIFY IN THE REAL IMPORT CONTEXT WITHOUT PAYING FOR IT: BUILD ONCE, THEN SCRATCH OFF THE OLEAN
(2026-07-31, `flt-lean-273`.) The scratch-module rule says develop against a small import set.
That leaves one gap it does not close: a proof that compiles against `Mathlib` alone can still
fail in the target file over namespaces, `open`s, and which of two `SpecQ`s is in scope. Those
are exactly the errors that cost a 25-minute round trip to discover.
There is a cheap way to close it, and it exploits the very thing CLAUDE.md warns about
elsewhere — **`lake env lean` does not rebuild imports.**
1. Build the target module ONCE, before editing it. (This also verifies the base you inherited,
   which is worth doing anyway in the release window.)
2. Edit the target module freely. The `.olean` is now stale, and that is the point.
3. Put the new declarations in a scratch that `public import`s the target module, with the
   colliding names suffixed. `lake env lean` loads the STALE olean — which has every name the
   new code refers to, since the new code refers to the file as it was — and elaborates the
   new declarations in the real namespace with the real `open`s.
Measured here: **8 seconds** per iteration against ~25 minutes for the file. It found three
context faults a `Mathlib`-only scratch could not have (`RelPoint` and `SpecQ` live in
`Fermat`, the declarations live in `MazurIsogenyPrimeJ` and NOT in `Fermat.MazurIsogenyPrimeJ`).
Then delete the scratch and do the one real build.
The namespace point deserves its own line, because guessing it wrong is silent until you try:
`MazurTorsion.lean`'s declarations are `MazurIsogenyPrimeJ.foo`, not `Fermat.MazurIsogenyPrimeJ.foo`,
even though their bodies name `Fermat.SpecQ`. To find out rather than guess, `run_cmd` over
`(← getEnv).constants` filtering on a name you already know.
