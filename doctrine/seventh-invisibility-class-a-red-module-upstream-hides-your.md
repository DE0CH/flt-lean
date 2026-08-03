## SEVENTH invisibility class: a RED module UPSTREAM hides your module's own errors
(2026-07-31, `flt-lean-79`.) `lake build <Module>` builds an import closure and stops
at the first red module in it. So when `X0.lean` is red — as it was on `merger` at
release 27, 101 errors, mid-repair — **`Patching.lean` is never compiled**, and its own
errors are invisible to `lake build`, to the `declaration uses 'sorry'` warning set, and
to every frontier scan. On that day `Patching.lean` had **52 errors of its own** and
nothing in the fleet could see one of them.
This composes with the other six rather than replacing them: the red upstream module has
a named owner and is being worked on, so the situation reads as "someone is on it" when
in fact a second, unowned, unrelated breakage is sitting behind it.
**The workaround is one command and it does not need the upstream repaired.**
`lake env lean` consumes whatever `.olean`s are on disk and does not rebuild imports, so
restore the red module's artifacts from the last good snapshot and elaborate YOUR file
directly:
    cp -p ~/.flt-release-lake/build/lib/lean/Fermat/FLT/ModularCurve/X0.* \
          .lake/build/lib/lean/Fermat/FLT/ModularCurve/
    lake env lean Fermat/FLT/Modularity/Patching.lean
(A failed `lake build` DELETES the stale outputs of the module that failed, which is why
the copy is needed at all — the first symptom is `object file '….olean' does not exist`.)
The snapshot olean is stale, so treat cross-module errors with the usual suspicion; but
errors internal to your file — parse errors, arity mismatches, unknown identifiers
declared in the same file — are real and are yours to fix.
### THE COMMONEST THING HIDING BEHIND A RED UPSTREAM: A HOIST THAT NEVER DELETED ITS SOURCE

(2026-07-31, `flt-lean-337`, and it is the SECOND confirmed instance in two files.)
When a block is hoisted out of a giant module into a new one and the new module is
`public import`ed back, the originals have to be deleted in the same commit. They
often are not — and **`tools/merge/semmerge.py` propagates ADDITIONS and never
DELETIONS**, so no later merge can remove them. Every duplicate is then a hard
`has already been declared`, and behind a red upstream nothing in the fleet can see
it.

Confirmed instances: `FreyCurve/MazurTorsion.lean` against `IsogenySignature.lean`
and `X0.lean` (249 duplicates); `Modularity/Patching.lean` against the hoisted
`Modularity/PatchingWitt.lean` (27, the entire Cohen/Witt coefficient-ring block,
`759621e8`). Both were invisible because `X0.lean` upstream was red.

The scan is cheap and worth running on ANY module that imports a recently created
sibling — intersect the two files' declaration-name sets, then compare bodies before
deleting anything:

    tools/merge/xdup.py .        # or a 20-line name-intersection in python

Delete the DOWNSTREAM copies, i.e. in the file doing the importing, and **compare
bodies whitespace- and comment-normalised first**: identical means nothing is being
chosen between, and a difference means the downstream copy may have been improved
after the hoist and deleting it would silently revert that work. In the
`PatchingWitt` case all 28 shared bodies were identical, which is what made the
deletion mechanical. A partial trim is a tell — `wittVectorTopology` had already
been removed from `Patching.lean` while the other 27 stayed, so the file was USING
one hoisted name and REDECLARING the rest.

