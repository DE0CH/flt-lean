## A RED RELEASE DOES NOT STOP YOU — elaborate your module against the LAST GOOD olean of the broken one

(2026-07-31, `flt-lean-258`.) Release 27 did not publish: `ModularCurve/X0.lean` is red
on `merger` with ~193 errors and has not been built since release 25. Everything
downstream of it is unbuildable, which on this tree is most of the project — including
`Modularity/Patching.lean`, three module hops away through `FreyCurve/MazurTorsion`.

An agent whose target lives in that cone will find, in this order: `lake build` fails
naming a module it never touched; and then **`lake env lean` on its own file dies with
`object file '….X0.olean' does not exist`**, because a failing `lake build` DELETES the
target olean at job start. That second message reads like a torn `.lake` and invites a
reseed, which does not help — the olean is missing because the module cannot be built,
not because the snapshot is damaged.

The escape is the `LEAN_PATH` shim CLAUDE.md already describes for the
"iterate while the final build runs" case, pointed at the *release* copy of the broken
module instead:

    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/lean
    R=~/.flt-release-lake/build/lib/lean
    cp --remove-destination -f "$R"/Fermat/FLT/ModularCurve/X0.*        /tmp/relean-N/lean/Fermat/FLT/ModularCurve/
    cp --remove-destination -f "$R"/Fermat/FLT/FreyCurve/MazurTorsion.* /tmp/relean-N/lean/Fermat/FLT/FreyCurve/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lean:$LP" LEAN_SRC_PATH="$LSP" \
      lean -o /tmp/relean-N/lean/<your module path>.olean <your file>.lean

**Two mechanics that are not in the existing write-up and cost a round each:**

* **`cp -f` onto a `cp -rs` farm entry WRITES THROUGH THE SYMLINK** into the real
  `/scratch` build directory. `cp --remove-destination` unlinks first. Getting this
  wrong does not fail loudly — it silently plants a stale olean in your own artifacts,
  which is the inconsistent-olean state this file spends a section on.
* **An olean is FIVE files at this toolchain**, not one: `.olean`, `.olean.private`,
  `.olean.server`, plus `.hash` siblings. Overlaying only `.olean` gives
  `failed to open file '….olean.server'`, which reads like a corrupt snapshot and is
  merely an incomplete copy. Always copy `<module>.*`.

Soundness condition, and it must actually be checked: the shim is honest only if
nothing in your cone uses a name added to the broken module since the release sha.
`git diff <release-sha> merger -- <broken module>` plus a grep for the added names
settles it, and a green result from the shim means nothing without it.

Corollary for triage, and it is the reason this belongs here rather than in a report:
**a build failure naming a module you have never heard of is a statement about the
RELEASE, not about your worktree.** Read `tools/merge/RELEASE-*-HANDOVER.md` before
reseeding anything — the merge worker records exactly which module is blocking and why,
and release 27's handover named X0 and its ~35-minute elaboration in the first screen.

