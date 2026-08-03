## VERIFY AGAINST `~/.flt-release-lake` WHEN YOUR MODULE CANNOT BE BUILT AT ALL

(Same run, measured: **8 seconds** per iteration against a module whose own build did not
finish in three hours and was killed twice by memory pressure.)

The doctrine's scratch-module rule assumes you can build the target once.  Under fleet
load on a 2 TB box with 32 GB free that assumption can simply fail — `WeilPairing.lean`
took >50 minutes and the whole `bash -c` wrapper then vanished with no `EXIT=` line, twice.
The release snapshot is a COMPLETE, CONSISTENT olean set at a known sha, and it is enough:

    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, 2 s
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    env LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Scratch.lean

Use the PRISTINE `~/.flt-release-lake/build`, not your own `.lake/build` — a `.lake` that
has been partly rebuilt from newer sources is exactly the inconsistent olean set the
doctrine warns about, and the shim is the way to avoid it rather than a way to live with it.

**The soundness condition is a diff, and it must be run.**  A scratch verified this way
proves something about the SNAPSHOT's theory.  For it to transfer, every declaration your
proof names must be unchanged between `$(cat ~/.flt-release-lake/sha)` and your HEAD:

    git show $(cat ~/.flt-release-lake/sha):<file> > /tmp/snap.lean
    # then diff the STATEMENT lines of each name you use, not a -A window --
    # a `grep -A 22` bleeds into the next docstring and reports spurious DIFFs

Here that was twelve names (`relPoint_pre_post`, `post_relSectionAlong_of_comm`,
`neronGenAut`, `neronGenAut_apply`, `IsX0JNeronDatum`, the section's `variable` block, …),
all identical, and the two apparent DIFFs were both the `-A` window running into unrelated
prose.  **A target that does not exist in the snapshot is the BEST case**: its name is free,
so the scratch can use the real final names and is then a character-exact test of the text
you are about to paste.

And the reverse reading, which is what makes the shim safe to rely on: `lake build <Mod>`
DELETES `<Mod>.olean` while it runs, so the two cannot be interleaved in `.lake` — but the
shim reads a different directory entirely and is unaffected.  Iterate in the shim, build once.

