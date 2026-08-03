## WHEN YOUR TARGET EXISTS ONLY ON `merger`, `merger` IS YOUR BASE — AND YOU CAN STILL VERIFY WHEN IT IS RED
(2026-07-31, `flt-lean-361`.) The release-window sections above all tell you to run
`git show merger:<file> | grep -n <name>` and stop when the answer is "already proven".
There is a third answer they do not cover and it is common: **the target DOES NOT EXIST
on `main` at all**, because the commit that cut it is sitting on `merger` waiting for a
release. `aj_eq_of_rationalProperCurve` was dispatched with a file-and-line reference
(`X0.lean:~46424 as of a33a7b1c`); `a33a7b1c` is on `merger`, is not an ancestor of
`main`, and the name appears **nowhere** in a `main`-based worktree. Every stale-worktree
check passes — `git rev-list --count HEAD..main` is `0` after one fast-forward, `git
status` is clean, the build is green — and the name is still missing.
**Do not re-create the declaration on `main`.** `X0.lean` was 81 530 lines on `main` and
107 787 on `merger`; a branch that re-cuts the leaf against the smaller file hands the
merge worker a 26 000-line conflict in the file it has the least capacity to resolve.
Merge `merger` into your branch (`git merge merger`, usually a fast-forward since your
worktree is behind it) and edit `merger`'s copy. The merge worker then fast-forwards you
back, and `git merge-tree` reports nothing to decide.
**THE PRICE IS THE BUILD, AND `merger` IS ROUTINELY RED.** Rebuilding `X0`'s cone at
`merger` took ~3 hours here and then failed: `merger` at `9e7f6e4b` has **103 errors in
`X0.lean` alone** (from `4887`, `5047`, `15542` `Unknown identifier
exists_nonConstant_qExpansion_gamma0GITPresentation`, `18083` `Unknown identifier
exists_jSection`, `22287`…, up to the `maxErrors` cap), i.e. the release-27 repair the
merge worker is in the middle of. That is not a reason to stop:
**Verify against the RELEASE oleans through the `LEAN_PATH` shim, after DIFFING THE
SIGNATURES of every declaration your proof names.** The shim is already documented above;
what makes it *sound* here — and this is the part that is new — is the signature diff.
Extract each name's declaration header from `git show main:<file>` and from your working
copy and compare them textually; if they are identical, a proof that elaborates against
the release environment ports verbatim. Nine names were checked this way
(`exists_relPicZero`, `RelPicEquiv.{refl,of_iso,tensor,cancel_left}`, `modTensorComm`,
`isInvertibleSheaf_sectionIdeal`, `IsRelPicZeroOf.isAlbaneseOf`,
`IsAlbaneseOf.isJacobianOf`), all identical, and the proof went from first draft to green
in **two 5-second iterations** against a file whose own build is hours long and broken.
Two riders:
* **The scratch farm must be the WHOLE release tree** (`cp -rs
  ~/.flt-release-lake/build/lib /tmp/relean-N/`), prefixed onto `LEAN_PATH` harvested with
  `lake env printenv` and run through **bare `lean`** — `lake env lean` resets
  `LEAN_PATH` and silently discards your prefix.
* **After porting, `lake env lean -DmaxErrors=400` the real file and grep for errors in
  YOUR line range.** A red file still elaborates past your region; the default cap of 100
  is what stops it, and raising it turns an unusable check into a usable one. "The module
  does not build" and "my edit does not build" are different claims, and only the second
  is yours.
