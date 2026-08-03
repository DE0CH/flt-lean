## VERIFY AGAINST THE LAST GREEN RELEASE'S OLEANS WHEN YOUR IMPORT CONE IS RED — and prove the shim sound by DIFFING THE API
(2026-07-31, `flt-lean-115`.) A target can live only on `merger`, and `merger` can be
RED in a module your file imports, for a reason that is not yours and whose repair is
somebody else's multi-hour task. Release 27 was in exactly that state: it was **not
published** (`tools/merge/RELEASE-27-HANDOVER.md`), `main` stayed at the last green
release, and `ModularCurve/X0.lean` carried ~193 errors *inherited from release 25*. So
`git merge merger` — which the doctrine correctly prescribes when your target exists
nowhere else — buys you the declaration and takes away `lake build`, because
`ModularCurve/X1.lean` imports `X0`.
**You are not blocked, and you must not "fix" X0 to unblock yourself.** The scratch shim
this file already documents for the *lake-deletes-the-target-olean* case is the general
answer, and this is its strongest use:
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, ~0.3 s
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Fermat/Scratch.lean
The farm is the LAST GREEN RELEASE's artifacts, so the red module is replaced by its
green predecessor and a scratch that `public import`s it elaborates in about a minute.
Here it verified 440 lines — three new leaves, five proven transport declarations and
the target's whole proof — first try, with exactly the three intended
`declaration uses 'sorry'` warnings.
**THE SOUNDNESS CONDITION IS NOT "the shim ran green"; it is that every name you use is
PRESENT AND UNCHANGED at the snapshot's sha, and you check that mechanically:**
    git show main:<the upstream file> > /tmp/up-main.lean
    # then, per name, compare the declaration text in /tmp/up-main.lean with your tree's
Nine names were compared this way (`IsFibreIdent`, `fibreIdentPullback`,
`IsSmoothProperCurve`, `finite_compl_range_fibreBaseChangeMap_generic`,
`genericFibreClassify`, and the four `Γ₁` structures) and all nine were byte-identical,
which is what makes the green scratch a genuine verification of the text that goes into
the file. The check also FOUND the one place it fails:
`exists_unit_natCast_of_isReductionBase` is merger-only, so a leaf stated over the
Katz–Mazur proviso `∃ n, 3 ≤ n ∧ IsUnit (n : ↥R)` could not have been verified — the
leaf was stated over `IsReductionBase` instead, with the improvement named in its
docstring for whoever takes it. **Design your cut around what the shim can verify**;
that is a cheap constraint and it is much cheaper than an unverifiable commit.
Two riders. Extract the scratch from the REAL FILE by line range once the edit is in
place, rather than keeping a hand-typed parallel copy — that way the thing you verified
and the thing you committed are the same characters. And a full shim run of the edited
module itself is worth launching in the background as a second opinion, but it is only
evidence about the parts that do not touch merger-only upstream names.
