## A PROVER CAN DECLINE ITS OWN RIVAL CUT — do it on your branch, not in the merger's lap

(2026-07-31, `flt-lean-238`. All THREE targets of one task were already closed on `merger`; the
check that found it cost one command and ran before any Lean was written.)

The release-window section above says `main` is not the frontier. This is the prover-side
consequence, and it has two halves that are learned separately.

**First: test SORRIEDNESS, not PRESENCE.** The obvious check —
`git show merger:<file> | grep -n <name>` — is necessary and, on its own, actively misleading
when the leaf was DECOMPOSED rather than proven. A decomposed parent **keeps its name and its
line**, so the grep hits either way; what changed is that its body is now a one-line call to a
NEW leaf with a DIFFERENT NAME that no scan keyed on your target can find. Two of the three
targets here were exactly that:

    exists_riemannRochGrowth_of_isProperSmoothCurve       -> exists_riemannRochGrowth_of_pointCountRecursion
    exists_planeModel_birationalOver_of_isProperSmoothCurve -> exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve

Both parents are PROVEN on `merger` and still `sorry` on `main`. So run the comment-stripping
attribution scan — `flt-frontier.py`'s `scan()` — against the *merger copy of the file*, not a
grep:

    git show merger:Fermat/FLT/.../File.lean > /tmp/m.lean
    # then flt-frontier.py's scan() on /tmp/m.lean; a name absent from its output is PROVEN there

**Second: when the collision is a genuine rival PROOF, decline it yourself.** The third target
had been proven on this branch by an elementary integral-matrix bijection (492 new lines, four
new lemmas) and independently on `merger` through Petersson self-adjointness (zero new
declarations, reusing analytic machinery the file already had). Both sorry-free. Two proofs of
one theorem cannot both be carried, so one had to go, and the file's own tie-breakers — fewer
new declarations, already integrated and consumed by neighbours — both pointed at `merger`'s.

Handing that to the merge worker as a conflict is the worse option, and not only for its time.
The four helper lemmas sat ~280 lines ABOVE the theorem, far enough that git merges them
CLEANLY while conflicting only on the theorem body — so resolving the visible conflict to
`merger`'s side leaves four FREE-FLOATING lemmas behind and no error to notice them by. That is
the interface-split hazard of class seven, arriving through a rival cut instead of a signature
change.

The recipe, and it is three commands:

    BLOB=$(git diff <base> <yourcommit> -- <the file> | git hash-object -w --stdin)
    git tag flt-lean-N-superseded-<what> "$BLOB"
    git checkout main -- <the file>          # decline; NOT `git revert`, which fights the merge

Then **verify the round trip before you commit** — `git show <tag> > /tmp/p.diff &&
git apply --check /tmp/p.diff` must pass against the declined tree. It will FAIL against the
undeclined one, which is the expected reading and not a broken tag.

What this buys: your branch merges trivially, the decline is recorded permanently in a commit
message rather than in a merge nobody re-reads, and the superseded proof stays recoverable in
the shared object store where it conflicts with nothing. A second independent route to a closed
node is an asset — downstream consumers are not hostage to whichever proof survives — so say in
the report that it exists and name the tag; it just must not be a second DECLARATION.

