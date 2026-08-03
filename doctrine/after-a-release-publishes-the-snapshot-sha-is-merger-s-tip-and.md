## AFTER A RELEASE PUBLISHES, THE SNAPSHOT SHA *IS* `merger`'s TIP — AND A PROMPT'S BUILD ESTIMATE IS THEN WRONG BY TWO ORDERS OF MAGNITUDE

(2026-08-01, `flt-lean-139`.) Every seeding rule above assumes
`~/.flt-release-lake/sha` is `main` and that `merger` runs ahead of it, so a
merger-based branch has no usable artifacts and must rebuild. **For the window after a
release publishes, that is exactly backwards: the snapshot sha is the `merger` tip.**

Measured. The task prompt said `lake build Fermat.FLT.FreyCurve.MazurTorsion` is
"a ~3h build from cold because `Fermat/FLT/ModularCurve/X0.lean` (a direct import) takes
~2.5h alone", and prescribed developing entirely in a scratch to avoid it. The target
declaration existed only on `merger`, so:

    git merge merger                                       # per [[flt-target-exists-only-on-merger]]
    cat ~/.flt-release-lake/sha                            # == the merged HEAD, character for character
    git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/      # EMPTY
    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/

That rsync took **15 seconds**, the pre-edit `lake build` of the target was a **pure
replay in under 30 s**, and after the edit the only module that elaborated was the one
file I had touched. Three hours became one file, and the "one final blocking verify"
budget became "verify as often as you like".

**So run the two commands BEFORE pricing anything**: `cat ~/.flt-release-lake/sha`, then
`git diff --stat <that sha> HEAD -- Fermat/`. An empty diff means the snapshot is YOUR
tree, whatever branch you are standing on. A prompt's build estimate is a statement about
the tree its WRITER had; a release landing in between invalidates it, and it invalidates
it in the direction that makes agents skip the real verification and ship
scratch-only evidence.

**Corollary — it settles the merger-vs-main question that
[[flt-target-exists-only-on-merger]] leaves open.** The standing objection to basing on
`merger` is that its build state is unknown and its artifacts are missing. When the
snapshot sha equals `merger`'s tip, both halves of that objection are false by
construction: the artifacts match `merger` exactly and they are a published green build.
Base on `merger` without hesitation, and say in `to_merger` that the branch is
merger-based *and that the snapshot certified it*, so the ancestry is not read as a
mistake.

**A pre-edit replay build is also the cheapest baseline you will ever get**, and it is
what makes the standing "diff the warning sets" check exact rather than approximate: run
`lake build <target>` BEFORE touching the file, keep the log, and compare the
`declaration uses 'sorry'` sets afterwards. Here that turned "the recut is `1 → 1`" from
a claim into a receipt — 37 sorried declarations before, 37 after, with the target's name
out of the set and the new leaf's name in it, computed by attributing each warning line to
its enclosing declaration rather than by eyeballing line numbers, which the insertion had
shifted.

### The pin has NO argument principle — so "integrate `dF/F` around a contour" is a development, not a step

Recorded because it is what prices every valence-formula-shaped leaf, and because the
absence is easy to disbelieve given how much complex analysis mathlib has. Checked
2026-08-01: `grep -rli "argument principle" Mathlib/`, `grep -rli "residue theorem"
Mathlib/`, `grep -rn "windingNumber\|winding number" Mathlib/` and
`find Mathlib -iname "*residue*"` (which returns only `SumOverResidueClass`, and three
files about residue FIELDS) are all empty of the thing. `Mathlib/Analysis/Meromorphic/`
does have `Divisor.lean` — the divisor of a meromorphic function, with finiteness of its
support — but nothing computing that divisor's DEGREE, which is the whole content. What
mathlib does have, and what a valence-formula prover will want, is the `SL₂(ℤ)` reduction
theory in `Mathlib/NumberTheory/Modular.lean` (`fd`, `fdo`, `exists_smul_mem_fd`,
`stabilizer_I`, `stabilizer_ρ`, `isCompact_truncatedFundamentalDomain`) and the level-one
dimension formula under `Mathlib/NumberTheory/ModularForms/LevelOne/`.

