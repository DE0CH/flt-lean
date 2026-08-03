## A STALE OLEAN HAS A STALE *IMPORT LIST* — SO A GREEN SCRATCH IMPORT DOES NOT MEAN THE SOURCE CAN BE ELABORATED
(Same task, and it cost the only real detour.)  The standing rule is that
`lake env lean` does not rebuild imports, so a partially-refreshed `.lake`
manufactures phantom errors.  There is a sharper consequence that reads as a torn
tree rather than as staleness:
A scratch module that `public import`s your target loads the target's `.olean`,
and **that olean carries the import list of the source it was built from.**  If
the target's source has since GAINED an import, the scratch still exercises the
OLD dependency set — so it is green — while elaborating the target's own SOURCE
fails instantly with
    error: object file '….lake/build/lib/lean/…/WeilRestriction.olean' of module
    Fermat.FLT.Mathlib.AlgebraicGeometry.WeilRestriction does not exist
naming a module you have never touched.  Measured here: `Probe95.lean` importing
`X1` was **green in 4.1 s**, and `lake env lean X1.lean` died in 3.9 s on a
missing dependency olean.  Both facts are about the same `.lake`, and only the
second is about the file you are editing.
So: **a green scratch is evidence about your TEXT, never about your `.lake`.**
Before the one real elaboration, seed a complete consistent artifact set rather
than trusting the tree you have been iterating against.  The check that decides
whether the release snapshot is usable is one command and it was EMPTY here, so
the rsync is exact:
    git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/   # empty ⇒ snapshot IS your sources
    rsync -a --delete ~/.flt-release-lake/build/ .lake/build/        # 10 s, 2.8 G
Two riders.  A worktree can hold TWO artifact trees — `/scratch/…/flt-lean-N/{build,packages}`
flat AND a nested `/scratch/…/flt-lean-N/.lake/` — from the symlink-one-level-too-high
runaway recorded above; the one your `.lake` symlink reaches can be the newer and
still be INCOMPLETE, so compare them by asking for a specific dependency's olean
rather than by `du`.  And the harness's Bash tool **strips newlines from a
multi-line command**, so a launcher written as `export PATH=…` on one line and
`setsid …` on the next silently becomes a single `export` with extra arguments and
nothing runs — while your trailing `echo` still prints "launched".  Write the
launcher to a `.sh` file and run that.

