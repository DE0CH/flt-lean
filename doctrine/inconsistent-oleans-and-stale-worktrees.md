## inconsistent oleans and stale worktrees

(Cut verbatim out of CLAUDE.md's `Verification is the COMMAND LINE. No MCP, no LSP, no servers` section at the 2026-08-03 doctrine split; nothing reworded.)

**`lake env lean` DOES NOT REBUILD IMPORTS — a partially refreshed `.lake`
manufactures phantom hard errors** (2026-07-26; cost at least four agents a
cycle each and produced a top-priority "defect repair" dispatch against a file
that was never broken).

`lake env lean <file>` sets environment variables and runs `lean`; it consumes
whatever `.olean`s happen to be on disk. `lake build <Module>` is the only
command that brings the import cone up to date. So after the worktree pointer
moves — which it does at every dispatch — **`lake build <Module>` FIRST, and
only then iterate with `lake env lean`.** An inconsistent olean set is the
default state of a freshly repointed worktree, not an exception.

Why an inconsistent set is worse than a stale one: **olean loading does not
typecheck.** A statement stored in an olean is deserialised verbatim, so an
olean compiled against an OLD signature keeps its old application arity, and the
mismatch surfaces only when a consumer uses the term — as a type mismatch, a
"rewrite failed, pattern not found", a "function expected", or a `(kernel)
application type mismatch`. All four shapes were observed from ONE cause. A
kernel error normally means "this proof is not accepted", and here it meant
"your `.lake` is inconsistent" — the most misleading possible signal.

The concrete instance: `38e8531` moved `Field.absoluteGaloisGroup.map` (and
`mapAux`, `lift_map`) above `variable [NumberField K]`, dropping an instance
argument. That is source-compatible — there is no `@`-application of it in the
tree — but NOT olean-compatible: oleans built before it store
`@Field.absoluteGaloisGroup.map ℚ Kᵥ Rat.instField _ Rat.numberField (algebraMap …)`
with `Rat.numberField` sitting in the `f` slot. Three worktrees whose
`AbsoluteGaloisGroup.olean` had been refreshed while `Semistable`/`Torsion`/
`WeilPairing` had not each reported the same four "hard errors" in
`MazurTorsion.lean`. A full `lake build` there produced `EXIT=0`, zero errors.

**Corollary for triage: "three agents confirmed it independently" is NOT
independent confirmation** when all three verified the same way in worktrees
sharing the same defect. Before treating a hard error as a source defect,
confirm it survives a complete `lake build` of the module, and check the olean
mtimes in dependency order:

    d=/scratch/chend-flt/flt-lean-N/.lake/build/lib/lean/Fermat/FLT
    stat -c '%y %n' $d/Deformations/RepresentationTheory/AbsoluteGaloisGroup.olean \
                    $d/FreyCurve/Semistable.olean $d/EllipticCurve/WeilPairing.olean

A downstream olean older than an upstream one it really imports means the set is
inconsistent and every diagnostic from it is untrustworthy.

**A FULL-CONE BUILD IS NOT ENOUGH — MERGE `main` FIRST** (2026-07-26, and this
corrects the rule immediately above). An agent applied exactly the test
prescribed here — a complete `lake build` of the cone — the error survived it,
and **the error was still not real**: its tree was ~250 commits stale and
current `main` already carried the repair. A full build proves the tree it is
given is broken; it says nothing about whether that tree is current. The two
failure modes are different and the build only separates one of them:

* *inconsistent oleans* → a full `lake build` clears it;
* *stale sources* → only `git fetch && git merge main` clears it.

So the triage order is **merge `main`, then full build, then believe it**. The
same defect (`MazurTorsion.lean`'s `map_baseChange` rewrite) was diagnosed
independently by at least seven agents and repaired on branches by six of them,
every one of which was working from a base that predated the fix landing. That
is not seven confirmations; it is one bug and seven stale checkouts.

**THE LINE NUMBERS IN YOUR OWN TASK PROMPT ARE A FREE STALENESS DETECTOR — check
them first, before anything else** (2026-07-31, measured). The loop generates a
task prompt's `Fermat/…:NNNN` references by scanning **`main` at the moment the
task is written**; the worktree hook fast-forwards the worktree at the moment the
task is *dispatched*. Those are different times, and under the loop they are
routinely hours apart: `flt-lean-318` was handed three targets at lines
3495/16362/17378 and opened a `TateModule.lean` whose copies of them were at
3303/14089/15105 — the checkout was `1411711d` (2026-07-30 11:54) against a `main`
of `d451d20b` (2026-07-31 00:25), **380 commits and +3057 lines in that one file**.

So the check costs one `grep -n` and settles it: if a target's line number in the
prompt does not match the worktree, the worktree is BEHIND `main` and everything
you are about to read is stale — merge before you read, not after your first
confusing result. The failure it prevents is the expensive one: reading a
docstring's absence table, route history or "already refuted" list from a version
that has since been rewritten, and then proving or re-refuting against it.

Do not "fix" the discrepancy by trusting the prompt's numbers and seeking around
them. A prompt is a snapshot of a file you do not have.

**A TARGET THAT DOES NOT EXIST IN YOUR WORKTREE IS A STALE WORKTREE FIRST, A
PHANTOM SECOND** (2026-07-31). This is the same rule, but its sharpest instance,
because a missing NAME looks like a completely different kind of failure from a
stale ERROR and invites a completely wrong report. `flt-lean-116` was dispatched
at `exists_neronModelData` in `X0.lean`, and the name occurred nowhere in its
copy of that file — zero hits, comments included, which is exactly the evidence
CLAUDE.md's own class-5 section says to read as a phantom dispatch. It was not.
The worktree was simply behind: `HEAD` was an old `merger` commit that happened
to be an ancestor of `main`, and one `git merge --ff-only main` brought the
declaration in along with 43 000 lines of `X0.lean`.
**So run these two commands before any `grep` for the target**, and note the
second is what distinguishes the cases — a phantom leaf and an un-advanced
worktree produce identical greps:
    git log --oneline -1
    git merge-base --is-ancestor HEAD main && echo "BEHIND: merge main first"
"The leaf is not here" and "I am not there yet" are the same observation until
you have run that. The dispatch hook normally fast-forwards a worktree at
allocation, so this state means the pointer did not move — do not treat it as
evidence about the frontier.
