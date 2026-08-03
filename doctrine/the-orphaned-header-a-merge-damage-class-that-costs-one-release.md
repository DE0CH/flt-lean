## THE ORPHANED HEADER: a merge-damage class that costs ONE RELEASE-BUILD ROUND EACH, and a script that finds all of them in seconds

(2026-07-31, `flt-lean-105`, four instances in one release.) The "MERGING NINETY
BRANCHES" section above already lists *"block-comment nesting depth returns to zero in
every file"* as check 3 and calls it the cheapest in the list. It was not run for
release 25, and four files were damaged: `EllipticCurve/IsogenyTrace.lean:804`,
`EllipticCurve/MordellWeil19.lean:476`, `ModularCurve/EllipticScheme.lean:11144`,
`Modularity/AmpleSheaf.lean:2293`. There is now a script, `flt-comment-balance.py`
(repo root, `python3 flt-comment-balance.py`), so there is no longer an excuse:

    Fermat/FLT/EllipticCurve/MordellWeil19.lean depth=1 unclosed_at=[476]

**The mechanism is narrower than "a conflict inside a docstring", and knowing it gives
you the repair for free.** In all four cases a branch had RENAMED a section header and
MOVED its block elsewhere in the file. The merge then kept the OLD header's first line
at the old position and the NEW block's body after it — so the old header lost its `-/`
and the file now contains a stranded title line immediately above an unrelated `/-!`:

    /-! ### Rank-two linear algebra for the `ℓ`-torsion        <- stranded, no `-/`
    /-! ### The parallelogram law collapses to its UNIT SHIFT  <- the surviving block

**So the repair is to DELETE the stranded line, not to close it with `-/`.** Grep its
title first: in every one of the four cases the block it named was alive elsewhere in
the same file under the new name (`### The Weil pairing on the ℓ-torsion` at ~1036;
`THE level-19 statement` re-proved at ~1388; `#### Δ = 0 forces a rational singular
point` on the very next line; `AN INVERTIBLE SHEAF … LOCALLY FREE OF RANK ONE` at
~2672). Closing the orphan instead leaves a duplicated, stale header that the next
reader will believe.

**Why it is worth a scan rather than a build.** The orphan swallows *every* declaration
after it, so the module emits exactly one diagnostic — `unterminated comment`, reported
at EOF, thousands of lines from the damage — and every module importing it then fails on
names that "do not exist". And because `lake build` stops at the first failing module in
dependency order, **the four were serialised behind one another**: each would have cost
its own release-build round, which is where the "budget three rounds minimum" figure in
the class-7 section comes from. The scan finds all four at once in a couple of seconds.

**`depth < 0` is MOSTLY noise and OCCASIONALLY the mirror defect — check it, cheaply,
and do not "fix" it blind.** The scanner matches two characters and Lean's lexer does
not, so a file Lean accepts can score negative: `X0.lean` scores `−11` and its comments
are fine. But `InvariantCoarseRing.lean` scored `−2` and was genuinely broken, in the
OTHER direction: a merge kept the first two lines of one branch's `theorem` signature
and then the other branch's docstring BODY without its `/--`, so the surviving `-/`
closed a comment that had never opened *and* ten lines of English were parsed as the
continuation of a truncated signature. Lean's diagnostic for that is
`unexpected token; expected ':'` — nothing about comments at all. So: `depth > 0` names
its own culprit and is always real; `depth < 0` is a prompt to run `lake env lean` on
that one file, which settles it in a couple of minutes.

Corollary about doctrine generally, and it is the uncomfortable half: this check was
already written down, in bold, one section up, described as the cheapest available — and
it still did not run, because a prose instruction in a 3 900-line file competes with a
hundred others at the moment somebody is merging ninety branches. **A check that is worth
running every release should be a script with a name, not a paragraph.** Converting one
costs ten minutes and is a full result for a task that has spare time.

