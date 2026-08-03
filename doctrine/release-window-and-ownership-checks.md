## release window and ownership checks

(Cut verbatim out of CLAUDE.md's `Continuous work loop: never stop while the frontier is nonem` section at the 2026-08-03 doctrine split; nothing reworded.)

**Fifth invisibility class, and by volume the worst: THE RELEASE WINDOW.
`main` IS NOT THE FRONTIER — it is the frontier as of the last release.**

Between an agent finishing and its branch reaching `main` there are hours. In
that window every ownership check this file prescribes gives the WRONG answer,
and they all agree with each other, which is what makes it convincing:

- `main`'s `declaration uses 'sorry'` warning set still lists the leaf;
- a freshly repointed worktree's source still shows the `sorry`;
- the three-part ownership test correctly says nobody is working on it —
  **because that agent already stopped.**

On 2026-07-28 this fired at least eight times in one cycle. Agents were
dispatched at leaves that were already proven (`exists_isDiffChar`,
`comap_le_range_units_integers_of_isCompact`, `isCompact_normOne_infiniteAdele`,
`finiteDimensional_h1_adZeroTwistRestricted`, two in `Patching.lean`), and — the
mirror image — at leaves that **did not exist on `main` at all** because they
had been *cut* on an unmerged branch (`map_pow_twentyFour_eq_self_of_potentiallyGoodModel`,
`exists_ringEquiv_quaternion_of_isTotallyDefinite`, the whole STEP 1a-i′ block in
`KhareWintenberger.lean`, `flat_of_surjective_of_isAdditiveOn`). One agent
produced a complete, green, duplicated degree-1 cochain API before discovering
the same dictionary already existed on the branch it had been told about, and
correctly discarded it.

**`~/.flt-inflight.jsonl` cannot see any of this, because it is PRUNED when a
worktree goes `batched`** — measured 158/158 `claimed` worktrees have a record,
**0/201 `batched` ones do**. So "no record names this leaf" matches *both*
"nobody has worked on it" and "its owner finished and the proof is queued".

The check that resolves it is one command, and it subsumes most of the batch,
because the merge worker merges branches into `merger` continuously:

    git show merger:<the file> | grep -n <name>

An agent that scanned all 54 branches carrying a modified `Patching.lean` found
three of its four candidates already proven — **all three were visible on
`merger` alone.** Then check the handful of `~/.flt-merge-batch` branches that
touch your file, since `merger` lags the batch.

And **a branch is not the whole picture either: check UNCOMMITTED work in the
other worktrees.** Two workers were sent at `henselianLocalRing_adicCompletionIntegers`,
and the decisive evidence was neither a record nor a branch — it was an
**untracked new file** in the incumbent's worktree holding that declaration,
relocated to a different generality under a new module path. That is a conflict
at *file* granularity, which no branch diff shows until merge time.

    for d in ~/flt-lean-*; do
      git -C "$d" status --short 2>/dev/null | grep -q . && echo "== $d" && git -C "$d" status --short
    done

Corollary for dispatch: **name the branch as an INSTRUCTION, not as attribution.**
"`flt-lean-311` proved X" in a credit line is not read as "merge `flt-lean-311`";
three successors fast-forwarded to a `main` without X and found nothing.

**And the AGENT-side remedy, which costs two commands** (2026-07-31, `flt-lean-345`;
salvaged from a discarded incarnation's commit `0a3d57db`, and confirmed by a second one
the same day). When your TARGET does not exist anywhere in your tree, do not report a
phantom and stop. Find where it does exist and base yourself there:

    git grep -n '<declName>' merger -- '*.lean'          # usually merger has it
    git merge-tree --write-tree HEAD <branch>            # memory dry run: clean?
    git merge --no-edit <branch>                         # or: git merge --ff-only merger
    git diff --stat HEAD^1 HEAD                          # MUST be non-empty (class six)

The merge worker has usually merged the creating branch into `merger` already, so this is
not a rival cut — it is you catching up to a release window. Fast-forward FIRST (a freshly
dispatched worktree can be dozens of commits behind), and say in `to_merger` which base you
took. **Basing on `merger` rather than `main` is the right call when the target only exists
there**, and it is the only way to see the CURRENT layout: the second incarnation above
found that a hoist had, in the meantime, moved the whole region into a new upstream module
and stranded the leaf below its consumers — invisible from `main`, where the module does
not exist at all.

**THE UNDERSCORE TELL: on `merger`, read the BINDER LIST, not the body**
(2026-07-31, and it is one `sed` instead of one build). This development has a
hard convention — a hypothesis a `sorry` cannot consume is written `_hℓ`, and the
underscores come OFF when the leaf is proven. So

    git show merger:<file> | grep -n 'theorem <name>' -A6

answers "was this closed while I was being dispatched?" at a glance, and it
answers a second question no `sorry`-scan asks: **whether the SIGNATURE changed.**
`exists_isX1Compactification_specialFibre` was still a `sorry` on `main` and
proven on `merger` — and proven over a *different hypothesis*, the integral model
carrying `IsX1Compactification` rather than only its generic fibre. A check that
had only looked for the token `sorry` would have caught the first fact and missed
the second, which is the one that decides whether your work is a rival cut.

I had already written and VERIFIED GREEN a decomposition of that leaf when the
check ran. Landing it would have re-opened a closed leaf and conflicted with the
release; the right move was to revert my own green work. **A green build is not
evidence that your edit is wanted.**

**And check your payload against `merger` WITHOUT touching your worktree:**

    git merge-tree --write-tree --name-only merger <your-branch>   # prints a tree sha + conflicts
    git show <that-tree-sha>:<path> > /tmp/merged.lean             # the resolved file, markers and all

This is the cheapest instance of the class-7 check two sections below: strip the
markers, then grep the RESULT for every name your edit's interface touches. Mine
was a five-site statement change, and the merged file confirmed all five sites
landed and that no consumer on `merger`'s 3300 newer lines projects the changed
clause — a class-7 "clean merge that does not compile" ruled out in seconds, and
the one conflict located precisely enough to hand the merger a resolution instead
of a warning. It writes nothing outside the object store.

**The checks are TWO SCRIPTS answering DIFFERENT questions, and both must run**
(2026-07-29). `own.py` answers *is somebody working on it*; `leafstat.py` answers
*is it already done*. A dispatch this day named two leaves as "genuinely UNOWNED
— zero hits each in `~/.flt-inflight.jsonl`" and **both clauses were wrong in
different ways**: leaf 1 had five hits, one of them a `TARGET:` line
(`flt-lean-261`, dispatched 21 h earlier); leaf 2 had been PROVEN on `main` for
42 hours, at a commit that was an ancestor of the successor's own dispatch HEAD.

Re-run afterwards, `own.py` reported `flt-lean-261` correctly and instantly. The
tool was right; it had not been run — a hand `grep` was substituted for it. So
the failure was not a gap in the test but the orchestrator improvising around a
script written to stop exactly this. **Run the scripts.**

**`own.py` grew a FOURTH check the same day, and it is the one nothing else
covers: UNCOMMITTED work in the other worktrees.** The three-part test is about
RECORDS. An incumbent's proof can exist only as uncommitted work — invisible to
`merger`, to the batch, and to every branch diff, so `leafstat.py` cannot see it
either. `flt-lean-261` held 399 uncommitted lines of `Interface.lean` proving
its leaf *and renaming it* to `hasFiniteWildMonodromyAt_of_residueChar_ne`; a
successor sent at the old name would have raced a rename it could not observe.
`Interface.lean` had **nine** concurrent uncommitted editors at that moment.
`own.py` now greps every `claimed` worktree's diff plus its untracked `.lean`
files (a relocation lands as a new module, which is a conflict at *file*
granularity) and flags a name that appears in WIP with no record claiming it.

Unrelated but found while fixing it, and it had been corrupting every scripted
check run from the scratchpad: a scratch file named **`grp.py` shadowed the
stdlib `grp` module**, which `shutil`/`subprocess` import on POSIX — so every
python script run from that directory executed an unrelated group-theory
computation at import time and printed its output ahead of the real answer.
Renamed. Watch for scratch filenames that collide with stdlib modules.

**THE RELEASE-WINDOW CHECK HAS MOVED TO THE PROVER (2026-07-31), because the loop
cannot do it.**

Everything above about the release window is addressed to a dispatcher that can run
`own.py` and `leafstat.py` before sending anybody. Since 2026-07-30 the dispatcher is
`flt-loop.py`, a Python state machine: it builds its task list from `main` and has no
way to look at `merger`. `main` IS the frontier as of the last release, and `merger`
runs hours ahead of it. So the check is now the PROVER's, and it is the prover's FIRST
action — before reading the target, before seeding `.lake`:

    git show merger:<the file> > /tmp/x.lean     # then READ the declaration

Measured cost of skipping it, 2026-07-31, `flt-lean-300`: dispatched at three leaves in
`HilbertModularity.lean`, **all three already resolved on `merger`** (release 24, while
the worktree sat at release 23), and the session went into independently rebuilding one
of them. The rebuilt cut turned out to be architecturally identical to the landed one —
same three helper lemmas, and the same non-obvious extra hypothesis, that `ℓ` must be a
NONZERODIVISOR in the coefficient ring (without it `ZMod 4 → ℤ_[2]` refutes the
statement). Two agents converging independently on the same repair is reassuring about
the mathematics and is still one worker-cycle thrown away.

**Grep the NAME and you will conclude the opposite of the truth.** All three names were
present on `merger`. Two carried full proofs. The third had been RESTATED — same name,
different conclusion (`exists_hilbertAuxHeckeModuleData` now PRODUCES `diamond` and
exports `ker diamond = 𝔟_ex`, the repair its own §5a audit demanded) — so a prover
working from `main` would have spent the session proving a statement that has been
withdrawn, and the `sorry` on `main` would have looked like ordinary open work the whole
time. The check must read the DECLARATION, not match its name; and a docstring's own
"DO NOT DISPATCH A PROVER HERE YET" is evidence about the version you are reading, not
about the frontier.

Corollary for what you commit: when `merger` already closes your target, **decline your
own payload** rather than carrying a rival cut. The tie-break is "fewer OPEN leaves
after", and a landed complete proof beats a fresh decomposition every time — carrying
mine would have traded a closed leaf for an open one plus a large conflict. Say so in
the sentinel's `to_merger`, so that an empty or tooling-only diff is not read as the
dropped-merge bug of class six.

**AND THE MERGER-CHECK CAN CONFIRM YOUR LEAF IS OPEN WHILE ITS PROOF SITS 260 LINES
ABOVE IT IN THE SAME FILE** (2026-07-31, `flt-lean-82`).

The variant the rule above does not cover: the name IS on `merger`, it IS still
`sorry`, and the answer is still wrong — because a SECOND declaration with the
IDENTICAL statement under a DIFFERENT name is proven earlier in the same file.
`mem_idl_of_X7_mul_mem` (`sorry`, line 689) and `mem_idl_of_Pz_mul_mem` (PROVEN,
line 423) in `ProjectiveEquationAdd2.lean` are character-for-character the same
proposition. Two branches decomposed `idl_isPrime` the same way under different
names; a union-style conflict resolution kept both blocks, so the file carries the
whole decomposition twice — the saturation half is duplicated too
(`exists_pow_Pz_mul_mem_idl` / `exists_pow_X7_mul_mem_idl`, both open).

This is the worst shape the merger-check takes, because it does not fail: it
returns a positive, correctly-quoted `sorry` at the right line, and every
subsequent step — the task prompt's route, the section docstring, the sorry-warning
count — agrees with it. Nothing anywhere says "look for this under another name".

So when the merger-check finds your leaf open, do not stop there. **Read the
enclosing section, and grep for the STATEMENT rather than the name:**

    git show merger:<the file> > /tmp/x.lean
    grep -n '∈ idl' /tmp/x.lean          # a distinctive fragment of the CONCLUSION
    grep -n '^theorem' /tmp/x.lean       # then scan the section for near-twins

A duplicate block announces itself in the declaration list — two `idl_ne_top`-shaped
runs of the same shape, or one file with two "### Half two" section headings. In this
file the module docstring named the `X7` pair while the proven pair was `Pz`-named,
which is exactly the tell.

What to do when you find it: **delegate, do not re-prove.** Replace your `sorry` with
a one-line application of the existing proof, say in the docstring that the
declaration is a duplicate slated for deletion, and put the deletion in `to_merger`.
Do NOT delete the twin of a leaf that has its own live owner — deleting
`exists_pow_X7_mul_mem_idl` here would have destroyed another agent's in-flight
target for the sake of tidiness. Closing your own by delegation costs one line and
conflicts with nobody.

