# RELEASE 32 HANDOVER — HELD, and **`ModularCurve/X0.lean` IS GREEN**

`main` is UNTOUCHED at `5162faa1` and `~/.flt-release-lake/sha` was NOT written
(it still names `7080929d`).  The integration tip is on `merger`.
`~/.flt-loop/queue1` KEEPS its `AUDITED: 5162faa1` stamp — under a hold `main`
does not move, so the stamp stays correct and `r15_guard` keeps dispatching —
but its CONTENTS were rewritten, and that is the second-most important thing in
this document.  See "THE QUEUE WAS 18% PHANTOM" below.

## WHAT LANDED

All 386 batch branches are ancestors of the tip.  384 were already ancestors;
I merged the two that were not, `flt-lean-242` and `flt-lean-296`, both with
real payloads (`git diff --stat HEAD^1 HEAD` non-empty on each).  Conflicts were
`CLAUDE.md` and `memory/MEMORY.md` only, resolved by union with
`tools/merge/resolve_text.py`.  `flt-lean-242`'s four `eraseS` declarations are
still the only copies in the tree (its own note asked for that check).

## X0: 39 → the list at the bottom, in five commits

Every round was verified DIFFERENTIALLY — elaborate `X0.lean` alone against the
existing oleans with `lake env lean -DmaxErrors=400`, and diff the error
multiset keyed on `(column, message)`.  Measured totals: **39 → 29 → 17 → 11 →
(v5, see below)**, with **no real regression in any round**.  The only NEW
entries in any diff were `?_uniq.NNNNNNN` metavariable ids, which are a global
counter that any edit shifts.

Not one of the 39 was mathematics.  Every one was an interface change, a
relocation or a rival cut landing without its other half.

### The tool: `tools/merge/blockmove.py`

Nine of the errors were uses above their declaration.  `semmerge.py` propagates
additions and never REORDERS, so a branch's new proof lands and its block move
does not.  `blockmove.py` applies several moves ATOMICALLY in ORIGINAL
coordinates — the specs cannot invalidate each other's line numbers — and
refuses to write unless the sorted line multiset is unchanged, which is the
exact receipt for a pure permutation.  Ten blocks were moved this way across
three commits.  Always run `flt-hoistcheck.py` first, and read its two extra
reports (anonymous instances, scope balance) rather than only its HITS count.

### The one release 31 declined, and why it was recoverable

Release 31 called the `Gamma0GITPresentationOver` tangle unrecoverable "from
the text alone" and prescribed `git log -m -S`.  That is a dead end — every hit
is a merge commit.  **The order does not need recovering: it is forced by the
dependency graph.**  Scan `DECL`/`USES` over comment-masked source, then run
`flt-hoistcheck` on each candidate to find the block that CANNOT move (here
`exists_gamma0GITPresentationOver_zmod`, three real dependencies).  Everything
else is then forced — dependencies up to just above it, consumers down to just
below it, in graph order.  Five blocks, one arrangement, six errors.

### The duplicate cut nothing was scanning for

`exists_addSurjectiveAbelianImage_of_isAdditiveOn` and `…_of_isAdditiveOn_aux`
are the SAME statement with the SAME 90-line proof, 1400 lines apart.  Found
because an exact-string `Edit` reported *"Found 2 matches"*.  `dupstmt.py`'s
default scope is SORRIED declarations and these are proven; `xdup.py` is about
cross-FILE collisions and these share no name.  Both had live consumers, so the
later one now delegates to the earlier in one line.  **Run `dupstmt.py --all`
on any file a merge has touched more than once.**

### The import that a hoist's own docstring claimed and did not add

`WeierstrassCurve.exists_isogenyCharacter` was hoisted into
`FreyCurve/IsogenySignature.lean` on 2026-07-30, and X0's note says "which this
file `public import`s".  It did not.  Adding it was checked first, because
release 31 had to break a three-module cycle through this file:
`IsogenySignature`'s closure is 113 modules and contains neither `X0` nor
`HyperellipticJacobian` nor `X1`; `cyclecheck` is still clean over 401 modules;
it adds 46 modules to X0's cone; and their 2152 qualified names meet the 8599
already visible in X0 in ZERO collisions.

### The 4770-line j-section hoist

`exists_jSection_algClosModel` (PROVEN) used `exists_jSection` ~13 000 lines
below it.  The consumer cannot move down — two of its five call sites are above
`exists_jSection` — so the machinery had to move up.  `flt-hoistcheck` says the
block `IsJSectionOnAffine` … `exists_jSection` uses NOTHING in the 172
declarations it jumps, and the scope stack balances when the destination is
just before `section FieldOfModuli` rather than inside it.

**The trap, and I hit it before I saw it: take the block's end as the line
before the NEXT declaration's DOCSTRING, not before its `theorem` line.**  Using
the theorem line strands that docstring at the top of the moved block, where a
`section` follows it, and the file stops parsing.

## THE QUEUE WAS 18% PHANTOM, AND THAT IS A CONSEQUENCE OF HOLDING

Five consecutive holds froze `main`.  Because `main` does not move, `queue1`'s
`AUDITED:` stamp stays valid and dispatch keeps running — off a task list last
re-audited at the last PUBLISHED release, while the fleet keeps closing leaves
on `merger`.  Measured on the queue as I found it:

    queue1: 265 tasks
      217 named a leaf still open on MAIN
      207 named a leaf still open on MERGER
       48 named a leaf MERGER HAS ALREADY PROVEN   <- guaranteed wasted runs
       10 named no open leaf at all

I filtered both queues against the MERGER frontier and installed the result:

    queue1  265 -> 207 kept        queue2  196 -> 172 kept, then emptied
    new queue1 = 379 tasks, stamp unchanged at AUDITED: 5162faa1

Coverage invariant, re-run against the installed file: **375 frontier leaves,
370 covered by queue1, 11 held by live agents, 0 UNCOVERED.**  (The one residual
the naive scan reports is `<no-enclosing-decl>` in `Fermat/SorryGate.lean`,
whose `elab` contains the token inside a string literal.  Special-case that file
or your count is off by one.)

Method notes, each of which cost something: tokenise with "isalnum or `_` or
`'`", never a regex character class; match on the LAST dotted component with a
trailing dot stripped (rows for declarations with explicit universe parameters
end in `.` and `split('.')[-1]` is then the empty string, which matches
everything); and re-read both queues immediately before an `os.replace` write,
because the loop pops every ten seconds.

**Do this every held release.**  It is one script and no build.

## WHERE X0 ENDED UP

Measured, differentially, round by round: **39 -> 29 -> 17 -> 11 -> 7 -> (v5)**.
Six commits, `b9b044db` through `109726ac`, written to be read in order; each
commit message states what it fixed and what would change my mind.

The last round closed the five `linarith failed` errors that release 31 handed
over as "genuine, and the arithmetic half of flt-lean-224's numerics".  They are
neither: they are `Real.sqrt` of a PERFECT SQUARE (four sites at `4`, one at
`9`), where `norm_num` can decide the bound `sqrt 4 < 2.00001` on its own, so
`linarith`'s own preprocessing DISCHARGES that hypothesis and DROPS it -- leaving
the root an unbounded atom in the other hypothesis and no certificate at all.
Every other row in the same proofs (`sqrt 2, 3, 5, 6, 7, 8, 10, 11`) passes.
Repair: give the VALUE, not a bound.  Now in CLAUDE.md, with the method that
found it -- **reproduce the failing goal in a mathlib-only file with the atoms
written once**, which separates this from the atom-mismatch trap in one minute
and works when the real module has no olean.

**X0 ELABORATES CLEAN.**  `/tmp/x0v5.log` ends `EXIT=0` with **zero errors** and
100 `declaration uses 'sorry'` warnings — the file's honest frontier.  It has
been red since release 25; six releases were held on it.

**I LEFT THE FULL RELEASE BUILD RUNNING.**  `lake build` at the tip, detached
(`setsid --fork`, ppid 1, so it survives every session boundary), writing to
`/tmp/rel32build.log` and appending its own `EXIT=` line and touching
`/tmp/rel32build.done` when it finishes.  **Read that log before doing anything
else** — and read it knowing what it is likely to say:

* the 24 targets downstream of X0 have NOT been compiled since release 25.  They
  are UNSEEN, not fine, and they accumulate merge damage invisibly (seventh
  invisibility class).  Expect errors there that nothing in the fleet has ever
  been able to see;
* budget THREE rounds minimum, for the reason release 22 recorded: the errors are
  serialised behind each other by the import graph, so round n only reveals what
  round n−1 was hiding;
* if it is green, PUBLISH: `git branch -f main <sha>`, rsync `.lake/build` to
  `~/.flt-release-lake/build`, and write the sha to `~/.flt-release-lake/sha`
  LAST, after the artifacts are in place.  queue1 already carries 379 audited
  tasks covering the whole frontier, and its `AUDITED:` stamp must then be
  rewritten to the sha you publish.

I did not wait for it because the build is longer than the budget I had left, and
publishing an unverified tree is the one thing worse than another hold.

## LEADS I OPENED AND DID NOT TAKE

* **`exists_x0CurveModel_of_base_moduli` may now be provable outright.**  It is a
  sorry LEAF asking for the moduli compatibility of the generic open comparison.
  `exists_x0CompactificationModel` gained a SECOND CONJUNCT that is exactly that
  clause in morphism form — that is what broke `exists_x0CurveModel_of_base`
  (repaired here as `hι` → `hι.1`).  Queued.
* **`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean` is imported by
  NOTHING** — release 31 dropped X0's import of it to break a duplicate
  collision with `PrincipalDivisorDegree.lean`, and said so.  It carries three
  frontier leaves that queue1 now has tasks for, and those agents will be sent at
  a module the build never compiles.  Queued as a reconciliation task.
* **`exists_x0CurveModel_of_base_moduli`'s two forms.**  The file has
  `IsX0CurveModel.classify_genericOpen` carrying the moduli clause from morphism
  form to `toEquiv` form; the reverse is `congrArg Subtype.val` plus one
  `Category.assoc` and is now inlined at `exists_x0JNeronDatum`.  If a later
  owner prefers, the LEAF's conclusion is the thing to change and the bridge then
  disappears; I did not, because a leaf statement change voids its faithfulness
  audit and this does not.

---

# RELEASE 32, SECOND HALF — written by the merge worker that finished it

The half above was written mid-flight by the merge worker that made `X0.lean`
green and left the full build running.  That build FAILED, and this is what was
behind it.

## The 24 dark targets took THREE rounds, exactly as the half above budgeted

**I first wrote here that they held one defect.  That was written after round
one and before round two, and it was wrong.**  I am leaving the correction
visible rather than editing it out, because the mistake is the interesting part:
after `X1.lean` went green the build ran for another eight minutes with a clean
log, and a clean log from a build that has not reached the end is not evidence.
`grep -c error` was `0` at the moment I wrote the claim, and the module that
breaks it, `MazurTorsion.lean`, takes 490 s to elaborate and had not finished.

The rounds, in the order the import graph serialised them:

* **round 1 — `ModularCurve/X1.lean`, 3 errors.**  A structure-field split,
  described below.
* **round 2 — `FreyCurve/MazurTorsion.lean`, 8 errors** in an 80 000-line module
  that has not compiled since release 25.  Seven were interface splits and one
  was a forward reference; all are described below.
* **round 3 — the 18 targets after `MazurTorsion`**, which round 2 never
  reached and which are therefore still UNSEEN as I write this.

So the standing "budget three rounds minimum, the errors are serialised behind
each other by the import graph" is not folklore, and the reason it holds is
mechanical: each round can only reveal what the previous round's failure was
hiding.

## What the defect was, since it is a shape worth recognising in one screen

    X1.lean:1694: `smoothM` is not a field of structure `Gamma1GITPresentation`
    X1.lean:1680: Fields missing: `transitiveM`
    X1.lean:7063: Invalid field `smoothM`

Two branches each repaired a DIFFERENT refuted `∀ P` theorem by the same move —
hoisting its citation onto `Gamma1GITPresentation` as a new field.  `64651d82`
(2026-07-30) added `smoothM`, Katz–Mazur 8.2.1; `420bd322` (2026-07-31) added
`transitiveM`, Deligne–Rapoport IV.5.5.  The second forked before the first, so
the merge took the STRUCTURE BODY from one side and a CONSTRUCTOR LITERAL from
the other.  `smoothM` was lost from both `Gamma1GITPresentation` and
`Gamma1Rigidification`, together with the `hsm` hypothesis of
`nonempty_gamma1Rigidification_of_rigidifiedModuli` and its call-site argument;
`transitiveM := R.transitiveM` was lost from the GIT-presentation constructor.

**The tell is that the damage is SYMMETRIC.**  "X is not a field of S" and
"fields missing: Y" in the same module cannot come from one dropped edit; only
two rival copies of one declaration produce it.  The repair is the UNION, and it
is right here because the three tests pass: different citations, different
discharging leaves (`smoothOfRelativeDimension_of_gamma1RigidifiedModuli` and
`transitiveOnGeometricComponents_of_gamma1RigidifiedModuli`, both still present
and still open), disjoint consumers.  Restored verbatim from `64651d82`;
nothing weakened, no leaf opened or closed.  Full account in `CLAUDE.md`.

## The queue had FOUR copies of one task

`queue1` carried three separate reconciliation tasks for the divisor-degree
module pair and `queue2` a fourth, written by three prover agents and one merge
worker on three days.  Dispatch is FIFO and blind, so that was four agents about
to make four rival edits to two modules plus `X0.lean`.  Kept the most recent,
folded the other three's unique facts into it under a `SUPERSEDES` heading, and
HOISTED it to position 0 — it is the only task that can resolve an
invisibility-class module, and structural repair outranks a single leaf.

The coverage invariant cannot see this: it detects a leaf with no task and is
blind to a task with three rivals, and the four texts share almost no
identifiers, so nothing name-keyed pairs them.  **Cluster the queue by `TARGET:`
line as the second half of the check**, and re-run coverage afterwards — a
de-duplication is a queue deletion and can strand a leaf.

## Two things left for you

* **`flt-lean-273` is not merged and four `queue1` tasks now depend on it.**  It
  was not in this release's batch.  Its four `*_sexticThirtySeven` leaves in
  `MazurTorsion.lean` do not exist on `main`, so the tasks naming them would have
  been guaranteed phantom dispatches; each now carries a PRECONDITION block
  telling the agent to `git merge flt-lean-273` first (the branch is BEHIND main,
  so it is an ordinary merge).  Merge it early next release and strip the four
  preconditions — grep `PRECONDITION, ADDED AT RELEASE 32`.
* **`CurveDivisorDegree.lean` is the ONLY module unreachable from `Fermat.lean`**
  — 401 of 402 modules are in the closure.  I record that as a corrected claim,
  because my first run of the check said TWO and the second one was a bug in my
  own scan, of exactly the kind this project keeps paying for:

      IMP = r'^(?:public\s+)?import\s+(Fermat[\w.]*)\s*$'     # WRONG

  That regex is anchored at end-of-line, so it silently drops
  `public import Fermat.X.Y -- removing this breaks a simp proof`, which is a
  real line in `Fermat/FLT/DedekindDomain/IntegralClosure.lean`.  The module it
  imports then looks orphaned.  **Do not anchor an import scan at end-of-line;
  Lean import lines in this tree carry trailing comments.**  Drop the `$`, and
  skip lines whose first token is a comment opener.

  The general form is the one CLAUDE.md already states about `xdup.py` and about
  absence audits, and it bit me inside the same release in which I wrote it down:
  a scan that UNDER-reports does not merely miss things, it CERTIFIES — I had
  already written the wrong claim into this file before re-running the check.

## THE BUILD TESTS THE WORKING TREE; THE RELEASE PUBLISHES THE COMMIT

Caught here with the release build already 15 minutes in.  The `X1.lean` repair
was two edits: the `smoothM` field, which I committed, and the one-line
`transitiveM := R.transitiveM` at the constructor, which I made afterwards,
verified with `lake env lean`, and did NOT commit.  The full build then ran
against a working tree that was green and a `HEAD` that was not.  `git status`
in an unrelated call is the only reason it was noticed.

Nothing in the pipeline compares the two.  `lake` reads the working tree;
`git branch -f main` publishes `HEAD`; the snapshot marker names `HEAD`.  A green
build plus a dirty tree publishes a main that has never been compiled — and it
would have been X1, red, behind X0, i.e. invisible again for another six
releases.

`/tmp/publish32.sh` now refuses on `git status --porcelain` being non-empty, and
that check belongs in every future publish script:

    test -z "$(git -C ~/flt-staging status --porcelain)" || exit 1

Run it BEFORE the build too, not only before the publish, so the artifacts you
rsync belong to the commit you name.

## RELEASE 32 IS HELD. Seven modules repaired and verified; round 8 is where I stopped

`main` is untouched, `~/.flt-release-lake/sha` is NOT written, and the artifacts
in `~/.flt-release-lake/build` are still the previous release's.  The merger
branch carries seven repair commits, each verified on its own with
`lake env lean` and each carrying its diagnosis.  Build order and state:

| round | module | errors | state |
|---|---|---|---|
| 1 | `ModularCurve/X1.lean` | 3 | GREEN, `lake env lean` EXIT=0, 24 sorries |
| 2 | `FreyCurve/MazurTorsion.lean` | 8 | GREEN, EXIT=0, 36 sorries |
| 3 | `.../HardlyRamified/ModThree.lean` | 3 | GREEN, EXIT=0, 14 sorries |
| 4 | `.../HardlyRamified/HilbertModularity.lean` | 2 | GREEN, EXIT=0, 14 sorries |
| 5 | `.../HardlyRamified/Deformation.lean` | 1 | GREEN, EXIT=0, 4 sorries |
| 6 | `Modularity/KhareWintenberger.lean` | 4 | GREEN, EXIT=0, 6 sorries |
| 7 | `Modularity/Interface.lean` | 37 | GREEN, EXIT=0, 16 sorries |
| 8 | `.../HardlyRamified/Family.lean` | 3 | **NOT REPAIRED — start here** |

The build reached target 5687/5695 and stopped in round 8.  Eight targets after
`Family.lean` remain UNSEEN, so budget at least two more rounds after fixing it.

### Round 8, diagnosed but not repaired

All three errors are in `Family.lean` and all three are interface splits, but one
of them is NOT a call-site edit, which is why I stopped rather than guess:

* **5538** — inside `isMultiplicativeType_corner_of_inertiaLevelOneFlag`'s body:
  it calls `isMultiplicativeType_corner_of_connected_of_inertiaLevelOneFlag
  hpodd G habel hflag e₀ …`, but that callee (declared at 5492 in the same file)
  no longer takes `habel` — its binder list runs straight from the instances to
  `(hflag : HasInertiaLevelOneFlag p G)`.  **Mechanical: drop `habel`.**
* **5647** — `mul_comm_of_injective_additive fG.toAddMonoidHom hfG.1` passed
  where `habel : ∀ φ ψ, φ * ψ = ψ * φ` is wanted.  `mul_comm_of_injective_additive`
  (5134) is `(f : Additive M₀ →+ A₀) (hf) (φ ψ) : φ * ψ = ψ * φ`, so the
  two-argument form is an eta-expansion that should still typecheck; the error is
  reported ON `fG.toAddMonoidHom`, so check whether `fG`'s type moved.  Probably
  mechanical, not certainly.
* **5301** — **this is the one with content.**
  `exists_levelOneFlag_of_injective_equivariant` (4420) GAINED two hypotheses,
  `(htor : ∀ w : N₀, ∃ k : ℕ, 0 < k ∧ k • w = 0)` and `(hq : q.Prime)`, and the
  call site passes neither.  So `(fun σ => σ ∈ localInertiaGroup …)` is being
  matched against `htor`, which is why the error reads as `σ` having the type of
  a MODULE element rather than of a Galois element — the message names the wrong
  thing entirely and will send you hunting for an instance problem.  `hq` is free
  (`hp.out`); `htor` is a torsion statement about
  `Additive (ℚᵖᵥ ⊗[𝒪ᵖᵥ] G →ₐ[ℚᵖᵥ] ℚᵖᵥᵃˡᵍ)` — the points of a finite flat Hopf
  algebra form a torsion group — and it is a PROOF, not an argument you can
  forward.  There is machinery at 3686/3697/3716 in the same file that takes
  exactly this shape of hypothesis, and 3716 derives it from invertibility
  (`hinv : ∀ w, ∃ v, w + v = 0`), which for a group of points is where I would
  start.

### What the seven rounds were, in one line each, because the shapes recur

Structure-field split (two complementary fields, merge kept one); seven interface
splits plus a forward reference; two call sites left behind by upstream
*improvements*; a declaration-order tangle needing two block moves; an `omit`
naming a referenced section variable; a lost `end`; and eight duplicate scope
lines from two concurrent hoists.  **Not one was mathematics.**  Every repair is
a call site, a scope line, or a pure permutation of lines, and no statement
changed and no leaf opened or closed in any of the seven modules.
