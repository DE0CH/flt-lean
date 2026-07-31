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

## The 24 dark targets held exactly one defect, and it was in the first of them

The prediction in the half above was right in shape and generous in size.  The
build stopped at target 5676/5695, `Fermat.FLT.ModularCurve.X1`, with three
errors, and there was nothing wrong behind it: after the repair the whole tree
built.  So six releases of accumulated invisibility cost one repair, not the
three rounds budgeted.  Do not read that as a reason to budget less next time —
X1 is the FIRST module after X0, and the reason nothing else broke is that
nothing else was as heavily edited during the dark window.

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
* **`Fermat/FLT/Mathlib/RingTheory/Localization/BaseChange.lean` is the SECOND
  module unreachable from `Fermat.lean`** (96 lines, 5 declarations).  Unlike
  `CurveDivisorDegree.lean` it has NO sorries, so it hides no frontier leaf and
  is not urgent — but it is free-floating and nothing in the tree records it.
  `cyclecheck.py` is clean; the reachability check that finds these is a BFS of
  the `^(public )?import Fermat` edges from `Fermat.lean`, differenced against
  the `.lean` files on disk, and it is ten lines.
