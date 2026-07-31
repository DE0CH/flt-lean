# RELEASE 32 HANDOVER — HELD, and `ModularCurve/X0.lean` is down from 39 errors to a short list

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

## WHAT IS STILL RED IN X0, WITH THE DIAGNOSIS

### FIVE `linarith failed` in the Fricke tail-sum numerics — the one real lead

`axisRestrict_one_ne_zero_of_le_eighteen` and three
`frickeTailSum_tail_lt_head_of_*`.  The failing goals are of the shape

    h  : ‖b 4‖ ≤ 3 * √4        (from `hd 4`, after `rw [d4]; push_cast`)
    s4 : √4 < 2.00001
    a✝ : 600003 / 100000 < ‖b 4‖
    ⊢ False

and **the arithmetic is valid**: `3 · 2.00001 = 6.00003 = 600003/100000` exactly,
so `h + 3·s4 + a✝` sums to `0 < 0`.  linarith works over exact rationals, so
boundary-tightness is not the problem; the certificate is purely linear, so
`nlinarith`'s products are not needed either.  That leaves an ATOM MISMATCH —
two `√4`s or two `‖b 4‖`s that print identically and are not syntactically
equal — which is the standing "printed pattern equals printed target" trap, and
which cannot be diagnosed without a compile probe.

I did not attempt it: X0 has no olean, so there is no scratch loop, and each
blind probe is a ~13-minute full elaboration.  **Whoever has an X0 olean can
settle it in seconds** with `set_option pp.explicit true` on one failing goal.
Release 31's lead is also still worth following: these are flt-lean-224's `65,
91` numerics, re-spliced by release 30 over merger's copy of the theorem, so
diff the four theorems against `flt-lean-224`'s versions before touching the
arithmetic.  Note the sibling `have e2`/`e5`/`e9` lines in the SAME proofs are
the same shape and do NOT fail, which is the discriminating fact to start from.

### `exists_jSection` at 18655 — CHECK THIS FIRST, it may already be gone

The v4 run was still in flight when this was written.  The 4770-line hoist and
the `exists_jSection` restatement are both in; if the two errors at 18655
survive, the cause is no longer position and is worth re-reading from scratch.

### The rest

Read the tail of this file's error list from the newest `lake env lean` log.
Everything I could diagnose is in the five commit messages, which are written to
be read in order.

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
