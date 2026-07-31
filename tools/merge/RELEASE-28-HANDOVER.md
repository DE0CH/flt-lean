# Release 28 — HELD, and exactly why

`main` was **not moved** and `~/.flt-release-lake/sha` was **not rewritten**.
`main` is still `5162faa1` (= the last published release `7080929d` plus tooling
commits, no Lean), and the snapshot under `~/.flt-release-lake/build` still
matches it. Publishing this tree would have replaced a **green** `main` with a
red one and seeded every worktree in the fleet from a snapshot whose oleans do
not match — which is the whole reason the merge batch exists.

`queue1` WAS rewritten, so the fleet is not idle. See *The queue* below for the
one caveat that comes with a held release.

## What landed

**All 249 branches of the batch are ancestors of `merger`.** 206 were already
ancestors from release 27; this release merged the remaining 43. Every merge was
verified non-empty with `git diff --stat HEAD^1 HEAD`. Nothing was declined.

Merges were done at declaration granularity with `tools/merge/semmerge.py`, and
every `BOTH-CHANGED, kept ours` decision was read. Two needed a judgement call:

* `natCast_ne_zero_of_geomBasis` (X0) — semmerge kept OURS (sorried) over THEIRS
  (proven), flagging it. Took theirs. Theirs is weaker (it adds `hP`, `hQ`), but
  the declaration has **no consumers anywhere in the tree**, so the extra
  hypotheses cost nothing and it closes a leaf at zero risk.
* `flt-lean-76` — resolved by RE-APPLYING its relocation rather than merging it
  textually, per its own handover note. See the merge commit; the receipt is that
  X0's sorted line multiset is unchanged.

## THE THREE BLOCKERS, in the order a successor should take them

### 1. `ModularCurve/X0.lean` — 176+ errors (the cap was hit; regenerate)

**It elaborates in 200 seconds, not 35 minutes.** Release 27's handover quoted
~35 min and that number has been wrong for a while; iteration here is cheap and
the file should not be treated as untouchable.

    lake env lean -DmaxErrors=800 Fermat/FLT/ModularCurve/X0.lean

The 100-error-capped distribution from build round 6 was:

    29  Function expected at            18  Unknown identifier
     8  unsolved goals                   8  Application type mismatch
     8  Ambiguous term                   5  Invalid field
     4  rcases … not an inductive datatype
     4  No goals to be solved            4  linarith failed
     3  cannot coerce to sort            2  Invalid projection
     1  (kernel) declaration has metavariables   1  whnf timeout

**Most of `Function expected at` and `Unknown identifier` are CASCADE.** An
errored declaration never enters the environment, so every later use reports as a
missing constant — CLAUDE.md's *an errored declaration disguises itself as a
missing one*. Read from the TOP and re-measure after each fix; do not count them
as independent work.

**Two are declaration ORDER and are the cheapest thing in the file:**

* `exists_qExpansion_gamma0GITPresentation` (~15564) calls
  `exists_nonConstant_qExpansion_gamma0GITPresentation`, declared at **15961** —
  391 lines below. Move the consumer down; it is ~13 lines.
* `exists_jSection_algClosModel` (18106) has the body
  `obtain ⟨js, hjs⟩ := exists_jSection`, and `exists_jSection` is at **30117** —
  12 000 lines below. Cheapest repair is to move the 13-line consumer DOWN past
  30117 after checking its own consumers are lower still. Note CLAUDE.md's
  section *A DECLARATION-ORDER BLOCKAGE IS DISCHARGED BY AN OPEN LEAF ABOVE*
  describes this same pair from the other side — it was a `sorry` leaf then, and
  a branch has since given it a proof that its position cannot support.

**The parse errors are all gone.** Three orphaned docstring bodies were reopened
this release and the whole tree now scans clean under
`tools/merge/commentscan.py`. That matters because one parse error truncates the
file and hides every later error — it is why release 27's count fell only
248 → 193 across nine real repairs.

### 2. `FreyCurve/MazurTorsion.lean` — 249 cross-file duplicate declarations

**Nobody has ever seen these.** The module has not compiled since release 25
because X0 blocks its cone, so they are invisible to `lake build`, to the
`declaration uses 'sorry'` warning set, and to every frontier scan.

    tools/merge/xdup.py .        ->  165  IsogenySignature <-> MazurTorsion
                                      84  X0               <-> MazurTorsion

and `MazurTorsion.lean` `public import`s both (IsogenySignature at line 373).
Each is a hard `has already been declared`.

**It is a hoist that never deleted its source**, and `git` proves it: at the last
green release `7080929d`, `IsogenySignature.lean` declared
`GaloisRepresentation.globalValuationSubring` **zero** times, `MazurTorsion.lean`
declared it, and MazurTorsion did not import IsogenySignature at all. Now both
declare it and the import is there. `semmerge.py` propagates ADDITIONS and never
DELETIONS, so no merge could have removed the originals.

Delete the DOWNSTREAM copies (MazurTorsion's). Not a single range deletion — the
names are scattered over MazurTorsion ~5982–20720 and ~30801–36067. Script it,
and compare bodies before deleting: a first pass found ~143 of 174 candidate
pairs with whitespace-normalised identical bodies; the rest need a decision.

**Why release 27 reported this tree clean:** it differenced `xdup.py` against its
own merge base, which already contained the duplicates. **Difference against the
last GREEN release.** A check whose baseline is itself broken certifies the
breakage.

### 3. `Modularity/Patching.lean` — one theorem that must be DELETED, not proved

`adjoin_residualCharFrob_eq_top_of_isTraceGenerated` (19743) is red, and it is red
because after the 2026-07-31 restatement of `IsTraceGeneratedDeformation` its
conclusion is **no longer derivable from its hypotheses**. So it must not be
`sorry`d — that would manufacture a false leaf with live consumers.

`flt-lean-79` wrote the full prescription into the 60-line docstring above it:
delete the theorem, add the companion hypothesis `hktr` beside each `hgen` binder
on the seven-declaration `Runiv` chain, and feed it to the PROVEN
`adjoin_residualCharFrob_eq_top_of_eq_top` at the one call site. It is a
hypothesis, not a leaf: the frontier does not move.

This is a class-7 interface change across seven signatures in one file. One
commit, and grep every call site afterwards.

## What this release fixed, so it is not re-diagnosed

* **An IMPORT CYCLE that stopped the whole project building.** `flt-lean-389`
  added `HyperellipticJacobian --> X0` under a comment asserting no cycle; the
  cycle is `X0 -> IsogenySignature -> HyperellipticJacobian -> X0`, two hops, and
  `lake` fails on the ROOT target with `build cycle detected`. Broken by moving
  the two `CubeModel` declarations into a new module,
  `Modularity/AbelianCubeModel.lean`. `tools/merge/cyclecheck.py` is the standing
  check; run it before the first build of every release.
* **Four scope-line wounds** from semmerge's documented glue hole — a lost
  `end StepanovDerivationCalculus` (MoretBailly, worth 39 errors on its own), a
  doubled namespace close (MazurNonCMCertificate), a lost `section CMPhiYoneda`
  opener (MazurTorsion), and a namespace splice (MazurNonCMFrobenius).
* **A reordering casualty**: flt-lean-294's consumers landed 2900 lines above
  merger's `stepanovTotalFilt`. Fixed by hoisting the minimal 171-line producer
  block. `MoretBailly.lean` is now GREEN, 0 errors, 15 sorries.
* **Four cross-file duplicates** in MazurNonCMCertificate (the same
  hoist-without-deletion shape as blocker 2, but small enough to fix here).
* **Four comment wounds** — one splice in MazurTorsion, three orphaned docstring
  bodies in X0.

## Tooling added

| script | question |
|---|---|
| `commentscan.py` | nesting-aware; reports UNCLOSED and STRAY **separately**, because a file with one of each balances to zero and `checks.py check-comment` cannot see either |
| `cyclecheck.py` | import cycles among project modules; asserts on a missing source file rather than skipping it |
| `gentask.py` | one queue task per uncovered leaf, quoting the leaf's own docstring |
| `resolve_text.py` | union-resolve conflicted non-Lean files (CLAUDE.md, memory/) |
| `domerge28.sh` | the driver, pointing at the committed tools |

## The queue

`queue1` holds **279 tasks** and satisfies the coverage invariant: every one of
the 332 distinct open leaves is either queued or held by a live agent. 248
obsolete tasks were dropped (97 from queue1, 151 from queue2) — their leaves are
no longer open.

**The caveat a held release forces.** The tasks' line numbers are `merger`'s, and
agents fast-forward to `main`, which is Lean-identical to release 25. Every
generated task therefore opens by telling the agent to run
`git merge --ff-only main`, to check `merger` for the declaration, and to treat a
line-number mismatch as a statement about its checkout rather than about the leaf.
That is the same discipline CLAUDE.md already prescribes; it is simply
load-bearing this cycle. `AUDITED:` is stamped with `main`'s sha so that
`audit_current` holds and dispatch continues.

The first three tasks in `queue1` are the three blockers above.
