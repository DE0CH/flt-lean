## WHAT A DECLARATION-LEVEL MERGE CANNOT SEE: DELETIONS, ORDER, AND `open … in`

(2026-07-31, release 27.  `tools/merge/semmerge.py` is the right tool and these are
the three things it structurally cannot do.  All three were live in one batch of 19
branches and none of them shows in a diff, a conflict marker, or `check-dup`.)

**0. A HOIST CAN ALSO MERGE AS A FORWARD REFERENCE, AND THE SYMPTOM IS AN
`Unknown identifier` FOR A NAME DECLARED LATER IN THE SAME FILE** (2026-07-31,
`flt-lean-395`, measured on `merger` at `9e7f6e4b`).  Case 1 below is the hoist
whose *copy* lands twice.  This is the other half: the branch PROVED a consumer
over a declaration it was simultaneously hoisting ABOVE it, the new proof merged
(it is an addition), and the block move did not (it is a reorder).  The consumer
then sits above its input.  Two instances in one file, both fatal:

    X0.lean:15565  obtain ... := exists_nonConstant_qExpansion_gamma0GITPresentation ...
    X0.lean:15956  theorem exists_nonConstant_qExpansion_gamma0GITPresentation      <- 391 lines BELOW
    X0.lean:18083  obtain ⟨js⟩ := exists_jSection        (in exists_jSection_algClosModel)
    X0.lean:30112  theorem exists_jSection                                          <- 12000 lines BELOW

On `main` the same pair is in the right order (`exists_jSection` at 27386, used at
27427), which is the tell that this is merge damage and not a bad branch.

**Do not diagnose it as a missing declaration.**  This file already warns that an
ERRORED declaration reports as `unknown constant`; this is a third cause of the
same message, and the discriminator is one `grep -n`: if the name IS declared in
the file but BELOW the use, nothing errored and nothing is missing — a relocation
failed to merge.  The repair is to move the block, which is the worst shape for a
merge and belongs in its own commit touching nothing else.

**And it is invisible to every check in the list below**: no duplicate name, no
scope imbalance, no missing branch-added declaration, comments balanced.  Only the
build sees it.  Add the cheap positive check instead — for each branch that
relocated a block, grep the RESOLVED file for the moved names and compare their
line numbers against their use sites.

**1. IT PROPAGATES ADDITIONS, NEVER DELETIONS — so a HOIST merges as pure
DUPLICATION.**  `semmerge` iterates over THEIRS' declaration names; a name that is
in the base and in ours but *not* in theirs is simply never considered, and ours
keeps it.  That is right for a branch that dropped something by accident and wrong
for every branch that MOVED something.  flt-lean-86 hoisted ~80 declarations
(`borelZMod` … `numCusps_le_order_qExpansion_norm`, the whole `Gamma0Cusp`
namespace) out of `FreyCurve/MazurTorsion.lean` up into `ModularCurve/X0.lean`;
the X0 copies landed, the MazurTorsion copies survived, and MazurTorsion imports
X0.  Every one of those names would have been `has already been declared`.

**No per-file check sees it, and the obvious cross-file check reports NOTHING.**
`checks.py check-dup` is per file by construction.  A qualified-name cross-file
scan is sound and silent here, because this tree's giant modules contain bare
`end`s that a stack model mis-attributes — from some point in `X0.lean` onward
every name loses its `Fermat.` prefix, so X0's `Fermat.borelZMod` is recorded as
`borelZMod` and does not collide with MazurTorsion's.  What found it was matching
on the LAST COMPONENT.  `tools/merge/xdup.py` now runs both passes: `XDUP`
(qualified, an error) and `XDUP-LAST` (last component, ~7000 hits on this tree, so
a REVIEW list that is only usable **differenced against pre-merge `main`**).  Run
it after every batch; release 27's diff was empty in the qualified pass, which is
the answer you want.

**2. IT DOES NOT REORDER, AND MOVING A DECLARATION ALSO MOVES IT OUT OF SCOPE.**
The README already says a hoisted helper can land below its consumer.  The half it
does not say is worse: `open X in`, `set_option … in` and `open scoped Classical in`
bind to ONE declaration, so relocating a declaration silently changes what is in
scope for it.  Two shapes, both from this release:

* `natDegree_minpoly_weberAlpha_le` (`BinaryQuadraticForm.lean`) took theirs' body
  and ours' position, 4500 lines above the `exists_int_gammaTwo` it calls.  Moving
  it down fixed that and broke it a second way: its old site was inside
  `open _root_.Polynomial in`, its new one was not, so `X` and `C` became unknown
  identifiers — **and the `ℚ⟮…⟯` adjoin notation stopped parsing, which reports as a
  bare `expected token` at a column in the middle of a `have`.**  A parse error that
  names no identifier and no namespace is this.  The branch carried
  `open _root_.Polynomial _root_.IntermediateField in` on exactly that declaration;
  the fix is to carry it with the declaration.
* `geomPic_descent` (`HyperellipticJacobian.lean`) lost `open scoped Classical in`
  entirely.  `semmerge` merges docstrings separately and keeps OURS when ours
  evolved — and an `open … in` line is part of the ATTACHMENT RUN, i.e. part of the
  docstring side.  Symptom: three `failed to synthesize Decidable/DecidableEq` in a
  proof otherwise byte-identical to the branch's.

So after any merge that reports `TOOK-THEIRS` on a declaration, **diff that
declaration's ATTACHMENT RUN, not just its body**, and grep the branch for an
`… in` line immediately above it.

**3. A `whnf` TIMEOUT IS REPORTED AT THE START OF A DOCSTRING — which belongs to the
declaration BELOW it.**  `MoretBailly.lean` reported
`27690:0: (deterministic) timeout at whnf`, and line 27690 is the opening `/--` of a
docstring whose theorem is 130 lines further down.  A `set_option maxHeartbeats … in`
placed on the declaration ABOVE that docstring — the natural reading — changes
nothing, and the run is wasted.  Read the line the error names, see whether it is
`/--`, and if so bump the NEXT declaration.  (The consequent `(kernel) unknown
constant` 700 lines below is the usual cascade; read the log from the top.)

### `flt-frontier.py` UNDER-REPORTS, AND THE QUEUE INVARIANT IS COMPUTED FROM IT

Same release, and it is the more dangerous finding because it is silent and it
shrinks the work the fleet is given.  `flt-frontier.py` reported **5** open leaves
in `Modularity/Interface.lean`; a comment-stripped token scan finds **15**, and two
independent agents' reports say 20-21.  Its total was 321 against a true 333.

`tools/merge/frontier.py` (added here) is the scan that was VALIDATED against the
compiler: on all 25 modules that completed in release 27's first build round its
per-file counts matched the `declaration uses 'sorry'` warning set exactly, 25 out
of 25, including `HyperellipticJacobian` (25) and `MoretBailly` (14).  Use it for
the coverage invariant, and re-validate it the same way — the check is ten lines and
it is the only thing standing between a scanner bug and a release that queues 200
tasks against a 333-leaf frontier.

**IT HARDCODES `ROOT = /home/chend/flt-staging` AND IGNORES ITS ARGUMENTS** (measured
2026-07-31, `flt-lean-115`). Run from a worktree it silently reports the STAGING tree's
frontier, and `python3 tools/merge/frontier.py <your file>` prints the whole staging
scan rather than erroring — so a worker measuring its own delta gets the pre-change
number and concludes it changed nothing. Same trap as
[[flt-hidden-sorries-scans-main-repo]], in the tool the release now depends on. From a
worktree, copy it with `ROOT` rewritten:

    sed "s#/home/chend/flt-staging#$PWD#" tools/merge/frontier.py > /tmp/frontier.py

The tell is that your own new declarations are absent from its output while the count
looks plausible. Cross-check by grepping the output for a name you just added.

**IT HARDCODES `ROOT = /home/chend/flt-staging`, so from a WORKTREE it reports the
MERGE WORKER'S tree and not yours** (2026-07-31, `flt-lean-395`).  Same trap as
[[flt-hidden-sorries-scans-main-repo]], and it is worse here because the output is
per-file with line numbers, so it looks like an answer about the file you are editing.
I had just PROVEN two leaves in `X1.lean` and the scan still listed both — at their
PRE-EDIT line numbers, which is the tell.  A prover checking its own work with it will
conclude the proof did not take.  Either run it with `ROOT` pointed at your worktree,
or verify your own file the way the compiler does — `lake build` and read the
`declaration uses 'sorry'` set.  **Any scanner in `tools/merge/` is the merge worker's
and is rooted at staging by design; check `ROOT` before believing per-file output.**
Two riders that cost real time here:

* **Tokenise task text unicode-safely before matching leaf names against it.**  A
  `[A-Za-z_][A-Za-z0-9_.']*` token regex misses every name containing `ι`, `Ψ`, `₁`
  or `₂`, and this tree is full of them: the naive pass called 59 queue entries
  obsolete, of which 43 named a live leaf under a subscripted name.  Splitting on
  "not `isalnum()` and not `_ ' .`" — minus the bracket characters
  ([[lean-identifier-regex-swallows-brackets]]) — took the false-obsolete count to
  zero.
* `Fermat/SorryGate.lean` contains the token `sorry` twice inside a STRING LITERAL in
  its `elab`.  Any scan must exclude that file or strip string literals.
