## SEVENTH invisibility class: A CLEAN MERGE THAT DOES NOT COMPILE — the interface split

(2026-07-30, release 22, three instances in one batch.) The six classes above are all about
*not seeing work*. This one is about *seeing a merge succeed*. Every check this file prescribes
for a merge — no conflict markers, `git diff --stat HEAD^1 HEAD` non-empty, the sorry counts,
the `declaration uses 'sorry'` warning set — passed on all three, and the tree did not build.

The shape is always the same. **An interface change and its call sites are ONE edit, and a merge
can split them across the conflict boundary.** The half that conflicts gets resolved; the half
that does not conflict lands unexamined; and the two halves now contradict each other.

- `RelativePicard.lean`: `flt-lean-133` CLOSED `nonempty_modTensor_assocPic` by hoisting, deleting
  the leaf and re-pointing the call sites *its base had*. `main` had gained more call sites since.
  Both edits merged without conflict; six calls to a deleted declaration survived.
- `ArtinConductor.lean`: `flt-lean-197` split break POSITIVITY into its own clause, so one theorem
  returns `⟨pos, counting⟩` and another takes two binders. The SIGNATURES were the non-conflicting
  half; the CALL SITES were the conflicted half, resolved to `ours`, still passing one conjunction.
- `Patching.lean`/`Interface.lean`: two owners threaded DIFFERENT hypotheses (`hp5`, `hgen`) through
  the same six-theorem positional argument chain. Signature edits merged cleanly, so the callees
  bind both; each side's call line passes only its own. **Neither `ours` nor `theirs` compiles** —
  and the conflict looks like a trivial whitespace disagreement. Positional argument lists are
  what make this a merge hazard at all.

**Corollary, and it inverts the obvious rule: resolving every conflict to `ours` is NOT a safe way
to decline a payload.** Twice this release it left the tree broken, because the branch's chain
straddled the boundary:
`flt-lean-366`'s three new leaves landed non-conflictingly while the two proven helpers they call
sat in the dropped half (seven live references to nothing); `flt-lean-123`'s hoist inserted 5164
lines into `X0.lean` while `MazurTorsion.lean` kept its copy (duplicate declarations). **To decline
a payload, `git checkout HEAD -- <the files>`** and let the diff against the first parent be empty
on purpose. Say so in the commit message, because an empty payload otherwise reads as the
dropped-merge bug of class six.

**Two checks catch this class before the build, and both cost seconds.**

1. *Duplicate declaration names, WITHIN a file and ACROSS files*, diffed against the previous
   release so the tree's many legitimate same-last-component names in different namespaces do not
   drown the new ones. Two real errors this release: `Gamma0AtlasOver.bcUniversal_transport`
   declared twice in `X0.lean` by two branches whose regions were too far apart to conflict, and
   `Fermat.isInvertibleSheaf_modPullback` declared in two modules one of which imports the other.
   A per-file scan cannot see the second.
2. *Per merge: names declared on the BRANCH but absent from the resolved file, grepped
   (comments stripped) against the resolved file.* This is what found `flt-lean-366`'s breakage
   before a build ran.
3. *A binder RENAMED to `_x` in a SIGNATURE while the body still says `x`.* This is the
   cheapest-to-detect shape of the split and it was live on `merger` at `f6755e85`
   (2026-07-31): `ProperPushforward.lean`'s `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`
   read `(_hm : m.IsMaximal)` while its body still called
   `exists_point_ker_Γevaluation_eq_of_isMaximal S m hm` — `unknown identifier 'hm'`, i.e. the
   whole module red. It arises when a branch reproves a theorem from a new upstream fact (here
   a hoisted `surjective_appTop_of_isIso_appTop_fiber`), so the hypothesis goes unused and gets
   underscored; the signature edit merges cleanly and the body replacement lands in the
   conflicted half. Grep the resolved file for a signature binder `_foo` whose declaration body
   mentions `foo` — seconds, no build, and it catches the whole class.
3. *Per merge: DECLARATION ORDER.* Both checks above ask whether a name is PRESENT. Lean also
   requires it to be present **above its use**, and a merge can get that wrong while every
   presence check passes. Found on `merger` at `9e7f6e4b` (release 27), in `X0.lean`: the branch
   that closed `exists_qExpansion_gamma0GITPresentation` inserted three declarations
   (`isAlgebraic_of_quotient_isMaximal`, `injective_of_not_isAlgebraic_apply`, and the replacement
   leaf `exists_nonConstant_qExpansion_gamma0GITPresentation`) and MOVED
   `isRegularRing_coarseRing_of_gamma0GITPresentation` up above them. The merge landed the new
   proof body at the CONSUMER'S OLD LINE (15535) and the whole helper block 200–400 lines LOWER
   (15743, 15820, 15846, 15933) — so the proof forward-references all four. Nothing is duplicated,
   nothing is missing, the diff against the first parent is fat, and the file cannot compile.
   The branch's own docstrings say what the intended order was ("was MOVED UP … to just above
   `exists_qExpansion_gamma0GITPresentation`", "the strictly smaller replacement for
   `exists_qExpansion_gamma0GITPresentation` immediately below") — **when a docstring says
   "above"/"below"/"MOVED", that is an order assertion to check, not prose.**

   The check is one command per merged file: for each name the branch newly declares, compare
   `grep -n "^theorem <name>"` with the line of every use. A RELOCATION is the trigger — a merge
   resolves a move as an insertion plus a deletion in two independent hunks, and only one of them
   has to land at the old site for the order to invert.

   Corollary for AUTHORS, and it is cheap: **do not relocate a declaration to reach something
   below you if you can re-run its body instead.** `flt-lean-359` needed the same coarse-ring
   package from the same below-it theorem and inlined its twenty-line body rather than hoisting
   it; that version has no move, hence no hunk that can land at the wrong site.

**A HOIST MANUFACTURES THIS CLASS ON ITS OWN, with no second branch involved** (2026-07-31).
The scan a hoist is told to run — the one every "moved verbatim" module docstring in this tree
cites — asks *what does the block REFERENCE*, and it is the right question for whether the move
is a cut-and-paste. It is the wrong question for duplicates, which are about *what already holds
these names*. Moving the `q`-expansion layer out of `Interface.lean` into
`Modularity/HeckeQExpansion.lean` collided on `qCoeff_heckeOp`: the source file had carried a
one-line corollary of the moved block since 2026-07-25, **1500 lines away from it**, so it was in
neither the block nor its reference list, and the mover re-derived it as new. `lake build` says
`has already been declared` and it is a one-line fix — but it costs a full re-elaboration of the
downstream cone, which for `Interface.lean` is forty minutes.

So the hoist checklist has a third item: after cutting the block, **grep the SOURCE file for
declarations DERIVED from it** (anything whose statement mentions a moved name) and decide
per declaration whether it moves too. They sit far from the block by construction — a corollary
is written where it is consumed, not where its input is defined.

And the standing one, which is what caught the rest: **the release build is not optional and its
first failure is not its last.** Fix, rebuild, repeat — FOUR rounds this release, and the reason is
structural rather than bad luck. **The errors are serialised behind each other by the import
graph**, so round *n* only reveals what round *n−1*'s failure was hiding: one interface change
(`IsSwanExponentAt` gaining a third clause) broke a consumer in its own module, found in round 1,
and a second consumer 79 000 lines away in another module from another branch, found only in round
4 after twenty minutes of elaboration. Budget three rounds minimum, and schedule nothing behind the
first green one.

### GET THE WHOLE MODULE'S ERROR LIST IN ONE RUN: `lake env lean -D maxErrors=2000`

(2026-07-31, `flt-lean-58`, measured on `merger`'s `X0.lean`.) The release-build
rule above says budget three rounds because the errors are serialised behind each
other by the import graph. That is true ACROSS modules. WITHIN one module you do
not have to pay rounds at all: `lake build` stops at `maxErrors` (100) and prints
`maximum number of errors … reached, exiting`, but once the module's dependencies
are built you can run the elaborator directly with the cap lifted —

    lake env lean -D maxErrors=2000 Fermat/FLT/ModularCurve/X0.lean

— and get the complete list in ONE elaboration. Here that was **~4.5 minutes** for
a 107 000-line module whose dependency build had just taken **50**, and it turned
"89 sites, cap reached" into the module's real inventory. Do this before reporting
a red module: a capped list is not a list, and the next 40 000 lines of the file
have not been looked at.

Two riders. The cap being reached is itself the tell — grep the log for
`maximum number of errors`. And a PARSE error truncates everything after it, so a
capped-and-truncated log can be wrong about the count in both directions at once.

### AN ORPHANED PROSE BLOCK IS REPAIRED WITH `--`, NEVER BY RE-OPENING IT

Same run, and it cost several build cycles to learn. The doctrine already says a
merge can strand a docstring body without its opener, and that a stray `-/` or an
unterminated `/--` takes the whole module down. What it does not say is how to put
one back, and the obvious repair is a trap:

* **Do not re-open the block with `/-!`.** Block comments NEST, so any `/-` or `-/`
  *inside* the stranded prose — and this project's prose is full of quoted
  delimiters — opens or closes a level and leaves the file worse. I re-opened one
  block and turned 81 errors into 122, twice, because my own explanatory note
  quoted the delimiters it was explaining.
* **`--` line comments are delimiter-safe.** Verified on a three-line scratch:
  `-- a comment with -/ inside it` and `-- another with /- inside it` both
  elaborate clean. So converting a stranded block line-by-line to `--` preserves
  every word and cannot nest. That is the repair.
* **Better still, check whether the block is a DUPLICATE first.** One of the two
  here was byte-identical to a live copy 380 lines below (`diff <(sed -n 'a,bp')
  <(sed -n 'c,dp')` — one command), so the right repair was deletion, not rescue.

**And do not trust a hand-rolled comment scanner over Lean.** Mine reported
`depth 0, no strays` on a file Lean rejected with `unterminated comment`, because
it did not skip string literals; with strings handled it found the opener
immediately. Even then it disagreed with Lean about nesting in the damaged region.
Use the scanner to LOCATE candidates and `lake env lean` to decide.

**Finally, know when to stop.** These wounds are layered: each repair reveals the
next, and the count can go UP because a broken comment was hiding real errors
inside itself. Repairing them is reconstructing another author's prose across a
100 000-line file. If the merge worker is mid-flight on that same file — check its
last few commits — the higher-value move is to REVERT your comment edits, keep your
own payload minimal and conflict-free, and hand over the uncapped error inventory
plus a per-wound diagnosis. That costs them one command instead of a release round,
and it cannot collide with their in-flight repairs.

### WHEN TWO RIVAL CUTS OF ONE LEAF BOTH LAND, THE **CALL SITE** IS THE ARBITER

(2026-07-31, `flt-lean-58`, on `not_forall_galoisScalar_of_cmEndomorphism` in `X0.lean`.)
The section above says how to DETECT an interface split and how to DECLINE a payload. It
does not say what to do when the split is between two rival cuts of the *same* declaration
and both are already ancestors of `merger` — which is the state a prover agent inherits,
long after either author could be asked.

The shape, and it is going to recur wherever this fleet cuts aggressively: branch A SPLITS
a leaf into regimes over a parameter `q` and proves the original by a trichotomy; branch B
NARROWS the same leaf to `q = p`, deletes the parameter and rewrites the hypotheses. Both
are correct alone. The declaration-level merge takes A's binder list and body together with
B's hypotheses, so the body passes `(p : ℤ) • u = 0` where A's regime lemmas want
`(q : ℤ) • u = 0` — and separately B's re-pointed call site passes no `_hq`. Red, with no
conflict marker, in a region neither author's diff looks wrong in.

**Do not try to reconcile the two docstrings — read the CONSUMER's argument list.** A call
site is the one artefact in the file that cannot be ambiguous about which signature is
current: it either elaborates against a signature or it does not. Here
`not_twoStableLines_of_cmEndomorphism` passed eleven arguments with no `_hq`, which settles
it in one `grep` and needs no judgement about which cut is nicer.

Then finish the job the arbitration implies, because it is never only a signature:

* **Re-derive consumerlessness for every declaration the losing cut introduced.** Under the
  narrowing, A's `…_two` was an OPEN leaf with no consumer (a guaranteed phantom dispatch)
  and A's PROVEN `…_unramifiedOdd` plus its arithmetic residue were free-floating. Deleting
  them took the cluster's frontier from 3 open leaves to 1.
* **Quote the recovery command with the sha you deleted from** — `git show <sha>:<path>` —
  and say what would reverse the decision. Deleted *proven* work is cheap to restore and
  impossible to find if nobody wrote down where it went.
* **Say "frontier 3 → 1" in the commit.** A warning-set delta of `−2` from a *repair* reads
  exactly like a regression otherwise.

Corollary for the merge worker, and it is the cheap prophylactic: when the per-declaration
merge reports "both changed the code, kept ours" on a leaf, **also grep that leaf's name for
call sites and diff their argument counts against both sides.** An arity mismatch at a call
site is a two-second check and it is the single tell that separates this class from an
ordinary docstring disagreement.

