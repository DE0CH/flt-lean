# RELEASE 31 HANDOVER — HELD, and `ModularCurve/X0.lean` is again the only thing red

`main` is UNTOUCHED at `5162faa1` and `~/.flt-release-lake/sha` was NOT written
(it still names `7080929d`).  The integration branch tip is on `merger`.
`~/.flt-loop/queue1` is DELIBERATELY UNCHANGED, still `AUDITED: 5162faa1` —
under a hold `main` does not move, so its audit stamp stays correct and its
tasks stay dispatchable, exactly as release 29 and 30 reasoned.

## WHAT LANDED

All 384 batch branches are ancestors of the tip.  375 were already ancestors
when I started; I merged the nine that were not — `flt-lean-{248, 254, 260,
261, 278, 286, 306, 307, 357}` — and every one has its receipt.

**flt-lean-357 was DECLINED** the class-7 way (`git checkout HEAD -- Fermat/`,
empty payload on purpose, reason in the merge commit), EXCEPT one three-line
proof.  Its 249-duplicate removal from `MazurTorsion.lean` was already in by
another route and merger's copy of that file is 519 lines SHORTER than the
branch's own de-duplicated one, so taking it would have reverted work.  The
exception is `X0GenusOne.finrank_cuspForm_eq_one_of_x0Genus_eq_one`, which the
branch's own note named as the one thing that must survive: `sorry` here, a
three-line proof there over `Fermat.finrank_cuspForm_eq_x0Genus` (X0:63307,
PROVEN, 48000 lines above it).  Frontier −1.  **Read a declined branch's note
for that sentence before you `git checkout HEAD --` anything.**

**flt-lean-261 is a RIVAL CUT and I resolved it against the branch.**  Two
branches closed `MazurCMForm.exists_isCMJInvariant_ne_of_not_equivalent` on
2026-07-31.  Merger's route (`exists_isCMJInvariant_complexEmbedding_eq` plus
the `formPoint` form-to-`ℍ` dictionary) is already integrated and its dictionary
has other consumers; 261's route needed the new leaf
`exists_isCMJInvariant_notMem_range_of_not_equivalent`.  Both leave one leaf, so
the tie-break was "already integrated and consumed".  I kept merger's cut and
did NOT carry 261's leaf.  I DID carry 261's `IsCMJInvariant.map` (PROVEN,
Galois stability) and its 296-line `GaloisTransport` section in
`Isogeny.lean`, because merger's own atomicity audit says stability is "worth
having for other reasons" and the CM survey in CLAUDE.md names that transport as
a missing build.  **`IsCMJInvariant.map` currently has NO consumer** — that is
free-floating and there is a queue task to consume or delete it.  To reverse me,
take `flt-lean-261`'s side of the seven `MazurTorsion.lean` hunks.

## TWO RELEASE-BLOCKING DUPLICATE COLLISIONS, FIXED — AND HOW THEY HID

`tools/merge/xdup.py` reported **0** qualified pairs on this tree when I started
and **21** after I merged the nine branches, none of which touched a Lean
declaration involved.  The difference is that `flt-lean-307` carried a two-line
fix to `xdup.py` itself: its pair test was `a in cone[b]` — *does one module
IMPORT the other* — and Lean's condition is weaker, **a collision happens as
soon as SOME SINGLE module sees both**.  Two siblings under a common consumer
were invisible to it.  Both clusters were hard `environment already contains …`
IMPORT failures, i.e. they stop the module before one line elaborates.

* `Modularity/HeckeAtkinLehner.lean` (196 declarations hoisted out of
  `Interface.lean`) vs `Modularity/HeckeQExpansion.lean` (19, a strict SUBSET),
  with `Interface.lean` `public import`ing both.  Resolved as CLAUDE.md
  prescribes: both modules kept, the larger now `public import`s the smaller,
  and the 19 blocks were deleted from the larger.  `dedup_cross.py`
  body-compared first — 18 identical, and `qCoeff_heckeOp` was the same
  STATEMENT with a different proof, removed by hand keeping the upstream copy.
* `Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean` vs
  `…/CurveDivisorDegree.lean` on `Scheme.ord_one`/`Scheme.ord_inv`, seen by
  `X0.lean`, the only module importing both.  I dropped X0's import of
  `CurveDivisorDegree` (re-deriving flt-lean-357's call rather than inheriting
  it: `PrincipalDivisorDegree.divDegree_eq_zero` is PROVEN with no `f ≠ 0` where
  the other's is a `sorry` leaf that needs it, and all eight
  `CurveDivisorDegree`-only names have ZERO code uses in `Fermat/`).
  **`CurveDivisorDegree.lean` is now imported by NOTHING**, which is the fourth
  invisibility class and must not be left as it is — queued.

**Lesson, and it is in CLAUDE.md now: when a merge brings in a change to a
CHECKER, re-run that checker on the tree you already certified with the old
one.**  Release 30's handover truthfully reported zero duplicates and the tree
had two release-blocking collisions in it.

## WHY IT IS HELD: X0, 39 ERRORS, AND IT IS THE SOLE RED MODULE

`lake build` reached **5670 of 5695** targets with `X0.lean` the only failure;
every other module built, zero errors anywhere else.  The 24 unreached targets
are X0's downstream and are UNSEEN, not fine — they have not compiled since
release 25 and accumulate merge damage invisibly (seventh invisibility class).

Structural checks are all CLEAN on this tree and are not where the problem is:
`parsecheck --all` 0 hard wounds, `scopecheck` 0, `cyclecheck` 0 over 401
modules, `dupstmt` 0 groups, `xdup` qualified 0 pairs.

### The 39, with the root cause of each

   18655  in `exists_jSection_algClosModel` (@18650) -- Tactic `rcases` failed: `x✝ : ?m.22` is not an inductive datatype
   18655  in `exists_jSection_algClosModel` (@18650) -- Unknown identifier `exists_jSection`  [`exists_jSection` is declared at 31418 -- BELOW the use]
   23058  in `not_twoStableLines_of_cmEndomorphism` (@23040) -- unsolved goals
   23059  in `not_twoStableLines_of_cmEndomorphism` (@23040) -- Unknown identifier `ker_cmSqrt_eq_zmultiples_of_stable`  [`ker_cmSqrt_eq_zmultiples_of_stable` is declared at 116090 -- BELOW the use]
   31231  in `exists_jValueOnAffine_of_localModels` (@31146) -- Type mismatch
   31457  in `exists_jLine` (@31455) -- Invalid field `jt`: The environment does not contain `Function.jt`, so it is not possible to pro  [`jt` is DECLARED NOWHERE in the file]
   31457  in `exists_jLine` (@31455) -- Invalid field `jt_natural`: The environment does not contain `Function.jt_natural`, so it is not  [`jt_natural` is DECLARED NOWHERE in the file]
   31458  in `exists_jLine` (@31455) -- Invalid field `jt_model`: The environment does not contain `Function.jt_model`, so it is not pos  [`jt_model` is DECLARED NOWHERE in the file]
   31467  in `exists_jLine` (@31455) -- Invalid field `jt_model`: The environment does not contain `Function.jt_model`, so it is not pos  [`jt_model` is DECLARED NOWHERE in the file]
   36624  in `false_of_stable_of_forall_padicValRat_nonneg` (@36598) -- Tactic `rcases` failed: `x✝ : ?m.589` is not an inductive datatype
   36624  in `false_of_stable_of_forall_padicValRat_nonneg` (@36598) -- Invalid field `exists_isogenyCharacter`: The environment does not contain `WeierstrassCurve.exis  [`exists_isogenyCharacter` is DECLARED NOWHERE in the file]
   38756  in `exists_ringHom_gamma0GITPresentationOver_of_atlas` (@38750) -- Unknown identifier `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux`  [`exists_ringHom_gamma0GITPresentationOver_of_atlas_aux` is declared at 39371 -- BELOW the use]
   38760  in `exists_ringHom_gamma0GITPresentationOver_of_atlas` (@38750) -- Invalid field `toOverSpecQ`: The environment does not contain `Fermat.Gamma0GITPresentation.toOv  [`toOverSpecQ` is DECLARED NOWHERE in the file]
   38761  in `exists_ringHom_gamma0GITPresentationOver_of_atlas` (@38750) -- Unknown identifier `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux`  [`exists_ringHom_gamma0GITPresentationOver_of_atlas_aux` is declared at 39371 -- BELOW the use]
   39381  in `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux` (@39371) -- Unknown identifier `nonempty_gamma0GITPresentationOver_zero`  [`nonempty_gamma0GITPresentationOver_zero` is declared at 42339 -- BELOW the use]
   39385  in `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux` (@39371) -- Unknown identifier `exists_ringHom_gamma0GITPresentationOver_of_atlas_charDvd`  [`exists_ringHom_gamma0GITPresentationOver_of_atlas_charDvd` is declared at 42426 -- BELOW the use]
   39390  in `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux` (@39371) -- Unknown identifier `exists_gamma0GITPresentationOver_zmod`  [`exists_gamma0GITPresentationOver_zmod` is declared at 42031 -- BELOW the use]
   42485  in `isDomain_of_gamma0AtlasOver_zmod` (@42467) -- Tactic `rcases` failed: `x✝ : ?m.209` is not an inductive datatype
   42485  in `isDomain_of_gamma0AtlasOver_zmod` (@42467) -- Unknown identifier `coarseRing_algEquiv_zmod`  [`coarseRing_algEquiv_zmod` is declared at 42854 -- BELOW the use]
   50748  in `axisRestrict_one_ne_zero_of_le_eighteen` (@50710) -- linarith failed to find a contradiction
   51830  in `frickeTailSum_tail_lt_head_of_le_fiftyFour` (@51788) -- linarith failed to find a contradiction
   51835  in `frickeTailSum_tail_lt_head_of_le_fiftyFour` (@51788) -- linarith failed to find a contradiction
   51906  in `frickeTailSum_tail_lt_head_of_eq_sixtyThree` (@51868) -- linarith failed to find a contradiction
   52002  in `frickeTailSum_tail_lt_head_of_eq_seventyFive` (@51966) -- linarith failed to find a contradiction
   75323  in `exists_x0CurveModel_of_base` (@75303) -- Application type mismatch: The argument
   79400  in `universal_classifyPullback_special` (@79386) -- Tactic `rcases` failed: `x✝ : (∃ n, 3 ≤ n ∧ IsUnit ↑n) →
   80977  in `jLineZCoord_injective` (@80962) -- Type mismatch: After simplification, term
   80987  in `jLineZPointOfCoord` (@80987) -- (kernel) declaration has metavariables 'Fermat.jLineZPointOfCoord'
   80993  in `jLineZPointOfCoord` (@80987) -- Tactic `rewrite` failed: Did not find an occurrence of the pattern
   80998  in `jLineZCoord_jLineZPointOfCoord` (@80996) -- unknown metavariable `?_uniq.3261995`
   80999  in `jLineZCoord_jLineZPointOfCoord` (@80996) -- (kernel) declaration has metavariables 'Fermat.jLineZPointOfCoord.eq_1'
   82331  in `exists_x0JGenericOpen_of_curveModel` (@82313) -- Fields missing: `genY_classify`
   82411  in `exists_x0JOpenModel_of_curveModel` (@82375) -- Fields missing: `genY_classify`
   82542  in `exists_x0JNeronDatum` (@82529) -- Type mismatch
   92402  in `exists_addSurjectiveAbelianImage_of_isAdditiveOn_aux` (@92333) -- Unknown identifier `flat_toImage_of_isAdditiveOn`  [`flat_toImage_of_isAdditiveOn` is DECLARED NOWHERE in the file]
   93807  in `exists_addSurjectiveAbelianImage_of_isAdditiveOn` (@93738) -- Unknown identifier `flat_toImage_of_isAdditiveOn`  [`flat_toImage_of_isAdditiveOn` is DECLARED NOWHERE in the file]
  102284  in `exists_atkinLehnerPrym_chabautySemiprimeLevel` (@102265) -- Unknown identifier `noFixedRationalPoint_atkinLehner_chabautySemiprimeLevel`  [`noFixedRationalPoint_atkinLehner_chabautySemiprimeLevel` is declared at 107342 -- BELOW the use]
  116131  in `ker_cmSqrt_eq_zmultiples_of_stable` (@116090) -- Application type mismatch: The argument
  116133  in `ker_cmSqrt_eq_zmultiples_of_stable` (@116090) -- No goals to be solved

### How they group, so you can price the job

**A. NINE DECLARATION-ORDER BREAKS (a use above its declaration).**  These are
relocations that a declaration-level merge cannot carry — `semmerge.py` does not
REORDER — so the new proof landed and the block move did not.  They are
mechanical but they are block moves in a 118 000-line file, which is the
highest-conflict edit there is; do each as its OWN commit touching nothing else,
and verify with the sorted-line-multiset receipt (`git show HEAD:<path> | sort`
against `sort <path>` — identical multiset means a pure permutation).

  * `exists_jSection` (used 18655, declared 31418)
  * `ker_cmSqrt_eq_zmultiples_of_stable` (used 23059, declared 116090) — note
    this one ALSO has two errors of its own at 116131/116133, so it is not only
    a move
  * `noFixedRationalPoint_atkinLehner_chabautySemiprimeLevel` (used 102284,
    declared 107342) — the cleanest single move on the list, start here
  * THE GIT-PRESENTATION CLUSTER, five errors and one tangle:
    `exists_ringHom_gamma0GITPresentationOver_of_atlas` (38750) uses `_aux`
    (39371) and `Gamma0GITPresentation.toOverSpecQ` (39303); `_aux` in turn uses
    `exists_gamma0GITPresentationOver_zmod` (42031),
    `nonempty_gamma0GITPresentationOver_zero` (42339) and
    `..._of_atlas_charDvd` (42426); and separately
    `isDomain_of_gamma0AtlasOver_zmod` (42467) uses `coarseRing_algEquiv_zmod`
    (42854).  So the destination for the 38750/39371 pair is BELOW 42854, and
    42467 must go below 42854 too.  I did NOT attempt this: the region
    38750–43000 has ~24 interleaved declarations and the intended order is not
    recoverable from the text alone.  `git log -m -S` on each name to find the
    commit that relocated it, and re-apply that relocation rather than
    reconstructing an order.

**B. `flat_toImage_of_isAdditiveOn` — DELETED ON PURPOSE, TWO CALL SITES NOT
REWRITTEN.**  Errors at 92402 and 93807.  This is a class-7 interface split: the
leaf was correctly closed (see the note at X0:88800 — it was declaration order,
not mathematics) and its call site inside
`exists_surjectiveAbelianImage_of_isAdditiveOn` (89776) WAS rewritten, while the
two later near-duplicates `exists_addSurjectiveAbelianImage_of_isAdditiveOn_aux`
(92333) and `exists_addSurjectiveAbelianImage_of_isAdditiveOn` (93738) were not.
**The repair is written out for you at 89848–89862**: name the image's
`AbelianSchemeStruct` with `obtain ⟨abB, hBadd⟩ : ∃ abB, …` (NOT a `have` — see
CLAUDE.md on `have` destroying defeq), derive `hπadd`, and then use
`epi_of_surjective_of_isAdditiveOn abJ abB hpi hπadd hsurj` (declared 90289,
above both sites) in place of `flat_toImage_of_isAdditiveOn … ; exact
Flat.epi_of_flat_of_surjective _`.  The two broken proofs currently build the
struct as an anonymous literal inside a `refine`, which is why the fix is a
restructuring rather than a one-line substitution.  **Also: those two later
theorems look like duplicates of 89776 — check whether they should exist at all
before repairing both.**

**C. FIVE `linarith failed` (50748, 51830, 51835, 51906, 52002).**  All in the
Fricke tail-sum numerics (`axisRestrict_one_ne_zero_of_le_eighteen`,
`frickeTailSum_tail_lt_head_of_*`).  These are genuine and are the arithmetic
half of flt-lean-224's `65, 91` numerics work, which release 30 re-spliced over
merger's copy of the theorem.  Suspect the splice took a body against a
different set of ambient hypotheses; diff the four theorems against
`flt-lean-224`'s versions before touching the arithmetic.

**D. THE `jLineZ` METAVARIABLE CLUSTER (80977, 80987, 80993, 80998, 80999).**
`Fermat.jLineZPointOfCoord` elaborates with metavariables, so the kernel rejects
it and its equation lemma, and `jLineZCoord_jLineZPointOfCoord` then fails on an
unknown metavariable.  One root cause, five errors; fix `jLineZPointOfCoord`
first and re-run before reading anything below it.

**E. THE `jt` / `IsJSection` CASCADE (31231, 31457, 31457, 31458, 31467).**
`Invalid field 'jt': the environment does not contain 'Function.jt'` means the
structure the projection is taken from is a FUNCTION, i.e. `exists_jSection`
(31418) returned something of the wrong shape — which is the same wound as the
type mismatch at 31231 in `exists_jValueOnAffine_of_localModels`.  Read from the
top: fix 31231 before 31457.

**F. THE REST, genuine and independent**: 36624
(`WeierstrassCurve.exists_isogenyCharacter` missing — a name in another module,
grep the tree and `git log -m -S` it), 75323 (application type mismatch), 79400
(`rcases` on a non-inductive `(∃ n, 3 ≤ n ∧ IsUnit ↑n) → …` — a hypothesis
turned into an implication by a signature change), 82331 and 82411 (`Fields
missing: genY_classify` — a structure gained a field and two constructors were
not updated; that is the "restated PREDICATE voids the audits" shape, find the
commit that added the field), 82542 (type mismatch), 116131/116133.

### THE FAST LOOP, because a `lake build` is the wrong instrument here

Every dependency of X0 is BUILT on this tree.  So use

    export PATH="$HOME/.elan/bin:$PATH"
    lake env lean -DmaxErrors=400 Fermat/FLT/ModularCurve/X0.lean

which elaborates X0 alone against the existing oleans and does not rebuild the
cone.  **Raise `maxErrors`** — the default is 100 and X0's errors run to line
116133, so a capped run silently hides the tail.  And elaborate the PRE-EDIT
file the same way in parallel and DIFF the two error sets keyed on
`(column, message)` rather than on line — every insertion shifts the tail, and a
naive line-set diff reports dozens of phantom regressions.  See CLAUDE.md's
"VERIFY DIFFERENTIALLY" section, which is written for exactly this file.

## THE QUEUE, AND WHAT I DID AND DID NOT DO TO IT

I did the coverage arithmetic against the MERGER tree and it is complete:
**377 open leaves, 0 uncovered** by a queue of 380 tasks built from
(remaining queue1) + (all of queue2) + 99 newly generated ones.  61 queue1
tasks and 16 queue2 tasks name leaves that are now PROVEN and were dropped
(verified against the frontier scan plus a 21 100-name declaration index, not
by grep).

**I did NOT install that queue**, because `main` did not move: tasks generated
from merger's frontier would name leaves that do not exist on the tree dispatch
runs against, and the `AUDITED:` stamp has nothing new to point at.  The 99 new
tasks are in this release's sentinel `queue` and become queue2.  **Whoever
publishes next should re-run the coverage arithmetic rather than trusting this
paragraph** — it is stamped to this tip and the frontier moves hourly:

    python3 tools/merge/frontier.py --root . > /tmp/frontier.tsv
    python3 tools/merge/gentask.py <uncovered-short-names.json> /tmp/frontier.tsv

Note `gentask.py` matches on `n.split('.')[-1]`, which is the empty string for
the handful of frontier rows whose name ends in a `.` (declarations carrying
explicit universe parameters, e.g.
`cocycleClass_eq_zero_of_eval₁_kerFix_eq_zero.{uK, uW}`).  Strip the trailing
dot from the TSV first or those leaves get no task and the invariant silently
fails by one.

## THE FLEET IS NOT STALLED BY THIS HOLD

queue1 still has 272 dispatchable tasks and 8 live agents.  But it has not been
refilled since release 26 and X0 has been red since release 25, so this is a
slow stall, not a safe steady state.  **The single highest-value thing the next
merge worker can do is finish X0** — not merge more branches.  Nothing else on
this tree is blocking.
