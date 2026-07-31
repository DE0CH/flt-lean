# RELEASE 33 HANDOVER — **PUBLISHED**, and `X0`'s cone is green for the first time since release 25

`main` moved to the commit named at the bottom of this file,
`~/.flt-release-lake/build` holds its artifacts and `~/.flt-release-lake/sha`
names it.  This is the first published release since 27; five were held.

## WHAT LANDED

All 399 branches on the batch list are ancestors of the published `main`.  389
were already ancestors (release 32 banked them under a hold); ten were merged
this run:

| branch | payload | resolution |
|---|---|---|
| `flt-lean-273` | four `sexticThirtySeven` leaves in `MazurTorsion.lean`, two closed | clean; text conflicts unioned |
| `flt-lean-345` | `FullTranslationDatum` hoisted `MazurTorsion` → `IsogenySignature` | clean; deletion verified, 0 duplicates |
| `flt-lean-326` | two local-lift leaves + a two-declaration move inside `Deformation.lean` | clean; move verified above its consumer |
| `flt-lean-316` | the continuous set-theoretic section, brick (ii) | **hand-constructed, see below** |
| `flt-lean-336` | continuous-cohomology cup product (8 new modules) + local Tate pairing | clean; four-declaration hoist verified |
| `flt-lean-346` | the `𝔽_ℓ` rigidification cluster, `exists_affine_rigidifiedModuliScheme_specF` PROVEN | clean |
| `flt-lean-386` | `exists_nonconstant_toAbelianScheme_of_nontrivial_cuspForm` PROVEN over two leaves | clean |
| `flt-lean-396` | `exists_neronExtension_atSpecialGenericPoint` PROVEN over two leaves | clean |
| `flt-lean-356` | the q-expansion cluster | `semmerge.py`, 0 `BOTH-CHANGED` |
| `flt-lean-366` | descent of the KM citation to `ℤ[1/n]` | **DECLINED, see below** |

### `flt-lean-316`: two rival cuts that were COMPLEMENTARY, and taking either whole orphans the other

`exists_obstructionCocycle_smallExtension_deformation` had been cut twice,
peeling DIFFERENT halves.  merger peeled the DEGENERATE branch (`K = ker φ`,
where the small extension is an isomorphism), leaving `..._ne_zero`.
`flt-lean-316` peeled the CONTINUOUS SET-THEORETIC SECTION, proving four lemmas
and leaving `..._of_section`.  The two residual statements are IDENTICAL except
for those two extra hypotheses — so `..._of_section` plus the PROVEN
`D.hasUniformSections` implies `..._ne_zero` by dropping an unused argument.

Kept merger's `by_cases` proof of the parent, transplanted 316's block verbatim
ABOVE `..._ne_zero`, and proved `..._ne_zero` in eight lines.  Everything is
consumed; the count is unchanged at 6 for that module.  **The general shape:
when two branches cut one parent, ask which HALF each peeled before deciding
which one dies — often neither has to.**

### `flt-lean-366`: declined, and the check that decided it took two commands

366 proves `exists_isAffine_rigidifiedModuliSchemeData_specF` over a new leaf
`..._zinv`.  That target was DELETED at release 32 as a duplicate statement of
`exists_affine_rigidifiedModuliScheme_specF`, and `flt-lean-346` — merged
earlier this run — proves the survivor over the BASE-GENERAL
`exists_rigidifiedModuliSchemeData_of_isUnit` at `R = ZMod ℓ`, with **no new
leaf**.  Verified: all six declarations of that chain are `sorry`-free.  So
366 would re-introduce a deduplicated name AND open a leaf where the tree has
none.  Its `IsUnit (n : R)` formulation is 366's own "honest long-run repair"
at a strictly more general base, so the descent is subsumed rather than
outvoted.  Recorded as a decline with `git checkout HEAD -- X0.lean`; its
CLAUDE.md and memory contributions WERE taken.

## `Family.lean`, round 8 — where release 32 stopped

The blocker was `exists_levelOneFlag_of_injective_equivariant` having gained
`(htor : ∀ w, ∃ k, 0 < k ∧ k • w = 0)` and `(hq : q.Prime)` with the call site
passing neither, so the level PREDICATE was matched against `htor` and the error
named a module element where a Galois element was expected.

Release 32 suggested deriving `htor` from finiteness of the point group plus an
antipode inverse.  **The FLAG already gives it, with the explicit exponent
`q ^ n`.**  `hstep` names one generator `x` of `Q (i+1)` with `q • x ∈ Q i`, and
`Q (i+1) = Q i ⊔ closure {x}`, so `q • Q (i+1) ≤ Q i` for EVERY element; induct
from `Q 0 = ⊥` and read off at `Q n = ⊤`.  Two new lemmas,
`nsmul_mem_of_flag_step` and `exists_pos_nsmul_eq_zero_of_flag`, pure
`AddSubmonoid` lattice theory — no Hopf algebra, no inertia, no finiteness.

The other two errors were a dropped `habel` (the callee was strengthened to get
commutativity from `hflag` alone) and **a stray `include hpodd in` sitting on
`mul_comm_of_injective_additive`**, a pure-algebra lemma in which `p` occurs
nowhere; it made the lemma take `Odd p` as its first explicit argument and its
one call site fail with `fG.toAddMonoidHom … is expected to have type Odd ?m`.
Removed the `include` rather than passing `hpodd`.

**Eight consecutive repair rounds across the dark cone, and not one was
mathematics.**  Every repair was a call site, a scope line, a stray modifier or
a pure permutation of lines.  No statement changed and no leaf opened or closed
in any of the nine modules repaired at releases 32 and 33.

## A CROSS-FILE DUPLICATE THAT ONLY THE FIXED `xdup` COULD SEE

`flt-lean-336` vendored `continuous_of_discreteTopology_snd` into the new
`Mathlib/Topology/CompactOpen.lean`, byte-identical to the copy already in
`Mathlib/Topology/Constructions.lean`.  Neither imports the other; both are seen
by `Deformation.lean`.  That is a hard `environment already contains` error and
it is exactly the SIBLING case release 31 fixed `xdup.py` to catch — an
import-chain pair test reports nothing.  Kept the older copy (two consumers) and
gave `CompactOpen.lean` a `public import` of `Constructions.lean`.

**Run every checker you inherit before quoting a previous release's clean
verdict on it.**  Release 30 truthfully reported zero duplicates on a tree that
had two release-blocking collisions in it; the checker was fixed afterwards.

## STRUCTURAL CHECKS ON THE PUBLISHED TREE

* `parsecheck.py --git HEAD` — delimiters OK on every file
* `commentscan.py` over every tracked `.lean` — clean
* `cyclecheck.py` — clean over 409 modules
* `xdup.py` qualified pass — **0** pairs (1 found and fixed, above)
* `dupstmt.py` — 0 exact + 0 reordered + 0 alpha-renamed groups
* `scopecheck.py` over every tracked `.lean` — 167 reports, **differenced
  against the pre-merge tip: ZERO new.**  Do not read the raw count; this tree
  has ~167 legitimate patterns the strict stack model flags.

## THE FRONTIER, AND WHY IT IS 380 AND NOT 377

`frontier.py --root .` gives 382 rows.  Two are `Fermat/SorryGate.lean`, whose
`elab` contains the token inside a STRING LITERAL — special-case that file or
your count is off by two.  Of the remaining 380, the compiler's
`declaration uses 'sorry'` warning set matches **377 exactly, in both
directions**.

The three it does not see are all in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`, and that is the
FOURTH INVISIBILITY CLASS rather than a scanner bug: that module is the one
module under `Fermat/` **not in `Fermat.lean`'s import closure** (401 of 402),
so it is never compiled and can contain anything.  Its three leaves are real,
they are in the frontier, and they are covered — the divisor-degree
reconciliation task that removes the module's rivalry is at **queue position
0**, where release 32 hoisted it.

## QUEUE

Audited against THIS tree's frontier, not against the old `main`:

    queue1  389 -> 377 kept   (12 named no open leaf)
    queue2   13 ->  12 kept   ( 1 named no open leaf), then emptied
    four DUPLICATE-TARGET pairs folded, loser's text kept verbatim under a
      `SUPERSEDES` heading rather than deleted
    three release-32 `PRECONDITION` blocks for `flt-lean-273` stripped — that
      branch is merged now
    installed: 385 tasks, stamped AUDITED: <the published sha>

Coverage invariant re-verified **against the installed file**: 378 distinct
frontier leaf names, 0 UNCOVERED, counting the two held by the one live agent
(`flt-lean-376`).

Method notes that cost something: tokenise with "isalnum or `_` `'` `.`", never
a regex character class; match on the LAST dotted component with a trailing dot
stripped, because rows for declarations with explicit universe parameters end in
`.` and `split('.')[-1]` is then the empty string; and re-verify coverage AFTER
de-duplicating, because a de-duplication is a queue deletion.

## THE ONE PROCEDURAL THING THAT MATTERS MOST

Release 32's own last lesson was that the build tests the WORKING TREE and the
release publishes the COMMIT, and nothing in the pipeline compares them.  Here:
`git status --porcelain` was empty BEFORE the build was launched and again after
it finished, and the published commit is the one that was built.  The only thing
committed after the build is this markdown file, which cannot change Lean.
