## A LOST SCOPE LINE REPORTS AS A TYPE ERROR — BALANCE THE FILE BEFORE READING ANY DIAGNOSTIC
(2026-08-02, release 34, four red modules, one root cause between them.)  This file already
records that a merge can drop a `namespace`/`section`/`variable`/`open` line, and that
`scopecheck.py` sees it.  What it does not say is the thing that decides whether you run that
check at all: **the compiler NEVER mentions scopes.**  Every one of these was a lost opener,
and every one of them reported as something else entirely:
| what was lost | what Lean said |
|---|---|
| `section Slices` + `variable {σ} {R} [CommRing R]` (`AdicEval.lean`) | **64 ×** `failed to synthesize instance of type class Semiring R` |
| `section AlgebraicallyClosedIn` + `open CategoryTheory` (`PlaneModelFunctionField.lean`) | `expected token` at the column of a `≫`, and `Unknown identifier IsIso` |
| an attachment run MOVED between two declarations (`PoleOrderValuation.lean`) | `Application type mismatch: the argument ι … expected to have type AbelianSchemeStruct ?m` |
| two types deleted by a rival cut's repair (`RelativePicard.lean`) | `Function expected at RelGroupSchemeStruct … applied to jstr` |
Not one of those four messages contains the words `section`, `namespace`, `variable` or
`open`, and three of the four name a TYPE — so the natural reading is "somebody changed a
signature" and the natural response is to go hunting through branch diffs for a signature
change that does not exist.  **So: when a module is red, run the scope-balance check FIRST,
before reading the errors.**  It is twenty lines, it needs no build, and it either names the
defect outright or costs you nothing.
Two refinements that made it decisive here rather than merely suggestive:
* **Mask block comments CHARACTER BY CHARACTER, and compare the ORPHAN LIST against the same
  file on green main and on each contributing branch.**  A bare `end` closing
  `@[expose] public noncomputable section` is a legitimate orphan in every file in this tree,
  so the raw count is meaningless; what is diagnostic is that a branch has ONE orphan and the
  merge result has FOUR.  `python3 /tmp/r34/bal.py <path>` and `… <branch>:<path>` print the
  open/close PAIRING, so a wrongly-paired `end` (`end Slices` closing `section KeyLemma`) is
  visible even when the totals happen to balance.
* **`section`, `end`, `namespace` are not the whole vocabulary.**  `@[expose] public
  noncomputable section` does not start with `section`, so a `startswith('section ')` scan
  reports every file in this tree as having one orphan close and you will dismiss the real
  ones as noise.  Match on the TOKEN, anywhere in the line's leading modifier run.
### THE REPAIR IS FOUND BY DIFFING THE BRANCH'S ATTACHMENT RUN, NOT ITS DECLARATION
Three of the four were repaired the same way and it is worth stating as a procedure, because
the "which branch is right" question has a mechanical answer here:
1. list the branches whose copy of the file differs in LINE COUNT from main's — in a batch of
   341 that is typically two or three, and they are the only candidates;
2. for each, print the scope pairing.  The branch that BALANCES is the one whose structure the
   merge should have preserved;
3. print that branch's ATTACHMENT RUN — the contiguous block of `--` comments, `@[...]`,
   `set_option … in`, `omit … in`, `include … in` and the docstring immediately above the
   declaration — and compare it with the merged file's.  `semmerge.py` merges docstrings
   separately from code, so an attachment run is exactly what it can move to the wrong
   declaration, and the symptom is an ARITY change (`include f hstr hrange in` on a lemma
   whose call sites were written against `include f hstr in`).
**An attachment run that has moved has TWO victims, and fixing one leaves the other broken.**
In `PoleOrderValuation.lean` the run had migrated from `exists_sub_smul_poleOrd_lt` (where its
own comment says, in as many words, why `hrange` is kept) onto `chartStruct_key` — so
`chartStruct_key` acquired two extra arguments and its call site broke, AND the original lost
its `set_option linter.unusedSectionVars false in`, which is why the build carried two
`automatically included section variable(s) unused` warnings 200 lines apart.  **Read the
comment's TEXT to find its true owner** — it named `exists_poleOrderValuation_of_affineComplement'`
and `hrange`, neither of which `chartStruct_key` mentions.  A misplaced comment is
self-identifying in a way a misplaced `include` is not.
### AND A RIVAL CUT CAN LEAVE A LEAF WHOSE HYPOTHESIS TYPES NO LONGER EXIST
`RelativePicard.lean`'s `universallyClosed_of_relPicZeroGroupScheme` took
`(_G : RelGroupSchemeStruct jstr)` and `(_hincl : IsRelPicZeroIncl …)`, and **both names occur
nowhere else in the tree except in that leaf's own docstring** — the winning cut's repair had
deleted them, and a branch forked before that deletion re-added the leaf (`semmerge.py`
propagates additions and never deletions, so this is the guaranteed outcome, not an accident).
The counts settle it without any mathematics:
    universallyClosed_of_relPicZeroGroupScheme   occ=1   (its own declaration — DEAD)
    isProper_of_relPicZeroGroupScheme            occ=4   declared NOWHERE (prose only)
    universallyClosed_relPicIdentityComponent    occ=4   declared, live
    isProper_relPicIdentityComponent             occ=13  declared, live
**A leaf whose hypothesis TYPE is undeclared is not a leaf at all** — it cannot be stated, let
alone proven — so this is a deletion and not a decision.  The check is one `grep` per name in
the signature, asking whether it is DECLARED and not merely mentioned; a name with a healthy
occurrence count that is declared nowhere (as `isProper_of_relPicZeroGroupScheme` was, four
times, all in docstrings) is the tell that a deletion landed and its prose did not.
### The other half of the same file: RIVAL CUTS BOTH LANDED, ONE PROVEN AND ONE SORRIED
`PlaneModelFunctionField.lean` carried **two copies** of `irreducible_map_algebraicClosure_functionField`
and `exists_planeModel_ringEquiv_functionField_specZMod` — flt-lean-157's PROVEN pair and
flt-lean-156's SORRY-LEAF pair — 80 lines apart, each with its own `end Fermat`.  The file
therefore had one `namespace Fermat` and two `end Fermat`, which is what the balance check
reports, and the duplicate is what a `declaration uses \`sorry\`` count reports as an extra
open leaf.  Keep the PROVEN copy, delete the sorried one, and note that neither
`dupstmt.py` nor `xdup.py` can see this pair: the two declarations have the SAME qualified
name, so it is not a cross-file collision, and one is proven while the other is sorried, so a
scan scoped to sorried declarations sees only one of them.  **A duplicate whose two copies are
one PROVEN and one `sorry`, in ONE file, is invisible to every instrument in this repository
except the scope balance.**

### THE TOOL IS `tools/merge/scopepair.py`, AND IT HAS NOW BEEN VALIDATED AGAINST THE COMPILER
(Same release, second pass.)  The paragraphs above cite `/tmp/r34/bal.py`, which is a temp
path and will not exist for the next reader — this file's own standing rule is that a check
worth running every release should be **a script with a name, not a paragraph**.  It is
`tools/merge/scopepair.py`, it prints the open/close PAIRING (so a wrongly-paired `end` is
visible even when the totals balance), `--quiet` makes it exit non-zero on any report, and it
is calibrated to **0 reports on all 409 `Fermat/**.lean` of green main `280981f1`**.
**It is not merely suggestive: it PREDICTED a fault before the build could report it.**  It
flagged `WeightTwoEigenform.lean` as having an unclosed `section ShimuraAlgebraicity`; the
build then produced, independently,
`Invalid name after 'end': Expected 'ShimuraAlgebraicity', but found 'Fermat'`.  A scan that
agrees with the compiler on a file the compiler has not yet reached is worth running before
every release build, because it is seconds against forty minutes.
### THE WOUNDS ARRIVE IN LAYERS, FOR THE SAME REASON COMMENT WOUNDS DO
Release 34 repaired four scope wounds, built, and found SIX MORE — in modules that had been
red the whole time and had therefore never been compiled.  `lake build` stops at the first red
module in a cone, so every module downstream of a wound is UNSEEN, and its own wounds surface
only after the upstream one is fixed.  **So budget the scope repair as several rounds, exactly
as the release build itself is budgeted**, and do not read "four wounds found and fixed" as a
count of what is wrong with the tree.
The corollary is the useful half: **run the scope scan TREE-WIDE, not on the red files.**  It
needs no build and no oleans, so it sees behind every red upstream at once — which is the one
thing the compiler cannot do.  A tree-wide sweep of 409 files takes about three minutes and it
is what turned this from a per-round hunt into a single pass.
### `git log -S` TIMES OUT ON A 119 000-LINE FILE — DEDUPLICATE THE MERGE PARENTS' BLOBS INSTEAD
To find which branch a merge lost something from, the reflex is `git log -S '<text>' -- <path>`.
On `X0.lean` that did not return in two minutes.  What does work, in seconds, is to search the
BLOBS rather than the history — a batch of 341 merges has far fewer distinct versions of one
file than it has commits:
    git log --format='%P' --first-parent <base>..HEAD | awk '{print $2}' > parents.txt
    while read c; do b=$(git rev-parse "$c:$PATH_" 2>/dev/null) && echo "$b $c"; done \
      < parents.txt | sort -u -k1,1 > ublobs.txt      # 341 -> 107 for X0, 22 for HyperellipticJacobian
    while read b c; do git cat-file blob "$b" | grep -q '<the thing>' && echo "HIT $c"; done < ublobs.txt
Two traps, both hit here.  The file is `"<blob> <commit>"`, so **grepping a COMMIT prefix
against it matches the blob column and silently returns nothing** — iterate and compare
`${b:0:8}` instead.  And a branch that merely *inherited* the text has the same blob as its
base, which is exactly what the dedup collapses: the survivors are the branches that CHANGED
the file, and those are the only candidates.
### TWO NEW SHAPES: A SECTION FUSED WITH ANOTHER, AND A SECTION SPLIT IN TWO
Both were found this pass and neither is the "lost opener" the section above describes.
**FUSED.**  Two branches each had a section carrying the IDENTICAL pair of opens —
`ShimuraAlgebraicity` (5821a6ad, `open ModularForm Matrix.SpecialLinearGroup` + `open scoped
Manifold`) and `SturmFiniteness` (8eb94e36, the same two) — and the merge kept ONE header and
ONE `end`, running the two blocks together.  The tell is that the surviving section's name
matches only the first block's content.  **The repair trap is sharp and I fell into it: adding
the missing `end` at the obvious place — after the last declaration that visibly belongs to the
named section — closes it too early, and the SECOND block then loses the opens.**  The symptom
is `Unknown identifier` for a NOTATION (`MDiff`, `∣[`, `𝒮ℒ`), which reads as a missing import.
So: **before placing an `end`, find the LAST CODE USE of the section's notation** — mask block
comments first, or a docstring quoting `∣[` will send you hundreds of lines too far — and put
the `end` after it.
**SPLIT.**  The mirror: `SinglePlaceBound` in `HyperellipticJacobian.lean` existed on two
branches, one with an extra block appended inside it (29e2ebac) and one without (29ff5516).
The merge took the second's `end PlaceData`/`end SinglePlaceBound`, then the first's extra
block, then ANOTHER `end PlaceData`/`end SinglePlaceBound` — and inserted the third branch's
`section RiemannRochSpaces` header run into the gap.  Three closers too many, one section
opener (`MultiPlaceBound`) lost entirely.  **The arithmetic is what settles it**: count the
openers and closers each NAME needs against what is present, and the deficit tells you exactly
what to insert and delete before you look at a single declaration.
**And the CONTENT is what assigns each block to its section**, not the line numbers: list the
declaration names in each candidate range and grep the branches for them.  Here that showed
`valMax_isPrime`…`exists_chartValue_of_isAlgClosed` sits INSIDE `SinglePlaceBound` on the only
branch that has it, so the `RiemannRochSpaces` header standing in front of it was misplaced —
a fact no amount of reasoning about the merge could have produced.
### AND THE CLASS-7 SPLIT SURFACES HERE TOO: A FALSITY REPAIR WHOSE CALL-SITE HALF WAS DROPPED
`MoretBailly.lean` carried flt-lean-79's repair `(hCne : Nonempty ↥C)` in the SIGNATURE of
`exists_boundarySubscheme_of_projectiveCompactification` and NOT at its call site, so `hZ` was
being passed in the `hCne` slot.  Lean says
`Application type mismatch: the argument hZ has type (Set.range ⇑j)ᶜ.Nonempty but is expected
to have type Nonempty ↥C` — which is the one diagnostic in this whole catalogue that names its
own cause.  **The repair is on a branch and should be recovered verbatim rather than rewritten**:
`git rev-parse <parent>:<path>` over the merge parents, dedup, and grep for the binder NAME
(`hCne`) — here 21 of 21 blobs had it in the signature and exactly one had it at the call site.

