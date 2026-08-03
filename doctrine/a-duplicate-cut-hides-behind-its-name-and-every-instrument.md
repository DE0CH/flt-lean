## A DUPLICATE CUT HIDES BEHIND ITS *NAME* — and every instrument reports it as ordinary work
(2026-07-31, `flt-lean-398`. Dispatched to prove one leaf; it was a duplicate of another
leaf ~980 lines above it in the same file, and had no consumer. A detector written on the
spot then found two more pairs in the tree, one of them in the same file.)
The duplicate-cut section further up says a duplicate cut "is invisible to every sorry
scan and makes the count go UP". This is the mechanism, and it is worse than it sounds:
**a duplicate cut is not one defect but three at once, and each hides from a different
check, so no instrument reports anything wrong.**
* `lake build` emits `declaration uses 'sorry'` for both — **truthfully**;
* a frontier scan counts two leaves, because there are two `sorry` bodies. It never asks
  whether two of them are the *same statement*;
* the three-part ownership test passes for both, because nobody is working on either;
* `xdup.py` / `checks.py check-dup` are silent, because they match **NAMES**, and the
  names differ. That is what they are for; it is not a bug in them.
So the pair sits there looking like two units of honest open work, and **it draws
dispatches** — this one drew mine.
**Two ways the same statement wears two faces, both measured in `ModularCurve/X0.lean`:**
1. *Different name, identical text.* `exists_affine_rigidifiedModuliScheme_specF` and
   `exists_isAffine_rigidifiedModuliSchemeData_specF` — two agents each performed the
   SAME fusion of the same two citation leaves on the same day, each naming the result
   differently. **A declaration-level merge lands both, because it propagates ADDITIONS
   and never DELETIONS** (the release-27 note above, arriving as a duplicate instead of
   as a hoist-duplication).
2. *Different binder GROUPING or ORDER.* `isReduced_isIntegrallyClosed_ringKrullDim_of_`
   `rigidifiedModuliData_specF` against `isNormalDimOne_rigidifiedModuliData_specF`:
   same hypotheses, same conclusion, and the only textual difference was
   `(N n ℓ : ℕ) (hN) …` against `(N : ℕ) (hN) (n ℓ : ℕ) …`. A `diff` shows a changed
   line; a reader sees two different theorems.
**The check is `tools/merge/dupstmt.py`**, added with this note. It compares declarations
modulo the declaration name, binder-name cosmetics (this project adds and removes a
leading `_` as a hypothesis becomes used or unused), whitespace, and binder grouping —
`(N n : ℕ)` is expanded to `(N : ℕ) (n : ℕ)` before comparison. A second pass additionally
ignores binder ORDER and is reported separately as **REVIEW**, because reordering is sound
only when the moved binders are independent. Default scope is sorried declarations; `--all`
widens it. Run it per release, alongside the name-level `xdup.py` — they answer different
questions and neither subsumes the other.
**Deleting is usually right, and proving one from the other is usually wrong.** The
one-line `exact <the twin> …` is tempting and it leaves a proven theorem that nothing
consumes — free-floating code, which this project forbids. Delete instead, and **keep the
copy with the live call sites**, not the one with the better name or the later date:
keeping the other means a rename plus a call-site edit for no gain. Fold whatever the
deleted docstring said that the survivor's did not into the survivor, and leave a `/-!`
note at the old site so the duplicate is not re-cut — a duplicate that was deleted without
explanation is a duplicate somebody will cut again.
**But check BOTH sides for consumers before reaching for the delete.** The third pair the
detector found — `exists_trivialization_sectionIdeal_at_section` and
`exists_trivialization_sectionIdeal_at` in `ModularCurve/RelativePicard.lean` — has **zero**
consumers on *either* side, so deleting one still leaves a dead leaf and the choice depends
on the consumer that file's owner intends to write. That is the owner's call. Fix the
duplicate in the file you were sent to, report the others.
Corollary for whoever CUTS a leaf: the cheapest prevention is to say, in the docstring,
which classical statement the leaf is **in words** — the rule the Riemann–Roch section
above already gives for a different reason. Both X0 pairs had near-identical prose
docstrings describing the same citation, and in each case that prose was the only thing
that matched; the identifiers shared nothing.
