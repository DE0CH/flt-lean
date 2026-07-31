---
name: flt-consumerless-leaf-is-dead-or-duplicate
description: Grep every open leaf in your file for a CODE consumer before proving anything — a consumerless leaf is dead code or a duplicate, and a RESHAPING orphans both halves of an earlier cut at once
metadata:
  type: project
---

The standing checks ask *is this leaf open* and *is it owned*; neither asks *does
anything consume it*. One grep per open name in the file you are already working
in answers it, and a hit list containing only the declaration's own line plus
docstrings means the leaf is DEAD — either genuinely unreachable, or a duplicate.

    grep -n '<leafName>' <the file>                                  # own line + prose ⇒ dead
    grep -rn '<leafName>' --include=*.lean Fermat/ | grep -v '<the file>:'

Measured 2026-07-31 in `ModularCurve/RelativePicard.lean`: it flagged
`exists_trivialization_sectionIdeal_at_section` and
`exists_trivialization_sectionIdeal_at`, which turned out to be
CHARACTER-FOR-CHARACTER the same proposition — cut out of the same parent a day
apart by two branches, kept by a union-style merge. Confirm a suspected twin by
diffing the two statements with the names elided and whitespace squashed; these
statements are six lines long and the eye does not do it.

**Why:** the orphaning cause is worth recognising on sight. A RESHAPING orphans
BOTH halves of an earlier cut at once. `isInvertibleSheaf_sectionIdeal` was
restated about a bare morphism (`…_of_isSection`) instead of about a base-changed
curve — a good change — and the reshaped parent could then consume neither old
half, since both still spoke of `relSection x` on `curveBaseChange strX g`. This
is [[flt-delete-times-refactor-orphans-a-leaf]] with *refactor on both sides*:
nothing is deleted, nothing conflicts, no scan complains, and the file owes one
theorem three times.

**How to apply:** delete the duplicate, RESHAPE the survivor into the form the
reshaped parent needs, and prove the parent over it — the parent's own docstring
usually already contains the cut. Two riders: a reshaping that ENLARGES the
quantified class VOIDS the inherited faithfulness audit (re-run it, and expect to
add a clause for whatever the old form got for free); and grep the dead name after
deleting, leaving exactly one mention, in the survivor's docstring, saying how to
recover the deleted text.
