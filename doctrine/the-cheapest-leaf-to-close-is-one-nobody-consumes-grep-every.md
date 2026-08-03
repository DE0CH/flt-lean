## THE CHEAPEST LEAF TO CLOSE IS ONE NOBODY CONSUMES — grep every open leaf in your file for a CODE consumer, first

(2026-07-31, `RelativePicard.lean`, and it was worth two leaves in ten minutes.)
The standing checks ask *is this leaf open* and *is it owned*. Neither asks *does anything
use it*, and a leaf with no consumer is either dead code or a duplicate. One `grep` per open
name in the file you are already in settles it, and the arithmetic is unusual: a hit list
whose only entries are the declaration's OWN line and some docstrings means the leaf is
consumerless.

    grep -n '<leafName>' <the file>            # own decl line + prose only  ⇒  DEAD
    grep -rn '<leafName>' --include=*.lean Fermat/ | grep -v '<the file>:'

Here that flagged `exists_trivialization_sectionIdeal_at_section` and
`exists_trivialization_sectionIdeal_at` at once — and they turned out to be
**character-for-character the same proposition**, cut out of the same parent a day apart by
two branches and kept by a union-style merge. Confirm a suspected twin mechanically rather
than by eye, since these statements run to six lines:

    sed -n 'A,Bp' F | sed 's/<nameA>/NAME/' > /tmp/a; sed -n 'C,Dp' F | sed 's/<nameB>/NAME/' > /tmp/b
    diff <(tr -s ' \n' ' ' < /tmp/a) <(tr -s ' \n' ' ' < /tmp/b)

**What had orphaned them is worth recognising on sight: a RESHAPING orphans BOTH halves of an
earlier cut at once.** `isInvertibleSheaf_sectionIdeal` had been re-stated about a bare
morphism (`…_of_isSection`) instead of about a base-changed curve — a good change, and it made
the reshaped parent unable to consume *either* old half, since they still spoke of
`relSection x` on `curveBaseChange strX g`. That is `DELETE × REFACTOR` with *refactor on both
sides*: nothing is deleted, nothing conflicts, no scan complains, and the file silently owes
one theorem three times.

The repair is mechanical once seen, and it is the good kind of −2: **delete the duplicate,
RESHAPE the survivor into the form the reshaped parent needs, and prove the parent over it.**
Here the parent's own docstring had already written down the cut (`by_cases` on
`z ∈ Set.range σ.base`, on-image = the leaf, off-image = an already-proven lemma), so the
proof was six lines. Two riders:

* **a reshaping that ENLARGES the quantified class voids the inherited faithfulness audit** —
  "every proper smooth relative curve" is strictly more than "every base change of a fixed
  one". Re-run it. Here both witnesses survived verbatim *because they had always been stated
  as curves over a base rather than as base changes*, and one clause had to be ADDED, for the
  hypothesis the old form got for free from `relSection` being a section by construction;
* **check the deletion is clean by grepping the dead name afterwards.** The only surviving hit
  should be the sentence in the survivor's docstring that records the deduplication — and say
  in it how to recover the deleted text (`git show <commit>^`).

