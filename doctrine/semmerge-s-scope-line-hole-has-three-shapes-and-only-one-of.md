## semmerge's SCOPE-LINE HOLE HAS THREE SHAPES, AND ONLY ONE OF THEM SAYS "end"

(Same release, four instances in one batch.)  `tools/merge/README.md` already warns
that `namespace`/`section`/`variable` live in the GLUE between declaration blocks,
so taking theirs for a block deletes the glue that followed ours.  What it does not
say is that the three ways this surfaces look nothing like each other:

1. **A lost `end <Name>`** — reported at the END OF THE FILE as
   `Invalid name after 'end': Expected X, but found Y`, thousands of lines from the
   damage.  This is the only shape that mentions scopes at all.
2. **An unclosed `section` whose `variable` stays in scope** — every later
   declaration silently gains a binder, and the errors are `Function expected at`
   and `Tactic introN failed` at the USE sites.  In `MoretBailly.lean` one lost
   `end StepanovDerivationCalculus` produced 39 of these and no scope message
   until the very last line of the file.
3. **BOTH sides' closing `end`s kept** — the second half of the file lands OUTSIDE
   the namespace, so its declarations get the wrong qualified names and consumers
   report `Unknown identifier` on names `grep` finds.

`scopecheck.py` sees all three, and it earns its 93 baseline false positives: every
one of the four real wounds this release was in its DELTA against pre-merge merger,
and two of them were in modules no build has ever REACHED (they sit behind X0), so
nothing else could have found them.  **Difference against the baseline with the LINE
NUMBERS NORMALISED AWAY** — most reports move by exactly the number of lines your
edits inserted, and a naive set-diff calls all of them new.

**Repair direction: restore the missing opener rather than deleting the surviving
closer.** Deleting an `end` can leave a `variable` in scope past where its author
intended, which is shape 2 — i.e. the cheap-looking repair is the bug.

