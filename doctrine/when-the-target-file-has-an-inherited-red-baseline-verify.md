## WHEN THE TARGET FILE HAS AN INHERITED RED BASELINE, VERIFY *DIFFERENTIALLY*

(2026-07-31, `flt-lean-112`, on `X0.lean` during the release-27 window, when that
file carried ~193 errors none of which were anybody's current work.)

Every verification rule in this file assumes a green baseline is reachable —
`EXIT=0` plus `Build completed successfully`. Sometimes it is not: a release can
hand you a module that has not built since two releases ago, and then "did my edit
break anything" and "does the file build" are different questions and only the
first is yours. Waiting for someone else to make it green is not an option, and
shipping unverified is the class-7 hazard.

**The differential check answers the first question exactly.** `lake env lean`
writes no `.olean`, so two runs do not race and neither disturbs `.lake`:

    cp <pristine copy of the file> Fermat/.../TargetBase.lean   # a REAL module path
    echo Fermat/.../TargetBase.lean >> $(git rev-parse --git-common-dir)/info/exclude
    lake env lean -DmaxErrors=800 Fermat/.../TargetBase.lean > /tmp/pre.log  &
    lake env lean -DmaxErrors=800 Fermat/.../Target.lean     > /tmp/post.log &
    wait

Then require **post ⊆ pre**, after shifting line numbers by your own diff's
insertion count (`git diff --numstat`). Put the copy at a genuine module path —
the name is derived from the path, so a `module` file elaborates fine there and
its diagnostics carry the *pre-edit* line numbers, which is what makes the two
logs comparable.

Three things that decide whether this works:

* **Do NOT repair the baseline's wounds first.** It is tempting, and it destroys
  the check: one parse error truncates the file, so fixing it unmasks thousands of
  previously-hidden lines and `post ⊆ pre` fails for reasons that have nothing to
  do with you. Repair after the differential, or not at all.
* **Check where the first parse error sits relative to your edit.** If it is
  *below* you, your declarations are still elaborated and the check is meaningful.
  If it is *above* you, the run says nothing about your work and you must fix that
  one wound (and then re-take the baseline).
* **A comment-nesting scan is the cheap companion, and it sees what the compiler
  cannot.** The compiler shows only the FIRST parse error; a character-level
  `/-`/`-/` scan lists them all in one second. Iterating "report first stray, patch
  it in a TEMP COPY, rescan" enumerates the whole set without a single build — three
  wounds here, matching the merge worker's own first entry to two lines.

And the ownership rule that goes with it: **a parse error is a passer-by's to fix,
a 193-error module is not.** Report the list to whoever owns the file, in their
line numbering as well as yours, with the repair for each — a repair chosen by
reading which paragraph belongs to which declaration, since "insert a `/--`" and
"delete the earlier `-/`" both parse and only one of them is faithful.

