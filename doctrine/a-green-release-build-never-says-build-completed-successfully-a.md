## A GREEN RELEASE BUILD NEVER SAYS `Build completed successfully` — a publish script that tests for it REFUSES A GREEN TREE

(2026-07-31, release 33, the first publish in six releases.)  The doctrine's own
positive-terminator rule says to require `EXIT=0` **and** a
`Build completed successfully (NNNN jobs)` line before believing a build.  That
rule is right for a MODULE build and it is **wrong for the release build of the
whole project**, for a reason that is structural and permanent:

`Fermat.lean` ends with `#assert_no_sorry fermat_last_theorem`, which throws a
hard error while the frontier is nonempty.  So the root target ALWAYS fails, the
build ALWAYS ends `EXIT=1`, and `Build completed successfully` NEVER appears —
and will not until the project is finished.  Release 32's publish script
(`/tmp/publish32.sh`) opened with

    grep -q 'Build completed successfully' $LOG || { echo "NOT GREEN -- refusing"; exit 1; }

and would have refused release 33's tree, which is green.

**The correct green test for the release build is a NEGATIVE one, and it must be
spelled out:**

    grep -q '^EXIT=1' $LOG                      # the gate fires, so 1 is expected
    grep -q 'SORRY GATE FAILED' $LOG            # and it is THE gate, not something else
    # every remaining `error` line must be the gate or one of its two consequences
    grep -E 'error' $LOG | grep -v 'declaration uses' \
      | grep -vE 'SORRY GATE FAILED|Lean exited with code 1|^error: build failed' | wc -l   # == 0
    grep -q '\[<N-1>/<N>\]' $LOG                # the target count was actually reached

The last line is not decoration: the first three are all satisfied by a build
that died early, because a build that never reached module 4000 has no errors in
modules 4000-5700 either.  **"No errors" and "no errors yet" are the same string.**

