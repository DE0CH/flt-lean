## THE SORRY WARNING IS SPELLED WITH BACKTICKS — every literal grep in this file returns ZERO

(2026-08-02, measured on a green build at toolchain `v4.32.0-rc1`.)  Lean emits

    warning: Fermat/FLT/EllipticCurve/WeilPairing.lean:4295:8: declaration uses `sorry`

with BACKTICKS around `sorry`.  This file quotes it as `declaration uses 'sorry'`, with
straight quotes, in roughly twenty places — including in the recipes that tell you to
validate a frontier scan against the compiler's warning set.  So

    grep -c "declaration uses 'sorry'" build.log        # -> 0, on a build with sorries

returns ZERO on a build that has them, which is indistinguishable from a clean build and
is the same "an empty grep reads as success" failure the truncated-log and
`lake: command not found` notes already describe.  Grep for the stem only:

    grep -c 'declaration uses' build.log
    grep 'declaration uses' build.log | sed 's/:.*//' | sort | uniq -c   # per file

Whenever you compare a scan against "the compiler's warning set", print the count you got
from the log and sanity-check it against a source token count of the same file; two
numbers that are both zero are not agreement.

