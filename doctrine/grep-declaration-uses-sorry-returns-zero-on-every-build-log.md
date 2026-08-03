## `grep "declaration uses 'sorry'"` RETURNS ZERO ON EVERY BUILD LOG — LEAN EMITS BACKTICKS
(2026-08-01, `flt-lean-241`, measured.) Lean 4 writes the warning as
    warning: Fermat/…/File.lean:9220:8: declaration uses `sorry`
with **BACKTICKS**. This file quotes it as `declaration uses 'sorry'`, with straight
quotes, in roughly thirty places — including every recipe that tells you to verify a build
by counting it. Copy that string into a `grep` and you get:
    grep -c "declaration uses 'sorry'" build.log     ->  0        # ALWAYS, on every log
    grep -c 'declaration uses `sorry`' build.log     ->  43       # the truth
**Zero is the most dangerous possible wrong answer here, because it is a plausible one.**
It is exactly what a finished project looks like, exactly what a build that never ran looks
like, and — worst — it makes the standard "did my edit change the count?" check read
`0 → 0`, i.e. **UNCHANGED**, across an edit that opened a leaf. The check most often used
to prove an edit is inert is the check that cannot see the edit. It joins
`lake: command not found`, the truncated log, and the killed build as a fourth way for
"no news" to be indistinguishable from "good news".
**Grep for the delimiter-agnostic form, and require a POSITIVE count:**
    grep -c 'declaration uses .sorry.' build.log            # matches either spelling
    grep 'declaration uses .sorry.' build.log | grep -c '<YourModule>.lean'
The second line matters as much as the first: a whole-log count includes every dependency
(43 here, of which only 22 were the target module), so a per-file claim needs the per-file
filter. And **a count of `0` is never evidence of success** — it is evidence that the
pattern is wrong or the build did not run. Cross-check against a baseline you measured the
same way, on the same log format, before your edit.
Corollary for every "verify with N `declaration uses 'sorry'` warnings" instruction in a
task prompt, and for the ones in this file: the NUMBER is a snapshot of the commit the
prompt was written at (mine said 23; `main` had 22 by dispatch time, one leaf having closed
in between), and the STRING is wrong. Re-measure the baseline yourself, before editing, and
assert *unchanged* rather than *equal to the quoted constant*.
