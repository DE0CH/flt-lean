---
name: flt-sorry-grep-returns-zero
description: Lean writes "declaration uses `sorry`" with BACKTICKS; CLAUDE.md and the doctrine write it with single quotes, so the literal grep they prescribe returns zero and reads as a clean build.
metadata:
  type: project
---

Lean 4 at this toolchain (v4.32.0-rc1) emits

    Fermat/FLT/ModularCurve/X1.lean:3948:8: warning: declaration uses `sorry`

with **BACKTICKS** around `sorry`. `CLAUDE.md` writes the string with single
quotes — `declaration uses 'sorry'` — **35 times**, and
`~/.flt-agent-doctrine.md` **10 times**; neither contains the backtick form
even once (measured 2026-08-02). So every recipe in this project that says
"grep the build log for `declaration uses 'sorry'`" returns **zero** on a log
full of them.

**Why:** an empty result here is indistinguishable from a clean build, and
the recipes that use it are exactly the ones that decide whether a leaf is
open, whether a cut moved the frontier, and whether a release is green. I hit
it in this run: `grep -c "declaration uses 'sorry'" /tmp/x1.log` printed `0`
for a file the same log showed 23 warnings for. Same family as
[[flt-error-count-recipe-returns-zero]] and the lake-not-on-PATH trap — a
check whose failure mode is a confident, quiet, wrong "nothing here".

**How to apply:** grep for a spelling that cannot be wrong —

    grep -c "declaration uses" /tmp/build.log      # quote-agnostic
    grep -ci sorry /tmp/build.log                  # cross-check

and cross-check any count against a comment-stripped source scan
([[flt-frontier-tools-hardcode-staging-root]] for why the scanner also needs
checking). Never let either number stand alone: they answer the same question
by independent routes, and agreement is the evidence.
