---
name: flt-checker-false-positive-blocks-a-release
description: A structural checker that over-reports costs a release exactly as much as one that under-reports; fix the checker, not the source
metadata:
  type: project
---

CLAUDE.md says repeatedly that a scan which UNDER-reports is worse than no scan,
because it certifies. The mirror is just as expensive and is easier to act on
wrongly: an OVER-reporting scan names a hard blocker in a file that is correct,
and the reflex is to "repair" the source.

Release 34: `parsecheck.py` reported `ModThree.lean:61359: ERROR stray
top-level line ... : by` — a bare `by` in column 0. That is LEGAL Lean 4 when
the previous line ends in `:=` (`theorem foo : T :=` / newline / `by`), verified
by elaborating a three-line scratch, EXIT=0. The tree was right and the checker
was wrong.

**Why:** the checker's whitelist is of tokens that can BEGIN a command, and a
term continuation is not one. Its own calibration note says "if this ever fires
on a file that really compiles, add the starter to the list rather than
weakening the check" — but adding `by` unconditionally would mask a genuine
stray `by`. The precise condition is about the PREVIOUS line.

**How to apply:** before editing a source file a checker calls broken, spend
one scratch elaboration on the construct in isolation. If it compiles, fix the
CHECKER and re-calibrate against a known-green revision (`--git <sha>` must
still report zero). Keying the exemption on the previous code line ending in
`:=`/`=>` keeps the check strong. Same discipline as
[[flt-frontier-tools-hardcode-staging-root]]: verify the instrument before
believing its verdict about the tree.
