## `declaration uses 'sorry'` IS SPELLED WITH BACKTICKS — every literal grep in this file returns ZERO
(2026-08-02, measured, and I hit it myself before noticing.) Lean 4 at this toolchain emits
    Fermat/FLT/ModularCurve/X1.lean:3948:8: warning: declaration uses `sorry`
with **BACKTICKS**. This file writes the string with SINGLE QUOTES — `declaration uses
'sorry'` — **35 times**, and `~/.flt-agent-doctrine.md` **10 times**; the backtick form
appears in neither, not once. So every recipe either document prescribes returns **zero**
on a log that is full of them:
    grep -c "declaration uses 'sorry'" /tmp/x1.log     # -> 0
    grep -c 'declaration uses'         /tmp/x1.log     # -> 23   (the truth)
**This is the worst-shaped failure in the catalogue**, because an empty result is exactly
what a clean build looks like — the same family as `lake: command not found` exiting 127
with an empty log, and as the truncated-log trap. And the counts it feeds are the ones that
decide whether a leaf is open, whether a cut moved the frontier, and whether a release is
green. **Grep quote-agnostically (`"declaration uses"`), and cross-check every count against
a comment-stripped source scan** — the two answer the same question by independent routes,
and it is their agreement that is the evidence, not either number alone.
Corollary for this file: the 45 occurrences are left as they are, because they are prose
naming Lean's warning and rewriting them all is a large diff in the most-merged file in the
tree. Read them as the NAME of the warning, never as a pattern to paste.
