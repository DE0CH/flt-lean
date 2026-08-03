## A LEVEL-GENERIC CUT DECLARED **BELOW** THE SPECIFIC PROOF IT WAS CUT FROM CANNOT BE RE-POINTED AT
(2026-07-31, `flt-lean-230`.) `flt-lean-220` opened the level of the `169` anti-invariance
pair, proved the generic versions, and wrote a note promising the `169` originals were "now
one-line corollaries of the two theorems below" and that re-pointing them was "a two-line
edit". It was not: the generic pair was written where its `65, 91` consumer needed it,
**~8000 lines BELOW the `169` cluster that would have to call it**, and Lean has no forward
references. The follow-up task inherited the "two-line edit" estimate verbatim and was
wrong by an 89-line hoist.
**So when you cut a generic statement out of a specific proof, declare it where the specific
one can REACH it — above, not beside its new consumer — or the dedup it exists for cannot be
taken and the duplicated proof is permanent.** The generic pair's own dependencies decide how
far up it can go; here all five were already above the `169` cluster, so the hoist was legal,
but that is luck and must be CHECKED (grep each dependency's `^theorem` line number) before
anyone promises the follow-up.
Two corollaries. **A "deliberately deferred, a follow-up should do it alone" note is an
estimate, not a plan** — re-derive the cost, since the author deferred precisely because they
did not do it. And **re-pointing orphans the intermediate specialisation**: here
`isTorsion_minusFactor_x0OneSixtyNine` lost its only call site, because the generic theorem
takes the arithmetic hypotheses directly rather than a pre-specialised lemma. Expect that,
and decide explicitly whether it is deleted or re-consumed; a statement-preserving cleanup
commit is the wrong place to delete a declaration that four other docstrings name.
