## A VACUITY SHIELD CAN BE REMOVED BY A LATER PARAGRAPH OF THE SAME DOCSTRING

(2026-07-31, `jm_eq_jLineZCoord_of_degeneracy`.) Its audit had three findings. (1) and
(2) showed the leaf entails something false. (3) said: *"The leaf is nevertheless NOT
FALSE, because `het` is INCONSISTENT … so this statement is vacuously true."* The LAST
paragraph of the same docstring then read: *"`het` WAS REMOVED FROM THIS SIGNATURE ON
2026-07-30."*

Both were written the same day, by repairs that were each correct. Nobody read them
against each other, and the leaf sat for a day as a FALSE statement with a live
consumer, wearing an audit that said it was safe. The file's own rule had predicted it
verbatim — *"Repairing `etale_of_specLocBase` removes the inconsistency, and AT THAT
MOMENT this leaf turns from vacuously true to FALSE"* — and the prediction fired through
the other available repair (deleting the false leaf rather than fixing it), which the
note did not name.

So: **a vacuity claim names a specific hypothesis, and it expires the moment that
hypothesis is edited. Treat "vacuously true because hypothesis H is inconsistent" as a
claim indexed by `H`, and re-check it against the CURRENT signature — the top of a
docstring is not evidence about the bottom of the same docstring.** Cheap check when
editing any signature: grep the docstring for the removed binder's name.

Corollary found in the same file: **an inconsistent hypothesis makes a PROVEN theorem
useless, not wrong.** `jm_eq_jLineZCoord_of_degeneracy_of_classifyCompat` — advertised as
"the true form, PROVEN, with NO new leaf" — still carried `het`, whose only use had been
deleted with `ofDvd`; the surviving `haveI := het …` was a dead binding. So the "true
form" was vacuous and no consumer could ever have used it. Deleting one unused binder
was the whole repair. **When a theorem is proven but nothing consumes it, check its
hypotheses for one that cannot be supplied.**

