## AN AUDIT'S DEAD AXES ARE EVIDENCE; ITS RECOMMENDED AXIS IS NOT
(2026-07-31, `exists_x0IntegralCompactifiedModel`.) An IRREDUCIBLE docstring listed four
searched-and-dead axes — all four verdicts correct, re-checked twice — and then named a
fifth as "the honest one a successor should take". Two reviews endorsed it. **It was the
worst option available.** It asked for the Deligne–Rapoport compactified moduli problem,
whose Néron-polygon clause is not definable at this pin; a leaf over a guessed version is
an EXISTENCE claim, hence FALSE if the clause is too strong (no DR object satisfies it) and
FALSE if it is too weak (the enlarged problem need not have a coarse space). The
free-floating rule also forbids defining the structure without wiring it into a leaf, so
"just write the definitions" is not a third option.
Verdict lines and recommendation lines sit in the same docstring in the same voice, and
only the first kind has been tested against anything. **A recommendation carries the
audit's authority without the audit's evidence.**
The axis that actually worked was not on the list, and it has a general shape worth
reaching for first: **which PROVEN pipeline in this repo already builds an object of this
shape over a DIFFERENT BASE?** Here `CurveCompactification.lean` carries Igusa's whole
construction — Nagata for an affine scheme, then relative normalisation — sorry-free over a
FIELD, and exactly two of its steps are field-specific (finiteness of normalisation wants a
Nagata ring, which `ℤ_(ℓ)` is; "normal + dimension one ⟹ smooth" is FALSE over a DVR and is
precisely Igusa's theorem). So the citation cut into a construction leaf plus two named
arithmetic leaves. An audit enumerates what its author searched for, and the search is
nearly always over the same base as the leaf.
Second, smaller, and from the same docstring: it asserted that "a smooth proper
geometrically connected curve over `ℚ` has infinitely many points" was NOT in the tree, and
carried an otherwise-useless `ℚ`-side hypothesis through three leaves for that reason
alone. It had been PROVEN four days earlier as `infinite_of_smoothOfRelativeDimension_one`.
**Grep the named missing lemma before pricing anything off its absence.**
