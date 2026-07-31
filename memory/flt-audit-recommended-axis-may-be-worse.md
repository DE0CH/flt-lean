---
name: flt-audit-recommended-axis-may-be-worse
description: An IRREDUCIBLE audit's four dead axes can all be right while its RECOMMENDED fifth axis is a falsity trap; look instead for a proven pipeline in this repo that builds the same shape over a DIFFERENT BASE
metadata:
  type: project
---

`exists_x0IntegralCompactifiedModel` (X0.lean) carried a careful audit: four axes
searched and dead (initiality, general relative-curve theory, reducing to its own
consumer, field-wise splitting), all four verdicts correct, plus a RECOMMENDATION —
build the Deligne–Rapoport compactified moduli problem (generalised elliptic curves).
Two independent reviews endorsed the recommendation.

**The recommendation was the worst available option.** A generalised elliptic curve
needs the Néron-polygon fibre dichotomy, which is not definable at this pin without
first gluing `n` copies of `ℙ¹`. Any leaf built over a guessed version of it is an
EXISTENCE claim, so it is FALSE if the polygon clause is too strong (no DR object
satisfies it — the `exists_muType_closure` shape) *and* FALSE if it is too weak (the
enlarged problem need not have a coarse space). And the free-floating rule forbids
writing the structure without wiring it into a leaf, so "just define it" is not open
either.

**The axis that worked was not on the list: the same construction over a DIFFERENT
BASE.** `CurveCompactification.lean` already carries Igusa's pipeline — Nagata for an
affine scheme, then relative normalisation — sorry-free over a FIELD. Exactly two of
its steps are field-specific (finiteness of normalisation wants a Nagata ring, which
`ℤ_(ℓ)` is; "normal + dim 1 ⟹ smooth" is FALSE over a DVR and is precisely Igusa's
theorem). So the leaf cut into a construction leaf plus two named arithmetic leaves,
with `pos_of_isX0Compactification` falling out PROVEN.

**How to apply:** before accepting an audit's recommended axis, ask *which proven
construction in this repo already produces an object of this shape over a different
base or a different field*, and price the base generalisation. An audit enumerates
what its author searched for; "build a new theory" is what is left when that search
fails, and the search is nearly always over the SAME base. See
[[flt-inventory-audits-understate-what-exists]] and
[[flt-missing-machinery-may-be-downstream]] for the two other directions the same
blind spot takes.

**Why:** a recommendation carries the audit's authority without the audit's evidence.
The four dead axes were checked; the fifth was only proposed. Verdict lines and
recommendation lines in the same docstring are not the same kind of claim, and only
the first kind has been tested. See also
[[flt-leaf-cost-estimates-are-hypotheses]] — the same docstring asserted "a smooth
proper geometrically connected curve over `ℚ` has infinitely many points is not in
the tree", which had been PROVEN four days earlier as
`infinite_of_smoothOfRelativeDimension_one`, and that stale sentence alone was
keeping an irrelevant `ℚ`-side hypothesis on three leaves.
