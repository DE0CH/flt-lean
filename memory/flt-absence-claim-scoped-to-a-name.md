---
name: flt-absence-claim-scoped-to-a-name
description: "Not in the pin" verdicts that quote the NAME you would have given a construction miss the construction under mathlib's name; grep the construction's DESCRIPTION instead.
metadata:
  type: project
---

(2026-08-02, `exists_boundarySubscheme_of_projectiveCompactification`.) The leaf was
priced on this, dated and with the search quoted:

> what it needs is the REDUCED INDUCED CLOSED SUBSCHEME, which is the one
> construction here that the mathlib pin does not obviously package (searched
> 2026-07-31: `Mathlib/AlgebraicGeometry/` has `IsClosedImmersion` and
> `Scheme.restrict` for OPENS, but no `Scheme.reducedInduced`).

`Scheme.reducedInduced` really is absent. The construction is not:
`Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean` has

    Scheme.IdealSheafData.vanishingIdeal (Z : Closeds X) : X.IdealSheafData

whose **own docstring** says *"The reduced induced scheme structure on the closed set
is the quotient of this ideal"*, and `IdealSheaf/Subscheme.lean` turns any
`IdealSheafData` into a scheme with a closed immersion (`subscheme`, `subschemeι`,
`range_subschemeι`, plus an `IsClosedImmersion` instance). Two rewrites give the
first two conjuncts of the leaf. The docstring's suggested fallback — build the
subscheme by hand as `Spec` of a product of residue fields — was never needed.

**The rule: an absence claim is only as good as the SPELLING it searched, and the
spelling you reach for is the name YOU would give the object.** Mathlib routinely
files a construction under the machinery it is built from rather than under the
classical name of the thing it constructs. So grep for what the object IS, in a
couple of phrasings — here `grep -rn 'reduced induced' Mathlib/` finds it in one
call, in the docstring of the very definition, while every search for
`reducedInduced`/`Scheme.reducedInduced` returns nothing.

Companion to [[audit-lacks-x-is-about-x]] and
[[theorem-absent-from-pin-may-be-present-in-another-formulation]]: those are about
the theorem being present under a different FORMULATION; this is the cheaper and
commoner case where it is present under a different NAME, and one grep of the prose
settles it.

Corollary about who is misled: a verdict that quotes its `grep` reads as *checked*,
and the quoted command is what the next reader re-runs. Re-running it reproduces the
"absence" for ever. **Quote what you searched FOR, not only where** — "searched for
`reducedInduced`" would have invited the fix; "searched `Mathlib/AlgebraicGeometry/`"
did not.
