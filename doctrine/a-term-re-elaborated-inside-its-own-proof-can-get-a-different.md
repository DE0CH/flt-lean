## A TERM RE-ELABORATED INSIDE ITS OWN PROOF CAN GET A DIFFERENT INSTANCE PATH
(2026-07-31, same file, cost one build cycle.) A theorem's statement contained
`TorsionCounting.endRestrict (WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom) (n : ℤ)`.
Writing that SAME text again in the tactic block — as a `set S : … := …` with the
type ascribed — produced a term Lean would not match against the goal, and the
error is the worst possible shape:
    rewrite failed: Did not find an occurrence of the pattern
      (TorsionCounting.endRestrict (Affine.Point.map ↑σ) ↑n) x
      (b.repr ((TorsionCounting.endRestrict (Affine.Point.map ↑σ) ↑n) x)) 0 * …
**The pattern and the target display IDENTICALLY.** The difference is invisible:
`Point.map` returns an `→+` whose `AddZeroClass` is `Affine.Point.instAddZeroClass`,
while the ascription forced `endRestrict`'s argument to be typed through
`Affine.Point.instAddCommGroup.toAddZeroClass`. Same type up to defeq, not
syntactically equal, so `rw` cannot see it and the kernel later reports an
"application type mismatch" between two things it prints the same way.
**The fix is not to write the term at all.** Abstract it as a universally
quantified variable of a `have`, phrased so the CONCLUSION matches the goal, and
let unification supply it:
    have key : ∀ (f : M →+ M), <leaf about f> → ∀ u v, <goal shape mentioning `f u`> := …
    exact key _ (theLeaf …) x y
The `_` is filled from the goal, so the instance path is whatever the STATEMENT
chose, which is by construction the right one. Same trick works for `LinearMap`s
via `AddMonoidHom.toZModLinearMap` (`coe_toZModLinearMap` is `rfl`, so `exact`
crosses the two forms even where `rw` cannot).
General rule: **in a file whose statements mention `WeierstrassCurve.Affine.Point`,
`nTorsion`, or any `Submodule.torsionBy` of them, never retype a term from the
statement — bind it.** A `letI : DecidableEq …` in the statement is the same
hazard in a different suit, which is why those `letI`s are written with
`Classical.typeDecidableEq` and named identically across consumers.
