## A LEAF CAN EXIST ONLY ON `merger`, WHICH IS RED — then there is no green base and repairing the cone IS the task

(2026-07-31, `flt-lean-367`.) The standing advice is "reset to `$(cat ~/.flt-release-lake/sha)`,
rsync its build in" — a green base with warm artifacts. That is not always available. This
target (`exists_riemannRochGrowth_of_pointCountRecursion`) was **cut during the release in
progress**: it does not exist at the release sha, and neither does the `CurveGenus.lean` /
`CurveDivisorDegree.lean` / `PrincipalDivisorDegree.lean` divisor vocabulary its decomposition
needs. The only tree carrying them was `merger`, and `merger` mid-release was red in three
unrelated files at once.

All three were the SAME merge-interaction class — one branch hoisting a declaration upstream,
another still editing the file it left, merging cleanly into two copies of one name:

* `NumberField.ramifiedBelow` / `finite_ramifiedBelow` / `finrank_eq_one_of_forall_inertiaDeg_eq_one`
  in `ArtinSymbol.lean`, hoisted to `Density.lean` (whose docstring says so) without the
  matching deletion — and the `ArtinSymbol` copy of the density leaf was a `sorry` while
  `Density.lean` **proves** it, so a duplicate declaration was also a duplicate FRONTIER LEAF;
* `NumberField.restrictNormalHom_frobAt` in `UnramifiedClassFieldExistence.lean`, hoisted to
  `ArtinSymbol.lean` under a DIFFERENT signature, so the three local call sites broke with
  `Application type mismatch` — a shape that reads as a real type error and is not one;
* `omit [Fact p.Prime] in` in `WeilPairingStageB.lean` against a section variable another
  branch had weakened to `[Fact (1 < p)]`.

The lesson is not "fix other people's files". It is that **when your leaf exists only on a red
`merger`, the repair is on your critical path and is part of your task**, and that these
repairs are cheap and mechanical when you recognise the class: grep the duplicated NAME across
`Fermat/`, read both docstrings, and keep the copy whose file the other one's docstring points
at. Do the repair minimally, say so in `to_merger`, and say which copy you kept and why — the
merge worker is fixing the same three defects at the end of the release and needs to know
whether to take yours or its own.

