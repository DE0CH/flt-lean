## "TRANSCRIBE THE ARGUMENT" IS ROUTINELY THE EXPENSIVE OPTION — PRICE THE SIBLING'S *SUBTREE*, NOT THE SIBLING
(2026-08-01, `flt-lean-172`, closing `exists_finiteIndex_divisible_pic` and
`finite_torsion_pic_geom` in `ModularCurve/HyperellipticJacobian.lean`.)
A leaf cut as *"the `Pic⁰` transcription of `<X0 statement>`, which is PROVEN there"* offers
two moves, and the task prompt that dispatched this one described them exactly as the file's
own docstring did: **(a)** build a bridge to the abelian-scheme interface, which closes the
leaves at one stroke, or **(b)** transcribe the sibling's argument, *"the cheaper local move
but it leaves the duplication in place"*.
**(b) was not cheaper, and it is worth knowing why the estimate goes wrong.** The sibling
`exists_finiteIndex_divisible_of_abelianScheme` is a six-line assembly — that is what you see
when you open it — over `exists_discrBound_divisionField_of_abelianScheme`, which is itself a
four-way cut over a torsion field, a Kummer degree bound, Néron–Ogg–Shafarevich and
Hermite–Minkowski, of which exactly one leaf is still open. Transcribing "the Hermite
argument" therefore means re-deriving a field of definition, a discriminant, a degree bound
and a ramification set **for the objects of your own file** — here for a geometric Picard
CLASS, where the sibling has them for a geometric POINT. It is the whole subtree again.
**So the check, and it is one `grep` per name plus one read: open the sibling's PROOF and
list what it cites, transitively, until you reach leaves.** An assembly's length tells you
nothing; what a transcription costs is the *vocabulary* its inputs are stated in, and that is
what does not transcribe. The bridge, by contrast, is ONE comparison theorem and leaves the
arithmetic owed once.
Two riders that made the bridge cheap, and both generalise:
* **Keep the bridge's STATEMENT free of every name from the module you are newly importing,
  and the import can stay NON-PUBLIC.** Spell `Spec (CommRingCat.of ℚ)` rather than `X0`'s
  `SpecQ`, and `RelPoint.pre (specAlgClos ℚ) rfl` rather than its `ratToGeom` — each is the
  abbreviation/definition unfolded, so nothing is lost. The imported module is then needed
  only in PROOF BODIES, which a plain `import` reaches, and its ~100 000 names are not
  re-exported through your module. It also means the new leaf can be read, and proved, by
  somebody who has never opened the module you imported.
* **A `def … deriving Group` type synonym can be COMPLETELY interchangeable with what it
  unfolds to — measure it, do not design around it.** `QbarGal`
  (`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`) versus `Field.absoluteGaloisGroup ℚ` looked
  like the standing type-synonym trap, and a `Subgroup`/quotient transport was budgeted for.
  A four-line scratch (`example : QbarGal = Field.absoluteGaloisGroup ℚ := rfl`, then the same
  for `Subgroup`, for `Finite (· ⧸ H)` and for `σ ∈ H`) compiled in **7 seconds** with every
  case closed by `rfl`, and the transport was deleted from the design before it was written.
  The standing warnings about type synonyms are about when this FAILS; the point is that
  which of the two you are in costs one scratch to find out, and finding out first is what
  decides the shape of the statement.
**And the accounting, stated the way the RECUT rule asks.** `2 → 1` on the two targets, plus
a third leaf closed for free (see the next paragraph), so the module went `22 → 20`. What the
count cannot show is that the surviving leaf mentions no Kummer theory, no discriminant, no
ramification and no finite-index subgroup — it is a Jacobian and a comparison of point groups.
### A RECUT ORPHANS THE LEAVES IT RE-POINTS AWAY FROM, AND ONE OF THEM MAY BE YOUR TARGET'S TWIN
Same run. The 2026-07-31 recut that created these two targets re-pointed
`finite_kummerCochains_pic` onto them and left the leaves it had previously consumed standing.
A comment-stripped consumer scan of `Fermat/` found **four** open-and-consumerless
declarations in that one file — the seventh invisibility class, manufactured by an ordinary,
correct recut rather than by a merge.
One of the four, `geomPic_finite_torsion`, is `{y | n • y = 0}.Finite` where my target is
`Finite {y // p • y = 0}` — **the same proposition in two spellings**, cut a day apart out of
the same node. It closed by `Set.finite_coe_iff.mp` applied to the target I had just proven:
one line, one leaf, no mathematics. Neither a name-based nor a statement-based duplicate scan
pairs those two, because `Set.Finite` and `Finite` are different heads.
So, when you close a leaf: **grep the file for other leaves whose CONCLUSION is your
conclusion in another spelling** (`Set.Finite` / `Finite`, `Nonempty (A ≃+ B)` / `∃ e : A ≃+ B`,
`∃ H, …` / `∀ …`), and **run a consumer scan over the whole cluster you are in**, not only over
your target. Do not delete an orphan that has a live owner — `geomPic_divisible_place` did —
and say in the docstring and to the merge worker which orphans you left standing and why.
