## "THE OBJECT CANNOT BE STATED" IS A CLAIM ABOUT ONE DEFINITION, NOT ABOUT THE OBJECT
(2026-07-31, `finrank_cuspForm_eq_x0Genus`.) That leaf sat as a bare `sorry` because three
independent audits agreed it could not be *decomposed*, and their shared reason was an
absence that is genuinely true:
> There is NO genus of a scheme, NO `arithmeticGenus`, NO `geometricGenus`, NO Riemann-Roch
> for schemes, and NO compact Riemann surface anywhere in mathlib at this pin or in
> `Fermat/`. So the intermediate objects the classical proof needs cannot currently be
> STATED, which is why nobody has decomposed this.
Every clause of the absence re-checked out. The inference did not. The audits had searched
for the *classical definitions* of the genus — `dim H¹(X, 𝒪)` and `dim H⁰(X, Ω¹)` — and both
are indeed unwritable here, because the pin has neither coherent cohomology nor a sheaf of
relative differentials for a morphism of schemes. But the genus has a third characterisation,
**Riemann's theorem** `ℓ(D) = deg D + 1 − g` for `deg D ≫ 0`, and all three of *its*
ingredients were sitting in the pin unused: `Scheme.functionField`, `Scheme.ord`
(`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`, added 2025 — the order of vanishing at a
codimension-one point) and `Scheme.Hom.residueDegree`. Ninety lines of definitions later the
genus is nameable, the leaf is an assembly over three named sub-leaves, and the
`Ω¹`-free characterisation is *stronger* for the consumers than the classical one would have
been, because it is exactly the form Abel-Jacobi and point-counting arguments want.
The general lesson, and it is not about algebraic geometry:
- **A "cannot be stated" verdict is only as wide as the DEFINITION the auditor had in mind.**
  Before accepting one, ask what *other* characterisations of the object exist, and price each
  against the pin separately. Equivalent definitions are not equally expressible.
- **Prefer the characterisation whose ingredients exist, even when it is not the textbook
  one.** Uniqueness is what makes that safe: `IsCurveGenus.unique` is 12 lines and it is what
  stops the definition from being a convention a consumer could satisfy by choosing `g`. Ship
  the uniqueness proof with the definition, always.
- **`grep` for the object, then `grep` for its INGREDIENTS.** "Zero files match `genus`" was
  true and told you nothing; `OrderOfVanishing.lean` is what mattered and no audit had opened
  it. This is the same failure as
  [Mathlib states point facts as morphism properties](memory/mathlib-states-point-facts-as-morphism-properties.md),
  one level up: there the theorem was spelled differently, here the whole theory was.
