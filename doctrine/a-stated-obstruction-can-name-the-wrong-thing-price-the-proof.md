## A STATED OBSTRUCTION CAN NAME THE WRONG THING — price the proof obligation, not the noun
(2026-07-31, `exists_isAffine_rigidifiedModuliSchemeData_specF`.) `X0.lean` carried, in a
sub-subsection docstring, an explicit and confident diagnosis of why two Katz–Mazur citation
leaves could not be merged into one:
> The honest long-run repair is to state each citation once over a base with `n` invertible and
> derive the four leaves; **that is not done here because this project has no predicate for
> "`n` is invertible on `S`"**, and inventing one is a larger change than the cut this
> sub-subsection is making.
The diagnosis was written by someone who had done the mathematics and it reads as settled. It was
wrong, and the repair cost about 200 lines with no new predicate: **what a base change actually
consumes is a MORPHISM, not a property.** `Spec 𝔽_ℓ ⟶ Spec ℤ[1/n]` exists exactly when `n` is
invertible in `𝔽_ℓ`, so `IsLocalization.Away.lift` delivers the hypothesis and the predicate never
has to be spelled.
The transferable move: **when a docstring blocks a route on "we lack an abstraction for X", write
down the proof obligation X was supposed to discharge and check whether some object already in the
pin discharges it directly.** An abstraction is a way of *quantifying over* instances of a fact; a
single instance needs no quantifier. Two of this file's four leaves were blocked for a month on a
universally-quantified predicate that no proof in the file ever needed universally.
**The second half of the same find, and it is the reusable one: SUBTERMINALITY.** `Spec R` is
subterminal — at most one morphism into it from any scheme — exactly when `ℤ → R` is an
epimorphism of rings, because `Spec ℤ` is terminal. Quotients and localisations of `ℤ` both
qualify, so `Spec 𝔽_ℓ`, `Spec ℤ[1/n]` and `Spec ℚ` are ALL subterminal, in two lines each over
mathlib's `AlgebraicGeometry.ext_to_Spec` plus `RingHom.ext_zmod` / `IsLocalization.ringHom_ext`.
That matters because of a defect this development's moduli structures share: their `universal`
field binds the structure map `(_g : T ⟶ S)` and **never inspects it**, so nothing relates a
classifying map to the base. Descending such a structure along `S' ⟶ S` needs the fibre product
`M ×_S S'`, and the fibre product's universal property needs precisely the compatibility
`m₀ ≫ strM = g ≫ s` that the moduli data cannot supply. Subterminality of `S` supplies it for
free; subterminality of `S'` pins the lifted map's second component and gives UNIQUENESS. So:
**when a fine-moduli structure over one arithmetic base has to be moved to another, check whether
both bases are `Spec` of a `ℤ`-epimorphic ring before concluding that the structure's universal
property is too weak to move.** Over the bases this project actually uses, it always is.
A third thing fell out of the same reading, and it is the cheaper lesson: **a proof written for an
ISOMORPHISM may never use invertibility.** `nonempty_rigidifiedModuliData_of_iso`'s whole
level-structure transport block — `alongInv` for the sections, `nsmul_eq_zero_of_toRelPoint` for
the torsion, `alongEquiv` for `geom_basis` — transcribes verbatim to an arbitrary base change,
because every step is a property of the cartesian square rather than of the map. It is now
`FullLevelStructure.ofBaseChange`. Before transcribing a proof "by analogy" at a weaker hypothesis,
check whether the original ever *used* the stronger one; here the answer was no, twice.
