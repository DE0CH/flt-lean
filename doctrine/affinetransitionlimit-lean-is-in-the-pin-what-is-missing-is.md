## `AffineTransitionLimit.lean` IS IN THE PIN — what is missing is OBJECT DESCENT, and ONLY that

(2026-08-01, re-verified.) `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` is a
**1371-line development of EGA IV 8 / Stacks 01YT**: inverse limits of schemes with affine
transition maps, `Scheme.nonempty_of_isLimit`, `Scheme.compactSpace_of_isLimit`,
`Scheme.exists_isAffine_of_isLimit`, `Scheme.exists_isOpenCover_and_isAffine`,
`nonempty_isColimit_Γ_mapCocone`, `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`
and `Scheme.preservesColimit_yoneda` (EGA IV 8.14.2). So **"limits / approximation of schemes
are absent from the pin" is FALSE**, and so is the commoner form of the same error,
*"`SpreadingOut.lean` spreads out stalk morphisms only, therefore scheme-level approximation
is unavailable"* — the premise is true of `SpreadingOut.lean` and the conclusion does not
follow.

What is genuinely absent is narrow and should be named precisely, because naming it wrongly
has already cost this project two mis-priced nodes: **object descent** — given `X` locally of
finite presentation over `S = lim Sᵢ`, produce an index `i` and `Xᵢ ⟶ Sᵢ` with
`X ≅ Xᵢ ×_{Sᵢ} S` (EGA IV 8.8.2) — together with **descent of `IsProper` (8.10.5) and of
`Smooth` (11.2.6 / 17.7.8) to a finite stage**. Mathlib has the MORPHISM half of
approximation and not the OBJECT half.

This correction was first made in `ProperPushforward.lean` on 2026-07-29 and sat inside a
leaf docstring in a 2 000-line file, where nobody not already reading that leaf could find
it. **A correction to an absence claim belongs in CLAUDE.md, not only next to the claim it
corrects** — the whole point is that the next agent will look somewhere else.

