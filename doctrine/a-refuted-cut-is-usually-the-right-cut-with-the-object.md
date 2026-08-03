## A REFUTED CUT IS USUALLY THE RIGHT CUT WITH THE OBJECT MANUFACTURED
(2026-07-31, `nonempty_cubeModel_of_isAmpleSheaf_cube`.) Two docstrings in this
development record the embedding/forms split of a projective-embedding leaf as **FALSE**,
with a cheap counterexample: `E : y² + y = x³ − x`, `E(ℚ) ≅ ℤ`, `coords n = (1, n³, n⁶)`
is an injection into `ℙ²(ℚ)` compatible with `[−1]` whose height `6 log|n|` breaks the
parallelogram law. Both were right about the cut they described. Neither noticed that the
falsity is **not a property of the axis** — it is a property of `coords` being an
EXISTENTIALLY QUANTIFIED FUNCTION.
Once `coords` is *defined* from the sheaf — here `ptSectionValue M (φ P) (s i)`: pull the
section back to `Spec ℚ`, read it through a trivialization, land in `ℚ` — the same split
along the same axis is true, and the counterexample cannot be instantiated because
`n ↦ (1 : n³ : n⁶)` is not the restriction of a morphism given by global sections. The
diagnostic question is therefore not *"is this axis faithful"* but:
> **Does the leaf's conclusion CONSTRUCT the object, or merely ASSERT one exists?**
An asserted object obeys only the properties written beside it, so a refutation just
picks a rogue instance. A constructed one inherits everything its ingredients satisfy,
and no rogue instance exists to pick. **So a recorded refutation of a cut is evidence
about the STATEMENT, never about the axis** — before accepting one, check whether the
object it refutes could be manufactured instead.
The corollary that made this a net gain rather than a rename: a manufactured `coords`
lets a hypothesis become a THEOREM. `coords_ne_zero` here is derived from base-point
freeness stated on `J` about the sheaf, mentioning no coordinates at all. Not every
field converts — `injective_of_smul` stayed one line of algebra over a separation clause,
and the honest thing is to say so in the commit message rather than to dress it up.
**And when the old note names the missing clause, take it literally.** The docstring said
the split needed a SPANNING hypothesis (projective normality) or it would still be false.
That was correct and it is not an extra assumption: `L^{⊗n}` on an abelian variety is very
ample AND projectively normal at the same threshold `n ≥ 3` (Mumford §6 Application 1;
Koizumi), so the two clauses of the embedding half are one classical theorem. A "the cut
needs clause X" note is a specification, not a warning to stay away.
**A Lean technique worth reusing: over `Spec` of a FIELD, carry the trivialization as a
GLOBAL iso `N ≅ modUnit`, never as a restriction `N|_U ≅ 𝒪_U`.** Then "the section does
not vanish at the point" becomes "the section is nonzero in `k`" in three rewrites —
`nonvanishingAt_of_iso`, `nonvanishingLocus_modUnit`, and `Scheme.basicOpen_of_isUnit` /
`Scheme.basicOpen_zero` (a basic open of a field's spectrum is `⊤` or `⊥`) — with no
`trivializedSection`, no stalk, no germ, and no `PrimeSpectrum` topology. The restriction
form costs all of that plus the identification `Γ((⊤ : Opens), ⊤) ≅ Γ(Spec k, ⊤)`. Since
`Pic(Spec k) = 0` the global form is free to ask for, so ask for it in the leaf.
