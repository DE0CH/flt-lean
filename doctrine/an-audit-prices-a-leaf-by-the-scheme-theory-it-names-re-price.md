## AN AUDIT PRICES A LEAF BY THE SCHEME-THEORY IT NAMES — RE-PRICE IT IN ALGEBRA
(2026-07-31, `redX_base_ne_of_isCusp` in `MazurTorsion.lean`.) That leaf's DERIVABILITY
AUDIT was correct in every particular: not derivable from the datum, two explicit
finite-but-not-étale counterexamples, verdict "a successor should expect to BUILD the
cuspidal subscheme as a finite étale scheme, not to find it". It also named the missing
step — *"a section of a separated étale morphism is an isomorphism onto an
open-and-closed subscheme, and over a LOCAL base two such images sharing their closed
point coincide"* — and **mathlib has no such lemma**, which reads as "this leaf costs a
chapter of scheme theory".
The SAME fact stated about algebras is `Algebra.FormallyUnramified.ext_of_iInf`, which
mathlib DOES have: two sections of a formally unramified algebra agreeing modulo `𝔪`
agree, walking the `𝔪`-adic filtration. The leaf's whole non-classical content then fits
in about forty lines. So: **when an audit prices a leaf by a scheme-level statement,
re-state that statement about rings and grep again before believing the price.** This
development is affine over affine wherever it matters (a cuspidal locus is finite over
the base, hence affine), so the translation is usually available.
Two corollaries that cost time here:
- **Carry the new object as an ALGEBRA, not as a closed subscheme.** `Spec` of a finite
  étale `R`-algebra plus a mono into the model plus `range ι.base = (range jZ.base)ᶜ` is
  the same datum with none of the closed-subscheme API, and it is the idiom `X0.lean`'s
  `IsX0Compactification.CuspLocus` already uses (residue ALGEBRAS, not a Galois orbit).
- **`IsReductionBase` carries no `IsNoetherianRing`, deliberately** ("needs no
  `IsDiscreteValuationRing`, `IsFractionRing` or `IsLocalRing` instance"), so mathlib's
  Krull intersection theorem does not apply and `⨅ 𝔪ⁱ = ⊥` has to be proven by hand. It
  is ~40 lines through `padicValRat`: `𝔪 = (q)` from `not_dvd_den`/`mem_of_not_dvd_den`,
  then `v_q` of a nonzero rational bounds the exponent. `q.Prime` is a CONSEQUENCE of
  `IsReductionBase` (its docstring always said so, nobody had proved it) and is now
  `prime_of_isReductionBase`.
**The sibling did NOT fall, and the reason is a trap worth naming: a
FUNCTOR-OF-POINTS datum looks like it has no map of spaces, and it does.**
`card_compl_range_le_card_divisors_specialFibre` counts points of `X'`, while
`IsX0JNeronDatum` relates `X'` to the integral model only through the `RelPoint`
equivalences `spX`/`genX`. First reading: no map `X' → XZ` exists, so no point count can
be transported and the leaf is structurally underivable. **That reading is wrong**, and
it is wrong in the way every "the datum does not carry it" claim in this development
tends to be wrong: `spX` quantifies over ALL `T : Scheme.{0}`, so instantiating at
`T = X'` and feeding it `𝟙 X'` produces an honest morphism
    u := (d.spX strX' (strX' ≫ SpecLoc.special toF) rfl ⟨𝟙 X', Category.id_comp _⟩).1
with `u ≫ xstr = strX' ≫ SpecLoc.special toF`. Naturality (`spX_nat`) makes `spX` a
Yoneda isomorphism, i.e. `X' ≅ XZ ×_{Spec ℤ_(q)} Spec 𝔽_q` with `u` the projection, so
`u` is the base change of the closed immersion `SpecLoc.special toF` and is therefore a
closed immersion — in particular injective on points. That is the missing bridge, and it
is bounded work rather than a wall.
**So: before declaring that a functor-of-points structure cannot express something, run
Yoneda on it by hand — instantiate the universally quantified `T` at the scheme you want
a map out of and feed it the identity.** The equivalences in this development are all
stated over an arbitrary `T` precisely so that they mean what a scheme isomorphism means
(`IsX0JNeronDatum`'s own docstring says so: "by Yoneda this is exactly `X ≅ 𝒳 ×_{ℤ_(ℓ)} ℚ`
… rather than merely comparing point sets"), and the point-set reading throws that away.
