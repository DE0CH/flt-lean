## PORTING A ℚ PROOF TO ℚ̄: THE STEPS THAT BREAK ARE THE ONES ABOUT ℚ's RIGIDITY
(2026-07-31, flt-lean-393.) `EllipticScheme.hom_specRat_eq_of_range_eq` — "a
`ℚ`-point of a scheme is determined by its image" — is the load-bearing step of the
ℚ-side Weierstrass bridge, and it rests on `Subsingleton (k →+* ℚ)`: a field has AT
MOST ONE ring map to ℚ, because ℚ is the prime field. **`Subsingleton (k →+* ℚ̄)` is
false** — `AlgebraicClosure ℚ` has an enormous automorphism group — so the ℚ proof
does not transfer, and the ℚ̄ statement needs a residue-field argument (it is
recoverable for SECTIONS: `K → κ(x) → K` being the identity forces `κ(x) → K` to be
the inverse of a bijection, hence unique).
The general shape: when a ℚ-argument is transported to `ℚ̄`, the steps that will
break are exactly those using "ℚ has no automorphisms / is the prime field / is
subsingleton as a target of ring maps". Everything topological or scheme-theoretic
(`Spec K` is a one-point space, connectedness, dominance, the valuative criterion)
transfers verbatim with `ℚ` replaced by any field.
**And the repair may be to delete the step rather than port it.** The zero section
was being matched by a range chase, which is what needed the point-determined-by-image
lemma. There are two ways out, and both were built independently the same day: port
the lemma (`section_eq_of_range_eq_algClos`, the residue-field argument — a `K`-point
that is a SECTION has `K → κ(x) → K` equal to the identity, which forces `κ(x) → K`
to be the inverse of a bijection, hence unique), or **avoid needing it**: for an
abelian scheme presented by its functor of points, TRANSLATION by a section costs no
geometry at all — add the pullback of the section to the UNIVERSAL relative point
`⟨𝟙 A, _⟩ : RelPoint f f`, and the group axioms plus `pre_add` alone show it is an
isomorphism with inverse the translation by the negative. Correcting an arbitrary
isomorphism by the translation that undoes `u(O₁)` matches the origins BY
CONSTRUCTION, and the resulting statement — *every* isomorphism over the base yields
an `IsEllipticIsoOf`, with no zero-section hypothesis — is both stronger and shorter.
The ported-lemma route is the one that landed (`flt-lean-182`, release 26); the
translation route is recorded here because it generalises to any abelian scheme over
any base and needs no residue fields.
**Same trick, same file, one leaf earlier: a functor-of-points endomorphism IS a
morphism of schemes.** `IsCMByRamifiedMaximalOrder.phi` is a family of maps on
`RelPoint d.f g` for every test scheme, and evaluating it at `⟨𝟙 d.E, _⟩` gives a
single `Φ : d.E ⟶ d.E`, with `phi_pre` proving every value is postcomposition with
it (six lines). That is the step that makes such a leaf attackable at all: an
`IsIsogeny` certificate is polynomials in the coordinates, and no polynomial can be
extracted from a family of abstract group maps. **Whenever a leaf's hypothesis is a
`∀ T'`-quantified functorial bundle, evaluate at the universal point FIRST and
restate it with the morphism.**
