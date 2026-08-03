## GENERALISING THE BASE VOIDS EVERY CHARACTERISTIC-`0` SENTENCE IN THE AUDIT
(2026-07-31, `card_relPoint_not_liesIn_le_of_finite_toAffineLine`.) The section above is
about a hypothesis lost at a DECOMPOSITION. This is the same failure at a
GENERALISATION, and it is cheaper to commit and harder to see, because the edit that
causes it changes no hypothesis at all.
`HasDoubleCoverOfAffineLine` encodes "degree `≤ 2`" as *"no field fibre of `φ : U ⟶ 𝔸¹`
has three points"*, and its docstring justifies the encoding **in characteristic `0`** —
honestly, with the hypothesis written down, because the base was `Spec ℚ`. The base was
later generalised to an arbitrary `S`, in a change correctly described as definitionally
inert at `S = SpecQ`, precisely so the predicate could be SPECIALISED to `X_0(169)_{𝔽₃}`.
Nothing in the prose was re-read. In characteristic `p` the encoding does not bound the
degree: `φ : 𝔸¹_{𝔽ₚ} ⟶ 𝔸¹_{𝔽ₚ}`, `t ↦ tᵖ`, is finite of degree `p` and every field fibre
is a SINGLE point, since any `L` receiving a map to `𝔸¹_{𝔽ₚ}` has `char L = p` and
`x ↦ xᵖ` is injective there.
**What survives and what dies is the useful part.** The STATEMENTS survive — the clause
bounds the SEPARABLE degree, a purely inseparable morphism is a universal homeomorphism
and so preserves fibre cardinalities, and over a perfect field a curve purely inseparably
dominating `Y` is a Frobenius twist of `Y`, hence hyperelliptic-or-rational when `Y` is.
The ROUTES die: this leaf's audit prescribed *"the pole divisor has degree `deg φ ≤ 2`"*,
which cannot be derived from the clause and would have been chased forever; and
`AlgebraicGeometry.Scheme.Hom.finrank` — which DOES exist at this pin
(`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`, the degree of a finite flat
morphism, locally constant, with base change) — is the TOTAL degree and is therefore the
one tool a prover will reach for and must not.
So: **when a statement is generalised off a characteristic-`0` base, grep its own audit
for "characteristic", "separable", "degree", "generic fibre" and re-run those paragraphs.**
A cardinality-of-fibres encoding of a degree bound is the commonest casualty. The repair
shape is to restate the leaf in the invariant that survives — here the complement bound
was re-cut as *"at most the largest field fibre of `φ`"*, uniform in `m`, with the
constant `2` recovered as the `m = 2` instance.
Second thing this cost, and it is the standing lesson about absence claims: the leaf also
carried *"blocked — this pin has no `ℙ¹` over a scheme"*. That is now **stale over a
field**. `AlgebraicGeometry.exists_isOpenImmersion_isProper_of_isAffine`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`, PROVEN — Nagata for an
affine finite-type scheme over a field) compactifies `𝔸¹_K = Spec K[t]` into a proper
`K`-scheme, which composed with `exists_unique_extension_of_isSmoothProperCurve` is exactly
the extension the audit called impossible. A blocker recorded against the pin is a
statement with a timestamp; re-check it before costing work off it.
