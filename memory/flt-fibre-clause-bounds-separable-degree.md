---
name: flt-fibre-clause-bounds-separable-degree
description: A "no fibre has n points" clause bounds the SEPARABLE degree, not the degree; a characteristic-0 caveat in an audit becomes load-bearing the moment the statement is generalised to an arbitrary base
metadata:
  type: project
---

`HasDoubleCoverOfAffineLine` (`ModularCurve/X0.lean`) encodes "degree `≤ 2`" as
"no field fibre of `φ : U ⟶ 𝔸¹` has three points", and its docstring justifies
that **in characteristic `0`**. The predicate was later generalised to an
arbitrary base `S` precisely so it could be SPECIALISED to `X_0(169)_{𝔽₃}` —
and in characteristic `p` the encoding no longer bounds the degree.

Witness: `φ : 𝔸¹_{𝔽ₚ} ⟶ 𝔸¹_{𝔽ₚ}`, `t ↦ tᵖ`. Finite of degree `p` (`𝔽ₚ[t]` is
free of rank `p` over `𝔽ₚ[tᵖ]`), yet every field fibre is a SINGLE point, since
any `L` receiving a map to `𝔸¹_{𝔽ₚ}` has `char L = p` and `x ↦ xᵖ` is injective
there. So the clause holds while `deg φ = p`.

What the clause bounds is `deg_sep φ` — the geometric generic fibre. The
statements built on it stay TRUE, because a purely inseparable morphism is a
universal homeomorphism and so preserves every fibre's cardinality; the
predicate also stays faithful over a perfect field, a curve purely inseparably
dominating `Y` being a Frobenius twist of `Y`. Only the PROOF ROUTES die:
`card_relPoint_not_liesIn_le_of_finite_toAffineLine` prescribed "the pole
divisor has degree `deg φ ≤ 2`", which cannot be derived, and
`AlgebraicGeometry.Scheme.Hom.finrank` (which DOES exist at this pin,
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`) is the total degree and is
therefore the wrong invariant to reach for.

**Why:** the audit was written when the base was `Spec ℚ` and said so honestly.
Generalising the base is a one-line edit that no reviewer reads as a change to
the mathematics, and it silently voids every characteristic-`0` clause in the
prose. Same shape as [[flt-decomposition-drops-a-hypothesis]]: the docstring
still reads as fully audited.

**How to apply:** when a statement is generalised from `Spec ℚ` (or any
characteristic-`0` base) to an arbitrary base, re-read its audit for the words
"characteristic", "separable", "degree", "generic fibre" and re-run it — a
cardinality-of-fibres encoding of a degree bound is the commonest casualty.
And the fix is usually to restate the leaf in the invariant that survives
(here: bound the complement by the largest field fibre, uniformly in `m`,
rather than by the constant `2`).
