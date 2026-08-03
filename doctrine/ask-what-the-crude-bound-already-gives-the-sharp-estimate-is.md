## ASK WHAT THE CRUDE BOUND ALREADY GIVES — the sharp estimate is usually the wrong thing to make cheap

(2026-07-31, `taylor_of_isFontainePresentation` in `ModThree.lean`.) That leaf carried
THREE successive route notes, written on two different days by two different owners, each
of which removed machinery the previous had called unavoidable — and all three still
over-bought, because all three were estimating the cost of the same *shape* of argument:

1. write a Hasse-derivative API for `MvPowerSeries` (the pin has one only for univariate
   `Polynomial`), plus `MvPowerSeries.subst`, and bound each `|r| ≥ 2` term of
   `P(w+μ) = Σ_r (∂^[r]P)(w)·μ^r` using `r!·∂^[r]P = ∂^r P` and `3 ∣ r! → |r| ≥ 3`;
2. *(sharpening)* do the Hasse theory for `MvPolynomial` instead, since `mk_adicEval`
   reduces the whole statement to the degree-`< n+1` truncation;
3. *(sharpening)* only the terms of `μ`-degree `≤ 2` need a divisibility statement, and
   those follow in three lines from `pderiv_eq` and `coeff_pderiv` — "what remains is the
   EXPANSION itself, an identity in `𝒪₃ᵥ[[X ⊕ Y]]`", via `MvPowerSeries.subst`.

Note (3) is *correct*, is the observation that unlocked the leaf, and STILL named the
wrong residue. The expansion is not an identity anybody has to write. What closed the
leaf was:

* the CRUDE first-order estimate — remainder in `(μ)²`, **no hypotheses at all**, one
  `MvPolynomial.induction_on` with one nontrivial case; then
* a single case split per monomial, because the crude estimate is short by exactly one
  factor of `3`: either the COEFFICIENT supplies it (some exponent prime to `3` ⟹ that
  exponent is a unit ⟹ `coeff ∈ (3)`), or the monomial is `g(X³)` and the SUBSTITUTION
  supplies it, since `(w+μ)³ − w³ = 3w²μ + 3wμ² + μ³` and the crude estimate applied at
  the cubed coordinates already lands where it must.

No divided powers, no Hasse derivatives, no `subst`, no `𝒪₃ᵥ[[X ⊕ Y]]`. ~200 lines, all
of it statements about `MvPolynomial` alone.

**The reusable rule: when a leaf's docstring says "this needs theory `T`", the first
framing has usually fixed the SHAPE of every later estimate, and the sharpenings inherit
it. Before costing `T`, ask what the crudest available bound gives and how far short it
falls.** A crude bound with no hypotheses plus a patch for the one case where it is short
is a different proof, not a cheaper version of the same one — and it is the one that is
usually already in reach. This is the same failure the memory note "leaf cost estimates
are hypotheses" records, one level up: not "the cost is wrong" but "the *shape* being
costed was never questioned".

Corollary for docstrings: when you close a leaf by a route its docstring did not
prescribe, REWRITE the docstring to the route taken and keep the rejected ones with a
one-line reason. The next owner of a sibling leaf is reading it for the shape, not the
details.

