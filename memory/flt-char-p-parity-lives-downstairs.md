---
name: flt-char-p-parity-lives-downstairs
description: A char-p ramification/parity statement that looks like it needs valuation theory on the curve's function field is often provable on ℙ¹ from the Artin–Schreier shape of the curve equation
metadata:
  type: project
---

In characteristic `2` the whole missing input of
`exists_wronskianPoly_scalar_charTwo` (`Fermat/FLT/EllipticCurve/DifferentialCharacter.lean`)
was *"the ramification indices of `u = x ∘ φ` are EVEN off the branch point of
`W → ℙ¹`"* — a statement whose textbook proof is
`e(W → ℙ¹_u) = e(W → W′)·e(W′ → ℙ¹_u)`, i.e. valuation theory on the function field
`K = F(W)`, a quadratic Artin–Schreier extension of `F(X)`. The file's route notes
had budgeted for building `K` as `AdjoinRoot p` with a lifted derivation
(~5 self-contained obligations, several hundred lines).

**It was not needed.** The curve equation, cleared of denominators, is already an
Artin–Schreier form *downstairs on `F(X)`*: with `γ = Cx/E`, `δ = D/E`, the
hypothesis reads `γ²f + δ² + γδS = g(u)`, whose left side factors as
`γ²f + δ·(δ + γS)`. At any place where the `γ²f` term is provably the largest, the
ordinary ultrametric case split ("in `z² + σz` the square wins unless the orders
tie") forces `ord_b(LHS) = 2·ord_b δ`, hence EVEN. One lemma,
`charTwo_AS_rootMultiplicity`, ~40 lines over `Polynomial.rootMultiplicity`, and it
is applied twice: directly at a pole of `u`, and after translating `δ` by the
`2`-torsion ordinate `c` at the fibre over `r′ = a₃′/a₁′`.

**Why:** the extension `K/F(X)` is unramified exactly where the argument needs it,
so every valuation it would have contributed is already visible on `F(X)`. Building
`K` would have re-derived downstairs data upstairs.

**How to apply:** before building a function field / derivation / valuation tower to
get a *parity* or *divisibility* fact in characteristic `p`, write the defining
equation as `z^p − z = W` (or `z² + σz = N`) over the base and ask whether the
ultrametric case split on that single equation already gives it. Two more signals
that this works: the needed nonvanishing at the ramified fibre was exactly
`Δ ≠ 0` in disguise (in char 2 the `y`-partial `2y + a₁x + a₃` vanishes at the
`2`-torsion point, so smoothness has to sit in the `x`-partial —
`charTwo_twoTorsion_partialX_ne_zero`, one `linear_combination` against
`Δ_of_char_two`); and `linear_combination`'s coefficients for such identities are
worth computing with sympy (`sp.div` of the residual by the relation) rather than by
hand. See [[flt-inventory-audits-understate-what-exists]] and
[[flt-missing-machinery-may-be-downstream]].
