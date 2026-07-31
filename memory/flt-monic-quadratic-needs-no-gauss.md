---
name: flt-monic-quadratic-needs-no-gauss
description: A monic quadratic is irreducible over a DOMAIN iff it has no root there (mathlib states it that way) — so "y² = f(x)" needs no fraction field, and "f is not a square" is ONE evaluation, not a coefficient comparison
metadata:
  type: reference
---

Two independent overprices, both found while closing
`isIntegral_planeCurveSchemeQ_sexticThirtySeven` (`MazurTorsion.lean`, 2026-07-31). The
leaf's own docstring prescribed the expensive route for each, and both corrections
generalise to every hyperelliptic/plane-curve integrality leaf in this development.

**1. `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` is stated over
`[CommRing R] [IsDomain R]`, not over a field.** So for `Y² − f` with `f ∈ R = ℚ[x]` you do
NOT need Gauss's lemma, a fraction field, `IsIntegrallyClosed`, or
`Monic.irreducible_iff_irreducible_map_fraction_map`. It is true over a domain for the
reason the field proof hides: a monic quadratic factors into non-units only as two monic
linear factors, because the leading coefficients multiply to `1` and are therefore units —
so a factorisation *is* a root, in `R` itself. Always check whether the mathlib lemma you
are about to descend to a field for is already stated over a domain.

**2. "`f` is not a square in `R[x]`" is one evaluation, not five coefficients.** A square
takes square values at every rational point, so ANY `t` with `f(t) < 0` kills it. Here
`f(0) = −4`, so the whole step is `eval`, `sq_nonneg`, `nlinarith`. The coefficient
comparison (`g = x³ + 4x² − 18x + 86`, then `b² + 2ac = 1012 ≠ −24`) is correct and was
checked, and the discriminant route (`Disc f = 2¹² · 37³ ≠ 0`) is correct too — both are
strictly dearer. Look for a sign before reaching for structure. Over a formally real base
this is essentially always available for a curve with rational points on both sheets.

**3. `IsIntegral (Spec R)` is an instance for `[IsDomain R]`**
(`Mathlib/AlgebraicGeometry/Properties.lean`), so the scheme half is `infer_instance` —
`isIntegral_of_isAffine_of_isDomain` plus a hand-built `Nonempty` is the route to write
only if the scheme is not literally a `Spec`.

The transport `MvPolynomial (Fin 2) ℚ ≃ₐ (MvPolynomial (Fin 1) ℚ)[Y]` with **`y` outer** is
`(renameEquiv ℚ (Equiv.swap 0 1)).trans (finSuccEquiv ℚ 1)`; the swap is what puts `y` in
slot `0` for `finSuccEquiv` to peel. Transport irreducibility back with
`MulEquiv.irreducible_iff`, then `UniqueFactorizationMonoid.irreducible_iff_prime`,
`Ideal.span_singleton_prime`, `Ideal.Quotient.isDomain_iff_prime`. The whole chain is about
40 lines. See also [[flt-leaf-cost-estimates-are-hypotheses]] — the docstring's cost
estimate was written before anyone tried.
