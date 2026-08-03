## A SPECIALISED COPY OF A GENERIC THEOREM IS EVIDENCE THAT THE GENERIC ONE IS CHEAP — GREP FOR THE PROOF TECHNIQUE, NOT THE CONCLUSION
(2026-08-02, `flt-lean-47`, closing `smoothOfRelativeDimension_sexticThirtySeven` in
`FreyCurve/MazurTorsion.lean`.) The leaf needed the Jacobian criterion for a plane
curve. A grep for the CONCLUSION over `Fermat/` finds nothing usable, and the honest
report is "not in the tree". That report is wrong, and the way it is wrong is
systematic enough to be worth a standing check.
The criterion existed **twice**, both times specialised to a Weierstrass chart —
`Fermat.isStandardSmoothOfRelativeDimension_projChartAway` in
`ModularCurve/EllipticScheme.lean` and again in `Modularity/MoretBailly.lean`. Both are
stated about `projChartPolynomial E i` and `ProjChartVar i`, so no grep phrased in the
consumer's vocabulary (`hypersurface`, `plane curve`, `MvPolynomial ... ⧸ span {F}`) hits
either, and neither is applicable to an arbitrary plane curve. The `EllipticScheme` copy
is additionally **unreachable** from most of the tree: `X0.lean` imports that module
NON-publicly on purpose, so nothing downstream of `X0` — including `MazurTorsion.lean` —
can name it.
**Neither proof used one fact about a Weierstrass equation.** Deleting the elliptic-curve
vocabulary — `ProjChartVar i` becomes any finite `V`, `projChartPolynomial E i` any `G`,
`ℚ` any commutative ring — is a mechanical port, and it **compiled first try, in 16
seconds**, as `Fermat/FLT/Mathlib/RingTheory/Smooth/Hypersurface.lean` (mathlib-only
imports, so it can never cycle and it iterates in seconds).
**The check, and it is one grep:** when a leaf needs a criterion the tree "does not have",
grep for the mathlib PROOF TECHNIQUE the criterion would be built from — here
`PreSubmersivePresentation`, `jacobiMatrix`, `SubmersivePresentation.ofAlgEquiv` — rather
than for the statement. A hit means somebody has already paid for the hard part in some
specialisation, and the generic statement is a rename away. This is the mirror of
[[flt-inventory-audits-understate-what-exists]]: there the theorem is present under
another name, here it is present under another *instantiation*, and only a
technique-level grep sees it.
Corollary for whoever writes the specialisation: if your proof never inspects the object
in the leaf's vocabulary, state it generically in `Fermat/FLT/Mathlib/**` and specialise
at the call site. Both authors here wrote "this is a piece of MATHLIB rather than of this
development" in the docstring and then stated it about a Weierstrass chart anyway.
### A ROUTE NOTE CAN NAME A PROVEN LEMMA THAT RUNS THE WRONG WAY
The same leaf's docstring, and the task prompt built from it, both prescribed
`AlgebraicGeometry.isStandardSmoothOfRelativeDimension_of_isLocalizationAway`
(`Mathlib/AlgebraicGeometry/CurveExtension.lean`) — "READ IT FIRST, it may be exactly the
shape you need and it is proven". It is proven, and it is the wrong direction: it takes
`[Algebra.IsStandardSmooth K A]` as a HYPOTHESIS and transports the relative DIMENSION
from a localization back to `A`. It cannot establish smoothness of `A`, which was the
whole of what was open. **Read the BINDER LIST of a lemma a route note names, not its
name** — a lemma whose conclusion matches your goal can still consume your goal.
What the statement actually needed was no new theory at all:
`SmoothOfRelativeDimension n` is a `HasRingHomProperty` for
`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)`, so
**`HasRingHomProperty.Spec_iff` turns the scheme statement into exactly "a family
generating the unit ideal on whose localizations the composite is standard smooth"** —
the two-chart cover, consumed by `RingHom.locally_of_exists`, with no gluing written by
hand, no `Algebra.Smooth`, and **no Krull dimension anywhere**. Both routes through
`ringKrullDim B = 1` (`smoothOfRelativeDimension_specMap_algebraMap_of_smooth` and its
`IsRegularRing` sibling) are strictly more expensive and neither is needed.
### A NUMERAL OF `MvPolynomial σ R` **IS** `C` OF ITS COEFFICIENT, BY `rfl` — and that is the only way to differentiate it
Three rounds went to this and it will bite anyone computing a `pderiv` of a concrete
polynomial. `MvPolynomial.pderiv_C` cannot fire against a bare numeral: the numeral's
`OfNat` instance path is not the one a `C`-shaped lemma matches, so `simp` reports the
helper as an *unused simp argument* and leaves `(pderiv 0) 4` sitting in the goal. Going
the other way is worse — `map_ofNat` rewrites `C 4` into `4` and fires BEFORE `pderiv_C`,
undoing exactly what you need.
**`(4 : MvPolynomial (Fin 2) ℚ) = MvPolynomial.C 4` is `rfl`**, so the whole polynomial
has a `C`-form by `rfl`. State that once and everything works:
    theorem sextic_C_form : sexticThirtySevenPoly =
        X 1 ^ 2 - (X 0 ^ 6 + C 8 * X 0 ^ 5 - ...) := rfl
    ...
      rw [sextic_C_form]
      simp [MvPolynomial.pderiv_X]     -- computes the derivative, C-numerals intact
      simp only [map_ofNat]            -- NOW normalise C n back to n
      ring
Note the staging is load-bearing and `simp only [pderiv_X, pderiv_C, ...]` is NOT a
substitute for the full `simp`: `pderiv_X` produces `Pi.single` Kronecker deltas that a
restricted simp set leaves unevaluated.
**And there is no `isUnit_of_mul_eq_one` at this pin** (already recorded elsewhere in this
file, met again here). Build the unit by hand: `⟨⟨_, _, h, by rw [mul_comm]; exact h⟩, rfl⟩`.
### CLEAR DENOMINATORS: a polynomial ring has no `Inv`, so a Bézout cofactor cannot be `A/296`
`gcdext` returns `296 = A·f + B·f'`, and the covering statement wants `1`. You cannot
write `A/296` in `MvPolynomial (Fin 2) ℚ` — there is no `Inv`, and `ring` cannot see
`C (1/296)` as a numeral. Substituting `f = y² − F`, `f' = −∂F/∂x`, `y² = y·(∂F/∂y)/2`
and clearing the last `2` gives an **all-integer** identity `ring` checks directly:
    592 = (−2B)·(∂F/∂x) + (A·y)·(∂F/∂y) + (−2A)·F
and `592` is a unit of any `ℚ`-algebra, so `Ideal.eq_top_of_isUnit_mem` finishes. General
form: **never divide to reach `1`; keep the resultant and discharge it as a unit at the
end.** Re-derive the cofactors in exact integer arithmetic outside Lean first — the CAS is
an untrusted searcher, and the check is ten lines of Python.
