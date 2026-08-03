## A NUMERICAL FORMULA CAN DEGENERATE — check the dimension before calling a leaf ATOMIC

(2026-07-31, `ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field`.) The leaf's own
docstring named its content correctly — "THE DIMENSION FORMULA FOR FINITE-TYPE `K`-SCHEMES,
and that is the whole of it", `dim 𝒪_{X,x} + trdeg_K κ(x) = dim X` — and concluded that
neither `trdeg` nor the formula "is in the pin as a statement about stalks, which is why
this is a leaf and not a step". Both clauses are true. The conclusion drawn from them was
still too pessimistic, and the reason generalises.

**In relative dimension `1` every term of that formula is `0` or `1`, so the EQUATION
degenerates to a DICHOTOMY**: `ringKrullDim 𝒪_{X,x} = 0` iff `κ(x)` is transcendental over
`K`. A dichotomy between two Props needs no arithmetic and no `trdeg` — it is a statement
about `Algebra.IsAlgebraic` alone, and `Algebra.IsAlgebraic` composes (`IsAlgebraic.trans`)
exactly where `trdeg` would have needed additivity. The whole development came to ~250
lines. So before accepting "this needs theory `T`", ask whether the instance of `T` you
actually need is a degenerate one; the general theory being absent from the pin says
nothing about the special case.

Two reusable facts found on the way, both worth knowing before attacking anything about
smooth curves over a field:

* **`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` is the whole
  toolkit.** It factors a smooth chart as `K → K[X₁,…,Xₙ] → A` with the second map ÉTALE,
  and étale gives `Module.Flat` (hence `Algebra.HasGoingDown`) and
  `Algebra.QuasiFinite` (hence `Algebra.QuasiFinite.eq_of_le_of_under_eq`: two primes with
  the same contraction, one below the other, are equal). Minimality of a prime and the
  vanishing of its contraction are then each other, in one line per direction. The same
  lemma is what closed `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` in
  `CurveExtension.lean` after three audits had declared "smooth ⟹ regular is absent from
  the pin".
* **`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean` carries an instance
  `Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)`** for `f` formally
  unramified and locally of finite type. So "the residue extension along a quasi-finite map
  is finite/algebraic" is `inferInstance`, not a sub-leaf. `Mono f` supplies
  `FormallyUnramified f` through the diagonal.

**AND THE ONE PLACE THE BOOKKEEPING IS NOT FREE: a `K`-algebra structure on `κ(x)` must be
CANONICAL, never a chart's.** A statement comparing an invariant at `x : X` and at
`u x : J` over a common base `Spec K` needs `IsScalarTower K κ(u x) κ(x)`, and that holds
only if both `K`-structures come from the STRUCTURE MORPHISMS
(`strX.residueFieldMap`, `jstr.residueFieldMap`), where `hu : u ≫ jstr = strX` can be fed
in through `Scheme.Γevaluation_naturality` and `Scheme.Hom.comp_appTop`. A chart-derived
`Algebra K ↥(X.residueField x)` is a different term of the same type, and every transitivity
lemma silently fails to apply to it. The fix is to define the canonical one as a
`@[reducible] def` (not an instance — it depends on data), state the chart lemma with
`letI := that`, and discharge the mismatch once with `Algebra.algebra_ext`. Budget for that
step: it was a third of the proof.

