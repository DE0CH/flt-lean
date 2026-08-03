## "THE ONLY GAP IS X" CAN BE WRONG ABOUT *WHICH STEP* IS THE GAP — CLOSING X THEN LEAVES THE LEAF OPEN
(2026-08-02, `flt-lean-122`, on `exists_specialGenericPoint_valuationRing` in
`ModularCurve/X0.lean`.) Two sibling leaves cut the same day carried the same absence
verdict, in the same words, and one sentence tying them together:
> So the ONLY gap here is "the special fibre is reduced", i.e. the same missing
> `Smooth ⟹ GeometricallyReduced` that `isIntegral_of_smoothProperCurve` above records.
> **Whoever closes that step closes both leaves.**
Everything about the mathlib PIN in that verdict is true and re-verified. Everything else
is wrong, in two independent ways, and the second is the one worth carrying.
**1. The gap was not open — it was closed TWICE, in modules the file already imports.**
`X0.lean` `public import`s both of
* `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` (sorry-free):
  `isReduced_of_smooth_over_field`, `isReduced_of_smooth_over_domain`, and
  `GeometricallyReduced.of_smooth` — **the exact converse of Cartier the audit declares
  absent**;
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean` (1818 lines, sorry-free):
  `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`,
  `valuationRing_stalk_of_smoothOfRelativeDimension_one`,
  `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` — whose route is the
  **local structure theorem** (`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`),
  not regularity theory, which is why "no `Smooth ⟹ regular` in the pin" never applied.
  `X0.lean` itself already applies the first as `isIntegral_pullbackSpecial_of_isReductionBase`.
Two agents on the same day found *different* copies of the same missing fact. This is the
`[[flt-inventory-audits-understate-what-exists]]` failure again, and the standing rule is
unchanged: **`Fermat/FLT/Mathlib/**` is where every agent's general-purpose geometry and
commutative algebra lands — grep it by CONCEPT before writing "absent from the pin", and
say in the verdict WHICH TREES were searched.**
**2. AND CLOSING THE GAP DID NOT CLOSE THIS LEAF.** That is the new lesson. The sibling
did close on that discovery; this one did not, because the docstring named the wrong step.
The reducedness that became free is a statement about the FIBRE; the surviving conjunct
needs it about a QUOTIENT OF A STALK OF THE MODEL, and the bridge between them —
    𝒪_{X,η} / (ℓ)  ≅  𝒪_{X ×_R 𝔽_ℓ, η'}
— is what nobody has. Mathlib packages it for neither `Scheme.Hom.fiber` (`Fiber.lean`
proves `range_fiberι` and `fiberHomeo` and **no stalk lemma**) nor the ideal of a
base-changed closed immersion.
**So an "only gap" sentence has TWO failure modes and they need different checks.** Whether
X is available is a `grep`, and everybody eventually runs it. Whether X is *the* gap is a
re-derivation of the route with X assumed, and almost nobody runs it — the sentence reads as
settled precisely because its author had just done the hard thinking. Run it: assume the
named gap, and write out the proof. If a step remains, name THAT step in the docstring, and
say so even when you cannot close it. A leaf whose advertised blocker gets closed elsewhere
and which then silently stays open is the most expensive kind of stale claim, because it
will draw a dispatch every time the blocker is mentioned.
**A cheaper-looking route that does NOT close it, recorded so it is not retried.** One can
prove with the machinery already present that `𝔪_η` is the ONLY prime containing `ℓ` (a
generization of `η` inside the special fibre is `η`, since `η` generizes that fibre), so
`𝒪_{X,η}/(ℓ)` is ARTINIAN local and `dim 𝒪_{X,η} = 1` by Krull's height theorem. Not
enough: an artinian local ring is a field exactly when it is REDUCED, and reducedness of
`𝒪_{X,η}/(ℓ)` is the identification again. **The topology bounds the dimension; only the
fibre's own reducedness makes the maximal ideal principal.**
Finally, base arithmetic this needed and nobody had: **`IsReductionBase` says only that
`R ⊆ ℚ` is local with residue field `𝔽_ℓ`, and that alone does not bound `dim R`.** The
uniformizer has to be extracted — `IsReductionBase.maximalIdeal_eq_span`, Bézout on
`num`/`den` through the already-present `isUnit_den_subring_rat`, ~25 lines — and only then
is `Spec R` two points, which is what converts "not in the generic fibre" into "in the
special fibre". Before assuming a `Subring ℚ` in this development is `ℤ_(ℓ)` for dimension
purposes, check that the lemma saying so exists.
