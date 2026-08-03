## AN ALGEBRAIC HALF PRICED AT A DEVELOPMENT IS OFTEN AN IDENTITY OF COEFFICIENTS
(Same task, and it is what made the cut worth making.) The leaf's algebraic content was
*"`j(Tate(q)) = 1/q + 744 + …` is transcendental over `ℚ`"*, and the obvious route is the
Tate-curve evaluation machinery — `TateCurve.evalInt`, summability, a complete
nonarchimedean field. `ℚ((q)) = FractionRing (PowerSeries ℚ)` needs **none of it**: over
that field the series ARE the coefficients, so `a₄`, `a₆`, `Δ` and `c₄` are the images of
`TateCurve.{a₄Formal,a₆Formal,ΔFormal,c₄Formal}` under `ℤ⟦q⟧ → ℚ⟦q⟧ ↪ K`, and every
statement is an identity in `ℚ⟦q⟧` pushed along an INJECTION. Ninety lines, first try.
Two levers, both general:
* **`ΔFormal` is DEFINED as the discriminant polynomial of `⟨1,0,0,a₄,a₆⟩`**, so
  "mathlib's `Δ` of the Tate quintuple is the image of `ΔFormal`" is
  `simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, map_*]; ring`. Likewise `c₄ = 1 - 48a₄`.
  Before transporting a named constant, check whether the project's version was defined by
  the same polynomial — here it was, and the docstring said so.
* **ASK THE CONSUMER WHICH STRENGTH IT NEEDS.** The consumer wants `¬ IsAlgebraic ℚ (f x)`,
  but `mem_range_algebraMap_of_isAlgebraic_fractionRing_powerSeries` (PROVEN, in
  `Mathlib/RingTheory/InvariantCoarseRing.lean`) already upgrades *"not in the image of
  `ℚ`"* to *"not algebraic over `ℚ`"*. So the leaf only owes **`j` is not a CONSTANT**,
  which is `Δ·j = c₄³` plus one reading of constant coefficients (`0·c = 0` against
  `1³ = 1`). Transcendence and non-constancy are a whole theory apart, and the file already
  contained the bridge.
**And name the object, or the algebra you just proved goes free-floating.** Stating the
modular residue as *"`∃ d, ∃ W, IsWeierstrassModel d.ab W ∧ W.j ∉ range ℚ`"* is the natural
shape and it is wrong: the assembly then never consumes the proven non-constancy, which
this project forbids. Stating it as *"`∃ d, IsWeierstrassModel d.ab tateCurveFractionRing`"*
— the curve NAMED — keeps the algebra in the cone and makes the residue a citation about a
specific object. Same rule as the discharged-hypothesis note; it applies to `def`s too.
