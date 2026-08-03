## `IsSchemeTheoreticallyDominant` is the pin's tool for "the image is a subgroup scheme"

(2026-07-31, same task — this is the concrete follow-up to the standing note that
schematic density is in the pin.)

The classical argument for "the scheme-theoretic image of a homomorphism is a subgroup
scheme" goes through "`B ×_ℚ B` is the image of `J ×_ℚ J`, because the source is reduced
and the base is a field". **Reducedness is a detour.** What the argument actually needs
is `AlgebraicGeometry.IsSchemeTheoreticallyDominant` (`f.ker = ⊥`), and the pin carries
everything:

* `IsSchemeTheoreticallyDominant.of_isPullback` — stable under **flat** base change;
* an instance for composition;
* `Scheme.Hom.ker_comp` + `IdealSheafData.map_bot` give **cancellation**:
  `p.ker = ⊥ → (p ≫ h).ker = h.ker`. Since `IsClosedImmersion.lift` asks exactly for
  `ι.ker ≤ (·).ker`, that turns "the composite lands in the subscheme" into "the
  morphism lands in the subscheme". This is the whole mechanism;
* **over `Spec` of a field, flatness is free** — `[Subsingleton Y] [IsIntegral Y] → Flat f`
  — so every base change along a structure morphism to `SpecQ` qualifies with no work.

`q ×_S q` is dominant when `q` is: cut it as `(q × 𝟙) ≫ (𝟙 × q)`, each a base change of
`q` along a projection, pasted with `IsPullback.of_bot`.

**Two things to check BEFORE writing any of it.** `X0.lean` already contained
`isSchemeTheoreticallyDominant_toImage` and a `sqCover` version of the product step —
proven for an unrelated leaf **58 000 lines away**, under names that share no keyword
with the leaf being worked on. Grep for the CONCEPT (`IsSchemeTheoreticallyDominant`,
`ker_eq_bot`, `of_isPullback`), not for the leaf's vocabulary. And develop in a scratch
module that `public import`s the target's built olean: the round trip on this file is
~25 minutes for a build and ~40 seconds for the scratch, and the leaf above went from
first draft to green in four scratch iterations.

Known GAP in the pin, found the same day: **`Smooth f → GeometricallyReduced f` does not
exist**, in any form, at any level. Mathlib DOES have Cartier's theorem
(`AlgebraicGeometry.smooth_of_grpObj`: a locally-finite-type geometrically reduced group
scheme over a field is smooth), so the char-0 smoothness of a group scheme is reachable
in principle — but its `GeometricallyReduced` hypothesis has to be built by hand, and for
an abelian scheme the obvious source is its own `smooth` field, which does not deliver.

