---
name: flt-ask-the-cas-where-the-cusps-sit
description: Before cutting a "modular curve = explicit model" leaf, ask the CAS WHERE the cusps sit in that model — the affine chart is usually not the open part
metadata:
  type: project
---

When a leaf identifies an abstract coarse moduli space with an explicit plane
model, the tempting cut is *"`Y_0(N)` IS the affine model, so `U := Y` and `uV`
is an isomorphism"*. At `N = 37` that is **FALSE**, and one five-second Magma
query settles it:

    X := SmallModularCurve(37); S, m := SimplifiedModel(X);
    Cusp(X, 37, 1);  Cusp(X, 37, 37);        // -> (1:1:1) and (1:1:0) on S

One cusp is the AFFINE point `(x, y) = (1, 1)`; the other is at infinity. So
`Y_0(37)` and the affine chart of `y² = x⁶ + 8x⁵ − 20x⁴ + 28x³ − 24x² + 12x − 4`
are incomparable opens of `X_0(37)` — neither contains the other — and their
intersection misses THREE of the four rational points, so it fails a `≤ 2`
complement bound that either one alone satisfies.

**Why:** the number of cusps and the number of points at infinity agree at `37`
(both `2`), which is exactly what makes the wrong guess plausible; the coordinate
`x` of the chosen model has nothing to do with the cusps. Nothing about the
EQUATION tells you where the cusps are.

**How to apply:** for any such leaf, before choosing `U`, get the model *and the
distinguished points inside it* out of the CAS, in one query. Then cut so that
the explicit chart is `U` and the abstract open is recognised INSIDE the chart's
compactification — not the other way round. See
`exists_affinePlaneOpen_x0ThirtySeven` in `Fermat/FLT/FreyCurve/MazurTorsion.lean`,
where this fixed the shape of a four-leaf decomposition, and
[[flt-inventory-audits-understate-what-exists]] for the general habit of checking
a plausible claim against the tree instead of assuming it.

Second, reusable half of the same cut: `AlgebraicGeometry.`
`exists_isSmoothCompactification_of_isAffine` is PROVEN and manufactures the
compactification of ANY smooth integral affine curve over a perfect field, so a
leaf that asks for "a compactification containing this explicit affine curve"
should be re-cut as *(integrality) + (smoothness) + (what is special about it)*
rather than proved by hand — which is exactly how `Fermat.exists_x0Compactification`
already builds `X_0(N)`.
