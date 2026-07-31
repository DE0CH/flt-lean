---
name: flt-field-of-moduli-not-definition
description: A coarse-moduli leaf that asks for the classifying datum over κ(x) is FALSE; the datum needs a bigger field than the point does
metadata:
  type: project
---

When re-cutting a leaf about a point `x` of a COARSE moduli space over the
object it classifies, do **not** write "there is a datum over `Spec κ(x)`".
`κ(x)` is the field of MODULI; the datum needs a field of DEFINITION, and they
differ already at the smallest interesting level.

Witness, found 2026-07-31 while cutting `exists_cuspAboveDivisor_root`
(`Fermat/FLT/ModularCurve/X0.lean`): at `N = 4`, `d = 2` the cusp of `X_0(4)`
has `g = gcd(2, 2) = 2`, `φ(g) = 1`, so it is **ℚ-rational** — while a
`Γ₀(4)`-structure on the Néron 2-gon is a cyclic `⟨(u, 1)⟩ ⊆ Kˣ × ℤ/2` of order
`4`, forcing `u² = −1`, so every datum carrying that cusp needs `ℚ(i)` and none
exists over `ℚ`. Writing the tempting form would have manufactured a false leaf
whose falsity audit reads as fine.

**Why:** a coarse space represents the moduli functor only up to the
automorphisms of the objects; the descent obstruction lives in `H¹(Gal, Aut)`
and is generally nonzero, so a rational point need not lift to a rational
object.

**How to apply:** quantify over an ARBITRARY base scheme `T` over the ground
field and ask only that some point of `T` map to `x` — that is what
`IsX0Compactification.CuspClassifier.IsClassOf` does. It costs nothing (for
`T = Spec L` the space is one point, so the quantifier is an identity) and it is
the difference between a true leaf and a false one. Same caution applies to any
`IsCoarseModuliY0`-style statement in this development.

See [[flt-overdetermined-degree-conjunct]] for the other half of that same
re-cut.
