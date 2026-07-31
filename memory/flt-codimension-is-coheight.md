---
name: flt-codimension-is-coheight
description: A `2 ≤ ringKrullDim (X.presheaf.stalk z)` clause is a CHAIN in the specialization order, not local-ring theory — and `Flat.generalizingMap` is how you produce the chain
metadata:
  type: reference
---

`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (x : X) :
ringKrullDim (X.presheaf.stalk x) = Order.coheight x` (mathlib,
`Mathlib/AlgebraicGeometry/Properties.lean`, stacks 02IZ). Schemes carry
`instance {X : Scheme} : Preorder X := specializationPreorder X`, in which
`a ≤ b` unfolds to `b ⤳ a` — **bigger means more generic**. So a codimension
clause is a statement about chains of generizations and **no local ring is ever
inspected**:

    z < η  and  η < ξ   ⟹   2 ≤ Order.coheight z   (Order.coheight_add_one_le, twice)
                        ⟹   2 ≤ ringKrullDim (X.presheaf.stalk z)

The two strict specializations come cheaply:

* `z < η` from `η ⤳ z` plus **`z ∉ U`, `η ∈ U` for an open `U`** —
  `Specializes.mem_open` makes `z ⤳ η` impossible, so no `T₀` argument is
  needed for this half;
* `η < ξ` from **flatness**: `AlgebraicGeometry.Flat.generalizingMap` (in
  `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`) says a flat
  morphism lifts generizations, and `Smooth ⟹ Flat` is an instance. Feed it
  `genericPoint_specializes (f x)` on an irreducible target and it hands back a
  generization of `x` sitting over the generic point. `Specializes.antisymm`
  returns `Inseparable`, not `Eq` — finish with `.eq` (schemes are `T₀`).

This closed the codimension half of `exists_neronExtension_codimOne` in
`ModularCurve/X0.lean` outright (2026-07-29), leaving only BLR's valuative
criterion as a leaf. The docstring there had recorded the obstruction as
"`XZ` is regular because it is smooth over a discrete valuation ring" —
**regularity is needed for the valuative criterion, but NOT for the
codimension bookkeeping**, and conflating the two is what made the node look
atomic. See [[audit-searched-production-not-invariant]]: same shape of error,
an audit scoped to one route.

To identify a fibre as a preimage, `Scheme.Pullback.range_fst :
Set.range (pullback.fst f g) = f ⁻¹' Set.range g`, composed through
`IsFibreIdent.compareIso` — the project's `IsFibreIdent.denseRange_universalPoint`
is the worked example to copy.
