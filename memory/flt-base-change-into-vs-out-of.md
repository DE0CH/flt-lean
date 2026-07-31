---
name: flt-base-change-into-vs-out-of
description: A universal property base-changes exactly when its fields are about maps INTO the object; maps OUT need Weil restriction, which does not exist at this pin — so change the presentation, not the proof
metadata:
  type: project
---

Whether a structure survives base change along `f : S' ⟶ S` is decided field by
field, by direction:

* fields about maps **INTO** `J` transport for free —
  `Hom_{S'}(T, J ×_S S') ≅ Hom_S(T, J)` is the defining adjunction of the fibre
  product (this is `IsCoarseModuliY0.classifyPullback`, and
  `IsJacobianOf`'s `aj` / `aj_pre` / `aj_base`);
* fields about maps **OUT of** `J` do not: maps out of a base change are
  `Hom_S(J, Res_{S'/S} A')`, i.e. Weil restriction, which is an abelian scheme
  only for `S' ⟶ S` finite locally free and which **does not exist anywhere at
  this pin** — `grep -rn "WeilRestriction\|weilRestriction"` over
  `.lake/packages/mathlib/Mathlib/` and over `Fermat/` returns zero hits in both.
  This is `IsCoarseModuliY0.universal` and `IsJacobianOf.universal`.

**Why it matters:** the reflex is to treat "the base-change lemma" as an open
proof obligation. It is not — it is a signal that the wrong PRESENTATION of the
object is being carried.

**How to apply:** when a universal-property structure will not base-change, look
for the representability presentation of the same object and base-change that
instead. This tree has both, and both times the swap was the resolution:
`Gamma0AtlasData` for `IsCoarseModuliY0` (`X0.lean`, `SpecialFibreCoarse`
subsection), and `IsRelPicZeroOf` (`ModularCurve/RelativePicard.lean`) for
`IsJacobianOf` — every field of `IsRelPicZeroOf` is about maps into `J`, so it
base-changes by inspection, which is exactly what
`exists_comp_jacobianBaseChangeAj`'s docstring gives as its classical proof.

Separately verified 2026-07-31 and worth knowing before costing any "reduce to a
field base" plan: mathlib's `SmoothOfRelativeDimension` API has **no fibrewise
criterion**. It is `HasRingHomProperty`, hence Zariski-local on the TARGET, not
on fibres, and `smoothOfRelativeDimension_isStableUnderBaseChange` preserves
along `Spec κ(s) ⟶ S` but does not reflect. Complete API: `.smooth`, the
`HasRingHomProperty` instance, base change, `comp` (`n + m`), open immersions at
`0`, `Etale ↔ 0`.

Related: [[flt-audit-refuting-check-unrun]].
