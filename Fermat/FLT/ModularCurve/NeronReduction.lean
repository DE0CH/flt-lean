/-
ModularCurve/NeronReduction.lean — own work for the Fermat project (not
vendored from the FLT project).

# Good reduction of a curve and its Jacobian, with NO moduli problem in sight

This module is the **moduli-free core** of the rank-`0` reduction argument.
`X0.lean` carries that argument in a `Γ₀`-shaped packaging —
`IsX0CurveModel`, `IsX0JacobianModel`, `IsX0NeronDatum` and the namespace
that turns the last of these into an `IsX0ReductionAt` — and exactly ONE
field of that packaging mentions a modular curve:
`model : IsX0Compactification N xstr ystr jZ`.  Everything else speaks only
about

* a smooth proper geometrically connected curve over `ℚ`,
* an integral model of it over the local ring `ℤ_(ℓ)` (`SpecLoc R`, pinned
  by `IsReductionBase`),
* its relative Jacobian,
* and the two fibre identifications, their naturality, their additivity,
  their compatibility with Abel–Jacobi, the Néron mapping property and the
  valuative criterion of properness.

## The check that licenses this file, and how to re-run it

The load-bearing claim is: **nothing in the production of an
`IsX0ReductionAt` from a Néron datum touches the moduli field.**  It is
mechanically checkable in one command:

```
grep -n '\.model\b' Fermat/FLT/ModularCurve/X0.lean
```

Every hit must lie OUTSIDE the range `structure IsX0NeronDatum` …
`end IsX0NeronDatum`.  Re-run on 2026-07-28: 67 hits, the first at line
29571, against a namespace running 26253–26455.  Zero hits inside.  If a
`d.model` ever appears in that range this file's premise is wrong.

The one apparent exception is `exists_x0JacobianModel_of_curveModel`, whose
proof opens with `⟨cm.model.isProper, cm.model.smooth, cm.model.connected⟩`.
That is not a use of the moduli structure but of the three GEOMETRIC facts
it happens to bundle, i.e. of `IsSmoothProperCurve xstr` — which is why
`IsCurveReductionModel` below carries that as a field named `curve` and the
Jacobian half then needs no model at all.

## What is here, and what a consumer supplies

* `IsCurveReductionModel` — `IsX0CurveModel` with `model` replaced by
  `curve : IsSmoothProperCurve xstr`.  Note `ystr` and `jZ` disappear
  entirely with it: they were parameters only because `model` mentioned
  them.
* `IsNeronReductionDatum` — `IsX0NeronDatum` with `model` deleted, together
  with its whole namespace (`intJ`, `intX`, `redJ`, `redX`, `intJ_add`,
  `intJ_aj`, `redJ_add`, `red_aj`, `finite_intPoints`) and the assembly
  `toReduction`, all copied unchanged because none of them ever mentioned
  the modular curve.
* `exists_neronReductionDatum_of_curveModel` — PROVEN, the moduli-free form
  of `exists_x0JacobianModel_of_curveModel` followed by
  `exists_x0NeronDatum_of_base`'s field copying.

A consumer therefore has exactly one obligation left, and it is the only
genuinely level-structure-specific one: **produce an
`IsCurveReductionModel` for its own curve** — i.e. Deligne–Rapoport /
Igusa for whichever moduli problem it is working with.  `X1.lean`'s
`exists_x1CurveModel_of_base` is the `Γ₁` instance.

## Why this file sits DOWNSTREAM of `X0.lean` rather than in the shim tree

A genuine hoist would put this under `Fermat/FLT/Mathlib/AlgebraicGeometry/`
and have `X0.lean` import it.  That is blocked, not by mathematics but by
where the vocabulary lives: `SpecQ`, `SpecF`, `SpecLoc`, `IsReductionBase`,
`IsSmoothProperCurve`, `IsFibreIdent`, `IsJacobianOf`, `IsX0ReductionAt`,
`exists_relativeJacobian`, `isSmoothProperCurve_of_fibreIdent`,
`exists_jacobianFibreIdent`, `bijective_pre_generic_of_isProper` and
`neronReduction_injective` are ALL declared inside `X0.lean`, most of them
with long proofs and their own deep dependencies.  Moving them would be a
six-region surgery on a 38 000-line file that currently has upwards of
twenty concurrent owners.

So the direction is inverted instead: this module imports `X0.lean` and
re-states the moduli-free structures.  The cost is that `IsX0NeronDatum`
and `IsX0CurveModel` remain in `X0.lean` alongside their counterparts here.
**The intended cleanup, for whoever next owns that region of `X0.lean`
(lines 28208–28250 and 26253–26455), is to replace them by**

```
structure IsX0CurveModel (N ℓ : ℕ) … extends IsCurveReductionModel ℓ R toF xstr where
  model : IsX0Compactification N xstr ystr jZ
```

**and to delete the `IsX0NeronDatum` namespace outright**, since dot
notation resolves through `extends`.  That is a one-region edit once this
module is on `main`; it is deliberately NOT done here, because a structural
refactor of `X0.lean` concurrent with twenty owners is the worst shape of
conflict this fleet produces.
-/

module

public import Fermat.FLT.ModularCurve.X0

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Fermat

/-! ### The curve half, moduli-free -/

/-- **An integral model of a curve over `ℤ_(ℓ)`, with its two fibres
identified** — `IsX0CurveModel` with the moduli field replaced by the
three geometric facts that the Jacobian half actually consumes.

`xstr : XZ ⟶ SpecLoc R` is the integral model; `strX : X ⟶ Spec ℚ` is its
generic fibre and `strX' : X' ⟶ Spec 𝔽_ℓ` its special fibre, each
identified as a FUNCTOR of points over an identified base point (so by
Yoneda `X ≅ XZ ×_{ℤ_(ℓ)} ℚ` and `X' ≅ XZ ×_{ℤ_(ℓ)} 𝔽_ℓ`, not merely a
bijection of point sets).

`curve` is what `model` was really being used for: the Jacobian half needs
`IsProper`, `SmoothOfRelativeDimension 1` and `GeometricallyConnected` for
`xstr` and nothing else about it.  Any moduli-shaped model supplies these —
`IsX0Compactification` and `IsX1Compactification` both carry the three
fields — so instantiating this structure from either is field copying.

`properX` is the valuative criterion of properness, `𝒳(ℤ_(ℓ)) ≅ X(ℚ)`; it
is what turns a rational point into an integral one, and hence the only
reason a reduction map exists at all.  It is stated rather than derived
from `curve.isProper` because the derivation
(`bijective_pre_generic_of_isProper`) needs the base pinning, which this
structure does not carry. -/
structure IsCurveReductionModel (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    {X X' XZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    (xstr : XZ ⟶ SpecLoc R) where
  /-- the integral model is a smooth proper geometrically connected curve -/
  curve : IsSmoothProperCurve xstr
  /-- the generic fibre of the curve model is `X`, functorially -/
  genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀
  /-- the special fibre of the curve model is `X'`, functorially -/
  spX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strX' g ≃ RelPoint xstr g₀
  /-- naturality of the generic identification of curves -/
  genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strX g),
    genX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x)
  /-- naturality of the special identification of curves -/
  spX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strX' g),
    spX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spX g g₀ h₀ x)
  /-- **valuative criterion of properness**: every rational point of `X`
  extends uniquely to an integral point of the model -/
  properX : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint xstr (𝟙 (SpecLoc R)) → RelPoint xstr (SpecLoc.generic R))

/-- **The generic fibre identification of a curve model, as an
`IsFibreIdent`** (PROVEN — pure field copying). -/
def IsCurveReductionModel.genIdent {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X X' XZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R}
    (cm : IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) :
    IsFibreIdent (SpecLoc.generic R) xstr strX where
  toEquiv := cm.genX
  nat := cm.genX_nat

/-- **The special fibre identification of a curve model, as an
`IsFibreIdent`** (PROVEN — pure field copying). -/
def IsCurveReductionModel.spIdent {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X X' XZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R}
    (cm : IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr) :
    IsFibreIdent (SpecLoc.special toF) xstr strX' where
  toEquiv := cm.spX
  nat := cm.spX_nat

/-! ### The full Néron-pinned reduction datum, moduli-free -/

/-- **A Néron-pinned reduction datum for a curve over `ℚ` at `ℓ`** —
`IsX0NeronDatum` with the single moduli field `model` deleted.

This is `IsX0ReductionAt` with `redJ` no longer free: instead of positing
a map with three properties, the datum carries the INTEGRAL MODELS over
`ℤ_(ℓ)` and reads `redX`, `redJ` off them.  All three properties of
`IsX0ReductionAt` are then theorems (`redJ_add`, `red_aj` below;
`redJ_inj` from `X0.lean`'s `neronReduction_injective`), assembled by
`toReduction`.

Field for field this is `IsX0NeronDatum` (see its docstring for what each
one says and why the pinning rather than the maps is the load-bearing
part), minus `model` and minus the two parameters `ystr`, `jZ` that only
`model` mentioned.

**Why deleting `model` costs nothing.**  The pinning argument in
`IsX0NeronDatum`'s docstring — that `(X', J', aj', Set.range redJ)` is
determined up to isomorphism, so `redJ` is the genuine reduction rather
than an arbitrary injective homomorphism — runs on `base`, `genX`/`spX`,
`neronJ` and `properX`.  `model` pins WHICH curve `X` is; it says nothing
about the reduction of that curve.  A consumer that needs the special
fibre identified as a specific moduli space must state that separately,
which is exactly what `X1.lean`'s `exists_x1CurveModel_of_base` does by
returning an `IsX1Compactification` alongside the model. -/
structure IsNeronReductionDatum (ℓ : ℕ) (R : Subring ℚ) (toF : R →+* ZMod ℓ)
    {X J X' J' XZ JZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    (jac : IsJacobianOf strX ab o) (jac' : IsJacobianOf strX' ab' o')
    {xstr : XZ ⟶ SpecLoc R}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} (jacZ : IsJacobianOf xstr abZ oZ) where
  /-- the base is the local ring of `ℤ` at `ℓ` -/
  base : IsReductionBase ℓ R toF
  /-- the generic fibre of the curve model is `X`, functorially -/
  genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀
  /-- the generic fibre of the Jacobian model is `J`, functorially -/
  genJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint jstr g ≃ RelPoint jstrZ g₀
  /-- the special fibre of the curve model is `X'`, functorially -/
  spX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint strX' g ≃ RelPoint xstr g₀
  /-- the special fibre of the Jacobian model is `J'`, functorially -/
  spJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.special toF = g₀ → RelPoint jstr' g ≃ RelPoint jstrZ g₀
  /-- naturality of the generic identification of curves -/
  genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint strX g),
    genX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x)
  /-- naturality of the generic identification of Jacobians -/
  genJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint jstr g),
    genJ g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genJ g g₀ h₀ x)
  /-- naturality of the special identification of curves -/
  spX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint strX' g),
    spX g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spX g g₀ h₀ x)
  /-- naturality of the special identification of Jacobians -/
  spJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecF ℓ} {g' : T' ⟶ SpecF ℓ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.special toF = g₀) (h₀' : g' ≫ SpecLoc.special toF = g₀')
    (x : RelPoint jstr' g),
    spJ g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (spJ g g₀ h₀ x)
  /-- the generic identification of Jacobians is additive -/
  genJ_add : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x y : RelPoint jstr g),
    genJ g g₀ h (ab.add x y) = abZ.add (genJ g g₀ h x) (genJ g g₀ h y)
  /-- the special identification of Jacobians is additive -/
  spJ_add : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (x y : RelPoint jstr' g),
    spJ g g₀ h (ab'.add x y) = abZ.add (spJ g g₀ h x) (spJ g g₀ h y)
  /-- Abel–Jacobi is defined over the base: generic fibre -/
  genX_aj : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x : RelPoint strX g),
    genJ g g₀ h (jac.aj g x) = jacZ.aj g₀ (genX g g₀ h x)
  /-- Abel–Jacobi is defined over the base: special fibre -/
  spX_aj : ∀ {T : Scheme.{0}} (g : T ⟶ SpecF ℓ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.special toF = g₀) (x : RelPoint strX' g),
    spJ g g₀ h (jac'.aj g x) = jacZ.aj g₀ (spX g g₀ h x)
  /-- **Néron mapping property**: every rational point of `J` extends
  uniquely to an integral point of the model -/
  neronJ : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.generic R))
  /-- **valuative criterion of properness**: every rational point of `X`
  extends uniquely to an integral point of the model -/
  properX : Function.Bijective
    (RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) :
      RelPoint xstr (𝟙 (SpecLoc R)) → RelPoint xstr (SpecLoc.generic R))

namespace IsNeronReductionDatum

variable {ℓ : ℕ} {R : Subring ℚ} {toF : R →+* ZMod ℓ}
    {X J X' J' XZ JZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    {strX' : X' ⟶ SpecF ℓ} {jstr' : J' ⟶ SpecF ℓ}
    {ab' : AbelianSchemeStruct jstr'} {o' : RelPoint strX' (𝟙 (SpecF ℓ))}
    {jac : IsJacobianOf strX ab o} {jac' : IsJacobianOf strX' ab' o'}
    {xstr : XZ ⟶ SpecLoc R}
    {jstrZ : JZ ⟶ SpecLoc R} {abZ : AbelianSchemeStruct jstrZ}
    {oZ : RelPoint xstr (𝟙 (SpecLoc R))} {jacZ : IsJacobianOf xstr abZ oZ}
    (d : IsNeronReductionDatum ℓ R toF jac jac' (abZ := abZ) jacZ)

/-- **The integral point of the Jacobian model** attached to a rational
point, by the Néron mapping property. -/
noncomputable def intJ (x : RelPoint jstr (𝟙 SpecQ)) : RelPoint jstrZ (𝟙 (SpecLoc R)) :=
  (Equiv.ofBijective _ d.neronJ).symm
    (d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x)

/-- **The integral point of the curve model** attached to a rational
point, by the valuative criterion of properness. -/
noncomputable def intX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint xstr (𝟙 (SpecLoc R)) :=
  (Equiv.ofBijective _ d.properX).symm
    (d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) x)

/-- **Reduction of rational points of the Jacobian**: extend to the
integral model, then restrict to the special fibre. -/
noncomputable def redJ (x : RelPoint jstr (𝟙 SpecQ)) : RelPoint jstr' (𝟙 (SpecF ℓ)) :=
  (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
    (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ x))

/-- **Reduction of rational points of the curve.** -/
noncomputable def redX (x : RelPoint strX (𝟙 SpecQ)) : RelPoint strX' (𝟙 (SpecF ℓ)) :=
  (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
    (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x))

theorem redJ_def (x : RelPoint jstr (𝟙 SpecQ)) :
    d.redJ x = (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ x)) := rfl

theorem redX_def (x : RelPoint strX (𝟙 SpecQ)) :
    d.redX x = (d.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intX x)) := rfl

theorem pre_intJ (z : RelPoint jstr (𝟙 SpecQ)) :
    RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) (d.intJ z)
      = d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) z :=
  (Equiv.ofBijective _ d.neronJ).apply_symm_apply _

theorem pre_intX (z : RelPoint strX (𝟙 SpecQ)) :
    RelPoint.pre (SpecLoc.generic R) (Category.comp_id (SpecLoc.generic R)) (d.intX z)
      = d.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) z :=
  (Equiv.ofBijective _ d.properX).apply_symm_apply _

/-- Extending a rational point to the integral model is additive. -/
theorem intJ_add (x y : RelPoint jstr (𝟙 SpecQ)) :
    d.intJ (ab.add x y) = abZ.add (d.intJ x) (d.intJ y) := by
  apply d.neronJ.1
  rw [d.pre_intJ, abZ.pre_add, d.pre_intJ, d.pre_intJ, d.genJ_add]

/-- Extending a rational point to the integral model commutes with
Abel–Jacobi. -/
theorem intJ_aj (x : RelPoint strX (𝟙 SpecQ)) :
    d.intJ (jac.aj (𝟙 SpecQ) x) = jacZ.aj (𝟙 (SpecLoc R)) (d.intX x) := by
  apply d.neronJ.1
  rw [d.pre_intJ, d.genX_aj, ← d.pre_intX, jacZ.aj_pre]

/-- **`redJ_add` of `IsX0ReductionAt`, as a theorem.** -/
theorem redJ_add (x y : RelPoint jstr (𝟙 SpecQ)) :
    d.redJ (ab.add x y) = ab'.add (d.redJ x) (d.redJ y) := by
  apply (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).injective
  rw [d.spJ_add, redJ_def, redJ_def, redJ_def, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, d.intJ_add, abZ.pre_add]

/-- **`red_aj` of `IsX0ReductionAt`, as a theorem.** -/
theorem red_aj (x : RelPoint strX (𝟙 SpecQ)) :
    d.redJ (jac.aj (𝟙 SpecQ) x) = jac'.aj (𝟙 (SpecF ℓ)) (d.redX x) := by
  apply (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).injective
  rw [d.spX_aj, redJ_def, Equiv.apply_symm_apply, redX_def, Equiv.apply_symm_apply,
    d.intJ_aj, jacZ.aj_pre]

include d in
/-- **Rank `0` transports to the integral model**, along
`𝒥(ℤ_(ℓ)) ≅ J(ℚ)`. -/
theorem finite_intPoints (hfin : Finite (RelPoint jstr (𝟙 SpecQ))) :
    Finite (RelPoint jstrZ (𝟙 (SpecLoc R))) := by
  haveI := hfin
  exact Finite.of_equiv _
    ((d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _)).trans
      (Equiv.ofBijective _ d.neronJ).symm)

/-- **A Néron-pinned datum is a reduction datum** (PROVEN), given
injectivity of reduction on integral points — which is `X0.lean`'s
`neronReduction_injective`.

This is the whole point of the pinning: `redJ_add` and `red_aj` are no
longer assumptions about an arbitrary map but consequences of the maps
being induced by morphisms of models over `ℤ_(ℓ)`.

The target `IsX0ReductionAt` is `X0.lean`'s, and the `Γ₀` in its name is
an accident of where it was first needed: it mentions only a curve, its
Jacobian and Abel–Jacobi. -/
noncomputable def toReduction
    (hinj : Function.Injective
      (RelPoint.pre (SpecLoc.special toF) (Category.comp_id (SpecLoc.special toF)) :
        RelPoint jstrZ (𝟙 (SpecLoc R)) → RelPoint jstrZ (SpecLoc.special toF))) :
    IsX0ReductionAt jac jac' where
  redX := d.redX
  redJ := d.redJ
  redJ_add := d.redJ_add
  redJ_inj := by
    intro a b hab
    have h1 : RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ a)
        = RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) (d.intJ b) := by
      have h := congrArg
        (d.spJ (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)) hab
      rwa [redJ_def, redJ_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    have h2 := congrArg (RelPoint.pre (SpecLoc.generic R)
      (Category.comp_id (SpecLoc.generic R))) (hinj h1)
    rw [d.pre_intJ, d.pre_intJ] at h2
    exact (d.genJ (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _)).injective h2
  red_aj := d.red_aj

end IsNeronReductionDatum

/-! ### From a curve model to a full reduction datum -/

/-- **The Jacobian half needs no moduli problem: a curve model over
`ℤ_(ℓ)` extends to a full Néron reduction datum** (PROVEN).

Identical, line for line, to `X0.lean`'s
`exists_x0JacobianModel_of_curveModel` followed by the field copying of
`exists_x0NeronDatum_of_base`, with the single change that
`IsSmoothProperCurve xstr` is read off `cm.curve` rather than off
`cm.model`.  That substitution is the entire content of the hoist, and it
is why the `Γ₁` residue is one statement rather than a re-mirroring of a
200-line structure.

The mathematics is Grothendieck's relative Picard scheme, all of it
already in this tree: `exists_relativeJacobian` builds `Pic⁰` of a smooth
proper curve over an arbitrary base, `isSmoothProperCurve_of_fibreIdent`
recovers the geometry of the special fibre from its functor of points,
`exists_jacobianFibreIdent` says formation of the Jacobian commutes with
base change (with additivity and Abel–Jacobi compatibility), and
`bijective_pre_generic_of_isProper` is the Néron mapping property for a
proper model over `ℤ_(ℓ)`.

**The two base points are CONSTRUCTED, not chosen.**  `oZ` is the integral
point extending `o`, by `cm.properX`; `o'` is its reduction, by `cm.spX`.
That is forced: `ho` of `exists_jacobianFibreIdent` requires the base
points to correspond at both ends, and any other choice would translate
Abel–Jacobi and break `genX_aj` / `spX_aj`.  So the assembly has no
freedom left in it. -/
theorem exists_neronReductionDatum_of_curveModel (ℓ : ℕ) (R : Subring ℚ)
    (toF : R →+* ZMod ℓ) (hbase : IsReductionBase ℓ R toF)
    {X X' XZ : Scheme.{0}} {strX : X ⟶ SpecQ} {strX' : X' ⟶ SpecF ℓ}
    {xstr : XZ ⟶ SpecLoc R}
    (cm : IsCurveReductionModel ℓ R toF (strX := strX) (strX' := strX') xstr)
    {J : Scheme.{0}} {jstr : J ⟶ SpecQ} {ab : AbelianSchemeStruct jstr}
    {o : RelPoint strX (𝟙 SpecQ)} (jac : IsJacobianOf strX ab o) :
    ∃ (J' JZ : Scheme.{0}) (jstr' : J' ⟶ SpecF ℓ) (ab' : AbelianSchemeStruct jstr')
      (o' : RelPoint strX' (𝟙 (SpecF ℓ))) (jac' : IsJacobianOf strX' ab' o')
      (jstrZ : JZ ⟶ SpecLoc R) (abZ : AbelianSchemeStruct jstrZ)
      (oZ : RelPoint xstr (𝟙 (SpecLoc R))) (jacZ : IsJacobianOf xstr abZ oZ),
      Nonempty (IsNeronReductionDatum ℓ R toF jac jac' (abZ := abZ) jacZ) := by
  have hcurve : IsSmoothProperCurve xstr := cm.curve
  -- the integral point extending `o`, by the valuative criterion
  obtain ⟨oZ, hoZ⟩ : ∃ oZ : RelPoint xstr (𝟙 (SpecLoc R)),
      cm.genX (𝟙 SpecQ) (SpecLoc.generic R) (Category.id_comp _) o
        = RelPoint.pre (SpecLoc.generic R) (Category.comp_id _) oZ :=
    ⟨(Equiv.ofBijective _ cm.properX).symm _,
      ((Equiv.ofBijective _ cm.properX).apply_symm_apply _).symm⟩
  -- its reduction, the base point of the special fibre
  obtain ⟨o', ho'⟩ : ∃ o' : RelPoint strX' (𝟙 (SpecF ℓ)),
      cm.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _) o'
        = RelPoint.pre (SpecLoc.special toF) (Category.comp_id _) oZ :=
    ⟨(cm.spX (𝟙 (SpecF ℓ)) (SpecLoc.special toF) (Category.id_comp _)).symm _,
      Equiv.apply_symm_apply _ _⟩
  obtain ⟨JZ, jstrZ, abZ, ⟨jacZ⟩⟩ := exists_relativeJacobian xstr hcurve oZ
  obtain ⟨J', jstr', ab', ⟨jac'⟩⟩ :=
    exists_relativeJacobian strX' (isSmoothProperCurve_of_fibreIdent cm.spIdent hcurve) o'
  obtain ⟨eGen, eGen_add, eGen_aj⟩ :=
    exists_jacobianFibreIdent (SpecLoc.generic R) jacZ hcurve jac cm.genIdent hoZ
  obtain ⟨eSp, eSp_add, eSp_aj⟩ :=
    exists_jacobianFibreIdent (SpecLoc.special toF) jacZ hcurve jac' cm.spIdent ho'
  exact ⟨J', JZ, jstr', ab', o', jac', jstrZ, abZ, oZ, jacZ,
    ⟨{ base := hbase
       genX := cm.genX
       genJ := eGen.toEquiv
       spX := cm.spX
       spJ := eSp.toEquiv
       genX_nat := cm.genX_nat
       genJ_nat := eGen.nat
       spX_nat := cm.spX_nat
       spJ_nat := eSp.nat
       genJ_add := eGen_add
       spJ_add := eSp_add
       genX_aj := eGen_aj
       spX_aj := eSp_aj
       neronJ := bijective_pre_generic_of_isProper ℓ R toF hbase jstrZ abZ.proper
       properX := cm.properX }⟩⟩

end Fermat
