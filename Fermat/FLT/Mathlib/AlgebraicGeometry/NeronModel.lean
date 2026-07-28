/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.ModularCurve.X0

/-!
# Good reduction of abelian varieties, and the Néron mapping property

Two classical facts about an abelian variety `A/ℚ` and a prime `q`, stated over the
base `Spec ℤ_(q)` that `IsReductionBase` pins (`ModularCurve/X0.lean`), and carrying
**no modular content whatever** — nothing here mentions a modular curve, a Hecke
operator or a cusp:

1. **Good reduction propagates along a surjective homomorphism**
   (`exists_goodReductionModel_of_surjective`).  If `J/ℚ` has good reduction at `q`
   and `u : J ↠ A` is a surjective homomorphism of abelian varieties over `ℚ`, then
   `A` has good reduction at `q`.  For `ℓ ≠ q` the `ℓ`-adic Tate module `V_ℓ A` is a
   `Γ_ℚ`-quotient of `V_ℓ J`, which is unramified at `q` by Néron–Ogg–Šafarevič;
   hence `V_ℓ A` is unramified, hence `A` has good reduction by the converse half of
   the same criterion.
   *Reference:* Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. **88**
   (1968), Thm 1 and Cor. 2; Bosch–Lütkebohmert–Raynaud, *Néron Models*, §7.4.

2. **A morphism from a smooth `ℤ_(q)`-scheme into an abelian scheme extends**
   (`exists_neronExtension`).  An abelian scheme over a DVR is smooth and proper,
   hence IS the Néron model of its generic fibre, so
   `Hom_{ℤ_(q)}(𝒵, 𝒜) ≅ Hom_ℚ(𝒵_ℚ, A)` for every smooth `𝒵/ℤ_(q)`.
   *Reference:* Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Def. 1 and §7.4/3.

Both are stated in the functor-of-points idiom this development uses throughout: a
model is a scheme over `SpecLoc R` together with an identification of the point sets
of its generic fibre with those of the `ℚ`-object, in the "identified base" form
`g ≫ SpecLoc.generic R = g₀`.

## Why here and not in `FreyCurve/MazurTorsion.lean`

Their one consumer today is `exists_abelianGoodReductionModel` there — the integral
half of Mazur's Eisenstein-quotient node — but neither statement knows that.  Both are
reusable **verbatim** by `ModularCurve/X1.lean` (which sits between this module and
`MazurTorsion.lean` in the import order) and by any other node that needs to spread a
`ℚ`-morphism out over `ℤ_(q)`.

## What is NOT here

Néron models themselves.  `grep -rn "NeronModel\|neronModel"` over this project,
over `Mathlib` at our pin and over `~/cs/FLT` returns nothing, and neither does the
Néron–Ogg–Šafarevič criterion; the same grep for Tate modules of abelian schemes
returns only the `[n]`-torsion API of `Modularity/AbelianSchemeIsogeny.lean`.  What
this project DOES have is the mapping property for the base itself,
`bijective_pre_generic_of_isProper` (`X0.lean`), i.e. on `ℤ_(q)`-POINTS: the
valuative criterion applied to a proper morphism.  The gap between that and
`exists_neronExtension` is exactly the passage from a point to a general smooth `𝒵`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Fermat

/-- **A model of `A/ℚ` over `ℤ_(q)` with GOOD REDUCTION**: an abelian scheme
`𝒜/ℤ_(q)` whose generic fibre is `A`.

The generic-fibre identification is stated on the functor of points, in the
"identified base" form the rest of this development uses, so by Yoneda `genA` says
`A ≅ 𝒜 ×_{ℤ_(q)} ℚ`.  The special fibre is deliberately absent: it is a base change
of `𝒜` and so is a construction rather than a datum (`fibreIdentPullback` together
with `AbelianSchemeStruct.baseChange`), which is exactly how
`exists_abelianGoodReductionModel` discharges it.

Note there is no naturality field, matching `IsAbelianGoodReductionModel`'s `genA` in
`FreyCurve/MazurTorsion.lean`, whose shape this is designed to feed. -/
structure IsGoodReductionModel (R : Subring ℚ) {A : Scheme.{0}} (astr : A ⟶ SpecQ) where
  /-- the integral model `𝒜/ℤ_(q)` -/
  AZ : Scheme.{0}
  /-- its structure morphism to `Spec ℤ_(q)` -/
  astrZ : AZ ⟶ SpecLoc R
  /-- **good reduction**: `𝒜` is an abelian scheme over the whole of `ℤ_(q)` -/
  abZ : AbelianSchemeStruct astrZ
  /-- the generic fibre of the model is `A`, functorially -/
  genA : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint astr g ≃ RelPoint astrZ g₀

/-- **The spread-out of a `ℚ`-morphism `fQ : X ⟶ A` over `ℤ_(q)`**, together with the
generic-fibre identification through which it is read as an extension of `fQ`.

`genA` is a FIELD rather than a parameter, and that is deliberate — see the
FAITHFULNESS NOTE on `exists_neronExtension`.  With `genA` fixed in advance the
statement would be strictly stronger than the node it exists to serve, because
`IsAbelianGoodReductionModel` produces its own `genA` and a prover of that node may
choose it after seeing `genX`. -/
structure IsNeronExtensionOver (R : Subring ℚ) {X XZ A AZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {xstr : XZ ⟶ SpecLoc R} {astr : A ⟶ SpecQ}
    (astrZ : AZ ⟶ SpecLoc R)
    (genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀)
    (fQ : X ⟶ A) (hfQ : fQ ≫ astr = strX) where
  /-- the generic fibre of the model is `A`, functorially -/
  genA : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
    g ≫ SpecLoc.generic R = g₀ → RelPoint astr g ≃ RelPoint astrZ g₀
  /-- the spread-out of `fQ`, as a morphism of integral models -/
  fmor : XZ ⟶ AZ
  /-- `fmor` is a morphism over `ℤ_(q)` -/
  fmor_over : fmor ≫ astrZ = xstr
  /-- **`fmor` really extends `fQ`**: on the generic fibre the two agree, at every
  test scheme and every base point -/
  genA_fmor : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x : RelPoint strX g),
    genA g g₀ h (RelPoint.post fQ hfQ x) = RelPoint.post fmor fmor_over (genX g g₀ h x)

/-- **Good reduction propagates along a surjective homomorphism of abelian
varieties** (sorry leaf, new 2026-07-28) — Néron–Ogg–Šafarevič, in the form
Serre–Tate state it.

TRUE.  `u : J ↠ A` is a surjective homomorphism of abelian varieties over `ℚ` and `J`
has good reduction at `q` — that is `abZ` together with `genJ`.  For `ℓ ≠ q` the
`ℓ`-adic Tate module `V_ℓ A` is a quotient of `V_ℓ J` as a `Γ_ℚ`-module (a surjective
homomorphism of abelian varieties is surjective on Tate modules up to isogeny),
`V_ℓ J` is unramified at `q` by Néron–Ogg–Šafarevič, hence so is `V_ℓ A`, hence `A`
has good reduction at `q` by the converse half of the same criterion.

**REFERENCES.**  Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. **88**
(1968), Thm 1 (the criterion) and Cor. 2 (its behaviour under isogeny and quotient);
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §7.4.

**WHERE THE HYPOTHESES ENTER, and none is decoration.**  `abZ` with `genJ` is "`J` has
good reduction at `q`", the whole input to the criterion; `hsurj` is what makes
`V_ℓ A` a QUOTIENT of `V_ℓ J` rather than an arbitrary Galois module — **drop it and
the statement is FALSE**, since every abelian variety over `ℚ` admits the ZERO
homomorphism from `J`, including ones with bad reduction at `q` (e.g. `X_0(11)`,
conductor `11`, at `q = 11`); `hadd` is what makes `u` act on Tate modules at all;
`hbase` pins `R` as `ℤ_(q)`, without which "good reduction at `q`" is not a statement
about `R`.  They are underscored only because a sorried body uses nothing.

**NON-VACUITY.**  `A := J`, `u := 𝟙`, `abA := ab` satisfies every hypothesis, so no
proof can discharge this by contradicting them; and the conclusion is then witnessed
by the given model, so the hypotheses are consistent with the conclusion too.

**WHAT IS GENUINELY MISSING, checked by name 2026-07-28.**  Néron models exist in
neither `Mathlib` at our pin, nor `~/cs/FLT`, nor this project (`grep -rn
"NeronModel\|neronModel"` over all three: no hits), and neither does the
Néron–Ogg–Šafarevič criterion (`grep -rn "OggSafarevic\|NeronOgg\|criterion.*unramified"`:
no hits).  The `ℓ`-adic Tate module of an abelian SCHEME is likewise absent; what
exists is the `[n]`-torsion subscheme API of `Modularity/AbelianSchemeIsogeny.lean`,
which is the right starting point for building `T_ℓ`. -/
theorem exists_goodReductionModel_of_surjective (q : ℕ) (_hq : q.Prime)
    (R : Subring ℚ) (toF : R →+* ZMod q) (_hbase : IsReductionBase q R toF)
    {J JZ A : Scheme.{0}} {jstr : J ⟶ SpecQ} {jstrZ : JZ ⟶ SpecLoc R} {astr : A ⟶ SpecQ}
    (ab : AbelianSchemeStruct jstr) (_abZ : AbelianSchemeStruct jstrZ)
    (abA : AbelianSchemeStruct astr)
    (_genJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint jstr g ≃ RelPoint jstrZ g₀)
    (u : J ⟶ A) (hu : u ≫ astr = jstr)
    (_hadd : IsAdditiveOn ab abA u hu) (_hsurj : AlgebraicGeometry.Surjective u) :
    Nonempty (IsGoodReductionModel R astr) :=
  sorry

/-- **A morphism from a smooth `ℤ_(q)`-scheme into an abelian scheme extends across
the special fibre** (sorry leaf, new 2026-07-28) — the Néron mapping property.

TRUE.  An abelian scheme over a DVR is proper and smooth, hence IS the Néron model of
its generic fibre, so `Hom_{ℤ_(q)}(𝒵, 𝒜) ≅ Hom_ℚ(𝒵_ℚ, A)` for every SMOOTH
`𝒵/ℤ_(q)`.  Applied to `𝒵 = 𝒳`, which is smooth by `hsm`, this gives `fmor` and
`genA_fmor`, with the honest `genA := genA₀`; uniqueness of the extension is what
makes the pair canonical.

**REFERENCES.**  Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Def. 1 (the mapping
property) and §7.4/3 (an abelian scheme is its own Néron model); Serre–Tate, Ann. of
Math. **88** (1968), §1.

**WHERE THE HYPOTHESES ENTER, and none is decoration.**  `hsm` is the smoothness of
`𝒳` without which the Néron mapping property says nothing about morphisms out of it —
**drop it and the statement is FALSE**: for a non-smooth `𝒳` a `ℚ`-morphism need not
extend, the standard witness being `𝒳 = Spec ℤ_(q)[x,y]/(xy - q)` and an elliptic
curve `A` with a `ℚ`-point that does not reduce; `abZ` is what makes `𝒜` proper and
smooth, i.e. a Néron model at all; `genA₀` is what says `𝒜` is a model **of `A`**
rather than an unrelated abelian scheme — drop it and the statement is FALSE, because
`RelPoint astr g` and `RelPoint astrZ g₀` then need not even be in bijection;
`hbase` pins `R` as a DVR with fraction field `ℚ`.  They are underscored only because
a sorried body uses nothing.

**FAITHFULNESS NOTE — why `genA` is an OUTPUT, and what would let it become an
input.**  `genX` here is a bare family of bijections with **no naturality field**: it
is `IsAbelianGoodReductionModel`'s `genX` parameter, which arrives from
`IsX0JNeronDatum.genX` at the use site but loses `genX_nat` in transit through
`exists_abelianGoodReductionModel`'s signature.  Against a junk `genX` the honest
`genA₀` need not satisfy `genA_fmor`, so pinning `genA := genA₀` would make this leaf
strictly stronger than the node it serves — that node produces its own `genA` and may
choose it after seeing `genX`.  Emitting `genA` keeps the cut exactly as strong as its
consumer and no stronger.

**The cheap repair, for whoever owns `exists_abelianGoodReductionModel` next:** carry
`genX_nat` (naturality of `genX`, i.e. make `genX` an `IsFibreIdent`) as a hypothesis
there.  Its only caller, `exists_eisensteinQuotientModel_of_jNeronDatum`, already
holds it as `d.genX_nat` and is discarding it — the shape CLAUDE.md records as usual
for this development.  With naturality in hand `genA` can go back to being a
parameter and this structure collapses to three fields.

**NON-VACUITY.**  `X := A`, `XZ := AZ`, `fQ := 𝟙`, `genX := genA₀`,
`fmor := 𝟙` satisfies every hypothesis and every conclusion (an abelian scheme is
smooth over its base, `AbelianSchemeStruct.smooth`), so no proof can discharge this by
contradicting its hypotheses.

**WHAT IS GENUINELY MISSING, checked by name 2026-07-28.**  As for
`exists_goodReductionModel_of_surjective`: Néron models are absent from all three
trees.  The nearest thing present is `bijective_pre_generic_of_isProper` (`X0.lean`),
which is this statement for `𝒵 = Spec ℤ_(q)` — the valuative criterion of properness,
proven there from `ValuationRing ↥R`.  The gap is exactly the passage from a point to
a general smooth `𝒵`, i.e. from properness alone to properness plus smoothness of the
TARGET (the weak Néron property), which is where BLR §1.2 does its work. -/
theorem exists_neronExtension (q : ℕ) (R : Subring ℚ) (toF : R →+* ZMod q)
    (_hbase : IsReductionBase q R toF)
    {X XZ A AZ : Scheme.{0}} {strX : X ⟶ SpecQ} {xstr : XZ ⟶ SpecLoc R}
    {astr : A ⟶ SpecQ} {astrZ : AZ ⟶ SpecLoc R}
    (_hsm : Smooth xstr) (_abZ : AbelianSchemeStruct astrZ)
    (genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀)
    (_genA₀ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint astr g ≃ RelPoint astrZ g₀)
    (fQ : X ⟶ A) (hfQ : fQ ≫ astr = strX) :
    Nonempty (IsNeronExtensionOver R astrZ genX fQ hfQ) :=
  sorry

end Fermat
