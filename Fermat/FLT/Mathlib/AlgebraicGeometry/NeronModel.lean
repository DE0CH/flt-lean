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

2. **A morphism from a smooth proper `ℤ_(q)`-curve into an abelian scheme extends**
   (`exists_neronExtension`).  An abelian scheme over a DVR is smooth and proper,
   hence IS the Néron model of its generic fibre, so
   `Hom_{ℤ_(q)}(𝒵, 𝒜) ≅ Hom_ℚ(𝒵_ℚ, A)` for every smooth `𝒵/ℤ_(q)`.
   *Reference:* Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Def. 1 and §7.4/3.

**BOTH ARE NOW PROVEN HERE** (2026-07-28), over material that was already in the
import cone — see the correction under "What is NOT here" below.  This module
contributes the faithfulness repair and the Yoneda glue, not new geometry.

Both are stated in the functor-of-points idiom this development uses throughout: a
model is a scheme over `SpecLoc R` together with an identification of the point sets
of its generic fibre with those of the `ℚ`-object, in the "identified base" form
`g ≫ SpecLoc.generic R = g₀`.

## THE FIBRE IDENTIFICATIONS CARRY THEIR NATURALITY HERE, and that is not decoration

**Every `gen…` family in this module comes with its `…_nat`, i.e. is an
`IsFibreIdent`.**  A bare family of bijections `RelPoint astr g ≃ RelPoint astrZ g₀`
with no naturality field is *point-set* data — it says the two functors of points
have the same cardinality at each test object and nothing else — and a statement
quantified over such a family is FALSE, not merely weak.  See the REFUTATION on
`exists_neronExtension` for the explicit witness, which is what forced this module's
2026-07-28 restatement.

With naturality in hand the whole module is Yoneda plus two upstream inputs:
`IsFibreIdent.apply_eq_comp` (`X0.lean`, PROVEN) says every value of a natural fibre
identification is composition with the image of the identity, so the
functor-of-points equation `genA_fmor` collapses to the single equation of morphisms
`uX ≫ fmor = fQ ≫ uA`.  That collapse is `genA_fmor_of_universalPoint` below and it
is PROVEN.

## Why here and not in `FreyCurve/MazurTorsion.lean`

Their one consumer today is `exists_abelianGoodReductionModel` there — the integral
half of Mazur's Eisenstein-quotient node — but neither statement knows that.  Both are
reusable **verbatim** by `ModularCurve/X1.lean` (which sits between this module and
`MazurTorsion.lean` in the import order) and by any other node that needs to spread a
`ℚ`-morphism out over `ℤ_(q)`.

## What is NOT here — and a STALE CLAIM this module used to make, CORRECTED

**The 2026-07-28 version of this section was WRONG, and it cost a duplicate leaf.**
It read: "Néron models themselves.  `grep -rn "NeronModel\|neronModel"` over this
project, over `Mathlib` at our pin and over `~/cs/FLT` returns nothing".  The mathlib
and `~/cs/FLT` halves are correct and were re-checked.  The PROJECT half is false, and
the very grep it prescribes disproves it: `X0.lean` carries a whole Néron block —

* `exists_goodAbelianReduction_of_abelianQuotient` (`X0.lean`, **PROVEN**) — good
  reduction propagates along a surjective homomorphism, delivered as
  `HasGoodAbelianReductionAtBase`, which packages the integral model, BOTH fibre
  identifications as `IsFibreIdent`s and the additivity of each;
* `exists_neronExtension_of_abelianScheme` (`X0.lean`, still an open leaf) — the
  Néron mapping property as an equation of morphisms;
* `exists_abelianSpread_of_neronModel` (`X0.lean`, PROVEN over the two above) — the
  same in the functor-of-points idiom.

`X0.lean` is this module's ONLY import, so all of it was in the cone the whole time.
Both leaves here are consequently PROVEN over it rather than opened as new sorries;
an earlier revision of this file opened `exists_neronExtensionHom`, a verbatim
restatement of `exists_neronExtension_of_abelianScheme` modulo the direction of one
equation, and it has been deleted.  The lesson is the doctrine's: a name that looks
like yours in the import cone is evidence to CHECK the cone, not a coincidence.

What genuinely remains missing is the Néron–Ogg–Šafarevič criterion under those names
(`grep -rn "OggSafarevic\|NeronOgg\|OggShafarevich"` over all three trees: no hits
outside this docstring) and the `ℓ`-adic Tate module of an abelian SCHEME; what exists
is the `[n]`-torsion subscheme API of `Modularity/AbelianSchemeIsogeny.lean`.  The
project also has the mapping property for the base itself,
`bijective_pre_generic_of_isProper` (`X0.lean`), i.e. on `ℤ_(q)`-POINTS: the valuative
criterion applied to a proper morphism.  The gap between that and
`exists_neronExtension_of_abelianScheme` is exactly the passage from a point to a
general smooth `𝒵`, and that is where the residual mathematics of this module now
lives — in `X0.lean`, under one owner, rather than in two places.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace Fermat

/-- **A model of `A/ℚ` over `ℤ_(q)` with GOOD REDUCTION**: an abelian scheme
`𝒜/ℤ_(q)` whose generic fibre is `A`.

The generic-fibre identification is stated on the functor of points, in the
"identified base" form the rest of this development uses, and it carries its
NATURALITY (`genA_nat`), so it is an `IsFibreIdent (SpecLoc.generic R) astrZ astr` and
by Yoneda (`IsFibreIdent.compareIso`) genuinely says `A ≅ 𝒜 ×_{ℤ_(q)} ℚ`.  The special
fibre is deliberately absent: it is a base change of `𝒜` and so is a construction
rather than a datum (`fibreIdentPullback` together with
`AbelianSchemeStruct.baseChange`), which is exactly how
`exists_abelianGoodReductionModel` discharges it.

**`genA_nat` was ADDED 2026-07-28, and it is what makes this structure mean what its
name says.**  Without it `genA` is a bare family of bijections of point SETS, so
"model of `A`" degenerates to "abelian scheme whose functor of points happens to be
equinumerous with `A`'s at every test object" — and, more importantly, the consumer
`exists_neronExtension` is then FALSE (see the REFUTATION there).  Adding it costs the
prover of `exists_goodReductionModel_of_surjective` nothing, because the honest
witness — the Néron model of `A`, with the canonical identification of its generic
fibre — is natural on the nose. -/
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
  /-- **naturality of the generic identification**: it is a natural equivalence of
  functors of points, not a family of unrelated bijections -/
  genA_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
    (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
    (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
    (x : RelPoint astr g),
    genA g' g₀' h₀' (RelPoint.pre h hg x)
      = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genA g g₀ h₀ x)

/-- **The spread-out of a `ℚ`-morphism `fQ : X ⟶ A` over `ℤ_(q)`**, read as an
extension of `fQ` through the two generic-fibre identifications.

Both identifications are now PARAMETERS (`genX`, `genA`) rather than one being a
field: `genA` was an output field until 2026-07-28, on the theory that emitting it
kept the leaf no stronger than its consumer.  It did — and the consumer was FALSE.
See the REFUTATION on `exists_neronExtension`.  With naturality supplied for both,
`genA` can be received honestly and this structure is three fields. -/
structure IsNeronExtensionOver (R : Subring ℚ) {X XZ A AZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {xstr : XZ ⟶ SpecLoc R} {astr : A ⟶ SpecQ}
    (astrZ : AZ ⟶ SpecLoc R)
    (genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀)
    (genA : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint astr g ≃ RelPoint astrZ g₀)
    (fQ : X ⟶ A) (hfQ : fQ ≫ astr = strX) where
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

**THE CONCLUSION WAS STRENGTHENED 2026-07-28** by the `genA_nat` field of
`IsGoodReductionModel`: the emitted identification must be a NATURAL equivalence of
functors of points, hence by Yoneda an isomorphism `A ≅ 𝒜 ×_{ℤ_(q)} ℚ`.  This costs
the prover nothing (the Néron model's own identification is natural) and it is what
the consumer needs; before the change the leaf could in principle have been
discharged by an abelian scheme merely equinumerous with `A` at every test object,
which is not "a model of `A`" in any usable sense.

**NON-VACUITY.**  `A := J`, `u := 𝟙`, `abA := ab` satisfies every hypothesis, so no
proof can discharge this by contradicting them; and the conclusion is then witnessed
by the given model together with the identity identification — which is natural, so
the strengthened conclusion is still satisfiable by the obvious witness.

**PROVEN 2026-07-28, and it needed no new geometry — only `genJ_nat`.**  The
statement above was opened as a leaf on the belief, recorded in the previous version
of this docstring, that "Néron models exist in neither `Mathlib` at our pin, nor
`~/cs/FLT`, nor this project".  The first two clauses are right; the third is FALSE.
`exists_goodAbelianReduction_of_abelianQuotient` (`X0.lean`, PROVEN) is exactly this
statement, and `X0.lean` is this module's only import.  What separated the two was
one hypothesis: that theorem takes `genJ` as an `IsFibreIdent`, i.e. WITH its
naturality, and this leaf took it bare.  `genJ_nat` is now a hypothesis here, and the
consumer chain already held it (`IsX0JacobianModel.genJ_nat`, which `X0.lean` itself
passes to the same theorem as `⟨jm.genJ, jm.genJ_nat⟩`).

Two consequences worth recording.  `_hadd` is no longer needed — the upstream theorem
manufactures the additive structure itself via `exists_isAdditiveOn_comp` — and is
kept only so the consumer's call site does not have to change; it is underscored.  And
the conclusion is now genuinely a MODEL: `HasGoodAbelianReductionAtBase` hands back
`genA` as an `IsFibreIdent`, so `genA_nat` is discharged on the nose rather than
demanded of a future prover.

**WHAT IS STILL MISSING, re-checked by name 2026-07-28.**  The Néron–Ogg–Šafarevič
criterion under that name (`grep -rn "OggSafarevic\|NeronOgg\|OggShafarevich"` over
this project, `Mathlib` at our pin and `~/cs/FLT`: no hits outside docstrings) and the
`ℓ`-adic Tate module of an abelian SCHEME; what exists is the `[n]`-torsion subscheme
API of `Modularity/AbelianSchemeIsogeny.lean`.  Neither is needed HERE, because the
route through `X0.lean` reaches good reduction by the model-theoretic argument rather
than the Tate-module one. -/
theorem exists_goodReductionModel_of_surjective (q : ℕ) (_hq : q.Prime)
    (R : Subring ℚ) (toF : R →+* ZMod q) (hbase : IsReductionBase q R toF)
    {J JZ A : Scheme.{0}} {jstr : J ⟶ SpecQ} {jstrZ : JZ ⟶ SpecLoc R} {astr : A ⟶ SpecQ}
    (_ab : AbelianSchemeStruct jstr) (abZ : AbelianSchemeStruct jstrZ)
    (abA : AbelianSchemeStruct astr)
    (genJ : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint jstr g ≃ RelPoint jstrZ g₀)
    (genJ_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
      (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
      (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
      (x : RelPoint jstr g),
      genJ g' g₀' h₀' (RelPoint.pre h hg x)
        = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genJ g g₀ h₀ x))
    (u : J ⟶ A) (hu : u ≫ astr = jstr)
    (_hadd : IsAdditiveOn _ab abA u hu) (hsurj : AlgebraicGeometry.Surjective u) :
    Nonempty (IsGoodReductionModel R astr) := by
  obtain ⟨_A', AZ, _astr', _ab', astrZ, abZ', genA, _spA, -, -⟩ :=
    exists_goodAbelianReduction_of_abelianQuotient q R toF hbase abZ
      ⟨genJ, genJ_nat⟩ abA u hu hsurj
  exact ⟨{ AZ := AZ
           astrZ := astrZ
           abZ := abZ'
           genA := genA.toEquiv
           genA_nat := genA.nat }⟩

/-- **Yoneda: the functor-of-points extension equation IS one equation of morphisms**
(PROVEN, new 2026-07-28).

`genA_fmor` quantifies over every test scheme `T`, every base point `g` and every
relative point `x`; this lemma discharges the whole family from the single equation
`uX ≫ fmor = fQ ≫ uA` between the two universal points.  It is `apply_eq_comp`
(`X0.lean`) applied twice and associativity — nothing else — and it is what lets
`exists_neronExtensionHom` be stated in the shape a geometer can attack.

Note that naturality of BOTH identifications is used, once each: `eA` to rewrite the
left-hand side, `eX` the right.  This is the precise place where the pre-2026-07-28
statement, which had neither, could not be repaired. -/
theorem genA_fmor_of_universalPoint {R : Subring ℚ} {X XZ A AZ : Scheme.{0}}
    {strX : X ⟶ SpecQ} {xstr : XZ ⟶ SpecLoc R} {astr : A ⟶ SpecQ} {astrZ : AZ ⟶ SpecLoc R}
    (eX : IsFibreIdent (SpecLoc.generic R) xstr strX)
    (eA : IsFibreIdent (SpecLoc.generic R) astrZ astr)
    {fQ : X ⟶ A} (hfQ : fQ ≫ astr = strX) {fmor : XZ ⟶ AZ} (hover : fmor ≫ astrZ = xstr)
    (hcomm : eX.universalPoint.1 ≫ fmor = fQ ≫ eA.universalPoint.1)
    {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R)
    (h : g ≫ SpecLoc.generic R = g₀) (x : RelPoint strX g) :
    eA.toEquiv g g₀ h (RelPoint.post fQ hfQ x)
      = RelPoint.post fmor hover (eX.toEquiv g g₀ h x) := by
  refine Subtype.ext ?_
  rw [eA.apply_eq_comp g g₀ h (RelPoint.post fQ hfQ x)]
  show (x.1 ≫ fQ) ≫ eA.universalPoint.1 = (eX.toEquiv g g₀ h x).1 ≫ fmor
  rw [eX.apply_eq_comp g g₀ h x, Category.assoc, ← hcomm, Category.assoc]

/-- **A morphism from a smooth `ℤ_(q)`-scheme into an abelian scheme extends across
the special fibre** (opened 2026-07-28 as a bare `sorry`; **REFUTED AS FIRST STATED
and RESTATED the same day; now PROVEN** over `exists_neronExtensionHom`) — the Néron
mapping property, in the functor-of-points idiom its consumer speaks.

## REFUTATION of the 2026-07-28 statement, with an explicit witness

The leaf as first cut took `genX` (and `genA₀`) as BARE families of bijections with
**no naturality field**, and emitted `genA` as a field of `IsNeronExtensionOver` — the
FAITHFULNESS NOTE it carried argued that emitting `genA` "keeps the cut exactly as
strong as its consumer and no stronger".  The first half is right and the second is
the trap: the consumer was itself false, and emitting `genA` does not repair it,
because `fmor` must be an actual morphism of schemes while `genX` need not be
anything at all.

**Witness.**  Let `A` be the elliptic curve `11a3` (`X_1(11)`), `y² + y = x³ - x²`, of
conductor `11`; verified with PARI: `A(ℚ) ≅ ℤ/5`, rank `0`, `Δ = -11`, `j = -4096/11`,
`End_ℚ A = ℤ` (no CM, `j ∉ ℤ`).  Take `q = 3`, `R = ℤ_(3)`, at which `A` has good
reduction, and let `𝒜/ℤ_(3)` be its Néron model — an abelian scheme, so `abZ` holds —
with `A ≅ 𝒜_ℚ`.  Now take

* `X := A ⊔ A` and `XZ := 𝒜 ⊔ 𝒜` (a coproduct of smooth `R`-schemes is smooth, so
  `hsm` holds), with `fQ := ∇` the codiagonal `A ⊔ A ⟶ A`;
* `genA₀ :=` the canonical identification (natural, so certainly admissible);
* `genX :=` the canonical identification at every test object EXCEPT
  `(T, g, g₀) = (Spec ℚ, 𝟙, SpecLoc.generic R)`, where it is post-composed with the
  permutation of `RelPoint xstr g₀ ≅ A(ℚ) ⊔ A(ℚ)` that fixes the first summand and
  acts on the second by the transposition `σ = (0 1)` of `A(ℚ) ≅ ℤ/5`.  Every value
  is still a bijection, so `genX` typechecks; it is simply not natural.

Every hypothesis of the old statement holds.  Now read the conclusion at that one test
object.  A morphism `fmor : 𝒜 ⊔ 𝒜 ⟶ 𝒜` over `R` is a PAIR `(f₀, f₁)` of morphisms
`𝒜 ⟶ 𝒜` (universal property of the coproduct), and `genA_fmor` at `x = (0, P)` and at
`x = (1, P)` reads

    genA P = f₀ P    and    genA P = f₁ (σ P)     for every P ∈ A(ℚ),

so `f₀ = f₁ ∘ σ` on `A(ℚ)`, with `f₀` bijective there because `genA` is.  By rigidity
every morphism of abelian varieties is a homomorphism followed by a translation, and
`End_ℚ A = ℤ`, so `f_i` acts on `A(ℚ) ≅ ℤ/5` as `u ↦ m_i u + c_i`.  Bijectivity forces
`m₀, m₁ ∈ (ℤ/5)ˣ`, whence `σ (u) = m₁⁻¹ (m₀ u + c₀ - c₁)` is AFFINE.  But `σ` is the
transposition `(0 1)`: it fixes `2`, so `2 m₁⁻¹ m₀ + k = 2`, and `σ 0 = 1`, `σ 1 = 0`
force `m₁⁻¹ m₀ = -1` and then `σ 2 = -2 + 1 = 4 ≠ 2`.  Contradiction.  So no `fmor`
and no `genA` exist, and the old statement was **false**.

The same witness refutes the old `exists_abelianGoodReductionModel`
(`FreyCurve/MazurTorsion.lean`) verbatim — there `AZ` is an output, but `f₀, f₁`
become morphisms `𝒜 ⟶ 𝒜'` into some other abelian scheme and are still homomorphisms
plus translations, so `σ` is still forced affine.  That is where the missing
hypothesis actually belonged, and it is now carried there.

## THE REPAIR, and it cost the caller nothing

`genX` and `genA` now arrive with their naturality (`genX_nat`, `genA_nat`), i.e. as
`IsFibreIdent`s, and `genA` is a PARAMETER rather than an emitted field.  The missing
hypothesis was already in the caller's hand, which is the shape CLAUDE.md records as
usual for this development: `exists_abelianGoodReductionModel`'s only caller,
`exists_eisensteinQuotientModel_of_jNeronDatum`, holds `d.genX_nat` and was
discarding it; and `genA_nat` is now a field of `IsGoodReductionModel`, supplied by
the sibling leaf that produces the model.  The old docstring named exactly this repair
and declined it as "a cut-level repair and this node's owner is not the caller's" —
correct about ownership, and the cost of declining was a false statement in the tree.

## What this proof is, and where the geometry actually lives

Yoneda and nothing else.  `genA_fmor_of_universalPoint` collapses the whole family of
functor-of-points equations to `uX ≫ fmor = fQ ≫ uA`, and that morphism equation is
`exists_neronExtension_of_abelianScheme` — which is in `X0.lean`, this module's only
import, and was there before this module existed.

**An earlier revision of this file opened that equation as a NEW leaf,
`exists_neronExtensionHom`, having believed the docstring claim that Néron models were
absent from this project.**  They are not; the claim was stale.  The duplicate has been
deleted and the residual mathematics is left where it already had a home.  The one
visible cost of consuming the existing leaf is its hypothesis: it asks for
`IsSmoothProperCurve xstr` where this statement previously asked only for
`Smooth xstr`.  That is a genuine narrowing — but the upstream docstring records that
"only SMOOTHNESS of `xstr` is used", so whoever proves it can widen both in one edit,
and the sole consumer here is a modular-curve model that has properness and connected
fibres in hand anyway.

**NON-VACUITY.**  `X := A`, `XZ := AZ`, `fQ := 𝟙`, `genX := genA`, `fmor := 𝟙`
satisfies every hypothesis and every conclusion, so no proof can discharge this by
contradicting its hypotheses. -/
theorem exists_neronExtension (q : ℕ) (R : Subring ℚ) (toF : R →+* ZMod q)
    (hbase : IsReductionBase q R toF)
    {X XZ A AZ : Scheme.{0}} {strX : X ⟶ SpecQ} {xstr : XZ ⟶ SpecLoc R}
    {astr : A ⟶ SpecQ} {astrZ : AZ ⟶ SpecLoc R}
    (hcurve : IsSmoothProperCurve xstr) (abZ : AbelianSchemeStruct astrZ)
    (genX : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint strX g ≃ RelPoint xstr g₀)
    (genX_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
      (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
      (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
      (x : RelPoint strX g),
      genX g' g₀' h₀' (RelPoint.pre h hg x)
        = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genX g g₀ h₀ x))
    (genA : ∀ {T : Scheme.{0}} (g : T ⟶ SpecQ) (g₀ : T ⟶ SpecLoc R),
      g ≫ SpecLoc.generic R = g₀ → RelPoint astr g ≃ RelPoint astrZ g₀)
    (genA_nat : ∀ {T' T : Scheme.{0}} (h : T' ⟶ T) {g : T ⟶ SpecQ} {g' : T' ⟶ SpecQ}
      (hg : h ≫ g = g') {g₀ : T ⟶ SpecLoc R} {g₀' : T' ⟶ SpecLoc R}
      (h₀ : g ≫ SpecLoc.generic R = g₀) (h₀' : g' ≫ SpecLoc.generic R = g₀')
      (x : RelPoint astr g),
      genA g' g₀' h₀' (RelPoint.pre h hg x)
        = RelPoint.pre h (by rw [← h₀, ← Category.assoc, hg, h₀']) (genA g g₀ h₀ x))
    (fQ : X ⟶ A) (hfQ : fQ ≫ astr = strX) :
    Nonempty (IsNeronExtensionOver R astrZ genX genA fQ hfQ) := by
  obtain ⟨fmor, hover, hcomm⟩ :=
    exists_neronExtension_of_abelianScheme q R toF hbase hcurve abZ
      ⟨genX, genX_nat⟩ ⟨genA, genA_nat⟩ fQ hfQ
  exact ⟨{ fmor := fmor
           fmor_over := hover
           genA_fmor := genA_fmor_of_universalPoint
             ⟨genX, genX_nat⟩ ⟨genA, genA_nat⟩ hfQ hover hcomm.symm }⟩

end Fermat
