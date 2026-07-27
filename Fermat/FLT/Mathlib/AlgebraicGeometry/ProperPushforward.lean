/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced

/-!
# Coherent pushforward along a proper morphism: `f_*𝒪_X = 𝒪_S`, and the rigidity lemma

For a **proper flat** morphism of finite presentation `f : X ⟶ S` whose fibres are
**geometrically connected and geometrically reduced**, the unit
`𝒪_S ⟶ f_*𝒪_X` is an isomorphism, and stays one after every base change
(Hartshorne III.12, Mumford *Abelian Varieties* §5, Stacks 0E6R / 0BUG).  This is the
single classical input behind every rigidity statement about abelian schemes, and it is
absent from `Mathlib` at this pin, from `~/cs/FLT`, and from this project — checked
2026-07-27 by grepping all three for `higherDirectImage`, `directImage` and any
cohomology-and-base-change API: there are **zero hits**, and `Mathlib` has no higher
direct images of quasi-coherent sheaves at all.

## What is here

* `AlgebraicGeometry.HasTrivialPushforward f` — the statement `𝒪_S ≅ f_*𝒪_X`, written as
  "`f.app U` is an isomorphism for every open `U ⊆ S`".  That is literally the assertion
  that the map of sheaves `𝒪_S ⟶ f_*𝒪_X` — whose component at `U` *is* `f.app U`, by
  `Scheme.Hom.app` — is an isomorphism, so no separate sheaf-level definition is needed.
* `AlgebraicGeometry.HasUniversallyTrivialPushforward f` — the same, universally.  The
  universal form is the one the rigidity lemma consumes: its proof base-changes `f` along
  an arbitrary `Y ⟶ S`, and `𝒪_S = f_*𝒪_X` alone does not survive that (it does under
  flatness + geometric connectedness + geometric reducedness, which is exactly what the
  main theorem below asserts).
* `isIso_appTop_of_isProper_of_flat` — **THE LEAF** (2026-07-27): `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is
  an isomorphism, for a single fixed `f` with the classical hypotheses.  This is all that
  is left of the theorem: see the next item.
* `hasUniversallyTrivialPushforward_of_isProper_of_flat` — **PROVEN** over that leaf.  Both
  of the theorem's quantifiers turned out to be bookkeeping rather than mathematics: all
  five hypotheses are stable under base change, and an open restriction `f ∣_ U` is itself
  a base change (`isPullback_morphismRestrict`), so `∀ U, IsIso (f.app U)` *and* the
  `universally` wrapper both reduce to the single global-sections statement above.
* `geometricallyReduced_of_smooth` — **PROVEN** (2026-07-27), as a re-export of
  `AlgebraicGeometry.GeometricallyReduced.of_smooth` from
  `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`.  It used to be a
  leaf of this file; the mathematical content now sits, once, in that file's single
  ring-theoretic leaf `Algebra.Smooth.isReduced_of_isField` (a smooth algebra over a field
  is reduced — a genuine `Mathlib` gap, and *unowned* as of this writing).
* `hasUniversallyTrivialPushforward_of_isProper_of_smooth` — PROVEN from those two.  This
  is the form every consumer in this development actually applies, because an abelian
  scheme and a smooth proper curve are both given as *smooth* rather than as *flat with
  reduced fibres*.
* `exists_comp_snd_eq_of_slice_const` — **LEAF**: the RIGIDITY LEMMA (Mumford *AV* §4;
  BLR *Néron Models* 8.4 in the relative case).
* `eq_comp_of_rigidity_axes` — PROVEN from the rigidity lemma: a morphism
  `A ×_S A ⟶ B` vanishing on both axes vanishes.  This is the form in which rigidity is
  used to prove that a pointed morphism of abelian schemes is a homomorphism.

## FAITHFULNESS NOTE on the rigidity lemma: the second factor MUST be connected

The rigidity lemma is often quoted with `Y` an arbitrary `S`-scheme.  In that generality
it is **FALSE**, and the counterexample is one line: take `S = Spec k`, `X = ℙ¹`,
`Y = Spec k ⊔ Spec k = {y₀, y₁}`, `Z = ℙ¹`, and `m : X ×_S Y ⟶ Z` equal to a constant on
`X × {y₀}` and to the identity on `X × {y₁}`.  Every hypothesis holds — `X` is proper with
`H⁰(X, 𝒪) = k`, `Z` is separated, `m` contracts the slice over `y₀` — and `m` does not
factor through `Y`.  What fails is that the locus of `y` whose slice is contracted is open
and closed but not everything.

So `exists_comp_snd_eq_of_slice_const` carries `[GeometricallyConnected q]`.  That costs
nothing at the point of use: in the abelian-scheme application both factors are the same
abelian scheme `A`, whose `AbelianSchemeStruct.connected` field is exactly this
hypothesis.

## Statement of the pushforward theorem, and why it is stated universally

`HasTrivialPushforward` is not stable under base change on its own — `f_*𝒪_X` need not
commute with base change for a general proper `f`.  It does when `f` is flat with
geometrically connected and geometrically reduced fibres, because then `f_*𝒪_X` is
locally free of rank one with formation commuting with base change (cohomology and base
change, Hartshorne III.12.11 / Grauert), and the unit is an isomorphism fibrewise by
`H⁰(X_s, 𝒪) = κ(s)` for a proper, geometrically connected, geometrically reduced `X_s`.
That is why the theorem below concludes the UNIVERSAL form directly: the universality is
not a strengthening bolted on afterwards, it is what the proof produces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}}

/-! ### The pushforward condition -/

/-- **`𝒪_S ⟶ f_*𝒪_X` is an isomorphism**, written as: `f.app U : Γ(S, U) ⟶ Γ(X, f⁻¹U)` is
an isomorphism for every open `U ⊆ S`.

`f.app U` is by definition the component at `U` of the map of sheaves `𝒪_S ⟶ f_*𝒪_X`
carried by `f`, so this really is the statement `f_*𝒪_X = 𝒪_S` and not a weakening of
it. -/
def HasTrivialPushforward (f : X ⟶ S) : Prop :=
  ∀ U : S.Opens, IsIso (f.app U)

/-- `HasTrivialPushforward` packaged as a `MorphismProperty`, so that `Mathlib`'s
`MorphismProperty.universally` can be applied to it. -/
def hasTrivialPushforwardProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ HasTrivialPushforward f

/-- **`𝒪_S ⟶ f_*𝒪_X` is an isomorphism, and remains one after every base change.**

This is the hypothesis the rigidity lemma needs: its proof base-changes the proper
morphism along an arbitrary test scheme, and `f_*𝒪_X = 𝒪_S` for one `f` says nothing
about the base changes of `f`. -/
def HasUniversallyTrivialPushforward (f : X ⟶ S) : Prop :=
  hasTrivialPushforwardProperty.universally f

theorem HasUniversallyTrivialPushforward.hasTrivialPushforward {f : X ⟶ S}
    (hf : HasUniversallyTrivialPushforward f) : HasTrivialPushforward f :=
  MorphismProperty.universally_le _ f hf

/-! ### The theorem -/

/-- **`Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY
CONNECTED AND REDUCED FIBRES** (sorry node — Hartshorne III.12, Mumford *AV* §5, Stacks
0E6R / 0BUG).  This is `f_*𝒪_X = 𝒪_S` read at global sections, and by
`hasUniversallyTrivialPushforward_of_isProper_of_flat` below it is *equivalent* to the
full sheaf-theoretic, universal statement — the reduction is recorded there.

This is the missing classical input behind the whole Jacobian half of this development:
`isAdditiveOn_of_post_zero` (relative rigidity), `exists_albaneseOfCurve` and
`universal_jacobianBaseChangeAj` all reduce to it, which is why it is stated here, once,
in the shim tree rather than inside a modular-curve file.

**The proof, and what formalizing it costs.**  Let `s ∈ S`.  The fibre `X_s` is proper,
geometrically connected and geometrically reduced over `κ(s)`, so `H⁰(X_s, 𝒪) = κ(s)`:
a global section generates a finite `κ(s)`-subalgebra of `H⁰`, which is a field extension
because `X_s` is reduced and connected, and is trivial because it is geometrically
connected.  Flatness plus properness plus finite presentation then give cohomology and
base change (Grauert / Hartshorne III.12.11): `f_*𝒪_X` is locally free of rank one and its
formation commutes with base change, and the unit `𝒪_S ⟶ f_*𝒪_X` is an isomorphism
because it is one on every fibre.

**PIN STATE, checked rather than assumed (2026-07-27).**  `Mathlib` has no higher direct
images of quasi-coherent sheaves, no `Rⁱf_*`, no semicontinuity, no cohomology-and-base-
change; `grep` for `higherDirectImage`/`directImage` over `Mathlib/AlgebraicGeometry` and
over `~/cs/FLT` returns nothing.  So this leaf is a genuine theory build, and it is the
one whose completion unblocks three separate leaves at once.

**LEAF: `Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM.**  This is the whole content: the two
quantifiers that decorate it — "and after every base change", "and over every open
`U ⊆ S`" — are both discharged by
`hasUniversallyTrivialPushforward_of_isProper_of_flat` below, because *all five*
hypotheses are stable under base change and an open restriction `f ∣_ U` is itself a base
change (`AlgebraicGeometry.isPullback_morphismRestrict`).  So whoever takes this leaf owes
**one global-sections computation and nothing else**; in particular there is no need to
carry the `universally` wrapper or the `∀ U` through the cohomological argument.

**THE ROUTE, restated at this reduced generality.**  `f` is proper, flat and of finite
presentation with geometrically connected and geometrically reduced fibres.  Cohomology
and base change (Grauert; Hartshorne III.12.11, Stacks 0E6R / 0BUG) makes `f_*𝒪_X` locally
free with formation commuting with base change; its fibre at `s` is `H⁰(X_s, 𝒪_{X_s})`,
which is `κ(s)` because `X_s` is proper, geometrically connected and geometrically reduced
over `κ(s)` (a global section generates a finite `κ(s)`-subalgebra of `H⁰`, which is a
field by reducedness and connectedness and is `κ(s)` itself by geometric connectedness).
Hence the unit `𝒪_S ⟶ f_*𝒪_X` is an isomorphism on fibres, so an isomorphism, so an
isomorphism on global sections.

**WHAT IS MISSING, and the check that refutes it**: `grep -rn 'higherDirectImage\|
directImage\|cohomologyAndBaseChange' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/
~/cs/FLT/FLT/ Fermat/` — zero hits at `982e0aea`.  There is no quasi-coherent cohomology
in the pin at all, so this is a theory build and not a missing-lemma hunt. -/
theorem isIso_appTop_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    IsIso f.appTop :=
  sorry

/-- **`f_*𝒪_X = 𝒪_S`, UNIVERSALLY, FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY CONNECTED
AND REDUCED FIBRES** — PROVEN over `isIso_appTop_of_isProper_of_flat`.

Both quantifiers are pure bookkeeping and are discharged here, once:

* *the base change*: `IsProper`, `Flat`, `LocallyOfFinitePresentation`,
  `GeometricallyConnected` and `GeometricallyReduced` all carry
  `MorphismProperty.IsStableUnderBaseChange` instances in `Mathlib`, so every leg of a
  pullback square over `f` inherits all five;
* *the open `U ⊆ S`*: `isPullback_morphismRestrict` exhibits `f ∣_ U` as a base change of
  `f`, so it inherits all five as well, and `morphismRestrict_appTop` together with
  `Scheme.Opens.ι_image_top` identifies `(f ∣_ U).appTop` with `f.app U` up to the
  `eqToHom`-induced isomorphism `X.presheaf.map (eqToHom …).op`.

This is why the remaining leaf may be stated at `⊤` over a *fixed* `f`: no generality is
lost, and a cohomological argument that had to thread `universally` through itself would be
considerably worse. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    HasUniversallyTrivialPushforward f := by
  intro X' S' i₁ i₂ f' hpb
  haveI : IsProper f' := MorphismProperty.of_isPullback hpb.flip ‹IsProper f›
  haveI : Flat f' := MorphismProperty.of_isPullback hpb.flip ‹Flat f›
  haveI : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback hpb.flip ‹LocallyOfFinitePresentation f›
  haveI : GeometricallyConnected f' :=
    MorphismProperty.of_isPullback hpb.flip ‹GeometricallyConnected f›
  haveI : GeometricallyReduced f' :=
    MorphismProperty.of_isPullback hpb.flip ‹GeometricallyReduced f›
  intro U
  haveI : IsProper (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip ‹IsProper f'›
  haveI : Flat (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip ‹Flat f'›
  haveI : LocallyOfFinitePresentation (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹LocallyOfFinitePresentation f'›
  haveI : GeometricallyConnected (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹GeometricallyConnected f'›
  haveI : GeometricallyReduced (f' ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f' U).flip
      ‹GeometricallyReduced f'›
  haveI hiso : IsIso (f'.app (U.ι ''ᵁ ⊤) ≫
      X'.presheaf.map (eqToHom (image_morphismRestrict_preimage f' U ⊤)).op) := by
    rw [← morphismRestrict_appTop]
    exact isIso_appTop_of_isProper_of_flat (f' ∣_ U)
  haveI h2 := (isIso_comp_right_iff _ _).mp hiso
  rwa [U.ι_image_top] at h2

/-- **A SMOOTH MORPHISM HAS GEOMETRICALLY REDUCED FIBRES** (PROVEN — a re-export of
`AlgebraicGeometry.GeometricallyReduced.of_smooth`).

TRUE and standard: smoothness is stable under base change, so every geometric fibre
`X ×_S Spec K` is smooth over the field `K`; a scheme smooth over a field is regular,
and a regular scheme is reduced.

**THIS IS NO LONGER A LEAF OF THIS FILE, AND THE ABSENCE NOTE THAT USED TO SIT HERE IS
STALE** (corrected 2026-07-27).  It said the implication `[Smooth f] → GeometricallyReduced f`
is missing at this pin — which is still true *of `Mathlib`*, and no longer true of this
project: `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` (landed by
`6591aca3`, reached here by the `public import` above) proves

* `AlgebraicGeometry.isReduced_of_smooth_over_field` — a scheme smooth over a field is
  reduced, by an affine cover, and
* `AlgebraicGeometry.GeometricallyReduced.of_smooth` — the base-change packaging,

over the single ring-theoretic leaf `Algebra.Smooth.isReduced_of_isField` (a smooth algebra
over a field is reduced; genuinely open, and genuinely a `Mathlib` gap — the Jacobian
criterion, which needs `IsRegularLocalRing → IsDomain` and a bridge to it, neither of which
exists at this pin).  **The check that refutes this note** — i.e. that would show the
implication is again missing rather than merely relocated — is

    grep -rn 'GeometricallyReduced.of_smooth' Fermat/FLT/Mathlib/AlgebraicGeometry/

Restating it here rather than deleting it costs nothing and keeps
`hasUniversallyTrivialPushforward_of_isProper_of_smooth` below readable at its point of
use; the mathematics is entirely in the sibling file. -/
theorem geometricallyReduced_of_smooth (f : X ⟶ S) [Smooth f] : GeometricallyReduced f :=
  GeometricallyReduced.of_smooth f

/-- **`f_*𝒪_X = 𝒪_S` for a PROPER SMOOTH morphism with geometrically connected fibres**
(PROVEN, over the two leaves above).

This is the form every consumer in this development uses, because both an abelian scheme
(`AbelianSchemeStruct`, whose fields are `proper`, `smooth`, `connected`) and a smooth
proper curve are handed over as smooth rather than as flat with reduced fibres.  The
missing implications `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` are
`Mathlib` instances. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_smooth (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
    HasUniversallyTrivialPushforward f :=
  haveI := geometricallyReduced_of_smooth f
  hasUniversallyTrivialPushforward_of_isProper_of_flat f

/-! ### The rigidity lemma -/

/-- **The slice `X ≅ X ×_S σ(S) ⊆ X ×_S Y` cut out by a section `σ` of `q`.**

`sliceIncl p q σ hσ` is the morphism `x ↦ (x, σ(p x))`.  It is a section of
`pullback.fst p q`, and it is the subscheme along which the rigidity lemma's hypothesis is
stated. -/
noncomputable def sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : X ⟶ pullback p q :=
  pullback.lift (𝟙 X) (p ≫ σ)
    (by rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

@[reassoc (attr := simp)]
theorem sliceIncl_fst {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : sliceIncl p q σ hσ ≫ pullback.fst p q = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceIncl_snd {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : sliceIncl p q σ hσ ≫ pullback.snd p q = p ≫ σ :=
  pullback.lift_snd _ _ _

/-- **THE RIGIDITY LEMMA** (sorry node — Mumford *Abelian Varieties* §4; BLR *Néron
Models* 8.4 in the relative case; Mumford *GIT* Prop. 6.1 over a general base).

Let `p : X ⟶ S` be proper with `𝒪_S = p_*𝒪_X` universally, let `q : Y ⟶ S` have
geometrically connected fibres, and let `r : Z ⟶ S` be separated.  An `S`-morphism
`m : X ×_S Y ⟶ Z` that is CONSTANT along one slice `X ×_S σ(S)` — that is, whose
restriction along `sliceIncl` factors through `p` — factors through the projection to `Y`.

**The proof.**  Fix `s ∈ S` and an affine open `U ⊆ Z` containing the image of the
contracted slice.  `m⁻¹(Z ∖ U)` is closed in `X ×_S Y`, and `pullback.fst p q` is proper
(base change of `p`), so its image in `Y` is closed and misses `σ(S)`; on the open
complement `V` the whole slice `X ×_S V` maps into the affine `U`, and a morphism from a
proper scheme with `p_*𝒪 = 𝒪` to an affine scheme over the base factors through the base
— this is where the pushforward hypothesis is consumed, and it is consumed after a base
change to `V`, which is why the hypothesis is the UNIVERSAL one.  So `m` factors through
`Y` over `V`.  The locus where `m` factors is then open and closed, and
`GeometricallyConnected q` makes it everything.

**WHY `[GeometricallyConnected q]` IS NOT DECORATION**: see the FAITHFULNESS NOTE in the
module docstring — with `Y = {y₀, y₁}` two points the statement is false.

**THE CHECK THAT WOULD REFUTE ANY "THIS IS IRREDUCIBLE" VERDICT** on this leaf: land
`hasUniversallyTrivialPushforward_of_isProper_of_flat`, and add the corollary "an
`S`-morphism from `X` to a scheme affine over `S` factors uniquely through `S`" (that
corollary is short — it is the `Γ ⊣ Spec` adjunction plus `IsIso (f.app ⊤)`).  With those
two in hand this leaf is the topological argument above and nothing more. -/
theorem exists_comp_snd_eq_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d :=
  sorry

/-- **A morphism `A ×_S A ⟶ B` vanishing on BOTH AXES vanishes** (PROVEN, over the
rigidity lemma).

This is Mumford *AV* §4 Cor. 1 in the form in which rigidity is actually applied: `e` is
the zero section of `A`, `z` is the zero section of `B`, and the two hypotheses say that
`m` restricted to `A × {0}` and to `{0} × A` is the composite `A ⟶ S ⟶ B`.  The
conclusion is that `m` itself is that composite.

Feeding it `m = u(x + y) − u(x) − u(y)` for an `S`-morphism `u : A ⟶ B` carrying the
origin to the origin is what turns `u` into a homomorphism. -/
theorem eq_comp_of_rigidity_axes {A B S : Scheme.{u}} {af : A ⟶ S} {bf : B ⟶ S}
    [IsProper af] [GeometricallyConnected af] [IsSeparated bf]
    (hpush : HasUniversallyTrivialPushforward af)
    (e : S ⟶ A) (he : e ≫ af = 𝟙 S) (z : S ⟶ B)
    {m : pullback af af ⟶ B} (hm : m ≫ bf = pullback.fst af af ≫ af)
    (h₁ : sliceIncl af af e he ≫ m = af ≫ z)
    (h₂ : pullback.lift (af ≫ e) (𝟙 A)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ m = af ≫ z) :
    m = pullback.fst af af ≫ af ≫ z := by
  obtain ⟨d, hd⟩ := exists_comp_snd_eq_of_slice_const hpush e he hm z h₁
  have hdz : d = af ≫ z := by
    rw [← h₂, hd, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  rw [hd, hdz, ← Category.assoc, ← pullback.condition, Category.assoc]

end AlgebraicGeometry
