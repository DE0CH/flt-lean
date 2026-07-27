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
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
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
* `hasUniversallyTrivialPushforward_of_isProper_of_smooth` — PROVEN from the leaf above
  together with `AlgebraicGeometry.GeometricallyReduced.of_smooth`.  This is the form
  every consumer in this development actually applies, because an abelian scheme and a
  smooth proper curve are both given as *smooth* rather than as *flat with reduced
  fibres*.
* `HasTrivialPushforward.existsUnique_comp_eq` and
  `existsUnique_comp_eq_of_hasTrivialPushforward` — **PROVEN** (two independently
  developed forms of one statement, merged from two branches): an `S`-morphism from `X`
  to an AFFINE scheme factors uniquely through `S`.  This is the corollary of
  `p_*𝒪_X = 𝒪_S` that the rigidity lemma consumes, and it is pure `Γ ⊣ Spec` formalism.
* `existsUnique_comp_snd_eq_of_spec` and `exists_comp_snd_eq_of_isAffine` — **PROVEN**:
  the rigidity lemma for an AFFINE target, where it needs neither the contracted slice
  nor connectedness of `q`.
* `exists_comp_snd_eq_of_isAffine_pullback` — PROVEN: **rigidity with a target AFFINE OVER
  THE BASE**, i.e. whenever `Y ×_S Z` is affine (in particular for `[IsAffine Y]`
  `[IsAffineHom r]`).  This is the form the classical proof consumes.
* `surjective_of_hasUniversallyTrivialPushforward`, `eq_of_comp_eq_of_hasTrivialPushforward`
  and `eq_of_comp_snd_eq` — **PROVEN**: `𝒪_S = p_*𝒪_X` universally makes `p` SURJECTIVE
  (base change along `Spec κ(s) ⟶ S`; an empty fibre would give `κ(s) ≅ Γ(∅, ⊤) = 0`), and
  surjectivity upgrades the affine-target injectivity to an arbitrary target, so
  `pullback.snd p q` is an EPIMORPHISM.  This is the uniqueness the gluing step runs on.
* `isPullback_sliceOverOpen` — **PROVEN**: `X ×_S V` is the part of `X ×_S Y` over `V`, i.e.
  `sliceOverOpen` sits in a cartesian square over `V.ι`; in particular it is an open
  immersion.
* `exists_comp_snd_eq_of_slice_const` — the RIGIDITY LEMMA (Mumford *AV* §4;
  BLR *Néron Models* 8.4 in the relative case), PROVEN over the single leaf below.
* `exists_comp_snd_eq_of_open_cover` — **PROVEN**: local factorizations through the
  projection, over an open cover of `Y`, glue to a global one.  Overlaps agree by
  `eq_of_comp_snd_eq`; the assembly is `Scheme.Cover.glueMorphisms` on
  `Y.openCoverOfIsOpenCover`, checked against the pullback of that cover along
  `pullback.snd p q` via `isPullback_sliceOverOpen`.
* `exists_isAffineOver_cover_of_slice_const` — **PROVEN** from the pointwise form below, by
  indexing the cover by the points of `Y`.
* `exists_isAffineOver_nbhd_of_slice_const` — **PROVEN** from the leaf below by
  `IsOpenImmersion.lift`: at each point `y : Y` there is an open `V ∋ y` over which `m`
  factors through a scheme affine over the base.
* `exists_isAffineOpen_slice_nbhd_of_slice_const` — **THE ONE REMAINING LEAF of the
  rigidity lemma**, and it is now a bare statement about OPENS: at each `y : Y` there are
  an open `V ∋ y` in `Y` and an open `U ⊆ Z` with `V ×_S U` affine and
  `range (X ×_S V ⟶ Z) ⊆ U`.  This is where properness of `pullback.snd`, the section `σ`
  and `[GeometricallyConnected q]` are consumed, and it is the *whole* of what is missing
  — every morphism, index-set, gluing and uniqueness obligation around it has been
  discharged.

## `geometricallyReduced_of_smooth` WAS A DUPLICATE LEAF, and has been deleted (2026-07-27)

This file used to carry its own sorried `geometricallyReduced_of_smooth`, described as
"small and separate".  Both halves of that description were wrong, and the leaf was
redundant:

* it is **not small** — mathlib's `IsRegularLocalRing` API is two files with no
  `IsRegularLocalRing → IsDomain` and no link to smoothness at all, so the classical
  "smooth ⟹ regular ⟹ reduced" route has *both* implications missing at this pin;
* it was **already decomposed elsewhere in this project**, in
  `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`, where
  `GeometricallyReduced.of_smooth` is PROVEN over the ring-theoretic leaf
  `Algebra.Smooth.isReduced_of_isField` — which is where the content actually lives, and
  which carries a full absence audit.

So this file now imports that one and consumes `GeometricallyReduced.of_smooth`.  Anyone
tempted to restate a smoothness-to-reducedness fact here should grep
`isReduced_of_smooth_over_field` first.
* `eq_comp_of_rigidity_axes` — PROVEN from the rigidity lemma: a morphism
  `A ×_S A ⟶ B` vanishing on both axes vanishes.  This is the form in which rigidity is
  used to prove that a pointed morphism of abelian schemes is a homomorphism.

## The cut of the rigidity lemma, and why it is where it is (2026-07-27)

The affine-target case is **not** a special case that has to wait for the topology: it is
complete, and it consumes the ENTIRE pushforward hypothesis.  What the section `σ`, the
properness of the projection and the connectedness of the fibres of `q` are actually for is
the single statement *"`m` maps each `q`-fibre into a piece of `Z` that is affine over the
base"* — the topological argument runs there and nowhere else.  So the leaf splits into

1. **the covering** (`exists_isAffineOver_cover_of_slice_const`) — genuinely the classical
   argument: `pullback.snd p q` is proper (base change of `p`), so the image of
   `m ⁻¹(Z ∖ U)` is closed in `Y` and misses `σ(S)`; the resulting open `V` is where the
   affine case applies, and `GeometricallyConnected q` is what makes the `V`s cover `Y`
   rather than a proper clopen part of it (see the FAITHFULNESS NOTE — with `Y` two points
   they do not);
2. **the gluing** (`exists_comp_snd_eq_of_open_cover`) — bookkeeping, but not free: the local
   factorizations agree on overlaps because `HasUniversallyTrivialPushforward p` makes the
   factorization through the projection UNIQUE (`exists_comp_snd_eq_of_isAffine` is stated as
   an `∃!` for exactly this reason).

**UPDATE (2026-07-27): (2) IS CLOSED, AND (1) HAS BEEN LOCALISED TO A POINT.**  The gluing
is proven, and what it cost is recorded because it is the reusable part: the uniqueness it
needs is the statement that `pullback.snd p q` is an EPIMORPHISM OF SCHEMES, which does NOT
follow from `HasTrivialPushforward` alone (Hartogs: `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ 0}` for a
non-surjective `j`).  It follows from the UNIVERSAL form, which forces `p` to be surjective
by base change along `Spec κ(s) ⟶ S` — an empty fibre would make the field `κ(s)` a zero
ring.  Surjectivity then upgrades `eq_of_comp_eq_of_isAffine` to an arbitrary target
because it makes two candidate factorizations agree on points, hence have the same
preimage of each affine open of `Z`.  So the `∃!` in the affine case is not merely
convenient — the general uniqueness is a theorem with real content, and it is now
`eq_of_comp_snd_eq`.

(1) has in turn been peeled twice.  First to `exists_isAffineOver_nbhd_of_slice_const` —
the same statement at ONE point of `Y` — plus a proven assembly that indexes the cover by
the points of `Y`; then to `exists_isAffineOpen_slice_nbhd_of_slice_const`, which drops the
morphism data entirely and asks only for two OPENS (`V ∋ y` in `Y` and `U` in `Z`) with
`V ×_S U` affine and `m(X ×_S V) ⊆ U`, the factorizing morphism being recovered by
`IsOpenImmersion.lift`.  The remaining leaf therefore carries exactly the geometry
(properness ⟹ closed map; the `GeometricallyConnected` clopen argument) and none of the
bookkeeping.

The leaves are stated with `sliceOverOpen p q V : X ×_S V ⟶ X ×_S Y`, the canonical map
induced by an open `V ⊆ Y`.

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

/-! ### Morphisms to an affine target factor through the base

The `Γ ⊣ Spec` half of the rigidity argument.  Nothing here needs properness, flatness or
any hypothesis on the fibres: `IsIso (p.app ⊤)` alone already makes
`(p ≫ ·) : (S ⟶ Z) → (X ⟶ Z)` a bijection for every affine `Z`, because both sides are
`Hom` out of a global-sections ring and `p.app ⊤` is the comparison between them. -/

/-- **`(p ≫ ·)` is injective on morphisms into an affine scheme**, as soon as
`p.app ⊤ : Γ(S, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism.

A morphism into an affine scheme is determined by its action on global sections
(`ext_of_isAffine`), and `(p ≫ c).app ⊤ = c.app ⊤ ≫ p.app ⊤`, so the claim is exactly that
`p.app ⊤` is a monomorphism. -/
theorem eq_of_comp_eq_of_isAffine {X S Z : Scheme.{u}} {p : X ⟶ S} [IsIso p.appTop]
    [IsAffine Z] {c₁ c₂ : S ⟶ Z} (h : p ≫ c₁ = p ≫ c₂) : c₁ = c₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  exact (cancel_mono p.appTop).mp h'

/-- **AN `S`-MORPHISM FROM `X` TO AN AFFINE SCHEME FACTORS UNIQUELY THROUGH `S`** — the
corollary of `p_*𝒪_X = 𝒪_S` that the rigidity lemma runs on.

The factorization is written down explicitly rather than extracted from an abstract
adjunction argument: the ring map is `φ = m.app ⊤ ≫ (p.app ⊤)⁻¹ : Γ(Z, ⊤) ⟶ Γ(S, ⊤)`, and
the morphism is `S ⟶ Spec Γ(S, ⊤) ⟶ Spec Γ(Z, ⊤) ≅ Z`.  The verification is then
`Scheme.toSpecΓ_naturality` twice, once in each direction, with `Spec.map_comp` in between.

Only `HasTrivialPushforward` at the single open `⊤` is used.  Note that the corresponding
statement for a target merely *affine over `S`* is `exists_comp_snd_eq_of_isAffine_pullback`
below, which is obtained from this one by a base change rather than by a relative `Spec`
(`Mathlib` has no relative `Spec` at this pin). -/
theorem HasTrivialPushforward.existsUnique_comp_eq {X S Z : Scheme.{u}} {p : X ⟶ S}
    (hp : HasTrivialPushforward p) [IsAffine Z] (m : X ⟶ Z) :
    ∃! c : S ⟶ Z, p ≫ c = m := by
  haveI : IsIso p.appTop := hp ⊤
  have key : p ≫ (S.toSpecΓ ≫ Spec.map (m.appTop ≫ inv p.appTop) ≫ Z.isoSpec.inv) = m := by
    rw [← Category.assoc, Scheme.toSpecΓ_naturality]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  exact ⟨_, key, fun c hc => eq_of_comp_eq_of_isAffine (p := p) (by rw [hc, key])⟩

/-! ### `𝒪_S = p_*𝒪_X` makes `p` an EPIMORPHISM

This is what makes the factorization through the base *unique* for an arbitrary — not
necessarily affine — target, and it is exactly what the gluing step of the rigidity lemma
needs: two local factorizations over `V i` and `V j` agree on the overlap because there is
at most one.

Two ingredients, and both are consequences of the pushforward hypothesis alone:

* `surjective_of_hasUniversallyTrivialPushforward` — the UNIVERSAL form forces `p` to be
  surjective, by base change along `Spec κ(s) ⟶ S`: an empty fibre would give
  `κ(s) ≅ Γ(∅, ⊤) = 0`, and `κ(s)` is a field.  This is the only place the *universal*
  form is used for anything other than an honest base change, and it is why
  `HasTrivialPushforward` alone will not do: `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ 0}` by Hartogs, and
  that `j` is not surjective.
* `eq_of_comp_eq_of_hasTrivialPushforward` — surjectivity plus `IsIso (p.app U)` at every
  open `U` upgrades the affine-target injectivity `eq_of_comp_eq_of_isAffine` to an
  arbitrary target, by covering `Z` with affine opens: surjectivity makes the two
  candidate morphisms agree on POINTS, hence have the same preimage of each affine open,
  and on that preimage the affine case applies to `p ∣_ (c₁ ⁻¹ᵁ U)`. -/

/-- Global sections of an empty scheme form the zero ring — `⊤ = ⊥` there, and
`Subsingleton Γ(X, ⊥)` is a `Mathlib` instance (the sheaf condition over the empty
cover). -/
theorem subsingleton_globalSections_of_isEmpty (W : Scheme.{u}) [IsEmpty W] :
    Subsingleton Γ(W, ⊤) := by
  have h : (⊤ : W.Opens) = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  rw [h]
  infer_instance

/-- **`𝒪_S = p_*𝒪_X` UNIVERSALLY FORCES `p` TO BE SURJECTIVE** (PROVEN).

Base-change `p` along `S.fromSpecResidueField s : Spec κ(s) ⟶ S`, whose range is `{s}`.
If `s` were not in the range of `p` the two ranges would be disjoint, so the fibre
product would be EMPTY (`Scheme.isEmpty_pullback_iff`) and its ring of global sections
would be the zero ring; but the hypothesis makes `(pullback.snd p _).app ⊤` an
isomorphism onto it from `Γ(Spec κ(s), ⊤) ≅ κ(s)`, forcing the field `κ(s)` to be
subsingleton.

Note this genuinely needs the UNIVERSAL form: `HasTrivialPushforward` alone does not
imply surjectivity — Hartogs gives `𝒪_{𝔸²} ≅ j_*𝒪_{𝔸² ∖ {0}}` for the inclusion `j` of
the complement of a codimension-two point. -/
theorem surjective_of_hasUniversallyTrivialPushforward {p : X ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) : Surjective p := by
  constructor
  intro s
  by_contra hs
  have h : HasTrivialPushforward (pullback.snd p (S.fromSpecResidueField s)) :=
    hpush (pullback.fst p _) _ (pullback.snd p _)
      (IsPullback.of_hasPullback p (S.fromSpecResidueField s)).flip
  haveI : IsEmpty ↥(pullback p (S.fromSpecResidueField s)) := by
    rw [Scheme.isEmpty_pullback_iff, Scheme.range_fromSpecResidueField]
    simpa [Set.disjoint_singleton_right] using hs
  haveI := h ⊤
  haveI : Subsingleton Γ(pullback p (S.fromSpecResidueField s), ⊤) :=
    subsingleton_globalSections_of_isEmpty _
  haveI : Subsingleton Γ(Spec (S.residueField s), ⊤) :=
    (asIso ((pullback.snd p (S.fromSpecResidueField s)).app
      ⊤)).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr inferInstance
  haveI : Subsingleton (S.residueField s) :=
    (Scheme.ΓSpecIso (CommRingCat.of (S.residueField s))).commRingCatIsoToRingEquiv.toEquiv
      |>.subsingleton_congr.mp inferInstance
  exact false_of_nontrivial_of_subsingleton (S.residueField s)

/-- `IsIso (g.app V)` for every open transfers to the RESTRICTED morphism `g ∣_ V`, whose
`appTop` is `g.app (V.ι ''ᵁ ⊤)` composed with an `eqToHom`-induced isomorphism.

Stated in this direction — the composite form first, then `rw [← morphismRestrict_appTop]`
— on purpose: rewriting FORWARDS with `morphismRestrict_appTop` produces a goal that is
not type-correct at `instances` transparency, so instance synthesis then fails on the
`eqToHom` factor even when every ingredient is available. -/
theorem HasTrivialPushforward.isIso_appTop_morphismRestrict {g : X ⟶ S}
    (hg : HasTrivialPushforward g) (V : S.Opens) : IsIso (g ∣_ V).appTop := by
  have h2 : IsIso (g.app (V.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage g V ⊤)).op) := by
    haveI := hg (V.ι ''ᵁ ⊤)
    infer_instance
  rwa [← morphismRestrict_appTop] at h2

/-- **A SURJECTIVE MORPHISM WITH `𝒪_S = g_*𝒪_X` IS AN EPIMORPHISM OF SCHEMES** (PROVEN),
i.e. `(g ≫ ·)` is injective on morphisms into an ARBITRARY scheme `Z`.

`eq_of_comp_eq_of_isAffine` is this statement for affine `Z`; the passage to a general
`Z` is local on `Z` and uses surjectivity twice:

* surjectivity makes `c₁` and `c₂` agree on POINTS, so `c₁ ⁻¹ᵁ U = c₂ ⁻¹ᵁ U` for every
  open `U ⊆ Z` — without which the two restrictions would not even have a common source;
* on `V := c₁ ⁻¹ᵁ U` with `U` an affine open around `c₁ s`, the affine case applies to
  `g ∣_ V`, whose `appTop` is an isomorphism by
  `HasTrivialPushforward.isIso_appTop_morphismRestrict`.

`Scheme.hom_ext_of_forall` then assembles the local equalities. -/
theorem eq_of_comp_eq_of_hasTrivialPushforward {g : X ⟶ S} (hg : HasTrivialPushforward g)
    [Surjective g] {c₁ c₂ : S ⟶ Z} (h : g ≫ c₁ = g ≫ c₂) : c₁ = c₂ := by
  have hbase : ∀ s : S, c₁.base s = c₂.base s := by
    intro s
    obtain ⟨x, rfl⟩ := g.surjective s
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
  have hpre : ∀ U : Z.Opens, c₁ ⁻¹ᵁ U = c₂ ⁻¹ᵁ U := by
    intro U
    ext s
    simp [hbase s]
  refine Scheme.hom_ext_of_forall c₁ c₂ fun s => ?_
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Z) (x := c₁.base s) (U := ⊤) (by trivial)
  haveI : IsAffine U.toScheme := hU
  refine ⟨c₁ ⁻¹ᵁ U, hmem, ?_⟩
  have e₂ : (c₁ ⁻¹ᵁ U) ≤ c₂ ⁻¹ᵁ U := (hpre U) ▸ le_rfl
  haveI : IsIso (g.resLE (c₁ ⁻¹ᵁ U) (g ⁻¹ᵁ (c₁ ⁻¹ᵁ U)) le_rfl).appTop := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hg.isIso_appTop_morphismRestrict _
  have key : c₁.resLE U (c₁ ⁻¹ᵁ U) le_rfl = c₂.resLE U (c₁ ⁻¹ᵁ U) e₂ := by
    refine eq_of_comp_eq_of_isAffine
      (p := g.resLE (c₁ ⁻¹ᵁ U) (g ⁻¹ᵁ (c₁ ⁻¹ᵁ U)) le_rfl) ?_
    rw [Scheme.Hom.resLE_comp_resLE, Scheme.Hom.resLE_comp_resLE]
    congr 1
  have := congrArg (fun t => t ≫ U.ι) key
  simpa only [Scheme.Hom.resLE_comp_ι] using this

/-- **THE PROJECTION `X ×_S Y ⟶ Y` IS AN EPIMORPHISM** (PROVEN) when
`HasUniversallyTrivialPushforward p`.

`HasUniversallyTrivialPushforward` is stable under base change, so it passes from `p` to
`pullback.snd p q`, which is then surjective and has trivial pushforward — the two
hypotheses of `eq_of_comp_eq_of_hasTrivialPushforward`.

This is the uniqueness that `exists_comp_snd_eq_of_isAffine` records as an `∃!` in the
affine case, now available for an arbitrary target; it is what makes the local
factorizations of the rigidity lemma agree on overlaps. -/
theorem eq_of_comp_snd_eq {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {c₁ c₂ : Y ⟶ Z}
    (h : pullback.snd p q ≫ c₁ = pullback.snd p q ≫ c₂) : c₁ = c₂ := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  exact eq_of_comp_eq_of_hasTrivialPushforward hu.hasTrivialPushforward h

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

/-- **`f_*𝒪_X = 𝒪_S` for a PROPER SMOOTH morphism with geometrically connected fibres**
(PROVEN, over the single leaf above).

This is the form every consumer in this development uses, because both an abelian scheme
(`AbelianSchemeStruct`, whose fields are `proper`, `smooth`, `connected`) and a smooth
proper curve are handed over as smooth rather than as flat with reduced fibres.  The
missing implications `Smooth → Flat` and `Smooth → LocallyOfFinitePresentation` are
`Mathlib` instances, and geometric reducedness comes from
`AlgebraicGeometry.GeometricallyReduced.of_smooth` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` — see the module
docstring for why this file no longer states that fact itself. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_smooth (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
    HasUniversallyTrivialPushforward f :=
  haveI := GeometricallyReduced.of_smooth f
  hasUniversallyTrivialPushforward_of_isProper_of_flat f

/-! ### The corollary the rigidity lemma consumes: factoring an affine-valued morphism -/

/-- **AN AFFINE-VALUED MORPHISM OUT OF `X` FACTORS UNIQUELY THROUGH `S`** (PROVEN).

If `𝒪_S ⟶ p_*𝒪_X` is an isomorphism then for every ring `R` the map
`(S ⟶ Spec R) → (X ⟶ Spec R)`, `c ↦ p ≫ c`, is a bijection.

This is the promised short corollary of `p_*𝒪_X = 𝒪_S`, and it is pure `Γ ⊣ Spec`
formalism with no geometry in it: under `ΓSpec.adjunction` the map `c ↦ p ≫ c` is
conjugate to `g ↦ Scheme.Γ.rightOp.map p ≫ g` on hom-sets, and `Scheme.Γ.rightOp.map p`
is `(p.appTop).op`, an isomorphism precisely because `HasTrivialPushforward p` says
`p.app ⊤` is one.  No properness, flatness or connectedness is used — the *only* input is
the pushforward hypothesis, which is why every geometric difficulty in the rigidity lemma
sits in reducing to an affine target rather than in this step.

Note it needs only `HasTrivialPushforward`, not the universal form; the universal form is
what lets the CALLER apply it after a base change. -/
theorem existsUnique_comp_eq_of_hasTrivialPushforward {p : X ⟶ S}
    (hp : HasTrivialPushforward p) {R : CommRingCat.{u}} (m : X ⟶ Spec R) :
    ∃! c : S ⟶ Spec R, m = p ≫ c := by
  haveI : IsIso p.appTop := hp ⊤
  haveI : IsIso (Scheme.Γ.rightOp.map p) := by
    show IsIso ((p.appTop).op)
    infer_instance
  set eX := ΓSpec.adjunction.homEquiv X (Opposite.op R) with heX
  set eS := ΓSpec.adjunction.homEquiv S (Opposite.op R) with heS
  have hfun : (fun c : S ⟶ Spec R => p ≫ c)
      = fun c => eX (Scheme.Γ.rightOp.map p ≫ eS.symm c) := by
    funext c
    rw [heX, heS, ΓSpec.adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    rfl
  have hcomp : Function.Bijective
      (fun g : Scheme.Γ.rightOp.obj S ⟶ Opposite.op R => Scheme.Γ.rightOp.map p ≫ g) := by
    constructor
    · intro a b hab
      simpa using congrArg (fun t => inv (Scheme.Γ.rightOp.map p) ≫ t) hab
    · intro b
      exact ⟨inv (Scheme.Γ.rightOp.map p) ≫ b, by simp⟩
  have hbij : Function.Bijective (fun c : S ⟶ Spec R => p ≫ c) := by
    rw [hfun]
    exact eX.bijective.comp (hcomp.comp eS.symm.bijective)
  obtain ⟨c, hc⟩ := hbij.surjective m
  exact ⟨c, hc.symm, fun y hy => hbij.injective (by simpa using hy.symm.trans hc.symm)⟩

/-- **THE RIGIDITY LEMMA FOR AN AFFINE TARGET** (PROVEN).

With `Z = Spec R` the rigidity lemma needs **none** of its geometric hypotheses: no
contracted slice `σ`, no `GeometricallyConnected q`, no separatedness of `r`, not even
properness of `p`.  The factorization is immediate from
`existsUnique_comp_eq_of_hasTrivialPushforward` applied to `pullback.snd p q`, which is a
base change of `p` and therefore inherits `HasUniversallyTrivialPushforward` — this is
exactly what the universal form of the hypothesis is for.  The factorization is moreover
UNIQUE, which the general statement does not record.

**This delimits the general leaf precisely.**  The whole content of
`exists_comp_snd_eq_of_slice_const` is the reduction to an affine target, and that
reduction is genuinely necessary: with `S = Spec k`, `X = Spec k`, `Y = Z = ℙ¹` and
`m = 𝟙` every hypothesis of the general statement holds, `d = 𝟙` is the factorization,
and `m` factors through no affine scheme at all.  So no globally-affine reduction can
exist and the passage must be LOCAL on `Y` — which is what drags in properness (a closed
image in `Y`), the contracted slice (a nonempty open where the image is affine) and
connectedness of `q` (to spread that open over all of `Y`). -/
theorem existsUnique_comp_snd_eq_of_spec {Y : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {R : CommRingCat.{u}}
    (m : pullback p q ⟶ Spec R) :
    ∃! d : Y ⟶ Spec R, m = pullback.snd p q ≫ d := by
  have h : hasTrivialPushforwardProperty.universally (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  exact existsUnique_comp_eq_of_hasTrivialPushforward
    (HasUniversallyTrivialPushforward.hasTrivialPushforward h) m

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

/-- **RIGIDITY WITH AN AFFINE TARGET** (PROVEN).

`HasUniversallyTrivialPushforward p` base-changes along `q` to `HasTrivialPushforward` for
the projection `pullback.snd p q : X ×_S Y ⟶ Y`, and then
`HasTrivialPushforward.existsUnique_comp_eq` factors `m` through `Y` — uniquely.

**No section, no connectedness, no separatedness.**  None of `σ`, `hconst`,
`[GeometricallyConnected q]` or `[IsSeparated r]` appears: for an affine target the whole
statement is the pushforward hypothesis and nothing else.  That is what localises the
remaining content of the rigidity lemma onto the covering step.

The uniqueness is load-bearing downstream: it is what makes local factorizations over an
open cover of `Y` agree on overlaps (`exists_comp_snd_eq_of_open_cover`). -/
theorem exists_comp_snd_eq_of_isAffine {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) [IsAffine Z] (m : pullback p q ⟶ Z) :
    ∃! d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  have h : HasTrivialPushforward (pullback.snd p q) :=
    hpush (pullback.fst p q) q (pullback.snd p q) (IsPullback.of_hasPullback p q).flip
  obtain ⟨d, hd, hu⟩ := h.existsUnique_comp_eq m
  exact ⟨d, hd.symm, fun d' hd' => hu d' hd'.symm⟩

/-- **RIGIDITY WITH A TARGET AFFINE OVER THE BASE** (PROVEN) — the relative form of the
`Γ ⊣ Spec` corollary, obtained by a base change instead of by a relative `Spec`.

`Mathlib` has no relative `Spec` at this pin, so "affine over `S`" cannot be turned into a
sheaf of algebras and split off directly.  It does not need to be: an `S`-morphism
`m : X ×_S Y ⟶ Z` is the same thing as a `Y`-morphism `X ×_S Y ⟶ Y ×_S Z`, and *that*
target is an honest affine scheme as soon as `Y ×_S Z` is one — which is exactly what
"`Z` is affine over `S`" gives over an affine `Y`.  So the hypothesis is stated as
`[IsAffine (pullback q r)]`, which is what the proof needs and is implied by
`[IsAffine Y] [IsAffineHom r]`.

This is the form the classical proof consumes, and it is consumed by
`exists_comp_snd_eq_of_slice_const` below. -/
theorem exists_comp_snd_eq_of_isAffine_pullback {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p) [IsAffine (pullback q r)]
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  have hcomm : pullback.snd p q ≫ q = m ≫ r := by rw [hm, ← pullback.condition]
  obtain ⟨e, he⟩ :=
    (exists_comp_snd_eq_of_isAffine (q := q) hpush (pullback.lift _ _ hcomm)).exists
  refine ⟨e ≫ pullback.snd q r, ?_⟩
  rw [← Category.assoc, ← he, pullback.lift_snd]

/-- **The canonical map `X ×_S V ⟶ X ×_S Y` induced by an open subscheme `V ⊆ Y`.**

This is how "the restriction of `m` to the part of `X ×_S Y` lying over `V`" is written in
the two leaves below, without ever forming an open subscheme of `X ×_S Y`. -/
noncomputable def sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    pullback p (V.ι ≫ q) ⟶ pullback p q :=
  pullback.map p (V.ι ≫ q) p q (𝟙 X) V.ι (𝟙 S) (by simp) (by simp)

/-- **`X ×_S V` IS THE PART OF `X ×_S Y` LYING OVER `V`** (PROVEN): the square

```
X ×_S V --sliceOverOpen--> X ×_S Y
   | snd                      | snd
   V --------- ι ---------->  Y
```

is cartesian.  Pasting: the outer rectangle obtained by adjoining `pullback.fst p q` and
`q` on the right is `pullback p (V.ι ≫ q)`, and the right-hand square is `X ×_S Y`, so
`IsPullback.of_bot` gives the left one.

Two consequences are used below: `sliceOverOpen` is an open immersion (base change of
`V.ι`), and `X ×_S V` is *the* fibre product `(X ×_S Y) ×_Y V`, which is how the
`sliceOverOpen`s are recognised as members of the pullback of an open cover of `Y`. -/
theorem isPullback_sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    IsPullback (sliceOverOpen p q V) (pullback.snd p (V.ι ≫ q)) (pullback.snd p q) V.ι := by
  refine (IsPullback.of_bot (h₁₁ := pullback.snd p (V.ι ≫ q)) (v₁₁ := sliceOverOpen p q V)
    (v₁₂ := V.ι) (h₂₁ := pullback.snd p q) (v₂₁ := pullback.fst p q) (v₂₂ := q) ?_ ?_
    (IsPullback.of_hasPullback p q).flip).flip
  · have e : sliceOverOpen p q V ≫ pullback.fst p q = pullback.fst p (V.ι ≫ q) := by
      simp [sliceOverOpen, pullback.map, pullback.lift_fst]
    rw [e]
    exact (IsPullback.of_hasPullback p (V.ι ≫ q)).flip
  · simp [sliceOverOpen, pullback.map, pullback.lift_snd]

instance {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    IsOpenImmersion (sliceOverOpen p q V) :=
  MorphismProperty.of_isPullback (isPullback_sliceOverOpen p q V).flip inferInstance

/-- **THE ONE REMAINING LEAF OF THE RIGIDITY LEMMA** (sorry node) — the whole topological
content, and the ONLY place where `σ`, `hconst` and `[GeometricallyConnected q]` are used.

Everything else is discharged: `exists_isAffineOver_nbhd_of_slice_const` below turns this
into the morphism-level factorization (by `IsOpenImmersion.lift`, since the containment
below is exactly the hypothesis that lift needs),
`exists_isAffineOver_cover_of_slice_const` turns THAT into an open cover (by indexing on
the points of `Y`), and `exists_comp_snd_eq_of_open_cover` glues.  So what is left here is
a bare statement about opens and set-theoretic images — no morphism plumbing, no index
set, no uniqueness.

**What has to be produced at `y`.**  An open `V ∋ y` in `Y` and an open `U ⊆ Z` such that

* `m` maps the whole of `X ×_S V` into `U` — written as the containment of set-theoretic
  ranges, which is precisely `IsOpenImmersion.lift`'s hypothesis; and
* `V ×_S U` is an AFFINE SCHEME — "`U` is affine over the base, over `V`".  In the
  intended construction `V` and `U` are affine opens lying over one affine open
  `S₀ ⊆ S`, so `V ×_S U = V ×_{S₀} U` is a fibre product of affines over an affine.

**The proof** (Mumford *AV* §4; BLR 8.4), in two halves.

1. *The properness half, which is local and needs no connectedness.*  Suppose the whole
   slice of `X ×_S Y` over `y` is mapped by `m` into an affine open `U ⊆ Z` with
   `r(U) ⊆ S₀` for an affine open `S₀ ∋ q y`.  Then `m ⁻¹(Z ∖ U)` is closed in `X ×_S Y`,
   and `pullback.snd p q` is proper (base change of `p`), hence a CLOSED MAP, so its image
   is closed in `Y` and misses `y`.  The complement is an open `V ∋ y` over which `m`
   lands in `U`; shrink `V` to an affine open inside `q ⁻¹ᵁ S₀` and take `W = U`, so
   `V ×_S W = V ×_{S₀} U` is a fibre product of affines over an affine, hence affine.

2. *The connectedness half, which is the actual content.*  The hypothesis of (1) — that
   the slice over `y` lands in a single affine — is what has to be established at EVERY
   `y`, and it is here that `σ`, `hconst` and `[GeometricallyConnected q]` enter.  At
   `y = σ(s)` it is immediate from `hconst`, which puts that slice at the single point
   `c(s)`.  Step (1) then propagates it to an open neighbourhood, so the locus where it
   holds is OPEN; running (1) at every point of that locus shows it is also closed in each
   fibre of `q`, and `[GeometricallyConnected q]` upgrades "clopen in each fibre and meets
   each fibre (via `σ`)" to "everything".

**WHY THE LEAF IS FALSE WITHOUT `[GeometricallyConnected q]`**: with `Y = {y₀, y₁}` two
points over `S = Spec k` the locus produced by (1) is a single point — see the FAITHFULNESS
NOTE in the module docstring.  So half (2) is not decoration and cannot be dropped.

**AXIS SEARCHED**: the affine and affine-over-the-base cases are DONE and are not what is
missing here (`exists_comp_snd_eq_of_isAffine`, `exists_comp_snd_eq_of_isAffine_pullback`);
so is the `Γ ⊣ Spec` corollary, and so — as of this cut — are the epimorphism property of
the projection (`eq_of_comp_snd_eq`), the cartesian square
(`isPullback_sliceOverOpen`) and the whole gluing step.  What is missing is purely the
scheme-theoretic topology: `IsProper → IsClosedMap` for the base-changed projection, and
the `GeometricallyConnected` clopen argument.  The étale axis
(`section_eq_of_formallyUnramified`, diagonal simultaneously open and closed) is searched
and DEAD: `Δ_{B/S}` is an open immersion iff `Ω_{B/S} = 0`, which fails in relative
dimension `> 0`. -/
theorem exists_isAffineOpen_slice_nbhd_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    ∃ (V : Y.Opens) (U : Z.Opens), y ∈ V ∧
      IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) ∧
      Set.range (sliceOverOpen p q V ≫ m) ⊆ (U : Set Z) :=
  sorry

/-- **THE COVERING STEP, LOCALISED AT A POINT** — PROVEN over
`exists_isAffineOpen_slice_nbhd_of_slice_const`.

At each point `y : Y` there is an open `V ∋ y` over which `m` factors through a scheme
affine over the base.  Given the leaf's opens `V` and `U`, the factorizing morphism is
`IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m)`: `U.ι` is an open immersion and the
leaf's range containment is literally the hypothesis that `lift` requires, so `W = U`,
`w = U.ι ≫ r` and `j = U.ι`.  That `n` is an `S`-morphism is `hm` together with
`sliceOverOpen p q V ≫ pullback.fst p q = pullback.fst p (V.ι ≫ q)`.

Neither `σ`, `hconst`, `hpush` nor any of the three instance hypotheses is used HERE —
they are all consumed inside the leaf; they are carried only so the statement matches
what the covering step needs. -/
theorem exists_isAffineOver_nbhd_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    ∃ (V : Y.Opens) (W : Scheme.{u}) (w : W ⟶ S) (j : W ⟶ Z)
      (n : pullback p (V.ι ≫ q) ⟶ W),
      y ∈ V ∧ IsAffine (pullback (V.ι ≫ q) w) ∧
      n ≫ w = pullback.fst p (V.ι ≫ q) ≫ p ∧
      n ≫ j = sliceOverOpen p q V ≫ m := by
  obtain ⟨V, U, hy, haff, hrange⟩ :=
    exists_isAffineOpen_slice_nbhd_of_slice_const hpush σ hσ hm c hconst y
  have hrange' : Set.range (sliceOverOpen p q V ≫ m) ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨V, U.toScheme, U.ι ≫ r, U.ι,
    IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange', hy, haff, ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hm, ← Category.assoc]
  congr 1
  simp [sliceOverOpen, pullback.map, pullback.lift_fst]

/-- **THE COVERING STEP OF THE RIGIDITY LEMMA** — PROVEN over
`exists_isAffineOver_nbhd_of_slice_const`.

`Y` is covered by opens `V i` over each of which `m` factors through a scheme `W i` that is
**affine over the base**, in the sense that `V i ×_S W i` is an affine scheme.  Given that,
`exists_comp_snd_eq_of_isAffine_pullback` factors `m` over each `V i`, and
`exists_comp_snd_eq_of_open_cover` glues.

The passage from the pointwise statement is pure bookkeeping and is done here once: index
the cover by the POINTS of `Y`, choosing for each `y` the neighbourhood `V y` produced by
the leaf.  Then `⨆ y, V y = ⊤` because `y ∈ V y`, and every other component of the
conclusion is transported unchanged.  That is the whole reason the remaining leaf may be
stated at a single point — no generality is lost, and a topological argument that had to
carry an index set through itself would be strictly worse. -/
theorem exists_isAffineOver_cover_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ (ι : Type u) (V : ι → Y.Opens) (W : ι → Scheme.{u}) (w : ∀ i, W i ⟶ S)
      (j : ∀ i, W i ⟶ Z) (n : ∀ i, pullback p ((V i).ι ≫ q) ⟶ W i),
      (⨆ i, V i) = ⊤ ∧ (∀ i, IsAffine (pullback ((V i).ι ≫ q) (w i))) ∧
      (∀ i, n i ≫ w i = pullback.fst p ((V i).ι ≫ q) ≫ p) ∧
      (∀ i, n i ≫ j i = sliceOverOpen p q (V i) ≫ m) := by
  choose V W w j n hmem haff hnw hnj using
    exists_isAffineOver_nbhd_of_slice_const (r := r) hpush σ hσ hm c hconst
  refine ⟨↥Y, V, W, w, j, n, ?_, haff, hnw, hnj⟩
  refine top_le_iff.mp fun y _ => ?_
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩

/-- **THE GLUING STEP OF THE RIGIDITY LEMMA** (PROVEN): local factorizations of `m`
through the projection, over an open cover of `Y`, glue to a global one.

**The proof, as carried out.**  Two halves, and the first is the one that is not free.

*Overlaps.*  The chosen `d i : V i ⟶ Z` agree on `V i ×_Y V j` because the factorization
through the projection is UNIQUE — that is `eq_of_comp_snd_eq`, the statement that
`pullback.snd p _` is an EPIMORPHISM, which is where the pushforward hypothesis is spent
(via surjectivity of `p` and the affine-target injectivity; see the section above).
Concretely: write `w := pullback.fst (V i).ι (V j).ι ≫ (V i).ι` for the canonical map
`V i ×_Y V j ⟶ Y`, which equals `pullback.snd (V i).ι (V j).ι ≫ (V j).ι` by
`pullback.condition`.  Base-changing `m` along `w` and using the defining property of
`d k` twice — once through the `i`-leg, once through the `j`-leg — expresses
`pullback.snd p (w ≫ q) ≫ (leg ≫ d k)` as ONE AND THE SAME morphism
`pullback.map … ≫ m` in both cases; cancelling the epimorphism gives the agreement.

*Assembly.*  `Scheme.Cover.glueMorphisms` on `Y.openCoverOfIsOpenCover V hV` produces the
global `d`, and `m = pullback.snd p q ≫ d` is checked on the pullback of that cover along
`pullback.snd p q`.  The `i`-th member of THAT cover is `(X ×_S Y) ×_Y V i`, which
`isPullback_sliceOverOpen` identifies with `X ×_S V i` carrying `sliceOverOpen p q (V i)`;
under that identification the goal is exactly the hypothesis `hd i` combined with
`ι_glueMorphisms`.

This is bookkeeping rather than mathematics, but it is not free: it is the reason
`exists_comp_snd_eq_of_isAffine` is stated as an `∃!` rather than an `∃`, and the reason
`eq_of_comp_snd_eq` had to be proven at all. -/
theorem exists_comp_snd_eq_of_open_cover {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    {ι : Type u} (V : ι → Y.Opens) (hV : (⨆ i, V i) = ⊤)
    (hd : ∀ i, ∃ d : (V i).toScheme ⟶ Z,
      sliceOverOpen p q (V i) ≫ m = pullback.snd p ((V i).ι ≫ q) ≫ d) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  choose d hd using hd
  let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover V hV
  have hcompat : ∀ i j : ι, pullback.fst ((V i).ι) ((V j).ι) ≫ d i
      = pullback.snd ((V i).ι) ((V j).ι) ≫ d j := by
    intro i j
    refine eq_of_comp_snd_eq (p := p)
      (q := (pullback.fst ((V i).ι) ((V j).ι) ≫ (V i).ι) ≫ q) hpush ?_
    have key : ∀ (k : ι) (w : pullback ((V i).ι) ((V j).ι) ⟶ Y)
        (c : pullback ((V i).ι) ((V j).ι) ⟶ (V k).toScheme), c ≫ (V k).ι = w →
        pullback.snd p (w ≫ q) ≫ c ≫ d k
          = pullback.map p (w ≫ q) p q (𝟙 X) w (𝟙 S) (by simp) (by simp) ≫ m := by
      intro k w c hc
      have hNs : pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
            (by rw [Category.comp_id, ← Category.assoc, hc]) ≫ pullback.snd p ((V k).ι ≫ q)
          = pullback.snd p (w ≫ q) ≫ c := by
        simp [pullback.map, pullback.lift_snd]
      have hNslice : pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
            (by rw [Category.comp_id, ← Category.assoc, hc]) ≫ sliceOverOpen p q (V k)
          = pullback.map p (w ≫ q) p q (𝟙 X) w (𝟙 S) (by simp) (by simp) := by
        apply pullback.hom_ext <;>
          simp [sliceOverOpen, pullback.map, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_snd_assoc, hc]
      calc pullback.snd p (w ≫ q) ≫ c ≫ d k
          = (pullback.map p (w ≫ q) p ((V k).ι ≫ q) (𝟙 X) c (𝟙 S) (by simp)
              (by rw [Category.comp_id, ← Category.assoc, hc]) ≫
                sliceOverOpen p q (V k)) ≫ m := by
            rw [Category.assoc, hd k, ← Category.assoc, ← hNs, Category.assoc]
        _ = _ := by rw [hNslice]
    rw [key i _ (pullback.fst ((V i).ι) ((V j).ι)) rfl,
      key j _ (pullback.snd ((V i).ι) ((V j).ι)) pullback.condition.symm]
  have hglue : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms d hcompat = d i :=
    fun i => 𝒰.ι_glueMorphisms d hcompat i
  refine ⟨𝒰.glueMorphisms d hcompat, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd p q)) _ _ fun i => ?_
  show pullback.fst (pullback.snd p q) ((V i).ι) ≫ m
      = pullback.fst (pullback.snd p q) ((V i).ι) ≫ pullback.snd p q ≫
        𝒰.glueMorphisms d hcompat
  refine (cancel_epi ((isPullback_sliceOverOpen p q (V i)).isoPullback.hom)).mp ?_
  rw [← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst, hd i,
    ← Category.assoc, (isPullback_sliceOverOpen p q (V i)).w, Category.assoc, hglue i]

/-- **THE RIGIDITY LEMMA** (PROVEN over the covering and gluing leaves above — Mumford
*Abelian Varieties* §4; BLR *Néron Models* 8.4 in the relative case; Mumford *GIT* Prop. 6.1
over a general base).

Let `p : X ⟶ S` be proper with `𝒪_S = p_*𝒪_X` universally, let `q : Y ⟶ S` have
geometrically connected fibres, and let `r : Z ⟶ S` be separated.  An `S`-morphism
`m : X ×_S Y ⟶ Z` that is CONSTANT along one slice `X ×_S σ(S)` — that is, whose
restriction along `sliceIncl` factors through `p` — factors through the projection to `Y`.

**The proof.**  Fix `s ∈ S` and an affine open `U ⊆ Z` containing the image of the
contracted slice.  `m⁻¹(Z ∖ U)` is closed in `X ×_S Y`, and `pullback.snd p q` is proper
(base change of `p`; the earlier version of this note said `pullback.fst`, which is the base
change of `q` and lands in `X`), so its image in `Y` is closed and misses `σ(S)`; on the open
complement `V` the whole slice `X ×_S V` maps into the affine `U`, and a morphism from a
proper scheme with `p_*𝒪 = 𝒪` to an affine scheme over the base factors through the base
— this is where the pushforward hypothesis is consumed, and it is consumed after a base
change to `V`, which is why the hypothesis is the UNIVERSAL one.  So `m` factors through
`Y` over `V`.  The locus where `m` factors is then open and closed, and
`GeometricallyConnected q` makes it everything.

**WHY `[GeometricallyConnected q]` IS NOT DECORATION**: see the FAITHFULNESS NOTE in the
module docstring — with `Y = {y₀, y₁}` two points the statement is false.

**STATUS (2026-07-27).**  The check recorded here — "land
`hasUniversallyTrivialPushforward_of_isProper_of_flat`, add the corollary *an `S`-morphism
from `X` to a scheme affine over `S` factors uniquely through `S`*, and this leaf is the
topological argument and nothing more" — has been RUN, and it came out as predicted.  The
corollary is `HasTrivialPushforward.existsUnique_comp_eq` (equivalently
`existsUnique_comp_eq_of_hasTrivialPushforward`), its relative form is
`exists_comp_snd_eq_of_isAffine_pullback`, and both are PROVEN above and consumed below,
**without** `hasUniversallyTrivialPushforward_of_isProper_of_flat` having landed (that leaf
is an input to the *hypothesis* `hpush`, not to this proof).  What is left is exactly the
topology, split into `exists_isAffineOver_cover_of_slice_const` (the covering — properness,
`σ`, connectedness) and `exists_comp_snd_eq_of_open_cover` (the gluing).

**STATUS (2026-07-27, later).**  The gluing is now PROVEN — over `eq_of_comp_snd_eq`, the
epimorphism property of the projection, which is itself proven from the universal
pushforward hypothesis via surjectivity of `p`.  The covering is PROVEN over
`exists_isAffineOver_nbhd_of_slice_const` (its pointwise form), which is in turn PROVEN
over `exists_isAffineOpen_slice_nbhd_of_slice_const` (its opens-only form).  So this
theorem now rests on exactly ONE open leaf, and that leaf is purely
`IsProper ⟹ IsClosedMap` plus the `GeometricallyConnected` clopen argument at a single
point of `Y`.

The concrete obstruction the earlier audit named is still worth recording, because it is
what that leaf has to get past: the reduction to an affine target cannot be done
globally — with `S = Spec k`, `X = Spec k`, `Y = Z = ℙ¹`, `q = r` the structure maps and
`m = 𝟙`, every hypothesis holds, `d = 𝟙` is the factorization, and `m` factors through no
affine scheme.  So the work is genuinely local-to-global on `Y`. -/
theorem exists_comp_snd_eq_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  obtain ⟨ι, V, W, w, j, n, hVtop, hWaff, hnw, hnj⟩ :=
    exists_isAffineOver_cover_of_slice_const hpush σ hσ hm c hconst
  refine exists_comp_snd_eq_of_open_cover hpush V hVtop fun i => ?_
  haveI := hWaff i
  obtain ⟨e, he⟩ := exists_comp_snd_eq_of_isAffine_pullback (p := p) (q := (V i).ι ≫ q)
    (r := w i) hpush (hnw i)
  exact ⟨e ≫ j i, by rw [← hnj i, he, Category.assoc]⟩

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
