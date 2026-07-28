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
* `isIso_appTop_of_isIso_app_affineOpens` — **PROVEN**: `f.appTop` is an isomorphism as soon
  as `f.app U` is for every *affine* open `U ⊆ S`.  Pure sheaf theory (`f.app U` is the
  component at `U` of `𝒪_S ⟶ f_*𝒪_X`, and the affine opens are a basis), and it is what
  lets the remaining leaf be stated over an affine base.
* `isIso_appTop_of_isProper_over_field` — **LEAF** (2026-07-27): `H⁰(Z, 𝒪_Z) = K` for `Z`
  proper, geometrically connected and geometrically reduced over a field `K`.  One scheme,
  one field, no flatness and no base change — the tractable half, and the one to take first.
* `isIso_appTop_of_isIso_appTop_fiber` — **PROVEN** (2026-07-28), degree-zero cohomology and
  base change.  For `f` proper, flat and of finite presentation over an **affine** base,
  `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism as soon as `κ(s) ⟶ Γ(X_s, ⊤)` is one for every
  `s ∈ S`.  Geometric connectedness and reducedness do not appear: they enter only through
  the fibrewise hypothesis.  Proven over three new leaves plus a fully proven
  commutative-algebra assembly (Nakayama on the cokernel; the equational criterion for
  flatness on the kernel):
  * `module_finite_appTop_of_isProper` — **LEAF**: `Γ(X, ⊤)` is a finite `Γ(S, ⊤)`-module.
    Grothendieck's finiteness theorem for a proper morphism, in degree `0`.
  * `module_flat_appTop_of_isIso_appTop_fiber` — **LEAF**: `f_*𝒪_X` is flat over the base.
  * `bijective_quotientMap_appTop_of_isIso_appTop_fiber` — **LEAF**: `R/𝔪 ⟶ A/𝔪A` is
    bijective at every maximal ideal.  The **only** consumer of the fibrewise hypothesis.

  The last two are two readings of ONE theorem (Hartshorne III.12.11 in degree `0`) and
  should go to a single owner; the first is independent of them.  The commutative algebra —
  `eq_bot_of_fg_of_le_smul_of_forall_isMaximal`,
  `surjective_algebraMap_of_finite_of_forall_isMaximal`,
  `injective_algebraMap_of_flat_of_ker_le_jacobson` and
  `bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap` — is proven here and is
  pure `RingTheory`; it could be hoisted to a shim file unchanged.
* `isIso_appTop_of_isProper_of_flat_of_isAffine` — **PROVEN** over those two, by feeding the
  first into the second (every fibre is a base change of `f`).
* `isIso_appTop_of_isProper_of_flat` — **PROVEN** over it, by the affine reduction.
* `hasUniversallyTrivialPushforward_of_isProper_of_flat` — **PROVEN** over it too.  Both
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
* `exists_comp_snd_eq_of_slice_const` — the RIGIDITY LEMMA (Mumford *AV* §4;
  BLR *Néron Models* 8.4 in the relative case), PROVEN over the two leaves below.
* `exists_isAffineOver_cover_of_slice_const` — **LEAF**: `Y` is covered by opens over each of
  which `m` factors through a scheme affine over the base.  This is where properness of
  `pullback.snd`, the section `σ` and `[GeometricallyConnected q]` are consumed.
* `exists_comp_snd_eq_of_open_cover` — **LEAF**: local factorizations through the projection,
  over an open cover of `Y`, glue to a global one.

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

Both leaves are stated with `sliceOverOpen p q V : X ×_S V ⟶ X ×_S Y`, the canonical map
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

/-! ### Reduction to an affine base

`IsIso (f.app U)` is a statement about the ⊤-component of a map of **sheaves** on `S`, namely
`f.c : 𝒪_S ⟶ f_*𝒪_X`.  So it is local on `S`, and the reduction of the theorem below to the
case of an affine base is pure sheaf theory, with no geometry in it at all. -/

/-- **`f.appTop` IS AN ISOMORPHISM AS SOON AS `f.app U` IS FOR EVERY AFFINE OPEN `U ⊆ S`**
(PROVEN).

`f.app U` is the component at `U` of `f.c : 𝒪_S ⟶ f_*𝒪_X`, a morphism of sheaves of rings on
`S` (the target is a sheaf by `TopCat.Sheaf.pushforward_sheaf_of_sheaf`).  The affine opens are
a basis of `S` (`Scheme.isBasis_affineOpens`), so componentwise bijectivity on them gives
bijectivity on every stalk — injectivity by `stalkFunctor_map_injective_of_isBasis`, surjectivity
because every germ is represented on a basis open (`exists_mem_germ_eq_of_isBasis`) — and a
morphism of sheaves that is a stalkwise isomorphism is an isomorphism on every open, in
particular on `⊤` (`app_isIso_of_stalkFunctor_map_iso`).

This is the step that lets the cohomological content below be stated over an **affine** base,
where `Γ(S, ⊤)` is an honest ring and `Γ(X, ⊤)` an honest module over it. -/
theorem isIso_appTop_of_isIso_app_affineOpens (f : X ⟶ S)
    (h : ∀ U ∈ S.affineOpens, IsIso (f.app U)) : IsIso f.appTop := by
  let G : TopCat.Sheaf CommRingCat S :=
    ⟨f.base _* X.presheaf, TopCat.Sheaf.pushforward_sheaf_of_sheaf f.base X.sheaf.2⟩
  let α : S.sheaf ⟶ G := ⟨f.c⟩
  have hb : TopologicalSpace.Opens.IsBasis S.affineOpens := S.isBasis_affineOpens
  have hbij : ∀ x : S, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.1) := by
    intro x
    constructor
    · refine TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hb ?_ x
      intro U hU
      haveI := h U hU
      exact (ConcreteCategory.bijective_of_isIso (f.app U)).1
    · intro t
      obtain ⟨U, hxU, hU, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hb G.1 x t
      haveI := h U hU
      obtain ⟨s', rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.app U)).2 s
      exact ⟨S.presheaf.germ U x hxU s',
        TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU α.1 s'⟩
  haveI : ∀ x : S, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.1) :=
    fun x => (ConcreteCategory.isIso_iff_bijective _).mpr (hbij x)
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso α ⊤

/-! ### The two leaves: the fibrewise computation, and cohomology and base change

The classical proof of `f_*𝒪_X = 𝒪_S` has exactly two moving parts, and they are independent
of one another:

* **over a field** — `H⁰(Z, 𝒪_Z) = K` for `Z` proper, geometrically connected and
  geometrically reduced over `K` (`isIso_appTop_of_isProper_over_field`).  No flatness, no
  base change, no cohomology in positive degree: this is a statement about *one* scheme over
  *one* field, and it is by far the more tractable half;
* **cohomology and base change** — for `f` proper, flat and of finite presentation over an
  affine base, `𝒪_S ⟶ f_*𝒪_X` is an isomorphism as soon as it is one on every fibre
  (`isIso_appTop_of_isIso_appTop_fiber`, now **PROVEN** over three narrower leaves).  This
  half never sees geometric connectedness or reducedness: they enter *only* through the
  fibrewise hypothesis.

`isIso_appTop_of_isProper_of_flat_of_isAffine` is PROVEN by feeding the first into the second,
which is why the two are cut apart here rather than proved together. -/

/-- **`H⁰(Z, 𝒪_Z) = K` FOR A PROPER, GEOMETRICALLY CONNECTED, GEOMETRICALLY REDUCED SCHEME
OVER A FIELD** (LEAF, 2026-07-27) — the fibrewise half of the pushforward theorem, and the
tractable one.

**The classical argument.**  Write `A := Γ(Z, ⊤)`.

1. `K ⟶ A` is *integral*: this is already in `Mathlib`, as
   `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` (properness is not even needed,
   universal closedness over an affine base suffices).
2. `A` is *reduced*, because `Z` is (geometric reducedness over `K` in particular gives
   `IsReduced Z`, `AlgebraicGeometry.GeometricallyReduced` instances).
3. Hence `A` is a *field*.  Every `a ∈ A` is algebraic over `K`, so `K[a]` is a finite reduced
   `K`-algebra, i.e. a finite product of fields; an idempotent of `K[a]` is an idempotent of
   `A`, and `Z` is connected, so `A` has no idempotents other than `0` and `1` (a nontrivial
   idempotent of `Γ(Z, ⊤)` is exactly a decomposition of `Z` into two nonempty opens).  So
   `K[a]` is a field and `a` is invertible when nonzero.
4. `A` is *finite* over `K`, by `AlgebraicGeometry.finite_appTop_of_universallyClosed` once
   `A` is known to be a field — note that mathlib's version is stated under `[IsIntegral Z]`,
   which is *stronger* than what is available here (connected + reduced does not give
   irreducible: two lines meeting in a point are a standing counterexample, and they do have
   `H⁰ = k`).  So this step needs the mathlib proof re-run without irreducibility; its actual
   content is `RingHom.finite_of_algHom_finiteType_of_isJacobsonRing` applied to
   `Γ(Z, ⊤) ⟶ Γ(Z, U)` for an affine open `U`, and irreducibility is used there only to know
   `Z` is nonempty — which geometric connectedness also gives.
5. Finally `[A : K] = 1`.  `A/K` is a finite field extension; geometric reducedness makes it
   *separable*, so `A ⊗_K K̄ ≅ K̄^{[A:K]}` has `[A : K]` idempotents, while geometric
   connectedness makes `Z_{K̄}` connected, hence `Γ(Z_{K̄}, 𝒪)` idempotent-free.  The one
   nontrivial input is that `Γ` of a quasi-compact quasi-separated scheme over a field
   commutes with the (flat) base change `K ⟶ K̄` — which for `H⁰` alone is the equalizer of a
   finite Čech diagram of affines and the exactness of `- ⊗_K K̄`, *not* the full
   cohomology-and-base-change theorem.

**FAITHFULNESS.**  All three hypotheses are load-bearing.  Without geometric connectedness the
statement fails for `Z = Spec (K × K)`; without geometric reducedness it fails for
`Z = Spec (K[ε]/ε²)`; and *geometric* connectedness cannot be weakened to connectedness — for
`K = ℝ` and `Z = Spec ℂ`, `Z` is connected, reduced and proper over `ℝ`, and
`H⁰(Z, 𝒪) = ℂ ≠ ℝ`.  Likewise geometric reducedness cannot be weakened to reducedness, by the
usual inseparable example `Z = Spec 𝔽_p(t^{1/p})` over `K = 𝔽_p(t)`. -/
theorem isIso_appTop_of_isProper_over_field {K : CommRingCat.{u}} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec K) [IsProper g] [GeometricallyConnected g] [GeometricallyReduced g] :
    IsIso g.appTop :=
  sorry

/-! #### The commutative algebra of the base-change argument

Everything in this block is pure commutative algebra about a ring map `φ : R ⟶ A`; no
geometry appears, and it is all **PROVEN**.  It lives here only because this file is its
single consumer — it would sit just as well in a `RingTheory` shim, and can be hoisted
verbatim.  It is stated inside `namespace AlgebraicGeometry` (with undotted names) so that
nothing lands in the root namespace.

What it isolates is exactly the part of the classical proof that is *not* cohomology: given
that `A` is a finite `R`-module, that `A` is `R`-flat, and that `R/𝔪 ⟶ A/𝔪A` is bijective
for every maximal `𝔪`, the map `R ⟶ A` is itself bijective.  The three geometric leaves
below supply those three inputs and nothing else. -/

/-- **NAKAYAMA OVER EVERY MAXIMAL IDEAL** (PROVEN): a finitely generated submodule `N` with
`N ≤ 𝔪 • N` for *every* maximal ideal `𝔪` is zero.

The usual local statement needs `𝔪` inside the Jacobson radical; the global one is got from
it by looking at the annihilator.  If `N ≠ 0` then `Ann N ≠ ⊤`, so `Ann N ≤ 𝔪` for some
maximal `𝔪`; the determinant trick
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) applied at that `𝔪`
produces `r` with `r - 1 ∈ 𝔪` and `r ∈ Ann N ≤ 𝔪`, whence `1 ∈ 𝔪`.  So `Ann N = ⊤` and
`N = 1 • N = 0`. -/
theorem eq_bot_of_fg_of_le_smul_of_forall_isMaximal {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {N : Submodule R M} (hfg : N.FG)
    (h : ∀ m : Ideal R, m.IsMaximal → N ≤ m • N) : N = ⊥ := by
  have hann : N.annihilator = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr2⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m N hfg (h m hm)
    have hrann : r ∈ N.annihilator := Submodule.mem_annihilator.mpr hr2
    have hone : (1 : R) ∈ m := by
      have h1 : r ∈ m := hle hrann
      have h2 := Submodule.sub_mem m h1 hr1
      simpa using h2
    exact hm.ne_top (Ideal.eq_top_iff_one m |>.mpr hone)
  refine le_antisymm (fun x hx => ?_) bot_le
  have h1 : (1 : R) ∈ N.annihilator := by rw [hann]; trivial
  have := Submodule.mem_annihilator.mp h1 x hx
  simpa using this

/-- **SURJECTIVITY BY NAKAYAMA** (PROVEN): if `A` is a *finite* `R`-module and every element
of `A` is congruent to an element of `R` modulo `𝔪A`, for every maximal ideal `𝔪`, then
`R ⟶ A` is surjective.

This is `eq_bot_of_fg_of_le_smul_of_forall_isMaximal` applied to `⊤` in the cokernel
`A ⧸ (image of R)`: the hypothesis says exactly that the cokernel is killed by passing to
`A/𝔪A`, i.e. that `⊤ ≤ 𝔪 • ⊤` there.  Only *finiteness* of `A` is used, not finite
presentation. -/
theorem surjective_algebraMap_of_finite_of_forall_isMaximal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (h : ∀ m : Ideal R, m.IsMaximal → ∀ a : A,
      ∃ r : R, a - algebraMap R A r ∈ m.map (algebraMap R A)) :
    Function.Surjective (algebraMap R A) := by
  set N : Submodule R A := LinearMap.range (Algebra.linearMap R A) with hNdef
  haveI : Module.Finite R (A ⧸ N) := Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  have hQ : (⊤ : Submodule R (A ⧸ N)) = ⊥ := by
    refine eq_bot_of_fg_of_le_smul_of_forall_isMaximal Module.Finite.fg_top ?_
    intro m hm q _
    obtain ⟨a, rfl⟩ := N.mkQ_surjective q
    obtain ⟨r, hr⟩ := h m hm a
    have hmem : a - algebraMap R A r ∈ m • (⊤ : Submodule R A) := by
      rw [Ideal.smul_top_eq_map]
      exact hr
    have hz : N.mkQ (algebraMap R A r) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨r, rfl⟩
    have heq : N.mkQ a = N.mkQ (a - algebraMap R A r) := by
      rw [map_sub, hz, sub_zero]
    rw [heq]
    have hmap : Submodule.map N.mkQ (m • (⊤ : Submodule R A))
        = m • (⊤ : Submodule R (A ⧸ N)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap]
    exact Submodule.mem_map_of_mem hmem
  intro a
  have hmem : N.mkQ a = 0 := by
    have h0 : N.mkQ a ∈ (⊤ : Submodule R (A ⧸ N)) := Submodule.mem_top
    rw [hQ] at h0
    simpa using h0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact ⟨r, hr⟩

/-- **INJECTIVITY FROM FLATNESS, WITHOUT ANY FINITENESS** (PROVEN): if `A` is a *flat*
`R`-algebra, `R ⟶ A` is surjective, and `ker (R ⟶ A)` lies in the Jacobson radical of `R`,
then `R ⟶ A` is injective.

The classical route here goes through `Tor₁(A, R/𝔪) = 0` and needs `ker` finitely generated
(via `Module.FinitePresentation.fg_ker`).  It is **not** needed: the *equational criterion
for flatness* (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, Stacks 00HK) applied to
the one-term relation `k • (1 : A) = 0` gives `aⱼ ∈ R` and `yⱼ ∈ A` with `1 = ∑ aⱼ • yⱼ` and
`k * aⱼ = 0`.  Surjectivity turns `yⱼ` into `algebraMap dⱼ`, so `e := ∑ aⱼ dⱼ` satisfies
`algebraMap e = 1` — i.e. `e - 1 ∈ ker` — and `k * e = 0`.  Since `e - 1` is in the Jacobson
radical, `e` is a *unit*, so `k = 0` outright.  No Nakayama, no finite generation, no `Tor`.

That is why the geometric leaf below asks only for `Module.Finite`, not
`Module.FinitePresentation`. -/
theorem injective_algebraMap_of_flat_of_ker_le_jacobson
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (hsurj : Function.Surjective (algebraMap R A))
    (hker : RingHom.ker (algebraMap R A) ≤ Ideal.jacobson ⊥) :
    Function.Injective (algebraMap R A) := by
  refine (injective_iff_map_eq_zero (algebraMap R A)).mpr ?_
  intro k hk
  have hrel : ∑ _i : Unit, k • (1 : A) = 0 := by
    simp [Algebra.smul_def, hk]
  obtain ⟨n, a, y, hx, ha⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) (ι := Unit)
      (f := fun _ => k) (x := fun _ => (1 : A)) hrel
  choose d hd using hsurj
  set e : R := ∑ j, a () j * d (y j) with he
  have he1 : algebraMap R A e = 1 := by
    rw [he, map_sum]
    have hterm : ∀ j : Fin n, algebraMap R A (a () j * d (y j)) = a () j • y j := by
      intro j
      rw [map_mul, hd, Algebra.smul_def]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← hx ()]
  have hke : k * e = 0 := by
    rw [he, Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : k * a () j = 0 := by simpa using ha j
    rw [← mul_assoc, hj, zero_mul]
  have hsub : e - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    refine hker ?_
    simp [RingHom.mem_ker, map_sub, he1]
  obtain ⟨b, hb⟩ := (Ideal.isUnit_of_sub_one_mem_jacobson_bot e hsub).exists_right_inv
  calc k = k * (e * b) := by rw [hb, mul_one]
    _ = (k * e) * b := by ring
    _ = 0 := by rw [hke, zero_mul]

/-- **THE ASSEMBLED COMMUTATIVE-ALGEBRA STATEMENT** (PROVEN): a finite flat `R`-algebra `A`
whose reduction `R/𝔪 ⟶ A/𝔪A` is bijective at every maximal ideal `𝔪` has `R ⟶ A` bijective.

Surjectivity is `surjective_algebraMap_of_finite_of_forall_isMaximal` (Nakayama on the
cokernel); injectivity is `injective_algebraMap_of_flat_of_ker_le_jacobson`, whose Jacobson
hypothesis is exactly the *injective* half of `R/𝔪 ⟶ A/𝔪A` read at every maximal `𝔪`
(`ker ≤ 𝔪` for all `𝔪`, and `Ideal.jacobson ⊥` is the infimum of the maximal ideals).

This is the whole of the base-change theorem that is not cohomology. -/
theorem bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (h : ∀ m : Ideal R, m.IsMaximal →
      Function.Bijective (Ideal.quotientMap (I := m) (m.map (algebraMap R A))
        (algebraMap R A) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap R A) := by
  have hsurj : Function.Surjective (algebraMap R A) := by
    refine surjective_algebraMap_of_finite_of_forall_isMaximal ?_
    intro m hm a
    obtain ⟨x, hx⟩ := (h m hm).2 (Ideal.Quotient.mk _ a)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨r, ?_⟩
    rw [Ideal.quotientMap_mk] at hx
    exact (Ideal.Quotient.eq.mp hx.symm)
  refine ⟨?_, hsurj⟩
  refine injective_algebraMap_of_flat_of_ker_le_jacobson hsurj ?_
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro J ⟨-, hJ⟩
  intro k hk
  have h0 : Ideal.quotientMap (I := J) (J.map (algebraMap R A)) (algebraMap R A)
      Ideal.le_comap_map (Ideal.Quotient.mk J k) = 0 := by
    rw [Ideal.quotientMap_mk]
    have hk0 : algebraMap R A k = 0 := hk
    rw [hk0, map_zero]
  have hinj : (Ideal.Quotient.mk J) k = 0 := (h J hJ).1 (by simpa using h0)
  rwa [Ideal.Quotient.eq_zero_iff_mem] at hinj

/-! #### The three geometric inputs

`R := Γ(S, ⊤)` and `A := Γ(X, ⊤)`, with `A` an `R`-algebra through `φ := f.appTop`.  Each of
the three leaves below is one of the hypotheses of
`bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap`, and together they are the
*entire* remaining content of degree-zero cohomology and base change.

**They are not three independent theory builds.**  Leaf 1 is Grothendieck's finiteness
theorem for a proper morphism (coherence of `f_*`); leaves 2 and 3 are two readings of *one*
theorem, Hartshorne III.12.11 / EGA III 7.8.6 applied in degree `0`, and should be dispatched
to a single owner:

* the comparison map `φ⁰(s) : (f_*𝒪_X) ⊗ κ(s) ⟶ H⁰(X_s, 𝒪)` is **surjective** for every `s`,
  because the hypothesis `h s` factors it: `κ(s) ⟶ (f_*𝒪_X) ⊗ κ(s) ⟶ H⁰(X_s, 𝒪)` is the
  structure map, which `h s` says is an isomorphism;
* III.12.11(a) then makes `φ⁰(s)` an isomorphism — that is **leaf 3**, since
  `(f_*𝒪_X) ⊗ κ(s) = A/𝔪A` over an affine base and `κ(s) = R/𝔪`;
* III.12.11(b), whose extra hypothesis in degree `0` is vacuous (`φ⁻¹` is a map of zero
  modules), then makes `f_*𝒪_X` **locally free** — that is **leaf 2**.

Note that the reducedness of `S` demanded by Grauert (Hartshorne III.12.9, Mumford *AV* §5
Corollary 2) is *not* needed on this route: III.12.11 has no such hypothesis, which matters
here because the bases this development feeds in are arbitrary. -/

/-- **LEAF 1 — `Γ(X, ⊤)` IS A FINITE `Γ(S, ⊤)`-MODULE** (Grothendieck's finiteness theorem
for a proper morphism; EGA III 3.2.1, Stacks 02O5 / 0B91).

Over an affine base, `Γ(X, ⊤) = (f_*𝒪_X)(S)`, so this is coherence of the direct image of
`𝒪_X` along a proper morphism, in degree `0`.

**What mathlib already gives, and what it does not.**
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` applies verbatim here (properness
gives `UniversallyClosed`, and `S` is affine) and yields that `φ = f.appTop` is **integral**.
Integral plus *finite type* is finite, so what is missing is precisely that `Γ(X, ⊤)` is an
`R`-algebra of finite type — which for non-affine `X` is not formal and is the actual content
of the finiteness theorem.  Mathlib's `finite_appTop_of_universallyClosed` is not usable: it
is stated over a *field* and under `[IsIntegral X]`.

`[Flat f]` is listed because over a base that is not noetherian the finiteness theorem is
stated for a proper morphism *of finite presentation* with the sheaf flat over the base; it
is not otherwise used, and a prover working over a noetherian base may ignore it.

**FAITHFULNESS.** Properness is essential: `𝔸¹_S ⟶ S` is flat and of finite presentation
with `Γ = R[x]`, not a finite `R`-module. -/
theorem module_finite_appTop_of_isProper (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
  sorry

/-- **LEAF 2 — `f_*𝒪_X` IS FLAT OVER THE BASE** (Hartshorne III.12.11(b) in degree `0`,
EGA III 7.8.6; the "constant `h⁰` ⟹ locally free" half of cohomology and base change).

Over an affine base this is exactly `Module.Flat R A` for `A = Γ(X, ⊤)`.  The hypothesis `h`
is what makes it true: it says `h⁰(X_s, 𝒪) = 1` for every `s`, so `s ↦ dim_{κ(s)} H⁰(X_s, 𝒪)`
is constant, and the comparison map `φ⁰(s)` is surjective (see the block comment above).
III.12.11(b) then gives `R⁰f_*𝒪_X = f_*𝒪_X` locally free, hence flat.

**FAITHFULNESS — `h` cannot be dropped.**  Without it the statement is false: `h⁰` is only
upper semicontinuous along a proper flat family, and where it jumps `f_*𝒪_X` is not locally
free.  `[Flat f]` cannot be dropped either — it is the hypothesis of III.12.11 itself.

**Shared with leaf 3.**  A prover who builds the degree-`0` base-change comparison map gets
both this leaf and `bijective_quotientMap_appTop_of_isIso_appTop_fiber` from it; they should
not be attacked separately. -/
theorem module_flat_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.Flat ↥Γ(S, ⊤) ↥Γ(X, ⊤) :=
  sorry

/-- **LEAF 3 — DEGREE-ZERO BASE CHANGE AT A CLOSED POINT** (Hartshorne III.12.11(a) in degree
`0`, EGA III 7.8.6): for every maximal ideal `𝔪` of `R = Γ(S, ⊤)`, the induced map
`R/𝔪 ⟶ A/𝔪A` is bijective.

This is the *only* place the fibrewise hypothesis enters the final theorem, and it enters
through the identification `A/𝔪A = (f_*𝒪_X) ⊗_R κ(s) ≅ H⁰(X_s, 𝒪_{X_s})` of degree-zero base
change, where `s ∈ S` is the closed point cut out by `𝔪` and `κ(s) = R/𝔪`.  Under that
identification the map `R/𝔪 ⟶ A/𝔪A` *is* `(f.fiberToSpecResidueField s).appTop`, which `h s`
says is an isomorphism.

Only maximal ideals appear because that is all the Nakayama assembly consumes; the base-change
theorem of course gives the statement at every point.

**FAITHFULNESS.**  The two halves are separately load-bearing and separately used:
surjectivity drives Nakayama on the cokernel, and injectivity is what puts `ker φ` inside the
Jacobson radical.  Note also that `h` forces every fibre to be **nonempty** — for `X_s = ∅`
one has `Γ(X_s, ⊤) = 0` and a field never maps isomorphically to the zero ring — which is
correct and intended, since `𝒪_S ⟶ f_*𝒪_X` is not an isomorphism over a point missed by `f`.

**Shared with leaf 2**: see `module_flat_appTop_of_isIso_appTop_fiber`. -/
theorem bijective_quotientMap_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
    ∀ m : Ideal ↥Γ(S, ⊤), m.IsMaximal →
      Function.Bijective (Ideal.quotientMap (I := m)
        (m.map (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤))) (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤))
        Ideal.le_comap_map) :=
  sorry

/-- **COHOMOLOGY AND BASE CHANGE IN DEGREE ZERO: `𝒪_S ⟶ f_*𝒪_X` IS AN ISOMORPHISM AS SOON AS
IT IS ONE ON EVERY FIBRE** — **PROVEN** (2026-07-28) over the three leaves above, by the
commutative-algebra assembly in this file (Hartshorne III.12.11, Grauert, Stacks 0E0L /
EGA III 7.8.6).

Note what is *not* here: no geometric connectedness, no geometric reducedness.  Those enter
only through the hypothesis `h`, discharged by `isIso_appTop_of_isProper_over_field` above.
What is left is exactly the classical cohomology-and-base-change statement, with the fibre
input abstracted away.

**THE ROUTE, in the vocabulary `[IsAffine S]` provides.**  Put `R := Γ(S, ⊤)`,
`A := Γ(X, ⊤)`, `φ := f.appTop : R ⟶ A`.  Three inputs give `φ` bijective:

1. *`A` is a finite `R`-module* — `module_finite_appTop_of_isProper`, the finiteness theorem
   for a proper morphism.  (An earlier version of this docstring asked for finite
   *presentation*; the injectivity argument below does not need it, see
   `injective_algebraMap_of_flat_of_ker_le_jacobson`.)
2. *`A` is `R`-flat* — `module_flat_appTop_of_isIso_appTop_fiber`.  This is where `Flat f`
   enters, through cohomology and base change: `f_*𝒪_X` is locally free with formation
   commuting with base change.
3. *For every maximal ideal `𝔪 ⊂ R`, `R/𝔪 ⟶ A/𝔪A` is bijective* —
   `bijective_quotientMap_appTop_of_isIso_appTop_fiber`, degree-zero base change, and the
   only consumer of the hypothesis `h`.

Given those, `φ` is surjective by Nakayama applied to `coker φ` (finitely generated, and zero
modulo every maximal ideal), and injective because flatness plus the equational criterion
turns `k • (1 : A) = 0` into `k * e = 0` for a *unit* `e` — the kernel lies in the Jacobson
radical by the injective half of input 3.  All of that is proven above; nothing of it is
geometric.

**Why `[IsAffine S]` costs nothing**: `isIso_appTop_of_isIso_app_affineOpens` above reduces the
general base to this one, because `f.app U` is the component at `U` of the sheaf map
`𝒪_S ⟶ f_*𝒪_X` and the affine opens are a basis of `S`.  It is what makes `R` and `A` honest
rings and the argument above expressible at all.

**FAITHFULNESS.**  Flatness is essential — without it `h⁰` jumps and the conclusion is false
(blow up a point on a surface and the exceptional fibre still has `H⁰ = κ(s)`, but a
non-flat family does not have `f_*𝒪 = 𝒪`).  The hypothesis `h` also silently forces every
fibre to be *nonempty*: for `X_s = ∅` one has `Γ(X_s, ⊤) = 0`, and a field never maps
isomorphically to the zero ring.  That is correct and intended — `𝒪_S ⟶ f_*𝒪_X` is not an
isomorphism over a point missed by `f`.

**PIN STATE, checked rather than assumed (2026-07-27, re-checked at `122c02b0`).**  `Mathlib`
has no higher direct images of quasi-coherent sheaves, no `Rⁱf_*`, no semicontinuity, no
cohomology-and-base-change: `grep -rn 'higherDirectImage\|directImage\|
cohomologyAndBaseChange' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/ ~/cs/FLT/FLT/
Fermat/` returns zero hits.  So the leaves above are a theory build and not a missing-lemma
hunt.  What mathlib *does* supply, and what an earlier version of this docstring did not
record, is `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`,
`AlgebraicGeometry.isField_of_universallyClosed` and
`AlgebraicGeometry.finite_appTop_of_universallyClosed`
(`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`) — the last two under `[IsIntegral X]`. -/
theorem isIso_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    IsIso f.appTop := by
  letI : Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤) := f.appTop.hom.toAlgebra
  haveI : Module.Finite ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_finite_appTop_of_isProper f
  haveI : Module.Flat ↥Γ(S, ⊤) ↥Γ(X, ⊤) := module_flat_appTop_of_isIso_appTop_fiber f h
  have hb := bijective_algebraMap_of_finite_of_flat_of_bijective_quotientMap
    (bijective_quotientMap_appTop_of_isIso_appTop_fiber f h)
  rw [RingHom.algebraMap_toAlgebra] at hb
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hb

/-! ### The theorem -/

/-- **`Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY
CONNECTED AND REDUCED FIBRES, OVER AN AFFINE BASE** — **PROVEN** (2026-07-27) over the two
leaves above, by the one-line assembly they were cut for: every fibre
`f.fiberToSpecResidueField s : X_s ⟶ Spec κ(s)` is a base change of `f`, hence proper,
geometrically connected and geometrically reduced over the field `κ(s)`, so
`isIso_appTop_of_isProper_over_field` discharges the fibrewise hypothesis of
`isIso_appTop_of_isIso_appTop_fiber`.

This is the missing classical input behind the whole Jacobian half of this development:
`isAdditiveOn_of_post_zero` (relative rigidity), `exists_albaneseOfCurve` and
`universal_jacobianBaseChangeAj` all reduce to it, which is why it is stated here, once,
in the shim tree rather than inside a modular-curve file.

**The instance plumbing, for the record.**  `f.fiberToSpecResidueField s` is by definition
`pullback.snd f (S.fromSpecResidueField s)`, and mathlib already carries
`GeometricallyConnected (f.fiberToSpecResidueField s)` and
`GeometricallyReduced (f.fiberToSpecResidueField s)` as instances; only `IsProper` has to be
produced by hand, from `MorphismProperty.pullback_snd`. -/
theorem isIso_appTop_of_isProper_of_flat_of_isAffine (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    IsIso f.appTop := by
  refine isIso_appTop_of_isIso_appTop_fiber f fun s => ?_
  haveI : IsProper (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact isIso_appTop_of_isProper_over_field _

/-- **`Γ(S, ⊤) ⟶ Γ(X, ⊤)` IS AN ISOMORPHISM FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY
CONNECTED AND REDUCED FIBRES**, over an arbitrary base — **PROVEN** over the affine-base leaf
`isIso_appTop_of_isProper_of_flat_of_isAffine` above.

The base is made affine by `isIso_appTop_of_isIso_app_affineOpens`: `f.app U` is the component
at `U` of the sheaf map `𝒪_S ⟶ f_*𝒪_X`, so it is enough to treat the affine opens, which are a
basis of `S`.  Over an affine open `U`, `isPullback_morphismRestrict` exhibits `f ∣_ U` as a
base change of `f`, so it inherits all five hypotheses, and `morphismRestrict_appTop` together
with `Scheme.Opens.ι_image_top` identifies `(f ∣_ U).appTop` with `f.app U` up to the
`eqToHom`-induced isomorphism.

So the affine reduction and the `universally`/`∀ U` bookkeeping of
`hasUniversallyTrivialPushforward_of_isProper_of_flat` below are all discharged mechanically:
the only remaining mathematics is the global-sections computation over an **affine** base. -/
theorem isIso_appTop_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    IsIso f.appTop := by
  refine isIso_appTop_of_isIso_app_affineOpens f fun U hU => ?_
  haveI : IsAffine U := hU
  haveI : IsProper (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹IsProper f›
  haveI : Flat (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip ‹Flat f›
  haveI : LocallyOfFinitePresentation (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹LocallyOfFinitePresentation f›
  haveI : GeometricallyConnected (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹GeometricallyConnected f›
  haveI : GeometricallyReduced (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      ‹GeometricallyReduced f›
  haveI hiso : IsIso (f.app (U.ι ''ᵁ ⊤) ≫
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) := by
    rw [← morphismRestrict_appTop]
    exact isIso_appTop_of_isProper_of_flat_of_isAffine (f ∣_ U)
  haveI h2 := (isIso_comp_right_iff _ _).mp hiso
  rwa [U.ι_image_top] at h2

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

/-- **THE COVERING STEP OF THE RIGIDITY LEMMA** (sorry node) — the whole topological content,
and the ONLY place where `σ`, `hconst` and `[GeometricallyConnected q]` are used.

The assertion is that `Y` is covered by opens `V i` over each of which `m` factors through a
scheme `W i` that is **affine over the base**, in the sense that `V i ×_S W i` is an affine
scheme.  Given that, `exists_comp_snd_eq_of_isAffine_pullback` factors `m` over each `V i`,
and `exists_comp_snd_eq_of_open_cover` glues.

**The proof** (Mumford *AV* §4; BLR 8.4).  Fix `s ∈ S`, an affine open `S₀ ⊆ S` around it,
and an affine open `U ⊆ Z` with `c(S₀) ⊆ U` and `r(U) ⊆ S₀`.  Then `m ⁻¹(Z ∖ U)` is closed
in `X ×_S Y`, and `pullback.snd p q` is proper (base change of `p`), hence a closed map, so
its image is closed in `Y` and — by `hconst`, which puts the slice `σ(S)` into `U` — misses
`σ(S₀)`.  The complement is an open `V ∋ σ(s)` over which `m` lands in `U`; refine `V` to an
affine open inside `q ⁻¹ S₀` and take `W = U`, so that `V ×_S W = V ×_{S₀} U` is a fibre
product of affines over an affine, hence affine.

**Where the connectedness is consumed, and why the leaf is FALSE without it**: the opens
produced this way a priori cover only the part of `Y` reachable from the section.  Their
union is open, and the argument above run at every point of it shows it is also closed in
each fibre of `q`; `[GeometricallyConnected q]` is what upgrades "clopen in each fibre and
meets each fibre (via `σ`)" to `⨆ i, V i = ⊤`.  With `Y` two points over `S = Spec k` the
union is a single point and the conclusion fails — see the FAITHFULNESS NOTE in the module
docstring.

**AXIS SEARCHED**: the affine and affine-over-the-base cases are DONE and are not what is
missing here (`exists_comp_snd_eq_of_isAffine`, `exists_comp_snd_eq_of_isAffine_pullback`);
so is the `Γ ⊣ Spec` corollary.  What is missing is purely the scheme-theoretic topology:
`IsProper → IsClosedMap` for the base-changed projection, and the `GeometricallyConnected`
clopen argument.  The étale axis (`section_eq_of_formallyUnramified`, diagonal
simultaneously open and closed) is searched and DEAD: `Δ_{B/S}` is an open immersion iff
`Ω_{B/S} = 0`, which fails in relative dimension `> 0`. -/
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
      (∀ i, n i ≫ j i = sliceOverOpen p q (V i) ≫ m) :=
  sorry

/-- **THE GLUING STEP OF THE RIGIDITY LEMMA** (sorry node): local factorizations of `m`
through the projection, over an open cover of `Y`, glue to a global one.

**The proof.**  The local data `d i : V i ⟶ Z` agree on overlaps because the factorization
is UNIQUE: over `V i ⊓ V j`, two factorizations of the same morphism through the projection
agree after composing with the projection, and `HasUniversallyTrivialPushforward p`
base-changes to make that projection an epimorphism — concretely, both restrict over each
affine open of `Z` to the situation of `exists_comp_snd_eq_of_isAffine`, whose conclusion is
an `∃!`.  Then `Scheme.OpenCover.glueMorphisms` on the cover `V` of `Y` produces `d`, and
`m = pullback.snd p q ≫ d` is checked on the cover of `X ×_S Y` by the
`pullback.snd p q ⁻¹ᵁ V i`.

This is bookkeeping rather than mathematics, but it is not free: it is the reason
`exists_comp_snd_eq_of_isAffine` is stated as an `∃!` rather than an `∃`. -/
theorem exists_comp_snd_eq_of_open_cover {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    {ι : Type u} (V : ι → Y.Opens) (hV : (⨆ i, V i) = ⊤)
    (hd : ∀ i, ∃ d : (V i).toScheme ⟶ Z,
      sliceOverOpen p q (V i) ≫ m = pullback.snd p ((V i).ι ≫ q) ≫ d) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d :=
  sorry

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

The concrete obstruction the earlier audit named is still worth recording, because it is
what those two leaves have to get past: the reduction to an affine target cannot be done
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
