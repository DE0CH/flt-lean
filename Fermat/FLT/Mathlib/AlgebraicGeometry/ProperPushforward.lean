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

**That absence claim is about POSITIVE degree only, and a 2026-07-28 re-check narrowed it.**
In degree zero `Mathlib` *does* have flat base change, as `pushoutSection` and
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` in
`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`, which give
`Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(T, ⊤) ≅ Γ(X ×_S T, ⊤)` for `X` qcqs over an affine base and `T ⟶ S` flat.
That is what closed the whole fibrewise half of this file.  Anyone reading the paragraph above
as "no base change of any kind exists" will rebuild machinery that is already here — the grep to
run is for `pushoutSection`, not for `directImage`.

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
* `isIso_appTop_of_isProper_over_field` — **PROVEN, no leaf under it** (2026-07-28):
  `H⁰(Z, 𝒪_Z) = K` for `Z` proper, geometrically connected and geometrically reduced over a field
  `K`.  **Its hypothesis was `[Field K]`, which made the statement FALSE** — for
  `K : CommRingCat` that binder is a field structure on the carrier *type*, unrelated to `K`'s
  ring structure; see the falsity audit on the declaration for the `ZMod 4` counterexample.  It
  now carries `hK : IsField K`.  Proven en route, and useful on their own:
  * `exists_eq_sq_mul_of_isIntegral` — a reduced ring is von Neumann regular at every element
    integral over a field;
  * `isField_of_isIntegral_of_forall_isIdempotentElem` — hence such a ring with no nontrivial
    idempotents is a field, with **no finiteness and no irreducibility**, which is what
    `Mathlib`'s `isField_of_universallyClosed` needs `[IsIntegral X]` for;
  * `isIdempotentElem_appTop_eq_zero_or_one` — `Γ` of a connected reduced scheme has no
    nontrivial idempotents;
  * `isField_appTop_of_universallyClosed` and
    `isIso_appTop_of_universallyClosed_of_isAlgClosed` — `Γ(Z, ⊤)` is a field, and equals `K`
    when `K` is algebraically closed.
* `isIso_appTop_of_isIso_appTop_baseChange` — **PROVEN** (2026-07-28): flat base change for `H⁰`
  along a field extension, in transfer form.  **Contrary to what this docstring used to say,
  `Mathlib` HAS the base-change machinery for global sections** —
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` in
  `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` gives
  `Γ(Z, ⊤) ⊗_K L ≅ Γ(Z ×_K Spec L, ⊤)` directly.  What `Mathlib` lacks is *higher* direct
  images, which is a different statement; the note below about "zero hits" is about those.
  Supporting lemmas, both PROVEN: `isIso_of_isPushout_of_isField` (faithfully flat descent of
  isomorphisms along a field extension, in pushout form) and
  `bijective_algebraMap_of_bijective_includeLeft` (a `K`-algebra whose base change to `L` is `L`
  is `K`).
* `isIso_appTop_of_isIso_appTop_fiber` — **LEAF** (2026-07-27): degree-zero cohomology and
  base change.  For `f` proper, flat and of finite presentation over an **affine** base,
  `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is an isomorphism as soon as `κ(s) ⟶ Γ(X_s, ⊤)` is one for every
  `s ∈ S`.  Geometric connectedness and reducedness do not appear: they enter only through
  the fibrewise hypothesis.  This is the genuine theory build.
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

/-! ### The two halves: the fibrewise computation, and cohomology and base change

The classical proof of `f_*𝒪_X = 𝒪_S` has exactly two moving parts, and they are independent
of one another:

* **over a field** — `H⁰(Z, 𝒪_Z) = K` for `Z` proper, geometrically connected and
  geometrically reduced over `K` (`isIso_appTop_of_isProper_over_field`).  No flatness and no
  cohomology in positive degree; this half is **DONE** (2026-07-28), and its only base change
  is the harmless one to `K̄`, which `Mathlib`'s flat-base-change API for `Γ` supplies;
* **cohomology and base change** — for `f` proper, flat and of finite presentation over an
  affine base, `𝒪_S ⟶ f_*𝒪_X` is an isomorphism as soon as it is one on every fibre
  (`isIso_appTop_of_isIso_appTop_fiber`).  This half never sees geometric connectedness or
  reducedness: they enter *only* through the fibrewise hypothesis.  It is the **one remaining
  leaf** of the pushforward theorem, and it is a genuine theory build: unlike degree zero, it
  needs `Rⁱf_*` and semicontinuity, which `Mathlib` does not have.

`isIso_appTop_of_isProper_of_flat_of_isAffine` is PROVEN by feeding the first into the second,
which is why the two are cut apart here rather than proved together. -/

/-! #### The fibrewise half: `H⁰(Z, 𝒪_Z) = K`

The route actually taken here is **shorter than the classical five-step one** recorded in earlier
versions of this docstring, and in particular it never needs `Γ(Z, ⊤)` to be *finite* over `K`,
nor `Z` to be irreducible.  It is:

1. `K ⟶ A := Γ(Z, ⊤)` is **integral** — `isIntegral_appTop_of_universallyClosed`, free from
   `Mathlib`, and the only place properness is used.
2. `A` is **reduced** (`Z` is), and has **no nontrivial idempotents** (`Z` is connected):
   an idempotent `e` splits `Z` into the two disjoint opens `Z.basicOpen e` and
   `Z.basicOpen (1 - e)`, which cover because an idempotent of a *local* ring is `0` or `1`
   (`IsLocalRing.isUnit_or_isUnit_one_sub_self`).
3. Hence `A` is a **field**: a reduced ring is *von Neumann regular* at every element integral
   over a field (`exists_eq_sq_mul_of_isIntegral`), so `a = a²t`, `at` is idempotent, and
   `at = 1` is the inverse.  This replaces the classical "`K[a]` is a finite reduced algebra,
   hence a product of fields" and needs no finiteness.
4. Over an **algebraically closed** field this already finishes: a field integral over an
   algebraically closed field *is* that field
   (`IsAlgClosed.ringHom_bijective_of_isIntegral`).  That is
   `isIso_appTop_of_universallyClosed_of_isAlgClosed`.
5. The general case is reduced to (4) by base-changing to `K̄`, which is where the geometric
   hypotheses are consumed and where the one remaining leaf sits.
-/

open Polynomial in
/-- The inductive step of `exists_eq_sq_mul_of_isIntegral`: if `a^k * (a * d + c) = 0` with `c`
a nonzero scalar, then `a = a² t`.

Reducedness turns `a ^ k * b = 0` into `a * b = 0` — because `(a * b) ^ (k + 1)
= a * (a ^ k * b) * b ^ k = 0` — and `a * (a * d + c) = 0` is `a² d + a c = 0`, which is
`a = a² * (-(d / c))` after dividing by the unit `c`. -/
theorem exists_eq_sq_mul_of_pow_mul_add_eq_zero {K A : Type*} [Field K] [CommRing A]
    [_root_.IsReduced A] [Algebra K A] {a d : A} {c : K} (hc : c ≠ 0) {k : ℕ}
    (h : a ^ k * (a * d + algebraMap K A c) = 0) : ∃ t : A, a = a ^ 2 * t := by
  set b : A := a * d + algebraMap K A c with hb
  have hnil : IsNilpotent (a * b) := by
    refine ⟨k + 1, ?_⟩
    have hpow : (a * b) ^ (k + 1) = a ^ k * b * (a * b ^ k) := by
      rw [mul_pow, pow_succ, pow_succ]; ring
    rw [h, zero_mul] at hpow
    exact hpow
  have hab : a * b = 0 := hnil.eq_zero
  refine ⟨-(d * algebraMap K A c⁻¹), ?_⟩
  have hcinv : algebraMap K A c * algebraMap K A c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hexp : a ^ 2 * d + a * algebraMap K A c = 0 := by rw [← hab, hb]; ring
  have h2 : a * (algebraMap K A c * algebraMap K A c⁻¹) = a ^ 2 * -(d * algebraMap K A c⁻¹) := by
    have hmul := congrArg (· * algebraMap K A c⁻¹) hexp
    simp only [zero_mul, add_mul] at hmul
    linear_combination hmul
  rwa [hcinv, mul_one] at h2

open Polynomial in
/-- **A REDUCED RING IS VON NEUMANN REGULAR AT EVERY ELEMENT INTEGRAL OVER A FIELD** (PROVEN):
if `A` is reduced and `a : A` is integral over a field `K`, then `a = a² t` for some `t : A`.

This is the elementary substitute for "a finite reduced algebra over a field is a product of
fields", and it is what makes `isField_of_isIntegral_of_forall_isIdempotentElem` need no
finiteness hypothesis at all.

**Proof.**  Induct on `p.natDegree` for a monic `p` killing `a`, in the strengthened form
"`a ^ k * p(a) = 0` for some `k`".  If `p.coeff 0 ≠ 0`, write `p = X * p.divX + C (p.coeff 0)`
and apply `exists_eq_sq_mul_of_pow_mul_add_eq_zero`.  If `p.coeff 0 = 0`, then `p = X * p.divX`,
so `a ^ (k + 1) * p.divX(a) = 0` and `p.divX` has smaller degree.  The two cases are exhaustive
because a nonzero polynomial of degree `0` is a nonzero constant. -/
theorem exists_eq_sq_mul_of_isIntegral {K A : Type*} [Field K] [CommRing A] [_root_.IsReduced A]
    [Algebra K A] {a : A} (ha : _root_.IsIntegral K a) : ∃ t : A, a = a ^ 2 * t := by
  suffices H : ∀ n : ℕ, ∀ p : K[X], p.natDegree ≤ n → p ≠ 0 → ∀ k : ℕ,
      a ^ k * aeval a p = 0 → ∃ t : A, a = a ^ 2 * t by
    obtain ⟨p, hmonic, hp⟩ := ha
    refine H p.natDegree p le_rfl hmonic.ne_zero 0 ?_
    simpa [aeval_def] using hp
  intro n
  induction n with
  | zero =>
    intro p hpn hp k hk
    have hpc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hpn)
    have hc : p.coeff 0 ≠ 0 := fun h => hp (by rw [hpc, h, map_zero])
    refine exists_eq_sq_mul_of_pow_mul_add_eq_zero (a := a) (d := 0) hc (k := k) ?_
    rw [mul_zero, zero_add]
    rw [hpc] at hk
    simpa using hk
  | succ n ih =>
    intro p hpn hp k hk
    by_cases hc : p.coeff 0 = 0
    · have hX : X * p.divX = p := by
        have hd := Polynomial.X_mul_divX_add p
        rwa [hc, map_zero, add_zero] at hd
      have hdiv : p.divX ≠ 0 := fun h => hp (by rw [← hX, h, mul_zero])
      have hdeg : p.divX.natDegree ≤ n := by
        have hnd : p.divX.natDegree = p.natDegree - 1 :=
          Polynomial.natDegree_divX_eq_natDegree_tsub_one
        omega
      refine ih p.divX hdeg hdiv (k + 1) ?_
      have key : a ^ (k + 1) * aeval a p.divX = a ^ k * aeval a p := by
        conv_rhs => rw [← hX]
        rw [map_mul, aeval_X]; ring
      rw [key]; exact hk
    · refine exists_eq_sq_mul_of_pow_mul_add_eq_zero (a := a) (d := aeval a p.divX) hc (k := k) ?_
      have hsplit : aeval a p = a * aeval a p.divX + algebraMap K A (p.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add p]
        rw [map_add, map_mul, aeval_X, aeval_C]
      rwa [← hsplit]

/-- **A REDUCED RING INTEGRAL OVER A FIELD WITH NO NONTRIVIAL IDEMPOTENTS IS A FIELD** (PROVEN).

Note what is *absent*: no finiteness, no irreducibility, no Noetherian hypothesis.  Von Neumann
regularity (`exists_eq_sq_mul_of_isIntegral`) gives `a = a² t`; then `a * t` is idempotent, so it
is `0` or `1`; it cannot be `0` (that forces `a = a * (a * t) = 0`), so `t` inverts `a`. -/
theorem isField_of_isIntegral_of_forall_isIdempotentElem {K A : Type*} [Field K] [CommRing A]
    [Nontrivial A] [_root_.IsReduced A] [Algebra K A] [Algebra.IsIntegral K A]
    (hidem : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) : IsField A := by
  refine ⟨exists_pair_ne A, mul_comm, ?_⟩
  intro a ha
  obtain ⟨t, ht⟩ := exists_eq_sq_mul_of_isIntegral (K := K) (Algebra.IsIntegral.isIntegral a)
  have he : IsIdempotentElem (a * t) := by
    unfold IsIdempotentElem
    calc a * t * (a * t) = a ^ 2 * t * t := by ring
      _ = a * t := by rw [← ht]
  rcases hidem _ he with h | h
  · exact absurd (by rw [ht, show a ^ 2 * t = a * (a * t) by ring, h, mul_zero]) ha
  · exact ⟨t, h⟩

/-- **`Γ(Z, ⊤)` HAS NO NONTRIVIAL IDEMPOTENTS FOR A CONNECTED REDUCED SCHEME** (PROVEN).

An idempotent `e` gives two opens `Z.basicOpen e` and `Z.basicOpen (1 - e)` which are *disjoint*
(`e * (1 - e) = 0`, and `Z.basicOpen 0 = ⊥`) and *cover* `Z` (in the local ring at any point,
`IsLocalRing.isUnit_or_isUnit_one_sub_self` makes `e` or `1 - e` a unit).  So `Z.basicOpen e` is
clopen; connectedness makes it `⊥` or `⊤`, and reducedness turns that into `e = 0` or `e = 1`
via `basicOpen_eq_bot_iff`.

Reducedness is genuinely needed: on `Z = Spec (K[ε]/ε²)` the element `ε` has `basicOpen ε = ⊥`
without being zero — though of course `ε` is not idempotent, the *implication*
`basicOpen s = ⊥ → s = 0` is what fails. -/
theorem isIdempotentElem_appTop_eq_zero_or_one {Z : Scheme.{u}} [IsReduced Z]
    [ConnectedSpace Z] {e : Γ(Z, ⊤)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have hdisj : Z.basicOpen e ⊓ Z.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, hmul, Scheme.basicOpen_zero]
  have hcover : Z.basicOpen e ⊔ Z.basicOpen (1 - e) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
        ((Z.presheaf.germ ⊤ x trivial) e) with h | h
    · exact Or.inl ((Z.mem_basicOpen_top e x).mpr h)
    · exact Or.inr ((Z.mem_basicOpen_top (1 - e) x).mpr (by simpa using h))
  have hclopen : IsClopen (Z.basicOpen e : Set Z) := by
    refine ⟨?_, (Z.basicOpen e).isOpen⟩
    have hcompl : (Z.basicOpen e : Set Z)ᶜ = (Z.basicOpen (1 - e) : Set Z) := by
      refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx hx' => ?_)
      · have hx' : x ∈ (⊤ : Z.Opens) := trivial
        rw [← hcover] at hx'
        exact hx'.resolve_left hx
      · have hmem : x ∈ Z.basicOpen e ⊓ Z.basicOpen (1 - e) := ⟨hx', hx⟩
        rw [hdisj] at hmem
        exact hmem
    rw [← isOpen_compl_iff, hcompl]
    exact (Z.basicOpen (1 - e)).isOpen
  rcases _root_.isClopen_iff.mp hclopen with h | h
  · exact Or.inl ((basicOpen_eq_bot_iff e).mp (by ext x; simp [h]))
  · refine Or.inr ?_
    have h1 : Z.basicOpen (1 - e) = ⊥ := by
      have htop : Z.basicOpen e = ⊤ := by ext x; simp [h]
      rw [htop, top_inf_eq] at hdisj
      exact hdisj
    exact (sub_eq_zero.mp ((basicOpen_eq_bot_iff (1 - e)).mp h1)).symm

/-- **`Γ(Z, ⊤)` IS A FIELD FOR A CONNECTED REDUCED SCHEME UNIVERSALLY CLOSED OVER A FIELD**
(PROVEN) — steps 1–3 of the route above, and the sharpening of `Mathlib`'s
`isField_of_universallyClosed`, which assumes `[IsIntegral Z]`.

Irreducibility really is dropped, not hidden: two lines meeting in a point are connected and
reduced but not irreducible, and they do have `H⁰ = k`. -/
theorem isField_appTop_of_universallyClosed {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [UniversallyClosed g] [IsReduced Z] [ConnectedSpace Z] :
    IsField Γ(Z, ⊤) := by
  let F : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed g
  algebraize [F.hom]
  haveI : Nonempty ↥(⊤ : Z.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  haveI : Nontrivial Γ(Z, ⊤) := LocallyRingedSpace.component_nontrivial Z.toLocallyRingedSpace ⊤
  exact isField_of_isIntegral_of_forall_isIdempotentElem (K := K)
    (fun e he => isIdempotentElem_appTop_eq_zero_or_one he)

/-- **`H⁰(Z, 𝒪_Z) = K` OVER AN ALGEBRAICALLY CLOSED FIELD** (PROVEN) — step 4.

`Γ(Z, ⊤)` is a field by `isField_appTop_of_universallyClosed`, hence a domain, and it is integral
over `K`; `IsAlgClosed.ringHom_bijective_of_isIntegral` then says the structure map is bijective.

No geometric connectedness or geometric reducedness appears, because over an algebraically closed
field ordinary connectedness and ordinary reducedness *are* the geometric notions. -/
theorem isIso_appTop_of_universallyClosed_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of K)) [UniversallyClosed g] [IsReduced Z]
    [ConnectedSpace Z] : IsIso g.appTop := by
  let F : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ g.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed g
  letI : Field ↥Γ(Z, ⊤) := (isField_appTop_of_universallyClosed g).toField
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).mpr
    (IsAlgClosed.ringHom_bijective_of_isIntegral F.hom hF)
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ F = g.appTop := by simp [F]
  rw [← hcomp]
  infer_instance

/-! #### Descent from `K̄` to `K`: flat base change for `H⁰`

Contrary to what an earlier version of this file's docstring asserted, `Mathlib` **does** carry
the base-change machinery for global sections, in
`Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`: for a cartesian square

```
Y --g--→ X
|        |
iY       iX
↓        ↓
T --f--→ S
```

`AlgebraicGeometry.pushoutSection` is the canonical map
`Γ(X, Uₓ) ⊗_{Γ(S, Uₛ)} Γ(T, Uₜ) ⟶ Γ(Y, Uy)`, and
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` makes it an isomorphism when `Uₛ`, `Uₜ`
are affine, `Uₓ` is quasi-compact and quasi-separated, and `f` is flat.  Instantiated at
`S = Spec K`, `T = Spec L`, `X = Z` with all opens `⊤`, that is exactly `Γ(Z_L, ⊤) =
Γ(Z, ⊤) ⊗_K L`, and the descent is then a one-line dimension count.  What was absent from
`Mathlib` is higher direct images, not this.
-/

open TensorProduct in
/-- **A `K`-ALGEBRA WHOSE BASE CHANGE TO `L` IS `L` IS `K`** (PROVEN) — the dimension count that
turns flat base change for `H⁰` into the descent.

If `L ⟶ L ⊗_K A` is bijective then `L ⊗_K A` has `L`-rank one, so `A` has `K`-rank one by
`Module.rank_baseChange`, and a unital `K`-algebra of rank one is `K`.  Note `A` is not assumed
nontrivial: that follows, because rank one is not rank zero. -/
theorem bijective_algebraMap_of_bijective_includeLeft {R A L : Type u} [Field R] [CommRing A]
    [Field L] [Algebra R A] [Algebra R L]
    (hbij : Function.Bijective (algebraMap L (L ⊗[R] A))) :
    Function.Bijective (algebraMap R A) := by
  have h1 : Module.rank L (L ⊗[R] A) = 1 := by
    have e : L ≃ₗ[L] (L ⊗[R] A) :=
      (AlgEquiv.ofBijective (Algebra.ofId L (L ⊗[R] A)) hbij).toLinearEquiv
    rw [← e.rank_eq, CommSemiring.rank_self]
  have h2 : Module.rank R A = 1 := by
    have hbc := Module.rank_baseChange (R := L) (S := R) (M' := A)
    rw [h1] at hbc
    simpa using hbc.symm
  haveI : Nontrivial A := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rw [rank_subsingleton'] at h2
    exact zero_ne_one h2
  refine ⟨(algebraMap R A).injective, ?_⟩
  intro w
  have hfr : Module.finrank R A = 1 := Module.rank_eq_one_iff_finrank_eq_one.mp h2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : A) one_ne_zero).mp hfr w
  exact ⟨c, by simpa [Algebra.smul_def] using hc⟩

open TensorProduct in
/-- **FAITHFULLY FLAT DESCENT OF ISOMORPHISMS ALONG A FIELD EXTENSION, IN PUSHOUT FORM** (PROVEN).

In a pushout square of commutative rings whose top-left corner `R` and lower-left corner `L` are
fields, the right-hand leg `δ : L ⟶ Y` being an isomorphism forces the left-hand leg
`α : R ⟶ A` to be one.

The proof does not invoke faithful flatness abstractly: the pushout is identified with
`L ⊗_R A` by `CommRingCat.isPushout_tensorProduct` (two pushouts over the same span are uniquely
isomorphic, and `IsPushout.inl_isoPushout_hom` says the identification carries `δ` to
`includeLeft`), and then `bijective_algebraMap_of_bijective_includeLeft` counts dimensions. -/
theorem isIso_of_isPushout_of_isField {R A L Y : CommRingCat.{u}} (hR : IsField R) (hL : IsField L)
    {α : R ⟶ A} {β : R ⟶ L} {γ : A ⟶ Y} {δ : L ⟶ Y}
    (hpo : IsPushout α β γ δ) [IsIso δ] : IsIso α := by
  letI : Field ↥R := hR.toField
  letI : Field ↥L := hL.toField
  algebraize [α.hom, β.hom]
  have hT : IsPushout β α
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A)))
      (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := ↥R) (A := ↥L) (B := ↥A)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct ↥R ↥L ↥A
  let e : CommRingCat.of (↥L ⊗[↥R] ↥A) ≅ Y := hT.isoPushout ≪≫ hpo.flip.isoPushout.symm
  have hinl : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A)) = δ ≫ e.inv := by
    have h1 := hT.inl_isoPushout_hom
    have h2 := hpo.flip.inl_isoPushout_hom
    simp only [e, Iso.trans_inv, Iso.symm_inv]
    rw [← Category.assoc, h2, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI hiso : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := ↥R) (A := ↥L) (B := ↥A))) := by
    rw [hinl]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective α).mpr
    (bijective_algebraMap_of_bijective_includeLeft
      ((ConcreteCategory.isIso_iff_bijective _).mp hiso))

/-- `f.appLE ⊤ ⊤` differs from `f.appTop` only by the restriction along `⊤ = f ⁻¹ᵁ ⊤`, which is
an isomorphism because `Opens` is a poset. -/
theorem isIso_appLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    IsIso (f.appLE ⊤ ⊤ e) ↔ IsIso f.appTop := by
  haveI : IsIso (homOfLE e) := ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rw [Scheme.Hom.appLE]
  exact isIso_comp_right_iff _ _

/-- **`Γ` COMMUTES WITH BASE FIELD EXTENSION, IN THE FORM THE DESCENT NEEDS** (PROVEN,
2026-07-28): if `Γ(Spec L, ⊤) ⟶ Γ(Z ×_{Spec K} Spec L, ⊤)` is an isomorphism, so is
`Γ(Spec K, ⊤) ⟶ Γ(Z, ⊤)`.

**The content.**  For `Z` quasi-compact and quasi-separated over a field `K` and any field
extension `L/K`, the canonical map `Γ(Z, ⊤) ⊗_K L ⟶ Γ(Z ×_{Spec K} Spec L, ⊤)` is bijective —
flat base change for `H⁰`, which is the *equalizer* of a finite Čech diagram of affines together
with the exactness of `- ⊗_K L`, not the full cohomology-and-base-change theorem.  That is
supplied by `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`; `Spec.map φ` is flat
because `K` is a field, and `Z` is quasi-compact and quasi-separated because `g` is and the base
is affine.  `isIso_pushoutSection_iff` turns it into an `IsPushout` square of rings, and
`isIso_of_isPushout_of_isField` descends the isomorphism.

**FAITHFULNESS.**  Both fields are load-bearing: `hK` is what makes `L` flat over `K` (so the
base change computes `Γ` at all), and `hL` is what makes "rank one over `L`" meaningful.  The
empty scheme is not a counterexample — there `Γ(Z, ⊤) = 0 = Γ(Z_L, ⊤)` and the hypothesis fails,
since a field never maps isomorphically to the zero ring. -/
theorem isIso_appTop_of_isIso_appTop_baseChange {K L : CommRingCat.{u}}
    (hK : IsField K) (hL : IsField L) (φ : K ⟶ L) {Z : Scheme.{u}} (g : Z ⟶ Spec K)
    [QuasiCompact g] [QuasiSeparated g]
    (h : IsIso (pullback.snd g (Spec.map φ)).appTop) : IsIso g.appTop := by
  letI : Field ↥K := hK.toField
  letI : Field ↥L := hL.toField
  haveI : Flat (Spec.map φ) := by
    rw [Flat.SpecMap_iff]
    letI := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat ↥K ↥L)
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace g).mp inferInstance
  haveI : QuasiSeparatedSpace Z := (quasiSeparated_iff_quasiSeparatedSpace g).mp inferInstance
  have H : IsPullback (pullback.fst g (Spec.map φ)) (pullback.snd g (Spec.map φ)) g
      (Spec.map φ) := IsPullback.of_hasPullback _ _
  have hpo := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right (H := H)
    (hUST := (le_top : (⊤ : (Spec L).Opens) ≤ _)) (hUSX := (le_top : (⊤ : Z.Opens) ≤ _))
    (hUY := (by simp : (⊤ : (pullback g (Spec.map φ)).Opens) = _))
    (isAffineOpen_top _) (isAffineOpen_top _) (by simpa using isCompact_univ (X := Z))
    (by simpa using isQuasiSeparated_univ (α := Z))
  rw [isIso_pushoutSection_iff] at hpo
  haveI : IsIso ((pullback.snd g (Spec.map φ)).appLE ⊤ ⊤ (by simp)) :=
    (isIso_appLE_top_iff _ _).mpr h
  refine (isIso_appLE_top_iff g (by simp)).mp ?_
  exact isIso_of_isPushout_of_isField
    ((Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv.isField hK)
    ((Scheme.ΓSpecIso L).commRingCatIsoToRingEquiv.toMulEquiv.isField hL) hpo

/-- **`H⁰(Z, 𝒪_Z) = K` FOR A PROPER, GEOMETRICALLY CONNECTED, GEOMETRICALLY REDUCED SCHEME
OVER A FIELD** — the fibrewise half of the pushforward theorem, **PROVEN** (2026-07-28), with no
leaf left under it.

**FALSITY AUDIT AND REPAIR (2026-07-28) — the hypothesis used to be `[Field K]` and that made
the statement FALSE.**  With `K : CommRingCat`, the binder `[Field K]` elaborates as
`Field ↥K`: a field structure on the *carrier type* of `K`, whose ring operations are a fresh
structure field and are **provably unrelated** to `K`'s own ring structure — the compiler reports
the two `CommSemiring ↥K` instance paths (`CommRing.toCommSemiring` from `CommRingCat` versus
`Field.toSemifield.toCommSemiring`) as not even definitionally equal.  So `[Field K]` did not say
"`K` is a field"; it said "the carrier of `K` happens to be in bijection with some field", which
is a condition on a *type*, not on a ring.

Explicit counterexample to the old statement: `K = CommRingCat.of (ZMod 4)`, `Z = Spec (ZMod 2)`,
`g` the closed immersion induced by `ZMod 4 ↠ ZMod 2`.  Then `g` is finite, hence proper; every
field-valued point of `Spec (ZMod 4)` kills the nilpotent `2`, so every base change of `g` to a
field is an isomorphism, making `g` geometrically connected and geometrically reduced; and
`g.appTop : ZMod 4 ⟶ ZMod 2` is not an isomorphism.  The old hypothesis `[Field ↥K]` is
satisfied because `↥K` is a four-element type, and a four-element type carries a field structure
(`𝔽₄`).

The repair is the honest hypothesis `hK : IsField K`, which is stated with respect to `K`'s own
semiring structure and therefore cannot be satisfied spuriously.  The consumer supplies it with
`Field.toIsField`, so nothing downstream got harder.

**The proof.**  Base-change to `K̄`: the pullback is proper, reduced and connected (this is
exactly what `GeometricallyReduced` and `GeometricallyConnected` say), so
`isIso_appTop_of_universallyClosed_of_isAlgClosed` computes its global sections, and
`isIso_appTop_of_isIso_appTop_baseChange` descends that to `K`.

**FAITHFULNESS.**  All three hypotheses are load-bearing.  Without geometric connectedness the
statement fails for `Z = Spec (K × K)`; without geometric reducedness it fails for
`Z = Spec (K[ε]/ε²)`; and *geometric* connectedness cannot be weakened to connectedness — for
`K = ℝ` and `Z = Spec ℂ`, `Z` is connected, reduced and proper over `ℝ`, and
`H⁰(Z, 𝒪) = ℂ ≠ ℝ`.  Likewise geometric reducedness cannot be weakened to reducedness, by the
usual inseparable example `Z = Spec 𝔽_p(t^{1/p})` over `K = 𝔽_p(t)`.  Note that the first two
are already invisible to steps 1–4: `Γ` of `Spec (K × K)` is a nontrivial idempotent, and `Γ` of
`Spec (K[ε]/ε²)` is not reduced. -/
theorem isIso_appTop_of_isProper_over_field {K : CommRingCat.{u}} (hK : IsField K)
    {Z : Scheme.{u}} (g : Z ⟶ Spec K) [IsProper g] [GeometricallyConnected g]
    [GeometricallyReduced g] : IsIso g.appTop := by
  letI : Field ↥K := hK.toField
  let φ : K ⟶ CommRingCat.of (AlgebraicClosure ↥K) :=
    CommRingCat.ofHom (algebraMap ↥K (AlgebraicClosure ↥K))
  refine isIso_appTop_of_isIso_appTop_baseChange hK (Field.toIsField _) φ g ?_
  haveI : UniversallyClosed (pullback.snd g (Spec.map φ)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsReduced (pullback g (Spec.map φ)) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  haveI : ConnectedSpace ↥(pullback g (Spec.map φ)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  exact isIso_appTop_of_universallyClosed_of_isAlgClosed (K := AlgebraicClosure ↥K) _

/-- **COHOMOLOGY AND BASE CHANGE IN DEGREE ZERO: `𝒪_S ⟶ f_*𝒪_X` IS AN ISOMORPHISM AS SOON AS
IT IS ONE ON EVERY FIBRE** (LEAF, 2026-07-27; Hartshorne III.12.11, Grauert, Stacks 0E0L /
EGA III 7.8.6) — the half of the pushforward theorem that is a genuine theory build.

Note what is *not* here: no geometric connectedness, no geometric reducedness.  Those enter
only through the hypothesis `h`, discharged by `isIso_appTop_of_isProper_over_field` above.
What is left is exactly the classical cohomology-and-base-change statement, with the fibre
input abstracted away.

**THE ROUTE, in the vocabulary `[IsAffine S]` provides.**  Put `R := Γ(S, ⊤)`,
`A := Γ(X, ⊤)`, `φ := f.appTop : R ⟶ A`.  Three inputs give `φ` bijective:

1. *`A` is a finitely presented `R`-module* — properness plus local finite presentation.
   Mathlib gives the weaker `isIntegral_appTop_of_universallyClosed` (`R ⟶ A` is integral) for
   free, but not finiteness.
2. *`A` is `R`-flat* — this is where `Flat f` enters, through cohomology and base change:
   `f_*𝒪_X` is locally free with formation commuting with base change (Grauert).
3. *For every maximal ideal `m ⊂ R`, `R/m ⟶ A/mA` is bijective* — degree-zero base change
   identifies `A/mA` with `Γ(X_s, ⊤)` for the point `s` cut out by `m`, and `κ(s) = R/m`, so
   this is precisely the hypothesis `h s`.

Given those, `φ` is surjective by Nakayama applied to `coker φ` (finitely generated, and zero
modulo every maximal ideal), and then injective because flatness of `A` keeps
`0 ⟶ ker φ ⟶ R ⟶ A ⟶ 0` exact after `- ⊗_R R/m`, forcing `ker φ = m · ker φ` for every
maximal `m`, with `ker φ` finitely generated by `Module.FinitePresentation.fg_ker`.

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
Fermat/` returns zero hits.  So this leaf is a theory build and not a missing-lemma hunt.
What mathlib *does* supply, and what an earlier version of this docstring did not record, is
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`,
`AlgebraicGeometry.isField_of_universallyClosed` and
`AlgebraicGeometry.finite_appTop_of_universallyClosed`
(`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`) — the last two under `[IsIntegral X]`. -/
theorem isIso_appTop_of_isIso_appTop_fiber (f : X ⟶ S) [IsAffine S]
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop) :
    IsIso f.appTop :=
  sorry

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
  exact isIso_appTop_of_isProper_over_field (Field.toIsField _) _

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
