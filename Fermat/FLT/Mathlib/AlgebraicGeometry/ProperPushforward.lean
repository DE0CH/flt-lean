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
* `isIso_appTop_of_isIso_appTop_fiber` — **PROVEN** (2026-07-28): degree-zero cohomology and
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
* `exists_isAffineOpen_slice_nbhd_of_slice_const` — **PROVEN** (2026-07-28): at each
  `y : Y` there are an open `V ∋ y` in `Y` and an open `U ⊆ Z` with `V ×_S U` affine and
  `range (X ×_S V ⟶ Z) ⊆ U`.  This is where properness of `pullback.snd`, the section `σ`
  and `[GeometricallyConnected q]` are consumed.  Its properness half is
  `isOpen_setOf_slice_mapsTo` (the tube lemma, PROVEN), its packaging is
  `mem_sliceGoodLocus_of_mem_sliceContractedLocus` (PROVEN), the converse identification
  of the two loci is `sliceContractedLocus_of_sliceGoodLocus` (PROVEN, and the place where
  `hpush` is spent), the base point is `slice_const_of_section` (PROVEN, over
  `isPullback_sliceIncl`: the slice cut out by a section is the base change of that
  section), and the clopen argument is `mem_sliceGoodLocus_of_slice_const` (PROVEN).
* `isClosed_sliceContractedLocus_fiber` — **PROVEN** (2026-07-28): the locus of `y : Y`
  whose slice `m` contracts to a point is CLOSED IN EACH FIBRE of `q`.  This is the
  semicontinuity half, and it closes the rigidity lemma: **the whole cone is now free of
  `sorry` except `isIso_appTop_of_isProper_of_flat`**, which is the pushforward theorem
  itself and has a separate owner.  The mechanism is that the projection away from
  `X ×_S X` is an OPEN map once restricted to a fibre of `q`, because everything there is
  flat over the field `κ(s)`; the input is `Mathlib`'s
  `instance [IsIntegral Y] [Subsingleton Y] : UniversallyOpen f` — *any* morphism to the
  spectrum of a field is universally open — packaged here as
  `universallyOpen_of_isPullback_residueField`.  **No flatness hypothesis on `p` is needed
  or used.**

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

**UPDATE (2026-07-28): THE RIGIDITY LEMMA IS CLOSED.**  `IsProper ⟹ IsClosedMap` for the
base-changed projection is `isOpen_setOf_slice_mapsTo`, the `GeometricallyConnected` clopen
argument is `mem_sliceGoodLocus_of_slice_const`, and
`exists_isAffineOpen_slice_nbhd_of_slice_const` is PROVEN from them.  The step the earlier
notes did not identify is the OTHER half of "clopen": the contracted locus must be closed
in each fibre of `q`.  That is not packaging but genuine geometry — semicontinuity of
"constant along the slice" — and it is proven as
`isClosed_sliceContractedLocus_fiber`, by restricting to the scheme-theoretic fibre, where
the projection away from `X ×_S X` becomes an open map because everything is flat over the
residue FIELD `κ(s)`.

Note the earlier note above got the shape of half (2) wrong, and the error is worth keeping
visible: "running (1) at every point of that locus shows it is also closed in each fibre"
is FALSE — running (1) again gives openness a second time, never closedness.  Closedness is
the semicontinuity statement and needs the flat-over-a-field input; there is no way to get
it out of properness alone.

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
  (`isIso_appTop_of_isIso_appTop_fiber`, now **PROVEN** over three narrower leaves).  This
  half never sees geometric connectedness or reducedness: they enter *only* through the
  fibrewise hypothesis.

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

/-! ### Ranges: the two point-set facts the covering step needs

Everything in this block is PROVEN and axiom-clean.  It is stated here rather than inside
`exists_isAffineOver_cover_of_slice_const` because it is exactly the part of that leaf's
argument that a diagram chase on points CANNOT supply, and because it is reusable:

**the underlying set of a fibre product of schemes is NOT the fibre product of the
underlying sets.**  So "the fibre of `pullback.snd p q` over `σ.base s` is covered by the
slice" — which is what turns `hconst` (a statement about the slice) into a statement about a
whole fibre, and hence what makes `m ⁻¹ (Z ∖ U)` miss that fibre — is a real theorem and not
bookkeeping.  What supplies it is that `sliceIncl` is a BASE CHANGE of `σ`, together with
`Scheme.Pullback.range_map`: the range of a base change is the preimage of the range.

`sliceOverMap` below is `sliceOverOpen` generalised from an open immersion to an arbitrary
morphism, which is needed because the slice is the base change of the SECTION `σ : S ⟶ Y` —
an immersion, but not an open one. -/

/-- **The canonical map `X ×_S V ⟶ X ×_S Y` induced by an arbitrary `g : V ⟶ Y`.**
`sliceOverOpen p q V` is the special case `g = V.ι`, definitionally. -/
noncomputable def sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) : pullback p (g ≫ q) ⟶ pullback p q :=
  pullback.map p (g ≫ q) p q (𝟙 X) g (𝟙 S) (by simp) (by simp)

theorem sliceOverOpen_eq_sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (V : Y.Opens) : sliceOverOpen p q V = sliceOverMap p q V.ι :=
  rfl

@[reassoc (attr := simp)]
theorem sliceOverMap_fst {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    sliceOverMap p q g ≫ pullback.fst p q = pullback.fst p (g ≫ q) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem sliceOverMap_snd {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    sliceOverMap p q g ≫ pullback.snd p q = pullback.snd p (g ≫ q) ≫ g :=
  pullback.lift_snd _ _ _

/-- **THE RANGE OF `sliceOverMap` IS THE PREIMAGE OF THE RANGE OF `g`** (PROVEN), because
`sliceOverMap p q g` is the base change of `g` along `pullback.snd p q`. -/
theorem range_sliceOverMap {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    Set.range (sliceOverMap p q g).base = (pullback.snd p q).base ⁻¹' Set.range g.base := by
  rw [sliceOverMap, Scheme.Pullback.range_map]
  simp

-- (`range_sliceOverOpen` is declared far BELOW, beside `isPullback_sliceOverOpen`.
-- Two branches proved it independently — this position and that one — and the lower
-- copy is the one every consumer in this file `rw`s with, so only it survives.
-- The statement is the same up to the `.base`/coercion spelling.)

section Slice

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)

/-- **The canonical isomorphism `X ≅ X ×_S S` supplied by the section `σ`.**

`σ ≫ q = 𝟙 S` makes `pullback p (σ ≫ q)` a pullback along an identity, hence a copy of `X`.
Composing it with `sliceOverMap p q σ` is `sliceIncl`, which is what exhibits the slice as
the base change of `σ`. -/
noncomputable def sliceIso : X ⟶ pullback p (σ ≫ q) :=
  pullback.lift (𝟙 X) p (by rw [Category.id_comp, hσ, Category.comp_id])

@[reassoc (attr := simp)]
theorem sliceIso_fst : sliceIso p q σ hσ ≫ pullback.fst p (σ ≫ q) = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sliceIso_snd : sliceIso p q σ hσ ≫ pullback.snd p (σ ≫ q) = p :=
  pullback.lift_snd _ _ _

instance : IsIso (sliceIso p q σ hσ) := by
  refine ⟨pullback.fst p (σ ≫ q), sliceIso_fst p q σ hσ, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sliceIso_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, sliceIso_snd, Category.id_comp, pullback.condition, hσ,
      Category.comp_id]

/-- **THE SLICE IS THE BASE CHANGE OF THE SECTION** (PROVEN). -/
theorem sliceIso_comp : sliceIso p q σ hσ ≫ sliceOverMap p q σ = sliceIncl p q σ hσ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, sliceOverMap_fst, sliceIso_fst, sliceIncl_fst]
  · rw [Category.assoc, sliceOverMap_snd, sliceIso_snd_assoc, sliceIncl_snd]

/-! #### **THE SLICE IS EXACTLY THE PART OF `X ×_S Y` LYING OVER `σ(S)`** (PROVEN).

This is the fact the covering step turns on: because the fibre of `pullback.snd p q` over
`σ.base s` is entirely covered by the slice, `hconst` — which constrains `m` only on the
slice — pins `m` on that whole fibre, and so the closed set `m ⁻¹ (Z ∖ U)` misses it.

It is NOT a diagram chase: the underlying set of a fibre product of schemes is not the fibre
product of the underlying sets, and the fibre of `pullback.snd p q` over a point `y` is
`X ×_S Spec κ(y)`, which is larger than `X_{q y}` for a general `y`.  It is the fact that `σ`
is a SECTION — so that `κ(σ.base s) = κ(s)` — that collapses it, and that is exactly the
content of `sliceIncl` being a base change of `σ`. -/
-- (`range_sliceIncl` is declared far BELOW, beside `isPullback_sliceIncl`, for the same
-- reason as `range_sliceOverOpen` above: two branches proved it independently and the
-- lower copy is the one every consumer in this file `rw`s with.)

end Slice

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

/-! ### The covering step, cut into the properness half and the connectedness half

The two halves of the covering step are separated here, and both are PROVEN:

1. *properness* — `isOpen_setOf_slice_mapsTo`: for a fixed open `U ⊆ Z`, the set of `y : Y`
   whose whole slice is mapped into `U` is OPEN.  This is the tube lemma, and it is exactly
   `IsProper p ⟹ IsClosedMap (pullback.snd p q)` (properness is stable under base change);
   the complement of that set is the image of the closed `m ⁻¹(Z ∖ U)`.
2. *connectedness* — the clopen argument, assembled here as
   `mem_sliceGoodLocus_of_slice_const` over `isClosed_sliceContractedLocus_fiber`, the
   semicontinuity statement proven in the section after next.

The assembly runs on two loci, which the lemmas below prove to be THE SAME SET:

* `sliceGoodLocus` — the set of `y` at which the leaf's conclusion holds.  It is open by
  construction (`isOpen_sliceGoodLocus`), since its defining witness `V` is a
  neighbourhood of every one of its points.
* `sliceContractedLocus` — the set of `y` whose slice `m` maps to a SINGLE POINT of `Z`.

`sliceContractedLocus ⊆ sliceGoodLocus` is the properness half packaged
(`mem_sliceGoodLocus_of_mem_sliceContractedLocus`): the single image point `z` sits in an
affine open `U` lying over an affine `S₀ ∋ q y`, the tube lemma shrinks `Y` to an open on
which the whole slice lands in `U`, and an affine `V` inside that open and inside
`q ⁻¹ᵁ S₀` makes `V ×_S U = V ×_{S₀} U` affine (`isAffine_pullback_ι_comp`).  The reverse
inclusion `sliceContractedLocus_of_sliceGoodLocus` is the affine-target rigidity lemma
already proven above: over `V` the map factors as `pullback.snd ≫ d`, so each slice over
`V` goes to the single point `d v`.  This is where `hpush` is consumed.

`σ` and `hconst` enter only through `slice_const_of_section`: the slice over `σ s` is
exactly the image of `sliceIncl` (`isPullback_sliceIncl` — the slice cut out by a section
is the BASE CHANGE of `σ` along `pullback.snd p q`, so `range (sliceIncl) =
(pullback.snd p q) ⁻¹ (range σ)`), and `hconst` sends all of it to `c s`. -/

/-- **THE TUBE LEMMA** (PROVEN) — the properness half of the covering step.

`{y | m maps the whole slice over y into U}` is OPEN, because its complement is
`(pullback.snd p q) '' (m ⁻¹ (Z ∖ U))`, the image of a closed set under a proper — hence
closed — map.  `pullback.snd p q` is proper as a base change of `p`.

No separatedness, no connectedness, no section: this is the entire content of
"`IsProper ⟹ IsClosedMap` for the base-changed projection". -/
theorem isOpen_setOf_slice_mapsTo {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} [IsProper p]
    (m : pullback p q ⟶ Z) (U : Z.Opens) :
    IsOpen {y : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w ∈ U} := by
  have hcl : IsClosedMap (pullback.snd p q) := (pullback.snd p q).isClosedMap
  have hset : {y : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w ∈ U}
      = (Set.image (pullback.snd p q) (m ⁻¹' (U : Set Z)ᶜ))ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
      not_exists, not_and]
    constructor
    · rintro h w hw rfl
      exact hw (h w rfl)
    · intro h w hw
      by_contra hc
      exact h w hc hw
  rw [hset]
  exact isOpen_compl_iff.mpr (hcl _ ((U.2.isClosed_compl).preimage m.continuous))

/-- **THE SLICE CUT OUT BY A SECTION IS A BASE CHANGE OF THAT SECTION** (PROVEN).

`pullback.snd p q` is the base change of `p` along `q`; base-changing it once more along
`σ` gives the base change of `p` along `σ ≫ q = 𝟙 S`, i.e. `X` itself, and the comparison
map is `sliceIncl`.  Formally this is one pasting: the outer rectangle obtained by
adjoining `pullback.fst p q` on the right is `IsPullback (𝟙 X) p p (𝟙 S)`.

The consequence used below is `range_sliceIncl`: every point of `X ×_S Y` lying over a
point of `σ(S)` — not merely those of the form `(x, σ (p x))` — is in the image of
`sliceIncl`.  That is a statement about the CARRIER of a fibre product and is not formal;
what makes it true is that `κ(σ s) = κ(s)`, so `κ(x) ⊗_{κ(s)} κ(σ s)` has a single prime. -/
theorem isPullback_sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) : IsPullback (sliceIncl p q σ hσ) p (pullback.snd p q) σ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p q) (h₂₂ := q) ?_
    (sliceIncl_snd p q σ hσ) (IsPullback.of_hasPullback p q)
  rw [sliceIncl_fst, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **THE IMAGE OF `sliceIncl` IS THE PART OF `X ×_S Y` OVER `σ(S)`** (PROVEN), from
`isPullback_sliceIncl` and `Scheme.Pullback.range_fst`. -/
theorem range_sliceIncl {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) :
    Set.range (sliceIncl p q σ hσ) = (pullback.snd p q) ⁻¹' Set.range σ := by
  have h := isPullback_sliceIncl p q σ hσ
  have e : (sliceIncl p q σ hσ : ↥X → ↥(pullback p q))
      = (pullback.fst (pullback.snd p q) σ) ∘ (h.isoPullback.hom) := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  have hsurj : Function.Surjective
      (h.isoPullback.hom : ↥X → ↥(pullback (pullback.snd p q) σ)) := by
    intro z
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply]; simp⟩
  rw [e, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

/-- **`X ×_S V` IS EXACTLY THE PART OF `X ×_S Y` LYING OVER `V`, ON POINTS** (PROVEN) — the
carrier form of `isPullback_sliceOverOpen`, proven the same way as `range_sliceIncl`. -/
theorem range_sliceOverOpen {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (V : Y.Opens) :
    Set.range (sliceOverOpen p q V) = (pullback.snd p q) ⁻¹' (V : Set Y) := by
  have h := isPullback_sliceOverOpen p q V
  have e : (sliceOverOpen p q V : ↥(pullback p (V.ι ≫ q)) → ↥(pullback p q))
      = (pullback.fst (pullback.snd p q) V.ι) ∘ (h.isoPullback.hom) := by
    funext x
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  have hsurj : Function.Surjective
      (h.isoPullback.hom : ↥(pullback p (V.ι ≫ q)) → ↥(pullback (pullback.snd p q) V.ι)) := by
    intro z
    exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply]; simp⟩
  rw [e, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst,
    Scheme.Opens.range_ι]

/-- A point of an open subscheme lands in that open. -/
theorem mem_range_ι {W : Scheme.{u}} (V : W.Opens) (v : ↥V) : V.ι v ∈ (V : Set W) := by
  rw [← Scheme.Opens.range_ι]; exact ⟨v, rfl⟩

/-- Affine opens are a basis, in the form used three times below. -/
theorem exists_isAffine_opens_subset {W : Scheme.{u}} {T : Set W} (hT : IsOpen T) (x : W)
    (hx : x ∈ T) : ∃ V : W.Opens, IsAffine V ∧ x ∈ V ∧ (V : Set W) ⊆ T := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open hx hT
  exact ⟨V, hV, hxV, hVW⟩

/-- **`V ×_S U` IS AFFINE WHEN `V` AND `U` ARE AFFINE OPENS OVER ONE AFFINE `S₀ ⊆ S`**
(PROVEN).

`Mathlib` has `IsAffine (pullback f g)` for `f` an affine morphism and `g` an affine
scheme, so the only issue is that `V.ι ≫ q` and `U.ι ≫ r` go to `S`, not to `S₀`.  Both
factor through the open immersion `S₀.ι`, which is a MONOMORPHISM, and
`pullbackIsPullbackOfCompMono` says that postcomposing both legs with a mono does not
change the fibre product: `V ×_S U = V ×_{S₀} U`, which is affine. -/
theorem isAffine_pullback_ι_comp {Y Z S : Scheme.{u}} {q : Y ⟶ S} {r : Z ⟶ S} (S₀ : S.Opens)
    (V : Y.Opens) (U : Z.Opens) [IsAffine S₀] [IsAffine V] [IsAffine U]
    (hV : Set.range (V.ι ≫ q) ⊆ (S₀ : Set S)) (hU : Set.range (U.ι ≫ r) ⊆ (S₀ : Set S)) :
    IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) := by
  have hV' : Set.range (V.ι ≫ q) ⊆ Set.range S₀.ι := by
    rw [Scheme.Opens.range_ι]; exact hV
  have hU' : Set.range (U.ι ≫ r) ⊆ Set.range S₀.ι := by
    rw [Scheme.Opens.range_ι]; exact hU
  have hv : IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV' ≫ S₀.ι = V.ι ≫ q :=
    IsOpenImmersion.lift_fac _ _ _
  have hu : IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU' ≫ S₀.ι = U.ι ≫ r :=
    IsOpenImmersion.lift_fac _ _ _
  rw [← hv, ← hu]
  have hpb : IsPullback (pullback.fst (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV')
      (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU'))
      (pullback.snd (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV')
        (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU'))
      (IsOpenImmersion.lift S₀.ι (V.ι ≫ q) hV' ≫ S₀.ι)
      (IsOpenImmersion.lift S₀.ι (U.ι ≫ r) hU' ≫ S₀.ι) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono _ _ S₀.ι)
  exact IsAffine.of_isIso hpb.isoPullback.inv

/-- **THE GOOD LOCUS**: the set of points of `Y` at which the conclusion of
`exists_isAffineOpen_slice_nbhd_of_slice_const` holds.  The theorem says it is all of `Y`. -/
def sliceGoodLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : Z ⟶ S)
    (m : pullback p q ⟶ Z) : Set Y :=
  {y | ∃ (V : Y.Opens) (U : Z.Opens), y ∈ V ∧
      IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) ∧
      Set.range (sliceOverOpen p q V ≫ m) ⊆ (U : Set Z)}

/-- **THE CONTRACTED LOCUS**: the set of `y : Y` whose slice `m` maps to a single point. -/
def sliceContractedLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (m : pullback p q ⟶ Z) : Set Y :=
  {y | ∃ z : Z, ∀ w : ↥(pullback p q), (pullback.snd p q) w = y → m w = z}

/-- **THE GOOD LOCUS IS OPEN** (PROVEN) — immediately, since its witness `V` at `y` is a
neighbourhood of `y` and witnesses membership at each of its own points. -/
theorem isOpen_sliceGoodLocus {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : Z ⟶ S)
    (m : pullback p q ⟶ Z) : IsOpen (sliceGoodLocus p q r m) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨V, U, hyV, haff, hrange⟩
  exact ⟨(V : Set Y), fun y' hy' => ⟨V, U, hy', haff, hrange⟩, V.2, hyV⟩

/-- **CONTRACTED ⟹ GOOD** (PROVEN) — the properness half, packaged.

Given that the slice over `y` goes to the single point `z`: `r z = q y` by `hm`, so an
affine `S₀ ∋ q y`, an affine `U ∋ z` inside `r ⁻¹ᵁ S₀`, the tube lemma, and an affine
`V ∋ y` inside both the tube and `q ⁻¹ᵁ S₀` give the required pair, with `V ×_S U` affine
by `isAffine_pullback_ι_comp`.

`[Surjective (pullback.snd p q)]` is used only to produce ONE point of the slice, which is
what pins `z` over `q y`; it comes from `surjective_of_hasUniversallyTrivialPushforward`. -/
theorem mem_sliceGoodLocus_of_mem_sliceContractedLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [Surjective (pullback.snd p q)]
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) {y : Y}
    (hy : y ∈ sliceContractedLocus p q m) : y ∈ sliceGoodLocus p q r m := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨w₀, hw₀⟩ := (pullback.snd p q).surjective y
  have hzs : r z = q y := by
    rw [← hz w₀ hw₀, ← hw₀]
    simp only [← Scheme.Hom.comp_apply, hm, ← pullback.condition]
  obtain ⟨S₀, hS₀, hsS₀, -⟩ := exists_isAffine_opens_subset isOpen_univ (q y) (Set.mem_univ _)
  haveI := hS₀
  obtain ⟨U, hU, hzU, hUS₀⟩ := exists_isAffine_opens_subset (r ⁻¹ᵁ S₀).2 z
    (show z ∈ ((r ⁻¹ᵁ S₀ : Z.Opens) : Set Z) by simpa [hzs] using hsS₀)
  haveI := hU
  obtain ⟨V, hV, hyV, hVsub⟩ :=
    exists_isAffine_opens_subset
      ((isOpen_setOf_slice_mapsTo m U).inter (q ⁻¹ᵁ S₀).2) y
      (show y ∈ {y' : Y | ∀ w : ↥(pullback p q), (pullback.snd p q) w = y' → m w ∈ U} ∩
          ((q ⁻¹ᵁ S₀ : Y.Opens) : Set Y) from
        ⟨fun w hw => by rw [hz w hw]; exact hzU, by simpa using hsS₀⟩)
  haveI := hV
  refine ⟨V, U, hyV, ?_, ?_⟩
  · refine isAffine_pullback_ι_comp S₀ V U ?_ ?_
    · rintro _ ⟨v, rfl⟩
      simpa using (hVsub (mem_range_ι V v)).2
    · rintro _ ⟨u, rfl⟩
      simpa using hUS₀ (mem_range_ι U u)
  · rintro _ ⟨w', rfl⟩
    have hw : (pullback.snd p q) ((sliceOverOpen p q V) w')
        = V.ι ((pullback.snd p (V.ι ≫ q)) w') := by
      rw [← Scheme.Hom.comp_apply, (isPullback_sliceOverOpen p q V).w, Scheme.Hom.comp_apply]
    have := (hVsub (hw ▸ mem_range_ι V ((pullback.snd p (V.ι ≫ q)) w'))).1
    simpa using this _ rfl

/-- **THE FACTORIZATION AT A POINT OF THE GOOD LOCUS** (PROVEN, over the affine-target
rigidity lemma) — this is where `hpush` is consumed.

At `y` with witnesses `V, U`: `IsOpenImmersion.lift` factors `m` over `V` through `U`, and
`exists_comp_snd_eq_of_isAffine_pullback` (which needs exactly `IsAffine (V ×_S U)`) then
factors it through the projection.  Both consumers of the good locus — contractedness on
points, and the diagonal statement `apply_mem_range_diagonal_of_mem_sliceGoodLocus` — run
off this one morphism-level identity. -/
theorem exists_comp_snd_eq_of_mem_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) {y : Y}
    (hy : y ∈ sliceGoodLocus p q r m) :
    ∃ (V : Y.Opens) (d : V.toScheme ⟶ Z), y ∈ V ∧
      sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d := by
  obtain ⟨V, U, hyV, haff, hrange⟩ := hy
  haveI := haff
  have hrange' : Set.range (sliceOverOpen p q V ≫ m) ⊆ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  have hnU : IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange' ≫ U.ι
      = sliceOverOpen p q V ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hnw : IsOpenImmersion.lift U.ι (sliceOverOpen p q V ≫ m) hrange' ≫ (U.ι ≫ r)
      = pullback.fst p (V.ι ≫ q) ≫ p := by
    rw [← Category.assoc, hnU, Category.assoc, hm, ← Category.assoc]
    congr 1
    simp [sliceOverOpen, pullback.map, pullback.lift_fst]
  obtain ⟨e, he⟩ := exists_comp_snd_eq_of_isAffine_pullback (p := p) (q := V.ι ≫ q)
    (r := U.ι ≫ r) hpush hnw
  exact ⟨V, e ≫ U.ι, hyV, by rw [← hnU, he, Category.assoc]⟩

/-- **GOOD ⟹ CONTRACTED** (PROVEN): every point of the slice over `y` is in the image of
`sliceOverOpen` by `range_sliceOverOpen`, and `V.ι` is injective, so the factorization above
sends all of them to the single point `d v`, where `v` is the point of `V` over `y`. -/
theorem sliceContractedLocus_of_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    (hm : m ≫ r = pullback.fst p q ≫ p) :
    sliceGoodLocus p q r m ⊆ sliceContractedLocus p q m := by
  intro y hy
  obtain ⟨V, d, hyV, hd⟩ := exists_comp_snd_eq_of_mem_sliceGoodLocus hpush hm hy
  obtain ⟨v, hv⟩ : y ∈ Set.range (V.ι) := by rw [Scheme.Opens.range_ι]; exact hyV
  refine ⟨d v, fun w hw => ?_⟩
  have hwmem : w ∈ Set.range (sliceOverOpen p q V) := by
    rw [range_sliceOverOpen, Set.mem_preimage, hw]
    exact hyV
  obtain ⟨w₁, rfl⟩ := hwmem
  have hvv : (pullback.snd p (V.ι ≫ q)) w₁ = v := by
    apply V.ι.isOpenEmbedding.injective
    rw [hv, ← hw, ← Scheme.Hom.comp_apply, ← (isPullback_sliceOverOpen p q V).w,
      Scheme.Hom.comp_apply]
  rw [← Scheme.Hom.comp_apply, hd, Scheme.Hom.comp_apply, hvv]

/-- **THE SLICE OVER `σ s` IS CONTRACTED** (PROVEN) — this is all that `σ` and `hconst` are
for.  Every point of that slice is in the image of `sliceIncl` (`range_sliceIncl`), and
`hconst` sends the image of `sliceIncl` to `c ∘ p`; `σ` is injective because it is a
section, which is what identifies the value as `c s`. -/
theorem slice_const_of_section {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S} (σ : S ⟶ Y)
    (hσ : σ ≫ q = 𝟙 S) {m : pullback p q ⟶ Z} (c : S ⟶ Z)
    (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (s : S) :
    σ s ∈ sliceContractedLocus p q m := by
  refine ⟨c s, fun w hw => ?_⟩
  have hmem : w ∈ Set.range (sliceIncl p q σ hσ) := by
    rw [range_sliceIncl]
    exact ⟨s, hw.symm⟩
  obtain ⟨x, rfl⟩ := hmem
  have hps : p x = s := by
    have h1 : σ (p x) = σ s := by
      rw [← hw]
      simp only [← Scheme.Hom.comp_apply, sliceIncl_snd]
    have h2 : (σ ≫ q) (p x) = (σ ≫ q) s := by
      simp only [Scheme.Hom.comp_apply, h1]
    rw [hσ] at h2
    simpa using h2
  rw [← Scheme.Hom.comp_apply, hconst, Scheme.Hom.comp_apply, hps]

/-! ### Semicontinuity: the contracted locus is closed along the fibres of `q`

This is the second half of "clopen", and the only part of the rigidity lemma that is not
either formal or an application of properness.  The mechanism is semicontinuity, and it is
NOT available globally on `Y`: "the slice over `y` is contracted" is a closed condition
only along the fibres of `q`, because what makes it closed is that the projection away from
the proper factor is an OPEN map, which here holds only after restricting to a fibre —
where everything in sight is flat over the FIELD `κ(s)`.

**No flatness hypothesis on `p` is needed or used.**  The flatness that supplies the
openness is the automatic flatness of a scheme over a field, and `Mathlib` packages exactly
that as `instance [IsIntegral Y] [Subsingleton Y] : UniversallyOpen f`
(`Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`): *any* morphism whose target
is the spectrum of a field is universally open.  That instance is the whole geometric input
of `universallyOpen_of_isPullback_residueField` below, and hence of this section.

**The pair scheme.**  Write `P := (X ×_S Y) ×_Y (X ×_S Y)` with projections `pr₁, pr₂` and
`π := pr₁ ≫ pullback.snd p q : P ⟶ Y`, and let `gP : P ⟶ Z ×_S Z` be
`pullback.lift (pr₁ ≫ m) (pr₂ ≫ m)`.  Then `E := gP ⁻¹ (range (pullback.diagonal r))` is
CLOSED, because `[IsSeparated r]` makes the diagonal a closed immersion, and

  `sliceContractedLocus = {y | π ⁻¹ {y} ⊆ E}`,

whose complement is `π '' Eᶜ` — the image of an OPEN set, hence open as soon as `π` is an
open map.  Over a residue-field base `π` is open, because `pr₁` and `pullback.snd p q` are
each base changes of `p` along morphisms that factor through `Spec κ(s)`.

**Why the scheme-theoretic `E` rather than the set-theoretic condition.**  "All points of
the slice have the same image" is NOT the preimage of the diagonal: for `w, w'` in one
slice with `m w = m w'` the induced point of `Z ×_S Z` need not lie on the diagonal, since
`κ(z) ⊗_{κ(s)} κ(z)` has many primes.  The two directions are proven separately —
`{y | π ⁻¹ {y} ⊆ E} ⊆ sliceContractedLocus` from `Mathlib`'s `PullbackCarrier`
(`exists_preimage_pullback`) together with `diagonal_fst`/`diagonal_snd`, and the reverse
through the good locus, where the factorization
`sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d` makes the two composites
`pr₁ ≫ m` and `pr₂ ≫ m` EQUAL AS MORPHISMS over `V`
(`apply_mem_range_diagonal_of_mem_sliceGoodLocus`). -/

/-- **ANY BASE CHANGE ALONG A MORPHISM THAT FACTORS THROUGH A RESIDUE FIELD IS UNIVERSALLY
OPEN** (PROVEN) — the geometric input of the semicontinuity argument.

If `b` is a base change of `p : X ⟶ S` along `g = g₀ ≫ S.fromSpecResidueField s`, then `b`
is also a base change, along `g₀`, of `X ×_S Spec κ(s) ⟶ Spec κ(s)` (this is
`IsPullback.of_right'` applied to the two squares), and that morphism is universally open
because its TARGET is the spectrum of a field — `Mathlib`'s
`[IsIntegral Y] [Subsingleton Y] : UniversallyOpen f`.  `UniversallyOpen` is stable under
base change, so `b` is universally open.

**`p` is arbitrary**: not flat, not proper, not finitely presented.  All the flatness is in
the base being a field. -/
theorem universallyOpen_of_isPullback_residueField {X W W' S : Scheme.{u}} {p : X ⟶ S}
    {a : W' ⟶ X} {b : W' ⟶ W} {g : W ⟶ S} (s : S) (g₀ : W ⟶ Spec (S.residueField s))
    (hg : g = g₀ ≫ S.fromSpecResidueField s) (h : IsPullback a b p g) :
    UniversallyOpen b := by
  subst hg
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right' h (IsPullback.of_hasPullback p (S.fromSpecResidueField s)))
    inferInstance

/-- **OVER THE GOOD LOCUS THE PAIR SCHEME LANDS IN THE DIAGONAL** (PROVEN).

This is the direction that cannot be done on points.  Over the witness `V` of the good
locus the two composites `pr₁ ≫ m` and `pr₂ ≫ m` become EQUAL AS MORPHISMS: both
projections restricted to `π ⁻¹ᵁ V` factor through `sliceOverOpen p q V` (by
`IsOpenImmersion.lift`, using `range_sliceOverOpen`), the two lifts have the same composite
with `pullback.snd p (V.ι ≫ q)` because `V.ι` is a MONOMORPHISM and both become
`π` after composing with it, and the factorization
`sliceOverOpen p q V ≫ m = pullback.snd p (V.ι ≫ q) ≫ d` then makes the two composites
literally the same morphism.  Hence `π ⁻¹ᵁ V ⟶ Z ×_S Z` factors through the diagonal, and
in particular each of its points does. -/
theorem apply_mem_range_diagonal_of_mem_sliceGoodLocus {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (gP : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback r r)
    (hg₁ : gP ≫ pullback.fst r r
      = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ m)
    (hg₂ : gP ≫ pullback.snd r r
      = pullback.snd (pullback.snd p q) (pullback.snd p q) ≫ m)
    (ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)))
    (hξ : (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ
      ∈ sliceGoodLocus p q r m) :
    gP ξ ∈ Set.range (pullback.diagonal r) := by
  obtain ⟨V, d, hyV, hd⟩ := exists_comp_snd_eq_of_mem_sliceGoodLocus hpush hm hξ
  obtain ⟨ξ', hξ'⟩ : ξ ∈ Set.range
      (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι) := by
    rw [Scheme.Opens.range_ι]; exact hyV
  have hrange : ∀ (t : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback p q),
      t ≫ pullback.snd p q
        = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q →
      Set.range (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ t) ⊆ Set.range (sliceOverOpen p q V) := by
    intro t ht
    rintro _ ⟨x, rfl⟩
    rw [range_sliceOverOpen, Set.mem_preimage, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      ht, Scheme.Hom.comp_apply]
    exact mem_range_ι _ x
  have h₁ := hrange (pullback.fst (pullback.snd p q) (pullback.snd p q)) rfl
  have h₂ := hrange (pullback.snd (pullback.snd p q) (pullback.snd p q)) pullback.condition.symm
  have key : (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m
      = (((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.snd (pullback.snd p q) (pullback.snd p q)) ≫ m := by
    have e₁ := IsOpenImmersion.lift_fac (sliceOverOpen p q V) _ h₁
    have e₂ := IsOpenImmersion.lift_fac (sliceOverOpen p q V) _ h₂
    have hmono : IsOpenImmersion.lift (sliceOverOpen p q V) _ h₁ ≫ pullback.snd p (V.ι ≫ q)
        = IsOpenImmersion.lift (sliceOverOpen p q V) _ h₂ ≫ pullback.snd p (V.ι ≫ q) := by
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc,
        ← (isPullback_sliceOverOpen p q V).w, ← Category.assoc, ← Category.assoc, e₁, e₂,
        Category.assoc, Category.assoc, pullback.condition]
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, hd, ← Category.assoc, ← Category.assoc,
      hmono]
  have hfac : ((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
      ≫ gP
      = ((((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
        ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m) ≫ pullback.diagonal r := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id, hg₁,
        Category.assoc]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id, hg₂]
      simpa using key.symm
  refine ⟨((((pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ⁻¹ᵁ V).ι
    ≫ pullback.fst (pullback.snd p q) (pullback.snd p q)) ≫ m) ξ', ?_⟩
  rw [← hξ', ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]

/-- **THE CONTRACTED LOCUS IS CLOSED WHEN `q` FACTORS THROUGH A RESIDUE FIELD** (PROVEN) —
the semicontinuity statement, in the only generality in which it is true.

The complement of the contracted locus is `π '' Eᶜ` with `E` closed, and `π` is an open map
here: `pullback.snd p q` is a base change of `p` along `q = q₀ ≫ fromSpecResidueField`, and
`pr₁` is a base change of `p` along `pullback.snd p q ≫ q` (paste the pair square onto the
fibre-product square), both of which factor through `Spec κ(s)`, so
`universallyOpen_of_isPullback_residueField` applies to each and `UniversallyOpen` is stable
under composition. -/
theorem isClosed_sliceContractedLocus_of_residueField {X F Z S : Scheme.{u}} {p : X ⟶ S}
    {q : F ⟶ S} {r : Z ⟶ S} [IsProper p] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p) {m : pullback p q ⟶ Z}
    (hm : m ≫ r = pullback.fst p q ≫ p) (s : S) (q₀ : F ⟶ Spec (S.residueField s))
    (hq : q = q₀ ≫ S.fromSpecResidueField s) :
    IsClosed (sliceContractedLocus p q m) := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  haveI : IsClosedImmersion (pullback.diagonal r) := IsSeparated.isClosedImmersion_diagonal
  have hover : ∀ t : (pullback (pullback.snd p q) (pullback.snd p q)) ⟶ pullback p q,
      (t ≫ m) ≫ r = (t ≫ pullback.snd p q) ≫ q := by
    intro t
    rw [Category.assoc, hm, pullback.condition, ← Category.assoc]
  obtain ⟨gP, hg₁, hg₂⟩ : ∃ g : pullback (pullback.snd p q) (pullback.snd p q) ⟶ pullback r r,
      g ≫ pullback.fst r r = pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ m ∧
      g ≫ pullback.snd r r = pullback.snd (pullback.snd p q) (pullback.snd p q) ≫ m := by
    refine ⟨pullback.lift _ _ ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [hover, hover, pullback.condition]
  have hEclosed : IsClosed
      ((gP : ↥(pullback (pullback.snd p q) (pullback.snd p q)) → ↥(pullback r r))
        ⁻¹' Set.range (pullback.diagonal r)) :=
    (pullback.diagonal r).isClosedEmbedding.isClosed_range.preimage gP.continuous
  have hCeq : sliceContractedLocus p q m
      = {y : F | ∀ ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)),
          (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ = y →
            gP ξ ∈ Set.range (pullback.diagonal r)} := by
    refine Set.Subset.antisymm (fun y hy ξ hξ => ?_) (fun y hy => ?_)
    · exact apply_mem_range_diagonal_of_mem_sliceGoodLocus hpush hm gP hg₁ hg₂ ξ
        (by rw [hξ]; exact mem_sliceGoodLocus_of_mem_sliceContractedLocus hm hy)
    · obtain ⟨w₀, hw₀⟩ := (pullback.snd p q).surjective y
      refine ⟨m w₀, fun w hw => ?_⟩
      obtain ⟨ξ, e₁, e₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p q)
        (g := pullback.snd p q) w w₀ (by rw [hw, hw₀])
      obtain ⟨z, hz⟩ := hy ξ (by rw [Scheme.Hom.comp_apply, e₁, hw])
      have hzw : m w = z := by
        rw [← e₁, ← Scheme.Hom.comp_apply, ← hg₁, Scheme.Hom.comp_apply, ← hz,
          ← Scheme.Hom.comp_apply, pullback.diagonal_fst]
        simp
      have hzw₀ : m w₀ = z := by
        rw [← e₂, ← Scheme.Hom.comp_apply, ← hg₂, Scheme.Hom.comp_apply, ← hz,
          ← Scheme.Hom.comp_apply, pullback.diagonal_snd]
        simp
      rw [hzw, hzw₀]
  have h1 : UniversallyOpen (pullback.fst (pullback.snd p q) (pullback.snd p q)) :=
    universallyOpen_of_isPullback_residueField s (pullback.snd p q ≫ q₀)
      (by rw [Category.assoc, ← hq])
      (IsPullback.paste_horiz
        ((IsPullback.of_hasPullback (pullback.snd p q) (pullback.snd p q)).flip)
        (IsPullback.of_hasPullback p q))
  have h2 : UniversallyOpen (pullback.snd p q) :=
    universallyOpen_of_isPullback_residueField s q₀ hq (IsPullback.of_hasPullback p q)
  haveI hπ : UniversallyOpen (pullback.fst (pullback.snd p q) (pullback.snd p q)
      ≫ pullback.snd p q) := MorphismProperty.comp_mem _ _ _ h1 h2
  rw [hCeq, ← isOpen_compl_iff]
  have hcompl : {y : F | ∀ ξ : ↥(pullback (pullback.snd p q) (pullback.snd p q)),
        (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ξ = y →
          gP ξ ∈ Set.range (pullback.diagonal r)}ᶜ
      = (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q) ''
        ((gP : ↥(pullback (pullback.snd p q) (pullback.snd p q)) → ↥(pullback r r))
          ⁻¹' Set.range (pullback.diagonal r))ᶜ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_image, Set.mem_preimage,
      not_forall]
    constructor
    · rintro ⟨ξ, hξ, hξ'⟩
      exact ⟨ξ, hξ', hξ⟩
    · rintro ⟨ξ, hξ', hξ⟩
      exact ⟨ξ, hξ, hξ'⟩
  rw [hcompl]
  exact (pullback.fst (pullback.snd p q) (pullback.snd p q) ≫ pullback.snd p q).isOpenMap _
    (isOpen_compl_iff.mpr hEclosed)

/-- **CONTRACTEDNESS IS A FIBREWISE NOTION** (PROVEN): base-changing `q` along an INJECTIVE
`t` pulls the contracted locus back to the contracted locus.

Only injectivity of `t` on points is used, plus the fact that the base change `j` has range
`(pullback.snd p q) ⁻¹ (range t)` — which for `t = q.fiberι s` is `Mathlib`'s
`Scheme.Pullback.range_map`. -/
theorem sliceContractedLocus_comp_eq {X Y Z T S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (t : T ⟶ Y) (ht : Function.Injective (t : ↥T → ↥Y)) {m : pullback p q ⟶ Z}
    (j : pullback p (t ≫ q) ⟶ pullback p q)
    (hjrange : Set.range (j : ↥(pullback p (t ≫ q)) → ↥(pullback p q))
      = (pullback.snd p q) ⁻¹' Set.range (t : ↥T → ↥Y))
    (hjsnd : j ≫ pullback.snd p q = pullback.snd p (t ≫ q) ≫ t) :
    sliceContractedLocus p (t ≫ q) (j ≫ m)
      = (t : ↥T → ↥Y) ⁻¹' sliceContractedLocus p q m := by
  ext f
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun w hw => ?_⟩
    have hwr : w ∈ Set.range (j : ↥(pullback p (t ≫ q)) → ↥(pullback p q)) := by
      rw [hjrange, Set.mem_preimage, hw]
      exact ⟨f, rfl⟩
    obtain ⟨w₁, rfl⟩ := hwr
    refine (?_ : m (j w₁) = z)
    rw [← Scheme.Hom.comp_apply]
    refine hz w₁ (ht ?_)
    rw [← Scheme.Hom.comp_apply, ← hjsnd, Scheme.Hom.comp_apply, hw]
  · rintro ⟨z, hz⟩
    refine ⟨z, fun w₁ hw₁ => ?_⟩
    rw [Scheme.Hom.comp_apply]
    refine hz _ ?_
    rw [← Scheme.Hom.comp_apply, hjsnd, Scheme.Hom.comp_apply, hw₁]

/-- **THE CONTRACTED LOCUS IS CLOSED IN EACH FIBRE OF `q`** (PROVEN) — the closed half of
the clopen argument, and the last piece of the rigidity lemma.

Restrict to the scheme-theoretic fibre `q.fiber s`, whose structure morphism to `S` factors
through `Spec κ(s)` by `Scheme.Hom.fiber_fac`.  `sliceContractedLocus_comp_eq` identifies
the contracted locus of the base-changed situation with the preimage of this one under
`q.fiberι s` — the fibre inclusion is injective, and `Scheme.Pullback.range_map` gives the
range of the base change — and
`isClosed_sliceContractedLocus_of_residueField` says the former is closed.  Finally
`Scheme.Hom.fiberHomeo` identifies the fibre with `q ⁻¹ {s}` as a topological subspace. -/
theorem isClosed_sliceContractedLocus_fiber {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [IsSeparated r] (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p) (s : S) :
    IsClosed {u : ↥((q : ↥Y → ↥S) ⁻¹' {s}) | (u : Y) ∈ sliceContractedLocus p q m} := by
  have hjfst : (pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ pullback.fst p q = pullback.fst p (q.fiberι s ≫ q) := by
    simp only [pullback.map]
    rw [pullback.lift_fst, Category.comp_id]
  have hjsnd : (pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ pullback.snd p q = pullback.snd p (q.fiberι s ≫ q) ≫ q.fiberι s := by
    simp only [pullback.map]
    rw [pullback.lift_snd]
  have hmF : ((pullback.map p (q.fiberι s ≫ q) p q (𝟙 X) (q.fiberι s) (𝟙 S) (by simp) (by simp))
      ≫ m) ≫ r = pullback.fst p (q.fiberι s ≫ q) ≫ p := by
    rw [Category.assoc, hm, ← Category.assoc, hjfst]
  have hclosed := isClosed_sliceContractedLocus_of_residueField hpush hmF s
    (q.fiberToSpecResidueField s) (q.fiber_fac s)
  rw [sliceContractedLocus_comp_eq (q.fiberι s) (q.fiberι s).isEmbedding.injective _
    (by rw [Scheme.Pullback.range_map]; simp) hjsnd] at hclosed
  rw [← (q.fiberHomeo s).isClosed_preimage]
  exact hclosed

/-- **THE CLOPEN ARGUMENT** (PROVEN): the good locus is everything.

`sliceContractedLocus = sliceGoodLocus` by the two inclusions above, so that set is OPEN;
it is closed in each fibre of `q` by `isClosed_sliceContractedLocus_fiber`; it meets each
fibre, at `σ s`, by
`slice_const_of_section`; and the fibres of `q` are CONNECTED — `Mathlib`'s
`Scheme.Hom.isConnected_preimage_singleton` for `[GeometricallyConnected q]`.  A nonempty
clopen subset of a preconnected space is everything.

This is where the FAITHFULNESS NOTE bites: with `Y` two points over `S = Spec k` the fibre
`q ⁻¹ {s}` is disconnected, the clopen subset is a single point, and the conclusion fails. -/
theorem mem_sliceGoodLocus_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p) (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    y ∈ sliceGoodLocus p q r m := by
  have hu : HasUniversallyTrivialPushforward (pullback.snd p q) :=
    MorphismProperty.pullback_snd (P := hasTrivialPushforwardProperty.universally) p q hpush
  haveI : Surjective (pullback.snd p q) := surjective_of_hasUniversallyTrivialPushforward hu
  have hCG : sliceContractedLocus p q m ⊆ sliceGoodLocus p q r m :=
    fun _ hy => mem_sliceGoodLocus_of_mem_sliceContractedLocus hm hy
  have hCeq : sliceContractedLocus p q m = sliceGoodLocus p q r m :=
    Set.Subset.antisymm hCG (sliceContractedLocus_of_sliceGoodLocus hpush hm)
  have hconn : _root_.IsConnected ((q : ↥Y → ↥S) ⁻¹' {q y}) :=
    q.isConnected_preimage_singleton _
  haveI : PreconnectedSpace ↥((q : ↥Y → ↥S) ⁻¹' {q y}) :=
    Subtype.preconnectedSpace hconn.isPreconnected
  have hclopen : IsClopen
      {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m} := by
    refine ⟨isClosed_sliceContractedLocus_fiber hpush hm _, ?_⟩
    rw [hCeq]
    exact (isOpen_sliceGoodLocus p q r m).preimage continuous_subtype_val
  have hσmem : σ (q y) ∈ ((q : ↥Y → ↥S) ⁻¹' {q y}) := by
    have h : (σ ≫ q) (q y) = q (σ (q y)) := Scheme.Hom.comp_apply _ _ _
    rw [hσ] at h
    simpa using h.symm
  have hne : {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m}.Nonempty :=
    ⟨⟨σ (q y), hσmem⟩, slice_const_of_section σ hσ c hconst (q y)⟩
  have huniv := hclopen.eq_univ hne
  have hy : (⟨y, rfl⟩ : ↥((q : ↥Y → ↥S) ⁻¹' {q y}))
      ∈ {t : ↥((q : ↥Y → ↥S) ⁻¹' {q y}) | (t : Y) ∈ sliceContractedLocus p q m} := by
    rw [huniv]; trivial
  exact hCG hy

/-- **THE COVERING STEP AT A POINT, IN OPENS ONLY** — PROVEN (2026-07-28) over the single
leaf `isClosed_sliceContractedLocus_fiber`; it is `mem_sliceGoodLocus_of_slice_const`
restated, since `sliceGoodLocus` is by definition the set of `y` at which this holds.

**What is produced at `y`.**  An open `V ∋ y` in `Y` and an open `U ⊆ Z` such that

* `m` maps the whole of `X ×_S V` into `U` — written as the containment of set-theoretic
  ranges, which is precisely `IsOpenImmersion.lift`'s hypothesis; and
* `V ×_S U` is an AFFINE SCHEME — "`U` is affine over the base, over `V`".  In the
  construction `V` and `U` are affine opens lying over one affine open `S₀ ⊆ S`, so
  `V ×_S U = V ×_{S₀} U` is a fibre product of affines over an affine
  (`isAffine_pullback_ι_comp`).

**The proof** (Mumford *AV* §4; BLR 8.4), in the two halves the section above develops.

1. *The properness half*, now PROVEN as `isOpen_setOf_slice_mapsTo`: if the whole slice
   over `y` is mapped into an open `U`, then the same holds over an open neighbourhood of
   `y`, because `m ⁻¹(Z ∖ U)` is closed and `pullback.snd p q` is proper — hence a CLOSED
   MAP — as a base change of `p`.  Packaged with the affine choices this is
   `mem_sliceGoodLocus_of_mem_sliceContractedLocus`.

2. *The connectedness half*, now assembled as `mem_sliceGoodLocus_of_slice_const`: the
   locus where the slice is contracted equals the locus where the conclusion holds (the
   two inclusions above, the second of which is where `hpush` is spent), hence is OPEN; it
   contains `σ(s)` for every `s` by `slice_const_of_section`; and
   `[GeometricallyConnected q]` makes the fibres of `q` connected.  That the locus is also
   CLOSED in each fibre is `isClosed_sliceContractedLocus_fiber`, the semicontinuity
   statement, which is where flatness over the residue field enters.

**WHY THE STATEMENT IS FALSE WITHOUT `[GeometricallyConnected q]`**: with `Y = {y₀, y₁}`
two points over `S = Spec k` the locus produced by (1) is a single point — see the
FAITHFULNESS NOTE in the module docstring.  So half (2) is not decoration.

**AXIS SEARCHED**: the affine and affine-over-the-base cases are DONE and were never what
was missing (`exists_comp_snd_eq_of_isAffine`, `exists_comp_snd_eq_of_isAffine_pullback`);
so is the `Γ ⊣ Spec` corollary, the epimorphism property of the projection
(`eq_of_comp_snd_eq`), the cartesian square (`isPullback_sliceOverOpen`) and the whole
gluing step.  The étale axis (`section_eq_of_formallyUnramified`, diagonal simultaneously
open and closed) is searched and DEAD: `Δ_{B/S}` is an open immersion iff `Ω_{B/S} = 0`,
which fails in relative dimension `> 0`. -/
theorem exists_isAffineOpen_slice_nbhd_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (y : Y) :
    ∃ (V : Y.Opens) (U : Z.Opens), y ∈ V ∧
      IsAffine (pullback (V.ι ≫ q) (U.ι ≫ r)) ∧
      Set.range (sliceOverOpen p q V ≫ m) ⊆ (U : Set Z) :=
  mem_sliceGoodLocus_of_slice_const hpush σ hσ hm c hconst y

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
over `exists_isAffineOpen_slice_nbhd_of_slice_const` (its opens-only form).

**STATUS (2026-07-28): PROVEN OUTRIGHT — NO OPEN LEAF REMAINS UNDER THIS THEOREM.**  The
opens-only form is proven from `isOpen_setOf_slice_mapsTo` (properness ⟹ closed map ⟹ the
tube lemma), `mem_sliceGoodLocus_of_slice_const` (the `GeometricallyConnected` clopen
argument) and `isClosed_sliceContractedLocus_fiber` (semicontinuity of contractedness along
the fibres of `q`, over a field).  The only `sorry` anywhere in this file's cone is
`isIso_appTop_of_isProper_of_flat`, which supplies the HYPOTHESIS `hpush` and is not used
by this proof.

The concrete obstruction the earlier audit named is still worth recording, because it is
what the covering step had to get past: the reduction to an affine target cannot be done
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
