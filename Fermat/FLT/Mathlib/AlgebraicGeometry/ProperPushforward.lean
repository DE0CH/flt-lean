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
* `hasUniversallyTrivialPushforward_of_isProper_of_flat` — **THE LEAF**: the theorem
  itself, in its classical hypotheses.
* `hasUniversallyTrivialPushforward_of_isProper_of_smooth` — PROVEN from the leaf above
  together with `AlgebraicGeometry.GeometricallyReduced.of_smooth`.  This is the form
  every consumer in this development actually applies, because an abelian scheme and a
  smooth proper curve are both given as *smooth* rather than as *flat with reduced
  fibres*.
* `existsUnique_comp_eq_of_hasTrivialPushforward` — **PROVEN**: an `S`-morphism from `X`
  to an AFFINE scheme factors uniquely through `S`.  This is the corollary of
  `p_*𝒪_X = 𝒪_S` that the rigidity lemma consumes, and it is pure `Γ ⊣ Spec` formalism.
* `existsUnique_comp_snd_eq_of_spec` — **PROVEN**: the rigidity lemma for an AFFINE
  target, where it needs neither the contracted slice nor connectedness of `q`.
* `pullbackMapComp` — the canonical `X ×_S V ⟶ X ×_S Y` induced by `g : V ⟶ Y`, with its
  two projection lemmas.  This is the shape in which the local-to-global passage is
  stated: it keeps every intermediate object a *pullback along a composite*, so that
  `existsUnique_comp_snd_eq_of_spec` applies to it verbatim with `q := g ≫ q`, and no
  identification of `(pullback.snd p q) ⁻¹ᵁ V` with `pullback p (V.ι ≫ q)` is needed.
* `HasAffineFactorizationAt p q m y` — the local predicate the reduction turns on: near
  `y`, `m` factors through an AFFINE scheme.
* `range_pullbackMapComp`, `sliceIso`, `range_sliceIncl` — the range of a base change is
  the preimage of the range, applied to `pullbackMapComp` and to the slice.  The second is
  the one with content: the underlying set of a fibre product of schemes is not the fibre
  product of the underlying sets, so "the fibre of `pullback.snd p q` over `σ.base s` is
  the slice" needs the base-change square, not a diagram chase on points.
* `hasAffineFactorizationAt_section` — **PROVEN**: the predicate holds at every point of
  the section `σ`.  Properness of `p` (through the closed image of `pullback.snd p q`) plus
  the contracted slice; this is the one classical step that is genuinely local.
* `hasAffineFactorizationAt_of_section` — **LEAF**: it then holds *everywhere*.  This is
  the open-and-closed / connected-fibres spreading argument, and it is where
  `GeometricallyConnected q` and `IsSeparated r` are consumed.
* `exists_comp_snd_eq_of_forall_locallyFactors` — **LEAF**: gluing.  Needs neither
  properness nor connectedness; its whole content is that `pullback.snd p q` is an
  epimorphism against `S`-morphisms into a separated `Z`.
* `exists_comp_snd_eq_of_slice_const` — **PROVEN** over those three: the RIGIDITY LEMMA
  (Mumford *AV* §4; BLR *Néron Models* 8.4 in the relative case).

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

/-- **`f_*𝒪_X = 𝒪_S` FOR A PROPER FLAT MORPHISM WITH GEOMETRICALLY CONNECTED AND REDUCED
FIBRES** (sorry node — Hartshorne III.12, Mumford *AV* §5, Stacks 0E6R / 0BUG).

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
because it is one on every fibre.  Base change is built into the conclusion for exactly
this reason.

**PIN STATE, checked rather than assumed (2026-07-27).**  `Mathlib` has no higher direct
images of quasi-coherent sheaves, no `Rⁱf_*`, no semicontinuity, no cohomology-and-base-
change; `grep` for `higherDirectImage`/`directImage` over `Mathlib/AlgebraicGeometry` and
over `~/cs/FLT` returns nothing.  So this leaf is a genuine theory build, and it is the
one whose completion unblocks three separate leaves at once. -/
theorem hasUniversallyTrivialPushforward_of_isProper_of_flat (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [GeometricallyReduced f] :
    HasUniversallyTrivialPushforward f :=
  sorry

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

/-! ### Restricting the second factor of a pullback -/

/-- **The canonical morphism `X ×_S V ⟶ X ×_S Y` induced by `g : V ⟶ Y`.**

This is the shape in which every local statement below is written, and the choice is
load-bearing rather than cosmetic.  The alternative — restricting `pullback.snd p q` to the
open `(pullback.snd p q) ⁻¹ᵁ g.opensRange` — forces an identification of that open
subscheme with `pullback p (g ≫ q)` before `existsUnique_comp_snd_eq_of_spec` can be
applied to it, and that identification is a pullback-pasting isomorphism whose transport
across `Category.assoc` on the index morphism is dependent-type noise with no mathematical
content.  Writing the piece as `pullback p (g ≫ q)` from the start means
`existsUnique_comp_snd_eq_of_spec` applies to it *verbatim*, with `q := g ≫ q`.

Written as `pullback.map` rather than as the equal `pullback.lift`, because that is the
form `AlgebraicGeometry.Scheme.Pullback.range_map` is stated for, and `range_pullbackMapComp`
below — the computation of its range as a preimage — is what makes the local step of the
rigidity lemma go through. -/
noncomputable def pullbackMapComp {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) : pullback p (g ≫ q) ⟶ pullback p q :=
  pullback.map p (g ≫ q) p q (𝟙 X) g (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem pullbackMapComp_fst {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    pullbackMapComp p q g ≫ pullback.fst p q = pullback.fst p (g ≫ q) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem pullbackMapComp_snd {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    pullbackMapComp p q g ≫ pullback.snd p q = pullback.snd p (g ≫ q) ≫ g :=
  pullback.lift_snd _ _ _

/-- **THE RANGE OF `pullbackMapComp` IS THE PREIMAGE OF THE RANGE OF `g`**, because
`pullbackMapComp p q g` is the base change of `g` along `pullback.snd p q`. -/
theorem range_pullbackMapComp {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    {V : Scheme.{u}} (g : V ⟶ Y) :
    Set.range (pullbackMapComp p q g).base =
      (pullback.snd p q).base ⁻¹' Set.range g.base := by
  rw [pullbackMapComp, Scheme.Pullback.range_map]
  simp

/-! ### The slice is the base change of the section -/

section Slice

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)

/-- **The canonical isomorphism `X ≅ X ×_S S` supplied by the section `σ`.**

`σ ≫ q = 𝟙 S` makes `pullback p (σ ≫ q)` a pullback along an identity, hence a copy of
`X`.  Composing the inverse of this with `pullbackMapComp p q σ` recovers `sliceIncl`, and
that is what exhibits the slice as the BASE CHANGE of `σ` along `pullback.snd p q` — which
is the only thing needed to compute its range. -/
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

theorem sliceIso_comp : sliceIso p q σ hσ ≫ pullbackMapComp p q σ = sliceIncl p q σ hσ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullbackMapComp_fst, sliceIso_fst, sliceIncl_fst]
  · rw [Category.assoc, pullbackMapComp_snd, sliceIso_snd_assoc, sliceIncl_snd]

/-- **THE SLICE IS EXACTLY THE PART OF `X ×_S Y` LYING OVER THE SECTION.**

This is the fact that makes the local step of the rigidity lemma work: it says the fibre of
`pullback.snd p q` over `σ.base s` is entirely covered by the slice, so `hconst` — which
constrains `m` only on the slice — pins `m` on that whole fibre.  Note that the underlying
set of a fibre product of schemes is *not* the fibre product of the underlying sets, so this
is a real statement and not bookkeeping; it holds because `sliceIncl` is a base change of
`σ`, and the range of a base change IS the preimage of the range. -/
theorem range_sliceIncl :
    Set.range (sliceIncl p q σ hσ).base = (pullback.snd p q).base ⁻¹' Set.range σ.base := by
  rw [← sliceIso_comp p q σ hσ, ← range_pullbackMapComp p q σ]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [Set.range_eq_univ.mpr (fun z => ((ConcreteCategory.bijective_of_isIso
    (sliceIso p q σ hσ).base).surjective z)), Set.image_univ]

end Slice

/-! ### The local predicate the rigidity lemma turns on -/

/-- **`m` FACTORS THROUGH AN AFFINE SCHEME NEAR `y`**: there is an open immersion
`g : V ⟶ Y` whose range contains `y`, a ring `R`, and a factorization of
`X ×_S V ⟶ X ×_S Y ⟶ Z` through `Spec R`.

Note this predicate is *manifestly open* in `y` — that is the point of phrasing it through
an open immersion whose range contains `y` rather than through the point `y` alone — so
the openness half of the classical open-and-closed argument is definitional here and only
the closedness half is left to `hasAffineFactorizationAt_of_section`.

It is also exactly the input `existsUnique_comp_snd_eq_of_spec` consumes: given the data
above, that lemma descends `n` along `pullback.snd p (g ≫ q)` to a unique `V ⟶ Spec R`,
and post-composing with `j` gives the local factorization of `m` through `V`.  That
descent is carried out inside the proof of `exists_comp_snd_eq_of_slice_const` below, and
it is the whole reason the affine target appears in this predicate at all. -/
def HasAffineFactorizationAt {X Y Z S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (m : pullback p q ⟶ Z) (y : Y) : Prop :=
  ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : IsOpenImmersion g), y ∈ Set.range g.base ∧
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ Z) (n : pullback p (g ≫ q) ⟶ Spec R),
      pullbackMapComp p q g ≫ m = n ≫ j

/-- **AT EVERY POINT OF THE SECTION, `m` FACTORS THROUGH AN AFFINE** (PROVEN 2026-07-27 —
the local half of the rigidity lemma).

This is the one step that is genuinely local, and it is the only place properness of `p`
is used.  It uses NEITHER the pushforward hypothesis, NOR connectedness of `q`, NOR
separatedness of `r` — the hypothesis list is exactly what the proof consumes.  The
argument is classical and short:

* `π := pullback.snd p q` is proper, being a base change of `p`, hence a CLOSED map
  (`Scheme.Hom.isClosedMap`);
* `Set.range (sliceIncl p q σ hσ) = π ⁻¹ (Set.range σ)` — `range_sliceIncl` above — so the
  fibre of `π` over `σ.base s` is entirely covered by the slice.  `hconst` therefore sends
  that whole fibre to the single point `c.base s`.  This is the step with actual content:
  the underlying set of a fibre product of schemes is *not* the fibre product of the
  underlying sets, and what rescues it is that `sliceIncl` is a base change of `σ`;
* choose an affine open `U ⊆ Z` containing `c.base s`.  Then `C := m ⁻¹ (Uᶜ)` is closed and
  misses that fibre, so `W := Y ∖ π '' C` is an open neighbourhood of `σ.base s` over which
  `m` lands in `U`;
* `U` affine gives `U ≅ Spec Γ(Z, U)` (`IsAffineOpen.isoSpec`), and `IsOpenImmersion.lift`
  produces the required `n : pullback p (W.ι ≫ q) ⟶ Spec Γ(Z, U)` — its range hypothesis is
  discharged by `range_pullbackMapComp`, again a base-change range computation. -/
theorem hasAffineFactorizationAt_section {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    [IsProper p] (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S) {m : pullback p q ⟶ Z}
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) (s : S) :
    HasAffineFactorizationAt p q m (σ.base s) := by
  classical
  -- an affine open neighbourhood `U` of the point `c s` the slice is contracted to
  obtain ⟨U, hU, hcU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Z) (x := c.base s) (U := ⊤) trivial
  -- the closed set of points that `m` throws outside `U`, and its closed image in `Y`
  set C := ⇑m.base ⁻¹' ((U : Set Z)ᶜ) with hCdef
  have hCclosed : IsClosed C := (U.2.isClosed_compl).preimage m.base.hom.continuous
  have hclosed : IsClosed ((pullback.snd p q).base '' C) :=
    (pullback.snd p q).isClosedMap C hCclosed
  set W : Y.Opens := ⟨((pullback.snd p q).base '' C)ᶜ, hclosed.isOpen_compl⟩ with hWdef
  -- points of `X ×_S Y` lying over `W` are sent into `U`
  have hsub : ∀ w, (pullback.snd p q).base w ∈ W → m.base w ∈ U := by
    intro w hw
    by_contra hcon
    exact hw ⟨w, hcon, rfl⟩
  have hqσ : ∀ t : S, q (σ t) = t := by
    intro t
    rw [← Scheme.Hom.comp_apply, hσ]
    simp
  -- the section's point lies in `W`, because the whole fibre over it is the slice
  have hWs : σ.base s ∈ W := by
    rintro ⟨w, hwC, hw⟩
    have hwr : w ∈ Set.range (sliceIncl p q σ hσ).base := by
      rw [range_sliceIncl]
      exact ⟨s, hw.symm⟩
    obtain ⟨x, rfl⟩ := hwr
    have e1 : (pullback.snd p q) ((sliceIncl p q σ hσ) x) = σ (p x) := by
      rw [← Scheme.Hom.comp_apply, sliceIncl_snd, Scheme.Hom.comp_apply]
    have e2 : m ((sliceIncl p q σ hσ) x) = c (p x) := by
      rw [← Scheme.Hom.comp_apply, hconst, Scheme.Hom.comp_apply]
    have hsx : σ (p x) = σ s := by rw [← e1, hw]
    have hps : p x = s := by rw [← hqσ (p x), hsx, hqσ]
    refine hwC ?_
    rw [e2, hps]
    exact hcU
  have hrange : Set.range (pullbackMapComp p q W.ι ≫ m) ⊆ Set.range U.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_pullbackMapComp,
      Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rintro _ ⟨w, hw, rfl⟩
    exact hsub w hw
  refine ⟨W.toScheme, W.ι, inferInstance, by rw [Scheme.Opens.range_ι]; exact hWs,
    Γ(Z, U), hU.isoSpec.inv ≫ U.ι,
    IsOpenImmersion.lift U.ι (pullbackMapComp p q W.ι ≫ m) hrange ≫ hU.isoSpec.hom, ?_⟩
  rw [Category.assoc, ← Category.assoc hU.isoSpec.hom, Iso.hom_inv_id, Category.id_comp,
    IsOpenImmersion.lift_fac]

/-- **THE AFFINE FACTORIZATION SPREADS FROM THE SECTION TO ALL OF `Y`** (sorry node — the
global half of the rigidity lemma).

`HasAffineFactorizationAt` is open by construction, so what is left is that its locus is
also CLOSED, after which `GeometricallyConnected q` — connected fibres for `q`, each met
by the section `σ` — makes it everything.  Closedness is where `IsSeparated r` enters: the
locus where the two `S`-morphisms `m` and `pullback.snd p q ≫ d` agree is closed because
the diagonal of `r` is a closed immersion, and it is where the pushforward hypothesis
enters, through `existsUnique_comp_snd_eq_of_spec`'s uniqueness clause, to see that the
locally-constructed `d`s are forced.

**FAITHFULNESS.** `GeometricallyConnected q` is not decoration: with `Y = Spec k ⊔ Spec k`
the conclusion is false — see the FAITHFULNESS NOTE in the module docstring.  This leaf is
where that hypothesis is consumed, and a proof of it that never uses `H`, `hσ` or
`GeometricallyConnected q` is proving something false. -/
theorem hasAffineFactorizationAt_of_section {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (H : ∀ s : S, HasAffineFactorizationAt p q m (σ.base s)) (y : Y) :
    HasAffineFactorizationAt p q m y :=
  sorry

/-- **GLUING THE LOCAL FACTORIZATIONS** (sorry node — and this, not the pushforward
theorem, is the piece that needs new machinery).

Given a factorization of `m` over a neighbourhood of every point of `Y`, produce a global
one.  Neither properness of `p`, nor a section, nor connectedness of `q` is used: this is
purely the statement that the local pieces agree on overlaps and glue.

**The content, stated so it can be checked rather than believed.**  Agreement on overlaps
is `Scheme.OpenCover.glueMorphisms`' compatibility hypothesis, and it asks for equality of
two morphisms into the possibly NON-affine `Z`, which
`existsUnique_comp_eq_of_hasTrivialPushforward` does not give (it is affine-target only).
What is wanted is:

> if `d₁ d₂ : Y ⟶ Z` are `S`-morphisms (`dᵢ ≫ r = q`) with
> `pullback.snd p q ≫ d₁ = pullback.snd p q ≫ d₂`, then `d₁ = d₂`

i.e. that `pullback.snd p q` is an epimorphism against `S`-morphisms into a separated `Z`.
That in turn has a short sheaf-theoretic proof from the hypotheses actually present here,
and it does NOT need scheme-theoretic images (an earlier audit in this file said it did;
that is corrected):

* `E := equalizer of d₁, d₂` is the pullback of `Δ_r` along `(d₁, d₂) : Y ⟶ Z ×_S Z`, and
  `IsSeparated r` makes `Δ_r` a closed immersion, so `E ⟶ Y` is a CLOSED IMMERSION;
* `π := pullback.snd p q` equalizes `d₁` and `d₂`, so `π` factors through `E`;
* therefore `𝒪_Y ↠ ι_* 𝒪_E ⟶ π_* 𝒪_W` composes to `π`'s unit, which is an ISOMORPHISM by
  `hpush` (base-changed along `q`).  The first map is surjective and the composite
  injective, so the first map is injective, hence an isomorphism, hence `E = Y`.

So the only genuinely absent ingredient is the equalizer-as-closed-subscheme construction
together with the sheaf-level statement of `HasTrivialPushforward`; the whole
cohomology-and-base-change theory (`hasUniversallyTrivialPushforward_of_isProper_of_flat`)
is NOT consumed anywhere in this cluster. -/
theorem exists_comp_snd_eq_of_forall_locallyFactors {X Y Z S : Scheme.{u}} {p : X ⟶ S}
    {q : Y ⟶ S} {r : Z ⟶ S} [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (H : ∀ y : Y, ∃ (V : Scheme.{u}) (g : V ⟶ Y) (_ : IsOpenImmersion g),
      y ∈ Set.range g.base ∧ ∃ dV : V ⟶ Z,
        pullbackMapComp p q g ≫ m = pullback.snd p (g ≫ q) ≫ dV) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d :=
  sorry

/-- **THE RIGIDITY LEMMA** (PROVEN 2026-07-27, over the three leaves above — Mumford
*Abelian Varieties* §4; BLR *Néron Models* 8.4 in the relative case; Mumford *GIT*
Prop. 6.1 over a general base).

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

**THE CHECK THAT WOULD REFUTE ANY "THIS IS IRREDUCIBLE" VERDICT** on this leaf was: land
`hasUniversallyTrivialPushforward_of_isProper_of_flat`, and add the corollary "an
`S`-morphism from `X` to an affine scheme factors uniquely through `S`" (that corollary is
short — it is the `Γ ⊣ Spec` adjunction plus `IsIso (f.app ⊤)`).

**HALF OF THAT CHECK HAS NOW BEEN RUN (2026-07-27) and it came out as predicted.**  The
corollary is `existsUnique_comp_eq_of_hasTrivialPushforward` above — PROVEN, ~20 lines,
no geometry — and the affine-target case of *this very statement* is
`existsUnique_comp_snd_eq_of_spec`, also PROVEN, and stronger than this leaf's conclusion
(it is an `∃!`, and it drops `σ`, `hconst`, `GeometricallyConnected q`, `IsSeparated r`
and `IsProper p`).  So the pushforward hypothesis is no longer any part of the
obstruction here, and neither is the flat pushforward leaf: **this leaf does not consume
`hasUniversallyTrivialPushforward_of_isProper_of_flat` at all**, only the hypothesis
`hpush` it is handed.

**WHAT IS ACTUALLY LEFT, stated so it can be checked rather than believed.**  Exactly the
reduction to an affine target, and it cannot be done globally: with `S = Spec k`,
`X = Spec k`, `Y = Z = ℙ¹`, `q = r` the structure maps and `m = 𝟙`, every hypothesis
holds, `d = 𝟙` is the factorization, and `m` factors through no affine scheme.  So the
remaining work is genuinely local-to-global on `Y`, and **it is now cut into three named
leaves, with the assembly below PROVEN over them** (2026-07-27):

1. *(local)* `hasAffineFactorizationAt_section` — for `s : S`, `m` factors through an
   affine near `σ.base s`.  This is where properness of `p` (closed image of
   `pullback.snd p q` in `Y`) and `hconst` are consumed, and it uses nothing else.
   **This one is PROVEN** (2026-07-27), so of the four steps only 2 and 4 remain open;
2. *(spreading)* `hasAffineFactorizationAt_of_section` — the affine-factorization locus,
   open by construction, is also closed, so `GeometricallyConnected q` plus the section
   makes it all of `Y`.  `IsSeparated r` is consumed here;
3. *(descent per piece)* `existsUnique_comp_snd_eq_of_spec` applied to
   `n : pullback p (g ≫ q) ⟶ Spec R` — **this step is done, right below**, and it is the
   only step of the three that needed nothing new.  It is what turns each affine
   factorization into an honest local factorization through `V`;
4. *(glue)* `exists_comp_snd_eq_of_forall_locallyFactors` — assemble the local
   factorizations into a global `d`.

**THE PREVIOUS AUDIT'S LAST CLAIM IS CORRECTED.**  It said the gluing step needs the
SCHEME-THEORETIC IMAGE, "absent from this project at this pin", and that this is the real
new machinery.  The epimorphism statement it identified is right and is exactly the
content of leaf 4 — but it does not need scheme-theoretic images: the equalizer of two
`S`-morphisms into a separated `Z` is already a closed subscheme (pull back the diagonal),
`pullback.snd p q` factors through it, and `𝒪_Y ↠ 𝒪_E ↪ π_*𝒪` with an isomorphism for the
composite forces `E = Y`.  See `exists_comp_snd_eq_of_forall_locallyFactors` for the
argument written out.  What that leaf actually needs is the equalizer construction and the
sheaf-level reading of `HasTrivialPushforward`, both of which are small next to a
scheme-theoretic image theory.

**AND, UNCHANGED AND WORTH REPEATING**: no leaf in this cluster consumes
`hasUniversallyTrivialPushforward_of_isProper_of_flat`.  Only the *hypothesis* `hpush` is
used.  Do not go build cohomology and base change on account of this statement. -/
theorem exists_comp_snd_eq_of_slice_const {X Y Z S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    {r : Z ⟶ S} [IsProper p] [GeometricallyConnected q] [IsSeparated r]
    (hpush : HasUniversallyTrivialPushforward p)
    (σ : S ⟶ Y) (hσ : σ ≫ q = 𝟙 S)
    {m : pullback p q ⟶ Z} (hm : m ≫ r = pullback.fst p q ≫ p)
    (c : S ⟶ Z) (hconst : sliceIncl p q σ hσ ≫ m = p ≫ c) :
    ∃ d : Y ⟶ Z, m = pullback.snd p q ≫ d := by
  refine exists_comp_snd_eq_of_forall_locallyFactors (r := r) hpush hm ?_
  intro y
  obtain ⟨V, g, hg, hy, R, j, n, hn⟩ :=
    hasAffineFactorizationAt_of_section (r := r) hpush σ hσ hm
      (fun s => hasAffineFactorizationAt_section σ hσ c hconst s) y
  obtain ⟨d', hd', -⟩ := existsUnique_comp_snd_eq_of_spec hpush n
  exact ⟨V, g, hg, hy, d' ≫ j, by rw [hn, hd', Category.assoc]⟩

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
