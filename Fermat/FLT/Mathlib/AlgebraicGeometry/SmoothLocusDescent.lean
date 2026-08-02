/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# The smooth locus along a composition

Two pointwise rules for `Scheme.Hom.smoothLocus`, one in each direction along a
composition `p ≫ f`, both of which `mathlib` states only in the GLOBAL form
(`Smooth` is stable under composition, and smoothness is fppf-local on the source).

* `Fermat.mem_smoothLocus_comp` — *postcomposition with a smooth morphism enlarges
  nothing*: if `p` is smooth at `x` and `f` is smooth, then `p ≫ f` is smooth at `x`.
  PROVEN: on stalks it is `RingHom.FormallySmooth.comp`.
* `Fermat.mem_smoothLocus_of_comp_of_smooth` — *smoothness DESCENDS along a smooth
  morphism*: if `p ≫ f` is smooth at `x` and `p` is smooth, then `f` is smooth at
  `p x`.  This is the pointwise form of Stacks `036M` ("smooth is fppf local on the
  source").  `Fermat.formallySmooth_of_comp_of_faithfullyFlat`, the ring-level
  statement under it, was PROVEN on 2026-07-31 over two sorry leaves.

Both are extracted from `Fermat/FLT/ModularCurve/X0.lean`, where the second is the
whole content of the `⊆` half of `smoothLocus_pairSquareMap` — the last obstruction
between `AbelianSchemeStruct` and "a surjective homomorphism of abelian schemes over
`ℚ` is smooth".  Extracting them puts the residual leaf in a 100-line module that
elaborates in seconds instead of inside an 80 000-line file, and states it in the
generality in which it is a `mathlib` statement rather than an `X0` one.

## The frontier of this file: ONE leaf, down from two on 2026-08-02

`Fermat.projective_of_projective_tensorProduct_of_faithfullyFlat` — the `Ω` half, and
the one that read as Raynaud–Gruson (Stacks `058B`) — was **CLOSED on 2026-08-02**, by
adding `[IsLocalRing S]` and `[Module.Finite S M]`, both of which the consumer chain
supplies for free.  `Fermat.projective_kaehlerDifferential_of_faithfullyFlat` is
therefore axiom-clean.  See that theorem's docstring for why neither hypothesis costs
anything and why no signature outside this file moved.

The single remaining leaf is
`Fermat.injective_liftBaseChange_h1Cotangent_of_formallySmooth`, the left end of the
Jacobi–Zariski sequence for a formally smooth upper map — i.e. `H₂(L_{T/S}) = 0`, which
the NAIVE cotangent complex mathlib carries at this pin cannot express.  Everything
else in this file is proven.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Fermat

open scoped TensorProduct

section Descent

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- `Algebra.H1Cotangent.map R R S T` computed against the COMPOSITE presentation
`(self S T).comp (self R S)` of `T` over `R`: it is the map induced by
`Generators.toComp`, followed by the comparison with `self R T`.

Both halves are `Algebra.Extension.H1Cotangent.map` of a `Hom` of extensions, and
`Extension.H1Cotangent.map_eq` says any two `Hom`s between the same two extensions induce
the same map — which is the whole proof, and the reason `H¹` may be computed against
whichever presentation is convenient. -/
theorem h1Cotangent_map_eq_comp :
    Algebra.H1Cotangent.map R R S T
      = (Algebra.Extension.H1Cotangent.map
          (Algebra.Generators.defaultHom
            ((Algebra.Generators.self S T).comp (Algebra.Generators.self R S))
            (Algebra.Generators.self R T)).toExtensionHom).restrictScalars S ∘ₗ
        Algebra.Extension.H1Cotangent.map
          ((Algebra.Generators.self S T).toComp
            (Algebra.Generators.self R S)).toExtensionHom := by
  rw [← Algebra.Extension.H1Cotangent.map_comp]
  exact Algebra.Extension.H1Cotangent.map_eq _ _

/-- Naturality of `Extension.h1Cotangentι` (`Extension.Cotangent.map_comp_h1Cotangentι`,
which is `rfl`) carried across the base change `- ⊗[S] T`: the `H¹` map into the composite
presentation is the restriction of the `Cotangent` map. -/
theorem key_h1Cotangentι_liftBaseChange
    (z : T ⊗[S] (Algebra.Generators.self R S).toExtension.H1Cotangent) :
    ((Algebra.Extension.Cotangent.map
        ((Algebra.Generators.self S T).toComp
          (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T)
        (LinearMap.lTensor T
          (Algebra.Extension.h1Cotangentι
            (P := (Algebra.Generators.self R S).toExtension)) z)
      = (((Algebra.Extension.H1Cotangent.map
          ((Algebra.Generators.self S T).toComp
            (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) z).1 := by
  induction z with
  | zero => simp
  | tmul t x => simp [LinearMap.liftBaseChange_tmul]
  | add x y hx hy => simp [hx, hy]

/-- **`T ⊗[S] I/I² → J/J²` IS INJECTIVE WHEN `T` IS FORMALLY SMOOTH OVER `S`**
(sorry leaf; **RECUT 2026-08-02** out of
`injective_liftBaseChange_h1Cotangent_of_formallySmooth` below, which is now PROVEN over
it — count unchanged, `1 → 1`).

Concretely, with `I = ker(R[X_S] ↠ S)` and `J = ker(R[Y_T, X_S] ↠ T)` the kernels of the
tautological presentations, this says

    IB ∩ J² = I²B + IB·J,        B = R[Y_T, X_S],

i.e. that the naive-complex row `T ⊗[S] P.Cotangent → (Q.comp P).Cotangent → Q.Cotangent → 0`
of `Algebra.Generators.Cotangent.exact` is exact **at the left** as well.

**IT IS EQUIVALENT TO THE STATEMENT IT REPLACES, and both directions are in this file**, so
the earlier leaf's faithfulness audit transfers with nothing to re-derive:

* `injective_liftBaseChange_h1Cotangent_of_formallySmooth` is proven over this one, and
* `injective_liftBaseChange_cotangent_toComp_of_injective_h1Cotangent` below proves the
  converse from the `H¹` statement as an explicit hypothesis (no circularity).

The mechanism of the converse is worth knowing, because it is what makes this a recut and
not a weakening: `Extension.CotangentSpace.map_toComp` is injective and
`map_comp_cotangentComplex_baseChange` commutes, so `ker u` already lies inside
`ker (T ⊗ P.cotangentComplex)`, which flatness identifies with `T ⊗ H¹(L_{S/R})`.  In other
words `ker u` IS the kernel of the `H¹` map — nothing else can be in it.

**WHAT WOULD CLOSE IT, and it is `H₂` however it is dressed.**  In the derived world
`ker u` is the image of `H₂(L_{T/S}) → H₁(L_{S/R} ⊗^L_S T)`, and `T` formally smooth over
`S` gives `L_{T/S} ≃ Ω_{T/S}[0]`, hence `H₂(L_{T/S}) = 0`.  At this pin there is no `H₂`:
mathlib has only the NAIVE cotangent complex (`Mathlib/RingTheory/Kaehler/JacobiZariski.lean`
says so in its own header, and its `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`
stops at exactness in the MIDDLE, `[stacks 00S2]`).  The naive-complex avatar of the missing
input is **quasi-regularity of `K = ker(S[Y] ↠ T)`** — `Sym_T(K/K²) ≅ gr_K(S[Y])` — which is
what a formally smooth `S → T` supplies (the sections `T → S[Y]/K^n`, built inductively from
`Algebra.FormallySmooth.iff_split_surjection`, each `S[Y]/K^{n+1} ↠ S[Y]/K^n` being a
square-zero extension of `S`-algebras).  That is a real development and it is the whole of
what is left here.

**THE PRESCRIBED ROUTE, and it deletes `R`, `I` and `B` from the problem** (worked out
2026-08-02; the reduction is elementary, only the last step is not).  Write
`B₂ := B/(I²B + IB·J)`, so that `N := IB/(I²B + IB·J) = T ⊗[S] I/I²` is the source of `u`,
`B₂/N = C := S[Y_T]`, `J₂ := J/(I²B + IB·J)` has `J₂/N = K := ker(C ↠ T)`, and
`ker u = N ∩ J₂²`.  Then:

* **`N·J₂ = 0` by construction** — that is exactly the `IB·J` we quotiented by.  So for
  `x, y ∈ J₂` the product `xy` is unchanged by moving `x` or `y` by an element of `N`, i.e.
  multiplication FACTORS through `K × K`;
* the resulting `μ : K × K → J₂²` is symmetric and `C`-bilinear (`N·J₂² ⊆ N·J₂ = 0`, so
  `J₂²` is a `C`-module) and surjective, giving `Sym²_C(K) ↠ J₂² ↠ K²` whose composite is
  the multiplication of `C`;
* hence **`ker u` is a quotient of `ker (Sym²_C K → K²)`**, and it is enough to prove

      the multiplication  Sym²_C(K) ⟶ K²  is INJECTIVE

  for `C = S[Y_T]`, `K = ker(C ↠ T)` and `S → T` formally smooth — an ideal-of-linear-type
  statement in which `R`, `I` and `B` do not occur at all.  It is what quasi-regularity of
  `K` buys (an ideal generated by a regular sequence is of linear type; the formally smooth
  case is the quasi-regular one), and it is the honest remaining input.

**THREE THINGS THAT WERE CHECKED AND DO NOT WORK** (2026-08-02), recorded so they are not
re-tried:

* *"`Q.Cotangent` is projective, so the row splits on the right"* — true (`FormallySmooth S T`
  makes `Q.cotangentComplex` split injective into the free `Q.CotangentSpace`, by
  `Algebra.Extension.formallySmooth_iff_split_injection`), and it gives
  `(Q.comp P).Cotangent ≅ im u ⊕ Q.Cotangent`, which says nothing about `ker u`.
* *"descend split injectivity of the cotangent complex along the faithfully flat `S → T`"* —
  the 2026-07-30 route, still the right shape for the `Ω` half.  For the `H¹` half it is
  CIRCULAR: a retraction of `T ⊗ P.cotangentComplex` would have to be assembled out of a
  retraction of `u`, and `u` is what is being proven injective.
* *"add `[Algebra.FormallySmooth R T]`, which the only consumer has anyway"* — that makes
  the leaf **equivalent to the consumer's own conclusion** and so buys nothing: with
  `H¹(L_{T/R}) = 0` one gets `ker u = T ⊗ H¹(L_{S/R})` on the nose, and `u` injective then
  says exactly `T ⊗ H¹(L_{S/R}) = 0`.  Do not add it.

**`Algebra.FormallySmooth S T` IS LOAD-BEARING.**  Without it the statement is the flat
case of Stacks `02VL`, whose only known proof runs through *"`A → B` flat local of
Noetherian local rings, `B` regular ⟹ `A` regular"* (Stacks `00OJ`), i.e. through Serre's
criterion — which is at this pin in NEITHER direction.  See the deleted-block note in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothLocusPerfect.lean`.

`[Module.Flat S T]` is kept because the consumer has it and because it is what makes the
converse above go through; it is not known to be needed for truth. -/
theorem injective_liftBaseChange_cotangent_toComp_of_formallySmooth
    [Module.Flat S T] [Algebra.FormallySmooth S T] :
    Function.Injective
      ((Algebra.Extension.Cotangent.map
          ((Algebra.Generators.self S T).toComp
            (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) :=
  sorry

/-- **THE JACOBI–ZARISKI SEQUENCE EXTENDS TO THE LEFT WITH A ZERO WHEN THE UPPER MAP
IS FORMALLY SMOOTH** (**PROVEN 2026-08-02** over
`injective_liftBaseChange_cotangent_toComp_of_formallySmooth` above; the leaf it used to be
was cut 2026-07-31 out of `formallySmooth_of_comp_of_faithfullyFlat` below).  For
`R → S → T` with `T` FLAT and FORMALLY SMOOTH over `S`,

    T ⊗[S] H¹(L_{S/R}) → H¹(L_{T/R})

is INJECTIVE.

**Why it is VOUCHED.**  In the derived world the transitivity triangle
`L_{S/R} ⊗^L_S T → L_{T/R} → L_{T/S}` gives a long exact sequence

    H₂(L_{T/S}) → H₁(L_{S/R} ⊗^L_S T) → H₁(L_{T/R}) → H₁(L_{T/S}) → …

`T` flat over `S` collapses `L_{S/R} ⊗^L_S T` to `L_{S/R} ⊗_S T`, so its `H₁` is
`T ⊗_S H₁(L_{S/R})` — that is precisely the hypothesis under which mathlib proves
`Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`.  `T` formally smooth over `S`
makes `L_{T/S}` a projective module in degree `0`, so `H₂(L_{T/S}) = 0` and the map is
injective.

**THE PROOF, and why it moves the obligation into the naive complex.**  `H1Cotangent` is
independent of the presentation, so the map may be computed against the composite
presentation `Q.comp P` of `T` over `R`, where `Q = Generators.self S T` and
`P = Generators.self R S`; `Algebra.Extension.H1Cotangent.map_eq` (any two homs between two
extensions induce the same map) is what licenses the substitution, and the comparison with
`Generators.self R T` is the isomorphism `Algebra.Generators.H1Cotangent.equiv`.  There,
`h1Cotangentι` is natural (`Extension.Cotangent.map_comp_h1Cotangentι`, which is `rfl`), so
the `H¹` map sits inside the `Cotangent` map after tensoring with the injective
`T ⊗ h1Cotangentι` — injective because `T` is flat over `S`.  Everything about the
geometry has moved into the leaf above. -/
theorem injective_liftBaseChange_h1Cotangent_of_formallySmooth
    [Module.Flat S T] [Algebra.FormallySmooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  classical
  -- the naive-complex map is injective: that is the leaf
  have hu := injective_liftBaseChange_cotangent_toComp_of_formallySmooth R S T
  -- `T ⊗ h1Cotangentι` is injective, by flatness
  have hflat : Function.Injective
      (LinearMap.lTensor T (Algebra.Extension.h1Cotangentι
        (P := (Algebra.Generators.self R S).toExtension))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      Algebra.Extension.h1Cotangentι_injective
  -- hence the `H¹` map into the composite presentation is injective
  have hι : Function.Injective
      ((Algebra.Extension.H1Cotangent.map
        ((Algebra.Generators.self S T).toComp
          (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) := by
    intro a b hab
    refine hflat (hu ?_)
    rw [key_h1Cotangentι_liftBaseChange R S T a,
      key_h1Cotangentι_liftBaseChange R S T b, hab]
  -- and `Algebra.H1Cotangent.map R R S T` is that map followed by an isomorphism
  rw [h1Cotangent_map_eq_comp R S T, ← LinearMap.liftBaseChange_comp]
  exact (Algebra.Generators.H1Cotangent.equiv
    ((Algebra.Generators.self S T).comp (Algebra.Generators.self R S))
    (Algebra.Generators.self R T)).injective.comp hι

/-- **THE CONVERSE, i.e. the receipt that the recut above is faithful.**  Injectivity of
`T ⊗[S] H¹(L_{S/R}) → H¹(L_{T/R})` implies injectivity of `T ⊗[S] I/I² → J/J²`, so the two
statements are EQUIVALENT under `[Module.Flat S T]` and nothing was strengthened when the
leaf moved from one to the other.

The hypothesis is taken explicitly rather than as an instance, so there is no circularity
with `injective_liftBaseChange_h1Cotangent_of_formallySmooth` above: this is a genuine
implication between two propositions, and `Algebra.FormallySmooth S T` does not appear.

`ker u` cannot be bigger than the kernel of the `H¹` map, because
`Algebra.Generators.CotangentSpace.map_toComp_injective` and
`Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange` force every element
of `ker u` into `ker (T ⊗ P.cotangentComplex)`, which flatness identifies with
`T ⊗[S] H¹(L_{S/R})` via `Module.Flat.lTensor_exact`. -/
theorem injective_liftBaseChange_cotangent_toComp_of_injective_h1Cotangent
    [Module.Flat S T]
    (h : Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)) :
    Function.Injective
      ((Algebra.Extension.Cotangent.map
          ((Algebra.Generators.self S T).toComp
            (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) := by
  classical
  rw [h1Cotangent_map_eq_comp R S T, ← LinearMap.liftBaseChange_comp,
    LinearMap.coe_comp] at h
  have hι : Function.Injective
      ((Algebra.Extension.H1Cotangent.map
        ((Algebra.Generators.self S T).toComp
          (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) :=
    h.of_comp
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  -- `z` dies in the cotangent SPACE, hence comes from `T ⊗ H¹`
  have hzCS : (Algebra.Generators.self R S).toExtension.cotangentComplex.baseChange T z = 0 := by
    apply Algebra.Generators.CotangentSpace.map_toComp_injective
      (Algebra.Generators.self S T) (Algebra.Generators.self R S)
    rw [map_zero, ← LinearMap.comp_apply,
      Algebra.Generators.H1Cotangent.map_comp_cotangentComplex_baseChange,
      LinearMap.comp_apply, hz, map_zero]
  rw [LinearMap.baseChange_eq_ltensor, ← LinearMap.mem_ker,
    (Module.Flat.lTensor_exact T
      (Algebra.Generators.self R S).toExtension.exact_hCotangentι_cotangentComplex
        ).linearMap_ker_eq] at hzCS
  obtain ⟨w, rfl⟩ := hzCS
  rw [key_h1Cotangentι_liftBaseChange R S T w] at hz
  have hw0 : ((Algebra.Extension.H1Cotangent.map
      ((Algebra.Generators.self S T).toComp
        (Algebra.Generators.self R S)).toExtensionHom).liftBaseChange T) w = 0 :=
    Subtype.ext hz
  have hw : w = 0 := hι (by rw [hw0, map_zero])
  rw [hw, map_zero]

/-- **PROJECTIVITY DESCENDS ALONG A FAITHFULLY FLAT RING MAP, OVER A LOCAL BASE**
(**PROVEN 2026-08-02**; was a sorry leaf from 2026-07-31 to 2026-08-02, cut out of
`formallySmooth_of_comp_of_faithfullyFlat` below).

Over a LOCAL `S` and for a FINITE `M` this is three lines and Raynaud–Gruson is not
needed:

* `T ⊗[S] M` projective over `T` is in particular FLAT over `T`
  (`Module.Flat.of_projective`);
* flatness DESCENDS along a faithfully flat ring map
  (`Module.Flat.of_flat_tensorProduct`), so `M` is flat over `S`;
* over a local ring a FINITE FLAT module is FREE — Stacks `00NZ`,
  `Module.free_of_flat_of_isLocalRing` — hence projective.

**WHY THE TWO ADDED HYPOTHESES COST NOTHING, and this is the whole point of the
2026-08-02 recut.**  The docstring that stood here priced the escape at
`[Module.FinitePresentation S M]` and recorded, correctly for that hypothesis, that
threading it would be an INTERFACE change through `mem_smoothLocus_of_comp_of_smooth`,
`mem_smoothLocus_of_commSq` and `smoothLocus_pairSquareMap_le` in
`Fermat/FLT/ModularCurve/X0.lean`.  Both halves of that estimate are avoidable:

* **`Module.Finite` suffices, not `Module.FinitePresentation`**, precisely *because*
  `S` is local — `Module.Flat.projective_of_finitePresentation` wants finite
  presentation over an arbitrary ring, but `Module.free_of_flat_of_isLocalRing` wants
  only `Module.Finite` over a local one;
* **and both hypotheses are discharged INSIDE THIS FILE**, at
  `mem_smoothLocus_of_comp_of_smooth`, whose `[LocallyOfFinitePresentation f]` was
  already there.  A stalk of a scheme is a local ring, and
  `AlgebraicGeometry.LocallyOfFiniteType.stalkMap` makes the stalk map essentially of
  finite type, whence `Module.Finite S Ω[S⁄R]` by the INSTANCE
  `KaehlerDifferential.finite`.  **So no signature outside this file moved**, and
  `X0.lean` was not touched.

**WHAT THIS DEVELOPMENT NO LONGER OWES.**  The general form — no hypothesis on `S`, no
finiteness on `M` — is Raynaud–Gruson, Stacks `058B`, and is the same statement mathlib
names as the obstruction to its own `proof_wanted`
`Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`
(`Mathlib/RingTheory/Etale/Descent.lean`).  It is a fine mathlib target and **nothing in
this project needs it**: the sole consumer chain here is
`projective_kaehlerDifferential_of_faithfullyFlat` →
`formallySmooth_of_comp_of_faithfullyFlat` → `mem_smoothLocus_of_comp_of_smooth`, and
that chain's own hypotheses supply both of the additions.  What would put the general
form back on the frontier is a consumer with a NON-LOCAL `S`, or one applying it to a
module that is not finite over `S`; there is none today, and a successor who introduces
one should re-cut the leaf rather than weaken this statement. -/
theorem projective_of_projective_tensorProduct_of_faithfullyFlat
    [IsLocalRing S] [Module.FaithfullyFlat S T] (M : Type*) [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module.Projective T (T ⊗[S] M)] :
    Module.Projective S M := by
  have : Module.Flat S M := Module.Flat.of_flat_tensorProduct S M T
  have : Module.Free S M := Module.free_of_flat_of_isLocalRing
  infer_instance

/-- **`H¹(L_{S/R}) = 0` DESCENDS** (PROVEN 2026-07-31 over
`injective_liftBaseChange_h1Cotangent_of_formallySmooth`) — half of
`formallySmooth_of_comp_of_faithfullyFlat`.

`T ⊗[S] H¹(L_{S/R})` injects into `H¹(L_{T/R})`, which vanishes because `T` is formally
smooth over `R`; and a faithfully flat base change reflects triviality
(`Module.FaithfullyFlat.lTensor_reflects_triviality`). -/
theorem subsingleton_h1Cotangent_of_faithfullyFlat
    [Module.FaithfullyFlat S T] [Algebra.FormallySmooth S T] [Algebra.FormallySmooth R T] :
    Subsingleton (Algebra.H1Cotangent R S) := by
  have hinj := injective_liftBaseChange_h1Cotangent_of_formallySmooth R S T
  haveI : Subsingleton (T ⊗[S] Algebra.H1Cotangent R S) :=
    ⟨fun _ _ => hinj (Subsingleton.elim _ _)⟩
  exact Module.FaithfullyFlat.lTensor_reflects_triviality S T (Algebra.H1Cotangent R S)

/-- **PROJECTIVITY OF `Ω[S⁄R]` DESCENDS** (PROVEN 2026-07-31 over
`projective_of_projective_tensorProduct_of_faithfullyFlat`, which is itself PROVEN
since 2026-08-02, so this theorem is now **axiom-clean**) — the other half of
`formallySmooth_of_comp_of_faithfullyFlat`.

`[IsLocalRing S]` and `[Algebra.EssFiniteType R S]` were added on 2026-08-02.  They are
what `projective_of_projective_tensorProduct_of_faithfullyFlat` consumes: the second
gives `Module.Finite S Ω[S⁄R]` by the instance `KaehlerDifferential.finite`.  Both are
free at the point of use — see that theorem's docstring — so no consumer moved.

The Jacobi–Zariski sequence

    H¹(L_{T/S}) →ᵟ T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0

has `H¹(L_{T/S}) = 0` because `T` is formally smooth over `S`, so its left map is
INJECTIVE; and `Ω[T⁄S]` is projective for the same reason, so the surjection on the right
has a section and the short exact sequence SPLITS.  Hence `T ⊗[S] Ω[S⁄R]` is a direct
summand of `Ω[T⁄R]`, which is projective because `T` is formally smooth over `R`.  The
descent along `S → T` is the only step that is not mathlib. -/
theorem projective_kaehlerDifferential_of_faithfullyFlat
    [IsLocalRing S] [Algebra.EssFiniteType R S]
    [Module.FaithfullyFlat S T] [Algebra.FormallySmooth S T] [Algebra.FormallySmooth R T] :
    Module.Projective S (Ω[S⁄R]) := by
  -- `H¹(L_{T/S}) = 0` makes the base-change map injective
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    intro x y hxy
    have hx : KaehlerDifferential.mapBaseChange R S T (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T (x - y)).mp hx
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  -- `Ω[T⁄S]` is projective, so the surjection `Ω[T⁄R] ↠ Ω[T⁄S]` has a section
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property
    (KaehlerDifferential.map R S T T) (LinearMap.id (R := T) (M := Ω[T⁄S]))
    (KaehlerDifferential.map_surjective (R := R) (S := S) (B := T))
  -- hence the short exact sequence splits and the base-change map is split injective
  obtain ⟨ret, hret⟩ :=
    (((KaehlerDifferential.exact_mapBaseChange_map R S T).split_tfae hinj
      (KaehlerDifferential.map_surjective (R := R) (S := S) (B := T))).out 0 1 rfl rfl).mp
      ⟨sec, hsec⟩
  haveI : Module.Projective T (T ⊗[S] Ω[S⁄R]) :=
    Module.Projective.of_split (KaehlerDifferential.mapBaseChange R S T) ret hret
  exact projective_of_projective_tensorProduct_of_faithfullyFlat S T (Ω[S⁄R])

end Descent

/-- **FORMAL SMOOTHNESS DESCENDS ALONG A FAITHFULLY FLAT, FORMALLY SMOOTH RING MAP**
(cut 2026-07-30 out of `smoothLocus_pairSquareMap_le` in
`Fermat/FLT/ModularCurve/X0.lean`; **PROVEN 2026-07-31** over the two leaves
`injective_liftBaseChange_h1Cotangent_of_formallySmooth` and
`projective_of_projective_tensorProduct_of_faithfullyFlat` above).

`R →φ S →ψ T` with `ψ` faithfully flat and formally smooth, and `ψ ∘ φ` formally
smooth: then `φ` is formally smooth.

**WHAT THE 2026-07-31 CUT DID, and why it is a `1 → 2` trade worth making.**  At this
pin `Algebra.FormallySmooth R S` is *by definition* the conjunction

    Module.Projective S Ω[S⁄R]   ∧   Subsingleton (Algebra.H1Cotangent R S)

(`Mathlib/RingTheory/Smooth/Basic.lean`, `Algebra.formallySmooth_iff`), so the leaf
splits along that conjunction with nothing left over, and each half descends by a
DIFFERENT mechanism:

* the `H¹` half is the left end of the Jacobi–Zariski sequence, and needs only that
  `H₂(L_{T/S}) = 0` — the residue is
  `injective_liftBaseChange_h1Cotangent_of_formallySmooth`;
* the `Ω` half is the splitting of `0 → T ⊗_S Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0`, which is
  fully proven here, followed by descent of PROJECTIVITY along `S → T` — the residue is
  `projective_of_projective_tensorProduct_of_faithfullyFlat`, i.e. Raynaud–Gruson.

Both residues are statements a mathlib contributor would recognise and neither mentions
a scheme, a stalk or anything from this development.  The count went `1 → 2`; what
changed is that no glue is left in either.

**WHY THE STATEMENT IS VOUCHED.**  It is the ring-level form of Stacks `036M`,
"the property *smooth* is fppf local on the source": if `g : X' → X` is flat,
locally of finite presentation and surjective and `f ∘ g` is smooth, then `f` is
smooth.  `ψ` faithfully flat is the local avatar of "flat and surjective", and
`ψ` formally smooth is the avatar of "locally of finite presentation" that keeps
the statement inside the formal theory.  **The formal smoothness of `ψ` is NOT
decoration**: descent of formal smoothness along a merely flat map is not a
statement this file is willing to promise, because the Jacobi–Zariski argument
needs the middle map to contribute a split cotangent complex, and the naive
`H₁(L_{T/R}) = 0` alone does not force `H₁(L_{S/R}) = 0` without it.

A NON-EXAMPLE showing faithful flatness alone is not the whole content, i.e. that
one may not drop `hψ` and reason "`T` is nice, so `S` is": take `R = k`,
`S = k[x]/(x²)`, and ask for a faithfully flat `S`-algebra `T` formally smooth over
`k`.  Such a `T` cannot exist — `T` is then geometrically regular over `k`, hence
reduced, while faithful flatness forces `x ≠ 0` in `T` and `x² = 0` — which is
exactly why the theorem is TRUE and simultaneously why no cheap argument reaches
it: every route passes through a regularity statement about `T`.

**THE ROUTE RECORDED ON 2026-07-30, KEPT BECAUSE ITS STEP 2 IS STILL THE CHEAPEST
ESCAPE FROM THE `Ω` RESIDUE — but its final paragraph was WRONG and is corrected
below.**  `mathlib` states formal smoothness as a SPLIT INJECTION, and splitting
is exactly what descends along a faithfully flat map — so the shape of the proof is
fixed, and only one step of it is heavy.

1. *The criterion.*  `Algebra.Extension.formallySmooth_iff_split_injection`
   (`Mathlib/RingTheory/Smooth/Basic.lean`) says: for a presentation `P` of `S` over
   `R`, `FormallySmooth R S` iff `P.cotangentComplex : P.Cotangent → S ⊗_P Ω[P⁄R]` is
   a SPLIT injection of `S`-modules.
2. *Descent of splitting is elementary, and this is the step that makes the theorem
   reachable at all.*  For `u : M → N` of `S`-modules with `M`, `N` finitely
   presented, `u` splits iff `𝟙 M` lies in the image of
   `φ : Hom_S(N, M) → Hom_S(M, M)`, `r ↦ r ∘ u`.  Base change along a FLAT `S → T`
   commutes with `Hom` out of a finitely presented module and with taking images, so
   `𝟙 M ⊗ 1` lies in `(im φ) ⊗_S T`; and for `S → T` FAITHFULLY flat the unit
   `Q → Q ⊗_S T` is injective on every `S`-module `Q`, applied to
   `Q := Hom_S(M, M)/im φ`.  Hence `u` splits.  No Raynaud–Gruson anywhere.  (This
   is the same move `IsLocalRing.split_injective_iff_lTensor_residueField_injective`
   makes against the residue field, and `Mathlib/RingTheory/Smooth/Local.lean` uses
   it for the Jacobian criteria.)
3. *Jacobi–Zariski, and this is the real work.*  What remains is to produce, from a
   presentation of `T` over `R`, the base change to `T` of a presentation of `S` over
   `R` as a DIRECT SUMMAND — which is where `hψ` is spent: `S → T` formally smooth
   makes `Ω[T⁄S]` projective and `H₁(L_{T⁄S}) = 0`, so the transitivity sequence
   `0 → T ⊗_S Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0` splits and the cotangent complex of
   `T/R` decomposes accordingly.  Split-injectivity of `T`'s complex then gives
   split-injectivity of `S`'s complex after `⊗_S T`, and step 2 removes the `T`.

**Finiteness is the trap in step 2** and must be handled, not assumed: `P.Cotangent`
is not finitely presented for an arbitrary presentation.  The two honest repairs are
to run the argument for a FINITELY PRESENTED presentation (available at the point of
use — every stalk map this file feeds it is a localisation of a map locally of finite
presentation), or to strengthen `hff` to what the `Hom` base-change actually needs.
A worker may therefore find it cheaper to prove the ESSENTIALLY-OF-FINITE-TYPE case
and add that hypothesis here; the consumers in
`Fermat/FLT/ModularCurve/X0.lean` all have it.

**CORRECTION (2026-07-31), and it is the one factual error in the paragraph above.**
The 2026-07-30 note ended: *"`Mathlib/RingTheory/Etale/Descent.lean` leaves the BASE
CHANGE form open … noting it needs Raynaud–Gruson descent of projectivity (Stacks
`058B`) — because there `Ω[S⁄R]` must be recovered as projective from `Ω[S⁄R] ⊗_S T`
projective, with no formal smoothness available in the middle.  Here `hψ` supplies the
middle, the conclusion is a SPLITTING rather than PROJECTIVITY, and splittings descend
by step 2 … No Raynaud–Gruson anywhere."*

The diagnosis of mathlib's `proof_wanted` is right; the inference is not.  At this pin
the CONCLUSION is not a splitting: `Algebra.FormallySmooth` is *defined* as
`Module.Projective S Ω[S⁄R] ∧ Subsingleton (H1Cotangent R S)`, so the projectivity has
to be produced literally, and `hψ` buys the SPLITTING of the Jacobi–Zariski sequence
(hence projectivity of `T ⊗_S Ω[S⁄R]` over `T`) and nothing more.  Recovering
`Module.Projective S Ω[S⁄R]` from that IS Stacks `058B`.

So Raynaud–Gruson does appear — **unless** step 2's finiteness route is taken: for a
finitely presented `M`, `Module.Projective` is `Module.Flat` plus finite presentation
(`Module.Flat.projective_of_finitePresentation`), and flatness descends along a
faithfully flat map by the ideal criterion.  That is why
`projective_of_projective_tensorProduct_of_faithfullyFlat` carries an explicit note
saying a `[Module.FinitePresentation S M]` hypothesis discharges it cheaply, at the
price of threading essential finite presentation of the stalk maps through
`mem_smoothLocus_of_comp_of_smooth` and its consumers in `X0.lean`.

**SECOND CORRECTION (2026-08-02), and it CLOSED the `Ω` residue.**  The finiteness route
above was taken, and both halves of its stated price turned out to be avoidable, so
Raynaud–Gruson does NOT appear anywhere in this file:

* the right hypothesis is `[IsLocalRing S]` plus `Module.Finite S M`, not
  `Module.FinitePresentation S M`.  `S` here is always a STALK, so it is local, and over
  a local ring `Module.free_of_flat_of_isLocalRing` (Stacks `00NZ`) turns finite + flat
  into FREE with no finite-presentation hypothesis at all;
* and nothing had to be threaded into `X0.lean`, because
  `mem_smoothLocus_of_comp_of_smooth` **already carried
  `[LocallyOfFinitePresentation f]`**, which gives `LocallyOfFiniteType f`, hence
  `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`, hence `Algebra.EssFiniteType R S`,
  hence `Module.Finite S Ω[S⁄R]` by the instance `KaehlerDifferential.finite`.  The two
  new binders are discharged inside this file and every signature below is unchanged.

The generalisable reading: *the docstring above priced the escape against the hypothesis
it happened to name (`FinitePresentation`) and against the interface change that
hypothesis would have needed.  Neither was a property of the statement — the first was
an artefact of not noticing `S` is local, the second of not reading the consumer's own
binder list.*  Both checks cost one `grep` each.

`φ` essentially of finite type is therefore a genuine hypothesis of this theorem now.
It is not decoration: without some finiteness on `Ω[S⁄R]` the `Ω` half is exactly Stacks
`058B` again.

Build the residues in `Fermat/FLT/Mathlib/RingTheory/` rather than inline. -/
theorem formallySmooth_of_comp_of_faithfullyFlat {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [IsLocalRing S] (φ : R →+* S) (ψ : S →+* T)
    (hff : ψ.FaithfullyFlat) (hψ : ψ.FormallySmooth) (hef : φ.EssFiniteType)
    (h : (ψ.comp φ).FormallySmooth) :
    φ.FormallySmooth := by
  algebraize [φ, ψ, ψ.comp φ]
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType R S := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]; exact hef
  exact ⟨projective_kaehlerDifferential_of_faithfullyFlat R S T,
    subsingleton_h1Cotangent_of_faithfullyFlat R S T⟩

/-- **POSTCOMPOSING WITH A SMOOTH MORPHISM PRESERVES THE SMOOTH LOCUS POINTWISE**
(PROVEN 2026-07-30) — `Smooth` is stable under composition in `mathlib`, but the
pointwise statement about `Scheme.Hom.smoothLocus` is not there.

On stalks `(p ≫ f).stalkMap x = f.stalkMap (p x) ≫ p.stalkMap x`, so this is
`RingHom.FormallySmooth.comp` together with `Scheme.Hom.smoothLocus_eq_top` for the
smooth factor. -/
theorem mem_smoothLocus_comp {X Y Z : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [LocallyOfFinitePresentation p] [Smooth f] {x : X}
    (hx : x ∈ p.smoothLocus) :
    x ∈ (p ≫ f).smoothLocus := by
  have hf : (f.stalkMap (p x)).hom.FormallySmooth := by
    have : p x ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
    exact this
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  rw [Scheme.Hom.stalkMap_comp]
  exact hf.comp hx

/-- **SMOOTHNESS DESCENDS ALONG A SMOOTH MORPHISM, POINTWISE** (PROVEN 2026-07-30
over `formallySmooth_of_comp_of_faithfullyFlat` above) — the pointwise form of
Stacks `036M`.  If `p ≫ f` is smooth at `x` and `p` is smooth, then `f` is smooth
at `p x`.

Surjectivity of `p` is NOT needed: the point `x` lying over `p x` is all the
faithfulness the stalk-level statement consumes, because a flat LOCAL homomorphism
of local rings is automatically faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`).

**THE SIGNATURE IS UNCHANGED BY THE 2026-08-02 RECUT**, and that is why that recut cost
nothing downstream: `formallySmooth_of_comp_of_faithfullyFlat` gained `[IsLocalRing S]`
and `φ.EssFiniteType`, and both are discharged HERE — a stalk of a scheme is a local
ring, and `[LocallyOfFinitePresentation f]`, which this theorem already required, gives
`LocallyOfFiniteType f` and hence `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`. -/
theorem mem_smoothLocus_of_comp_of_smooth {X Y Z : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Smooth p] [LocallyOfFinitePresentation f] {x : X}
    (hx : x ∈ (p ≫ f).smoothLocus) :
    p x ∈ f.smoothLocus := by
  -- the stalk map of `p` at `x` is faithfully flat, being flat and local
  have hff : (p.stalkMap x).hom.FaithfullyFlat := by
    algebraize [(p.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap p x) (p.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›
  -- and it is formally smooth, `p` being smooth
  have hps : (p.stalkMap x).hom.FormallySmooth := by
    have : x ∈ p.smoothLocus := by rw [p.smoothLocus_eq_top]; trivial
    exact this
  -- and `f` is locally of finite presentation, so its stalk map is essentially of
  -- finite type — which is what makes `Ω[S⁄R]` a FINITE module over the local ring `S`
  have hef : (f.stalkMap (p x)).hom.EssFiniteType :=
    LocallyOfFiniteType.stalkMap f (p x)
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  rw [Scheme.Hom.stalkMap_comp] at hx
  exact formallySmooth_of_comp_of_faithfullyFlat _ _ hff hps hef hx

/-- Transport of the smooth locus along an equality of morphisms — the
universe-polymorphic twin of `smoothLocus_congr` in `Fermat/FLT/ModularCurve/X0.lean`,
which is stated only at `Scheme.{0}`. -/
theorem smoothLocus_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    f.smoothLocus = g.smoothLocus := by
  cases h; rfl

/-- **THE SMOOTH LOCUS ACROSS A COMMUTATIVE SQUARE** (PROVEN 2026-07-30) — the two
lemmas above run together once, so that a consumer pays for a single application
instead of a `mem_smoothLocus_comp`, a rewrite and a descent.

Given `p ≫ g = q ≫ f` with `g` and `q` smooth: if `p` is smooth at `w`, then `f` is
smooth at `q w`.  Concretely — the shape every consumer has — `p` and `q` are the two
edges out of a fibre-product corner, `g` is a base change of the target's structure
morphism and `f` is the morphism whose smooth locus is wanted. -/
theorem mem_smoothLocus_of_commSq {W X Y Z : Scheme.{u}} (p : W ⟶ X) (g : X ⟶ Z)
    (q : W ⟶ Y) (f : Y ⟶ Z) (hcomm : p ≫ g = q ≫ f)
    [LocallyOfFinitePresentation p] [Smooth g] [Smooth q] [LocallyOfFinitePresentation f]
    {w : W} (hw : w ∈ p.smoothLocus) :
    q w ∈ f.smoothLocus := by
  have h1 : w ∈ (p ≫ g).smoothLocus := mem_smoothLocus_comp p g hw
  rw [smoothLocus_eq_of_eq hcomm] at h1
  exact mem_smoothLocus_of_comp_of_smooth q f h1

end Fermat
