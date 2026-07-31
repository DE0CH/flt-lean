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
  statement under it, was PROVEN on 2026-07-31 over the two sorry leaves of this file,
  `Fermat.injective_liftBaseChange_h1Cotangent_of_formallySmooth` (the left end of the
  Jacobi–Zariski sequence for a formally smooth upper map) and
  `Fermat.projective_of_projective_tensorProduct_of_faithfullyFlat` (Raynaud–Gruson,
  Stacks `058B`).

Both are extracted from `Fermat/FLT/ModularCurve/X0.lean`, where the second is the
whole content of the `⊆` half of `smoothLocus_pairSquareMap` — the last obstruction
between `AbelianSchemeStruct` and "a surjective homomorphism of abelian schemes over
`ℚ` is smooth".  Extracting them puts the residual leaf in a 100-line module that
elaborates in seconds instead of inside an 80 000-line file, and states it in the
generality in which it is a `mathlib` statement rather than an `X0` one.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Fermat

open scoped TensorProduct

section Descent

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- **THE JACOBI–ZARISKI SEQUENCE EXTENDS TO THE LEFT WITH A ZERO WHEN THE UPPER MAP
IS FORMALLY SMOOTH** (sorry leaf, cut 2026-07-31 out of
`formallySmooth_of_comp_of_faithfullyFlat` below).  For `R → S → T` with `T` FLAT and
FORMALLY SMOOTH over `S`,

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

**WHAT IS MISSING, checked against the pin on 2026-07-31.**  Mathlib's Jacobi–Zariski
file (`Mathlib/RingTheory/Kaehler/JacobiZariski.lean`) proves exactness of

    T ⊗[S] H¹(L_{S/R}) →ˡᵇᶜ H¹(L_{T/R}) → H¹(L_{T/S})

at the MIDDLE term (`Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`, `[stacks
00S2]`) and stops there, because the NAIVE cotangent complex has no `H₂` to continue
with — the file's own header says as much.  So the missing input is either `H₂` of the
full cotangent complex (absent at this pin), or, in the snake-lemma presentation
mathlib actually uses, injectivity of

    T ⊗[S] P.Cotangent → (Q.comp P).Cotangent

for `P` a presentation of `S` over `R` and `Q` one of `T` over `S`.  That second form is
the cheaper target: with `T` formally smooth over `S` the presentation `Q` may be chosen
so that `Q.Cotangent → Q.CotangentSpace` is split injective, and the snake lemma then
delivers the whole left end.  Everything else in `formallySmooth_of_comp_of_faithfullyFlat`
is now proven over this one statement and over `Module.Projective`-descent below.

**`Algebra.FormallySmooth S T` IS LOAD-BEARING.**  Without it the statement is the flat
case of Stacks `02VL`, whose only known proof runs through *"`A → B` flat local of
Noetherian local rings, `B` regular ⟹ `A` regular"* (Stacks `00OJ`), i.e. through Serre's
criterion — which is at this pin in NEITHER direction.  See the deleted-block note in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothLocusPerfect.lean`. -/
theorem injective_liftBaseChange_h1Cotangent_of_formallySmooth
    [Module.Flat S T] [Algebra.FormallySmooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) :=
  sorry

/-- **PROJECTIVITY DESCENDS ALONG A FAITHFULLY FLAT RING MAP** (sorry leaf, cut
2026-07-31 out of `formallySmooth_of_comp_of_faithfullyFlat` below) — Raynaud–Gruson,
Stacks `058B`.

This is the SAME statement mathlib names as the obstruction to its own `proof_wanted`
`Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`
(`Mathlib/RingTheory/Etale/Descent.lean`), so it is a mathlib-facing target and not a
project-specific one.

**A cheaper escape, if a successor prefers it to Raynaud–Gruson.**  For a FINITELY
PRESENTED `M` the statement is elementary — projective ⟺ flat and finitely presented,
and flatness descends along a faithfully flat map — so adding
`[Module.FinitePresentation S M]` here discharges it without any of the hard theory.  The
consumer needs it at `M := Ω[S⁄R]`, and every `S` reaching it in this development is a
stalk of a scheme locally of finite presentation, hence essentially of finite
presentation over `R`.  Threading that hypothesis is an INTERFACE change through
`mem_smoothLocus_of_comp_of_smooth`, `mem_smoothLocus_of_commSq` and
`smoothLocus_pairSquareMap_le` in `Fermat/FLT/ModularCurve/X0.lean`, which is why it was
not done here; it is a legitimate and much smaller alternative to proving this leaf. -/
theorem projective_of_projective_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat S T] (M : Type*) [AddCommGroup M] [Module S M]
    [Module.Projective T (T ⊗[S] M)] :
    Module.Projective S M :=
  sorry

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
`projective_of_projective_tensorProduct_of_faithfullyFlat`) — the other half of
`formallySmooth_of_comp_of_faithfullyFlat`.

The Jacobi–Zariski sequence

    H¹(L_{T/S}) →ᵟ T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0

has `H¹(L_{T/S}) = 0` because `T` is formally smooth over `S`, so its left map is
INJECTIVE; and `Ω[T⁄S]` is projective for the same reason, so the surjection on the right
has a section and the short exact sequence SPLITS.  Hence `T ⊗[S] Ω[S⁄R]` is a direct
summand of `Ω[T⁄R]`, which is projective because `T` is formally smooth over `R`.  The
descent along `S → T` is the only step that is not mathlib. -/
theorem projective_kaehlerDifferential_of_faithfullyFlat
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

Build the residues in `Fermat/FLT/Mathlib/RingTheory/` rather than inline. -/
theorem formallySmooth_of_comp_of_faithfullyFlat {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    (hff : ψ.FaithfullyFlat) (hψ : ψ.FormallySmooth)
    (h : (ψ.comp φ).FormallySmooth) :
    φ.FormallySmooth := by
  algebraize [φ, ψ, ψ.comp φ]
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
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
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`). -/
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
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  rw [Scheme.Hom.stalkMap_comp] at hx
  exact formallySmooth_of_comp_of_faithfullyFlat _ _ hff hps hx

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
