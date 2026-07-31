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
  source") and it rests on the one sorry leaf of this file,
  `Fermat.formallySmooth_of_comp_of_faithfullyFlat`.

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

/-- **FORMAL SMOOTHNESS DESCENDS ALONG A FAITHFULLY FLAT, FORMALLY SMOOTH RING MAP**
(sorry leaf, cut 2026-07-30 out of `smoothLocus_pairSquareMap_le` in
`Fermat/FLT/ModularCurve/X0.lean`).

`R →φ S →ψ T` with `ψ` faithfully flat and formally smooth, and `ψ ∘ φ` formally
smooth: then `φ` is formally smooth.

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

**THE ROUTE, worked out on 2026-07-30 against the pin rather than left as "build a
theory".**  `mathlib` states formal smoothness as a SPLIT INJECTION, and splitting
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

**Why the pin's own `proof_wanted` is NOT evidence that this is out of reach.**
`Mathlib/RingTheory/Etale/Descent.lean` leaves the BASE CHANGE form open,
`Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`, noting it
needs Raynaud–Gruson descent of projectivity (Stacks `058B`) — because there `Ω[S⁄R]`
must be recovered as projective from `Ω[S⁄R] ⊗_S T` projective, with no formal
smoothness available in the middle.  Here `hψ` supplies the middle, the conclusion is
a SPLITTING rather than PROJECTIVITY, and splittings descend by step 2.  The two
statements look alike and their difficulty is not the same.

Build it in `Fermat/FLT/Mathlib/RingTheory/` rather than inline. -/
theorem formallySmooth_of_comp_of_faithfullyFlat {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T)
    (_hff : ψ.FaithfullyFlat) (_hψ : ψ.FormallySmooth)
    (_h : (ψ.comp φ).FormallySmooth) :
    φ.FormallySmooth :=
  sorry

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
