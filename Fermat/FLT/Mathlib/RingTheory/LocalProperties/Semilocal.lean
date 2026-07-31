/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-!
# A criterion for a ring to be semilocal, and the freeness criterion it unlocks

Material destined for Mathlib, mirroring `Mathlib/RingTheory/LocalProperties/Semilocal.lean`
(where "semilocal" is spelled `[Finite (MaximalSpectrum R)]`).

Mathlib has the semilocal freeness criterion `Module.free_of_flat_of_finrank_eq` /
`Module.nonempty_basis_of_flat_of_finrank_eq` (Stacks 02M9) but **no way to produce its
`[Finite (MaximalSpectrum R)]` hypothesis from a local base**, which is by far the commonest
source of semilocal rings in practice: a finite algebra over a local ring. This file supplies

* `finite_maximalSpectrum_of_isLocalRing_of_module_finite` — a finite algebra over a local ring
  is semilocal;
* `Module.nonempty_basis_of_flat_of_finrank_eq_of_isLocalRing_base` — Stacks 02M9 phrased over a
  local BASE ring rather than over a semilocal ring, i.e. the composite that the consumer of the
  mathlib criterion in this development was assembling by hand.

There is deliberately no `Module.free_of_flat_of_finrank_eq_of_isLocalRing_base` beside it, even
though it is two lines: nothing consumes it, and this project forbids free-floating declarations.
Add it in the commit that first needs it.

## Provenance

The first was MOVED here (2026-07-31) from
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean`, where it was proven at the root
namespace inside a Hopf-algebra file only because that is where it was first needed. There is
deliberately **no copy left behind**: a declaration living in two modules one of which imports
the other is a hard `has already been declared` error, and is the failure mode CLAUDE.md's
seventh invisibility class describes. The second is new, and is exactly the three-step assembly
that `HopfAlgebra.IsShortExact.nonempty_basis_chooseBasisIndex_cartierDual` was performing
inline.
-/

@[expose] public section

open TensorProduct

/-- **A finite algebra over a local ring is semilocal.**

Proof: `S` is integral over `R`, so every maximal ideal of `S` contracts to a maximal ideal of
`R`, which is `𝔪`; hence every maximal ideal of `S` contains `I = 𝔪 · S`, and `P ↦ P.map (mk I)`
is an injection of `MaximalSpectrum S` into `MaximalSpectrum (S ⧸ I)`. And `S ⧸ I` is a finite
algebra over the field `R ⧸ 𝔪`, hence an artinian ring, which has finitely many maximal ideals.

This cannot be an `instance`: `R` occurs in no hypothesis of the conclusion, so instance search
has nothing to unify it against. Consumers that want it as one should write
`haveI := finite_maximalSpectrum_of_isLocalRing_of_module_finite R S`, or — better — go through
`Module.nonempty_basis_of_flat_of_finrank_eq_of_isLocalRing_base` below, which is what wanting it
almost always means.

TWO INSTANCE TRAPS, both of which cost a build cycle when this was first written and neither of
which is visible in the statement:

* `IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R)` does **not** synthesise from a plain
  `haveI : Field _ := Ideal.Quotient.field _` — the `Ring` structure the `Field` carries is a
  different instance path from the canonical `Ideal.Quotient.commRing`, and the mismatch surfaces
  much later as `synthesized type class instance is not definitionally equal`. The working form
  is `letI : Field _ := fast_instance% Ideal.Quotient.field _`, scoped inside the `haveI` block
  so it cannot leak.
* `IsField (S ⧸ P.asIdeal)` must come from `Ideal.Quotient.maximal_ideal_iff_isField_quotient`
  rather than from a local `Field` instance, or the `MulEquiv.isField` application below hits the
  same diamond. -/
theorem finite_maximalSpectrum_of_isLocalRing_of_module_finite
    (R : Type*) (S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  classical
  set I : Ideal S := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) with hI
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hle : ∀ P : Ideal S, P.IsMaximal → I ≤ P := by
    intro P hP
    haveI := hP
    have hcm : (P.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) P
    rw [hI, Ideal.map_le_iff_le_comap]
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hcm).symm
  haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I) := by
    have : Module.Finite R (S ⧸ I) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mk_surjective)
    exact Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinianRing (S ⧸ I) := by
    letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := fast_instance% Ideal.Quotient.field _
    exact IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ I)
  have hmax : ∀ P : MaximalSpectrum S,
      (P.asIdeal.map (Ideal.Quotient.mk I)).IsMaximal := by
    intro P
    haveI := P.isMaximal
    have hf : IsField (S ⧸ P.asIdeal) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp P.isMaximal
    exact Ideal.Quotient.maximal_of_isField _
      ((DoubleQuot.quotQuotEquivQuotOfLE (hle _ P.isMaximal)).toMulEquiv.isField hf)
  refine Finite.of_injective
    (fun P : MaximalSpectrum S => (⟨P.asIdeal.map (Ideal.Quotient.mk I), hmax P⟩ :
      MaximalSpectrum (S ⧸ I))) ?_
  intro P Q hPQ
  have h := congrArg (fun J : MaximalSpectrum (S ⧸ I) => J.asIdeal.comap (Ideal.Quotient.mk I)) hPQ
  simp only [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
  refine MaximalSpectrum.ext ?_
  rw [← sup_eq_left.mpr (hle _ P.isMaximal), ← sup_eq_left.mpr (hle _ Q.isMaximal)]
  exact h

/-- **Stacks 02M9 over a LOCAL BASE**: if `R` is local, `S` is a finite `R`-algebra and `M` is an
`S`-module which is finite over `R`, flat over `S`, and has the same fibre dimension `n` at every
maximal ideal of `S`, then `M` is free over `S` on `Fin n`.

This is the composite that consumers of `Module.nonempty_basis_of_flat_of_finrank_eq` in this
development were assembling by hand: semilocality of `S` from
`finite_maximalSpectrum_of_isLocalRing_of_module_finite`, finiteness of `M` over `S` from
finiteness over `R` down the tower, and then the mathlib criterion. Stating it once removes the
two `haveI`s from every call site, and — the reason it is worth a declaration rather than a
comment — makes the hypothesis that is genuinely local (`[IsLocalRing R]`) visible in the
signature, so a later reader can see at a glance where the local base is being spent.

`[Module.Finite R M]` rather than `[Module.Finite S M]` is deliberate: the former is what a
consumer over a local base actually has (the whole tower is finite over `R`), and it implies the
latter through `Module.Finite.of_restrictScalars_finite`. -/
theorem Module.nonempty_basis_of_flat_of_finrank_eq_of_isLocalRing_base
    (R : Type*) (S : Type*) (M : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R M] [Module.Flat S M] (n : ℕ)
    (rk : ∀ P : MaximalSpectrum S,
      Module.finrank (S ⧸ P.asIdeal) ((S ⧸ P.asIdeal) ⊗[S] M) = n) :
    Nonempty (Module.Basis (Fin n) S M) := by
  haveI : Finite (MaximalSpectrum S) :=
    finite_maximalSpectrum_of_isLocalRing_of_module_finite R S
  haveI : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  exact Module.nonempty_basis_of_flat_of_finrank_eq S M n rk
