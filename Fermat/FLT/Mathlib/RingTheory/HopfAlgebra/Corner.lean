/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Quotient

/-!
# The corner Hopf algebra at a connected counit idempotent

Let `A` be a commutative `R`-Hopf algebra — the coordinate ring of a commutative group scheme
`Spec A` — and let `e : A` be an idempotent which is *a connected counit idempotent*:

* `counit e = 1` (`e` does not vanish at the identity section), and
* `e` is **minimal**: every idempotent `x` satisfies `x * e = 0` or `x * e = e`, so the clopen
  piece `Spec (e A)` cut out by `e` has no proper clopen subpiece — it is *connected*, and
  contains the identity;
* `comul e * (e ⊗ₜ e) = e ⊗ₜ e`, which says the multiplication of the group scheme carries
  `Spec (eA) × Spec (eA)` into `Spec (eA)`.

Under these hypotheses the ideal `(1 - e)` is a **Hopf ideal**, so the corner
`A ⧸ (1 - e) ≅ e A` inherits a Hopf algebra structure: it is the coordinate ring of the
**connected component of the identity** `G°` of `G = Spec A`, as a closed subgroup scheme.

## Why this file exists

`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean` carries the Raynaud citation
`exists_unramified_grouplike_family_generating_corner`, whose remaining requirement `(R1)` is the
*dévissage* of the connected component `G°` into `μ`-type graded pieces. Its extension step
`(R3)` is already proven (`HopfAlgebra.isMultiplicativeType_of_isShortExact` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean`), stated over
`HopfAlgebra.IsShortExact` and `HopfAlgebra.IsMultiplicativeType` — both of which are statements
about a **Hopf algebra**. But `Family.lean` never had `G°` as an object: it carried only the
idempotent `e₀` and the corner *submodule* `(ℚᵖᵥᵃˡᵍ ⊗ G) · ē₀`, which is not a Hopf algebra and
about which neither `IsShortExact` nor `IsMultiplicativeType` can even be stated.

Three successive audits in that file recorded the leaf as "IRREDUCIBLY A CITATION" and dismissed
building this object as "real work but pure plumbing: it moves no part of `(R1)`–`(R4)`". That is
the inference the fleet doctrine names explicitly as the commonest bad one — *stating* a theory is
not *proving* it, and a structure that can be written before anything satisfies it is often
exactly what makes a safe cut possible. This file writes the object; with it, `(R1)` becomes the
statable, dispatchable `IsMultiplicativeType R (A ⧸ cornerIdeal e)` instead of an unstatable
citation.

## Main results

* `HopfAlgebra.antipode_mul_self_eq_of_connected` — `S(e) * e = e`.
* `HopfAlgebra.isHopfIdeal_cornerIdeal` — `(1 - e)` is a Hopf ideal, hence `A ⧸ (1 - e)` is a
  Hopf algebra by mathlib's `HopfAlgebra.Quotient` instance.
-/

@[expose] public section

open Coalgebra TensorProduct

namespace HopfAlgebra

section Def

variable {A : Type*} [CommRing A]

/-- **The corner ideal at an idempotent** `e`: the ideal `(1 - e)`, whose quotient is the corner
`e A`. Geometrically `Spec (A ⧸ cornerIdeal e)` is the clopen piece of `Spec A` cut out by `e`. -/
def cornerIdeal (e : A) : Ideal A := Ideal.span {1 - e}

lemma mem_cornerIdeal_iff {e x : A} : x ∈ cornerIdeal e ↔ ∃ c : A, c * (1 - e) = x :=
  Ideal.mem_span_singleton'

lemma one_sub_mem_cornerIdeal (e : A) : 1 - e ∈ cornerIdeal e :=
  Ideal.subset_span rfl

/-- In the corner quotient the idempotent becomes the unit: `e ↦ 1`. -/
lemma mk_eq_one_cornerIdeal (e : A) :
    (Ideal.Quotient.mk (cornerIdeal e) e : A ⧸ cornerIdeal e) = 1 := by
  have h : (Ideal.Quotient.mk (cornerIdeal e)) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (one_sub_mem_cornerIdeal e)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

end Def

section CornerIdeal

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] {e : A}

/-- **The antipode fixes a connected counit idempotent up to the corner**: `S(e) * e = e`.

`S` is an algebra homomorphism on a commutative Hopf algebra, so `S(e)` is again an idempotent,
and `counit (S e) = counit e = 1`. Minimality of `e` therefore leaves only `S(e) * e = 0` or
`S(e) * e = e`, and the first is excluded by applying the counit, which would give `1 = 0`. -/
theorem antipode_mul_self_eq_of_connected [Nontrivial R]
    (he : IsIdempotentElem e) (hε : counit (R := R) e = (1 : R))
    (hprim : ∀ x : A, IsIdempotentElem x → x * e = 0 ∨ x * e = e) :
    antipode R e * e = e := by
  have hSidem : IsIdempotentElem (antipode R e) := by
    have h := map_mul (antipodeAlgHom R A) e e
    rw [he] at h
    show antipode R e * antipode R e = antipode R e
    exact h.symm
  have hSε : counit (R := R) (antipode R e) = (1 : R) := by rw [counit_antipode, hε]
  rcases hprim _ hSidem with h | h
  · exfalso
    have h0 : counit (R := R) (antipode R e * e) = (0 : R) := by rw [h, map_zero]
    rw [Bialgebra.counit_mul, hSε, hε, one_mul] at h0
    exact one_ne_zero h0
  · exact h

/-- **The corner at a connected counit idempotent is a Hopf ideal**, so the corner
`A ⧸ (1 - e)` is again a Hopf algebra — the coordinate ring of the connected component of the
identity `G° ⊆ G = Spec A`.

The three conditions of `Ideal.IsHopfIdeal` come out as follows.

* *Counit*: `counit (1 - e) = 1 - 1 = 0`, and the counit is multiplicative, so it kills the whole
  principal ideal.
* *Coideal*: pushing `comul e * (e ⊗ₜ e) = e ⊗ₜ e` through the algebra map
  `A ⊗ A → (A ⧸ I) ⊗ (A ⧸ I)` and using `e ↦ 1` gives `comul e ↦ 1`, hence `comul (1 - e) ↦ 0`.
  This is the *only* place `hcomul` is used, and it is exactly the statement that the group law
  restricts to the corner.
* *Antipode*: `S(1 - e) = 1 - S(e)`, and `(1 - S e) * (1 - e) = 1 - S e` because
  `S(e) * e = e` (`antipode_mul_self_eq_of_connected`), so `1 - S e` lies in `(1 - e)`. -/
theorem isHopfIdeal_cornerIdeal [Nontrivial R]
    (he : IsIdempotentElem e) (hε : counit (R := R) e = (1 : R))
    (hprim : ∀ x : A, IsIdempotentElem x → x * e = 0 ∨ x * e = e)
    (hcomul : comul (R := R) e * (e ⊗ₜ[R] e) = e ⊗ₜ[R] e) :
    (cornerIdeal e).IsHopfIdeal R := by
  set I : Ideal A := cornerIdeal e with hI
  -- the counit kills `I`
  have hcounit : ∀ ⦃x : A⦄, x ∈ I → counit (R := R) x = 0 := by
    rintro x hx
    obtain ⟨c, rfl⟩ := mem_cornerIdeal_iff.mp hx
    rw [Bialgebra.counit_mul, map_sub, Bialgebra.counit_one, hε, sub_self, mul_zero]
  -- the quotient map, tensored with itself, as an algebra map
  set Φ : A ⊗[R] A →ₐ[R] (A ⧸ I) ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I) with hΦ
  have hΦe : Φ (e ⊗ₜ[R] e) = 1 := by
    rw [hΦ]
    show (Ideal.Quotient.mk I e) ⊗ₜ[R] (Ideal.Quotient.mk I e) = 1
    rw [hI, mk_eq_one_cornerIdeal e]
    rfl
  have hΦcomul : Φ (comul (R := R) e) = 1 := by
    have h := congrArg Φ hcomul
    rw [map_mul, hΦe, mul_one] at h
    exact h
  -- `Φ` is the linear `TensorProduct.map` of the two module quotient maps
  have hΦlin : Φ.toLinearMap =
      TensorProduct.map (I.restrictScalars R).mkQ (I.restrictScalars R).mkQ := by
    ext a b
    rfl
  have hcoideal : ∀ ⦃x : A⦄, x ∈ I →
      TensorProduct.map (I.restrictScalars R).mkQ (I.restrictScalars R).mkQ
        (comul (R := R) x) = 0 := by
    rintro x hx
    obtain ⟨c, rfl⟩ := mem_cornerIdeal_iff.mp hx
    have hlin : TensorProduct.map (I.restrictScalars R).mkQ (I.restrictScalars R).mkQ
        (comul (R := R) (c * (1 - e))) = Φ (comul (R := R) (c * (1 - e))) := by
      rw [← hΦlin]; rfl
    rw [hlin, Bialgebra.comul_mul, map_sub, Bialgebra.comul_one, map_mul, map_sub, map_one,
      hΦcomul, sub_self, mul_zero]
    rfl
  -- the antipode preserves `I`
  have hantipode : ∀ ⦃x : A⦄, x ∈ I → antipode R x ∈ I := by
    rintro x hx
    obtain ⟨c, rfl⟩ := mem_cornerIdeal_iff.mp hx
    have hSe : antipode R e * e = e := antipode_mul_self_eq_of_connected he hε hprim
    have hkey : (1 - antipode R e) * (1 - e) = 1 - antipode R e := by
      have h1 : (1 - antipode R e) * (1 - e) = 1 - e - antipode R e + antipode R e * e := by
        ring
      rw [h1, hSe]; ring
    have hmem : 1 - antipode R e ∈ I := by
      rw [hI, cornerIdeal, ← hkey]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    have hS : antipode R (c * (1 - e)) = antipode R c * (1 - antipode R e) := by
      have h := map_mul (antipodeAlgHom R A) c (1 - e)
      have h2 := map_sub (antipodeAlgHom R A) 1 e
      rw [map_one] at h2
      show antipode R (c * (1 - e)) = antipode R c * (1 - antipode R e)
      rw [show antipode R (c * (1 - e)) = (antipodeAlgHom R A) (c * (1 - e)) from rfl, h,
        show ((antipodeAlgHom R A) (1 - e)) = 1 - antipode R e from h2]
      rfl
    rw [hS]
    exact Ideal.mul_mem_left _ _ hmem
  haveI : (I.restrictScalars R).IsCoideal := ⟨hcounit, hcoideal⟩
  exact { antipode_mem := hantipode }

end CornerIdeal

end HopfAlgebra
