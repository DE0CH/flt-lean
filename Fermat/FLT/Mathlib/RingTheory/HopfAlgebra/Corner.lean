/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Quotient
-- `Module.free_of_finite_type_torsion_free'`: a module-finite torsion-free module over a
-- principal ideal domain is free.  This is the engine of `free_quotient_cornerIdeal`.
public import Mathlib.LinearAlgebra.FreeModule.PID
-- `Module.Flat.rTensor_preserves_injective_linearMap`: the flatness input to
-- `isCocomm_of_baseChange`, which descends cocommutativity from `S ⊗[R] A` to `A` along an
-- injective `R → S`.
public import Mathlib.RingTheory.Flat.Basic
-- `Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap`: the comultiplication of a
-- base-changed bialgebra, the compatibility that makes that descent possible.
public import Mathlib.RingTheory.Bialgebra.TensorProduct

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
* `HopfAlgebra.free_quotient_cornerIdeal` — over a principal ideal domain the corner of a
  module-finite torsion-free algebra is **free**.
* `Coalgebra.isCocomm_quotient` — a coideal quotient of a cocommutative coalgebra is
  cocommutative.
* `Coalgebra.isCocomm_of_baseChange` — cocommutativity **descends** from `S ⊗[R] A` to `A`
  along an injective `R → S`, when `A ⊗[R] A` is `R`-flat.
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

section Freeness

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {e : A}

/-- **Membership in the corner ideal is annihilation by the idempotent**: for an idempotent
`e : A`, `x ∈ (1 - e)` if and only if `e * x = 0`.

Both directions are one line of `ring`: `e * (c * (1 - e)) = c * (e - e²) = 0`, and conversely
`x * (1 - e) = x - e * x = x`. -/
lemma mem_cornerIdeal_iff_mul_eq_zero (he : IsIdempotentElem e) {x : A} :
    x ∈ cornerIdeal e ↔ e * x = 0 := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := mem_cornerIdeal_iff.mp hx
    have h : e * (c * (1 - e)) = c * (e - e * e) := by ring
    rw [h, he, sub_self, mul_zero]
  · refine mem_cornerIdeal_iff.mpr ⟨x, ?_⟩
    have h : x * (1 - e) = x - e * x := by ring
    rw [h, hx, sub_zero]

/-- **The corner quotient of a torsion-free algebra is torsion-free.**

`A ⧸ (1 - e)` is isomorphic as an `R`-module to the direct summand `e A ⊆ A`, and a submodule of
a torsion-free module is torsion-free.  The proof below runs that argument without naming the
isomorphism: an `r`-torsion relation `r • a ≡ r • b` in the quotient says
`e * (r • (a - b)) = 0`, i.e. `r • (e * (a - b)) = 0`, and regularity of `r` on `A` kills the
factor `r`, leaving `e * (a - b) = 0`, which is `a ≡ b`. -/
theorem isTorsionFree_quotient_cornerIdeal [Module.IsTorsionFree R A]
    (he : IsIdempotentElem e) : Module.IsTorsionFree R (A ⧸ cornerIdeal e) where
  isSMulRegular r hr := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : r • (Ideal.Quotient.mk (cornerIdeal e) a) =
        Ideal.Quotient.mk (cornerIdeal e) (r • a) :=
      (map_smul (Ideal.Quotient.mkₐ R (cornerIdeal e)) r a).symm
    have hy : r • (Ideal.Quotient.mk (cornerIdeal e) b) =
        Ideal.Quotient.mk (cornerIdeal e) (r • b) :=
      (map_smul (Ideal.Quotient.mkₐ R (cornerIdeal e)) r b).symm
    replace hxy : r • (Ideal.Quotient.mk (cornerIdeal e) a) =
        r • (Ideal.Quotient.mk (cornerIdeal e) b) := hxy
    rw [hx, hy, Ideal.Quotient.eq, mem_cornerIdeal_iff_mul_eq_zero he, ← smul_sub,
      mul_smul_comm] at hxy
    have h3 : e * (a - b) = (0 : A) := hr.isSMulRegular (M := A) (by simpa using hxy)
    exact Ideal.Quotient.eq.mpr ((mem_cornerIdeal_iff_mul_eq_zero he).mpr h3)

/-- **The corner of a module-finite torsion-free algebra over a PID is FREE.**

`A ⧸ (1 - e)` is module-finite (quotient of a module-finite algebra) and torsion-free
(`isTorsionFree_quotient_cornerIdeal`), so `Module.free_of_finite_type_torsion_free'` applies.

At the intended call site `R` is the discrete valuation ring `𝒪ᵥ` and `A` a finite flat Hopf
order; `Module.Flat.isTorsionFree` supplies the torsion-freeness. -/
theorem free_quotient_cornerIdeal [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R A] [Module.IsTorsionFree R A] (he : IsIdempotentElem e) :
    Module.Free R (A ⧸ cornerIdeal e) := by
  haveI : Module.Finite R (A ⧸ cornerIdeal e) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (cornerIdeal e)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI := isTorsionFree_quotient_cornerIdeal (R := R) he
  infer_instance

end Freeness

end HopfAlgebra

namespace Coalgebra

section QuotientCocomm

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]

/-- Swapping the two factors of a tensor square commutes with the functorial image of a single
linear map in both slots. -/
lemma comm_map_apply {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (t : M ⊗[R] M) :
    _root_.TensorProduct.comm R N N (_root_.TensorProduct.map f f t) =
      _root_.TensorProduct.map f f (_root_.TensorProduct.comm R M M t) := by
  induction t with
  | zero => simp
  | tmul x y => simp
  | add u v hu hv => simp [hu, hv]

/-- **A coideal quotient of a cocommutative coalgebra is cocommutative.**

`comul` on `A ⧸ I` is `(mk ⊗ mk) ∘ comul` (`Bialgebra.Quotient.comul_mk`, definitional), and
`mk ⊗ mk` commutes with the swap, so cocommutativity passes through the surjection. -/
theorem isCocomm_quotient (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
    [IsCocomm R A] : IsCocomm R (A ⧸ I) := by
  constructor
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show _root_.TensorProduct.comm R (A ⧸ I) (A ⧸ I)
      (comul (R := R) (Ideal.Quotient.mk I a)) = comul (R := R) (Ideal.Quotient.mk I a)
  rw [Bialgebra.Quotient.comul_mk, comm_map_apply, comm_comul]

end QuotientCocomm

section CocommDescent

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [Bialgebra R H]

/-- **The comultiplication of a base-changed bialgebra on a pure tensor `1 ⊗ h`.**

This is `Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap` evaluated at `1 ⊗ₜ h`: the
comultiplication of `S ⊗[R] H` is the comultiplication of `H`, base-changed and reshuffled by
`tensorTensorTensorComm`. -/
theorem comul_one_tmul (h : H) :
    comul (R := S) ((1 : S) ⊗ₜ[R] h) =
      (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H).toAlgHom
        ((1 : S ⊗[S] S) ⊗ₜ[R] (comul (R := R) h)) := by
  rw [congr($(Bialgebra.TensorProduct.comul_eq_algHom_toLinearMap R S S H) ((1 : S) ⊗ₜ[R] h))]
  simp [Algebra.TensorProduct.one_def]

variable (R S H) in
/-- The `R`-linear comparison map `H ⊗[R] H → (S ⊗[R] H) ⊗[S] (S ⊗[R] H)`, `a ⊗ b ↦
(1 ⊗ a) ⊗ (1 ⊗ b)`, written as `tensorTensorTensorComm` applied to `1 ⊗ t` so that
`comul_one_tmul` matches it on the nose. -/
noncomputable def baseChangeTensorSquare : H ⊗[R] H → (S ⊗[R] H) ⊗[S] (S ⊗[R] H) := fun t =>
  (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H).toAlgHom
    ((1 : S ⊗[S] S) ⊗ₜ[R] t)

lemma baseChangeTensorSquare_tmul (a b : H) :
    baseChangeTensorSquare R S H (a ⊗ₜ[R] b) =
      ((1 : S) ⊗ₜ[R] a) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b) := by
  show (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H)
      (((1 : S) ⊗ₜ[S] (1 : S)) ⊗ₜ[R] (a ⊗ₜ[R] b)) = _
  rw [Algebra.TensorProduct.tensorTensorTensorComm_tmul]

lemma baseChangeTensorSquare_zero :
    baseChangeTensorSquare R S H 0 = 0 := by
  show (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H)
      ((1 : S ⊗[S] S) ⊗ₜ[R] (0 : H ⊗[R] H)) = 0
  rw [_root_.TensorProduct.tmul_zero, map_zero]

lemma baseChangeTensorSquare_add (t t' : H ⊗[R] H) :
    baseChangeTensorSquare R S H (t + t') =
      baseChangeTensorSquare R S H t + baseChangeTensorSquare R S H t' := by
  show (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H)
      ((1 : S ⊗[S] S) ⊗ₜ[R] (t + t')) = _
  rw [_root_.TensorProduct.tmul_add, map_add]
  rfl

lemma baseChangeTensorSquare_comul (h : H) :
    baseChangeTensorSquare R S H (comul (R := R) h) = comul (R := S) ((1 : S) ⊗ₜ[R] h) :=
  (comul_one_tmul h).symm

/-- The comparison map intertwines the two swaps. -/
lemma baseChangeTensorSquare_comm (t : H ⊗[R] H) :
    baseChangeTensorSquare R S H (_root_.TensorProduct.comm R H H t) =
      _root_.TensorProduct.comm S (S ⊗[R] H) (S ⊗[R] H)
        (baseChangeTensorSquare R S H t) := by
  induction t with
  | zero => rw [map_zero, baseChangeTensorSquare_zero, map_zero]
  | tmul x y =>
      rw [_root_.TensorProduct.comm_tmul, baseChangeTensorSquare_tmul,
        baseChangeTensorSquare_tmul, _root_.TensorProduct.comm_tmul]
  | add u v hu hv =>
      rw [map_add, baseChangeTensorSquare_add, baseChangeTensorSquare_add, hu, hv, map_add]

/-- The comparison map is injective when `H ⊗[R] H` is `R`-flat and `R → S` is injective:
it is `t ↦ 1 ⊗ₜ t` followed by an isomorphism, and `M → S ⊗[R] M` is injective for flat `M`
(`Module.Flat.tensorProduct_mk_injective`). -/
lemma baseChangeTensorSquare_injective [Module.Flat R (H ⊗[R] H)]
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (baseChangeTensorSquare R S H) := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have hmk := Module.Flat.tensorProduct_mk_injective (R := R) (S := S) (M := H ⊗[R] H)
  intro t t' htt
  have h0 : ((1 : S ⊗[S] S) ⊗ₜ[R] t : (S ⊗[S] S) ⊗[R] (H ⊗[R] H)) =
      (1 : S ⊗[S] S) ⊗ₜ[R] t' :=
    (Algebra.TensorProduct.tensorTensorTensorComm R S R S S S H H).injective htt
  have hF : ∀ z : H ⊗[R] H,
      (_root_.TensorProduct.map
          ((_root_.TensorProduct.lid S S).toLinearMap.restrictScalars R)
          (LinearMap.id (R := R) (M := H ⊗[R] H)))
        ((1 : S ⊗[S] S) ⊗ₜ[R] z) = (1 : S) ⊗ₜ[R] z := by
    intro z
    show (_root_.TensorProduct.map _ _) (((1 : S) ⊗ₜ[S] (1 : S)) ⊗ₜ[R] z) = _
    rw [_root_.TensorProduct.map_tmul]
    congr 1
    show (_root_.TensorProduct.lid S S) ((1 : S) ⊗ₜ[S] (1 : S)) = (1 : S)
    simp
  have h1 : ((1 : S) ⊗ₜ[R] t : S ⊗[R] (H ⊗[R] H)) = (1 : S) ⊗ₜ[R] t' := by
    rw [← hF t, ← hF t', h0]
  exact hmk h1

/-- **Cocommutativity descends along a faithfully-acting base change.**

If `S ⊗[R] H` is cocommutative over `S`, `H ⊗[R] H` is `R`-flat and `R → S` is injective, then
`H` is cocommutative over `R`.  The comparison map `H ⊗[R] H → (S ⊗[R] H) ⊗[S] (S ⊗[R] H)` is
injective and intertwines both the comultiplications and the swaps, so the identity
`τ ∘ Δ = Δ` may be checked after base change.

This is the formal content of "the generic fibre is a commutative group scheme, and flatness
descends the identity to the integral model". -/
theorem isCocomm_of_baseChange [Module.Flat R (H ⊗[R] H)] [IsCocomm S (S ⊗[R] H)]
    (hinj : Function.Injective (algebraMap R S)) : IsCocomm R H := by
  constructor
  refine LinearMap.ext fun h => ?_
  show _root_.TensorProduct.comm R H H (comul (R := R) h) = comul (R := R) h
  refine baseChangeTensorSquare_injective (S := S) hinj ?_
  rw [baseChangeTensorSquare_comm, baseChangeTensorSquare_comul, comm_comul]

end CocommDescent

end Coalgebra
