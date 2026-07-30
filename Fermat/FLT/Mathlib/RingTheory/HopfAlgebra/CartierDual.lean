/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Cartier duality for finite flat commutative group schemes

For a finite flat commutative group scheme `G = Spec A` over a base `S = Spec R`, the
**Cartier dual** is the group scheme `G^D = Hom_{S-gp}(G, 𝔾_m)`, and it is again finite
flat of the same rank. On coordinate rings it is the *linear dual Hopf algebra*: the
multiplication and comultiplication of `A` are exchanged.

This file works entirely on the Hopf-algebra side, which is how this development models
finite flat commutative group schemes: a group scheme is a commutative ring `A` with
`[HopfAlgebra R A] [Module.Flat R A] [Module.Finite R A]`, cocommutative
(`[Coalgebra.IsCocomm R A]`) exactly when the group scheme is commutative. See
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean`, whose leaf
`exists_unramified_grouplike_family_generating_corner` is what this file exists to unblock.

## Main definitions

* `CartierDual R A` — the linear dual `Module.Dual R A`, carried on the `WithConv` type
  synonym so that its multiplication is the *convolution* product coming from `comul` on `A`.
* `CartierDual.toDual` — the defining `R`-linear equivalence with `Module.Dual R A`.
* The `CommRing`, `Algebra`, `CoalgebraStruct`, `Bialgebra` and `HopfAlgebra` instances.
* `CartierDual.bidualityLinear` — the biduality isomorphism `A ≃ₗ[R] CartierDual R
  (CartierDual R A)`, together with `bidualityLinear_one`, `bidualityLinear_mul`,
  `bidualityLinear_counit` and `bidualityLinear_comul`.
* `CartierDual.bidualityBialgEquiv` — **biduality as a bundled bialgebra equivalence**
  `A ≃ₐc[R] CartierDual R (CartierDual R A)`; `bidualityAlgEquiv` is its algebra half.
* `CartierDual.finrank_cartierDual` — the dual is finite flat of the same rank.

All three standard examples are proven elsewhere: `μ_n^D ≅ ℤ/n` and `(ℤ/n)^D ≅ μ_n` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDualExamples.lean`, and `α_p^D ≅ α_p` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaPSelfDual.lean` (over
`.../HopfAlgebra/AlphaP.lean`). See the section "What remains" at the end of this file for the
one piece that is still open — exactness on short exact sequences — and what it is blocked on.

## Design notes

**Why `WithConv`.** Mathlib already puts the convolution ring structure on
`WithConv (C →ₗ[R] A)` for `C` a coalgebra and `A` an algebra
(`LinearMap.convCommSemiring` and friends in `Mathlib/RingTheory/Coalgebra/Convolution.lean`).
Taking `C := A` and the target algebra `:= R` gives *exactly* the algebra structure of the
Cartier dual, for free and with the mathlib API attached. So `CartierDual R A` is defined as
`WithConv (Module.Dual R A)` and the ring structure is inherited rather than rebuilt.

**Why finite free.** The comultiplication of the dual is the transpose of the multiplication
of `A`, which lands in `Module.Dual R (A ⊗[R] A)`; to read it as an element of
`Module.Dual R A ⊗[R] Module.Dual R A` one needs `TensorProduct.dualDistribEquiv`, which
requires `A` finite free. That is no loss here: the intended base `𝒪ᵖᵥ` is local, and over a
local ring a finite flat module is free.

**The workhorse.** Every structural identity below is proven by pairing against `A`, via
`CartierDual.dualDistrib_comul_apply`: the comultiplication of `f : CartierDual R A` is
characterised by `⟨Δ f, a ⊗ b⟩ = f (a * b)`. Statements about the dual are then transposes of
statements about `A`.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 2.
* Demazure–Gabriel, *Groupes algébriques*, II §1.
-/

@[expose] public section

open TensorProduct Coalgebra WithConv
open scoped RingTheory.LinearMap

universe u v w

variable (R : Type u) (A : Type v)

/-- The **Cartier dual** of a finite flat commutative group scheme `Spec A`, on coordinate
rings: the linear dual `Module.Dual R A`, whose multiplication is the convolution product
determined by the comultiplication of `A`, and whose comultiplication is the transpose of the
multiplication of `A`.

Carried on `WithConv` so that the convolution product — and not composition — is *the*
multiplication, and so that mathlib's convolution API applies directly. -/
def CartierDual [CommSemiring R] [AddCommMonoid A] [Module R A] : Type max u v :=
  WithConv (Module.Dual R A)

namespace CartierDual

section Module

variable {R A} [CommSemiring R] [AddCommMonoid A] [Module R A]

instance : AddCommMonoid (CartierDual R A) :=
  inferInstanceAs (AddCommMonoid (WithConv (Module.Dual R A)))

instance : Module R (CartierDual R A) :=
  inferInstanceAs (Module R (WithConv (Module.Dual R A)))

variable (R A) in
/-- The defining `R`-linear equivalence between the Cartier dual and the linear dual. -/
def toDual : CartierDual R A ≃ₗ[R] Module.Dual R A :=
  WithConv.linearEquiv R (Module.Dual R A)

instance : FunLike (CartierDual R A) A R where
  coe f := toDual R A f
  coe_injective _ _ h := (toDual R A).injective (DFunLike.coe_injective h)

@[simp] lemma coe_apply (f : CartierDual R A) (a : A) : toDual R A f a = f a := rfl

@[ext] lemma ext {f g : CartierDual R A} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

@[simp] lemma add_apply (f g : CartierDual R A) (a : A) : (f + g) a = f a + g a := rfl

@[simp] lemma zero_apply (a : A) : (0 : CartierDual R A) a = 0 := rfl

@[simp] lemma smul_apply (r : R) (f : CartierDual R A) (a : A) : (r • f) a = r * f a := rfl

lemma sum_apply {ι : Type*} (s : Finset ι) (F : ι → CartierDual R A) (a : A) :
    (∑ i ∈ s, F i) a = ∑ i ∈ s, F i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, add_apply, ih]

end Module

section Ring

variable {R A} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] [IsCocomm R A]

noncomputable instance : CommSemiring (CartierDual R A) :=
  inferInstanceAs (CommSemiring (WithConv (A →ₗ[R] R)))

noncomputable instance : Algebra R (CartierDual R A) :=
  inferInstanceAs (Algebra R (WithConv (A →ₗ[R] R)))

/-- The unit of the Cartier dual is the counit of `A`. -/
lemma one_apply (a : A) : (1 : CartierDual R A) a = counit (R := R) a := by
  show ((1 : WithConv (A →ₗ[R] R))).ofConv a = _
  rw [LinearMap.convOne_def]
  simp

/-- Multiplication in the Cartier dual is the convolution product. -/
lemma mul_apply (f g : CartierDual R A) (a : A) :
    (f * g) a = LinearMap.mul' R R (TensorProduct.map (toDual R A f) (toDual R A g) (comul a)) :=
  rfl

/-- Convolution in Sweedler form: `(f * g) a = ∑ f a₍₁₎ * g a₍₂₎`. -/
lemma mul_apply_repr {ι : Type*} {a : A} (𝓡 : Coalgebra.Repr R a ι) (f g : CartierDual R A) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) :=
  𝓡.convMul_apply _ _

end Ring

section Coalg

variable {R A} [CommRing R] [CommRing A] [HopfAlgebra R A]
variable [Module.Finite R A] [Module.Free R A]

/-- The comultiplication of the Cartier dual, as a map on linear duals: the transpose of the
multiplication of `A`, read through `TensorProduct.dualDistribEquiv`. -/
noncomputable def comulDual :
    Module.Dual R A →ₗ[R] Module.Dual R A ⊗[R] Module.Dual R A :=
  (TensorProduct.dualDistribEquiv R A A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap

/-- The counit of the Cartier dual: evaluation at `1 : A`. -/
noncomputable def counitDual : Module.Dual R A →ₗ[R] R :=
  LinearMap.applyₗ (1 : A)

noncomputable instance instCoalgebraStruct : CoalgebraStruct R (CartierDual R A) where
  comul :=
    (TensorProduct.map (toDual R A).symm.toLinearMap (toDual R A).symm.toLinearMap) ∘ₗ
      comulDual ∘ₗ (toDual R A).toLinearMap
  counit := counitDual ∘ₗ (toDual R A).toLinearMap

@[simp] lemma counit_apply (f : CartierDual R A) : counit (R := R) f = f 1 := rfl

omit [Module.Finite R A] [Module.Free R A] in
/-- `toDual` and its inverse cancel on the tensor square. -/
lemma map_toDual_map_symm (x : Module.Dual R A ⊗[R] Module.Dual R A) :
    TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
      (TensorProduct.map (toDual R A).symm.toLinearMap (toDual R A).symm.toLinearMap x) = x := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  simp

/-- **The workhorse.** The comultiplication of the Cartier dual is characterised by pairing:
`⟨Δ f, a ⊗ b⟩ = f (a * b)`. Every structural identity in this file is proven from this. -/
lemma dualDistrib_comul_apply (f : CartierDual R A) (a b : A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap
          (comul (R := R) f)) (a ⊗ₜ[R] b)
      = f (a * b) := by
  show TensorProduct.dualDistrib R A A
      (TensorProduct.map _ _ (TensorProduct.map _ _ (comulDual (toDual R A f)))) _ = _
  rw [map_toDual_map_symm]
  show (TensorProduct.dualDistribEquiv R A A) ((TensorProduct.dualDistribEquiv R A A).symm
      ((LinearMap.mul' R A).dualMap (toDual R A f))) _ = _
  rw [LinearEquiv.apply_symm_apply]
  simp

/-! ### The pairing API

Everything below is proven by pairing against `A`. `evalAt a` is evaluation at `a : A`, and
`pairMap a b` / `pairMap₃ a b c` are the induced pairings on the tensor square and cube of the
Cartier dual. `pairMap_injective` says these pairings are faithful, which is what turns an
identity in `A` into the corresponding identity in `CartierDual R A`. -/

variable (R A) in
omit [Module.Finite R A] [Module.Free R A] in
/-- Evaluation at `a : A`, as an `R`-linear functional on the Cartier dual. -/
noncomputable def evalAt (a : A) : CartierDual R A →ₗ[R] R :=
  LinearMap.applyₗ a ∘ₗ (toDual R A).toLinearMap

omit [Module.Finite R A] [Module.Free R A] in
@[simp] lemma evalAt_apply (a : A) (f : CartierDual R A) : evalAt R A a f = f a := rfl

/-- The pairing of the tensor square of the Cartier dual against a pair of elements of `A`:
`⟨f ⊗ g, a ⊗ b⟩ = f a * g b`. -/
noncomputable def pairMap (a b : A) :
    CartierDual R A ⊗[R] CartierDual R A →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map (evalAt R A a) (evalAt R A b)

omit [Module.Finite R A] [Module.Free R A] in
@[simp] lemma pairMap_tmul (a b : A) (f g : CartierDual R A) :
    pairMap a b (f ⊗ₜ[R] g) = f a * g b := by
  simp [pairMap]

/-- The pairing of the tensor cube (right-bracketed) of the Cartier dual against three
elements of `A`. -/
noncomputable def pairMap₃ (a b c : A) :
    CartierDual R A ⊗[R] (CartierDual R A ⊗[R] CartierDual R A) →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap ∘ₗ TensorProduct.map (evalAt R A a) (pairMap b c)

omit [Module.Finite R A] [Module.Free R A] in
@[simp] lemma pairMap₃_tmul (a b c : A) (f g h : CartierDual R A) :
    pairMap₃ a b c (f ⊗ₜ[R] (g ⊗ₜ[R] h)) = f a * (g b * h c) := by
  simp [pairMap₃]

omit [Module.Finite R A] [Module.Free R A] in
/-- The triple pairing splits off its first factor, for an arbitrary second argument. -/
@[simp] lemma pairMap₃_tmul_right (a b c : A) (f : CartierDual R A)
    (y : CartierDual R A ⊗[R] CartierDual R A) :
    pairMap₃ a b c (f ⊗ₜ[R] y) = f a * pairMap b c y := by
  simp [pairMap₃]

omit [Module.Finite R A] [Module.Free R A] in
/-- The pairing agrees with `TensorProduct.dualDistrib` transported along `toDual`. -/
lemma pairMap_eq_dualDistrib (x : CartierDual R A ⊗[R] CartierDual R A) (a b : A) :
    pairMap a b x
      = TensorProduct.dualDistrib R A A
          (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap x) (a ⊗ₜ[R] b) := by
  induction x with
  | zero => simp
  | tmul f g => simp
  | add x y hx hy => simp [hx, hy]

/-- **Faithfulness of the pairing.** Two elements of the tensor square of the Cartier dual that
pair equally against all of `A × A` are equal. This is where finite freeness of `A` is spent. -/
lemma pairMap_injective {x y : CartierDual R A ⊗[R] CartierDual R A}
    (h : ∀ a b, pairMap a b x = pairMap a b y) : x = y := by
  have hmap : Function.Injective
      (TensorProduct.map (toDual R A).toLinearMap (toDual R A).toLinearMap) :=
    (TensorProduct.congr (toDual R A) (toDual R A)).injective
  apply hmap
  apply (TensorProduct.dualDistribEquiv R A A).injective
  show TensorProduct.dualDistrib R A A _ = TensorProduct.dualDistrib R A A _
  refine LinearMap.ext fun z => ?_
  induction z with
  | zero => simp
  | tmul a b => simpa [pairMap_eq_dualDistrib] using h a b
  | add z w hz hw => simp [hz, hw]

/-- The characterising property of the Cartier dual's comultiplication, in pairing form:
`⟨Δ f, a ⊗ b⟩ = f (a * b)`. -/
@[simp] lemma pairMap_comul (f : CartierDual R A) (a b : A) :
    pairMap a b (comul (R := R) f) = f (a * b) := by
  rw [pairMap_eq_dualDistrib]
  exact dualDistrib_comul_apply f a b

/-- The triple pairing, as a linear equivalence with the dual of the tensor cube of `A`. -/
noncomputable def tripleEquiv :
    CartierDual R A ⊗[R] (CartierDual R A ⊗[R] CartierDual R A) ≃ₗ[R]
      Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr (toDual R A) ((TensorProduct.congr (toDual R A) (toDual R A)).trans
      (TensorProduct.dualDistribEquiv R A A))).trans
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A))

lemma pairMap₃_eq_tripleEquiv
    (x : CartierDual R A ⊗[R] (CartierDual R A ⊗[R] CartierDual R A)) (a b c : A) :
    pairMap₃ a b c x = tripleEquiv x (a ⊗ₜ[R] (b ⊗ₜ[R] c)) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f y =>
      induction y with
      | zero => simp [tripleEquiv]
      | add y z hy hz =>
          simp only [tmul_add, map_add, LinearMap.add_apply, hy, hz]
      | tmul g h => simp [tripleEquiv, TensorProduct.dualDistribEquiv]

/-- **Faithfulness of the triple pairing.** -/
lemma pairMap₃_injective
    {x y : CartierDual R A ⊗[R] (CartierDual R A ⊗[R] CartierDual R A)}
    (h : ∀ a b c, pairMap₃ a b c x = pairMap₃ a b c y) : x = y := by
  apply (tripleEquiv (R := R) (A := A)).injective
  refine LinearMap.ext fun z => ?_
  induction z with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul a u =>
      induction u with
      | zero => simp
      | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
      | tmul b c => simpa [pairMap₃_eq_tripleEquiv] using h a b c

/-! ### The coalgebra axioms -/

omit [Module.Finite R A] [Module.Free R A] in
/-- Pairing formula for the left-bracketed coassociator. -/
lemma pairMap₃_assoc_tmul (a b c : A) (y : CartierDual R A ⊗[R] CartierDual R A)
    (g : CartierDual R A) :
    pairMap₃ a b c (TensorProduct.assoc R (CartierDual R A) (CartierDual R A) (CartierDual R A)
        (y ⊗ₜ[R] g)) = pairMap a b y * g c := by
  induction y with
  | zero => simp
  | tmul u v => rw [TensorProduct.assoc_tmul, pairMap₃_tmul, pairMap_tmul, mul_assoc]
  | add u v hu hv =>
      rw [add_tmul, map_add, map_add, hu, hv, map_add]; ring

/-- Coassociativity of the Cartier dual's comultiplication is the transpose of associativity
of the multiplication of `A`. -/
theorem coassoc_dual :
    TensorProduct.assoc R (CartierDual R A) (CartierDual R A) (CartierDual R A) ∘ₗ
        (comul (R := R) (A := CartierDual R A)).rTensor (CartierDual R A) ∘ₗ comul
      = (comul (R := R) (A := CartierDual R A)).lTensor (CartierDual R A) ∘ₗ comul := by
  refine LinearMap.ext fun f => ?_
  refine pairMap₃_injective fun a b c => ?_
  have hL : ∀ x : CartierDual R A ⊗[R] CartierDual R A,
      pairMap₃ a b c (TensorProduct.assoc R (CartierDual R A) (CartierDual R A) (CartierDual R A)
        ((comul (R := R) (A := CartierDual R A)).rTensor (CartierDual R A) x))
        = pairMap (a * b) c x := by
    intro x
    induction x with
    | zero => simp
    | tmul u v => rw [LinearMap.rTensor_tmul, pairMap₃_assoc_tmul, pairMap_comul, pairMap_tmul]
    | add u v hu hv => simp only [map_add, hu, hv]
  have hR : ∀ x : CartierDual R A ⊗[R] CartierDual R A,
      pairMap₃ a b c ((comul (R := R) (A := CartierDual R A)).lTensor (CartierDual R A) x)
        = pairMap a (b * c) x := by
    intro x
    induction x with
    | zero => simp
    | tmul u v => rw [LinearMap.lTensor_tmul, pairMap₃_tmul_right, pairMap_comul, pairMap_tmul]
    | add u v hu hv => simp only [map_add, hu, hv]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hL, hR, pairMap_comul, pairMap_comul, mul_assoc]

/-- Pairing formula for the left counit contraction. -/
lemma lid_rTensor_counit_apply (x : CartierDual R A ⊗[R] CartierDual R A) (b : A) :
    (TensorProduct.lid R (CartierDual R A))
      ((counit (R := R) (A := CartierDual R A)).rTensor (CartierDual R A) x) b
      = pairMap 1 b x := by
  induction x with
  | zero => simp
  | tmul u v => simp
  | add u v hu hv => simp only [map_add, add_apply, hu, hv]

/-- Pairing formula for the right counit contraction. -/
lemma rid_lTensor_counit_apply (x : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    (TensorProduct.rid R (CartierDual R A))
      ((counit (R := R) (A := CartierDual R A)).lTensor (CartierDual R A) x) a
      = pairMap a 1 x := by
  induction x with
  | zero => simp
  | tmul u v => simp [mul_comm]
  | add u v hu hv => simp only [map_add, add_apply, hu, hv]

/-- Left counitality for the Cartier dual: the transpose of `1 * a = a` in `A`. -/
theorem rTensor_counit_comp_comul_dual :
    (counit (R := R) (A := CartierDual R A)).rTensor (CartierDual R A) ∘ₗ comul
      = TensorProduct.mk R R (CartierDual R A) 1 := by
  refine LinearMap.ext fun f => ?_
  apply (TensorProduct.lid R (CartierDual R A)).injective
  refine ext fun b => ?_
  rw [LinearMap.comp_apply, lid_rTensor_counit_apply, pairMap_comul, one_mul]
  simp

/-- Right counitality for the Cartier dual: the transpose of `a * 1 = a` in `A`. -/
theorem lTensor_counit_comp_comul_dual :
    (counit (R := R) (A := CartierDual R A)).lTensor (CartierDual R A) ∘ₗ comul
      = (TensorProduct.mk R (CartierDual R A) R).flip 1 := by
  refine LinearMap.ext fun f => ?_
  apply (TensorProduct.rid R (CartierDual R A)).injective
  refine ext fun a => ?_
  rw [LinearMap.comp_apply, rid_lTensor_counit_apply, pairMap_comul, mul_one]
  simp

noncomputable instance instCoalgebra : Coalgebra R (CartierDual R A) where
  coassoc := coassoc_dual
  rTensor_counit_comp_comul := rTensor_counit_comp_comul_dual
  lTensor_counit_comp_comul := lTensor_counit_comp_comul_dual

/-! ### Finiteness, freeness and rank -/

instance : Module.Finite R (CartierDual R A) :=
  Module.Finite.equiv (toDual R A).symm

instance : Module.Free R (CartierDual R A) :=
  Module.Free.of_equiv (toDual R A).symm

/-- **The Cartier dual is finite flat of the same rank.** -/
theorem finrank_cartierDual [Nontrivial R] :
    Module.finrank R (CartierDual R A) = Module.finrank R A := by
  classical
  rw [LinearEquiv.finrank_eq (toDual R A),
    Module.finrank_eq_card_basis (Module.Free.chooseBasis R A).dualBasis,
    Module.finrank_eq_card_basis (Module.Free.chooseBasis R A)]

end Coalg

section Bialg

variable {R A} [CommRing R] [CommRing A] [HopfAlgebra R A] [IsCocomm R A]
variable [Module.Finite R A] [Module.Free R A]

noncomputable instance : CommRing (CartierDual R A) :=
  inferInstanceAs (CommRing (WithConv (A →ₗ[R] R)))

/-! ### The bialgebra axioms -/

/-- The counit of the Cartier dual is unital: `ε_D 1 = 1`, i.e. `ε_A 1 = 1`. -/
theorem counit_one_dual : counit (R := R) (1 : CartierDual R A) = 1 := by
  rw [counit_apply, one_apply, Bialgebra.counit_one]

/-- The counit of the Cartier dual is multiplicative: `(f * g) 1 = f 1 * g 1`, which holds
because `Δ_A 1 = 1 ⊗ 1`. -/
theorem counit_mul_dual (f g : CartierDual R A) :
    counit (R := R) (f * g) = counit (R := R) f * counit (R := R) g := by
  simp only [counit_apply]
  rw [mul_apply]
  rw [show (comul (R := R) (1 : A)) = (1 : A) ⊗ₜ[R] (1 : A) from Bialgebra.comul_one]
  simp

/-- The comultiplication of the Cartier dual is unital: `Δ_D 1 = 1`, which holds because the
counit of `A` is multiplicative. -/
theorem comul_one_dual : comul (R := R) (1 : CartierDual R A) = 1 := by
  refine pairMap_injective fun a b => ?_
  rw [pairMap_comul, one_apply]
  show counit (R := R) (a * b) = pairMap a b ((1 : CartierDual R A) ⊗ₜ[R] (1 : CartierDual R A))
  rw [pairMap_tmul, one_apply, one_apply, Bialgebra.counit_mul]

/-- The product of two Sweedler representations represents the comultiplication of the product.
This is `Bialgebra.comul_mul` in indexed form. -/
def reprMul {ι κ : Type*} {a b : A} (𝓐 : Coalgebra.Repr R a ι) (𝓑 : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a * b) (ι × κ) where
  index := 𝓐.index ×ˢ 𝓑.index
  left p := 𝓐.left p.1 * 𝓑.left p.2
  right p := 𝓐.right p.1 * 𝓑.right p.2
  eq := by
    rw [Finset.sum_product, Bialgebra.comul_mul, ← 𝓐.eq, ← 𝓑.eq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

omit [IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
@[simp] lemma reprMul_index {ι κ : Type*} {a b : A}
    (𝓐 : Coalgebra.Repr R a ι) (𝓑 : Coalgebra.Repr R b κ) :
    (reprMul 𝓐 𝓑).index = 𝓐.index ×ˢ 𝓑.index := rfl

omit [IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
@[simp] lemma reprMul_left {ι κ : Type*} {a b : A}
    (𝓐 : Coalgebra.Repr R a ι) (𝓑 : Coalgebra.Repr R b κ) (p : ι × κ) :
    (reprMul 𝓐 𝓑).left p = 𝓐.left p.1 * 𝓑.left p.2 := rfl

omit [IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
@[simp] lemma reprMul_right {ι κ : Type*} {a b : A}
    (𝓐 : Coalgebra.Repr R a ι) (𝓑 : Coalgebra.Repr R b κ) (p : ι × κ) :
    (reprMul 𝓐 𝓑).right p = 𝓐.right p.1 * 𝓑.right p.2 := rfl

omit [Module.Finite R A] [Module.Free R A] in
/-- The pairing of a PRODUCT in the tensor square of the Cartier dual. This is the statement
that pairing against `a ⊗ b` is a map of convolution algebras, and it is what makes the
bialgebra compatibility self-dual. -/
lemma pairMap_mul {ι κ : Type*} {a b : A} (𝓐 : Coalgebra.Repr R a ι) (𝓑 : Coalgebra.Repr R b κ)
    (x y : CartierDual R A ⊗[R] CartierDual R A) :
    pairMap a b (x * y)
      = ∑ i ∈ 𝓐.index, ∑ j ∈ 𝓑.index,
          pairMap (𝓐.left i) (𝓑.left j) x * pairMap (𝓐.right i) (𝓑.right j) y := by
  induction x with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
      simp only [add_mul, map_add, h₁, h₂, ← Finset.sum_add_distrib]
  | tmul u v =>
      induction y with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
          simp only [mul_add, map_add, h₁, h₂, ← Finset.sum_add_distrib]
      | tmul u' v' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, pairMap_tmul, mul_apply_repr 𝓐,
            mul_apply_repr 𝓑, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [pairMap_tmul, pairMap_tmul]; ring

/-- The comultiplication of the Cartier dual is multiplicative. This is the self-dual bialgebra
compatibility: it is the transpose of `Δ_A (a * b) = Δ_A a * Δ_A b` together with the
convolution formula for the product on the dual. -/
theorem comul_mul_dual (f g : CartierDual R A) :
    comul (R := R) (f * g) = comul (R := R) f * comul (R := R) g := by
  refine pairMap_injective fun a b => ?_
  rw [pairMap_comul, mul_apply_repr (reprMul (ℛ R a) (ℛ R b)) f g,
    pairMap_mul (ℛ R a) (ℛ R b)]
  simp only [pairMap_comul, reprMul_index, reprMul_left, reprMul_right]
  rw [Finset.sum_product]

noncomputable instance instBialgebra : Bialgebra R (CartierDual R A) where
  counit_one := counit_one_dual
  mul_compr₂_counit := by ext f g; exact counit_mul_dual f g
  comul_one := comul_one_dual
  mul_compr₂_comul := by ext f g; exact comul_mul_dual f g

/-! ### The antipode -/

/-- The antipode of the Cartier dual is the transpose of the antipode of `A`. -/
noncomputable instance instHopfAlgebraStruct : HopfAlgebraStruct R (CartierDual R A) where
  antipode := (toDual R A).symm.toLinearMap ∘ₗ (HopfAlgebra.antipode R (A := A)).dualMap ∘ₗ
    (toDual R A).toLinearMap

@[simp] lemma antipode_apply (f : CartierDual R A) (a : A) :
    HopfAlgebra.antipode R f a = f (HopfAlgebra.antipode R a) := rfl

omit [Module.Finite R A] [Module.Free R A] in
/-- Evaluating a product in the Cartier dual against `a : A` contracts the tensor square with
a Sweedler representation of `comul a`. -/
lemma mul'_apply_repr {ι : Type*} {a : A} (𝓡 : Coalgebra.Repr R a ι)
    (x : CartierDual R A ⊗[R] CartierDual R A) :
    (LinearMap.mul' R (CartierDual R A) x) a
      = ∑ i ∈ 𝓡.index, pairMap (𝓡.left i) (𝓡.right i) x := by
  induction x with
  | zero => simp
  | tmul u v => rw [LinearMap.mul'_apply, mul_apply_repr 𝓡]; simp
  | add x y hx hy =>
      rw [map_add, add_apply, hx, hy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (map_add _ _ _).symm

/-- Transposing the antipode through the pairing, on the left factor. -/
lemma pairMap_rTensor_antipode (a b : A) (x : CartierDual R A ⊗[R] CartierDual R A) :
    pairMap a b ((HopfAlgebra.antipode R (A := CartierDual R A)).rTensor (CartierDual R A) x)
      = pairMap (HopfAlgebra.antipode R a) b x := by
  induction x with
  | zero => simp
  | tmul u v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Transposing the antipode through the pairing, on the right factor. -/
lemma pairMap_lTensor_antipode (a b : A) (x : CartierDual R A ⊗[R] CartierDual R A) :
    pairMap a b ((HopfAlgebra.antipode R (A := CartierDual R A)).lTensor (CartierDual R A) x)
      = pairMap a (HopfAlgebra.antipode R b) x := by
  induction x with
  | zero => simp
  | tmul u v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- First antipode axiom for the Cartier dual, the transpose of the first antipode axiom
for `A`. -/
theorem mul_antipode_rTensor_comul_dual :
    LinearMap.mul' R (CartierDual R A) ∘ₗ
        (HopfAlgebra.antipode R (A := CartierDual R A)).rTensor (CartierDual R A) ∘ₗ comul
      = Algebra.linearMap R (CartierDual R A) ∘ₗ counit := by
  refine LinearMap.ext fun f => ?_
  refine ext fun a => ?_
  have hR : ((Algebra.linearMap R (CartierDual R A) ∘ₗ
      counit (R := R) (A := CartierDual R A)) f) a = f 1 * counit (R := R) a := by
    show (algebraMap R (WithConv (A →ₗ[R] R)) (counit (R := R) (A := CartierDual R A) f)) a = _
    rw [LinearMap.convAlgebraMap_apply]
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mul'_apply_repr (ℛ R a), hR]
  simp only [pairMap_rTensor_antipode, pairMap_comul, ← coe_apply, ← map_sum]
  rw [HopfAlgebra.sum_antipode_mul_eq_smul (ℛ R a), map_smul]
  simp [mul_comm]

/-- Second antipode axiom for the Cartier dual. -/
theorem mul_antipode_lTensor_comul_dual :
    LinearMap.mul' R (CartierDual R A) ∘ₗ
        (HopfAlgebra.antipode R (A := CartierDual R A)).lTensor (CartierDual R A) ∘ₗ comul
      = Algebra.linearMap R (CartierDual R A) ∘ₗ counit := by
  refine LinearMap.ext fun f => ?_
  refine ext fun a => ?_
  have hR : ((Algebra.linearMap R (CartierDual R A) ∘ₗ
      counit (R := R) (A := CartierDual R A)) f) a = f 1 * counit (R := R) a := by
    show (algebraMap R (WithConv (A →ₗ[R] R)) (counit (R := R) (A := CartierDual R A) f)) a = _
    rw [LinearMap.convAlgebraMap_apply]
    simp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, mul'_apply_repr (ℛ R a), hR]
  simp only [pairMap_lTensor_antipode, pairMap_comul, ← coe_apply, ← map_sum]
  rw [HopfAlgebra.sum_mul_antipode_eq_smul (ℛ R a), map_smul]
  simp [mul_comm]

/-- **The Cartier dual of a finite flat commutative group scheme is again one.** -/
noncomputable instance instHopfAlgebra : HopfAlgebra R (CartierDual R A) where
  mul_antipode_rTensor_comul := mul_antipode_rTensor_comul_dual
  mul_antipode_lTensor_comul := mul_antipode_lTensor_comul_dual

omit [IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
/-- Swapping the pairing arguments corresponds to swapping the tensor factors. -/
lemma pairMap_comm (a b : A) (x : CartierDual R A ⊗[R] CartierDual R A) :
    pairMap a b (TensorProduct.comm R (CartierDual R A) (CartierDual R A) x) = pairMap b a x := by
  induction x with
  | zero => simp
  | tmul u v => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsCocomm R A] in
/-- The Cartier dual is cocommutative, because `A` is commutative — this is the statement that
the dual group scheme is again COMMUTATIVE. -/
theorem isCocomm_dual : IsCocomm R (CartierDual R A) where
  comm_comp_comul := by
    refine LinearMap.ext fun f => ?_
    refine pairMap_injective fun a b => ?_
    show pairMap a b (TensorProduct.comm R (CartierDual R A) (CartierDual R A)
      (comul (R := R) f)) = pairMap a b (comul (R := R) f)
    rw [pairMap_comm, pairMap_comul, pairMap_comul, mul_comm]

noncomputable instance : IsCocomm R (CartierDual R A) := isCocomm_dual

/-! ### Biduality

`G^{DD} ≅ G`. The underlying linear equivalence is mathlib's `Module.evalEquiv` (available
because a finite free module is reflexive) transported along `toDual`; the content is that it
respects the Hopf structure, which is proven below for the ALGEBRA structure and the counit. -/

variable (R A) in
/-- The biduality map `A → CartierDual R (CartierDual R A)`, as an `R`-linear equivalence:
`a ↦ (f ↦ f a)`. Note that the target is well-formed only because every instance needed to
form the double dual — `CommRing`, `HopfAlgebra`, `IsCocomm`, `Module.Finite`, `Module.Free`
on `CartierDual R A` — has been established above. -/
noncomputable def bidualityLinear : A ≃ₗ[R] CartierDual R (CartierDual R A) :=
  (Module.evalEquiv R A).trans (((toDual R A).dualMap).trans (toDual R (CartierDual R A)).symm)

omit [IsCocomm R A] in
@[simp] lemma bidualityLinear_apply (a : A) (f : CartierDual R A) :
    bidualityLinear R A a f = f a := rfl

/-- Biduality carries `1` to `1`: the unit of the double dual is the counit of the dual, which
is evaluation at `1`. -/
theorem bidualityLinear_one : bidualityLinear R A 1 = 1 := by
  refine ext fun f => ?_
  rw [bidualityLinear_apply, one_apply, counit_apply]

omit [IsCocomm R A] in
/-- Biduality is multiplicative. This is exactly the characterising property of the dual's
comultiplication, `⟨Δ f, a ⊗ b⟩ = f (a * b)`, read backwards. -/
theorem bidualityLinear_mul (a b : A) :
    bidualityLinear R A (a * b) = bidualityLinear R A a * bidualityLinear R A b := by
  refine ext fun f => ?_
  rw [mul_apply_repr (ℛ R f), bidualityLinear_apply, ← pairMap_comul f a b, ← (ℛ R f).eq,
    map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [pairMap_tmul]; rfl

/-- Biduality respects the counit. -/
theorem bidualityLinear_counit (a : A) :
    counit (R := R) (bidualityLinear R A a) = counit (R := R) a := by
  rw [counit_apply, bidualityLinear_apply, one_apply]

/-- **Biduality respects the comultiplication.** This is the transpose of `bidualityLinear_mul`:
pairing `Δ (bidual a)` against `f ⊗ g` gives `(f * g) a`, which is `∑ f a₍₁₎ * g a₍₂₎` by the
convolution formula — and that is exactly the pairing of `(bidual ⊗ bidual) (Δ a)`. -/
theorem bidualityLinear_comul (a : A) :
    comul (R := R) (bidualityLinear R A a)
      = TensorProduct.map (bidualityLinear R A).toLinearMap (bidualityLinear R A).toLinearMap
          (comul (R := R) a) := by
  refine pairMap_injective fun f g => ?_
  rw [pairMap_comul, bidualityLinear_apply, mul_apply_repr (ℛ R a) f g, ← (ℛ R a).eq, map_sum,
    map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [TensorProduct.map_tmul, pairMap_tmul]; rfl

variable (R A) in
/-- Biduality as an ALGEBRA equivalence `A ≃ₐ[R] A^{DD}`. -/
noncomputable def bidualityAlgEquiv : A ≃ₐ[R] CartierDual R (CartierDual R A) :=
  { bidualityLinear R A with
    map_mul' := bidualityLinear_mul
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      show bidualityLinear R A (r • (1 : A)) = _
      rw [map_smul, bidualityLinear_one] }

variable (R A) in
/-- **BIDUALITY.** `G ≅ G^{DD}` for a finite flat commutative group scheme, as a bundled
equivalence of `R`-bialgebras: the underlying map is `Module.evalEquiv`, and it respects the
unit, the multiplication, the counit and the comultiplication. Since a bialgebra map between
Hopf algebras automatically commutes with the antipodes, this is the full statement that Cartier
duality is an involution. -/
noncomputable def bidualityBialgEquiv : A ≃ₐc[R] CartierDual R (CartierDual R A) where
  __ := bidualityAlgEquiv R A
  map_smul' := map_smul (bidualityLinear R A)
  counit_comp := LinearMap.ext bidualityLinear_counit
  map_comp_comul := LinearMap.ext fun a => (bidualityLinear_comul a).symm

@[simp] lemma bidualityBialgEquiv_apply (a : A) (f : CartierDual R A) :
    bidualityBialgEquiv R A a f = f a := rfl

/-! ### What remains, and why it is a separate task

The construction above is complete and unconditional. Two of the five pieces the Cartier-duality
dispatch asked for are **not** here, and both are blocked on things that are genuinely absent
rather than merely unwritten. Recording them precisely so the next owner does not re-derive the
survey:

**1. Exactness of duality on short exact sequences — NOW STATED ELSEWHERE, still open.** This is
the piece `(R3)` under `exists_unramified_grouplike_family_generating_corner` actually consumes.

STALE NOTE CORRECTED (2026-07-27): this item read "it is not stated here because *this tree has
no definition of a short exact sequence of finite flat group schemes*, and writing one is a
design decision rather than a proof … it should be written by whoever also writes `(R3)`, so
that the definition is pinned by its consumer rather than guessed at in advance." That is
exactly what happened, and it is done.
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` carries the predicted formulation
verbatim — `A'' ↪ A ↠ A'` with `A` faithfully flat over `A''` and
`ker(A → A') = A · ker(ε_{A''})`, as `HopfAlgebra.IsShortExact` — together with the
functoriality `CartierDual.map` this file does not have, and `(R3)` itself as
`HopfAlgebra.isMultiplicativeType_of_isShortExact`, whose three-symbol proof is the evidence
that the definition really is pinned by its consumer. No fppf descent was needed.

CORRECTED 2026-07-27: this paragraph read "what is still OPEN there is the mathematics, in two
named leaves: `HopfAlgebra.IsShortExact.cartierDual` … and `HopfAlgebra.etale_of_isShortExact`
… those are the dispatchable targets". **BOTH ARE NOW PROVEN** — `IsShortExact.cartierDual` at
`ShortExact.lean:669` (a four-field assembly) and `etale_of_isShortExact` at `:916` — so neither
is a dispatchable target and neither is owned. The decomposition that was "in flight on an
unreleased branch" landed; what is open in `ShortExact.lean` are the four leaves those two
consume: `IsShortExact.exists_linearRetraction` (`:564`), `.ker_cartierDual_le` (`:628`),
`.faithfullyFlat_cartierDual` (`:648`, the deepest — classically `Ext¹(G'', 𝔾ₘ) = 0`) and
`Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_finitePresentation` (`:238`), all four
separately queued as of 2026-07-27. This file remains complete and unconditional.

Do not trust that count of four either: `grep -n 'sorry' ShortExact.lean` is the check that
settles the current list, and it costs nothing.

**2. The examples — SUPERSEDED, mostly DONE (2026-07-27).** The blocker recorded here was the
missing Hopf structure on the coordinate ring of a finite constant group scheme. It now exists as
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/GroupFunctions.lean` (`GroupFunctions R G`), and both
diagonalizable/constant examples are proven in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDualExamples.lean`:

* `CartierDual.dualGroupAlgebraBialgEquiv : CartierDual R (MonoidAlgebra R G) ≃ₐc[R]
  GroupFunctions R G` — `μ_n^D ≅ ℤ/n`, at `G := Multiplicative (ZMod n)`;
* `CartierDual.groupAlgebraBialgEquivDual : MonoidAlgebra R G ≃ₐc[R]
  CartierDual R (GroupFunctions R G)` — `(ℤ/n)^D ≅ μ_n`, same instantiation.

**`α_p^D ≅ α_p` is also DONE** (2026-07-27), and the "theory gap" recorded here is closed.
`O(𝔾_a) = R[X]` with additive comultiplication was indeed absent from the pin, from `~/cs/FLT`
and from this tree — but it turned out not to be needed: building `α_p` DIRECTLY as
`AdjoinRoot (X^p)` skips `𝔾_a` and the Hopf-ideal quotient entirely. See
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaP.lean` for the Hopf algebra and
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaPSelfDual.lean` for
`AlphaP.selfDualBialgEquiv : AlphaP R p ≃ₐc[R] CartierDual R (AlphaP R p)`, whose content is
the divided-power pairing `y^m = m! · e_m` with `y := e_1` and `m!` a unit for `m < p`.

So all three commissioned examples are proven, and only piece 1 above (exactness) remains. -/

end Bialg

end CartierDual
