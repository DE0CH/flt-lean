/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDual
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDualExamples
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.Corner
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.GroupFunctions
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.ShortExact
public import Fermat.FLT.Mathlib.RingTheory.Henselian.FiniteSplit
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TotallySplit

/-!
# Diagonalizability: multiplicative type over a strictly henselian local base

SGA 3, Exp. VIII/X: **a group scheme of multiplicative type over a strictly henselian local
base is diagonalizable**, i.e. its coordinate ring is spanned by genuine group-like elements.
This file states that (`HopfAlgebra.exists_spanning_groupLike_of_isMultiplicativeType`) and
PROVES it over two named leaves, having first supplied the piece of Cartier-duality
infrastructure the argument needs.

## Main definitions

* `CartierDual.baseChangeAlgEquiv` — **base change of the Cartier dual**,
  `S ⊗[R] A^D ≃ₐ[S] (S ⊗[R] A)^D` for `A` finite free over `R`. PROVEN.
* `CartierDual.congr` — Cartier duality carries a bialgebra ISOMORPHISM to one. PROVEN.
* `Coalgebra.Repr.baseChange` — a Sweedler representation base-changes. PROVEN.

## Main statements

* `HopfAlgebra.isMultiplicativeType_baseChange` — multiplicative type is stable under base
  change. PROVEN, from `baseChangeAlgEquiv` and `Algebra.Etale.baseChange`.
* `Algebra.IsFiniteSplit.of_henselianLocalRing` — **(E1)**, a finite étale algebra over a
  strictly henselian local ring is split. **PROVEN**, over the general commutative algebra in
  `Fermat/FLT/Mathlib/RingTheory/Henselian/FiniteSplit.lean`. It was a genuine gap in the mathlib
  pin, which has the statement only over a FIELD
  (`Algebra.FormallyEtale.equivPiOfIsSepClosed`) — confirmed by grep, see that file.
* `HopfAlgebra.exists_bialgEquiv_groupFunctions_of_isFiniteSplit` — **(E2)**, a split
  cocommutative group scheme over a LOCAL base is the constant one. **PROVEN**, over the
  `Points` section: the points `Γ = WithConv (X →ₐ[S] S)` are the `n` projections of the
  splitting (`splitPointsEquiv`, over `Pi.exists_eq_evalAlgHom_of_isLocalRing`), and evaluation
  at them (`pointsAlgHom`) is a bialgebra isomorphism onto `GroupFunctions S Γ`.
* `HopfAlgebra.exists_spanning_groupLike_of_isMultiplicativeType` — the theorem above. PROVEN
  over `(E1)`; `(E2)` is now discharged, so `(E1)` is the only remaining leaf of this file.

## Design notes

**Cartier BIDUALITY is NOT a gap and is not restated here.** A survey attached to the consuming
leaf in `Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean` recorded biduality as one of
three missing pieces, on the strength of a `grep` for the lowercase string `cartierDual`. It has
in fact been proven unconditionally since the Cartier-duality file was written:
`CartierDual.bidualityBialgEquiv : A ≃ₐc[R] CartierDual R (CartierDual R A)`, in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean`. The assembly below consumes it
directly. (The stale note has been corrected in place.)

**Only the ALGEBRA half of base change is built.** `baseChangeAlgEquiv` transports the ring and
`S`-algebra structure but not the comultiplication, because the sole consumer needs only
étaleness of the dual. The coalgebra half is true and provable by the same pairing argument; it
is deliberately not written, since an unused API is an API nobody maintains.

## References

* SGA 3, Exp. VIII–X (groups of multiplicative type).
* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Stacks Project, [04GG](https://stacks.math.columbia.edu/tag/04GG) (finite étale over a
  strictly henselian local ring).
-/

@[expose] public section

open TensorProduct Coalgebra

universe u

/-! ## Base change of a Sweedler representation -/

namespace Coalgebra

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [Bialgebra R H]

lemma baseChangeTensorSquare_sum {ι : Type*} (s : Finset ι) (F : ι → H ⊗[R] H) :
    baseChangeTensorSquare R S H (∑ i ∈ s, F i)
      = ∑ i ∈ s, baseChangeTensorSquare R S H (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using baseChangeTensorSquare_zero (R := R) (S := S) (H := H)
  | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, baseChangeTensorSquare_add, ih]

variable (S) in
/-- **A Sweedler representation base-changes.** If `∑ᵢ aᵢ ⊗ bᵢ` represents `Δ a` in `H`, then
`∑ᵢ (1 ⊗ aᵢ) ⊗ (1 ⊗ bᵢ)` represents `Δ (1 ⊗ a)` in `S ⊗[R] H`. -/
noncomputable def Repr.baseChange {ι : Type*} {a : H} (𝓡 : Coalgebra.Repr R a ι) :
    Coalgebra.Repr S ((1 : S) ⊗ₜ[R] a) ι where
  index := 𝓡.index
  left i := (1 : S) ⊗ₜ[R] 𝓡.left i
  right i := (1 : S) ⊗ₜ[R] 𝓡.right i
  eq := by
    rw [← baseChangeTensorSquare_comul (R := R) (S := S), ← 𝓡.eq, baseChangeTensorSquare_sum]
    exact Finset.sum_congr rfl fun i _ => baseChangeTensorSquare_tmul _ _

@[simp] lemma Repr.baseChange_index {ι : Type*} {a : H} (𝓡 : Coalgebra.Repr R a ι) :
    (𝓡.baseChange S).index = 𝓡.index := rfl

@[simp] lemma Repr.baseChange_left {ι : Type*} {a : H} (𝓡 : Coalgebra.Repr R a ι) (i : ι) :
    (𝓡.baseChange S).left i = (1 : S) ⊗ₜ[R] 𝓡.left i := rfl

@[simp] lemma Repr.baseChange_right {ι : Type*} {a : H} (𝓡 : Coalgebra.Repr R a ι) (i : ι) :
    (𝓡.baseChange S).right i = (1 : S) ⊗ₜ[R] 𝓡.right i := rfl

end Coalgebra

/-! ## Base change of the Cartier dual -/

namespace CartierDual

section BaseChange

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Free R A]

variable (R S A) in
/-- The base-change comparison for the Cartier dual, as an `S`-linear equivalence. -/
noncomputable def baseChangeLinearEquiv :
    S ⊗[R] CartierDual R A ≃ₗ[S] CartierDual S (S ⊗[R] A) :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) (toDual R A)).trans
      (IsBaseChange.toDualBaseChange (TensorProduct.isBaseChange R A S))).trans
    (toDual S (S ⊗[R] A)).symm

omit [IsCocomm R A] in
@[simp] lemma baseChangeLinearEquiv_tmul_one_tmul (s : S) (f : CartierDual R A) (a : A) :
    baseChangeLinearEquiv R S A (s ⊗ₜ[R] f) ((1 : S) ⊗ₜ[R] a)
      = s * algebraMap R S (f a) := by
  show (toDual S (S ⊗[R] A)) ((toDual S (S ⊗[R] A)).symm _) _ = _
  rw [LinearEquiv.apply_symm_apply]
  exact IsBaseChange.toDualBaseChange_tmul _ s (toDual R A f) a

omit [IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
/-- Two functionals on `S ⊗[R] A` agreeing on the pure tensors `1 ⊗ a` are equal: those
generate `S ⊗[R] A` over `S`. -/
lemma ext_one_tmul {F G : CartierDual S (S ⊗[R] A)}
    (h : ∀ a : A, F ((1 : S) ⊗ₜ[R] a) = G ((1 : S) ⊗ₜ[R] a)) : F = G :=
  (toDual S (S ⊗[R] A)).injective
    ((TensorProduct.isBaseChange R A S).algHom_ext _ _ h)

lemma baseChangeLinearEquiv_one :
    baseChangeLinearEquiv R S A 1 = 1 := by
  refine ext_one_tmul fun a => ?_
  show baseChangeLinearEquiv R S A ((1 : S) ⊗ₜ[R] (1 : CartierDual R A)) _ = _
  rw [baseChangeLinearEquiv_tmul_one_tmul, one_mul, one_apply, one_apply,
    TensorProduct.counit_tmul]
  simp [Algebra.algebraMap_eq_smul_one]

lemma baseChangeLinearEquiv_mul (x y : S ⊗[R] CartierDual R A) :
    baseChangeLinearEquiv R S A (x * y)
      = baseChangeLinearEquiv R S A x * baseChangeLinearEquiv R S A y := by
  induction x with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | tmul s f =>
      induction y with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
      | tmul t g =>
          refine ext_one_tmul fun a => ?_
          rw [Algebra.TensorProduct.tmul_mul_tmul, baseChangeLinearEquiv_tmul_one_tmul,
            mul_apply_repr ((Coalgebra.Repr.arbitrary R a).baseChange S),
            mul_apply_repr (Coalgebra.Repr.arbitrary R a)]
          simp only [Coalgebra.Repr.baseChange_index, Coalgebra.Repr.baseChange_left,
            Coalgebra.Repr.baseChange_right, baseChangeLinearEquiv_tmul_one_tmul, map_sum,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring

variable (R S A) in
/-- **BASE CHANGE OF THE CARTIER DUAL.** For a finite free cocommutative Hopf algebra `A` over
`R` and any `R`-algebra `S`, Cartier duality commutes with base change:
`S ⊗[R] A^D ≃ₐ[S] (S ⊗[R] A)^D`.

The underlying linear equivalence is mathlib's `IsBaseChange.toDualBaseChange` — finite freeness
of `A` is exactly what makes it an equivalence rather than a mere map. The content added here is
that it is MULTIPLICATIVE, i.e. that the two *convolution* products agree; that is the transpose
of the fact that the comultiplication of `S ⊗[R] A` is the base change of the comultiplication of
`A` (`Coalgebra.Repr.baseChange`).

Only the ALGEBRA structure is transported, because that is what the consumer
(`HopfAlgebra.isMultiplicativeType_baseChange`, hence étaleness of the dual) needs. The
comultiplication is compatible too — the same pairing argument transposes it — but nothing in
this development uses it, so it is deliberately not built. -/
noncomputable def baseChangeAlgEquiv :
    S ⊗[R] CartierDual R A ≃ₐ[S] CartierDual S (S ⊗[R] A) :=
  AlgEquiv.ofLinearEquiv (baseChangeLinearEquiv R S A)
    baseChangeLinearEquiv_one baseChangeLinearEquiv_mul

@[simp] lemma baseChangeAlgEquiv_tmul_one_tmul (s : S) (f : CartierDual R A) (a : A) :
    baseChangeAlgEquiv R S A (s ⊗ₜ[R] f) ((1 : S) ⊗ₜ[R] a) = s * algebraMap R S (f a) :=
  baseChangeLinearEquiv_tmul_one_tmul s f a

end BaseChange

/-! ## Cartier duality carries an isomorphism to an isomorphism -/

section Congr

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [IsCocomm R A] [IsCocomm R B]
  [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B]

/-- **Cartier duality is a functor into the opposite category, so it carries isomorphisms to
isomorphisms.** `CartierDual.map` already transposes a bialgebra map; this packages the
transposes of `e` and `e.symm` as mutually inverse. -/
noncomputable def congr (e : A ≃ₐc[R] B) : CartierDual R B ≃ₐc[R] CartierDual R A :=
  BialgEquiv.ofBijective (map (e : A →ₐc[R] B))
    (Function.bijective_iff_has_inverse.mpr
      ⟨map (e.symm : B →ₐc[R] A),
        fun φ => by ext b; simp only [map_apply, BialgEquiv.coe_toBialgHom,
          BialgEquiv.apply_symm_apply],
        fun ψ => by ext a; simp only [map_apply, BialgEquiv.coe_toBialgHom,
          BialgEquiv.symm_apply_apply]⟩)

@[simp] lemma congr_apply (e : A ≃ₐc[R] B) (φ : CartierDual R B) (a : A) :
    congr e φ a = φ (e a) := rfl

end Congr

end CartierDual

/-! ## Multiplicative type is stable under base change -/

namespace HopfAlgebra

section BaseChange

variable (R S A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A]

/-- **Multiplicative type is stable under base change.** Immediate from
`CartierDual.baseChangeAlgEquiv` and `Algebra.Etale.baseChange`: being of multiplicative type is
*defined* as étaleness of the Cartier dual, and both duality and étaleness commute with base
change.

This is what turns the abstract statement below — about a Hopf algebra over the strictly
henselian ring itself — into a statement about `𝒪ᵘⁿʳ ⊗ A` for an `A` living over the smaller
base, which is the form the arithmetic consumer needs. -/
theorem isMultiplicativeType_baseChange (h : IsMultiplicativeType R A) :
    IsMultiplicativeType S (S ⊗[R] A) := by
  haveI : Algebra.Etale R (CartierDual R A) := h
  haveI : Algebra.Etale S (S ⊗[R] CartierDual R A) :=
    Algebra.Etale.baseChange R (CartierDual R A) S
  exact Algebra.Etale.of_equiv (CartierDual.baseChangeAlgEquiv R S A)

end BaseChange

/-! ## The points of a split algebra over a LOCAL base

Everything in this section is machinery for `(E2)` below and is used nowhere else. It is kept in
one contiguous block, separate from `(E1)`, so that the two leaves of this file can be worked
concurrently.
-/

section Points

/-- **In a local ring the only idempotents are `0` and `1`.** `c` and `1 - c` cannot both be
non-units, and either being a unit kills the other factor of `c * (c - 1) = 0`. This is where
locality does its work in `(E2)`, and it is exactly what the `k × k` counterexample in `(E2)`'s
docstring violates. (`[IsLocalRing S]` is consumed in one other, much weaker way: the
`Nontrivial S` it carries is what makes the point indexing of `splitPointsEquiv` injective.) -/
theorem _root_.IsIdempotentElem.eq_zero_or_one_of_isLocalRing {S : Type*} [CommRing S]
    [IsLocalRing S] {c : S} (hc : c * c = c) : c = 0 ∨ c = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
  · right
    have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
    exact sub_eq_zero.mp ((IsUnit.mul_right_eq_zero h).mp h0)
  · left
    have h0 : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    exact (IsUnit.mul_right_eq_zero h).mp h0

/-- **Over a LOCAL base, the only `S`-algebra maps `(ι → S) → S` are the projections.**

The values `c i := φ (e_i)` on the standard orthogonal idempotents are idempotents of `S`
summing to `1` and multiplying to `0` in pairs. Over a local ring each is `0` or `1`; the sum
forces one of them to be `1`, and orthogonality kills the rest. Then
`φ f = ∑ⱼ f j * c j = f i`.

This is the whole content of "a split algebra is determined by its points", and it FAILS over a
disconnected base. Witness: `S = k × k`, `ι = {1, 2}`, and `φ (a, b) := (a₁, b₂)` — the first
component of `a` paired with the second component of `b`. That is a ring map, and it is
`S`-linear because `S` acts componentwise (`φ (s • (a, b)) = (s₁ a₁, s₂ b₂) = s • φ (a, b)`),
and it commutes with `algebraMap S (ι → S) s = (s, s)` since `φ (s, s) = (s₁, s₂) = s`. It is
NEITHER projection. Its values on the idempotents are `c₁ = (1, 0)` and `c₂ = (0, 1)`, precisely
the nontrivial idempotents that `IsIdempotentElem.eq_zero_or_one_of_isLocalRing` rules out. -/
theorem _root_.Pi.exists_eq_evalAlgHom_of_isLocalRing {S : Type*} [CommRing S] [IsLocalRing S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : (ι → S) →ₐ[S] S) :
    ∃ i : ι, φ = Pi.evalAlgHom S (fun _ => S) i := by
  classical
  have hone : (∑ i : ι, Pi.single i (1 : S)) = 1 := by
    funext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  have hidem : ∀ i : ι, φ (Pi.single i 1) * φ (Pi.single i 1) = φ (Pi.single i 1) := by
    intro i
    rw [← map_mul]
    congr 1
    funext j
    by_cases h : j = i <;> simp [h]
  have hsum : (∑ i : ι, φ (Pi.single i 1)) = 1 := by
    rw [← map_sum, hone, map_one]
  have horth : ∀ i j : ι, i ≠ j → φ (Pi.single i 1) * φ (Pi.single j 1) = 0 := by
    intro i j hij
    rw [← map_mul]
    have hz : (Pi.single i (1 : S) : ι → S) * (Pi.single j (1 : S) : ι → S) = 0 := by
      funext k
      by_cases hk : k = i <;> by_cases hk' : k = j <;> simp_all
    rw [hz, map_zero]
  have hex : ∃ i : ι, φ (Pi.single i 1) = 1 := by
    by_contra hcon
    have hzero : ∀ i : ι, φ (Pi.single i (1 : S)) = 0 := by
      intro i
      rcases IsIdempotentElem.eq_zero_or_one_of_isLocalRing (hidem i) with h | h
      · exact h
      · exact absurd ⟨i, h⟩ hcon
    rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi⟩ := hex
  have hother : ∀ j : ι, j ≠ i → φ (Pi.single j 1) = 0 := by
    intro j hj
    have h := horth i j (Ne.symm hj)
    rwa [hi, one_mul] at h
  refine ⟨i, ?_⟩
  refine AlgHom.ext fun f => ?_
  have hf : f = ∑ j : ι, Pi.single j (f j) := (Finset.univ_sum_single f).symm
  have hstep : ∀ j : ι, Pi.single j (f j) = f j • Pi.single j (1 : S) := by
    intro j
    funext k
    by_cases hk : k = j <;> simp [hk]
  calc φ f = ∑ j : ι, φ (Pi.single j (f j)) := by rw [← map_sum, ← hf]
    _ = ∑ j : ι, f j * φ (Pi.single j 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hstep j, map_smul, smul_eq_mul]
    _ = f i := by
        rw [Finset.sum_eq_single i]
        · rw [hi, mul_one]
        · intro j _ hj; rw [hother j hj, mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h

/-- Pulling `Coalgebra.comul` on `GroupFunctions R G` through `tensorEquiv` is the pullback
along the group law — which is how `comulAlgHom` was defined in the first place.

NOTE (2026-07-28): `CartierDual.tensorEquiv_comul` in `CartierDualExamples.lean` is the same
fact, stated as an equality of functions rather than pointwise, but under `[CommGroup G]` and
in the `CartierDual` namespace. This version needs only `[Group G]`, which is what the
`GroupFunctions` bialgebra structure itself needs — using the `CartierDual` one here would
force `[Coalgebra.IsCocomm S X]` into `map_comp_comulAlgHom_pointsAlgHom`, where it is not
mathematically required. The two should be consolidated into `GroupFunctions.lean` (this
statement, generalised to a function equality) whenever that file is next opened. -/
theorem _root_.GroupFunctions.tensorEquiv_comul {R : Type*} [CommRing R] {G : Type*} [Group G]
    [Fintype G] [DecidableEq G] (f : GroupFunctions R G) (p : G × G) :
    GroupFunctions.tensorEquiv R G (Coalgebra.comul (R := R) f) p = f (p.1 * p.2) := by
  rw [GroupFunctions.comul_eq]
  show GroupFunctions.tensorEquiv R G
    ((GroupFunctions.tensorEquiv R G).symm (GroupFunctions.mulPullback R G f)) p = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

variable (S X : Type u) [CommRing S] [CommRing X]

/-- **Over a LOCAL base, the `S`-points of a split algebra are indexed by any splitting.**
`i ↦ ev_i ∘ e`, bijective by `Pi.exists_eq_evalAlgHom_of_isLocalRing`. No Hopf structure is
involved: this is a statement about the underlying algebra. -/
noncomputable def splitPointsEquiv [IsLocalRing S] [Algebra S X] {n : ℕ}
    (e : X ≃ₐ[S] (Fin n → S)) : Fin n ≃ (X →ₐ[S] S) := by
  classical
  refine Equiv.ofBijective
    (fun i => (Pi.evalAlgHom S (fun _ => S) i).comp (e : X →ₐ[S] (Fin n → S))) ⟨?_, ?_⟩
  · intro i j hij
    by_contra hne
    have h := congrArg (fun ψ => ψ (e.symm (Pi.single i (1 : S)))) hij
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
      Pi.evalAlgHom_apply] at h
    rw [Pi.single_apply, Pi.single_apply, if_pos rfl, if_neg (Ne.symm hne)] at h
    exact one_ne_zero h
  · intro φ
    obtain ⟨i, hi⟩ :=
      Pi.exists_eq_evalAlgHom_of_isLocalRing (φ.comp (e.symm : (Fin n → S) →ₐ[S] X))
    refine ⟨i, ?_⟩
    refine AlgHom.ext fun x => ?_
    have h := congrArg (fun ψ => ψ (e x)) hi
    simpa using h.symm

@[simp] lemma splitPointsEquiv_apply [IsLocalRing S] [Algebra S X] {n : ℕ}
    (e : X ≃ₐ[S] (Fin n → S)) (i : Fin n) (x : X) :
    splitPointsEquiv S X e i x = e x i := rfl

variable [HopfAlgebra S X]

/-- **Evaluation at the `S`-points**: `x ↦ (φ ↦ φ x)`, an `S`-algebra map from `X` into the
functions on the point group `Γ = WithConv (X →ₐ[S] S)`.

`Γ` is a group under CONVOLUTION by mathlib's `AlgHom.convGroup` (unit `ε`, inverse
`φ ∘ antipode`), and the anonymous `CommGroup` instance beside it in
`Mathlib/RingTheory/HopfAlgebra/Convolution.lean` upgrades that under
`Coalgebra.IsCocomm S X`. Neither fact needs the base to be local, and neither is built here;
locality enters only through bijectivity below. -/
def pointsAlgHom : X →ₐ[S] GroupFunctions S (WithConv (X →ₐ[S] S)) where
  toFun x := (fun φ : WithConv (X →ₐ[S] S) => φ.ofConv x : GroupFunctions S _)
  map_one' := by ext φ; exact map_one φ.ofConv
  map_mul' x y := by ext φ; exact map_mul φ.ofConv x y
  map_zero' := by ext φ; exact map_zero φ.ofConv
  map_add' x y := by ext φ; exact map_add φ.ofConv x y
  commutes' r := by ext φ; simp

@[simp] lemma pointsAlgHom_apply (x : X) (φ : WithConv (X →ₐ[S] S)) :
    pointsAlgHom S X x φ = φ.ofConv x := rfl

section Bialg

variable [Fintype (WithConv (X →ₐ[S] S))] [DecidableEq (WithConv (X →ₐ[S] S))]

/-- The counit of `GroupFunctions` is evaluation at `1`, and `1 : Γ` IS the counit of `X`. -/
lemma counitAlgHom_comp_pointsAlgHom :
    (Bialgebra.counitAlgHom S (GroupFunctions S (WithConv (X →ₐ[S] S)))).comp
        (pointsAlgHom S X) = Bialgebra.counitAlgHom S X := by
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
  rw [GroupFunctions.counit_eq, pointsAlgHom_apply]
  show ((1 : WithConv (X →ₐ[S] S)) : X → S) x = _
  rw [AlgHom.convOne_apply]
  simp

/-- **The comultiplication matches because the group law on `Γ` IS convolution.** Read through
`tensorEquiv`, the left side at `(φ, ψ)` is `∑ φ(x₁) ψ(x₂)` over any Sweedler representation of
`Δx`, and the right side is `(φ ⋆ ψ)(x)` — the same sum, by `AlgHom.convMul_apply`. -/
lemma map_comp_comulAlgHom_pointsAlgHom :
    (Algebra.TensorProduct.map (pointsAlgHom S X) (pointsAlgHom S X)).comp
        (Bialgebra.comulAlgHom S X)
      = (Bialgebra.comulAlgHom S (GroupFunctions S (WithConv (X →ₐ[S] S)))).comp
          (pointsAlgHom S X) := by
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  refine (GroupFunctions.tensorEquiv S (WithConv (X →ₐ[S] S))).injective ?_
  funext p
  obtain ⟨φ, ψ⟩ := p
  rw [GroupFunctions.tensorEquiv_comul]
  set 𝓡 := Coalgebra.Repr.arbitrary S x with h𝓡
  rw [pointsAlgHom_apply]
  show _ = ((φ * ψ : WithConv (X →ₐ[S] S)) : X → S) x
  rw [AlgHom.convMul_apply, ← 𝓡.eq]
  simp only [map_sum, Finset.sum_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul, GroupFunctions.tensorEquiv_tmul, pointsAlgHom_apply]

end Bialg

variable [IsLocalRing S]

/-- **`pointsAlgHom` is bijective.** Under a splitting `e : X ≃ₐ[S] (Fin n → S)` the point group
is `Fin n` (`splitPointsEquiv`) and `pointsAlgHom` becomes `f ↦ f ∘ E.symm` — a relabelling of
coordinates, hence bijective. -/
lemma pointsAlgHom_bijective_of_equiv {n : ℕ} (e : X ≃ₐ[S] (Fin n → S)) :
    Function.Bijective (pointsAlgHom S X) := by
  classical
  set E : Fin n ≃ WithConv (X →ₐ[S] S) :=
    (splitPointsEquiv S X e).trans (WithConv.equiv (X →ₐ[S] S)).symm with hE
  have hEapp : ∀ (i : Fin n) (x : X), (E i).ofConv x = e x i := fun _ _ => rfl
  constructor
  · intro x y hxy
    have h : ∀ φ : WithConv (X →ₐ[S] S), φ.ofConv x = φ.ofConv y := fun φ => congrFun hxy φ
    refine e.injective ?_
    funext i
    rw [← hEapp i x, ← hEapp i y, h]
  · intro g
    refine ⟨e.symm (fun i => g (E i)), ?_⟩
    funext φ
    obtain ⟨j, rfl⟩ := E.surjective φ
    rw [pointsAlgHom_apply, hEapp j, AlgEquiv.apply_symm_apply]

end Points

/-! ## The two remaining leaves, and the assembly over them -/

/-- **(E1) A FINITE ÉTALE ALGEBRA OVER A STRICTLY HENSELIAN LOCAL RING IS SPLIT** (**PROVEN** —
pure commutative algebra, no Hopf structure, no group schemes; it was a genuine gap in the
mathlib pin, and the supporting development now lives in
`Fermat/FLT/Mathlib/RingTheory/Henselian/FiniteSplit.lean`).

**THE ARGUMENT BELOW IS NOT THE ONE USED, AND CANNOT BE — read the design note in
`FiniteSplit.lean`.** Its idempotent-lifting step is unavailable over this pin: `Henselian`
occurs in exactly ONE mathlib file, which offers only polynomial root-lifting, and mathlib's
idempotent lifting (`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`) is along NIL ideals
only — the maximal ideal of a henselian local ring is not nil. The route actually taken lifts a
GENERATOR by Nakayama instead of idempotents, splits the minimal polynomial by Hensel in its
mathlib-definitional (polynomial) form, and concludes with an invertible VANDERMONDE matrix.
The sketch is kept because it is the standard textbook argument and records the mathematics.

Stacks [04GG](https://stacks.math.columbia.edu/tag/04GG)/[04GH]: if `S` is henselian local with
SEPARABLY CLOSED residue field and `E` is a finite étale `S`-algebra, then `E ≅ Πⁿ S`.

WHAT IS PRESENT AND WHAT IS MISSING. Both halves of the argument exist in the pin and only
their assembly is absent:

* `Algebra.IsFiniteSplit` itself, in `Mathlib/RingTheory/TotallySplit.lean`, together with the
  instance `[IsSepClosed k] [EssFiniteType k E] [FormallyEtale k E] : IsFiniteSplit k E` — but
  over a FIELD `k` only. That instance is the special case `S = k` of this statement, and it is
  the input to the residue-field step below.
* `HenselianLocalRing`, in `Mathlib/RingTheory/Henselian.lean`, with the idempotent-lifting
  characterisation (`HenselianLocalRing.TFAE`).

THE ARGUMENT. Write `k` for the residue field and `E₀ := k ⊗[S] E`. Then `E₀` is finite étale
over `k`, so the field instance above splits it, `E₀ ≅ Πⁿ k`. Its `n` orthogonal idempotents lift
to `E` because `(S, m)` is henselian and `E` is a finite `S`-algebra (a finite algebra over a
henselian local ring is a product of local rings, which is one of the standard equivalent forms of
henselianness). That decomposes `E ≅ Π Eᵢ` with each `Eᵢ` local, finite and étale over `S`. Étale
means unramified, so `m Eᵢ` is the maximal ideal of `Eᵢ` and `Eᵢ/m Eᵢ` is a finite SEPARABLE
extension of `k` — hence `= k`, as `k` is separably closed. So `S → Eᵢ` is a finite flat local map
inducing an isomorphism on residue fields, therefore an isomorphism (Nakayama on the rank-one
free module `Eᵢ`).

FAITHFULNESS (settled: the statement is now PROVEN, so it is true; what follows is only about
whether each hypothesis is NECESSARY). `Module.Finite S E` is not implied by `Algebra.Etale S E`
(which gives only finite PRESENTATION as an algebra) and cannot be dropped: a localization `S_f`
is étale over `S` (mathlib's `Algebra.Etale (Localization.Away s)` instance) without being finite.

CORRECTION (2026-07-29): the witness previously recorded here for that — `E = ℚ_p` over
`S = ℤ_p` — is INADMISSIBLE, because `ℤ_p` has residue field `𝔽_p`, which is not separably
closed, so it fails the OTHER hypothesis and tests nothing about this statement. A valid witness
must keep the base strictly henselian: take `S` the strict henselization of `ℤ_p` (residue field
`𝔽̄_p`, separably closed) and `E = Frac S`. Then `E` is étale over `S` and not `Πⁿ S`, since `E`
is a field while `Πⁿ S` is local only for `n = 1`, and `E ≠ S`.
Separable closedness of the RESIDUE FIELD is what forces
each factor to be `S` rather than a nontrivial unramified extension; over `ℤ_p` with its residue
field `𝔽_p` the statement is false for `E = 𝒪_{ℚ_p(ζ_ℓ)}`, `ℓ ≠ p`. Both hypotheses are therefore
load-bearing, and the leaf is not vacuous: `E = S` and `E = S × S` both satisfy it nontrivially. -/
theorem _root_.Algebra.IsFiniteSplit.of_henselianLocalRing
    (S E : Type u) [CommRing S] [CommRing E] [Algebra S E]
    [HenselianLocalRing S] [IsSepClosed (IsLocalRing.ResidueField S)]
    [Module.Finite S E] [Algebra.Etale S E] :
    Algebra.IsFiniteSplit S E := by
  classical
  haveI : Infinite (IsLocalRing.ResidueField S) := IsSepClosed.infinite _
  haveI : Module.Free S E := Module.free_of_flat_of_isLocalRing
  haveI : Algebra.Etale (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] E) :=
    Algebra.Etale.baseChange S E (IsLocalRing.ResidueField S)
  obtain ⟨n, β₀, a, ha, hgen₀, hmin₀⟩ := Algebra.IsFiniteSplit.exists_minpoly_eq_prod
    (k := IsLocalRing.ResidueField S) (A := IsLocalRing.ResidueField S ⊗[S] E)
  obtain ⟨β, hβ⟩ := TensorProduct.mk_surjective S E (IsLocalRing.ResidueField S)
    Ideal.Quotient.mk_surjective β₀
  rw [TensorProduct.mk_apply] at hβ
  have hgen : Algebra.adjoin S {β} = ⊤ :=
    IsLocalRing.adjoin_eq_top_of_residue β (by rw [hβ]; exact hgen₀)
  have hfmonic : (minpoly S β).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral β)
  have H := IsAdjoinRootMonic.mkOfAdjoinEqTop' hgen
  have hn₀ : (minpoly (IsLocalRing.ResidueField S) β₀).natDegree = n := by
    rw [hmin₀, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
    simp
  have hfinbc : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] E) = Module.finrank S E := Module.finrank_baseChange
  have hdeg : (minpoly S β).natDegree = n := by
    have h1 := H.finrank
    have h2 := (IsAdjoinRootMonic.mkOfAdjoinEqTop' hgen₀).finrank
    rw [hfinbc, hn₀] at h2
    omega
  have hmap : (minpoly S β).map (IsLocalRing.residue S)
      = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    rw [← hmin₀]
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral β₀)) (hfmonic.map _) (minpoly.dvd _ _ ?_) ?_
    · rw [← hβ, ← IsLocalRing.one_tmul_aeval, minpoly.aeval, TensorProduct.tmul_zero]
    · rw [hfmonic.natDegree_map, hdeg, hn₀]
  obtain ⟨b, hb1, hb2⟩ := HenselianLocalRing.exists_roots_of_map_eq_prod hfmonic a ha hmap
  refine Algebra.IsFiniteSplit.of_isAdjoinRootMonic_of_roots H hdeg b hb1 (fun i j hij => ?_)
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
    map_sub, hb2 i, hb2 j, sub_eq_zero]
  exact fun h => hij (ha h).symm

/-- **(E2) A SPLIT COCOMMUTATIVE GROUP SCHEME OVER A LOCAL BASE IS THE CONSTANT ONE** — the
group-scheme half of SGA 3, Exp. VIII. **PROVEN**, over the `Points` section above.

If the coordinate ring `X` of a finite flat commutative group scheme over a LOCAL ring `S` is
split as an `S`-ALGEBRA (`Algebra.IsFiniteSplit S X`, i.e. `X ≅ Πⁿ S`), then it is the constant
group scheme on a finite abelian group: `X ≃ₐc[S] GroupFunctions S Γ`.

THE ARGUMENT AS FORMALISED. `Γ := WithConv (X →ₐ[S] S)`, the `S`-points under CONVOLUTION;
mathlib's `AlgHom.convGroup` already makes that a `Group` (unit `ε`, inverse `φ ∘ antipode`) and
upgrades it to a `CommGroup` under `Coalgebra.IsCocomm S X`, so no group structure is built here.
The map is `pointsAlgHom : x ↦ (φ ↦ φ x)`, and the three obligations are discharged separately:

* it is an `S`-ALGEBRA map, pointwise and by construction;
* it respects the COUNIT (`counitAlgHom_comp_pointsAlgHom`) because the counit of
  `GroupFunctions` is evaluation at `1 : Γ` and `1 : Γ` IS `ε`;
* it respects the COMULTIPLICATION (`map_comp_comulAlgHom_pointsAlgHom`) because, read through
  `GroupFunctions.tensorEquiv`, both sides at `(φ, ψ)` are `∑ φ(x₁) ψ(x₂)` over a Sweedler
  representation of `Δx` — that is literally `AlgHom.convMul_apply`, i.e. the group law on
  points is convolution;
* it is BIJECTIVE (`pointsAlgHom_bijective_of_equiv`) because under a splitting
  `e : X ≃ₐ[S] (Fin n → S)` the points are exactly the `n` projections (`splitPointsEquiv`,
  over `Pi.exists_eq_evalAlgHom_of_isLocalRing`), so `pointsAlgHom` is `e` followed by a
  relabelling of coordinates.

`BialgEquiv.ofAlgEquiv` then assembles it.

CORRECTION TO THE ROUTE ORIGINALLY RECORDED HERE. Two of its ingredients turned out not to be
needed. (i) `Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` is stated over a FIELD base and does
not apply; the local-base statement is proven directly from orthogonal idempotents and is shorter
than transporting the spectrum. (ii) `GroupFunctions.pointsMulEquiv` is NOT used: bijectivity is
obtained by transporting along the splitting, which never needs to know the points of
`GroupFunctions S Γ`. Likewise `GroupFunctions.comul_single` is not used — the comultiplication
is matched through `tensorEquiv` rather than on the idempotent basis. `[Module.Finite S X]` and
`[Module.Free S X]` are also redundant (both follow from `Algebra.IsFiniteSplit`); they are kept
because they are part of the statement the consumer was written against.

FAITHFULNESS: `[IsLocalRing S]` IS LOAD-BEARING and may not be weakened to a general base.
`Algebra.IsFiniteSplit S X` only says `X ≅ Πⁿ S` as an ALGEBRA; if `Spec S` is DISCONNECTED the
group law may differ from component to component, and then no single `Γ` works. Explicitly: with
`S = k × k` and `n = 4`, the group scheme that is `ℤ/4` over the first factor and `(ℤ/2)²` over
the second is split as an algebra, cocommutative, finite free — and is not `GroupFunctions S Γ`
for any `Γ`, since base-changing to the two factors would force `Γ` to be both cyclic and not.
Over a local ring the only idempotents are `0` and `1`, which is exactly what rules this out —
and it is the single point where locality is consumed, in
`IsIdempotentElem.eq_zero_or_one_of_isLocalRing`. Not vacuous: `X = S` satisfies every
hypothesis, with `Γ` trivial. -/
theorem exists_bialgEquiv_groupFunctions_of_isFiniteSplit
    (S X : Type u) [CommRing S] [IsLocalRing S] [CommRing X] [HopfAlgebra S X]
    [Coalgebra.IsCocomm S X] [Module.Finite S X] [Module.Free S X]
    [Algebra.IsFiniteSplit S X] :
    ∃ (Γ : Type u) (_ : CommGroup Γ) (_ : Fintype Γ) (_ : DecidableEq Γ),
      Nonempty (X ≃ₐc[S] GroupFunctions S Γ) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun S X
  have hbij : Function.Bijective (pointsAlgHom S X) := pointsAlgHom_bijective_of_equiv S X e
  haveI : Fintype (WithConv (X →ₐ[S] S)) :=
    Fintype.ofEquiv (Fin n) ((splitPointsEquiv S X e).trans (WithConv.equiv (X →ₐ[S] S)).symm)
  haveI : DecidableEq (WithConv (X →ₐ[S] S)) := Classical.decEq _
  refine ⟨WithConv (X →ₐ[S] S), inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact BialgEquiv.ofAlgEquiv (AlgEquiv.ofBijective (pointsAlgHom S X) hbij)
    (counitAlgHom_comp_pointsAlgHom S X) (map_comp_comulAlgHom_pointsAlgHom S X)

/-- **MULTIPLICATIVE TYPE OVER A STRICTLY HENSELIAN LOCAL BASE IS DIAGONALIZABLE** — the
group-like elements span. PROVEN, as an assembly over `(E1)` and `(E2)`.

`hmult` says the Cartier dual `X := Aᴰ` is étale over `S`; `(E1)` splits it; `(E2)` identifies it
with the constant group scheme `GroupFunctions S Γ`. Cartier duality then carries that
identification back — `CartierDual.congr` — and BIDUALITY (`CartierDual.bidualityBialgEquiv`,
proven unconditionally in `CartierDual.lean`) together with the diagonalizable dictionary
`CartierDual.groupAlgebraBialgEquivDual` turns it into `MonoidAlgebra S Γ ≃ₐc[S] A`. The
group-likes `single γ 1` of a group algebra are a BASIS, so their images span. -/
theorem exists_spanning_groupLike_of_isMultiplicativeType
    (S A : Type u) [CommRing S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)]
    [CommRing A] [HopfAlgebra S A] [Coalgebra.IsCocomm S A]
    [Module.Finite S A] [Module.Free S A]
    (hmult : IsMultiplicativeType S A) :
    ∃ (ι : Type u) (x : ι → A),
      (∀ i, Coalgebra.counit (R := S) (x i) = (1 : S)) ∧
      (∀ i, Coalgebra.comul (R := S) (x i) = x i ⊗ₜ[S] x i) ∧
      Submodule.span S (Set.range x) = ⊤ := by
  haveI : Algebra.Etale S (CartierDual S A) := hmult
  haveI : Algebra.IsFiniteSplit S (CartierDual S A) :=
    Algebra.IsFiniteSplit.of_henselianLocalRing S (CartierDual S A)
  obtain ⟨Γ, _, _, _, ⟨e⟩⟩ :=
    exists_bialgEquiv_groupFunctions_of_isFiniteSplit S (CartierDual S A)
  -- `A ≃ₐc[S] MonoidAlgebra S Γ`, read backwards
  let φ : MonoidAlgebra S Γ ≃ₐc[S] A :=
    ((CartierDual.groupAlgebraBialgEquivDual S Γ).trans (CartierDual.congr e)).trans
      (CartierDual.bidualityBialgEquiv S A).symm
  -- the group-likes of a group algebra
  have hgl : ∀ γ : Γ, IsGroupLikeElem S (MonoidAlgebra.single γ (1 : S)) := fun γ =>
    { counit_eq_one := by simp
      comul_eq_tmul_self := by simp }
  refine ⟨Γ, fun γ => φ (MonoidAlgebra.single γ (1 : S)), fun γ => ((hgl γ).map φ).counit_eq_one,
    fun γ => ((hgl γ).map φ).comul_eq_tmul_self, ?_⟩
  set lφ : MonoidAlgebra S Γ →ₗ[S] A := (φ : MonoidAlgebra S Γ →ₗ[S] A)
  have hspan : Submodule.span S (Set.range fun γ : Γ => MonoidAlgebra.single γ (1 : S)) = ⊤ :=
    (MonoidAlgebra.basis Γ S).span_eq
  have hrange : (Set.range fun γ : Γ => φ (MonoidAlgebra.single γ (1 : S)))
      = lφ '' (Set.range fun γ : Γ => MonoidAlgebra.single γ (1 : S)) := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    exact ⟨fun ⟨γ, hγ⟩ => ⟨_, ⟨γ, rfl⟩, hγ⟩, fun ⟨_, ⟨γ, rfl⟩, hγ⟩ => ⟨γ, hγ⟩⟩
  rw [hrange, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact φ.surjective

/-- **The BASE-CHANGED form of the theorem above** — `A` lives over a small base `R` and the
conclusion is about `S ⊗[R] A` for a strictly henselian `S`. This is the shape an arithmetic
consumer wants (`A` a group scheme over `𝒪ᵖᵥ`, `S = 𝒪ᵘⁿʳ` the strict henselisation), and it is
one composition of the two theorems above.

PERFORMANCE, and the reason this corollary exists rather than being inlined at the call site.
Stating it here means the `HopfAlgebra`/`IsCocomm`/`Module.Finite`/`Module.Free` instances on the
tensor product `S ⊗[R] A` are synthesized ONCE, against ABSTRACT `R`, `S`, `A`. Written out at the
call site they are re-synthesized against the concrete `unramifiedIntegers p` — a *reducible*
`abbrev` for `IntegralClosure 𝒪ᵖᵥ ↥(unramifiedSubfield p)`, itself an `abbrev` for a `fixedField`
— so every unification step is free to unfold the whole tower.

Measured on `Family.lean` (11k lines), 2026-07-28, three builds of the same file differing only in
this one declaration's proof:

| proof of the consuming leaf                            | Family.lean elaboration |
|--------------------------------------------------------|------------------------|
| aborted at an unknown constant (control)                | **105 s**              |
| composition written out at the call site                | **3537 s**             |
| this corollary applied at the call site                 | **1288 s**             |

So the refactor is worth 37 minutes and is not optional; the residual ~20 minutes is the
unification of this conclusion against the leaf's goal, and is the price of the `abbrev`. If
`unramifiedIntegers`/`unramifiedSubfield` are ever changed from `abbrev` to `def` with the needed
instances re-exported, expect that residual to collapse too. -/
theorem exists_spanning_groupLike_baseChange_of_isMultiplicativeType
    (R S A : Type u) [CommRing R] [CommRing S] [Algebra R S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)]
    [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]
    (hmult : IsMultiplicativeType R A) :
    ∃ (ι : Type u) (x : ι → S ⊗[R] A),
      (∀ i, Coalgebra.counit (R := S) (x i) = (1 : S)) ∧
      (∀ i, Coalgebra.comul (R := S) (x i) = x i ⊗ₜ[S] x i) ∧
      Submodule.span S (Set.range x) = ⊤ :=
  exists_spanning_groupLike_of_isMultiplicativeType S (S ⊗[R] A)
    (isMultiplicativeType_baseChange R S A hmult)

end HopfAlgebra
