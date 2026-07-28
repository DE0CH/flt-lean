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
  strictly henselian local ring is split. OPEN. Pure commutative algebra; a genuine gap in the
  mathlib pin, which has the statement only over a FIELD
  (`Algebra.FormallyEtale.equivPiOfIsSepClosed`).
* `HopfAlgebra.exists_bialgEquiv_groupFunctions_of_isFiniteSplit` — **(E2)**, a split
  cocommutative group scheme over a LOCAL base is the constant one. OPEN.
* `HopfAlgebra.exists_spanning_groupLike_of_isMultiplicativeType` — the theorem above. PROVEN
  over `(E1)` and `(E2)`.

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

/-! ## The two remaining leaves, and the assembly over them -/

/-- **(E1) A FINITE ÉTALE ALGEBRA OVER A STRICTLY HENSELIAN LOCAL RING IS SPLIT** (SORRY LEAF —
pure commutative algebra, no Hopf structure, no group schemes; a genuine gap in the mathlib pin).

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

FAITHFULNESS. `Module.Finite S E` is not implied by `Algebra.Etale S E` (which gives only finite
PRESENTATION as an algebra) and cannot be dropped: a localization `S_f` is étale over `S`
(mathlib's `Algebra.Etale (Localization.Away s)` instance) without being finite, and
`E = Localization.Away p = ℚ_p` over the henselian `S = ℤ_p` is not `Πⁿ ℤ_p` for any `n`.
Separable closedness of the RESIDUE FIELD is what forces
each factor to be `S` rather than a nontrivial unramified extension; over `ℤ_p` with its residue
field `𝔽_p` the statement is false for `E = 𝒪_{ℚ_p(ζ_ℓ)}`, `ℓ ≠ p`. Both hypotheses are therefore
load-bearing, and the leaf is not vacuous: `E = S` and `E = S × S` both satisfy it nontrivially. -/
theorem _root_.Algebra.IsFiniteSplit.of_henselianLocalRing
    (S E : Type u) [CommRing S] [CommRing E] [Algebra S E]
    [HenselianLocalRing S] [IsSepClosed (IsLocalRing.ResidueField S)]
    [Module.Finite S E] [Algebra.Etale S E] :
    Algebra.IsFiniteSplit S E :=
  sorry

/-- **(E2) A SPLIT COCOMMUTATIVE GROUP SCHEME OVER A LOCAL BASE IS THE CONSTANT ONE** (SORRY
LEAF — the group-scheme half of SGA 3, Exp. VIII; formal, no arithmetic).

If the coordinate ring `X` of a finite flat commutative group scheme over a LOCAL ring `S` is
split as an `S`-ALGEBRA (`Algebra.IsFiniteSplit S X`, i.e. `X ≅ Πⁿ S`), then it is the constant
group scheme on a finite abelian group: `X ≃ₐc[S] GroupFunctions S Γ`.

THE ARGUMENT. `X ≅ Πⁿ S` means `Spec X` is `n` disjoint copies of `Spec S`, i.e. the `S`-points
`Γ := X →ₐ[S] S` are `n` in number and the `n` orthogonal idempotents `e_γ` of `X` are their
indicator functions (`Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` is the field-base form of
this dictionary). The Hopf structure then makes `Γ` a group under CONVOLUTION —
`(φ ⋆ ψ)(x) = (φ ⊗ ψ)(Δ x)`, with unit `ε` and inverse `φ ∘ antipode`; `IsCocomm S X` makes it
ABELIAN — and `x ↦ (φ ↦ φ x)` is the required bialgebra map `X → GroupFunctions S Γ`, an
isomorphism because it carries the basis `e_γ` to the basis `GroupFunctions.single γ`. The
comultiplication matches because `Δ e_g = ∑ₐ e_a ⊗ e_{a⁻¹g}` (`GroupFunctions.comul_single`) is
precisely the statement that the group law on points is convolution.

`GroupFunctions.pointsMulEquiv` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/GroupFunctions.lean` is the CONVERSE dictionary,
already proven — the `L`-points of `GroupFunctions R G` with their convolution product ARE `G` —
so the two halves of the equivalence to be established here are: that dictionary, and the fact
that a split algebra is determined by its points.

FAITHFULNESS: `[IsLocalRing S]` IS LOAD-BEARING and may not be weakened to a general base.
`Algebra.IsFiniteSplit S X` only says `X ≅ Πⁿ S` as an ALGEBRA; if `Spec S` is DISCONNECTED the
group law may differ from component to component, and then no single `Γ` works. Explicitly: with
`S = k × k` and `n = 4`, the group scheme that is `ℤ/4` over the first factor and `(ℤ/2)²` over
the second is split as an algebra, cocommutative, finite free — and is not `GroupFunctions S Γ`
for any `Γ`, since `Γ` would have to be both cyclic and not. Over a local ring the only
idempotents are `0` and `1`, which is exactly what rules this out. -/
theorem exists_bialgEquiv_groupFunctions_of_isFiniteSplit
    (S X : Type u) [CommRing S] [IsLocalRing S] [CommRing X] [HopfAlgebra S X]
    [Coalgebra.IsCocomm S X] [Module.Finite S X] [Module.Free S X]
    [Algebra.IsFiniteSplit S X] :
    ∃ (Γ : Type u) (_ : CommGroup Γ) (_ : Fintype Γ) (_ : DecidableEq Γ),
      Nonempty (X ≃ₐc[S] GroupFunctions S Γ) :=
  sorry

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
