/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDualExamples
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.Etale.StandardEtale
public import Fermat.FLT.Deformations.RepresentationTheory.Etale

/-!
# The geometric points of `μ_n`, and the etaleness of its generic fibre

`CartierDual.MuCoord R n = R[ℤ/n]` (`CartierDualExamples.lean`) is the coordinate ring of
the group scheme `μ_n` of `n`-th roots of unity over `R`. That file supplies its Hopf
structure (from mathlib's `MonoidAlgebra.instHopfAlgebra`) and its Cartier dual, and
nothing else. This file supplies the three things a FLAT-MODEL argument needs and which
that file leaves out:

* `MuPoints.muCoordPointEquiv` — **the geometric points**: an `A`-point of `μ_n` is
  exactly an `n`-th root of unity in `A`, `φ ↦ φ X`. PROVEN.
* `MuPoints.muCoord_convMul`, `MuPoints.muCoord_convOne`,
  `MuPoints.muCoord_smul_apply` — under that identification the CONVOLUTION product of
  points (the group law of `μ_n`, i.e. the monoid structure on `A →ₐ[K] L` of
  `Deformations/RepresentationTheory/Etale.lean`) is MULTIPLICATION of roots of unity,
  the unit is `1`, and the Galois action is the Galois action on roots of unity. PROVEN.
* `MuPoints.muCoord_etale` — **the generic fibre is etale** as soon as `n` is invertible:
  `μ_n` over a field `K` with `(n : K) ≠ 0` is the standard etale algebra of the pair
  `(X ^ n - 1, 1)`, whose `cond` is witnessed by `n X^{n-1} · (X/n) − (X^n − 1) = 1`.
  PROVEN, over mathlib's `StandardEtalePair`.
* `MuPoints.muMap` — the map of Hopf algebras `μ_n → μ_m` attached to an `n`-torsion
  element `w` of `ZMod m`; on points it is `ζ ↦ ζ ^ w` (`muMap_muGen`). At
  `w = X ^ p`, `n = p ^ k`, `m = p ^ (k+1)` this is the inclusion `μ_{p^k} ↪ μ_{p^{k+1}}`
  of a `p`-divisible group, whose effect on points is `ζ ↦ ζ ^ p`. PROVEN.

Flatness and finiteness need no work here: `MonoidAlgebra R G` is `Finsupp`, hence free,
hence flat, and finite for finite `G` — all mathlib instances, and `MuCoord` inherits
them.

WHY THIS IS NOT A DUPLICATE OF `GroupFunctions.lean`. That file builds the CONSTANT group
scheme `ℤ/n`, whose points carry the TRIVIAL Galois action; this one is its Cartier dual
`μ_n`, whose points carry the CYCLOTOMIC action. Both are needed and neither is
constructible from the other over a base that does not contain the roots of unity —
which is the whole content of `CartierDual.muDualEquivZMod`'s asymmetry.
-/

@[expose] public section

open TensorProduct Polynomial CartierDual

universe u

namespace MuPoints

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The tautological generator `X` of `μ_n`. -/
noncomputable def muGen : MuCoord R n :=
  MonoidAlgebra.single (Multiplicative.ofAdd 1) 1

variable {R n}

theorem muGen_def : muGen R n = MonoidAlgebra.single (Multiplicative.ofAdd 1) 1 := rfl

theorem ofAdd_one_pow : (Multiplicative.ofAdd (1 : ZMod n)) ^ n = 1 := by
  rw [← ofAdd_nsmul]; norm_num

theorem muGen_pow_eq_one : (muGen R n) ^ n = 1 := by
  rw [muGen_def, MonoidAlgebra.single_pow, one_pow, ofAdd_one_pow]; rfl

theorem pow_mod_eq {A : Type*} [Monoid A] {u : A} (hu : u ^ n = 1) (x : ℕ) :
    u ^ (x % n) = u ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n]
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

/-- The monoid hom out of the cyclic group determined by an `n`-th root of unity. -/
noncomputable def zmodPowHom {A : Type*} [CommMonoid A] (hn : n ≠ 0)
    {u : A} (hu : u ^ n = 1) : Multiplicative (ZMod n) →* A where
  toFun a := u ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    haveI : NeZero n := ⟨hn⟩
    have hv : (Multiplicative.toAdd (a * b)).val =
        ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % n :=
      ZMod.val_add _ _
    simp only [hv, pow_mod_eq hu, pow_add]

@[simp]
theorem zmodPowHom_ofAdd_one {A : Type*} [CommMonoid A] (hn : n ≠ 0)
    {u : A} (hu : u ^ n = 1) :
    zmodPowHom hn hu (Multiplicative.ofAdd 1) = u := by
  show u ^ (ZMod.val (1 : ZMod n)) = u
  rw [ZMod.val_one_eq_one_mod, pow_mod_eq hu, pow_one]

/-- A monoid hom out of the cyclic group is determined at the generator. -/
theorem monoidHom_ext {A : Type*} [CommMonoid A] (hn : n ≠ 0)
    {f g : Multiplicative (ZMod n) →* A}
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  haveI : NeZero n := ⟨hn⟩
  refine MonoidHom.ext fun a => ?_
  obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective (Multiplicative.toAdd a)
  have ha : a = (Multiplicative.ofAdd (1 : ZMod n)) ^ m := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, hm]; rfl
  rw [ha, map_pow, map_pow, h]

/-- Algebra maps out of `μ_n` are determined at the generator. -/
theorem muCoord_algHom_ext {A : Type u} [CommRing A] [Algebra R A] (hn : n ≠ 0)
    {φ ψ : MuCoord R n →ₐ[R] A} (h : φ (muGen R n) = ψ (muGen R n)) : φ = ψ := by
  refine (MonoidAlgebra.lift R A _).symm.injective (monoidHom_ext hn ?_)
  exact h

theorem lift_apply_muGen {A : Type u} [CommRing A] [Algebra R A]
    (f : Multiplicative (ZMod n) →* A) :
    MonoidAlgebra.lift R A _ f (muGen R n) = f (Multiplicative.ofAdd 1) := by
  rw [muGen_def, MonoidAlgebra.lift_single, one_smul]

/-- **THE GEOMETRIC POINTS OF `μ_n`**: an `A`-point is an `n`-th root of unity. -/
noncomputable def muCoordPointEquiv {A : Type u} [CommRing A] [Algebra R A] (hn : n ≠ 0) :
    (MuCoord R n →ₐ[R] A) ≃ {ζ : A // ζ ^ n = 1} where
  toFun φ := ⟨φ (muGen R n), by rw [← map_pow, muGen_pow_eq_one, map_one]⟩
  invFun ζ := MonoidAlgebra.lift R A _ (zmodPowHom hn ζ.2)
  left_inv φ := by
    refine muCoord_algHom_ext hn ?_
    rw [lift_apply_muGen, zmodPowHom_ofAdd_one]
  right_inv ζ := by
    refine Subtype.ext ?_
    show MonoidAlgebra.lift R A _ (zmodPowHom hn ζ.2) (muGen R n) = (ζ : A)
    rw [lift_apply_muGen, zmodPowHom_ofAdd_one]

/-- The map of Hopf algebras `μ_n → μ_m` attached to an `n`-torsion element of
`ZMod m`; on points it is `ζ ↦ ζ ^ (that element)`. -/
noncomputable def muMap (hn : n ≠ 0) {m : ℕ} {w : Multiplicative (ZMod m)}
    (hw : w ^ n = 1) : MuCoord R n →ₐ[R] MuCoord R m :=
  MonoidAlgebra.mapDomainAlgHom R R (zmodPowHom hn hw)

@[simp]
theorem muMap_muGen (hn : n ≠ 0) {m : ℕ} {w : Multiplicative (ZMod m)} (hw : w ^ n = 1) :
    muMap (R := R) hn hw (muGen R n) = MonoidAlgebra.single w 1 := by
  rw [muMap, muGen_def, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    zmodPowHom_ofAdd_one]

/-! ### The convolution product on points is multiplication of roots of unity -/

section Conv
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem muCoord_comul_muGen :
    Coalgebra.comul (R := K) (muGen K n) = muGen K n ⊗ₜ[K] muGen K n := by
  rw [muGen_def]; simp

theorem muCoord_convMul (φ ψ : MuCoord K n →ₐ[K] L) :
    (φ * ψ) (muGen K n) = φ (muGen K n) * ψ (muGen K n) := by
  show Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _)
    (Coalgebra.comul (R := K) (muGen K n)) = _
  rw [muCoord_comul_muGen]
  simp

theorem muCoord_convOne : (1 : MuCoord K n →ₐ[K] L) (muGen K n) = 1 := by
  show (Algebra.ofId K L) (Bialgebra.counitAlgHom K (MuCoord K n) (muGen K n)) = 1
  rw [muGen_def]
  simp

theorem muCoord_smul_apply (σ : L ≃ₐ[K] L) (φ : MuCoord K n →ₐ[K] L) :
    (σ • φ) (muGen K n) = σ (φ (muGen K n)) := rfl

end Conv

/-! ### The generic fibre is etale -/

section Etale
variable {K : Type u} [Field K]

/-- The standard etale pair `(X ^ n - 1, 1)` over a field in which `n` is invertible. -/
noncomputable def muPair (hn : (n : K) ≠ 0) : StandardEtalePair K where
  f := X ^ n - 1
  monic_f := by
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    simpa using Polynomial.monic_X_pow_sub_C (1 : K) hn0
  g := 1
  cond := by
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    refine ⟨C ((n : K)⁻¹) * X, -1, 1, ?_⟩
    have hx : (X : K[X]) ^ (n - 1) * X = X ^ n := by
      rw [← pow_succ, Nat.sub_add_cancel hn1]
    have hc : (C (n : K)) * (C ((n : K)⁻¹)) = 1 := by
      rw [← C_mul, mul_inv_cancel₀ hn, C_1]
    rw [derivative_sub, derivative_one, derivative_X_pow, sub_zero, pow_one]
    calc C (n : K) * X ^ (n - 1) * (C ((n : K)⁻¹) * X) + (X ^ n - 1) * (-1)
        = (C (n : K) * C ((n : K)⁻¹)) * (X ^ (n - 1) * X) + (X ^ n - 1) * (-1) := by ring
      _ = 1 := by rw [hc, hx]; ring

@[simp] theorem muPair_f (hn : (n : K) ≠ 0) : (muPair (K := K) (n := n) hn).f = X ^ n - 1 := rfl
@[simp] theorem muPair_g (hn : (n : K) ≠ 0) : (muPair (K := K) (n := n) hn).g = 1 := rfl

theorem muPair_X_pow (hn : (n : K) ≠ 0) : (muPair (K := K) (n := n) hn).X ^ n = 1 := by
  have h := (muPair (K := K) (n := n) hn).hasMap_X.1
  rw [muPair_f] at h
  simp only [map_sub, map_one, map_pow, aeval_X] at h
  linear_combination h

theorem muHasMap (hn : (n : K) ≠ 0) :
    (muPair (K := K) (n := n) hn).HasMap (muGen K n) := by
  constructor
  · rw [muPair_f]
    simp only [map_sub, map_one, map_pow, aeval_X]
    rw [muGen_pow_eq_one, sub_self]
  · rw [muPair_g]
    simp

/-- **THE GENERIC FIBRE OF `μ_n` IS ETALE** when `n` is invertible: `μ_n` is the
standard etale algebra of the pair `(X ^ n - 1, 1)`. -/
noncomputable def muStdEtale (hn : (n : K) ≠ 0) :
    StandardEtalePresentation K (MuCoord K n) where
  __ := muPair hn
  x := muGen K n
  hasMap := muHasMap hn
  lift_bijective := by
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    set P := muPair (K := K) (n := n) hn with hP
    set Φ := P.lift (muGen K n) (muHasMap hn) with hΦ
    set Ψ : MuCoord K n →ₐ[K] P.Ring :=
      MonoidAlgebra.lift K P.Ring _ (zmodPowHom hn0 (muPair_X_pow hn)) with hΨ
    have hΨg : Ψ (muGen K n) = P.X := by
      rw [hΨ, lift_apply_muGen, zmodPowHom_ofAdd_one]
    have h1 : Φ.comp Ψ = AlgHom.id K (MuCoord K n) := by
      refine muCoord_algHom_ext hn0 ?_
      show Φ (Ψ (muGen K n)) = muGen K n
      rw [hΨg, hΦ, StandardEtalePair.lift_X]
    have h2 : Ψ.comp Φ = AlgHom.id K P.Ring := by
      refine P.hom_ext ?_
      show Ψ (Φ P.X) = P.X
      rw [hΦ, StandardEtalePair.lift_X, hΨg]
    exact (AlgEquiv.ofAlgHom Φ Ψ h1 h2).bijective

theorem muCoord_etale (hn : (n : K) ≠ 0) : Algebra.Etale K (MuCoord K n) :=
  haveI : Algebra.IsStandardEtale K (MuCoord K n) := ⟨⟨muStdEtale hn⟩⟩
  inferInstance

end Etale

end MuPoints
