/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Henselian
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Splitting finite etale algebras over a strictly henselian local ring

Supporting commutative algebra for `Algebra.IsFiniteSplit.of_henselianLocalRing` (Stacks
[04GG](https://stacks.math.columbia.edu/tag/04GG)): a finite etale algebra over a henselian
local ring with separably closed residue field is split. Nothing here mentions Hopf algebras
or group schemes; it is general commutative algebra and is plausibly upstreamable.

## Main statements

* `Algebra.IsFiniteSplit.of_algHom_family` — `n` algebra maps `A -> R` whose evaluation matrix
  against an `n`-element basis is invertible split `A`. PROVEN.
* `Algebra.IsFiniteSplit.of_isAdjoinRootMonic_of_roots` — **Vandermonde splitting**: if
  `A = R[X]/(f)` with `f` monic of degree `n` having `n` roots in `R` with pairwise-UNIT
  differences, then `A` is split. PROVEN.
* `Algebra.IsFiniteSplit.exists_minpoly_eq_prod` — a split algebra over an INFINITE field is
  monogenic, with a generator whose minimal polynomial is `∏ (X - a i)`, the `a i` distinct.
  PROVEN, by Lagrange interpolation.
* `HenselianLocalRing.exists_roots_of_map_eq_prod` — Hensel-lift the roots of a monic `f` whose
  reduction is a product of DISTINCT monic linear factors. PROVEN.
* `IsLocalRing.adjoin_eq_top_of_residue` — Nakayama: a generator of `k ⊗[S] E` over the residue
  field lifts to a generator of `E` over `S`. PROVEN.
* `IsSepClosed.infinite` — a separably closed field is infinite. PROVEN.

## Design note: why NOT the idempotent-lifting route

The route usually quoted for [04GG] — split the residue algebra, then LIFT its `n` orthogonal
idempotents because `S` is henselian — is not available over this mathlib pin. `Henselian` occurs
in exactly ONE mathlib file (`Mathlib/RingTheory/Henselian.lean`), which offers only the
polynomial root-lifting form; mathlib's idempotent lifting
(`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`) is along NIL ideals only, and the
maximal ideal of a henselian local ring is not nil. Taking that route would mean first proving
"henselian implies idempotents lift", itself a substantial development.

The route taken here instead uses only the polynomial form, which IS mathlib's *definition* of
`HenselianLocalRing`:

1. `E` is finite flat over the local ring `S`, hence free; `k ⊗[S] E` is finite etale over the
   separably closed `k`, hence split (mathlib's instance over a FIELD).
2. A separably closed field is infinite, so the split algebra `k ⊗[S] E` is monogenic, generated
   by some `β₀` whose minimal polynomial is `∏ (X - a i)` with the `a i` DISTINCT (Lagrange
   interpolation supplies the generator).
3. Nakayama lifts `β₀` to a generator `β` of `E` over `S`, so `E ≅ S[X]/(f)` with `f = minpoly S β`
   monic; comparing degrees, `f.map (residue S) = ∏ (X - a i)`.
4. Each `a i` is a SIMPLE root of `f mod m` (the `a i` are distinct), so Hensel lifts it to a root
   `b i ∈ S`. Distinct residues make each `b j - b i` a unit in the local ring `S`.
5. The `n` algebra maps `E → S`, `β ↦ b i`, assemble into `E → Fin n → S` whose matrix in the
   basis `1, β, …, β^{n-1}` is VANDERMONDE, with determinant `∏_{i<j} (b j - b i)` a unit — so it
   is an isomorphism and `E` is split.

## References

* Stacks Project, [04GG](https://stacks.math.columbia.edu/tag/04GG).
-/

@[expose] public section

open Polynomial TensorProduct

universe u


namespace Algebra.IsFiniteSplit

/-- If an `R`-algebra `A` admits a basis indexed by `Fin n` and `n` algebra maps `A →ₐ[R] R`
whose evaluation matrix against that basis is invertible, then `A` is split. -/
theorem of_algHom_family {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (b : Module.Basis (Fin n) R A) (φ : Fin n → (A →ₐ[R] R))
    (h : IsUnit (Matrix.of fun i j => φ i (b j)).det) :
    Algebra.IsFiniteSplit R A := by
  classical
  set M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => φ i (b j) with hM
  set F : A →ₐ[R] (Fin n → R) := AlgHom.pi φ with hF
  have hmat : LinearMap.toMatrix b (Pi.basisFun R (Fin n)) F.toLinearMap = M := by
    ext i j
    simp [LinearMap.toMatrix_apply, hF, hM]
  have htoLin : Matrix.toLin b (Pi.basisFun R (Fin n)) M = F.toLinearMap := by
    rw [← hmat, Matrix.toLin_toMatrix]
  letI : Invertible M := M.invertibleOfIsUnitDet h
  have hMM' : M * (⅟M) = 1 := mul_invOf_self M
  have hM'M : (⅟M) * M = 1 := invOf_mul_self M
  have he : ((Matrix.toLinOfInv b (Pi.basisFun R (Fin n)) hMM' hM'M) : A → (Fin n → R))
      = (F : A → (Fin n → R)) := by
    funext x
    have := congrArg (fun g : A →ₗ[R] (Fin n → R) => g x) htoLin
    simpa [Matrix.toLinOfInv] using this
  have hbij : Function.Bijective F :=
    he ▸ (Matrix.toLinOfInv b (Pi.basisFun R (Fin n)) hMM' hM'M).bijective
  exact ⟨n, ⟨AlgEquiv.ofBijective F hbij⟩⟩

/-- **Vandermonde splitting.** If `A = R[β]` is presented as `R[X]/(f)` with `f` monic of degree
`n`, and `f` has `n` roots in `R` with pairwise-unit differences, then `A ≃ₐ[R] Fin n → R`. -/
theorem of_isAdjoinRootMonic_of_roots {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {f : R[X]} (H : IsAdjoinRootMonic A f) {n : ℕ} (hn : f.natDegree = n) (a : Fin n → R)
    (haroot : ∀ i, aeval (a i) f = 0)
    (hsep : ∀ i j, i ≠ j → IsUnit (a j - a i)) :
    Algebra.IsFiniteSplit R A := by
  classical
  subst hn
  refine of_algHom_family H.basis (fun i => H.liftHom (a i) (haroot i)) ?_
  have hentry : (Matrix.of fun i j => (H.liftHom (a i) (haroot i)) (H.basis j))
      = Matrix.vandermonde a := by
    ext i j
    simp [H.basis_apply, map_pow, IsAdjoinRoot.liftHom_root, Matrix.vandermonde]
  rw [hentry, Matrix.det_vandermonde]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => ?_)
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j hj => ?_)
  exact hsep i j (Finset.mem_Ioi.mp hj).ne

end Algebra.IsFiniteSplit

/-- A separably closed field is infinite: a finite field is perfect, and a perfect separably
closed field is algebraically closed, hence infinite. -/
theorem IsSepClosed.infinite (k : Type*) [Field k] [IsSepClosed k] : Infinite k := by
  rw [← not_finite_iff_infinite]
  intro hfin
  haveI : Finite k := hfin
  haveI : PerfectField k := inferInstance
  haveI : IsAlgClosed k := isAlgClosed_of_perfectField k
  exact (not_finite k)

/-- Evaluating the derivative of `∏ (X - a j)` at `a i` gives `∏_{j ≠ i} (a i - a j)`. -/
theorem Polynomial.eval_derivative_prod_X_sub_C_at {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → K) (i : Fin n) :
    eval (a i) (derivative (∏ j, (X - C (a j)))) = ∏ j ∈ Finset.univ.erase i, (a i - a j) := by
  classical
  rw [Polynomial.derivative_prod_finset, eval_finsetSum,
    Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp [eval_prod]
  · have hz : (∏ l ∈ Finset.univ.erase j, (X - C (a l))).eval (a i) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) (by simp)
    simp [hz]

namespace Algebra.IsFiniteSplit

/-- A split algebra over an INFINITE field is monogenic, and one may choose the generator so that
its minimal polynomial is a product of distinct monic linear factors. -/
theorem exists_minpoly_eq_prod {k A : Type*} [Field k] [Infinite k] [CommRing A] [Algebra k A]
    [Algebra.IsFiniteSplit k A] :
    ∃ (n : ℕ) (β : A) (a : Fin n → k), Function.Injective a ∧
      Algebra.adjoin k {β} = ⊤ ∧ minpoly k β = ∏ i, (X - C (a i)) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k A
  set a : Fin n → k := fun i => Infinite.natEmbedding k (i : ℕ) with hadef
  have ha : Function.Injective a := fun i j h =>
    Fin.val_injective ((Infinite.natEmbedding k).injective h)
  set β : A := e.symm a with hβdef
  -- evaluation of a polynomial at `a` in the product algebra is coordinatewise evaluation
  have hpi : ∀ (p : k[X]) (i : Fin n), (aeval a p) i = eval (a i) p := fun p i => by
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom k (fun _ : Fin n => k) i) a p
    simp
  have heβ : e β = a := by rw [hβdef]; exact e.apply_symm_apply a
  have hgen : Algebra.adjoin k {β} = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    intro x
    refine ⟨Lagrange.interpolate Finset.univ a (e x), e.injective ?_⟩
    rw [← Polynomial.aeval_algHom_apply e β, heβ]
    funext i
    rw [hpi]
    exact Lagrange.eval_interpolate_at_node _ (ha.injOn) (Finset.mem_univ i)
  have hmonic : (∏ i, (X - C (a i)) : k[X]).Monic :=
    monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hroot : aeval β (∏ i, (X - C (a i))) = 0 := by
    refine e.injective ?_
    rw [← Polynomial.aeval_algHom_apply e β, heβ, map_zero]
    funext i
    rw [hpi, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hgdeg : (∏ i, (X - C (a i)) : k[X]).natDegree = n := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp
  have hfin : Module.finrank k A = n := by
    rw [e.toLinearEquiv.finrank_eq]
    simp
  have hdeg : (minpoly k β).natDegree = n := by
    have h := (IsAdjoinRootMonic.mkOfAdjoinEqTop' hgen).finrank
    rw [hfin] at h
    exact h.symm
  refine ⟨n, β, a, ha, hgen, ?_⟩
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral β)) hmonic
    (minpoly.dvd k β hroot) ?_).symm
  omega

end Algebra.IsFiniteSplit

/-- **Hensel root lifting for a split reduction.** If `f` is monic over a henselian local ring `S`
and its reduction to the residue field is a product of distinct monic linear factors `X - a i`,
then each `a i` lifts to a genuine root of `f` in `S`. -/
theorem HenselianLocalRing.exists_roots_of_map_eq_prod {S : Type*} [CommRing S]
    [HenselianLocalRing S] {f : S[X]} (hf : f.Monic) {n : ℕ}
    (a : Fin n → IsLocalRing.ResidueField S) (ha : Function.Injective a)
    (hmap : f.map (IsLocalRing.residue S) = ∏ i, (X - C (a i))) :
    ∃ b : Fin n → S, (∀ i, aeval (b i) f = 0) ∧ (∀ i, IsLocalRing.residue S (b i) = a i) := by
  classical
  choose c hc using fun i => IsLocalRing.residue_surjective (R := S) (a i)
  have key : ∀ i, ∃ b : S, f.IsRoot b ∧ b - c i ∈ IsLocalRing.maximalIdeal S := by
    intro i
    refine HenselianLocalRing.is_henselian f hf (c i) ?_ ?_
    · rw [← IsLocalRing.residue_eq_zero_iff]
      have hev : (f.map (IsLocalRing.residue S)).eval (a i)
          = IsLocalRing.residue S (f.eval (c i)) := by
        rw [← hc i, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      rw [← hev, hmap, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    · have hev : (derivative (f.map (IsLocalRing.residue S))).eval (a i)
          = IsLocalRing.residue S ((derivative f).eval (c i)) := by
        rw [Polynomial.derivative_map, ← hc i, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      have hne : IsLocalRing.residue S ((derivative f).eval (c i)) ≠ 0 := by
        rw [← hev, hmap, Polynomial.eval_derivative_prod_X_sub_C_at]
        refine Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (fun hEq => ?_))
        exact (Finset.mem_erase.mp hj).1 (ha hEq).symm
      exact IsLocalRing.notMem_maximalIdeal.mp
        (fun hm => hne ((IsLocalRing.residue_eq_zero_iff _).mpr hm))
  choose b hb1 hb2 using key
  refine ⟨b, fun i => by simpa using hb1 i, fun i => ?_⟩
  have h0 : IsLocalRing.residue S (b i - c i) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (hb2 i)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, hc i]

open IsLocalRing

/-- Base-changing `aeval` to the residue field. -/
theorem IsLocalRing.one_tmul_aeval {S E : Type u} [CommRing S] [IsLocalRing S] [CommRing E]
    [Algebra S E] (β : E) (q : S[X]) :
    (1 : ResidueField S) ⊗ₜ[S] (aeval β q)
      = aeval ((1 : ResidueField S) ⊗ₜ[S] β) (q.map (residue S)) := by
  rw [← ResidueField.algebraMap_eq, Polynomial.aeval_map_algebraMap]
  exact (Polynomial.aeval_algHom_apply
    (Algebra.TensorProduct.includeRight : E →ₐ[S] ResidueField S ⊗[S] E) β q).symm

/-- **Nakayama lift of a generator.** If the image of `β` in `k ⊗[S] E` generates that algebra
over the residue field `k`, then `β` generates `E` over `S`. -/
theorem IsLocalRing.adjoin_eq_top_of_residue {S E : Type u} [CommRing S] [IsLocalRing S]
    [CommRing E] [Algebra S E] [Module.Finite S E] (β : E)
    (hβ₀ : Algebra.adjoin (ResidueField S) {(1 : ResidueField S) ⊗ₜ[S] β} = ⊤) :
    Algebra.adjoin S {β} = ⊤ := by
  classical
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hβ₀
  refine Subalgebra.toSubmodule_injective ?_
  refine IsLocalRing.map_tensorProduct_mk_eq_top.mp (eq_top_iff.mpr fun y _ => ?_)
  obtain ⟨p, hp⟩ := hβ₀ y
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (residue S) residue_surjective p
  refine Submodule.mem_map.mpr ⟨aeval β q, ?_, ?_⟩
  · rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · rw [TensorProduct.mk_apply, IsLocalRing.one_tmul_aeval]
    exact hp
