/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.AlphaP

/-!
# `α_p` is Cartier self-dual

`AlphaP.selfDualBialgEquiv : AlphaP R p ≃ₐc[R] CartierDual R (AlphaP R p)` — the third of the
three standard Cartier-duality examples, and the only one that is not a group-scheme duality
between a constant and a diagonalizable group (those are `μ_n^D ≅ ℤ/n` and `(ℤ/n)^D ≅ μ_n`, in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDualExamples.lean`).

## The argument

Write `A = O(α_p) = R[x]/(x^p)` and let `e_m` be the basis of `A^D` dual to the monomials `x^m`,
`m < p`. Everything follows from ONE computation, the binomial expansion of the additive
comultiplication:

  `Δ (x^n) = ∑_{k ≤ n} x^k ⊗ C(n,k) x^{n-k}`   (`AlphaP.comul_x_pow`)

packaged as a Sweedler representation (`AlphaP.reprXPow`). Feeding it to the convolution product
on the dual gives the **divided-power identity**

  `y^m = m! · e_m`,  where `y := e_1`   (`AlphaP.y_pow_eq_smul`),

proved in the sharper pointwise form `y^m (x^n) = m! · δ_{n,m}` (`AlphaP.y_pow_apply`) by
induction on `m`, the step being `C(m+1,m) · m! = (m+1)!`.

Three consequences, and they are the whole theorem:

* `y^p = 0` (`AlphaP.y_pow_p`), since `y^p (x^n) = δ_{n,p} = 0` for every `n < p`. So
  `AlphaP.lift` produces an algebra map `A → A^D` sending `x ↦ y`.
* `m!` is a **unit** in `R` for `m < p` (`AlphaP.isUnit_factorial`): `p ∤ m!` by
  `Nat.Prime.dvd_factorial`, and a natural number prime to `p` is invertible in any ring of
  characteristic `p` by Bézout in `ℤ` (`AlphaP.isUnit_natCast_of_not_dvd`). Hence `{y^m}_{m<p}`
  is again a basis (`AlphaP.dualBasisY`, via `Module.Basis.isUnitSMul`), so the map is bijective.
* `y` is **primitive**, `Δ y = y ⊗ 1 + 1 ⊗ y` (`AlphaP.comul_y`) — the transpose of
  `x^a · x^b = x^{a+b}`, since `⟨Δ y, x^a ⊗ x^b⟩ = y (x^{a+b}) = δ_{a+b,1}`. So the algebra
  isomorphism is a map of bialgebras, checked at `x` by `AlphaP.algHom_ext`.

This is the classical statement that the Frobenius kernel of `𝔾_a` is its own Cartier dual, with
the divided-power structure `x^{[m]} = x^m / m!` supplying the pairing.

## Implementation notes

**`Nontrivial R` is a hypothesis only for convenience.** It is implied by `CharP R p` with `p`
prime, but carrying it explicitly avoids threading a derivation through the `PowerBasis`
dimension `natDegree (X^p) = p`, which is where it is actually used.

**Faithfulness of the pairing is reduced to the basis** by `AlphaP.pairMap_basis_ext`.
`CartierDual.pairMap_injective` quantifies over all of `A × A`; since `pairMap a b z` is linear
in `a` and in `b` (`pairMap_add_left` and friends), checking on monomials suffices. That
reduction is four short inductions plus two `Finset` sums, and it is what lets `comul_y` be a
finite computation.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 11.
* Demazure–Gabriel, *Groupes algébriques*, II §7.
-/

@[expose] public section

open TensorProduct Coalgebra Polynomial CartierDual

universe u

namespace AlphaP

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p] [Nontrivial R]

omit [Nontrivial R] in
/-- The binomial expansion of the comultiplication on the monomial basis:
`Δ (x^n) = ∑_k x^k ⊗ C(n,k) x^{n-k}`. -/
lemma comul_x_pow (n : ℕ) :
    comul (R := R) ((x : AlphaP R p) ^ n)
      = ∑ k ∈ Finset.range (n + 1),
          ((x : AlphaP R p) ^ k) ⊗ₜ[R] ((n.choose k : R) • (x : AlphaP R p) ^ (n - k)) := by
  show (comulAlgHom R p) ((x : AlphaP R p) ^ n) = _
  rw [map_pow, comulAlgHom_x, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    show ((n.choose k : ℕ) : AlphaP R p ⊗[R] AlphaP R p)
      = algebraMap R _ ((n.choose k : ℕ) : R) from (map_natCast (algebraMap R _) _).symm,
    mul_comm, ← Algebra.smul_def, ← TensorProduct.tmul_smul]

/-- A Sweedler representation of `x^n`, read off from the binomial expansion. -/
noncomputable def reprXPow (n : ℕ) : Coalgebra.Repr R ((x : AlphaP R p) ^ n) ℕ where
  index := Finset.range (n + 1)
  left k := (x : AlphaP R p) ^ k
  right k := (n.choose k : R) • (x : AlphaP R p) ^ (n - k)
  eq := (comul_x_pow n).symm

variable (R p)

/-- The monomial power basis `1, x, …, x^{p-1}` of `O(α_p)`. -/
noncomputable def pb : PowerBasis R (AlphaP R p) :=
  AdjoinRoot.powerBasis' (monic_X_pow p)

omit [Fact p.Prime] [CharP R p] in
@[simp] lemma pb_dim : (pb R p).dim = p := natDegree_X_pow p

omit [Fact p.Prime] [CharP R p] [Nontrivial R] in
@[simp] lemma pb_basis_apply (i : Fin (pb R p).dim) :
    (pb R p).basis i = (x : AlphaP R p) ^ (i : ℕ) :=
  (pb R p).basis_eq_pow i

/-- The index `1`, as an element of the basis index type. -/
def oneIdx : Fin (pb R p).dim :=
  ⟨1, by rw [pb_dim]; exact (Fact.out : p.Prime).one_lt⟩

/-- The generator of the Cartier dual of `α_p`: the functional dual to `x` in the monomial
basis. Under the self-duality this is the coordinate of the dual copy of `α_p`. -/
noncomputable def y : CartierDual R (AlphaP R p) :=
  (toDual R (AlphaP R p)).symm ((pb R p).basis.coord (oneIdx R p))

variable {R p}

omit [Fact p.Prime] [CharP R p] [Nontrivial R] in
lemma coord_x_pow (i : Fin (pb R p).dim) (n : ℕ) (hn : n < (pb R p).dim) :
    (pb R p).basis.coord i ((x : AlphaP R p) ^ n) = if (i : ℕ) = n then 1 else 0 := by
  rw [show (x : AlphaP R p) ^ n = (pb R p).basis ⟨n, hn⟩ from (pb_basis_apply R p ⟨n, hn⟩).symm,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [Fin.ext_iff, eq_comm]

omit [CharP R p] in
lemma y_apply (a : AlphaP R p) : (y R p) a = (pb R p).basis.coord (oneIdx R p) a := by
  show (toDual R (AlphaP R p)) (y R p) a = _
  rw [y, LinearEquiv.apply_symm_apply]

omit [CharP R p] in
@[simp] lemma y_apply_x_pow (n : ℕ) (hn : n < p) :
    (y R p) ((x : AlphaP R p) ^ n) = if n = 1 then 1 else 0 := by
  rw [y_apply, coord_x_pow (oneIdx R p) n (by rw [pb_dim]; exact hn)]
  simp [oneIdx, eq_comm]

omit [Fact p.Prime] [CharP R p] in
/-- A functional on `O(α_p)` is determined by its values on the monomials. -/
lemma dual_ext {f g : CartierDual R (AlphaP R p)}
    (h : ∀ n, n < p → f ((x : AlphaP R p) ^ n) = g ((x : AlphaP R p) ^ n)) : f = g := by
  refine (toDual R (AlphaP R p)).injective (Module.Basis.ext (pb R p).basis fun i => ?_)
  rw [pb_basis_apply]
  exact h i (by simpa using i.2)

/-- The convolution powers of `y` are the divided powers: `y^m` is `m!` times the functional
dual to `x^m`. -/
lemma y_pow_apply (m n : ℕ) (hn : n < p) :
    ((y R p) ^ m) ((x : AlphaP R p) ^ n) = if n = m then (m.factorial : R) else 0 := by
  induction m generalizing n with
  | zero =>
      rw [pow_zero, one_apply]
      show (counitAlgHom R p) ((x : AlphaP R p) ^ n) = _
      rw [map_pow, counitAlgHom_x]
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · rw [zero_pow hpos.ne', if_neg hpos.ne']
  | succ m ih =>
      rw [pow_succ, mul_apply_repr (reprXPow n)]
      show (∑ k ∈ Finset.range (n + 1), ((y R p) ^ m) ((x : AlphaP R p) ^ k) *
        (y R p) ((n.choose k : R) • (x : AlphaP R p) ^ (n - k))) = _
      have hval : ∀ k ∈ Finset.range (n + 1),
          ((y R p) ^ m) ((x : AlphaP R p) ^ k) *
              (y R p) ((n.choose k : R) • (x : AlphaP R p) ^ (n - k))
            = (if k = m then (m.factorial : R) else 0) *
              ((n.choose k : R) * (if n - k = 1 then 1 else 0)) := by
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ih k (lt_of_le_of_lt hkn hn),
          show (y R p) ((n.choose k : R) • (x : AlphaP R p) ^ (n - k))
            = (n.choose k : R) * (y R p) ((x : AlphaP R p) ^ (n - k)) from
              map_smul (toDual R (AlphaP R p) (y R p)) _ _,
          y_apply_x_pow (n - k) (lt_of_le_of_lt (Nat.sub_le n k) hn)]
      rw [Finset.sum_congr rfl hval, Finset.sum_eq_single m]
      · rw [if_pos rfl]
        by_cases hnm : n = m + 1
        · subst hnm
          rw [if_pos rfl, Nat.add_sub_cancel_left, if_pos rfl, mul_one,
            Nat.choose_succ_self_right, Nat.factorial_succ]
          push_cast
          ring
        · rw [if_neg hnm, if_neg (fun hc => hnm (by omega)), mul_zero, mul_zero]
      · intro k _ hk
        rw [if_neg hk, zero_mul]
      · intro hcon
        have hmn : n < m := by
          by_contra hc
          exact hcon (Finset.mem_range.mpr (by omega))
        rw [if_pos rfl, if_neg (by omega : ¬(n - m = 1)), mul_zero, mul_zero]

lemma y_pow_p : (y R p) ^ p = 0 :=
  dual_ext fun n hn => by rw [y_pow_apply p n hn, if_neg hn.ne, CartierDual.zero_apply]

/-! ## `α_p` is self-dual -/

omit [Nontrivial R] in
/-- A natural number prime to `p` is a unit in any `R` of characteristic `p`: Bézout in `ℤ`,
pushed into `R`, where the `p`-term dies. -/
lemma isUnit_natCast_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : IsUnit ((n : R)) := by
  have hcop : Nat.gcd p n = 1 := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [hcop] at hb
  have hR := congrArg (fun z : ℤ => (z : R)) hb
  push_cast at hR
  rw [show ((p : ℕ) : R) = 0 from CharP.cast_eq_zero R p, zero_mul, zero_add] at hR
  exact isUnit_iff_exists_inv.mpr ⟨((Nat.gcdB p n : ℤ) : R), hR.symm⟩

omit [Nontrivial R] in
lemma isUnit_factorial {m : ℕ} (hm : m < p) : IsUnit ((m.factorial : R)) :=
  isUnit_natCast_of_not_dvd (fun hdvd =>
    absurd ((Nat.Prime.dvd_factorial Fact.out).mp hdvd) (by omega))

variable (R p)

/-- The basis of `CartierDual R (AlphaP R p)` dual to the monomial basis. -/
noncomputable def dualBasisEval :
    Module.Basis (Fin (pb R p).dim) R (CartierDual R (AlphaP R p)) :=
  ((pb R p).basis.dualBasis).map (toDual R (AlphaP R p)).symm

variable {R p}

omit [Fact p.Prime] [CharP R p] in
lemma dualBasisEval_apply_x_pow (m : Fin (pb R p).dim) (n : ℕ) (hn : n < p) :
    (dualBasisEval R p m) ((x : AlphaP R p) ^ n) = if (m : ℕ) = n then 1 else 0 := by
  show (toDual R (AlphaP R p)) (dualBasisEval R p m) ((x : AlphaP R p) ^ n) = _
  rw [dualBasisEval, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.dualBasis_apply, ← Module.Basis.coord_apply,
    coord_x_pow m n (by rw [pb_dim]; exact hn)]

/-- **The divided-power identity.** `y^m = m! · e_m`, where `e_m` is dual to `x^m`. -/
lemma y_pow_eq_smul (m : Fin (pb R p).dim) :
    (y R p) ^ (m : ℕ) = ((m : ℕ).factorial : R) • dualBasisEval R p m := by
  refine dual_ext fun n hn => ?_
  rw [y_pow_apply (m : ℕ) n hn, CartierDual.smul_apply,
    dualBasisEval_apply_x_pow m n hn]
  by_cases h : n = (m : ℕ)
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), mul_zero]

variable (R p)

/-- The convolution powers `y^m`, `m < p`, form a basis of the Cartier dual: each is a UNIT
multiple of a dual basis vector, because `m!` is prime to `p`. -/
noncomputable def dualBasisY :
    Module.Basis (Fin (pb R p).dim) R (CartierDual R (AlphaP R p)) :=
  (dualBasisEval R p).isUnitSMul (w := fun m => ((m : ℕ).factorial : R))
    (fun m => isUnit_factorial (by simpa using m.2))

variable {R p}

lemma dualBasisY_apply (m : Fin (pb R p).dim) : dualBasisY R p m = (y R p) ^ (m : ℕ) := by
  rw [dualBasisY, Module.Basis.isUnitSMul_apply, y_pow_eq_smul]

variable (R p)

/-- The comparison map `O(α_p) → O(α_p)^D`, sending the coordinate `x` to its dual `y`. -/
noncomputable def toDualAlgHom : AlphaP R p →ₐ[R] CartierDual R (AlphaP R p) :=
  lift R p (y R p) y_pow_p

variable {R p}

@[simp] lemma toDualAlgHom_x_pow (n : ℕ) :
    toDualAlgHom R p ((x : AlphaP R p) ^ n) = (y R p) ^ n := by
  rw [map_pow, toDualAlgHom, lift_x]

lemma toDualAlgHom_bijective : Function.Bijective (toDualAlgHom R p) := by
  have hEq : (toDualAlgHom R p).toLinearMap
      = ((pb R p).basis.equiv (dualBasisY R p) (Equiv.refl _)).toLinearMap := by
    refine Module.Basis.ext (pb R p).basis fun i => ?_
    show toDualAlgHom R p ((pb R p).basis i)
      = (pb R p).basis.equiv (dualBasisY R p) (Equiv.refl _) ((pb R p).basis i)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply, dualBasisY_apply, pb_basis_apply,
      toDualAlgHom_x_pow]
  have hb := ((pb R p).basis.equiv (dualBasisY R p) (Equiv.refl _)).bijective
  have hfun : ⇑(toDualAlgHom R p)
      = ⇑((pb R p).basis.equiv (dualBasisY R p) (Equiv.refl _)) :=
    funext fun a => congrArg (fun L : AlphaP R p →ₗ[R] CartierDual R (AlphaP R p) => L a) hEq
  rw [hfun]
  exact hb

/-- `α_p^D ≅ α_p` as ALGEBRAS. -/
noncomputable def selfDualAlgEquiv : AlphaP R p ≃ₐ[R] CartierDual R (AlphaP R p) :=
  AlgEquiv.ofBijective (toDualAlgHom R p) toDualAlgHom_bijective

/-! ### The pairing, on the monomial basis -/

omit [Nontrivial R] in
lemma pairMap_add_left (a₁ a₂ b : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap (a₁ + a₂) b z = pairMap a₁ b z + pairMap a₂ b z := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, pairMap_tmul, pairMap_tmul,
        show (u : CartierDual R (AlphaP R p)) (a₁ + a₂) = u a₁ + u a₂ from
          map_add (toDual R (AlphaP R p) u) _ _, add_mul]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]; ring

omit [Nontrivial R] in
lemma pairMap_smul_left (r : R) (a b : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap (r • a) b z = r * pairMap a b z := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, pairMap_tmul,
        show (u : CartierDual R (AlphaP R p)) (r • a) = r * u a from by
          rw [show (u : CartierDual R (AlphaP R p)) (r • a)
            = (toDual R (AlphaP R p) u) (r • a) from rfl, map_smul, smul_eq_mul]; rfl,
        mul_assoc]
  | add u v hu hv => rw [map_add, map_add, hu, hv]; ring

omit [Nontrivial R] in
lemma pairMap_add_right (a b₁ b₂ : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap a (b₁ + b₂) z = pairMap a b₁ z + pairMap a b₂ z := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, pairMap_tmul, pairMap_tmul,
        show (v : CartierDual R (AlphaP R p)) (b₁ + b₂) = v b₁ + v b₂ from
          map_add (toDual R (AlphaP R p) v) _ _, mul_add]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]; ring

omit [Nontrivial R] in
lemma pairMap_smul_right (r : R) (a b : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap a (r • b) z = r * pairMap a b z := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, pairMap_tmul,
        show (v : CartierDual R (AlphaP R p)) (r • b) = r * v b from by
          rw [show (v : CartierDual R (AlphaP R p)) (r • b)
            = (toDual R (AlphaP R p) v) (r • b) from rfl, map_smul, smul_eq_mul]; rfl]
      ring
  | add u v hu hv => rw [map_add, map_add, hu, hv]; ring

omit [Nontrivial R] in
lemma pairMap_zero_left (b : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap (0 : AlphaP R p) b z = 0 := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, show (u : CartierDual R (AlphaP R p)) 0 = 0 from
        map_zero (toDual R (AlphaP R p) u), zero_mul]
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

omit [Nontrivial R] in
lemma pairMap_zero_right (a : AlphaP R p)
    (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap a (0 : AlphaP R p) z = 0 := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [pairMap_tmul, show (v : CartierDual R (AlphaP R p)) 0 = 0 from
        map_zero (toDual R (AlphaP R p) v), mul_zero]
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

omit [Nontrivial R] in
lemma pairMap_sum_left {ι : Type*} (s : Finset ι) (c : ι → R) (v : ι → AlphaP R p)
    (b : AlphaP R p) (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap (∑ i ∈ s, c i • v i) b z = ∑ i ∈ s, c i * pairMap (v i) b z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pairMap_zero_left b z
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, pairMap_add_left, pairMap_smul_left, ih, Finset.sum_insert hi]

omit [Nontrivial R] in
lemma pairMap_sum_right {ι : Type*} (s : Finset ι) (c : ι → R) (v : ι → AlphaP R p)
    (a : AlphaP R p) (z : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) :
    pairMap a (∑ i ∈ s, c i • v i) z = ∑ i ∈ s, c i * pairMap a (v i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pairMap_zero_right a z
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, pairMap_add_right, pairMap_smul_right, ih, Finset.sum_insert hi]

/-- Faithfulness of the pairing, reduced to the monomial basis. -/
lemma pairMap_basis_ext {z w : CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)}
    (h : ∀ m n : ℕ, m < p → n < p →
      pairMap ((x : AlphaP R p) ^ m) ((x : AlphaP R p) ^ n) z
        = pairMap ((x : AlphaP R p) ^ m) ((x : AlphaP R p) ^ n) w) : z = w := by
  refine pairMap_injective fun a b => ?_
  have key : ∀ (m : ℕ), m < p → ∀ c : AlphaP R p,
      pairMap ((x : AlphaP R p) ^ m) c z = pairMap ((x : AlphaP R p) ^ m) c w := by
    intro m hm c
    rw [← (pb R p).basis.sum_equivFun c, pairMap_sum_right, pairMap_sum_right]
    exact Finset.sum_congr rfl fun i _ => by
      rw [pb_basis_apply, h m i hm (by simpa using i.2)]
  rw [← (pb R p).basis.sum_equivFun a, pairMap_sum_left, pairMap_sum_left]
  exact Finset.sum_congr rfl fun i _ => by
    rw [pb_basis_apply, key i (by simpa using i.2) b]

lemma counit_y : counit (R := R) (y R p) = 0 := by
  rw [CartierDual.counit_apply, show (1 : AlphaP R p) = (x : AlphaP R p) ^ 0 from (pow_zero _).symm,
    y_apply_x_pow 0 (Fact.out : p.Prime).pos]
  simp

omit [Nontrivial R] in
lemma counit_x_pow (n : ℕ) :
    counit (R := R) ((x : AlphaP R p) ^ n) = if n = 0 then (1 : R) else 0 := by
  show (counitAlgHom R p) ((x : AlphaP R p) ^ n) = _
  rw [map_pow, counitAlgHom_x]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · rw [zero_pow hpos.ne', if_neg hpos.ne']

omit [CharP R p] in
lemma y_apply_x_pow' (n : ℕ) :
    (y R p) ((x : AlphaP R p) ^ n) = if n = 1 then (1 : R) else 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_cases hn : n < p
  · exact y_apply_x_pow n hn
  · rw [show (x : AlphaP R p) ^ n = 0 from by
      rw [show n = p + (n - p) from by omega, pow_add, x_pow, zero_mul],
    show (y R p) (0 : AlphaP R p) = 0 from map_zero (toDual R (AlphaP R p) (y R p)),
    if_neg (by omega)]

/-- `y` is primitive: `Δ y = y ⊗ 1 + 1 ⊗ y`. This is the transpose of `x^a · x^b = x^{a+b}`,
and it is what makes the self-duality a map of COALGEBRAS. -/
lemma comul_y : comul (R := R) (y R p) = (y R p) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] (y R p) := by
  have hkey : ∀ a b : ℕ, (if a + b = 1 then (1 : R) else 0)
      = (if a = 1 then (1 : R) else 0) * (if b = 0 then (1 : R) else 0)
        + (if a = 0 then (1 : R) else 0) * (if b = 1 then (1 : R) else 0) := by
    intro a b
    by_cases ha : a = 0
    · subst ha; simp
    by_cases ha1 : a = 1
    · subst ha1
      by_cases hb : b = 0
      · subst hb; simp
      · rw [if_neg (by omega : ¬(1 + b = 1)), if_pos rfl, if_neg hb,
          if_neg (by omega : ¬(1 = 0))]
        ring
    · rw [if_neg (by omega : ¬(a + b = 1)), if_neg ha1, if_neg ha]
      ring
  refine pairMap_basis_ext fun m n _ _ => ?_
  rw [pairMap_comul, ← pow_add, map_add, pairMap_tmul, pairMap_tmul, CartierDual.one_apply,
    CartierDual.one_apply, y_apply_x_pow' (m + n), y_apply_x_pow' m, y_apply_x_pow' n,
    counit_x_pow, counit_x_pow]
  exact hkey m n

/-- The comparison map intertwines the comultiplications: an equality of ALGEBRA homs, so it
is enough to check it at `x`, where it is exactly `Δ y = y ⊗ 1 + 1 ⊗ y`. -/
lemma map_comp_comul_toDualAlgHom :
    (((Algebra.TensorProduct.map (toDualAlgHom R p) (toDualAlgHom R p) :
        AlphaP R p ⊗[R] AlphaP R p →ₐ[R]
          CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p))).comp (comulAlgHom R p) :
      AlphaP R p →ₐ[R] CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p))
      = (Bialgebra.comulAlgHom R (CartierDual R (AlphaP R p))).comp (toDualAlgHom R p) := by
  refine AlphaP.algHom_ext
    (S := CartierDual R (AlphaP R p) ⊗[R] CartierDual R (AlphaP R p)) ?_
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comulAlgHom_x,
    show toDualAlgHom R p (x : AlphaP R p) = y R p from lift_x _ _, comul_y,
    map_add, Algebra.TensorProduct.map_tmul, map_one]

/-- **`α_p^D ≅ α_p`.** The Cartier dual of the Frobenius kernel of `𝔾_a` is itself. The
divided-power basis `e_m` of the dual satisfies `y^m = m! · e_m` for `y := e_1`, and `m!` is a
unit for `m < p`, so `{y^m}` is again a basis and `y^p = 0`; `AlphaP.lift` therefore sends `x`
to `y` isomorphically, and `Δ y = y ⊗ 1 + 1 ⊗ y` makes it a map of Hopf algebras. -/
noncomputable def selfDualBialgEquiv : AlphaP R p ≃ₐc[R] CartierDual R (AlphaP R p) where
  __ := selfDualAlgEquiv (R := R) (p := p)
  map_smul' := map_smul (toDualAlgHom R p).toLinearMap
  counit_comp :=
    algHomLinearMap_congr
      (Φ := (Bialgebra.counitAlgHom R (CartierDual R (AlphaP R p))).comp (toDualAlgHom R p))
      (Ψ := counitAlgHom R p)
      (by
        show counit (R := R) (toDualAlgHom R p (x : AlphaP R p)) = counitAlgHom R p (x : AlphaP R p)
        rw [show toDualAlgHom R p (x : AlphaP R p) = y R p from lift_x _ _, counit_y,
          counitAlgHom_x])
  map_comp_comul := congrArg AlgHom.toLinearMap map_comp_comul_toDualAlgHom

end AlphaP
