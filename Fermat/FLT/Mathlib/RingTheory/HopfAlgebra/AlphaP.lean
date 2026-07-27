/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDual
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.Nat.Choose.Dvd

/-!
# `α_p`: the Frobenius kernel of the additive group, as a Hopf algebra

`α_p` is the finite flat commutative group scheme `ker(F : 𝔾_a → 𝔾_a)` over a base of
characteristic `p`. On coordinate rings it is `R[x]/(x^p)` with the **additive**
comultiplication `Δ x = x ⊗ 1 + 1 ⊗ x`, counit `ε x = 0` and antipode `S x = -x`. It is the
standard example of a finite flat group scheme that is neither étale nor diagonalizable, and
(together with `μ_p` and `ℤ/p`) one of the three order-`p` group schemes over a field of
characteristic `p`.

**Nothing in the mathlib pin provides this.** Mathlib's only Hopf structures on
polynomial-shaped algebras come from `(Add)MonoidAlgebra`, whose comultiplication is
GROUPLIKE — so `AddMonoidAlgebra R ℕ = R[X]` receives `Δ X = X ⊗ X`, which is `𝔾_m`-shaped,
not `𝔾_a`. Nor is it in `~/cs/FLT`. Hence this file.

## Main definitions

* `AlphaP R p` — the coordinate ring `R[x]/(x^p)`, realised as `AdjoinRoot (X^p)`, with
  `CommRing`, `Algebra R`, `Module.Free`, `Module.Finite`, `Coalgebra`, `Bialgebra`,
  `HopfAlgebra R` and `Coalgebra.IsCocomm R` instances.
* `AlphaP.x` — the coordinate, with `AlphaP.x_pow : x ^ p = 0`.
* `AlphaP.lift` — the universal property: an `R`-algebra hom out of `O(α_p)` *is* a choice of
  `p`-nilpotent element. `AlphaP.algHom_ext` is the matching extensionality principle.
* `AlphaP.comulAlgHom`, `counitAlgHom`, `antipodeAlgHom` — the structure maps as ALGEBRA homs.

## Implementation notes

**Why `AdjoinRoot (X^p)` and not a quotient of a Hopf algebra `R[X]`.** The textbook route is
to build `O(𝔾_a) = R[X]` first and then quotient by the Hopf ideal `(X^p)`. That needs a Hopf
structure on the whole polynomial ring, which does not exist in the pin either. Going directly
to `AdjoinRoot (X^p)` avoids it entirely: `AdjoinRoot.liftAlgHom` gives each structure map from
a single nilpotency check, `AdjoinRoot.algHom_ext` gives extensionality, and
`Polynomial.Monic.free_adjoinRoot` / `finite_adjoinRoot` give freeness and finiteness from
`monic_X_pow`. `𝔾_a` is then never needed.

**Every axiom is checked at `x` only.** All six structure identities (coassociativity, the two
counitalities, the two antipode axioms, cocommutativity) are equalities of maps that happen to
be ALGEBRA homs on both sides — `LinearMap.rTensor`/`lTensor` of an algebra hom is
`Algebra.TensorProduct.map`, the associator is `Algebra.TensorProduct.assoc`, and `mul'` is
`Algebra.TensorProduct.lmul'` because `AlphaP R p` is commutative. All three of those bridges
are DEFINITIONAL at this pin (checked), so `algHomLinearMap_congr` reduces each axiom to a
one-line computation on `x`. That is why this file is short.

**`add_pow_eq_zero` rather than `add_pow_char`.** `Δ x = x ⊗ 1 + 1 ⊗ x` must be `p`-nilpotent
in `AlphaP R p ⊗[R] AlphaP R p`, which is the freshman's dream there. Using mathlib's
`add_pow_char` would need a `CharP` (or `ExpChar`) instance on the tensor square, and getting
one means proving `algebraMap R (A ⊗ A)` injective. It is cheaper and more robust to expand
`add_pow` directly and kill the middle terms with `Nat.Prime.dvd_choose_self`: divisibility by
`p` makes each binomial coefficient vanish in any `R`-algebra, since it factors through
`(· : R)` and `CharP R p`.

## Cartier self-duality

`α_p^D ≅ α_p` is PROVEN, in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaPSelfDual.lean`, as
`AlphaP.selfDualBialgEquiv : AlphaP R p ≃ₐc[R] CartierDual R (AlphaP R p)`. The content is the
divided-power pairing: writing `e_m` for the basis of the dual dual to `x^m`, the binomial
expansion `Δ (x^n) = ∑_k x^k ⊗ C(n,k) x^{n-k}` gives `y^m = m! · e_m` for `y := e_1`; `m!` is a
unit for `m < p`, so `{y^m}` is again a basis and `y^p = 0`; and `y` is primitive. See that
file's module docstring for the full argument.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 11 (`α_p` and `μ_p`).
* Demazure–Gabriel, *Groupes algébriques*, II §7.
-/

@[expose] public section

open TensorProduct Coalgebra Polynomial

universe u

variable (R : Type u) [CommRing R] (p : ℕ)

/-- The coordinate ring of the group scheme `α_p` in characteristic `p`:
`R[x]/(x^p)`, with the ADDITIVE comultiplication `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def AlphaP : Type u := AdjoinRoot (X ^ p : R[X])

namespace AlphaP

noncomputable instance : CommRing (AlphaP R p) := inferInstanceAs (CommRing (AdjoinRoot _))
noncomputable instance : Algebra R (AlphaP R p) := inferInstanceAs (Algebra R (AdjoinRoot _))
noncomputable instance (priority := 2000) : Module R (AlphaP R p) := Algebra.toModule

instance : Module.Free R (AlphaP R p) :=
  (monic_X_pow p).free_adjoinRoot
instance : Module.Finite R (AlphaP R p) :=
  (monic_X_pow p).finite_adjoinRoot

variable {R p}

/-- The coordinate `x`, the image of `X`. -/
noncomputable def x : AlphaP R p := AdjoinRoot.root _

@[simp] lemma x_pow : (x : AlphaP R p) ^ p = 0 := by
  show AdjoinRoot.root _ ^ p = 0
  have h := AdjoinRoot.aeval_eq (f := (X ^ p : R[X])) (X ^ p)
  rw [AdjoinRoot.mk_self, map_pow, Polynomial.aeval_X] at h
  exact h

@[ext] lemma algHom_ext {S : Type*} [CommRing S] [Algebra R S] {φ ψ : AlphaP R p →ₐ[R] S}
    (h : φ x = ψ x) : φ = ψ :=
  AdjoinRoot.algHom_ext h

variable (R p) in
/-- The universal property: an `R`-algebra hom out of `O(α_p)` is a choice of a `p`-nilpotent
element. -/
noncomputable def lift {S : Type*} [CommRing S] [Algebra R S] (t : S) (h : t ^ p = 0) :
    AlphaP R p →ₐ[R] S :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) t (by simpa using h)

@[simp] lemma lift_x {S : Type*} [CommRing S] [Algebra R S] (t : S) (h : t ^ p = 0) :
    lift R p t h x = t :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

section CharP

variable [Fact p.Prime] [CharP R p]

/-- In an `R`-algebra with `R` of characteristic `p`, a sum of two `p`-nilpotents is
`p`-nilpotent: the freshman's dream, proved from `p ∣ C(p,k)` rather than from a `CharP`
instance on the algebra (which would need injectivity of its structure map). -/
lemma add_pow_eq_zero {S : Type*} [CommRing S] [Algebra R S] {a b : S}
    (ha : a ^ p = 0) (hb : b ^ p = 0) : (a + b) ^ p = 0 := by
  have hcast : ∀ n : ℕ, p ∣ n → (n : S) = 0 := fun n hn => by
    rw [← map_natCast (algebraMap R S) n, (CharP.cast_eq_zero_iff R p n).mpr hn, map_zero]
  rw [add_pow]
  refine Finset.sum_eq_zero fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, one_mul, Nat.sub_zero, hb, zero_mul]
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) with rfl | hkp
  · rw [ha, zero_mul, zero_mul]
  · rw [hcast _ (Nat.Prime.dvd_choose_self Fact.out hk0.ne' hkp), mul_zero]

lemma tensor_x_add_pow :
    ((x : AlphaP R p) ⊗ₜ[R] (1 : AlphaP R p) + (1 : AlphaP R p) ⊗ₜ[R] (x : AlphaP R p)) ^ p
      = 0 := by
  refine add_pow_eq_zero (R := R) ?_ ?_
  · rw [Algebra.TensorProduct.tmul_pow, x_pow, TensorProduct.zero_tmul]
  · rw [Algebra.TensorProduct.tmul_pow, x_pow, TensorProduct.tmul_zero]

omit [Fact p.Prime] [CharP R p] in
lemma neg_x_pow : (-(x : AlphaP R p)) ^ p = 0 := by
  rw [neg_pow, x_pow, mul_zero]

variable (R p)

/-- The comultiplication of `α_p`: `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
noncomputable def comulAlgHom : AlphaP R p →ₐ[R] AlphaP R p ⊗[R] AlphaP R p :=
  lift R p (x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x) tensor_x_add_pow

/-- The counit of `α_p`: evaluation at `0`. -/
noncomputable def counitAlgHom : AlphaP R p →ₐ[R] R :=
  lift R p 0 (zero_pow (Nat.Prime.ne_zero Fact.out))

/-- The antipode of `α_p`: `x ↦ -x`. -/
noncomputable def antipodeAlgHom : AlphaP R p →ₐ[R] AlphaP R p :=
  lift R p (-x) neg_x_pow

@[simp] lemma comulAlgHom_x :
    comulAlgHom R p (x : AlphaP R p) = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x := lift_x _ _

omit [CharP R p] in
@[simp] lemma counitAlgHom_x : counitAlgHom R p (x : AlphaP R p) = 0 := lift_x _ _

omit [Fact p.Prime] [CharP R p] in
@[simp] lemma antipodeAlgHom_x : antipodeAlgHom R p (x : AlphaP R p) = -x := lift_x _ _

noncomputable instance : CoalgebraStruct R (AlphaP R p) where
  comul := (comulAlgHom R p).toLinearMap
  counit := (counitAlgHom R p).toLinearMap

lemma comul_x : comul (R := R) (x : AlphaP R p) = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x := comulAlgHom_x R p

lemma counit_x : counit (R := R) (x : AlphaP R p) = 0 := counitAlgHom_x R p


section Axioms

variable {R p}

omit [Fact p.Prime] [CharP R p] in
/-- Two algebra homs out of `O(α_p)` that agree at `x` induce the same linear map. -/
lemma algHomLinearMap_congr {S : Type*} [CommRing S] [Algebra R S]
    {Φ Ψ : AlphaP R p →ₐ[R] S} (h : Φ x = Ψ x) : Φ.toLinearMap = Ψ.toLinearMap :=
  congrArg AlgHom.toLinearMap (AlphaP.algHom_ext h)

noncomputable instance : Coalgebra R (AlphaP R p) where
  coassoc :=
    algHomLinearMap_congr (Φ := (Algebra.TensorProduct.assoc (R := R) (S := R) (T := R)
        (A := AlphaP R p) (AlphaP R p) (AlphaP R p)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlgHom R p) (AlgHom.id R (AlphaP R p))).comp
          (comulAlgHom R p)))
      (Ψ := (Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p)) (comulAlgHom R p)).comp
          (comulAlgHom R p))
      (by
        show (Algebra.TensorProduct.assoc (R := R) (S := R) (T := R) (A := AlphaP R p)
            (AlphaP R p) (AlphaP R p))
            (Algebra.TensorProduct.map (comulAlgHom R p) (AlgHom.id R (AlphaP R p))
              (comulAlgHom R p x))
          = Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p)) (comulAlgHom R p)
              (comulAlgHom R p x)
        rw [comulAlgHom_x]
        simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
          comulAlgHom_x, Algebra.TensorProduct.one_def, TensorProduct.add_tmul,
          TensorProduct.tmul_add]
        abel)
  rTensor_counit_comp_comul :=
    algHomLinearMap_congr (S := R ⊗[R] AlphaP R p)
      (Φ := (Algebra.TensorProduct.map (counitAlgHom R p)
        (AlgHom.id R (AlphaP R p))).comp (comulAlgHom R p))
      (Ψ := (Algebra.TensorProduct.includeRight : AlphaP R p →ₐ[R] R ⊗[R] AlphaP R p))
      (by
        show Algebra.TensorProduct.map (counitAlgHom R p) (AlgHom.id R (AlphaP R p))
            (comulAlgHom R p x) = _
        rw [comulAlgHom_x]
        simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          counitAlgHom_x, map_one, TensorProduct.zero_tmul, zero_add]
        rfl)
  lTensor_counit_comp_comul :=
    algHomLinearMap_congr (S := AlphaP R p ⊗[R] R)
      (Φ := (Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p))
        (counitAlgHom R p)).comp (comulAlgHom R p))
      (Ψ := (Algebra.TensorProduct.includeLeft : AlphaP R p →ₐ[R] AlphaP R p ⊗[R] R))
      (by
        show Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p)) (counitAlgHom R p)
            (comulAlgHom R p x) = _
        rw [comulAlgHom_x]
        simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          counitAlgHom_x, map_one, TensorProduct.tmul_zero, add_zero]
        rfl)

noncomputable instance : Bialgebra R (AlphaP R p) :=
  Bialgebra.mk' R _ (map_one (counitAlgHom R p)) (fun {a b} => map_mul (counitAlgHom R p) a b)
    (map_one (comulAlgHom R p)) (fun {a b} => map_mul (comulAlgHom R p) a b)

noncomputable instance : HopfAlgebraStruct R (AlphaP R p) where
  antipode := (antipodeAlgHom R p).toLinearMap

noncomputable instance : HopfAlgebra R (AlphaP R p) where
  mul_antipode_rTensor_comul :=
    algHomLinearMap_congr (Φ := (Algebra.TensorProduct.lmul' (S := AlphaP R p) R).comp
        ((Algebra.TensorProduct.map (antipodeAlgHom R p) (AlgHom.id R (AlphaP R p))).comp
          (comulAlgHom R p)))
      (Ψ := (Algebra.ofId R (AlphaP R p)).comp (counitAlgHom R p))
      (by
        show Algebra.TensorProduct.lmul' (S := AlphaP R p) R
            (Algebra.TensorProduct.map (antipodeAlgHom R p) (AlgHom.id R (AlphaP R p))
              (comulAlgHom R p x)) = _
        rw [comulAlgHom_x]
        simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          antipodeAlgHom_x, map_one, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul,
          neg_add_cancel]
        show (0 : AlphaP R p) = (Algebra.ofId R (AlphaP R p)) (counitAlgHom R p x)
        rw [counitAlgHom_x, map_zero])
  mul_antipode_lTensor_comul :=
    algHomLinearMap_congr (Φ := (Algebra.TensorProduct.lmul' (S := AlphaP R p) R).comp
        ((Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p)) (antipodeAlgHom R p)).comp
          (comulAlgHom R p)))
      (Ψ := (Algebra.ofId R (AlphaP R p)).comp (counitAlgHom R p))
      (by
        show Algebra.TensorProduct.lmul' (S := AlphaP R p) R
            (Algebra.TensorProduct.map (AlgHom.id R (AlphaP R p)) (antipodeAlgHom R p)
              (comulAlgHom R p x)) = _
        rw [comulAlgHom_x]
        simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          antipodeAlgHom_x, map_one, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, one_mul,
          add_neg_cancel]
        show (0 : AlphaP R p) = (Algebra.ofId R (AlphaP R p)) (counitAlgHom R p x)
        rw [counitAlgHom_x, map_zero])

noncomputable instance : IsCocomm R (AlphaP R p) where
  comm_comp_comul :=
    algHomLinearMap_congr (Φ := (Algebra.TensorProduct.comm R (AlphaP R p) (AlphaP R p)).toAlgHom.comp
        (comulAlgHom R p))
      (Ψ := comulAlgHom R p)
      (by
        show (Algebra.TensorProduct.comm R (AlphaP R p) (AlphaP R p)) (comulAlgHom R p x) = _
        rw [comulAlgHom_x, map_add, Algebra.TensorProduct.comm_tmul,
          Algebra.TensorProduct.comm_tmul, add_comm])

end Axioms

end CharP

end AlphaP
