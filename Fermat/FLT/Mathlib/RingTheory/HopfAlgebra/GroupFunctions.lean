/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Deyao Chen
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Bialgebra.Convolution

/-!
# The constant group scheme: the Hopf algebra of functions on a finite group

For a finite group `G` and a commutative ring `R`, `GroupFunctions R G` is the `R`-algebra
`G → R` of `R`-valued functions on `G`, equipped with the Hopf-algebra structure DUAL to the
group law of `G`. `Spec` of it is the CONSTANT group scheme `G_R`.

Mathlib (pin `a3364fa`) does not have this object. It has the group ALGEBRA `R[G]`
(`MonoidAlgebra.instHopfAlgebra`, the diagonalizable group scheme, i.e. the Cartier DUAL of
this one), and it has a coalgebra structure on `Π i, A i` (`Pi.instCoalgebraStruct`) -- but
that one is the COMPONENTWISE structure, not the one dual to the group law, so it is not the
one wanted here. Hence the type synonym.

## Main definitions

* `GroupFunctions R G` : the type synonym, with `CommRing`, `Algebra R`, `Module.Free`,
  `Module.Finite`, `Coalgebra`, `Bialgebra` and `HopfAlgebra R` instances.
* `GroupFunctions.single R g` : the indicator function `e_g`; these form an `R`-basis.
* `GroupFunctions.baseChangeAlgEquiv` : `S ⊗[R] GroupFunctions R G ≃ₐ[S] (G → S)`, the
  generic fibre. Combined with `Algebra.FormallyEtale`'s finite-product instance this is
  what makes the constant group scheme ÉTALE over a base in which it is split.
* `GroupFunctions.pointsMulEquiv` : `G ≃* WithConv (GroupFunctions R G →ₐ[R] L)` for `L` a
  nontrivial `R`-algebra without zero divisors -- the `L`-points of the constant group
  scheme, with their convolution product, ARE `G`.

## Main statements

* `GroupFunctions.comul_single` : `comul (e_g) = Σ_a e_a ⊗ e_{a⁻¹ g}`.
* `GroupFunctions.exists_eq_pointAlgHom` : every `R`-algebra hom `GroupFunctions R G → L`
  into a nontrivial ring without zero divisors is evaluation at a (unique) `g : G`.
* `GroupFunctions.comp_pointAlgHom` : those points are fixed by every `R`-algebra
  endomorphism of `L`. In the arithmetic application (`L = Kᵃˡᵍ`, `R` the base) this is the
  statement that the Galois action on the points of a constant group scheme is trivial.

## Implementation notes

The comultiplication is defined as an ALGEBRA hom -- the pullback of functions along
`G × G → G`, read through `tensorEquiv : (G → R) ⊗ (G → R) ≃ₐ (G × G → R)` -- so that the
bialgebra axioms are true by construction; only the coalgebra axioms need proof, and those
are checked on the basis `e_g` via `GroupFunctions.linearMap_ext`.

The `Module R (GroupFunctions R G)` instance is declared explicitly, at high priority, as
`Algebra.toModule`. Without it, `Module ℤ (GroupFunctions ℤ G)` resolves to
`AddCommGroup.toIntModule`, which is definitionally but not `instances`-transparently equal
to the algebra one (the synonym does not unfold at that transparency), and then
`Algebra.TensorProduct`'s ring instances fail to apply to `S ⊗[ℤ] GroupFunctions ℤ G`.
-/

@[expose] public section

open TensorProduct

universe u w

/-- **The coordinate ring of the CONSTANT group scheme `G_R`**: the `R`-algebra of
`R`-valued functions on `G`, carrying the Hopf structure DUAL to the group law of `G`,

  `comul (e_g) = Σ_{a b = g} e_a ⊗ e_b`,  `counit f = f 1`,  `antipode f = f ∘ (·⁻¹)`.

This is a TYPE SYNONYM for `G → R` and not an abbreviation, deliberately: mathlib's
`Pi.instCoalgebraStruct` puts the COMPONENTWISE coalgebra structure on `G → R`, which is
a different (and, for this purpose, wrong) structure, so the two must not collide. -/
def GroupFunctions (R : Type u) (G : Type w) : Type max u w := G → R

namespace GroupFunctions

variable {R : Type u} {G : Type w} [CommRing R]

instance : CommRing (GroupFunctions R G) := inferInstanceAs (CommRing (G → R))
instance : Algebra R (GroupFunctions R G) := inferInstanceAs (Algebra R (G → R))
-- `Module R (GroupFunctions R G)` must be the one coming from the algebra structure,
-- and at `R = ℤ` it would otherwise be `AddCommGroup.toIntModule`; the two are
-- definitionally equal but not at `instances` transparency (the synonym does not
-- unfold there), which breaks `Algebra.TensorProduct` instance synthesis.
instance (priority := 2000) : Module R (GroupFunctions R G) := Algebra.toModule
instance [Finite G] : Module.Finite R (GroupFunctions R G) :=
  inferInstanceAs (Module.Finite R (G → R))
instance [Finite G] : Module.Free R (GroupFunctions R G) :=
  inferInstanceAs (Module.Free R (G → R))

omit [CommRing R] in
@[ext] lemma ext {f g : GroupFunctions R G} (h : ∀ x, f x = g x) : f = g := funext h

@[simp] lemma add_apply (f g : GroupFunctions R G) (x : G) : (f + g) x = f x + g x := rfl
@[simp] lemma mul_apply (f g : GroupFunctions R G) (x : G) : (f * g) x = f x * g x := rfl
@[simp] lemma one_apply (x : G) : (1 : GroupFunctions R G) x = 1 := rfl
@[simp] lemma zero_apply (x : G) : (0 : GroupFunctions R G) x = 0 := rfl
@[simp] lemma smul_apply (r : R) (f : GroupFunctions R G) (x : G) : (r • f) x = r * f x := rfl
@[simp] lemma algebraMap_apply (r : R) (x : G) :
    algebraMap R (GroupFunctions R G) r x = r := rfl

variable (R) in
/-- The indicator function of `g` -- the dual basis vector `e_g`. -/
def single [DecidableEq G] (g : G) : GroupFunctions R G := Pi.single g (1 : R)

@[simp] lemma single_apply [DecidableEq G] (g x : G) :
    (single R g : GroupFunctions R G) x = if x = g then 1 else 0 := by
  simp [single, Pi.single_apply]

lemma single_mul_single [DecidableEq G] (g h : G) :
    (single R g : GroupFunctions R G) * single R h = if g = h then single R g else 0 := by
  rcases eq_or_ne g h with rfl | hgh
  · rw [if_pos rfl]
    ext x
    simp only [mul_apply, single_apply]
    rcases eq_or_ne x g with rfl | hx
    · simp
    · simp [hx]
  · rw [if_neg hgh]
    ext x
    simp only [mul_apply, single_apply, zero_apply]
    rcases eq_or_ne x g with rfl | hx
    · rw [if_pos rfl, if_neg hgh, mul_zero]
    · rw [if_neg hx, zero_mul]

lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → GroupFunctions R G) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

lemma sum_single [DecidableEq G] [Fintype G] :
    ∑ g : G, (single R g : GroupFunctions R G) = 1 := by
  ext x
  rw [sum_apply]
  simp

lemma sum_smul_single [DecidableEq G] [Fintype G] (f : GroupFunctions R G) :
    ∑ g : G, f g • (single R g : GroupFunctions R G) = f := by
  ext x
  rw [sum_apply]
  simp [mul_ite]

lemma linearMap_ext [DecidableEq G] [Fintype G] {N : Type*} [AddCommMonoid N] [Module R N]
    {φ ψ : GroupFunctions R G →ₗ[R] N} (h : ∀ g, φ (single R g) = ψ (single R g)) : φ = ψ := by
  refine LinearMap.ext fun f => ?_
  rw [← sum_smul_single f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, map_smul, h]

lemma algHom_ext [DecidableEq G] [Fintype G] {N : Type*} [Semiring N] [Algebra R N]
    {φ ψ : GroupFunctions R G →ₐ[R] N} (h : ∀ g, φ (single R g) = ψ (single R g)) : φ = ψ := by
  apply AlgHom.toLinearMap_injective
  exact linearMap_ext h

variable (R G) in
/-- Uncurrying `G → (G → R)` into `G × G → R` (with the two coordinates SWAPPED, to match
the order produced by `Algebra.TensorProduct.piScalarRight`), as an algebra equivalence. -/
def uncurryAlgEquiv : (G → GroupFunctions R G) ≃ₐ[R] (G × G → R) where
  toFun u := fun p => u p.2 p.1
  invFun w := fun a b => w (b, a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (R G) in
/-- `(G → R) ⊗[R] (G → R) ≃ₐ[R] (G × G → R)`, sending `x ⊗ y` to `(a, b) ↦ x a * y b`.
This is `Algebra.TensorProduct.piScalarRight` followed by uncurrying, and it is what makes
the dual-to-the-group-law comultiplication typecheck. -/
noncomputable def tensorEquiv [Fintype G] [DecidableEq G] :
    (GroupFunctions R G) ⊗[R] (GroupFunctions R G) ≃ₐ[R] (G × G → R) :=
  (Algebra.TensorProduct.piScalarRight R R (GroupFunctions R G) G).trans (uncurryAlgEquiv R G)

@[simp] lemma tensorEquiv_tmul [Fintype G] [DecidableEq G]
    (x y : GroupFunctions R G) (p : G × G) :
    tensorEquiv R G (x ⊗ₜ y) p = x p.1 * y p.2 := by
  show (Algebra.TensorProduct.piScalarRight R R (GroupFunctions R G) G (x ⊗ₜ y)) p.2 p.1 = _
  rw [Algebra.TensorProduct.piScalarRight_tmul_apply]
  simp [mul_comm]

variable (R G) in
/-- Pullback of functions along the multiplication map `G × G → G`. -/
def mulPullback [Mul G] : GroupFunctions R G →ₐ[R] (G × G → R) where
  toFun f := fun p => f (p.1 * p.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma mulPullback_apply [Mul G] (f : GroupFunctions R G) (p : G × G) :
    mulPullback R G f p = f (p.1 * p.2) := rfl

variable (R G) in
/-- The comultiplication, as an ALGEBRA hom: the pullback along the group law, read through
`tensorEquiv`. Building it this way makes the bialgebra axioms (`comul` multiplicative and
unital) hold by construction. -/
noncomputable def comulAlgHom [Group G] [Fintype G] [DecidableEq G] :
    GroupFunctions R G →ₐ[R] (GroupFunctions R G) ⊗[R] (GroupFunctions R G) :=
  ((tensorEquiv R G).symm : (G × G → R) ≃ₐ[R] _).toAlgHom.comp (mulPullback R G)

variable (R G) in
/-- The counit, as an algebra hom: evaluation at `1 : G`. -/
def counitAlgHom [One G] : GroupFunctions R G →ₐ[R] R where
  toFun f := f 1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma counitAlgHom_apply [One G] (f : GroupFunctions R G) :
    counitAlgHom R G f = f 1 := rfl

variable (R G) in
/-- The antipode, as an algebra hom: precomposition with inversion in `G`. -/
def antipodeAlgHom [Inv G] : GroupFunctions R G →ₐ[R] GroupFunctions R G where
  toFun f := fun x => f x⁻¹
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma antipodeAlgHom_apply [Inv G] (f : GroupFunctions R G) (x : G) :
    antipodeAlgHom R G f x = f x⁻¹ := rfl

section Coalg

variable [Group G] [Fintype G] [DecidableEq G]

noncomputable instance : CoalgebraStruct R (GroupFunctions R G) where
  comul := (comulAlgHom R G).toLinearMap
  counit := (counitAlgHom R G).toLinearMap

lemma comul_eq (f : GroupFunctions R G) :
    Coalgebra.comul (R := R) f = comulAlgHom R G f := rfl

lemma counit_eq (f : GroupFunctions R G) :
    Coalgebra.counit (R := R) f = f 1 := rfl

lemma comul_single (g : G) :
    Coalgebra.comul (R := R) (single R g : GroupFunctions R G) =
      ∑ a : G, (single R a : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g) := by
  apply (tensorEquiv R G).injective
  rw [map_sum]
  have h : (tensorEquiv R G) (Coalgebra.comul (R := R) (single R g : GroupFunctions R G)) =
      mulPullback R G (single R g) := by
    rw [comul_eq, comulAlgHom]
    show (tensorEquiv R G) ((tensorEquiv R G).symm (mulPullback R G (single R g))) = _
    rw [AlgEquiv.apply_symm_apply]
  rw [h]
  funext p
  obtain ⟨u, v⟩ := p
  rw [mulPullback_apply, single_apply]
  rw [Finset.sum_apply]
  simp only [tensorEquiv_tmul, single_apply]
  rw [Finset.sum_eq_single u]
  · by_cases h1 : u * v = g
    · have h2 : v = u⁻¹ * g := by rw [← h1]; group
      simp [h2]
    · have h2 : ¬ (v = u⁻¹ * g) := fun h2 => h1 (by rw [h2]; group)
      simp [h1, h2]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ u) h

noncomputable instance : Coalgebra R (GroupFunctions R G) where
  coassoc := by
    refine linearMap_ext fun g => ?_
    show (TensorProduct.assoc R _ _ _)
      ((Coalgebra.comul (R := R)).rTensor _ (Coalgebra.comul (R := R) (single R g))) =
        (Coalgebra.comul (R := R)).lTensor _ (Coalgebra.comul (R := R) (single R g))
    rw [comul_single, map_sum, map_sum, map_sum]
    have hL : ∀ a : G, (TensorProduct.assoc R (GroupFunctions R G) _ _)
        ((Coalgebra.comul (R := R)).rTensor (GroupFunctions R G)
          ((single R a : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g))) =
        ∑ b : G, (single R b : GroupFunctions R G) ⊗ₜ[R]
          ((single R (b⁻¹ * a) : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g)) := by
      intro a
      rw [LinearMap.rTensor_tmul, comul_single, TensorProduct.sum_tmul, map_sum]
      exact Finset.sum_congr rfl fun b _ => TensorProduct.assoc_tmul _ _ _
    have hR : ∀ a : G, (Coalgebra.comul (R := R)).lTensor (GroupFunctions R G)
        ((single R a : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g)) =
        ∑ c : G, (single R a : GroupFunctions R G) ⊗ₜ[R]
          ((single R c : GroupFunctions R G) ⊗ₜ[R] single R (c⁻¹ * (a⁻¹ * g))) := by
      intro a
      rw [LinearMap.lTensor_tmul, comul_single, TensorProduct.tmul_sum]
    simp only [hL, hR]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulLeft b)
      (fun a : G => (single R b : GroupFunctions R G) ⊗ₜ[R]
        ((single R (b⁻¹ * a) : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    show (single R b : GroupFunctions R G) ⊗ₜ[R]
        ((single R (b⁻¹ * (b * c)) : GroupFunctions R G) ⊗ₜ[R] single R ((b * c)⁻¹ * g)) = _
    congr 2 <;> [skip; congr 1] <;> group
  rTensor_counit_comp_comul := by
    refine linearMap_ext fun g => ?_
    show (Coalgebra.counit (R := R)).rTensor _ (Coalgebra.comul (R := R) (single R g)) =
      (1 : R) ⊗ₜ[R] (single R g : GroupFunctions R G)
    rw [comul_single, map_sum]
    rw [Finset.sum_eq_single (1 : G)]
    · rw [LinearMap.rTensor_tmul]
      show (Coalgebra.counit (R := R) (single R (1 : G) : GroupFunctions R G)) ⊗ₜ[R]
        (single R ((1 : G)⁻¹ * g) : GroupFunctions R G) = _
      rw [counit_eq]
      simp
    · intro b _ hb
      rw [LinearMap.rTensor_tmul]
      show (Coalgebra.counit (R := R) (single R b : GroupFunctions R G)) ⊗ₜ[R] _ = 0
      rw [counit_eq, single_apply, if_neg (by simpa using Ne.symm hb), TensorProduct.zero_tmul]
    · intro h; exact absurd (Finset.mem_univ (1 : G)) h
  lTensor_counit_comp_comul := by
    refine linearMap_ext fun g => ?_
    show (Coalgebra.counit (R := R)).lTensor _ (Coalgebra.comul (R := R) (single R g)) =
      (single R g : GroupFunctions R G) ⊗ₜ[R] (1 : R)
    rw [comul_single, map_sum]
    rw [Finset.sum_eq_single g]
    · rw [LinearMap.lTensor_tmul]
      show (single R g : GroupFunctions R G) ⊗ₜ[R]
        (Coalgebra.counit (R := R) (single R (g⁻¹ * g) : GroupFunctions R G)) = _
      rw [counit_eq]
      simp
    · intro b _ hb
      rw [LinearMap.lTensor_tmul]
      show _ ⊗ₜ[R] (Coalgebra.counit (R := R) (single R (b⁻¹ * g) : GroupFunctions R G)) = 0
      rw [counit_eq, single_apply,
        if_neg (fun hc => hb (inv_mul_eq_one.mp hc.symm)), TensorProduct.tmul_zero]
    · intro h; exact absurd (Finset.mem_univ g) h

noncomputable instance : Bialgebra R (GroupFunctions R G) :=
  Bialgebra.mk' R _ (map_one (counitAlgHom R G)) (fun {a b} => map_mul (counitAlgHom R G) a b)
    (map_one (comulAlgHom R G)) (fun {a b} => map_mul (comulAlgHom R G) a b)

lemma sum_single_inv : ∑ a : G, (single R a⁻¹ : GroupFunctions R G) = 1 :=
  (Fintype.sum_equiv (Equiv.inv G) (fun a : G => (single R a⁻¹ : GroupFunctions R G))
    (fun b : G => (single R b : GroupFunctions R G)) (fun _ => rfl)).trans sum_single

noncomputable instance : HopfAlgebraStruct R (GroupFunctions R G) where
  antipode := (antipodeAlgHom R G).toLinearMap

lemma antipode_eq (f : GroupFunctions R G) :
    HopfAlgebra.antipode (A := GroupFunctions R G) R f = antipodeAlgHom R G f := rfl

lemma antipode_single (g : G) :
    HopfAlgebra.antipode (A := GroupFunctions R G) R (single R g : GroupFunctions R G) =
      single R g⁻¹ := by
  rw [antipode_eq]
  ext x
  rw [antipodeAlgHom_apply, single_apply, single_apply]
  congr 1
  simp [inv_eq_iff_eq_inv]

noncomputable instance : HopfAlgebra R (GroupFunctions R G) where
  mul_antipode_rTensor_comul := by
    refine linearMap_ext fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply]
    rw [comul_single, map_sum, map_sum]
    have hterm : ∀ a : G, LinearMap.mul' R (GroupFunctions R G)
        ((HopfAlgebra.antipode (A := GroupFunctions R G) R).rTensor (GroupFunctions R G)
          ((single R a : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g))) =
        if g = 1 then (single R a⁻¹ : GroupFunctions R G) else 0 := by
      intro a
      rw [LinearMap.rTensor_tmul, antipode_single, LinearMap.mul'_apply, single_mul_single]
      by_cases hg : g = 1
      · subst hg; simp
      · rw [if_neg hg, if_neg]
        intro hc
        exact hg (by simpa using hc.symm)
    simp only [hterm]
    rw [counit_eq, single_apply]
    by_cases hg : g = 1
    · subst hg
      simpa using (sum_single_inv (R := R) (G := G))
    · simp only [if_neg hg, Finset.sum_const_zero]
      rw [if_neg (by simpa using Ne.symm hg)]
      simp
  mul_antipode_lTensor_comul := by
    refine linearMap_ext fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply]
    rw [comul_single, map_sum, map_sum]
    have hterm : ∀ a : G, LinearMap.mul' R (GroupFunctions R G)
        ((HopfAlgebra.antipode (A := GroupFunctions R G) R).lTensor (GroupFunctions R G)
          ((single R a : GroupFunctions R G) ⊗ₜ[R] single R (a⁻¹ * g))) =
        if g = 1 then (single R a : GroupFunctions R G) else 0 := by
      intro a
      rw [LinearMap.lTensor_tmul, antipode_single, LinearMap.mul'_apply, single_mul_single]
      by_cases hg : g = 1
      · subst hg; simp
      · rw [if_neg hg, if_neg]
        intro hc
        apply hg
        have h2 : a * a = a * (a⁻¹ * g)⁻¹ := by rw [← hc]
        simpa [mul_inv_rev] using h2
    simp only [hterm]
    rw [counit_eq, single_apply]
    by_cases hg : g = 1
    · subst hg
      simpa using (sum_single (R := R) (G := G))
    · simp only [if_neg hg, Finset.sum_const_zero]
      rw [if_neg (by simpa using Ne.symm hg)]
      simp

end Coalg


variable (R G) in
/-- The generic fibre of the constant group scheme: base change along `R → S` is
the algebra of `S`-valued functions on `G`. -/
noncomputable def baseChangeAlgEquiv [Fintype G] [DecidableEq G]
    (S : Type*) [CommRing S] [Algebra R S] :
    S ⊗[R] GroupFunctions R G ≃ₐ[S] (G → S) :=
  Algebra.TensorProduct.piScalarRight R S S G

section Points

variable [Group G] [Fintype G] [DecidableEq G]
variable {L : Type*} [CommRing L] [Algebra R L]

variable (R L) in
/-- Evaluation at `g`, valued in an `R`-algebra `L`. -/
def pointAlgHom (g : G) : GroupFunctions R G →ₐ[R] L where
  toFun f := algebraMap R L (f g)
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp
  commutes' _ := by simp

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] lemma pointAlgHom_apply (g : G) (f : GroupFunctions R G) :
    pointAlgHom R L g f = algebraMap R L (f g) := rfl

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The point `ev_g` is fixed by postcomposition with any `R`-algebra endomorphism of `L`:
its values lie in the image of `R`. This is what makes the Galois action on the points of
the constant group scheme TRIVIAL. -/
lemma comp_pointAlgHom (ψ : L →ₐ[R] L) (g : G) :
    ψ.comp (pointAlgHom R L g) = pointAlgHom R L g :=
  AlgHom.ext fun _ => ψ.commutes _

variable [Nontrivial L] [NoZeroDivisors L]

omit [Group G] [Fintype G] [NoZeroDivisors L] in
lemma pointAlgHom_injective : Function.Injective (pointAlgHom R L (G := G)) := by
  intro a b hab
  by_contra hne
  have h := congrArg (fun φ => φ (single R a : GroupFunctions R G)) hab
  simp [Ne.symm hne] at h

omit [Group G] in
/-- **Classification of the points**: an `R`-algebra hom out of the constant group scheme,
into a nontrivial ring without zero divisors, is evaluation at a group element. -/
lemma exists_eq_pointAlgHom (φ : GroupFunctions R G →ₐ[R] L) :
    ∃ g : G, φ = pointAlgHom R L g := by
  have hsum : ∑ x : G, φ (single R x : GroupFunctions R G) = 1 := by
    rw [← map_sum, sum_single, map_one]
  have hex : ∃ x : G, φ (single R x : GroupFunctions R G) ≠ 0 := by
    by_contra hcon
    have hzero : ∀ x : G, φ (single R x : GroupFunctions R G) = 0 := fun x => by
      by_contra hx
      exact hcon ⟨x, hx⟩
    rw [Finset.sum_congr rfl (fun x _ => hzero x), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨g, hg⟩ := hex
  have hidem : φ (single R g : GroupFunctions R G) * φ (single R g : GroupFunctions R G) =
      φ (single R g : GroupFunctions R G) := by
    rw [← map_mul, single_mul_single, if_pos rfl]
  have hg1 : φ (single R g : GroupFunctions R G) = 1 := by
    have h0 : φ (single R g : GroupFunctions R G) *
        (φ (single R g : GroupFunctions R G) - 1) = 0 := by
      rw [mul_sub, mul_one, hidem, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hg
    · exact sub_eq_zero.mp h
  have hother : ∀ x : G, x ≠ g → φ (single R x : GroupFunctions R G) = 0 := by
    intro x hx
    have h2 : φ (single R g : GroupFunctions R G) * φ (single R x : GroupFunctions R G) = 0 := by
      rw [← map_mul, single_mul_single, if_neg (Ne.symm hx), map_zero]
    rwa [hg1, one_mul] at h2
  refine ⟨g, ?_⟩
  refine algHom_ext fun x => ?_
  show φ (single R x : GroupFunctions R G) = pointAlgHom R L g (single R x)
  rw [pointAlgHom_apply, single_apply]
  rcases eq_or_ne x g with rfl | hx
  · rw [hg1, if_pos rfl, map_one]
  · rw [hother x hx, if_neg hx.symm, map_zero]

variable (R G L) in
/-- The `L`-points of the constant group scheme on `G` are the elements of `G`. -/
noncomputable def pointsEquiv : G ≃ (GroupFunctions R G →ₐ[R] L) :=
  Equiv.ofBijective (pointAlgHom R L)
    ⟨pointAlgHom_injective, fun φ => (exists_eq_pointAlgHom φ).imp fun _ h => h.symm⟩

omit [Group G] in
@[simp] lemma pointsEquiv_apply (g : G) : pointsEquiv R G L g = pointAlgHom R L g := rfl

omit [Nontrivial L] [NoZeroDivisors L] in
/-- The convolution UNIT is the point `1 : G`. -/
lemma pointAlgHom_convOne :
    (1 : WithConv (GroupFunctions R G →ₐ[R] L)).ofConv = pointAlgHom R L (1 : G) := by
  refine algHom_ext fun g => ?_
  show (1 : WithConv (GroupFunctions R G →ₐ[R] L)) (single R g) = _
  rw [AlgHom.convOne_apply, counit_eq, pointAlgHom_apply]

omit [Nontrivial L] [NoZeroDivisors L] in
/-- The convolution PRODUCT of the points `a` and `b` is the point `a * b`: the group law of
the constant group scheme really is the group law of `G`. -/
lemma pointAlgHom_convMul (a b : G) :
    ((WithConv.toConv (pointAlgHom R L a) *
        WithConv.toConv (pointAlgHom R L b) :
      WithConv (GroupFunctions R G →ₐ[R] L))).ofConv = pointAlgHom R L (a * b) := by
  refine algHom_ext fun g => ?_
  show (WithConv.toConv (pointAlgHom R L a) *
      WithConv.toConv (pointAlgHom R L b) : WithConv (GroupFunctions R G →ₐ[R] L))
      (single R g) = _
  rw [AlgHom.convMul_apply, comul_single, map_sum]
  rw [Finset.sum_eq_single a]
  · rw [Algebra.TensorProduct.lift_tmul]
    show (pointAlgHom R L a) (single R a) * (pointAlgHom R L b) (single R (a⁻¹ * g)) = _
    rw [pointAlgHom_apply, pointAlgHom_apply, pointAlgHom_apply, single_apply, single_apply,
      single_apply, if_pos rfl, map_one, one_mul]
    by_cases h1 : a * b = g
    · rw [if_pos h1, if_pos (by rw [← h1]; group)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (by rw [h2]; group))]
  · intro c _ hc
    rw [Algebra.TensorProduct.lift_tmul]
    show (pointAlgHom R L a) (single R c) * (pointAlgHom R L b) (single R (c⁻¹ * g)) = 0
    rw [pointAlgHom_apply, single_apply, if_neg (Ne.symm hc), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

variable (R G L) in
/-- The `L`-points of the constant group scheme on `G`, with their convolution product,
form a group isomorphic to `G`. -/
noncomputable def pointsMulEquiv : G ≃* WithConv (GroupFunctions R G →ₐ[R] L) where
  toFun g := WithConv.toConv (pointAlgHom R L g)
  invFun φ := (pointsEquiv R G L).symm φ.ofConv
  left_inv g := by
    show (pointsEquiv R G L).symm (pointsEquiv R G L g) = g
    rw [Equiv.symm_apply_apply]
  right_inv φ := by
    refine WithConv.ext ?_
    show pointsEquiv R G L ((pointsEquiv R G L).symm φ.ofConv) = φ.ofConv
    rw [Equiv.apply_symm_apply]
  map_mul' a b := by
    refine WithConv.ext ?_
    exact (pointAlgHom_convMul a b).symm

@[simp] lemma pointsMulEquiv_apply (g : G) :
    pointsMulEquiv R G L g = WithConv.toConv (pointAlgHom R L g) := rfl

end Points

end GroupFunctions
