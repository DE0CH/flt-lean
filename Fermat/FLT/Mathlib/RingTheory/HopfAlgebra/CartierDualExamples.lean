/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.CartierDual
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.GroupFunctions
-- the third commissioned Cartier-duality example, `α_p^D ≅ α_p`; collected here so that all
-- three are built together. Organizational, not a proof dependency — see "The third example".
public import Fermat.FLT.Mathlib.RingTheory.HopfAlgebra.AlphaPSelfDual
public import Mathlib.Data.ZMod.Basic

/-!
# Cartier duality: the constant and diagonalizable examples

The two standard sanity checks for the Cartier dual constructed in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/CartierDual.lean`, for a finite ABELIAN group `G`:

* `CartierDual.dualGroupAlgebraBialgEquiv : CartierDual R (MonoidAlgebra R G) ≃ₐc[R]
  GroupFunctions R G` — the dual of the DIAGONALIZABLE group scheme `Spec R[G]` is the CONSTANT
  group scheme on `G`. At `G := Multiplicative (ZMod n)` this is `μ_n^D ≅ ℤ/n`.
* `CartierDual.groupAlgebraBialgEquivDual : MonoidAlgebra R G ≃ₐc[R]
  CartierDual R (GroupFunctions R G)` — the converse, `(ℤ/n)^D ≅ μ_n`.

Both are proven as bundled `R`-bialgebra equivalences (`≃ₐc[R]`), so they carry the
multiplication, the unit, the counit and the comultiplication; the antipodes then agree
automatically.

The concrete instantiations at `ZMod n` are `CartierDual.muDualEquivZMod` and
`CartierDual.zmodDualEquivMu`.

## The third example

`α_p^D ≅ α_p` is **PROVEN** (2026-07-27), in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaPSelfDual.lean` as
`AlphaP.selfDualBialgEquiv`, over the Hopf algebra `AlphaP R p` of
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/AlphaP.lean`.

STALE NOTE CORRECTED (2026-07-27): this section previously recorded `α_p^D ≅ α_p` as missing and
as a THEORY gap, on the ground that `O(𝔾_a) = R[X]` with ADDITIVE comultiplication exists in
neither the mathlib pin, nor `~/cs/FLT`, nor this tree. That premise is still true and the
conclusion drawn from it was still wrong: `𝔾_a` is not needed, because building `α_p` DIRECTLY as
`AdjoinRoot (X^p)` skips the ambient group and the Hopf-ideal quotient entirely. The content is
the divided-power pairing `y^m = m! · e_m`, with `m!` a unit for `m < p`.

This module imports `AlphaPSelfDual` so that all three commissioned examples are collected — and
therefore COMPILED — as one unit. That import is organizational, not a proof dependency: nothing
below uses `AlphaP`. It is here because the whole Cartier-duality cluster was unreachable from
`Fermat.lean` until 2026-07-27 and so was never built by `lake build` at all; a module no module
in the root's import closure imports is invisible to the build, to the `declaration uses 'sorry'`
warning set, and to the transitive census, and can rot silently. If a later owner gives `AlphaP` a
real consumer, this import should move there.

## Design notes

**Where the content lives.** Both equivalences reduce to one computation each on the two
canonical bases. On the group-algebra side the basis is the grouplike family `single g 1`, whose
comultiplication is `single g 1 ⊗ single g 1` (`comul_monoidAlgebra_single`); on the function
side it is the indicator family `GroupFunctions.single R g`, whose comultiplication is
`∑ₐ e_a ⊗ e_{a⁻¹g}` (`GroupFunctions.comul_single`). Duality exchanges the two: convolution
against a grouplike element is pointwise multiplication, and convolution against an indicator
family is the group law. Those are `CartierDual.evalPoint_mul` and
`CartierDual.dualGroupAlgebraToFunctions_mul` respectively.

**Cocommutativity.** `CartierDual R A` needs `[Coalgebra.IsCocomm R A]` even to have its ring
structure, so `GroupFunctions R G` must be shown cocommutative before its dual can be formed.
That holds exactly when `G` is ABELIAN, and the proof is a reindexing `a ↦ a⁻¹ g` of
`comul_single` — which is a bijection of `G` inverting itself only because `G` is commutative.
Hence the `[CommGroup G]` hypothesis throughout; it is not a convenience.

## References

* Tate, *Finite flat group schemes*, in Cornell–Silverman–Stevens, §2.
* Waterhouse, *Introduction to Affine Group Schemes*, ch. 2.
-/

@[expose] public section

open TensorProduct Coalgebra WithConv

universe u w

namespace GroupFunctions

variable (R : Type u) (G : Type w) [CommRing R]

/-- The forgetful linear equivalence with the plain function module. -/
def piLinearEquiv : GroupFunctions R G ≃ₗ[R] (G → R) where
  toFun f := f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype G] [DecidableEq G]

/-- The indicator functions form a basis. -/
noncomputable def basisSingle : Module.Basis G R (GroupFunctions R G) :=
  (Pi.basisFun R G).map (piLinearEquiv R G).symm

@[simp] lemma basisSingle_apply (g : G) : basisSingle R G g = single R g := by
  simp [basisSingle, single, piLinearEquiv]

section Grp

variable {R G} [Group G]

/-- A Sweedler representation of `comul (e_g)`, read off from `comul_single`. -/
noncomputable def reprSingle (g : G) : Coalgebra.Repr R (single R g : GroupFunctions R G) G where
  index := Finset.univ
  left a := single R a
  right a := single R (a⁻¹ * g)
  eq := (comul_single g).symm

end Grp

section Cocomm

variable {R G} [CommGroup G]

/-- The function algebra of a finite ABELIAN group is cocommutative: the constant group
scheme on an abelian group is a commutative group scheme. -/
instance : IsCocomm R (GroupFunctions R G) where
  comm_comp_comul := by
    refine linearMap_ext fun g => ?_
    show (TensorProduct.comm R (GroupFunctions R G) (GroupFunctions R G))
        (Coalgebra.comul (R := R) (single R g)) = Coalgebra.comul (R := R) (single R g)
    have key : ∀ x : G, (x⁻¹ * g)⁻¹ * g = x := fun x => by
      rw [mul_inv_rev, inv_inv, mul_comm g⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]
    rw [comul_single, map_sum]
    refine Fintype.sum_equiv
      { toFun := fun a : G => a⁻¹ * g, invFun := fun b : G => b⁻¹ * g,
        left_inv := key, right_inv := key } _ _ fun a => ?_
    rw [TensorProduct.comm_tmul]
    show (single R (a⁻¹ * g) : GroupFunctions R G) ⊗ₜ[R] single R a =
      (single R (a⁻¹ * g) : GroupFunctions R G) ⊗ₜ[R] single R ((a⁻¹ * g)⁻¹ * g)
    rw [key a]

end Cocomm

end GroupFunctions

namespace CartierDual

variable {R : Type u} {G : Type w} [CommRing R] [CommGroup G] [Fintype G] [DecidableEq G]

/-- Evaluation at `g : G`, as an element of the Cartier dual of the constant group scheme.
Under the duality below this is the basis vector `g` of the group algebra. -/
noncomputable def evalPoint (g : G) : CartierDual R (GroupFunctions R G) :=
  (toDual R (GroupFunctions R G)).symm
    (LinearMap.proj g ∘ₗ (GroupFunctions.piLinearEquiv R G).toLinearMap)

omit [CommGroup G] [Fintype G] [DecidableEq G] in
@[simp] lemma evalPoint_apply (g : G) (u : GroupFunctions R G) : evalPoint g u = u g := rfl

lemma evalPoint_one : (evalPoint (1 : G) : CartierDual R (GroupFunctions R G)) = 1 := by
  refine ext fun u => ?_
  rw [evalPoint_apply, one_apply, GroupFunctions.counit_eq]

lemma evalPoint_mul (a b : G) :
    (evalPoint (a * b) : CartierDual R (GroupFunctions R G)) = evalPoint a * evalPoint b := by
  refine (toDual R (GroupFunctions R G)).injective (GroupFunctions.linearMap_ext fun g => ?_)
  show (evalPoint (a * b) : CartierDual R (GroupFunctions R G)) (GroupFunctions.single R g) =
    (evalPoint a * evalPoint b : CartierDual R (GroupFunctions R G)) (GroupFunctions.single R g)
  rw [mul_apply_repr (GroupFunctions.reprSingle g), evalPoint_apply, GroupFunctions.single_apply]
  show _ = ∑ c : G, (GroupFunctions.single R c : GroupFunctions R G) a *
    (GroupFunctions.single R (c⁻¹ * g) : GroupFunctions R G) b
  rw [Finset.sum_eq_single a]
  · rw [GroupFunctions.single_apply, GroupFunctions.single_apply, if_pos rfl, one_mul]
    by_cases h : a * b = g
    · rw [if_pos h, if_pos (by rw [← h]; group)]
    · rw [if_neg h, if_neg (fun hc => h (by rw [hc]; group))]
  · intro c _ hc
    rw [GroupFunctions.single_apply, if_neg (Ne.symm hc), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma comul_evalPoint (g : G) :
    comul (R := R) (evalPoint g : CartierDual R (GroupFunctions R G))
      = evalPoint g ⊗ₜ[R] evalPoint g := by
  refine pairMap_injective fun u v => ?_
  rw [pairMap_comul, pairMap_tmul, evalPoint_apply, evalPoint_apply, evalPoint_apply,
    GroupFunctions.mul_apply]

lemma counit_evalPoint (g : G) :
    counit (R := R) (evalPoint g : CartierDual R (GroupFunctions R G)) = 1 := by
  rw [counit_apply, evalPoint_apply, GroupFunctions.one_apply]

/-! ## Grouplike basis vectors of the group algebra -/

section GroupAlgebra

variable (R G)

omit [CommGroup G] [Fintype G] [DecidableEq G] in
lemma comul_monoidAlgebra_single (g : G) :
    comul (R := R) (MonoidAlgebra.single g (1 : R))
      = MonoidAlgebra.single g (1 : R) ⊗ₜ[R] MonoidAlgebra.single g (1 : R) := by
  rw [MonoidAlgebra.comul_single, show comul (R := R) (1 : R) = (1 : R) ⊗ₜ[R] (1 : R) from by
    rw [Bialgebra.comul_one, Algebra.TensorProduct.one_def], TensorProduct.map_tmul]
  rfl

/-- A Sweedler representation of the grouplike element `single g 1`. -/
noncomputable def reprMonoidAlgebraSingle (g : G) :
    Coalgebra.Repr R (MonoidAlgebra.single g (1 : R)) Unit where
  index := {()}
  left _ := MonoidAlgebra.single g 1
  right _ := MonoidAlgebra.single g 1
  eq := by rw [Finset.sum_singleton]; exact (comul_monoidAlgebra_single R G g).symm

/-! ## `(ℤ/n)^D ≅ μ_n`: the dual of a constant group scheme is diagonalizable -/

/-- The points of the constant group scheme, as a monoid hom into its Cartier dual. -/
noncomputable def evalPointMonoidHom : G →* CartierDual R (GroupFunctions R G) where
  toFun := evalPoint
  map_one' := evalPoint_one
  map_mul' a b := evalPoint_mul a b

/-- The comparison map `R[G] → O(G)^D`, sending the basis vector `g` to evaluation at `g`. -/
noncomputable def groupAlgebraToDual :
    MonoidAlgebra R G →ₐ[R] CartierDual R (GroupFunctions R G) :=
  MonoidAlgebra.lift R _ G (evalPointMonoidHom R G)

@[simp] lemma groupAlgebraToDual_single (g : G) :
    groupAlgebraToDual R G (MonoidAlgebra.single g (1 : R)) = evalPoint g := by
  rw [groupAlgebraToDual, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- The inverse comparison map, reading off the coefficients of a functional on the indicator
basis. -/
noncomputable def dualToGroupAlgebra :
    CartierDual R (GroupFunctions R G) →ₗ[R] MonoidAlgebra R G :=
  ∑ g : G, (MonoidAlgebra.lsingle (R := R) g).comp
    (evalAt R (GroupFunctions R G) (GroupFunctions.single R g))

lemma dualToGroupAlgebra_apply (f : CartierDual R (GroupFunctions R G)) :
    dualToGroupAlgebra R G f
      = ∑ g : G, MonoidAlgebra.single g (f (GroupFunctions.single R g)) := by
  rw [dualToGroupAlgebra, LinearMap.sum_apply]
  rfl

lemma dualToGroupAlgebra_groupAlgebraToDual (x : MonoidAlgebra R G) :
    dualToGroupAlgebra R G (groupAlgebraToDual R G x) = x := by
  revert x
  suffices h : (dualToGroupAlgebra R G).comp (groupAlgebraToDual R G).toLinearMap
      = LinearMap.id from fun x => congr($h x)
  refine MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring ?_
  show dualToGroupAlgebra R G (groupAlgebraToDual R G (MonoidAlgebra.single g (1 : R)))
    = MonoidAlgebra.single g (1 : R)
  rw [groupAlgebraToDual_single, dualToGroupAlgebra_apply, Finset.sum_eq_single g]
  · rw [evalPoint_apply, GroupFunctions.single_apply, if_pos rfl]
  · intro c _ hc
    rw [evalPoint_apply, GroupFunctions.single_apply, if_neg (Ne.symm hc),
      MonoidAlgebra.single_zero]
  · intro h; exact absurd (Finset.mem_univ g) h

lemma groupAlgebraToDual_dualToGroupAlgebra (f : CartierDual R (GroupFunctions R G)) :
    groupAlgebraToDual R G (dualToGroupAlgebra R G f) = f := by
  rw [dualToGroupAlgebra_apply, map_sum]
  refine (toDual R (GroupFunctions R G)).injective (GroupFunctions.linearMap_ext fun h => ?_)
  show (∑ g : G, groupAlgebraToDual R G (MonoidAlgebra.single g (f (GroupFunctions.single R g))))
      (GroupFunctions.single R h) = f (GroupFunctions.single R h)
  rw [sum_apply, Finset.sum_eq_single h]
  · rw [show MonoidAlgebra.single h (f (GroupFunctions.single R h))
      = f (GroupFunctions.single R h) • MonoidAlgebra.single h (1 : R) from by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], map_smul, groupAlgebraToDual_single,
      smul_apply, evalPoint_apply, GroupFunctions.single_apply, if_pos rfl, mul_one]
  · intro c _ hc
    rw [show MonoidAlgebra.single c (f (GroupFunctions.single R c))
      = f (GroupFunctions.single R c) • MonoidAlgebra.single c (1 : R) from by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], map_smul, groupAlgebraToDual_single,
      smul_apply, evalPoint_apply, GroupFunctions.single_apply, if_neg hc, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ h) h'

/-- **`(ℤ/n)^D ≅ μ_n`, in general form**: the Cartier dual of the constant group scheme on a
finite abelian group `G` is the diagonalizable group scheme `Spec R[G]`. -/
noncomputable def groupAlgebraAlgEquivDual :
    MonoidAlgebra R G ≃ₐ[R] CartierDual R (GroupFunctions R G) :=
  AlgEquiv.ofBijective (groupAlgebraToDual R G)
    (Function.bijective_iff_has_inverse.mpr
      ⟨dualToGroupAlgebra R G, dualToGroupAlgebra_groupAlgebraToDual R G,
        groupAlgebraToDual_dualToGroupAlgebra R G⟩)

@[simp] lemma groupAlgebraAlgEquivDual_single (g : G) :
    groupAlgebraAlgEquivDual R G (MonoidAlgebra.single g (1 : R)) = evalPoint g :=
  groupAlgebraToDual_single R G g

/-- **`(ℤ/n)^D ≅ μ_n` as HOPF algebras.** -/
noncomputable def groupAlgebraBialgEquivDual :
    MonoidAlgebra R G ≃ₐc[R] CartierDual R (GroupFunctions R G) :=
  BialgEquiv.ofAlgEquiv (groupAlgebraAlgEquivDual R G)
    (MonoidAlgebra.algHom_ext (fun g => by
      show counit (R := R) (groupAlgebraToDual R G (MonoidAlgebra.single g (1 : R)))
        = counit (R := R) (MonoidAlgebra.single g (1 : R))
      rw [groupAlgebraToDual_single, counit_evalPoint, MonoidAlgebra.counit_single,
        Bialgebra.counit_one])
      (Subsingleton.elim _ _))
    (MonoidAlgebra.algHom_ext (fun g => by
      show (Algebra.TensorProduct.map (groupAlgebraToDual R G) (groupAlgebraToDual R G))
          (comul (R := R) (MonoidAlgebra.single g (1 : R)))
        = comul (R := R) (groupAlgebraToDual R G (MonoidAlgebra.single g (1 : R)))
      rw [comul_monoidAlgebra_single, Algebra.TensorProduct.map_tmul, groupAlgebraToDual_single,
        comul_evalPoint])
      (Subsingleton.elim _ _))

/-! ## `μ_n^D ≅ ℤ/n`: the dual of a diagonalizable group scheme is constant -/

lemma tensorEquiv_comul (u : GroupFunctions R G) :
    GroupFunctions.tensorEquiv R G (comul (R := R) u) = GroupFunctions.mulPullback R G u := by
  rw [GroupFunctions.comul_eq, GroupFunctions.comulAlgHom]
  show GroupFunctions.tensorEquiv R G
    ((GroupFunctions.tensorEquiv R G).symm (GroupFunctions.mulPullback R G u)) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The comparison map `R[G]^D → O(G)`: a functional on the group algebra is the function
recording its values on the grouplike basis. -/
noncomputable def dualGroupAlgebraToFunctions :
    CartierDual R (MonoidAlgebra R G) ≃ₗ[R] GroupFunctions R G :=
  ((toDual R (MonoidAlgebra R G)).trans ((MonoidAlgebra.basis G R).constr R).symm).trans
    (GroupFunctions.piLinearEquiv R G).symm

omit [CommGroup G] [Fintype G] [DecidableEq G] in
@[simp] lemma dualGroupAlgebraToFunctions_apply (f : CartierDual R (MonoidAlgebra R G)) (g : G) :
    dualGroupAlgebraToFunctions R G f g = f (MonoidAlgebra.single g (1 : R)) := by
  have h := Module.Basis.constr_basis (MonoidAlgebra.basis G R) R
    (((MonoidAlgebra.basis G R).constr R).symm (toDual R (MonoidAlgebra R G) f)) g
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

omit [Fintype G] [DecidableEq G] in
lemma dualGroupAlgebraToFunctions_one : dualGroupAlgebraToFunctions R G 1 = 1 := by
  refine GroupFunctions.ext fun g => ?_
  rw [dualGroupAlgebraToFunctions_apply, one_apply, MonoidAlgebra.counit_single,
    Bialgebra.counit_one, GroupFunctions.one_apply]

omit [CommGroup G] [Fintype G] [DecidableEq G] in
lemma dualGroupAlgebraToFunctions_mul (f₁ f₂ : CartierDual R (MonoidAlgebra R G)) :
    dualGroupAlgebraToFunctions R G (f₁ * f₂)
      = dualGroupAlgebraToFunctions R G f₁ * dualGroupAlgebraToFunctions R G f₂ := by
  refine GroupFunctions.ext fun g => ?_
  rw [GroupFunctions.mul_apply, dualGroupAlgebraToFunctions_apply,
    dualGroupAlgebraToFunctions_apply, dualGroupAlgebraToFunctions_apply,
    mul_apply_repr (reprMonoidAlgebraSingle R G g)]
  show (∑ _i ∈ ({()} : Finset Unit), f₁ (MonoidAlgebra.single g (1 : R)) *
    f₂ (MonoidAlgebra.single g (1 : R))) = _
  rw [Finset.sum_singleton]

/-- `μ_n^D ≅ ℤ/n` as algebras. -/
noncomputable def dualGroupAlgebraAlgEquiv :
    CartierDual R (MonoidAlgebra R G) ≃ₐ[R] GroupFunctions R G :=
  { dualGroupAlgebraToFunctions R G with
    map_mul' := dualGroupAlgebraToFunctions_mul R G
    commutes' := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      show dualGroupAlgebraToFunctions R G (r • 1) = _
      rw [map_smul, dualGroupAlgebraToFunctions_one] }

lemma tensorEquiv_map_dualGroupAlgebra
    (z : CartierDual R (MonoidAlgebra R G) ⊗[R] CartierDual R (MonoidAlgebra R G)) (p : G × G) :
    GroupFunctions.tensorEquiv R G
        (TensorProduct.map (dualGroupAlgebraToFunctions R G).toLinearMap
          (dualGroupAlgebraToFunctions R G).toLinearMap z) p
      = pairMap (MonoidAlgebra.single p.1 (1 : R)) (MonoidAlgebra.single p.2 (1 : R)) z := by
  induction z with
  | zero => simp
  | tmul u v =>
      rw [TensorProduct.map_tmul, GroupFunctions.tensorEquiv_tmul, pairMap_tmul]
      exact congrArg₂ _ (dualGroupAlgebraToFunctions_apply R G u p.1)
        (dualGroupAlgebraToFunctions_apply R G v p.2)
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, map_add]

/-- Biduality-free statement of comultiplication compatibility for `μ_n^D ≅ ℤ/n`. -/
theorem map_comul_dualGroupAlgebra (f : CartierDual R (MonoidAlgebra R G)) :
    TensorProduct.map (dualGroupAlgebraToFunctions R G).toLinearMap
        (dualGroupAlgebraToFunctions R G).toLinearMap (comul (R := R) f)
      = comul (R := R) (dualGroupAlgebraToFunctions R G f) := by
  apply (GroupFunctions.tensorEquiv R G).injective
  rw [tensorEquiv_comul]
  funext p
  rw [tensorEquiv_map_dualGroupAlgebra, pairMap_comul, MonoidAlgebra.single_mul_single, one_mul,
    GroupFunctions.mulPullback_apply, dualGroupAlgebraToFunctions_apply]

lemma counit_dualGroupAlgebraToFunctions (f : CartierDual R (MonoidAlgebra R G)) :
    counit (R := R) (dualGroupAlgebraToFunctions R G f) = counit (R := R) f := by
  rw [GroupFunctions.counit_eq, dualGroupAlgebraToFunctions_apply, counit_apply,
    MonoidAlgebra.one_def]

/-- **`μ_n^D ≅ ℤ/n` as HOPF algebras**: the Cartier dual of the diagonalizable group scheme
`Spec R[G]` is the constant group scheme on `G`. -/
noncomputable def dualGroupAlgebraBialgEquiv :
    CartierDual R (MonoidAlgebra R G) ≃ₐc[R] GroupFunctions R G where
  __ := dualGroupAlgebraAlgEquiv R G
  map_smul' := map_smul (dualGroupAlgebraToFunctions R G)
  counit_comp := LinearMap.ext (counit_dualGroupAlgebraToFunctions R G)
  map_comp_comul := LinearMap.ext (map_comul_dualGroupAlgebra R G)

end GroupAlgebra

/-! ## The concrete examples at `ZMod n` -/

section ZMod

variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]

/-- `O(μ_n)`: the coordinate ring of the group scheme of `n`-th roots of unity, i.e. the group
algebra `R[ℤ/n] ≅ R[x]/(xⁿ - 1)`. -/
abbrev MuCoord := MonoidAlgebra R (Multiplicative (ZMod n))

/-- `O(ℤ/n)`: the coordinate ring of the CONSTANT group scheme on `ℤ/n`. -/
abbrev ZModCoord := GroupFunctions R (Multiplicative (ZMod n))

/-- **`μ_n^D ≅ ℤ/n`.** The Cartier dual of the group scheme of `n`-th roots of unity is the
constant group scheme on `ℤ/n`. -/
noncomputable def muDualEquivZMod : CartierDual R (MuCoord R n) ≃ₐc[R] ZModCoord R n :=
  dualGroupAlgebraBialgEquiv R (Multiplicative (ZMod n))

/-- **`(ℤ/n)^D ≅ μ_n`.** The Cartier dual of the constant group scheme on `ℤ/n` is the group
scheme of `n`-th roots of unity — the other half of the involution. -/
noncomputable def zmodDualEquivMu : CartierDual R (ZModCoord R n) ≃ₐc[R] MuCoord R n :=
  (groupAlgebraBialgEquivDual R (Multiplicative (ZMod n))).symm

end ZMod

end CartierDual
