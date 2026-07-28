/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Degree-one continuous cohomology: the inhomogeneous description

Our mathlib pin computes `continuousCohomology n X` from the HOMOGENEOUS cochain complex
`TopRep.homogeneousCochains X`, whose degree-`j` term is the `G`-invariants of the `j+1`-fold
coinduction `C(G, C(G, … , M))`, and its `ContCohomology/LowDegree.lean` stops at degree `0`
(`zeroIso`, the identification of `H⁰` with the invariants).  Nothing identifies `H¹` with
crossed homomorphisms modulo principal ones.

That identification is what every obstruction-theoretic and Chebotarev-style argument needs,
because those arguments evaluate a class at a single group element: "`c(σ) ∉ (σ - 1)·M`" is
not expressible until a class has an INHOMOGENEOUS cocycle representative.

This file supplies the half of the identification that such arguments actually use — the
map from a homogeneous 1-cochain to an inhomogeneous one, and the crossed-homomorphism
identity it satisfies when the cochain is a cocycle:

* `ContinuousCohomology.eval₁ X f g = f 1 g`, together with `continuous_eval₁`;
* `eval₁_mul`: `eval₁ f (g * h) = eval₁ f g + ρ g (eval₁ f h)` for a cocycle `f`;
* `eval₁_one`, `eval₁_inv`, `eval₁_conj` — the usual consequences;
* `eval₁_mem_range_sub_conj`: the SURVIVING LOCUS
  `{x | eval₁ f x ∉ (ρ x - 1) · M}` is stable under conjugation.  This is the property that
  makes such a locus usable with Chebotarev density, where only conjugacy classes of
  Frobenius elements are available;
* `exists_cocycleClass_eq`: every class is the class of a cocycle, i.e.
  `ContinuousCohomology.cocycleClass X j` is surjective.

## The concrete formulas, and where they come from

Mathlib's `TopRep.d` is defined inductively rather than as an alternating sum:
`d X 0 = coind₁ι = const` and `d X (n+1) = coind₁ι - coind₁Map (d X n)`.  Unfolding twice
gives, for `F : C(G, M)` and `f : C(G, C(G, M))`,

    (d X 1 F) g h   = F h - F g ,
    (d X 2 f) g h l = f h l - f g l + f g h ,

which is `homogeneousCochains_d_one_two_apply` below; and `G`-invariance of `f` — membership
in `(resolution' X).X 1`'s invariants, unfolded through `coind₁_apply_apply` — reads

    f (σ x) (σ y) = ρ σ (f x y) ,

which is `homogeneousCochains_apply_smul`.  Setting `z g := f 1 g`, the cocycle relation at
`g = 1` gives `f h l = z l - z h`, and invariance at `σ = g`, `x = 1`, `y = h` gives
`f g (g * h) = ρ g (z h)`; the two together are the crossed-homomorphism identity.

Material destined for `Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree`.
-/

@[expose] public section

universe u v

namespace ContinuousCohomology

open CategoryTheory TopRep ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G)

/-- **Homogeneity of a degree-`1` homogeneous cochain**: `f (σ x) (σ y) = ρ σ (f x y)`.
This is membership in the invariants of the twice-coinduced representation, unfolded
through `ContRepresentation.coind₁_apply_apply`. -/
lemma homogeneousCochains_apply_smul (f : ↥((homogeneousCochains X).X 1)) (σ x y : G) :
    (f.1 (σ * x)) (σ * y) = X.ρ σ ((f.1 x) y) := by
  have h := (ContRepresentation.mem_invariants (π := (X.resolution'.X 1).ρ) f.1).mp f.2 σ
  have h2 := congr(($h) (σ * x) (σ * y))
  rw [← h2]
  simp [ContRepresentation.coind₁_apply_apply]

/-- **The degree-`1` differential of the homogeneous cochain complex, evaluated**:
`(d f) g h l = f h l - f g l + f g h`.  The inductive definition of `TopRep.d` makes this
a definitional unfolding up to associativity of subtraction. -/
lemma homogeneousCochains_d_one_two_apply (f : ↥((homogeneousCochains X).X 1)) (g h l : G) :
    (((homogeneousCochains X).d 1 2).hom f).1 g h l =
      f.1 h l - f.1 g l + f.1 g h := by
  rw [homogeneousCochains.d_apply]
  show f.1 h l - (f.1 g l - f.1 g h) = _
  abel

/-- **The inhomogeneous `1`-cochain attached to a homogeneous one**: `eval₁ f g = f 1 g`.
For a COCYCLE `f` this is a continuous crossed homomorphism (`eval₁_mul`). -/
def eval₁ (f : ↥((homogeneousCochains X).X 1)) (g : G) : ↥X := f.1 1 g

lemma eval₁_def (f : ↥((homogeneousCochains X).X 1)) (g : G) :
    eval₁ X f g = f.1 1 g := rfl

/-- `eval₁ f` is continuous, being an evaluation of the continuous map `f 1`. -/
lemma continuous_eval₁ (f : ↥((homogeneousCochains X).X 1)) :
    Continuous (eval₁ X f) := (f.1 1).continuous

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The representation is multiplicative, pointwise. -/
lemma rho_mul_apply (u v : G) (a : ↥X) : X.ρ (u * v) a = X.ρ u (X.ρ v a) := by simp

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `ρ g⁻¹` undoes `ρ g`. -/
lemma rho_inv_apply (g : G) (a : ↥X) : X.ρ g⁻¹ (X.ρ g a) = a := by
  have h := rho_mul_apply X g⁻¹ g a
  rw [inv_mul_cancel] at h
  have h1 : X.ρ (1 : G) a = a := by simp
  rw [h1] at h
  exact h.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `ρ g` undoes `ρ g⁻¹`. -/
lemma rho_apply_inv (g : G) (a : ↥X) : X.ρ g (X.ρ g⁻¹ a) = a := by
  simpa using rho_inv_apply X g⁻¹ a

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `ρ g` is injective on the underlying module. -/
lemma rho_injective (g : G) : Function.Injective fun a : ↥X => X.ρ g a := by
  intro a b hab
  have h := congrArg (fun t : ↥X => X.ρ g⁻¹ t) hab
  simpa only [rho_inv_apply] using h

variable {X}

/-- **A cocycle is determined by its inhomogeneous cochain**: `f h l = eval₁ f l - eval₁ f h`,
the cocycle relation at `g = 1`. -/
lemma cocycle_apply {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) (h l : G) :
    f.1 h l = eval₁ X f l - eval₁ X f h := by
  have hd := homogeneousCochains_d_one_two_apply X f 1 h l
  rw [hf] at hd
  have h3 : f.1 h l - f.1 1 l + f.1 1 h = 0 := by rw [← hd]; rfl
  unfold eval₁
  have h4 : f.1 h l - (f.1 1 l - f.1 1 h) = 0 := by rw [← h3]; abel
  exact sub_eq_zero.mp h4

/-- **The crossed-homomorphism identity**: a continuous `1`-cocycle evaluates as
`z (g * h) = z g + ρ g (z h)`. -/
lemma eval₁_mul {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) (g h : G) :
    eval₁ X f (g * h) = eval₁ X f g + X.ρ g (eval₁ X f h) := by
  have h1 := cocycle_apply hf g (g * h)
  have h2 := homogeneousCochains_apply_smul X f g 1 h
  rw [mul_one] at h2
  rw [h1] at h2
  rw [sub_eq_iff_eq_add] at h2
  rw [h2, add_comm]
  rfl

/-- A crossed homomorphism vanishes at `1`. -/
lemma eval₁_one {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) :
    eval₁ X f 1 = 0 := by
  have h := eval₁_mul hf 1 1
  rw [mul_one] at h
  simpa using h

/-- A crossed homomorphism at an inverse: `z g⁻¹ = - ρ g⁻¹ (z g)`. -/
lemma eval₁_inv {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) (g : G) :
    eval₁ X f g⁻¹ = - X.ρ g⁻¹ (eval₁ X f g) := by
  have h := eval₁_mul hf g⁻¹ g
  rw [inv_mul_cancel, eval₁_one hf] at h
  exact add_eq_zero_iff_eq_neg.mp h.symm

/-- **A crossed homomorphism at a conjugate**:
`z (g x g⁻¹) = ρ g (z x) + z g - ρ (g x g⁻¹) (z g)`.  The correction term is a
`(ρ (g x g⁻¹) - 1)`-boundary, which is what makes the surviving locus below conjugation
stable. -/
lemma eval₁_conj {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) (g x : G) :
    eval₁ X f (g * x * g⁻¹) =
      X.ρ g (eval₁ X f x) + eval₁ X f g - X.ρ (g * x * g⁻¹) (eval₁ X f g) := by
  have hρ : ∀ m : ↥X, X.ρ (g * (x * g⁻¹)) m = X.ρ g (X.ρ x (X.ρ g⁻¹ m)) := by
    intro m; simp
  rw [mul_assoc, eval₁_mul hf g (x * g⁻¹), eval₁_mul hf x g⁻¹, eval₁_inv hf g,
    map_neg, map_add, map_neg, hρ]
  abel

/-- **The surviving locus of a `1`-cocycle is stable under conjugation.**  A class
`c` survives at `x` when a cocycle representative `z` has `z x ∉ (ρ x - 1) · M`; this says
the condition depends only on the conjugacy class of `x`, which is what makes the locus
usable with Chebotarev density (only Frobenius CONJUGACY CLASSES are available there).

The proof is the identity `eval₁_conj` plus the observation that `ρ g` carries
`(ρ x - 1) · M` onto `(ρ (g x g⁻¹) - 1) · M` bijectively. -/
lemma eval₁_mem_range_sub_conj {f : ↥((homogeneousCochains X).X 1)}
    (hf : ((homogeneousCochains X).d 1 2).hom f = 0) (g x : G)
    (h : eval₁ X f (g * x * g⁻¹) ∈ Set.range fun m : ↥X => X.ρ (g * x * g⁻¹) m - m) :
    eval₁ X f x ∈ Set.range fun m : ↥X => X.ρ x m - m := by
  obtain ⟨m, hm⟩ := h
  have hm2 : X.ρ (g * x * g⁻¹) m - m = eval₁ X f (g * x * g⁻¹) := hm
  have hcomp : ∀ m' : ↥X, X.ρ g (X.ρ x (X.ρ g⁻¹ m')) = X.ρ (g * x * g⁻¹) m' := by
    intro m'; simp [mul_assoc]
  refine ⟨X.ρ g⁻¹ (m + eval₁ X f g), ?_⟩
  show X.ρ x (X.ρ g⁻¹ (m + eval₁ X f g)) - X.ρ g⁻¹ (m + eval₁ X f g) = eval₁ X f x
  refine rho_injective X g ?_
  show X.ρ g (X.ρ x (X.ρ g⁻¹ (m + eval₁ X f g)) - X.ρ g⁻¹ (m + eval₁ X f g)) = _
  rw [map_sub, hcomp, rho_apply_inv]
  show X.ρ (g * x * g⁻¹) (m + eval₁ X f g) - (m + eval₁ X f g) = X.ρ g (eval₁ X f x)
  have hsplit : X.ρ (g * x * g⁻¹) (m + eval₁ X f g) - (m + eval₁ X f g) =
      (X.ρ (g * x * g⁻¹) m - m) +
        (X.ρ (g * x * g⁻¹) (eval₁ X f g) - eval₁ X f g) := by
    rw [map_add]; abel
  rw [hsplit, hm2, eval₁_conj hf]
  abel

variable (X)

/-- **The continuous `1`-cocycles of `X`**, in the kernel model — exactly the domain of
`ContinuousCohomology.cocycleClass X 1`. -/
abbrev cocycles₁ : Type _ :=
  ↥(TopModuleCat.ker ((homogeneousCochains X).d 1 (1 + 1)))

variable {X}

/-- A `1`-cocycle satisfies the cocycle equation. -/
lemma cocycles₁_d_eq_zero (z : cocycles₁ X) :
    ((homogeneousCochains X).d 1 2).hom z.1 = 0 := z.2

/-- The crossed-homomorphism identity, for a member of `cocycles₁`. -/
lemma cocycles₁_eval₁_mul (z : cocycles₁ X) (g h : G) :
    eval₁ X z.1 (g * h) = eval₁ X z.1 g + X.ρ g (eval₁ X z.1 h) :=
  eval₁_mul (cocycles₁_d_eq_zero z) g h

/-- Conjugation stability of the surviving locus, for a member of `cocycles₁`. -/
lemma cocycles₁_eval₁_mem_range_sub_conj (z : cocycles₁ X) (g x : G)
    (h : eval₁ X z.1 (g * x * g⁻¹) ∈ Set.range fun m : ↥X => X.ρ (g * x * g⁻¹) m - m) :
    eval₁ X z.1 x ∈ Set.range fun m : ↥X => X.ρ x m - m :=
  eval₁_mem_range_sub_conj (cocycles₁_d_eq_zero z) g x h

/-- **Every class is the class of a cocycle**: `ContinuousCohomology.cocycleClass X j` is
surjective, because it is the concrete quotient map `TopModuleCat.cokerπ` followed by an
isomorphism. -/
lemma exists_cocycleClass_eq (j : ℕ) (c : ↥(continuousCohomology j X)) :
    ∃ z : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1))),
      cocycleClass X j z = c := by
  obtain ⟨y, hy⟩ := TopModuleCat.cokerπ_surjective (bdryKer X j)
    ((cohomologyIsoQuot X j).hom c)
  refine ⟨y, ?_⟩
  rw [cocycleClass_apply, hy]
  exact congr($((cohomologyIsoQuot X j).hom_inv_id) c)

end ContinuousCohomology
