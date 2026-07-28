/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
-- ADDED 2026-07-28 for the FUNCTORIALITY half of the dictionary
-- (`map_cocycleClass`, `cocyclesMapKer`, `eval₁_cochainsMap`): restriction of a
-- class to a subgroup is `ContinuousCohomology.map`, and reading it off on
-- cocycles is what every "the class dies on `N`" argument needs.  `public`
-- because `cocyclesMapKer` appears in signature position below.
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

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

ADDED 2026-07-28, and it is the half that turns the dictionary from a way of *writing*
`z x` into a way of *computing with classes* — the coboundary criterion and the
functoriality:

* `eval₁_bdryKer`: the inhomogeneous cochain of a COBOUNDARY is `g ↦ ρ g m - m`, where
  `m = F 1` is the value of the degree-`0` cochain at `1`;
* `exists_eval₁_eq_sub_of_cocycleClass_eq_zero` and
  `cocycleClass_eq_zero_of_eval₁_eq_sub`: the two halves of
  "`[z] = 0 ↔ z` is a principal crossed homomorphism".  The forward half is
  unconditional; the converse needs `Continuous fun g ↦ ρ g m`, which is NOT automatic
  (`ContRepresentation` asks continuity of each `ρ g` on `M` and nothing about `g`) —
  but it IS free at `m = 0`, which is the case every "the class dies on `N`" argument
  uses;
* `cocycleClass_cyclesIsoKer_hom`: `cocycleClass` is `HomologicalComplex.homologyπ`
  read through the kernel model, which is what connects the concrete quotient model of
  `ContCohomology/Basic.lean` to mathlib's `ContinuousCohomology.π_map`;
* `cocyclesMapKer` and `map_cocycleClass` / `map_cocycleClass_cocyclesMapKer`:
  FUNCTORIALITY, `map φ f j [z] = [f ∘ z ∘ φ]`, together with
  `eval₁_cochainsMap` / `eval₁_cocyclesMapKer` computing the transported cocycle,
  `eval₁ (f ∘ z ∘ φ) h = f (eval₁ z (φ h))`.

Those last two are what makes RESTRICTION usable: `res^G_N [z] = 0` becomes
"`eval₁ z` is a coboundary on `N`", and conversely a cocycle vanishing on `N` has a
class killed by restriction.

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

open CategoryTheory Limits TopRep ContRepresentation

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


/-! ### The coboundary criterion in degree `1`

ADDED 2026-07-28.  Everything above describes a cocycle's inhomogeneous cochain; this
section describes when its CLASS vanishes, which is what a restriction argument
actually consumes.  A degree-`0` homogeneous cochain is an invariant `F ∈ C(G, M)`,
hence `F g = ρ g (F 1)`, and its differential is `g ↦ F g - F 1 = ρ g m - m` with
`m = F 1`: the classical principal crossed homomorphism. -/

section degreeZero

variable (X)

/-- **Homogeneity of a degree-`0` homogeneous cochain**: `F (σ x) = ρ σ (F x)`.  The
degree-`0` analogue of `homogeneousCochains_apply_smul`. -/
lemma homogeneousCochains_zero_apply_smul (F : ↥((homogeneousCochains X).X 0)) (σ x : G) :
    F.1 (σ * x) = X.ρ σ (F.1 x) := by
  have h := (ContRepresentation.mem_invariants (π := (X.resolution'.X 0).ρ) F.1).mp F.2 σ
  have h2 := congr(($h) (σ * x))
  rw [← h2]
  simp [ContRepresentation.coind₁_apply_apply]

/-- **The degree-`0` differential of the homogeneous cochain complex, evaluated**:
`(d F) g h = F h - F g`. -/
lemma homogeneousCochains_d_zero_one_apply (F : ↥((homogeneousCochains X).X 0)) (g h : G) :
    (((homogeneousCochains X).d 0 1).hom F).1 g h = F.1 h - F.1 g := by
  rw [homogeneousCochains.d_apply]
  rfl

/-- **The inhomogeneous cochain of a COBOUNDARY** is the principal crossed homomorphism
`g ↦ ρ g m - m`, with `m = F 1`. -/
lemma eval₁_bdryKer (F : ↥((homogeneousCochains X).X 0)) (g : G) :
    eval₁ X (bdryKer X 1 F) g = X.ρ g (F.1 1) - F.1 1 := by
  have h1 : (bdryKer X 1 F).1 = ((homogeneousCochains X).d 0 1).hom F := bdryKer_apply_coe X 1 F
  rw [eval₁_def, h1, homogeneousCochains_d_zero_one_apply,
    show F.1 g = F.1 (g * 1) by rw [mul_one], homogeneousCochains_zero_apply_smul]

variable {X}

/-- **A cocycle with vanishing class is a principal crossed homomorphism.**  This half
of the criterion is UNCONDITIONAL, which is why it is the one restriction arguments use
on the target group. -/
lemma exists_eval₁_eq_sub_of_cocycleClass_eq_zero (z : cocycles₁ X)
    (hz : cocycleClass X 1 z = 0) :
    ∃ m : ↥X, ∀ g : G, eval₁ X z.1 g = X.ρ g m - m := by
  rw [cocycleClass_eq_zero_iff] at hz
  obtain ⟨F, hF⟩ := hz
  refine ⟨F.1 1, fun g => ?_⟩
  have hFz : (bdryKer X 1 F) = z := hF
  rw [← hFz, eval₁_bdryKer]

/-- **The converse half**: a principal crossed homomorphism has vanishing class.

`hcont` is genuinely needed and is NOT automatic: `ContRepresentation` asks that each
`ρ g` be continuous on `M` and says nothing about continuity in `g` (that is deliberate
upstream — it is what lets `coind₁` be formed with no hypothesis on the topology of
`G`), so the degree-`0` cochain `g ↦ ρ g m` need not exist.  At `m = 0` the hypothesis
is `Continuous fun _ ↦ 0` and therefore free, and that is the instance every
"the restriction of this class to `N` vanishes" argument needs. -/
lemma cocycleClass_eq_zero_of_eval₁_eq_sub (z : cocycles₁ X) (m : ↥X)
    (hcont : Continuous fun g : G => X.ρ g m)
    (h : ∀ g : G, eval₁ X z.1 g = X.ρ g m - m) :
    cocycleClass X 1 z = 0 := by
  classical
  have hinv : (⟨fun g : G => X.ρ g m, hcont⟩ : C(G, ↥X)) ∈
      (X.resolution'.X 0).ρ.invariants := by
    intro σ
    ext x
    have hval : ∀ y : G, (⟨fun g : G => X.ρ g m, hcont⟩ : C(G, ↥X)) y = X.ρ y m := fun _ => rfl
    simp only [ContRepresentation.coind₁_apply_apply, hval]
    rw [rho_mul_apply X σ⁻¹ x m]
    exact rho_apply_inv X σ _
  set F : ↥((homogeneousCochains X).X 0) := ⟨⟨fun g : G => X.ρ g m, hcont⟩, hinv⟩ with hFdef
  rw [cocycleClass_eq_zero_iff]
  refine ⟨F, ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  ext g l
  have hb : (bdryKer X 1 F).1 = ((homogeneousCochains X).d 0 1).hom F := bdryKer_apply_coe X 1 F
  have h1 : ((bdryKer X 1 F).1).1 g l = X.ρ l m - X.ρ g m := by
    rw [hb, homogeneousCochains_d_zero_one_apply]
    rfl
  have h2 : (z.1).1 g l = X.ρ l m - X.ρ g m := by
    rw [cocycle_apply (cocycles₁_d_eq_zero z), h, h]
    abel
  exact h1.trans h2.symm

end degreeZero

/-! ### Functoriality: restriction of a class, read on cocycles

ADDED 2026-07-28.  Mathlib's `ContinuousCohomology.map φ f n` is built from
`HomologicalComplex.homologyMap`, and `ContCohomology/Basic.lean`'s `cocycleClass` is
built from the concrete quotient `cohomologyIsoQuot`; nothing connected the two, so
"`res^G_N c = 0`" could not be turned into a statement about a cocycle.  The bridge is
`cocycleClass_cyclesIsoKer_hom` — `cocycleClass` IS `homologyπ` in the kernel model —
after which mathlib's own `π_map` and `HomologicalComplex.cyclesMap_i` do the rest. -/

section functoriality

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- `homologyπ` composed with the concrete-cokernel identification is `cokerπ` of the
boundary map into the cycles: `CokernelCofork.π_mapOfIsColimit` for
`HomologicalComplex.homologyIsoCoker`. -/
lemma homologyπ_comp_homologyIsoCoker_hom (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).homologyπ j ≫
      ((homogeneousCochains X).homologyIsoCoker (j - 1) j (CochainComplex.prev_nat j)).hom =
      TopModuleCat.cokerπ ((homogeneousCochains X).toCycles (j - 1) j) := by
  have h := CokernelCofork.π_mapOfIsColimit
    ((homogeneousCochains X).homologyIsCokernel (j - 1) j (CochainComplex.prev_nat j))
    (CokernelCofork.ofπ (TopModuleCat.cokerπ ((homogeneousCochains X).toCycles (j - 1) j))
      (TopModuleCat.comp_cokerπ _))
    (Iso.refl (Arrow.mk ((homogeneousCochains X).toCycles (j - 1) j))).hom
  simp only [Iso.refl_hom, Arrow.id_right, Category.id_comp] at h
  simp only [HomologicalComplex.homologyIsoCoker, CokernelCofork.mapIsoOfIsColimit_hom,
    Iso.refl_hom]
  exact h

/-- The same statement through `cohomologyIsoQuot`, i.e. after transporting the cycles
to the kernel model. -/
lemma homologyπ_comp_cohomologyIsoQuot_hom (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).homologyπ j ≫ (cohomologyIsoQuot X j).hom =
      ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom ≫
        TopModuleCat.cokerπ (bdryKer X j) := by
  rw [cohomologyIsoQuot, Iso.trans_hom, ← Category.assoc,
    homologyπ_comp_homologyIsoCoker_hom, TopModuleCat.cokerπ_cokerCongr_hom]

/-- **`cocycleClass` is `homologyπ` in the kernel model.**  This is the bridge between
`ContCohomology/Basic.lean`'s concrete quotient model and mathlib's functoriality
lemmas, all of which are stated for `ContinuousCohomology.π`. -/
lemma cocycleClass_cyclesIsoKer_hom (X : TopRep k G) (j : ℕ) (w : ↥(cocycles X j)) :
    cocycleClass X j (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom w) =
      π X j w := by
  rw [cocycleClass_apply]
  have h := congr($(homologyπ_comp_cohomologyIsoQuot_hom X j) w)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [← h]
  exact congr($((cohomologyIsoQuot X j).hom_inv_id) _)

variable {X : TopRep k G} {Y : TopRep k H}

/-- **`eval₁` transported along `cochainsMap`**: `eval₁ (f ∘ F ∘ φ) h = f (eval₁ F (φ h))`.
Definitional except for `φ 1 = 1`. -/
lemma eval₁_cochainsMap (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (F : ↥((homogeneousCochains X).X 1)) (h : H) :
    eval₁ Y (((cochainsMap φ f).f 1).hom F) h = f.hom (eval₁ X F (φ h)) := by
  show f.hom (F.1 (φ 1) (φ h)) = f.hom (F.1 1 (φ h))
  rw [map_one]

/-- **Functoriality of `cocycleClass`**, in the "underlying cochain is prescribed" form,
so that no map on the kernel model has to be named in the statement. -/
lemma map_cocycleClass (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) (j : ℕ)
    (z : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1))))
    (z' : ↥(TopModuleCat.ker ((homogeneousCochains Y).d j (j + 1))))
    (hz : z'.1 = ((cochainsMap φ f).f j).hom z.1) :
    map φ f j (cocycleClass X j z) = cocycleClass Y j z' := by
  obtain ⟨w, hw⟩ : ∃ w, ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom w = z :=
    ⟨_, congr($(((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv_hom_id) z)⟩
  subst hw
  rw [cocycleClass_cyclesIsoKer_hom]
  have hpi := congr($(π_map φ f j) w)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hpi
  rw [hpi, ← cocycleClass_cyclesIsoKer_hom Y j (cocyclesMap φ f j w)]
  congr 1
  refine Subtype.ext ?_
  rw [(homogeneousCochains Y).cyclesIsoKer_hom_apply_coe j (j + 1) (by simp)]
  have e2 := congr($(HomologicalComplex.cyclesMap_i (cochainsMap φ f) j) w)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e2
  rw [e2, ← (homogeneousCochains X).cyclesIsoKer_hom_apply_coe j (j + 1) (by simp) w]
  exact hz.symm

/-- **The transported cocycle** `f ∘ z ∘ φ`, in the kernel model.  Well defined because
`cochainsMap` is a chain map. -/
noncomputable def cocyclesMapKer (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) (j : ℕ)
    (z : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    ↥(TopModuleCat.ker ((homogeneousCochains Y).d j (j + 1))) :=
  ⟨((cochainsMap φ f).f j).hom z.1, by
    have h := congr($((cochainsMap φ f).comm j (j + 1)) z.1)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have hz : ((homogeneousCochains X).d j (j + 1)).hom z.1 = 0 := z.2
    show ((homogeneousCochains Y).d j (j + 1)).hom (((cochainsMap φ f).f j).hom z.1) = 0
    rw [h, hz, map_zero]⟩

lemma cocyclesMapKer_coe (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y) (j : ℕ)
    (z : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    (cocyclesMapKer φ f j z).1 = ((cochainsMap φ f).f j).hom z.1 := rfl

/-- **`map φ f j` on a class is the class of the transported cocycle.** -/
lemma map_cocycleClass_cocyclesMapKer (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (j : ℕ) (z : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    map φ f j (cocycleClass X j z) = cocycleClass Y j (cocyclesMapKer φ f j z) :=
  map_cocycleClass φ f j z _ rfl

/-- The inhomogeneous cochain of the transported cocycle. -/
lemma eval₁_cocyclesMapKer (φ : H →ₜ* G) (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (z : ↥(TopModuleCat.ker ((homogeneousCochains X).d 1 (1 + 1)))) (h : H) :
    eval₁ Y (cocyclesMapKer φ f 1 z).1 h = f.hom (eval₁ X z.1 (φ h)) :=
  eval₁_cochainsMap φ f z.1 h

end functoriality

end ContinuousCohomology
