/-
Fermat/FLT/Mathlib/RingTheory/SmallExtension.lean — own work for the Fermat
project (not vendored).
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Small extensions of local rings

A surjection of local rings `π : A ↠ B` is a **small extension** when its kernel
is annihilated by the maximal ideal of `A`:

`𝔪_A · ker π = 0`.

This is the basic object of deformation theory: Schlessinger's criteria, Mazur's
tangent-space computation and Böckle's obstruction calculus all proceed by
factoring an arbitrary surjection of Artinian local rings into a chain of small
extensions and solving the lifting problem one step at a time. Every such step
has a square-zero kernel which is a vector space over the residue field, and it
is that vector space in which the obstruction cocycle takes its values.

Nothing of this exists in mathlib, which carries only the generic square-zero
machinery (`RingTheory/Derivation/ToSquareZero.lean`, `TrivSqZeroExt`) and the
formal-smoothness lifting criteria — neither of which mentions the maximal ideal,
and both of which are about `Algebra`s rather than about a surjection of local
rings. It does not exist in the reference project `~/cs/FLT` either (checked
2026-07-27, `grep -rn "SmallExtension\|IsSmallExtension"`).

## Main definitions

* `IsSmallExtension π` — the predicate above, for `π : A →+* B` with `A` local.

## Main results

* `IsSmallExtension.mul_eq_zero_of_mem_maximalIdeal` — the defining annihilation,
  in element form.
* `IsSmallExtension.ker_le_maximalIdeal`, `IsSmallExtension.ker_sq_eq_bot` — the
  kernel is a square-zero ideal inside `𝔪_A`.
* `IsSmallExtension.isTorsionBySet_ker` — the kernel is a module over the residue
  field `A ⧸ 𝔪_A`, which is what makes the obstruction a class in cohomology with
  coefficients in a `k`-vector space rather than merely in an abelian group.
* `isSmallExtension_quotientLift` — **the constructor everything is built from**:
  if `φ : S ↠ R` is a surjection from a local ring and `K` is an ideal with
  `𝔪_S · ker φ ≤ K ≤ ker φ`, then the induced `S ⧸ K ↠ R` is a small extension.
  This is exactly the shape in which small extensions arise from a presentation
  of a deformation ring: the tautological extension `S ⧸ 𝔪_S·ker φ ↠ R` and each
  of its pushouts `S ⧸ K_ψ ↠ R` along a functional `ψ` on the relation space.

## References

* Schlessinger, *Functors of Artin rings*.
* Mazur, *Deforming Galois representations*, §1.6–1.7.
* Böckle, *Presentations of universal deformation rings*.
-/

@[expose] public section

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A]

/-- **A small extension of local rings**: a surjective ring homomorphism whose
kernel is annihilated by the maximal ideal of the source.

The kernel of such a map is automatically square-zero (`ker_sq_eq_bot`) and is a
vector space over the residue field of `A` (`isTorsionBySet_ker`); those two
consequences are what the lifting theory uses, and the single hypothesis
`𝔪_A · ker π = 0` is what makes them both true at once. -/
structure IsSmallExtension (π : A →+* B) : Prop where
  /-- A small extension is in particular a surjection. -/
  surjective : Function.Surjective π
  /-- The maximal ideal of the source annihilates the kernel. -/
  maximalIdeal_mul_ker : IsLocalRing.maximalIdeal A * RingHom.ker π = ⊥

namespace IsSmallExtension

variable {π : A →+* B}

/-- The defining annihilation, in element form. -/
theorem mul_eq_zero_of_mem_maximalIdeal (h : IsSmallExtension π) {x j : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A) (hj : j ∈ RingHom.ker π) : x * j = 0 := by
  have hmem : x * j ∈ IsLocalRing.maximalIdeal A * RingHom.ker π := Ideal.mul_mem_mul hx hj
  rw [h.maximalIdeal_mul_ker] at hmem
  simpa using hmem

/-- The kernel of a small extension onto a nontrivial ring is a proper ideal. -/
theorem ker_ne_top [Nontrivial B] (_h : IsSmallExtension π) : RingHom.ker π ≠ ⊤ := by
  intro htop
  have h1 : (1 : A) ∈ RingHom.ker π := htop ▸ Submodule.mem_top
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- The kernel of a small extension onto a nontrivial ring lies in the maximal
ideal — so the source is a "square-zero thickening" of the target. -/
theorem ker_le_maximalIdeal [Nontrivial B] (h : IsSmallExtension π) :
    RingHom.ker π ≤ IsLocalRing.maximalIdeal A :=
  IsLocalRing.le_maximalIdeal h.ker_ne_top

/-- Any two elements of the kernel of a small extension multiply to zero. -/
theorem mul_eq_zero_of_mem_ker [Nontrivial B] (h : IsSmallExtension π) {x j : A}
    (hx : x ∈ RingHom.ker π) (hj : j ∈ RingHom.ker π) : x * j = 0 :=
  h.mul_eq_zero_of_mem_maximalIdeal (h.ker_le_maximalIdeal hx) hj

/-- **The kernel of a small extension is square-zero.** -/
theorem ker_sq_eq_bot [Nontrivial B] (h : IsSmallExtension π) : RingHom.ker π ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun x hx j hj => ?_
  rw [h.mul_eq_zero_of_mem_ker hx hj]
  exact Ideal.zero_mem _

/-- **The kernel of a small extension is a module over the residue field.** Stated
as the torsion condition `𝔪_A · ker π = 0` on the `A`-module `ker π`, from which
`Module.IsTorsionBySet.module` manufactures the `A ⧸ 𝔪_A`-module structure.

This is the reason the obstruction to lifting along a small extension is a class
in cohomology with coefficients in a vector space over the residue field: the
kernel through which one must lift is such a vector space. -/
theorem isTorsionBySet_ker (h : IsSmallExtension π) :
    Module.IsTorsionBySet A (RingHom.ker π) (IsLocalRing.maximalIdeal A : Set A) := by
  intro j x
  refine Subtype.ext ?_
  exact h.mul_eq_zero_of_mem_maximalIdeal x.2 j.2

end IsSmallExtension

/-! ### Small extensions cut out of a presentation

The way small extensions actually arise: from a surjection `φ : S ↠ R` out of a
local ring, together with an ideal `K` squeezed between `𝔪_S · ker φ` and
`ker φ`. -/

section Quotient

variable {S R : Type*} [CommRing S] [CommRing R] [IsLocalRing S]

/-- The quotient of a local ring by a proper ideal is local. Stated as an
instance keyed on `Nontrivial (S ⧸ K)`, which is the form in which properness is
available at every use site below. -/
instance IsLocalRing.instQuotientOfNontrivial (K : Ideal S) [Nontrivial (S ⧸ K)] :
    IsLocalRing (S ⧸ K) :=
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The reduction map to a proper quotient of a local ring is local. -/
theorem IsLocalRing.isLocalHom_quotientMk (K : Ideal S) [Nontrivial (S ⧸ K)] :
    IsLocalHom (Ideal.Quotient.mk K) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

/-- **The maximal ideal of a proper quotient of a local ring** is the image of the
maximal ideal. (mathlib proves this inline inside
`IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient` and does not
export it.) -/
theorem IsLocalRing.maximalIdeal_quotient (K : Ideal S) [Nontrivial (S ⧸ K)] :
    IsLocalRing.maximalIdeal (S ⧸ K) =
      (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk K) := by
  haveI := IsLocalRing.isLocalHom_quotientMk K
  have hKtop : K ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹Nontrivial (S ⧸ K)›
  refine (?_ : (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk K) = _).symm
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hKtop)]

omit [IsLocalRing S] in
/-- **The kernel of a surjection out of a local ring onto a nontrivial ring is
proper**, hence the quotient by any smaller ideal is nontrivial. -/
theorem Ideal.Quotient.nontrivial_of_le_ker [Nontrivial R] {φ : S →+* R} {K : Ideal S}
    (hK : K ≤ RingHom.ker φ) : Nontrivial (S ⧸ K) := by
  refine Ideal.Quotient.nontrivial_iff.mpr fun htop => ?_
  have h1 : (1 : S) ∈ RingHom.ker φ := hK (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

/-- **The constructor: a squeezed ideal presents a small extension.**

If `φ : S ↠ R` is a surjection out of a local ring and `K` is an ideal with
`𝔪_S · ker φ ≤ K ≤ ker φ`, then the induced surjection `S ⧸ K ↠ R` is a small
extension. Its kernel is `ker φ / K`, which is killed by `𝔪_S` precisely because
`𝔪_S · ker φ` was already thrown away.

This is the shape in which the deformation-theoretic small extensions appear: `S`
is the presenting power series ring, `R` the deformation ring, `K = 𝔪_S · ker φ`
gives the tautological extension whose kernel is the relation space, and
`K = K_ψ` for a functional `ψ` on the relation space gives its pushout along `ψ`,
whose kernel is the line `k`. -/
theorem isSmallExtension_quotientLift [Nontrivial R] {φ : S →+* R}
    (hφ : Function.Surjective φ) {K : Ideal S} (hK : K ≤ RingHom.ker φ)
    (hmK : IsLocalRing.maximalIdeal S * RingHom.ker φ ≤ K) :
    haveI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_of_le_ker hK
    IsSmallExtension (Ideal.Quotient.lift K φ fun _ ha => hK ha) := by
  haveI : Nontrivial (S ⧸ K) := Ideal.Quotient.nontrivial_of_le_ker hK
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hφ b
    exact ⟨Ideal.Quotient.mk K a, rfl⟩
  · have hker : RingHom.ker (Ideal.Quotient.lift K φ fun _ ha => hK ha) =
        (RingHom.ker φ).map (Ideal.Quotient.mk K) := Ideal.ker_quotient_lift φ hK
    rw [IsLocalRing.maximalIdeal_quotient K, hker, ← Ideal.map_mul]
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hmK

end Quotient

/-! ### Functionals on `M ⧸ 𝔪·M` are semilinear over the base

The kernel of a small extension is a vector space over the residue field
`S ⧸ 𝔪_S`, and in practice one transports that structure along an identification
`e : S ⧸ 𝔪_S ≃+* K` of the residue field with a chosen coefficient field — which
is what `Module.compHom … e.symm.toRingHom` does. The one fact needed about the
resulting `K`-module structure is that a `K`-linear map out of it is *semilinear*
over `S`: the `S`-action is the `K`-action through `e ∘ (S ↠ S ⧸ 𝔪_S)`.

This is what makes the annihilator of a functional an IDEAL of `S` rather than
merely an additive subgroup, which is the step by which the pushout of a small
extension along a functional stays inside ordinary ideal theory. -/

section Semilinear

variable {S : Type*} [CommRing S] [IsLocalRing S] {K : Type*} [Field K]
  {M : Type*} [AddCommGroup M] [Module S M] {N : Type*} [AddCommGroup N] [Module K N]

/-- **A `K`-linear map out of `M ⧸ 𝔪_S·M` is `S`-semilinear**, the `S`-action
being the `K`-action pushed through `e ∘ (S ↠ S ⧸ 𝔪_S)`.

The `K`-module structure is the one transported along `e` by `Module.compHom`,
which is how a relation space `ker φ / 𝔪·ker φ` is made into a vector space over
the coefficient field of a deformation problem. -/
theorem apply_smul_of_residueEquiv (e : (S ⧸ IsLocalRing.maximalIdeal S) ≃+* K) :
    letI : Module K (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))) :=
      Module.compHom _ e.symm.toRingHom
    ∀ (ψ : (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))) →ₗ[K] N) (c : S)
      (w : M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))),
      ψ (c • w) = e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) c) • ψ w := by
  letI : Module K (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))) :=
    Module.compHom _ e.symm.toRingHom
  intro ψ c w
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hk : ∀ (a : K) (w' : M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))),
      a • w' = (e.symm a) • w' := fun _ _ => rfl
  have hS : (c • (Submodule.Quotient.mk u :
        M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)))) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) c) • Submodule.Quotient.mk u := rfl
  calc ψ (c • (Submodule.Quotient.mk u :
          M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))))
      = ψ ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) c) •
          (Submodule.Quotient.mk u :
            M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)))) := by rw [hS]
    _ = ψ ((e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) c)) •
          (Submodule.Quotient.mk u :
            M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)))) := by
          rw [hk, e.symm_apply_apply]
    _ = e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) c) •
          ψ (Submodule.Quotient.mk u) := by rw [map_smul]

end Semilinear
