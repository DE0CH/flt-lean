/-
Deformations/RepresentationTheory/GaloisRepTransport.lean — own work for the
Fermat project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Transport of Galois representations along maps of base fields

`GaloisRep.map` (base change of a Galois representation along a field
embedding `f : K →+* L`) and `GaloisRep.charFrob` (the characteristic
polynomial of the arithmetic Frobenius at a finite place) are both
defined through ARBITRARY CHOICES:

* `Field.absoluteGaloisGroup.map f` restricts along an arbitrarily chosen
  embedding `Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ` (`AlgebraicClosure.map`, itself
  `IsAlgClosed.lift`);
* `Field.AbsoluteGaloisGroup.adicArithFrob v` is an arbitrarily chosen
  element of the local Galois group with the arithmetic-Frobenius
  property at the (canonical) maximal ideal of the integral closure of
  `𝒪ᵥ` in `Kᵥᵃˡᵍ`.

Consequently NEITHER `GaloisRep.map` is functorial on the nose, NOR is
`charFrob` visibly independent of the choices. Both defects are
harmless for characteristic polynomials, and this module supplies the
API that makes that precise:

* `Field.absoluteGaloisGroup.exists_conj_map_comp` — functoriality of
  `Γ` up to a single conjugation: the maps `Γ F → Γ K` induced by
  `g ∘ f` and by `f` after `g` differ by conjugation by ONE element
  `τ ∈ Γ K`, independent of the argument;
* `GaloisRep.charFrob_map_comp` — hence `charFrob` IS functorial:
  conjugation does not change characteristic polynomials;
* `GaloisRep.charFrob_map_ringEquiv` — transport along an isomorphism of
  number fields (a sorried leaf: this is the genuinely arithmetic step,
  comparing the two independently chosen Frobenii);
* `GaloisRep.charFrob_map_algEquiv` — the combination, the form
  consumers want: the Frobenius characteristic polynomials of a
  representation read over two `K`-isomorphic number fields agree at
  corresponding places;
* `GaloisRep.exists_finset_isUnramifiedAt_map` — almost-all
  unramifiedness is inherited by restriction to a finite extension (a
  sorried leaf), which is what discharges the unramifiedness hypothesis
  of the transport lemma at all but finitely many places.

The unramifiedness hypothesis in the transport lemma is NOT removable:
at a place where the representation is ramified, `charFrob` genuinely
depends on the choice made by `adicArithFrob` (two arithmetic Frobenii
at the same prime differ by an inertia element), so no choice-free
comparison of the two sides can hold.
-/

@[expose] public section

open IsDedekindDomain
open scoped NumberField

universe u

-- Every field in this module is a number field: `Field.absoluteGaloisGroup.map`
-- and `GaloisRep.map` both carry a `NumberField` hypothesis on their SOURCE
-- field (they are stated in the number-field section of
-- `AbsoluteGaloisGroup.lean`), and `charFrob` needs one on the field the
-- representation lives over.
variable {K L F : Type*} [Field K] [Field L] [Field F]
  [NumberField K] [NumberField L] [NumberField F]
variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Free A M]

/-- The bijection between the finite places of two number fields induced by a
ring isomorphism between them: transport the ring of integers along the
isomorphism (`NumberField.RingOfIntegers.mapRingEquiv`) and pull height-one
primes back along the resulting isomorphism of Dedekind domains
(`RingEquiv.heightOneSpectrum`). -/
noncomputable def NumberField.finitePlaceEquiv (e : L ≃+* F) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) ≃
      HeightOneSpectrum (NumberField.RingOfIntegers F) :=
  (NumberField.RingOfIntegers.mapRingEquiv e).heightOneSpectrum

omit [NumberField F] in
/-- **Functoriality of the absolute Galois group, up to one conjugation**
(PROVEN): `Field.absoluteGaloisGroup.map` is defined through an
arbitrarily chosen embedding of algebraic closures, so it is not
functorial on the nose; but the two maps `Γ F → Γ K` obtained from a
tower `K →+* L →+* F` — restricting along the chosen embedding
`Kᵃˡᵍ → Fᵃˡᵍ`, versus restricting first along `Lᵃˡᵍ → Fᵃˡᵍ` and then
along `Kᵃˡᵍ → Lᵃˡᵍ` — differ by conjugation by a SINGLE element
`τ ∈ Γ K` (independent of the argument): the two composite embeddings
`Kᵃˡᵍ → Fᵃˡᵍ` differ by an automorphism of `Kᵃˡᵍ`.

The hypothesis `Algebra.IsAlgebraic K F` (satisfied by number fields
over a number field, in particular in every application in this
project) is what makes the chosen embedding `Kᵃˡᵍ → Fᵃˡᵍ` an
ISOMORPHISM, which is how `τ` is produced. -/
theorem Field.absoluteGaloisGroup.exists_conj_map_comp
    [Algebra K F] [Algebra.IsAlgebraic K F] (f : K →+* L) (g : L →+* F)
    (hgf : g.comp f = algebraMap K F) :
    ∃ τ : Field.absoluteGaloisGroup K, ∀ σ : Field.absoluteGaloisGroup F,
      Field.absoluteGaloisGroup.map (algebraMap K F) σ =
        τ * Field.absoluteGaloisGroup.map f
          (Field.absoluteGaloisGroup.map g σ) * τ⁻¹ := by
  classical
  -- Every `K`-embedding of `Kᵃˡᵍ` into `Fᵃˡᵍ` is an ISOMORPHISM: `Fᵃˡᵍ` is
  -- algebraic over `K`, hence integral over the image of `Kᵃˡᵍ`, and an
  -- algebraically closed field is not a proper integral subring.
  have key : ∀ j : AlgebraicClosure K →+* AlgebraicClosure F,
      (∀ y : K, j (algebraMap K (AlgebraicClosure K) y)
        = algebraMap K (AlgebraicClosure F) y) → Function.Bijective j := by
    intro j hj
    refine IsAlgClosed.ringHom_bijective_of_isIntegral j fun x => ?_
    refine ⟨(minpoly K x).map (algebraMap K (AlgebraicClosure K)),
      (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _, ?_⟩
    have hcomp : j.comp (algebraMap K (AlgebraicClosure K))
        = algebraMap K (AlgebraicClosure F) := RingHom.ext hj
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def, minpoly.aeval]
  have hjK : Function.Bijective (AlgebraicClosure.map (algebraMap K F)) :=
    key _ fun y => by
      rw [AlgebraicClosure.map_algebraMap, ← IsScalarTower.algebraMap_apply]
  have hcomp : ∀ y : K, (AlgebraicClosure.map g).comp (AlgebraicClosure.map f)
      (algebraMap K (AlgebraicClosure K) y) = algebraMap K (AlgebraicClosure F) y := by
    intro y
    show AlgebraicClosure.map g (AlgebraicClosure.map f
      (algebraMap K (AlgebraicClosure K) y)) = _
    rw [AlgebraicClosure.map_algebraMap, AlgebraicClosure.map_algebraMap,
      show g (f y) = algebraMap K F y from RingHom.congr_fun hgf y,
      ← IsScalarTower.algebraMap_apply]
  have hι : Function.Bijective
      ((AlgebraicClosure.map g).comp (AlgebraicClosure.map f)) := key _ hcomp
  -- the automorphism of `Kᵃˡᵍ` comparing the two composite embeddings
  obtain ⟨τ, hτ⟩ : ∃ τ : Field.absoluteGaloisGroup K, ∀ x : AlgebraicClosure K,
      AlgebraicClosure.map (algebraMap K F) (τ x)
        = AlgebraicClosure.map g (AlgebraicClosure.map f x) := by
    refine ⟨AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective _ hι).trans
      (RingEquiv.ofBijective _ hjK).symm) (fun y => ?_), fun x => ?_⟩
    · show (RingEquiv.ofBijective _ hjK).symm
        ((RingEquiv.ofBijective _ hι) (algebraMap K (AlgebraicClosure K) y)) = _
      rw [RingEquiv.symm_apply_eq]
      show _ = AlgebraicClosure.map (algebraMap K F) _
      rw [AlgebraicClosure.map_algebraMap, ← IsScalarTower.algebraMap_apply]
      exact hcomp y
    · show AlgebraicClosure.map (algebraMap K F) ((RingEquiv.ofBijective _ hjK).symm
        ((RingEquiv.ofBijective _ hι) x)) = _
      show (RingEquiv.ofBijective _ hjK) ((RingEquiv.ofBijective _ hjK).symm
        ((RingEquiv.ofBijective _ hι) x)) = _
      rw [RingEquiv.apply_symm_apply]
      rfl
  have hinv : ∀ x : AlgebraicClosure K, τ (τ⁻¹ x) = x := by
    intro x
    show (τ * τ⁻¹) x = x
    rw [mul_inv_cancel]
    rfl
  refine ⟨τ, fun σ => AlgEquiv.ext fun x => hjK.injective ?_⟩
  calc AlgebraicClosure.map (algebraMap K F)
        (Field.absoluteGaloisGroup.map (algebraMap K F) σ x)
      = σ (AlgebraicClosure.map (algebraMap K F) x) :=
        Field.absoluteGaloisGroup.lift_map _ _ _
    _ = σ (AlgebraicClosure.map (algebraMap K F) (τ (τ⁻¹ x))) := by rw [hinv]
    _ = σ (AlgebraicClosure.map g (AlgebraicClosure.map f (τ⁻¹ x))) := by rw [hτ]
    _ = AlgebraicClosure.map g (Field.absoluteGaloisGroup.map g σ
          (AlgebraicClosure.map f (τ⁻¹ x))) :=
        (Field.absoluteGaloisGroup.lift_map g σ _).symm
    _ = AlgebraicClosure.map g (AlgebraicClosure.map f
          (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ) (τ⁻¹ x))) := by
        rw [Field.absoluteGaloisGroup.lift_map f (Field.absoluteGaloisGroup.map g σ)]
    _ = AlgebraicClosure.map (algebraMap K F)
          (τ (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ) (τ⁻¹ x))) :=
        (hτ _).symm
    _ = AlgebraicClosure.map (algebraMap K F)
          ((τ * Field.absoluteGaloisGroup.map f
            (Field.absoluteGaloisGroup.map g σ) * τ⁻¹) x) := rfl

omit [IsTopologicalRing A] in
/-- **`charFrob` IS functorial along a tower** (PROVEN): although
`GaloisRep.map` is only functorial up to conjugacy
(`Field.absoluteGaloisGroup.exists_conj_map_comp`), the Frobenius
characteristic polynomials do not see the conjugation
(`LinearEquiv.charpoly_conj`), so base changing a representation along
`g ∘ f` and base changing it in two steps give the same `charFrob` at
every finite place. -/
theorem GaloisRep.charFrob_map_comp [Algebra K F] [Algebra.IsAlgebraic K F]
    (ρ : GaloisRep K A M) (f : K →+* L) (g : L →+* F)
    (hgf : g.comp f = algebraMap K F)
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (ρ.map (algebraMap K F)).charFrob w = ((ρ.map f).map g).charFrob w := by
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp f g hgf
  -- the Galois element at which both sides are evaluated
  set x : Field.absoluteGaloisGroup F :=
    Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F))
      (Field.AbsoluteGaloisGroup.adicArithFrob w) with hx
  -- the conjugating linear automorphism
  have hunit : (ρ τ : Module.End A M) * ρ τ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hunit' : (ρ τ⁻¹ : Module.End A M) * ρ τ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  set u : M ≃ₗ[A] M :=
    LinearEquiv.ofLinear (ρ τ) (ρ τ⁻¹) (by ext m; exact congrFun (congrArg _ hunit) m)
      (by ext m; exact congrFun (congrArg _ hunit') m) with hu
  have hLHS : (ρ.map (algebraMap K F)) x =
      u.conj (((ρ.map f).map g) x) := by
    rw [GaloisRep.map_apply, hτ x, map_mul, map_mul]
    ext m
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, hu, LinearEquiv.ofLinear_apply,
      LinearEquiv.ofLinear_symm_apply, Module.End.mul_apply]
    rw [GaloisRep.map_apply, GaloisRep.map_apply]
  show ((ρ.map (algebraMap K F)).toLocal w
      (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly = _
  show ((ρ.map (algebraMap K F)) x).charpoly = _
  rw [hLHS, LinearEquiv.charpoly_conj]
  rfl

/-- **Transport of the Frobenius characteristic polynomials along an
isomorphism of number fields** (sorry node; the missing `charFrob`
transport API — pure formal Galois/arithmetic bookkeeping, no
literature): a ring isomorphism `e : L ≃+* F` of number fields carries
the finite places of `L` bijectively to those of `F`
(`NumberField.finitePlaceEquiv`); for a Galois representation `ρ` of
`Γ L` UNRAMIFIED at `w`, the base change `ρ.map e` (a representation of
`Γ F`) has the same Frobenius characteristic polynomial at `e w` as `ρ`
has at `w`.

Classically this is the statement that `charFrob` is intrinsic: the
Frobenius conjugacy class at an unramified place is transported by any
isomorphism of number fields, and characteristic polynomials are
conjugation-invariant.

WHY IT IS A LEAF: on this pin the comparison is not formally free.
`e` induces an isomorphism of completions `L_w ≃ F_{e w}` and hence, up
to the arbitrary embeddings of algebraic closures, an isomorphism of the
local Galois groups; under it, `adicArithFrob w` is carried to SOME
arithmetic Frobenius at the maximal ideal of the integral closure over
`e w`, while `adicArithFrob (e w)` is the ARBITRARILY CHOSEN one. Two
arithmetic Frobenii at the same prime differ by an element of the
inertia subgroup (`IsArithFrobAt.mul_inv_mem_inertia`), which the
unramifiedness hypothesis kills; the residual discrepancy is a
conjugation, invisible to characteristic polynomials
(`LinearEquiv.charpoly_conj`). Formalizing this requires the
functoriality of `HeightOneSpectrum.adicCompletion` along `e` (a
valuation-preserving isomorphism of completions), which the pin does not
have.

SOUNDNESS AUDIT: the unramifiedness hypothesis is LOAD-BEARING and must
not be dropped — at a ramified place `charFrob` genuinely depends on the
`adicArithFrob` choice, and the statement would be an assertion about
two unrelated choices. With it, the statement is a true theorem of
algebraic number theory, with no vacuity: it applies to every
representation and every place of good reduction. -/
theorem GaloisRep.charFrob_map_ringEquiv
    (ρ : GaloisRep L A M) (e : L ≃+* F)
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : ρ.IsUnramifiedAt w) :
    (ρ.map (e : L →+* F)).charFrob (NumberField.finitePlaceEquiv e w) =
      ρ.charFrob w :=
  sorry

/-- **Transport of `charFrob` along a `K`-isomorphism of number fields**
(PROVEN, the form consumers want): if `L` and `F` are `K`-isomorphic
number fields, then the Frobenius characteristic polynomials of the base
change of `ρ : GaloisRep K A M` to `L` and to `F` agree at corresponding
places, at every place where the base change to `L` is unramified.
Assembled from `GaloisRep.charFrob_map_comp` (the conjugation
bookkeeping) and `GaloisRep.charFrob_map_ringEquiv` (the arithmetic
transport). -/
theorem GaloisRep.charFrob_map_algEquiv
    [Algebra K L] [Algebra K F] [Algebra.IsAlgebraic K F]
    (ρ : GaloisRep K A M) (e : L ≃ₐ[K] F)
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : (ρ.map (algebraMap K L)).IsUnramifiedAt w) :
    (ρ.map (algebraMap K F)).charFrob
        (NumberField.finitePlaceEquiv e.toRingEquiv w) =
      (ρ.map (algebraMap K L)).charFrob w := by
  have hgf : ((e.toRingEquiv : L →+* F)).comp (algebraMap K L) = algebraMap K F := by
    ext k
    exact e.commutes k
  rw [GaloisRep.charFrob_map_comp ρ (algebraMap K L) (e.toRingEquiv : L →+* F) hgf]
  exact GaloisRep.charFrob_map_ringEquiv (ρ.map (algebraMap K L)) e.toRingEquiv w hw

/-- **Almost-everywhere unramifiedness is inherited by base change to a
finite extension** (sorry node; local Galois theory, no literature): if
`ρ` is unramified at every finite place of the number field `K` outside
a finite set `S`, then its base change to a number field `L ⊇ K` is
unramified at every finite place of `L` outside a finite set — namely
outside the (finite) set of places of `L` lying over `S`.

Classically: the local inertia group at a place `w` of `L` maps INTO the
local inertia group at the place `v` of `K` below `w` (an automorphism of
the algebraic closure that is trivial on the residue field over `w` is
trivial on the smaller residue field over `v`), and the kernel of `ρ` is
normal, so the conjugation ambiguity of
`Field.absoluteGaloisGroup.map` is invisible to the kernel containment
that defines `IsUnramifiedAt`.

WHY IT IS A LEAF: this needs the embedding `K_v →+* L_w` of completions
attached to `w | v` and the compatibility of the local inertia subgroups
under it — the local half of the same missing functoriality that
`GaloisRep.charFrob_map_ringEquiv` needs — plus the finiteness of the
set of places of `L` over a finite set of places of `K`.

SOUNDNESS AUDIT: a true theorem of algebraic number theory, with no
hypotheses beyond the ones displayed and no vacuity route (it is applied
below to hardly ramified representations, which are unramified outside
`{2, ℓ}`). -/
theorem GaloisRep.exists_finset_isUnramifiedAt_map [Algebra K L] (ρ : GaloisRep K A M)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v ∉ S, ρ.IsUnramifiedAt v) :
    ∃ T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers L)),
      ∀ w ∉ T, (ρ.map (algebraMap K L)).IsUnramifiedAt w :=
  sorry

end
