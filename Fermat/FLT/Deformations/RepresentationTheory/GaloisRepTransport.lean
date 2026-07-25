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
* `Field.absoluteGaloisGroup.exists_conj_map_comp'` — the same with no
  algebraicity hypothesis on the tower, which is what makes it usable
  when the top field is a COMPLETION;
* `GaloisRep.charFrob_map_comp` — hence `charFrob` IS functorial:
  conjugation does not change characteristic polynomials;
* `GaloisRep.charFrob_map_ringEquiv` — transport along an isomorphism of
  number fields, reduced to and proven from the arithmetic leaf
  `Field.absoluteGaloisGroup.exists_conj_map_adicArithFrob_ringEquiv`
  (the genuinely arithmetic step, comparing the two independently chosen
  Frobenii);
* `GaloisRep.charFrob_map_algEquiv` — the combination, the form
  consumers want: the Frobenius characteristic polynomials of a
  representation read over two `K`-isomorphic number fields agree at
  corresponding places;
* `GaloisRep.exists_finset_isUnramifiedAt_map` — almost-all
  unramifiedness is inherited by restriction to a finite extension,
  which is what discharges the unramifiedness hypothesis of the
  transport lemma at all but finitely many places; proven from the
  arithmetic leaf
  `Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le`.

The two remaining sorried leaves of this module are exactly those two
arithmetic statements: both need the functoriality of
`HeightOneSpectrum.adicCompletion` (along an isomorphism of number
fields, resp. along `w | v`), which this mathlib pin does not have.
Neither mentions representations any more.

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

omit [NumberField F] in
/-- **Functoriality up to one conjugation, with NO algebraicity
hypothesis** (PROVEN): the general form of
`Field.absoluteGaloisGroup.exists_conj_map_comp`, for an arbitrary
factorisation `h = g ∘ f` of a ring hom of fields. The two maps
`Γ F → Γ K` induced by `h` and by `f` after `g` differ by conjugation by
a single `τ ∈ Γ K`.

WHY THE HYPOTHESIS CAN BE DROPPED: `exists_conj_map_comp` produced `τ`
by showing the chosen embedding `Kᵃˡᵍ → Fᵃˡᵍ` is BIJECTIVE, which needs
`F/K` algebraic. That is more than necessary. Both
`AlgebraicClosure.map h` and `AlgebraicClosure.map g ∘ AlgebraicClosure.map f`
are `K`-algebra embeddings `Kᵃˡᵍ → Fᵃˡᵍ`, and `Kᵃˡᵍ/K` is NORMAL, so
mathlib's `AlgHom.restrictNormal'` restricts the second one along the
first to an automorphism `τ` of `Kᵃˡᵍ` with
`AlgebraicClosure.map h ∘ τ = AlgebraicClosure.map g ∘ AlgebraicClosure.map f`
(`AlgHom.restrictNormal_commutes`); injectivity of `AlgebraicClosure.map h`
— automatic for a ring hom of fields — then finishes the same calculation
as in the special case.

This is what makes the transport lemmas below usable: their intermediate
field is a COMPLETION `Kᵥ`, which is very far from algebraic over `K`. -/
theorem Field.absoluteGaloisGroup.exists_conj_map_comp'
    (f : K →+* L) (g : L →+* F) (h : K →+* F) (hgf : g.comp f = h) :
    ∃ τ : Field.absoluteGaloisGroup K, ∀ σ : Field.absoluteGaloisGroup F,
      Field.absoluteGaloisGroup.map h σ =
        τ * Field.absoluteGaloisGroup.map f
          (Field.absoluteGaloisGroup.map g σ) * τ⁻¹ := by
  classical
  letI : Algebra K F := h.toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure F) :=
    (AlgebraicClosure.map h).toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure F) := by
    refine IsScalarTower.of_algebraMap_eq fun y => ?_
    show algebraMap K (AlgebraicClosure F) y
      = AlgebraicClosure.map h (algebraMap K (AlgebraicClosure K) y)
    rw [AlgebraicClosure.map_algebraMap]
    exact IsScalarTower.algebraMap_apply K F (AlgebraicClosure F) y
  have hcomp : ∀ y : K, (AlgebraicClosure.map g) (AlgebraicClosure.map f
      (algebraMap K (AlgebraicClosure K) y)) = algebraMap K (AlgebraicClosure F) y := by
    intro y
    rw [AlgebraicClosure.map_algebraMap, AlgebraicClosure.map_algebraMap,
      show g (f y) = h y from RingHom.congr_fun hgf y]
    exact (IsScalarTower.algebraMap_apply K F (AlgebraicClosure F) y).symm
  set j₂ : AlgebraicClosure K →ₐ[K] AlgebraicClosure F :=
    { ((AlgebraicClosure.map g).comp (AlgebraicClosure.map f)) with
      commutes' := fun y => hcomp y }
  obtain ⟨τ, hτ⟩ : ∃ τ : Field.absoluteGaloisGroup K, ∀ x : AlgebraicClosure K,
      AlgebraicClosure.map h (τ x)
        = AlgebraicClosure.map g (AlgebraicClosure.map f x) := by
    refine ⟨j₂.restrictNormal' (AlgebraicClosure K), fun x => ?_⟩
    exact AlgHom.restrictNormal_commutes j₂ (AlgebraicClosure K) x
  have hinv : ∀ x : AlgebraicClosure K, τ (τ⁻¹ x) = x := by
    intro x
    show (τ * τ⁻¹) x = x
    rw [mul_inv_cancel]
    rfl
  refine ⟨τ, fun σ => AlgEquiv.ext fun x => (AlgebraicClosure.map h).injective ?_⟩
  calc AlgebraicClosure.map h (Field.absoluteGaloisGroup.map h σ x)
      = σ (AlgebraicClosure.map h x) := Field.absoluteGaloisGroup.lift_map _ _ _
    _ = σ (AlgebraicClosure.map h (τ (τ⁻¹ x))) := by rw [hinv]
    _ = σ (AlgebraicClosure.map g (AlgebraicClosure.map f (τ⁻¹ x))) := by rw [hτ]
    _ = AlgebraicClosure.map g (Field.absoluteGaloisGroup.map g σ
          (AlgebraicClosure.map f (τ⁻¹ x))) :=
        (Field.absoluteGaloisGroup.lift_map g σ _).symm
    _ = AlgebraicClosure.map g (AlgebraicClosure.map f
          (Field.absoluteGaloisGroup.map f
            (Field.absoluteGaloisGroup.map g σ) (τ⁻¹ x))) := by
        rw [Field.absoluteGaloisGroup.lift_map f (Field.absoluteGaloisGroup.map g σ)]
    _ = AlgebraicClosure.map h
          (τ (Field.absoluteGaloisGroup.map f
            (Field.absoluteGaloisGroup.map g σ) (τ⁻¹ x))) := (hτ _).symm
    _ = AlgebraicClosure.map h
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

/-- **The two Frobenii of an isomorphism of number fields differ by
inertia and one conjugation** (sorry leaf; the purely arithmetic core of
`GaloisRep.charFrob_map_ringEquiv`, no representation theory left in
it): reading the arithmetic Frobenius at `e w` back into `Γ L` along the
composite `L →(e) F → F_{e w}` gives the arithmetic Frobenius at `w`
read along `L → L_w`, up to (i) multiplication by ONE inertia element
`ι ∈ localInertiaGroup w` and (ii) conjugation by ONE `τ ∈ Γ L`.

INTENDED PROOF. `e` is valuation-preserving from `w` to `e w` (that is
exactly what `NumberField.finitePlaceEquiv` says: the ideal of `e w` is
the image of the ideal of `w`), so it completes to a ring isomorphism
`ê : L_w ≃+* F_{e w}` with `ê ∘ algebraMap = algebraMap ∘ e` and
`Valued.v ∘ ê = Valued.v` — build it as
`UniformSpace.Completion.mapRingEquiv (WithVal.congr _ _ e) _ _`, whose
two continuity side goals are the valuation identity. Then:

* `algebraMap F F_{e w} ∘ e = ê ∘ algebraMap L L_w` as ring homs
  `L →+* F_{e w}`, so by `Field.absoluteGaloisGroup.exists_conj_map_comp'`
  (applied twice, once to each factorisation — this is where the
  algebraicity-free form is needed, `F_{e w}` being a completion) both
  sides of the goal are conjugates in `Γ L` of
  `Field.absoluteGaloisGroup.map (algebraMap L L_w)` applied to,
  respectively, `Field.absoluteGaloisGroup.map ê (adicArithFrob (e w))`
  and `adicArithFrob w`; the two conjugators combine into the single `τ`.
* `Field.absoluteGaloisGroup.map ê (adicArithFrob (e w))` is again an
  ARITHMETIC FROBENIUS at `𝔪 (IntegralClosure 𝒪_w L_wᵃˡᵍ)`: the chosen
  embedding `L_wᵃˡᵍ → F_{e w}ᵃˡᵍ` is bijective (both are algebraic
  closures of isomorphic fields), it carries `IntegralClosure 𝒪_w` onto
  `IntegralClosure 𝒪_{e w}` and `𝔪` onto `𝔪` because `ê` preserves the
  valuation, and the residue cardinalities agree. Two arithmetic Frobenii
  at the same prime differ by an inertia element
  (`IsArithFrobAt.mul_inv_mem_inertia`), which is `ι`.

Note the statement cannot be split at `Field.absoluteGaloisGroup.map ê`:
that map needs `[NumberField (w.adicCompletion L)]`, which is false —
only the composites out of the number field `L` are expressible.

REFERENCE MATERIAL: the reference project `~/cs/FLT` has the completion
functoriality this needs, in `FLT/DedekindDomain/Completion/BaseChange.lean`
(`adicCompletionSemialgHom`, `valued_adicCompletionSemialgHom`,
`adicCompletionSemialgHom_image_adicCompletionIntegers`); vendoring
requires the pin-drift audit described in `CLAUDE.md`.

SOUNDNESS AUDIT: no hypotheses beyond a ring isomorphism of number
fields and a finite place; nothing is vacuous (`ι` may be taken to be
`1` exactly when the two arbitrary choices happen to agree). Unlike its
consumer this statement needs NO unramifiedness hypothesis — that
hypothesis is what lets the consumer discard `ι`. -/
theorem Field.absoluteGaloisGroup.exists_conj_map_adicArithFrob_ringEquiv
    (e : L ≃+* F) (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ∃ τ : Field.absoluteGaloisGroup L, ∃ ι ∈ localInertiaGroup w,
      Field.absoluteGaloisGroup.map
          ((algebraMap F ((NumberField.finitePlaceEquiv e w).adicCompletion F)).comp
            (e : L →+* F))
          (Field.AbsoluteGaloisGroup.adicArithFrob (NumberField.finitePlaceEquiv e w)) =
        τ * Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L))
          (Field.AbsoluteGaloisGroup.adicArithFrob w * ι) * τ⁻¹ :=
  sorry

omit [IsTopologicalRing A] in
/-- **Transport of the Frobenius characteristic polynomials along an
isomorphism of number fields** (PROVEN from
`Field.absoluteGaloisGroup.exists_conj_map_adicArithFrob_ringEquiv`): a
ring isomorphism `e : L ≃+* F` of number fields carries the finite places
of `L` bijectively to those of `F` (`NumberField.finitePlaceEquiv`); for
a Galois representation `ρ` of `Γ L` UNRAMIFIED at `w`, the base change
`ρ.map e` (a representation of `Γ F`) has the same Frobenius
characteristic polynomial at `e w` as `ρ` has at `w`.

Classically this is the statement that `charFrob` is intrinsic: the
Frobenius conjugacy class at an unramified place is transported by any
isomorphism of number fields, and characteristic polynomials are
conjugation-invariant.

The representation-theoretic half is what is discharged here: the
arithmetic leaf writes the transported Frobenius as
`τ * (Frob_w * ι) * τ⁻¹`; unramifiedness sends `ι` into `ker ρ`, so `ρ`
does not see it, and the conjugation by `τ` becomes conjugation of
`ρ (Frob_w)` by the linear automorphism `ρ τ`, which characteristic
polynomials do not see (`LinearEquiv.charpoly_conj`).

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
      ρ.charFrob w := by
  classical
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp' (e : L →+* F)
    (algebraMap F ((NumberField.finitePlaceEquiv e w).adicCompletion F))
    ((algebraMap F ((NumberField.finitePlaceEquiv e w).adicCompletion F)).comp
      (e : L →+* F)) rfl
  obtain ⟨τ, ι, hι, hmain⟩ :=
    Field.absoluteGaloisGroup.exists_conj_map_adicArithFrob_ringEquiv e w
  obtain ⟨μ, hμ⟩ : ∃ μ : Field.absoluteGaloisGroup L, τ₀⁻¹ * τ = μ := ⟨_, rfl⟩
  -- the inertia discrepancy is killed by the unramifiedness hypothesis
  have hι1 : ρ (Field.absoluteGaloisGroup.map
      (algebraMap L (w.adicCompletion L)) ι) = 1 := by
    have h1 : ρ.toLocal w ι = 1 := hw.localInertiaGroup_le hι
    rwa [GaloisRep.toLocal_apply] at h1
  -- the conjugating linear automorphism
  have hunit : (ρ μ : Module.End A M) * ρ μ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hunit' : (ρ μ⁻¹ : Module.End A M) * ρ μ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  set u : M ≃ₗ[A] M :=
    LinearEquiv.ofLinear (ρ μ) (ρ μ⁻¹) (by ext m; exact congrFun (congrArg _ hunit) m)
      (by ext m; exact congrFun (congrArg _ hunit') m) with hu
  have hLHS : (ρ.map (e : L →+* F)).toLocal (NumberField.finitePlaceEquiv e w)
        (Field.AbsoluteGaloisGroup.adicArithFrob (NumberField.finitePlaceEquiv e w))
      = u.conj (ρ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)) := by
    have hX' : Field.absoluteGaloisGroup.map (e : L →+* F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F ((NumberField.finitePlaceEquiv e w).adicCompletion F))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            (NumberField.finitePlaceEquiv e w)))
        = τ₀⁻¹ * (Field.absoluteGaloisGroup.map
            ((algebraMap F
              ((NumberField.finitePlaceEquiv e w).adicCompletion F)).comp (e : L →+* F))
            (Field.AbsoluteGaloisGroup.adicArithFrob
              (NumberField.finitePlaceEquiv e w))) * τ₀ := by
      rw [hτ₀]
      group
    have hX : Field.absoluteGaloisGroup.map (e : L →+* F)
        (Field.absoluteGaloisGroup.map
          (algebraMap F ((NumberField.finitePlaceEquiv e w).adicCompletion F))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            (NumberField.finitePlaceEquiv e w)))
        = μ * (Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L))
              (Field.AbsoluteGaloisGroup.adicArithFrob w)
            * Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) ι)
          * μ⁻¹ := by
      rw [hX', hmain, map_mul, ← hμ]
      group
    rw [GaloisRep.toLocal_apply, GaloisRep.map_apply, GaloisRep.toLocal_apply, hX,
      map_mul, map_mul, map_mul, hι1, mul_one]
    ext m
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, hu, LinearEquiv.ofLinear_apply,
      LinearEquiv.ofLinear_symm_apply, Module.End.mul_apply]
  show ((ρ.map (e : L →+* F)).toLocal (NumberField.finitePlaceEquiv e w)
      (Field.AbsoluteGaloisGroup.adicArithFrob
        (NumberField.finitePlaceEquiv e w))).charpoly
    = (ρ.toLocal w (Field.AbsoluteGaloisGroup.adicArithFrob w)).charpoly
  rw [hLHS, LinearEquiv.charpoly_conj]

omit [IsTopologicalRing A] in
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

/-- **Local inertia over a finite extension comes, almost everywhere,
from local inertia over a place outside `S`** (sorry leaf; the purely
arithmetic core of `GaloisRep.exists_finset_isUnramifiedAt_map`, no
representation theory left in it): outside a finite set `T` of places of
`L`, every `w` admits a place `v ∉ S` of `K` and ONE conjugator
`τ ∈ Γ K` such that each inertia element at `w`, read into `Γ K` along
`K → L → L_w`, is the `τ`-conjugate of an inertia element at `v` read
into `Γ K` along `K → K_v`.

INTENDED PROOF. Take `T` to be the places of `L` lying over `S` and,
for `w ∉ T`, take `v := w.under (𝓞 K)`, the place below `w`; then
`v ∉ S`. Finiteness of `T` is the statement that
`w ↦ w.under (𝓞 K)` pulls finite sets back to finite sets, i.e.
tends to `cofinite` along `cofinite` (this is `tendsTo_comap_cofinite`
in the reference project, see below). Then:

* `w | v` gives an embedding of completions `φ : K_v →+* L_w` with
  `φ ∘ algebraMap K K_v = algebraMap K L_w`;
* `φ` is local (it maps `𝒪_v` into `𝒪_w` and `𝔪_v` into `𝔪_w`), so the
  induced `Field.absoluteGaloisGroup.map φ : Γ L_w → Γ K_v` carries
  `localInertiaGroup w` into `localInertiaGroup v`: an automorphism
  trivial modulo `𝔪` on `IntegralClosure 𝒪_w L_wᵃˡᵍ` is trivial modulo
  `𝔪` on the smaller `IntegralClosure 𝒪_v K_vᵃˡᵍ`. That gives `κ`;
* `Field.absoluteGaloisGroup.exists_conj_map_comp'` applied to the
  factorisations `algebraMap K L_w = φ ∘ algebraMap K K_v` and
  `algebraMap K L_w = algebraMap L L_w ∘ algebraMap K L` supplies the
  single argument-independent `τ` (again the algebraicity-free form is
  essential: completions are not algebraic over `K`).

As in the `ringEquiv` leaf, the statement is phrased through the
composites out of the number field `K` only: `Γ L_w → Γ K_v` is not
expressible, because `Field.absoluteGaloisGroup.map` demands
`[NumberField]` on the SOURCE field of its ring hom and `K_v` is not one.

REFERENCE MATERIAL: `~/cs/FLT` has both halves —
`FLT/DedekindDomain/Completion/BaseChange.lean` for
`adicCompletionSemialgHom` (the embedding `K_v →ₛₐ L_w` for `w | v`),
`valued_adicCompletionSemialgHom` and
`adicCompletionSemialgHom_image_adicCompletionIntegers` (its locality),
and `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` for
`tendsTo_comap_cofinite` (the finiteness of `T`). Vendoring requires the
pin-drift audit described in `CLAUDE.md`.

SOUNDNESS AUDIT: no hypotheses beyond a finite extension of number
fields and a finite set of places; no vacuity route — the conclusion is
an honest ∀/∃ over all inertia elements at all but finitely many
places. -/
theorem Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le [Algebra K L]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    ∃ T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers L)),
      ∀ w ∉ T, ∃ v ∉ S, ∃ τ : Field.absoluteGaloisGroup K,
        ∀ ι ∈ localInertiaGroup w, ∃ κ ∈ localInertiaGroup v,
          Field.absoluteGaloisGroup.map
              ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) ι =
            τ * Field.absoluteGaloisGroup.map
              (algebraMap K (v.adicCompletion K)) κ * τ⁻¹ :=
  sorry

omit [IsTopologicalRing A] [Module.Finite A M] [Module.Free A M] in
/-- **Almost-everywhere unramifiedness is inherited by base change to a
finite extension** (PROVEN from
`Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le`): if
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

That last step is what is discharged here: the arithmetic leaf writes
the transported inertia element as `τ * κ * τ⁻¹` with `κ` inertia at
`v ∉ S`, and `ρ κ = 1` by `hS`, so `ρ (τ * κ * τ⁻¹) = ρ τ * ρ τ⁻¹ = 1`.

SOUNDNESS AUDIT: a true theorem of algebraic number theory, with no
hypotheses beyond the ones displayed and no vacuity route (it is applied
below to hardly ramified representations, which are unramified outside
`{2, ℓ}`). -/
theorem GaloisRep.exists_finset_isUnramifiedAt_map [Algebra K L] (ρ : GaloisRep K A M)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v ∉ S, ρ.IsUnramifiedAt v) :
    ∃ T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers L)),
      ∀ w ∉ T, (ρ.map (algebraMap K L)).IsUnramifiedAt w := by
  classical
  obtain ⟨T, hT⟩ :=
    Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le (K := K) (L := L) S
  refine ⟨T, fun w hwT => ⟨fun ι hι => ?_⟩⟩
  obtain ⟨v, hv, τ, hτ⟩ := hT w hwT
  obtain ⟨κ, hκ, hmain⟩ := hτ ι hι
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp' (algebraMap K L)
    (algebraMap L (w.adicCompletion L))
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) rfl
  obtain ⟨μ, hμ⟩ : ∃ μ : Field.absoluteGaloisGroup K, τ₀⁻¹ * τ = μ := ⟨_, rfl⟩
  have hker : ρ (Field.absoluteGaloisGroup.map
      (algebraMap K (v.adicCompletion K)) κ) = 1 := by
    have h1 : ρ.toLocal v κ = 1 := (hS v hv).localInertiaGroup_le hκ
    rwa [GaloisRep.toLocal_apply] at h1
  show (ρ.map (algebraMap K L)).toLocal w ι = 1
  have hX : Field.absoluteGaloisGroup.map (algebraMap K L)
      (Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) ι)
      = μ * Field.absoluteGaloisGroup.map
          (algebraMap K (v.adicCompletion K)) κ * μ⁻¹ := by
    have h1 := hτ₀ ι
    rw [hmain] at h1
    rw [← hμ, show τ₀⁻¹ * τ * Field.absoluteGaloisGroup.map
        (algebraMap K (v.adicCompletion K)) κ * (τ₀⁻¹ * τ)⁻¹
      = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map
        (algebraMap K (v.adicCompletion K)) κ * τ⁻¹) * τ₀ from by group, h1]
    group
  rw [GaloisRep.toLocal_apply, GaloisRep.map_apply, hX, map_mul, map_mul, hker,
    mul_one, ← map_mul, mul_inv_cancel, map_one]

end
