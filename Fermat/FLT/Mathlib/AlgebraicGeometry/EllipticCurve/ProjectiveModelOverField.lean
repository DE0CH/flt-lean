/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveModel
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Prime

/-!
# The projective Weierstrass model over an ARBITRARY base field

`Fermat/FLT/ModularCurve/EllipticScheme.lean` proves that the projective Weierstrass model
`Proj (R[X, Y, Z] ⧸ (W))` of an elliptic curve is smooth of relative dimension `1` and
geometrically connected over its base — but only for `R = ℚ`, in `Scheme.{0}`.  This module is
that development at an **arbitrary base field `F : Type u`**, in `Scheme.{u}`:

* `WeierstrassCurve.Projective.OverField.smoothOfRelativeDimension_projToSpec` — smooth of
  relative dimension `1`;
* `WeierstrassCurve.Projective.OverField.geometricallyConnected_projToSpec` — geometrically
  connected.

Both are consumed by `GaloisRepresentation.Modularity.exists_ellipticSchemeOverField`
(`Fermat/FLT/Modularity/MoretBailly.lean`) through
`Fermat.AbelianSchemeStruct.ofMorphisms`, which needs exactly `IsProper`, `Smooth` and
`GeometricallyConnected`.  It is a separate module rather than 2 000 more lines of
`MoretBailly.lean` because elaboration is single-threaded per file.

**STALE RATIONALE CORRECTED, 2026-07-31.**  This paragraph used to say the module lives here
because "`EllipticScheme.lean` is DOWNSTREAM of `MoretBailly.lean` and so cannot be imported
there".  That is FALSE at this commit, in both directions, and the correction matters because
the port that consumes this module was being planned around it.  Computing the two `Fermat.*`
import closures (no module missing from either walk):

* `EllipticScheme.lean` reaches 56 modules and `MoretBailly.lean` is NOT among them;
* `MoretBailly.lean` reaches 170 and `EllipticScheme.lean` is NOT among them.

The two are INCOMPARABLE.  So `MoretBailly.lean` may import `EllipticScheme.lean` — it is
acyclic and would add only 7 modules to its closure — and `EllipticScheme.lean` may import
THIS module, whose whole `Fermat.*` closure is `{ProjectiveModel, GradedAlgebra.Quotient}`.
Both directions are available; the reason to keep this material in its own file is
elaboration time, not the import graph.

## Relation to the `ℚ` development, and the two places it does not simply transfer

Almost everything below is `EllipticScheme.lean`'s proof with `ℚ` replaced by `F` and `Type`
by `Type u`.  The two exceptions are worth recording, because each is a place where the `ℚ`
argument is *unsound* over a general base rather than merely differently spelled:

1. **`hom_ext_spec_rat` is false over a general base field.**  The ℚ file constructs a
   comparison morphism `proj (E ⊗ K) ⟶ proj E ×_{Spec ℚ} Spec K` by `pullback.lift`, whose
   commuting-square obligation it discharges with "a scheme admits at most one morphism to
   `Spec ℚ`".  There is no such statement over `F`.  The repair is to prove the base-change
   square CARTESIAN first (`isPullback_projBaseChangeMap`, which never mentions the
   comparison morphism) and read the isomorphism off `IsPullback.isoPullback`; see the
   section note there.
2. **`not_X_dvd_polynomial` is proved over `ℚ` by an argument that fails in characteristic
   two,** and no argument by evaluation at `F`-points can replace it: over `𝔽₂` with
   `a₃ = 1`, `a₆ = 0` the polynomial `W(0, Y, Z) = YZ(Y + Z)` vanishes at every point of
   `𝔽₂²` while `X ∤ W` remains true.  The repair evaluates in `F[t]` instead, at
   `(X, Y, Z) = (0, t, 1)`, and reads off a COEFFICIENT; see that lemma's docstring.

Everything else — the point at infinity `[0 : 1 : 0]`, primality of the projective
Weierstrass cubic, `Proj` of a graded domain being irreducible, the dehomogenisation
isomorphism `(A_s)₀ ≅ A ⧸ (s - 1)`, base change for `Proj`, and the Jacobian criterion where
`Δ` is consumed — is base-independent, and a good third of it was already written over an
arbitrary commutative ring in the ℚ file.

## Eventual cleanup

`EllipticScheme.lean`'s `isProper_projToSpec`, `smoothOfRelativeDimension_projToSpec` and
`geometricallyConnected_projToSpec` are now instances of statements proved here (and in
`MoretBailly.lean`, for properness); they can collapse to `… (F := ℚ)` applications, which
would delete some 1 800 lines from that module.  That is not done here, but the reason given
for not doing it — "this module is upstream of `MoretBailly.lean`, which is upstream of
`EllipticScheme.lean`" — was WRONG (see the correction above): `MoretBailly.lean` is not
upstream of `EllipticScheme.lean` at all, and this module's entire `Fermat.*` closure is
`{ProjectiveModel, GradedAlgebra.Quotient}`, so `EllipticScheme.lean` can import it today.
The cleanup is available now and is purely subtractive; only properness would still have to
be re-proved or moved, since that one really does live in `MoretBailly.lean`.

## What the group-law port still needs (2026-07-31)

The section at the very bottom of this file adds the two "lies over the base" equations for
`projInfty` and `projNeg` over an arbitrary `[CommRing R]`, which are the fields `he` and `hi`
of `GaloisRepresentation.Modularity.ProjGroupLawOverField`.  What is NOT here, and is the
whole of what `exists_projGroupLawOverField_geomFibreAddEquiv` still wants, is the group law
`m` itself: the port of `Fermat.exists_projAdd`.  The addition polynomials it glues
(`WeierstrassCurve.Projective.addXYZ` in the pin, `add2XYZ` in
`.../EllipticCurve/ProjectiveAddition.lean`) are ALREADY stated over an arbitrary
`[CommRing R]`, so no polynomial-identity work remains at that layer, and
`Fermat.ProjCoords` ALREADY carries its base as an explicit field `base : ℚ →+* Γ(X, ⊤)`.
What is genuinely lost over a general base is the UNIQUENESS of that base —
`ProjCoords.base_eq` is `Subsingleton.elim` for `ℚ →+* A` and `@[ext] ProjCoords.ext` rests on
it — together with `Fermat.hom_ext_spec_rat` itself.  Comment-stripped counts in
`EllipticScheme.lean` at `7080929d`: `hom_ext_spec_rat` 59, `base_eq` 11, `ProjCoords.ext` 14.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open _root_.WeierstrassCurve.Projective
open MvPolynomial

namespace WeierstrassCurve.Projective.OverField

universe u

attribute [local instance] MvPolynomial.gradedAlgebra


section ProjGeometryOverField

variable {K : Type u} [CommRing K]

/-- **Setting `X` and `Z` to zero**: the retraction of `K[X, Y, Z]` onto `K[Y]`, realised
inside `K[X, Y, Z]` itself so that the codomain is visibly a domain. -/
noncomputable def killXZ (K : Type u) [CommRing K] :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![0, X 1, 0]

@[simp] theorem killXZ_X0 : killXZ K (X 0) = 0 := by simp [killXZ]
@[simp] theorem killXZ_X1 : killXZ K (X 1) = X 1 := by simp [killXZ]
@[simp] theorem killXZ_X2 : killXZ K (X 2) = 0 := by simp [killXZ]

/-- On a monomial involving neither `X` nor `Z`, `killXZ` is the identity. -/
theorem killXZ_monomial_of {m : Fin 3 →₀ ℕ} (h0 : m 0 = 0) (h2 : m 2 = 0) (c : K) :
    killXZ K (monomial m c) = monomial m c := by
  have hm : m = Finsupp.single 1 (m 1) := by
    ext i; fin_cases i <;> simp [h0, h2]
  rw [hm, killXZ, aeval_monomial, Finsupp.prod_single_index (by simp)]
  simp [algebraMap_eq, C_mul_X_pow_eq_monomial]

/-- **The ideal `(X, Z)` is exactly the kernel of `killXZ`.**

The inclusion `⊆` is immediate.  For `⊇`, divide `p` by `X` and then the remainder by `Z`
(`MvPolynomial.modMonomial_add_divMonomial_single`): what is left is supported on
monomials with no `X` and no `Z`, hence is fixed by `killXZ`, hence is `0` when `p` is. -/
theorem span_X_Z_eq_ker_killXZ :
    (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K))
      = RingHom.ker (killXZ K) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f (rfl | rfl) <;> simp [SetLike.mem_coe, RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hcoeff : ∀ m : Fin 3 →₀ ℕ, m 0 ≠ 0 ∨ m 2 ≠ 0 → coeff m
        ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1)) = 0 := by
      intro m hm
      rcases hm with h | h
      · by_cases h2 : Finsupp.single (2 : Fin 3) 1 ≤ m
        · exact coeff_modMonomial_of_le _ h2
        · rw [coeff_modMonomial_of_not_le _ h2]
          exact coeff_modMonomial_of_le _
            (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr h)
      · exact coeff_modMonomial_of_le _
          (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr h)
    have hys : killXZ K ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
        (Finsupp.single (2 : Fin 3) 1))
        = (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1) := by
      set s : MvPolynomial (Fin 3) K :=
        (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial (Finsupp.single (2 : Fin 3) 1)
      calc killXZ K s = killXZ K (∑ m ∈ s.support, monomial m (coeff m s)) := by
            rw [← MvPolynomial.as_sum]
        _ = ∑ m ∈ s.support, killXZ K (monomial m (coeff m s)) := by rw [map_sum]
        _ = ∑ m ∈ s.support, monomial m (coeff m s) := by
            refine Finset.sum_congr rfl fun m hm => ?_
            refine killXZ_monomial_of ?_ ?_ _
            · by_contra h; exact (mem_support_iff.mp hm) (hcoeff m (Or.inl h))
            · by_contra h; exact (mem_support_iff.mp hm) (hcoeff m (Or.inr h))
        _ = s := (MvPolynomial.as_sum s).symm
    have h1 := modMonomial_add_divMonomial_single p (0 : Fin 3)
    have h2 := modMonomial_add_divMonomial_single
      (p.modMonomial (Finsupp.single (0 : Fin 3) 1)) (2 : Fin 3)
    have hp0 : (p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
        (Finsupp.single (2 : Fin 3) 1) = 0 := by
      have hpp : killXZ K p = killXZ K ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).modMonomial
          (Finsupp.single (2 : Fin 3) 1)) := by
        conv_lhs => rw [← h1, ← h2]
        simp
      rw [hys, hp] at hpp
      exact hpp.symm
    have hpeq : p = X 2 * ((p.modMonomial (Finsupp.single (0 : Fin 3) 1)).divMonomial
          (Finsupp.single (2 : Fin 3) 1)) + X 0 * (p.divMonomial (Finsupp.single (0 : Fin 3) 1)) := by
      conv_lhs => rw [← h1, ← h2]
      rw [hp0, zero_add]
    rw [hpeq]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- `(X, Z)` is a prime ideal of `K[X, Y, Z]` — the kernel of a map to a domain. -/
theorem isPrime_span_X_Z [IsDomain K] :
    (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)).IsPrime := by
  rw [span_X_Z_eq_ker_killXZ]; exact RingHom.ker_isPrime _

/-- `Y ∉ (X, Z)`: this is what makes the point at infinity a point of `Proj` rather than a
point of the irrelevant locus. -/
theorem X1_notMem_span_X_Z [Nontrivial K] :
    (X 1 : MvPolynomial (Fin 3) K) ∉ (Ideal.span {X (0 : Fin 3), X 2}) := by
  rw [span_X_Z_eq_ker_killXZ, RingHom.mem_ker, killXZ_X1]
  exact X_ne_zero 1

/-- **The projective Weierstrass cubic lies in `(X, Z)`**: every one of its seven terms is
divisible by `X` or by `Z`.  This is exactly the statement that `[0 : 1 : 0]` is on the
curve, and it is what lets `(X̄, Z̄)` be formed in the quotient. -/
theorem projPolynomial_mem_span_X_Z (W : WeierstrassCurve K) :
    polynomial W ∈ (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)) := by
  have h : polynomial W
      = X 0 * (C W.a₁ * X 1 * X 2 - X 0 ^ 2 - C W.a₂ * X 0 * X 2 - C W.a₄ * X 2 ^ 2)
        + X 2 * (X 1 ^ 2 + C W.a₃ * X 1 * X 2 - C W.a₆ * X 2 ^ 2) := by
    rw [WeierstrassCurve.Projective.polynomial]; ring
  rw [h]
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

section PointAtInfinity

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- The homogeneous ideal `(X̄, Z̄)` of the homogeneous coordinate ring `K[X, Y, Z] ⧸ (W)`. -/
noncomputable def infIdeal :
    Ideal (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal W).toIdeal) :=
  Ideal.map (Ideal.Quotient.mk _) (Ideal.span {X (0 : Fin 3), X 2})

theorem ker_le_span_X_Z :
    RingHom.ker (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
      ≤ (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)) := by
  rw [Ideal.mk_ker]
  exact Ideal.span_le.mpr (by simpa using projPolynomial_mem_span_X_Z W)

theorem infIdeal_eq_span :
    infIdeal W = Ideal.span {Ideal.Quotient.mk _ (X (0 : Fin 3)),
      Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal (X 2)} := by
  rw [infIdeal, Ideal.map_span, Set.image_pair]

theorem isPrime_infIdeal : (infIdeal W).IsPrime := by
  haveI : (Ideal.span {X (0 : Fin 3), X 2} : Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    isPrime_span_X_Z
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (ker_le_span_X_Z W)

theorem isHomogeneous_infIdeal : (infIdeal W).IsHomogeneous (projGrading W) := by
  rw [infIdeal_eq_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro x (rfl | rfl)
  · exact ⟨1, HomogeneousIdeal.mk_mem_quotientGrading
      (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _))⟩
  · exact ⟨1, HomogeneousIdeal.mk_mem_quotientGrading
      (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _))⟩

/-- `Ȳ` is not in `(X̄, Z̄)`, so `(X̄, Z̄)` does not contain the irrelevant ideal. -/
theorem mk_X1_notMem_infIdeal :
    Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal (X 1) ∉ infIdeal W := by
  intro h
  have hc : (X 1 : MvPolynomial (Fin 3) K) ∈ Ideal.comap
      (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal) (infIdeal W) := h
  rw [infIdeal, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr (ker_le_span_X_Z W)] at hc
  exact X1_notMem_span_X_Z hc

/-- **The point at infinity `[0 : 1 : 0]`**, as a point of the projective spectrum of the
homogeneous coordinate ring: the homogeneous prime `(X̄, Z̄)`, which is prime because
`K[X, Y, Z] ⧸ (W, X, Z) = K[X, Y, Z] ⧸ (X, Z) ≅ K[Y]`, using that `W ∈ (X, Z)`. -/
noncomputable def pointAtInfinity : ProjectiveSpectrum (projGrading W) where
  asHomogeneousIdeal := ⟨infIdeal W, isHomogeneous_infIdeal W⟩
  isPrime := isPrime_infIdeal W
  not_irrelevant_le := by
    intro h
    refine mk_X1_notMem_infIdeal W (h ?_)
    exact HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (HomogeneousIdeal.mk_mem_quotientGrading
        (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _)))

/-- **The projective Weierstrass model is nonempty** (PROVEN) — this is the `hne` step of
`geometricallyConnected_projToSpec`, over an arbitrary base field. -/
theorem nonempty_proj : Nonempty (proj W) := ⟨pointAtInfinity W⟩

end PointAtInfinity

/-! ### `Proj` of a graded domain is irreducible -/

section GradedDomain

variable {A : Type*} {σ' : Type*} [CommRing A] [SetLike σ' A] [AddSubmonoidClass σ' A]

/-- **`Proj` of a graded domain is an irreducible space**, provided it is nonempty.

This is the projective analogue of `PrimeSpectrum.irreducibleSpace`, and it is absent from
mathlib at this pin — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` contains no
irreducibility or connectedness statement at all.

The proof is the same one line of ideas as the affine case: in a domain the zero ideal is
prime, and it is homogeneous, so it is a POINT of `ProjectiveSpectrum 𝒜` as soon as the
space is nonempty (nonemptiness is what rules out the irrelevant ideal being `⊥`).  It is
then a generic point, because `vanishingIdeal {0} = 0` and `zeroLocus 0` is everything.  A
space with a dense point is irreducible, and an irreducible space is preconnected. -/
theorem irreducibleSpace_projectiveSpectrum (𝒜 : ℕ → σ') [GradedRing 𝒜] [IsDomain A]
    (x₀ : ProjectiveSpectrum 𝒜) : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
  have hbot : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (⊥ : HomogeneousIdeal 𝒜) := fun h =>
    x₀.not_irrelevant_le (h.trans bot_le)
  have hprime : (⊥ : HomogeneousIdeal 𝒜).toIdeal.IsPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot
  let z : ProjectiveSpectrum 𝒜 := ⟨⊥, hprime, hbot⟩
  have hdense : closure ({z} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    simp only [z]
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
  exact isIrreducible_singleton.closure

end GradedDomain

/-! ### The two remaining leaves of `geometricallyConnected_projToSpec` -/

section Leaves

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- **A monic cubic over a domain with no root in the ring is irreducible.**

`Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three` already holds over an
arbitrary `[CommRing R] [IsDomain R]` — it is NOT a field-only statement — so no Gauss
lemma, no fraction field and no integral-closedness argument is needed here.  This wrapper
just packages it with the degree computation. -/
theorem irreducible_monicCubic_of_no_root {A : Type*} [CommRing A] [IsDomain A]
    (c₂ c₁ c₀ : A) (h : ∀ r : A, r ^ 3 + c₂ * r ^ 2 + c₁ * r + c₀ ≠ 0) :
    Irreducible (Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2
      + Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀) := by
  set p : Polynomial A := Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2
      + Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀ with hp
  have hmonic : p.Monic := by rw [hp]; monicity!
  have hdeg : p.natDegree = 3 := by rw [hp]; compute_degree!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot.def] at hr
  exact h r (by simpa [hp] using hr)

/-- **`Z` is prime in `K[Y, Z]`.**  Mathlib has `Polynomial.prime_X` but no `MvPolynomial`
analogue; transporting along `finSuccEquiv` supplies it for the variable of index `0`, and
`renameEquiv` along `Equiv.swap 0 1` moves it to the variable of index `1`. -/
theorem prime_X_one_fin_two : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) K) := by
  have hswap : (X (1 : Fin 2) : MvPolynomial (Fin 2) K)
      = MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1) (X 0) := by
    simp
  rw [hswap, MulEquiv.prime_iff]
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 1)).mp ?_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  exact Polynomial.prime_X

/-- **`Z ∤ Y` in `K[Y, Z]`** — seen by evaluating at `(Y, Z) = (1, 0)`. -/
theorem X_one_not_dvd_X_zero_fin_two :
    ¬ ((X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 0) := by
  rintro ⟨c, hc⟩
  have h := congrArg (MvPolynomial.aeval (S₁ := K) ![(1 : K), 0]) hc
  simp at h

/-- **The projective Weierstrass cubic, read as a cubic in `X` over `K[Y, Z]`.**

`MvPolynomial.finSuccEquiv` splits off the variable of index `0`, which for
`WeierstrassCurve.Projective.polynomial` is exactly `X`; the cubic is then MONIC up to the
global sign, with leading coefficient `-1`.  That is the whole point of choosing this
splitting: no Gauss lemma and no primitivity argument is needed for a monic polynomial. -/
theorem finSuccEquiv_projPolynomial :
    MvPolynomial.finSuccEquiv K 2 (polynomial W)
      = -(Polynomial.X ^ 3
          + Polynomial.C (C W.a₂ * X 1) * Polynomial.X ^ 2
          + Polynomial.C (C W.a₄ * X 1 ^ 2 - C W.a₁ * X 0 * X 1) * Polynomial.X
          + Polynomial.C (C W.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1
              - C W.a₃ * X 0 * X 1 ^ 2)) := by
  have e0 : (MvPolynomial.finSuccEquiv K 2) (X 0 : MvPolynomial (Fin 3) K) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have e1 : (MvPolynomial.finSuccEquiv K 2) (X 1 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 0) := by
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl]
    exact MvPolynomial.finSuccEquiv_X_succ
  have e2 : (MvPolynomial.finSuccEquiv K 2) (X 2 : MvPolynomial (Fin 3) K)
      = Polynomial.C (X 1) := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
    exact MvPolynomial.finSuccEquiv_X_succ
  have eC : ∀ a : K, (MvPolynomial.finSuccEquiv K 2) (C a) = Polynomial.C (C a) := by
    intro a; simp [MvPolynomial.finSuccEquiv_apply]
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow, e0, e1, e2, eC]
  ring

/-- **The projective Weierstrass cubic is prime in `K[X, Y, Z]`** (PROVEN).

This is all that was left of the `hpre` step: given it, the homogeneous coordinate ring is a
domain and `irreducibleSpace_projectiveSpectrum` finishes the job.  It carries NO
ellipticity hypothesis, and should not: the Weierstrass cubic is irreducible over EVERY
field, singular ones included.

## The route actually taken, and why it is short

An earlier docstring here recorded this leaf as needing two pieces of missing mathlib —
homogenisation of a bivariate polynomial into a trivariate one, and the fact that a factor
of a homogeneous element of a graded domain is homogeneous — and proposed to descend from
mathlib's AFFINE `WeierstrassCurve.Affine.irreducible_polynomial` by dehomogenising at
`Z = 1`.  **Neither piece is needed, and neither is the affine statement.**  The graded
machinery only ever enters if one insists on factoring a HOMOGENEOUS polynomial as such;
reading `W` as an ordinary cubic in ONE distinguished variable avoids all of it:

1. `MvPolynomial.finSuccEquiv K 2` presents `K[X, Y, Z]` as `(K[Y, Z])[X]`, and under it
   `W` becomes `-q` with `q` MONIC of degree `3` (`finSuccEquiv_projPolynomial`).  The
   index-`0` variable of `WeierstrassCurve.Projective.polynomial` is `X`, and `W` contains
   `-X ^ 3`, so this splitting — and only this one — makes the leading coefficient a unit.
2. Monic + degree `3` reduces irreducibility to the absence of a ROOT in `K[Y, Z]`, by
   `Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three`, which holds over any
   `[IsDomain A]` and not merely over a field.  So there is no Gauss lemma, no fraction
   field, and no integral-closedness step anywhere in this proof.
3. There is no root: if `q(r) = 0` then reducing mod `Z` gives `r ³ ≡ 0`, so `Z ∣ r` since
   `Z` is prime (`prime_X_one_fin_two`); writing `r = Z s` and cancelling one `Z` leaves
   `Y ² = Z · (…)`, so `Z ∣ Y ²`, so `Z ∣ Y` — and `Z ∤ Y`
   (`X_one_not_dvd_X_zero_fin_two`).
4. `MvPolynomial (Fin 3) K` is a UFD, so irreducible gives prime. -/
theorem prime_projPolynomial : Prime (polynomial W) := by
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)).mp ?_
  rw [finSuccEquiv_projPolynomial W]
  refine Prime.neg ?_
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine irreducible_monicCubic_of_no_root _ _ _ ?_
  intro r hr
  have hz : Prime (X (1 : Fin 2) : MvPolynomial (Fin 2) K) := prime_X_one_fin_two
  have h1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ r ^ 3 := by
    refine ⟨-(C W.a₂ * r ^ 2 + (C W.a₄ * X 1 - C W.a₁ * X 0) * r
      + (C W.a₆ * X 1 ^ 2 - X 0 ^ 2 - C W.a₃ * X 0 * X 1)), ?_⟩
    linear_combination hr
  obtain ⟨s, rfl⟩ := hz.dvd_of_dvd_pow h1
  have hA : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) *
      (X 1 ^ 2 * s ^ 3 + C W.a₂ * X 1 ^ 2 * s ^ 2 + C W.a₄ * X 1 ^ 2 * s
        - C W.a₁ * X 0 * X 1 * s + C W.a₆ * X 1 ^ 2 - X 0 ^ 2 - C W.a₃ * X 0 * X 1)
      = X 1 * 0 := by
    linear_combination hr
  have hA0 := mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := K) (1 : Fin 2)) hA
  have h2 : (X (1 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 0 ^ 2 :=
    ⟨X 1 * s ^ 3 + C W.a₂ * X 1 * s ^ 2 + C W.a₄ * X 1 * s - C W.a₁ * X 0 * s
      + C W.a₆ * X 1 - C W.a₃ * X 0, by linear_combination -hA0⟩
  exact X_one_not_dvd_X_zero_fin_two (hz.dvd_of_dvd_pow h2)

/-- The homogeneous coordinate ring of the projective model is a domain (PROVEN) — the
content of `hpre`, modulo the general `Proj`-of-a-graded-domain statement. -/
theorem isDomain_projCoordinateRing :
    IsDomain (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal W).toIdeal) := by
  haveI : ((polynomialHomogeneousIdeal W).toIdeal).IsPrime := by
    show (Ideal.span {polynomial W}).IsPrime
    rw [Ideal.span_singleton_prime (prime_projPolynomial W).ne_zero]
    exact prime_projPolynomial W
  exact Ideal.Quotient.isDomain _

/-- **The projective Weierstrass model is preconnected** (PROVEN) — the `hpre` step of
`geometricallyConnected_projToSpec`, over an arbitrary base field, with no remaining
leaf.  `prime_projPolynomial`, which was the last one, is proven above. -/
theorem preconnectedSpace_proj : PreconnectedSpace (proj W) := by
  haveI := isDomain_projCoordinateRing W
  haveI := irreducibleSpace_projectiveSpectrum (projGrading W) (pointAtInfinity W)
  show PreconnectedSpace (ProjectiveSpectrum (projGrading W))
  infer_instance

end Leaves

/-- The image of the `i`-th homogeneous coordinate in the homogeneous coordinate ring.

(Hoisted above `exists_projCoordsOpenCover` on 2026-07-28: the chart development below
needs it, and it used to sit in the "Dehomogenisation" section some 2000 lines later.) -/
noncomputable abbrev projCoord {R : Type u} [CommRing R] (E : WeierstrassCurve R) (i : Fin 3) :
    MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal E).toIdeal :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

section BaseChange

variable {F : Type u} [Field F] (E : WeierstrassCurve F) (K : Type u) [Field K] [Algebra F K]

/-- Base change of the projective Weierstrass polynomial, `W_K = map (algebraMap F K) W`. -/
theorem polynomial_baseChange :
    polynomial (E.baseChange K) = MvPolynomial.map (algebraMap F K) (polynomial E) :=
  WeierstrassCurve.Projective.map_polynomial (W' := E) (f := algebraMap F K)

/-- Base change carries the ideal `(W)` into `(W_K)`, so it descends to the quotients. -/
theorem map_mem_polynomialHomogeneousIdeal_baseChange
    {a : MvPolynomial (Fin 3) F} (ha : a ∈ (polynomialHomogeneousIdeal E).toIdeal) :
    MvPolynomial.map (algebraMap F K) a
      ∈ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal := by
  have h : (polynomialHomogeneousIdeal E).toIdeal = Ideal.span {polynomial E} := rfl
  have h' : (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal
      = Ideal.span {polynomial (E.baseChange K)} := rfl
  rw [h, Ideal.mem_span_singleton] at ha
  rw [h', Ideal.mem_span_singleton]
  obtain ⟨c, rfl⟩ := ha
  exact ⟨MvPolynomial.map (algebraMap F K) c, by
    rw [map_mul, polynomial_baseChange, mul_comm]⟩

/-- **Base change on the homogeneous coordinate rings**, `F[X, Y, Z] ⧸ (W) → K[X, Y, Z] ⧸ (W_K)`. -/
noncomputable def projBaseChangeQuot :
    (MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal) →+*
      (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (algebraMap F K)))
    fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2
      (map_mem_polynomialHomogeneousIdeal_baseChange E K ha)

@[simp] theorem projBaseChangeQuot_mk (p : MvPolynomial (Fin 3) F) :
    projBaseChangeQuot E K (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap F K) p) := rfl

/-- **Base change as a GRADED ring hom** of homogeneous coordinate rings — the input
`Proj.map` consumes.  Degrees are preserved because `MvPolynomial.map` preserves
homogeneity (`MvPolynomial.IsHomogeneous.map`). -/
noncomputable def projBaseChangeGradedHom :
    projGrading E →+*ᵍ projGrading (E.baseChange K) where
  __ := projBaseChangeQuot E K
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hx
    exact HomogeneousIdeal.mem_quotientGrading.mpr
      ⟨MvPolynomial.map (algebraMap F K) a,
        mem_homogeneousSubmodule _ _ |>.mpr
          ((mem_homogeneousSubmodule _ _ |>.mp ha).map _), rfl⟩

@[simp] theorem projBaseChangeGradedHom_apply
    (a : MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal) :
    projBaseChangeGradedHom E K a = projBaseChangeQuot E K a := rfl

/-- **The hypothesis `Proj.map` demands**: the irrelevant ideal downstairs is contained in
the ideal generated by the image of the irrelevant ideal upstairs.

A positive-degree homogeneous polynomial over `K` has every monomial of positive total
degree, hence lies in the ideal of the variables (`MvPolynomial.mem_pow_idealOfVars_iff'`
at exponent `1`), and each variable is the image of the corresponding variable over `F`. -/
theorem irrelevant_le_map_projBaseChangeGradedHom :
    HomogeneousIdeal.irrelevant (projGrading (E.baseChange K)) ≤
      (HomogeneousIdeal.irrelevant (projGrading E)).map (projBaseChangeGradedHom E K) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp ha
  have hp' : p.IsHomogeneous i := mem_homogeneousSubmodule _ _ |>.mp hp
  have hspan : p ∈ MvPolynomial.idealOfVars (Fin 3) K := by
    rw [show MvPolynomial.idealOfVars (Fin 3) K = MvPolynomial.idealOfVars (Fin 3) K ^ 1 from
      (pow_one _).symm, MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    exact hp'.coeff_eq_zero (by omega)
  have hle : MvPolynomial.idealOfVars (Fin 3) K ≤
      Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal)
        ((HomogeneousIdeal.irrelevant (projGrading E)).map
          (projBaseChangeGradedHom E K)).toIdeal := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hXmem : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (X j))
        ∈ HomogeneousIdeal.irrelevant (projGrading E) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
        (HomogeneousIdeal.mk_mem_quotientGrading
          (mem_homogeneousSubmodule _ _ |>.mpr (isHomogeneous_X _ _)))
    have h2 := Ideal.mem_map_of_mem (projBaseChangeGradedHom E K) hXmem
    simpa using h2
  exact hle hspan

/-- **The base-change morphism of projective models** `proj (E_K) ⟶ proj E`, namely `Proj`
applied to the graded base-change hom. -/
noncomputable def projBaseChangeMap : proj (E.baseChange K) ⟶ proj E :=
  Proj.map (projBaseChangeGradedHom E K) (irrelevant_le_map_projBaseChangeGradedHom E K)

/-! #### `hbc`, part 2: the base-change square is CARTESIAN

**THE ONE STRUCTURAL DIFFERENCE FROM THE `ℚ` DEVELOPMENT.**  At `F = ℚ` the module
`EllipticScheme.lean` first builds a comparison morphism `projBaseChangeHom` into the
pullback and then proves it is an isomorphism; the commuting square that `pullback.lift`
demands is FREE there, because `hom_ext_spec_rat` says a scheme admits at most one morphism
to `Spec ℚ`.  Over a general base field that lemma is FALSE and the square is a real
obligation — so the comparison morphism cannot be written down first.

The fix costs nothing: `isPullback_projBaseChangeMap` below proves the square is CARTESIAN
without ever mentioning the comparison morphism, and an `IsPullback` carries its own
commuting square (`.w`) together with `IsPullback.isoPullback`.  So the ℚ file's
`projBaseChangeHom` and `isIso_projBaseChangeHom` are simply *not needed here*: they are
replaced by `(isPullback_projBaseChangeMap E K).isoPullback`, which is the same morphism
with its commutation supplied rather than assumed.

The argument for the square itself is the ℚ one verbatim.  It has two halves, and each is a
piece of mathlib infrastructure that did not exist at this pin:

* **Geometric half.**  `Proj.map` is *cartesian on the standard charts*
  (`isPullback_awayι_map`): `Proj.map_preimage_basicOpen` says `D₊(φ s)` is exactly the
  preimage of `D₊(s)` ON THE NOSE, and `Proj.awayι_comp_map` gives the commuting square, so
  `IsOpenImmersion.isPullback` applies verbatim.  Feeding those charts to
  `Scheme.isPullback_of_openCover` reduces the whole base-change square to one AFFINE square
  per chart, and `Proj.awayι_toSpecZero` turns each chart's structure morphism into a
  `Spec.map` — so the affine square is `Spec` of a ring square, and
  `isPullback_SpecMap_of_isPushout` closes it from a pushout of rings.
* **Ring half.**  The residual ring statement is `Away 𝒜 s ⊗_F K ≅ Away ℬ (φ s)`.  It is
  proven by DEHOMOGENISING: for `s` of degree ONE there is a canonical isomorphism
  `(A_s)₀ ≅ A ⧸ (s - 1)` (`awayDehomEquiv`), natural in the graded ring
  (`awayToDehom_comp_awayMap`), and on the right-hand side base change is elementary —
  a quotient of a polynomial ring, handled by `isPushout_quotientMk` (quotients commute with
  base change) pasted onto mathlib's `Algebra.IsPushout R S (MvPolynomial σ R)
  (MvPolynomial σ S)`.  No graded base-change theory is needed anywhere.

The degree-one hypothesis is not a restriction here: the cover used is `D₊(x₀), D₊(x₁),
D₊(x₂)`, and the coordinates are homogeneous of degree one. -/

/-- Transport of `IsPullback` along an isomorphism of the apex. -/
theorem isPullback_of_isoApex {C : Type*} [Category C] {P P' X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Limits.HasPullback f g] (e : P' ≅ P) :
    IsPullback (e.hom ≫ fst) (e.hom ≫ snd) f g :=
  IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, h.w]⟩ (e ≪≫ h.isoPullback)
    (by simp) (by simp)

/-- The structure map `R → (A_t)₀` of a standard chart of `proj W`. -/
noncomputable def awayBaseHom {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    R →+* HomogeneousLocalization.Away (projGrading W) t :=
  (HomogeneousLocalization.fromZeroRingHom (projGrading W) (Submonoid.powers t)).comp
    (algebraMap R (projGrading W 0))

/-- **The chart composite `Spec (A_t)₀ ⟶ proj W ⟶ Spec R` is `Spec.map` of `awayBaseHom`**,
over an arbitrary base ring and for an arbitrary homogeneous `t` of positive degree.  This is
the base-free version of `awayι_projToSpec_eq_specMap`, needed because the base-change square
has `proj E` over `F` on one side and `proj (E_K)` over `K` on the other. -/
theorem awayι_projToSpec_eq_specMap' {R : Type u} [CommRing R] (W : WeierstrassCurve R) {m : ℕ}
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)
    (ht : t ∈ projGrading W m) (hm : 0 < m) :
    Proj.awayι (projGrading W) t ht hm ≫ projToSpec W
      = Spec.map (CommRingCat.ofHom (awayBaseHom W t)) := by
  show Proj.awayι (projGrading W) t ht hm ≫
      (Proj.toSpecZero (projGrading W) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (projGrading W 0)))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- **The standard chart square of `Proj.map` is CARTESIAN** — a general statement about
`Proj` that mathlib does not have.

`Proj.map_preimage_basicOpen` gives `map f ⁻¹ᵁ D₊(s) = D₊(f s)` on the nose, so the ranges of
the two chart immersions match, and `Proj.awayι_comp_map` is the commuting square;
`IsOpenImmersion.isPullback` then says a commuting square of open immersions with matching
preimage IS a pullback. -/
theorem isPullback_awayι_map {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
    [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) (hfs : f s ∈ ℬ i) :
    IsPullback (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)))
      (Proj.awayι ℬ (f s) hfs hi) (Proj.awayι 𝒜 s hs hi) (Proj.map f hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map f hf hi s hs)
    (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen])

/-- The three homogeneous coordinates have degree one. -/
theorem projCoord_mem_grading {R : Type u} [CommRing R] (W : WeierstrassCurve R) (i : Fin 3) :
    projCoord W i ∈ projGrading W 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i))

/-- The three coordinates span the irrelevant ideal, so `D₊(x₀), D₊(x₁), D₊(x₂)` cover
`proj W`.  This is the covering condition of `smoothOfRelativeDimension_projToSpec`, extracted
as a named lemma over an arbitrary base ring. -/
theorem irrelevant_le_span_projCoord {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (projGrading W)).toIdeal
      ≤ Ideal.span (Set.range (projCoord W)) := by
  classical
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi z hz
  obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hz
  have hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hm0 : m = 0 := by
      ext j; exact hcon j (Set.mem_univ j)
    have hdeg := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
      (MvPolynomial.mem_support_iff.mp hm)
    rw [hm0] at hdeg
    simp at hdeg
    omega
  have hle : Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3)))
      ≤ Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
        (Ideal.span (Set.range (projCoord W))) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hle hp'

/-! #### Dehomogenisation at a degree-one element: `(A_s)₀ ≅ A ⧸ (s - 1)`

This is the standard "set `s = 1`" isomorphism for a graded ring `A` and `s ∈ 𝒜 1`, and it is
absent from mathlib in every form.  It is what converts the graded base-change question into an
ungraded one.

Both maps are constructed explicitly and the two round trips are checked on generators, so no
graded induction on the degree is needed anywhere:

* `awayToDehom` is `IsLocalization.lift` of `A ↠ A ⧸ (s - 1)` (which inverts `s`, since `s ↦ 1`),
  restricted to the degree-zero part;
* `dehomToAway` is `DirectSum.toSemiring` applied to `a ↦ a / s^d` on each graded piece — this
  IS a ring hom because `1 / s^0 = 1` and `(ab) / s^{i+j} = (a/s^i)(b/s^j)`. -/

section Dehom

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {s : A} (hs : s ∈ 𝒜 1)

/-- `s` becomes `1` in `A ⧸ (s - 1)`. -/
theorem mk_self_dehom : Ideal.Quotient.mk (Ideal.span {s - 1}) s = 1 := by
  have h : Ideal.Quotient.mk (Ideal.span {s - 1}) (s - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

/-- Every power of `s` is a unit in `A ⧸ (s - 1)` — indeed it is `1`. -/
theorem isUnit_mk_dehom (y : Submonoid.powers s) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {s - 1}) y) := by
  obtain ⟨n, hn⟩ := y.2
  rw [show ((y : A)) = s ^ n from hn.symm, map_pow, mk_self_dehom, one_pow]
  exact isUnit_one

/-- **Dehomogenisation**, `(A_s)₀ → A ⧸ (s - 1)`: the fraction `a / sⁿ` goes to `a`. -/
noncomputable def awayToDehom :
    HomogeneousLocalization.Away 𝒜 s →+* A ⧸ Ideal.span {s - 1} :=
  (IsLocalization.lift (M := Submonoid.powers s) (S := Localization.Away s)
      (g := Ideal.Quotient.mk (Ideal.span {s - 1})) (isUnit_mk_dehom (s := s))).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 s) (Localization.Away s))

@[simp] theorem awayToDehom_apply (x : HomogeneousLocalization.Away 𝒜 s) {n : ℕ} {a : A}
    (hx : x.val = Localization.mk a (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) :
    awayToDehom 𝒜 x = Ideal.Quotient.mk _ a := by
  show IsLocalization.lift (isUnit_mk_dehom (s := s)) x.val = _
  rw [hx, Localization.mk_eq_mk', IsLocalization.lift_mk'_spec]
  rw [map_pow, mk_self_dehom, one_pow, one_mul]

/-- The degree-zero fraction `a / sⁱ` attached to a homogeneous `a` of degree `i`. -/
noncomputable def homFrac (i : ℕ) (a : 𝒜 i) : HomogeneousLocalization.Away 𝒜 s :=
  HomogeneousLocalization.mk
    ⟨i, a, ⟨s ^ i, by simpa using SetLike.pow_mem_graded i hs⟩, ⟨i, rfl⟩⟩

@[simp] theorem val_homFrac (i : ℕ) (a : 𝒜 i) :
    (homFrac 𝒜 hs i a).val = Localization.mk (a : A) (⟨s ^ i, i, rfl⟩ : Submonoid.powers s) :=
  rfl

/-- `a ↦ a / sⁱ` is additive on the degree-`i` part. -/
noncomputable def homFracHom (i : ℕ) : 𝒜 i →+ HomogeneousLocalization.Away 𝒜 s where
  toFun a := homFrac 𝒜 hs i a
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [val_homFrac, HomogeneousLocalization.val_zero]
    simp [Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add, val_homFrac, val_homFrac, val_homFrac,
      Localization.add_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [AddMemClass.coe_add, Submonoid.coe_mul]; ring⟩

theorem homFracHom_apply (i : ℕ) (a : 𝒜 i) : homFracHom 𝒜 hs i a = homFrac 𝒜 hs i a := rfl

/-- **The dehomogenisation section** `A → (A_s)₀`, `a ↦ Σ_d a_d / s^d`.

`DirectSum.toSemiring` builds it as a RING hom out of the degreewise maps, the two side
conditions being `1 / s^0 = 1` and `(a b) / s^{i+j} = (a / s^i) (b / s^j)`. -/
noncomputable def dehomToAway : A →+* HomogeneousLocalization.Away 𝒜 s :=
  (DirectSum.toSemiring (homFracHom 𝒜 hs)
    (by
      apply HomogeneousLocalization.val_injective
      rw [homFracHom_apply, val_homFrac, HomogeneousLocalization.val_one,
        ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩)
    (by
      intro i j ai aj
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mul, homFracHom_apply, homFracHom_apply, homFracHom_apply,
        val_homFrac, val_homFrac, val_homFrac, Localization.mk_mul]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp only [SetLike.coe_gMul, Submonoid.coe_mul, pow_add]; try ring⟩)).comp
    (DirectSum.decomposeRingEquiv 𝒜).toRingHom

theorem dehomToAway_of_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    dehomToAway 𝒜 hs a = homFrac 𝒜 hs i ⟨a, ha⟩ := by
  unfold dehomToAway
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    show (DirectSum.decomposeRingEquiv 𝒜) a = DirectSum.decompose 𝒜 a from rfl,
    DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toSemiring_of]
  rfl

theorem dehomToAway_self : dehomToAway 𝒜 hs s = 1 := by
  rw [dehomToAway_of_mem 𝒜 hs hs]
  apply HomogeneousLocalization.val_injective
  rw [val_homFrac, HomogeneousLocalization.val_one, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem awayToDehom_dehomToAway (a : A) :
    awayToDehom 𝒜 (dehomToAway 𝒜 hs a) = Ideal.Quotient.mk _ a := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dehomToAway_of_mem 𝒜 hs (DirectSum.decompose 𝒜 a i).2]
  exact awayToDehom_apply 𝒜 _ (val_homFrac 𝒜 hs i _)

/-- The dehomogenisation section kills `s - 1`, so it descends to the quotient. -/
noncomputable def dehomQuotToAway :
    A ⧸ Ideal.span {s - 1} →+* HomogeneousLocalization.Away 𝒜 s :=
  Ideal.Quotient.lift _ (dehomToAway 𝒜 hs) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_sub, dehomToAway_self, map_one, sub_self, mul_zero])

@[simp] theorem dehomQuotToAway_mk (a : A) :
    dehomQuotToAway 𝒜 hs (Ideal.Quotient.mk _ a) = dehomToAway 𝒜 hs a := rfl

/-- **The dehomogenisation isomorphism** `(A_s)₀ ≅ A ⧸ (s - 1)` for `s` homogeneous of degree
one.  Absent from mathlib; it is the whole reason the base-change residue is elementary. -/
noncomputable def awayDehomEquiv :
    HomogeneousLocalization.Away 𝒜 s ≃+* A ⧸ Ideal.span {s - 1} :=
  RingEquiv.ofRingHom (awayToDehom 𝒜) (dehomQuotToAway 𝒜 hs)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, RingHom.id_apply, dehomQuotToAway_mk]
      exact awayToDehom_dehomToAway 𝒜 hs a))
    (RingHom.ext fun x => by
      obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs x
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [awayToDehom_apply 𝒜 _ (HomogeneousLocalization.Away.val_mk 𝒜 n hs a ha),
        dehomQuotToAway_mk, dehomToAway_of_mem 𝒜 hs ha]
      apply HomogeneousLocalization.val_injective
      rw [val_homFrac, HomogeneousLocalization.Away.val_mk]
      simp)

@[simp] theorem awayDehomEquiv_apply (x : HomogeneousLocalization.Away 𝒜 s) :
    awayDehomEquiv 𝒜 hs x = awayToDehom 𝒜 x := rfl

end Dehom

section DehomMap

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The map on dehomogenisations induced by a graded ring hom. -/
noncomputable def dehomMap (φ : 𝒜 →+*ᵍ ℬ) (s : A) :
    A ⧸ Ideal.span {s - 1} →+* B ⧸ Ideal.span {φ s - 1} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (φ : A →+* B)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    show Ideal.Quotient.mk _ (φ (c * (s - 1))) = 0
    rw [map_mul, map_sub, map_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
@[simp] theorem dehomMap_mk (φ : 𝒜 →+*ᵍ ℬ) (s a : A) :
    dehomMap φ s (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := rfl

/-- **Naturality of dehomogenisation** in the graded ring: `(A_s)₀ ≅ A ⧸ (s - 1)` intertwines
`HomogeneousLocalization.Away.map` with `dehomMap`. -/
theorem awayToDehom_comp_awayMap (φ : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 1) :
    (awayToDehom ℬ).comp (HomogeneousLocalization.Away.map φ s)
      = (dehomMap φ s).comp (awayToDehom 𝒜) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs x
  rw [RingHom.comp_apply, RingHom.comp_apply,
    HomogeneousLocalization.Away.map_mk φ s hs n a ha,
    awayToDehom_apply 𝒜 _ (HomogeneousLocalization.Away.val_mk 𝒜 n hs a ha),
    awayToDehom_apply ℬ _ (HomogeneousLocalization.Away.val_mk ℬ n (φ.map_mem hs) (φ a)
      (φ.map_mem ha)),
    dehomMap_mk]
  rfl

end DehomMap

/-- The chart base map `R → (A_t)₀`, dehomogenised, is the structure map of `A ⧸ (t - 1)`. -/
theorem awayToDehom_comp_awayBaseHom {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (t : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) :
    (awayToDehom (projGrading W)).comp (awayBaseHom W t)
      = (Ideal.Quotient.mk (Ideal.span {t - 1})).comp
        (algebraMap R (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)) :=
  RingHom.ext fun r =>
    awayToDehom_apply (projGrading W) _ (n := 0)
      (a := algebraMap R (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) r)
      (by simp [awayBaseHom, HomogeneousLocalization.fromZeroRingHom])

/-! #### Quotients commute with base change -/

/-- **Pushing out a quotient map along any ring map gives the quotient by the extended ideal**:
`B ⊗_A (A ⧸ I) = B ⧸ I·B`.  Proved directly from the universal property, since a ring map out
of `B ⧸ I·B` is a ring map out of `B` killing `I·B`. -/
theorem isPushout_quotientMk {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f)
        (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem f ha))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))) := by
  refine IsPushout.of_isColimit' ⟨CommRingCat.hom_ext (RingHom.ext fun _ => rfl)⟩
    (Limits.PushoutCocone.isColimitAux' _ fun c => ?_)
  have hcw : ∀ a : A, c.inl.hom (Ideal.Quotient.mk I a) = c.inr.hom (f a) := fun a =>
    congrArg (fun g : CommRingCat.of A ⟶ c.pt => g.hom a) c.condition
  have hker : I.map f ≤ RingHom.ker c.inr.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker, ← hcw a,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift (I.map f) c.inr.hom fun b hb => hker hb),
    ?_, rfl, ?_⟩
  · exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => (hcw a).symm))
  · intro m _ hr
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_))
    exact congrArg (fun g : CommRingCat.of B ⟶ c.pt => g.hom b) hr

/-- Variant of `isPushout_quotientMk` with the downstairs ideal and the induced map supplied by
the caller — which is what makes it usable against concrete maps such as `projBaseChangeQuot`
and `dehomMap` without any transport along `Ideal.quotEquivOfEq`. -/
theorem isPushout_quotientMk' {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (J : Ideal B) (hJ : J = I.map f) (g : A ⧸ I →+* B ⧸ J)
    (hg : g.comp (Ideal.Quotient.mk I) = (Ideal.Quotient.mk J).comp f) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  subst hJ
  have hgeq : g = Ideal.Quotient.lift I ((Ideal.Quotient.mk (I.map f)).comp f)
      (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem f ha)) :=
    Ideal.Quotient.ringHom_ext (by rw [hg]; rfl)
  rw [hgeq]
  exact isPushout_quotientMk f I

section MvPoly

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **Base change of the polynomial ring** is a pushout of rings — mathlib's
`Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S)`, transported into `CommRingCat`. -/
theorem isPushout_mvPolyBaseChange :
    IsPushout (CommRingCat.ofHom (algebraMap F (MvPolynomial (Fin 3) F)))
      (CommRingCat.ofHom (algebraMap F K))
      (CommRingCat.ofHom (MvPolynomial.map (algebraMap F K)))
      (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))) :=
  CommRingCat.isPushout_of_isPushout F (MvPolynomial (Fin 3) F) K (MvPolynomial (Fin 3) K)

end MvPoly

theorem ofHom_algebraMap_projQuot {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin 3) R)) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (polynomialHomogeneousIdeal W).toIdeal)
      = CommRingCat.ofHom (algebraMap R
          (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)) := by
  ext r
  rfl

/-- **The homogeneous coordinate ring base-changes**: `K[X, Y, Z] ⧸ (W_K)` is
`(F[X, Y, Z] ⧸ (W)) ⊗_F K`. -/
theorem isPushout_projQuotBaseChange :
    IsPushout
      (CommRingCat.ofHom (algebraMap F
        (MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal)))
      (CommRingCat.ofHom (algebraMap F K))
      (CommRingCat.ofHom (projBaseChangeQuot E K))
      (CommRingCat.ofHom (algebraMap K
        (MvPolynomial (Fin 3) K ⧸ (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal))) := by
  have hq := isPushout_quotientMk' (MvPolynomial.map (algebraMap F K))
    (polynomialHomogeneousIdeal E).toIdeal
    (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal
    (by
      show Ideal.span {polynomial (E.baseChange K)}
        = Ideal.map (MvPolynomial.map (algebraMap F K)) (Ideal.span {polynomial E})
      rw [Ideal.map_span, Set.image_singleton, polynomial_baseChange])
    (projBaseChangeQuot E K) rfl
  have h := (isPushout_mvPolyBaseChange K).paste_horiz hq
  rwa [ofHom_algebraMap_projQuot, ofHom_algebraMap_projQuot] at h

/-- **The dehomogenised chart base-changes** — the ring residue of `hbc`, in the form the
dehomogenisation isomorphism delivers it.  Quotients commute with base change, so this is the
coordinate-ring pushout pasted with one more quotient. -/
theorem isPushout_dehomBaseChange
    (s : MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal) :
    IsPushout
      (CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span {s - 1})).comp
        (algebraMap F (MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal))))
      (CommRingCat.ofHom (algebraMap F K))
      (CommRingCat.ofHom (dehomMap (projBaseChangeGradedHom E K) s))
      (CommRingCat.ofHom ((Ideal.Quotient.mk
        (Ideal.span {projBaseChangeGradedHom E K s - 1})).comp
        (algebraMap K (MvPolynomial (Fin 3) K ⧸
          (polynomialHomogeneousIdeal (E.baseChange K)).toIdeal)))) := by
  have hq := isPushout_quotientMk' (projBaseChangeQuot E K) (Ideal.span {s - 1})
    (Ideal.span {projBaseChangeGradedHom E K s - 1})
    (by rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]; rfl)
    (dehomMap (projBaseChangeGradedHom E K) s) rfl
  have h := (isPushout_projQuotBaseChange E K).paste_horiz hq
  rwa [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at h

/-- **THE RING RESIDUE OF `hbc`, PROVEN**: `Away 𝒜 s ⊗_F K ≅ Away ℬ (φ s)` for `s` of degree
one, stated as a pushout square of rings.  Transported from `isPushout_dehomBaseChange` along
the dehomogenisation isomorphism, whose naturality is `awayToDehom_comp_awayMap`. -/
theorem isPushout_awayBaseChange
    (s : MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal)
    (hs : s ∈ projGrading E 1) :
    IsPushout (CommRingCat.ofHom (awayBaseHom E s))
      (CommRingCat.ofHom (algebraMap F K))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) s))
      (CommRingCat.ofHom
        (awayBaseHom (E.baseChange K) (projBaseChangeGradedHom E K s))) := by
  refine (isPushout_dehomBaseChange E K s).of_iso' (Iso.refl _)
    (awayDehomEquiv (projGrading E) hs).toCommRingCatIso (Iso.refl _)
    (awayDehomEquiv (projGrading (E.baseChange K))
      ((projBaseChangeGradedHom E K).map_mem hs)).toCommRingCatIso ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
    exact (congrArg CommRingCat.ofHom (awayToDehom_comp_awayBaseHom E s)).symm
  · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact (congrArg CommRingCat.ofHom (awayToDehom_comp_awayMap _ hs)).symm
  · rw [Iso.refl_hom, Category.id_comp]
    exact (congrArg CommRingCat.ofHom
      (awayToDehom_comp_awayBaseHom (E.baseChange K) (projBaseChangeGradedHom E K s))).symm

/-- **The base-change square of projective models is CARTESIAN.**

`Scheme.isPullback_of_openCover` reduces this to the three standard charts `D₊(x₀), D₊(x₁),
D₊(x₂)` of `proj E`.  Over each chart, `isPullback_awayι_map` identifies the pullback of
`projBaseChangeMap` with `Spec` of `HomogeneousLocalization.Away.map`, and
`awayι_projToSpec_eq_specMap'` turns the two structure morphisms into `Spec.map`s — so the
chart obligation is `Spec` of the ring pushout `isPushout_awayBaseChange`. -/
theorem isPullback_projBaseChangeMap :
    IsPullback (projBaseChangeMap E K) (projToSpec (E.baseChange K)) (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap F K))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _
    (Proj.affineOpenCoverOfIrrelevantLESpan (projGrading E) (projCoord E) (m := fun _ => 1)
      (projCoord_mem_grading E) (fun _ => Nat.one_pos)
      (irrelevant_le_span_projCoord E)).openCover fun i => ?_
  have hfs : projBaseChangeGradedHom E K (projCoord E i) ∈ projGrading (E.baseChange K) 1 :=
    (projBaseChangeGradedHom E K).map_mem (projCoord_mem_grading E i)
  -- the chart square of `Proj.map` is cartesian
  have C : IsPullback
      (Proj.awayι (projGrading (E.baseChange K))
        (projBaseChangeGradedHom E K (projCoord E i)) hfs Nat.one_pos)
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) (projCoord E i))))
      (projBaseChangeMap E K)
      (Proj.awayι (projGrading E) (projCoord E i) (projCoord_mem_grading E i) Nat.one_pos) :=
    (isPullback_awayι_map (projBaseChangeGradedHom E K)
      (irrelevant_le_map_projBaseChangeGradedHom E K) Nat.one_pos (projCoord E i)
      (projCoord_mem_grading E i) hfs).flip
  -- the chart square over the base is cartesian, by the ring pushout
  have H : IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projBaseChangeGradedHom E K) (projCoord E i))))
      (Proj.awayι (projGrading (E.baseChange K))
        (projBaseChangeGradedHom E K (projCoord E i)) hfs Nat.one_pos
        ≫ projToSpec (E.baseChange K))
      (Proj.awayι (projGrading E) (projCoord E i) (projCoord_mem_grading E i) Nat.one_pos
        ≫ projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap F K))) := by
    rw [awayι_projToSpec_eq_specMap' E _ _ Nat.one_pos,
      awayι_projToSpec_eq_specMap' (E.baseChange K) _ _ Nat.one_pos]
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (isPushout_awayBaseChange E K (projCoord E i) (projCoord_mem_grading E i))
  have key := isPullback_of_isoApex H C.isoPullback.symm
  rw [Iso.symm_hom, ← Category.assoc, C.isoPullback_inv_fst, C.isoPullback_inv_snd] at key
  exact key


/-- **`Proj` commutes with base change of the base field** — the `hbc` step of
`geometricallyConnected_projToSpecOverField`, over an ARBITRARY base field.

Read off `isPullback_projBaseChangeMap` through `IsPullback.isoPullback`: the cartesian
square identifies `proj (E ⊗ K)` with the pullback on the nose, so no comparison morphism
has to be constructed and no commuting square has to be assumed.  (The ℚ development
constructs `projBaseChangeHom` first and then proves it invertible; see the section note
above for why that order is not available over a general base.)

Historical note carried over from the ℚ file, since the earlier version of its docstring sent
a successor the wrong way: `Proj.pullbackAwayιIso` looks relevant and is NOT (it compares two
charts of ONE `Proj`), and `pullbackSpecIso` is not needed either — the affine chart
obligation is discharged by `isPullback_SpecMap_of_isPushout` from a pushout of rings, which
is strictly less work than building the tensor-product comparison by hand. -/
theorem nonempty_projPullbackIso :
    Nonempty (Limits.pullback (projToSpec E)
      (Spec.map (CommRingCat.ofHom (algebraMap F K))) ≅ proj (E.baseChange K)) :=
  ⟨(isPullback_projBaseChangeMap E K).isoPullback.symm⟩

end BaseChange

theorem geometricallyConnected_projToSpec (F : Type u) [Field F]
    (E : WeierstrassCurve F) [E.IsElliptic] :
    GeometricallyConnected (projToSpec E) := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  obtain ⟨hbc⟩ := nonempty_projPullbackIso E K
  haveI hne : Nonempty (proj (E.baseChange K)) := nonempty_proj _
  haveI hpre : PreconnectedSpace (proj (E.baseChange K)) := preconnectedSpace_proj _
  have hconn : ConnectedSpace (proj (E.baseChange K)) := ⟨hne⟩
  exact ObjectProperty.prop_of_iso (fun X : Scheme.{u} => ConnectedSpace X) hbc.symm hconn

section SmoothOverField

variable {F : Type u} [Field F]


/-! ### The Jacobian criterion for a Weierstrass equation

The three lemmas below are the ring-theoretic heart of item 7a, and they hold over an
ARBITRARY commutative ring — nothing here is special to `F`.

The point is `Δ_mem_jacobianSpan`: the discriminant lies in the ideal generated by the
Weierstrass polynomial and its two partial derivatives, evaluated at any pair of ring
elements.  Granted that, `IsElliptic` (which says `Δ` is a UNIT) upgrades "the Jacobian
ideal contains `Δ`" to "the Jacobian ideal is everything" at any point OF the curve, which
is exactly the hypothesis the Jacobian criterion for smoothness consumes.

The certificate is found by a route that keeps the cofactors small.  Written directly, the
identity `Δ = A·W + B·W_X + C·W_Y` in `F[a₁,…,a₆][X, Y]` has cofactors of forty-odd terms
(confirmed by a Gröbner `lift`).  But mathlib's own variable change `(X, Y) ↦ (X + x, Y + y)`
— i.e. `VariableChange.mk 1 x 0 y` — carries the curve to one whose `a₃`, `a₄`, `a₆` ARE
(up to sign) the three quantities `W_Y`, `W_X`, `W` evaluated at `(x, y)`, while fixing `Δ`.
So it suffices to certify `Δ ∈ (a₃, a₄, a₆)` in `ℤ[a₁,…,a₆]`, where the cofactors are tiny
and `ring` closes the identity outright.  That is `Δ_eq_coeffCombination`.

A numerical check worth recording: over `F[a₁,…,a₆][u, v]` the Jacobian ideal of each of the
three standard charts does NOT contain `1`, so `Δ` is genuinely carrying the content here —
the statement is not vacuously true. -/

/-- **`Δ` lies in the ideal `(a₃, a₄, a₆)`**, with explicit cofactors.

Read off from `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` by expanding each of `b₈`, `b₄³`, `b₆²`
and `b₂b₄b₆` along `a₃`, `a₄`, `a₆`; `ring` verifies the result. -/
theorem Δ_eq_coeffCombination {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.Δ =
      (-W.b₂ ^ 2 * (W.a₂ * W.a₃ - W.a₁ * W.a₄) - 8 * W.b₄ ^ 2 * W.a₁ - 27 * W.b₆ * W.a₃
        + 9 * W.b₂ * W.b₄ * W.a₃) * W.a₃
      + (W.b₂ ^ 2 * W.a₄ - 16 * W.b₄ ^ 2) * W.a₄
      + (-W.b₂ ^ 3 - 108 * W.b₆ + 36 * W.b₂ * W.b₄) * W.a₆ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    WeierstrassCurve.Δ]
  ring

/-- Translating the curve by `(x, y)` sends `a₃` to `W_Y(x, y)`. -/
theorem variableChangeShift_a₃ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₃
      = Polynomial.evalEval x y W.toAffine.polynomialY := by
  rw [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.Affine.evalEval_polynomialY]
  simp
  ring

/-- Translating the curve by `(x, y)` sends `a₄` to `-W_X(x, y)`. -/
theorem variableChangeShift_a₄ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₄
      = -Polynomial.evalEval x y W.toAffine.polynomialX := by
  rw [WeierstrassCurve.variableChange_a₄, WeierstrassCurve.Affine.evalEval_polynomialX]
  simp
  ring

/-- Translating the curve by `(x, y)` sends `a₆` to `-W(x, y)`. -/
theorem variableChangeShift_a₆ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).a₆
      = -Polynomial.evalEval x y W.toAffine.polynomial := by
  rw [WeierstrassCurve.variableChange_a₆, WeierstrassCurve.Affine.evalEval_polynomial]
  simp
  ring

/-- Translating the curve by `(x, y)` fixes the discriminant (the scaling unit is `1`). -/
theorem variableChangeShift_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W).Δ = W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ]
  simp

/-- **The discriminant lies in the Jacobian ideal of the affine Weierstrass equation**,
at every pair of ring elements. -/
theorem Δ_mem_jacobianSpan {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    W.Δ ∈ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomial,
      Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} := by
  have h := Δ_eq_coeffCombination ((WeierstrassCurve.VariableChange.mk 1 x 0 y) • W)
  rw [variableChangeShift_Δ, variableChangeShift_a₃, variableChangeShift_a₄,
    variableChangeShift_a₆] at h
  rw [h]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
    (Ideal.mul_mem_left _ _ ?_)
  · exact Ideal.subset_span (by simp)
  · exact neg_mem (Ideal.subset_span (by simp))
  · exact neg_mem (Ideal.subset_span (by simp))

/-- **On an elliptic curve, the two partial derivatives generate the unit ideal at every
point of the curve.**  This is the Jacobian criterion in the form the chart argument needs,
and it is the ONLY place `E.IsElliptic` is consumed in item 7a. -/
theorem jacobianSpan_eq_top {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (x y : R) (h : W.toAffine.Equation x y) :
    Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem := Δ_mem_jacobianSpan W x y
  rw [show Polynomial.evalEval x y W.toAffine.polynomial = 0 from h] at hmem
  have hsub : Ideal.span {(0 : R), Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY}
      ≤ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
        Polynomial.evalEval x y W.toAffine.polynomialY} := by
    rw [Ideal.span_le]
    rintro z (rfl | hz)
    · exact Ideal.zero_mem _
    · exact Ideal.subset_span hz
  obtain ⟨u, hu⟩ := W.isUnit_Δ
  have hu' : (u : R) ∈ Ideal.span {Polynomial.evalEval x y W.toAffine.polynomialX,
      Polynomial.evalEval x y W.toAffine.polynomialY} := hu ▸ hsub hmem
  simpa using Ideal.mul_mem_left _ (↑u⁻¹) hu'

/-- `SmoothOfRelativeDimension n` of a `Spec.map` is exactly the associated ring-hom
property, by `HasRingHomProperty.Spec_iff`. -/
theorem smoothOfRelativeDimension_specMap_of_locally {A : Type u} [CommRing A] (φ : F →+* A)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) φ) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact h


/-! ### Dehomogenisation: the standard affine chart of `Proj` of a polynomial quotient

This is the MISSING MATHLIB PIECE of item 7a, and nothing below is elliptic-curve
mathematics: it is the identification of the degree-zero part of an away-localisation of a
graded polynomial quotient with a concrete polynomial quotient.  Mathlib has
`HomogeneousLocalization.Away` and `Proj.awayι` but no such identification — a grep for
`dehomogeni` over the pin returns NOTHING, and neither `~/cs/FLT` nor this project has one.

The three declarations below cut the residual leaf into three independent pieces, each
stated exactly as `locally_isStandardSmooth_awayCoord` consumes it and each carrying its own
proof plan.  The assembly is written and PROVEN, and so now are two of the three pieces:
only `projChart_jacobian_span_eq_top` is still open.

The identification itself (`exists_projChartRingEquiv`) is built here out of the material
between `eval₂_dehomogenizeAt` and `projChartHom_ker`, and that material is written to be
upstreamable: the only place the Weierstrass equation enters is `not_X_dvd_polynomial`,
everything else being generic "dehomogenise a homogeneous polynomial and divide by `Xᵢ^n`". -/

/-- The two affine coordinates on the standard chart `D₊(Xᵢ)` of `Proj F[X, Y, Z]`, namely
the two homogeneous coordinates OTHER than `Xᵢ` — the chart coordinates being the ratios
`Xⱼ / Xᵢ` for `j ≠ i`. -/
abbrev ProjChartVar (i : Fin 3) : Type := {j : Fin 3 // j ≠ i}

/-- **Dehomogenisation at the `i`-th coordinate**: substitute `Xᵢ ↦ 1` and send each other
variable `Xⱼ` to the corresponding affine chart coordinate.

For a polynomial `p` homogeneous of degree `d` this is the numerator of `p / Xᵢ^d` written
in the chart coordinates, which is exactly what the chart identification needs. -/
noncomputable def dehomogenizeAt (R : Type u) [CommRing R] (i : Fin 3) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (ProjChartVar i) R :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

/-- The dehomogenisation of the projective Weierstrass polynomial at the `i`-th chart.

For `i = 2` (the chart `Z ≠ 0`) this is literally the affine Weierstrass polynomial
`y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆`.  For `i = 0` and `i = 1` it is a different plane
cubic — the charts at `X ≠ 0` and `Y ≠ 0` — and in particular the chart `i = 1` is the one
containing the point at infinity `[0 : 1 : 0]`. -/
noncomputable def projChartPolynomial {R : Type u} [CommRing R] (E : WeierstrassCurve R)
    (i : Fin 3) : MvPolynomial (ProjChartVar i) R :=
  dehomogenizeAt R i (polynomial E)

/-- The coordinate ring of the standard chart `D₊(Xᵢ)` of the projective Weierstrass model:
a plane curve in the two chart coordinates. -/
abbrev ProjChartRing {R : Type u} [CommRing R] (E : WeierstrassCurve R) (i : Fin 3) : Type u :=
  MvPolynomial (ProjChartVar i) R ⧸ Ideal.span {projChartPolynomial E i}

open _root_.MvPolynomial in
/-- Evaluating a dehomogenisation is evaluating the original polynomial with `Xᵢ ↦ 1`. -/
theorem eval₂_dehomogenizeAt {S : Type u} [CommRing S] (c : F →+* S) (i : Fin 3)
    (g : Fin 3 → S) (p : MvPolynomial (Fin 3) F) :
    MvPolynomial.eval₂ c (fun j : ProjChartVar i => g j.1) (dehomogenizeAt F i p)
      = MvPolynomial.eval₂ c (fun j => if j = i then 1 else g j) p := by
  classical
  have key : (MvPolynomial.eval₂Hom c (fun j : ProjChartVar i => g j.1)).comp
      ((dehomogenizeAt F i).toRingHom)
      = MvPolynomial.eval₂Hom c (fun j => if j = i then 1 else g j) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [dehomogenizeAt]
    · intro j
      by_cases h : j = i <;> simp [dehomogenizeAt, h]
  exact congrArg (fun φ : MvPolynomial (Fin 3) F →+* S => φ p) key

open _root_.MvPolynomial in
/-- **The core dehomogenisation identity** (PROVEN).  If `t i` is invertible with inverse `s`,
then evaluating the dehomogenisation of a degree-`n` homogeneous `p` at the ratios `t j / t i`
gives `p(t) / t i ^ n`.

The proof is the one-line monomial computation made uniform: after reducing to a monomial `d`
with `∑ⱼ dⱼ = n`, the two products over `Fin 3` are compared factorwise, the factor at `j = i`
being `1 ^ dᵢ · t i ^ dᵢ` and the factor at `j ≠ i` being `(s · t j) ^ dⱼ · t i ^ dⱼ = t j ^ dⱼ`.
No case split on `i` is needed. -/
theorem eval₂_dehomogenizeAt_mul_pow {S : Type u} [CommRing S] (c : F →+* S) (i : Fin 3)
    (t : Fin 3 → S) (s : S) (hs : s * t i = 1) {n : ℕ} {p : MvPolynomial (Fin 3) F}
    (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂ c (fun j : ProjChartVar i => s * t j.1) (dehomogenizeAt F i p) * t i ^ n
      = MvPolynomial.eval₂ c t p := by
  classical
  rw [eval₂_dehomogenizeAt c i (fun j => s * t j)]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [← MvPolynomial.coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : ∑ j : Fin 3, d j = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _),
      Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
  rw [mul_assoc, ← hdn, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h; simp
  · simp only [h, if_false, ← mul_pow]
    congr 1
    rw [mul_right_comm, hs, one_mul]

/-! #### Homogenisation, the section of `dehomogenizeAt` -/

/-- The inclusion `F[uⱼ : j ≠ i] → F[X₀, X₁, X₂]` sending each chart variable to the
corresponding homogeneous coordinate. -/
noncomputable def inclChartVar (i : Fin 3) :
    MvPolynomial (ProjChartVar i) F →ₐ[F] MvPolynomial (Fin 3) F :=
  MvPolynomial.aeval fun j => MvPolynomial.X j.1

theorem dehomogenizeAt_inclChartVar (i : Fin 3) (q : MvPolynomial (ProjChartVar i) F) :
    dehomogenizeAt F i (inclChartVar i q) = q := by
  have key : (dehomogenizeAt F i).comp (inclChartVar i) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [dehomogenizeAt, inclChartVar, dif_neg j.2]
  exact congrArg (fun φ : MvPolynomial (ProjChartVar i) F →ₐ[F] _ => φ q) key

/-- **Homogenisation at the `i`-th coordinate.**  The homogeneous component of degree `d` of
`q` (viewed in the big polynomial ring) is multiplied by `Xᵢ^(n - d)`, where `n` is the total
degree.  This is a section of `dehomogenizeAt` landing in a single degree, and it is the only
thing the kernel computation needs: the *value* of `n` is irrelevant. -/
noncomputable def homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) F) :
    MvPolynomial (Fin 3) F :=
  ∑ d ∈ Finset.range ((inclChartVar i q).totalDegree + 1),
    MvPolynomial.X i ^ ((inclChartVar i q).totalDegree - d) *
      MvPolynomial.homogeneousComponent d (inclChartVar i q)

theorem isHomogeneous_homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) F) :
    (homogenizeAt i q).IsHomogeneous (inclChartVar i q).totalDegree := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd => ?_
  have hdle : d ≤ (inclChartVar i q).totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  have h := (MvPolynomial.isHomogeneous_X_pow (R := F) i
      ((inclChartVar i q).totalDegree - d)).mul
    (MvPolynomial.homogeneousComponent_isHomogeneous d (inclChartVar i q))
  rwa [Nat.sub_add_cancel hdle] at h

theorem dehomogenizeAt_homogenizeAt (i : Fin 3) (q : MvPolynomial (ProjChartVar i) F) :
    dehomogenizeAt F i (homogenizeAt i q) = q := by
  have hXi : dehomogenizeAt F i (MvPolynomial.X i) = 1 := by simp [dehomogenizeAt]
  rw [homogenizeAt, map_sum]
  simp only [map_mul, map_pow, hXi, one_pow, one_mul]
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  exact dehomogenizeAt_inclChartVar i q

/-! #### The chart homomorphism `F[u, v] → (B_{xᵢ})₀` -/

section ChartHom

variable (E : WeierstrassCurve F) (i : Fin 3) (hcoord : projCoord E i ∈ projGrading E 1)

/-- The chart ratio `xⱼ / xᵢ`, an element of the degree-zero away-localisation. -/
noncomputable def projChartRatio (j : ProjChartVar i) :
    HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  HomogeneousLocalization.Away.mk (projGrading E) hcoord 1
    (Ideal.Quotient.mk _ (MvPolynomial.X j.1))
    (by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X F j.1)))

/-- The base map `F → (B_{xᵢ})₀`, exactly the composite appearing in the commuting triangle of
`exists_projChartRingEquiv`. -/
noncomputable def projChartBase :
    F →+* HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  (HomogeneousLocalization.fromZeroRingHom (projGrading E)
    (Submonoid.powers (projCoord E i))).comp (algebraMap F (projGrading E 0))

/-- **The chart homomorphism** `F[u, v] → (B_{xᵢ})₀`, sending `uⱼ ↦ xⱼ / xᵢ`. -/
noncomputable def projChartHom :
    MvPolynomial (ProjChartVar i) F →+*
      HomogeneousLocalization.Away (projGrading E) (projCoord E i) :=
  MvPolynomial.eval₂Hom (projChartBase E i) (projChartRatio E i hcoord)

/-- **The chart homomorphism computes dehomogenisations** (PROVEN): a homogeneous `p` of
degree `n` dehomogenises to a polynomial whose image is the fraction `p̄ / xᵢ^n`.

This is the whole content of the identification.  It is proved by transporting both sides into
the ordinary localisation `B_{xᵢ}` along `HomogeneousLocalization.val` — which is available as
a ring hom, being `algebraMap (HomogeneousLocalization 𝒜 x) (Localization x)` — and then
applying `eval₂_dehomogenizeAt_mul_pow` with `t j = xⱼ/1` and `s = 1/xᵢ`, cancelling the unit
`xᵢ^n`. -/
theorem projChartHom_dehomogenizeAt {n : ℕ} {p : MvPolynomial (Fin 3) F}
    (hp : p.IsHomogeneous n) (hmem : Ideal.Quotient.mk _ p ∈ projGrading E (n • 1)) :
    projChartHom E i hcoord (dehomogenizeAt F i p)
      = HomogeneousLocalization.Away.mk (projGrading E) hcoord n
        (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) hmem := by
  classical
  set B := MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal with hB
  set f : B := projCoord E i with hf
  set L := Localization (Submonoid.powers f) with hL
  set V := algebraMap (HomogeneousLocalization.Away (projGrading E) f) L with hV
  set t : Fin 3 → L := fun j => algebraMap B L (Ideal.Quotient.mk _ (MvPolynomial.X j)) with ht
  set s : L := Localization.mk 1 ⟨f, ⟨1, pow_one f⟩⟩ with hs'
  set c : F →+* L := V.comp (projChartBase E i) with hc
  have hti : t i = algebraMap B L f := rfl
  have htj : ∀ j : Fin 3, t j = Localization.mk
      (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.X j)) 1 := fun j => by
    rw [ht]; exact (Localization.mk_one_eq_algebraMap _).symm
  -- `s` inverts `t i`
  have hs : s * t i = 1 := by
    rw [hs', hti, Localization.mk_eq_mk']
    exact (IsLocalization.mk'_spec L 1 (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f)).trans (map_one _)
  -- the ratios are `s * t j`
  have hratio : ∀ j : ProjChartVar i, V (projChartRatio E i hcoord j) = s * t j.1 := fun j => by
    rw [hs', htj]
    show Localization.mk _ ⟨f ^ 1, _⟩ = Localization.mk 1 ⟨f, _⟩ * Localization.mk _ 1
    rw [Localization.mk_mul, one_mul, mul_one]
    congr 1
    exact Subtype.ext (pow_one f)
  -- `V ∘ projChartHom` is `eval₂` into the localisation
  have hcomp : V.comp (projChartHom E i hcoord)
      = MvPolynomial.eval₂Hom c (fun j : ProjChartVar i => s * t j.1) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [projChartHom, hc]
    · intro j; simp [projChartHom, hratio j]
  -- `eval₂ c t` is the quotient map followed by localisation
  have hct : MvPolynomial.eval₂Hom c t
      = (algebraMap B L).comp (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hcr : ((algebraMap F (projGrading E 0) r : B)) =
          Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.C r) := by
        rw [SetLike.GradeZero.coe_algebraMap,
          IsScalarTower.algebraMap_apply F (MvPolynomial (Fin 3) F) B r,
          Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hc]
      show Localization.mk ((algebraMap F (projGrading E 0) r : B))
            (1 : ↥(Submonoid.powers f))
          = algebraMap B L
            (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.C r))
      rw [hcr, Localization.mk_one_eq_algebraMap]
    · intro j; simp [ht]
  -- assemble
  have hcore := eval₂_dehomogenizeAt_mul_pow c i t s hs hp
  have h1 : V (projChartHom E i hcoord (dehomogenizeAt F i p))
      = MvPolynomial.eval₂ c (fun j : ProjChartVar i => s * t j.1) (dehomogenizeAt F i p) :=
    RingHom.congr_fun hcomp _
  have h2 : MvPolynomial.eval₂ c t p
      = algebraMap B L (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) :=
    RingHom.congr_fun hct p
  have hVeq : V (projChartHom E i hcoord (dehomogenizeAt F i p)) * t i ^ n
      = algebraMap B L (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal p) := by
    rw [h1, hcore, h2]
  have hunit : IsUnit (t i ^ n) := by
    rw [hti]
    exact (IsLocalization.map_units L (⟨f, ⟨1, pow_one f⟩⟩ : Submonoid.powers f)).pow n
  apply HomogeneousLocalization.val_injective
  apply hunit.mul_left_cancel
  have hlhs : (projChartHom E i hcoord (dehomogenizeAt F i p)).val
      = V (projChartHom E i hcoord (dehomogenizeAt F i p)) := rfl
  rw [hlhs, mul_comm (t i ^ n) (V _), hVeq, HomogeneousLocalization.Away.val_mk, hti, ← map_pow,
    Localization.mk_eq_mk', mul_comm]
  exact (IsLocalization.mk'_spec L _ _).symm

/-- **The chart homomorphism is surjective.**  This is the half that was already in mathlib:
`HomogeneousLocalization.Away.mk_surjective` says every element of `(B_{xᵢ})₀` is `a / xᵢ^m`
with `a` of degree `m`, and `projChartHom_dehomogenizeAt` exhibits `dehomogenizeAt F i p` as a
preimage. -/
theorem projChartHom_surjective : Function.Surjective (projChartHom E i hcoord) := by
  intro z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (projGrading E) hcoord z
  obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp ha
  have hp' : p.IsHomogeneous m := by
    have h := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
    simpa using h
  exact ⟨dehomogenizeAt F i p, projChartHom_dehomogenizeAt E i hcoord hp' _⟩

end ChartHom

/-! #### `Xᵢ ∤ W`, and the kernel -/

/-- **`Xᵢ` does not divide the projective Weierstrass polynomial**, for any of the three
coordinates.  This — *not* irreducibility of `W` — is the only input the kernel computation
needs beyond primality of `Xᵢ`.

It is checked by evaluation.  For `i = 1, 2` the point `(1, 0, 0)` gives `-1 = 0`, in any
field.

**`i = 0` IS THE ONE PLACE THE `ℚ` PROOF DOES NOT TRANSFER, and it is a genuine
characteristic obstruction rather than a tactic failure.**  That proof evaluates at the three
`ℚ`-points `(0, 0, 1)`, `(0, 1, 1)`, `(0, -1, 1)`, obtaining `-a₆ = 0`, `1 + a₃ - a₆ = 0` and
`1 - a₃ - a₆ = 0`, and finishes with `linarith` — i.e. by adding the last two to get `2 = 0`.
Over `𝔽₂` that is not a contradiction, and **no** finite set of `F`-points can work: at
`a₃ = 1`, `a₆ = 0` over `𝔽₂` the polynomial `W(0, Y, Z) = Y²Z + YZ² = YZ(Y + Z)` vanishes at
every one of the four points of `𝔽₂²`, while `X ∤ W` remains true.  Point evaluation over `F`
is simply blind to it.

The repair is to evaluate in `F[t]` instead of in `F`: base-change along `C : F → F[t]` and
evaluate at `(X, Y, Z) = (0, t, 1)`, which leaves `t² + a₃t - a₆`, whose degree-two
coefficient is `1`.  A coefficient of a polynomial identity is characteristic-free, so this
version of the argument holds over every field — and over every nontrivial commutative
ring. -/
theorem not_X_dvd_polynomial (E : WeierstrassCurve F) (i : Fin 3) :
    ¬ (MvPolynomial.X i ∣ polynomial E) := by
  rintro ⟨S, hS⟩
  have hev : ∀ P : Fin 3 → F, P i = 0 → MvPolynomial.eval P (polynomial E) = 0 := by
    intro P hP
    rw [hS, map_mul, MvPolynomial.eval_X, hP, zero_mul]
  fin_cases i
  · -- Push the divisibility into `F[t][X, Y, Z]` and evaluate at `(0, t, 1)`.
    have hmap := congrArg (MvPolynomial.map (Polynomial.C : F →+* Polynomial F)) hS
    rw [← WeierstrassCurve.Projective.map_polynomial, map_mul, MvPolynomial.map_X] at hmap
    have h := congrArg (MvPolynomial.eval ![0, Polynomial.X, 1]) hmap
    rw [WeierstrassCurve.Projective.eval_polynomial, map_mul, MvPolynomial.eval_X] at h
    -- `h : t² + a₃ t - a₆ = 0` in `F[t]`; read off the coefficient of `t²`.
    simp at h
    have hc := congrArg (fun p : Polynomial F => p.coeff 2) h
    simp at hc
  · have h := hev ![1, 0, 0] rfl
    simp only [eval_polynomial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    norm_num at h
  · have h := hev ![1, 0, 0] rfl
    simp only [eval_polynomial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h
    norm_num at h

/-- `W ∣ Xᵢ^k · P → W ∣ P`.  This is the UFD half of the kernel argument, and mathlib's
`MvPolynomial.dvd_X_mul_iff` packages it so that a bare induction on `k` suffices: at each step
the alternative disjunct says `Xᵢ ∣ W`, refuted by `not_X_dvd_polynomial`. -/
theorem polynomial_dvd_of_dvd_X_pow_mul (E : WeierstrassCurve F) (i : Fin 3) :
    ∀ (k : ℕ) (P : MvPolynomial (Fin 3) F),
      polynomial E ∣ MvPolynomial.X i ^ k * P → polynomial E ∣ P := by
  intro k
  induction k with
  | zero => intro P h; simpa using h
  | succ k ih =>
    intro P h
    rw [pow_succ', mul_assoc] at h
    rcases MvPolynomial.dvd_X_mul_iff.mp h with h' | ⟨h'', -⟩
    · exact ih P h'
    · exact absurd h'' (not_X_dvd_polynomial E i)

section Kernel

variable (E : WeierstrassCurve F) (i : Fin 3) (hcoord : projCoord E i ∈ projGrading E 1)

/-- **The kernel of the chart homomorphism is the dehomogenised Weierstrass ideal** (PROVEN).

`⊇` is immediate since `W ↦ 0`.  For `⊆`: a `q` in the kernel homogenises to some `Q` of a
single degree `n` with `dehom Q = q`; the vanishing of `Q̄ / xᵢ^n` in the localisation says
`xᵢ^k · Q̄ = 0` in `B`, i.e. `W ∣ Xᵢ^k · Q`, whence `W ∣ Q` by
`polynomial_dvd_of_dvd_X_pow_mul`, and dehomogenising the factorisation gives `wᵢ ∣ q`. -/
theorem projChartHom_ker :
    RingHom.ker (projChartHom E i hcoord) = Ideal.span {projChartPolynomial E i} := by
  have hW0 : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (polynomial E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  apply le_antisymm
  · intro q hq
    rw [RingHom.mem_ker] at hq
    have hQhom : (homogenizeAt i q).IsHomogeneous (inclChartVar i q).totalDegree :=
      isHomogeneous_homogenizeAt i q
    have hmem : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (homogenizeAt i q)
        ∈ projGrading E ((inclChartVar i q).totalDegree • 1) := by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hQhom)
    have h0 : HomogeneousLocalization.Away.mk (projGrading E) hcoord
        (inclChartVar i q).totalDegree
        (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (homogenizeAt i q)) hmem = 0 := by
      rw [← projChartHom_dehomogenizeAt E i hcoord hQhom hmem, dehomogenizeAt_homogenizeAt, hq]
    have hval := congrArg HomogeneousLocalization.val h0
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨-, k, rfl⟩, hk⟩ := hval
    have hdvd : polynomial E ∣ MvPolynomial.X i ^ k * homogenizeAt i q := by
      rw [← Ideal.mem_span_singleton]
      show _ ∈ (polynomialHomogeneousIdeal E).toIdeal
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
      exact hk
    obtain ⟨T, hT⟩ := polynomial_dvd_of_dvd_X_pow_mul E i k _ hdvd
    rw [Ideal.mem_span_singleton]
    refine ⟨dehomogenizeAt F i T, ?_⟩
    rw [← dehomogenizeAt_homogenizeAt i q, hT, map_mul]
    rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have hhom : (polynomial E).IsHomogeneous 3 := isHomogeneous_polynomial E
    have hmem : Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (polynomial E)
        ∈ projGrading E (3 • 1) := by
      simpa using HomogeneousIdeal.mk_mem_quotientGrading (I := polynomialHomogeneousIdeal E)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hhom)
    show projChartHom E i hcoord (dehomogenizeAt F i (polynomial E)) = 0
    rw [projChartHom_dehomogenizeAt E i hcoord hhom hmem]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, hW0,
      Localization.mk_zero]

end Kernel

/-- **LEAF A — THE DEHOMOGENISATION ISOMORPHISM** (PROVEN; it was a missing piece of MATHLIB,
not of this development, and it is written above in a form fit to be upstreamed).

  `(F[X, Y, Z] ⧸ (W))_{(Xᵢ)}` in degree `0`  ≃  `F[u, v] ⧸ (wᵢ)`,

compatibly with the two structure maps out of `F`.  It is stated as a `RingEquiv` together
with the commuting triangle rather than as an `AlgEquiv` deliberately: the source carries an
`Algebra (projGrading E 0)` instance and the target an `Algebra F` one, and forcing them
into a common `Algebra F` structure invites exactly the "two defeq but never syntactically
equal instances" trap this development has been bitten by repeatedly.  The commuting
triangle is what the consumer actually needs, and it is instance-free.

## How it is proved

Everything is routed through the single ring hom `projChartHom E i hcoord : F[u, v] → (B_{xᵢ})₀`
sending `uⱼ ↦ xⱼ / xᵢ`, of which this is the first isomorphism theorem:
`projChartHom_surjective` and `projChartHom_ker`, glued by
`RingHom.quotientKerEquivOfSurjective` and `Ideal.quotEquivOfEq`.

*Surjectivity was already in mathlib*, and more cheaply than the original plan supposed.  The
plan called for `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` at `d = 1`, which does
force every algebra generator to be a product of a SUBSET of the coordinates over `xᵢ^card`.
But `HomogeneousLocalization.Away.mk_surjective` is stronger and immediate: every element of
`(B_{xᵢ})₀` is literally `ā / xᵢ^m` with `a` homogeneous of degree `m`, and
`projChartHom_dehomogenizeAt` says `dehomogenizeAt F i a` is a preimage.  So no generation
argument is needed at all.

*The kernel is the one genuinely new argument.*  Given `q` in the kernel, `homogenizeAt i q`
is a homogeneous `Q` of a single degree with `dehom Q = q` (built from the homogeneous
components of `q`, each pushed up by a power of `Xᵢ` — the degree itself is never needed).
Its image `Q̄ / xᵢ^n` vanishes iff `Xᵢ^k · Q ∈ (W)` for some `k`.  Now `F[X, Y, Z]` is a UFD,
`Xᵢ` is prime, and `Xᵢ ∤ W` for each of the three `i` — `W` contains the monomial `Y²Z` (so
`X ∤ W`) and the monomial `-X³` (so `Y ∤ W` and `Z ∤ W`).  Hence `W ∣ Xᵢ^k Q` forces `W ∣ Q`
(`polynomial_dvd_of_dvd_X_pow_mul`, an induction on `k` off `MvPolynomial.dvd_X_mul_iff`).
Dehomogenising, `wᵢ ∣ q`.  The reverse inclusion is immediate since `W` maps to `0`.

Note this argument does NOT need `W` irreducible, only `Xᵢ ∤ W`, which is a numerical check
(`not_X_dvd_polynomial`, done by evaluation at three rational points).

This is the piece that ought to be upstreamed: stated for an arbitrary homogeneous ideal of
`R[X₀ .. Xₙ]` it is the standard affine chart of `Proj` of a projective scheme over `R`, and
its absence is what had kept every `Proj`-level smoothness argument out of reach.  The one
genuinely elliptic-curve-specific input is `not_X_dvd_polynomial`; everything else above is
stated for the Weierstrass ideal only because that is the ideal at hand. -/
theorem exists_projChartRingEquiv (E : WeierstrassCurve F) (i : Fin 3)
    (hcoord : projCoord E i ∈ projGrading E 1) :
    ∃ e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) ≃+* ProjChartRing E i,
      (e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) →+* ProjChartRing E i).comp
          ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
            (Submonoid.powers (projCoord E i))).comp (algebraMap F (projGrading E 0)))
        = algebraMap F (ProjChartRing E i) := by
  have hsurj := projChartHom_surjective E i hcoord
  have hker := projChartHom_ker E i hcoord
  refine ⟨(RingHom.quotientKerEquivOfSurjective hsurj).symm.trans (Ideal.quotEquivOfEq hker), ?_⟩
  refine RingHom.ext fun r => ?_
  show Ideal.quotEquivOfEq hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm
      (projChartBase E i r)) = algebraMap F (ProjChartRing E i) r
  have h1 : projChartBase E i r = projChartHom E i hcoord (MvPolynomial.C r) :=
    (MvPolynomial.eval₂Hom_C _ _ r).symm
  rw [h1, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
    IsScalarTower.algebraMap_apply F (MvPolynomial (ProjChartVar i) F) (ProjChartRing E i) r,
    Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]

/-! #### The two ingredients of the chart Jacobian criterion

Both are stated for an arbitrary base ring and are pure `MvPolynomial` bookkeeping; only
`false_of_eval_pderiv_projPolynomial_eq_zero` below is elliptic-curve mathematics. -/

/-- Dehomogenisation sends `Xₙ` to `1` when `n = i`, and to the `n`-th chart coordinate
otherwise. -/
theorem dehomogenizeAt_X {R : Type u} [CommRing R] (i n : Fin 3) :
    dehomogenizeAt R i (MvPolynomial.X n)
      = if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩ := by
  simp [dehomogenizeAt]

/-- `pderiv_dehomogenizeAt` on a single variable — the base case of the induction. -/
theorem pderiv_dehomogenizeAt_X {R : Type u} [CommRing R] (i : Fin 3) (j : ProjChartVar i)
    (n : Fin 3) :
    MvPolynomial.pderiv j (dehomogenizeAt R i (MvPolynomial.X n))
      = dehomogenizeAt R i (MvPolynomial.pderiv (j : Fin 3) (MvPolynomial.X n)) := by
  classical
  rw [dehomogenizeAt_X]
  rcases eq_or_ne n i with rfl | h
  · rw [dif_pos rfl, MvPolynomial.pderiv_one,
      MvPolynomial.pderiv_X_of_ne (Ne.symm j.2), map_zero]
  · rw [dif_neg h]
    rcases eq_or_ne n (j : Fin 3) with h2 | h2
    · have hj : (⟨n, h⟩ : ProjChartVar i) = j := Subtype.ext h2
      rw [hj, MvPolynomial.pderiv_X_self, h2, MvPolynomial.pderiv_X_self, map_one]
    · rw [MvPolynomial.pderiv_X_of_ne (fun hc => h2 (congrArg Subtype.val hc)),
        MvPolynomial.pderiv_X_of_ne h2, map_zero]

/-- **INGREDIENT 1 — dehomogenisation commutes with the chart partials.**

For a chart variable `j ≠ i` the substitution `Xᵢ ↦ 1` is a constant in the `j`-th variable,
so `∂/∂uⱼ` may be taken before or after dehomogenising.  Consequently the two partials of
the chart equation `wᵢ` are the dehomogenisations of two of mathlib's `polynomialX`,
`polynomialY`, `polynomialZ`. -/
theorem pderiv_dehomogenizeAt {R : Type u} [CommRing R] (i : Fin 3) (j : ProjChartVar i)
    (p : MvPolynomial (Fin 3) R) :
    MvPolynomial.pderiv j (dehomogenizeAt R i p)
      = dehomogenizeAt R i (MvPolynomial.pderiv (j : Fin 3) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n h =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, map_mul, h,
      pderiv_dehomogenizeAt_X]

/-- Evaluating a base-changed polynomial at the image of the chart point `(…, 1, …)` is
`φ` applied to its dehomogenisation.  This is the bridge between the `MvPolynomial (Fin 3)`
world, where Euler's relation lives, and the chart ring. -/
theorem eval_map_eq_dehomogenizeAt {k : Type u} [CommRing k] [Algebra F k] (i : Fin 3)
    (φ : MvPolynomial (ProjChartVar i) F →ₐ[F] k) (p : MvPolynomial (Fin 3) F) :
    MvPolynomial.eval (fun n => φ (if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩))
        (MvPolynomial.map (algebraMap F k) p)
      = φ (dehomogenizeAt F i p) := by
  rw [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, dehomogenizeAt,
    MvPolynomial.comp_aeval_apply]

/-- **INGREDIENT 2 — EULER.**  Euler's homogeneous function theorem
`3W = X·W_X + Y·W_Y + Z·W_Z` (`WeierstrassCurve.Projective.polynomial_relation`) says the
three partials are not independent along the curve.  So at a point `P` of the curve whose
`i`-th coordinate is `1`, the vanishing of the two partials `∂/∂Xⱼ`, `j ≠ i`, forces the
vanishing of the third — which is why the chart's own two partials already control all
three. -/
theorem eval_pderiv_projPolynomial_eq_zero (E : WeierstrassCurve F) (k : Type u) [Field k]
    [Algebra F k] (i : Fin 3) (P : Fin 3 → k) (hPi : P i = 1)
    (hW : MvPolynomial.eval P (polynomial (E.map (algebraMap F k))) = 0)
    (hj : ∀ n : Fin 3, n ≠ i →
      MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap F k)))) = 0)
    (n : Fin 3) :
    MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap F k)))) = 0 := by
  have hE := WeierstrassCurve.Projective.polynomial_relation (W' := E.map (algebraMap F k)) P
  rw [hW, mul_zero] at hE
  have eX : polynomialX (E.map (algebraMap F k))
      = MvPolynomial.pderiv (0 : Fin 3) (polynomial (E.map (algebraMap F k))) := rfl
  have eY : polynomialY (E.map (algebraMap F k))
      = MvPolynomial.pderiv (1 : Fin 3) (polynomial (E.map (algebraMap F k))) := rfl
  have eZ : polynomialZ (E.map (algebraMap F k))
      = MvPolynomial.pderiv (2 : Fin 3) (polynomial (E.map (algebraMap F k))) := rfl
  rw [eX, eY, eZ] at hE
  by_cases h : n = i
  · subst h
    have hsum : ∑ b : Fin 3,
        P b * MvPolynomial.eval P (MvPolynomial.pderiv b (polynomial (E.map (algebraMap F k))))
        = 0 := by
      rw [Fin.sum_univ_three]
      linear_combination -hE
    rw [Finset.sum_eq_single_of_mem n (Finset.mem_univ n)
      (fun b _ hb => by rw [hj b hb, mul_zero]), hPi, one_mul] at hsum
    exact hsum
  · exact hj n h

/-- **THE GEOMETRIC CORE — over a FIELD there is no singular point.**

`hjac` (the affine Jacobian criterion, where `Δ` is consumed) forbids a point of the
projective Weierstrass curve at which all three homogeneous partials vanish and some
coordinate equals `1`.  The proof is a two-case check on whether the point is at infinity,
and **neither case mentions a chart** — that is what makes
`projChart_jacobian_span_eq_top` uniform in `i`.

* `P z ≠ 0`: the point is affine, `hjac` applies at `S := k`, and the two affine partials
  are `eval P W_X / P z ^ 2` and `eval P W_Y / P z ^ 2`, both zero — so `span {0, 0} = ⊤`
  in a field, absurd.
* `P z = 0`: the projective equation degenerates to `P x ^ 3 = 0`, so `P x = 0`, and then
  `eval P W_Z = P y ^ 2`, forcing `P y = 0`.  Every coordinate vanishes, contradicting
  `P i = 1`.  (The constant term of `W_Z` is what does the work here; this is the point at
  infinity, and it is not a separate chart argument.) -/
theorem false_of_eval_pderiv_projPolynomial_eq_zero (E : WeierstrassCurve F) (k : Type u)
    [Field k] [Algebra F k]
    (hjac : ∀ (S : Type u) [CommRing S] [Algebra F S] (x y : S),
      (E.map (algebraMap F S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialY} = ⊤)
    (i : Fin 3) (P : Fin 3 → k) (hPi : P i = 1)
    (hW : MvPolynomial.eval P (polynomial (E.map (algebraMap F k))) = 0)
    (hq : ∀ n : Fin 3,
      MvPolynomial.eval P (MvPolynomial.pderiv n (polynomial (E.map (algebraMap F k)))) = 0) :
    False := by
  by_cases hPz : P 2 = 0
  · -- the point lies on the line at infinity, and is then forced to be `(0 : 0 : 0)`
    have hx : P 0 = 0 := by
      have h3 := (WeierstrassCurve.Projective.equation_of_Z_eq_zero
        (W' := E.map (algebraMap F k)) hPz).1 hW
      by_contra hc
      exact pow_ne_zero 3 hc h3
    have hy : P 1 = 0 := by
      have h2 := hq 2
      rw [show MvPolynomial.pderiv (2 : Fin 3) (polynomial (E.map (algebraMap F k)))
        = polynomialZ (E.map (algebraMap F k)) from rfl,
        WeierstrassCurve.Projective.eval_polynomialZ, hx, hPz] at h2
      have hsq : P 1 ^ 2 = 0 := by linear_combination h2
      by_contra hc
      exact pow_ne_zero 2 hc hsq
    have hall : ∀ n : Fin 3, P n = 0 := by intro n; fin_cases n <;> assumption
    exact one_ne_zero (hPi.symm.trans (hall i))
  · -- an honest affine point of the curve over the field `k`
    have heq : (E.map (algebraMap F k)).toAffine.Equation (P 0 / P 2) (P 1 / P 2) :=
      (WeierstrassCurve.Projective.equation_of_Z_ne_zero (W := E.map (algebraMap F k)) hPz).1 hW
    have hX0 : Polynomial.evalEval (P 0 / P 2) (P 1 / P 2)
        (E.map (algebraMap F k)).toAffine.polynomialX = 0 := by
      rw [← WeierstrassCurve.Projective.eval_polynomialX_of_Z_ne_zero
        (W := E.map (algebraMap F k)) hPz,
        show polynomialX (E.map (algebraMap F k))
          = MvPolynomial.pderiv (0 : Fin 3) (polynomial (E.map (algebraMap F k))) from rfl,
        hq 0, zero_div]
    have hY0 : Polynomial.evalEval (P 0 / P 2) (P 1 / P 2)
        (E.map (algebraMap F k)).toAffine.polynomialY = 0 := by
      rw [← WeierstrassCurve.Projective.eval_polynomialY_of_Z_ne_zero
        (W := E.map (algebraMap F k)) hPz,
        show polynomialY (E.map (algebraMap F k))
          = MvPolynomial.pderiv (1 : Fin 3) (polynomial (E.map (algebraMap F k))) from rfl,
        hq 1, zero_div]
    have hspan := hjac k (P 0 / P 2) (P 1 / P 2) heq
    rw [hX0, hY0, Ideal.eq_top_iff_one] at hspan
    simp at hspan

/-- **THE CHART JACOBIAN CRITERION** (PROVEN): on each of the three charts the two partial
derivatives of the dehomogenised Weierstrass cubic generate the UNIT ideal of the chart
ring.  This is what makes the chart ring locally a hypersurface with an invertible partial,
and it is where `hjac` — hence `Δ` — is consumed.

## NOT VACUOUS, and true on all three charts

Checked with a Gröbner basis over `F(a₁, …, a₆)`: for each of the three charts the ideal
generated by `wᵢ` and its two partials is `(1)`.  So the statement holds for all `i`, not
merely for the affine chart, and `Δ` is genuinely doing the work (over `F[a₁, …, a₆]` the
ideal is proper — that is the content of `Δ_mem_jacobianSpan`).

## The proof, and why it is UNIFORM in `i`

The plan recorded with this leaf while it was open had three cases: `hjac` applied directly
on the affine chart `i = 2`; a unit `Z/X` on the chart `i = 0`; and, for the chart `i = 1`
containing the point at infinity, a coprimality step `span {p₂, z} = ⊤` combined with
`IsCoprime.pow_right` over the localisation away from `z`.  A Gröbner cofactor certificate
was offered as the fallback for that last chart.

**None of that is needed, and there is no case split on `i` below.**  The move that removes
it is to apply `hjac` not over the chart ring itself but over a RESIDUE FIELD of it.
Suppose the span were proper.  Pull it back: the ideal
`J := (wᵢ, ∂wᵢ/∂u, ∂wᵢ/∂v)` of `F[u, v]` is then proper too, since its image in
`F[u, v] ⧸ (wᵢ)` is exactly the span in question.  So `J ⊆ M` for some maximal `M`, and
`k := F[u, v] ⧸ M` is a FIELD.  Let `P : Fin 3 → k` be the image of the chart point, so
`P i = 1` and `P j = ūⱼ` for `j ≠ i`.  Then

* `eval P W = 0`, because `W` dehomogenises to `wᵢ ∈ J ⊆ M` (`eval_map_eq_dehomogenizeAt`);
* `eval P W_{Xⱼ} = 0` for `j ≠ i`, because dehomogenisation commutes with those partials
  (`pderiv_dehomogenizeAt`) and `∂wᵢ/∂uⱼ ∈ J ⊆ M`;
* `eval P W_{Xᵢ} = 0` as well, by Euler's relation together with `P i = 1`
  (`eval_pderiv_projPolynomial_eq_zero`).

So `P` is a singular point of the projective Weierstrass curve over a FIELD, which
`false_of_eval_pderiv_projPolynomial_eq_zero` rules out in two chart-free cases.

The point at infinity is not a special case here: it is the `P z = 0` case there, and what
disposes of it is the constant term of `W_Z` — precisely the fact the original plan had
identified as operative for the chart `i = 1`.  Passing to a residue field is what lets that
one observation serve all three charts at once, and it is why no localisation, no
`IsCoprime.pow_right`, and no Gröbner cofactor certificate appear in the proof. -/
theorem projChart_jacobian_span_eq_top (E : WeierstrassCurve F) [E.IsElliptic] (i : Fin 3)
    (hjac : ∀ (S : Type u) [CommRing S] [Algebra F S] (x y : S),
      (E.map (algebraMap F S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialY} = ⊤) :
    Ideal.span (Set.range fun j : ProjChartVar i =>
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i)) = ⊤ := by
  classical
  by_contra hne
  -- the Jacobian ideal PULLED BACK to the polynomial ring is proper
  have hJ : Ideal.span (insert (projChartPolynomial E i)
      (Set.range fun j : ProjChartVar i =>
        MvPolynomial.pderiv j (projChartPolynomial E i))) ≠ ⊤ := by
    intro htop
    refine hne ((Ideal.eq_top_iff_one _).2 ?_)
    have hmap : Ideal.map (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}))
        (Ideal.span (insert (projChartPolynomial E i)
          (Set.range fun j : ProjChartVar i =>
            MvPolynomial.pderiv j (projChartPolynomial E i))))
        ≤ Ideal.span (Set.range fun j : ProjChartVar i =>
            (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
              (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i)) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro x ⟨y, hy, rfl⟩
      rcases hy with rfl | ⟨j, rfl⟩
      · simp only [SetLike.mem_coe]
        rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
        exact Ideal.zero_mem _
      · exact Ideal.subset_span ⟨j, rfl⟩
    refine hmap ?_
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}))]
    exact Ideal.mem_map_of_mem _ (htop ▸ Submodule.mem_top)
  obtain ⟨M, hM, hMle⟩ := Ideal.exists_le_maximal _ hJ
  haveI : M.IsMaximal := hM
  letI : Field (MvPolynomial (ProjChartVar i) F ⧸ M) := Ideal.Quotient.field M
  refine false_of_eval_pderiv_projPolynomial_eq_zero E (MvPolynomial (ProjChartVar i) F ⧸ M)
    hjac i (fun n => Ideal.Quotient.mkₐ F M (if h : n = i then 1 else MvPolynomial.X ⟨n, h⟩))
    (by simp) ?_ ?_
  · rw [WeierstrassCurve.Projective.map_polynomial,
      eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ F M)]
    show (Ideal.Quotient.mkₐ F M) (projChartPolynomial E i) = 0
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hMle (Ideal.subset_span (Set.mem_insert _ _)))
  · refine eval_pderiv_projPolynomial_eq_zero E _ i _ (by simp) ?_ ?_
    · rw [WeierstrassCurve.Projective.map_polynomial,
        eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ F M)]
      show (Ideal.Quotient.mkₐ F M) (projChartPolynomial E i) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hMle (Ideal.subset_span (Set.mem_insert _ _)))
    · intro n hn
      rw [WeierstrassCurve.Projective.map_polynomial, MvPolynomial.pderiv_map,
        eval_map_eq_dehomogenizeAt i (Ideal.Quotient.mkₐ F M),
        ← pderiv_dehomogenizeAt i (⟨n, hn⟩ : ProjChartVar i)]
      show (Ideal.Quotient.mkₐ F M)
        (MvPolynomial.pderiv (⟨n, hn⟩ : ProjChartVar i) (projChartPolynomial E i)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (hMle (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨n, hn⟩, rfl⟩)))

/-- **A PLANE CURVE IS STANDARD SMOOTH OF RELATIVE DIMENSION `1` WHERE A PARTIAL DERIVATIVE
IS INVERTIBLE** (PROVEN; it was LEAF C of the residual item-7a leaf, and it is a piece of
MATHLIB rather than of this development).

## The construction

`Algebra.PreSubmersivePresentation.naive` (`Mathlib/RingTheory/Extension/Presentation/
Submersive.lean`) builds a pre-submersive presentation of `R[Xₛ] ⧸ (vᵣ)` from an INJECTIVE
assignment `a : relations → variables`, with `jacobiMatrix_naive` computing the Jacobian
matrix as `(vⱼ).pderiv (a i)`.  So the whole of the construction is:

* variables `σ := ProjChartVar i ⊕ Unit`, i.e. `(u, v, t)` — three of them;
* relations `ι := Fin 2`, namely `wᵢ` and `t · ∂wᵢ/∂uⱼ - 1`;
* the assignment `a` sends the first relation to `uⱼ` and the second to `t`, which is
  injective;
* the Jacobian matrix is then LOWER TRIANGULAR,
  `[[∂wᵢ/∂uⱼ, 0], [t · ∂²wᵢ/∂uⱼ², ∂wᵢ/∂uⱼ]]`, with determinant `(∂wᵢ/∂uⱼ)²`, a unit in the
  quotient because the second relation says `t` inverts it;
* `dimension = card σ - card ι = 3 - 2 = 1`, using
  `Fintype.card (ProjChartVar i) = 2`.

The one piece of plumbing is the identification of the presented ring with `T`:

  `F[u, v, t] ⧸ (wᵢ, t·∂wᵢ/∂uⱼ - 1)`  ≃  `(F[u, v] ⧸ (wᵢ))_{∂wᵢ/∂uⱼ}`,

obtained from `MvPolynomial.optionEquivLeft` (or `sumAlgEquiv`) to split off `t`, then
`Ideal.polynomialQuotientEquivQuotientPolynomial` to push the quotient by `wᵢ` inside, then
`Localization.awayEquivAdjoin` — which is precisely
`Localization.Away r ≃ₐ[R] AdjoinRoot (C r * X - 1)` — to recognise the remaining quotient.
The one piece of plumbing is the identification of the presented ring with `T`,

  `F[u, v, t] ⧸ (wᵢ, t·∂wᵢ/∂uⱼ - 1)`  ≃  `(F[u, v] ⧸ (wᵢ))_{∂wᵢ/∂uⱼ}`.

It is built here by hand as a pair of mutually inverse maps rather than by chaining
mathlib's quotient/localisation equivalences: `Ideal.Quotient.liftₐ` in one direction and
`IsLocalization.lift` in the other, compared on generators with `MvPolynomial.ringHom_ext`
and `IsLocalization.ringHom_ext`.  That turned out to be markedly shorter than assembling
`MvPolynomial.optionEquivLeft`, `Ideal.polynomialQuotientEquivQuotientPolynomial` and
`Localization.awayEquivAdjoin`, and it avoids the `Algebra F (MvPolynomial V F ⧸ I)` SMul
diamond — `Submodule.Quotient.instSMul'` versus `Algebra.toSMul` — which defeats
`IsScalarTower.of_algebraMap_eq` on the nose and is why the maps below are compared as
RING homs wherever the chart ring is involved.

Then `SubmersivePresentation.ofAlgEquiv` transports the presentation onto `T`, and the
dimension count is `Nat.card (Option (ProjChartVar i)) - Nat.card (Fin 2) = 3 - 2 = 1`.

Axiom audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem isStandardSmoothOfRelativeDimension_projChartAway (E : WeierstrassCurve F) (i : Fin 3)
    (j : ProjChartVar i) (T : Type u) [CommRing T] [Algebra (ProjChartRing E i) T]
    [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
      (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i) T] :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      ((algebraMap (ProjChartRing E i) T).comp (algebraMap F (ProjChartRing E i))) := by
  classical
  algebraize [(algebraMap (ProjChartRing E i) T).comp (algebraMap F (ProjChartRing E i))]
  -- the two relations of the presentation, in the variables `(u, v, t)`
  set v : Fin 2 → MvPolynomial (Option (ProjChartVar i)) F :=
    ![MvPolynomial.rename Option.some (projChartPolynomial E i),
      MvPolynomial.X none * MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)) - 1] with hv
  set P := MvPolynomial (Option (ProjChartVar i)) F ⧸ (Ideal.span <| Set.range v) with hP
  -- `t` inverts `∂w/∂u` in `P`
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)))) := by
    have key : Ideal.Quotient.mk (Ideal.span <| Set.range v)
        (MvPolynomial.rename Option.some
          (MvPolynomial.pderiv j (projChartPolynomial E i)))
        * Ideal.Quotient.mk _ (MvPolynomial.X none) = 1 := by
      rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)),
        ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
    exact ⟨⟨_, _, key, by rw [mul_comm]; exact key⟩, rfl⟩
  set dbar : ProjChartRing E i := Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
    (MvPolynomial.pderiv j (projChartPolynomial E i)) with hdbar
  -- the ring map `C → P`
  have hkillw : ∀ a ∈ Ideal.span {projChartPolynomial E i},
      (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        (MvPolynomial.rename Option.some a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hz : (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        (MvPolynomial.rename Option.some (projChartPolynomial E i)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨0, by simp [hv]⟩
    rw [map_mul, map_mul, hz, mul_zero]
  set CtoP : ProjChartRing E i →ₐ[F] P :=
    Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ F (Ideal.span <| Set.range v)).comp
      (MvPolynomial.rename Option.some)) hkillw with hCtoP
  have hCtoP_mk : ∀ p, CtoP (Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.rename Option.some p) :=
    fun p => rfl
  -- the ring map `P → T`
  set g : Option (ProjChartVar i) → T := fun o => match o with
    | none => IsLocalization.mk' T (1 : ProjChartRing E i) ⟨dbar, Submonoid.mem_powers _⟩
    | some x => algebraMap (ProjChartRing E i) T
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) (MvPolynomial.X x)) with hg
  have hrename : ∀ p : MvPolynomial (ProjChartVar i) F,
      MvPolynomial.aeval g (MvPolynomial.rename Option.some p)
        = algebraMap (ProjChartRing E i) T
          (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) p) := by
    have : ((MvPolynomial.aeval g : MvPolynomial (Option (ProjChartVar i)) F →ₐ[F] T) :
          MvPolynomial (Option (ProjChartVar i)) F →+* T).comp
          ((MvPolynomial.rename Option.some :
            MvPolynomial (ProjChartVar i) F →ₐ[F] MvPolynomial (Option (ProjChartVar i)) F) :
            MvPolynomial (ProjChartVar i) F →+* _)
        = (algebraMap (ProjChartRing E i) T).comp
          (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
          MvPolynomial.rename_C, MvPolynomial.aeval_C]
        exact IsScalarTower.algebraMap_apply F (ProjChartRing E i) T r
      · simp [hg]
    exact fun p => congrArg (fun f : MvPolynomial (ProjChartVar i) F →+* T => f p) this
  have hginv : g none * algebraMap (ProjChartRing E i) T dbar = 1 := by
    show IsLocalization.mk' T (1 : ProjChartRing E i) ⟨dbar, Submonoid.mem_powers _⟩
      * algebraMap (ProjChartRing E i) T dbar = 1
    rw [IsLocalization.mk'_spec, map_one]
  have hkillv : ∀ a ∈ Ideal.span (Set.range v), MvPolynomial.aeval g a = 0 := by
    intro a ha
    refine Submodule.span_induction ?_ (by simp) (by intro x y _ _ hx hy; simp [hx, hy])
      (by intro c x _ hx; simp [hx]) ha
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · show MvPolynomial.aeval g
        (MvPolynomial.rename Option.some (projChartPolynomial E i)) = 0
      rw [hrename, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self _), map_zero]
    · show MvPolynomial.aeval g (MvPolynomial.X none * MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i)) - 1) = 0
      rw [map_sub, map_mul, MvPolynomial.aeval_X, hrename, map_one, ← hdbar, hginv, sub_self]
  set PtoT : P →ₐ[F] T := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval g) hkillv with hPtoT
  have hPtoT_mk : ∀ q, PtoT (Ideal.Quotient.mk (Ideal.span <| Set.range v) q)
      = MvPolynomial.aeval g q := fun q => rfl
  -- the ring map `T → P`
  have hCtoP_dbar : CtoP dbar = Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i))) := rfl
  have hunits : ∀ y : Submonoid.powers dbar, IsUnit ((CtoP : ProjChartRing E i →+* P) y) := by
    rintro ⟨_, n, rfl⟩
    rw [show ((CtoP : ProjChartRing E i →+* P) (dbar ^ n)) = (CtoP dbar) ^ n from map_pow _ _ _,
      hCtoP_dbar]
    exact hunit.pow n
  set TtoP : T →+* P := IsLocalization.lift hunits with hTtoP
  have hTtoP_alg : ∀ c, TtoP (algebraMap (ProjChartRing E i) T c) = CtoP c :=
    fun c => IsLocalization.lift_eq hunits c
  have hcomp : ∀ c : ProjChartRing E i, PtoT (CtoP c) = algebraMap (ProjChartRing E i) T c := by
    intro c
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hCtoP_mk, hPtoT_mk, hrename]
  -- the two composites are the identity
  have hTP : ∀ x : T, PtoT (TtoP x) = x := by
    have := IsLocalization.ringHom_ext (M := Submonoid.powers dbar) (S := T)
      (j := (PtoT : P →+* T).comp TtoP) (k := RingHom.id T)
      (RingHom.ext fun c => by
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
          AlgHom.coe_toRingHom]
        rw [hTtoP_alg, hcomp])
    exact fun x => congrArg (fun f : T →+* T => f x) this
  have hPT : ∀ x : P, TtoP (PtoT x) = x := by
    have : (TtoP.comp (PtoT : P →+* T)).comp
        (Ideal.Quotient.mk (Ideal.span <| Set.range v))
        = (RingHom.id P).comp (Ideal.Quotient.mk (Ideal.span <| Set.range v)) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun n => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
        rw [hPtoT_mk]
        simp only [MvPolynomial.aeval_C]
        rw [IsScalarTower.algebraMap_apply F (ProjChartRing E i) T r, hTtoP_alg]
        exact (CtoP.commutes r).trans (by rfl)
      · cases n with
        | none =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (IsLocalization.mk' T (1 : ProjChartRing E i)
            ⟨dbar, Submonoid.mem_powers _⟩) = _
          rw [IsLocalization.lift_mk'_spec]
          rw [map_one]
          change (1 : P) = CtoP dbar *
            Ideal.Quotient.mk (Ideal.span <| Set.range v) (MvPolynomial.X none)
          rw [hCtoP_dbar, ← map_mul, eq_comm, ← sub_eq_zero,
            ← map_one (Ideal.Quotient.mk (Ideal.span <| Set.range v)), ← map_sub,
            Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span ⟨1, by simp [hv, mul_comm]⟩
        | some x =>
          simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
            AlgHom.coe_toRingHom]
          rw [hPtoT_mk]
          simp only [MvPolynomial.aeval_X]
          show TtoP (algebraMap (ProjChartRing E i) T
            (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i}) (MvPolynomial.X x))) = _
          rw [hTtoP_alg, hCtoP_mk, MvPolynomial.rename_X]
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun f : MvPolynomial (Option (ProjChartVar i)) F →+* P => f q) this
  -- the isomorphism `P ≃ₐ[F] T`
  set eA : P ≃ₐ[F] T := AlgEquiv.ofRingEquiv
    (f := { (PtoT : P →+* T) with invFun := TtoP, left_inv := hPT, right_inv := hTP })
    (fun x => PtoT.commutes x) with heA
  -- `∂/∂t` kills everything pulled back from the chart variables
  have hpd0 : ∀ p : MvPolynomial (ProjChartVar i) F,
      MvPolynomial.pderiv (none : Option (ProjChartVar i))
        (MvPolynomial.rename Option.some p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp => simp [hp]
  have ha : Function.Injective (![some j, none] : Fin 2 → Option (ProjChartVar i)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hdet : (Algebra.PreSubmersivePresentation.naive (R := F) (v := v)
      ![some j, none] ha).jacobiMatrix.det
      = (MvPolynomial.rename Option.some
          (MvPolynomial.pderiv j (projChartPolynomial E i))) ^ 2 := by
    rw [Matrix.det_fin_two, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    simp only [hv, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_sub, MvPolynomial.pderiv_X, Derivation.leibniz,
      MvPolynomial.pderiv_rename (Option.some_injective (ProjChartVar i)), hpd0]
    simp [sq]
  refine (Algebra.SubmersivePresentation.ofAlgEquiv
    ⟨Algebra.PreSubmersivePresentation.naive (R := F) (v := v) ![some j, none] ha, ?_⟩
    eA).isStandardSmoothOfRelativeDimension ?_
  · rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hdet, map_pow]
    refine IsUnit.pow 2 ?_
    show IsUnit (Ideal.Quotient.mk (Ideal.span <| Set.range v)
      (MvPolynomial.rename Option.some
        (MvPolynomial.pderiv j (projChartPolynomial E i))))
    exact hunit
  · show Nat.card (Option (ProjChartVar i)) - Nat.card (Fin 2) = 1
    simp

/-- **THE RESIDUAL LEAF OF ITEM 7a** — the degree-zero part of the localisation of the
homogeneous coordinate ring at a coordinate is locally standard smooth of relative
dimension `1` over `F`.

Everything else in `smoothOfRelativeDimension_projToSpec` is now proven: the reduction to
the three coordinate charts, the identification of each chart composite with a `Spec.map`
(`awayι_projToSpec_eq_specMap`), the passage to the ring-hom property
(`smoothOfRelativeDimension_specMap_of_locally`), and the Jacobian criterion itself
(`jacobianSpan_eq_top`, supplied here as `hjac` and therefore genuinely consumed).

## THIS IS NOW PROVEN, from three named sub-leaves

The recipe below is written out and compiles; what remain are the three declarations in the
"Dehomogenisation" section above, each of which is a missing piece of MATHLIB rather than
any further elliptic-curve mathematics:

* `exists_projChartRingEquiv` (LEAF A) — the **dehomogenisation isomorphism**
  `(F[X, Y, Z] ⧸ (W))_{(xᵢ)}` in degree `0` ≃ `F[u, v] ⧸ (wᵢ)`, with the commuting triangle
  over `F`.  Mathlib has `HomogeneousLocalization.Away` and `Proj.awayι` but NO
  identification of the degree-zero away-part with a concrete polynomial quotient — a grep
  for `dehomogeni` over the pin returns nothing, and neither does one over `~/cs/FLT`.
* `projChart_jacobian_span_eq_top` (LEAF B) — the two chart partials generate the unit
  ideal.  This is where `hjac`, and hence `Δ`, is consumed.
* `isStandardSmoothOfRelativeDimension_projChartAway` (**PROVEN**) — on each of the two
  localisations the `2 × 2` Jacobian of the relations `(wᵢ, t·∂wᵢ/∂u - 1)` in the generators
  `(u, v, t)` is triangular with determinant `(∂wᵢ/∂u)²`, a unit there, so the presentation
  is submersive of dimension `3 - 2 = 1`.

Leaves A and B each carry their own proof plan; see their docstrings.  A Gröbner computation confirms the
Jacobian ideal of each of the three charts is the unit ideal over `F(a₁, …, a₆)` and is
PROPER over `F[a₁, …, a₆]`, so no chart is exceptional and none of this is vacuous. -/
theorem locally_isStandardSmooth_awayCoord (E : WeierstrassCurve F) [E.IsElliptic] (i : Fin 3)
    (hcoord : (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal (MvPolynomial.X i))
      ∈ projGrading E 1)
    (hjac : ∀ (S : Type u) [CommRing S] [Algebra F S] (x y : S),
      (E.map (algebraMap F S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialY} = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((HomogeneousLocalization.fromZeroRingHom (projGrading E)
        (Submonoid.powers (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal
          (MvPolynomial.X i)))).comp (algebraMap F (projGrading E 0))) := by
  classical
  obtain ⟨e, he⟩ := exists_projChartRingEquiv E i hcoord
  /- The chart ring is locally standard smooth of relative dimension `1`: the two partial
  derivatives generate the unit ideal (LEAF B, where `hjac` and hence `Δ` is consumed), and
  on each of the two localisations the curve is a hypersurface with an invertible partial
  (LEAF C). -/
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap F (ProjChartRing E i)) :=
    RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      (fun j : ProjChartVar i =>
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i))
      (projChart_jacobian_span_eq_top E i hjac)
      (fun j => Localization.Away
        (Ideal.Quotient.mk (Ideal.span {projChartPolynomial E i})
          (MvPolynomial.pderiv j (projChartPolynomial E i)) : ProjChartRing E i))
      (fun j => isStandardSmoothOfRelativeDimension_projChartAway E i j _)
  -- transport back along the dehomogenisation isomorphism (LEAF A)
  have htrans := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ e.symm hloc
  rw [← he, ← RingHom.comp_assoc] at htrans
  have hid : e.symm.toRingHom.comp
      (e : HomogeneousLocalization.Away (projGrading E) (projCoord E i) →+* ProjChartRing E i)
      = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  rwa [hid, RingHom.id_comp] at htrans

/-- **The projective Weierstrass model is smooth of relative dimension
`1` over `Spec F`** (sorry node — item 7a).

CORRECTION to the item-7 note in `exists_ellipticScheme_of_weierstrass`'s
docstring, and a sharpening rather than a restatement: the Jacobian
criterion is NOT absent from this pin.  `Mathlib/RingTheory/Smooth/Local.lean`
states it for LOCAL ALGEBRAS and `Smooth/StandardSmoothOfFree.lean` carries
`isUnit_jacobian_of_cotangentRestrict_bijective`.  What is missing is a
`Proj`-level formulation, so the task here is to DESCEND the local
criterion along the standard affine cover of `Proj` — `Proj.awayι` and
`Proj.affineOpenCover` — not to build a criterion from nothing.

On each affine chart the partial derivatives of the Weierstrass
polynomial generate the unit ideal exactly when `Δ` is invertible, which
is `E.IsElliptic`.  This is where ellipticity is genuinely used, and it
is the only place the discriminant enters.

## What is PROVEN here and what remains

The **reduction to the three coordinate charts is now proven**, and it is the whole
of the glue: `SmoothOfRelativeDimension n` has a `HasRingHomProperty`, hence is
Zariski-local at the SOURCE, so `IsZariskiLocalAtSource.of_openCover` reduces the
claim to the charts of any affine open cover.  The cover used is
`Proj.affineOpenCoverOfIrrelevantLESpan` at the three images `x₀, x₁, x₂` of the
coordinates — i.e. `D₊(X)`, `D₊(Y)`, `D₊(Z)` — rather than mathlib's default
`Proj.affineOpenCover`, whose index set is ALL homogeneous elements of positive
degree and which would therefore leave a strictly harder residual obligation.

Both side conditions of that cover are discharged:

* the degree condition `xᵢ ∈ projGrading E 1`, from
  `HomogeneousIdeal.mk_mem_quotientGrading` and `MvPolynomial.isHomogeneous_X`;
* the covering condition `(projGrading E)₊ ≤ span {x₀, x₁, x₂}`, via
  `HomogeneousIdeal.toIdeal_irrelevant_le` (which reduces it to homogeneous elements
  of positive degree) and `MvPolynomial.mem_ideal_span_X_image` (a polynomial lies in
  the ideal generated by the variables iff every monomial of its support involves
  one) — a homogeneous polynomial of degree `i > 0` has no constant monomial, so it
  qualifies.

**`hchart` is now proven too, modulo ONE named leaf.**  The chart obligation has been
reduced all the way to a ring-hom property, and the Jacobian criterion — the part that
actually uses `Δ` — is PROVEN:

* `awayι_projToSpec_eq_specMap` — by `Proj.awayι_toSpecZero`, the chart composite
  `Spec ((A_{xᵢ})₀) ⟶ Proj 𝒜 ⟶ Spec F` IS `Spec.map` of the ring map `F → (A_{xᵢ})₀`,
  so the residual obligation is purely RING-THEORETIC;
* `smoothOfRelativeDimension_specMap_of_locally` — for such a `Spec.map`,
  `SmoothOfRelativeDimension 1` is exactly `Locally (IsStandardSmoothOfRelativeDimension 1)`
  of that ring map, by `HasRingHomProperty.Spec_iff`;
* `jacobianSpan_eq_top` — **where `Δ` enters, and PROVEN over an ARBITRARY commutative
  ring**: at any point of the curve the two partial derivatives generate the unit ideal.
  It is handed to the leaf as the hypothesis `hjac`, so the discriminant is genuinely
  consumed rather than merely available.

The single remaining leaf is `locally_isStandardSmooth_awayCoord`, and what it needs is a
piece of MATHLIB infrastructure rather than any further elliptic-curve mathematics: the
dehomogenisation isomorphism between the degree-zero part of `(F[X, Y, Z] ⧸ (W))_{xᵢ}` and
`F[u, v] ⧸ (wᵢ)`.  Its own docstring states precisely what is missing and how the
remaining pieces fit.  Concretely, for `i = 2` the target ring is
`F[x, y] ⧸ (y² + a₁xy + a₃y − x³ − a₂x² − a₄x − a₆)`. -/
theorem smoothOfRelativeDimension_projToSpec (E : WeierstrassCurve F) [E.IsElliptic] :
    SmoothOfRelativeDimension 1 (projToSpec E) := by
  classical
  -- the images of the three coordinates in the homogeneous coordinate ring
  set f : Fin 3 → (MvPolynomial (Fin 3) F ⧸ (polynomialHomogeneousIdeal E).toIdeal) :=
    fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  have f_deg : ∀ i, f i ∈ projGrading E 1 := fun i =>
    HomogeneousIdeal.mk_mem_quotientGrading
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X F i))
  -- the three basic opens `D₊(xᵢ)` really do cover `Proj`
  have hf : (HomogeneousIdeal.irrelevant (projGrading E)).toIdeal
      ≤ Ideal.span (Set.range f) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi z hz
    obtain ⟨p, hp, rfl⟩ := HomogeneousIdeal.mem_quotientGrading.mp hz
    have hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hcon
      push Not at hcon
      have hm0 : m = 0 := by
        ext j; exact hcon j (Set.mem_univ j)
      have hdeg := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
        (MvPolynomial.mem_support_iff.mp hm)
      rw [hm0] at hdeg
      simp at hdeg
      omega
    have hle : Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3)))
        ≤ Ideal.comap (Ideal.Quotient.mk (polynomialHomogeneousIdeal E).toIdeal)
          (Ideal.span (Set.range f)) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, -, rfl⟩
      exact Ideal.subset_span ⟨j, rfl⟩
    exact hle hp'
  /- **The Jacobian criterion**, PROVEN: at any point of any base change of `E`, the two
  partial derivatives generate the unit ideal.  This is where `E.IsElliptic` is consumed,
  and it is the mathematical input to the chart obligation below. -/
  have hjac : ∀ (S : Type u) [CommRing S] [Algebra F S] (x y : S),
      (E.map (algebraMap F S)).toAffine.Equation x y →
      Ideal.span {Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialX,
        Polynomial.evalEval x y (E.map (algebraMap F S)).toAffine.polynomialY} = ⊤ :=
    fun S _ _ x y h => jacobianSpan_eq_top _ x y h
  /- **The residual leaf**, now reduced to a purely ring-theoretic statement: each chart
  composite is `Spec.map` of a ring map out of `F`, so smoothness of relative dimension `1`
  is the corresponding ring-hom property of that map. -/
  have hchart : ∀ i : Fin 3, SmoothOfRelativeDimension 1
      (Proj.awayι (projGrading E) (f i) (f_deg i) Nat.one_pos ≫ projToSpec E) := by
    intro i
    rw [awayι_projToSpec_eq_specMap' E (f i) (f_deg i) Nat.one_pos]
    exact smoothOfRelativeDimension_specMap_of_locally _
      (locally_isStandardSmooth_awayCoord E i (f_deg i) hjac)
  exact IsZariskiLocalAtSource.of_openCover
    (Proj.affineOpenCoverOfIrrelevantLESpan (projGrading E) f (m := fun _ => 1) f_deg
      (fun _ => Nat.one_pos) hf).openCover hchart

end SmoothOverField

end ProjGeometryOverField


end WeierstrassCurve.Projective.OverField

/-! ## The two group-law data that lie over the base, over an ARBITRARY commutative ring

`GaloisRepresentation.Modularity.ProjGroupLawOverField` (`Fermat/FLT/Modularity/MoretBailly.lean`)
carries three "lies over the base" fields — `hm`, `he`, `hi` — which the `ℚ` development
(`Fermat/FLT/ModularCurve/EllipticScheme.lean`) gets for free from
`Fermat.hom_ext_spec_rat`: over `Spec ℚ` a scheme has at most one morphism to the base, so
every morphism between `ℚ`-schemes is automatically a `ℚ`-morphism and all three are
`Subsingleton.elim`.  Over a general base that lemma is FALSE and the three become real
obligations.

Two of the three are discharged HERE, over an arbitrary `[CommRing R]` — they concern
`projInfty` and `projNeg`, which are exactly the two pieces of the chord–tangent law that
need no gluing:

* `projInfty_comp_projToSpec` — `[0 : 1 : 0]` is a SECTION of the structure morphism, i.e.
  the field `he`;
* `projNeg_comp_projToSpec` — inversion lies over the base, i.e. the field `hi`.

`hm` is NOT here and cannot be: it is a statement about the group law `m`, which does not
exist over a general base yet — constructing it is the `exists_projAdd` half of the port, and
it is the one part of `exists_projGroupLawOverField_geomFibreAddEquiv` that is still open.

Both proofs are the universal properties, not computations.  `projInfty` is
`Proj.fromOfGlobalSections` of the evaluation `X ↦ 0, Y ↦ 1, Z ↦ 0`, so
`Proj.fromOfGlobalSections_toSpecZero` reduces `he` to the statement that the composite
`R → Γ(Spec R) → R[X,Y,Z]/(W) → Γ(Spec R)` back to `R` is the identity, which
`toSpecΓ_SpecMap_ΓSpecIso_inv` supplies.  `projNeg` is `Proj.map` of a graded automorphism,
and mathlib has no naturality lemma for `Proj.toSpecZero` along `Proj.map`, so the proof goes
through the affine open cover `Proj.mapAffineOpenCover`: on each chart the two sides are
`Spec` of maps out of `(projGrading W) 0`, and they agree because the Weierstrass involution
`Y ↦ −Y − a₁X − a₃Z` fixes the degree-zero part pointwise (`negGradedHom_apply_zero` — the
degree-zero part of the homogeneous coordinate ring is the image of the constants). -/

namespace WeierstrassCurve.Projective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option backward.isDefEq.respectTransparency false in
/-- **The point at infinity is a section of the structure morphism**, over an arbitrary
commutative ring.  This is the field `he` of `ProjGroupLawOverField`. -/
theorem projInfty_comp_projToSpec :
    projInfty W ≫ projToSpec W = 𝟙 (Spec (CommRingCat.of R)) := by
  have key := Proj.fromOfGlobalSections_toSpecZero (𝒜 := projGrading W)
      (X := Spec (CommRingCat.of R))
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom.comp (evalInftyQuot W))
      (map_irrelevant_evalInfty_eq_top W)
  rw [projToSpec, projInfty, ← Category.assoc, key, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have hcomp :
      ((((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom.comp (evalInftyQuot W)).comp
          (algebraMap (projGrading W 0)
            (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal))).comp
        (algebraMap R (projGrading W 0)) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom := by
    ext r
    have h2 : (algebraMap (↥(projGrading W 0))
          (MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal))
          ((algebraMap R ↥(projGrading W 0)) r)
        = Ideal.Quotient.mk _ (MvPolynomial.C r) := rfl
    simp only [RingHom.comp_apply, h2, evalInftyQuot_mk]
    simp [evalInfty]
  rw [hcomp]
  simp

/-- A polynomial homogeneous of degree `0` is a constant. -/
theorem eq_C_of_isHomogeneous_zero {σ : Type*} {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous 0) : p = MvPolynomial.C (p.coeff 0) := by
  have h : p.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hp
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h

/-- **The Weierstrass involution fixes the degree-zero part of the homogeneous coordinate
ring pointwise**: in degree `0` every class is the class of a constant, and
`Y ↦ −Y − a₁X − a₃Z` is an `R`-algebra map. -/
theorem negGradedHom_apply_zero (a : ↥(projGrading W 0)) :
    negGradedHom W (a : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal)
      = (a : MvPolynomial (Fin 3) R ⧸ (polynomialHomogeneousIdeal W).toIdeal) := by
  obtain ⟨p, hp, hpa⟩ := HomogeneousIdeal.mem_quotientGrading.mp a.2
  rw [← hpa, negGradedHom_apply, negQuot_mk]
  congr 1
  rw [eq_C_of_isHomogeneous_zero (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mp hp)]
  simp [negAlgHom]

set_option backward.isDefEq.respectTransparency false in
/-- **Inversion lies over the base**, over an arbitrary commutative ring.  This is the field
`hi` of `ProjGroupLawOverField`. -/
theorem projNeg_comp_projToSpec :
    projNeg W ≫ projToSpec W = projToSpec W := by
  rw [projToSpec, projNeg, ← Category.assoc]
  congr 1
  refine (Proj.mapAffineOpenCover (negGradedHom W)
    (irrelevant_le_map_negGradedHom W)).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [← Category.assoc, Proj.awayι_comp_map _ _ s.1.2 _ s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext a
  simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  congr 1
  · exact negGradedHom_apply_zero W a
  · exact Subtype.ext (by simp)

end WeierstrassCurve.Projective

end
