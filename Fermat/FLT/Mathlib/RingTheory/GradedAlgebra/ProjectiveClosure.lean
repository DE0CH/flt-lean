/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.FiniteType
public import Fermat.FLT.Mathlib.RingTheory.GradedAlgebra.Quotient

/-!
# The projective closure of an affine scheme, as a graded quotient

Let `A` be an `ℕ`-graded `K`-algebra, `f ∈ 𝒜 1`, and let `ρ : (A_f)₀ → B` be a surjection of
rings.  Geometrically `Spec B` is a closed subscheme of the standard chart `D₊(f) = Spec (A_f)₀`
of `Proj 𝒜`, and this file constructs the SCHEME-THEORETIC CLOSURE of `Spec B` in `Proj 𝒜` on
the level of graded rings: a graded quotient `A ⧸ I` whose own `D₊(f̄)` chart is exactly
`Spec B`.  Stacks tag `01MZ`; Hartshorne I.2.9 in the classical language.

## The construction, and why it is the cheap one

The naive route defines `I` degreewise — `I_d := {a ∈ 𝒜 d : ρ (a / f ^ d) = 0}` — and must then
prove that the ideal it generates meets `𝒜 d` in exactly `I_d`, i.e. that `I` is SATURATED.
That is the whole difficulty of the classical construction.

Instead we package the entire degreewise family into a single ring homomorphism

  `toPoly : A →+* B[X]`,  `a ↦ ρ (a / f ^ d) * X ^ d`  for `a ∈ 𝒜 d`,

assembled from its degreewise pieces by `DirectSum.toSemiring`, and take `I := ker toPoly`.
Saturation is then automatic (`mem_ker_iff`): distinct degrees land in distinct COEFFICIENTS of
`B[X]`, so the kernel cannot mix them.  Note the target does **not** need to be graded — only
`Polynomial.coeff` is used to separate degrees — so no `ℕ`-grading on `Polynomial B` is
required.

The identification `((A ⧸ I)_{f̄})₀ ≅ B` is then built DOWNWARD, by `Localization.awayLift` out
of the dehomogenisation `a ↦ (toPoly a)(1)`, rather than upward out of generators.  The image of
`f` becomes the UNIT `1` under that map (`dehomQuot_f`, since `f / f = 1`), which is exactly what
`awayLift` needs.  This is the same reversal that closed
`nonempty_projChart_mvPolynomial` in `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.

## Main results

* `toPoly`, `coeff_toPoly`, `toPoly_of_mem` — the graded map into `B[X]`.
* `isHomogeneous_ker` — its kernel is a homogeneous ideal.
* `mem_ker_iff` — SATURATION, for free.
* `awayEquiv` — `((A ⧸ I)_{f̄})₀ ≃+* B`, the identification of charts.
* `finite_closureGrading_zero`, `finiteType_closure` — the two finiteness inheritances.

## Degenerate case

For `B = 0` the map `ρ` is zero, so `I = A`, `A ⧸ I = 0` and the degree-zero part is `0` — which
is finite over `K` but NOT isomorphic to `K`.  Nothing here breaks; a consumer must therefore ask
only for `Module.Finite K 𝒜₀` and not for `𝒜₀ ≅ K`.
-/

@[expose] public section

open DirectSum HomogeneousLocalization Polynomial

namespace ProjClosure

variable {K A B : Type*} [CommRing K] [CommRing A] [Algebra K A] [CommRing B]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜] {f : A} (hf : f ∈ 𝒜 1)

/-- `a / f ^ n` for `a` of degree `n`, when `f` has degree one. -/
def awayMk (n : ℕ) (a : 𝒜 n) : Away 𝒜 f :=
  Away.mk 𝒜 hf n (a : A) (by rw [smul_eq_mul, mul_one]; exact a.2)

theorem val_awayMk (n : ℕ) (a : 𝒜 n) :
    (awayMk 𝒜 hf n a).val = Localization.mk (a : A) ⟨f ^ n, (by use n)⟩ := rfl

theorem awayMk_congr {n : ℕ} {a b : 𝒜 n} (h : (a : A) = (b : A)) :
    awayMk 𝒜 hf n a = awayMk 𝒜 hf n b :=
  congrArg _ (Subtype.ext h)

theorem awayMk_add {n : ℕ} (a b : 𝒜 n) :
    awayMk 𝒜 hf n (a + b) = awayMk 𝒜 hf n a + awayMk 𝒜 hf n b := by
  rw [ext_iff_val, val_add, val_awayMk, val_awayMk, val_awayMk]
  exact (Localization.add_mk_self _ _ _).symm

theorem awayMk_mul {m n : ℕ} (a : 𝒜 m) (b : 𝒜 n) (c : 𝒜 (m + n)) (hc : (c : A) = a * b) :
    awayMk 𝒜 hf (m + n) c = awayMk 𝒜 hf m a * awayMk 𝒜 hf n b := by
  rw [ext_iff_val, val_mul, val_awayMk, val_awayMk, val_awayMk, Localization.mk_mul, hc]
  congr 1
  exact Subtype.ext (by simp [pow_add])

theorem awayMk_zero (n : ℕ) : awayMk 𝒜 hf n 0 = 0 := by
  rw [ext_iff_val, val_zero, val_awayMk]
  simpa using Localization.mk_zero (⟨f ^ n, (by use n)⟩ : Submonoid.powers f)

theorem awayMk_one (c : 𝒜 0) (hc : (c : A) = 1) : awayMk 𝒜 hf 0 c = 1 := by
  rw [ext_iff_val, val_one, val_awayMk, hc]
  simp

/-- `f ^ n / f ^ n = 1`. -/
theorem awayMk_pow_self (n : ℕ) (c : 𝒜 n) (hc : (c : A) = f ^ n) :
    awayMk 𝒜 hf n c = 1 := by
  rw [ext_iff_val, val_one, val_awayMk, hc]
  exact Localization.mk_self (⟨f ^ n, (by use n)⟩ : Submonoid.powers f)

variable (ρ : Away 𝒜 f →+* B)

/-- The degree-`d` piece of the graded map `A → B[X]`: `a ↦ ρ (a / f ^ d) * X ^ d`. -/
noncomputable def piece (d : ℕ) : 𝒜 d →+ Polynomial B where
  toFun a := C (ρ (awayMk 𝒜 hf d a)) * X ^ d
  map_zero' := by rw [awayMk_zero, map_zero, map_zero, zero_mul]
  map_add' a b := by rw [awayMk_add, map_add, map_add, add_mul]

@[simp] theorem piece_apply (d : ℕ) (a : 𝒜 d) :
    piece 𝒜 hf ρ d a = C (ρ (awayMk 𝒜 hf d a)) * X ^ d := rfl

theorem piece_one : piece 𝒜 hf ρ 0 (GradedMonoid.GOne.one (A := fun i => 𝒜 i)) = 1 := by
  rw [piece_apply, awayMk_one 𝒜 hf _ rfl, map_one, map_one, pow_zero, mul_one]

theorem piece_mul {i j : ℕ} (ai : 𝒜 i) (aj : 𝒜 j) :
    piece 𝒜 hf ρ (i + j) ⟨(ai : A) * (aj : A), SetLike.mul_mem_graded ai.2 aj.2⟩
      = piece 𝒜 hf ρ i ai * piece 𝒜 hf ρ j aj := by
  rw [piece_apply, piece_apply, piece_apply,
    awayMk_mul 𝒜 hf ai aj ⟨(ai : A) * (aj : A), SetLike.mul_mem_graded ai.2 aj.2⟩ rfl,
    map_mul, map_mul]
  ring

/-- The graded map `⨁ 𝒜 i → B[X]`. -/
noncomputable def toPolyAux : (⨁ i, 𝒜 i) →+* Polynomial B :=
  DirectSum.toSemiring (piece 𝒜 hf ρ) (piece_one 𝒜 hf ρ)
    (fun {_i _j} ai aj => piece_mul 𝒜 hf ρ ai aj)

theorem coeff_toPolyAux (z : ⨁ i, 𝒜 i) (d : ℕ) :
    (toPolyAux 𝒜 hf ρ z).coeff d = ρ (awayMk 𝒜 hf d (z d)) := by
  induction z using DirectSum.induction_on with
  | zero => simp [awayMk_zero]
  | of i a =>
      rw [toPolyAux, DirectSum.toSemiring_of, piece_apply, coeff_C_mul, coeff_X_pow]
      rcases eq_or_ne d i with rfl | hne
      · simp
      · rw [if_neg hne, mul_zero]
        rw [awayMk_congr 𝒜 hf (a := (DirectSum.of (fun i => 𝒜 i) i a) d) (b := 0)
          (by rw [DirectSum.of_eq_of_ne _ _ _ hne]), awayMk_zero, map_zero]
  | add x y hx hy =>
      rw [map_add, coeff_add, hx, hy, DirectSum.add_apply, awayMk_add, map_add]

/-- The graded ring map `A → B[X]` sending a degree-`d` element `a` to `ρ (a / f ^ d) X ^ d`. -/
noncomputable def toPoly : A →+* Polynomial B :=
  (toPolyAux 𝒜 hf ρ).comp (DirectSum.decomposeRingEquiv 𝒜 : A ≃+* ⨁ i, 𝒜 i).toRingHom

theorem coeff_toPoly (x : A) (d : ℕ) :
    (toPoly 𝒜 hf ρ x).coeff d = ρ (awayMk 𝒜 hf d (DirectSum.decompose 𝒜 x d)) :=
  coeff_toPolyAux 𝒜 hf ρ _ d

/-- On a homogeneous element the map is a single monomial. -/
theorem toPoly_of_mem {d : ℕ} (a : A) (ha : a ∈ 𝒜 d) :
    toPoly 𝒜 hf ρ a = C (ρ (awayMk 𝒜 hf d ⟨a, ha⟩)) * X ^ d := by
  refine Polynomial.ext fun e => ?_
  rw [coeff_toPoly, coeff_C_mul, coeff_X_pow]
  rcases eq_or_ne e d with rfl | hne
  · rw [if_pos rfl, mul_one,
      awayMk_congr 𝒜 hf (a := DirectSum.decompose 𝒜 a e) (b := ⟨a, ha⟩)
        (DirectSum.decompose_of_mem_same 𝒜 ha)]
  · rw [if_neg hne, mul_zero,
      awayMk_congr 𝒜 hf (a := DirectSum.decompose 𝒜 a e) (b := 0)
        (by rw [DirectSum.decompose_of_mem_ne 𝒜 ha (Ne.symm hne)]; rfl),
      awayMk_zero, map_zero]

/-- **The kernel is homogeneous** — because `toPoly` records the whole degreewise family
in separate coefficients of `B[X]`. -/
theorem isHomogeneous_ker : (RingHom.ker (toPoly 𝒜 hf ρ)).IsHomogeneous 𝒜 := by
  intro i r hr
  have h0 : ρ (awayMk 𝒜 hf i (DirectSum.decompose 𝒜 r i)) = 0 := by
    rw [← coeff_toPoly, RingHom.mem_ker.mp hr, coeff_zero]
  rw [RingHom.mem_ker, toPoly_of_mem 𝒜 hf ρ _ (DirectSum.decompose 𝒜 r i).2,
    awayMk_congr 𝒜 hf (a := (⟨_, (DirectSum.decompose 𝒜 r i).2⟩ : 𝒜 i))
      (b := DirectSum.decompose 𝒜 r i) rfl, h0, map_zero, zero_mul]

/-- **Saturation, for free**: a homogeneous element lies in the kernel exactly when its
associated fraction dies in `B`. -/
theorem mem_ker_iff {n : ℕ} (a : 𝒜 n) :
    (a : A) ∈ RingHom.ker (toPoly 𝒜 hf ρ) ↔ ρ (awayMk 𝒜 hf n a) = 0 := by
  rw [RingHom.mem_ker, toPoly_of_mem 𝒜 hf ρ (a : A) a.2,
    awayMk_congr 𝒜 hf (a := (⟨(a : A), a.2⟩ : 𝒜 n)) (b := a) rfl]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero, zero_mul]⟩
  have := congrArg (fun p => Polynomial.coeff p n) h
  simpa using this

theorem awayMk_surjective (z : Away 𝒜 f) : ∃ (n : ℕ) (a : 𝒜 n), awayMk 𝒜 hf n a = z := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  exact ⟨n, ⟨a, by simpa using ha⟩, rfl⟩

/-! ### The projective closure -/

/-- The homogeneous vanishing ideal of the closed subscheme cut out by `ρ`. -/
noncomputable def vanishingIdeal : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (toPoly 𝒜 hf ρ), isHomogeneous_ker 𝒜 hf ρ⟩

/-- The grading induced on the projective closure's coordinate ring. -/
noncomputable abbrev closureGrading : ℕ → Submodule K (A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) :=
  HomogeneousIdeal.quotientGrading 𝒜 (vanishingIdeal 𝒜 hf ρ)

/-- The quotient map, as a graded ring homomorphism. -/
noncomputable def mkGraded : 𝒜 →+*ᵍ closureGrading 𝒜 hf ρ :=
  { Ideal.Quotient.mk (vanishingIdeal 𝒜 hf ρ).toIdeal with
    map_mem := fun {_i _x} h => HomogeneousIdeal.mk_mem_quotientGrading h }

@[simp] theorem mkGraded_apply (a : A) :
    mkGraded 𝒜 hf ρ a = Ideal.Quotient.mk (vanishingIdeal 𝒜 hf ρ).toIdeal a := rfl

theorem mkGraded_f_mem : mkGraded 𝒜 hf ρ f ∈ closureGrading 𝒜 hf ρ 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading hf

/-- `A → B`, the dehomogenisation `a ↦ (toPoly a)(1)`. -/
noncomputable def dehom : A →+* B := (Polynomial.evalRingHom 1).comp (toPoly 𝒜 hf ρ)

theorem dehom_of_mem {d : ℕ} (a : A) (ha : a ∈ 𝒜 d) :
    dehom 𝒜 hf ρ a = ρ (awayMk 𝒜 hf d ⟨a, ha⟩) := by
  rw [dehom, RingHom.comp_apply, toPoly_of_mem 𝒜 hf ρ a ha]
  simp

/-- `A ⧸ I → B`, the dehomogenisation descended to the closure's coordinate ring. -/
noncomputable def dehomQuot : (A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) →+* B :=
  Ideal.Quotient.lift _ (dehom 𝒜 hf ρ) (fun a ha => by
    rw [dehom, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero])

@[simp] theorem dehomQuot_mk (a : A) :
    dehomQuot 𝒜 hf ρ (Ideal.Quotient.mk _ a) = dehom 𝒜 hf ρ a := rfl

/-- The image of `f` becomes a UNIT in `B` — it is `f / f = 1`.  This is what lets the
dehomogenisation be lifted off the localisation. -/
theorem dehomQuot_f : dehomQuot 𝒜 hf ρ (mkGraded 𝒜 hf ρ f) = 1 := by
  rw [mkGraded_apply, dehomQuot_mk, dehom_of_mem 𝒜 hf ρ f hf,
    awayMk_pow_self 𝒜 hf 1 ⟨f, hf⟩ (by simp), map_one]

theorem dehomQuot_f_unit : dehomQuot 𝒜 hf ρ (mkGraded 𝒜 hf ρ f) * 1 = 1 := by
  rw [dehomQuot_f, one_mul]

/-- The comparison map `(A_f)₀ → ((A ⧸ I)_{f̄})₀` induced by the quotient. -/
noncomputable def awayQuot :
    Away 𝒜 f →+* Away (closureGrading 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f) :=
  HomogeneousLocalization.Away.map (mkGraded 𝒜 hf ρ) f

/-- The inverse comparison `((A ⧸ I)_{f̄})₀ → B`, built DOWNWARD by `Localization.awayLift`
out of the dehomogenisation — the same reversal that closed
`nonempty_projChart_mvPolynomial`. -/
noncomputable def toB :
    Away (closureGrading 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f) →+* B :=
  (Localization.awayLift (dehomQuot 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f)
    (isUnit_iff_exists_inv.mpr ⟨1, dehomQuot_f_unit 𝒜 hf ρ⟩)).comp (algebraMap _ _)

theorem toB_mk (n : ℕ) (y : A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal)
    (hy : y ∈ closureGrading 𝒜 hf ρ (n • 1)) :
    toB 𝒜 hf ρ (Away.mk (closureGrading 𝒜 hf ρ) (mkGraded_f_mem 𝒜 hf ρ) n y hy)
      = dehomQuot 𝒜 hf ρ y := by
  show Localization.awayLift (dehomQuot 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f)
      (isUnit_iff_exists_inv.mpr ⟨1, dehomQuot_f_unit 𝒜 hf ρ⟩)
      (Away.mk (closureGrading 𝒜 hf ρ) (mkGraded_f_mem 𝒜 hf ρ) n y hy).val = _
  rw [Away.val_mk, Localization.awayLift_mk _ _ _ 1 (dehomQuot_f_unit 𝒜 hf ρ)]
  simp

/-- **`toB` inverts the comparison map on the nose.** -/
theorem toB_awayQuot (z : Away 𝒜 f) : toB 𝒜 hf ρ (awayQuot 𝒜 hf ρ z) = ρ z := by
  obtain ⟨n, a, rfl⟩ := awayMk_surjective 𝒜 hf z
  rw [awayQuot, awayMk, Away.map_mk, toB_mk, mkGraded_apply, dehomQuot_mk,
    dehom_of_mem 𝒜 hf ρ (a : A) a.2]
  exact congrArg ρ (awayMk_congr 𝒜 hf rfl)

theorem awayQuot_surjective : Function.Surjective (awayQuot 𝒜 hf ρ) := by
  intro w
  obtain ⟨n, y, hy, rfl⟩ :=
    Away.mk_surjective (closureGrading 𝒜 hf ρ) (mkGraded_f_mem 𝒜 hf ρ) w
  obtain ⟨a, ha, hay⟩ := HomogeneousIdeal.mem_quotientGrading.mp hy
  refine ⟨awayMk 𝒜 hf n ⟨a, by simpa using ha⟩, ?_⟩
  subst hay
  rw [awayQuot, awayMk, Away.map_mk]
  rfl

/-- If `ρ z = 0` then `z` already dies in the closure's away-localisation. -/
theorem awayQuot_eq_zero_of (z : Away 𝒜 f) (hz : ρ z = 0) : awayQuot 𝒜 hf ρ z = 0 := by
  obtain ⟨n, a, rfl⟩ := awayMk_surjective 𝒜 hf z
  have hmem : (a : A) ∈ RingHom.ker (toPoly 𝒜 hf ρ) := (mem_ker_iff 𝒜 hf ρ a).mpr hz
  rw [awayQuot, awayMk, Away.map_mk]
  refine HomogeneousLocalization.mk_eq_zero_of_num _ ?_
  exact Subtype.ext ((Ideal.Quotient.eq_zero_iff_mem).mpr hmem)

/-- **`((A ⧸ I)_{f̄})₀ ≅ B`** — the identification that makes the projective closure a chart
for `B`.  Surjectivity is where `ρ` being surjective is consumed; injectivity is the
saturation of `I = ker (toPoly)`. -/
noncomputable def awayEquiv (hρ : Function.Surjective ρ) :
    Away (closureGrading 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f) ≃+* B := by
  refine RingEquiv.ofBijective (toB 𝒜 hf ρ) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
    obtain ⟨z, rfl⟩ := awayQuot_surjective 𝒜 hf ρ w
    exact awayQuot_eq_zero_of 𝒜 hf ρ z ((toB_awayQuot 𝒜 hf ρ z).symm.trans hw)
  · intro b
    obtain ⟨z, hz⟩ := hρ b
    exact ⟨awayQuot 𝒜 hf ρ z, (toB_awayQuot 𝒜 hf ρ z).trans hz⟩

@[simp] theorem awayEquiv_apply (hρ : Function.Surjective ρ)
    (w : Away (closureGrading 𝒜 hf ρ) (mkGraded 𝒜 hf ρ f)) :
    awayEquiv 𝒜 hf ρ hρ w = toB 𝒜 hf ρ w := rfl

/-! ### The remaining `ProjChart` fields -/

/-- `𝒜₀` surjects onto the closure's degree-zero part, so finiteness over `K` is inherited. -/
theorem finite_closureGrading_zero (h : Module.Finite K ↥(𝒜 0)) :
    Module.Finite K ↥(closureGrading 𝒜 hf ρ 0) :=
  Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp h).map _)

/-- The degree-zero structure map, recognised as an `Away.mk`. -/
theorem fromZeroClosure_eq (c : ↥(closureGrading 𝒜 hf ρ 0)) :
    fromZeroRingHom (closureGrading 𝒜 hf ρ) (Submonoid.powers (mkGraded 𝒜 hf ρ f)) c
      = Away.mk (closureGrading 𝒜 hf ρ) (mkGraded_f_mem 𝒜 hf ρ) 0 (c : _)
          (by simp only [smul_eq_mul, mul_one]; exact c.2) := by
  rw [ext_iff_val, Away.val_mk]
  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, pow_zero]
  rfl

theorem toB_fromZero (c : ↥(closureGrading 𝒜 hf ρ 0)) :
    toB 𝒜 hf ρ (fromZeroRingHom (closureGrading 𝒜 hf ρ)
        (Submonoid.powers (mkGraded 𝒜 hf ρ f)) c)
      = dehomQuot 𝒜 hf ρ (c : A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) := by
  rw [fromZeroClosure_eq, toB_mk]

theorem fromZero_eq_awayMk (c : ↥(𝒜 0)) :
    fromZeroRingHom 𝒜 (Submonoid.powers f) c = awayMk 𝒜 hf 0 c := by
  rw [ext_iff_val, val_awayMk]
  simp [fromZeroRingHom]

theorem algebraMap_mem_zero (k : K) : algebraMap K A k ∈ 𝒜 0 := by
  have h := (algebraMap K ↥(𝒜 0) k).2
  simpa using h

/-- **The structure map out of `K` is unchanged by taking the closure.**  This is the `compat`
field of a `ProjChart`, in ring-theoretic form. -/
theorem toB_algebraMap (k : K) :
    toB 𝒜 hf ρ (fromZeroRingHom (closureGrading 𝒜 hf ρ)
        (Submonoid.powers (mkGraded 𝒜 hf ρ f)) (algebraMap K ↥(closureGrading 𝒜 hf ρ 0) k))
      = ρ (fromZeroRingHom 𝒜 (Submonoid.powers f) (algebraMap K ↥(𝒜 0) k)) := by
  rw [toB_fromZero, fromZero_eq_awayMk 𝒜 hf]
  have h1 : ((algebraMap K ↥(closureGrading 𝒜 hf ρ 0) k : ↥(closureGrading 𝒜 hf ρ 0)) :
      A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal)
      = Ideal.Quotient.mk _ (algebraMap K A k) := by
    simp
  rw [h1, dehomQuot_mk, dehom_of_mem 𝒜 hf ρ _ (algebraMap_mem_zero 𝒜 k)]
  exact congrArg ρ (awayMk_congr 𝒜 hf (by simp))


/-! ### Finite type descends to the closure -/

/-- The degree-zero parts, as a ring homomorphism. -/
noncomputable def gradeZeroHom : ↥(𝒜 0) →+* ↥(closureGrading 𝒜 hf ρ 0) where
  toFun a := ⟨Ideal.Quotient.mk _ (a : A), HomogeneousIdeal.mk_mem_quotientGrading a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp] theorem coe_gradeZeroHom (a : ↥(𝒜 0)) :
    (gradeZeroHom 𝒜 hf ρ a : A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal)
      = Ideal.Quotient.mk _ (a : A) := rfl

/-- **`A ⧸ I` is still of finite type over its own degree-zero part.**  It is a quotient of `A`,
which is of finite type over `𝒜 0`, and `𝒜 0` surjects onto the new degree-zero part — so no
separate generating set has to be produced. -/
theorem finiteType_closure (h : Algebra.FiniteType ↥(𝒜 0) A) :
    Algebra.FiniteType ↥(closureGrading 𝒜 hf ρ 0)
      (A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) := by
  haveI := h
  -- the quotient is of finite type over the OLD degree-zero part
  haveI hq : Algebra.FiniteType ↥(𝒜 0) (A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ ↥(𝒜 0) (vanishingIdeal 𝒜 hf ρ).toIdeal)
      Ideal.Quotient.mk_surjective
  -- and the old degree-zero part maps onto the new one, compatibly
  letI : Algebra ↥(𝒜 0) ↥(closureGrading 𝒜 hf ρ 0) := (gradeZeroHom 𝒜 hf ρ).toAlgebra
  haveI : IsScalarTower ↥(𝒜 0) ↥(closureGrading 𝒜 hf ρ 0)
      (A ⧸ (vanishingIdeal 𝒜 hf ρ).toIdeal) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType ↥(𝒜 0) _ _

end ProjClosure

end
