/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
import Fermat.FLT.EllipticCurve.TorsionCardSep
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Etale.Field
-- infinite Galois theory (`InfiniteGalois.mem_range_algebraMap_iff_fixed`):
-- Speiser's lemma at the infinite level in the `EtaleGrothendieck` section
import Mathlib.FieldTheory.Galois.Infinite
-- tensor products commute with finite products (`Algebra.TensorProduct.piRight`)
-- and étale-ness is product-local (`Algebra.FormallyEtale.pi_iff`): the product
-- assembly of `exists_finite_etale_algebra_form_of_inertia_fixes`
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Etale.Pi
public import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction

/-!

# Good reduction implies flat torsion

Let `E` be an elliptic curve over the field of fractions `K` of a discrete valuation
ring `R`, suppose that `E` has good reduction over `R`, and let `n ≥ 1` be a natural
number. Then the `n`-torsion of `E` "is a finite flat group scheme": the Galois module
`E(Kˢᵉᵖ)[n]` is, Galois-equivariantly, the group of `Kˢᵉᵖ`-points of the generic fibre
of a finite flat group scheme over `R`.

Mathlib has no group schemes, so we speak throughout of the (commutative) Hopf algebra
of functions on the group scheme instead: the statement below produces a commutative
Hopf algebra `H` over `R`, finite and flat as an `R`-module (`R` is a DVR, so this
says finite free; over a general base the right condition is finite locally free),
together with a Galois-equivariant isomorphism of groups from the `Kˢᵉᵖ`-points
`K ⊗[R] H →ₐ[K] Kˢᵉᵖ` of its generic fibre (a group under convolution, `K ⊗[R] H`
being a Hopf algebra over `K`) to the `n`-torsion subgroup of `E(Kˢᵉᵖ)`.

## Mathematical discussion: what is the correct generality?

Good reduction means that the minimal Weierstrass equation of `E` has unit discriminant
over `R`, so it defines an elliptic scheme (an abelian scheme of relative dimension 1)
`𝓔` over `R` with generic fibre `E`. Multiplication by `n` on an elliptic scheme is a
finite locally free morphism of degree `n²` for every `n ≥ 1` [Katz–Mazur, *Arithmetic
moduli of elliptic curves*, Theorem 2.3.1], so its kernel `𝓔[n]` is a finite flat group
scheme over `R` of order `n²` with generic fibre `E[n]`. This is the robust form of the
statement: it holds for every `n` over any DVR (indeed over any base scheme), in every
characteristic.

The statement formalised below is instead about the Galois module `E(Kˢᵉᵖ)[n]`, because
mathlib cannot yet express `E[n]` as a group scheme. How the two statements compare
depends on whether `n` is invertible in `K`:

* If `n` is invertible in `K` then `E[n]` is a finite étale group scheme over `K` of
  order `n²`. It is therefore determined by its Galois module of `Kˢᵉᵖ`-points, which is
  free of rank 2 over `ℤ/nℤ`, and the statement below carries the full content of the
  group-scheme statement.

* If `K` has characteristic `p` and `p ∣ n` then `E[n]` is not étale, and `E(Kˢᵉᵖ)[n]`
  sees only the points of its maximal étale quotient. This case is EXCLUDED by the
  hypothesis `(n : K) ≠ 0` of the theorem below (added 2026-07-23): the previously
  attempted route — an equal-characteristic Néron–Ogg–Shafarevich, deducing an étale
  prolongation from unramifiedness of `E(Kˢᵉᵖ)[n]` — is refuted by an explicit
  counterexample (good reduction with supersingular special fibre and ordinary generic
  fibre puts genuinely ramified prime-order torsion inside the kernel of reduction; see
  the section comment above `torsion_flat_of_good_reduction_prime_pow`). Whether the
  flat-package statement itself still holds in equal characteristic is left undecided
  here; the honest robust statement in that case is the group-scheme statement of the
  previous paragraph, which cannot yet be formalised, and no consumer of this file
  needs the equal-characteristic case (`K = ℚ` in the Frey-curve application).

Which values of `n` make flatness interesting? Let `p` denote the characteristic of the
residue field of `R`.

* If `n` is invertible in the residue field then the conclusion is equivalent to the
  Galois module `E(Kˢᵉᵖ)[n]` being unramified, which is the statement of
  `FLT.KnownIn1980s.EllipticCurves.GoodReduction`. Indeed, the order of a finite flat
  group scheme kills its module of invariant differentials [Tate, *Finite flat group
  schemes*, in *Modular forms and Fermat's Last Theorem*], so a finite flat group scheme
  over `R` whose order is invertible in `R` is unramified over `R`, hence finite étale;
  and finite étale group schemes over `R` are the same thing as unramified Galois
  modules, via normalization. In particular "unramified implies flat" holds for *any*
  finite abelian Galois module of order invertible in the residue field, for reasons
  having nothing to do with elliptic curves.

* The interesting case is therefore `p > 0` and `p ∣ n`, where flatness is genuinely
  stronger than anything expressible via ramification: for `K` of characteristic zero
  (e.g. a finite extension of `ℚ_p`) and `n = p`, this is the sense in which "`ρ` is
  flat at `p`" is used for mod `p` representations in [Serre, *Sur les représentations
  modulaires de degré 2 de Gal(ℚ̄/ℚ)*, Duke Math. J. 54 (1987), §2.8] and in the
  modularity lifting literature, and it matches the definition `GaloisRep.IsFlatAt` in
  `FLT.Deformations.RepresentationTheory.GaloisRep` (stated there for number fields; the
  theorem below is the local statement feeding into it). Note that flat does *not* imply
  unramified here: the `p`-torsion of a curve with good reduction is flat but in general
  highly ramified at `p`.

The `Algebra.Etale K (K ⊗[R] H)` condition below pins down the generic fibre as the
finite étale group scheme attached to the Galois module `E(Kˢᵉᵖ)[n]` (in particular it
forces the `R`-rank of `H` to equal the number of `n`-torsion points). It is automatic
when `K` has characteristic zero, by Cartier's theorem that finite group schemes in
characteristic zero are étale, and it is what makes the equivalence "flat ⟺ unramified"
above honest; compare the corresponding condition in `GaloisRep.HasFlatProlongationAt`.

## TODO

* `FLT.GroupScheme.FiniteFlat` plans a definition of what it means for an action of
  `Gal(Kˢᵉᵖ/K)` on a finite abelian group to be *flat*, for `K` the field of fractions
  of a DVR. Once that definition exists, the conclusion below should be refactored to
  "the Galois module `E(Kˢᵉᵖ)[n]` is flat".

* Once `E[n]` can be expressed as a group scheme (equivalently, once its Hopf algebra of
  functions is available), state the stronger result that `E[n]` itself, not just its
  Galois module of points, prolongs to a finite flat group scheme over `R`; as explained
  above, this is insensitive to the characteristic of `K`.

* The division polynomial lemma `WeierstrassCurve.isCoprime_Φ_ΨSq`, which isolates the
  arithmetic input to the theorem as a purely polynomial statement, is PROVEN and now
  lives upstream in `Fermat.FLT.EllipticCurve.PhiPsiCoprime` (see the note at the bottom
  of this file).

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of points
open scoped TensorProduct -- `⊗[R]` notation

universe u

/-!
### Arithmetic helpers: splitting `n` into a unit part and a residue-characteristic part

Over a local ring `R`, at most one prime number `p` can fail to be a unit (two distinct
primes satisfy a Bézout identity over `ℤ`, and the two generators of a Bézout identity
cannot both lie in the maximal ideal), so every `n ≥ 1` factors as `n = p ^ k * m` with
`IsUnit (m : R)` and `p ∤ m`. The two lemmas below provide the glue for this reduction;
they are consumed by the case split in `WeierstrassCurve.torsion_flat_of_good_reduction`.
-/

/-- If every prime factor of `n` is a unit in the commutative ring `A`, then so is
`(n : A)`. (Glue for `WeierstrassCurve.torsion_flat_of_good_reduction`.) -/
theorem isUnit_natCast_of_forall_prime_isUnit {A : Type*} [CommRing A] :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : A)) → IsUnit (n : A) := by
  intro n₀
  induction n₀ using Nat.strong_induction_on with
  | _ n₀ ih =>
    intro hn hall
    rcases eq_or_ne n₀ 1 with rfl | hn1
    · simp
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m, rfl⟩ := hpd
    have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
    have hmlt : m < p * m := by
      have hm : 0 < m := Nat.pos_of_ne_zero hm0
      calc m = 1 * m := (one_mul m).symm
      _ < p * m := (Nat.mul_lt_mul_right hm).mpr hp.one_lt
    have hpu : IsUnit (p : A) := hall p hp (dvd_mul_right p m)
    have hmu : IsUnit (m : A) :=
      ih m hmlt hm0 fun q hq hqm => hall q hq (hqm.mul_left p)
    rw [Nat.cast_mul]
    exact hpu.mul hmu

/-- In a local ring, at least one of two coprime natural numbers is a unit: a Bézout
identity `a * p + b * q = 1` cannot have both `p` and `q` in the maximal ideal.
(Glue for `WeierstrassCurve.torsion_flat_of_good_reduction`.) -/
theorem IsLocalRing.isUnit_natCast_or_isUnit_natCast {A : Type*} [CommRing A] [IsLocalRing A]
    {p q : ℕ} (h : p.Coprime q) : IsUnit (p : A) ∨ IsUnit (q : A) := by
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using h)
  have hA := hZ.map (Int.castRingHom A)
  rw [map_natCast, map_natCast] at hA
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab⟩ := hA
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := hab ▸
    Ideal.add_mem _
      (Ideal.mul_mem_left _ a
        ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon.1)))
      (Ideal.mul_mem_left _ b
        ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon.2)))
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h1) isUnit_one

/-!
### Valuation helpers for the kernel-of-reduction leaves

The two kernel leaves below (`kernel_add_abscissa_notMem`,
`kernel_sub_abscissa_notMem_of_residue_eq`) are pure valuation arithmetic on
Weierstrass coordinates (Silverman *AEC* VII.2.1–2). The helpers in this section carry
that arithmetic out over an arbitrary valuation subring `A` of a field `F`, for a
Weierstrass curve with `A`-integral coefficients: an affine point with integral
abscissa has integral ordinate (`ordinate_mem_of_abscissa_mem`), while a non-integral
abscissa forces `v x < v y` (`val_abscissa_lt_val_ordinate`, the `y²`/`x³` dominance);
the chord–tangent line through two kernel points has slope of strictly smaller
valuation than its intercept `c = y₁ - λx₁`, which satisfies `v c > 1`
(`kernel_slope_facts`, computed in the `(z, w) = (x/y, 1/y)` chart, where the line is
`λz + cw = 1` and the slope `-λ/c` of its chart form lies in the maximal ideal by the
subtracted-curve-equations factorization); and the two endgames: an affine point on
such a deep line has non-integral abscissa (`abscissa_notMem_of_line_deep`), and
`addX` over a slope of valuation `> 1` is non-integral
(`addX_notMem_of_one_lt_val_slope`).
-/

section KernelValuationHelpers

variable {F : Type*} [Field F] (A : ValuationSubring F)

/-- An `A`-integral multiple of an element of valuation `< 1` has valuation `< 1`.
(Glue for the kernel-of-reduction leaves.) -/
theorem ValuationSubring.val_mul_lt_one_of_mem_of_lt {a b : F} (ha : a ∈ A)
    (hb : A.valuation b < 1) : A.valuation (a * b) < 1 := by
  rw [map_mul]
  calc A.valuation a * A.valuation b ≤ 1 * A.valuation b :=
    mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
  _ = A.valuation b := one_mul _
  _ < 1 := hb

/-- If `L * d` has valuation `1` while `d` has valuation `< 1`, then `L` has valuation
`> 1`. (Glue for the congruent-points leaf: `L` is a chord or tangent slope, `d` its
denominator, `L * d` its numerator.) -/
theorem ValuationSubring.one_lt_val_of_val_mul_eq_one {L d : F}
    (hd : A.valuation d < 1) (hprod : A.valuation (L * d) = 1) :
    1 < A.valuation L := by
  by_contra hle
  rw [not_lt] at hle
  rw [map_mul] at hprod
  have hlt : A.valuation L * A.valuation d < 1 :=
    lt_of_le_of_lt (mul_le_mul_left hle _) (by rwa [one_mul])
  exact absurd hprod hlt.ne

variable (W : WeierstrassCurve F)

/-- **Integral abscissa forces integral ordinate**: on a Weierstrass curve with
`A`-integral coefficients, an affine point with `x ∈ A` has `y ∈ A` — otherwise `y²`
strictly dominates the `y`-side of the Weierstrass equation while the `x`-side stays
integral. -/
theorem WeierstrassCurve.ordinate_mem_of_abscissa_mem
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {x y : F} (hE : W.toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  by_contra hy
  rw [← A.valuation_le_one_iff, not_le] at hy
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).mp hE
  have hR : A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr
      (add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2)))
        (mul_mem ha₄ hx)) ha₆)
  have hyadd : A.valuation (y + (W.a₁ * x + W.a₃)) = A.valuation y :=
    A.valuation.map_add_eq_of_lt_left
      (lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr (add_mem (mul_mem ha₁ hx) ha₃)) hy)
  have hL : A.valuation (y ^ 2 + W.a₁ * x * y + W.a₃ * y)
      = A.valuation y * A.valuation y := by
    rw [show y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) from by ring,
      map_mul, hyadd]
  rw [hE'] at hL
  rw [hL] at hR
  exact absurd hR (not_le.mpr (hy.trans_le (le_mul_of_one_le_left' hy.le)))

/-- **Kernel points have dominant ordinate**: on a Weierstrass curve with `A`-integral
coefficients, an affine point with non-integral abscissa satisfies `v x < v y` — the
Weierstrass equation forces `v(y)² = v(x)³`, so in particular `y` strictly dominates
`x`. -/
theorem WeierstrassCurve.val_abscissa_lt_val_ordinate
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {x y : F} (hE : W.toAffine.Equation x y) (hx : x ∉ A) :
    A.valuation x < A.valuation y := by
  rw [← A.valuation_le_one_iff, not_le] at hx
  by_contra hle
  rw [not_lt] at hle
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).mp hE
  -- the `x`-side has valuation exactly `v(x)³`
  have hR : A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = A.valuation x ^ 3 := by
    rw [show x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
        = x ^ 3 + (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) from by ring]
    have h2 : A.valuation (W.a₂ * x ^ 2 + (W.a₄ * x + W.a₆)) < A.valuation (x ^ 3) := by
      rw [map_pow]
      refine A.valuation.map_add_lt ?_ (A.valuation.map_add_lt ?_ ?_)
      · rw [map_mul, map_pow]
        calc A.valuation W.a₂ * A.valuation x ^ 2 ≤ 1 * A.valuation x ^ 2 :=
          mul_le_mul_left ((A.valuation_le_one_iff _).mpr ha₂) _
        _ = A.valuation x ^ 2 := one_mul _
        _ < A.valuation x ^ 3 := pow_lt_pow_right₀ hx (by omega)
      · rw [map_mul]
        calc A.valuation W.a₄ * A.valuation x ≤ 1 * A.valuation x :=
          mul_le_mul_left ((A.valuation_le_one_iff _).mpr ha₄) _
        _ = A.valuation x ^ 1 := by rw [one_mul, pow_one]
        _ < A.valuation x ^ 3 := pow_lt_pow_right₀ hx (by omega)
      · calc A.valuation W.a₆ ≤ 1 := (A.valuation_le_one_iff _).mpr ha₆
        _ = A.valuation x ^ 0 := (pow_zero _).symm
        _ < A.valuation x ^ 3 := pow_lt_pow_right₀ hx (by omega)
    rw [A.valuation.map_add_eq_of_lt_left h2, map_pow]
  -- the `y`-side has valuation at most `v(x)²`
  have hLest : A.valuation (y ^ 2 + W.a₁ * x * y + W.a₃ * y) ≤ A.valuation x ^ 2 := by
    refine A.valuation.map_add_le (A.valuation.map_add_le ?_ ?_) ?_
    · rw [map_pow]
      exact pow_le_pow_left' hle 2
    · rw [map_mul, map_mul]
      calc A.valuation W.a₁ * A.valuation x * A.valuation y
          ≤ 1 * A.valuation x * A.valuation x := by
            exact mul_le_mul' (mul_le_mul_left ((A.valuation_le_one_iff _).mpr ha₁) _) hle
      _ = A.valuation x ^ 2 := by rw [one_mul, sq]
    · rw [map_mul]
      calc A.valuation W.a₃ * A.valuation y ≤ 1 * A.valuation y :=
        mul_le_mul_left ((A.valuation_le_one_iff _).mpr ha₃) _
      _ = A.valuation y := one_mul _
      _ ≤ A.valuation x := hle
      _ ≤ A.valuation x ^ 2 := le_self_pow hx.le (by omega)
  rw [hE', hR] at hLest
  exact absurd hLest (not_le.mpr (pow_lt_pow_right₀ hx (by omega)))

/-- **Points on a deep line are non-integral**: if an affine point of a Weierstrass
curve with `A`-integral coefficients lies on a line `Y = L·X + c` whose slope has
strictly smaller valuation than its intercept and whose intercept is non-integral,
then the abscissa is non-integral — else the ordinate `L·x + c` would have valuation
`v c > 1` while the Weierstrass equation over the integral abscissa forces it
integral. (Endgame of the kernel-addition leaf.) -/
theorem WeierstrassCurve.abscissa_notMem_of_line_deep
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {x L c : F} (hE : W.toAffine.Equation x (L * x + c))
    (hLc : A.valuation L < A.valuation c) (hc : 1 < A.valuation c) : x ∉ A := by
  intro hx
  have hy : L * x + c ∈ A := W.ordinate_mem_of_abscissa_mem A ha₁ ha₂ ha₃ ha₄ ha₆ hE hx
  have hvLx : A.valuation (L * x) < A.valuation c := by
    rw [map_mul]
    calc A.valuation L * A.valuation x ≤ A.valuation L * 1 :=
      mul_le_mul_right ((A.valuation_le_one_iff _).mpr hx) _
    _ = A.valuation L := mul_one _
    _ < A.valuation c := hLc
  have hvy := (A.valuation_le_one_iff _).mpr hy
  rw [A.valuation.map_add_eq_of_lt_right hvLx] at hvy
  exact absurd hvy (not_le.mpr hc)

/-- **`addX` over a steep slope is non-integral**: if `1 < v L` and `x₁, x₂ ∈ A`, then
`L² + a₁L - a₂ - x₁ - x₂ ∉ A` — the `L²` term strictly dominates. (Endgame of the
congruent-points leaf.) -/
theorem WeierstrassCurve.addX_notMem_of_one_lt_val_slope
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) {x₁ x₂ L : F}
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hL : 1 < A.valuation L) :
    L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂ ∉ A := by
  intro hmem
  have hL2 : A.valuation L < A.valuation L ^ 2 := by
    calc A.valuation L = A.valuation L ^ 1 := (pow_one _).symm
    _ < A.valuation L ^ 2 := pow_lt_pow_right₀ hL (by omega)
  have hsmall : ∀ {t : F}, t ∈ A → A.valuation t < A.valuation L ^ 2 := fun ht =>
    lt_of_le_of_lt ((A.valuation_le_one_iff _).mpr ht) (lt_trans hL hL2)
  have hrest : A.valuation (W.a₁ * L - W.a₂ - x₁ - x₂) < A.valuation (L ^ 2) := by
    rw [map_pow]
    refine A.valuation.map_sub_lt (A.valuation.map_sub_lt (A.valuation.map_sub_lt ?_
      (hsmall ha₂)) (hsmall hx₁)) (hsmall hx₂)
    rw [map_mul]
    calc A.valuation W.a₁ * A.valuation L ≤ 1 * A.valuation L :=
      mul_le_mul_left ((A.valuation_le_one_iff _).mpr ha₁) _
    _ = A.valuation L := one_mul _
    _ < A.valuation L ^ 2 := hL2
  have hvx₃ := (A.valuation_le_one_iff _).mpr hmem
  rw [show L ^ 2 + W.a₁ * L - W.a₂ - x₁ - x₂
      = L ^ 2 + (W.a₁ * L - W.a₂ - x₁ - x₂) from by ring,
    A.valuation.map_add_eq_of_lt_left hrest, map_pow] at hvx₃
  exact absurd hvx₃ (not_le.mpr (lt_trans hL hL2))

set_option maxHeartbeats 1000000 in
/-- **The chord–tangent line through kernel points is deep** (the heart of the
kernel-addition leaf; Silverman *AEC* VII.2.2 computed in the `(z, w) = (x/y, 1/y)`
chart without formal groups): through two (possibly equal) affine points with
non-integral abscissae whose sum is affine, the line `Y = L·X + c` of the mathlib
addition law satisfies `c ≠ 0`, `v L < v c` and `1 < v c`. Proof: on each kernel
point `v x < v y` (`val_abscissa_lt_val_ordinate`), so `z = x/y` and `w = 1/y` lie in
the maximal ideal and satisfy the chart equation
`w + a₁zw + a₃w² = z³ + a₂z²w + a₄zw² + a₆w³`; subtracting the chart equations of the
two points (resp. implicit differentiation for the tangent) factors the chart slope as
`B/A` with `A ∈ 1 + 𝔪` a unit and `B ∈ 𝔪`; the line in the chart is `Lz + cw = 1`,
whose chart slope is `-L/c`, giving `v L < v c`; and `v c > 1` because `Lz₁ + cw₁ = 1`
could not reach valuation `1` with `v c ≤ 1`. -/
theorem WeierstrassCurve.kernel_slope_facts {F : Type*} [Field F] [DecidableEq F]
    (A : ValuationSubring F) (W : WeierstrassCurve F)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {x₁ y₁ x₂ y₂ L c : F}
    (hE₁ : W.toAffine.Equation x₁ y₁) (hE₂ : W.toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hL : L = W.toAffine.slope x₁ x₂ y₁ y₂) (hc : c = y₁ - L * x₁) :
    c ≠ 0 ∧ A.valuation L < A.valuation c ∧ 1 < A.valuation c := by
  have h2A : (2 : F) ∈ A := by
    rw [show (2 : F) = 1 + 1 from by norm_num]
    exact add_mem (one_mem A) (one_mem A)
  have h3A : (3 : F) ∈ A := by
    rw [show (3 : F) = 1 + 1 + 1 from by norm_num]
    exact add_mem (add_mem (one_mem A) (one_mem A)) (one_mem A)
  -- valuation facts for the first point and its chart coordinates
  have hvx₁ : 1 < A.valuation x₁ := by rwa [← A.valuation_le_one_iff, not_le] at hx₁
  have hvxy₁ : A.valuation x₁ < A.valuation y₁ :=
    W.val_abscissa_lt_val_ordinate A ha₁ ha₂ ha₃ ha₄ ha₆ hE₁ hx₁
  have hvy₁ : 1 < A.valuation y₁ := lt_trans hvx₁ hvxy₁
  have hy₁0 : y₁ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvy₁
    exact absurd hvy₁ (by simp)
  have hvy₁0 : (0 : A.ValueGroup) < A.valuation y₁ :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy₁0)
  set z₁ := x₁ / y₁ with hz₁def
  set w₁ := 1 / y₁ with hw₁def
  have hvz₁ : A.valuation z₁ < 1 := by
    rw [hz₁def, map_div₀]
    exact (div_lt_one₀ hvy₁0).mpr hvxy₁
  have hvw₁ : A.valuation w₁ < 1 := by
    rw [hw₁def, one_div, map_inv₀]
    exact (inv_lt_one₀ hvy₁0).mpr hvy₁
  have hz₁A : z₁ ∈ A := (A.valuation_le_one_iff _).mp hvz₁.le
  have hw₁A : w₁ ∈ A := (A.valuation_le_one_iff _).mp hvw₁.le
  have hE₁' := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hE₁
  have hzw₁ : w₁ + W.a₁ * z₁ * w₁ + W.a₃ * w₁ ^ 2
      = z₁ ^ 3 + W.a₂ * z₁ ^ 2 * w₁ + W.a₄ * z₁ * w₁ ^ 2 + W.a₆ * w₁ ^ 3 := by
    rw [hz₁def, hw₁def]
    field_simp
    linear_combination hE₁'
  -- the line of the addition law passes through the first chart point
  have hlz₁ : L * z₁ + c * w₁ = 1 := by
    rw [hz₁def, hw₁def, hc]
    field_simp
    ring
  -- each case produces `c ≠ 0` and `v L < v c`
  have hmain : c ≠ 0 ∧ A.valuation L < A.valuation c := by
    by_cases hxx : x₁ = x₂
    · -- tangent case: the two points coincide
      subst hxx
      have hy12 : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hE₁ hE₂ rfl fun h => hxy ⟨rfl, h⟩
      subst hy12
      have hyne : y₁ ≠ W.toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
      have hD0 : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hyne
      have hDeq : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by
        simp only [WeierstrassCurve.Affine.negY]
        ring
      have hslope : L * (2 * y₁ + W.a₁ * x₁ + W.a₃)
          = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
        rw [hL, WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, hDeq]
        exact div_mul_cancel₀ _ (hDeq ▸ hD0)
      -- the key identity: tangency transported to the chart
      have hID : L * (y₁ ^ 2 + W.a₁ * x₁ * y₁ + 2 * W.a₃ * y₁ - W.a₂ * x₁ ^ 2
            - 2 * W.a₄ * x₁ - 3 * W.a₆)
          = -(c * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁)) := by
        rw [hc]
        linear_combination (3 * L) * hE₁' - y₁ * hslope
      -- chart forms of the two brackets
      have hA : y₁ ^ 2 + W.a₁ * x₁ * y₁ + 2 * W.a₃ * y₁ - W.a₂ * x₁ ^ 2
            - 2 * W.a₄ * x₁ - 3 * W.a₆
          = y₁ ^ 2 * (1 + (W.a₁ * z₁ + 2 * W.a₃ * w₁ - W.a₂ * z₁ ^ 2
            - 2 * W.a₄ * (z₁ * w₁) - 3 * W.a₆ * w₁ ^ 2)) := by
        rw [hz₁def, hw₁def]
        field_simp
        ring
      have hB : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁
          = y₁ ^ 2 * (3 * z₁ ^ 2 + 2 * W.a₂ * (z₁ * w₁) + W.a₄ * w₁ ^ 2 - W.a₁ * w₁) := by
        rw [hz₁def, hw₁def]
        field_simp
      -- valuations of the chart brackets
      have hvA : A.valuation (1 + (W.a₁ * z₁ + 2 * W.a₃ * w₁ - W.a₂ * z₁ ^ 2
          - 2 * W.a₄ * (z₁ * w₁) - 3 * W.a₆ * w₁ ^ 2)) = 1 := by
        refine A.valuation.map_one_add_of_lt ?_
        refine A.valuation.map_sub_lt (A.valuation.map_sub_lt (A.valuation.map_sub_lt
          (A.valuation.map_add_lt ?_ ?_) ?_) ?_) ?_
        · exact A.val_mul_lt_one_of_mem_of_lt ha₁ hvz₁
        · exact A.val_mul_lt_one_of_mem_of_lt (mul_mem h2A ha₃) hvw₁
        · refine A.val_mul_lt_one_of_mem_of_lt ha₂ ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvz₁ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt (mul_mem h2A ha₄)
            (A.val_mul_lt_one_of_mem_of_lt hz₁A hvw₁)
        · refine A.val_mul_lt_one_of_mem_of_lt (mul_mem h3A ha₆) ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvw₁ (by omega)
      have hvB : A.valuation (3 * z₁ ^ 2 + 2 * W.a₂ * (z₁ * w₁) + W.a₄ * w₁ ^ 2
          - W.a₁ * w₁) < 1 := by
        refine A.valuation.map_sub_lt (A.valuation.map_add_lt (A.valuation.map_add_lt
          ?_ ?_) ?_) ?_
        · refine A.val_mul_lt_one_of_mem_of_lt h3A ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvz₁ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt (mul_mem h2A ha₂)
            (A.val_mul_lt_one_of_mem_of_lt hz₁A hvw₁)
        · refine A.val_mul_lt_one_of_mem_of_lt ha₄ ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvw₁ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt ha₁ hvw₁
      -- `c ≠ 0`: otherwise the tangent identity forces `L = 0`, hence `y₁ = 0`
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, zero_mul, neg_zero, mul_eq_zero] at hID
        rcases hID with hL0 | hA0
        · rw [hL0, zero_mul, sub_zero] at hc
          exact hy₁0 (hc.symm.trans h0)
        · have := congrArg A.valuation hA0
          rw [hA, map_zero, map_mul, hvA, mul_one] at this
          exact (Valuation.ne_zero_iff _).mpr (pow_ne_zero 2 hy₁0) this
      -- `v L < v c` from the valuations of the identity
      refine ⟨hc0, ?_⟩
      set vB := A.valuation (3 * z₁ ^ 2 + 2 * W.a₂ * (z₁ * w₁) + W.a₄ * w₁ ^ 2
        - W.a₁ * w₁) with hvBdef
      have hY0 : A.valuation (y₁ ^ 2) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (pow_ne_zero 2 hy₁0)
      have hkeyv := congrArg A.valuation hID
      rw [Valuation.map_neg, map_mul, map_mul, hA, hB, map_mul, map_mul, hvA,
        mul_one, ← hvBdef] at hkeyv
      have hLeq : A.valuation L = A.valuation c * vB := by
        apply mul_right_cancel₀ hY0
        rw [hkeyv, mul_assoc, mul_comm vB]
      have hvc0 : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
      rw [hLeq]
      refine lt_of_le_of_ne (mul_le_of_le_one_right' hvB.le) fun h => hvB.ne ?_
      exact mul_left_cancel₀ hvc0 (h.trans (mul_one _).symm)
    · -- chord case: the two points are distinct in abscissa
      have hvx₂' : 1 < A.valuation x₂ := by rwa [← A.valuation_le_one_iff, not_le] at hx₂
      have hvxy₂ : A.valuation x₂ < A.valuation y₂ :=
        W.val_abscissa_lt_val_ordinate A ha₁ ha₂ ha₃ ha₄ ha₆ hE₂ hx₂
      have hvy₂ : 1 < A.valuation y₂ := lt_trans hvx₂' hvxy₂
      have hy₂0 : y₂ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hvy₂
        exact absurd hvy₂ (by simp)
      have hvy₂0 : (0 : A.ValueGroup) < A.valuation y₂ :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy₂0)
      set z₂ := x₂ / y₂ with hz₂def
      set w₂ := 1 / y₂ with hw₂def
      have hvz₂ : A.valuation z₂ < 1 := by
        rw [hz₂def, map_div₀]
        exact (div_lt_one₀ hvy₂0).mpr hvxy₂
      have hvw₂ : A.valuation w₂ < 1 := by
        rw [hw₂def, one_div, map_inv₀]
        exact (inv_lt_one₀ hvy₂0).mpr hvy₂
      have hz₂A : z₂ ∈ A := (A.valuation_le_one_iff _).mp hvz₂.le
      have hw₂A : w₂ ∈ A := (A.valuation_le_one_iff _).mp hvw₂.le
      have hE₂' := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hE₂
      have hzw₂ : w₂ + W.a₁ * z₂ * w₂ + W.a₃ * w₂ ^ 2
          = z₂ ^ 3 + W.a₂ * z₂ ^ 2 * w₂ + W.a₄ * z₂ * w₂ ^ 2 + W.a₆ * w₂ ^ 3 := by
        rw [hz₂def, hw₂def]
        field_simp
        linear_combination hE₂'
      -- subtracting the chart equations factors the chart chord
      have hkey : (w₂ - w₁) * (1 + (W.a₁ * z₂ + W.a₃ * (w₂ + w₁) - W.a₂ * z₂ ^ 2
            - W.a₄ * (z₂ * (w₂ + w₁)) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)))
          = (z₂ - z₁) * ((z₂ ^ 2 + z₂ * z₁ + z₁ ^ 2) + W.a₂ * (w₁ * (z₂ + z₁))
            + W.a₄ * w₁ ^ 2 - W.a₁ * w₁) := by
        linear_combination hzw₂ - hzw₁
      have hvA : A.valuation (1 + (W.a₁ * z₂ + W.a₃ * (w₂ + w₁) - W.a₂ * z₂ ^ 2
          - W.a₄ * (z₂ * (w₂ + w₁)) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2))) = 1 := by
        refine A.valuation.map_one_add_of_lt ?_
        have hww : A.valuation (w₂ + w₁) < 1 := A.valuation.map_add_lt hvw₂ hvw₁
        refine A.valuation.map_sub_lt (A.valuation.map_sub_lt (A.valuation.map_sub_lt
          (A.valuation.map_add_lt ?_ ?_) ?_) ?_) ?_
        · exact A.val_mul_lt_one_of_mem_of_lt ha₁ hvz₂
        · exact A.val_mul_lt_one_of_mem_of_lt ha₃ hww
        · refine A.val_mul_lt_one_of_mem_of_lt ha₂ ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvz₂ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt ha₄
            (A.val_mul_lt_one_of_mem_of_lt hz₂A hww)
        · refine A.val_mul_lt_one_of_mem_of_lt ha₆ ?_
          refine A.valuation.map_add_lt (A.valuation.map_add_lt ?_ ?_) ?_
          · rw [map_pow]
            exact pow_lt_one₀ zero_le hvw₂ (by omega)
          · exact A.val_mul_lt_one_of_mem_of_lt hw₂A hvw₁
          · rw [map_pow]
            exact pow_lt_one₀ zero_le hvw₁ (by omega)
      have hvB : A.valuation ((z₂ ^ 2 + z₂ * z₁ + z₁ ^ 2) + W.a₂ * (w₁ * (z₂ + z₁))
          + W.a₄ * w₁ ^ 2 - W.a₁ * w₁) < 1 := by
        refine A.valuation.map_sub_lt (A.valuation.map_add_lt (A.valuation.map_add_lt
          (A.valuation.map_add_lt (A.valuation.map_add_lt ?_ ?_) ?_) ?_) ?_) ?_
        · rw [map_pow]
          exact pow_lt_one₀ zero_le hvz₂ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt hz₂A hvz₁
        · rw [map_pow]
          exact pow_lt_one₀ zero_le hvz₁ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt ha₂
            (A.val_mul_lt_one_of_mem_of_lt hw₁A (A.valuation.map_add_lt hvz₂ hvz₁))
        · refine A.val_mul_lt_one_of_mem_of_lt ha₄ ?_
          rw [map_pow]
          exact pow_lt_one₀ zero_le hvw₁ (by omega)
        · exact A.val_mul_lt_one_of_mem_of_lt ha₁ hvw₁
      -- the unit bracket is nonzero
      have hA0 : (1 + (W.a₁ * z₂ + W.a₃ * (w₂ + w₁) - W.a₂ * z₂ ^ 2
          - W.a₄ * (z₂ * (w₂ + w₁)) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2))) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hvA
        exact zero_ne_one hvA
      -- distinct kernel points have distinct chart abscissae
      have hzne : z₁ ≠ z₂ := by
        intro hzeq
        have hz0 : z₂ - z₁ = 0 := by rw [hzeq, sub_self]
        rw [hz0, zero_mul, mul_eq_zero] at hkey
        have hw12 : w₂ = w₁ := sub_eq_zero.mp (hkey.resolve_right hA0)
        have hy12 : y₁ = y₂ := by
          rw [hw₂def, hw₁def, one_div, one_div] at hw12
          exact (inv_injective hw12).symm
        apply hxx
        have := congrArg (· * y₁) hzeq
        simp only [hz₁def, hz₂def, ← hy12] at this
        rwa [div_mul_cancel₀ _ hy₁0, div_mul_cancel₀ _ hy₁0] at this
      -- the line passes through the second chart point
      have hline₂ : y₂ = L * x₂ + c := by
        rw [hc, hL, WeierstrassCurve.Affine.slope_of_X_ne hxx]
        field_simp
        ring
      have hlz₂ : L * z₂ + c * w₂ = 1 := by
        rw [hz₂def, hw₂def]
        field_simp
        linear_combination -hline₂
      -- `c ≠ 0`: otherwise the line goes through the chart origin and `z₁ = z₂`
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, zero_mul, add_zero] at hlz₁ hlz₂
        exact hzne (mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hlz₁)
          (hlz₁.trans hlz₂.symm))
      refine ⟨hc0, ?_⟩
      -- the chart slope of the line is `-L/c`, and it equals `B/A`
      have hμ : L * (z₂ - z₁) = -(c * (w₂ - w₁)) := by
        linear_combination hlz₂ - hlz₁
      have h5 : (z₂ - z₁) * (L * (1 + (W.a₁ * z₂ + W.a₃ * (w₂ + w₁) - W.a₂ * z₂ ^ 2
            - W.a₄ * (z₂ * (w₂ + w₁)) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2))))
          = (z₂ - z₁) * (-(c * ((z₂ ^ 2 + z₂ * z₁ + z₁ ^ 2) + W.a₂ * (w₁ * (z₂ + z₁))
            + W.a₄ * w₁ ^ 2 - W.a₁ * w₁))) := by
        linear_combination (1 + (W.a₁ * z₂ + W.a₃ * (w₂ + w₁) - W.a₂ * z₂ ^ 2
            - W.a₄ * (z₂ * (w₂ + w₁)) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2))) * hμ
          - c * hkey
      have hLA := mul_left_cancel₀ (sub_ne_zero.mpr fun h => hzne h.symm) h5
      have hkeyv := congrArg A.valuation hLA
      rw [Valuation.map_neg, map_mul, map_mul, hvA, mul_one] at hkeyv
      have hvc0 : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
      rw [hkeyv]
      refine lt_of_le_of_ne (mul_le_of_le_one_right' hvB.le) fun h => hvB.ne ?_
      exact mul_left_cancel₀ hvc0 (h.trans (mul_one _).symm)
  -- shared ending: `1 < v c` from the line through the first chart point
  obtain ⟨hc0, hvLc⟩ := hmain
  refine ⟨hc0, hvLc, ?_⟩
  by_contra hle
  rw [not_lt] at hle
  have h1 : A.valuation (L * z₁) < 1 := by
    rw [map_mul]
    calc A.valuation L * A.valuation z₁ ≤ A.valuation L * 1 :=
      mul_le_mul_right hvz₁.le _
    _ = A.valuation L := mul_one _
    _ < A.valuation c := hvLc
    _ ≤ 1 := hle
  have h2 : A.valuation (c * w₁) < 1 :=
    A.val_mul_lt_one_of_mem_of_lt ((A.valuation_le_one_iff _).mp hle) hvw₁
  have h3 := A.valuation.map_add_lt h1 h2
  rw [hlz₁, map_one] at h3
  exact absurd h3 (lt_irrefl _)

end KernelValuationHelpers

-- let R be a discrete valuation ring with field of fractions K
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

-- Let E/K be an elliptic curve with good reduction over R. Note that mathlib's
-- `HasGoodReduction` asks that the given Weierstrass equation for E is a minimal
-- integral equation whose discriminant has valuation 1; this loses no generality
-- because every elliptic curve over K is isomorphic to one given by a minimal
-- equation (`WeierstrassCurve.exists_isMinimal`).
variable (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a positive natural number. (The interesting case is when n is divisible by
-- the residue characteristic of R; away from it, flatness reduces to the unramifiedness
-- statement of `FLT.KnownIn1980s.EllipticCurves.GoodReduction` — see the discussion above.)
variable (n : ℕ) [NeZero n]

-- Let Ksep be a separable closure of K (`DecidableEq` is needed for the group law on points)
variable (Ksep : Type*) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [DecidableEq Ksep]

/-!
### Decomposition of the étale case: Néron–Ogg–Shafarevich plus descent

The étale leaf `torsion_flat_of_good_reduction_of_isUnit` splits into an
elliptic-curve half — inertia above `R` acts trivially on the `m`-torsion, the easy
direction of Néron–Ogg–Shafarevich, proven in
`Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction` for odd primes, reduced
below to its prime-power core by a proven CRT/Bézout argument, with the prime-power
core in turn assembled (proven) from a proven dévissage over two characteristic-free
kernel-of-reduction leaves — and a pure descent half: an unramified torsion Galois
module of order invertible in the residue field prolongs to a finite étale (in
particular finite flat) Hopf algebra over `R`, decomposed further below into the
Galois-correspondence and prolongation leaves. All assemblies are proven. The two
kernel-of-reduction leaves (`kernel_add_abscissa_notMem`,
`kernel_sub_abscissa_notMem_of_residue_eq`) are PROVEN (2026-07-22), making the
Néron–Ogg–Shafarevich chain through `torsion_inertia_fixes_of_isUnit` sorry-free;
`torsion_flat_of_inertia_fixes_prolong` is likewise PROVEN (2026-07-22/23) through
the flat Hopf-form transport. The remaining sorries in this subsection are the
descent leaves: the curve-independent Galois-correspondence core
`exists_finiteQuotient_galoisModule_etale_package`, and the two curve-free halves of
the decomposed prolongation — `exists_finite_etale_algebra_form_of_inertia_fixes`
(DVR Galois theory) and `exists_finite_flat_hopf_form_of_etale_algebra_form`
(integral-closure commutative algebra).
-/

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [IsSepClosure K Ksep] [DecidableEq Ksep] in
/-- **The base-changed minimal model has integral coefficients** over any valuation
subring of `Kˢᵉᵖ` above `R` (glue for the two kernel-of-reduction leaves): the
coefficients of `E` come from the integral model over `R`, and `h𝒪` pulls the image of
`R` into `𝒪`. -/
theorem WeierstrassCurve.baseChange_coeff_mem
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range) :
    (E⁄Ksep).a₁ ∈ 𝒪 ∧ (E⁄Ksep).a₂ ∈ 𝒪 ∧ (E⁄Ksep).a₃ ∈ 𝒪 ∧ (E⁄Ksep).a₄ ∈ 𝒪 ∧
      (E⁄Ksep).a₆ ∈ 𝒪 := by
  haveI : E.IsIntegral R := inferInstance
  have hamem : ∀ z : R, algebraMap K Ksep (algebraMap R K z) ∈ 𝒪 := by
    intro z
    have hmem : algebraMap R K z ∈ (algebraMap R K).range := ⟨_, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem
  have hEeq : ((E.integralModel R)⁄K) = E :=
    WeierstrassCurve.baseChange_integralModel_eq R E
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]; exact hamem _)

set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] [IsSepClosure K Ksep] in
/-- **The kernel of reduction is closed under addition, abscissa form** (PROVEN
2026-07-22; Silverman *AEC* VII.2.2 in coordinates, characteristic-free and
torsion-free, no formal groups): on the minimal model, if two affine points of
`E(Kˢᵉᵖ)` both have non-integral abscissa over a valuation subring `𝒪` of `Kˢᵉᵖ` above
`R`, then any affine value of their sum again has non-integral abscissa. Proof: `xᵢ ∉ 𝒪`
forces `v yᵢ > v xᵢ > 1` (`val_abscissa_lt_val_ordinate`), so both points lie in the
chart `(z, w) = (x/y, 1/y)` with `z, w` in the maximal ideal; the chord–tangent line
`Y = LX + c` of the addition law then has `v L < v c` and `v c > 1`
(`kernel_slope_facts`), and the third intersection ordinate `L(x₃ - x₁) + y₁ = Lx₃ + c`
on the curve over an integral `x₃` would contradict `v c > 1`
(`abscissa_notMem_of_line_deep`). -/
theorem WeierstrassCurve.kernel_add_abscissa_notMem
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x₁ y₁ x₂ y₂ x₃ y₃ : Ksep}
    (h₁ : (E⁄Ksep).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄Ksep).toAffine.Nonsingular x₂ y₂)
    (h₃ : (E⁄Ksep).toAffine.Nonsingular x₃ y₃)
    (hx₁ : x₁ ∉ 𝒪) (hx₂ : x₂ ∉ 𝒪)
    (hadd : (Affine.Point.some x₁ y₁ h₁ : (E⁄Ksep).Point) +
      Affine.Point.some x₂ y₂ h₂ = Affine.Point.some x₃ y₃ h₃) :
    x₃ ∉ 𝒪 := by
  classical
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ :=
    WeierstrassCurve.baseChange_coeff_mem R K E Ksep 𝒪 h𝒪
  -- the sum is affine, so it is computed by the slope formulas
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (E⁄Ksep).toAffine.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    rw [Affine.Point.add_of_Y_eq hx hy] at hadd
    exact Affine.Point.some_ne_zero h₃ hadd.symm
  rw [Affine.Point.add_some hxy] at hadd
  injection hadd with hX hY
  set L := (E⁄Ksep).toAffine.slope x₁ x₂ y₁ y₂ with hLdef
  -- the negated-sum ordinate lies on the curve over `x₃`
  have hE₃ : (E⁄Ksep).toAffine.Equation x₃ (L * (x₃ - x₁) + y₁) := by
    have h0 := WeierstrassCurve.Affine.equation_negAdd h₁.1 h₂.1 hxy
    simp only [WeierstrassCurve.Affine.negAddY] at h0
    rw [← hLdef, hX] at h0
    exact h0
  -- the line of the addition law is deep
  obtain ⟨hc0, hvLc, hvc⟩ := WeierstrassCurve.kernel_slope_facts 𝒪 (E⁄Ksep)
    ha₁ ha₂ ha₃ ha₄ ha₆ h₁.1 h₂.1 hx₁ hx₂ hxy hLdef rfl
  have hE₃' : (E⁄Ksep).toAffine.Equation x₃ (L * x₃ + (y₁ - L * x₁)) := by
    rwa [show L * (x₃ - x₁) + y₁ = L * x₃ + (y₁ - L * x₁) from by ring] at hE₃
  exact WeierstrassCurve.abscissa_notMem_of_line_deep 𝒪 (E⁄Ksep)
    ha₁ ha₂ ha₃ ha₄ ha₆ hE₃' hvLc hvc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsElliptic] [IsSepClosure K Ksep] [DecidableEq Ksep] in
/-- **The tangent numerator is a unit where `ψ₂` degenerates** (glue for the
congruent-points leaf, the good-reduction input): for an integral point of the
base-changed minimal model whose `ψ₂ = 2y + a₁x + a₃` falls into the maximal ideal of
`𝒪`, the other partial derivative `3x² + 2a₂x + a₄ - a₁y` is a unit of `𝒪` — otherwise
the residues `(x̄, ȳ)` would be a singular point of the reduced curve, which good
reduction (`Δ̄ ≠ 0`, through `hasGoodReduction_iff_isElliptic_reduction`) forbids. -/
theorem WeierstrassCurve.val_tangent_numerator_eq_one
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x y : Ksep} (hx : x ∈ 𝒪) (hy : y ∈ 𝒪)
    (hE : (E⁄Ksep).toAffine.Equation x y)
    (hψ : 𝒪.valuation (2 * y + (E⁄Ksep).a₁ * x + (E⁄Ksep).a₃) < 1) :
    𝒪.valuation (3 * x ^ 2 + 2 * (E⁄Ksep).a₂ * x + (E⁄Ksep).a₄ - (E⁄Ksep).a₁ * y)
      = 1 := by
  classical
  haveI : E.IsIntegral R := inferInstance
  set φ := WeierstrassCurve.RtoO R K Ksep 𝒪 h𝒪
  set ψm := IsLocalRing.ResidueField.map φ
  set Ered := (E.reduction R).map ψm
  haveI hredell : (E.reduction R).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  haveI : Ered.IsElliptic := inferInstanceAs (((E.reduction R).map ψm).IsElliptic)
  have hEeq : ((E.integralModel R)⁄K) = E :=
    WeierstrassCurve.baseChange_integralModel_eq R E
  -- identification of the coefficients, on both sides of `𝒪`
  have hcoe : ∀ r : R, ((φ r : 𝒪) : Ksep) = algebraMap K Ksep (algebraMap R K r) :=
    fun r => WeierstrassCurve.RtoO_coe R K Ksep 𝒪 h𝒪 r
  have hered : ∀ r : R, IsLocalRing.residue 𝒪 (φ r) = ψm (IsLocalRing.residue R r) :=
    fun r => (IsLocalRing.ResidueField.map_residue φ r).symm
  have hcoe₁ : ((φ ((E.integralModel R).a₁) : 𝒪) : Ksep) = (E⁄Ksep).a₁ := by
    rw [hcoe, show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]
    rfl
  have hcoe₂ : ((φ ((E.integralModel R).a₂) : 𝒪) : Ksep) = (E⁄Ksep).a₂ := by
    rw [hcoe, show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]
    rfl
  have hcoe₃ : ((φ ((E.integralModel R).a₃) : 𝒪) : Ksep) = (E⁄Ksep).a₃ := by
    rw [hcoe, show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]
    rfl
  have hcoe₄ : ((φ ((E.integralModel R).a₄) : 𝒪) : Ksep) = (E⁄Ksep).a₄ := by
    rw [hcoe, show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]
    rfl
  have hcoe₆ : ((φ ((E.integralModel R).a₆) : 𝒪) : Ksep) = (E⁄Ksep).a₆ := by
    rw [hcoe, show (E⁄Ksep) = (((E.integralModel R)⁄K)⁄Ksep) from by rw [hEeq]]
    rfl
  have hEreda₁ : Ered.a₁ = IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₁)) := by
    rw [hered]; rfl
  have hEreda₂ : Ered.a₂ = IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₂)) := by
    rw [hered]; rfl
  have hEreda₃ : Ered.a₃ = IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₃)) := by
    rw [hered]; rfl
  have hEreda₄ : Ered.a₄ = IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₄)) := by
    rw [hered]; rfl
  have hEreda₆ : Ered.a₆ = IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₆)) := by
    rw [hered]; rfl
  -- the `𝒪`-integral model of the point satisfies the `𝒪`-level equation
  have hE' := (WeierstrassCurve.Affine.equation_iff x y).mp hE
  have hEO : (⟨y, hy⟩ : 𝒪) ^ 2 + φ ((E.integralModel R).a₁) * ⟨x, hx⟩ * ⟨y, hy⟩
        + φ ((E.integralModel R).a₃) * ⟨y, hy⟩
      = (⟨x, hx⟩ : 𝒪) ^ 3 + φ ((E.integralModel R).a₂) * ⟨x, hx⟩ ^ 2
        + φ ((E.integralModel R).a₄) * ⟨x, hx⟩ + φ ((E.integralModel R).a₆) := by
    apply Subtype.ext
    push_cast
    rw [hcoe₁, hcoe₂, hcoe₃, hcoe₄, hcoe₆]
    exact hE'
  -- hence the residues satisfy the reduced curve's equation, which is nonsingular
  have hEredEq : Ered.toAffine.Equation (IsLocalRing.residue 𝒪 ⟨x, hx⟩)
      (IsLocalRing.residue 𝒪 ⟨y, hy⟩) := by
    rw [WeierstrassCurve.Affine.equation_iff, hEreda₁, hEreda₂, hEreda₃, hEreda₄,
      hEreda₆]
    have hres := congrArg (IsLocalRing.residue 𝒪) hEO
    simpa only [map_add, map_mul, map_pow] using hres
  have hns : Ered.toAffine.Nonsingular (IsLocalRing.residue 𝒪 ⟨x, hx⟩)
      (IsLocalRing.residue 𝒪 ⟨y, hy⟩) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEredEq
  -- the `ψ₂`-partial vanishes at the residues
  have hψO : (2 * ⟨y, hy⟩ + φ ((E.integralModel R).a₁) * ⟨x, hx⟩
      + φ ((E.integralModel R).a₃) : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have hc : ((2 * ⟨y, hy⟩ + φ ((E.integralModel R).a₁) * ⟨x, hx⟩
        + φ ((E.integralModel R).a₃) : 𝒪) : Ksep)
        = 2 * y + (E⁄Ksep).a₁ * x + (E⁄Ksep).a₃ := by
      push_cast
      rw [hcoe₁, hcoe₃]
      norm_cast
    rw [hc]
    exact hψ
  have hψres : IsLocalRing.residue 𝒪 (2 * ⟨y, hy⟩ + φ ((E.integralModel R).a₁) * ⟨x, hx⟩
      + φ ((E.integralModel R).a₃) : 𝒪) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hψO
  -- so the `X`-partial cannot also vanish there
  obtain ⟨-, hdisj⟩ := (WeierstrassCurve.Affine.nonsingular_iff' _ _).mp hns
  have hXne : Ered.a₁ * IsLocalRing.residue 𝒪 ⟨y, hy⟩
      - (3 * IsLocalRing.residue 𝒪 ⟨x, hx⟩ ^ 2
        + 2 * Ered.a₂ * IsLocalRing.residue 𝒪 ⟨x, hx⟩ + Ered.a₄) ≠ 0 := by
    refine hdisj.resolve_right fun hYne => hYne ?_
    rw [hEreda₁, hEreda₃]
    calc 2 * IsLocalRing.residue 𝒪 ⟨y, hy⟩
          + IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₁))
            * IsLocalRing.residue 𝒪 ⟨x, hx⟩
          + IsLocalRing.residue 𝒪 (φ ((E.integralModel R).a₃))
        = IsLocalRing.residue 𝒪 (2 * ⟨y, hy⟩ + φ ((E.integralModel R).a₁) * ⟨x, hx⟩
            + φ ((E.integralModel R).a₃) : 𝒪) := by
          simp only [map_add, map_mul, map_ofNat]
      _ = 0 := hψres
  -- the tangent numerator is integral with nonzero residue, hence a unit
  have hNres : IsLocalRing.residue 𝒪 (3 * ⟨x, hx⟩ ^ 2
      + 2 * φ ((E.integralModel R).a₂) * ⟨x, hx⟩ + φ ((E.integralModel R).a₄)
      - φ ((E.integralModel R).a₁) * ⟨y, hy⟩ : 𝒪) ≠ 0 := by
    intro h0
    apply hXne
    have hexp : IsLocalRing.residue 𝒪 (3 * ⟨x, hx⟩ ^ 2
        + 2 * φ ((E.integralModel R).a₂) * ⟨x, hx⟩ + φ ((E.integralModel R).a₄)
        - φ ((E.integralModel R).a₁) * ⟨y, hy⟩ : 𝒪)
        = 3 * IsLocalRing.residue 𝒪 ⟨x, hx⟩ ^ 2
          + 2 * Ered.a₂ * IsLocalRing.residue 𝒪 ⟨x, hx⟩ + Ered.a₄
          - Ered.a₁ * IsLocalRing.residue 𝒪 ⟨y, hy⟩ := by
      rw [hEreda₁, hEreda₂, hEreda₄]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination hexp - h0
  have hNnotmem : (3 * ⟨x, hx⟩ ^ 2 + 2 * φ ((E.integralModel R).a₂) * ⟨x, hx⟩
      + φ ((E.integralModel R).a₄) - φ ((E.integralModel R).a₁) * ⟨y, hy⟩ : 𝒪)
      ∉ IsLocalRing.maximalIdeal 𝒪 :=
    fun hmem => hNres (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hNcoe : ((3 * ⟨x, hx⟩ ^ 2 + 2 * φ ((E.integralModel R).a₂) * ⟨x, hx⟩
      + φ ((E.integralModel R).a₄) - φ ((E.integralModel R).a₁) * ⟨y, hy⟩ : 𝒪) : Ksep)
      = 3 * x ^ 2 + 2 * (E⁄Ksep).a₂ * x + (E⁄Ksep).a₄ - (E⁄Ksep).a₁ * y := by
    push_cast
    rw [hcoe₁, hcoe₂, hcoe₄]
    norm_cast
  rw [← hNcoe]
  refine le_antisymm ((𝒪.valuation_le_one_iff _).mpr (Subtype.mem _)) (not_lt.mp ?_)
  exact fun hlt => hNnotmem ((ValuationSubring.valuation_lt_one_iff 𝒪 _).mpr hlt)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsElliptic] [IsSepClosure K Ksep] in
/-- **Congruent distinct integral points differ by a kernel element** (PROVEN
2026-07-22; Silverman *AEC* VII.2.1-2 in coordinates, characteristic-free and
torsion-free): on the minimal model, if two DISTINCT affine points of `E(Kˢᵉᵖ)` have
integral coordinates with equal residues over a valuation subring `𝒪` of `Kˢᵉᵖ` above
`R`, then any affine value of their difference has non-integral abscissa ("the
difference lies in the kernel of reduction"). Proof, by the chord construction for
`(x₁, y₁) + (x₂, -y₂ - a₁x₂ - a₃)`: in every case the slope `L` satisfies `v L > 1`,
whence `x₃ = L² + a₁L - a₂ - x₁ - x₂` has `v x₃ = (v L)² > 1`
(`addX_notMem_of_one_lt_val_slope`). If `x₁ ≠ x₂` and `ψ₂(x₂, y₂) = 2y₂ + a₁x₂ + a₃`
is a unit, the slope numerator `y₁ + y₂ + a₁x₂ + a₃ ≡ ψ₂(x₂, y₂)` is a unit over the
maximal-ideal denominator `x₁ - x₂`. If `ψ₂(x₂, y₂) ∈ 𝔪`, the subtracted curve
equations factor the numerator as `(x₂ - x₁)G/(y₁ - y₂)` with
`G ≡ -(3x₂² + 2a₂x₂ + a₄ - a₁y₂) mod 𝔪` a unit by the residue curve's nonsingularity
(`val_tangent_numerator_eq_one`), so `v L = v G / v(y₁ - y₂) > 1`. If `x₁ = x₂` the
points differ by an ordinate flip, the difference is the double of `(x₁, y₁)`, the
tangent denominator is `y₁ - y₂ ∈ 𝔪 \ {0}` and the tangent numerator is again a unit
by the same nonsingularity input. -/
theorem WeierstrassCurve.kernel_sub_abscissa_notMem_of_residue_eq
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x₁ y₁ x₂ y₂ x₃ y₃ : Ksep}
    (h₁ : (E⁄Ksep).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄Ksep).toAffine.Nonsingular x₂ y₂)
    (h₃ : (E⁄Ksep).toAffine.Nonsingular x₃ y₃)
    (hne : (Affine.Point.some x₁ y₁ h₁ : (E⁄Ksep).Point) ≠ Affine.Point.some x₂ y₂ h₂)
    (hm₁ : x₁ ∈ 𝒪) (hm₂ : x₂ ∈ 𝒪) (hn₁ : y₁ ∈ 𝒪) (hn₂ : y₂ ∈ 𝒪)
    (hrx : IsLocalRing.residue 𝒪 ⟨x₁, hm₁⟩ = IsLocalRing.residue 𝒪 ⟨x₂, hm₂⟩)
    (hry : IsLocalRing.residue 𝒪 ⟨y₁, hn₁⟩ = IsLocalRing.residue 𝒪 ⟨y₂, hn₂⟩)
    (hsub : (Affine.Point.some x₁ y₁ h₁ : (E⁄Ksep).Point) -
      Affine.Point.some x₂ y₂ h₂ = Affine.Point.some x₃ y₃ h₃) :
    x₃ ∉ 𝒪 := by
  classical
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ :=
    WeierstrassCurve.baseChange_coeff_mem R K E Ksep 𝒪 h𝒪
  -- the residue congruences, as valuation bounds in `Kˢᵉᵖ`
  have hvxx : 𝒪.valuation (x₁ - x₂) < 1 := by
    have hmem : (⟨x₁, hm₁⟩ - ⟨x₂, hm₂⟩ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub]; exact sub_eq_zero.mpr hrx)
    simpa using (ValuationSubring.valuation_lt_one_iff 𝒪 _).mp hmem
  have hvyy : 𝒪.valuation (y₁ - y₂) < 1 := by
    have hmem : (⟨y₁, hn₁⟩ - ⟨y₂, hn₂⟩ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪 :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub]; exact sub_eq_zero.mpr hry)
    simpa using (ValuationSubring.valuation_lt_one_iff 𝒪 _).mp hmem
  -- the difference is an addition with the ordinate-flipped second point
  rw [sub_eq_add_neg, Affine.Point.neg_some] at hsub
  have hxy : ¬(x₁ = x₂ ∧
      y₁ = (E⁄Ksep).toAffine.negY x₂ ((E⁄Ksep).toAffine.negY x₂ y₂)) := by
    rintro ⟨hx, hy⟩
    rw [Affine.Point.add_of_Y_eq hx hy] at hsub
    exact Affine.Point.some_ne_zero h₃ hsub.symm
  rw [Affine.Point.add_some hxy] at hsub
  injection hsub with hX hY
  set L := (E⁄Ksep).toAffine.slope x₁ x₂ y₁ ((E⁄Ksep).toAffine.negY x₂ y₂) with hLdef
  -- in every case the slope has valuation `> 1`
  have hvL : 1 < 𝒪.valuation L := by
    by_cases hxx : x₁ = x₂
    · -- ordinate flip: the difference is the double of `(x₁, y₁)`
      have hy12 : y₁ ≠ y₂ := by
        intro h
        exact hne (by subst hxx; subst h; rfl)
      have hy1eq : y₁ = (E⁄Ksep).toAffine.negY x₂ y₂ :=
        (WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxx).resolve_left hy12
      have hyne : y₁ ≠ (E⁄Ksep).toAffine.negY x₂ ((E⁄Ksep).toAffine.negY x₂ y₂) :=
        fun h => hxy ⟨hxx, h⟩
      have hnegYeq : (E⁄Ksep).toAffine.negY x₁ y₁ = y₂ := by
        rw [hxx, hy1eq, WeierstrassCurve.Affine.negY_negY]
      have hD0 : y₁ - (E⁄Ksep).toAffine.negY x₁ y₁ ≠ 0 := by
        rw [hnegYeq]
        exact sub_ne_zero.mpr hy12
      have hslope : L * (y₁ - y₂)
          = 3 * x₁ ^ 2 + 2 * (E⁄Ksep).a₂ * x₁ + (E⁄Ksep).a₄ - (E⁄Ksep).a₁ * y₁ := by
        rw [hLdef, WeierstrassCurve.Affine.slope_of_Y_ne hxx hyne, ← hnegYeq]
        exact div_mul_cancel₀ _ hD0
      have hψ : 𝒪.valuation (2 * y₁ + (E⁄Ksep).a₁ * x₁ + (E⁄Ksep).a₃) < 1 := by
        have hψeq : 2 * y₁ + (E⁄Ksep).a₁ * x₁ + (E⁄Ksep).a₃ = y₁ - y₂ := by
          rw [← hnegYeq]
          simp only [WeierstrassCurve.Affine.negY]
          ring
        rw [hψeq]
        exact hvyy
      have hN := WeierstrassCurve.val_tangent_numerator_eq_one R K E Ksep 𝒪 h𝒪
        hm₁ hn₁ h₁.1 hψ
      exact ValuationSubring.one_lt_val_of_val_mul_eq_one 𝒪 hvyy
        (by rw [hslope]; exact hN)
    · -- chord: distinct abscissae with congruent residues
      have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hxx
      have hslope : L * (x₁ - x₂) = y₁ - (E⁄Ksep).toAffine.negY x₂ y₂ := by
        rw [hLdef, WeierstrassCurve.Affine.slope_of_X_ne hxx]
        exact div_mul_cancel₀ _ hx12
      set ψ := 2 * y₂ + (E⁄Ksep).a₁ * x₂ + (E⁄Ksep).a₃ with hψdef
      have hNum : y₁ - (E⁄Ksep).toAffine.negY x₂ y₂ = ψ + (y₁ - y₂) := by
        rw [hψdef]
        simp only [WeierstrassCurve.Affine.negY]
        ring
      by_cases hψm : 𝒪.valuation ψ < 1
      · -- `ψ₂` degenerates: route through the subtracted-equations factorization
        have hN₂ := WeierstrassCurve.val_tangent_numerator_eq_one R K E Ksep 𝒪 h𝒪
          hm₂ hn₂ h₂.1 (hψdef ▸ hψm)
        have hE₁' := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.1
        have hE₂' := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂.1
        have hGid : (y₁ - y₂) * (y₁ - (E⁄Ksep).toAffine.negY x₂ y₂)
            = (x₂ - x₁) * ((E⁄Ksep).a₁ * y₁ - (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2)
              - (E⁄Ksep).a₂ * (x₂ + x₁) - (E⁄Ksep).a₄) := by
          simp only [WeierstrassCurve.Affine.negY]
          linear_combination hE₁' - hE₂'
        have hGval : 𝒪.valuation ((E⁄Ksep).a₁ * y₁ - (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2)
            - (E⁄Ksep).a₂ * (x₂ + x₁) - (E⁄Ksep).a₄) = 1 := by
          have hvxx' : 𝒪.valuation (x₂ - x₁) < 1 := by
            rw [show x₂ - x₁ = -(x₁ - x₂) from by ring, Valuation.map_neg]
            exact hvxx
          have herr : (E⁄Ksep).a₁ * y₁ - (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2)
              - (E⁄Ksep).a₂ * (x₂ + x₁) - (E⁄Ksep).a₄
              = -(3 * x₂ ^ 2 + 2 * (E⁄Ksep).a₂ * x₂ + (E⁄Ksep).a₄ - (E⁄Ksep).a₁ * y₂)
                + ((E⁄Ksep).a₁ * (y₁ - y₂) + (2 * x₂ + x₁) * (x₂ - x₁)
                  + (E⁄Ksep).a₂ * (x₂ - x₁)) := by
            ring
          have hverr : 𝒪.valuation ((E⁄Ksep).a₁ * (y₁ - y₂) + (2 * x₂ + x₁) * (x₂ - x₁)
              + (E⁄Ksep).a₂ * (x₂ - x₁)) < 1 := by
            have h2mem : (2 : Ksep) ∈ 𝒪 := by
              rw [show (2 : Ksep) = 1 + 1 from by norm_num]
              exact add_mem (one_mem 𝒪) (one_mem 𝒪)
            refine 𝒪.valuation.map_add_lt (𝒪.valuation.map_add_lt ?_ ?_) ?_
            · exact 𝒪.val_mul_lt_one_of_mem_of_lt ha₁ hvyy
            · exact 𝒪.val_mul_lt_one_of_mem_of_lt
                (add_mem (mul_mem h2mem hm₂) hm₁) hvxx'
            · exact 𝒪.val_mul_lt_one_of_mem_of_lt ha₂ hvxx'
          rw [herr, 𝒪.valuation.map_add_eq_of_lt_left
            (by rw [Valuation.map_neg, hN₂]; exact hverr), Valuation.map_neg, hN₂]
        have hLG : L * (y₁ - y₂)
            = -((E⁄Ksep).a₁ * y₁ - (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2)
              - (E⁄Ksep).a₂ * (x₂ + x₁) - (E⁄Ksep).a₄) := by
          apply mul_right_cancel₀ hx12
          linear_combination (y₁ - y₂) * hslope + hGid
        exact ValuationSubring.one_lt_val_of_val_mul_eq_one 𝒪 hvyy
          (by rw [hLG, Valuation.map_neg]; exact hGval)
      · -- `ψ₂` is a unit: the slope numerator is a unit outright
        have h2mem : (2 : Ksep) ∈ 𝒪 := by
          rw [show (2 : Ksep) = 1 + 1 from by norm_num]
          exact add_mem (one_mem 𝒪) (one_mem 𝒪)
        have hψ1 : 𝒪.valuation ψ = 1 := by
          refine le_antisymm ((𝒪.valuation_le_one_iff _).mpr ?_) (not_lt.mp hψm)
          rw [hψdef]
          exact add_mem (add_mem (mul_mem h2mem hn₂) (mul_mem ha₁ hm₂)) ha₃
        have hNumval : 𝒪.valuation (y₁ - (E⁄Ksep).toAffine.negY x₂ y₂) = 1 := by
          rw [hNum, 𝒪.valuation.map_add_eq_of_lt_left (by rw [hψ1]; exact hvyy), hψ1]
        exact ValuationSubring.one_lt_val_of_val_mul_eq_one 𝒪 hvxx
          (by rw [hslope]; exact hNumval)
  -- endgame: the `addX` over a steep slope is non-integral
  have hnot := WeierstrassCurve.addX_notMem_of_one_lt_val_slope 𝒪 (E⁄Ksep)
    ha₁ ha₂ hm₁ hm₂ hvL
  rw [← hX]
  exact hnot

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure K Ksep] in
/-- **Reduction is injective on prime-power torsion, deep cases** (dévissage assembly
PROVEN 2026-07-22; rests on the two characteristic-free kernel-of-reduction leaves
above): two `p ^ k`-torsion points of `E(Kˢᵉᵖ)` with integral coordinates and congruent
residues in a valuation subring `𝒪` above `R` are equal, for `p ^ k` invertible in `R`
and either `p = 2` or `k ≥ 2` (the case `p` odd, `k = 1` is PROVEN separately — via
`WeierstrassCurve.torsion_abscissa_residue_ne` and
`WeierstrassCurve.torsion_ordinate_eq_of_residue_eq` in
`Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction` — and is consumed by the
Néron–Ogg–Shafarevich assembly below through `torsion_unramified_of_good_reduction`,
so it is excluded here; the proof written here would in fact cover it too once the two
kernel leaves are closed).

The dévissage: if the points differ, their difference `T ≠ 0` is `p ^ k`-torsion and
lies in the kernel of reduction (`kernel_sub_abscissa_notMem_of_residue_eq`), every
nonzero multiple of `T` stays in the kernel (`kernel_add_abscissa_notMem`, by induction
on the multiplier), and the last nonzero point `T' = p ^ j • T` of the multiplication
tower is a nonzero `p`-torsion point in the kernel — but `p`-torsion abscissas are
integral (`torsion_abscissa_mem`, as `p` is a unit in `R`): contradiction. -/
theorem WeierstrassCurve.torsion_eq_of_residue_eq_of_prime_pow_deep
    (p k : ℕ) (hp : p.Prime) (hpk : IsUnit ((p ^ k : ℕ) : R)) (hk : k ≠ 0)
    (_hdeep : p = 2 ∨ 2 ≤ k)
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x₁ y₁ x₂ y₂ : Ksep}
    (h₁ : (E⁄Ksep).toAffine.Nonsingular x₁ y₁)
    (h₂ : (E⁄Ksep).toAffine.Nonsingular x₂ y₂)
    (ht₁ : ((p ^ k : ℕ) : ℤ) • (Affine.Point.some x₁ y₁ h₁ : (E⁄Ksep).Point) = 0)
    (ht₂ : ((p ^ k : ℕ) : ℤ) • (Affine.Point.some x₂ y₂ h₂ : (E⁄Ksep).Point) = 0)
    (hm₁ : x₁ ∈ 𝒪) (hm₂ : x₂ ∈ 𝒪) (hn₁ : y₁ ∈ 𝒪) (hn₂ : y₂ ∈ 𝒪)
    (hrx : IsLocalRing.residue 𝒪 ⟨x₁, hm₁⟩ = IsLocalRing.residue 𝒪 ⟨x₂, hm₂⟩)
    (hry : IsLocalRing.residue 𝒪 ⟨y₁, hn₁⟩ = IsLocalRing.residue 𝒪 ⟨y₂, hn₂⟩) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  classical
  by_contra hcon
  -- the two points are distinct
  have hPne : (Affine.Point.some x₁ y₁ h₁ : (E⁄Ksep).Point) ≠
      Affine.Point.some x₂ y₂ h₂ := by
    intro heq
    injection heq with e1 e2
    exact hcon ⟨e1, e2⟩
  -- their difference is a nonzero `p ^ k`-torsion point
  set T : (E⁄Ksep).Point :=
    Affine.Point.some x₁ y₁ h₁ - Affine.Point.some x₂ y₂ h₂ with hTdef
  have hT0 : T ≠ 0 := sub_ne_zero.mpr hPne
  have hTtor : ((p ^ k : ℕ) : ℤ) • T = 0 := by
    rw [hTdef, smul_sub, ht₁, ht₂, sub_zero]
  -- `T` is affine with non-integral abscissa: it lies in the kernel of reduction
  obtain ⟨xT, yT, hT3, hTeq, hxT⟩ : ∃ (xT yT : Ksep)
      (hT3 : (E⁄Ksep).toAffine.Nonsingular xT yT),
      T = Affine.Point.some xT yT hT3 ∧ xT ∉ 𝒪 := by
    cases hTc : T with
    | zero => exact absurd hTc hT0
    | @some xT yT hT3 =>
      refine ⟨xT, yT, hT3, rfl, ?_⟩
      refine WeierstrassCurve.kernel_sub_abscissa_notMem_of_residue_eq R K E Ksep 𝒪 h𝒪
        h₁ h₂ hT3 hPne hm₁ hm₂ hn₁ hn₂ hrx hry ?_
      rw [← hTdef]
      exact hTc
  -- every nonzero multiple of `T` stays in the kernel of reduction
  have hmult : ∀ n : ℕ, 1 ≤ n → ∀ {xS yS : Ksep}
      (hS : (E⁄Ksep).toAffine.Nonsingular xS yS),
      (n : ℤ) • T = Affine.Point.some xS yS hS → xS ∉ 𝒪 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro xS yS hS hSeq
      rw [Nat.cast_one, one_smul, hTeq] at hSeq
      injection hSeq with e1 e2
      rw [← e1]
      exact hxT
    | succ n _ ih =>
      intro xS yS hS hSeq
      have hstep : ((n : ℤ) + 1) • T = (n : ℤ) • T + T := by
        rw [add_smul, one_smul]
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, hstep] at hSeq
      cases hnT : (n : ℤ) • T with
      | zero =>
        rw [hnT, show (Affine.Point.zero : (E⁄Ksep).Point) = 0 from rfl,
          zero_add, hTeq] at hSeq
        injection hSeq with e1 e2
        rw [← e1]
        exact hxT
      | @some xn yn hn3 =>
        have hxn : xn ∉ 𝒪 := ih hn3 hnT
        rw [hnT, hTeq] at hSeq
        exact WeierstrassCurve.kernel_add_abscissa_notMem R K E Ksep 𝒪 h𝒪
          hn3 hT3 hS hxn hxT hSeq
  -- the multiplication tower: the last nonzero `p`-power multiple of `T`
  have hex : ∃ j : ℕ, ((p ^ j : ℕ) : ℤ) • T = 0 := ⟨k, hTtor⟩
  set j₁ := Nat.find hex
  have hj₁spec : ((p ^ j₁ : ℕ) : ℤ) • T = 0 := Nat.find_spec hex
  have hj₁0 : j₁ ≠ 0 := by
    intro h0
    rw [h0] at hj₁spec
    simp only [pow_zero, Nat.cast_one, one_smul] at hj₁spec
    exact hT0 hj₁spec
  have hj₁pred : ((p ^ (j₁ - 1) : ℕ) : ℤ) • T ≠ 0 :=
    Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hj₁0) one_pos)
  set T' : (E⁄Ksep).Point := ((p ^ (j₁ - 1) : ℕ) : ℤ) • T with hT'def
  -- `T'` is a nonzero `p`-torsion point
  have hT'tor : ((p : ℕ) : ℤ) • T' = 0 := by
    rw [hT'def, smul_smul, ← Nat.cast_mul, ← pow_succ',
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj₁0)]
    exact hj₁spec
  cases hT'c : T' with
  | zero => exact hj₁pred (hT'def ▸ hT'c)
  | @some xT' yT' hT'3 =>
    -- its abscissa is NOT integral: it is a nonzero multiple of `T`
    have hxT'notMem : xT' ∉ 𝒪 := by
      refine hmult (p ^ (j₁ - 1)) ?_ hT'3 (hT'def ▸ hT'c)
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
    -- but `p`-torsion abscissas ARE integral, since `p` is a unit in `R`
    have hpu : IsUnit ((p : ℕ) : R) := by
      have h2 : IsUnit (((p : ℕ) : R) ^ k) := by
        have := hpk
        rwa [Nat.cast_pow] at this
      exact (isUnit_pow_iff hk).mp h2
    haveI : NeZero ((p : ℕ) : IsLocalRing.ResidueField R) := by
      have h2 : IsUnit (IsLocalRing.residue R ((p : ℕ) : R)) :=
        hpu.map (IsLocalRing.residue R)
      rw [map_natCast] at h2
      exact ⟨h2.ne_zero⟩
    have hT'torsome : ((p : ℕ) : ℤ) •
        (Affine.Point.some xT' yT' hT'3 : (E⁄Ksep).Point) = 0 := by
      rw [← hT'c]
      exact hT'tor
    exact hxT'notMem (WeierstrassCurve.torsion_abscissa_mem R K E p Ksep 𝒪
      h𝒪 hT'3 hT'torsome)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsSepClosure K Ksep] in
/-- **Prime-power Néron–Ogg–Shafarevich, easy direction** (assembly PROVEN 2026-07-22;
rests on the injectivity leaf `torsion_eq_of_residue_eq_of_prime_pow_deep` for `p = 2`
or `k ≥ 2`): if `E` has good reduction over `R` and the prime power `p ^ k` is
invertible in `R`, every inertia subgroup above `R` acts trivially on the
`p ^ k`-torsion of `E(Kˢᵉᵖ)`. For `k = 1` and `p` odd this is discharged by the proven
`WeierstrassCurve.torsion_unramified_of_good_reduction`
(`Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction`, consumable here since the
2026-07-22 import untangling): torsion coordinates are integral over any valuation
subring `𝒪` of `Kˢᵉᵖ` above `R`, inertia fixes their residues, and reduction is
injective on the prime torsion through the residue curve's separability. In the
remaining cases the same three-step assembly is written out below, with the
injectivity step supplied by the sorried deep leaf. -/
theorem WeierstrassCurve.torsion_inertia_fixes_of_prime_pow_isUnit
    (p k : ℕ) (hp : p.Prime) (hpk : IsUnit ((p ^ k : ℕ) : R))
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup K,
      ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ),
        Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P := by
  classical
  intro σ hσ P hP
  -- trivial case `k = 0`: the `1`-torsion is the zero subgroup
  rcases eq_or_ne k 0 with rfl | hk0
  · have h1 : ((p ^ 0 : ℕ) : ℤ) • P = 0 := hP
    have hP0 : P = 0 := by simpa using h1
    rw [hP0]
    exact map_zero _
  by_cases hcase : Odd p ∧ k = 1
  -- the proven case: odd prime torsion
  · obtain ⟨hodd, rfl⟩ := hcase
    have hpu : IsUnit ((p : ℕ) : R) := by rwa [pow_one] at hpk
    haveI : NeZero ((p : ℕ) : IsLocalRing.ResidueField R) := by
      have h2 : IsUnit (IsLocalRing.residue R ((p : ℕ) : R)) :=
        hpu.map (IsLocalRing.residue R)
      rw [map_natCast] at h2
      exact ⟨h2.ne_zero⟩
    have hP' : P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point ((p : ℕ) : ℤ) := by
      have h1 : ((p ^ 1 : ℕ) : ℤ) • P = 0 := hP
      rw [pow_one] at h1
      exact h1
    exact WeierstrassCurve.torsion_unramified_of_good_reduction R K E p Ksep 𝒪
      hp hodd h𝒪 σ hσ P hP'
  -- the deep cases `p = 2` or `k ≥ 2`: integrality + inertia congruence + injectivity
  · have hdeep : p = 2 ∨ 2 ≤ k := by
      rcases hp.eq_two_or_odd' with h2 | hodd
      · exact Or.inl h2
      · have hk1 : k ≠ 1 := fun h => hcase ⟨hodd, h⟩
        exact Or.inr (by omega)
    haveI : NeZero ((p ^ k : ℕ) : IsLocalRing.ResidueField R) := by
      have h2 : IsUnit (IsLocalRing.residue R ((p ^ k : ℕ) : R)) :=
        hpk.map (IsLocalRing.residue R)
      rw [map_natCast] at h2
      exact ⟨h2.ne_zero⟩
    haveI : (E⁄Ksep).IsElliptic :=
      inferInstanceAs ((E.map (algebraMap K Ksep)).IsElliptic)
    -- inertia fixes residues in `𝒪`
    have hres : ∀ z : 𝒪, IsLocalRing.residue 𝒪 (σ • z) =
        IsLocalRing.residue 𝒪 z := by
      intro z
      rw [IsLocalRing.ResidueField.residue_smul]
      have h1 := MonoidHom.mem_ker.mp hσ
      calc (σ : 𝒪.decompositionSubgroup K) • IsLocalRing.residue 𝒪 z
          = (MulSemiringAction.toRingAut (𝒪.decompositionSubgroup K)
              (IsLocalRing.ResidueField 𝒪) σ)
              (IsLocalRing.residue 𝒪 z) := rfl
        _ = IsLocalRing.residue 𝒪 z := by rw [h1]; rfl
    have hcoe : ∀ z : 𝒪, ((σ • z : 𝒪) : Ksep) =
        ((σ : Ksep ≃ₐ[K] Ksep)).toAlgHom (z : Ksep) := fun z => rfl
    have hPtor : ((p ^ k : ℕ) : ℤ) • P = 0 := hP
    cases P with
    | zero => rfl
    | @some x y h =>
      have htor : ((p ^ k : ℕ) : ℤ) •
          (Affine.Point.some x y h : (E⁄Ksep).Point) = 0 := hPtor
      -- the coordinates are integral over `𝒪`
      have hxm := WeierstrassCurve.torsion_abscissa_mem R K E (p ^ k) Ksep 𝒪
        h𝒪 h htor
      have hym := WeierstrassCurve.torsion_ordinate_mem R K E (p ^ k) Ksep 𝒪
        h𝒪 h htor
      set σf := ((σ : Ksep ≃ₐ[K] Ksep)).toAlgHom
      rw [Affine.Point.map_some]
      have hns' : (E⁄Ksep).toAffine.Nonsingular (σf x) (σf y) :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := E)
          σf.injective x y).mpr (show (E⁄Ksep).Nonsingular x y from h)
      -- the image is torsion
      have h1 : Affine.Point.map σf (Affine.Point.some x y h) =
          (Affine.Point.some (σf x) (σf y) hns' : (E⁄Ksep).Point) :=
        Affine.Point.map_some _ h
      have hmaptor : ((p ^ k : ℕ) : ℤ) • (Affine.Point.some (σf x) (σf y) hns' :
          (E⁄Ksep).Point) = 0 := by
        rw [← h1, ← map_zsmul, htor, map_zero]
      -- memberships of the image coordinates
      have hσxm : σf x ∈ 𝒪 := by
        have := hcoe ⟨x, hxm⟩
        rw [← this]
        exact Subtype.mem _
      have hσym : σf y ∈ 𝒪 := by
        have := hcoe ⟨y, hym⟩
        rw [← this]
        exact Subtype.mem _
      -- inertia gives congruent residues
      have hrx : IsLocalRing.residue 𝒪 ⟨σf x, hσxm⟩ =
          IsLocalRing.residue 𝒪 ⟨x, hxm⟩ := by
        have h2 := hres ⟨x, hxm⟩
        rwa [show (σ • (⟨x, hxm⟩ : 𝒪)) = ⟨σf x, hσxm⟩ from
          Subtype.ext (hcoe ⟨x, hxm⟩)] at h2
      have hry : IsLocalRing.residue 𝒪 ⟨σf y, hσym⟩ =
          IsLocalRing.residue 𝒪 ⟨y, hym⟩ := by
        have h2 := hres ⟨y, hym⟩
        rwa [show (σ • (⟨y, hym⟩ : 𝒪)) = ⟨σf y, hσym⟩ from
          Subtype.ext (hcoe ⟨y, hym⟩)] at h2
      -- the injectivity leaf identifies the image with the original point
      obtain ⟨hxeq, hyeq⟩ :=
        WeierstrassCurve.torsion_eq_of_residue_eq_of_prime_pow_deep R K E Ksep
          p k hp hpk hk0 hdeep 𝒪 h𝒪 hns' h hmaptor htor hσxm hxm hσym hym hrx hry
      congr 1

omit [IsSepClosure K Ksep] in
/-- **Composite Néron–Ogg–Shafarevich from its prime-power core** (PROVEN 2026-07-22):
for `m` invertible in `R`, every inertia subgroup above `R` acts trivially on the
`m`-torsion. Strong induction on `m`: split off a maximal prime power `m = p ^ k * m'`
with `p ∤ m'`; a Bézout identity `u * p ^ k + v * m' = 1` splits an `m`-torsion point
`P` as `P = (v * m') • P + (u * p ^ k) • P`, a sum of a `p ^ k`-torsion point and an
`m'`-torsion point, each fixed by inertia (the prime-power leaf above, resp. the
inductive hypothesis at `m' < m`), and `Affine.Point.map` is additive. -/
theorem WeierstrassCurve.torsion_inertia_fixes_of_isUnit
    (m : ℕ) (hm : IsUnit (m : R))
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup K,
      ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ),
        Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P := by
  intro σ hσ
  revert hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm P hP
    rcases eq_or_ne m 0 with rfl | hm0
    · exact absurd (by exact_mod_cast hm) (not_isUnit_zero (M₀ := R))
    rcases eq_or_ne m 1 with rfl | hm1
    · have h1 : ((1 : ℕ) : ℤ) • P = 0 := hP
      have hP0 : P = 0 := by simpa using h1
      rw [hP0]
      exact map_zero _
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨k, m', hpm', hfact⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hfact
      exact hpm' (hfact ▸ hpd)
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hfact
      exact hm0 hfact
    have hm'lt : m' < m := by
      rw [hfact]
      calc m' = 1 * m' := (one_mul m').symm
      _ < p ^ k * m' := (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hm'0)).mpr
          (one_lt_pow' hp.one_lt hk0)
    have hcast : ((m : ℕ) : R) = ((p ^ k : ℕ) : R) * ((m' : ℕ) : R) := by
      rw [hfact]; push_cast; ring
    have hpku : IsUnit ((p ^ k : ℕ) : R) := isUnit_of_mul_isUnit_left (hcast ▸ hm)
    have hm'u : IsUnit ((m' : ℕ) : R) := isUnit_of_mul_isUnit_right (hcast ▸ hm)
    obtain ⟨u, v, huv⟩ : IsCoprime ((p ^ k : ℕ) : ℤ) ((m' : ℕ) : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_iff_gcd_eq_one.mp
          (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpm')))
    have hPm : ((m : ℕ) : ℤ) • P = 0 := hP
    have hmZ : ((m : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) * ((m' : ℕ) : ℤ) := by
      rw [hfact]; push_cast; ring
    have hP₁mem : (v * ((m' : ℕ) : ℤ)) • P ∈
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ) := by
      show ((p ^ k : ℕ) : ℤ) • (v * ((m' : ℕ) : ℤ)) • P = 0
      rw [smul_smul,
        show ((p ^ k : ℕ) : ℤ) * (v * ((m' : ℕ) : ℤ)) =
          v * (((p ^ k : ℕ) : ℤ) * ((m' : ℕ) : ℤ)) by ring,
        ← hmZ, mul_smul, hPm, smul_zero]
    have hP₂mem : (u * ((p ^ k : ℕ) : ℤ)) • P ∈
        AddSubgroup.torsionBy (E⁄Ksep).Point ((m' : ℕ) : ℤ) := by
      show ((m' : ℕ) : ℤ) • (u * ((p ^ k : ℕ) : ℤ)) • P = 0
      rw [smul_smul,
        show ((m' : ℕ) : ℤ) * (u * ((p ^ k : ℕ) : ℤ)) =
          u * (((p ^ k : ℕ) : ℤ) * ((m' : ℕ) : ℤ)) by ring,
        ← hmZ, mul_smul, hPm, smul_zero]
    have hsplit : (v * ((m' : ℕ) : ℤ)) • P + (u * ((p ^ k : ℕ) : ℤ)) • P = P := by
      rw [← add_smul,
        show v * ((m' : ℕ) : ℤ) + u * ((p ^ k : ℕ) : ℤ) =
          u * ((p ^ k : ℕ) : ℤ) + v * ((m' : ℕ) : ℤ) by ring,
        huv, one_smul]
    have f1 := WeierstrassCurve.torsion_inertia_fixes_of_prime_pow_isUnit R K E Ksep
      p k hp hpku 𝒪 h𝒪 σ hσ _ hP₁mem
    have f2 := ih m' hm'lt hm'u _ hP₂mem
    calc Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P
        = Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom
            ((v * ((m' : ℕ) : ℤ)) • P + (u * ((p ^ k : ℕ) : ℤ)) • P) := by rw [hsplit]
      _ = Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom ((v * ((m' : ℕ) : ℤ)) • P) +
            Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom
              ((u * ((p ^ k : ℕ) : ℤ)) • P) := map_add _ _ _
      _ = (v * ((m' : ℕ) : ℤ)) • P + (u * ((p ^ k : ℕ) : ℤ)) • P := by rw [f1, f2]
      _ = P := hsplit

/-!
### The Grothendieck Galois correspondence for a finite-quotient Galois module

The curve-independent core `exists_finiteQuotient_galoisModule_etale_package` below is
attacked by the classical construction: for a finite abelian group `A` with an action
`ρ` of the finite Galois group `Gal(L/K₀)`, the functions algebra is the `K₀`-algebra
of equivariant maps `A → L` (`galoisEquivariantAlgebra`). PROVEN here: it is finite
over `K₀` (a subspace of the finite-dimensional `A → L`); it is étale over `K₀` (every
element is annihilated by a squarefree product of separable minimal polynomials, so
every residue field of this — automatically Artinian and reduced — algebra is a
separable extension of `K₀`, and a finite product of separable extensions is formally
étale by `Algebra.FormallyEtale` machinery); the evaluation `Ω`-points at distinct
elements of `A` are distinct, because equivariant functions separate the elements of
`A` (on distinct orbits: an orbit indicator valued in the fixed field of the
stabilizer; within one orbit: a fixed-field element moved by the connecting
automorphism, which exists by the fundamental theorem of Galois theory
`IntermediateField.fixingSubgroup_fixedField`); and the Galois equivariance of
evaluation. The remaining SORRIED leaves are `galoisEquivariantEval_surjective` and
`exists_hopfAlgebra_galoisEquivariantAlgebra` (see their docstrings); the
assembly of the package from the two leaves is proven.
-/

section GaloisEtalePackage

variable {K₀ : Type*} [Field K₀]
variable {Ω : Type*} [Field Ω] [Algebra K₀ Ω]
variable {A : Type*} [AddCommGroup A]
variable (L : IntermediateField K₀ Ω) [FiniteDimensional K₀ L] [IsGalois K₀ L]
variable (ρ : (L ≃ₐ[K₀] L) →* AddMonoid.End A)

/-- **The equivariant-functions algebra** of a `Gal(L/K₀)`-module `A`: the
`K₀`-subalgebra of `A → L` of functions `f` with `f (ρ g a) = g (f a)` — the functions
algebra of the form of the constant group scheme on `A` twisted by `ρ`, realized inside
its split form `A → L`. -/
def galoisEquivariantAlgebra : Subalgebra K₀ (A → L) where
  carrier := {f | ∀ (g : L ≃ₐ[K₀] L) (a : A), f (ρ g a) = g (f a)}
  mul_mem' := fun hf hg g a => by
    simp only [Pi.mul_apply, map_mul, hf g a, hg g a]
  one_mem' := fun g a => by simp only [Pi.one_apply, map_one]
  add_mem' := fun hf hg g a => by
    simp only [Pi.add_apply, map_add, hf g a, hg g a]
  zero_mem' := fun g a => by simp only [Pi.zero_apply, map_zero]
  algebraMap_mem' := fun r g a => by
    simp only [Pi.algebraMap_apply, AlgEquiv.commutes]

/-- **Evaluation at an element of `A`**: the `Ω`-point of the equivariant-functions
algebra given by evaluating at `a` and embedding `L` into `Ω`. (Glue for the package
assembly; the injectivity is proven below, the surjectivity is the sorried leaf
`galoisEquivariantEval_surjective`.) -/
def galoisEquivariantEval (a : A) : galoisEquivariantAlgebra L ρ →ₐ[K₀] Ω :=
  (IsScalarTower.toAlgHom K₀ L Ω).comp
    ((Pi.evalAlgHom K₀ (fun _ : A => L) a).comp (galoisEquivariantAlgebra L ρ).val)

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
theorem galoisEquivariantEval_apply (a : A) (f : galoisEquivariantAlgebra L ρ) :
    galoisEquivariantEval L ρ a f = algebraMap L Ω ((f : A → L) a) := rfl

omit [FiniteDimensional K₀ ↥L] in
/-- **Galois equivariance of evaluation** (PROVEN; glue for the package assembly):
postcomposing the evaluation at `a` with `σ : Gal(Ω/K₀)` is the evaluation at the image
of `a` under the restriction of `σ` to `L`, because the entries of an equivariant
function transform by the very same rule. -/
theorem algEquiv_comp_galoisEquivariantEval (σ : Ω ≃ₐ[K₀] Ω) (a : A) :
    σ.toAlgHom.comp (galoisEquivariantEval L ρ a) =
      galoisEquivariantEval L ρ
        (ρ (AlgEquiv.restrictNormalHom (F := K₀) (K₁ := Ω) L σ) a) := by
  apply AlgHom.ext
  rintro ⟨f, hf⟩
  show σ (algebraMap L Ω (f a)) =
    algebraMap L Ω (f (ρ (AlgEquiv.restrictNormalHom (F := K₀) (K₁ := Ω) L σ) a))
  rw [hf, IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
    AlgEquiv.restrictNormalHom_apply]

instance galoisEquivariantAlgebra_finite [Finite A] :
    Module.Finite K₀ (galoisEquivariantAlgebra L ρ) := by
  haveI := Fintype.ofFinite A
  haveI : Module.Finite K₀ (A → L) := Module.Finite.pi
  infer_instance

instance galoisEquivariantAlgebra_isReduced :
    IsReduced (galoisEquivariantAlgebra L ρ) :=
  ⟨fun x hx => by
    obtain ⟨n, hn⟩ := hx
    have h0 : (x : A → L) ^ n = 0 := by
      simpa using congrArg Subtype.val hn
    have hz := IsReduced.eq_zero (x : A → L) ⟨n, h0⟩
    exact Subtype.ext (by simpa using hz)⟩

omit [FiniteDimensional K₀ ↥L] in
/-- **A separable annihilator for every equivariant function** (PROVEN; feeds the
étale-ness of the equivariant-functions algebra): the product of the distinct minimal
polynomials of the (finitely many) entries — distinct monic irreducibles are coprime,
so the product of these separable polynomials is separable, and it kills every entry,
hence the function. -/
theorem galoisEquivariantAlgebra_exists_separable_annihilator [Finite A]
    (x : galoisEquivariantAlgebra L ρ) :
    ∃ P : Polynomial K₀, P.Separable ∧ Polynomial.aeval x P = 0 := by
  classical
  haveI := Fintype.ofFinite A
  have hint : ∀ a : A, IsIntegral K₀ ((x : A → L) a) := fun a =>
    Algebra.IsIntegral.isIntegral _
  set T : Finset (Polynomial K₀) :=
    Finset.image (fun a => minpoly K₀ ((x : A → L) a)) Finset.univ with hT
  refine ⟨T.prod id, ?_, ?_⟩
  · refine Polynomial.separable_prod' ?_ ?_
    · intro p hp q hq hpq
      rw [hT] at hp hq
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hq
      refine (minpoly.irreducible (hint a)).coprime_iff_not_dvd.mpr fun hdvd => hpq ?_
      exact Polynomial.eq_of_monic_of_associated (minpoly.monic (hint a))
        (minpoly.monic (hint b))
        ((minpoly.irreducible (hint a)).associated_of_dvd
          (minpoly.irreducible (hint b)) hdvd)
    · intro p hp
      rw [hT] at hp
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
      exact Algebra.IsSeparable.isSeparable K₀ ((x : A → L) a)
  · have hval : (galoisEquivariantAlgebra L ρ).val (Polynomial.aeval x (T.prod id)) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]
      funext a
      show Pi.evalAlgHom K₀ (fun _ : A => L) a (Polynomial.aeval
        ((galoisEquivariantAlgebra L ρ).val x) (T.prod id)) = 0
      rw [← Polynomial.aeval_algHom_apply, map_prod]
      refine Finset.prod_eq_zero (i := minpoly K₀ ((x : A → L) a)) ?_ (minpoly.aeval _ _)
      rw [hT]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    exact Subtype.ext hval

/-- **The equivariant-functions algebra is formally étale** (PROVEN): it is a finite
reduced algebra over the field `K₀`, hence an Artinian ring, hence a finite product of
its residue fields; each residue field is generated by images of elements annihilated
by separable polynomials (the annihilator lemma above), hence is a separable extension
of `K₀`; and a finite product of separable extensions is formally étale. -/
theorem galoisEquivariantAlgebra_formallyEtale [Finite A] :
    Algebra.FormallyEtale K₀ (galoisEquivariantAlgebra L ρ) := by
  classical
  haveI : IsArtinianRing (galoisEquivariantAlgebra L ρ) :=
    isArtinian_of_tower K₀ inferInstance
  have hsep : ∀ m : MaximalSpectrum (galoisEquivariantAlgebra L ρ),
      Algebra.IsSeparable K₀ (↥(galoisEquivariantAlgebra L ρ) ⧸ m.asIdeal) := by
    intro m
    constructor
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective K₀ m.asIdeal y
    obtain ⟨P, hPsep, hP0⟩ :=
      galoisEquivariantAlgebra_exists_separable_annihilator L ρ x
    have h0 : Polynomial.aeval (Ideal.Quotient.mkₐ K₀ m.asIdeal x) P = 0 := by
      rw [Polynomial.aeval_algHom_apply, hP0, map_zero]
    exact hPsep.of_dvd (minpoly.dvd K₀ _ h0)
  rw [Algebra.FormallyEtale.iff_of_equiv
    ((IsArtinianRing.equivPi _).restrictScalars K₀), Algebra.FormallyEtale.pi_iff]
  intro m
  letI := Ideal.Quotient.field m.asIdeal
  haveI := hsep m
  exact Algebra.FormallyEtale.of_isSeparable K₀ _

/-- **The equivariant-functions algebra is étale** (PROVEN): formally étale by the
theorem above, and finitely presented because it is module-finite over the Noetherian
field `K₀`. -/
theorem galoisEquivariantAlgebra_etale [Finite A] :
    Algebra.Etale K₀ (galoisEquivariantAlgebra L ρ) := by
  haveI := galoisEquivariantAlgebra_formallyEtale L ρ
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

omit [IsGalois K₀ ↥L] in
/-- **Equivariant functions separate the elements of `A`** (PROVEN; the injectivity
half of the points bijection): on distinct orbits, an orbit indicator valued in the
fixed field of the stabilizer separates; within one orbit, some element of the fixed
field of the stabilizer is moved by the connecting automorphism — else that
automorphism would lie in the fixing subgroup of the fixed field, which is the
stabilizer itself by the fundamental theorem of Galois theory
(`IntermediateField.fixingSubgroup_fixedField`). -/
theorem galoisEquivariantAlgebra_separates {a b : A} (hab : a ≠ b) :
    ∃ f ∈ galoisEquivariantAlgebra L ρ, f a ≠ f b := by
  classical
  have hmulapp : ∀ (φ ψ : AddMonoid.End A) (x : A), (φ * ψ) x = φ (ψ x) :=
    fun _ _ _ => rfl
  have hcancel : ∀ (g : L ≃ₐ[K₀] L) (x : A), ρ g⁻¹ (ρ g x) = x := by
    intro g x
    rw [← hmulapp, ← map_mul, inv_mul_cancel, map_one, AddMonoid.End.one_apply]
  set Stab : Subgroup (L ≃ₐ[K₀] L) :=
    { carrier := {g | ρ g a = a}
      one_mem' := by simp only [Set.mem_setOf_eq, map_one, AddMonoid.End.one_apply]
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_setOf_eq] at hg hh ⊢
        rw [map_mul, hmulapp, hh, hg]
      inv_mem' := by
        intro g hg
        simp only [Set.mem_setOf_eq] at hg ⊢
        conv_lhs => rw [← hg]
        exact hcancel g a }
  have hStabMem : ∀ g : L ≃ₐ[K₀] L, g ∈ Stab ↔ ρ g a = a := fun g => Iff.rfl
  -- an equivariant function supported on the orbit of `a`, with prescribed
  -- stabilizer-fixed value on the orbit
  have hfun : ∀ c : L, c ∈ IntermediateField.fixedField Stab →
      ∃ f ∈ galoisEquivariantAlgebra L ρ,
        (∀ g : L ≃ₐ[K₀] L, f (ρ g a) = g c) ∧
          ∀ x : A, (¬∃ g : L ≃ₐ[K₀] L, ρ g a = x) → f x = 0 := by
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have hval : ∀ g₁ g₂ : L ≃ₐ[K₀] L, ρ g₁ a = ρ g₂ a → g₁ c = g₂ c := by
      intro g₁ g₂ h12
      have hmem : g₂⁻¹ * g₁ ∈ Stab := by
        rw [hStabMem, map_mul, hmulapp, h12]
        exact hcancel g₂ a
      have hfix := hc _ hmem
      rw [AlgEquiv.mul_apply] at hfix
      have h2 := congrArg g₂ hfix
      rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at h2
    refine ⟨fun x => if h : ∃ g : L ≃ₐ[K₀] L, ρ g a = x then h.choose c else 0,
      ?_, ?_, ?_⟩
    · intro g₀ x
      show (if h : ∃ g : L ≃ₐ[K₀] L, ρ g a = ρ g₀ x then h.choose c else 0) =
        g₀ (if h : ∃ g : L ≃ₐ[K₀] L, ρ g a = x then h.choose c else 0)
      by_cases hx : ∃ g : L ≃ₐ[K₀] L, ρ g a = x
      · have hgx : ∃ g : L ≃ₐ[K₀] L, ρ g a = ρ g₀ x :=
          ⟨g₀ * hx.choose, by rw [map_mul, hmulapp, hx.choose_spec]⟩
        rw [dif_pos hx, dif_pos hgx]
        have heq : ρ hgx.choose a = ρ (g₀ * hx.choose) a := by
          rw [hgx.choose_spec, map_mul, hmulapp, hx.choose_spec]
        rw [hval _ _ heq, AlgEquiv.mul_apply]
      · have hgx : ¬∃ g : L ≃ₐ[K₀] L, ρ g a = ρ g₀ x := by
          rintro ⟨g, hg⟩
          refine hx ⟨g₀⁻¹ * g, ?_⟩
          rw [map_mul, hmulapp, hg]
          exact hcancel g₀ x
        rw [dif_neg hx, dif_neg hgx, map_zero]
    · intro g
      show (if h : ∃ g' : L ≃ₐ[K₀] L, ρ g' a = ρ g a then h.choose c else 0) = g c
      have hg : ∃ g' : L ≃ₐ[K₀] L, ρ g' a = ρ g a := ⟨g, rfl⟩
      rw [dif_pos hg]
      exact hval _ _ hg.choose_spec
    · intro x hx
      show (if h : ∃ g : L ≃ₐ[K₀] L, ρ g a = x then h.choose c else 0) = 0
      rw [dif_neg hx]
  have hone : ρ (1 : L ≃ₐ[K₀] L) a = a := by
    rw [map_one, AddMonoid.End.one_apply]
  by_cases horb : ∃ g : L ≃ₐ[K₀] L, ρ g a = b
  · obtain ⟨g₀, hg₀⟩ := horb
    have hg₀Stab : g₀ ∉ Stab := fun hmem =>
      hab (((hStabMem g₀).mp hmem).symm.trans hg₀)
    have hex : ∃ c ∈ IntermediateField.fixedField Stab, g₀ c ≠ c := by
      by_contra hall
      refine hg₀Stab ?_
      rw [← IntermediateField.fixingSubgroup_fixedField Stab]
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
      intro y hy
      by_contra hne
      exact hall ⟨y, hy, hne⟩
    obtain ⟨c, hcmem, hgc⟩ := hex
    obtain ⟨f, hfmem, hforb, -⟩ := hfun c hcmem
    refine ⟨f, hfmem, ?_⟩
    have hfa : f a = c := by
      have h1 := hforb 1
      rw [hone] at h1
      simpa using h1
    have hfb : f b = g₀ c := by rw [← hg₀]; exact hforb g₀
    rw [hfa, hfb]
    exact fun h => hgc h.symm
  · obtain ⟨f, hfmem, hforb, hoff⟩ := hfun 1 (one_mem _)
    refine ⟨f, hfmem, ?_⟩
    have hfa : f a = 1 := by
      have h1 := hforb 1
      rw [hone] at h1
      simpa using h1
    have hfb : f b = 0 := hoff b horb
    rw [hfa, hfb]
    exact one_ne_zero

omit [IsGalois K₀ ↥L] in
/-- **Injectivity of the evaluation points** (PROVEN): evaluations at distinct
elements of `A` differ on a separating equivariant function. -/
theorem galoisEquivariantEval_injective :
    Function.Injective (galoisEquivariantEval L ρ) := by
  intro a b hab
  by_contra hne
  obtain ⟨f, hfmem, hfab⟩ := galoisEquivariantAlgebra_separates L ρ hne
  apply hfab
  have h := DFunLike.congr_fun hab (⟨f, hfmem⟩ : galoisEquivariantAlgebra L ρ)
  rw [galoisEquivariantEval_apply, galoisEquivariantEval_apply] at h
  exact (algebraMap (↥L) Ω).injective h

/-- **A point sharing its kernel with an evaluation is an evaluation** (PROVEN; the
Galois-theoretic half of the points surjectivity, counting-free): if the kernel of an
`Ω`-point `φ` of the equivariant-functions algebra equals the kernel of the
evaluation at `a`, then `φ` is the evaluation at a point of the orbit of `a`. Proof:
let `m` be the common kernel — also the kernel of the corestricted evaluation
`evalL : f ↦ f a` into `L` — and factor both `φ` and `evalL` through the residue
field `HK ⧸ m` (maximal by Artinian-ness, so a field). The two factorizations make
`L` and `Ω` algebras over the residue field; `L` is separable over it (tower), so
`IsSepClosed.lift` extends the `Ω`-factorization to an embedding `σ : L →ₐ[K₀] Ω`
compatible with the `L`-factorization (by `AlgHom.commutes`). Since `L/K₀` is
normal, `σ` is an automorphism `g` of `L` followed by the inclusion
(`Normal.algHomEquivAut`), and the equivariance of the functions in the algebra
turns `σ ∘ evalL = φ` into `φ = eval (ρ g a)`. -/
theorem galoisEquivariantEval_of_ker_eq [Finite A] [IsSepClosure K₀ Ω]
    (φ : galoisEquivariantAlgebra L ρ →ₐ[K₀] Ω) (a : A)
    (h : RingHom.ker φ = RingHom.ker (galoisEquivariantEval L ρ a)) :
    ∃ x : A, galoisEquivariantEval L ρ x = φ := by
  classical
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K₀
  -- the evaluation into `L` and its kernel
  set evalL : galoisEquivariantAlgebra L ρ →ₐ[K₀] L :=
    (Pi.evalAlgHom K₀ (fun _ : A => L) a).comp (galoisEquivariantAlgebra L ρ).val
  have hkerL : RingHom.ker (galoisEquivariantEval L ρ a) = RingHom.ker evalL := by
    ext f
    rw [RingHom.mem_ker, RingHom.mem_ker]
    constructor
    · intro hf
      apply (algebraMap (↥L) Ω).injective
      rw [map_zero]
      exact hf
    · intro hf
      show algebraMap L Ω (evalL f) = 0
      rw [hf, map_zero]
  set m : Ideal (galoisEquivariantAlgebra L ρ) := RingHom.ker evalL
  -- `m` is maximal: the algebra is Artinian and `m` is prime
  haveI : IsArtinianRing (galoisEquivariantAlgebra L ρ) :=
    isArtinian_of_tower K₀ inferInstance
  haveI hprime : m.IsPrime := RingHom.ker_isPrime evalL
  haveI hmax : m.IsMaximal := IsArtinianRing.isMaximal_of_isPrime m
  letI : Field (galoisEquivariantAlgebra L ρ ⧸ m) := Ideal.Quotient.field m
  -- factor `φ` and `evalL` through the residue field
  have hφ0 : ∀ f ∈ m, φ f = 0 := by
    intro f hf
    refine RingHom.mem_ker.mp ?_
    rw [h, hkerL]
    exact hf
  have hevL0 : ∀ f ∈ m, evalL f = 0 := fun f hf => RingHom.mem_ker.mp hf
  set φbar := Ideal.Quotient.liftₐ m φ hφ0
  set ebar := Ideal.Quotient.liftₐ m evalL hevL0
  -- `L` and `Ω` as algebras over the residue field, via the two factorizations
  letI : Algebra (galoisEquivariantAlgebra L ρ ⧸ m) L := ebar.toRingHom.toAlgebra
  letI : Algebra (galoisEquivariantAlgebra L ρ ⧸ m) Ω := φbar.toRingHom.toAlgebra
  haveI : IsScalarTower K₀ (galoisEquivariantAlgebra L ρ ⧸ m) L :=
    IsScalarTower.of_algebraMap_eq fun x => (ebar.commutes x).symm
  haveI : IsScalarTower K₀ (galoisEquivariantAlgebra L ρ ⧸ m) Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (φbar.commutes x).symm
  haveI : Algebra.IsSeparable (galoisEquivariantAlgebra L ρ ⧸ m) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K₀ _ L
  -- extend the `Ω`-factorization along `L`
  set σ0 : L →ₐ[galoisEquivariantAlgebra L ρ ⧸ m] Ω := IsSepClosed.lift
  set σ : L →ₐ[K₀] Ω := σ0.restrictScalars K₀
  have hσe : ∀ y, σ (ebar y) = φbar y := by
    intro y
    show σ0 (algebraMap (galoisEquivariantAlgebra L ρ ⧸ m) L y) = φbar y
    rw [AlgHom.commutes]
    rfl
  -- since `L/K₀` is normal, the extension is an automorphism followed by inclusion
  set g : L ≃ₐ[K₀] L := Normal.algHomEquivAut K₀ Ω L σ
  have hg : ∀ z : L, algebraMap L Ω (g z) = σ z := by
    intro z
    have h1 := (Normal.algHomEquivAut K₀ Ω L).symm_apply_apply σ
    rw [Normal.algHomEquivAut_symm_apply] at h1
    exact DFunLike.congr_fun h1 z
  refine ⟨ρ g a, ?_⟩
  apply AlgHom.ext
  rintro ⟨f, hf⟩
  show algebraMap L Ω (f (ρ g a)) = φ ⟨f, hf⟩
  rw [hf g a, hg]
  have hea : ebar (Ideal.Quotient.mkₐ K₀ m ⟨f, hf⟩) = f a :=
    DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp m evalL hevL0) ⟨f, hf⟩
  calc σ (f a) = σ (ebar (Ideal.Quotient.mkₐ K₀ m ⟨f, hf⟩)) := by rw [hea]
    _ = φbar (Ideal.Quotient.mkₐ K₀ m ⟨f, hf⟩) := hσe _
    _ = φ ⟨f, hf⟩ := DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp m φ hφ0) ⟨f, hf⟩

/-- **Surjectivity of the evaluation points** (DECOMPOSED 2026-07-23; assembly
PROVEN): every `Ω`-point of the equivariant-functions algebra is an evaluation.
The kernels of the evaluations intersect to zero (a function vanishing at every
point of `A` is zero), so their product lands in the prime kernel of any given
point `φ`, which therefore contains — and by maximality (the algebra is Artinian)
equals — the kernel of some evaluation; the sorried leaf
`galoisEquivariantEval_of_ker_eq` upgrades the kernel equality to an equality of
points along the orbit of the evaluation base point. -/
theorem galoisEquivariantEval_surjective [Finite A] [IsSepClosure K₀ Ω] :
    Function.Surjective (galoisEquivariantEval L ρ) := by
  classical
  haveI := Fintype.ofFinite A
  intro φ
  -- the kernels of the evaluations intersect to zero
  have hbot : (Finset.univ.inf fun a : A =>
      RingHom.ker (galoisEquivariantEval L ρ a)) = ⊥ := by
    refine eq_bot_iff.mpr fun f hf => ?_
    have hzero : ∀ a : A, (f : A → L) a = 0 := by
      intro a
      have hle : (Finset.univ.inf fun a : A =>
          RingHom.ker (galoisEquivariantEval L ρ a)) ≤
          RingHom.ker (galoisEquivariantEval L ρ a) :=
        Finset.inf_le (Finset.mem_univ a)
      have hfa : galoisEquivariantEval L ρ a f = 0 := RingHom.mem_ker.mp (hle hf)
      rw [galoisEquivariantEval_apply] at hfa
      exact (algebraMap (↥L) Ω).injective (by rw [hfa, map_zero])
    have hf0 : f = 0 := Subtype.ext (funext hzero)
    rw [hf0]
    exact (Submodule.mem_bot _).mpr rfl
  -- the product of the kernels lands in the kernel of `φ`
  have hprod : (∏ a ∈ Finset.univ, RingHom.ker (galoisEquivariantEval L ρ (a : A)))
      ≤ RingHom.ker φ :=
    le_trans (le_trans Ideal.prod_le_inf (le_of_eq hbot)) bot_le
  haveI hprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨a₀, -, ha₀⟩ := (Ideal.IsPrime.prod_le hprime).mp hprod
  -- upgrade the containment to an equality by maximality
  haveI : IsArtinianRing (galoisEquivariantAlgebra L ρ) :=
    isArtinian_of_tower K₀ inferInstance
  haveI hp₀ : (RingHom.ker (galoisEquivariantEval L ρ a₀)).IsPrime :=
    RingHom.ker_isPrime _
  have hmax : (RingHom.ker (galoisEquivariantEval L ρ a₀)).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime _
  exact galoisEquivariantEval_of_ker_eq L ρ φ a₀
    (hmax.eq_of_le hprime.ne_top ha₀).symm

/-- **A structureless copy of the equivariant-functions algebra**, used as the
carrier of its Hopf-algebra structure in `exists_hopfAlgebra_galoisHopfCarrier`: a
type synonym deliberately carrying NO instances, so that the Hopf-algebra package —
whose convolution structure is keyed to the Bialgebra-derived algebra instance of its
carrier, incompatible with any pre-existing canonical instance — can bind all its
instances existentially without a diamond. -/
def GaloisHopfCarrier : Type _ := galoisEquivariantAlgebra L ρ

/-- **The Hopf-algebra package on the canonical-universe carrier** (sorry node; the
comultiplication half of the package, freed 2026-07-23 of all universe bookkeeping —
the `Type u` realization is now the separate transport leaf
`exists_hopfAlgebra_small_copy`, assembled in
`exists_hopfAlgebra_galoisEquivariantAlgebra`): the structureless copy
`GaloisHopfCarrier L ρ` of the equivariant-functions algebra carries a
`K₀`-Hopf-algebra structure together with an algebra equivalence `e` to the
equivariant-functions algebra for which the convolution product of evaluation points
is the evaluation at the sum. Intended proof: transfer the commutative ring and
algebra structure of `galoisEquivariantAlgebra L ρ` along the definitional equality
of the type synonym (so `e` is the identity equivalence); the comultiplication is
the pullback of the addition `A × A → A` through the descent identification of
`galoisEquivariantAlgebra L ρ ⊗[K₀] galoisEquivariantAlgebra L ρ` with the
equivariant functions on `A × A` (the tensor square of the descent isomorphism of
`galoisEquivariantEval_surjective`'s docstring), the counit is evaluation at `0 : A`
(which lands in the bottom fixed field `K₀` since `0` is `ρ`-fixed), and the
antipode is the pullback of negation; the required convolution identity is then the
computation `(eval a ⊛ eval b) f = (eval a ⊗ eval b) (Δ f) = f (a + b)` holding by
construction. -/
theorem exists_hopfAlgebra_galoisHopfCarrier [Finite A] :
    ∃ (_ : CommRing (GaloisHopfCarrier L ρ))
      (_ : HopfAlgebra K₀ (GaloisHopfCarrier L ρ))
      (e : GaloisHopfCarrier L ρ ≃ₐ[K₀] galoisEquivariantAlgebra L ρ),
      ∀ a b : A,
        WithConv.toConv ((galoisEquivariantEval L ρ a).comp e.toAlgHom) *
          WithConv.toConv ((galoisEquivariantEval L ρ b).comp e.toAlgHom) =
        WithConv.toConv ((galoisEquivariantEval L ρ (a + b)).comp e.toAlgHom) :=
  sorry

universe v in
/-- **Hopf algebras have Hopf-algebra copies in every admissible universe** (sorry
node; pure transfer of structure, curve-free and Galois-free — the universe half of
the equivariant-functions package): a Hopf algebra `B` over `K₁` that is `v`-small
as a type admits a `Type v` copy: a commutative ring `C` in `Type v` with a
`K₁`-Hopf-algebra structure, an algebra equivalence `ê : C ≃ₐ[K₁] B`, and a
bialgebra homomorphism `êc` witnessing that `ê` respects the comultiplications.
Intended proof: `C := Shrink.{v} B` with the ring and algebra structure transported
along `equivShrink` (`Shrink.instCommRing`, `Shrink.instAlgebra`, `Shrink.algEquiv`),
the comultiplication `(ê ⊗ ê).symm ∘ Δ_B ∘ ê`, counit `ε_B ∘ ê`, antipode
`ê.symm ∘ S_B ∘ ê`; each Hopf axiom is the corresponding axiom of `B` conjugated by
`ê` (`Algebra.TensorProduct.congr` supplies the tensor legs), and the
bialgebra-homomorphism property of `ê` then holds by construction. -/
theorem exists_hopfAlgebra_small_copy {K₁ : Type*} [CommSemiring K₁]
    {B : Type*} [CommRing B] [HopfAlgebra K₁ B] [Small.{v} B] :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra K₁ C) (ê : C ≃ₐ[K₁] B)
      (êc : C →ₐc[K₁] B), (êc : C →ₐ[K₁] B) = ê.toAlgHom :=
  sorry

/-- **The Hopf-algebra structure on a `u`-small carrier of the equivariant-functions
algebra** (DECOMPOSED 2026-07-23 into the canonical-universe package leaf
`exists_hopfAlgebra_galoisHopfCarrier` — the comultiplication content — and the
universe-transport leaf `exists_hopfAlgebra_small_copy`; the smallness of the
carrier and the assembly below are PROVEN): a `Type u` copy of the
equivariant-functions algebra carrying a `K₀`-Hopf-algebra structure for which the
convolution product of evaluation points is the evaluation at the sum. The algebra
is `u`-small — finite-dimensional over the `u`-small `K₀`, hence in linear bijection
with `Fin d → K₀` (`Module.finBasis` + `Basis.equivFun` + `small_Pi`) — hence so is
the carrier of its Hopf package, which the transport leaf copies into `Type u`; the
convolution identity transports along the bialgebra homomorphism underlying the copy
equivalence by `AlgHom.convMul_comp_bialgHom_distrib`. -/
theorem exists_hopfAlgebra_galoisEquivariantAlgebra [Finite A] [Small.{u} K₀] :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K₀ HK)
      (e : HK ≃ₐ[K₀] galoisEquivariantAlgebra L ρ),
      ∀ a b : A,
        WithConv.toConv ((galoisEquivariantEval L ρ a).comp e.toAlgHom) *
          WithConv.toConv ((galoisEquivariantEval L ρ b).comp e.toAlgHom) =
        WithConv.toConv ((galoisEquivariantEval L ρ (a + b)).comp e.toAlgHom) := by
  classical
  obtain ⟨instCR, instH, e₀, hconv₀⟩ := exists_hopfAlgebra_galoisHopfCarrier L ρ
  letI := instCR
  letI := instH
  -- the equivariant-functions algebra, hence the carrier, is `u`-small
  haveI : Small.{u} (galoisEquivariantAlgebra L ρ) :=
    small_of_injective
      (Module.finBasis K₀ (galoisEquivariantAlgebra L ρ)).equivFun.injective
  haveI : Small.{u} (GaloisHopfCarrier L ρ) := small_of_injective e₀.injective
  -- copy the package into `Type u`
  obtain ⟨HK, jCR, jH, ê, êc, hêc⟩ :=
    exists_hopfAlgebra_small_copy (K₁ := K₀) (B := GaloisHopfCarrier L ρ)
  letI := jCR
  letI := jH
  refine ⟨HK, jCR, jH, ê.trans e₀, ?_⟩
  intro a b
  -- fold compositions through the copy equivalence
  have key : ∀ c : A, ((galoisEquivariantEval L ρ c).comp e₀.toAlgHom).comp
      (êc : HK →ₐ[K₀] GaloisHopfCarrier L ρ) =
      (galoisEquivariantEval L ρ c).comp (ê.trans e₀).toAlgHom := by
    intro c
    rw [hêc]
    exact AlgHom.ext fun x => rfl
  -- transport the convolution identity along the bialgebra homomorphism
  have hd := AlgHom.convMul_comp_bialgHom_distrib
    (WithConv.toConv ((galoisEquivariantEval L ρ a).comp e₀.toAlgHom))
    (WithConv.toConv ((galoisEquivariantEval L ρ b).comp e₀.toAlgHom)) êc
  rw [hconv₀ a b] at hd
  have hd' := (congrArg WithConv.toConv hd).trans (WithConv.toConv_ofConv _)
  rw [key a, key b, key (a + b)] at hd'
  exact hd'.symm

end GaloisEtalePackage

/-- **The finite-étale package of a finite-quotient Galois module, small carrier**
(DECOMPOSED 2026-07-23 into the Grothendieck construction of the section above —
equivariant-functions algebra, finiteness, étale-ness, injectivity and equivariance of
evaluation all PROVEN — plus the two sorried leaves `galoisEquivariantEval_surjective`
(descent/point-count) and `exists_hopfAlgebra_galoisEquivariantAlgebra`
(comultiplication); the assembly below is proven. Originally: the curve-independent
core of the torsion-package decomposition — the
separable-closure counterpart of the structurally parallel sorry node
`exists_galoisModulePackage_of_finiteQuotient` in `Fermat.FLT.FreyCurve.Semistable`
(downstream, hence not importable here); when either node is proven the other should
be derived from or aligned with it. Differences from that node: `Ω` is only a
separable closure and `K₀` is not constrained to characteristic zero — costless, since
the étale-algebra correspondence lives entirely inside separable extensions — the
carrier is realized in an arbitrary universe `u` under the precise smallness
hypothesis `Small.{u} K₀` (a finite-dimensional algebra over a `u`-small field is
`u`-small), and there is no redundant `K₀ ⊗[K₀] ·` base change): for a finite abelian
group `A` with an action `ρ` of the finite Galois group `Gal(L/K₀)`, there is a finite
étale `K₀`-Hopf algebra `HK` with carrier in `Type u` whose `Ω`-points under
convolution are isomorphic to `A`, equivariantly for `Gal(Ω/K₀)` acting through
restriction to `L`. Intended proof (Grothendieck's Galois correspondence for étale
algebras, with group structure): `HK` is the algebra of `Gal(L/K₀)`-equivariant
functions `A → L`; evaluation at orbit representatives identifies it with
`∏_{orbits} Fix(Stab)`, a product of finite separable subextensions, finite étale of
`K₀`-dimension `#A`; the comultiplication is the pullback of the addition of `A`
through the same identification for `HK ⊗[K₀] HK`; the `Ω`-points are the evaluations
at the elements of `A`, equivariantly by construction; finally transport the whole
package along an equivalence of the carrier with a `Type u` type (`Small.{u}`,
`Fin d → Shrink K₀`-style). -/
theorem exists_finiteQuotient_galoisModule_etale_package
    (K₀ : Type*) [Field K₀] [Small.{u} K₀]
    (Ω : Type*) [Field Ω] [Algebra K₀ Ω] [IsSepClosure K₀ Ω]
    (A : Type*) [AddCommGroup A] [Finite A]
    (L : IntermediateField K₀ Ω) [FiniteDimensional K₀ L] [IsGalois K₀ L]
    (ρ : (L ≃ₐ[K₀] L) →* AddMonoid.End A) :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K₀ HK)
      (_ : Module.Finite K₀ HK) (_ : Algebra.Etale K₀ HK)
      (f : Additive (WithConv (HK →ₐ[K₀] Ω)) ≃+ A),
      ∀ (σ : Ω ≃ₐ[K₀] Ω) (φ : HK →ₐ[K₀] Ω),
        f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
          ρ (AlgEquiv.restrictNormalHom (F := K₀) (K₁ := Ω) L σ)
            (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  obtain ⟨HK, instCR, instHopf, e, hconv⟩ :=
    exists_hopfAlgebra_galoisEquivariantAlgebra (Ω := Ω) L ρ
  letI := instCR
  letI := instHopf
  haveI := galoisEquivariantAlgebra_etale (Ω := Ω) L ρ
  haveI hfin : Module.Finite K₀ HK := Module.Finite.equiv e.symm.toLinearEquiv
  haveI het : Algebra.Etale K₀ HK := Algebra.Etale.of_equiv e.symm
  -- the composite-with-`e` evaluations and their bijectivity
  have hcompsymm : ∀ ψ : galoisEquivariantAlgebra L ρ →ₐ[K₀] Ω,
      (ψ.comp e.toAlgHom).comp e.symm.toAlgHom = ψ :=
    fun ψ => AlgHom.ext fun x => by simp
  have hbij : Function.Bijective (fun a : A =>
      (galoisEquivariantEval L ρ a).comp e.toAlgHom) := by
    constructor
    · intro a b hab
      apply galoisEquivariantEval_injective L ρ
      have h2 := congrArg (fun ψ : _ →ₐ[K₀] Ω => ψ.comp e.symm.toAlgHom) hab
      simpa only [hcompsymm] using h2
    · intro φ
      obtain ⟨a, ha⟩ := galoisEquivariantEval_surjective L ρ
        (φ.comp e.symm.toAlgHom)
      refine ⟨a, ?_⟩
      show (galoisEquivariantEval L ρ a).comp e.toAlgHom = φ
      rw [ha]
      exact AlgHom.ext fun x => by simp
  -- the points equivalence, additively
  set e₂ : A ≃ Additive (WithConv (HK →ₐ[K₀] Ω)) :=
    (Equiv.ofBijective _ hbij).trans ((WithConv.equiv _).symm.trans Additive.ofMul)
  have hmap : ∀ x y : A, e₂ (x + y) = e₂ x + e₂ y := by
    intro x y
    show Additive.ofMul (WithConv.toConv ((galoisEquivariantEval L ρ (x + y)).comp
        e.toAlgHom)) =
      Additive.ofMul (WithConv.toConv ((galoisEquivariantEval L ρ x).comp e.toAlgHom)) +
      Additive.ofMul (WithConv.toConv ((galoisEquivariantEval L ρ y).comp e.toAlgHom))
    rw [← ofMul_mul]
    exact congrArg Additive.ofMul (hconv x y).symm
  have key : ∀ y : A, (AddEquiv.mk' e₂ hmap).symm
      (Additive.ofMul (WithConv.toConv ((galoisEquivariantEval L ρ y).comp
        e.toAlgHom))) = y := fun y =>
    (AddEquiv.mk' e₂ hmap).symm_apply_apply y
  refine ⟨HK, instCR, instHopf, hfin, het, (AddEquiv.mk' e₂ hmap).symm, ?_⟩
  intro σ φ
  obtain ⟨x, hx⟩ := hbij.2 φ
  have hx' : (galoisEquivariantEval L ρ x).comp e.toAlgHom = φ := hx
  have hσ : σ.toAlgHom.comp φ = (galoisEquivariantEval L ρ
      (ρ (AlgEquiv.restrictNormalHom (F := K₀) (K₁ := Ω) L σ) x)).comp e.toAlgHom := by
    rw [← hx', ← AlgHom.comp_assoc, algEquiv_comp_galoisEquivariantEval]
  rw [hσ, key, ← hx', key]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsDomain R] [IsDiscreteValuationRing R] [E.HasGoodReduction R] in
/-- **The `m`-torsion is finite for every `m ≠ 0`, in every characteristic** (PROVEN
2026-07-23; needs neither `(m : R) ≠ 0` nor good reduction — the finiteness input to
the two package wrappers below): the
division polynomial `ΨSq m` is a nonzero polynomial — were it identically zero, the
torsion dictionary (`TorsionCard.smul_some_eq_zero_iff`) would make every affine point
of `E(Kˢᵉᵖ)` an `m`-torsion point, in particular the `q² > 1` points of `q`-torsion
for an auxiliary prime `q` exceeding both `m` and the characteristic
(`TorsionCard.card_torsionBy`), whose nonzero members would then be killed by the
coprime pair `m`, `q` — so the nonzero `m`-torsion points inject, via the same
dictionary, into (roots of `ΨSq m`) × (roots of the monic `y`-quadratic), a finite
set. -/
theorem WeierstrassCurve.torsion_finite_of_ne_zero (m : ℕ) (hm : m ≠ 0) :
    Finite (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) := by
  classical
  haveI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  haveI : (E⁄Ksep).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap K Ksep)).IsElliptic)
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  -- step 1: the division polynomial `ΨSq m` is nonzero
  have hΨne : (E⁄Ksep).ΨSq (m : ℤ) ≠ 0 := by
    intro hΨ0
    -- an auxiliary prime `q` exceeding `m` and the characteristic
    obtain ⟨q, hqle, hq⟩ := Nat.exists_infinite_primes (max m (ringChar Ksep) + 1)
    have hqm : m < q := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hqle
    have hqchar : ringChar Ksep < q :=
      lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hqle
    have hqK : (q : Ksep) ≠ 0 := by
      intro h0
      rcases hq.eq_one_or_self_of_dvd (ringChar Ksep) ((ringChar.spec Ksep q).mp h0)
        with h1 | h1
      · exact CharP.char_ne_one Ksep (ringChar Ksep) h1
      · exact absurd h1 hqchar.ne
    -- the `q`-torsion has `q² > 1` points, so it has a nonzero point
    have hcard := TorsionCard.card_torsionBy (E.map (algebraMap K Ksep)) q hqK
    have h1 : 1 < Nat.card
        (Submodule.torsionBy ℤ ((E.map (algebraMap K Ksep))⁄Ksep).Point q) := by
      rw [hcard]
      nlinarith [hq.two_le]
    haveI : Finite
        (Submodule.torsionBy ℤ ((E.map (algebraMap K Ksep))⁄Ksep).Point q) :=
      (Nat.card_pos_iff.mp (lt_trans one_pos h1)).2
    haveI := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨Q, hQne⟩ :=
      exists_ne (0 : Submodule.torsionBy ℤ ((E.map (algebraMap K Ksep))⁄Ksep).Point q)
    have hqtor : ((q : ℕ) : ℤ) • (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp Q.2
    -- the vanishing of `ΨSq m` makes `Q` an `m`-torsion point by the dictionary
    have hmtor : (m : ℤ) • (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point) = 0 := by
      cases hQval : (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point) with
      | zero => exact smul_zero _
      | @some x y h =>
        refine (TorsionCard.smul_some_eq_zero_iff (E.map (algebraMap K Ksep))
          hmZ h).mpr ?_
        rw [show ((E.map (algebraMap K Ksep))⁄Ksep).ΨSq (m : ℤ)
          = (E⁄Ksep).ΨSq (m : ℤ) from rfl, hΨ0, Polynomial.eval_zero]
    -- Bézout at the coprime pair `m`, `q` kills `Q`
    have hcop : IsCoprime (m : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast (hq.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm) hqm)).symm
    obtain ⟨a, b, hab⟩ := hcop
    refine hQne (Subtype.ext ?_)
    calc (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point)
        = (1 : ℤ) • (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point) :=
          (one_smul _ _).symm
      _ = (a * (m : ℤ) + b * (q : ℤ)) •
          (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point) := by rw [hab]
      _ = a • ((m : ℤ) • (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point)) +
          b • (((q : ℕ) : ℤ) • (Q : ((E.map (algebraMap K Ksep))⁄Ksep).Point)) := by
          rw [add_smul, mul_smul, mul_smul]
      _ = 0 := by rw [hmtor, hqtor, smul_zero, smul_zero, add_zero]
  -- step 2: nonzero torsion points inject into (roots of `ΨSq m`) × (`y`-quadratic roots)
  have hYfin : ∀ x : Ksep, {y : Ksep | (E⁄Ksep).toAffine.Equation x y}.Finite := by
    intro x
    set f : Polynomial Ksep := Polynomial.X ^ 2 +
      Polynomial.C ((E⁄Ksep).a₁ * x + (E⁄Ksep).a₃) * Polynomial.X -
      Polynomial.C (x ^ 3 + (E⁄Ksep).a₂ * x ^ 2 + (E⁄Ksep).a₄ * x + (E⁄Ksep).a₆)
      with hfdef
    have hd2 : f.natDegree = 2 := by
      rw [hfdef]
      compute_degree!
    have hfne : f ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hd2
      exact two_ne_zero hd2.symm
    refine (Polynomial.finite_setOf_isRoot hfne).subset ?_
    intro y hy
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hy
    show f.eval y = 0
    rw [hfdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination heq
  have hSfin : {x : Ksep | ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot hΨne
  have hTfin : (⋃ x ∈ {x : Ksep | ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x},
      ({x} ×ˢ {y : Ksep | (E⁄Ksep).toAffine.Equation x y})).Finite :=
    hSfin.biUnion fun x _ => (Set.finite_singleton x).prod (hYfin x)
  have hcarrier : ((AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) :
      Set (E⁄Ksep).Point).Finite := by
    let F : (E⁄Ksep).Point → Option (Ksep × Ksep) := fun P =>
      match P with
      | .zero => none
      | .some x y _ => some (x, y)
    have hinj : Function.Injective F := by
      intro P P' hPP'
      cases P with
      | zero =>
        cases P' with
        | zero => rfl
        | @some x' y' h' => injection hPP'
      | @some x y h =>
        cases P' with
        | zero => injection hPP'
        | @some x' y' h' =>
          injection hPP' with hpair
          injection hpair with hx hy
          subst hx
          subst hy
          rfl
    have himg : F '' (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) ⊆
        insert none (Option.some ''
          (⋃ x ∈ {x : Ksep | ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x},
            ({x} ×ˢ {y : Ksep | (E⁄Ksep).toAffine.Equation x y}))) := by
      rintro _ ⟨P, hP, rfl⟩
      cases P with
      | zero => exact Set.mem_insert _ _
      | @some x y h =>
        refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, rfl⟩
        have htor : (m : ℤ) • (Affine.Point.some x y h : (E⁄Ksep).Point) = 0 :=
          (Submodule.mem_torsionBy_iff _ _).mp hP
        have hroot : ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x :=
          (TorsionCard.smul_some_eq_zero_iff (E.map (algebraMap K Ksep)) hmZ h).mp htor
        exact Set.mem_biUnion hroot ⟨rfl, h.1⟩
    exact Set.Finite.of_finite_image
      (((hTfin.image _).insert none).subset himg) hinj.injOn
  exact hcarrier.to_subtype

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsDomain R] [IsDiscreteValuationRing R] [E.IsElliptic] [E.HasGoodReduction R] in
/-- **The torsion Galois action factors through a finite Galois quotient, finiteness
form** (PROVEN 2026-07-22, generalized 2026-07-23 to consume the finiteness of the
torsion as a hypothesis — everything about elliptic curves in it is the finiteness
and Galois-stability of the torsion, so this form serves both the `(m : R) ≠ 0` case
and the equal-characteristic case at once): there is a finite Galois subextension
`L/K` inside `Kˢᵉᵖ` and an action of `Gal(L/K)` on the `m`-torsion through which the
geometric action of `Gal(Kˢᵉᵖ/K)` factors. Proof: the torsion set is finite by
hypothesis, so the coordinates of its points are finitely many separable elements of
`Kˢᵉᵖ`; `L` is the normal closure of their adjunction, finite Galois; the action of
an automorphism on a torsion point only depends on its restriction to `L` (the
coordinates lie in `L`), so `σ' : Gal(L/K)` acts through `AlgEquiv.liftNormal`,
multiplicatively because lifts of equal restrictions act equally. -/
theorem WeierstrassCurve.exists_torsion_galois_finiteQuotient_of_finite
    (m : ℕ) (hT : Finite (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))) :
    ∃ (L : IntermediateField K Ksep) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (ρ : (L ≃ₐ[K] L) →*
        AddMonoid.End (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))),
      ∀ (σ : Ksep ≃ₐ[K] Ksep)
        (P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
        ((ρ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ksep) L σ) P :
            AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point) := by
  classical
  haveI := hT
  -- the (finite) set of coordinates of the torsion points
  set pcs : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ) → Set Ksep := fun P =>
    WeierstrassCurve.Affine.Point.casesOn (P : (E⁄Ksep).Point) ∅
      (fun x y _ => {x, y}) with hpcsdef
  have hpcs_fin : ∀ P, (pcs P).Finite := by
    intro P
    cases hP : (P : (E⁄Ksep).Point) with
    | zero => simp [hpcsdef, hP]
    | @some x y h =>
      rw [hpcsdef]
      simp only [hP]
      exact (Set.finite_singleton y).insert x
  set S : Set Ksep := ⋃ P, pcs P
  have hSfin : S.Finite := Set.finite_iUnion hpcs_fin
  haveI : Finite ↥S := hSfin.to_subtype
  -- its adjunction and the normal closure of that
  set L₀ := IntermediateField.adjoin K S
  haveI : FiniteDimensional K ↥L₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsSeparable.isSeparable K x).isIntegral
  set L := IntermediateField.normalClosure K ↥L₀ Ksep
  haveI : Algebra.IsSeparable K ↥L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K ↥L Ksep
  haveI hGalL : IsGalois K ↥L := ⟨⟩
  -- coordinates of torsion points lie in `L`
  have hcoordL : ∀ (P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) (x y : Ksep)
      (h : (E⁄Ksep).toAffine.Nonsingular x y),
      (P : (E⁄Ksep).Point) = Affine.Point.some x y h → x ∈ L ∧ y ∈ L := by
    intro P x y h hP
    have hsub : S ⊆ (L : Set Ksep) := fun z hz =>
      IntermediateField.le_normalClosure L₀ (IntermediateField.subset_adjoin K S hz)
    have hxy : x ∈ pcs P ∧ y ∈ pcs P := by
      rw [hpcsdef]
      simp only [hP]
      exact ⟨Set.mem_insert x {y}, Set.mem_insert_of_mem x rfl⟩
    exact ⟨hsub (Set.mem_iUnion.mpr ⟨P, hxy.1⟩), hsub (Set.mem_iUnion.mpr ⟨P, hxy.2⟩)⟩
  -- the geometric action on a torsion point only sees the restriction to `L`
  have key : ∀ σ τ : Ksep ≃ₐ[K] Ksep, (∀ l ∈ L, σ l = τ l) →
      ∀ P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ),
        Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point)
          = Affine.Point.map τ.toAlgHom (P : (E⁄Ksep).Point) := by
    intro σ τ hστ P
    cases hP : (P : (E⁄Ksep).Point) with
    | zero => rfl
    | @some x y h =>
      obtain ⟨hxL, hyL⟩ := hcoordL P x y h hP
      rw [Affine.Point.map_some, Affine.Point.map_some, Affine.Point.some.injEq]
      exact ⟨hστ x hxL, hστ y hyL⟩
  -- the geometric action restricted to the torsion subgroup
  have hmemT : ∀ (σ : Ksep ≃ₐ[K] Ksep)
      (P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point)
        ∈ AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ) := by
    intro σ P
    have hP2 : ((m : ℤ)) • (P : (E⁄Ksep).Point) = 0 := P.2
    show ((m : ℤ)) • Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point) = 0
    rw [← map_zsmul, hP2, map_zero]
  set act : (Ksep ≃ₐ[K] Ksep) →
      AddMonoid.End (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) := fun σ =>
    { toFun := fun P => ⟨Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point), hmemT σ P⟩
      map_zero' := Subtype.ext (by exact rfl)
      map_add' := fun P Q => Subtype.ext (by exact map_add _ _ _) }
  have hact_coe : ∀ (σ : Ksep ≃ₐ[K] Ksep)
      (P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ((act σ P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point)
        = Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point) := fun σ P => rfl
  -- one and mul of the full Galois group act correctly
  have hone : ∀ P : (E⁄Ksep).Point,
      Affine.Point.map (1 : Ksep ≃ₐ[K] Ksep).toAlgHom P = P := by
    intro P
    cases P <;> rfl
  have hcomp : ∀ (σ τ : Ksep ≃ₐ[K] Ksep) (P : (E⁄Ksep).Point),
      Affine.Point.map σ.toAlgHom (Affine.Point.map τ.toAlgHom P)
        = Affine.Point.map (σ * τ : Ksep ≃ₐ[K] Ksep).toAlgHom P := by
    intro σ τ P
    rw [Affine.Point.map_map]
    rfl
  -- assemble the `Gal(L/K)`-action through `liftNormal`
  refine ⟨L, inferInstance, hGalL,
    { toFun := fun σ' => act (AlgEquiv.liftNormal σ' Ksep)
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · refine DFunLike.ext _ _ fun P => Subtype.ext ?_
    have hfix : ∀ l ∈ L, (AlgEquiv.liftNormal (1 : ↥L ≃ₐ[K] ↥L) Ksep) l
        = (1 : Ksep ≃ₐ[K] Ksep) l := by
      intro l hl
      have hc := AlgEquiv.liftNormal_commutes (1 : ↥L ≃ₐ[K] ↥L) Ksep ⟨l, hl⟩
      simpa using hc
    show ((act (AlgEquiv.liftNormal (1 : ↥L ≃ₐ[K] ↥L) Ksep) P :
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point) = ↑P
    rw [hact_coe, key _ _ hfix P, hone]
  · intro σ' τ'
    refine DFunLike.ext _ _ fun P => Subtype.ext ?_
    have hfix : ∀ l ∈ L, (AlgEquiv.liftNormal (σ' * τ') Ksep) l
        = ((AlgEquiv.liftNormal σ' Ksep) * (AlgEquiv.liftNormal τ' Ksep) :
          Ksep ≃ₐ[K] Ksep) l := by
      intro l hl
      have hc := AlgEquiv.liftNormal_commutes (σ' * τ') Ksep ⟨l, hl⟩
      have hcτ := AlgEquiv.liftNormal_commutes τ' Ksep ⟨l, hl⟩
      have hcσ := AlgEquiv.liftNormal_commutes σ' Ksep (τ' ⟨l, hl⟩)
      simp only [IntermediateField.algebraMap_apply] at hc hcτ hcσ
      show (AlgEquiv.liftNormal (σ' * τ') Ksep) l
        = (AlgEquiv.liftNormal σ' Ksep) ((AlgEquiv.liftNormal τ' Ksep) l)
      rw [hc, hcτ, hcσ]
      rfl
    show ((act (AlgEquiv.liftNormal (σ' * τ') Ksep) P :
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point)
      = ((act (AlgEquiv.liftNormal σ' Ksep) (act (AlgEquiv.liftNormal τ' Ksep) P) :
          AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point)
    rw [hact_coe, key _ _ hfix P, hact_coe, hact_coe, hcomp]
  · intro σ P
    have hfix : ∀ l ∈ L, (AlgEquiv.liftNormal
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ksep) L σ) Ksep) l = σ l := by
      intro l hl
      have hc := AlgEquiv.liftNormal_commutes
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ksep) L σ) Ksep ⟨l, hl⟩
      have hr := AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := Ksep) L σ ⟨l, hl⟩
      simp only [IntermediateField.algebraMap_apply] at hc
      rw [hc, hr]
    show ((act (AlgEquiv.liftNormal
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ksep) L σ) Ksep) P :
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point)
      = Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point)
    rw [hact_coe, key _ _ hfix P]

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
  [E.HasGoodReduction R] in
/-- **The torsion Galois action factors through a finite Galois quotient** (PROVEN
2026-07-22; since 2026-07-23 a wrapper around the finiteness form
`exists_torsion_galois_finiteQuotient_of_finite`, supplying the finiteness of the
torsion via `torsion_finite_of_ne_zero`). -/
theorem WeierstrassCurve.exists_torsion_galois_finiteQuotient
    (m : ℕ) (hm : (m : R) ≠ 0) :
    ∃ (L : IntermediateField K Ksep) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (ρ : (L ≃ₐ[K] L) →*
        AddMonoid.End (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))),
      ∀ (σ : Ksep ≃ₐ[K] Ksep)
        (P : AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
        ((ρ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ksep) L σ) P :
            AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (P : (E⁄Ksep).Point) :=
  WeierstrassCurve.exists_torsion_galois_finiteQuotient_of_finite K E Ksep m
    (WeierstrassCurve.torsion_finite_of_ne_zero K E Ksep m fun h0 => hm (by
      rw [h0, Nat.cast_zero]))

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [E.IsElliptic] [E.HasGoodReduction R] in
include R in
/-- **The finite étale Hopf package of the torsion, finiteness form** (DECOMPOSED
2026-07-22 into the curve-independent Galois-correspondence core
`exists_finiteQuotient_galoisModule_etale_package` — kept aligned with the
structurally parallel Semistable node, see its docstring — and the curve-specific
finite-quotient leaf `exists_torsion_galois_finiteQuotient_of_finite`; the assembly
below is proven, including the `u`-smallness of `K` via `FractionRing.algEquiv`;
generalized 2026-07-23 to consume the finiteness of the torsion as a hypothesis, so
that the `(m : R) ≠ 0` case and the equal-characteristic case share it): given that
the `m`-torsion of `E(Kˢᵉᵖ)` is finite, the `m`-torsion Galois module `E(Kˢᵉᵖ)[m]`
is, `Gal(Kˢᵉᵖ/K)`-equivariantly, the group of `Kˢᵉᵖ`-points of a finite étale Hopf
algebra over `K`. -/
theorem WeierstrassCurve.exists_torsion_etale_package_of_finite
    (m : ℕ) (hT : Finite (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))) :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K HK)
      (_ : Module.Finite K HK) (_ : Algebra.Etale K HK)
      (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  -- the geometric action factors through a finite Galois quotient
  obtain ⟨L, hFD, hGal, ρ, hρ⟩ :=
    WeierstrassCurve.exists_torsion_galois_finiteQuotient_of_finite K E Ksep m hT
  haveI := hFD
  haveI := hGal
  -- `K` is `u`-small, being a fraction field of `R : Type u`
  haveI : Small.{u} K := ⟨⟨FractionRing R, ⟨(FractionRing.algEquiv R K).toEquiv.symm⟩⟩⟩
  -- the `m`-torsion is finite, by hypothesis
  haveI := hT
  -- apply the curve-independent core to the descended action
  obtain ⟨HK, hCR, hHopf, hFin, hEt, f, hf⟩ :=
    exists_finiteQuotient_galoisModule_etale_package K Ksep
      (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) L ρ
  refine ⟨HK, hCR, hHopf, hFin, hEt, f, ?_⟩
  intro σ φ
  rw [hf σ φ]
  exact hρ σ (f (Additive.ofMul (WithConv.toConv φ)))

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [E.HasGoodReduction R] in
/-- **The finite étale Hopf package of the torsion over the fraction field**
(DECOMPOSED 2026-07-22; since 2026-07-23 a wrapper around the finiteness form
`exists_torsion_etale_package_of_finite`, supplying the finiteness of the torsion
via `torsion_finite_of_ne_zero`): for `m` nonzero in `R`, the `m`-torsion
Galois module `E(Kˢᵉᵖ)[m]` is, `Gal(Kˢᵉᵖ/K)`-equivariantly, the group of
`Kˢᵉᵖ`-points of a finite étale Hopf algebra over `K`. -/
theorem WeierstrassCurve.exists_torsion_etale_package_over_fractionField
    (m : ℕ) (hm : (m : R) ≠ 0) :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K HK)
      (_ : Module.Finite K HK) (_ : Algebra.Etale K HK)
      (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  WeierstrassCurve.exists_torsion_etale_package_of_finite R K E Ksep m
    (WeierstrassCurve.torsion_finite_of_ne_zero K E Ksep m fun h0 => hm (by
      rw [h0, Nat.cast_zero]))

/-!
### Shared machinery: flat Hopf `R`-forms and package transport

The three deep leaves of this file (`torsion_flat_of_inertia_fixes_prolong`,
`torsion_flat_prolong_of_good_reduction_prime_pow`,
`torsion_flat_of_good_reduction_prime_pow_of_eqChar`) all end by exhibiting a
finite flat Hopf algebra over `R` together with a Galois-equivariant points
isomorphism. The two proven lemmas below factor out the shared plumbing:
`torsion_flat_package_of_flat_hopf_form` produces the final package from a mere
`R`-FORM of the finite étale Hopf `K`-algebra `HK` of the torsion (a finite
flat Hopf `R`-algebra `H` with a `K`-bialgebra equivalence
`K ⊗[R] H ≃ₐc[K] HK`), and `algHom_comp_eq_of_torsion_inertia_fixes` converts
inertia-triviality on the torsion POINTS into inertia-triviality on the
`K`-algebra points of `HK`. After this factorization the Hopf-theoretic content
of both unramified cases (order invertible in `R`, and equal characteristic) is
concentrated in the single curve-free leaf
`exists_finite_flat_hopf_form_of_inertia_fixes`, and the mixed-characteristic
case in the Katz–Mazur form leaf
`exists_finite_flat_hopf_form_of_good_reduction_prime_pow`.
-/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [E.IsElliptic]
  [E.HasGoodReduction R] [IsSepClosure K Ksep] in
/-- **Package transport along a flat Hopf `R`-form** (PROVEN 2026-07-22): if the
finite étale Hopf `K`-algebra `HK` of the `m`-torsion admits a finite flat Hopf
`R`-form `H` — a `K`-bialgebra equivalence `K ⊗[R] H ≃ₐc[K] HK` — then the full
flat-torsion package holds at `m`. Precomposition with the form equivalence is a
convolution-group isomorphism on `Kˢᵉᵖ`-points
(`AlgHom.convMul_comp_bialgHom_distrib`), étaleness of the generic fibre
transports along the underlying `K`-algebra equivalence
(`Algebra.Etale.of_equiv`), and Galois equivariance is associativity of
composition. This is the common final step of all three deep leaves of this
file. -/
theorem WeierstrassCurve.torsion_flat_package_of_flat_hopf_form
    (m : ℕ)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))))
    (H : Type u) [CommRing H] [HopfAlgebra R H]
    [Module.Finite R H] [Module.Flat R H]
    (e : (K ⊗[R] H) ≃ₐc[K] HK) :
    ∃ (H' : Type u) (_ : CommRing H') (_ : HopfAlgebra R H')
      (_ : Module.Finite R H') (_ : Module.Flat R H')
      (_ : Algebra.Etale K (K ⊗[R] H'))
      (g : Additive (WithConv (K ⊗[R] H' →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H' →ₐ[K] Ksep),
        (g (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (g (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  -- étaleness of the generic fibre transports along the form equivalence
  haveI hEt : Algebra.Etale K (K ⊗[R] H) := Algebra.Etale.of_equiv e.toAlgEquiv.symm
  -- the two directions of the form equivalence, as bialgebra homomorphisms
  let ι : HK →ₐc[K] K ⊗[R] H := e.symm.toBialgHom
  let ι' : (K ⊗[R] H) →ₐc[K] HK := e.toBialgHom
  -- precomposition with `ι` is a bijection between the `Ksep`-point sets
  let Φ : ((K ⊗[R] H) →ₐ[K] Ksep) ≃ (HK →ₐ[K] Ksep) :=
    { toFun := fun ψ => ψ.comp (ι : HK →ₐ[K] K ⊗[R] H)
      invFun := fun φ => φ.comp (ι' : (K ⊗[R] H) →ₐ[K] HK)
      left_inv := fun ψ => AlgHom.ext fun x => by
        show ψ ((ι : HK →ₐ[K] K ⊗[R] H) ((ι' : (K ⊗[R] H) →ₐ[K] HK) x)) = ψ x
        congr 1
        exact e.symm_apply_apply x
      right_inv := fun φ => AlgHom.ext fun x => by
        show φ ((ι' : (K ⊗[R] H) →ₐ[K] HK) ((ι : HK →ₐ[K] K ⊗[R] H) x)) = φ x
        congr 1
        exact e.apply_symm_apply x }
  -- ... and it is multiplicative for the convolution products
  have hΦmul : ∀ x y : WithConv ((K ⊗[R] H) →ₐ[K] Ksep),
      WithConv.toConv (Φ (x * y).ofConv) =
        WithConv.toConv (Φ x.ofConv) * WithConv.toConv (Φ y.ofConv) := by
    intro x y
    have d := AlgHom.convMul_comp_bialgHom_distrib x y ι
    show WithConv.toConv ((x * y).ofConv.comp (ι : HK →ₐ[K] K ⊗[R] H)) =
      WithConv.toConv (x.ofConv.comp (ι : HK →ₐ[K] K ⊗[R] H)) *
        WithConv.toConv (y.ofConv.comp (ι : HK →ₐ[K] K ⊗[R] H))
    rw [d, WithConv.toConv_ofConv]
  -- assemble the additive equivalence of point groups
  let g₀ : Additive (WithConv ((K ⊗[R] H) →ₐ[K] Ksep)) ≃+
      Additive (WithConv (HK →ₐ[K] Ksep)) :=
    { toFun := fun x => Additive.ofMul (WithConv.toConv (Φ (Additive.toMul x).ofConv))
      invFun := fun y => Additive.ofMul (WithConv.toConv (Φ.symm (Additive.toMul y).ofConv))
      left_inv := fun x => by
        show Additive.ofMul (WithConv.toConv (Φ.symm
          (WithConv.ofConv (WithConv.toConv (Φ (Additive.toMul x).ofConv))))) = x
        rw [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]
        rfl
      right_inv := fun y => by
        show Additive.ofMul (WithConv.toConv (Φ
          (WithConv.ofConv (WithConv.toConv (Φ.symm (Additive.toMul y).ofConv))))) = y
        rw [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv]
        rfl
      map_add' := fun x y => by
        show Additive.ofMul (WithConv.toConv
            (Φ (Additive.toMul x * Additive.toMul y).ofConv)) = _
        rw [hΦmul]
        rfl }
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, hEt,
    g₀.trans f, ?_⟩
  intro σ ψ
  have hg₀ : ∀ χ : K ⊗[R] H →ₐ[K] Ksep,
      g₀ (Additive.ofMul (WithConv.toConv χ)) =
        Additive.ofMul (WithConv.toConv (χ.comp (ι : HK →ₐ[K] K ⊗[R] H))) :=
    fun χ => rfl
  have hassoc : (σ.toAlgHom.comp ψ).comp (ι : HK →ₐ[K] K ⊗[R] H) =
      σ.toAlgHom.comp (ψ.comp (ι : HK →ₐ[K] K ⊗[R] H)) :=
    AlgHom.comp_assoc σ.toAlgHom ψ (ι : HK →ₐ[K] K ⊗[R] H)
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hg₀, hg₀, hassoc]
  exact hf σ (ψ.comp (ι : HK →ₐ[K] K ⊗[R] H))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [E.IsElliptic]
  [E.HasGoodReduction R] [IsSepClosure K Ksep] in
/-- **From fixed torsion points to fixed algebra points** (PROVEN 2026-07-22):
through the equivariant points isomorphism `f`, inertia-triviality on the
`m`-torsion of `E(Kˢᵉᵖ)` forces inertia to fix every `K`-algebra homomorphism
`HK → Kˢᵉᵖ` — the form in which unramifiedness of `HK` enters the curve-free
prolongation leaf `exists_finite_flat_hopf_form_of_inertia_fixes`. Injectivity
of `f` converts `map σ (f φ) = f φ` (the Néron–Ogg–Shafarevich conclusion) into
`σ ∘ φ = φ`. -/
theorem WeierstrassCurve.algHom_comp_eq_of_torsion_inertia_fixes
    (m : ℕ)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))))
    (hunr : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K,
        ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ),
          Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P) :
    ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : HK →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ := by
  intro 𝒪 h𝒪 σ hσ φ
  have heq : f (Additive.ofMul (WithConv.toConv
      ((σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ))) =
      f (Additive.ofMul (WithConv.toConv φ)) := by
    apply Subtype.ext
    rw [hf (σ : Ksep ≃ₐ[K] Ksep) φ]
    exact hunr 𝒪 h𝒪 σ hσ (f (Additive.ofMul (WithConv.toConv φ)))
      (f (Additive.ofMul (WithConv.toConv φ))).2
  have h1 := f.injective heq
  have h2 : WithConv.toConv ((σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ) =
      WithConv.toConv φ := h1
  exact WithConv.toConv_injective h2

/-- **Unramified finite separable field extensions have finite étale `R`-forms**
(sorry node; the single-factor core of the Galois half of the curve-free
Hopf-form leaf, isolated 2026-07-23 — the product assembly is proven in
`exists_finite_etale_algebra_form_of_inertia_fixes`): a finite separable field
extension `L/K`, all of whose embeddings into `Kˢᵉᵖ` are fixed by every inertia
subgroup above `R`, admits a finite étale `R`-form. Intended proof: the
hypothesis places each embedding `L → Kˢᵉᵖ` inside the inertia field of every
valuation subring above `R`, so `L` is unramified with separable residue
extension at every prime above the maximal ideal of `R`; take `H₀` to be the
integral closure of `R` in `L` (transported to `Type u` along an `R`-basis):
it is finite over `R` (separability + Noetherian normal base, Neukirch I.8/
Serre *Local Fields* I–II), free (torsion-free finite over a DVR), and étale
over `R` (finite flat with unramified fibres, by the inertia hypothesis), and
`K ⊗[R] H₀ → L` is an isomorphism (clearing denominators). -/
theorem exists_finite_etale_algebra_form_of_inertia_fixes_field
    (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : L →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    ∃ (H₀ : Type u) (_ : CommRing H₀) (_ : Algebra R H₀)
      (_ : Module.Finite R H₀) (_ : Algebra.Etale R H₀),
      Nonempty ((K ⊗[R] H₀) ≃ₐ[K] L) :=
  sorry

/-- **Unramified finite étale `K`-algebras have finite étale `R`-forms**
(DECOMPOSED 2026-07-23 into the single-field-extension leaf
`exists_finite_etale_algebra_form_of_inertia_fixes_field`; the assembly below
is proven — no Hopf structure appears at all): a finite étale `K`-algebra
`HK`, all of whose `Kˢᵉᵖ`-points are fixed by every inertia subgroup above
`R`, admits a finite étale `R`-form. Assembly: `HK` is a finite product of
finite separable field extensions `Lᵢ` (`Algebra.Etale.iff_exists_algEquiv_prod`);
the inertia-fixing hypothesis descends to each factor through the (surjective)
projection `HK → Lᵢ`; the factor leaf produces étale forms `H₀ᵢ`, whose
product is a finite étale `R`-form of `HK` since the tensor product commutes
with finite products (`Algebra.TensorProduct.piRight`) and étaleness is a
product-local property (`Algebra.FormallyEtale.pi_iff`). -/
theorem exists_finite_etale_algebra_form_of_inertia_fixes
    (HK : Type u) [CommRing HK] [Algebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : HK →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    ∃ (H₀ : Type u) (_ : CommRing H₀) (_ : Algebra R H₀)
      (_ : Module.Finite R H₀) (_ : Algebra.Etale R H₀),
      Nonempty ((K ⊗[R] H₀) ≃ₐ[K] HK) := by
  classical
  -- split `HK` into a finite product of finite separable field extensions
  obtain ⟨I, hIfin, Ai, iF, iAlgK, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K HK).mp inferInstance
  haveI := hIfin
  letI := iF
  letI := iAlgK
  haveI := Fintype.ofFinite I
  haveI := Classical.decEq I
  -- each factor acquires an étale `R`-form from the field-extension leaf
  have hform : ∀ i : I, ∃ (H₀ : Type u) (_ : CommRing H₀) (_ : Algebra R H₀)
      (_ : Module.Finite R H₀) (_ : Algebra.Etale R H₀),
      Nonempty ((K ⊗[R] H₀) ≃ₐ[K] Ai i) := by
    intro i
    haveI := (hAi i).1
    haveI := (hAi i).2
    refine exists_finite_etale_algebra_form_of_inertia_fixes_field R K Ksep
      (Ai i) ?_
    -- the inertia-fixing hypothesis descends through the projection `HK → Ai i`
    intro 𝒪 h𝒪 σ hσ φ
    have h := hfix 𝒪 h𝒪 σ hσ (φ.comp ((Pi.evalAlgHom K Ai i).comp e.toAlgHom))
    have hsurj : Function.Surjective ((Pi.evalAlgHom K Ai i).comp e.toAlgHom) :=
      (Function.surjective_eval i).comp e.surjective
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    exact DFunLike.congr_fun h y
  choose H₀ iCR iAlg iFin iEt hEq using hform
  letI := iCR
  letI := iAlg
  haveI := iFin
  haveI := iEt
  -- the product of the factor forms is an étale `R`-form of `HK`
  haveI hfin : Module.Finite R (∀ i, H₀ i) := Module.Finite.pi
  refine ⟨∀ i, H₀ i, inferInstance, inferInstance, hfin, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R K K H₀).trans
    ((AlgEquiv.piCongrRight fun i => (hEq i).some).trans e.symm)

/-- **Étale algebra forms are the integral closure** (sorry node; the CANONICITY
half of the Hopf-upgrade leaf — pure commutative algebra over the DVR `R`, no
Hopf structure): if the finite étale `K`-algebra `HK` admits a finite étale
`R`-algebra form `H₀`, then the integral closure of `R` in `HK` is itself a
finite étale `R`-algebra form. Intended proof: a finite étale `R`-algebra is
normal, hence integrally closed in its total fraction ring `K ⊗[R] H₀ ≅ HK`,
and every element of `HK` integral over `R` is a fraction of elements of the
image of `H₀` with denominator invertible in `K`, hence already in the image —
so the image of `H₀` under `x ↦ e (1 ⊗ x)` IS the integral closure, and the
form data transports along the induced isomorphism `H₀ ≅ integralClosure R HK`
(étale forms are canonical). -/
theorem integralClosure_finite_etale_form_of_etale_algebra_form
    (HK : Type u) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] [Module.Finite K HK] [Algebra.Etale K HK]
    (H₀ : Type u) [CommRing H₀] [Algebra R H₀] [Module.Finite R H₀]
    [Algebra.Etale R H₀]
    (e : (K ⊗[R] H₀) ≃ₐ[K] HK) :
    Module.Finite R (integralClosure R HK) ∧
      Algebra.Etale R (integralClosure R HK) ∧
      Nonempty ((K ⊗[R] (integralClosure R HK)) ≃ₐ[K] HK) :=
  sorry

/-- **The integral closure in an étale-formed Hopf algebra is a Hopf order**
(sorry node; the HOPF half of the Hopf-upgrade leaf): if the integral closure
`H₀ := integralClosure R HK` of `R` in the finite étale Hopf `K`-algebra `HK`
is a finite étale `R`-algebra form, then `HK` admits a finite flat Hopf
`R`-form (namely `H₀` itself). Intended proof: comultiplication is a ring
homomorphism, so it sends `H₀` (integral over `R`) into elements of
`HK ⊗[K] HK` integral over `R`, and the integral closure of `R` there is the
image of `H₀ ⊗[R] H₀` (étale ⊗ étale is étale over the normal base `R`, hence
normal, hence integrally closed in its total fraction ring, and
`K ⊗ (H₀ ⊗[R] H₀) ≅ HK ⊗[K] HK` — the canonicity leaf
`integralClosure_finite_etale_form_of_etale_algebra_form` applied to the
tensor square); the counit sends `H₀` into elements of `K` integral over `R`,
i.e. into `R` (a DVR is integrally closed); the antipode is an algebra
endomorphism, so it preserves integrality; the corestricted operations
satisfy the Hopf axioms because the inclusions `H₀ → HK` and
`H₀ ⊗[R] H₀ → HK ⊗[K] HK` are injective (`H₀` is finite free over the DVR
`R`); flatness is freeness of a finite torsion-free module over a DVR. The
`μ_p` counterexample (whose normalization over `ℤ_p` is NOT a Hopf order)
does not contradict this: there the normalization is not étale over `R`, so
the étale-form hypothesis fails. -/
theorem exists_finite_flat_hopf_form_integralClosure
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] [Module.Finite K HK] [Algebra.Etale K HK]
    (hfin : Module.Finite R (integralClosure R HK))
    (het : Algebra.Etale R (integralClosure R HK))
    (heq : Nonempty ((K ⊗[R] (integralClosure R HK)) ≃ₐ[K] HK)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) :=
  sorry

/-- **Étale algebra forms of Hopf algebras are Hopf forms** (DECOMPOSED
2026-07-23 into the canonicity leaf
`integralClosure_finite_etale_form_of_etale_algebra_form` — étale forms are
the integral closure — and the Hopf-order leaf
`exists_finite_flat_hopf_form_integralClosure` — the integral closure is
comultiplication-stable; the assembly below is proven — pure commutative
algebra over the DVR `R`, no Galois theory and no elliptic curve): if the
finite étale Hopf `K`-algebra `HK` admits a finite étale `R`-ALGEBRA form
`H₀`, then it admits a finite flat Hopf `R`-form. The key point making this
honest: étale forms are canonical (the canonicity leaf), so Hopf-stability is
a property, not extra data. -/
theorem exists_finite_flat_hopf_form_of_etale_algebra_form
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (H₀ : Type u) [CommRing H₀] [Algebra R H₀] [Module.Finite R H₀]
    [Algebra.Etale R H₀]
    (e : (K ⊗[R] H₀) ≃ₐ[K] HK) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) := by
  letI : Algebra R HK := ((algebraMap K HK).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K HK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfin, het, heq⟩ :=
    integralClosure_finite_etale_form_of_etale_algebra_form R K HK H₀ e
  exact exists_finite_flat_hopf_form_integralClosure R K HK hfin het heq

/-- **Unramified finite étale Hopf algebras prolong over a DVR** (DECOMPOSED
2026-07-23 into the Galois-half leaf
`exists_finite_etale_algebra_form_of_inertia_fixes` and the commutative-algebra
Hopf-upgrade leaf `exists_finite_flat_hopf_form_of_etale_algebra_form`; the
assembly below is proven; curve-free — the Hopf-theoretic core of BOTH
unramified cases of this file: the order-invertible étale case
`torsion_flat_of_inertia_fixes_prolong` and the equal-characteristic case
`torsion_flat_of_good_reduction_prime_pow_of_eqChar`; note that NO
order-invertibility hypothesis is needed): a finite étale Hopf `K`-algebra
`HK`, all of whose `Kˢᵉᵖ`-points are fixed by every inertia subgroup above `R`,
admits a finite flat Hopf `R`-form. The `μ_p` counterexample to flat
prolongation WITHOUT unramifiedness does not apply: its points are moved by
inertia. -/
theorem exists_finite_flat_hopf_form_of_inertia_fixes
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : HK →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) := by
  obtain ⟨H₀, iCR, iAlg, iFin, iEt, ⟨e⟩⟩ :=
    exists_finite_etale_algebra_form_of_inertia_fixes R K Ksep HK hfix
  letI := iCR; letI := iAlg; letI := iFin; letI := iEt
  exact exists_finite_flat_hopf_form_of_etale_algebra_form R K HK H₀ e

omit [E.IsElliptic] [E.HasGoodReduction R] in
/-- **Unramified implies étale prolongation** (DECOMPOSED 2026-07-22 into the
curve-free Hopf-form leaf `exists_finite_flat_hopf_form_of_inertia_fixes` via the
proven bridges `algHom_comp_eq_of_torsion_inertia_fixes` and
`torsion_flat_package_of_flat_hopf_form`; the assembly below is proven — note that
the invertibility hypothesis `_hm` is NOT needed by the decomposition, which is
what lets the equal-characteristic case share the same Hopf-form leaf): given the
finite étale Hopf `K`-algebra `HK` of the `m`-torsion (the leaf above), if every
inertia subgroup above `R` acts trivially on `E(Kˢᵉᵖ)[m]`, then `HK` prolongs to
a finite étale (in particular finite flat) Hopf algebra over `R`. See the
docstring of `exists_finite_flat_hopf_form_of_inertia_fixes` for the intended
proof of the remaining content (integral closure of `R` in `HK`, étale by
unramifiedness, Hopf by integrality of the comultiplication). -/
theorem WeierstrassCurve.torsion_flat_of_inertia_fixes_prolong
    (m : ℕ) (_hm : IsUnit (m : R))
    (hunr : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K,
        ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ),
          Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (g : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (g (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (g (Additive.ofMul (WithConv.toConv φ))) := by
  obtain ⟨H, iCR, iHopf, iFin, iFlat, ⟨e⟩⟩ :=
    exists_finite_flat_hopf_form_of_inertia_fixes R K Ksep HK
      (WeierstrassCurve.algHom_comp_eq_of_torsion_inertia_fixes R K E Ksep m HK
        f hf hunr)
  letI := iCR; letI := iHopf; letI := iFin; letI := iFlat
  exact WeierstrassCurve.torsion_flat_package_of_flat_hopf_form R K E Ksep m HK
    f hf H e

omit [E.HasGoodReduction R] in
/-- **Unramified implies flat, order invertible in the residue field** (DECOMPOSED
2026-07-22 into the Galois-correspondence leaf
`exists_torsion_etale_package_over_fractionField` and the prolongation leaf
`torsion_flat_of_inertia_fixes_prolong`; the assembly below is proven): if every
inertia subgroup above `R` acts trivially on `E(Kˢᵉᵖ)[m]` and `m` is invertible in
`R`, the `m`-torsion prolongs to a finite étale (in particular finite flat) Hopf
algebra over `R`. -/
theorem WeierstrassCurve.torsion_flat_of_inertia_fixes
    (m : ℕ) (hm : IsUnit (m : R))
    (hunr : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K,
        ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ),
          Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  obtain ⟨HK, iCR, iHopf, iFin, iEt, f, hf⟩ :=
    WeierstrassCurve.exists_torsion_etale_package_over_fractionField R K E Ksep
      m hm.ne_zero
  letI := iCR; letI := iHopf; letI := iFin; letI := iEt
  exact WeierstrassCurve.torsion_flat_of_inertia_fixes_prolong R K E Ksep
    m hm hunr HK f hf

/-- **The étale case** (DECOMPOSED 2026-07-22 into the Néron–Ogg–Shafarevich leaf
`torsion_inertia_fixes_of_prime_pow_isUnit` — via the proven composite reduction
`torsion_inertia_fixes_of_isUnit` — and the descent leaf
`torsion_flat_of_inertia_fixes`; the assembly below is proven): the flat-torsion
package for the `m`-torsion of `E` when `m` is invertible in `R` (equivalently,
invertible in the residue field). In this case flatness carries no more content than
unramifiedness — see the module docstring. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_of_isUnit
    (m : ℕ) (hm : IsUnit (m : R)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  WeierstrassCurve.torsion_flat_of_inertia_fixes R K E Ksep m hm
    (WeierstrassCurve.torsion_inertia_fixes_of_isUnit R K E Ksep m hm)

set_option maxHeartbeats 1600000 in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [E.IsElliptic]
  [E.HasGoodReduction R] [IsSepClosure K Ksep] in
/-- **Multiplicativity in the order** (PROVEN 2026-07-22): flat-torsion packages for coprime
`a` and `b` tensor to a flat-torsion package for `a * b`. The intended proof takes
`H := H_a ⊗[R] H_b` with the tensor-product Hopf structure; finiteness and flatness of a
tensor product of finite flat modules are standard, étaleness of
`K ⊗[R] (H_a ⊗[R] H_b) ≅ (K ⊗[R] H_a) ⊗[K] (K ⊗[R] H_b)` is stability of étale algebras
under base change and tensor product, `K`-algebra homomorphisms out of a tensor product
are pairs of homomorphisms (`Algebra.TensorProduct.lift`, an iso of convolution groups
here), and `AddSubgroup.torsionBy (a*b) ≃ torsionBy a × torsionBy b` for coprime `a`, `b`
is the Chinese remainder theorem for the divisible-by-`n` filtration of an abelian group
(cf. `AddSubgroup.torsionBy` and the `Submodule.torsionBy` internal-direct-sum API). -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_mul
    (a b : ℕ) (hab : a.Coprime b)
    (Ha : ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))))
    (Hb : ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((a * b : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  obtain ⟨A, hAcr, hAhopf, hAfin, hAflat, hAet, fa, hfa⟩ := Ha
  obtain ⟨B, hBcr, hBhopf, hBfin, hBflat, hBet, fb, hfb⟩ := Hb
  letI := hAcr; letI := hAhopf; letI := hAfin; letI := hAflat; letI := hAet
  letI := hBcr; letI := hBhopf; letI := hBfin; letI := hBflat; letI := hBet
  -- the convolution monoid structure on the `Ksep`-points of `K ⊗[R] (A ⊗[R] B)`;
  -- `inferInstance` does not find this through the nested tensor product, but the
  -- explicit application does
  letI : Mul (WithConv ((K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep)) :=
    @AlgHom.instMulWithConv K Ksep (K ⊗[R] (A ⊗[R] B)) _ _ _ _ _
  -- the generic fibre of `A ⊗[R] B` is étale over `K`: `K ⊗[R] (A ⊗[R] B)` is
  -- isomorphic as a `K`-algebra to `(K ⊗[R] A) ⊗[K] (K ⊗[R] B)`
  -- (`Algebra.TensorProduct.assoc`-style associator through `K`), and the tensor
  -- product of two étale `K`-algebras is étale (base change + transitivity)
  have hEt : Algebra.Etale K (K ⊗[R] (A ⊗[R] B)) := by
    haveI : Algebra.Etale K ((K ⊗[R] A) ⊗[K] (K ⊗[R] B)) :=
      Algebra.Etale.comp K (K ⊗[R] A) ((K ⊗[R] A) ⊗[K] (K ⊗[R] B))
    exact Algebra.Etale.of_equiv
      ((Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] A) B).trans
        (Algebra.TensorProduct.assoc R R K K A B))
  -- points of a tensor product are pairs of points: restriction along the two
  -- inclusions `A → A ⊗[R] B ← B` is a bijection onto pairs (because `Ksep` is
  -- commutative and `⊗` is the coproduct of commutative algebras), and it is a
  -- homomorphism for the convolution structures because comultiplication on
  -- `A ⊗[R] B` is the shuffled tensor product of the comultiplications;
  -- moreover it commutes with postcomposition by any `σ : Ksep ≃ₐ[K] Ksep`
  have hpair : ∃ (e : Additive (WithConv ((K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep)) ≃+
        Additive (WithConv ((K ⊗[R] A) →ₐ[K] Ksep)) ×
          Additive (WithConv ((K ⊗[R] B) →ₐ[K] Ksep))),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : (K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep),
        e (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
          (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
              (Additive.toMul ((e (Additive.ofMul (WithConv.toConv φ))).1)).ofConv)),
            Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp
              (Additive.toMul ((e (Additive.ofMul (WithConv.toConv φ))).2)).ofConv))) := by
    -- the two inclusions of generic fibres, `K ⊗ A → K ⊗ (A ⊗ B) ← K ⊗ B`
    let ι₁ : (K ⊗[R] A) →ₐ[K] K ⊗[R] (A ⊗[R] B) :=
      Algebra.TensorProduct.map (AlgHom.id K K) Algebra.TensorProduct.includeLeft
    let ι₂ : (K ⊗[R] B) →ₐ[K] K ⊗[R] (A ⊗[R] B) :=
      Algebra.TensorProduct.map (AlgHom.id K K) Algebra.TensorProduct.includeRight
    -- restriction along `ι₁`, `ι₂` is multiplicative for the convolution products:
    -- the inclusions are maps of coalgebras (comultiplication on a tensor product of
    -- Hopf algebras is the shuffled tensor of the comultiplications, and `ι₁`, `ι₂`
    -- are `1` on the missing factor, which is grouplike)
    have hmul : ∀ x y : WithConv ((K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep),
        ((WithConv.toConv ((x * y).ofConv.comp ι₁) : WithConv ((K ⊗[R] A) →ₐ[K] Ksep)),
         (WithConv.toConv ((x * y).ofConv.comp ι₂) : WithConv ((K ⊗[R] B) →ₐ[K] Ksep))) =
        (WithConv.toConv (x.ofConv.comp ι₁) * WithConv.toConv (y.ofConv.comp ι₁),
         WithConv.toConv (x.ofConv.comp ι₂) * WithConv.toConv (y.ofConv.comp ι₂)) := by
      -- the inclusions upgrade to bialgebra homomorphisms, so restriction along them
      -- distributes over convolution (`AlgHom.convMul_comp_bialgHom_distrib`)
      let inc₁ : A →ₐc[R] A ⊗[R] B :=
        (BialgHom.lTensor A (Bialgebra.unitBialgHom R B)).comp
          (Bialgebra.TensorProduct.rid R R A).symm.toBialgHom
      let inc₂ : B →ₐc[R] A ⊗[R] B :=
        (BialgHom.rTensor B (Bialgebra.unitBialgHom R A)).comp
          (Bialgebra.TensorProduct.lid R B).symm.toBialgHom
      let ι₁' : (K ⊗[R] A) →ₐc[K] K ⊗[R] (A ⊗[R] B) :=
        Bialgebra.TensorProduct.map (BialgHom.id K K) inc₁
      let ι₂' : (K ⊗[R] B) →ₐc[K] K ⊗[R] (A ⊗[R] B) :=
        Bialgebra.TensorProduct.map (BialgHom.id K K) inc₂
      have hcoe₁ : (ι₁' : (K ⊗[R] A) →ₐ[K] K ⊗[R] (A ⊗[R] B)) = ι₁ := by
        apply Algebra.TensorProduct.ext
        · exact AlgHom.ext fun k => by
            simp [ι₁', ι₁, inc₁]
        · exact AlgHom.ext fun a₀ => by
            simp [ι₁', ι₁, inc₁, Bialgebra.TensorProduct.rid_symm_apply]
      have hcoe₂ : (ι₂' : (K ⊗[R] B) →ₐ[K] K ⊗[R] (A ⊗[R] B)) = ι₂ := by
        apply Algebra.TensorProduct.ext
        · exact AlgHom.ext fun k => by
            simp [ι₂', ι₂, inc₂]
        · exact AlgHom.ext fun b₀ => by
            simp [ι₂', ι₂, inc₂, Bialgebra.TensorProduct.lid_symm_apply]
      intro x y
      have d₁ := @AlgHom.convMul_comp_bialgHom_distrib K Ksep (K ⊗[R] A)
        (K ⊗[R] (A ⊗[R] B)) _ _ _ _ _ _ _ x y ι₁'
      have d₂ := @AlgHom.convMul_comp_bialgHom_distrib K Ksep (K ⊗[R] B)
        (K ⊗[R] (A ⊗[R] B)) _ _ _ _ _ _ _ x y ι₂'
      rw [hcoe₁] at d₁
      rw [hcoe₂] at d₂
      exact Prod.ext (by rw [d₁, WithConv.toConv_ofConv]) (by rw [d₂, WithConv.toConv_ofConv])
    -- restriction along the two inclusions is bijective onto pairs: the tensor product
    -- is the coproduct in commutative `K`-algebras (injectivity: the images of `ι₁` and
    -- `ι₂` generate; surjectivity: `Algebra.TensorProduct.lift` through the base-change
    -- isomorphism `K ⊗[R] (A ⊗[R] B) ≃ₐ[K] (K ⊗[R] A) ⊗[K] (K ⊗[R] B)`)
    have hbij : Function.Bijective (fun φ : (K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep =>
        (φ.comp ι₁, φ.comp ι₂)) := by
      letI : Algebra R Ksep := ((algebraMap K Ksep).comp (algebraMap R K)).toAlgebra
      letI : IsScalarTower R K Ksep := IsScalarTower.of_algebraMap_eq fun _ => rfl
      constructor
      · intro φ ψ h
        have h₁ : φ.comp ι₁ = ψ.comp ι₁ := congrArg Prod.fst h
        have h₂ : φ.comp ι₂ = ψ.comp ι₂ := congrArg Prod.snd h
        apply Algebra.TensorProduct.ext
        · exact AlgHom.ext fun k => by
            simpa [ι₁, Algebra.TensorProduct.one_def] using
              AlgHom.congr_fun h₁ (k ⊗ₜ (1 : A))
        · apply Algebra.TensorProduct.ext
          · exact AlgHom.ext fun a₀ => by
              simpa [ι₁] using AlgHom.congr_fun h₁ ((1 : K) ⊗ₜ a₀)
          · exact AlgHom.ext fun b₀ => by
              simpa [ι₂] using AlgHom.congr_fun h₂ ((1 : K) ⊗ₜ b₀)
      · intro p
        refine ⟨(Algebra.TensorProduct.lift p.1 p.2 fun _ _ => Commute.all _ _).comp
          ((Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] A) B).trans
            (Algebra.TensorProduct.assoc R R K K A B)).symm.toAlgHom, ?_⟩
        refine Prod.ext ?_ ?_
        · apply Algebra.TensorProduct.ext
          · exact AlgHom.ext fun k => by
              simp [ι₁]
              rw [show ((1 : K) ⊗ₜ (1 : B) : K ⊗[R] B) = 1 from rfl, map_one, mul_one]
          · exact AlgHom.ext fun a₀ => by
              simp [ι₁]
              rw [show ((1 : K) ⊗ₜ (1 : B) : K ⊗[R] B) = 1 from rfl, map_one, mul_one]
        · apply Algebra.TensorProduct.ext
          · exact AlgHom.ext fun k => by
              simp [ι₂]
              rw [show ((1 : K) ⊗ₜ (1 : B) : K ⊗[R] B) = 1 from rfl, map_one, mul_one,
                show (k ⊗ₜ (1 : A) : K ⊗[R] A) = algebraMap K (K ⊗[R] A) k from rfl,
                show (k ⊗ₜ (1 : B) : K ⊗[R] B) = algebraMap K (K ⊗[R] B) k from rfl,
                p.1.commutes, p.2.commutes]
          · exact AlgHom.ext fun b₀ => by
              simp [ι₂]
              rw [show ((1 : K) ⊗ₜ (1 : A) : K ⊗[R] A) = 1 from rfl, map_one, one_mul]
    let Φ₀ : ((K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep) ≃
        ((K ⊗[R] A) →ₐ[K] Ksep) × ((K ⊗[R] B) →ₐ[K] Ksep) :=
      Equiv.ofBijective _ hbij
    refine ⟨{ toFun := fun x =>
                (Additive.ofMul (WithConv.toConv ((Additive.toMul x).ofConv.comp ι₁)),
                 Additive.ofMul (WithConv.toConv ((Additive.toMul x).ofConv.comp ι₂)))
              invFun := fun p => Additive.ofMul (WithConv.toConv (Φ₀.symm
                ((Additive.toMul p.1).ofConv, (Additive.toMul p.2).ofConv)))
              left_inv := fun x => by
                show Additive.ofMul (WithConv.toConv (Φ₀.symm
                  (Φ₀ ((Additive.toMul x).ofConv)))) = x
                rw [Equiv.symm_apply_apply]
                rfl
              right_inv := fun p => by
                show (Additive.ofMul (WithConv.toConv ((Φ₀ (Φ₀.symm
                    ((Additive.toMul p.1).ofConv, (Additive.toMul p.2).ofConv))).1)),
                  Additive.ofMul (WithConv.toConv ((Φ₀ (Φ₀.symm
                    ((Additive.toMul p.1).ofConv, (Additive.toMul p.2).ofConv))).2))) = p
                rw [Equiv.apply_symm_apply]
                rfl
              map_add' := fun x y =>
                congrArg (fun q => (Additive.ofMul q.1, Additive.ofMul q.2))
                  (hmul (Additive.toMul x) (Additive.toMul y)) },
      fun σ φ => rfl⟩
  -- Chinese remainder for the torsion: for coprime `a`, `b`, addition
  -- `E[a] × E[b] → E[a * b]` is an isomorphism of abelian groups
  have hcrt : ∃ (g : AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ) ×
        AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((a * b : ℕ) : ℤ)),
      ∀ P : AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ) ×
          AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ),
        (g P : (E⁄Ksep).Point) = (P.1 : (E⁄Ksep).Point) + (P.2 : (E⁄Ksep).Point) := by
    -- Bézout certificate for the coprime pair
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (a : ℤ) + v * (b : ℤ) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hab)
    -- the sum of an `a`-torsion point and a `b`-torsion point is `a * b`-torsion
    have hmem : ∀ (P : AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ) ×
        AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ)),
        ((a * b : ℕ) : ℤ) • ((P.1 : (E⁄Ksep).Point) + (P.2 : (E⁄Ksep).Point)) = 0 := by
      intro P
      have h1 : (a : ℤ) • (P.1 : (E⁄Ksep).Point) = 0 := P.1.2
      have h2 : (b : ℤ) • (P.2 : (E⁄Ksep).Point) = 0 := P.2.2
      have hx : ((a : ℤ) * (b : ℤ)) • (P.1 : (E⁄Ksep).Point) = 0 := by
        rw [mul_comm, mul_smul, h1, smul_zero]
      have hy : ((a : ℤ) * (b : ℤ)) • (P.2 : (E⁄Ksep).Point) = 0 := by
        rw [mul_smul, h2, smul_zero]
      push_cast
      rw [smul_add, hx, hy, add_zero]
    -- addition as a homomorphism `E[a] × E[b] →+ E[a * b]`
    let φ : AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ) ×
        AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ) →+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((a * b : ℕ) : ℤ) :=
      { toFun := fun P => ⟨(P.1 : (E⁄Ksep).Point) + (P.2 : (E⁄Ksep).Point), hmem P⟩
        map_zero' := by apply Subtype.ext; simp
        map_add' := by
          intro P Q
          apply Subtype.ext
          show ((P.1 + Q.1 : AddSubgroup.torsionBy (E⁄Ksep).Point (a : ℤ)) :
              (E⁄Ksep).Point) + ((P.2 + Q.2 : AddSubgroup.torsionBy (E⁄Ksep).Point (b : ℤ)) :
              (E⁄Ksep).Point) = ((P.1 : (E⁄Ksep).Point) + (P.2 : (E⁄Ksep).Point)) +
              ((Q.1 : (E⁄Ksep).Point) + (Q.2 : (E⁄Ksep).Point))
          push_cast
          exact add_add_add_comm _ _ _ _ }
    -- injectivity: a Bézout combination recovers each component from the sum
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro P hP
      have hP0 : (P.1 : (E⁄Ksep).Point) + (P.2 : (E⁄Ksep).Point) = 0 :=
        congrArg Subtype.val hP
      have h1 : (a : ℤ) • (P.1 : (E⁄Ksep).Point) = 0 := P.1.2
      have h2 : (b : ℤ) • (P.2 : (E⁄Ksep).Point) = 0 := P.2.2
      have hneg : (P.2 : (E⁄Ksep).Point) = -(P.1 : (E⁄Ksep).Point) := by
        rwa [add_comm, add_eq_zero_iff_eq_neg] at hP0
      have hb1 : (b : ℤ) • (P.1 : (E⁄Ksep).Point) = 0 := by
        have h3 : (b : ℤ) • -(P.1 : (E⁄Ksep).Point) = 0 := hneg ▸ h2
        simpa using h3
      have hP1 : (P.1 : (E⁄Ksep).Point) = 0 := by
        calc (P.1 : (E⁄Ksep).Point) = (1 : ℤ) • (P.1 : (E⁄Ksep).Point) := (one_smul _ _).symm
        _ = (u * (a : ℤ) + v * (b : ℤ)) • (P.1 : (E⁄Ksep).Point) := by rw [huv]
        _ = u • ((a : ℤ) • (P.1 : (E⁄Ksep).Point)) + v • ((b : ℤ) • (P.1 : (E⁄Ksep).Point)) := by
            rw [add_smul, mul_smul, mul_smul]
        _ = 0 := by rw [h1, hb1, smul_zero, smul_zero, add_zero]
      have hP2 : (P.2 : (E⁄Ksep).Point) = 0 := by rw [hneg, hP1, neg_zero]
      exact Prod.ext (Subtype.ext hP1) (Subtype.ext hP2)
    -- surjectivity: `x = v • (b • x) + u • (a • x)` splits any `a * b`-torsion point
    have hsurj : Function.Surjective φ := by
      intro x
      have hx : ((a : ℤ) * (b : ℤ)) • (x : (E⁄Ksep).Point) = 0 := by
        have h0 : ((a * b : ℕ) : ℤ) • (x : (E⁄Ksep).Point) = 0 := x.2
        push_cast at h0
        exact h0
      refine ⟨(⟨(v * (b : ℤ)) • (x : (E⁄Ksep).Point), ?_⟩,
               ⟨(u * (a : ℤ)) • (x : (E⁄Ksep).Point), ?_⟩), ?_⟩
      · show (a : ℤ) • (v * (b : ℤ)) • (x : (E⁄Ksep).Point) = 0
        rw [smul_smul, show (a : ℤ) * (v * (b : ℤ)) = v * ((a : ℤ) * (b : ℤ)) by ring,
          mul_smul, hx, smul_zero]
      · show (b : ℤ) • (u * (a : ℤ)) • (x : (E⁄Ksep).Point) = 0
        rw [smul_smul, show (b : ℤ) * (u * (a : ℤ)) = u * ((a : ℤ) * (b : ℤ)) by ring,
          mul_smul, hx, smul_zero]
      · apply Subtype.ext
        show (v * (b : ℤ)) • (x : (E⁄Ksep).Point) + (u * (a : ℤ)) • (x : (E⁄Ksep).Point) =
          (x : (E⁄Ksep).Point)
        rw [← add_smul, show v * (b : ℤ) + u * (a : ℤ) = u * (a : ℤ) + v * (b : ℤ) by ring,
          huv, one_smul]
    exact ⟨AddEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun P => rfl⟩
  obtain ⟨e, he⟩ := hpair
  obtain ⟨g, hg⟩ := hcrt
  refine ⟨A ⊗[R] B, inferInstance, inferInstance, inferInstance, inferInstance, hEt,
    (e.trans (AddEquiv.prodCongr fa fb)).trans g, ?_⟩
  intro σ φ
  -- unfold the composite equivalence on both sides
  have expand : ∀ ψ : (K ⊗[R] (A ⊗[R] B)) →ₐ[K] Ksep,
      (((e.trans (AddEquiv.prodCongr fa fb)).trans g)
          (Additive.ofMul (WithConv.toConv ψ)) : (E⁄Ksep).Point) =
        (fa (e (Additive.ofMul (WithConv.toConv ψ))).1 : (E⁄Ksep).Point) +
          (fb (e (Additive.ofMul (WithConv.toConv ψ))).2 : (E⁄Ksep).Point) := by
    intro ψ
    rw [AddEquiv.trans_apply, AddEquiv.trans_apply, hg]
    rfl
  rw [expand, expand, he σ φ]
  -- apply the two equivariance hypotheses componentwise and reassemble with `map_add`
  dsimp only
  simp [hfa σ, hfb σ, map_add]

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Ksep] in
/-- **Points separate a finite étale algebra** (PROVEN 2026-07-23; glue for the
Hopf-upgrade leaf `exists_bialgEquiv_of_algEquiv_conv` and for the
`EtaleGrothendieck` section below): an element of a finite
étale `K`-algebra killed by every `Kˢᵉᵖ`-point is zero. The algebra is reduced
(unramified over a field) and Artinian, so a nonzero element avoids some prime;
that prime is maximal, its residue field is a finite unramified — hence
separable — extension of `K`, which embeds into `Kˢᵉᵖ`, and the composite
point does not kill the element. -/
theorem eq_zero_of_forall_algHom_eq_zero
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (x : A) (hx : ∀ φ : A →ₐ[K] Ksep, φ x = 0) : x = 0 := by
  classical
  haveI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  by_contra hx0
  have hnil : x ∉ nilradical A := by
    rw [nilradical_eq_zero]
    simpa using hx0
  obtain ⟨p, hp, hxp⟩ : ∃ p : Ideal A, Ideal.IsPrime p ∧ x ∉ p := by
    by_contra hall
    push Not at hall
    exact hnil (nilradical_eq_sInf A ▸ Submodule.mem_sInf.mpr
      fun q hq => hall q hq)
  haveI : Ideal.IsPrime p := hp
  haveI : Ideal.IsMaximal p := IsArtinianRing.isMaximal_of_isPrime p
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  haveI : Algebra.IsSeparable K (A ⧸ p) :=
    Algebra.FormallyUnramified.isSeparable K (A ⧸ p)
  have hcontra := hx ((IsSepClosed.lift : (A ⧸ p) →ₐ[K] Ksep).comp
    (Ideal.Quotient.mkₐ K p))
  rw [AlgHom.comp_apply] at hcontra
  have hker : Ideal.Quotient.mkₐ K p x = 0 :=
    (IsSepClosed.lift : (A ⧸ p) →ₐ[K] Ksep).toRingHom.injective
      (by simpa using hcontra)
  exact hxp (by rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hker)

/-!
### The Gelfand transform onto equivariant functions at the infinite level

Support for `exists_algEquiv_of_algHom_equiv` below. For a finite étale
`K`-algebra `A`, the Gelfand transform `a ↦ (φ ↦ φ a)` maps `A` into the
`Gal(Kˢᵉᵖ/K)`-equivariant functions `(A →ₐ[K] Kˢᵉᵖ) → Kˢᵉᵖ`; it is injective by
the separation lemma `eq_zero_of_forall_algHom_eq_zero` (below) and surjective
by a dimension squeeze that needs NO point counting and no finite splitting
level: a `K`-linearly independent family of equivariant functions is
automatically `Kˢᵉᵖ`-linearly independent (Speiser's lemma, the minimal-relation
argument of split Galois descent run for the full group `Gal(Kˢᵉᵖ/K)`, with
`InfiniteGalois.mem_range_algebraMap_iff_fixed` supplying "fixed by all of
`Gal(Kˢᵉᵖ/K)` means in `K`"), so an equivariant function outside the image of
the Gelfand transform would produce `dim_K A + 1` many `Kˢᵉᵖ`-independent
vectors inside the function space on the points, whose `Kˢᵉᵖ`-dimension
`#points` is at most `dim_K A` by `card_algHom_le_finrank`.
-/

section EtaleGrothendieck

variable {S : Type*}

omit [DecidableEq Ksep] in
/-- **Speiser's lemma at the infinite level** (PROVEN; the descent half of the
Gelfand identification feeding `exists_algEquiv_of_algHom_equiv`): a family of
`Gal(Kˢᵉᵖ/K)`-equivariant functions on a `Gal(Kˢᵉᵖ/K)`-set `S` that is linearly
independent over `K` is linearly independent over `Kˢᵉᵖ`. Minimal-relation
argument: normalize a shortest nontrivial `Kˢᵉᵖ`-relation to have a coefficient
`1`, subtract its Galois translates (again relations, by equivariance of the
functions), conclude by strong induction that all coefficients are fixed by
`Gal(Kˢᵉᵖ/K)`, hence lie in `K` (`Kˢᵉᵖ/K` is Galois, being a separable
closure) — contradicting `K`-independence. No group laws of the action and no
finiteness of `S` are needed. -/
theorem linearIndependent_sepClosure_of_equivariant
    (act : (Ksep ≃ₐ[K] Ksep) → S → S) {ι : Type*} {v : ι → S → Ksep}
    (hmem : ∀ (i : ι) (σ : Ksep ≃ₐ[K] Ksep) (s : S), v i (act σ s) = σ (v i s))
    (hv : LinearIndependent K v) : LinearIndependent Ksep v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀s, hi₀⟩ := hne
    set c' : ι → Ksep := fun i => (c i₀)⁻¹ * c i with hc'def
    have hrel : ∑ i ∈ s, c' i • v i = 0 := by
      have h1 := congrArg (fun f : S → Ksep => (c i₀)⁻¹ • f) hc
      simpa [Finset.smul_sum, smul_smul, hc'def] using h1
    have hc'i₀ : c' i₀ = 1 := by
      simp only [hc'def]
      exact inv_mul_cancel₀ hi₀
    have hrelg : ∀ σ : Ksep ≃ₐ[K] Ksep, ∑ i ∈ s, σ (c' i) • v i = 0 := by
      intro σ
      have h0 : ∀ b : S, ∑ i ∈ s, c' i * v i (act σ⁻¹ b) = 0 := by
        intro b
        have h2 := congrFun hrel (act σ⁻¹ b)
        simpa using h2
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc ∑ i ∈ s, σ (c' i) * v i b
          = ∑ i ∈ s, σ (c' i) * σ (v i (act σ⁻¹ b)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hmem i σ⁻¹ b, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = σ (∑ i ∈ s, c' i * v i (act σ⁻¹ b)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => (map_mul σ _ _).symm
        _ = 0 := by rw [h0 b, map_zero]
    have hfix : ∀ (σ : Ksep ≃ₐ[K] Ksep) (i : ι), i ∈ s → σ (c' i) = c' i := by
      intro σ i hi
      have h3 : ∑ j ∈ s, (σ (c' j) - c' j) • v j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hrelg σ, hrel, sub_zero]
      have h4 : ∑ j ∈ s.erase i₀, (σ (c' j) - c' j) • v j = 0 := by
        rwa [← Finset.add_sum_erase _ _ hi₀s, hc'i₀, map_one, sub_self, zero_smul,
          zero_add] at h3
      have h5 := ih (s.erase i₀) (Finset.erase_ssubset hi₀s) _ h4
      rcases eq_or_ne i i₀ with rfl | hne'
      · rw [hc'i₀, map_one]
      · exact sub_eq_zero.mp (h5 i (Finset.mem_erase.mpr ⟨hne', hi⟩))
    have hK : ∀ i : ι, ∃ k : K, i ∈ s → algebraMap K Ksep k = c' i := by
      intro i
      by_cases hi : i ∈ s
      · have hmem' : c' i ∈ Set.range (algebraMap K Ksep) := by
          rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
          exact fun σ => hfix σ i hi
        exact ⟨hmem'.choose, fun _ => hmem'.choose_spec⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose k hk using hK
    have hrelK : ∑ i ∈ s, k i • v i = 0 := by
      have hcoe : ∑ i ∈ s, k i • v i = ∑ i ∈ s, c' i • v i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hk i hi, algebraMap_smul]
      rw [hcoe, hrel]
    have h6 := linearIndependent_iff'.mp hv s k hrelK i₀ hi₀s
    rw [← hk i₀ hi₀s, h6, map_zero] at hc'i₀
    exact zero_ne_one hc'i₀

omit [DecidableEq Ksep] in
/-- **The equivariant-functions algebra on a `Gal(Kˢᵉᵖ/K)`-set** (glue for
`exists_algEquiv_of_algHom_equiv`): the `K`-subalgebra of functions `S → Kˢᵉᵖ`
commuting with the Galois action `act` — the infinite-level counterpart of
`galoisEquivariantAlgebra` for a set-level action. -/
def sepPointsEquivariantSubalgebra (act : (Ksep ≃ₐ[K] Ksep) → S → S) :
    Subalgebra K (S → Ksep) where
  carrier := {F | ∀ (σ : Ksep ≃ₐ[K] Ksep) (s : S), F (act σ s) = σ (F s)}
  mul_mem' := fun hf hg σ s => by simp only [Pi.mul_apply, map_mul, hf σ s, hg σ s]
  one_mem' := fun σ s => by simp only [Pi.one_apply, map_one]
  add_mem' := fun hf hg σ s => by simp only [Pi.add_apply, map_add, hf σ s, hg σ s]
  zero_mem' := fun σ s => by simp only [Pi.zero_apply, map_zero]
  algebraMap_mem' := fun r σ s => by
    simp only [Pi.algebraMap_apply, AlgEquiv.commutes]

omit [IsSepClosure K Ksep] [DecidableEq Ksep] in
/-- Membership in the equivariant subalgebra, unfolded. -/
theorem mem_sepPointsEquivariantSubalgebra_iff {act : (Ksep ≃ₐ[K] Ksep) → S → S}
    {F : S → Ksep} :
    F ∈ sepPointsEquivariantSubalgebra K Ksep act ↔
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (s : S), F (act σ s) = σ (F s) :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Ksep] in
/-- **Gelfand surjectivity for finite étale algebras** (PROVEN; the descent core
of `exists_algEquiv_of_algHom_equiv`): every `Gal(Kˢᵉᵖ/K)`-equivariant function
on the `Kˢᵉᵖ`-points of a finite étale `K`-algebra is evaluation at an element.
Proof by dimension squeeze: were `F` outside the image of the (injective, by
separation) Gelfand transform, adjoining it to the image of a basis would give
`dim_K A + 1` many `K`-independent equivariant functions, `Kˢᵉᵖ`-independent by
Speiser's lemma, inside a function space of `Kˢᵉᵖ`-dimension
`#(A →ₐ[K] Kˢᵉᵖ) ≤ dim_K A` (`card_algHom_le_finrank`). -/
theorem exists_eval_eq_of_equivariant
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (F : (A →ₐ[K] Ksep) → Ksep)
    (hF : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : A →ₐ[K] Ksep),
      F (σ.toAlgHom.comp φ) = σ (F φ)) :
    ∃ a : A, ∀ φ : A →ₐ[K] Ksep, φ a = F φ := by
  classical
  haveI : Finite (A →ₐ[K] Ksep) := Finite.algHom K A Ksep
  haveI := Fintype.ofFinite (A →ₐ[K] Ksep)
  let ε : A →ₐ[K] ((A →ₐ[K] Ksep) → Ksep) := AlgHom.pi (fun φ => φ)
  have hεinj : Function.Injective ε := by
    intro x y hxy
    have hzero : x - y = 0 := by
      refine eq_zero_of_forall_algHom_eq_zero K Ksep A _ fun φ => ?_
      rw [map_sub, sub_eq_zero]
      exact congrFun hxy φ
    exact sub_eq_zero.mp hzero
  by_contra hnot
  push Not at hnot
  have hFnot : F ∉ Submodule.span K
      (Set.range fun i => ε (Module.finBasis K A i)) := by
    intro hFmem
    have hrange : Submodule.span K (Set.range fun i => ε (Module.finBasis K A i)) =
        LinearMap.range ε.toLinearMap := by
      have h1 : (Set.range fun i => ε (Module.finBasis K A i)) =
          ε.toLinearMap '' Set.range (Module.finBasis K A) := by
        rw [← Set.range_comp]
        rfl
      rw [h1, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top]
    rw [hrange] at hFmem
    obtain ⟨a, ha⟩ := hFmem
    obtain ⟨φ, hφ⟩ := hnot a
    exact hφ (congrFun ha φ)
  have hvind : LinearIndependent K fun i => ε (Module.finBasis K A i) :=
    (Module.finBasis K A).linearIndependent.map' ε.toLinearMap
      (LinearMap.ker_eq_bot.mpr hεinj)
  have hopt : LinearIndependent K
      (fun o => Option.casesOn' o F fun i => ε (Module.finBasis K A i)) :=
    hvind.option hFnot
  have hΩ : LinearIndependent Ksep
      (fun o => Option.casesOn' o F fun i => ε (Module.finBasis K A i)) := by
    refine linearIndependent_sepClosure_of_equivariant K Ksep
      (fun σ φ => σ.toAlgHom.comp φ) ?_ hopt
    intro o σ φ
    cases o with
    | none => exact hF σ φ
    | some i => rfl
  have hcard := hΩ.fintype_card_le_finrank
  rw [Module.finrank_pi, Fintype.card_option, Fintype.card_fin] at hcard
  have hle := card_algHom_le_finrank K A Ksep
  rw [Nat.card_eq_fintype_card] at hle
  omega

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Ksep] in
/-- **One direction of Grothendieck full faithfulness** (PROVEN; glue for
`exists_algEquiv_of_algHom_equiv`): an equivariant map `t` from the
`Kˢᵉᵖ`-points of a finite étale `K`-algebra `A` to the points of any `K`-algebra
`B` is induced by an algebra homomorphism `B →ₐ[K] A`. The homomorphism is the
composite of `b ↦ (φ ↦ t φ b)` (landing in the equivariant functions on the
points of `A`) with the inverse of the Gelfand transform of `A`, an isomorphism
onto the equivariant functions by separation and
`exists_eval_eq_of_equivariant`. -/
theorem exists_algHom_of_algHom_map
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (B : Type*) [CommRing B] [Algebra K B]
    (t : (A →ₐ[K] Ksep) → (B →ₐ[K] Ksep))
    (ht : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : A →ₐ[K] Ksep),
      t (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (t φ)) :
    ∃ e₀ : B →ₐ[K] A, ∀ (φ : A →ₐ[K] Ksep) (b : B), φ (e₀ b) = t φ b := by
  classical
  let act : (Ksep ≃ₐ[K] Ksep) → (A →ₐ[K] Ksep) → (A →ₐ[K] Ksep) :=
    fun σ φ => σ.toAlgHom.comp φ
  let ε : A →ₐ[K] ((A →ₐ[K] Ksep) → Ksep) := AlgHom.pi (fun φ => φ)
  have hεmem : ∀ a : A, ε a ∈ sepPointsEquivariantSubalgebra K Ksep act :=
    fun a => (mem_sepPointsEquivariantSubalgebra_iff K Ksep).mpr fun σ φ => rfl
  have hεbij : Function.Bijective
      (ε.codRestrict (sepPointsEquivariantSubalgebra K Ksep act) hεmem) := by
    constructor
    · intro x y hxy
      have hxy' : ∀ φ : A →ₐ[K] Ksep, φ x = φ y := fun φ =>
        congrFun (congrArg Subtype.val hxy) φ
      have hzero : x - y = 0 := by
        refine eq_zero_of_forall_algHom_eq_zero K Ksep A _ fun φ => ?_
        rw [map_sub, sub_eq_zero]
        exact hxy' φ
      exact sub_eq_zero.mp hzero
    · rintro ⟨F, hF⟩
      obtain ⟨a, ha⟩ := exists_eval_eq_of_equivariant K Ksep A F
        ((mem_sepPointsEquivariantSubalgebra_iff K Ksep).mp hF)
      exact ⟨a, Subtype.ext (funext fun φ => ha φ)⟩
  let εe : A ≃ₐ[K] (sepPointsEquivariantSubalgebra K Ksep act) :=
    AlgEquiv.ofBijective
      (ε.codRestrict (sepPointsEquivariantSubalgebra K Ksep act) hεmem) hεbij
  let T : B →ₐ[K] ((A →ₐ[K] Ksep) → Ksep) := AlgHom.pi (fun φ => t φ)
  have hTmem : ∀ b : B, T b ∈ sepPointsEquivariantSubalgebra K Ksep act := by
    intro b
    refine (mem_sepPointsEquivariantSubalgebra_iff K Ksep).mpr fun σ φ => ?_
    show (t (σ.toAlgHom.comp φ)) b = σ ((t φ) b)
    rw [ht σ φ]
    rfl
  refine ⟨εe.symm.toAlgHom.comp
    (T.codRestrict (sepPointsEquivariantSubalgebra K Ksep act) hTmem), ?_⟩
  intro φ b
  have h1 : εe (εe.symm
      (T.codRestrict (sepPointsEquivariantSubalgebra K Ksep act) hTmem b)) =
      T.codRestrict (sepPointsEquivariantSubalgebra K Ksep act) hTmem b :=
    εe.apply_symm_apply _
  exact congrFun (congrArg Subtype.val h1) φ

end EtaleGrothendieck

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Ksep] in
/-- **Grothendieck full faithfulness, algebra half** (PROVEN 2026-07-23;
curve-free — the descent core of the comparison leaf
`exists_bialgEquiv_of_torsion_points_equiv`): a `Gal(Kˢᵉᵖ/K)`-equivariant
bijection between the `Kˢᵉᵖ`-points of two finite étale `K`-algebras is induced
by composition with a (unique, but only existence is stated) `K`-algebra
isomorphism. This is the full faithfulness of the Grothendieck
anti-equivalence between finite étale `K`-algebras and finite discrete Galois
sets. Proof, via the `EtaleGrothendieck` section above: the two directions of
the bijection induce (`exists_algHom_of_algHom_map`, the Gelfand transform onto
the equivariant functions of the point set — injective by separation,
surjective by Speiser independence plus `card_algHom_le_finrank`, with no point
counting) algebra homomorphisms `e₀ : B →ₐ[K] A` and `e₁ : A →ₐ[K] B` acting
on points as `g` and `g.symm` respectively; the composites act on points as the
identity, hence are the identity by separation
(`eq_zero_of_forall_algHom_eq_zero`), and `AlgEquiv.ofAlgHom` assembles the
isomorphism. -/
theorem exists_algEquiv_of_algHom_equiv
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (B : Type*) [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (g : (A →ₐ[K] Ksep) ≃ (B →ₐ[K] Ksep))
    (hg : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : A →ₐ[K] Ksep),
      g (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (g φ)) :
    ∃ e : B ≃ₐ[K] A, ∀ φ : A →ₐ[K] Ksep, g φ = φ.comp e.toAlgHom := by
  classical
  have hgsymm : ∀ (σ : Ksep ≃ₐ[K] Ksep) (ψ : B →ₐ[K] Ksep),
      g.symm (σ.toAlgHom.comp ψ) = σ.toAlgHom.comp (g.symm ψ) := by
    intro σ ψ
    apply g.injective
    rw [Equiv.apply_symm_apply, hg σ (g.symm ψ), Equiv.apply_symm_apply]
  obtain ⟨e₀, he₀⟩ := exists_algHom_of_algHom_map K Ksep A B (fun φ => g φ)
    (fun σ φ => hg σ φ)
  obtain ⟨e₁, he₁⟩ := exists_algHom_of_algHom_map K Ksep B A (fun ψ => g.symm ψ)
    (fun σ ψ => hgsymm σ ψ)
  have h1 : e₀.comp e₁ = AlgHom.id K A := by
    apply AlgHom.ext
    intro a
    have hzero : e₀ (e₁ a) - a = 0 := by
      refine eq_zero_of_forall_algHom_eq_zero K Ksep A _ fun φ => ?_
      rw [map_sub, sub_eq_zero, he₀ φ (e₁ a), he₁ (g φ) a, Equiv.symm_apply_apply]
    have h := sub_eq_zero.mp hzero
    simpa using h
  have h2 : e₁.comp e₀ = AlgHom.id K B := by
    apply AlgHom.ext
    intro b
    have hzero : e₁ (e₀ b) - b = 0 := by
      refine eq_zero_of_forall_algHom_eq_zero K Ksep B _ fun ψ => ?_
      rw [map_sub, sub_eq_zero, he₁ ψ (e₀ b), he₀ (g.symm ψ) b, Equiv.apply_symm_apply]
    have h := sub_eq_zero.mp hzero
    simpa using h
  refine ⟨AlgEquiv.ofAlgHom e₀ e₁ h1 h2, fun φ => AlgHom.ext fun b => ?_⟩
  exact (he₀ φ b).symm

omit [DecidableEq Ksep] in
/-- **Grothendieck full faithfulness, Hopf upgrade** (PROVEN 2026-07-23;
curve-free — the coalgebra-compatibility core of the comparison leaf
`exists_bialgEquiv_of_torsion_points_equiv`): a `K`-algebra isomorphism of
finite étale Hopf `K`-algebras whose composition action on `Kˢᵉᵖ`-points
respects the convolution unit (`hone`) and the convolution product (`hmul`) is
automatically compatible with the comultiplications and counits, so the two
Hopf algebras are isomorphic as bialgebras. Proof: points separate a finite
étale `K`-algebra (`eq_zero_of_forall_algHom_eq_zero`, applied to
`HK₂ ⊗[K] HK₂`, which is finite étale by base change and transitivity), every
point of `HK₂ ⊗[K] HK₂` is the `Algebra.TensorProduct.lift` of its two
restrictions (images commute in the commutative `Kˢᵉᵖ`); testing `comul ∘ e⁻¹`
against `(e⁻¹ ⊗ e⁻¹) ∘ comul` on such a point is, after unfolding
`AlgHom.convMul_apply`, exactly the hypothesis `hmul` transported
through `e⁻¹`, and testing the counits is `hone`; conclude with
`BialgEquiv.ofAlgEquiv` on `e.symm`. (The antipode needs no separate check:
`≃ₐc` is a bialgebra equivalence, and antipodes are automatically
preserved.) -/
theorem exists_bialgEquiv_of_algEquiv_conv
    (HK₁ : Type*) [CommRing HK₁] [HopfAlgebra K HK₁]
    [Module.Finite K HK₁] [Algebra.Etale K HK₁]
    (HK₂ : Type*) [CommRing HK₂] [HopfAlgebra K HK₂]
    [Module.Finite K HK₂] [Algebra.Etale K HK₂]
    (e : HK₂ ≃ₐ[K] HK₁)
    (hone : ((1 : WithConv (HK₁ →ₐ[K] Ksep)).ofConv).comp e.toAlgHom =
      (1 : WithConv (HK₂ →ₐ[K] Ksep)).ofConv)
    (hmul : ∀ φ ψ : HK₁ →ₐ[K] Ksep,
      ((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp e.toAlgHom =
        (WithConv.toConv (φ.comp e.toAlgHom) *
          WithConv.toConv (ψ.comp e.toAlgHom)).ofConv) :
    Nonempty (HK₁ ≃ₐc[K] HK₂) := by
  classical
  -- the underlying algebra isomorphism of the bialgebra equivalence
  set f : HK₁ ≃ₐ[K] HK₂ := e.symm with hf
  have hfe : (f.toAlgHom).comp e.toAlgHom = AlgHom.id K HK₂ := by
    apply AlgHom.ext
    intro b
    simp [hf]
  -- composing a point of `HK₂` back through `e` then `f` is the identity
  have hcomp_fe : ∀ χ : HK₂ →ₐ[K] Ksep,
      (χ.comp f.toAlgHom).comp e.toAlgHom = χ := by
    intro χ
    rw [AlgHom.comp_assoc, hfe, AlgHom.comp_id]
  -- the `e.symm`-transport of `hmul`
  have hmul' : ∀ φ ψ : HK₂ →ₐ[K] Ksep,
      (WithConv.toConv (φ.comp f.toAlgHom) *
        WithConv.toConv (ψ.comp f.toAlgHom)).ofConv =
        ((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp f.toAlgHom := by
    intro φ ψ
    have h1 := hmul (φ.comp f.toAlgHom) (ψ.comp f.toAlgHom)
    rw [hcomp_fe φ, hcomp_fe ψ] at h1
    calc (WithConv.toConv (φ.comp f.toAlgHom) *
        WithConv.toConv (ψ.comp f.toAlgHom)).ofConv
        = (((WithConv.toConv (φ.comp f.toAlgHom) *
            WithConv.toConv (ψ.comp f.toAlgHom)).ofConv).comp e.toAlgHom).comp
              f.toAlgHom := by
          rw [AlgHom.comp_assoc]
          rw [show e.toAlgHom.comp f.toAlgHom = AlgHom.id K HK₁ from
            AlgHom.ext fun a => by simp [hf]]
          rw [AlgHom.comp_id]
      _ = ((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp f.toAlgHom := by
          rw [h1]
  -- étale-ness and finiteness of `HK₂ ⊗[K] HK₂`
  haveI hEt2 : Algebra.Etale K (HK₂ ⊗[K] HK₂) :=
    Algebra.Etale.comp K HK₂ (HK₂ ⊗[K] HK₂)
  -- counit compatibility, from `hone` and injectivity of `K → Kˢᵉᵖ`
  have hcounit : (Bialgebra.counitAlgHom K HK₂).comp (f : HK₁ →ₐ[K] HK₂) =
      Bialgebra.counitAlgHom K HK₁ := by
    apply AlgHom.ext
    intro a
    have h1 := AlgHom.congr_fun hone (f a)
    have h2 : ((1 : WithConv (HK₁ →ₐ[K] Ksep)).ofConv).comp e.toAlgHom (f a) =
        algebraMap K Ksep (Coalgebra.counit (e (f a))) := rfl
    have h3 : ((1 : WithConv (HK₂ →ₐ[K] Ksep)).ofConv) (f a) =
        algebraMap K Ksep (Coalgebra.counit (f a)) := rfl
    rw [h2, h3] at h1
    have h4 : e (f a) = a := by simp [hf]
    rw [h4] at h1
    exact ((algebraMap K Ksep).injective h1).symm
  -- comultiplication compatibility, tested against all points of `HK₂ ⊗ HK₂`
  have hcomul : (Algebra.TensorProduct.map (f : HK₁ →ₐ[K] HK₂)
      (f : HK₁ →ₐ[K] HK₂)).comp (Bialgebra.comulAlgHom K HK₁) =
      (Bialgebra.comulAlgHom K HK₂).comp (f : HK₁ →ₐ[K] HK₂) := by
    apply AlgHom.ext
    intro a
    -- separation: it suffices to test against every point `χ`
    have hsep := eq_zero_of_forall_algHom_eq_zero K Ksep (HK₂ ⊗[K] HK₂)
      ((Algebra.TensorProduct.map (f : HK₁ →ₐ[K] HK₂)
          (f : HK₁ →ₐ[K] HK₂)).comp (Bialgebra.comulAlgHom K HK₁) a -
        (Bialgebra.comulAlgHom K HK₂).comp (f : HK₁ →ₐ[K] HK₂) a)
    rw [sub_eq_zero] at hsep
    apply hsep
    intro χ
    rw [map_sub, sub_eq_zero]
    -- decompose the point `χ` into its two restrictions
    set φ := χ.comp Algebra.TensorProduct.includeLeft with hφ
    set ψ := χ.comp (Algebra.TensorProduct.includeRight :
      HK₂ →ₐ[K] HK₂ ⊗[K] HK₂) with hψ
    have hχ : χ = Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _ := by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro b
        simp [hφ]
      · apply AlgHom.ext
        intro b
        simp [hψ]
    -- the left side is the convolution of the transported points, at `a`
    have hleft : χ ((Algebra.TensorProduct.map (f : HK₁ →ₐ[K] HK₂)
        (f : HK₁ →ₐ[K] HK₂)).comp (Bialgebra.comulAlgHom K HK₁) a) =
        ((WithConv.toConv (φ.comp f.toAlgHom) *
          WithConv.toConv (ψ.comp f.toAlgHom)).ofConv) a := by
      rw [hχ]
      have hlift : (Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _).comp
          ((Algebra.TensorProduct.map (f : HK₁ →ₐ[K] HK₂)
            (f : HK₁ →ₐ[K] HK₂))) =
          Algebra.TensorProduct.lift (φ.comp f.toAlgHom) (ψ.comp f.toAlgHom)
            (fun _ _ => Commute.all _ _) := by
        apply Algebra.TensorProduct.ext
        · apply AlgHom.ext
          intro b
          simp
        · apply AlgHom.ext
          intro b
          simp
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (Algebra.TensorProduct.lift φ ψ _),
        hlift]
      rw [AlgHom.convMul_apply]
      rfl
    -- the right side is the convolution of the original points, at `f a`
    have hright : χ ((Bialgebra.comulAlgHom K HK₂).comp (f : HK₁ →ₐ[K] HK₂) a) =
        (((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp f.toAlgHom) a := by
      rw [hχ]
      rw [AlgHom.comp_apply]
      rw [show (Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _)
          ((Bialgebra.comulAlgHom K HK₂) ((f : HK₁ →ₐ[K] HK₂) a)) =
        ((WithConv.toConv φ * WithConv.toConv ψ).ofConv) ((f : HK₁ →ₐ[K] HK₂) a) from
          (AlgHom.convMul_apply _ _ _).symm]
      rfl
    rw [hleft, hright, hmul' φ ψ]
  exact ⟨BialgEquiv.ofAlgEquiv f hcounit hcomul⟩

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain R] [IsDiscreteValuationRing R] [E.IsElliptic]
  [E.HasGoodReduction R] in
/-- **Grothendieck full faithfulness for torsion points** (DECOMPOSED
2026-07-23 into the two curve-free leaves above — the algebra-level full
faithfulness `exists_algEquiv_of_algHom_equiv` and the Hopf upgrade
`exists_bialgEquiv_of_algEquiv_conv`; the assembly below is proven): two finite
étale Hopf `K`-algebras whose `Kˢᵉᵖ`-point groups are `Gal(Kˢᵉᵖ/K)`-equivariantly
isomorphic to the same `m`-torsion Galois module are isomorphic as Hopf algebras.
The assembly composes the two point-group identifications into an equivariant
convolution-monoid isomorphism `g` of the point sets, obtains from the algebra
leaf an algebra isomorphism inducing `g` by composition, and feeds the
multiplicativity and unitality of `g` (inherited from the additivity of `f₁`
and `f₂`) to the Hopf-upgrade leaf. -/
theorem WeierstrassCurve.exists_bialgEquiv_of_torsion_points_equiv
    (m : ℕ)
    (HK₁ : Type*) [CommRing HK₁] [HopfAlgebra K HK₁]
    [Module.Finite K HK₁] [Algebra.Etale K HK₁]
    (HK₂ : Type*) [CommRing HK₂] [HopfAlgebra K HK₂]
    [Module.Finite K HK₂] [Algebra.Etale K HK₂]
    (f₁ : Additive (WithConv (HK₁ →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf₁ : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK₁ →ₐ[K] Ksep),
      (f₁ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f₁ (Additive.ofMul (WithConv.toConv φ))))
    (f₂ : Additive (WithConv (HK₂ →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf₂ : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK₂ →ₐ[K] Ksep),
      (f₂ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f₂ (Additive.ofMul (WithConv.toConv φ)))) :
    Nonempty (HK₁ ≃ₐc[K] HK₂) := by
  classical
  -- the composite point-group identification, as a bijection of plain point sets
  set gAdd : Additive (WithConv (HK₁ →ₐ[K] Ksep)) ≃+
      Additive (WithConv (HK₂ →ₐ[K] Ksep)) := f₁.trans f₂.symm with hgAdd
  let g : (HK₁ →ₐ[K] Ksep) ≃ (HK₂ →ₐ[K] Ksep) :=
    ((WithConv.equiv (HK₁ →ₐ[K] Ksep)).symm.trans
      (Additive.ofMul.trans (gAdd.toEquiv.trans
        (Additive.toMul.trans (WithConv.equiv (HK₂ →ₐ[K] Ksep))))))
  have gdef : ∀ φ : HK₁ →ₐ[K] Ksep,
      g φ = (Additive.toMul (gAdd (Additive.ofMul (WithConv.toConv φ)))).ofConv :=
    fun _ => rfl
  -- `g` intertwines the two identifications with the torsion module
  have hkey : ∀ φ : HK₁ →ₐ[K] Ksep,
      f₂ (Additive.ofMul (WithConv.toConv (g φ))) =
        f₁ (Additive.ofMul (WithConv.toConv φ)) := by
    intro φ
    rw [gdef, WithConv.toConv_ofConv, ofMul_toMul, hgAdd,
      AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  -- equivariance of `g`, from the equivariance of `f₁` and `f₂`
  have hgequi : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK₁ →ₐ[K] Ksep),
      g (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (g φ) := by
    intro σ φ
    have h1 : f₂ (Additive.ofMul (WithConv.toConv (g (σ.toAlgHom.comp φ)))) =
        f₂ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp (g φ)))) := by
      apply Subtype.ext
      calc (f₂ (Additive.ofMul (WithConv.toConv (g (σ.toAlgHom.comp φ)))) :
          (E⁄Ksep).Point)
          = (f₁ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
              (E⁄Ksep).Point) := by rw [hkey]
        _ = Affine.Point.map σ.toAlgHom
              (f₁ (Additive.ofMul (WithConv.toConv φ))) := hf₁ σ φ
        _ = Affine.Point.map σ.toAlgHom
              (f₂ (Additive.ofMul (WithConv.toConv (g φ)))) := by rw [hkey]
        _ = (f₂ (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp (g φ)))) :
              (E⁄Ksep).Point) := (hf₂ σ (g φ)).symm
    exact WithConv.toConv_injective (Additive.ofMul.injective (f₂.injective h1))
  obtain ⟨e, he⟩ := exists_algEquiv_of_algHom_equiv K Ksep HK₁ HK₂ g hgequi
  -- unitality of `g`, from `gAdd 0 = 0`
  have hone : ((1 : WithConv (HK₁ →ₐ[K] Ksep)).ofConv).comp e.toAlgHom =
      (1 : WithConv (HK₂ →ₐ[K] Ksep)).ofConv := by
    rw [← he, gdef, WithConv.toConv_ofConv]
    rw [show Additive.ofMul (1 : WithConv (HK₁ →ₐ[K] Ksep)) =
      (0 : Additive (WithConv (HK₁ →ₐ[K] Ksep))) from rfl, map_zero]
    rfl
  -- multiplicativity of `g`, from the additivity of `gAdd`
  have hmul : ∀ φ ψ : HK₁ →ₐ[K] Ksep,
      ((WithConv.toConv φ * WithConv.toConv ψ).ofConv).comp e.toAlgHom =
        (WithConv.toConv (φ.comp e.toAlgHom) *
          WithConv.toConv (ψ.comp e.toAlgHom)).ofConv := by
    intro φ ψ
    have h₃ := (he ((WithConv.toConv φ * WithConv.toConv ψ).ofConv)).symm
    rw [← he φ, ← he ψ, h₃]
    simp only [gdef, WithConv.toConv_ofConv, ofMul_mul, map_add, toMul_add]
  exact exists_bialgEquiv_of_algEquiv_conv K Ksep HK₁ HK₂ e hone hmul

set_option backward.isDefEq.respectTransparency false in
/-- **The Katz–Mazur Hopf order** (sorry node; the CURVE half of the decomposed
Katz–Mazur existence leaf `exists_torsion_flat_model_of_good_reduction_prime_pow`,
freed 2026-07-23 of all structure transport, and stated for ANY torsion order
`m` nonzero in `K` — no primality and no non-invertibility in `R` is needed for
the order to exist): inside the finite étale Hopf `K`-algebra `HK` of the
`m`-torsion of a good-reduction curve, some finitely generated `R`-subalgebra
`H₀` spans `HK` over `K` and is closed under the Hopf structure maps — the
counit takes `H₀` into `R`, the antipode preserves `H₀`, and the
comultiplication takes `H₀` into the `R`-span of the pure tensors of `H₀`.
Unlike the unramified case, `H₀` is NOT the integral closure of `R` (for `μ_p`
over `ℤ_p` the normalization has a special fibre with two connected components
of lengths `1` and `p - 1`, which is not a group scheme). The mathematical
content is [Katz–Mazur, *Arithmetic moduli of elliptic curves*, Thm 2.3.1]:
`H₀` is (the image in the generic fibre of) the affine algebra of the kernel
`𝓔[m]` of multiplication by `m` on the elliptic scheme `𝓔` of the minimal
(good-reduction) Weierstrass equation. It suffices to construct the order for
ONE `HK` carrying an equivariant points isomorphism: any other is Hopf-isomorphic
to it by `exists_bialgEquiv_of_torsion_points_equiv` (proven), and Hopf-closed
orders transport along Hopf isomorphisms.

SCHEME-FREE CONSTRUCTION ROADMAP (worked out 2026-07-23, restated for the
Hopf-ORDER formulation; `𝓔[m]` is flat, so it is the schematic closure of its
generic fibre, so `H₀` is the image of the functions on any affine open
`U ⊇ 𝓔[m]` inside the étale generic-fibre algebra):

1. Carrier. Realize `HK` concretely as the `Gal(L/K)`-equivariant functions
   `V → L` of the `GaloisEtalePackage` section, `V := E(Kˢᵉᵖ)[m]` (finite by
   `torsion_finite_of_ne_zero`), `L` a finite Galois splitting subextension —
   or transport the order constructed there along the Hopf isomorphism above.
2. Avoiding denominator. Choose `h ∈ R[X]` monic of degree `d ≥ 2` whose
   reduction is coprime to the reduced affine-torsion locus: `h(x(P))` is a
   unit of the valuation ring for every torsion point `P` with integral
   abscissa (possible because the residue field admits irreducibles of
   arbitrarily large degree avoiding the finitely many torsion abscissa
   residues; for non-integral abscissas `v(h(x(P))) = d·v(x(P)) < 0`
   automatically). Then `U := 𝓔 ∖ V(h ∘ x)` contains the whole kernel,
   including the origin.
3. Generators. `H₀` := the `R`-subalgebra of equivariant functions generated
   by the finitely many `g_{a,b} : P ↦ x(P)^a y(P)^b / h(x(P))^j` (with
   `2a + 3b ≤ 2dj`, `b ≤ 1`, value `0`-or-limit at `P = 0`; these are the
   monomial sections of `Γ(U)` restricted to the kernel). Each `g_{a,b}` has
   integral values at every point (choice of `h`), hence is integral over
   `R`: `H₀` is module-finite (`(Subalgebra.toSubmodule H₀).FG`).
4. Spanning. `K · H₀` is a `K`-subalgebra of the étale algebra separating the
   `Kˢᵉᵖ`-points (the `g_{a,b}` separate affine torsion points from each
   other and from the origin), and a separating subalgebra of a finite étale
   algebra is everything (both are étale — subalgebras of separable algebras
   are separable — so `dim = #points` on both sides, restriction of points is
   injective by separation and surjective by integrality lifting; compare the
   dimension-squeeze route of `exists_eval_eq_of_equivariant`, which proves
   the spanning without any point counting). This is the span hypothesis
   `Submodule.span K H₀ = ⊤`.
5. Hopf-closure — THE Katz–Mazur core: `Δ g_{a,b}` lies in the `R`-span of
   pure tensors of `H₀`, i.e. the two-variable functions
   `(P, Q) ↦ g_{a,b}(P + Q)` are `R`-polynomial in `g_{a',b'}(P),
   g_{a'',b''}(Q)`. This is the integrality of the addition law relative to
   `h` on the kernel — the point where the division-polynomial arithmetic
   enters: the addition formulas have denominators `(x(P) - x(Q))²` resp.
   `ψ²`, controlled on the torsion locus by the monic
   `(Φ n).eval X - ξ * (ΨSq n).eval X` (degree `n²` over `R[ξ]`) and the
   fibrewise coprimality `isCoprime_Φ_ΨSq` (proven,
   `Fermat.FLT.EllipticCurve.PhiPsiCoprime`). Counit and antipode closure are
   immediate (`ε g = g(0)`, integral over `R` and in `K`, hence in the
   integrally closed DVR `R`; `S g = g ∘ (-1)` is again a generator up to the
   curve relation).

For the Frey curve application (`R = ℤ_(p)`, `K = ℚ`, `m = p`) the same
object is the kernel of `[p]` on the good-reduction Weierstrass model; the
prime case admits no genuine shortcut past the origin chart, because the
connected component of `𝓔[p]` (where the model is NOT étale) is present
whenever `p` is not invertible in `R`. -/
theorem WeierstrassCurve.exists_hopf_order_of_good_reduction
    (m : ℕ) (hm : (m : K) ≠ 0)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    [Algebra R HK] [IsScalarTower R K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ H₀ : Subalgebra R HK,
      (Subalgebra.toSubmodule H₀).FG ∧
      Submodule.span K (H₀ : Set HK) = ⊤ ∧
      (∀ x ∈ H₀, Bialgebra.counitAlgHom K HK x ∈ (algebraMap R K).range) ∧
      (∀ x ∈ H₀, HopfAlgebra.antipode K x ∈ H₀) ∧
      (∀ x ∈ H₀, Bialgebra.comulAlgHom K HK x ∈
        Submodule.span R {z : HK ⊗[K] HK | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K] b = z}) :=
  sorry

set_option linter.unusedSectionVars false in -- deliberate: `omit` of the unused section
-- instances measurably slows the consuming theorem's elaboration; keep the passing signature
/-- Coalgebra counit axiom (`lTensor` side) for a corestricted comultiplication,
stated against ABSTRACT corestricted maps `comul₀`/`counit₀`/`j2`: inline in the
structure literal of `exists_flat_hopf_form_of_free_hopf_order` the same proof
elaborates in a context where these are `let`-bound to large corestriction
composites (`codRestrict`/`ofInjective` towers), and the rewrite path of this
particular axiom forces those `let`s to unfold, making elaboration diverge
(hours; observed 2026-07-23/24). Against opaque hypotheses every defeq step
stays small. Consumed by `exists_flat_hopf_form_of_free_hopf_order` only. -/
theorem corestrict_lTensor_counit_comp_comul
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Algebra R HK] [IsScalarTower R K HK]
    (H₀ : Subalgebra R HK)
    (comul₀ : H₀ →ₗ[R] H₀ ⊗[R] H₀) (counit₀ : H₀ →ₗ[R] R)
    (j2 : H₀ ⊗[R] H₀ →ₗ[R] HK ⊗[K] HK)
    (hj2tmul : ∀ x y : H₀, j2 (x ⊗ₜ[R] y) = (x : HK) ⊗ₜ[K] (y : HK))
    (hj2comul₀ : ∀ x : H₀, j2 (comul₀ x) = Coalgebra.comul (R := K) (x : HK))
    (hcounit₀K : ∀ x : H₀,
      algebraMap R K (counit₀ x) = Coalgebra.counit (R := K) (x : HK)) :
    counit₀.lTensor H₀ ∘ₗ comul₀ = (TensorProduct.mk R H₀ R).flip 1 := by
  apply LinearMap.ext
  intro x
  apply (TensorProduct.rid R H₀).injective
  apply Subtype.coe_injective
  have haux : ∀ t : H₀ ⊗[R] H₀,
      (((TensorProduct.rid R H₀) ((counit₀.lTensor H₀) t)) : HK) =
      (TensorProduct.rid K HK)
        (((Coalgebra.counit (R := K)).lTensor HK) (j2 t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero]
    | add u v hu hv => simp only [map_add, AddMemClass.coe_add, hu, hv]
    | tmul a c =>
      rw [hj2tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, TensorProduct.rid_tmul]
      show ((counit₀ c • a : H₀) : HK) =
        Coalgebra.counit (R := K) (c : HK) • (a : HK)
      rw [← hcounit₀K c]
      show counit₀ c • (a : HK) = algebraMap R K (counit₀ c) • (a : HK)
      rw [algebraMap_smul]
  have h1 := haux (comul₀ x)
  rw [hj2comul₀ x] at h1
  have h2 := LinearMap.congr_fun
    (Coalgebra.lTensor_counit_comp_comul (R := K) (A := HK)) (x : HK)
  rw [LinearMap.comp_apply] at h2
  rw [h2] at h1
  show (((TensorProduct.rid R H₀) ((counit₀.lTensor H₀) (comul₀ x))) : HK) =
    (((TensorProduct.rid R H₀) (((TensorProduct.mk R H₀ R).flip 1) x)) : HK)
  rw [h1]
  show (TensorProduct.rid K HK) ((x : HK) ⊗ₜ[K] (1 : K)) =
    (((TensorProduct.rid R H₀) (x ⊗ₜ[R] (1 : R))) : HK)
  rw [TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul]
  show (x : HK) = (((1 : R) • x : H₀) : HK)
  rw [one_smul]

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- **The Hopf corestriction core** (PROVEN 2026-07-24; the deepest layer of the
curve-free structure half of the Katz–Mazur decomposition — pure
transport-of-structure over the DVR `R`): a FREE finite Hopf order whose
base-change map is bijective is a flat Hopf form. Given that the base-change
algebra map `K ⊗[R] H₀ → HK`, `k ⊗ h ↦ k • h` (`AlgHom.liftEquiv` applied to
the inclusion), is bijective, an `R`-basis of `H₀` is a `K`-basis of `HK`, so
the induced maps `H₀ ⊗[R] H₀ → HK ⊗[K] HK` and the triple-tensor analogue are
injective with image exactly the `R`-span of the pure tensors of `H₀`
(expand both factors in the basis with `R`-coefficients); the three closure
hypotheses then corestrict the comultiplication, the counit (through
`R ≃ (algebraMap R K).range`) and the antipode to `H₀`; every coalgebra,
bialgebra and Hopf axiom of the corestricted structure holds because it holds
in `HK` and the comparison maps are injective; flatness is freeness; and the
base-change equivalence is a bialgebra equivalence because comultiplication
on `K ⊗[R] H₀` is the base change of the corestricted comultiplication, which
agrees with the comultiplication of `HK` through the tensor-square comparison
map by construction. -/
theorem exists_flat_hopf_form_of_free_hopf_order
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Algebra R HK] [IsScalarTower R K HK]
    (H₀ : Subalgebra R HK)
    [Module.Finite R H₀] [Module.Free R H₀]
    (hbij : Function.Bijective (AlgHom.liftEquiv R K H₀ HK H₀.val))
    (hcounit : ∀ x ∈ H₀, Bialgebra.counitAlgHom K HK x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode K x ∈ H₀)
    (hcomul : ∀ x ∈ H₀, Bialgebra.comulAlgHom K HK x ∈
      Submodule.span R {z : HK ⊗[K] HK | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K] b = z}) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) := by
  classical
  -- the base-change equivalence of algebras
  let μe : (K ⊗[R] H₀) ≃ₐ[K] HK :=
    AlgEquiv.ofBijective (AlgHom.liftEquiv R K H₀ HK H₀.val) hbij
  -- the tensor-square comparison map into the `K`-side tensor square
  let j2 : H₀ ⊗[R] H₀ →ₗ[R] HK ⊗[K] HK :=
    TensorProduct.lift (LinearMap.mk₂ R (fun x y => (x : HK) ⊗ₜ[K] (y : HK))
      (fun x x' y => by simp [TensorProduct.add_tmul])
      (fun r x y => by simp [TensorProduct.smul_tmul'])
      (fun x y y' => by simp [TensorProduct.tmul_add])
      (fun r x y => by simp [TensorProduct.tmul_smul]))
  have hj2tmul : ∀ x y : H₀, j2 (x ⊗ₜ[R] y) = (x : HK) ⊗ₜ[K] (y : HK) :=
    fun _ _ => rfl
  -- the `R`-span of pure tensors of `H₀` is the range of `j2`
  have hj2range : Submodule.span R
      {z : HK ⊗[K] HK | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K] b = z} ≤
      LinearMap.range j2 := by
    rw [Submodule.span_le]
    rintro z ⟨a, ha, b', hb', rfl⟩
    exact ⟨(⟨a, ha⟩ : H₀) ⊗ₜ[R] (⟨b', hb'⟩ : H₀), rfl⟩
  -- an `R`-basis of `H₀` maps to a `K`-basis of `HK` under the inclusion
  let b := Module.Free.chooseBasis R H₀
  let bK := (b.baseChange K).map μe.toLinearEquiv
  have hbK : ∀ i, bK i = (b i : HK) := by
    intro i
    show μe ((b.baseChange K) i) = (b i : HK)
    rw [Module.Basis.baseChange_apply]
    show AlgHom.liftEquiv R K H₀ HK H₀.val ((1 : K) ⊗ₜ[R] b i) = (b i : HK)
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hj2inj : Function.Injective j2 := by
    -- the image of the tensor-square basis is `K`-linearly independent
    have hli2 : LinearIndependent K fun p : _ × _ => j2 ((b.tensorProduct b) p) := by
      have hEq : (fun p => j2 ((b.tensorProduct b) p)) =
          fun p => (bK.tensorProduct bK) p := by
        funext p
        rw [Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply']
        show (b p.1 : HK) ⊗ₜ[K] (b p.2 : HK) = bK p.1 ⊗ₜ[K] bK p.2
        rw [hbK, hbK]
      rw [hEq]
      exact (bK.tensorProduct bK).linearIndependent
    -- a map sending a basis to independent vectors is injective
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : ∑ p, algebraMap R K ((b.tensorProduct b).repr t p) •
        j2 ((b.tensorProduct b) p) = 0 := by
      have h1 : ∑ p, (b.tensorProduct b).repr t p • j2 ((b.tensorProduct b) p) =
          j2 t := by
        calc ∑ p, (b.tensorProduct b).repr t p • j2 ((b.tensorProduct b) p)
            = j2 (∑ p, (b.tensorProduct b).repr t p • (b.tensorProduct b) p) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun p _ => (j2.map_smul _ _).symm
          _ = j2 t := by rw [Module.Basis.sum_repr]
      calc ∑ p, algebraMap R K ((b.tensorProduct b).repr t p) •
          j2 ((b.tensorProduct b) p)
          = ∑ p, (b.tensorProduct b).repr t p • j2 ((b.tensorProduct b) p) :=
            Finset.sum_congr rfl fun p _ => by rw [algebraMap_smul]
        _ = j2 t := h1
        _ = 0 := ht
    have h2 := Fintype.linearIndependent_iff.mp hli2 _ h0
    have h3 : ∀ p, (b.tensorProduct b).repr t p = 0 := fun p =>
      (injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) _ (h2 p)
    rw [← Module.Basis.sum_repr (b.tensorProduct b) t]
    simp [h3]
  -- comultiplication corestricts to `H₀` through `j2`
  let e2 : (H₀ ⊗[R] H₀) ≃ₗ[R] LinearMap.range j2 := LinearEquiv.ofInjective j2 hj2inj
  have hmem2 : ∀ x : H₀, ((Coalgebra.comul (R := K)).restrictScalars R ∘ₗ
      H₀.val.toLinearMap) x ∈ LinearMap.range j2 :=
    fun x => hj2range (by simpa using hcomul x x.2)
  let comul₀ : H₀ →ₗ[R] H₀ ⊗[R] H₀ :=
    e2.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range j2)
      ((Coalgebra.comul (R := K)).restrictScalars R ∘ₗ H₀.val.toLinearMap) hmem2
  -- the defining identity of the corestricted comultiplication
  have hj2e2 : ∀ y : LinearMap.range j2, j2 (e2.symm y) = (y : HK ⊗[K] HK) := by
    intro y
    have h1 : e2 (e2.symm y) = y := e2.apply_symm_apply y
    have h2 : (e2 (e2.symm y) : HK ⊗[K] HK) = j2 (e2.symm y) := rfl
    rw [← h2, h1]
  have hj2comul₀ : ∀ x : H₀, j2 (comul₀ x) = Coalgebra.comul (R := K) (x : HK) := by
    intro x
    show j2 (e2.symm (LinearMap.codRestrict (LinearMap.range j2)
      ((Coalgebra.comul (R := K)).restrictScalars R ∘ₗ H₀.val.toLinearMap) hmem2 x)) =
      Coalgebra.comul (R := K) (x : HK)
    rw [hj2e2]
    rfl
  -- the counit corestricts to `R`
  have hmemR : ∀ x : H₀, ((Coalgebra.counit (R := K)).restrictScalars R ∘ₗ
      H₀.val.toLinearMap) x ∈ LinearMap.range (Algebra.linearMap R K) := by
    intro x
    obtain ⟨r, hr⟩ := hcounit x x.2
    exact ⟨r, by simpa using hr⟩
  let eR : R ≃ₗ[R] LinearMap.range (Algebra.linearMap R K) :=
    LinearEquiv.ofInjective (Algebra.linearMap R K) (IsFractionRing.injective R K)
  let counit₀ : H₀ →ₗ[R] R :=
    eR.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range (Algebra.linearMap R K))
      ((Coalgebra.counit (R := K)).restrictScalars R ∘ₗ H₀.val.toLinearMap) hmemR
  -- the defining identity of the corestricted counit
  have hjReR : ∀ y : LinearMap.range (Algebra.linearMap R K),
      algebraMap R K (eR.symm y) = (y : K) := by
    intro y
    have h1 : eR (eR.symm y) = y := eR.apply_symm_apply y
    have h2 : (eR (eR.symm y) : K) = algebraMap R K (eR.symm y) := rfl
    rw [← h2, h1]
  have hcounit₀K : ∀ x : H₀,
      algebraMap R K (counit₀ x) = Coalgebra.counit (R := K) (x : HK) := by
    intro x
    show algebraMap R K (eR.symm (LinearMap.codRestrict
      (LinearMap.range (Algebra.linearMap R K))
      ((Coalgebra.counit (R := K)).restrictScalars R ∘ₗ H₀.val.toLinearMap) hmemR x)) =
      Coalgebra.counit (R := K) (x : HK)
    rw [hjReR]
    rfl
  -- the antipode corestricts to `H₀`
  let antipode₀ : H₀ →ₗ[R] H₀ :=
    LinearMap.codRestrict (Subalgebra.toSubmodule H₀)
      ((HopfAlgebra.antipode K : HK →ₗ[K] HK).restrictScalars R ∘ₗ H₀.val.toLinearMap)
      (fun x => hantipode x x.2)
  have hantval : ∀ x : H₀, ((antipode₀ x : H₀) : HK) = HopfAlgebra.antipode K (x : HK) :=
    fun _ => rfl
  -- the tensor-cube comparison map, injective by the same basis argument
  let j3 : H₀ ⊗[R] (H₀ ⊗[R] H₀) →ₗ[R] HK ⊗[K] (HK ⊗[K] HK) :=
    TensorProduct.lift (LinearMap.mk₂ R (fun x t => (x : HK) ⊗ₜ[K] j2 t)
      (fun x x' t => by simp [TensorProduct.add_tmul])
      (fun r x t => by simp [TensorProduct.smul_tmul'])
      (fun x t t' => by simp [TensorProduct.tmul_add])
      (fun r x t => by simp [TensorProduct.tmul_smul]))
  have hj3inj : Function.Injective j3 := by
    have hli3 : LinearIndependent K
        fun p : _ × (_ × _) => j3 ((b.tensorProduct (b.tensorProduct b)) p) := by
      have hEq : (fun p => j3 ((b.tensorProduct (b.tensorProduct b)) p)) =
          fun p => (bK.tensorProduct (bK.tensorProduct bK)) p := by
        funext p
        rw [Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply',
          Module.Basis.tensorProduct_apply', Module.Basis.tensorProduct_apply']
        show (b p.1 : HK) ⊗ₜ[K] j2 (b p.2.1 ⊗ₜ[R] b p.2.2) =
          bK p.1 ⊗ₜ[K] (bK p.2.1 ⊗ₜ[K] bK p.2.2)
        rw [hbK, hbK, hbK]
        rfl
      rw [hEq]
      exact (bK.tensorProduct (bK.tensorProduct bK)).linearIndependent
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : ∑ p, algebraMap R K ((b.tensorProduct (b.tensorProduct b)).repr t p) •
        j3 ((b.tensorProduct (b.tensorProduct b)) p) = 0 := by
      have h1 : ∑ p, (b.tensorProduct (b.tensorProduct b)).repr t p •
          j3 ((b.tensorProduct (b.tensorProduct b)) p) = j3 t := by
        calc ∑ p, (b.tensorProduct (b.tensorProduct b)).repr t p •
            j3 ((b.tensorProduct (b.tensorProduct b)) p)
            = j3 (∑ p, (b.tensorProduct (b.tensorProduct b)).repr t p •
                (b.tensorProduct (b.tensorProduct b)) p) := by
              rw [map_sum]
              exact Finset.sum_congr rfl fun p _ => (j3.map_smul _ _).symm
          _ = j3 t := by rw [Module.Basis.sum_repr]
      calc ∑ p, algebraMap R K ((b.tensorProduct (b.tensorProduct b)).repr t p) •
          j3 ((b.tensorProduct (b.tensorProduct b)) p)
          = ∑ p, (b.tensorProduct (b.tensorProduct b)).repr t p •
              j3 ((b.tensorProduct (b.tensorProduct b)) p) :=
            Finset.sum_congr rfl fun p _ => by rw [algebraMap_smul]
        _ = j3 t := h1
        _ = 0 := ht
    have h2 := Fintype.linearIndependent_iff.mp hli3 _ h0
    have h3 : ∀ p, (b.tensorProduct (b.tensorProduct b)).repr t p = 0 := fun p =>
      (injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) _ (h2 p)
    rw [← Module.Basis.sum_repr (b.tensorProduct (b.tensorProduct b)) t]
    simp [h3]
  -- `j2` is multiplicative
  have hj2mul : ∀ s t : H₀ ⊗[R] H₀, j2 (s * t) = j2 s * j2 t := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp [add_mul, map_add, hu, hv]
    | tmul x y =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp [mul_add, map_add, hu, hv]
      | tmul x' y' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        show ((x * x' : H₀) : HK) ⊗ₜ[K] ((y * y' : H₀) : HK) =
          ((x : HK) ⊗ₜ[K] (y : HK)) * ((x' : HK) ⊗ₜ[K] (y' : HK))
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
  -- the corestricted structure is a Hopf algebra: every axiom transfers along
  -- the injective comparison maps
  letI instCo : Coalgebra R H₀ :=
    { comul := comul₀
      counit := counit₀
      coassoc := by
        apply LinearMap.ext
        intro x
        apply hj3inj
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        have hL : ∀ t : H₀ ⊗[R] H₀,
            j3 ((TensorProduct.assoc R H₀ H₀ H₀) ((comul₀.rTensor H₀) t)) =
            (TensorProduct.assoc K HK HK HK)
              (((Coalgebra.comul (R := K)).rTensor HK) (j2 t)) := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp only [map_zero]
          | add u v hu hv => simp only [map_add, hu, hv]
          | tmul y z =>
            rw [LinearMap.rTensor_tmul]
            show j3 ((TensorProduct.assoc R H₀ H₀ H₀) (comul₀ y ⊗ₜ[R] z)) =
              (TensorProduct.assoc K HK HK HK)
                (((Coalgebra.comul (R := K)).rTensor HK) ((y : HK) ⊗ₜ[K] (z : HK)))
            rw [LinearMap.rTensor_tmul, ← hj2comul₀ y]
            generalize comul₀ y = s
            induction s using TensorProduct.induction_on with
            | zero => simp
            | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
            | tmul a c =>
              rw [TensorProduct.assoc_tmul]
              show (a : HK) ⊗ₜ[K] j2 (c ⊗ₜ[R] z) =
                (TensorProduct.assoc K HK HK HK)
                  (((a : HK) ⊗ₜ[K] (c : HK)) ⊗ₜ[K] (z : HK))
              rw [TensorProduct.assoc_tmul]
              rfl
        have hRt : ∀ t : H₀ ⊗[R] H₀,
            j3 ((comul₀.lTensor H₀) t) =
            ((Coalgebra.comul (R := K)).lTensor HK) (j2 t) := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp only [map_zero]
          | add u v hu hv => simp only [map_add, hu, hv]
          | tmul y z =>
            rw [LinearMap.lTensor_tmul]
            show (y : HK) ⊗ₜ[K] j2 (comul₀ z) =
              ((Coalgebra.comul (R := K)).lTensor HK) ((y : HK) ⊗ₜ[K] (z : HK))
            rw [LinearMap.lTensor_tmul, hj2comul₀ z]
        rw [hL (comul₀ x), hRt (comul₀ x), hj2comul₀ x]
        exact Coalgebra.coassoc_apply (x : HK)
      rTensor_counit_comp_comul := by
        apply LinearMap.ext
        intro x
        apply (TensorProduct.lid R H₀).injective
        apply Subtype.coe_injective
        have haux : ∀ t : H₀ ⊗[R] H₀,
            (((TensorProduct.lid R H₀) ((counit₀.rTensor H₀) t)) : HK) =
            (TensorProduct.lid K HK)
              (((Coalgebra.counit (R := K)).rTensor HK) (j2 t)) := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp only [map_zero, ZeroMemClass.coe_zero]
          | add u v hu hv =>
            simp only [map_add, AddMemClass.coe_add, hu, hv]
          | tmul a c =>
            rw [LinearMap.rTensor_tmul]
            show (((TensorProduct.lid R H₀) (counit₀ a ⊗ₜ[R] c)) : HK) =
              (TensorProduct.lid K HK) (((Coalgebra.counit (R := K)).rTensor HK)
                ((a : HK) ⊗ₜ[K] (c : HK)))
            rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul]
            show ((counit₀ a • c : H₀) : HK) =
              Coalgebra.counit (R := K) (a : HK) • (c : HK)
            rw [← hcounit₀K a]
            show counit₀ a • (c : HK) = algebraMap R K (counit₀ a) • (c : HK)
            rw [algebraMap_smul]
        have h1 := haux (comul₀ x)
        rw [hj2comul₀ x] at h1
        have h2 := LinearMap.congr_fun
          (Coalgebra.rTensor_counit_comp_comul (R := K) (A := HK)) (x : HK)
        rw [LinearMap.comp_apply] at h2
        rw [h2] at h1
        show (((TensorProduct.lid R H₀) ((counit₀.rTensor H₀) (comul₀ x))) : HK) =
          (((TensorProduct.lid R H₀) ((TensorProduct.mk R R H₀) 1 x)) : HK)
        rw [h1]
        show (TensorProduct.lid K HK) ((1 : K) ⊗ₜ[K] (x : HK)) =
          (((TensorProduct.lid R H₀) ((1 : R) ⊗ₜ[R] x)) : HK)
        rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul]
        show (x : HK) = (((1 : R) • x : H₀) : HK)
        rw [one_smul]
      lTensor_counit_comp_comul :=
        corestrict_lTensor_counit_comp_comul R K HK H₀ comul₀ counit₀ j2
          hj2tmul hj2comul₀ hcounit₀K }
  letI instBi : Bialgebra R H₀ := Bialgebra.mk' R H₀
    (by
      apply IsFractionRing.injective R K
      show algebraMap R K (counit₀ (1 : H₀)) = algebraMap R K 1
      rw [hcounit₀K, OneMemClass.coe_one, Bialgebra.counit_one, map_one])
    (fun {a c} => by
      apply IsFractionRing.injective R K
      show algebraMap R K (counit₀ (a * c)) = algebraMap R K (counit₀ a * counit₀ c)
      rw [hcounit₀K]
      calc Coalgebra.counit (R := K) ((a * c : H₀) : HK)
          = Coalgebra.counit (R := K) ((a : HK) * (c : HK)) := by
            rw [MulMemClass.coe_mul]
        _ = Coalgebra.counit (R := K) (a : HK) * Coalgebra.counit (R := K) (c : HK) :=
            Bialgebra.counit_mul _ _
        _ = algebraMap R K (counit₀ a) * algebraMap R K (counit₀ c) := by
            rw [hcounit₀K, hcounit₀K]
        _ = algebraMap R K (counit₀ a * counit₀ c) := (map_mul _ _ _).symm)
    (by
      apply hj2inj
      show j2 (comul₀ (1 : H₀)) = j2 (1 : H₀ ⊗[R] H₀)
      rw [hj2comul₀]
      show Coalgebra.comul (R := K) ((1 : H₀) : HK) = j2 (1 : H₀ ⊗[R] H₀)
      rw [OneMemClass.coe_one, Bialgebra.comul_one,
        show (1 : H₀ ⊗[R] H₀) = (1 : H₀) ⊗ₜ[R] (1 : H₀) from
          Algebra.TensorProduct.one_def]
      show (1 : HK ⊗[K] HK) = ((1 : H₀) : HK) ⊗ₜ[K] ((1 : H₀) : HK)
      rw [OneMemClass.coe_one]
      exact Algebra.TensorProduct.one_def)
    (fun {a c} => by
      apply hj2inj
      show j2 (comul₀ (a * c)) = j2 (comul₀ a * comul₀ c)
      rw [hj2mul, hj2comul₀ (a * c), hj2comul₀ a, hj2comul₀ c]
      show Coalgebra.comul (R := K) ((a * c : H₀) : HK) = _
      rw [MulMemClass.coe_mul, Bialgebra.comul_mul])
  letI instHopf : HopfAlgebra R H₀ :=
    { antipode := antipode₀
      mul_antipode_rTensor_comul := by
        apply LinearMap.ext
        intro x
        apply Subtype.coe_injective
        have haux : ∀ t : H₀ ⊗[R] H₀,
            ((LinearMap.mul' R H₀ ((antipode₀.rTensor H₀) t)) : HK) =
            LinearMap.mul' K HK
              (((HopfAlgebra.antipode K : HK →ₗ[K] HK).rTensor HK) (j2 t)) := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp only [map_zero, ZeroMemClass.coe_zero]
          | add u v hu hv =>
            simp only [map_add, AddMemClass.coe_add, hu, hv]
          | tmul a c =>
            rw [LinearMap.rTensor_tmul]
            show ((LinearMap.mul' R H₀ (antipode₀ a ⊗ₜ[R] c)) : HK) =
              LinearMap.mul' K HK
                (((HopfAlgebra.antipode K : HK →ₗ[K] HK).rTensor HK)
                  ((a : HK) ⊗ₜ[K] (c : HK)))
            rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply]
            show ((antipode₀ a * c : H₀) : HK) =
              HopfAlgebra.antipode K (a : HK) * (c : HK)
            rw [MulMemClass.coe_mul, hantval]
        simp only [LinearMap.comp_apply]
        show ((LinearMap.mul' R H₀ ((antipode₀.rTensor H₀) (comul₀ x))) : HK) =
          ((Algebra.linearMap R H₀ (counit₀ x) : H₀) : HK)
        rw [haux (comul₀ x), hj2comul₀ x,
          HopfAlgebra.mul_antipode_rTensor_comul_apply, ← hcounit₀K x,
          ← IsScalarTower.algebraMap_apply]
        rfl
      mul_antipode_lTensor_comul := by
        apply LinearMap.ext
        intro x
        apply Subtype.coe_injective
        have haux : ∀ t : H₀ ⊗[R] H₀,
            ((LinearMap.mul' R H₀ ((antipode₀.lTensor H₀) t)) : HK) =
            LinearMap.mul' K HK
              (((HopfAlgebra.antipode K : HK →ₗ[K] HK).lTensor HK) (j2 t)) := by
          intro t
          induction t using TensorProduct.induction_on with
          | zero => simp only [map_zero, ZeroMemClass.coe_zero]
          | add u v hu hv =>
            simp only [map_add, AddMemClass.coe_add, hu, hv]
          | tmul a c =>
            rw [LinearMap.lTensor_tmul]
            show ((LinearMap.mul' R H₀ (a ⊗ₜ[R] antipode₀ c)) : HK) =
              LinearMap.mul' K HK
                (((HopfAlgebra.antipode K : HK →ₗ[K] HK).lTensor HK)
                  ((a : HK) ⊗ₜ[K] (c : HK)))
            rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, LinearMap.mul'_apply]
            show ((a * antipode₀ c : H₀) : HK) =
              (a : HK) * HopfAlgebra.antipode K (c : HK)
            rw [MulMemClass.coe_mul, hantval]
        simp only [LinearMap.comp_apply]
        show ((LinearMap.mul' R H₀ ((antipode₀.lTensor H₀) (comul₀ x))) : HK) =
          ((Algebra.linearMap R H₀ (counit₀ x) : H₀) : HK)
        rw [haux (comul₀ x), hj2comul₀ x,
          HopfAlgebra.mul_antipode_lTensor_comul_apply, ← hcounit₀K x,
          ← IsScalarTower.algebraMap_apply]
        rfl }
  -- the base-change equivalence respects the corestricted Hopf structure
  have hμ1 : ∀ y : H₀, μe ((1 : K) ⊗ₜ[R] y) = (y : HK) := by
    intro y
    show AlgHom.liftEquiv R K H₀ HK H₀.val ((1 : K) ⊗ₜ[R] y) = (y : HK)
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hO1 : (Bialgebra.counitAlgHom K HK).comp (μe : (K ⊗[R] H₀) →ₐ[K] HK) =
      Bialgebra.counitAlgHom K (K ⊗[R] H₀) := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    show Bialgebra.counitAlgHom K HK (μe ((1 : K) ⊗ₜ[R] x)) =
      Bialgebra.counitAlgHom K (K ⊗[R] H₀) ((1 : K) ⊗ₜ[R] x)
    rw [hμ1 x]
    show Coalgebra.counit (R := K) (x : HK) =
      Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] x : K ⊗[R] H₀)
    rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
      mul_one]
    exact (hcounit₀K x).symm
  have hO2 : (Algebra.TensorProduct.map (μe : (K ⊗[R] H₀) →ₐ[K] HK)
      (μe : (K ⊗[R] H₀) →ₐ[K] HK)).comp (Bialgebra.comulAlgHom K (K ⊗[R] H₀)) =
      (Bialgebra.comulAlgHom K HK).comp (μe : (K ⊗[R] H₀) →ₐ[K] HK) := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    show (Algebra.TensorProduct.map (μe : (K ⊗[R] H₀) →ₐ[K] HK)
        (μe : (K ⊗[R] H₀) →ₐ[K] HK))
        (Bialgebra.comulAlgHom K (K ⊗[R] H₀) ((1 : K) ⊗ₜ[R] x)) =
      Bialgebra.comulAlgHom K HK (μe ((1 : K) ⊗ₜ[R] x))
    rw [hμ1 x]
    show (Algebra.TensorProduct.map (μe : (K ⊗[R] H₀) →ₐ[K] HK)
        (μe : (K ⊗[R] H₀) →ₐ[K] HK))
        (Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[R] x : K ⊗[R] H₀)) =
      Coalgebra.comul (R := K) (x : HK)
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    -- the composite carrying the base-changed comultiplication into `HK ⊗ HK`
    -- agrees with `j2`, checked on pure tensors
    have hLext : (LinearMap.restrictScalars R
          (Algebra.TensorProduct.map (μe : (K ⊗[R] H₀) →ₐ[K] HK)
            (μe : (K ⊗[R] H₀) →ₐ[K] HK)).toLinearMap ∘ₗ
        LinearMap.restrictScalars R
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
            R K R K K K H₀ H₀).toLinearMap ∘ₗ
        TensorProduct.mk R (K ⊗[K] K) (H₀ ⊗[R] H₀)
          ((1 : K) ⊗ₜ[K] (1 : K))) = j2 := by
      apply TensorProduct.ext'
      intro a c
      show (Algebra.TensorProduct.map (μe : (K ⊗[R] H₀) →ₐ[K] HK)
          (μe : (K ⊗[R] H₀) →ₐ[K] HK))
          ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R K R K K K H₀ H₀)
            (((1 : K) ⊗ₜ[K] (1 : K)) ⊗ₜ[R] (a ⊗ₜ[R] c))) = j2 (a ⊗ₜ[R] c)
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        Algebra.TensorProduct.map_tmul]
      show (μe ((1 : K) ⊗ₜ[R] a) : HK) ⊗ₜ[K] (μe ((1 : K) ⊗ₜ[R] c) : HK) =
        j2 (a ⊗ₜ[R] c)
      rw [hμ1 a, hμ1 c]
      rfl
    have h5 := LinearMap.congr_fun hLext (comul₀ x)
    rw [hj2comul₀ x] at h5
    exact h5
  exact ⟨H₀, inferInstance, instHopf, inferInstance, inferInstance,
    ⟨BialgEquiv.ofAlgEquiv μe hO1 hO2⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Hopf orders are flat Hopf forms** (DECOMPOSED 2026-07-23 into the
corestriction core `exists_flat_hopf_form_of_free_hopf_order`; the reduction
below is PROVEN — the curve-free STRUCTURE half of the decomposed Katz–Mazur
existence leaf `exists_torsion_flat_model_of_good_reduction_prime_pow`,
commutative algebra over the DVR `R`, no Galois theory and no elliptic
curve): a finitely generated `R`-subalgebra `H₀` of a Hopf `K`-algebra `HK`,
finite as a `K`-module, which spans `HK` over `K` and is closed under counit
(into `R`), antipode, and comultiplication (into the `R`-span of its pure
tensors), is a finite flat Hopf `R`-form of `HK`. The proven reduction: `H₀`
is torsion-free (it sits inside a `K`-vector space and `R` injects into `K`)
and finitely generated over the DVR `R`, hence finite FREE; an `R`-basis of
`H₀` is a `K`-basis of `HK` — it spans by the span hypothesis, and it is
`K`-independent because a `K`-relation clears denominators
(`IsLocalization.exist_integer_multiples`) to an `R`-relation inside `H₀` —
so the base-change algebra map `K ⊗[R] H₀ → HK` is bijective (it matches the
basis equivalence), which is what the corestriction core consumes. The `μ_p`
counterexample (normalization over `ℤ_p` not a Hopf order) does not
contradict this statement: there the COMULTIPLICATION-closure hypothesis
fails for the normalization. -/
theorem exists_flat_hopf_form_of_hopf_order
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra R HK] [IsScalarTower R K HK]
    (H₀ : Subalgebra R HK)
    (hfg : (Subalgebra.toSubmodule H₀).FG)
    (hspan : Submodule.span K (H₀ : Set HK) = ⊤)
    (hcounit : ∀ x ∈ H₀, Bialgebra.counitAlgHom K HK x ∈ (algebraMap R K).range)
    (hantipode : ∀ x ∈ H₀, HopfAlgebra.antipode K x ∈ H₀)
    (hcomul : ∀ x ∈ H₀, Bialgebra.comulAlgHom K HK x ∈
      Submodule.span R {z : HK ⊗[K] HK | ∃ a ∈ H₀, ∃ b ∈ H₀, a ⊗ₜ[K] b = z}) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) := by
  classical
  -- `H₀` is a finite `R`-module
  haveI hfin : Module.Finite R H₀ := Module.Finite.iff_fg.mpr hfg
  -- `HK` is torsion-free over `K` (a vector space), hence `H₀` over `R`
  haveI : Module.IsTorsionFree K HK :=
    ⟨fun k hk x y hxy => by
      have hk0 : k ≠ 0 := isRegular_iff_ne_zero.mp hk
      have h : k • x = k • y := hxy
      calc x = k⁻¹ • (k • x) := by rw [smul_smul, inv_mul_cancel₀ hk0, one_smul]
        _ = k⁻¹ • (k • y) := by rw [h]
        _ = y := by rw [smul_smul, inv_mul_cancel₀ hk0, one_smul]⟩
  haveI : Module.IsTorsionFree R H₀ :=
    ⟨fun r hr x y hxy => by
      have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
      have hrK : algebraMap R K r ≠ 0 :=
        fun h0 => hr0 ((injective_iff_map_eq_zero _).mp
          (IsFractionRing.injective R K) r h0)
      have hval : algebraMap R K r • (x : HK) = algebraMap R K r • (y : HK) := by
        rw [algebraMap_smul, algebraMap_smul]
        exact congrArg Subtype.val hxy
      exact Subtype.ext ((IsRegular.of_ne_zero hrK).isSMulRegular.eq_iff.mp hval)⟩
  haveI hfree : Module.Free R H₀ := Module.free_of_finite_type_torsion_free'
  -- an `R`-basis of `H₀`
  let b := Module.Free.chooseBasis R H₀
  -- its image in `HK` is `K`-linearly independent: clear denominators
  have hli : LinearIndependent K (fun i => (b i : HK)) := by
    rw [linearIndependent_iff']
    intro s c hc
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) s c
    have hnum : ∀ i : Module.Free.ChooseBasisIndex R H₀,
        ∃ r : R, i ∈ s → algebraMap R K r = (d : R) • c i := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨r, hr⟩ := hd i hi
        exact ⟨r, fun _ => hr⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose r hr using hnum
    have hrel : ∑ i ∈ s, r i • b i = (0 : H₀) := by
      apply Subtype.ext
      have h1 : ((∑ i ∈ s, r i • b i : H₀) : HK) = ∑ i ∈ s, r i • (b i : HK) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun i _ => rfl
      have h2 : ∑ i ∈ s, r i • (b i : HK) = (d : R) • ∑ i ∈ s, c i • (b i : HK) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← algebraMap_smul K (r i) ((b i : HK)), hr i hi, smul_assoc]
      rw [h1, h2, hc, smul_zero]
      rfl
    intro i hi
    have hri := linearIndependent_iff'.mp b.linearIndependent s r hrel i hi
    have hzero : (d : R) • c i = 0 := by rw [← hr i hi, hri, map_zero]
    have hd0 : algebraMap R K (d : R) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    rw [Algebra.smul_def] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hd0
  -- ... and spans `HK` over `K`
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : HK)) := by
    rw [← hspan]
    refine Submodule.span_le.mpr fun x hx => ?_
    have hx' : (⟨x, hx⟩ : H₀) ∈ Submodule.span R (Set.range b) := by
      rw [b.span_eq]
      trivial
    have h2 : x ∈ Submodule.map (Subalgebra.toSubmodule H₀).subtype
        (Submodule.span R (Set.range b)) :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rw [Submodule.map_span] at h2
    have h3 : (Subalgebra.toSubmodule H₀).subtype '' Set.range b =
        Set.range fun i => (b i : HK) := by
      rw [← Set.range_comp]
      rfl
    rw [h3] at h2
    exact Submodule.span_subset_span R K _ h2
  -- hence the base-change map matches a basis equivalence, so it is bijective
  let bK := Module.Basis.mk hli hsp
  have heq : (AlgHom.liftEquiv R K H₀ HK H₀.val).toLinearMap =
      ↑((b.baseChange K).equiv bK (Equiv.refl _)) := by
    refine (b.baseChange K).ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply,
      Module.Basis.baseChange_apply]
    show AlgHom.liftEquiv R K H₀ HK H₀.val ((1 : K) ⊗ₜ[R] b i) = bK i
    rw [AlgHom.liftEquiv_tmul, one_smul, Module.Basis.mk_apply]
    rfl
  have hbij : Function.Bijective (AlgHom.liftEquiv R K H₀ HK H₀.val) := by
    have hcoe : ⇑(AlgHom.liftEquiv R K H₀ HK H₀.val) =
        ⇑((b.baseChange K).equiv bK (Equiv.refl _)) := by
      have h1 := congrArg (fun f : K ⊗[R] H₀ →ₗ[K] HK => ⇑f) heq
      simpa using h1
    rw [hcoe]
    exact ((b.baseChange K).equiv bK (Equiv.refl _)).bijective
  exact exists_flat_hopf_form_of_free_hopf_order R K HK H₀ hbij hcounit
    hantipode hcomul

/-- **The Katz–Mazur flat model, mixed characteristic** (DECOMPOSED 2026-07-23
into the curve leaf `exists_hopf_order_of_good_reduction` — the Katz–Mazur
2.3.1 kernel model presented as a Hopf ORDER, a set-level statement inside the
étale generic-fibre algebra, carrying the whole construction roadmap in its
docstring — and the curve-free structure leaf
`exists_flat_hopf_form_of_hopf_order` — Hopf orders over a DVR are flat Hopf
forms; the assembly below is proven, through the proven transports
`exists_torsion_etale_package_over_fractionField` and
`torsion_flat_package_of_flat_hopf_form`): when the prime `p` is not
invertible in `R` but nonzero in `K`, SOME finite flat Hopf `R`-algebra has
étale generic fibre whose `Kˢᵉᵖ`-points are, `Gal(Kˢᵉᵖ/K)`-equivariantly, the
`p ^ k`-torsion of `E(Kˢᵉᵖ)`. Routes examined and rejected for the order:
normalization (the `μ_p` special fibre is not a group scheme),
connected-étale splitting and `k`-dévissage (see the git history of this
docstring). For the Frey curve application (`R = ℤ_(p)`, `K = ℚ`, `k = 1`)
the object is the kernel of `[p]` on the good-reduction Weierstrass model. -/
theorem WeierstrassCurve.exists_torsion_flat_model_of_good_reduction_prime_pow
    (p : ℕ) (_hp : p.Prime) (_hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0)
    (hpK : (p : K) ≠ 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (g : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (g (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (g (Additive.ofMul (WithConv.toConv φ))) := by
  classical
  -- `p ^ k` is nonzero in `R`, so the étale `K`-package of the torsion applies
  have hpR : ((p ^ k : ℕ) : R) ≠ 0 := by
    intro h0
    apply hpK
    have h1 : ((p ^ k : ℕ) : K) = 0 := by
      rw [← map_natCast (algebraMap R K), h0, map_zero]
    push_cast at h1
    exact (pow_eq_zero_iff hk).mp h1
  have hmK : ((p ^ k : ℕ) : K) ≠ 0 := by
    push_cast
    exact pow_ne_zero k hpK
  obtain ⟨HK, iCR, iHopf, iFin, iEt, f, hf⟩ :=
    WeierstrassCurve.exists_torsion_etale_package_over_fractionField R K E Ksep
      (p ^ k) hpR
  letI := iCR; letI := iHopf; letI := iFin; haveI := iEt
  -- give `HK` its `R`-algebra structure through `K`
  letI : Algebra R HK := ((algebraMap K HK).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K HK := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the Katz–Mazur Hopf order (the curve leaf)
  obtain ⟨H₀, hfg, hspan, hcounit, hantipode, hcomul⟩ :=
    WeierstrassCurve.exists_hopf_order_of_good_reduction R K E Ksep
      (p ^ k) hmK HK f hf
  -- the order is a flat Hopf form (the structure leaf)
  obtain ⟨H, jCR, jHopf, jFin, jFlat, ⟨e⟩⟩ :=
    exists_flat_hopf_form_of_hopf_order R K HK H₀ hfg hspan hcounit
      hantipode hcomul
  letI := jCR; letI := jHopf; letI := jFin; letI := jFlat
  -- transport the étale package along the form (proven plumbing)
  exact WeierstrassCurve.torsion_flat_package_of_flat_hopf_form R K E Ksep
    (p ^ k) HK f hf H e

/-- **The Katz–Mazur flat Hopf form, mixed characteristic** (DECOMPOSED
2026-07-23 into the existence leaf
`exists_torsion_flat_model_of_good_reduction_prime_pow` — the Katz–Mazur
2.3.1 kernel model with equivariant torsion points, see its docstring — and
the comparison leaf `exists_bialgEquiv_of_torsion_points_equiv` — Grothendieck
full faithfulness: the given `HK` and the model's generic fibre have
equivariantly isomorphic point groups, hence are Hopf-isomorphic; the assembly
below is proven): under the hypotheses of
`torsion_flat_prolong_of_good_reduction_prime_pow`, the finite étale Hopf
`K`-algebra `HK` of the `p ^ k`-torsion admits a finite flat Hopf `R`-form. -/
theorem WeierstrassCurve.exists_finite_flat_hopf_form_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0)
    (hpK : (p : K) ≠ 0)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) := by
  obtain ⟨H, iCR, iHopf, iFin, iFlat, iEt, g, hg⟩ :=
    WeierstrassCurve.exists_torsion_flat_model_of_good_reduction_prime_pow
      R K E Ksep p hp hpu k hk hpK
  letI := iCR
  letI := iHopf
  letI := iFin
  letI := iFlat
  haveI := iEt
  exact ⟨H, iCR, iHopf, iFin, iFlat,
    WeierstrassCurve.exists_bialgEquiv_of_torsion_points_equiv K E Ksep
      (p ^ k) (K ⊗[R] H) HK g hg f hf⟩

/-- **The Katz–Mazur flat prolongation, mixed characteristic** (DECOMPOSED
2026-07-22 into the flat Hopf-form leaf
`exists_finite_flat_hopf_form_of_good_reduction_prime_pow` — which carries the
whole Katz–Mazur 2.3.1 content, see its docstring — and the proven transport
`torsion_flat_package_of_flat_hopf_form`; the assembly below is proven): given
the finite étale Hopf `K`-algebra `HK` of the `p ^ k`-torsion (the shared
Galois-correspondence leaf `exists_torsion_etale_package_over_fractionField`),
when the prime `p` is *not* invertible in `R` but nonzero in `K` (so `p` is the
residue characteristic and `K` has characteristic `0` or prime-to-`p`; for the
Frey curve application `R = ℤ_(p)`, `K = ℚ`, `k = 1`), `HK` prolongs to a
finite FLAT — no longer étale — Hopf algebra over `R`. -/
theorem WeierstrassCurve.torsion_flat_prolong_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0)
    (hpK : (p : K) ≠ 0)
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
      AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ))
    (hf : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ)))) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (g : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (g (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (g (Additive.ofMul (WithConv.toConv φ))) := by
  obtain ⟨H, iCR, iHopf, iFin, iFlat, ⟨e⟩⟩ :=
    WeierstrassCurve.exists_finite_flat_hopf_form_of_good_reduction_prime_pow
      R K E Ksep p hp hpu k hk hpK HK f hf
  letI := iCR; letI := iHopf; letI := iFin; letI := iFlat
  exact WeierstrassCurve.torsion_flat_package_of_flat_hopf_form R K E Ksep
    (p ^ k) HK f hf H e

/-!
### The equal-characteristic branch was REFUTED and excised (2026-07-23)

An equal-characteristic branch (`(p : K) = 0`) used to live here, decomposed
through an equal-characteristic Néron–Ogg–Shafarevich chain
(`torsion_flat_of_good_reduction_prime_pow_of_eqChar` ←
`torsion_inertia_fixes_of_eqChar` ← `kernel_prime_pow_torsion_of_eqChar` ←
the sorried leaf `kernel_prime_torsion_of_eqChar`, plus the helpers
`kernel_nsmul_abscissa_notMem`, `baseChange_ordinate_mem_of_abscissa_mem` and
the Galois-correspondence sibling `exists_torsion_etale_package_of_eqChar`).
That chain rested on the claim that in equal characteristic `p` the kernel of
reduction of a good-reduction curve is `p`-torsion-free. **The claim is false**
— machine-verified counterexample (all three identities checked by `ring` over
any field of characteristic `2`): over `K = 𝔽₂((t))`, `R = 𝔽₂[[t]]`, the curve
`E : y² + t²xy + y = x³ + 1` has `Δ = t¹² + t⁶ + 1 ∈ Rˣ` (good reduction,
minimal model, supersingular residue curve `y² + y = x³ + 1`, ordinary generic
fibre), and `P = (t⁻², t⁻³ + 1) ∈ E(K)` satisfies the curve equation and
`y(P) = negY P`, i.e. `2 • P = 0`, `P ≠ 0` — a rational prime-order torsion
point in the kernel of reduction (`v(x) = -2 < 0`). The inertia statement
fails as well: over `K = 𝔽₃((t))` the curve `y² = x³ + t³x² + x` has
`Δ = 2 + t⁶ ∈ Rˣ`, `ψ₃ = t³X³ + 2` vanishes at `x₀ = t⁻¹`, and the 3-torsion
point above `x₀` has `y₀² = t⁻³ + t⁻¹ + t` of odd valuation, so `K(y₀)/K` is a
ramified (separable) quadratic extension and inertia sends `P ↦ -P ≠ P`.
This is the classical Igusa phenomenon: near a supersingular point of the
moduli the étale-quotient `p`-torsion sits inside the kernel of reduction and
its Galois module is genuinely ramified, good reduction notwithstanding — an
equal-characteristic-`p` "Néron–Ogg–Shafarevich at `p`" is simply not a
theorem. Consequently the vendored `torsion_flat_of_good_reduction` and this
prime-power case now carry the hypothesis that the torsion order is nonzero in
`K` — mixed characteristic at `p`, the only case its consumer chain
(`isFlatAt_of_hasGoodReduction`, `K = ℚ`) ever instantiates. Whether the flat
package itself survives in equal characteristic (via twisted
additive-polynomial models `Spec R[T]/(T^p - aT)` rather than the refuted
unramifiedness route) is left undecided and untracked: no consumer needs it.
The excised chain is recoverable from git history at this commit's parent.
-/

/-- **The residue-characteristic prime-power case** (DECOMPOSED 2026-07-22 into the
Katz–Mazur prolongation leaf `torsion_flat_prolong_of_good_reduction_prime_pow` —
fed by the shared Galois-correspondence leaf
`exists_torsion_etale_package_over_fractionField`; the assembly below is proven;
NARROWED 2026-07-23 by the mixed-characteristic hypothesis `(p : K) ≠ 0` after the
equal-characteristic branch was refuted — see the section comment above): the
flat-torsion package for the `p ^ k`-torsion of `E` when the prime `p` is *not*
invertible in `R` but nonzero in `K` (so `p` is the residue characteristic and the
characteristic of `K` is zero or prime to `p`; for the Frey curve application
`R = ℤ_(p)`, `K = ℚ`, `k = 1`). -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0)
    (hpK : (p : K) ≠ 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  -- mixed characteristic: the shared étale `K`-package + the Katz–Mazur prolongation
  have hpR : ((p ^ k : ℕ) : R) ≠ 0 := by
    intro h0
    apply hpK
    have h1 : ((p ^ k : ℕ) : K) = 0 := by
      rw [← map_natCast (algebraMap R K), h0, map_zero]
    push_cast at h1
    exact (pow_eq_zero_iff hk).mp h1
  obtain ⟨HK, iCR, iHopf, iFin, iEt, f, hf⟩ :=
    WeierstrassCurve.exists_torsion_etale_package_over_fractionField R K E Ksep
      (p ^ k) hpR
  letI := iCR; letI := iHopf; letI := iFin; letI := iEt
  exact WeierstrassCurve.torsion_flat_prolong_of_good_reduction_prime_pow
    R K E Ksep p hp hpu k hk hpK HK f hf

set_option maxHeartbeats 1000000 in
/-- (Vendored from the FLT project; DECOMPOSED 2026-07-22 into the sorried leaves
above by splitting `n` into its `R`-unit part and its residue-characteristic part;
NARROWED 2026-07-23 by the hypothesis `(n : K) ≠ 0` after the equal-characteristic
branch was refuted by an explicit good-reduction curve with prime-order torsion in
the kernel of reduction — see the section comment above
`torsion_flat_of_good_reduction_prime_pow`. The hypothesis is automatic when `K`
has characteristic zero, in particular for the consumer chain
`isFlatAt_of_hasGoodReduction` over `K = ℚ`.)
If `E` is an elliptic curve over the field of fractions `K` of a discrete valuation
ring `R` with good reduction over `R`, and `n` is nonzero in `K`, then the `n`-torsion
of `E` is a finite flat group scheme: there is a commutative Hopf algebra `H` over `R`,
finite and flat as an `R`-module, whose generic fibre `K ⊗[R] H` is étale over `K` and
whose group of `Kˢᵉᵖ`-points (a group under convolution) is isomorphic, compatibly with
the actions of `Gal(Kˢᵉᵖ/K)` on the two sides, to the `n`-torsion subgroup of
`E(Kˢᵉᵖ)`. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction (hnK : (n : K) ≠ 0) :
    -- There is a commutative Hopf algebra H over R (the functions on a group scheme over R),
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      -- finite and flat as an R-module (so the group scheme is finite flat),
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      -- whose generic fibre K ⊗[R] H is étale over K,
      (_ : Algebra.Etale K (K ⊗[R] H))
      -- together with an isomorphism of groups from the Kˢᵉᵖ-points of the generic fibre
      -- (a group under convolution, because K ⊗[R] H is a Hopf algebra over K)
      -- to the n-torsion subgroup of E(Kˢᵉᵖ),
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (n : ℤ)),
      -- which is equivariant for the actions of Gal(Kˢᵉᵖ/K) on the two sides.
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  by_cases hu : IsUnit (n : R)
  -- if `n` is invertible in the residue field, the étale leaf applies directly
  · exact WeierstrassCurve.torsion_flat_of_good_reduction_of_isUnit R K E Ksep n hu
  -- otherwise some prime factor `p` of `n` is a nonunit in `R` (necessarily the residue
  -- characteristic, and the only nonunit prime); split `n = p ^ k * m` with `p ∤ m`,
  -- so `m` is a unit in `R`, and tensor the prime-power package with the étale package
  · have hn0 : n ≠ 0 := NeZero.ne n
    have hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬IsUnit (p : R) := by
      by_contra hall
      push Not at hall
      exact hu (isUnit_natCast_of_forall_prime_isUnit n hn0 hall)
    obtain ⟨p, hp, hpn, hpu⟩ := hex
    obtain ⟨k, m, hk0, hpm, hfact⟩ : ∃ k m : ℕ, k ≠ 0 ∧ ¬p ∣ m ∧ p ^ k * m = n := by
      obtain ⟨k, m, hpm, hfact⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
      refine ⟨k, m, ?_, hpm, hfact.symm⟩
      rintro rfl
      rw [pow_zero, one_mul] at hfact
      exact hpm (hfact ▸ hpn)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hfact
      exact hn0 hfact.symm
    have hmu : IsUnit (m : R) := by
      refine isUnit_natCast_of_forall_prime_isUnit m hm0 fun q hq hqm => ?_
      refine (IsLocalRing.isUnit_natCast_or_isUnit_natCast (A := R)
        ((Nat.coprime_primes hp hq).mpr ?_)).resolve_left hpu
      rintro rfl
      exact hpm hqm
    have hpK : (p : K) ≠ 0 := by
      intro h0
      apply hnK
      rw [← hfact]
      push_cast
      rw [h0, zero_pow hk0, zero_mul]
    have hpkg := WeierstrassCurve.torsion_flat_of_good_reduction_mul R K E Ksep
      (p ^ k) m (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpm))
      (WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow R K E Ksep p hp hpu k hk0
        hpK)
      (WeierstrassCurve.torsion_flat_of_good_reduction_of_isUnit R K E Ksep m hmu)
    rwa [hfact] at hpkg

/-!
### A step towards the proof, via division polynomials

Mathlib knows the division polynomials of a Weierstrass curve `W` over any commutative
ring: `W.Φ n` is monic of degree `n²`, and `W.ΨSq n` has degree `n² - 1` with leading
coefficient `n²` (see `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`, in
particular `natDegree_Φ`, `natDegree_ΨSq` and `leadingCoeff_ΨSq`). What mathlib does not
yet know is the dictionary between division polynomials and torsion: for a point `P ≠ 0`
of `E` over a field, `n • P = 0` iff `ΨSq n` vanishes at `x(P)`, and more generally
`x(n • P) = (Φ n).eval x(P) / (ΨSq n).eval x(P)`.

The two lemmas below isolate the arithmetic input to `torsion_flat_of_good_reduction` as
a purely polynomial statement: the resultant of `Φ n` and `ΨSq n` is `±Δ ^ ((n⁴ - n²)/6)`;
in particular the two polynomials are coprime whenever `Δ` is a unit.

Why the identity is true: over a field on which `Δ` is invertible, a common root of `Φ n`
and `ΨSq n` would — via the dictionary and the definition
`Φ n = X * ΨSq n - preΨ (n+1) * preΨ (n-1) * (1 or Ψ₂Sq)` — be the `x`-coordinate of a
nonzero `n`-torsion point which is also `(n+1)`- or `(n-1)`-torsion, hence trivial, a
contradiction. So over `ℤ[a₁, …, a₆]`, where `Δ` is irreducible, the resultant is forced
to be `±c * Δ ^ k` with `c` an integer; running the same no-common-root argument over
`𝔽ₗ` for every prime `ℓ` (it is insensitive to the characteristic) gives `c = ±1`; and
weights (`aᵢ` has weight `i`, `x` has weight `2`, `Δ` has weight `12`, and the resultant
is isobaric of weight `2 * n² * (n² - 1)`) pin `k = (n⁴ - n²)/6`. Sanity check for
`n = 2`, `y² = x³ - x`: `Φ₂ = (x² + 1)²`, `Ψ₂² = 4(x³ - x)`, so the resultant is
`4⁴ * Φ₂(0) * Φ₂(1) * Φ₂(-1) = 4096 = Δ²`, and `(2⁴ - 2²)/6 = 2`.

Why it is a step towards `torsion_flat_of_good_reduction`:

* For `n` invertible in the residue field of `R`, the leading coefficient `n²` of
  `ΨSq n` is a unit of `R`, so the `x`-coordinates of the nonzero `n`-torsion points of
  `E(Kˢᵉᵖ)` (the roots of `ΨSq n`) are integral over `R`, and coprimality of `Φ n` and
  `ΨSq n` over the residue field (`Δ` is a unit there by good reduction) together with a
  companion identity for the discriminant of `ΨSq n` (of the same `±nᵃ * Δᵇ` shape) shows
  that reduction is injective on the `n`-torsion. Since inertia acts trivially on residue
  fields, it then acts trivially on the torsion: this is the unramifiedness statement of
  `FLT.KnownIn1980s.EllipticCurves.GoodReduction`, and by the discussion in the module
  docstring above (an unramified module of order invertible in the residue field prolongs
  étale-ly), it implies `torsion_flat_of_good_reduction` for all such `n`.

* For `n` divisible by the residue characteristic `p`, division polynomials cannot
  produce the Hopf algebra `H` by themselves: the leading coefficient `n²` of `ΨSq n`
  now lies in the maximal ideal, which is the concrete manifestation of the fact that
  part of the `n`-torsion group scheme sits at the origin, outside the affine chart
  where the division polynomials live (the torsion in the kernel of reduction has
  `x`-coordinates of negative valuation). But the identity is still the arithmetic core
  of the scheme-theoretic proof [Katz–Mazur, *Arithmetic moduli of elliptic curves*,
  Theorem 2.3.1] that multiplication by `n` on the elliptic scheme `𝓔` is finite locally
  free of degree `n²`: the polynomial `(Φ n).eval X - ξ * (ΨSq n).eval X` is monic of
  degree `n²` over `R[ξ]`, where `ξ = x ∘ [n]`, which gives finiteness of `[n]`, and
  coprimality on each fibre gives the constant fibre degree `n²`. So nothing proved here
  is wasted on the hard case.

Reference for the resultant identity in short Weierstrass form: M. Ayad, *Points
S-entiers des courbes elliptiques*, Manuscripta Math. 76 (1992), 305–324.
-/

-- `WeierstrassCurve.isCoprime_Φ_ΨSq` — the Bézout identity `F * Φ n + G * ΨSq n = 1`
-- for a Weierstrass curve with unit discriminant over a field — was PROVEN here
-- (2026-07-17) and MOVED upstream to `Fermat.FLT.EllipticCurve.PhiPsiCoprime`
-- (2026-07-22, still re-exported through this module's public import) to untangle the
-- import cycle recorded in the history of this file: `TorsionCard`/`TorsionCardSep`
-- consume it and `GoodReduction` builds on them, while this file consumes the proven
-- Néron–Ogg–Shafarevich theorem of `GoodReduction`.
