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
-- tensor products commute with finite products (`Algebra.TensorProduct.piRight`)
-- and étale-ness is product-local (`Algebra.FormallyEtale.pi_iff`): the product
-- assembly of `exists_finite_etale_algebra_form_of_inertia_fixes`
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Etale.Pi
-- étale ⟹ smooth ⟹ flat: the injectivity of `H₀ → K ⊗[R] H₀` for an étale
-- `R`-form `H₀`, in the canonicity leaf
-- `range_comp_includeRight_eq_integralClosure_of_etale_form`
import Mathlib.RingTheory.Smooth.Flat
-- radicality of `𝔪 H₀` for an unramified `R`-algebra `H₀`
-- (`Algebra.FormallyUnramified.isRadical_map_isMaximal`), same leaf
import Mathlib.RingTheory.Unramified.Field
-- ring/algebra structure on `Shrink` and the `coassoc_simps` normalization set:
-- the universe-transport leaf `exists_hopfAlgebra_small_copy`
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Coalgebra.CoassocSimps
-- `HopfAlgebra.antipodeAlgHom` (the antipode of a commutative Hopf algebra is
-- an algebra homomorphism), same leaf
public import Mathlib.RingTheory.HopfAlgebra.Convolution
-- `IsGalois.normalBasis`: the Dedekind-matrix inversion step of the
-- Galois-descent core `galoisEquivariant_mem_span`
import Mathlib.FieldTheory.Galois.NormalBasis
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

/-- **The product Galois action on `B × C`** (glue for the Hopf package of the
equivariant-functions algebra: its tensor square is identified with the
equivariant functions on `A × A` carrying the diagonal instance of this
action; the mixed instances appear in the coassociativity diagrams). -/
def galoisProdAction {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C) :
    (L ≃ₐ[K₀] L) →* AddMonoid.End (B × C) where
  toFun g := AddMonoidHom.prodMap (ρB g) (ρC g)
  map_one' := AddMonoidHom.ext fun x => by
    show ((ρB 1) x.1, (ρC 1) x.2) = x
    rw [map_one, map_one]
    rfl
  map_mul' g₁ g₂ := AddMonoidHom.ext fun x => by
    show ((ρB (g₁ * g₂)) x.1, (ρC (g₁ * g₂)) x.2) = _
    rw [map_mul, map_mul]
    rfl

/-- **Pullback of equivariant functions along an equivariant map** (glue for
the Hopf package): precomposition with an equivariant additive map `f : B → C`
carries `Gal(L/K₀)`-equivariant functions on `C` to equivariant functions on
`B`, as a `K₀`-algebra homomorphism. The comultiplication, antipode and the
tensor-comparison legs of the equivariant-functions Hopf algebra are all
instances of this. -/
def galoisEquivariantPullback {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C)
    (f : B →+ C) (hf : ∀ g b, f (ρB g b) = ρC g (f b)) :
    galoisEquivariantAlgebra L ρC →ₐ[K₀] galoisEquivariantAlgebra L ρB where
  toFun h := ⟨fun b => (h : C → L) (f b), fun g b => by
    show (h : C → L) (f (ρB g b)) = g ((h : C → L) (f b))
    rw [hf g b]
    exact h.2 g (f b)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- **The tensor-comparison homomorphism** (glue for the Hopf package):
`h₁ ⊗ h₂` acts on `B × C` as `(b, c) ↦ h₁ b * h₂ c`, giving a `K₀`-algebra map
from the tensor product of two equivariant-functions algebras to the
equivariant functions on `B × C`. Its bijectivity is the sorried
Galois-descent core `galoisEquivariantTensorHom_bijective`; the Hopf package
uses the diagonal instance `B = C = A` and (for the coassociativity diagrams)
the mixed instances with `A × A`. -/
noncomputable def galoisEquivariantTensorHom {B C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C) :
    (galoisEquivariantAlgebra L ρB) ⊗[K₀] (galoisEquivariantAlgebra L ρC)
      →ₐ[K₀] galoisEquivariantAlgebra L (galoisProdAction L ρB ρC) :=
  Algebra.TensorProduct.productMap
    (galoisEquivariantPullback L (galoisProdAction L ρB ρC) ρB
      (AddMonoidHom.fst B C) fun _ _ => rfl)
    (galoisEquivariantPullback L (galoisProdAction L ρB ρC) ρC
      (AddMonoidHom.snd B C) fun _ _ => rfl)

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- Membership in the equivariant-functions algebra, unfolded. -/
theorem mem_galoisEquivariantAlgebra_iff {B : Type*} [AddCommGroup B]
    {ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B} {f : B → L} :
    f ∈ galoisEquivariantAlgebra L ρB ↔ ∀ g b, f (ρB g b) = g (f b) :=
  Iff.rfl

/-- **Linear disjointness of equivariant functions** (the injectivity half of
split Galois descent, ported 2026-07-23 from the proven
`galDesc_linearIndependent` of `Fermat.FLT.FreyCurve.Semistable`): a
`K₀`-linearly independent family in the equivariant-functions algebra stays
`L`-linearly independent as functions `B → L`. Minimal-relation argument:
normalize a shortest nontrivial `L`-relation to have a coefficient `1`,
subtract its Galois translates (again relations, by equivariance of the
functions), conclude all coefficients are Galois-fixed, hence in `K₀` —
contradiction. -/
theorem galoisEquivariant_linearIndependent {B : Type*} [AddCommGroup B]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B) {ι : Type*}
    {v : ι → galoisEquivariantAlgebra L ρB} (hv : LinearIndependent K₀ v) :
    LinearIndependent ↥L fun i => (v i : B → L) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀s, hi₀⟩ := hne
    set c' : ι → ↥L := fun i => (c i₀)⁻¹ * c i with hc'def
    have hrel : ∑ i ∈ s, c' i • (v i : B → L) = 0 := by
      have h1 := congrArg (fun f : B → ↥L => (c i₀)⁻¹ • f) hc
      simpa [Finset.smul_sum, smul_smul, hc'def] using h1
    have hc'i₀ : c' i₀ = 1 := by
      simp only [hc'def]
      exact inv_mul_cancel₀ hi₀
    have hrelg : ∀ g : ↥L ≃ₐ[K₀] ↥L,
        ∑ i ∈ s, g (c' i) • (v i : B → L) = 0 := by
      intro g
      have h0 : ∀ b : B, ∑ i ∈ s, c' i * (v i : B → L) (ρB g⁻¹ b) = 0 := by
        intro b
        have h2 := congrFun hrel (ρB g⁻¹ b)
        simpa using h2
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc ∑ i ∈ s, g (c' i) * (v i : B → L) b
          = ∑ i ∈ s, g (c' i) * g ((v i : B → L) (ρB g⁻¹ b)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [(v i).2 g⁻¹ b, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        _ = g (∑ i ∈ s, c' i * (v i : B → L) (ρB g⁻¹ b)) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => (map_mul g _ _).symm
        _ = 0 := by rw [h0 b, map_zero]
    have hfix : ∀ (g : ↥L ≃ₐ[K₀] ↥L) (i : ι), i ∈ s → g (c' i) = c' i := by
      intro g i hi
      have h3 : ∑ j ∈ s, (g (c' j) - c' j) • (v j : B → L) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hrelg g, hrel, sub_zero]
      have h4 : ∑ j ∈ s.erase i₀, (g (c' j) - c' j) • (v j : B → L) = 0 := by
        rwa [← Finset.add_sum_erase _ _ hi₀s, hc'i₀, map_one, sub_self, zero_smul,
          zero_add] at h3
      have h5 := ih (s.erase i₀) (Finset.erase_ssubset hi₀s) _ h4
      rcases eq_or_ne i i₀ with rfl | hne'
      · rw [hc'i₀, map_one]
      · exact sub_eq_zero.mp (h5 i (Finset.mem_erase.mpr ⟨hne', hi⟩))
    have hK : ∀ i : ι, ∃ k : K₀, i ∈ s → algebraMap K₀ ↥L k = c' i := by
      intro i
      by_cases hi : i ∈ s
      · have hmem : c' i ∈ Set.range (algebraMap K₀ ↥L) := by
          rw [IsGalois.mem_range_algebraMap_iff_fixed]
          exact fun g => hfix g i hi
        exact ⟨hmem.choose, fun _ => hmem.choose_spec⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose k hk using hK
    have hrelK : ∑ i ∈ s, k i • v i = 0 := by
      have hcoe : ((∑ i ∈ s, k i • v i : galoisEquivariantAlgebra L ρB) :
          B → L) = ∑ i ∈ s, c' i • (v i : B → L) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [SetLike.val_smul, ← hk i hi, algebraMap_smul]
      exact Subtype.ext (by rw [hcoe, hrel]; rfl)
    have h6 := linearIndependent_iff'.mp hv s k hrelK i₀ hi₀s
    rw [← hk i₀ hi₀s, h6, map_zero] at hc'i₀
    exact zero_ne_one hc'i₀

/-- **Spanning by equivariant functions** (the surjectivity half of split
Galois descent, ported 2026-07-23 from the proven `galDesc_mem_span` of
`Fermat.FLT.FreyCurve.Semistable`): every function `B → L` is an `L`-linear
combination of equivariant ones. For `c : L` the averaged function
`b ↦ ∑ g, g (c · f (ρB g⁻¹ b))` is equivariant; running `c` through a normal
basis of `L/K₀` and inverting the Dedekind matrix `(g (nb j))` recovers `f`
itself as a combination of averages. -/
theorem galoisEquivariant_mem_span {B : Type*} [AddCommGroup B]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B) (f : B → L) :
    f ∈ Submodule.span ↥L (galoisEquivariantAlgebra L ρB : Set (B → L)) := by
  classical
  have hmul : ∀ (g₁ g₂ : L ≃ₐ[K₀] L) (b : B),
      ρB (g₁ * g₂) b = ρB g₁ (ρB g₂ b) := fun g₁ g₂ b => by rw [map_mul]; rfl
  have havg : ∀ c : ↥L,
      (fun b => ∑ g : ↥L ≃ₐ[K₀] ↥L, g (c * f (ρB g⁻¹ b))) ∈
        galoisEquivariantAlgebra L ρB := by
    intro c
    refine (mem_galoisEquivariantAlgebra_iff L).mpr fun g₀ b => ?_
    have hstep : ∀ g : ↥L ≃ₐ[K₀] ↥L,
        (g₀ * g) (c * f (ρB (g₀ * g)⁻¹ (ρB g₀ b))) = g₀ (g (c * f (ρB g⁻¹ b))) := by
      intro g
      have hact : ρB (g₀ * g)⁻¹ (ρB g₀ b) = ρB g⁻¹ b := by
        rw [← hmul, mul_inv_rev, inv_mul_cancel_right]
      rw [hact, AlgEquiv.mul_apply]
    calc (fun b => ∑ g : ↥L ≃ₐ[K₀] ↥L, g (c * f (ρB g⁻¹ b))) (ρB g₀ b)
        = ∑ g : ↥L ≃ₐ[K₀] ↥L, (g₀ * g) (c * f (ρB (g₀ * g)⁻¹ (ρB g₀ b))) :=
          (Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => rfl).symm
      _ = ∑ g : ↥L ≃ₐ[K₀] ↥L, g₀ (g (c * f (ρB g⁻¹ b))) :=
          Finset.sum_congr rfl fun g _ => hstep g
      _ = g₀ ((fun b => ∑ g : ↥L ≃ₐ[K₀] ↥L, g (c * f (ρB g⁻¹ b))) b) :=
          (map_sum g₀ _ _).symm
  set nb : Module.Basis (↥L ≃ₐ[K₀] ↥L) K₀ ↥L := IsGalois.normalBasis K₀ ↥L
  set M : Matrix (↥L ≃ₐ[K₀] ↥L) (↥L ≃ₐ[K₀] ↥L) ↥L :=
    Matrix.of fun g j => g (nb j) with hM
  have hMinj : Function.Injective M.vecMul := by
    have hli : LinearIndependent ↥L
        fun g : ↥L ≃ₐ[K₀] ↥L => (g : ↥L →ₐ[K₀] ↥L).toLinearMap :=
      (linearIndependent_toLinearMap K₀ ↥L ↥L).comp
        (fun g : ↥L ≃ₐ[K₀] ↥L => (g : ↥L →ₐ[K₀] ↥L))
        AlgEquiv.coe_toAlgHom_injective
    have hker : ∀ z : (↥L ≃ₐ[K₀] ↥L) → ↥L, M.vecMul z = 0 → z = 0 := by
      intro z hz
      have hzero : (∑ g : ↥L ≃ₐ[K₀] ↥L, z g • (g : ↥L →ₐ[K₀] ↥L).toLinearMap)
          = (0 : ↥L →ₗ[K₀] ↥L) := by
        refine nb.ext fun j => ?_
        have hj : ∑ g : ↥L ≃ₐ[K₀] ↥L, z g * g (nb j) = 0 := by
          have h1 := congrFun hz j
          simpa [Matrix.vecMul, dotProduct, hM] using h1
        simpa using hj
      funext g
      exact Fintype.linearIndependent_iff.mp hli z hzero g
    intro x y hxy
    have hxy' : Matrix.vecMul x M = Matrix.vecMul y M := hxy
    have hsub := hker (x - y) (by rw [Matrix.sub_vecMul, hxy', sub_self])
    exact sub_eq_zero.mp hsub
  obtain ⟨d, hd⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (Matrix.vecMul_injective_iff_isUnit.mp hMinj)) (Pi.single 1 1)
  have hfeq : f = ∑ j : ↥L ≃ₐ[K₀] ↥L,
      d j • fun b => ∑ g : ↥L ≃ₐ[K₀] ↥L, g (nb j * f (ρB g⁻¹ b)) := by
    funext b
    have hpt : ∀ g j : ↥L ≃ₐ[K₀] ↥L,
        d j * g (nb j * f (ρB g⁻¹ b)) = M g j * d j * g (f (ρB g⁻¹ b)) := by
      intro g j
      rw [map_mul, hM, Matrix.of_apply]
      ring
    have hRHS : (∑ j : ↥L ≃ₐ[K₀] ↥L, d j • fun b' =>
        ∑ g : ↥L ≃ₐ[K₀] ↥L, g (nb j * f (ρB g⁻¹ b'))) b
        = ∑ g : ↥L ≃ₐ[K₀] ↥L, M.mulVec d g * g (f (ρB g⁻¹ b)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc ∑ j : ↥L ≃ₐ[K₀] ↥L, d j * ∑ g : ↥L ≃ₐ[K₀] ↥L, g (nb j * f (ρB g⁻¹ b))
          = ∑ j : ↥L ≃ₐ[K₀] ↥L, ∑ g : ↥L ≃ₐ[K₀] ↥L, d j * g (nb j * f (ρB g⁻¹ b)) :=
            Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        _ = ∑ g : ↥L ≃ₐ[K₀] ↥L, ∑ j : ↥L ≃ₐ[K₀] ↥L, d j * g (nb j * f (ρB g⁻¹ b)) :=
            Finset.sum_comm
        _ = ∑ g : ↥L ≃ₐ[K₀] ↥L, ∑ j : ↥L ≃ₐ[K₀] ↥L, M g j * d j * g (f (ρB g⁻¹ b)) :=
            Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun j _ => hpt g j
        _ = ∑ g : ↥L ≃ₐ[K₀] ↥L, (∑ j : ↥L ≃ₐ[K₀] ↥L, M g j * d j) * g (f (ρB g⁻¹ b)) :=
            Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
        _ = ∑ g : ↥L ≃ₐ[K₀] ↥L, M.mulVec d g * g (f (ρB g⁻¹ b)) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            congr 1
    rw [hRHS, hd]
    simp [Pi.single_apply, ite_mul]
  rw [hfeq]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (havg (nb j)))

/-- **The dimension count of split descent** (ported 2026-07-23 from the proven
`galDesc_finrank` of `Fermat.FLT.FreyCurve.Semistable`): the
equivariant-functions algebra of a finite `Gal(L/K₀)`-module `B` has
`K₀`-dimension `|B|` — the split base-change map `θ : L ⊗[K₀] H_B → (B → L)`,
`l ⊗ h ↦ l·h`, is bijective (injective by
`galoisEquivariant_linearIndependent` on a basis, surjective by
`galoisEquivariant_mem_span`), and `dim_L (B → L) = |B|`. -/
theorem galoisEquivariant_finrank {B : Type*} [AddCommGroup B] [Finite B]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B) :
    Module.finrank K₀ (galoisEquivariantAlgebra L ρB) = Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  set θ : ↥L ⊗[K₀] (galoisEquivariantAlgebra L ρB) →ₗ[↥L] (B → L) :=
    ((Subalgebra.toSubmodule (galoisEquivariantAlgebra L ρB)).subtype).liftBaseChange
      ↥L with hθ
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    set β := Module.finBasis K₀ (galoisEquivariantAlgebra L ρB)
    have hLI := galoisEquivariant_linearIndependent L ρB β.linearIndependent
    have hcoeff : ∀ i, (β.baseChange ↥L).repr t i = 0 := by
      have hθt : ∑ i, (β.baseChange ↥L).repr t i • (β i : B → L) = 0 := by
        have hsum : θ (∑ i, (β.baseChange ↥L).repr t i • β.baseChange ↥L i)
            = ∑ i, (β.baseChange ↥L).repr t i • (β i : B → L) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, Module.Basis.baseChange_apply, hθ,
            LinearMap.liftBaseChange_tmul, one_smul]
          rfl
        rw [← hsum, Module.Basis.sum_repr, ht]
      exact fun i => Fintype.linearIndependent_iff.mp hLI _ hθt i
    rw [← Module.Basis.sum_repr (β.baseChange ↥L) t]
    simp [hcoeff]
  have hsurj : Function.Surjective θ := by
    intro f
    have hle : Submodule.span ↥L (galoisEquivariantAlgebra L ρB : Set (B → L)) ≤
        LinearMap.range θ := by
      rw [Submodule.span_le]
      intro x hx
      exact ⟨(1 : ↥L) ⊗ₜ[K₀] ⟨x, hx⟩, by
        rw [hθ, LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
    exact LinearMap.mem_range.mp (hle (galoisEquivariant_mem_span L ρB f))
  have hfr := (LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_pi] at hfr
  rw [Nat.card_eq_fintype_card]
  exact hfr

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- Evaluating the tensor-comparison homomorphism on a pure tensor at a point
of `B × C` multiplies the two evaluations. -/
theorem galoisEquivariantTensorHom_tmul_apply {B C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C)
    (h : galoisEquivariantAlgebra L ρB) (k : galoisEquivariantAlgebra L ρC)
    (x : B × C) :
    (galoisEquivariantTensorHom L ρB ρC (h ⊗ₜ[K₀] k) : (B × C) → L) x
      = (h : B → L) x.1 * (k : C → L) x.2 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Galois descent for the tensor product of equivariant-functions algebras**
(PROVEN 2026-07-23, ported from the proven `galDescProdHom_bijective` of
`Fermat.FLT.FreyCurve.Semistable`; the descent core of the
equivariant-functions Hopf package): the tensor-comparison homomorphism is
bijective. Both sides have `K₀`-dimension `|B| ⬝ |C|`
(`galoisEquivariant_finrank`), and the map is injective by linear disjointness
of the evaluations: expanding a kernel element along a `K₀`-basis of the right
factor, the coefficient functions vanish because the basis stays `L`-linearly
independent (`galoisEquivariant_linearIndependent` — Dedekind's independence). -/
theorem galoisEquivariantTensorHom_bijective {B C : Type*}
    [AddCommGroup B] [AddCommGroup C] [Finite B] [Finite C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C) :
    Function.Bijective (galoisEquivariantTensorHom L ρB ρC) := by
  classical
  haveI : Module.Finite K₀ (galoisEquivariantAlgebra L ρB) :=
    galoisEquivariantAlgebra_finite L ρB
  haveI : Module.Finite K₀ (galoisEquivariantAlgebra L ρC) :=
    galoisEquivariantAlgebra_finite L ρC
  haveI : Module.Finite K₀
      (galoisEquivariantAlgebra L (galoisProdAction L ρB ρC)) :=
    galoisEquivariantAlgebra_finite L _
  have hinj : Function.Injective (galoisEquivariantTensorHom L ρB ρC) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    set γ := Module.finBasis K₀ (galoisEquivariantAlgebra L ρC)
    obtain ⟨w, rfl⟩ : ∃ w : Fin (Module.finrank K₀ (galoisEquivariantAlgebra L ρC))
        → galoisEquivariantAlgebra L ρB, t = ∑ i, w i ⊗ₜ[K₀] γ i := by
      clear ht
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul h k =>
        refine ⟨fun i => γ.repr k i • h, ?_⟩
        conv_lhs => rw [← Module.Basis.sum_repr γ k]
        rw [TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
      | add t₁ t₂ h₁ h₂ =>
        obtain ⟨w₁, rfl⟩ := h₁
        obtain ⟨w₂, rfl⟩ := h₂
        refine ⟨w₁ + w₂, ?_⟩
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (TensorProduct.add_tmul _ _ _).symm
    have hLI := galoisEquivariant_linearIndependent L ρC γ.linearIndependent
    have hpt : ∀ (b : B) (cc : C),
        ∑ i, ((w i : B → L) b) * ((γ i : C → L) cc) = 0 := by
      intro b cc
      have h1 := congrArg
        (fun F : galoisEquivariantAlgebra L (galoisProdAction L ρB ρC) =>
          (F : (B × C) → L) (b, cc)) ht
      simpa [map_sum, galoisEquivariantTensorHom_tmul_apply] using h1
    have hw : ∀ i, w i = 0 := by
      intro i
      apply Subtype.ext
      funext b
      have hrel : ∑ j, ((w j : B → L) b) • (γ j : C → L) = 0 := by
        funext cc
        simpa using hpt b cc
      exact Fintype.linearIndependent_iff.mp hLI _ hrel i
    simp [hw]
  refine ⟨hinj, ?_⟩
  have hfr : Module.finrank K₀
      ((galoisEquivariantAlgebra L ρB) ⊗[K₀] (galoisEquivariantAlgebra L ρC))
      = Module.finrank K₀
        (galoisEquivariantAlgebra L (galoisProdAction L ρB ρC)) := by
    rw [Module.finrank_tensorProduct,
      galoisEquivariant_finrank L ρB,
      galoisEquivariant_finrank L ρC,
      galoisEquivariant_finrank L (galoisProdAction L ρB ρC),
      Nat.card_prod]
  have hsurjlin := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := K₀)
    (V := (galoisEquivariantAlgebra L ρB) ⊗[K₀] (galoisEquivariantAlgebra L ρC))
    (V₂ := galoisEquivariantAlgebra L (galoisProdAction L ρB ρC))
    hfr (f := (galoisEquivariantTensorHom L ρB ρC).toLinearMap)).mp
    (by simpa using hinj)
  simpa using hsurjlin

/-- Postcomposition with an algebra map distributes over
`Algebra.TensorProduct.lift` into a commutative target (toolkit for the
Hopf-axiom computations below; ported from the proven `galDesc_comp_lift` of
`Fermat.FLT.FreyCurve.Semistable`). -/
theorem galois_comp_lift {R A₁ A₂ S T : Type*} [CommSemiring R]
    [Semiring A₁] [Algebra R A₁] [Semiring A₂] [Algebra R A₂]
    [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (f : A₁ →ₐ[R] S) (g : A₂ →ₐ[R] S) :
    φ.comp (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _)
      = Algebra.TensorProduct.lift (φ.comp f) (φ.comp g)
          fun _ _ => Commute.all _ _ :=
  Algebra.TensorProduct.ext' fun x y => by
    simp [Algebra.TensorProduct.lift_tmul]

/-- The lift of three algebra maps into a commutative target regroups along the
associator (toolkit for the coassociativity computation below; ported from the
proven `galDesc_lift_assoc` of `Fermat.FLT.FreyCurve.Semistable`). -/
theorem galois_lift_assoc {R A₁ A₂ A₃ S : Type*} [CommSemiring R]
    [Semiring A₁] [Algebra R A₁] [Semiring A₂] [Algebra R A₂]
    [Semiring A₃] [Algebra R A₃] [CommSemiring S] [Algebra R S]
    (f : A₁ →ₐ[R] S) (g : A₂ →ₐ[R] S) (h : A₃ →ₐ[R] S) :
    (Algebra.TensorProduct.lift f
        (Algebra.TensorProduct.lift g h fun _ _ => Commute.all _ _)
        fun _ _ => Commute.all _ _).comp
      (Algebra.TensorProduct.assoc R R R A₁ A₂ A₃).toAlgHom
      = Algebra.TensorProduct.lift
          (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _) h
          fun _ _ => Commute.all _ _ := by
  apply Algebra.TensorProduct.ext'
  intro u c
  induction u using TensorProduct.induction_on with
  | zero => simp [TensorProduct.zero_tmul]
  | tmul x y =>
    simp [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul,
      mul_assoc]
  | add u₁ u₂ h₁ h₂ =>
    rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂]

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- Evaluation of an equivariant function at a point of `B`, valued in `L` —
the separating functional for the Hopf-axiom computations. -/
def galoisEvalL {B : Type*} [AddCommGroup B]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B) (b : B) :
    galoisEquivariantAlgebra L ρB →ₐ[K₀] L :=
  (Pi.evalAlgHom K₀ (fun _ : B => L) b).comp (galoisEquivariantAlgebra L ρB).val

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- Evaluating the tensor-comparison homomorphism at a point of `B × C` is the
lift of the two evaluations. -/
theorem galoisEvalL_comp_tensorHom {B C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (ρB : (L ≃ₐ[K₀] L) →* AddMonoid.End B)
    (ρC : (L ≃ₐ[K₀] L) →* AddMonoid.End C) (b : B) (c : C) :
    (galoisEvalL L (galoisProdAction L ρB ρC) (b, c)).comp
        (galoisEquivariantTensorHom L ρB ρC)
      = Algebra.TensorProduct.lift (galoisEvalL L ρB b) (galoisEvalL L ρC c)
          fun _ _ => Commute.all _ _ :=
  Algebra.TensorProduct.ext' fun h k => by
    rw [Algebra.TensorProduct.lift_tmul]
    exact galoisEquivariantTensorHom_tmul_apply L ρB ρC h k (b, c)

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- **Pullback along the addition `A × A → A`** — the group law of the twisted
constant group scheme, before identification of the tensor square. -/
def galoisAddHom : galoisEquivariantAlgebra L ρ →ₐ[K₀]
    galoisEquivariantAlgebra L (galoisProdAction L ρ ρ) :=
  galoisEquivariantPullback L (galoisProdAction L ρ ρ) ρ
    (AddMonoidHom.coprod (AddMonoidHom.id A) (AddMonoidHom.id A))
    fun g x => show ρ g x.1 + ρ g x.2 = ρ g (x.1 + x.2) from
      (map_add (ρ g) x.1 x.2).symm

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- **Pullback along the negation `A → A`** — the antipode of the twisted
constant group scheme. -/
def galoisAntipodeHom : galoisEquivariantAlgebra L ρ →ₐ[K₀]
    galoisEquivariantAlgebra L ρ :=
  galoisEquivariantPullback L ρ ρ (negAddMonoidHom (α := A))
    fun g a => show -(ρ g a) = ρ g (-a) from (map_neg (ρ g) a).symm

/-- The tensor-comparison isomorphism `H ⊗[K₀] H ≃ H₂` (from the bijectivity
hypothesis). -/
noncomputable def galoisTensorAlgEquiv
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    ((galoisEquivariantAlgebra L ρ) ⊗[K₀] (galoisEquivariantAlgebra L ρ)) ≃ₐ[K₀]
      galoisEquivariantAlgebra L (galoisProdAction L ρ ρ) :=
  AlgEquiv.ofBijective (galoisEquivariantTensorHom L ρ ρ) hbij

/-- The comultiplication of the twisted constant group scheme: pull back along
the addition, then identify the equivariant functions on `A × A` with the
tensor square. -/
noncomputable def galoisComulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    galoisEquivariantAlgebra L ρ →ₐ[K₀]
      (galoisEquivariantAlgebra L ρ) ⊗[K₀] (galoisEquivariantAlgebra L ρ) :=
  ((galoisTensorAlgEquiv L ρ hbij).symm.toAlgHom).comp (galoisAddHom L ρ)

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- The tensor comparison inverts the comultiplication back to the pullback
along the addition: `μ ∘ Δ = add*`. -/
theorem galoisTensorHom_comp_comulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (galoisEquivariantTensorHom L ρ ρ).comp (galoisComulHom L ρ hbij)
      = galoisAddHom L ρ :=
  AlgHom.ext fun h =>
    (galoisTensorAlgEquiv L ρ hbij).apply_symm_apply (galoisAddHom L ρ h)

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- **Evaluations compose with the comultiplication as addition of the
evaluation points**: `(ev_x ⊗ ev_y) ∘ Δ = ev_{x+y}` — the computational heart
of all the Hopf-axiom computations below. -/
theorem galois_lift_evalL_comp_comulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) (x y : A) :
    (Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        fun _ _ => Commute.all _ _).comp (galoisComulHom L ρ hbij)
      = galoisEvalL L ρ (x + y) := by
  have h1 : Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
      (fun _ _ => Commute.all _ _)
      = (galoisEvalL L (galoisProdAction L ρ ρ) (x, y)).comp
          (galoisEquivariantTensorHom L ρ ρ) :=
    (galoisEvalL_comp_tensorHom L ρ ρ x y).symm
  rw [h1, AlgHom.comp_assoc, galoisTensorHom_comp_comulHom]
  exact AlgHom.ext fun h => rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Elements of the triple tensor `H ⊗ (H ⊗ H)` are separated by the triple
evaluations `ev_a ⊗ (ev_b ⊗ ev_c)`: the comparison maps into the equivariant
functions on `A × (A × A)` are injective, and equivariant functions are
separated pointwise. -/
theorem galoisTensor₃_ext [Finite A]
    {x y : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      ((galoisEquivariantAlgebra L ρ) ⊗[K₀] (galoisEquivariantAlgebra L ρ))}
    (hxy : ∀ a b c : A,
      Algebra.TensorProduct.lift (galoisEvalL L ρ a)
        (Algebra.TensorProduct.lift (galoisEvalL L ρ b)
          (galoisEvalL L ρ c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) x
      = Algebra.TensorProduct.lift (galoisEvalL L ρ a)
        (Algebra.TensorProduct.lift (galoisEvalL L ρ b)
          (galoisEvalL L ρ c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) y) :
    x = y := by
  classical
  have hval : ∀ (t : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      ((galoisEquivariantAlgebra L ρ) ⊗[K₀] (galoisEquivariantAlgebra L ρ)))
      (a b c : A),
      (galoisEquivariantTensorHom L ρ (galoisProdAction L ρ ρ)
        ((Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
          (galoisEquivariantTensorHom L ρ ρ)) t) : A × (A × A) → L) (a, (b, c))
      = Algebra.TensorProduct.lift (galoisEvalL L ρ a)
        (Algebra.TensorProduct.lift (galoisEvalL L ρ b)
          (galoisEvalL L ρ c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _) t := by
    intro t a b c
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul h u =>
      have hE : ((galoisEquivariantTensorHom L ρ ρ u :
          galoisEquivariantAlgebra L (galoisProdAction L ρ ρ)) : A × A → L) (b, c)
          = Algebra.TensorProduct.lift (galoisEvalL L ρ b) (galoisEvalL L ρ c)
            (fun _ _ => Commute.all _ _) u :=
        DFunLike.congr_fun (galoisEvalL_comp_tensorHom L ρ ρ b c) u
      calc (galoisEquivariantTensorHom L ρ (galoisProdAction L ρ ρ)
            ((Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
              (galoisEquivariantTensorHom L ρ ρ)) (h ⊗ₜ[K₀] u)) : A × (A × A) → L)
            (a, (b, c))
          = (h : A → L) a *
              ((galoisEquivariantTensorHom L ρ ρ u :
                galoisEquivariantAlgebra L (galoisProdAction L ρ ρ)) :
                A × A → L) (b, c) := rfl
        _ = (h : A → L) a *
              Algebra.TensorProduct.lift (galoisEvalL L ρ b) (galoisEvalL L ρ c)
                (fun _ _ => Commute.all _ _) u := by rw [hE]
        _ = Algebra.TensorProduct.lift (galoisEvalL L ρ a)
              (Algebra.TensorProduct.lift (galoisEvalL L ρ b)
                (galoisEvalL L ρ c) fun _ _ => Commute.all _ _)
              (fun _ _ => Commute.all _ _) (h ⊗ₜ[K₀] u) := by
            rw [Algebra.TensorProduct.lift_tmul]
            rfl
    | add t₁ t₂ ih₁ ih₂ =>
      simp [map_add, ih₁, ih₂]
  have hmapinj : Function.Injective
      ⇑(Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
        (galoisEquivariantTensorHom L ρ ρ)) := by
    have h1 := Module.Flat.lTensor_preserves_injective_linearMap
      (M := galoisEquivariantAlgebra L ρ)
      (galoisEquivariantTensorHom L ρ ρ).toLinearMap
      (galoisEquivariantTensorHom_bijective L ρ ρ).injective
    exact h1
  have hprodinj :=
    (galoisEquivariantTensorHom_bijective L ρ (galoisProdAction L ρ ρ)).injective
  apply hmapinj
  apply hprodinj
  apply Subtype.ext
  funext p
  obtain ⟨a, bc⟩ := p
  obtain ⟨b, c⟩ := bc
  rw [hval x a b c, hval y a b c]
  exact hxy a b c

/-- The value at `0` of an equivariant function is Galois-fixed, hence lies in
the base field (`IsGalois.mem_range_algebraMap_iff_fixed`). -/
theorem galois_apply_zero_mem_range (h : galoisEquivariantAlgebra L ρ) :
    (h : A → L) 0 ∈ Set.range (algebraMap K₀ ↥L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro g
  have h2 := h.2 g 0
  simp only [map_zero] at h2
  exact h2.symm

/-- The counit of the twisted constant group scheme: evaluation at the
identity point `0 ∈ A`, landing in `K₀` by the fixed-field identification. -/
noncomputable def galoisCounitHom : galoisEquivariantAlgebra L ρ →ₐ[K₀] K₀ where
  toFun h := (galois_apply_zero_mem_range L ρ h).choose
  map_one' := by
    apply (algebraMap K₀ ↥L).injective
    rw [(galois_apply_zero_mem_range L ρ 1).choose_spec, map_one]
    rfl
  map_mul' x y := by
    apply (algebraMap K₀ ↥L).injective
    rw [map_mul, (galois_apply_zero_mem_range L ρ (x * y)).choose_spec,
      (galois_apply_zero_mem_range L ρ x).choose_spec,
      (galois_apply_zero_mem_range L ρ y).choose_spec]
    rfl
  map_zero' := by
    apply (algebraMap K₀ ↥L).injective
    rw [(galois_apply_zero_mem_range L ρ 0).choose_spec, map_zero]
    rfl
  map_add' x y := by
    apply (algebraMap K₀ ↥L).injective
    rw [map_add, (galois_apply_zero_mem_range L ρ (x + y)).choose_spec,
      (galois_apply_zero_mem_range L ρ x).choose_spec,
      (galois_apply_zero_mem_range L ρ y).choose_spec]
    rfl
  commutes' r := by
    apply (algebraMap K₀ ↥L).injective
    rw [(galois_apply_zero_mem_range L ρ
      (algebraMap K₀ (galoisEquivariantAlgebra L ρ) r)).choose_spec]
    rfl

/-- The defining property of the counit: its image in `L` is the value of the
equivariant function at `0`. -/
theorem galoisCounitHom_algebraMap (h : galoisEquivariantAlgebra L ρ) :
    algebraMap K₀ ↥L (galoisCounitHom L ρ h) = (h : A → L) 0 :=
  (galois_apply_zero_mem_range L ρ h).choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Coassociativity of the twisted comultiplication** (after composing with
the injective tensor comparison into functions on `A × (A × A)`, both sides
are pullback along `(a,b,c) ↦ a+b+c`; elementwise, all triple evaluations
agree by `add_assoc`). -/
theorem galoisComulHom_coassoc [Finite A]
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (Algebra.TensorProduct.assoc K₀ K₀ K₀ (galoisEquivariantAlgebra L ρ)
      (galoisEquivariantAlgebra L ρ) (galoisEquivariantAlgebra L ρ)).toAlgHom.comp
      ((Algebra.TensorProduct.map (galoisComulHom L ρ hbij)
        (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))).comp
        (galoisComulHom L ρ hbij)) =
    (Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
      (galoisComulHom L ρ hbij)).comp (galoisComulHom L ρ hbij) := by
  classical
  apply AlgHom.ext
  intro h
  apply galoisTensor₃_ext L ρ
  intro a b c
  simp only [AlgHom.coe_comp, Function.comp_apply]
  have hΔ : ∀ (x y : A) (t : galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        (fun _ _ => Commute.all _ _) (galoisComulHom L ρ hbij t)
      = (t : A → L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galois_lift_evalL_comp_comulHom L ρ hbij x y) t
  have h1 := DFunLike.congr_fun (galois_lift_assoc
    (galoisEvalL L ρ a) (galoisEvalL L ρ b) (galoisEvalL L ρ c))
    ((Algebra.TensorProduct.map (galoisComulHom L ρ hbij)
      (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ)))
      (galoisComulHom L ρ hbij h))
  simp only [AlgHom.coe_comp, Function.comp_apply] at h1
  rw [h1]
  have hleft : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift
        (Algebra.TensorProduct.lift (galoisEvalL L ρ a)
          (galoisEvalL L ρ b) fun _ _ => Commute.all _ _)
        (galoisEvalL L ρ c) (fun _ _ => Commute.all _ _)
        ((Algebra.TensorProduct.map (galoisComulHom L ρ hbij)
          (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))) u)
      = Algebra.TensorProduct.lift (galoisEvalL L ρ (a + b))
          (galoisEvalL L ρ c) (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_id, id_eq]
      rw [hΔ a b p]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  have hright : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ a)
        (Algebra.TensorProduct.lift (galoisEvalL L ρ b)
          (galoisEvalL L ρ c) fun _ _ => Commute.all _ _)
        (fun _ _ => Commute.all _ _)
        ((Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
          (galoisComulHom L ρ hbij)) u)
      = Algebra.TensorProduct.lift (galoisEvalL L ρ a)
          (galoisEvalL L ρ (b + c)) (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
        AlgHom.coe_id, id_eq]
      rw [hΔ b c q]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  rw [hleft (galoisComulHom L ρ hbij h), hright (galoisComulHom L ρ hbij h),
    hΔ (a + b) c h, hΔ a (b + c) h, add_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Left counit axiom for the twisted comultiplication** (evaluation of the
first tensor factor at `0` collapses the pullback along addition to the
identity: pointwise, `h (0 + z) = h z`). -/
theorem galoisComulHom_rTensor_counit [Finite A]
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (Algebra.TensorProduct.map (galoisCounitHom L ρ)
      (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))).comp
      (galoisComulHom L ρ hbij) =
    ((Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ)).symm :
      galoisEquivariantAlgebra L ρ →ₐ[K₀]
        K₀ ⊗[K₀] galoisEquivariantAlgebra L ρ) := by
  classical
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ)).injective
  show (Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ))
      ((Algebra.TensorProduct.map (galoisCounitHom L ρ)
        (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ)))
        (galoisComulHom L ρ hbij h))
    = (Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ))
      ((Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ)).symm h)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        (fun _ _ => Commute.all _ _) (galoisComulHom L ρ hbij t)
      = (t : A → L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galois_lift_evalL_comp_comulHom L ρ hbij x y) t
  have hval : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      ((Algebra.TensorProduct.lid K₀ (galoisEquivariantAlgebra L ρ))
        ((Algebra.TensorProduct.map (galoisCounitHom L ρ)
          (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))) u) : A → L) z
      = Algebra.TensorProduct.lift (galoisEvalL L ρ 0) (galoisEvalL L ρ z)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        AlgHom.coe_id, id_eq, Algebra.TensorProduct.lift_tmul]
      rw [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def,
        galoisCounitHom_algebraMap]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  rw [hval (galoisComulHom L ρ hbij h), hΔ 0 z h, zero_add]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Right counit axiom for the twisted comultiplication** (symmetric to the
left axiom: pointwise, `h (z + 0) = h z`). -/
theorem galoisComulHom_lTensor_counit [Finite A]
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
      (galoisCounitHom L ρ)).comp (galoisComulHom L ρ hbij) =
    ((Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ)).symm :
      galoisEquivariantAlgebra L ρ →ₐ[K₀]
        (galoisEquivariantAlgebra L ρ) ⊗[K₀] K₀) := by
  classical
  apply AlgHom.ext
  intro h
  apply (Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ)).injective
  show (Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ))
      ((Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
        (galoisCounitHom L ρ)) (galoisComulHom L ρ hbij h))
    = (Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ))
      ((Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ)).symm h)
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        (fun _ _ => Commute.all _ _) (galoisComulHom L ρ hbij t)
      = (t : A → L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galois_lift_evalL_comp_comulHom L ρ hbij x y) t
  have hval : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      ((Algebra.TensorProduct.rid K₀ K₀ (galoisEquivariantAlgebra L ρ))
        ((Algebra.TensorProduct.map (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
          (galoisCounitHom L ρ)) u) : A → L) z
      = Algebra.TensorProduct.lift (galoisEvalL L ρ z) (galoisEvalL L ρ 0)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        AlgHom.coe_id, id_eq, Algebra.TensorProduct.lift_tmul]
      rw [SetLike.val_smul, Pi.smul_apply, Algebra.smul_def,
        galoisCounitHom_algebraMap]
      exact mul_comm _ _
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  rw [hval (galoisComulHom L ρ hbij h), hΔ z 0 h, add_zero]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Left antipode axiom** (after the tensor comparison, `m ∘ (S ⊗ id) ∘ Δ`
is pullback along `a ↦ (-a) + a = 0`, the unit of the convolution; pointwise,
`h (-z + z) = h 0`). -/
theorem galois_mul_antipode_rTensor_comulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (Algebra.TensorProduct.lift (galoisAntipodeHom L ρ)
      (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ)) fun _ => Commute.all _).comp
      (galoisComulHom L ρ hbij) =
    (Algebra.ofId K₀ (galoisEquivariantAlgebra L ρ)).comp
      (galoisCounitHom L ρ) := by
  classical
  apply AlgHom.ext
  intro h
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        (fun _ _ => Commute.all _ _) (galoisComulHom L ρ hbij t)
      = (t : A → L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galois_lift_evalL_comp_comulHom L ρ hbij x y) t
  have hval : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      ((Algebra.TensorProduct.lift (galoisAntipodeHom L ρ)
        (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ)) fun _ => Commute.all _) u
        : A → L) z
      = Algebra.TensorProduct.lift (galoisEvalL L ρ (-z)) (galoisEvalL L ρ z)
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq]
      rw [MulMemClass.coe_mul, Pi.mul_apply]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  show ((Algebra.TensorProduct.lift (galoisAntipodeHom L ρ)
      (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ)) fun _ => Commute.all _)
      (galoisComulHom L ρ hbij h) : A → L) z
    = ((Algebra.ofId K₀ (galoisEquivariantAlgebra L ρ))
      (galoisCounitHom L ρ h) : A → L) z
  rw [hval (galoisComulHom L ρ hbij h), hΔ (-z) z h, neg_add_cancel]
  exact (galoisCounitHom_algebraMap L ρ h).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Right antipode axiom** (symmetric to the left axiom: pointwise,
`h (z + -z) = h 0`). -/
theorem galois_mul_antipode_lTensor_comulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    (Algebra.TensorProduct.lift (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
      (galoisAntipodeHom L ρ) fun _ _ => Commute.all _ _).comp
      (galoisComulHom L ρ hbij) =
    (Algebra.ofId K₀ (galoisEquivariantAlgebra L ρ)).comp
      (galoisCounitHom L ρ) := by
  classical
  apply AlgHom.ext
  intro h
  apply Subtype.ext
  funext z
  have hΔ : ∀ (x y : A) (t : galoisEquivariantAlgebra L ρ),
      Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
        (fun _ _ => Commute.all _ _) (galoisComulHom L ρ hbij t)
      = (t : A → L) (x + y) := by
    intro x y t
    exact DFunLike.congr_fun (galois_lift_evalL_comp_comulHom L ρ hbij x y) t
  have hval : ∀ u : (galoisEquivariantAlgebra L ρ) ⊗[K₀]
      (galoisEquivariantAlgebra L ρ),
      ((Algebra.TensorProduct.lift (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
        (galoisAntipodeHom L ρ) fun _ _ => Commute.all _ _) u : A → L) z
      = Algebra.TensorProduct.lift (galoisEvalL L ρ z) (galoisEvalL L ρ (-z))
          (fun _ _ => Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq]
      rw [MulMemClass.coe_mul, Pi.mul_apply]
      rfl
    | add u₁ u₂ ih₁ ih₂ => simp [map_add, ih₁, ih₂]
  show ((Algebra.TensorProduct.lift (AlgHom.id K₀ (galoisEquivariantAlgebra L ρ))
      (galoisAntipodeHom L ρ) fun _ _ => Commute.all _ _)
      (galoisComulHom L ρ hbij h) : A → L) z
    = ((Algebra.ofId K₀ (galoisEquivariantAlgebra L ρ))
      (galoisCounitHom L ρ h) : A → L) z
  rw [hval (galoisComulHom L ρ hbij h), hΔ z (-z) h, add_neg_cancel]
  exact (galoisCounitHom_algebraMap L ρ h).symm

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- **The `Ω`-valued evaluations compose with the comultiplication as addition
of the evaluation points** (the `Ω`-upgrade of
`galois_lift_evalL_comp_comulHom`, feeding the convolution identity of the
Hopf package): `(ev_x ⊗ ev_y) ∘ Δ = ev_{x+y}` for the evaluations into `Ω`. -/
theorem galois_lift_eval_comp_comulHom
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) (x y : A) :
    (Algebra.TensorProduct.lift (galoisEquivariantEval L ρ x)
        (galoisEquivariantEval L ρ y)
        fun _ _ => Commute.all _ _).comp (galoisComulHom L ρ hbij)
      = galoisEquivariantEval L ρ (x + y) := by
  have h5 : Algebra.TensorProduct.lift (galoisEquivariantEval L ρ x)
      (galoisEquivariantEval L ρ y) (fun _ _ => Commute.all _ _)
      = (IsScalarTower.toAlgHom K₀ (↥L) Ω).comp
          (Algebra.TensorProduct.lift (galoisEvalL L ρ x) (galoisEvalL L ρ y)
            fun _ _ => Commute.all _ _) :=
    (galois_comp_lift (IsScalarTower.toAlgHom K₀ (↥L) Ω)
      (galoisEvalL L ρ x) (galoisEvalL L ρ y)).symm
  rw [h5, AlgHom.comp_assoc, galois_lift_evalL_comp_comulHom]
  exact AlgHom.ext fun h => rfl

/-- **A structureless copy of the equivariant-functions algebra**, used as the
carrier of its Hopf-algebra structure in `exists_hopfAlgebra_galoisHopfCarrier`: a
type synonym deliberately carrying NO instances, so that the Hopf-algebra package —
whose convolution structure is keyed to the Bialgebra-derived algebra instance of its
carrier, incompatible with any pre-existing canonical instance — can bind all its
instances existentially without a diamond. -/
def GaloisHopfCarrier : Type _ := galoisEquivariantAlgebra L ρ

section HopfCopy

/-! ##### Hopf-algebra transport along an algebra equivalence

The conjugation core of `exists_hopfAlgebra_small_copy` below, factored
2026-07-23 for reuse by the Hopf-carrier package leaf (pure transfer of
structure, curve-free and Galois-free): given a Hopf algebra `B` over `K₁` and
an algebra equivalence `ê : C ≃ₐ[K₁] B` from a commutative algebra `C`, the
algebra `C` carries a `K₁`-Hopf-algebra structure over its GIVEN ring and
algebra instances (`hopfAlgebraCopyOfAlgEquiv`). The comultiplication is
`(ê⁻¹ ⊗ ê⁻¹) ∘ Δ_B ∘ ê`, counit `ε_B ∘ ê`, antipode `ê⁻¹ ∘ S_B ∘ ê`; the
coalgebra axioms are the axioms of `B` conjugated by `ê`, checked at the
linear level after cancelling along the surjection `ê.symm` (the
`coassoc_simps` normalization set does the tensor bookkeeping); the antipode
axioms are conjugated at the algebra-homomorphism level. Everything is a
top-level term-mode definition rather than a `letI` inside one proof so that
the resulting instance stays TRANSPARENT: consumers must identify
`(hopfAlgebraCopyOfAlgEquiv ê).toAlgebra` with the ambient algebra instance
by unfolding, which an opaque existential would forbid. -/

variable {K₁ : Type*} [CommSemiring K₁]
variable {B C : Type*} [CommRing B] [HopfAlgebra K₁ B] [CommRing C] [Algebra K₁ C]

/-- The transported comultiplication `(ê⁻¹ ⊗ ê⁻¹) ∘ Δ_B ∘ ê`. -/
noncomputable def hopfCopyComul (ê : C ≃ₐ[K₁] B) : C →ₐ[K₁] C ⊗[K₁] C :=
  (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
    ((Bialgebra.comulAlgHom K₁ B).comp ê.toAlgHom)

/-- The transported counit `ε_B ∘ ê`. -/
noncomputable def hopfCopyCounit (ê : C ≃ₐ[K₁] B) : C →ₐ[K₁] K₁ :=
  (Bialgebra.counitAlgHom K₁ B).comp ê.toAlgHom

/-- The transported antipode `ê⁻¹ ∘ S_B ∘ ê`. -/
noncomputable def hopfCopyAntipode (ê : C ≃ₐ[K₁] B) : C →ₐ[K₁] C :=
  ê.symm.toAlgHom.comp ((HopfAlgebra.antipodeAlgHom K₁ B).comp ê.toAlgHom)

/-- The transported comultiplication precomposed with `ê.symm`, at the linear
level (the workhorse cancellation identity). -/
theorem hopfCopyComul_toLinearMap_comp (ê : C ≃ₐ[K₁] B) :
    (hopfCopyComul ê).toLinearMap ∘ₗ ê.symm.toLinearMap =
      TensorProduct.map ê.symm.toLinearMap ê.symm.toLinearMap ∘ₗ
        Coalgebra.comul := by
  have hmm' : ê.toLinearMap ∘ₗ ê.symm.toLinearMap = LinearMap.id := by
    ext x; simp
  simp only [hopfCopyComul, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
    Bialgebra.toLinearMap_comulAlgHom, LinearMap.comp_assoc, hmm',
    LinearMap.comp_id]

/-- The transported counit precomposed with `ê.symm`, at the linear level. -/
theorem hopfCopyCounit_toLinearMap_comp (ê : C ≃ₐ[K₁] B) :
    (hopfCopyCounit ê).toLinearMap ∘ₗ ê.symm.toLinearMap = Coalgebra.counit := by
  have hmm' : ê.toLinearMap ∘ₗ ê.symm.toLinearMap = LinearMap.id := by
    ext x; simp
  simp only [hopfCopyCounit, AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
    Bialgebra.toLinearMap_counitAlgHom, LinearMap.comp_assoc, hmm',
    LinearMap.comp_id]

/-- Coassociativity of the transported comultiplication. -/
theorem hopfCopyComul_coassoc (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.assoc K₁ K₁ K₁ C C C).toAlgHom.comp
      ((Algebra.TensorProduct.map (hopfCopyComul ê) (AlgHom.id K₁ C)).comp
        (hopfCopyComul ê)) =
    (Algebra.TensorProduct.map (AlgHom.id K₁ C) (hopfCopyComul ê)).comp
      (hopfCopyComul ê) := by
  apply AlgHom.toLinearMap_injective
  refine (LinearMap.cancel_right
    (show Function.Surjective ê.symm.toLinearMap from ê.symm.surjective)).mp ?_
  simp only [coassoc_simps, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
    AlgEquiv.toAlgHom_toLinearMap, Algebra.TensorProduct.assoc_toLinearEquiv,
    hopfCopyComul_toLinearMap_comp]

/-- Left counit axiom for the transported comultiplication. -/
theorem hopfCopyComul_rTensor_counit (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.map (hopfCopyCounit ê) (AlgHom.id K₁ C)).comp
      (hopfCopyComul ê) =
      ((Algebra.TensorProduct.lid K₁ C).symm : C →ₐ[K₁] K₁ ⊗[K₁] C) := by
  apply AlgHom.toLinearMap_injective
  refine (LinearMap.cancel_right
    (show Function.Surjective ê.symm.toLinearMap from ê.symm.surjective)).mp ?_
  simp only [coassoc_simps, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
    AlgEquiv.toAlgHom_toLinearMap, hopfCopyComul_toLinearMap_comp,
    hopfCopyCounit_toLinearMap_comp]
  rw [CoassocSimps.map_counit_comp_comul_left]
  rfl

/-- Right counit axiom for the transported comultiplication. -/
theorem hopfCopyComul_lTensor_counit (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.map (AlgHom.id K₁ C) (hopfCopyCounit ê)).comp
      (hopfCopyComul ê) =
      ((Algebra.TensorProduct.rid K₁ K₁ C).symm : C →ₐ[K₁] C ⊗[K₁] K₁) := by
  apply AlgHom.toLinearMap_injective
  refine (LinearMap.cancel_right
    (show Function.Surjective ê.symm.toLinearMap from ê.symm.surjective)).mp ?_
  simp only [coassoc_simps, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
    AlgEquiv.toAlgHom_toLinearMap, hopfCopyComul_toLinearMap_comp,
    hopfCopyCounit_toLinearMap_comp]
  rw [CoassocSimps.map_counit_comp_comul_right]
  rfl

/-- The transported comultiplication precomposed with `ê.symm`, at the
algebra-homomorphism level. -/
theorem hopfCopyComul_comp_symm (ê : C ≃ₐ[K₁] B) :
    (hopfCopyComul ê).comp ê.symm.toAlgHom =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Bialgebra.comulAlgHom K₁ B) := by
  apply AlgHom.ext
  intro b
  show (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom)
      (Bialgebra.comulAlgHom K₁ B (ê (ê.symm b))) = _
  rw [ê.apply_symm_apply]
  rfl

/-- The transported antipode precomposed with `ê.symm`. -/
theorem hopfCopyAntipode_comp_symm (ê : C ≃ₐ[K₁] B) :
    (hopfCopyAntipode ê).comp ê.symm.toAlgHom =
      ê.symm.toAlgHom.comp (HopfAlgebra.antipodeAlgHom K₁ B) := by
  apply AlgHom.ext
  intro b
  show ê.symm (HopfAlgebra.antipodeAlgHom K₁ B (ê (ê.symm b))) = _
  rw [ê.apply_symm_apply]
  rfl

/-- The transported counit precomposed with `ê.symm`. -/
theorem hopfCopyCounit_comp_symm (ê : C ≃ₐ[K₁] B) :
    (hopfCopyCounit ê).comp ê.symm.toAlgHom = Bialgebra.counitAlgHom K₁ B := by
  apply AlgHom.ext
  intro b
  show Bialgebra.counitAlgHom K₁ B (ê (ê.symm b)) = _
  rw [ê.apply_symm_apply]

/-- Multiplicativity of the copy inverse against the tensor multiplication. -/
theorem hopfCopy_lmul'_comp_map (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.lmul' K₁ (S := C)).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      ê.symm.toAlgHom.comp (Algebra.TensorProduct.lmul' K₁) := by
  ext <;> simp

set_option maxHeartbeats 1000000 in
/-- The left antipode axiom of `B`, in `lmul' ∘ map` algebra-homomorphism
form. -/
theorem hopf_mul_antipode_rTensor_comul_algHom :
    (Algebra.TensorProduct.lmul' K₁ (S := B)).comp
      ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom K₁ B)
        (AlgHom.id K₁ B)).comp (Bialgebra.comulAlgHom K₁ B)) =
      (Algebra.ofId K₁ B).comp (Bialgebra.counitAlgHom K₁ B) := by
  apply AlgHom.toLinearMap_injective
  simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq,
    HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_id,
    Bialgebra.toLinearMap_comulAlgHom, Bialgebra.toLinearMap_counitAlgHom]
  rw [← LinearMap.rTensor_def]
  exact HopfAlgebra.mul_antipode_rTensor_comul

set_option maxHeartbeats 1000000 in
/-- The right antipode axiom of `B`, in `lmul' ∘ map` algebra-homomorphism
form. -/
theorem hopf_mul_antipode_lTensor_comul_algHom :
    (Algebra.TensorProduct.lmul' K₁ (S := B)).comp
      ((Algebra.TensorProduct.map (AlgHom.id K₁ B)
        (HopfAlgebra.antipodeAlgHom K₁ B)).comp (Bialgebra.comulAlgHom K₁ B)) =
      (Algebra.ofId K₁ B).comp (Bialgebra.counitAlgHom K₁ B) := by
  apply AlgHom.toLinearMap_injective
  simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq,
    HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_id,
    Bialgebra.toLinearMap_comulAlgHom, Bialgebra.toLinearMap_counitAlgHom]
  rw [← LinearMap.lTensor_def]
  exact HopfAlgebra.mul_antipode_lTensor_comul

set_option maxHeartbeats 1000000 in
/-- The left antipode axiom for the transported structure maps, by
conjugation. -/
theorem hopfCopy_mul_antipode_rTensor (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.lift (hopfCopyAntipode ê) (AlgHom.id K₁ C)
      fun _ => Commute.all _).comp (hopfCopyComul ê) =
    (Algebra.ofId K₁ C).comp (hopfCopyCounit ê) := by
  have hmapS : (Algebra.TensorProduct.map (hopfCopyAntipode ê)
      (AlgHom.id K₁ C)).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom K₁ B)
          (AlgHom.id K₁ B)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      hopfCopyAntipode_comp_symm, AlgHom.comp_id, AlgHom.id_comp]
  rw [← Algebra.TensorProduct.lmul'_comp_map]
  refine (AlgHom.cancel_right (f := ê.symm.toAlgHom)
    (show Function.Surjective ⇑ê.symm.toAlgHom from ê.symm.surjective)).mp ?_
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hopfCopyComul_comp_symm,
    ← AlgHom.comp_assoc _ _ (Bialgebra.comulAlgHom K₁ B), hmapS,
    AlgHom.comp_assoc _ _ (Bialgebra.comulAlgHom K₁ B), ← AlgHom.comp_assoc,
    hopfCopy_lmul'_comp_map, AlgHom.comp_assoc,
    hopf_mul_antipode_rTensor_comul_algHom, AlgHom.comp_assoc,
    hopfCopyCounit_comp_symm]
  apply AlgHom.ext
  intro b
  show ê.symm (algebraMap K₁ B (Bialgebra.counitAlgHom K₁ B b)) = _
  rw [AlgEquiv.commutes]
  rfl

set_option maxHeartbeats 1000000 in
/-- The right antipode axiom for the transported structure maps, by
conjugation. -/
theorem hopfCopy_mul_antipode_lTensor (ê : C ≃ₐ[K₁] B) :
    (Algebra.TensorProduct.lift (AlgHom.id K₁ C) (hopfCopyAntipode ê)
      fun _ _ => Commute.all _ _).comp (hopfCopyComul ê) =
    (Algebra.ofId K₁ C).comp (hopfCopyCounit ê) := by
  have hmapS' : (Algebra.TensorProduct.map (AlgHom.id K₁ C)
      (hopfCopyAntipode ê)).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Algebra.TensorProduct.map (AlgHom.id K₁ B)
          (HopfAlgebra.antipodeAlgHom K₁ B)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      hopfCopyAntipode_comp_symm, AlgHom.comp_id, AlgHom.id_comp]
  rw [← Algebra.TensorProduct.lmul'_comp_map]
  refine (AlgHom.cancel_right (f := ê.symm.toAlgHom)
    (show Function.Surjective ⇑ê.symm.toAlgHom from ê.symm.surjective)).mp ?_
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hopfCopyComul_comp_symm,
    ← AlgHom.comp_assoc _ _ (Bialgebra.comulAlgHom K₁ B), hmapS',
    AlgHom.comp_assoc _ _ (Bialgebra.comulAlgHom K₁ B), ← AlgHom.comp_assoc,
    hopfCopy_lmul'_comp_map, AlgHom.comp_assoc,
    hopf_mul_antipode_lTensor_comul_algHom, AlgHom.comp_assoc,
    hopfCopyCounit_comp_symm]
  apply AlgHom.ext
  intro b
  show ê.symm (algebraMap K₁ B (Bialgebra.counitAlgHom K₁ B b)) = _
  rw [AlgEquiv.commutes]
  rfl

/-- The transported bialgebra structure. -/
@[reducible] noncomputable def hopfCopyBialgebra (ê : C ≃ₐ[K₁] B) : Bialgebra K₁ C :=
  Bialgebra.ofAlgHom (hopfCopyComul ê) (hopfCopyCounit ê)
    (hopfCopyComul_coassoc ê) (hopfCopyComul_rTensor_counit ê)
    (hopfCopyComul_lTensor_counit ê)

/-- **The transported Hopf-algebra structure** — the conjugation core, as a
TRANSPARENT definition (consumers identify its `toAlgebra` with the ambient
algebra instance by unfolding). -/
@[reducible] noncomputable def hopfAlgebraCopyOfAlgEquiv (ê : C ≃ₐ[K₁] B) :
    HopfAlgebra K₁ C :=
  letI instBi : Bialgebra K₁ C := hopfCopyBialgebra ê
  HopfAlgebra.ofAlgHom (hopfCopyAntipode ê)
    (by rw [show Bialgebra.comulAlgHom K₁ C = hopfCopyComul ê from
              AlgHom.toLinearMap_injective rfl,
            show Bialgebra.counitAlgHom K₁ C = hopfCopyCounit ê from
              AlgHom.toLinearMap_injective rfl]
        exact hopfCopy_mul_antipode_rTensor ê)
    (by rw [show Bialgebra.comulAlgHom K₁ C = hopfCopyComul ê from
              AlgHom.toLinearMap_injective rfl,
            show Bialgebra.counitAlgHom K₁ C = hopfCopyCounit ê from
              AlgHom.toLinearMap_injective rfl]
        exact hopfCopy_mul_antipode_lTensor ê)

end HopfCopy

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- The canonical commutative ring structure of the structureless carrier,
transported along the definitional equality of the type synonym (a TOP-LEVEL
definition — transporting inside a proof via `letI` produces hoisted auxiliary
definitions the kernel rejects). -/
@[reducible] noncomputable def galoisHopfCarrierCommRing :
    CommRing (GaloisHopfCarrier L ρ) :=
  inferInstanceAs (CommRing (galoisEquivariantAlgebra L ρ))

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- The canonical algebra structure of the structureless carrier, over the
transported ring structure. -/
@[reducible] noncomputable def galoisHopfCarrierAlgebra :
    @Algebra K₀ (GaloisHopfCarrier L ρ) _ (galoisHopfCarrierCommRing L ρ).toSemiring :=
  inferInstanceAs (Algebra K₀ (galoisEquivariantAlgebra L ρ))

omit [FiniteDimensional K₀ ↥L] [IsGalois K₀ ↥L] in
/-- The identity algebra equivalence between the structureless carrier (with
its transported instances) and the equivariant-functions algebra. -/
noncomputable def galoisHopfCarrierAlgEquiv : by
    letI := galoisHopfCarrierCommRing L ρ
    letI := galoisHopfCarrierAlgebra L ρ
    exact GaloisHopfCarrier L ρ ≃ₐ[K₀] galoisEquivariantAlgebra L ρ := by
  letI := galoisHopfCarrierCommRing L ρ
  letI := galoisHopfCarrierAlgebra L ρ
  exact { toFun := fun x => x
          invFun := fun x => x
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl
          map_add' := fun _ _ => rfl
          commutes' := fun _ => rfl }

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Hopf-algebra package given the tensor-comparison isomorphism** (sorry
node; the construction-and-axioms core of the package, isolated 2026-07-23 —
the comparison data and the assembly are built outside): granted bijectivity
of the tensor-comparison homomorphism, the structureless copy
`GaloisHopfCarrier L ρ` of the equivariant-functions algebra carries a
`K₀`-Hopf-algebra structure together with an algebra equivalence `e` to the
equivariant-functions algebra for which the convolution product of evaluation
points is the evaluation at the sum. Intended proof: transfer the commutative
ring and algebra structure of `galoisEquivariantAlgebra L ρ` along the
definitional equality of the type synonym (so `e` is the identity equivalence);
the comultiplication is `(comparison)⁻¹ ∘ (pullback of the addition)`
(`galoisEquivariantPullback` along `AddMonoidHom.coprod id id`, then
`AlgEquiv.ofBijective _ hbij |>.symm`), the counit is evaluation at `0 : A`
(landing in the bottom fixed field `K₀` since `0` is `ρ`-fixed —
`IsGalois.mem_range_algebraMap_iff_fixed` as in the parallel `galDescCounit`),
and the antipode is the pullback of negation; the coalgebra and antipode
axioms hold after composing with the injective comparison maps, where all
sides become pullbacks along the corresponding additive maps
(`(a,b,c) ↦ a+b+c` for coassociativity, `a ↦ (-a)+a = 0` for the antipode);
the convolution identity is the computation
`(eval a ⊛ eval b) f = (eval a ⊗ eval b) (Δ f) = f (a + b)` holding by
construction of `Δ`. -/
theorem exists_hopfAlgebra_galoisHopfCarrier_of_tensorHom_bijective [Finite A]
    (hbij : Function.Bijective (galoisEquivariantTensorHom L ρ ρ)) :
    ∃ (_ : CommRing (GaloisHopfCarrier L ρ))
      (_ : HopfAlgebra K₀ (GaloisHopfCarrier L ρ))
      (e : GaloisHopfCarrier L ρ ≃ₐ[K₀] galoisEquivariantAlgebra L ρ),
      ∀ a b : A,
        WithConv.toConv ((galoisEquivariantEval L ρ a).comp e.toAlgHom) *
          WithConv.toConv ((galoisEquivariantEval L ρ b).comp e.toAlgHom) =
        WithConv.toConv ((galoisEquivariantEval L ρ (a + b)).comp e.toAlgHom) := by
  classical
  -- the Hopf structure on the equivariant-functions algebra itself, over its
  -- canonical instances (a mixin — no instance mixing): comultiplication
  -- through the comparison inverse, counit by evaluation at `0`, antipode by
  -- pullback of negation
  letI instBiH : Bialgebra K₀ (galoisEquivariantAlgebra L ρ) :=
    Bialgebra.ofAlgHom (galoisComulHom L ρ hbij) (galoisCounitHom L ρ)
      (galoisComulHom_coassoc L ρ hbij)
      (galoisComulHom_rTensor_counit L ρ hbij)
      (galoisComulHom_lTensor_counit L ρ hbij)
  have hcomulH : Bialgebra.comulAlgHom K₀ (galoisEquivariantAlgebra L ρ)
      = galoisComulHom L ρ hbij := AlgHom.toLinearMap_injective rfl
  have hcounitH : Bialgebra.counitAlgHom K₀ (galoisEquivariantAlgebra L ρ)
      = galoisCounitHom L ρ := AlgHom.toLinearMap_injective rfl
  letI instHopfH : HopfAlgebra K₀ (galoisEquivariantAlgebra L ρ) :=
    HopfAlgebra.ofAlgHom (galoisAntipodeHom L ρ)
      (by rw [hcomulH, hcounitH]
          exact galois_mul_antipode_rTensor_comulHom L ρ hbij)
      (by rw [hcomulH, hcounitH]
          exact galois_mul_antipode_lTensor_comulHom L ρ hbij)
  -- the transported instances and the identity equivalence on the carrier
  letI instCR := galoisHopfCarrierCommRing L ρ
  letI instAlg := galoisHopfCarrierAlgebra L ρ
  letI instHopf : HopfAlgebra K₀ (GaloisHopfCarrier L ρ) :=
    hopfAlgebraCopyOfAlgEquiv (galoisHopfCarrierAlgEquiv L ρ)
  refine ⟨instCR, instHopf, galoisHopfCarrierAlgEquiv L ρ, ?_⟩
  intro a b
  -- unfold the convolution product and reduce along the conjugated
  -- comultiplication to `(ev_a ⊗ ev_b) ∘ Δ = ev_{a+b}` on the algebra itself
  rw [AlgHom.convMul_def]
  refine congrArg WithConv.toConv ?_
  have hΔGhc : Bialgebra.comulAlgHom K₀ (GaloisHopfCarrier L ρ)
      = hopfCopyComul (galoisHopfCarrierAlgEquiv L ρ) :=
    AlgHom.toLinearMap_injective rfl
  have hcc : hopfCopyComul (galoisHopfCarrierAlgEquiv L ρ)
      = (Algebra.TensorProduct.map
          (galoisHopfCarrierAlgEquiv L ρ).symm.toAlgHom
          (galoisHopfCarrierAlgEquiv L ρ).symm.toAlgHom).comp
        ((Bialgebra.comulAlgHom K₀ (galoisEquivariantAlgebra L ρ)).comp
          (galoisHopfCarrierAlgEquiv L ρ).toAlgHom) := rfl
  rw [hΔGhc, hcc, hcomulH]
  apply AlgHom.ext
  intro h
  have h1 := DFunLike.congr_fun (galois_lift_eval_comp_comulHom L ρ hbij a b)
    (galoisHopfCarrierAlgEquiv L ρ h)
  simp only [AlgHom.coe_comp, Function.comp_apply] at h1
  -- pointwise: fuse the two `map`s and cancel `ê ∘ ê.symm`
  show (Algebra.TensorProduct.lmul' K₀)
      ((Algebra.TensorProduct.map
        ((galoisEquivariantEval L ρ a).comp
          (galoisHopfCarrierAlgEquiv L ρ).toAlgHom)
        ((galoisEquivariantEval L ρ b).comp
          (galoisHopfCarrierAlgEquiv L ρ).toAlgHom))
        ((Algebra.TensorProduct.map
          (galoisHopfCarrierAlgEquiv L ρ).symm.toAlgHom
          (galoisHopfCarrierAlgEquiv L ρ).symm.toAlgHom)
          (galoisComulHom L ρ hbij (galoisHopfCarrierAlgEquiv L ρ h))))
    = galoisEquivariantEval L ρ (a + b) (galoisHopfCarrierAlgEquiv L ρ h)
  rw [← h1]
  generalize galoisComulHom L ρ hbij (galoisHopfCarrierAlgEquiv L ρ h) = u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    simp only [Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [(galoisHopfCarrierAlgEquiv L ρ).apply_symm_apply,
      (galoisHopfCarrierAlgEquiv L ρ).apply_symm_apply]
  | add u₁ u₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- **The Hopf-algebra package on the canonical-universe carrier** (DECOMPOSED
2026-07-23 into the Galois-descent core `galoisEquivariantTensorHom_bijective`
— the tensor square of the equivariant-functions algebra is the equivariant
functions on `A × A` — and the construction-and-axioms core
`exists_hopfAlgebra_galoisHopfCarrier_of_tensorHom_bijective`; the comparison
data — diagonal action, equivariant pullbacks, comparison homomorphism — and
the assembly below are PROVEN): the structureless copy `GaloisHopfCarrier L ρ`
of the equivariant-functions algebra carries a `K₀`-Hopf-algebra structure
together with an algebra equivalence `e` to the equivariant-functions algebra
for which the convolution product of evaluation points is the evaluation at
the sum. -/
theorem exists_hopfAlgebra_galoisHopfCarrier [Finite A] :
    ∃ (_ : CommRing (GaloisHopfCarrier L ρ))
      (_ : HopfAlgebra K₀ (GaloisHopfCarrier L ρ))
      (e : GaloisHopfCarrier L ρ ≃ₐ[K₀] galoisEquivariantAlgebra L ρ),
      ∀ a b : A,
        WithConv.toConv ((galoisEquivariantEval L ρ a).comp e.toAlgHom) *
          WithConv.toConv ((galoisEquivariantEval L ρ b).comp e.toAlgHom) =
        WithConv.toConv ((galoisEquivariantEval L ρ (a + b)).comp e.toAlgHom) :=
  exists_hopfAlgebra_galoisHopfCarrier_of_tensorHom_bijective L ρ
    (galoisEquivariantTensorHom_bijective L ρ ρ)

universe v in
/-- **Hopf algebras have Hopf-algebra copies in every admissible universe** (PROVEN
2026-07-23; pure transfer of structure, curve-free and Galois-free — the universe
half of the equivariant-functions package): a Hopf algebra `B` over `K₁` that is
`v`-small as a type admits a `Type v` copy: a commutative ring `C` in `Type v` with
a `K₁`-Hopf-algebra structure, an algebra equivalence `ê : C ≃ₐ[K₁] B`, and a
bialgebra homomorphism `êc` witnessing that `ê` respects the comultiplications.
Proof: `C := Shrink.{v} B` with the ring and algebra structure transported along
`equivShrink` (`Shrink.instCommRing`, `Shrink.instAlgebra`, `Shrink.algEquiv`),
the comultiplication `(ê⁻¹ ⊗ ê⁻¹) ∘ Δ_B ∘ ê`, counit `ε_B ∘ ê`, antipode
`ê⁻¹ ∘ S_B ∘ ê` (all through `Bialgebra.ofAlgHom`/`HopfAlgebra.ofAlgHom`); the
coalgebra axioms are the axioms of `B` conjugated by `ê`, checked at the linear
level after cancelling along the surjection `ê.symm` (the `coassoc_simps`
normalization set does the tensor bookkeeping); the antipode axioms are conjugated
at the algebra-homomorphism level (`HopfAlgebra.antipodeAlgHom`,
`mul_antipode_rTensor_comul`/`lTensor`); the bialgebra-homomorphism property of
`ê` holds by construction. -/
theorem exists_hopfAlgebra_small_copy {K₁ : Type*} [CommSemiring K₁]
    {B : Type*} [CommRing B] [HopfAlgebra K₁ B] [Small.{v} B] :
    ∃ (C : Type v) (_ : CommRing C) (_ : HopfAlgebra K₁ C) (ê : C ≃ₐ[K₁] B)
      (êc : C →ₐc[K₁] B), (êc : C →ₐ[K₁] B) = ê.toAlgHom := by
  classical
  -- the `Type v` copy with its transported ring and algebra structure
  let ê : Shrink.{v} B ≃ₐ[K₁] B := Shrink.algEquiv K₁ B
  -- the transported comultiplication, counit and antipode, as algebra maps
  let Δ : Shrink.{v} B →ₐ[K₁] Shrink.{v} B ⊗[K₁] Shrink.{v} B :=
    (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
      ((Bialgebra.comulAlgHom K₁ B).comp ê.toAlgHom)
  let ε : Shrink.{v} B →ₐ[K₁] K₁ :=
    (Bialgebra.counitAlgHom K₁ B).comp ê.toAlgHom
  let S : Shrink.{v} B →ₐ[K₁] Shrink.{v} B :=
    ê.symm.toAlgHom.comp ((HopfAlgebra.antipodeAlgHom K₁ B).comp ê.toAlgHom)
  -- cancellation identities for the two directions of the copy equivalence
  have hmm' : ê.toLinearMap ∘ₗ ê.symm.toLinearMap = LinearMap.id := by
    ext x; simp
  -- the structure maps, precomposed with the (surjective) inverse direction
  have hΔ : Δ.toLinearMap ∘ₗ ê.symm.toLinearMap =
      TensorProduct.map ê.symm.toLinearMap ê.symm.toLinearMap ∘ₗ
        Coalgebra.comul := by
    simp only [Δ, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq, AlgEquiv.toAlgHom_toLinearMap,
      Bialgebra.toLinearMap_comulAlgHom, LinearMap.comp_assoc, hmm',
      LinearMap.comp_id]
  have hε : ε.toLinearMap ∘ₗ ê.symm.toLinearMap = Coalgebra.counit := by
    simp only [ε, AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
      Bialgebra.toLinearMap_counitAlgHom, LinearMap.comp_assoc, hmm',
      LinearMap.comp_id]
  -- the coalgebra axioms, conjugated: reduce along the surjection `ê.symm`
  have hsurj : Function.Surjective ê.symm.toLinearMap := ê.symm.surjective
  have h_coassoc :
      (Algebra.TensorProduct.assoc K₁ K₁ K₁ (Shrink.{v} B) (Shrink.{v} B)
          (Shrink.{v} B)).toAlgHom.comp
        ((Algebra.TensorProduct.map Δ (AlgHom.id K₁ (Shrink.{v} B))).comp Δ) =
      (Algebra.TensorProduct.map (AlgHom.id K₁ (Shrink.{v} B)) Δ).comp Δ := by
    apply AlgHom.toLinearMap_injective
    refine (LinearMap.cancel_right hsurj).mp ?_
    simp only [coassoc_simps, AlgHom.comp_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
      AlgEquiv.toAlgHom_toLinearMap, Algebra.TensorProduct.assoc_toLinearEquiv,
      hΔ]
  have h_rTensor :
      (Algebra.TensorProduct.map ε (AlgHom.id K₁ (Shrink.{v} B))).comp Δ =
        ((Algebra.TensorProduct.lid K₁ (Shrink.{v} B)).symm :
          Shrink.{v} B →ₐ[K₁] K₁ ⊗[K₁] Shrink.{v} B) := by
    apply AlgHom.toLinearMap_injective
    refine (LinearMap.cancel_right hsurj).mp ?_
    simp only [coassoc_simps, AlgHom.comp_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
      AlgEquiv.toAlgHom_toLinearMap, hΔ, hε]
    rw [CoassocSimps.map_counit_comp_comul_left]
    rfl
  have h_lTensor :
      (Algebra.TensorProduct.map (AlgHom.id K₁ (Shrink.{v} B)) ε).comp Δ =
        ((Algebra.TensorProduct.rid K₁ K₁ (Shrink.{v} B)).symm :
          Shrink.{v} B →ₐ[K₁] Shrink.{v} B ⊗[K₁] K₁) := by
    apply AlgHom.toLinearMap_injective
    refine (LinearMap.cancel_right hsurj).mp ?_
    simp only [coassoc_simps, AlgHom.comp_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map, AlgHom.toLinearMap_id,
      AlgEquiv.toAlgHom_toLinearMap, hΔ, hε]
    rw [CoassocSimps.map_counit_comp_comul_right]
    rfl
  letI instBi : Bialgebra K₁ (Shrink.{v} B) :=
    Bialgebra.ofAlgHom Δ ε h_coassoc h_rTensor h_lTensor
  -- the structure maps of the new instance are the transported ones
  have hcomul_new : Bialgebra.comulAlgHom K₁ (Shrink.{v} B) = Δ :=
    AlgHom.toLinearMap_injective rfl
  have hcounit_new : Bialgebra.counitAlgHom K₁ (Shrink.{v} B) = ε :=
    AlgHom.toLinearMap_injective rfl
  -- multiplicativity of the copy inverse against the tensor multiplication
  have hmul : (Algebra.TensorProduct.lmul' K₁ (S := Shrink.{v} B)).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      ê.symm.toAlgHom.comp (Algebra.TensorProduct.lmul' K₁) := by
    ext <;> simp
  -- the structure maps, conjugated at the algebra-homomorphism level
  have hΔa : Δ.comp ê.symm.toAlgHom =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Bialgebra.comulAlgHom K₁ B) :=
    AlgHom.toLinearMap_injective (by
      simpa only [AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
        Bialgebra.toLinearMap_comulAlgHom, Algebra.TensorProduct.toLinearMap_map,
        TensorProduct.AlgebraTensorModule.map_eq] using hΔ)
  have hSa : S.comp ê.symm.toAlgHom =
      ê.symm.toAlgHom.comp (HopfAlgebra.antipodeAlgHom K₁ B) := by
    apply AlgHom.ext
    intro b
    show ê.symm (HopfAlgebra.antipodeAlgHom K₁ B (ê (ê.symm b))) = _
    rw [ê.apply_symm_apply]
    rfl
  have hεa : ε.comp ê.symm.toAlgHom = Bialgebra.counitAlgHom K₁ B := by
    apply AlgHom.ext
    intro b
    show Bialgebra.counitAlgHom K₁ B (ê (ê.symm b)) = _
    rw [ê.apply_symm_apply]
  -- the two `map` conjugation identities for the antipode legs
  have hmapS : (Algebra.TensorProduct.map S (AlgHom.id K₁ (Shrink.{v} B))).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom K₁ B)
          (AlgHom.id K₁ B)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hSa,
      AlgHom.comp_id, AlgHom.id_comp]
  have hmapS' : (Algebra.TensorProduct.map (AlgHom.id K₁ (Shrink.{v} B)) S).comp
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
      (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
        (Algebra.TensorProduct.map (AlgHom.id K₁ B)
          (HopfAlgebra.antipodeAlgHom K₁ B)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp, hSa,
      AlgHom.comp_id, AlgHom.id_comp]
  -- the antipode axioms of `B`, in `lmul' ∘ map` form
  have hB1 : (Algebra.TensorProduct.lmul' K₁ (S := B)).comp
      ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom K₁ B)
        (AlgHom.id K₁ B)).comp (Bialgebra.comulAlgHom K₁ B)) =
      (Algebra.ofId K₁ B).comp (Bialgebra.counitAlgHom K₁ B) := by
    apply AlgHom.toLinearMap_injective
    simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq,
      HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_id,
      Bialgebra.toLinearMap_comulAlgHom, Bialgebra.toLinearMap_counitAlgHom]
    rw [← LinearMap.rTensor_def]
    exact HopfAlgebra.mul_antipode_rTensor_comul
  have hB2 : (Algebra.TensorProduct.lmul' K₁ (S := B)).comp
      ((Algebra.TensorProduct.map (AlgHom.id K₁ B)
        (HopfAlgebra.antipodeAlgHom K₁ B)).comp (Bialgebra.comulAlgHom K₁ B)) =
      (Algebra.ofId K₁ B).comp (Bialgebra.counitAlgHom K₁ B) := by
    apply AlgHom.toLinearMap_injective
    simp only [AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq,
      HopfAlgebra.toLinearMap_antipodeAlgHom, AlgHom.toLinearMap_id,
      Bialgebra.toLinearMap_comulAlgHom, Bialgebra.toLinearMap_counitAlgHom]
    rw [← LinearMap.lTensor_def]
    exact HopfAlgebra.mul_antipode_lTensor_comul
  -- the antipode axioms for the copy, by conjugation
  have h_S1 : (Algebra.TensorProduct.lift S (AlgHom.id K₁ (Shrink.{v} B))
        fun _ => Commute.all _).comp (Bialgebra.comulAlgHom K₁ (Shrink.{v} B)) =
      (Algebra.ofId K₁ (Shrink.{v} B)).comp
        (Bialgebra.counitAlgHom K₁ (Shrink.{v} B)) := by
    rw [← Algebra.TensorProduct.lmul'_comp_map, hcomul_new, hcounit_new]
    refine (AlgHom.cancel_right (f := ê.symm.toAlgHom)
      (show Function.Surjective ⇑ê.symm.toAlgHom from ê.symm.surjective)).mp ?_
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hΔa, ← AlgHom.comp_assoc _ _
      (Bialgebra.comulAlgHom K₁ B), hmapS, AlgHom.comp_assoc _ _
      (Bialgebra.comulAlgHom K₁ B), ← AlgHom.comp_assoc, hmul,
      AlgHom.comp_assoc, hB1, AlgHom.comp_assoc, hεa]
    apply AlgHom.ext
    intro b
    show ê.symm (algebraMap K₁ B (Bialgebra.counitAlgHom K₁ B b)) = _
    rw [AlgEquiv.commutes]
    rfl
  have h_S2 : (Algebra.TensorProduct.lift (AlgHom.id K₁ (Shrink.{v} B)) S
        fun _ _ => Commute.all _ _).comp
        (Bialgebra.comulAlgHom K₁ (Shrink.{v} B)) =
      (Algebra.ofId K₁ (Shrink.{v} B)).comp
        (Bialgebra.counitAlgHom K₁ (Shrink.{v} B)) := by
    rw [← Algebra.TensorProduct.lmul'_comp_map, hcomul_new, hcounit_new]
    refine (AlgHom.cancel_right (f := ê.symm.toAlgHom)
      (show Function.Surjective ⇑ê.symm.toAlgHom from ê.symm.surjective)).mp ?_
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hΔa, ← AlgHom.comp_assoc _ _
      (Bialgebra.comulAlgHom K₁ B), hmapS', AlgHom.comp_assoc _ _
      (Bialgebra.comulAlgHom K₁ B), ← AlgHom.comp_assoc, hmul,
      AlgHom.comp_assoc, hB2, AlgHom.comp_assoc, hεa]
    apply AlgHom.ext
    intro b
    show ê.symm (algebraMap K₁ B (Bialgebra.counitAlgHom K₁ B b)) = _
    rw [AlgEquiv.commutes]
    rfl
  letI instHopf : HopfAlgebra K₁ (Shrink.{v} B) :=
    HopfAlgebra.ofAlgHom S h_S1 h_S2
  -- the copy equivalence respects the comultiplications by construction
  refine ⟨Shrink.{v} B, inferInstance, instHopf, ê,
    BialgHom.ofAlgHom ê.toAlgHom ?_ ?_, ?_⟩
  · rw [hcounit_new]
  · rw [hcomul_new]
    have hcomp : ê.toAlgHom.comp ê.symm.toAlgHom = AlgHom.id K₁ B :=
      AlgHom.ext fun b => ê.apply_symm_apply b
    have hmapinv : (Algebra.TensorProduct.map ê.toAlgHom ê.toAlgHom).comp
        (Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom) =
        AlgHom.id K₁ (B ⊗[K₁] B) := by
      rw [← Algebra.TensorProduct.map_comp, hcomp, Algebra.TensorProduct.map_id]
    show (Algebra.TensorProduct.map ê.toAlgHom ê.toAlgHom).comp
        ((Algebra.TensorProduct.map ê.symm.toAlgHom ê.symm.toAlgHom).comp
          ((Bialgebra.comulAlgHom K₁ B).comp ê.toAlgHom)) =
      (Bialgebra.comulAlgHom K₁ B).comp ê.toAlgHom
    rw [← AlgHom.comp_assoc, hmapinv, AlgHom.id_comp]
  · rfl

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

/-- **Denominator clearing in a base-changed algebra** (PROVEN 2026-07-23; glue
for the canonicity leaf `range_comp_includeRight_eq_integralClosure_of_etale_form`
and the Hopf-order multiplication-map bijectivity
`integralClosureMul_bijective`): every element of `K ⊗[R] B` has a nonzero
`R`-multiple in the image of `B`, `K` being the fraction field of the domain
`R` — collect the denominators of the (finitely many) left tensor legs. -/
theorem exists_ne_zero_algebraMap_mul_eq_includeRight
    (B : Type*) [CommRing B] [Algebra R B] (w : K ⊗[R] B) :
    ∃ r : R, r ≠ 0 ∧ ∃ b : B,
      algebraMap R (K ⊗[R] B) r * w =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B) b := by
  induction w with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul k b =>
    obtain ⟨c, hc⟩ :=
      IsLocalization.exists_integer_multiple (nonZeroDivisors R) k
    obtain ⟨s, hs⟩ := hc
    refine ⟨(c : R), nonZeroDivisors.ne_zero c.2, s • b, ?_⟩
    have hs' : algebraMap R K (c : R) * k = algebraMap R K s :=
      (hs.trans (Algebra.smul_def (c : R) k)).symm
    rw [IsScalarTower.algebraMap_apply R K (K ⊗[R] B),
      Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, hs',
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      Algebra.TensorProduct.includeRight_apply]
  | add w₁ w₂ ih₁ ih₂ =>
    obtain ⟨r₁, hr₁, b₁, he₁⟩ := ih₁
    obtain ⟨r₂, hr₂, b₂, he₂⟩ := ih₂
    refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂,
      algebraMap R B r₂ * b₁ + algebraMap R B r₁ * b₂, ?_⟩
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)
        (algebraMap R B r₂ * b₁ + algebraMap R B r₁ * b₂) =
        algebraMap R (K ⊗[R] B) r₂ * (algebraMap R (K ⊗[R] B) r₁ * w₁) +
          algebraMap R (K ⊗[R] B) r₁ *
            (algebraMap R (K ⊗[R] B) r₂ * w₂) := by
      rw [map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes,
        he₁, he₂]
    rw [h1, map_mul]
    ring

/-- **The canonical multiplication map from the base change of the integral
closure** (glue for the field-extension form leaf below and for the Hopf-order
leaf): `k ⊗ h ↦ k • h`, as a `K`-algebra homomorphism
`K ⊗[R] integralClosure R HK →ₐ[K] HK`. Unlike an abstract form equivalence
from `Nonempty`-data, this CANONICAL map is compatible with the subalgebra
inclusion by definition, which is what lets the comultiplication, counit and
antipode corestrict along it in the Hopf-order leaf. -/
noncomputable def integralClosureMul
    (HK : Type*) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] :
    (K ⊗[R] (integralClosure R HK)) →ₐ[K] HK :=
  Algebra.TensorProduct.lift (Algebra.ofId K HK) (integralClosure R HK).val
    fun _ _ => Commute.all _ _

/-- **Injectivity of the canonical multiplication map** (PROVEN 2026-07-23;
needs no form hypothesis): a kernel element has a nonzero `R`-multiple of the
form `1 ⊗ h` (denominator clearing), whose image `h` vanishes, and
multiplication by a nonzero `r : R` is invertible on the `K`-module
`K ⊗[R] integralClosure R HK`. -/
theorem integralClosureMul_injective
    (HK : Type*) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] :
    Function.Injective (integralClosureMul R K HK) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨r, hr, h, hrh⟩ :=
    exists_ne_zero_algebraMap_mul_eq_includeRight R K
      (integralClosure R HK) w
  -- the image of `h` in `HK` vanishes, so `h = 0`
  have h3 : integralClosureMul R K HK
      ((Algebra.TensorProduct.includeRight :
        _ →ₐ[R] K ⊗[R] (integralClosure R HK)) h) = (h : HK) := by
    simp [integralClosureMul, Algebra.ofId_apply]
  have h1 : (h : HK) = 0 := by
    rw [← h3, ← hrh, map_mul, hw, mul_zero]
  have h0 : h = 0 := Subtype.ext h1
  rw [h0, map_zero] at hrh
  -- multiplication by the nonzero `r` is injective on a `K`-module
  have hu : IsUnit (algebraMap R (K ⊗[R] (integralClosure R HK)) r) := by
    rw [IsScalarTower.algebraMap_apply R K (K ⊗[R] (integralClosure R HK))]
    exact (isUnit_iff_ne_zero.mpr fun hzero => hr
      ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) r
        hzero)).map (algebraMap K (K ⊗[R] (integralClosure R HK)))
  exact (hu.mul_right_eq_zero).mp hrh

/-- **Étaleness of the integral closure under inertia-fixed embeddings** (sorry
node; the DVR-Galois core of the single-factor leaf, isolated 2026-07-23 — the
finiteness of the integral closure and the form equivalence via the canonical
multiplication map are PROVEN in
`exists_finite_etale_algebra_form_of_inertia_fixes_field`): for a finite
separable field extension `L/K`, all of whose embeddings into `Kˢᵉᵖ` are fixed
by every inertia subgroup above `R`, the integral closure of `R` in `L` is
étale over `R`. Intended proof: finite presentation is Noetherian-automatic
(the closure is module-finite over `R` by separability); for formal
étaleness, the closure is flat (torsion-free over the DVR `R`) and it remains
to see it is unramified: the inertia hypothesis places each embedding
`L → Kˢᵉᵖ` inside the inertia field of every extension of the valuation of `R`
to `Kˢᵉᵖ`, so for every prime `𝔮` above `𝔪 = (π)` the extension of complete
local fields is inertia-trivial, i.e. `e(𝔮/𝔪) = 1` with separable residue
extension (Neukirch I.9/II.9, Serre *Local Fields* I–II); hence `π` generates
the maximal ideal at every `𝔮` and `𝔪`-fibre is a finite product of separable
residue field extensions, which is `Algebra.FormallyUnramified`; finally
flat + unramified + finitely presented over the DVR is étale (fibrewise
smoothness of dimension zero). -/
theorem integralClosure_etale_of_inertia_fixes_field
    (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : L →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    Algebra.Etale R (integralClosure R L) :=
  sorry

/-- **Unramified finite separable field extensions have finite étale `R`-forms**
(DECOMPOSED 2026-07-23 into the étaleness core
`integralClosure_etale_of_inertia_fixes_field`; the finiteness of the integral
closure — separability over the Noetherian integrally closed `R`
(`IsIntegralClosure.finite`) — and the form equivalence — bijectivity of the
canonical multiplication map `K ⊗[R] integralClosure R L → L`, by denominator
clearing on both sides — are PROVEN in the assembly below): a finite separable
field extension `L/K`, all of whose embeddings into `Kˢᵉᵖ` are fixed by every
inertia subgroup above `R`, admits a finite étale `R`-form, namely the
integral closure of `R` in `L`. -/
theorem exists_finite_etale_algebra_form_of_inertia_fixes_field
    (L : Type u) [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : L →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    ∃ (H₀ : Type u) (_ : CommRing H₀) (_ : Algebra R H₀)
      (_ : Module.Finite R H₀) (_ : Algebra.Etale R H₀),
      Nonempty ((K ⊗[R] H₀) ≃ₐ[K] L) := by
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- finiteness of the integral closure: separability over the Noetherian
  -- integrally closed base `R`
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  -- étaleness: the sorried DVR-Galois core
  have het : Algebra.Etale R (integralClosure R L) :=
    integralClosure_etale_of_inertia_fixes_field R K Ksep L hfix
  -- the canonical multiplication map realizes the form equivalence
  have hbij : Function.Bijective (integralClosureMul R K L) := by
    refine ⟨integralClosureMul_injective R K L, fun z => ?_⟩
    obtain ⟨r, hr, hint⟩ := exists_integral_multiples R K ({z} : Finset L)
    have hz : IsIntegral R (r • z) := hint z (Finset.mem_singleton_self z)
    have hr' : algebraMap R K r ≠ 0 := fun h0 => hr
      ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) r h0)
    have hrL : algebraMap K L (algebraMap R K r) ≠ 0 :=
      fun h0 => hr' ((algebraMap K L).injective (h0.trans (map_zero _).symm))
    refine ⟨(algebraMap R K r)⁻¹ ⊗ₜ ⟨r • z, hz⟩, ?_⟩
    simp only [integralClosureMul, Algebra.TensorProduct.lift_tmul,
      Algebra.ofId_apply]
    rw [map_inv₀]
    show (algebraMap K L (algebraMap R K r))⁻¹ * (r • z) = z
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K L,
      inv_mul_cancel_left₀ hrL]
  exact ⟨integralClosure R L, inferInstance, inferInstance, hfin, het,
    ⟨AlgEquiv.ofBijective (integralClosureMul R K L) hbij⟩⟩

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

/-- **The image of a finite étale `R`-form is the integral closure** (PROVEN
2026-07-23; the workhorse behind the canonicity leaf
`integralClosure_finite_etale_form_of_etale_algebra_form`, stated separately so
that the Hopf-order leaf can reuse it on the tensor square): for a finite étale
`R`-algebra `H₀` and a `K`-algebra equivalence `e : K ⊗[R] H₀ ≃ₐ[K] HK`, the
image of `H₀` in `HK` under `x ↦ e (1 ⊗ x)` is exactly the integral closure of
`R` in `HK`. Inclusion `⊆`: `H₀` is module-finite over `R`, hence integral, and
integrality is preserved by `R`-algebra maps. Inclusion `⊇`: an integral `z` has
`π ^ k * z` in the image for some `k` (clearing denominators through `e`, `K`
being the fraction field of the DVR `R`), and `k` descends to zero: if `π * z`
is the image of `h`, then `h ^ m` lies in `π H₀` (root the integral equation of
`z` scaled by `π` at `h` and pull back along the injective form map), and
`π H₀ = 𝔪 H₀` is a RADICAL ideal by unramifiedness of the form
(`Algebra.FormallyUnramified.isRadical_map_isMaximal` — exactly where étaleness
enters, and where the `μ_p` counterexample fails), so `h = π * h'` and `z` is
the image of `h'`, `π` being invertible in the `K`-algebra `HK`. -/
theorem range_comp_includeRight_eq_integralClosure_of_etale_form
    (HK : Type*) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK]
    (H₀ : Type*) [CommRing H₀] [Algebra R H₀] [Module.Finite R H₀]
    [Algebra.Etale R H₀]
    (e : (K ⊗[R] H₀) ≃ₐ[K] HK) :
    ((e.toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : H₀ →ₐ[R] K ⊗[R] H₀)).range =
      integralClosure R HK := by
  classical
  set φ : H₀ →ₐ[R] HK :=
    (e.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H₀ →ₐ[R] K ⊗[R] H₀) with hφdef
  -- the form map is injective (`H₀` is flat: étale ⟹ smooth ⟹ flat)
  have hinj : Function.Injective φ :=
    e.injective.comp
      (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))
  -- a uniformizer of `R`, invertible in the `K`-algebra `HK`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπK : IsUnit (algebraMap R HK π) := by
    rw [IsScalarTower.algebraMap_apply R K HK]
    exact (isUnit_iff_ne_zero.mpr fun h0 => hπ0
      ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective R K) π h0)).map
      (algebraMap K HK)
  -- the descent step: an integral `z` with `π * z` in the image is in the image
  have hstep : ∀ z : HK, IsIntegral R z →
      algebraMap R HK π * z ∈ φ.range → z ∈ φ.range := by
    intro z hz hmem
    obtain ⟨h, hh⟩ := hmem
    replace hh : φ h = algebraMap R HK π * z := hh
    obtain ⟨p, hpmonic, hp0⟩ := hz
    -- scale the roots of the integral equation by `π` and evaluate at `h`
    have hq0 : Polynomial.aeval (algebraMap R HK π * z) (p.scaleRoots π) = 0 :=
      Polynomial.scaleRoots_aeval_eq_zero hp0
    rw [← hh, Polynomial.aeval_algHom_apply] at hq0
    have hqh : Polynomial.aeval h (p.scaleRoots π) = 0 :=
      hinj (hq0.trans (map_zero φ).symm)
    -- isolate the leading term: `h ^ m ∈ π H₀`
    have hpow : h ^ p.natDegree ∈ Ideal.span {algebraMap R H₀ π} := by
      have hsum := Polynomial.aeval_eq_sum_range (p := p.scaleRoots π) h
      rw [hqh, Polynomial.natDegree_scaleRoots, Finset.sum_range_succ,
        Polynomial.coeff_scaleRoots_natDegree, hpmonic.leadingCoeff, one_smul]
        at hsum
      have hneg : h ^ p.natDegree =
          -∑ i ∈ Finset.range p.natDegree, (p.scaleRoots π).coeff i • h ^ i :=
        eq_neg_of_add_eq_zero_right hsum.symm
      rw [hneg]
      refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
      rw [Algebra.smul_def]
      refine Ideal.mem_span_singleton.mpr (Dvd.dvd.mul_right ?_ _)
      refine map_dvd (algebraMap R H₀) ?_
      rw [Polynomial.coeff_scaleRoots]
      exact ((dvd_pow_self π
        (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hi))).mul_left _)
    -- `π H₀ = 𝔪 H₀` is radical because the form is unramified
    have hrad : (Ideal.span {algebraMap R H₀ π}).IsRadical := by
      have h1 := Algebra.FormallyUnramified.isRadical_map_isMaximal R H₀
        (IsLocalRing.maximalIdeal R)
      rwa [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at h1
    obtain ⟨h', hh'⟩ := Ideal.mem_span_singleton'.mp (hrad ⟨p.natDegree, hpow⟩)
    -- cancel the (invertible in `HK`) factor `π`
    refine ⟨h', hπK.mul_left_cancel ?_⟩
    calc algebraMap R HK π * φ h'
        = φ (algebraMap R H₀ π * h') := by rw [map_mul, AlgHom.commutes]
      _ = φ h := by rw [mul_comm, hh']
      _ = algebraMap R HK π * z := hh
  -- clearing denominators: every element of `HK` has a `π`-power multiple in the image
  have hden : ∀ z : HK, ∃ k : ℕ, algebraMap R HK π ^ k * z ∈ φ.range := by
    have hden0 := exists_ne_zero_algebraMap_mul_eq_includeRight R K H₀
    intro z
    obtain ⟨r, hr, h, hrh⟩ := hden0 (e.symm z)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
    have he1 : algebraMap R HK r * z = φ h := by
      have h2 := congrArg e hrh
      rw [map_mul, e.apply_symm_apply,
        show e (algebraMap R (K ⊗[R] H₀) r) = algebraMap R HK r from
          (e.toAlgHom.restrictScalars R).commutes r] at h2
      exact h2
    have hval : ((u⁻¹ : Rˣ) : R) * r = π ^ n := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    refine ⟨n, algebraMap R H₀ ((u⁻¹ : Rˣ) : R) * h, ?_⟩
    calc φ (algebraMap R H₀ ((u⁻¹ : Rˣ) : R) * h)
        = algebraMap R HK ((u⁻¹ : Rˣ) : R) * φ h := by
          rw [map_mul, AlgHom.commutes]
      _ = algebraMap R HK ((u⁻¹ : Rˣ) : R) * (algebraMap R HK r * z) := by
          rw [he1]
      _ = algebraMap R HK (((u⁻¹ : Rˣ) : R) * r) * z := by
          rw [map_mul, mul_assoc]
      _ = algebraMap R HK π ^ n * z := by rw [hval, map_pow]
  -- descend the `π`-power by induction, using integrality of `z` throughout
  have hall : ∀ k : ℕ, ∀ z : HK, IsIntegral R z →
      algebraMap R HK π ^ k * z ∈ φ.range → z ∈ φ.range := by
    intro k
    induction k with
    | zero => intro z _ h0; simpa using h0
    | succ k ih =>
      intro z hz hk
      refine ih z hz (hstep _ (((isIntegral_algebraMap (x := π)).pow k).mul hz) ?_)
      rw [← mul_assoc, ← pow_succ']
      exact hk
  -- assemble the two inclusions
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral y).map φ
  · intro z hz
    obtain ⟨k, hk⟩ := hden z
    exact hall k z hz hk

/-- **Étale algebra forms are the integral closure** (PROVEN 2026-07-23 from the
range identity `range_comp_includeRight_eq_integralClosure_of_etale_form`; the
CANONICITY half of the Hopf-upgrade leaf — pure commutative algebra over the DVR
`R`, no Hopf structure): if the finite étale `K`-algebra `HK` admits a finite
étale `R`-algebra form `H₀`, then the integral closure of `R` in `HK` is itself
a finite étale `R`-algebra form. The image of `H₀` under `x ↦ e (1 ⊗ x)` IS the
integral closure (the range identity), and the form data transports along the
induced isomorphism `H₀ ≅ integralClosure R HK` (étale forms are canonical). -/
theorem integralClosure_finite_etale_form_of_etale_algebra_form
    (HK : Type u) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] [Module.Finite K HK] [Algebra.Etale K HK]
    (H₀ : Type u) [CommRing H₀] [Algebra R H₀] [Module.Finite R H₀]
    [Algebra.Etale R H₀]
    (e : (K ⊗[R] H₀) ≃ₐ[K] HK) :
    Module.Finite R (integralClosure R HK) ∧
      Algebra.Etale R (integralClosure R HK) ∧
      Nonempty ((K ⊗[R] (integralClosure R HK)) ≃ₐ[K] HK) := by
  classical
  set φ : H₀ →ₐ[R] HK :=
    (e.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : H₀ →ₐ[R] K ⊗[R] H₀) with hφdef
  have hrange : φ.range = integralClosure R HK :=
    range_comp_includeRight_eq_integralClosure_of_etale_form R K HK H₀ e
  have hinj : Function.Injective φ :=
    e.injective.comp
      (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))
  -- the induced isomorphism `H₀ ≃ₐ[R] integralClosure R HK`
  let e₀ : H₀ ≃ₐ[R] integralClosure R HK :=
    (AlgEquiv.ofInjective φ hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  exact ⟨Module.Finite.equiv e₀.toLinearEquiv, Algebra.Etale.of_equiv e₀,
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K))
      e₀.symm).trans e⟩⟩

/-- **Bijectivity of the canonical multiplication map** (PROVEN 2026-07-23):
if SOME `K`-algebra form equivalence `K ⊗[R] integralClosure R HK ≃ₐ[K] HK`
exists, then the canonical multiplication map is itself bijective.
Surjectivity: `e` maps `1 ⊗ h` into the integral closure (integrality is
preserved by `R`-algebra maps), so `e (k ⊗ h) = k • e (1 ⊗ h)` already lies in
the image of the canonical map, and the `e (k ⊗ h)` span the target. -/
theorem integralClosureMul_bijective
    (HK : Type*) [CommRing HK] [Algebra K HK] [Algebra R HK]
    [IsScalarTower R K HK]
    (heq : Nonempty ((K ⊗[R] (integralClosure R HK)) ≃ₐ[K] HK)) :
    Function.Bijective (integralClosureMul R K HK) := by
  obtain ⟨e⟩ := heq
  constructor
  · exact integralClosureMul_injective R K HK
  · intro z
    suffices h : ∀ w : K ⊗[R] (integralClosure R HK),
        ∃ v, integralClosureMul R K HK v = e w by
      obtain ⟨v, hv⟩ := h (e.symm z)
      exact ⟨v, by rw [hv, e.apply_symm_apply]⟩
    intro w
    induction w with
    | zero => exact ⟨0, by simp⟩
    | tmul k h =>
      -- `e (1 ⊗ h)` is integral over `R`, hence in the integral closure
      have hint : IsIntegral R (e ((Algebra.TensorProduct.includeRight :
          _ →ₐ[R] K ⊗[R] (integralClosure R HK)) h)) :=
        (integralClosure.isIntegral (R := R) (A := HK) h).map
          ((e.toAlgHom.restrictScalars R).comp
            Algebra.TensorProduct.includeRight)
      refine ⟨k ⊗ₜ ⟨e ((Algebra.TensorProduct.includeRight :
          _ →ₐ[R] K ⊗[R] (integralClosure R HK)) h), hint⟩, ?_⟩
      -- both sides are `algebraMap k * e (1 ⊗ h)`
      have hsplit : (k ⊗ₜ h : K ⊗[R] (integralClosure R HK)) =
          algebraMap K (K ⊗[R] (integralClosure R HK)) k *
            (Algebra.TensorProduct.includeRight :
              _ →ₐ[R] K ⊗[R] (integralClosure R HK)) h := by
        rw [Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          Algebra.algebraMap_self, RingHom.id_apply, mul_one]
      rw [hsplit, map_mul, e.commutes]
      simp [integralClosureMul, Algebra.ofId_apply]
    | add w₁ w₂ ih₁ ih₂ =>
      obtain ⟨v₁, hv₁⟩ := ih₁
      obtain ⟨v₂, hv₂⟩ := ih₂
      exact ⟨v₁ + v₂, by rw [map_add, map_add, hv₁, hv₂]⟩

/-- **The Hopf-order structure on the integral closure** (sorry node; the
corestriction core of the Hopf half of the Hopf-upgrade leaf, isolated
2026-07-23 — the canonical multiplication map, its bijectivity and the final
assembly are PROVEN): if the integral closure `H₀ := integralClosure R HK` of
the DVR `R` in the finite étale Hopf `K`-algebra `HK` is finite étale over `R`
and the canonical multiplication map `μ : K ⊗[R] H₀ → HK` is bijective, then
`H₀` carries an `R`-Hopf-algebra structure whose base change is `HK` as a
`K`-bialgebra. Intended proof: comultiplication is a ring homomorphism, so it
sends `H₀` (integral over `R`) into elements of `HK ⊗[K] HK` integral over `R`;
the integral closure of `R` there is the image of `H₀ ⊗[R] H₀` under
`τ := e₂ ∘ (1 ⊗ ·)`, where `e₂ : K ⊗[R] (H₀ ⊗[R] H₀) ≃ HK ⊗[K] HK` is the
base-change comparison (`Algebra.TensorProduct.assoc`/`cancelBaseChange`
composed with `congr μ μ`) and the range identity is the canonicity workhorse
`range_comp_includeRight_eq_integralClosure_of_etale_form` applied to the
tensor square (`H₀ ⊗[R] H₀` is finite étale: étale is stable under base change
and composition); so the comultiplication corestricts along the injective `τ`
(injectivity: flatness of `H₀ ⊗[R] H₀`). The counit sends `H₀` into elements
of `K` integral over `R`, i.e. into `R` (`IsIntegrallyClosed R`, `R` a DVR);
the antipode is an algebra endomorphism of `HK`, so it preserves the integral
closure. The corestricted operations satisfy the Hopf axioms because `τ` and
its double/triple analogues are injective, and `μ` becomes a bialgebra
equivalence because its compatibility with `τ` holds by construction. The
`μ_p` counterexample (whose normalization over `ℤ_p` is NOT a Hopf order) does
not contradict this: there the normalization is not étale over `R`, so the
étale hypothesis fails. NOTE the conclusion carries its own abstract carrier
`H` with ALL instances existential rather than a Hopf structure on
`integralClosure R HK` itself: the carrier has canonical `CommRing`/`Algebra`
instances, and an existentially bound Hopf structure on it cannot state the
`≃ₐc` conclusion without an instance diamond (the same probe-verified
obstruction as for `GaloisHopfCarrier`); the intended `H` is a structureless
copy of the integral closure. -/
theorem exists_hopfAlgebra_integralClosure_of_mul_bijective
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] [Module.Finite K HK] [Algebra.Etale K HK]
    (hfin : Module.Finite R (integralClosure R HK))
    (het : Algebra.Etale R (integralClosure R HK))
    (hbij : Function.Bijective (integralClosureMul R K HK)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) :=
  sorry

/-- **The integral closure in an étale-formed Hopf algebra is a Hopf order**
(DECOMPOSED 2026-07-23 into the bijectivity of the canonical multiplication
map `integralClosureMul_bijective` — PROVEN — and the corestriction core
`exists_hopfAlgebra_integralClosure_of_mul_bijective`; the assembly below is
proven): if the integral closure `H₀ := integralClosure R HK` of `R` in the
finite étale Hopf `K`-algebra `HK` is a finite étale `R`-algebra form, then
`HK` admits a finite flat Hopf `R`-form (namely `H₀` itself); flatness is
étale ⟹ smooth ⟹ flat. -/
theorem exists_finite_flat_hopf_form_integralClosure
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK] [Algebra R HK]
    [IsScalarTower R K HK] [Module.Finite K HK] [Algebra.Etale K HK]
    (hfin : Module.Finite R (integralClosure R HK))
    (het : Algebra.Etale R (integralClosure R HK))
    (heq : Nonempty ((K ⊗[R] (integralClosure R HK)) ≃ₐ[K] HK)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) :=
  exists_hopfAlgebra_integralClosure_of_mul_bijective R K HK hfin het
    (integralClosureMul_bijective R K HK heq)

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

/-- **Grothendieck full faithfulness, algebra half** (sorry node; curve-free —
the descent core of the comparison leaf
`exists_bialgEquiv_of_torsion_points_equiv`): a `Gal(Kˢᵉᵖ/K)`-equivariant
bijection between the `Kˢᵉᵖ`-points of two finite étale `K`-algebras is induced
by composition with a (unique, but only existence is stated) `K`-algebra
isomorphism. This is the full faithfulness of the Grothendieck
anti-equivalence between finite étale `K`-algebras and finite discrete Galois
sets. Intended proof, aligned with the `GaloisEtalePackage` section above:
choose a finite Galois subextension `L` of `Kˢᵉᵖ` splitting both `A` and `B`
(a compositum of the finitely many images of the finitely many points); the
evaluation maps `A → (A →ₐ[K] Kˢᵉᵖ) → L` and `B → (B →ₐ[K] Kˢᵉᵖ) → L` land in
the `Gal(L/K)`-equivariant functions and are isomorphisms onto them (the
étale-algebra Gelfand transform: injective because points separate a finite
étale algebra, surjective by the dimension count
`dim A = #points = dim (equivariant functions)`); conjugating the second by
the equivariant bijection `g` of the point sets identifies the two
equivariant-function algebras, and the composite `B ≃ A` induces `g` by
construction. -/
theorem exists_algEquiv_of_algHom_equiv
    (A : Type*) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    (B : Type*) [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (g : (A →ₐ[K] Ksep) ≃ (B →ₐ[K] Ksep))
    (hg : ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : A →ₐ[K] Ksep),
      g (σ.toAlgHom.comp φ) = σ.toAlgHom.comp (g φ)) :
    ∃ e : B ≃ₐ[K] A, ∀ φ : A →ₐ[K] Ksep, g φ = φ.comp e.toAlgHom :=
  sorry

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Ksep] in
/-- **Points separate a finite étale algebra** (PROVEN 2026-07-23; glue for the
Hopf-upgrade leaf `exists_bialgEquiv_of_algEquiv_conv`): an element of a finite
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

/-- **The Katz–Mazur flat model, mixed characteristic** (sorry node; the
EXISTENCE half of the Katz–Mazur leaf — the flat-package statement with no
reference algebra to compare against): when the prime `p` is not invertible in
`R` but nonzero in `K`, SOME finite flat Hopf `R`-algebra has étale generic
fibre whose `Kˢᵉᵖ`-points are, `Gal(Kˢᵉᵖ/K)`-equivariantly, the
`p ^ k`-torsion of `E(Kˢᵉᵖ)`. Unlike the unramified case, `H` is NOT a
normalization: division polynomials cannot produce `H` here (part of the
torsion group scheme sits in the kernel of reduction, outside the affine
chart), and the integral closure of `R` in the torsion algebra is in general
not a Hopf algebra (for `μ_p` over `ℤ_p` the normalization has a special fibre
with two connected components of lengths `1` and `p - 1`, which is not a group
scheme). The mathematical content is [Katz–Mazur, *Arithmetic moduli of
elliptic curves*, Thm 2.3.1]: `H` is the affine algebra of the kernel
`𝓔[p ^ k]` of multiplication by `p ^ k` on the elliptic scheme `𝓔` of the
minimal (good-reduction) Weierstrass equation.

SCHEME-FREE CONSTRUCTION ROADMAP (worked out 2026-07-23, for the next owner —
a Hopf-ORDER presentation of the same object; `𝓔[p ^ k]` is flat, so it is
the schematic closure of its generic fibre, so `H` is the image of the
functions on any affine open `U ⊇ 𝓔[p ^ k]` inside the étale generic-fibre
algebra):

1. Carrier. Realize the generic fibre concretely as the
   `Gal(L/K)`-equivariant functions `V → L` of the `GaloisEtalePackage`
   section, `V := E(Kˢᵉᵖ)[p ^ k]` (finite by `torsion_finite_of_ne_zero`),
   `L` a finite Galois splitting subextension.
2. Avoiding denominator. Choose `h ∈ R[X]` monic of degree `d ≥ 2` whose
   reduction is coprime to the reduced affine-torsion locus: `h(x(P))` is a
   unit of the valuation ring for every torsion point `P` with integral
   abscissa (possible because the residue field admits irreducibles of
   arbitrarily large degree avoiding the finitely many torsion abscissa
   residues; for non-integral abscissas `v(h(x(P))) = d·v(x(P)) < 0`
   automatically). Then `U := 𝓔 ∖ V(h ∘ x)` contains the whole kernel,
   including the origin.
3. Generators. `H` := the `R`-subalgebra of equivariant functions generated
   by the finitely many `g_{a,b} : P ↦ x(P)^a y(P)^b / h(x(P))^m` (with
   `2a + 3b ≤ 2dm`, `b ≤ 1`, value `0`-or-limit at `P = 0`; these are the
   monomial sections of `Γ(U)` restricted to the kernel). Each `g_{a,b}` has
   integral values at every point (choice of `h`), hence is integral over
   `R`: `H` is module-finite; it is torsion-free inside a `K`-space, hence
   FREE over the DVR `R`: finite flat.
4. Spanning. `K · H` is a `K`-subalgebra of the étale algebra separating the
   `Kˢᵉᵖ`-points (the `g_{a,b}` separate affine torsion points from each
   other and from the origin), and a separating subalgebra of a finite étale
   algebra is everything (both are étale — subalgebras of separable algebras
   are separable — so `dim = #points` on both sides, restriction of points is
   injective by separation and surjective by integrality lifting).
5. Hopf-closure — THE Katz–Mazur core: `Δ g_{a,b} ∈ H ⊗[R] H`, i.e. the
   two-variable functions `(P, Q) ↦ g_{a,b}(P + Q)` are `R`-polynomial in
   `g_{a',b'}(P), g_{a'',b''}(Q)`. This is the integrality of the addition
   law relative to `h` on the kernel — the point where the division-polynomial
   arithmetic enters: the addition formulas have denominators
   `(x(P) - x(Q))²` resp. `ψ²`, controlled on the torsion locus by the monic
   `(Φ n).eval X - ξ * (ΨSq n).eval X` (degree `n²` over `R[ξ]`) and the
   fibrewise coprimality `isCoprime_Φ_ΨSq` (proven,
   `Fermat.FLT.EllipticCurve.PhiPsiCoprime`). Counit and antipode closure are
   immediate (`ε g = g(0) ∈ R`, `S g = g ∘ (-1)` is again a generator up to
   the curve relation). Étaleness of the generic fibre is by construction
   (step 4 identifies it with the étale package); the points identification
   and its equivariance are the evaluation dictionary of the
   `GaloisEtalePackage` section.

For the Frey curve application (`R = ℤ_(p)`, `K = ℚ`, `k = 1`) the same
object is the kernel of `[p]` on the good-reduction Weierstrass model; the
`k = 1` specialization admits no genuine shortcut past the origin chart,
because the connected component of `𝓔[p]` (where the model is NOT étale) is
present for every `k`. -/
theorem WeierstrassCurve.exists_torsion_flat_model_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0)
    (hpK : (p : K) ≠ 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (g : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (g (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (g (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

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
