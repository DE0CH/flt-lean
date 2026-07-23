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
  sees only its maximal étale quotient (for `n = p`: a group of order `p` if the
  reduction is ordinary and of order `1` if it is supersingular). The statement below
  should still be true — for `H` one can take the Cartier dual of the schematic closure
  in `𝓔[n]` of the Cartier dual of the maximal étale quotient of `E[n]` — but it is
  strictly weaker than flatness of `E[n]` itself. The honest statement in this case is
  the group-scheme statement of the previous paragraph, which cannot yet be formalised.

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
Galois-correspondence and prolongation leaves. All assemblies are proven; the
remaining sorries in this subsection are the two kernel-of-reduction leaves
(`kernel_add_abscissa_notMem`, `kernel_sub_abscissa_notMem_of_residue_eq`), the
Galois-correspondence leaf (`exists_torsion_etale_package_over_fractionField`),
and — since the 2026-07-22 decomposition of `torsion_flat_of_inertia_fixes_prolong`
through the flat Hopf-form transport — the curve-free Hopf-form leaf
(`exists_finite_flat_hopf_form_of_inertia_fixes`).
-/

/-- **The kernel of reduction is closed under addition, abscissa form** (sorry node;
Silverman *AEC* VII.2.2 in coordinates, characteristic-free and torsion-free): on the
minimal model, if two affine points of `E(Kˢᵉᵖ)` both have non-integral abscissa over a
valuation subring `𝒪` of `Kˢᵉᵖ` above `R`, then any affine value of their sum again has
non-integral abscissa. Intended proof: `xᵢ ∉ 𝒪` forces `v(xᵢ) < 0`, and on the curve
`2 v(yᵢ) = 3 v(xᵢ)` (once `v(x) < 0` and the `aᵢ` are integral, the dominant terms of
the Weierstrass equation are `y²` and `x³`), so both points lie in the formal-group
chart `zᵢ = -xᵢ/yᵢ` with `v(zᵢ) = -v(xᵢ)/2... > 0`; the formal group law
`z₃ = z₁ + z₂ + (higher order, integral coefficients)` gives
`v(z₃) ≥ min (v(z₁)) (v(z₂)) > 0`, and `v(x₃) = -2 v(z₃) < 0`. Alternatively, direct
chord/tangent slope bookkeeping on the addition formulas avoids introducing the formal
group law. -/
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
    x₃ ∉ 𝒪 :=
  sorry

/-- **Congruent distinct integral points differ by a kernel element** (sorry node;
Silverman *AEC* VII.2.1-2 in coordinates, characteristic-free and torsion-free): on the
minimal model, if two DISTINCT affine points of `E(Kˢᵉᵖ)` have integral coordinates
with equal residues over a valuation subring `𝒪` of `Kˢᵉᵖ` above `R`, then any affine
value of their difference has non-integral abscissa ("the difference lies in the kernel
of reduction"). Intended proof, by the chord construction for
`(x₁, y₁) + (x₂, -y₂ - a₁x₂ - a₃)`: if `x₁ ≠ x₂`, the slope
`λ = (y₁ + y₂ + a₁x₂ + a₃)/(x₁ - x₂)` has denominator in the maximal ideal `𝔪` and
numerator congruent to `ψ₂(x₂, y₂) mod 𝔪`; when `ψ₂(x₂, y₂) ∉ 𝔪` this gives
`v(λ) < 0` and `v(x₃) = 2 v(λ) + (integral) < 0`; when `ψ₂(x₂, y₂) ∈ 𝔪` compare the
valuations of the two ordinates above `x₂` via the `y`-quadratic. If `x₁ = x₂` the
points differ by an ordinate flip, `y₁ ≠ y₂` congruent forces `ψ₂(x₁, y₁) ∈ 𝔪` with
`ψ₂(x₁, y₁) ≠ 0`, and the difference is the DOUBLE of `(x₁, y₁)`: the duplication
formula has denominator `ψ₂² ≡ 0 mod 𝔪` and numerator `x⁴ - b₄x² - 2b₆x - b₈`, whose
common vanishing with `Ψ₂Sq = 4x³ + b₂x² + 2b₄x + b₆` modulo `𝔪` is excluded by a
Bézout identity with resultant a power of `Δ` — a unit by good reduction (compare the
proven `(2,3)` certificates in `Fermat.FLT.EllipticCurve.PhiPsiCoprime`). -/
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
    x₃ ∉ 𝒪 :=
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
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
    | succ n hn ih =>
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
  set j₁ := Nat.find hex with hj₁def
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
      set σf := ((σ : Ksep ≃ₐ[K] Ksep)).toAlgHom with hσfdef
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

/-- **The finite étale Hopf package of the torsion over the fraction field** (sorry
node; the Galois-theory half, shared by the étale case below and the mixed-characteristic
branch of the residue-characteristic case — nothing DVR-arithmetic remains in its
intended proof): for `m` nonzero in `R`, the `m`-torsion Galois module `E(Kˢᵉᵖ)[m]` is,
`Gal(Kˢᵉᵖ/K)`-equivariantly, the group of `Kˢᵉᵖ`-points of a finite étale Hopf algebra
over `K`. Intended proof (Grothendieck's Galois correspondence for étale `K`-algebras,
with group structure): `H_K` is the algebra of `Gal(Kˢᵉᵖ/K)`-equivariant maps
`E(Kˢᵉᵖ)[m] → Kˢᵉᵖ`; the torsion is finite (division polynomials) and the action is
discrete (a torsion point is fixed by the fixing subgroup of the finite extension
generated by its coordinates), so evaluation at orbit representatives identifies `H_K`
with a finite product `∏_{orbits} Fix(Stab)` of finite separable subextensions of
`Kˢᵉᵖ/K` — finite étale of `K`-dimension `#E(Kˢᵉᵖ)[m]` — and the comultiplication is
the pullback of the group law through the same identification for `H_K ⊗[K] H_K`. The
universe-`u` carrier is legitimate because `K` is the fraction field of `R : Type u`
(transport along a `K`-basis realizes the algebra on `Fin d → FractionRing R`). The
structurally parallel sorry node `exists_galoisModulePackage_of_finiteQuotient` in
`Fermat.FLT.FreyCurve.Semistable` (downstream, hence not importable here) proves the
same correspondence over `ℚ`; when one of the two is resolved the other should be
derived from or aligned with it. -/
theorem WeierstrassCurve.exists_torsion_etale_package_over_fractionField
    (m : ℕ) (hm : (m : R) ≠ 0) :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K HK)
      (_ : Module.Finite K HK) (_ : Algebra.Etale K HK)
      (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

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

/-- **Unramified finite étale `K`-algebras have finite étale `R`-forms** (sorry
node; the GALOIS half of the curve-free Hopf-form leaf — no Hopf structure
appears at all): a finite étale `K`-algebra `HK`, all of whose `Kˢᵉᵖ`-points
are fixed by every inertia subgroup above `R`, admits a finite étale `R`-form.
Intended proof: `HK` is a finite product of finite separable subextensions
`Lᵢ` of `Kˢᵉᵖ/K` (étale `K`-algebras split by `Kˢᵉᵖ`); the hypothesis places
each embedding `Lᵢ → Kˢᵉᵖ` inside the inertia field of every valuation subring
above `R`, so each `Lᵢ` is unramified with separable residue extension at
every prime above the maximal ideal of `R`. Take `H₀` to be the integral
closure of `R` in `HK` (transported to `Type u` along an `R`-basis), i.e. the
product of the normalizations `Rᵢ` of `R` in `Lᵢ`: each `Rᵢ` is finite over
`R` (separability + Noetherian normal base), free (torsion-free finite over a
DVR), and étale over `R` (finite flat + unramified fibres, by the inertia
hypothesis), and `K ⊗[R] H₀ → HK` is an isomorphism (clearing denominators). -/
theorem exists_finite_etale_algebra_form_of_inertia_fixes
    (HK : Type u) [CommRing HK] [Algebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (hfix : ∀ 𝒪 : ValuationSubring Ksep,
      (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
      ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ φ : HK →ₐ[K] Ksep,
        (σ : Ksep ≃ₐ[K] Ksep).toAlgHom.comp φ = φ) :
    ∃ (H₀ : Type u) (_ : CommRing H₀) (_ : Algebra R H₀)
      (_ : Module.Finite R H₀) (_ : Algebra.Etale R H₀),
      Nonempty ((K ⊗[R] H₀) ≃ₐ[K] HK) :=
  sorry

/-- **Étale algebra forms of Hopf algebras are Hopf forms** (sorry node; the
HOPF half of the curve-free Hopf-form leaf — pure commutative algebra over the
DVR `R`, no Galois theory and no elliptic curve): if the finite étale Hopf
`K`-algebra `HK` admits a finite étale `R`-ALGEBRA form `H₀`, then it admits a
finite flat Hopf `R`-form. The key point making this honest: a finite étale
`R`-algebra is normal, hence integrally closed in its total fraction ring
`K ⊗[R] H₀ ≅ HK`, hence `H₀` is THE integral closure of `R` in `HK` — étale
forms are canonical, so Hopf-stability is a property, not extra data. Intended
proof: comultiplication is a ring homomorphism, so it sends `H₀` (integral over
`R`) into elements of `HK ⊗[K] HK` integral over `R`, and the integral closure
of `R` there is `H₀ ⊗[R] H₀` (étale ⊗ étale is étale over the normal base `R`,
hence normal, hence integrally closed in its total fraction ring, and
`K ⊗ (H₀ ⊗[R] H₀) ≅ HK ⊗[K] HK`); the counit sends `H₀` into elements of `K`
integral over `R`, i.e. into `R` (a DVR is integrally closed); the antipode is
an algebra endomorphism, so it preserves integrality; flatness is freeness of
a finite torsion-free module over a DVR. The `μ_p` counterexample (whose
normalization over `ℤ_p` is NOT a Hopf order) does not contradict this: there
the normalization is not étale over `R`, so it is not an étale algebra form. -/
theorem exists_finite_flat_hopf_form_of_etale_algebra_form
    (HK : Type u) [CommRing HK] [HopfAlgebra K HK]
    [Module.Finite K HK] [Algebra.Etale K HK]
    (H₀ : Type u) [CommRing H₀] [Algebra R H₀] [Module.Finite R H₀]
    [Algebra.Etale R H₀]
    (e : (K ⊗[R] H₀) ≃ₐ[K] HK) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H),
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) :=
  sorry

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

/-- **The Katz–Mazur flat Hopf form, mixed characteristic** (sorry node; the
mathematical core of flatness at `p`, stripped by
`torsion_flat_package_of_flat_hopf_form` of all point bookkeeping — what remains
is exactly the existence of a finite flat `R`-FORM of the torsion Hopf algebra):
under the hypotheses of `torsion_flat_prolong_of_good_reduction_prime_pow`, the
finite étale Hopf `K`-algebra `HK` of the `p ^ k`-torsion admits a finite flat
Hopf `R`-form. Unlike the unramified case, `H` is NOT the normalization:
division polynomials cannot produce `H` here (part of the torsion group scheme
sits in the kernel of reduction, outside the affine chart), and the integral
closure of `R` in `HK` is in general not a Hopf algebra (for `μ_p` over `ℤ_p`
the normalization has a special fibre with two connected components of lengths
`1` and `p - 1`, which is not a group scheme). The intended construction is the
schematic one of [Katz–Mazur, *Arithmetic moduli of elliptic curves*,
Thm 2.3.1]: good reduction makes the minimal Weierstrass equation an elliptic
scheme `𝓔` over `R`; multiplication by `p ^ k` on `𝓔` is finite locally free of
degree `p ^ (2k)` — the arithmetic input being that
`(Φ n).eval X - ξ * (ΨSq n).eval X` is monic of degree `n²` over `R[ξ]`
together with the fibrewise coprimality `isCoprime_Φ_ΨSq` (proven,
`Fermat.FLT.EllipticCurve.PhiPsiCoprime`) — and `H` is the affine algebra of
its kernel `𝓔[p ^ k]`, glued from the division-polynomial chart and a
formal-group chart `R[[T]]/([p ^ k](T))` at the origin; the identification of
`K ⊗[R] H` with `HK` is Cartier's theorem (étaleness of the generic fibre) plus
the matching of `Kˢᵉᵖ`-points with the torsion, transported through `f`/`hf`
(Galois descent: two finite étale `K`-Hopf algebras with equivariantly
isomorphic point groups are isomorphic). For the Frey curve application
(`R = ℤ_(p)`, `K = ℚ`, `k = 1`) the same object is more concretely the kernel
of `[p]` on the good-reduction Weierstrass model; the `k = 1` specialization
admits no genuine shortcut past the origin chart, because the connected
component of `𝓔[p]` (where the model is NOT étale) is present for every `k`. -/
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
      Nonempty ((K ⊗[R] H) ≃ₐc[K] HK) :=
  sorry

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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsElliptic] [IsSepClosure K Ksep] [DecidableEq Ksep] in
/-- **Ordinates are integral once abscissas are** (PROVEN 2026-07-23; the
`NeZero`-free core of `torsion_ordinate_mem`, needed at the residue
characteristic where that lemma's `[NeZero (n : ResidueField R)]` hypothesis is
unavailable — no torsion hypothesis is needed at all): on the minimal model, an
affine point of `E(Kˢᵉᵖ)` with integral abscissa over a valuation subring `𝒪`
above `R` has integral ordinate, because `y` satisfies the monic `y`-quadratic
of the Weierstrass equation, whose coefficients are integral. -/
theorem WeierstrassCurve.ordinate_mem_of_abscissa_mem
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x y : Ksep} (h : (E⁄Ksep).toAffine.Nonsingular x y)
    (hx : x ∈ 𝒪) : y ∈ 𝒪 := by
  classical
  haveI : E.IsIntegral R := inferInstance
  obtain ⟨Eint, hEint⟩ := (inferInstance : E.IsIntegral R).integral
  have hamem : ∀ z : R, algebraMap K Ksep (algebraMap R K z) ∈ 𝒪 := by
    intro z
    have hmem : algebraMap R K z ∈ (algebraMap R K).range := ⟨_, rfl⟩
    rw [← h𝒪] at hmem
    exact hmem
  have ha1 : (E⁄Ksep).a₁ ∈ 𝒪 := by
    rw [show (E⁄Ksep) = ((Eint⁄K)⁄Ksep) from by rw [hEint]]
    exact hamem _
  have ha2 : (E⁄Ksep).a₂ ∈ 𝒪 := by
    rw [show (E⁄Ksep) = ((Eint⁄K)⁄Ksep) from by rw [hEint]]
    exact hamem _
  have ha3 : (E⁄Ksep).a₃ ∈ 𝒪 := by
    rw [show (E⁄Ksep) = ((Eint⁄K)⁄Ksep) from by rw [hEint]]
    exact hamem _
  have ha4 : (E⁄Ksep).a₄ ∈ 𝒪 := by
    rw [show (E⁄Ksep) = ((Eint⁄K)⁄Ksep) from by rw [hEint]]
    exact hamem _
  have ha6 : (E⁄Ksep).a₆ ∈ 𝒪 := by
    rw [show (E⁄Ksep) = ((Eint⁄K)⁄Ksep) from by rw [hEint]]
    exact hamem _
  set f : Polynomial Ksep := Polynomial.X ^ 2 +
    Polynomial.C ((E⁄Ksep).a₁ * x + (E⁄Ksep).a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + (E⁄Ksep).a₂ * x ^ 2 + (E⁄Ksep).a₄ * x +
      (E⁄Ksep).a₆) with hfdef
  have hd2 : f.natDegree = 2 := by
    rw [hfdef]
    compute_degree!
  have hfne : f ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd2
    exact two_ne_zero hd2.symm
  have hroot : f.eval y = 0 := by
    have heq := (Affine.equation_iff _ _).mp h.1
    rw [hfdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    linear_combination heq
  have hcoeff : ∀ i, f.coeff i ∈ 𝒪 := by
    intro i
    rw [hfdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    match i with
    | 0 =>
      norm_num
      exact add_mem (neg_mem ha6) (add_mem (neg_mem (mul_mem ha4 hx))
        (add_mem (neg_mem (mul_mem ha2 (pow_mem hx 2)))
          (neg_mem (pow_mem hx 3))))
    | 1 =>
      norm_num
      exact add_mem (mul_mem ha1 hx) ha3
    | 2 =>
      norm_num
    | (j + 3) =>
      norm_num
      exact zero_mem _
  have hlc : (f.leadingCoeff)⁻¹ ∈ 𝒪 := by
    have h1 : f.leadingCoeff = 1 := by
      rw [Polynomial.leadingCoeff, hd2, hfdef]
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    rw [h1, inv_one]
    exact one_mem _
  exact 𝒪.mem_of_root_of_inv_leadingCoeff_mem hfne hcoeff hlc hroot

/-- **The kernel of reduction is `p`-power-torsion-free in equal characteristic
`p`** (sorry node; the whole surviving elliptic-curve content of the
equal-characteristic Néron–Ogg–Shafarevich): when `p` vanishes in `K`, a
nonzero `p ^ k`-torsion point of `E(Kˢᵉᵖ)` cannot lie in the kernel of
reduction (non-integral abscissa) over a valuation subring `𝒪` above `R`.
Intended proof: a point with `v(x) < 0` lies in the formal-group chart
`z = -x/y` with `v(z) > 0`; over an equal-characteristic-`p` base the
multiplication-by-`p` power series of the formal group of the minimal model
factors as `[p](T) = g(T^(p^h))` with `h ≥ 1` the height and `g` with unit
linear coefficient (`[p] = V ∘ Frobeniusʰ`), so `[p]` — hence `[p ^ k]` — is
injective on the points of the valuation ideal (a domain), and the only
`p ^ k`-torsion point of the kernel is the origin. Compare the multiplicative
model: `(1 + z)^(p ^ k) = 1 + z^(p ^ k)` has no nonzero root in a domain of
characteristic `p`. -/
theorem WeierstrassCurve.kernel_prime_pow_torsion_of_eqChar
    (p k : ℕ) (hp : p.Prime) (hpK : (p : K) = 0)
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range)
    {x y : Ksep} (h : (E⁄Ksep).toAffine.Nonsingular x y)
    (hx : x ∉ 𝒪)
    (htor : ((p ^ k : ℕ) : ℤ) • (Affine.Point.some x y h : (E⁄Ksep).Point) = 0) :
    False :=
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Equal-characteristic Néron–Ogg–Shafarevich** (DECOMPOSED 2026-07-23 into
the kernel-torsion-freeness leaf `kernel_prime_pow_torsion_of_eqChar` — via the
proven `ordinate_mem_of_abscissa_mem` and the kernel-of-reduction leaf
`kernel_sub_abscissa_notMem_of_residue_eq`; the assembly below is proven): when
`p` vanishes in `K` (so `R` is an equal-characteristic-`p` DVR), every inertia
subgroup above `R` acts trivially on the `p ^ k`-torsion of `E(Kˢᵉᵖ)` — even
though `p ^ k` is NOT invertible in the residue field. The assembly is simpler
than the invertible-order dévissage because the kernel of reduction is entirely
`p`-power-torsion-free here: torsion abscissas are integral (a non-integral
abscissa would BE a nonzero torsion point of the kernel), ordinates follow by
the `y`-quadratic, inertia fixes residues, and if `σP ≠ P` then `σP − P` is a
nonzero `p ^ k`-torsion point of the kernel
(`kernel_sub_abscissa_notMem_of_residue_eq`) — absurd. This is the statement
that `E(Kˢᵉᵖ)[p ^ k]` sees only the maximal étale quotient of the torsion group
scheme, whose points reduce injectively to the residue curve. -/
theorem WeierstrassCurve.torsion_inertia_fixes_of_eqChar
    (p k : ℕ) (hp : p.Prime) (hpK : (p : K) = 0)
    (𝒪 : ValuationSubring Ksep)
    (h𝒪 : (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup K,
      ∀ P ∈ AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ),
        Affine.Point.map (σ : Ksep ≃ₐ[K] Ksep).toAlgHom P = P := by
  classical
  intro σ hσ P hP
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
    -- the coordinates are integral: a non-integral abscissa would be a nonzero
    -- `p ^ k`-torsion point of the kernel of reduction
    have hxm : x ∈ 𝒪 := by
      by_contra hx
      exact WeierstrassCurve.kernel_prime_pow_torsion_of_eqChar R K E Ksep
        p k hp hpK 𝒪 h𝒪 h hx htor
    have hym : y ∈ 𝒪 :=
      WeierstrassCurve.ordinate_mem_of_abscissa_mem R K E Ksep 𝒪 h𝒪 h hxm
    set σf := ((σ : Ksep ≃ₐ[K] Ksep)).toAlgHom
    have hns' : (E⁄Ksep).toAffine.Nonsingular (σf x) (σf y) :=
      (WeierstrassCurve.Affine.baseChange_nonsingular (W := E)
        σf.injective x y).mpr (show (E⁄Ksep).Nonsingular x y from h)
    have hmap : Affine.Point.map σf (Affine.Point.some x y h) =
        (Affine.Point.some (σf x) (σf y) hns' : (E⁄Ksep).Point) :=
      Affine.Point.map_some _ h
    rw [hmap]
    -- the image is torsion
    have hmaptor : ((p ^ k : ℕ) : ℤ) • (Affine.Point.some (σf x) (σf y) hns' :
        (E⁄Ksep).Point) = 0 := by
      rw [← hmap, ← map_zsmul, htor, map_zero]
    -- memberships and residue congruences for the image coordinates
    have hσxm : σf x ∈ 𝒪 := by
      have := hcoe ⟨x, hxm⟩
      rw [← this]
      exact Subtype.mem _
    have hσym : σf y ∈ 𝒪 := by
      have := hcoe ⟨y, hym⟩
      rw [← this]
      exact Subtype.mem _
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
    -- if `σP ≠ P`, the difference is a nonzero `p ^ k`-torsion point of the
    -- kernel of reduction — absurd in equal characteristic
    by_contra hne
    set D : (E⁄Ksep).Point :=
      Affine.Point.some (σf x) (σf y) hns' - Affine.Point.some x y h with hDdef
    have hD0 : D ≠ 0 := sub_ne_zero.mpr hne
    have hDtor : ((p ^ k : ℕ) : ℤ) • D = 0 := by
      rw [hDdef, smul_sub, hmaptor, htor, sub_zero]
    cases hDc : D with
    | zero => exact absurd hDc hD0
    | @some x₃ y₃ h₃ =>
      have hsub : (Affine.Point.some (σf x) (σf y) hns' : (E⁄Ksep).Point) -
          Affine.Point.some x y h = Affine.Point.some x₃ y₃ h₃ := by
        rw [← hDdef]
        exact hDc
      have hx₃ : x₃ ∉ 𝒪 :=
        WeierstrassCurve.kernel_sub_abscissa_notMem_of_residue_eq R K E Ksep 𝒪
          h𝒪 hns' h h₃ hne hσxm hxm hσym hym hrx hry hsub
      have hDtor' : ((p ^ k : ℕ) : ℤ) •
          (Affine.Point.some x₃ y₃ h₃ : (E⁄Ksep).Point) = 0 := by
        rw [← hDc]
        exact hDtor
      exact WeierstrassCurve.kernel_prime_pow_torsion_of_eqChar R K E Ksep
        p k hp hpK 𝒪 h𝒪 h₃ hx₃ hDtor'

/-- **The finite étale torsion package, equal characteristic** (sorry node; the
Galois-correspondence half of the equal-characteristic case — the sibling of
`exists_torsion_etale_package_over_fractionField`, whose hypothesis
`(m : R) ≠ 0` FAILS here since `(p : R) = 0` when `(p : K) = 0`): the
`p ^ k`-torsion Galois module `E(Kˢᵉᵖ)[p ^ k]` — finite of order at most
`p ^ k` in equal characteristic (the étale-quotient points; order `p ^ k` for
ordinary reduction, `1` for supersingular) — is, `Gal(Kˢᵉᵖ/K)`-equivariantly,
the group of `Kˢᵉᵖ`-points of a finite étale Hopf algebra over `K`. The
intended proof is the SAME Grothendieck Galois correspondence as in the
`(m : R) ≠ 0` leaf (equivariant maps `E(Kˢᵉᵖ)[p ^ k] → Kˢᵉᵖ`, evaluation at
orbit representatives): the correspondence needs only finiteness of the torsion
and discreteness of the action, both of which hold in every characteristic;
when either leaf is resolved the other should be aligned with it, ideally by
generalizing the correspondence to any nonzero `m : ℕ`. (The characteristic
hypothesis is stated in `R` — equivalent to `(p : K) = 0` through the injective
`algebraMap R K` — so that the carrier universe `u` stays tied to `R`, exactly
as in the `(m : R) ≠ 0` sibling.) -/
theorem WeierstrassCurve.exists_torsion_etale_package_of_eqChar
    (p k : ℕ) (hp : p.Prime) (hpR : (p : R) = 0) :
    ∃ (HK : Type u) (_ : CommRing HK) (_ : HopfAlgebra K HK)
      (_ : Module.Finite K HK) (_ : Algebra.Etale K HK)
      (f : Additive (WithConv (HK →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : HK →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

/-- **The equal-characteristic prime-power case** (DECOMPOSED 2026-07-22 into
the equal-characteristic Néron–Ogg–Shafarevich leaf
`torsion_inertia_fixes_of_eqChar`, the equal-characteristic Galois-correspondence
leaf `exists_torsion_etale_package_of_eqChar`, and the SHARED curve-free
Hopf-form leaf `exists_finite_flat_hopf_form_of_inertia_fixes` — whose freedom
from any order-invertibility hypothesis is exactly what makes it applicable at
the residue characteristic; the assembly below is proven): the flat-torsion
package at order `p ^ k` when `p` vanishes in `K` itself (so `R` is an equal-
characteristic-`p` DVR, e.g. `𝔽_q[[t]]`; NOT the case of the Frey-curve
application, which has `K = ℚ` — the consumer chain
`torsion_flat_of_good_reduction → isFlatAt_of_hasGoodReduction` only ever
instantiates mixed characteristic, but this leaf is required for the stated
generality of the vendored `torsion_flat_of_good_reduction`, and its hypotheses
are satisfiable (`𝔽_q[[t]]`), so no hypothesis-narrowing or vacuity closure is
honest here). Here `E(Kˢᵉᵖ)[p ^ k]` sees only the maximal étale quotient of the
`p ^ k`-torsion group scheme — its Galois module is unramified (reduction is
injective on its points), so a finite flat — indeed étale — prolongation of the
étale generic fibre exists even at the residue characteristic, by the same
normalization construction as the invertible-order case. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow_of_eqChar
    (p : ℕ) (hp : p.Prime) (_hpu : ¬IsUnit (p : R)) (k : ℕ) (_hk : k ≠ 0)
    (hpK : (p : K) = 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  have hpR : (p : R) = 0 := by
    apply IsFractionRing.injective R K
    rw [map_natCast, map_zero, hpK]
  obtain ⟨HK, iCR, iHopf, iFin, iEt, f, hf⟩ :=
    WeierstrassCurve.exists_torsion_etale_package_of_eqChar R K E Ksep p k hp hpR
  letI := iCR; letI := iHopf; letI := iFin; letI := iEt
  obtain ⟨H, jCR, jHopf, jFin, jFlat, ⟨e⟩⟩ :=
    exists_finite_flat_hopf_form_of_inertia_fixes R K Ksep HK
      (WeierstrassCurve.algHom_comp_eq_of_torsion_inertia_fixes R K E Ksep
        (p ^ k) HK f hf (fun 𝒪 h𝒪 =>
          WeierstrassCurve.torsion_inertia_fixes_of_eqChar R K E Ksep p k hp hpK
            𝒪 h𝒪))
  letI := jCR; letI := jHopf; letI := jFin; letI := jFlat
  exact WeierstrassCurve.torsion_flat_package_of_flat_hopf_form R K E Ksep
    (p ^ k) HK f hf H e

/-- **The residue-characteristic prime-power case** (DECOMPOSED 2026-07-22 along the
characteristic of `K` into the Katz–Mazur prolongation leaf
`torsion_flat_prolong_of_good_reduction_prime_pow` — fed by the shared
Galois-correspondence leaf `exists_torsion_etale_package_over_fractionField` — and the
equal-characteristic leaf `torsion_flat_of_good_reduction_prime_pow_of_eqChar`; the
assembly below is proven): the flat-torsion package for the `p ^ k`-torsion of `E`
when the prime `p` is *not* invertible in `R` (so `p` is the residue characteristic;
for the Frey curve application `R = ℤ_(p)`, `K = ℚ`, `k = 1`, which lands in the
mixed-characteristic branch). -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  by_cases hpK : (p : K) = 0
  -- equal characteristic: the étale-quotient/Cartier-dual leaf
  · exact WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow_of_eqChar
      R K E Ksep p hp hpu k hk hpK
  -- mixed characteristic: the shared étale `K`-package + the Katz–Mazur prolongation
  · have hpR : ((p ^ k : ℕ) : R) ≠ 0 := by
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
/-- (Vendored from the FLT project; DECOMPOSED 2026-07-22 into the three sorried leaves
above by splitting `n` into its `R`-unit part and its residue-characteristic part.)
If `E` is an elliptic curve over the field of fractions `K` of a discrete valuation
ring `R` with good reduction over `R`, then the `n`-torsion of `E` is a finite flat group
scheme: there is a commutative Hopf algebra `H` over `R`, finite and flat as an `R`-module,
whose generic fibre `K ⊗[R] H` is étale over `K` and whose group of `Kˢᵉᵖ`-points (a group
under convolution) is isomorphic, compatibly with the actions of `Gal(Kˢᵉᵖ/K)` on the two
sides, to the `n`-torsion subgroup of `E(Kˢᵉᵖ)`. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction :
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
    have hpkg := WeierstrassCurve.torsion_flat_of_good_reduction_mul R K E Ksep
      (p ^ k) m (Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpm))
      (WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow R K E Ksep p hp hpu k hk0)
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
