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
`Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction` for odd primes and reduced
below to its prime-power core by a proven CRT/Bézout argument — and a pure descent
half: an unramified torsion Galois module of order invertible in the residue field
prolongs to a finite étale (in particular finite flat) Hopf algebra over `R`. The
assembly is proven; the two remaining sorries in this subsection are the prime-power
Néron–Ogg–Shafarevich core and the descent statement, neither of which mentions the
other's mathematics.
-/

/-- **Reduction is injective on prime-power torsion, deep cases** (sorry node): two
`p ^ k`-torsion points of `E(Kˢᵉᵖ)` with integral coordinates and congruent residues in
a valuation subring `𝒪` above `R` are equal, for `p ^ k` invertible in `R` and either
`p = 2` or `k ≥ 2` (the case `p` odd, `k = 1` is PROVEN — via
`WeierstrassCurve.torsion_abscissa_residue_ne` and
`WeierstrassCurve.torsion_ordinate_eq_of_residue_eq` in
`Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction` — and is consumed by the
assembly below through `torsion_unramified_of_good_reduction`, so it is excluded here).

Intended proof (dévissage to the prime layer plus a formal-group valuation estimate):
the difference `T = P₁ - P₂` of two congruent integral torsion points lies in the
"kernel of reduction" — concretely, if `T ≠ 0` its abscissa has negative valuation:
in the chord construction for `P₁ + (-P₂)` the denominator `x₁ - x₂ ∈ 𝔪` while the
numerator is congruent to `ψ₂(P₂) mod 𝔪`, giving `v(x(T)) = 2 v(λ) < 0` when
`ψ₂(P₂) ∉ 𝔪`, with the near-2-torsion case `ψ₂(P₂) ∈ 𝔪` handled by comparing the
valuations of the two ordinate roots (for `p = 2` this ordinate-flip analysis is the
whole content). On the other hand a suitable multiple `p ^ j • T` is a NONZERO
`p`-torsion point (tower dévissage), whose abscissa is a root of `ΨSq p` — of unit
leading coefficient `p²` since `p ∈ Rˣ` — hence integral over `𝒪`: contradiction.
The division-polynomial coprimality input at composite order, `isCoprime_Φ_ΨSq`, is
proven (`Fermat.FLT.EllipticCurve.PhiPsiCoprime`; over the residue field `Δ` is a unit
by good reduction). -/
theorem WeierstrassCurve.torsion_eq_of_residue_eq_of_prime_pow_deep
    (p k : ℕ) (hp : p.Prime) (hpk : IsUnit ((p ^ k : ℕ) : R)) (hk : k ≠ 0)
    (hdeep : p = 2 ∨ 2 ≤ k)
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
    x₁ = x₂ ∧ y₁ = y₂ :=
  sorry

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

/-- **Unramified implies flat, order invertible in the residue field** (sorry node; the
descent half of the étale case — nothing about elliptic curves remains in its intended
proof, which applies to any finite abelian Galois module): if every inertia subgroup
above `R` acts trivially on `E(Kˢᵉᵖ)[m]` and `m` is invertible in `R`, the `m`-torsion
prolongs to a finite étale (in particular finite flat) Hopf algebra over `R`. Intended
proof: Galois-descend the split Hopf `K`-algebra `Maps(E(Kˢᵉᵖ)[m], Kˢᵉᵖ)` of functions
on the torsion to the finite étale Hopf algebra `H_K` of Galois-equivariant maps
`E(Kˢᵉᵖ)[m] → Kˢᵉᵖ` (the action factors through a finite quotient of `Gal(Kˢᵉᵖ/K)`, so
`K ⊗[?] H_K → Maps` is an isomorphism), then take `H` to be the integral closure of `R`
in `H_K`: the splitting field of the torsion is unramified over `K` by the hypothesis
(its inertia acts trivially) and its degree divides `#GL₂(ℤ/m)`, whose relevant part is
prime to the residue characteristic since `m` is a unit in `R`, so the normalization is
finite étale over `R` and comultiplication preserves integrality. -/
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
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

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

/-- **The residue-characteristic prime-power case** (sorry node; the mathematical core of
flatness at `p`): the flat-torsion package for the `p ^ k`-torsion of `E` when the prime
`p` is *not* invertible in `R` (so `p` is the residue characteristic; for the Frey curve
application `R = ℤ_(p)`, `K = ℚ`, `k = 1`). Division polynomials cannot produce `H` here
(part of the torsion group scheme sits in the kernel of reduction, outside the affine
chart), and there is no cheap commutative-algebra description of `H` inside its generic
fibre — e.g. the integral closure of `R` in the generic fibre is in general *not* a Hopf
algebra (for `μ_p` over `ℤ_p` the normalization has a special fibre with two connected
components of lengths `1` and `p - 1`, which is not a group scheme). The intended proof
is the schematic one of [Katz–Mazur, *Arithmetic moduli of elliptic curves*, Thm 2.3.1]:
good reduction makes the minimal Weierstrass equation an elliptic scheme `𝓔` over `R`;
multiplication by `p ^ k` on `𝓔` is finite locally free of degree `p ^ (2k)` — the
arithmetic input being that `(Φ n).eval X - ξ * (ΨSq n).eval X` is monic of degree `n²`
over `R[ξ]` together with the fibrewise coprimality `isCoprime_Φ_ΨSq` proven at the
bottom of this file — and `H` is the affine algebra of its kernel `𝓔[p ^ k]`, glued from
the division-polynomial chart and a formal-group chart `R[[T]]/([p ^ k](T))` at the
origin. Étaleness of the generic fibre for `K` of characteristic `0` is Cartier's
theorem; in characteristic `p` one must instead take the flat closure of the étale part,
as discussed in the module docstring. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction_prime_pow
    (p : ℕ) (hp : p.Prime) (hpu : ¬IsUnit (p : R)) (k : ℕ) (hk : k ≠ 0) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point ((p ^ k : ℕ) : ℤ)),
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

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
