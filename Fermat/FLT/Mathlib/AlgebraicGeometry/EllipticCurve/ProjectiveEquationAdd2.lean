/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveAddition
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveEquationAdd
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The SECOND chord–tangent addition law preserves the Weierstrass equation

`WeierstrassCurve.Projective.equation_add2XYZ` —
`W.Equation P → W.Equation Q → W.Equation (W.add2XYZ P Q)` over any `[CommRing R]`,
for the Bosma–Lenstra law of the line `Y = 0` defined in
`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/ProjectiveAddition.lean`.

## Why this is its own module

It is the THIRD sibling of the pair split apart at the release-10 integration:
it needs `equation_addXYZ` (from `ProjectiveEquationAdd.lean`) *and* the second
law (from `ProjectiveAddition.lean`), and those two must not import each other —
each carries a multi-minute normalisation and their being siblings is what keeps
the build's critical path down to the larger of the two rather than their sum.
Everything in THIS module is cheap (seconds), so adding it after them costs
essentially nothing.

## THE ROUTE: no large `ring1` anywhere, and why the recorded cost wall does not apply

A predecessor generated the `Singular` certificate for
`W(add2X, add2Y, add2Z) ∈ (W(P), W(Q))` — cofactors of 158 and 280 monomials,
denominator-free — and measured `ring1` on it TWICE, in two different monomial
orders: **killed at 4 h 08 m / 294 GB and 3 h 52 m / 298 GB**, both still
allocating.  The dominant cost is not the certificate but forming
`W(add2X, add2Y, add2Z)` at all: `add2Y ^ 2 * add2Z` alone is `74 * 74 * 43`
monomial products collected into a ~20 000-term normal form.

The route taken here **never expands any of those polynomials**.  Write
`u, v, w` for `add2X, add2Y, add2Z` and `X, Y, Z` for `addX, addY, addZ`.  Then:

* `add2X_mul_addZ` and `add2Y_mul_addZ` (both PROVEN, cofactors of 27/21 and
  28/35 monomials) say `u * Z = w * X` and `v * Z = w * Y`;
* the Weierstrass cubic `W` is homogeneous of degree `3`, so
  `Z ^ 3 * W(u, v, w) = W(u * Z, v * Z, w * Z) = W(w * X, w * Y, w * Z)
  = w ^ 3 * W(X, Y, Z)`;
* `equation_addXYZ` kills the right-hand side.

Every `ring1` in that chain sees `u, v, w, X, Y, Z, a₁, …, a₆` as ATOMS — twelve
of them, in an identity of degree four — so the whole thing verifies in seconds
(`wpoly_of_proportional` and `addZ_pow_mul_equationPoly_add2XYZ` below).

**The docstring this replaces recorded the same route as "measurably WORSE, do
not take", at 412 929 monomials.  That figure is the cost of EXPANDING
`addZ ^ 3 * W(add2XYZ) - add2Z ^ 3 * W(addXYZ)`, which is exactly what one must
not do:** the identity is a formal consequence of the two proportionalities with
the six forms kept opaque, and costs nothing.

## What is left: cancelling `addZ ^ 3`

An arbitrary commutative ring does not license it, and no further identity among
these forms can supply it — the degeneracy locus of the first law (the diagonal
`P = Q`) is precisely where every annihilator of `W(add2XYZ)` obtainable this way
vanishes, and `equation_addXYZ` is the only "seed" available, so nothing here
sees the diagonal.

So the cancellation is done ONCE, in the UNIVERSAL ring — the generic Weierstrass
curve with two generic marked points,
`ℤ[a₁, a₂, a₃, a₄, a₆, Px, Py, Pz, Qx, Qy, Qz] ⧸ (W(P), W(Q))` — which is an
integral domain, and in which `addZ ≠ 0` (witnessed by `y² = x³ + 1` with
`[0 : 1 : 1]` and `[2 : 3 : 1]`, where `addZ = -8`).  Every `(R, W', P, Q)` with
`W'.Equation P` and `W'.Equation Q` is a specialisation of it, so the identity
transports.  That reduces the whole leaf to the single standard fact
`Universal.idl_isPrime`, which is in turn PROVEN below from two shallower leaves —
`Universal.mem_idl_of_X7_mul_mem` (`Pz` is a non-zerodivisor modulo the ideal) and
`Universal.exists_pow_X7_mul_mem_idl` (the ideal is prime once `Pz` is inverted).
See the section docstring at `Universal.idl_ne_top` for a complete route in which
BOTH halves are elementary: monic division for the first, degree-one primitivity
over a UFD for the second.
-/

@[expose] public section

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve R} {P Q : Fin 3 → R}

/-! ## Naturality of the second law under a ring homomorphism -/

/-- The `X`-coordinate of the second law commutes with base change. -/
theorem map_add2X {S : Type*} [CommRing S] (f : R →+* S) (W' : WeierstrassCurve R)
    (P Q : Fin 3 → R) : add2X (map W' f) (f ∘ P) (f ∘ Q) = f (add2X W' P Q) := by
  simp only [add2X]
  simp only [map_ofNat, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

/-- The `Y`-coordinate of the second law commutes with base change. -/
theorem map_add2Y {S : Type*} [CommRing S] (f : R →+* S) (W' : WeierstrassCurve R)
    (P Q : Fin 3 → R) : add2Y (map W' f) (f ∘ P) (f ∘ Q) = f (add2Y W' P Q) := by
  simp only [add2Y]
  simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

/-- The `Z`-coordinate of the second law commutes with base change. -/
theorem map_add2Z {S : Type*} [CommRing S] (f : R →+* S) (W' : WeierstrassCurve R)
    (P Q : Fin 3 → R) : add2Z (map W' f) (f ∘ P) (f ∘ Q) = f (add2Z W' P Q) := by
  simp only [add2Z]
  simp only [map_ofNat, map_neg, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

/-- The second law commutes with base change — the analogue of mathlib's
`map_addXYZ`. -/
theorem map_add2XYZ {S : Type*} [CommRing S] (f : R →+* S) (W' : WeierstrassCurve R)
    (P Q : Fin 3 → R) : add2XYZ (map W' f) (f ∘ P) (f ∘ Q) = f ∘ add2XYZ W' P Q := by
  simp only [add2XYZ, map_add2X, map_add2Y, map_add2Z, comp_fin3]

/-! ## The cheap half: `addZ ^ 3` annihilates the second law's Weierstrass value -/

/-- **Homogeneity of the Weierstrass cubic, applied to a proportional pair**
(PROVEN).  Nothing here knows what `u, v, w, X, Y, Z` are: they are twelve free
ring elements, which is exactly what makes this cheap when they are instantiated
at polynomials of 43–74 monomials. -/
theorem wpoly_of_proportional {S : Type*} [CommRing S] (a₁ a₂ a₃ a₄ a₆ u v w X Y Z : S)
    (h1 : u * Z = w * X) (h2 : v * Z = w * Y)
    (h3 : Y ^ 2 * Z + a₁ * X * Y * Z + a₃ * Y * Z ^ 2
      - (X ^ 3 + a₂ * X ^ 2 * Z + a₄ * X * Z ^ 2 + a₆ * Z ^ 3) = 0) :
    Z ^ 3 * (v ^ 2 * w + a₁ * u * v * w + a₃ * v * w ^ 2
      - (u ^ 3 + a₂ * u ^ 2 * w + a₄ * u * w ^ 2 + a₆ * w ^ 3)) = 0 := by
  have e1 : Z ^ 3 * (v ^ 2 * w + a₁ * u * v * w + a₃ * v * w ^ 2
      - (u ^ 3 + a₂ * u ^ 2 * w + a₄ * u * w ^ 2 + a₆ * w ^ 3))
      = (v * Z) ^ 2 * (w * Z) + a₁ * (u * Z) * (v * Z) * (w * Z)
        + a₃ * (v * Z) * (w * Z) ^ 2
        - ((u * Z) ^ 3 + a₂ * (u * Z) ^ 2 * (w * Z) + a₄ * (u * Z) * (w * Z) ^ 2
          + a₆ * (w * Z) ^ 3) := by ring
  rw [e1, h1, h2]
  linear_combination w ^ 3 * h3

/-- **`addZ ^ 3` annihilates the second law's Weierstrass value** (PROVEN, over an
arbitrary commutative ring, in seconds).  This is the whole of
`equation_add2XYZ` except for one cancellation. -/
theorem addZ_pow_mul_equationPoly_add2XYZ (hP : Equation W' P) (hQ : Equation W' Q) :
    addZ W' P Q ^ 3 *
      (add2Y W' P Q ^ 2 * add2Z W' P Q
        + W'.a₁ * add2X W' P Q * add2Y W' P Q * add2Z W' P Q
        + W'.a₃ * add2Y W' P Q * add2Z W' P Q ^ 2
        - (add2X W' P Q ^ 3 + W'.a₂ * add2X W' P Q ^ 2 * add2Z W' P Q
          + W'.a₄ * add2X W' P Q * add2Z W' P Q ^ 2
          + W'.a₆ * add2Z W' P Q ^ 3)) = 0 := by
  have h3 := (equation_iff _).mp (equation_addXYZ (W' := W') (P := P) (Q := Q) hP hQ)
  rw [addXYZ_X, addXYZ_Y, addXYZ_Z] at h3
  exact wpoly_of_proportional _ _ _ _ _ _ _ _ _ _ _ (add2X_mul_addZ hP hQ)
    (add2Y_mul_addZ hP hQ) h3

/-! ## The universal Weierstrass curve with two marked points

Every quadruple `(R, W', P, Q)` with `W'.Equation P` and `W'.Equation Q` is a
specialisation of one universal object, so a ring-level identity in that object
transports to all of them. -/

namespace Universal

open MvPolynomial

/-- The eleven indeterminates `a₁, a₂, a₃, a₄, a₆, Px, Py, Pz, Qx, Qy, Qz`. -/
abbrev Poly : Type := MvPolynomial (Fin 11) ℤ

/-- The generic Weierstrass curve. -/
noncomputable def curve : WeierstrassCurve Poly := ⟨X 0, X 1, X 2, X 3, X 4⟩

/-- The generic first point. -/
noncomputable def pt₁ : Fin 3 → Poly := ![X 5, X 6, X 7]

/-- The generic second point. -/
noncomputable def pt₂ : Fin 3 → Poly := ![X 8, X 9, X 10]

/-- The values a specialisation sends the eleven indeterminates to. -/
def vals {R : Type*} (a₁ a₂ a₃ a₄ a₆ p₀ p₁ p₂ q₀ q₁ q₂ : R) : Fin 11 → R
  | 0 => a₁ | 1 => a₂ | 2 => a₃ | 3 => a₄ | 4 => a₆
  | 5 => p₀ | 6 => p₁ | 7 => p₂ | 8 => q₀ | 9 => q₁ | 10 => q₂

variable (W' P Q) in
/-- The specialisation `Poly →+* R` at a Weierstrass curve and two points. -/
noncomputable def spec : Poly →+* R :=
  eval₂Hom (Int.castRingHom R) (vals W'.a₁ W'.a₂ W'.a₃ W'.a₄ W'.a₆ (P 0) (P 1) (P 2)
    (Q 0) (Q 1) (Q 2))

theorem spec_curve : map curve (spec W' P Q) = W' := by
  cases W'
  simp [curve, spec, vals, WeierstrassCurve.map]

theorem spec_pt₁ : (spec W' P Q) ∘ pt₁ = P := by
  funext i; fin_cases i <;> simp [pt₁, spec, vals]

theorem spec_pt₂ : (spec W' P Q) ∘ pt₂ = Q := by
  funext i; fin_cases i <;> simp [pt₂, spec, vals]

/-- The first defining relation: the generic first point lies on the generic curve. -/
noncomputable def gen₁ : Poly := eval pt₁ (polynomial curve)

/-- The second defining relation: the generic second point lies on the generic curve. -/
noncomputable def gen₂ : Poly := eval pt₂ (polynomial curve)

theorem spec_gen₁ (hP : Equation W' P) : spec W' P Q gen₁ = 0 := by
  have h : eval ((spec W' P Q) ∘ pt₁) (polynomial (map curve (spec W' P Q))) = 0 := by
    rw [spec_curve, spec_pt₁]; exact hP
  rwa [map_polynomial, eval_map, ← eval₂_comp] at h

theorem spec_gen₂ (hQ : Equation W' Q) : spec W' P Q gen₂ = 0 := by
  have h : eval ((spec W' P Q) ∘ pt₂) (polynomial (map curve (spec W' P Q))) = 0 := by
    rw [spec_curve, spec_pt₂]; exact hQ
  rwa [map_polynomial, eval_map, ← eval₂_comp] at h

/-- The universal ideal `(W(P), W(Q))`. -/
noncomputable def idl : Ideal Poly := Ideal.span {gen₁, gen₂}

theorem spec_of_mem_idl (hP : Equation W' P) (hQ : Equation W' Q) {a : Poly} (ha : a ∈ idl) :
    spec W' P Q a = 0 := by
  rw [idl, Ideal.mem_span_pair] at ha
  obtain ⟨c, d, rfl⟩ := ha
  simp [spec_gen₁ hP, spec_gen₂ hQ]

/-- The universal ring: the generic Weierstrass curve with two generic points on it. -/
abbrev Univ : Type := Poly ⧸ idl

/-- The universal Weierstrass curve. -/
noncomputable def ucurve : WeierstrassCurve Univ := map curve (Ideal.Quotient.mk idl)

/-- The universal first point. -/
noncomputable def upt₁ : Fin 3 → Univ := (Ideal.Quotient.mk idl) ∘ pt₁

/-- The universal second point. -/
noncomputable def upt₂ : Fin 3 → Univ := (Ideal.Quotient.mk idl) ∘ pt₂

theorem map_ucurve {S : Type*} [CommRing S] (g : Univ →+* S) :
    map ucurve g = map curve (g.comp (Ideal.Quotient.mk idl)) := rfl

theorem comp_upt₁ {S : Type*} [CommRing S] (g : Univ →+* S) :
    g ∘ upt₁ = (g.comp (Ideal.Quotient.mk idl)) ∘ pt₁ := rfl

theorem comp_upt₂ {S : Type*} [CommRing S] (g : Univ →+* S) :
    g ∘ upt₂ = (g.comp (Ideal.Quotient.mk idl)) ∘ pt₂ := rfl

theorem equation_upt₁ : Equation ucurve upt₁ := by
  have h : (Ideal.Quotient.mk idl) gen₁ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  show eval upt₁ (polynomial ucurve) = 0
  rw [ucurve, upt₁, map_polynomial, eval_map, ← eval₂_comp]
  exact h

theorem equation_upt₂ : Equation ucurve upt₂ := by
  have h : (Ideal.Quotient.mk idl) gen₂ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  show eval upt₂ (polynomial ucurve) = 0
  rw [ucurve, upt₂, map_polynomial, eval_map, ← eval₂_comp]
  exact h

/-! ### A concrete specialisation

`y² = x³ + 1` over `ℤ` with the two points `[0 : 1 : 1]` and `[2 : 3 : 1]`.  It is
used twice: to see that the universal ideal is PROPER, and to see that the first
law's `Z`-coordinate does not vanish universally (it specialises to `-8`). -/

/-- `[0 : 1 : 1]` lies on `y² = x³ + 1`. -/
theorem equation_test₁ : Equation (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ) ![0, 1, 1] := by
  rw [equation_iff]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- `[2 : 3 : 1]` lies on `y² = x³ + 1`. -/
theorem equation_test₂ : Equation (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ) ![2, 3, 1] := by
  rw [equation_iff]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/-- **The universal ideal is proper** (PROVEN).  If `1 ∈ idl` then the
specialisation to `y² = x³ + 1` at `[0 : 1 : 1]`, `[2 : 3 : 1]` would give
`(1 : ℤ) = 0`. -/
theorem idl_ne_top : idl ≠ ⊤ := by
  intro h
  have h1 : (1 : Poly) ∈ idl := (Ideal.eq_top_iff_one idl).mp h
  have h0 := spec_of_mem_idl equation_test₁ equation_test₂ h1
  rw [map_one] at h0
  exact one_ne_zero h0

/-! ### The universal ideal is prime

Equivalently: the generic Weierstrass curve with two generic marked points is an
INTEGRAL scheme.  This is the sole remaining content of `equation_add2XYZ`.

## THE ROUTE: invert `Pz`, and everything becomes a primitivity argument

The docstring this replaces proposed the tower
`Poly ⧸ idl ≅ (B[Px] ⧸ (f₁))[Qx] ⧸ (f₂)` over
`B = ℤ[a₁, a₂, a₃, a₄, a₆, Py, Pz, Qy, Qz]`, and stopped at its second step —
"`f₂` irreducible over `C = B[Px] ⧸ (f₁)`; **this half is the real work**, because
`C` need not be a UFD, so the primitivity argument is unavailable".

**`C` DOES become a UFD once `Pz = X 7` is inverted**, and that is the whole
difficulty.  `f₁` is of degree `1` in `a₆` with coefficient `Pz³`; so in
`C[1/Pz]` the relation `f₁ = 0` simply SOLVES for `a₆`, and

  `C[1/Pz] ≅ ℤ[a₁, a₂, a₃, a₄, Py, Qy, Qz, Px][Pz^{±1}]`,

a localisation of a polynomial ring — a UFD.  So both halves of the tower are the
same easy kind of argument, and the leaf splits into a *localised primality*
statement and a *saturation* statement, which is the decomposition below.

### Half one: primality after inverting `Pz` (`exists_pow_X7_mul_mem_idl`)

Inverting `Pz` and eliminating `a₆` by `gen₁` turns the second generator into

  `h := Pz ^ 3 * gen₂ - Qz ^ 3 * gen₁`

(the `a₆` terms cancel, so `h` does not involve `a₆ = X 4`), and

  `Poly[1/Pz] ⧸ idl ≅ (ℤ[a₁, a₂, a₃, a₄, Px, Py, Qx, Qy, Qz][Pz^{±1}]) ⧸ (h)`.

`h` is of degree `1` in `a₄ = X 3`, over the UFD
`ℤ[a₁, a₂, a₃, Px, Py, Pz, Qx, Qy, Qz]`, with

* coefficient `Pz ^ 2 * Qz ^ 2 * (Px * Qz - Qx * Pz)`;
* `a₄`-free part `c = Pz ^ 3 * g₂ - Qz ^ 3 * g₁`, where `gᵢ` is `genᵢ` with
  `a₄ = a₆ = 0`.

It is PRIMITIVE, i.e. none of the three prime factors of the coefficient divides
`c` — and this is the only computation in the whole route:

* `Pz ∤ c`, since `g₁ ≡ -Px ^ 3 (mod Pz)`, so `c ≡ Px ^ 3 * Qz ^ 3 (mod Pz)`;
* `Qz ∤ c`, since `g₂ ≡ -Qx ^ 3 (mod Qz)`, so `c ≡ -Pz ^ 3 * Qx ^ 3 (mod Qz)`;
* `(Px * Qz - Qx * Pz) ∤ c` — this factor is itself irreducible (degree `1` in
  `Px` with coefficient `Qz`, and `Qz ∤ Qx * Pz`), and substituting the generic
  point `Px = t * Pz`, `Qx = t * Qz` of the hypersurface it cuts out gives

  `c = Pz * Qz * (Pz * Qy - Qz * Py) * (Pz * Qy + Qz * Py + (a₁ * t + a₃) * Pz * Qz)`,

  which is not `0` (the `a₂` and `t ^ 3` contributions cancel identically).

A primitive polynomial of degree `1` over a UFD is irreducible, hence prime; and
`h` stays prime after `Pz` is inverted because `Pz ∤ h` (indeed
`h ≡ Px ^ 3 * Qz ^ 3 (mod Pz)`).

### Half two: `Pz` is a non-zerodivisor modulo `idl` (`mem_idl_of_X7_mul_mem`)

This is what lets the localised statement be contracted back.  **It needs no
primality and no UFD at all** — only that division by a MONIC polynomial has a
unique remainder, applied twice.  Write `f₁ = -gen₁`, `f₂ = -gen₂`, which are
monic cubics in `Px` resp. `Qx` over `B = ℤ[a₁, a₂, a₃, a₄, a₆, Py, Pz, Qy, Qz]`,
in DISJOINT variables (`f₁` does not involve `Qx`, nor `f₂` `Px`).

*Normal form.*  Dividing by `f₁` in `Px` and then by `f₂` in `Qx` writes any
`a ∈ Poly = B[Px, Qx]` as `a = q₁ f₁ + q₂ f₂ + r` with
`deg_Px r ≤ 2` and `deg_Qx r ≤ 2`.

*Uniqueness.*  If `g ∈ idl` has `deg_Px g ≤ 2` and `deg_Qx g ≤ 2` then `g = 0`.
Indeed `B[Qx] ⧸ (f₂) =: C₂` is `B`-free on `1, Qx, Qx²` (`f₂` monic), and
`C₂[Px] ⧸ (f₁)` is `C₂`-free on `1, Px, Px²` (`f₁` monic).  The image of `g` in
the latter is `0`, and `g` has `Px`-degree `≤ 2`, so already `g = 0` in `C₂[Px]`;
each `Px`-coefficient of `g` therefore vanishes in `C₂` while having
`Qx`-degree `≤ 2`, hence is `0` in `B[Qx]`.

Given those two: from `Pz * a ∈ idl`, put `a` in normal form; then `Pz * r ∈ idl`
and `Pz * r` still has both degrees `≤ 2`, so `Pz * r = 0`, so `r = 0` (`Poly` is
a domain), so `a ∈ idl`.

The same argument shows more, and the stronger form may be worth stating: `Poly ⧸ idl`
is a FREE `B`-module on the nine monomials `Px^i Qx^j`, `i, j ≤ 2`, so EVERY nonzero
element of `B` is a non-zerodivisor modulo `idl` — `Pz` is nothing special.

### What each half needs from mathlib

Half two needs only `Polynomial.eq_zero_of_dvd_of_degree_lt` and
`Polynomial.modByMonic` (or `AdjoinRoot.powerBasis'`, which packages the freeness
directly).

Half one's degree-one step is already in mathlib in exactly the form wanted, and
does NOT have to go through Gauss's lemma:

  `Polynomial.irreducible_C_mul_X_add_C : a ≠ 0 → IsRelPrime a b →`
    `Irreducible (C a * X + C b)`

(`Mathlib/Algebra/Polynomial/RingDivision.lean`; the underlying
`irreducible_of_degree_eq_one_of_isRelPrime_coeff` takes any degree-one `p`).
`IsRelPrime a b` — every common divisor is a unit — is precisely the primitivity
check computed above, with `a = Pz ^ 2 * Qz ^ 2 * (Px * Qz - Qx * Pz)` and
`b = c`.  Irreducible then upgrades to Prime because the base is a UFD
(`UniqueFactorizationMonoid.irreducible_iff_prime`).

### How half one was ACTUALLY proven (2026-07-31): NO LOCALISATION, NO `Fin 10`

The plan above ended "what is left is the explicit isomorphism
`Poly[1/Pz] ⧸ idl ≅ (…)[Pz^{±1}] ⧸ (h)`", and the bookkeeping subsection below
was written for the fight that isomorphism implies.  **Neither was needed, and
the whole `Fin 11` → `B[Px][Qx]` re-presentation was avoided.**  See `SatPrime`.

Two moves did it.

*First: `Poly ↪ Poly[T]`, not `Poly ≃ E[T]`.*  `SatPrime.peel k` is the ring map
`Poly →ₐ[ℤ] Polynomial Poly` sending `X k ↦ T` and every other `X i ↦ C (X i)`.
It is NOT surjective, so it is not the structural isomorphism — but it is
**injective, with an explicit retraction** (`Polynomial.eval (X k)`), and that is
all the two uses need.  The base ring stays `Poly` itself, so there is no second
index convention and no `renameEquiv`/`finSuccEquiv` juggling anywhere: `peel 4 u`
is literally `C u` for any `u` written in the `X i`, `i ≠ 4`.  Irreducibility does
not transfer along a non-surjection, but PRIMALITY transfers *downwards* through a
retraction (`SatPrime.prime_of_peel_prime`): from `peel k p ∣ peel k a` apply the
retraction to get `p ∣ a`.  `Xfree k`, "no `X k` occurs", is then the subalgebra
where `peel k` agrees with `C`, so closure under `+ - * ^` is free.

*Second: saturate by hand instead of localising.*  Inverting `Pz` is only ever
used to divide by the leading coefficient of `gen₁` in `a₆`, which is `-Pz ^ 3`.
So do exactly that and keep the cofactor: `SatPrime.exists_reduction` says every
`a` satisfies `Pz ^ n * a ≡ r (mod gen₁)` with `r` free of `a₆`, proved by
`MvPolynomial.induction_on` (the `X 4` step multiplies by `Pz ^ 3` and rewrites
`Pz ^ 3 * a₆ = u - gen₁`).  Because `gen₁` has degree EXACTLY `1` in `a₆`, an
`a₆`-free multiple of `gen₁` is `0` (`SatPrime.eq_zero_of_mem_Xfree_of_mem_span`),
which turns congruences into equations.  The leaf then falls out of `Prime hpoly`
plus `¬ hpoly ∣ Pz` with no localisation object ever constructed.

*Third, and the cheapest trick here:* every non-divisibility the primitivity check
needs — `Pz ∤ c`, `Qz ∤ c`, `(Px Qz - Qx Pz) ∤ c`, `hpoly ∤ Pz` — is discharged by
evaluating at ONE integer point where the divisor vanishes and the dividend does
not (`SatPrime.not_dvd_of_eval`).  No `Singular` certificate is transcribed; the
CAS results quoted above only told us which points to look for.  In particular the
generic-point substitution `Px = t Pz`, `Qx = t Qz` never appears in Lean — it was
only how the point `(Px, Py, Pz, Qx, Qy, Qz) = (0, 0, 1, 0, 1, 1)` was found.

### For HALF TWO, which is still open: `peel` is probably your bookkeeping fix too

The advice this subsection used to give — "if the `Fin 11` bookkeeping resists,
re-present the universal ring as `Polynomial (Polynomial (MvPolynomial (Fin 9) ℤ))`
by construction, rebuilding `curve`, `pt₁`, `pt₂`, `vals`, `spec` and their
specialisation lemmas" — is still AVAILABLE and nothing below `idl` depends on how
`Poly` is presented.  But it is now the second-choice move, because half one paid
none of that cost.

`SatPrime.peel 5` and `SatPrime.peel 8` are `Poly ↪ Poly[T]` sending `Px` resp.
`Qx` to `T`, and under them `-gen₁` and `-gen₂` are visibly MONIC of degree `3`
(their `Px ^ 3`, `Qx ^ 3` coefficients are `1`) — which is exactly the hypothesis
`Polynomial.modByMonic` and `Polynomial.eq_zero_of_dvd_of_degree_lt` want, and it
is one `simp` away rather than a refactor of the module.  The catch to know in
advance: `peel` is injective but NOT surjective, so anything you prove upstairs
must come back down through the retraction `Polynomial.eval (X k)` (see
`SatPrime.peel_dvd_cancel` and `SatPrime.prime_of_peel_prime` for the two shapes
that worked).  Degree and freeness statements come back fine; a statement that
quantifies over ALL of `Poly[T]` does not.

### Two facts recovered from the docstring this section replaced

Both were recorded on `main` on 2026-07-30 against the earlier "invert `Pz`"
sketch, and they survive the change of route.

* *Why the `ℤ[…]`-freeness of half two is mechanical.*  `{gen₁, gen₂}` is already
  a Gröbner basis for the degree-reverse-lex order: the leading terms are `Px ^ 3`
  and `Qx ^ 3`, which are coprime, so the single S-pair reduces to zero by
  Buchberger's first criterion.  Equivalently `(gen₁, gen₂)` is a regular
  sequence, so `Poly ⧸ idl` is a complete intersection — Cohen–Macaulay and
  unmixed.
* *Do not expect the CAS to settle half two.*  `Singular`'s `quotient(idl, Pz)`
  and `minAssGTZ(idl)` were both killed at 900 s in these eleven variables.

Note that only a WEAKER statement than `idl.IsPrime` is actually consumed below,
and a proof of it would close the node just as well: that `addZ ucurve upt₁ upt₂`
is a non-zerodivisor in `Univ`. -/

/-- **`Pz = X 7` is a non-zerodivisor modulo the universal ideal** (sorry leaf).
See the section docstring above for a complete elementary proof: `gen₁` and `gen₂`
are monic cubics in `Px` resp. `Qx` up to sign, so every `a` has a normal form of
bidegree `≤ (2, 2)` modulo `idl`, and a bidegree-`≤ (2, 2)` element of `idl` is
`0`.  No primality and no UFD are involved — only uniqueness of division by a
monic polynomial, twice. -/
theorem mem_idl_of_X7_mul_mem {a : Poly} (ha : X 7 * a ∈ idl) : a ∈ idl := sorry

/-! ### Machinery for `exists_pow_X7_mul_mem_idl`

Everything in `SatPrime` exists to prove that one leaf; it is namespaced so that
the sibling leaf `mem_idl_of_X7_mul_mem`, which is owned elsewhere and needs a
normal-form development of its own, cannot collide with these names. -/

namespace SatPrime

/-- View `Poly` inside `Poly[T]` with `X k ↦ T` and every other `X i ↦ C (X i)`. -/
noncomputable def peel (k : Fin 11) : Poly →ₐ[ℤ] Polynomial Poly :=
  aeval (fun i => if i = k then Polynomial.X else Polynomial.C (X i))

@[simp] theorem peel_X_self (k : Fin 11) : peel k (X k) = Polynomial.X := by
  simp [peel]

@[simp] theorem peel_X_of_ne {k i : Fin 11} (h : i ≠ k) :
    peel k (X i) = Polynomial.C (X i) := by
  simp [peel, h]

/-- The retraction: substitute `T ↦ X k`. -/
theorem peel_leftInverse (k : Fin 11) (x : Poly) :
    Polynomial.eval (X k) (peel k x) = x := by
  have : (Polynomial.evalRingHom (X k)).comp (peel k : Poly →+* Polynomial Poly)
      = RingHom.id Poly := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [peel]
    · intro i; by_cases h : i = k <;> simp [peel, h]
  exact congrArg (fun f => f x) this

theorem peel_injective (k : Fin 11) : Function.Injective (peel k) :=
  Function.LeftInverse.injective (peel_leftInverse k)

theorem peel_dvd_cancel {k : Fin 11} {a b : Poly} (h : peel k a ∣ peel k b) : a ∣ b := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Polynomial.eval (X k) g, ?_⟩
  have := congrArg (Polynomial.eval (X k)) hg
  simpa [peel_leftInverse] using this

/-- `Xfree k` : the elements of `Poly` in which `X k` does not occur. -/
noncomputable def Xfree (k : Fin 11) : Subalgebra ℤ Poly :=
  AlgHom.equalizer (peel k)
    ((Polynomial.CAlgHom (R := Poly) (A := Poly)).restrictScalars ℤ)

theorem mem_Xfree_iff {k : Fin 11} {x : Poly} :
    x ∈ Xfree k ↔ peel k x = Polynomial.C x := Iff.rfl

theorem X_mem_Xfree {k i : Fin 11} (h : i ≠ k) : X i ∈ Xfree k := by
  rw [mem_Xfree_iff, peel_X_of_ne h]

/-! ## The two generators, written out -/

/-- The `a₆`-free part of `gen₁`. -/
noncomputable def upoly : Poly :=
  X 6 ^ 2 * X 7 + X 0 * X 5 * X 6 * X 7 + X 2 * X 6 * X 7 ^ 2
    - (X 5 ^ 3 + X 1 * X 5 ^ 2 * X 7 + X 3 * X 5 * X 7 ^ 2)

/-- The `a₆`-free part of `gen₂`. -/
noncomputable def vpoly : Poly :=
  X 9 ^ 2 * X 10 + X 0 * X 8 * X 9 * X 10 + X 2 * X 9 * X 10 ^ 2
    - (X 8 ^ 3 + X 1 * X 8 ^ 2 * X 10 + X 3 * X 8 * X 10 ^ 2)

theorem gen₁_eq : gen₁ = upoly - X 4 * X 7 ^ 3 := by
  rw [gen₁, curve, pt₁, upoly, eval_polynomial]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem gen₂_eq : gen₂ = vpoly - X 4 * X 10 ^ 3 := by
  rw [gen₂, curve, pt₂, vpoly, eval_polynomial]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem peel4_upoly : peel 4 upoly = Polynomial.C upoly := by
  rw [upoly]; simp

theorem peel4_vpoly : peel 4 vpoly = Polynomial.C vpoly := by
  rw [vpoly]; simp

/-! ## The relation left after `Pz` is inverted and `a₆` eliminated -/

/-- `Px * Qz - Qx * Pz`, the third prime factor of `hpoly`'s `a₄`-coefficient. -/
noncomputable def dpoly : Poly := X 5 * X 10 - X 8 * X 7

/-- The `a₄`-coefficient of `hpoly`. -/
noncomputable def apoly : Poly := X 7 ^ 2 * X 10 ^ 2 * dpoly

/-- `gen₁` with both the `a₄` and the `a₆` term dropped. -/
noncomputable def u₀ : Poly :=
  X 6 ^ 2 * X 7 + X 0 * X 5 * X 6 * X 7 + X 2 * X 6 * X 7 ^ 2 - (X 5 ^ 3 + X 1 * X 5 ^ 2 * X 7)

/-- `gen₂` with both the `a₄` and the `a₆` term dropped. -/
noncomputable def v₀ : Poly :=
  X 9 ^ 2 * X 10 + X 0 * X 8 * X 9 * X 10 + X 2 * X 9 * X 10 ^ 2 - (X 8 ^ 3 + X 1 * X 8 ^ 2 * X 10)

/-- The `a₄`-free part of `hpoly`. -/
noncomputable def cpoly : Poly := X 7 ^ 3 * v₀ - X 10 ^ 3 * u₀

/-- `Pz ^ 3 * gen₂ - Qz ^ 3 * gen₁`: the `a₆` terms cancel. -/
noncomputable def hpoly : Poly := X 7 ^ 3 * vpoly - X 10 ^ 3 * upoly

theorem hpoly_eq_gen : hpoly = X 7 ^ 3 * gen₂ - X 10 ^ 3 * gen₁ := by
  rw [gen₁_eq, gen₂_eq, hpoly]; ring

theorem hpoly_eq_a4 : hpoly = apoly * X 3 + cpoly := by
  rw [hpoly, apoly, dpoly, cpoly, upoly, vpoly, u₀, v₀]; ring

/-! ## Non-divisibilities, each witnessed by one integer point -/

theorem not_dvd_of_eval {p q : Poly} (pt : Fin 11 → ℤ)
    (hp : eval pt p = 0) (hq : eval pt q ≠ 0) : ¬ p ∣ q := by
  rintro ⟨g, rfl⟩
  exact hq (by rw [map_mul, hp, zero_mul])

theorem ne_zero_of_eval {p : Poly} (pt : Fin 11 → ℤ) (h : eval pt p ≠ 0) : p ≠ 0 := by
  rintro rfl; simp at h

theorem apoly_ne_zero : apoly ≠ 0 :=
  ne_zero_of_eval (vals 0 0 0 0 0 1 0 1 0 0 1) (by norm_num [apoly, dpoly, vals])

theorem not_X10_dvd_X8_mul_X7 : ¬ (X 10 : Poly) ∣ X 8 * X 7 :=
  not_dvd_of_eval (vals 0 0 0 0 0 0 0 1 1 0 0) (by norm_num [vals]) (by norm_num [vals])

theorem not_X7_dvd_cpoly : ¬ (X 7 : Poly) ∣ cpoly :=
  not_dvd_of_eval (vals 0 0 0 0 0 1 0 0 0 0 1) (by norm_num [vals])
    (by norm_num [cpoly, u₀, v₀, vals])

theorem not_X10_dvd_cpoly : ¬ (X 10 : Poly) ∣ cpoly :=
  not_dvd_of_eval (vals 0 0 0 0 0 0 0 1 1 0 0) (by norm_num [vals])
    (by norm_num [cpoly, u₀, v₀, vals])

theorem not_dpoly_dvd_cpoly : ¬ dpoly ∣ cpoly :=
  not_dvd_of_eval (vals 0 0 0 0 0 0 0 1 0 1 1) (by norm_num [dpoly, vals])
    (by norm_num [cpoly, u₀, v₀, vals])

theorem not_hpoly_dvd_X7 : ¬ hpoly ∣ (X 7 : Poly) :=
  not_dvd_of_eval (vals 0 0 0 0 0 0 0 1 0 0 0)
    (by norm_num [hpoly, upoly, vpoly, vals]) (by norm_num [vals])

/-! ## `hpoly` is prime -/

theorem isRelPrime_of_prime {R : Type*} [CommRing R] [IsDomain R] {p x : R}
    (hp : Prime p) (h : ¬ p ∣ x) :
    IsRelPrime p x := by
  intro d hdp hdx
  obtain ⟨e, he⟩ := hdp
  rcases hp.irreducible.isUnit_or_isUnit he with hd | he'
  · exact hd
  · obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp he'
    exact absurd (Dvd.dvd.trans ⟨w, by rw [he, mul_assoc, hw, mul_one]⟩ hdx) h

theorem prime_of_peel_prime {k : Fin 11} {p : Poly} (h : Prime (peel k p)) : Prime p := by
  refine ⟨fun h0 => h.ne_zero (by rw [h0, map_zero]), fun hu => h.not_unit (hu.map (peel k)), ?_⟩
  intro a b hab
  have hd : peel k p ∣ peel k a * peel k b := by
    rw [← map_mul]; exact map_dvd _ hab
  rcases h.2.2 _ _ hd with h1 | h1
  · exact Or.inl (peel_dvd_cancel h1)
  · exact Or.inr (peel_dvd_cancel h1)

theorem peel5_dpoly :
    peel 5 dpoly = Polynomial.C (X 10) * Polynomial.X + Polynomial.C (-(X 8 * X 7)) := by
  rw [dpoly]; simp; ring

theorem prime_dpoly : Prime dpoly := by
  refine prime_of_peel_prime (k := 5) ?_
  rw [peel5_dpoly]
  refine UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (Polynomial.irreducible_C_mul_X_add_C (X_ne_zero _) ?_)
  exact isRelPrime_of_prime MvPolynomial.X_prime
    (by rw [dvd_neg]; exact not_X10_dvd_X8_mul_X7)

theorem peel3_apoly : peel 3 apoly = Polynomial.C apoly := by
  rw [apoly, dpoly]; simp

theorem peel3_cpoly : peel 3 cpoly = Polynomial.C cpoly := by
  rw [cpoly, u₀, v₀]; simp

theorem peel3_hpoly :
    peel 3 hpoly = Polynomial.C apoly * Polynomial.X + Polynomial.C cpoly := by
  rw [hpoly_eq_a4, map_add, map_mul, peel_X_self, peel3_apoly, peel3_cpoly]

theorem isRelPrime_apoly_cpoly : IsRelPrime apoly cpoly := by
  intro d hda hdc
  by_contra hdu
  have hd0 : d ≠ 0 := fun h => apoly_ne_zero (zero_dvd_iff.mp (h ▸ hda))
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hqp : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hqc : q ∣ cpoly := hqd.trans hdc
  have key : ∀ r : Poly, Prime r → q ∣ r → ¬ r ∣ cpoly → False := fun r hr hqr hrc =>
    hrc ((hqp.associated_of_dvd hr hqr).symm.dvd.trans hqc)
  have hqa : q ∣ apoly := hqd.trans hda
  rw [apoly] at hqa
  rcases hqp.2.2 _ _ hqa with h1 | h1
  · rcases hqp.2.2 _ _ h1 with h2 | h2
    · exact key _ MvPolynomial.X_prime (hqp.dvd_of_dvd_pow h2) not_X7_dvd_cpoly
    · exact key _ MvPolynomial.X_prime (hqp.dvd_of_dvd_pow h2) not_X10_dvd_cpoly
  · exact key _ prime_dpoly h1 not_dpoly_dvd_cpoly

theorem prime_hpoly : Prime hpoly := by
  refine prime_of_peel_prime (k := 3) ?_
  rw [peel3_hpoly]
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (Polynomial.irreducible_C_mul_X_add_C apoly_ne_zero isRelPrime_apoly_cpoly)

/-! ## Reduction modulo `gen₁`: clearing `a₆` at the cost of powers of `Pz` -/

theorem C_mem_Xfree (k : Fin 11) (c : ℤ) : (C c : Poly) ∈ Xfree k := by
  rw [mem_Xfree_iff]; simp [peel]

theorem upoly_mem : upoly ∈ Xfree 4 := mem_Xfree_iff.mpr peel4_upoly

theorem vpoly_mem : vpoly ∈ Xfree 4 := mem_Xfree_iff.mpr peel4_vpoly

theorem X7_mem : (X 7 : Poly) ∈ Xfree 4 := X_mem_Xfree (by decide)

theorem hpoly_mem_Xfree : hpoly ∈ Xfree 4 := by
  rw [hpoly]
  exact sub_mem (mul_mem (pow_mem X7_mem 3) vpoly_mem)
    (mul_mem (pow_mem (X_mem_Xfree (by decide : (10 : Fin 11) ≠ 4)) 3) upoly_mem)

theorem gen₁_mem_span : gen₁ ∈ Ideal.span ({gen₁} : Set Poly) :=
  Ideal.mem_span_singleton_self _

/-- **Reduction.** Multiplying by a power of `Pz` makes any `a` congruent, modulo `gen₁`,
to a polynomial free of `a₆ = X 4`.  This is division by `gen₁` in `a₆`, whose leading
coefficient is `-Pz ^ 3`. -/
theorem exists_reduction (a : Poly) :
    ∃ (n : ℕ) (r : Poly), r ∈ Xfree 4 ∧ X 7 ^ n * a - r ∈ Ideal.span ({gen₁} : Set Poly) := by
  induction a using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C c, C_mem_Xfree 4 c, ?_⟩
    simp
  | add p q hp hq =>
    obtain ⟨n₁, r₁, hr₁, h₁⟩ := hp
    obtain ⟨n₂, r₂, hr₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, X 7 ^ n₂ * r₁ + X 7 ^ n₁ * r₂,
      add_mem (mul_mem (pow_mem X7_mem _) hr₁) (mul_mem (pow_mem X7_mem _) hr₂), ?_⟩
    have key : X 7 ^ (n₁ + n₂) * (p + q) - (X 7 ^ n₂ * r₁ + X 7 ^ n₁ * r₂)
        = X 7 ^ n₂ * (X 7 ^ n₁ * p - r₁) + X 7 ^ n₁ * (X 7 ^ n₂ * q - r₂) := by ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p i hp =>
    obtain ⟨n, r, hr, h⟩ := hp
    by_cases hi : i = 4
    · subst hi
      refine ⟨n + 3, r * upoly, mul_mem hr upoly_mem, ?_⟩
      have key : X 7 ^ (n + 3) * (p * X 4) - r * upoly
          = X 7 ^ 3 * X 4 * (X 7 ^ n * p - r) - r * gen₁ := by
        rw [gen₁_eq]; ring
      rw [key]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ gen₁_mem_span)
    · refine ⟨n, r * X i, mul_mem hr (X_mem_Xfree hi), ?_⟩
      have key : X 7 ^ n * (p * X i) - r * X i = (X 7 ^ n * p - r) * X i := by ring
      rw [key]
      exact Ideal.mul_mem_right _ _ h

/-- **The degree kill.** `gen₁` has degree exactly `1` in `a₆`, so a multiple of it that
is free of `a₆` is `0`. -/
theorem eq_zero_of_mem_Xfree_of_mem_span {y : Poly} (hy : y ∈ Xfree 4)
    (h : y ∈ Ideal.span ({gen₁} : Set Poly)) : y = 0 := by
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp h
  rcases eq_or_ne e 0 with rfl | he0
  · rw [← he, zero_mul]
  exfalso
  have hg : peel 4 gen₁ = Polynomial.C (-(X 7 ^ 3)) * Polynomial.X + Polynomial.C upoly := by
    rw [gen₁_eq, map_sub, map_mul, map_pow, peel_X_self,
      peel_X_of_ne (show (7 : Fin 11) ≠ 4 by decide), peel4_upoly, map_neg, map_pow]
    ring
  have hdeg : (peel 4 gen₁).natDegree = 1 := by
    rw [hg]
    exact Polynomial.natDegree_linear (neg_ne_zero.mpr (pow_ne_zero 3 (X_ne_zero _)))
  have he' : peel 4 e ≠ 0 := fun hc => he0 (peel_injective 4 (by rw [hc, map_zero]))
  have hgz : peel 4 gen₁ ≠ 0 := fun hc => by simp [hc] at hdeg
  have hy' : peel 4 y = Polynomial.C y := hy
  have : (Polynomial.C y).natDegree = (peel 4 e).natDegree + 1 := by
    rw [← hy', ← he, map_mul, Polynomial.natDegree_mul he' hgz, hdeg]
  rw [Polynomial.natDegree_C] at this
  omega

/-! ## Primality after `Pz` is inverted -/

theorem gen₁_mem_idl : gen₁ ∈ idl := Ideal.subset_span (by simp)

theorem gen₂_mem_idl : gen₂ ∈ idl := Ideal.subset_span (by simp)

theorem hpoly_mem_idl : hpoly ∈ idl := by
  rw [hpoly_eq_gen]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ gen₂_mem_idl)
    (Ideal.mul_mem_left _ _ gen₁_mem_idl)

theorem span_gen₁_le_idl : Ideal.span ({gen₁} : Set Poly) ≤ idl :=
  (Ideal.span_singleton_le_iff_mem _).mpr gen₁_mem_idl

/-- An `a₆`-free element of `idl` is, up to a power of `Pz`, a multiple of `hpoly`. -/
theorem exists_pow_mul_mem_span_hpoly {x : Poly} (hx : x ∈ Xfree 4) (hmem : x ∈ idl) :
    ∃ m : ℕ, X 7 ^ m * x ∈ Ideal.span ({hpoly} : Set Poly) := by
  rw [idl, Ideal.mem_span_pair] at hmem
  obtain ⟨c₁, c₂, hc⟩ := hmem
  obtain ⟨n, r, hr, hrn⟩ := exists_reduction c₂
  refine ⟨n + 3, ?_⟩
  have key : X 7 ^ (n + 3) * x - r * hpoly
      = X 7 ^ n * (X 7 ^ 3 * c₁ + X 10 ^ 3 * c₂) * gen₁ + (X 7 ^ n * c₂ - r) * hpoly := by
    rw [← hc, hpoly_eq_gen]; ring
  have hz : X 7 ^ (n + 3) * x - r * hpoly = 0 := by
    refine eq_zero_of_mem_Xfree_of_mem_span
      (sub_mem (mul_mem (pow_mem X7_mem _) hx) (mul_mem hr hpoly_mem_Xfree)) ?_
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ gen₁_mem_span)
      (Ideal.mul_mem_right _ _ hrn)
  have : X 7 ^ (n + 3) * x = r * hpoly := by linear_combination hz
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end SatPrime

open SatPrime in
/-- **The universal ideal is prime once `Pz = X 7` is inverted** (PROVEN) —
stated as a `Pz`-saturated primality, which is exactly the contraction to `Poly`
of `IsPrime (idl ⬝ Poly[1/Pz])`.  Inverting `Pz` solves `gen₁` for `a₆` and leaves
the single relation `SatPrime.hpoly = Pz ^ 3 * gen₂ - Qz ^ 3 * gen₁`, which is a
PRIMITIVE polynomial of degree `1` in `a₄` over a polynomial ring over `ℤ`, hence
irreducible, hence prime.  See `SatPrime` above for the whole route. -/
theorem exists_pow_X7_mul_mem_idl {a b : Poly} (hab : a * b ∈ idl) :
    (∃ n : ℕ, X 7 ^ n * a ∈ idl) ∨ (∃ n : ℕ, X 7 ^ n * b ∈ idl) := by

  obtain ⟨na, ra, hra, hrna⟩ := exists_reduction a
  obtain ⟨nb, rb, hrb, hrnb⟩ := exists_reduction b
  have hprod : ra * rb ∈ idl := by
    have key : ra * rb = X 7 ^ (na + nb) * (a * b)
        - (ra * (X 7 ^ nb * b - rb) + (X 7 ^ na * a - ra) * (X 7 ^ nb * b)) := by ring
    rw [key]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hab)
      (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (span_gen₁_le_idl hrnb))
        (Ideal.mul_mem_right _ _ (span_gen₁_le_idl hrna)))
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_span_hpoly (mul_mem hra hrb) hprod
  have hdvd : hpoly ∣ X 7 ^ m * (ra * rb) := Ideal.mem_span_singleton.mp hm
  have final : ∀ (n : ℕ) (c rc : Poly), hpoly ∣ rc →
      X 7 ^ n * c - rc ∈ Ideal.span ({gen₁} : Set Poly) → X 7 ^ n * c ∈ idl := by
    intro n c rc hrc hspan
    obtain ⟨t, ht⟩ := hrc
    have hrcidl : rc ∈ idl := by rw [ht]; exact Ideal.mul_mem_right t idl hpoly_mem_idl
    have : X 7 ^ n * c = (X 7 ^ n * c - rc) + rc := by ring
    rw [this]
    exact Ideal.add_mem _ (span_gen₁_le_idl hspan) hrcidl
  rcases prime_hpoly.2.2 _ _ hdvd with h1 | h1
  · exact absurd (prime_hpoly.dvd_of_dvd_pow h1) not_hpoly_dvd_X7
  rcases prime_hpoly.2.2 _ _ h1 with h2 | h2
  · exact Or.inl ⟨na, final na a ra h2 hrna⟩
  · exact Or.inr ⟨nb, final nb b rb h2 hrnb⟩

/-- **The universal ideal is prime** (PROVEN from the two leaves above): a
`Pz`-saturated primality plus the fact that `Pz` is a non-zerodivisor modulo
`idl` is primality. -/
theorem idl_isPrime : idl.IsPrime := by
  refine ⟨idl_ne_top, ?_⟩
  have key : ∀ (n : ℕ) (c : Poly), X 7 ^ n * c ∈ idl → c ∈ idl := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ k ih =>
      intro c hc
      refine mem_idl_of_X7_mul_mem (ih (X 7 * c) ?_)
      have hrw : X 7 ^ k * (X 7 * c) = X 7 ^ (k + 1) * c := by ring
      rw [hrw]
      exact hc
  intro a b hab
  rcases exists_pow_X7_mul_mem_idl hab with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact Or.inl (key n a hn)
  · exact Or.inr (key n b hn)

noncomputable instance : IsDomain Univ := (Ideal.Quotient.isDomain_iff_prime idl).mpr idl_isPrime

/-- **The universal `addZ` is nonzero** (PROVEN) — witnessed by the specialisation
to `y² = x³ + 1` over `ℤ` at the points `[0 : 1 : 1]` and `[2 : 3 : 1]`, where the
first law's `Z`-coordinate is `-8`. -/
theorem addZ_upt_ne_zero : addZ ucurve upt₁ upt₂ ≠ 0 := by
  set g : Univ →+* ℤ := Ideal.Quotient.lift idl (spec ⟨0, 0, 0, 0, 1⟩ ![0, 1, 1] ![2, 3, 1])
    (fun _ ha => spec_of_mem_idl equation_test₁ equation_test₂ ha) with hg
  have hcomp : g.comp (Ideal.Quotient.mk idl) = spec ⟨0, 0, 0, 0, 1⟩ ![0, 1, 1] ![2, 3, 1] :=
    RingHom.ext fun _ => rfl
  intro hz
  have h := congrArg g hz
  rw [map_zero, ← map_addZ, map_ucurve, comp_upt₁, comp_upt₂, hcomp, spec_curve, spec_pt₁,
    spec_pt₂] at h
  rw [addZ] at h
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h

/-- **The universal instance of the theorem** (PROVEN from the leaf) — the
cancellation of `addZ ^ 3`, done once, where it is legitimate. -/
theorem equation_uadd2XYZ : Equation ucurve (add2XYZ ucurve upt₁ upt₂) := by
  have hkey := addZ_pow_mul_equationPoly_add2XYZ equation_upt₁ equation_upt₂
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) addZ_upt_ne_zero
  · rw [equation_iff, add2XYZ_X, add2XYZ_Y, add2XYZ_Z]
    exact h

end Universal

/-- **The second triple again satisfies the Weierstrass equation** — exactly what
`equation_addXYZ` proves for the standard law, for the law of the line `Y = 0`,
over an arbitrary commutative ring.

Proved by specialising the universal instance `Universal.equation_uadd2XYZ`; see
the module docstring for why no large `ring1` is involved. -/
theorem equation_add2XYZ (hP : Equation W' P) (hQ : Equation W' Q) :
    Equation W' (add2XYZ W' P Q) := by
  set f : Universal.Univ →+* R := Ideal.Quotient.lift Universal.idl (Universal.spec W' P Q)
    (fun _ ha => Universal.spec_of_mem_idl hP hQ ha) with hf
  have hcomp : f.comp (Ideal.Quotient.mk Universal.idl) = Universal.spec W' P Q :=
    RingHom.ext fun _ => rfl
  have h := (Universal.equation_uadd2XYZ).map f
  rw [← map_add2XYZ, Universal.map_ucurve, Universal.comp_upt₁, Universal.comp_upt₂, hcomp,
    Universal.spec_curve, Universal.spec_pt₁, Universal.spec_pt₂] at h
  exact h

end WeierstrassCurve.Projective
