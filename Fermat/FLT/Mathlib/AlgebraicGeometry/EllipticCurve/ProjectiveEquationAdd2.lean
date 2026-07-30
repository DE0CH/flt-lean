/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveAddition
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.ProjectiveEquationAdd

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
`Universal.idl_isPrime`.
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

/-- **The universal ideal is prime** (sorry node) — equivalently, the generic
Weierstrass curve with two generic marked points is an INTEGRAL scheme.  This is
the sole remaining content of `equation_add2XYZ`.

## Why it is true

Write `Y = {(a, P) : W_a(P) = 0} ⊂ 𝔸⁵ × 𝔸³` (dimension `7`).  The zero set of
`idl` is `Y ×_{𝔸⁵} Y`, of dimension `9` in `𝔸¹¹`.  `Y → 𝔸⁵` has irreducible
generic fibre (the cone over the generic Weierstrass cubic, which is an
irreducible surface), so exactly one component of the fibre product dominates
`Y`.  Any other component lies over the discriminant locus `Δ ⊂ 𝔸⁵`, hence has
dimension at most `4 + 2 + 2 = 8`; but every component of an intersection with a
hypersurface has dimension at least `dim Y + 2 - 1 = 9`.  So there is no other
component.  Generic reducedness plus the complete intersection (hence
Cohen–Macaulay, hence unmixed) property gives reducedness, and `ℤ`-torsion-freeness
— `Poly ⧸ idl` is `ℤ[…]`-free on `Px^i Qx^j`, `i, j ≤ 2`, since both generators are
monic up to sign in `Px` resp. `Qx` — carries it over `Spec ℤ`.

## A concrete two-step route for the formalisation

`gen₁` and `gen₂` are, up to sign, MONIC cubics in `Px = X 5` resp. `Qx = X 8`,
over `B = ℤ[a₁, a₂, a₃, a₄, a₆, Py, Pz, Qy, Qz]`, and their coefficients involve
disjoint sets of the remaining variables.  So
`Poly ⧸ idl ≅ (B[Px] ⧸ (f₁))[Qx] ⧸ (f₂)` and it suffices to show

1. `f₁` is irreducible over the UFD `B`.  **This half is easy**: `f₁` is of degree
   `1` in `a₆ = X 4`, with coefficient `Pz³` and `a₆`-free part `g`; `Pz ∤ g`
   because `g mod Pz = Px³`, so `f₁` is primitive, and a primitive degree-one
   polynomial over a UFD is irreducible.
2. `f₂` is irreducible over the domain `C = B[Px] ⧸ (f₁)`.  This half is the real
   work: `C` need not be a UFD, so the primitivity argument is unavailable, and
   one is asking that the generic Weierstrass cubic stay irreducible after
   adjoining one generic point of itself.

Note that only a WEAKER statement is actually consumed below, and a proof of it
would close the leaf just as well: that `addZ ucurve upt₁ upt₂` is a
non-zerodivisor in `Univ`.

## A SECOND ROUTE, WITH THE HARD HALF RELOCATED (recorded 2026-07-30, not proven)

The two-step route above puts all the difficulty into "`f₂` is irreducible over a
ring that need not be a UFD".  Localising instead of towering moves the whole
difficulty somewhere else, and the half that survives is *elementary*.

Both generators are AFFINE-LINEAR in `(a₁, a₂, a₃, a₄, a₆)` — that is the one
structural fact neither the dimension count nor the tower above uses.  Write
`u`, `v` for the `a₆`-free parts of `gen₁`, `gen₂`, so `gen₁ = u - a₆ Pz³` and
`gen₂ = v - a₆ Qz³`.  Over `Poly[1/Pz]` the first generator SOLVES for `a₆`
(`a₆ = u / Pz³`), and substituting into the second leaves a single generator
`w := Qz³ u - Pz³ v`, so

> `Poly[1/Pz] ⧸ idl ≅ ℤ[a₁, a₂, a₃, a₄, Px, Py, Pz^{±1}, Qx, Qy, Qz] ⧸ (w)`.

**`w` is PRIME, and the proof is one Gauss argument.**  `w` is irreducible over
`ℚ` — checked with `Singular`'s `factorize`, which returns the single factor `w`
with multiplicity `1` (untrusted searcher, so this certifies the statement, not a
proof) — and every coefficient of `w` is `±1`, so its `ℤ`-content is `1`; an
irreducible-over-`ℚ` primitive polynomial is irreducible in `ℤ[…]`, hence prime.
The route to that in Lean is the same trick step 1 above uses: `w` has degree `1`
in `a₁` with coefficient `Pz Qz (Px Py Qz² - Qx Qy Pz²)`, whose irreducible factors
are `Pz`, `Qz` and `Px Py Qz² - Qx Qy Pz²` (itself degree `1` and primitive in
`Py`); none divides the `a₁`-free part of `w`, which is `-Qz³ Px³` mod `Pz`,
`Pz³ Qx³` mod `Qz`, and `10 + a₃ + 3 a₂ + a₄` at
`(Px, Py, Pz, Qx, Qy, Qz) = (1, 2, 1, 2, 1, 1)` — a point of the third factor's
zero locus.  So `w` is primitive in `a₁` over a UFD, hence irreducible.  (Do NOT
test that last non-divisibility on the diagonal `P = Q`: there the `a₁`-free part
of `w` vanishes identically and the check reads as a false positive.)

**So the entire remaining gap is SATURATION**: that `Pz` is a non-zerodivisor on
`Poly ⧸ idl`, equivalently `idl : Pz^∞ = idl`.  Given that, `Poly ⧸ idl` embeds in
the domain `Poly[1/Pz] ⧸ idl` and the leaf follows.  This is a genuinely different
reduction from step 2 above — it is a question about associated primes of a
complete intersection rather than about irreducibility over a non-UFD — and it is
the same question the consumer's weaker form asks, since `addZ` and `Pz` cut out
comparable loci.

Two supporting observations.  `{gen₁, gen₂}` is already a Gröbner basis for the
degree-reverse-lex order: the leading terms are `Px³` and `Qx³`, which are coprime,
so the single S-pair reduces to zero by Buchberger's first criterion — that is the
mechanical justification for the `ℤ[…]`-freeness on `Px^i Qx^j` claimed above, and
it says `(gen₁, gen₂)` is a regular sequence, hence a complete intersection, hence
Cohen–Macaulay and unmixed.  With unmixedness the saturation reduces to a statement
about MINIMAL primes only.  And the saturation is not merely unproven but
unconfirmed: `Singular`'s `quotient(idl, Pz)` and `minAssGTZ(idl)` were both killed
at 900 s in these eleven variables, so a successor should not expect the CAS to
settle it either. -/
theorem idl_isPrime : idl.IsPrime := sorry

noncomputable instance : IsDomain Univ := (Ideal.Quotient.isDomain_iff_prime idl).mpr idl_isPrime

/-- **The universal `addZ` is nonzero** (PROVEN) — witnessed by the specialisation
to `y² = x³ + 1` over `ℤ` at the points `[0 : 1 : 1]` and `[2 : 3 : 1]`, where the
first law's `Z`-coordinate is `-8`. -/
theorem addZ_upt_ne_zero : addZ ucurve upt₁ upt₂ ≠ 0 := by
  have hP : Equation (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ) ![0, 1, 1] := by
    rw [equation_iff]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hQ : Equation (⟨0, 0, 0, 0, 1⟩ : WeierstrassCurve ℤ) ![2, 3, 1] := by
    rw [equation_iff]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  set g : Univ →+* ℤ := Ideal.Quotient.lift idl (spec ⟨0, 0, 0, 0, 1⟩ ![0, 1, 1] ![2, 3, 1])
    (fun _ ha => spec_of_mem_idl hP hQ ha) with hg
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
