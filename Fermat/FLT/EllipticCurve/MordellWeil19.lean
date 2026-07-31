module

/-
MordellWeil19.lean — own work for the Fermat project.

# `X_0(19)` as the elliptic curve `19a1`, and the `3`-isogeny that makes it cheap

This module supplies the level-`19` row of `X0GenusOne.finite_x0Model` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`: the rational points of

    19a1 :  y² + y = x³ + x² − 9x − 15        (conductor `19`, `Δ = −19³`)

are exactly `(5, 9)`, `(5, −10)` and the point at infinity, so `19a1(ℚ) ≅ ℤ/3`
is FINITE.  It is the level-`19` analogue of `MordellWeil.lean`'s `MazurLevel11`
(for `11a3`) and `MazurLevel14` (for `14a4`), and it follows those files'
architecture exactly: an unconditional plane-Diophantine statement, from which
rank `0`, finiteness AND the point enumeration all follow.

## THE ROUTE, and why it is NOT the descent the consumer's docstring predicted

`MazurTorsion.lean`'s section note anticipated "a full `2`-descent" on `19a1`
itself, on the ground that `19a1` has no rational `2`-torsion (its `2`-division
cubic `4x³ + 4x² − 36x − 59` is irreducible), so the `2`-isogeny shortcut used at
level `14` is unavailable.  That is true, and it is not the cheapest route.

**`19a1` carries TWO rational `3`-isogenies**, and one of them lands on the curve
of SMALLEST discriminant in the isogeny class:

    19a3 :  y² + y = x³ + x² + x              (conductor `19`, `Δ = −19`)

`elldivpol(19a1, 3)` factors as `(x − 5)(3x + 4)(x² + 5x + 7)`.  The rational root
`x = 5` is the rational `3`-torsion point `(5, 9)`, whose quotient is
`[0,1,1,−769,−8470]`; the OTHER rational kernel is `x = −4/3`, whose quotient is
`19a3`.  Writing that second isogeny down and composing with the minimal model
(`u, r, s, t = 3, 8/3, 0, 13`) gives the completely explicit degree-`3` map

    X = (x³ − 18x − 35) / (3x + 4)²
    Y = ((y − 13)(x³ + 4x²) + (18y − 63)x + 46y − 9) / (3x + 4)³

from `19a1` to `19a3`, and the underlying polynomial identity — `cover_identity`
below — is a `linear_combination` over the `19a1` equation with cofactor
`(x³ + 4x² + 18x + 46)²`.  It is verified by the kernel, not asserted.

**What that buys.**  Only the *map of curves* is needed, never the isogeny as a
group homomorphism (which is what `MazurTorsion.lean`'s "isogeny axis" note
correctly recorded as missing, and which nothing in this tree provides).  The
argument is: every affine rational point of `19a3` has `x = 0`; the numerator
`x³ − 18x − 35 = (x − 5)(x² + 5x + 7)` therefore vanishes; `x² + 5x + 7` has
discriminant `−3 < 0`; hence `x = 5`, and then `y ∈ {9, −10}`.  The excluded
fibre `3x + 4 = 0` is killed outright over `ℝ`: at `x = −4/3` the equation reads
`(54y + 27)² = −9747`.

**And the descent moves to the RIGHT curve.**  The arithmetic input is now rank
`0` for `19a3`, whose monic model `W² = U³ + 4U² + 16U + 16` (`U = 4X`,
`W = 8Y + 4`) has

    N(p − 2e²θ) = p³ + 4p²e² + 16pe⁴ + 16e⁶,     θ³ + 2θ² + 4θ + 2 = 0,

i.e. the descent runs in the cubic ring `ℤ[θ]` of discriminant `−76`, which is
the FULL ring of integers (index `1`, since `−76/f² = −19` is not a cubic field
discriminant for `f = 2`) and has class number `1`.  Compare level `11`, where
`MazurLevel11.Cubic.ZS` is `ℤ[s]/(s³ − 2s² + 2)` of discriminant `−44` with
`N(p − 2e²s) = p³ − 4p²e² + 16e⁶`: **the two are the same shape with different
constants**, so `MazurLevel11`'s development transcribes.  Doing the `2`-descent
on `19a1` instead would run in the SAME field but with `ℤ[ρ]` of index `152`
(best possible after rescaling: `19`), because `19a1`'s cubic
`U³ + 4U² − 144U − 944` has discriminant `−2⁸·19³`.  That is the concrete reason
this file descends on `19a3` and transports by the isogeny rather than the other
way round.

## THE ONE LEAF (recut twice on 2026-07-31)

`MazurX0Nineteen.descent_unit_square` — the valuation bookkeeping in
`ℤ[θ]`, `θ³ + 2θ² + 4θ + 2 = 0`: the descent image `β = p − 2θe²` is one of
`16` explicit units times a square.  It is the ONLY place algebraic number
theory enters, and it is the level-`19` transcription of
`MazurLevel11.descent_unit_square` (PROVEN there over `𝓞_K = ℤ[s]` with
`h(K) = 1`, and units mod squares).

**`integral_leaf` is PROVEN over it** (2026-07-31), together with the whole
elementary half of the descent AND both prunings, which are now in this file:

    descent_unit_square     (the ℤ[θ] leaf)
      → descent_square_class      (norm pruning: 16 classes → {1, ε})
      → epsilon_class_impossible  (local condition: ε dies, pure parity mod 4)
      → exists_halving_witness    (β = δ², in coordinates)
      → halving_norm_relation / halving_x_relation / halving_relation
          (eliminate the halving coordinates m, c)
      → height_drop_or_small
          (over forms_common_dvd, forms_archimedean, MazurLevel11.reduced_fraction)
      → smallPoints           (bitmask quadratic-residue sieve, |p| + e² ≤ 574)
      → halving_descends / witness_c_ne_zero / trivial_ascends
      → integral_leaf_aux     (strong induction on |p| + e²)
      → integral_leaf → U_eq_zero → x0Nineteen_x_eq_zero
      → rational_point_x0Nineteen   (over cover_identity, cover_eq)

The two binary forms of the height bound are computed from the duplication
formula on `W² = U³ + 4U² + 16U + 16` (`a₂ = 4`, `a₄ = a₆ = 16`):

    F(X, Y) = X⁴ − 32X²Y² − 128XY³,   G(X, Y) = X³ + 4X²Y + 16XY² + 16Y³,

against level `11`'s `X⁴ − 128XY³ + 256Y⁴` and `X³ − 4X²Y + 16Y³`; `Res(F, G) =
2¹⁶·19²`, the Bezout cofactors clear `2¹⁰·19²  = 369664`, and the box is
`|p| + e² ≤ 574`.  Note `F` has no constant term — `U = 0` is the `3`-torsion
point and duplicates to itself — which is why the exceptional set here has ONE
element where level `11` has two.

A successor should follow `MordellWeil.lean` rather than looking for a general
Mordell–Weil theorem, which exists nowhere in this tree, in `Mathlib`, or in
`~/cs/FLT`.

CHECKED EXTERNALLY (PARI/GP 2.17.4, an untrusted searcher — not a proof; every
witness used below is verified in Lean).  `ellinit([0,1,1,-9,-15])` gives
`Δ = −6859 = −19³` and conductor `19`; `ellrank` returns `[0, 0]`, so rank `0` is
proven rather than bounded; `elltors` returns `ℤ/3`; `ellratpoints` returns
exactly `(5, 9)`, `(5, −10)`.  `ellinit([0,1,1,1,0])` gives `Δ = −19`, conductor
`19`, and its affine rational points are `(0, 0)`, `(0, −1)` — both with `x = 0`,
which is what `x0Nineteen_x_eq_zero` says.  `ellisogeny(19a1, 3*x + 4)` returns
the target `[0, 1, 1, 163/3, 298/27]`, of discriminant `−3¹²·19`, i.e. `19a3`
after `u = 3`.  `nfinit(x³ + 2x² + 4x + 2)` has discriminant `−76`, class group
trivial, fundamental unit `θ + 1`.  A direct search over `|p| ≤ 4000`,
`1 ≤ e ≤ 300`, `gcd(p, e) = 1` finds `(0, 1)` and nothing else, so
`integral_leaf` is true as written.
-/

public import Fermat.FLT.EllipticCurve.MordellWeil

@[expose] public section

namespace MazurX0Nineteen

/-! ### `ℤ[θ]` in coordinates: the descent map, its norm, and the square classes

`θ³ + 2θ² + 4θ + 2 = 0`, so `θ³ = −2θ² − 4θ − 2` and `θ⁴ = 6θ + 4`.  The
coordinate layer below is enough to STATE the descent and to run both prunings
that consume it; it is not enough to PROVE it, because the proof factors `β` in
`ℤ[θ]` and factoring needs the ring rather than its multiplication table.  So the
cut is placed exactly where level `11` places it: `descent_unit_square` is the
leaf, and everything above it is proven here.

The two prunings, both PROVEN below:

* the NORM pruning (`descent_square_class`): of the `16` square classes only the
  `2` of norm `1` survive, because `N(β) = N(u)·N(δ)²` is a square and the other
  fourteen have `N(u) ∈ {±1, ±2, ±19, ±38}`, none of which is;
* the LOCAL condition (`epsilon_class_impossible`): the surviving nontrivial
  class `ε = θ + 1` is impossible for a coprime point, and — exactly as at level
  `11`, and again with no `19`-adic input — it is pure parity mod `4`.
-/

/-- Multiplication of `ℤ[θ] = ℤ[X]/(X³ + 2X² + 4X + 2)` in the `ℤ`-basis
`1, θ, θ²`, with `(x₀, x₁, x₂)` denoting `x₀ + x₁θ + x₂θ²`.

Derivation: `∑ xᵢyⱼ θⁱ⁺ʲ` with `θ³ = −2θ² − 4θ − 2` and `θ⁴ = 6θ + 4`, so the
`θ³` term contributes `(−2, −4, −2)` and the `θ⁴` term `(4, 6, 0)`.  Certified by
`zsNorm_zsMul`: no other table would make `zsNorm` multiplicative. -/
def zsMul (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 * y.1 - 2 * (x.2.1 * y.2.2 + x.2.2 * y.2.1) + 4 * (x.2.2 * y.2.2),
   x.1 * y.2.1 + x.2.1 * y.1 - 4 * (x.2.1 * y.2.2 + x.2.2 * y.2.1) + 6 * (x.2.2 * y.2.2),
   x.1 * y.2.2 + x.2.1 * y.2.1 + x.2.2 * y.1 - 2 * (x.2.1 * y.2.2 + x.2.2 * y.2.1))

/-- The field norm `N : ℤ[θ] → ℤ`, as the determinant of multiplication-by-`x`
in the basis `1, θ, θ²`.

Spot values, all re-derived in PARI/GP: `N(θ) = −2`, `N(θ + 1) = 1` for the
fundamental unit `ε`, `N(θ + 3) = 19`, `N(16 + 16θ + 12θ²) = 2⁸·19`. -/
def zsNorm (x : ℤ × ℤ × ℤ) : ℤ :=
  x.1 ^ 3 - 2 * x.1 ^ 2 * x.2.1 - 4 * x.1 ^ 2 * x.2.2 + 4 * x.1 * x.2.1 ^ 2
    - 2 * x.1 * x.2.1 * x.2.2 + 8 * x.1 * x.2.2 ^ 2 - 2 * x.2.1 ^ 3
    + 4 * x.2.1 ^ 2 * x.2.2 - 8 * x.2.1 * x.2.2 ^ 2 + 4 * x.2.2 ^ 3

/-- **THE DESCENT MAP, in coordinates.**  The classical `2`-descent on
`W² = U³ + 4U² + 16U + 16` sends a point to `x(P) − 2θ` modulo squares, `2θ`
being the root of the cubic (`U = 2θ` turns `U³ + 4U² + 16U + 16` into
`8(θ³ + 2θ² + 4θ + 2)`).  On the coprime integral point `(p, e, n)` with
`U = p/e²` this is `β = p − 2θ·e² ∈ ℤ[θ]`, i.e. the triple `(p, −2e², 0)`.

As at level `11`, what the descent needs is that the IMAGE is trivial, not that
the map is a homomorphism with kernel `2E(ℚ)`; image-triviality is what
`descent_unit_square` asserts and it is proved by factorisation in `ℤ[θ]`. -/
def descentImage (p e : ℤ) : ℤ × ℤ × ℤ := (p, -2 * e ^ 2, 0)

/-- **The multiplication table is right** (PROVEN 2026-07-31): `zsNorm` is
multiplicative for `zsMul`. -/
theorem zsNorm_zsMul (x y : ℤ × ℤ × ℤ) :
    zsNorm (zsMul x y) = zsNorm x * zsNorm y := by
  simp only [zsNorm, zsMul]
  ring

/-- **`N(β) = n²` on the curve** (PROVEN 2026-07-31): the norm of the descent
image is exactly the curve's right-hand side, `N(p − 2θe²) = t³·P(p/t)` at
`t = 2e²` for the minimal polynomial `P`.  This is why the descent map lands in
the norm-square classes at all. -/
theorem zsNorm_descentImage (p e : ℤ) :
    zsNorm (descentImage p e) = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6 := by
  simp only [zsNorm, descentImage]
  ring

/-- `1` is a left unit for `zsMul` (PROVEN 2026-07-31). -/
theorem zsMul_one_left (x : ℤ × ℤ × ℤ) : zsMul (1, 0, 0) x = x := by
  simp only [zsMul]
  ring_nf

/-- Sanity: `θ·θ·θ = −2 − 4θ − 2θ²`, the defining relation. -/
example : zsMul (0, 1, 0) (zsMul (0, 1, 0) (0, 1, 0)) = (-2, -4, -2) := by decide

/-- Sanity: `ε·(θ² + θ + 3) = 1` for the fundamental unit `ε = θ + 1`, so `ε`
really is a unit. -/
example : zsMul (1, 1, 0) (3, 1, 1) = (1, 0, 0) := by decide

/-- Sanity, and a NON-VACUITY witness: `(2 + 2θ + θ²)² = −2θ`, so the one known
rational point `(p, e) = (0, 1)` really does lie in the trivial square class.
The leaf below is therefore not vacuously about an empty set of points. -/
example : zsMul (2, 2, 1) (2, 2, 1) = descentImage 0 1 := by decide

/-- **`β ≠ 0`, in the form `n ≠ 0`** (PROVEN 2026-07-31): no coprime integral
point of `W² = U³ + 4U² + 16U + 16` has `W = 0`.

`n = 0` forces `e² ∣ p³`, and `IsCoprime p e` then makes `e²` a unit, so `e = 1`;
the remaining `p³ + 4p² + 16p + 16 = 0` has `p ∣ 16`, and none of the `33`
candidates works.  Needed below because a zero norm would make the square-class
pruning vacuous. -/
theorem descentImage_norm_ne_zero {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (hn : zsNorm (descentImage p e) = n ^ 2) : n ≠ 0 := by
  rintro rfl
  rw [zsNorm_descentImage] at hn
  have hdvd : e ^ 2 ∣ p ^ 3 :=
    ⟨-(4 * p ^ 2) - 16 * p * e ^ 2 - 16 * e ^ 4, by linear_combination hn⟩
  have hu : IsUnit (e ^ 2) :=
    (hcop.pow (m := 3) (n := 2)).isUnit_of_dvd' hdvd dvd_rfl
  have he1 : e = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · nlinarith
    · nlinarith
  subst he1
  have hdvd16 : p ∣ 16 := ⟨-(p ^ 2) - 4 * p - 16, by linear_combination hn⟩
  have hup : p ≤ 16 := Int.le_of_dvd (by norm_num) hdvd16
  have hlo : -p ≤ 16 := Int.le_of_dvd (by norm_num) (neg_dvd.mpr hdvd16)
  have hlo' : -16 ≤ p := by linarith
  interval_cases p <;> norm_num at hn

/-- `19` is not a square (PROVEN 2026-07-31). -/
theorem not_isSquare_nineteen : ¬ IsSquare (19 : ℤ) :=
  WeierstrassCurve.MazurLevel11.not_isSquare_of_bounded (by norm_num)
    (by intro r h1 h2; interval_cases r <;> decide)

/-- `38` is not a square (PROVEN 2026-07-31). -/
theorem not_isSquare_thirtyEight : ¬ IsSquare (38 : ℤ) :=
  WeierstrassCurve.MazurLevel11.not_isSquare_of_bounded (by norm_num)
    (by intro r h1 h2; interval_cases r <;> decide)

/-- **THE VALUATION BOOKKEEPING** (sorry leaf, cut 2026-07-31 out of
`exists_halving_witness`): `β = p − 2θe²` is one of `16` explicit units times a
square in `ℤ[θ]`.

THIS IS THE ONLY REMAINING LEAF OF LEVEL `19`, and it is the exact analogue of
`MazurLevel11.descent_unit_square`, which is PROVEN there over two statements
about the cubic field — `Cubic.ZS.isPrincipalIdealRing_zs` (`𝓞_K = ℤ[s]`,
`h(K) = 1`) and `Cubic.ZS.unit_sq_class` (units mod squares).

THE SIXTEEN CLASSES, and why exactly these.  Write `θ = (0, 1, 0)`,
`ε = θ + 1 = (1, 1, 0)`, `g = θ + 3 = (3, 1, 0)`.  Then the list below is
`v·θ^r·g^t` for `v ∈ {1, −1, ε, −ε}` and `r, t ∈ {0, 1}`, in that order, with
norms

    1, 19, −2, −38,  −1, −19, 2, 38,  1, 19, −2, −38,  −1, −19, 2, 38.

The unit part is `{±1, ±ε}` because `ℤ[θ]ˣ = {±1} × ⟨ε⟩` (rank `1`, torsion
`{±1}`, fundamental unit `ε = θ + 1` of norm `1` — PARI/GP `bnfinit`, and the
`ε·(θ² + θ + 3) = 1` above is the Lean-side witness).  The prime part is `θ` and
`g` because THOSE ARE THE ONLY PRIMES THAT CAN DIVIDE `gcd(β, γ)`: with
`γ = adj β = (p² + 4pe² + 16e⁴, 2pe² + 8e⁴, 4e⁴)` one has `β·γ = N(β) = n²` and
the exact division

    γ = Q·β + D·e⁴,   Q = (p + 4e², 4e², 0),   D = (16, 16, 12),

with `N(D) = 2⁸·19 = 4864` and `D = uD·θ⁸·g` for the unit
`uD = (191, 83, 61)`, `N(uD) = 1` — all four identities verified numerically
against the multiplication table above.  So a prime dividing both `β` and `γ`
divides `D·e⁴`, hence is `θ`, `g`, or divides `e`; and the last is excluded by
`IsCoprime p e` through `β ≡ p mod θ`.

A PROOF should follow `MordellWeil.lean` lines `659`–`1852`
(`Cubic.ZS` through `descent_unit_square`) declaration by declaration.  The
field data, re-derived in PARI/GP: `poldisc(X³ + 2X² + 4X + 2) = −76 = disc(K)`
and `nfbasis` is `[1, θ, θ²]`, so the index is `1`; `h(K) = 1`; signature
`(1, 1)`; unit rank `1`, torsion `{±1}`, fundamental unit `θ + 1`.  Note
`−76 = −2²·19` is NOT squarefree, so — exactly as at level `11` — "the
discriminants agree, hence index `1`" is a CONCLUSION and not an input; the
minimal polynomial IS Eisenstein at `2`, which kills the `2`-part, and `19` must
be killed separately.  The trace, needed for the discriminant computation inside
`ℤ[θ]`, is `Tr(a + bθ + cθ²) = 3a − 2b − 4c`.

THE UNIT OBSTRUCTION, which is the step level `11`'s docstring flags as the one
that is easy to get wrong.  `N(ε) = +1` here (level `11` has `−1`), and in
NEITHER case does the norm alone force the exponent parity — what is needed is a
quadratic-residue obstruction at a degree-one prime, and level `19` has one at
**`q = 29`**: `X³ + 2X² + 4X + 2 ≡ 0 (mod 29)` at `θ ↦ 18`, so
`φ(a + bθ + cθ²) = a + 18b + 5c (mod 29)` is a ring map (`18² ≡ 5`), and
`φ(ε) = 19`, of which neither `19` nor `−19 = 10` is a square mod `29`.  This is
the analogue of `MazurLevel11.phi13`; the search that found it ran over primes
`q ≡ 1 (mod 4)` — that congruence is what makes `−1` a square, so that ONE
non-residue check rules out both `ε` and `−ε` — and `29, 37, 41, 53, 89, …` all
work.

**ENLARGING THE LIST IS SAFE**; shrinking it is not.  A successor who finds the
bookkeeping easier with more classes may add any units to the list: the two
consumers (`descent_square_class`, then `epsilon_class_impossible`) prune by
NORM and then by parity, and both are stated per-class. -/
theorem descent_unit_square {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (hn : zsNorm (descentImage p e) = n ^ 2) :
    ∃ u δ : ℤ × ℤ × ℤ, descentImage p e = zsMul u (zsMul δ δ) ∧
      u ∈ [((1 : ℤ), (0 : ℤ), (0 : ℤ)), (3, 1, 0), (0, 1, 0), (0, 3, 1),
        (-1, 0, 0), (-3, -1, 0), (0, -1, 0), (0, -3, -1),
        (1, 1, 0), (3, 4, 1), (0, 1, 1), (-2, -1, 2),
        (-1, -1, 0), (-3, -4, -1), (0, -1, -1), (2, 1, -2)] := sorry

/-- **The norm pruning** (PROVEN 2026-07-31): of the `16` square classes only the
two of norm `1` survive, so `β` is a square or `ε` times a square.

`N(β) = N(u)·N(δ)²` with `N(β) = n²` and `N(δ) ≠ 0` (else `n = 0`, refuted by
`descentImage_norm_ne_zero`), so `N(u)` must be a rational square.  The other
fourteen classes have `N(u) ∈ {−38, −19, −2, −1, 2, 19, 38}`: the negatives die
trivially and `2, 19, 38` by `sq_ne_mul_sq_of_not_isSquare`. -/
theorem descent_square_class {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (hn : zsNorm (descentImage p e) = n ^ 2) :
    ∃ a b c : ℤ, descentImage p e = zsMul (a, b, c) (a, b, c) ∨
      descentImage p e = zsMul (1, 1, 0) (zsMul (a, b, c) (a, b, c)) := by
  obtain ⟨u, δ, hbeta, hu⟩ := descent_unit_square he hcop hn
  obtain ⟨a, b, c⟩ := δ
  have hn0 : n ≠ 0 := descentImage_norm_ne_zero he hcop hn
  obtain ⟨M, hM⟩ : ∃ M : ℤ, zsNorm (a, b, c) = M := ⟨_, rfl⟩
  have hnorm : n ^ 2 = zsNorm u * M ^ 2 := by
    rw [← hM, ← hn, hbeta, zsNorm_zsMul, zsNorm_zsMul]; ring
  have hm0 : M ≠ 0 := by
    rintro rfl
    exact hn0 ((pow_eq_zero_iff two_ne_zero).mp (by rw [hnorm]; ring))
  fin_cases hu
  · exact ⟨a, b, c, Or.inl (by rw [hbeta, zsMul_one_left])⟩
  · exact absurd (show n ^ 2 = 19 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare not_isSquare_nineteen hm0)
  · exact absurd (show n ^ 2 = -2 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -38 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -1 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -19 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = 2 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        WeierstrassCurve.MazurLevel11.not_isSquare_two hm0)
  · exact absurd (show n ^ 2 = 38 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        not_isSquare_thirtyEight hm0)
  · exact ⟨a, b, c, Or.inr hbeta⟩
  · exact absurd (show n ^ 2 = 19 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare not_isSquare_nineteen hm0)
  · exact absurd (show n ^ 2 = -2 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -38 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -1 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = -19 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        (WeierstrassCurve.MazurLevel11.not_isSquare_of_neg (by norm_num)) hm0)
  · exact absurd (show n ^ 2 = 2 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        WeierstrassCurve.MazurLevel11.not_isSquare_two hm0)
  · exact absurd (show n ^ 2 = 38 * M ^ 2 by rw [hnorm]; norm_num [zsNorm])
      (WeierstrassCurve.MazurLevel11.sq_ne_mul_sq_of_not_isSquare
        not_isSquare_thirtyEight hm0)

/-- **THE LOCAL CONDITION, AND IT IS PURE PARITY** (PROVEN 2026-07-31): the
surviving nontrivial square class `ε = θ + 1` is impossible for a coprime point.

This is the one place the arithmetic of the curve enters, and — exactly as at
level `11` — it costs mod `4` and no `19`-adic input at all.  Writing
`β = (1 + θ)·(a + bθ + cθ²)²` in coordinates gives

    p    = a² − 2b² − 4ac + 4bc + 4c²,
    −2e² = a² + 2ab − 4b² − 8ac + 4bc + 10c²,
    0    = −b² + 2ab − 2ac − 4bc + 6c².

The second forces `a` even; the third then forces `b` even and, with `a, b`
even, `c` even (its `6c²` becomes divisible by `4`); the first then makes `p`
even and the second makes `e` even — contradicting `IsCoprime p e`.  Brute force
over `ℤ/4` independently confirms: zero solutions with `p, e` not both even, and
`ℤ/2` alone is NOT enough (it leaves two residue solutions).

Note what is NOT used: `he : 0 < e`, the curve equation, and any information
about `n`.  The class is killed by coprimality alone. -/
theorem epsilon_class_impossible {p e a b c : ℤ} (hcop : IsCoprime p e) :
    descentImage p e ≠ zsMul (1, 1, 0) (zsMul (a, b, c) (a, b, c)) := by
  intro h
  simp only [descentImage, zsMul, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (2 : ℤ) ∣ a := by
    refine Int.prime_two.dvd_of_dvd_pow (n := 2)
      ⟨-(e ^ 2) - a * b + 2 * b ^ 2 + 4 * (a * c) - 2 * (b * c) - 5 * c ^ 2, by linarith⟩
  obtain ⟨a₁, rfl⟩ := ha
  have hb : (2 : ℤ) ∣ b := by
    refine Int.prime_two.dvd_of_dvd_pow (n := 2)
      ⟨2 * (a₁ * b) - 2 * (a₁ * c) - 2 * (b * c) + 3 * c ^ 2, by linarith⟩
  obtain ⟨b₁, rfl⟩ := hb
  have hc : (2 : ℤ) ∣ c := by
    refine Int.prime_two.dvd_of_dvd_pow (n := 2)
      ⟨b₁ ^ 2 - 2 * (a₁ * b₁) + a₁ * c + 2 * (b₁ * c) - c ^ 2, by linarith⟩
  obtain ⟨c₁, rfl⟩ := hc
  have hp : (2 : ℤ) ∣ p :=
    ⟨2 * a₁ ^ 2 - 4 * b₁ ^ 2 - 8 * (a₁ * c₁) + 8 * (b₁ * c₁) + 8 * c₁ ^ 2, by linarith⟩
  have he : (2 : ℤ) ∣ e := by
    refine Int.prime_two.dvd_of_dvd_pow (n := 2)
      ⟨-(a₁ ^ 2) - 2 * (a₁ * b₁) + 4 * b₁ ^ 2 + 8 * (a₁ * c₁) - 4 * (b₁ * c₁)
        - 10 * c₁ ^ 2, by linarith⟩
  exact absurd (hcop.isUnit_of_dvd' hp he) (by decide)

/-! ### The `2`-descent proper: the halving witness

PROVEN 2026-07-31 over the single leaf `descent_unit_square`.
-/

/-- **THE `2`-DESCENT AT LEVEL `19`** (PROVEN 2026-07-31 over
`descent_square_class` and `epsilon_class_impossible`, hence over the single leaf
`descent_unit_square`; it was itself a sorry leaf for a few hours the same day,
cut out of `integral_leaf` before being decomposed one level further): the
descent image `β = p − 2e²θ` of a coprime integral point of
`W² = U³ + 4U² + 16U + 16` is a SQUARE in `ℤ[θ]`, `θ³ + 2θ² + 4θ + 2 = 0`, and
this is that fact written out in coordinates.

Reduction in `ℤ[θ]` is `θ³ = −2θ² − 4θ − 2` and `θ⁴ = 6θ + 4`, so

    (a + bθ + cθ²)² = (a² − 4bc + 4c²) + (2ab − 8bc + 6c²)θ + (b² + 2ac − 4bc)θ²,

and `β = δ²` with `δ = a + bθ + cθ²` reads exactly

    b² + 2ac − 4bc = 0,   p = a² − 4bc + 4c²,   e² = −ab + 4bc − 3c²

(the `θ`-coordinate `2ab − 8bc + 6c² = −2e²` halved).  These are the three
conjuncts below, and nothing else about `ℤ[θ]` appears anywhere in this file.

**IT IS CONSISTENT AT THE ONE REAL POINT**, which is the cheapest available check
on the whole derivation: `(a, b, c) = (2, 2, 1)` gives `4 + 4 − 8 = 0`,
`p = 4 − 8 + 4 = 0` and `e² = −4 + 8 − 3 = 1`, i.e. `(p, e) = (0, 1)` — and
`δ = θ² + 2θ + 2` is the square root recorded in the module docstring,
`−2θ = (θ² + 2θ + 2)²`.  Since `(0, 1)` is the ONLY solution of the hypotheses
(exhaustive search, `|p| ≤ 6000`, `1 ≤ e ≤ 300`), this statement is TRUE as
stated independently of the descent that proves it.

WHAT THE PROOF NEEDED, and what of it is now DONE.  The bullets below were
written when this was a leaf; the first three items are now discharged HERE — the
`{1, ε}` reduction is `descent_square_class` and the `ε`-exclusion is
`epsilon_class_impossible`, both PROVEN above — and only the LAST bullet, the
valuation bookkeeping, survives, as `descent_unit_square`.

* `ℤ[θ]` is the FULL ring of integers of the cubic field of discriminant `−76`
  (index `1`: `−76/f²` would have to be `−19` for `f = 2`, and `−19` is not a
  cubic field discriminant, the smallest complex one being `−23`).  Level `11`
  proves the corresponding `disc = −44` statement via an Eisenstein-at-`2`
  minimal polynomial and an explicit `mul11_mem` denominator bound; here the
  minimal polynomial `θ³ + 2θ² + 4θ + 2` is Eisenstein at `2` in the same way.
* Class number `1` (`Cubic.ZS.isPrincipalIdealRing_zs` at level `11`, via
  Minkowski over `NumberField.discr`).
* Units mod squares: rank `1`, fundamental unit `ε = θ + 1` of norm `1`, so the
  ambiguity is `{1, ε}` — `N(−1) = −1 < 0` cannot divide the square `n²`.  The
  `ε`-class must then be excluded, which at level `11` is
  `epsilon_class_impossible`, a character mod `13`.
* The valuation bookkeeping at the ramified primes, `(2) = (θ)³` and
  `19 = 𝔮₁𝔮₂²` with both residue degrees `1` (level `11`:
  `Cubic.ZS.descent_zs`).

A successor should follow `MordellWeil.lean` lines `659`–`1852`
(`MazurLevel11.Cubic.ZS` through `descent_unit_square`) declaration by
declaration; the ONLY things that change are the constants, which are all
gathered in `descent_unit_square`'s docstring. -/
theorem exists_halving_witness {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    ∃ a b c : ℤ, b ^ 2 + 2 * a * c - 4 * b * c = 0 ∧
      p = a ^ 2 - 4 * b * c + 4 * c ^ 2 ∧
      e ^ 2 = -(a * b) + 4 * b * c - 3 * c ^ 2 := by
  obtain ⟨a, b, c, hsq | hbad⟩ :=
    descent_square_class (n := n) he hcop (by rw [zsNorm_descentImage]; linarith)
  · refine ⟨a, b, c, ?_, ?_, ?_⟩ <;>
      · simp only [descentImage, zsMul, Prod.mk.injEq] at hsq
        obtain ⟨h1, h2, h3⟩ := hsq
        linarith
  · exact absurd hbad (epsilon_class_impossible hcop)

/-! ### `halving_descends`, decomposed: eliminate `m` and `c` first

The halving coordinates `m` and `c` carry no arithmetic — they are removed
outright by three `linear_combination`s, exactly as at level `11`, and what is
left is a statement about two explicit binary forms.

At level `19` the duplication formula on `W² = U³ + 4U² + 16U + 16`
(`a₂ = a₄ = a₆ = 16`, `a₂ = 4`) is

    U(2Q) = (U⁴ − 2a₄U² − 8a₆U + a₄² − 4a₂a₆) / (4(U³ + 4U² + 16U + 16))
          = (U⁴ − 32U² − 128U) / (4(U³ + 4U² + 16U + 16)),

so the two binary forms of this file are

    F(X, Y) = X⁴ − 32X²Y² − 128XY³,   G(X, Y) = X³ + 4X²Y + 16XY² + 16Y³,

against level `11`'s `X⁴ − 128XY³ + 256Y⁴` and `X³ − 4X²Y + 16Y³`.  Note the
constant term of `F` vanishes — `U = 0` is the `3`-torsion point, which duplicates
to itself — which is why the exceptional set below has ONE element rather than
level `11`'s two.
-/

/-- **The norm half of the halving, with `c` eliminated** (PROVEN 2026-07-31):
`c²·n'² = 16·e²·e'⁶`, i.e. `(c·n')² = (4·e·e'³)²`.

`c³n'² = (cp')³ + 4c(cp')²e'² + 16c²(cp')e'⁴ + 16c³e'⁶ = 8e'⁶(m³ + 2cm² + 4c²m +
2c³) = 16c·e²e'⁶` using `cp' = 2me'²` and the covering identity, and one factor
of `c` cancels.  Downstream this gives `n' ≠ 0`, so the halved point is affine. -/
theorem halving_norm_relation {e m c p' e' n' : ℤ} (hc : c ≠ 0)
    (hcov : 2 * c * e ^ 2 = m ^ 3 + 2 * c * m ^ 2 + 4 * c ^ 2 * m + 2 * c ^ 3)
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (hn' : n' ^ 2 = p' ^ 3 + 4 * p' ^ 2 * e' ^ 2 + 16 * p' * e' ^ 4 + 16 * e' ^ 6) :
    c ^ 2 * n' ^ 2 = 16 * e ^ 2 * e' ^ 6 := by
  have hcp : c * p' = 2 * m * e' ^ 2 := by linarith
  refine mul_left_cancel₀ hc ?_
  linear_combination (c ^ 3) * hn' +
    ((c * p') ^ 2 + (c * p') * (2 * m * e' ^ 2) + (2 * m * e' ^ 2) ^ 2
      + 4 * c * e' ^ 2 * (c * p' + 2 * m * e' ^ 2) + 16 * c ^ 2 * e' ^ 4) * hcp
    - 8 * e' ^ 6 * hcov

/-- **The `x`-half of the halving, with `c` eliminated** (PROVEN 2026-07-31):
`c²·(p'⁴ − 32p'²e'⁴ − 128p'e'⁶) = 64·p·e'⁸`.

This is the numerator of the duplication formula: `c⁴F(p', e'²) = (cp')⁴ −
32c²(cp')²e'⁴ − 128c³(cp')e'⁶ = 16e'⁸(m⁴ − 8c²m² − 16c³m) = 64c²p·e'⁸`, and `c²`
cancels. -/
theorem halving_x_relation {p m c p' e' : ℤ} (hc : c ≠ 0)
    (hpm : 4 * c ^ 2 * p = m ^ 4 - 8 * m ^ 2 * c ^ 2 - 16 * m * c ^ 3)
    (hcross : 2 * m * e' ^ 2 = p' * c) :
    c ^ 2 * (p' ^ 4 - 32 * p' ^ 2 * e' ^ 4 - 128 * p' * e' ^ 6) = 64 * p * e' ^ 8 := by
  have hcp : c * p' = 2 * m * e' ^ 2 := by linarith
  refine mul_left_cancel₀ (pow_ne_zero 2 hc) ?_
  linear_combination
    (((c * p') ^ 3 + (c * p') ^ 2 * (2 * m * e' ^ 2) + (c * p') * (2 * m * e' ^ 2) ^ 2
        + (2 * m * e' ^ 2) ^ 3)
      - 32 * c ^ 2 * e' ^ 4 * (c * p' + 2 * m * e' ^ 2) - 128 * c ^ 3 * e' ^ 6) * hcp
    - 16 * e' ^ 8 * hpm

/-- **THE HALVING, WITH `m` AND `c` GONE** (PROVEN 2026-07-31): the duplication
formula as a single identity between the two coprime integral models,

    e²·(p'⁴ − 32p'²e'⁴ − 128p'e'⁶)  =  4·p·e'²·n'² ,

i.e. `p/e² = F(p', e'²) / (4e'²·G(p', e'²))` since `n'² = G(p', e'²)`.  Obtained
by multiplying `halving_x_relation` by `n'²`, substituting
`halving_norm_relation`, and cancelling `16e'⁶`. -/
theorem halving_relation {p e m c p' e' n' : ℤ} (hc : c ≠ 0) (he' : e' ≠ 0)
    (hcov : 2 * c * e ^ 2 = m ^ 3 + 2 * c * m ^ 2 + 4 * c ^ 2 * m + 2 * c ^ 3)
    (hpm : 4 * c ^ 2 * p = m ^ 4 - 8 * m ^ 2 * c ^ 2 - 16 * m * c ^ 3)
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (hn' : n' ^ 2 = p' ^ 3 + 4 * p' ^ 2 * e' ^ 2 + 16 * p' * e' ^ 4 + 16 * e' ^ 6) :
    e ^ 2 * (p' ^ 4 - 32 * p' ^ 2 * e' ^ 4 - 128 * p' * e' ^ 6) = 4 * p * e' ^ 2 * n' ^ 2 := by
  have hI := halving_norm_relation (e := e) hc hcov hcross hn'
  have hII := halving_x_relation (p := p) hc hpm hcross
  have h16 : (16 * e' ^ 6 : ℤ) ≠ 0 := by
    have h6 : e' ^ 6 ≠ 0 := pow_ne_zero 6 he'
    simpa using h6
  refine mul_left_cancel₀ h16 ?_
  linear_combination (-(p' ^ 4 - 32 * p' ^ 2 * e' ^ 4 - 128 * p' * e' ^ 6)) * hI + n' ^ 2 * hII

/-- **THE NON-ARCHIMEDEAN HALF OF THE HEIGHT BOUND** (PROVEN 2026-07-31): any
common divisor of the two binary forms

    F(X, Y) = X⁴ − 32X²Y² − 128XY³   and   4Y·G(X, Y) = 4Y(X³ + 4X²Y + 16XY² + 16Y³)

at a COPRIME pair `(X, Y)` divides `2¹⁰·19² = 369664`.

Two integral Bezout identities, both checked by `linear_combination`:

    (4Y(3X² + 8XY + 48Y²))·F + (−3X³ + 4X²Y + 80XY² + 304Y³)·(4YG) = 19456·Y⁷,
    (19X³ + 64X²Y + 352XY² + 384Y³)·F + (−16X³ + 128X²Y + 768XY²)·(4YG) = 19·X⁷,

with `19456 = 2¹⁰·19`.  Then `k ∣ 19456·Y⁷` and `k ∣ 19·X⁷`, and with
`u·X⁷ + v·Y⁷ = 1` one writes `369664 = 19456u·(19X⁷) + 19v·(19456Y⁷)`.

The first identity is the extended Euclidean algorithm for `f = X⁴ − 32X² − 128X`
and `g = X³ + 4X² + 16X + 16` cleared of denominators (`4864 = 2⁸·19`, times the
`4Y`); the second is the same for the reversed polynomials, plus one syzygy
`(u, w) ↦ (u + 24G, w − 24F)` — needed because the raw cofactor of `G` is not
divisible by `Y`, and adding `24` (the constant term of the raw cofactor,
against `F ≡ X⁴ mod Y`) makes it so.  The bare resultant is
`Res(F, 4YG) = 2²⁴·19²`; as at level `11` the Bezout cofactors clear far less. -/
theorem forms_common_dvd {X Y k : ℤ} (hcop : IsCoprime X Y)
    (h1 : k ∣ X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3)
    (h2 : k ∣ 4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)) :
    k ∣ 369664 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hY : k ∣ 19456 * Y ^ 7 :=
    ⟨4 * Y * (3 * X ^ 2 + 8 * X * Y + 48 * Y ^ 2) * a
        + (-3 * X ^ 3 + 4 * X ^ 2 * Y + 80 * X * Y ^ 2 + 304 * Y ^ 3) * b, by
      linear_combination (4 * Y * (3 * X ^ 2 + 8 * X * Y + 48 * Y ^ 2)) * ha
        + (-3 * X ^ 3 + 4 * X ^ 2 * Y + 80 * X * Y ^ 2 + 304 * Y ^ 3) * hb⟩
  have hX : k ∣ 19 * X ^ 7 :=
    ⟨(19 * X ^ 3 + 64 * X ^ 2 * Y + 352 * X * Y ^ 2 + 384 * Y ^ 3) * a
        + (-16 * X ^ 3 + 128 * X ^ 2 * Y + 768 * X * Y ^ 2) * b, by
      linear_combination (19 * X ^ 3 + 64 * X ^ 2 * Y + 352 * X * Y ^ 2 + 384 * Y ^ 3) * ha
        + (-16 * X ^ 3 + 128 * X ^ 2 * Y + 768 * X * Y ^ 2) * hb⟩
  obtain ⟨u, v, huv⟩ := hcop.pow (m := 7) (n := 7)
  obtain ⟨cX, hcX⟩ := hX
  obtain ⟨cY, hcY⟩ := hY
  exact ⟨19456 * u * cX + 19 * v * cY, by
    linear_combination (19456 * u) * hcX + (19 * v) * hcY - 369664 * huv⟩

/-- **THE ARCHIMEDEAN INGREDIENT** (PROVEN 2026-07-31): the two binary quartics
are never both small,

    max(|X|, Y)⁴  ≤  4·max(|F(X, Y)|, |4Y·G(X, Y)|)     for `Y > 0`,

with `F(X, Y) = X⁴ − 32X²Y² − 128XY³` and `G(X, Y) = X³ + 4X²Y + 16XY² + 16Y³`.

THE PROOF, by three exact identities and no estimation.  Write `t = X/Y`.

* `4F − X⁴ = X(X − 8Y)(3X² + 24XY + 64Y²)`, and `3X² + 24XY + 64Y² =
  3(X + 4Y)² + 16Y² > 0`.  So `4F ≥ X⁴` exactly on `t ≤ 0` and `t ≥ 8`.
* `16Y·G − X⁴ = X³(16Y − X) + 64X²Y² + 256XY³ + 256Y⁴`, manifestly `≥ 0` on
  `0 ≤ X ≤ 16Y`, which covers the gap `0 < t < 8` with room to spare.
* `G − 3Y³ = (X + Y)(X² + 3XY + 13Y²)` and `4(X² + 3XY + 13Y²) = (2X + 3Y)² +
  43Y² > 0`, so `G ≥ 3Y³` whenever `X ≥ −Y` — which handles the branch `|X| ≤ Y`,
  where the height is `Y` and `4·|4YG| ≥ 48Y⁴`.

Contrast level `11`, where `4|f|` failed on TWO intervals and the `G`-branch was
tight (equality at `t = 4`).  Here nothing is tight: the worst case is `t = 8`,
where `4F = X⁴` exactly, and it is covered twice over. -/
theorem forms_archimedean {X Y : ℤ} (hY : 0 < Y) :
    max X.natAbs Y.natAbs ^ 4 ≤
      4 * max (X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3).natAbs
        (4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)).natAbs := by
  have hY3 : (0 : ℤ) < Y ^ 3 := pow_pos hY 3
  have hY4 : (0 : ℤ) < Y ^ 4 := pow_pos hY 4
  have hmain : max |X| Y ^ 4 ≤
      4 * max |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3|
        |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| := by
    have hFle : |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3| ≤
        max |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3|
          |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| := le_max_left _ _
    have hGle : |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| ≤
        max |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3|
          |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| := le_max_right _ _
    have hquad : (0 : ℤ) < X ^ 2 + 3 * X * Y + 13 * Y ^ 2 := by
      nlinarith [sq_nonneg (2 * X + 3 * Y), hY4, sq_nonneg Y]
    rcases le_or_gt |X| Y with hle | hgt
    · -- `|X| ≤ Y`: the height is `Y`, and `G ≥ 3Y³` outright.
      rw [max_eq_right hle]
      have hXY : -Y ≤ X := (abs_le.mp hle).1
      have hG3 : 3 * Y ^ 3 ≤ X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ X + Y) hquad.le]
      have hGpos : 12 * Y ^ 4 ≤ 4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3) := by
        nlinarith [mul_le_mul_of_nonneg_left hG3 (by linarith : (0 : ℤ) ≤ 4 * Y)]
      have hGabs : 12 * Y ^ 4 ≤
          |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| :=
        le_trans hGpos (le_abs_self _)
      linarith
    · -- `Y < |X|`: the height is `|X|`, and `max |X| Y ^ 4 = X ^ 4`.
      rw [max_eq_left hgt.le]
      have habs4 : |X| ^ 4 = X ^ 4 := by
        rw [← abs_pow]; exact abs_of_nonneg (by positivity)
      rw [habs4]
      have hq2 : (0 : ℤ) < 3 * X ^ 2 + 24 * X * Y + 64 * Y ^ 2 := by
        nlinarith [sq_nonneg (X + 4 * Y), hY4, sq_nonneg Y]
      rcases le_or_gt X 0 with h0 | h0
      · -- `t ≤ 0`: `4F − X⁴ = X(X − 8Y)(3X² + 24XY + 64Y²) ≥ 0`.
        have hXneg : X < 0 := by
          rcases lt_or_eq_of_le h0 with h | h
          · exact h
          · exfalso; rw [h] at hgt; simp at hgt; omega
        have hprod : (0 : ℤ) ≤ X * (X - 8 * Y) :=
          le_of_lt (mul_pos_of_neg_of_neg hXneg (by linarith))
        have h4F : X ^ 4 ≤ 4 * (X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3) := by
          nlinarith [mul_nonneg hprod hq2.le]
        have hFabs : X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3 ≤
            |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3| := le_abs_self _
        linarith
      · rcases le_or_gt X (8 * Y) with h8 | h8
        · -- `0 < t ≤ 8`: `16YG − X⁴ = X³(16Y − X) + 64X²Y² + 256XY³ + 256Y⁴ ≥ 0`.
          have hX3 : (0 : ℤ) < X ^ 3 := by positivity
          have ht1 : (0 : ℤ) ≤ X ^ 3 * (16 * Y - X) := mul_nonneg hX3.le (by linarith)
          have ht2 : (0 : ℤ) ≤ 64 * X ^ 2 * Y ^ 2 := by positivity
          have ht3 : (0 : ℤ) ≤ 256 * X * Y ^ 3 := by positivity
          have h4G : X ^ 4 ≤
              4 * (4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)) := by
            nlinarith [ht1, ht2, ht3, hY4]
          have hGabs : 4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3) ≤
              |4 * Y * (X ^ 3 + 4 * X ^ 2 * Y + 16 * X * Y ^ 2 + 16 * Y ^ 3)| := le_abs_self _
          linarith
        · -- `t > 8`: `4F − X⁴ = X(X − 8Y)(3X² + 24XY + 64Y²) > 0`.
          have hprod : (0 : ℤ) ≤ X * (X - 8 * Y) :=
            le_of_lt (mul_pos h0 (by linarith))
          have h4F : X ^ 4 ≤ 4 * (X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3) := by
            nlinarith [mul_nonneg hprod hq2.le]
          have hFabs : X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3 ≤
              |X ^ 4 - 32 * X ^ 2 * Y ^ 2 - 128 * X * Y ^ 3| := le_abs_self _
          linarith
  -- Transport back to `ℕ`.
  rw [← Nat.cast_le (α := ℤ)]
  push_cast [Int.natCast_natAbs]
  rw [abs_of_pos hY]
  exact hmain

/-- **THE RESULTANT / HEIGHT NODE at level `19`** (PROVEN 2026-07-31 over
`forms_archimedean`, `forms_common_dvd` and `MazurLevel11.reduced_fraction`): the
halving either strictly drops the height, or the point was small all along.

**THIS IS THE FINITE-GENERATION CONTENT OF LEVEL `19`.**  A `2`-descent alone
gives unique `2`-divisibility, which infinite groups satisfy too; it is exactly
this height inequality that converts it into finiteness.

Put `H = max(|p|, e²)`, `H' = max(|p'|, e'²)`, `A = F(p', e'²)`,
`B = 4e'²·G(p', e'²) = 4e'²n'² > 0`.  Then `H = max(|A|, B)/k` for the single `k`
of `reduced_fraction`; `k ∣ 369664` by `forms_common_dvd`; and
`max(|A|, B) ≥ H'⁴/4` by `forms_archimedean`.  Combining, `H'⁴ ≤ 4·369664·H`, and
if the height does NOT drop then `H ≤ 2H'`, so

    H⁴ ≤ 16H'⁴ ≤ 16·4·369664·H = 23658496·H,

i.e. `H³ ≤ 23658496 = 2²⁴·19²/2⁸ = Res(F, G)`, giving `H ≤ 287` and
`|p| + e² ≤ 2H ≤ 574`.  That is the box `smallPoints` searches. -/
theorem height_drop_or_small {p e p' e' n' : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (he' : 0 < e') (hcop' : IsCoprime p' e') (hn'0 : n' ≠ 0)
    (hn' : n' ^ 2 = p' ^ 3 + 4 * p' ^ 2 * e' ^ 2 + 16 * p' * e' ^ 4 + 16 * e' ^ 6)
    (hrel : e ^ 2 * (p' ^ 4 - 32 * p' ^ 2 * e' ^ 4 - 128 * p' * e' ^ 6)
      = 4 * p * e' ^ 2 * n' ^ 2) :
    p'.natAbs + (e' ^ 2).natAbs < p.natAbs + (e ^ 2).natAbs ∨
      p.natAbs + (e ^ 2).natAbs ≤ 574 := by
  set A : ℤ := p' ^ 4 - 32 * p' ^ 2 * e' ^ 4 - 128 * p' * e' ^ 6 with hA
  set B : ℤ := 4 * e' ^ 2 * n' ^ 2 with hBdef
  have hBpos : 0 < B := by
    have h1 : (0 : ℤ) < e' ^ 2 := pow_pos he' 2
    have h2 : (0 : ℤ) < n' ^ 2 := by positivity
    rw [hBdef]; positivity
  have hrel' : e ^ 2 * A = p * B := by rw [hA, hBdef]; linear_combination hrel
  obtain ⟨k, hk0, hkB, hkA⟩ :=
    WeierstrassCurve.MazurLevel11.reduced_fraction he hcop hBpos hrel'
  have hAform : A = p' ^ 4 - 32 * p' ^ 2 * (e' ^ 2) ^ 2 - 128 * p' * (e' ^ 2) ^ 3 := by
    rw [hA]; ring
  have hBform : B = 4 * e' ^ 2 * (p' ^ 3 + 4 * p' ^ 2 * (e' ^ 2)
      + 16 * p' * (e' ^ 2) ^ 2 + 16 * (e' ^ 2) ^ 3) := by
    rw [hBdef, hn']; ring
  have hkdvd : k ∣ 369664 :=
    forms_common_dvd (X := p') (Y := e' ^ 2) hcop'.pow_right
      (by rw [← hAform, hkA]; exact Dvd.intro_left p rfl)
      (by rw [← hBform, hkB]; exact Dvd.intro_left (e ^ 2) rfl)
  have hkle : k.natAbs ≤ 369664 := by
    have hd : k.natAbs ∣ 369664 := by
      have hdd := Int.natAbs_dvd_natAbs.mpr hkdvd
      simpa using hdd
    exact Nat.le_of_dvd (by norm_num) hd
  set H : ℕ := max p.natAbs (e ^ 2).natAbs with hH
  set H' : ℕ := max p'.natAbs (e' ^ 2).natAbs with hH'
  have harch : H' ^ 4 ≤ 4 * max A.natAbs B.natAbs := by
    rw [hH', hAform, hBform]
    exact forms_archimedean (X := p') (Y := e' ^ 2) (pow_pos he' 2)
  have hmaxmul : ∀ a b c : ℕ, max (a * c) (b * c) = max a b * c := by
    intro a b c
    rcases Nat.le_total a b with hab | hab
    · rw [Nat.max_eq_right hab, Nat.max_eq_right (Nat.mul_le_mul hab (le_refl c))]
    · rw [Nat.max_eq_left hab, Nat.max_eq_left (Nat.mul_le_mul hab (le_refl c))]
  have hAB : max A.natAbs B.natAbs = H * k.natAbs := by
    rw [hkA, hkB, hH, Int.natAbs_mul, Int.natAbs_mul, hmaxmul]
  have hmain : H' ^ 4 ≤ 1478656 * H := by
    calc H' ^ 4 ≤ 4 * max A.natAbs B.natAbs := harch
      _ = 4 * (H * k.natAbs) := by rw [hAB]
      _ ≤ 4 * (H * 369664) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left H hkle)
      _ = 1478656 * H := by ring
  by_cases hdrop : p'.natAbs + (e' ^ 2).natAbs < p.natAbs + (e ^ 2).natAbs
  · exact Or.inl hdrop
  · refine Or.inr ?_
    replace hdrop : p.natAbs + (e ^ 2).natAbs ≤ p'.natAbs + (e' ^ 2).natAbs :=
      Nat.not_lt.mp hdrop
    have hHs : H ≤ p.natAbs + (e ^ 2).natAbs := by rw [hH]; omega
    have hs'H' : p'.natAbs + (e' ^ 2).natAbs ≤ 2 * H' := by rw [hH']; omega
    have hH2 : H ≤ 2 * H' := le_trans hHs (le_trans hdrop hs'H')
    have hcube : H ^ 4 ≤ 23658496 * H := by
      calc H ^ 4 ≤ (2 * H') ^ 4 := Nat.pow_le_pow_left hH2 4
        _ = 16 * H' ^ 4 := by ring
        _ ≤ 16 * (1478656 * H) := Nat.mul_le_mul_left 16 hmain
        _ = 23658496 * H := by ring
    have hH287 : H ≤ 287 := by
      by_contra hcon
      have h288 : 288 ≤ H := Nat.lt_of_not_le hcon
      have hp3 : (288 : ℕ) ^ 3 ≤ H ^ 3 := Nat.pow_le_pow_left h288 3
      have hbig : 23887872 * H ≤ H ^ 4 := by
        calc 23887872 * H = 288 ^ 3 * H := by norm_num
          _ ≤ H ^ 3 * H := Nat.mul_le_mul hp3 (le_refl H)
          _ = H ^ 4 := by ring
      omega
    have hle2H : p.natAbs + (e ^ 2).natAbs ≤ 2 * H := by rw [hH]; omega
    omega

/-! ### The finite base case, by a bitmask quadratic-residue sieve

Transcribed from `MazurLevel11`, whose `qrMaskBad` / `qrMaskBad_sq` are reused
verbatim — only the modulus list, the box and the exceptional set change.  The
eight prime-power moduli were FOUND, not guessed: a greedy search over prime
powers `< 256` picked at each step the modulus killing the most survivors of the
`11158` coprime cells in the box, and `5` alone kills `5608` of the `7461`
non-negative ones.  All eight are load-bearing.
-/

/-- The sieve: `N` is rejected if it is negative or a quadratic non-residue
modulo any of eight prime powers. -/
def sieveBad (N : ℤ) : Bool :=
  decide (N < 0)
  || WeierstrassCurve.MazurLevel11.qrMaskBad 5 19 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 128
      2668882576834431627811302641479385619 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 11 571 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 89 526807005835216593886842679 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 29 332473075 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 73 9059857384996697084767 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 53 5310023542746835 N
  || WeierstrassCurve.MazurLevel11.qrMaskBad 9 147 N

set_option maxRecDepth 20000 in
/-- A perfect square survives the sieve.  Each mask is re-derived inside Lean by
`decide` from `qrMaskBad_sq`'s hypothesis, so no arithmetic claim about the
constants above needs to be trusted. -/
theorem sieveBad_sq (n : ℤ) : sieveBad (n ^ 2) = false := by
  have h0 : decide ((n : ℤ) ^ 2 < 0) = false := by
    simp only [decide_eq_false_iff_not, not_lt]; positivity
  simp only [sieveBad, h0,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 5) (mask := 19)
      (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 128)
      (mask := 2668882576834431627811302641479385619) (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 11) (mask := 571)
      (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 89)
      (mask := 526807005835216593886842679) (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 29) (mask := 332473075)
      (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 73) (mask := 9059857384996697084767)
      (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 53) (mask := 5310023542746835)
      (by norm_num) (by decide) n,
    WeierstrassCurve.MazurLevel11.qrMaskBad_sq (q := 9) (mask := 147)
      (by norm_num) (by decide) n,
    Bool.or_false]

/-- One cell of the search: `true` means "this `(e, p)` is disposed of" — outside
the box, not coprime, the one genuine point, or sieved out. -/
def sieveCell (e p : ℤ) : Bool :=
  decide (574 < p.natAbs + (e ^ 2).natAbs)
  || decide (Int.gcd p e ≠ 1)
  || decide (p = 0 ∧ e = 1)
  || sieveBad (p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6)

/-- The whole search: `e = i + 1` for `i < 23` (since `e² ≤ 574`) and
`p = j − 574` for `j < 1149` (since `|p| ≤ 574`).  `23 × 1149 = 26427` cells. -/
def sieveComplete : Bool :=
  (List.range 23).all fun i =>
    (List.range 1149).all fun j => sieveCell ((i : ℤ) + 1) ((j : ℤ) - 574)

set_option maxRecDepth 10000 in
/-- **THE FINITE SEARCH, DISCHARGED BY THE KERNEL** (2026-07-31). -/
theorem sieveComplete_true : sieveComplete = true := by decide +kernel

/-- **THE FINITE BASE CASE at level `19`** (PROVEN 2026-07-31 by a bitmask
quadratic-residue sieve): the only SMALL coprime integral point of
`W² = U³ + 4U² + 16U + 16` is the real one.

This is `integral_leaf` restricted to `|p| + e² ≤ 574`, and unlike that statement
it is a FINITE check: `1 ≤ e ≤ 23` and `|p| ≤ 574`, `11159` coprime pairs in the
box out of `26427` cells, each decided by whether
`p³ + 4p²e² + 16pe⁴ + 16e⁶` is a perfect square; it is negative — hence instantly
not a square — on `3697` of them. -/
theorem smallPoints {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6)
    (hsmall : p.natAbs + (e ^ 2).natAbs ≤ 574) :
    p = 0 ∧ e = 1 := by
  have hgcd : Int.gcd p e = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hesq : e ^ 2 ≤ 574 := by
    have h1 : (e ^ 2).natAbs ≤ 574 := le_trans (Nat.le_add_left _ _) hsmall
    have h2 : (0 : ℤ) ≤ e ^ 2 := sq_nonneg e
    omega
  have he23 : e ≤ 23 := by nlinarith
  have hpb : p.natAbs ≤ 574 := le_trans (Nat.le_add_right _ _) hsmall
  have hple : -574 ≤ p ∧ p ≤ 574 := by omega
  set i : ℕ := (e - 1).toNat with hidef
  set j : ℕ := (p + 574).toNat with hjdef
  have hie : ((i : ℤ)) + 1 = e := by omega
  have hjp : ((j : ℤ)) - 574 = p := by omega
  have hi : i < 23 := by omega
  have hj : j < 1149 := by omega
  have hcell : sieveCell ((i : ℤ) + 1) ((j : ℤ) - 574) = true :=
    List.all_eq_true.mp
      (List.all_eq_true.mp sieveComplete_true i (List.mem_range.mpr hi)) j
      (List.mem_range.mpr hj)
  rw [hie, hjp] at hcell
  have hbad : sieveBad (p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) = false := by
    rw [← h]; exact sieveBad_sq n
  simp only [sieveCell, hbad, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hcell
  rcases hcell with (h1 | h1) | h1
  · omega
  · exact absurd hgcd h1
  · exact h1

/-- **THE HEIGHT STEP at level `19`** (PROVEN 2026-07-31 over
`height_drop_or_small` and `smallPoints`): the halving supplied by
`exists_halving_witness` strictly decreases the height, except at the one point
that is actually there. -/
theorem halving_descends {p e n m c p' e' n' : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) (hc : c ≠ 0)
    (hcov : 2 * c * e ^ 2 = m ^ 3 + 2 * c * m ^ 2 + 4 * c ^ 2 * m + 2 * c ^ 3)
    (hpm : 4 * c ^ 2 * p = m ^ 4 - 8 * m ^ 2 * c ^ 2 - 16 * m * c ^ 3)
    (he' : 0 < e') (hcop' : IsCoprime p' e')
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (hn' : n' ^ 2 = p' ^ 3 + 4 * p' ^ 2 * e' ^ 2 + 16 * p' * e' ^ 4 + 16 * e' ^ 6) :
    (p = 0 ∧ e = 1) ∨ p'.natAbs + (e' ^ 2).natAbs < p.natAbs + (e ^ 2).natAbs := by
  have hI := halving_norm_relation (e := e) hc hcov hcross hn'
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    have h1 : (0 : ℤ) < e ^ 2 := pow_pos he 2
    have h2 : (0 : ℤ) < e' ^ 6 := pow_pos he' 6
    have hz : (0 : ℤ) = 16 * e ^ 2 * e' ^ 6 := by linear_combination hI
    nlinarith [h1, h2]
  have hrel := halving_relation hc he'.ne' hcov hpm hcross hn'
  rcases height_drop_or_small he hcop he' hcop' hn'0 hn' hrel with hlt | hsm
  · exact Or.inr hlt
  · exact Or.inl (smallPoints he hcop h hsm)

/-- **The halving witness has `c ≠ 0`** (PROVEN 2026-07-31).  If `c = 0` the
quadric `b² + 2ac − 4bc = 0` collapses to `b² = 0`, and then
`e² = −ab + 4bc − 3c² = 0` contradicts `0 < e`. -/
theorem witness_c_ne_zero {e a b c : ℤ} (he : 0 < e)
    (hq : b ^ 2 + 2 * a * c - 4 * b * c = 0)
    (hee : e ^ 2 = -(a * b) + 4 * b * c - 3 * c ^ 2) : c ≠ 0 := by
  rintro rfl
  have hb2 : b ^ 2 = 0 := by linear_combination hq
  have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb2
  have hz : e ^ 2 = 0 := by rw [hee, hb]; ring
  have he0 : e = 0 := pow_eq_zero_iff two_ne_zero |>.mp hz
  omega

/-- **Triviality of the halved point ascends** (PROVEN 2026-07-31): if the
halving `Q` of `P` is the known point, so is `P`.

This is the duplication of the rational `3`-torsion, done in integers.  If
`(p', e') = (0, 1)` then `U' = 0`, so `m = 0`, and the `x`-covering identity
collapses to `p = 0`; coprimality alone then forces `e = 1`.  That is
`2·(0, 4) = (0, −4)` on `W² = U³ + 4U² + 16U + 16` — the `3`-torsion point
duplicating to its own inverse, which is what makes the descent close upwards
instead of merely producing ever smaller solutions.

The covering identity `hcov` is NOT a hypothesis here, unlike at level `11`:
there the exceptional branch `U' = 0` gave `p = 4c²` and needed `e² = c²` to see
`e ∣ p`, whereas here it gives `p = 0` outright and `IsCoprime 0 e` finishes. -/
theorem trivial_ascends {p e m c p' e' : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (hc : c ≠ 0)
    (hpm : 4 * c ^ 2 * p = m ^ 4 - 8 * m ^ 2 * c ^ 2 - 16 * m * c ^ 3)
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (h' : p' = 0 ∧ e' = 1) :
    p = 0 ∧ e = 1 := by
  have hc2 : (4 * c ^ 2 : ℤ) ≠ 0 := by positivity
  obtain ⟨hp', he'1⟩ := h'
  subst hp'; subst he'1
  have hm : m = 0 := by linarith [hcross]
  subst hm
  have hpv : p = 0 := by
    refine mul_left_cancel₀ hc2 ?_
    linear_combination hpm
  have hu : IsUnit e := by
    rw [hpv] at hcop
    exact isCoprime_zero_left.mp hcop
  have he1 : e = 1 := by
    rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
  exact ⟨hpv, he1⟩

/-- **The infinite descent at level `19`** (PROVEN 2026-07-31 over
`exists_halving_witness`), by strong induction on `|p| + e²`.

Each step: take the halving witness `(a, b, c)`; `c ≠ 0`; put `m = b − 2c`, for
which the `θ²`-equation eliminates `a` and gives the two covering identities

    2c·e² = m³ + 2cm² + 4c²m + 2c³,   4c²·p = m⁴ − 8m²c² − 16mc³

by `linear_combination`; pass to the rational point `(U', W') = (2m/c, 4e/c)` of
the SAME curve — which lies on it precisely because `θ³ + 2θ² + 4θ + 2 = 0` is
the minimal polynomial, `W'² = 8·(m/c)³ + 16(m/c)² + 32(m/c) + 16 =
8·P(m/c) = 16e²/c²` — and take its coprime integral model with
`RationalPointDescent.exists_int_model`; then either `P` is the known point, or
the model is strictly smaller and the induction hypothesis applies, and
`trivial_ascends` carries the conclusion back up. -/
theorem integral_leaf_aux : ∀ N : ℕ, ∀ p e n : ℤ, p.natAbs + (e ^ 2).natAbs ≤ N →
    0 < e → IsCoprime p e →
    n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6 →
    p = 0 ∧ e = 1 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p e n hN he hcop h
    obtain ⟨a, b, c, hq, hp, hee⟩ := exists_halving_witness he hcop h
    have hc : c ≠ 0 := witness_c_ne_zero he hq hee
    set m : ℤ := b - 2 * c with hm
    have hcov : 2 * c * e ^ 2 = m ^ 3 + 2 * c * m ^ 2 + 4 * c ^ 2 * m + 2 * c ^ 3 := by
      rw [hm]; linear_combination (2 * c) * hee - b * hq
    have hpm : 4 * c ^ 2 * p = m ^ 4 - 8 * m ^ 2 * c ^ 2 - 16 * m * c ^ 3 := by
      rw [hm]; linear_combination (4 * c ^ 2) * hp + (2 * a * c - b ^ 2 + 4 * b * c) * hq
    have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hcovQ : 2 * (c : ℚ) * (e : ℚ) ^ 2 =
        (m : ℚ) ^ 3 + 2 * (c : ℚ) * (m : ℚ) ^ 2 + 4 * (c : ℚ) ^ 2 * (m : ℚ)
          + 2 * (c : ℚ) ^ 3 := by
      exact_mod_cast hcov
    have hV : (4 * (e : ℚ) / (c : ℚ)) ^ 2 =
        (2 * (m : ℚ) / (c : ℚ)) ^ 3 + ((4 : ℤ) : ℚ) * (2 * (m : ℚ) / (c : ℚ)) ^ 2
          + ((16 : ℤ) : ℚ) * (2 * (m : ℚ) / (c : ℚ)) + ((16 : ℤ) : ℚ) := by
      push_cast
      field_simp
      linear_combination (8 : ℚ) * hcovQ
    obtain ⟨p', e', n', he', hcop', hTeq, hn'0⟩ :=
      WeierstrassCurve.RationalPointDescent.exists_int_model (A := 4) (B := 16) (C := 16) hV
    have hn' : n' ^ 2 = p' ^ 3 + 4 * p' ^ 2 * e' ^ 2 + 16 * p' * e' ^ 4 + 16 * e' ^ 6 := by
      linear_combination hn'0
    have he'Q : ((e' : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hcross : 2 * m * e' ^ 2 = p' * c := by
      have hQ : 2 * (m : ℚ) * (e' : ℚ) ^ 2 = (p' : ℚ) * (c : ℚ) := by
        field_simp at hTeq
        linarith [hTeq]
      exact_mod_cast hQ
    rcases halving_descends he hcop h hc hcov hpm he' hcop' hcross hn' with h1 | hlt
    · exact h1
    · exact trivial_ascends he hcop hc hpm hcross
        (ih (p'.natAbs + (e' ^ 2).natAbs) (lt_of_lt_of_le hlt hN) p' e' n' le_rfl he' hcop' hn')

/-- **THE level-`19` statement** (PROVEN 2026-07-31 over the single leaf
`exists_halving_witness`; a sorry leaf itself from 2026-07-28 to 2026-07-31): the
only coprime integral points of the monic model `W² = U³ + 4U² + 16U + 16` of
`19a3` are `(p, e) = (0, 1)`, i.e. `U = 0`.

DECOMPOSED 2026-07-31.  It is no longer a leaf: it is the infinite descent
`integral_leaf_aux` over `exists_halving_witness` and `halving_descends`, and
`halving_descends` is in turn PROVEN over `height_drop_or_small` and
`smallPoints` once `halving_relation` eliminates the halving coordinates `m` and
`c`.  `height_drop_or_small` — the resultant/archimedean height bound, where the
finite-generation content lives — is PROVEN over `forms_common_dvd`,
`forms_archimedean` and `MazurLevel11.reduced_fraction`; `smallPoints` — the
finite base case, `|p| ≤ 574` and `1 ≤ e ≤ 23` — is PROVEN by a bitmask
quadratic-residue sieve.  What remains open is ONLY the `2`-descent proper,
`exists_halving_witness`, which is where `ℤ[θ]` enters; the bullets below are its
route and no longer this declaration's.

This is `x0Nineteen_x_eq_zero` — every affine rational point of
`y² + y = x³ + x² + x` has `x = 0` — with the rationals removed, and through the
`3`-isogeny of `cover_identity` it carries the ENTIRE arithmetic content of
level `19`: rank `0` for one explicit curve, and nothing else.

TRUE.  Verified by exhaustive search (`|p| ≤ 4000`, `1 ≤ e ≤ 300`, coprime):
`(0, 1)` is the only solution.  PARI/GP `ellrank([0,1,1,1,0])` returns the
interval `[0, 0]`, so the rank is proven rather than bounded, and `elltors`
returns `ℤ/3` — the three points being `O`, `(0, 0)` and `(0, −1)`.

**Not vacuous, and not degenerate**: `(p, e) = (0, 1)` IS a solution
(`n² = 16`), so the conclusion cannot be strengthened to "no solutions", and the
coprimality hypothesis is load-bearing — `(p, e) = (0, k)` solves the equation
for every `k` with `n = 4k³`.

THE ROUTE, in the shape that closed the identical level-`11` leaf
`MazurLevel11.integral_leaf`, with every constant below computed and
cross-checked (PARI/GP for the field invariants, hand-verifiable identities for
the rest).  Put `θ³ + 2θ² + 4θ + 2 = 0`.  Then:

* **The norm form.**  `N(a + bθ + cθ²) = a³ − 2a²b − 4a²c + 4ab² − 2abc + 8ac²
  − 2b³ + 4b²c − 8bc² + 4c³`, so with `(a, b, c) = (p, −2e², 0)`

      N(p − 2e²θ) = p³ + 4p²e² + 16pe⁴ + 16e⁶ = n²,

  which is the descent image `β = p − 2e²θ` of the point `U = p/e²`, exactly as
  `MazurLevel11.descentImage p e = (p, −2e², 0)` is `p − 2e²s` there.

* **The ring.**  `ℤ[θ]` is the FULL ring of integers of the cubic field of
  discriminant `−76` (index `1`: `−76/f²` would have to be `−19` for `f = 2`,
  and `−19` is not a cubic field discriminant, the smallest complex one being
  `−23`).  Class number `1`; fundamental unit `ε = θ + 1`, of norm `1`.
  Reduction: `θ³ = −2θ² − 4θ − 2` and `θ⁴ = 6θ + 4`, so squaring in the basis
  `1, θ, θ²` is

      (a + bθ + cθ²)² = (a² − 4bc + 4c²) + (2ab − 8bc + 6c²)θ + (2ac + b² − 4bc)θ².

* **The halving witness.**  `β = δ²` therefore reads, in coordinates,

      b² + 2ac − 4bc = 0,   p = a² − 4bc + 4c²,   e² = −ab + 4bc − 3c²,

  which is the level-`19` form of `MazurLevel11.exists_halving_witness`
  (`b² + 2ac + 4bc + 4c² = 0`, `p = a² − 4c² − 4bc`, `e² = c² − ab`).

* **It is CONSISTENT at the known solution**, which is the cheapest available
  check on the whole derivation.  `2 = −θ³/(θ + 1)²` (equivalently
  `θ³ = −2(θ + 1)²`, an identity in `ℤ[θ]`), and `(θ + 1)⁻¹ = θ² + θ + 3`, so
  `−2θ = (θ²(θ + 1)⁻¹)² = (θ² + 2θ + 2)²`.  That is `(a, b, c) = (2, 2, 1)`, and
  the three equations above give `p = 4 − 8 + 4 = 0`, `e² = −4 + 8 − 3 = 1`,
  `4 + 4 − 8 = 0` — the solution `(p, e) = (0, 1)`.

* **What is left** — and it is now exactly the statement of
  `exists_halving_witness`, not of this declaration.  The unit ambiguity is only `{1, ε}` modulo squares, since
  `N(−1) = −1 < 0` cannot divide the square `n²`; so the `ε`-class must be
  excluded (`MazurLevel11.epsilon_class_impossible`, there by a character
  `mod 13`), together with the valuation bookkeeping at the ramified primes —
  `(2) = (θ)³`, and `19 = 𝔮₁𝔮₂²` with both residue degrees `1`.  After that the
  witness feeds an archimedean height drop plus a finite sieve, exactly as at
  level `11`.

**These bullets are a derivation, not a theorem.**  Only the identities are
mechanical (`ring` will check the squaring rule, the norm form and the
`(2, 2, 1)` witness); that `β` is a square times a unit at all is the descent
itself, and it is what this leaf asks for.

**THE NAME IS NOT A PLACEHOLDER — AUDITED 2026-07-30, DO NOT RE-LITIGATE IT.**  A
dispatch of that date flagged `integral_leaf` as "a name that generic in a file this
small usually means a placeholder that was never restated", and asked whether the
statement is the one the consumers need.  It is, and there is nothing to rename:

* the name is deliberate and SHARED with the level-`11` analogue
  `MazurLevel11.integral_leaf` in `MordellWeil.lean` (identical shape,
  `n² = p³ − 4p²e² + 16e⁶` there against `n² = p³ + 4p²e² + 16pe⁴ + 16e⁶` here), and
  that one is fully PROVEN, so the naming is a convention with a working precedent
  rather than a stub;
* every consumer in this file is proven OVER this exact statement — `U_eq_zero` feeds
  it `WeierstrassCurve.RationalPointDescent.exists_int_model`'s output verbatim
  (`he : 0 < e`, `hcop : IsCoprime p e`, and the equation by `linear_combination`), so
  the three hypotheses and the conclusion `p = 0 ∧ e = 1` are exactly what is
  consumed, with no slack;
* it is TRUE as stated, not merely plausible: the exhaustive search recorded above
  (`|p| ≤ 4000`, `1 ≤ e ≤ 300`, coprime) finds `(0, 1)` and nothing else, and the
  `(a, b, c) = (2, 2, 1)` consistency check reproduces it from the descent equations;
* and it is neither vacuous nor over-strong — `(0, 1)` IS a solution, and dropping
  `hcop` admits `(0, k)` for every `k`.

So the work here is the DESCENT, following `MazurLevel11.integral_leaf`'s chain, and a
successor should not spend a cycle re-auditing the name. -/
theorem integral_leaf {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    p = 0 ∧ e = 1 :=
  integral_leaf_aux (p.natAbs + (e ^ 2).natAbs) p e n le_rfl he hcop h

/-- **The only rational `U` on `W² = U³ + 4U² + 16U + 16` is `U = 0`** (PROVEN
2026-07-28 from `integral_leaf`).

`U = 4X` and `W = 8Y + 4` is the monic integral model of `19a3`, and
`WeierstrassCurve.RationalPointDescent.exists_int_model` — the shared plumbing of
`MordellWeil.lean` — turns a rational point of a monic integral cubic into a
coprime integral one. -/
theorem U_eq_zero {U W : ℚ} (h : W ^ 2 = U ^ 3 + 4 * U ^ 2 + 16 * U + 16) : U = 0 := by
  obtain ⟨p, e, n, he, hcop, hUeq, hn⟩ :=
    WeierstrassCurve.RationalPointDescent.exists_int_model
      (A := 4) (B := 16) (C := 16) (T := U) (V := W)
      (by push_cast; linear_combination h)
  obtain ⟨hp, he1⟩ := integral_leaf (n := n) he hcop (by linear_combination hn)
  rw [hUeq, hp, he1]; norm_num

/-- **Every affine rational point of `19a3 : y² + y = x³ + x² + x` has `x = 0`**
(PROVEN 2026-07-28 from `U_eq_zero`).

The two such points are `(0, 0)` and `(0, −1)`; with the point at infinity they
are the three elements of `19a3(ℚ) ≅ ℤ/3`.  Only the `x`-coordinate is asserted,
because only the `x`-coordinate is consumed: `rational_point_x0Nineteen` feeds
this the image of a point of `19a1` under the `3`-isogeny and reads off that the
isogeny's numerator vanishes. -/
theorem x0Nineteen_x_eq_zero {X Y : ℚ} (h : Y ^ 2 + Y = X ^ 3 + X ^ 2 + X) : X = 0 := by
  have hWU : (8 * Y + 4) ^ 2 = (4 * X) ^ 3 + 4 * (4 * X) ^ 2 + 16 * (4 * X) + 16 := by
    linear_combination (64 : ℚ) * h
  have h4 : 4 * X = 0 := U_eq_zero hWU
  linarith

/-- **The `3`-isogeny `19a1 → 19a3`, as a polynomial identity** (PROVEN
2026-07-28 by `linear_combination`).

With `N = x³ − 18x − 35`, `M = (y − 13)(x³ + 4x²) + (18y − 63)x + 46y − 9` and
`D = 3x + 4`, the homogeneous form of `Y² + Y = X³ + X² + X` at
`(X, Y) = (N/D², M/D³)` is

    M² + MD³ − (N³ + N²D² + ND⁴) = (x³ + 4x² + 18x + 46)² · (y² + y − (x³ + x² − 9x − 15)),

so it vanishes exactly on `19a1`.  The cofactor is the square of the coefficient
of `y` in `M`, which is why the identity is a single `linear_combination`: `M` is
affine-linear in `y` and the `19a1` relation is used once, on `y²`.

The kernel of this isogeny is the rational subgroup with `x`-coordinate `−4/3`,
the factor `3x + 4` of `elldivpol(19a1, 3)`; it is NOT the subgroup generated by
the rational `3`-torsion point `(5, 9)`, whose quotient is `[0,1,1,−769,−8470]`
instead. -/
theorem cover_identity (x y : ℚ) (h : y ^ 2 + y = x ^ 3 + x ^ 2 - 9 * x - 15) :
    ((y - 13) * (x ^ 3 + 4 * x ^ 2) + (18 * y - 63) * x + 46 * y - 9) ^ 2
      + ((y - 13) * (x ^ 3 + 4 * x ^ 2) + (18 * y - 63) * x + 46 * y - 9) * (3 * x + 4) ^ 3
      = (x ^ 3 - 18 * x - 35) ^ 3 + (x ^ 3 - 18 * x - 35) ^ 2 * (3 * x + 4) ^ 2
        + (x ^ 3 - 18 * x - 35) * (3 * x + 4) ^ 4 := by
  linear_combination ((x ^ 3 + 4 * x ^ 2 + 18 * x + 46) ^ 2) * h

/-- **Dehomogenising the covering** (PROVEN 2026-07-28): away from the kernel
fibre `D = 0`, the homogeneous identity of `cover_identity` says exactly that
`(N/D², M/D³)` lies on `y² + y = x³ + x² + x`. -/
theorem cover_eq {N M D : ℚ} (hD : D ≠ 0)
    (key : M ^ 2 + M * D ^ 3 = N ^ 3 + N ^ 2 * D ^ 2 + N * D ^ 4) :
    (M / D ^ 3) ^ 2 + M / D ^ 3 = (N / D ^ 2) ^ 3 + (N / D ^ 2) ^ 2 + N / D ^ 2 := by
  field_simp
  linear_combination key

/-- **The two affine rational points of `19a1`** (PROVEN 2026-07-28 over the
single leaf `integral_leaf`): every rational solution of
`y² + y = x³ + x² − 9x − 15` has `x = 5` and `y ∈ {9, −10}`.

**This single statement carries the whole arithmetic content of level `19`**,
and it is equivalent to "rank `19a1` `= 0`": stated unconditionally, it gives
finiteness of `19a1(ℚ)` (in `MazurTorsion.lean`'s `X0GenusOne.finite_curve19a1`)
rather than needing it, which is what breaks the circle — exactly as
`curve11a3_rational_points` does at level `11`.

THE PROOF, in three steps and no group law.  (i) The fibre `3x + 4 = 0` is empty
over `ℝ`: at `x = −4/3` the equation is `(54y + 27)² = −9747`.  (ii) Off that
fibre the `3`-isogeny of `cover_identity` puts `((x³ − 18x − 35)/(3x + 4)², …)`
on `19a3`, so `x0Nineteen_x_eq_zero` forces `x³ − 18x − 35 = 0`.  (iii) That
cubic is `(x − 5)(x² + 5x + 7)` and `x² + 5x + 7 = ((2x + 5)² + 3)/4 > 0`, so
`x = 5`; then `y² + y = 90 = 9 · 10` gives `(y − 9)(y + 10) = 0`. -/
theorem rational_point_x0Nineteen (x y : ℚ)
    (h : y ^ 2 + y = x ^ 3 + x ^ 2 - 9 * x - 15) :
    x = 5 ∧ (y = 9 ∨ y = -10) := by
  rcases eq_or_ne (3 * x + 4) 0 with hd | hd
  · exfalso
    have hx : x = -4 / 3 := by linarith
    rw [hx] at h
    nlinarith [sq_nonneg (2 * y + 1)]
  · have hX0 : (x ^ 3 - 18 * x - 35) / (3 * x + 4) ^ 2 = 0 :=
      x0Nineteen_x_eq_zero (cover_eq hd (cover_identity x y h))
    have hnum : x ^ 3 - 18 * x - 35 = 0 := by
      rcases div_eq_zero_iff.mp hX0 with h1 | h1
      · exact h1
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1) hd
    have hx5 : x = 5 := by
      have hfac : (x - 5) * (x ^ 2 + 5 * x + 7) = 0 := by linear_combination hnum
      rcases mul_eq_zero.mp hfac with h1 | h1
      · linarith
      · nlinarith [sq_nonneg (2 * x + 5)]
    refine ⟨hx5, ?_⟩
    rw [hx5] at h
    have hfy : (y - 9) * (y + 10) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfy with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

end MazurX0Nineteen
