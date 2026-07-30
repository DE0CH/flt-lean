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

## THE ONE LEAF

`MazurX0Nineteen.integral_leaf` — the pure integer statement

    n² = p³ + 4p²e² + 16pe⁴ + 16e⁶,  gcd(p, e) = 1,  e > 0   ⟹   (p, e) = (0, 1).

Everything else in this file is PROVEN over it:
`U_eq_zero` (`RationalPointDescent.exists_int_model`, the shared plumbing from
`MordellWeil.lean`), `x0Nineteen_x_eq_zero`, `cover_identity`, `cover_eq`,
`rational_point_x0Nineteen`.

**The template for closing it is `MazurLevel11.integral_leaf`**, which was itself
a leaf until 2026-07-27 and is now fully proven; its chain is
`exists_halving_witness` (the `2`-descent proper: `descent_zs`,
`descent_unit_square`, `descent_square_class`, `epsilon_class_impossible`, over
`Cubic.ZS.isPrincipalIdealRing_zs` and `Cubic.ZS.unit_sq_class`), then
`halving_relation` → `height_drop_or_small` (`reduced_fraction`,
`forms_common_dvd`, `forms_archimedean`) → `smallPoints` (a bitmask
quadratic-residue sieve) → `halving_descends`/`trivial_ascends` →
`integral_leaf_aux` by strong induction on `|p| + e²`.  A successor should
follow that file rather than looking for a general Mordell–Weil theorem, which
exists nowhere in this tree, in `Mathlib`, or in `~/cs/FLT`.

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

/-- **THE level-`19` statement** (sorry leaf, introduced 2026-07-28): the only
coprime integral points of the monic model `W² = U³ + 4U² + 16U + 16` of `19a3`
are `(p, e) = (0, 1)`, i.e. `U = 0`.

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

  **WARNING (2026-07-30): THIS IS THE ONE PLACE WHERE LEVEL 11 DOES *NOT*
  TRANSCRIBE, and it is not a matter of changing constants.**
  `MazurLevel11.Cubic.ZS.isPrincipalIdealRing_zs` gets `h = 1` from
  `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, i.e. from Minkowski's
  DISCRIMINANT bound: with `n = 3` and `r₂ = 1` that bound is
  `(2·(π/4)·(3³/3!))² = (2.25π)² ≈ 49.96`, and level 11 squeaks in with
  `|disc| = 44 < 49.96`.  **At level 19 `|disc| = 76 > 49.96`, so that lemma does
  not apply at all** — the same proof text will simply fail to elaborate, and no
  choice of model helps, because the cubic field is the `2`-division field of the
  curve and is therefore the same (`disc −76 = −4·19`) for every member of the
  isogeny class `19a1, 19a2, 19a3`.

  What is true is the sharper Minkowski bound on ideal NORMS,
  `(4/π)^{r₂}·(n!/n^n)·√|d| = (4/π)·(6/27)·√76 ≈ 2.47`, so the class group is
  generated by the primes of norm `≤ 2`; the only one is `(θ)`, of norm
  `|N(θ)| = |−2| = 2` (`θ³ + 2θ² + 4θ + 2` monic gives `N(θ) = −2`), and it is
  principal by construction — whence `h = 1`, and indeed `(2) = (θ)³`.  But that
  argument needs the ideal-norm side of `Mathlib/NumberTheory/ClassNumber/*`,
  which nothing in this tree currently drives.  **Budget for it separately: it is
  a real prerequisite, not plumbing, and it is the reason a straight transcription
  of `MazurLevel11` stalls.**  (Everything else in the level-11 chain — the norm
  form, the halving witness, the `ε`-class obstruction, the archimedean drop, the
  sieve — really does transcribe with new constants.)
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

* **What is left.**  The unit ambiguity is only `{1, ε}` modulo squares, since
  `N(−1) = −1 < 0` cannot divide the square `n²`; so the `ε`-class must be
  excluded (`MazurLevel11.epsilon_class_impossible`, there by a character
  `mod 13`), together with the valuation bookkeeping at the ramified primes —
  `(2) = (θ)³`, and `19 = 𝔮₁𝔮₂²` with both residue degrees `1`.  After that the
  witness feeds an archimedean height drop plus a finite sieve, exactly as at
  level `11`.

**These bullets are a derivation, not a theorem.**  Only the identities are
mechanical (`ring` will check the squaring rule, the norm form and the
`(2, 2, 1)` witness); that `β` is a square times a unit at all is the descent
itself, and it is what this leaf asks for. -/
theorem integral_leaf {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    p = 0 ∧ e = 1 := sorry

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
