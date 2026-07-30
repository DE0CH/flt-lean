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

## THE ONE LEAF (moved 2026-07-30 from `19a3` to `19a1` — read this before working)

The leaf is now `MazurX0Nineteen.hesse_leaf`, the **Hesse cubic**

    X³ + Y³ + Z³ = 2XYZ,   gcd(X, Y) = 1   ⟹   X + Y + Z = 0,

and `integral_leaf` — the pure integer statement

    n² = p³ + 4p²e² + 16pe⁴ + 16e⁶,  gcd(p, e) = 1,  e > 0   ⟹   (p, e) = (0, 1)

— is PROVEN over it by an explicit hand-written `3`-isogeny descent
(`four_dvd_of_even`, `exists_reduced_even`, `descent_odd`, `descent_even`,
`hesse_kill`).  Everything else in this file is PROVEN over `integral_leaf`, as
before: `U_eq_zero`, `x0Nineteen_x_eq_zero`, `cover_identity`, `cover_eq`,
`rational_point_x0Nineteen`.

**What the descent is, and which curve the leaf now lives on.**  `X³+Y³+Z³=2XYZ`
IS `19a1`: `ellfromeqn(x³+y³+1−2xy)` has minimal model `[0,1,1,−9,−15]`,
`Δ = −6859 = −19³`, conductor `19`, `ellrank = [0,0]`, `elltors = ℤ/3`, and its
only primitive integer triples are the six `(±1,∓1,0)`, `(±1,0,∓1)`,
`(0,±1,∓1)` — all with `X+Y+Z = 0`, which is why the leaf is TRUE.  So
`descent_odd`/`descent_even` invert the `3`-isogeny `19a1 → 19a3` of
`cover_identity`: they take a rational point of `19a3` and produce its preimage
on `19a1`, one third of the canonical height.

**THE ELEMENTARY DESCENT CANNOT BE ITERATED — this is the reason the leaf stops
here, and it was checked rather than guessed (2026-07-30).**  The next step is
available and completely explicit.  Writing `19a1` with its rational `3`-torsion
at the origin, `y² + 8xy + 19y = x³` (from `[0,1,1,−9,−15]` by `x ↦ x+5`,
`y ↦ y+4x+9`), the three inflectional tangents of the Hesse model satisfy, as a
polynomial identity checkable by `linear_combination` (verified symbolically):

    (3u−3v+2f)(2u−3v+3f)(3u−2v+3f) = 19(u−v+f)³ + (v³−u³−f³−2uvf),
    (3u−3v+2f)+(2u−3v+3f)+(3u−2v+3f) = 8(u−v+f),

so on the curve the three factors have product `19·M³` with `M = u−v+f`.  They
are pairwise coprime for a primitive triple, and the argument is worth recording
because it is the only fiddly step: the same linear system inverts to

    8u = 3A − 5B + 3C,   8v = −3A − 3B + 5C,   8f = −5A + 3B + 3C

(writing `A, B, C` for the three tangent forms), so a prime dividing two of them
divides `8u`, `8v`, `8f` and `8M ≡ A+B+C`; away from `2` and `19` that forces it
to divide `u`, `v` and `f` at once.  At `2` exactly one of the three is even, and
at `19` the same inversion applies since `19 ∤ u, v, f`.  Extracting cubes then
gives `a³ + b³ + 19c³ = 8abc`.  **That curve is `19a2`**
(`ellfromeqn(x³+y³+19−8xy)` has minimal model `[0,1,1,−769,−8470]`, conductor
`19`, rank `0`), and `19a2` has **trivial torsion** — no rational `3`-torsion
point, hence no "`y` is a cube" descent.  The isogeny class is exactly
`19a2 — 19a1 — 19a3` with matrix `[[1,3,3],[3,1,9],[3,9,1]]`, so the elementary
chain runs `19a3 → 19a1 → 19a2` and terminates.  Closing the loop would need
`19a1(ℚ)/ψ(19a3(ℚ))`, whose descent group is `H¹(G, ℤ/3) = Hom(G, ℤ/3)` — cyclic
cubic fields, not `ℚ*/(ℚ*)³`.  **Do not spend another cycle looking for an
elementary `3`-descent that closes; there is none.**

**So the remaining work is still the `2`-descent, and the TRADE-OFF the move
costs must be stated.**  The template is `MazurLevel11.integral_leaf`, itself a
leaf until 2026-07-27 and now fully proven; its chain is
`exists_halving_witness` (the `2`-descent proper: `descent_zs`,
`descent_unit_square`, `descent_square_class`, `epsilon_class_impossible`, over
`Cubic.ZS.isPrincipalIdealRing_zs` and `Cubic.ZS.unit_sq_class`), then
`halving_relation` → `height_drop_or_small` (`reduced_fraction`,
`forms_common_dvd`, `forms_archimedean`) → `smallPoints` (a bitmask
quadratic-residue sieve) → `halving_descends`/`trivial_ascends` →
`integral_leaf_aux` by strong induction on `|p| + e²`.  A successor should follow
that file rather than looking for a general Mordell–Weil theorem, which exists
nowhere in this tree, in `Mathlib`, or in `~/cs/FLT`.

That `2`-descent is CHEAPER ON `19a3` than on `19a1`: both run in the same cubic
field `ℚ(θ)`, `θ³ + 2θ² + 4θ + 2 = 0`, of discriminant `−76`, but `19a3`'s monic
cubic `U³ + 4U² + 16U + 16` generates the FULL ring of integers (index `1`) while
`19a1`'s `U³ + 4U² − 144U − 944` generates an order of index `152 = 8·19`.  So a
successor has two honest options:

* prove `hesse_leaf` directly, paying the index-`152` bookkeeping (extra bad
  primes `2` and `19` in the square-class analysis, nothing worse in kind); or
* prove the `19a3` statement first as a SEPARATE theorem by the index-`1`
  descent, then bridge it to `hesse_leaf` through `cover_identity` plus the
  linear Hesse ↔ Weierstrass change of coordinates recorded above — this is NOT
  circular, because `integral_leaf` is proven from `hesse_leaf` and not
  conversely, but it does duplicate the `19a3` statement, so if that is the route
  chosen it is cleaner to REVERT this file's routing and restore `integral_leaf`
  as the leaf.  Either way the descent lemmas below are unaffected.

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

/-! ### The `3`-isogeny descent `19a3 → 19a1`, by hand

Everything in this section is elementary: no number field, no class group, no
ideal theory.  The only nontrivial input is `exists_associated_pow_of_mul_eq_pow'`
(coprime factors of a cube are cubes up to units) together with the fact that
every unit of `ℤ` is a cube.  It reduces `integral_leaf` to the single leaf
`hesse_leaf`; see the module docstring for what that costs and why the chain
cannot be iterated. -/

/-- Coprimality is unchanged by adding a multiple of the left argument to the
right one. -/
theorem cop_add_mul {x y z : ℤ} (h : IsCoprime x y) : IsCoprime x (y + x * z) := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a - b * z, b, by linear_combination hab⟩

/-- A coprime factor of a cube is a cube.  Over `ℤ` the unit ambiguity is
harmless: `1` and `−1` are both cubes. -/
theorem cube_of_coprime_mul_eq_cube {a b c : ℤ} (hab : IsCoprime a b) (h : a * b = c ^ 3) :
    ∃ d : ℤ, a = d ^ 3 := by
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  rcases Int.isUnit_eq_one_or u.isUnit with h1 | h1
  · exact ⟨d, by rw [← hu, h1, mul_one]⟩
  · exact ⟨-d, by rw [← hu, h1]; ring⟩

/-- If `a² = 2b` then `a` is even, delivered in the `2 * c` shape (`Even` unfolds
to `c + c`, which `linarith` cannot use directly). -/
theorem two_mul_of_sq_eq_two_mul {a b : ℤ} (h : a ^ 2 = 2 * b) : ∃ c : ℤ, a = 2 * c := by
  obtain ⟨t, ht⟩ := (Int.even_pow.mp (⟨b, by linarith⟩ : Even (a ^ 2))).1
  exact ⟨t, by linarith⟩

/-- Cubing is injective on `ℤ`; proved by factoring `a³ − b³` rather than by a
monotonicity argument, so that it works uniformly in sign. -/
theorem cube_left_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b := by
  have hf : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hf with h1 | h1
  · linarith
  · have hb2 : b ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (2 * a + b)]) (sq_nonneg b)
    have hb : b = 0 := by simpa using sq_eq_zero_iff.mp hb2
    have ha2 : a ^ 2 = 0 := by rw [hb] at h1; linarith
    have ha : a = 0 := by simpa using sq_eq_zero_iff.mp ha2
    rw [ha, hb]

/-- **THE level-`19` LEAF** (moved here 2026-07-30 from `integral_leaf`, which is
now proven over it): the Hesse cubic

    X³ + Y³ + Z³ = 2XYZ,   gcd(X, Y) = 1   ⟹   X + Y + Z = 0.

**This IS "`19a1` has rank `0`"**, in the cleanest available form.
`ellfromeqn(x³ + y³ + 1 − 2xy)` has minimal model `[0,1,1,−9,−15]`, i.e. `19a1`,
with `Δ = −6859 = −19³` and conductor `19`; the cubic is smooth (the Hesse
pencil `x³+y³+z³−3μxyz` is singular only at `μ³ = 1`, and here `μ = 2/3`), so it
is a genus-`1` curve and the statement is exactly a Mordell–Weil assertion.

TRUE, and the evidence is an ENUMERATION rather than a bound.  PARI/GP
(untrusted searcher) gives `ellrank([0,1,1,−9,−15]) = [0,0]` — rank `0` proven,
not merely bounded — and `elltors = ℤ/3`, so `19a1(ℚ)` has exactly three points;
a plane cubic's projective rational points are in bijection with them, and each
contributes exactly two primitive integer triples `±(X,Y,Z)`.  A direct search
over `|X|, |Y|, |Z| ≤ 60` finds exactly those six:

    (1,−1,0), (−1,1,0), (1,0,−1), (−1,0,1), (0,1,−1), (0,−1,1),

every one of which satisfies `X + Y + Z = 0`.  Note `gcd(X, Y) = 1` already
forces `gcd(X, Y, Z) = 1` (a prime dividing `X` and `Z` divides `Y³`), so the
hypothesis really does cut out primitive triples and the list is complete.

**FALSITY AUDIT (2026-07-30, first audit of this statement — it has not been
restated before, so nothing is inherited).**

* *Not vacuous*: all six triples above satisfy the hypotheses.
* *The coprimality hypothesis is NOT needed for truth — it is kept deliberately,
  and this is worth stating because the reflex is to assume otherwise.*  The
  equation is homogeneous, so every integer solution is a scalar multiple of a
  primitive one (or is `(0,0,0)`), and `X + Y + Z = 0` survives scaling; hence
  the hypothesis-free statement is true as well.  `IsCoprime X Y` is kept
  because a WEAKER leaf is a cheaper leaf, and because the sole consumer
  supplies it for free.  A successor may drop it at the cost of one
  `gcd`-extraction step, but there is no reason to.
* *The conclusion is not a hidden triviality, and this is the subtle point.*
  `X + Y + Z = 0` is NOT a component of the curve: substituting `Z = −(X+Y)`
  gives `X³ + Y³ − (X+Y)³ = −3XY(X+Y)` against `2XYZ = −2XY(X+Y)`, so the line
  meets the cubic only where `XY(X+Y) = 0`.  Hence conclusion-plus-equation is
  equivalent to `XYZ = 0`, and the leaf really does assert that the curve has no
  rational point off the three inflections.  A successor tempted to "simplify"
  the conclusion to `XYZ = 0` may do so — the two are interchangeable here — but
  must not weaken it to something the line `X+Y+Z = 0` satisfies identically.
* *Consumed with no slack*: the sole consumer is `hesse_kill`, which feeds it
  `IsCoprime (−u) v` and the equation in the form
  `(−u)³ + v³ + (−w)³ = 2(−u)v(−w)`.

THE ROUTE.  What remains is a `2`-descent, and the template is
`MazurLevel11.integral_leaf` in `MordellWeil.lean` (fully proven 2026-07-27).
Both `19a1` and `19a3` descend in the SAME cubic field `ℚ(θ)`,
`θ³ + 2θ² + 4θ + 2 = 0`, of discriminant `−76`; the difference is the order.  For
`19a3`'s monic model `W² = U³ + 4U² + 16U + 16` the ring `ℤ[θ]` is the FULL ring
of integers (index `1`: `−76/f²` would have to be `−19` for `f = 2`, and `−19` is
not a cubic field discriminant, the smallest complex one being `−23`), class
number `1`, fundamental unit `ε = θ + 1` of norm `1`.  For `19a1`'s
`U³ + 4U² − 144U − 944` the generated order has index `152 = 8·19`.

The `19a3` computation, kept here because option 2 of the module docstring uses
it, and because every constant in it was cross-checked:

* **The norm form.**  `N(a + bθ + cθ²) = a³ − 2a²b − 4a²c + 4ab² − 2abc + 8ac²
  − 2b³ + 4b²c − 8bc² + 4c³`, so with `(a, b, c) = (p, −2e², 0)`

      N(p − 2e²θ) = p³ + 4p²e² + 16pe⁴ + 16e⁶ = n²,

  the descent image `β = p − 2e²θ` of the point `U = p/e²`, exactly as
  `MazurLevel11.descentImage p e = (p, −2e², 0)` is `p − 2e²s` there.
* **Squaring.**  `θ³ = −2θ² − 4θ − 2` and `θ⁴ = 6θ + 4`, so

      (a + bθ + cθ²)² = (a² − 4bc + 4c²) + (2ab − 8bc + 6c²)θ + (2ac + b² − 4bc)θ².

* **The halving witness.**  `β = δ²` reads `b² + 2ac − 4bc = 0`,
  `p = a² − 4bc + 4c²`, `e² = −ab + 4bc − 3c²`, the level-`19` form of
  `MazurLevel11.exists_halving_witness`.
* **Consistent at the known solution**, the cheapest check on the derivation:
  `θ³ = −2(θ + 1)²` and `(θ + 1)⁻¹ = θ² + θ + 3` give
  `−2θ = (θ² + 2θ + 2)²`, i.e. `(a, b, c) = (2, 2, 1)`, whence
  `p = 4 − 8 + 4 = 0`, `e² = −4 + 8 − 3 = 1` and `4 + 4 − 8 = 0` — the solution
  `(p, e) = (0, 1)`.
* **What is left.**  The unit ambiguity is only `{1, ε}` modulo squares, since
  `N(−1) = −1 < 0` cannot divide the square `n²`; the `ε`-class must be excluded
  (`MazurLevel11.epsilon_class_impossible`, there by a character `mod 13`),
  together with the valuation bookkeeping at the ramified primes — `(2) = (θ)³`,
  and `19 = 𝔮₁𝔮₂²` with both residue degrees `1`.  Then an archimedean height
  drop plus a finite sieve, exactly as at level `11`.

**These bullets are a derivation, not a theorem**: only the identities are
mechanical (`ring` checks the squaring rule, the norm form and the `(2, 2, 1)`
witness).  That `β` is a square times a unit at all IS the descent. -/
theorem hesse_leaf {X Y Z : ℤ} (hcop : IsCoprime X Y)
    (h : X ^ 3 + Y ^ 3 + Z ^ 3 = 2 * X * Y * Z) : X + Y + Z = 0 := sorry

/-- **Step 1 of the descent: `p ≡ 2 mod 4` is impossible** (PROVEN 2026-07-30).

If `p` is even then `4 ∣ p`.  Writing `p = 2m` with `m` odd makes the right-hand
side `8·(odd)`, so `n = 4n₂` would force `2 ∣ 2K + 1`. -/
theorem four_dvd_of_even {p e n m : ℤ} (hm : p = 2 * m)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    ∃ p₂ : ℤ, p = 4 * p₂ := by
  rcases Int.even_or_odd m with hme | hmo
  · obtain ⟨t, ht⟩ := hme
    exact ⟨t, by rw [hm, ht]; ring⟩
  · exfalso
    obtain ⟨j, hj⟩ := hmo
    subst hj
    subst hm
    obtain ⟨K, hK⟩ : ∃ K : ℤ, K = 4 * j ^ 3 + 6 * j ^ 2 + 3 * j + (2 * j + 1) ^ 2 * e ^ 2
        + 2 * (2 * j + 1) * e ^ 4 + e ^ 6 := ⟨_, rfl⟩
    have hn8 : n ^ 2 = 8 * (2 * K + 1) := by rw [hK]; linear_combination h
    obtain ⟨n₁, hn₁⟩ := two_mul_of_sq_eq_two_mul (a := n) (b := 4 * (2 * K + 1)) (by linarith)
    subst hn₁
    have h1 : n₁ ^ 2 = 2 * (2 * K + 1) := by
      have h4 : 4 * n₁ ^ 2 = 4 * (2 * (2 * K + 1)) := by linear_combination hn8
      linarith
    obtain ⟨n₂, hn₂⟩ := two_mul_of_sq_eq_two_mul (a := n₁) (b := 2 * K + 1) h1
    subst hn₂
    have h2 : (2 : ℤ) ∣ 2 * K + 1 := by
      refine ⟨n₂ ^ 2, ?_⟩
      have h4 : 2 * (2 * K + 1) = 2 * (2 * n₂ ^ 2) := by linear_combination -h1
      linarith
    omega

/-- **Step 2: dividing the `4` out** (PROVEN 2026-07-30).  With `p = 4p₂` the
equation becomes `16 ∣ n²`, and the reduced equation
`n₂² = 4p₂³ + 4p₂²e² + 4p₂e⁴ + e⁶` is the one `descent_even` factors. -/
theorem exists_reduced_even {p₂ e n : ℤ}
    (h : n ^ 2 = (4 * p₂) ^ 3 + 4 * (4 * p₂) ^ 2 * e ^ 2 + 16 * (4 * p₂) * e ^ 4 + 16 * e ^ 6) :
    ∃ n₂ : ℤ, n = 4 * n₂ ∧
      n₂ ^ 2 = 4 * p₂ ^ 3 + 4 * p₂ ^ 2 * e ^ 2 + 4 * p₂ * e ^ 4 + e ^ 6 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = 4 * p₂ ^ 3 + 4 * p₂ ^ 2 * e ^ 2 + 4 * p₂ * e ^ 4 + e ^ 6 :=
    ⟨_, rfl⟩
  have hn16 : n ^ 2 = 16 * J := by rw [hJ]; linear_combination h
  obtain ⟨n₁, hn₁⟩ := two_mul_of_sq_eq_two_mul (a := n) (b := 8 * J) (by linarith)
  subst hn₁
  have h1 : n₁ ^ 2 = 4 * J := by
    have h4 : 4 * n₁ ^ 2 = 4 * (4 * J) := by linear_combination hn16
    linarith
  obtain ⟨n₂, hn₂⟩ := two_mul_of_sq_eq_two_mul (a := n₁) (b := 2 * J) (by linarith)
  subst hn₂
  refine ⟨n₂, by ring, ?_⟩
  have h4 : 4 * n₂ ^ 2 = 4 * J := by linear_combination h1
  rw [hJ] at h4; linarith

/-- **Step 3: the descent proper, `p` odd** (PROVEN 2026-07-30).

The point of the whole construction is the identity

    (n − 2pe − 4e³)(n + 2pe + 4e³) = n² − (2pe + 4e³)² = p³,

so the equation exhibits `p³` as a product of two factors whose gcd divides
`4e(p + 2e²)` — coprime to `p³` when `p` is odd and `gcd(p, e) = 1`.  Coprime
factors of a cube are cubes, `p = uv`, and subtracting the two cubes gives the
Hesse equation with `Z = 2e`. -/
theorem descent_odd {p e n : ℤ} (hcop : IsCoprime p e) (hpo : Odd p)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    ∃ u v : ℤ, IsCoprime u v ∧ p = u * v ∧
      v ^ 3 - u ^ 3 - (2 * e) ^ 3 = 2 * u * v * (2 * e) := by
  obtain ⟨k, hk⟩ := hpo
  have hp2 : IsCoprime p (2 : ℤ) := ⟨1, -k, by linear_combination hk⟩
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = n - 2 * p * e - 4 * e ^ 3 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = n + 2 * p * e + 4 * e ^ 3 := ⟨_, rfl⟩
  have hST : S * T = p ^ 3 := by rw [hS, hT]; linear_combination h
  have hSd : S ∣ p ^ 3 := ⟨T, hST.symm⟩
  have hSe : IsCoprime S e :=
    (hcop.pow_left : IsCoprime (p ^ 3) e).of_isCoprime_of_dvd_left hSd
  have hp4 : IsCoprime p (4 : ℤ) := by
    have h1 : IsCoprime p ((2 : ℤ) ^ 2) := hp2.pow_right
    rwa [show ((2 : ℤ) ^ 2) = 4 by norm_num] at h1
  have hS4 : IsCoprime S (4 : ℤ) :=
    (hp4.pow_left : IsCoprime (p ^ 3) 4).of_isCoprime_of_dvd_left hSd
  have hq : IsCoprime p (p + 2 * e ^ 2) := by
    have h1 : IsCoprime p (2 * e ^ 2) := hp2.mul_right hcop.pow_right
    have h2 := cop_add_mul (z := 1) h1
    rwa [show 2 * e ^ 2 + p * 1 = p + 2 * e ^ 2 by ring] at h2
  have hSq : IsCoprime S (p + 2 * e ^ 2) :=
    (hq.pow_left : IsCoprime (p ^ 3) (p + 2 * e ^ 2)).of_isCoprime_of_dvd_left hSd
  have hSTcop : IsCoprime S T := by
    have h1 : IsCoprime S (4 * e * (p + 2 * e ^ 2)) := (hS4.mul_right hSe).mul_right hSq
    have h2 := cop_add_mul (z := 1) h1
    rwa [show 4 * e * (p + 2 * e ^ 2) + S * 1 = T by rw [hS, hT]; ring] at h2
  obtain ⟨u, hu⟩ : ∃ u : ℤ, S = u ^ 3 := cube_of_coprime_mul_eq_cube hSTcop hST
  obtain ⟨v, hv⟩ : ∃ v : ℤ, T = v ^ 3 :=
    cube_of_coprime_mul_eq_cube hSTcop.symm (show T * S = p ^ 3 by linear_combination hST)
  have hud : u ∣ S := ⟨u ^ 2, by rw [hu]; ring⟩
  have hvd : v ∣ T := ⟨v ^ 2, by rw [hv]; ring⟩
  have huv : IsCoprime u v :=
    (hSTcop.of_isCoprime_of_dvd_left hud).of_isCoprime_of_dvd_right hvd
  have hpuv : p = u * v := by
    have h1 : (u * v) ^ 3 = p ^ 3 := by rw [mul_pow, ← hu, ← hv]; exact hST
    exact (cube_left_inj h1).symm
  rw [hS] at hu
  rw [hT] at hv
  exact ⟨u, v, huv, hpuv, by linear_combination hu - hv + 4 * e * hpuv⟩

/-- **Step 4: the descent proper, `4 ∣ p`** (PROVEN 2026-07-30).

Same shape as `descent_odd` on the reduced equation of `exists_reduced_even`:
`(n₂ − 2p₂e − e³)(n₂ + 2p₂e + e³) = 4p₂³`, both factors are even, and halving
them gives `στ = p₂³` with `σ, τ` coprime.  The Hesse equation comes out with
`Z = e` rather than `2e`. -/
theorem descent_even {p₂ e n₂ : ℤ} (hcop : IsCoprime p₂ e)
    (h : n₂ ^ 2 = 4 * p₂ ^ 3 + 4 * p₂ ^ 2 * e ^ 2 + 4 * p₂ * e ^ 4 + e ^ 6) :
    ∃ u v : ℤ, IsCoprime u v ∧ p₂ = u * v ∧ v ^ 3 - u ^ 3 - e ^ 3 = 2 * u * v * e := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = n₂ - 2 * p₂ * e - e ^ 3 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = n₂ + 2 * p₂ * e + e ^ 3 := ⟨_, rfl⟩
  have hAB : A * B = 4 * p₂ ^ 3 := by rw [hA, hB]; linear_combination h
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, A = 2 * σ := by
    have hev : Even (A * B) := ⟨2 * p₂ ^ 3, by linarith⟩
    rcases Int.even_mul.mp hev with hd | hd
    · obtain ⟨c, hc⟩ := hd; exact ⟨c, by linarith⟩
    · obtain ⟨c, hc⟩ := hd
      exact ⟨c - 2 * p₂ * e - e ^ 3, by rw [hA]; rw [hB] at hc; linarith⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℤ, τ = σ + (2 * p₂ * e + e ^ 3) := ⟨_, rfl⟩
  have hB2 : B = 2 * τ := by rw [hτ, hB]; rw [hA] at hσ; linarith
  have hστ : σ * τ = p₂ ^ 3 := by
    have h4 : 4 * (σ * τ) = 4 * p₂ ^ 3 := by rw [← hAB, hσ, hB2]; ring
    linarith
  have hσd : σ ∣ p₂ ^ 3 := ⟨τ, hστ.symm⟩
  have hσe : IsCoprime σ e :=
    (hcop.pow_left : IsCoprime (p₂ ^ 3) e).of_isCoprime_of_dvd_left hσd
  have hq : IsCoprime p₂ (2 * p₂ + e ^ 2) := by
    have h1 : IsCoprime p₂ (e ^ 2) := hcop.pow_right
    have h2 := cop_add_mul (z := 2) h1
    rwa [show e ^ 2 + p₂ * 2 = 2 * p₂ + e ^ 2 by ring] at h2
  have hσq : IsCoprime σ (2 * p₂ + e ^ 2) :=
    (hq.pow_left : IsCoprime (p₂ ^ 3) (2 * p₂ + e ^ 2)).of_isCoprime_of_dvd_left hσd
  have hστcop : IsCoprime σ τ := by
    have h1 : IsCoprime σ (e * (2 * p₂ + e ^ 2)) := hσe.mul_right hσq
    have h2 := cop_add_mul (z := 1) h1
    rwa [show e * (2 * p₂ + e ^ 2) + σ * 1 = τ by rw [hτ]; ring] at h2
  obtain ⟨u, hu⟩ : ∃ u : ℤ, σ = u ^ 3 := cube_of_coprime_mul_eq_cube hστcop hστ
  obtain ⟨v, hv⟩ : ∃ v : ℤ, τ = v ^ 3 :=
    cube_of_coprime_mul_eq_cube hστcop.symm (show τ * σ = p₂ ^ 3 by linear_combination hστ)
  have hud : u ∣ σ := ⟨u ^ 2, by rw [hu]; ring⟩
  have hvd : v ∣ τ := ⟨v ^ 2, by rw [hv]; ring⟩
  have huv : IsCoprime u v :=
    (hστcop.of_isCoprime_of_dvd_left hud).of_isCoprime_of_dvd_right hvd
  have hpuv : p₂ = u * v := by
    have h1 : (u * v) ^ 3 = p₂ ^ 3 := by rw [mul_pow, ← hu, ← hv]; exact hστ
    exact (cube_left_inj h1).symm
  exact ⟨u, v, huv, hpuv, by linear_combination hu - hv + hτ + 2 * e * hpuv⟩

/-- **The leaf, applied** (PROVEN 2026-07-30 over `hesse_leaf`).

`(X, Y, Z) = (−u, v, −w)` turns `v³ − u³ − w³ = 2uvw` into `X³+Y³+Z³ = 2XYZ`, so
`hesse_leaf` gives `v = u + w`.  Feeding that BACK into the equation collapses it
to `3uvw = 2uvw`, i.e. `uvw = 0`; with `w ≠ 0` this is `uv = 0`.  (That
back-substitution is the content flagged in `hesse_leaf`'s falsity audit: the
line `X+Y+Z = 0` meets the cubic only where `XYZ = 0`.) -/
theorem hesse_kill {u v w : ℤ} (hw : w ≠ 0) (huv : IsCoprime u v)
    (hh : v ^ 3 - u ^ 3 - w ^ 3 = 2 * u * v * w) : u * v = 0 := by
  have hsum : -u + v + -w = 0 := hesse_leaf huv.neg_left (by linear_combination hh)
  have hveq : v = u + w := by linarith
  have huvw : u * v * w = 0 := by rw [hveq] at hh ⊢; linear_combination hh
  rcases mul_eq_zero.mp huvw with h1 | h1
  · exact h1
  · exact absurd h1 hw

/-- **THE level-`19` statement** (PROVEN 2026-07-30 over `hesse_leaf`): the only
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

THE PROOF is the explicit `3`-isogeny descent of the section above, and it is
elementary throughout.  Split on the parity of `p`: when `p` is even it is in
fact divisible by `4` (`four_dvd_of_even`) and the equation reduces
(`exists_reduced_even`); either branch then factors the equation as a difference
of squares equal to a cube, `n² − (2pe + 4e³)² = p³`, whose two factors are
coprime, hence cubes (`descent_odd`, `descent_even`).  That yields `p = uv`
together with a point of `19a1` in Hesse coordinates, and `hesse_kill` forces
`uv = 0`.  Finally `p = 0` makes `IsCoprime 0 e` say `IsUnit e`, so `e = ±1`, and
`0 < e` picks `e = 1`.

**The `2`-descent derivation that used to sit in this docstring has MOVED to
`hesse_leaf`**, which is where the remaining work now is; the module docstring
records what that move costs and how to undo it.

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
  (`|p| ≤ 4000`, `1 ≤ e ≤ 300`, coprime) finds `(0, 1)` and nothing else;
* and it is neither vacuous nor over-strong — `(0, 1)` IS a solution, and dropping
  `hcop` admits `(0, k)` for every `k`. -/
theorem integral_leaf {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 + 4 * p ^ 2 * e ^ 2 + 16 * p * e ^ 4 + 16 * e ^ 6) :
    p = 0 ∧ e = 1 := by
  have hp0 : p = 0 := by
    rcases Int.even_or_odd p with hpe | hpo
    · obtain ⟨m, hm⟩ := hpe
      obtain ⟨p₂, hp₂⟩ := four_dvd_of_even (m := m) (e := e) (n := n) (by linarith) h
      subst hp₂
      obtain ⟨n₂, hn₂, hn₂sq⟩ := exists_reduced_even h
      obtain ⟨u, v, huv, hpuv, hh⟩ :=
        descent_even (hcop.of_isCoprime_of_dvd_left ⟨4, by ring⟩) hn₂sq
      rw [hpuv, hesse_kill he.ne' huv hh]; ring
    · obtain ⟨u, v, huv, hpuv, hh⟩ := descent_odd hcop hpo h
      rw [hpuv, hesse_kill (by positivity) huv hh]
  refine ⟨hp0, ?_⟩
  rw [hp0] at hcop
  rcases Int.isUnit_iff.mp (isCoprime_zero_left.mp hcop) with h1 | h1
  · exact h1
  · omega

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
