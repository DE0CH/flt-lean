module

/-
MordellWeil.lean — own work for the Fermat project (not vendored from the
FLT project; mathlib has no Mordell–Weil theorem of any kind).

# The modular curve `X_1(11)` as the elliptic curve `11a3`

This module supplies the arithmetic input that level `11` of Mazur's
torsion theorem needs: the rational points of `y² + y = x³ − x²`.

## Why this is the right next brick

`MazurTorsion.lean` proves `no_prime_torsion_ge_eleven` by reducing to eight
per-level nodes, and then proves each node's general form from a
**Tate-coordinate** node `tateNormalForm_origin_order_ne_ℓ` via the PROVEN
`exists_tateNormalForm`. That reduction already discharges the moduli half
of missing-machinery item 1: the two-parameter family
`tateNormalForm b c : y² + (1 − c)xy − by = x³ − bx²` with the marked point
`(0,0)` is a plane model of `X_1(ℓ)` in the `(b,c)`-coordinates.

What is left at level `11` is exactly the classical Billing–Mahler
argument, and it has two halves:

* the **plane model**: the locus where the origin has order `11` is
  birational to the elliptic curve `v² + v = u³ − u²` — Cremona **11a3**,
  which *is* `X_1(11)`, of genus `1`; and
* the **arithmetic**: `11a3` has Mordell–Weil rank `0` over `ℚ` with
  torsion `ℤ/5`, so `11a3(ℚ)` has exactly five points — and all five are
  cusps, carrying no elliptic curve with a point of order `11`.

The plane model half is PROVEN in `MazurTorsion.lean` (`MazurX1Plane`,
`x1Eleven_plane_ne_zero`). This module is the arithmetic half.

## FRONTIER RESTRUCTURE, 2026-07-26 — the general Mordell–Weil theorem is
## NOT on the critical path, and has been removed

This module used to carry three leaves: `mordellWeil` (the Mordell–Weil
theorem for every elliptic curve over `ℚ`), `curve11a3_isTorsion` (rank `0`
for `11a3`) and `curve11a3_points` (the enumeration, *given finiteness*).
That factorisation was wasteful, and the waste was load-bearing: it put a
whole missing chapter of arithmetic geometry — weak Mordell–Weil via the
Kummer sequence, `S`-units and class groups, plus the theory of canonical
heights, none of which exists in mathlib — in front of level `11`.

The observation that collapses it: the enumeration's finiteness hypothesis
was already **unused** (`_hfin`), so the enumeration *implies* finiteness
rather than needing it. Stated unconditionally it therefore subsumes all
three: five points is finiteness, finiteness is torsion, and torsion plus
finiteness is what rank `0` means for this curve. So the frontier here is
now a single leaf, `curve11a3_rational_points`, carrying exactly the
irreducible arithmetic content (rank `0` for one explicit curve) and no
general theory at all.

Two declarations were deleted rather than left unconsumed, since this
development forbids free-floating code:

* `mordellWeil` — `AddGroup.FG E.toAffine.Point` for every `[E.IsElliptic]`
  `E : WeierstrassCurve ℚ`. Nothing else in the tree consumed it. Note that
  finite generation alone never gives rank `0`, so it was never the hard
  half; it was only ever the route from "rank `0`" to "finite".
* `curve11a3_isTorsion` — `AddMonoid.IsTorsion curve11a3.toAffine.Point`.
  This is now a ONE-LINE corollary and is not an open problem: it is
  `haveI := curve11a3_finite; is_add_torsion_of_finite`. It was removed only
  because, with `curve11a3_finite` proven directly from the enumeration,
  nothing consumes it. Reinstate it verbatim if a consumer appears.

Both are recoverable from git history at this file's parent commit.

## What is PROVEN here and what is left

PROVEN:
* `WeierstrassCurve.curve11a3` and its `IsElliptic` instance — the
  discriminant is `Δ = −11 ≠ 0`, computed rather than asserted.
* `WeierstrassCurve.curve11a3_finite` — `11a3(ℚ)` is FINITE, now proven
  directly from the enumeration by transporting along mathlib's
  `Affine.nonsingularPointEquiv` (`Point ≃ WithZero {xy // Nonsingular}`)
  and bounding the affine part by a four-element set.
* `WeierstrassCurve.curve11a3_points` — the enumeration in the exact form
  `MazurTorsion.lean` calls it, finiteness hypothesis and all. The
  hypothesis is retained (and supplied there by `curve11a3_finite`) so that
  the consumer's call site does not have to change.

THE SHAPE OF THIS MODULE, after the 2026-07-27 reconciliation of the two
parallel level-`14` cuts (`main`'s `curve14a4_rational_T` and `flt-lean-86`'s
`MazurLevel14` descent — they are the SAME statement, so nothing was
discarded). `mordellWeil` (the general Mordell–Weil theorem) and
`curve11a3_isTorsion` are GONE: they were deleted, not proven, because
neither level consumes them any longer. Each level is now an unconditional
plane-Diophantine statement, from which rank `0`, finiteness AND the point
enumeration all follow; they are not independent facts, and none of the three
implies the others. Finiteness is DERIVED from the enumeration rather than
assumed for it, and that is what breaks the circle at each level. The scar
`curve14a4_fg` — the single-curve Mordell–Weil leaf opened at integration only
to repair a clean merge — is closed rather than carried.

The released consumer names are unchanged: `curve11a3_rational_points`,
`curve11a3_finite`, `curve11a3_points`, `curve14a4_rational_T`,
`curve14a4_affine_points`, `curve14a4_points`, `curve14a4_finite`,
`curve14a4_isTorsion`. What changed is that both levels' plane statements are
now PROVEN one level further down, over the leaves listed next.

THE ONE LEAF AT LEVEL `11` (2026-07-26: now `MazurLevel11.integral_leaf`).
`WeierstrassCurve.curve11a3_rational_points` — the four affine rational points
of `y² + y = x³ − x²`, unconditionally — is PROVEN from it. The Weierstrass API
and the rationals have been stripped off: with `U = 4x`, `W = 8y + 4` the curve
is the monic integral model `W² = U³ − 4U² + 16`, and
`RationalPointDescent.exists_int_model` turns a rational point into an integral
one, so what is left is the pure integer statement

    n² = p³ − 4p²e² + 16e⁶,  gcd(p, e) = 1,  e > 0   ⟹   (p,e) = (0,1) or (4,1).

That is the whole arithmetic content of level `11` and nothing else. See the
`MazurLevel11` section docstring for why no elementary descent reaches it.

## LEVEL `14`, 2026-07-26: `curve14a4_isTorsion` is PROVEN, and the residue is
## two elementary quartics

`curve14a4_isTorsion` (rank `0` for `14a4`) was a leaf that appeared to need
the Mordell–Weil theorem and a rank function. It does not. `14a4` has a
rational point of order `2` — its `2`-division polynomial `4x³ + x² − 2x + 1`
has the rational root `x = −1` — so the classical `2`-isogeny descent is
available, and in its ELEMENTARY (Diophantine, no group law) form it is exactly
the argument the conductor-`15` cluster `MazurLevel15` already runs in
`MazurTorsion.lean`.

The `MazurLevel14` section below carries that descent. Its `T_trichotomy` IS
`curve14a4_rational_T` — the statement `main` carried as the single level-`14`
leaf — so that leaf is now PROVEN, and with it `curve14a4_affine_points`,
`curve14a4_points`, `curve14a4_finite` and `curve14a4_isTorsion`, all of which
were already written over it. The whole level reduces to exactly two explicit
integer statements:

* `MazurLevel14.quartic_one`  — `Q² =  S⁴ − 11S²e² + 32e⁴` has only `(S,e) = (2,1)`;
* `MazurLevel14.quartic_two`  — `Q² = 2S⁴ − 11S²e² + 16e⁴` has only `(S,e) = (2,1)`.

**`11a3` gets no such route, and this is not a matter of effort.**
`4x³ − 4x² + 1` is irreducible over `ℚ` (the candidates `±1, ±1/2, ±1/4` all
fail), so `E[2]` is irreducible and the isogeny class `11a` contains no
`2`-isogeny at all. The descent there is by the rational `5`-isogeny, whose
dual side is `H¹(ℚ, ℤ/5)` — cyclic quintic extensions unramified outside
`{5, 11}` with local conditions — and that needs class field theory, not a
`gcd` argument. The alternative, a `2`-descent over the cubic field
`ℚ[s]/(s³ − 2s² + 2)` of discriminant `−44`, needs that field's class group and
unit group. Neither is in the pin. See `curve11a3_rational_points`.

The `X_1(11)` plane model itself — the birational passage between
`tateNormalForm b c` with an order-`11` origin and a rational point of
`curve11a3` — lives in `MazurTorsion.lean`, next to its consumer. That
passage is `x1Eleven_plane_ne_zero`, and it takes the PLANE route rather
than the original birational one: main's `MazurX1Plane` section derives the
plane quintic `F₁₁(b, c)` inside Lean from the proven `normEDS`/`preΨ'`
recursion, so the modular curve never has to be transported — one leaf
fewer. `x1Eleven_plane_ne_zero` reduces `F₁₁` to this file's `curve11a3` by
an explicit birational map and consumes `curve11a3_points` through
`WeierstrassCurve.x1Eleven_11a3_x_eq_zero_or_one`. That is what makes this
module reachable from the root theorem.
-/

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section

namespace WeierstrassCurve

/-! ### Rational points of a monic integral cubic are integral points

The one piece of plumbing that every curve in this module needs, and that
nothing in the pin provides: a rational solution of `V² = T³ + AT² + BT + C`
with `A, B, C ∈ ℤ` has `T = p/e²` and `V = n/e³` with `gcd(p, e) = 1`. It is
used at level `11` (`MazurLevel11`) and at level `14` (`MazurLevel14`). -/

namespace RationalPointDescent

/-- **The denominator of a rational point on a monic integral cubic is a
square** (PROVEN 2026-07-26).

If `V² = T³ + AT² + BT + C` with `A, B, C` integers, then writing
`T = T.num / T.den` in lowest terms, `T.den` is coprime to
`T.num³ + A T.num² T.den + B T.num T.den² + C T.den³`, which forces
`V.den² = T.den³` and hence `T.den = e²`, `V.den = e³`. Clearing denominators
then gives the integral equation below.

This is the standard first step of any descent on a Weierstrass curve and it is
stated once here rather than per curve. -/
theorem exists_int_model {A B C : ℤ} {T V : ℚ}
    (h : V ^ 2 = T ^ 3 + (A : ℚ) * T ^ 2 + (B : ℚ) * T + (C : ℚ)) :
    ∃ p e n : ℤ, 0 < e ∧ IsCoprime p e ∧ T = (p : ℚ) / (e : ℚ) ^ 2 ∧
      n ^ 2 = p ^ 3 + A * p ^ 2 * e ^ 2 + B * p * e ^ 4 + C * e ^ 6 := by
  have hTn : (T.num : ℚ) = T * ((T.den : ℤ) : ℚ) := by
    push_cast; exact (div_eq_iff (by exact_mod_cast T.den_nz)).mp (Rat.num_div_den T)
  have hVn : (V.num : ℚ) = V * ((V.den : ℤ) : ℚ) := by
    push_cast; exact (div_eq_iff (by exact_mod_cast V.den_nz)).mp (Rat.num_div_den V)
  have hrel : V.num ^ 2 * (T.den : ℤ) ^ 3 =
      (V.den : ℤ) ^ 2 * (T.num ^ 3 + A * T.num ^ 2 * (T.den : ℤ)
        + B * T.num * (T.den : ℤ) ^ 2 + C * (T.den : ℤ) ^ 3) := by
    have hq : ((V.num : ℚ)) ^ 2 * (((T.den : ℤ) : ℚ)) ^ 3 =
        (((V.den : ℤ) : ℚ)) ^ 2 * ((T.num : ℚ) ^ 3
          + (A : ℚ) * (T.num : ℚ) ^ 2 * (((T.den : ℤ) : ℚ))
          + (B : ℚ) * (T.num : ℚ) * (((T.den : ℤ) : ℚ)) ^ 2
          + (C : ℚ) * (((T.den : ℤ) : ℚ)) ^ 3) := by
      rw [hTn, hVn]
      linear_combination (((V.den : ℤ) : ℚ)) ^ 2 * (((T.den : ℤ) : ℚ)) ^ 3 * h
    exact_mod_cast hq
  have hpq : IsCoprime T.num ((T.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using T.reduced
  have hrs : IsCoprime V.num ((V.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd] using V.reduced
  have hqN : IsCoprime ((T.den : ℤ))
      (T.num ^ 3 + A * T.num ^ 2 * (T.den : ℤ) + B * T.num * (T.den : ℤ) ^ 2
        + C * (T.den : ℤ) ^ 3) := by
    have h3 : IsCoprime ((T.den : ℤ)) (T.num ^ 3) := (hpq.symm).pow_right
    have hrw : T.num ^ 3 + A * T.num ^ 2 * (T.den : ℤ) + B * T.num * (T.den : ℤ) ^ 2
          + C * (T.den : ℤ) ^ 3
        = T.num ^ 3 + (T.den : ℤ) * (A * T.num ^ 2 + B * T.num * (T.den : ℤ)
          + C * (T.den : ℤ) ^ 2) := by ring
    rw [hrw]; exact h3.add_mul_left_right _
  have hd1 : ((V.den : ℤ)) ^ 2 ∣ ((T.den : ℤ)) ^ 3 := by
    have hdv : ((V.den : ℤ)) ^ 2 ∣ V.num ^ 2 * ((T.den : ℤ)) ^ 3 := ⟨_, hrel⟩
    exact ((hrs.symm).pow (m := 2) (n := 2)).dvd_of_dvd_mul_left hdv
  have hd2 : ((T.den : ℤ)) ^ 3 ∣ ((V.den : ℤ)) ^ 2 := by
    have hdv : ((T.den : ℤ)) ^ 3 ∣ ((V.den : ℤ)) ^ 2 *
        (T.num ^ 3 + A * T.num ^ 2 * (T.den : ℤ) + B * T.num * (T.den : ℤ) ^ 2
          + C * (T.den : ℤ) ^ 3) := ⟨V.num ^ 2, by linarith [hrel]⟩
    exact hqN.pow_left.dvd_of_dvd_mul_right hdv
  have hqs : ((T.den : ℤ)) ^ 3 = ((V.den : ℤ)) ^ 2 :=
    Int.dvd_antisymm (by positivity) (by positivity) hd2 hd1
  have hnat : T.den ^ 3 = V.den ^ 2 := by exact_mod_cast hqs
  obtain ⟨c, hc1, hc2⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (three_ne_zero)) hnat
  norm_num at hc1 hc2
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun hzero => T.den_nz (by simp [hc1, hzero])
  refine ⟨T.num, (c : ℤ), V.num, by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · have hqe : ((T.den : ℤ)) = (c : ℤ) ^ 2 := by exact_mod_cast hc1
    rw [hqe] at hpq
    exact hpq.of_isCoprime_of_dvd_right (dvd_pow_self _ two_ne_zero)
  · have hqe : ((T.den : ℚ)) = ((c : ℚ)) ^ 2 := by exact_mod_cast hc1
    push_cast
    rw [← hqe]
    exact (Rat.num_div_den T).symm
  · have hqe : ((T.den : ℤ)) = (c : ℤ) ^ 2 := by exact_mod_cast hc1
    have hse : ((V.den : ℤ)) = (c : ℤ) ^ 3 := by exact_mod_cast hc2
    rw [hqe, hse] at hrel
    have hcne : ((c : ℤ)) ^ 6 ≠ 0 := by positivity
    refine mul_left_cancel₀ hcne ?_
    linear_combination hrel

end RationalPointDescent

/-! ### `X_1(11)` as the elliptic curve 11a3 -/

/-- **The modular curve `X_1(11)`**, as the elliptic curve
`y² + y = x³ − x²` — Cremona label **11a3**, the curve of conductor `11`
and discriminant `Δ = −11`.

`X_1(11)` has genus `1` and a rational cusp, so it *is* an elliptic curve
over `ℚ`; this is that curve. Its Mordell–Weil group is `ℤ/5`, and all five
rational points are cusps — which is precisely why no elliptic curve over
`ℚ` has a rational point of order `11`. -/
def curve11a3 : WeierstrassCurve ℚ := ⟨0, -1, 1, 0, 0⟩

/-- `11a3` is an elliptic curve: its discriminant is `Δ = −11 ≠ 0`.

Computed from `b₂ = −4`, `b₄ = 0`, `b₆ = 1`, `b₈ = −1`, giving
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = 16 − 27 = −11`. -/
instance instIsEllipticCurve11a3 : curve11a3.IsElliptic := by
  refine ⟨?_⟩
  refine isUnit_iff_ne_zero.mpr ?_
  simp only [curve11a3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-! ### The level-`11` reduction to a pure integer statement (2026-07-26)

`11a3` admits NO elementary `2`-isogeny descent, and this is structural rather
than a matter of effort: its `2`-division polynomial `4x³ − 4x² + 1` has no
rational root (the candidates `±1, ±1/2, ±1/4` all fail), so `E[2]` is
irreducible over `ℚ` and the whole isogeny class `11a` — `{11a1, 11a2, 11a3}`,
linked by `5`- and `25`-isogenies — contains no `2`-isogeny at all. That is
exactly the hypothesis the conductor-`15` and conductor-`14` descents consume,
so their route is unavailable here; contrast `MazurLevel14`, which works
precisely because `14a4` has the rational `2`-torsion point `(−1, 0)`.

What IS done here is the part that any attack must do anyway, and that is now
PROVEN: strip the Weierstrass API and the rationals off the statement. With
`U = 4x` and `W = 8y + 4` the curve becomes the monic integral model

    W² = U³ − 4U² + 16

(the four affine points are `U ∈ {0, 4}`, `W = ±4`), and
`RationalPointDescent.exists_int_model` turns a rational point into an integral
one. So `curve11a3_rational_points` is now a corollary of the single integer
statement `integral_leaf` below.

WHAT REMAINS, and it is unchanged in substance: the two routes are (i) the
`5`-isogeny descent, whose descent map is `α(P) = f(P)` for
`f = y + x² + xy` with `div(f) = 5(T) − 5(O)` — that side is trivial, but the
DUAL side is `H¹(ℚ, ℤ/5)`, i.e. cyclic quintic extensions unramified outside
`{5, 11}` cut out by local conditions, which needs class field theory; or
(ii) a `2`-descent over the cubic field `ℚ[s]/(s³ − 2s² + 2)` — the `2`-division
field, of discriminant `−44` — which needs that field's class group and unit
group (unit rank `1`). Neither is in the pin, and neither is a `gcd` argument.
Whoever takes `integral_leaf` should expect to build one of them. -/

namespace MazurLevel11

/-- **THE level-`11` leaf** (sorry leaf, 2026-07-26): the only coprime integral
points of the monic model `W² = U³ − 4U² + 16` of `11a3` are `(p, e) = (0, 1)`
and `(4, 1)`, i.e. `U = 0` and `U = 4`.

This is `curve11a3_rational_points` with the Weierstrass API and the rationals
removed; the reduction is PROVEN (`U_dichotomy`), so this statement carries the
ENTIRE arithmetic content of level `11` — rank `0` for one explicit curve — and
nothing else.

Verified by exhaustive search (`|p| < 6000`, `1 ≤ e < 260`, coprime): `(0, 1)`
and `(4, 1)` are the only solutions, so the statement is true as written.

CHECKED EXTERNALLY (PARI/GP, untrusted searcher — not a proof).
`ellinit([0,-1,1,0,0])` gives `disc = −11`, conductor `11`,
`j = −4096/11`; `ellrank` returns rank `0` with matching lower and upper
bounds, i.e. it *proves* rank `0`; `elltors` returns `ℤ/5`; and
`ellratpoints(E, 1000)` returns exactly the four affine points.

See the section docstring above for why no elementary descent reaches this and
what the two genuine routes are. -/
theorem integral_leaf {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 - 4 * p ^ 2 * e ^ 2 + 16 * e ^ 6) :
    (p = 0 ∧ e = 1) ∨ (p = 4 ∧ e = 1) := sorry

/-- **The two rational `U`-values of `W² = U³ − 4U² + 16`** (PROVEN 2026-07-26
from `integral_leaf`): `U ∈ {0, 4}`. These are `U = 4x` for the two
`x`-coordinates `0` and `1` of the four affine rational points of `11a3`. -/
theorem U_dichotomy {U W : ℚ} (h : W ^ 2 = U ^ 3 - 4 * U ^ 2 + 16) :
    U = 0 ∨ U = 4 := by
  obtain ⟨p, e, n, he, hcop, hUeq, hn⟩ :=
    RationalPointDescent.exists_int_model (A := -4) (B := 0) (C := 16) (T := U) (V := W)
      (by push_cast; linear_combination h)
  rcases integral_leaf (n := n) he hcop (by linear_combination hn) with ⟨hp, he1⟩ | ⟨hp, he1⟩
  · left; rw [hUeq, hp, he1]; norm_num
  · right; rw [hUeq, hp, he1]; norm_num

end MazurLevel11

/-- **The rational points of `11a3`** (PROVEN 2026-07-26 from
`MazurLevel11.integral_leaf`): the affine rational points of `y² + y = x³ − x²` are
exactly `(0,0)`, `(0,−1)`, `(1,0)`, `(1,−1)`. With the point at infinity
these are the five elements of `11a3(ℚ) ≅ ℤ/5`, generated by `(0,0)`.

**This single statement carries the whole arithmetic content of level `11`**,
and it is equivalent to "rank `11a3` `= 0`": it is stated unconditionally,
so `curve11a3_finite` and hence torsion-ness are corollaries of it rather
than inputs to it. See the FRONTIER RESTRUCTURE note in the module
docstring for why the general Mordell–Weil theorem is no longer in front of
it — finite generation alone never yields rank `0`, so it was never the
hard half.

CLASSICAL PROOF. Billing–Mahler, "On exceptional points on cubic curves"
(J. London Math. Soc. 15, 1940); subsumed in Mazur 1977, Thm 7. The
argument is a **descent by the rational `5`-isogeny** that `11a3` admits,
not a `2`-descent: `E[2]` is irreducible here (`4x³ − 4x² + 1` has no
rational root), and in any case a complete `2`-descent bounds
`E(ℚ)/2E(ℚ)` without giving rank `0` in the absence of the height theory.
Both `5`-Selmer groups vanish, so the rank is `0`. Silverman AEC X.4
(descent via a general isogeny) is the recipe; the isogeny class of `11a3`
is `{11a1, 11a2, 11a3}` with `5`- and `25`-isogenies between them, and
`11a3` is `5`-isogenous to `11a1`.

CONCRETE STARTING POINT for that descent, computed and checked here so the
next owner does not have to rediscover it. Let `T = (0,0)`, which generates
the rational `5`-torsion, and put

    f = y + x² + x y  ∈  ℚ(11a3).

Then `div(f) = 5(T) − 5(O)`: at `O` the pole orders of `x`, `y`, `x²`, `xy`
are `2, 3, 4, 5`, so `f` has pole order exactly `5`; and expanding the
curve equation at `T` with `x` as uniformiser gives
`y = −x² + x³ − x⁴ + 2x⁵ + O(x⁶)`, whence `f = x⁵ + O(x⁶)`, a zero of order
exactly `5`. `f` is therefore the function underlying the `5`-descent map
`α : 11a3(ℚ) → ℚ*/(ℚ*)⁵`. Its values on the four points below are
`f(0,0) = 0`, `f(1,0) = 1`, `f(0,−1) = −1`, `f(1,−1) = −1` — and `−1 = (−1)⁵`
is a fifth power, so the image of `α` is trivial, exactly as a rank-`0`
descent predicts.

CHECKED EXTERNALLY (PARI/GP, as an untrusted searcher — not a proof).
`ellinit([0,-1,1,0,0])` gives `disc = −11`, conductor `11`,
`j = −4096/11 = −2¹²/11`; `ellrank` returns rank `0` with matching lower and
upper bounds, i.e. it *proves* rank `0`; `elltors` returns `ℤ/5`; and
`ellratpoints(E, 1000)` returns exactly the four points below.

WHAT A LEAN PROOF STILL NEEDS. Mathlib has no isogenies of elliptic curves,
no Selmer groups and no Galois cohomology of curves, so the descent above
cannot be assembled from the pin as it stands. The two routes that avoid
building all of it are (i) formalise the `5`-isogeny descent for this one
curve concretely, using `f` above and unique factorisation to run the
descent by hand on the coprime factorisation of
`(2y+1)² = 4x³ − 4x² + 1`; or (ii) develop the general descent machinery.
Route (i) is the smaller of the two and is what the concrete data above is
for.

DECOMPOSED 2026-07-26. This is no longer the leaf: the Weierstrass-API layer
has been stripped off and PROVEN, leaving the pure integer statement
`MazurLevel11.integral_leaf`. See that declaration and the `MazurLevel11`
section docstring. -/
theorem curve11a3_rational_points (x y : ℚ)
    (h : curve11a3.toAffine.Nonsingular x y) :
    (x, y) = ((0 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((1 : ℚ), (-1 : ℚ)) := by
  have he := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [curve11a3, WeierstrassCurve.toAffine] at he
  have hWU : (8 * y + 4) ^ 2 = (4 * x) ^ 3 - 4 * (4 * x) ^ 2 + 16 := by
    linear_combination (64 : ℚ) * he
  have hsq : (8 * y + 4) ^ 2 = 16 := by
    rcases MazurLevel11.U_dichotomy hWU with hU | hU <;> rw [hWU, hU] <;> norm_num
  have hW : (8 * y + 4 - 4) * (8 * y + 4 + 4) = 0 := by linear_combination hsq
  have hy : y = 0 ∨ y = -1 := by
    rcases mul_eq_zero.mp hW with hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hx : x = 0 ∨ x = 1 := by
    rcases MazurLevel11.U_dichotomy hWU with hU | hU
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

/-- **`11a3(ℚ)` is finite** (PROVEN 2026-07-26, directly from
`curve11a3_rational_points`).

Previously this was the descent conclusion "finitely generated + rank `0` ⟹
finite", assembled from the Mordell–Weil theorem and a rank-`0` leaf. Both
of those are now gone: the enumeration is stated unconditionally, so
finiteness follows from it by transporting along mathlib's
`Affine.nonsingularPointEquiv : W.Point ≃ WithZero {xy // W.Nonsingular xy.1 xy.2}`
and observing that the affine part is contained in a four-element set. -/
theorem curve11a3_finite : Finite curve11a3.toAffine.Point := by
  have hsub : {xy : ℚ × ℚ | curve11a3.toAffine.Nonsingular xy.1 xy.2} ⊆
      ({((0 : ℚ), (0 : ℚ)), (0, -1), (1, 0), (1, -1)} : Set (ℚ × ℚ)) := by
    rintro ⟨x, y⟩ hxy
    rcases curve11a3_rational_points x y hxy with h | h | h | h <;> rw [h] <;> simp
  haveI : Finite {xy : ℚ × ℚ // curve11a3.toAffine.Nonsingular xy.fst xy.snd} :=
    (Set.Finite.subset ((((Set.finite_singleton _).insert _).insert _).insert _) hsub).to_subtype
  haveI : Finite (WithZero {xy : ℚ × ℚ // curve11a3.toAffine.Nonsingular xy.fst xy.snd}) :=
    inferInstanceAs (Finite (Option _))
  exact Finite.of_equiv _ curve11a3.toAffine.nonsingularPointEquiv.symm

/-- **The five rational points of `11a3`** (PROVEN 2026-07-26 from
`curve11a3_rational_points`), in the exact form `MazurTorsion.lean` calls
it: given that `11a3(ℚ)` is finite, its affine rational points are exactly
`(0,0)`, `(0,−1)`, `(1,0)`, `(1,−1)`.

The finiteness hypothesis is now REDUNDANT — it is `_hfin`, unused, and it
was already unused when this was a leaf, which is precisely the observation
that let the Mordell–Weil theorem be removed from level `11` (see the
module docstring). It is retained in the signature so that the call site
`WeierstrassCurve.x1Eleven_11a3_x_eq_zero_or_one` in `MazurTorsion.lean`,
which supplies it as `curve11a3_finite`, does not have to change; that is
also what keeps `curve11a3_finite` consumed rather than free-floating. A
future owner is free to drop the hypothesis and adjust the one call site.

All five points are CUSPS of `X_1(11)`; that is the input to
`WeierstrassCurve.x1Eleven_11a3_x_eq_zero_or_one` in `MazurTorsion.lean`,
whose consumer `x1Eleven_plane_ne_zero` shows the two cusps with a finite
`b`-coordinate, `x = 0` and `x = 1`, to be the loci `b = c² + c` and
`b = c` of the Tate family — neither of which meets the chart `b ≠ 0`. -/
theorem curve11a3_points (_hfin : Finite curve11a3.toAffine.Point) (x y : ℚ)
    (h : curve11a3.toAffine.Nonsingular x y) :
    (x, y) = ((0 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((1 : ℚ), (-1 : ℚ)) :=
  curve11a3_rational_points x y h

/-! ### `X_1(14)` as the elliptic curve 14a4 -/

/-- **The modular curve `X_1(14)`**, as the elliptic curve
`y² + xy + y = x³ − x` — Cremona label **14a4**, the curve of conductor `14`
and discriminant `Δ = −28`.

`X_1(14)` has genus `1` and a rational cusp, so it *is* an elliptic curve over
`ℚ`; this is that curve. Its Mordell–Weil group is `ℤ/6`, and all six rational
points are cusps — which is precisely why no elliptic curve over `ℚ` carries a
rational point of order `2` together with one of order `7`.

IDENTIFICATION (Magma 2026-07-26, untrusted searcher; the classical fact is
Kubert's and Ligozat's). The `2`-division cubic of the Kubert family
`E(d³ − d², d² − d)` of `X_1(7)`, i.e. the plane sextic

    4x³ + ((1 + d − d²)² − 4(d³ − d²))x² − 2(1 + d − d²)(d³ − d²)x + (d³ − d²)²

in the coordinates `(d, x)`, has projective closure of `Genus = 1`, and
`EllipticCurve` + `MinimalModel` return exactly `y² + xy + y = x³ − x`, with
`Conductor = 14` and `CremonaReference = 14a4`. That birational map is written
out and PROVEN in `x1_fourteen_no_rational_point`
(`Fermat/FLT/FreyCurve/TateNormalForm.lean`), so this curve is the whole
arithmetic content of level `14`, exactly as `curve11a3` is of level `11`. -/
def curve14a4 : WeierstrassCurve ℚ := ⟨1, 0, 1, -1, 0⟩

/-- `14a4` is an elliptic curve: its discriminant is `Δ = −28 ≠ 0`.

Computed from `b₂ = 1`, `b₄ = −1`, `b₆ = 1`, `b₈ = 0`, giving
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = 0 + 8 − 27 − 9 = −28`. -/
instance instIsEllipticCurve14a4 : curve14a4.IsElliptic := by
  refine ⟨?_⟩
  refine isUnit_iff_ne_zero.mpr ?_
  simp only [curve14a4, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-! ### The level-`14` descent, in elementary form (2026-07-26)

`MazurLevel14` is the arithmetic engine behind `curve14a4_isTorsion`: it proves
the UNCONDITIONAL enumeration of `14a4(ℚ)` by a completely elementary
Diophantine descent, with **no group law, no rank function, no Mordell–Weil
theorem and no Selmer group** anywhere in it. It is modelled directly on the
`MazurLevel15` cluster in `MazurTorsion.lean`, which closed the conductor-`15`
curve `V² = X(X+1)(X+16)` the same way.

**Why an elementary route exists here and NOT for `11a3`.** `14a4` has a
rational point of order `2`, namely `(−1, 0)`: its `2`-division polynomial
`4x³ + x² − 2x + 1` has the rational root `x = −1`. That single rational root
is what lets the cubic be split off as a linear factor over `ℚ`, which is the
whole content of a `2`-isogeny descent in elementary form. `11a3`'s
`2`-division polynomial `4x³ − 4x² + 1` is irreducible over `ℚ` (no rational
root: the candidates `±1, ±1/2, ±1/4` all fail), so `E[2]` is irreducible
there, no `2`-isogeny exists anywhere in the isogeny class `11a`, and this
route is simply unavailable — see `curve11a3_rational_points`.

**The chain, completely explicit.** Let `(x, y)` be a rational point.

* Completing the square with `Y = 2y + x + 1` gives `Y² = 4x³ + x² − 2x + 1`,
  and then `T = 4x + 4`, `V = 4Y = 8y + 4x + 4` give the integral model

      V² = T³ − 11T² + 32T = T · (T² − 11T + 32).

  This is `14a4` moved so that its rational `2`-torsion point sits at the
  origin; `4(T² − 11T + 32) = (2T − 11)² + 7`, so the quadratic factor is
  positive for every real `T` and never has a rational root.
* Hence `V² = T · (positive)`, so `T ≥ 0`, and `T = 0` is the `2`-torsion point
  `(x, y) = (−1, 0)` itself.
* For `T > 0`: writing `T = p/q` in lowest terms, `q` is coprime to
  `p(p² − 11pq + 32q²)`, which forces `V.den² = q³` and hence `q = e²` a
  perfect square (`exists_int_model`). So `T = p/e²`, `V = n/e³` and

      n² = p · (p² − 11pe² + 32e⁴),   gcd(p, e) = 1,  p, e > 0.

* Both factors are positive and their `gcd` `g` divides `32` (it divides `p`,
  and `32e⁴` is an integer combination of the two, while `gcd(g, e) = 1`).
  `split_gcd` then writes `p = g a²` and the second factor as `g b²`; absorbing
  the square part of `g` into `a` leaves exactly the two square-free classes
  `d ∈ {1, 2}` — `d` cannot be negative because `p > 0` — and the descent
  equation `d S⁴ − 11 S²e² + (32/d) e⁴ = Q²` (`descent_step`).

That leaves the two homogeneous spaces below. **Neither is
congruence-obstructed** — each carries exactly one rational point, which is why
each is a leaf rather than a `decide` — and they are the entire residual
content of `curve14a4_isTorsion`.

    d = 1 : Q² =  S⁴ − 11S²e² + 32e⁴      (`quartic_one`; solution `(S,e) = (2,1)`, `T = 4`)
    d = 2 : Q² = 2S⁴ − 11S²e² + 16e⁴      (`quartic_two`; solution `(S,e) = (2,1)`, `T = 8`)

Verified by exhaustive search (`1 ≤ S, e ≤ 700`, coprime): `(S, e) = (2, 1)` is
the ONLY solution of each, so both statements are true as written and each is a
genuine infinite descent in the style of `MazurLevel15.concordant_one` /
`concordant_five`, `QuarticDescent.not_isSquare_form` (conductor `20`) and
`MazurTwoTwelve.Quartic` (conductor `24`).

RECONNAISSANCE FOR WHOEVER TAKES THE TWO QUARTICS. Both are norm forms for
`ℚ(√−7)` — completing the square gives `4Q² = u² + 7e⁴` with `u = 2S² − 11e²`
for `quartic_one`, and `8Q² = u² + 7e⁴` with `u = 4S² − 11e²` for
`quartic_two`; `ℤ[(1 + √−7)/2]` is a PID, which is what makes the coprime
factorisation available. Worked first step for `quartic_one` with `e` odd:
`u` is then odd and `Q` even, `(2Q − u)(2Q + u) = 7e⁴` has coprime factors
(a common factor would have to be `7`, which forces `7 ∣ e` against
`gcd(u, e) = 1`), so `2Q − u = 7m⁴`, `2Q + u = n⁴` with `mn = e`,
`gcd(m, n) = 1`, and substituting `u = 2S² − 11m²n²` gives

    4S² = ± (n⁴ − 7m⁴) + 22m²n².

The `−` branch is `4S² = 7m⁴ + 22m²n² − n⁴`, which **dies mod `7`**: squares
and fourth powers mod `7` both lie in `{0, 1, 2, 4}`, so `4S² ≡ −n⁴` forces
`7 ∣ S` and `7 ∣ n`, and then dividing through forces `7 ∣ m`, contradicting
`gcd(m, n) = 1`. The `+` branch `4S² = n⁴ + 22m²n² − 7m⁴` carries the solution
`m = n = 1` and is where the genuine descent continues; note
`4S² = (n² + 11m²)² − 128m⁴`. The `e` even case of `quartic_one` splits
further: `e ≡ 2 mod 4` dies mod `8` (the form is `≡ 5 mod 8`, not a square),
while `e ≡ 0 mod 4` needs the descent again.

These two forms are, in the classical language, the `d = 7` and `d = −1`
homogeneous spaces of the `2`-isogenous curve `Y² = X³ + 22X² − 7X`
(`a' = −2a = 22`, `b' = a² − 4b = −7`). That is the *reason* rank `0` is true
here: `Im α ⊆ {1, 2}` automatically because `T > 0`, and `Im α' = {1, −7}`
because the `d = 7` space dies mod `7`, so `2^rank = 2 · 2 / 4 = 1`.
`RankBound(14a4) = 0` with proof flag `true` (Magma, untrusted searcher);
`MordellWeilGroup` returns `ℤ/6`. -/
namespace MazurLevel14

/-- A nonnegative coprime factor of a square is a square. (Same statement as
`MazurLevel15.sq_of_gcd_nonneg`, which lives in `MazurTorsion.lean` — that
module imports THIS one, so it cannot be imported here.) -/
theorem sq_of_gcd_nonneg {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2)
    (ha : 0 ≤ a) : ∃ a0 : ℤ, a = a0 ^ 2 := by
  obtain ⟨a0, ha0 | ha0⟩ := Int.sq_of_gcd_eq_one h heq
  · exact ⟨a0, ha0⟩
  · rw [ha0] at ha
    have h1 : a0 ^ 2 = 0 := by linarith [sq_nonneg a0]
    exact ⟨0, by rw [ha0, h1]; ring⟩

/-- **Splitting a square along the `gcd`.** If `A · B = c²` with `A`, `B ≥ 0`
and `A ≠ 0`, then writing `g = gcd(A, B)` both cofactors are `g` times a
square. This is the workhorse of `descent_step`, where `g` is constrained to
divide `32`. (Same statement as `MazurLevel15.split_gcd`; see
`sq_of_gcd_nonneg` for why it is restated rather than imported.) -/
theorem split_gcd {A B c : ℤ} (hAB : A * B = c ^ 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hA0 : A ≠ 0) :
    ∃ a b : ℤ, A = (Int.gcd A B : ℤ) * a ^ 2 ∧ B = (Int.gcd A B : ℤ) * b ^ 2 ∧
      IsCoprime a b := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = Int.gcd A B := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hgdef]; exact Int.gcd_pos_iff.mpr (Or.inl hA0)
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hgp : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
  obtain ⟨A₁, hA₁⟩ : (g : ℤ) ∣ A := by rw [hgdef]; exact Int.gcd_dvd_left A B
  obtain ⟨B₁, hB₁⟩ : (g : ℤ) ∣ B := by rw [hgdef]; exact Int.gcd_dvd_right A B
  have hcop1 : Int.gcd A₁ B₁ = 1 := by
    have h0 := Int.gcd_div_gcd_div_gcd (i := A) (j := B) (by rw [← hgdef]; exact hgpos)
    rw [← hgdef] at h0
    rwa [hA₁, hB₁, Int.mul_ediv_cancel_left _ hgz, Int.mul_ediv_cancel_left _ hgz] at h0
  obtain ⟨c₁, hc₁⟩ : (g : ℤ) ∣ c := by
    have h2 : ((g : ℤ)) ^ 2 ∣ c ^ 2 := ⟨A₁ * B₁, by rw [← hAB, hA₁, hB₁]; ring⟩
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp h2
  have hpq : A₁ * B₁ = c₁ ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hgz) ?_
    have h' : ((g : ℤ) * A₁) * ((g : ℤ) * B₁) = ((g : ℤ) * c₁) ^ 2 := by
      rw [← hA₁, ← hB₁, ← hc₁]; exact hAB
    linear_combination h'
  have hA₁0 : 0 ≤ A₁ := by
    by_contra hcon
    have h' : A₁ < 0 := not_le.mp hcon
    have hlt : A < 0 := by rw [hA₁]; exact mul_neg_of_pos_of_neg hgp h'
    linarith
  have hB₁0 : 0 ≤ B₁ := by
    by_contra hcon
    have h' : B₁ < 0 := not_le.mp hcon
    have hlt : B < 0 := by rw [hB₁]; exact mul_neg_of_pos_of_neg hgp h'
    linarith
  obtain ⟨a, ha⟩ := sq_of_gcd_nonneg hcop1 hpq hA₁0
  obtain ⟨b, hb⟩ := sq_of_gcd_nonneg (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact hpq) hB₁0
  have hcop2 : IsCoprime a b := by
    rw [ha, hb] at hcop1
    have hc := Int.isCoprime_iff_gcd_eq_one.mpr hcop1
    exact ((hc.of_isCoprime_of_dvd_left (dvd_pow_self a two_ne_zero)).symm.of_isCoprime_of_dvd_left
      (dvd_pow_self b two_ne_zero)).symm
  exact ⟨a, b, by rw [← hgdef, hA₁, ha], by rw [← hgdef, hB₁, hb], hcop2⟩

/-- The divisors of `32`, which is where the descent `gcd` lives. -/
theorem dvd_thirtytwo {n : ℕ} (h : n ∣ 32) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 := by
  have hle : n ≤ 32 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> revert h <;> decide

/-- **The `d = 1` homogeneous space of `14a4`** (sorry leaf, 2026-07-26): the
only coprime positive solution of `Q² = S⁴ − 11S²e² + 32e⁴` is `(S, e) = (2, 1)`,
which is the rational point `T = 4` of `V² = T³ − 11T² + 32T`, i.e. the pair of
points `(x, y) = (0, 0)` and `(0, −1)` of `14a4`.

Not congruence-obstructed: it carries that one point, so it needs a genuine
infinite descent. See the `MazurLevel14` section docstring for the worked first
step (`4Q² = (2S² − 11e²)² + 7e⁴`, the coprime factorisation over `ℤ`, the
`mod 7` death of one branch and the `mod 8` death of `e ≡ 2 mod 4`) and for the
classical reading as a `2`-isogeny homogeneous space. -/
theorem quartic_one {S e Q : ℤ} (hS : 0 < S) (he : 0 < e) (hcop : IsCoprime S e)
    (h : S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4 = Q ^ 2) : S = 2 ∧ e = 1 := sorry

/-- **The `d = 2` homogeneous space of `14a4`** (sorry leaf, 2026-07-26): the
only coprime positive solution of `Q² = 2S⁴ − 11S²e² + 16e⁴` is `(S, e) = (2, 1)`,
which is the rational point `T = 8`, i.e. the pair `(x, y) = (1, 0)` and
`(1, −2)` of `14a4`.

Same shape as `quartic_one` and equally un-obstructed; here the completed
square is `8Q² = (4S² − 11e²)² + 7e⁴`. -/
theorem quartic_two {S e Q : ℤ} (hS : 0 < S) (he : 0 < e) (hcop : IsCoprime S e)
    (h : 2 * S ^ 4 - 11 * S ^ 2 * e ^ 2 + 16 * e ^ 4 = Q ^ 2) : S = 2 ∧ e = 1 := sorry

/-- The `d = 1` shape of the `gcd` split: `g = c²` is a square, so `p` is a
square and the descent equation is `quartic_one`'s. -/
theorem case_one {p e a b c : ℤ} (hc : 0 < c) (ha0 : a ≠ 0) (hcop : IsCoprime p e)
    (ha : p = c ^ 2 * a ^ 2) (hb : p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4 = c ^ 2 * b ^ 2) :
    ∃ S Q : ℤ, 0 < S ∧ IsCoprime S e ∧ p = S ^ 2 ∧
      S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4 = Q ^ 2 := by
  have hS2 : (c * |a|) ^ 2 = c ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
  have hSp : p = (c * |a|) ^ 2 := by rw [hS2]; exact ha
  refine ⟨c * |a|, c * b, mul_pos hc (abs_pos.mpr ha0),
    hcop.of_isCoprime_of_dvd_left ⟨c * |a|, by rw [hSp]; ring⟩, hSp, ?_⟩
  rw [ha] at hb
  linear_combination hb + ((c * |a|) ^ 2 + c ^ 2 * a ^ 2 - 11 * e ^ 2) * hS2

/-- The `d = 2` shape of the `gcd` split: `g = 2c²`, so `p = 2S²` and the
descent equation is `quartic_two`'s. -/
theorem case_two {p e a b c : ℤ} (hc : 0 < c) (ha0 : a ≠ 0) (hcop : IsCoprime p e)
    (ha : p = 2 * (c ^ 2 * a ^ 2))
    (hb : p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4 = 2 * (c ^ 2 * b ^ 2)) :
    ∃ S Q : ℤ, 0 < S ∧ IsCoprime S e ∧ p = 2 * S ^ 2 ∧
      2 * S ^ 4 - 11 * S ^ 2 * e ^ 2 + 16 * e ^ 4 = Q ^ 2 := by
  have hS2 : (c * |a|) ^ 2 = c ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
  have hSp : p = 2 * (c * |a|) ^ 2 := by rw [hS2]; exact ha
  refine ⟨c * |a|, c * b, mul_pos hc (abs_pos.mpr ha0),
    hcop.of_isCoprime_of_dvd_left ⟨2 * (c * |a|), by rw [hSp]; ring⟩, hSp, ?_⟩
  rw [ha] at hb
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination hb + (4 * ((c * |a|) ^ 2 + c ^ 2 * a ^ 2) - 22 * e ^ 2) * hS2

/-- **The `gcd` descent** (PROVEN 2026-07-26): an integral point
`n² = p(p² − 11pe² + 32e⁴)` with `p, e > 0` coprime lies on one of the two
homogeneous spaces `quartic_one` (`d = 1`) or `quartic_two` (`d = 2`).

The `gcd` of the two factors divides `32`, and `p > 0` rules out the negative
square-free classes, which is why only `d ∈ {1, 2}` survive rather than
`d ∈ {±1, ±2}`. -/
theorem descent_step {p e n : ℤ} (hp : 0 < p) (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p * (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4)) :
    ∃ S Q : ℤ, 0 < S ∧ IsCoprime S e ∧
      ((p = S ^ 2 ∧ S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4 = Q ^ 2) ∨
        (p = 2 * S ^ 2 ∧ 2 * S ^ 4 - 11 * S ^ 2 * e ^ 2 + 16 * e ^ 4 = Q ^ 2)) := by
  have he4 : (0 : ℤ) < e ^ 4 := by positivity
  have hBpos : (0 : ℤ) < p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4 := by
    nlinarith [sq_nonneg (2 * p - 11 * e ^ 2)]
  obtain ⟨a, b, ha, hb, _hab⟩ := split_gcd (A := p)
    (B := p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) (c := n) h.symm hp.le hBpos.le hp.ne'
  have hGp : ((Int.gcd p (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) : ℤ)) ∣ p := Int.gcd_dvd_left _ _
  have hGB : ((Int.gcd p (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) : ℤ)) ∣
      p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4 := Int.gcd_dvd_right _ _
  have hGe : IsCoprime ((Int.gcd p (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) : ℤ)) e :=
    hcop.of_isCoprime_of_dvd_left hGp
  have hG32e : ((Int.gcd p (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) : ℤ)) ∣ 32 * e ^ 4 := by
    have hd := dvd_sub hGB (hGp.mul_right (p - 11 * e ^ 2))
    have hrw : (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) - p * (p - 11 * e ^ 2)
        = 32 * e ^ 4 := by ring
    rwa [hrw] at hd
  have hG32 : Int.gcd p (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) ∣ 32 := by
    have := (hGe.pow_right (n := 4)).dvd_of_dvd_mul_right hG32e
    exact_mod_cast this
  have ha0 : a ≠ 0 := by rintro rfl; rw [ha] at hp; simp at hp
  rcases dvd_thirtytwo hG32 with hg | hg | hg | hg | hg | hg <;> rw [hg] at ha hb <;>
    push_cast at ha hb
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_one (c := 1) one_pos ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inl ⟨h3, h4⟩⟩
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_two (c := 1) one_pos ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inr ⟨h3, h4⟩⟩
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_one (c := 2) two_pos ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inl ⟨h3, h4⟩⟩
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_two (c := 2) two_pos ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inr ⟨h3, h4⟩⟩
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_one (c := 4) (by norm_num) ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inl ⟨h3, h4⟩⟩
  · obtain ⟨S, Q, h1, h2, h3, h4⟩ :=
      case_two (c := 4) (by norm_num) ha0 hcop (by linarith) (by linarith)
    exact ⟨S, Q, h1, h2, Or.inr ⟨h3, h4⟩⟩

/-- **The integral model at level `14`** (PROVEN 2026-07-26): a rational
solution of `V² = T³ − 11T² + 32T` with `T > 0` comes from an integral one,
`T = p/e²` with `gcd(p, e) = 1` and `p, e > 0`, satisfying
`n² = p(p² − 11pe² + 32e⁴)`.

The denominator work is `RationalPointDescent.exists_int_model` (`A = −11`,
`B = 32`, `C = 0`); all that is added here is `0 < p`, which comes from
`T = p/e² > 0`, and the factored form of the cubic — the factor `p` being
present is exactly the rational `2`-torsion point, and is what makes the
`gcd` descent of `descent_step` possible. -/
theorem exists_int_model {T V : ℚ} (hT : 0 < T) (h : V ^ 2 = T ^ 3 - 11 * T ^ 2 + 32 * T) :
    ∃ p e n : ℤ, 0 < p ∧ 0 < e ∧ IsCoprime p e ∧ T = (p : ℚ) / (e : ℚ) ^ 2 ∧
      n ^ 2 = p * (p ^ 2 - 11 * p * e ^ 2 + 32 * e ^ 4) := by
  obtain ⟨p, e, n, he, hcop, hTeq, hn⟩ :=
    RationalPointDescent.exists_int_model (A := -11) (B := 32) (C := 0) (T := T) (V := V)
      (by push_cast; linear_combination h)
  refine ⟨p, e, n, ?_, he, hcop, hTeq, by linear_combination hn⟩
  have hene : ((e : ℚ)) ≠ 0 := by exact_mod_cast he.ne'
  have hepos : (0 : ℚ) < ((e : ℚ)) ^ 2 := by positivity
  rw [hTeq] at hT
  rcases div_pos_iff.mp hT with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact_mod_cast h1
  · linarith

/-- **The three rational `T`-values of `V² = T³ − 11T² + 32T`** (PROVEN
2026-07-26 from the two quartic leaves): `T ∈ {0, 4, 8}`.

`T = 0` is the rational `2`-torsion point; `T = 4` and `T = 8` are the two
`x`-fibres each carrying a pair of points. Together with the point at infinity
that is `14a4(ℚ) ≅ ℤ/6`. -/
theorem T_trichotomy {T V : ℚ} (h : V ^ 2 = T ^ 3 - 11 * T ^ 2 + 32 * T) :
    T = 0 ∨ T = 4 ∨ T = 8 := by
  rcases eq_or_ne T 0 with rfl | hT0
  · exact Or.inl rfl
  have hquad : (0 : ℚ) < T ^ 2 - 11 * T + 32 := by nlinarith [sq_nonneg (2 * T - 11)]
  have hTpos : 0 < T := by
    rcases lt_trichotomy T 0 with hlt | heq | hgt
    · exfalso; nlinarith [sq_nonneg V]
    · exact absurd heq hT0
    · exact hgt
  obtain ⟨p, e, n, hp, he, hcop, hTeq, hint⟩ := exists_int_model hTpos h
  obtain ⟨S, Q, hS, hSe, hcase⟩ := descent_step hp he hcop hint
  rcases hcase with ⟨hpS, hq⟩ | ⟨hpS, hq⟩
  · obtain ⟨hS2, he1⟩ := quartic_one hS he hSe hq
    right; left
    rw [hTeq, hpS, hS2, he1]; norm_num
  · obtain ⟨hS2, he1⟩ := quartic_two hS he hSe hq
    right; right
    rw [hTeq, hpS, hS2, he1]; norm_num

end MazurLevel14

/-- **The rational points of the descent model of `14a4`** (PROVEN 2026-07-27
from `MazurLevel14.T_trichotomy`; this was the single level-`14` sorry leaf on
`main`, and the whole `MazurLevel14` descent above exists to discharge it): the
only rational points of

    W² = T³ − 11T² + 32T

have `T ∈ {0, 4, 8}`.

THE MODEL. Completing the square in `14a4 : y² + xy + y = x³ − x` gives
`(2y + x + 1)² = 4x³ + x² − 2x + 1`, and scaling by `T = 4(x + 1)`,
`W = 4(2y + x + 1)` clears the leading `4` and moves the rational `2`-torsion
point to the origin:

    T = 4x + 4,   W = 8y + 4x + 4,   W² = T³ − 11T² + 32T,

an isomorphism of `14a4` onto `[0, −11, 0, 32, 0]` (`Δ = −114688`, conductor
`14`, torsion `ℤ/6`, rank `0` — PARI 2026-07-26, untrusted searcher). The six
rational points are `∞` and `T ∈ {0, 4, 8}` with `W ∈ {0}, {±4}, {±8}`; they
pull back to the point at infinity and the five affine points listed in
`curve14a4_points`.

WHY THIS IS THE RIGHT LEAF, AND WHY IT IS ONE RATHER THAN TWO. Rank `0` and
the torsion enumeration are not independent facts about `14a4`: the single
Diophantine statement above yields both, and neither of the two former leaves
yields the other. `curve14a4_points` follows by the birational map plus solving
the quadratic in `y` at each of `x ∈ {−1, 0, 1}`; `curve14a4_finite` follows by
exhibiting the point set as a subset of a five-element set; and
`curve14a4_isTorsion` is then just "a finite group is torsion". All three are
now PROVEN below, and `mordellWeil` is no longer needed at `14a4` at all.

HOW TO ATTACK IT — the shape is exactly `MazurLevel15.rank_zero_x` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, whose whole elementary-descent chain
(`sq_or_two_sq`, `quartic_*`, `concordant_*`) is the template. Reconnaissance
carried out 2026-07-26 and recorded here so it need not be redone:

* Write `T = p/q` in lowest terms. `q` is coprime to `p(p² − 11pq + 32q²)`, so
  `q = e²`; then `gcd(p, p² − 11pe² + 32e⁴) = gcd(p, 32e⁴)` divides `32`, so
  `p = dS²` with `d ∈ {1, −1, 2, −2}` squarefree.
* `d < 0` dies by POSITIVITY, with no congruence needed: the quadratic
  `T² − 11T + 32` has discriminant `121 − 128 = −7 < 0`, hence is positive
  everywhere, so `W² = T(T² − 11T + 32) ≥ 0` forces `T ≥ 0`.
* `d = 1` gives the quartic `c² = S⁴ − 11S²e² + 32e⁴` (whose only coprime
  solution up to `300` is `(S, e) = (2, 1)`, i.e. `T = 4`), and `d = 2` gives
  `c² = 2S⁴ − 11S²e² + 16e⁴` (only `(0, 1)` and `(2, 1)`, i.e. `T = 0` and
  `T = 8`) — PARI 2026-07-26, untrusted searcher.
* Neither quartic is congruence-obstructed — each HAS a rational point — so
  they must be SOLVED, not excluded, and a genuine SECOND descent is needed,
  exactly as at level `15`. Completing the square turns them into
  `4c² = N² + 7e⁴` with `N = 2S² − 11e²` and `8c² = M² + 7e⁴` with
  `M = 4S² − 11e²`, i.e. into the `2`-isogenous curve `Y² = X³ + 22X² − 7X`
  (`b′ = a² − 4b = 121 − 128 = −7`).

THE SECOND DESCENT, mapped out 2026-07-26. Factor `A² − N² = 7e⁴` as
`(A − N)(A + N) = 7e⁴` with `A = 2c`. The gcd of the two factors divides `7`,
and `7` itself is impossible (it forces `7 ∣ S` and `7 ∣ e`), so the factors are
coprime; writing `e = mn` the coprime split into fourth powers gives exactly two
branches, and the even-`e` case of quartic A and both cases of quartic B run
into the SAME two branches after dividing out powers of `2`:

* **Branch (i)** yields `X² = −m⁴ + 22m²n² + 7n⁴` — the `d′ = −1` homogeneous
  space of the isogenous curve. **This branch is DEAD by a pure congruence**,
  and it is the one genuinely new ingredient: for coprime `m`, `n`, split on
  parity — `m`, `n` both odd gives `X² ≡ 12 (mod 16)`, impossible; `m` odd,
  `n` even gives `X² ≡ 3 (mod 4)`, impossible; `m` even, `n` odd gives
  `X² ≡ 7 (mod 8)`, impossible. (No coprime solution with `|m|, |n| ≤ 400`,
  PARI 2026-07-26 — consistent, as it must be.)
* **Branch (ii)** yields `X² = n⁴ + 22m²n² − 7m⁴`, whose ONLY coprime solutions
  up to `400` are `(m, n) = (0, 1)` and `(1, 1)` (PARI 2026-07-26) — i.e. it
  must be shown that `m = 0 ∨ m² = n²`. This is the surviving hard branch and it
  is where the infinite descent lives: completing the square gives
  `(n² + 11m²)² − X² = 128m⁴`, and stripping the powers of `2` leads to
  `n² = 8a⁴ − 11a²b² + 4b⁴` with `ab = m`, a strictly smaller instance. That is
  precisely the shape of `MazurLevel15.concordant_aux`, whose well-founded
  recursion on `x² + y²` is the template to copy.

So the remaining work is: the level-`15` integral bookkeeping transported
(`sq_or_two_sq` with `32` in place of `16`, and `split_gcd`), the mod-`16`
congruence above, and ONE well-founded descent on branch (ii). Note those
helpers currently live in `Fermat/FLT/FreyCurve/MazurTorsion.lean`, which is
DOWNSTREAM of this file, so they have to be restated here (or hoisted) rather
than imported. -/
theorem curve14a4_rational_T (T W : ℚ) (h : W ^ 2 = T ^ 3 - 11 * T ^ 2 + 32 * T) :
    T = 0 ∨ T = 4 ∨ T = 8 :=
  MazurLevel14.T_trichotomy h

/-- **The five affine rational points of `14a4`, UNCONDITIONALLY** (PROVEN
2026-07-26 over `curve14a4_rational_T`): the affine rational points of
`y² + xy + y = x³ − x` are exactly `(1,−2)`, `(0,−1)`, `(−1,0)`, `(0,0)`,
`(1,0)`. Together with the point at infinity these are the six elements of
`14a4(ℚ) ≅ ℤ/6`.

This is the hypothesis-free form, and it is what `curve14a4_finite` consumes —
`curve14a4_points` below is the same statement with the (now unused) finiteness
hypothesis its consumer supplies positionally. Splitting the two is what breaks
the circle: finiteness is DERIVED from this enumeration rather than assumed for
it.

THE PROOF. `Nonsingular` gives `Equation`, i.e. `y² + xy + y = x³ − x`; the
scaled coordinates `T = 4x + 4`, `W = 8y + 4x + 4` satisfy
`W² = T³ − 11T² + 32T` (the identity is `64 ×` the curve equation), so
`curve14a4_rational_T` pins `x ∈ {−1, 0, 1}`. At each the equation becomes a
quadratic in `y` that factors over `ℚ`: `y² = 0`, `y(y + 1) = 0`,
`y(y + 2) = 0`. Note the `x`-coordinates take only THREE values, and that is
the form in which the consumer uses this lemma.

All six points are CUSPS of `X_1(14)` (`φ(14)/2 = 3` rational cusps, plus the
three conjugate ones that happen to be rational on this model). That is the
input to `x1_fourteen_no_rational_point`, whose proof exhibits the birational
map from the plane sextic and checks that each of the three `x`-values pulls
back to `d ∈ {0, 1}` — the two excluded degenerate loci. -/
theorem curve14a4_affine_points (x y : ℚ)
    (h : curve14a4.toAffine.Nonsingular x y) :
    (x, y) = ((1 : ℚ), (-2 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((-1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (0 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) := by
  have heq : curve14a4.toAffine.Equation x y := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curve14a4] at heq
  have key : (8 * y + 4 * x + 4) ^ 2
      = (4 * x + 4) ^ 3 - 11 * (4 * x + 4) ^ 2 + 32 * (4 * x + 4) := by
    linear_combination 64 * heq
  rcases curve14a4_rational_T _ _ key with hT | hT | hT
  · have hx : x = -1 := by linarith
    subst hx
    have hy : y ^ 2 = 0 := by linarith [heq]
    have hy0 : y = 0 := pow_eq_zero_iff (n := 2) (a := y) (by norm_num) |>.mp hy
    subst hy0; simp
  · have hx : x = 0 := by linarith
    subst hx
    have hy : y * (y + 1) = 0 := by linarith [heq]
    rcases mul_eq_zero.mp hy with h0 | h0
    · subst h0; simp
    · have hy1 : y = -1 := by linarith
      subst hy1; simp
  · have hx : x = 1 := by linarith
    subst hx
    have hy : y * (y + 2) = 0 := by linarith [heq]
    rcases mul_eq_zero.mp hy with h0 | h0
    · subst h0; simp
    · have hy2 : y = -2 := by linarith
      subst hy2; simp

/-- **The five affine rational points of `14a4`** (PROVEN 2026-07-26 over
`curve14a4_rational_T`; was a sorry leaf) — the form the consumer calls, with
the finiteness hypothesis it supplies.

**The finiteness hypothesis is now UNUSED** (hence `_hfin`), and that is a
strengthening rather than a gap: the enumeration is no longer conditional on a
Mordell–Weil input. It is kept in the signature only because
`x1_fourteen_no_rational_point` in `Fermat/FLT/FreyCurve/TateNormalForm.lean`
passes `curve14a4_finite` positionally. All content is in
`curve14a4_affine_points`. -/
theorem curve14a4_points (_hfin : Finite curve14a4.toAffine.Point) (x y : ℚ)
    (h : curve14a4.toAffine.Nonsingular x y) :
    (x, y) = ((1 : ℚ), (-2 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((-1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (0 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) :=
  curve14a4_affine_points x y h

/-- **`14a4(ℚ)` is finite** (PROVEN 2026-07-26 over `curve14a4_affine_points`, hence
over `curve14a4_rational_T` alone).

This USED to be the descent conclusion "finitely generated (Mordell–Weil) plus
torsion (rank `0`) gives finite", and it no longer is: with the five affine
points enumerated outright, finiteness is immediate from mathlib's
`nonsingularPointEquiv`, which identifies `E(ℚ)` with `WithZero` of the set of
nonsingular affine pairs. **So `mordellWeil` is NOT consumed at `14a4`** —
contrary to what this file's earlier docstrings claimed, it is not load-bearing
here. It remains load-bearing at `11a3`, where the enumeration is still a leaf.
-/
theorem curve14a4_finite : Finite curve14a4.toAffine.Point := by
  have hsub : {xy : ℚ × ℚ | curve14a4.toAffine.Nonsingular xy.1 xy.2} ⊆
      ({((1 : ℚ), (-2 : ℚ)), (0, -1), (-1, 0), (0, 0), (1, 0)} : Set (ℚ × ℚ)) := by
    rintro ⟨x, y⟩ hxy
    have hx := curve14a4_affine_points x y hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hfin : {xy : ℚ × ℚ | curve14a4.toAffine.Nonsingular xy.1 xy.2}.Finite :=
    Set.Finite.subset (Set.toFinite _) hsub
  haveI : Finite {xy : ℚ × ℚ // curve14a4.toAffine.Nonsingular xy.1 xy.2} := hfin
  haveI : Finite (WithZero {xy : ℚ × ℚ // curve14a4.toAffine.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option _))
  exact Finite.of_equiv _ curve14a4.toAffine.nonsingularPointEquiv.symm

/-- **Rank `0` for `14a4`** (PROVEN 2026-07-26 over `curve14a4_finite`; was a
sorry leaf), in the concrete form that carries the content: every rational
point of `y² + xy + y = x³ − x` is a torsion point.

Classically this is a descent by the rational `2`-isogeny that `14a4` admits;
here it is a corollary of the full enumeration instead, since a finite group is
a torsion group. `RankBound(E) = 0` with proof flag `true` (Magma 2026-07-26,
untrusted searcher). Kubert, "Universal bounds on the torsion of elliptic
curves" (Proc. LMS 33, 1976); Ligozat; subsumed in Mazur 1977, Thm 8.

Stated as `AddMonoid.IsTorsion` rather than as `rank = 0` for the same reason
as `curve11a3_isTorsion`: there is no rank function here to state the latter
against. -/
theorem curve14a4_isTorsion : AddMonoid.IsTorsion curve14a4.toAffine.Point :=
  haveI := curve14a4_finite
  fun g => isOfFinAddOrder_of_finite g

end WeierstrassCurve
