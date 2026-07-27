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
`gcd` argument. The alternative is a `2`-descent over the cubic field
`ℚ[s]/(s³ − 2s² + 2)` of discriminant `−44`. **Corrected 2026-07-27**: that
field's class group and unit group were recorded here as the obstruction, and
they are not — `ℤ[s] = 𝓞_K` exactly (index `1`) and `h = 1` follows from one
mathlib lemma. The real obstruction is the HEIGHT descent, which both routes
need. See the `MazurLevel11` section docstring for the computed evidence, and
`curve11a3_rational_points`.

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

## ROUTING CORRECTION, 2026-07-27 — the class group is CHEAP; the expensive
## ingredient is the HEIGHT DESCENT, and it was hiding behind a deleted leaf

The previous version of this docstring named two routes and said of route (ii),
the `2`-descent over the cubic field `ℚ[s]/(s³ − 2s² + 2)`, that it "needs that
field's class group and unit group … neither is in the pin". **Both halves of
that are wrong**, and the error mattered: it pointed successive owners at the
cheapest ingredient and away from the expensive one. Computed evidence (PARI/GP
as an untrusted searcher; every number below is independently checkable):

* `f = X³ − 2X² + 2` is irreducible with `poldisc f = −44`, and the FIELD
  discriminant is also `−44`, so the index `[𝓞_K : ℤ[s]]` is `1` — i.e.
  **`ℤ[s] = 𝓞_K` exactly**, no index correction anywhere.
* **`h(K) = 1`**, and it follows from a single mathlib lemma already in the pin:
  `NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`
  (`Mathlib/NumberTheory/NumberField/ClassNumber.lean:200`). At
  `finrank ℚ K = 3`, `nrComplexPlaces K = 1` its bound reads
  `|discr K| < (2·(π/4)·(3³/3!))² = 81π²/16 ≈ 49.96`, and `44 < 49.96`; the
  only real input is `π > 2.949`. Worked precedent for the whole pattern:
  `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean:35,50`.
* The identification `𝓞_K = ℤ[s]` is likewise in reach: `−44 = −2²·11` and
  `11² ∤ 44`, so only `p = 2` needs clearing, and **`X³ − 2X² + 2` is Eisenstein
  at `2`**. The two lemmas are `Algebra.discr_mul_isIntegral_mem_adjoin`
  (`Mathlib/RingTheory/Discriminant.lean:257`) and
  `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt`
  (`Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean:363`), combined
  exactly as `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean:94` does.
* Units: rank `1`, torsion `{±1}`, fundamental unit `ε = −s² + s + 1`, certified
  by the single `ring` identity `ε·(s − 1) = 1`; `N(ε) = −1`, `N(s − 1) = −1`.

**What is actually expensive is FINITE GENERATION — the height theory.** A
complete `2`-descent here yields only `E(ℚ)/2E(ℚ) = 0`, and since `E[2]` is
irreducible over `ℚ` so that `E(ℚ)[2] = 0`, that says exactly that `E(ℚ)` is
*uniquely `2`-divisible*. That is true of `ℤ/5` — and equally true of `ℚ`, of
`ℤ[1/2]`, and of every uniquely `2`-divisible infinite group. The `5`-isogeny
route stalls in the same place: it yields `E(ℚ) = 5E(ℚ)` and no more. So route
(ii) is **not** cheaper than route (i); *both* need Mordell–Weil or a hand-rolled
height descent, and this module deleted its `mordellWeil` leaf on the ground
that it was "not on the critical path". It is on the critical path. The two
descent-map facts previously recorded are still correct and still useful — the
`5`-isogeny map is `α(P) = f(P)` for `f = y + x² + xy` with
`div(f) = 5(T) − 5(O)`, whose dual side `H¹(ℚ, ℤ/5)` is cyclic quintic
extensions unramified outside `{5, 11}` and does need class field theory — but
neither of them is where the difficulty lives.

## THE DESCENT, MADE EXPLICIT (2026-07-27): the `2`-covering IS the curve, so
## the descent witness is literally a HALVING

Writing the `2`-descent out in coordinates turns it into pure integer algebra,
and the result is much more concrete than the prose above suggested. Since
`X³ − 4X² + 16` is the minimal polynomial of `2s`, the cubic factors over `K` as

    U³ − 4U² + 16 = (U − 2s)(U² + (2s − 4)U + (4s² − 8s)),

so a coprime integral point `(p, e, n)` has `N(β) = n²` for `β = p − 2s·e²`, and
the descent map is `P ↦ β mod (K*)²`. Because `E(ℚ) ≅ ℤ/5` is `2`-divisible,
every `β` is a square — and a square root of an algebraic integer is an
algebraic integer, so `β = δ²` with `δ = a + bs + cs² ∈ 𝓞_K = ℤ[s]`. Expanding
with `s³ = 2s² − 2` and `s⁴ = 4s² − 2s − 4` and comparing coefficients gives the
system carried by `exists_halving_witness` below:

    1  :  a² − 4c² − 4bc = p
    s  :  2ab − 2c²      = −2e²      i.e.  e² = c² − ab
    s² :  b² + 2ac + 4bc + 4c² = 0

Both known points sit in this trivial class, with explicit witnesses:
`(s² − 2)² = −2s` gives `(p, e) = (0, 1)`, and `(s² − 2s)² = 4 − 2s` gives
`(p, e) = (4, 1)`. That is *why* the finite-generation gap bites — every
NONTRIVIAL square class dies locally, and the surviving trivial class is the
`2`-covering `P ↦ 2P` of `E` by itself.

The last sentence is literally true, and it is the useful discovery here. Put
`m = b + 2c`; the `s²`-equation is exactly `2ac = −m²`, and eliminating `a`
turns the other two into (both PROVEN below, by `linear_combination`)

    2c·e² = m³ − 2c·m² + 2c³        and        4c²·p = m⁴ + 16c⁴ − 16m·c³.

Dividing the first by `c³` and setting `U' = 2m/c`, `W' = 4e/c` gives
`W'² = U'³ − 4U'² + 16` — **the same curve**. Eliminating `m` and `c` between
the two identities gives

    U  =  (U'⁴ − 128U' + 256) / (4(U'³ − 4U'² + 16))  =  (U'⁴ − 128U' + 256)/(4W'²),

which is precisely the standard duplication formula for
`y² = x³ + a₂x² + a₄x + a₆` at `(a₂, a₄, a₆) = (−4, 0, 16)`. So the witness
`(a, b, c)` is a halving: `(U', W')` is a point `Q` with `2Q = P`. The two known
witnesses realise the two `5`-torsion duplications `2·(4, 4) = (0, 4)` and
`2·(0, 4) = (4, −4)`, and `trivial_ascends` below PROVES both of them from the
integer identities.

WHAT REMAINS is therefore exactly one quantitative statement, `halving_descends`
below: the halving strictly decreases the height. The standard resultant bound
gives it for all but boundedly many points, and the bound is small:

    Res(X⁴ − 128X + 256, X³ − 4X² + 16) = 2¹⁶·11² = 7929856,

so `H(2Q) ≥ H(Q)⁴/7929856`, and a counterexample of minimal height must satisfy
`max(|p|, e²)³ ≤ 7929856`, i.e. `max(|p|, e²) ≤ 199` and `e ≤ 14`. That base
case is genuinely finite and small — a few thousand coprime pairs — rather than
the exponentially large check one would fear from a crude height inequality.
Whoever takes these two leaves should expect: `exists_halving_witness` from the
`ℤ[s]` arithmetic above (PID + units + the local conditions killing the
nontrivial classes), and `halving_descends` from the resultant bound plus that
bounded base case. -/

namespace MazurLevel11

/-- **THE `2`-DESCENT LEAF at level `11`** (sorry leaf, 2026-07-27): every
coprime integral point of `W² = U³ − 4U² + 16` lies in the TRIVIAL square class
of the `2`-division field, written out in coordinates.

MEANING. With `s³ = 2s² − 2` the cubic factors as `U³ − 4U² + 16 =
(U − 2s)(U² + (2s − 4)U + 4s² − 8s)` over `K = ℚ(s)`, and a coprime integral
point has `N(p − 2s·e²) = n²`. This statement says `p − 2s·e² = (a + bs + cs²)²`
in `𝓞_K = ℤ[s]`: the three components of that equation, after reducing with
`s³ = 2s² − 2` and `s⁴ = 4s² − 2s − 4`, are exactly the three conclusions below
(constant, `s`, and `s²` coefficients respectively, the `s`-one divided by `−2`).

WHY IT IS TRUE, and it is: the `2`-descent map `P ↦ (x(P) − 2s) mod (K*)²` is a
homomorphism with kernel `2E(ℚ)`, and `E(ℚ) ≅ ℤ/5` is `2`-divisible, so every
`β = p − 2s·e²` is a square in `K*`; a square root of an algebraic integer is an
algebraic integer, so the root lies in `𝓞_K`, which is `ℤ[s]` on the nose
(index `1`, see the section docstring). Note `β ≠ 0`, since `N(β) = 0` would
force `e = 0`. Both known points have explicit witnesses:
`(a, b, c) = (−2, 0, 1)` for `(p, e) = (0, 1)` and `(0, −2, 1)` for `(4, 1)`.

HOW TO PROVE IT. This is the leaf that consumes the cubic field's arithmetic,
and the section docstring records that all of it is within reach of the pin:
`𝓞_K = ℤ[s]` from `Algebra.discr_mul_isIntegral_mem_adjoin` plus the Eisenstein
lemma (`X³ − 2X² + 2` is Eisenstein at `2`, and `2` is the only prime needing
clearing), then `h(K) = 1` from
`NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` since
`44 < 81π²/16`, then the unit group `⟨−1⟩ × ⟨ε⟩` with `ε = −s² + s + 1`, and
finally the local conditions that kill the nontrivial square classes. Nothing
here needs heights or finite generation — that burden is entirely in
`halving_descends`. -/
theorem exists_halving_witness {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 - 4 * p ^ 2 * e ^ 2 + 16 * e ^ 6) :
    ∃ a b c : ℤ, b ^ 2 + 2 * a * c + 4 * b * c + 4 * c ^ 2 = 0 ∧
      p = a ^ 2 - 4 * c ^ 2 - 4 * b * c ∧ e ^ 2 = c ^ 2 - a * b := sorry

/-- **THE HEIGHT LEAF at level `11`** (sorry leaf, 2026-07-27): the halving
supplied by `exists_halving_witness` strictly decreases the height, except at
the two points that are actually there.

The hypotheses are the halving in its eliminated form: `m` and `c` satisfy the
`2`-covering `2c·e² = m³ − 2c·m² + 2c³` and the `x`-relation
`4c²·p = m⁴ + 16c⁴ − 16m·c³` (both PROVEN from the witness in
`integral_leaf_aux`), and `(p', e', n')` is the coprime integral model of the
halved point `U' = 2m/c`, pinned by the cross-multiplied `2m·e'² = p'·c`.

**THIS IS THE FINITE-GENERATION CONTENT OF LEVEL `11`**, and it is the only
place it appears. Everything else in this section is either the `2`-descent
(`exists_halving_witness`) or proven algebra. A `2`-descent alone gives
`E(ℚ)/2E(ℚ) = 0`, i.e. unique `2`-divisibility, which is satisfied by infinite
groups too; it is exactly this height inequality that converts that into
finiteness. So do not expect to remove this leaf by strengthening the descent.

HOW TO PROVE IT, quantitatively. Eliminating `m, c` shows the halving is the
duplication `U = (U'⁴ − 128U' + 256)/(4(U'³ − 4U'² + 16))`, and

    Res(X⁴ − 128X + 256, X³ − 4X² + 16) = 2¹⁶·11² = 7929856,

so the numerator and denominator share only divisors of that resultant and
`H(2Q) ≥ H(Q)⁴/7929856`. If the height did NOT drop we would get
`H(P)³ ≤ 7929856`, i.e. `max(|p|, e²) ≤ 199` and hence `e ≤ 14` — a base case of
a few thousand coprime pairs, each decided by whether `p³ − 4p²e² + 16e⁶` is a
square. That is the whole proof, and both halves of it are elementary; the
work is in the coprimality bookkeeping for the resultant bound.

The two exceptional disjuncts are not slack: the halvings of the two real points
INCREASE the height (`(p, e) = (0, 1)` has `m = 2`, `c = 1`, and halves to
`U' = 4`; `(4, 1)` has `m = 0` and halves to `U' = 0`), because both are
`5`-torsion. `trivial_ascends` handles them on the way back up. -/
theorem halving_descends {p e n m c p' e' n' : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 - 4 * p ^ 2 * e ^ 2 + 16 * e ^ 6) (hc : c ≠ 0)
    (hcov : 2 * c * e ^ 2 = m ^ 3 - 2 * c * m ^ 2 + 2 * c ^ 3)
    (hpm : 4 * c ^ 2 * p = m ^ 4 + 16 * c ^ 4 - 16 * m * c ^ 3)
    (he' : 0 < e') (hcop' : IsCoprime p' e')
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (hn' : n' ^ 2 = p' ^ 3 - 4 * p' ^ 2 * e' ^ 2 + 16 * e' ^ 6) :
    (p = 0 ∧ e = 1) ∨ (p = 4 ∧ e = 1) ∨
      p'.natAbs + (e' ^ 2).natAbs < p.natAbs + (e ^ 2).natAbs := sorry

/-- **The halving witness has `c ≠ 0`** (PROVEN 2026-07-27). If `c = 0` the
quadric `b² + 2ac + 4bc + 4c² = 0` collapses to `b² = 0`, and then
`e² = c² − ab = 0` contradicts `0 < e`. Equivalently: `δ = a + bs + cs²` with
`c = 0` cannot have `δ²` in the `ℤ`-span of `1` and `s` unless `δ ∈ ℤ`. -/
theorem witness_c_ne_zero {e a b c : ℤ} (he : 0 < e)
    (hq : b ^ 2 + 2 * a * c + 4 * b * c + 4 * c ^ 2 = 0)
    (hee : e ^ 2 = c ^ 2 - a * b) : c ≠ 0 := by
  rintro rfl
  have hb2 : b ^ 2 = 0 := by linear_combination hq
  have hb : b = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb2
  have hz : e ^ 2 = 0 := by rw [hee, hb]; ring
  have he0 : e = 0 := pow_eq_zero_iff two_ne_zero |>.mp hz
  omega

/-- **Triviality of the halved point ascends** (PROVEN 2026-07-27): if the
halving `Q` of `P` is one of the two known points, so is `P`.

This is the duplication of the rational `5`-torsion, done in integers. If
`(p', e') = (0, 1)` then `U' = 0`, so `m = 0`, and the two covering identities
collapse to `p = 4c²`, `e² = c²`; coprimality of `p` and `e` then forces `e = 1`
and `p = 4`. If `(p', e') = (4, 1)` then `U' = 4`, so `m = 2c`, and they
collapse to `p = 0`, `e² = c²`, forcing `e = 1`. These are exactly
`2·(0, 4) = (4, −4)` and `2·(4, 4) = (0, 4)` on `W² = U³ − 4U² + 16`, which is
what makes the descent below close upwards instead of merely producing ever
smaller solutions. -/
theorem trivial_ascends {p e m c p' e' : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (hc : c ≠ 0)
    (hcov : 2 * c * e ^ 2 = m ^ 3 - 2 * c * m ^ 2 + 2 * c ^ 3)
    (hpm : 4 * c ^ 2 * p = m ^ 4 + 16 * c ^ 4 - 16 * m * c ^ 3)
    (hcross : 2 * m * e' ^ 2 = p' * c)
    (h' : (p' = 0 ∧ e' = 1) ∨ (p' = 4 ∧ e' = 1)) :
    (p = 0 ∧ e = 1) ∨ (p = 4 ∧ e = 1) := by
  have hc2 : (4 * c ^ 2 : ℤ) ≠ 0 := by positivity
  have h2c : (2 * c : ℤ) ≠ 0 := by simpa using hc
  rcases h' with ⟨hp', he'1⟩ | ⟨hp', he'1⟩
  · -- `U' = 0`, so `m = 0`, and `P` is the point with `U = 4`.
    subst hp'; subst he'1
    have hm : m = 0 := by linarith [hcross]
    subst hm
    have hpv : p = 4 * c ^ 2 := by
      refine mul_left_cancel₀ hc2 ?_
      linear_combination hpm
    have hev : e ^ 2 = c ^ 2 := by
      refine mul_left_cancel₀ h2c ?_
      linear_combination hcov
    have hdvd : e ∣ p := by
      rw [hpv, ← hev]
      exact ⟨4 * e, by ring⟩
    have hu : IsUnit e := hcop.isUnit_of_dvd' hdvd dvd_rfl
    have he1 : e = 1 := by
      rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
    refine Or.inr ⟨?_, he1⟩
    rw [hpv, ← hev, he1]; ring
  · -- `U' = 4`, so `m = 2c`, and `P` is the point with `U = 0`.
    subst hp'; subst he'1
    have hm : m = 2 * c := by linarith [hcross]
    subst hm
    have hpv : p = 0 := by
      refine mul_left_cancel₀ hc2 ?_
      linear_combination hpm
    have hev : e ^ 2 = c ^ 2 := by
      refine mul_left_cancel₀ h2c ?_
      linear_combination hcov
    have hu : IsUnit e := by
      rw [hpv] at hcop
      exact isCoprime_zero_left.mp hcop
    have he1 : e = 1 := by
      rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega
    exact Or.inl ⟨hpv, he1⟩

/-- **The infinite descent at level `11`** (PROVEN 2026-07-27 over the two
leaves above), by strong induction on `|p| + e²` — the same shape as
`MazurLevel14.h1_classification`, `MazurLevel15.concordant_both_aux` and
`QuarticDescent.not_isSquare_form`.

Each step: take the halving witness `(a, b, c)`; `c ≠ 0`; put `m = b + 2c`, for
which the `s²`-equation reads `2ac = −m²` and eliminating `a` gives the two
covering identities by `linear_combination`; pass to the rational point
`(U', W') = (2m/c, 4e/c)` of the SAME curve and take its coprime integral model
with `RationalPointDescent.exists_int_model`; then either `P` is one of the two
known points, or the model is strictly smaller and the induction hypothesis
applies to it — and `trivial_ascends` carries the conclusion back up. -/
theorem integral_leaf_aux : ∀ N : ℕ, ∀ p e n : ℤ, p.natAbs + (e ^ 2).natAbs ≤ N →
    0 < e → IsCoprime p e → n ^ 2 = p ^ 3 - 4 * p ^ 2 * e ^ 2 + 16 * e ^ 6 →
    (p = 0 ∧ e = 1) ∨ (p = 4 ∧ e = 1) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro p e n hN he hcop h
    obtain ⟨a, b, c, hq, hp, hee⟩ := exists_halving_witness he hcop h
    have hc : c ≠ 0 := witness_c_ne_zero he hq hee
    set m : ℤ := b + 2 * c with hm
    have hcov : 2 * c * e ^ 2 = m ^ 3 - 2 * c * m ^ 2 + 2 * c ^ 3 := by
      rw [hm]; linear_combination (2 * c) * hee - b * hq
    have hpm : 4 * c ^ 2 * p = m ^ 4 + 16 * c ^ 4 - 16 * m * c ^ 3 := by
      rw [hm]; linear_combination (4 * c ^ 2) * hp + (2 * a * c - (b + 2 * c) ^ 2) * hq
    have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hcovQ : 2 * (c : ℚ) * (e : ℚ) ^ 2 =
        (m : ℚ) ^ 3 - 2 * (c : ℚ) * (m : ℚ) ^ 2 + 2 * (c : ℚ) ^ 3 := by
      exact_mod_cast hcov
    have hV : (4 * (e : ℚ) / (c : ℚ)) ^ 2 =
        (2 * (m : ℚ) / (c : ℚ)) ^ 3 + ((-4 : ℤ) : ℚ) * (2 * (m : ℚ) / (c : ℚ)) ^ 2
          + ((0 : ℤ) : ℚ) * (2 * (m : ℚ) / (c : ℚ)) + ((16 : ℤ) : ℚ) := by
      push_cast
      field_simp
      linear_combination (8 : ℚ) * hcovQ
    obtain ⟨p', e', n', he', hcop', hTeq, hn'0⟩ :=
      RationalPointDescent.exists_int_model (A := -4) (B := 0) (C := 16) hV
    have hn' : n' ^ 2 = p' ^ 3 - 4 * p' ^ 2 * e' ^ 2 + 16 * e' ^ 6 := by
      linear_combination hn'0
    have he'Q : ((e' : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hcross : 2 * m * e' ^ 2 = p' * c := by
      have hQ : 2 * (m : ℚ) * (e' : ℚ) ^ 2 = (p' : ℚ) * (c : ℚ) := by
        field_simp at hTeq
        linarith [hTeq]
      exact_mod_cast hQ
    rcases halving_descends he hcop h hc hcov hpm he' hcop' hcross hn' with h1 | h1 | hlt
    · exact Or.inl h1
    · exact Or.inr h1
    · exact trivial_ascends he hcop hc hcov hpm hcross
        (ih (p'.natAbs + (e' ^ 2).natAbs) (lt_of_lt_of_le hlt hN) p' e' n' le_rfl he' hcop' hn')

/-- **THE level-`11` statement** (PROVEN 2026-07-27 from
`exists_halving_witness` and `halving_descends`): the only coprime integral
points of the monic model `W² = U³ − 4U² + 16` of `11a3` are `(p, e) = (0, 1)`
and `(4, 1)`, i.e. `U = 0` and `U = 4`.

This is `curve11a3_rational_points` with the Weierstrass API and the rationals
removed; the reduction is PROVEN (`U_dichotomy`), so this statement carries the
ENTIRE arithmetic content of level `11` — rank `0` for one explicit curve.

DECOMPOSED 2026-07-27. It is no longer a leaf: it is the infinite descent
`integral_leaf_aux` over exactly two open statements, which are the two genuinely
different mathematical inputs and are attackable independently —
`exists_halving_witness` (the `2`-descent over `ℤ[s]`: PID, units, and the local
conditions) and `halving_descends` (the height inequality, which is where the
finite-generation content actually lives). See the section docstring for the
computed evidence behind that split, including why the earlier routing note —
which called the cubic field's class group the obstruction — was wrong.

Verified by exhaustive search (`|p| < 6000`, `1 ≤ e < 260`, coprime): `(0, 1)`
and `(4, 1)` are the only solutions, so the statement is true as written.

CHECKED EXTERNALLY (PARI/GP, untrusted searcher — not a proof).
`ellinit([0,-1,1,0,0])` gives `disc = −11`, conductor `11`,
`j = −4096/11`; `ellrank` returns rank `0` with matching lower and upper
bounds, i.e. it *proves* rank `0`; `elltors` returns `ℤ/5`; and
`ellratpoints(E, 1000)` returns exactly the four affine points. On the monic
model `ellinit([0,-4,0,0,16])` the four affine points are `(0, ±4)`, `(4, ±4)`,
and `ellmul` confirms the two duplications used by `trivial_ascends`. -/
theorem integral_leaf {p e n : ℤ} (he : 0 < e) (hcop : IsCoprime p e)
    (h : n ^ 2 = p ^ 3 - 4 * p ^ 2 * e ^ 2 + 16 * e ^ 6) :
    (p = 0 ∧ e = 1) ∨ (p = 4 ∧ e = 1) :=
  integral_leaf_aux (p.natAbs + (e ^ 2).natAbs) p e n le_rfl he hcop h

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

DECOMPOSED 2026-07-26, and again 2026-07-27. The Weierstrass-API layer was
stripped off first, leaving the pure integer statement
`MazurLevel11.integral_leaf`; that statement is now itself PROVEN, as an
infinite descent (`MazurLevel11.integral_leaf_aux`) over exactly two open
statements — `MazurLevel11.exists_halving_witness` (the `2`-descent over
`ℤ[s]`) and `MazurLevel11.halving_descends` (the height inequality). See the
`MazurLevel11` section docstring.

Note the sentence above — "finite generation alone never yields rank `0`, so it
was never the hard half" — is true but was read the wrong way round when
`mordellWeil` was deleted. Finite generation is not SUFFICIENT, and it is also
not OPTIONAL: a complete `2`-descent here gives only `E(ℚ)/2E(ℚ) = 0`, which
without a height theory is satisfied by infinite groups. The height content is
now explicit and named, in `MazurLevel11.halving_descends`. -/
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

/-- A nonnegative coprime factor of a fourth power is a fourth power. -/
theorem pow_four_of_coprime {A B C : ℤ} (hcop : IsCoprime A B) (h : A * B = C ^ 4)
    (hA : 0 ≤ A) : ∃ a : ℤ, 0 ≤ a ∧ A = a ^ 4 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcop h
  rcases Int.associated_iff.mp hd with h1 | h1
  · refine ⟨|d|, abs_nonneg d, ?_⟩
    rw [← h1, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  · have hd0 : d ^ 4 ≤ 0 := by rw [h1]; omega
    have hdz : d = 0 := by
      by_contra hne
      exact absurd hd0 (not_le.mpr (by positivity))
    refine ⟨0, le_refl _, ?_⟩
    rw [hdz] at h1
    norm_num at h1
    omega

/-- `7` is prime in `ℤ`.  Stated by hand rather than by `norm_num` because this
module does not import `Mathlib.Tactic.NormNum.Prime`, so `norm_num` reduces
`Prime (7 : ℤ)` to `Nat.Prime 7` and then stalls. -/
theorem prime_seven_int : Prime (7 : ℤ) := by
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num]
  exact Nat.prime_iff_prime_int.mp (by decide)

theorem sq_eq_of_pow_four_eq {t s : ℤ} (h : t ^ 4 = s ^ 4) : t ^ 2 = s ^ 2 := by
  have h1 : (t ^ 2 - s ^ 2) * (t ^ 2 + s ^ 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · nlinarith [sq_nonneg t, sq_nonneg s]

/-- `x² + y² ≡ 0 (mod 4)` forces both `x` and `y` even. -/
theorem two_dvd_of_four_dvd_sq_add_sq {x y : ℤ} (h : (4 : ℤ) ∣ x ^ 2 + y ^ 2) :
    (2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' x <;> obtain ⟨b, hb | hb⟩ := Int.even_or_odd' y <;>
      subst ha <;> subst hb <;> obtain ⟨k, hk⟩ := h
  · exact ⟨⟨a, by ring⟩, ⟨b, by ring⟩⟩
  · exfalso; have h1 : (4 : ℤ) ∣ 1 := ⟨k - (a ^ 2 + b ^ 2 + b), by linarith [hk]⟩; omega
  · exfalso; have h1 : (4 : ℤ) ∣ 1 := ⟨k - (a ^ 2 + a + b ^ 2), by linarith [hk]⟩; omega
  · exfalso; have h1 : (4 : ℤ) ∣ 2 := ⟨k - (a ^ 2 + a + b ^ 2 + b), by linarith [hk]⟩; omega

/-- Splitting `A · B = p · C⁴` with `A`, `B` coprime and nonnegative and `p` prime. -/
theorem split_prime_pow_four {A B C p : ℤ} (hp : Prime p) (hppos : 0 < p) (hcop : IsCoprime A B)
    (h : A * B = p * C ^ 4) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ IsCoprime m n ∧ A = p * m ^ 4 ∧ B = n ^ 4 ∧
        (m * n) ^ 2 = C ^ 2) ∨
    (∃ m n : ℤ, 0 ≤ m ∧ 0 ≤ n ∧ IsCoprime m n ∧ A = n ^ 4 ∧ B = p * m ^ 4 ∧
        (m * n) ^ 2 = C ^ 2) := by
  have hpd : p ∣ A * B := ⟨C ^ 4, h⟩
  rcases hp.dvd_or_dvd hpd with hpa | hpb
  · left
    obtain ⟨A', hA'⟩ := hpa
    have hp0 : p ≠ 0 := hp.ne_zero
    have hAB : A' * B = C ^ 4 := by
      have : p * (A' * B) = p * C ^ 4 := by rw [← h, hA']; ring
      exact mul_left_cancel₀ hp0 this
    have hcop' : IsCoprime A' B := hcop.of_isCoprime_of_dvd_left ⟨p, by rw [hA']; ring⟩
    have hA'0 : 0 ≤ A' := by
      by_contra hcon
      push Not at hcon
      have hneg : p * A' < 0 := mul_neg_of_pos_of_neg hppos hcon
      rw [← hA'] at hneg
      omega
    obtain ⟨m, hm0, hm⟩ := pow_four_of_coprime hcop' hAB hA'0
    obtain ⟨n, hn0, hn⟩ := pow_four_of_coprime hcop'.symm (by rw [mul_comm]; exact hAB) hB
    refine ⟨m, n, hm0, hn0, ?_, by rw [hA', hm], hn, ?_⟩
    · exact (hcop'.of_isCoprime_of_dvd_left ⟨m ^ 3, by rw [hm]; ring⟩).symm.of_isCoprime_of_dvd_left
        ⟨n ^ 3, by rw [hn]; ring⟩ |>.symm
    · exact sq_eq_of_pow_four_eq (by rw [mul_pow, ← hm, ← hn, hAB])
  · right
    obtain ⟨B', hB'⟩ := hpb
    have hp0 : p ≠ 0 := hp.ne_zero
    have hAB : A * B' = C ^ 4 := by
      have : p * (A * B') = p * C ^ 4 := by rw [← h, hB']; ring
      exact mul_left_cancel₀ hp0 this
    have hcop' : IsCoprime A B' := hcop.of_isCoprime_of_dvd_right ⟨p, by rw [hB']; ring⟩
    have hB'0 : 0 ≤ B' := by
      by_contra hcon
      push Not at hcon
      have hneg : p * B' < 0 := mul_neg_of_pos_of_neg hppos hcon
      rw [← hB'] at hneg
      omega
    obtain ⟨n, hn0, hn⟩ := pow_four_of_coprime hcop' hAB hA
    obtain ⟨m, hm0, hm⟩ := pow_four_of_coprime hcop'.symm (by rw [mul_comm]; exact hAB) hB'0
    refine ⟨m, n, hm0, hn0, ?_, hn, by rw [hB', hm], ?_⟩
    · exact ((hcop'.of_isCoprime_of_dvd_left ⟨n ^ 3, by rw [hn]; ring⟩).symm.of_isCoprime_of_dvd_left
        ⟨m ^ 3, by rw [hm]; ring⟩)
    · exact sq_eq_of_pow_four_eq (by rw [mul_pow, ← hm, ← hn, mul_comm, hAB])

/-- The square of an odd integer is `8k + 1`. -/
theorem odd_sq_eq {M : ℤ} (h : ¬ (2 : ℤ) ∣ M) : ∃ k : ℤ, M ^ 2 = 8 * k + 1 := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' M
  · exact absurd ⟨a, ha⟩ h
  · obtain ⟨t, ht⟩ : ∃ t : ℤ, a ^ 2 + a = 2 * t := by
      rcases Int.even_or_odd' a with ⟨c, hc | hc⟩
      · exact ⟨2 * c ^ 2 + c, by rw [hc]; ring⟩
      · exact ⟨2 * c ^ 2 + 3 * c + 1, by rw [hc]; ring⟩
    exact ⟨t, by rw [ha]; linear_combination 4 * ht⟩

/-- Squares modulo `8`, together with the parity each residue forces. -/
theorem sq_form (x : ℤ) :
    ((2 : ℤ) ∣ x ∧ ∃ k, x ^ 2 = 8 * k) ∨ ((2 : ℤ) ∣ x ∧ ∃ k, x ^ 2 = 8 * k + 4) ∨
      (¬ (2 : ℤ) ∣ x ∧ ∃ k, x ^ 2 = 8 * k + 1) := by
  rcases Int.even_or_odd' x with ⟨a, ha | ha⟩
  · subst ha
    rcases Int.even_or_odd' a with ⟨b, hb | hb⟩
    · exact Or.inl ⟨⟨a, rfl⟩, 2 * b ^ 2, by rw [hb]; ring⟩
    · exact Or.inr (Or.inl ⟨⟨a, rfl⟩, 2 * b ^ 2 + 2 * b, by rw [hb]; ring⟩)
  · subst ha
    obtain ⟨k, hk⟩ := odd_sq_eq (M := 2 * a + 1) (by omega)
    exact Or.inr (Or.inr ⟨by omega, k, hk⟩)

/-- `8 ∣ n² − 11m²` forces both `m` and `n` even. -/
theorem eight_dvd_imp_even {m n : ℤ} (h : (8 : ℤ) ∣ n ^ 2 - 11 * m ^ 2) :
    (2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ n := by
  obtain ⟨K, hK⟩ := h
  rcases sq_form m with ⟨hm2, s, hs⟩ | ⟨hm2, s, hs⟩ | ⟨hm2, s, hs⟩ <;>
    rcases sq_form n with ⟨hn2, t, ht⟩ | ⟨hn2, t, ht⟩ | ⟨hn2, t, ht⟩ <;>
      rw [hs, ht] at hK <;>
        first
          | exact ⟨hm2, hn2⟩
          | (exfalso; omega)

/-- **The `d′ = 7` homogeneous space of the isogenous curve is empty.**
`X² = 7m⁴ + 22m²n² − n⁴` has no coprime solution: completing the square the other
way gives `X² + (n² − 11m²)² = 128m⁴`, three rounds of "a sum of two squares
divisible by `4` has both terms even" force `8 ∣ n² − 11m²`, and that forces
`m`, `n` both even. -/
theorem h7_dead {m n X : ℤ} (hcop : IsCoprime m n)
    (h : X ^ 2 = 7 * m ^ 4 + 22 * m ^ 2 * n ^ 2 - n ^ 4) : False := by
  have key : X ^ 2 + (n ^ 2 - 11 * m ^ 2) ^ 2 = 128 * m ^ 4 := by linear_combination h
  obtain ⟨⟨X1, hX1⟩, ⟨Y1, hY1⟩⟩ :=
    two_dvd_of_four_dvd_sq_add_sq (x := X) (y := n ^ 2 - 11 * m ^ 2) ⟨32 * m ^ 4, by linarith⟩
  rw [hX1, hY1] at key
  have key1 : X1 ^ 2 + Y1 ^ 2 = 32 * m ^ 4 := by
    have h' : 4 * (X1 ^ 2 + Y1 ^ 2) = 4 * (32 * m ^ 4) := by linear_combination key
    linarith
  obtain ⟨⟨X2, hX2⟩, ⟨Y2, hY2⟩⟩ :=
    two_dvd_of_four_dvd_sq_add_sq (x := X1) (y := Y1) ⟨8 * m ^ 4, by linarith⟩
  rw [hX2, hY2] at key1
  have key2 : X2 ^ 2 + Y2 ^ 2 = 8 * m ^ 4 := by
    have h' : 4 * (X2 ^ 2 + Y2 ^ 2) = 4 * (8 * m ^ 4) := by linear_combination key1
    linarith
  obtain ⟨-, ⟨Y3, hY3⟩⟩ :=
    two_dvd_of_four_dvd_sq_add_sq (x := X2) (y := Y2) ⟨2 * m ^ 4, by linarith⟩
  have h8 : (8 : ℤ) ∣ n ^ 2 - 11 * m ^ 2 := ⟨Y3, by rw [hY1, hY2, hY3]; ring⟩
  obtain ⟨hm, hn⟩ := eight_dvd_imp_even h8
  exact absurd (hcop.isUnit_of_dvd' hm hn) (by norm_num [Int.isUnit_iff])

theorem isCoprime_of_no_common_prime {A B : ℤ}
    (h : ∀ p : ℤ, Prime p → p ∣ A → p ∣ B → False) : IsCoprime A B := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hd : (p : ℤ) ∣ (Int.gcd A B : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  exact h p (Nat.prime_iff_prime_int.mp hp) (hd.trans (Int.gcd_dvd_left A B))
    (hd.trans (Int.gcd_dvd_right A B))

theorem two_dvd_of_prime_dvd_two {p : ℤ} (hp : Prime p) (h : p ∣ 2) : (2 : ℤ) ∣ p := by
  have h1 : p.natAbs ∣ 2 := by simpa using Int.natAbs_dvd_natAbs.mpr h
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
  · exact absurd (Int.isUnit_iff.mpr (by simpa using Int.natAbs_eq_iff.mp h2)) hp.not_unit
  · rcases Int.natAbs_eq_iff.mp h2 with h3 | h3 <;> rw [h3] <;> norm_num

/-- Two odd integers have even sum and even difference. -/
theorem two_dvd_sub_add_of_odd {x y : ℤ} (hx : ¬ (2 : ℤ) ∣ x) (hy : ¬ (2 : ℤ) ∣ y) :
    (2 : ℤ) ∣ (x - y) ∧ (2 : ℤ) ∣ (x + y) := by
  obtain ⟨a, ha | ha⟩ := Int.even_or_odd' x
  · exact absurd ⟨a, ha⟩ hx
  · obtain ⟨b, hb | hb⟩ := Int.even_or_odd' y
    · exact absurd ⟨b, hb⟩ hy
    · exact ⟨⟨a - b, by rw [ha, hb]; ring⟩, ⟨a + b + 1, by rw [ha, hb]; ring⟩⟩

theorem not_two_dvd_of_odd_form {x t : ℤ} (h : x = 2 * t + 1) : ¬ (2 : ℤ) ∣ x := by
  rintro ⟨c, rfl⟩; omega

theorem not_two_dvd_of_sq_odd_form {x t : ℤ} (h : x ^ 2 = 2 * t + 1) : ¬ (2 : ℤ) ∣ x := by
  rintro ⟨c, rfl⟩
  have h1 : (2 : ℤ) ∣ 1 := ⟨2 * c ^ 2 - t, by linarith [h]⟩
  omega

/-- **The shared coprimality step.** If `A · B = c · g⁴` with `c` prime, then any prime
dividing both `A` and `B` also divides `g` — because it divides `c` only if `c` and it are
associated, and then `c²  ∣ c g⁴` gives `c ∣ g⁴`. -/
theorem isCoprime_split {A B c g : ℤ} (hcp : Prime c) (hAB : A * B = c * g ^ 4)
    (hkey : ∀ p : ℤ, Prime p → ¬ p ∣ (2 : ℤ) → p ∣ A → p ∣ B → p ∣ g → False)
    (hodd : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B)) : IsCoprime A B := by
  apply isCoprime_of_no_common_prime
  intro p hp hpA hpB
  have hp2 : ¬ p ∣ (2 : ℤ) := by
    intro hd
    have h2p := two_dvd_of_prime_dvd_two hp hd
    exact hodd ⟨h2p.trans hpA, h2p.trans hpB⟩
  refine hkey p hp hp2 hpA hpB ?_
  have hdvd : p ∣ c * g ^ 4 := hAB ▸ hpA.mul_right _
  rcases hp.dvd_or_dvd hdvd with h1 | h1
  · obtain ⟨d, hd⟩ := h1
    have hdu : IsUnit d := (hcp.irreducible.isUnit_or_isUnit hd).resolve_left hp.not_unit
    have hpsq : p * p ∣ p * (d * g ^ 4) := by
      rw [show p * (d * g ^ 4) = c * g ^ 4 by rw [hd]; ring, ← hAB]
      exact mul_dvd_mul hpA hpB
    have hpd : p ∣ d * g ^ 4 := (mul_dvd_mul_iff_left hp.ne_zero).mp hpsq
    have hg4 : p ∣ g ^ 4 := by
      rcases Int.isUnit_iff.mp hdu with h2 | h2 <;> rw [h2] at hpd <;> simpa using hpd
    exact hp.dvd_of_dvd_pow hg4
  · exact hp.dvd_of_dvd_pow h1

/-- **`G₁` with `e` odd descends to `H₁`.**  From `Q² = S⁴ − 11S²e² + 32e⁴` and `2 ∤ e`,
the coprime factorisation of `4Q² − (2S² − 11e²)² = 7e⁴` gives `mn = ±e` with
`(2S)² = n⁴ + 22m²n² − 7m⁴`. -/
theorem step_G1_oddE {S e Q : ℤ} (hcop : IsCoprime S e) (he : ¬ (2 : ℤ) ∣ e)
    (h : Q ^ 2 = S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4) :
    ∃ m n : ℤ, IsCoprime m n ∧ (m * n) ^ 2 = e ^ 2 ∧
      (2 * S) ^ 2 = n ^ 4 + 22 * m ^ 2 * n ^ 2 - 7 * m ^ 4 := by
  have hq2 : |Q| ^ 2 = Q ^ 2 := sq_abs Q
  have hq0 : 0 ≤ |Q| := abs_nonneg Q
  have he0 : e ≠ 0 := by rintro rfl; exact he ⟨0, by ring⟩
  have he4 : (0 : ℤ) < e ^ 4 := by positivity
  set A := 2 * |Q| - (2 * S ^ 2 - 11 * e ^ 2) with hAdef
  set B := 2 * |Q| + (2 * S ^ 2 - 11 * e ^ 2) with hBdef
  have hsum : A + B = 4 * |Q| := by rw [hAdef, hBdef]; ring
  have hdiff : B - A = 2 * (2 * S ^ 2 - 11 * e ^ 2) := by rw [hAdef, hBdef]; ring
  have hprod : A * B = 7 * e ^ 4 := by rw [hAdef, hBdef]; linear_combination 4 * hq2 + 4 * h
  have hAodd : ¬ (2 : ℤ) ∣ A := by
    rw [hAdef]
    rintro ⟨c, hc⟩
    have h1 : (2 : ℤ) ∣ 11 * e ^ 2 := ⟨c - |Q| + S ^ 2, by linarith [hc]⟩
    exact he (Int.prime_two.dvd_of_dvd_pow
      ((Int.prime_two.dvd_or_dvd h1).resolve_left (by decide)))
  have hABpos : 0 < A ∧ 0 < B := by
    have hpos : 0 < A * B := by rw [hprod]; linarith
    rcases mul_pos_iff.mp hpos with h1 | h1
    · exact h1
    · exact absurd hsum (by linarith [h1.1, h1.2, hq0])
  have hcopAB : IsCoprime A B := by
    refine isCoprime_split prime_seven_int hprod (fun p hp hp2 hpA hpB hpe => ?_)
      (fun hc => hAodd hc.1)
    have hpU : p ∣ 2 * S ^ 2 - 11 * e ^ 2 :=
      (hp.dvd_or_dvd (hdiff ▸ dvd_sub hpB hpA)).resolve_left hp2
    have hpS : p ∣ S := by
      obtain ⟨c, hc⟩ := hpU
      obtain ⟨d, hd⟩ := hpe
      rw [hd] at hc
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd
        (⟨c + 11 * p * d ^ 2, by linear_combination hc⟩ : p ∣ 2 * S ^ 2)).resolve_left hp2)
    exact hp.not_unit (hcop.isUnit_of_dvd' hpS hpe)
  rcases split_prime_pow_four prime_seven_int (by norm_num) hcopAB hprod
      hABpos.1.le hABpos.2.le with h1 | h1
  · obtain ⟨m, n, -, -, hmn, hA7, hBn, hmne⟩ := h1
    rw [hAdef] at hA7; rw [hBdef] at hBn
    exact ⟨m, n, hmn, hmne, by linear_combination hBn - hA7 - 22 * hmne⟩
  · obtain ⟨m, n, -, -, hmn, hAn, hB7, hmne⟩ := h1
    rw [hAdef] at hAn; rw [hBdef] at hB7
    exact (h7_dead hmn (X := 2 * S) (by linear_combination hB7 - hAn - 22 * hmne)).elim

/-- **`G₁` with `e` even descends to `H₁`.**  Here `S` is odd, `e = 2f`, and the
factorisation of `Q² − (S² − 22f²)² = 28f⁴` gives `mn = ±f` with
`S² = n⁴ + 22m²n² − 7m⁴`. -/
theorem step_G1_evenE {S e Q : ℤ} (hcop : IsCoprime S e) (he : (2 : ℤ) ∣ e) (he0 : e ≠ 0)
    (h : Q ^ 2 = S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4) :
    ∃ m n : ℤ, IsCoprime m n ∧ (2 * (m * n)) ^ 2 = e ^ 2 ∧
      S ^ 2 = n ^ 4 + 22 * m ^ 2 * n ^ 2 - 7 * m ^ 4 := by
  have hS : ¬ (2 : ℤ) ∣ S := fun hd => Int.prime_two.not_unit (hcop.isUnit_of_dvd' hd he)
  obtain ⟨f, hf⟩ : ∃ f, e = 2 * f := he
  have hf0 : f ≠ 0 := by rintro rfl; exact he0 (by rw [hf]; ring)
  have hf4 : (0 : ℤ) < f ^ 4 := by positivity
  obtain ⟨k, hk⟩ := odd_sq_eq hS
  have h' : Q ^ 2 = S ^ 4 - 44 * S ^ 2 * f ^ 2 + 512 * f ^ 4 := by rw [h, hf]; ring
  have hQodd : ¬ (2 : ℤ) ∣ Q := not_two_dvd_of_sq_odd_form
    (t := 32 * k ^ 2 + 8 * k - 176 * k * f ^ 2 - 22 * f ^ 2 + 256 * f ^ 4)
    (by rw [h', show S ^ 4 = (S ^ 2) ^ 2 by ring, hk]; ring)
  have hQaodd : ¬ (2 : ℤ) ∣ |Q| := fun hd => hQodd ((dvd_abs 2 Q).mp hd)
  have hUodd : ¬ (2 : ℤ) ∣ (S ^ 2 - 22 * f ^ 2) :=
    not_two_dvd_of_odd_form (t := 4 * k - 11 * f ^ 2) (by rw [hk]; ring)
  obtain ⟨⟨A, hAdef⟩, ⟨B, hBdef⟩⟩ := two_dvd_sub_add_of_odd hQaodd hUodd
  have hsum : A + B = |Q| := by linarith [hAdef, hBdef]
  have hu1 : S ^ 2 - 22 * f ^ 2 = B - A := by linarith [hAdef, hBdef]
  have hq0 : 0 ≤ |Q| := abs_nonneg Q
  have hprod : A * B = 7 * f ^ 4 := by
    have h4 : (2 * A) * (2 * B) = 28 * f ^ 4 := by
      rw [← hAdef, ← hBdef]; linear_combination sq_abs Q + h'
    linarith [h4]
  have hABpos : 0 < A ∧ 0 < B := by
    have hpos : 0 < A * B := by rw [hprod]; linarith
    rcases mul_pos_iff.mp hpos with h1 | h1
    · exact h1
    · exact absurd hsum (by linarith [h1.1, h1.2, hq0])
  have hnot2 : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact hQaodd ⟨c + d, by linarith [hsum, hc, hd]⟩
  have hcopAB : IsCoprime A B := by
    refine isCoprime_split prime_seven_int hprod (fun p hp hp2 hpA hpB hpf => ?_) hnot2
    have hpU : p ∣ S ^ 2 - 22 * f ^ 2 := hu1 ▸ dvd_sub hpB hpA
    have hpS : p ∣ S := by
      obtain ⟨c, hc⟩ := hpU
      obtain ⟨d, hd⟩ := hpf
      rw [hd] at hc
      exact hp.dvd_of_dvd_pow (⟨c + 22 * p * d ^ 2, by linear_combination hc⟩ : p ∣ S ^ 2)
    exact hp.not_unit (hcop.isUnit_of_dvd' hpS (hf ▸ hpf.mul_left 2))
  rcases split_prime_pow_four prime_seven_int (by norm_num) hcopAB hprod
      hABpos.1.le hABpos.2.le with h1 | h1
  · obtain ⟨m, n, -, -, hmn, hA7, hBn, hmnf⟩ := h1
    exact ⟨m, n, hmn, by rw [hf]; linear_combination 4 * hmnf,
      by linear_combination hu1 + hBn - hA7 - 22 * hmnf⟩
  · obtain ⟨m, n, -, -, hmn, hAn, hB7, hmnf⟩ := h1
    exact (h7_dead hmn (X := S) (by linear_combination hu1 + hB7 - hAn - 22 * hmnf)).elim

/-- **`G₈` with `a` odd descends to `H₁`.**  `16q² − (8b² − 11a²)² = 7a⁴`. -/
theorem step_G8_odd {a b q : ℤ} (hcop : IsCoprime a b) (ha : ¬ (2 : ℤ) ∣ a)
    (h : q ^ 2 = 8 * a ^ 4 - 11 * a ^ 2 * b ^ 2 + 4 * b ^ 4) :
    ∃ m n : ℤ, IsCoprime m n ∧ (m * n) ^ 2 = a ^ 2 ∧
      (4 * b) ^ 2 = n ^ 4 + 22 * m ^ 2 * n ^ 2 - 7 * m ^ 4 := by
  have hq2 : |q| ^ 2 = q ^ 2 := sq_abs q
  have hq0 : 0 ≤ |q| := abs_nonneg q
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by ring⟩
  have ha4 : (0 : ℤ) < a ^ 4 := by positivity
  set A := 4 * |q| - (8 * b ^ 2 - 11 * a ^ 2) with hAdef
  set B := 4 * |q| + (8 * b ^ 2 - 11 * a ^ 2) with hBdef
  have hsum : A + B = 8 * |q| := by rw [hAdef, hBdef]; ring
  have hdiff : B - A = 2 * (8 * b ^ 2 - 11 * a ^ 2) := by rw [hAdef, hBdef]; ring
  have hprod : A * B = 7 * a ^ 4 := by rw [hAdef, hBdef]; linear_combination 16 * hq2 + 16 * h
  have hAodd : ¬ (2 : ℤ) ∣ A := by
    rw [hAdef]
    rintro ⟨c, hc⟩
    have h1 : (2 : ℤ) ∣ 11 * a ^ 2 := ⟨c - 2 * |q| + 4 * b ^ 2, by linarith [hc]⟩
    exact ha (Int.prime_two.dvd_of_dvd_pow
      ((Int.prime_two.dvd_or_dvd h1).resolve_left (by decide)))
  have hABpos : 0 < A ∧ 0 < B := by
    have hpos : 0 < A * B := by rw [hprod]; linarith
    rcases mul_pos_iff.mp hpos with h1 | h1
    · exact h1
    · exact absurd hsum (by linarith [h1.1, h1.2, hq0])
  have hcopAB : IsCoprime A B := by
    refine isCoprime_split prime_seven_int hprod (fun p hp hp2 hpA hpB hpa => ?_)
      (fun hc => hAodd hc.1)
    have hpw : p ∣ 8 * b ^ 2 - 11 * a ^ 2 :=
      (hp.dvd_or_dvd (hdiff ▸ dvd_sub hpB hpA)).resolve_left hp2
    have hpb : p ∣ b := by
      obtain ⟨c, hc⟩ := hpw
      obtain ⟨d, hd⟩ := hpa
      rw [hd] at hc
      have h8 : p ∣ 8 * b ^ 2 := ⟨c + 11 * p * d ^ 2, by linear_combination hc⟩
      rcases hp.dvd_or_dvd h8 with h9 | h9
      · exact absurd (hp.dvd_of_dvd_pow (show p ∣ (2 : ℤ) ^ 3 by simpa using h9)) hp2
      · exact hp.dvd_of_dvd_pow h9
    exact hp.not_unit (hcop.isUnit_of_dvd' hpa hpb)
  rcases split_prime_pow_four prime_seven_int (by norm_num) hcopAB hprod
      hABpos.1.le hABpos.2.le with h1 | h1
  · obtain ⟨m, n, -, -, hmn, hA7, hBn, hmna⟩ := h1
    rw [hAdef] at hA7; rw [hBdef] at hBn
    exact ⟨m, n, hmn, hmna, by linear_combination hBn - hA7 - 22 * hmna⟩
  · obtain ⟨m, n, -, -, hmn, hAn, hB7, hmna⟩ := h1
    rw [hAdef] at hAn; rw [hBdef] at hB7
    exact (h7_dead hmn (X := 4 * b) (by linear_combination hB7 - hAn - 22 * hmna)).elim

/-- **`H₁` with `M`, `N` both odd descends to `G₈`.**
`(M² + 11N²)² − Z² = 128N⁴`; here `M² + 11N² = 4p′` with `p′` odd and `4 ∣ Z`, and the
coprime split of `p′² − z² = 8N⁴` gives `ab = ±N` with `M² = 8a⁴ − 11a²b² + 4b⁴`. -/
theorem step_H1_odd {M N Z : ℤ} (hcop : IsCoprime M N) (hM : ¬ (2 : ℤ) ∣ M)
    (hN : ¬ (2 : ℤ) ∣ N) (hN0 : N ≠ 0)
    (h : Z ^ 2 = M ^ 4 + 22 * M ^ 2 * N ^ 2 - 7 * N ^ 4) :
    ∃ a b : ℤ, IsCoprime a b ∧ (a * b) ^ 2 = N ^ 2 ∧
      M ^ 2 = 8 * a ^ 4 - 11 * a ^ 2 * b ^ 2 + 4 * b ^ 4 := by
  obtain ⟨k, hk⟩ := odd_sq_eq hM
  obtain ⟨l, hl⟩ := odd_sq_eq hN
  have hN2 : (0 : ℤ) < N ^ 2 := by positivity
  have hN4 : (0 : ℤ) < N ^ 4 := by positivity
  have hP : M ^ 2 + 11 * N ^ 2 = 4 * (2 * k + 22 * l + 3) := by rw [hk, hl]; ring
  have hp'odd : ¬ (2 : ℤ) ∣ (2 * k + 22 * l + 3) :=
    not_two_dvd_of_odd_form (t := k + 11 * l + 1) (by ring)
  have hZ16 : Z ^ 2 = 16 * (4 * k ^ 2 + 88 * k * l - 28 * l ^ 2 + 12 * k + 4 * l + 1) := by
    rw [h, show M ^ 4 = (M ^ 2) ^ 2 by ring, show N ^ 4 = (N ^ 2) ^ 2 by ring, hk, hl]; ring
  obtain ⟨z, hz⟩ : (4 : ℤ) ∣ Z := (Int.pow_dvd_pow_iff two_ne_zero).mp
    ⟨4 * k ^ 2 + 88 * k * l - 28 * l ^ 2 + 12 * k + 4 * l + 1, by rw [hZ16]; ring⟩
  have hz2 : z ^ 2 = 4 * k ^ 2 + 88 * k * l - 28 * l ^ 2 + 12 * k + 4 * l + 1 := by
    have h16 : 16 * z ^ 2 = 16 * (4 * k ^ 2 + 88 * k * l - 28 * l ^ 2 + 12 * k + 4 * l + 1) := by
      rw [← hZ16, hz]; ring
    linarith
  have hzodd : ¬ (2 : ℤ) ∣ z := not_two_dvd_of_sq_odd_form
    (t := 2 * k ^ 2 + 44 * k * l - 14 * l ^ 2 + 6 * k + 2 * l) (by rw [hz2]; ring)
  have hkey : (2 * k + 22 * l + 3) ^ 2 - z ^ 2 = 8 * N ^ 4 := by
    have hPZ : (M ^ 2 + 11 * N ^ 2) ^ 2 - Z ^ 2 = 128 * N ^ 4 := by linear_combination -h
    rw [hP, hz] at hPZ
    have h16 : 16 * ((2 * k + 22 * l + 3) ^ 2 - z ^ 2) = 16 * (8 * N ^ 4) := by
      linear_combination hPZ
    linarith
  obtain ⟨⟨A, hAdef⟩, ⟨B, hBdef⟩⟩ := two_dvd_sub_add_of_odd hp'odd hzodd
  have hsum : A + B = 2 * k + 22 * l + 3 := by linarith [hAdef, hBdef]
  have hprod : A * B = 2 * N ^ 4 := by
    have h4 : (2 * A) * (2 * B) = 8 * N ^ 4 := by rw [← hAdef, ← hBdef]; linear_combination hkey
    linarith [h4]
  have hp'pos : 0 < 2 * k + 22 * l + 3 := by linarith [hP, sq_nonneg M, hN2]
  have hABpos : 0 < A ∧ 0 < B := by
    have hpos : 0 < A * B := by rw [hprod]; linarith
    rcases mul_pos_iff.mp hpos with h1 | h1
    · exact h1
    · exact absurd hsum (by linarith [h1.1, h1.2, hp'pos])
  have hnot2 : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact hp'odd ⟨c + d, by linarith [hsum, hc, hd]⟩
  have hcopAB : IsCoprime A B := by
    refine isCoprime_split Int.prime_two hprod (fun p hp _ hpA hpB hpN => ?_) hnot2
    obtain ⟨c, hc⟩ : p ∣ (2 * k + 22 * l + 3) := hsum ▸ dvd_add hpA hpB
    obtain ⟨d, hd⟩ := id hpN
    rw [hd] at hP
    exact hp.not_unit (hcop.isUnit_of_dvd'
      (hp.dvd_of_dvd_pow (⟨4 * c - 11 * p * d ^ 2, by linear_combination hP + 4 * hc⟩ :
        p ∣ M ^ 2)) hpN)
  rcases split_prime_pow_four Int.prime_two (by norm_num) hcopAB hprod
      hABpos.1.le hABpos.2.le with h1 | h1
  · obtain ⟨a, b, -, -, hab, hA2, hBn, habN⟩ := h1
    exact ⟨a, b, hab, habN, by linear_combination hP - 4 * hsum + 4 * hA2 + 4 * hBn + 11 * habN⟩
  · obtain ⟨a, b, -, -, hab, hAn, hB2, habN⟩ := h1
    exact ⟨a, b, hab, habN, by linear_combination hP - 4 * hsum + 4 * hAn + 4 * hB2 + 11 * habN⟩

/-- **`H₁` with `M`, `N` of opposite parity descends to `G₁`.**
Then `M² + 11N²` and `Z` are both odd, `A·B = 2·(2N)⁴` splits as `{32μ⁴, n⁴}` with `n`
odd and `μn = ±N`, and `M² = n⁴ − 11n²μ² + 32μ⁴`. -/
theorem step_H1_mixed {M N Z : ℤ} (hcop : IsCoprime M N) (hpar : (2 : ℤ) ∣ M ∨ (2 : ℤ) ∣ N)
    (hN0 : N ≠ 0) (h : Z ^ 2 = M ^ 4 + 22 * M ^ 2 * N ^ 2 - 7 * N ^ 4) :
    ∃ n mu : ℤ, IsCoprime n mu ∧ (n * mu) ^ 2 = N ^ 2 ∧ ¬ (2 : ℤ) ∣ n ∧
      M ^ 2 = n ^ 4 - 11 * n ^ 2 * mu ^ 2 + 32 * mu ^ 4 := by
  have hN2 : (0 : ℤ) < N ^ 2 := by positivity
  have hodd : ¬ (2 : ℤ) ∣ (M ^ 2 + 11 * N ^ 2) ∧ ¬ (2 : ℤ) ∣ Z := by
    rcases hpar with hM | hN
    · have hNodd : ¬ (2 : ℤ) ∣ N := fun hd =>
        Int.prime_two.not_unit (hcop.isUnit_of_dvd' hM hd)
      obtain ⟨M', hM'⟩ := hM
      obtain ⟨l, hl⟩ := odd_sq_eq hNodd
      exact ⟨not_two_dvd_of_odd_form (t := 2 * M' ^ 2 + 44 * l + 5) (by rw [hM', hl]; ring),
        not_two_dvd_of_sq_odd_form
          (t := 8 * M' ^ 4 + 352 * M' ^ 2 * l + 44 * M' ^ 2 - 224 * l ^ 2 - 56 * l - 4)
          (by rw [h, hM', show N ^ 4 = (N ^ 2) ^ 2 by ring, hl]; ring)⟩
    · have hModd : ¬ (2 : ℤ) ∣ M := fun hd =>
        Int.prime_two.not_unit (hcop.isUnit_of_dvd' hd hN)
      obtain ⟨N', hN'⟩ := hN
      obtain ⟨k, hk⟩ := odd_sq_eq hModd
      exact ⟨not_two_dvd_of_odd_form (t := 4 * k + 22 * N' ^ 2) (by rw [hN', hk]; ring),
        not_two_dvd_of_sq_odd_form
          (t := 32 * k ^ 2 + 8 * k + 352 * k * N' ^ 2 + 44 * N' ^ 2 - 56 * N' ^ 4)
          (by rw [h, hN', show M ^ 4 = (M ^ 2) ^ 2 by ring, hk]; ring)⟩
  obtain ⟨⟨A, hAdef⟩, ⟨B, hBdef⟩⟩ := two_dvd_sub_add_of_odd hodd.1 hodd.2
  have hsum : A + B = M ^ 2 + 11 * N ^ 2 := by linarith [hAdef, hBdef]
  have hprod : A * B = 2 * (2 * N) ^ 4 := by
    have h4 : (2 * A) * (2 * B) = 4 * (2 * (2 * N) ^ 4) := by
      rw [← hAdef, ← hBdef]; linear_combination -h
    linarith [h4]
  have hgpos : (0 : ℤ) < 2 * (2 * N) ^ 4 := by positivity
  have hABpos : 0 < A ∧ 0 < B := by
    have hpos : 0 < A * B := by rw [hprod]; linarith
    rcases mul_pos_iff.mp hpos with h1 | h1
    · exact h1
    · exact absurd hsum (by linarith [h1.1, h1.2, sq_nonneg M, hN2])
  have hnot2 : ¬ ((2 : ℤ) ∣ A ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact hodd.1 ⟨c + d, by linarith [hsum, hc, hd]⟩
  have hcopAB : IsCoprime A B := by
    refine isCoprime_split Int.prime_two hprod (fun p hp hp2 hpA hpB hpg => ?_) hnot2
    have hpN : p ∣ N := (hp.dvd_or_dvd hpg).resolve_left hp2
    obtain ⟨c, hc⟩ : p ∣ (M ^ 2 + 11 * N ^ 2) := hsum ▸ dvd_add hpA hpB
    obtain ⟨d, hd⟩ := id hpN
    rw [hd] at hc
    exact hp.not_unit (hcop.isUnit_of_dvd'
      (hp.dvd_of_dvd_pow (⟨c - 11 * p * d ^ 2, by linear_combination hc⟩ : p ∣ M ^ 2)) hpN)
  have hfin : ∀ m n : ℤ, IsCoprime m n → ¬ (2 : ℤ) ∣ n → (m * n) ^ 2 = (2 * N) ^ 2 →
      ∃ mu : ℤ, m = 2 * mu ∧ (n * mu) ^ 2 = N ^ 2 ∧ IsCoprime n mu := by
    intro m n hmn hnodd hmnN
    have h2mn : (2 : ℤ) ∣ m * n := Int.prime_two.dvd_of_dvd_pow
      (⟨2 * N ^ 2, by linear_combination hmnN⟩ : (2 : ℤ) ∣ (m * n) ^ 2)
    obtain ⟨mu, hmu⟩ := (Int.prime_two.dvd_or_dvd h2mn).resolve_right hnodd
    refine ⟨mu, hmu, ?_, (hmn.of_isCoprime_of_dvd_left ⟨2, by rw [hmu]; ring⟩).symm⟩
    have h4 : 4 * (n * mu) ^ 2 = 4 * N ^ 2 := by rw [hmu] at hmnN; linear_combination hmnN
    linarith
  rcases split_prime_pow_four Int.prime_two (by norm_num) hcopAB hprod
      hABpos.1.le hABpos.2.le with h1 | h1
  · obtain ⟨m, n, -, -, hmn, hA2, hBn, hmnN⟩ := h1
    have hnodd : ¬ (2 : ℤ) ∣ n := fun hd =>
      hnot2 ⟨⟨m ^ 4, hA2⟩, hBn ▸ dvd_pow hd (by norm_num)⟩
    obtain ⟨mu, hmu, hnmu, hcnmu⟩ := hfin m n hmn hnodd hmnN
    have hA32 : A = 32 * mu ^ 4 := by rw [hA2, hmu]; ring
    exact ⟨n, mu, hcnmu, hnmu, hnodd, by linear_combination -hsum + hA32 + hBn + 11 * hnmu⟩
  · obtain ⟨m, n, -, -, hmn, hAn, hB2, hmnN⟩ := h1
    have hnodd : ¬ (2 : ℤ) ∣ n := fun hd =>
      hnot2 ⟨hAn ▸ dvd_pow hd (by norm_num), ⟨m ^ 4, hB2⟩⟩
    obtain ⟨mu, hmu, hnmu, hcnmu⟩ := hfin m n hmn hnodd hmnN
    have hB32 : B = 32 * mu ^ 4 := by rw [hB2, hmu]; ring
    exact ⟨n, mu, hcnmu, hnmu, hnodd, by linear_combination -hsum + hAn + hB32 + 11 * hnmu⟩

theorem one_le_sq {x : ℤ} (h : x ≠ 0) : 1 ≤ x ^ 2 := by
  rcases lt_trichotomy x 0 with h1 | h1 | h1
  · nlinarith
  · exact absurd h1 h
  · nlinarith

theorem natAbs_lt_of_sq_lt {x y : ℤ} (h : x ^ 2 < y ^ 2) : x.natAbs < y.natAbs := by
  by_contra hc
  push Not at hc
  have h1 : (y.natAbs : ℤ) ≤ (x.natAbs : ℤ) := by exact_mod_cast hc
  rw [← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs] at h1
  nlinarith [sq_abs x, sq_abs y, abs_nonneg y]

/-- **THE MASTER DESCENT.**  The only coprime solutions of the `d′ = 1` homogeneous space
`Z² = M⁴ + 22M²N² − 7N⁴` of `Y² = X³ + 22X² − 7X` are `(M, N) = (±1, 0)` and `(±1, ±1)`.

Proved by strong induction on `|N|`.  If `M` and `N` have opposite parity the space
descends to `G₁` at `(n₁, μ)` with `n₁` odd, and `G₁` either dies mod `8` (`μ` odd) or
descends again to a strictly smaller `H₁`; either way that branch is empty.  If `M` and
`N` are both odd the space descends to `G₈` and then back to `H₁` at `(n, m)` with
`|m| · |n| · |b| = |N|`, which is a strict decrease unless `|nb| = 1` — and in that case
the equation itself forces `m² = 1`. -/
theorem h1_classification : ∀ nn : ℕ, ∀ M N Z : ℤ, N.natAbs ≤ nn → IsCoprime M N →
    Z ^ 2 = M ^ 4 + 22 * M ^ 2 * N ^ 2 - 7 * N ^ 4 → M ^ 2 = 1 ∧ N ^ 2 ≤ 1 := by
  intro nn
  induction nn using Nat.strong_induction_on with
  | _ nn IH =>
  intro M N Z hle hcop h
  rcases eq_or_ne N 0 with rfl | hN0
  · refine ⟨?_, by norm_num⟩
    rcases Int.isUnit_iff.mp (hcop.isUnit_of_dvd' dvd_rfl (dvd_zero M)) with h1 | h1 <;>
      rw [h1] <;> norm_num
  by_cases hpar : (2 : ℤ) ∣ M ∨ (2 : ℤ) ∣ N
  · exfalso
    obtain ⟨n1, mu, hcnmu, hnmu, hn1odd, heq⟩ := step_H1_mixed hcop hpar hN0 h
    have hn10 : n1 ≠ 0 := by rintro rfl; exact hn1odd ⟨0, by ring⟩
    have hmu0 : mu ≠ 0 := by
      rintro rfl
      exact hN0 (by nlinarith [hnmu, sq_nonneg N])
    by_cases hmu2 : (2 : ℤ) ∣ mu
    · obtain ⟨m2, n2, hc2, he2, heq2⟩ := step_G1_evenE hcnmu hmu2 hmu0 heq
      have hm20 : m2 ≠ 0 := by
        rintro rfl
        exact hmu0 (by nlinarith [he2, sq_nonneg mu])
      have hn20 : n2 ≠ 0 := by
        rintro rfl
        exact hmu0 (by nlinarith [he2, sq_nonneg mu])
      have hN2eq : N ^ 2 = 4 * (n1 ^ 2 * n2 ^ 2) * m2 ^ 2 := by
        linear_combination -hnmu - n1 ^ 2 * he2
      have hlt : m2.natAbs < N.natAbs := by
        refine natAbs_lt_of_sq_lt ?_
        rw [hN2eq]
        nlinarith [one_le_sq hn10, one_le_sq hn20, one_le_sq hm20]
      obtain ⟨hn2sq, hm2sq⟩ :=
        IH m2.natAbs (lt_of_lt_of_le hlt hle) n2 m2 n1 le_rfl hc2.symm (by linear_combination heq2)
      have hm2e : m2 ^ 2 = 1 := le_antisymm hm2sq (one_le_sq hm20)
      rw [show n2 ^ 4 = (n2 ^ 2) ^ 2 by ring, show m2 ^ 4 = (m2 ^ 2) ^ 2 by ring,
        hn2sq, hm2e] at heq2
      obtain ⟨kk, hkk⟩ := odd_sq_eq hn1odd
      omega
    · obtain ⟨k, hk⟩ := odd_sq_eq hn1odd
      obtain ⟨l, hl⟩ := odd_sq_eq hmu2
      have h6 : M ^ 2 = 8 * (8 * k ^ 2 - 88 * k * l + 256 * l ^ 2 - 9 * k + 53 * l + 2) + 6 := by
        rw [heq, show n1 ^ 4 = (n1 ^ 2) ^ 2 by ring, show mu ^ 4 = (mu ^ 2) ^ 2 by ring, hk, hl]
        ring
      rcases sq_form M with ⟨-, s, hs⟩ | ⟨-, s, hs⟩ | ⟨-, s, hs⟩ <;> omega
  · push Not at hpar
    obtain ⟨a, b, hab, habN, heq⟩ := step_H1_odd hcop hpar.1 hpar.2 hN0 h
    have haodd : ¬ (2 : ℤ) ∣ a := fun hd => hpar.2 (Int.prime_two.dvd_of_dvd_pow
      (habN ▸ (dvd_pow (hd.mul_right b) two_ne_zero) : (2 : ℤ) ∣ N ^ 2))
    have hbodd : ¬ (2 : ℤ) ∣ b := fun hd => hpar.2 (Int.prime_two.dvd_of_dvd_pow
      (habN ▸ (dvd_pow (Dvd.dvd.mul_left hd a) two_ne_zero) : (2 : ℤ) ∣ N ^ 2))
    have ha0 : a ≠ 0 := by rintro rfl; exact haodd ⟨0, by ring⟩
    have hb0 : b ≠ 0 := by rintro rfl; exact hbodd ⟨0, by ring⟩
    obtain ⟨m, n, hmn, hmna, heq2⟩ := step_G8_odd hab haodd heq
    have hm0 : m ≠ 0 := by rintro rfl; exact ha0 (by nlinarith [hmna, sq_nonneg a])
    have hn0 : n ≠ 0 := by rintro rfl; exact ha0 (by nlinarith [hmna, sq_nonneg a])
    have hNfact : N ^ 2 = m ^ 2 * (n ^ 2 * b ^ 2) := by
      linear_combination -habN - b ^ 2 * hmna
    have hcore : m ^ 2 = 1 ∧ n ^ 2 = 1 ∧ b ^ 2 = 1 := by
      by_cases hnb : n ^ 2 * b ^ 2 = 1
      · have hn2 : n ^ 2 = 1 := by nlinarith [one_le_sq hn0, one_le_sq hb0]
        have hb2 : b ^ 2 = 1 := by nlinarith [one_le_sq hn0, one_le_sq hb0]
        refine ⟨?_, hn2, hb2⟩
        rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, show m ^ 4 = (m ^ 2) ^ 2 by ring, hn2] at heq2
        have hfac : (m ^ 2 - 1) * (7 * m ^ 2 - 15) = 0 := by
          linear_combination heq2 - 16 * hb2
        rcases mul_eq_zero.mp hfac with h8 | h8
        · linarith
        · obtain ⟨u, hu⟩ : ∃ u : ℤ, m ^ 2 = u := ⟨_, rfl⟩
          rw [hu] at h8 ⊢
          omega
      · have h2le : 2 ≤ n ^ 2 * b ^ 2 := by
          rcases lt_or_gt_of_ne hnb with h3 | h3
          · nlinarith [one_le_sq hn0, one_le_sq hb0]
          · omega
        have hlt : m.natAbs < N.natAbs := by
          refine natAbs_lt_of_sq_lt ?_
          rw [hNfact]
          nlinarith [one_le_sq hm0, h2le]
        obtain ⟨hn2, hm2⟩ := IH m.natAbs (lt_of_lt_of_le hlt hle) n m (4 * b) le_rfl hmn.symm (by linear_combination heq2)
        have hm2e : m ^ 2 = 1 := le_antisymm hm2 (one_le_sq hm0)
        refine ⟨hm2e, hn2, ?_⟩
        rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, show m ^ 4 = (m ^ 2) ^ 2 by ring, hn2,
          hm2e] at heq2
        linarith
    obtain ⟨hm2e, hn2e, hb2e⟩ := hcore
    have hasq : a ^ 2 = 1 := by rw [← hmna]; nlinarith [hm2e, hn2e]
    refine ⟨?_, ?_⟩
    · rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, show b ^ 4 = (b ^ 2) ^ 2 by ring, hasq,
        hb2e] at heq
      linarith
    · rw [← habN]; nlinarith [hasq, hb2e]

/-- **The `d = 1` homogeneous space of `14a4`** (PROVEN 2026-07-27): the only
coprime positive solution of `Q² = S⁴ − 11S²e² + 32e⁴` is `(S, e) = (2, 1)`,
which is the rational point `T = 4` of `V² = T³ − 11T² + 32T`, i.e. the pair of
points `(x, y) = (0, 0)` and `(0, −1)` of `14a4`.

Not congruence-obstructed — it carries that one point — so the proof is a genuine
infinite descent, carried by `h1_classification` above. Both parities of `e` reduce
to the SAME space `H₁`: for `e` odd through `4Q² = (2S² − 11e²)² + 7e⁴` and
`step_G1_oddE`, for `e` even through `Q² = (S² − 22f²)² + 28f⁴` and
`step_G1_evenE`. The `e` even branch then dies not by a congruence but because
`H₁` forces `e = 2`, `S = 4`, contradicting `gcd(S, e) = 1`. -/
theorem quartic_one {S e Q : ℤ} (hS : 0 < S) (he : 0 < e) (hcop : IsCoprime S e)
    (h : S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4 = Q ^ 2) : S = 2 ∧ e = 1 := by
  have h' : Q ^ 2 = S ^ 4 - 11 * S ^ 2 * e ^ 2 + 32 * e ^ 4 := h.symm
  by_cases heodd : (2 : ℤ) ∣ e
  · exfalso
    obtain ⟨m, n, hmn, hmne, heq⟩ := step_G1_evenE hcop heodd (by omega) h'
    have hm0 : m ≠ 0 := by rintro rfl; nlinarith [hmne, he]
    obtain ⟨hn2, hm2⟩ :=
      h1_classification m.natAbs n m S le_rfl hmn.symm (by linear_combination heq)
    have hm2e : m ^ 2 = 1 := le_antisymm hm2 (one_le_sq hm0)
    have he2 : e ^ 2 = 4 := by nlinarith [hmne, hm2e, hn2]
    have heval : e = 2 := by nlinarith [he2, he]
    rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, show m ^ 4 = (m ^ 2) ^ 2 by ring, hn2, hm2e] at heq
    have hSval : S = 4 := by nlinarith [heq, hS]
    exact Int.prime_two.not_unit
      (hcop.isUnit_of_dvd' ⟨2, by omega⟩ ⟨1, by omega⟩)
  · obtain ⟨m, n, hmn, hmne, heq⟩ := step_G1_oddE hcop heodd h'
    have hm0 : m ≠ 0 := by rintro rfl; nlinarith [hmne, he]
    obtain ⟨hn2, hm2⟩ :=
      h1_classification m.natAbs n m (2 * S) le_rfl hmn.symm (by linear_combination heq)
    have hm2e : m ^ 2 = 1 := le_antisymm hm2 (one_le_sq hm0)
    have he2 : e ^ 2 = 1 := by nlinarith [hmne, hm2e, hn2]
    rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, show m ^ 4 = (m ^ 2) ^ 2 by ring, hn2, hm2e] at heq
    exact ⟨by nlinarith [heq, hS], by nlinarith [he2, he]⟩

/-- **The `d = 2` homogeneous space of `14a4`** (PROVEN 2026-07-27): the only
coprime positive solution of `Q² = 2S⁴ − 11S²e² + 16e⁴` is `(S, e) = (2, 1)`,
which is the rational point `T = 8`, i.e. the pair `(x, y) = (1, 0)` and
`(1, −2)` of `14a4`.

Here both parities are FORCED before any descent: `e` even gives `Q² ≡ 2 (mod 4)`
and `S`, `e` both odd gives `Q² ≡ 7 (mod 8)`, so `S = 2s` is even and `e` is odd.
Dividing by `4` lands on `q² = 8s⁴ − 11s²e² + 4e⁴`, the `d = 8` member of the same
family, which for `s` odd descends to `H₁` by `step_G8_odd` and for `s` even
reduces to `quartic_one` at `(e, s/2)` — and that forces `e = 2`, contradicting
`e` odd. -/
theorem quartic_two {S e Q : ℤ} (hS : 0 < S) (he : 0 < e) (hcop : IsCoprime S e)
    (h : 2 * S ^ 4 - 11 * S ^ 2 * e ^ 2 + 16 * e ^ 4 = Q ^ 2) : S = 2 ∧ e = 1 := by
  have heodd : ¬ (2 : ℤ) ∣ e := by
    rintro ⟨f, hf⟩
    have hSodd : ¬ (2 : ℤ) ∣ S := fun hd =>
      Int.prime_two.not_unit (hcop.isUnit_of_dvd' hd ⟨f, hf⟩)
    obtain ⟨k, hk⟩ := odd_sq_eq hSodd
    have h4 : Q ^ 2 = 4 * (32 * k ^ 2 + 8 * k - 88 * k * f ^ 2 - 11 * f ^ 2 + 64 * f ^ 4) + 2 := by
      rw [← h, hf, show S ^ 4 = (S ^ 2) ^ 2 by ring, hk]; ring
    rcases sq_form Q with ⟨-, s, hs⟩ | ⟨-, s, hs⟩ | ⟨-, s, hs⟩ <;> omega
  have hSeven : (2 : ℤ) ∣ S := by
    by_contra hSodd
    obtain ⟨k, hk⟩ := odd_sq_eq hSodd
    obtain ⟨l, hl⟩ := odd_sq_eq heodd
    have h8 : Q ^ 2 = 8 * (16 * k ^ 2 - 88 * k * l + 128 * l ^ 2 - 7 * k + 21 * l) + 7 := by
      rw [← h, show S ^ 4 = (S ^ 2) ^ 2 by ring, show e ^ 4 = (e ^ 2) ^ 2 by ring, hk, hl]; ring
    rcases sq_form Q with ⟨-, s, hs⟩ | ⟨-, s, hs⟩ | ⟨-, s, hs⟩ <;> omega
  obtain ⟨s, hs⟩ := hSeven
  have hs0 : 0 < s := by omega
  have hcse : IsCoprime s e := hcop.of_isCoprime_of_dvd_left ⟨2, by rw [hs]; ring⟩
  obtain ⟨q, hq⟩ : (2 : ℤ) ∣ Q := Int.prime_two.dvd_of_dvd_pow
    (⟨2 * (8 * s ^ 4 - 11 * s ^ 2 * e ^ 2 + 4 * e ^ 4), by rw [← h, hs]; ring⟩ : (2 : ℤ) ∣ Q ^ 2)
  have hG8 : q ^ 2 = 8 * s ^ 4 - 11 * s ^ 2 * e ^ 2 + 4 * e ^ 4 := by
    have h4 : 4 * q ^ 2 = 4 * (8 * s ^ 4 - 11 * s ^ 2 * e ^ 2 + 4 * e ^ 4) := by
      rw [hq, hs] at h; linear_combination -h
    linarith
  by_cases hsodd : (2 : ℤ) ∣ s
  · exfalso
    obtain ⟨sg, hsg⟩ := hsodd
    have hsg0 : 0 < sg := by omega
    have hcesg : IsCoprime e sg := (hcse.of_isCoprime_of_dvd_left ⟨2, by rw [hsg]; ring⟩).symm
    obtain ⟨q', hq'⟩ : (2 : ℤ) ∣ q := Int.prime_two.dvd_of_dvd_pow
      (⟨2 * (32 * sg ^ 4 - 11 * sg ^ 2 * e ^ 2 + e ^ 4), by rw [hG8, hsg]; ring⟩ :
        (2 : ℤ) ∣ q ^ 2)
    have hG1 : e ^ 4 - 11 * e ^ 2 * sg ^ 2 + 32 * sg ^ 4 = q' ^ 2 := by
      have h4 : 4 * (e ^ 4 - 11 * e ^ 2 * sg ^ 2 + 32 * sg ^ 4) = 4 * q' ^ 2 := by
        rw [hq', hsg] at hG8; linear_combination -hG8
      linarith
    have hev : e = 2 := (quartic_one he hsg0 hcesg hG1).1
    exact heodd ⟨1, by omega⟩
  · obtain ⟨m, n, hmn, hmns, heq2⟩ := step_G8_odd hcse hsodd hG8
    have hm0 : m ≠ 0 := by rintro rfl; nlinarith [hmns, hs0]
    obtain ⟨hn2, hm2⟩ :=
      h1_classification m.natAbs n m (4 * e) le_rfl hmn.symm (by linear_combination heq2)
    have hm2e : m ^ 2 = 1 := le_antisymm hm2 (one_le_sq hm0)
    rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, show m ^ 4 = (m ^ 2) ^ 2 by ring, hn2, hm2e] at heq2
    exact ⟨by nlinarith [hmns, hm2e, hn2, hs0, hs], by nlinarith [heq2, he]⟩

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
