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

THE ONE LEAF:
* `WeierstrassCurve.curve11a3_rational_points` — the four affine rational
  points of `y² + y = x³ − x²`, unconditionally.

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

/-- **The rational points of `11a3`** (THE sorry leaf of this module,
restated 2026-07-26): the affine rational points of `y² + y = x³ − x²` are
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
for. -/
theorem curve11a3_rational_points (x y : ℚ)
    (_h : curve11a3.toAffine.Nonsingular x y) :
    (x, y) = ((0 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((1 : ℚ), (-1 : ℚ)) :=
  sorry

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

end WeierstrassCurve
