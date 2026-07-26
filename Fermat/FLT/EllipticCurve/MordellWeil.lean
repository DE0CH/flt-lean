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

## SECOND RESTRUCTURE, 2026-07-26 — level `14` collapses the same way, and
## the Mordell–Weil leaf for `14a4` is GONE

`14a4` arrived carrying three leaves — `curve14a4_isTorsion` (rank `0`),
`curve14a4_fg` (Mordell–Weil for this one curve) and `curve14a4_points` (the
enumeration, *given* finiteness). Two of them are now closed, and the third
was not restated but simply became unnecessary.

The observation, which is the `11a3` collapse run through reduction instead of
through an unconditional restatement: **torsion injects into the reduction at a
good odd prime**. `Δ(14a4) = −28`, so `3` is a prime of good reduction, and
`#14a4(𝔽₃) = 6` by exhaustive check over nine pairs. Hence rank `0` alone —
"`14a4(ℚ)` is torsion" — gives both that `14a4(ℚ)` is FINITE and that it has at
most `6` elements. Six are exhibited, so the enumeration follows.

So `curve14a4_fg` was DELETED (recoverable from this file's parent commit):
finite generation was only ever the route from rank `0` to finiteness, and
reduction supplies that route without it. `curve14a4_finite`,
`curve14a4_natCard_le` and `curve14a4_points` are PROVEN, and
`curve14a4_isTorsion` is the single surviving leaf at level `14` — exactly
parallel to `curve11a3_rational_points` at level `11`.

The brick itself lives in `Fermat/FLT/EllipticCurve/TorsionReduction.lean` as
`WeierstrassCurve.exists_injective_torsion_toReduction`, and is shared with
`MazurTorsion.lean`'s `no_rational_point_of_isogenyPrime_jInvariant`; see that
module's docstring for why one auxiliary prime settles the whole `X₀` table at
`p ∈ {37, 43, 67, 163}` and supersedes Olson's theorem.

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

* `WeierstrassCurve.curve14a4Int` and the reduction data at `3`
  (`curve14a4Int_Δ = −28`, `curve14a4_reduction_natCard = 6`), then
  `curve14a4_finite`, `curve14a4_natCard_le` and `curve14a4_points` — see the
  SECOND RESTRUCTURE note above.

THE TWO LEAVES, one per level, each exactly "rank `0` for one explicit curve":
* `WeierstrassCurve.curve11a3_rational_points` — the four affine rational
  points of `y² + y = x³ − x²`, unconditionally.
* `WeierstrassCurve.curve14a4_isTorsion` — `14a4(ℚ)` is torsion.

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
public import Fermat.FLT.EllipticCurve.TorsionReduction

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

/-- **Rank `0` for `14a4`** (sorry leaf, 2026-07-26), in the concrete form that
carries the content: every rational point of `y² + xy + y = x³ − x` is a
torsion point.

Classically this is a descent by the rational `2`-isogeny that `14a4` admits
(the isogeny class `14a` is `2`- and `3`-isogeny connected, so a `6`-isogeny
descent is also available): both descent images are trivial, so the rank is
`0`. `RankBound(E) = 0` with proof flag `true` (Magma 2026-07-26, untrusted
searcher). Kubert, "Universal bounds on the torsion of elliptic curves" (Proc.
LMS 33, 1976); Ligozat; subsumed in Mazur 1977, Thm 8.

Stated as `AddMonoid.IsTorsion` rather than as `rank = 0` because there is no
rank function here to state the latter against, and this form is exactly what
the reduction brick consumes.

**THIS IS NOW THE ONLY LEAF AT LEVEL `14`** (2026-07-26). It used to sit beside
`curve14a4_fg` (Mordell–Weil for this curve) and `curve14a4_points` (the
enumeration, given finiteness); both are gone, because reduction at the good
prime `3` embeds the torsion of `14a4(ℚ)` into the six-element group
`14a4(𝔽₃)`. Rank `0` therefore yields finiteness AND the enumeration at once,
with no Mordell–Weil input at all — the `11a3`-shaped collapse that
`curve14a4_fg`'s own docstring asked for, carried out through
`Fermat/FLT/EllipticCurve/TorsionReduction.lean` rather than through an
unconditional restatement. See `curve14a4_natCard_le` below. -/
theorem curve14a4_isTorsion : AddMonoid.IsTorsion curve14a4.toAffine.Point :=
  sorry

/-- The integral model of `14a4`, i.e. the same Weierstrass equation with its
coefficients read in `ℤ`. Reduction is coefficientwise from here, so the
brick's hypotheses are checked on this model and not on `curve14a4`. -/
def curve14a4Int : WeierstrassCurve ℤ := ⟨1, 0, 1, -1, 0⟩

/-- `curve14a4` is the base change to `ℚ` of its integral model. -/
theorem curve14a4Int_map_rat : curve14a4Int.map (Int.castRingHom ℚ) = curve14a4 := by
  simp only [curve14a4Int, curve14a4, WeierstrassCurve.map]
  norm_num

/-- `Δ(14a4) = −28` over `ℤ`, computed rather than asserted; in particular
`3 ∤ Δ`, so `14a4` has good reduction at `3`. -/
theorem curve14a4Int_Δ : curve14a4Int.Δ = -28 := by
  simp only [curve14a4Int, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- The reduction of `14a4` mod `3` is the same tuple read in `ZMod 3`. -/
theorem curve14a4Int_map_zmod3 :
    curve14a4Int.map (Int.castRingHom (ZMod 3)) = ⟨1, 0, 1, -1, 0⟩ := by
  simp only [curve14a4Int, WeierstrassCurve.map]
  norm_num

/-- The five affine points of `14a4` over `𝔽₃`, by exhaustive check: the curve
`y² + xy + y = x³ − x` over `𝔽₃` meets `x = 0` in `y ∈ {0, 2}`, `x = 1` in
`y ∈ {0, 1}` and `x = 2` in `y = 0`. -/
theorem curve14a4_reduction_nonsingular_iff (x y : ZMod 3) :
    (⟨1, 0, 1, -1, 0⟩ : WeierstrassCurve (ZMod 3)).toAffine.Nonsingular x y ↔
      (x, y) ∈ ({(0, 0), (0, 2), (1, 0), (1, 1), (2, 0)} : Finset (ZMod 3 × ZMod 3)) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  revert x y
  decide

/-- **`#14a4(𝔽₃) = 6`** — five affine points and the point at infinity. This is
the number that bounds `14a4(ℚ)`, and it is exactly `#(ℤ/6)`. -/
theorem curve14a4_reduction_natCard :
    Nat.card (⟨1, 0, 1, -1, 0⟩ : WeierstrassCurve (ZMod 3)).toAffine.Point = 6 := by
  rw [WeierstrassCurve.natCard_affine_point_eq _
    (WeierstrassCurve.finite_affine_point_of_finite _)]
  have h : Nat.card {xy : ZMod 3 × ZMod 3 //
      (⟨1, 0, 1, -1, 0⟩ : WeierstrassCurve (ZMod 3)).toAffine.Nonsingular xy.fst xy.snd} = 5 := by
    have e : {xy : ZMod 3 × ZMod 3 //
        (⟨1, 0, 1, -1, 0⟩ : WeierstrassCurve (ZMod 3)).toAffine.Nonsingular xy.fst xy.snd} ≃
        {xy : ZMod 3 × ZMod 3 //
          xy ∈ ({(0, 0), (0, 2), (1, 0), (1, 1), (2, 0)} : Finset (ZMod 3 × ZMod 3))} :=
      Equiv.subtypeEquivRight fun xy => curve14a4_reduction_nonsingular_iff xy.1 xy.2
    rw [Nat.card_congr e]
    simp
    decide
  rw [h]

/-- **Rank `0` bounds `14a4(ℚ)` by `#14a4(𝔽₃) = 6`** (PROVEN 2026-07-26 over
`WeierstrassCurve.exists_injective_torsion_toReduction`).

Stated for a variable `W` with `hW` pinning it to the integral model's base
change, so that `subst` — rather than a rewrite under a binder whose motive
mentions the `AddCommGroup` instance — carries the identification. That is the
standard remedy in this tree for an instance path that prints identically and
refuses to unify. -/
theorem curve14a4_finite_and_natCard_le {W : WeierstrassCurve ℚ}
    (hW : W = curve14a4Int.map (Int.castRingHom ℚ))
    (htor : AddMonoid.IsTorsion W.toAffine.Point) :
    Finite W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ 6 := by
  subst hW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := WeierstrassCurve.exists_injective_torsion_toReduction
    (ℓ := 3) (by norm_num) curve14a4Int (by rw [curve14a4Int_Δ]; decide)
  haveI : Finite (curve14a4Int.map (Int.castRingHom (ZMod 3))).toAffine.Point :=
    WeierstrassCurve.finite_affine_point_of_finite _
  have hcard : Nat.card (curve14a4Int.map (Int.castRingHom (ZMod 3))).toAffine.Point = 6 := by
    rw [curve14a4Int_map_zmod3]
    exact curve14a4_reduction_natCard
  have hf : Function.Injective
      (fun P : (curve14a4Int.map (Int.castRingHom ℚ)).toAffine.Point => g ⟨P, htor P⟩) :=
    fun _ _ hab => congrArg Subtype.val (hg hab)
  exact ⟨Finite.of_injective _ hf,
    le_trans (Nat.card_le_card_of_injective _ hf) hcard.le⟩

/-- **`14a4(ℚ)` is finite** (PROVEN 2026-07-26 from rank `0` alone).

No Mordell–Weil input: the torsion of `14a4(ℚ)` injects into `14a4(𝔽₃)` at the
good prime `3`, and `14a4(ℚ)` is all torsion, so it embeds in a six-element
group. The leaf `curve14a4_fg` that used to supply finite generation here was
DELETED — it is recoverable from this file's parent commit. -/
theorem curve14a4_finite : Finite curve14a4.toAffine.Point :=
  (curve14a4_finite_and_natCard_le curve14a4Int_map_rat.symm curve14a4_isTorsion).1

/-- **`#14a4(ℚ) ≤ 6`** (PROVEN 2026-07-26): the count that makes the
enumeration below complete. -/
theorem curve14a4_natCard_le : Nat.card curve14a4.toAffine.Point ≤ 6 :=
  (curve14a4_finite_and_natCard_le curve14a4Int_map_rat.symm curve14a4_isTorsion).2

/-- The five listed pairs really are nonsingular points of `14a4`. -/
theorem curve14a4_nonsingular_of_mem (x y : ℚ)
    (hx : (x, y) = ((1 : ℚ), (-2 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((-1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (0 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ))) :
    curve14a4.toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [curve14a4]
  rcases hx with h | h | h | h | h <;>
    (rw [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;> norm_num

/-- **The five affine rational points of `14a4`** (PROVEN 2026-07-26 from rank
`0` and reduction at `3`): the affine rational points of `y² + xy + y = x³ − x`
are exactly `(1,−2)`, `(0,−1)`, `(−1,0)`, `(0,0)`, `(1,0)`. Together with the
point at infinity these are the six elements of `14a4(ℚ) ≅ ℤ/6`.

THE PROOF, which is the argument the old docstring described as available and
which is now carried out. `14a4(ℚ)` is torsion (`curve14a4_isTorsion`, the one
remaining leaf at this level); torsion injects into `14a4(𝔽₃)` at the good
prime `3` (`WeierstrassCurve.exists_injective_torsion_toReduction`, with
`Δ = −28` and `3 ∤ 28`); and `#14a4(𝔽₃) = 6` by exhaustive check
(`curve14a4_reduction_natCard`). So `#14a4(ℚ) ≤ 6`. The five pairs listed are
nonsingular points and pairwise distinct, so with the point at infinity they
already exhaust the group — a sixth affine point would make seven.

The `Finite` hypothesis is retained in the signature, now genuinely unused
(`_hfin`), so that the call site `x1_fourteen_no_rational_point` in
`Fermat/FLT/FreyCurve/TateNormalForm.lean` does not have to change; that is
also what keeps `curve14a4_finite` consumed rather than free-floating. A future
owner is free to drop it and adjust the one call site.

`MordellWeilGroup` returns `ℤ/6` and lists exactly these five affine points
plus `(0 : 1 : 0)` (Magma 2026-07-26, untrusted searcher). Note the
`x`-coordinates take only THREE values, `0`, `1`, `−1`, and that is the form in
which the consumer uses this leaf.

All six points are CUSPS of `X_1(14)` (`φ(14)/2 = 3` rational cusps, plus the
three conjugate ones that happen to be rational on this model). That is the
input to `x1_fourteen_no_rational_point` in
`Fermat/FLT/FreyCurve/TateNormalForm.lean`, whose proof exhibits the birational
map from the plane sextic and checks that each of the three `x`-values pulls
back to `d ∈ {0, 1}` — the two excluded degenerate loci. -/
theorem curve14a4_points (_hfin : Finite curve14a4.toAffine.Point) (x y : ℚ)
    (h : curve14a4.toAffine.Nonsingular x y) :
    (x, y) = ((1 : ℚ), (-2 : ℚ)) ∨ (x, y) = ((0 : ℚ), (-1 : ℚ)) ∨
      (x, y) = ((-1 : ℚ), (0 : ℚ)) ∨ (x, y) = ((0 : ℚ), (0 : ℚ)) ∨
      (x, y) = ((1 : ℚ), (0 : ℚ)) := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨n1, n2, n3, n4, n5⟩ := hcon
  haveI := curve14a4_finite
  haveI := curve14a4.finite_nonsingular_subtype_of_finite_point curve14a4_finite
  haveI : Fintype {xy : ℚ × ℚ // curve14a4.toAffine.Nonsingular xy.fst xy.snd} :=
    Fintype.ofFinite _
  have hsub : Nat.card {xy : ℚ × ℚ // curve14a4.toAffine.Nonsingular xy.fst xy.snd} + 1 ≤ 6 := by
    rw [← WeierstrassCurve.natCard_affine_point_eq _ curve14a4_finite]
    exact curve14a4_natCard_le
  have h1 := curve14a4_nonsingular_of_mem 1 (-2) (by tauto)
  have h2 := curve14a4_nonsingular_of_mem 0 (-1) (by tauto)
  have h3 := curve14a4_nonsingular_of_mem (-1) 0 (by tauto)
  have h4 := curve14a4_nonsingular_of_mem 0 0 (by tauto)
  have h5 := curve14a4_nonsingular_of_mem 1 0 (by tauto)
  have hnd : ([⟨(1, -2), h1⟩, ⟨(0, -1), h2⟩, ⟨(-1, 0), h3⟩, ⟨(0, 0), h4⟩, ⟨(1, 0), h5⟩,
      ⟨(x, y), h⟩] :
      List {xy : ℚ × ℚ // curve14a4.toAffine.Nonsingular xy.fst xy.snd}).Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      first
        | exact Ne.symm n1
        | exact Ne.symm n2
        | exact Ne.symm n3
        | exact Ne.symm n4
        | exact Ne.symm n5
        | norm_num
  have hle := hnd.length_le_card
  rw [← Nat.card_eq_fintype_card] at hle
  simp only [List.length_cons, List.length_nil] at hle
  omega

end WeierstrassCurve
