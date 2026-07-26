/-
Velu.lean — own work for the Fermat project (not vendored).

**Vélu's construction of the quotient of an elliptic curve by a finite
subgroup**, cut 2026-07-25 out of the single sorry leaf
`WeierstrassCurve.exists_quotient_isogeny_of_odd_prime_card` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, which asks for: given a
Galois-stable subgroup `C` of ODD prime order `ℓ` in `E(ℚ̄)` for an
elliptic curve `E/ℚ`, an elliptic curve `E'/ℚ` and a Galois-equivariant
group homomorphism `E(ℚ̄) →+ E'(ℚ̄)` with kernel exactly `C`.

## The cut

The classical presentation of Vélu's formulas (Vélu 1971, p. 238; Kohel's
thesis §2.4; Washington, *Elliptic Curves*, ch. 12) writes the isogeny as
an explicit rational function of `x` and `y` whose poles sit at the
`x`-coordinates of the points of `C`. That form needs a choice of
representatives of `C ∖ {0}` modulo `±`, and the resulting expressions are
unusable for the group law.

The form used here is the equivalent **group-law form**: for `P ∉ C`,

  `X(P) = x(P) + Σ_{Q ∈ C ∖ 0} (x(P + Q) − x(Q))`
  `Y(P) = y(P) + Σ_{Q ∈ C ∖ 0} (y(P + Q) − y(Q))`

which is written here — giving `veluCoordX` / `veluCoordY` — as a
difference of two sums over ALL of `C`, using the junk value `0` for the
coordinates of the point at infinity: the `Q = 0` term contributes `x(P)`
to the first sum and `0` to the second. Two consequences make this the
right cut for a formalisation:

* **Galois equivariance is immediate.** Galois permutes `C` and commutes
  with the group law and with the coordinate functions, so both sums are
  permuted; no rational-function bookkeeping is needed. This is PROVEN
  below (`velu_coordX_map`, `velu_coordY_map`).
* **No choice of representatives is needed.** Vélu's coefficients `t` and
  `w` are sums over representatives of `C ∖ {0}` modulo `±`; each summand
  is `±`-invariant (see `veluTTerm`/`veluWTerm`, where the `y`-dependence
  of `t` has already been cancelled), so summing over all of `C ∖ {0}` and
  halving gives the same number. Halving is why `CharZero` appears.

The quotient curve is `veluCurve W S`, i.e.

  `y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x + (a₆ − b₂t − 7w)`.

## What is PROVEN here and what is left

PROVEN: the definitions; the coordinate and term transport lemmas; the
reindexing of a Galois-stable sum; the descent of `t` and `w` to `ℚ`
(`velu_t_mem_range`, `velu_w_mem_range`); Galois equivariance of the
Vélu coordinates (`velu_coordX_map`, `velu_coordY_map`); and, since
2026-07-26, the invariance of the Vélu coordinates under translation by the
kernel and under negation (`veluCoordX_add_mem`, `veluCoordY_add_mem`,
`veluCoordX_neg`, `veluCoordY_neg`, over the kernel sum `velu_sum_kernel`),
together with the assemblies of `velu_isElliptic` and `velu_map_add` over
the leaves below; and the `±`-paired addition law identifying the group-law
sums with Vélu's classical rational functions (`velu_pair_X`, `velu_pair_Y`,
`velu_coordX_eq`, `velu_coordY_eq`), which proves `velu_equation` — since
2026-07-26 `velu_equation_pole`
itself is PROVEN, by completing the square and factoring
`2Y + a₁X + a₃ = (2y + a₁x + a₃)(1 − Σ veluPoleV)` (`velu_pole_V`,
`velu_two_poleY_add_poleX`), which eliminates `y` from the quotient equation
outright and leaves a one-variable identity.

Also PROVEN, 2026-07-26:

* `isElliptic_of_three_twoTorsion` and its converse
  `exists_three_twoTorsion_of_Δ_ne_zero` — general Weierstrass geometry,
  no Vélu input: three affine `2`-torsion points with distinct `x` exist
  exactly when `Δ ≠ 0`, because `16 Δ` is the discriminant of the
  `2`-division cubic `4x³ + b₂x² + 2b₄x + b₆`.
* the base change of the whole Vélu construction along `F → L`
  (`velu_baseChange_curve` and the lemmas around it), and the parity
  argument `velu_twoTorsion_notMem` placing `2`-torsion outside a subgroup
  of odd order.
* `velu_exists_three_twoTorsion`, and (2026-07-26) the leaf it was assembled
  over, `velu_coordX_twoTorsion_ne`: the Vélu `x`-coordinates of two distinct
  `2`-torsion points outside the kernel differ. Its proof is a root count for
  the monic degree-`|S|` polynomial `veluXNum S − X(T₁)·veluH S`, in which the
  translates `x(T₁ + Q)` are DOUBLE roots because the logarithmic-derivative
  identity `velu_dlog_XNum` turns `dX/dx = 0` there into
  `velu_poleV_sum_eq_one`. It consumes no open leaf.

Also PROVEN, 2026-07-26: `velu_pole_identity` itself, the `y`-free
rational-function identity in `x` alone that remains of the verification of
Vélu 1971 after `velu_equation_pole` has completed the square — over the two
POLYNOMIAL leaves below. The identity is a genuine rational-function identity
in `x` (checked numerically at random `x` unrelated to any point), so clearing
the denominator `veluH S = ∏_{Q ∈ S ∖ 0}(T − x_Q)` turns it into
`veluTheta S = 0` for an explicit polynomial `veluTheta`, and Vélu's classical
two-part argument becomes: `veluH S ^ 4` divides `veluTheta S`, and
`deg (veluTheta S) < 4(|S| − 1)`. See the section header at `section PolePoly`.

**BOTH POLYNOMIAL LEAVES ARE NOW PROVEN** (2026-07-26, by two owners
working concurrently; the halves were merged at integration and compose
without circularity):

* `WeierstrassCurve.velu_theta_degree_lt` — `deg (veluTheta S) < 4(|S| − 1)`:
  "vanishing at infinity", where `veluT` and `veluW` are consumed. Proven
  outright by a reflection argument; see its docstring. Verified numerically
  to hold on `±`-stable NON-subgroups too, so it does not need `hS`.
* `WeierstrassCurve.velu_theta_local_dvd` — `(T − x_Q)⁸ ∣ veluTheta S` for
  each nonzero `Q` of the kernel: "no poles", in local form. ALL of the
  arithmetic content of Vélu's theorem is here, and it is the only one of the
  two polynomial leaves that needs closure of `S` under addition. Proven by
  the generic-point route: translation invariance of the Vélu coordinates
  identifies the local behaviour at `x_Q` with the behaviour at infinity. See
  the `GenericPoint` section for the coordinate-ring machinery it needs.

  It takes the degree bound as an explicit HYPOTHESIS `hdeg` (deliberately
  weaker than the sibling: `≤ 4n` rather than `< 4n`) rather than calling the
  sibling itself, so the two are independent theorems; `velu_pole_identity`
  discharges `hdeg` with `(velu_theta_degree_lt hS hodd).le` at the call site.

Also PROVEN 2026-07-26: `WeierstrassCurve.velu_coordX_twoTorsion_ne` — the
Vélu `x`-coordinates of two distinct `2`-torsion points outside the kernel
differ. Proven by a rational-function DEGREE COUNT that deliberately avoids
the addition law: with `D = veluXNum S − c · veluH S` monic of degree `|S|`,
the translates `x(T₁ + Q)` are DOUBLE roots via the identity
`veluXNum' · veluH − veluXNum · veluH' = veluXi`, giving a divisor of degree
`|S| + 1 > |S|`. Its `hodd` hypothesis is LOAD-BEARING and must not be
stripped: an even-order kernel containing a nonzero `2`-torsion `Q₀` makes
`T₂ = T₁ + Q₀` a counterexample (PARI: 733 of 733 even-order instances fail).

SORRY LEAF (one, stated over an arbitrary field of characteristic zero for a
finite subgroup of odd order):

* `WeierstrassCurve.velu_map_add_of_notMem` — additivity in the generic
  case, `P`, `Q`, `P + Q` all outside the kernel.

That is now the ONLY open leaf in this file (its body carries two sorried
`have`s, goals 2 and 3 of the reduction recorded in its docstring). The
injectivity half of Vélu's theorem was closed on 2026-07-26:
`velu_coord_ne_neg` is PROVEN over the fibre identity

  `velu_xNum_sub_eq_prod : veluXNum S − X(P)·veluH S = ∏_{Q ∈ S} (T − x(P+Q))`,

itself PROVEN over `velu_wronskian` (`XNum'·H − XNum·H' = Ξ`, the
polynomial form of `X'(T) = 1 − Σ veluPoleV`) and the two directions of
the collision criterion, `velu_two_mem_of_xi_eq_zero` and
`velu_xi_eval_eq_zero_of_two_mem`. `velu_coord_ne_neg` discharges goal 1
of `velu_map_add_of_notMem`, and it also gives a second route to
`velu_coordX_twoTorsion_ne` — which however keeps its own INDEPENDENT
degree-count proof, so `velu_exists_three_twoTorsion` and
`velu_isElliptic` rest on no open leaf either way, and the nonsingularity
half is complete. (`velu_equation` was also listed here as a leaf until
2026-07-26 and is PROVEN over `velu_equation_pole` and
`velu_pole_identity`.)

The polynomial machinery written for the degree-count route
(`veluXNum_eval`, `veluXNum_monic`, `veluXNum_degree`, `velu_dlog_XNum`,
`veluPX_degree_lt`, `veluH_degree_eq_card`) is available to the remaining
leaf, and `veluPX_degree_lt` in particular is a step towards
`velu_theta_degree_lt`.

These are the mathematical content of Vélu's theorem. NONE of it is in
mathlib, and none of it is in the reference project `~/cs/FLT` either
(both checked 2026-07-26): there is no isogeny, no quotient curve and no
curve function field anywhere to build on.

That does NOT make the remaining leaf a function-field project. It rests
on ONE elementary brick — Vélu's pair identity

  `x(P+Q) + x(P−Q) = 2x_Q + t_Q/(x_P − x_Q) + u_Q/(x_P − x_Q)²`,

with `t_Q = veluTTerm W Q` and `u_Q = veluWTerm W Q − x_Q · veluTTerm W Q`
— which was COMPILED on 2026-07-26 (`field_simp`, then
`linear_combination 2 * h₁ - 2 * hQ` from the two Weierstrass equations)
and is reproduced in `velu_map_add_of_notMem`'s docstring, along
with the reindexing that sums it over `S` with no choice of
representatives. It is not committed only because nothing consumes it yet.
(It was originally written for `velu_coord_ne_neg`, which IS integrated and
PROVEN as of 2026-07-26 — by the polynomial route through
`velu_xNum_sub_eq_prod`, not by this identity.)
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ### Coordinates, with a junk value at infinity -/

section Coords

variable {F : Type*} [Field F] {W : Affine F}

/-- Two affine points with the same coordinates are equal. -/
lemma velu_point_some_eq {x y x' y' : F} {h : W.Nonsingular x y}
    {h' : W.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

/-- The `x`-coordinate of an affine point of a Weierstrass curve, with the junk
value `0` at the point at infinity. The junk value is what lets the Vélu sums
below range over the whole subgroup instead of over its nonzero part. -/
def veluPointX : W.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of an affine point of a Weierstrass curve, with the junk
value `0` at the point at infinity. -/
def veluPointY : W.Point → F
  | .zero => 0
  | .some _ y _ => y

@[simp] lemma veluPointX_zero : veluPointX (0 : W.Point) = 0 := rfl

@[simp] lemma veluPointY_zero : veluPointY (0 : W.Point) = 0 := rfl

@[simp] lemma veluPointX_some {x y : F} (h : W.Nonsingular x y) :
    veluPointX (Affine.Point.some x y h) = x := rfl

@[simp] lemma veluPointY_some {x y : F} (h : W.Nonsingular x y) :
    veluPointY (Affine.Point.some x y h) = y := rfl

/-- Vélu's `t`-term at a point of the kernel. The `y`-dependence of Vélu's
`t_Q = 2 g^x_Q − a₁ g^y_Q` cancels, leaving `6x² + b₂x + b₄`; in particular the
term is invariant under `Q ↦ −Q`, which is what allows the sum over
representatives modulo `±` to be replaced by half the sum over `C ∖ {0}`. -/
def veluTTerm (W : Affine F) : W.Point → F
  | .zero => 0
  | .some x _ _ => 6 * x ^ 2 + W.b₂ * x + W.b₄

/-- Vélu's `w`-term at a point of the kernel, `u_Q + x_Q t_Q` with
`u_Q = (g^y_Q)² = (2y + a₁x + a₃)²`. Also invariant under `Q ↦ −Q`. -/
def veluWTerm (W : Affine F) : W.Point → F
  | .zero => 0
  | .some x y _ =>
      (2 * y + W.a₁ * x + W.a₃) ^ 2 + x * (6 * x ^ 2 + W.b₂ * x + W.b₄)

@[simp] lemma veluTTerm_zero : veluTTerm W (0 : W.Point) = 0 := rfl

@[simp] lemma veluWTerm_zero : veluWTerm W (0 : W.Point) = 0 := rfl

@[simp] lemma veluTTerm_some {x y : F} (h : W.Nonsingular x y) :
    veluTTerm W (Affine.Point.some x y h) = 6 * x ^ 2 + W.b₂ * x + W.b₄ := rfl

@[simp] lemma veluWTerm_some {x y : F} (h : W.Nonsingular x y) :
    veluWTerm W (Affine.Point.some x y h) =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 + x * (6 * x ^ 2 + W.b₂ * x + W.b₄) := rfl

end Coords

/-! ### The Vélu data of a finite subgroup -/

/-- A finite subgroup of the group of points of a Weierstrass curve, presented as
a `Finset` so that Vélu's sums are ordinary `Finset` sums. -/
structure IsPointSubgroup {F : Type*} [Field F] [DecidableEq F] {W : Affine F}
    (S : Finset W.Point) : Prop where
  /-- The identity belongs to `S`. -/
  zero_mem : (0 : W.Point) ∈ S
  /-- `S` is closed under addition. -/
  add_mem : ∀ P ∈ S, ∀ Q ∈ S, P + Q ∈ S
  /-- `S` is closed under negation. -/
  neg_mem : ∀ P ∈ S, -P ∈ S

section Data

variable {F : Type*} [Field F] (W : Affine F)

/-- Vélu's coefficient `t`: half the sum of `veluTTerm` over the kernel. -/
def veluT (S : Finset W.Point) : F := (2 : F)⁻¹ * ∑ Q ∈ S, veluTTerm W Q

/-- Vélu's coefficient `w`: half the sum of `veluWTerm` over the kernel. -/
def veluW (S : Finset W.Point) : F := (2 : F)⁻¹ * ∑ Q ∈ S, veluWTerm W Q

/-- The Weierstrass model `y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x +
(a₆ − b₂t − 7w)` produced by Vélu's formulas from coefficients `t` and `w`. -/
def veluModel (t w : F) : Affine F :=
  ⟨W.a₁, W.a₂, W.a₃, W.a₄ - 5 * t, W.a₆ - W.b₂ * t - 7 * w⟩

/-- The Vélu quotient curve `W / S`. -/
def veluCurve (S : Finset W.Point) : Affine F :=
  W.veluModel (W.veluT S) (W.veluW S)

lemma veluCurve_eq (S : Finset W.Point) :
    W.veluCurve S = W.veluModel (W.veluT S) (W.veluW S) := rfl

end Data

section CoordData

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F)

/-- The `x`-coordinate of the Vélu image of a point:
`x(P) + Σ_{Q ∈ S ∖ 0} (x(P + Q) − x(Q))`, written as a difference of two sums
over all of `S` using the junk value at infinity. -/
def veluCoordX (S : Finset W.Point) (P : W.Point) : F :=
  (∑ Q ∈ S, veluPointX (P + Q)) - ∑ Q ∈ S, veluPointX Q

/-- The `y`-coordinate of the Vélu image of a point:
`y(P) + Σ_{Q ∈ S ∖ 0} (y(P + Q) − y(Q))`. -/
def veluCoordY (S : Finset W.Point) (P : W.Point) : F :=
  (∑ Q ∈ S, veluPointY (P + Q)) - ∑ Q ∈ S, veluPointY Q

end CoordData

/-! ### Transport of points along an equality of curves -/

section Transport

variable {F : Type*} [Field F] [DecidableEq F]

/-- The points of two equal Weierstrass curves form the same group. -/
def pointAddEquivOfEq {W W' : Affine F} (h : W = W') : W.Point ≃+ W'.Point := by
  subst h; exact AddEquiv.refl _

lemma pointAddEquivOfEq_some {W W' : Affine F} (h : W = W') {x y : F}
    (hns : W.Nonsingular x y) :
    pointAddEquivOfEq h (Affine.Point.some x y hns) =
      Affine.Point.some x y (h ▸ hns) := by
  subst h; rfl

end Transport

/-! ### Elementary identities satisfied by the Vélu coordinates

The three lemmas that reduce Vélu's additivity to its generic case: the Vélu
coordinates are INVARIANT under translation by the kernel (`veluCoordX_add_mem`,
`veluCoordY_add_mem`) and ANTI-invariant under negation (`veluCoordX_neg`,
`veluCoordY_neg`). Both are pure reindexing statements about sums over `S` and
need nothing from Vélu's theorem; together they discharge every case of
`velu_map_add` except the generic one, in which `P`, `Q` and `P + Q` all lie
outside the kernel. -/

section Identities

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- Reindexing a sum over the kernel by translation by a kernel element. -/
lemma velu_sum_translate {S : Finset W.Point} (hS : IsPointSubgroup S) {R : W.Point}
    (hR : R ∈ S) (g : W.Point → F) :
    ∑ Q ∈ S, g (R + Q) = ∑ Q ∈ S, g Q :=
  Finset.sum_nbij' (fun Q => R + Q) (fun Q => -R + Q)
    (fun a ha => hS.add_mem R hR a ha)
    (fun a ha => hS.add_mem (-R) (hS.neg_mem R hR) a ha)
    (fun a _ => by abel)
    (fun a _ => by abel)
    (fun _ _ => rfl)

/-- **Translation invariance of the Vélu `x`-coordinate** (PROVEN): translating a point by
an element of the kernel does not move its Vélu image. -/
lemma veluCoordX_add_mem {S : Finset W.Point} (hS : IsPointSubgroup S) (P : W.Point)
    {R : W.Point} (hR : R ∈ S) : W.veluCoordX S (P + R) = W.veluCoordX S P := by
  unfold veluCoordX
  congr 1
  calc ∑ Q ∈ S, veluPointX (P + R + Q) = ∑ Q ∈ S, veluPointX (P + (R + Q)) :=
        Finset.sum_congr rfl fun Q _ => by rw [add_assoc]
    _ = ∑ Q ∈ S, veluPointX (P + Q) :=
        velu_sum_translate hS hR (fun Q => veluPointX (P + Q))

/-- **Translation invariance of the Vélu `y`-coordinate** (PROVEN). -/
lemma veluCoordY_add_mem {S : Finset W.Point} (hS : IsPointSubgroup S) (P : W.Point)
    {R : W.Point} (hR : R ∈ S) : W.veluCoordY S (P + R) = W.veluCoordY S P := by
  unfold veluCoordY
  congr 1
  calc ∑ Q ∈ S, veluPointY (P + R + Q) = ∑ Q ∈ S, veluPointY (P + (R + Q)) :=
        Finset.sum_congr rfl fun Q _ => by rw [add_assoc]
    _ = ∑ Q ∈ S, veluPointY (P + Q) :=
        velu_sum_translate hS hR (fun Q => veluPointY (P + Q))

omit [DecidableEq F] in
/-- The `x`-coordinate is invariant under negation (junk value included). -/
lemma velu_pointX_neg (P : W.Point) : veluPointX (-P) = veluPointX P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

omit [DecidableEq F] in
/-- The `y`-coordinate of `-P` is `negY` of the coordinates of `P`, for `P` affine. -/
lemma velu_pointY_neg (P : W.Point) (hP : P ≠ 0) :
    veluPointY (-P) = -veluPointY P - W.a₁ * veluPointX P - W.a₃ := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => show W.negY x y = _; simp [WeierstrassCurve.Affine.negY]

/-- Reindexing a sum over the kernel by negation. -/
lemma velu_sum_neg {S : Finset W.Point} (hS : IsPointSubgroup S) (g : W.Point → F) :
    ∑ Q ∈ S, g (-Q) = ∑ Q ∈ S, g Q :=
  Finset.sum_nbij' (fun Q => -Q) (fun Q => -Q)
    (fun a ha => hS.neg_mem a ha) (fun a ha => hS.neg_mem a ha)
    (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun _ _ => rfl)

omit [DecidableEq F] in
/-- The Vélu model does not change `a₁` or `a₃`, so it has the same `negY`. -/
lemma veluCurve_negY (S : Finset W.Point) (x y : F) :
    (W.veluCurve S).negY x y = W.negY x y := rfl

/-- **The kernel sum** (PROVEN): `2 Σ_{Q ∈ S} y(Q) + a₁ Σ_{Q ∈ S} x(Q) + a₃ (|S| − 1) = 0`.

Pairing `Q` with `−Q` over `S ∖ {0}` gives `y(Q) + y(−Q) = −a₁ x(Q) − a₃` for each of the
`|S| − 1` nonzero points; the junk values at `0` contribute nothing on the left. -/
lemma velu_sum_kernel {S : Finset W.Point} (hS : IsPointSubgroup S) :
    2 * (∑ Q ∈ S, veluPointY Q) + W.a₁ * (∑ Q ∈ S, veluPointX Q)
      + W.a₃ * ((S.card : F) - 1) = 0 := by
  have hcard : ((S.erase 0).card : F) = (S.card : F) - 1 := by
    have h := Finset.card_erase_add_one hS.zero_mem
    have h' : ((S.erase 0).card : F) + 1 = (S.card : F) := by
      exact_mod_cast congrArg (Nat.cast (R := F)) h
    linear_combination h'
  rw [← hcard]
  have hsplitY : ∑ Q ∈ S, veluPointY (-Q)
      = veluPointY (-(0 : W.Point)) + ∑ Q ∈ S.erase 0, veluPointY (-Q) :=
    (Finset.add_sum_erase S (fun Q => veluPointY (-Q)) hS.zero_mem).symm
  have hsplitX : ∑ Q ∈ S, veluPointX Q
      = veluPointX (0 : W.Point) + ∑ Q ∈ S.erase 0, veluPointX Q :=
    (Finset.add_sum_erase S (fun Q => veluPointX Q) hS.zero_mem).symm
  have hsplitY' : ∑ Q ∈ S, veluPointY Q
      = veluPointY (0 : W.Point) + ∑ Q ∈ S.erase 0, veluPointY Q :=
    (Finset.add_sum_erase S (fun Q => veluPointY Q) hS.zero_mem).symm
  have key : ∀ Q ∈ S.erase 0, veluPointY (-Q)
      = -veluPointY Q - W.a₁ * veluPointX Q - W.a₃ := fun Q hQ =>
    velu_pointY_neg Q (Finset.ne_of_mem_erase hQ)
  have hexp : ∑ Q ∈ S.erase 0, veluPointY (-Q)
      = ∑ Q ∈ S.erase 0, (-veluPointY Q - W.a₁ * veluPointX Q - W.a₃) :=
    Finset.sum_congr rfl key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib,
    Finset.sum_const, nsmul_eq_mul] at hexp
  have hneg : ∑ Q ∈ S, veluPointY (-Q) = ∑ Q ∈ S, veluPointY Q :=
    velu_sum_neg hS (fun Q => veluPointY Q)
  rw [hsplitY, hsplitY'] at hneg
  simp only [neg_zero, veluPointY_zero, veluPointX_zero, zero_add] at hneg hsplitX hsplitY'
  rw [hexp] at hneg
  rw [hsplitY', hsplitX]
  linear_combination -hneg

/-- **The Vélu `x`-coordinate is invariant under negation** (PROVEN). -/
lemma veluCoordX_neg {S : Finset W.Point} (hS : IsPointSubgroup S) (P : W.Point) :
    W.veluCoordX S (-P) = W.veluCoordX S P := by
  unfold veluCoordX
  congr 1
  calc ∑ Q ∈ S, veluPointX (-P + Q) = ∑ Q ∈ S, veluPointX (-P + -Q) :=
        (velu_sum_neg hS (fun Q => veluPointX (-P + Q))).symm
    _ = ∑ Q ∈ S, veluPointX (P + Q) := Finset.sum_congr rfl fun Q _ => by
          rw [show (-P + -Q : W.Point) = -(P + Q) by abel, velu_pointX_neg]

/-- **The Vélu image of `−P` is the negative of the Vélu image of `P`** (PROVEN, coordinate
form): `Y(−P) = negY (X(P), Y(P))`, the `x`-coordinates agreeing by `veluCoordX_neg`.

Reindexing by `Q ↦ −Q` turns `Σ y(−P + Q)` into `Σ y(−(P + Q))`, and each term is
`−y(P+Q) − a₁ x(P+Q) − a₃` because `P ∉ S` forces `P + Q ≠ 0`; what is left over is exactly
the kernel sum `velu_sum_kernel`.

A corollary worth recording for the owner of `velu_exists_three_twoTorsion`: if `T = −T`
and `T ∉ S`, then `Y(T) = Y(−T) = negY (X(T), Y(T))`, i.e. the Vélu image of a `2`-torsion
point is again `2`-torsion. -/
lemma veluCoordY_neg {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point}
    (hP : P ∉ S) :
    W.veluCoordY S (-P)
      = (W.veluCurve S).negY (W.veluCoordX S P) (W.veluCoordY S P) := by
  have hkey : ∀ Q ∈ S, veluPointY (-P + -Q)
      = -veluPointY (P + Q) - W.a₁ * veluPointX (P + Q) - W.a₃ := by
    intro Q hQ
    have hne : P + Q ≠ 0 := by
      intro h
      refine hP ?_
      have hPQ : P = -Q := by rwa [add_eq_zero_iff_eq_neg] at h
      rw [hPQ]
      exact hS.neg_mem Q hQ
    rw [show (-P + -Q : W.Point) = -(P + Q) by abel, velu_pointY_neg _ hne]
  have h1 : ∑ Q ∈ S, veluPointY (-P + Q)
      = ∑ Q ∈ S, (-veluPointY (P + Q) - W.a₁ * veluPointX (P + Q) - W.a₃) := by
    rw [← Finset.sum_congr rfl hkey]
    exact (velu_sum_neg hS (fun Q => veluPointY (-P + Q))).symm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib,
    Finset.sum_const, nsmul_eq_mul] at h1
  have h2 := velu_sum_kernel hS
  rw [veluCurve_negY]
  unfold veluCoordX veluCoordY
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination h1 - h2

end Identities

/-! ### Vélu's pole expansion of the group-law sums

The classical presentation of Vélu's isogeny writes `X` and `Y` as explicit rational
functions of `(x, y)` whose poles sit at the `x`-coordinates of the kernel. This section
proves that the group-law sums `veluCoordX`/`veluCoordY` ARE those rational functions —
the first half of the two-step route recorded at `velu_equation` below, namely "the
addition law applied to `P + Q` and `P − Q` and summed".

No choice of representatives of `S ∖ {0}` modulo `±` is needed: negation is a bijection
of `S` (`velu_sum_neg`, proven in the previous section), so the sum of a function over `S`
equals the sum of its `±`-symmetrisation halved, and the factor `2⁻¹` below is exactly
that halving. Each summand `veluPoleX`/`veluPoleY` is `±`-invariant and vanishes at the
point at infinity, so the sums may be taken over all of `S`. -/

section Pole

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- Vélu's `u`-term at a point of the kernel, `u_Q = (g^y_Q)² = (2y + a₁x + a₃)²`, with the
junk value `0` at the point at infinity. Like `veluTTerm` it is invariant under `Q ↦ −Q`,
because `g^y` merely changes sign there. Note `veluWTerm = veluUTerm + x · veluTTerm`. -/
def veluUTerm (W : Affine F) : W.Point → F
  | .zero => 0
  | .some x y _ => (2 * y + W.a₁ * x + W.a₃) ^ 2

omit [DecidableEq F] in
@[simp] lemma veluUTerm_zero : veluUTerm W (0 : W.Point) = 0 := rfl

omit [DecidableEq F] in
@[simp] lemma veluUTerm_some {x y : F} (h : W.Nonsingular x y) :
    veluUTerm W (Affine.Point.some x y h) = (2 * y + W.a₁ * x + W.a₃) ^ 2 := rfl

/-- The `x`-part of Vélu's pole expansion at a kernel point `Q`, as a function of the
`x`-coordinate `x` of the point being mapped: `t_Q/(x − x_Q) + u_Q/(x − x_Q)²`. The point
at infinity contributes `0`, since `t_0 = u_0 = 0`. -/
def veluPoleX (W : Affine F) (x : F) (Q : W.Point) : F :=
  veluTTerm W Q / (x - veluPointX Q) + veluUTerm W Q / (x - veluPointX Q) ^ 2

/-- The `y`-part of Vélu's pole expansion at a kernel point `Q`,

  `−[ u_Q(2y + a₁x + a₃)/(x − x_Q)³ + (t_Q(2y + a₁x_Q + a₃) + a₁u_Q)/(2(x − x_Q)²)
      + a₁t_Q/(x − x_Q) ]`.

This is Vélu's `y`-expansion (Kohel's thesis §2.4) rewritten so that every coefficient is
manifestly `±`-invariant: the textbook form carries the summands
`t_Q(a₁(x − x_Q) + y − y_Q)/(x − x_Q)²` and `(a₁u_Q − g^x_Q g^y_Q)/(x − x_Q)²`, neither of
which is invariant on its own, and `t_Q(y − y_Q) + (a₁u_Q − g^x_Q g^y_Q)` collapses to
`(t_Q(2y + a₁x_Q + a₃) + a₁u_Q)/2` using `t_Q = 2g^x_Q − a₁g^y_Q`. The point at infinity
contributes `0`. -/
def veluPoleY (W : Affine F) (x y : F) (Q : W.Point) : F :=
  -(veluUTerm W Q * (2 * y + W.a₁ * x + W.a₃) / (x - veluPointX Q) ^ 3 +
      (veluTTerm W Q * (2 * y + W.a₁ * veluPointX Q + W.a₃) + W.a₁ * veluUTerm W Q) /
        (2 * (x - veluPointX Q) ^ 2) +
      W.a₁ * veluTTerm W Q / (x - veluPointX Q))

omit [DecidableEq F] in
@[simp] lemma veluPoleX_zero (x : F) : veluPoleX W x (0 : W.Point) = 0 := by
  simp [veluPoleX]

omit [DecidableEq F] in
@[simp] lemma veluPoleY_zero (x y : F) : veluPoleY W x y (0 : W.Point) = 0 := by
  simp [veluPoleY]

/-- For `P ∉ S` and `Q` a nonzero point of the subgroup `S`, the `x`-coordinates of `P` and
`Q` differ (PROVEN): equality of `x`-coordinates on a Weierstrass curve forces `P = ±Q`,
and both lie in `S`. This is what makes every summand of Vélu's expansion defined, and it
is also what puts every translate `P ± Q` in the generic (secant) branch of the addition
law, so no case split survives into the computation. -/
lemma velu_X_ne {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point} (hP : P ∉ S)
    {Q : W.Point} (hQ : Q ∈ S) (hQ0 : Q ≠ 0) : veluPointX P ≠ veluPointX Q := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd hS.zero_mem hP
  obtain _ | ⟨x₂, y₂, h₂⟩ := Q
  · exact absurd rfl hQ0
  intro hx
  have hx' : x₁ = x₂ := hx
  rcases (Affine.Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx' with h | h
  · exact hP (by rw [h]; exact hQ)
  · exact hP (by rw [h]; exact hS.neg_mem _ hQ)

omit [DecidableEq F] in
/-- **The `±`-paired addition law in `x`, as a field identity** (PROVEN). Adding the two
secant formulas for `P + Q` and `P − Q` and using the Weierstrass equations at both points
produces Vélu's `x`-pole term. The two slopes are `L₁` and `L₂`; note that `P` and `−Q`
have the same `x`-coordinate difference, so the same denominator occurs twice.

The `linear_combination` cofactors were not guessed: they are the exact cofactors returned
by Singular's `lift` for the ideal generated by the two Weierstrass equations. -/
lemma velu_addX_pair_identity (W : Affine F) {x₁ y₁ x₂ y₂ L₁ L₂ : F} (hd : x₁ - x₂ ≠ 0)
    (hL₁ : L₁ = (y₁ - y₂) / (x₁ - x₂))
    (hL₂ : L₂ = (y₁ - (-y₂ - W.a₁ * x₂ - W.a₃)) / (x₁ - x₂))
    (e₁ : W.Equation x₁ y₁) (e₂ : W.Equation x₂ y₂) :
    L₁ ^ 2 + W.a₁ * L₁ - W.a₂ - x₁ - x₂ - x₂ +
        (L₂ ^ 2 + W.a₁ * L₂ - W.a₂ - x₁ - x₂ - x₂) =
      (6 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) / (x₁ - x₂) +
        (2 * y₂ + W.a₁ * x₂ + W.a₃) ^ 2 / (x₁ - x₂) ^ 2 := by
  rw [Affine.equation_iff] at e₁ e₂
  subst hL₁ hL₂
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp
  linear_combination (2 : F) * e₁ - (2 : F) * e₂

/-- **The `±`-paired addition law in `x`** (PROVEN). For `P, Q` nonzero points of `W` with
distinct `x`-coordinates,
`(x(P + Q) − x(Q)) + (x(P − Q) − x(−Q)) = t_Q/(x − x_Q) + u_Q/(x − x_Q)²`. -/
lemma velu_pair_X {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : veluPointX P ≠ veluPointX Q) :
    veluPointX (P + Q) - veluPointX Q + (veluPointX (P + -Q) - veluPointX (-Q)) =
      veluPoleX W (veluPointX P) Q := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd rfl hP
  obtain _ | ⟨x₂, y₂, h₂⟩ := Q
  · exact absurd rfl hQ
  have hx' : x₁ ≠ x₂ := hx
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx'
  simp only [Affine.Point.neg_some, Affine.Point.add_of_X_ne hx', veluPointX_some, veluPoleX,
    veluTTerm_some, veluUTerm_some, Affine.addX, Affine.negY, Affine.slope_of_X_ne hx']
  linear_combination velu_addX_pair_identity W hd rfl rfl h₁.1 h₂.1

end Pole

section PoleSum

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] {W : Affine F}

omit [DecidableEq F] in
/-- **The `±`-paired addition law in `y`, as a field identity** (PROVEN). Same computation
as `velu_addX_pair_identity` for the `y`-coordinate: `X₁`, `X₂` are the two `addX` values
and the conclusion is Vélu's `y`-pole term. The `linear_combination` cofactors are again
those returned by Singular's `lift`. -/
lemma velu_addY_pair_identity (W : Affine F) {x₁ y₁ x₂ y₂ L₁ L₂ X₁ X₂ : F} (hd : x₁ - x₂ ≠ 0)
    (hL₁ : L₁ = (y₁ - y₂) / (x₁ - x₂))
    (hL₂ : L₂ = (y₁ - (-y₂ - W.a₁ * x₂ - W.a₃)) / (x₁ - x₂))
    (hX₁ : X₁ = L₁ ^ 2 + W.a₁ * L₁ - W.a₂ - x₁ - x₂)
    (hX₂ : X₂ = L₂ ^ 2 + W.a₁ * L₂ - W.a₂ - x₁ - x₂)
    (e₁ : W.Equation x₁ y₁) (e₂ : W.Equation x₂ y₂) :
    -(L₁ * (X₁ - x₁) + y₁) - W.a₁ * X₁ - W.a₃ - y₂ +
        (-(L₂ * (X₂ - x₁) + y₁) - W.a₁ * X₂ - W.a₃ - (-y₂ - W.a₁ * x₂ - W.a₃)) =
      -((2 * y₂ + W.a₁ * x₂ + W.a₃) ^ 2 * (2 * y₁ + W.a₁ * x₁ + W.a₃) / (x₁ - x₂) ^ 3 +
          ((6 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) * (2 * y₁ + W.a₁ * x₂ + W.a₃) +
              W.a₁ * (2 * y₂ + W.a₁ * x₂ + W.a₃) ^ 2) / (2 * (x₁ - x₂) ^ 2) +
          W.a₁ * (6 * x₂ ^ 2 + W.b₂ * x₂ + W.b₄) / (x₁ - x₂)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  rw [Affine.equation_iff] at e₁ e₂
  subst hX₁ hX₂ hL₁ hL₂
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp
  linear_combination (-(4 * W.a₁ * x₁) + 2 * W.a₁ * x₂ - 4 * y₁ - 2 * W.a₃) * e₁ +
    (4 * W.a₁ * x₁ - 2 * W.a₁ * x₂ + 4 * y₁ + 2 * W.a₃) * e₂

/-- **The `±`-paired addition law in `y`** (PROVEN). For `P, Q` nonzero points of `W` with
distinct `x`-coordinates, `(y(P + Q) − y(Q)) + (y(P − Q) − y(−Q)) = veluPoleY`. -/
lemma velu_pair_Y {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : veluPointX P ≠ veluPointX Q) :
    veluPointY (P + Q) - veluPointY Q + (veluPointY (P + -Q) - veluPointY (-Q)) =
      veluPoleY W (veluPointX P) (veluPointY P) Q := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd rfl hP
  obtain _ | ⟨x₂, y₂, h₂⟩ := Q
  · exact absurd rfl hQ
  have hx' : x₁ ≠ x₂ := hx
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx'
  simp only [Affine.Point.neg_some, Affine.Point.add_of_X_ne hx', veluPointX_some,
    veluPointY_some, veluPoleY, veluTTerm_some, veluUTerm_some, Affine.addY, Affine.negAddY,
    Affine.addX, Affine.negY, Affine.slope_of_X_ne hx']
  linear_combination velu_addY_pair_identity W hd rfl rfl rfl rfl h₁.1 h₂.1

/-- **The `±`-pairing of a Vélu sum** (PROVEN). If `g` vanishes at the point at infinity
and symmetrises `f` over each `±`-pair of nonzero points of the subgroup `S`, then the sum
of `f` over `S` is `f 0` plus half the sum of `g`. The reindexing is `velu_sum_neg`:
negation is a bijection of `S`, which is what replaces a choice of representatives modulo
`±`. -/
lemma velu_sum_pair {S : Finset W.Point} (hS : IsPointSubgroup S) (f g : W.Point → F)
    (hg0 : g 0 = 0) (hfg : ∀ Q ∈ S, Q ≠ 0 → f Q + f (-Q) = g Q) :
    ∑ Q ∈ S, f Q = f 0 + (2 : F)⁻¹ * ∑ Q ∈ S, g Q := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hstep : (2 : F) * ∑ Q ∈ S, f Q = ∑ Q ∈ S, (f Q + f (-Q)) := by
    rw [Finset.sum_add_distrib, velu_sum_neg hS f]; ring
  refine mul_left_cancel₀ h2 ?_
  rw [hstep, mul_add, ← mul_assoc, mul_inv_cancel₀ h2, one_mul,
    ← Finset.add_sum_erase S (fun Q => f Q + f (-Q)) hS.zero_mem,
    ← Finset.add_sum_erase S g hS.zero_mem, hg0, zero_add]
  simp only [neg_zero]
  rw [Finset.sum_congr rfl fun Q hQ =>
    hfg Q (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ)]
  ring

/-- **Vélu's `x`-coordinate is Vélu's rational function** (PROVEN). For `P ∉ S`,

  `x(P) + Σ_{Q ∈ S ∖ 0} (x(P + Q) − x(Q)) = x(P) + ½ Σ_{Q ∈ S} veluPoleX`. -/
lemma velu_coordX_eq {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point} (hP : P ∉ S) :
    W.veluCoordX S P = veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hpair : ∀ Q ∈ S, Q ≠ 0 →
      veluPointX (P + Q) - veluPointX Q + (veluPointX (P + -Q) - veluPointX (-Q)) =
        veluPoleX W (veluPointX P) Q := fun Q hQS hQ0 =>
    velu_pair_X hP0 hQ0 (velu_X_ne hS hP hQS hQ0)
  have h := velu_sum_pair hS (fun Q => veluPointX (P + Q) - veluPointX Q)
    (fun Q => veluPoleX W (veluPointX P) Q) (by simp) hpair
  rw [veluCoordX, ← Finset.sum_sub_distrib]
  simpa only [add_zero, veluPointX_zero, sub_zero] using h

/-- **Vélu's `y`-coordinate is Vélu's rational function** (PROVEN). -/
lemma velu_coordY_eq {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point} (hP : P ∉ S) :
    W.veluCoordY S P =
      veluPointY P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hpair : ∀ Q ∈ S, Q ≠ 0 →
      veluPointY (P + Q) - veluPointY Q + (veluPointY (P + -Q) - veluPointY (-Q)) =
        veluPoleY W (veluPointX P) (veluPointY P) Q := fun Q hQS hQ0 =>
    velu_pair_Y hP0 hQ0 (velu_X_ne hS hP hQS hQ0)
  have h := velu_sum_pair hS (fun Q => veluPointY (P + Q) - veluPointY Q)
    (fun Q => veluPoleY W (veluPointX P) (veluPointY P) Q) (by simp) hpair
  rw [veluCoordY, ← Finset.sum_sub_distrib]
  simpa only [add_zero, veluPointY_zero, sub_zero] using h

/-! ### Eliminating `y` from the quotient equation -/

omit [CharZero F] in
/-- The `V`-part of Vélu's pole expansion at a kernel point `Q`:

  `u_Q/(x − x_Q)³ + t_Q/(2(x − x_Q)²)`,

with the junk value `0` at the point at infinity (where `t_0 = u_0 = 0`).

Its role is `velu_pole_V`: the completed square `V := 2Y + a₁X + a₃` of the Vélu
coordinates factors as `V = (2y + a₁x + a₃)·(1 − Σ_{Q ∈ S} veluPoleV)`. Analytically this
is `−½ d/dx` of Vélu's `x`-expansion, but no derivative is needed — the factorisation is
the termwise field identity `velu_two_poleY_add_poleX`, in which `t_Q` and `u_Q` are free
atoms. -/
def veluPoleV (W : Affine F) (x : F) (Q : W.Point) : F :=
  veluUTerm W Q / (x - veluPointX Q) ^ 3 + veluTTerm W Q / (2 * (x - veluPointX Q) ^ 2)

omit [DecidableEq F] [CharZero F] in
@[simp] lemma veluPoleV_zero (x : F) : veluPoleV W x (0 : W.Point) = 0 := by
  simp [veluPoleV]

omit [DecidableEq F] in
/-- **Termwise elimination of `y`** (PROVEN):

  `2·veluPoleY + a₁·veluPoleX = −2(2y + a₁x + a₃)·veluPoleV`.

The `y_Q`-dependence and every `a₁`-contribution cancel. Writing `v = 2y + a₁x + a₃` and
`d = x − x_Q`, the middle numerator of `veluPoleY` is `t_Q(v − a₁d) + a₁u_Q`, so

  `2·veluPoleY = −2u_Q v/d³ − t_Q v/d² + a₁t_Q/d − a₁u_Q/d² − 2a₁t_Q/d`,

and adding `a₁·veluPoleX = a₁t_Q/d + a₁u_Q/d²` leaves exactly `−v(2u_Q/d³ + t_Q/d²)`. The
identity is true with `t_Q`, `u_Q` free — no Weierstrass equation at `Q` is used. -/
lemma velu_two_poleY_add_poleX {x y : F} {Q : W.Point} (hd : Q ≠ 0 → x ≠ veluPointX Q) :
    2 * veluPoleY W x y Q + W.a₁ * veluPoleX W x Q =
      -(2 * (2 * y + W.a₁ * x + W.a₃)) * veluPoleV W x Q := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  · have h : x - veluPointX Q ≠ 0 := sub_ne_zero.mpr (hd hQ)
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    simp only [veluPoleX, veluPoleY, veluPoleV]
    field_simp
    ring

/-- **The completed square of the Vélu coordinates factors** (PROVEN). For `P ∉ S` with
pole-form Vélu coordinates `X`, `Y`,

  `2Y + a₁X + a₃ = (2y + a₁x + a₃)·(1 − Σ_{Q ∈ S} veluPoleV)`.

This is what removes `y` from the quotient equation: the quotient equation in the
completed-square form `V² = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)` then only
involves `y` through `v² = 4x³ + b₂x² + 2b₄x + b₆`. -/
lemma velu_pole_V {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point} (hP : P ∉ S) :
    2 * (veluPointY P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q) +
        W.a₁ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) + W.a₃ =
      (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) *
        (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have key : 2 * (∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q) +
      W.a₁ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q =
      -(2 * (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)) *
        ∑ Q ∈ S, veluPoleV W (veluPointX P) Q := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Q hQS => ?_
    exact velu_two_poleY_add_poleX fun hQ0 => velu_X_ne hS hP hQS hQ0
  field_simp
  linear_combination key

end PoleSum

/-! ### Two-torsion and the discriminant

Two converse statements of general Weierstrass geometry, with no Vélu input at all: a curve
carrying three affine points of order dividing `2` with distinct `x` has `Δ ≠ 0`, and over an
algebraically closed field the converse holds. Both are the assertion that `16 Δ` is the
discriminant of the `2`-division cubic `4x³ + b₂x² + 2b₄x + b₆`, read in the two directions. -/

/-- **PROVEN 2026-07-26** (general Weierstrass geometry, no Vélu input). Over a field of
characteristic zero, a Weierstrass curve carrying three affine points of order dividing `2`
with pairwise distinct `x`-coordinates is nonsingular.

Proof. Substituting `y = negY x y`, i.e. `2y + a₁x + a₃ = 0`, into the Weierstrass equation
turns it into `4x³ + b₂x² + 2b₄x + b₆ = 0`; the hypothesis therefore supplies three distinct
roots `e₁, e₂, e₃` of that cubic. Dividing the differences of the three instances by
`eᵢ − eⱼ` — which is where the distinctness is consumed — solves the resulting Vandermonde
system for the coefficients:

  `b₂ = −4(e₁+e₂+e₃)`,  `b₄ = 2(e₁e₂+e₁e₃+e₂e₃)`,  `b₆ = −4e₁e₂e₃`,

and then `b₈ = 4(e₁+e₂+e₃)e₁e₂e₃ − (e₁e₂+e₁e₃+e₂e₃)²` from `4b₈ = b₂b₆ − b₄²`. Unfolding
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆` and substituting gives the `ring` identity

  `Δ = 16 (e₁−e₂)² (e₁−e₃)² (e₂−e₃)²`

— i.e. `16Δ` is the discriminant of `4x³ + b₂x² + 2b₄x + b₆`, cf. mathlib's
`twoTorsionPolynomial_discr` — so `Δ ≠ 0`. Characteristic zero is used only to divide by
`2` and `4`; characteristic `≠ 2` would do. -/
theorem isElliptic_of_three_twoTorsion {K : Type*} [Field K] [CharZero K]
    {W' : Affine K} {x₁ x₂ x₃ y₁ y₂ y₃ : K}
    (h₁ : W'.Equation x₁ y₁) (h₂ : W'.Equation x₂ y₂) (h₃ : W'.Equation x₃ y₃)
    (t₁ : y₁ = W'.negY x₁ y₁) (t₂ : y₂ = W'.negY x₂ y₂) (t₃ : y₃ = W'.negY x₃ y₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) : W'.IsElliptic := by
  -- Substituting `2y + a₁x + a₃ = 0` into the Weierstrass equation.
  have C : ∀ {x y : K}, W'.Equation x y → y = W'.negY x y →
      4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 := by
    intro x y he ht
    rw [equation_iff'] at he
    have hT : 2 * y + W'.a₁ * x + W'.a₃ = 0 := by
      simp only [negY] at ht; linear_combination ht
    simp only [b₂, b₄, b₆]
    linear_combination (2 * y + W'.a₁ * x + W'.a₃) * hT - 4 * he
  have c₁ := C h₁ t₁
  have c₂ := C h₂ t₂
  have c₃ := C h₃ t₃
  -- Dividing the difference of two instances of the cubic by `u − v`.
  have key : ∀ {u v : K}, u ≠ v →
      4 * u ^ 3 + W'.b₂ * u ^ 2 + 2 * W'.b₄ * u + W'.b₆ = 0 →
      4 * v ^ 3 + W'.b₂ * v ^ 2 + 2 * W'.b₄ * v + W'.b₆ = 0 →
      4 * (u ^ 2 + u * v + v ^ 2) + W'.b₂ * (u + v) + 2 * W'.b₄ = 0 := by
    intro u v huv hu hv
    have hmul : (u - v) * (4 * (u ^ 2 + u * v + v ^ 2) + W'.b₂ * (u + v) + 2 * W'.b₄) = 0 := by
      linear_combination hu - hv
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h) huv
    · exact h
  have A₁₂ := key h₁₂ c₁ c₂
  have A₁₃ := key h₁₃ c₁ c₃
  have hb₂ : W'.b₂ = -4 * (x₁ + x₂ + x₃) := by
    have hmul : (x₂ - x₃) * (4 * (x₁ + x₂ + x₃) + W'.b₂) = 0 := by linear_combination A₁₂ - A₁₃
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h) h₂₃
    · linear_combination h
  have hb₄ : W'.b₄ = 2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
    linear_combination (1 / 2 : K) * A₁₂ - ((x₁ + x₂) / 2) * hb₂
  have hb₆ : W'.b₆ = -4 * (x₁ * x₂ * x₃) := by
    linear_combination c₁ - x₁ ^ 2 * hb₂ - 2 * x₁ * hb₄
  have hb₈ : W'.b₈ = 4 * (x₁ + x₂ + x₃) * (x₁ * x₂ * x₃)
      - (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) ^ 2 := by
    have h := W'.b_relation
    rw [hb₂, hb₄, hb₆] at h
    linear_combination h / 4
  have hΔ : W'.Δ = 16 * ((x₁ - x₂) * (x₁ - x₃) * (x₂ - x₃)) ^ 2 := by
    simp only [WeierstrassCurve.Δ, hb₂, hb₄, hb₆, hb₈]
    ring
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [hΔ]
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁₂) (sub_ne_zero.mpr h₁₃))
      (sub_ne_zero.mpr h₂₃)))

/-- **PROVEN 2026-07-26**, the converse of `isElliptic_of_three_twoTorsion` over an
algebraically closed field: a Weierstrass curve with `Δ ≠ 0` carries three affine points of
order dividing `2` with pairwise distinct `x`-coordinates.

Proof. The `2`-division cubic `4x³ + b₂x² + 2b₄x + b₆` is mathlib's `twoTorsionPolynomial`;
it splits because the field is algebraically closed, and its discriminant is `16 Δ ≠ 0`, so
its three roots `e₁, e₂, e₃` are pairwise distinct (`Cubic.discr_ne_zero_iff_roots_ne`). Each
root `e` is then paired with `y = −(a₁e + a₃)/2`, the unique `y` with `y = negY e y`; the
Weierstrass equation at `(e, y)` is `−1/4` times the cubic, since `4·(equation) =
(2y + a₁e + a₃)² − (4e³ + b₂e² + 2b₄e + b₆)` and the first bracket vanishes identically for
this `y`. -/
theorem exists_three_twoTorsion_of_Δ_ne_zero {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (W' : Affine K) (hΔ : W'.Δ ≠ 0) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃ : K,
      W'.Equation x₁ y₁ ∧ W'.Equation x₂ y₂ ∧ W'.Equation x₃ y₃ ∧
      y₁ = W'.negY x₁ y₁ ∧ y₂ = W'.negY x₂ y₂ ∧ y₃ = W'.negY x₃ y₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  have ha : W'.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : K) ≠ 0
    norm_num
  have hsplits : (W'.twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits := by
    rw [Polynomial.map_id]
    exact IsAlgClosed.splits _
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplits
  have hdiscr : W'.twoTorsionPolynomial.discr ≠ 0 := by
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) hΔ
  obtain ⟨d₁₂, d₁₃, d₂₃⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdiscr
  have hb₂ : W'.b₂ = -4 * (e₁ + e₂ + e₃) := by
    have h := Cubic.b_eq_three_roots ha h3
    simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
    linear_combination h
  have hb₄ : W'.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
    have h := Cubic.c_eq_three_roots ha h3
    simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
    linear_combination h / 2
  have hb₆ : W'.b₆ = -4 * (e₁ * e₂ * e₃) := by
    have h := Cubic.d_eq_three_roots ha h3
    simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
    linear_combination h
  -- From a root of the `2`-division cubic to an affine point of order dividing `2`.
  have E : ∀ e : K, 4 * e ^ 3 + W'.b₂ * e ^ 2 + 2 * W'.b₄ * e + W'.b₆ = 0 →
      W'.Equation e (-(W'.a₁ * e + W'.a₃) / 2) ∧
        (-(W'.a₁ * e + W'.a₃) / 2) = W'.negY e (-(W'.a₁ * e + W'.a₃) / 2) := by
    intro e he
    simp only [b₂, b₄, b₆] at he
    refine ⟨?_, ?_⟩
    · rw [equation_iff']
      linear_combination (-1 / 4 : K) * he
    · simp only [negY]
      ring
  have r₁ : 4 * e₁ ^ 3 + W'.b₂ * e₁ ^ 2 + 2 * W'.b₄ * e₁ + W'.b₆ = 0 := by
    rw [hb₂, hb₄, hb₆]; ring
  have r₂ : 4 * e₂ ^ 3 + W'.b₂ * e₂ ^ 2 + 2 * W'.b₄ * e₂ + W'.b₆ = 0 := by
    rw [hb₂, hb₄, hb₆]; ring
  have r₃ : 4 * e₃ ^ 3 + W'.b₂ * e₃ ^ 2 + 2 * W'.b₄ * e₃ + W'.b₆ = 0 := by
    rw [hb₂, hb₄, hb₆]; ring
  exact ⟨e₁, e₂, e₃, _, _, _, (E e₁ r₁).1, (E e₂ r₂).1, (E e₃ r₃).1,
    (E e₁ r₁).2, (E e₂ r₂).2, (E e₃ r₃).2, d₁₂, d₁₃, d₂₃⟩

/-! ### Base change of the Vélu construction

Everything in this section is PROVEN and purely formal: the Vélu data of `W` and of a finite
subgroup `S` transports along a field extension `F → L`, because `veluTTerm` and `veluWTerm`
are polynomial in the coordinates and `Affine.Point.map` is injective. The content is the
identification

  `(W.veluCurve S)⁄L = (W⁄L).veluCurve (image of S)`,

which is what lets `velu_exists_three_twoTorsion` produce the `2`-torsion of the quotient
over `AlgebraicClosure F` from the `2`-torsion of `W` there. -/

section BaseChangeData

variable {F : Type*} [Field F] {W : Affine F} {L : Type*} [Field L] [Algebra F L]

lemma velu_bc_b₂ : (W⁄L : Affine L).b₂ = algebraMap F L W.b₂ :=
  WeierstrassCurve.map_b₂ (W := W) (f := algebraMap F L)

lemma velu_bc_b₄ : (W⁄L : Affine L).b₄ = algebraMap F L W.b₄ :=
  WeierstrassCurve.map_b₄ (W := W) (f := algebraMap F L)

lemma velu_bc_a₁ : (W⁄L : Affine L).a₁ = algebraMap F L W.a₁ := rfl

lemma velu_bc_a₃ : (W⁄L : Affine L).a₃ = algebraMap F L W.a₃ := rfl

/-- Vélu's `t`-term at an affine point, in terms of the junk-valued coordinate. -/
lemma veluTTerm_of_ne_zero {P : W.Point} (hP : P ≠ 0) :
    veluTTerm W P = 6 * veluPointX P ^ 2 + W.b₂ * veluPointX P + W.b₄ := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

/-- Vélu's `w`-term at an affine point, in terms of the junk-valued coordinates. -/
lemma veluWTerm_of_ne_zero {P : W.Point} (hP : P ≠ 0) :
    veluWTerm W P = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) ^ 2
      + veluPointX P * (6 * veluPointX P ^ 2 + W.b₂ * veluPointX P + W.b₄) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

end BaseChangeData

section BaseChange

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F)
  (L : Type*) [Field L] [DecidableEq L] [Algebra F L]

/-- Base change of points, with the source written as `W.Point` rather than as the
propositionally — but not syntactically — equal `(W⁄F).Point`. Naming the composite is what
keeps the rewrites below from tripping over that mismatch. -/
noncomputable def veluBaseChangePoint : W.Point →+ (W⁄L : Affine L).Point :=
  Affine.Point.baseChange (W' := W) F L

variable {W L}

lemma veluBaseChangePoint_injective :
    Function.Injective (veluBaseChangePoint W L) :=
  Affine.Point.map_injective _

lemma veluBaseChangePoint_ne_zero {P : W.Point} (hP : P ≠ 0) :
    veluBaseChangePoint W L P ≠ 0 := fun hc =>
  hP (veluBaseChangePoint_injective (hc.trans (map_zero (veluBaseChangePoint W L)).symm))

lemma veluBaseChangePoint_pointX (P : W.Point) :
    veluPointX (veluBaseChangePoint W L P) = algebraMap F L (veluPointX P) := by
  cases P with
  | zero =>
      show veluPointX (veluBaseChangePoint W L 0) = algebraMap F L (veluPointX (0 : W.Point))
      rw [map_zero, veluPointX_zero, veluPointX_zero, map_zero]
  | some x y h => rfl

lemma veluBaseChangePoint_pointY (P : W.Point) :
    veluPointY (veluBaseChangePoint W L P) = algebraMap F L (veluPointY P) := by
  cases P with
  | zero =>
      show veluPointY (veluBaseChangePoint W L 0) = algebraMap F L (veluPointY (0 : W.Point))
      rw [map_zero, veluPointY_zero, veluPointY_zero, map_zero]
  | some x y h => rfl

lemma velu_baseChange_TTerm (P : W.Point) :
    veluTTerm (W⁄L : Affine L) (veluBaseChangePoint W L P)
      = algebraMap F L (veluTTerm W P) := by
  by_cases hP : P = 0
  · subst hP
    rw [map_zero, veluTTerm_zero, veluTTerm_zero, map_zero]
  · rw [veluTTerm_of_ne_zero (veluBaseChangePoint_ne_zero hP), veluTTerm_of_ne_zero hP,
      veluBaseChangePoint_pointX, velu_bc_b₂, velu_bc_b₄]
    simp only [map_add, map_mul, map_pow, map_ofNat]

lemma velu_baseChange_WTerm (P : W.Point) :
    veluWTerm (W⁄L : Affine L) (veluBaseChangePoint W L P)
      = algebraMap F L (veluWTerm W P) := by
  by_cases hP : P = 0
  · subst hP
    rw [map_zero, veluWTerm_zero, veluWTerm_zero, map_zero]
  · rw [veluWTerm_of_ne_zero (veluBaseChangePoint_ne_zero hP), veluWTerm_of_ne_zero hP,
      veluBaseChangePoint_pointX, veluBaseChangePoint_pointY, velu_bc_b₂, velu_bc_b₄,
      velu_bc_a₁, velu_bc_a₃]
    simp only [map_add, map_mul, map_pow, map_ofNat]

lemma velu_baseChange_T (S : Finset W.Point) :
    (W⁄L : Affine L).veluT (S.image (veluBaseChangePoint W L))
      = algebraMap F L (W.veluT S) := by
  rw [veluT, veluT, map_mul, map_inv₀, map_ofNat, map_sum,
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h)]
  exact congrArg _ (Finset.sum_congr rfl fun Q _ => velu_baseChange_TTerm Q)

lemma velu_baseChange_W (S : Finset W.Point) :
    (W⁄L : Affine L).veluW (S.image (veluBaseChangePoint W L))
      = algebraMap F L (W.veluW S) := by
  rw [veluW, veluW, map_mul, map_inv₀, map_ofNat, map_sum,
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h)]
  exact congrArg _ (Finset.sum_congr rfl fun Q _ => velu_baseChange_WTerm Q)

/-- **The Vélu quotient commutes with base change** (PROVEN). -/
lemma velu_baseChange_curve (S : Finset W.Point) :
    ((W.veluCurve S)⁄L : Affine L)
      = (W⁄L : Affine L).veluCurve (S.image (veluBaseChangePoint W L)) := by
  refine WeierstrassCurve.ext rfl rfl rfl ?_ ?_
  · show algebraMap F L (W.a₄ - 5 * W.veluT S) = _
    rw [map_sub, map_mul, map_ofNat]
    show _ = (W⁄L : Affine L).a₄ - 5 * (W⁄L : Affine L).veluT _
    rw [velu_baseChange_T]
    rfl
  · show algebraMap F L (W.a₆ - W.b₂ * W.veluT S - 7 * W.veluW S) = _
    rw [map_sub, map_sub, map_mul, map_mul, map_ofNat]
    show _ = (W⁄L : Affine L).a₆ - (W⁄L : Affine L).b₂ * (W⁄L : Affine L).veluT _
      - 7 * (W⁄L : Affine L).veluW _
    rw [velu_baseChange_T, velu_baseChange_W, velu_bc_b₂]
    rfl

/-- The image of a finite subgroup under base change is again one (PROVEN). -/
lemma velu_baseChange_isPointSubgroup {S : Finset W.Point} (hS : IsPointSubgroup S) :
    IsPointSubgroup (S.image (veluBaseChangePoint W L)) where
  zero_mem := Finset.mem_image.mpr ⟨0, hS.zero_mem, map_zero _⟩
  add_mem := by
    rintro P hP Q hQ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hQ
    exact Finset.mem_image.mpr ⟨p + q, hS.add_mem p hp q hq, map_add _ _ _⟩
  neg_mem := by
    rintro P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_image.mpr ⟨-p, hS.neg_mem p hp, map_neg _ _⟩

end BaseChange

section Parity

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- **A nonzero point of order dividing `2` cannot lie in a subgroup of odd order** (PROVEN).

Translation by `T` is a fixed-point-free involution of `S`, so `∏_{Q ∈ S} (−1) = 1` by
`Finset.prod_involution`, while an odd exponent makes that product `−1`. This is where the
ODDNESS of the kernel enters `velu_exists_three_twoTorsion`. -/
lemma velu_twoTorsion_notMem {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {T : W.Point} (hT0 : T ≠ 0) (hT2 : -T = T) : T ∉ S := by
  intro hT
  have hTT : T + T = 0 := add_eq_zero_iff_eq_neg.mpr hT2.symm
  have hprod : ∏ _Q ∈ S, (-1 : ℤ) = 1 :=
    Finset.prod_involution (fun Q _ => Q + T) (fun a _ => by norm_num)
      (fun a _ _ hc => hT0 (add_left_cancel (a := a) (by rw [add_zero]; exact hc)))
      (fun a ha => hS.add_mem a ha T hT)
      (fun a _ => by rw [add_assoc, hTT, add_zero])
  rw [Finset.prod_const, hodd.neg_one_pow] at hprod
  norm_num at hprod

end Parity

/-! ### The generic point of a Weierstrass curve

The affine coordinate ring `F[W] = F[X, Y]/(W(X, Y))` of `W` (mathlib's
`WeierstrassCurve.Affine.CoordinateRing`) is a domain, so it embeds into its fraction field, over
which `(X, Y)` is an honest point of `W` — the GENERIC point. Two features of it are what the
"no poles" leaf below needs:

* `X - x₀` is nonzero for every `x₀ ∈ F` (`velu_gen_ne`), so the generic point avoids the kernel
  and every denominator of the addition law is invertible;
* evaluation at an affine point of `W` is a ring homomorphism `F[W] → F` (`veluEvalAt`) killing
  `X - x₀`, which is how a divisibility by `(X - x₀)^8` is read off.

Nothing here is specific to Vélu's construction. -/

section GenericPoint

variable {F : Type*} [Field F] {W : Affine F}

/-- The `x`-coordinate of the generic point: the image of `X` in the affine coordinate ring. -/
noncomputable def veluGenX (W : Affine F) : W.CoordinateRing :=
  AdjoinRoot.of W.polynomial Polynomial.X

/-- The `y`-coordinate of the generic point: the image of `Y` in the affine coordinate ring. -/
noncomputable def veluGenY (W : Affine F) : W.CoordinateRing :=
  AdjoinRoot.root W.polynomial

lemma velu_of_C (c : F) :
    AdjoinRoot.of W.polynomial (Polynomial.C c) = algebraMap F W.CoordinateRing c := by
  rw [AdjoinRoot.algebraMap_eq']
  rfl

lemma velu_of_injective : Function.Injective (AdjoinRoot.of W.polynomial) := by
  intro p q hpq
  have h : (p - q) • (1 : W.CoordinateRing)
      + (0 : Polynomial F) • Affine.CoordinateRing.mk W Polynomial.X = 0 := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one, AdjoinRoot.algebraMap_eq, map_sub, hpq,
      sub_self]
  exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero h).1

lemma velu_gen_eval (q : Polynomial F) :
    Polynomial.eval (veluGenX W) (q.map (algebraMap F W.CoordinateRing))
      = AdjoinRoot.of W.polynomial q := by
  rw [Polynomial.eval_map]
  conv_rhs => rw [← Polynomial.eval₂_C_X (p := q)]
  rw [Polynomial.hom_eval₂]
  rfl

section MapCoeffs

variable {R : Type*} [CommRing R] [Algebra F R]

lemma velu_ma₁ : (W⁄R : Affine R).a₁ = algebraMap F R W.a₁ := rfl
lemma velu_ma₂ : (W⁄R : Affine R).a₂ = algebraMap F R W.a₂ := rfl
lemma velu_ma₃ : (W⁄R : Affine R).a₃ = algebraMap F R W.a₃ := rfl
lemma velu_ma₄ : (W⁄R : Affine R).a₄ = algebraMap F R W.a₄ := rfl
lemma velu_ma₆ : (W⁄R : Affine R).a₆ = algebraMap F R W.a₆ := rfl

end MapCoeffs

lemma velu_gen_equation :
    (W⁄W.CoordinateRing : Affine W.CoordinateRing).Equation (veluGenX W) (veluGenY W) := by
  have h : AdjoinRoot.mk W.polynomial (Polynomial.X ^ 2
      + Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) * Polynomial.X
      - Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
          + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)) = 0 := by
    rw [← Affine.polynomial]
    exact AdjoinRoot.mk_self
  have hC : ∀ q : Polynomial F,
      AdjoinRoot.mk W.polynomial (Polynomial.C q) = AdjoinRoot.of W.polynomial q := fun _ => rfl
  have hY : AdjoinRoot.mk W.polynomial Polynomial.X = veluGenY W := rfl
  have hX : AdjoinRoot.of W.polynomial Polynomial.X = veluGenX W := rfl
  simp only [map_sub, map_add, map_mul, map_pow, hC, hY, hX, velu_of_C] at h
  rw [Affine.equation_iff, velu_ma₁, velu_ma₂, velu_ma₃, velu_ma₄, velu_ma₆]
  linear_combination h

lemma velu_gen_ne (c : F) : veluGenX W - algebraMap F W.CoordinateRing c ≠ 0 := by
  intro hc
  have h : AdjoinRoot.of W.polynomial (Polynomial.X - Polynomial.C c) = 0 := by
    rw [map_sub, velu_of_C]; exact hc
  exact Polynomial.X_sub_C_ne_zero c
    (velu_of_injective (h.trans (map_zero (AdjoinRoot.of W.polynomial)).symm))

/-- `X - x₀` in the affine coordinate ring. -/
noncomputable def veluGenD (W : Affine F) (x₀ : F) : W.CoordinateRing :=
  veluGenX W - algebraMap F W.CoordinateRing x₀

/-- `(X - x₀)²` times the `x`-coordinate of the translate of the generic point by `-Q`. -/
noncomputable def veluGenN (W : Affine F) (x₀ y₀ : F) : W.CoordinateRing :=
  (veluGenY W - algebraMap F W.CoordinateRing (W.negY x₀ y₀)) ^ 2
    + algebraMap F W.CoordinateRing W.a₁
        * (veluGenY W - algebraMap F W.CoordinateRing (W.negY x₀ y₀)) * veluGenD W x₀
    - (algebraMap F W.CoordinateRing W.a₂ + veluGenX W + algebraMap F W.CoordinateRing x₀)
        * veluGenD W x₀ ^ 2

lemma velu_gen_evalL {L : Type*} [Field L] [Algebra F L] [Algebra W.CoordinateRing L]
    (htower : (algebraMap F L)
      = (algebraMap W.CoordinateRing L).comp (algebraMap F W.CoordinateRing))
    (p : Polynomial F) :
    (p.map (algebraMap F L)).eval (algebraMap W.CoordinateRing L (veluGenX W))
      = algebraMap W.CoordinateRing L (AdjoinRoot.of W.polynomial p) := by
  rw [htower, ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
    velu_gen_eval]

/-- Evaluation of the affine coordinate ring at an affine point of the curve. -/
noncomputable def veluEvalAt {x₀ y₀ : F} (h : W.Equation x₀ y₀) : W.CoordinateRing →+* F :=
  AdjoinRoot.lift (Polynomial.evalRingHom x₀) y₀ (by
    rw [Affine.polynomial]
    rw [Affine.equation_iff] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    linear_combination h)

lemma veluEvalAt_of {x₀ y₀ : F} (h : W.Equation x₀ y₀) (q : Polynomial F) :
    veluEvalAt h (AdjoinRoot.of W.polynomial q) = q.eval x₀ := by
  show AdjoinRoot.lift _ _ _ (AdjoinRoot.mk W.polynomial (Polynomial.C q)) = _
  rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C, Polynomial.coe_evalRingHom]

lemma veluEvalAt_genX {x₀ y₀ : F} (h : W.Equation x₀ y₀) : veluEvalAt h (veluGenX W) = x₀ := by
  rw [veluGenX, veluEvalAt_of, Polynomial.eval_X]

lemma veluEvalAt_genY {x₀ y₀ : F} (h : W.Equation x₀ y₀) : veluEvalAt h (veluGenY W) = y₀ :=
  AdjoinRoot.lift_root _

lemma veluEvalAt_algebraMap {x₀ y₀ : F} (h : W.Equation x₀ y₀) (c : F) :
    veluEvalAt h (algebraMap F W.CoordinateRing c) = c := by
  rw [← velu_of_C, veluEvalAt_of, Polynomial.eval_C]

lemma velu_eval_scaled {K : Type*} [Field K] (p : Polynomial K) (Nv e z : K)
    (D : ℕ) (hD : p.natDegree ≤ D) (hz : z * e = Nv) :
    p.eval z * e ^ D = ∑ j ∈ Finset.range (D + 1), p.coeff j * Nv ^ j * e ^ (D - j) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc p.coeff j * z ^ j * e ^ D
      = p.coeff j * (z * e) ^ j * e ^ (D - j) := by
        rw [mul_pow, ← pow_mul_pow_sub e hjD]; ring
    _ = p.coeff j * Nv ^ j * e ^ (D - j) := by rw [hz]

end GenericPoint


/-! ### Vélu's rational-function identity, cleared of denominators

The single remaining arithmetic input to Vélu's theorem is the ONE-VARIABLE identity

  `Ψ(x)·(1 − D)² = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)`,

`Ψ(x) = 4x³ + b₂x² + 2b₄x + b₆`, `X = x + ½ Σ_{Q ∈ S} veluPoleX`, `D = Σ_{Q ∈ S} veluPoleV`
— `velu_pole_identity` at the end of this section. `velu_pole_V` has already eliminated `y`,
so nothing here mentions it.

**It is a RATIONAL-FUNCTION identity in `x`, not merely an identity at `x`-coordinates of
points** (checked in PARI/GP over `𝔽_p`, `101 ≤ p ≤ 200`, odd kernels: 761 random values of
`x` — unrelated to any point of the curve — all pass). That is what this section exploits:
clearing denominators turns it into an identity of POLYNOMIALS, `veluTheta S = 0`, and the
classical two-part argument becomes a divisibility statement plus a degree statement.

The bookkeeping. Write `S' = S ∖ {0}`, `n = |S'| = |S| − 1`, and (this is where `hodd` is
used) note that every `x_Q`, `Q ∈ S'`, is attained by EXACTLY TWO points of `S'`, namely
`±Q`, since a subgroup of odd order has no `2`-torsion (`velu_twoTorsion_notMem`). With

* `H  = veluH S  = ∏_{Q ∈ S'} (T − x_Q)`                    (monic, degree `n`),
* `Hq_Q = veluHq S Q = H / (T − x_Q)²`                       (`veluH_factor`),
* `PX = veluPX S = Σ_{Q ∈ S'} (t_Q(T − x_Q) + u_Q)·Hq_Q`     (degree `≤ n − 1`),
* `PV = veluPV S = Σ_{Q ∈ S'} (u_Q(T − x_Q) + ½t_Q(T − x_Q)²)·Hq_Q²`  (degree `≤ 2n − 2`),

one has `PX/H = Σ veluPoleX` and `PV/H² = Σ veluPoleV` (`veluPX_eval`, `veluPV_eval`) — the
point of the pairing is that `(T − x_Q)²` divides `H` and `(T − x_Q)³` divides `H²`, so both
numerators are honest polynomials with no choice of representatives modulo `±` anywhere.
Hence `veluXi S = H² − PV` is `H²(1 − D)`, `veluXNum S = T·H + ½PX` is `H·X`, and

  `veluTheta S = Ψ·(veluXi S)² − H·(veluPhiNum S)`

is `H⁴` times the difference of the two sides of the identity. So `veluTheta S = 0` gives
the identity back after dividing by `H(x)⁴ ≠ 0`.

`veluTheta S` has degree `≤ 4n + 2` (the degree-`4n + 3` terms cancel because `H` is monic
and both sides are `4x³ + …`), and `deg H⁴ = 4n`, so `veluTheta S = 0` follows from

1. `velu_theta_local_dvd` — `(T − x_Q)⁸ ∣ veluTheta S` for each `Q ∈ S'` (the LOCAL form of
   "no poles": `H⁴ = ∏_{r} (T − x_r)⁸` over the `n/2` distinct roots, and the eight orders
   are `2` from the explicit factor `H` plus the six of the classical `h⁶`), and
2. `velu_theta_degree_lt` — `deg (veluTheta S) < 4n` ("vanishing at infinity").

**The two halves are cleanly separated by the subgroup hypothesis**, which is what makes
this the right cut. Measured in PARI/GP on `±`-stable NON-subgroups `S = {0} ∪ {±G, …, ±kG}`
(`k = 1, 2, 3`; `101 ≤ p ≤ 200`), for which every definition above is equally well posed:
`deg (veluTheta S) < 4n` held in **248 of 248** instances, while `H⁴ ∣ veluTheta S` failed in
**248 of 248**. So the degree half needs only `±`-stability, and ALL of the arithmetic
content — closure of `S` under addition — sits in the local divisibility half. -/

section PolePoly

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] {W : Affine F}

/-- `H = ∏_{Q ∈ S ∖ {0}} (T − x_Q)`, the polynomial whose vanishing locus carries every
pole of Vélu's rational functions. Each root occurs twice (from `±Q`) when `S` has odd
order. -/
noncomputable def veluH (S : Finset W.Point) : Polynomial F :=
  ∏ Q ∈ S.erase 0, (Polynomial.X - Polynomial.C (veluPointX Q))

/-- `veluH` with the `±`-pair of `Q` removed, i.e. `veluH S / (T − x_Q)²`. -/
noncomputable def veluHq (S : Finset W.Point) (Q : W.Point) : Polynomial F :=
  ∏ Q' ∈ ((S.erase 0).erase Q).erase (-Q), (Polynomial.X - Polynomial.C (veluPointX Q'))

omit [CharZero F] in
/-- **PROVEN.** `veluH S = (T − x_Q)²·veluHq S Q`: the `x`-coordinate of a nonzero `Q` in an
odd-order subgroup is attained by exactly the two points `±Q`, so the linear factor occurs
squared. This is the ONE place `hodd` is consumed in this section. -/
lemma veluH_factor {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    veluH S = (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2 * veluHq S Q := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
  have hne : -Q ≠ Q := fun h => velu_twoTorsion_notMem hS hodd hQ0 h hQS
  have h1 : -Q ∈ (S.erase 0).erase Q :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
  rw [veluH, ← Finset.mul_prod_erase _ _ hQ, ← Finset.mul_prod_erase _ _ h1, veluHq,
    velu_pointX_neg]
  ring

/-- Numerator of `Σ_{Q ∈ S} veluPoleX` over `veluH`. -/
noncomputable def veluPX (S : Finset W.Point) : Polynomial F :=
  ∑ Q ∈ S.erase 0,
    (Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
      + Polynomial.C (veluUTerm W Q)) * veluHq S Q

/-- Numerator of `Σ_{Q ∈ S} veluPoleV` over `veluH²`. -/
noncomputable def veluPV (S : Finset W.Point) : Polynomial F :=
  ∑ Q ∈ S.erase 0,
    (Polynomial.C (veluUTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
      + Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
          * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2) * (veluHq S Q) ^ 2

/-- `veluH² · (1 − D)`, monic of degree `2n`. -/
noncomputable def veluXi (S : Finset W.Point) : Polynomial F := (veluH S) ^ 2 - veluPV S

/-- `veluH · X`, where `X = x + ½ Σ veluPoleX` is Vélu's `x`-coordinate. -/
noncomputable def veluXNum (S : Finset W.Point) : Polynomial F :=
  Polynomial.X * veluH S + Polynomial.C ((2 : F)⁻¹) * veluPX S

/-- The `2`-division cubic `Ψ = 4T³ + b₂T² + 2b₄T + b₆` of `W`, i.e. the completed square of
the Weierstrass equation. -/
noncomputable def veluPsi (W : Affine F) : Polynomial F :=
  Polynomial.C (4 : F) * Polynomial.X ^ 3 + Polynomial.C W.b₂ * Polynomial.X ^ 2
    + Polynomial.C (2 * W.b₄) * Polynomial.X + Polynomial.C W.b₆

/-- `veluH³ · Φ(X)`, where `Φ(T) = 4T³ + b₂T² + (2b₄ − 20t)T + (b₆ − 4b₂t − 28w)` is the
`2`-division cubic of the quotient curve `veluCurve W S`. -/
noncomputable def veluPhiNum (S : Finset W.Point) : Polynomial F :=
  Polynomial.C (4 : F) * (veluXNum S) ^ 3 + Polynomial.C W.b₂ * (veluXNum S) ^ 2 * veluH S
    + Polynomial.C (2 * W.b₄ - 20 * W.veluT S) * veluXNum S * (veluH S) ^ 2
    + Polynomial.C (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S) * (veluH S) ^ 3

/-- `Θ = Ψ·Ξ² − H·Φ_num`, i.e. `veluH⁴` times the difference of the two sides of
`velu_pole_identity`. The whole remaining content of Vélu's theorem is `veluTheta S = 0`. -/
noncomputable def veluTheta (S : Finset W.Point) : Polynomial F :=
  veluPsi W * (veluXi S) ^ 2 - veluH S * veluPhiNum S

omit [CharZero F] in
lemma veluH_monic (S : Finset W.Point) : (veluH S).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

omit [CharZero F] in
lemma veluH_natDegree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluH S).natDegree = S.card - 1 := by
  rw [veluH, Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero _)]
  simp [Finset.card_erase_of_mem hS.zero_mem]

omit [CharZero F] in
lemma veluH_pow_degree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    ((veluH S) ^ 4).degree = ((4 * (S.card - 1) : ℕ) : WithBot ℕ) := by
  have hne : ((veluH S) ^ 4) ≠ 0 := ((veluH_monic S).pow 4).ne_zero
  rw [Polynomial.degree_eq_natDegree hne, Polynomial.natDegree_pow, veluH_natDegree hS]

omit [CharZero F] in
/-- **PROVEN.** `veluH` does not vanish at the `x`-coordinate of a point outside `S`; this is
`velu_X_ne`, and it is what lets the polynomial identity be divided back down. -/
lemma veluH_eval_ne_zero {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point}
    (hP : P ∉ S) : (veluH S).eval (veluPointX P) ≠ 0 := by
  rw [veluH, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr
    (velu_X_ne hS hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))

omit [CharZero F] in
/-- **PROVEN.** `veluPX S / veluH S = Σ_{Q ∈ S} veluPoleX`, in cleared form. -/
lemma veluPX_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluPX S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P) * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q := by
  rw [← Finset.sum_erase S (veluPoleX_zero (W := W) (veluPointX P)), veluPX,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hd : veluPointX P - veluPointX Q ≠ 0 := sub_ne_zero.mpr
    (velu_X_ne hS hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))
  rw [veluH_factor hS hodd hQ]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, veluPoleX]
  field_simp

/-- **PROVEN.** `veluPV S / (veluH S)² = Σ_{Q ∈ S} veluPoleV`, in cleared form. -/
lemma veluPV_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluPV S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 2 * ∑ Q ∈ S, veluPoleV W (veluPointX P) Q := by
  rw [← Finset.sum_erase S (veluPoleV_zero (W := W) (veluPointX P)), veluPV,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hd : veluPointX P - veluPointX Q ≠ 0 := sub_ne_zero.mpr
    (velu_X_ne hS hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))
  rw [veluH_factor hS hodd hQ]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, veluPoleV]
  field_simp

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN.** Two nonzero points with the same `x`-coordinate are equal or opposite. -/
lemma velu_pointX_eq_iff {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : veluPointX P = veluPointX Q) : P = Q ∨ P = -Q := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd rfl hP
  obtain _ | ⟨x₂, y₂, h₂⟩ := Q
  · exact absurd rfl hQ
  exact (Affine.Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp h

omit [CharZero F] in
/-- **PROVEN.** The fibre of `veluPointX` over `x_Q` inside `S ∖ {0}` is exactly `{Q, −Q}`. -/
lemma velu_fiber {S : Finset W.Point} (hS : IsPointSubgroup S) {Q : W.Point}
    (hQ : Q ∈ S.erase 0) :
    {Q' ∈ S.erase 0 | veluPointX Q' = veluPointX Q} = {Q, -Q} := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
  ext Q'
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hQ'0, hQ'S⟩, hx⟩
    exact velu_pointX_eq_iff hQ'0 hQ0 hx
  · rintro (rfl | rfl)
    · exact ⟨⟨hQ0, hQS⟩, rfl⟩
    · exact ⟨⟨hnQ0, hS.neg_mem _ hQS⟩, velu_pointX_neg Q⟩

omit [CharZero F] in
lemma velu_fiber_card {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    ({Q' ∈ S.erase 0 | veluPointX Q' = veluPointX Q}).card = 2 := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  have hne : -Q ≠ Q := fun h => velu_twoTorsion_notMem hS hodd hQ0 h hQS
  rw [velu_fiber hS hQ, Finset.card_insert_of_notMem (by simpa using fun h => hne h.symm),
    Finset.card_singleton]

omit [CharZero F] in
/-- **PROVEN.** `veluH⁴ = ∏_{r} (T − x_r)⁸` over the `(|S| − 1)/2` DISTINCT roots: every root
of `veluH` is double, so the fourth power is an eighth power fibrewise. -/
lemma veluH_pow_eq {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluH S) ^ 4
      = ∏ a ∈ (S.erase 0).image veluPointX, (Polynomial.X - Polynomial.C a) ^ 8 := by
  rw [veluH, ← Finset.prod_pow, ← Finset.prod_fiberwise_of_maps_to
    (g := veluPointX) (t := (S.erase 0).image veluPointX)
    (fun i hi => Finset.mem_image_of_mem _ hi)
    (fun Q => (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 4)]
  refine Finset.prod_congr rfl fun a ha => ?_
  have hcard : ({Q' ∈ S.erase 0 | veluPointX Q' = a}).card = 2 := by
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
    exact velu_fiber_card hS hodd hQ
  calc ∏ Q' ∈ {Q' ∈ S.erase 0 | veluPointX Q' = a},
        (Polynomial.X - Polynomial.C (veluPointX Q')) ^ 4
      = ∏ _Q' ∈ {Q' ∈ S.erase 0 | veluPointX Q' = a}, (Polynomial.X - Polynomial.C a) ^ 4 :=
        Finset.prod_congr rfl fun Q' hQ' => by rw [(Finset.mem_filter.mp hQ').2]
    _ = ((Polynomial.X - Polynomial.C a) ^ 4) ^ 2 := by rw [Finset.prod_const, hcard]
    _ = (Polynomial.X - Polynomial.C a) ^ 8 := by ring

omit [DecidableEq F] [CharZero F] in
lemma veluUTerm_of_ne_zero {P : W.Point} (hP : P ≠ 0) :
    veluUTerm W P = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) ^ 2 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

omit [DecidableEq F] [CharZero F] in
/-- The `2`-division cubic at a solution of the Weierstrass equation. -/
lemma velu_psi_eval_eq {x y : F} (h : W.Equation x y) :
    (veluPsi W).eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [Affine.equation_iff] at h
  simp only [veluPsi, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  linear_combination -4 * h

omit [DecidableEq F] [CharZero F] in
/-- The `2`-division cubic evaluated at a point is the square of the completed square. -/
lemma velu_psi_eval {P : W.Point} (hP : P ≠ 0) :
    (veluPsi W).eval (veluPointX P)
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) ^ 2 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact velu_psi_eval_eq h.1

lemma veluXNum_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluXNum S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P) * W.veluCoordX S P := by
  rw [veluXNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, veluPX_eval hS hodd hP, velu_coordX_eq hS hP]
  ring

lemma veluXi_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluXi S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 2
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
  rw [veluXi, Polynomial.eval_sub, Polynomial.eval_pow, veluPV_eval hS hodd hP]
  ring

lemma veluPhiNum_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluPhiNum S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 3
        * (4 * (W.veluCoordX S P) ^ 3 + W.b₂ * (W.veluCoordX S P) ^ 2
            + (2 * W.b₄ - 20 * W.veluT S) * W.veluCoordX S P
            + (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S)) := by
  simp only [veluPhiNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C]
  rw [veluXNum_eval hS hodd hP]
  ring

/-- **PROVEN.** The value of `veluTheta` at the `x`-coordinate of a point outside the kernel
is `veluH⁴` times the quotient-curve defect of the Vélu image of that point. -/
lemma velu_theta_eval {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (veluTheta S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 4
        * ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) ^ 2
            - (4 * (W.veluCoordX S P) ^ 3 + W.b₂ * (W.veluCoordX S P) ^ 2
              + (2 * W.b₄ - 20 * W.veluT S) * W.veluCoordX S P
              + (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S))) := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hV : 2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
    rw [velu_coordX_eq hS hP, velu_coordY_eq hS hP]
    exact velu_pole_V hS hP
  rw [veluTheta, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_pow, velu_psi_eval hP0, veluXi_eval hS hodd hP,
    veluPhiNum_eval hS hodd hP]
  linear_combination (-(((veluH S).eval (veluPointX P)) ^ 4
    * ((2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q)
      + (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)))) * hV

section PolePolyBaseChange

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L] [Algebra F L]

omit [DecidableEq F] [DecidableEq L] [CharZero F] [CharZero L] in
lemma velu_bc_b₆ : (W⁄L : Affine L).b₆ = algebraMap F L W.b₆ :=
  WeierstrassCurve.map_b₆ (W := W) (f := algebraMap F L)

omit [CharZero F] [CharZero L] in
lemma velu_baseChange_UTerm (P : W.Point) :
    veluUTerm (W⁄L : Affine L) (veluBaseChangePoint W L P)
      = algebraMap F L (veluUTerm W P) := by
  by_cases hP : P = 0
  · subst hP; rw [map_zero, veluUTerm_zero, veluUTerm_zero, map_zero]
  · rw [veluUTerm_of_ne_zero (veluBaseChangePoint_ne_zero hP), veluUTerm_of_ne_zero hP,
      veluBaseChangePoint_pointX, veluBaseChangePoint_pointY, velu_bc_a₁, velu_bc_a₃]
    simp only [map_add, map_mul, map_pow, map_ofNat]

omit [CharZero F] [CharZero L] in
lemma velu_bc_erase (S : Finset W.Point) :
    (S.erase 0).image (veluBaseChangePoint W L)
      = (S.image (veluBaseChangePoint W L)).erase 0 := by
  rw [Finset.image_erase veluBaseChangePoint_injective, map_zero]

omit [CharZero F] [CharZero L] in
lemma velu_bc_H (S : Finset W.Point) :
    veluH (S.image (veluBaseChangePoint W L)) = (veluH S).map (algebraMap F L) := by
  rw [veluH, veluH, Polynomial.map_prod, ← velu_bc_erase,
    Finset.prod_image (fun a _ b _ h => veluBaseChangePoint_injective h)]
  refine Finset.prod_congr rfl fun Q _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, veluBaseChangePoint_pointX]

omit [CharZero F] [CharZero L] in
lemma velu_bc_Hq (S : Finset W.Point) (Q : W.Point) :
    veluHq (S.image (veluBaseChangePoint W L)) (veluBaseChangePoint W L Q)
      = (veluHq S Q).map (algebraMap F L) := by
  have hinj := veluBaseChangePoint_injective (W := W) (L := L)
  have hset : (((S.image (veluBaseChangePoint W L)).erase 0).erase
        (veluBaseChangePoint W L Q)).erase (-(veluBaseChangePoint W L Q))
      = (((S.erase 0).erase Q).erase (-Q)).image (veluBaseChangePoint W L) := by
    rw [Finset.image_erase hinj, Finset.image_erase hinj, Finset.image_erase hinj, map_zero,
      map_neg]
  rw [veluHq, veluHq, Polynomial.map_prod, hset,
    Finset.prod_image (fun a _ b _ h => hinj h)]
  refine Finset.prod_congr rfl fun Q' _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, veluBaseChangePoint_pointX]

omit [CharZero F] [CharZero L] in
lemma velu_bc_PX (S : Finset W.Point) :
    veluPX (S.image (veluBaseChangePoint W L)) = (veluPX S).map (algebraMap F L) := by
  have hinj := veluBaseChangePoint_injective (W := W) (L := L)
  rw [veluPX, veluPX, Polynomial.map_sum, ← velu_bc_erase,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
    velu_bc_Hq, velu_baseChange_TTerm, velu_baseChange_UTerm, veluBaseChangePoint_pointX]

omit [CharZero F] [CharZero L] in
lemma velu_bc_PV (S : Finset W.Point) :
    veluPV (S.image (veluBaseChangePoint W L)) = (veluPV S).map (algebraMap F L) := by
  have hinj := veluBaseChangePoint_injective (W := W) (L := L)
  rw [veluPV, veluPV, Polynomial.map_sum, ← velu_bc_erase,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [velu_bc_Hq, velu_baseChange_TTerm, velu_baseChange_UTerm, veluBaseChangePoint_pointX]
  simp only [map_mul, map_inv₀, map_ofNat]

omit [CharZero F] [CharZero L] in
lemma velu_bc_Xi (S : Finset W.Point) :
    veluXi (S.image (veluBaseChangePoint W L)) = (veluXi S).map (algebraMap F L) := by
  rw [veluXi, veluXi, Polynomial.map_sub, Polynomial.map_pow, velu_bc_H, velu_bc_PV]

omit [CharZero F] [CharZero L] in
lemma velu_bc_XNum (S : Finset W.Point) :
    veluXNum (S.image (veluBaseChangePoint W L)) = (veluXNum S).map (algebraMap F L) := by
  rw [veluXNum, veluXNum, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, velu_bc_H, velu_bc_PX]
  simp only [map_inv₀, map_ofNat]

omit [DecidableEq F] [DecidableEq L] [CharZero F] [CharZero L] in
lemma velu_bc_Psi : veluPsi (W⁄L : Affine L) = (veluPsi W).map (algebraMap F L) := by
  rw [veluPsi, veluPsi, Polynomial.map_add, Polynomial.map_add, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_X, velu_bc_b₂, velu_bc_b₄, velu_bc_b₆]
  simp only [map_mul, map_ofNat]

omit [CharZero F] [CharZero L] in
lemma velu_bc_PhiNum (S : Finset W.Point) :
    veluPhiNum (S.image (veluBaseChangePoint W L)) = (veluPhiNum S).map (algebraMap F L) := by
  simp only [veluPhiNum, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C]
  rw [velu_bc_H, velu_bc_XNum, velu_bc_b₂, velu_bc_b₄, velu_bc_b₆, velu_baseChange_T,
    velu_baseChange_W]
  simp only [map_mul, map_sub, map_ofNat]

omit [CharZero F] [CharZero L] in
lemma velu_bc_Theta (S : Finset W.Point) :
    veluTheta (S.image (veluBaseChangePoint W L)) = (veluTheta S).map (algebraMap F L) := by
  rw [veluTheta, veluTheta, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, velu_bc_Psi, velu_bc_Xi, velu_bc_H, velu_bc_PhiNum]

end PolePolyBaseChange

/-- **PROVEN.** Translation invariance of the values of `veluTheta`. -/
lemma velu_theta_translate {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P R : W.Point} (hR : R ∈ S) (hP : P ∉ S) :
    (veluTheta S).eval (veluPointX (P + R)) * ((veluH S).eval (veluPointX P)) ^ 4
      = (veluTheta S).eval (veluPointX P) * ((veluH S).eval (veluPointX (P + R))) ^ 4 := by
  have hPR : P + R ∉ S := by
    intro hc
    exact hP (by simpa using hS.add_mem _ hc _ (hS.neg_mem R hR))
  rw [velu_theta_eval hS hodd hP, velu_theta_eval hS hodd hPR,
    veluCoordX_add_mem hS P hR, veluCoordY_add_mem hS P hR]
  ring

/-- **The translation identity, transported to the affine coordinate ring.**

Over any field `L` receiving `W.CoordinateRing`, the generic point `(X, Y)` and its translate
by `-Q` have the same Vélu image, so their `veluTheta` values agree up to the fourth power of
`veluH`.  Clearing the denominator `(X - x_Q)^2` of the translate's `x`-coordinate turns that
into an identity of elements of the coordinate ring. -/
lemma velu_theta_key_over (L : Type*) [Field L] [DecidableEq L] [CharZero L] [Algebra F L]
    [Algebra W.CoordinateRing L]
    (htower : algebraMap F L
      = (algebraMap W.CoordinateRing L).comp (algebraMap F W.CoordinateRing))
    (hinj : Function.Injective (algebraMap W.CoordinateRing L))
    {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (hdeg : (veluTheta S).natDegree ≤ 4 * (S.card - 1))
    {x₀ y₀ : F} (hQns : W.Nonsingular x₀ y₀)
    (hQ : Affine.Point.some x₀ y₀ hQns ∈ S.erase 0) :
    AdjoinRoot.of W.polynomial (veluTheta S)
        * (∏ Q' ∈ S.erase 0, (veluGenN W x₀ y₀
            - algebraMap F W.CoordinateRing (veluPointX Q') * veluGenD W x₀ ^ 2)) ^ 4
      = (∑ j ∈ Finset.range (4 * (S.card - 1) + 1),
            algebraMap F W.CoordinateRing ((veluTheta S).coeff j) * veluGenN W x₀ y₀ ^ j
              * (veluGenD W x₀ ^ 2) ^ (4 * (S.card - 1) - j))
          * veluGenD W x₀ ^ 8
          * AdjoinRoot.of W.polynomial (veluHq S (Affine.Point.some x₀ y₀ hQns)) ^ 4 := by
  have hφ : ∀ c : F,
      algebraMap W.CoordinateRing L (algebraMap F W.CoordinateRing c) = algebraMap F L c :=
    fun c => by rw [htower]; rfl
  refine hinj ?_
  have hxne : ∀ c : F,
      algebraMap W.CoordinateRing L (veluGenX W) - algebraMap F L c ≠ 0 := by
    intro c hc
    refine velu_gen_ne (W := W) c (hinj ?_)
    rw [map_sub, map_zero, hφ]
    exact hc
  have hxx : algebraMap W.CoordinateRing L (veluGenX W) ≠ algebraMap F L x₀ :=
    fun hc => hxne x₀ (by rw [hc, sub_self])
  have hdval : algebraMap W.CoordinateRing L (veluGenD W x₀)
      = algebraMap W.CoordinateRing L (veluGenX W) - algebraMap F L x₀ := by
    rw [veluGenD, map_sub, hφ]
  have hdne : algebraMap W.CoordinateRing L (veluGenD W x₀) ≠ 0 := by
    rw [hdval]; exact hxne x₀
  -- The generic point of `W` over `L`.
  have hEqL : (W⁄L : Affine L).Equation (algebraMap W.CoordinateRing L (veluGenX W))
      (algebraMap W.CoordinateRing L (veluGenY W)) := by
    have h := velu_gen_equation (W := W)
    rw [Affine.equation_iff, velu_ma₁, velu_ma₂, velu_ma₃, velu_ma₄, velu_ma₆] at h
    rw [Affine.equation_iff, velu_ma₁, velu_ma₂, velu_ma₃, velu_ma₄, velu_ma₆]
    have h2 := congrArg (algebraMap W.CoordinateRing L) h
    simpa only [map_add, map_mul, map_pow, hφ] using h2
  have hpsi : veluPsi W ≠ 0 := by
    intro hc
    have h3 : (veluPsi W).coeff 3 = 4 := by
      simp [veluPsi, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [hc, Polynomial.coeff_zero] at h3
    norm_num at h3
  have hns : (W⁄L : Affine L).Nonsingular (algebraMap W.CoordinateRing L (veluGenX W))
      (algebraMap W.CoordinateRing L (veluGenY W)) := by
    refine ⟨hEqL, Or.inr ?_⟩
    rw [Affine.evalEval_polynomialY]
    intro hc
    have h := velu_psi_eval_eq hEqL
    rw [hc, velu_bc_Psi, velu_gen_evalL htower] at h
    refine hpsi (velu_of_injective (W := W) ?_)
    refine (hinj ?_).trans (map_zero (AdjoinRoot.of W.polynomial)).symm
    rw [map_zero, h]
    ring
  -- The kernel over `L`.
  have hSL : IsPointSubgroup (S.image (veluBaseChangePoint W L)) :=
    velu_baseChange_isPointSubgroup hS
  have hcardL : (S.image (veluBaseChangePoint W L)).card = S.card :=
    Finset.card_image_of_injective _ veluBaseChangePoint_injective
  have hoddL : Odd (S.image (veluBaseChangePoint W L)).card := by rw [hcardL]; exact hodd
  have hQ0 : Affine.Point.some x₀ y₀ hQns ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQL : veluBaseChangePoint W L (Affine.Point.some x₀ y₀ hQns)
      ∈ (S.image (veluBaseChangePoint W L)).erase 0 := by
    rw [← velu_bc_erase]
    exact Finset.mem_image_of_mem _ hQ
  have hPS : Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
      (algebraMap W.CoordinateRing L (veluGenY W)) hns
      ∉ S.image (veluBaseChangePoint W L) := by
    intro hcm
    obtain ⟨R, _, hRe⟩ := Finset.mem_image.mp hcm
    have hxr : algebraMap W.CoordinateRing L (veluGenX W) = algebraMap F L (veluPointX R) := by
      have h := veluBaseChangePoint_pointX (L := L) R
      rw [hRe] at h
      exact h
    exact hxne _ (by rw [hxr, sub_self])
  -- The translate of the generic point.
  have hex : ∀ P : (W⁄L : Affine L).Point, P ≠ 0 →
      ∃ (xL : L) (yL : L) (h : (W⁄L : Affine L).Nonsingular xL yL),
        P = Affine.Point.some xL yL h := by
    rintro (_ | ⟨a, b, hab⟩) hP
    · exact absurd rfl hP
    · exact ⟨a, b, hab, rfl⟩
  obtain ⟨xL, yL, hnsL, hQLeq⟩ := hex _ (veluBaseChangePoint_ne_zero hQ0)
  have hxLv : xL = algebraMap F L x₀ := by
    have h := veluBaseChangePoint_pointX (L := L) (Affine.Point.some x₀ y₀ hQns)
    rw [hQLeq] at h
    exact h
  have hyLv : yL = algebraMap F L y₀ := by
    have h := veluBaseChangePoint_pointY (L := L) (Affine.Point.some x₀ y₀ hQns)
    rw [hQLeq] at h
    exact h
  subst hxLv
  subst hyLv
  have hnegY : (W⁄L : Affine L).negY (algebraMap F L x₀) (algebraMap F L y₀)
      = algebraMap F L (W.negY x₀ y₀) := by
    rw [Affine.negY, Affine.negY, velu_ma₁, velu_ma₃]
    simp only [map_sub, map_neg, map_mul]
  have hx'val : veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
        (algebraMap W.CoordinateRing L (veluGenY W)) hns
      + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL))
      * algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2
      = algebraMap W.CoordinateRing L (veluGenN W x₀ y₀) := by
    simp only [Affine.Point.neg_some, hnegY, Affine.Point.add_of_X_ne hxx, veluPointX_some,
      Affine.addX, Affine.slope_of_X_ne hxx, veluGenN, map_sub, map_add, map_mul, map_pow,
      hφ, velu_ma₁, velu_ma₂, hdval]
    field_simp
    ring
  -- The two evaluations of `veluH`.
  have hHgen : (veluH (S.image (veluBaseChangePoint W L))).eval
        (algebraMap W.CoordinateRing L (veluGenX W))
      = algebraMap W.CoordinateRing L (veluGenD W x₀ ^ 2
          * AdjoinRoot.of W.polynomial (veluHq S (Affine.Point.some x₀ y₀ hQns))) := by
    rw [veluH_factor hSL hoddL hQL, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, velu_bc_Hq,
      velu_gen_evalL htower, veluBaseChangePoint_pointX, veluPointX_some, map_mul, map_pow,
      hdval]
  have hHtr : (veluH (S.image (veluBaseChangePoint W L))).eval
        (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
          (algebraMap W.CoordinateRing L (veluGenY W)) hns
        + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
        * (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (S.erase 0).card
      = algebraMap W.CoordinateRing L (∏ Q' ∈ S.erase 0, (veluGenN W x₀ y₀
          - algebraMap F W.CoordinateRing (veluPointX Q') * veluGenD W x₀ ^ 2)) := by
    rw [veluH, Polynomial.eval_prod, ← velu_bc_erase,
      Finset.prod_image (fun a _ b _ h => veluBaseChangePoint_injective h), map_prod,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun Q' _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, veluBaseChangePoint_pointX,
      map_sub, map_mul, map_pow, hφ, sub_mul, hx'val]
  -- The two evaluations of `veluTheta`.
  have hΘgen : (veluTheta (S.image (veluBaseChangePoint W L))).eval
        (algebraMap W.CoordinateRing L (veluGenX W))
      = algebraMap W.CoordinateRing L (AdjoinRoot.of W.polynomial (veluTheta S)) := by
    rw [velu_bc_Theta, velu_gen_evalL htower]
  have hΘtr : (veluTheta (S.image (veluBaseChangePoint W L))).eval
        (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
          (algebraMap W.CoordinateRing L (veluGenY W)) hns
        + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
        * (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (4 * (S.card - 1))
      = algebraMap W.CoordinateRing L (∑ j ∈ Finset.range (4 * (S.card - 1) + 1),
          algebraMap F W.CoordinateRing ((veluTheta S).coeff j) * veluGenN W x₀ y₀ ^ j
            * (veluGenD W x₀ ^ 2) ^ (4 * (S.card - 1) - j)) := by
    rw [velu_bc_Theta,
      velu_eval_scaled ((veluTheta S).map (algebraMap F L))
        (algebraMap W.CoordinateRing L (veluGenN W x₀ y₀))
        (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) _ (4 * (S.card - 1))
        (le_trans (Polynomial.natDegree_map_le) hdeg) hx'val, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.coeff_map, map_mul, map_pow, hφ]
  -- Combine.
  have htrans := velu_theta_translate hSL hoddL
    (hSL.neg_mem _ (Finset.mem_of_mem_erase hQL)) hPS
  rw [hQLeq] at htrans
  simp only [veluPointX_some] at htrans
  have hcard : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem hS.zero_mem
  have hsplit : (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (4 * (S.card - 1))
      = ((algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (S.erase 0).card) ^ 4 := by
    rw [hcard, ← pow_mul, ← pow_mul, ← pow_mul,
      show 2 * (4 * (S.card - 1)) = 2 * ((S.card - 1) * 4) from by ring]
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, ← hΘgen]
  calc (veluTheta (S.image (veluBaseChangePoint W L))).eval
          (algebraMap W.CoordinateRing L (veluGenX W))
        * (algebraMap W.CoordinateRing L (∏ Q' ∈ S.erase 0, (veluGenN W x₀ y₀
            - algebraMap F W.CoordinateRing (veluPointX Q') * veluGenD W x₀ ^ 2))) ^ 4
      = ((veluTheta (S.image (veluBaseChangePoint W L))).eval
            (algebraMap W.CoordinateRing L (veluGenX W))
          * ((veluH (S.image (veluBaseChangePoint W L))).eval
              (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
                (algebraMap W.CoordinateRing L (veluGenY W)) hns
              + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))) ^ 4)
          * (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (4 * (S.card - 1)) := by
        rw [← hHtr, mul_pow, hsplit]; ring
    _ = ((veluTheta (S.image (veluBaseChangePoint W L))).eval
            (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
              (algebraMap W.CoordinateRing L (veluGenY W)) hns
            + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
          * ((veluH (S.image (veluBaseChangePoint W L))).eval
              (algebraMap W.CoordinateRing L (veluGenX W))) ^ 4)
          * (algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2) ^ (4 * (S.card - 1)) := by
        linear_combination (-((algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2)
          ^ (4 * (S.card - 1)))) * htrans
    _ = _ := by rw [← hΘtr, hHgen, map_mul, map_pow]; ring

/-- **PROVEN 2026-07-26: no poles, in local form** — over the degree bound `hdeg`, which the
sibling leaf `velu_theta_degree_lt` supplies.

For each nonzero `Q` of the kernel, `(T − x_Q)⁸` divides `veluTheta S`: the difference of the two
sides of Vélu's identity has NO POLE at `x_Q`.

**Why this consumes the subgroup hypothesis, and where.** Measured in PARI/GP: on `±`-stable
NON-subgroups `{0} ∪ {±G, …, ±kG}` (`k = 1, 2, 3`, `101 ≤ p ≤ 200`) this divisibility fails in 248
of 248 instances, while `velu_theta_degree_lt` holds in all 248. `hS` enters here exactly once,
through `veluCoordX_add_mem` / `veluCoordY_add_mem` inside `velu_theta_translate`.

**The proof.** Translation invariance of the Vélu coordinates identifies the local behaviour at
`x_Q` with the behaviour AT INFINITY, which is the sibling leaf — the route the previous owner
recorded, and it needs none of the four-relations bookkeeping the older docstring described.
Concretely, over the fraction field `L` of the affine coordinate ring `F[W]` take the generic point
`𝐏 = (X, Y)` (`velu_gen_equation`). It lies outside the kernel because `X − x_{Q'} ≠ 0` in `F[W]`
for every `Q'` (`velu_gen_ne`), so `velu_theta_eval` applies both to `𝐏` and to `𝐏 − Q`, and their
Vélu images coincide; hence

  `Θ(x_𝐏)·H(x_{𝐏−Q})⁴ = Θ(x_{𝐏−Q})·H(x_𝐏)⁴`   (`velu_theta_translate`).

Now `x_{𝐏−Q} = N/d²` with `d = X − x_Q` and `N ∈ F[W]` the cleared addition law (`veluGenN`),
while `H(x_𝐏) = d²·G` with `G` a unit at `Q` (`veluH_factor`). Multiplying by `(d²)^{4n}` —
legitimate precisely because `deg Θ ≤ 4n`, i.e. `hdeg` — clears every denominator and gives an
identity IN `F[W]` (`velu_theta_key_over`):

  `Θ(X)·𝓗⁴ = 𝓣·d⁸·G⁴`,  `𝓗 = ∏_{Q'}(N − x_{Q'}d²)`.

Evaluating at `Q` itself (`veluEvalAt`) sends `d ↦ 0` and `N ↦ (2y_Q + a₁x_Q + a₃)² ≠ 0` — nonzero
because a subgroup of odd order has no `2`-torsion. So if `(T − x_Q)^k ‖ Θ` with `k < 8`, cancelling
`d^k` in the domain `F[W]` and evaluating gives `Θ₁(x_Q)·(2y_Q + a₁x_Q + a₃)^{8n} = 0` with both
factors nonzero — a contradiction. (The argument in fact yields `k ≥ 10`; only `k ≥ 8` is used.)

`hdeg` is deliberately WEAKER than `velu_theta_degree_lt`: `≤ 4n` rather than `< 4n`. -/
theorem velu_theta_local_dvd {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (hdeg : (veluTheta S).degree ≤ ((4 * (S.card - 1) : ℕ) : WithBot ℕ))
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 8 ∣ veluTheta S := by
  classical
  rcases eq_or_ne (veluTheta S) 0 with hΘ0 | hΘ0
  · rw [hΘ0]; exact dvd_zero _
  suffices h8 : 8 ≤ Polynomial.rootMultiplicity (veluPointX Q) (veluTheta S) from
    dvd_trans (pow_dvd_pow _ h8) (Polynomial.pow_rootMultiplicity_dvd _ _)
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  obtain _ | ⟨x₀, y₀, hQns⟩ := Q
  · exact absurd rfl hQ0
  simp only [veluPointX_some] at hlt
  -- `Q` is not `2`-torsion, so the `u`-term at `Q` is nonzero.
  have hne2 : W.negY x₀ y₀ ≠ y₀ := by
    intro hc
    refine velu_twoTorsion_notMem hS hodd hQ0 ?_ hQS
    rw [Affine.Point.neg_some]
    exact velu_point_some_eq rfl hc
  have hv₀ : y₀ - W.negY x₀ y₀ ≠ 0 := sub_ne_zero.mpr fun hc => hne2 hc.symm
  -- The root multiplicity data.
  set k := Polynomial.rootMultiplicity x₀ (veluTheta S) with hkdef
  set Θ₁ := (veluTheta S) /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k) with hΘ₁def
  have hΘsplit : (Polynomial.X - Polynomial.C x₀) ^ k * Θ₁ = veluTheta S :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq _ _
  have hΘ₁ne : Θ₁.eval x₀ ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ hΘ0
  -- The affine coordinate ring and its fraction field.
  haveI : IsDomain W.CoordinateRing := inferInstance
  letI : Algebra F (FractionRing W.CoordinateRing) :=
    ((algebraMap W.CoordinateRing (FractionRing W.CoordinateRing)).comp
      (algebraMap F W.CoordinateRing)).toAlgebra
  have htower : (algebraMap F (FractionRing W.CoordinateRing))
      = (algebraMap W.CoordinateRing (FractionRing W.CoordinateRing)).comp
          (algebraMap F W.CoordinateRing) := rfl
  haveI : CharZero (FractionRing W.CoordinateRing) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap F (FractionRing W.CoordinateRing)))
  have hALinj : Function.Injective
      (algebraMap W.CoordinateRing (FractionRing W.CoordinateRing)) :=
    IsFractionRing.injective _ _
  -- Abbreviations in the coordinate ring.
  set d : W.CoordinateRing := veluGenD W x₀ with hddef
  set N : W.CoordinateRing := veluGenN W x₀ y₀ with hNdef
  set n : ℕ := S.card - 1 with hndef
  set 𝓗 : W.CoordinateRing :=
    ∏ Q' ∈ S.erase 0, (N - algebraMap F W.CoordinateRing (veluPointX Q') * d ^ 2) with h𝓗def
  set 𝓣 : W.CoordinateRing := ∑ j ∈ Finset.range (4 * n + 1),
    algebraMap F W.CoordinateRing ((veluTheta S).coeff j) * N ^ j * (d ^ 2) ^ (4 * n - j)
      with h𝓣def
  set G : W.CoordinateRing :=
    AdjoinRoot.of W.polynomial (veluHq S (Affine.Point.some x₀ y₀ hQns)) with hGdef
  -- The key identity in the coordinate ring.
  have key : AdjoinRoot.of W.polynomial (veluTheta S) * 𝓗 ^ 4 = 𝓣 * d ^ 8 * G ^ 4 :=
    velu_theta_key_over (FractionRing W.CoordinateRing) htower hALinj hS hodd
      (Polynomial.natDegree_le_iff_degree_le.mpr hdeg) hQns hQ
  -- Conclude by evaluating at `Q`.
  have hd : d ≠ 0 := velu_gen_ne x₀
  have hdvd : (d : W.CoordinateRing) ^ k *
      (AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4) = d ^ k * (𝓣 * d ^ (8 - k) * G ^ 4) := by
    have hofd : AdjoinRoot.of W.polynomial (Polynomial.X - Polynomial.C x₀) = d := by
      rw [hddef, veluGenD, map_sub, velu_of_C]
      rfl
    have hdk : AdjoinRoot.of W.polynomial (veluTheta S)
        = d ^ k * AdjoinRoot.of W.polynomial Θ₁ := by
      rw [← hΘsplit, map_mul, map_pow, hofd]
    calc d ^ k * (AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4)
        = AdjoinRoot.of W.polynomial (veluTheta S) * 𝓗 ^ 4 := by rw [hdk]; ring
      _ = 𝓣 * d ^ 8 * G ^ 4 := key
      _ = d ^ k * (𝓣 * d ^ (8 - k) * G ^ 4) := by
          have h8 : (d : W.CoordinateRing) ^ (8 : ℕ) = d ^ k * d ^ (8 - k) := by
            rw [← pow_add, Nat.add_sub_cancel' hlt.le]
          rw [h8]; ring
  have hcancel : AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4 = 𝓣 * d ^ (8 - k) * G ^ 4 :=
    mul_left_cancel₀ (pow_ne_zero k hd) hdvd
  -- Evaluate.
  have hEqQ : W.Equation x₀ y₀ := hQns.1
  have hev := congrArg (veluEvalAt hEqQ) hcancel
  simp only [map_mul, map_pow, veluEvalAt_of] at hev
  have hevd : veluEvalAt hEqQ d = 0 := by
    rw [hddef, veluGenD, map_sub, veluEvalAt_genX, veluEvalAt_algebraMap, sub_self]
  have hevN : veluEvalAt hEqQ N = (y₀ - W.negY x₀ y₀) ^ 2 := by
    rw [hNdef, veluGenN, ← hddef]
    simp only [map_sub, map_add, map_mul, map_pow, veluEvalAt_genX, veluEvalAt_genY,
      veluEvalAt_algebraMap, hevd]
    ring
  have hev𝓗 : veluEvalAt hEqQ 𝓗 = ((y₀ - W.negY x₀ y₀) ^ 2) ^ (S.erase 0).card := by
    calc veluEvalAt hEqQ 𝓗
        = ∏ Q' ∈ S.erase 0, veluEvalAt hEqQ
            (N - algebraMap F W.CoordinateRing (veluPointX Q') * d ^ 2) := by
          rw [h𝓗def, map_prod]
      _ = ∏ _Q' ∈ S.erase 0, (y₀ - W.negY x₀ y₀) ^ 2 := by
          refine Finset.prod_congr rfl fun Q' _ => ?_
          rw [map_sub, map_mul, map_pow, hevd, hevN, veluEvalAt_algebraMap]
          ring
      _ = ((y₀ - W.negY x₀ y₀) ^ 2) ^ (S.erase 0).card := by rw [Finset.prod_const]
  rw [hev𝓗, hevd, zero_pow (Nat.sub_ne_zero_of_lt hlt), mul_zero, zero_mul] at hev
  exact (mul_ne_zero hΘ₁ne (pow_ne_zero 4 (pow_ne_zero _ (pow_ne_zero 2 hv₀)))) hev

omit [CharZero F] in
/-- **PROVEN.** The local divisibilities assemble: distinct linear factors are coprime, and
`veluH⁴` is their product by `veluH_pow_eq`. -/
theorem velu_theta_dvd {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (hloc : ∀ Q ∈ S.erase 0,
      (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 8 ∣ veluTheta S) :
    (veluH S) ^ 4 ∣ veluTheta S := by
  rw [veluH_pow_eq hS hodd]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun a ha => ?_)
  · exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
    exact hloc Q hQ

section PolePolyDegree

open _root_.Polynomial

/-! ### Two-jet calculus -/

omit [DecidableEq F] in
lemma velu_coeff_one_eq_eval (f : Polynomial F) : f.coeff 1 = (derivative f).eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

omit [DecidableEq F] in
lemma velu_coeff_one_mul (f g : Polynomial F) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  simp only [velu_coeff_one_eq_eval, coeff_zero_eq_eval_zero, derivative_mul, eval_add, eval_mul]
  ring

omit [DecidableEq F] [CharZero F] in
lemma velu_prod_coeff_zero {ι : Type*} (s : Finset ι) (c : ι → F) :
    (∏ i ∈ s, (1 - C (c i) * X)).coeff 0 = 1 := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s' ha ih
  rw [Finset.prod_insert ha, mul_coeff_zero, ih]
  simp [coeff_one]

omit [DecidableEq F] in
lemma velu_prod_coeff_one {ι : Type*} (s : Finset ι) (c : ι → F) :
    (∏ i ∈ s, (1 - C (c i) * X)).coeff 1 = -∑ i ∈ s, c i := by
  classical
  refine Finset.induction_on s (by simp [coeff_one]) ?_
  intro a s' ha ih
  rw [Finset.prod_insert ha, velu_coeff_one_mul, ih, velu_prod_coeff_zero, Finset.sum_insert ha]
  have h0 : ((1 : Polynomial F) - C (c a) * X).coeff 0 = 1 := by simp [coeff_one]
  have h1 : ((1 : Polynomial F) - C (c a) * X).coeff 1 = -c a := by simp [coeff_one]
  rw [h0, h1]; ring

/-! ### `reflect` helpers -/

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_shift {f : Polynomial F} {M : ℕ} (hf : f.natDegree ≤ M) (k : ℕ) :
    reflect (M + k) f = reflect M f * X ^ k := by
  have h := reflect_mul f (1 : Polynomial F) hf
    (show (1 : Polynomial F).natDegree ≤ k by simp)
  rwa [mul_one, reflect_one] at h

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial F) (N : ℕ) :
    reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, reflect N (f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s' ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, reflect_add, ih]

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_one_X_sub_C (c : F) : reflect 1 (X - C c) = 1 - C c * X := by
  rw [reflect_sub, reflect_one_X, reflect_C]
  ring

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_prod_X_sub_C {ι : Type*} (s : Finset ι) (c : ι → F) :
    reflect s.card (∏ i ∈ s, (X - C (c i))) = ∏ i ∈ s, (1 - C (c i) * X) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s' ha ih
  have hd : (∏ i ∈ s', (X - C (c i))).natDegree ≤ s'.card := by
    refine le_trans (natDegree_prod_le _ _) ?_
    simp
  rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, Finset.prod_insert ha,
    show s'.card + 1 = 1 + s'.card from Nat.add_comm _ _,
    reflect_mul _ _ (le_of_eq (natDegree_X_sub_C _)) hd, ih, velu_reflect_one_X_sub_C]

omit [DecidableEq F] [CharZero F] in
lemma velu_degree_lt_of_reflect {f : Polynomial F} {N k : ℕ}
    (hf : f.natDegree ≤ N) (hdvd : (X : Polynomial F) ^ k ∣ reflect N f) :
    f.degree < ((N + 1 - k : ℕ) : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rcases le_or_gt m N with hmN | hmN
  · have h1 : (reflect N f).coeff (N - m) = 0 := X_pow_dvd_iff.mp hdvd (N - m) (by omega)
    rwa [coeff_reflect, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hmN] at h1
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hmN)

/-! ### The key algebraic step, at the level of reflected polynomials -/

omit [DecidableEq F] in
lemma velu_reflect_theta_dvd (h px pv : Polynomial F) (t w b2 b4 b6 a : F)
    (h0 : h.coeff 0 = 1) (h1 : h.coeff 1 = a)
    (px0 : px.coeff 0 = t) (px1 : px.coeff 1 = t * a + w)
    (pv0 : pv.coeff 0 = t) (pv1 : pv.coeff 1 = 2 * (t * a) + 2 * w) :
    (X : Polynomial F) ^ 4 ∣
      (4 + C b2 * X + 2 * C b4 * X ^ 2 + C b6 * X ^ 3) * (h ^ 2 - pv * X ^ 2) ^ 2
        - h * (4 * (h + px * X ^ 2) ^ 3
              + C b2 * ((h + px * X ^ 2) ^ 2 * h * X)
              + (2 * C b4 - 20 * C t) * ((h + px * X ^ 2) * h ^ 2 * X ^ 2)
              + (C b6 - 4 * C b2 * C t - 28 * C w) * (h ^ 3 * X ^ 3)) := by
  have h0' : h.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero]; exact h0
  have h1' : (derivative h).eval 0 = a := by rw [← velu_coeff_one_eq_eval]; exact h1
  have px0' : px.eval 0 = t := by rw [← coeff_zero_eq_eval_zero]; exact px0
  have px1' : (derivative px).eval 0 = t * a + w := by rw [← velu_coeff_one_eq_eval]; exact px1
  have pv0' : pv.eval 0 = t := by rw [← coeff_zero_eq_eval_zero]; exact pv0
  have pv1' : (derivative pv).eval 0 = 2 * (t * a) + 2 * w := by
    rw [← velu_coeff_one_eq_eval]; exact pv1
  have hAB : (X : Polynomial F) ^ 2 ∣
      (-8 * h ^ 2 * pv - 12 * h ^ 3 * px + 20 * C t * h ^ 4)
        + X * (-2 * C b2 * h ^ 2 * pv - 2 * C b2 * h ^ 3 * px
                + (4 * C b2 * C t + 28 * C w) * h ^ 4) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp only [coeff_zero_eq_eval_zero, eval_add, eval_sub, eval_mul, eval_pow, eval_neg,
        eval_ofNat, eval_C, eval_X, h0', px0', pv0']
      ring
    · rw [velu_coeff_one_eq_eval]
      simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_X,
        derivative_C, derivative_ofNat, derivative_neg, eval_add, eval_sub,
        eval_mul, eval_pow, eval_neg, eval_ofNat, eval_C, eval_X, eval_zero, eval_one,
        h0', h1', px0', px1', pv0', pv1']
      push_cast
      ring
  obtain ⟨D, hD⟩ := hAB
  refine ⟨D + (4 * pv ^ 2 - 12 * h ^ 2 * px ^ 2 - 4 * X ^ 2 * h * px ^ 3 + C b2 * X * pv ^ 2
      - C b2 * X * h ^ 2 * px ^ 2 - 4 * C b4 * h ^ 2 * pv - 2 * C b4 * h ^ 3 * px
      + 2 * C b4 * X ^ 2 * pv ^ 2 + 20 * C t * h ^ 3 * px - 2 * C b6 * X * h ^ 2 * pv
      + C b6 * X ^ 3 * pv ^ 2), ?_⟩
  have key : (4 + C b2 * X + 2 * C b4 * X ^ 2 + C b6 * X ^ 3) * (h ^ 2 - pv * X ^ 2) ^ 2
        - h * (4 * (h + px * X ^ 2) ^ 3
              + C b2 * ((h + px * X ^ 2) ^ 2 * h * X)
              + (2 * C b4 - 20 * C t) * ((h + px * X ^ 2) * h ^ 2 * X ^ 2)
              + (C b6 - 4 * C b2 * C t - 28 * C w) * (h ^ 3 * X ^ 3))
      = X ^ 2 * ((-8 * h ^ 2 * pv - 12 * h ^ 3 * px + 20 * C t * h ^ 4)
          + X * (-2 * C b2 * h ^ 2 * pv - 2 * C b2 * h ^ 3 * px
                  + (4 * C b2 * C t + 28 * C w) * h ^ 4))
        + X ^ 4 * (4 * pv ^ 2 - 12 * h ^ 2 * px ^ 2 - 4 * X ^ 2 * h * px ^ 3 + C b2 * X * pv ^ 2
          - C b2 * X * h ^ 2 * px ^ 2 - 4 * C b4 * h ^ 2 * pv - 2 * C b4 * h ^ 3 * px
          + 2 * C b4 * X ^ 2 * pv ^ 2 + 20 * C t * h ^ 3 * px - 2 * C b6 * X * h ^ 2 * pv
          + C b6 * X ^ 3 * pv ^ 2) := by
    ring
  rw [key, hD]
  ring

/-! ### Small reflect computations -/

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_two_X_sub_C (c : F) :
    reflect 2 (X - C c) = (1 - C c * X) * X := by
  have h := velu_reflect_shift (f := (X - C c : Polynomial F)) (M := 1)
    (le_of_eq (natDegree_X_sub_C c)) 1
  rw [velu_reflect_one_X_sub_C, pow_one] at h
  exact h

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_two_X_sub_C_sq (c : F) :
    reflect 2 ((X - C c) ^ 2) = (1 - C c * X) ^ 2 := by
  rw [pow_two, pow_two]
  exact (reflect_mul _ _ (le_of_eq (natDegree_X_sub_C c))
    (le_of_eq (natDegree_X_sub_C c))).trans (by rw [velu_reflect_one_X_sub_C])

omit [DecidableEq F] [CharZero F] in
lemma velu_reflect_pow {f : Polynomial F} {M : ℕ} (hf : f.natDegree ≤ M) (k : ℕ) :
    reflect (k * M) (f ^ k) = (reflect M f) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (f ^ k).natDegree ≤ k * M := le_trans natDegree_pow_le (Nat.mul_le_mul le_rfl hf)
    rw [pow_succ, pow_succ, show (k + 1) * M = k * M + M from by ring,
      reflect_mul _ _ hk hf, ih]

omit [DecidableEq F] [CharZero F] in
lemma velu_one_sub_sq_coeff_zero (c : F) :
    ((1 - C c * X : Polynomial F) ^ 2).coeff 0 = 1 := by
  rw [pow_two, mul_coeff_zero]
  simp [coeff_one]

omit [DecidableEq F] in
lemma velu_one_sub_sq_coeff_one (c : F) :
    ((1 - C c * X : Polynomial F) ^ 2).coeff 1 = -2 * c := by
  rw [pow_two, velu_coeff_one_mul]
  simp [coeff_one]
  ring

/-! ### The Vélu `w`-term splits -/

omit [DecidableEq F] [CharZero F] in
lemma velu_wTerm_eq (Q : W.Point) :
    veluWTerm W Q = veluUTerm W Q + veluPointX Q * veluTTerm W Q := by
  cases Q with
  | zero =>
    show veluWTerm W (0 : W.Point)
      = veluUTerm W (0 : W.Point) + veluPointX (0 : W.Point) * veluTTerm W (0 : W.Point)
    simp
  | some x y hxy => simp

/-- **PROVEN 2026-07-26: vanishing at infinity**, the second of the two polynomial leaves
cut out of `velu_pole_identity` (the first, `velu_theta_local_dvd`, was PROVEN the same day
by a different owner, over this bound supplied as its `hdeg` hypothesis).

`deg (veluTheta S) < 4n`, `n = |S| − 1`. Both `veluPsi W * (veluXi S)²` and
`veluH S * veluPhiNum S` have degree `4n + 3` with leading coefficient `4` (`veluH` is monic,
`veluXi` is monic of degree `2n` because `deg (veluPV S) ≤ 2n − 2`), so the difference has
degree `≤ 4n + 2` for free; what has to be shown is that the coefficients in degrees
`4n + 2`, `4n + 1` and `4n` also vanish. THAT is where Vélu's `t = veluT S` and `w = veluW S`
are consumed: they are exactly the constants for which those three coefficients cancel.

**The proof, and why it is a reflection argument.** Reading the four top coefficients of a
product of polynomials of symbolic degree is painful; reading the four BOTTOM coefficients is
not. So the whole computation is transported through `Polynomial.reflect`, which is
multiplicative (`reflect_mul`) and turns "degree `< 4n`" into "`X⁴` divides", by
`velu_degree_lt_of_reflect`. Writing `ĥ = reflect n H`, `p̂x = reflect (n−1) (½·PX)`,
`p̂v = reflect (2n−2) PV`, the reflected shapes are

  `reflect (2n) Ξ = ĥ² − p̂v·X²`,  `reflect (n+1) XNum = ĥ + p̂x·X²`,
  `reflect 3 Ψ = 4 + b₂X + 2b₄X² + b₆X³`,

and `reflect (4n+3) Θ` is the expression appearing in `velu_reflect_theta_dvd`. That lemma is
the entire arithmetic: an exact `ring` identity `Θ̂ = X²·A + X³·B + X⁴·C` reduces the claim to
`X² ∣ A + X·B`, i.e. to two scalar identities in the two-jets

  `ĥ = 1 + aX + …`,  `p̂x = t + (ta + w)X + …`,  `p̂v = t + 2(ta + w)X + …`,

namely `−8t − 12t + 20t = 0` in degree `0` and `−28w + 28w = 0` in degree `1`. The jets
themselves come from the fibrewise pairing: `veluHq` contributes `1` and `−(e₁ − 2x_Q)`, and
summing over `S ∖ {0}` turns `Σ t_Q` into `2t` and `Σ (u_Q + x_Q t_Q) = Σ w_Q` into `2w`,
with `a = −e₁ = ĥ.coeff 1`. Note `p̂x` and `p̂v` have the SAME first-order coefficient, which
is what makes the degree-`1` identity collapse.

**This half does NOT need `hS`, only `±`-stability** — verified in PARI/GP on `±`-stable
non-subgroups `{0} ∪ {±G, …, ±kG}` (`k = 1, 2, 3`, `101 ≤ p ≤ 200`): 248 of 248 instances
satisfy the degree bound even though `veluTheta S ≠ 0` there. `hS` and `hodd` are used here
only through `velu_twoTorsion_notMem` (so that `Q` and `−Q` are two distinct points of
`S ∖ {0}`, giving `veluHq` its degree `n − 2`) and through `veluH_natDegree`. -/
theorem velu_theta_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluTheta S).degree < ((4 * (S.card - 1) : ℕ) : WithBot ℕ) := by
  classical
  have h2ne : (2 : F) ≠ 0 := by norm_num
  have hcard : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem hS.zero_mem
  have hScard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hsumT : ∑ Q ∈ S.erase 0, veluTTerm W Q = ∑ Q ∈ S, veluTTerm W Q := by
    rw [← Finset.sum_erase_add S (veluTTerm W) hS.zero_mem, veluTTerm_zero, add_zero]
  have hsumW : ∑ Q ∈ S.erase 0, veluWTerm W Q = ∑ Q ∈ S, veluWTerm W Q := by
    rw [← Finset.sum_erase_add S (veluWTerm W) hS.zero_mem, veluWTerm_zero, add_zero]
  rcases Nat.eq_zero_or_pos (S.erase 0).card with h0 | hpos
  · -- degenerate kernel `S = {0}`
    have hE : S.erase 0 = ∅ := Finset.card_eq_zero.mp h0
    have hH : veluH S = 1 := by rw [veluH, hE, Finset.prod_empty]
    have hPX : veluPX S = 0 := by rw [veluPX, hE, Finset.sum_empty]
    have hPV : veluPV S = 0 := by rw [veluPV, hE, Finset.sum_empty]
    have hT : W.veluT S = 0 := by
      rw [veluT, ← hsumT, hE, Finset.sum_empty, mul_zero]
    have hW : W.veluW S = 0 := by
      rw [veluW, ← hsumW, hE, Finset.sum_empty, mul_zero]
    have hTheta : veluTheta S = 0 := by
      rw [veluTheta, veluXi, veluPhiNum, veluXNum, hH, hPX, hPV, hT, hW, veluPsi]
      ring_nf
    have hz : 4 * (S.card - 1) = 0 := by omega
    rw [hTheta, degree_zero, hz]
    exact WithBot.bot_lt_coe _
  · -- the substantial case
    obtain ⟨m, hm⟩ : ∃ m, (S.erase 0).card = m + 2 := by
      have hne1 : (S.erase 0).card ≠ 1 := by
        intro hh
        have h2 : S.card = 2 := by omega
        rw [h2] at hodd
        simp [Nat.odd_iff] at hodd
      exact ⟨(S.erase 0).card - 2, by omega⟩
    have hHdeg : (veluH S).natDegree = m + 2 := by
      rw [veluH_natDegree hS]; omega
    have hTcard : ∀ Q ∈ S.erase 0, (((S.erase 0).erase Q).erase (-Q)).card = m := by
      intro Q hQ
      have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
      have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
      have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
      have hne : -Q ≠ Q := fun h => velu_twoTorsion_notMem hS hodd hQ0 h hQS
      have h1 : -Q ∈ (S.erase 0).erase Q :=
        Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
      have e1 := Finset.card_erase_of_mem h1
      have e2 := Finset.card_erase_of_mem hQ
      omega
    have hTsum : ∀ Q ∈ S.erase 0,
        ∑ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), veluPointX Q'
          = (∑ Q' ∈ S.erase 0, veluPointX Q') - 2 * veluPointX Q := by
      intro Q hQ
      have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
      have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
      have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
      have hne : -Q ≠ Q := fun h => velu_twoTorsion_notMem hS hodd hQ0 h hQS
      have h1 : -Q ∈ (S.erase 0).erase Q :=
        Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
      have e1 := Finset.sum_erase_add (S.erase 0) veluPointX hQ
      have e2 := Finset.sum_erase_add ((S.erase 0).erase Q) veluPointX h1
      rw [velu_pointX_neg] at e2
      linear_combination e1 + e2
    have hHqdeg : ∀ Q ∈ S.erase 0, (veluHq S Q).natDegree ≤ m := by
      intro Q hQ
      rw [veluHq]
      refine le_trans (natDegree_prod_le _ _) ?_
      simp [hTcard Q hQ]
    have hreflHq : ∀ Q ∈ S.erase 0, reflect m (veluHq S Q)
        = ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), (1 - C (veluPointX Q') * X) := by
      intro Q hQ
      rw [veluHq, ← hTcard Q hQ, velu_reflect_prod_X_sub_C]
    have hreflH : reflect (m + 2) (veluH S)
        = ∏ Q ∈ S.erase 0, (1 - C (veluPointX Q) * X) := by
      rw [veluH, ← hm, velu_reflect_prod_X_sub_C]
    -- degree bounds
    have hPXdeg : (veluPX S).natDegree ≤ m + 1 := by
      rw [veluPX]
      refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
      refine le_trans natDegree_mul_le ?_
      have hlin : (C (veluTTerm W Q) * (X - C (veluPointX Q))
          + C (veluUTerm W Q)).natDegree ≤ 1 := by
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_sub_C _))
        · simp
      have := add_le_add hlin (hHqdeg Q hQ)
      omega
    have hPVdeg : (veluPV S).natDegree ≤ 2 * m + 2 := by
      rw [veluPV]
      refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
      refine le_trans natDegree_mul_le ?_
      have hq := hHqdeg Q hQ
      have hsq : ((veluHq S Q) ^ 2).natDegree ≤ 2 * m :=
        le_trans natDegree_pow_le (by omega)
      have hquad : (C (veluUTerm W Q) * (X - C (veluPointX Q))
          + C ((2 : F)⁻¹ * veluTTerm W Q) * (X - C (veluPointX Q)) ^ 2).natDegree ≤ 2 := by
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (natDegree_C_mul_le _ _)
            (le_trans (le_of_eq (natDegree_X_sub_C _)) one_le_two)
        · refine le_trans (natDegree_C_mul_le _ _) ?_
          refine le_trans natDegree_pow_le ?_
          simp
      have := add_le_add hquad hsq
      omega
    have hCPXdeg : (C ((2 : F)⁻¹) * veluPX S).natDegree ≤ m + 1 :=
      le_trans (natDegree_C_mul_le _ _) hPXdeg
    have hXideg : (veluXi S).natDegree ≤ 2 * m + 4 := by
      rw [veluXi]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans natDegree_pow_le (by omega)
      · omega
    have hXNdeg : (veluXNum S).natDegree ≤ m + 3 := by
      rw [veluXNum]
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans natDegree_mul_le ?_
        rw [natDegree_X]; omega
      · exact le_trans (natDegree_C_mul_le _ _) (by omega)
    have hxn2 : ((veluXNum S) ^ 2).natDegree ≤ 2 * (m + 3) :=
      le_trans natDegree_pow_le (by omega)
    have hxn3 : ((veluXNum S) ^ 3).natDegree ≤ 3 * m + 9 :=
      le_trans natDegree_pow_le (by omega)
    have hh2 : ((veluH S) ^ 2).natDegree ≤ 2 * (m + 2) :=
      le_trans natDegree_pow_le (by omega)
    have hh3 : ((veluH S) ^ 3).natDegree ≤ 3 * m + 6 :=
      le_trans natDegree_pow_le (by omega)
    have hPhideg : (veluPhiNum S).natDegree ≤ 3 * m + 9 := by
      have t1 : (C (4 : F) * (veluXNum S) ^ 3).natDegree ≤ 3 * m + 9 :=
        le_trans (natDegree_C_mul_le _ _) hxn3
      have t2 : (C W.b₂ * (veluXNum S) ^ 2 * veluH S).natDegree ≤ 3 * m + 9 := by
        refine le_trans natDegree_mul_le ?_
        have := le_trans (natDegree_C_mul_le W.b₂ ((veluXNum S) ^ 2)) hxn2
        omega
      have t3 : (C (2 * W.b₄ - 20 * W.veluT S) * veluXNum S * (veluH S) ^ 2).natDegree
          ≤ 3 * m + 9 := by
        refine le_trans natDegree_mul_le ?_
        have := le_trans (natDegree_C_mul_le (2 * W.b₄ - 20 * W.veluT S) (veluXNum S)) hXNdeg
        omega
      have t4 : (C (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S)
          * (veluH S) ^ 3).natDegree ≤ 3 * m + 9 :=
        le_trans (natDegree_C_mul_le _ _) (by omega)
      rw [veluPhiNum]
      exact le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
        (max_le (le_trans (natDegree_add_le _ _) (max_le t1 t2)) t3)) t4)
    have hPsideg : (veluPsi W).natDegree ≤ 3 := by
      rw [veluPsi]
      refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
        (max_le (le_trans (natDegree_add_le _ _) (max_le ?_ ?_)) ?_)) ?_)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
      · exact le_trans (natDegree_C_mul_le _ _) (by simp)
      · simp
    have hThetadeg : (veluTheta S).natDegree ≤ 4 * m + 11 := by
      rw [veluTheta]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans natDegree_mul_le ?_
        have hxi2 : ((veluXi S) ^ 2).natDegree ≤ 4 * m + 8 :=
          le_trans natDegree_pow_le (by omega)
        omega
      · refine le_trans natDegree_mul_le ?_
        omega
    -- reflected forms
    have hPXrefl : reflect (m + 1) (veluPX S)
        = ∑ Q ∈ S.erase 0,
            ((C (veluTTerm W Q)
              + (C (veluUTerm W Q) - C (veluTTerm W Q) * C (veluPointX Q)) * X)
              * ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), (1 - C (veluPointX Q') * X)) := by
      rw [veluPX, velu_reflect_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hlin : (C (veluTTerm W Q) * (X - C (veluPointX Q))
          + C (veluUTerm W Q)).natDegree ≤ 1 := by
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_sub_C _))
        · simp
      rw [show m + 1 = 1 + m from Nat.add_comm _ _,
        reflect_mul _ _ hlin (hHqdeg Q hQ), hreflHq Q hQ, reflect_add, reflect_C_mul,
        velu_reflect_one_X_sub_C, reflect_C]
      ring
    have hPVrefl : reflect (2 * m + 2) (veluPV S)
        = ∑ Q ∈ S.erase 0,
            ((C (veluUTerm W Q) * ((1 - C (veluPointX Q) * X) * X)
              + C ((2 : F)⁻¹ * veluTTerm W Q) * (1 - C (veluPointX Q) * X) ^ 2)
              * (∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
                  (1 - C (veluPointX Q') * X)) ^ 2) := by
      rw [veluPV, velu_reflect_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hq := hHqdeg Q hQ
      have hsq : ((veluHq S Q) ^ 2).natDegree ≤ m + m :=
        le_trans natDegree_pow_le (by omega)
      have hquad : (C (veluUTerm W Q) * (X - C (veluPointX Q))
          + C ((2 : F)⁻¹ * veluTTerm W Q) * (X - C (veluPointX Q)) ^ 2).natDegree ≤ 2 := by
        refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
        · exact le_trans (natDegree_C_mul_le _ _)
            (le_trans (le_of_eq (natDegree_X_sub_C _)) one_le_two)
        · refine le_trans (natDegree_C_mul_le _ _) ?_
          refine le_trans natDegree_pow_le ?_
          simp
      have hHq2 : reflect (m + m) ((veluHq S Q) ^ 2) = (reflect m (veluHq S Q)) ^ 2 := by
        rw [pow_two, pow_two, reflect_mul _ _ hq hq]
      rw [show 2 * m + 2 = 2 + (m + m) from by ring, reflect_mul _ _ hquad hsq, hHq2,
        hreflHq Q hQ, reflect_add, reflect_C_mul, reflect_C_mul,
        velu_reflect_two_X_sub_C, velu_reflect_two_X_sub_C_sq]
    -- jets
    have hjh0 : (reflect (m + 2) (veluH S)).coeff 0 = 1 := by
      rw [hreflH, velu_prod_coeff_zero]
    have hjh1 : (reflect (m + 2) (veluH S)).coeff 1 = -∑ Q ∈ S.erase 0, veluPointX Q := by
      rw [hreflH, velu_prod_coeff_one]
    have hjpx0 : (reflect (m + 1) (veluPX S)).coeff 0 = ∑ Q ∈ S.erase 0, veluTTerm W Q := by
      rw [hPXrefl, finsetSum_coeff]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [mul_coeff_zero, velu_prod_coeff_zero]
      simp
    have hjpx1 : (reflect (m + 1) (veluPX S)).coeff 1
        = ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
            - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q') := by
      rw [hPXrefl, finsetSum_coeff]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [velu_coeff_one_mul, velu_prod_coeff_zero, velu_prod_coeff_one, hTsum Q hQ]
      have e0 : (C (veluTTerm W Q)
          + (C (veluUTerm W Q) - C (veluTTerm W Q) * C (veluPointX Q)) * X).coeff 0
            = veluTTerm W Q := by simp
      have e1 : (C (veluTTerm W Q)
          + (C (veluUTerm W Q) - C (veluTTerm W Q) * C (veluPointX Q)) * X).coeff 1
            = veluUTerm W Q - veluTTerm W Q * veluPointX Q := by simp
      rw [e0, e1]; ring
    have hjpv0 : (reflect (2 * m + 2) (veluPV S)).coeff 0
        = ∑ Q ∈ S.erase 0, (2 : F)⁻¹ * veluTTerm W Q := by
      rw [hPVrefl, finsetSum_coeff]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have p0 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
          (1 - C (veluPointX Q') * X)) ^ 2).coeff 0 = 1 := by
        rw [pow_two, mul_coeff_zero, velu_prod_coeff_zero]; ring
      have a0 : (C (veluUTerm W Q) * ((1 - C (veluPointX Q) * X) * X)
          + C ((2 : F)⁻¹ * veluTTerm W Q) * (1 - C (veluPointX Q) * X) ^ 2).coeff 0
            = (2 : F)⁻¹ * veluTTerm W Q := by
        simp [velu_one_sub_sq_coeff_zero]
      rw [mul_coeff_zero, p0, a0, mul_one]
    have hjpv1 : (reflect (2 * m + 2) (veluPV S)).coeff 1
        = ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
            - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q') := by
      rw [hPVrefl, finsetSum_coeff]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have p0 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
          (1 - C (veluPointX Q') * X)) ^ 2).coeff 0 = 1 := by
        rw [pow_two, mul_coeff_zero, velu_prod_coeff_zero]; ring
      have p1 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
          (1 - C (veluPointX Q') * X)) ^ 2).coeff 1
            = 2 * -(∑ Q' ∈ S.erase 0, veluPointX Q' - 2 * veluPointX Q) := by
        rw [pow_two, velu_coeff_one_mul, velu_prod_coeff_zero, velu_prod_coeff_one, hTsum Q hQ]
        ring
      have a0 : (C (veluUTerm W Q) * ((1 - C (veluPointX Q) * X) * X)
          + C ((2 : F)⁻¹ * veluTTerm W Q) * (1 - C (veluPointX Q) * X) ^ 2).coeff 0
            = (2 : F)⁻¹ * veluTTerm W Q := by
        simp [velu_one_sub_sq_coeff_zero]
      have a1 : (C (veluUTerm W Q) * ((1 - C (veluPointX Q) * X) * X)
          + C ((2 : F)⁻¹ * veluTTerm W Q) * (1 - C (veluPointX Q) * X) ^ 2).coeff 1
            = veluUTerm W Q + (2 : F)⁻¹ * veluTTerm W Q * (-2 * veluPointX Q) := by
        rw [coeff_add, coeff_C_mul, coeff_C_mul, velu_one_sub_sq_coeff_one,
          velu_coeff_one_mul]
        simp [coeff_one]
      rw [velu_coeff_one_mul, p0, p1, a0, a1]
      field_simp
      ring
    -- assembled reflected identity
    have hXirefl : reflect (2 * m + 4) (veluXi S)
        = (reflect (m + 2) (veluH S)) ^ 2 - (reflect (2 * m + 2) (veluPV S)) * X ^ 2 := by
      have e1 : reflect (2 * m + 4) ((veluH S) ^ 2) = (reflect (m + 2) (veluH S)) ^ 2 := by
        rw [pow_two, pow_two, show 2 * m + 4 = (m + 2) + (m + 2) from by ring,
          reflect_mul _ _ (le_of_eq hHdeg) (le_of_eq hHdeg)]

      have e2 : reflect (2 * m + 4) (veluPV S) = (reflect (2 * m + 2) (veluPV S)) * X ^ 2 := by
        rw [show 2 * m + 4 = (2 * m + 2) + 2 from by ring, velu_reflect_shift hPVdeg]
      rw [veluXi, reflect_sub, e1, e2]
    have hXNrefl : reflect (m + 3) (veluXNum S)
        = reflect (m + 2) (veluH S)
          + (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) * X ^ 2 := by
      have e1 : reflect (m + 3) (X * veluH S) = reflect (m + 2) (veluH S) := by
        rw [show m + 3 = 1 + (m + 2) from by ring,
          reflect_mul _ _ (le_of_eq natDegree_X) (le_of_eq hHdeg), reflect_one_X, one_mul]
      have e2 : reflect (m + 3) (C ((2 : F)⁻¹) * veluPX S)
          = (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) * X ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 from by ring, velu_reflect_shift hCPXdeg]
      rw [veluXNum, reflect_add, e1, e2]
    have hPhirefl : reflect (3 * m + 9) (veluPhiNum S)
        = 4 * (reflect (m + 3) (veluXNum S)) ^ 3
          + C W.b₂ * ((reflect (m + 3) (veluXNum S)) ^ 2 * reflect (m + 2) (veluH S) * X)
          + (2 * C W.b₄ - 20 * C (W.veluT S))
              * ((reflect (m + 3) (veluXNum S)) * (reflect (m + 2) (veluH S)) ^ 2 * X ^ 2)
          + (C W.b₆ - 4 * C W.b₂ * C (W.veluT S) - 28 * C (W.veluW S))
              * ((reflect (m + 2) (veluH S)) ^ 3 * X ^ 3) := by
      have e1 : reflect (3 * m + 9) ((veluXNum S) ^ 3)
          = (reflect (m + 3) (veluXNum S)) ^ 3 := by
        rw [show 3 * m + 9 = 3 * (m + 3) from by ring, velu_reflect_pow hXNdeg 3]
      have e2 : reflect (3 * m + 9) ((veluXNum S) ^ 2 * veluH S)
          = ((reflect (m + 3) (veluXNum S)) ^ 2 * reflect (m + 2) (veluH S)) * X := by
        have hd : ((veluXNum S) ^ 2 * veluH S).natDegree ≤ 3 * m + 8 := by
          refine le_trans natDegree_mul_le ?_; omega
        rw [show 3 * m + 9 = (3 * m + 8) + 1 from by ring, velu_reflect_shift hd, pow_one,
          show 3 * m + 8 = 2 * (m + 3) + (m + 2) from by ring,
          reflect_mul _ _ hxn2 (le_of_eq hHdeg), velu_reflect_pow hXNdeg 2]
      have e3 : reflect (3 * m + 9) (veluXNum S * (veluH S) ^ 2)
          = ((reflect (m + 3) (veluXNum S)) * (reflect (m + 2) (veluH S)) ^ 2) * X ^ 2 := by
        have hd : (veluXNum S * (veluH S) ^ 2).natDegree ≤ 3 * m + 7 := by
          refine le_trans natDegree_mul_le ?_; omega
        rw [show 3 * m + 9 = (3 * m + 7) + 2 from by ring, velu_reflect_shift hd,
          show 3 * m + 7 = (m + 3) + 2 * (m + 2) from by ring,
          reflect_mul _ _ hXNdeg hh2, velu_reflect_pow (le_of_eq hHdeg) 2]
      have e4 : reflect (3 * m + 9) ((veluH S) ^ 3)
          = (reflect (m + 2) (veluH S)) ^ 3 * X ^ 3 := by
        rw [show 3 * m + 9 = (3 * m + 6) + 3 from by ring, velu_reflect_shift hh3,
          show 3 * m + 6 = 3 * (m + 2) from by ring, velu_reflect_pow (le_of_eq hHdeg) 3]
      rw [veluPhiNum, reflect_add, reflect_add, reflect_add, mul_assoc (C W.b₂),
        mul_assoc (C (2 * W.b₄ - 20 * W.veluT S)), reflect_C_mul, reflect_C_mul,
        reflect_C_mul, reflect_C_mul, e1, e2, e3, e4]
      simp only [map_sub, map_mul, map_ofNat]
    have hPsirefl : reflect 3 (veluPsi W)
        = 4 + C W.b₂ * X + 2 * C W.b₄ * X ^ 2 + C W.b₆ * X ^ 3 := by
      rw [veluPsi]
      rw [show (C (2 * W.b₄) * X : Polynomial F) = C (2 * W.b₄) * X ^ 1 from by rw [pow_one]]
      rw [reflect_add, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
        reflect_C_mul_X_pow, reflect_C]
      simp only [revAt, Function.Embedding.coeFn_mk, map_mul, map_ofNat]
      norm_num
    have hThetarefl : reflect (4 * m + 11) (veluTheta S)
        = (4 + C W.b₂ * X + 2 * C W.b₄ * X ^ 2 + C W.b₆ * X ^ 3)
            * ((reflect (m + 2) (veluH S)) ^ 2
                - (reflect (2 * m + 2) (veluPV S)) * X ^ 2) ^ 2
          - reflect (m + 2) (veluH S)
            * (4 * (reflect (m + 2) (veluH S)
                    + (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) * X ^ 2) ^ 3
              + C W.b₂ * ((reflect (m + 2) (veluH S)
                    + (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) * X ^ 2) ^ 2
                  * reflect (m + 2) (veluH S) * X)
              + (2 * C W.b₄ - 20 * C (W.veluT S))
                  * ((reflect (m + 2) (veluH S)
                      + (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) * X ^ 2)
                    * (reflect (m + 2) (veluH S)) ^ 2 * X ^ 2)
              + (C W.b₆ - 4 * C W.b₂ * C (W.veluT S) - 28 * C (W.veluW S))
                  * ((reflect (m + 2) (veluH S)) ^ 3 * X ^ 3)) := by
      have e1 : reflect (4 * m + 11) (veluPsi W * (veluXi S) ^ 2)
          = reflect 3 (veluPsi W) * (reflect (2 * m + 4) (veluXi S)) ^ 2 := by
        have hxi2 : ((veluXi S) ^ 2).natDegree ≤ 4 * m + 8 :=
          le_trans natDegree_pow_le (by omega)
        rw [show 4 * m + 11 = 3 + (4 * m + 8) from by ring,
          reflect_mul _ _ hPsideg hxi2,
          show 4 * m + 8 = 2 * (2 * m + 4) from by ring, velu_reflect_pow hXideg 2]
      have e2 : reflect (4 * m + 11) (veluH S * veluPhiNum S)
          = reflect (m + 2) (veluH S) * reflect (3 * m + 9) (veluPhiNum S) := by
        rw [show 4 * m + 11 = (m + 2) + (3 * m + 9) from by ring,
          reflect_mul _ _ (le_of_eq hHdeg) hPhideg]
      rw [veluTheta, reflect_sub, e1, e2, hPsirefl, hXirefl, hPhirefl, hXNrefl]
    -- final jets in Vélu's constants
    have hjpx0' : (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)).coeff 0 = W.veluT S := by
      rw [reflect_C_mul, coeff_C_mul, hjpx0, hsumT, veluT]
    have hsplit : ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
        - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q')
        = (∑ Q ∈ S.erase 0, veluWTerm W Q)
          - (∑ Q' ∈ S.erase 0, veluPointX Q') * ∑ Q ∈ S.erase 0, veluTTerm W Q := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun Q _ => by rw [velu_wTerm_eq]; ring
      · exact Finset.sum_congr rfl fun Q _ => by ring
    have hjpx1' : (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)).coeff 1
        = W.veluT S * (-∑ Q ∈ S.erase 0, veluPointX Q) + W.veluW S := by
      rw [reflect_C_mul, coeff_C_mul, hjpx1, hsplit, veluT, veluW, ← hsumT, ← hsumW]
      ring
    have hjpv0' : (reflect (2 * m + 2) (veluPV S)).coeff 0 = W.veluT S := by
      rw [hjpv0, ← Finset.mul_sum, veluT, ← hsumT]
    have hjpv1' : (reflect (2 * m + 2) (veluPV S)).coeff 1
        = 2 * (W.veluT S * (-∑ Q ∈ S.erase 0, veluPointX Q)) + 2 * W.veluW S := by
      rw [hjpv1, hsplit, veluT, veluW, ← hsumT, ← hsumW]
      field_simp
      ring
    have hdvd := velu_reflect_theta_dvd (reflect (m + 2) (veluH S))
      (reflect (m + 1) (C ((2 : F)⁻¹) * veluPX S)) (reflect (2 * m + 2) (veluPV S))
      (W.veluT S) (W.veluW S) W.b₂ W.b₄ W.b₆ (-∑ Q ∈ S.erase 0, veluPointX Q)
      hjh0 hjh1 hjpx0' hjpx1' hjpv0' hjpv1'
    rw [← hThetarefl] at hdvd
    have hres := velu_degree_lt_of_reflect hThetadeg hdvd
    have heq : 4 * (S.card - 1) = 4 * m + 11 + 1 - 4 := by omega
    rw [heq]
    exact hres

end PolePolyDegree

/-- **PROVEN over the two leaves.** `veluTheta S = 0`: a polynomial divisible by `veluH⁴` and
of degree below `deg veluH⁴ = 4(|S| − 1)` is zero. -/
theorem velu_theta_eq_zero {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    veluTheta S = 0 :=
  Polynomial.eq_zero_of_dvd_of_degree_lt
    (velu_theta_dvd hS hodd fun _ hQ =>
      velu_theta_local_dvd hS hodd (velu_theta_degree_lt hS hodd).le hQ)
    (by rw [veluH_pow_degree hS]; exact velu_theta_degree_lt hS hodd)

/-- **Vélu's rational-function identity, with `y` eliminated** (PROVEN 2026-07-26 over the two
polynomial leaves `velu_theta_local_dvd` and `velu_theta_degree_lt`; itself cut 2026-07-26 out
of `velu_equation_pole`).

Writing `x = x(P)`, `X = x + ½ Σ_{Q ∈ S} veluPoleX`, `D = Σ_{Q ∈ S} veluPoleV`,
`t = veluT S` and `w = veluW S`, this is the ONE-VARIABLE identity

  `(4x³ + b₂x² + 2b₄x + b₆)·(1 − D)² = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)`.

Nothing here mentions `y`: `velu_pole_V` has already replaced the completed square
`V = 2Y + a₁X + a₃` by `(2y + a₁x + a₃)(1 − D)`, and `(2y + a₁x + a₃)² = 4x³ + b₂x² +
2b₄x + b₆` is the Weierstrass equation at `P`. So this is the whole remaining content of
Vélu's theorem, part 2.

The proof is the clearing of denominators described at the head of this section: evaluate
`veluTheta S = 0` at `x`, recognise the three factors as `Ψ(x)`, `H(x)²(1 − D)` and
`H(x)³Φ(X)` (`veluPX_eval`, `veluPV_eval`), and divide by `H(x)⁴ ≠ 0`
(`veluH_eval_ne_zero`, i.e. `velu_X_ne`).

**Faithfulness.** Validated in PARI/GP over `𝔽_p` for `101 ≤ p ≤ 500` and kernel orders up to
`523`: with a genuine subgroup, 75789 instances pass and none fail; with the `±`-stable
NON-subgroup `{0, G, −G}` for `G` of order `≥ 5`, for which every formula above is equally
well defined, 31006 of 31143 instances FAIL. So `hS` is essential and the pole form does not
carry it.

**SUPERSEDED ROUTE, kept for the record** (integration note, 2026-07-26). The
Laurent-expansion analysis below was the plan for `velu_pole_identity` when it was
still open. That leaf is now PROVEN, by a different route — clear denominators to
`veluTheta S = 0` and split it into `velu_theta_local_dvd` and
`velu_theta_degree_lt`, both of which are also proven. The four local conditions
below are therefore NOT needed, and in particular the missing ingredient flagged at
the end (invariance of the invariant differential) is NOT a blocker for anything.
The closed forms are recorded because they are independently verified and may serve
`velu_map_add_of_notMem`, the one leaf still open in this file.

1. *No poles*: `h⁶` divides the difference. A Laurent expansion at `x_Q` (computed in
   PARI/GP) shows the `d^{-6}` and `d^{-5}` coefficients vanish identically — this is
   exactly `u_Q = 4x_Q³ + b₂x_Q² + 2b₄x_Q + b₆`, the Weierstrass equation at `Q` — while
   the `d^{-4}, …, d^{-1}` coefficients impose four relations, and only four, on the
   Taylor coefficients `r₀, r₁, r₂, r₃` at `x_Q` of

     `R(x) := Σ_{Q' ∈ S ∖ {Q, −Q}} veluPoleX W x Q'`.

   THIS is where closure of `S` under addition is consumed. See below: all four `r_j`
   have closed forms in the group law.
2. *Vanishing at infinity*: the difference has degree `< 6·deg h`, which pins the top four
   coefficients. `w = veluW S` occurs ONLY here — it is absent from every pole condition,
   appearing first in the `d^0` coefficient — so this half is where `w` is consumed.

**The four local conditions, in closed form** (each confirmed on 50744 instances in
PARI/GP, `101 ≤ p ≤ 400`, general `a₁, a₂, a₃`; NONE of them is proven here). Write
`v(Z) = 2y(Z) + a₁x(Z) + a₃`, `τ(z) = 6z² + b₂z + b₄` (`= ½ψ'(z) = veluTTerm` away from
`0`), `τ_Q = τ(x_Q)`, and `T = 2·veluT S − τ(x_Q) − τ(x_{2Q})`. Then

  `r₀ = 2(x_Q − x_{2Q})`
  `r₁ = −2 − 2 v(2Q)/v(Q)`
  `r₂ = T/v(Q)² + τ_Q(v(Q) + v(2Q))/v(Q)³`
  `r₃ = ⅙[W₃/v(Q)³ − 3W₂τ_Q/v(Q)⁴ − W₁(12x_Q + b₂)/v(Q)³ + 3W₁τ_Q²/v(Q)⁵]`,
  `W₁ = −2(v(Q) + v(2Q))`, `W₂ = 2T`,
  `W₃ = −2[(12x_Q + b₂)v(Q) + (12x_{2Q} + b₂)v(2Q)]`.

They come from ONE generating principle, and every ingredient except the last is already
PROVEN in this file:

* `velu_pair_X` rewrites `veluPoleX W x Q' = x(P+Q') + x(P−Q') − 2x_{Q'}` for a point `P`
  with `x(P) = x`, so `R` is a sum of coordinates of translates.
* Reindexing `Q' ↦ Q ± Q'` (`velu_sum_translate`) sends `S ∖ {0, Q, −Q}` onto
  `S ∖ {0, Q, 2Q}` for BOTH signs — this is exactly the use of closure under addition, and
  it is why `2Q` is the only new point appearing anywhere above.
* The vanishing sums: `Σ_{Z ∈ S ∖ 0} v(Z) = 0` is `velu_sum_kernel`; `Σ_{Z ∈ S ∖ 0} x_Z v(Z) = 0`
  is the same `±`-pairing (`velu_sum_neg`), whence `Σ_{Z ∈ S ∖ 0} τ'(x_Z)v(Z) = 0`; and
  `Σ_{Z ∈ S ∖ 0} τ(x_Z) = 2·veluT S` is the definition of `veluT`.
* NOT yet in this file: **invariance of the invariant differential** `dx/v`, i.e.
  `d x(P+Q')/d x(P) = v(P+Q')/v(P)` and `d v(Z)/d x(P) = τ(x_Z)/v(P)`. Despite the
  notation this needs no calculus — it is an algebraic identity in the explicit `addX`
  formula and should fall to `field_simp; ring`, in the same style as
  `velu_addX_pair_identity`. It is what produces `r₁, r₂, r₃` from `r₀`, by successive
  differentiation, and it is the one genuinely new brick the "no poles" half needs.

A warning against a natural false guess: `r₁, r₂, r₃` are NOT the Taylor coefficients of
`2(x − φ(x)/ψ(x))`, the duplication map whose value gives `r₀`. That was tested and fails
in 220 of 222 instances at every order `≥ 1`.

**`hodd` is not needed for the TRUTH of this statement**, only for this proof of it. The same
sweep finds the identity holding verbatim for kernels of order `2`, `4` and `6` (16077
instances, none failing; re-confirmed here at 901 + 890 further instances), because the
halving convention reproduces Vélu's SEPARATE `2`-torsion coefficients automatically: at a
`2`-torsion `Q` one has `2y_Q + a₁x_Q + a₃ = 0`, so `u_Q = 0` and
`veluTTerm W Q = 6x_Q² + b₂x_Q + b₄ = 2 g^x_Q`, whence `½·veluTTerm W Q = g^x_Q` and
`½·veluWTerm W Q = x_Q g^x_Q` — exactly Vélu's `t_Q` and `w_Q` in the order-`2` case. What
`hodd` buys HERE is `veluH_factor`: without it a `2`-torsion `Q` contributes a SIMPLE root to
`veluH`, and the numerators `veluPX`, `veluPV` would have to be defined differently. -/
theorem velu_pole_identity {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆) *
        (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) ^ 2 =
      4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
        W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
        (2 * W.b₄ - 20 * W.veluT S) *
          (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
        (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S) := by
  have hH := veluH_eval_ne_zero hS hP
  have hΘ : (veluPsi W).eval (veluPointX P) * ((veluXi S).eval (veluPointX P)) ^ 2
      - (veluH S).eval (veluPointX P) * ((veluPhiNum S).eval (veluPointX P)) = 0 := by
    have h0 := congrArg (Polynomial.eval (veluPointX P)) (velu_theta_eq_zero hS hodd)
    simpa [veluTheta] using h0
  have hPsi : (veluPsi W).eval (veluPointX P)
      = 4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆ := by
    simp only [veluPsi, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
  have hXi : (veluXi S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 2
          * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
    rw [veluXi, Polynomial.eval_sub, Polynomial.eval_pow, veluPV_eval hS hodd hP]; ring
  have hXN : (veluXNum S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P)
          * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) := by
    rw [veluXNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, veluPX_eval hS hodd hP]
    ring
  have hPhi : (veluPhiNum S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 3
        * (4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
            W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
            (2 * W.b₄ - 20 * W.veluT S) *
              (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
            (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S)) := by
    simp only [veluPhiNum, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C]
    rw [hXN]
    ring
  rw [hPsi, hXi, hPhi] at hΘ
  have key : ((veluH S).eval (veluPointX P)) ^ 4 *
      (((4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆) *
          (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) ^ 2)
        - (4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
            W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
            (2 * W.b₄ - 20 * W.veluT S) *
              (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
            (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S))) = 0 := by
    linear_combination hΘ
  rcases mul_eq_zero.mp key with h1 | h2
  · exact absurd h1 (pow_ne_zero _ hH)
  · exact sub_eq_zero.mp h2

/-! ### The Vélu `x`-map as a rational function, and its fibre over a `2`-torsion image

Everything below is PROVEN and is what `velu_coordX_twoTorsion_ne` (in the next section)
consumes. None of it depends on `velu_pole_identity` or on any other open leaf: the two
inputs are `veluPX_eval`/`veluPV_eval` (the cleared-denominator forms of Vélu's pole
expansion, proven above) and the translation/negation invariances of the Vélu coordinates
(proven in the `Identities` section).

The content is that `veluXNum S / veluH S` IS the Vélu `x`-coordinate as a rational
function of `x` (`veluXNum_eval`), that it is monic of degree `|S|` over a denominator of
degree `|S| − 1` (`veluXNum_monic`, `veluXNum_degree`), and — the one genuinely new
identity — that its logarithmic derivative is Vélu's `Ξ`,

  `veluXNum' · veluH − veluXNum · veluH' = veluXi`      (`velu_dlog_XNum`),

which is the polynomial form of `dX/dx = 1 − Σ veluPoleV`. That is exactly what turns the
translates `x(T + Q)` of a `2`-torsion point into DOUBLE roots of `veluXNum − X(T)·veluH`,
and the double roots are what make the degree count work. -/

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN.** Two nonzero points with the same coordinates are equal. -/
lemma velu_point_eq_of_coords {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : veluPointX P = veluPointX Q) (hy : veluPointY P = veluPointY Q) : P = Q := by
  obtain _ | ⟨x₁, y₁, h₁⟩ := P
  · exact absurd rfl hP
  obtain _ | ⟨x₂, y₂, h₂⟩ := Q
  · exact absurd rfl hQ
  exact velu_point_some_eq hx hy

omit [CharZero F] in
/-- **PROVEN.** The completed square `2y + a₁x + a₃` vanishes exactly at the `2`-torsion:
it is `y − negY x y`, so it is nonzero at an affine point with `−P ≠ P`. -/
lemma velu_two_y_ne_zero {P : W.Point} (hP0 : P ≠ 0) (hP2 : -P ≠ P) :
    2 * veluPointY P + W.a₁ * veluPointX P + W.a₃ ≠ 0 := by
  intro h
  have hneg0 : (-P : W.Point) ≠ 0 := fun hc => hP0 (neg_eq_zero.mp hc)
  refine hP2 (velu_point_eq_of_coords hneg0 hP0 (velu_pointX_neg P) ?_)
  rw [velu_pointY_neg P hP0]
  linear_combination -h

omit [CharZero F] in
/-- **PROVEN.** The Vélu image of a `2`-torsion point outside the kernel is again
`2`-torsion: `Y(T) = Y(−T) = negY (X(T), Y(T))` by `veluCoordY_neg`. -/
lemma velu_twoTorsion_coordY {S : Finset W.Point} (hS : IsPointSubgroup S)
    {T : W.Point} (hT : T ∉ S) (hT2 : -T = T) :
    2 * W.veluCoordY S T + W.a₁ * W.veluCoordX S T + W.a₃ = 0 := by
  have h := veluCoordY_neg hS hT
  rw [hT2, veluCurve_negY] at h
  simp only [WeierstrassCurve.Affine.negY] at h
  linear_combination h

omit [CharZero F] in
/-- **PROVEN.** `T + Q ∉ S` for `T ∉ S` and `Q ∈ S`. -/
lemma velu_add_notMem {S : Finset W.Point} (hS : IsPointSubgroup S)
    {T : W.Point} (hT : T ∉ S) {Q : W.Point} (hQ : Q ∈ S) : T + Q ∉ S := by
  intro hc
  refine hT ?_
  have := hS.add_mem _ hc _ (hS.neg_mem _ hQ)
  simpa using this

omit [CharZero F] in
/-- **PROVEN.** A translate `T + Q` of a `2`-torsion point by a NONZERO element of an
odd-order subgroup is never `2`-torsion — `−(T + Q) = T + (−Q)`, so `2`-torsion would force
`−Q = Q`, impossible in an odd-order subgroup (`velu_twoTorsion_notMem`). -/
lemma velu_add_not_twoTorsion {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {T : W.Point} (hT2 : -T = T) {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    -(T + Q) ≠ T + Q := by
  intro hc
  refine velu_twoTorsion_notMem hS hodd (Finset.ne_of_mem_erase hQ) ?_
    (Finset.mem_of_mem_erase hQ)
  have h1 : T + -Q = T + Q := by
    calc T + -Q = -T + -Q := by rw [hT2]
      _ = -(T + Q) := by abel
      _ = T + Q := hc
  exact add_left_cancel h1

/-- **PROVEN: the Vélu `x`-map is RAMIFIED at every translate `T + Q` of a `2`-torsion point
by a nonzero kernel element.** In pole form the ramification is the vanishing of
`1 − Σ_{Q' ∈ S} veluPoleV` at `x(T + Q)`, i.e. `dX/dx = 0` there.

Proof: `velu_pole_V` factors `2Y + a₁X + a₃ = (2y + a₁x + a₃)·(1 − Σ veluPoleV)` at the point
`T + Q`. The left side vanishes because the Vélu image of `T + Q` equals that of `T`
(`veluCoordX_add_mem`, `veluCoordY_add_mem`) and the image of a `2`-torsion point is
`2`-torsion (`velu_twoTorsion_coordY`); the first factor on the right does not vanish
because `T + Q` is itself not `2`-torsion (`velu_add_not_twoTorsion`, where `hodd` is
used). -/
lemma velu_poleV_sum_eq_one {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {T : W.Point} (hT : T ∉ S) (hT2 : -T = T) {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    ∑ Q' ∈ S, veluPoleV W (veluPointX (T + Q)) Q' = 1 := by
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  have hTQ : T + Q ∉ S := velu_add_notMem hS hT hQS
  have hTQ0 : T + Q ≠ 0 := fun hc => hTQ (hc ▸ hS.zero_mem)
  have hTQ2 : -(T + Q) ≠ T + Q := velu_add_not_twoTorsion hS hodd hT2 hQ
  have hV := velu_pole_V hS hTQ
  rw [← velu_coordX_eq hS hTQ, ← velu_coordY_eq hS hTQ, veluCoordX_add_mem hS T hQS,
    veluCoordY_add_mem hS T hQS, velu_twoTorsion_coordY hS hT hT2] at hV
  rcases mul_eq_zero.mp hV.symm with h | h
  · exact absurd h (velu_two_y_ne_zero hTQ0 hTQ2)
  · linear_combination -h

omit [CharZero F] in
lemma veluHq_monic (S : Finset W.Point) (Q : W.Point) : (veluHq S Q).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

omit [CharZero F] in
/-- **PROVEN.** `deg veluH = 2 + deg veluHq` — the `±`-pair form of `veluH_factor`. -/
lemma veluH_degree_eq {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (veluH S).degree = 2 + (veluHq S Q).degree := by
  rw [veluH_factor hS hodd hQ, Polynomial.degree_mul, Polynomial.degree_pow,
    Polynomial.degree_X_sub_C]
  norm_num

omit [CharZero F] in
/-- **PROVEN.** `deg veluPX < deg veluH`: each summand is a linear polynomial times
`veluHq`, of degree `≤ deg veluH − 1`. -/
lemma veluPX_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluPX S).degree < (veluH S).degree := by
  have hHne : (veluH S) ≠ 0 := (veluH_monic S).ne_zero
  have hbot : (⊥ : WithBot ℕ) < (veluH S).degree :=
    bot_lt_iff_ne_bot.mpr fun h => hHne (Polynomial.degree_eq_bot.mp h)
  rw [veluPX]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff hbot]
  intro Q hQ
  have hHq : (veluHq S Q) ≠ 0 := (veluHq_monic S Q).ne_zero
  have hHqbot : (veluHq S Q).degree ≠ ⊥ := fun h => hHq (Polynomial.degree_eq_bot.mp h)
  have hg : (Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
      + Polynomial.C (veluUTerm W Q)).degree < 2 := by
    refine lt_of_le_of_lt (?_ : _ ≤ (1 : WithBot ℕ)) (by norm_num)
    compute_degree
  rw [Polynomial.degree_mul, veluH_degree_eq hS hodd hQ]
  exact WithBot.add_lt_add_right hHqbot hg

omit [CharZero F] in
lemma veluH_degree_eq_card {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluH S).degree = ((S.card - 1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (veluH_monic S).ne_zero, veluH_natDegree hS]

omit [CharZero F] in
lemma velu_XH_degree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (Polynomial.X * veluH S : Polynomial F).degree = ((S.card : ℕ) : WithBot ℕ) := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  rw [Polynomial.degree_mul, Polynomial.degree_X, veluH_degree_eq_card hS,
    ← Nat.cast_one (R := WithBot ℕ), ← Nat.cast_add]
  congr 1
  omega

lemma velu_CPX_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (Polynomial.C ((2 : F)⁻¹) * veluPX S).degree
      < (Polynomial.X * veluH S : Polynomial F).degree := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have h2ne : ((2 : F)⁻¹) ≠ 0 := inv_ne_zero two_ne_zero
  have h1 : (Polynomial.C ((2 : F)⁻¹) * veluPX S).degree ≤ (veluPX S).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C h2ne, zero_add]
  calc (Polynomial.C ((2 : F)⁻¹) * veluPX S).degree ≤ (veluPX S).degree := h1
    _ < (veluH S).degree := veluPX_degree_lt hS hodd
    _ = ((S.card - 1 : ℕ) : WithBot ℕ) := veluH_degree_eq_card hS
    _ < ((S.card : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : S.card - 1 < S.card)
    _ = (Polynomial.X * veluH S : Polynomial F).degree := (velu_XH_degree hS).symm

/-- **PROVEN.** `veluXNum S = T·veluH S + ½·veluPX S` is MONIC: the second summand has
strictly smaller degree. -/
lemma veluXNum_monic {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluXNum S).Monic := by
  rw [veluXNum]
  exact ((Polynomial.monic_X).mul (veluH_monic S)).add_of_left (velu_CPX_degree_lt hS hodd)

/-- **PROVEN.** `deg (veluXNum S) = |S|` — the Vélu `x`-map has degree `|S|`, as it must. -/
lemma veluXNum_degree {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluXNum S).degree = ((S.card : ℕ) : WithBot ℕ) := by
  rw [veluXNum, Polynomial.degree_add_eq_left_of_degree_lt (velu_CPX_degree_lt hS hodd),
    velu_XH_degree hS]

/-- **PROVEN: `veluPV` is `−½` the derivative of Vélu's `x`-expansion, in cleared form.**

`veluPX' · veluH − veluPX · veluH' = −2·veluPV`. The proof is TERMWISE: substituting
`veluH = (T − x_Q)²·veluHq S Q` (`veluH_factor`) makes the `Q`-summand of the left side
equal to `veluHq² ·(T − x_Q)·(−t_Q(T − x_Q) − 2u_Q)`, in which every occurrence of
`veluHq'` has cancelled, and that is exactly `−2` times the `Q`-summand of `veluPV`. No
Weierstrass equation and no subgroup property beyond `veluH_factor` is used. -/
lemma velu_dlog_PX {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    Polynomial.derivative (veluPX S) * veluH S - veluPX S * Polynomial.derivative (veluH S)
      = -2 * veluPV S := by
  have hC2 : (Polynomial.C (2 : F) : Polynomial F) = 2 := map_ofNat _ 2
  have h2 : (Polynomial.C ((2 : F)⁻¹) : Polynomial F) * 2 = 1 := by
    rw [← hC2, ← Polynomial.C_mul]
    norm_num
  rw [veluPX, veluPV, Polynomial.derivative_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [veluH_factor hS hodd hQ]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_pow,
    Polynomial.C_mul, Nat.cast_ofNat, hC2, sub_zero, mul_one, zero_mul, add_zero, zero_add]
  linear_combination (Polynomial.C (veluTTerm W Q) *
    (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2 * (veluHq S Q) ^ 2) * h2

/-- **PROVEN: the logarithmic derivative of the Vélu `x`-map is `veluXi`.**

`veluXNum' · veluH − veluXNum · veluH' = veluXi`, i.e. `dX/dx = Ξ/H² = 1 − Σ veluPoleV`.
Immediate from `velu_dlog_PX` and `veluXi = veluH² − veluPV`. Together with
`velu_poleV_sum_eq_one` this is what makes `x(T + Q)` a DOUBLE root of
`veluXNum − X(T)·veluH` for `2`-torsion `T`. -/
lemma velu_dlog_XNum {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    Polynomial.derivative (veluXNum S) * veluH S
        - veluXNum S * Polynomial.derivative (veluH S) = veluXi S := by
  have hC2 : (Polynomial.C (2 : F) : Polynomial F) = 2 := map_ofNat _ 2
  have h2 : (Polynomial.C ((2 : F)⁻¹) : Polynomial F) * 2 = 1 := by
    rw [← hC2, ← Polynomial.C_mul]
    norm_num
  have hd := velu_dlog_PX hS hodd
  rw [veluXNum, veluXi]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, zero_mul, one_mul, zero_add]
  linear_combination Polynomial.C ((2 : F)⁻¹) * hd - (veluPV S) * h2

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN.** A common root of `p` and `p'` is a double root of `p`. -/
lemma velu_sq_dvd_of_isRoot {p : Polynomial F} {a : F} (h1 : p.IsRoot a)
    (h2 : (Polynomial.derivative p).IsRoot a) :
    (Polynomial.X - Polynomial.C a) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr h1
  subst hq
  have hq0 : q.IsRoot a := by
    simp only [Polynomial.IsRoot, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul, add_zero] at h2
    exact h2
  obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr hq0
  exact ⟨r, by rw [hr]; ring⟩

end PolePoly

/-! ### Vélu's theorem -/

section Velu

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

omit [W.IsElliptic] in
/-- **Vélu's theorem, part 2a: the quotient equation in pole form** (PROVEN 2026-07-26
over `velu_pole_identity`, itself PROVEN 2026-07-26 over the two polynomial leaves
`velu_theta_local_dvd` and `velu_theta_degree_lt`; this was itself the leaf cut on 2026-07-26 out
of `velu_equation`, whose first half — the passage from the group-law sums to Vélu's
rational functions — is `velu_coordX_eq` and `velu_coordY_eq`).

What this proof does is eliminate `y`. Complete the square on the quotient curve: since
`veluCurve` does not change `a₁`, `a₂`, `a₃`, the quotient equation at `(X, Y)` is
equivalent, after multiplying by `4`, to

  `V² = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)`,  `V := 2Y + a₁X + a₃`.

Now `velu_pole_V` factors `V = (2y + a₁x + a₃)·(1 − Σ_{Q ∈ S} veluPoleV)` — a termwise
field identity (`velu_two_poleY_add_poleX`) in which the `y_Q`-dependence and every
`a₁`-contribution cancel — and the Weierstrass equation at `P` turns `(2y + a₁x + a₃)²`
into `4x³ + b₂x² + 2b₄x + b₆`. What is left is `velu_pole_identity`, a rational-function
identity in `x` ALONE.

The Vélu coefficients are `t = ½ Σ_{Q ∈ S} t_Q` and `w = ½ Σ_{Q ∈ S} w_Q` with
`w_Q = u_Q + x_Q t_Q`, so `veluUTerm` and `veluTTerm` are exactly the data of
`veluCurve W S` — see `veluT`, `veluW`, `veluModel`. -/
theorem velu_equation_pole (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∉ S) :
    (W.veluCurve S).Equation
      (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q)
      (veluPointY P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q) := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hEq : W.Equation (veluPointX P) (veluPointY P) := by
    obtain _ | ⟨x, y, hns⟩ := P
    · exact absurd rfl hP0
    · exact hns.1
  have hV := velu_pole_V hS hP
  have hI := velu_pole_identity hS hodd hP
  have hv : (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) ^ 2 =
      4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆ := by
    rw [Affine.equation_iff] at hEq
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (4 : F) * hEq
  rw [Affine.equation_iff']
  simp only [veluCurve, veluModel, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆] at hv hI ⊢
  set x := veluPointX P with hxdef
  set y := veluPointY P with hydef
  set X := x + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W x Q with hXdef
  set Y := y + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W x y Q with hYdef
  set D := ∑ Q ∈ S, veluPoleV W x Q with hDdef
  linear_combination (2 * Y + W.a₁ * X + W.a₃ + (2 * y + W.a₁ * x + W.a₃) * (1 - D)) / 4 * hV +
    (1 - D) ^ 2 / 4 * hv + hI / 4

omit [W.IsElliptic] in
/-- **Vélu's theorem, part 2: the image lies on the quotient curve** (PROVEN
2026-07-26 over the single arithmetic leaf `velu_equation_pole`).

(Moved textually to the head of this section on 2026-07-26 — statement and proof are
UNCHANGED — because `velu_exists_three_twoTorsion` below now consumes it.)

For a finite subgroup `S` of odd order in `W.Point` and a point `P ∉ S`, the
Vélu coordinates `X(P) = x(P) + Σ_{Q ∈ S ∖ 0} (x(P + Q) − x(Q))` and
`Y(P) = y(P) + Σ_{Q ∈ S ∖ 0} (y(P + Q) − y(Q))` satisfy the equation of
`veluCurve W S`.

The proof rewrites the two group-law sums into Vélu's rational functions —
`velu_coordX_eq` and `velu_coordY_eq`, both PROVEN above out of the `±`-paired
addition law — and appeals to `velu_equation_pole` for the remaining
rational-function verification.

Note `P ∉ S` is exactly what makes every summand defined: `x(P) = x(Q)` would
force `P = ±Q ∈ S` (this is `velu_X_ne`), and `P + Q = 0` would force
`P = −Q ∈ S`. -/
theorem velu_equation (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∉ S) :
    (W.veluCurve S).Equation (W.veluCoordX S P) (W.veluCoordY S P) := by
  rw [velu_coordX_eq hS hP, velu_coordY_eq hS hP]
  exact W.velu_equation_pole S hS hodd hP

omit [CharZero F] [W.IsElliptic] in
/-- **PROVEN.** A point outside the kernel stays nonzero after translation by a kernel
element. -/
lemma velu_add_ne_zero {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point} (hP : P ∉ S)
    {Q : W.Point} (hQ : Q ∈ S) : P + Q ≠ 0 := by
  intro h
  exact hP (by
    have hPQ : P = -Q := by rwa [add_eq_zero_iff_eq_neg] at h
    rw [hPQ]; exact hS.neg_mem _ hQ)

-- (`velu_add_notMem` — `P ∉ S`, `Q ∈ S` ⟹ `P + Q ∉ S` — is already proven in section
-- `PolePoly` above, with `W` implicit and without `[W.IsElliptic]`; a second copy added
-- here at integration was dropped as a duplicate declaration.)

omit [W.IsElliptic] in
/-- **PROVEN: the Wronskian identity `XNum'·H − XNum·H' = Ξ`.**

Vélu's `x`-coordinate is the rational function `X(T) = XNum(T)/H(T)`, and `Ξ/H²` is
`1 − Σ_{Q ∈ S} veluPoleV`, which is exactly `dX/dT`. So this lemma is the *polynomial* form
of `X'(T) = 1 − Σ veluPoleV` — the statement `veluPoleV` was designed to satisfy — with the
denominators cleared. **No analysis is involved**: `derivative` is the formal derivative, and
the proof is a termwise algebraic identity.

The computation, worth recording because it is short and entirely mechanical. Write
`D = T − x_Q`, `Hq = veluHq S Q`, so that `H = D²·Hq` (`veluH_factor`, the one place `hodd`
is used), and put `A = t_Q·D + u_Q` and `B = u_Q·D + ½t_Q·D²`, so that
`PX = Σ_Q A·Hq` and `PV = Σ_Q B·Hq²`. Then for each `Q`, since `A' = t_Q` and
`H' = 2D·Hq + D²·Hq'`,

  `(A·Hq)'·H − (A·Hq)·H' = A'·Hq²·D² − 2A·D·Hq² = Hq²·(−t_Q D² − 2u_Q D) = −2·B·Hq²`,

the `Hq'` terms cancelling identically. Summing over `Q ∈ S ∖ {0}` gives
`PX'·H − PX·H' = −2·PV`, and since `XNum = T·H + ½PX` and `Ξ = H² − PV`,

  `XNum'·H − XNum·H' = H² + ½(PX'·H − PX·H') = H² − PV = Ξ`.

This is what converts "`Ξ` vanishes at `x_P`" into "`x_P` is a MULTIPLE root of the fibre
polynomial", which is how `velu_two_mem_of_xi_eq_zero` detects a collision in the fibre. -/
theorem velu_wronskian (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    Polynomial.derivative (veluXNum S) * veluH S
        - veluXNum S * Polynomial.derivative (veluH S) = veluXi S := by
  have h2C : Polynomial.C (2 : F) = (2 : Polynomial F) := map_ofNat Polynomial.C 2
  have hc : (2 : Polynomial F) * Polynomial.C ((2 : F)⁻¹) = 1 := by
    rw [← h2C, ← Polynomial.C_mul]
    norm_num
  have hterm : ∀ Q ∈ S.erase 0,
      Polynomial.derivative
            ((Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
              + Polynomial.C (veluUTerm W Q)) * veluHq S Q) * veluH S
          - ((Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
              + Polynomial.C (veluUTerm W Q)) * veluHq S Q)
            * Polynomial.derivative (veluH S)
        = -2 * ((Polynomial.C (veluUTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q))
              + Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
                * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2) * (veluHq S Q) ^ 2) := by
    intro Q hQ
    have hct : (2 : Polynomial F) * Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
        = Polynomial.C (veluTTerm W Q) := by
      rw [← h2C, ← Polynomial.C_mul]
      congr 1
      field_simp
    rw [veluH_factor hS hodd hQ]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_pow,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, sub_zero, zero_mul, add_zero,
      zero_add, mul_one, h2C]
    linear_combination ((Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2
      * (veluHq S Q) ^ 2) * hct
  have key : Polynomial.derivative (veluPX S) * veluH S
      - veluPX S * Polynomial.derivative (veluH S) = -2 * veluPV S := by
    rw [veluPX, veluPV, Polynomial.derivative_sum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [veluXNum, veluXi]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, zero_mul, one_mul, zero_add]
  linear_combination Polynomial.C ((2 : F)⁻¹) * key - veluPV S * hc

omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN.** A root of `p` that is also a root of `p'` is at least a DOUBLE root. Written
out rather than routed through `rootMultiplicity` because that is all this file needs: divide
`p` by `X − a` once, differentiate, and observe that the quotient inherits the root. -/
lemma velu_sq_dvd_of_isRoot_derivative {p : Polynomial F} {a : F}
    (h : p.IsRoot a) (h' : (derivative p).IsRoot a) : (X - C a) ^ 2 ∣ p := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr h)
  have hq0 : q.IsRoot a := by
    have hd : derivative p = q + (X - C a) * derivative q := by
      rw [hq]; simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
        one_mul]
    have hz := h'
    rw [IsRoot, hd] at hz
    simpa using hz
  obtain ⟨r, hr⟩ := (dvd_iff_isRoot.mpr hq0)
  exact ⟨r, by rw [hq, hr]; ring⟩

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN.** `veluHq` has degree `|S| − 3`, read straight off the factorisation
`H = (T − x_Q)²·Hq` of `veluH_factor` — the `±`-pair of `Q` is exactly what is removed. -/
lemma velu_Hq_natDegree {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (veluHq S Q).natDegree + 2 = S.card - 1 := by
  have hfac := veluH_factor hS hodd hQ
  have hHne : veluH S ≠ 0 := (veluH_monic S).ne_zero
  have hHq0 : veluHq S Q ≠ 0 := by
    intro h; rw [h, mul_zero] at hfac; exact hHne hfac
  have hpow : ((X - C (veluPointX Q)) ^ 2 : Polynomial F) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero _)
  have hd := congrArg Polynomial.natDegree hfac
  rw [natDegree_mul hpow hHq0, natDegree_pow, natDegree_X_sub_C, veluH_natDegree hS] at hd
  omega

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN.** `deg (veluPX S) ≤ |S| − 2`, so the correction `½·veluPX` never disturbs the
leading term of `veluXNum = T·H + ½·PX`. Each summand is a degree-`≤ 1` factor times `Hq`. -/
lemma velu_PX_natDegree_le {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluPX S).natDegree ≤ S.card - 2 := by
  rw [veluPX]
  refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
  refine le_trans natDegree_mul_le ?_
  have hlin : (C (veluTTerm W Q) * (X - C (veluPointX Q))
      + C (veluUTerm W Q)).natDegree ≤ 1 := by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_sub_C _))
    · simp
  have hq := velu_Hq_natDegree W hS hodd hQ
  omega

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN: the fibre polynomial `G = veluXNum S − X(P)·veluH S` is MONIC of degree `|S|`.**

Regrouping it as `(T − X(P))·H + ½·PX` exhibits a monic degree-`|S|` head (`veluH` is monic
of degree `|S| − 1`) plus a tail of degree `≤ |S| − 2`. This is what turns the divisibility
`∏ ∣ G` into an equality: `|S|` is also the degree of the product over the coset. -/
lemma velu_fibrePoly_monic {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (P : W.Point) :
    (veluXNum S - C (W.veluCoordX S P) * veluH S).Monic ∧
      (veluXNum S - C (W.veluCoordX S P) * veluH S).natDegree = S.card := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hHm : (veluH S).Monic := veluH_monic S
  have hlin : (X - C (W.veluCoordX S P)).Monic := monic_X_sub_C _
  have hmul : ((X - C (W.veluCoordX S P)) * veluH S).Monic := hlin.mul hHm
  have hdeg : ((X - C (W.veluCoordX S P)) * veluH S).natDegree = S.card := by
    rw [natDegree_mul hlin.ne_zero hHm.ne_zero, natDegree_X_sub_C, veluH_natDegree hS]
    omega
  have hsplit : veluXNum S - C (W.veluCoordX S P) * veluH S
      = (X - C (W.veluCoordX S P)) * veluH S + C ((2 : F)⁻¹) * veluPX S := by
    rw [veluXNum]; ring
  have hPXdeg : (C ((2 : F)⁻¹) * veluPX S).degree
      < ((X - C (W.veluCoordX S P)) * veluH S).degree := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [degree_eq_natDegree hmul.ne_zero, hdeg]
    have h1 : (C ((2 : F)⁻¹) * veluPX S).natDegree ≤ S.card - 2 :=
      le_trans (natDegree_C_mul_le _ _) (velu_PX_natDegree_le W hS hodd)
    exact_mod_cast lt_of_le_of_lt h1 (by omega)
  have hdegadd : ((X - C (W.veluCoordX S P)) * veluH S + C ((2 : F)⁻¹) * veluPX S).degree
      = ((X - C (W.veluCoordX S P)) * veluH S).degree :=
    degree_add_eq_left_of_degree_lt hPXdeg
  refine ⟨by rw [hsplit]; exact hmul.add_of_left hPXdeg, ?_⟩
  rw [hsplit, natDegree_eq_of_degree_eq hdegadd]
  exact hdeg

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN: `H·G' = Ξ` at every point of the fibre.** The Wronskian identity `velu_wronskian`
divided back down at a point `R ∉ S` whose Vélu `x`-coordinate agrees with that of `P` — which
by `veluCoordX_add_mem` is every point of the coset `P + S`. -/
lemma velu_H_mul_deriv_fibrePoly {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P R : W.Point} (hR : R ∉ S)
    (hXeq : W.veluCoordX S R = W.veluCoordX S P) :
    (veluH S).eval (veluPointX R)
        * (derivative (veluXNum S - C (W.veluCoordX S P) * veluH S)).eval (veluPointX R)
      = (veluXi S).eval (veluPointX R) := by
  have hw := congrArg (Polynomial.eval (veluPointX R)) (velu_wronskian W S hS hodd)
  simp only [eval_sub, eval_mul] at hw
  have hGeval : (veluXNum S).eval (veluPointX R)
      = (veluH S).eval (veluPointX R) * W.veluCoordX S P := by
    rw [veluXNum_eval hS hodd hR, hXeq]
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, eval_sub,
    eval_mul, eval_C]
  rw [← hw, hGeval]
  ring

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- **PROVEN: a collision in the fibre forces `Ξ` to vanish** — the converse of
`velu_two_mem_of_xi_eq_zero`. If `2R ∈ S` and `R` is not `2`-torsion on `W`, then
`Ξ(x_R) = 0`.

Neither circular nor dependent on the fibre product identity: `2R ∈ S` says that `−R` and `R`
differ by the kernel element `−2R`, so `veluCoordX_add_mem` / `veluCoordY_add_mem` and
`veluCoordY_neg` give `Y R = negY (X R) (Y R)`. Then `velu_pole_V` factors that as
`(2y_R + a₁x_R + a₃)·(1 − Σ veluPoleV) = 0`, and the first factor is nonzero precisely because
`R` is not `2`-torsion; `veluXi_eval` converts the second into `Ξ(x_R) = 0`.

This is the lemma that supplies the MULTIPLICITY in `velu_xNum_sub_eq_prod`: a fibre point of
a collided pair has `2(P + Q) ∈ S`, hence a vanishing `Ξ`, hence — by `velu_wronskian` — a
double root. -/
lemma velu_xi_eval_eq_zero_of_two_mem {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {R : W.Point} (hR : R ∉ S) (h2 : R + R ∈ S) (hne : R + R ≠ 0) :
    (veluXi S).eval (veluPointX R) = 0 := by
  have hkey : W.veluCoordY S R = (W.veluCurve S).negY (W.veluCoordX S R) (W.veluCoordY S R) := by
    have hmem : -(R + R) ∈ S := hS.neg_mem _ h2
    have hRR : -R = R + -(R + R) := by abel
    have hz := veluCoordY_neg hS hR
    rw [hRR, veluCoordY_add_mem hS R hmem] at hz
    exact hz
  have hzero : 2 * W.veluCoordY S R + W.a₁ * W.veluCoordX S R + W.a₃ = 0 := by
    have hs := hkey
    rw [veluCurve_negY] at hs
    simp only [WeierstrassCurve.Affine.negY] at hs
    linear_combination hs
  have hV := velu_pole_V hS hR
  rw [← velu_coordX_eq hS hR, ← velu_coordY_eq hS hR, hzero] at hV
  have hRne : R ≠ 0 := fun h => hR (h ▸ hS.zero_mem)
  have hfac : 2 * veluPointY R + W.a₁ * veluPointX R + W.a₃ ≠ 0 := by
    intro hL
    refine hne ?_
    cases R with
    | zero => exact absurd rfl hRne
    | some x y hns =>
        simp only [veluPointX_some, veluPointY_some] at hL
        have hyy : y = W.negY x y := by
          simp only [WeierstrassCurve.Affine.negY]; linear_combination hL
        exact Affine.Point.add_of_Y_eq rfl hyy
  have hD : (1 : F) - ∑ Q ∈ S, veluPoleV W (veluPointX R) Q = 0 :=
    (mul_eq_zero.mp hV.symm).resolve_left hfac
  rw [veluXi_eval hS hodd hR, hD, mul_zero]

/-- **PROVEN 2026-07-26: the fibre of the Vélu `x`-map over `X(P)` is exactly the coset
`P + S`**, as an identity of MONIC polynomials of degree `|S|`:

  `veluXNum S − X(P)·veluH S = ∏_{Q ∈ S} (T − x(P + Q))`.

This is the brick under `velu_coord_ne_neg`, hence under the injectivity half of Vélu's
theorem. It is the statement that the Vélu `x`-map has degree `|S|` with fibres exactly the
cosets of `S` — everything else in that node (`velu_wronskian`, the collision criterion
`velu_two_mem_of_xi_eq_zero`, the `±`-case analysis) is bookkeeping around it.

**What is easy and what is not.** The `⊇` half is free: for each `Q ∈ S` the point `P + Q`
lies outside `S` (`velu_add_notMem`), so `veluXNum_eval` applies to it, and translation
invariance `veluCoordX_add_mem` gives `X(P + Q) = X(P)`; hence
`(veluXNum S − X(P)·veluH S)` vanishes at `x(P + Q)`. So every `x(P + Q)` IS a root. Both
sides are monic of degree `|S|` (`veluXNum` is monic of degree `|S|` because `veluH` is monic
of degree `|S| − 1` and `deg veluPX ≤ |S| − 1`). What remains is that these roots EXHAUST the
left side with the right MULTIPLICITIES.

**The multiplicity bookkeeping, which is the whole content, and how to do it.** The map
`Q ↦ x(P + Q)` on `S` collides exactly when `x(P + Q₁) = x(P + Q₂)` with `Q₁ ≠ Q₂`, i.e.
`P + Q₁ = −(P + Q₂)`, i.e. `2P + Q₁ + Q₂ = 0`. So:

* If `2P ∉ S` the map is INJECTIVE, the `|S|` roots are distinct, and the identity is just
  "monic of degree `n` with `n` distinct roots".
* If `2P ∈ S` the involution `Q ↦ −2P − Q` acts on `S` with exactly ONE fixed point `Q*`
  (doubling is a bijection on a group of ODD order, so `2Q* = −2P` has a unique solution),
  pairing the other `|S| − 1` elements. The fibre therefore has `(|S| + 1)/2` distinct
  values: `x(P + Q*)` simple, and `(|S| − 1)/2` values that are DOUBLE.

  The doubling is available and is NOT circular: for `Q ≠ Q*` one has `2(P + Q) = 2P + 2Q ∈ S`
  (both summands lie in `S`), so `−(P + Q) = (P + Q) + (−2(P + Q))` differs from `P + Q` by a
  kernel element; `veluCoordX_add_mem` and `veluCoordY_add_mem` then give
  `Y(P + Q) = negY (X(P + Q)) (Y(P + Q))`, and `velu_pole_V` turns that into
  `Ξ(x(P + Q)) = 0` (the other factor, `2y + a₁x + a₃`, vanishes only when `P + Q` is
  `2`-torsion on `W`, which forces `Q = Q*`). By `velu_wronskian` that says precisely that
  `x(P + Q)` is a DOUBLE root. Multiplicities then sum to `1 + 2·(|S| − 1)/2 = |S| = deg`,
  which closes the count.

The doubling step is `velu_xi_eval_eq_zero_of_two_mem` above, and it is not circular: it is
proven directly from `veluCoordY_neg` and `velu_pole_V`, using neither this identity nor
`velu_two_mem_of_xi_eq_zero` (which is the same equivalence read in the opposite direction).

**How the proof is organised.** It never needs to know WHICH case it is in. Regroup the
product fibrewise (`Finset.prod_fiberwise_of_maps_to`, as in `veluH_pow_eq`) into
`∏_a (T − a)^{m_a}`; show `m_a ≤ 2` (a fibre is contained in `{Q₁, −2P − Q₁}`); show each
`(T − a)^{m_a} ∣ G`, by `dvd_iff_isRoot` when `m_a ≤ 1` and by
`velu_sq_dvd_of_isRoot_derivative` when `m_a = 2` — the second element of the fibre is
exactly what supplies `2P ∈ S`, hence `2(P + Q₁) ∈ S`, hence `Ξ(x(P+Q₁)) = 0`, hence a
vanishing derivative through `velu_H_mul_deriv_fibrePoly`. The factors for distinct `a` are
coprime, so `Finset.prod_dvd_of_coprime` assembles them, and `velu_fibrePoly_monic` closes
the argument: two monic polynomials of the same degree that divide one another are equal.

**Faithfulness note.** `P ∉ S` is needed (otherwise `veluCoordX` is a junk value and
`veluXNum_eval` does not apply); `hodd` is needed through `veluH_factor`, and through
`velu_twoTorsion_notMem` inside `velu_fiber_card`. -/
theorem velu_xNum_sub_eq_prod (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    veluXNum S - Polynomial.C (W.veluCoordX S P) * veluH S
      = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))) := by
  classical
  set G : Polynomial F := veluXNum S - Polynomial.C (W.veluCoordX S P) * veluH S with hG
  obtain ⟨hGm, hGdeg⟩ := velu_fibrePoly_monic W hS hodd P
  -- Every `x(P + Q)`, `Q ∈ S`, is a root of `G`: translation invariance of `X`.
  have hroot : ∀ Q ∈ S, G.IsRoot (veluPointX (P + Q)) := by
    intro Q hQ
    have hPQ : P + Q ∉ S := velu_add_notMem hS hP hQ
    rw [Polynomial.IsRoot, hG]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [veluXNum_eval hS hodd hPQ, veluCoordX_add_mem hS P hQ]
    ring
  -- A fibre has at most two elements, since `x(P+Q₁) = x(P+Q₂)` forces `2P + Q₁ + Q₂ = 0`.
  have hfib : ∀ a : F, ({Q ∈ S | veluPointX (P + Q) = a}).card ≤ 2 := by
    intro a
    rcases Finset.eq_empty_or_nonempty {Q ∈ S | veluPointX (P + Q) = a} with he | ⟨Q₁, hQ₁⟩
    · simp [he]
    · obtain ⟨hQ₁S, hQ₁a⟩ := Finset.mem_filter.mp hQ₁
      refine le_trans (Finset.card_le_card (t := ({Q₁, -(P + P) - Q₁} : Finset W.Point)) ?_) ?_
      · intro Q hQ
        obtain ⟨hQS, hQa⟩ := Finset.mem_filter.mp hQ
        have hx : veluPointX (P + Q) = veluPointX (P + Q₁) := by rw [hQa, hQ₁a]
        rcases velu_pointX_eq_iff (velu_add_ne_zero W hS hP hQS)
            (velu_add_ne_zero W hS hP hQ₁S) hx with h1 | h1
        · exact Finset.mem_insert.mpr (Or.inl (by linear_combination (norm := abel) h1))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
            (by linear_combination (norm := abel) h1)))
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
  -- Regroup the product over the coset into powers indexed by the distinct fibre values.
  have hregroup : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))))
      = ∏ a ∈ S.image (fun Q => veluPointX (P + Q)),
          (Polynomial.X - Polynomial.C a) ^ ({Q ∈ S | veluPointX (P + Q) = a}).card := by
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun Q => veluPointX (P + Q)) (t := S.image (fun Q => veluPointX (P + Q)))
      (fun i hi => Finset.mem_image_of_mem _ hi)
      (fun Q => Polynomial.X - Polynomial.C (veluPointX (P + Q)))]
    refine Finset.prod_congr rfl fun a ha => ?_
    calc ∏ Q ∈ {Q ∈ S | veluPointX (P + Q) = a},
          (Polynomial.X - Polynomial.C (veluPointX (P + Q)))
        = ∏ _Q ∈ {Q ∈ S | veluPointX (P + Q) = a}, (Polynomial.X - Polynomial.C a) :=
          Finset.prod_congr rfl fun Q hQ => by rw [(Finset.mem_filter.mp hQ).2]
      _ = (Polynomial.X - Polynomial.C a) ^ _ := Finset.prod_const _
  -- Each fibre factor divides `G`, and distinct factors are coprime.
  have hdvd : (∏ a ∈ S.image (fun Q => veluPointX (P + Q)),
      (Polynomial.X - Polynomial.C a) ^ ({Q ∈ S | veluPointX (P + Q) = a}).card) ∣ G := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a ha b hb hab
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))).pow
    · intro a ha
      obtain ⟨Q₁, hQ₁S, rfl⟩ := Finset.mem_image.mp ha
      rcases Nat.lt_or_ge
          ({Q ∈ S | veluPointX (P + Q) = veluPointX (P + Q₁)}).card 2 with hlt | hge
      · have h1 : ({Q ∈ S | veluPointX (P + Q) = veluPointX (P + Q₁)}).card ≤ 1 := by omega
        refine dvd_trans (pow_dvd_pow
          (Polynomial.X - Polynomial.C (veluPointX (P + Q₁))) h1) ?_
        rw [pow_one]
        exact Polynomial.dvd_iff_isRoot.mpr (hroot Q₁ hQ₁S)
      · have hc2 : ({Q ∈ S | veluPointX (P + Q) = veluPointX (P + Q₁)}).card = 2 :=
          le_antisymm (hfib _) hge
        rw [hc2]
        -- A second, distinct element of the fibre is exactly a collision `2P + Q₁ + Q₂ = 0`.
        obtain ⟨Q₂, hQ₂mem, hQ₂ne⟩ : ∃ Q₂ ∈ {Q ∈ S | veluPointX (P + Q) = veluPointX (P + Q₁)},
            Q₂ ≠ Q₁ := by
          by_contra hcon
          push_neg at hcon
          have hsub : {Q ∈ S | veluPointX (P + Q) = veluPointX (P + Q₁)} ⊆ {Q₁} :=
            fun Q hQ => Finset.mem_singleton.mpr (hcon Q hQ)
          have hle := Finset.card_le_card hsub
          simp [hc2] at hle
        obtain ⟨hQ₂S, hQ₂a⟩ := Finset.mem_filter.mp hQ₂mem
        have hsum : P + P + (Q₁ + Q₂) = 0 := by
          rcases velu_pointX_eq_iff (velu_add_ne_zero W hS hP hQ₂S)
              (velu_add_ne_zero W hS hP hQ₁S) hQ₂a with h1 | h1
          · exact absurd (by linear_combination (norm := abel) h1 : Q₂ = Q₁) hQ₂ne
          · linear_combination (norm := abel) h1
        have h2P : P + P ∈ S := by
          have he : P + P = -(Q₁ + Q₂) := by linear_combination (norm := abel) hsum
          rw [he]
          exact hS.neg_mem _ (hS.add_mem _ hQ₁S _ hQ₂S)
        have h2PQ : (P + Q₁) + (P + Q₁) ∈ S := by
          have he : (P + Q₁) + (P + Q₁) = (P + P) + (Q₁ + Q₁) := by abel
          rw [he]
          exact hS.add_mem _ h2P _ (hS.add_mem _ hQ₁S _ hQ₁S)
        have hne2 : (P + Q₁) + (P + Q₁) ≠ 0 := by
          intro hz
          exact hQ₂ne (by linear_combination (norm := abel) hsum - hz)
        refine velu_sq_dvd_of_isRoot_derivative (hroot Q₁ hQ₁S) ?_
        have hXeq : W.veluCoordX S (P + Q₁) = W.veluCoordX S P := veluCoordX_add_mem hS P hQ₁S
        have hH : (veluH S).eval (veluPointX (P + Q₁)) ≠ 0 :=
          veluH_eval_ne_zero hS (velu_add_notMem hS hP hQ₁S)
        have hHG := velu_H_mul_deriv_fibrePoly W hS hodd (P := P)
          (velu_add_notMem hS hP hQ₁S) hXeq
        rw [velu_xi_eval_eq_zero_of_two_mem W hS hodd (velu_add_notMem hS hP hQ₁S)
          h2PQ hne2] at hHG
        exact (mul_eq_zero.mp hHG).resolve_left hH
  -- Two monic polynomials of the same degree, one dividing the other, are equal.
  rw [← hregroup] at hdvd
  have hPim : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q)))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
  have hPideg : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q)))).natDegree
      = S.card := by
    rw [Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero _)]
    simp
  obtain ⟨K, hK⟩ := hdvd
  have hK0 : K ≠ 0 := by
    intro h; rw [h, mul_zero] at hK; exact hGm.ne_zero hK
  have hmulm : ((∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q)))) * K).Monic := by
    rw [← hK]; exact hGm
  have hdegK : K.natDegree = 0 := by
    have hc := congrArg Polynomial.natDegree hK
    rw [Polynomial.natDegree_mul hPim.ne_zero hK0, hPideg, hGdeg] at hc
    omega
  have hKm : K.Monic := hPim.of_mul_monic_left hmulm
  have hK1 : K = 1 := by
    have hcoeff : K.coeff 0 = 1 := by
      have hlc : K.leadingCoeff = K.coeff 0 := by rw [Polynomial.leadingCoeff, hdegK]
      rw [← hlc]; exact hKm
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegK, hcoeff, Polynomial.C_1]
  rw [hK, hK1, mul_one]

/-- **PROVEN 2026-07-26 over `velu_xNum_sub_eq_prod` and `velu_wronskian`: `Ξ` vanishes at
`x_P` only if the fibre of the Vélu `x`-map collides at `P`, i.e. only if `2P ∈ S`.**

`Ξ/H²` is the derivative of Vélu's `x`-map (see `velu_wronskian`), so its vanishing at `x_P`
says that `x_P` is a RAMIFICATION point. Concretely: writing `G = veluXNum S − X(P)·veluH S`
for the fibre polynomial, `velu_wronskian` gives `H(x_P)·G'(x_P) = Ξ(x_P)`, and `H(x_P) ≠ 0`
because `P ∉ S` (`veluH_eval_ne_zero`), so `G'(x_P) = 0`. Splitting the product identity at
`Q = 0` as `G = (T − x_P)·K` with `K = ∏_{Q ∈ S ∖ 0}(T − x(P + Q))` gives `G'(x_P) = K(x_P)`,
so some `Q₁ ∈ S ∖ {0}` has `x(P + Q₁) = x_P`. Then `P + Q₁ = ±P`; the `+` sign forces
`Q₁ = 0`, so `P + Q₁ = −P` and `2P = −Q₁ ∈ S`.

This is the step that makes `velu_coord_ne_neg` work in the case its consumer actually needs:
`velu_coordX_twoTorsion_ne` applies it at a `2`-torsion `P`, where `2P = 0 ∈ S` and the fibre
genuinely does collide. -/
theorem velu_two_mem_of_xi_eq_zero (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∉ S)
    (h : (veluXi S).eval (veluPointX P) = 0) : P + P ∈ S := by
  classical
  have hH : (veluH S).eval (veluPointX P) ≠ 0 := veluH_eval_ne_zero hS hP
  set G : Polynomial F := veluXNum S - Polynomial.C (W.veluCoordX S P) * veluH S with hG
  have hderiv : (veluH S).eval (veluPointX P) * (Polynomial.derivative G).eval (veluPointX P)
      = (veluXi S).eval (veluPointX P) :=
    velu_H_mul_deriv_fibrePoly W hS hodd hP rfl
  have hG' : (Polynomial.derivative G).eval (veluPointX P) = 0 := by
    have hz := hderiv
    rw [h] at hz
    exact (mul_eq_zero.mp hz).resolve_left hH
  have hprod : G = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))) :=
    velu_xNum_sub_eq_prod W S hS hodd hP
  set K : Polynomial F :=
    ∏ Q ∈ S.erase 0, (Polynomial.X - Polynomial.C (veluPointX (P + Q))) with hK
  have hsplit : G = (Polynomial.X - Polynomial.C (veluPointX P)) * K := by
    rw [hprod, hK, ← Finset.mul_prod_erase _ _ hS.zero_mem, add_zero]
  have hKeval : K.eval (veluPointX P) = 0 := by
    have hd : (Polynomial.derivative G).eval (veluPointX P) = K.eval (veluPointX P) := by
      rw [hsplit]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
    rw [← hd]; exact hG'
  rw [hK, Polynomial.eval_prod] at hKeval
  obtain ⟨Q₁, hQ₁mem, hQ₁⟩ := Finset.prod_eq_zero_iff.mp hKeval
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ₁
  have hQ₁0 : Q₁ ≠ 0 := Finset.ne_of_mem_erase hQ₁mem
  have hQ₁S : Q₁ ∈ S := Finset.mem_of_mem_erase hQ₁mem
  have hxeq : veluPointX (P + Q₁) = veluPointX P := (sub_eq_zero.mp hQ₁).symm
  have hPne : P ≠ 0 := fun h0 => hP (h0 ▸ hS.zero_mem)
  rcases velu_pointX_eq_iff (velu_add_ne_zero W hS hP hQ₁S) hPne hxeq with h1 | h1
  · exact absurd (by simpa using h1 : Q₁ = 0) hQ₁0
  · have h2 : P + P = -Q₁ := by linear_combination (norm := abel) h1
    rw [h2]; exact hS.neg_mem _ hQ₁S

/-- **PROVEN 2026-07-26 over the single brick `velu_xNum_sub_eq_prod` (itself now PROVEN):
the Vélu images of two points outside the kernel are negatives
of one another only if their sum lies in the kernel.** Equivalently — via `veluCoordX_neg`
and `veluCoordY_neg`, which say that the coordinate pair of `−Q` is `negY` of that of `Q` —
this is the injectivity of the Vélu coordinate map MODULO the kernel:

  `X P = X R ∧ Y P = Y R  →  P − R ∈ S`,   read at `R = −Q`.

It is stated at the level of COORDINATES only: no `veluMap`, no `IsElliptic`, hence no
circularity with `velu_isElliptic`. That is deliberate, because it is needed on both sides of
Vélu's theorem:

* it is goal (1) of the three-goal reduction of `velu_map_add_of_notMem` recorded in that
  leaf's docstring, i.e. the branch of the addition law in which the two images cancel. That
  is this lemma's consumer, and the reason it is not floating.
* it also yields a second, INDEPENDENT proof of `velu_coordX_twoTorsion_ne` below (hence of
  `velu_exists_three_twoTorsion` and `velu_isElliptic`). That theorem nevertheless keeps its
  own degree-count proof, which needs neither this lemma nor `[W.IsElliptic]`; see its
  docstring.

So this is the shared brick, and it should have the SAME OWNER as
`velu_map_add_of_notMem`. Both express one fact: the Vélu map is a homomorphism with kernel
exactly `S`.

Note `P + Q ∉ S` is what makes the statement true rather than vacuous: for `Q = −P` the two
images ARE negatives of one another, by `veluCoordX_neg` and `veluCoordY_neg`.

## The recommended route, and a foundation for it that is ALREADY VERIFIED

Neither mathlib nor the reference project `~/cs/FLT` has ANY isogeny, quotient-curve or
curve-function-field material (checked 2026-07-26: `grep -rl isogeny Mathlib/` is empty). But
that does NOT mean this leaf needs a function-field development — the classical route through
Vélu's RATIONAL FUNCTIONS is elementary, and its foundational identity was compiled on
2026-07-26 and is reproduced here verbatim so the next owner can paste it:

```
theorem velu_addX_pair {x₁ y₁ ξ η : F} (h₁ : W.Equation x₁ y₁) (hQ : W.Equation ξ η)
    (hne : x₁ ≠ ξ) :
    W.addX x₁ ξ (W.slope x₁ ξ y₁ η) + W.addX x₁ ξ (W.slope x₁ ξ y₁ (W.negY ξ η))
      = 2 * ξ + (6 * ξ ^ 2 + W.b₂ * ξ + W.b₄) / (x₁ - ξ)
        + (2 * η + W.a₁ * ξ + W.a₃) ^ 2 / (x₁ - ξ) ^ 2 := by
  have hd : x₁ - ξ ≠ 0 := sub_ne_zero.mpr hne
  rw [equation_iff'] at h₁ hQ
  rw [slope_of_X_ne hne, slope_of_X_ne hne]
  simp only [addX, negY, b₂, b₄]
  field_simp
  ring_nf
  linear_combination 2 * h₁ - 2 * hQ
```

i.e. `x(P+Q) + x(P−Q) = 2 x_Q + t_Q/(x_P − x_Q) + u_Q/(x_P − x_Q)²`, where `t_Q` is exactly
`veluTTerm W Q` and `u_Q = (2y_Q + a₁x_Q + a₃)²` is exactly
`veluWTerm W Q − x_Q * veluTTerm W Q`. It is NOT committed here only because nothing consumes
it yet and free-floating declarations are banned.

**It sums with NO choice of representatives**, which is what makes it fit this file's design.
Summing over `Q ∈ S ∖ {0}` and reindexing the `x(P−Q)` terms by `Q ↦ −Q` — that is
`velu_sum_neg`, already proven above — collapses the left side, giving

  `2 (X P − x_P) = Σ_{Q ∈ S ∖ 0} [ t_Q/(x_P − x_Q) + u_Q/(x_P − x_Q)² ]`.

Every summand is defined because `P ∉ S` forces `x_P ≠ x_Q` (equal `x` would make `P = ±Q`).

## THE PROOF AS CARRIED OUT (2026-07-26)

The classical argument is polynomial, not function-theoretic, and in this file's polynomial
language it is `velu_xNum_sub_eq_prod`: with `G = veluXNum S − X(P)·veluH S`, monic of degree
`|S|`,

  `G = ∏_{Q ∈ S} (T − x(P + Q))`.

Write `R = −Q`, so that by `veluCoordX_neg` and `veluCoordY_neg` the hypothesis says exactly
`X R = X P` and `Y R = Y P`, and the conclusion `P + Q ∈ S` says `P − R ∈ S`. Then:

1. `X R = X P` and `veluXNum_eval` make `x_R` a ROOT of `G`, so `x_R = x(P + Q₀)` for some
   `Q₀ ∈ S`, whence `R = ±(P + Q₀)` by `velu_pointX_eq_iff`.
2. If `R = P + Q₀` then `P + Q = −Q₀ ∈ S` and we are done.
3. If `R = −(P + Q₀)` then `Q = P + Q₀`, so `P + Q = 2P + Q₀`, and it suffices that `2P ∈ S`.
   Here the `Y`-clause finally does its work: it forces `Y P = negY (X P) (Y P)`, and
   `velu_pole_V` factors that as `(2y_P + a₁x_P + a₃)·(1 − Σ veluPoleV) = 0`. The first
   factor vanishing makes `P` itself `2`-torsion on `W`, so `2P = 0 ∈ S`; the second is
   `Ξ(x_P) = 0` by `veluXi_eval`, and `velu_two_mem_of_xi_eq_zero` converts that into
   `2P ∈ S`.

Note that step 3 is exactly the case the consumer `velu_coordX_twoTorsion_ne` lives in, so it
is not an edge case that could have been dodged: at a `2`-torsion `T` the fibre of the Vélu
`x`-map genuinely collides, and the multiplicity bookkeeping inside
`velu_xNum_sub_eq_prod` is what pays for it. -/
theorem velu_coord_ne_neg (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    ¬(W.veluCoordX S P = W.veluCoordX S Q ∧
      W.veluCoordY S P = (W.veluCurve S).negY (W.veluCoordX S Q) (W.veluCoordY S Q)) := by
  classical
  rintro ⟨hx, hy⟩
  have hnQ : -Q ∉ S := fun h => hQ (by simpa using hS.neg_mem _ h)
  have hxR : W.veluCoordX S (-Q) = W.veluCoordX S P := by
    rw [veluCoordX_neg hS, hx]
  -- `x(−Q)` is a root of the fibre polynomial of `P`.
  have hprod := velu_xNum_sub_eq_prod W S hS hodd hP
  have hroot : (∏ Q' ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q')))).eval
      (veluPointX (-Q)) = 0 := by
    rw [← hprod]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [veluXNum_eval hS hodd hnQ, hxR]
    ring
  rw [Polynomial.eval_prod] at hroot
  obtain ⟨Q₀, hQ₀S, hQ₀⟩ := Finset.prod_eq_zero_iff.mp hroot
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ₀
  have hxQ₀ : veluPointX (-Q) = veluPointX (P + Q₀) := sub_eq_zero.mp hQ₀
  have hnQ0 : -Q ≠ 0 := fun h => hnQ (h ▸ hS.zero_mem)
  rcases velu_pointX_eq_iff hnQ0 (velu_add_ne_zero W hS hP hQ₀S) hxQ₀ with h1 | h1
  · -- `−Q = P + Q₀`, so `P + Q = −Q₀ ∈ S`.
    refine hPQ ?_
    have hPQeq : P + Q = -Q₀ := by linear_combination (norm := abel) -h1
    rw [hPQeq]; exact hS.neg_mem _ hQ₀S
  · -- `−Q = −(P + Q₀)`, so `Q = P + Q₀` and `P + Q = 2P + Q₀`.
    have hQeq : Q = P + Q₀ := by linear_combination (norm := abel) -h1
    have hXQ : W.veluCoordX S Q = W.veluCoordX S P := by
      rw [hQeq, veluCoordX_add_mem hS P hQ₀S]
    have hYQ : W.veluCoordY S Q = W.veluCoordY S P := by
      rw [hQeq, veluCoordY_add_mem hS P hQ₀S]
    -- The Vélu image of `P` is then its own negative.
    have hself : W.veluCoordY S P
        = (W.veluCurve S).negY (W.veluCoordX S P) (W.veluCoordY S P) :=
      hy.trans (by rw [hXQ, hYQ])
    have h2P : P + P ∈ S := by
      have hV := velu_pole_V hS hP
      rw [← velu_coordX_eq hS hP, ← velu_coordY_eq hS hP] at hV
      have hzero : 2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃ = 0 := by
        have hs := hself
        rw [veluCurve_negY] at hs
        simp only [WeierstrassCurve.Affine.negY] at hs
        linear_combination hs
      rw [hzero] at hV
      rcases mul_eq_zero.mp hV.symm with hL | hR
      · -- `P` is `2`-torsion on `W`, so `2P = 0 ∈ S`.
        have hPne : P ≠ 0 := fun h => hP (h ▸ hS.zero_mem)
        have h0 : P + P = 0 := by
          cases P with
          | zero => exact absurd rfl hPne
          | some x y hns =>
              simp only [veluPointX_some, veluPointY_some] at hL
              have hyy : y = W.negY x y := by
                simp only [WeierstrassCurve.Affine.negY]; linear_combination hL
              exact Affine.Point.add_of_Y_eq rfl hyy
        rw [h0]; exact hS.zero_mem
      · -- `Ξ(x_P) = 0`, so the fibre collides at `P`.
        refine velu_two_mem_of_xi_eq_zero W S hS hodd hP ?_
        rw [veluXi_eval hS hodd hP, hR, mul_zero]
    refine hPQ ?_
    have hPQeq : P + Q = (P + P) + Q₀ := by rw [hQeq]; abel
    rw [hPQeq]; exact hS.add_mem _ h2P _ hQ₀S

omit [W.IsElliptic] in
/-- **PROVEN 2026-07-26: the Vélu `x`-coordinates of two distinct `2`-torsion points
differ.** Cut 2026-07-26 out of `velu_exists_three_twoTorsion`, of which it was the whole
remaining content.

The obvious argument is CIRCULAR and is not used: "the images are the three nonzero
`2`-torsion points of the quotient, which are distinct because the quotient is nonsingular"
assumes `velu_isElliptic`, which is what this leaf is being used to prove. The docstring of
the previous owner recorded a route through the quotient's addition law; the proof below
takes a different one, purely at the level of the rational function, and consumes NO open
leaf (in particular not `velu_pole_identity`).

**Two independent proofs exist; this file keeps the degree count.** A second, much shorter
route deduces this lemma from `velu_coord_ne_neg` above (equal `x` plus order dividing `2`
forces equal `y`, so the two images are negatives of one another while `T₁ + T₂ ∉ S`). It was
written concurrently and is CORRECT, but the degree count below is kept because it is
independent of `velu_coord_ne_neg`, needs no `[W.IsElliptic]`, and keeps the polynomial
machinery (`veluXNum_monic`, `velu_dlog_XNum`, `veluPX_degree_lt`) consumed.

**Proof.** Write `c = X(T₁)` and `D = veluXNum S − c·veluH S`, so that
`D(x_P) = veluH(x_P)·(X(P) − c)` for every `P ∉ S` (`veluXNum_eval`). Then:

* `D` is MONIC of degree `|S|` (`veluXNum_monic`, `veluXNum_degree`, and
  `deg (c·veluH) = |S| − 1`).
* `x(T₁)` and `x(T₂)` are roots — the second one is exactly the assumption `X(T₁) = X(T₂)`.
* For each `Q ∈ S ∖ {0}`, `x(T₁ + Q)` is a DOUBLE root. It is a root because the Vélu
  coordinates are translation-invariant (`veluCoordX_add_mem`); it is double because the
  derivative of `D` also vanishes there, which by the logarithmic-derivative identity
  `velu_dlog_XNum` reduces to `veluXi(x(T₁ + Q)) = 0`, i.e. to `dX/dx = 0`, i.e. to
  `velu_poleV_sum_eq_one` — the Vélu map is ramified at the translates of a `2`-torsion
  point.
* The `(|S| − 1)/2` distinct values `x(T₁ + Q)` (each attained by exactly `±Q`) together
  with `x(T₁)` and `x(T₂)` are PAIRWISE DISTINCT, and the corresponding pairwise coprime
  factors multiply to a divisor of `D` of degree `2 + (|S| − 1) = |S| + 1 > |S|`.

That contradicts `deg D = |S|`, so `X(T₁) ≠ X(T₂)`.

**Where each hypothesis is used, and `hodd` is genuinely load-bearing.** `hodd` enters
twice — via `velu_twoTorsion_notMem`, to know `−Q ≠ Q` for `Q ∈ S ∖ {0}` (so the fibres of
`Q ↦ x(T₁ + Q)` have exactly two elements, and `T₁ + Q` is not `2`-torsion), and to rule out
`T₁ + T₂ ∈ S`. Without it the statement is FALSE: if `Q₀ ∈ S` is a nonzero `2`-torsion point
then `T₂ = T₁ + Q₀` is `2`-torsion, outside `S`, distinct from `T₁`, and has the same Vélu
`x`-coordinate by `veluCoordX_add_mem`. Checked in PARI/GP: over `𝔽_p`, `11 ≤ p < 60`, with
kernels of every order `2 ≤ n ≤ 30`, **733 of 733** even-order instances are counterexamples.
Dropping the `2`-torsion clauses is likewise fatal (`T₂ = −T₁`, `veluCoordX_neg`).

**Numerics behind the route.** The proof is the polynomial form of the fibre identity
`(X(P) − X(T))·∏_{Q ∈ S∖0}(x_P − x_Q) = ∏_{Q ∈ S}(x_P − x(T + Q))`, verified in PARI/GP in
1618 instances over `𝔽_p` (`11 ≤ p < 60`, all kernel orders) and 202 instances over `ℚ`,
with zero failures. -/
theorem velu_coordX_twoTorsion_ne (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {T₁ T₂ : W.Point} (hT₁ : T₁ ∉ S) (hT₂ : T₂ ∉ S)
    (hn₁ : -T₁ = T₁) (hn₂ : -T₂ = T₂) (hne : T₁ ≠ T₂) :
    W.veluCoordX S T₁ ≠ W.veluCoordX S T₂ := by
  intro hEq
  have hnegT₁ : ∀ Q : W.Point, -(T₁ + Q) = T₁ + -Q := fun Q => by
    rw [show -(T₁ + Q) = -T₁ + -Q from by abel, hn₁]
  have hT₁0 : T₁ ≠ 0 := fun h => hT₁ (h ▸ hS.zero_mem)
  have hT₂0 : T₂ ≠ 0 := fun h => hT₂ (h ▸ hS.zero_mem)
  have hsum0 : T₁ + T₁ = 0 := by rw [← hn₁]; exact add_neg_cancel T₁ ▸ (by rw [hn₁])
  set c := W.veluCoordX S T₁ with hc
  set D : Polynomial F := veluXNum S - Polynomial.C c * veluH S with hD
  -- `D` is monic of degree `|S|`.
  have hCcH : (Polynomial.C c * veluH S).degree < (veluXNum S).degree := by
    rw [veluXNum_degree hS hodd]
    have hle : (Polynomial.C c * veluH S).degree ≤ (veluH S).degree := by
      rcases eq_or_ne c 0 with h | h
      · simp [h]
      · rw [Polynomial.degree_mul, Polynomial.degree_C h, zero_add]
    have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
    calc (Polynomial.C c * veluH S).degree ≤ (veluH S).degree := hle
      _ = ((S.card - 1 : ℕ) : WithBot ℕ) := veluH_degree_eq_card hS
      _ < ((S.card : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : S.card - 1 < S.card)
  have hDmonic : D.Monic := by
    rw [hD, sub_eq_add_neg]
    exact (veluXNum_monic hS hodd).add_of_left (by rwa [Polynomial.degree_neg])
  have hDdeg : D.degree = ((S.card : ℕ) : WithBot ℕ) := by
    rw [hD, sub_eq_add_neg,
      Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_neg]),
      veluXNum_degree hS hodd]
  have hDeval : ∀ P : W.Point, P ∉ S →
      D.eval (veluPointX P) = (veluH S).eval (veluPointX P) * (W.veluCoordX S P - c) := by
    intro P hP
    rw [hD, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      veluXNum_eval hS hodd hP]
    ring
  -- The two `2`-torsion `x`-coordinates are roots.
  have hroot₁ : D.IsRoot (veluPointX T₁) := by
    rw [Polynomial.IsRoot, hDeval T₁ hT₁, ← hc, sub_self, mul_zero]
  have hroot₂ : D.IsRoot (veluPointX T₂) := by
    rw [Polynomial.IsRoot, hDeval T₂ hT₂, ← hEq, sub_self, mul_zero]
  -- The translates `x(T₁ + Q)`, `Q ≠ 0`, are DOUBLE roots.
  have hdouble : ∀ Q ∈ S.erase 0,
      (Polynomial.X - Polynomial.C (veluPointX (T₁ + Q))) ^ 2 ∣ D := by
    intro Q hQ
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
    have hTQ : T₁ + Q ∉ S := velu_add_notMem hS hT₁ hQS
    have hH := veluH_eval_ne_zero hS hTQ
    have hA : (veluXNum S).eval (veluPointX (T₁ + Q))
        = (veluH S).eval (veluPointX (T₁ + Q)) * c := by
      rw [veluXNum_eval hS hodd hTQ, veluCoordX_add_mem hS T₁ hQS]
    refine velu_sq_dvd_of_isRoot ?_ ?_
    · rw [Polynomial.IsRoot, hDeval _ hTQ, veluCoordX_add_mem hS T₁ hQS, sub_self, mul_zero]
    · have hXi : (veluXi S).eval (veluPointX (T₁ + Q)) = 0 := by
        rw [veluXi_eval hS hodd hTQ, velu_poleV_sum_eq_one hS hodd hT₁ hn₁ hQ, sub_self,
          mul_zero]
      have hdl := congrArg (Polynomial.eval (veluPointX (T₁ + Q))) (velu_dlog_XNum hS hodd)
      simp only [Polynomial.eval_sub, Polynomial.eval_mul] at hdl
      rw [hXi, hA] at hdl
      rw [Polynomial.IsRoot, hD, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C]
      have hfac : (veluH S).eval (veluPointX (T₁ + Q)) *
          ((Polynomial.derivative (veluXNum S)).eval (veluPointX (T₁ + Q))
            - c * (Polynomial.derivative (veluH S)).eval (veluPointX (T₁ + Q))) = 0 := by
        linear_combination hdl
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hH
      · linear_combination h
  -- All the roots exhibited are pairwise distinct.
  have hx12 : veluPointX T₁ ≠ veluPointX T₂ := by
    intro h
    rcases velu_pointX_eq_iff hT₁0 hT₂0 h with h' | h'
    · exact hne h'
    · exact hne (by rw [h', hn₂])
  have hx1Q : ∀ Q ∈ S.erase 0, veluPointX T₁ ≠ veluPointX (T₁ + Q) := by
    intro Q hQ h
    have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
    have hTQ0 : T₁ + Q ≠ 0 := fun hz =>
      (velu_add_notMem hS hT₁ hQS) (hz ▸ hS.zero_mem)
    rcases velu_pointX_eq_iff hT₁0 hTQ0 h with h' | h'
    · exact hQ0 (add_left_cancel (a := T₁) (by rw [add_zero]; exact h'.symm))
    · rw [hnegT₁ Q] at h'
      exact hQ0 (neg_eq_zero.mp
        (add_left_cancel (a := T₁) (by rw [add_zero]; exact h'.symm)))
  have hx2Q : ∀ Q ∈ S.erase 0, veluPointX T₂ ≠ veluPointX (T₁ + Q) := by
    intro Q hQ h
    have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
    have hTQ0 : T₁ + Q ≠ 0 := fun hz =>
      (velu_add_notMem hS hT₁ hQS) (hz ▸ hS.zero_mem)
    have hmem : T₁ + T₂ ∈ S := by
      rcases velu_pointX_eq_iff hT₂0 hTQ0 h with h' | h'
      · have : T₁ + T₂ = Q := by rw [h', ← add_assoc, hsum0, zero_add]
        rw [this]; exact hQS
      · rw [hnegT₁ Q] at h'
        have : T₁ + T₂ = -Q := by rw [h', ← add_assoc, hsum0, zero_add]
        rw [this]; exact hS.neg_mem _ hQS
    have h2t : -(T₁ + T₂) = T₁ + T₂ := by
      rw [show -(T₁ + T₂) = -T₁ + -T₂ from by abel, hn₁, hn₂]
    have h0 : T₁ + T₂ ≠ 0 := by
      intro hz
      exact hne (by rw [← hn₂]; exact add_eq_zero_iff_eq_neg.mp hz)
    exact velu_twoTorsion_notMem hS hodd h0 h2t hmem
  -- The fibres of `Q ↦ x(T₁ + Q)` on `S ∖ {0}` are the `±`-pairs.
  have hfib : ∀ Q ∈ S.erase 0,
      {Q' ∈ S.erase 0 | veluPointX (T₁ + Q') = veluPointX (T₁ + Q)} = {Q, -Q} := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
    have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
    have hTQ0 : T₁ + Q ≠ 0 := fun hz => (velu_add_notMem hS hT₁ hQS) (hz ▸ hS.zero_mem)
    ext Q'
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hQ'0, hQ'S⟩, hx⟩
      have hTQ'0 : T₁ + Q' ≠ 0 := fun hz => (velu_add_notMem hS hT₁ hQ'S) (hz ▸ hS.zero_mem)
      rcases velu_pointX_eq_iff hTQ'0 hTQ0 hx with h' | h'
      · exact Or.inl (add_left_cancel h')
      · rw [hnegT₁ Q] at h'
        exact Or.inr (add_left_cancel h')
    · rintro (rfl | rfl)
      · exact ⟨⟨hQ0, hQS⟩, rfl⟩
      · exact ⟨⟨hnQ0, hS.neg_mem _ hQS⟩, by rw [← hnegT₁ Q]; exact velu_pointX_neg _⟩
  have hfibcard : ∀ Q ∈ S.erase 0,
      ({Q' ∈ S.erase 0 | veluPointX (T₁ + Q') = veluPointX (T₁ + Q)}).card = 2 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
    have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
    have hne' : -Q ≠ Q := fun h => velu_twoTorsion_notMem hS hodd hQ0 h hQS
    rw [hfib Q hQ, Finset.card_insert_of_notMem (by simpa using fun h => hne' h.symm),
      Finset.card_singleton]
  -- Assemble a divisor of `D` of degree `|S| + 1`.
  have hcopl : ∀ a b : F, a ≠ b → IsCoprime (Polynomial.X - Polynomial.C a : Polynomial F)
      (Polynomial.X - Polynomial.C b) := by
    intro a b hab
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hkey : (Polynomial.C ((b - a)⁻¹) : Polynomial F) * Polynomial.C (b - a) = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hba, Polynomial.C_1]
    refine ⟨Polynomial.C ((b - a)⁻¹), -Polynomial.C ((b - a)⁻¹), ?_⟩
    rw [Polynomial.C_sub] at hkey
    linear_combination hkey
  set img := (S.erase 0).image (fun Q => veluPointX (T₁ + Q)) with himg
  set M : Polynomial F := ∏ a ∈ img, (Polynomial.X - Polynomial.C a) ^ 2 with hM
  have hMmonic : M.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => (Polynomial.monic_X_sub_C a).pow 2
  have hMdvd : M ∣ D := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a ha b hb hab
      exact ((hcopl a b hab).pow)
    · intro a ha
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
      exact hdouble Q hQ
  have himgcard : (S.erase 0).card = 2 * img.card := by
    rw [Finset.card_eq_sum_card_image (fun Q => veluPointX (T₁ + Q)) (S.erase 0)]
    have hall : ∀ b ∈ img, ({Q' ∈ S.erase 0 | veluPointX (T₁ + Q') = b}).card = 2 := by
      intro b hb
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hb
      exact hfibcard Q hQ
    rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, mul_comm]
  have hMnat : M.natDegree = 2 * img.card := by
    rw [hM, Polynomial.natDegree_prod _ _
      fun a _ => ((Polynomial.monic_X_sub_C a).pow 2).ne_zero]
    simp [Polynomial.natDegree_pow, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcop2M : IsCoprime (Polynomial.X - Polynomial.C (veluPointX T₂) : Polynomial F) M := by
    refine IsCoprime.prod_right fun a ha => ?_
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
    exact (hcopl _ _ (hx2Q Q hQ)).pow_right
  have hcop1 : IsCoprime (Polynomial.X - Polynomial.C (veluPointX T₁) : Polynomial F)
      ((Polynomial.X - Polynomial.C (veluPointX T₂)) * M) := by
    refine IsCoprime.mul_right (hcopl _ _ hx12) (IsCoprime.prod_right fun a ha => ?_)
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
    exact (hcopl _ _ (hx1Q Q hQ)).pow_right
  have hZdvd : (Polynomial.X - Polynomial.C (veluPointX T₁)) *
      ((Polynomial.X - Polynomial.C (veluPointX T₂)) * M) ∣ D :=
    hcop1.mul_dvd (Polynomial.dvd_iff_isRoot.mpr hroot₁)
      (hcop2M.mul_dvd (Polynomial.dvd_iff_isRoot.mpr hroot₂) hMdvd)
  have hZmonic : ((Polynomial.X - Polynomial.C (veluPointX T₁)) *
      ((Polynomial.X - Polynomial.C (veluPointX T₂)) * M) : Polynomial F).Monic :=
    (Polynomial.monic_X_sub_C _).mul ((Polynomial.monic_X_sub_C _).mul hMmonic)
  have hZnat : ((Polynomial.X - Polynomial.C (veluPointX T₁)) *
      ((Polynomial.X - Polynomial.C (veluPointX T₂)) * M) : Polynomial F).natDegree
      = S.card + 1 := by
    have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
    have herase : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem hS.zero_mem
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C _).ne_zero
        ((Polynomial.monic_X_sub_C _).mul hMmonic).ne_zero,
      Polynomial.natDegree_mul (Polynomial.monic_X_sub_C _).ne_zero hMmonic.ne_zero,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C, hMnat, ← himgcard, herase]
    omega
  have hfinal := Polynomial.degree_le_of_dvd hZdvd hDmonic.ne_zero
  rw [Polynomial.degree_eq_natDegree hZmonic.ne_zero, hZnat, hDdeg] at hfinal
  have : S.card + 1 ≤ S.card := by exact_mod_cast hfinal
  omega

/-- **PROVEN 2026-07-26 over the single leaf `velu_coordX_twoTorsion_ne`: the Vélu quotient
acquires three affine `2`-torsion points over the algebraic closure.**

The base field `F` is arbitrary, so the three `x`-coordinates cannot be asked for in `F`
itself (a quotient curve over `ℚ` typically has a single rational `2`-torsion point); the
statement is therefore made over `AlgebraicClosure F`, which is also the only field the
consumer `exists_velu_quotient_isogeny` ever uses.

Proof (none of it uses `veluMap`, whose definition consumes `velu_isElliptic`):

1. Base change: `veluCurve` commutes with `F → L` (`velu_baseChange_curve`), so the
   base-changed quotient is the Vélu quotient of `W⁄L` by the image `S'` of `S`, which is
   again a subgroup (`velu_baseChange_isPointSubgroup`) of the same odd order
   (`Affine.Point.map_injective`).
2. Over `L = AlgebraicClosure F` the curve `W⁄L` is elliptic, so it has three nonzero points
   `T` with `T = −T` and pairwise distinct `x` (`exists_three_twoTorsion_of_Δ_ne_zero`). Each
   lies OUTSIDE `S'` by `velu_twoTorsion_notMem` — this is where the ODD ORDER is consumed.
3. Their Vélu coordinates satisfy the quotient equation by `velu_equation`, and are
   `2`-torsion by `veluCoordY_neg` (`Y(T) = Y(−T) = negY (X T) (Y T)`).
4. Pairwise distinctness of the three `X(Tᵢ)` is the leaf `velu_coordX_twoTorsion_ne`. -/
theorem velu_exists_three_twoTorsion (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃ : AlgebraicClosure F,
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₁ y₁ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₂ y₂ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₃ y₃ ∧
      y₁ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₁ y₁ ∧
      y₂ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₂ y₂ ∧
      y₃ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₃ y₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  classical
  haveI : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  rw [velu_baseChange_curve (L := AlgebraicClosure F) S]
  set S' : Finset (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    S.image (veluBaseChangePoint W (AlgebraicClosure F)) with hS'def
  have hS' : IsPointSubgroup S' := velu_baseChange_isPointSubgroup hS
  have hodd' : Odd S'.card := by
    rw [hS'def, Finset.card_image_of_injective _ veluBaseChangePoint_injective]
    exact hodd
  obtain ⟨u₁, u₂, u₃, v₁, v₂, v₃, hq₁, hq₂, hq₃, hn₁, hn₂, hn₃, hu₁₂, hu₁₃, hu₂₃⟩ :=
    exists_three_twoTorsion_of_Δ_ne_zero (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F))
      (WeierstrassCurve.isUnit_Δ
        (W := (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)))).ne_zero
  have hns₁ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Nonsingular u₁ v₁ :=
    Affine.equation_iff_nonsingular.mp hq₁
  have hns₂ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Nonsingular u₂ v₂ :=
    Affine.equation_iff_nonsingular.mp hq₂
  have hns₃ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Nonsingular u₃ v₃ :=
    Affine.equation_iff_nonsingular.mp hq₃
  set T₁ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    Affine.Point.some u₁ v₁ hns₁ with hT₁def
  set T₂ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    Affine.Point.some u₂ v₂ hns₂ with hT₂def
  set T₃ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    Affine.Point.some u₃ v₃ hns₃ with hT₃def
  have hneg₁ : -T₁ = T₁ := by
    rw [hT₁def, Affine.Point.neg_some]; exact velu_point_some_eq rfl hn₁.symm
  have hneg₂ : -T₂ = T₂ := by
    rw [hT₂def, Affine.Point.neg_some]; exact velu_point_some_eq rfl hn₂.symm
  have hneg₃ : -T₃ = T₃ := by
    rw [hT₃def, Affine.Point.neg_some]; exact velu_point_some_eq rfl hn₃.symm
  have hmem₁ : T₁ ∉ S' :=
    velu_twoTorsion_notMem hS' hodd' (Affine.Point.some_ne_zero hns₁) hneg₁
  have hmem₂ : T₂ ∉ S' :=
    velu_twoTorsion_notMem hS' hodd' (Affine.Point.some_ne_zero hns₂) hneg₂
  have hmem₃ : T₃ ∉ S' :=
    velu_twoTorsion_notMem hS' hodd' (Affine.Point.some_ne_zero hns₃) hneg₃
  have hTne₁₂ : T₁ ≠ T₂ := by
    rw [hT₁def, hT₂def]; intro hc; exact hu₁₂ (Affine.Point.some.inj hc).1
  have hTne₁₃ : T₁ ≠ T₃ := by
    rw [hT₁def, hT₃def]; intro hc; exact hu₁₃ (Affine.Point.some.inj hc).1
  have hTne₂₃ : T₂ ≠ T₃ := by
    rw [hT₂def, hT₃def]; intro hc; exact hu₂₃ (Affine.Point.some.inj hc).1
  refine ⟨_, _, _, _, _, _,
    velu_equation _ S' hS' hodd' hmem₁, velu_equation _ S' hS' hodd' hmem₂,
    velu_equation _ S' hS' hodd' hmem₃, ?_, ?_, ?_,
    velu_coordX_twoTorsion_ne _ S' hS' hodd' hmem₁ hmem₂ hneg₁ hneg₂ hTne₁₂,
    velu_coordX_twoTorsion_ne _ S' hS' hodd' hmem₁ hmem₃ hneg₁ hneg₃ hTne₁₃,
    velu_coordX_twoTorsion_ne _ S' hS' hodd' hmem₂ hmem₃ hneg₂ hneg₃ hTne₂₃⟩
  · rw [← veluCoordY_neg hS' hmem₁, hneg₁]
  · rw [← veluCoordY_neg hS' hmem₂, hneg₂]
  · rw [← veluCoordY_neg hS' hmem₃, hneg₃]

/-- **Vélu's theorem, part 1: the quotient curve is elliptic** (PROVEN 2026-07-26 as an
assembly over the two leaves `velu_exists_three_twoTorsion` and
`isElliptic_of_three_twoTorsion`).

For a finite subgroup `S` of odd order in `W.Point`, the Vélu model
`y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x + (a₆ − b₂t − 7w)` is nonsingular.

`Δ ≠ 0` is detected after base change to the algebraic closure, since
`Δ (W'⁄L) = algebraMap F L (Δ W')` and `algebraMap` into a field extension is injective. -/
theorem velu_isElliptic (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) : (W.veluCurve S).IsElliptic := by
  obtain ⟨x₁, x₂, x₃, y₁, y₂, y₃, he₁, he₂, he₃, ht₁, ht₂, ht₃, d₁₂, d₁₃, d₂₃⟩ :=
    velu_exists_three_twoTorsion W S hS hodd
  haveI : ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).IsElliptic :=
    isElliptic_of_three_twoTorsion he₁ he₂ he₃ ht₁ ht₂ ht₃ d₁₂ d₁₃ d₂₃
  refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
  have hne := (isUnit_Δ
    (W := ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)))).ne_zero
  rw [show ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Δ =
      algebraMap F (AlgebraicClosure F) (W.veluCurve S).Δ from
    WeierstrassCurve.map_Δ (W := W.veluCurve S) (f := algebraMap F (AlgebraicClosure F)),
    h0, map_zero] at hne
  exact hne rfl

/-- The Vélu image of a point as a point of the quotient curve: the points of the
kernel `S` go to `0`, and every other point goes to its Vélu coordinates.

Nonsingularity of the image is `Affine.equation_iff_nonsingular` applied to the
two leaves `velu_isElliptic` and `velu_equation`. -/
noncomputable def veluMap (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (P : W.Point) : (W.veluCurve S).Point :=
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  if hP : P ∈ S then 0
  else .some _ _ (Affine.equation_iff_nonsingular.mp (W.velu_equation S hS hodd hP))

lemma veluMap_of_mem {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∈ S) :
    W.veluMap S hS hodd P = 0 := by
  rw [veluMap, dif_pos hP]

lemma veluMap_of_notMem {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    W.veluMap S hS hodd P = Affine.Point.some (W.veluCoordX S P) (W.veluCoordY S P)
      (Affine.equation_iff_nonsingular.mp (W.velu_equation S hS hodd hP)) := by
  rw [veluMap, dif_neg hP]

omit [CharZero F] [W.IsElliptic] in
/-- The kernel is closed under negation, restated as a `∉` fact. -/
lemma velu_neg_notMem {S : Finset W.Point} (hS : IsPointSubgroup S) {P : W.Point}
    (hP : P ∉ S) : -P ∉ S := fun hc => hP (by simpa using hS.neg_mem _ hc)

/-- **PROVEN: the Vélu map commutes with negation**, `φ(−P) = −φ(P)`, for EVERY `P` —
both when `P` lies in the kernel (both sides are `0`) and when it does not, where it is
`veluCoordX_neg` and `veluCoordY_neg` read through `Affine.Point.neg_some`. -/
lemma veluMap_neg (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (P : W.Point) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    W.veluMap S hS hodd (-P) = -W.veluMap S hS hodd P := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  by_cases hP : P ∈ S
  · rw [W.veluMap_of_mem hS hodd hP, W.veluMap_of_mem hS hodd (hS.neg_mem _ hP), neg_zero]
  · rw [W.veluMap_of_notMem hS hodd (velu_neg_notMem W hS hP),
      W.veluMap_of_notMem hS hodd hP, Affine.Point.neg_some]
    exact velu_point_some_eq (veluCoordX_neg hS P) (veluCoordY_neg hS hP)

/-- **PROVEN: additivity UP TO SIGN implies additivity.** If for all `A, B` outside the
kernel with `A + B` outside the kernel one knows only the weaker
`φ(A + B) = ±(φ(A) + φ(B))`, then the sign is always `+`.

**Proof, entirely inside the group `(W.veluCurve S).Point`.** Suppose `φ(P + Q) = −Z` with
`Z = φ(P) + φ(Q)`. Instantiate the hypothesis at the pair `(P + Q, −Q)`, whose sum is `P`
and both of whose entries are outside the kernel (`velu_neg_notMem`); using
`veluMap_neg` the two alternatives read `P ↦ −Z − φ(Q)` and `P ↦ Z + φ(Q)`, i.e.

* `2Z = 0`, or
* `2φ(Q) = 0`.

Symmetrically at `(P + Q, −P)` one gets `2Z = 0` or `2φ(P) = 0`. In the one remaining
combination `2φ(P) = 2φ(Q) = 0`, whence `2Z = 2φ(P) + 2φ(Q) = 0` again. So `2Z = 0` in
every case, i.e. `−Z = Z`, and the assumed identity IS the wanted one.

Note what is NOT needed: no injectivity of `φ` modulo the kernel, no nondegeneracy, and no
hypothesis relating `P` to `Q`. -/
theorem velu_map_add_of_add_eq_neg (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card)
    (hpm : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
      W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q ∨
      W.veluMap S hS hodd (P + Q) = -(W.veluMap S hS hodd P + W.veluMap S hS hodd Q))
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  rcases hpm P Q hP hQ hPQ with h | h
  · exact h
  have hnP : -P ∉ S := velu_neg_notMem W hS hP
  have hnQ : -Q ∉ S := velu_neg_notMem W hS hQ
  have hnegP : W.veluMap S hS hodd (-P) = -W.veluMap S hS hodd P := veluMap_neg W S hS hodd P
  have hnegQ : W.veluMap S hS hodd (-Q) = -W.veluMap S hS hodd Q := veluMap_neg W S hS hodd Q
  have e₁ : P + Q + -Q = P := by abel
  have h₁ := hpm (P + Q) (-Q) hPQ hnQ (by rw [e₁]; exact hP)
  rw [e₁, h, hnegQ] at h₁
  have e₂ : P + Q + -P = Q := by abel
  have h₂ := hpm (P + Q) (-P) hPQ hnP (by rw [e₂]; exact hQ)
  rw [e₂, h, hnegP] at h₂
  have hkey : W.veluMap S hS hodd P + W.veluMap S hS hodd Q
      + (W.veluMap S hS hodd P + W.veluMap S hS hodd Q) = 0 := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · linear_combination (norm := abel) h₁
    · linear_combination (norm := abel) h₁
    · linear_combination (norm := abel) h₂
    · linear_combination (norm := abel) -h₁ - h₂
  rw [h]
  exact (add_eq_zero_iff_eq_neg.mp hkey).symm

/-- **PROVEN: goal 1 of the leaf's reduction supplies the nondegeneracy `hz` below.**

`φ(P) + φ(Q) = 0` says `φ(P) = −φ(Q) = φ(−Q)` (`veluMap_neg`), and since `P` and `−Q` are
both outside the kernel their images are affine, so their coordinates agree; through
`veluCoordX_neg` and `veluCoordY_neg` that is exactly the pair
`X(P) = X(Q)`, `Y(P) = negY(X(Q), Y(Q))` which goal 1 forbids.

So a consumer holding goal 1 — the injectivity of the Vélu coordinate map modulo the
kernel, in the `by_cases` form produced by `Affine.Point.add_some` — gets `hz` for free,
and the leaf reduces to the `addX` identity alone. -/
lemma velu_map_add_ne_zero (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S)
    (hcoord : ¬(W.veluCoordX S P = W.veluCoordX S Q ∧
      W.veluCoordY S P
        = (W.veluCurve S).negY (W.veluCoordX S Q) (W.veluCoordY S Q))) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    W.veluMap S hS hodd P + W.veluMap S hS hodd Q ≠ 0 := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  intro h
  have h1 : W.veluMap S hS hodd P = W.veluMap S hS hodd (-Q) := by
    rw [veluMap_neg W S hS hodd Q]; exact add_eq_zero_iff_eq_neg.mp h
  rw [W.veluMap_of_notMem hS hodd hP,
    W.veluMap_of_notMem hS hodd (velu_neg_notMem W hS hQ)] at h1
  obtain ⟨hx, hy⟩ := (Affine.Point.some.injEq ..).mp h1
  exact hcoord ⟨by rw [hx, veluCoordX_neg hS Q], by rw [hy, veluCoordY_neg hS hQ]⟩

/-- **PROVEN: the `x`-coordinate identity ALONE implies Vélu additivity.** This is the
lemma that removes goal 3 (`addY`) from the open leaf `velu_map_add_of_notMem`.

`hx` is goal 2 in point form: the Vélu image of `P + Q` has the same `x`-coordinate as the
sum of the images. `hz` is the nondegeneracy `φ(P) + φ(Q) ≠ 0`, which is exactly goal 1 —
`φ(P) = −φ(Q) = φ(−Q)` would force `P + Q` into the kernel — and is therefore supplied by
the injectivity-modulo-the-kernel statement, not proved again here.

Given both, `velu_pointX_eq_iff` upgrades `hx` to `φ(P + Q) = ±(φ(P) + φ(Q))` and
`velu_map_add_of_add_eq_neg` fixes the sign. -/
theorem velu_map_add_of_coordX (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card)
    (hz : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
      W.veluMap S hS hodd P + W.veluMap S hS hodd Q ≠ 0)
    (hx : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
      W.veluCoordX S (P + Q)
        = veluPointX (W.veluMap S hS hodd P + W.veluMap S hS hodd Q))
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  refine velu_map_add_of_add_eq_neg W S hS hodd (fun A B hA hB hAB => ?_) hP hQ hPQ
  have hne : W.veluMap S hS hodd (A + B) ≠ 0 := by
    rw [W.veluMap_of_notMem hS hodd hAB]; exact Affine.Point.some_ne_zero _
  have hxAB : veluPointX (W.veluMap S hS hodd (A + B))
      = veluPointX (W.veluMap S hS hodd A + W.veluMap S hS hodd B) := by
    rw [W.veluMap_of_notMem hS hodd hAB]; exact hx A B hA hB hAB
  exact velu_pointX_eq_iff hne (hz A B hA hB hAB) hxAB

/-- **SORRY LEAF: the generic case of Vélu additivity**, cut 2026-07-26 out of
`velu_map_add`: `P`, `Q` and `P + Q` all lie OUTSIDE the kernel, so all three Vélu images
are affine points and the identity is the genuine addition law on the quotient curve.

Every other case of `velu_map_add` is proven from the reindexing identities above
(`veluCoordX_add_mem` / `veluCoordY_add_mem` for a summand in the kernel,
`veluCoordX_neg` / `veluCoordY_neg` when `P + Q` is in the kernel), so this is the whole
remaining content of Vélu's additivity.

Route. The classical argument is the function-field one: the coordinate functions `X, Y`
generate the subfield of `W`'s function field fixed by translation by `S`, that subfield is
the function field of `veluCurve W S`, and the induced map of curves is a morphism sending
`0` to `0`, hence a group homomorphism (`Affine.FunctionField` exists in mathlib; the rest
does not).

The finite-form alternative, which avoids the function field, is to verify additivity as a
rational-function identity in the coordinates of `P`, `Q` modulo the equations of `W` — that
is how the classical `2`-isogeny is handled in `MazurTorsion.twoIsogenyFun_add_of_ne` — but
for general `S` the identity involves the `|S|` translates and does not reduce to a single
`ring` call.

**The reduction to coordinates, machine-checked on 2026-07-26 and recorded here so that it
need not be rediscovered.** Writing `X = veluCoordX W S`, `Y = veluCoordY W S` and
`V = W.veluCurve S`, the three `veluMap`s unfold by `veluMap_of_notMem` and the case split
`by_cases hxy : X P = X Q ∧ Y P = V.negY (X Q) (Y Q)` leaves EXACTLY three goals:

1. `hxy → False` — **DISCHARGED 2026-07-26**: this is EXACTLY `velu_coord_ne_neg` above,
   which is now PROVEN. It is applied as `hxy` in the skeleton below.
2. `X (P + Q) = V.addX (X P) (X Q) (V.slope (X P) (X Q) (Y P) (Y Q))`.
3. `Y (P + Q) = V.addY (X P) (X Q) (Y P) (V.slope (X P) (X Q) (Y P) (Y Q))`.

(That three-goal reduction is the COORDINATE route, and it is recorded because it is what
the numerics were checked against. The proof below no longer runs it: it goes through
`velu_map_add_of_coordX`, which needs only goals 1 and 2. The coordinate glue —
`Affine.Point.add_some hxy` and `velu_point_some_eq` — is therefore no longer used here.)

**GOAL 3 (`addY`) IS GONE — 2026-07-26, and it took no coordinate work at all.**
`velu_map_add_of_coordX` below shows that the `x`-coordinate identity ALONE implies
additivity: `velu_pointX_eq_iff` upgrades it to `φ(P + Q) = ±(φ(P) + φ(Q))`, and
`velu_map_add_of_add_eq_neg` fixes the sign by pure group algebra inside
`(W.veluCurve S).Point` — no coordinates, no degree count. Its nondegeneracy hypothesis
`hz` is goal 1, supplied by `velu_map_add_ne_zero` out of `velu_coord_ne_neg`.

So the assembly below is now: goal 1 PROVEN, goal 3 PROVEN AWAY, and exactly ONE sorried
`have` — the `addX` identity, in the point form `velu_map_add_of_coordX` consumes. It is
TRUE independently of route (it just says the Vélu image of `P + Q` has the `x`-coordinate
of the secant-line sum of the images), so it is safe to build against.

It stays a sorried `have` rather than a new top-level leaf for the reason the previous owner
gave: a function-field development would supply it along with everything else, and an owner
who later proves this by any route simply replaces the body, leaving no orphaned declaration
behind. Nothing here can be lifted from mathlib or `~/cs/FLT`, neither of which has any
isogeny material at all.

## ROUTE MAP (2026-07-26, second owner): what is missing, and TWO ROUTES THAT DO NOT WORK

Everything below was either derived here or machine-checked in PARI/GP over **295**
`(A, B)` configurations — `y² = x³ + a₄x + a₆` over `𝔽_p` for `11 ≤ p < 40`,
`0 ≤ a₄, a₆ ≤ 3`, kernels of every odd order dividing a generator's order — with **zero**
failures. That sweep re-confirms the leaf itself is faithful, independently of the earlier
one recorded at the end of this section.

**What is missing is the PUSHFORWARD of divisors, not the pullback.** Write `ψ = veluMap`
and `V = veluCurve W S`. The one-line proof of this leaf is: take `h` on `W` with
`div h = [A] + [B] − [A+B] − [0]`; then `div (N_{F(W)/F(V)} h) = ψ_*(div h) =
[ψA] + [ψB] − [ψ(A+B)] − [0]`, which is principal, hence sums to `0` — and that IS the leaf.
So the missing ingredient is the norm map for `F(W) / F(W)^S` together with
`F(W)^S = F(X, Y)`, i.e. the invariant-function statement. Nothing weaker suffices:

**REFUTED ROUTE 1 — mathlib's `toClass` / `ClassGroup` CANNOT close this leaf.** It is the
obvious thing to reach for, because it is how mathlib proves the group law associative:
`WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)`
is Abel–Jacobi and `toClass_injective` is proven (`Affine/Point.lean:713, 758`;
`W.FunctionField` is there too, line 95). What it yields is "the affine zeros of a function
sum to `0` in `W.Point`".

Apply that to the best function available — the pullback along `ψ` of the line through `ψA`
and `ψB`. Its divisor is `Σ_{Q∈S} ([A+Q] + [B+Q] + [D+Q]) − 3 Σ_{Q∈S} [Q]`, where `D` is the
point with `ψD = −(ψA + ψB)`, and `Σ_{Q∈S} Q = 0` because `S` has odd order and pairs under
`±`. Summing gives **exactly `n · (A + B + D) = 0`**, while the leaf is `A + B + D ∈ S`.
Over `F̄` one has `S ⊆ W[n]` of INDEX `n`, so the deduction falls short by precisely a factor
of `n`. This is not an artefact of the choice of function: every relation obtainable this way
is a PULLBACK `ψ*`, which on divisor classes is the dual isogeny and therefore factors
through `[n]`. Do not spend a cycle on `toClass`.

**REFUTED RESTATEMENT — do NOT weaken this leaf to collinearity of the three images.** The
tempting symmetric restatement is: for `A + B + C = 0` with `A, B, C ∉ S`, the three points
`(X T, Y T)` are collinear on `V`, i.e. the `3 × 3` determinant with rows `(X T, Y T, 1)`
vanishes. It looks attractive because the two constants `Σ_{Q∈S} x_Q` and `Σ_{Q∈S} y_Q` in
`veluCoordX`/`veluCoordY` genuinely do drop out of that determinant (they are column
operations against the all-ones column). **It is strictly weaker, and VACUOUS on a real
subcase.** Take `B = −2A + s` with `s ∈ S` and `A, 2A ∉ S`: then `A, B, A + B ∉ S` all hold,
`C = A − s`, hence `ψC = ψA`, two rows COINCIDE and the determinant vanishes for free —
while the actual content there, `ψB = −2ψA`, is untouched. The `x`-coordinate form kept below
has no such hole, which is why it is the right statement.

**THE CRUX, ISOLATED (machine-checked, unproven).** Let `A + B + C = 0` on `W` with
`A, B, C ∉ S`, let `y = ℓx + m` be the line through them, and set
`N(P) := ∏_{Q∈S} (y(P+Q) − ℓ·x(P+Q) − m)` and `κ := H(x_A)·H(x_B)·H(x_C)`, where
`H = veluH S = ∏_{Q ∈ S∖0} (T − x_Q)`. Then

  **(HNORM)  ∃ λ μ c,  c² = κ  and  N(P) = c·(Y P − λ·X P − μ)  for every `P ∉ S`.**

That is "the norm of the line function is again a line function", i.e. the norm map lands in
`F(V)` — the invariant-function statement in its most concrete form. Verified in the sweep
above, `c² = κ` included.

**THE COMPUTABLE HALF IS ALREADY IN REACH HERE, AND IT IS SIGN-BLIND.** The companion

  **(STAR)  N(P)·N(−P) = −κ · (X P − X A)(X P − X B)(X P − X C)   for `P ∉ S`**

needs NO new theory. Both ingredients exist. The second,

  `∏_{Q∈S} (c − x(P+Q)) = (veluXNum S).eval c − (W.veluCoordX S P) · (veluH S).eval c`,

is `velu_xNum_sub_eq_prod` evaluated at `c`, and was COMPILE-CHECKED here on 2026-07-26 in a
scratch module — it is four lines (`congrArg (Polynomial.eval c)`, then `simp only` with
`eval_sub`, `eval_mul`, `eval_C`, `eval_prod`, `eval_X`). The first,
`F(R)·F(−R) = −(x_R − x_A)(x_R − x_B)(x_R − x_C)` with `F(R) = y_R − ℓx_R − m`, is mathlib's
`Affine.addPolynomial_slope` (`Affine/Formula.lean:264`, factoring the substituted cubic as
`−((X − C x₁)(X − C x₂)(X − C (addX …)))`): expanding `F(R)·F(−R)` with `negY` and applying
the Weierstrass equation at `R` gives exactly `(W.addPolynomial x_A y_A ℓ).eval x_R`, and
`addX x_A x_B ℓ = x_{A+B} = x_C`. Assembling the two over `S` (reindexing
`∏_{Q} F(−(P+Q)) = N(−P)` by `Q ↦ −Q`, and using `veluXNum_eval` to turn
`XNum(x_T)` into `H(x_T)·X T`) gives STAR; all the sign powers of `(−1)^n` cancel. Estimated
80–120 lines. STAR was verified in the same PARI sweep.

The reason to record STAR is what it shows: it pins `N` only up to SIGN, and **the missing
sign is exactly the content of this leaf**. The norm of a VERTICAL line is computable from
the fibre polynomial; the norm of a SLANTED line is not.

**How STAR + HNORM would close it, and the two gaps any such decomposition must handle.**
Substituting HNORM into STAR and using `velu_equation` on `V` gives
`c² · q(X P) = κ · ∏_T (X P − X T)`, where `q(ξ) = ξ³ + (a₂ − λ² − a₁λ)ξ² + …` is the cubic
cut out on `V` by `η = λξ + μ`; with `c² = κ` the `ξ²` coefficients give
`X A + X B + X C = λ² + a₁λ − a₂`, which is this leaf.

The remaining gap is ONE degenerate subcase, and it is worth stating precisely because the
generic case needs nothing extra. Dividing by `c² = κ ≠ 0` and using `velu_equation` on `V`,
STAR + HNORM give the POINTWISE identity `q(X P) = ∏_T (X P − X T)` for every `P ∉ S`. Both
`q` and `∏_T (ξ − X T)` are MONIC cubics, so their difference has degree `≤ 2`; and
`P = A, B, C` are themselves admissible, each making both sides vanish. **So as soon as
`X A, X B, X C` are pairwise distinct, a degree-`≤ 2` polynomial with three distinct roots is
zero and the leaf follows with no base change and no extra points.** Only the collision cases
need more: `X A = X B ⟺ A − B ∈ S`, `X A = X C ⟺ 2A + B ∈ S`, `X B = X C ⟺ A + 2B ∈ S`
(in each, `⟹` goes through the fibre structure `X R = X R' ⟹ R ≡ ±R' mod S`, and it is
`A + B ∉ S` that kills the other sign). There a third distinct evaluation
point is needed, which over a small `F` may not exist in `W(F)` — base change to `F̄` is the
fix, legitimate here because `CharZero F` makes `W(F̄)` infinite and `velu_baseChange_curve` /
`veluBaseChangePoint` / `velu_baseChange_isPointSubgroup` are already in this file (a
base-change lemma for `veluCoordX` itself would have to be added). That subcase is real, not
hypothetical, and a decomposition that skipped it would be unfaithful.

**Absence re-checked 2026-07-26.** `grep -ril 'isogeny\|RiemannRoch'` over
`Mathlib/AlgebraicGeometry` and `Mathlib/NumberTheory` returns NOTHING, and the same over
`~/cs/FLT` returns nothing. `Mathlib/AlgebraicGeometry/EllipticCurve/` holds only
`Affine/{AddSubMap,Basic,Formula,Point}`, `DivisionPolynomial`, `Jacobian`, `Projective`,
`IsomOfJ`, `LFunction`, `ModelsWithJ`, `NormalForms`, `Reduction`, `VariableChange`,
`Weierstrass`. So the norm/pushforward has to be built here; the Abel–Jacobi half
(`toClass`, `FunctionField`, `CoordinateRing`) is the part mathlib does supply. -/
theorem velu_map_add_of_notMem (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  -- Goal (1): PROVEN (`velu_coord_ne_neg`), and it is exactly the nondegeneracy `hz`.
  have hz : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluMap S hS hodd A + W.veluMap S hS hodd B ≠ 0 := fun A B hA hB hAB =>
    velu_map_add_ne_zero W S hS hodd hA hB (W.velu_coord_ne_neg S hS hodd hA hB hAB)
  -- Goal (2), the `addX` identity in point form: THE ONE REMAINING LEAF OF THIS FILE.
  have hX : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluCoordX S (A + B)
        = veluPointX (W.veluMap S hS hodd A + W.veluMap S hS hodd B) := by
    sorry
  -- Goal (3) is discharged by `velu_map_add_of_coordX`, not proved here.
  exact velu_map_add_of_coordX W S hS hodd hz hX hP hQ hPQ

/-- **Vélu's theorem, part 3: the map is additive** (PROVEN 2026-07-26 outside the generic
case, which is the leaf `velu_map_add_of_notMem`).

For a finite subgroup `S` of odd order in `W.Point`, the Vélu map is a group
homomorphism `W.Point → (W.veluCurve S).Point`.

The case split is on membership of `P` and `Q` in the kernel `S`:

* both in `S`: both sides are `0`, since `S` is closed under addition;
* exactly one in `S`: the Vélu coordinates are unchanged by translation by a kernel element
  (`veluCoordX_add_mem`, `veluCoordY_add_mem`), and `P + Q ∉ S` because `S` is a subgroup;
* neither in `S` but `P + Q ∈ S`: then `Q = −P + (P + Q)` differs from `−P` by a kernel
  element, so by `veluCoordX_neg` and `veluCoordY_neg` the image of `Q` is the negative of
  the image of `P` and the right-hand side collapses to `0` through
  `Affine.Point.add_of_Y_eq`;
* neither in `S` and `P + Q ∉ S`: the leaf. -/
theorem velu_map_add (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (P Q : W.Point) :
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  by_cases hP : P ∈ S
  · by_cases hQ : Q ∈ S
    · rw [W.veluMap_of_mem hS hodd (hS.add_mem P hP Q hQ), W.veluMap_of_mem hS hodd hP,
        W.veluMap_of_mem hS hodd hQ, add_zero]
    · have hPQ : P + Q ∉ S := fun hc => hQ (by
        simpa using hS.add_mem (-P) (hS.neg_mem P hP) (P + Q) hc)
      rw [W.veluMap_of_mem hS hodd hP, zero_add, W.veluMap_of_notMem hS hodd hPQ,
        W.veluMap_of_notMem hS hodd hQ]
      exact velu_point_some_eq
        (by rw [add_comm, veluCoordX_add_mem hS Q hP])
        (by rw [add_comm, veluCoordY_add_mem hS Q hP])
  · by_cases hQ : Q ∈ S
    · have hPQ : P + Q ∉ S := fun hc => hP (by
        simpa using hS.add_mem (P + Q) hc (-Q) (hS.neg_mem Q hQ))
      rw [W.veluMap_of_mem hS hodd hQ, add_zero, W.veluMap_of_notMem hS hodd hPQ,
        W.veluMap_of_notMem hS hodd hP]
      exact velu_point_some_eq (veluCoordX_add_mem hS P hQ) (veluCoordY_add_mem hS P hQ)
    · by_cases hPQ : P + Q ∈ S
      · have hQeq : Q = -P + (P + Q) := by abel
        rw [W.veluMap_of_mem hS hodd hPQ, W.veluMap_of_notMem hS hodd hP,
          W.veluMap_of_notMem hS hodd hQ]
        have hXQ : W.veluCoordX S Q = W.veluCoordX S P := by
          rw [hQeq, veluCoordX_add_mem hS (-P) hPQ, veluCoordX_neg hS]
        have hYQ : W.veluCoordY S Q
            = (W.veluCurve S).negY (W.veluCoordX S P) (W.veluCoordY S P) := by
          rw [hQeq, veluCoordY_add_mem hS (-P) hPQ, veluCoordY_neg hS hP]
        exact (Affine.Point.add_of_Y_eq hXQ.symm
          (by rw [hYQ, hXQ, Affine.negY_negY])).symm
      · exact velu_map_add_of_notMem W S hS hodd hP hQ hPQ

/-- The kernel of the Vélu map is exactly `S`: this holds BY CONSTRUCTION, since
points outside `S` are sent to affine points. -/
theorem veluMap_eq_zero_iff (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (P : W.Point) : W.veluMap S hS hodd P = 0 ↔ P ∈ S := by
  by_cases hP : P ∈ S
  · exact iff_of_true (W.veluMap_of_mem hS hodd hP) hP
  · refine iff_of_false ?_ hP
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
    rw [W.veluMap_of_notMem hS hodd hP]
    exact Affine.Point.some_ne_zero _

/-! ### Reducing the additivity leaf to its `x`-coordinate half

The open leaf `velu_map_add_of_notMem` reduces, via `Affine.Point.add_some`, to the two
coordinate identities `addX` and `addY` (goals 2 and 3 of the reduction recorded in its
docstring). **The `addY` half is not independent content**: the three lemmas below discharge
it outright, so that whoever attacks the leaf has to prove the `x`-coordinate identity ONLY.

The argument is pure group algebra in `(W.veluCurve S).Point` — no coordinates, no rational
functions, no polynomial degree count — and it is independent of the route by which the
`x`-half is eventually obtained.

**Machine-checked faithfulness (PARI/GP, 2026-07-26).** Over `𝔽_p` for `11 ≤ p < 40`, curves
`y² = x³ + a₄x + a₆` with `0 ≤ a₄, a₆ ≤ 4`, and kernels of every odd prime order dividing a
generator's order: 169 curve/kernel cases and **61878** ordered pairs `(P, Q)` with
`P, Q, P + Q ∉ S`. In every one of them the Vélu image of `P + Q` computed from the sum
definition equals the sum of the images on `veluCurve W S`, with **zero** failures. So both
the leaf and the `addX`/`addY` reduction are faithful as stated. -/

end Velu

/-! ### Galois equivariance and descent over `ℚ` -/

section Descent

-- The instance itself is supplied by the consumer (`Fermat.FLT.EllipticCurve.Torsion`
-- declares `Classical.typeDecidableEq _` for this field); taking it as a hypothesis
-- keeps this module's import cone down to mathlib and makes the instances used here
-- literally the ones used at the call site.
variable [DecidableEq (AlgebraicClosure ℚ)] (E : WeierstrassCurve ℚ)

/-- The Galois action on points is invertible: `σ⁻¹` undoes `σ`. -/
lemma velu_point_map_symm_map
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    Affine.Point.map σ.symm.toAlgHom (Affine.Point.map σ.toAlgHom P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.map_some, Affine.Point.map_some]
    exact velu_point_some_eq (by simp) (by simp)

lemma velu_pointX_map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluPointX (Affine.Point.map σ.toAlgHom P) = σ (veluPointX P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rw [Affine.Point.map_some]; rfl

lemma velu_pointY_map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluPointY (Affine.Point.map σ.toAlgHom P) = σ (veluPointY P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rw [Affine.Point.map_some]; rfl

omit [DecidableEq (AlgebraicClosure ℚ)] in
lemma velu_baseChange_b₂ :
    (E⁄(AlgebraicClosure ℚ)).b₂ = algebraMap ℚ (AlgebraicClosure ℚ) E.b₂ :=
  WeierstrassCurve.map_b₂ (W := E) (f := algebraMap ℚ (AlgebraicClosure ℚ))

omit [DecidableEq (AlgebraicClosure ℚ)] in
lemma velu_baseChange_b₄ :
    (E⁄(AlgebraicClosure ℚ)).b₄ = algebraMap ℚ (AlgebraicClosure ℚ) E.b₄ :=
  WeierstrassCurve.map_b₄ (W := E) (f := algebraMap ℚ (AlgebraicClosure ℚ))

lemma velu_TTerm_map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluTTerm (E⁄(AlgebraicClosure ℚ)) (Affine.Point.map σ.toAlgHom P) =
      σ (veluTTerm (E⁄(AlgebraicClosure ℚ)) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rw [Affine.Point.map_some, veluTTerm_some, veluTTerm_some, velu_baseChange_b₂,
      velu_baseChange_b₄]
    simp only [map_add, map_mul, map_pow, map_ofNat, AlgEquiv.commutes]
    rfl

lemma velu_WTerm_map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluWTerm (E⁄(AlgebraicClosure ℚ)) (Affine.Point.map σ.toAlgHom P) =
      σ (veluWTerm (E⁄(AlgebraicClosure ℚ)) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero σ).symm
  · rw [Affine.Point.map_some, veluWTerm_some, veluWTerm_some, velu_baseChange_b₂,
      velu_baseChange_b₄,
      show (E⁄(AlgebraicClosure ℚ)).a₁ = algebraMap ℚ (AlgebraicClosure ℚ) E.a₁ from rfl,
      show (E⁄(AlgebraicClosure ℚ)).a₃ = algebraMap ℚ (AlgebraicClosure ℚ) E.a₃ from rfl]
    simp only [map_add, map_mul, map_pow, map_ofNat, AlgEquiv.commutes]
    rfl

variable {E}

/-- **Reindexing a sum over a Galois-stable finite set of points** (PROVEN). -/
lemma velu_sum_reindex {S : Finset ((E⁄(AlgebraicClosure ℚ)).Point)}
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : (E⁄(AlgebraicClosure ℚ)).Point → AlgebraicClosure ℚ) :
    ∑ Q ∈ S, g (Affine.Point.map σ.toAlgHom Q) = ∑ Q ∈ S, g Q :=
  Finset.sum_nbij' (fun Q => Affine.Point.map σ.toAlgHom Q)
    (fun Q => Affine.Point.map σ.symm.toAlgHom Q)
    (fun a ha => hstable σ a ha) (fun a ha => hstable σ.symm a ha)
    (fun a _ => velu_point_map_symm_map E σ a)
    (fun a _ => by simpa using velu_point_map_symm_map E σ.symm a)
    (fun _ _ => rfl)

/-- A sum of a Galois-equivariant function over a Galois-stable finite set of
points is Galois-fixed (PROVEN). -/
lemma velu_sum_fixed {S : Finset ((E⁄(AlgebraicClosure ℚ)).Point)}
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : (E⁄(AlgebraicClosure ℚ)).Point → AlgebraicClosure ℚ)
    (hg : ∀ P, g (Affine.Point.map σ.toAlgHom P) = σ (g P)) :
    σ (∑ Q ∈ S, g Q) = ∑ Q ∈ S, g Q := by
  rw [map_sum]
  calc ∑ Q ∈ S, σ (g Q) = ∑ Q ∈ S, g (Affine.Point.map σ.toAlgHom Q) :=
        Finset.sum_congr rfl fun Q _ => (hg Q).symm
    _ = ∑ Q ∈ S, g Q := velu_sum_reindex hstable σ g

/-- **Galois descent of Vélu's coefficient `t`** (PROVEN). -/
theorem velu_t_mem_range (S : Finset ((E⁄(AlgebraicClosure ℚ)).Point))
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S) :
    veluT (E⁄(AlgebraicClosure ℚ)) S ∈
      Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ => ?_
  rw [veluT, map_mul, map_inv₀, map_ofNat,
    velu_sum_fixed hstable σ _ (velu_TTerm_map E σ)]

/-- **Galois descent of Vélu's coefficient `w`** (PROVEN). -/
theorem velu_w_mem_range (S : Finset ((E⁄(AlgebraicClosure ℚ)).Point))
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S) :
    veluW (E⁄(AlgebraicClosure ℚ)) S ∈
      Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ => ?_
  rw [veluW, map_mul, map_inv₀, map_ofNat,
    velu_sum_fixed hstable σ _ (velu_WTerm_map E σ)]

/-- **Galois equivariance of the Vélu `x`-coordinate** (PROVEN). -/
theorem velu_coordX_map {S : Finset ((E⁄(AlgebraicClosure ℚ)).Point)}
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluCoordX (E⁄(AlgebraicClosure ℚ)) S (Affine.Point.map σ.toAlgHom P) =
      σ (veluCoordX (E⁄(AlgebraicClosure ℚ)) S P) := by
  have hmain : ∑ Q ∈ S, veluPointX (Affine.Point.map σ.toAlgHom P + Q) =
      σ (∑ Q ∈ S, veluPointX (P + Q)) := by
    rw [map_sum, ← velu_sum_reindex hstable σ
      (fun Q => veluPointX (Affine.Point.map σ.toAlgHom P + Q))]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [← map_add, velu_pointX_map E σ (P + Q)]
  rw [veluCoordX, veluCoordX, map_sub, hmain,
    velu_sum_fixed hstable σ _ (velu_pointX_map E σ)]

/-- **Galois equivariance of the Vélu `y`-coordinate** (PROVEN). -/
theorem velu_coordY_map {S : Finset ((E⁄(AlgebraicClosure ℚ)).Point)}
    (hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : (E⁄(AlgebraicClosure ℚ)).Point) :
    veluCoordY (E⁄(AlgebraicClosure ℚ)) S (Affine.Point.map σ.toAlgHom P) =
      σ (veluCoordY (E⁄(AlgebraicClosure ℚ)) S P) := by
  have hmain : ∑ Q ∈ S, veluPointY (Affine.Point.map σ.toAlgHom P + Q) =
      σ (∑ Q ∈ S, veluPointY (P + Q)) := by
    rw [map_sum, ← velu_sum_reindex hstable σ
      (fun Q => veluPointY (Affine.Point.map σ.toAlgHom P + Q))]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [← map_add, velu_pointY_map E σ (P + Q)]
  rw [veluCoordY, veluCoordY, map_sub, hmain,
    velu_sum_fixed hstable σ _ (velu_pointY_map E σ)]

omit [DecidableEq (AlgebraicClosure ℚ)] in
/-- `IsElliptic` descends along the base change `ℚ → ℚ̄`: the discriminant of the
base change is the image of the discriminant, and `algebraMap` is injective. -/
lemma isElliptic_of_baseChange (E' : WeierstrassCurve ℚ)
    (h : ((E'⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ))).IsElliptic) :
    E'.IsElliptic := by
  haveI := h
  refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
  have hne := (isUnit_Δ (W := (E'⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)))).ne_zero
  rw [show ((E'⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ))).Δ =
      algebraMap ℚ (AlgebraicClosure ℚ) E'.Δ from
    WeierstrassCurve.map_Δ (W := E') (f := algebraMap ℚ (AlgebraicClosure ℚ)),
    h0, map_zero] at hne
  exact hne rfl

/-- **The quotient isogeny by a finite Galois-stable subgroup of ODD order**
(assembled 2026-07-25 from the three Vélu leaves `velu_isElliptic`,
`velu_equation`, `velu_map_add` together with the Galois descent and
equivariance proven above).

For an elliptic curve `E/ℚ` and a finite Galois-stable subgroup `C` of odd
order in `E(ℚ̄)` there are an elliptic curve `E'/ℚ` — the Vélu model
`y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x + (a₆ − b₂t − 7w)`, whose
coefficients `t` and `w` are rational because they are Galois-fixed sums over
`C` — and a Galois-equivariant group homomorphism `E(ℚ̄) →+ E'(ℚ̄)` with kernel
exactly `C`.

Primality of the order is NOT needed: Vélu's construction works for any finite
subgroup, and oddness is used only to halve the `±`-invariant sums defining `t`
and `w`.

**This is the MODEL-NAMING form** (strengthened 2026-07-26 for
`WeierstrassCurve.exists_tateInvariants_of_stableThreeSubgroup`): the quotient
curve is not merely *some* `E'`, it is literally `E.veluModel t w`, and the two
rational coefficients `t`, `w` are pinned by `algebraMap ℚ ℚ̄ t = veluT …`,
`algebraMap ℚ ℚ̄ w = veluW …` over `hCfin.toFinset`. A consumer that knows the
kernel explicitly can therefore evaluate Vélu's sums and obtain the quotient's
`c₄` and `Δ` by `ring`. The unnamed form is `exists_velu_quotient_isogeny`
below.

**The parity-free version already exists and is assembled**: see
`exists_velu_quotient_isogeny_model_of_subgroup` in the `VeluAllOrders` /
`DescentAllOrders` sections at the end of this file, which is this statement with
`hCodd` deleted, together with an audit of exactly which parts of this development
already work at even order. Do not re-cut it. -/
theorem exists_velu_quotient_isogeny_model (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCodd : Odd (Nat.card C))
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (t w : ℚ) (_ : (E.veluModel t w).IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+
        ((E.veluModel t w)⁄(AlgebraicClosure ℚ)).Point),
      algebraMap ℚ (AlgebraicClosure ℚ) t =
          veluT (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset ∧
      algebraMap ℚ (AlgebraicClosure ℚ) w =
          veluW (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset ∧
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  classical
  haveI : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ))).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  -- the kernel as a `Finset`
  set S : Finset ((E⁄(AlgebraicClosure ℚ)).Point) := hCfin.toFinset with hSdef
  have hmem : ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, P ∈ S ↔ P ∈ C := fun P => by
    rw [hSdef]; exact hCfin.mem_toFinset
  have hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S := fun σ Q hQ =>
    (hmem _).mpr (hCstable σ Q ((hmem Q).mp hQ))
  have hS : IsPointSubgroup S :=
    { zero_mem := (hmem _).mpr (zero_mem C)
      add_mem := fun P hP Q hQ =>
        (hmem _).mpr (add_mem ((hmem P).mp hP) ((hmem Q).mp hQ))
      neg_mem := fun P hP => (hmem _).mpr (neg_mem ((hmem P).mp hP)) }
  have hcard : S.card = Nat.card C := by
    rw [hSdef, ← Set.ncard_eq_toFinset_card _ hCfin, ← Nat.card_coe_set_eq]
    rfl
  have hodd : Odd S.card := hcard ▸ hCodd
  -- Vélu's coefficients descend to `ℚ`
  obtain ⟨t, ht⟩ := velu_t_mem_range S hstable
  obtain ⟨w, hw⟩ := velu_w_mem_range S hstable
  -- the quotient curve over `ℚ`, and the identification of its base change
  have hEq : ((E.veluModel t w)⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)) =
      (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S := by
    refine WeierstrassCurve.ext rfl rfl rfl ?_ ?_
    · show algebraMap ℚ (AlgebraicClosure ℚ) (E.a₄ - 5 * t) =
        (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).a₄ -
          5 * veluT (E⁄(AlgebraicClosure ℚ)) S
      rw [map_sub, map_mul, map_ofNat, ht]
      rfl
    · show algebraMap ℚ (AlgebraicClosure ℚ) (E.a₆ - E.b₂ * t - 7 * w) =
        (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).a₆ -
          (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).b₂ *
            veluT (E⁄(AlgebraicClosure ℚ)) S -
          7 * veluW (E⁄(AlgebraicClosure ℚ)) S
      rw [map_sub, map_sub, map_mul, map_mul, map_ofNat, ht, hw, velu_baseChange_b₂]
      rfl
  haveI hVE : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S).IsElliptic :=
    velu_isElliptic _ S hS hodd
  haveI hE'K : ((E.veluModel t w)⁄(AlgebraicClosure ℚ) :
      Affine (AlgebraicClosure ℚ)).IsElliptic := hEq ▸ hVE
  -- transport the Vélu map along the identification
  set ψ : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S).Point ≃+
      ((E.veluModel t w)⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).Point :=
    pointAddEquivOfEq hEq.symm with hψdef
  refine ⟨t, w, isElliptic_of_baseChange _ hE'K,
    AddMonoidHom.mk' (fun P => ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd P))
      (fun P Q => by
        rw [velu_map_add _ S hS hodd P Q, map_add]), ht, hw, ?_, ?_⟩
  · -- Galois equivariance
    intro σ Pt
    show ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd
        (Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt)) =
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
        (ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd Pt))
    by_cases hPt : Pt ∈ S
    · rw [veluMap_of_mem _ hS hodd hPt,
        veluMap_of_mem _ hS hodd (hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt hPt),
        map_zero, map_zero]
    · have hPtσ : Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt ∉ S := by
        intro hc
        exact hPt (by
          simpa [velu_point_map_symm_map] using
            hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).symm _ hc)
      rw [veluMap_of_notMem _ hS hodd hPt, veluMap_of_notMem _ hS hodd hPtσ, hψdef,
        pointAddEquivOfEq_some, pointAddEquivOfEq_some, Affine.Point.map_some]
      exact velu_point_some_eq
        (velu_coordX_map hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt)
        (velu_coordY_map hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt)
  · -- the kernel
    intro Pt
    show ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd Pt) = 0 ↔ Pt ∈ C
    rw [← hmem, ← veluMap_eq_zero_iff (E⁄(AlgebraicClosure ℚ)) S hS hodd Pt]
    constructor
    · intro h
      exact ψ.injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]

/-- **The quotient isogeny by a finite Galois-stable subgroup of ODD order**,
in the form that forgets the model: for an elliptic curve `E/ℚ` and a finite
Galois-stable subgroup `C` of odd order in `E(ℚ̄)` there are an elliptic curve
`E'/ℚ` and a Galois-equivariant group homomorphism `E(ℚ̄) →+ E'(ℚ̄)` with kernel
exactly `C`.

This is `exists_velu_quotient_isogeny_model` with the identification
`E' = E.veluModel t w` and the two Vélu-sum equations discarded; consumers that
need to compute the quotient's invariants must use the model form. -/
theorem exists_velu_quotient_isogeny (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCodd : Odd (Nat.card C))
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  obtain ⟨t, w, hell, φ, -, -, hgal, hker⟩ :=
    exists_velu_quotient_isogeny_model E C hCfin hCodd hCstable
  exact ⟨E.veluModel t w, hell, φ, hgal, hker⟩

end Descent

/-! ## Vélu for a kernel of ARBITRARY order: dropping `Odd`

Everything above carries the hypothesis `Odd S.card`. Vélu's construction does NOT
need it — the classical formulas treat the `2`-torsion of the kernel as its own
`±`-orbit — and the theorems below are the parity-free forms, cut 2026-07-26 out of
the request to give `exists_velu_quotient_isogeny_model` an even-kernel case (the
named blocker for the `2`-isogeny chain of `exists_x0ThirtyTwo_point`).

### AUDIT: what is ALREADY parity-free, and what is not

The task was dispatched on the belief that the even case is bookkeeping over the
`±`-orbit decomposition — that the sums `t = Σ t_T`, `w = Σ w_T` need their
`2`-torsion terms handled separately, `t_T = g^x_T` instead of `2 g^x_T`. **That
half is already done**, by the design decision recorded at the top of this file:
`veluT` and `veluW` are HALF the sum over ALL of the kernel, not a sum over
representatives. The `2`-torsion terms come out right automatically. In detail,
writing `g^x_Q = 3x_Q² + 2a₂x_Q + a₄ − a₁y_Q` and `g^y_Q = −(2y_Q + a₁x_Q + a₃)`:

* `veluTTerm Q = 6x_Q² + b₂x_Q + b₄ = 2 g^x_Q − a₁ g^y_Q` for EVERY `Q`, and
  `veluUTerm Q = (g^y_Q)²`, `veluWTerm Q = veluUTerm Q + x_Q · veluTTerm Q`;
* a `2`-torsion `T` is exactly the condition `2y_T + a₁x_T + a₃ = 0`, i.e.
  `g^y_T = 0`, hence `veluTTerm T = 2 g^x_T` and `veluUTerm T = 0`;
* so half the `T`-term of `veluT` is `g^x_T`, which is Vélu's `t_T`, and half the
  `T`-term of `veluW` is `x_T g^x_T = veluUTerm T + t_T x_T`, which is Vélu's `w_T`;
* while a genuine `±`-pair contributes its term twice, and halving recovers it once.

So `veluT`, `veluW`, `veluModel` and `veluCurve` are already the correct Vélu data
at EVERY order. The same is true one layer up: `veluCoordX`, `veluCoordY`,
`velu_coordX_eq`, `velu_coordY_eq`, `velu_sum_pair` and `velu_pair_X` / `velu_pair_Y`
carry no parity hypothesis and are already stated without one. At a `2`-torsion `T`
the paired identity degenerates to `2(x(P + T) − x_T) = t_T/(x_P − x_T)`, whose right
side has lost its double pole precisely because `veluUTerm T = 0`. (Checked
numerically on `y² = x³ − x` at `T = (0,0)` and on `[1,2,3,4,5]` at its real
`2`-torsion point; PARI/GP as an untrusted searcher, statement check only.)

### Where the parity hypothesis is GENUINELY load-bearing

The obstruction is one layer lower, in the POLYNOMIAL machinery, and it is not
bookkeeping over the coefficient sums:

* `veluH S = ∏_{Q ∈ S ∖ 0} (T − x_Q)` is still the right common denominator at every
  order — a `±`-pair contributes its linear factor twice and a `2`-torsion point
  contributes it once, matching the double and simple poles respectively.
* `veluH_factor` is the FALSE statement in the even case: it asserts
  `(T − x_Q)² ∣ veluH S` for every nonzero `Q`, which fails at a `2`-torsion `T`,
  where the factor is simple. This is the ONE place `hodd` is consumed in the
  `PolePoly` section, and it is what every later degree count is built on. Its
  parity-free form is uniform, with the exponent depending on the orbit:
  `veluH S = (X − C x_Q) ^ (if -Q = Q then 1 else 2) * veluHq S Q`, which is correct
  because `veluHq` erases `Q` and then `-Q`, and at a `2`-torsion point that second
  erase is idempotent.
* `veluPX` and `veluPV` are the definitions that must actually CHANGE. Both give the
  summand at `Q` the numerator `t_Q(X − x_Q) + u_Q` over `veluHq S Q`, which encodes a
  double pole; at a `2`-torsion `T` this yields `t_T` rather than `t_T/(X − x_T)`. The
  uniform repair is to multiply the `t_Q` part by `(X − C x_Q) ^ (if -Q = Q then 0
  else 1)`; the `u_Q` part needs no correction because `veluUTerm T = 0`.
* Downstream of those, `velu_theta_degree_lt`, `velu_theta_eq_zero`,
  `velu_pole_identity`, `velu_wronskian` and `velu_xNum_sub_eq_prod` all re-derive
  with the changed degree count, and `velu_exists_three_twoTorsion` needs a different
  argument outright: with a `2`-torsion `T` in the kernel, the two other `2`-torsion
  points of `W` have the SAME image (their difference is `T`), so the quotient
  receives only one nonzero `2`-torsion point from `W[2]` and the remaining two must
  come from points of order `4`.

That is a re-derivation of the `PolePoly` and `Velu` sections, not an edit to them,
which is why the parity-free statements below are left as three named leaves rather
than being generalized in place: generalizing in place would rewrite the signature of
some sixty declarations in this file and collide with the open odd-kernel leaf
`velu_map_add_of_notMem`. The odd-order path above is deliberately untouched.

**Faithfulness.** All three leaves are TRUE as stated; the audit above is what
establishes that the parity-free `veluCurve S` really is the quotient curve, so
nothing here is a statement weakened to make it provable.
-/

section VeluAllOrders

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

/-- **LEAF: the Vélu quotient curve is elliptic, at EVERY kernel order.**

The parity-free form of `velu_isElliptic`. The odd-order proof goes through
`velu_exists_three_twoTorsion`, which reads three distinct `2`-torsion points of the
quotient off the three `2`-torsion points of `W` over the algebraic closure; that
argument does not survive an even kernel, because a `2`-torsion point `T` inside the
kernel identifies the other two. Expect either a route through points of order `4`,
or a direct computation of `Δ (veluCurve W S)`. -/
theorem velu_isElliptic_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S) :
    (W.veluCurve S).IsElliptic := sorry

/-- **LEAF: Vélu's coordinates satisfy the quotient equation, at EVERY kernel order.**

The parity-free form of `velu_equation`. By `velu_coordX_eq` and `velu_coordY_eq` —
both already parity-free — this reduces exactly as in the odd case to the
rational-function identity `velu_equation_pole`, hence to `veluTheta S = 0`; that is
the statement needing the `veluPX` / `veluPV` repair described in the section note
above. -/
theorem velu_equation_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (W.veluCurve S).Equation (W.veluCoordX S P) (W.veluCoordY S P) := sorry

/-- The Vélu image of a point as a point of the quotient curve, for a kernel of
ARBITRARY order: the parity-free counterpart of `veluMap`. -/
noncomputable def veluMapAll (S : Finset W.Point) (hS : IsPointSubgroup S)
    (P : W.Point) : (W.veluCurve S).Point :=
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  if hP : P ∈ S then 0
  else .some _ _ (Affine.equation_iff_nonsingular.mp (W.velu_equation_of_subgroup S hS hP))

lemma veluMapAll_of_mem {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∈ S) : W.veluMapAll S hS P = 0 := by
  rw [veluMapAll, dif_pos hP]

lemma veluMapAll_of_notMem {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS P = Affine.Point.some (W.veluCoordX S P) (W.veluCoordY S P)
      (Affine.equation_iff_nonsingular.mp (W.velu_equation_of_subgroup S hS hP)) := by
  rw [veluMapAll, dif_neg hP]

/-- **LEAF: the Vélu map is additive, at EVERY kernel order.**

The parity-free form of `velu_map_add`. The reduction above it is formal and
parity-free once its inputs are — `veluMapAll_neg`, additivity up to sign, and the
kernel cases — so the real content is the parity-free forms of `velu_coord_ne_neg`
(which routes through `velu_xNum_sub_eq_prod`, hence through `veluH_factor`) and of
the `addX` identity still open at `velu_map_add_of_notMem`. Whoever closes this
should expect to close that odd-order leaf on the way, and should coordinate with
its owner. -/
theorem velu_map_add_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    (P Q : W.Point) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q := sorry

/-- The kernel of the arbitrary-order Vélu map is exactly `S` (PROVEN): this holds BY
CONSTRUCTION, since points outside `S` are sent to affine points. -/
theorem veluMapAll_eq_zero_iff (S : Finset W.Point) (hS : IsPointSubgroup S)
    (P : W.Point) : W.veluMapAll S hS P = 0 ↔ P ∈ S := by
  by_cases hP : P ∈ S
  · exact iff_of_true (W.veluMapAll_of_mem hS hP) hP
  · refine iff_of_false ?_ hP
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    rw [W.veluMapAll_of_notMem hS hP]
    exact Affine.Point.some_ne_zero _

end VeluAllOrders

section DescentAllOrders

variable [DecidableEq (AlgebraicClosure ℚ)]

/-- **The quotient isogeny by a finite Galois-stable subgroup of ARBITRARY order**
(PROVEN 2026-07-26 as an assembly over the three parity-free leaves
`velu_isElliptic_of_subgroup`, `velu_equation_of_subgroup` and
`velu_map_add_of_subgroup`, together with the Galois descent and equivariance already
proven for the odd case, which are themselves parity-free).

This is `exists_velu_quotient_isogeny_model` with the hypothesis `Odd (Nat.card C)`
REMOVED. The Galois-descent half — `velu_t_mem_range`, `velu_w_mem_range`,
`velu_coordX_map`, `velu_coordY_map`, `isElliptic_of_baseChange` — never used the
parity hypothesis, so the assembly is the odd-order one with `hodd` deleted. -/
theorem exists_velu_quotient_isogeny_model_of_subgroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (t w : ℚ) (_ : (E.veluModel t w).IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+
        ((E.veluModel t w)⁄(AlgebraicClosure ℚ)).Point),
      algebraMap ℚ (AlgebraicClosure ℚ) t =
          veluT (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset ∧
      algebraMap ℚ (AlgebraicClosure ℚ) w =
          veluW (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset ∧
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  classical
  haveI : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ))).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic
  set S : Finset ((E⁄(AlgebraicClosure ℚ)).Point) := hCfin.toFinset with hSdef
  have hmem : ∀ P : (E⁄(AlgebraicClosure ℚ)).Point, P ∈ S ↔ P ∈ C := fun P => by
    rw [hSdef]; exact hCfin.mem_toFinset
  have hstable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ Q ∈ S,
      Affine.Point.map σ.toAlgHom Q ∈ S := fun σ Q hQ =>
    (hmem _).mpr (hCstable σ Q ((hmem Q).mp hQ))
  have hS : IsPointSubgroup S :=
    { zero_mem := (hmem _).mpr (zero_mem C)
      add_mem := fun P hP Q hQ =>
        (hmem _).mpr (add_mem ((hmem P).mp hP) ((hmem Q).mp hQ))
      neg_mem := fun P hP => (hmem _).mpr (neg_mem ((hmem P).mp hP)) }
  obtain ⟨t, ht⟩ := velu_t_mem_range S hstable
  obtain ⟨w, hw⟩ := velu_w_mem_range S hstable
  have hEq : ((E.veluModel t w)⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)) =
      (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S := by
    refine WeierstrassCurve.ext rfl rfl rfl ?_ ?_
    · show algebraMap ℚ (AlgebraicClosure ℚ) (E.a₄ - 5 * t) =
        (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).a₄ -
          5 * veluT (E⁄(AlgebraicClosure ℚ)) S
      rw [map_sub, map_mul, map_ofNat, ht]
      rfl
    · show algebraMap ℚ (AlgebraicClosure ℚ) (E.a₆ - E.b₂ * t - 7 * w) =
        (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).a₆ -
          (E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).b₂ *
            veluT (E⁄(AlgebraicClosure ℚ)) S -
          7 * veluW (E⁄(AlgebraicClosure ℚ)) S
      rw [map_sub, map_sub, map_mul, map_mul, map_ofNat, ht, hw, velu_baseChange_b₂]
      rfl
  haveI hVE : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S).IsElliptic :=
    velu_isElliptic_of_subgroup _ S hS
  haveI hE'K : ((E.veluModel t w)⁄(AlgebraicClosure ℚ) :
      Affine (AlgebraicClosure ℚ)).IsElliptic := hEq ▸ hVE
  set ψ : ((E⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).veluCurve S).Point ≃+
      ((E.veluModel t w)⁄(AlgebraicClosure ℚ) : Affine (AlgebraicClosure ℚ)).Point :=
    pointAddEquivOfEq hEq.symm with hψdef
  refine ⟨t, w, isElliptic_of_baseChange _ hE'K,
    AddMonoidHom.mk' (fun P => ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS P))
      (fun P Q => by
        rw [velu_map_add_of_subgroup _ S hS P Q, map_add]), ht, hw, ?_, ?_⟩
  · -- Galois equivariance
    intro σ Pt
    show ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS
        (Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt)) =
      Affine.Point.map (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
        (ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS Pt))
    by_cases hPt : Pt ∈ S
    · rw [veluMapAll_of_mem _ hS hPt,
        veluMapAll_of_mem _ hS (hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt hPt),
        map_zero, map_zero]
    · have hPtσ : Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt ∉ S := by
        intro hc
        exact hPt (by
          simpa [velu_point_map_symm_map] using
            hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).symm _ hc)
      rw [veluMapAll_of_notMem _ hS hPt, veluMapAll_of_notMem _ hS hPtσ, hψdef,
        pointAddEquivOfEq_some, pointAddEquivOfEq_some, Affine.Point.map_some]
      exact velu_point_some_eq
        (velu_coordX_map hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt)
        (velu_coordY_map hstable (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) Pt)
  · -- the kernel
    intro Pt
    show ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS Pt) = 0 ↔ Pt ∈ C
    rw [← hmem, ← veluMapAll_eq_zero_iff (E⁄(AlgebraicClosure ℚ)) S hS Pt]
    constructor
    · intro h
      exact ψ.injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]

/-- **The quotient isogeny by a finite Galois-stable subgroup of ARBITRARY order**,
in the form that forgets the model.

This is `exists_velu_quotient_isogeny` with the hypothesis `Odd (Nat.card C)` removed;
it is `exists_velu_quotient_isogeny_model_of_subgroup` with the identification
`E' = E.veluModel t w` and the two Vélu-sum equations discarded. -/
theorem exists_velu_quotient_isogeny_of_subgroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) := by
  obtain ⟨t, w, hell, φ, -, -, hgal, hker⟩ :=
    exists_velu_quotient_isogeny_model_of_subgroup E C hCfin hCstable
  exact ⟨E.veluModel t w, hell, φ, hgal, hker⟩

end DescentAllOrders

end WeierstrassCurve
