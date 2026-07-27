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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

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

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** Base change of the Vélu `x`-coordinate. This is the one member of the
base-change family that was missing, and it is what lets an argument needing MORE POINTS
than `W(F)` supplies be run over `F̄` and descended: see `velu_coordX_add_eq_addX`. Pure
reindexing of the two sums off `veluBaseChangePoint_pointX`. -/
lemma velu_bc_coordX (S : Finset W.Point) (P : W.Point) :
    (W⁄L : Affine L).veluCoordX (S.image (veluBaseChangePoint W L))
        (veluBaseChangePoint W L P)
      = algebraMap F L (W.veluCoordX S P) := by
  rw [veluCoordX, veluCoordX, map_sub, map_sum, map_sum,
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h),
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h)]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun Q _ => ?_)
    (Finset.sum_congr rfl fun Q _ => veluBaseChangePoint_pointX Q)
  rw [← map_add, veluBaseChangePoint_pointX]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** Base change of the Vélu `y`-coordinate, the companion of
`velu_bc_coordX`. -/
lemma velu_bc_coordY (S : Finset W.Point) (P : W.Point) :
    (W⁄L : Affine L).veluCoordY (S.image (veluBaseChangePoint W L))
        (veluBaseChangePoint W L P)
      = algebraMap F L (W.veluCoordY S P) := by
  rw [veluCoordY, veluCoordY, map_sub, map_sum, map_sum,
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h),
    Finset.sum_image (fun a _ b _ h => veluBaseChangePoint_injective h)]
  refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun Q _ => ?_)
    (Finset.sum_congr rfl fun Q _ => veluBaseChangePoint_pointY Q)
  rw [← map_add, veluBaseChangePoint_pointY]

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

/-! ### STAR: the norm of a line function, paired with its own negation

The five lemmas below prove `STAR`, the computable half of the norm identity that the open
leaf `velu_map_add_of_notMem` needs; see the ROUTE MAP in that leaf's docstring for how it
fits. Writing `f` for the line function `y − (ℓ(x − x_A) + y_A)` on `W` and
`N(P) = ∏_{Q ∈ S} f(P + Q)` for its norm along the kernel,

  `N(P) · N(−P) = −κ · (X P − X T₁)(X P − X T₂)(X P − X T₃)`,   `κ = ∏ᵢ H(x(Tᵢ))`,

where `T₁, T₂, T₃` are the three points of `W` cut out by the line. The proof is four moves:
reindex the second product by `Q ↦ −Q` so that the two products pair up termwise; turn each
pair `f(R)·f(−R)` into `addPolynomial.eval (x R)` using the Weierstrass equation at `R`;
factor `addPolynomial` through its three roots; and evaluate each of the three resulting
fibre products with `velu_xNum_sub_eq_prod`, whose value at `x(T)` is `H(x T)·(X P − X T)`
by `veluXNum_eval`. The sign `(−1)^{|S|} = −1` is where `hodd` enters. -/

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
/-- The value of mathlib's `addPolynomial` at a point, in closed form. -/
lemma velu_addPolynomial_eval (x y ℓ ξ : F) :
    (W.addPolynomial x y ℓ).eval ξ
      = (ℓ * (ξ - x) + y) ^ 2 + W.a₁ * ξ * (ℓ * (ξ - x) + y) + W.a₃ * (ℓ * (ξ - x) + y)
        - (ξ ^ 3 + W.a₂ * ξ ^ 2 + W.a₄ * ξ + W.a₆) := by
  rw [Affine.addPolynomial_eq]
  simp only [Cubic.toPoly, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

omit [CharZero F] [W.IsElliptic] in
/-- Reindexing a PRODUCT over the kernel by negation, the multiplicative companion of
`velu_sum_neg`. -/
lemma velu_prod_neg {S : Finset W.Point} (hS : IsPointSubgroup S) (g : W.Point → F) :
    ∏ Q ∈ S, g (-Q) = ∏ Q ∈ S, g Q :=
  Finset.prod_nbij' (fun Q => -Q) (fun Q => -Q)
    (fun a ha => hS.neg_mem a ha) (fun a ha => hS.neg_mem a ha)
    (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun _ _ => rfl)

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
/-- **PROVEN.** The line function at `R` times the line function at `−R` is the value of
`addPolynomial` at `x(R)`: the `y`-linear terms cancel against `negY`, and what is left is
the Weierstrass equation at `R`. This is the pointwise brick under `STAR`. -/
lemma velu_line_pair (x y ℓ : F) {R : W.Point} (hR : R ≠ 0) :
    (veluPointY R - (ℓ * (veluPointX R - x) + y))
      * (veluPointY (-R) - (ℓ * (veluPointX (-R) - x) + y))
      = (W.addPolynomial x y ℓ).eval (veluPointX R) := by
  have heq : W.Equation (veluPointX R) (veluPointY R) := by
    cases R with
    | zero => exact absurd rfl hR
    | some x' y' h => exact h.1
  rw [Affine.equation_iff] at heq
  rw [velu_pointX_neg, velu_pointY_neg R hR, velu_addPolynomial_eval]
  linear_combination -heq

/-- **PROVEN.** The product of `x(P + Q) − c` over the kernel, read off the fibre polynomial
`velu_xNum_sub_eq_prod`. The sign `(−1)^{|S|} = −1` is where `hodd` is used. -/
lemma velu_fibre_prod_sub (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) (c : F) :
    ∏ Q ∈ S, (veluPointX (P + Q) - c)
      = W.veluCoordX S P * (veluH S).eval c - (veluXNum S).eval c := by
  have hkey := congrArg (Polynomial.eval c) (velu_xNum_sub_eq_prod W S hS hodd hP)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_X] at hkey
  have hneg : ∏ Q ∈ S, (veluPointX (P + Q) - c)
      = (-1 : F) ^ S.card * ∏ Q ∈ S, (c - veluPointX (P + Q)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => by ring
  rw [hneg, ← hkey, hodd.neg_one_pow]
  ring

/-- **PROVEN.** The same fibre product at the `x`-coordinate of a point `T` OUTSIDE the
kernel, where `veluXNum_eval` turns `XNum(x T)` into `H(x T)·X T`: the product is
`H(x T)·(X P − X T)`, i.e. it sees only the Vélu coordinates. -/
lemma velu_fibre_prod_sub_point (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P : W.Point} (hP : P ∉ S) {T : W.Point} (hT : T ∉ S) :
    ∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T)
      = (veluH S).eval (veluPointX T) * (W.veluCoordX S P - W.veluCoordX S T) := by
  rw [velu_fibre_prod_sub W S hS hodd hP, veluXNum_eval hS hodd hT]
  ring

/-- **STAR, PROVEN 2026-07-26 (general line).** For ANY line `y = ℓ(x − x₀) + y₀` whose
`addPolynomial` factors through three points `T₁, T₂, T₃` of `W` lying outside the kernel,
the norm `N(P) = ∏_{Q ∈ S} f(P + Q)` of the line function satisfies

  `N(P) · N(−P) = −(H(x T₁)H(x T₂)H(x T₃)) · (X P − X T₁)(X P − X T₂)(X P − X T₃)`.

The factorization is passed as the hypothesis `hfac` rather than derived, so that the lemma
covers the TANGENT line (`T₁ = T₂`) on the same footing as the secant — which matters,
because the tangent case is exactly the degenerate subcase of the additivity leaf.

`STAR` pins the norm only up to SIGN; supplying the sign is `HNORM`, the statement that the
norm is itself a line function on the quotient, and that is the content still missing. -/
lemma velu_norm_line_mul_neg (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) (x₀ y₀ ℓ : F)
    {T₁ T₂ T₃ : W.Point} (h₁ : T₁ ∉ S) (h₂ : T₂ ∉ S) (h₃ : T₃ ∉ S)
    (hfac : W.addPolynomial x₀ y₀ ℓ
      = -((Polynomial.X - Polynomial.C (veluPointX T₁))
          * (Polynomial.X - Polynomial.C (veluPointX T₂))
          * (Polynomial.X - Polynomial.C (veluPointX T₃)))) :
    (∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)))
      * (∏ Q ∈ S, (veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀)))
      = -((veluH S).eval (veluPointX T₁) * (veluH S).eval (veluPointX T₂)
            * (veluH S).eval (veluPointX T₃))
        * ((W.veluCoordX S P - W.veluCoordX S T₁) * (W.veluCoordX S P - W.veluCoordX S T₂)
            * (W.veluCoordX S P - W.veluCoordX S T₃)) := by
  classical
  have hre : (∏ Q ∈ S, (veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀)))
      = ∏ Q ∈ S, (veluPointY (-(P + Q)) - (ℓ * (veluPointX (-(P + Q)) - x₀) + y₀)) := by
    rw [← velu_prod_neg W hS
      (fun Q => veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀))]
    exact Finset.prod_congr rfl fun Q _ => by
      rw [show (-P + -Q : W.Point) = -(P + Q) by abel]
  have hstep : ∀ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀))
        * (veluPointY (-(P + Q)) - (ℓ * (veluPointX (-(P + Q)) - x₀) + y₀))
      = -((veluPointX (P + Q) - veluPointX T₁) * (veluPointX (P + Q) - veluPointX T₂)
            * (veluPointX (P + Q) - veluPointX T₃)) := by
    intro Q hQ
    have hPQ : P + Q ∉ S := velu_add_notMem hS hP hQ
    have hPQ0 : P + Q ≠ 0 := fun h => hPQ (h ▸ hS.zero_mem)
    rw [velu_line_pair W x₀ y₀ ℓ hPQ0, hfac]
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hre, ← Finset.prod_mul_distrib, Finset.prod_congr rfl hstep]
  have hsplit : (∏ Q ∈ S, -((veluPointX (P + Q) - veluPointX T₁)
        * (veluPointX (P + Q) - veluPointX T₂) * (veluPointX (P + Q) - veluPointX T₃)))
      = (-1 : F) ^ S.card * ((∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₁))
          * (∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₂))
          * (∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₃))) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => by ring
  rw [hsplit, hodd.neg_one_pow, velu_fibre_prod_sub_point W S hS hodd hP h₁,
    velu_fibre_prod_sub_point W S hS hodd hP h₂, velu_fibre_prod_sub_point W S hS hodd hP h₃]
  ring

/-- **STAR for the secant through `A` and `B`, PROVEN 2026-07-26.** The specialization of
`velu_norm_line_mul_neg` to the line of `velu_map_add_of_notMem`: `ℓ` is mathlib's `slope`,
the three points cut out are `A`, `B` and `−(A + B)`, and `A + B ∉ S` is exactly what
supplies mathlib's nondegeneracy side condition `¬(x_A = x_B ∧ y_A = negY x_B y_B)`, since
that condition says precisely `A = −B`.

The third point is recorded through `veluPointX (A + B)`, which is legitimate because
`veluPointX` and `veluCoordX` are both even (`velu_pointX_neg`, `veluCoordX_neg`), so the
third factor is stated at `A + B` rather than at `−(A + B)`. -/
theorem velu_norm_line_mul_neg_slope (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S)
    {P : W.Point} (hP : P ∉ S) :
    (∏ Q ∈ S, (veluPointY (P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
      * (∏ Q ∈ S, (veluPointY (-P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (-P + Q) - veluPointX A) + veluPointY A)))
      = -((veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
            * (veluH S).eval (veluPointX (A + B)))
        * ((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) := by
  have hA0 : A ≠ 0 := fun h => hA (h ▸ hS.zero_mem)
  have hB0 : B ≠ 0 := fun h => hB (h ▸ hS.zero_mem)
  have hAB0 : A + B ≠ 0 := fun h => hAB (h ▸ hS.zero_mem)
  have heqA : W.Equation (veluPointX A) (veluPointY A) := by
    cases A with
    | zero => exact absurd rfl hA0
    | some x y h => exact h.1
  have heqB : W.Equation (veluPointX B) (veluPointY B) := by
    cases B with
    | zero => exact absurd rfl hB0
    | some x y h => exact h.1
  have hxy : ¬(veluPointX A = veluPointX B
      ∧ veluPointY A = W.negY (veluPointX B) (veluPointY B)) := by
    rintro ⟨hx, hy⟩
    refine hAB0 ?_
    have hAn : A = -B := by
      cases A with
      | zero => exact absurd rfl hA0
      | some xa ya ha =>
        cases B with
        | zero => exact absurd rfl hB0
        | some xb yb hb =>
          rw [Affine.Point.neg_some]
          exact velu_point_some_eq hx hy
    rw [hAn, neg_add_cancel]
  have hxAB : veluPointX (A + B)
      = W.addX (veluPointX A) (veluPointX B)
          (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)) := by
    cases A with
    | zero => exact absurd rfl hA0
    | some xa ya ha =>
      cases B with
      | zero => exact absurd rfl hB0
      | some xb yb hb =>
        simp only [veluPointX_some, veluPointY_some] at hxy ⊢
        rw [Affine.Point.add_some hxy]
        rfl
  refine velu_norm_line_mul_neg W S hS hodd hP (veluPointX A) (veluPointY A) _ hA hB hAB ?_
  rw [Affine.addPolynomial_slope heqA heqB hxy, hxAB]

omit [DecidableEq F] in
/-- Over an algebraically closed field `veluPointX` hits every value, so it avoids any
prescribed FINITE set of values: complete the square and take a square root. -/
lemma velu_exists_point_notMem [IsAlgClosed F] (Bad : Finset F) :
    ∃ P : W.Point, veluPointX P ∉ Bad := by
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset Bad
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq
      ((W.a₁ * x + W.a₃) ^ 2 + 4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
      (n := 2) (by norm_num)
  refine ⟨Affine.Point.some x ((d - (W.a₁ * x + W.a₃)) / 2) ?_, hx⟩
  refine Affine.equation_iff_nonsingular.mp ?_
  rw [Affine.equation_iff]
  field_simp
  linear_combination hd

/-- **The fibres of the Vélu `x`-coordinate are small.** If two points outside `S` have the
same Vélu `x`-coordinate then the second one's own `x`-coordinate is among the `|S|` values
`x(P + Q)`: the two fibre polynomials of `velu_xNum_sub_eq_prod` coincide, and `x(P')` is a
root of the second one through its `Q = 0` factor. -/
lemma velu_pointX_mem_of_coordX_eq {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P P' : W.Point} (hP : P ∉ S) (hP' : P' ∉ S)
    (h : W.veluCoordX S P = W.veluCoordX S P') :
    veluPointX P' ∈ S.image (fun Q => veluPointX (P + Q)) := by
  classical
  have hprod := velu_xNum_sub_eq_prod W S hS hodd hP
  have hprod' := velu_xNum_sub_eq_prod W S hS hodd hP'
  rw [← h] at hprod'
  have heqprod : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))))
      = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P' + Q))) := hprod.symm.trans hprod'
  have hz : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q)))).eval
      (veluPointX P') = 0 := by
    rw [heqprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hS.zero_mem (by simp)
  rw [Polynomial.eval_prod] at hz
  obtain ⟨Q, hQ, hQ0⟩ := Finset.prod_eq_zero_iff.mp hz
  refine Finset.mem_image.mpr ⟨Q, hQ, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ0
  exact (sub_eq_zero.mp hQ0).symm

/-- **PROVEN: three admissible points with pairwise distinct Vélu `x`-coordinates**, over an
algebraically closed field.  This is the second ingredient of `velu_coordX_add_eq_addX`, and
it is exactly what can FAIL over the ground field. -/
lemma velu_exists_three_coordX [IsAlgClosed F] (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) :
    ∃ P₀ P₁ P₂ : W.Point, P₀ ∉ S ∧ P₁ ∉ S ∧ P₂ ∉ S
      ∧ W.veluCoordX S P₀ ≠ W.veluCoordX S P₁
      ∧ W.veluCoordX S P₀ ≠ W.veluCoordX S P₂
      ∧ W.veluCoordX S P₁ ≠ W.veluCoordX S P₂ := by
  classical
  have step : ∀ Bad : Finset F, ∃ P : W.Point, P ∉ S ∧ veluPointX P ∉ Bad := by
    intro Bad
    obtain ⟨P, hP⟩ := velu_exists_point_notMem W (Bad ∪ S.image veluPointX)
    exact ⟨P, fun hc => hP (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)),
      fun hc => hP (Finset.mem_union_left _ hc)⟩
  obtain ⟨P₀, hP₀, -⟩ := step ∅
  obtain ⟨P₁, hP₁, h1⟩ := step (S.image (fun Q => veluPointX (P₀ + Q)))
  obtain ⟨P₂, hP₂, h2⟩ := step ((S.image (fun Q => veluPointX (P₀ + Q)))
      ∪ (S.image (fun Q => veluPointX (P₁ + Q))))
  exact ⟨P₀, P₁, P₂, hP₀, hP₁, hP₂,
    fun h => h1 (velu_pointX_mem_of_coordX_eq W hS hodd hP₀ hP₁ h),
    fun h => h2 (Finset.mem_union_left _ (velu_pointX_mem_of_coordX_eq W hS hodd hP₀ hP₂ h)),
    fun h => h2 (Finset.mem_union_right _
      (velu_pointX_mem_of_coordX_eq W hS hodd hP₁ hP₂ h))⟩


/-! ### From STAR to the `addX` identity: the assembly, and the base change it needs

`velu_addX_eq_of_norm_line` below is the ~40-line finish the ROUTE MAP in the next
docstring describes: substituting `HNORM` into `STAR` and applying `velu_line_pair` ON the
quotient curve leaves two monic cubics, and their difference — of degree `≤ 2` — is killed
by three distinct evaluation points.  It needs NO case split on collisions and no
cubic-coefficient comparison beyond the two coefficients it reads off.

`velu_coordX_add_eq_addX` then runs that over `AlgebraicClosure F` and descends, because the
three evaluation points can genuinely fail to exist over `F` (take `A` of order `3` modulo
`S`, `B ≡ A`, `W(F) = ⟨A⟩ + S`).  The descent is `velu_bc_coordX` / `velu_bc_coordY`
together with the base-change family already in this file. -/

omit [CharZero F] [W.IsElliptic] in
/-- A point of `W` lying ON the line `y = ℓ(x − x₀) + y₀` makes the whole norm product
vanish, through its `Q = 0` factor. -/
lemma velu_norm_eq_zero_of_on_line {S : Finset W.Point} (hS : IsPointSubgroup S)
    {x₀ y₀ ℓ : F} {T : W.Point}
    (hT : veluPointY T = ℓ * (veluPointX T - x₀) + y₀) :
    ∏ Q ∈ S, (veluPointY (T + Q) - (ℓ * (veluPointX (T + Q) - x₀) + y₀)) = 0 :=
  Finset.prod_eq_zero hS.zero_mem (by simp only [add_zero]; rw [hT]; ring)

omit [CharZero F] [W.IsElliptic] in
/-- **The second point of a secant lies on it.** For two points of `W` satisfying mathlib's
nondegeneracy side condition, `(x₂, y₂)` lies on the line through `(x₁, y₁)` of slope
`W.slope x₁ x₂ y₁ y₂`. -/
lemma velu_slope_line_snd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    y₂ = W.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) + y₁ := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    have := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    rw [← hx, ← this]; ring
  · rw [Affine.slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
lemma velu_point_equation {P : W.Point} (hP : P ≠ 0) :
    W.Equation (veluPointX P) (veluPointY P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h.1

omit [CharZero F] [W.IsElliptic] in
/-- `A + B ∉ S` supplies mathlib's nondegeneracy side condition for the secant through
`A` and `B`, since that condition says precisely `A = −B`. -/
lemma velu_point_ne_negY {S : Finset W.Point} (hS : IsPointSubgroup S)
    {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S) :
    ¬(veluPointX A = veluPointX B
      ∧ veluPointY A = W.negY (veluPointX B) (veluPointY B)) := by
  have hA0 : A ≠ 0 := fun h => hA (h ▸ hS.zero_mem)
  have hB0 : B ≠ 0 := fun h => hB (h ▸ hS.zero_mem)
  have hAB0 : A + B ≠ 0 := fun h => hAB (h ▸ hS.zero_mem)
  rintro ⟨hx, hy⟩
  refine hAB0 ?_
  have hAn : A = -B := by
    cases A with
    | zero => exact absurd rfl hA0
    | some xa ya ha =>
      cases B with
      | zero => exact absurd rfl hB0
      | some xb yb hb =>
        rw [Affine.Point.neg_some]
        exact velu_point_some_eq hx hy
  rw [hAn, neg_add_cancel]

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
/-- Subtraction of `Cubic.toPoly`s, coefficientwise. -/
lemma velu_cubic_toPoly_sub (P Q : Cubic F) :
    P.toPoly - Q.toPoly
      = (⟨P.a - Q.a, P.b - Q.b, P.c - Q.c, P.d - Q.d⟩ : Cubic F).toPoly := by
  simp only [Cubic.toPoly, Polynomial.C_sub]
  ring

/-- **THE ASSEMBLY.** Given `HNORM` — the statement that the norm along `S` of the secant
line function through `A` and `B` is again a line function `c·(Y − λX − μ)` with `c² = κ` —
together with three points of `W ∖ S` whose Vélu `x`-coordinates are pairwise distinct, the
`addX` identity for the Vélu map follows.  No case split on collisions is needed. -/
theorem velu_addX_eq_of_norm_line (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S)
    {c lam mu : F}
    (hc : c ^ 2 = (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
            * (veluH S).eval (veluPointX (A + B)))
    (hN : ∀ P : W.Point, P ∉ S →
      (∏ Q ∈ S, (veluPointY (P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
        = c * (W.veluCoordY S P - (lam * W.veluCoordX S P + mu)))
    {P₀ P₁ P₂ : W.Point} (hP₀ : P₀ ∉ S) (hP₁ : P₁ ∉ S) (hP₂ : P₂ ∉ S)
    (h01 : W.veluCoordX S P₀ ≠ W.veluCoordX S P₁)
    (h02 : W.veluCoordX S P₀ ≠ W.veluCoordX S P₂)
    (h12 : W.veluCoordX S P₁ ≠ W.veluCoordX S P₂) :
    W.veluCoordX S (A + B)
      = (W.veluCurve S).addX (W.veluCoordX S A) (W.veluCoordX S B)
          ((W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
            (W.veluCoordY S A) (W.veluCoordY S B)) := by
  classical
  -- (1) `κ ≠ 0`, hence `c ≠ 0`.
  have hκ : (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
              * (veluH S).eval (veluPointX (A + B)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (veluH_eval_ne_zero hS hA) (veluH_eval_ne_zero hS hB))
      (veluH_eval_ne_zero hS hAB)
  have hc0 : c ≠ 0 := by intro h; exact hκ (by rw [← hc, h]; ring)
  -- (2) `N` vanishes at any point of `W ∖ S` lying on the line, so its Vélu image lies on
  -- the line `η = λ ξ + μ` of the quotient.
  have hline : ∀ T : W.Point, T ∉ S →
      veluPointY T = W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
          * (veluPointX T - veluPointX A) + veluPointY A →
      W.veluCoordY S T = lam * W.veluCoordX S T + mu := by
    intro T hT hTline
    have h0 := (hN T hT).symm.trans (velu_norm_eq_zero_of_on_line W hS hTline)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hc0)
  have hlineA : W.veluCoordY S A = lam * W.veluCoordX S A + mu := hline A hA (by ring)
  have hlineB : W.veluCoordY S B = lam * W.veluCoordX S B + mu :=
    hline B hB (velu_slope_line_snd W (velu_point_equation W (fun h => hA (h ▸ hS.zero_mem)))
      (velu_point_equation W (fun h => hB (h ▸ hS.zero_mem)))
      (velu_point_ne_negY W hS hA hB hAB))
  -- Eliminate `μ`, which the line relation at `A` determines.
  have hmu : mu = W.veluCoordY S A - lam * W.veluCoordX S A := by rw [hlineA]; ring
  subst hmu
  -- (3) STAR + HNORM give the pointwise cubic identity on the quotient curve.
  have hcube : ∀ P : W.Point, P ∉ S →
      ((W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam).eval
          (W.veluCoordX S P)
        = -((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) := by
    intro P hP
    have hstar := velu_norm_line_mul_neg_slope W S hS hodd hA hB hAB hP
    rw [hN P hP, hN (-P) (velu_neg_notMem W hS hP), veluCoordX_neg hS P,
      veluCoordY_neg hS hP] at hstar
    have heq := W.velu_equation S hS hodd hP
    rw [Affine.equation_iff] at heq
    simp only [Affine.negY] at hstar
    have hkey : c ^ 2 * (((W.veluCurve S).addPolynomial (W.veluCoordX S A)
          (W.veluCoordY S A) lam).eval (W.veluCoordX S P)
        + (W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) = 0 := by
      rw [velu_addPolynomial_eval]
      linear_combination hstar + c ^ 2 * heq
        + ((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) * hc
    linear_combination (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hc0)
  -- (4) Three distinct evaluation points upgrade it to an identity of POLYNOMIALS.
  have hcard : ({W.veluCoordX S P₀, W.veluCoordX S P₁, W.veluCoordX S P₂} : Finset F).card
      = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  have hdiff : (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
      + (Polynomial.X - Polynomial.C (W.veluCoordX S A))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B))) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
      {W.veluCoordX S P₀, W.veluCoordX S P₁, W.veluCoordX S P₂} ?_ ?_
    · intro ξ hξ
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hξ
      rcases hξ with rfl | rfl | rfl
      · linear_combination hcube P₀ hP₀
      · linear_combination hcube P₁ hP₁
      · linear_combination hcube P₂ hP₂
    · rw [hcard, show (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
          + (Polynomial.X - Polynomial.C (W.veluCoordX S A))
            * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
            * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B)))
          = (⟨(1 : F) - 1,
              -(W.veluCoordX S A + W.veluCoordX S B + W.veluCoordX S (A + B))
                - (-lam ^ 2 - (W.veluCurve S).a₁ * lam + (W.veluCurve S).a₂),
              (W.veluCoordX S A * W.veluCoordX S B + W.veluCoordX S A * W.veluCoordX S (A + B)
                  + W.veluCoordX S B * W.veluCoordX S (A + B))
                - (2 * W.veluCoordX S A * lam ^ 2
                  + ((W.veluCurve S).a₁ * W.veluCoordX S A - 2 * W.veluCoordY S A
                      - (W.veluCurve S).a₃) * lam
                  + (-(W.veluCurve S).a₁ * W.veluCoordY S A + (W.veluCurve S).a₄)),
              -(W.veluCoordX S A * W.veluCoordX S B * W.veluCoordX S (A + B))
                - (-W.veluCoordX S A ^ 2 * lam ^ 2
                  + (2 * W.veluCoordX S A * W.veluCoordY S A
                      + (W.veluCurve S).a₃ * W.veluCoordX S A) * lam
                  - (W.veluCoordY S A ^ 2 + (W.veluCurve S).a₃ * W.veluCoordY S A
                      - (W.veluCurve S).a₆))⟩ : Cubic F).toPoly from ?_]
      · exact lt_of_le_of_lt (Cubic.natDegree_of_a_eq_zero (by ring)) (by norm_num)
      · rw [Affine.addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_add_eq_sub,
          velu_cubic_toPoly_sub]
  have hpoly : (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
      = -((Polynomial.X - Polynomial.C (W.veluCoordX S A))
          * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
          * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B)))) :=
    eq_neg_of_add_eq_zero_left hdiff
  -- (5) Coefficient comparison.
  rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq] at hpoly
  have hb := Cubic.b_of_eq hpoly
  have hcc := Cubic.c_of_eq hpoly
  simp only at hb hcc
  -- (6) `λ` IS the slope on the quotient curve: the secant case from the line relations,
  -- the tangent case from the `ξ`-coefficient.
  have hxyV := W.velu_coord_ne_neg S hS hodd hA hB hAB
  have hslope : lam = (W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
      (W.veluCoordY S A) (W.veluCoordY S B) := by
    by_cases hab : W.veluCoordX S A = W.veluCoordX S B
    · have hy : W.veluCoordY S A
          ≠ (W.veluCurve S).negY (W.veluCoordX S B) (W.veluCoordY S B) := fun h => hxyV ⟨hab, h⟩
      have hyy : W.veluCoordY S A = W.veluCoordY S B := by rw [hlineB, hab]; ring
      have hnegeq : (W.veluCurve S).negY (W.veluCoordX S A) (W.veluCoordY S A)
          = (W.veluCurve S).negY (W.veluCoordX S B) (W.veluCoordY S B) := by rw [hab, hyy]
      have hy' : W.veluCoordY S A
          ≠ (W.veluCurve S).negY (W.veluCoordX S A) (W.veluCoordY S A) := by
        rw [hnegeq]; exact hy
      rw [Affine.slope_of_Y_ne hab hy, eq_div_iff (sub_ne_zero.mpr hy')]
      rw [← hab] at hb hcc
      simp only [Affine.negY]
      linear_combination (-1 : F) * hcc + (-2 * W.veluCoordX S A) * hb
    · rw [Affine.slope_of_X_ne hab, eq_div_iff (sub_ne_zero.mpr hab)]
      linear_combination hlineB
  -- (7) The `ξ²`-coefficient IS the leaf.
  rw [← hslope]
  simp only [Affine.addX]
  linear_combination hb

/-! ### `HNORM` reduced to `POLY`: the sign and `c² = κ` are DERIVED, not assumed

(2026-07-27, fourth owner.)  `HNORM` — "the norm of the secant line function is again a
LINE function `c·(Y − λX − μ)` on the quotient, with `c² = κ`" — was carried as a single
sorried `obtain` inside `velu_coordX_add_eq_addX`.  It is now PROVEN (`velu_hnorm` below)
from a strictly weaker and much more standard leaf:

  **(POLY)  `∃ a b : F[T]`, `N(P) = a(X P) + b(X P)·Y P` for every `P ∉ S`.**

That is, the norm lies in the COORDINATE RING `F[X] ⊕ F[X]·Y` of the affine quotient curve
— the honest regularity statement, with no reference to degrees, to `κ`, or to a sign.
`N` is `S`-invariant by construction (reindex the product) and regular off `S`, so it
descends to a regular function on `V ∖ {O}`, whose ring of regular functions is exactly
`F[X] ⊕ F[X]·Y`.  `POLY` says precisely that, and nothing more.

**Everything that used to be assumed alongside it is now a theorem**, and this is the
mathematical content added here.  Given `POLY`, `STAR` alone forces the degrees, and the
degrees force the sign:

1. `X` is even and `Y(−P) = negY (X P) (Y P)` (`veluCoordX_neg`, `veluCoordY_neg`), so
   `POLY` at `−P` reads `N(−P) = a(ξ) + b(ξ)·negY(ξ, Y)` with the SAME `ξ = X P`.
2. Multiplying, and eliminating `Y²` by `velu_equation` on `V`, turns `STAR` into a
   POINTWISE identity between two expressions in `ξ` alone.  Completing the square with
   `AA := 2a − b·(A₁T + A₃)` puts it in the two-term form

     `AA(ξ)² − b(ξ)²·Φ_V(ξ) = −4κ·ρ(ξ)`,   `Φ_V := 4T³ + (4A₂+A₁²)T² + (4A₄+2A₁A₃)T + 4A₆+A₃²`,

   where `Φ_V` is `(2Y + A₁X + A₃)²` reduced by the Weierstrass equation of `V`, and
   `ρ := (T − X A)(T − X B)(T − X (A+B))`.
3. Over `F̄` the admissible Vélu `x`-coordinates are INFINITE in number
   (`velu_exists_coordX_values`, proven below by iterating `velu_exists_point_notMem`
   against the finite fibres of `velu_pointX_mem_of_coordX_eq`), so a pointwise identity
   between polynomials of bounded degree is a POLYNOMIAL identity.
4. **The degree argument, which is the whole trick.**  `deg(AA²) = 2·deg AA` is EVEN and
   `deg(b²Φ_V) = 2·deg b + 3` is ODD, so the two can never cancel and
   `deg(AA² − b²Φ_V) = max`.  The right-hand side has degree exactly `3` (`κ ≠ 0` by
   `veluH_eval_ne_zero` at `A`, `B`, `A+B`; `ρ` is monic).  Hence `b ≠ 0` (else `2·deg AA = 3`),
   `2·deg b + 3 ≤ 3` so **`b` is a CONSTANT `β`**, and `2·deg AA ≤ 3` so **`AA` is LINEAR**.
   Comparing the `T³` coefficients then gives `β² = κ` outright.

So `c := β`, and `λ`, `μ` are read off the two coefficients of `AA`.  **No pole order at
infinity is ever computed, and no Riemann–Roch input is used**: the bound that the route map
expected to come from a pole count at `O` falls out of `STAR` plus the parity of `2·deg b + 3`.
That is the one genuinely new observation here, and it is what makes `POLY` — rather than
`HNORM` — the right leaf.

**Which AXIS was searched, and what remains refuted.**  The four routes refuted by the
previous owners (`Ideal.relNorm`; the even/odd split of `N`; any pairing of `N` against
`N ∘ [−1]`; `Affine.Point.toClass` / `ClassGroup`) were all searched along the
*multiplicative* axis — identities among norms of functions on `W`.  This owner searched
that axis again and confirms it is closed, with a sharper reason than "every identity is
even": the multiplicative group of functions whose norm is COMPUTABLE from the fibre
polynomial is exactly the group of EVEN functions, because `∏_{Q∈S} g(x(P+Q))` for a
polynomial `g` factors over `F̄` into `∏_i (X P·H(r_i) − XNum(r_i))` by
`velu_fibre_prod_sub` at each root `r_i` of `g` — an explicit polynomial in `X P` of degree
`≤ deg g`.  A slanted line is not in that group, and `f·(f∘[−1])` is the only even
combination available, which is `STAR` itself.  So no new relation can be manufactured
multiplicatively; this is why `POLY` is not a corollary of `STAR`.

The axis searched and found OPEN is the *additive* one, and it is recorded here because it
is the most promising handle anyone has produced on `POLY`.  Writing `w_R := 2y_R + a₁x_R + a₃`
and comparing `x(R + T₀)` against `x(R − T₀)` through the two slopes at `T₀` gives, for every
`T₀ ∉ S ∪ (−P + S)` and every `P ∉ S`,

  `Σ_{Q∈S} w_{P+Q} / (x(P+Q) − x_{T₀})²  =  (X(P − T₀) − X(P + T₀)) / w_{T₀}`,

an ODD identity — the first one in this development that is not a consequence of `STAR`.
Specialising `T₀ = Q₀ ∈ S ∖ 0` makes the right side VANISH (`veluCoordX_add_mem`), giving
`(|S|−1)/2` independent linear relations among the `|S|` unknown power sums
`Σ_{Q∈S} x(P+Q)^j · y(P+Q)`; Vélu's `Y` is the `j = 0` one.  That is `(|S|+1)/2` knowns out
of `|S|`, so it is genuinely SHORT, and the general-`T₀` form is circular (its right-hand
side is `X` at TRANSLATED points, which is what additivity is for).

**RESOLVED 2026-07-27, and `POLY` IS NOW PROVEN.**  The refuting check recorded here — "express
the odd traces `Σ_j x^j y` in `X P` and `Y P`" — was met, but by a completely different handle
from the `T₀`-identity above, which stays circular.  The handle is that the fibre polynomial
`f_P` is the SAME polynomial at every point of the coset (translation invariance of `X`), so
`velu_wronskian` read at `R = P + Q` instead of at `P` gives `w_R·f_P'(x_R) = W_P·H(x_R)`, and
Lagrange interpolation turns that into `Σ_{Q∈S} β(x(P+Q))·w(P+Q) = W_P·coeff_{n−1}((βH) mod f_P)`.
See the section `POLY PROVEN: traces over the Vélu fibre` below for the full route; the
multiplicative-axis verdict above still stands and is still the reason `POLY` is not a corollary
of `STAR`. -/
lemma velu_exists_coordX_values [IsAlgClosed F] (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (k : ℕ) :
    ∃ t : Finset F, t.card = k ∧ ∀ ξ ∈ t, ∃ P : W.Point, P ∉ S ∧ W.veluCoordX S P = ξ := by
  classical
  have step : ∀ Bad : Finset F, ∃ P : W.Point, P ∉ S ∧ veluPointX P ∉ Bad := by
    intro Bad
    obtain ⟨P, hP⟩ := velu_exists_point_notMem W (Bad ∪ S.image veluPointX)
    exact ⟨P, fun hc => hP (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)),
      fun hc => hP (Finset.mem_union_left _ hc)⟩
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨t, hcard, hw⟩ := ih
    choose f hf1 hf2 using hw
    obtain ⟨P, hPS, hPBad⟩ :=
      step (t.attach.biUnion fun ξ => S.image fun Q => veluPointX (f ξ.1 ξ.2 + Q))
    have hnew : W.veluCoordX S P ∉ t := by
      intro hmem
      refine hPBad (Finset.mem_biUnion.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, ?_⟩)
      exact velu_pointX_mem_of_coordX_eq W hS hodd (hf1 _ hmem) hPS ((hf2 _ hmem).trans rfl)
    refine ⟨insert (W.veluCoordX S P) t, by rw [Finset.card_insert_of_notMem hnew, hcard], ?_⟩
    intro ξ hξ
    rcases Finset.mem_insert.mp hξ with h | h
    · exact ⟨P, hPS, h.symm⟩
    · exact ⟨f ξ h, hf1 ξ h, hf2 ξ h⟩

/-! ### `POLY` PROVEN: traces over the Vélu fibre

(2026-07-27, fifth owner.)  The leaf `POLY` below is now a THEOREM.  The route is
elementary and closes the *additive axis* that the section docstring above recorded as the
one open handle; no function-field theory, no divisors and no Riemann–Roch are used.

**The observation that unlocks it.**  Write `f_P := XNum − X_P·H` for the fibre polynomial,
whose roots are exactly the `x(P+Q)`, `Q ∈ S` (`velu_xNum_sub_eq_prod`).  Because the Vélu
coordinates are translation invariant (`veluCoordX_add_mem`), `f_R = f_P` for EVERY `R` in
the coset `P + S`.  So `velu_wronskian` — `XNum'·H − XNum·H' = Ξ`, which is the statement
`w_P·f_P'(x_P) = W_P·H(x_P)` in cleared form — may be read at `R` rather than at `P`:

  **`w_R · f_P'(x_R) = W_P · H(x_R)`  for every `R = P + Q`, `Q ∈ S`**  (`velu_key_wronskian`),

with `w_R = 2y_R + a₁x_R + a₃` and `W_P = 2Y_P + A₁X_P + A₃`.  That single identity makes
every ODD trace over the fibre computable, which is exactly what the previous owners were
missing: the multiplicative axis is genuinely closed, but the additive one is not.

**The two trace formulas.**  For `f = ∏_i (T − r_i)` monic and any `h`:

* `∑_i h(r_i) = coeff_{n−1}((h·f') mod f)` (`velu_trace_even`) — no separability needed,
  because `(h·f_i) mod f = h(r_i)·f_i` termwise for `f_i = f/(T − r_i)`;
* if the `r_i` are DISTINCT and `c_i·f'(r_i) = μ·g(r_i)`, then
  `∑_i c_i = μ·coeff_{n−1}(g mod f)` (`velu_trace_odd`), by Lagrange interpolation.

Applied to the fibre with `c_Q = β(x(P+Q))·w(P+Q)` and `g = β·H`, the second gives

  `∑_{Q∈S} β(x(P+Q))·w(P+Q) = W_P · coeff_{n−1}((β·H) mod f_P)`  (`velu_trace_odd_fibre`).

The fibre `x`-coordinates are distinct exactly when `2P ∉ S`; and when `2P ∈ S` the coset is
stable under negation, so the left side vanishes by pairing `R ↔ −R` while `W_P = 0` because
the Vélu image of `P` is then `2`-torsion.  So both sides vanish and the formula still holds.

**Uniformity in `P`.**  Reducing modulo the GENERIC fibre polynomial `XNum − χ·H` over `F[χ]`
(`veluGenFibrePoly`, monic in `T` of degree `|S|`) and specialising `χ ↦ X_P` — `modByMonic`
commutes with the coefficientwise ring map — turns both trace coefficients into fixed
polynomials evaluated at `X_P` (`velu_exists_trace_even`, `velu_exists_trace_odd`).

**From traces to the product.**  Say `g` is REPRESENTED (`VeluRepr`) if `g P = u(X_P) +
v(X_P)·W_P` for fixed `u`, `v`.  Represented functions form a ring — the product uses
`W_P² = Ψ_V(X_P)`, i.e. the quotient Weierstrass equation `velu_equation`.  Each power of
the line function is `α(x) + β(x)·y` in `W.CoordinateRing` (power basis `{1, Y}`), so every
POWER SUM `∑_{Q∈S} ℓ(P+Q)^k` is represented, by the two trace formulas.  Newton's identities
(`MvPolynomial.mul_esymm_eq_sum`, in characteristic zero) then propagate representability
from the power sums to every elementary symmetric function, and the `|S|`-th of those is the
norm `∏_{Q∈S} ℓ(P+Q)` itself.  Finally `u + v·W = (u + v(A₁X+A₃)) + 2v·Y`, which is `POLY`.

The whole argument is uniform in the line, so `POLY` holds for a general line as stated. -/

section VeluPolyTrace

open _root_.Polynomial

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- `∏_{j ∈ s} (X - C (r j))` is monic. -/
lemma velu_prodLin_monic (s : Finset ι) (r : ι → K) :
    (∏ j ∈ s, (X - C (r j))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [DecidableEq ι] in
lemma velu_prodLin_degree (s : Finset ι) (r : ι → K) :
    (∏ j ∈ s, (X - C (r j))).degree = (s.card : WithBot ℕ) := by
  rw [degree_prod]
  simp

omit [DecidableEq ι] in
lemma velu_prodLin_natDegree (s : Finset ι) (r : ι → K) :
    (∏ j ∈ s, (X - C (r j))).natDegree = s.card := by
  rw [natDegree_prod _ _ fun j _ => X_sub_C_ne_zero (r j)]
  simp

omit [DecidableEq ι] in
lemma velu_sum_modByMonic (s : Finset ι) (p : ι → K[X]) (q : K[X]) :
    (∑ i ∈ s, p i) %ₘ q = ∑ i ∈ s, (p i %ₘ q) := by
  classical
  induction s using Finset.induction with
  | empty => simp [zero_modByMonic]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_modByMonic, ih]

/-- The remainder of `h · ∏_{j ≠ i}(X − r j)` modulo `∏_j (X − r j)` is `h(r i)` times
`∏_{j ≠ i}(X − r j)`. -/
lemma velu_modByMonic_mul_prod_erase (s : Finset ι) (r : ι → K) {i : ι} (hi : i ∈ s) (h : K[X]) :
    (h * ∏ j ∈ s.erase i, (X - C (r j))) %ₘ (∏ j ∈ s, (X - C (r j)))
      = C (h.eval (r i)) * ∏ j ∈ s.erase i, (X - C (r j)) := by
  have hmon := velu_prodLin_monic s r
  have hfac : (∏ j ∈ s, (X - C (r j))) = (X - C (r i)) * ∏ j ∈ s.erase i, (X - C (r j)) :=
    (Finset.mul_prod_erase _ _ hi).symm
  obtain ⟨q, hq⟩ : (X - C (r i)) ∣ (h - C (h.eval (r i))) := dvd_iff_isRoot.mpr (by simp)
  have hsplit : h * ∏ j ∈ s.erase i, (X - C (r j))
      = C (h.eval (r i)) * ∏ j ∈ s.erase i, (X - C (r j))
        + (∏ j ∈ s, (X - C (r j))) * q := by
    rw [hfac]
    linear_combination (∏ j ∈ s.erase i, (X - C (r j))) * hq
  have hcardpos : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hsmall : (C (h.eval (r i)) * ∏ j ∈ s.erase i, (X - C (r j))).degree
      < (∏ j ∈ s, (X - C (r j))).degree := by
    rw [velu_prodLin_degree s r]
    calc (C (h.eval (r i)) * ∏ j ∈ s.erase i, (X - C (r j))).degree
        ≤ (C (h.eval (r i))).degree + (∏ j ∈ s.erase i, (X - C (r j))).degree :=
          degree_mul_le _ _
      _ ≤ 0 + (((s.erase i).card : ℕ) : WithBot ℕ) :=
          add_le_add degree_C_le (le_of_eq (velu_prodLin_degree _ _))
      _ = (((s.card - 1 : ℕ)) : WithBot ℕ) := by rw [Finset.card_erase_of_mem hi]; simp
      _ < ((s.card : ℕ) : WithBot ℕ) := by
          have hlt : s.card - 1 < s.card := by omega
          exact_mod_cast hlt
  rw [hsplit, add_modByMonic, self_mul_modByMonic hmon, add_zero,
    (modByMonic_eq_self_iff hmon).mpr hsmall]

/-- **The EVEN trace.** For `f = ∏_{i ∈ s}(X − r i)` the sum of `h` over the roots (with
multiplicity) is the top coefficient of `h·f'` reduced mod `f`. No separability needed. -/
theorem velu_trace_even (s : Finset ι) (r : ι → K) (h : K[X]) :
    ∑ i ∈ s, h.eval (r i)
      = ((h * derivative (∏ i ∈ s, (X - C (r i)))) %ₘ
          (∏ i ∈ s, (X - C (r i)))).coeff (s.card - 1) := by
  have hder : derivative (∏ i ∈ s, (X - C (r i)))
      = ∑ i ∈ s, ∏ j ∈ s.erase i, (X - C (r j)) := by
    rw [derivative_prod_finset]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [hder, Finset.mul_sum, velu_sum_modByMonic]
  rw [Polynomial.finsetSum_coeff]
  refine (Finset.sum_congr rfl fun i hi => ?_).symm
  rw [velu_modByMonic_mul_prod_erase s r hi h, coeff_C_mul]
  have hmoner : (∏ j ∈ s.erase i, (X - C (r j))).Monic := velu_prodLin_monic _ _
  have hdeger : (∏ j ∈ s.erase i, (X - C (r j))).natDegree = s.card - 1 := by
    rw [velu_prodLin_natDegree, Finset.card_erase_of_mem hi]
  have : (∏ j ∈ s.erase i, (X - C (r j))).coeff (s.card - 1) = 1 := by
    rw [← hdeger]
    exact hmoner
  rw [this, mul_one]

/-- **The ODD trace.** With DISTINCT roots, if `c i` satisfies `c i · f'(r i) = μ · g(r i)`
then `∑ c i = μ ·` (top coefficient of `g mod f`). -/
theorem velu_trace_odd (s : Finset ι) (r : ι → K)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, r i = r j → i = j)
    (g : K[X]) (c : ι → K) (μ : K)
    (hc : ∀ i ∈ s, c i * (derivative (∏ j ∈ s, (X - C (r j)))).eval (r i) = μ * g.eval (r i)) :
    ∑ i ∈ s, c i = μ * (g %ₘ (∏ i ∈ s, (X - C (r i)))).coeff (s.card - 1) := by
  classical
  set f : K[X] := ∏ i ∈ s, (X - C (r i)) with hf
  have hmon : f.Monic := velu_prodLin_monic s r
  have hder : derivative f = ∑ i ∈ s, ∏ j ∈ s.erase i, (X - C (r j)) := by
    rw [hf, derivative_prod_finset]
    exact Finset.sum_congr rfl fun i _ => by simp
  -- the Lagrange combination
  set L : K[X] := ∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, (X - C (r j)) with hL
  -- `L` agrees with `μ • (g %ₘ f)` at every root
  have heval : ∀ i ∈ s, L.eval (r i) = μ * (g %ₘ f).eval (r i) := by
    intro i hi
    have hfeval : f.eval (r i) = 0 := by
      rw [hf, eval_prod]
      exact Finset.prod_eq_zero hi (by simp)
    have h1 : L.eval (r i) = c i * (∏ j ∈ s.erase i, (X - C (r j))).eval (r i) := by
      rw [hL, eval_finsetSum]
      rw [Finset.sum_eq_single i]
      · rw [eval_mul, eval_C]
      · intro b _ hbi
        rw [eval_mul, eval_prod]
        refine mul_eq_zero_of_right _
          (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hbi, hi⟩) ?_)
        simp
      · intro hni; exact absurd hi hni
    have h2 : (derivative f).eval (r i) = (∏ j ∈ s.erase i, (X - C (r j))).eval (r i) := by
      rw [hder, eval_finsetSum, Finset.sum_eq_single i]
      · intro b _ hbi
        rw [eval_prod]
        refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hbi, hi⟩) ?_
        simp
      · intro hni; exact absurd hi hni
    have h3 : (g %ₘ f).eval (r i) = g.eval (r i) := by
      rw [modByMonic_eq_sub_mul_div g f, eval_sub, eval_mul, hfeval, zero_mul, sub_zero]
    rw [h1, ← h2, hc i hi, h3]
  -- both sides have degree < card s, and agree at card s distinct points
  have hLdeg : L.natDegree ≤ s.card - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C, zero_add, velu_prodLin_natDegree, Finset.card_erase_of_mem hi]
  have hRdeg : (C μ * (g %ₘ f)).natDegree ≤ s.card - 1 := by
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C, zero_add]
    have h1 : (g %ₘ f).degree < f.degree := degree_modByMonic_lt g hmon
    rw [velu_prodLin_degree] at h1
    rcases eq_or_ne (g %ₘ f) 0 with h0 | h0
    · simp [h0]
    · have := (Polynomial.degree_eq_natDegree h0) ▸ h1
      have hlt : (g %ₘ f).natDegree < s.card := by exact_mod_cast this
      omega
  have hEq : L = C μ * (g %ₘ f) := by
    by_contra hne
    have hsub : L - C μ * (g %ₘ f) ≠ 0 := sub_ne_zero.mpr hne
    have hdeg : (L - C μ * (g %ₘ f)).natDegree ≤ s.card - 1 :=
      le_trans (natDegree_sub_le _ _) (max_le hLdeg hRdeg)
    have hcard : s.card ≠ 0 := by
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i, hi⟩
      · exact absurd (by simp [hL, hf] : L - C μ * (g %ₘ f) = 0) hsub
      · exact Finset.card_ne_zero_of_mem hi
    have hroots : ∀ i ∈ s, (L - C μ * (g %ₘ f)).eval (r i) = 0 := by
      intro i hi
      rw [eval_sub, eval_mul, eval_C, heval i hi]
      ring
    have himg : (s.image r).card = s.card :=
      Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)
    refine hsub (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (L - C μ * (g %ₘ f)) (s.image r) ?_ ?_)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hroots i hi
    · rw [himg]; omega
  have := congrArg (fun p => Polynomial.coeff p (s.card - 1)) hEq
  simp only [hL, coeff_C_mul] at this
  rw [← this, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coeff_C_mul]
  have hmoner : (∏ j ∈ s.erase i, (X - C (r j))).Monic := velu_prodLin_monic _ _
  have hdeger : (∏ j ∈ s.erase i, (X - C (r j))).natDegree = s.card - 1 := by
    rw [velu_prodLin_natDegree, Finset.card_erase_of_mem hi]
  have hc1 : (∏ j ∈ s.erase i, (X - C (r j))).coeff (s.card - 1) = 1 := by
    rw [← hdeger]; exact hmoner
  rw [hc1, mul_one]

end VeluPolyTrace



section VeluFibreTrace

open _root_.Polynomial

omit [W.IsElliptic] in
/-- `W_P · H(x_P)² = w_P · Ξ(x_P)`: the completed square of the Vélu coordinates, cleared. -/
lemma velu_coordW_mul {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * ((veluH S).eval (veluPointX P)) ^ 2
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) * (veluXi S).eval (veluPointX P) := by
  have hV : 2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
    rw [velu_coordX_eq hS hP, velu_coordY_eq hS hP]
    exact velu_pole_V hS hP
  rw [hV, veluXi_eval hS hodd hP]
  ring

/-- The Vélu fibre polynomial at `P`. -/
noncomputable abbrev veluFibrePoly (S : Finset W.Point) (P : W.Point) : Polynomial F :=
  veluXNum S - Polynomial.C (W.veluCoordX S P) * veluH S

omit [W.IsElliptic] in
/-- **THE KEY IDENTITY.** For every `Q ∈ S`, writing `R = P + Q` and `f_P` for the fibre
polynomial, `w_R · f_P'(x_R) = W_P · H(x_R)`.

This is `velu_wronskian` transported along the translation invariance of the Vélu
coordinates: `f_P = f_R` because `X_R = X_P`, so the wronskian identity read AT `R` says
exactly this. It is what makes every "odd" trace over the fibre computable. -/
lemma velu_key_wronskian {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) {Q : W.Point} (hQ : Q ∈ S) :
    (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
        * (Polynomial.derivative (veluFibrePoly W S P)).eval (veluPointX (P + Q))
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * (veluH S).eval (veluPointX (P + Q)) := by
  have hR : P + Q ∉ S := velu_add_notMem hS hP hQ
  have hX : W.veluCoordX S (P + Q) = W.veluCoordX S P := veluCoordX_add_mem hS P hQ
  have hY : W.veluCoordY S (P + Q) = W.veluCoordY S P := veluCoordY_add_mem hS P hQ
  have hH : (veluH S).eval (veluPointX (P + Q)) ≠ 0 := veluH_eval_ne_zero hS hR
  set ξ := veluPointX (P + Q) with hξ
  -- `f_P'(ξ) · H(ξ) = Ξ(ξ)`
  have hd : (Polynomial.derivative (veluFibrePoly W S P)).eval ξ * (veluH S).eval ξ
      = (veluXi S).eval ξ := by
    have hw := congrArg (Polynomial.eval ξ) (W.velu_wronskian S hS hodd)
    have hXN : (veluXNum S).eval ξ = (veluH S).eval ξ * W.veluCoordX S P := by
      rw [veluXNum_eval hS hodd hR, hX]
    simp only [veluFibrePoly, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hw ⊢
    linear_combination hw + (Polynomial.derivative (veluH S)).eval ξ * hXN
  -- combine with the completed-square factorisation at `R`
  have hW := velu_coordW_mul W hS hodd hR
  rw [hX, hY] at hW
  have hcancel : ((2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃)
        * (Polynomial.derivative (veluFibrePoly W S P)).eval ξ) * (veluH S).eval ξ
      = ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) * (veluH S).eval ξ)
        * (veluH S).eval ξ := by
    calc ((2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃)
          * (Polynomial.derivative (veluFibrePoly W S P)).eval ξ) * (veluH S).eval ξ
        = (2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃) * (veluXi S).eval ξ := by
          rw [← hd]; ring
      _ = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
            * ((veluH S).eval ξ) ^ 2 := hW.symm
      _ = ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) * (veluH S).eval ξ)
            * (veluH S).eval ξ := by ring
  exact mul_right_cancel₀ hH hcancel

/-- The even trace over the Vélu fibre. -/
lemma velu_trace_even_fibre {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) (h : Polynomial F) :
    ∑ Q ∈ S, h.eval (veluPointX (P + Q))
      = ((h * Polynomial.derivative (veluFibrePoly W S P))
          %ₘ (veluFibrePoly W S P)).coeff (S.card - 1) := by
  classical
  have hprod : veluFibrePoly W S P = ∏ Q ∈ S, (X - C (veluPointX (P + Q))) :=
    velu_xNum_sub_eq_prod W S hS hodd hP
  rw [hprod]
  exact velu_trace_even S (fun Q => veluPointX (P + Q)) h

omit [W.IsElliptic] [CharZero F] in
/-- If `2P ∈ S` then the Vélu image of `P` is `2`-torsion, so `W_P = 0`. -/
lemma velu_coordW_eq_zero_of_two_mem {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (h2 : P + P ∈ S) :
    2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃ = 0 := by
  have hneg : -(P + P) ∈ S := hS.neg_mem _ h2
  have hEq : (-P : W.Point) = P + -(P + P) := by abel
  have hY : W.veluCoordY S (-P) = W.veluCoordY S P := by
    rw [hEq]; exact veluCoordY_add_mem hS P hneg
  have h := veluCoordY_neg hS hP
  rw [hY, veluCurve_negY] at h
  simp only [WeierstrassCurve.Affine.negY] at h
  linear_combination h

omit [W.IsElliptic] in
/-- In the degenerate case `2P ∈ S` the fibre is stable under negation, so every odd trace
over it vanishes by pairing `R ↔ −R`. -/
lemma velu_trace_odd_fibre_zero {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (h2 : P + P ∈ S) (β : Polynomial F) :
    ∑ Q ∈ S, β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃) = 0 := by
  have hneg : -(P + P) ∈ S := hS.neg_mem _ h2
  have hmem : ∀ a ∈ S, -(P + P) - a ∈ S := fun a ha => by
    rw [sub_eq_add_neg]; exact hS.add_mem _ hneg _ (hS.neg_mem _ ha)
  have hinv : ∀ a ∈ S, -(P + P) - (-(P + P) - a) = a := fun a _ => by abel
  have key : ∑ Q ∈ S, β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
      = ∑ Q ∈ S, -(β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)) := by
    refine Finset.sum_nbij' (fun Q => -(P + P) - Q) (fun Q => -(P + P) - Q)
      hmem hmem hinv hinv ?_
    intro a ha
    have hne : P + a ≠ 0 := velu_add_ne_zero W hS hP ha
    have hrw : P + (-(P + P) - a) = -(P + a) := by abel
    rw [hrw, velu_pointX_neg, velu_pointY_neg _ hne]
    ring
  rw [Finset.sum_neg_distrib] at key
  linear_combination key / 2

/-- **THE ODD TRACE OVER THE VÉLU FIBRE.** For every polynomial `β`,

  `∑_{Q ∈ S} β(x(P+Q))·w(P+Q) = W_P · coeff_{n−1}((β·H) mod f_P)`,

with `w_R = 2y_R + a₁x_R + a₃` and `W_P = 2Y_P + A₁X_P + A₃`. This is the identity the
docstring of `velu_norm_line_eq_poly` recorded as the OPEN additive axis; it follows from
`velu_key_wronskian` (which turns `w_R` into `W_P·H(x_R)/f_P'(x_R)`) together with Lagrange
interpolation, and the degenerate fibres (`2P ∈ S`, where `f_P` has repeated roots) are
exactly the ones on which BOTH sides vanish. -/
lemma velu_trace_odd_fibre {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) (β : Polynomial F) :
    ∑ Q ∈ S, β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * ((β * veluH S) %ₘ (veluFibrePoly W S P)).coeff (S.card - 1) := by
  classical
  by_cases h2 : P + P ∈ S
  · rw [velu_trace_odd_fibre_zero W hS hP h2 β, velu_coordW_eq_zero_of_two_mem W hS hP h2, zero_mul]
  · have hprod : veluFibrePoly W S P = ∏ Q ∈ S, (X - C (veluPointX (P + Q))) :=
      velu_xNum_sub_eq_prod W S hS hodd hP
    have hinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S,
        veluPointX (P + Q₁) = veluPointX (P + Q₂) → Q₁ = Q₂ := by
      intro Q₁ h₁ Q₂ h₂ hx
      have hn₁ : P + Q₁ ≠ 0 := velu_add_ne_zero W hS hP h₁
      have hn₂ : P + Q₂ ≠ 0 := velu_add_ne_zero W hS hP h₂
      rcases velu_pointX_eq_iff hn₁ hn₂ hx with h | h
      · exact add_left_cancel h
      · exfalso
        refine h2 ?_
        have hz : (P + Q₁) + (P + Q₂) = 0 := by rw [h]; exact neg_add_cancel _
        have h' : (P + P) + (Q₁ + Q₂) = 0 := by rw [← hz]; abel
        rw [add_eq_zero_iff_eq_neg] at h'
        rw [h', neg_add]
        exact hS.add_mem _ (hS.neg_mem _ h₁) _ (hS.neg_mem _ h₂)
    have hk : ∀ Q ∈ S,
        (β.eval (veluPointX (P + Q))
            * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃))
          * (Polynomial.derivative
              (∏ Q' ∈ S, (X - C (veluPointX (P + Q'))))).eval (veluPointX (P + Q))
        = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
          * (β * veluH S).eval (veluPointX (P + Q)) := by
      intro Q hQ
      have hkw := velu_key_wronskian W hS hodd hP hQ
      rw [hprod] at hkw
      simp only [Polynomial.eval_mul]
      linear_combination β.eval (veluPointX (P + Q)) * hkw
    rw [hprod]
    exact velu_trace_odd S (fun Q => veluPointX (P + Q)) hinj (β * veluH S)
      (fun Q => β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃))
      (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) hk

end VeluFibreTrace



section VeluUniformTrace

open _root_.Polynomial

/-- The GENERIC fibre polynomial `XNum − χ·H` over `F[χ]`: monic of degree `|S|` in `T`,
and specialising at `χ = X_P` to the fibre polynomial of `P`. -/
noncomputable def veluGenFibrePoly (S : Finset W.Point) : Polynomial (Polynomial F) :=
  (veluXNum S).map Polynomial.C
    - Polynomial.C (Polynomial.X : Polynomial F) * (veluH S).map Polynomial.C

omit [W.IsElliptic] [CharZero F] in
lemma veluGenFibrePoly_map (S : Finset W.Point) (ξ : F) :
    (veluGenFibrePoly W S).map (Polynomial.evalRingHom ξ)
      = veluXNum S - Polynomial.C ξ * veluH S := by
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [veluGenFibrePoly, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_id]
  simp

omit [W.IsElliptic] in
lemma veluGenFibrePoly_monic {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card) :
    (veluGenFibrePoly W S).Monic := by
  have hCinj : Function.Injective (Polynomial.C : F →+* Polynomial F) :=
    fun _ _ h => Polynomial.C_inj.mp h
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hXNmon : ((veluXNum S).map Polynomial.C).Monic := (veluXNum_monic hS hodd).map _
  have hXNdeg : ((veluXNum S).map Polynomial.C).degree = ((S.card : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective hCinj, veluXNum_degree hS hodd]
  have hHdeg : ((veluH S).map Polynomial.C).degree = (((S.card - 1 : ℕ)) : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective hCinj,
      Polynomial.degree_eq_natDegree (veluH_monic S).ne_zero, veluH_natDegree hS]
  rw [veluGenFibrePoly, sub_eq_add_neg]
  refine hXNmon.add_of_left ?_
  rw [Polynomial.degree_neg, hXNdeg]
  calc (Polynomial.C (Polynomial.X : Polynomial F) * (veluH S).map Polynomial.C).degree
      ≤ (Polynomial.C (Polynomial.X : Polynomial F)).degree
          + ((veluH S).map Polynomial.C).degree := degree_mul_le _ _
    _ ≤ 0 + (((S.card - 1 : ℕ)) : WithBot ℕ) := add_le_add degree_C_le (le_of_eq hHdeg)
    _ < ((S.card : ℕ) : WithBot ℕ) := by
        have hlt : S.card - 1 < S.card := by omega
        rw [zero_add]
        exact_mod_cast hlt

/-- **UNIFORM EVEN TRACE.** A single polynomial `u` works for every `P ∉ S`. -/
lemma velu_exists_trace_even (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (h : Polynomial F) :
    ∃ u : Polynomial F, ∀ P : W.Point, P ∉ S →
      ∑ Q ∈ S, h.eval (veluPointX (P + Q)) = u.eval (W.veluCoordX S P) := by
  refine ⟨(((h.map Polynomial.C) * Polynomial.derivative (veluGenFibrePoly W S))
      %ₘ (veluGenFibrePoly W S)).coeff (S.card - 1), ?_⟩
  intro P hP
  rw [velu_trace_even_fibre W hS hodd hP h]
  set ξ := W.veluCoordX S P with hξ
  have hstep : ∀ (p : Polynomial (Polynomial F)) (k : ℕ),
      Polynomial.eval ξ (p.coeff k) = (p.map (Polynomial.evalRingHom ξ)).coeff k := by
    intro p k
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [hstep, Polynomial.map_modByMonic _ (veluGenFibrePoly_monic W hS hodd), Polynomial.map_mul,
    Polynomial.map_map, hcomp, Polynomial.map_id, ← Polynomial.derivative_map,
    veluGenFibrePoly_map W S ξ]

/-- **UNIFORM ODD TRACE.** A single polynomial `v` works for every `P ∉ S`. -/
lemma velu_exists_trace_odd (S : Finset W.Point) (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (β : Polynomial F) :
    ∃ v : Polynomial F, ∀ P : W.Point, P ∉ S →
      ∑ Q ∈ S, β.eval (veluPointX (P + Q))
          * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
        = v.eval (W.veluCoordX S P)
          * (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) := by
  refine ⟨((((β * veluH S).map Polynomial.C)) %ₘ (veluGenFibrePoly W S)).coeff (S.card - 1), ?_⟩
  intro P hP
  rw [velu_trace_odd_fibre W hS hodd hP β]
  set ξ := W.veluCoordX S P with hξ
  have hstep : ∀ (p : Polynomial (Polynomial F)) (k : ℕ),
      Polynomial.eval ξ (p.coeff k) = (p.map (Polynomial.evalRingHom ξ)).coeff k := by
    intro p k
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [hstep, Polynomial.map_modByMonic _ (veluGenFibrePoly_monic W hS hodd),
    Polynomial.map_map, hcomp, Polynomial.map_id, veluGenFibrePoly_map W S ξ]
  exact mul_comm _ _

end VeluUniformTrace



section VeluReprSection

open _root_.Polynomial

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
lemma veluCurve_a₁ (S : Finset W.Point) : (W.veluCurve S).a₁ = W.a₁ := rfl

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
lemma veluCurve_a₃ (S : Finset W.Point) : (W.veluCurve S).a₃ = W.a₃ := rfl

/-- `g` is REPRESENTED on the Vélu quotient: `g P = u(X_P) + v(X_P)·W_P` for fixed
polynomials `u`, `v`, where `W_P = 2Y_P + A₁X_P + A₃`. -/
def VeluRepr (S : Finset W.Point) (g : W.Point → F) : Prop :=
  ∃ u v : Polynomial F, ∀ P : W.Point, P ∉ S →
    g P = u.eval (W.veluCoordX S P)
      + v.eval (W.veluCoordX S P)
        * (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)

omit [W.IsElliptic] [CharZero F] in
lemma veluRepr_const (S : Finset W.Point) (c : F) : VeluRepr W S (fun _ => c) :=
  ⟨Polynomial.C c, 0, fun P _ => by simp⟩

omit [W.IsElliptic] [CharZero F] in
lemma veluRepr_add {S : Finset W.Point} {g₁ g₂ : W.Point → F}
    (h₁ : VeluRepr W S g₁) (h₂ : VeluRepr W S g₂) :
    VeluRepr W S (fun P => g₁ P + g₂ P) := by
  obtain ⟨u₁, v₁, e₁⟩ := h₁
  obtain ⟨u₂, v₂, e₂⟩ := h₂
  refine ⟨u₁ + u₂, v₁ + v₂, fun P hP => ?_⟩
  show g₁ P + g₂ P = _
  rw [e₁ P hP, e₂ P hP]
  simp only [Polynomial.eval_add]
  ring

omit [W.IsElliptic] in
lemma veluRepr_mul {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {g₁ g₂ : W.Point → F} (h₁ : VeluRepr W S g₁) (h₂ : VeluRepr W S g₂) :
    VeluRepr W S (fun P => g₁ P * g₂ P) := by
  obtain ⟨u₁, v₁, e₁⟩ := h₁
  obtain ⟨u₂, v₂, e₂⟩ := h₂
  refine ⟨u₁ * u₂ + v₁ * v₂ * (veluPsi (W.veluCurve S)), u₁ * v₂ + u₂ * v₁, fun P hP => ?_⟩
  have hW : (veluPsi (W.veluCurve S)).eval (W.veluCoordX S P)
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) ^ 2 := by
    have := velu_psi_eval_eq (W := W.veluCurve S) (W.velu_equation S hS hodd hP)
    rwa [veluCurve_a₁, veluCurve_a₃] at this
  show g₁ P * g₂ P = _
  rw [e₁ P hP, e₂ P hP]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hW]
  ring

omit [CharZero F] [W.IsElliptic] in
lemma veluRepr_sum {S : Finset W.Point} {ι : Type*} (t : Finset ι) (g : ι → W.Point → F)
    (h : ∀ i ∈ t, VeluRepr W S (g i)) :
    VeluRepr W S (fun P => ∑ i ∈ t, g i P) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using veluRepr_const W S 0
  | insert a t ha ih =>
      have hrest := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hone := h a (Finset.mem_insert_self a t)
      have := veluRepr_add W hone hrest
      simpa [Finset.sum_insert ha] using this

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
/-- Evaluation of a coordinate-ring element written in the power basis `{1, Y}`. -/
lemma velu_coordRing_eval_basis {x₁ y₁ : F} (hEq : W.Equation x₁ y₁) (p q : Polynomial F) :
    veluEvalAt hEq (p • (1 : W.CoordinateRing)
        + q • Affine.CoordinateRing.mk W Polynomial.X)
      = p.eval x₁ + q.eval x₁ * y₁ := by
  have h1 : (p • (1 : W.CoordinateRing)) = AdjoinRoot.of W.polynomial p := by
    rw [Affine.CoordinateRing.smul, mul_one]; rfl
  have h2 : (q • Affine.CoordinateRing.mk W Polynomial.X)
      = AdjoinRoot.of W.polynomial q * veluGenY W := by
    rw [Affine.CoordinateRing.smul]; rfl
  rw [h1, h2, map_add, map_mul, veluEvalAt_of, veluEvalAt_of, veluEvalAt_genY]

omit [DecidableEq F] [CharZero F] [W.IsElliptic] in
/-- Every power of the line function is `α(x) + β(x)·y` for FIXED polynomials. -/
lemma velu_exists_line_pow (x₀ y₀ ℓ : F) (k : ℕ) :
    ∃ α β : Polynomial F, ∀ R : W.Point, R ≠ 0 →
      (veluPointY R - (ℓ * (veluPointX R - x₀) + y₀)) ^ k
        = α.eval (veluPointX R) + β.eval (veluPointX R) * veluPointY R := by
  set L : W.CoordinateRing :=
    veluGenY W - (algebraMap F W.CoordinateRing ℓ
      * (veluGenX W - algebraMap F W.CoordinateRing x₀) + algebraMap F W.CoordinateRing y₀)
    with hLdef
  obtain ⟨α, β, hαβ⟩ := Affine.CoordinateRing.exists_smul_basis_eq (L ^ k)
  refine ⟨α, β, fun R hR => ?_⟩
  have hEq : W.Equation (veluPointX R) (veluPointY R) := velu_point_equation W hR
  have hL : veluEvalAt hEq L
      = veluPointY R - (ℓ * (veluPointX R - x₀) + y₀) := by
    simp only [hLdef, map_sub, map_add, map_mul, veluEvalAt_genX, veluEvalAt_genY,
      veluEvalAt_algebraMap]
  have := congrArg (veluEvalAt hEq) hαβ
  rw [velu_coordRing_eval_basis W hEq α β, map_pow, hL] at this
  exact this.symm

end VeluReprSection



section VeluNewtonAssembly

open _root_.Polynomial

omit [W.IsElliptic] [CharZero F] in
lemma veluRepr_congr {S : Finset W.Point} {g₁ g₂ : W.Point → F}
    (h : ∀ P : W.Point, P ∉ S → g₁ P = g₂ P) (hg : VeluRepr W S g₂) : VeluRepr W S g₁ := by
  obtain ⟨u, v, e⟩ := hg
  exact ⟨u, v, fun P hP => (h P hP).trans (e P hP)⟩

omit [DecidableEq F] [CharZero F] in
lemma velu_aeval_esymm {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → F) (k : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.esymm σ F k)
      = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset σ), ∏ i ∈ t, f i := by
  simp [MvPolynomial.esymm]

omit [DecidableEq F] [CharZero F] in
lemma velu_aeval_psum {σ : Type*} [Fintype σ] (f : σ → F) (k : ℕ) :
    MvPolynomial.aeval f (MvPolynomial.psum σ F k) = ∑ i, f i ^ k := by
  simp [MvPolynomial.psum]

/-- The power sums of the line function over the fibre are represented on the quotient. -/
lemma veluRepr_powersum {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (x₀ y₀ ℓ : F) (k : ℕ) :
    VeluRepr W S (fun P => ∑ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ k) := by
  obtain ⟨α, β, hαβ⟩ := velu_exists_line_pow W x₀ y₀ ℓ k
  set γ : Polynomial F := α - Polynomial.C (2⁻¹ : F)
    * (β * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)) with hγ
  obtain ⟨u, hu⟩ := velu_exists_trace_even W S hS hodd γ
  obtain ⟨v, hv⟩ := velu_exists_trace_odd W S hS hodd β
  refine ⟨u, Polynomial.C (2⁻¹ : F) * v, fun P hP => ?_⟩
  show (∑ Q ∈ S, _) = _
  have hterm : ∀ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ k
        = γ.eval (veluPointX (P + Q))
          + (2⁻¹ : F) * (β.eval (veluPointX (P + Q))
              * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)) := by
    intro Q hQ
    have hne : P + Q ≠ 0 := velu_add_ne_zero W hS hP hQ
    rw [hαβ _ hne, hγ]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    hu P hP, hv P hP]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- **Every elementary symmetric function of the line values over the fibre is represented.**
By Newton's identities from the power sums. -/
lemma veluRepr_esymm {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    (x₀ y₀ ℓ : F) (k : ℕ) :
    VeluRepr W S (fun P => ∑ t ∈ Finset.powersetCard k
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀))) := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine veluRepr_congr W (g₂ := fun _ => (1 : F)) (fun P _ => ?_) (veluRepr_const W S 1)
      simp
    · -- Newton's identity for the values
      set val : W.Point → {Q : W.Point // Q ∈ S} → F := fun P i =>
        veluPointY (P + (i : W.Point))
          - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀) with hval
      have hnewton : ∀ P : W.Point,
          (k : F) * (∑ t ∈ Finset.powersetCard k
              (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
            = (-1) ^ (k + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
                (-1) ^ a.1
                  * (∑ t ∈ Finset.powersetCard a.1
                      (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                  * (∑ i, val P i ^ a.2) := by
        intro P
        have h := congrArg (MvPolynomial.aeval (val P))
          (MvPolynomial.mul_esymm_eq_sum {Q : W.Point // Q ∈ S} F k)
        simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
          velu_aeval_esymm, velu_aeval_psum] using h
      have hrepr : VeluRepr W S (fun P => (-1) ^ (k + 1)
          * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
              (-1) ^ a.1
                * (∑ t ∈ Finset.powersetCard a.1
                    (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                * (∑ i, val P i ^ a.2)) := by
        refine veluRepr_mul W hS hodd (veluRepr_const W S ((-1) ^ (k + 1))) ?_
        refine veluRepr_sum W _ _ (fun a ha => ?_)
        have ha1 : a.1 < k := (Finset.mem_filter.mp ha).2
        refine veluRepr_mul W hS hodd
          (veluRepr_mul W hS hodd (veluRepr_const W S ((-1) ^ a.1)) (ih a.1 ha1)) ?_
        refine veluRepr_congr W (g₂ := fun P => ∑ Q ∈ S,
          (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ a.2)
          (fun P _ => ?_) (veluRepr_powersum W hS hodd x₀ y₀ ℓ a.2)
        exact Finset.sum_coe_sort S (fun Q => (veluPointY (P + Q)
          - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ a.2)
      have hkne : (k : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      refine veluRepr_congr W (g₂ := fun P => (k : F)⁻¹ * ((-1) ^ (k + 1)
          * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
              (-1) ^ a.1
                * (∑ t ∈ Finset.powersetCard a.1
                    (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                * (∑ i, val P i ^ a.2)))
        (fun P _ => ?_) (veluRepr_mul W hS hodd (veluRepr_const W S ((k : F)⁻¹)) hrepr)
      rw [← hnewton P, inv_mul_cancel_left₀ hkne]

end VeluNewtonAssembly

/-- **`POLY`, PROVEN 2026-07-27** (cut the same day out of `HNORM`, which it replaces, and
closed a few hours later).  With it the ODD-ORDER Vélu development is complete: every
declaration in its cone is `sorry`-free and axiom-clean.

The norm along `S` of ANY line function on `W` lies in the coordinate ring of the quotient
curve: there are polynomials `a`, `b` with

  `∏_{Q∈S} (y(P+Q) − ℓ·(x(P+Q) − x₀) − y₀)  =  a(X P) + b(X P)·Y P`   for every `P ∉ S`.

This is the invariant-function theorem for `F(W)` over `F(W)^S`, in the weakest form that
the development actually needs.  `N` is `S`-invariant by construction and regular off `S`,
hence descends to a regular function on the affine curve `V ∖ {O}`, whose ring of regular
functions is `F[X] ⊕ F[X]·Y`; that is the whole content.

**It is stated for a GENERAL line** (`x₀`, `y₀`, `ℓ` arbitrary, not required to pass through
any point of `W`), because nothing in the argument uses the line's zeros, and the tangent
case of the additivity leaf is then covered on the same footing as the secant.

**Everything else that `HNORM` used to assert is derived** — the degree bounds, the fact
that `b` is a nonzero CONSTANT `c`, and `c² = κ`; see the section docstring above.

**The proof** is the trace calculus of the section `POLY PROVEN: traces over the Vélu fibre`
immediately above: `velu_key_wronskian` makes the odd traces over the fibre computable,
Newton's identities lift representability from the power sums of the line values to their
product, and the product is the norm.  It is elementary and uniform in the line — no
function-field descent, no divisors, no Riemann–Roch. -/
lemma velu_norm_line_eq_poly (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (x₀ y₀ ℓ : F) :
    ∃ a b : Polynomial F, ∀ P : W.Point, P ∉ S →
      (∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)))
        = a.eval (W.veluCoordX S P) + b.eval (W.veluCoordX S P) * W.veluCoordY S P := by
  classical
  obtain ⟨u, v, huv⟩ := veluRepr_esymm W hS hodd x₀ y₀ ℓ S.card
  refine ⟨u + v * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃),
    Polynomial.C 2 * v, fun P hP => ?_⟩
  have hcard : (Finset.univ : Finset {Q : W.Point // Q ∈ S}).card = S.card := by simp
  have hpc : Finset.powersetCard S.card (Finset.univ : Finset {Q : W.Point // Q ∈ S})
      = {Finset.univ} := by
    rw [← hcard]; exact Finset.powersetCard_self _
  have hprod : (∑ t ∈ Finset.powersetCard S.card
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀)))
      = ∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) := by
    rw [hpc, Finset.sum_singleton]
    exact Finset.prod_coe_sort S
      (fun Q => veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀))
  have h : (∑ t ∈ Finset.powersetCard S.card
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀)))
      = u.eval (W.veluCoordX S P) + v.eval (W.veluCoordX S P)
        * (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) := huv P hP
  rw [← hprod, h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring


/-- **`HNORM`, PROVEN 2026-07-27** from `POLY` (`velu_norm_line_eq_poly`), `STAR`
(`velu_norm_line_mul_neg_slope`) and a degree count — over an algebraically closed field,
which is where `velu_coordX_add_eq_addX` runs it.

The norm along `S` of the secant through `A` and `B` is `c·(Y − λX − μ)` on the quotient,
with `c² = κ = H(x_A)·H(x_B)·H(x_{A+B})`.  Both the LINE shape (that `b` is a constant and
`a` is linear) and the SIGN-carrying relation `c² = κ` are consequences of `POLY` here, not
hypotheses: see the section docstring above.  The only step that needs `IsAlgClosed` is
`velu_exists_coordX_values`, which supplies enough distinct Vélu `x`-coordinates to promote
the pointwise identity to a polynomial one. -/
theorem velu_hnorm [IsAlgClosed F] (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S) :
    ∃ c lam mu : F,
      c ^ 2 = (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
          * (veluH S).eval (veluPointX (A + B))
      ∧ ∀ P : W.Point, P ∉ S →
          (∏ Q ∈ S, (veluPointY (P + Q)
            - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
                * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
            = c * (W.veluCoordY S P - (lam * W.veluCoordX S P + mu)) := by
  classical
  set V := W.veluCurve S with hV
  set κ := (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
      * (veluH S).eval (veluPointX (A + B)) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact veluH_eval_ne_zero hS hA
    · exact veluH_eval_ne_zero hS hB
    · exact veluH_eval_ne_zero hS hAB
  obtain ⟨a, b, hab⟩ := velu_norm_line_eq_poly W S hS hodd (veluPointX A) (veluPointY A)
    (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B))
  -- The three polynomials of the degree argument: `AA` completes the square, `Φ_V` is
  -- `(2Y + A₁X + A₃)²` reduced by the Weierstrass equation of `V`, and `ρ` is `STAR`'s cubic.
  set AA : Polynomial F :=
    Polynomial.C (2 : F) * a - b * (Polynomial.C V.a₁ * Polynomial.X + Polynomial.C V.a₃) with hAA
  set ΦV : Polynomial F :=
    Polynomial.C (4 : F) * Polynomial.X ^ 3
      + Polynomial.C (4 * V.a₂ + V.a₁ ^ 2) * Polynomial.X ^ 2
      + Polynomial.C (4 * V.a₄ + 2 * V.a₁ * V.a₃) * Polynomial.X
      + Polynomial.C (4 * V.a₆ + V.a₃ ^ 2) with hΦV
  set ρ : Polynomial F :=
    (Polynomial.X - Polynomial.C (W.veluCoordX S A))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
      * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B))) with hρ
  set D : Polynomial F := AA ^ 2 - b ^ 2 * ΦV + Polynomial.C (4 * κ) * ρ with hD
  -- `D` vanishes at every admissible Vélu `x`-coordinate: this is `STAR` after `POLY` has
  -- been substituted at `P` and at `−P`, with `Y²` eliminated by `velu_equation` on `V`.
  have hDval : ∀ P : W.Point, P ∉ S → D.eval (W.veluCoordX S P) = 0 := by
    intro P hP
    have hnP : -P ∉ S := fun hc => hP (by simpa using hS.neg_mem _ hc)
    have h1 := hab P hP
    have h2 := hab (-P) hnP
    rw [veluCoordX_neg hS P, veluCoordY_neg hS hP] at h2
    have h3 := velu_norm_line_mul_neg_slope W S hS hodd hA hB hAB hP
    rw [h1, h2] at h3
    have h4 := W.velu_equation S hS hodd hP
    rw [Affine.equation_iff] at h4
    simp only [hD, hAA, hΦV, hρ, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Affine.negY] at h3 h4 ⊢
    linear_combination (4 : F) * h3 + 4 * (b.eval (W.veluCoordX S P)) ^ 2 * h4
  -- Infinitely many distinct evaluation points promote that to a polynomial identity.
  have hD0 : D = 0 := by
    obtain ⟨t, hcard, hw⟩ := velu_exists_coordX_values W S hS hodd (D.natDegree + 1)
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D t ?_ (by omega)
    intro ξ hξ
    obtain ⟨P, hP, rfl⟩ := hw ξ hξ
    exact hDval P hP
  have hkey : AA ^ 2 - b ^ 2 * ΦV = Polynomial.C (-(4 * κ)) * ρ := by
    have h := hD0
    rw [hD] at h
    rw [map_neg, neg_mul, ← sub_eq_zero]
    linear_combination h
  -- The degree count.  `deg (AA²)` is EVEN and `deg (b²Φ_V) = 2·deg b + 3` is ODD, so
  -- nothing cancels and the maximum is the degree `3` of the right-hand side.
  have hρmonic : ρ.Monic := by
    rw [hρ]
    exact ((Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _)).mul
      (Polynomial.monic_X_sub_C _)
  have hρdeg : ρ.natDegree = 3 := by rw [hρ]; compute_degree!
  have hrhsdeg : (Polynomial.C (-(4 * κ)) * ρ).natDegree = 3 := by
    rw [Polynomial.natDegree_C_mul (by simpa using hκ0), hρdeg]
  have hΦdeg : ΦV.natDegree = 3 := by rw [hΦV]; compute_degree!
  have hΦ0 : ΦV ≠ 0 := fun h => by simp [h] at hΦdeg
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb] at hkey
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero] at hkey
    have h := congrArg Polynomial.natDegree hkey
    rw [Polynomial.natDegree_pow, hrhsdeg] at h
    omega
  have hbΦdeg : (b ^ 2 * ΦV).natDegree = 2 * b.natDegree + 3 := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ hb0) hΦ0, Polynomial.natDegree_pow, hΦdeg]
  have hAAdeg : (AA ^ 2).natDegree = 2 * AA.natDegree := Polynomial.natDegree_pow _ _
  have hlt : (AA ^ 2).natDegree < (b ^ 2 * ΦV).natDegree := by
    rcases lt_trichotomy ((AA ^ 2).natDegree) ((b ^ 2 * ΦV).natDegree) with h | h | h
    · exact h
    · rw [hAAdeg, hbΦdeg] at h; omega
    · exfalso
      have h' : (AA ^ 2 - b ^ 2 * ΦV).natDegree = (AA ^ 2).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt h
      rw [hkey, hrhsdeg, hAAdeg] at h'
      omega
  have hbdeg : b.natDegree = 0 := by
    have h := Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
    have h2 : (b ^ 2 * ΦV - AA ^ 2).natDegree = 3 := by
      rw [show b ^ 2 * ΦV - AA ^ 2 = -(AA ^ 2 - b ^ 2 * ΦV) by ring, Polynomial.natDegree_neg,
        hkey, hrhsdeg]
    rw [h2, hbΦdeg] at h
    omega
  have hAAle : AA.natDegree ≤ 1 := by
    have h := hlt
    rw [hAAdeg, hbΦdeg, hbdeg] at h
    omega
  -- `b` is the constant `c`, and comparing the `T³` coefficients gives `c² = κ`.
  obtain ⟨β, hβ⟩ : ∃ β : F, b = Polynomial.C β :=
    ⟨b.coeff 0, (Polynomial.eq_C_of_natDegree_eq_zero hbdeg)⟩
  have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 (by simpa using hβ)
  have hρ3 : ρ.coeff 3 = 1 := by
    have h' := hρmonic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hρdeg] at h'
    exact h'
  have hβκ : β ^ 2 = κ := by
    have h : (AA ^ 2 - b ^ 2 * ΦV).coeff 3 = (Polynomial.C (-(4 * κ)) * ρ).coeff 3 := by rw [hkey]
    have hA3 : (AA ^ 2).coeff 3 = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hAAdeg]; omega)
    have hΦ3 : ΦV.coeff 3 = 4 := by
      rw [hΦV]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [Polynomial.coeff_sub, hA3, hβ, ← Polynomial.C_pow, Polynomial.coeff_C_mul, hΦ3,
      Polynomial.coeff_C_mul, hρ3] at h
    linear_combination (-4⁻¹ : F) * h
  -- `λ` and `μ` are the two coefficients of the linear polynomial `AA`.
  obtain ⟨α₁, α₀, hAAeq⟩ : ∃ α₁ α₀ : F, AA = Polynomial.C α₁ * Polynomial.X + Polynomial.C α₀ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hAAle
  have hAAeq' : Polynomial.C (2 : F) * a
        - b * (Polynomial.C V.a₁ * Polynomial.X + Polynomial.C V.a₃)
      = Polynomial.C α₁ * Polynomial.X + Polynomial.C α₀ := by rw [← hAA]; exact hAAeq
  have haeq : ∀ ξ : F, (2 : F) * a.eval ξ - β * (V.a₁ * ξ + V.a₃) = α₁ * ξ + α₀ := by
    intro ξ
    have h := congrArg (Polynomial.eval ξ) hAAeq'
    rw [hβ] at h
    simpa using h
  refine ⟨β, -(α₁ + β * V.a₁) / (2 * β), -(α₀ + β * V.a₃) / (2 * β), hβκ, ?_⟩
  intro P hP
  have ha : a.eval (W.veluCoordX S P)
      = (α₁ * W.veluCoordX S P + α₀ + β * (V.a₁ * W.veluCoordX S P + V.a₃)) / 2 := by
    field_simp
    linear_combination haeq (W.veluCoordX S P)
  rw [hab P hP, hβ]
  simp only [Polynomial.eval_C]
  rw [ha]
  field_simp
  ring

/-- **THE ODD-ORDER VÉLU `addX` IDENTITY, and since 2026-07-27 it carries NO sorried step of
its own**: the one remaining leaf underneath it is `POLY` (`velu_norm_line_eq_poly`), which
is now a named top-level declaration rather than an anonymous sorried `obtain` here.

`velu_addX_eq_of_norm_line` above is the finish — it consumes `STAR`
(`velu_norm_line_mul_neg_slope`) and needs only `HNORM` plus three evaluation points.  This
theorem runs it over `AlgebraicClosure F` and descends through `velu_bc_coordX` /
`velu_bc_coordY` and the rest of the base-change family.

**Why the algebraic closure is not optional.** Over `F` the three evaluation points can
genuinely FAIL to exist: take `A` of order `3` modulo `S`, `B ≡ A`, and `W(F) = ⟨A⟩ + S`;
then `A, B, A + B ∉ S` all hold, every admissible `P` has `X P = X A`, and the conclusion
(`3·ψA = 0`, true because `3A ∈ S`) is invisible to the argument.  Over `F̄` they exist —
that is `velu_exists_three_coordX`, PROVEN above off `velu_exists_point_notMem` (complete
the square, take a square root, and the field is infinite) and
`velu_pointX_mem_of_coordX_eq` (the fibres of the Vélu `x`-coordinate are contained in the
`|S|` values `x(P + Q)`, read off `velu_xNum_sub_eq_prod`).

**`HNORM` is now PROVEN** (`velu_hnorm`, above): the sorried `obtain` that used to sit in
the body below is an ordinary application.  It says the norm `N(P) = ∏_{Q ∈ S} f(P+Q)` of
the secant line function is again a LINE function `c·(Y − λX − μ)` on the quotient, with
`c² = κ = H(x_A)H(x_B)H(x_C)`.  **The LINE shape and the relation `c² = κ` are no longer
assumed**: they are derived from the strictly weaker leaf `POLY`
(`velu_norm_line_eq_poly` — "the norm lies in `F[X] ⊕ F[X]·Y`") together with `STAR` and a
parity-of-degrees argument, which is what removed the sign question entirely.  See the
section docstring above `velu_exists_coordX_values` for the derivation.

The four refuted routes recorded in `velu_map_add_of_notMem`'s ROUTE MAP (`Ideal.relNorm`;
the even/odd split of `N`; any pairing of `N` against `N ∘ [−1]`; `Affine.Point.toClass` /
`ClassGroup`) still stand and should not be re-attempted **against `POLY`** — they were all
searched along the multiplicative axis, which the section docstring above shows to be closed
for a sharp reason.  That docstring also records the one OPEN axis (an additive identity
that is not a consequence of `STAR`) together with the explicit check that would refute
`POLY`'s irreducibility along it. -/
theorem velu_coordX_add_eq_addX (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S) :
    W.veluCoordX S (A + B)
      = (W.veluCurve S).addX (W.veluCoordX S A) (W.veluCoordX S B)
          ((W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
            (W.veluCoordY S A) (W.veluCoordY S B)) := by
  classical
  haveI : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  set A' := veluBaseChangePoint W (AlgebraicClosure F) A
  set B' := veluBaseChangePoint W (AlgebraicClosure F) B
  set S' : Finset (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    S.image (veluBaseChangePoint W (AlgebraicClosure F)) with hS'def
  have hS' : IsPointSubgroup S' := velu_baseChange_isPointSubgroup hS
  have hodd' : Odd S'.card := by
    rw [hS'def, Finset.card_image_of_injective _ veluBaseChangePoint_injective]; exact hodd
  have hmem : ∀ P : W.Point, P ∉ S →
      veluBaseChangePoint W (AlgebraicClosure F) P ∉ S' := by
    intro P hP hcon
    rw [hS'def, Finset.mem_image] at hcon
    obtain ⟨Q, hQ, hQeq⟩ := hcon
    exact hP (veluBaseChangePoint_injective hQeq ▸ hQ)
  have hsum : A' + B' = veluBaseChangePoint W (AlgebraicClosure F) (A + B) := (map_add _ _ _).symm
  -- **HNORM**, PROVEN above (`velu_hnorm`) off the leaf `POLY` (`velu_norm_line_eq_poly`):
  -- the norm along `S` of a line function on `W` is again a LINE function on the quotient
  -- curve, with `c² = κ`.  Both the line shape and `c² = κ` are derived, not assumed.
  obtain ⟨c, lam, mu, hc, hN⟩ :
      ∃ c lam mu : AlgebraicClosure F,
        c ^ 2 = (veluH S').eval (veluPointX A') * (veluH S').eval (veluPointX B')
            * (veluH S').eval (veluPointX (A' + B'))
        ∧ ∀ P : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point, P ∉ S' →
            (∏ Q ∈ S', (veluPointY (P + Q)
              - ((W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).slope
                    (veluPointX A') (veluPointX B') (veluPointY A') (veluPointY B')
                  * (veluPointX (P + Q) - veluPointX A') + veluPointY A')))
              = c * ((W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordY S' P
                  - (lam * (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P
                      + mu)) :=
    velu_hnorm (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS' hodd'
      (hmem A hA) (hmem B hB) (hsum ▸ hmem (A + B) hAB)
  -- Three admissible points with pairwise distinct Vélu `x`-coordinates.  Over `F` this can
  -- genuinely fail; over the algebraic closure it does not, which is why the whole argument
  -- is run there and descended.
  obtain ⟨P₀, P₁, P₂, hP₀, hP₁, hP₂, h01, h02, h12⟩ :
      ∃ P₀ P₁ P₂ : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point,
        P₀ ∉ S' ∧ P₁ ∉ S' ∧ P₂ ∉ S'
        ∧ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₀
            ≠ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₁
        ∧ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₀
            ≠ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₂
        ∧ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₁
            ≠ (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).veluCoordX S' P₂ :=
    velu_exists_three_coordX (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS' hodd'
  have key := velu_addX_eq_of_norm_line
    (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS' hodd'
    (hmem A hA) (hmem B hB) (hsum ▸ hmem (A + B) hAB) hc hN hP₀ hP₁ hP₂ h01 h02 h12
  rw [hsum, velu_bc_coordX, velu_bc_coordX, velu_bc_coordX,
    velu_bc_coordY, velu_bc_coordY, ← velu_baseChange_curve,
    show ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F))
        = (W.veluCurve S).map (algebraMap F (AlgebraicClosure F)) from rfl,
    Affine.map_slope, Affine.map_addX] at key
  exact (algebraMap F (AlgebraicClosure F)).injective key


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

**THE COMPUTABLE HALF IS NOW PROVEN (2026-07-26, third owner), AND IT IS SIGN-BLIND.** The
companion

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
`XNum(x_T)` into `H(x_T)·X T`) gives STAR; all the sign powers of `(−1)^n` cancel.

That is now DONE, and it came in at the low end of the estimate. STAR is
`velu_norm_line_mul_neg` (general line, hypothesis `hfac` supplying the factorization, so
the TANGENT case is covered too) and `velu_norm_line_mul_neg_slope` (the secant through `A`
and `B`), just above this docstring, off the four bricks `velu_addPolynomial_eval`,
`velu_prod_neg`, `velu_line_pair` and `velu_fibre_prod_sub` / `velu_fibre_prod_sub_point`.
Every one of them is `[propext, Classical.choice, Quot.sound]`. STAR was verified in the
same PARI sweep.

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

## WITH STAR PROVEN: THE ASSEMBLY FROM HNORM IS ~40 LINES, NOT A COEFFICIENT COMPARISON

(2026-07-26, third owner.) The coefficient-comparison finish sketched above works, but it is
not the cheap one, and it is what forces the case split on collisions. Write `V` for
`veluCurve W S` and suppose `HNORM` holds for the secant through `A`, `B`, with constants
`c, λ, μ` and `c² = κ`. Then:

1. `c ≠ 0`, because `κ ≠ 0` by `veluH_eval_ne_zero` at `A`, `B`, `A + B`, all outside `S`.
2. `N` vanishes at `A`, at `B` and at `−(A + B)`: in each case the `Q = 0` factor of the
   product is the line function at a point lying ON the line. With `c ≠ 0`, HNORM turns
   that into `Y T = λ · X T + μ` for those three `T`; `veluCoordX_neg` and `veluCoordY_neg`
   move the third one from `−(A + B)` to `A + B`.
3. Substituting HNORM into STAR, and applying `velu_line_pair` ON `V` at the point `ψP` —
   whose coordinates are `(X P, Y P)` by `veluMap_of_notMem`, and whose negative has
   coordinates given by `veluCoordX_neg` / `veluCoordY_neg` — cancels `c² = κ ≠ 0` and
   leaves, for EVERY `P ∉ S`,

     `(V.addPolynomial (X A) (Y A) λ).eval (X P) = −(X P − X A)(X P − X B)(X P − X (A+B))`.

4. `λ` is `V.slope (X A) (X B) (Y A) (Y B)`: step 2 gives it when `X A ≠ X B`, and the
   nondegeneracy side condition `¬(X A = X B ∧ Y A = V.negY (X B) (Y B))` is already proven
   here — it is `velu_coord_ne_neg`.
5. So `addPolynomial_slope` ON `V` factors the left side as
   `−(ξ − X A)(ξ − X B)(ξ − V.addX (X A) (X B) λ)`, and the two cubics differ by a product
   that collapses: `−(ξ−a)(ξ−b)(ξ−u) + (ξ−a)(ξ−b)(ξ−v) = (ξ−a)(ξ−b)(u−v)`. Hence

     `(X P − X A)(X P − X B) · (V.addX (X A) (X B) λ − X (A+B)) = 0`  for every `P ∉ S`.

6. ONE point `P ∉ S` with `X P ≠ X A` and `X P ≠ X B` therefore finishes it, and
   `V.addX (X A) (X B) λ = X (A+B)` IS the leaf, in the exact form that
   `velu_map_add_of_coordX` consumes.

No cubic-coefficient comparison, no degree count, and NO separate treatment of the
degenerate subcase.

**The only remaining gap besides HNORM is that one auxiliary point, and it is real.** Step 6
needs `P` outside the five cosets `S`, `±A + S`, `±B + S`. Over `F̄` that is free; over `F`
it can genuinely fail. Take `A` of order `3` modulo `S`, `B ≡ A`, and `W(F) = ⟨A⟩ + S`: then
`A, B, A + B ∉ S` all hold, every admissible `P` has `X P = X A`, and the conclusion
(`3·ψA = 0`, true because `3A ∈ S`) is invisible to this argument. So the finish is: base
change to `F̄`, apply there, descend by injectivity of `veluBaseChangePoint`. The
base-change lemmas for `H`, `XNum`, `Xi`, `Theta`, `T`, `W`, the curve and
`IsPointSubgroup` are all already in this file; the ONE that is missing is for `veluCoordX`
itself, and it should be a short `Finset.prod`/`sum` reindexing off
`veluBaseChangePoint_pointX`.

**Collisions all reduce to DOUBLING** (recorded so it need not be rederived). `X A = X B`
forces `A ≡ B mod S`, since `A ≡ −B` is excluded by `A + B ∉ S`, so the claim is
`ψ(2A) = 2ψA`; `X A = X C` forces `2A + B ∈ S`, i.e. `B ≡ −2A`, and the claim is again
`ψ(2A) = 2ψA`; `X B = X C` forces `A + 2B ∈ S`, the same statement at `B`. So the collision
cases carry EXACTLY the duplication content — which is why the collinearity restatement,
being blind to multiplicity, is vacuous precisely there.

**Why HNORM is irreducible, and the check that would refute that.** `N` is `S`-invariant by
construction (reindex the product), so HNORM says exactly that an `S`-invariant function
lies in `F(X, Y)` — the invariant-function theorem for `F(W)` over `F(W)^S`. Two cheaper
attempts were tried here and both fail for a structural reason: STAR determines `N` only up
to sign, and no identity pairing `N` against `N∘[−1]` can supply it, because every such
identity is EVEN; and splitting `N` into even and odd parts does not help either, since the
odd part is the half carrying the content and it is a PRODUCT that would have to be shown
proportional to a SUM. The refuting check, for anyone who believes otherwise: exhibit
`Σ_{Q∈S} u(x(P+Q))·y(P+Q)` as an explicit expression in `X P` and `Y P` for a single `u`
other than `u = 1`. Vélu's `Y` is precisely the `u = 1` case, and it is a DEFINITION, not a
theorem.

**Absence re-checked 2026-07-26.** `grep -ril 'isogeny\|RiemannRoch'` over
`Mathlib/AlgebraicGeometry` and `Mathlib/NumberTheory` returns NOTHING, and the same over
`~/cs/FLT` returns nothing. `Mathlib/AlgebraicGeometry/EllipticCurve/` holds only
`Affine/{AddSubMap,Basic,Formula,Point}`, `DivisionPolynomial`, `Jacobian`, `Projective`,
`IsomOfJ`, `LFunction`, `ModelsWithJ`, `NormalForms`, `Reduction`, `VariableChange`,
`Weierstrass`. So the norm/pushforward has to be built here; the Abel–Jacobi half
(`toClass`, `FunctionField`, `CoordinateRing`) is the part mathlib does supply.

## STATUS UPDATE 2026-07-27 — THIS DECLARATION NO LONGER CONTAINS A SORRY

Everything above is the ROUTE MAP as it stood when this was a bare `sorry`. It has now been
executed. The `have hX` below is discharged by `velu_coordX_add_eq_addX`, and the chain
from here down to the one remaining gap is:

* `velu_addX_eq_of_norm_line` — the ~40-line assembly the section "WITH STAR PROVEN"
  above predicted, PROVEN. It consumes `STAR` (`velu_norm_line_mul_neg_slope`), which was
  free-floating until now. Its steps 1–6 are exactly the ones listed above, with one
  addition the sketch omitted: step 4 (`λ` IS `V.slope`) does NOT follow from the line
  relations in the TANGENT case `X A = X B`; it is read off the `ξ`-COEFFICIENT of the
  cubic identity instead, which is why the polynomial identity is taken first and the
  coefficient comparison is not avoidable after all. Both needed coefficients come from
  `Cubic.b_of_eq` / `Cubic.c_of_eq`.
* `velu_coordX_add_eq_addX` — runs that over `AlgebraicClosure F` and descends. The
  auxiliary-point gap flagged above ("the ONE that is missing is for `veluCoordX` itself")
  is closed: `velu_bc_coordX` / `velu_bc_coordY` are PROVEN, and the three points
  themselves are `velu_exists_three_coordX`, PROVEN.
* **`HNORM` is PROVEN since 2026-07-27** (`velu_hnorm`), and the sorried `obtain` inside
  `velu_coordX_add_eq_addX` is gone. It comes off a strictly weaker leaf,
  **`POLY` (`velu_norm_line_eq_poly`)**: "the norm of a line function lies in the coordinate
  ring `F[X] ⊕ F[X]·Y` of the quotient". The LINE shape, the constancy of `c`, and `c² = κ`
  are all DERIVED from `POLY` + `STAR` by a parity-of-degrees argument — `deg(AA²)` is even,
  `deg(b²Φ_V) = 2·deg b + 3` is odd, so they cannot cancel and the right-hand side's degree
  `3` pins both. In particular **no pole count at `O` and no Riemann–Roch input is needed**,
  which is where the earlier route map expected the degree bound to come from.
* **`POLY` is the single remaining leaf of the odd-order development.** The four refutations
  recorded above still stand against it and should not be re-attempted: all four range over
  the MULTIPLICATIVE axis, which is closed because the functions whose norm is computable
  from the fibre polynomial are exactly the EVEN ones (`∏_{Q∈S} g(x(P+Q))` factors through
  `velu_fibre_prod_sub` at each root of `g`), and `f·(f∘[−1])` is the only even combination
  a slanted line admits — that combination being `STAR` itself. The axis that is OPEN is the
  ADDITIVE one; see the section docstring above `velu_exists_coordX_values` for the one
  non-`STAR` odd identity found so far and the explicit check that would refute
  irreducibility along it. -/
theorem velu_map_add_of_notMem (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  -- Goal (1): PROVEN (`velu_coord_ne_neg`), and it is exactly the nondegeneracy `hz`.
  have hz : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluMap S hS hodd A + W.veluMap S hS hodd B ≠ 0 := fun A B hA hB hAB =>
    velu_map_add_ne_zero W S hS hodd hA hB (W.velu_coord_ne_neg S hS hodd hA hB hAB)
  -- Goal (2), the `addX` identity in point form.  Since 2026-07-27 this is no longer a
  -- bare `sorry`: it is `velu_coordX_add_eq_addX` above, whose own remaining content is
  -- HNORM ALONE, stated over `AlgebraicClosure F`.
  have hX : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluCoordX S (A + B)
        = veluPointX (W.veluMap S hS hodd A + W.veluMap S hS hodd B) := by
    intro A B hA hB hAB
    rw [W.veluMap_of_notMem hS hodd hA, W.veluMap_of_notMem hS hodd hB,
      Affine.Point.add_some (W.velu_coord_ne_neg S hS hodd hA hB hAB)]
    exact W.velu_coordX_add_eq_addX S hS hodd hA hB hAB
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
already work at even order. Do not re-cut it.

**The COORDINATE IDENTIFICATION is now part of the conclusion** (added 2026-07-27).
The final conjunct pins `φ` pointwise off the kernel: for `Pt ∉ C` the image
`φ Pt` is the affine point whose coordinates are literally Vélu's sums,
`veluPointX (φ Pt) = veluCoordX … Pt` and `veluPointY (φ Pt) = veluCoordY … Pt`.
Without it the theorem exhibits `φ` only up to its kernel and its equivariance,
which is not enough to apply the `IsRationalMap` bridge of
`Fermat/FLT/EllipticCurve/Isogeny.lean` at the call site — the bridge's
certificate is written in `veluXNum` / `veluH` / `veluXi`, and it needs to know
that `φ`'s coordinates are the Vélu ones. -/
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
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, Pt ∉ C →
        veluPointX (φ Pt) =
            veluCoordX (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset Pt ∧
          veluPointY (φ Pt) =
            veluCoordY (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset Pt) := by
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
        rw [velu_map_add _ S hS hodd P Q, map_add]), ht, hw, ?_, ?_, ?_⟩
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
  · -- the coordinate identification off the kernel
    intro Pt hPt
    have hPtS : Pt ∉ S := fun hc => hPt ((hmem Pt).mp hc)
    show veluPointX (ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd Pt)) =
          veluCoordX (E⁄(AlgebraicClosure ℚ)) S Pt ∧
        veluPointY (ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd Pt)) =
          veluCoordY (E⁄(AlgebraicClosure ℚ)) S Pt
    rw [veluMap_of_notMem _ hS hodd hPtS, hψdef, pointAddEquivOfEq_some]
    exact ⟨rfl, rfl⟩

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
  obtain ⟨t, w, hell, φ, -, -, hgal, hker, -⟩ :=
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

### STATUS 2026-07-27 — the whole `PolePoly` re-derivation is DONE

The `PolePoly` re-derivation predicted above was carried out; it lives in the two sections
`PolePolyAllOrders` / `PolePolyAllOrdersChar` immediately below this note. **All three
polynomial leaves are now PROVEN** — `velu_thetaAll_local_dvd`, `velu_thetaAll_key_over` and
`velu_thetaAll_degree_lt` — so `veluThetaAll S = 0` holds at EVERY kernel order and the
parity dependence of the pole layer is GONE. The only leaf left in the parity-free path is
`velu_exists_three_twoTorsion_of_subgroup`, which is not a polynomial statement at all.

The `2`-torsion obstruction `velu_thetaAll_local_dvd` was blocked on is resolved by
`velu_genN_eq_genD_mul`; `velu_thetaAll_key_over` is the mechanical mirror of
`velu_theta_key_over` over it.

* `velu_equation_of_subgroup` — **PROVEN**, over `velu_equation_pole_of_subgroup` ←
  `velu_pole_identity_of_subgroup` ← `velu_thetaAll_eq_zero` ← the two polynomial leaves.
* `velu_isElliptic_of_subgroup` — **PROVEN**, over
  `velu_exists_three_twoTorsion_of_subgroup`, which is itself now PROVEN (2026-07-27) over
  the single new leaf `velu_curve_Δ_ne_zero` (`Δ (veluCurve W S) ≠ 0`). That leaf carries a
  COMPLETE elementary route in its docstring — a Wronskian/multiplicity argument over the
  identity `Ψ·Ξ² = H·Φnum` — replacing the earlier audit, which sent the reader at points of
  order `4` and at the quotient's group law, neither of which is needed or available.
* `velu_map_add_of_subgroup` — **PROVEN 2026-07-27**, over the two leaves
  `velu_coord_ne_neg_of_subgroup` and `velu_coordX_add_eq_addX_of_subgroup` cut beside it.
  The note this replaces said it was BLOCKED on the odd-order `velu_map_add_of_notMem`;
  that is now stale twice over — `velu_map_add_of_notMem` is PROVEN (its last leaf `POLY`
  closed the same day), and in any case the formal half of the arbitrary-order reduction
  never needed the odd-order theorem, only its SHAPE, which mirrors with `hodd` deleted.

Axiom-clean and standalone (`[propext, Classical.choice, Quot.sound]`, verified against the
built module 2026-07-27): `veluH_factor_all`, `velu_fiber_card_all`, `veluH_pow_eq_all`,
`veluUTerm_eq_zero_of_neg_eq`, `veluTTerm_ne_zero_of_neg_eq`, `veluPXAll_eval`,
`veluPVAll_eval`, `veluXNumAll_eval`, `veluXiAll_eval`, `veluPhiNumAll_eval`,
`velu_thetaAll_dvd`.

**Two corrections to the audit above.** (1) The prediction that `veluPX`/`veluPV` must
change was right, and the corrected exponents are `ε_Q` on the `t_Q` summand of `veluPXAll`
and `2ε_Q` on the `t_Q` summand of `veluPVAll` (the audit named only the first). (2) The
prediction that `velu_theta_local_dvd` and the degree count "re-derive with the changed
degree count" understates the local half: at a `2`-torsion `T` BOTH inputs of the odd-order
contradiction degenerate (`u_T = 0` makes `veluGenN` evaluate to `0`, not just `veluH`
factor differently), and the repair needs the new coordinate-ring identity recorded in
`velu_thetaAll_local_dvd`'s docstring. The degree half does re-derive as predicted.
-/

section PolePolyAllOrders

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- `ε_Q = 0` if `Q` is `2`-torsion, `1` otherwise. This is the exponent that makes every
statement of the `PolePoly` section parity-free: `Q` and `−Q` are two distinct points of the
kernel exactly when `ε_Q = 1`, and the pole of Vélu's expansion at `x_Q` has order `1 + ε_Q`
in `x`. -/
def veluEps (Q : W.Point) : ℕ := if -Q = Q then 0 else 1

lemma veluEps_of_twoTorsion {Q : W.Point} (h : -Q = Q) : veluEps Q = 0 := if_pos h

lemma veluEps_of_not_twoTorsion {Q : W.Point} (h : -Q ≠ Q) : veluEps Q = 1 := if_neg h

/-- **PROVEN: the parity-free factorisation of `veluH`**, replacing the FALSE
`veluH_factor` in the even case. A nonzero `Q` of the subgroup `S` contributes the linear
factor `(T − x_Q)` to `veluH S` twice when `−Q ≠ Q` and only ONCE when `Q` is `2`-torsion;
`veluHq S Q` erases `Q` and then `−Q`, and at a `2`-torsion point that second erase is
idempotent, which is exactly why the uniform exponent `1 + ε_Q` is correct. -/
lemma veluH_factor_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    veluH S = (Polynomial.X - Polynomial.C (veluPointX Q)) ^ (1 + veluEps Q) * veluHq S Q := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
  have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
  rcases eq_or_ne (-Q) Q with h2 | h2
  · rw [veluEps_of_twoTorsion h2, veluH, ← Finset.mul_prod_erase _ _ hQ, veluHq, h2,
      Finset.erase_idem]
    ring
  · have h1 : -Q ∈ (S.erase 0).erase Q :=
      Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
    rw [veluEps_of_not_twoTorsion h2, veluH, ← Finset.mul_prod_erase _ _ hQ,
      ← Finset.mul_prod_erase _ _ h1, veluHq, velu_pointX_neg]
    ring

/-- **PROVEN.** The fibre of `veluPointX` over `x_Q` inside `S ∖ {0}` has `1 + ε_Q`
elements: `{Q, −Q}` collapses to a singleton exactly at a `2`-torsion point. -/
lemma velu_fiber_card_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    ({Q' ∈ S.erase 0 | veluPointX Q' = veluPointX Q}).card = 1 + veluEps Q := by
  rw [velu_fiber hS hQ]
  rcases eq_or_ne (-Q) Q with h2 | h2
  · rw [veluEps_of_twoTorsion h2, h2]
    simp
  · rw [veluEps_of_not_twoTorsion h2,
      Finset.card_insert_of_notMem (by simpa using fun h => h2 h.symm), Finset.card_singleton]

/-- **PROVEN, parity-free.** `veluH⁴ = ∏_a (T − a)^{4·|fibre(a)|}` over the DISTINCT roots.
No parity hypothesis is needed at all: the exponent simply records the fibre size, which is
`2` at an ordinary `±`-pair and `1` at a `2`-torsion point. This is the parity-free form of
`veluH_pow_eq`, whose uniform exponent `8` is what the odd case's `hodd` bought. -/
lemma veluH_pow_eq_all (S : Finset W.Point) :
    (veluH S) ^ 4
      = ∏ a ∈ (S.erase 0).image veluPointX,
          (Polynomial.X - Polynomial.C a)
            ^ (4 * ({Q' ∈ S.erase 0 | veluPointX Q' = a}).card) := by
  rw [veluH, ← Finset.prod_pow, ← Finset.prod_fiberwise_of_maps_to
    (g := veluPointX) (t := (S.erase 0).image veluPointX)
    (fun i hi => Finset.mem_image_of_mem _ hi)
    (fun Q => (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 4)]
  refine Finset.prod_congr rfl fun a _ => ?_
  calc ∏ Q' ∈ {Q' ∈ S.erase 0 | veluPointX Q' = a},
        (Polynomial.X - Polynomial.C (veluPointX Q')) ^ 4
      = ∏ _Q' ∈ {Q' ∈ S.erase 0 | veluPointX Q' = a}, (Polynomial.X - Polynomial.C a) ^ 4 :=
        Finset.prod_congr rfl fun Q' hQ' => by rw [(Finset.mem_filter.mp hQ').2]
    _ = ((Polynomial.X - Polynomial.C a) ^ 4)
          ^ ({Q' ∈ S.erase 0 | veluPointX Q' = a}).card := by rw [Finset.prod_const]
    _ = _ := by rw [← pow_mul]

end PolePolyAllOrders

section PolePolyAllOrdersChar

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] {W : Affine F}

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN.** At a `2`-torsion point Vélu's `u`-term vanishes: `u_Q = (g^y_Q)²` and
`g^y_Q = 2y + a₁x + a₃` is exactly the condition `−Q = Q`. This is the fact that makes the
whole coefficient layer (`veluT`, `veluW`, `veluCurve`) already correct at even order. -/
lemma veluUTerm_eq_zero_of_neg_eq {Q : W.Point} (h : -Q = Q) : veluUTerm W Q = 0 := by
  cases Q with
  | zero => rfl
  | some x y hns =>
      have hy : W.negY x y = y := by
        have h2 := congrArg veluPointY h
        rw [Affine.Point.neg_some] at h2
        exact h2
      have hv : 2 * y + W.a₁ * x + W.a₃ = 0 := by
        simp only [Affine.negY] at hy; linear_combination -hy
      rw [veluUTerm_some, hv]
      ring

omit [DecidableEq F] in
/-- **PROVEN.** At a `2`-torsion point of a NONSINGULAR Weierstrass curve, Vélu's `t`-term
is NONZERO. Indeed `t_Q = 2 g^x_Q + a₁ g^y_Q` in general and `g^y_Q = 0` here, so
`t_Q = 2 g^x_Q`; and a point with `g^x_Q = g^y_Q = 0` would be a singular point.

This is the replacement, at a `2`-torsion kernel point, for the nonvanishing of `u_Q` that
the odd-order local-divisibility argument uses: it is what keeps the evaluation of the
cleared translate nonzero. -/
lemma veluTTerm_ne_zero_of_neg_eq {Q : W.Point} (hQ : Q ≠ 0) (h : -Q = Q) :
    veluTTerm W Q ≠ 0 := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y hns =>
      have hy : W.negY x y = y := by
        have h2 := congrArg veluPointY h
        rw [Affine.Point.neg_some] at h2
        exact h2
      have hv : 2 * y + W.a₁ * x + W.a₃ = 0 := by
        simp only [Affine.negY] at hy; linear_combination -hy
      rcases hns.2 with hX | hY
      · rw [Affine.evalEval_polynomialX] at hX
        rw [veluTTerm_some]
        intro hc
        refine hX ?_
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄] at hc
        linear_combination -(hc / 2) + (W.a₁ / 2) * hv
      · rw [Affine.evalEval_polynomialY] at hY
        exact absurd hv hY

/-- Numerator of `Σ_{Q ∈ S} veluPoleX` over `veluH`, at EVERY kernel order. The `t_Q`
summand carries the factor `(T − x_Q)^{ε_Q}`, which is absent at a `2`-torsion point
precisely because the pole there is SIMPLE; the `u_Q` summand needs no correction because
`u_Q = 0` there (`veluUTerm_eq_zero_of_neg_eq`). At odd order this is `veluPX`. -/
noncomputable def veluPXAll (S : Finset W.Point) : Polynomial F :=
  ∑ Q ∈ S.erase 0,
    (Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
      + Polynomial.C (veluUTerm W Q)) * veluHq S Q

/-- Numerator of `Σ_{Q ∈ S} veluPoleV` over `veluH²`, at EVERY kernel order; the `t_Q`
summand carries `(T − x_Q)^{2ε_Q}`. At odd order this is `veluPV`. -/
noncomputable def veluPVAll (S : Finset W.Point) : Polynomial F :=
  ∑ Q ∈ S.erase 0,
    (Polynomial.C (veluUTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
      + Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
          * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ (2 * veluEps Q))
    * (veluHq S Q) ^ 2

/-- `veluH² · (1 − D)`, at EVERY kernel order. -/
noncomputable def veluXiAll (S : Finset W.Point) : Polynomial F := (veluH S) ^ 2 - veluPVAll S

/-- `veluH · X`, at EVERY kernel order. -/
noncomputable def veluXNumAll (S : Finset W.Point) : Polynomial F :=
  Polynomial.X * veluH S + Polynomial.C ((2 : F)⁻¹) * veluPXAll S

/-- `veluH³ · Φ(X)`, at EVERY kernel order. -/
noncomputable def veluPhiNumAll (S : Finset W.Point) : Polynomial F :=
  Polynomial.C (4 : F) * (veluXNumAll S) ^ 3
    + Polynomial.C W.b₂ * (veluXNumAll S) ^ 2 * veluH S
    + Polynomial.C (2 * W.b₄ - 20 * W.veluT S) * veluXNumAll S * (veluH S) ^ 2
    + Polynomial.C (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S) * (veluH S) ^ 3

/-- `Θ = Ψ·Ξ² − H·Φ_num`, at EVERY kernel order. The whole remaining content of Vélu's
theorem for an arbitrary kernel is `veluThetaAll S = 0`. -/
noncomputable def veluThetaAll (S : Finset W.Point) : Polynomial F :=
  veluPsi W * (veluXiAll S) ^ 2 - veluH S * veluPhiNumAll S

/-- **PROVEN, parity-free.** `veluPXAll S / veluH S = Σ_{Q ∈ S} veluPoleX`, in cleared
form. The `2`-torsion branch is where the new definition earns its keep. -/
lemma veluPXAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluPXAll S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P) * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q := by
  rw [← Finset.sum_erase S (veluPoleX_zero (W := W) (veluPointX P)), veluPXAll,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hd : veluPointX P - veluPointX Q ≠ 0 := sub_ne_zero.mpr
    (velu_X_ne hS hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))
  rw [veluH_factor_all hS hQ]
  rcases eq_or_ne (-Q) Q with h2 | h2
  · have hu : veluUTerm W Q = 0 := veluUTerm_eq_zero_of_neg_eq h2
    rw [veluEps_of_twoTorsion h2]
    simp only [pow_zero, mul_one, hu, map_zero, add_zero, Nat.add_zero, pow_one,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      veluPoleX]
    field_simp
    ring
  · rw [veluEps_of_not_twoTorsion h2]
    simp only [pow_one, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, veluPoleX]
    field_simp
    ring

/-- **PROVEN, parity-free.** `veluPVAll S / (veluH S)² = Σ_{Q ∈ S} veluPoleV`. -/
lemma veluPVAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluPVAll S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 2 * ∑ Q ∈ S, veluPoleV W (veluPointX P) Q := by
  rw [← Finset.sum_erase S (veluPoleV_zero (W := W) (veluPointX P)), veluPVAll,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hd : veluPointX P - veluPointX Q ≠ 0 := sub_ne_zero.mpr
    (velu_X_ne hS hP (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ))
  rw [veluH_factor_all hS hQ]
  rcases eq_or_ne (-Q) Q with h2 | h2
  · have hu : veluUTerm W Q = 0 := veluUTerm_eq_zero_of_neg_eq h2
    rw [veluEps_of_twoTorsion h2]
    simp only [pow_zero, mul_one, hu, map_zero, zero_add, Nat.mul_zero, Nat.add_zero,
      pow_one, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, veluPoleV]
    field_simp
    ring
  · rw [veluEps_of_not_twoTorsion h2, Nat.mul_one]
    simp only [pow_one, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, veluPoleV]
    field_simp
    ring

/-- **PROVEN, parity-free.** -/
lemma veluXNumAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluXNumAll S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P)
          * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) := by
  rw [veluXNumAll, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, veluPXAll_eval hS hP]
  ring

/-- **PROVEN, parity-free.** -/
lemma veluXiAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluXiAll S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 2
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
  rw [veluXiAll, Polynomial.eval_sub, Polynomial.eval_pow, veluPVAll_eval hS hP]
  ring

/-- **PROVEN, parity-free.** -/
lemma veluPhiNumAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluPhiNumAll S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 3
        * (4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
            W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
            (2 * W.b₄ - 20 * W.veluT S) *
              (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
            (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S)) := by
  simp only [veluPhiNumAll, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C]
  rw [veluXNumAll_eval hS hP]
  ring

/-- **PROVEN, parity-free.** The value of `veluThetaAll` at the `x`-coordinate of a point
outside the kernel is `veluH⁴` times the quotient-curve defect of the Vélu image — the
parity-free `velu_theta_eval`. Together with `velu_thetaAll_translate` this is one of the
two inputs of the still-open `velu_thetaAll_key_over`. -/
lemma velu_thetaAll_eval {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluThetaAll S).eval (veluPointX P)
      = ((veluH S).eval (veluPointX P)) ^ 4
        * ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) ^ 2
            - (4 * (W.veluCoordX S P) ^ 3 + W.b₂ * (W.veluCoordX S P) ^ 2
              + (2 * W.b₄ - 20 * W.veluT S) * W.veluCoordX S P
              + (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S))) := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hV := velu_pole_V hS hP
  rw [veluThetaAll, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_pow, velu_psi_eval hP0, veluXiAll_eval hS hP,
    veluPhiNumAll_eval hS hP, velu_coordX_eq hS hP, velu_coordY_eq hS hP]
  linear_combination (-(((veluH S).eval (veluPointX P)) ^ 4
    * ((2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q)
      + (2 * (veluPointY P
              + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q)
          + W.a₁ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q)
          + W.a₃)))) * hV

/-- **PROVEN, parity-free.** Translation invariance of the Vélu image transported to
`veluThetaAll` — the parity-free `velu_theta_translate`. This is where the SUBGROUP
hypothesis enters the local half, through `veluCoordX_add_mem` / `veluCoordY_add_mem`. -/
lemma velu_thetaAll_translate {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P R : W.Point} (hR : R ∈ S) (hP : P ∉ S) :
    (veluThetaAll S).eval (veluPointX (P + R)) * ((veluH S).eval (veluPointX P)) ^ 4
      = (veluThetaAll S).eval (veluPointX P) * ((veluH S).eval (veluPointX (P + R))) ^ 4 := by
  have hPR : P + R ∉ S := by
    intro hc
    exact hP (by simpa using hS.add_mem _ hc _ (hS.neg_mem R hR))
  rw [velu_thetaAll_eval hS hP, velu_thetaAll_eval hS hPR,
    veluCoordX_add_mem hS P hR, veluCoordY_add_mem hS P hR]
  ring

/-! ### The `2`-torsion repair: `veluGenD` DIVIDES `veluGenN`

This is the new mathematical content that makes the local half work at even order, and the
reason the audit's "re-derives with the changed degree count" understates it. -/

/-- The cofactor `M` with `veluGenN = veluGenD · M` at a `2`-TORSION point, so that
`veluGenD · M` — rather than `veluGenD² · (…)` — is the cleared `x`-coordinate of the
translate of the generic point.

Remarkably `M` is LINEAR: `M = x₀·X + (2x₀² + 2a₂x₀ + a₄ − a₁y₀)`. Its value at the point
itself is `3x₀² + 2a₂x₀ + a₄ − a₁y₀ = g^x`, which is `½·veluTTerm` there and hence
NONZERO. -/
noncomputable def veluGenM (W : Affine F) (x₀ y₀ : F) : W.CoordinateRing :=
  algebraMap F W.CoordinateRing x₀ * veluGenX W
    + algebraMap F W.CoordinateRing (2 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN — the coordinate-ring identity that unblocks the `2`-torsion case of the local
divisibility.** At a `2`-torsion point `(x₀, y₀)` of `W`, `veluGenD = X − x₀` divides the
cleared translate `veluGenN`.

Why it is needed. The odd-order argument evaluates `veluGenN` at the point and gets
`u_Q ≠ 0`; at a `2`-torsion point `u_Q = 0` (`veluUTerm_eq_zero_of_neg_eq`), so that
evaluation degenerates to `0` and the contradiction collapses. Geometrically `x − x_T` has a
DOUBLE zero at a `2`-torsion `T`, so `x(𝐏 + T)` has only a simple pole in `x − x_T`, and the
clearing factor must be `d` rather than `d²`.

The content is `(Y − y₀)² = (X − x₀)·(X² + (x₀ + a₂)X + (x₀² + a₂x₀ + a₄) − a₁Y)`: the
Weierstrass relation turns `(Y − y₀)²` into `X³ + a₂X² + a₄X + a₆ + y₀² − Y·(a₁X + a₃ + 2y₀)`,
the bracket is `a₁(X − x₀)` because `a₃ + 2y₀ = −a₁x₀`, and the cubic vanishes at `x₀`
because `x₀³ + a₂x₀² + a₄x₀ + a₆ + y₀² = y₀·(2y₀ + a₁x₀ + a₃) = 0`. The other two summands
of `veluGenN` already carry `(X − x₀)` and `(X − x₀)²`, and the `a₁Y` terms cancel — which
is why `M` comes out linear. -/
lemma velu_genN_eq_genD_mul {x₀ y₀ : F} (hEq : W.Equation x₀ y₀)
    (h2 : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    veluGenN W x₀ y₀ = veluGenD W x₀ * veluGenM W x₀ y₀ := by
  have hgen := velu_gen_equation (W := W)
  have hnegY : W.negY x₀ y₀ = y₀ := by
    simp only [Affine.negY]; linear_combination -h2
  rw [Affine.equation_iff] at hEq
  rw [Affine.equation_iff] at hgen
  simp only [velu_ma₁, velu_ma₂, velu_ma₃, velu_ma₄, velu_ma₆] at hgen
  have hEqR : (algebraMap F W.CoordinateRing) (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀)
      = (algebraMap F W.CoordinateRing) (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) := by
    rw [hEq]
  have h2R : (algebraMap F W.CoordinateRing) (2 * y₀ + W.a₁ * x₀ + W.a₃)
      = (algebraMap F W.CoordinateRing) 0 := by rw [h2]
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_zero] at hEqR h2R
  simp only [veluGenN, veluGenD, veluGenM, hnegY]
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
  linear_combination hgen - hEqR
    + (algebraMap F W.CoordinateRing y₀ - veluGenY W) * h2R

omit [DecidableEq F] [CharZero F] in
/-- **PROVEN.** `veluGenM` evaluates at the point itself to `g^x = 3x₀² + 2a₂x₀ + a₄ − a₁y₀`,
which at a `2`-torsion point is `½·veluTTerm` and hence nonzero. -/
lemma veluEvalAt_genM {x₀ y₀ : F} (hEq : W.Equation x₀ y₀) :
    veluEvalAt hEq (veluGenM W x₀ y₀)
      = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
  simp only [veluGenM, map_add, map_mul, veluEvalAt_genX, veluEvalAt_algebraMap]
  ring

/-- The cleared `x`-coordinate of the translate of the generic point by `−Q`, normalised by
the CORRECT power `veluGenD ^ (1 + ε_Q)`: `veluGenN` at an ordinary `±`-pair, and its
cofactor `veluGenM` at a `2`-torsion point. Its evaluation at the point is `u_Q` in the
first case and `g^x_Q` in the second, and is NONZERO in both — which is exactly what the
local-divisibility contradiction needs. -/
noncomputable def veluGenNq (W : Affine F) (x₀ y₀ : F) (Q : W.Point) : W.CoordinateRing :=
  if -Q = Q then veluGenM W x₀ y₀ else veluGenN W x₀ y₀

/-! ### Base change of the parity-free numerators

The parity-free counterparts of the `velu_bc_*` family of `PolePolyBaseChange`. The only new
ingredient is `velu_bc_eps`: `veluEps` is invariant under `veluBaseChangePoint` because that
map is an injective group homomorphism, so `−Q = Q` transfers in both directions. -/

section PolePolyAllOrdersBaseChange

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L] [Algebra F L]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** `veluEps` is a base-change invariant. -/
lemma velu_bc_eps (Q : W.Point) :
    veluEps (veluBaseChangePoint W L Q) = veluEps Q := by
  have hneg : veluBaseChangePoint W L (-Q) = -(veluBaseChangePoint W L Q) := map_neg _ _
  rcases eq_or_ne (-Q) Q with h2 | h2
  · refine (veluEps_of_twoTorsion ?_).trans (veluEps_of_twoTorsion h2).symm
    rw [← hneg, h2]
  · refine (veluEps_of_not_twoTorsion ?_).trans (veluEps_of_not_twoTorsion h2).symm
    intro hc
    exact h2 (veluBaseChangePoint_injective (hneg.trans hc))

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** The parity-free `velu_bc_PX`. -/
lemma velu_bc_PXAll (S : Finset W.Point) :
    veluPXAll (S.image (veluBaseChangePoint W L)) = (veluPXAll S).map (algebraMap F L) := by
  have hinj := veluBaseChangePoint_injective (W := W) (L := L)
  rw [veluPXAll, veluPXAll, Polynomial.map_sum, ← velu_bc_erase,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [velu_bc_Hq, velu_baseChange_TTerm, velu_baseChange_UTerm, veluBaseChangePoint_pointX,
    velu_bc_eps]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** The parity-free `velu_bc_PV`. -/
lemma velu_bc_PVAll (S : Finset W.Point) :
    veluPVAll (S.image (veluBaseChangePoint W L)) = (veluPVAll S).map (algebraMap F L) := by
  have hinj := veluBaseChangePoint_injective (W := W) (L := L)
  rw [veluPVAll, veluPVAll, Polynomial.map_sum, ← velu_bc_erase,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [velu_bc_Hq, velu_baseChange_TTerm, velu_baseChange_UTerm, veluBaseChangePoint_pointX,
    velu_bc_eps]
  simp only [map_mul, map_inv₀, map_ofNat]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** The parity-free `velu_bc_Xi`. -/
lemma velu_bc_XiAll (S : Finset W.Point) :
    veluXiAll (S.image (veluBaseChangePoint W L)) = (veluXiAll S).map (algebraMap F L) := by
  rw [veluXiAll, veluXiAll, Polynomial.map_sub, Polynomial.map_pow, velu_bc_H, velu_bc_PVAll]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** The parity-free `velu_bc_XNum`. -/
lemma velu_bc_XNumAll (S : Finset W.Point) :
    veluXNumAll (S.image (veluBaseChangePoint W L)) = (veluXNumAll S).map (algebraMap F L) := by
  rw [veluXNumAll, veluXNumAll, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, velu_bc_H, velu_bc_PXAll]
  simp only [map_inv₀, map_ofNat]

omit [CharZero F] [CharZero L] in
/-- **PROVEN.** The parity-free `velu_bc_PhiNum`. -/
lemma velu_bc_PhiNumAll (S : Finset W.Point) :
    veluPhiNumAll (S.image (veluBaseChangePoint W L))
      = (veluPhiNumAll S).map (algebraMap F L) := by
  simp only [veluPhiNumAll, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C]
  rw [velu_bc_H, velu_bc_XNumAll, velu_bc_b₂, velu_bc_b₄, velu_bc_b₆, velu_baseChange_T,
    velu_baseChange_W]
  simp only [map_mul, map_sub, map_ofNat]

/-- **PROVEN.** The parity-free `velu_bc_Theta`. -/
lemma velu_bc_ThetaAll (S : Finset W.Point) :
    veluThetaAll (S.image (veluBaseChangePoint W L))
      = (veluThetaAll S).map (algebraMap F L) := by
  rw [veluThetaAll, veluThetaAll, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, velu_bc_Psi, velu_bc_XiAll, velu_bc_H, velu_bc_PhiNumAll]

end PolePolyAllOrdersBaseChange

/-- **PROVEN 2026-07-27: the parity-free key identity in the affine coordinate ring** — a
UNIFORM generalisation of `velu_theta_key_over` (which is the case `ε_Q = 1`,
`veluGenNq = veluGenN`), obtained from it by the substitutions

* `veluTheta → veluThetaAll`, `veluPX/veluPV → veluPXAll/veluPVAll`;
* `veluH_factor hSL hoddL hQL → veluH_factor_all hSL hQL`, so `veluH` evaluated at the
  generic point is `d ^ (1 + ε) · G` rather than `d² · G`;
* every exponent `(d²)^k` becomes `(d ^ (1 + ε))^k`, and the final `d ^ 8` becomes
  `d ^ (4·(1 + ε))`;
* `velu_theta_translate hSL hoddL → velu_thetaAll_translate hSL`.

The ONE step needing a case split is `hx'val`, the assertion that the translate's
`x`-coordinate times `d ^ (1 + ε)` is `veluGenNq`. The `ε = 1` computation `hx'sq` is valid
at every orbit type; for `ε = 0` it is followed by `velu_genN_eq_genD_mul` and one
cancellation of `d ≠ 0`.

Note `ε` is computed on the point of `W`, while the identity is taken over the base-changed
kernel; `velu_bc_eps` transports it. -/
theorem velu_thetaAll_key_over (L : Type*) [Field L] [DecidableEq L] [CharZero L]
    [Algebra F L] [Algebra W.CoordinateRing L]
    (htower : algebraMap F L
      = (algebraMap W.CoordinateRing L).comp (algebraMap F W.CoordinateRing))
    (hinj : Function.Injective (algebraMap W.CoordinateRing L))
    {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hdeg : (veluThetaAll S).natDegree ≤ 4 * (S.card - 1))
    {x₀ y₀ : F} (hQns : W.Nonsingular x₀ y₀)
    (hQ : Affine.Point.some x₀ y₀ hQns ∈ S.erase 0) :
    AdjoinRoot.of W.polynomial (veluThetaAll S)
        * (∏ Q' ∈ S.erase 0, (veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns)
            - algebraMap F W.CoordinateRing (veluPointX Q')
              * veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))) ^ 4
      = (∑ j ∈ Finset.range (4 * (S.card - 1) + 1),
            algebraMap F W.CoordinateRing ((veluThetaAll S).coeff j)
              * veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns) ^ j
              * (veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))
                  ^ (4 * (S.card - 1) - j))
          * veluGenD W x₀ ^ (4 * (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))
          * AdjoinRoot.of W.polynomial (veluHq S (Affine.Point.some x₀ y₀ hQns)) ^ 4 := by
  have hφ : ∀ c : F,
      algebraMap W.CoordinateRing L (algebraMap F W.CoordinateRing c) = algebraMap F L c :=
    fun c => by rw [htower]; rfl
  -- Normalise the single numeric exponent so that `d ^ (1 + ε)` is a uniform atom.
  have hpow4 : veluGenD W x₀ ^ (4 * (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))
      = (veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ 4 := by
    rw [← pow_mul]; congr 1; ring
  rw [hpow4]
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
  -- The `ε = 1` clearing computation, which is valid at EVERY orbit type.
  have hx'sq : veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
        (algebraMap W.CoordinateRing L (veluGenY W)) hns
      + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL))
      * algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2
      = algebraMap W.CoordinateRing L (veluGenN W x₀ y₀) := by
    simp only [Affine.Point.neg_some, hnegY, Affine.Point.add_of_X_ne hxx, veluPointX_some,
      Affine.addX, Affine.slope_of_X_ne hxx, veluGenN, map_sub, map_add, map_mul, map_pow,
      hφ, velu_ma₁, velu_ma₂, hdval]
    field_simp
    ring
  -- The parity-free clearing: `d ^ (1 + ε)` suffices, with `veluGenM` the cofactor at
  -- `2`-torsion.  THIS IS THE ONLY CASE SPLIT.
  have hx'val : veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
        (algebraMap W.CoordinateRing L (veluGenY W)) hns
      + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL))
      * algebraMap W.CoordinateRing L (veluGenD W x₀)
          ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))
      = algebraMap W.CoordinateRing L
          (veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns)) := by
    rcases eq_or_ne (-(Affine.Point.some x₀ y₀ hQns)) (Affine.Point.some x₀ y₀ hQns) with
      h2 | h2
    · rw [veluEps_of_twoTorsion h2, veluGenNq, if_pos h2, Nat.add_zero, pow_one]
      have hy : W.negY x₀ y₀ = y₀ := by
        have hc := congrArg veluPointY h2
        rw [Affine.Point.neg_some] at hc
        exact hc
      have hv : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
        simp only [Affine.negY] at hy; linear_combination -hy
      refine mul_left_cancel₀ hdne ?_
      calc algebraMap W.CoordinateRing L (veluGenD W x₀)
            * (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
                (algebraMap W.CoordinateRing L (veluGenY W)) hns
              + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL))
              * algebraMap W.CoordinateRing L (veluGenD W x₀))
          = veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
                (algebraMap W.CoordinateRing L (veluGenY W)) hns
              + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL))
              * algebraMap W.CoordinateRing L (veluGenD W x₀) ^ 2 := by ring
        _ = algebraMap W.CoordinateRing L (veluGenN W x₀ y₀) := hx'sq
        _ = algebraMap W.CoordinateRing L (veluGenD W x₀ * veluGenM W x₀ y₀) := by
              rw [velu_genN_eq_genD_mul hQns.1 hv]
        _ = _ := by rw [map_mul]
    · rw [veluEps_of_not_twoTorsion h2, veluGenNq, if_neg h2]
      exact hx'sq
  -- The two evaluations of `veluH`.
  have hHgen : (veluH (S.image (veluBaseChangePoint W L))).eval
        (algebraMap W.CoordinateRing L (veluGenX W))
      = algebraMap W.CoordinateRing L
          (veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))
            * AdjoinRoot.of W.polynomial (veluHq S (Affine.Point.some x₀ y₀ hQns))) := by
    rw [veluH_factor_all hSL hQL, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, velu_bc_Hq,
      velu_gen_evalL htower, veluBaseChangePoint_pointX, veluPointX_some, velu_bc_eps,
      map_mul, map_pow, hdval]
  have hHtr : (veluH (S.image (veluBaseChangePoint W L))).eval
        (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
          (algebraMap W.CoordinateRing L (veluGenY W)) hns
        + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
        * (algebraMap W.CoordinateRing L (veluGenD W x₀)
            ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (S.erase 0).card
      = algebraMap W.CoordinateRing L
          (∏ Q' ∈ S.erase 0, (veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns)
            - algebraMap F W.CoordinateRing (veluPointX Q')
              * veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))) := by
    rw [veluH, Polynomial.eval_prod, ← velu_bc_erase,
      Finset.prod_image (fun a _ b _ h => veluBaseChangePoint_injective h), map_prod,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun Q' _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, veluBaseChangePoint_pointX,
      map_sub, map_mul, map_pow, hφ, sub_mul, hx'val]
  -- The two evaluations of `veluThetaAll`.
  have hΘgen : (veluThetaAll (S.image (veluBaseChangePoint W L))).eval
        (algebraMap W.CoordinateRing L (veluGenX W))
      = algebraMap W.CoordinateRing L (AdjoinRoot.of W.polynomial (veluThetaAll S)) := by
    rw [velu_bc_ThetaAll, velu_gen_evalL htower]
  have hΘtr : (veluThetaAll (S.image (veluBaseChangePoint W L))).eval
        (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
          (algebraMap W.CoordinateRing L (veluGenY W)) hns
        + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
        * (algebraMap W.CoordinateRing L (veluGenD W x₀)
            ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (4 * (S.card - 1))
      = algebraMap W.CoordinateRing L (∑ j ∈ Finset.range (4 * (S.card - 1) + 1),
          algebraMap F W.CoordinateRing ((veluThetaAll S).coeff j)
            * veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns) ^ j
            * (veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns)))
                ^ (4 * (S.card - 1) - j)) := by
    rw [velu_bc_ThetaAll,
      velu_eval_scaled ((veluThetaAll S).map (algebraMap F L))
        (algebraMap W.CoordinateRing L
          (veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns)))
        (algebraMap W.CoordinateRing L (veluGenD W x₀)
          ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) _ (4 * (S.card - 1))
        (le_trans (Polynomial.natDegree_map_le) hdeg) hx'val, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.coeff_map, map_mul, map_pow, hφ]
  -- Combine.
  have htrans := velu_thetaAll_translate hSL
    (hSL.neg_mem _ (Finset.mem_of_mem_erase hQL)) hPS
  rw [hQLeq] at htrans
  simp only [veluPointX_some] at htrans
  have hcard : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem hS.zero_mem
  have hsplit : (algebraMap W.CoordinateRing L (veluGenD W x₀)
        ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (4 * (S.card - 1))
      = ((algebraMap W.CoordinateRing L (veluGenD W x₀)
          ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (S.erase 0).card) ^ 4 := by
    rw [hcard, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  simp only [map_mul, map_pow]
  rw [← hΘgen]
  calc (veluThetaAll (S.image (veluBaseChangePoint W L))).eval
          (algebraMap W.CoordinateRing L (veluGenX W))
        * (algebraMap W.CoordinateRing L
            (∏ Q' ∈ S.erase 0, (veluGenNq W x₀ y₀ (Affine.Point.some x₀ y₀ hQns)
              - algebraMap F W.CoordinateRing (veluPointX Q')
                * veluGenD W x₀ ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))))) ^ 4
      = ((veluThetaAll (S.image (veluBaseChangePoint W L))).eval
            (algebraMap W.CoordinateRing L (veluGenX W))
          * ((veluH (S.image (veluBaseChangePoint W L))).eval
              (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
                (algebraMap W.CoordinateRing L (veluGenY W)) hns
              + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))) ^ 4)
          * (algebraMap W.CoordinateRing L (veluGenD W x₀)
              ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (4 * (S.card - 1)) := by
        rw [← hHtr, mul_pow, hsplit]; ring
    _ = ((veluThetaAll (S.image (veluBaseChangePoint W L))).eval
            (veluPointX (Affine.Point.some (algebraMap W.CoordinateRing L (veluGenX W))
              (algebraMap W.CoordinateRing L (veluGenY W)) hns
            + -(Affine.Point.some (algebraMap F L x₀) (algebraMap F L y₀) hnsL)))
          * ((veluH (S.image (veluBaseChangePoint W L))).eval
              (algebraMap W.CoordinateRing L (veluGenX W))) ^ 4)
          * (algebraMap W.CoordinateRing L (veluGenD W x₀)
              ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (4 * (S.card - 1)) := by
        linear_combination (-((algebraMap W.CoordinateRing L (veluGenD W x₀)
          ^ (1 + veluEps (Affine.Point.some x₀ y₀ hQns))) ^ (4 * (S.card - 1)))) * htrans
    _ = _ := by rw [← hΘtr, hHgen, map_mul, map_pow]; ring

/-- **PROVEN 2026-07-27 over `velu_thetaAll_key_over`: no poles, in local form, at EVERY
kernel order** — the parity-free `velu_theta_local_dvd`.

At a nonzero `Q` of the kernel, `(T − x_Q)` divides `veluThetaAll S` to the order
`4·(1 + ε_Q)`: EIGHT times at an ordinary `±`-pair (as in the odd case) and only FOUR times
at a `2`-torsion point — which is exactly the multiplicity `veluH⁴` has there, so the
assembly `velu_thetaAll_dvd` still goes through.

**Route (worked out 2026-07-27; the two `2`-torsion inputs it needs are already PROVEN
above).** The odd-order proof translates the generic point `𝐏 = (X, Y)` of the affine
coordinate ring by `−Q`, uses `x_{𝐏−Q} = N/d²` with `d = X − x_Q` and `N = veluGenN`, and
derives a contradiction by cancelling `d^k` and evaluating at `Q`, where `d ↦ 0` and
`N ↦ u_Q ≠ 0`. At a `2`-torsion `T` BOTH of those degenerate: `u_T = 0`
(`veluUTerm_eq_zero_of_neg_eq`), so `N ↦ 0` as well, and the evaluation is `0 = 0`.

The repair is that `d` DIVIDES `N` there, and the quotient is a unit at `T`. Concretely, at
a `2`-torsion `(x₀, y₀)` one has `2y₀ + a₁x₀ + a₃ = 0`, and the Weierstrass relation gives
the coordinate-ring identity

  `(Y − y₀)² = (X − x₀)·(X² + (x₀ + a₂)X + (x₀² + a₂x₀ + a₄) − a₁Y)`

(the cubic `X³ + a₂X² + a₄X + a₆ + y₀²` vanishes at `x₀` because `x₀³ + a₂x₀² + a₄x₀ + a₆ =
y₀² + a₁x₀y₀ + a₃y₀` and `a₃ + 2y₀ = −a₁x₀`). Since the other two summands of `veluGenN`
already carry `d` and `d²`, this gives `N = d·M` with

  `M ↦ 3x₀² + 2a₂x₀ + a₄ − a₁y₀ = g^x_T = ½·veluTTerm W T ≠ 0`

under `veluEvalAt`, the nonvanishing being `veluTTerm_ne_zero_of_neg_eq`. So `x_{𝐏−T} =
M/d`, `veluH(x_𝐏) = d·G` with `G = veluHq` a unit at `T` (`veluH_factor_all` with
`ε_T = 0`), and multiplying the translation identity `velu_theta_translate` by `d^{4n}`
gives `Θ(X)·𝓗⁴ = 𝓣·d⁴·G⁴` with `𝓗 = ∏_{Q'}(M − x_{Q'}d)`. Cancelling `d^k` for `k < 4` and
evaluating at `T` sends the right side to `0` while the left side is
`Θ₁(x₀)·(g^x_T)^{4n} ≠ 0` — the same contradiction, with `4` in place of `8`.

That whole route is now CARRIED OUT: the identity is `velu_genN_eq_genD_mul`, the
evaluation is `veluEvalAt_genM`, the uniform normalisation is `veluGenNq`, and the argument
below is parity-UNIFORM — the only case split is inside `hNne`, the nonvanishing of the
evaluated translate. Its input `velu_thetaAll_key_over` is PROVEN (2026-07-27).

`hdeg` is deliberately WEAKER than `velu_thetaAll_degree_lt`: `≤ 4n` rather than `< 4n`. -/
theorem velu_thetaAll_local_dvd {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hdeg : (veluThetaAll S).degree ≤ ((4 * (S.card - 1) : ℕ) : WithBot ℕ))
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (Polynomial.X - Polynomial.C (veluPointX Q)) ^ (4 * (1 + veluEps Q)) ∣ veluThetaAll S := by
  classical
  rcases eq_or_ne (veluThetaAll S) 0 with hT0 | hT0
  · rw [hT0]; exact dvd_zero _
  suffices h : 4 * (1 + veluEps Q)
      ≤ Polynomial.rootMultiplicity (veluPointX Q) (veluThetaAll S) from
    dvd_trans (pow_dvd_pow _ h) (Polynomial.pow_rootMultiplicity_dvd _ _)
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  obtain _ | ⟨x₀, y₀, hQns⟩ := Q
  · exact absurd rfl hQ0
  simp only [veluPointX_some] at hlt
  have hEqQ : W.Equation x₀ y₀ := hQns.1
  set T : W.Point := Affine.Point.some x₀ y₀ hQns with hTdef
  set e : ℕ := 1 + veluEps T with hedef
  set 𝒩 : W.CoordinateRing := veluGenNq W x₀ y₀ T with hNdef
  -- The evaluation of the cleared translate at the point itself is NONZERO. This is the
  -- only case split in the argument: `u_Q ≠ 0` at an ordinary pair, `g^x_Q ≠ 0` at
  -- `2`-torsion.
  have hNne : veluEvalAt hEqQ 𝒩 ≠ 0 := by
    rcases eq_or_ne (-T) T with h2 | h2
    · rw [hNdef, veluGenNq, if_pos h2, veluEvalAt_genM]
      have hy : W.negY x₀ y₀ = y₀ := by
        have hc := congrArg veluPointY h2
        rw [hTdef, Affine.Point.neg_some] at hc
        exact hc
      have hv : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
        simp only [Affine.negY] at hy; linear_combination -hy
      intro hc
      refine veluTTerm_ne_zero_of_neg_eq (W := W) (Q := T) hQ0 h2 ?_
      rw [hTdef, veluTTerm_some]
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      linear_combination 2 * hc + W.a₁ * hv
    · rw [hNdef, veluGenNq, if_neg h2]
      have hne2 : W.negY x₀ y₀ ≠ y₀ := fun hc =>
        h2 (by rw [hTdef, Affine.Point.neg_some]; exact velu_point_some_eq rfl hc)
      have hevN : veluEvalAt hEqQ (veluGenN W x₀ y₀) = (y₀ - W.negY x₀ y₀) ^ 2 := by
        have hevd : veluEvalAt hEqQ (veluGenD W x₀) = 0 := by
          rw [veluGenD, map_sub, veluEvalAt_genX, veluEvalAt_algebraMap, sub_self]
        simp only [veluGenN, map_sub, map_add, map_mul, map_pow, veluEvalAt_genX,
          veluEvalAt_genY, veluEvalAt_algebraMap, hevd]
        ring
      rw [hevN]
      exact pow_ne_zero 2 (sub_ne_zero.mpr fun hc => hne2 hc.symm)
  -- The root-multiplicity data.
  set k := Polynomial.rootMultiplicity x₀ (veluThetaAll S) with hkdef
  set Θ₁ := (veluThetaAll S) /ₘ ((Polynomial.X - Polynomial.C x₀) ^ k) with hΘ₁def
  have hΘsplit : (Polynomial.X - Polynomial.C x₀) ^ k * Θ₁ = veluThetaAll S :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq _ _
  have hΘ₁ne : Θ₁.eval x₀ ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ hT0
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
  set d : W.CoordinateRing := veluGenD W x₀ with hddef
  set n : ℕ := S.card - 1 with hndef
  set 𝓗 : W.CoordinateRing :=
    ∏ Q' ∈ S.erase 0, (𝒩 - algebraMap F W.CoordinateRing (veluPointX Q') * d ^ e) with h𝓗def
  set 𝓣 : W.CoordinateRing := ∑ j ∈ Finset.range (4 * n + 1),
    algebraMap F W.CoordinateRing ((veluThetaAll S).coeff j) * 𝒩 ^ j * (d ^ e) ^ (4 * n - j)
      with h𝓣def
  set G : W.CoordinateRing := AdjoinRoot.of W.polynomial (veluHq S T) with hGdef
  have key : AdjoinRoot.of W.polynomial (veluThetaAll S) * 𝓗 ^ 4 = 𝓣 * d ^ (4 * e) * G ^ 4 :=
    velu_thetaAll_key_over (FractionRing W.CoordinateRing) htower hALinj hS
      (Polynomial.natDegree_le_iff_degree_le.mpr hdeg) hQns hQ
  have hd : d ≠ 0 := velu_gen_ne x₀
  have hdvd : (d : W.CoordinateRing) ^ k *
      (AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4)
        = d ^ k * (𝓣 * d ^ (4 * e - k) * G ^ 4) := by
    have hofd : AdjoinRoot.of W.polynomial (Polynomial.X - Polynomial.C x₀) = d := by
      rw [hddef, veluGenD, map_sub, velu_of_C]
      rfl
    have hdk : AdjoinRoot.of W.polynomial (veluThetaAll S)
        = d ^ k * AdjoinRoot.of W.polynomial Θ₁ := by
      rw [← hΘsplit, map_mul, map_pow, hofd]
    calc d ^ k * (AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4)
        = AdjoinRoot.of W.polynomial (veluThetaAll S) * 𝓗 ^ 4 := by rw [hdk]; ring
      _ = 𝓣 * d ^ (4 * e) * G ^ 4 := key
      _ = d ^ k * (𝓣 * d ^ (4 * e - k) * G ^ 4) := by
          have hsp : (d : W.CoordinateRing) ^ (4 * e) = d ^ k * d ^ (4 * e - k) := by
            rw [← pow_add, Nat.add_sub_cancel' hlt.le]
          rw [hsp]; ring
  have hcancel : AdjoinRoot.of W.polynomial Θ₁ * 𝓗 ^ 4 = 𝓣 * d ^ (4 * e - k) * G ^ 4 :=
    mul_left_cancel₀ (pow_ne_zero k hd) hdvd
  -- Evaluate at the point.
  have hev := congrArg (veluEvalAt hEqQ) hcancel
  simp only [map_mul, map_pow, veluEvalAt_of] at hev
  have hevd : veluEvalAt hEqQ d = 0 := by
    rw [hddef, veluGenD, map_sub, veluEvalAt_genX, veluEvalAt_algebraMap, sub_self]
  have hev𝓗 : veluEvalAt hEqQ 𝓗 = (veluEvalAt hEqQ 𝒩) ^ (S.erase 0).card := by
    calc veluEvalAt hEqQ 𝓗
        = ∏ Q' ∈ S.erase 0, veluEvalAt hEqQ
            (𝒩 - algebraMap F W.CoordinateRing (veluPointX Q') * d ^ e) := by
          rw [h𝓗def, map_prod]
      _ = ∏ _Q' ∈ S.erase 0, veluEvalAt hEqQ 𝒩 := by
          refine Finset.prod_congr rfl fun Q' _ => ?_
          rw [map_sub, map_mul, map_pow, hevd, veluEvalAt_algebraMap,
            zero_pow (by omega : e ≠ 0)]
          ring
      _ = _ := by rw [Finset.prod_const]
  rw [hev𝓗, hevd, zero_pow (Nat.sub_ne_zero_of_lt hlt), mul_zero, zero_mul] at hev
  exact (mul_ne_zero hΘ₁ne (pow_ne_zero 4 (pow_ne_zero _ hNne))) hev

section PolePolyAllOrdersDegree

open _root_.Polynomial

/-- **PROVEN 2026-07-27: vanishing at infinity, at EVERY kernel order** — the parity-free
`velu_theta_degree_lt`, `deg (veluThetaAll S) < 4(|S| − 1)`.

The odd-order proof of `velu_theta_degree_lt` uses `hodd` only through
`velu_twoTorsion_notMem` (so that `veluHq` has degree `n − 2`) and through
`veluH_natDegree`. Parity-free, `veluHq S Q` has degree `n − 1 − ε_Q`, and the two
numerators `veluPXAll`, `veluPVAll` carry the compensating factors `(T − x_Q)^{ε_Q}` and
`(T − x_Q)^{2ε_Q}`, so every summand of `veluPXAll` still has degree `≤ n − 1` and every
summand of `veluPVAll` degree `≤ 2n − 2`, exactly as in the odd case; the two-jet calculus of
the `PolePolyDegree` section then applies verbatim.

**Three things the audit's "re-derives with the changed degree count" did not say**, all of
which the proof below has to handle.

1. The right bookkeeping variable is `k` with `|S| − 1 = k + 1`, NOT the odd case's `m` with
   `|S| − 1 = m + 2`: parity-free, `|S| − 1 = 1` really occurs (`S = {0, T}` with `T` of
   order `2`), so the odd proof's step "`(S.erase 0).card ≠ 1`, hence `= m + 2`" — which is
   where it consumed `hodd` a second time — has no parity-free analogue and must be dropped.
   Every reflect index changes accordingly (`H` at `k + 1`, `PXAll` at `k`, `PVAll` at `2k`,
   `XiAll` at `2k + 2`, `XNumAll` at `k + 2`, `PhiNumAll` at `3k + 6`, `ThetaAll` at
   `4k + 7`), and the `ε_Q = 1` branch of `hTcard` now needs the nonemptiness of
   `(S ∖ {0}) ∖ {Q}` explicitly, because `k ≥ 1` is no longer free.
2. The per-orbit split of the reflect index is `(1 + ε_Q) + |fibre| = k`, i.e. it VARIES with
   `Q`; only the total is uniform. So `reflect_mul` has to be applied at
   `veluEps Q + (((S.erase 0).erase Q).erase (-Q)).card` rather than at a fixed `1 + m`.
3. The two-jets are nevertheless PARITY-UNIFORM, and that is the load-bearing coincidence:
   at a `2`-torsion `Q` the reflected linear/quadratic factor degenerates to a CONSTANT, so
   its own first-order jet vanishes — but `u_Q = 0` there (`veluUTerm_eq_zero_of_neg_eq`) and
   the fibre sum loses exactly one copy of `x_Q` (`∑ − x_Q` instead of `∑ − 2x_Q`), and the
   two corrections cancel. Both jets come out as `t_Q` and `u_Q + t_Q x_Q − t_Q ∑ x`, exactly
   as in the odd case, so `velu_reflect_theta_dvd` is reused unchanged. -/
theorem velu_thetaAll_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluThetaAll S).degree < ((4 * (S.card - 1) : ℕ) : WithBot ℕ) := by
  classical
  have h2ne : (2 : F) ≠ 0 := by norm_num
  have hcard : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem hS.zero_mem
  have hsumT : ∑ Q ∈ S.erase 0, veluTTerm W Q = ∑ Q ∈ S, veluTTerm W Q := by
    rw [← Finset.sum_erase_add S (veluTTerm W) hS.zero_mem, veluTTerm_zero, add_zero]
  have hsumW : ∑ Q ∈ S.erase 0, veluWTerm W Q = ∑ Q ∈ S, veluWTerm W Q := by
    rw [← Finset.sum_erase_add S (veluWTerm W) hS.zero_mem, veluWTerm_zero, add_zero]
  rcases Nat.eq_zero_or_pos (S.erase 0).card with h0 | hpos
  · -- degenerate kernel `S = {0}`
    have hE : S.erase 0 = ∅ := Finset.card_eq_zero.mp h0
    have hH : veluH S = 1 := by rw [veluH, hE, Finset.prod_empty]
    have hPX : veluPXAll S = 0 := by rw [veluPXAll, hE, Finset.sum_empty]
    have hPV : veluPVAll S = 0 := by rw [veluPVAll, hE, Finset.sum_empty]
    have hT : W.veluT S = 0 := by
      rw [veluT, ← hsumT, hE, Finset.sum_empty, mul_zero]
    have hW : W.veluW S = 0 := by
      rw [veluW, ← hsumW, hE, Finset.sum_empty, mul_zero]
    have hTheta : veluThetaAll S = 0 := by
      rw [veluThetaAll, veluXiAll, veluPhiNumAll, veluXNumAll, hH, hPX, hPV, hT, hW, veluPsi]
      ring_nf
    have hz : 4 * (S.card - 1) = 0 := by omega
    rw [hTheta, degree_zero, hz]
    exact WithBot.bot_lt_coe _
  · -- the substantial case
    obtain ⟨k, hk⟩ : ∃ k, (S.erase 0).card = k + 1 := ⟨(S.erase 0).card - 1, by omega⟩
    have hHdeg : (veluH S).natDegree = k + 1 := by rw [veluH_natDegree hS]; omega
    have hTcard : ∀ Q ∈ S.erase 0,
        (((S.erase 0).erase Q).erase (-Q)).card + veluEps Q = k := by
      intro Q hQ
      have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
      have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
      have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
      have e2 := Finset.card_erase_of_mem hQ
      rcases eq_or_ne (-Q) Q with h2 | h2
      · rw [veluEps_of_twoTorsion h2, h2, Finset.erase_idem]
        omega
      · have h1 : -Q ∈ (S.erase 0).erase Q :=
          Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
        have e1 := Finset.card_erase_of_mem h1
        have e1pos : 0 < ((S.erase 0).erase Q).card := Finset.card_pos.mpr ⟨-Q, h1⟩
        rw [veluEps_of_not_twoTorsion h2]
        omega
    have hTsum1 : ∀ Q ∈ S.erase 0, -Q ≠ Q →
        ∑ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), veluPointX Q'
          = (∑ Q' ∈ S.erase 0, veluPointX Q') - 2 * veluPointX Q := by
      intro Q hQ h2
      have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
      have hQS : Q ∈ S := Finset.mem_of_mem_erase hQ
      have hnQ0 : -Q ≠ 0 := fun h => hQ0 (neg_eq_zero.mp h)
      have h1 : -Q ∈ (S.erase 0).erase Q :=
        Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨hnQ0, hS.neg_mem _ hQS⟩⟩
      have e1 := Finset.sum_erase_add (S.erase 0) veluPointX hQ
      have e2 := Finset.sum_erase_add ((S.erase 0).erase Q) veluPointX h1
      rw [velu_pointX_neg] at e2
      linear_combination e1 + e2
    have hTsum0 : ∀ Q ∈ S.erase 0, -Q = Q →
        ∑ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), veluPointX Q'
          = (∑ Q' ∈ S.erase 0, veluPointX Q') - veluPointX Q := by
      intro Q hQ h2
      rw [h2, Finset.erase_idem]
      have e1 := Finset.sum_erase_add (S.erase 0) veluPointX hQ
      linear_combination e1
    have hHqdeg : ∀ Q ∈ S.erase 0,
        (veluHq S Q).natDegree ≤ (((S.erase 0).erase Q).erase (-Q)).card := by
      intro Q hQ
      rw [veluHq]
      refine le_trans (natDegree_prod_le _ _) ?_
      simp
    have hreflHq : ∀ Q ∈ S.erase 0,
        reflect ((((S.erase 0).erase Q).erase (-Q)).card) (veluHq S Q)
          = ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)), (1 - C (veluPointX Q') * X) := by
      intro Q hQ
      rw [veluHq]
      exact velu_reflect_prod_X_sub_C _ _
    have hreflH : reflect (k + 1) (veluH S)
        = ∏ Q ∈ S.erase 0, (1 - C (veluPointX Q) * X) := by
      rw [veluH, ← hk]
      exact velu_reflect_prod_X_sub_C _ _
    -- per-orbit degree bounds of the two numerator factors
    have hlin : ∀ Q : W.Point, (C (veluTTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
        + C (veluUTerm W Q)).natDegree ≤ veluEps Q := by
      intro Q
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_pow_le ?_)
        simp
      · simp
    have hquad : ∀ Q : W.Point, (C (veluUTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
        + C ((2 : F)⁻¹ * veluTTerm W Q)
            * (X - C (veluPointX Q)) ^ (2 * veluEps Q)).natDegree ≤ 2 * veluEps Q := by
      intro Q
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_pow_le ?_)
        simp
        omega
      · refine le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_pow_le ?_)
        simp
    -- degree bounds
    have hPXdeg : (veluPXAll S).natDegree ≤ k := by
      rw [veluPXAll]
      refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
      refine le_trans natDegree_mul_le ?_
      have hc := hTcard Q hQ
      have := add_le_add (hlin Q) (hHqdeg Q hQ)
      omega
    have hPVdeg : (veluPVAll S).natDegree ≤ 2 * k := by
      rw [veluPVAll]
      refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
      refine le_trans natDegree_mul_le ?_
      have hsq : ((veluHq S Q) ^ 2).natDegree
          ≤ 2 * (((S.erase 0).erase Q).erase (-Q)).card := by
        have := hHqdeg Q hQ
        exact le_trans natDegree_pow_le (by omega)
      have hc := hTcard Q hQ
      have := add_le_add (hquad Q) hsq
      omega
    have hCPXdeg : (C ((2 : F)⁻¹) * veluPXAll S).natDegree ≤ k :=
      le_trans (natDegree_C_mul_le _ _) hPXdeg
    have hXideg : (veluXiAll S).natDegree ≤ 2 * k + 2 := by
      rw [veluXiAll]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans natDegree_pow_le (by omega)
      · omega
    have hXNdeg : (veluXNumAll S).natDegree ≤ k + 2 := by
      rw [veluXNumAll]
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans natDegree_mul_le ?_
        rw [natDegree_X]; omega
      · exact le_trans (natDegree_C_mul_le _ _) (by omega)
    have hxn2 : ((veluXNumAll S) ^ 2).natDegree ≤ 2 * (k + 2) :=
      le_trans natDegree_pow_le (by omega)
    have hxn3 : ((veluXNumAll S) ^ 3).natDegree ≤ 3 * k + 6 :=
      le_trans natDegree_pow_le (by omega)
    have hh2 : ((veluH S) ^ 2).natDegree ≤ 2 * (k + 1) :=
      le_trans natDegree_pow_le (by omega)
    have hh3 : ((veluH S) ^ 3).natDegree ≤ 3 * k + 3 :=
      le_trans natDegree_pow_le (by omega)
    have hPhideg : (veluPhiNumAll S).natDegree ≤ 3 * k + 6 := by
      have t1 : (C (4 : F) * (veluXNumAll S) ^ 3).natDegree ≤ 3 * k + 6 :=
        le_trans (natDegree_C_mul_le _ _) hxn3
      have t2 : (C W.b₂ * (veluXNumAll S) ^ 2 * veluH S).natDegree ≤ 3 * k + 6 := by
        refine le_trans natDegree_mul_le ?_
        have := le_trans (natDegree_C_mul_le W.b₂ ((veluXNumAll S) ^ 2)) hxn2
        omega
      have t3 : (C (2 * W.b₄ - 20 * W.veluT S) * veluXNumAll S * (veluH S) ^ 2).natDegree
          ≤ 3 * k + 6 := by
        refine le_trans natDegree_mul_le ?_
        have := le_trans (natDegree_C_mul_le (2 * W.b₄ - 20 * W.veluT S) (veluXNumAll S)) hXNdeg
        omega
      have t4 : (C (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S)
          * (veluH S) ^ 3).natDegree ≤ 3 * k + 6 :=
        le_trans (natDegree_C_mul_le _ _) (by omega)
      rw [veluPhiNumAll]
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
    have hThetadeg : (veluThetaAll S).natDegree ≤ 4 * k + 7 := by
      rw [veluThetaAll]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans natDegree_mul_le ?_
        have hxi2 : ((veluXiAll S) ^ 2).natDegree ≤ 4 * k + 4 :=
          le_trans natDegree_pow_le (by omega)
        omega
      · refine le_trans natDegree_mul_le ?_
        omega
    -- reflected forms
    have hPXrefl : reflect k (veluPXAll S)
        = ∑ Q ∈ S.erase 0,
            (reflect (veluEps Q) (C (veluTTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
                + C (veluUTerm W Q)))
              * ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
                  (1 - C (veluPointX Q') * X) := by
      rw [veluPXAll, velu_reflect_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hkeq : veluEps Q + (((S.erase 0).erase Q).erase (-Q)).card = k := by
        have := hTcard Q hQ; omega
      rw [← hkeq, reflect_mul _ _ (hlin Q) (hHqdeg Q hQ), hreflHq Q hQ]
    have hPVrefl : reflect (2 * k) (veluPVAll S)
        = ∑ Q ∈ S.erase 0,
            (reflect (2 * veluEps Q) (C (veluUTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
                + C ((2 : F)⁻¹ * veluTTerm W Q)
                    * (X - C (veluPointX Q)) ^ (2 * veluEps Q)))
              * (∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
                  (1 - C (veluPointX Q') * X)) ^ 2 := by
      rw [veluPVAll, velu_reflect_sum]
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hq := hHqdeg Q hQ
      have hsq : ((veluHq S Q) ^ 2).natDegree
          ≤ (((S.erase 0).erase Q).erase (-Q)).card
            + (((S.erase 0).erase Q).erase (-Q)).card :=
        le_trans natDegree_pow_le (by omega)
      have hHq2 : reflect ((((S.erase 0).erase Q).erase (-Q)).card
            + (((S.erase 0).erase Q).erase (-Q)).card) ((veluHq S Q) ^ 2)
          = (reflect ((((S.erase 0).erase Q).erase (-Q)).card) (veluHq S Q)) ^ 2 := by
        rw [pow_two, pow_two, reflect_mul _ _ hq hq]
      have hkeq : 2 * veluEps Q + ((((S.erase 0).erase Q).erase (-Q)).card
          + (((S.erase 0).erase Q).erase (-Q)).card) = 2 * k := by
        have := hTcard Q hQ; omega
      rw [← hkeq, reflect_mul _ _ (hquad Q) hsq, hHq2, hreflHq Q hQ]
    -- per-orbit jets (the ONLY case split)
    have hjetX : ∀ Q ∈ S.erase 0,
        ((reflect (veluEps Q) (C (veluTTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
            + C (veluUTerm W Q)))
          * ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
              (1 - C (veluPointX Q') * X)).coeff 0 = veluTTerm W Q
        ∧ ((reflect (veluEps Q) (C (veluTTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
            + C (veluUTerm W Q)))
          * ∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
              (1 - C (veluPointX Q') * X)).coeff 1
            = veluUTerm W Q + veluTTerm W Q * veluPointX Q
              - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q' := by
      intro Q hQ
      rcases eq_or_ne (-Q) Q with h2 | h2
      · have hu : veluUTerm W Q = 0 := veluUTerm_eq_zero_of_neg_eq h2
        rw [veluEps_of_twoTorsion h2]
        simp only [pow_zero, mul_one, hu, map_zero, add_zero, reflect_C, pow_zero, mul_one]
        refine ⟨?_, ?_⟩
        · rw [coeff_C_mul, velu_prod_coeff_zero, mul_one]
        · rw [coeff_C_mul, velu_prod_coeff_one, hTsum0 Q hQ h2]
          ring
      · rw [veluEps_of_not_twoTorsion h2, pow_one, reflect_add, reflect_C_mul,
          velu_reflect_one_X_sub_C, reflect_C, pow_one]
        have e0 : (C (veluTTerm W Q) * (1 - C (veluPointX Q) * X)
            + C (veluUTerm W Q) * X).coeff 0 = veluTTerm W Q := by
          simp [coeff_one]
        have e1 : (C (veluTTerm W Q) * (1 - C (veluPointX Q) * X)
            + C (veluUTerm W Q) * X).coeff 1
              = veluUTerm W Q - veluTTerm W Q * veluPointX Q := by
          simp [coeff_one]
          ring
        refine ⟨?_, ?_⟩
        · rw [mul_coeff_zero, e0, velu_prod_coeff_zero, mul_one]
        · rw [velu_coeff_one_mul, e0, e1, velu_prod_coeff_zero, velu_prod_coeff_one,
            hTsum1 Q hQ h2]
          ring
    have hjetV : ∀ Q ∈ S.erase 0,
        ((reflect (2 * veluEps Q) (C (veluUTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
            + C ((2 : F)⁻¹ * veluTTerm W Q)
                * (X - C (veluPointX Q)) ^ (2 * veluEps Q)))
          * (∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
              (1 - C (veluPointX Q') * X)) ^ 2).coeff 0 = (2 : F)⁻¹ * veluTTerm W Q
        ∧ ((reflect (2 * veluEps Q) (C (veluUTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
            + C ((2 : F)⁻¹ * veluTTerm W Q)
                * (X - C (veluPointX Q)) ^ (2 * veluEps Q)))
          * (∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
              (1 - C (veluPointX Q') * X)) ^ 2).coeff 1
            = veluUTerm W Q + veluTTerm W Q * veluPointX Q
              - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q' := by
      intro Q hQ
      have p0 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
          (1 - C (veluPointX Q') * X)) ^ 2).coeff 0 = 1 := by
        rw [pow_two, mul_coeff_zero, velu_prod_coeff_zero]; ring
      rcases eq_or_ne (-Q) Q with h2 | h2
      · have hu : veluUTerm W Q = 0 := veluUTerm_eq_zero_of_neg_eq h2
        have p1 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
            (1 - C (veluPointX Q') * X)) ^ 2).coeff 1
              = 2 * -((∑ Q' ∈ S.erase 0, veluPointX Q') - veluPointX Q) := by
          rw [pow_two, velu_coeff_one_mul, velu_prod_coeff_zero, velu_prod_coeff_one,
            hTsum0 Q hQ h2]
          ring
        rw [veluEps_of_twoTorsion h2]
        simp only [pow_zero, mul_one, hu, map_zero, zero_add, Nat.mul_zero, reflect_C,
          pow_zero, mul_one]
        refine ⟨?_, ?_⟩
        · rw [coeff_C_mul, p0, mul_one]
        · rw [coeff_C_mul, p1]
          field_simp
          ring
      · have p1 : ((∏ Q' ∈ (((S.erase 0).erase Q).erase (-Q)),
            (1 - C (veluPointX Q') * X)) ^ 2).coeff 1
              = 2 * -((∑ Q' ∈ S.erase 0, veluPointX Q') - 2 * veluPointX Q) := by
          rw [pow_two, velu_coeff_one_mul, velu_prod_coeff_zero, velu_prod_coeff_one,
            hTsum1 Q hQ h2]
          ring
        rw [veluEps_of_not_twoTorsion h2, pow_one, Nat.mul_one, reflect_add, reflect_C_mul,
          reflect_C_mul, velu_reflect_two_X_sub_C, velu_reflect_two_X_sub_C_sq]
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
        refine ⟨?_, ?_⟩
        · rw [mul_coeff_zero, a0, p0, mul_one]
        · rw [velu_coeff_one_mul, a0, a1, p0, p1]
          field_simp
          ring
    -- jets
    have hjh0 : (reflect (k + 1) (veluH S)).coeff 0 = 1 := by
      rw [hreflH, velu_prod_coeff_zero]
    have hjh1 : (reflect (k + 1) (veluH S)).coeff 1 = -∑ Q ∈ S.erase 0, veluPointX Q := by
      rw [hreflH, velu_prod_coeff_one]
    have hjpx0 : (reflect k (veluPXAll S)).coeff 0 = ∑ Q ∈ S.erase 0, veluTTerm W Q := by
      rw [hPXrefl, finsetSum_coeff]
      exact Finset.sum_congr rfl fun Q hQ => (hjetX Q hQ).1
    have hjpx1 : (reflect k (veluPXAll S)).coeff 1
        = ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
            - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q') := by
      rw [hPXrefl, finsetSum_coeff]
      exact Finset.sum_congr rfl fun Q hQ => (hjetX Q hQ).2
    have hjpv0 : (reflect (2 * k) (veluPVAll S)).coeff 0
        = ∑ Q ∈ S.erase 0, (2 : F)⁻¹ * veluTTerm W Q := by
      rw [hPVrefl, finsetSum_coeff]
      exact Finset.sum_congr rfl fun Q hQ => (hjetV Q hQ).1
    have hjpv1 : (reflect (2 * k) (veluPVAll S)).coeff 1
        = ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
            - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q') := by
      rw [hPVrefl, finsetSum_coeff]
      exact Finset.sum_congr rfl fun Q hQ => (hjetV Q hQ).2
    -- assembled reflected identity
    have hXirefl : reflect (2 * k + 2) (veluXiAll S)
        = (reflect (k + 1) (veluH S)) ^ 2 - (reflect (2 * k) (veluPVAll S)) * X ^ 2 := by
      have e1 : reflect (2 * k + 2) ((veluH S) ^ 2) = (reflect (k + 1) (veluH S)) ^ 2 := by
        rw [pow_two, pow_two, show 2 * k + 2 = (k + 1) + (k + 1) from by ring,
          reflect_mul _ _ (le_of_eq hHdeg) (le_of_eq hHdeg)]
      have e2 : reflect (2 * k + 2) (veluPVAll S)
          = (reflect (2 * k) (veluPVAll S)) * X ^ 2 := by
        rw [show 2 * k + 2 = (2 * k) + 2 from by ring, velu_reflect_shift hPVdeg]
      rw [veluXiAll, reflect_sub, e1, e2]
    have hXNrefl : reflect (k + 2) (veluXNumAll S)
        = reflect (k + 1) (veluH S)
          + (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) * X ^ 2 := by
      have e1 : reflect (k + 2) (X * veluH S) = reflect (k + 1) (veluH S) := by
        rw [show k + 2 = 1 + (k + 1) from by ring,
          reflect_mul _ _ (le_of_eq natDegree_X) (le_of_eq hHdeg), reflect_one_X, one_mul]
      have e2 : reflect (k + 2) (C ((2 : F)⁻¹) * veluPXAll S)
          = (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) * X ^ 2 := by
        rw [show k + 2 = k + 2 from by ring, velu_reflect_shift hCPXdeg]
      rw [veluXNumAll, reflect_add, e1, e2]
    have hPhirefl : reflect (3 * k + 6) (veluPhiNumAll S)
        = 4 * (reflect (k + 2) (veluXNumAll S)) ^ 3
          + C W.b₂ * ((reflect (k + 2) (veluXNumAll S)) ^ 2 * reflect (k + 1) (veluH S) * X)
          + (2 * C W.b₄ - 20 * C (W.veluT S))
              * ((reflect (k + 2) (veluXNumAll S)) * (reflect (k + 1) (veluH S)) ^ 2 * X ^ 2)
          + (C W.b₆ - 4 * C W.b₂ * C (W.veluT S) - 28 * C (W.veluW S))
              * ((reflect (k + 1) (veluH S)) ^ 3 * X ^ 3) := by
      have e1 : reflect (3 * k + 6) ((veluXNumAll S) ^ 3)
          = (reflect (k + 2) (veluXNumAll S)) ^ 3 := by
        rw [show 3 * k + 6 = 3 * (k + 2) from by ring, velu_reflect_pow hXNdeg 3]
      have e2 : reflect (3 * k + 6) ((veluXNumAll S) ^ 2 * veluH S)
          = ((reflect (k + 2) (veluXNumAll S)) ^ 2 * reflect (k + 1) (veluH S)) * X := by
        have hd : ((veluXNumAll S) ^ 2 * veluH S).natDegree ≤ 3 * k + 5 := by
          refine le_trans natDegree_mul_le ?_; omega
        rw [show 3 * k + 6 = (3 * k + 5) + 1 from by ring, velu_reflect_shift hd, pow_one,
          show 3 * k + 5 = 2 * (k + 2) + (k + 1) from by ring,
          reflect_mul _ _ hxn2 (le_of_eq hHdeg), velu_reflect_pow hXNdeg 2]
      have e3 : reflect (3 * k + 6) (veluXNumAll S * (veluH S) ^ 2)
          = ((reflect (k + 2) (veluXNumAll S)) * (reflect (k + 1) (veluH S)) ^ 2) * X ^ 2 := by
        have hd : (veluXNumAll S * (veluH S) ^ 2).natDegree ≤ 3 * k + 4 := by
          refine le_trans natDegree_mul_le ?_; omega
        rw [show 3 * k + 6 = (3 * k + 4) + 2 from by ring, velu_reflect_shift hd,
          show 3 * k + 4 = (k + 2) + 2 * (k + 1) from by ring,
          reflect_mul _ _ hXNdeg hh2, velu_reflect_pow (le_of_eq hHdeg) 2]
      have e4 : reflect (3 * k + 6) ((veluH S) ^ 3)
          = (reflect (k + 1) (veluH S)) ^ 3 * X ^ 3 := by
        rw [show 3 * k + 6 = (3 * k + 3) + 3 from by ring, velu_reflect_shift hh3,
          show 3 * k + 3 = 3 * (k + 1) from by ring, velu_reflect_pow (le_of_eq hHdeg) 3]
      rw [veluPhiNumAll, reflect_add, reflect_add, reflect_add, mul_assoc (C W.b₂),
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
    have hThetarefl : reflect (4 * k + 7) (veluThetaAll S)
        = (4 + C W.b₂ * X + 2 * C W.b₄ * X ^ 2 + C W.b₆ * X ^ 3)
            * ((reflect (k + 1) (veluH S)) ^ 2
                - (reflect (2 * k) (veluPVAll S)) * X ^ 2) ^ 2
          - reflect (k + 1) (veluH S)
            * (4 * (reflect (k + 1) (veluH S)
                    + (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) * X ^ 2) ^ 3
              + C W.b₂ * ((reflect (k + 1) (veluH S)
                    + (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) * X ^ 2) ^ 2
                  * reflect (k + 1) (veluH S) * X)
              + (2 * C W.b₄ - 20 * C (W.veluT S))
                  * ((reflect (k + 1) (veluH S)
                      + (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) * X ^ 2)
                    * (reflect (k + 1) (veluH S)) ^ 2 * X ^ 2)
              + (C W.b₆ - 4 * C W.b₂ * C (W.veluT S) - 28 * C (W.veluW S))
                  * ((reflect (k + 1) (veluH S)) ^ 3 * X ^ 3)) := by
      have e1 : reflect (4 * k + 7) (veluPsi W * (veluXiAll S) ^ 2)
          = reflect 3 (veluPsi W) * (reflect (2 * k + 2) (veluXiAll S)) ^ 2 := by
        have hxi2 : ((veluXiAll S) ^ 2).natDegree ≤ 4 * k + 4 :=
          le_trans natDegree_pow_le (by omega)
        rw [show 4 * k + 7 = 3 + (4 * k + 4) from by ring,
          reflect_mul _ _ hPsideg hxi2,
          show 4 * k + 4 = 2 * (2 * k + 2) from by ring, velu_reflect_pow hXideg 2]
      have e2 : reflect (4 * k + 7) (veluH S * veluPhiNumAll S)
          = reflect (k + 1) (veluH S) * reflect (3 * k + 6) (veluPhiNumAll S) := by
        rw [show 4 * k + 7 = (k + 1) + (3 * k + 6) from by ring,
          reflect_mul _ _ (le_of_eq hHdeg) hPhideg]
      rw [veluThetaAll, reflect_sub, e1, e2, hPsirefl, hXirefl, hPhirefl, hXNrefl]
    -- final jets in Vélu's constants
    have hjpx0' : (reflect k (C ((2 : F)⁻¹) * veluPXAll S)).coeff 0 = W.veluT S := by
      rw [reflect_C_mul, coeff_C_mul, hjpx0, hsumT, veluT]
    have hsplit : ∑ Q ∈ S.erase 0, (veluUTerm W Q + veluTTerm W Q * veluPointX Q
        - veluTTerm W Q * ∑ Q' ∈ S.erase 0, veluPointX Q')
        = (∑ Q ∈ S.erase 0, veluWTerm W Q)
          - (∑ Q' ∈ S.erase 0, veluPointX Q') * ∑ Q ∈ S.erase 0, veluTTerm W Q := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun Q _ => by rw [velu_wTerm_eq]; ring
      · exact Finset.sum_congr rfl fun Q _ => by ring
    have hjpx1' : (reflect k (C ((2 : F)⁻¹) * veluPXAll S)).coeff 1
        = W.veluT S * (-∑ Q ∈ S.erase 0, veluPointX Q) + W.veluW S := by
      rw [reflect_C_mul, coeff_C_mul, hjpx1, hsplit, veluT, veluW, ← hsumT, ← hsumW]
      ring
    have hjpv0' : (reflect (2 * k) (veluPVAll S)).coeff 0 = W.veluT S := by
      rw [hjpv0, ← Finset.mul_sum, veluT, ← hsumT]
    have hjpv1' : (reflect (2 * k) (veluPVAll S)).coeff 1
        = 2 * (W.veluT S * (-∑ Q ∈ S.erase 0, veluPointX Q)) + 2 * W.veluW S := by
      rw [hjpv1, hsplit, veluT, veluW, ← hsumT, ← hsumW]
      field_simp
      ring
    have hdvd := velu_reflect_theta_dvd (reflect (k + 1) (veluH S))
      (reflect k (C ((2 : F)⁻¹) * veluPXAll S)) (reflect (2 * k) (veluPVAll S))
      (W.veluT S) (W.veluW S) W.b₂ W.b₄ W.b₆ (-∑ Q ∈ S.erase 0, veluPointX Q)
      hjh0 hjh1 hjpx0' hjpx1' hjpv0' hjpv1'
    rw [← hThetarefl] at hdvd
    have hres := velu_degree_lt_of_reflect hThetadeg hdvd
    have heq : 4 * (S.card - 1) = 4 * k + 7 + 1 - 4 := by omega
    rw [heq]
    exact hres

end PolePolyAllOrdersDegree

omit [CharZero F] in
/-- **PROVEN, parity-free.** The local divisibilities assemble: distinct linear factors are
coprime, and `veluH⁴` is their product with the per-orbit exponents of
`veluH_pow_eq_all`. -/
theorem velu_thetaAll_dvd {S : Finset W.Point} (hS : IsPointSubgroup S)
    (hloc : ∀ Q ∈ S.erase 0,
      (Polynomial.X - Polynomial.C (veluPointX Q)) ^ (4 * (1 + veluEps Q)) ∣ veluThetaAll S) :
    (veluH S) ^ 4 ∣ veluThetaAll S := by
  rw [veluH_pow_eq_all S]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun a ha => ?_)
  · exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ha
    rw [velu_fiber_card_all hS hQ]
    exact hloc Q hQ

/-- **PROVEN over the two leaves, parity-free.** `veluThetaAll S = 0`: a polynomial
divisible by `veluH⁴` and of degree below `deg veluH⁴ = 4(|S| − 1)` is zero. -/
theorem velu_thetaAll_eq_zero {S : Finset W.Point} (hS : IsPointSubgroup S) :
    veluThetaAll S = 0 :=
  Polynomial.eq_zero_of_dvd_of_degree_lt
    (velu_thetaAll_dvd hS fun _ hQ =>
      velu_thetaAll_local_dvd hS (velu_thetaAll_degree_lt hS).le hQ)
    (by rw [veluH_pow_degree hS]; exact velu_thetaAll_degree_lt hS)

/-- **PROVEN, parity-free: Vélu's rational-function identity with `y` eliminated.**

This is `velu_pole_identity` with the hypothesis `Odd S.card` DELETED, and it is the single
node at which parity entered the whole development: everything above it in the pole layer
(`velu_coordX_eq`, `velu_coordY_eq`, `velu_pole_V`, `velu_sum_pair`) was already stated
without a parity hypothesis, and everything below it follows formally. -/
theorem velu_pole_identity_of_subgroup {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆) *
        (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) ^ 2 =
      4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
        W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
        (2 * W.b₄ - 20 * W.veluT S) *
          (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
        (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S) := by
  have hH := veluH_eval_ne_zero hS hP
  have hTheta : (veluPsi W).eval (veluPointX P) * ((veluXiAll S).eval (veluPointX P)) ^ 2
      - (veluH S).eval (veluPointX P) * ((veluPhiNumAll S).eval (veluPointX P)) = 0 := by
    have h0 := congrArg (Polynomial.eval (veluPointX P)) (velu_thetaAll_eq_zero hS)
    simpa [veluThetaAll] using h0
  have hPsi : (veluPsi W).eval (veluPointX P)
      = 4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆ := by
    simp only [veluPsi, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
  rw [hPsi, veluXiAll_eval hS hP, veluPhiNumAll_eval hS hP] at hTheta
  have key : ((veluH S).eval (veluPointX P)) ^ 4 *
      (((4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆) *
          (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) ^ 2)
        - (4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
            W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
            (2 * W.b₄ - 20 * W.veluT S) *
              (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
            (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S))) = 0 := by
    linear_combination hTheta
  rcases mul_eq_zero.mp key with h1 | h2
  · exact absurd h1 (pow_ne_zero _ hH)
  · exact sub_eq_zero.mp h2

omit [DecidableEq F] [CharZero F] in
lemma veluUTerm_neg (P : W.Point) : veluUTerm W (-P) = veluUTerm W P := by
  cases P with
  | zero => rfl
  | some x y h =>
      show (2 * W.negY x y + W.a₁ * x + W.a₃) ^ 2 = (2 * y + W.a₁ * x + W.a₃) ^ 2
      simp only [WeierstrassCurve.Affine.negY]
      ring

omit [DecidableEq F] [CharZero F] in
lemma veluUTerm_ne_zero_of_neg_ne {Q : W.Point} (hQ : Q ≠ 0) (h : -Q ≠ Q) :
    veluUTerm W Q ≠ 0 := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y hns =>
      rw [veluUTerm_some]
      intro hc
      refine h ?_
      have hv : 2 * y + W.a₁ * x + W.a₃ = 0 := (pow_eq_zero_iff two_ne_zero).mp hc
      have hy : W.negY x y = y := by
        simp only [WeierstrassCurve.Affine.negY]; linear_combination -hv
      simp only [Affine.Point.neg_some, hy]

omit [CharZero F] in
lemma veluHq_neg (S : Finset W.Point) (Q : W.Point) : veluHq S (-Q) = veluHq S Q := by
  rw [veluHq, veluHq, neg_neg]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext a
  simp only [Finset.mem_erase]
  tauto

omit [CharZero F] in
lemma veluHq_eval_self_ne_zero {S : Finset W.Point}
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (veluHq S Q).eval (veluPointX Q) ≠ 0 := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  rw [veluHq, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun Q' hQ' => ?_
  have h1 : Q' ≠ -Q := Finset.ne_of_mem_erase hQ'
  have h2 : Q' ≠ Q := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hQ')
  have h3 : Q' ≠ 0 :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hQ'))
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  intro hc
  rcases velu_pointX_eq_iff h3 hQ0 (sub_eq_zero.mp hc).symm with h | h
  · exact h2 h
  · exact h1 h

omit [CharZero F] in
lemma veluHq_eval_other_eq_zero {S : Finset W.Point}
    {Q Q' : W.Point} (hQ : Q ∈ S.erase 0) (hne : veluPointX Q' ≠ veluPointX Q) :
    (veluHq S Q').eval (veluPointX Q) = 0 := by
  rw [veluHq, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := Q) ?_ ?_
  · refine Finset.mem_erase.mpr ⟨fun hc => hne ?_, Finset.mem_erase.mpr ⟨fun hc => hne ?_, hQ⟩⟩
    · rw [hc, velu_pointX_neg]
    · rw [hc]
  · simp

/-- **SUB-LEAF (item 4), first half.** At a root `x_Q` of `veluH`, the numerator `veluPXAll`
does not vanish. -/
lemma velu_pXAll_eval_ne_zero {S : Finset W.Point} (hS : IsPointSubgroup S)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (veluPXAll S).eval (veluPointX Q) ≠ 0 := by
  have hQ0 : Q ≠ 0 := Finset.ne_of_mem_erase hQ
  have hhq := veluHq_eval_self_ne_zero hQ
  rw [veluPXAll, Polynomial.eval_finsetSum,
    ← Finset.sum_filter_add_sum_filter_not (S.erase 0)
      (fun Q' => veluPointX Q' = veluPointX Q)]
  have hzero : ∑ Q' ∈ (S.erase 0).filter (fun Q' => ¬ (veluPointX Q' = veluPointX Q)),
      Polynomial.eval (veluPointX Q)
        ((Polynomial.C (veluTTerm W Q') * (Polynomial.X - Polynomial.C (veluPointX Q'))
            ^ veluEps Q' + Polynomial.C (veluUTerm W Q')) * veluHq S Q') = 0 :=
    Finset.sum_eq_zero fun Q' hQ' => by
      rw [Polynomial.eval_mul, veluHq_eval_other_eq_zero hQ (Finset.mem_filter.mp hQ').2,
        mul_zero]
  rw [hzero, add_zero, velu_fiber hS hQ]
  rcases eq_or_ne (-Q) Q with h2 | h2
  · have hpair : ({Q, -Q} : Finset W.Point) = {Q} := by rw [h2]; simp
    rw [hpair, Finset.sum_singleton, veluEps_of_twoTorsion h2,
      veluUTerm_eq_zero_of_neg_eq h2]
    simp only [pow_zero, mul_one, map_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero (veluTTerm_ne_zero_of_neg_eq hQ0 h2) hhq
  · rw [Finset.sum_pair h2.symm, veluEps_of_not_twoTorsion h2,
      veluEps_of_not_twoTorsion (show -(-Q) ≠ -Q by rw [neg_neg]; exact h2.symm),
      velu_pointX_neg, veluUTerm_neg, veluHq_neg]
    have hshape : Polynomial.eval (veluPointX Q)
          ((Polynomial.C (veluTTerm W Q) * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 1
            + Polynomial.C (veluUTerm W Q)) * veluHq S Q)
        + Polynomial.eval (veluPointX Q)
          ((Polynomial.C (veluTTerm W (-Q)) * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 1
            + Polynomial.C (veluUTerm W Q)) * veluHq S Q)
        = 2 * (veluUTerm W Q * (veluHq S Q).eval (veluPointX Q)) := by
      simp only [pow_one, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, mul_zero, zero_add]
      ring
    rw [hshape]
    exact mul_ne_zero (by norm_num : (2 : F) ≠ 0)
      (mul_ne_zero (veluUTerm_ne_zero_of_neg_ne hQ0 h2) hhq)

omit [CharZero F] in
lemma velu_H_root_iff {S : Finset W.Point} {a : F} (ha : (veluH S).eval a = 0) :
    ∃ Q ∈ S.erase 0, veluPointX Q = a := by
  rw [veluH, Polynomial.eval_prod] at ha
  obtain ⟨Q, hQ, hQ0⟩ := Finset.prod_eq_zero_iff.mp ha
  refine ⟨Q, hQ, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ0
  exact (sub_eq_zero.mp hQ0).symm

/-- **SUB-LEAF 1 (item 4): `gcd(veluXNumAll, veluH) = 1`, in the no-common-root form.** -/
lemma velu_xNumAll_ne_zero_of_H_eq_zero {S : Finset W.Point} (hS : IsPointSubgroup S)
    {a : F} (ha : (veluH S).eval a = 0) : (veluXNumAll S).eval a ≠ 0 := by
  obtain ⟨Q, hQ, rfl⟩ := velu_H_root_iff ha
  rw [veluXNumAll]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, ha,
    mul_zero, zero_add]
  exact mul_ne_zero (inv_ne_zero (by norm_num : (2 : F) ≠ 0))
    (velu_pXAll_eval_ne_zero hS hQ)

/-- **SUB-LEAF 2 (item 5), the `veluPX` half: parity-free `velu_dlog_PX`.** -/
lemma velu_dlog_PXAll {S : Finset W.Point} (hS : IsPointSubgroup S) :
    Polynomial.derivative (veluPXAll S) * veluH S
        - veluPXAll S * Polynomial.derivative (veluH S) = -2 * veluPVAll S := by
  have hC2 : (Polynomial.C (2 : F) : Polynomial F) = 2 := map_ofNat _ 2
  have h2 : (Polynomial.C ((2 : F)⁻¹) : Polynomial F) * 2 = 1 := by
    rw [← hC2, ← Polynomial.C_mul]; norm_num
  rw [veluPXAll, veluPVAll, Polynomial.derivative_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [veluH_factor_all hS hQ]
  rcases eq_or_ne (-Q) Q with h2t | h2t
  · rw [veluEps_of_twoTorsion h2t, veluUTerm_eq_zero_of_neg_eq h2t]
    simp only [pow_zero, mul_one, map_zero, add_zero, pow_one, Polynomial.C_mul,
      Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, zero_mul, add_zero, zero_add, sub_zero,
      one_mul, mul_zero]
    linear_combination (Polynomial.C (veluTTerm W Q) * (veluHq S Q) ^ 2) * h2
  · rw [veluEps_of_not_twoTorsion h2t]
    simp only [show (1 : ℕ) + 1 = 2 from rfl, show 2 * 1 = 2 from rfl, pow_one]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.derivative_pow, Polynomial.C_mul, Nat.cast_ofNat, hC2, sub_zero, mul_one,
      zero_mul, add_zero, zero_add]
    linear_combination (Polynomial.C (veluTTerm W Q) *
      (Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2 * (veluHq S Q) ^ 2) * h2

/-- **SUB-LEAF 2 (item 5): parity-free `velu_dlog_XNum`.** -/
lemma velu_dlog_XNumAll {S : Finset W.Point} (hS : IsPointSubgroup S) :
    Polynomial.derivative (veluXNumAll S) * veluH S
        - veluXNumAll S * Polynomial.derivative (veluH S) = veluXiAll S := by
  have hC2 : (Polynomial.C (2 : F) : Polynomial F) = 2 := map_ofNat _ 2
  have h2 : (Polynomial.C ((2 : F)⁻¹) : Polynomial F) * 2 = 1 := by
    rw [← hC2, ← Polynomial.C_mul]; norm_num
  have hd := velu_dlog_PXAll hS
  rw [veluXNumAll, veluXiAll]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, zero_mul, one_mul, zero_add]
  linear_combination Polynomial.C ((2 : F)⁻¹) * hd - (veluPVAll S) * h2

omit [DecidableEq F] [CharZero F] in
lemma velu_degree_X_sub_C_pow (a : F) (n : ℕ) :
    ((Polynomial.X - Polynomial.C a) ^ n).degree = (n : WithBot ℕ) := by
  have hm : ((Polynomial.X - Polynomial.C a) ^ n).Monic := (Polynomial.monic_X_sub_C a).pow n
  rw [Polynomial.degree_eq_natDegree hm.ne_zero, Polynomial.natDegree_pow,
    Polynomial.natDegree_X_sub_C, mul_one]

omit [CharZero F] in
lemma veluPXAll_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluPXAll S).degree < (veluH S).degree := by
  have hHne : (veluH S) ≠ 0 := (veluH_monic S).ne_zero
  have hbot : (⊥ : WithBot ℕ) < (veluH S).degree :=
    bot_lt_iff_ne_bot.mpr fun h => hHne (Polynomial.degree_eq_bot.mp h)
  rw [veluPXAll]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff hbot]
  intro Q hQ
  have hHq : (veluHq S Q) ≠ 0 := (veluHq_monic S Q).ne_zero
  have hHqbot : (veluHq S Q).degree ≠ ⊥ := fun h => hHq (Polynomial.degree_eq_bot.mp h)
  have hg : (Polynomial.C (veluTTerm W Q)
        * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
      + Polynomial.C (veluUTerm W Q)).degree < ((1 + veluEps Q : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (?_ : _ ≤ ((veluEps Q : ℕ) : WithBot ℕ)) ?_
    · compute_degree!
    · exact_mod_cast (by omega : veluEps Q < 1 + veluEps Q)
  rw [Polynomial.degree_mul, veluH_factor_all hS hQ, Polynomial.degree_mul,
    velu_degree_X_sub_C_pow]
  exact WithBot.add_lt_add_right hHqbot hg

lemma velu_CPXAll_degree_lt {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (Polynomial.C ((2 : F)⁻¹) * veluPXAll S).degree
      < (Polynomial.X * veluH S : Polynomial F).degree := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have h2ne : ((2 : F)⁻¹) ≠ 0 := inv_ne_zero two_ne_zero
  have h1 : (Polynomial.C ((2 : F)⁻¹) * veluPXAll S).degree ≤ (veluPXAll S).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C h2ne, zero_add]
  calc (Polynomial.C ((2 : F)⁻¹) * veluPXAll S).degree ≤ (veluPXAll S).degree := h1
    _ < (veluH S).degree := veluPXAll_degree_lt hS
    _ = ((S.card - 1 : ℕ) : WithBot ℕ) := veluH_degree_eq_card hS
    _ < ((S.card : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : S.card - 1 < S.card)
    _ = (Polynomial.X * veluH S : Polynomial F).degree := (velu_XH_degree hS).symm

lemma veluXNumAll_monic {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluXNumAll S).Monic := by
  rw [veluXNumAll]
  exact ((Polynomial.monic_X).mul (veluH_monic S)).add_of_left (velu_CPXAll_degree_lt hS)

lemma veluXNumAll_degree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluXNumAll S).degree = ((S.card : ℕ) : WithBot ℕ) := by
  rw [veluXNumAll, Polynomial.degree_add_eq_left_of_degree_lt (velu_CPXAll_degree_lt hS),
    velu_XH_degree hS]

end PolePolyAllOrdersChar

section VeluDeltaAlgClosed

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K] [IsAlgClosed K]

/-- **The Vélu quotient model is nonsingular, at EVERY kernel order**, over an
algebraically closed field. -/
theorem velu_curve_Δ_ne_zero_algClosed {V : Affine K} (hΔV : V.Δ ≠ 0)
    {S : Finset V.Point} (hS : IsPointSubgroup S) : (V.veluCurve S).Δ ≠ 0 := by
  intro hΔ
  -- Step 2: the quotient's `2`-division cubic has a repeated root `α`, third root `β`.
  obtain ⟨α, β, hb₂, hb₄, hb₆⟩ :
      ∃ α β : K, (V.veluCurve S).b₂ = -4 * (2 * α + β) ∧
        (V.veluCurve S).b₄ = 2 * (α ^ 2 + 2 * α * β) ∧
        (V.veluCurve S).b₆ = -4 * (α ^ 2 * β) := by
    have ha : (V.veluCurve S).twoTorsionPolynomial.a ≠ 0 := by
      show (4 : K) ≠ 0; norm_num
    have hsplits :
        ((V.veluCurve S).twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits := by
      rw [Polynomial.map_id]; exact IsAlgClosed.splits _
    obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplits
    have hdiscr : (V.veluCurve S).twoTorsionPolynomial.discr = 0 := by
      rw [WeierstrassCurve.twoTorsionPolynomial_discr, hΔ, mul_zero]
    have hne : ¬ (e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃) := fun h =>
      (Cubic.discr_ne_zero_iff_roots_ne ha h3).mpr h hdiscr
    have hp₂ : (V.veluCurve S).b₂ = -4 * (e₁ + e₂ + e₃) := by
      have h := Cubic.b_eq_three_roots ha h3
      simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
      linear_combination h
    have hp₄ : (V.veluCurve S).b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
      have h := Cubic.c_eq_three_roots ha h3
      simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
      linear_combination h / 2
    have hp₆ : (V.veluCurve S).b₆ = -4 * (e₁ * e₂ * e₃) := by
      have h := Cubic.d_eq_three_roots ha h3
      simp only [WeierstrassCurve.twoTorsionPolynomial, RingHom.id_apply] at h
      linear_combination h
    rcases (by tauto : e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃) with h | h | h
    · exact ⟨e₁, e₃, by rw [hp₂, h]; ring, by rw [hp₄, h]; ring, by rw [hp₆, h]; ring⟩
    · exact ⟨e₁, e₂, by rw [hp₂, h]; ring, by rw [hp₄, h]; ring, by rw [hp₆, h]; ring⟩
    · exact ⟨e₂, e₁, by rw [hp₂, h]; ring, by rw [hp₄, h]; ring, by rw [hp₆, h]; ring⟩
  -- the `b`-invariants of the Vélu model
  have eb₂ : (V.veluCurve S).b₂ = V.b₂ := by
    simp only [veluCurve, veluModel, WeierstrassCurve.b₂]
  have eb₄ : (V.veluCurve S).b₄ = V.b₄ - 10 * V.veluT S := by
    simp only [veluCurve, veluModel, WeierstrassCurve.b₄]; ring
  have eb₆ : (V.veluCurve S).b₆ = V.b₆ - 4 * V.b₂ * V.veluT S - 28 * V.veluW S := by
    simp only [veluCurve, veluModel, WeierstrassCurve.b₆, WeierstrassCurve.b₂]; ring
  -- Step 2': `Φnum = 4·G²·K`
  obtain ⟨G, hGdef⟩ : ∃ G : Polynomial K,
      G = veluXNumAll S - Polynomial.C α * veluH S := ⟨_, rfl⟩
  obtain ⟨Kp, hKpdef⟩ : ∃ Kp : Polynomial K,
      Kp = veluXNumAll S - Polynomial.C β * veluH S := ⟨_, rfl⟩
  have hΦ : veluPhiNumAll S = Polynomial.C 4 * G ^ 2 * Kp := by
    have p2 : V.b₂ = -4 * (2 * α + β) := by rw [← eb₂]; exact hb₂
    have p4 : 2 * V.b₄ - 20 * V.veluT S = 4 * (α ^ 2 + 2 * α * β) := by
      have h := hb₄; rw [eb₄] at h; linear_combination 2 * h
    have p6 : V.b₆ - 4 * V.b₂ * V.veluT S - 28 * V.veluW S = -4 * (α ^ 2 * β) := by
      rw [← eb₆]; exact hb₆
    rw [veluPhiNumAll, p6, p4, p2, hGdef, hKpdef]
    simp only [map_neg, map_mul, map_add, map_pow, map_ofNat]
    ring
  -- Step 3: `G` is monic of degree `|S| ≥ 1`, so it has a root `r` in `K`.
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hCα : (Polynomial.C α * veluH S).degree < (veluXNumAll S).degree := by
    have h1 : (Polynomial.C α * veluH S).degree ≤ (veluH S).degree := by
      refine le_trans (Polynomial.degree_mul_le _ _) ?_
      rw [add_comm]
      simpa using add_le_add_right (Polynomial.degree_C_le (a := α)) (veluH S).degree
    refine lt_of_le_of_lt h1 ?_
    rw [veluH_degree_eq_card hS, veluXNumAll_degree hS]
    exact_mod_cast (by omega : S.card - 1 < S.card)
  have hGdeg : G.degree = ((S.card : ℕ) : WithBot ℕ) := by
    rw [hGdef, Polynomial.degree_sub_eq_left_of_degree_lt hCα, veluXNumAll_degree hS]
  have hG0 : G ≠ 0 := fun h => by
    rw [h, Polynomial.degree_zero] at hGdeg; exact absurd hGdeg.symm (by simp)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root G (by rw [hGdeg]; exact_mod_cast (by omega))
  have hroot : G.eval r = 0 := hr
  -- Step 4: `H(r) ≠ 0` — the coprimality sub-leaf.
  have hHr : (veluH S).eval r ≠ 0 := by
    intro hc
    refine velu_xNumAll_ne_zero_of_H_eq_zero hS hc ?_
    rw [hGdef] at hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hc, mul_zero,
      sub_zero] at hroot
    exact hroot
  -- Step 6: the multiplicity of `r` in `G`, and the Wronskian cofactor `E`.
  have hμpos : 0 < G.rootMultiplicity r := (Polynomial.rootMultiplicity_pos hG0).mpr hroot
  obtain ⟨ν, hν⟩ : ∃ ν, G.rootMultiplicity r = ν + 1 := ⟨G.rootMultiplicity r - 1, by omega⟩
  obtain ⟨g, hgdef⟩ : ∃ g : Polynomial K,
      g = G /ₘ (Polynomial.X - Polynomial.C r) ^ G.rootMultiplicity r := ⟨_, rfl⟩
  have hGfac : (Polynomial.X - Polynomial.C r) ^ (ν + 1) * g = G := by
    rw [hgdef, ← hν]; exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq G r
  have hgr : g.eval r ≠ 0 := by
    rw [hgdef]; exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero r hG0
  obtain ⟨E, hEdef⟩ : ∃ E : Polynomial K,
      E = Polynomial.C ((ν : K) + 1) * g * veluH S
        + (Polynomial.X - Polynomial.C r)
            * (Polynomial.derivative g * veluH S
              - g * Polynomial.derivative (veluH S)) := ⟨_, rfl⟩
  have hEr : E.eval r ≠ 0 := by
    have hν1 : ((ν : K) + 1) ≠ 0 := by
      have h : ((ν + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero ν)
      simpa using h
    rw [hEdef]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, sub_self, zero_mul, add_zero]
    exact mul_ne_zero (mul_ne_zero hν1 hgr) hHr
  have hXi : veluXiAll S = (Polynomial.X - Polynomial.C r) ^ ν * E := by
    have hGXi : Polynomial.derivative G * veluH S - G * Polynomial.derivative (veluH S)
        = veluXiAll S := by
      rw [hGdef, ← velu_dlog_XNumAll hS]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
        zero_mul, zero_add]
      ring
    rw [← hGXi, ← hGfac, hEdef]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one, Nat.add_sub_cancel]
    push_cast
    ring
  -- Step 7: cancel `(T − r)^{2ν}` in Vélu's identity and evaluate.
  have hkey : veluPsi V * (veluXiAll S) ^ 2 = veluH S * veluPhiNumAll S := by
    have h := velu_thetaAll_eq_zero hS
    rw [veluThetaAll] at h
    exact sub_eq_zero.mp h
  have hcancel : veluPsi V * E ^ 2
      = (Polynomial.X - Polynomial.C r) ^ 2
        * (Polynomial.C 4 * veluH S * g ^ 2 * Kp) := by
    refine mul_left_cancel₀
      (pow_ne_zero (2 * ν) (Polynomial.X_sub_C_ne_zero (R := K) r)) ?_
    have e1 : veluPsi V * (veluXiAll S) ^ 2
        = (Polynomial.X - Polynomial.C r) ^ (2 * ν) * (veluPsi V * E ^ 2) := by
      rw [hXi]; ring
    have e2 : veluH S * veluPhiNumAll S
        = (Polynomial.X - Polynomial.C r) ^ (2 * ν)
          * ((Polynomial.X - Polynomial.C r) ^ 2
            * (Polynomial.C 4 * veluH S * g ^ 2 * Kp)) := by
      rw [hΦ, ← hGfac]; ring
    rw [← e1, ← e2]; exact hkey
  have hΨr : (veluPsi V).eval r = 0 := by
    have h := congrArg (Polynomial.eval r) hcancel
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at h
    have h0 : (veluPsi V).eval r * (E.eval r) ^ 2 = 0 := by rw [h]; simp
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact h'
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h') hEr
  obtain ⟨P, hP⟩ := Polynomial.dvd_iff_isRoot.mpr hΨr
  have hPr : P.eval r = 0 := by
    have h : (Polynomial.X - Polynomial.C r) * (P * E ^ 2)
        = (Polynomial.X - Polynomial.C r)
          * ((Polynomial.X - Polynomial.C r)
            * (Polynomial.C 4 * veluH S * g ^ 2 * Kp)) := by
      have h0 := hcancel
      rw [hP] at h0
      linear_combination h0
    have h2 := mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (R := K) r) h
    have h3 := congrArg (Polynomial.eval r) h2
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul] at h3
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h') hEr
  have hΨ'r : (Polynomial.derivative (veluPsi V)).eval r = 0 := by
    rw [hP]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
    exact hPr
  -- Step 8: `Ψ(r) = Ψ'(r) = 0` forces `Δ V = 0`.
  have hΨeval : 4 * r ^ 3 + V.b₂ * r ^ 2 + 2 * V.b₄ * r + V.b₆ = 0 := by
    rw [veluPsi] at hΨr
    simpa using hΨr
  have hΨ'eval : 12 * r ^ 2 + 2 * V.b₂ * r + 2 * V.b₄ = 0 := by
    rw [veluPsi] at hΨ'r
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
      Polynomial.derivative_X_pow, Polynomial.derivative_X, zero_mul, zero_add, mul_one,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_zero] at hΨ'r
    linear_combination hΨ'r
  refine hΔV ?_
  have e4 : V.b₄ = -6 * r ^ 2 - V.b₂ * r := by linear_combination hΨ'eval / 2
  have e6 : V.b₆ = 8 * r ^ 3 + V.b₂ * r ^ 2 := by
    linear_combination hΨeval - 2 * r * e4
  have e8 : V.b₈ = -V.b₂ * r ^ 3 - 9 * r ^ 4 := by
    have h := V.b_relation
    rw [e4, e6] at h
    linear_combination h / 4
  simp only [WeierstrassCurve.Δ, e4, e6, e8]
  ring

end VeluDeltaAlgClosed

section VeluAllOrders

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

/-- **PROVEN 2026-07-27, parity-free: the Vélu quotient MODEL is nonsingular, at EVERY
kernel order.**

The route recorded below was carried out in full. Both sub-leaves it names are now closed:
item 4 is `velu_xNumAll_ne_zero_of_H_eq_zero` (over `velu_pXAll_eval_ne_zero`,
`veluHq_eval_self_ne_zero`, `veluHq_eval_other_eq_zero`, `veluUTerm_neg`, `veluHq_neg`,
`veluUTerm_ne_zero_of_neg_ne`) and item 5 is `velu_dlog_XNumAll` (over `velu_dlog_PXAll`).
**The refuting check named at the end of this audit was run first and PASSED**: at
`ε_Q = 0` the `Q`-summand of `PXAll'·H − PXAll·H'` is `−(t_Q + u_Q)·h²` while `−2·(Q`-summand
of `PVAll)` is `−(2u_Q + t_Q)·h²`, and these agree precisely because
`veluUTerm_eq_zero_of_neg_eq` gives `u_Q = 0` there — so the parity-free Wronskian identity
holds and the route is sound. The mathematics lives in
`velu_curve_Δ_ne_zero_algClosed`; this statement is its base change to `AlgebraicClosure F`
(`velu_baseChange_curve`, `map_Δ`, and injectivity of `algebraMap` into a field extension).

This is the whole remaining content of Vélu's theorem in the parity-free path. It is stated
over the BASE field and as a scalar inequation: the three-`2`-torsion-points packaging of
`velu_exists_three_twoTorsion_of_subgroup` and its base change to `AlgebraicClosure F` are
formal, and are discharged below by `exists_three_twoTorsion_of_Δ_ne_zero`.

**CORRECTION TO THE PREVIOUS AUDIT (which pointed at a dead end).** The audit of 2026-07-27
proposed producing the three `2`-torsion points of the quotient from points `R` of order `4`
with `2R ∈ S`, and then noted — correctly — that the group structure of the quotient is not
available, since `Affine.Point`'s group instance is exactly what `IsElliptic` is being
established for. It also noted, correctly, that a `2`-torsion `T` INSIDE the kernel collapses
`W[2]`: `T ↦ 0` and the other two `2`-torsion points `T'`, `T' + T` have the SAME image, so
`W[2]` contributes only ONE nonzero `2`-torsion point to the quotient. Both observations
stand. What the audit did not see is that the order-`4` route is not needed at all, and that
the "alternative route" it dismissed in one line — compute `Δ ≠ 0` directly — is elementary
and uses only material already in this file.

**THE ROUTE, in full (a Wronskian/multiplicity argument; no group theory, no order-`4`
points, no geometry of the quotient).** Work over `L = AlgebraicClosure F` with
`S' = S.image (veluBaseChangePoint W L)`, and abbreviate, all in `L[T]`,

  `H = veluH S'`, `N = veluXNumAll S'`, `Ξ = veluXiAll S'`, `Ψ = veluPsi (W⁄L)`,
  `Φnum = veluPhiNumAll S'`.

1. **The identity.** `Ψ·Ξ² = H·Φnum` — this is `veluThetaAll S' = 0`, PROVEN (2026-07-27),
   and it is the only place the whole `PolePoly` layer is used.
2. **Suppose `Δ (veluCurve W S) = 0`.** Over `L` the `2`-division cubic
   `Φ(X) = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)` of the quotient splits
   (`Cubic.splits_iff_roots_eq_three`) and has `discr = 16·Δ = 0`, so two of its roots
   coincide (`Cubic.discr_ne_zero_iff_roots_ne`): `Φ = 4(X − α)²(X − β)`. Reading the
   coefficients off `Cubic.b_eq_three_roots` / `c_` / `d_` — exactly as in
   `exists_three_twoTorsion_of_Δ_ne_zero` — and clearing denominators gives, by `ring`,
   `Φnum = 4·G²·K` with `G = N − C α·H` and `K = N − C β·H`.
3. **`G` has a root.** `G` is monic of degree `|S|` (`N` is monic of degree `|S|`, `H` of
   degree `|S| − 1`), so `deg G ≥ 1` and `L` algebraically closed supplies a root `r`.
4. **`H(r) ≠ 0`** — this is the coprimality `gcd(N, H) = 1`, a NEW parity-free sub-leaf. At a
   root `a = x_Q` of `H` every summand of `veluPXAll` with `x_{Q'} ≠ a` still carries the
   factor `(T − a)^{1+ε}` inside `veluHq S' Q'`, so only the fibre `{Q, −Q}` survives, and
   `PXAll(a) = 2u_Q·Hq_Q(a)` when `ε_Q = 1` (`u_Q ≠ 0` off `2`-torsion) and `t_Q·Hq_Q(a)`
   when `ε_Q = 0` (`veluTTerm_ne_zero_of_neg_eq`). Both are nonzero, and
   `N = T·H + ½·PXAll`, so `N(a) ≠ 0`.
5. **The Wronskian.** `Ξ = N'·H − N·H'` — the parity-free `velu_dlog_XNum`, the second NEW
   sub-leaf. Termwise as in `velu_dlog_PX`, with `veluH_factor_all` in place of
   `veluH_factor`: writing `d = T − x_Q`, `h = veluHq S' Q`, the `Q`-summand of
   `PXAll'·H − PXAll·H'` is `−d·h²·(t_Q d + 2u_Q)` at `ε_Q = 1` and `−(t_Q + u_Q)·h²` at
   `ε_Q = 0`, against `−2·(Q`-summand of `PVAll)` equal to `−d·h²(t_Q d + 2u_Q)` and
   `−(2u_Q + t_Q)·h²`. The two agree at `ε_Q = 0` PRECISELY BECAUSE `u_Q = 0` there
   (`veluUTerm_eq_zero_of_neg_eq`) — the identity is FALSE termwise without it, which is why
   this is a genuine sub-leaf and not a copy. Since `G' H − G H' = N' H − N H'`, also
   `Ξ = G'·H − G·H'`.
6. **Multiplicity.** Let `μ = rootMultiplicity r G ≥ 1` and `g = G /ₘ (T − r)^μ`, so
   `G = (T − r)^μ·g` with `g(r) ≠ 0` (`pow_mul_divByMonic_rootMultiplicity_eq`,
   `eval_divByMonic_pow_rootMultiplicity_ne_zero`). Then
   `Ξ = (T − r)^{μ−1}·E` with `E = C μ·g·H + (T − r)(g'H − gH')` and
   `E(r) = μ·g(r)·H(r) ≠ 0` — characteristic `0` is used exactly here.
7. **Cancel and evaluate.** `Ψ·(T−r)^{2μ−2}E² = 4H(T−r)^{2μ}g²K` cancels to
   `Ψ·E² = 4H·(T−r)²·g²·K` in the domain `L[T]`. Evaluating at `r` gives `Ψ(r) = 0`;
   differentiating and evaluating at `r` gives `Ψ'(r)·E(r)² = 0`, hence `Ψ'(r) = 0`.
8. **Contradiction.** `Ψ(r) = Ψ'(r) = 0` for `Ψ = 4T³ + b₂T² + 2b₄T + b₆` forces
   `b₄ = −6r² − b₂r`, `b₆ = 8r³ + b₂r²`, hence `4b₈ = b₂b₆ − b₄²` gives
   `b₈ = −b₂r³ − 9r⁴` and `Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = 0` by `ring`. But
   `Δ (W⁄L) = algebraMap F L (Δ W) ≠ 0` because `W` is elliptic. ∎

So the leaf reduces to **two** new sub-leaves, item 4 (`gcd(veluXNumAll S, veluH S) = 1`, in
the "no common root" form) and item 5 (the parity-free `velu_dlog_XNum`), plus bookkeeping.
Neither needs anything outside this file. **The check that would refute this audit** is item
5's termwise identity at `ε_Q = 0`: if `(t_Q + u_Q)·h²` did not equal `(2u_Q + t_Q)·h²` after
`veluUTerm_eq_zero_of_neg_eq`, the Wronskian identity would fail parity-free and the whole
route would collapse; `linear_combination` on that one line settles it. -/
theorem velu_curve_Δ_ne_zero (S : Finset W.Point) (hS : IsPointSubgroup S) :
    (W.veluCurve S).Δ ≠ 0 := by
  classical
  intro hΔ
  haveI : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  refine velu_curve_Δ_ne_zero_algClosed
    (V := (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)))
    (WeierstrassCurve.isUnit_Δ
      (W := (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)))).ne_zero
    (velu_baseChange_isPointSubgroup hS) ?_
  rw [← velu_baseChange_curve (L := AlgebraicClosure F) S,
    show ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Δ =
      algebraMap F (AlgebraicClosure F) (W.veluCurve S).Δ from
      WeierstrassCurve.map_Δ (W := W.veluCurve S) (f := algebraMap F (AlgebraicClosure F)),
    hΔ, map_zero]

/-- **PROVEN 2026-07-27 over `velu_curve_Δ_ne_zero`: three `2`-torsion points on the
quotient, at EVERY kernel order** — the parity-free form of `velu_exists_three_twoTorsion`.

The odd-order proof pushed the three `2`-torsion points of `W` through the Vélu map; that
route is UNAVAILABLE parity-free, because a `2`-torsion `T` inside the kernel maps to `0` and
identifies the other two `2`-torsion points of `W`, so `W[2]` contributes only one nonzero
`2`-torsion point to the quotient (see the audit on `velu_curve_Δ_ne_zero`). Instead the
three points are produced on the quotient MODEL directly, from `Δ ≠ 0` by
`exists_three_twoTorsion_of_Δ_ne_zero` — which is the exact converse of the
`isElliptic_of_three_twoTorsion` that consumes this statement, so nothing is lost. The base
change is formal: `Δ (W'⁄L) = algebraMap F L (Δ W')` and `algebraMap` into a field extension
is injective. -/
theorem velu_exists_three_twoTorsion_of_subgroup (S : Finset W.Point)
    (hS : IsPointSubgroup S) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃ : AlgebraicClosure F,
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₁ y₁ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₂ y₂ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₃ y₃ ∧
      y₁ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₁ y₁ ∧
      y₂ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₂ y₂ ∧
      y₃ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₃ y₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  refine exists_three_twoTorsion_of_Δ_ne_zero
    ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) ?_
  rw [show ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Δ =
      algebraMap F (AlgebraicClosure F) (W.veluCurve S).Δ from
    WeierstrassCurve.map_Δ (W := W.veluCurve S) (f := algebraMap F (AlgebraicClosure F))]
  exact fun h => velu_curve_Δ_ne_zero W S hS
    ((injective_iff_map_eq_zero (algebraMap F (AlgebraicClosure F))).mp
      (algebraMap F (AlgebraicClosure F)).injective _ h)

/-- **TARGET PROVEN 2026-07-27: the Vélu quotient curve is elliptic, at EVERY kernel
order** — an assembly over the leaf `velu_exists_three_twoTorsion_of_subgroup` and the
already-proven `isElliptic_of_three_twoTorsion`, exactly as in the odd case.

`Δ ≠ 0` is detected after base change to the algebraic closure, since
`Δ (W'⁄L) = algebraMap F L (Δ W')` and `algebraMap` into a field extension is injective. -/
theorem velu_isElliptic_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S) :
    (W.veluCurve S).IsElliptic := by
  obtain ⟨x₁, x₂, x₃, y₁, y₂, y₃, he₁, he₂, he₃, ht₁, ht₂, ht₃, d₁₂, d₁₃, d₂₃⟩ :=
    velu_exists_three_twoTorsion_of_subgroup W S hS
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

omit [W.IsElliptic] in
/-- **PROVEN 2026-07-27, parity-free.** `velu_equation_pole` with `hodd` DELETED: the
statement in pole form, from which the point form follows by `velu_coordX_eq` and
`velu_coordY_eq`. The proof is the odd-order one verbatim, over
`velu_pole_identity_of_subgroup` in place of `velu_pole_identity`. -/
theorem velu_equation_pole_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (W.veluCurve S).Equation
      (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q)
      (veluPointY P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleY W (veluPointX P) (veluPointY P) Q) := by
  have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact hS.zero_mem)
  have hEq : W.Equation (veluPointX P) (veluPointY P) := by
    obtain _ | ⟨x, y, hns⟩ := P
    · exact absurd rfl hP0
    · exact hns.1
  have hV := velu_pole_V hS hP
  have hI := velu_pole_identity_of_subgroup hS hP
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
/-- **TARGET PROVEN 2026-07-27: Vélu's coordinates satisfy the quotient equation, at EVERY
kernel order** — the parity-free form of `velu_equation`, over the single leaf
`velu_thetaAll_local_dvd` and its sibling `velu_thetaAll_degree_lt`.

By `velu_coordX_eq` and `velu_coordY_eq` — both already parity-free — this reduces exactly
as in the odd case to `velu_equation_pole_of_subgroup`. -/
theorem velu_equation_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (W.veluCurve S).Equation (W.veluCoordX S P) (W.veluCoordY S P) := by
  rw [velu_coordX_eq hS hP, velu_coordY_eq hS hP]
  exact W.velu_equation_pole_of_subgroup S hS hP

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

/-! ### Additivity at EVERY kernel order: the reduction to the parity-free `addX` identity

(2026-07-27.)  The formal half of `velu_map_add_of_subgroup` is parity-free VERBATIM: the
kernel cases, additivity-up-to-sign, and the promotion of the `addX` identity to a point
identity all mirror the odd-order proofs with `hodd` simply deleted.  So the whole content
of `velu_map_add_of_subgroup` is the two leaves cut here,

* `velu_coord_ne_neg_of_subgroup` — injectivity of the Vélu coordinates modulo the kernel;
* `velu_coordX_add_eq_addX_of_subgroup` — the `addX` identity.

**What those two actually need**, established while proving the odd-order `POLY` above; this
is a route map, not an obstruction claim, and each item is a checkable statement:

1. `velu_xNum_sub_eq_prod` in parity-free form — `veluXNumAll S − X_P·H = ∏_{Q∈S}(T − x(P+Q))`.
   For an arbitrary kernel the roots repeat at `2`-torsion, so `velu_fibrePoly_monic` and
   `velu_fiber_card` must be re-derived from `veluH_factor_all` / `velu_fiber_card_all`
   (both already PROVEN).  Everything downstream of this in the odd development consumes it
   only as "the fibre polynomial", so this is the single largest item.
2. `velu_wronskian` in parity-free form — `veluXNumAll'·H − veluXNumAll·H' = veluXiAll`.
   `veluXNumAll_eval` and `veluXiAll_eval` are already PROVEN, so this is a polynomial
   identity in the same style as `velu_dlog_PX`, with the `ε_Q` exponents of `veluPXAll` /
   `veluPVAll` in place of the odd-order ones.
3. Given 1 and 2, **the whole `POLY` trace calculus above transfers unchanged**: it uses
   `hodd` ONLY through those two, plus `veluXNum_eval` / `veluXi_eval` (whose `All` forms are
   proven) and parity-free facts (`veluH_eval_ne_zero`, `veluCoordX_add_mem`,
   `veluCoordY_add_mem`, `velu_add_notMem`).  In particular `velu_key_wronskian`,
   `velu_trace_even_fibre` and `velu_trace_odd_fibre` mirror directly, and the degenerate
   fibre case (`2P ∈ S`) is already handled parity-free.
4. ~~**`STAR` changes SIGN.**~~ **REFUTED 2026-07-27 — `STAR` is parity-free VERBATIM, and so
   is `HNORM`'s `c² = κ`.**  This item claimed that `velu_norm_line_mul_neg` picks up a factor
   `(−1)^{|S|}`, so that a parity-free `velu_hnorm` would have to read `c² = (−1)^{|S|+1}·κ`
   and that `c² = κ` is FALSE for even `|S|`.  **That is wrong, and the error is a
   MISCOUNT: `(−1)^{|S|}` enters the proof FOUR times, not once.**

   The item counted only the explicit `hodd.neg_one_pow` in `velu_norm_line_mul_neg`'s own
   body (the `hsplit` step, which pulls `(−1)^{|S|}` out of `∏_{Q∈S} −(f₁f₂f₃)`).  But each
   of the THREE `velu_fibre_prod_sub_point` rewrites that follow carries one more, because
   `velu_fibre_prod_sub` reverses `∏(x(P+Q) − c)` into `∏(c − x(P+Q))` and consumes
   `hodd.neg_one_pow` internally.  In parity-free form, with `e := (−1)^{|S|}`,

     `∏_{Q∈S}(x(P+Q) − x_T) = e·H(x_T)·(X T − X P) = −e·H(x_T)·(X P − X T)`,

   so the three fibre products contribute `(−e)³` and `hsplit` contributes `e`, giving
   `e·(−e³) = −e⁴ = −1` since `e = ±1`.  The four occurrences cancel and the conclusion is
   the odd one unchanged:  `N(P)·N(−P) = −κ·ρ(X P)`, for EVERY `|S|`.

   `velu_norm_line_mul_neg_all` below is exactly that statement and is PROVEN; the only
   change from the odd proof is that `hodd.neg_one_pow` is replaced by
   `he4 : ((−1)^{|S|})⁴ = 1` in the closing `linear_combination`.  Consequently
   `velu_hnorm_all` carries `c² = κ` with **no** sign correction, since the `T³`-coefficient
   comparison reads `−4β² = 4σκ` with `σ = −1` at every order.

Everything else in this route map was correct, and items 1–3 transferred as predicted. -/

/-- **PROVEN, parity-free: the arbitrary-order Vélu map commutes with negation.** -/
lemma veluMapAll_neg (S : Finset W.Point) (hS : IsPointSubgroup S) (P : W.Point) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (-P) = -W.veluMapAll S hS P := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  by_cases hP : P ∈ S
  · rw [W.veluMapAll_of_mem hS hP, W.veluMapAll_of_mem hS (hS.neg_mem _ hP), neg_zero]
  · rw [W.veluMapAll_of_notMem hS (velu_neg_notMem W hS hP),
      W.veluMapAll_of_notMem hS hP, Affine.Point.neg_some]
    exact velu_point_some_eq (veluCoordX_neg hS P) (veluCoordY_neg hS hP)

/-- **PROVEN, parity-free: additivity UP TO SIGN implies additivity.** The mirror of
`velu_map_add_of_add_eq_neg`; the argument is entirely inside the quotient group. -/
theorem velu_map_add_of_add_eq_neg_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hpm : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
      W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q ∨
      W.veluMapAll S hS (P + Q) = -(W.veluMapAll S hS P + W.veluMapAll S hS Q))
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  rcases hpm P Q hP hQ hPQ with h | h
  · exact h
  have hnP : -P ∉ S := velu_neg_notMem W hS hP
  have hnQ : -Q ∉ S := velu_neg_notMem W hS hQ
  have hnegP : W.veluMapAll S hS (-P) = -W.veluMapAll S hS P := veluMapAll_neg W S hS P
  have hnegQ : W.veluMapAll S hS (-Q) = -W.veluMapAll S hS Q := veluMapAll_neg W S hS Q
  have e₁ : P + Q + -Q = P := by abel
  have h₁ := hpm (P + Q) (-Q) hPQ hnQ (by rw [e₁]; exact hP)
  rw [e₁, h, hnegQ] at h₁
  have e₂ : P + Q + -P = Q := by abel
  have h₂ := hpm (P + Q) (-P) hPQ hnP (by rw [e₂]; exact hQ)
  rw [e₂, h, hnegP] at h₂
  have hkey : W.veluMapAll S hS P + W.veluMapAll S hS Q
      + (W.veluMapAll S hS P + W.veluMapAll S hS Q) = 0 := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · linear_combination (norm := abel) h₁
    · linear_combination (norm := abel) h₁
    · linear_combination (norm := abel) h₂
    · linear_combination (norm := abel) -h₁ - h₂
  rw [h]
  exact (add_eq_zero_iff_eq_neg.mp hkey).symm

omit [W.IsElliptic] in
/-- Parity-free Wronskian. -/
theorem velu_wronskian_all (S : Finset W.Point) (hS : IsPointSubgroup S) :
    Polynomial.derivative (veluXNumAll S) * veluH S
        - veluXNumAll S * Polynomial.derivative (veluH S) = veluXiAll S := by
  have h2C : Polynomial.C (2 : F) = (2 : Polynomial F) := map_ofNat Polynomial.C 2
  have hc : (2 : Polynomial F) * Polynomial.C ((2 : F)⁻¹) = 1 := by
    rw [← h2C, ← Polynomial.C_mul]
    norm_num
  have hterm : ∀ Q ∈ S.erase 0,
      Polynomial.derivative
            ((Polynomial.C (veluTTerm W Q)
                * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
              + Polynomial.C (veluUTerm W Q)) * veluHq S Q) * veluH S
          - ((Polynomial.C (veluTTerm W Q)
                * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
              + Polynomial.C (veluUTerm W Q)) * veluHq S Q)
            * Polynomial.derivative (veluH S)
        = -2 * ((Polynomial.C (veluUTerm W Q)
                * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ veluEps Q
              + Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
                * (Polynomial.X - Polynomial.C (veluPointX Q)) ^ (2 * veluEps Q))
            * (veluHq S Q) ^ 2) := by
    intro Q hQ
    have hct : (2 : Polynomial F) * Polynomial.C ((2 : F)⁻¹ * veluTTerm W Q)
        = Polynomial.C (veluTTerm W Q) := by
      rw [← h2C, ← Polynomial.C_mul]
      congr 1
      field_simp
    rw [veluH_factor_all hS hQ]
    rcases eq_or_ne (-Q) Q with h2 | h2
    · rw [veluEps_of_twoTorsion h2, veluUTerm_eq_zero_of_neg_eq h2]
      simp only [pow_zero, mul_one, map_zero, zero_mul, add_zero, zero_add, Nat.mul_zero,
        pow_one, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X,
        sub_zero, one_mul]
      linear_combination (veluHq S Q) ^ 2 * hct
    · rw [veluEps_of_not_twoTorsion h2]
      simp only [show (1 : ℕ) + 1 = 2 from rfl, show 2 * (1 : ℕ) = 2 from rfl, pow_one]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X,
        Polynomial.derivative_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, sub_zero,
        zero_mul, add_zero, zero_add, mul_one, h2C]
      linear_combination ((Polynomial.X - Polynomial.C (veluPointX Q)) ^ 2
        * (veluHq S Q) ^ 2) * hct
  have key : Polynomial.derivative (veluPXAll S) * veluH S
      - veluPXAll S * Polynomial.derivative (veluH S) = -2 * veluPVAll S := by
    rw [veluPXAll, veluPVAll, Polynomial.derivative_sum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [veluXNumAll, veluXiAll]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, zero_mul, one_mul, zero_add]
  linear_combination Polynomial.C ((2 : F)⁻¹) * key - veluPVAll S * hc

omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free degree of `veluHq`. -/
lemma velu_Hq_natDegree_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {Q : W.Point} (hQ : Q ∈ S.erase 0) :
    (veluHq S Q).natDegree + (1 + veluEps Q) = S.card - 1 := by
  have hfac := veluH_factor_all hS hQ
  have hHne : veluH S ≠ 0 := (veluH_monic S).ne_zero
  have hHq0 : veluHq S Q ≠ 0 := by
    intro h; rw [h, mul_zero] at hfac; exact hHne hfac
  have hpow : ((X - C (veluPointX Q)) ^ (1 + veluEps Q) : Polynomial F) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero _)
  have hd := congrArg Polynomial.natDegree hfac
  rw [natDegree_mul hpow hHq0, natDegree_pow, natDegree_X_sub_C, veluH_natDegree hS] at hd
  omega

omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free degree bound on `veluPXAll`. -/
lemma velu_PXAll_natDegree_le {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluPXAll S).natDegree ≤ S.card - 2 := by
  rw [veluPXAll]
  refine natDegree_sum_le_of_forall_le _ _ (fun Q hQ => ?_)
  refine le_trans natDegree_mul_le ?_
  have hlin : (C (veluTTerm W Q) * (X - C (veluPointX Q)) ^ veluEps Q
      + C (veluUTerm W Q)).natDegree ≤ veluEps Q := by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (natDegree_C_mul_le _ _) ?_
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · simp
  have hq := velu_Hq_natDegree_all W hS hQ
  omega

omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free: the fibre polynomial is monic of degree `|S|`. -/
lemma velu_fibrePoly_monic_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    (P : W.Point) :
    (veluXNumAll S - C (W.veluCoordX S P) * veluH S).Monic ∧
      (veluXNumAll S - C (W.veluCoordX S P) * veluH S).natDegree = S.card := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hHm : (veluH S).Monic := veluH_monic S
  have hlin : (X - C (W.veluCoordX S P)).Monic := monic_X_sub_C _
  have hmul : ((X - C (W.veluCoordX S P)) * veluH S).Monic := hlin.mul hHm
  have hdeg : ((X - C (W.veluCoordX S P)) * veluH S).natDegree = S.card := by
    rw [natDegree_mul hlin.ne_zero hHm.ne_zero, natDegree_X_sub_C, veluH_natDegree hS]
    omega
  have hsplit : veluXNumAll S - C (W.veluCoordX S P) * veluH S
      = (X - C (W.veluCoordX S P)) * veluH S + C ((2 : F)⁻¹) * veluPXAll S := by
    rw [veluXNumAll]; ring
  have hPXdeg : (C ((2 : F)⁻¹) * veluPXAll S).degree
      < ((X - C (W.veluCoordX S P)) * veluH S).degree := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [degree_eq_natDegree hmul.ne_zero, hdeg]
    have h1 : (C ((2 : F)⁻¹) * veluPXAll S).natDegree ≤ S.card - 2 :=
      le_trans (natDegree_C_mul_le _ _) (velu_PXAll_natDegree_le W hS)
    exact_mod_cast lt_of_le_of_lt h1 (by omega)
  have hdegadd : ((X - C (W.veluCoordX S P)) * veluH S + C ((2 : F)⁻¹) * veluPXAll S).degree
      = ((X - C (W.veluCoordX S P)) * veluH S).degree :=
    degree_add_eq_left_of_degree_lt hPXdeg
  refine ⟨by rw [hsplit]; exact hmul.add_of_left hPXdeg, ?_⟩
  rw [hsplit, natDegree_eq_of_degree_eq hdegadd]
  exact hdeg

omit [W.IsElliptic] in
/-- Parity-free `veluXNumAll` evaluation, in `veluCoordX` form. -/
lemma veluXNumAll_eval' {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (veluXNumAll S).eval (veluPointX P)
      = (veluH S).eval (veluPointX P) * W.veluCoordX S P := by
  rw [veluXNumAll_eval hS hP, velu_coordX_eq hS hP]

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free `H·G' = Ξ` on the fibre. -/
lemma velu_H_mul_deriv_fibrePoly_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P R : W.Point} (hR : R ∉ S)
    (hXeq : W.veluCoordX S R = W.veluCoordX S P) :
    (veluH S).eval (veluPointX R)
        * (derivative (veluXNumAll S - C (W.veluCoordX S P) * veluH S)).eval (veluPointX R)
      = (veluXiAll S).eval (veluPointX R) := by
  have hw := congrArg (Polynomial.eval (veluPointX R)) (velu_wronskian_all W S hS)
  simp only [eval_sub, eval_mul] at hw
  have hGeval : (veluXNumAll S).eval (veluPointX R)
      = (veluH S).eval (veluPointX R) * W.veluCoordX S P := by
    rw [veluXNumAll_eval' W hS hR, hXeq]
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, eval_sub,
    eval_mul, eval_C]
  rw [← hw, hGeval]
  ring

omit [W.IsElliptic] in
/-- Parity-free: a fibre collision forces `Ξ` to vanish. -/
lemma velu_xi_eval_eq_zero_of_two_mem_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {R : W.Point} (hR : R ∉ S) (h2 : R + R ∈ S) (hne : R + R ≠ 0) :
    (veluXiAll S).eval (veluPointX R) = 0 := by
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
  rw [veluXiAll_eval hS hR, hD, mul_zero]

omit [W.IsElliptic] in
/-- Parity-free fibre-product identity. -/
theorem velu_xNumAll_sub_eq_prod (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    veluXNumAll S - Polynomial.C (W.veluCoordX S P) * veluH S
      = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))) := by
  classical
  set G : Polynomial F := veluXNumAll S - Polynomial.C (W.veluCoordX S P) * veluH S with hG
  obtain ⟨hGm, hGdeg⟩ := velu_fibrePoly_monic_all W hS P
  have hroot : ∀ Q ∈ S, G.IsRoot (veluPointX (P + Q)) := by
    intro Q hQ
    have hPQ : P + Q ∉ S := velu_add_notMem hS hP hQ
    rw [Polynomial.IsRoot, hG]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [veluXNumAll_eval' W hS hPQ, veluCoordX_add_mem hS P hQ]
    ring
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
        have hHG := velu_H_mul_deriv_fibrePoly_all W hS (P := P)
          (velu_add_notMem hS hP hQ₁S) hXeq
        rw [velu_xi_eval_eq_zero_of_two_mem_all W hS (velu_add_notMem hS hP hQ₁S)
          h2PQ hne2] at hHG
        exact (mul_eq_zero.mp hHG).resolve_left hH
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

omit [W.IsElliptic] in
/-- Parity-free: `Ξ(x_P) = 0` forces `2P ∈ S`. -/
theorem velu_two_mem_of_xiAll_eq_zero (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S)
    (h : (veluXiAll S).eval (veluPointX P) = 0) : P + P ∈ S := by
  classical
  have hH : (veluH S).eval (veluPointX P) ≠ 0 := veluH_eval_ne_zero hS hP
  set G : Polynomial F := veluXNumAll S - Polynomial.C (W.veluCoordX S P) * veluH S with hG
  have hderiv : (veluH S).eval (veluPointX P) * (Polynomial.derivative G).eval (veluPointX P)
      = (veluXiAll S).eval (veluPointX P) :=
    velu_H_mul_deriv_fibrePoly_all W hS hP rfl
  have hG' : (Polynomial.derivative G).eval (veluPointX P) = 0 := by
    have hz := hderiv
    rw [h] at hz
    exact (mul_eq_zero.mp hz).resolve_left hH
  have hprod : G = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))) :=
    velu_xNumAll_sub_eq_prod W S hS hP
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

omit [W.IsElliptic] in
/-- **PROVEN 2026-07-27: injectivity of the Vélu coordinates modulo the kernel, at EVERY
kernel order.** The parity-free form of `velu_coord_ne_neg`.

Its odd-order proof is short and goes entirely through `velu_xNum_sub_eq_prod`: `X(−Q) =
X(P)` makes `x(−Q)` a root of the fibre polynomial of `P`, hence `−Q ∈ P + S`, hence
`P + Q ∈ S`. So this leaf was exactly item 1 of the route map above and nothing else, and
once `velu_xNumAll_sub_eq_prod` was available it mirrored VERBATIM.

The one place the even case genuinely differs is inside `velu_xNumAll_sub_eq_prod` itself,
and it costs nothing: the fibre multiplicity bookkeeping never asks WHICH parity it is in.
The odd docstring's count ("exactly one fixed point `Q*`, since doubling is a bijection on a
group of odd order") is a description of the odd case, not a step of the proof — the proof
regroups the coset product fibrewise, bounds each fibre by `2` from
`x(P+Q₁) = x(P+Q₂) ⟹ 2P + Q₁ + Q₂ = 0`, and discharges a doubled root through
`velu_xi_eval_eq_zero_of_two_mem_all`. At even order the degenerate fibres are no longer
rare, and that is the only change. -/
theorem velu_coord_ne_neg_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    ¬(W.veluCoordX S P = W.veluCoordX S Q ∧
      W.veluCoordY S P = (W.veluCurve S).negY (W.veluCoordX S Q) (W.veluCoordY S Q)) := by
  classical
  rintro ⟨hx, hy⟩
  have hnQ : -Q ∉ S := fun h => hQ (by simpa using hS.neg_mem _ h)
  have hxR : W.veluCoordX S (-Q) = W.veluCoordX S P := by
    rw [veluCoordX_neg hS, hx]
  have hprod := velu_xNumAll_sub_eq_prod W S hS hP
  have hroot : (∏ Q' ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q')))).eval
      (veluPointX (-Q)) = 0 := by
    rw [← hprod]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [veluXNumAll_eval' W hS hnQ, hxR]
    ring
  rw [Polynomial.eval_prod] at hroot
  obtain ⟨Q₀, hQ₀S, hQ₀⟩ := Finset.prod_eq_zero_iff.mp hroot
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ₀
  have hxQ₀ : veluPointX (-Q) = veluPointX (P + Q₀) := sub_eq_zero.mp hQ₀
  have hnQ0 : -Q ≠ 0 := fun h => hnQ (h ▸ hS.zero_mem)
  rcases velu_pointX_eq_iff hnQ0 (velu_add_ne_zero W hS hP hQ₀S) hxQ₀ with h1 | h1
  · refine hPQ ?_
    have hPQeq : P + Q = -Q₀ := by linear_combination (norm := abel) -h1
    rw [hPQeq]; exact hS.neg_mem _ hQ₀S
  · have hQeq : Q = P + Q₀ := by linear_combination (norm := abel) -h1
    have hXQ : W.veluCoordX S Q = W.veluCoordX S P := by
      rw [hQeq, veluCoordX_add_mem hS P hQ₀S]
    have hYQ : W.veluCoordY S Q = W.veluCoordY S P := by
      rw [hQeq, veluCoordY_add_mem hS P hQ₀S]
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
      · have hPne : P ≠ 0 := fun h => hP (h ▸ hS.zero_mem)
        have h0 : P + P = 0 := by
          cases P with
          | zero => exact absurd rfl hPne
          | some x y hns =>
              simp only [veluPointX_some, veluPointY_some] at hL
              have hyy : y = W.negY x y := by
                simp only [WeierstrassCurve.Affine.negY]; linear_combination hL
              exact Affine.Point.add_of_Y_eq rfl hyy
        rw [h0]; exact hS.zero_mem
      · refine velu_two_mem_of_xiAll_eq_zero W S hS hP ?_
        rw [veluXiAll_eval hS hP, hR, mul_zero]
    refine hPQ ?_
    have hPQeq : P + Q = (P + P) + Q₀ := by rw [hQeq]; abel
    rw [hPQeq]; exact hS.add_mem _ h2P _ hQ₀S

/-- **PROVEN, parity-free.** `velu_coord_ne_neg_of_subgroup` supplies the nondegeneracy
`φ(P) + φ(Q) ≠ 0`. Mirror of `velu_map_add_ne_zero`. -/
lemma velu_map_add_ne_zero_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S)
    (hcoord : ¬(W.veluCoordX S P = W.veluCoordX S Q ∧
      W.veluCoordY S P
        = (W.veluCurve S).negY (W.veluCoordX S Q) (W.veluCoordY S Q))) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS P + W.veluMapAll S hS Q ≠ 0 := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  intro h
  have h1 : W.veluMapAll S hS P = W.veluMapAll S hS (-Q) := by
    rw [veluMapAll_neg W S hS Q]; exact add_eq_zero_iff_eq_neg.mp h
  rw [W.veluMapAll_of_notMem hS hP,
    W.veluMapAll_of_notMem hS (velu_neg_notMem W hS hQ)] at h1
  obtain ⟨hx, hy⟩ := (Affine.Point.some.injEq ..).mp h1
  exact hcoord ⟨by rw [hx, veluCoordX_neg hS Q], by rw [hy, veluCoordY_neg hS hQ]⟩

omit [W.IsElliptic] in
/-- Parity-free fibre product. -/
lemma velu_fibre_prod_sub_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (c : F) :
    ∏ Q ∈ S, (veluPointX (P + Q) - c)
      = (-1 : F) ^ S.card
        * ((veluXNumAll S).eval c - W.veluCoordX S P * (veluH S).eval c) := by
  have hkey := congrArg (Polynomial.eval c) (velu_xNumAll_sub_eq_prod W S hS hP)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_X] at hkey
  have hneg : ∏ Q ∈ S, (veluPointX (P + Q) - c)
      = (-1 : F) ^ S.card * ∏ Q ∈ S, (c - veluPointX (P + Q)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => by ring
  rw [hneg]
  linear_combination (-((-1 : F) ^ S.card)) * hkey

omit [W.IsElliptic] in
/-- Parity-free fibre product at a point outside the kernel. -/
lemma velu_fibre_prod_sub_point_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) {T : W.Point} (hT : T ∉ S) :
    ∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T)
      = (-1 : F) ^ S.card
        * ((veluH S).eval (veluPointX T) * (W.veluCoordX S T - W.veluCoordX S P)) := by
  rw [velu_fibre_prod_sub_all W S hS hP, veluXNumAll_eval' W hS hT]
  ring

omit [W.IsElliptic] in
/-- STAR, parity-free: the sign does NOT change. -/
lemma velu_norm_line_mul_neg_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (x₀ y₀ ℓ : F)
    {T₁ T₂ T₃ : W.Point} (h₁ : T₁ ∉ S) (h₂ : T₂ ∉ S) (h₃ : T₃ ∉ S)
    (hfac : W.addPolynomial x₀ y₀ ℓ
      = -((Polynomial.X - Polynomial.C (veluPointX T₁))
          * (Polynomial.X - Polynomial.C (veluPointX T₂))
          * (Polynomial.X - Polynomial.C (veluPointX T₃)))) :
    (∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)))
      * (∏ Q ∈ S, (veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀)))
      = -((veluH S).eval (veluPointX T₁) * (veluH S).eval (veluPointX T₂)
            * (veluH S).eval (veluPointX T₃))
        * ((W.veluCoordX S P - W.veluCoordX S T₁) * (W.veluCoordX S P - W.veluCoordX S T₂)
            * (W.veluCoordX S P - W.veluCoordX S T₃)) := by
  classical
  have hre : (∏ Q ∈ S, (veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀)))
      = ∏ Q ∈ S, (veluPointY (-(P + Q)) - (ℓ * (veluPointX (-(P + Q)) - x₀) + y₀)) := by
    rw [← velu_prod_neg W hS
      (fun Q => veluPointY (-P + Q) - (ℓ * (veluPointX (-P + Q) - x₀) + y₀))]
    exact Finset.prod_congr rfl fun Q _ => by
      rw [show (-P + -Q : W.Point) = -(P + Q) by abel]
  have hstep : ∀ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀))
        * (veluPointY (-(P + Q)) - (ℓ * (veluPointX (-(P + Q)) - x₀) + y₀))
      = -((veluPointX (P + Q) - veluPointX T₁) * (veluPointX (P + Q) - veluPointX T₂)
            * (veluPointX (P + Q) - veluPointX T₃)) := by
    intro Q hQ
    have hPQ : P + Q ∉ S := velu_add_notMem hS hP hQ
    have hPQ0 : P + Q ≠ 0 := fun h => hPQ (h ▸ hS.zero_mem)
    rw [velu_line_pair W x₀ y₀ ℓ hPQ0, hfac]
    simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hre, ← Finset.prod_mul_distrib, Finset.prod_congr rfl hstep]
  have hsplit : (∏ Q ∈ S, -((veluPointX (P + Q) - veluPointX T₁)
        * (veluPointX (P + Q) - veluPointX T₂) * (veluPointX (P + Q) - veluPointX T₃)))
      = (-1 : F) ^ S.card * ((∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₁))
          * (∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₂))
          * (∏ Q ∈ S, (veluPointX (P + Q) - veluPointX T₃))) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => by ring
  have he4 : ((-1 : F) ^ S.card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm S.card 4, pow_mul]
    norm_num
  rw [hsplit, velu_fibre_prod_sub_point_all W S hS hP h₁,
    velu_fibre_prod_sub_point_all W S hS hP h₂, velu_fibre_prod_sub_point_all W S hS hP h₃]
  linear_combination (-((veluH S).eval (veluPointX T₁) * (veluH S).eval (veluPointX T₂)
      * (veluH S).eval (veluPointX T₃))
    * ((W.veluCoordX S P - W.veluCoordX S T₁) * (W.veluCoordX S P - W.veluCoordX S T₂)
        * (W.veluCoordX S P - W.veluCoordX S T₃))) * he4

/- INTEGRATION NOTE (2026-07-27).  The three lemmas that follow were proven
independently of, and in the same release as, the same-named trio far above
(`velu_CPXAll_degree_lt`, `veluXNumAll_monic`, `veluXNumAll_degree`).  Both
branches landed in DISJOINT regions of this file, so the merge was textually
clean and produced three DUPLICATE declarations — a hard "already declared"
error that no frontier scan can see.

They are NOT interchangeable, which is why both are kept rather than one
deleted: the copies here `omit [CharZero F] [W.IsElliptic]` and so are
strictly more general, and their consumer `veluGenFibrePolyAll_monic` omits
those instances too, so it cannot call the earlier versions.  The earlier
versions in turn cannot be deleted, because their own consumers sit ~1000
lines ABOVE these and `velu_PXAll_natDegree_le` — which the proofs here
need — is not declared until line ~8874.

Renamed with a `_charFree` suffix at integration.  CONSOLIDATION IS OWED:
the right end state is one trio, stated in the `omit`ed form, hoisted above
the earliest consumer, with `velu_PXAll_natDegree_le` hoisted with it.  That
is a single-owner reordering task in this file. -/
omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
lemma velu_CPXAll_degree_lt_charFree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (C ((2 : F)⁻¹) * veluPXAll S).degree < (X * veluH S : Polynomial F).degree := by
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [velu_XH_degree hS]
  have h1 : (C ((2 : F)⁻¹) * veluPXAll S).natDegree ≤ S.card - 2 :=
    le_trans (natDegree_C_mul_le _ _) (velu_PXAll_natDegree_le W hS)
  exact_mod_cast lt_of_le_of_lt h1 (by omega)

omit [CharZero F] [W.IsElliptic] in
lemma veluXNumAll_monic_charFree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluXNumAll S).Monic := by
  rw [veluXNumAll]
  exact ((Polynomial.monic_X).mul (veluH_monic S)).add_of_left (velu_CPXAll_degree_lt_charFree W hS)

omit [CharZero F] [W.IsElliptic] in
lemma veluXNumAll_degree_charFree {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluXNumAll S).degree = ((S.card : ℕ) : WithBot ℕ) := by
  rw [veluXNumAll, Polynomial.degree_add_eq_left_of_degree_lt (velu_CPXAll_degree_lt_charFree W hS),
    velu_XH_degree hS]

omit [W.IsElliptic] in
/-- Parity-free `W_P · H(x_P)² = w_P · Ξ(x_P)`. -/
lemma velu_coordW_mul_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) :
    (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * ((veluH S).eval (veluPointX P)) ^ 2
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) * (veluXiAll S).eval (veluPointX P) := by
  have hV : 2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
    rw [velu_coordX_eq hS hP, velu_coordY_eq hS hP]
    exact velu_pole_V hS hP
  rw [hV, veluXiAll_eval hS hP]
  ring

/-- The parity-free Vélu fibre polynomial at `P`. -/
noncomputable abbrev veluFibrePolyAll (S : Finset W.Point) (P : W.Point) : Polynomial F :=
  veluXNumAll S - Polynomial.C (W.veluCoordX S P) * veluH S

omit [W.IsElliptic] in
/-- Parity-free KEY IDENTITY: `w_R · f_P'(x_R) = W_P · H(x_R)` across the whole fibre. -/
lemma velu_key_wronskian_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) {Q : W.Point} (hQ : Q ∈ S) :
    (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
        * (Polynomial.derivative (veluFibrePolyAll W S P)).eval (veluPointX (P + Q))
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * (veluH S).eval (veluPointX (P + Q)) := by
  have hR : P + Q ∉ S := velu_add_notMem hS hP hQ
  have hX : W.veluCoordX S (P + Q) = W.veluCoordX S P := veluCoordX_add_mem hS P hQ
  have hY : W.veluCoordY S (P + Q) = W.veluCoordY S P := veluCoordY_add_mem hS P hQ
  have hH : (veluH S).eval (veluPointX (P + Q)) ≠ 0 := veluH_eval_ne_zero hS hR
  set ξ := veluPointX (P + Q) with hξ
  have hd : (Polynomial.derivative (veluFibrePolyAll W S P)).eval ξ * (veluH S).eval ξ
      = (veluXiAll S).eval ξ := by
    have hw := congrArg (Polynomial.eval ξ) (velu_wronskian_all W S hS)
    have hXN : (veluXNumAll S).eval ξ = (veluH S).eval ξ * W.veluCoordX S P := by
      rw [veluXNumAll_eval' W hS hR, hX]
    simp only [veluFibrePolyAll, Polynomial.derivative_sub, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hw ⊢
    linear_combination hw + (Polynomial.derivative (veluH S)).eval ξ * hXN
  have hW := velu_coordW_mul_all W hS hR
  rw [hX, hY] at hW
  have hcancel : ((2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃)
        * (Polynomial.derivative (veluFibrePolyAll W S P)).eval ξ) * (veluH S).eval ξ
      = ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) * (veluH S).eval ξ)
        * (veluH S).eval ξ := by
    calc ((2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃)
          * (Polynomial.derivative (veluFibrePolyAll W S P)).eval ξ) * (veluH S).eval ξ
        = (2 * veluPointY (P + Q) + W.a₁ * ξ + W.a₃) * (veluXiAll S).eval ξ := by
          rw [← hd]; ring
      _ = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
            * ((veluH S).eval ξ) ^ 2 := hW.symm
      _ = ((2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) * (veluH S).eval ξ)
            * (veluH S).eval ξ := by ring
  exact mul_right_cancel₀ hH hcancel

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free even trace over the Vélu fibre. -/
lemma velu_trace_even_fibre_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (h : Polynomial F) :
    ∑ Q ∈ S, h.eval (veluPointX (P + Q))
      = ((h * Polynomial.derivative (veluFibrePolyAll W S P))
          %ₘ (veluFibrePolyAll W S P)).coeff (S.card - 1) := by
  classical
  have hprod : veluFibrePolyAll W S P = ∏ Q ∈ S, (X - C (veluPointX (P + Q))) :=
    velu_xNumAll_sub_eq_prod W S hS hP
  rw [hprod]
  exact velu_trace_even S (fun Q => veluPointX (P + Q)) h

omit [W.IsElliptic] in
open _root_.Polynomial in
/-- Parity-free ODD TRACE over the Vélu fibre. -/
lemma velu_trace_odd_fibre_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P : W.Point} (hP : P ∉ S) (β : Polynomial F) :
    ∑ Q ∈ S, β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
        * ((β * veluH S) %ₘ (veluFibrePolyAll W S P)).coeff (S.card - 1) := by
  classical
  by_cases h2 : P + P ∈ S
  · rw [velu_trace_odd_fibre_zero W hS hP h2 β, velu_coordW_eq_zero_of_two_mem W hS hP h2,
      zero_mul]
  · have hprod : veluFibrePolyAll W S P = ∏ Q ∈ S, (X - C (veluPointX (P + Q))) :=
      velu_xNumAll_sub_eq_prod W S hS hP
    have hinj : ∀ Q₁ ∈ S, ∀ Q₂ ∈ S,
        veluPointX (P + Q₁) = veluPointX (P + Q₂) → Q₁ = Q₂ := by
      intro Q₁ h₁ Q₂ h₂ hx
      have hn₁ : P + Q₁ ≠ 0 := velu_add_ne_zero W hS hP h₁
      have hn₂ : P + Q₂ ≠ 0 := velu_add_ne_zero W hS hP h₂
      rcases velu_pointX_eq_iff hn₁ hn₂ hx with h | h
      · exact add_left_cancel h
      · exfalso
        refine h2 ?_
        have hz : (P + Q₁) + (P + Q₂) = 0 := by rw [h]; exact neg_add_cancel _
        have h' : (P + P) + (Q₁ + Q₂) = 0 := by rw [← hz]; abel
        rw [add_eq_zero_iff_eq_neg] at h'
        rw [h', neg_add]
        exact hS.add_mem _ (hS.neg_mem _ h₁) _ (hS.neg_mem _ h₂)
    have hk : ∀ Q ∈ S,
        (β.eval (veluPointX (P + Q))
            * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃))
          * (Polynomial.derivative
              (∏ Q' ∈ S, (X - C (veluPointX (P + Q'))))).eval (veluPointX (P + Q))
        = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃)
          * (β * veluH S).eval (veluPointX (P + Q)) := by
      intro Q hQ
      have hkw := velu_key_wronskian_all W hS hP hQ
      rw [hprod] at hkw
      simp only [Polynomial.eval_mul]
      linear_combination β.eval (veluPointX (P + Q)) * hkw
    rw [hprod]
    exact velu_trace_odd S (fun Q => veluPointX (P + Q)) hinj (β * veluH S)
      (fun Q => β.eval (veluPointX (P + Q))
        * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃))
      (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) hk

/-- The parity-free GENERIC fibre polynomial over `F[χ]`. -/
noncomputable def veluGenFibrePolyAll (S : Finset W.Point) : Polynomial (Polynomial F) :=
  (veluXNumAll S).map Polynomial.C
    - Polynomial.C (Polynomial.X : Polynomial F) * (veluH S).map Polynomial.C

omit [W.IsElliptic] [CharZero F] in
lemma veluGenFibrePolyAll_map (S : Finset W.Point) (ξ : F) :
    (veluGenFibrePolyAll W S).map (Polynomial.evalRingHom ξ)
      = veluXNumAll S - Polynomial.C ξ * veluH S := by
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [veluGenFibrePolyAll, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.map_id]
  simp

omit [CharZero F] [W.IsElliptic] in
open _root_.Polynomial in
lemma veluGenFibrePolyAll_monic {S : Finset W.Point} (hS : IsPointSubgroup S) :
    (veluGenFibrePolyAll W S).Monic := by
  have hCinj : Function.Injective (Polynomial.C : F →+* Polynomial F) :=
    fun _ _ h => Polynomial.C_inj.mp h
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, hS.zero_mem⟩
  have hXNmon : ((veluXNumAll S).map Polynomial.C).Monic := (veluXNumAll_monic_charFree W hS).map _
  have hXNdeg : ((veluXNumAll S).map Polynomial.C).degree = ((S.card : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective hCinj, veluXNumAll_degree_charFree W hS]
  have hHdeg : ((veluH S).map Polynomial.C).degree = (((S.card - 1 : ℕ)) : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective hCinj,
      Polynomial.degree_eq_natDegree (veluH_monic S).ne_zero, veluH_natDegree hS]
  rw [veluGenFibrePolyAll, sub_eq_add_neg]
  refine hXNmon.add_of_left ?_
  rw [Polynomial.degree_neg, hXNdeg]
  calc (Polynomial.C (Polynomial.X : Polynomial F) * (veluH S).map Polynomial.C).degree
      ≤ (Polynomial.C (Polynomial.X : Polynomial F)).degree
          + ((veluH S).map Polynomial.C).degree := degree_mul_le _ _
    _ ≤ 0 + (((S.card - 1 : ℕ)) : WithBot ℕ) := add_le_add degree_C_le (le_of_eq hHdeg)
    _ < ((S.card : ℕ) : WithBot ℕ) := by
        have hlt : S.card - 1 < S.card := by omega
        rw [zero_add]
        exact_mod_cast hlt

omit [W.IsElliptic] in
/-- Parity-free UNIFORM EVEN TRACE. -/
lemma velu_exists_trace_even_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    (h : Polynomial F) :
    ∃ u : Polynomial F, ∀ P : W.Point, P ∉ S →
      ∑ Q ∈ S, h.eval (veluPointX (P + Q)) = u.eval (W.veluCoordX S P) := by
  refine ⟨(((h.map Polynomial.C) * Polynomial.derivative (veluGenFibrePolyAll W S))
      %ₘ (veluGenFibrePolyAll W S)).coeff (S.card - 1), ?_⟩
  intro P hP
  rw [velu_trace_even_fibre_all W hS hP h]
  set ξ := W.veluCoordX S P with hξ
  have hstep : ∀ (p : Polynomial (Polynomial F)) (k : ℕ),
      Polynomial.eval ξ (p.coeff k) = (p.map (Polynomial.evalRingHom ξ)).coeff k := by
    intro p k
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [hstep, Polynomial.map_modByMonic _ (veluGenFibrePolyAll_monic W hS), Polynomial.map_mul,
    Polynomial.map_map, hcomp, Polynomial.map_id, ← Polynomial.derivative_map,
    veluGenFibrePolyAll_map W S ξ]

omit [W.IsElliptic] in
/-- Parity-free UNIFORM ODD TRACE. -/
lemma velu_exists_trace_odd_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    (β : Polynomial F) :
    ∃ v : Polynomial F, ∀ P : W.Point, P ∉ S →
      ∑ Q ∈ S, β.eval (veluPointX (P + Q))
          * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)
        = v.eval (W.veluCoordX S P)
          * (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) := by
  refine ⟨((((β * veluH S).map Polynomial.C)) %ₘ (veluGenFibrePolyAll W S)).coeff (S.card - 1),
    ?_⟩
  intro P hP
  rw [velu_trace_odd_fibre_all W hS hP β]
  set ξ := W.veluCoordX S P with hξ
  have hstep : ∀ (p : Polynomial (Polynomial F)) (k : ℕ),
      Polynomial.eval ξ (p.coeff k) = (p.map (Polynomial.evalRingHom ξ)).coeff k := by
    intro p k
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  have hcomp : (Polynomial.evalRingHom ξ).comp (Polynomial.C : F →+* Polynomial F)
      = RingHom.id F := by ext a; simp
  rw [hstep, Polynomial.map_modByMonic _ (veluGenFibrePolyAll_monic W hS),
    Polynomial.map_map, hcomp, Polynomial.map_id, veluGenFibrePolyAll_map W S ξ]
  exact mul_comm _ _

omit [W.IsElliptic] in
lemma veluRepr_mul_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {g₁ g₂ : W.Point → F} (h₁ : VeluRepr W S g₁) (h₂ : VeluRepr W S g₂) :
    VeluRepr W S (fun P => g₁ P * g₂ P) := by
  obtain ⟨u₁, v₁, e₁⟩ := h₁
  obtain ⟨u₂, v₂, e₂⟩ := h₂
  refine ⟨u₁ * u₂ + v₁ * v₂ * (veluPsi (W.veluCurve S)), u₁ * v₂ + u₂ * v₁, fun P hP => ?_⟩
  have hW : (veluPsi (W.veluCurve S)).eval (W.veluCoordX S P)
      = (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) ^ 2 := by
    have := velu_psi_eval_eq (W := W.veluCurve S) (W.velu_equation_of_subgroup S hS hP)
    rwa [veluCurve_a₁, veluCurve_a₃] at this
  show g₁ P * g₂ P = _
  rw [e₁ P hP, e₂ P hP]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hW]
  ring

omit [W.IsElliptic] in
/-- Parity-free: power sums of the line function over the fibre are represented. -/
lemma veluRepr_powersum_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    (x₀ y₀ ℓ : F) (k : ℕ) :
    VeluRepr W S (fun P => ∑ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ k) := by
  obtain ⟨α, β, hαβ⟩ := velu_exists_line_pow W x₀ y₀ ℓ k
  set γ : Polynomial F := α - Polynomial.C (2⁻¹ : F)
    * (β * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)) with hγ
  obtain ⟨u, hu⟩ := velu_exists_trace_even_all W S hS γ
  obtain ⟨v, hv⟩ := velu_exists_trace_odd_all W S hS β
  refine ⟨u, Polynomial.C (2⁻¹ : F) * v, fun P hP => ?_⟩
  show (∑ Q ∈ S, _) = _
  have hterm : ∀ Q ∈ S,
      (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ k
        = γ.eval (veluPointX (P + Q))
          + (2⁻¹ : F) * (β.eval (veluPointX (P + Q))
              * (2 * veluPointY (P + Q) + W.a₁ * veluPointX (P + Q) + W.a₃)) := by
    intro Q hQ
    have hne : P + Q ≠ 0 := velu_add_ne_zero W hS hP hQ
    rw [hαβ _ hne, hγ]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    hu P hP, hv P hP]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

omit [W.IsElliptic] in
/-- Parity-free: every elementary symmetric function of the line values is represented. -/
lemma veluRepr_esymm_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    (x₀ y₀ ℓ : F) (k : ℕ) :
    VeluRepr W S (fun P => ∑ t ∈ Finset.powersetCard k
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀))) := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine veluRepr_congr W (g₂ := fun _ => (1 : F)) (fun P _ => ?_) (veluRepr_const W S 1)
      simp
    · set val : W.Point → {Q : W.Point // Q ∈ S} → F := fun P i =>
        veluPointY (P + (i : W.Point))
          - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀) with hval
      have hnewton : ∀ P : W.Point,
          (k : F) * (∑ t ∈ Finset.powersetCard k
              (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
            = (-1) ^ (k + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
                (-1) ^ a.1
                  * (∑ t ∈ Finset.powersetCard a.1
                      (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                  * (∑ i, val P i ^ a.2) := by
        intro P
        have h := congrArg (MvPolynomial.aeval (val P))
          (MvPolynomial.mul_esymm_eq_sum {Q : W.Point // Q ∈ S} F k)
        simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
          velu_aeval_esymm, velu_aeval_psum] using h
      have hrepr : VeluRepr W S (fun P => (-1) ^ (k + 1)
          * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
              (-1) ^ a.1
                * (∑ t ∈ Finset.powersetCard a.1
                    (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                * (∑ i, val P i ^ a.2)) := by
        refine veluRepr_mul_all W hS (veluRepr_const W S ((-1) ^ (k + 1))) ?_
        refine veluRepr_sum W _ _ (fun a ha => ?_)
        have ha1 : a.1 < k := (Finset.mem_filter.mp ha).2
        refine veluRepr_mul_all W hS
          (veluRepr_mul_all W hS (veluRepr_const W S ((-1) ^ a.1)) (ih a.1 ha1)) ?_
        refine veluRepr_congr W (g₂ := fun P => ∑ Q ∈ S,
          (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ a.2)
          (fun P _ => ?_) (veluRepr_powersum_all W hS x₀ y₀ ℓ a.2)
        exact Finset.sum_coe_sort S (fun Q => (veluPointY (P + Q)
          - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) ^ a.2)
      have hkne : (k : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      refine veluRepr_congr W (g₂ := fun P => (k : F)⁻¹ * ((-1) ^ (k + 1)
          * ∑ a ∈ {a ∈ Finset.antidiagonal k | a.1 < k},
              (-1) ^ a.1
                * (∑ t ∈ Finset.powersetCard a.1
                    (Finset.univ : Finset {Q : W.Point // Q ∈ S}), ∏ i ∈ t, val P i)
                * (∑ i, val P i ^ a.2)))
        (fun P _ => ?_) (veluRepr_mul_all W hS (veluRepr_const W S ((k : F)⁻¹)) hrepr)
      rw [← hnewton P, inv_mul_cancel_left₀ hkne]

omit [W.IsElliptic] in
/-- POLY, parity-free. -/
lemma velu_norm_line_eq_poly_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    (x₀ y₀ ℓ : F) :
    ∃ a b : Polynomial F, ∀ P : W.Point, P ∉ S →
      (∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)))
        = a.eval (W.veluCoordX S P) + b.eval (W.veluCoordX S P) * W.veluCoordY S P := by
  classical
  obtain ⟨u, v, huv⟩ := veluRepr_esymm_all W hS x₀ y₀ ℓ S.card
  refine ⟨u + v * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃),
    Polynomial.C 2 * v, fun P hP => ?_⟩
  have hcard : (Finset.univ : Finset {Q : W.Point // Q ∈ S}).card = S.card := by simp
  have hpc : Finset.powersetCard S.card (Finset.univ : Finset {Q : W.Point // Q ∈ S})
      = {Finset.univ} := by
    rw [← hcard]; exact Finset.powersetCard_self _
  have hprod : (∑ t ∈ Finset.powersetCard S.card
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀)))
      = ∏ Q ∈ S, (veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀)) := by
    rw [hpc, Finset.sum_singleton]
    exact Finset.prod_coe_sort S
      (fun Q => veluPointY (P + Q) - (ℓ * (veluPointX (P + Q) - x₀) + y₀))
  have h : (∑ t ∈ Finset.powersetCard S.card
        (Finset.univ : Finset {Q : W.Point // Q ∈ S}),
      ∏ i ∈ t, (veluPointY (P + (i : W.Point))
        - (ℓ * (veluPointX (P + (i : W.Point)) - x₀) + y₀)))
      = u.eval (W.veluCoordX S P) + v.eval (W.veluCoordX S P)
        * (2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃) := huv P hP
  rw [← hprod, h]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

omit [W.IsElliptic] in
/-- Parity-free: the fibres of the Vélu `x`-coordinate are small. -/
lemma velu_pointX_mem_of_coordX_eq_all {S : Finset W.Point} (hS : IsPointSubgroup S)
    {P P' : W.Point} (hP : P ∉ S) (hP' : P' ∉ S)
    (h : W.veluCoordX S P = W.veluCoordX S P') :
    veluPointX P' ∈ S.image (fun Q => veluPointX (P + Q)) := by
  classical
  have hprod := velu_xNumAll_sub_eq_prod W S hS hP
  have hprod' := velu_xNumAll_sub_eq_prod W S hS hP'
  rw [← h] at hprod'
  have heqprod : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q))))
      = ∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P' + Q))) := hprod.symm.trans hprod'
  have hz : (∏ Q ∈ S, (Polynomial.X - Polynomial.C (veluPointX (P + Q)))).eval
      (veluPointX P') = 0 := by
    rw [heqprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero hS.zero_mem (by simp)
  rw [Polynomial.eval_prod] at hz
  obtain ⟨Q, hQ, hQ0⟩ := Finset.prod_eq_zero_iff.mp hz
  refine Finset.mem_image.mpr ⟨Q, hQ, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hQ0
  exact (sub_eq_zero.mp hQ0).symm

/-- Parity-free: three admissible points with pairwise distinct Vélu `x`-coordinates. -/
lemma velu_exists_three_coordX_all [IsAlgClosed F] (S : Finset W.Point)
    (hS : IsPointSubgroup S) :
    ∃ P₀ P₁ P₂ : W.Point, P₀ ∉ S ∧ P₁ ∉ S ∧ P₂ ∉ S
      ∧ W.veluCoordX S P₀ ≠ W.veluCoordX S P₁
      ∧ W.veluCoordX S P₀ ≠ W.veluCoordX S P₂
      ∧ W.veluCoordX S P₁ ≠ W.veluCoordX S P₂ := by
  classical
  have step : ∀ Bad : Finset F, ∃ P : W.Point, P ∉ S ∧ veluPointX P ∉ Bad := by
    intro Bad
    obtain ⟨P, hP⟩ := velu_exists_point_notMem W (Bad ∪ S.image veluPointX)
    exact ⟨P, fun hc => hP (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)),
      fun hc => hP (Finset.mem_union_left _ hc)⟩
  obtain ⟨P₀, hP₀, -⟩ := step ∅
  obtain ⟨P₁, hP₁, h1⟩ := step (S.image (fun Q => veluPointX (P₀ + Q)))
  obtain ⟨P₂, hP₂, h2⟩ := step ((S.image (fun Q => veluPointX (P₀ + Q)))
      ∪ (S.image (fun Q => veluPointX (P₁ + Q))))
  exact ⟨P₀, P₁, P₂, hP₀, hP₁, hP₂,
    fun h => h1 (velu_pointX_mem_of_coordX_eq_all W hS hP₀ hP₁ h),
    fun h => h2 (Finset.mem_union_left _ (velu_pointX_mem_of_coordX_eq_all W hS hP₀ hP₂ h)),
    fun h => h2 (Finset.mem_union_right _
      (velu_pointX_mem_of_coordX_eq_all W hS hP₁ hP₂ h))⟩

/-- Parity-free: arbitrarily many distinct admissible Vélu `x`-coordinates. -/
lemma velu_exists_coordX_values_all [IsAlgClosed F] (S : Finset W.Point)
    (hS : IsPointSubgroup S) (k : ℕ) :
    ∃ t : Finset F, t.card = k ∧ ∀ ξ ∈ t, ∃ P : W.Point, P ∉ S ∧ W.veluCoordX S P = ξ := by
  classical
  have step : ∀ Bad : Finset F, ∃ P : W.Point, P ∉ S ∧ veluPointX P ∉ Bad := by
    intro Bad
    obtain ⟨P, hP⟩ := velu_exists_point_notMem W (Bad ∪ S.image veluPointX)
    exact ⟨P, fun hc => hP (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)),
      fun hc => hP (Finset.mem_union_left _ hc)⟩
  induction k with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨t, hcard, hw⟩ := ih
    choose f hf1 hf2 using hw
    obtain ⟨P, hPS, hPBad⟩ :=
      step (t.attach.biUnion fun ξ => S.image fun Q => veluPointX (f ξ.1 ξ.2 + Q))
    have hnew : W.veluCoordX S P ∉ t := by
      intro hmem
      refine hPBad (Finset.mem_biUnion.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, ?_⟩)
      exact velu_pointX_mem_of_coordX_eq_all W hS (hf1 _ hmem) hPS ((hf2 _ hmem).trans rfl)
    refine ⟨insert (W.veluCoordX S P) t, by rw [Finset.card_insert_of_notMem hnew, hcard], ?_⟩
    intro ξ hξ
    rcases Finset.mem_insert.mp hξ with h | h
    · exact ⟨P, hPS, h.symm⟩
    · exact ⟨f ξ h, hf1 ξ h, hf2 ξ h⟩

omit [W.IsElliptic] in
/-- STAR for the secant, parity-free. -/
theorem velu_norm_line_mul_neg_slope_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S)
    {P : W.Point} (hP : P ∉ S) :
    (∏ Q ∈ S, (veluPointY (P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
      * (∏ Q ∈ S, (veluPointY (-P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (-P + Q) - veluPointX A) + veluPointY A)))
      = -((veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
            * (veluH S).eval (veluPointX (A + B)))
        * ((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) := by
  have hA0 : A ≠ 0 := fun h => hA (h ▸ hS.zero_mem)
  have hB0 : B ≠ 0 := fun h => hB (h ▸ hS.zero_mem)
  have heqA : W.Equation (veluPointX A) (veluPointY A) := velu_point_equation W hA0
  have heqB : W.Equation (veluPointX B) (veluPointY B) := velu_point_equation W hB0
  have hxy : ¬(veluPointX A = veluPointX B
      ∧ veluPointY A = W.negY (veluPointX B) (veluPointY B)) :=
    velu_point_ne_negY W hS hA hB hAB
  have hxAB : veluPointX (A + B)
      = W.addX (veluPointX A) (veluPointX B)
          (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)) := by
    cases A with
    | zero => exact absurd rfl hA0
    | some xa ya ha =>
      cases B with
      | zero => exact absurd rfl hB0
      | some xb yb hb =>
        simp only [veluPointX_some, veluPointY_some] at hxy ⊢
        rw [Affine.Point.add_some hxy]
        rfl
  refine velu_norm_line_mul_neg_all W S hS hP (veluPointX A) (veluPointY A) _ hA hB hAB ?_
  rw [Affine.addPolynomial_slope heqA heqB hxy, hxAB]

/-- HNORM, parity-free: `c² = κ`, with NO sign correction. -/
theorem velu_hnorm_all [IsAlgClosed F] (S : Finset W.Point) (hS : IsPointSubgroup S)
    {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S) :
    ∃ c lam mu : F,
      c ^ 2 = (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
          * (veluH S).eval (veluPointX (A + B))
      ∧ ∀ P : W.Point, P ∉ S →
          (∏ Q ∈ S, (veluPointY (P + Q)
            - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
                * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
            = c * (W.veluCoordY S P - (lam * W.veluCoordX S P + mu)) := by
  classical
  set V := W.veluCurve S with hV
  set κ := (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
      * (veluH S).eval (veluPointX (A + B)) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact veluH_eval_ne_zero hS hA
    · exact veluH_eval_ne_zero hS hB
    · exact veluH_eval_ne_zero hS hAB
  obtain ⟨a, b, hab⟩ := velu_norm_line_eq_poly_all W S hS (veluPointX A) (veluPointY A)
    (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B))
  set AA : Polynomial F :=
    Polynomial.C (2 : F) * a - b * (Polynomial.C V.a₁ * Polynomial.X + Polynomial.C V.a₃) with hAA
  set ΦV : Polynomial F :=
    Polynomial.C (4 : F) * Polynomial.X ^ 3
      + Polynomial.C (4 * V.a₂ + V.a₁ ^ 2) * Polynomial.X ^ 2
      + Polynomial.C (4 * V.a₄ + 2 * V.a₁ * V.a₃) * Polynomial.X
      + Polynomial.C (4 * V.a₆ + V.a₃ ^ 2) with hΦV
  set ρ : Polynomial F :=
    (Polynomial.X - Polynomial.C (W.veluCoordX S A))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
      * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B))) with hρ
  set D : Polynomial F := AA ^ 2 - b ^ 2 * ΦV + Polynomial.C (4 * κ) * ρ with hD
  have hDval : ∀ P : W.Point, P ∉ S → D.eval (W.veluCoordX S P) = 0 := by
    intro P hP
    have hnP : -P ∉ S := fun hc => hP (by simpa using hS.neg_mem _ hc)
    have h1 := hab P hP
    have h2 := hab (-P) hnP
    rw [veluCoordX_neg hS P, veluCoordY_neg hS hP] at h2
    have h3 := velu_norm_line_mul_neg_slope_all W S hS hA hB hAB hP
    rw [h1, h2] at h3
    have h4 := W.velu_equation_of_subgroup S hS hP
    rw [Affine.equation_iff] at h4
    simp only [hD, hAA, hΦV, hρ, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Affine.negY] at h3 h4 ⊢
    linear_combination (4 : F) * h3 + 4 * (b.eval (W.veluCoordX S P)) ^ 2 * h4
  have hD0 : D = 0 := by
    obtain ⟨t, hcard, hw⟩ := velu_exists_coordX_values_all W S hS (D.natDegree + 1)
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D t ?_ (by omega)
    intro ξ hξ
    obtain ⟨P, hP, rfl⟩ := hw ξ hξ
    exact hDval P hP
  have hkey : AA ^ 2 - b ^ 2 * ΦV = Polynomial.C (-(4 * κ)) * ρ := by
    have h := hD0
    rw [hD] at h
    rw [map_neg, neg_mul, ← sub_eq_zero]
    linear_combination h
  have hρmonic : ρ.Monic := by
    rw [hρ]
    exact ((Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _)).mul
      (Polynomial.monic_X_sub_C _)
  have hρdeg : ρ.natDegree = 3 := by rw [hρ]; compute_degree!
  have hrhsdeg : (Polynomial.C (-(4 * κ)) * ρ).natDegree = 3 := by
    rw [Polynomial.natDegree_C_mul (by simpa using hκ0), hρdeg]
  have hΦdeg : ΦV.natDegree = 3 := by rw [hΦV]; compute_degree!
  have hΦ0 : ΦV ≠ 0 := fun h => by simp [h] at hΦdeg
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb] at hkey
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      sub_zero] at hkey
    have h := congrArg Polynomial.natDegree hkey
    rw [Polynomial.natDegree_pow, hrhsdeg] at h
    omega
  have hbΦdeg : (b ^ 2 * ΦV).natDegree = 2 * b.natDegree + 3 := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ hb0) hΦ0, Polynomial.natDegree_pow, hΦdeg]
  have hAAdeg : (AA ^ 2).natDegree = 2 * AA.natDegree := Polynomial.natDegree_pow _ _
  have hlt : (AA ^ 2).natDegree < (b ^ 2 * ΦV).natDegree := by
    rcases lt_trichotomy ((AA ^ 2).natDegree) ((b ^ 2 * ΦV).natDegree) with h | h | h
    · exact h
    · rw [hAAdeg, hbΦdeg] at h; omega
    · exfalso
      have h' : (AA ^ 2 - b ^ 2 * ΦV).natDegree = (AA ^ 2).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt h
      rw [hkey, hrhsdeg, hAAdeg] at h'
      omega
  have hbdeg : b.natDegree = 0 := by
    have h := Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt
    have h2 : (b ^ 2 * ΦV - AA ^ 2).natDegree = 3 := by
      rw [show b ^ 2 * ΦV - AA ^ 2 = -(AA ^ 2 - b ^ 2 * ΦV) by ring, Polynomial.natDegree_neg,
        hkey, hrhsdeg]
    rw [h2, hbΦdeg] at h
    omega
  have hAAle : AA.natDegree ≤ 1 := by
    have h := hlt
    rw [hAAdeg, hbΦdeg, hbdeg] at h
    omega
  obtain ⟨β, hβ⟩ : ∃ β : F, b = Polynomial.C β :=
    ⟨b.coeff 0, (Polynomial.eq_C_of_natDegree_eq_zero hbdeg)⟩
  have hβ0 : β ≠ 0 := by rintro rfl; exact hb0 (by simpa using hβ)
  have hρ3 : ρ.coeff 3 = 1 := by
    have h' := hρmonic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hρdeg] at h'
    exact h'
  have hβκ : β ^ 2 = κ := by
    have h : (AA ^ 2 - b ^ 2 * ΦV).coeff 3 = (Polynomial.C (-(4 * κ)) * ρ).coeff 3 := by
      rw [hkey]
    have hA3 : (AA ^ 2).coeff 3 = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hAAdeg]; omega)
    have hΦ3 : ΦV.coeff 3 = 4 := by
      rw [hΦV]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [Polynomial.coeff_sub, hA3, hβ, ← Polynomial.C_pow, Polynomial.coeff_C_mul, hΦ3,
      Polynomial.coeff_C_mul, hρ3] at h
    linear_combination (-4⁻¹ : F) * h
  obtain ⟨α₁, α₀, hAAeq⟩ : ∃ α₁ α₀ : F, AA = Polynomial.C α₁ * Polynomial.X + Polynomial.C α₀ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hAAle
  have hAAeq' : Polynomial.C (2 : F) * a
        - b * (Polynomial.C V.a₁ * Polynomial.X + Polynomial.C V.a₃)
      = Polynomial.C α₁ * Polynomial.X + Polynomial.C α₀ := by rw [← hAA]; exact hAAeq
  have haeq : ∀ ξ : F, (2 : F) * a.eval ξ - β * (V.a₁ * ξ + V.a₃) = α₁ * ξ + α₀ := by
    intro ξ
    have h := congrArg (Polynomial.eval ξ) hAAeq'
    rw [hβ] at h
    simpa using h
  refine ⟨β, -(α₁ + β * V.a₁) / (2 * β), -(α₀ + β * V.a₃) / (2 * β), hβκ, ?_⟩
  intro P hP
  have ha : a.eval (W.veluCoordX S P)
      = (α₁ * W.veluCoordX S P + α₀ + β * (V.a₁ * W.veluCoordX S P + V.a₃)) / 2 := by
    field_simp
    linear_combination haeq (W.veluCoordX S P)
  rw [hab P hP, hβ]
  simp only [Polynomial.eval_C]
  rw [ha]
  field_simp
  ring

omit [W.IsElliptic] in
/-- THE ASSEMBLY, parity-free. -/
theorem velu_addX_eq_of_norm_line_all (S : Finset W.Point) (hS : IsPointSubgroup S)
    {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S)
    {c lam mu : F}
    (hc : c ^ 2 = (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
            * (veluH S).eval (veluPointX (A + B)))
    (hN : ∀ P : W.Point, P ∉ S →
      (∏ Q ∈ S, (veluPointY (P + Q)
        - (W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
            * (veluPointX (P + Q) - veluPointX A) + veluPointY A)))
        = c * (W.veluCoordY S P - (lam * W.veluCoordX S P + mu)))
    {P₀ P₁ P₂ : W.Point} (hP₀ : P₀ ∉ S) (hP₁ : P₁ ∉ S) (hP₂ : P₂ ∉ S)
    (h01 : W.veluCoordX S P₀ ≠ W.veluCoordX S P₁)
    (h02 : W.veluCoordX S P₀ ≠ W.veluCoordX S P₂)
    (h12 : W.veluCoordX S P₁ ≠ W.veluCoordX S P₂) :
    W.veluCoordX S (A + B)
      = (W.veluCurve S).addX (W.veluCoordX S A) (W.veluCoordX S B)
          ((W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
            (W.veluCoordY S A) (W.veluCoordY S B)) := by
  classical
  have hκ : (veluH S).eval (veluPointX A) * (veluH S).eval (veluPointX B)
              * (veluH S).eval (veluPointX (A + B)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (veluH_eval_ne_zero hS hA) (veluH_eval_ne_zero hS hB))
      (veluH_eval_ne_zero hS hAB)
  have hc0 : c ≠ 0 := by intro h; exact hκ (by rw [← hc, h]; ring)
  have hline : ∀ T : W.Point, T ∉ S →
      veluPointY T = W.slope (veluPointX A) (veluPointX B) (veluPointY A) (veluPointY B)
          * (veluPointX T - veluPointX A) + veluPointY A →
      W.veluCoordY S T = lam * W.veluCoordX S T + mu := by
    intro T hT hTline
    have h0 := (hN T hT).symm.trans (velu_norm_eq_zero_of_on_line W hS hTline)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hc0)
  have hlineA : W.veluCoordY S A = lam * W.veluCoordX S A + mu := hline A hA (by ring)
  have hlineB : W.veluCoordY S B = lam * W.veluCoordX S B + mu :=
    hline B hB (velu_slope_line_snd W (velu_point_equation W (fun h => hA (h ▸ hS.zero_mem)))
      (velu_point_equation W (fun h => hB (h ▸ hS.zero_mem)))
      (velu_point_ne_negY W hS hA hB hAB))
  have hmu : mu = W.veluCoordY S A - lam * W.veluCoordX S A := by rw [hlineA]; ring
  subst hmu
  have hcube : ∀ P : W.Point, P ∉ S →
      ((W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam).eval
          (W.veluCoordX S P)
        = -((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) := by
    intro P hP
    have hstar := velu_norm_line_mul_neg_slope_all W S hS hA hB hAB hP
    rw [hN P hP, hN (-P) (velu_neg_notMem W hS hP), veluCoordX_neg hS P,
      veluCoordY_neg hS hP] at hstar
    have heq := W.velu_equation_of_subgroup S hS hP
    rw [Affine.equation_iff] at heq
    simp only [Affine.negY] at hstar
    have hkey : c ^ 2 * (((W.veluCurve S).addPolynomial (W.veluCoordX S A)
          (W.veluCoordY S A) lam).eval (W.veluCoordX S P)
        + (W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) = 0 := by
      rw [velu_addPolynomial_eval]
      linear_combination hstar + c ^ 2 * heq
        + ((W.veluCoordX S P - W.veluCoordX S A) * (W.veluCoordX S P - W.veluCoordX S B)
            * (W.veluCoordX S P - W.veluCoordX S (A + B))) * hc
    linear_combination (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hc0)
  have hcard : ({W.veluCoordX S P₀, W.veluCoordX S P₁, W.veluCoordX S P₂} : Finset F).card
      = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  have hdiff : (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
      + (Polynomial.X - Polynomial.C (W.veluCoordX S A))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
        * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B))) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
      {W.veluCoordX S P₀, W.veluCoordX S P₁, W.veluCoordX S P₂} ?_ ?_
    · intro ξ hξ
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hξ
      rcases hξ with rfl | rfl | rfl
      · linear_combination hcube P₀ hP₀
      · linear_combination hcube P₁ hP₁
      · linear_combination hcube P₂ hP₂
    · rw [hcard, show (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
          + (Polynomial.X - Polynomial.C (W.veluCoordX S A))
            * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
            * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B)))
          = (⟨(1 : F) - 1,
              -(W.veluCoordX S A + W.veluCoordX S B + W.veluCoordX S (A + B))
                - (-lam ^ 2 - (W.veluCurve S).a₁ * lam + (W.veluCurve S).a₂),
              (W.veluCoordX S A * W.veluCoordX S B + W.veluCoordX S A * W.veluCoordX S (A + B)
                  + W.veluCoordX S B * W.veluCoordX S (A + B))
                - (2 * W.veluCoordX S A * lam ^ 2
                  + ((W.veluCurve S).a₁ * W.veluCoordX S A - 2 * W.veluCoordY S A
                      - (W.veluCurve S).a₃) * lam
                  + (-(W.veluCurve S).a₁ * W.veluCoordY S A + (W.veluCurve S).a₄)),
              -(W.veluCoordX S A * W.veluCoordX S B * W.veluCoordX S (A + B))
                - (-W.veluCoordX S A ^ 2 * lam ^ 2
                  + (2 * W.veluCoordX S A * W.veluCoordY S A
                      + (W.veluCurve S).a₃ * W.veluCoordX S A) * lam
                  - (W.veluCoordY S A ^ 2 + (W.veluCurve S).a₃ * W.veluCoordY S A
                      - (W.veluCurve S).a₆))⟩ : Cubic F).toPoly from ?_]
      · exact lt_of_le_of_lt (Cubic.natDegree_of_a_eq_zero (by ring)) (by norm_num)
      · rw [Affine.addPolynomial_eq, Cubic.prod_X_sub_C_eq, neg_add_eq_sub,
          velu_cubic_toPoly_sub]
  have hpoly : (W.veluCurve S).addPolynomial (W.veluCoordX S A) (W.veluCoordY S A) lam
      = -((Polynomial.X - Polynomial.C (W.veluCoordX S A))
          * (Polynomial.X - Polynomial.C (W.veluCoordX S B))
          * (Polynomial.X - Polynomial.C (W.veluCoordX S (A + B)))) :=
    eq_neg_of_add_eq_zero_left hdiff
  rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq] at hpoly
  have hb := Cubic.b_of_eq hpoly
  have hcc := Cubic.c_of_eq hpoly
  simp only at hb hcc
  have hxyV := W.velu_coord_ne_neg_of_subgroup S hS hA hB hAB
  have hslope : lam = (W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
      (W.veluCoordY S A) (W.veluCoordY S B) := by
    by_cases hab : W.veluCoordX S A = W.veluCoordX S B
    · have hy : W.veluCoordY S A
          ≠ (W.veluCurve S).negY (W.veluCoordX S B) (W.veluCoordY S B) := fun h => hxyV ⟨hab, h⟩
      have hyy : W.veluCoordY S A = W.veluCoordY S B := by rw [hlineB, hab]; ring
      have hnegeq : (W.veluCurve S).negY (W.veluCoordX S A) (W.veluCoordY S A)
          = (W.veluCurve S).negY (W.veluCoordX S B) (W.veluCoordY S B) := by rw [hab, hyy]
      have hy' : W.veluCoordY S A
          ≠ (W.veluCurve S).negY (W.veluCoordX S A) (W.veluCoordY S A) := by
        rw [hnegeq]; exact hy
      rw [Affine.slope_of_Y_ne hab hy, eq_div_iff (sub_ne_zero.mpr hy')]
      rw [← hab] at hb hcc
      simp only [Affine.negY]
      linear_combination (-1 : F) * hcc + (-2 * W.veluCoordX S A) * hb
    · rw [Affine.slope_of_X_ne hab, eq_div_iff (sub_ne_zero.mpr hab)]
      linear_combination hlineB
  rw [← hslope]
  simp only [Affine.addX]
  linear_combination hb

/-- **PROVEN 2026-07-27: the `addX` identity at EVERY kernel order.** The parity-free form
of `velu_coordX_add_eq_addX`, and the real content of arbitrary-order Vélu additivity.

The odd-order proof runs the identity over `AlgebraicClosure F` and descends; the descent
half (`velu_bc_coordX`, `velu_bc_coordY`, `velu_baseChange_isPointSubgroup`) is already
parity-free, so what had to be mirrored is the algebraically-closed core: `velu_hnorm` and
`velu_addX_eq_of_norm_line`. Both are now `velu_hnorm_all` and
`velu_addX_eq_of_norm_line_all` above.

**The whole chain turned out to be parity-free VERBATIM** — `STAR`, `POLY`, the trace
calculus, `HNORM` and this assembly all mirror the odd-order proofs with `hodd` deleted and
the `All` bricks substituted. In particular `velu_hnorm_all` carries `c² = κ` with **no**
sign correction; the route map's item 4, which predicted `c² = (−1)^{|S|+1}·κ` and warned
that `c² = κ` is FALSE at even order, was itself wrong, and is refuted in place above.

The only genuinely new work is underneath: `velu_wronskian_all` (a two-branch termwise
computation, where the `2`-torsion branch works precisely because `u_Q = 0` there) and
`velu_xNumAll_sub_eq_prod`. -/
theorem velu_coordX_add_eq_addX_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {A B : W.Point} (hA : A ∉ S) (hB : B ∉ S) (hAB : A + B ∉ S) :
    W.veluCoordX S (A + B)
      = (W.veluCurve S).addX (W.veluCoordX S A) (W.veluCoordX S B)
          ((W.veluCurve S).slope (W.veluCoordX S A) (W.veluCoordX S B)
            (W.veluCoordY S A) (W.veluCoordY S B)) := by
  classical
  haveI : (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).IsElliptic :=
    inferInstanceAs (W.map (algebraMap F (AlgebraicClosure F))).IsElliptic
  set A' := veluBaseChangePoint W (AlgebraicClosure F) A
  set B' := veluBaseChangePoint W (AlgebraicClosure F) B
  set S' : Finset (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)).Point :=
    S.image (veluBaseChangePoint W (AlgebraicClosure F)) with hS'def
  have hS' : IsPointSubgroup S' := velu_baseChange_isPointSubgroup hS
  have hmem : ∀ P : W.Point, P ∉ S →
      veluBaseChangePoint W (AlgebraicClosure F) P ∉ S' := by
    intro P hP hcon
    rw [hS'def, Finset.mem_image] at hcon
    obtain ⟨Q, hQ, hQeq⟩ := hcon
    exact hP (veluBaseChangePoint_injective hQeq ▸ hQ)
  have hsum : A' + B' = veluBaseChangePoint W (AlgebraicClosure F) (A + B) := (map_add _ _ _).symm
  obtain ⟨c, lam, mu, hc, hN⟩ :=
    velu_hnorm_all (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS'
      (hmem A hA) (hmem B hB) (hsum ▸ hmem (A + B) hAB)
  obtain ⟨P₀, P₁, P₂, hP₀, hP₁, hP₂, h01, h02, h12⟩ :=
    velu_exists_three_coordX_all (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS'
  have key := velu_addX_eq_of_norm_line_all
    (W⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F)) S' hS'
    (hmem A hA) (hmem B hB) (hsum ▸ hmem (A + B) hAB) hc hN hP₀ hP₁ hP₂ h01 h02 h12
  rw [hsum, velu_bc_coordX, velu_bc_coordX, velu_bc_coordX,
    velu_bc_coordY, velu_bc_coordY, ← velu_baseChange_curve,
    show ((W.veluCurve S)⁄(AlgebraicClosure F) : Affine (AlgebraicClosure F))
        = (W.veluCurve S).map (algebraMap F (AlgebraicClosure F)) from rfl,
    Affine.map_slope, Affine.map_addX] at key
  exact (algebraMap F (AlgebraicClosure F)).injective key

/-- **PROVEN, parity-free: the `x`-coordinate identity ALONE implies additivity.**
Mirror of `velu_map_add_of_coordX`. -/
theorem velu_map_add_of_coordX_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hz : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
      W.veluMapAll S hS P + W.veluMapAll S hS Q ≠ 0)
    (hx : ∀ P Q : W.Point, P ∉ S → Q ∉ S → P + Q ∉ S →
      haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
      W.veluCoordX S (P + Q)
        = veluPointX (W.veluMapAll S hS P + W.veluMapAll S hS Q))
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  refine velu_map_add_of_add_eq_neg_of_subgroup W S hS (fun A B hA hB hAB => ?_) hP hQ hPQ
  have hne : W.veluMapAll S hS (A + B) ≠ 0 := by
    rw [W.veluMapAll_of_notMem hS hAB]; exact Affine.Point.some_ne_zero _
  have hxAB : veluPointX (W.veluMapAll S hS (A + B))
      = veluPointX (W.veluMapAll S hS A + W.veluMapAll S hS B) := by
    rw [W.veluMapAll_of_notMem hS hAB]; exact hx A B hA hB hAB
  exact velu_pointX_eq_iff hne (hz A B hA hB hAB) hxAB

/-- **PROVEN, parity-free (over the two leaves above): the generic case of additivity.**
Mirror of `velu_map_add_of_notMem`. -/
theorem velu_map_add_of_notMem_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    {P Q : W.Point} (hP : P ∉ S) (hQ : Q ∉ S) (hPQ : P + Q ∉ S) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  have hz : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluMapAll S hS A + W.veluMapAll S hS B ≠ 0 := fun A B hA hB hAB =>
    velu_map_add_ne_zero_of_subgroup W S hS hA hB
      (W.velu_coord_ne_neg_of_subgroup S hS hA hB hAB)
  have hX : ∀ A B : W.Point, A ∉ S → B ∉ S → A + B ∉ S →
      W.veluCoordX S (A + B)
        = veluPointX (W.veluMapAll S hS A + W.veluMapAll S hS B) := by
    intro A B hA hB hAB
    rw [W.veluMapAll_of_notMem hS hA, W.veluMapAll_of_notMem hS hB,
      Affine.Point.add_some (W.velu_coord_ne_neg_of_subgroup S hS hA hB hAB)]
    exact W.velu_coordX_add_eq_addX_of_subgroup S hS hA hB hAB
  exact velu_map_add_of_coordX_of_subgroup W S hS hz hX hP hQ hPQ

/-- **PROVEN (2026-07-27): the Vélu map is additive, at EVERY kernel order.**

The parity-free form of `velu_map_add`. This is no longer a leaf: the whole route
closed and this declaration is now a pure assembly over the four kernel cases plus
`velu_map_add_of_notMem_of_subgroup`. Axiom audit: `[propext, Classical.choice,
Quot.sound]`, and `Velu.lean` emits **no** `declaration uses 'sorry'` warning at any
line.

Historical note, kept because the route is the interesting part: the reduction here
is formal and parity-free once its inputs are — `veluMapAll_neg`, additivity up to
sign, and the kernel cases — so the real content was the parity-free forms of
`velu_coord_ne_neg` (routing through `velu_xNum_sub_eq_prod`, hence through
`veluH_factor`) and of the `addX` identity. Both landed, along with
`velu_norm_line_eq_poly` and the parity-free `velu_curve_Δ_ne_zero`, so the
odd-order coordination this docstring used to ask for is discharged. -/
theorem velu_map_add_of_subgroup (S : Finset W.Point) (hS : IsPointSubgroup S)
    (P Q : W.Point) :
    haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
    W.veluMapAll S hS (P + Q) = W.veluMapAll S hS P + W.veluMapAll S hS Q := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic_of_subgroup S hS
  by_cases hP : P ∈ S
  · by_cases hQ : Q ∈ S
    · rw [W.veluMapAll_of_mem hS (hS.add_mem P hP Q hQ), W.veluMapAll_of_mem hS hP,
        W.veluMapAll_of_mem hS hQ, add_zero]
    · have hPQ : P + Q ∉ S := fun hc => hQ (by
        simpa using hS.add_mem (-P) (hS.neg_mem P hP) (P + Q) hc)
      rw [W.veluMapAll_of_mem hS hP, zero_add, W.veluMapAll_of_notMem hS hPQ,
        W.veluMapAll_of_notMem hS hQ]
      exact velu_point_some_eq
        (by rw [add_comm, veluCoordX_add_mem hS Q hP])
        (by rw [add_comm, veluCoordY_add_mem hS Q hP])
  · by_cases hQ : Q ∈ S
    · have hPQ : P + Q ∉ S := fun hc => hP (by
        simpa using hS.add_mem (P + Q) hc (-Q) (hS.neg_mem Q hQ))
      rw [W.veluMapAll_of_mem hS hQ, add_zero, W.veluMapAll_of_notMem hS hPQ,
        W.veluMapAll_of_notMem hS hP]
      exact velu_point_some_eq (veluCoordX_add_mem hS P hQ) (veluCoordY_add_mem hS P hQ)
    · by_cases hPQ : P + Q ∈ S
      · have hQeq : Q = -P + (P + Q) := by abel
        rw [W.veluMapAll_of_mem hS hPQ, W.veluMapAll_of_notMem hS hP,
          W.veluMapAll_of_notMem hS hQ]
        have hXQ : W.veluCoordX S Q = W.veluCoordX S P := by
          rw [hQeq, veluCoordX_add_mem hS (-P) hPQ, veluCoordX_neg hS]
        have hYQ : W.veluCoordY S Q
            = (W.veluCurve S).negY (W.veluCoordX S P) (W.veluCoordY S P) := by
          rw [hQeq, veluCoordY_add_mem hS (-P) hPQ, veluCoordY_neg hS hP]
        exact (Affine.Point.add_of_Y_eq hXQ.symm
          (by rw [hYQ, hXQ, Affine.negY_negY])).symm
      · exact velu_map_add_of_notMem_of_subgroup W S hS hP hQ hPQ

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
parity hypothesis, so the assembly is the odd-order one with `hodd` deleted.

**The COORDINATE IDENTIFICATION is now part of the conclusion** (added 2026-07-27,
mirroring `exists_velu_quotient_isogeny_model`): the final conjunct pins `φ`
pointwise off the kernel, `veluPointX (φ Pt) = veluCoordX … Pt` and
`veluPointY (φ Pt) = veluCoordY … Pt` for `Pt ∉ C`. It is what lets a call site
apply the `IsRationalMap` bridge of `Fermat/FLT/EllipticCurve/Isogeny.lean`, whose
certificate is written in `veluXNum` / `veluH` / `veluXi`. -/
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
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, Pt ∉ C →
        veluPointX (φ Pt) =
            veluCoordX (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset Pt ∧
          veluPointY (φ Pt) =
            veluCoordY (E⁄(AlgebraicClosure ℚ)) hCfin.toFinset Pt) := by
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
        rw [velu_map_add_of_subgroup _ S hS P Q, map_add]), ht, hw, ?_, ?_, ?_⟩
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
  · -- the coordinate identification off the kernel
    intro Pt hPt
    have hPtS : Pt ∉ S := fun hc => hPt ((hmem Pt).mp hc)
    show veluPointX (ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS Pt)) =
          veluCoordX (E⁄(AlgebraicClosure ℚ)) S Pt ∧
        veluPointY (ψ (veluMapAll (E⁄(AlgebraicClosure ℚ)) S hS Pt)) =
          veluCoordY (E⁄(AlgebraicClosure ℚ)) S Pt
    rw [veluMapAll_of_notMem _ hS hPtS, hψdef, pointAddEquivOfEq_some]
    exact ⟨rfl, rfl⟩

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
  obtain ⟨t, w, hell, φ, -, -, hgal, hker, -⟩ :=
    exists_velu_quotient_isogeny_model_of_subgroup E C hCfin hCstable
  exact ⟨E.veluModel t w, hell, φ, hgal, hker⟩

end DescentAllOrders

end WeierstrassCurve
