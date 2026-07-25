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
the leaves below.

SORRY LEAVES (four, each stated over an arbitrary field of characteristic
zero for a finite subgroup of odd order):

* `WeierstrassCurve.isElliptic_of_three_twoTorsion` — three affine
  `2`-torsion points with distinct `x` force `Δ ≠ 0` (general Weierstrass
  geometry, no Vélu input).
* `WeierstrassCurve.velu_exists_three_twoTorsion` — the quotient curve has
  three such points over the algebraic closure.
* `WeierstrassCurve.velu_equation` — the image coordinates satisfy the
  quotient equation.
* `WeierstrassCurve.velu_map_add_of_notMem` — additivity in the generic
  case, `P`, `Q`, `P + Q` all outside the kernel.

These are the mathematical content of Vélu's theorem; none of it is in
mathlib.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite

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

/-! ### The sorry leaves: Vélu's theorem -/

/-- **SORRY LEAF (general Weierstrass geometry), cut 2026-07-26 out of
`velu_isElliptic`.** Over a field of characteristic zero, a Weierstrass curve carrying
three affine points of order dividing `2` with pairwise distinct `x`-coordinates is
nonsingular.

Route. Substituting `y = negY x y`, i.e. `2y + a₁x + a₃ = 0`, into the Weierstrass equation
turns it into `4x³ + b₂x² + 2b₄x + b₆ = 0`; the hypothesis therefore supplies three distinct
roots of that cubic, which is thus separable. Its discriminant is `16 Δ`, so `Δ ≠ 0`. Only
the last step needs a computation: with `4x³ + b₂x² + 2b₄x + b₆ = 4(x−e₁)(x−e₂)(x−e₃)` one
has `b₂ = −4(e₁+e₂+e₃)`, `2b₄ = 4(e₁e₂+e₁e₃+e₂e₃)`, `b₆ = −4e₁e₂e₃`, and
`Δ = 16(e₁−e₂)²(e₁−e₃)²(e₂−e₃)²` is then a `ring` identity in `e₁, e₂, e₃` after unfolding
`Δ`, `b₂`, `b₄`, `b₆`, `b₈`. Characteristic zero is used to solve `2y = −a₁x − a₃` for `y`
and to divide by `4`; characteristic `≠ 2` would do. -/
theorem isElliptic_of_three_twoTorsion {K : Type*} [Field K] [CharZero K]
    {W' : Affine K} {x₁ x₂ x₃ y₁ y₂ y₃ : K}
    (h₁ : W'.Equation x₁ y₁) (h₂ : W'.Equation x₂ y₂) (h₃ : W'.Equation x₃ y₃)
    (t₁ : y₁ = W'.negY x₁ y₁) (t₂ : y₂ = W'.negY x₂ y₂) (t₃ : y₃ = W'.negY x₃ y₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) : W'.IsElliptic :=
  sorry

section Velu

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

/-- **SORRY LEAF: the Vélu quotient acquires three affine `2`-torsion points over the
algebraic closure**, cut 2026-07-26 out of `velu_isElliptic`.

The base field `F` is arbitrary, so the three `x`-coordinates cannot be asked for in `F`
itself (a quotient curve over `ℚ` typically has a single rational `2`-torsion point); the
statement is therefore made over `AlgebraicClosure F`, which is also the only field the
consumer `exists_velu_quotient_isogeny` ever uses.

Route (the plan `velu_isElliptic`'s old docstring described, minus the circularity — none
of it may use `veluMap`, whose definition consumes `velu_isElliptic`):

1. Base change: `veluCurve` commutes with the base change `F → L`, because Vélu's `t` and
   `w` are sums of the `veluTTerm`/`veluWTerm` over `S` and `Affine.Point.map` is injective;
   so the base-changed quotient is the Vélu quotient of `W⁄L` by the image of `S`.
2. Over `L = AlgebraicClosure F` the curve `W⁄L` has exactly three nonzero points `T` with
   `T = −T` — the roots of `4x³ + b₂x² + 2b₄x + b₆`, distinct because `Δ ≠ 0`. Each lies
   OUTSIDE `S`: translation by a `T ∈ S` with `T ≠ 0`, `2T = 0` is a fixed-point-free
   involution of `S`, which would make `S.card` even.
3. Their Vélu coordinates satisfy the quotient equation by `velu_equation`, and are
   `2`-torsion by `veluCoordY_neg` (proven above: `Y(T) = Y(−T) = negY (X T) (Y T)`).
4. The three `x`-coordinates are pairwise distinct. This is the one genuinely hard clause
   and it is where the ODD ORDER is finally consumed: if `X(T₁) = X(T₂)` with `T₁ ≠ T₂`
   then, both images being `2`-torsion, the images coincide, so the image of
   `T₃ = T₁ + T₂ ∉ S` would be the double of a `2`-torsion point, namely `0` — contradicting
   that a point outside the kernel has an affine image. Carried out at the level of the
   `addX`/`addY` formulas this needs no nonsingularity, hence no circularity; it is the
   coordinate shadow of the additivity leaf `velu_map_add_of_notMem`. -/
theorem velu_exists_three_twoTorsion (S : Finset W.Point) (_hS : IsPointSubgroup S)
    (_hodd : Odd S.card) :
    ∃ x₁ x₂ x₃ y₁ y₂ y₃ : AlgebraicClosure F,
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₁ y₁ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₂ y₂ ∧
      ((W.veluCurve S)⁄(AlgebraicClosure F)).Equation x₃ y₃ ∧
      y₁ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₁ y₁ ∧
      y₂ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₂ y₂ ∧
      y₃ = ((W.veluCurve S)⁄(AlgebraicClosure F)).negY x₃ y₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ :=
  sorry

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

/-- **Vélu's theorem, part 2: the image lies on the quotient curve** (SORRY
LEAF, cut 2026-07-25 out of `exists_quotient_isogeny_of_odd_prime_card`).

For a finite subgroup `S` of odd order in `W.Point` and a point `P ∉ S`, the
Vélu coordinates `X(P) = x(P) + Σ_{Q ∈ S ∖ 0} (x(P + Q) − x(Q))` and
`Y(P) = y(P) + Σ_{Q ∈ S ∖ 0} (y(P + Q) − y(Q))` satisfy the equation of
`veluCurve W S`.

Route. This is the computational core of Vélu 1971. In the classical
presentation one first shows that the group-law sums equal the rational
functions

  `X = x + Σ_{Q ∈ S₀} [t_Q/(x − x_Q) + u_Q/(x − x_Q)²]`,
  `Y = y − Σ_{Q ∈ S₀} [u_Q(2y + a₁x + a₃)/(x − x_Q)³ + …]`

over a set `S₀` of representatives of `S ∖ {0}` modulo `±` (that identity is
itself the addition law applied to `P + Q` and `P − Q` and summed), and then
verifies the quotient equation as an identity of rational functions in `x, y`
modulo the equation of `W`, using that the `x_Q` are roots of the division
polynomial of `S`. Kohel's thesis §2.4 carries out the verification in this
normalisation; Washington, *Elliptic Curves*, ch. 12 does `char ≠ 2, 3`.

Note `P ∉ S` is exactly what makes every summand defined: `P + Q = 0` would
force `P = −Q ∈ S`. -/
theorem velu_equation (S : Finset W.Point) (_hS : IsPointSubgroup S)
    (_hodd : Odd S.card) {P : W.Point} (_hP : P ∉ S) :
    (W.veluCurve S).Equation (W.veluCoordX S P) (W.veluCoordY S P) :=
  sorry

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

Note that the coordinate shadow of this leaf — the special case in which the two images are
negatives of one another, which cannot happen for `P + Q ∉ S` — is also what
`velu_exists_three_twoTorsion` needs for its distinctness clause, so the two leaves are
worth attacking together. -/
theorem velu_map_add_of_notMem (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) {P Q : W.Point} (_hP : P ∉ S) (_hQ : Q ∉ S) (_hPQ : P + Q ∉ S) :
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q :=
  sorry

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
and `w`. -/
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
  refine ⟨E.veluModel t w, isElliptic_of_baseChange _ hE'K,
    AddMonoidHom.mk' (fun P => ψ (veluMap (E⁄(AlgebraicClosure ℚ)) S hS hodd P))
      (fun P Q => by
        rw [velu_map_add _ S hS hodd P Q, map_add]), ?_, ?_⟩
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

end Descent

end WeierstrassCurve
