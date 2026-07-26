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
`velu_coordX_eq`, `velu_coordY_eq`), which proves `velu_equation` over the
single leaf `velu_pole_identity` — since 2026-07-26 `velu_equation_pole`
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
* `velu_exists_three_twoTorsion`, assembled over the single leaf
  `velu_coordX_twoTorsion_ne` below.

SORRY LEAVES (three, each stated over an arbitrary field of characteristic
zero for a finite subgroup of odd order):

* `WeierstrassCurve.velu_pole_identity` — the `y`-free rational-function
  identity in `x` alone that remains of the verification of Vélu 1971 after
  `velu_equation_pole` has completed the square.
* `WeierstrassCurve.velu_coordX_twoTorsion_ne` — the Vélu `x`-coordinates
  of two distinct `2`-torsion points outside the kernel differ.
* `WeierstrassCurve.velu_map_add_of_notMem` — additivity in the generic
  case, `P`, `Q`, `P + Q` all outside the kernel.

The last two are two faces of one fact — that the Vélu map is a
homomorphism read on coordinates — and are worth attacking together.

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

/-- **SORRY LEAF: Vélu's rational-function identity, with `y` eliminated**, cut 2026-07-26
out of `velu_equation_pole`.

Writing `x = x(P)`, `X = x + ½ Σ_{Q ∈ S} veluPoleX`, `D = Σ_{Q ∈ S} veluPoleV`,
`t = veluT S` and `w = veluW S`, the claim is the ONE-VARIABLE identity

  `(4x³ + b₂x² + 2b₄x + b₆)·(1 − D)² = 4X³ + b₂X² + (2b₄ − 20t)X + (b₆ − 4b₂t − 28w)`.

Nothing here mentions `y`: `velu_pole_V` has already replaced the completed square
`V = 2Y + a₁X + a₃` by `(2y + a₁x + a₃)(1 − D)`, and `(2y + a₁x + a₃)² = 4x³ + b₂x² +
2b₄x + b₆` is the Weierstrass equation at `P`. So this is the whole remaining content of
Vélu's theorem, part 2.

**Route** (Vélu 1971; Kohel's thesis §2.4). Both sides are rational functions of `x` with
poles only at the `x`-coordinates of `S ∖ {0}`; note each such `x_Q` occurs TWICE in a sum
over all of `S`, from `Q` and `−Q`, so the principal part of `Σ veluPoleX` at `x_Q` is
`2t_Q/(x − x_Q) + 2u_Q/(x − x_Q)²`. Clearing the denominator `h⁶`, where
`h = ∏_{Q ∈ R}(x − x_Q)` over a set `R` of representatives of `S ∖ {0}` modulo `±`, turns
the claim into a polynomial identity of degree `6·deg h + 3`, and it splits in two:

1. *No poles*: `h⁶` divides the difference. A Laurent expansion at `x_Q` (verified in
   PARI/GP) shows the `d^{-6}` and `d^{-5}` coefficients vanish identically — this is
   exactly `u_Q = 4x_Q³ + b₂x_Q² + 2b₄x_Q + b₆`, the Weierstrass equation at `Q` — while
   the `d^{-4}, …, d^{-1}` coefficients impose four relations on the value and the first
   three derivatives at `x_Q` of the sum over `S ∖ {Q, −Q}`. THIS is where closure of `S`
   under addition is consumed: the value itself is `2(x_Q − x_{2Q})`, by the `±`-paired
   addition law `velu_pair_X` plus the reindexing `Q' ↦ Q + Q'` of `S`.
2. *Vanishing at infinity*: the difference has degree `< 6·deg h`, which pins the top four
   coefficients and is where `t` and `w` are consumed.

**The subgroup hypothesis is essential and the pole form does not carry it.** Verified in
PARI/GP over `𝔽_p` for `101 ≤ p ≤ 500` and kernel orders up to `523`: with a genuine
subgroup, 75789 instances pass and none fail; with the `±`-stable NON-subgroup
`{0, G, −G}` for `G` of order `≥ 5`, for which every formula above is equally well
defined, 31006 of 31143 instances FAIL.

**`hodd` may well be unnecessary here.** It is carried over from the consumer
`velu_equation_pole`, but the same PARI/GP sweep finds the identity holding verbatim for
kernels of order `2`, `4` and `6` (16077 instances, none failing). The reason is that the
halving convention reproduces Vélu's SEPARATE `2`-torsion coefficients automatically: at a
`2`-torsion `Q` one has `2y_Q + a₁x_Q + a₃ = 0`, so `u_Q = 0` and
`veluTTerm W Q = 6x_Q² + b₂x_Q + b₄ = 2 g^x_Q`, whence `½·veluTTerm W Q = g^x_Q` and
`½·veluWTerm W Q = x_Q g^x_Q` — exactly Vélu's `t_Q` and `w_Q` in the order-`2` case,
which the classical presentation has to write down separately. Oddness is used elsewhere
in this file (it is what makes `x_Q` occur exactly TWICE in a sum over `S`, which is how
the principal parts are read off above), so a proof may still want it. -/
theorem velu_pole_identity {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {P : W.Point} (hP : P ∉ S) :
    (4 * veluPointX P ^ 3 + W.b₂ * veluPointX P ^ 2 + 2 * W.b₄ * veluPointX P + W.b₆) *
        (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) ^ 2 =
      4 * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 3 +
        W.b₂ * (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) ^ 2 +
        (2 * W.b₄ - 20 * W.veluT S) *
          (veluPointX P + (2 : F)⁻¹ * ∑ Q ∈ S, veluPoleX W (veluPointX P) Q) +
        (W.b₆ - 4 * W.b₂ * W.veluT S - 28 * W.veluW S) :=
  sorry

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

/-! ### Vélu's theorem -/

section Velu

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

omit [W.IsElliptic] in
/-- **Vélu's theorem, part 2a: the quotient equation in pole form** (PROVEN 2026-07-26
over the single leaf `velu_pole_identity`; it was itself the leaf cut on 2026-07-26 out
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

/-- **SORRY LEAF: the Vélu `x`-coordinates of two distinct `2`-torsion points differ**, cut
2026-07-26 out of `velu_exists_three_twoTorsion`. This is the WHOLE remaining content of that
node — everything else in it (base change, the existence of the three `2`-torsion points over
the algebraic closure, their lying outside the kernel, and the quotient equation) is proven.

Why it is true: by Vélu's theorem the images of the three nonzero `2`-torsion points of `W`
are the three nonzero `2`-torsion points of the quotient, which are distinct because the
quotient is nonsingular. That reasoning may NOT be used here, since `velu_isElliptic` is
exactly what is being proved.

Route without circularity. If `X(T₁) = X(T₂)` then, both images being `2`-torsion — their
`Y` is forced to `negY(X, Y)` by `veluCoordY_neg`, hence to `−(a₁X + a₃)/2` — the two images
coincide as coordinate pairs. The third `2`-torsion point `T₃ = T₁ + T₂` also lies outside
the kernel, and the addition law of the quotient applied to the two coinciding images returns
`0`, whereas the coordinates of `T₃` are those of an affine point. Carried out at the level of
the `addX`/`addY` formulas this needs no nonsingularity of the quotient, hence no
circularity; it is the coordinate shadow of the additivity leaf `velu_map_add_of_notMem`, and
the two are worth attacking together.

Hypotheses `_hS`, `_hodd`, `_hT₁`, `_hT₂`, `_hn₁`, `_hn₂`, `_hne` are all genuinely needed:
dropping the `2`-torsion clauses makes the statement FALSE (take `T₂ = −T₁`, or
`T₂ = T₁ + Q` for `Q ∈ S`, both of which have the same Vélu `x`-coordinate by
`veluCoordX_neg` and `veluCoordX_add_mem`); they are underscored only because no proof
consumes them yet. -/
theorem velu_coordX_twoTorsion_ne (S : Finset W.Point) (_hS : IsPointSubgroup S)
    (_hodd : Odd S.card) {T₁ T₂ : W.Point} (_hT₁ : T₁ ∉ S) (_hT₂ : T₂ ∉ S)
    (_hn₁ : -T₁ = T₁) (_hn₂ : -T₂ = T₂) (_hne : T₁ ≠ T₂) :
    W.veluCoordX S T₁ ≠ W.veluCoordX S T₂ :=
  sorry

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

1. `hxy → False`. By `veluCoordX_neg` and `veluCoordY_neg` the hypothesis says precisely that
   `P` and `−Q` have the same Vélu coordinate pair, while `P − (−Q) = P + Q ∉ S`; so this
   goal is the coordinate form of "the fibres of the Vélu map are exactly the cosets of `S`",
   i.e. injectivity modulo the kernel. It is the same fact that
   `velu_coordX_twoTorsion_ne` needs for its distinctness clause.
2. `X (P + Q) = V.addX (X P) (X Q) (V.slope (X P) (X Q) (Y P) (Y Q))`.
3. `Y (P + Q) = V.addY (X P) (X Q) (Y P) (V.slope (X P) (X Q) (Y P) (Y Q))`.

(The remaining glue is `Affine.Point.add_some hxy` and `velu_point_some_eq`.)

That decomposition is deliberately NOT committed as three sorried leaves: goals 2 and 3
commit the proof to the finite/rational-function route judged impractical above, and a
function-field development would supply all three at once. Take it as a map, not as a cut.

So this leaf and `velu_coordX_twoTorsion_ne` are two faces of one fact — that the Vélu map
is a homomorphism with kernel exactly `S`, read on coordinates — and are worth attacking
together, by one owner. -/
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
