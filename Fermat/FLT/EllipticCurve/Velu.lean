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
(`velu_t_mem_range`, `velu_w_mem_range`); and Galois equivariance of the
Vélu coordinates (`velu_coordX_map`, `velu_coordY_map`).

SORRY LEAVES (three, each stated over an arbitrary field of characteristic
zero for a finite subgroup of odd order):

* `WeierstrassCurve.velu_isElliptic` — the quotient curve is nonsingular.
* `WeierstrassCurve.velu_equation` — the image coordinates satisfy the
  quotient equation.
* `WeierstrassCurve.velu_map_add` — the map is additive.

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

/-! ### The three sorry leaves: Vélu's theorem -/

section Velu

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] (W : Affine F) [W.IsElliptic]

/-- **Vélu's theorem, part 1: the quotient curve is elliptic** (SORRY LEAF, cut
2026-07-25 out of `exists_quotient_isogeny_of_odd_prime_card`).

For a finite subgroup `S` of odd order in `W.Point`, the Vélu model
`y² + a₁xy + a₃y = x³ + a₂x² + (a₄ − 5t)x + (a₆ − b₂t − 7w)` is nonsingular.

Route. The discriminant of the Vélu model is not a nice function of `Δ W`, so
the intended argument is indirect, through the `2`-torsion:

1. The Vélu map is injective on `W.Point[2]`, because its kernel is `S` and `S`
   has ODD order, so `S ∩ W.Point[2] = 0`. Over an algebraically closed field
   `W.Point[2] ≅ (ℤ/2)²` has four elements, so the quotient curve carries at
   least four points killed by `2`.
2. The affine `2`-torsion of a Weierstrass curve is cut out by the `2`-division
   polynomial `4x³ + b₂x² + 2b₄x + b₆`, whose discriminant is `16Δ`. If `Δ = 0`
   this cubic has a repeated root, and a repeated root is the `x`-coordinate of
   the SINGULAR point (both partials vanish there), which is not a point of
   `Point`. Hence a singular Weierstrass curve has at most `1 + 2 = 3` points
   killed by `2`.

Steps 1 and 2 contradict each other, so `Δ ≠ 0`. Note step 1 needs the
additivity leaf `velu_map_add`, so this brick should be attacked AFTER it, or
the two should be cut together. An owner may instead prefer the direct route:
Vélu's own proof exhibits the quotient as a curve with a nonvanishing invariant
differential. -/
theorem velu_isElliptic (S : Finset W.Point) (_hS : IsPointSubgroup S)
    (_hodd : Odd S.card) : (W.veluCurve S).IsElliptic :=
  sorry

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

/-- **Vélu's theorem, part 3: the map is additive** (SORRY LEAF, cut 2026-07-25
out of `exists_quotient_isogeny_of_odd_prime_card`).

For a finite subgroup `S` of odd order in `W.Point`, the Vélu map is a group
homomorphism `W.Point → (W.veluCurve S).Point`.

Route. Additivity is the one part of Vélu's theorem that is not a coordinate
computation in disguise. The classical argument is the function-field one: the
coordinate functions `X, Y` generate the subfield of `W`'s function field fixed
by translation by `S`, that subfield is the function field of `veluCurve W S`,
and the induced map of curves is a morphism sending `0` to `0`, hence a group
homomorphism (`Affine.FunctionField` exists in mathlib; the rest does not).

The finite-form alternative, which avoids the function field, is to verify
additivity as a rational-function identity in the coordinates of `P₁, P₂` modulo
the equations of `W` — that is how the classical `2`-isogeny is handled in
`MazurTorsion.twoIsogenyFun_add_of_ne` — but for general `S` the identity
involves the `|S|` translates and does not reduce to a single `ring` call. -/
theorem velu_map_add (S : Finset W.Point) (hS : IsPointSubgroup S)
    (hodd : Odd S.card) (P Q : W.Point) :
    W.veluMap S hS hodd (P + Q) = W.veluMap S hS hodd P + W.veluMap S hS hodd Q :=
  sorry

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
