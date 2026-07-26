/-
ModularCurve/HyperellipticJacobian.lean — own work for the Fermat project (not
vendored from the FLT project).

# Genus-`2` hyperelliptic curves, their integral models, and the Jacobian layer

This module supplies the **definitional layer** demanded by
`MazurLevel18.no_noncuspidal_point_on_smooth_model` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, namely the objects that the
rank-`0` proof of

    y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1   has only cuspidal ℚ-points

quantifies over, and which exist neither in mathlib at this pin nor in
`~/cs/FLT`.  That leaf's own docstring records the four missing pieces:

1. hyperelliptic curves of genus `2` and their Jacobians as `Pic⁰`, with
   the Mumford representation and its group law;
2. the Abel–Jacobi embedding `X ↪ J` from a rational base point;
3. good reduction `J(ℚ) → J(𝔽ₚ)` and injectivity on prime-to-`p` torsion;
4. `rank J(ℚ) = 0` by `2`-descent.

## What is BUILT here, and what remains

Everything **except** the existence of the Jacobian is now real code, and
the two arithmetic inputs that people usually hand-wave are discharged by
the kernel:

* `Pt` — the `R`-points of the smooth projective model of a monic sextic,
  in the weighted projective space `ℙ(1, 3, 1)`.  The leading coefficient
  is `1`, a square, so there are exactly **two** points at infinity; the
  type is therefore `AffPt ⊕ Bool` and that is a theorem about
  `ℙ(1,3,1)`, not a modelling choice: a point with `Z = 0` satisfies
  `Y² = X⁶` with `X ≠ 0`, so after normalising `X = 1` it is `Y = ±1`.
* `exists_int_coords` (PROVEN) — every rational point has integral
  weighted-projective coordinates `[a : t : b]` with `b = x.den`,
  `a = x.num` coprime, and `t = y·b³` an **integer**.  Integrality of `t`
  is the one non-formal step: `t² = F(a, b) ∈ ℤ` and `ℤ` is integrally
  closed in `ℚ`, which is `Rat.den_pow` here.
* `redPt` — the reduction map `X(ℚ) → X(𝔽ₚ)`, defined on those integral
  coordinates.  Coprimality of `(a, b)` is what makes it total: when
  `p ∣ b` the point reduces to an infinite point (with the sign of
  `t/a³`), otherwise to the affine point `(a/b, t/b³)`.  This is the map
  that item 3 above is *about*, so it had to be constructed rather than
  postulated — a package whose reduction map were an existentially
  quantified field would be discharged by the theorem it is meant to
  prove.
* `card_X18_F5` (PROVEN BY `decide`) — `#X(𝔽₅) = 6`.  The kernel checks
  it: mod `5` the sextic is `x² + 4x + 1` (Fermat's little theorem
  collapses `x⁶ + x⁵` to `x² + x`), whose values `1, 1, 3, 2, 3` at
  `x = 0, …, 4` are squares exactly twice, giving `4` affine points plus
  the `2` at infinity.  This is the point count the whole argument turns
  on, and it is now a machine-checked fact rather than a citation.
* `sevenPts_injective` (PROVEN) — the six cusps `(0, ±1)`, `(1, ±1)`,
  `∞±` together with any putative point of abscissa `∉ {0, 1}` are seven
  pairwise-distinct points of `X(ℚ)`.
* `redPt_injective` (PROVEN from the package) — reduction is injective on
  `X(ℚ)`.  The derivation is the entire mathematical content of the
  rank-`0` argument and is three lines: `J(ℚ)` is finite, so every
  element is killed by `Nat.card J`; the kernel of reduction is
  torsion-free; hence the kernel is trivial; hence `aj` injective plus
  the compatibility square makes `redPt` injective.
* `X18.no_noncuspidal_point` (PROVEN modulo the single leaf) — `7 ≤ 6`.

## The single remaining leaf

`X18.exists_jacobianPackage : Nonempty (JacobianPackage 1 (-2) 5 (-10) 10 (-4) 5)`

Its fields are exactly items 1–4:

| field | item |
|---|---|
| `J`, `addCommGroup` | 1 — `Pic⁰` of the curve, as a group |
| `aj`, `aj_injective` | 2 — Abel–Jacobi from a rational base point; injective because the genus is `2 ≥ 1` |
| `red`, `red_aj` | 3 — reduction is a group homomorphism compatible with `redPt` |
| `red_ker_torsionFree` | 3 — the kernel of reduction is the formal group over `ℤ₅`, torsion-free because `5 > e + 1 = 2` |
| `fin` | 4 — Mordell–Weil plus `rank J(ℚ) = 0` |

**FAITHFULNESS AUDIT.**  The package is *not* vacuous and *not*
discharged by junk.  `aj_injective` forces `J` to contain a copy of
`X(ℚ)`, and `fin` then forces `X(ℚ)` to be finite; so nobody can supply
`J = 0`.  Nor is it stronger than the truth: the honest Jacobian
`Pic⁰(X/ℚ)` satisfies every field, with `J(ℚ) ≅ ℤ/21` (see below).  It is
correspondingly a *hard* leaf — its content is precisely the four missing
theories — and no part of the argument is hidden inside it that could
have been discharged here instead: the two finite computations, the
integral model, and the reduction map all live outside it.

**`card_coprime` is deliberately ABSENT.**  One might expect the package
to record `gcd(#J(ℚ), p) = 1` (here `21` and `5`).  It is not needed:
`red_ker_torsionFree` together with finiteness already gives injectivity,
because in a finite group every element is torsion.  The sharper input
`#J(𝔽₅) = 21` — reduction at `5` is an *isomorphism* — is therefore not
required either.  Stating only what is used keeps the leaf as weak as
possible, which is the direction that makes it easier to discharge.

## The arithmetic, computed externally (untrusted searchers, not proofs)

Recorded in `MazurLevel18.no_noncuspidal_point_on_smooth_model`'s
docstring and re-derived there independently of Magma; repeated here
because it is what makes the package's fields TRUE:

* `#J(𝔽ₚ) = 21, 63, 84, 189, 441` for `p = 5, 7, 11, 13, 17`, from raw
  point counts through the zeta numerator; `gcd = 21`, and the cuspidal
  group gives the reverse divisibility, so `J(ℚ)_tors ≅ ℤ/21`.
* `S₂(Γ₁(18))` has one newform orbit with `L(f, 1) ≈ 0.4103 − 0.0724i`
  and `lfunorderzero = 0`, so `L(J, 1) ≠ 0` and Kolyvagin–Logachev gives
  `rank J(ℚ) = 0`; Magma's `RankBound(J) = 0` agrees by a different
  computation.
* The Jacobian has conductor `324 = 18²`; the sextic has discriminant
  `−2¹⁵·3⁴`, so `5` is a prime of good reduction, which is what
  `red_ker_torsionFree` needs.

## Generality

`sext`, `hsext`, `AffPt`, `Pt`, `exists_int_coords`, `redAff`,
`redTriple` and `redPt` are stated for an arbitrary monic sextic
`x⁶ + c₅x⁵ + c₄x⁴ + c₃x³ + c₂x² + c₁x + c₀` over `ℤ` and an arbitrary
prime `p`, so the layer is reusable for the other genus-`2` modular
curves in this development; only `JacobianPackage`'s instantiation and
the two `X18` computations are specific.  Nothing here assumes
separability of the sextic — that hypothesis belongs to the *truth* of
the package's fields, not to the definitions, and it is why the package
is stated at a concrete sextic and prime rather than universally.

Coordinated with `Fermat/FLT/ModularCurve/X0.lean`, which owns `J_0(N)`
and Mordell–Weil for the level family: that layer is scheme-theoretic and
about modular curves as moduli, this one is the concrete hyperelliptic
model needed for one explicit curve.  They meet at "the Jacobian is a
finite group of rank `0`", which is item 4 in both.
-/
module

public import Mathlib.Tactic.Tauto
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Fermat

namespace Hyperelliptic

variable {R : Type*} [CommRing R]

/-- The monic sextic `x⁶ + c₅x⁵ + c₄x⁴ + c₃x³ + c₂x² + c₁x + c₀`, evaluated in
any commutative ring `R` through the canonical map from `ℤ`. -/
def sext (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (x : R) : R :=
  x ^ 6 + (c₅ : R) * x ^ 5 + (c₄ : R) * x ^ 4 + (c₃ : R) * x ^ 3
    + (c₂ : R) * x ^ 2 + (c₁ : R) * x + (c₀ : R)

/-- Its homogenisation `F(a, b) = b⁶ · sext (a/b)`, an integer form of degree `6`. -/
def hsext (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (a b : ℤ) : ℤ :=
  a ^ 6 + c₅ * a ^ 5 * b + c₄ * a ^ 4 * b ^ 2 + c₃ * a ^ 3 * b ^ 3
    + c₂ * a ^ 2 * b ^ 4 + c₁ * a * b ^ 5 + c₀ * b ^ 6

/-- Affine points of `y² = sext x` over `R`. -/
abbrev AffPt (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (R : Type*) [CommRing R] : Type _ :=
  {p : R × R // p.2 ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ p.1}

/-- `R`-points of the smooth projective model in `ℙ(1, 3, 1)`.

The sextic is monic, so its leading coefficient is a square and the two
points at infinity are `R`-rational: a point `[X : Y : Z]` with `Z = 0`
satisfies `Y² = X⁶` with `X` a unit, hence normalises to `[1 : ±1 : 0]`.
The `Bool` summand is that sign, `true` denoting the branch `Y/X³ = 1`. -/
abbrev Pt (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (R : Type*) [CommRing R] : Type _ :=
  AffPt c₀ c₁ c₂ c₃ c₄ c₅ R ⊕ Bool

section IntCoords

variable (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ)

/-- **Integral weighted-projective coordinates** (PROVEN).  A rational point
`(x, y)` of `y² = sext x` has `y · (x.den)³` an INTEGER `t`, and then
`t² = F(x.num, x.den)`.

The only non-formal step is integrality of `t`: its square is an integer, and
`ℤ` is integrally closed in `ℚ`, which is available here as `Rat.den_pow`
(`(t²).den = t.den²`, and `t²` has denominator `1`). -/
lemma exists_int_coords (x y : ℚ) (h : y ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ x) :
    ∃ t : ℤ, (t : ℚ) = y * (x.den : ℚ) ^ 3 ∧
      t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ x.num x.den := by
  have hb : ((x.den : ℚ)) ≠ 0 := by
    exact_mod_cast x.den_ne_zero
  have ha : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hb).mp (Rat.num_div_den x)
  have key : (y * (x.den : ℚ) ^ 3) ^ 2
      = ((hsext c₀ c₁ c₂ c₃ c₄ c₅ x.num x.den : ℤ) : ℚ) := by
    simp only [hsext, sext] at h ⊢
    push_cast
    rw [ha]
    linear_combination ((x.den : ℚ)) ^ 6 * h
  have hden : (y * (x.den : ℚ) ^ 3).den = 1 := by
    have h2 : ((y * (x.den : ℚ) ^ 3) ^ 2).den = 1 := by rw [key]; exact Rat.den_intCast _
    rw [Rat.den_pow] at h2
    simpa using h2
  refine ⟨(y * (x.den : ℚ) ^ 3).num, Rat.coe_int_num_of_den_eq_one hden, ?_⟩
  have hkey := key
  rw [← Rat.coe_int_num_of_den_eq_one hden] at hkey
  exact_mod_cast hkey

end IntCoords

section Reduce

variable (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ)

/-- Clearing denominators in the sextic: `sext (A/B) · B⁶ = F(A, B)`. -/
lemma sext_div {K : Type*} [Field K] (A B : K) (hB : B ≠ 0) :
    sext c₀ c₁ c₂ c₃ c₄ c₅ (A / B) * B ^ 6
      = A ^ 6 + (c₅ : K) * A ^ 5 * B + (c₄ : K) * A ^ 4 * B ^ 2 + (c₃ : K) * A ^ 3 * B ^ 3
        + (c₂ : K) * A ^ 2 * B ^ 4 + (c₁ : K) * A * B ^ 5 + (c₀ : K) * B ^ 6 := by
  simp only [sext]
  field_simp

/-- Reduction of an integral triple `[a : t : b]` at a prime not dividing `b`:
the affine point `(a/b, t/b³)` of the reduced curve. -/
def redAff {p : ℕ} [Fact p.Prime] (a b t : ℤ) (hb : (b : ZMod p) ≠ 0)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b) :
    AffPt c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p) :=
  ⟨((a : ZMod p) / (b : ZMod p), (t : ZMod p) / (b : ZMod p) ^ 3), by
    have ht' : ((t : ZMod p)) ^ 2 = (a : ZMod p) ^ 6 + (c₅ : ZMod p) * (a : ZMod p) ^ 5 * b
        + (c₄ : ZMod p) * (a : ZMod p) ^ 4 * (b : ZMod p) ^ 2
        + (c₃ : ZMod p) * (a : ZMod p) ^ 3 * (b : ZMod p) ^ 3
        + (c₂ : ZMod p) * (a : ZMod p) ^ 2 * (b : ZMod p) ^ 4
        + (c₁ : ZMod p) * (a : ZMod p) * (b : ZMod p) ^ 5
        + (c₀ : ZMod p) * (b : ZMod p) ^ 6 := by
      have hcast := congrArg (fun z : ℤ => (z : ZMod p)) ht
      simpa [hsext] using hcast
    have h1 : sext c₀ c₁ c₂ c₃ c₄ c₅ ((a : ZMod p) / (b : ZMod p)) * (b : ZMod p) ^ 6
        = (t : ZMod p) ^ 2 := by
      rw [sext_div c₀ c₁ c₂ c₃ c₄ c₅ _ _ hb, ← ht']
    have hb6 : (((b : ZMod p)) ^ 3) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hb)
    rw [div_pow, div_eq_iff hb6, ← h1]
    ring⟩

/-- Reduction of an integral weighted-projective triple `[a : t : b]`.

When `p ∣ b` the point lies over infinity; there `p ∤ a` (the coordinates of a
rational point are coprime), `t² ≡ a⁶`, so `t/a³ = ±1` and the reduced point is
the corresponding infinite point.  Totality does not need that fact — the sign
is read off as a `Bool` — but it is why the definition is the right one. -/
def redTriple {p : ℕ} [Fact p.Prime] (a b t : ℤ)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b) : Pt c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p) :=
  if hb : ((b : ZMod p)) ≠ 0 then
    Sum.inl (redAff c₀ c₁ c₂ c₃ c₄ c₅ a b t hb ht)
  else
    Sum.inr (decide ((t : ZMod p) / ((a : ZMod p)) ^ 3 = 1))

/-- **Reduction of points mod `p`**, `X(ℚ) → X(𝔽ₚ)`.  Infinite points reduce to
infinite points with the same sign; affine points reduce through their integral
coordinates. -/
noncomputable def redPt {p : ℕ} [Fact p.Prime] :
    Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ → Pt c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p) :=
  Sum.elim
    (fun q => redTriple c₀ c₁ c₂ c₃ c₄ c₅ q.1.1.num (q.1.1.den : ℤ)
      (exists_int_coords c₀ c₁ c₂ c₃ c₄ c₅ q.1.1 q.1.2 q.2).choose
      (exists_int_coords c₀ c₁ c₂ c₃ c₄ c₅ q.1.1 q.1.2 q.2).choose_spec.2)
    Sum.inr

end Reduce

section Package

/-- **The Jacobian layer, bundled.**  A `JacobianPackage` for the sextic
`c` at the prime `p` is the data of

* the Mordell–Weil group `J = J(ℚ)`, FINITE (this is `rank J(ℚ) = 0`);
* the group `J' = J(𝔽ₚ)`;
* the Abel–Jacobi map `aj : X(ℚ) → J`, INJECTIVE (genus `≥ 1`), and its
  counterpart `aj'` over `𝔽ₚ`;
* the reduction homomorphism `red : J →+ J'`, whose kernel is
  TORSION-FREE (the formal group of a `g`-dimensional abelian variety over
  `ℤₚ`, torsion-free for `p > e + 1`), and which is COMPATIBLE with the
  concrete point-reduction map `redPt`.

Everything the rank-`0` argument uses is here and nothing else; in
particular no coprimality between `#J(ℚ)` and `p` is assumed, because
finiteness plus a torsion-free kernel already forces `red` to be
injective. -/
structure JacobianPackage (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (p : ℕ) [Fact p.Prime] where
  /-- the Mordell–Weil group `J(ℚ)` -/
  J : Type
  [addCommGroup : AddCommGroup J]
  /-- Mordell–Weil plus rank `0` -/
  [fin : Finite J]
  /-- the group of `𝔽ₚ`-points of the Jacobian -/
  J' : Type
  [addCommGroup' : AddCommGroup J']
  /-- Abel–Jacobi, `P ↦ [P − ∞₊]` -/
  aj : Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ → J
  /-- injective because the genus is at least `1` -/
  aj_injective : Function.Injective aj
  /-- Abel–Jacobi over the residue field -/
  aj' : Pt c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p) → J'
  /-- reduction of the Jacobian at a prime of good reduction -/
  red : J →+ J'
  /-- the kernel of reduction is the formal group, hence torsion-free -/
  red_ker_torsionFree : ∀ z : J, red z = 0 → ∀ n : ℕ, n ≠ 0 → n • z = 0 → z = 0
  /-- reduction commutes with Abel–Jacobi -/
  red_aj : ∀ P, red (aj P) = aj' (redPt c₀ c₁ c₂ c₃ c₄ c₅ P)

attribute [instance] JacobianPackage.addCommGroup JacobianPackage.fin
  JacobianPackage.addCommGroup'

/-- **Reduction is injective on rational points** (PROVEN from the package).

This is the whole rank-`0` argument.  If two rational points reduce alike then
the difference of their Abel–Jacobi images lies in the kernel of reduction;
`J(ℚ)` is finite, so that difference is killed by `Nat.card J ≠ 0`; the kernel
is torsion-free, so the difference vanishes; and `aj` is injective. -/
theorem redPt_injective {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime]
    (D : JacobianPackage c₀ c₁ c₂ c₃ c₄ c₅ p) :
    Function.Injective (redPt c₀ c₁ c₂ c₃ c₄ c₅ (p := p)) := by
  intro P Q hPQ
  have h1 : D.red (D.aj P) = D.red (D.aj Q) := by
    rw [D.red_aj, D.red_aj, hPQ]
  have h2 : D.red (D.aj P - D.aj Q) = 0 := by
    rw [map_sub, h1, sub_self]
  have h3 : D.aj P - D.aj Q = 0 := by
    refine D.red_ker_torsionFree _ h2 (Nat.card D.J) ?_ ?_
    · have hpos : 0 < Nat.card D.J := Nat.card_pos
      omega
    · exact card_nsmul_eq_zero'
  exact D.aj_injective (sub_eq_zero.mp h3)

end Package

namespace X18

local instance factFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The `X_1(18)` sextic in the coefficient form used by this module. -/
theorem sext18 {R : Type*} [CommRing R] (x : R) :
    sext 1 (-2) 5 (-10) 10 (-4) x
      = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1 := by
  simp only [sext]
  push_cast
  ring

/-- **`#X(𝔽₅) = 6`** (PROVEN BY `decide`).

Modulo `5`, Fermat's little theorem gives `x⁶ + x⁵ ≡ x² + x`, so the sextic
reduces to `x² + 4x + 1`, with values `1, 1, 3, 2, 3` at `x = 0, 1, 2, 3, 4`.
Exactly two of those are squares in `𝔽₅`, giving `4` affine points; the two
points at infinity bring the total to `6`.  This count is the arithmetic input
that the whole rank-`0` argument turns on, and the kernel verifies it. -/
theorem card_X18_F5 : Fintype.card (Pt 1 (-2) 5 (-10) 10 (-4) (ZMod 5)) = 6 := by decide

/-- **THE REMAINING LEAF: the Jacobian of `X_1(18)` exists with rank `0`.**

Discharging this is the four-part project recorded in the module docstring and
in `MazurLevel18.no_noncuspidal_point_on_smooth_model`:

1. `Pic⁰` of a genus-`2` hyperelliptic curve, with the Mumford representation
   and Cantor's group law — this supplies `J`, `addCommGroup`, `J'`;
2. Abel–Jacobi from a rational base point, injective for genus `≥ 1` — this
   supplies `aj`, `aj_injective`, `aj'`;
3. good reduction at `5` (the discriminant is `−2¹⁵·3⁴` and the conductor is
   `324 = 18²`, so `5` is good), the reduction homomorphism, its compatibility
   with `redPt`, and torsion-freeness of its kernel — the kernel is the formal
   group over `ℤ₅`, torsion-free since `5 > e + 1 = 2`;
4. `rank J(ℚ) = 0`, giving `fin`.  Externally: `L(f, 1) ≈ 0.4103 − 0.0724i ≠ 0`
   for the unique newform orbit of `S₂(Γ₁(18))`, so Kolyvagin–Logachev applies;
   Magma's `RankBound(J) = 0` agrees.  With `J(ℚ)_tors ≅ ℤ/21` this makes
   `J(ℚ) ≅ ℤ/21`, though only its FINITENESS is used here.

**This leaf is not vacuous**: `aj_injective` and `fin` together force `X(ℚ)` to
be finite, so it cannot be met by a trivial group.  **Nor is it overstated**:
the honest `Pic⁰(X/ℚ)` satisfies every field. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 (-2) 5 (-10) 10 (-4) 5) := sorry

/-- The six cusps of `X_1(18)` — `(0, ±1)`, `(1, ±1)` and the two points at
infinity — together with a putative seventh point of abscissa `u`. -/
noncomputable def sevenPts (u v : ℚ) (h : v ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) u) :
    Fin 7 → Pt 1 (-2) 5 (-10) 10 (-4) ℚ :=
  ![Sum.inl ⟨(u, v), h⟩,
    Sum.inl ⟨(0, 1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(0, -1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(1, 1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(1, -1), by rw [sext18]; norm_num⟩,
    Sum.inr true,
    Sum.inr false]

/-- **The seven points are pairwise distinct** (PROVEN) as soon as `u ∉ {0, 1}`.

The argument is carried out after forgetting the defining equations — on the
underlying data in `(ℚ × ℚ) ⊕ Bool` — because the curve equation, kept in
context, is a rewrite rule that `simp_all` orients as `1 ↦ sext …` and loops on. -/
lemma sevenPts_injective (u v : ℚ) (h : v ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) u)
    (hx0 : u ≠ 0) (hx1 : u ≠ 1) : Function.Injective (sevenPts u v h) := by
  have hdata : Function.Injective (![Sum.inl (u, v), Sum.inl (0, 1), Sum.inl (0, -1),
      Sum.inl (1, 1), Sum.inl (1, -1), Sum.inr true, Sum.inr false] :
      Fin 7 → (ℚ × ℚ) ⊕ Bool) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      (try rfl) <;> (try exfalso) <;> (try norm_num at hij) <;> (try tauto)
  have hmap : ∀ i, Sum.map Subtype.val id (sevenPts u v h i)
      = (![Sum.inl (u, v), Sum.inl (0, 1), Sum.inl (0, -1),
          Sum.inl (1, 1), Sum.inl (1, -1), Sum.inr true, Sum.inr false] :
          Fin 7 → (ℚ × ℚ) ⊕ Bool) i := by
    intro i; fin_cases i <;> rfl
  intro a b hab
  refine hdata ?_
  rw [← hmap a, ← hmap b]
  exact congrArg _ hab

/-- **`X_1(18)` has no non-cuspidal rational point on its smooth model**
(PROVEN modulo `exists_jacobianPackage`).

`X(ℚ) ↪ X(𝔽₅)` by `redPt_injective`, and `#X(𝔽₅) = 6`; but a rational point
with `x ∉ {0, 1}` would be a seventh point of `X(ℚ)` alongside the six cusps.
`7 ≤ 6` is the contradiction.  No Chabauty and no Mordell–Weil sieve: only
rank `0` and one point count. -/
theorem no_noncuspidal_point (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hxy : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) :
    False := by
  obtain ⟨D⟩ := exists_jacobianPackage
  have hq : y ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) x := by rw [sext18]; exact hxy
  have hcard : Fintype.card (Fin 7)
      ≤ Fintype.card (Pt 1 (-2) 5 (-10) 10 (-4) (ZMod 5)) :=
    Fintype.card_le_of_injective _
      ((redPt_injective D).comp (sevenPts_injective x y hq hx0 hx1))
  rw [Fintype.card_fin, card_X18_F5] at hcard
  omega

end X18

namespace X13

local instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The `X_1(13)` sextic in the coefficient form used by this module.

This is Sutherland's optimal model of `X_1(13)`, the genus-`2` curve of
conductor `169`: completing the square in `y² + (x³ + x² + 1)y = x² + x`
gives `(2y + x³ + x² + 1)² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`. -/
theorem sext13 {R : Type*} [CommRing R] (x : R) :
    sext 1 4 6 2 1 2 x
      = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 := by
  simp only [sext]
  push_cast
  ring

/-- **`#X(𝔽₃) = 6`** (PROVEN BY `decide`).

Modulo `3` the sextic is `x⁶ + 2x⁵ + x⁴ + 2x³ + x + 1`, whose values at
`x = 0, 1, 2` are `1, 2, 1`.  Squares in `𝔽₃` are `{0, 1}`, so `x = 0` and
`x = 2` each give two affine points and `x = 1` gives none: `4` affine
points, plus the `2` points at infinity, is `6`.  This is the point count
the whole rank-`0` argument turns on, and the kernel verifies it.

`3` is a prime of good reduction: the sextic has discriminant `−2¹²·13²`
(PARI, untrusted), and `J_1(13)` has conductor `169 = 13²`.  It also
satisfies the formal-group hypothesis `p > e + 1 = 2` that
`red_ker_torsionFree` needs. -/
theorem card_X13_F3 : Fintype.card (Pt 1 4 6 2 1 2 (ZMod 3)) = 6 := by decide

/-- **THE REMAINING LEAF: the Jacobian of `X_1(13)` exists with rank `0`.**

Exactly the shape of `X18.exists_jacobianPackage`, and deliberately so: one
future development of genus-`2` Jacobians discharges both at once.  The four
parts are those recorded in this module's docstring:

1. `Pic⁰` of a genus-`2` hyperelliptic curve, with the Mumford representation
   and Cantor's group law — supplying `J`, `addCommGroup`, `J'`;
2. Abel–Jacobi from a rational base point, injective for genus `≥ 1` —
   supplying `aj`, `aj_injective`, `aj'`;
3. good reduction at `3` (the sextic's discriminant is `−2¹²·13²`, and the
   conductor of `J_1(13)` is `169`), the reduction homomorphism, its
   compatibility with `redPt`, and torsion-freeness of its kernel — the kernel
   is the formal group over `ℤ₃`, torsion-free since `3 > e + 1 = 2`;
4. `rank J(ℚ) = 0`, giving `fin`.  Externally (untrusted searchers): `J_1(13)`
   is `ℚ`-simple of dimension `2` with `J(ℚ)_tors ≅ ℤ/19`, and a `2`-descent
   gives `rank J(ℚ) = 0`, so `J(ℚ) ≅ ℤ/19`; equivalently `LRatio(J, 1) =
   1/361 ≠ 0`.  Only FINITENESS is used here.

This is Mazur–Tate, *Points of order 13 on elliptic curves*, Invent. Math. 22
(1973); subsumed in Mazur, IHÉS 47 (1977), Thm 7.

**Not vacuous**: `aj_injective` and `fin` together force `X(ℚ)` to be finite,
so no trivial group discharges it.  **Not overstated**: the honest
`Pic⁰(X/ℚ)` satisfies every field. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 4 6 2 1 2 3) := sorry

/-- The six cusps of `X_1(13)` — `(0, ±1)`, `(−1, ±1)` and the two points at
infinity — together with a putative seventh point of abscissa `u`.

`φ(13)/2 = 6`, so these six are all of them; the sextic takes the value `1` at
both `0` and `−1`, which is what makes the four affine cusps rational. -/
noncomputable def sevenPts (u v : ℚ) (h : v ^ 2 = sext 1 4 6 2 1 2 u) :
    Fin 7 → Pt 1 4 6 2 1 2 ℚ :=
  ![Sum.inl ⟨(u, v), h⟩,
    Sum.inl ⟨(0, 1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(0, -1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(-1, 1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(-1, -1), by rw [sext13]; norm_num⟩,
    Sum.inr true,
    Sum.inr false]

/-- **The seven points are pairwise distinct** (PROVEN) as soon as
`u ∉ {0, −1}`.

As at level `18`, the argument is carried out after forgetting the defining
equations — on the underlying data in `(ℚ × ℚ) ⊕ Bool` — because the curve
equation, kept in context, is a rewrite rule that `simp_all` orients as
`1 ↦ sext …` and loops on. -/
lemma sevenPts_injective (u v : ℚ) (h : v ^ 2 = sext 1 4 6 2 1 2 u)
    (hx0 : u ≠ 0) (hx1 : u ≠ -1) : Function.Injective (sevenPts u v h) := by
  have hdata : Function.Injective (![Sum.inl (u, v), Sum.inl (0, 1), Sum.inl (0, -1),
      Sum.inl (-1, 1), Sum.inl (-1, -1), Sum.inr true, Sum.inr false] :
      Fin 7 → (ℚ × ℚ) ⊕ Bool) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      (try rfl) <;> (try exfalso) <;> (try norm_num at hij) <;> (try tauto)
  have hmap : ∀ i, Sum.map Subtype.val id (sevenPts u v h i)
      = (![Sum.inl (u, v), Sum.inl (0, 1), Sum.inl (0, -1),
          Sum.inl (-1, 1), Sum.inl (-1, -1), Sum.inr true, Sum.inr false] :
          Fin 7 → (ℚ × ℚ) ⊕ Bool) i := by
    intro i; fin_cases i <;> rfl
  intro a b hab
  refine hdata ?_
  rw [← hmap a, ← hmap b]
  exact congrArg _ hab

/-- **`X_1(13)` has no non-cuspidal rational point on its smooth model**
(PROVEN modulo `exists_jacobianPackage`).

`X(ℚ) ↪ X(𝔽₃)` by `redPt_injective`, and `#X(𝔽₃) = 6`; but a rational point
with `x ∉ {0, −1}` would be a seventh point of `X(ℚ)` alongside the six cusps.
`7 ≤ 6` is the contradiction.  No Chabauty and no Mordell–Weil sieve: only
rank `0` and one point count. -/
theorem no_noncuspidal_point (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ -1)
    (hxy : y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1) :
    False := by
  obtain ⟨D⟩ := exists_jacobianPackage
  have hq : y ^ 2 = sext 1 4 6 2 1 2 x := by rw [sext13]; exact hxy
  have hcard : Fintype.card (Fin 7)
      ≤ Fintype.card (Pt 1 4 6 2 1 2 (ZMod 3)) :=
    Fintype.card_le_of_injective _
      ((redPt_injective D).comp (sevenPts_injective x y hq hx0 hx1))
  rw [Fintype.card_fin, card_X13_F3] at hcard
  omega

end X13

end Hyperelliptic

end Fermat
