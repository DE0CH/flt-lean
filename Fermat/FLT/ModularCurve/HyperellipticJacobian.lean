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
* `ptData`, `redTriple_congr`, `redPt_inl`, `ptData_redTriple_of_ne`,
  `ptData_redPt_inl` (all PROVEN) — the machinery that COMPUTES `redPt` at a
  concrete rational point.  `redPt` goes through `Classical.choose`, so its
  value is not directly reducible; the choice is however pinned by injectivity
  of `ℤ → ℚ`, and comparing points through their raw data (`ptData`, which
  drops the `Subtype` proof) removes the motive failures that otherwise block
  every rewrite.
* `X18.red_sixPts` and `X18.sixPtsData_injective` (PROVEN, the latter by
  `decide`) — the six cusps reduce mod `5` to six DISTINCT points.  With
  `card_X18_F5` this says the cusps fill `X(𝔽₅)` exactly.
* `X18.redPt_injective_five` (PROVEN from the leaf below) — reduction at `5` is
  injective on `X(ℚ)`.

## The single remaining leaf

`X18.affine_rational_points` — the affine rational points of `X_1(18)` are
`(0, ±1)` and `(1, ±1)`.

**This replaced the former leaf `X18.redPt_injective_five`, which is now PROVEN**
(2026-07-26), which had itself replaced `X18.exists_jacobianPackage`.  Each
replacement is an EQUIVALENCE, so no statement was weakened at either step:

* `exists_jacobianPackage ↔ redPt_injective_five` by `redPt_injective` and
  `nonempty_jacobianPackage_of_redPt_injective`, both proven here;
* `redPt_injective_five ↔ affine_rational_points` by `red_sixPts` plus
  `sixPtsData_injective` forwards, and by `sevenPts_injective` plus
  `card_X18_F5` backwards (the argument of `no_noncuspidal_point`, plus
  `y² = 1 ⟹ y = ±1` at `x ∈ {0, 1}`); the backwards direction is written out in
  `affine_rational_points`' docstring rather than as a declaration, since
  nothing in the root cone consumes it.

What each step removed is a layer of Lean-specific interface: first the
obligation to exhibit a *structure*, then the obligation to reason about a
`Classical.choose`n reduction map.  What is left is one sextic Diophantine
equation.  **Neither step is progress on abelian varieties**, and the leaf count
is unchanged at one throughout.

**FORMAL-CONTENT AUDIT: `JacobianPackage`'s abelian-variety structure is not
load-bearing, and the previous audit in this docstring was WRONG.**  It
asserted that the package is "not discharged by junk" because `aj_injective`
plus `fin` force `X(ℚ)` to be finite.  That argument shows only that the
package implies finiteness; it does not show that the package needs a Jacobian.
It does not: once `redPt` is known injective, the whole package is met by the
free `𝔽₂`-vector spaces on `X(ℚ)` and `X(𝔽ₚ)` with `red = Finsupp.mapDomain
redPt` — no divisor classes, no group law, no formal group, no Mordell–Weil.
`red_ker_torsionFree` is then satisfied for the *strong* reason that `red` is
outright injective, so its torsion hypotheses are never used.

So the arithmetic content of items 1–4 lives entirely in the injectivity
statement, which is where the sorry now is.  Closing `exists_jacobianPackage`
was the removal of an interface obligation, **not** progress on abelian
varieties, and it should not be counted as such.

The package is kept, and `no_noncuspidal_point` still routes through it,
because it is the intended plug-in point: when the honest `Pic⁰(X/ℚ)` is
built it satisfies every field, and `redPt_injective` then discharges the
leaf with no consumer changing.  What the honest Jacobian gives, and the junk
witness does not, is a *proof* of the injectivity.

| field | item |
|---|---|
| `J`, `addCommGroup` | 1 — `Pic⁰` of the curve, as a group |
| `aj`, `aj_injective` | 2 — Abel–Jacobi from a rational base point; injective because the genus is `2 ≥ 1` |
| `red`, `red_aj` | 3 — reduction is a group homomorphism compatible with `redPt` |
| `red_ker_torsionFree` | 3 — the kernel of reduction is the formal group over `ℤ₅`, torsion-free because `5 > e + 1 = 2` |
| `fin` | 4 — Mordell–Weil plus `rank J(ℚ) = 0` |

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
public import Mathlib.Data.Finsupp.Basic

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

/-- **The raw DATA of a point**, forgetting the defining equation.

Reduction computations are carried out through this map rather than on `Pt`
itself.  `redPt` is defined through `Classical.choose`, so its value carries a
`Subtype` proof mentioning the chosen integral coordinate; rewriting that
coordinate inside the proof fails on the motive.  Stripping the proof first
removes the obstruction and loses nothing, a `Subtype` element being determined
by its value. -/
def ptData : Pt c₀ c₁ c₂ c₃ c₄ c₅ R → (R × R) ⊕ Bool :=
  Sum.map Subtype.val id

/-- `redTriple` depends on the integral coordinate `t` only through its VALUE
(PROVEN): the defining equation enters as a proof argument, and proofs are
definitionally irrelevant.  This is what lets an explicitly exhibited coordinate
replace the `Classical.choose`n one. -/
lemma redTriple_congr {p : ℕ} [Fact p.Prime] (a b t t' : ℤ)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b)
    (ht' : t' ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b) (h : t = t') :
    redTriple c₀ c₁ c₂ c₃ c₄ c₅ (p := p) a b t ht
      = redTriple c₀ c₁ c₂ c₃ c₄ c₅ (p := p) a b t' ht' := by
  subst h
  rfl

/-- **`redPt` at an affine point, through ANY valid integral coordinate**
(PROVEN).  The choice made by `redPt` is pinned by injectivity of `ℤ → ℚ`: any
`t` with `t = y · den³` IS the chosen one. -/
lemma redPt_inl {p : ℕ} [Fact p.Prime] (x y : ℚ)
    (h : y ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ x) (t : ℤ)
    (hty : (t : ℚ) = y * (x.den : ℚ) ^ 3)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ x.num x.den) :
    redPt c₀ c₁ c₂ c₃ c₄ c₅ (p := p) (Sum.inl ⟨(x, y), h⟩)
      = redTriple c₀ c₁ c₂ c₃ c₄ c₅ x.num (x.den : ℤ) t ht := by
  have hchoose : (exists_int_coords c₀ c₁ c₂ c₃ c₄ c₅ x y h).choose = t := by
    have hspec := (exists_int_coords c₀ c₁ c₂ c₃ c₄ c₅ x y h).choose_spec.1
    exact_mod_cast hspec.trans hty.symm
  exact redTriple_congr c₀ c₁ c₂ c₃ c₄ c₅ x.num (x.den : ℤ) _ t _ ht hchoose

/-- Data of a reduced triple at a prime NOT dividing the denominator (PROVEN):
the affine coordinates `(a/b, t/b³)` of the reduced curve. -/
lemma ptData_redTriple_of_ne {p : ℕ} [Fact p.Prime] (a b t : ℤ)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b) (hb : ((b : ZMod p)) ≠ 0) :
    ptData c₀ c₁ c₂ c₃ c₄ c₅ (redTriple c₀ c₁ c₂ c₃ c₄ c₅ a b t ht)
      = Sum.inl ((a : ZMod p) / (b : ZMod p), (t : ZMod p) / (b : ZMod p) ^ 3) := by
  have hdif : redTriple c₀ c₁ c₂ c₃ c₄ c₅ a b t ht
      = Sum.inl (redAff c₀ c₁ c₂ c₃ c₄ c₅ a b t hb ht) := dif_pos hb
  rw [hdif]
  rfl

/-- **`redPt` at an affine point with denominator prime to `p`, as raw data**
(PROVEN).  The coordinates `a = x.num`, `b = x.den` are passed as hypotheses so
that a caller can supply concrete numerals: the conclusion is proof-free data,
so they may be rewritten there, which they could not be inside `redTriple`. -/
lemma ptData_redPt_inl {p : ℕ} [Fact p.Prime] (x y : ℚ)
    (h : y ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ x) (a b t : ℤ)
    (hnum : x.num = a) (hden : (x.den : ℤ) = b)
    (hty : (t : ℚ) = y * (b : ℚ) ^ 3)
    (ht : t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b) (hb : ((b : ZMod p)) ≠ 0) :
    ptData c₀ c₁ c₂ c₃ c₄ c₅
        (redPt c₀ c₁ c₂ c₃ c₄ c₅ (p := p) (Sum.inl ⟨(x, y), h⟩))
      = Sum.inl ((a : ZMod p) / (b : ZMod p), (t : ZMod p) / (b : ZMod p) ^ 3) := by
  subst hnum
  subst hden
  have hty' : (t : ℚ) = y * (x.den : ℚ) ^ 3 := by push_cast at hty ⊢; exact hty
  rw [redPt_inl c₀ c₁ c₂ c₃ c₄ c₅ x y h t hty' ht,
    ptData_redTriple_of_ne c₀ c₁ c₂ c₃ c₄ c₅ x.num (x.den : ℤ) t ht hb]

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

/-- **CONVERSE: injectivity of `redPt` already BUILDS a package** (PROVEN).

Together with `redPt_injective` this says that, over a finite residue field,

    `Nonempty (JacobianPackage c p)`  ↔  `Function.Injective (redPt c (p := p))`

so the two are *equivalent*, not merely one-way related.  The witness built
here is deliberate junk: `J` is the free `𝔽₂`-vector space on `X(ℚ)`, `J'` the
free `𝔽₂`-vector space on `X(𝔽ₚ)`, `aj` and `aj'` the basis inclusions, and
`red` the pushforward `Finsupp.mapDomain redPt`.  Then

* `fin` holds because `redPt` injective into a finite type makes `X(ℚ)` finite;
* `aj_injective` is `Finsupp.single_left_injective`;
* `red_aj` is `Finsupp.mapDomain_single`, definitionally;
* `red_ker_torsionFree` holds for the *strong* reason that `red` is outright
  injective (`Finsupp.mapDomain_injective`) — the torsion hypotheses `n ≠ 0`
  and `n • z = 0` are never used, which is why they appear as `_` in the proof.

**FORMAL-CONTENT AUDIT — the abelian-variety structure of `JacobianPackage` is
NOT load-bearing.**  Everything in the package beyond the concrete conclusion
`redPt` is injective can be met by this junk group; no divisor classes, no
group law, no formal group and no Mordell–Weil theorem are needed to satisfy
the fields once that injectivity is known.  The package is therefore best read
as a *convenient plug-in point* for the eventual honest `Pic⁰(X/ℚ)` — which
does satisfy every field — and **not** as an independent statement of the
four-part Jacobian project.  The project is the content of the injectivity,
which since 2026-07-26 is itself PROVEN from the Diophantine determination of
`X(ℚ)`; the sorry now lives one step further down, at
`X18.affine_rational_points`.

This matters for anyone auditing the leaf count: closing `exists_jacobianPackage`
below is *not* progress on abelian varieties.  It is the removal of an interface
obligation that was never carrying arithmetic. -/
theorem nonempty_jacobianPackage_of_redPt_injective
    {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime] [Finite (ZMod p)]
    (h : Function.Injective (redPt c₀ c₁ c₂ c₃ c₄ c₅ (p := p))) :
    Nonempty (JacobianPackage c₀ c₁ c₂ c₃ c₄ c₅ p) := by
  haveI hfinQ : Finite (Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ) := Finite.of_injective _ h
  haveI hfinJ : Finite (Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ →₀ ZMod 2) :=
    Finite.of_equiv (Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ → ZMod 2) Finsupp.equivFunOnFinite.symm
  refine ⟨{ J := Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ →₀ ZMod 2
            J' := Pt c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p) →₀ ZMod 2
            aj := fun P => Finsupp.single P 1
            aj_injective := Finsupp.single_left_injective (by decide)
            aj' := fun Q => Finsupp.single Q 1
            red := Finsupp.mapDomain.addMonoidHom (redPt c₀ c₁ c₂ c₃ c₄ c₅)
            red_ker_torsionFree := ?_
            red_aj := ?_ }⟩
  · intro z hz _ _ _
    refine Finsupp.mapDomain_injective h ?_
    rw [Finsupp.mapDomain_zero]
    exact hz
  · intro P
    exact Finsupp.mapDomain_single

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

/-- **THE REMAINING LEAF, now in purely Diophantine form: the affine rational
points of `X_1(18)` are its four finite cusps.**

This *replaces* the former leaf `redPt_injective_five`, which is now PROVEN from
it below.  Nothing has been weakened, because the two are EQUIVALENT:

* forwards — this leaf pins `X(ℚ)` to the six points `sixPts`, whose reductions
  mod `5` are computed in `red_sixPts` and are pairwise distinct, giving
  `redPt_injective_five`;
* backwards — from `redPt_injective_five`, a rational point with `x ∉ {0, 1}`
  would give seven distinct points of `X(ℚ)` (`sevenPts_injective`) injecting
  into the six of `X(𝔽₅)` (`card_X18_F5`), which is `7 ≤ 6`; and at `x ∈ {0, 1}`
  the sextic takes the value `1`, so `y² = 1` and `y = ±1`.

What the restatement buys is that the obligation no longer mentions `redPt`,
`Classical.choose`, weighted-projective coordinates or reduction at all.  It is
a statement about integer solutions of one sextic equation, which is the form in
which the literature proves it and the form a descent argument can attack.

Discharging it is the four-part project recorded in the module docstring and in
`MazurLevel18.no_noncuspidal_point_on_smooth_model`:

1. `Pic⁰` of a genus-`2` hyperelliptic curve, with the Mumford representation
   and Cantor's group law — the group `J = J(ℚ)` and its reduction `J(𝔽₅)`;
2. Abel–Jacobi from a rational base point, injective for genus `≥ 1`;
3. good reduction at `5` (the discriminant is `−2¹⁵·3⁴` and the conductor is
   `324 = 18²`, so `5` is good), the reduction homomorphism, its compatibility
   with `redPt`, and torsion-freeness of its kernel — the kernel is the formal
   group over `ℤ₅`, torsion-free since `5 > e + 1 = 2`;
4. `rank J(ℚ) = 0`.  Externally: `L(f, 1) ≈ 0.4103 − 0.0724i ≠ 0` for the
   unique newform orbit of `S₂(Γ₁(18))`, so Kolyvagin–Logachev applies; Magma's
   `RankBound(J) = 0` agrees.  With `J(ℚ)_tors ≅ ℤ/21` this makes
   `J(ℚ) ≅ ℤ/21`, though only its FINITENESS is used.

Given 1–4 the route is `redPt_injective` applied to the resulting package, then
`redPt_injective_five`, then the backwards direction above; every step of that
is already written and proven here.

**RECONNAISSANCE FOR WHOEVER TAKES THIS ON** (PARI/GP, untrusted searcher, so
each item is a claim to be re-derived and not a proof):

* the sextic is IRREDUCIBLE over `ℚ`, with discriminant `−2¹⁵·3⁴`.  So there is
  no factorisation `f = g·h` to descend along, and no elementary two-cover
  argument of the kind that settles many genus-`2` curves;
* the curve carries an ORDER-`3` AUTOMORPHISM
  `σ(x, y) = (1/(1 − x), y/(1 − x)³)`, the identity
  `f(1/(1 − x))·(1 − x)⁶ = f(x)` being exact (verified as a polynomial
  identity).  `σ` cycles `0 ↦ 1 ↦ ∞ ↦ 0`, so the six rational points form a
  SINGLE orbit under `⟨σ, ι⟩ ≅ ℤ/6` with `ι` the hyperelliptic involution.
  This is the geometric source of the `ℤ[ζ₃]`-action on `J` and of
  `#J(ℚ) = 21 = 3·7`; it also means `J` is of `GL₂`-type with non-rational
  coefficient field, hence NOT isogenous to a product of elliptic curves over
  `ℚ` — a route through elliptic curves of rank `0` is therefore closed;
* every quotient of the curve by a subgroup of `⟨σ, ι⟩` has genus `0`
  (Riemann–Hurwitz), which closes the same route a second way;
* a search over `x = a/b` with `|a| ≤ 80`, `1 ≤ b ≤ 40`, `gcd(a, b) = 1` finds
  exactly `x = 0` and `x = 1`, consistent with the statement.

**Not vacuous, and not overstated.**  It asserts that a genus-`2` curve has
exactly four affine rational points; it is TRUE, `X_1(18)(ℚ)` consisting of its
six cusps, which is the classical statement that no elliptic curve over `ℚ` has
a rational point of order `18`. -/
theorem affine_rational_points (x y : ℚ)
    (h : y ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) x) :
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := sorry

/-- The six cusps of `X_1(18)`: `(0, ±1)`, `(1, ±1)`, and the two points at
infinity.  Under the order-`3` automorphism `σ(x, y) = (1/(1 − x), y/(1 − x)³)`
recorded on `affine_rational_points` they form a single `⟨σ, ι⟩`-orbit, `σ`
cycling `0 ↦ 1 ↦ ∞ ↦ 0`. -/
def sixPts : Fin 6 → Pt 1 (-2) 5 (-10) 10 (-4) ℚ :=
  ![Sum.inl ⟨(0, 1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(0, -1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(1, 1), by rw [sext18]; norm_num⟩,
    Sum.inl ⟨(1, -1), by rw [sext18]; norm_num⟩,
    Sum.inr true,
    Sum.inr false]

/-- The reductions of the six cusps mod `5`, as raw data.  All four finite cusps
have denominator `1`, so they reduce affinely, with `−1 = 4` in `𝔽₅`; the two
infinite points reduce to themselves. -/
def sixPtsData : Fin 6 → ((ZMod 5) × (ZMod 5)) ⊕ Bool :=
  ![Sum.inl (0, 1), Sum.inl (0, 4), Sum.inl (1, 1), Sum.inl (1, 4),
    Sum.inr true, Sum.inr false]

/-- **The six reduced points are pairwise distinct** (PROVEN BY `decide`).  This
is the second machine-checked arithmetic input of the argument, after
`card_X18_F5`: together they say the six cusps fill `X(𝔽₅)` exactly. -/
lemma sixPtsData_injective : Function.Injective sixPtsData := by decide

/-- **The six cusps reduce as stated** (PROVEN, by computation).

Each finite cusp `(x, y)` has `x.den = 1`, so its integral weighted-projective
coordinates are `[x.num : y : 1]` and `5 ∤ 1`; `ptData_redPt_inl` then computes
the reduction as `(x.num/1, y/1³)` in `𝔽₅`.  The infinite points are handled by
`redPt`'s definition, which is `Sum.inr` on that summand. -/
lemma red_sixPts (i : Fin 6) :
    ptData 1 (-2) 5 (-10) 10 (-4)
        (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5) (sixPts i)) = sixPtsData i := by
  fin_cases i
  · show ptData 1 (-2) 5 (-10) 10 (-4) (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)
      (Sum.inl ⟨((0 : ℚ), (1 : ℚ)), by rw [sext18]; norm_num⟩)) = Sum.inl (0, 1)
    rw [ptData_redPt_inl 1 (-2) 5 (-10) 10 (-4) (p := 5) 0 1 _ 0 1 1
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_zero, Int.cast_one, one_pow, div_one]
  · show ptData 1 (-2) 5 (-10) 10 (-4) (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)
      (Sum.inl ⟨((0 : ℚ), (-1 : ℚ)), by rw [sext18]; norm_num⟩)) = Sum.inl (0, 4)
    rw [ptData_redPt_inl 1 (-2) 5 (-10) 10 (-4) (p := 5) 0 (-1) _ 0 1 (-1)
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, one_pow, div_one]
    decide
  · show ptData 1 (-2) 5 (-10) 10 (-4) (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)
      (Sum.inl ⟨((1 : ℚ), (1 : ℚ)), by rw [sext18]; norm_num⟩)) = Sum.inl (1, 1)
    rw [ptData_redPt_inl 1 (-2) 5 (-10) 10 (-4) (p := 5) 1 1 _ 1 1 1
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_one, one_pow, div_one]
  · show ptData 1 (-2) 5 (-10) 10 (-4) (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)
      (Sum.inl ⟨((1 : ℚ), (-1 : ℚ)), by rw [sext18]; norm_num⟩)) = Sum.inl (1, 4)
    rw [ptData_redPt_inl 1 (-2) 5 (-10) 10 (-4) (p := 5) 1 (-1) _ 1 1 (-1)
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_one, Int.cast_neg, one_pow, div_one]
    decide
  · rfl
  · rfl

/-- **Every rational point is one of the six cusps** (PROVEN from the leaf).
The affine case is `affine_rational_points`; the two infinite points are the
`Bool` summand of `Pt`, which is exhaustive by construction. -/
lemma exists_eq_sixPts (P : Pt 1 (-2) 5 (-10) 10 (-4) ℚ) : ∃ i, P = sixPts i := by
  rcases P with ⟨⟨x, y⟩, h⟩ | b
  · rcases affine_rational_points x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · cases b
    · exact ⟨5, rfl⟩
    · exact ⟨4, rfl⟩

/-- **Reduction at `5` is injective on `X_1(18)(ℚ)`** (PROVEN from
`affine_rational_points`).

Formerly the leaf of this module.  Given the determination of `X(ℚ)` the proof
is a finite computation and nothing else: both points are cusps
(`exists_eq_sixPts`), their reductions are computed by `red_sixPts`, and the six
values are distinct by `sixPtsData_injective`.  No Jacobian, no formal group and
no Mordell–Weil enters here — all of that sits in the leaf above, which is where
the arithmetic is. -/
theorem redPt_injective_five :
    Function.Injective (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)) := by
  intro P Q hPQ
  obtain ⟨i, rfl⟩ := exists_eq_sixPts P
  obtain ⟨j, rfl⟩ := exists_eq_sixPts Q
  have hdata : sixPtsData i = sixPtsData j := by
    rw [← red_sixPts i, ← red_sixPts j, hPQ]
  rw [sixPtsData_injective hdata]

/-- **The Jacobian package of `X_1(18)` exists** (PROVEN from
`redPt_injective_five`).

Formerly the leaf of this module.  It is retained — rather than bypassed in
`no_noncuspidal_point` — because it is the intended plug-in point for the
honest `Pic⁰(X/ℚ)`.  Read the audit on
`nonempty_jacobianPackage_of_redPt_injective` before recording this as progress
on abelian varieties: it is not.

**How to plug in a real Jacobian, since the chain now runs the other way.**  The
proofs currently compose as

    affine_rational_points (LEAF) → redPt_injective_five → exists_jacobianPackage

so a real `Pic⁰` cannot simply be dropped in underneath: it proves
`exists_jacobianPackage` directly, which would close a cycle.  The rewiring is
three edits and no statement changes.  Prove this theorem from the real package;
replace `redPt_injective_five`'s proof by `redPt_injective D` for that package;
and prove `affine_rational_points` from `redPt_injective_five` by the backwards
argument recorded in its docstring (`sevenPts_injective` and `card_X18_F5` give
`x ∈ {0, 1}`, then `y² = 1`).  Every consumer outside this module is untouched,
which is the property the bundling exists to provide. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 (-2) 5 (-10) 10 (-4) 5) :=
  nonempty_jacobianPackage_of_redPt_injective redPt_injective_five

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

end Hyperelliptic

end Fermat
