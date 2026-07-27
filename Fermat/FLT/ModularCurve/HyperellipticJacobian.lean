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
* `X18.red_sixPts` / `X13.red_sixPts` and `X18.sixPtsData_injective` /
  `X13.sixPtsData_injective` (PROVEN, the latter pair by `decide`) — the six
  cusps reduce mod `5` (resp. mod `3`) to six DISTINCT points.  With
  `card_X18_F5` (resp. `card_X13_F3`) this says the cusps fill `X(𝔽ₚ)` exactly.
* `X18.redPt_injective_five` and `X13.redPt_injective_three` (both PROVEN from
  the leaves below) — reduction is injective on `X(ℚ)` at each level.
* `X18.sext18_eq_sq_add_eight_sq` and `X18.hsext18_eq_sq_add_eight_sq` (PROVEN,
  `ring`, axiom-clean) — the sextic is the PRINCIPAL binary quadratic form of
  discriminant `−32` evaluated at the two `σ`-semi-invariants:
  `f = (x³ − 2x² − x + 1)² + 8(x² − x)²`, and the same homogeneously.  This is
  the structural identity behind `disc f = −2¹⁵·3⁴`; see its docstring for the
  `σ`-derivation, the genus-`0` quotient conic `z² = t² − 4t + 12`, and the
  cyclic-cubic fibration.
* `X13.sext13_eq_sq_add_four_sq` and `X13.hsext13_eq_sq_add_four_sq` (PROVEN,
  `ring`, axiom-clean, 2026-07-27) — the exact level-`13` analogue:
  `f = (x³ + x² − 2x − 1)² + 4(x² + x)²`, the PRINCIPAL form of discriminant
  `−16`, i.e. a norm form from `ℤ[i]`.  **This REFUTES the paragraph headed
  "NOT ANALOGOUS AT LEVEL 13" in `X18.abd_eq_zero_of_sq_eq`'s route audit**,
  which asserts no such identity exists; that argument only forces the top two
  coefficients of the cube, not its linear one.  See the docstring for the
  refutation, the `σ`-derivation, the quotient conic `z² = t² − 4t + 8`, and the
  Shanks simplest-cubic fibration with the SAME discriminant `(t² − 3t + 9)²` as
  at level `18`.
* `holds_num_den_of_sq_eq_sext` and `eq_intCast_of_num_eq_mul_den` (PROVEN,
  axiom-clean, 2026-07-27) — the `ℚ`-to-`ℤ` passage and the reading-off of a
  degenerate abscissa, stated GENERICALLY for an arbitrary sextic, so neither
  level has to open-code them.
* `X18.affine_rational_points` and `X13.affine_rational_points` (both PROVEN
  from the leaves below, 2026-07-27) — the affine rational points of `X_1(18)`
  are `(0, ±1)` and `(1, ±1)`; those of `X_1(13)` are `(0, ±1)` and `(−1, ±1)`.
  They carry the whole `ℚ`-to-`ℤ` passage.

## The remaining leaves — one per level, and the SAME statement shape

`X18.abd_eq_zero_of_sq_eq` — for coprime `a, b : ℤ`, if
`t² = C̃(a, b)² + 8·B̃(a, b)²` then `ab(a − b) = 0`, where
`C̃ = a³ − 2a²b − ab² + b³` and `B̃ = ab(a − b)`.  A statement about integers
only: no rationals, no denominators, no `redPt`, no `Classical.choose`.

`X13.abd_eq_zero_of_sq_eq` — for coprime `a, b : ℤ`, if
`t² = C̃(a, b)² + 4·B̃(a, b)²` then `ab(a + b) = 0`, where
`C̃ = a³ + a²b − 2ab² − b³` and `B̃ = ab(a + b)`.  Same shape, same purity.

The two chains ran the same route and, since 2026-07-27, have reached the same
stage: both levels are now down to an integral sextic Diophantine leaf, and
`X13.affine_rational_points` and `X18.affine_rational_points` are both PROVEN.
Every replacement is an EQUIVALENCE, so no statement was weakened at any step:

* `exists_jacobianPackage ↔ redPt_injective` (at either prime) by
  `redPt_injective` and `nonempty_jacobianPackage_of_redPt_injective`, both
  proven here and both stated for an ARBITRARY sextic and prime; what was
  removed is the obligation to exhibit a *structure*.
* `redPt_injective ↔ affine_rational_points` (both levels) by `red_sixPts` plus
  `sixPtsData_injective` forwards, and by `sevenPts_injective` plus the point
  count backwards (the argument of `no_noncuspidal_point`, plus
  `y² = 1 ⟹ y = ±1` at the two cuspidal abscissae); the backwards direction is
  written out in `affine_rational_points`' docstring rather than as a
  declaration, since nothing in the root cone consumes it.
* `affine_rational_points ↔ abd_eq_zero_of_sq_eq` (BOTH levels since
  2026-07-27) by `exists_int_coords` and the level's sum-of-squares identity
  forwards (the direction that is written), and by `x := a/b` backwards; the two
  differ only by clearing denominators.  At level `13` the forward direction
  goes through the GENERIC bridge `holds_num_den_of_sq_eq_sext`, which states
  the whole `ℚ`-to-`ℤ` passage once for an arbitrary sextic; level `18` still
  open-codes it and can be rewritten over the bridge without changing either its
  statement or its leaf.

What each step removed is a layer of Lean-specific interface: first the
obligation to exhibit a *structure*, then the obligation to reason about a
`Classical.choose`n reduction map, then (at level `18`) the passage from `ℚ`
to `ℤ`.  What is left is one sextic Diophantine equation per level, over `ℤ`
at level `18` and over `ℚ` at level `13`.  **No step is progress on abelian
varieties**, and no step changed the sorry COUNT: one leaf closed, one opened,
at each level, throughout.

**What the 2026-07-27 step DID add, beyond bookkeeping**, is two axiom-clean
identities and one NEGATIVE result: the `ℤ[√−2]` descent that the identity
invites is provably reversible and so cannot reduce the leaf.  That audit, with
the check that would refute it, is on `abd_eq_zero_of_sq_eq`.  Reading it before
attacking either level is worth the two minutes.

The value of the whole chain is that the surviving obligations mention neither
`redPt` nor `Classical.choose` nor weighted-projective coordinates, and that the
machinery computing `redPt` at a concrete point is generic in `(sextic, p)`, so
it served both levels unchanged and will serve any further genus-`2` modular
curve in this development.  Level `13` can be pushed to the integral form too by
the same `exists_int_coords` route if anyone wants it in that shape.

Note that the earlier level-`18`-only phrasing of this section ("the single
remaining leaf") was already stale when the `X13` namespace was added below it;
it is corrected here.

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

/-- **THE `ℚ`-TO-`ℤ` BRIDGE, STATED GENERICALLY** (PROVEN, for an ARBITRARY
sextic).  `(x.num, x.den)` is a COPRIME integral solution of the homogeneous
form, so any property `P` of coprime integral solutions of `t² = F(a, b)`
transfers to every rational point `(x, y)` of `y² = sext x`.

This packages the whole passage from `ℚ` to `ℤ` — denominators, the integrality
of `y · den³`, and coprimality — ONCE and for all levels, so a level-specific
Diophantine leaf never has to restate it.  It is the generic form of the step
that `X18.affine_rational_points` and `X13.affine_rational_points` each perform
by hand; `X13` is written over it below, and `X18` can be rewritten over it
without changing its statement or its leaf. -/
lemma holds_num_den_of_sq_eq_sext (P : ℤ → ℤ → Prop)
    (hP : ∀ a b t : ℤ, Int.gcd a b = 1 →
      t ^ 2 = hsext c₀ c₁ c₂ c₃ c₄ c₅ a b → P a b)
    (x y : ℚ) (h : y ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ x) :
    P x.num (x.den : ℤ) := by
  obtain ⟨t, -, ht⟩ := exists_int_coords c₀ c₁ c₂ c₃ c₄ c₅ x y h
  refine hP x.num (x.den : ℤ) t ?_ ht
  rw [Int.gcd_def]
  exact x.reduced

/-- **Reading off a degenerate abscissa** (PROVEN): `x.num = k · x.den` forces
`x = k`.  Generic in `k`, so it serves every level: `k = 0` gives `x = 0`,
`k = 1` gives `x = 1` (level `18`), `k = −1` gives `x = −1` (level `13`). -/
lemma eq_intCast_of_num_eq_mul_den (x : ℚ) (k : ℤ)
    (h : x.num = k * (x.den : ℤ)) : x = (k : ℚ) := by
  have hd : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hnum : ((x.num : ℚ)) = (k : ℚ) * (x.den : ℚ) := by exact_mod_cast h
  have hx := Rat.num_div_den x
  rw [hnum, mul_div_assoc, div_self hd, mul_one] at hx
  exact hx.symm

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
which at both levels is itself PROVEN from the Diophantine determination of
`X(ℚ)` (level `18` on 2026-07-26, level `13` on 2026-07-27); the sorries now
live further down, at `X18.abd_eq_zero_of_sq_eq` and `X13.abd_eq_zero_of_sq_eq`
— the integral forms of that determination, one step beyond
`affine_rational_points` at each level since 2026-07-27.

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

/-- **The `X_1(18)` sextic is a norm form from `ℤ[√−2]`** (PROVEN, `ring`):

`x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1 = (x³ − 2x² − x + 1)² + 8(x² − x)²`.

This is not a coincidence and it is the structural fact about the curve, so it
is worth recording where it comes from.  The order-`3` automorphism
`σ(x, y) = (1/(1 − x), y/(1 − x)³)` acts on the `x`-line by `x ↦ 1/(1 − x)`,
whose two basic semi-invariants are

* `A(x) = x³ − 3x + 1`, with `A(σx)(1 − x)³ = −A(x)` — its splitting field is the
  cyclic cubic of conductor `9`, i.e. the real subfield of `ℚ(ζ₉)`, matching
  `disc A = 81`;
* `B(x) = x² − x`, with `B(σx)(1 − x)² = −B(x)`; also `q(x) = x² − x + 1`
  satisfies `q(σx)(1 − x)² = q(x)`, and `q³ = B²·(t² − 3t + 9)` below.

Every `σ`-semi-invariant sextic is therefore a binary quadratic form in `A` and
`B`, and this one is `f = A² − 4AB + 12B²`, of discriminant `16 − 48 = −32`.
Completing the square with `C := A − 2B = x³ − 2x² − x + 1` puts it in the
PRINCIPAL form of that discriminant, `C² + 8B²`, which is the statement below.
`disc C = 49`, so `C` cuts out the cyclic cubic field of conductor `7` — the
other half of `#J(ℚ) = 21 = 3·7`.

The same construction is what produces the genus-`0` quotient: with
`t := A/B` (the degree-`3` map to `X/⟨σ⟩`) the identity reads
`y² = B²·(t² − 4t + 12)`, so `X/⟨σ⟩` is the conic `z² = t² − 4t + 12`, which has
the rational point `(t, z) = (1, 3)` and hence is `≅ P¹`.  The fibre over `t` is
the cubic `X³ − tX² + (t − 3)X + 1`, of discriminant `(t² − 3t + 9)²` — a square,
so it is CYCLIC, which is the same `ℤ/3` again (it is Shanks' simplest-cubic
family under `X ↦ −X`, `t ↦ −t`).  All six rational points of `X` lie in the
single fibre over `t = ∞`. -/
theorem sext18_eq_sq_add_eight_sq {R : Type*} [CommRing R] (x : R) :
    sext 1 (-2) 5 (-10) 10 (-4) x
      = (x ^ 3 - 2 * x ^ 2 - x + 1) ^ 2 + 8 * (x ^ 2 - x) ^ 2 := by
  simp only [sext]
  push_cast
  ring

/-- The homogeneous form of `sext18_eq_sq_add_eight_sq` (PROVEN, `ring`):
`F(a, b) = C̃(a, b)² + 8·B̃(a, b)²` with `C̃ = a³ − 2a²b − ab² + b³` and
`B̃ = ab(a − b)`, the degree-`3` homogenisations of `C` and `B`. -/
theorem hsext18_eq_sq_add_eight_sq (a b : ℤ) :
    hsext 1 (-2) 5 (-10) 10 (-4) a b
      = (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) ^ 2 + 8 * (a * b * (a - b)) ^ 2 := by
  simp only [hsext]
  ring

/-- **THE LEAF, in integral homogeneous form: a coprime integral point of
`X_1(18)` is degenerate.**

`t² = C̃(a, b)² + 8·B̃(a, b)²` with `gcd(a, b) = 1` forces `ab(a − b) = 0`, i.e.
`x = a/b ∈ {0, 1, ∞}`.  Its consumer `affine_rational_points` is PROVEN over it
and discharges the whole `ℚ`-to-`ℤ` passage, so what remains is a statement about
integers only: no rationals, no denominators, no `redPt`, no `Classical.choose`.

**HONEST ACCOUNTING.**  This is *equivalent* to `affine_rational_points`, not
weaker; it is the same arithmetic in the coordinates the literature uses.  What
was bought is the elimination of one layer of Lean bookkeeping, and — see the
audit below — the elimination of the descent route as a candidate, which was
not previously known to be a dead end.

**ROUTE AUDIT: THE `ℤ[√−2]` DESCENT IS REVERSIBLE AND THEREFORE GAINS NOTHING.**
This is a negative result, established 2026-07-27, and it is recorded so nobody
spends the cycle again.  The identity above invites the classical descent, and
the descent goes through completely:

* `C̃` is ODD for every coprime `(a, b)` (check the three residues mod `2`);
* `gcd(C̃, B̃) = 1`, since `C̃ ≡ b³ (mod a)`, `C̃ ≡ a³ (mod b)` and
  `C̃ ≡ −b³ (mod a − b)`, and `a`, `b`, `a − b` are pairwise coprime;
* hence `t` is odd, `m := (t − C̃)/2` and `n := (t + C̃)/2` are coprime integers
  with `mn = 2B̃²`, so one is `±2r²` and the other `±s²`;
* `ℤ[√−2]` is norm-Euclidean with unit group `{±1}`, and `C̃² + 8B̃²` is the norm
  of `C̃ + 2B̃√−2`, whose two conjugate factors are coprime because `t` is odd.
  Normalising the sign of `(a, b)` so that `C̃ > 0` — legitimate, since `C̃` and
  `B̃` are odd-degree forms and `C̃ ≠ 0` because `x³ − 2x² − x + 1` has no
  rational root — the descent yields coprime `p, q` with

      C̃(a, b) = p² − 2q²    and    B̃(a, b) = pq.

**And that system is EQUIVALENT to the original**: given any such `p, q`,
`(p² + 2q²)² = (p² − 2q²)² + 8(pq)²`, so `t = ±(p² + 2q²)` recovers the point.
The descent is a bijection, not a reduction — which is exactly what one should
expect, since the class number of `ℤ[√−2]` is `1` and its units are `±1`, so
there is no Selmer bookkeeping for it to expose.

**The refuting check, so this audit can be overturned cheaply**: it would be
wrong if the relevant order had class number `> 1` or units beyond `±1`.  It does
not — `h(−8) = 1`, and the form `A² − 4AB + 12B²` of discriminant `−32` is the
principal one (the other class of that discriminant is `3A² + 2AB + 3B²`).  A
descent that *does* gain something must therefore come from somewhere else: the
`ℤ[ζ₃]`-action, i.e. a `(1 − ζ₃)`-descent on `J`, not from `√−2`.

A related dead end, checked the same day: `a`, `b`, `a − b` being pairwise
coprime does NOT force each of them into `p` or into `q` wholesale, because
`gcd(p, q) = 1` only splits each of them between the two.  So the tempting
"eight cases" enumeration (`p` a product of a subset of `{a, b, a − b}`) is a
proper SUBSET of the solutions, not a case division.  Each of those eight
equations does have only degenerate solutions for `|a|, |b| ≤ 80` (PARI/GP,
untrusted searcher), but that fact settles nothing.

**What is still needed** is unchanged and is the four-part project in the module
docstring: `Pic⁰` of a genus-`2` curve, Abel–Jacobi, good reduction at `5` with
torsion-free kernel, and `rank J(ℚ) = 0`.  Equivalently a Chabauty–Coleman or
Mordell–Weil-sieve argument.  Nothing shorter is known to the author of this
docstring, and the two shortcuts that look available from the identity — descent
along a factorisation of the sextic, and quotienting to a rank-`0` elliptic
curve — are both closed: the sextic is irreducible, and every quotient by a
subgroup of `⟨σ, ι⟩` has genus `0`.

**NOT ANALOGOUS AT LEVEL 13** (checked 2026-07-27, for `X13.redPt_injective_three`
and any future restatement of it).  For `sext 1 4 6 2 1 2 = x⁶ + 2x⁵ + x⁴ + 2x³ +
6x² + 4x + 1` the polynomial square root is forced to be `x³ + x² + 1`, and the
remainder is `4x² + 4x = 4x(x + 1)`, which is not a constant times a square.  So
level `13` has NO identity of the shape `C² + kB²` with `B` quadratic, and the
`√−2` structure here is specific to level `18`.  Whatever is generic across the
two levels is the `σ`-semi-invariant construction, not this identity. -/
theorem abd_eq_zero_of_sq_eq (a b t : ℤ) (hab : Int.gcd a b = 1)
    (ht : t ^ 2 = (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) ^ 2
              + 8 * (a * b * (a - b)) ^ 2) :
    a * b * (a - b) = 0 := sorry

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
a rational point of order `18`.

**Since 2026-07-27 this is PROVEN** from the integral leaf
`abd_eq_zero_of_sq_eq` below, through the identity `sext18_eq_sq_add_eight_sq`
and `exists_int_coords`.  What that step discharges is the whole passage from
`ℚ` to `ℤ` — denominators, the integrality of `y · den³`, and the reading off of
`y = ±1` at the two surviving abscissae — so no later attack has to redo it. -/
theorem affine_rational_points (x y : ℚ)
    (h : y ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) x) :
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := by
  obtain ⟨t, -, ht⟩ := exists_int_coords 1 (-2) 5 (-10) 10 (-4) x y h
  have hgcd : Int.gcd x.num (x.den : ℤ) = 1 := by
    simpa [Int.gcd, Nat.Coprime] using x.reduced
  have ht' : t ^ 2
      = (x.num ^ 3 - 2 * x.num ^ 2 * (x.den : ℤ) - x.num * (x.den : ℤ) ^ 2
            + (x.den : ℤ) ^ 3) ^ 2
        + 8 * (x.num * (x.den : ℤ) * (x.num - (x.den : ℤ))) ^ 2 := by
    rw [ht, hsext18_eq_sq_add_eight_sq]
  have hden : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = 0 ∨ x = 1 := by
    rcases mul_eq_zero.mp (abd_eq_zero_of_sq_eq x.num (x.den : ℤ) t hgcd ht') with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact Or.inl (Rat.num_eq_zero.mp h3)
      · exact absurd h4 hden
    · refine Or.inr ?_
      have hnd : (x.num : ℚ) = (x.den : ℚ) := by exact_mod_cast sub_eq_zero.mp h2
      have hdQ : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have hd := Rat.num_div_den x
      rw [hnd, div_self hdQ] at hd
      exact hd.symm
  rw [sext18_eq_sq_add_eight_sq] at h
  have hy : (y - 1) * (y + 1) = 0 := by
    rcases hx with rfl | rfl <;> linear_combination h
  rcases hx with rfl | rfl
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inl ⟨rfl, by linear_combination h1⟩
    · exact Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩)
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linear_combination h1⟩))

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

    abd_eq_zero_of_sq_eq (LEAF) → affine_rational_points
                                → redPt_injective_five → exists_jacobianPackage

so a real `Pic⁰` cannot simply be dropped in underneath: it proves
`exists_jacobianPackage` directly, which would close a cycle.  The rewiring is
four edits and no statement changes.  Prove this theorem from the real package;
replace `redPt_injective_five`'s proof by `redPt_injective D` for that package;
prove `affine_rational_points` from `redPt_injective_five` by the backwards
argument recorded in its docstring (`sevenPts_injective` and `card_X18_F5` give
`x ∈ {0, 1}`, then `y² = 1`); and prove `abd_eq_zero_of_sq_eq` from
`affine_rational_points` by `x := a/b`.  Every consumer outside this module is
untouched, which is the property the bundling exists to provide. -/
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

/-- **The `X_1(13)` sextic is a SUM OF TWO SQUARES — a norm form from `ℤ[i]`**
(PROVEN, `ring`):

`x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1 = (x³ + x² − 2x − 1)² + 4(x² + x)²`.

**THIS REFUTES A CLAIM DOCUMENTED ELSEWHERE IN THIS FILE** (2026-07-27).  The
ROUTE AUDIT on `X18.abd_eq_zero_of_sq_eq` closes with a paragraph headed *"NOT
ANALOGOUS AT LEVEL 13"*, asserting that level `13` has **no** identity of the
shape `C² + kB²` with `B` quadratic, on the ground that "the polynomial square
root is forced to be `x³ + x² + 1`, and the remainder is `4x² + 4x`, which is
not a constant times a square".  **That inference is wrong.**  `kB²` has degree
`4`, so it contributes to the `x⁴` coefficient of `C² + kB²`; only the TOP TWO
coefficients of `C` are forced, and its linear coefficient is free.  Taking that
coefficient to be `−2` rather than `0` — `C = x³ + x² − 2x − 1` in place of
`x³ + x² + 1` — gives the identity above, verified here by `ring` and so by the
kernel.  The `√−2` structure at level `18` therefore **does** have a level-`13`
analogue, namely `√−1`; the two levels are parallel after all.

**The refuting check, in one line**: expand `(x³ + x² − 2x − 1)² + 4(x² + x)²`.
That paragraph should be corrected by the owner of `X18.abd_eq_zero_of_sq_eq`;
it is not edited here because it lies in another agent's region.

**What the audit's conclusion DOES survive**, and it is the important half: the
resulting descent is still reversible, so the identity buys no elementary route.
See `abd_eq_zero_of_sq_eq` below, where that is worked out for `ℤ[i]`.

**Where the identity comes from**, by the same `σ`-semi-invariant construction
the level-`18` docstring describes.  The order-`3` automorphism acts on the
`x`-line by `τ(x) = −1/(x + 1)`.  For the weight-`3` action
`(S₃g)(x) = g(τx)·(x + 1)³` the `(−1)`-eigenspace is TWO-dimensional, spanned by

* `A(x) = x³ + 3x² − 1`, since `A(τx)(x + 1)³ = −1 + 3(x + 1) − (x + 1)³ = −A(x)`;
* `B(x) = x² + x`, since `B(τx)(x + 1)³ = (x + 1) − (x + 1)² = −B(x)`.

Every product of two of them is therefore a weight-`6` INVARIANT, and the sextic
is the binary quadratic form

    f = A² − 4AB + 8B²,

of discriminant `16 − 32 = −16`.  Completing the square with
`C := A − 2B = x³ + x² − 2x − 1` puts it in the PRINCIPAL form of that
discriminant, `C² + 4B²`, which is the statement below.

Two corollaries worth recording, because each replaces a separate computation:

* the `σ`-invariance asserted in the reconnaissance on `affine_rational_points`
  is now a CONSEQUENCE, not an independent check:
  `f(τx)(x + 1)⁶ = (−A)² − 4(−A)(−B) + 8(−B)² = f(x)`;
* the genus-`0` quotient is explicit.  With `t := A/B` the identity reads
  `y² = B²·(t² − 4t + 8)`, so `X/⟨σ⟩` is the conic `z² = t² − 4t + 8`, which
  carries the rational point `(t, z) = (2, 2)` and hence is `≅ P¹`.  The fibre
  over `t` is the cubic `X³ + (3 − t)X² − tX − 1`, which is Shanks' SIMPLEST
  CUBIC with parameter `s = t − 3` (`X³ − sX² − (s + 3)X − 1`), of discriminant
  `(s² + 3s + 9)² = (t² − 3t + 9)²` — a square, hence cyclic, which is the same
  `ℤ/3` again.  The expression `t² − 3t + 9` is literally the one that appears
  at level `18`: *that*, and not the quadratic form, is what is generic across
  the two levels. -/
theorem sext13_eq_sq_add_four_sq {R : Type*} [CommRing R] (x : R) :
    sext 1 4 6 2 1 2 x
      = (x ^ 3 + x ^ 2 - 2 * x - 1) ^ 2 + 4 * (x ^ 2 + x) ^ 2 := by
  simp only [sext]
  push_cast
  ring

/-- The homogeneous form of `sext13_eq_sq_add_four_sq` (PROVEN, `ring`):
`F(a, b) = C̃(a, b)² + 4·B̃(a, b)²` with `C̃ = a³ + a²b − 2ab² − b³` and
`B̃ = ab(a + b)`, the degree-`3` homogenisations of `C` and `B`. -/
theorem hsext13_eq_sq_add_four_sq (a b : ℤ) :
    hsext 1 4 6 2 1 2 a b
      = (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) ^ 2 + 4 * (a * b * (a + b)) ^ 2 := by
  simp only [hsext]
  ring

/-- **THE LEAF, in integral homogeneous form: a coprime integral point of
`X_1(13)` is degenerate.**

`t² = C̃(a, b)² + 4·B̃(a, b)²` with `gcd(a, b) = 1` forces `ab(a + b) = 0`, i.e.
`x = a/b ∈ {0, −1, ∞}`.  Its consumer `affine_rational_points` is PROVEN over it
and discharges the whole `ℚ`-to-`ℤ` passage (through the generic bridge
`holds_num_den_of_sq_eq_sext`), so what remains is a statement about INTEGERS
only: no rationals, no denominators, no `redPt`, no `Classical.choose`, no
weighted-projective coordinates.

**HONEST ACCOUNTING.**  This is *equivalent* to `affine_rational_points`, not
weaker; it is the same arithmetic in the coordinates the literature uses.  The
net leaf count is unchanged at one, and **this is not progress on abelian
varieties**.  What was bought is (a) one fewer layer of Lean bookkeeping, shared
generically with level `18`, and (b) the elimination of the `ℤ[i]` descent as a
candidate route — which, unlike at level `18`, was not previously known to be a
dead end, because the identity it rests on was believed not to exist.

**ROUTE AUDIT: THE `ℤ[i]` DESCENT IS REVERSIBLE AND THEREFORE GAINS NOTHING.**
A negative result, established 2026-07-27, recorded so nobody spends the cycle
again.  The identity invites the classical descent, and the descent goes through
completely:

* `C̃` is ODD for every coprime `(a, b)`: mod `2`, `C̃ ≡ a³ + a²b + b³`, whose
  values at the three coprime residues `(1,0), (0,1), (1,1)` are all `1`;
* `gcd(C̃, B̃) = 1`, since `C̃ ≡ −b³ (mod a)`, `C̃ ≡ a³ (mod b)` and
  `C̃ ≡ b³ (mod a + b)`, while `a`, `b`, `a + b` are pairwise coprime;
* hence `t² = C̃² + (2B̃)²` is a PRIMITIVE Pythagorean triple with `t` odd, so
  `m := (t − C̃)/2` and `n := (t + C̃)/2` are coprime integers with `mn = B̃²`.
  Normalising `t > 0` makes both positive, so `m = u²`, `n = v²` with
  `gcd(u, v) = 1`, and

      C̃(a, b) = v² − u²    and    B̃(a, b) = u·v.

**And that system is EQUIVALENT to the original**: given any coprime `u, v`,
`(u² + v²)² = (v² − u²)² + 4(uv)²`, so `t = ±(u² + v²)` recovers the point.  The
descent is a bijection, not a reduction — exactly what to expect, since the
class number of the relevant order is `1` and its units are `±1`, so there is no
Selmer bookkeeping for it to expose.

**The refuting check, so this audit can be overturned cheaply**: it would be
wrong if the order had class number `> 1` or units beyond `±1`.  It does not —
`h(−16) = 1`, and `A² + 4B²` is the principal form of discriminant `−16` (the
only other reduced form of that discriminant, `2A² + 2B²`, is imprimitive).  A
descent that *does* gain something must therefore come from elsewhere: the
`ℤ[ζ₃]`-action, i.e. a `(1 − ζ₃)`-descent on `J`, not from `√−1`.

Two further dead ends checked the same day, both mirroring level `18`:

* here `C̃` factors further, as `(v − u)(v + u)` — level `18`'s `C̃ = p² − 2q²`
  does not — but this gains nothing, because `a`, `b`, `a + b` being pairwise
  coprime does NOT force each of them wholesale into `u` or into `v`:
  `gcd(u, v) = 1` only splits each of them between the two.  So the tempting
  eight-case enumeration is a proper SUBSET of the solutions, not a case
  division;
* the sextic is irreducible with Galois group `F₁₈(6) = 3 ≀ 2`, so there is no
  factorisation to descend along and no elementary two-cover route; and
  `J_1(13)` is `ℚ`-simple of `GL₂`-type, so no quotient to a rank-`0` elliptic
  curve exists.

**NUMERICAL CORROBORATION** (exact integer arithmetic, untrusted searcher, so a
claim to be re-derived and not a proof): over all coprime `(a, b)` with
`|a| ≤ 400` and `1 ≤ b ≤ 400`, the only solutions of `t² = C̃² + 4B̃²` have
`B̃ = ab(a + b) = 0`.  That is a considerably wider search than the
`|a| ≤ 60`, `b ≤ 30` one recorded on `affine_rational_points`.  The same run
confirms the two structural claims above: `C̃` is odd, and `gcd(C̃, B̃) = 1`,
on every coprime pair in the range.

**What is still needed** is unchanged and is the four-part project recorded on
`affine_rational_points` and in the module docstring: `Pic⁰` of a genus-`2`
curve, Abel–Jacobi, good reduction at `3` with torsion-free kernel, and
`rank J(ℚ) = 0` — with `#J(𝔽₃) = 19 = #J(ℚ)` as the sharp target.  Equivalently
a Chabauty–Coleman or Mordell–Weil-sieve argument.  Nothing shorter is known to
the author of this docstring. -/
theorem abd_eq_zero_of_sq_eq (a b t : ℤ) (hab : Int.gcd a b = 1)
    (ht : t ^ 2 = (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) ^ 2
              + 4 * (a * b * (a + b)) ^ 2) :
    a * b * (a + b) = 0 := sorry

/-- **The affine rational points of `X_1(13)` are its four finite cusps.**

**PROVEN since 2026-07-27** from the integral leaf `abd_eq_zero_of_sq_eq`
above, through the identity `hsext13_eq_sq_add_four_sq` and the generic bridge
`holds_num_den_of_sq_eq_sext`.  What that step discharges is the whole passage
from `ℚ` to `ℤ` — denominators, the integrality of `y · den³`, coprimality of
`(num, den)`, and the reading off of `y = ±1` at the two surviving abscissae —
so no later attack has to redo it.  This mirrors what was done at level `18`,
except that the bridge is now stated once, generically, for an arbitrary sextic
rather than open-coded per level.

This *replaced* the former leaf `redPt_injective_three`, which is now PROVEN
from it below, and which had itself replaced `exists_jacobianPackage`.  Nothing
has been weakened at either step, because each is an EQUIVALENCE:

* `exists_jacobianPackage ↔ redPt_injective_three` by `redPt_injective` and
  `nonempty_jacobianPackage_of_redPt_injective`, both proven above and both
  stated for an ARBITRARY sextic and prime;
* `redPt_injective_three ↔ affine_rational_points` by `red_sixPts` plus
  `sixPtsData_injective` forwards, and by `sevenPts_injective` plus
  `card_X13_F3` backwards (the argument of `no_noncuspidal_point`, plus
  `y² = 1 ⟹ y = ±1` at `x ∈ {0, −1}`); the backwards direction is written out
  here rather than as a declaration, since nothing in the root cone consumes it.

What each step removed is a layer of Lean-specific interface: first the
obligation to exhibit a *structure*, then the obligation to reason about a
`Classical.choose`n reduction map, and finally the passage from `ℚ` to `ℤ`.
What is left, in `abd_eq_zero_of_sq_eq`, is one sextic Diophantine equation over
the integers, mentioning neither `redPt` nor weighted-projective coordinates nor
reduction nor denominators at all.  **No step of this is progress on abelian
varieties**, and the leaf count is unchanged at one throughout.

This is exactly the shape of `X18.affine_rational_points`, and deliberately so:
the machinery that computes `redPt` at a concrete point (`ptData`,
`redPt_inl`, `ptData_redPt_inl`) is stated for an arbitrary sextic and prime,
so it served both levels unchanged, and one future development of genus-`2`
Jacobians discharges both leaves at once.  The four parts are those recorded in
this module's docstring:

1. `Pic⁰` of a genus-`2` hyperelliptic curve, with the Mumford representation
   and Cantor's group law — the group `J = J(ℚ)` and its reduction `J(𝔽₃)`;
2. Abel–Jacobi from a rational base point, injective for genus `≥ 1`;
3. good reduction at `3` (the sextic's discriminant is `−2¹²·13²`, and the
   conductor of `J_1(13)` is `169`), the reduction homomorphism, its
   compatibility with `redPt`, and torsion-freeness of its kernel — the kernel
   is the formal group over `ℤ₃`, torsion-free since `3 > e + 1 = 2`;
4. `rank J(ℚ) = 0`.  Externally (untrusted searchers): `J_1(13)`
   is `ℚ`-simple of dimension `2` with `J(ℚ)_tors ≅ ℤ/19`, and a `2`-descent
   gives `rank J(ℚ) = 0`, so `J(ℚ) ≅ ℤ/19`; equivalently `LRatio(J, 1) =
   1/361 ≠ 0`.  Only FINITENESS is used.

Given 1–4 the route is `redPt_injective` applied to the resulting package, then
`redPt_injective_three`, then the backwards direction above; every step of that
is already written and proven here.

**NUMERICAL CORROBORATION (PARI/GP, 2026-07-26 and re-run 2026-07-27; untrusted
searcher, verified against the Lean-side `decide` where it overlaps).**  For
`f = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`:

* `factor(poldisc(f)) = −2¹² · 13²`, so `3 ∤ disc` — `3` really is a prime of
  good reduction, confirming step 3's hypothesis;
* `hyperellcharpoly(Mod(1,3)*f) = T⁴ + 2T³ + T² + 6T + 9`, whose `T³`
  coefficient gives `#X(𝔽₃) = 3 + 1 + 2 = 6` — an independent check of
  `card_X13_F3`, which the kernel proves by `decide`;
* the same polynomial evaluated at `1` gives `#J(𝔽₃) = 1 + 2 + 1 + 6 + 9 = 19`.

That last number is the reason this leaf is true and worth stating in this
form: `J(ℚ) ≅ ℤ/19` injects into `J(𝔽₃)`, which also has order exactly `19`,
so reduction on the Jacobian is an *isomorphism* — in particular injective —
and `redPt` injectivity follows through Abel–Jacobi.  A future prover can use
`19` as the sharp target rather than rediscovering it.  (At `p = 5` the same
computation gives `#J(𝔽₅) = 19` as well, so `5` would serve equally; at `p = 7`
it gives `57 = 3 · 19`.)

**RECONNAISSANCE FOR WHOEVER TAKES THIS ON** (PARI/GP, untrusted searcher, so
each item is a claim to be re-derived and not a proof):

* the sextic is IRREDUCIBLE over `ℚ`, with Galois group `F₁₈(6) = 3 ≀ 2` of
  order `18`.  So there is no factorisation `f = g·h` to descend along, and no
  elementary two-cover argument of the kind that settles many genus-`2` curves;
* the curve carries an ORDER-`3` AUTOMORPHISM `σ(x, y) = (−1/(x + 1),
  y/(x + 1)³)`, the identity `f(−1/(x + 1))·(x + 1)⁶ = f(x)` being exact
  (verified as a polynomial identity, and `σ³ = id` as a Möbius map).  `σ`
  cycles `0 ↦ −1 ↦ ∞ ↦ 0`, so the six rational points form a SINGLE orbit
  under `⟨σ, ι⟩ ≅ ℤ/6` with `ι` the hyperelliptic involution.  This is the
  diamond action `⟨5⟩` on `X_1(13)`, the geometric source of the `ℤ[ζ₃]`-action
  on `J`; `J_1(13)` is `ℚ`-simple of `GL₂`-type with non-rational coefficient
  field, hence NOT isogenous to a product of elliptic curves over `ℚ`, so a
  route through elliptic curves of rank `0` is closed;
* a search over `x = a/b` with `|a| ≤ 60`, `1 ≤ b ≤ 30`, `gcd(a, b) = 1` finds
  exactly `x = 0` and `x = −1`, consistent with the statement.

This is Mazur–Tate, *Points of order 13 on elliptic curves*, Invent. Math. 22
(1973); subsumed in Mazur, IHÉS 47 (1977), Thm 7.

**Not vacuous, and not overstated.**  It asserts that a genus-`2` curve has
exactly four affine rational points; it is TRUE, `X_1(13)(ℚ)` consisting of its
six cusps, which is the classical statement that no elliptic curve over `ℚ` has
a rational point of order `13`. -/
theorem affine_rational_points (x y : ℚ)
    (h : y ^ 2 = sext 1 4 6 2 1 2 x) :
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = -1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  have hzero : x.num * (x.den : ℤ) * (x.num + (x.den : ℤ)) = 0 := by
    refine holds_num_den_of_sq_eq_sext 1 4 6 2 1 2
      (fun a b => a * b * (a + b) = 0) (fun a b t hab ht => ?_) x y h
    exact abd_eq_zero_of_sq_eq a b t hab (by rw [hsext13_eq_sq_add_four_sq] at ht; exact ht)
  have hden : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = 0 ∨ x = -1 := by
    rcases mul_eq_zero.mp hzero with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact Or.inl (Rat.num_eq_zero.mp h3)
      · exact absurd h4 hden
    · refine Or.inr ?_
      have h' := eq_intCast_of_num_eq_mul_den x (-1) (by linear_combination h2)
      rw [h', Int.cast_neg, Int.cast_one]
  rw [sext13_eq_sq_add_four_sq] at h
  have hy : (y - 1) * (y + 1) = 0 := by
    rcases hx with rfl | rfl <;> linear_combination h
  rcases hx with rfl | rfl
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inl ⟨rfl, by linear_combination h1⟩
    · exact Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩)
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linear_combination h1⟩))

/-- The six cusps of `X_1(13)`: `(0, ±1)`, `(−1, ±1)`, and the two points at
infinity.  Under the order-`3` automorphism `σ(x, y) = (−1/(x + 1), y/(x + 1)³)`
recorded on `affine_rational_points` they form a single `⟨σ, ι⟩`-orbit, `σ`
cycling `0 ↦ −1 ↦ ∞ ↦ 0`. -/
def sixPts : Fin 6 → Pt 1 4 6 2 1 2 ℚ :=
  ![Sum.inl ⟨(0, 1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(0, -1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(-1, 1), by rw [sext13]; norm_num⟩,
    Sum.inl ⟨(-1, -1), by rw [sext13]; norm_num⟩,
    Sum.inr true,
    Sum.inr false]

/-- The reductions of the six cusps mod `3`, as raw data.  All four finite cusps
have denominator `1`, so they reduce affinely, with `−1 = 2` in `𝔽₃`; the two
infinite points reduce to themselves. -/
def sixPtsData : Fin 6 → ((ZMod 3) × (ZMod 3)) ⊕ Bool :=
  ![Sum.inl (0, 1), Sum.inl (0, 2), Sum.inl (2, 1), Sum.inl (2, 2),
    Sum.inr true, Sum.inr false]

/-- **The six reduced points are pairwise distinct** (PROVEN BY `decide`).  This
is the second machine-checked arithmetic input of the argument, after
`card_X13_F3`: together they say the six cusps fill `X(𝔽₃)` exactly. -/
lemma sixPtsData_injective : Function.Injective sixPtsData := by decide

/-- **The six cusps reduce as stated** (PROVEN, by computation).

Each finite cusp `(x, y)` has `x.den = 1`, so its integral weighted-projective
coordinates are `[x.num : y : 1]` and `3 ∤ 1`; `ptData_redPt_inl` then computes
the reduction as `(x.num/1, y/1³)` in `𝔽₃`.  The infinite points are handled by
`redPt`'s definition, which is `Sum.inr` on that summand. -/
lemma red_sixPts (i : Fin 6) :
    ptData 1 4 6 2 1 2 (redPt 1 4 6 2 1 2 (p := 3) (sixPts i)) = sixPtsData i := by
  fin_cases i
  · show ptData 1 4 6 2 1 2 (redPt 1 4 6 2 1 2 (p := 3)
      (Sum.inl ⟨((0 : ℚ), (1 : ℚ)), by rw [sext13]; norm_num⟩)) = Sum.inl (0, 1)
    rw [ptData_redPt_inl 1 4 6 2 1 2 (p := 3) 0 1 _ 0 1 1
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_zero, Int.cast_one, one_pow, div_one]
  · show ptData 1 4 6 2 1 2 (redPt 1 4 6 2 1 2 (p := 3)
      (Sum.inl ⟨((0 : ℚ), (-1 : ℚ)), by rw [sext13]; norm_num⟩)) = Sum.inl (0, 2)
    rw [ptData_redPt_inl 1 4 6 2 1 2 (p := 3) 0 (-1) _ 0 1 (-1)
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, one_pow, div_one]
    decide
  · show ptData 1 4 6 2 1 2 (redPt 1 4 6 2 1 2 (p := 3)
      (Sum.inl ⟨((-1 : ℚ), (1 : ℚ)), by rw [sext13]; norm_num⟩)) = Sum.inl (2, 1)
    rw [ptData_redPt_inl 1 4 6 2 1 2 (p := 3) (-1) 1 _ (-1) 1 1
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_one, Int.cast_neg, one_pow, div_one]
    decide
  · show ptData 1 4 6 2 1 2 (redPt 1 4 6 2 1 2 (p := 3)
      (Sum.inl ⟨((-1 : ℚ), (-1 : ℚ)), by rw [sext13]; norm_num⟩)) = Sum.inl (2, 2)
    rw [ptData_redPt_inl 1 4 6 2 1 2 (p := 3) (-1) (-1) _ (-1) 1 (-1)
      (by simp) (by simp) (by norm_num)
      (by norm_num [hsext]) (by decide)]
    simp only [Int.cast_one, Int.cast_neg, one_pow, div_one]
    decide
  · rfl
  · rfl

/-- **Every rational point is one of the six cusps** (PROVEN from the leaf).
The affine case is `affine_rational_points`; the two infinite points are the
`Bool` summand of `Pt`, which is exhaustive by construction. -/
lemma exists_eq_sixPts (P : Pt 1 4 6 2 1 2 ℚ) : ∃ i, P = sixPts i := by
  rcases P with ⟨⟨x, y⟩, h⟩ | b
  · rcases affine_rational_points x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · cases b
    · exact ⟨5, rfl⟩
    · exact ⟨4, rfl⟩

/-- **Reduction at `3` is injective on `X_1(13)(ℚ)`** (PROVEN from
`affine_rational_points`).

Formerly the leaf of this namespace.  Given the determination of `X(ℚ)` the
proof is a finite computation and nothing else: both points are cusps
(`exists_eq_sixPts`), their reductions are computed by `red_sixPts`, and the six
values are distinct by `sixPtsData_injective`.  No Jacobian, no formal group and
no Mordell–Weil enters here — all of that sits in the leaf above, which is where
the arithmetic is. -/
theorem redPt_injective_three :
    Function.Injective (redPt 1 4 6 2 1 2 (p := 3)) := by
  intro P Q hPQ
  obtain ⟨i, rfl⟩ := exists_eq_sixPts P
  obtain ⟨j, rfl⟩ := exists_eq_sixPts Q
  have hdata : sixPtsData i = sixPtsData j := by
    rw [← red_sixPts i, ← red_sixPts j, hPQ]
  rw [sixPtsData_injective hdata]

/-- **The Jacobian package of `X_1(13)` exists** (PROVEN from
`redPt_injective_three`).

Formerly the leaf of this namespace.  It is retained — rather than bypassed in
`no_noncuspidal_point` — because it is the intended plug-in point for the
honest `Pic⁰(X/ℚ)`.  Read the audit on
`nonempty_jacobianPackage_of_redPt_injective` before recording this as progress
on abelian varieties: it is not.

**How to plug in a real Jacobian, since the chain now runs the other way.**  The
proofs currently compose as

    affine_rational_points (LEAF) → redPt_injective_three → exists_jacobianPackage

so a real `Pic⁰` cannot simply be dropped in underneath: it proves
`exists_jacobianPackage` directly, which would close a cycle.  The rewiring is
three edits and no statement changes.  Prove this theorem from the real package;
replace `redPt_injective_three`'s proof by `redPt_injective D` for that package;
and prove `affine_rational_points` from `redPt_injective_three` by the backwards
argument recorded in its docstring (`sevenPts_injective` and `card_X13_F3` give
`x ∈ {0, −1}`, then `y² = 1`).  Every consumer outside this module is untouched,
which is the property the bundling exists to provide. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 4 6 2 1 2 3) :=
  nonempty_jacobianPackage_of_redPt_injective redPt_injective_three

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
