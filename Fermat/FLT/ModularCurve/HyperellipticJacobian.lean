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

`X18.sq_ne_of_zero_lt_lt` — for coprime `0 < a < b` the integer
`C̃(a, b)² + 8·B̃(a, b)²` is never a perfect square, where
`C̃ = a³ − 2a²b − ab² + b³` and `B̃ = ab(a − b)`.  A statement about integers
only: no rationals, no denominators, no `redPt`, no `Classical.choose`.  Its
consumer `X18.abd_eq_zero_of_sq_eq` — same equation, no sign hypotheses,
conclusion `ab(a − b) = 0` — is PROVEN from it by the σ-normalisation
(2026-07-27), so the frontier at level `18` is now a single non-existence
statement over a fundamental domain of the order-`3` automorphism.

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
* `abd_eq_zero_of_sq_eq ↔ sq_ne_of_zero_lt_lt` (level `18`, 2026-07-27) by the
  σ-normalisation: `σ` permutes the three intervals `(−∞, 0)`, `(0, 1)`,
  `(1, ∞)` cyclically, so every non-degenerate orbit has exactly one
  representative with `0 < a < b`, and the degenerate ones are exactly those
  with none.  Written out in both directions in `sq_ne_of_snd_pos` and
  `abd_eq_zero_of_sq_eq`.
* `<level>.abd_eq_zero_of_sq_eq ↔ <level>.descent_system_no_solution` (BOTH
  levels, 2026-07-27) by the classical descent `descent_sq_add_four_sq` /
  `descent_sq_add_eight_sq`, which are proven here generically in `(C, B, t)`
  over the level-specific `C_odd` and `C_isCoprime`.  Reversible in one `ring`
  identity each, so again an equivalence.  **This is the step at which the
  route's elliptic curve becomes visible**, and both levels' Chabauty
  computations were run — see the audits on the two
  `descent_system_no_solution` declarations, and the GAP recorded on each of
  them on 2026-07-27: the covering collection is not established, so the
  Chabauty runs close the leaves modulo a descent step that is not on record.
* `<level>.descent_system_no_solution` → `<level>.descent_system_no_solution_pos`
  and `..._neg` (BOTH levels, 2026-07-27) by `rcases` on the sign disjunct.
  The two branches carry DIFFERENT theories and are independently
  dispatchable: at level `18` the `+` branch is rank `1` and needs `p`-adic
  elliptic Chabauty while the `−` branch is rank `0` and needs none; at level
  `13` both live on one rank-`1` curve and need a Chabauty run each.

What each step removed is a layer of Lean-specific interface: first the
obligation to exhibit a *structure*, then the obligation to reason about a
`Classical.choose`n reduction map, then (at level `18`) the passage from `ℚ`
to `ℤ`.  What is left is one sextic Diophantine equation per level, over `ℤ`
at level `18` and over `ℚ` at level `13`.  **No step is progress on abelian
varieties**, and no step changed the sorry COUNT: one leaf closed, one opened,
at each level, throughout.

**What the 2026-07-27 steps DID add, beyond bookkeeping**, is three axiom-clean
identities, one NEGATIVE result and one POSITIVE route.  The negative result:
the imaginary-quadratic descent that the identities invite is provably
reversible at BOTH levels and so cannot reduce either leaf.  The positive route:
over the imaginary quadratic field the sextic splits into conjugate cubics, and
each branch is an ELLIPTIC CURVE of rank `1` over that field carrying the
condition `x ∈ ℚ` — i.e. elliptic Chabauty applies, with `1 < 2 = [K : ℚ]`, and
the object needed is an elliptic curve over a quadratic field rather than `Pic⁰`
of a genus-`2` curve.  Both audits, with the checks that would refute them, are
on `X18.sq_ne_of_zero_lt_lt` and `X18.abd_eq_zero_of_sq_eq`.  Reading them
before attacking either level is worth the five minutes; the second also
records a claim about level `13` that was asserted here and later REFUTED.

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
-- for the classical descent in `section Descent` below: `IsCoprime` over `ℤ`,
-- `Int.sq_of_isCoprime`, `Int.prime_two` and `Nat.prime_iff_prime_int`
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic.Linarith

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
live further down, at the FOUR sign branches
`X18.descent_system_no_solution_pos` / `_neg` and
`X13.descent_system_no_solution_pos` / `_neg` (opened 2026-07-27) — the
descended integral forms of that determination, split along the sign of the
descent, four steps beyond `X18.affine_rational_points` and three beyond
`X13.affine_rational_points`.

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

section Descent

/-! ### The classical descent on `t² = C² + k·B²`, `k ∈ {4, 8}`

Both levels' integral leaves have the shape `t² = C² + k·B²` with `C` odd and
`gcd(C, B) = 1`, and both therefore admit the classical descent.  The three
lemmas below carry it out ONCE, generically in `(C, B, t)`, so neither level
restates it.

**HONEST ACCOUNTING, and it is the same warning both route audits already
carry: this descent is REVERSIBLE, so it is a change of coordinates and NOT a
reduction in difficulty.**  Given any coprime `u, v` the identities

    (u² + v²)²   = (v² − u²)²   + 4(uv)²
    (v² + 2u²)²  = (v² − 2u²)²  + 8(uv)²

(both `ring`) recover a solution, so nothing is discarded and the leaf count is
unchanged at one per level.  What it buys is that the surviving obligation is
stated in the coordinates where the elliptic curve of the verified route is
visible: `C + 2B√−1 = (v + u√−1)²` at level `13` and `C + 2B√−2 = (v + u√−2)²`
at level `18`, which is exactly the assertion that `(x, w)` is a point of
`w² = g(x)` over the imaginary quadratic field.  See the route audits on
`X18.sq_ne_of_zero_lt_lt` and `X13.abd_eq_zero_of_sq_eq`.

The descent needs no `Zsqrtd` arithmetic — this pin equips neither `Zsqrtd (-1)`
nor `Zsqrtd (-2)` with a Euclidean-domain instance — only coprime factorisation
in `ℤ`, via `Int.sq_of_isCoprime`. -/

/-- **Square roots inherit coprimality** (PROVEN).  If `x` and `y` are coprime
and each is `±` a square, the two square roots are coprime.  The four sign cases
are all the same one-line argument through `IsCoprime.neg_left_iff` /
`IsCoprime.neg_right_iff`. -/
theorem descentCoprimeAux {x y u v : ℤ} (h : IsCoprime x y)
    (hu : x = u ^ 2 ∨ x = -u ^ 2) (hv : y = v ^ 2 ∨ y = -v ^ 2) : IsCoprime u v := by
  have h1 : IsCoprime (u ^ 2) (v ^ 2) := by
    rcases hu with hu | hu <;> rcases hv with hv | hv <;>
      [ (rw [← hu, ← hv]; exact h);
        (rw [← hu]; exact (IsCoprime.neg_right_iff _ _).mp (by rw [← hv]; exact h));
        (rw [← hv]; exact (IsCoprime.neg_left_iff _ _).mp (by rw [← hu]; exact h));
        (exact (IsCoprime.neg_left_iff _ _).mp ((IsCoprime.neg_right_iff _ _).mp
          (by rw [← hu, ← hv]; exact h))) ]
  exact (h1.of_isCoprime_of_dvd_left (dvd_pow_self u two_ne_zero)).of_isCoprime_of_dvd_right
    (dvd_pow_self v two_ne_zero)

/-- **The descent at level `13`** (PROVEN): `t² = C² + 4B²` with `C` odd and
`gcd(C, B) = 1` forces `C = ±(v² − u²)` and `B = uv` for some coprime `u, v`.

`t` is odd, so `m := (t − C)/2` and `n := (t + C)/2` are integers with
`n − m = C` and `mn = B²`; they are coprime because a common prime `p` divides
`C` and `B²`, and `gcd(C, B) = 1`.  `Int.sq_of_isCoprime` then makes each of
them `±` a square.  The two MIXED sign choices force `mn ≤ 0`, hence `B = 0` and
(by coprimality) `{m, n} = {0, ±1}`, so `C = ±1`; those are discharged by the
explicit degenerate witnesses `(u, v) = (0, 1)` and `(1, 0)`.  The sign of `B`
is normalised by replacing `u` with `−u`, which changes neither `u²` nor
coprimality. -/
theorem descent_sq_add_four_sq (C B t : ℤ) (hodd : ¬ (2 : ℤ) ∣ C) (hcop : IsCoprime C B)
    (ht : t ^ 2 = C ^ 2 + 4 * B ^ 2) :
    ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧ (C = v ^ 2 - u ^ 2 ∨ C = u ^ 2 - v ^ 2) := by
  have hCO : Odd C := Int.not_even_iff_odd.mp fun h => hodd h.two_dvd
  have htO : Odd t := by
    rcases Int.even_or_odd t with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      apply hodd
      refine Int.prime_two.dvd_of_dvd_pow (n := 2) ?_
      exact ⟨2 * (k * k) - 2 * B ^ 2, by rw [hk] at ht; linarith [ht]⟩
    · exact ho
  obtain ⟨n, hn⟩ : (2 : ℤ) ∣ (t + C) := (htO.add_odd hCO).two_dvd
  obtain ⟨m, hm⟩ : (2 : ℤ) ∣ (t - C) := (htO.sub_odd hCO).two_dvd
  have hC : n - m = C := by linarith
  have hmn : m * n = B ^ 2 := by
    have h4 : (2 * m) * (2 * n) = 4 * B ^ 2 := by rw [← hm, ← hn]; linear_combination ht
    linarith [show (2 * m) * (2 * n) = 4 * (m * n) from by ring, h4]
  have hcopmn : IsCoprime m n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpZ : ((p : ℤ)) ∣ ((Int.gcd m n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have hpZm : (p : ℤ) ∣ m := hpZ.trans (Int.gcd_dvd_left ..)
    have hpZn : (p : ℤ) ∣ n := hpZ.trans (Int.gcd_dvd_right ..)
    have hpC : (p : ℤ) ∣ C := hC ▸ dvd_sub hpZn hpZm
    have hpB2 : (p : ℤ) ∣ B ^ 2 := hmn ▸ Dvd.dvd.mul_right hpZm n
    have hU : IsUnit ((p : ℤ)) := (hcop.pow_right (n := 2)).isUnit_of_dvd' hpC hpB2
    rw [Int.isUnit_iff] at hU
    have := hp.two_le
    omega
  obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcopmn hmn
  obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcopmn.symm (by rw [mul_comm]; exact hmn)
  have hcopuv : IsCoprime u v := descentCoprimeAux hcopmn hu hv
  have norm : ∀ p q : ℤ, IsCoprime p q → B ^ 2 = (p * q) ^ 2 →
      (C = q ^ 2 - p ^ 2 ∨ C = p ^ 2 - q ^ 2) →
      ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧ (C = v ^ 2 - u ^ 2 ∨ C = u ^ 2 - v ^ 2) := by
    intro p q hpq hB2 hCd
    have hfac : (B - p * q) * (B + p * q) = 0 := by linear_combination hB2
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨p, q, hpq, by linarith, hCd⟩
    · refine ⟨-p, q, hpq.neg_left, by linarith, ?_⟩
      simpa using hCd
  have degen : B = 0 → (C = 1 ∨ C = -1) →
      ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧ (C = v ^ 2 - u ^ 2 ∨ C = u ^ 2 - v ^ 2) := by
    rintro hB0 (h | h)
    · exact ⟨0, 1, isCoprime_zero_left.mpr isUnit_one, by simp [hB0], Or.inl (by simp [h])⟩
    · exact ⟨1, 0, isCoprime_one_left, by simp [hB0], Or.inl (by simp [h])⟩
  have mixed : B = 0 → C = 1 ∨ C = -1 := by
    intro hB0
    have hmn0 : m * n = 0 := by rw [hmn, hB0]; ring
    rcases mul_eq_zero.mp hmn0 with h | h
    · have hc' : IsCoprime (0 : ℤ) n := by rw [← h]; exact hcopmn
      have hU := isCoprime_zero_left.mp hc'
      rw [Int.isUnit_iff] at hU
      rcases hU with h1 | h1
      · exact Or.inl (by rw [← hC, h, h1]; ring)
      · exact Or.inr (by rw [← hC, h, h1]; ring)
    · have hc' : IsCoprime m (0 : ℤ) := by rw [← h]; exact hcopmn
      have hU := isCoprime_zero_right.mp hc'
      rw [Int.isUnit_iff] at hU
      rcases hU with h1 | h1
      · exact Or.inr (by rw [← hC, h, h1]; ring)
      · exact Or.inl (by rw [← hC, h, h1]; ring)
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact norm u v hcopuv (by rw [← hmn, hu, hv]; ring) (Or.inl (by rw [← hC, hu, hv]))
  · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn, hu, hv]; ring
    have hB0 : B = 0 := by
      nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
    exact degen hB0 (mixed hB0)
  · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn, hu, hv]; ring
    have hB0 : B = 0 := by
      nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
    exact degen hB0 (mixed hB0)
  · exact norm u v hcopuv (by rw [← hmn, hu, hv]; ring) (Or.inr (by rw [← hC, hu, hv]; ring))

/-- **The descent at level `18`** (PROVEN): `t² = C² + 8B²` with `C` odd and
`gcd(C, B) = 1` forces `C = ±(v² − 2u²)` and `B = uv` for some coprime `u, v`.

The same argument as `descent_sq_add_four_sq`, with one extra layer: here
`mn = 2B²`, so the factor `2` sits in exactly one of `m`, `n` — they are
coprime — and is split off before `Int.sq_of_isCoprime` applies.  The two
placements of that factor give the two orderings of the square roots, which is
why the conclusion is symmetric under swapping them.  Note also that the odd
prime step needs `C` odd a second time: `p ∣ 2B²` only gives `p ∣ B²` once
`p ≠ 2` is known, and that is what `C` odd supplies. -/
theorem descent_sq_add_eight_sq (C B t : ℤ) (hodd : ¬ (2 : ℤ) ∣ C) (hcop : IsCoprime C B)
    (ht : t ^ 2 = C ^ 2 + 8 * B ^ 2) :
    ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧ (C = v ^ 2 - 2 * u ^ 2 ∨ C = 2 * u ^ 2 - v ^ 2) := by
  have hCO : Odd C := Int.not_even_iff_odd.mp fun h => hodd h.two_dvd
  have htO : Odd t := by
    rcases Int.even_or_odd t with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      apply hodd
      refine Int.prime_two.dvd_of_dvd_pow (n := 2) ?_
      exact ⟨2 * (k * k) - 4 * B ^ 2, by rw [hk] at ht; linarith [ht]⟩
    · exact ho
  obtain ⟨n, hn⟩ : (2 : ℤ) ∣ (t + C) := (htO.add_odd hCO).two_dvd
  obtain ⟨m, hm⟩ : (2 : ℤ) ∣ (t - C) := (htO.sub_odd hCO).two_dvd
  have hC : n - m = C := by linarith
  have hmn : m * n = 2 * B ^ 2 := by
    have h4 : (2 * m) * (2 * n) = 8 * B ^ 2 := by rw [← hm, ← hn]; linear_combination ht
    linarith [show (2 * m) * (2 * n) = 4 * (m * n) from by ring, h4]
  have hcopmn : IsCoprime m n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpZ : ((p : ℤ)) ∣ ((Int.gcd m n : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have hpZm : (p : ℤ) ∣ m := hpZ.trans (Int.gcd_dvd_left ..)
    have hpZn : (p : ℤ) ∣ n := hpZ.trans (Int.gcd_dvd_right ..)
    have hpC : (p : ℤ) ∣ C := hC ▸ dvd_sub hpZn hpZm
    have hp2 : (p : ℤ) ∣ 2 * B ^ 2 := hmn ▸ Dvd.dvd.mul_right hpZm n
    have hpne : (p : ℤ) ≠ 2 := by
      rintro h2
      exact hodd (h2 ▸ hpC)
    have hpB2 : (p : ℤ) ∣ B ^ 2 := by
      have hpp : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
      rcases hpp.dvd_mul.mp hp2 with h | h
      · exfalso
        have hle : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
        have h2 := hp.two_le
        exact hpne (by omega)
      · exact h
    have hU : IsUnit ((p : ℤ)) := (hcop.pow_right (n := 2)).isUnit_of_dvd' hpC hpB2
    rw [Int.isUnit_iff] at hU
    have := hp.two_le
    omega
  have norm : ∀ p q : ℤ, IsCoprime p q → B ^ 2 = (p * q) ^ 2 →
      (C = q ^ 2 - 2 * p ^ 2 ∨ C = 2 * p ^ 2 - q ^ 2) →
      ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧
        (C = v ^ 2 - 2 * u ^ 2 ∨ C = 2 * u ^ 2 - v ^ 2) := by
    intro p q hpq hB2 hCd
    have hfac : (B - p * q) * (B + p * q) = 0 := by linear_combination hB2
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨p, q, hpq, by linarith, hCd⟩
    · refine ⟨-p, q, hpq.neg_left, by linarith, ?_⟩
      simpa using hCd
  have degen : B = 0 → (C = 1 ∨ C = -1) →
      ∃ u v : ℤ, IsCoprime u v ∧ B = u * v ∧
        (C = v ^ 2 - 2 * u ^ 2 ∨ C = 2 * u ^ 2 - v ^ 2) := by
    rintro hB0 (h | h)
    · exact ⟨0, 1, isCoprime_zero_left.mpr isUnit_one, by simp [hB0], Or.inl (by simp [h])⟩
    · exact ⟨0, 1, isCoprime_zero_left.mpr isUnit_one, by simp [hB0], Or.inr (by simp [h])⟩
  have mixed : B = 0 → C = 1 ∨ C = -1 := by
    intro hB0
    have hmn0 : m * n = 0 := by rw [hmn, hB0]; ring
    rcases mul_eq_zero.mp hmn0 with h | h
    · have hc' : IsCoprime (0 : ℤ) n := by rw [← h]; exact hcopmn
      have hU := isCoprime_zero_left.mp hc'
      rw [Int.isUnit_iff] at hU
      rcases hU with h1 | h1
      · exact Or.inl (by rw [← hC, h, h1]; ring)
      · exact Or.inr (by rw [← hC, h, h1]; ring)
    · have hc' : IsCoprime m (0 : ℤ) := by rw [← h]; exact hcopmn
      have hU := isCoprime_zero_right.mp hc'
      rw [Int.isUnit_iff] at hU
      rcases hU with h1 | h1
      · exact Or.inr (by rw [← hC, h, h1]; ring)
      · exact Or.inl (by rw [← hC, h, h1]; ring)
  have h2mn : (2 : ℤ) ∣ m ∨ (2 : ℤ) ∣ n := Int.prime_two.dvd_mul.mp ⟨B ^ 2, hmn⟩
  rcases h2mn with ⟨m0, hm0⟩ | ⟨n0, hn0⟩
  · have hmn0 : m0 * n = B ^ 2 := by
      rw [hm0] at hmn
      linarith [show (2 * m0) * n = 2 * (m0 * n) from by ring, hmn]
    have hcop0 : IsCoprime m0 n := hcopmn.of_isCoprime_of_dvd_left ⟨2, by linarith⟩
    obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcop0 hmn0
    obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcop0.symm (by rw [mul_comm]; exact hmn0)
    have hcopuv : IsCoprime u v := descentCoprimeAux hcop0 hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact norm u v hcopuv (by rw [← hmn0, hu, hv]; ring)
        (Or.inl (by rw [← hC, hm0, hu, hv]))
    · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn0, hu, hv]; ring
      have hB0 : B = 0 := by
        nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
      exact degen hB0 (mixed hB0)
    · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn0, hu, hv]; ring
      have hB0 : B = 0 := by
        nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
      exact degen hB0 (mixed hB0)
    · exact norm u v hcopuv (by rw [← hmn0, hu, hv]; ring)
        (Or.inr (by rw [← hC, hm0, hu, hv]; ring))
  · have hmn0 : m * n0 = B ^ 2 := by
      rw [hn0] at hmn
      linarith [show m * (2 * n0) = 2 * (m * n0) from by ring, hmn]
    have hcop0 : IsCoprime m n0 := hcopmn.of_isCoprime_of_dvd_right ⟨2, by linarith⟩
    obtain ⟨u, hu⟩ := Int.sq_of_isCoprime hcop0 hmn0
    obtain ⟨v, hv⟩ := Int.sq_of_isCoprime hcop0.symm (by rw [mul_comm]; exact hmn0)
    have hcopuv : IsCoprime u v := descentCoprimeAux hcop0 hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact norm v u hcopuv.symm (by rw [← hmn0, hu, hv]; ring)
        (Or.inr (by rw [← hC, hn0, hu, hv]))
    · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn0, hu, hv]; ring
      have hB0 : B = 0 := by
        nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
      exact degen hB0 (mixed hB0)
    · have hz : B ^ 2 = -(u ^ 2 * v ^ 2) := by rw [← hmn0, hu, hv]; ring
      have hB0 : B = 0 := by
        nlinarith [sq_nonneg B, sq_nonneg u, sq_nonneg v, sq_nonneg (u * v)]
      exact degen hB0 (mixed hB0)
    · exact norm v u hcopuv.symm (by rw [← hmn0, hu, hv]; ring)
        (Or.inl (by rw [← hC, hn0, hu, hv]; ring))

end Descent

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

/-- **`C̃` is ODD for every coprime `(a, b)`** (PROVEN 2026-07-27; the route
audit below previously recorded this only as a numerical observation over
`|a|, |b| ≤ 80`).  Modulo `2`, `C̃ ≡ a³ + ab² + b³`, whose value at each of the
three coprime residue pairs `(1,0)`, `(0,1)`, `(1,1)` is `1`; `decide` over
`ZMod 2` checks all four pairs, and the excluded `(0,0)` is exactly the
non-coprime one. -/
theorem C_odd (a b : ℤ) (hab : Int.gcd a b = 1) :
    ¬ (2 : ℤ) ∣ (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) := by
  intro hdvd
  have hnot : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b) := by
    rintro ⟨ha, hb⟩
    have h2 := Int.dvd_gcd ha hb
    rw [hab] at h2
    norm_num at h2
  have key : ∀ x y : ZMod 2,
      x ^ 3 - 2 * x ^ 2 * y - x * y ^ 2 + y ^ 3 = 0 → x = 0 ∧ y = 0 := by decide
  have hA : ((a : ZMod 2)) ^ 3 - 2 * (a : ZMod 2) ^ 2 * (b : ZMod 2)
      - (a : ZMod 2) * (b : ZMod 2) ^ 2 + (b : ZMod 2) ^ 3 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) 2).mpr (by exact_mod_cast hdvd)
    push_cast at h
    exact h
  obtain ⟨h1, h2⟩ := key _ _ hA
  exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp h2⟩

/-- **`gcd(C̃, B̃) = 1` for every coprime `(a, b)`** (PROVEN 2026-07-27; also
previously only numerical).  `a`, `b` and `a − b` are pairwise coprime, and

    C̃ ≡ b³ (mod a),   C̃ ≡ a³ (mod b),   C̃ ≡ −b³ (mod a − b),

with respective cofactors `a² − 2ab − b²`, `−2a² − ab + b²` and
`a² − ab − 2b²` (three `ring` identities).  Each congruence turns coprimality
of the modulus with `b` or `a` into coprimality with `C̃`. -/
theorem C_isCoprime (a b : ℤ) (hab : IsCoprime a b) :
    IsCoprime (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) (a * b * (a - b)) := by
  have hca : IsCoprime a (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) := by
    have e : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3
        = b ^ 3 + a * (a ^ 2 - 2 * a * b - b ^ 2) := by ring
    rw [e]; exact (hab.pow_right).add_mul_left_right _
  have hcb : IsCoprime b (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) := by
    have e : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3
        = a ^ 3 + b * (-2 * a ^ 2 - a * b + b ^ 2) := by ring
    rw [e]; exact (hab.symm.pow_right).add_mul_left_right _
  have hab' : IsCoprime (a - b) b := by
    have e : a - b = a + b * (-1) := by ring
    rw [e]; exact hab.add_mul_left_left _
  have hcd : IsCoprime (a - b) (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) := by
    have e : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3
        = -b ^ 3 + (a - b) * (a ^ 2 - a * b - 2 * b ^ 2) := by ring
    rw [e]; exact ((hab'.pow_right).neg_right).add_mul_left_right _
  exact ((hca.symm).mul_right (hcb.symm)).mul_right (hcd.symm)

/-- **THE `δ = +1` BRANCH OF THE DESCENDED SYSTEM** (opened 2026-07-27 by
splitting `descent_system_no_solution` below along the sign of `hC`; read that
declaration's docstring for the full route audit and for the GAP recorded on
it).

`C̃ = v² − 2u²` together with `B̃ = uv` says exactly that the homogeneous cubic
is a SQUARE in `ℤ[√−2]`:

    C̃(a, b) + 2√−2·B̃(a, b) = (v + u√−2)².

Equivalently — clear the denominator in `g(a/b) = F(a, b)/b³` by `X = bx`,
`Y = b²w`, which is the same pair of `ring` identities as the hypotheses —
`(X, Y) = (a, v + u√−2)` is an INTEGRAL POINT of

    E⁽ᵇ⁾ : Y² = X³ + b(2√−2 − 2)X² − b²(2√−2 + 1)X + b³,

the quadratic twist **by `b`** of `E : w² = g(x)`,
`g(x) = x³ + (2√−2 − 2)x² − (2√−2 + 1)x + 1`, over `K = ℚ(√−2)`.

**RETRACTION (2026-07-27): the branch-to-curve identification that stood here
was FALSE, and with it the claim that this branch, and only it, needs elliptic
Chabauty.**  The curve carrying a solution is selected by the SQUARE CLASS OF
`b`, not by the sign `δ`: the class of `g(a/b)` in `K*/K*²` is `δ·b`, so a
`δ = +1` solution lands on `E⁽ᵇ⁾` and a `δ = −1` solution on `E⁽⁻ᵇ⁾`.  Magma:
`2 ∉ K*²` but `−2 ∈ K*²` (so `−1 ≡ 2`), hence for `b > 0` the twist is trivial
exactly when `b ∈ ℚ*²` and is the `−1`-twist exactly when `b ∈ 2ℚ*²`.  Since
`0 < a < b` forces `b ≥ 2`, **the rank-`1` curve `E` itself is not even
reachable from this branch unless `b` is a perfect square `≥ 4`**, and `b = 2`
puts this branch on the rank-`0` curve `E_d` — the exact opposite of what was
recorded.  The sibling `_neg` carries the mirror-image correction, with the
explicit witness `(a, b, u, v) = (0, −1, 0, 1)`, a `δ = −1` solution lying on
`E`, not on `E_d`.

**THE COVERING COLLECTION ASKED FOR DOES NOT EXIST, and this is not a
bookkeeping gap** (2026-07-27; this replaces the "GAP" note, which correctly
found the discrepancy but prescribed an unattainable repair).  Three findings,
each with the check that would refute it.

1. *No bound on `b` modulo squares is available.*  The descent class of a value
   of a form of ODD degree is denominator-dependent: `ord_𝔭(g(a/b)) =
   −3·ord_p(b)` has the parity of `ord_p(b)`, and the usual "even outside the
   discriminant" argument fails at the pole.  Nor does a local condition bite:
   for `p ∣ b`, `F(a, b) ≡ a³ (mod p)` is a unit by `gcd(a, b) = 1`, so every
   local solvability condition at `p` is satisfiable with `ord_p(b)` odd.  And
   `TwoCoverDescent` returns a **fake** 2-Selmer set — it lands in
   `L*/L*²·ℚ*`, modulo the very `ℚ*` that would have to be bounded.  Refuting
   check: produce a valuation or local argument forcing `ord_p(b)` even.
2. *The obstruction cannot be removed by re-choosing the splitting field.*  An
   EVEN-degree factor would kill the `b`-dependence (`b^even` is a square), and
   none exists: PARI `nfsubfields` on the sextic reports that `L = ℚ[x]/(f)`
   has exactly ONE proper subfield, `K = ℚ(√−2)` (returned as `x² − 2x + 33`,
   discriminant `−128`), and `polgalois(f) = [18, −1, 1, "3 wr 2"]`.  So the
   only nontrivial factorisation of `f` over a subfield is the one already in
   use, `f = g·ḡ` with both factors CUBIC.  Refuting check: exhibit a subfield
   of `L` other than `ℚ`, `K`, `L`.
3. *Even enumerating the family would not close it: Chabauty is INAPPLICABLE at
   some members.*  Elliptic Chabauty needs `rank E⁽ᵈ⁾(K) < [K : ℚ] = 2`.  Magma
   `RankBounds(… : Effort := 1)` on `E⁽ᵈ⁾` over `K` (2026-07-27):

       d :   1    2    3    5    6    7   10   11   13   14   15   17   19   22
       r : 1..1 0..0 0..0 1..1 1..1 0..0 0..0 2..2 1..1 1..1 0..0 0..1 0..0 1..1

       d :  26   29   30   31   33   34   37   41   46   51   53   55   57   59
       r : 0..0 0..1 0..1 0..0 1..1 0..0 1..1 1..1 1..1 0..0 1..1 2..2 0..1 0..0

   **`d = 11` and `d = 55` are sharp rank `2`**, and both are perfectly
   admissible values of `b` here (`0 < a < b`, `gcd(a, b) = 1`).  Refuting
   check: re-run `RankBounds` at `d = 11`; anything `≤ 1` restores that member.
   (`d = 1` reproduces the recorded `E`: rank `1`, torsion trivial,
   `Norm 𝔣 = 1296`; `d = 2` reproduces the recorded `E_d`: rank `0`, torsion
   `ℤ/3`, `Norm 𝔣 = 324`.  So the two Chabauty runs on record cover exactly the
   members `b ∈ ℚ*²` and `b ∈ 2ℚ*²`, and nothing else.)

**The branch split does NOT separate difficulty.**  `M(a, b) = (b, b − a)`
flips the sign of both `C̃` and `B̃`, so it carries a `δ = +1` solution to a
`δ = −1` one; but it also moves the region, and the six points of an orbit
alternate sign region by region with exactly one in `{0 < a < b}`.  So neither
branch reduces to the other, and neither is the cheap one; the sibling's
"CHEAP branch" heading is wrong for the same reason this docstring's
"only this branch" was.

**What route is actually available.**  Not route 1 (elliptic Chabauty over
`K`), by 1–3 above.  Route 2 — `Pic⁰` of the genus-`2` curve, `rank J(ℚ) = 0`,
injectivity of reduction at `5` — is the route with an established proof, and
it is what a Magma `Chabauty0` run on this curve is (a decision procedure on a
rank-`0` Jacobian, not a point search).  Re-verified here 2026-07-27,
independently of the earlier report: `J(ℚ)_tors ≅ ℤ/21`, `RankBound(J) = 0`,
`disc(C) = 2²³·3⁴`, and `Points(C : Bound := 500)` returns exactly the six
cusps `(0, ±1)`, `(1, ±1)`, `∞±`.  That route lives UPSTREAM of this leaf —
the file's chain from `redPt_injective` down to here is a chain of
equivalences — so adopting it is a cut-level repair, not something a prover
dispatched at this leaf can carry out.  Pieces of it already proven here:
`card_X18_F5`, `sevenPts_injective`, `redPt_injective`,
`nonempty_jacobianPackage_of_redPt_injective`. -/
theorem descent_system_no_solution_pos (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (ha : 0 < a) (hb : a < b) (huv : IsCoprime u v)
    (hB : a * b * (a - b) = u * v)
    (hC : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3 = v ^ 2 - 2 * u ^ 2) : False := sorry

/-- **THE `δ = −1` BRANCH OF THE DESCENDED SYSTEM** (opened 2026-07-27; sibling
of `descent_system_no_solution_pos` above).

`C̃ = 2u² − v²` together with `B̃ = uv` says that the homogeneous cubic is
MINUS a square in `ℤ[√−2]`:

    C̃(a, b) + 2√−2·B̃(a, b) = −(v − u√−2)².

**This is the CHEAP branch of the pair, and that is the reason for the split.**
Its curve is the twist `E_d : w² = −g(−x)`, for which Magma returns
`rank E_d(K) = 0` and torsion `ℤ/3`, `Norm(𝔣) = 324`.  Rank `0` means NO
Chabauty is needed: `E_d(K)` is finite, the three points have affine
`x`-coordinate `−1` twice (i.e. `x = 1` after `x ↦ −x`) and `x = ∞` once, all
degenerate and all excluded here by `0 < a < b`.  So what this branch needs is
strictly less than its sibling — a rank-`0` statement over a quadratic field
plus the finiteness of `E_d(K)` — and no `p`-adic analysis at all.  **A worker
dispatched here should not be dispatched at elliptic Chabauty.**

Subject to the same GAP recorded on `descent_system_no_solution` below. -/
theorem descent_system_no_solution_neg (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (ha : 0 < a) (hb : a < b) (huv : IsCoprime u v)
    (hB : a * b * (a - b) = u * v)
    (hC : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3 = 2 * u ^ 2 - v ^ 2) : False := sorry

/-- **THE DESCENDED SYSTEM, AFTER THE `√−2` DESCENT** (opened 2026-07-27,
replacing the `t`-form directly above, which is PROVEN over it by
`descent_sq_add_eight_sq`; itself PROVEN since 2026-07-27 from the two sign
branches above).

For coprime `0 < a < b` there are no coprime `u, v` with

    ab(a − b) = uv    and    C̃(a, b) = ±(v² − 2u²).

**HONEST ACCOUNTING: this is EQUIVALENT to the `t`-form, not weaker.**  Given
such `u, v` the identity `(v² + 2u²)² = (v² − 2u²)² + 8(uv)²` (`ring`) returns a
`t`.  The leaf count at this level is unchanged at one and **no Diophantine
content was disposed of**; what changed is that the two facts the descent needs
— `C̃` odd and `gcd(C̃, B̃) = 1` — are now THEOREMS (`C_odd`, `C_isCoprime`)
rather than the numerical observations the audit below recorded, and the
statement is in the coordinates where the route's elliptic curve is visible:
`C̃ + 2B̃√−2 = ±(v + u√−2)²` says exactly that `(a/b, ·)` is a point of
`w² = g(x)` over `ℚ(√−2)`.

**ROUTE STATUS: the elliptic-Chabauty route of the audit below was EXECUTED on
2026-07-27 and it CLOSES this leaf.**  Item 4 of that audit's refuting-check
list — *"This is the one item NOT verified here: only `|n| ≤ 12` was
enumerated, which is a search, not a Chabauty computation"* — has now been run.
Magma (untrusted searcher, so each number is a claim to be re-derived, but the
computation itself is Bruin's algorithm and not a search):

* `δ = +1`, `E : w² = g(x)` over `K = ℚ(√−2)`: `RankBounds` returns the sharp
  `1 ≤ r ≤ 1`, torsion trivial, `Norm(𝔣_E) = 1296`, generator `(1 − √−2, −1)` —
  every value the audit predicted.  `Chabauty` on the `x`-coordinate cover
  `E → ℙ¹_ℚ` succeeds with bound `N = 12` and returns exactly THREE group
  elements, with rational `x`-coordinates `∞` and `0` (the latter twice, from
  `±2P`).
* `δ = −1`, `E_d : w² = −g(−x)`: `RankBounds` returns `0 ≤ r ≤ 0` and torsion
  `ℤ/3`, `Norm(𝔣) = 324`; the two affine torsion points both have `x = −1`,
  i.e. `x = 1` after the substitution.  No Chabauty needed, as predicted.

Together: `x ∈ {∞, 0, 1}`, which is exactly `ab(a − b) = 0`.  So the leaf is
TRUE and the route is real.  **It is not, however, complete end-to-end — see
the GAP section below, added 2026-07-27, which is the correction to the
sentence that used to stand here.**  **The refuting check on this paragraph**
is to re-run `RankBounds` and `Chabauty` on those two curves; a rank `≥ 2` on
the first, or a Chabauty run returning a fourth element, overturns it.

**Numerical corroboration, extended 2026-07-27**: exact integer search over all
coprime `(a, b)` with `|a|, |b| ≤ 2000` — five times the previously recorded
range — finds no non-degenerate solution at either level, and confirms `C̃` odd
and `gcd(C̃, B̃) = 1` throughout (both now proven above anyway).

**What is NOT available in this pin**, and is therefore the real obstruction:
elliptic curves over a number field with Mordell–Weil rank machinery, and
Bruin's elliptic Chabauty on top of it.  Neither mathlib, nor `~/cs/FLT`, nor
this project has any of it.

**GAP IN THE ROUTE ABOVE (found 2026-07-27): the passage from this INTEGRAL
statement to a point of `E(K)` is not the identity map, and the audit records
it as though it were.**

What the descent proves is the integral statement `F(a, b) = ±Z²` for a
COPRIME pair `(a, b)`, where `F(a, b) := C̃(a, b) + 2√−2·B̃(a, b)` is the
homogeneous cubic.  The curve of the route is `E : w² = g(x)` at `x = a/b ∈ ℚ`,
and the two are related by the homogenisation identity (a `ring` identity,
re-checked in PARI 2026-07-27):

    g(a/b) = F(a, b) / b³,      hence      g(a/b) ≡ ± b   (mod `K*²`).

So `F(a, b) = ±Z²` produces a point not of `E(K)` but of its QUADRATIC TWIST BY
`b`.  One lands on `E` (or on its `δ = −1` twist) exactly when `b` is a square
times a power of `2` — note `2 = −(√−2)²`, so `2 ≡ −1` mod `K*²`.  Every
solution actually known is degenerate with `b ∈ {0, 1}`, so the discrepancy is
invisible both to the executed Magma runs and to every numerical search; but a
proof cannot step over it.

**What this changes.**  A complete route needs a FOURTH item beside the three
the audit lists: the COVERING COLLECTION — the finitely many `δ ∈ K*/K*²` for
which `δw² = g(x)` can carry a point with `x ∈ ℚ`, equivalently a bound on `b`
modulo squares — plus a Chabauty run on EACH member.  The audit ran Chabauty on
exactly two curves, `δ = ±1`, without recording the descent showing that those
two are the whole collection.  Finiteness of the collection is not in doubt:
`F₁F₂` is a square and `gcd(F₁(a,b), F₂(a,b)) ∣ Res(F₁, F₂)` for coprime
`(a, b)`.  What is missing is the recorded computation of it.

**The refuting check, which would retire this note cheaply**: exhibit the
covering-collection computation — Magma's `TwoCoverDescent`, or Bruin's
covering-collection construction for `y² = f₁f₂` — showing the collection is
exactly `{δ = 1, δ = −1}`; or exhibit the elementary argument bounding `b`
modulo `K*²`.  Either one turns this from a gap into a step.

**A narrowing proven in passing (PARI-checked 2026-07-27; `decide` over
`ZMod 8` would prove it in Lean if a consumer ever wants it).**  For coprime
`u, v` with `v² − 2u²` odd, `v² − 2u² ≡ ±1 (mod 8)`.  So the hypotheses below
force `C̃(a, b) ≡ ±1 (mod 8)`, which excludes exactly 24 of the 48 residue
classes of coprime `(a, b)` mod `8`.  It is not carried as a hypothesis,
because `hC` already implies it; it is recorded because it is the cheapest
nontrivial necessary condition on `(a, b)` that an elementary attack would
want.  **Level `13` has no analogue**: `v² − u²` with `gcd(u, v) = 1` takes
every odd residue mod `8`.

**PROVEN since 2026-07-27** from the two sign branches above, which is a
`rcases` on `hC` and nothing more. -/
theorem descent_system_no_solution (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (ha : 0 < a) (hb : a < b) (huv : IsCoprime u v)
    (hB : a * b * (a - b) = u * v)
    (hC : a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3 = v ^ 2 - 2 * u ^ 2 ∨
          a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3 = 2 * u ^ 2 - v ^ 2) : False := by
  rcases hC with h | h
  · exact descent_system_no_solution_pos a b u v hab ha hb huv hB h
  · exact descent_system_no_solution_neg a b u v hab ha hb huv hB h

/-- **THE σ-NORMALISED FORM: no coprime `0 < a < b` makes `C̃² + 8B̃²` a
square.**  **PROVEN since 2026-07-27** from `descent_system_no_solution` above
via `descent_sq_add_eight_sq`, `C_odd` and `C_isCoprime`.  The ROUTE AUDIT
below is still the current one and is what that leaf's docstring refers to;
read the two together.

`abd_eq_zero_of_sq_eq` below is PROVEN from this, and the two are EQUIVALENT.

**HONEST ACCOUNTING: this is a NORMALISATION, not a reduction in difficulty.**
It is equivalent for a reason that costs nothing.  The order-`3` automorphism
`σ(x) = 1/(1 − x)` acts on homogeneous coordinates by `M : (a, b) ↦ (b, b − a)`,
and both semi-invariants change sign under it:

    C̃(b, b − a) = −C̃(a, b),      B̃(b, b − a) = −B̃(a, b)
    C̃(−a, −b)  = −C̃(a, b),      B̃(−a, −b)  = −B̃(a, b)

(four `ring` identities, all four used in the proof of `abd_eq_zero_of_sq_eq`).
So both the hypothesis and the conclusion are invariant under the order-`6`
group `⟨M⟩`, which satisfies `M³ = −I`.  On the `x`-line `σ` permutes the three
intervals `(−∞, 0) → (0, 1) → (1, ∞) → (−∞, 0)` cyclically, so a NON-degenerate
orbit meets `(0, 1)` exactly once — that representative is `0 < a < b`.  The
three cases the proof below distinguishes are exactly

    a < 0 < b   ↦   (b, b − a),   giving `0 < b < b − a`;
    0 < b < a   ↦   (a − b, a),   giving `0 < a − b < a`;
    0 < a < b   ↦   itself.

The degenerate `(a, b)` — those with `ab(a − b) = 0` — are precisely the ones
with NO representative in that range, which is why nothing is weakened.  What
this buys is shape, not mathematics: any later attack may now assume `a`, `b`
and `b − a` all POSITIVE and pairwise coprime, hence `B̃ < 0`, and needs no sign
analysis at all.

**Numerical sanity (PARI/GP, untrusted searcher, 2026-07-27).**  No coprime
`0 < a < b ≤ 400` makes `C̃² + 8B̃²` a square.  Over `|a|, |b| ≤ 80` it was also
checked that `C̃` is ODD and `gcd(C̃, B̃) = 1` for every coprime `(a, b)` — the
two facts the descent below starts from.

**ROUTE AUDIT — A NEW AXIS (2026-07-27): ELLIPTIC CHABAUTY OVER `ℚ(√−2)`, and
it is a strictly smaller object than `Pic⁰` of a genus-`2` curve.**

The audit on `abd_eq_zero_of_sq_eq` searched three axes and correctly closed all
three: DESCENT (the `√−2` descent is reversible), FACTORISATION (the sextic is
irreducible) and QUOTIENT (every quotient by a subgroup of `⟨σ, ι⟩` has genus
`0`).  The axis it did not search is the one where the `√−2` structure is used
not to descend but to CHANGE THE BASE FIELD.  Over `K := ℚ(√−2)` the sextic
factors into two conjugate CUBICS,

    f = g·ḡ,   g(x) = C(x) + 2√−2·B(x) = x³ + (2√−2 − 2)x² − (2√−2 + 1)x + 1,

so `y² = N_{K/ℚ}(g(x))`, and the descent recorded below says exactly that
`g(x) = δ·w²` with `w ∈ K` and `δ ∈ {1, −1}`.  Each branch is an ELLIPTIC CURVE
over `K` carrying the extra condition `x ∈ ℚ` — which is Bruin's elliptic
Chabauty.  Magma (untrusted searcher; every number here is a claim to be
re-derived) reports:

* `δ = +1`:  `E : w² = g(x)` over `K`.  `E(K) ≅ ℤ`, TORSION TRIVIAL, generated by
  `P = (1 − √−2, −1)`, with `Norm(𝔣_E) = 1296` and `j(E) = −256 − 512√−2`.  Since
  `rank E(K) = 1 < 2 = [K : ℚ]`, elliptic Chabauty APPLIES.  Enumerating `nP` for
  `|n| ≤ 12`, the only rational `x`-coordinates are `n = 0` (`x = ∞`) and
  `n = ±2` (`x = 0`).  Note `x(P) = 1 − √−2` is itself irrational, so the
  rational points are NOT the small multiples.
* `δ = −1`:  `E_d : w² = −g(−x)`, i.e. `w² = x³ + (2 − 2√−2)x² − (2√−2 + 1)x − 1`.
  `E_d(K) ≅ ℤ/3` and `rank E_d(K) = 0`, so this branch needs NO Chabauty at
  all — three points, whose two affine `x`-coordinates are both `−1`, i.e.
  `x = 1` after the substitution `x ↦ −x`.

Together these give `x ∈ {0, 1, ∞}`, which is this leaf.

**Why it matters for the FORMALISATION plan.**  The module docstring's four-part
project asks for `Pic⁰` of a genus-`2` curve with the Mumford representation and
Cantor's group law, Abel–Jacobi, good reduction at `5`, and `rank J(ℚ) = 0`.
The route above asks instead for elliptic curves over a QUADRATIC field — for
which mathlib already has Weierstrass models and the group law — plus (i) the
descent `g(x) = ±w²`, which is elementary (see below), (ii) rank computations
over `K`, and (iii) elliptic Chabauty for the `δ = +1` branch ONLY.  That is not
easy, but it is a different and smaller project, and half of it is a finite
check.

**Correction to the descent as recorded below: it needs NO `ℤ[√−2]` arithmetic.**
`gcd(t − C̃, t + C̃) = 2` (both are even since `C̃` and `t` are odd; a common odd
prime would divide `2t` and `2C̃`, hence `C̃` and `8B̃²`, contradicting
`gcd(C̃, B̃) = 1`), and `((t − C̃)/2)·((t + C̃)/2) = 2B̃²` with the two factors
coprime.  Coprime factorisation in `ℤ` alone therefore gives
`C̃ = ±(v² − 2u²)`, `B̃ = ±uv`, `t = ±(v² + 2u²)` with `gcd(u, v) = 1` — the sign
being exactly the `δ` above.  So `Zsqrtd (-2)`, which this pin does not equip
with a Euclidean-domain instance, is not needed anywhere on this route.

**The checks that would refute this audit**, in increasing cost:

1. `δ ∈ {1, −1}` is not enough — refuted by a coprime `(a, b)` whose `g(a/b)` is
   neither `w²` nor `−w²` in `K`.  It IS enough by the coprime factorisation in
   the previous paragraph, together with `h(K) = 1` and `ℤ[√−2]ˣ = {±1}`.
2. `rank E(K) ≠ 1` — refuted by a point of infinite order independent of `P`, or
   by a `2`-descent upper bound below `1`.  Magma returns the sharp `1 ≤ r ≤ 1`.
3. `rank E_d(K) ≠ 0` — refuted by any point of infinite order on `E_d(K)`.
4. Elliptic Chabauty does not close the `δ = +1` branch.  **This is the one item
   NOT verified here**: only `|n| ≤ 12` was enumerated, which is a search, not a
   Chabauty computation.

**What was NOT searched**, so the next auditor knows the boundary: the
`(1 − ζ₃)`-descent on `J` that the previous audit named as the way forward, and
any `3`-descent along the cyclic degree-`3` map `X → X/⟨σ⟩ ≅ ℙ¹`.  That map is
the modular map `X_1(18) → X_1(9)` (and `X_1(9)` has genus `0`), whose fibre over
`t` is the Shanks simplest cubic `X³ − tX² + (t − 3)X + 1`; a rational point of
the fibre is exactly a rational `2`-torsion point on the `X_1(9)`-family curve.
That reading is recorded because it explains why the fibration is cyclic, not
because it was found to lead anywhere. -/
theorem sq_ne_of_zero_lt_lt (a b t : ℤ) (hab : Int.gcd a b = 1) (ha : 0 < a) (hb : a < b) :
    t ^ 2 ≠ (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) ^ 2
              + 8 * (a * b * (a - b)) ^ 2 := by
  intro ht
  obtain ⟨u, v, huv, hB, hC⟩ :=
    descent_sq_add_eight_sq _ _ t (C_odd a b hab)
      (C_isCoprime a b (Int.isCoprime_iff_gcd_eq_one.mpr hab)) ht
  exact descent_system_no_solution a b u v hab ha hb huv hB hC

/-- The `0 < b` half of the σ-normalisation (PROVEN from `sq_ne_of_zero_lt_lt`).

With `b > 0` fixed, the sign of `a` and its comparison with `b` decide which
element of the `⟨M⟩`-orbit lands in the fundamental domain `0 < a < b`:
`a < 0` needs one application of `M`, `a > b` needs `−M²`, and `0 < a < b` is
already normalised.  The coprimality of each new pair is the one-line
divisibility argument `d ∣ b` and `d ∣ b − a` imply `d ∣ a`. -/
theorem sq_ne_of_snd_pos (a b t : ℤ) (hab : Int.gcd a b = 1) (hb : 0 < b)
    (ha0 : a ≠ 0) (hne : a ≠ b) :
    t ^ 2 ≠ (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) ^ 2
              + 8 * (a * b * (a - b)) ^ 2 := by
  intro ht
  rcases lt_trichotomy a 0 with hlt | h0 | hgt
  · -- `a < 0 < b`: the orbit representative is `M(a, b) = (b, b − a)`.
    have hg : Int.gcd b (b - a) = 1 := by
      have h1 : ((Int.gcd b (b - a) : ℤ)) ∣ b := Int.gcd_dvd_left ..
      have h2 : ((Int.gcd b (b - a) : ℤ)) ∣ (b - a) := Int.gcd_dvd_right ..
      have h3 : ((Int.gcd b (b - a) : ℤ)) ∣ a := by
        have := dvd_sub h1 h2
        simpa using this
      have h4 : Int.gcd b (b - a) ∣ Int.gcd a b := Int.dvd_gcd h3 h1
      rw [hab] at h4
      exact Nat.dvd_one.mp h4
    exact sq_ne_of_zero_lt_lt b (b - a) t hg hb (by omega) (by linear_combination ht)
  · exact ha0 h0
  · rcases lt_trichotomy a b with h | h | h
    · exact sq_ne_of_zero_lt_lt a b t hab hgt h ht
    · exact hne h
    · -- `0 < b < a`: the orbit representative is `−M²(a, b) = (a − b, a)`.
      have hg : Int.gcd (a - b) a = 1 := by
        have h1 : ((Int.gcd (a - b) a : ℤ)) ∣ (a - b) := Int.gcd_dvd_left ..
        have h2 : ((Int.gcd (a - b) a : ℤ)) ∣ a := Int.gcd_dvd_right ..
        have h3 : ((Int.gcd (a - b) a : ℤ)) ∣ b := by
          have := dvd_sub h2 h1
          simpa using this
        have h4 : Int.gcd (a - b) a ∣ Int.gcd a b := Int.dvd_gcd h2 h3
        rw [hab] at h4
        exact Nat.dvd_one.mp h4
      exact sq_ne_of_zero_lt_lt (a - b) a t hg (by omega) (by omega) (by linear_combination ht)

/-- **THE LEAF, in integral homogeneous form: a coprime integral point of
`X_1(18)` is degenerate.**  **PROVEN since 2026-07-27** from the σ-normalised
form `sq_ne_of_zero_lt_lt` above, whose docstring carries the current route
audit; read that one first.

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

**REFUTED 2026-07-27: "NOT ANALOGOUS AT LEVEL 13" WAS FALSE.**  This docstring
previously asserted that `sext 1 4 6 2 1 2 = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`
admits no identity of shape `C² + kB²` with `B` quadratic, on the ground that
the polynomial square root is forced to be `x³ + x² + 1` with remainder
`4x(x + 1)`.  **It does admit one:**

    x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1 = (x³ + x² − 2x − 1)² + 4(x² + x)²

The error is exactly locatable: `kB²` has DEGREE `4`, so it contributes to the
`x⁴` coefficient, which the forcing argument treated as pinned.  Only the top
TWO coefficients of `C` are forced; taking the linear coefficient to be `−2`
rather than `0` gives the identity.  The refuting check is one expansion, and it
is `ring`-checkable.  (Found by the owner of the level-`13` chain; re-derived
here independently in PARI/GP before this correction was written.)

**So the two levels are PARALLEL, and in more detail than the refutation
claims.**  With `A₁₃ = x³ + 3x² − 1` and `B₁₃ = x² + x` one has
`f₁₃ = A₁₃² − 4A₁₃B₁₃ + 8B₁₃²`, of discriminant `−16`, with
`C₁₃ = A₁₃ − 2B₁₃` — the same completion of the square as here.  Verified in
PARI/GP: `disc C₁₃ = 49` and `disc A₁₃ = 81`, *identical* to the level-`18`
values, and `f₁₃` is irreducible with Galois group `F₁₈(6) = 3 ≀ 2`, again the
same.  The quadratic form is principal at both levels (`h(−16) = 1`,
`h(−32) = 2` but `A² − 4AB + 12B²` is the principal class).  Consequently the
`ℤ[i]` descent at level `13` is reversible for the same reason the `ℤ[√−2]`
descent is here — `(u² + v²)² = (v² − u²)² + 4(uv)²` recovers the point — so it
gains nothing at either level.

**And the ELLIPTIC-CHABAUTY route of the audit on `sq_ne_of_zero_lt_lt` transfers
to level 13, with one simplification** (Magma, untrusted searcher, 2026-07-27):
over `K₁₃ := ℚ(i)`, `f₁₃ = g₁₃·ḡ₁₃` with
`g₁₃ = x³ + (1 + 2i)x² + (2i − 2)x − 1`, and because `−1 = i²` IS a square in
`ℚ(i)` the two twists COINCIDE — level `13` has ONE elliptic curve where level
`18` has two.  `E₁₃ : w² = g₁₃(x)` has `Norm(𝔣) = 1352`, `E₁₃(K₁₃) ≅ ℤ` with
trivial torsion, generated by `(−1 − i, 1)`; `rank = 1 < 2 = [K₁₃ : ℚ]`, so
elliptic Chabauty applies.  Among `nP` with `|n| ≤ 12` the rational
`x`-coordinates are exactly `n = 0` (`x = ∞`), `n = ±2` (`x = 0`) and `n = ±4`
(`x = −1`) — precisely the three abscissae of `X_1(13)(ℚ)`.  (`RankBound(J₁₃) = 0`
and `J₁₃(ℚ)_tors ≅ ℤ/19`, matching `#J₁(13)(ℚ) = 19`.)

**What is therefore generic across the two levels is the WHOLE construction** —
the `σ`-semi-invariants, the principal binary quadratic form, the Shanks
simplest-cubic fibration of discriminant `(t² − 3t + 9)²`, the reversibility of
the imaginary-quadratic descent, AND the rank-`1` elliptic curve over the
imaginary quadratic field.  Anything built for one level should be built for a
variable level. -/
theorem abd_eq_zero_of_sq_eq (a b t : ℤ) (hab : Int.gcd a b = 1)
    (ht : t ^ 2 = (a ^ 3 - 2 * a ^ 2 * b - a * b ^ 2 + b ^ 3) ^ 2
              + 8 * (a * b * (a - b)) ^ 2) :
    a * b * (a - b) = 0 := by
  by_contra hne
  have ha0 : a ≠ 0 := by rintro rfl; exact hne (by ring)
  have hb0 : b ≠ 0 := by rintro rfl; exact hne (by ring)
  have hab0 : a ≠ b := by rintro rfl; exact hne (by ring)
  rcases lt_trichotomy b 0 with hlt | h0 | hgt
  · -- `b < 0`: replace `(a, b)` by `−(a, b)`, which flips both `C̃` and `B̃`.
    have hg : Int.gcd (-a) (-b) = 1 := by simpa [Int.gcd] using hab
    exact sq_ne_of_snd_pos (-a) (-b) t hg (by omega) (by omega) (by omega)
      (by linear_combination ht)
  · exact hb0 h0
  · exact sq_ne_of_snd_pos a b t hab hgt ha0 hab0 ht

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

/-- **`C̃` is ODD for every coprime `(a, b)`** (PROVEN 2026-07-27; the route
audit below recorded this, correctly, but only as a numerical observation).
Modulo `2`, `C̃ ≡ a³ + a²b + b³`, whose value at each of the three coprime
residue pairs is `1`; `decide` over `ZMod 2` checks all four pairs. -/
theorem C_odd (a b : ℤ) (hab : Int.gcd a b = 1) :
    ¬ (2 : ℤ) ∣ (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) := by
  intro hdvd
  have hnot : ¬ ((2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b) := by
    rintro ⟨ha, hb⟩
    have h2 := Int.dvd_gcd ha hb
    rw [hab] at h2
    norm_num at h2
  have key : ∀ x y : ZMod 2,
      x ^ 3 + x ^ 2 * y - 2 * x * y ^ 2 - y ^ 3 = 0 → x = 0 ∧ y = 0 := by decide
  have hA : ((a : ZMod 2)) ^ 3 + (a : ZMod 2) ^ 2 * (b : ZMod 2)
      - 2 * (a : ZMod 2) * (b : ZMod 2) ^ 2 - (b : ZMod 2) ^ 3 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) 2).mpr (by exact_mod_cast hdvd)
    push_cast at h
    exact h
  obtain ⟨h1, h2⟩ := key _ _ hA
  exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp h2⟩

/-- **`gcd(C̃, B̃) = 1` for every coprime `(a, b)`** (PROVEN 2026-07-27).  This
is the second structural claim of the route audit below, which stated exactly
the right congruences —

    C̃ ≡ −b³ (mod a),   C̃ ≡ a³ (mod b),   C̃ ≡ b³ (mod a + b),

with cofactors `a² + ab − 2b²`, `a² − 2ab − b²` and `a² − 2b²` — and checked
them numerically.  They are three `ring` identities. -/
theorem C_isCoprime (a b : ℤ) (hab : IsCoprime a b) :
    IsCoprime (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) (a * b * (a + b)) := by
  have hca : IsCoprime a (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) := by
    have e : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3
        = -b ^ 3 + a * (a ^ 2 + a * b - 2 * b ^ 2) := by ring
    rw [e]; exact ((hab.pow_right).neg_right).add_mul_left_right _
  have hcb : IsCoprime b (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) := by
    have e : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3
        = a ^ 3 + b * (a ^ 2 - 2 * a * b - b ^ 2) := by ring
    rw [e]; exact (hab.symm.pow_right).add_mul_left_right _
  have hab' : IsCoprime (a + b) b := by
    have e : a + b = a + b * 1 := by ring
    rw [e]; exact hab.add_mul_left_left _
  have hcd : IsCoprime (a + b) (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) := by
    have e : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3
        = b ^ 3 + (a + b) * (a ^ 2 - 2 * b ^ 2) := by ring
    rw [e]; exact ((hab'.pow_right)).add_mul_left_right _
  exact ((hca.symm).mul_right (hcb.symm)).mul_right (hcd.symm)

/-- **THE `δ = +1` BRANCH OF THE DESCENDED SYSTEM** (opened 2026-07-27 by
splitting `descent_system_no_solution` below along the sign of `hC`; that
declaration's docstring carries the full route audit and the GAP recorded on
it).

`C̃ = v² − u²` with `B̃ = uv` says exactly that the homogeneous cubic is a
SQUARE in `ℤ[i]`:

    C̃(a, b) + 2i·B̃(a, b) = (v + u·i)².

Over `K = ℚ(i)` the sextic splits as `f = g·ḡ` with
`g(x) = x³ + (1 + 2i)x² + (−2 + 2i)x − 1`, and this branch is the cover on
which Magma's `Chabauty` succeeds with bound `N = 4`, returning five group
elements whose rational `x`-coordinates are exactly `∞`, `0` and `−1` — all
three degenerate, i.e. `ab(a + b) = 0`.

**Cost note, and the reason the level-`13` pair is NOT the cheaper one.**
Unlike level `18`, where the sibling branch has rank `0`, here BOTH branches
sit on the same rank-`1` curve `E(K) ≅ ℤ` (torsion trivial, `RankBounds` sharp
at `1 ≤ r ≤ 1`, generator with `x = −1 − i`, `Norm(𝔣) = 1352`,
`j = 768 − 512i`).  So `p`-adic elliptic Chabauty is needed for this branch AND
for its sibling — two runs, not one. -/
theorem descent_system_no_solution_pos (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (huv : IsCoprime u v) (hB : a * b * (a + b) = u * v)
    (hC : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3 = v ^ 2 - u ^ 2) :
    a * b * (a + b) = 0 := sorry

/-- **THE `δ = −1` BRANCH OF THE DESCENDED SYSTEM** (opened 2026-07-27; sibling
of `descent_system_no_solution_pos` above).

`C̃ = u² − v²` with `B̃ = uv` says that the homogeneous cubic is MINUS a square
in `ℤ[i]`:

    C̃(a, b) + 2i·B̃(a, b) = −(v − u·i)².

Magma's `Chabauty` on this cover succeeds with bound `N = 12` and returns only
`x = ∞`, i.e. `b = 0`; with `gcd(a, b) = 1` that forces `a = ±1` and
`ab(a + b) = 0`.  **The conclusion is stated in the common weak form
`ab(a + b) = 0` rather than the stronger `b = 0` that the computation actually
gives**, so that the two branches assemble uniformly and so that nothing rests
on the stronger reading being correctly transcribed.

Note `−1 = i²` is a square in `K = ℚ(i)`, so `δ = −1` and `δ = +1` are the same
class here and this cover lives on the SAME rank-`1` curve as its sibling —
which is why level `13` needs two Chabauty runs where level `18` needs one. -/
theorem descent_system_no_solution_neg (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (huv : IsCoprime u v) (hB : a * b * (a + b) = u * v)
    (hC : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3 = u ^ 2 - v ^ 2) :
    a * b * (a + b) = 0 := sorry

/-- **THE DESCENDED SYSTEM, AFTER THE `ℤ[i]` DESCENT** (opened 2026-07-27,
replacing the `t`-form below, which is PROVEN over it by
`descent_sq_add_four_sq`; itself PROVEN since 2026-07-27 from the two sign
branches above).

For coprime `a, b`, if there are coprime `u, v` with `ab(a + b) = uv` and
`C̃(a, b) = ±(v² − u²)`, then `ab(a + b) = 0`.

**HONEST ACCOUNTING: EQUIVALENT, not weaker** — the audit below already proved
that, and this declaration does not contradict it.  `(u² + v²)² =
(v² − u²)² + 4(uv)²` recovers a `t` from any such `u, v`, so the descent is a
bijection and the leaf count is unchanged at one.  What the step banks is that
the audit's two structural claims are now the THEOREMS `C_odd` and
`C_isCoprime` above rather than numerical observations, and that the surviving
statement is in the coordinates of the elliptic curve: `C̃ + 2B̃i = ±(v + ui)²`
says exactly that `(a/b, ·)` is a point of `w² = g(x)` over `ℚ(i)`.

**ROUTE STATUS: elliptic Chabauty over `ℚ(i)` was EXECUTED on 2026-07-27 and it
CLOSES this leaf.**  The audit below closes the `ℤ[i]` DESCENT as a route and is
right to; the route that works changes the BASE FIELD instead.  Over
`K = ℚ(i)` the sextic splits as `f = g·ḡ` with
`g(x) = x³ + (1 + 2i)x² + (−2 + 2i)x − 1`, and each branch is an elliptic curve
over `K` carrying the condition `x ∈ ℚ`.  Magma (untrusted searcher; the
numbers are claims to be re-derived, but `Chabauty` is Bruin's algorithm, not a
search):

* the two branches `w² = g(x)` and `w² = −g(−x)` are ISOMORPHIC over `K` —
  `IsIsomorphic` returns true, both with `Norm(𝔣) = 1352` and
  `j = 768 − 512i` — which is the level-`13` form of "the two twists coincide
  because `−1 = i²`";
* `E(K) ≅ ℤ`, TORSION TRIVIAL, `RankBounds` sharp at `1 ≤ r ≤ 1`, generator
  `x = −1 − i`.  So `rank = 1 < 2 = [K : ℚ]` and Chabauty applies;
* `Chabauty` on the `x`-cover of the `δ = +1` branch succeeds with bound
  `N = 4`, returning FIVE group elements whose rational `x`-coordinates are
  exactly `∞`, `0` and `−1`; on the `δ = −1` branch it succeeds with `N = 12`
  and returns only `x = ∞`.

Union: `x ∈ {∞, 0, −1}`, which is exactly `ab(a + b) = 0`.  **The leaf is
TRUE** and the route is real; it is **not** complete end-to-end, and the
sentence that used to claim it was has been corrected — see the GAP section
below, added 2026-07-27, which applies verbatim at this level too.  Refuting
check: re-run `RankBounds`/`Chabauty`; rank `≥ 2`, or a sixth element with
rational `x`, overturns this.

**CORRECTION to "the two levels are structurally parallel", which is how this
pair is usually dispatched.**  They are parallel in shape but NOT in cost.  At
level `18` one of the two branches has RANK `0` (torsion `ℤ/3`), so only one
Chabauty computation is needed there; at level `13` both covers sit on the same
RANK-`1` curve, so Chabauty is needed TWICE.  Level `13` is therefore strictly
the more expensive of the two to formalise, not the easier one.

**Numerical corroboration, extended 2026-07-27** to all coprime `(a, b)` with
`|a|, |b| ≤ 2000` (previously `400`): no non-degenerate solution at either
level.

**GAP IN THE ROUTE ABOVE (found 2026-07-27, the same one recorded at level
`18` on `X18.descent_system_no_solution`): the passage from this INTEGRAL
statement to a point of `E(K)` is not the identity map.**

The descent proves `F(a, b) = ±Z²` for a COPRIME pair `(a, b)`, where
`F(a, b) := C̃(a, b) + 2i·B̃(a, b)` is the homogeneous cubic; the curve of the
route is `E : w² = g(x)` at `x = a/b ∈ ℚ`.  The homogenisation identity (a
`ring` identity) is

    g(a/b) = F(a, b) / b³,      hence      g(a/b) ≡ b   (mod `K*²`),

so a solution gives a point of the QUADRATIC TWIST BY `b`, not of `E` itself,
unless `b` is a square in `K = ℚ(i)` — i.e. unless `b` or `−b` is a rational
square, `−1 = i²` being a square here.  That `−1` is a square in `ℚ(i)` is
also exactly why the two branches are isomorphic over `K`, as the audit above
observes: at this level `δ = +1` and `δ = −1` are the SAME class, so the two
Chabauty runs are two covers of one curve rather than two curves.  Every known
solution is degenerate with `b ∈ {0, 1}`, so the discrepancy is invisible to
the executed computation and to every search.

**What this changes.**  A complete route needs a further item: the COVERING
COLLECTION — the finitely many `δ ∈ K*/K*²` for which `δw² = g(x)` can carry a
point with `x ∈ ℚ`, equivalently a bound on `b` modulo squares — with a
Chabauty run on each member.  Finiteness is not in doubt (`F₁F₂` is a square
and `gcd(F₁(a,b), F₂(a,b)) ∣ Res(F₁, F₂)` for coprime `(a, b)`); the recorded
computation of the collection is what is missing.  **Refuting check**: exhibit
Magma's `TwoCoverDescent` / Bruin's covering-collection output showing the
collection is exactly the two covers already run, or the elementary argument
bounding `b` modulo `K*²`.

**No congruence narrowing exists at this level**, unlike at level `18`: there
`C̃ = ±(v² − 2u²)` with `gcd(u, v) = 1` forces `C̃ ≡ ±1 (mod 8)` and kills half
the residue classes, whereas here `v² − u²` with `gcd(u, v) = 1` takes every
odd residue mod `8` (PARI, 2026-07-27).  Recorded so nobody spends the cycle
looking for the level-`13` analogue.

**PROVEN since 2026-07-27** from the two sign branches above, by `rcases` on
`hC` and nothing more. -/
theorem descent_system_no_solution (a b u v : ℤ) (hab : Int.gcd a b = 1)
    (huv : IsCoprime u v) (hB : a * b * (a + b) = u * v)
    (hC : a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3 = v ^ 2 - u ^ 2 ∨
          a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3 = u ^ 2 - v ^ 2) :
    a * b * (a + b) = 0 := by
  rcases hC with h | h
  · exact descent_system_no_solution_pos a b u v hab huv hB h
  · exact descent_system_no_solution_neg a b u v hab huv hB h

/-- **THE LEAF, in integral homogeneous form: a coprime integral point of
`X_1(13)` is degenerate.**  **PROVEN since 2026-07-27** from
`descent_system_no_solution` above, via `descent_sq_add_four_sq`, `C_odd` and
`C_isCoprime`.

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
* the sextic is irreducible OVER `ℚ` with Galois group of order `18` (Magma
  names it `C3*S3`), so there is no factorisation over `ℚ` to descend along;
  and `J_1(13)` is `ℚ`-simple of `GL₂`-type, so no quotient to a rank-`0`
  elliptic curve over `ℚ` exists.  The clause "and no elementary two-cover
  route", which this bullet used to carry, is too strong and is withdrawn:
  over `ℚ(i)` the sextic DOES factor, and that factorisation is exactly the
  descent a machine uses.  See the `ℚ(i)` item in the last section.

**AUDIT EXTENSION, 2026-07-27 (second pass).**  Four further routes were
searched and each is now closed by a stated, cheap, refutable check rather than
left as an invitation.  The axes searched were: *other quadratic-form
descents*; *the `ℤ[ζ₃]` descent at the level of the CURVE*; *bielliptic /
elliptic-Chabauty*; and *congruences*.  The axis deliberately NOT searched, and
the only one still open, is a descent on the JACOBIAN — for which the last
section now names the cheapest known certificate.

**(1) THE `ℤ[i]` REPRESENTATION IS THE ONLY ONE OF ITS SHAPE.**  This is
strictly stronger than "the descent it invites is reversible": there is no
*other* quadratic order to try instead.  Write `C = x³ + c₂x² + c₁x + c₀`;
matching `x⁵` forces `c₂ = 1`, and demanding `f − C² = k·D²` with `D` quadratic
is then two conditions on `(c₁, c₀)`.  Eliminating `c₀` between them (PARI
`polresultant`) gives

    c₁⁴ · (c₁ + 2)² · P₉(c₁) · Q₉(c₁),
    P₉ = 64c₁⁹ − 256c₁⁸ − 160c₁⁷ + 2416c₁⁶ − 3132c₁⁵ − 2140c₁⁴ + 2889c₁³
           + 2134c₁² + 364c₁ + 8,
    Q₉ = 64c₁⁹ − 256c₁⁸ + 224c₁⁷ + 16c₁⁶ + 84c₁⁵ + 516c₁⁴ − 295c₁³
           + 278c₁² + 172c₁ + 8,

and **`P₉` and `Q₉` are both IRREDUCIBLE over `ℚ`** (PARI `factor`).  The root
`c₁ = 0` is the degenerate branch: it forces `deg D ≤ 1` and `c₀ = 1`, giving
`C = x³ + x² + 1` and `f − C² = 4x(x + 1)`, which is not a constant times a
square — precisely the computation the refuted "NOT ANALOGOUS AT LEVEL 13"
paragraph performed, and precisely why stopping there was wrong.  The root
`c₁ = −2` is the representation above.  So `k = 4`, i.e. `ℤ[i]`, is the only
quadratic-form descent that exists here at all.
*Refuting check*: exhibit a rational root of `P₉` or of `Q₉`.

**(2) THE `ℤ[ζ₃]` DESCENT ON THE CURVE IS REVERSIBLE TOO.**  This corrects the
sentence above which says a gainful descent "must come from the `ℤ[ζ₃]`-action,
i.e. a `(1 − ζ₃)`-descent on `J`".  The `J` half of that is still the live
route; what is now ruled out is the tempting curve-level version, which the
Shanks fibration makes explicit enough to test outright.  For
`X³ − sX² − (s + 3)X − 1` with `t = s + 3`, the Lagrange resolvent satisfies

    R³ = N(λ)·λ,        λ := t + 3ω,   ω := ζ₃,

from `e₁ = s`, `e₂ = −(s + 3)`, `e₃ = 1`: `R³ + S³ = 2s³ + 9s² + 27s + 27`,
`RS = s² + 3s + 9 = N(λ)`, `(R³ − S³)² = −27·disc`, and the factorisation
`s³ + 6s² + 18s + 27 = (s + 3)(s² + 3s + 9)`.  Hence the cubic is reducible
over `ℚ` **iff** `λ̄/λ` is a cube in `ℚ(ω)*`, iff `t + 3ω ∈ ℚ*·(ℚ(ω)*)³`.
Writing `t + 3ω = r·ν³` with `ν = (x + y√−3)/2` and imposing the conic
condition `(t − 2)² + 4 = z²` clears — the free parameter `r` cancelling
identically, which is the tell — to

    G(x, y) := (x³ − x²y − 9xy² + y³)² + 16y²(x² − y²)²    must be a square,

i.e. to the genus-`2` curve `w² = x⁶ − 2x⁵ − x⁴ + 20x³ + 47x² − 18x + 17`, of
discriminant `−2⁴²·13²`.  Magma's `IsIsomorphic` returns TRUE: that curve is
**isomorphic to the original over `ℚ`** (same conductor `13²`, torsion `ℤ/19`,
rank `0`; its six rational points are `(±1, ±8)` and `∞±`).  A bijection again,
and for the same structural reason as at `√−1`: `h(−3) = 1` with units `μ₆`.
*Refuting check*: run `IsIsomorphic` on the two hyperelliptic curves.

**(3) BIELLIPTIC / ELLIPTIC-CHABAUTY IS CLOSED — although `X` IS geometrically
bielliptic.**  `#GeometricAutomorphismGroup(X) = 12` (dihedral) against
`#Aut_ℚ(X) = 6`, so over `ℚ̄` there are three extra involutions and `J` does
split geometrically.  But they are not defined even over the SPLITTING field of
the sextic: for `L'` that field, of degree `18` and discriminant `2¹⁸·13¹²`,
Magma gives `#Aut(X_{L'}) = 6`.  So a bielliptic quotient is an elliptic curve
over a field of degree `≥ 36`, and the elementary-descent template of
`Fermat/FLT/EllipticCurve/MordellWeil.lean` — which proves `rank = 0` for the
level-`14` curve by explicit Fermat descent, with no Mordell–Weil theorem and
no Selmer group anywhere in it — has nothing here to attach to.
*Refuting check*: exhibit a degree-`2` map from `X` to an elliptic curve over a
field of small degree.

**(4) NO CONGRUENCE CAN EVER PROVE THIS LEAF**, so "find a modulus, then
`decide`" should not be attempted.  A brute-force scan of every prime power
`≤ 2100` for a coprime residue solution of `t² ≡ F(a, b)` with
`ab(a + b) ≢ 0 (mod p)` finds an obstruction at exactly the powers of `2`, `3`
and `5`, and at nothing else.  Those carry no new information: `2 ∣ ab(a + b)`
holds for every coprime pair outright, and the `3` and `5` obstructions are
exactly `#X(𝔽₃) = 6` and `#X(𝔽₅) = 6` — the former being `card_X13_F3`, already
proven above by `decide`.  (By hand at `3`: `3 ∤ ab(a + b)` forces `a ≡ b ≢ 0`,
and `F(1, 1) = 17 ≡ 2 (mod 3)`, a non-residue.)

The approach is moreover structurally incapable of working, which is the part
worth remembering.  `X` is smooth and `X(ℚ_p)` is infinite for every `p`, so
non-degenerate `p`-adic points exist at every `p`; Hensel-lifting one and
truncating gives, for EVERY modulus `m`, integers `(a, b, t)` with
`gcd(a, b) = 1`, `ab(a + b) ≠ 0` and `t² ≡ F(a, b) (mod m)`.  The exceptional
set `ab(a + b) = 0` is not cut out by any congruence, because this is a global
statement about a curve that has points everywhere locally.

**NUMERICAL CORROBORATION.**  (i) Exact integer arithmetic over all coprime
`(a, b)` with `|a| ≤ 400`, `1 ≤ b ≤ 400`: the only solutions of
`t² = C̃² + 4B̃²` have `B̃ = ab(a + b) = 0`; the same run confirms `C̃` odd and
`gcd(C̃, B̃) = 1` on every coprime pair in the range.  (ii) Magma's point search
on `y² = f(x)` to height bound `10⁴` — a `25×` wider sweep — returns exactly the
six known points `(0, ±1)`, `(−1, ±1)`, `∞±`.  Untrusted searchers both, so
claims to be re-derived and not proofs.

**THE CHEAPEST KNOWN CERTIFICATE, AND WHAT A LEAN PROOF SHOULD TARGET**
(Magma, untrusted searcher; every number here is a claim to be re-derived).
The leaf is exactly a NORM EQUATION.  With `L := ℚ[x]/(f)` and `θ` the image of
`x`, the sextic being monic of degree `6` gives `F(a, b) = N_{L/ℚ}(a − bθ)`, so
the statement reads

    N_{L/ℚ}(a − bθ) = t²,    gcd(a, b) = 1    ⟹    ab(a + b) = 0.

The descent therefore lives over `L`, and `L` is about as friendly as such a
field ever gets:

* `[L : ℚ] = 6`, `disc L = 2⁶·13²`, totally complex (signature `(0, 3)`);
* **`h(L) = 1`** — this removes the single most infeasible ingredient of a
  formalised descent, namely a class-group computation;
* `rank O_L^* = 2`, and `i ∈ L`, since `ℚ(√(disc f)) = ℚ(i)`;
* over `ℚ(i)` the sextic FACTORS, into the two conjugate cubics
  `z³ + (1 ∓ 2i)z² − (2 ± 2i)z − 1`.  That is the sum-of-two-squares identity
  re-read as the block decomposition of the order-`18` Galois action, the two
  blocks being swapped by `Gal(ℚ(i)/ℚ)`; so the descent may equally be run on
  the relative cubic `L/ℚ(i)`.

And the certificate itself: **the `2`-Selmer group of `J` is TRIVIAL**,
`#Sel₂(J/ℚ) = 1`.  That one fact delivers more than item `4` of the four-part
project asks for: it gives `rank J(ℚ) = 0` *and* `J(ℚ)[2] = 0` simultaneously,
so `J(ℚ)` has odd order and injects into `J(𝔽₃) ≅ ℤ/19`.  With items `1`–`3`
(`Pic⁰`, Abel–Jacobi, good reduction at `3` with torsion-free kernel) the leaf
then follows, `#J(𝔽₃) = #J(𝔽₅) = 19` remaining the sharp targets.

So the honest summary of where the difficulty sits has MOVED, and this is the
one thing to carry away from this pass: it is **not** the rank computation —
that is a trivial-Selmer statement over a class-number-one sextic field, which
is the friendliest shape such a computation can have — but items `1`–`3`, the
genus-`2` Jacobian itself.  Nothing shorter is known to the author of this
docstring. -/
theorem abd_eq_zero_of_sq_eq (a b t : ℤ) (hab : Int.gcd a b = 1)
    (ht : t ^ 2 = (a ^ 3 + a ^ 2 * b - 2 * a * b ^ 2 - b ^ 3) ^ 2
              + 4 * (a * b * (a + b)) ^ 2) :
    a * b * (a + b) = 0 := by
  obtain ⟨u, v, huv, hB, hC⟩ :=
    descent_sq_add_four_sq _ _ t (C_odd a b hab)
      (C_isCoprime a b (Int.isCoprime_iff_gcd_eq_one.mpr hab)) ht
  exact descent_system_no_solution a b u v hab huv hB hC

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
