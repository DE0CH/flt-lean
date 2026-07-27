/-
ModularCurve/HyperellipticJacobian.lean — own work for the Fermat project (not
vendored from the FLT project).

# Genus-`2` hyperelliptic curves, their integral models, and the Jacobian layer

This module supplies the layer demanded by
`MazurLevel18.no_noncuspidal_point_on_smooth_model` and its level-`13`
counterpart in `Fermat/FLT/FreyCurve/MazurTorsion.lean`, namely the objects that
the rank-`0` proofs of

    y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1      (`X_1(18)`)
    y² = x⁶ + 2x⁵ +  x⁴ +  2x³ + 6x² + 4x + 1      (`X_1(13)`)

have only cuspidal `ℚ`-points quantify over, and which exist neither in mathlib
at this pin nor in `~/cs/FLT`.  Four pieces are needed at each level:

1. hyperelliptic curves of genus `2` and their Jacobians as `Pic⁰`, with the
   Mumford representation and Cantor's group law;
2. the Abel–Jacobi embedding `X ↪ J` from a rational base point;
3. good reduction `J(ℚ) → J(𝔽ₚ)` and injectivity on prime-to-`p` torsion;
4. `rank J(ℚ) = 0`.

## ROUTE 2, adopted 2026-07-27: the file now runs in the direction the
mathematics does

Until 2026-07-27 the two namespaces derived everything from an integral
Diophantine leaf reached by an imaginary-quadratic descent (`ℤ[√−2]` at level
`18`, `ℤ[i]` at level `13`), whose proposed closing move was Bruin's elliptic
Chabauty over the quadratic field.  **That route was refuted three times over
and has been RETIRED**, together with the whole descent development: the odd
degree of the cubic makes the required bound on the denominator modulo squares
unobtainable, the sextic has exactly one proper subfield so no better splitting
is available, and the twists actually reachable include members of sharp rank
`2 = [K : ℚ]`, where elliptic Chabauty does not apply at all.  The three
findings, each with the check that would refute it, are on
`X18.exists_jacobianPackage`; the retired text — some 1400 lines of proven,
axiom-clean descent material, all of it still true and none of it useful for
this purpose — is recoverable with

    git show ade8359a:Fermat/FLT/ModularCurve/HyperellipticJacobian.lean

**Do not rebuild toward elliptic Chabauty.**

What replaced it is the classical argument, which is what Magma's `Chabauty0`
on a rank-`0` Jacobian *is* — the Mazur–Tate decision procedure, involving no
covering collection.  Each namespace now reads top-down:

    exists_jacobianPackage        LEAF: Pic⁰, rank 0, torsion-free reduction kernel
      → affine_rational_points    `X(ℚ)` has exactly four affine points
      → exists_eq_sixPts          `X(ℚ)` is exactly the six cusps
      → redPt_injective_five/three  reduction is injective, via the explicit table
      → no_noncuspidal_point      the export consumed by `MazurTorsion.lean`

## What is BUILT here, and what remains

Everything except the existence of the Jacobian is real code, and the two
arithmetic inputs that people usually hand-wave are discharged by the kernel:

* `Pt` — the `R`-points of the smooth projective model of a monic sextic, in the
  weighted projective space `ℙ(1, 3, 1)`.  The leading coefficient is `1`, a
  square, so there are exactly **two** points at infinity; the type is therefore
  `AffPt ⊕ Bool` and that is a theorem about `ℙ(1,3,1)`, not a modelling choice:
  a point with `Z = 0` satisfies `Y² = X⁶` with `X ≠ 0`, so after normalising
  `X = 1` it is `Y = ±1`.
* `exists_int_coords` (PROVEN) — every rational point has integral weighted
  projective coordinates `[a : t : b]` with `b = x.den`, `a = x.num` coprime,
  and `t = y·b³` an INTEGER.  Integrality of `t` is the one non-formal step:
  `t² = F(a, b) ∈ ℤ` and `ℤ` is integrally closed in `ℚ`.
* `redPt` — the reduction map `X(ℚ) → X(𝔽ₚ)`, defined on those integral
  coordinates.  Coprimality of `(a, b)` is what makes it total.  This is the map
  item 3 is *about*, so it had to be constructed rather than postulated.
* `card_X18_F5` and `card_X13_F3` (both PROVEN BY `decide`) — `#X(𝔽₅) = 6` and
  `#X(𝔽₃) = 6`.  Mod `5`, Fermat's little theorem collapses the level-`18`
  sextic to `x² + 4x + 1`, whose values are squares exactly twice, giving `4`
  affine points plus the `2` at infinity.  These are the point counts the whole
  argument turns on, and they are machine-checked facts rather than citations.
* `sevenPts_injective` (PROVEN, both levels) — the six cusps together with any
  putative point of a non-cuspidal abscissa are seven pairwise-distinct points
  of `X(ℚ)`.  With the point count this is the `7 ≤ 6` contradiction.
* `ptData`, `redTriple_congr`, `redPt_inl`, `ptData_redTriple_of_ne`,
  `ptData_redPt_inl` (all PROVEN, all generic in the sextic and the prime) — the
  machinery that COMPUTES `redPt` at a concrete rational point.  `redPt` goes
  through `Classical.choose`, so its value is not directly reducible; the choice
  is pinned by injectivity of `ℤ → ℚ`, and comparing points through their raw
  data (`ptData`, which drops the `Subtype` proof) removes the motive failures
  that otherwise block every rewrite.
* `red_sixPts` and `sixPtsData_injective` (PROVEN, the latter by `decide`, both
  levels) — the six cusps reduce mod `5` (resp. `3`) to six DISTINCT points.
  With the point counts this says the cusps FILL `X(𝔽ₚ)` exactly, which is the
  machine-checked half of the `#J(𝔽ₚ) = #J(ℚ)` certificate.
* `redPt_injective` (PROVEN, generic) — the whole rank-`0` argument in three
  lines: `J(ℚ)` is finite, so every element is killed by `Nat.card J`; the
  kernel of reduction is torsion-free; hence the kernel is trivial; hence `aj`
  injective plus the compatibility square makes `redPt` injective.

**The two remaining leaves are `X18.exists_jacobianPackage` and
`X13.exists_jacobianPackage`**, one per level, of identical shape: they differ
only in the sextic and the prime, so ONE genus-`2` Jacobian development closes
both.  Read their docstrings for the Magma certificates (re-run from scratch
2026-07-27: rank `0` sharp at both levels, `J(ℚ)_tors ≅ ℤ/21` and `ℤ/19`,
`#J(𝔽₅) = 21`, `#J(𝔽₃) = #J(𝔽₅) = 19`, `Chabauty0` returning exactly six points
at each level) and for the refutation of route 1.

## HONEST ACCOUNTING for the 2026-07-27 inversion

The retired chain was a chain of EQUIVALENCES — its own audits said so at every
link — so reversing its direction MOVED the obligation and proved nothing new.
The leaf count went from three (`X18.descent_system_no_solution_pos` / `_neg`
and `X13.descent_system_no_solution_pos`) to two, and that drop is bookkeeping,
not mathematics: the level-`13` pair had already collapsed to one because
`−1 = i²` makes the two sign branches the same statement relabelled, while at
level `18` the corresponding swap sends `v² − 2u²` to `u² − 2v²` rather than to
`2u² − v²`, so its two branches are genuinely distinct — the two levels do NOT
collapse into each other.  What the inversion buys is that the surviving
obligation is now "Mordell–Weil and rank `0` for `J₁(18)` / `J₁(13)`", which has
a classical proof and a plug-in point in this file, instead of a sextic
Diophantine equation whose only proposed attack had been refuted.

**A caveat that must not be lost.**  `JacobianPackage` is stated as weakly as
`redPt_injective` needs, and it is therefore EQUIVALENT to the injectivity, not
stronger: it can be satisfied by the free `𝔽₂`-vector spaces on `X(ℚ)` and
`X(𝔽ₚ)` with `red = Finsupp.mapDomain redPt`, with no divisor classes, no group
law, no formal group and no Mordell–Weil, once that injectivity is known by any
means.  (The retired `nonempty_jacobianPackage_of_redPt_injective` proved
exactly this and is in the same recoverable commit.)  So closing a leaf by
exhibiting a *structure* would not be progress on abelian varieties; what
discharges it honestly is items 1–4, and the package is stated precisely so that
an honest `Pic⁰` slots in with no consumer changing.

| field | item |
|---|---|
| `J`, `addCommGroup` | 1 — `Pic⁰` of the curve, as a group |
| `aj`, `aj_injective` | 2 — Abel–Jacobi from a rational base point; injective because the genus is `2 ≥ 1` |
| `red`, `red_aj` | 3 — reduction is a group homomorphism compatible with `redPt` |
| `red_ker_torsionFree` | 3 — the kernel of reduction is the formal group over `ℤₚ`, torsion-free because `p > e + 1 = 2` |
| `fin` | 4 — Mordell–Weil plus `rank J(ℚ) = 0` |

**`card_coprime` is deliberately ABSENT.**  One might expect the package to
record `gcd(#J(ℚ), p) = 1` (here `21` and `5`, `19` and `3`).  It is not needed:
`red_ker_torsionFree` together with finiteness already gives injectivity,
because in a finite group every element is torsion.  The sharper input
`#J(𝔽ₚ) = #J(ℚ)` — reduction is an *isomorphism* — is therefore not required
either.  Stating only what is used keeps the leaves as weak as possible, which
is the direction that makes them easier to discharge.

## Generality

`sext`, `hsext`, `AffPt`, `Pt`, `exists_int_coords`, `redAff`, `redTriple`,
`redPt`, `ptData` and the reduction-computation lemmas are stated for an
arbitrary monic sextic `x⁶ + c₅x⁵ + c₄x⁴ + c₃x³ + c₂x² + c₁x + c₀` over `ℤ` and
an arbitrary prime `p`, so the layer is reusable for other genus-`2` modular
curves; only the two `JacobianPackage` instantiations and the per-level
computations are specific.  Nothing here assumes separability of the sextic —
that hypothesis belongs to the *truth* of the package's fields, not to the
definitions, and it is why the packages are stated at concrete sextics and
primes rather than universally.

Coordinated with `Fermat/FLT/ModularCurve/X0.lean`, which owns `J_0(N)` and
Mordell–Weil for the level family: that layer is scheme-theoretic and about
modular curves as moduli, this one is the concrete hyperelliptic model needed
for two explicit curves.  They meet at "the Jacobian is a finite group of rank
`0`", which is item 4 in both.
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
-- `IsCoprime` over `ℤ` and `Int.gcd`, used by `exists_int_coords` and by the
-- integral-coordinate machinery
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

/-- **THE LEAF AT LEVEL `18`: `Pic⁰(X_1(18))` exists, has rank `0`, and reduces
injectively at `5`.**  (Made the leaf on 2026-07-27, when the file's dependency
direction was inverted; see the ROUTE-2 section below.)

Unfolding `JacobianPackage`, the obligation is exactly the four-part project
that the module docstring and
`MazurLevel18.no_noncuspidal_point_on_smooth_model` both record, and nothing
else:

1. `Pic⁰` of the genus-`2` hyperelliptic curve `y² = f(x)`, with the Mumford
   representation and Cantor's group law — the group `J = J(ℚ)` and its
   counterpart `J(𝔽₅)`;
2. Abel–Jacobi `X(ℚ) → J` from a rational base point, INJECTIVE because the
   genus is `≥ 1`;
3. good reduction at `5`, the reduction homomorphism `J(ℚ) → J(𝔽₅)`, its
   compatibility with the concrete point map `redPt`, and torsion-freeness of
   its kernel — the kernel is the formal group over `ℤ₅`, torsion-free because
   `5 > e + 1 = 2`;
4. `rank J(ℚ) = 0`, which with Mordell–Weil is the field `fin : Finite J`.

Only FINITENESS of `J(ℚ)` is asked for, not its order: `redPt_injective` needs
nothing sharper, and `card_coprime` is deliberately absent for the reason given
on `JacobianPackage`.

## The arithmetic that makes the fields true (untrusted searchers, not proofs)

Magma, re-run from scratch on 2026-07-27 — the third independent run, and it
reproduces both earlier ones exactly:

    C : y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1
    Factorization(Discriminant(C)) = 2²³ · 3⁴      — so `5` is a good prime
    TorsionSubgroup(J)             = ℤ/21
    RankBound(J)                   = 0             — SHARP, not merely `≤ 1`
    #J(𝔽₅)                         = 21            — reduction at `5` is an ISO
    #C(𝔽₅)                         = 6             — matches `card_X18_F5`
    Chabauty0(J) = {(1 : ±1 : 0), (1 : ±1 : 1), (0 : ±1 : 1)}   — SIX points

`Chabauty0` on a rank-`0` Jacobian is **not** a point search: it is the
Mazur–Tate argument, a decision procedure returning a provably complete `C(ℚ)`,
and it involves no covering collection.  Independently, `S₂(Γ₁(18))` has one
newform orbit with `L(f, 1) ≈ 0.4103 − 0.0724i ≠ 0`, so Kolyvagin–Logachev
gives `rank J(ℚ) = 0` by a different route; the conductor of `J` is `324 = 18²`.

Refuting checks: `RankBound(J)` returning a positive lower bound overturns
item 4; `TorsionSubgroup(J) ≠ ℤ/21` or `#J(𝔽₅) ≠ 21` overturns the sharpness
claims; a seventh point from `Chabauty0` overturns the conclusion downstream.

## ROUTE 1 (elliptic Chabauty over `ℚ(√−2)`) IS DEAD — why this file no longer
carries it

Until 2026-07-27 this namespace derived everything from an integral Diophantine
leaf `descent_system_no_solution_pos` / `_neg`, reached by a `ℤ[√−2]` descent,
and the route proposed for closing it was Bruin's elliptic Chabauty over
`K = ℚ(√−2)`.  That route was refuted three times over, and the whole chain has
been RETIRED; recover it with
`git show ade8359a:Fermat/FLT/ModularCurve/HyperellipticJacobian.lean`.  The
three findings, each with the check that would refute it:

1. *No bound on `b` modulo squares is obtainable.*  `F` has ODD degree, so
   `ord_𝔭(g(a/b)) = −3·ord_p(b)` has the parity of `ord_p(b)` and the usual
   "even outside the discriminant" argument fails at the pole.  No local
   condition bites either: for `p ∣ b`, `F(a, b) ≡ a³ (mod p)` is a unit by
   `gcd(a, b) = 1`.  Magma's `TwoCoverDescent` returns a FAKE 2-Selmer set — it
   lands in `L*/L*²·ℚ*`, modulo the very `ℚ*` that would have to be bounded.
   Structurally unavoidable: `F` cubic means `(a, b) ↦ (λa, λb)` scales it by
   `λ³ ≡ λ` mod squares.  *Refuting check*: exhibit a valuation or local
   argument forcing `ord_p(b)` even.
2. *No re-choice of splitting field removes it.*  An EVEN-degree factor would
   kill the `b`-dependence, and none exists: PARI `nfsubfields` reports that
   `L = ℚ[x]/(f)` has exactly ONE proper subfield, `K = ℚ(√−2)` (returned as
   `x² − 2x + 33`, discriminant `−128`), and `polgalois(f) = [18, −1, 1,
   "3 wr 2"]`.  So `f = g·ḡ` into two CUBICS is the only subfield
   factorisation there is.  *Refuting check*: exhibit a subfield of `L` other
   than `ℚ`, `K`, `L`.
3. *Elliptic Chabauty is INAPPLICABLE at some members of the family.*  It needs
   `rank E⁽ᵈ⁾(K) < [K : ℚ] = 2`, and Magma `RankBounds` on the twists
   `E⁽ᵈ⁾ : Y² = X³ + d(2√−2 − 2)X² − d²(2√−2 + 1)X + d³` over `K` gives SHARP
   rank `2` at `d = 11` and `d = 55`, both admissible values of `b`.  The two
   runs that were ever on record, `d = 1` and `d = 2`, cover exactly
   `b ∈ ℚ*²` and `b ∈ 2ℚ*²` and nothing else.  *Refuting check*: re-run
   `RankBounds` at `d = 11`; anything `≤ 1` restores that member.

**Do not rebuild toward elliptic Chabauty**, and do not re-open the `ℤ[√−2]`
descent expecting it to help: the descent itself is sound and reversible, and
that is precisely why it cannot reduce anything.

## HONEST ACCOUNTING: this is a RELOCATION of the sorry, not a reduction

Every step of the retired chain was an EQUIVALENCE — its own audits said so at
each link — so inverting the direction moved the obligation without proving
anything new.  What it bought is that the obligation now sits where the known
proof attaches: "Mordell–Weil and rank `0` for `J₁(18)`" instead of "one more
sextic Diophantine equation with no available attack".  The count at this level
went from two open leaves (`_pos`, `_neg`) to one.

**The one caveat a future prover must know.**  This statement is EQUIVALENT to
`redPt_injective_five` below, not stronger: a `JacobianPackage` can be built out
of nothing but that injectivity, taking `J` and `J'` to be the free `𝔽₂`-vector
spaces on `X(ℚ)` and `X(𝔽₅)` with `red = Finsupp.mapDomain redPt` (the retired
`nonempty_jacobianPackage_of_redPt_injective`, in the same recoverable commit).
So closing this leaf by exhibiting a *structure* is not by itself progress on
abelian varieties; what discharges it honestly is items 1–4, and the package is
stated exactly so that an honest `Pic⁰` slots in with no consumer changing. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 (-2) 5 (-10) 10 (-4) 5) := sorry

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

/-- **The affine rational points of `X_1(18)` are its four finite cusps**
(PROVEN from `exists_jacobianPackage`).

`X(ℚ) ↪ X(𝔽₅)` by `redPt_injective`, and `#X(𝔽₅) = 6` by `card_X18_F5`; a
rational point with `x ∉ {0, 1}` would be a SEVENTH point of `X(ℚ)` alongside
the six cusps (`sevenPts_injective`), and `7 ≤ 6` is false.  So `x ∈ {0, 1}`,
where the sextic takes the value `1`, whence `y² = 1` and `y = ±1`.

This is the direction that used to be an open Diophantine problem and is now a
five-line consequence of rank `0`.  Until 2026-07-27 the file ran the other way
— this statement was derived from `abd_eq_zero_of_sq_eq` and a `ℤ[√−2]` descent,
with the sorry at the bottom of that chain — and the inversion is the whole of
the ROUTE-2 repair; see `exists_jacobianPackage` above.

It asserts that a genus-`2` curve has exactly four affine rational points, which
is TRUE, `X_1(18)(ℚ)` being its six cusps; classically, no elliptic curve over
`ℚ` has a rational point of order `18`. -/
theorem affine_rational_points (x y : ℚ)
    (h : y ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) x) :
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) := by
  obtain ⟨D⟩ := exists_jacobianPackage
  have hx : x = 0 ∨ x = 1 := by
    by_contra hcon
    have hx0 : x ≠ 0 := fun h0 => hcon (Or.inl h0)
    have hx1 : x ≠ 1 := fun h1 => hcon (Or.inr h1)
    have hcard : Fintype.card (Fin 7)
        ≤ Fintype.card (Pt 1 (-2) 5 (-10) 10 (-4) (ZMod 5)) :=
      Fintype.card_le_of_injective _
        ((redPt_injective D).comp (sevenPts_injective x y h hx0 hx1))
    rw [Fintype.card_fin, card_X18_F5] at hcard
    omega
  rw [sext18] at h
  have hy : (y - 1) * (y + 1) = 0 := by
    rcases hx with rfl | rfl <;> linear_combination h
  rcases hx with rfl | rfl
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inl ⟨rfl, by linear_combination h1⟩
    · exact Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩)
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linear_combination h1⟩))

/-- **Every rational point is one of the six cusps** (PROVEN).
The affine case is `affine_rational_points`; the two infinite points are the
`Bool` summand of `Pt`, which is exhaustive by construction.

This is the Lean form of Magma's `Chabauty0(J)` output — a provably complete
`X(ℚ)`, not a point search — recorded on `exists_jacobianPackage` above. -/
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
`exists_eq_sixPts`).

`redPt_injective exists_jacobianPackage.some` proves this abstractly in one
line; the concrete derivation is kept and is the one `no_noncuspidal_point`
consumes, because it goes through the explicit reduction TABLE — both points are
cusps (`exists_eq_sixPts`), their reductions mod `5` are computed by
`red_sixPts`, and the six values are pairwise distinct by
`sixPtsData_injective`.  That table, together with `card_X18_F5`, is the
machine-checked half of the rank-`0` certificate: it says the six cusps FILL
`X(𝔽₅)`, which is what makes `#J(𝔽₅) = #J(ℚ) = 21` the sharp statement it is.
Keeping it in the root cone is deliberate. -/
theorem redPt_injective_five :
    Function.Injective (redPt 1 (-2) 5 (-10) 10 (-4) (p := 5)) := by
  intro P Q hPQ
  obtain ⟨i, rfl⟩ := exists_eq_sixPts P
  obtain ⟨j, rfl⟩ := exists_eq_sixPts Q
  have hdata : sixPtsData i = sixPtsData j := by
    rw [← red_sixPts i, ← red_sixPts j, hPQ]
  rw [sixPtsData_injective hdata]

/-- **`X_1(18)` has no non-cuspidal rational point on its smooth model**
(PROVEN modulo `exists_jacobianPackage`).

`X(ℚ) ↪ X(𝔽₅)` by `redPt_injective_five`, and `#X(𝔽₅) = 6`; but a rational
point with `x ∉ {0, 1}` would be a seventh point of `X(ℚ)` alongside the six
cusps.  `7 ≤ 6` is the contradiction.  No Chabauty and no Mordell–Weil sieve:
only rank `0` and one point count. -/
theorem no_noncuspidal_point (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hxy : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) :
    False := by
  have hq : y ^ 2 = sext 1 (-2) 5 (-10) 10 (-4) x := by rw [sext18]; exact hxy
  have hcard : Fintype.card (Fin 7)
      ≤ Fintype.card (Pt 1 (-2) 5 (-10) 10 (-4) (ZMod 5)) :=
    Fintype.card_le_of_injective _
      (redPt_injective_five.comp (sevenPts_injective x y hq hx0 hx1))
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

/-- **THE LEAF AT LEVEL `13`: `Pic⁰(X_1(13))` exists, has rank `0`, and reduces
injectively at `3`.**  (Made the leaf on 2026-07-27, by the same inversion as at
level `18`; the RECOMMENDED RE-CUT that the retired level-`13` audit asked for
and could not perform from inside the leaf.)

Unfolding `JacobianPackage`, the obligation is the four-part project of the
module docstring, at `p = 3` instead of `p = 5`:

1. `Pic⁰` of `y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`, with the Mumford
   representation and Cantor's group law — `J = J(ℚ)` and `J(𝔽₃)`;
2. Abel–Jacobi from a rational base point (`(0, 1)` will do), injective because
   the genus is `≥ 1`;
3. good reduction at `3`, the reduction homomorphism and its compatibility with
   `redPt`, with torsion-free kernel — the formal group over `ℤ₃`;
4. `rank J(ℚ) = 0`, i.e. `Finite J`.

## The arithmetic that makes the fields true (untrusted searchers, not proofs)

Magma, re-run from scratch on 2026-07-27, reproducing the earlier runs exactly:

    C : y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1
    Factorization(Discriminant(C)) = 2²⁰ · 13²     — so `3` is a good prime
    TorsionSubgroup(J)             = ℤ/19
    RankBound(J)                   = 0             — SHARP
    #J(𝔽₃) = #J(𝔽₅)                = 19            — reduction at `3` is an ISO
    #C(𝔽₃)                         = 6             — matches `card_X13_F3`
    Chabauty0(J) = {(1 : ±1 : 0), (−1 : ±1 : 1), (0 : ±1 : 1)}   — SIX points

`#J(𝔽₃) = 19 = #J(ℚ)` is why the argument is sharp here: reduction on the
Jacobian is an isomorphism, so injectivity is not merely available but forced.
`p = 5` gives the same certificate independently, which is a second check on
item 3.  PARI corroborates the point count through the zeta numerator:
`hyperellcharpoly(Mod(1,3)*f) = T⁴ + 2T³ + T² + 6T + 9`, whose `T³` coefficient
gives `#C(𝔽₃) = 3 + 1 + 2 = 6` and whose value at `1` gives `#J(𝔽₃) = 19`.

Refuting checks: a positive lower bound from `RankBound(J)`; a torsion subgroup
other than `ℤ/19`; `#Jacobian(ChangeRing(C, GF(3))) ≠ 19`; a seventh point from
`Chabauty0`.

## ROUTE 1 (elliptic Chabauty over `ℚ(i)`) IS DEAD HERE TOO

The retired chain descended through `ℤ[i]` — `f = (x³ + x² − 2x − 1)² +
4(x² + x)²` is the principal form of discriminant `−16` — to an integral leaf
`descent_system_no_solution_pos`, and proposed elliptic Chabauty over
`K = ℚ(i)`.  The obstruction is the same as at level `18` and is recorded in
full there: the homogenisation identity `g(a/b) = F(a, b)/b³` puts a solution on
the QUADRATIC TWIST BY `b`, not on `E`, so the route needs a covering
collection — a bound on `b` modulo `K*²` — which the odd degree of `F` makes
unobtainable, which no re-choice of splitting field removes, and which Chabauty
could not exploit anyway at the members where the twist has rank `≥ [K : ℚ]`.
The whole development is retired; recover it with
`git show ade8359a:Fermat/FLT/ModularCurve/HyperellipticJacobian.lean`.

Two structural facts from that development are worth keeping, because they are
about the CURVES and remain true:

* the two sign branches at level `13` are the SAME statement relabelled —
  `−(v − u·i)² = (u + v·i)²`, so `(u, v) ↦ (v, u)` carries one to the other.
  At level `18` they are NOT: the swap sends `v² − 2u²` to `u² − 2v²`, not to
  `2u² − v²`, because `−1` is not a square in `ℚ(√−2)`.  The two levels do not
  collapse into each other, and `M(a, b) = (b, b − a)` flips both level-`18`
  semi-invariants but moves the region, with exactly one representative per
  orbit in `{0 < a < b}` — so neither level-`18` branch reduces to the other;
* `J_1(13)` is `ℚ`-simple of `GL₂`-type with non-rational coefficient field
  (the `ℤ[ζ₃]`-action coming from the diamond `⟨5⟩`, an order-`3` automorphism
  `σ(x, y) = (−1/(x + 1), y/(x + 1)³)` cycling `0 ↦ −1 ↦ ∞ ↦ 0`), hence NOT
  isogenous to a product of elliptic curves over `ℚ`.  So no route through
  elliptic curves of rank `0` over `ℚ` exists, and item 1 really does have to be
  a genus-`2` Jacobian.

## HONEST ACCOUNTING

As at level `18`, the inversion RELOCATES the sorry rather than reducing it —
every link of the retired chain was an equivalence, which is exactly why the
count never moved along it.  The gain is that the residual obligation is now
"Mordell–Weil and rank `0` for `J₁(13)`", which has a classical proof
(Mazur–Tate, *Points of order 13 on elliptic curves*, Invent. Math. 22 (1973);
subsumed in Mazur, IHÉS 47 (1977), Thm 7), rather than a sextic Diophantine
equation with no available attack.  The same caveat applies: this is EQUIVALENT
to `redPt_injective_three`, so exhibiting a *structure* is not by itself
progress on abelian varieties — items 1–4 are.

**One genus-`2` Jacobian development discharges both levels**, since this leaf
and `X18.exists_jacobianPackage` have the identical shape and differ only in the
sextic and the prime. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 4 6 2 1 2 3) := sorry

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

/-- **The affine rational points of `X_1(13)` are its four finite cusps**
(PROVEN from `exists_jacobianPackage`).

Identical to the level-`18` argument at the prime `3`: `X(ℚ) ↪ X(𝔽₃)` by
`redPt_injective`, `#X(𝔽₃) = 6` by `card_X13_F3`, and a rational point with
`x ∉ {0, −1}` would be a seventh point of `X(ℚ)` (`sevenPts_injective`),
contradicting `7 ≤ 6`.  At `x ∈ {0, −1}` the sextic takes the value `1`, so
`y² = 1`.

Until 2026-07-27 this was derived from `abd_eq_zero_of_sq_eq` and a `ℤ[i]`
descent, with the sorry at the bottom of that chain; the inversion is the
ROUTE-2 repair described on `exists_jacobianPackage` above.

Classically: no elliptic curve over `ℚ` has a rational point of order `13`. -/
theorem affine_rational_points (x y : ℚ)
    (h : y ^ 2 = sext 1 4 6 2 1 2 x) :
    (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = -1 ∧ y = 1) ∨ (x = -1 ∧ y = -1) := by
  obtain ⟨D⟩ := exists_jacobianPackage
  have hx : x = 0 ∨ x = -1 := by
    by_contra hcon
    have hx0 : x ≠ 0 := fun h0 => hcon (Or.inl h0)
    have hx1 : x ≠ -1 := fun h1 => hcon (Or.inr h1)
    have hcard : Fintype.card (Fin 7) ≤ Fintype.card (Pt 1 4 6 2 1 2 (ZMod 3)) :=
      Fintype.card_le_of_injective _
        ((redPt_injective D).comp (sevenPts_injective x y h hx0 hx1))
    rw [Fintype.card_fin, card_X13_F3] at hcard
    omega
  rw [sext13] at h
  have hy : (y - 1) * (y + 1) = 0 := by
    rcases hx with rfl | rfl <;> linear_combination h
  rcases hx with rfl | rfl
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inl ⟨rfl, by linear_combination h1⟩
    · exact Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩)
  · rcases mul_eq_zero.mp hy with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linear_combination h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linear_combination h1⟩))

/-- **Every rational point is one of the six cusps** (PROVEN).
The affine case is `affine_rational_points`; the two infinite points are the
`Bool` summand of `Pt`, which is exhaustive by construction.

This is the Lean form of Magma's `Chabauty0(J)` output at level `13` — a
provably complete `X(ℚ)`, not a point search. -/
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
`exists_eq_sixPts`).

As at level `18`: `redPt_injective exists_jacobianPackage.some` gives this
abstractly, and the concrete derivation through the explicit reduction table
(`red_sixPts`, `sixPtsData_injective`) is the one kept and consumed, because
with `card_X13_F3` it says the six cusps FILL `X(𝔽₃)` — the machine-checked half
of the `#J(𝔽₃) = #J(ℚ) = 19` certificate. -/
theorem redPt_injective_three :
    Function.Injective (redPt 1 4 6 2 1 2 (p := 3)) := by
  intro P Q hPQ
  obtain ⟨i, rfl⟩ := exists_eq_sixPts P
  obtain ⟨j, rfl⟩ := exists_eq_sixPts Q
  have hdata : sixPtsData i = sixPtsData j := by
    rw [← red_sixPts i, ← red_sixPts j, hPQ]
  rw [sixPtsData_injective hdata]

/-- **`X_1(13)` has no non-cuspidal rational point on its smooth model**
(PROVEN modulo `exists_jacobianPackage`).

`X(ℚ) ↪ X(𝔽₃)` by `redPt_injective_three`, and `#X(𝔽₃) = 6`; but a rational
point with `x ∉ {0, −1}` would be a seventh point of `X(ℚ)` alongside the six
cusps.  `7 ≤ 6` is the contradiction.  No Chabauty and no Mordell–Weil sieve:
only rank `0` and one point count. -/
theorem no_noncuspidal_point (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ -1)
    (hxy : y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1) :
    False := by
  have hq : y ^ 2 = sext 1 4 6 2 1 2 x := by rw [sext13]; exact hxy
  have hcard : Fintype.card (Fin 7)
      ≤ Fintype.card (Pt 1 4 6 2 1 2 (ZMod 3)) :=
    Fintype.card_le_of_injective _
      (redPt_injective_three.comp (sevenPts_injective x y hq hx0 hx1))
  rw [Fintype.card_fin, card_X13_F3] at hcard
  omega

end X13

end Hyperelliptic

end Fermat