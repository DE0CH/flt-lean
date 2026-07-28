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

      → exists_functionFieldData  PROVEN: the function field K(x)[y]/(y²−f), as AdjoinRoot
    finite_isPlaceFun             LEAF: a nonzero function has finitely many zeros/poles
      → exists_placeSystem        PROVEN: the TAUTOLOGICAL system; ord_complete is rfl
    exists_isPlaceFun_of_affPt    LEAF: the valuation of an affine rational point
    exists_isPlaceFun_of_infPt    LEAF: the valuation of a branch at infinity
      → exists_isPlaceOfPt        PROVEN: from the two, through ord_complete
      → exists_placeData          PROVEN: assembled, with pt_injective proven
    finrank_residue_pt_eq_one     LEAF: κ(v) = K at the place of a rational point
    degOf_divisor_eq_zero         LEAF: Σ_v ord_v(g)·[κ(v):K] = 0  (Stichtenoth I.4.11)
      → exists_degreeMap          PROVEN: assembled over the constructed `degOf`
    isRationalGenerator_of_divisor_eq_sub_single
                                  LEAF: a single simple pole forces F = K(g)
    not_isRationalGenerator       LEAF: F is NOT rational — the genus, and the only
                                  place where separability does any work
      → sub_single_pt_notMem_princ PROVEN: assembled, over `princ = range divisor`
      → aj_injective_of_separable PROVEN: assembled
    exists_reductionFiltration    LEAF: red together with the formal-group filtration
      → exists_reduction          PROVEN: torsion-freeness from the filtration
    X18.finite_pic / X13.finite_pic  LEAF: Mordell–Weil and rank 0, one per curve
      → exists_jacobianPackage    PROVEN: the four obligations assembled
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

**The remaining leaves are the eight listed in the tree above** (amended 2026-07-28, when
the three generic obligations were themselves decomposed; the earlier amendment of
2026-07-27 decomposed and PROVED `exists_jacobianPackage`).  Six of them —
`finite_isPlaceFun`, `exists_isPlaceFun_of_affPt`, `exists_isPlaceFun_of_infPt`,
`exists_degreeMap`,
`sub_single_pt_notMem_princ`, `exists_reductionFiltration` — are generic in the sextic and
the prime, so ONE genus-`2` divisor-theory development closes them for both levels at once;
only `X18.finite_pic` and `X13.finite_pic`, which are Mordell–Weil together with
`rank J(ℚ) = 0`, are specific to the curves.  (The count rose from five to eight while
`exists_placeData`, `aj_injective_of_separable` and `exists_reduction` all became PROVEN:
that is decomposition, and with it the two arguments that used to be sketched only in prose
— `pt_injective` from the valuation axioms, and torsion-freeness from a formal-group
filtration — are now machine-checked.)  Read the
`finite_pic` docstrings for the Magma certificates (re-run from scratch 2026-07-27: rank
`0` sharp at both levels, `J(ℚ)_tors ≅ ℤ/21` and `ℤ/19`, `#J(𝔽₅) = 21`,
`#J(𝔽₃) = #J(𝔽₅) = 19`, `Chabauty0` returning exactly six points at each level) and the
`exists_jacobianPackage` docstrings for the refutation of route 1.

The smoothness of the two curves, `Separable` of the sextic over `ℚ` and over `𝔽ₚ` — which
over `𝔽ₚ` IS good reduction at `p` — is PROVEN at both levels by an explicit Bézout
certificate (`X18.separable_sextPoly`, `X13.separable_sextPoly`), in the same spirit as the
`decide`-checked point counts: `U·f + V·f' = 144` and `= 104` are identities over `ℤ`, so
`ring` checks them and they specialise to every field where the constant is invertible.

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

**A caveat that must not be lost — and how the 2026-07-27 decomposition answers it.**
`JacobianPackage` is stated as weakly as `redPt_injective` needs, and it is therefore
EQUIVALENT to the injectivity, not stronger: it can be satisfied by the free `𝔽₂`-vector
spaces on `X(ℚ)` and `X(𝔽ₚ)` with `red = Finsupp.mapDomain redPt`, with no divisor classes,
no group law, no formal group and no Mordell–Weil, once that injectivity is known by any
means.  (The retired `nonempty_jacobianPackage_of_redPt_injective` proved exactly this and
is in the same recoverable commit.)  So closing a leaf by exhibiting a *structure* would
not be progress on abelian varieties; what discharges it honestly is items 1–4, and the
package is stated precisely so that an honest `Pic⁰` slots in with no consumer changing.

That junk model is exactly why the package could not be decomposed field-by-field: any
split of "a structure with items 1–3 exists" from "such a structure satisfies item 4" is
either satisfied by the junk model or false for it.  The repair is to stop quantifying over
structures: `PlaceData` pins the divisor theory of the function field, `PlaceData.Pic` is
then a DEFINITION, and the four items become four statements about `Pic⁰` that no exhibited
structure can discharge.  `exists_jacobianPackage` is their assembly, and the `J` it
supplies is the honest `Pic⁰` — so the caveat now describes only what the interface
`JacobianPackage` would permit, not what this file does.

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
-- the divisor-theoretic `Pic⁰` layer of the `Picard` section: polynomials and their
-- derivatives (the sextic as a polynomial, and the separability certificates),
-- `Transcendental` (the pinning of the function field) and quotient groups
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.QuotientGroup.Basic
-- the degree homomorphism on divisors, `Finsupp.liftAddHom`
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
-- (restored at the release-12 integration: flt-lean-201's import-block hunk landed on top
-- of flt-lean-207's and dropped these three, every one of which 207's own proofs consume.)
public import Fermat.FLT.Mathlib.GroupTheory.Descent
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
-- the construction of the function field `K(x)[y]/(y² − f)` in `exists_functionFieldData`:
-- rational functions, root adjunction, the Kummer irreducibility criterion for `Yᵖ − a`,
-- integral closedness of a UFD (`K[X]` is integrally closed in `K(x)`), and `compute_degree`
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Tactic.ComputeDegree

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

section Picard

open Polynomial

/-!
## The honest `Pic⁰`, and the decomposition of `exists_jacobianPackage` (2026-07-27)

`JacobianPackage` existentially quantifies over a *structure*, and the caveat recorded on
it — and repeated on both `exists_jacobianPackage` docstrings — is that this makes
`Nonempty (JacobianPackage …)` EQUIVALENT to `redPt_injective` rather than stronger: the
free `𝔽₂`-vector spaces on `X(ℚ)` and `X(𝔽ₚ)` with `red = Finsupp.mapDomain redPt` satisfy
every field once that injectivity is known by any means.  A leaf with a junk model cannot
be honestly decomposed *by its fields*: any split into "a structure with items 1–3 exists"
plus "such a structure has property 4" is either satisfied by the junk model (so vacuous)
or false for it.  The content lives in the combination, not in the pieces.

The way out is the one this development has used before (`exists_x0Sieve`, and
`ModularCurve/RelativePicard.lean` for the scheme-theoretic Jacobian): **pin the object,
then cut**.  `PlaceData` below pins the divisor theory of the hyperelliptic function field,
and `PlaceData.Pic` is then a *definition*, not a field — so the four obligations of the
module docstring become four statements ABOUT `Pic⁰` that no exhibited structure can
discharge:

| obligation | statement | status |
|---|---|---|
| 1 | `exists_placeData` — the function field, its places, and the divisor theory exist | PROVEN 2026-07-28 from `exists_functionFieldData`, `exists_placeSystem`, `exists_isPlaceOfPt` |
| 2 | `aj_injective_of_separable` — Abel–Jacobi is injective, because the genus is `2 ≥ 1` | PROVEN 2026-07-28 from `exists_degreeMap`, `sub_single_pt_notMem_princ` |
| 3 | `exists_reduction` — good reduction: the homomorphism, its compatibility with `redPt`, and torsion-freeness of its kernel | PROVEN 2026-07-28 from `exists_reductionFiltration` |
| 4 | `X18.finite_pic`, `X13.finite_pic` — Mordell–Weil together with `rank J(ℚ) = 0` | LEAF |

and `X18.exists_jacobianPackage` / `X13.exists_jacobianPackage` become PROVEN assemblies.

**Obligation 4 was split again on 2026-07-28** and both `finite_pic` are now PROVEN too;
the `MordellWeil` section below separates the generic Mordell–Weil half (`fg_pic`, over
`exists_descentHeight_pic` and `finite_quotient_psmul_pic`) from the level-specific rank-`0`
half (`X18.two_divisible_pic`, `X13.two_divisible_pic`).  Note that the same
pin-then-cut argument applies there: `2`-divisibility is a statement ABOUT the defined
`Pic`, and no exhibited structure discharges it.

### Why `Pic` is `Pic⁰` although no degree map appears

`Pic` is `Div / (principal divisors + ℤ·[∞₊])`.  Since `deg [∞₊] = 1`, the degree map
splits `Pic(X) ≅ ℤ ⊕ Pic⁰(X)` with `[∞₊]` a generator of the `ℤ`, so quotienting by
`ℤ·[∞₊]` lands on `Pic⁰(X)` canonically.  That is what lets the whole layer be stated
without constructing residue fields and degrees — the degree theory is needed to PROVE the
leaves, not to STATE them.  And `X` has a rational point, so `Pic⁰(X_ℚ) = J(ℚ)`: the group
being asked to be finite really is the Mordell–Weil group.

### Why quantifying over an arbitrary `PlaceData` is safe

`aj_injective_of_separable`, `exists_reduction`, the two Mordell–Weil leaves and
`two_divisible_pic` are `∀`-quantified over
presentations, which is exactly the shape that made the naive field-wise cut unsound.  It
is sound here because the axioms **pin the presentation up to isomorphism**:

* `eqn`, `transcendental_xx` and `gen` say `(F, xx, yy)` IS the function field
  `K(x)[y]/(y² − f(x))`, so any two presentations are `K`-isomorphic by `xx ↦ xx'`,
  `yy ↦ yy'` (for a non-square `f`, which separability gives);
* `ord_injective` and `ord_complete` say `Places` is EXACTLY the set of normalised
  `K`-trivial discrete valuations of `F` — the closed points of the smooth projective
  model — so an isomorphism of function fields transports places bijectively;
* `ord_pt_affine` and `ord_pt_infinite` pin `pt` on the nose: a place with
  `ord (x − a) > 0` and `ord (y − b) > 0` is the point `(a, b)`, and the two places with
  `ord x = −1` are separated by the sign of `y/x³` at infinity (`−3 < ord (y ∓ x³)` holds
  for exactly one of them once `2 ≠ 0`, since `y/x³ → ±1` there).

Hence `Divisors`, `princ`, `picRel`, `Pic` and `aj` are carried along by any isomorphism of
presentations, and the three `∀`-statements are model-independent facts about the curve.

### What the axioms deliberately do NOT do

Nothing here constructs a place, computes a degree, or proves the degree formula
`deg (div g) = 0`; those are obligations of `exists_placeData` and of whoever proves
`aj_injective_of_separable`.  `PlaceData` is an interface, in the sense the doctrine names:
*stating* a theory is what makes the cut available, and is much weaker than proving it.
-/

/-- The monic sextic `x⁶ + c₅x⁵ + c₄x⁴ + c₃x³ + c₂x² + c₁x + c₀` as a POLYNOMIAL over `R`.

`sext` evaluates it at a point; this is the polynomial itself, needed to say
`Separable` — i.e. that the curve is smooth, which over `ZMod p` is exactly good
reduction at `p`. -/
noncomputable def sextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (R : Type*) [CommRing R] : R[X] :=
  X ^ 6 + (c₅ : R[X]) * X ^ 5 + (c₄ : R[X]) * X ^ 4 + (c₃ : R[X]) * X ^ 3
    + (c₂ : R[X]) * X ^ 2 + (c₁ : R[X]) * X + (c₀ : R[X])

/-- `sextPoly` evaluates to `sext` (PROVEN). -/
lemma eval_sextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [CommRing R] (x : R) :
    (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ R).eval x = sext c₀ c₁ c₂ c₃ c₄ c₅ x := by
  simp [sextPoly, sext]

/-- `sextPoly` evaluates to `sext` in any algebra (PROVEN).  This is the form the curve
equation takes inside the function field, where the abscissa is `xx : F` and the
coefficients arrive through `algebraMap K F`. -/
lemma aeval_sextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {K F : Type*} [CommRing K] [CommRing F]
    [Algebra K F] (x : F) :
    aeval x (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) = sext c₀ c₁ c₂ c₃ c₄ c₅ x := by
  simp [sextPoly, sext]

/-- **The divisor theory of the hyperelliptic curve `y² = sext x` over `K`.**

This is the interface that pins `Pic⁰`; see the section docstring above for why each group
of axioms is present and why quantifying over it is safe.  In one line: `F` is the function
field, `Places` is its set of normalised `K`-trivial discrete valuations — the closed points
of the smooth projective model — and `pt` is the place of a `K`-rational point.

Nothing about degrees, residue fields or Riemann–Roch appears: `Pic⁰` is obtained below as
`Div` modulo principal divisors and the class of the base point `∞₊`, which needs no degree
map because `deg [∞₊] = 1` splits `Pic ≅ ℤ ⊕ Pic⁰`.

The `Bool`-indexed conditions at infinity are the reason `2 ≠ 0` is a hypothesis of
`exists_placeData`: in characteristic `2` the two points at infinity of a monic sextic
collide and no injective `pt` exists. -/
structure PlaceData (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K] where
  /-- the function field `K(x)[y]/(y² − f(x))` -/
  F : Type
  [instField : Field F]
  [instAlgebra : Algebra K F]
  /-- the abscissa -/
  xx : F
  /-- the ordinate -/
  yy : F
  /-- the curve equation, in the function field -/
  eqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx
  /-- the abscissa is transcendental: the curve is a curve, not a point -/
  transcendental_xx : Transcendental K xx
  /-- `F = K(xx, yy)`: every element is `(a(xx) + b(xx)·yy)/d(xx)`.  With `eqn` and
  `transcendental_xx` this pins `F` as THE function field of the curve. -/
  gen : ∀ z : F, ∃ a b d : K[X], aeval xx d ≠ 0 ∧
      z * aeval xx d = aeval xx a + aeval xx b * yy
  /-- the places, i.e. the closed points of the smooth projective model -/
  Places : Type
  /-- the normalised order of vanishing at a place; `ord v 0 = 0` is a junk convention,
  which is why every axiom below carries a nonvanishing side condition -/
  ord : Places → F → ℤ
  ord_zero : ∀ v, ord v 0 = 0
  ord_mul : ∀ (v : Places) (a b : F), a ≠ 0 → b ≠ 0 → ord v (a * b) = ord v a + ord v b
  ord_add : ∀ (v : Places) (a b : F), a ≠ 0 → b ≠ 0 → a + b ≠ 0 →
      min (ord v a) (ord v b) ≤ ord v (a + b)
  ord_algebraMap : ∀ (v : Places) (a : K), a ≠ 0 → ord v (algebraMap K F a) = 0
  /-- each place is normalised: its value group is all of `ℤ` -/
  ord_surjective : ∀ v : Places, ∃ t : F, ord v t = 1
  /-- distinct places are distinct valuations -/
  ord_injective : Function.Injective ord
  /-- **and every valuation is a place** — this is the axiom that pins `Places`, and
  without it a presentation could omit points and make `Pic` anything at all -/
  ord_complete : ∀ o : F → ℤ, o 0 = 0 →
      (∀ a b : F, a ≠ 0 → b ≠ 0 → o (a * b) = o a + o b) →
      (∀ a b : F, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (o a) (o b) ≤ o (a + b)) →
      (∀ a : K, a ≠ 0 → o (algebraMap K F a) = 0) → (∃ t : F, o t = 1) →
      ∃ v, ord v = o
  /-- a nonzero function has finitely many zeros and poles; this is what makes `divisor`
  a finitely supported function, i.e. an honest divisor -/
  ord_finite : ∀ g : F, g ≠ 0 → {v : Places | ord v g ≠ 0}.Finite
  /-- the place of a `K`-rational point of the smooth model -/
  pt : Pt c₀ c₁ c₂ c₃ c₄ c₅ K → Places
  pt_injective : Function.Injective pt
  /-- an affine point is the place where `x − a` and `y − b` both vanish -/
  ord_pt_affine : ∀ q : AffPt c₀ c₁ c₂ c₃ c₄ c₅ K,
      0 < ord (pt (Sum.inl q)) (xx - algebraMap K F q.1.1) ∧
      0 < ord (pt (Sum.inl q)) (yy - algebraMap K F q.1.2)
  /-- an infinite point is a pole of `x` of order one, and the `Bool` is the sign of
  `y/x³` there: `ord (yy − ε·xx³) > −3` says `y/x³ − ε` vanishes, which holds for the
  matching sign and fails (with value exactly `−3`) for the other -/
  ord_pt_infinite : ∀ s : Bool,
      ord (pt (Sum.inr s)) xx = -1 ∧
      -3 < ord (pt (Sum.inr s)) (yy - (if s then 1 else -1) * xx ^ 3)

namespace PlaceData

attribute [instance] PlaceData.instField PlaceData.instAlgebra

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-- **Divisors**: finitely supported formal `ℤ`-combinations of places. -/
abbrev Divisors (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : Type := D.Places →₀ ℤ

open scoped Classical in
/-- **The divisor of a function**, `div g = Σ_v ord_v(g)·v`.  Finitely supported by
`ord_finite`; the value at `0` is junk (`0`), and is never used, `princ` being generated by
the divisors of all elements and `div 0 = 0` contributing nothing. -/
noncomputable def divisor (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) : D.Divisors :=
  if h : g = 0 then 0
  else Finsupp.onFinset (D.ord_finite g h).toFinset (fun v => D.ord v g)
    (fun v hv => by simpa using hv)

/-- **The subgroup of principal divisors.**  Taken as the subgroup GENERATED by the
divisors of functions, which is the same subgroup as their image — `divisor` is a
homomorphism by `ord_mul` — while needing no proof to be well defined. -/
noncomputable def princ (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : AddSubgroup D.Divisors :=
  AddSubgroup.closure (Set.range D.divisor)

/-- The base point `∞₊`, the point at infinity on the branch `y/x³ = 1`.

It is a rational point of degree `1`, which is what makes the quotient below `Pic⁰`, and
it is fixed by reduction (`redPt` is `Sum.inr` on the infinite summand by definition), which
is what makes `red_aj` a statement about the same base point on both sides. -/
def infPlus : Pt c₀ c₁ c₂ c₃ c₄ c₅ K := Sum.inr true

/-- Principal divisors together with the class of the base point.  Quotienting by this,
rather than restricting to degree `0`, is what removes the need for a degree map: `deg`
sends `[∞₊]` to `1`, so `Pic(X)/ℤ·[∞₊] ≅ Pic⁰(X)`. -/
noncomputable def picRel (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : AddSubgroup D.Divisors :=
  D.princ ⊔ AddSubgroup.zmultiples (Finsupp.single (D.pt infPlus) 1)

/-- **`Pic⁰` of the curve** — the Mordell–Weil group `J(K)` when `K` is a number field,
the curve having a rational point. -/
def Pic (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : Type := D.Divisors ⧸ D.picRel

noncomputable instance (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : AddCommGroup D.Pic :=
  inferInstanceAs (AddCommGroup (D.Divisors ⧸ D.picRel))

/-- **Abel–Jacobi**, `P ↦ [P] = [P − ∞₊]`.  The base point is invisible because the class
of `[∞₊]` has been quotiented away. -/
noncomputable def aj (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) :
    D.Pic :=
  QuotientAddGroup.mk (Finsupp.single (D.pt P) 1)

end PlaceData

/-!
### Obligation 1: the divisor theory of the hyperelliptic function field exists

For a separable monic sextic over a field in which `2 ≠ 0`, the curve `y² = f(x)` is a
smooth projective curve of genus `2`, and this asks for its function field together with
its places — that is, a `PlaceData`.  What has to be built:

* the function field `F = K(x)[y]/(y² − f(x))` (`AdjoinRoot` over `RatFunc K`, a field
  because `f` is not a square in `K(x)`, which separability gives);
* its places.  The finite ones are the height-one primes of the integral closure of `K[x]`
  in `F`, a Dedekind domain by `IsIntegralClosure.isDedekindDomain` (`F/K(x)` is separable
  because `2 ≠ 0`), with `ord` the `𝔭`-adic valuation; the two infinite ones come from the
  chart `u = 1/x`, `v = y/x³`, where the equation becomes `v² = u⁶f(1/u)` with constant
  term `1`, so that `v = ±1` are two rational points — this is the same fact about
  `ℙ(1, 3, 1)` that makes `Pt` a `Sum` with a `Bool`, seen valuation-theoretically;
* `ord_complete`: every `K`-trivial discrete valuation of a function field of one variable
  is one of these.  This is the standard classification (a valuation either restricts
  nontrivially to `K[x]`, giving a height-one prime, or is the one at infinity), and it is
  the axiom that makes the interface pin anything;
* `ord_finite`: a nonzero function has finitely many zeros and poles;
* `pt` and its two specifications, which are the evaluation places of rational points.

None of this needs Riemann–Roch, and none of it is specific to genus `2`.

## DECOMPOSED 2026-07-28 — see `exists_placeData` below, now PROVEN

The five bullets above are three genuinely different theories, and they became three
separate leaves: `exists_functionFieldData` (build `F`), `exists_placeSystem` (its places,
complete and normalised), `exists_isPlaceOfPt` (the evaluation place of a rational point).
The fourth obligation of the structure — `pt_injective`, that distinct rational points get
distinct places — is NOT a leaf: it is PROVEN below from the axioms, and it is the only
place in the whole layer where `2 ≠ 0` is used.

## LATER THE SAME DAY — all three of those are now PROVEN, and the third bullet is GONE

* `exists_functionFieldData` is **PROVEN**: `AdjoinRoot (Y² − f)` over `RatFunc K`, a field
  by Kummer's criterion once `f` is not a square, which is integral closedness of `K[X]`
  plus squarefreeness.  It does not use `2 ≠ 0`.
* `exists_placeSystem` is **PROVEN**, and the third bullet above — `ord_complete`, "the
  standard classification", advertised as the axiom that makes the interface pin anything —
  **is `rfl`**.  Take `Places` to be the set of ALL normalised `K`-trivial discrete
  valuations of `F` (`IsPlaceFun`) and `ord` to be `Subtype.val`; then every axiom of
  `PlaceSystem` except `ord_finite` is a projection.  Quantifying over all valuations is
  what made the interface honest, and it is also what makes the tautological model free.
  The residue is `finite_isPlaceFun` — the fourth bullet, finiteness of zeros and poles.
* `exists_isPlaceOfPt` is **PROVEN** from two sharper leaves that need only produce a
  valuation FUNCTION (`exists_isPlaceFun_of_affPt`, `exists_isPlaceFun_of_infPt`);
  `ord_complete` then turns it into a place of any given system.

So the fifth bullet's `pt` splits into "construct the valuation at a point", which is
Hensel in `K[[t]]` and nothing else.
-/

/-- **The function field of `y² = sext x` over `K`**, as data: the first block of
`PlaceData`'s fields, taken on its own so that building the field and finding its places
become separate obligations. -/
structure FunctionFieldData (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K] where
  /-- the function field `K(x)[y]/(y² − f(x))` -/
  F : Type
  [instField : Field F]
  [instAlgebra : Algebra K F]
  /-- the abscissa -/
  xx : F
  /-- the ordinate -/
  yy : F
  /-- the curve equation, in the function field -/
  eqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx
  /-- the abscissa is transcendental: the curve is a curve, not a point -/
  transcendental_xx : Transcendental K xx
  /-- `F = K(xx, yy)`; with `eqn` and `transcendental_xx` this pins `F` as THE function
  field of the curve -/
  gen : ∀ z : F, ∃ a b d : K[X], aeval xx d ≠ 0 ∧
      z * aeval xx d = aeval xx a + aeval xx b * yy

attribute [instance] FunctionFieldData.instField FunctionFieldData.instAlgebra

/-- **The places of `F/K`**: the closed points of the smooth projective model, as
normalised `K`-trivial discrete valuations.

This is the second block of `PlaceData`'s axioms, taken on its own so that it can be
demanded of a function field that has already been built.  `ord_complete` is what makes it
an honest pinning rather than a wish: together with `ord_injective` it says `Places` is
EXACTLY the set of such valuations, so any two systems on the same `F` are canonically
isomorphic and nothing quantified over them can be junk-satisfied. -/
structure PlaceSystem (K F : Type) [Field K] [Field F] [Algebra K F] where
  /-- the places, i.e. the closed points of the smooth projective model -/
  Places : Type
  /-- the normalised order of vanishing at a place; `ord v 0 = 0` is a junk convention -/
  ord : Places → F → ℤ
  ord_zero : ∀ v, ord v 0 = 0
  ord_mul : ∀ (v : Places) (a b : F), a ≠ 0 → b ≠ 0 → ord v (a * b) = ord v a + ord v b
  ord_add : ∀ (v : Places) (a b : F), a ≠ 0 → b ≠ 0 → a + b ≠ 0 →
      min (ord v a) (ord v b) ≤ ord v (a + b)
  ord_algebraMap : ∀ (v : Places) (a : K), a ≠ 0 → ord v (algebraMap K F a) = 0
  /-- each place is normalised: its value group is all of `ℤ` -/
  ord_surjective : ∀ v : Places, ∃ t : F, ord v t = 1
  /-- distinct places are distinct valuations -/
  ord_injective : Function.Injective ord
  /-- **and every valuation is a place** -/
  ord_complete : ∀ o : F → ℤ, o 0 = 0 →
      (∀ a b : F, a ≠ 0 → b ≠ 0 → o (a * b) = o a + o b) →
      (∀ a b : F, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (o a) (o b) ≤ o (a + b)) →
      (∀ a : K, a ≠ 0 → o (algebraMap K F a) = 0) → (∃ t : F, o t = 1) →
      ∃ v, ord v = o
  /-- a nonzero function has finitely many zeros and poles -/
  ord_finite : ∀ g : F, g ≠ 0 → {v : Places | ord v g ≠ 0}.Finite

namespace PlaceSystem

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- `ord v 1 = 0` (PROVEN): `1` is a nonzero constant. -/
lemma ord_one (S : PlaceSystem K F) (v : S.Places) : S.ord v 1 = 0 := by
  simpa using S.ord_algebraMap v 1 one_ne_zero

/-- `ord` is insensitive to sign (PROVEN): `−1` is a nonzero constant. -/
lemma ord_neg (S : PlaceSystem K F) (v : S.Places) (a : F) (ha : a ≠ 0) :
    S.ord v (-a) = S.ord v a := by
  have h : (-a) = algebraMap K F (-1) * a := by simp
  have hm : algebraMap K F (-1 : K) ≠ 0 := by simp
  rw [h, S.ord_mul v _ _ hm ha, S.ord_algebraMap v (-1) (by simp), zero_add]

/-- `ord v (aⁿ) = n · ord v a` (PROVEN). -/
lemma ord_pow (S : PlaceSystem K F) (v : S.Places) (a : F) (ha : a ≠ 0) (n : ℕ) :
    S.ord v (a ^ n) = n * S.ord v a := by
  induction n with
  | zero => simpa using S.ord_one v
  | succ m ih =>
    rw [pow_succ, S.ord_mul v _ _ (pow_ne_zero _ ha) ha, ih]
    push_cast
    ring

/-- The ultrametric inequality in subtractive form (PROVEN). -/
lemma ord_sub (S : PlaceSystem K F) (v : S.Places) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a - b ≠ 0) : min (S.ord v a) (S.ord v b) ≤ S.ord v (a - b) := by
  have h := S.ord_add v a (-b) ha (neg_ne_zero.mpr hb) (by simpa [sub_eq_add_neg] using hab)
  rwa [S.ord_neg v b hb, ← sub_eq_add_neg] at h

end PlaceSystem

/-- **`v` is the place of the rational point `P`** — the two specifications that `PlaceData`
imposes on `pt`, packaged so that they can be quantified over uniformly.

An affine point is the place where `x − a` and `y − b` both vanish; an infinite point is a
simple pole of `x`, and the `Bool` is the sign of `y/x³` there. -/
def IsPlaceOfPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (S : PlaceSystem K E.F)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) (v : S.Places) : Prop :=
  match P with
  | Sum.inl q => 0 < S.ord v (E.xx - algebraMap K E.F q.1.1) ∧
      0 < S.ord v (E.yy - algebraMap K E.F q.1.2)
  | Sum.inr s => S.ord v E.xx = -1 ∧
      -3 < S.ord v (E.yy - (if s then 1 else -1) * E.xx ^ 3)

/-- The sextic has degree `6` (PROVEN).  Used only to see that it is not a unit, which is
the last step of `not_isSquare_sextPoly`. -/
lemma natDegree_sextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K] :
    (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).natDegree = 6 := by
  unfold sextPoly
  compute_degree!

/-- **A squarefree non-unit of `K[X]` is not a square in `K(x)`** (PROVEN).

This is the one substantive step in building the function field.  If `b² = p` in `K(x)`
then `b` is a root of the MONIC polynomial `Y² − p` over `K[X]`, hence integral over
`K[X]`; `K[X]` is a UFD, so it is integrally closed in its fraction field `K(x)`, and `b`
is therefore a polynomial `q`.  Then `q² = p`, so `q · q ∣ p`, so squarefreeness makes `q`
— and hence `p = q²` — a unit, against the hypothesis.

Nothing here needs `2 ≠ 0`, and nothing needs the degree to be `6`. -/
lemma not_isSquare_sextPoly {K : Type} [Field K] {p : K[X]} (hsq : Squarefree p)
    (hu : ¬ IsUnit p) (b : RatFunc K) : b ^ 2 ≠ algebraMap K[X] (RatFunc K) p := by
  intro hb
  have hint : IsIntegral K[X] b := by
    refine ⟨X ^ 2 - C p, monic_X_pow_sub_C p (by norm_num), ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
    rw [hb, sub_self]
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hqp : q ^ 2 = p := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    rw [map_pow, hq, hb]
  have huq : IsUnit q := hsq q ⟨1, by rw [← hqp]; ring⟩
  exact hu (hqp ▸ huq.pow 2)

/-- **LEAF (obligation 1a), now PROVEN: the function field of the curve exists.**

`F = K(x)[y]/(y² − f(x))`, as `AdjoinRoot (Y² − C f)` over `RatFunc K`.  It is a field
because `f` is not a square in `K(x)`: a square in `K(x)` lying in `K[x]` is a square in
`K[x]` (`K[x]` is integrally closed in its fraction field), and a squarefree polynomial of
positive degree is not a square — separability gives squarefreeness.  That is
`not_isSquare_sextPoly`, and irreducibility of `Y² − f` is then Kummer's criterion
`X_pow_sub_C_irreducible_of_prime` at the prime `2`.

Then `xx` is the image of `RatFunc.X` and `yy` is `AdjoinRoot.root`; `eqn` is
`AdjoinRoot.eval₂_root`, `transcendental_xx` is transcendence of `X` in `K(x)`
(`RatFunc.transcendental_X`) transported along the injection `K(x) ↪ F`
(`transcendental_algebraMap_iff`), and `gen` is the two-term normal form `a + b·y` of
`AdjoinRoot` of a quadratic — obtained by reducing a representative modulo the monic
`Y² − f`, which leaves a polynomial of degree `≤ 1` — with denominators cleared through
`RatFunc.num_div_denom`.

Nothing here is specific to genus `2`, and nothing needs the places.

**`2 ≠ 0` IS NOT USED and is underscored.**  The hypothesis is kept because it is part of
the interface `exists_placeData` calls with, but the construction is characteristic-free:
in characteristic `2` the extension `F/K(x)` is inseparable, yet `F` is still a field and
`FunctionFieldData` demands nothing else.  Where `2 ≠ 0` really earns its keep in this
layer is `isPlaceOfPt_injective`, and only there. -/
theorem exists_functionFieldData (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K]
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (_h2 : (2 : K) ≠ 0) :
    Nonempty (FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) := by
  classical
  -- the sextic is squarefree and not a unit, hence not a square in `K(x)`
  have hsqf : Squarefree (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := hsep.squarefree
  have hnu : ¬ IsUnit (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    intro h
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [natDegree_sextPoly] at h1
    exact absurd h1 (by norm_num)
  set fK : RatFunc K := algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) with hfK
  set g : (RatFunc K)[X] := X ^ 2 - C fK with hg
  have hirr : Irreducible g := by
    rw [hg]
    exact X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_isSquare_sextPoly hsqf hnu)
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  have hmonic : g.Monic := by rw [hg]; exact monic_X_pow_sub_C fK (by norm_num)
  have hAinj : Function.Injective (algebraMap (RatFunc K) (AdjoinRoot g)) :=
    (algebraMap (RatFunc K) (AdjoinRoot g)).injective
  set xx : AdjoinRoot g := algebraMap (RatFunc K) (AdjoinRoot g) RatFunc.X with hxx
  set yy : AdjoinRoot g := AdjoinRoot.root g with hyy
  -- evaluation of a `K`-polynomial at `xx` is the composite of the two algebra maps
  have hcomp : ∀ a : K[X], (Polynomial.aeval xx a : AdjoinRoot g)
      = algebraMap (RatFunc K) (AdjoinRoot g) (algebraMap K[X] (RatFunc K) a) := by
    intro a
    have h1 : (Polynomial.aeval (RatFunc.X : RatFunc K) a) = algebraMap K[X] (RatFunc K) a := by
      have h2 : (Polynomial.aeval (RatFunc.X : RatFunc K) : K[X] →ₐ[K] RatFunc K)
          = IsScalarTower.toAlgHom K K[X] (RatFunc K) := by
        apply Polynomial.algHom_ext
        simp [RatFunc.algebraMap_X]
      exact congrArg (fun φ => φ a) h2
    rw [← h1, hxx, Polynomial.aeval_algebraMap_apply]
  -- the curve equation
  have heqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx := by
    have h0 : (X ^ 2 - C fK : (RatFunc K)[X]).eval₂ (AdjoinRoot.of g) (AdjoinRoot.root g) = 0 := by
      rw [← hg]; exact AdjoinRoot.eval₂_root g
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h0
    have h1 : (AdjoinRoot.root g) ^ 2 = AdjoinRoot.of g fK := by rwa [sub_eq_zero] at h0
    rw [hyy, h1, hfK, ← AdjoinRoot.algebraMap_eq, ← hcomp (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)]
    exact aeval_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ xx
  -- the abscissa is transcendental
  have htr : Transcendental K xx := by
    rw [hxx]
    exact (transcendental_algebraMap_iff hAinj).mpr RatFunc.transcendental_X
  -- the two-term normal form `(a + b·y)/d`
  have hgen : ∀ z : AdjoinRoot g, ∃ a b d : K[X], Polynomial.aeval xx d ≠ 0 ∧
      z * Polynomial.aeval xx d = Polynomial.aeval xx a + Polynomial.aeval xx b * yy := by
    intro z
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
    have hdvd : g ∣ q - q %ₘ g := by
      rw [Polynomial.modByMonic_eq_sub_mul_div q g]
      exact ⟨q /ₘ g, by ring⟩
    have hred : AdjoinRoot.mk g q = AdjoinRoot.mk g (q %ₘ g) := AdjoinRoot.mk_eq_mk.mpr hdvd
    have hdeg : (q %ₘ g).degree ≤ 1 := by
      have h3 := Polynomial.degree_modByMonic_lt q hmonic
      rw [hg, Polynomial.degree_X_pow_sub_C (by norm_num) fK] at h3
      exact Order.le_of_lt_succ (by exact_mod_cast h3)
    have hform := Polynomial.eq_X_add_C_of_degree_le_one hdeg
    have hz : AdjoinRoot.mk g q
        = algebraMap (RatFunc K) (AdjoinRoot g) ((q %ₘ g).coeff 0)
          + algebraMap (RatFunc K) (AdjoinRoot g) ((q %ₘ g).coeff 1) * yy := by
      rw [hred]
      conv_lhs => rw [hform]
      rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
        ← AdjoinRoot.algebraMap_eq, hyy]
      ring
    have hdu : (algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 0).denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero ((q %ₘ g).coeff 0).denom_ne_zero
    have hdv : (algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 1).denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero ((q %ₘ g).coeff 1).denom_ne_zero
    have hun : ((q %ₘ g).coeff 0) * algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 0).denom
        = algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 0).num := by
      have h := RatFunc.num_div_denom ((q %ₘ g).coeff 0)
      rw [div_eq_iff hdu] at h
      exact h.symm
    have hvn : ((q %ₘ g).coeff 1) * algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 1).denom
        = algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 1).num := by
      have h := RatFunc.num_div_denom ((q %ₘ g).coeff 1)
      rw [div_eq_iff hdv] at h
      exact h.symm
    refine ⟨((q %ₘ g).coeff 0).num * ((q %ₘ g).coeff 1).denom,
      ((q %ₘ g).coeff 1).num * ((q %ₘ g).coeff 0).denom,
      ((q %ₘ g).coeff 0).denom * ((q %ₘ g).coeff 1).denom, ?_, ?_⟩
    · rw [hcomp]
      refine fun hzero => RatFunc.algebraMap_ne_zero
        (mul_ne_zero ((q %ₘ g).coeff 0).denom_ne_zero ((q %ₘ g).coeff 1).denom_ne_zero)
        (hAinj ?_)
      rw [hzero, map_zero]
    · have e1 : ((q %ₘ g).coeff 0)
            * algebraMap K[X] (RatFunc K)
                (((q %ₘ g).coeff 0).denom * ((q %ₘ g).coeff 1).denom)
          = algebraMap K[X] (RatFunc K)
              (((q %ₘ g).coeff 0).num * ((q %ₘ g).coeff 1).denom) := by
        rw [map_mul, map_mul, ← mul_assoc, hun]
      have e2 : ((q %ₘ g).coeff 1)
            * algebraMap K[X] (RatFunc K)
                (((q %ₘ g).coeff 0).denom * ((q %ₘ g).coeff 1).denom)
          = algebraMap K[X] (RatFunc K)
              (((q %ₘ g).coeff 1).num * ((q %ₘ g).coeff 0).denom) := by
        rw [map_mul, map_mul, mul_comm (algebraMap K[X] (RatFunc K) ((q %ₘ g).coeff 0).denom),
          ← mul_assoc, hvn, mul_comm]
      rw [hz, hcomp, hcomp, hcomp, ← e1, ← e2]
      simp only [map_mul]
      ring
  exact ⟨{ F := AdjoinRoot g
           xx := xx
           yy := yy
           eqn := heqn
           transcendental_xx := htr
           gen := hgen }⟩

/-- **A normalised `K`-trivial discrete valuation of `F`, as a raw function.**

Exactly the five conditions that `PlaceSystem.ord_complete` quantifies over, packaged as a
predicate so that the SET of such valuations can be named and reasoned about.  (`o 0 = 0`
is the same junk convention as `ord_zero`, which is why every other clause carries a
nonvanishing side condition.) -/
structure IsPlaceFun (K F : Type) [Field K] [Field F] [Algebra K F] (o : F → ℤ) : Prop where
  /-- the junk value at `0` -/
  map_zero : o 0 = 0
  /-- multiplicativity on nonzero elements -/
  map_mul : ∀ a b : F, a ≠ 0 → b ≠ 0 → o (a * b) = o a + o b
  /-- the ultrametric inequality -/
  ultra : ∀ a b : F, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → min (o a) (o b) ≤ o (a + b)
  /-- triviality on the constants `K^×` -/
  map_algebraMap : ∀ a : K, a ≠ 0 → o (algebraMap K F a) = 0
  /-- normalisation: the value group is all of `ℤ` -/
  normalised : ∃ t : F, o t = 1

/-- **LEAF (obligation 1b, RESIDUE): a nonzero function has finitely many zeros and poles.**

## What happened to the rest of obligation 1b (2026-07-28)

The docstring this replaces said the mathematical heart of `exists_placeSystem` is
`ord_complete`, the classification of the `K`-trivial discrete valuations of a function
field of one variable, and that the finite places have to be produced as height-one primes
of the integral closure of `K[x]` in `F`.  **That is not so, and the reason is worth
recording: `PlaceSystem` quantifies over ALL such valuations, so the system whose `Places`
is literally the set of them satisfies `ord_complete` BY `rfl`.**  Taking

    Places := {o : F → ℤ // IsPlaceFun K F o},   ord := Subtype.val

makes `ord_zero`, `ord_mul`, `ord_add`, `ord_algebraMap` and `ord_surjective` the five
components of the subtype's own property, `ord_injective` the injectivity of `Subtype.val`,
and `ord_complete` the identity function.  No Dedekind domain, no integral closure, and no
classification is needed anywhere — the classification is exactly the content that
`ord_complete` was ASKING for, and asking for it as an axiom over the tautological system
is asking for nothing.

What does NOT come for free is `ord_finite`, and that is this leaf.  It is the honest
residue of obligation 1b: a nonzero `g ∈ F` is a nonunit at only finitely many places.

Route.  Let `n = [F : K(x)] = 2`.  The places with `o x < 0` are the ones above the place
at infinity of `K(x)`, and there are at most `n` of them (a place of `K(x)` has at most
`[F : K(x)]` extensions); at every other place `o` is `≥ 0` on `K[x]`, so `o` restricts to
a place of `K(x)` coming from a monic irreducible `π ∈ K[X]`, and `o g ≠ 0` forces `π` to
divide one of the two nonzero polynomials `N(g)`, `N(g)⁻¹`-denominators produced by
`E.gen`'s normal form `g = (a + b·y)/d` — finitely many `π`, each with at most `n`
extensions.  Stichtenoth, *Algebraic Function Fields and Codes*, I.3 (the finiteness of the
divisor of a function) and III.1 (at most `[F : K(x)]` places above a place of `K(x)`).

Generic in the sextic and the prime: proving it closes obligation 1b at both levels. -/
theorem finite_isPlaceFun {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0)
    (g : E.F) (hg : g ≠ 0) :
    {v : {o : E.F → ℤ // IsPlaceFun K E.F o} | v.1 g ≠ 0}.Finite := sorry

/-- **LEAF (obligation 1b), now PROVEN from `finite_isPlaceFun`.**

The tautological place system: see `finite_isPlaceFun`'s docstring for why everything
except `ord_finite` is definitional here. -/
theorem exists_placeSystem {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0) :
    Nonempty (PlaceSystem K E.F) :=
  ⟨{ Places := {o : E.F → ℤ // IsPlaceFun K E.F o}
     ord := fun v => v.1
     ord_zero := fun v => v.2.map_zero
     ord_mul := fun v => v.2.map_mul
     ord_add := fun v => v.2.ultra
     ord_algebraMap := fun v => v.2.map_algebraMap
     ord_surjective := fun v => v.2.normalised
     ord_injective := fun _ _ h => Subtype.ext h
     ord_complete := fun o h0 hmul hadd halg hsurj => ⟨⟨o, ⟨h0, hmul, hadd, halg, hsurj⟩⟩, rfl⟩
     ord_finite := finite_isPlaceFun E hsep h2 }⟩

/-- **`o` is the valuation of the rational point `P`** — `IsPlaceOfPt` with the place
replaced by a raw valuation function, so that a place can be produced through
`PlaceSystem.ord_complete` rather than exhibited inside a given system. -/
def IsPlaceFunOfPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (o : E.F → ℤ)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) : Prop :=
  match P with
  | Sum.inl q => 0 < o (E.xx - algebraMap K E.F q.1.1) ∧ 0 < o (E.yy - algebraMap K E.F q.1.2)
  | Sum.inr s => o E.xx = -1 ∧ -3 < o (E.yy - (if s then 1 else -1) * E.xx ^ 3)

/-- **LEAF (obligation 1c, AFFINE HALF): an affine rational point carries a valuation.**

Route, which is the same for both halves and needs no Dedekind theory: embed `F` into the
Laurent series field `K((t))` as a `K(x)`-algebra realising the point, and pull back the
`t`-adic order.  Concretely, at `(a, b)` with `b ≠ 0` the point is unramified over `x = a`:
`f(a + t) = b²·(1 + …)` has a square root in `K[[t]]` by Hensel (this is where `2 ≠ 0` is
used, and it is the ONLY place in this half), so `x ↦ a + t`, `y ↦ b·√(f(a+t)/b²)` is a
`K`-embedding with `o(x − a) = 1 > 0` and `o(y − b) > 0`.  At `(a, 0)` the point is
ramified: `f` is separable so `f'(a) ≠ 0`, and `x ↦ a + f'(a)⁻¹t²`, `y ↦ t·√(1 + O(t²))`
works, with `o(x − a) = 2` and `o(y) = 1`.

Only EXISTENCE is asked: that distinct points get distinct places is
`isPlaceOfPt_injective` below, which is PROVEN. -/
theorem exists_isPlaceFun_of_affPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0)
    (q : AffPt c₀ c₁ c₂ c₃ c₄ c₅ K) :
    ∃ o : E.F → ℤ, IsPlaceFun K E.F o ∧
      0 < o (E.xx - algebraMap K E.F q.1.1) ∧ 0 < o (E.yy - algebraMap K E.F q.1.2) := sorry

/-- **LEAF (obligation 1c, INFINITE HALF): each branch at infinity carries a valuation.**

In the chart `u = 1/x`, `w = y/x³` the equation becomes `w² = g(u) := u⁶f(1/u)`, a
polynomial with constant term `1` (the sextic is MONIC — this is exactly why the two points
at infinity are rational and why `Pt` carries a `Bool`).  Since `g(0) = 1 = 1²` and
`2 ≠ 0`, Hensel gives `√g ∈ K[[u]]` with `√g(0) = 1`, and `u ↦ t`, `w ↦ ±√g(t)` are two
`K`-embeddings `F ↪ K((t))`, the sign being the `Bool`.

Pulling back the `t`-adic order gives `o x = o(1/u) = −1`, and
`y − ε·x³ = u⁻³(±√g − ε)`, whose order is `> −3` exactly when the signs agree — for the
opposite sign `±√g − ε` has constant term `∓2 ≠ 0`, so the order is exactly `−3`.  That
dichotomy is what `isPlaceOfPt_injective` consumes; here only the matching sign is
asserted. -/
theorem exists_isPlaceFun_of_infPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0) (s : Bool) :
    ∃ o : E.F → ℤ, IsPlaceFun K E.F o ∧
      o E.xx = -1 ∧ -3 < o (E.yy - (if s then 1 else -1) * E.xx ^ 3) := sorry

/-- **LEAF (obligation 1c), now PROVEN from the two halves above.**

`PlaceSystem.ord_complete` is what makes this a reduction rather than a restatement: the
two halves need only produce a valuation FUNCTION with the right orders, and completeness
of `S` turns it into a place OF `S`.  Nothing here depends on which place system `S` is —
which is the point of `ord_complete` being an axiom of the interface. -/
theorem exists_isPlaceOfPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (S : PlaceSystem K E.F)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) : ∃ v : S.Places, IsPlaceOfPt E S P v := by
  have key : ∃ o : E.F → ℤ, IsPlaceFun K E.F o ∧ IsPlaceFunOfPt E o P := by
    cases P with
    | inl q =>
        obtain ⟨o, ho, h1, h2'⟩ := exists_isPlaceFun_of_affPt E hsep h2 q
        exact ⟨o, ho, h1, h2'⟩
    | inr s =>
        obtain ⟨o, ho, h1, h2'⟩ := exists_isPlaceFun_of_infPt E hsep h2 s
        exact ⟨o, ho, h1, h2'⟩
  obtain ⟨o, ho, hoP⟩ := key
  obtain ⟨v, hv⟩ := S.ord_complete o ho.map_zero ho.map_mul ho.ultra ho.map_algebraMap
    ho.normalised
  subst hv
  exact ⟨v, by cases P <;> exact hoP⟩

/-- **PROVEN: distinct rational points have distinct places.**

Three separate arguments, all from the valuation axioms alone:

* two affine points.  If `x − a` and `x − a'` both vanish at `v` then so does their
  difference, the nonzero constant `a' − a` — but a nonzero constant has order `0`.  Same
  for the ordinates.
* an affine point against a point at infinity.  `x = (x − a) + a` has order `≥ min(>0, 0)
  = 0` at an affine place, and order `−1` at an infinite one.
* the two points at infinity.  `(y + x³) − (y − x³) = 2x³` has order exactly `−3`, while
  both `y ∓ x³` have order `> −3`; the ultrametric inequality forbids that.  **This is the
  only use of `2 ≠ 0` in the whole layer**, and it is exactly why `exists_placeData`
  carries that hypothesis: in characteristic `2` the two branches at infinity collide and
  no injective `pt` exists. -/
theorem isPlaceOfPt_injective {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (S : PlaceSystem K E.F) (h2 : (2 : K) ≠ 0)
    {P Q : Pt c₀ c₁ c₂ c₃ c₄ c₅ K} {v : S.Places}
    (hP : IsPlaceOfPt E S P v) (hQ : IsPlaceOfPt E S Q v) : P = Q := by
  -- a nonzero constant has order `0`, so two constants cannot both be approximated at `v`
  have hconst : ∀ (t : E.F) (a b : K), 0 < S.ord v (t - algebraMap K E.F a) →
      0 < S.ord v (t - algebraMap K E.F b) → a = b := by
    intro t a b ha hb
    by_contra hab
    have hA : t - algebraMap K E.F a ≠ 0 := by
      intro h; rw [h, S.ord_zero] at ha; exact lt_irrefl 0 ha
    have hB : t - algebraMap K E.F b ≠ 0 := by
      intro h; rw [h, S.ord_zero] at hb; exact lt_irrefl 0 hb
    have hne : (a - b) ≠ 0 := sub_ne_zero.mpr hab
    have hd : (t - algebraMap K E.F b) - (t - algebraMap K E.F a)
        = algebraMap K E.F (a - b) := by rw [map_sub]; ring
    have hne' : algebraMap K E.F (a - b) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap K E.F).injective]; exact hne
    have hkey := S.ord_sub v _ _ hB hA (by rw [hd]; exact hne')
    rw [hd, S.ord_algebraMap v _ hne] at hkey
    have := lt_min hb ha
    omega
  -- the abscissa is nonzero at a place at infinity
  have hxxne : ∀ w : S.Places, S.ord w E.xx = -1 → E.xx ≠ 0 := by
    intro w hw h; rw [h, S.ord_zero] at hw; omega
  -- an affine place is not a place at infinity
  have hmix : ∀ a : K, 0 < S.ord v (E.xx - algebraMap K E.F a) → S.ord v E.xx = -1 → False := by
    intro a ha hb
    have hxx : E.xx ≠ 0 := hxxne v hb
    have hsub : E.xx - algebraMap K E.F a ≠ 0 := by
      intro h; rw [h, S.ord_zero] at ha; exact lt_irrefl 0 ha
    by_cases hA : a = 0
    · rw [hA, map_zero, sub_zero, hb] at ha; omega
    · have hne : algebraMap K E.F a ≠ 0 := by
        rw [ne_eq, map_eq_zero_iff _ (algebraMap K E.F).injective]; exact hA
      have heq : (E.xx - algebraMap K E.F a) + algebraMap K E.F a = E.xx := by ring
      have hk := S.ord_add v (E.xx - algebraMap K E.F a) (algebraMap K E.F a)
        hsub hne (by rw [heq]; exact hxx)
      rw [heq, S.ord_algebraMap v _ hA, hb] at hk
      have hmin : (0 : ℤ) ≤ min (S.ord v (E.xx - algebraMap K E.F a)) 0 :=
        le_min (le_of_lt ha) le_rfl
      omega
  -- the two branches at infinity are separated, and this is where `2 ≠ 0` is used
  have hinf : ∀ d : E.F, (d = 2 ∨ d = -2) → S.ord v E.xx = -1 → ∀ A B : E.F,
      A - B = d * E.xx ^ 3 → -3 < S.ord v A → -3 < S.ord v B → False := by
    intro d hd hx A B hAB hA hB
    have hxx : E.xx ≠ 0 := hxxne v hx
    have hx3 : E.xx ^ 3 ≠ 0 := pow_ne_zero _ hxx
    have h2F : (2 : E.F) ≠ 0 := by
      have h := (map_ne_zero_iff (algebraMap K E.F) (algebraMap K E.F).injective).mpr h2
      rwa [map_ofNat] at h
    have hord2 : S.ord v (2 : E.F) = 0 := by
      have h := S.ord_algebraMap v (2 : K) h2
      rwa [map_ofNat] at h
    have hdne : d ≠ 0 := by rcases hd with rfl | rfl; · exact h2F
                            · simpa using h2F
    have hordd : S.ord v d = 0 := by
      rcases hd with rfl | rfl
      · exact hord2
      · rw [S.ord_neg v (2 : E.F) h2F]; exact hord2
    have hordD : S.ord v (d * E.xx ^ 3) = -3 := by
      rw [S.ord_mul v _ _ hdne hx3, hordd, S.ord_pow v E.xx hxx 3, hx]
      norm_num
    have hDne : d * E.xx ^ 3 ≠ 0 := mul_ne_zero hdne hx3
    by_cases hAz : A = 0
    · by_cases hBz : B = 0
      · rw [hAz, hBz, sub_zero] at hAB; exact hDne hAB.symm
      · rw [hAz, zero_sub] at hAB
        have : S.ord v (d * E.xx ^ 3) = S.ord v B := by rw [← hAB, S.ord_neg v B hBz]
        omega
    · by_cases hBz : B = 0
      · rw [hBz, sub_zero] at hAB
        have : S.ord v (d * E.xx ^ 3) = S.ord v A := by rw [← hAB]
        omega
      · have hk := S.ord_sub v _ _ hAz hBz (by rw [hAB]; exact hDne)
        rw [hAB, hordD] at hk
        have := lt_min hA hB
        omega
  rcases P with q | s <;> rcases Q with q' | s'
  · obtain ⟨ha1, ha2⟩ := hP
    obtain ⟨hb1, hb2⟩ := hQ
    have hx : q.1.1 = q'.1.1 := hconst E.xx _ _ ha1 hb1
    have hy : q.1.2 = q'.1.2 := hconst E.yy _ _ ha2 hb2
    exact congrArg Sum.inl (Subtype.ext (Prod.ext hx hy))
  · obtain ⟨ha1, _⟩ := hP
    obtain ⟨hb1, _⟩ := hQ
    exact (hmix q.1.1 ha1 hb1).elim
  · obtain ⟨ha1, _⟩ := hP
    obtain ⟨hb1, _⟩ := hQ
    exact (hmix q'.1.1 hb1 ha1).elim
  · obtain ⟨ha1, ha2⟩ := hP
    obtain ⟨_, hb2⟩ := hQ
    by_cases hss : s = s'
    · rw [hss]
    · refine ((hinf ((if s' then (1 : E.F) else -1) - (if s then (1 : E.F) else -1)) ?_ ha1
        (E.yy - (if s then (1 : E.F) else -1) * E.xx ^ 3)
        (E.yy - (if s' then (1 : E.F) else -1) * E.xx ^ 3) (by ring) ha2 hb2)).elim
      rcases s <;> rcases s' <;> simp_all <;> norm_num

/-- **LEAF (obligation 1), now PROVEN from `exists_functionFieldData`,
`exists_placeSystem`, `exists_isPlaceOfPt` and `isPlaceOfPt_injective`.**

The three leaves supply the function field, its complete system of places, and one place
per rational point; `Classical.choose` turns the last into the map `pt`, and injectivity of
`pt` — the only field of `PlaceData` that the three leaves do not hand over directly — is
the proven lemma above. -/
theorem exists_placeData (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K]
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0) :
    Nonempty (PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) := by
  obtain ⟨E⟩ := exists_functionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K hsep h2
  obtain ⟨S⟩ := exists_placeSystem E hsep h2
  choose ptv hpt using exists_isPlaceOfPt E S hsep h2
  exact ⟨{ F := E.F
           xx := E.xx
           yy := E.yy
           eqn := E.eqn
           transcendental_xx := E.transcendental_xx
           gen := E.gen
           Places := S.Places
           ord := S.ord
           ord_zero := S.ord_zero
           ord_mul := S.ord_mul
           ord_add := S.ord_add
           ord_algebraMap := S.ord_algebraMap
           ord_surjective := S.ord_surjective
           ord_injective := S.ord_injective
           ord_complete := S.ord_complete
           ord_finite := S.ord_finite
           pt := ptv
           pt_injective := fun P Q h =>
             isPlaceOfPt_injective E S h2 (hpt P) (by rw [h]; exact hpt Q)
           ord_pt_affine := fun q => hpt (Sum.inl q)
           ord_pt_infinite := fun s => hpt (Sum.inr s) }⟩

/-!
### Obligation 2: Abel–Jacobi is injective, because the genus is `2 ≥ 1`

`aj P = aj Q` says `(P) − (Q) = div g + n·(∞₊)` for some `g` and `n`.  Taking degrees kills
`n` (`deg (div g) = 0` and `deg (∞₊) = 1`), so `(P) − (Q)` is principal; and a function with
a single simple pole is an isomorphism to `ℙ¹`, which a curve of genus `2` does not admit.
For a separable monic sextic the genus is exactly `2`, so `P = Q`.

Separability is not decoration: for `f = g²` the "curve" is rational and `aj` is very far
from injective, and for `f` merely non-separable the model is singular and two rational
points can collide.  A prover needs the degree map (`deg v = [κ(v) : K]`) and the degree
formula `deg (div g) = 0` — neither is in the interface, both are theorems about it.

## DECOMPOSED 2026-07-28 — see `aj_injective_of_separable` below, now PROVEN

The two sentences of the sketch are the two leaves: `exists_degreeMap` is the degree theory
("taking degrees kills `n`"), `sub_single_pt_notMem_princ` is the genus ("`(Q) − (P)` is
not principal").  The bookkeeping that joins them — that `picRel` is `princ ⊔ ℤ·[∞₊]`, that
the degree map kills `princ` because it kills every `div g`, and that the coefficient of
`[∞₊]` is therefore forced to `0` — is PROVEN below.

## DECOMPOSED AGAIN 2026-07-28 — both of those two are now PROVEN, over four sub-leaves

`exists_degreeMap` quantified existentially over `deg`, so it could not be cut at all until
a `deg` was written down.  It is written down below — `PlaceData.degOf v = [κ(v) : K]`, the
residue degree of the valuation ring `O_v = {z : 0 ≤ ord v z}` modulo its maximal ideal,
both of which the interface's axioms already support (`ord_mul`, `ord_add`,
`ord_algebraMap` are exactly the closure properties needed, and the junk convention
`ord v 0 = 0` puts `0` in `O_v` for free while forcing the `z = 0` disjunct in `m_v`).
With `deg` fixed, the leaf splits along the two conjuncts it asks for:

* `finrank_residue_pt_eq_one` — a `K`-rational point has residue field `K`;
* `degOf_divisor_eq_zero` — the degree formula, [Stichtenoth, Thm. 1.4.11].

`sub_single_pt_notMem_princ` was stated as a NON-MEMBERSHIP precisely to avoid identifying
`princ` with the set of divisors of functions.  That identification is now PROVEN
(`PlaceData.mem_princ_iff`, over `divisor_mul` / `divisor_inv`: `Set.range divisor` is
already a subgroup, so the subgroup it generates is itself), which turns the leaf into a
statement about a single `g` and lets it split along the classical argument:

* `isRationalGenerator_of_divisor_eq_sub_single` — a function whose only pole is one simple
  pole at a degree-`1` place generates: `F = K(g)`.  This is the `[F : K(g)] = deg div_∞(g)`
  half of Stichtenoth I.4.11 again, at the single value `deg div_∞(g) = 1`;
* `not_isRationalGenerator` — `F` is not a rational function field.  **This is where "the
  genus is `2`" lives, and it is the one sub-leaf that certainly cannot be proven without
  `hsep`**: for `f = (x³ + 1)²` the curve IS rational and the statement is false.  It is
  also the only one of the four that is not general function-field theory, so it is the one
  to dispatch at separately.  The classical proof is the pencil argument: `F = K(t)` makes
  `xx = A/B` with `A, B` coprime and `max (deg A) (deg B) = 2` (that maximum is
  `[K(t) : K(xx)] = [F : K(xx)] = 2`), so `(y·B³)² = ∏_{i<6} (A − rᵢ B)` over `K̄` is a
  product of six pairwise coprime quadratics — pairwise coprime because a common root of
  `A − rᵢB` and `A − rⱼB` with `rᵢ ≠ rⱼ` would be a common root of `A` and `B` — each of
  which is therefore a square of a linear form; but the pencil `⟨A, B⟩` of binary quadratics
  has at most two singular members, and `6 > 2`.  Separability enters exactly once, as the
  distinctness of the `rᵢ`.

Each of the other three is expected NOT to need `hsep` — they are statements about an
arbitrary `PlaceData`, and the sextic enters them only through the shape of `Pt`.  They
carry the hypothesis anyway, because every consumer has it and because a leaf that turns
out to need it should not have to be restated.  **A proof that does not use it should
underscore it** (`_hsep`): that makes the separation mechanically visible, and a proof of
one of the first three that DOES use `hsep` is a sign the cut leaked the genus into the
wrong leaf and should be reported.
-/

/-- Multiplication by `d`, as an additive endomorphism of `ℤ`: the coefficient map of the
degree homomorphism below. -/
def mulRightHom (d : ℤ) : ℤ →+ ℤ where
  toFun n := n * d
  map_zero' := zero_mul d
  map_add' a b := add_mul a b d

/-- **The degree of a divisor**, `deg (Σ n_v · v) = Σ n_v · deg v`, as a homomorphism
`Div → ℤ` attached to a choice of degree function on places. -/
noncomputable def degHom {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (deg : D.Places → ℤ) : D.Divisors →+ ℤ :=
  Finsupp.liftAddHom (fun v => mulRightHom (deg v))

/-- The degree of a one-point divisor (PROVEN). -/
lemma degHom_single {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (deg : D.Places → ℤ) (v : D.Places) (n : ℤ) :
    degHom D deg (Finsupp.single v n) = n * deg v := by
  simp [degHom, mulRightHom]

namespace PlaceData

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-! ### The valuation ring, the residue field and the degree of a place (PROVEN)

Everything here is forced by the interface: `O_v` is a `K`-subalgebra of `F` because
`ord_mul`, `ord_add` and `ord_algebraMap` say exactly that `{0 ≤ ord v ·}` is closed under
the operations, and `m_v` is an ideal of it for the same reason.  The junk convention
`ord v 0 = 0` is what makes `0 ∈ O_v` free and what forces the explicit `z = 0` disjunct in
`m_v` — `0 < ord v 0` is FALSE, so `{0 < ord v ·}` is not an ideal. -/

/-- **The valuation ring at a place** (PROVEN), `O_v = {z : F | 0 ≤ ord v z}`.

A `K`-subalgebra of `F`; `0 ∈ O_v` holds by the junk convention `ord v 0 = 0` rather than
by a side condition. -/
def valRing (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) : Subalgebra K D.F where
  carrier := {z : D.F | 0 ≤ D.ord v z}
  mul_mem' := by
    intro a b ha hb
    have ha' : 0 ≤ D.ord v a := ha
    have hb' : 0 ≤ D.ord v b := hb
    show 0 ≤ D.ord v (a * b)
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [D.ord_zero]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [D.ord_zero]
    rw [D.ord_mul v a b ha0 hb0]
    omega
  one_mem' := by
    show 0 ≤ D.ord v 1
    have h := D.ord_algebraMap v 1 one_ne_zero
    rw [map_one] at h
    omega
  add_mem' := by
    intro a b ha hb
    have ha' : 0 ≤ D.ord v a := ha
    have hb' : 0 ≤ D.ord v b := hb
    show 0 ≤ D.ord v (a + b)
    rcases eq_or_ne a 0 with rfl | ha0
    · simpa using hb'
    rcases eq_or_ne b 0 with rfl | hb0
    · simpa using ha'
    rcases eq_or_ne (a + b) 0 with h | h
    · rw [h, D.ord_zero]
    · have := D.ord_add v a b ha0 hb0 h
      omega
  zero_mem' := by
    show 0 ≤ D.ord v 0
    rw [D.ord_zero]
  algebraMap_mem' := by
    intro r
    show 0 ≤ D.ord v (algebraMap K D.F r)
    rcases eq_or_ne r 0 with rfl | hr
    · simp [D.ord_zero]
    · rw [D.ord_algebraMap v r hr]

/-- `z` **vanishes at** `v`: it is `0`, or it has positive order there.  The first disjunct
is the junk convention `ord v 0 = 0` showing through, not a degenerate case. -/
def VanishesAt (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) (z : D.F) : Prop :=
  z = 0 ∨ 0 < D.ord v z

/-- Vanishing is closed under addition (PROVEN). -/
lemma vanishesAt_add {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K} {v : D.Places} {a b : D.F}
    (ha : D.VanishesAt v a) (hb : D.VanishesAt v b) : D.VanishesAt v (a + b) := by
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · exact Or.inr (by simpa using ha)
  have ha0 : a ≠ 0 := by rintro rfl; rw [D.ord_zero] at ha; omega
  have hb0 : b ≠ 0 := by rintro rfl; rw [D.ord_zero] at hb; omega
  rcases eq_or_ne (a + b) 0 with h | h
  · exact Or.inl h
  · have := D.ord_add v a b ha0 hb0 h
    exact Or.inr (by omega)

/-- Vanishing absorbs multiplication by an element of the valuation ring (PROVEN). -/
lemma vanishesAt_mul_left {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K} {v : D.Places} {a b : D.F}
    (ha : 0 ≤ D.ord v a) (hb : D.VanishesAt v b) : D.VanishesAt v (a * b) := by
  rcases hb with rfl | hb
  · exact Or.inl (mul_zero a)
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inl (zero_mul b)
  have hb0 : b ≠ 0 := by rintro rfl; rw [D.ord_zero] at hb; omega
  exact Or.inr (by rw [D.ord_mul v a b ha0 hb0]; omega)

/-- **The maximal ideal at a place** (PROVEN), `m_v = {z ∈ O_v | z vanishes at v}`. -/
def valMax (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) : Ideal (D.valRing v) where
  carrier := {z : D.valRing v | D.VanishesAt v (z : D.F)}
  add_mem' := fun ha hb => vanishesAt_add ha hb
  zero_mem' := Or.inl rfl
  smul_mem' := fun c _ hx => vanishesAt_mul_left c.2 hx

/-- **The residue field at a place**, `κ(v) = O_v / m_v`, as a `K`-algebra.

It is a field — `m_v` is maximal, since `ord v z = 0` makes `z` a unit of `O_v` — but
nothing below needs that, so it is not proven here: `degOf` only wants a `K`-module. -/
abbrev residue (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) : Type :=
  (D.valRing v) ⧸ (D.valMax v)

/-- **The degree of a place**, `deg v = [κ(v) : K]`.

This is the design commitment that makes `exists_degreeMap` decomposable at all: that
statement quantifies existentially over `deg`, so no cut of it exists until some `deg` is
named, and this is the only canonical choice — `deg` has to induce a homomorphism
`Pic → ℤ` sending every rational point to `1`, and the residue degree is what does.

`Module.finrank`'s junk value `0` for an infinite-dimensional quotient is harmless: the
residue degree of a place of a function field of transcendence degree `1` is always finite,
so the junk branch is never taken — but nothing here needs that either, because both leaves
below are stated about `degOf` as written. -/
noncomputable def degOf (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) : ℤ :=
  (Module.finrank K (D.residue v) : ℤ)

/-! ### `princ` IS the range of `divisor` (PROVEN)

`princ` is defined as the subgroup GENERATED by the divisors of functions, which needed no
proof to be well defined.  The price was that membership in it says only "a sum of divisors
of functions".  It is in fact already the plain range, because `divisor` is multiplicative
where it is not junk — and that is what lets `sub_single_pt_notMem_princ` be reduced to a
statement about a single `g`. -/

/-- The divisor of a nonzero function, coefficientwise (PROVEN). -/
lemma divisor_apply (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {g : D.F} (hg : g ≠ 0)
    (v : D.Places) : D.divisor g v = D.ord v g := by
  classical
  simp [divisor, hg]

/-- `div 0 = 0`, by the junk convention (PROVEN). -/
@[simp] lemma divisor_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : D.divisor 0 = 0 := by
  classical
  simp [divisor]

/-- `div 1 = 0` (PROVEN). -/
@[simp] lemma divisor_one (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : D.divisor 1 = 0 := by
  ext v
  rw [divisor_apply D one_ne_zero v]
  have h := D.ord_algebraMap v 1 one_ne_zero
  rw [map_one] at h
  simp [h]

/-- `divisor` is multiplicative away from `0` (PROVEN), i.e. `ord_mul` coefficientwise. -/
lemma divisor_mul (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {a b : D.F} (ha : a ≠ 0) (hb : b ≠ 0) :
    D.divisor (a * b) = D.divisor a + D.divisor b := by
  ext v
  rw [Finsupp.add_apply, divisor_apply D (mul_ne_zero ha hb) v, divisor_apply D ha v,
    divisor_apply D hb v, D.ord_mul v a b ha hb]

/-- `div (g⁻¹) = − div g` (PROVEN). -/
lemma divisor_inv (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {a : D.F} (ha : a ≠ 0) :
    D.divisor a⁻¹ = -D.divisor a := by
  have h : D.divisor a + D.divisor a⁻¹ = 0 := by
    rw [← divisor_mul D ha (inv_ne_zero ha), mul_inv_cancel₀ ha, divisor_one]
  ext v
  have hv := congrArg (fun t : D.Divisors => t v) h
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at hv
  simp only [Finsupp.neg_apply]
  omega

/-- **The range of `divisor` is already a subgroup** (PROVEN): `0 = div 1`, sums are
`div (a·b)` and negatives are `div a⁻¹`, with the junk value `div 0 = 0` absorbing the
degenerate cases. -/
noncomputable def princRange (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : AddSubgroup D.Divisors where
  carrier := Set.range D.divisor
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨b, by simp⟩
    rcases eq_or_ne b 0 with rfl | hb
    · exact ⟨a, by simp⟩
    exact ⟨a * b, divisor_mul D ha hb⟩
  zero_mem' := ⟨0, divisor_zero D⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    exact ⟨a⁻¹, divisor_inv D ha⟩

/-- The subgroup generated by the divisors of functions is that set itself (PROVEN). -/
lemma princ_eq_princRange (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : D.princ = D.princRange :=
  AddSubgroup.closure_eq D.princRange

/-- **A divisor is principal exactly when it IS the divisor of a function** (PROVEN).

This is the identification that `sub_single_pt_notMem_princ`'s docstring deferred. -/
lemma mem_princ_iff (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {z : D.Divisors} :
    z ∈ D.princ ↔ ∃ g : D.F, D.divisor g = z := by
  rw [princ_eq_princRange]
  exact Iff.rfl

/-- **`F = K(t)`**: every element of `F` is a quotient of polynomials in `t`.

The shape mirrors the interface's own `gen` axiom, which says the same thing for the pair
`(xx, yy)`; here a single element is asked to generate, which is what "the function field is
rational", i.e. "the curve has genus `0`", means. -/
def IsRationalGenerator (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (t : D.F) : Prop :=
  ∀ z : D.F, ∃ a b : K[X], aeval t b ≠ 0 ∧ z * aeval t b = aeval t a

end PlaceData

/-- **LEAF (obligation 2a, first half): a rational point has residue field `K`.**

`[κ(v) : K] = 1` at `v = pt P`.  For an affine point `q = (a, b)` the interface already
supplies the two facts the classical proof starts from — `ord v (xx − a) > 0` and
`ord v (yy − b) > 0` (`ord_pt_affine`) — from which `xx, yy ∈ O_v` and every polynomial in
them reduces into `K`: `h(xx) − h(a) = (xx − a)·k(xx)` vanishes at `v`.  What is left is the
step that a general `z ∈ O_v` reduces too, i.e. that `O_v` is the LOCALIZATION of
`K[xx, yy]` at the maximal ideal of `(a, b)` and not merely a valuation ring dominating it.
That is where smoothness of the affine model at `(a, b)` is used: `K[xx, yy]` localised
there is a DVR, and a normalised valuation ring of `F` dominating a DVR with the same
fraction field equals it.  The two infinite points are the same argument in the chart
`u = 1/xx`, `w = yy/xx³`, where `ord_pt_infinite` gives `ord v u = 1` and `w ∓ 1` vanishing.

Not specific to genus `2` or to the sextic beyond the shape of `Pt`.  See
[Stichtenoth, *Algebraic Function Fields and Codes*, §I.1]. -/
theorem finrank_residue_pt_eq_one {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) :
    Module.finrank K (D.residue (D.pt P)) = 1 := sorry

/-- **LEAF (obligation 2a, second half): the degree formula.**

`Σ_v ord_v(g)·[κ(v) : K] = 0` — a function on a projective curve has as many zeros as poles,
counted with residue degrees.  This is
[Stichtenoth, *Algebraic Function Fields and Codes*, Thm. 1.4.11], and it is the whole
weight of obligation 2a.

The classical route, in the order the pieces are needed:

1. for `g ∈ K` the divisor is `0` (`ord_algebraMap`), so assume `g` transcendental;
2. `[F : K(g)] = deg (div_∞ g)`, the pole divisor of `g` — Stichtenoth I.4.11 proper,
   proven there from the weak approximation theorem plus a dimension count;
3. applying 2 to `g` and to `g⁻¹` gives `deg (div_0 g) = deg (div_∞ g)`, since
   `div_0 g = div_∞ g⁻¹` and `K(g) = K(g⁻¹)`;
4. `div g = div_0 g − div_∞ g`, so its degree is `0`.

(`0 < deg v` also holds, and is deliberately not asked for anywhere: nothing downstream
uses it, and a weaker leaf is an easier leaf.) -/
theorem degOf_divisor_eq_zero {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (g : D.F) :
    degHom D D.degOf (D.divisor g) = 0 := sorry

/-- **LEAF (obligation 2a), now PROVEN from `finrank_residue_pt_eq_one` and
`degOf_divisor_eq_zero`.**

The witness is `PlaceData.degOf`, the residue degree; the two conjuncts are the two
sub-leaves verbatim, so the only content here is that a `deg` has been NAMED.  Before it
was, the statement quantified existentially over `deg` and no decomposition of it was
possible at all. -/
theorem exists_degreeMap {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) :
    ∃ deg : D.Places → ℤ, (∀ P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K, deg (D.pt P) = 1) ∧
      (∀ g : D.F, degHom D deg (D.divisor g) = 0) :=
  ⟨D.degOf, fun P => by
      rw [PlaceData.degOf, finrank_residue_pt_eq_one D hsep P, Nat.cast_one],
    fun g => degOf_divisor_eq_zero D hsep g⟩

/-! ### Obligation 2b: the genus is at least one

`(Q) − (P)` is not a principal divisor for `P ≠ Q`: a function with a single simple pole
would be an isomorphism to `ℙ¹`, and a smooth model of a separable monic sextic has genus
`2`.  This is where separability is indispensable — for `f = g²` the curve is rational and
the conclusion is false.

Membership in `princ` (the subgroup GENERATED by the divisors of functions) is the same as
being the divisor of a function, since `div` is multiplicative; stating the leaf as a
non-membership avoided having to prove that identification here.  **It is now proven**
(`PlaceData.mem_princ_iff`), so `sub_single_pt_notMem_princ` below is assembled from the two
sub-leaves that follow rather than being sorried. -/

/-- **LEAF: a single simple pole at a rational point forces `F = K(g)`.**

If `div g = (Q) − (P)` then `g` has exactly one pole, simple, at the degree-`1` place
`pt P`, so `div_∞ g = (P)` and `[F : K(g)] = deg (div_∞ g) = 1` by
[Stichtenoth, Thm. 1.4.11] — the same theorem that `degOf_divisor_eq_zero` needs, used here
at the single value `1`.  `P ≠ Q` is what makes `g` non-constant: for `P = Q` the divisor is
`0` and `g ∈ K`.

This half is pure function-field theory; the genus is entirely in
`not_isRationalGenerator`. -/
theorem isRationalGenerator_of_divisor_eq_sub_single
    {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    {P Q : Pt c₀ c₁ c₂ c₃ c₄ c₅ K} (hPQ : P ≠ Q) {g : D.F}
    (hg : D.divisor g = Finsupp.single (D.pt Q) (1 : ℤ) - Finsupp.single (D.pt P) (1 : ℤ)) :
    D.IsRationalGenerator g := sorry

/-- **LEAF: the function field of a separable sextic is NOT rational** — "genus ≥ 1".

`F ≠ K(t)` for every `t ∈ F`.  **This is the only leaf in the whole Picard layer that uses
separability, and it is false without it**: for `f = (x³ + 1)²` the curve `y² = f(x)` is
`y = ±(x³+1)`, a pair of rational lines, and `F` really is `K(t)`.  Any proof that does not
use `hsep` is therefore wrong, which makes this leaf unusually easy to sanity-check.

The classical argument (see the module note above `mulRightHom`): `F = K(t)` writes
`xx = A/B` with `A, B ∈ K[T]` coprime and `max (deg A) (deg B) = [F : K(xx)] = 2`, whence
`(yy·B³)² = ∏_{i<6} (A − rᵢB)` over `K̄`, a product of six pairwise coprime binary quadratics
(coprime because a common root would be a common root of `A` and `B`; six distinct `rᵢ`
because `hsep`).  A product of pairwise coprime polynomials is a square only if each factor
is, so each `A − rᵢB` is a square of a linear form — but the pencil spanned by `A` and `B`
contains at most two singular binary quadratics, and `6 > 2`.

**CHARACTERISTIC-2 AUDIT (2026-07-28) — the pencil argument does NOT cover `char K = 2`,
and the leaf is true there for a completely different reason.**  In characteristic `2` a
separable sextic still exists (`f' = c₅x⁴ + c₃x² + c₁` need not vanish), `f` is still not a
square, and over a PERFECT `K` the field `F = K(xx)(√f)` is **rational**: writing
`f = f₀(x²) + x·f₁(x²)` gives `√f = √f₀(x) + x^{1/2}·√f₁(x)` with `√f₁ ≠ 0`, so
`F = K(x^{1/2}) ≅ K(u)`.  So the statement would be FALSE in characteristic `2` if a
`PlaceData` existed there.  **None does**, and that is the char-`2` proof:

* `F/K(xx)` is purely INSEPARABLE of degree `2` (`yy² = f(xx) ∈ K(xx)`), and a purely
  inseparable extension has exactly ONE place above each place of the base;
* but `ord_pt_infinite` puts both `pt (Sum.inr true)` and `pt (Sum.inr false)` above the
  infinite place of `K(xx)` (`ord xx = -1` for both), and `pt_injective` makes them
  distinct.  Two places over one — contradiction.

Concretely, over a perfect `K` of characteristic `2` the pole of `xx` in `F = K(u)` has
`ord xx = ord (u²) = -2`, so `ord_pt_infinite` is already unsatisfiable on its own.

The same remark applies to `finrank_residue_pt_eq_one`,
`isRationalGenerator_of_divisor_eq_sub_single` and hence to `sub_single_pt_notMem_princ`
itself, which has carried this since it was written: none of them says `2 ≠ 0`, and none of
them needs to.  **Do not "repair" these statements by adding a characteristic hypothesis** —
that would push a new obligation onto every consumer for a case that is already vacuous. -/
theorem not_isRationalGenerator {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (t : D.F) :
    ¬ D.IsRationalGenerator t := sorry

/-- **Obligation 2b, now PROVEN** from `isRationalGenerator_of_divisor_eq_sub_single` and
`not_isRationalGenerator`, over `PlaceData.mem_princ_iff`. -/
theorem sub_single_pt_notMem_princ {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    {P Q : Pt c₀ c₁ c₂ c₃ c₄ c₅ K} (hPQ : P ≠ Q) :
    Finsupp.single (D.pt Q) (1 : ℤ) - Finsupp.single (D.pt P) (1 : ℤ) ∉ D.princ := by
  rw [PlaceData.mem_princ_iff]
  rintro ⟨g, hg⟩
  exact not_isRationalGenerator D hsep g
    (isRationalGenerator_of_divisor_eq_sub_single D hsep hPQ hg)

/-- **LEAF (obligation 2), now PROVEN from `exists_degreeMap` and
`sub_single_pt_notMem_princ`.**

`aj P = aj Q` unfolds to `(P) − (Q) ∈ princ ⊔ ℤ·[∞₊]`, say `(P) − (Q) = y + n·[∞₊]` with
`y` principal.  Apply the degree: the left side has degree `1 − 1 = 0`, `y` has degree `0`
because the degree map kills every `div g` and hence the subgroup they generate, and
`n·[∞₊]` has degree `n`.  So `n = 0`, `(P) − (Q)` is principal, and the genus leaf forbids
that unless `P = Q`. -/
theorem aj_injective_of_separable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) :
    Function.Injective D.aj := by
  intro P Q hPQ
  by_contra hne
  obtain ⟨deg, hdeg1, hdeg0⟩ := exists_degreeMap D hsep
  have hmem : Finsupp.single (D.pt P) (1 : ℤ) - Finsupp.single (D.pt Q) (1 : ℤ) ∈
      D.princ ⊔ AddSubgroup.zmultiples
        (Finsupp.single (D.pt (PlaceData.infPlus : Pt c₀ c₁ c₂ c₃ c₄ c₅ K)) (1 : ℤ)) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hPQ
  rw [AddSubgroup.mem_sup] at hmem
  obtain ⟨y, hy, w, hw, hsum⟩ := hmem
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  -- principal divisors are killed by the degree
  have hker : ∀ z ∈ D.princ, degHom D deg z = 0 := by
    intro z hz
    have hle : AddSubgroup.closure (Set.range D.divisor) ≤ (degHom D deg).ker := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      simpa [AddMonoidHom.mem_ker] using hdeg0 g
    have hz' : z ∈ AddSubgroup.closure (Set.range D.divisor) := hz
    simpa [AddMonoidHom.mem_ker] using hle hz'
  have hL : degHom D deg (n • Finsupp.single
      (D.pt (PlaceData.infPlus : Pt c₀ c₁ c₂ c₃ c₄ c₅ K)) (1 : ℤ)) = n := by
    rw [map_zsmul, degHom_single, hdeg1 PlaceData.infPlus]
    simp
  have hR : degHom D deg (Finsupp.single (D.pt P) (1 : ℤ) - Finsupp.single (D.pt Q) (1 : ℤ))
      = 0 := by
    rw [map_sub, degHom_single, degHom_single, hdeg1 P, hdeg1 Q]
    ring
  have hn0 : n = 0 := by
    have := congrArg (degHom D deg) hsum
    rw [map_add, hker y hy, zero_add, hL, hR] at this
    exact this
  rw [hn0, zero_smul, add_zero] at hsum
  exact sub_single_pt_notMem_princ D hsep (Ne.symm hne) (hsum ▸ hy)

/-!
### Obligation 3: good reduction — the reduction homomorphism, its compatibility
with `redPt`, and torsion-freeness of its kernel

The sextic is separable mod `p` and `p` is odd, so `y² = f(x)` is a smooth proper curve
over `ℤ_p`, and:

* specialisation of divisors along the smooth model gives `red : Pic⁰(X_ℚ) → Pic⁰(X_𝔽ₚ)`,
  a homomorphism, sending `[∞₊]` to `[∞₊]` — which is why the two quotients match up;
* on a rational point, specialisation is exactly the coordinate-wise reduction `redPt`
  built earlier in this file, because the integral weighted-projective coordinates of
  `exists_int_coords` ARE the `ℤ_p`-point of the model;
* the kernel is contained in the kernel of `J(ℚ_p) → J(𝔽ₚ)`, which is the formal group
  `Ĵ(pℤ_p)`, and a formal group over `ℤ_p` is torsion-free once `p > e + 1 = 2`.

**Why the two halves are one leaf and not two.**  Torsion-freeness is a statement about
`red`, which nothing pins until an integral model is written down: split off as
`∀ red, compatible red → torsionFreeKernel red` it would be FALSE (a compatible `red` may
be built by hand with junk on the rest of `Pic`), and split off as a second existential it
would not compose with the first.  The honest split is to state the smooth proper model
over `ℤ[1/N]` and define `red` from it, which is a further theory build; until then this
leaf carries both halves, and that is deliberate rather than an oversight.

## DECOMPOSED 2026-07-28 — see `exists_reduction` below, now PROVEN

The warning above stands and the cut below RESPECTS it: `red` is **not** split off from its
torsion-freeness.  What is split off is the *reason* for the torsion-freeness, namely the
formal group, and it is bundled WITH `red` in a single existential (`ReductionFiltration`),
so no hand-built compatible `red` can satisfy the leaf without also carrying a separated
`p`-adic filtration of its kernel.

What that buys: the group-theoretic half of Silverman *AEC* VII.3.2 / IV.6.1 — "a separated
filtration with elementary-abelian `p`-graded pieces on which `[p]` shifts the level by
exactly one has no torsion" — becomes PROVEN here, and the remaining leaf is the concrete
arithmetic statement that the formal group of the Jacobian over `ℤ_p` provides such a
filtration for `p > e + 1 = 2`.  That is exactly where the hypothesis `p ≠ 2` lives.
-/

/-- **Reduction of divisor classes, together with the `p`-adic filtration of its kernel.**

`filt n` is `J(ℚ) ∩ Ĵ(pⁿℤ_p)`, the `n`-th subgroup of the formal group of the Jacobian
along the smooth model over `ℤ_p`.  The axioms are what the formal group provides for
`p > e + 1 = 2`:

* `filt_one`: the kernel of reduction is exactly the first step, `J(ℚ) ∩ Ĵ(pℤ_p)`;
* `filt_separated`: `⋂ₙ Ĵ(pⁿℤ_p) = 0`, the filtration is Hausdorff;
* `smul_p_mem`: each graded piece `Ĵ(pⁿ)/Ĵ(pⁿ⁺¹) ≅ 𝔽_p^g` is killed by `p`;
* `smul_p_notMem`: `[p] : Ĵ(pⁿ) → Ĵ(pⁿ⁺¹)` is BIJECTIVE when `p > e + 1`, so multiplication
  by `p` raises the level by exactly one and never by more.

Bundling the filtration with `red` rather than quantifying over compatible `red`s is what
keeps the cut sound; see the section note above. -/
structure ReductionFiltration {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (p : ℕ) [Fact p.Prime]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)) where
  /-- reduction of divisor classes, `J(ℚ) → J(𝔽ₚ)` -/
  red : D.Pic →+ D'.Pic
  /-- compatibility with the concrete reduction of points -/
  red_aj : ∀ P, red (D.aj P) = D'.aj (redPt c₀ c₁ c₂ c₃ c₄ c₅ P)
  /-- the filtration by the subgroups of the formal group -/
  filt : ℕ → AddSubgroup D.Pic
  /-- the first step is the kernel of reduction -/
  filt_one : filt 1 = red.ker
  filt_antitone : Antitone filt
  /-- the filtration is separated -/
  filt_separated : ∀ z : D.Pic, (∀ n, z ∈ filt n) → z = 0
  /-- each graded piece is killed by `p` -/
  smul_p_mem : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ filt n, p • z ∈ filt (n + 1)
  /-- and multiplication by `p` raises the level by exactly one -/
  smul_p_notMem : ∀ n : ℕ, 1 ≤ n → ∀ z ∈ filt n, z ∉ filt (n + 1) → p • z ∉ filt (n + 2)

namespace ReductionFiltration

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime]
  {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ} {D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)}

/-- **PROVEN: an element sitting at a FINITE level of the filtration is killed by no
nonzero integer.**

Strong induction on `m`.  If `p ∤ m` then `m` is invertible modulo the level: Bézout gives
`u·m + v·p = 1`, and both `m • w` (assumed `0`) and `p • w` (in the next level) then place
`w` itself in the next level, contradicting `w ∉ filt (j+1)`.  If `p ∣ m`, write `m = p·m'`
and apply the inductive hypothesis to `m' < m` at `p • w`, which by the two `smul_p`
axioms sits at level exactly `j + 1`. -/
theorem nsmul_ne_zero_of_notMem (R : ReductionFiltration p D D') :
    ∀ m : ℕ, m ≠ 0 → ∀ j : ℕ, 1 ≤ j → ∀ w : D.Pic, w ∈ R.filt j → w ∉ R.filt (j + 1) →
      m • w ≠ 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm j hj w hin hout
    by_cases hdvd : p ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      have hp : p.Prime := Fact.out
      have hm' : m' ≠ 0 := by rintro rfl; simp at hm
      have hlt : m' < p * m' := by
        have h2 := hp.two_le
        have h3 := Nat.pos_of_ne_zero hm'
        nlinarith
      have h1 : p • w ∈ R.filt (j + 1) := R.smul_p_mem j hj w hin
      have h2 : p • w ∉ R.filt (j + 1 + 1) := R.smul_p_notMem j hj w hin hout
      have hkey := ih m' hlt hm' (j + 1) (by omega) (p • w) h1 h2
      intro hcon
      rw [mul_comm, mul_smul] at hcon
      exact hkey hcon
    · intro hcon
      apply hout
      have hp : p.Prime := Fact.out
      have hcop : Nat.Coprime m p := Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr hdvd)
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have hz1 : ((m : ℤ)) • w = 0 := by rw [natCast_zsmul]; exact hcon
      have hz2 : ((p : ℤ)) • w ∈ R.filt (j + 1) := by
        rw [natCast_zsmul]; exact R.smul_p_mem j hj w hin
      have hw : w = u • ((m : ℤ) • w) + v • ((p : ℤ) • w) := by
        rw [smul_smul, smul_smul, ← add_smul, huv, one_smul]
      rw [hw, hz1, smul_zero, zero_add]
      exact AddSubgroup.zsmul_mem _ hz2 v

/-- **PROVEN: the kernel of reduction is torsion-free.**

A nonzero `z` in the kernel lies in `filt 1`, and by separatedness it leaves the filtration
at some finite level `k`; the lemma above then says no nonzero integer kills it. -/
theorem ker_torsionFree (R : ReductionFiltration p D D') :
    ∀ z : D.Pic, R.red z = 0 → ∀ n : ℕ, n ≠ 0 → n • z = 0 → z = 0 := by
  intro z hz n hn hnz
  by_contra hz0
  have hz1 : z ∈ R.filt 1 := by rw [R.filt_one]; exact hz
  have hstep : ∃ k, 1 ≤ k ∧ z ∈ R.filt k ∧ z ∉ R.filt (k + 1) := by
    by_contra hcon
    have hcon' : ∀ k, 1 ≤ k → z ∈ R.filt k → z ∈ R.filt (k + 1) := by
      intro k hk hzk
      by_contra h
      exact hcon ⟨k, hk, hzk, h⟩
    have hall : ∀ k, 1 ≤ k → z ∈ R.filt k := by
      intro k hk
      induction k with
      | zero => omega
      | succ m ihm =>
        rcases Nat.lt_or_ge 1 (m + 1) with h | h
        · have hm : 1 ≤ m := by omega
          exact hcon' m hm (ihm hm)
        · have hm1 : m + 1 = 1 := by omega
          rw [hm1]; exact hz1
    refine hz0 (R.filt_separated z fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact R.filt_antitone (Nat.zero_le 1) hz1
    · exact hall k hk
  obtain ⟨k, hk1, hkin, hkout⟩ := hstep
  exact R.nsmul_ne_zero_of_notMem n hn k hk1 z hkin hkout hnz

end ReductionFiltration

/-- **LEAF (obligation 3a): reduction and its formal-group filtration exist.**

The sextic is separable mod `p` and `p` is odd, so `y² = f(x)` is a smooth proper curve over
`ℤ_p`; specialisation of divisors along it gives `red`, sending `[∞₊]` to `[∞₊]`, and on a
rational point it is the coordinate-wise `redPt` because the integral weighted-projective
coordinates of `exists_int_coords` ARE the `ℤ_p`-point of the model.  The filtration is
`filt n = J(ℚ) ∩ Ĵ(pⁿℤ_p)`, and its four axioms are the standard properties of the formal
group of an abelian variety over `ℤ_p`, valid because `p > e + 1 = 2` — which is where
`hp : p ≠ 2` is used.

This leaf is generic in the sextic and the prime, so proving it closes obligation 3 at both
levels at once. -/
theorem exists_reductionFiltration {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p))
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)).Separable) :
    Nonempty (ReductionFiltration p D D') := sorry

/-- **LEAF (obligation 3), now PROVEN from `exists_reductionFiltration` and
`ReductionFiltration.ker_torsionFree`.** -/
theorem exists_reduction {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p))
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)).Separable) :
    ∃ red : D.Pic →+ D'.Pic,
      (∀ P, red (D.aj P) = D'.aj (redPt c₀ c₁ c₂ c₃ c₄ c₅ P)) ∧
      (∀ z : D.Pic, red z = 0 → ∀ n : ℕ, n ≠ 0 → n • z = 0 → z = 0) := by
  obtain ⟨R⟩ := exists_reductionFiltration hp D D' hsep
  exact ⟨R.red, R.red_aj, R.ker_torsionFree⟩

end Picard

section MordellWeil

/-!
## Obligation 4 SPLIT (2026-07-28): Mordell–Weil is generic, only rank `0` is level-specific

`X18.finite_pic` and `X13.finite_pic` were single leaves until 2026-07-28, each carrying
"Mordell–Weil together with `rank J(ℚ) = 0`" for one curve.  Those two halves are **not**
equally level-specific, and the file was mis-cut along that line:

* **Mordell–Weil** — `Pic⁰` is finitely generated — holds for *every* separable monic
  sextic over `ℚ`.  Nothing about `X₁(18)` or `X₁(13)` enters it, so it belongs beside
  `exists_placeData`, `aj_injective_of_separable` and `exists_reduction`, which are generic
  in the same way.  It is `fg_pic` below, and it is PROVEN over two leaves.
* **Rank `0`** is the whole of what is specific to the two curves, and its sharpest
  self-contained form is *not* "`Pic` is torsion" (which re-imports Mordell–Weil) but
  `Pic = 2·Pic`, the literal output of a `2`-descent: `J(ℚ)/2J(ℚ) ↪ Sel₂(J/ℚ) = 0`.  That
  is `X18.two_divisible_pic` and `X13.two_divisible_pic`.

The join is `finite_of_fg_of_two_divisible`, PROVEN below: a finitely generated abelian
group `A` with `A = 2A` is finite.  Note that neither half alone gives finiteness — `ℤ` is
finitely generated and `ℚ` is `2`-divisible, and both are infinite — so the cut is not
a repackaging of the conclusion.

**Why `Pic = 2·Pic` rather than `rank = 0` spelled some other way.**  `Sel₂ = 0` was
verified independently for both curves on 2026-07-28 (Magma, `SetClassGroupBounds("GRH")`,
`TwoSelmerGroup(J)` of order `1` at both levels, `RankBound(J) = 0` at both); together with
`TorsionSubgroup(J) = ℤ/21` and `ℤ/19` — both of ODD order — that is exactly
`J(ℚ) = 2J(ℚ)`.  The refuting check is `#TwoSelmerGroup(Jacobian(HyperellipticCurve(f)))`
returning anything but `1`, or a torsion subgroup of even order.

**Relation to `Fermat/FLT/ModularCurve/X0.lean`.**  That file carries the same two
obligations for a scheme-theoretic abelian variety, assembled into
`fg_relPoint_of_abelianScheme`.  **The leaf names below were refreshed on 2026-07-28**;
the `b6ab74e9` reading recorded here — `exists_integralCoordinates_of_abelianScheme` and
`finite_kummerCochains_of_abelianScheme` — is stale in both halves.  The height leaf is
now the pair `Fermat.exists_isAmpleSheaf_symmetric_cube`
(`Modularity/AbelianSchemeIsogeny.lean`) and
`Fermat.nonempty_cubeModel_of_isAmpleSheaf_cube` (`X0.lean`) — a 2026-07-28 sheaf-level
cut of what was then `exists_cubeModel_of_abelianScheme`, which is now PROVEN over them —
and `finite_kummerCochains_of_abelianScheme` was
DELETED: release 12 rewired `finite_quotient_psmul_of_abelianScheme` onto
`exists_finiteIndex_divisible_of_abelianScheme`, which is itself PROVEN over Hermite's
theorem, leaving `exists_geomPt_nsmul_eq_of_abelianScheme` and
`exists_discrBound_divisionField_of_abelianScheme`.  Class groups and units are NOT on
that path any more.  The two open leaves below are the
`PlaceData.Pic` instances of exactly those.  **They should not be proven twice.**  The
right long-term repair is a bridge
`D.Pic ≃+ RelPoint jstr (𝟙 SpecQ)` for the Jacobian of the smooth model, after which
`fg_pic` follows from `fg_relPoint_of_abelianScheme` and both leaves below can be deleted;
that bridge was recorded as unavailable because importing `X0.lean` into this module would
drag its whole cone into `MazurTorsion.lean`.

**THAT OBJECTION IS STALE, checked 2026-07-28 and left here for its owner to act on.**
`MazurTorsion.lean` is the SOLE consumer of this module (`grep -rn 'import
Fermat.FLT.ModularCurve.HyperellipticJacobian' Fermat/` returns exactly one line,
`MazurTorsion.lean:257`), and it **already carries `public import
Fermat.FLT.ModularCurve.X0` at line 266**.  So the bridge adds ZERO modules to
`MazurTorsion.lean`'s import cone; and there is no cycle, since `X0.lean` does not mention
this module.  What the bridge would actually cost is a build-order edge
`HyperellipticJacobian → X0`, which is a compile-time price, not a cone-growth one.  All six
declarations named above still exist in `X0.lean` (`fg_relPoint_of_abelianScheme:26330`,
`exists_cubeModel_of_abelianScheme:25196`, `finite_quotient_psmul_of_abelianScheme:26099`,
`exists_finiteIndex_divisible_of_abelianScheme:26007`,
`exists_geomPt_nsmul_eq_of_abelianScheme:25838`,
`exists_discrBound_divisionField_of_abelianScheme:25927`), so the deletion of the two
generic leaves below is a live option worth about `−2` on the frontier.

**The bridge does NOT help the two level-specific leaves.**  `X0.lean` does not prove rank
`0` anywhere: it *assumes* it, as the `Prop`-valued hypothesis `HasRankZeroJacobian`
(`X0.lean:22356`), whose consumers take it as an argument.  So `X18.two_divisible_pic` and
`X13.two_divisible_pic` are the same obligation appearing as honest leaves rather than as
a hypothesis, and no amount of X0 machinery discharges them.
-/

/-- **A finitely generated abelian group `A` with `A = 2·A` is finite** (PROVEN) — the
join of the two halves of obligation 4.

The determinant trick (Nakayama's lemma, `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`,
applied to `I = (2)` and `N = ⊤`) produces an integer `r` with `r ≡ 1 (mod 2)` killing all
of `A`.  Being odd, `r ≠ 0`, so `A` is a finitely generated `ℤ`-torsion module, hence
finite by `Module.finite_of_fg_torsion`.

Neither hypothesis can be dropped: `ℤ` is finitely generated and infinite, `ℚ` satisfies
`hdiv` and is infinite.  Concretely, for `J₁(18)(ℚ) ≅ ℤ/21` the `r` produced is any odd
multiple-of-`2`-plus-one killing the group, e.g. `21`. -/
theorem finite_of_fg_of_two_divisible {A : Type*} [AddCommGroup A]
    (hfg : AddGroup.FG A) (hdiv : ∀ z : A, ∃ w : A, z = 2 • w) : Finite A := by
  haveI hmf : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr hfg
  have htop : (⊤ : Submodule ℤ A).FG := Module.finite_def.mp hmf
  have hin : (⊤ : Submodule ℤ A) ≤ Ideal.span {(2 : ℤ)} • (⊤ : Submodule ℤ A) := by
    intro z _
    obtain ⟨w, rfl⟩ := hdiv z
    have hz : (2 : ℕ) • w = (2 : ℤ) • w := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      norm_num
    rw [hz]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (2 : ℤ)) Submodule.mem_top
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(2 : ℤ)}) ⊤ htop hin
  have hrne : r ≠ 0 := by
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hr1
    rintro rfl
    omega
  have htor : Module.IsTorsion ℤ A := fun z =>
    ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hrne⟩, hr0 z Submodule.mem_top⟩
  exact Module.finite_of_fg_torsion A htor

/-- **LEAF (Mordell–Weil, geometric half): a height function with the Northcott property
exists on `Pic⁰(X_ℚ)`**, for every separable monic sextic.

`DescentHeight` (`Fermat/FLT/Mathlib/GroupTheory/Descent.lean`, PROVEN there) bundles the
three hypotheses of Silverman *AEC* VIII.3.1: the quasi-parallelogram translate bound, the
one-sided quadraticity bound `m²·h(P) ≤ h(mP) + C`, and Northcott finiteness.  For a
genus-`2` Jacobian the height is the Weil height attached to the theta divisor `2Θ`, which
is symmetric and ample; concretely it is the naive height of the four Kummer coordinates of
the Mumford representation, and the quadraticity bound is the duplication formula on the
Kummer surface.

The `m` is a field of `DescentHeight`, and the sibling leaf below is deliberately stated at
every prime rather than at `2`, so that this node stays free to supply whichever `m` its
proof produces (`Fermat.WeilHeight.toDescentHeight` supplies `2`).

**Not vacuous, and not the conclusion in disguise.**  A `DescentHeight` on an infinite
group is a real object — it exists on `E(ℚ)` of any rank — and it says nothing on its own
about finite generation; the descent theorem needs the arithmetic half too.

**Do not prove this twice.**  `Fermat/FLT/ModularCurve/X0.lean`'s
`exists_integralCoordinates_of_abelianScheme` (feeding its PROVEN
`exists_descentHeight_of_abelianScheme`) is the same obligation for a scheme-theoretic
abelian variety; see the section docstring for the bridge that would make one of the two
redundant. -/
theorem exists_descentHeight_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    Nonempty (DescentHeight D.Pic) := sorry

/-- **LEAF (Mordell–Weil, arithmetic half): weak Mordell–Weil at a prime —
`Pic⁰(X_ℚ) / p·Pic⁰(X_ℚ)` is finite**, for every separable monic sextic and every prime `p`.

Silverman *AEC* VIII.1.1 for elliptic curves; the abelian-variety argument is the same.
Adjoin the `p`-torsion to get `L = ℚ(J[p])`, a finite extension; the Kummer sequence
`0 → J[p] → J →[p] J → 0` embeds `J(ℚ)/pJ(ℚ)` into `H¹(G_ℚ, J[p])`, and the image is
unramified outside the finite set of places dividing `p·disc(f)`.  Finiteness of that
`H¹_S` is finiteness of the class group of `L` together with Dirichlet's unit theorem, via
the `p`-Selmer group of `L`.

Stated at a PRIME on purpose: `Fermat.finite_quotient_nsmul_of_prime` (PROVEN) promotes it
to every `n ≠ 0` by induction on the prime factorisation, and at a prime the arithmetic
input is an `𝔽_p`-vector space rather than a general finite abelian group.

**FAITHFULNESS.**  `hp` is load-bearing: at `p = 0` the quotient is `Pic` itself and the
statement is FALSE for any positive-rank Jacobian; at `p = 1` it is vacuously true.

**Do not prove this twice** — `Fermat/FLT/ModularCurve/X0.lean` proves the corresponding
`finite_quotient_psmul_of_abelianScheme` by Galois descent over
`exists_finiteIndex_divisible_of_abelianScheme` (the name
`finite_kummerCochains_of_abelianScheme`, recorded here until 2026-07-28, no longer
exists), which is the same weak-Mordell–Weil obligation as this leaf; see the section
docstring. -/
theorem finite_quotient_psmul_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) (p : ℕ) (hp : p.Prime) :
    Finite (D.Pic ⧸ (nsmulAddMonoidHom p : D.Pic →+ D.Pic).range) := sorry

/-- **Mordell–Weil for the hyperelliptic Jacobian: `Pic⁰(X_ℚ)` is finitely generated**
(PROVEN, from the two leaves above and the descent theorem) — GENERIC in the sextic, and
carrying no level-`18` or level-`13` content.

The descent theorem `Fermat.fg_of_descentHeight` (Silverman *AEC* VIII.3.1) is pure group
theory and is PROVEN in `Fermat/FLT/Mathlib/GroupTheory/Descent.lean`; the two things it
consumes are exactly the two leaves above.  So the only obstructions to Mordell–Weil here
are heights and weak Mordell–Weil — the descent argument itself is compiler-checked. -/
theorem fg_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    AddGroup.FG D.Pic := by
  obtain ⟨dh⟩ := exists_descentHeight_pic D hsep
  refine fg_of_descentHeight dh (finite_quotient_nsmul_of_prime
    (fun p hp => finite_quotient_psmul_pic D hsep p hp) dh.m ?_)
  have h := dh.two_le
  omega

end MordellWeil

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

open Polynomial

/-- The level-`18` sextic as a polynomial, in numeral form (PROVEN). -/
lemma sextPoly_eq {K : Type*} [CommRing K] :
    sextPoly 1 (-2) 5 (-10) 10 (-4) K
      = X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 + 5 * X ^ 2 - 2 * X + 1 := by
  simp only [sextPoly]
  push_cast
  ring

/-- Its derivative (PROVEN). -/
lemma derivative_sextPoly_eq {K : Type*} [CommRing K] :
    derivative (X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 + 5 * X ^ 2 - 2 * X + 1 : K[X])
      = 6 * X ^ 5 - 20 * X ^ 4 + 40 * X ^ 3 - 30 * X ^ 2 + 10 * X - 2 := by
  simp [derivative_pow, map_ofNat]
  ring

/-- **The level-`18` sextic is separable over every field in which `144 ≠ 0`** (PROVEN, by
an explicit Bézout certificate).

`f` and `f'` satisfy `U·f + V·f' = 144` with

    U = 60x⁴ − 80x³ + 150x² + 120x + 178,   V = −10x⁵ + 20x⁴ − 45x³ − 20x² − 33x + 17

an identity of polynomials with INTEGER coefficients, so it holds over every commutative
ring and `ring` checks it; dividing by `144` gives `IsCoprime f f'`.  (PARI/GP found the
certificate — an untrusted searcher — and the kernel verifies it.  `144 = 2⁴·3²` and
`disc f = −2¹⁵·3⁴`, which is why `5` is a good prime: `144` is a unit in `𝔽₅`.)

This is the smoothness of the curve, and over `ZMod p` it is exactly good reduction at
`p`; it is the hypothesis of `exists_placeData`, `aj_injective_of_separable` and
`exists_reduction`. -/
lemma separable_sextPoly {K : Type} [Field K] (h : (144 : K) ≠ 0) :
    (sextPoly 1 (-2) 5 (-10) 10 (-4) K).Separable := by
  rw [Polynomial.separable_def', sextPoly_eq, derivative_sextPoly_eq]
  refine ⟨C (144 : K)⁻¹ * (60 * X ^ 4 - 80 * X ^ 3 + 150 * X ^ 2 + 120 * X + 178),
    C (144 : K)⁻¹ * (-10 * X ^ 5 + 20 * X ^ 4 - 45 * X ^ 3 - 20 * X ^ 2 - 33 * X + 17), ?_⟩
  have hc : (C (144 : K)⁻¹) * (144 : K[X]) = 1 := by
    rw [show ((144 : K[X])) = C (144 : K) by simp [map_ofNat], ← C_mul, inv_mul_cancel₀ h, C_1]
  calc C (144 : K)⁻¹ * (60 * X ^ 4 - 80 * X ^ 3 + 150 * X ^ 2 + 120 * X + 178)
        * (X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 + 5 * X ^ 2 - 2 * X + 1)
      + C (144 : K)⁻¹ * (-10 * X ^ 5 + 20 * X ^ 4 - 45 * X ^ 3 - 20 * X ^ 2 - 33 * X + 17)
        * (6 * X ^ 5 - 20 * X ^ 4 + 40 * X ^ 3 - 30 * X ^ 2 + 10 * X - 2)
      = C (144 : K)⁻¹ * (144 : K[X]) := by ring
    _ = 1 := hc

/-- **LEAF (obligation 4, LEVEL-SPECIFIC HALF) AT LEVEL `18`: `rank J₁(18)(ℚ) = 0`, in the
form `J₁(18)(ℚ) = 2·J₁(18)(ℚ)`.**

This is what is left of `finite_pic` once Mordell–Weil — which is generic in the sextic —
has been split off as `fg_pic`; see the `MordellWeil` section docstring for why the cut
runs here and not elsewhere.  `D.Pic` is `Pic⁰` of the smooth projective model of
`y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1` over `ℚ`, which is `J₁(18)(ℚ)` because the
curve has a rational point.

**Why `2`-divisibility is the right statement of rank `0`.**  It is the literal output of a
`2`-descent — `J(ℚ)/2J(ℚ) ↪ Sel₂(J/ℚ)`, and `Sel₂(J/ℚ) = 0` here — so a prover can close it
without first proving Mordell–Weil.  The alternative phrasing "`Pic` is torsion" is
equivalent only *given* finite generation, and would therefore silently re-import the
generic half into this level-specific leaf.

Quantifying over an arbitrary `D` is safe because `PlaceData` pins the presentation up to
isomorphism; see the `Picard` section docstring.

**Not vacuous, and not implied by the shape of `Pic`.**  `Pic⁰` of a positive-rank
Jacobian is not `2`-divisible, and neither is one with even torsion; the statement fails,
for instance, for `y² = x⁶ + x² + 1` (rank `1`).

## The arithmetic that makes this true (untrusted searchers, not proofs)

Magma, re-run from scratch on 2026-07-28 — the fourth independent run, reproducing the
earlier three and adding the `2`-Selmer computation this leaf now rests on
(`SetClassGroupBounds("GRH")`):

    C : y² = x⁶ − 4x⁵ + 10x⁴ − 10x³ + 5x² − 2x + 1
    Genus(C)                       = 2
    Factorization(Discriminant(C)) = 2²³ · 3⁴      — so `5` is a good prime
    Factorization(f)               = irreducible of degree 6
    TorsionSubgroup(J)             = ℤ/21          — ODD order
    #TwoSelmerGroup(J)             = 1             — so `J(ℚ)/2J(ℚ) = 0`
    RankBound(J)                   = 0             — SHARP, not merely `≤ 1`
    #J(𝔽₅)                         = 21            — reduction at `5` is an ISO
    #C(𝔽₅)                         = 6             — matches `card_X18_F5`
    Chabauty0(J) = {(1 : ±1 : 0), (1 : ±1 : 1), (0 : ±1 : 1)}   — SIX points

`Sel₂ = 0` gives this leaf directly: `J(ℚ)/2J(ℚ)` injects into it, so the quotient is
trivial, which is exactly `∀ z, ∃ w, z = 2 • w`.  Independently, `S₂(Γ₁(18))` has one
newform orbit with `L(f, 1) ≈ 0.4103 − 0.0724i ≠ 0`, so Kolyvagin–Logachev gives
`rank J(ℚ) = 0` by a different route; the conductor of `J` is `324 = 18²`.  `Chabauty0` on
a rank-`0` Jacobian is **not** a point search: it is the Mazur–Tate argument, a decision
procedure returning a provably complete `C(ℚ)`, and it involves no covering collection.

Refuting checks: `#TwoSelmerGroup(Jacobian(HyperellipticCurve(f))) ≠ 1` overturns this leaf
outright; `RankBound(J)` returning a positive lower bound, or `TorsionSubgroup(J)` of even
order, overturns it as well; a seventh point from `Chabauty0` overturns the conclusion
downstream.  A FIFTH independent Magma run on 2026-07-28 reproduced every line of the
table above exactly — `genus 2`, `f` irreducible, `disc = 2²³·3⁴`, `TorsionSubgroup = ℤ/21`,
`#TwoSelmerGroup = 1`, `RankBounds = [0, 0]`.

## ATOMICITY AUDIT (2026-07-28) — which AXES were searched, and what would refute each

This leaf has now been left atomic by successive dispatches.  Per the standing rule that an
irreducibility verdict is only as wide as the axis its author searched, here are the axes,
so the next reader can re-check a claim instead of redoing the survey.

* **DESCENT axis (`2`-Selmer) — live, but blocked on MISSING STRUCTURE, not on difficulty.**
  The cut this leaf wants is `J(ℚ)/2J(ℚ) ↪ Sel₂ = 0`, over a descent map
  `δ : Pic → L*/L*²` with `L = ℚ[x]/(f)` (a degree-`6` field, `f` being irreducible),
  PINNED to be the genuine `∏ (x(Pᵢ) − θ)`.  The cheap way to pin a map — constrain its
  VALUES on rational points — is **provably powerless here**, and that is the sharp
  obstruction: `#Sel₂ = 1` says the genuine `δ` is IDENTICALLY ZERO on `J(ℚ)`, so the junk
  model `δ = 0` satisfies every constraint that naming rational points can impose (and
  `J₁(18)(ℚ) ≅ ℤ/21` has ODD order, so this is not an accident of which points were named).
  With `δ = 0` the residual obligation `ker δ ⊆ 2·Pic` IS this leaf's conclusion, verbatim
  — the junk-structure trap the `Picard` section docstring warns against.  An honest
  pinning must therefore constrain `δ` at a NON-rational closed point, which needs residue
  fields `κ(v)` and the norms `N_{κ(v) ⊗ L / L}` — precisely the degree theory `PlaceData`
  deliberately omits (see "Why `Pic` is `Pic⁰` although no degree map appears").  So the
  cut is available exactly when someone extends `PlaceData` with residue fields.
  *Refuting check*: exhibit constraints on `δ` mentioning only rational points that the
  genuine descent map satisfies and the zero map does not.
* **REDUCTION axis — structurally empty, not merely unfinished.**  `exists_reduction` gives
  `red : D.Pic →+ D'.Pic` with torsion-free kernel.  For finitely generated `Pic` that
  makes `ker red ≅ ℤ^rank` and `Pic / ker red` embed in the finite `J(𝔽₅)`, so reduction
  bounds TORSION and conveys no rank information at all.  No sharpening of `exists_reduction`
  can help.  *Refuting check*: a reduction statement whose conclusion constrains a FREE
  quotient of `Pic`.
* **ELLIPTIC axis — dead, and now machine-checked at this level too.**  Magma `ModAbVar`,
  2026-07-28: `IsSimple(JOne(18)) = true`, `Dimension = 2`, decomposition a single factor
  `image(18A[2])` of conductor `2²·3⁴`.  So `J₁(18)` is `ℚ`-SIMPLE and not `ℚ`-isogenous to
  a product of elliptic curves; the project's elliptic-curve Mordell–Weil machinery cannot
  be routed to it.  (`X13.exists_jacobianPackage` records the same conclusion at level `13`
  from the diamond `⟨5⟩`; `IsSimple(JOne(13)) = true` confirms it by a second method.)  This
  axis was NOT recorded here before 2026-07-28.  *Refuting check*: `IsSimple(JOne(18))`
  returning `false`, or a degree-`n` map from `C` to an elliptic curve over `ℚ`.
* **ELLIPTIC-CHABAUTY axis** — refuted three times over; see ROUTE 1 below, which keeps the
  refuting check for each of the three findings.
* **ANALYTIC axis** — `L(f, 1) ≠ 0` plus Kolyvagin–Logachev gives rank `0` by a genuinely
  independent route, but neither Gross–Zagier nor the Euler-system input exists in this
  project, in mathlib, or in `~/cs/FLT`.  *Refuting check*: grep any of the three for an
  Euler system or a Gross–Zagier formula.

**Do not manufacture a decomposition along the descent axis without the residue fields.**
Every cut of the shape "a `δ` with `ker δ ⊆ 2·Pic` exists" plus "that `δ` vanishes" is
discharged by `δ = 0` and is therefore vacuous, by the first bullet. -/
theorem two_divisible_pic (D : PlaceData 1 (-2) 5 (-10) 10 (-4) ℚ) (z : D.Pic) :
    ∃ w : D.Pic, z = 2 • w := sorry

/-- **`J₁(18)(ℚ)` is FINITE** — obligation 4 at level `18` — a LEAF from its creation until
2026-07-28, now PROVEN over the generic Mordell–Weil node `fg_pic` and the level-specific
rank-`0` leaf `two_divisible_pic` above.

Only FINITENESS is asked for, not the order: `redPt_injective` needs nothing sharper, and
`card_coprime` is deliberately absent for the reason given on `JacobianPackage`.

The smoothness side condition is `separable_sextPoly` at `144 ≠ 0` in `ℚ`. -/
theorem finite_pic (D : PlaceData 1 (-2) 5 (-10) 10 (-4) ℚ) : Finite D.Pic :=
  finite_of_fg_of_two_divisible (fg_pic D (separable_sextPoly (by norm_num)))
    (two_divisible_pic D)

/-- **`Pic⁰(X_1(18))` exists, has rank `0`, and reduces injectively at `5`** — a LEAF from
its creation on 2026-07-27 until later the same day, now PROVEN by decomposition.

The four obligations that unfolding `JacobianPackage` produces — the ones the module
docstring and `MazurLevel18.no_noncuspidal_point_on_smooth_model` both record — are now
four named leaves, three of them generic in the sextic and one specific to this curve:

1. `Pic⁰` of the genus-`2` curve, as a group: `exists_placeData` (the function field, its
   places, and the divisor theory) followed by the DEFINITION `PlaceData.Pic`;
2. Abel–Jacobi injective because the genus is `≥ 1`: `aj_injective_of_separable`;
3. good reduction at `5`, the reduction homomorphism, its compatibility with `redPt`, and
   torsion-freeness of its kernel: `exists_reduction`;
4. `rank J(ℚ) = 0`, i.e. Mordell–Weil plus rank zero: `finite_pic` above, itself PROVEN
   since 2026-07-28 over the generic Mordell–Weil node `fg_pic` and the level-specific
   rank-`0` leaf `two_divisible_pic`.

The smoothness side conditions are discharged by `separable_sextPoly` from an explicit
Bézout certificate, at `144 ≠ 0` in `ℚ` and in `𝔽₅`.

**What the decomposition buys, in the terms of the caveat below.**  The caveat is that
`Nonempty (JacobianPackage …)` is EQUIVALENT to `redPt_injective_five`, being satisfiable
by a junk structure; that is a property of an existential over a STRUCTURE, and it does not
survive the cut, because `PlaceData.Pic` is a definition.  There is no free `𝔽₂`-vector
space to exhibit against `finite_pic`: it asks that the divisor class group of a specific
curve be finite, and only Mordell–Weil and rank `0` can answer.  The same holds of
`two_divisible_pic`, into which its level-specific half was split on 2026-07-28.

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
stated exactly so that an honest `Pic⁰` slots in with no consumer changing.
That is what the decomposition above does: `J` is now `PlaceData.Pic`, the honest
`Pic⁰`, and the four items are the four leaves. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 (-2) 5 (-10) 10 (-4) 5) := by
  obtain ⟨D⟩ := exists_placeData 1 (-2) 5 (-10) 10 (-4) ℚ (separable_sextPoly (by norm_num))
    (by norm_num)
  obtain ⟨D'⟩ := exists_placeData 1 (-2) 5 (-10) 10 (-4) (ZMod 5)
    (separable_sextPoly (by decide)) (by decide)
  obtain ⟨red, hcompat, hker⟩ := exists_reduction (p := 5) (by norm_num) D D'
    (separable_sextPoly (by decide))
  exact ⟨{ J := D.Pic
           addCommGroup := inferInstance
           fin := finite_pic D
           J' := D'.Pic
           addCommGroup' := inferInstance
           aj := D.aj
           aj_injective := aj_injective_of_separable D (separable_sextPoly (by norm_num))
           aj' := D'.aj
           red := red
           red_ker_torsionFree := hker
           red_aj := hcompat }⟩

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

open Polynomial

/-- The level-`13` sextic as a polynomial, in numeral form (PROVEN). -/
lemma sextPoly_eq {K : Type*} [CommRing K] :
    sextPoly 1 4 6 2 1 2 K
      = X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 + 6 * X ^ 2 + 4 * X + 1 := by
  simp only [sextPoly]
  push_cast
  ring

/-- Its derivative (PROVEN). -/
lemma derivative_sextPoly_eq {K : Type*} [CommRing K] :
    derivative (X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 + 6 * X ^ 2 + 4 * X + 1 : K[X])
      = 6 * X ^ 5 + 10 * X ^ 4 + 4 * X ^ 3 + 6 * X ^ 2 + 12 * X + 4 := by
  simp [derivative_pow, map_ofNat]
  ring

/-- **The level-`13` sextic is separable over every field in which `104 ≠ 0`** (PROVEN, by
an explicit Bézout certificate).

`f` and `f'` satisfy `U·f + V·f' = 104` with

    U = 300x⁴ + 416x³ + 54x² + 252x + 548,   V = −50x⁵ − 86x⁴ − 21x³ − 87x² − 278x − 111

an identity of polynomials with INTEGER coefficients, so it holds over every commutative
ring and `ring` checks it; dividing by `104` gives `IsCoprime f f'`.  (PARI/GP found the
certificate; the kernel verifies it.  `104 = 2³·13` and `disc f = −2¹²·13²`, which is why
`3` is a good prime: `104` is a unit in `𝔽₃`.) -/
lemma separable_sextPoly {K : Type} [Field K] (h : (104 : K) ≠ 0) :
    (sextPoly 1 4 6 2 1 2 K).Separable := by
  rw [Polynomial.separable_def', sextPoly_eq, derivative_sextPoly_eq]
  refine ⟨C (104 : K)⁻¹ * (300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548),
    C (104 : K)⁻¹ * (-50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 - 278 * X - 111), ?_⟩
  have hc : (C (104 : K)⁻¹) * (104 : K[X]) = 1 := by
    rw [show ((104 : K[X])) = C (104 : K) by simp [map_ofNat], ← C_mul, inv_mul_cancel₀ h, C_1]
  calc C (104 : K)⁻¹ * (300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548)
        * (X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 + 6 * X ^ 2 + 4 * X + 1)
      + C (104 : K)⁻¹ * (-50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 - 278 * X - 111)
        * (6 * X ^ 5 + 10 * X ^ 4 + 4 * X ^ 3 + 6 * X ^ 2 + 12 * X + 4)
      = C (104 : K)⁻¹ * (104 : K[X]) := by ring
    _ = 1 := hc

/-- **LEAF (obligation 4, LEVEL-SPECIFIC HALF) AT LEVEL `13`: `rank J₁(13)(ℚ) = 0`, in the
form `J₁(13)(ℚ) = 2·J₁(13)(ℚ)`.**

The level-`13` counterpart of `X18.two_divisible_pic`, and what is left of `finite_pic`
once the generic Mordell–Weil node `fg_pic` has been split off; see the `MordellWeil`
section docstring for why the cut runs here.  `D.Pic` is `Pic⁰` of the smooth projective
model of `y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1` over `ℚ`, which is `J₁(13)(ℚ)`.  The
classical proof of rank `0` is Mazur–Tate, *Points of order 13 on elliptic curves*, Invent.
Math. 22 (1973), subsumed in Mazur, IHÉS 47 (1977), Thm 7.

As at level `18`, `2`-divisibility rather than "torsion" is the honest phrasing: it is the
direct output of a `2`-descent and does not presuppose finite generation.

## The arithmetic that makes this true (untrusted searchers, not proofs)

Magma, re-run from scratch on 2026-07-28 (`SetClassGroupBounds("GRH")`), reproducing the
earlier runs and adding the `2`-Selmer computation this leaf rests on:

    C : y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1
    Genus(C)                       = 2
    Factorization(Discriminant(C)) = 2²⁰ · 13²     — so `3` is a good prime
    Factorization(f)               = irreducible of degree 6
    TorsionSubgroup(J)             = ℤ/19          — ODD order
    #TwoSelmerGroup(J)             = 1             — so `J(ℚ)/2J(ℚ) = 0`
    RankBound(J)                   = 0             — SHARP
    #J(𝔽₃) = #J(𝔽₅)                = 19            — reduction at `3` is an ISO
    #C(𝔽₃)                         = 6             — matches `card_X13_F3`
    Chabauty0(J) = {(1 : ±1 : 0), (−1 : ±1 : 1), (0 : ±1 : 1)}   — SIX points

`Sel₂ = 0` gives this leaf directly: `J(ℚ)/2J(ℚ)` injects into it.  `#J(𝔽₃) = 19 = #J(ℚ)`
is why the argument is sharp here: reduction on the Jacobian is an isomorphism, so
injectivity is not merely available but forced.  `p = 5` gives the same certificate
independently, which is a second check on item 3.  PARI corroborates the point count
through the zeta numerator: `hyperellcharpoly(Mod(1,3)*f) = T⁴ + 2T³ + T² + 6T + 9`, whose
`T³` coefficient gives `#C(𝔽₃) = 3 + 1 + 2 = 6` and whose value at `1` gives `#J(𝔽₃) = 19`.

Refuting checks: `#TwoSelmerGroup(Jacobian(HyperellipticCurve(f))) ≠ 1`; a positive lower
bound from `RankBound(J)`; a torsion subgroup other than `ℤ/19`;
`#Jacobian(ChangeRing(C, GF(3))) ≠ 19`; a seventh point from `Chabauty0`.  A FIFTH
independent Magma run on 2026-07-28 reproduced the table exactly — `genus 2`, `f`
irreducible, `disc = 2²⁰·13²`, `TorsionSubgroup = ℤ/19`, `#TwoSelmerGroup = 1`,
`RankBounds = [0, 0]`.

## ATOMICITY AUDIT (2026-07-28)

The axes searched, and the refuting check for each, are written out in full on
`X18.two_divisible_pic`; every one of them applies verbatim here, the two leaves differing
only in the sextic and the good prime.  The load-bearing item is the first: a `2`-descent
cut needs the map `δ : Pic → L*/L*²`, `L = ℚ[x]/(f)`, pinned by a CONSTRUCTION, and pinning
it by its values on rational points is powerless because `#Sel₂ = 1` makes the genuine `δ`
identically zero on `J(ℚ)` — so the junk model `δ = 0` meets every such constraint and
reduces the cut to this leaf's own conclusion.  Pinning needs residue fields `κ(v)` and
their norms, which `PlaceData` deliberately does not carry.

The level-`13` specifics that strengthen the same verdict: `IsSimple(JOne(13)) = true`
(Magma `ModAbVar`, 2026-07-28) confirms by a second, independent method the `ℚ`-simplicity
already recorded below from the diamond `⟨5⟩`, so the elliptic axis is doubly closed here;
and `#J(𝔽₃) = 19 = #J(ℚ)` makes reduction at `3` an isomorphism, which is the sharpest that
the reduction axis can ever be — and it still yields no rank information, since the kernel
of reduction is where all the rank would live. -/
theorem two_divisible_pic (D : PlaceData 1 4 6 2 1 2 ℚ) (z : D.Pic) :
    ∃ w : D.Pic, z = 2 • w := sorry

/-- **`J₁(13)(ℚ)` is FINITE** — obligation 4 at level `13` — a LEAF from its creation until
2026-07-28, now PROVEN over the generic Mordell–Weil node `fg_pic` and the level-specific
rank-`0` leaf `two_divisible_pic` above.

The smoothness side condition is `separable_sextPoly` at `104 ≠ 0` in `ℚ`. -/
theorem finite_pic (D : PlaceData 1 4 6 2 1 2 ℚ) : Finite D.Pic :=
  finite_of_fg_of_two_divisible (fg_pic D (separable_sextPoly (by norm_num)))
    (two_divisible_pic D)

/-- **`Pic⁰(X_1(13))` exists, has rank `0`, and reduces injectively at `3`** — a LEAF from
its creation on 2026-07-27 until later the same day, now PROVEN by the same decomposition
as at level `18`.

The four obligations, at `p = 3` instead of `p = 5`:

1. `Pic⁰` of `y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`, as a group: `exists_placeData`
   followed by the DEFINITION `PlaceData.Pic`;
2. Abel–Jacobi injective because the genus is `≥ 1`: `aj_injective_of_separable`;
3. good reduction at `3`, the reduction homomorphism, its compatibility with `redPt`, and
   torsion-freeness of its kernel: `exists_reduction`;
4. `rank J(ℚ) = 0` together with Mordell–Weil: `finite_pic` above, itself PROVEN since
   2026-07-28 over the generic `fg_pic` and the level-specific `two_divisible_pic`.

Leaves 1–3 are shared verbatim with level `18` — they are generic in the sextic and the
prime, as are the two Mordell–Weil leaves under `fg_pic` — so the only level-`13`-specific
obligations left are `two_divisible_pic` and the smoothness certificate
`separable_sextPoly`, the latter PROVEN.

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
sextic and the prime.  That is now literally true of the code: leaves 1–3 are the same
three declarations at both levels. -/
theorem exists_jacobianPackage :
    Nonempty (JacobianPackage 1 4 6 2 1 2 3) := by
  obtain ⟨D⟩ := exists_placeData 1 4 6 2 1 2 ℚ (separable_sextPoly (by norm_num))
    (by norm_num)
  obtain ⟨D'⟩ := exists_placeData 1 4 6 2 1 2 (ZMod 3)
    (separable_sextPoly (by decide)) (by decide)
  obtain ⟨red, hcompat, hker⟩ := exists_reduction (p := 3) (by norm_num) D D'
    (separable_sextPoly (by decide))
  exact ⟨{ J := D.Pic
           addCommGroup := inferInstance
           fin := finite_pic D
           J' := D'.Pic
           addCommGroup' := inferInstance
           aj := D.aj
           aj_injective := aj_injective_of_separable D (separable_sextPoly (by norm_num))
           aj' := D'.aj
           red := red
           red_ker_torsionFree := hker
           red_aj := hcompat }⟩

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