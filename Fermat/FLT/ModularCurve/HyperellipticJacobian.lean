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
      → finite_isPlaceFun         PROVEN 2026-07-30: finitely many zeros/poles, by classifying
                                  every place as an `ordAt` of one of the two towers
      → exists_placeSystem        PROVEN: the TAUTOLOGICAL system; ord_complete is rfl
      → exists_isPlaceFun_of_affPt  PROVEN 2026-07-30: the affine place, via the Dedekind
                                  ring of integers and the hyperelliptic involution
      → exists_isPlaceFun_of_infPt  PROVEN 2026-07-30: the branches at infinity, by embedding
                                  in K((t)) with x ↦ 1/t, which makes ord x = −1 exact
      → exists_isPlaceOfPt        PROVEN: from the two, through ord_complete
      → exists_placeData          PROVEN: assembled, with pt_injective proven
      → finrank_residue_pt_eq_one PROVEN 2026-07-30: κ(v) = K, over the two `exists_localDenom`
                                  leaves, both now proven by a descent on the denominator
    degOf_divisor_eq_zero         LEAF: Σ_v ord_v(g)·[κ(v):K] = 0  (Stichtenoth I.4.11)
      → exists_degreeMap          PROVEN: assembled over the constructed `degOf`
    isRationalGenerator_of_divisor_eq_sub_single
                                  LEAF: a single simple pole forces F = K(g)
    not_isRationalGenerator       LEAF: F is NOT rational — the genus, and the only
                                  place where separability does any work
      → sub_single_pt_notMem_princ PROVEN: assembled, over `princ = range divisor`
      → aj_injective_of_separable PROVEN: assembled
    exists_smoothModel            LEAF: the ℤ_p-model — divisor specialisation and the
                                        formal logarithm, in one existential
      → exists_reductionFiltration PROVEN: red descends, the four filtration axioms
      → exists_reduction          PROVEN: torsion-freeness from the filtration
    exists_descentHeight_pic      LEAF: a Northcott height on Pic⁰(X_ℚ)
    finite_quotient_psmul_pic     LEAF: weak Mordell–Weil, Pic⁰/p·Pic⁰ is finite
      → fg_pic                    PROVEN: Mordell–Weil, by the descent theorem
    X18.two_divisible_pic / X13.two_divisible_pic
                                  LEAF: rank 0 — every class is 2-divisible
      → X18.finite_pic / X13.finite_pic
                                  PROVEN: finite, from `fg_pic` and 2-divisibility
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

**DO NOT TRUST A LEAF COUNT WRITTEN HERE — ASK THE COMPILER.**  Two branches
amended this paragraph on the same day, one saying "eight" and one saying "TEN",
and the merged file has neither number: at the release-18 merge the
`declaration uses 'sorry'` set of this module is

    degOf_poleDivisor_eq_finrank_of_transcendental,
    exists_smoothModel, exists_cubeModel_pic, exists_geomPic,
    geomPic_bc_injective, geomPic_descent, geomPic_divisible_place,
    finite_kummerCochains_pic, and `two_divisible_pic` at BOTH levels

— TEN declarations, as of 2026-07-30 (a comment-stripped `sorry`-token count agrees, so there
are no anonymous inner sorries).  The whole of obligations 1b and 1c, and obligation 2a's
residue-field half, closed that day: `finite_isPlaceFun`, `exists_isPlaceFun_of_affPt`,
`exists_isPlaceFun_of_infPt` and both `exists_localDenom_*` (hence
`finrank_residue_pt_eq_one`).  `degOf_divisor_eq_zero`,
`isRationalGenerator_of_divisor_eq_sub_single` and `not_isRationalGenerator` had already been
reduced to `degOf_poleDivisor_eq_finrank_of_transcendental`, which is now the single remaining
node of the divisor theory — Stichtenoth I.4.11, weak approximation plus a dimension count.

(`geomPic_divisible_place` replaced `geomPic_divisible` in that set on
2026-07-30: the general `∀ n ≠ 0, ∀ y` form is now PROVEN from the
single-place, single-prime instance, so the leaf moved rather than
multiplied — the count is unchanged.)

`exists_functionFieldData`, `exists_placeSystem`, `exists_isPlaceOfPt`,
`exists_degreeMap`, `sub_single_pt_notMem_princ`, `exists_descentHeight_pic`,
`geomPic_divisible`, `divisible_of_prime`, `divisible_of_finsuppSingle`,
`finite_quotient_psmul_pic` and both `finite_pic` are PROVEN; earlier text here
listing them as open is stale.  All of the above except `two_divisible_pic` are
generic in the sextic and
the prime, so ONE genus-`2` divisor-theory development closes them for both levels at once;
only `X18.two_divisible_pic` and `X13.two_divisible_pic`, which are `rank J(ℚ) = 0`, are
specific to the curves.  (The count rose from five while
`exists_placeData`, `aj_injective_of_separable`, `exists_reduction` and both `finite_pic`
all became PROVEN:
that is decomposition, and with it the two arguments that used to be sketched only in prose
— `pt_injective` from the valuation axioms, and torsion-freeness from a formal-group
filtration — are now machine-checked.)  Read the
`two_divisible_pic` docstrings for the Magma certificates (re-run from scratch 2026-07-27: rank
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
-- `CubeModel` / `CubeEmbedding` / `ProjectiveHeightSource`, and the PROVEN chain from a
-- projective embedding with the theorem of the cube to a `DescentHeight`.  This adds no
-- module to the cone of the only consumer of this file: `FreyCurve/MazurTorsion.lean`
-- already `public import`s `ModularCurve/X0.lean`, which imports it.
public import Fermat.FLT.Mathlib.NumberTheory.ProjectiveHeight
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
-- the formal logarithm of the Jacobian over `ℤ_p`, whose target is `ℤ_[p] × ℤ_[p]`: this
-- is what carries the filtration of `ker red` in `SmoothModel`, and `PadicInt`'s
-- `mem_span_pow_iff_le_valuation` is what makes the filtration separated
public import Mathlib.NumberTheory.Padics.PadicIntegers
-- `finrank_residue_pt_eq_one` and the residue-field arguments around it
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
-- `no_sextic_sq_of_ratFunc`, the genus: the pencil count needs an algebraic closure (six
-- distinct roots, and every unit a square), Frobenius on a perfect field for the
-- characteristic-`p` descent, `expand`/`contract` for the `p`-th-power shape, `a^n ∣ b^n → a ∣ b`
-- and `exists_associated_pow_of_mul_eq_pow'` in the UFD `L[X]`
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DedekindDomain.Factorization

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
| 3 | `exists_reduction` — good reduction: the homomorphism, its compatibility with `redPt`, and torsion-freeness of its kernel | PROVEN 2026-07-28 from `exists_reductionFiltration`, itself PROVEN the same day from `exists_smoothModel` |
| 4 | `X18.finite_pic`, `X13.finite_pic` — Mordell–Weil together with `rank J(ℚ) = 0` | PROVEN 2026-07-28 from `fg_pic` (over `exists_descentHeight_pic`, `finite_quotient_psmul_pic`) and `two_divisible_pic` |

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

/-- **`o` is the valuation of the rational point `P`** — `IsPlaceOfPt` with the place
replaced by a raw valuation function, so that a place can be produced through
`PlaceSystem.ord_complete` rather than exhibited inside a given system. -/
def IsPlaceFunOfPt {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (o : E.F → ℤ)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) : Prop :=
  match P with
  | Sum.inl q => 0 < o (E.xx - algebraMap K E.F q.1.1) ∧ 0 < o (E.yy - algebraMap K E.F q.1.2)
  | Sum.inr s => o E.xx = -1 ∧ -3 < o (E.yy - (if s then 1 else -1) * E.xx ^ 3)

/-! ### Places from the Dedekind ring of integers (PROVEN, 2026-07-30)

The machinery that closes the affine half of obligation 1c, and the reusable half of the
infinite half.  It replaces the Laurent-series/Hensel route the docstring below proposes by
the Dedekind one, which mathlib already carries: `A = integralClosure K[X] F` is a Dedekind
domain with `Frac A = F` (`integralClosure.isDedekindDomain`, once the tower
`K[X] ⊆ K(x) ⊆ F` is in place and `F/K(x)` is finite separable), and each of its height-one
primes gives a normalised `K`-trivial discrete valuation of `F` — that is `ordAt`, whose
five `IsPlaceFun` axioms are `isPlaceFun_ordAt`.

The point `(a, b)` is then reached by LYING OVER the maximal ideal `(X − a)` of `K[X]`, and
the two branches `y = ±b` are separated by the HYPERELLIPTIC INVOLUTION rather than by a
count of primes: `exists_isPlaceFun_of_affPt_upToSign` produces a place at which `x − a` is
positive and at least ONE of `y ∓ b` is, and precomposing with the `K(x)`-automorphism
`y ↦ −y` (built through `AdjoinRoot (Y² − f)`, whose irreducibility is the file's own
`not_isSquare_sextPoly`) exchanges the two disjuncts.  That is where `2 ≠ 0` is used, and
`hsep` enters only through the irreducibility.
-/

section PlacesFromDedekind

open IsDedekindDomain
open scoped WithZero

namespace PlaceFromDedekind

variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {A : Type} [CommRing A] [IsDedekindDomain A]
  [Algebra A F] [IsFractionRing A F]

/-- The `ℤ`-valued additive valuation attached to a height-one prime of `A`, on the
fraction field `F`. -/
noncomputable def ordAt (v : HeightOneSpectrum A) (z : F) : ℤ :=
  - WithZero.log (v.valuation F z)

lemma ordAt_zero (v : HeightOneSpectrum A) : ordAt (F := F) v 0 = 0 := by
  simp [ordAt]

lemma valuation_ne_zero (v : HeightOneSpectrum A) {z : F} (hz : z ≠ 0) :
    v.valuation F z ≠ 0 := by
  simpa [Valuation.ne_zero_iff] using hz

lemma ordAt_mul (v : HeightOneSpectrum A) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ordAt v (a * b) = ordAt v a + ordAt v b := by
  simp only [ordAt, map_mul]
  rw [WithZero.log_mul (valuation_ne_zero v ha) (valuation_ne_zero v hb)]
  ring

lemma ordAt_ultra (v : HeightOneSpectrum A) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) : min (ordAt v a) (ordAt v b) ≤ ordAt v (a + b) := by
  have hle : v.valuation F (a + b) ≤ max (v.valuation F a) (v.valuation F b) :=
    (v.valuation F).map_add a b
  have hmax : max (v.valuation F a) (v.valuation F b) ≠ 0 := by
    rcases max_cases (v.valuation F a) (v.valuation F b) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · exact valuation_ne_zero v ha
    · exact valuation_ne_zero v hb
  have hlog : WithZero.log (v.valuation F (a + b))
      ≤ WithZero.log (max (v.valuation F a) (v.valuation F b)) :=
    (WithZero.log_le_log (valuation_ne_zero v hab) hmax).2 hle
  have hmaxlog : WithZero.log (max (v.valuation F a) (v.valuation F b))
      = max (WithZero.log (v.valuation F a)) (WithZero.log (v.valuation F b)) := by
    rcases max_cases (v.valuation F a) (v.valuation F b) with ⟨h, hle'⟩ | ⟨h, hlt⟩
    · rw [h, max_eq_left ((WithZero.log_le_log (valuation_ne_zero v hb)
        (valuation_ne_zero v ha)).2 hle')]
    · rw [h, max_eq_right (le_of_lt ((WithZero.log_lt_log (valuation_ne_zero v ha)
        (valuation_ne_zero v hb)).2 hlt))]
  rw [hmaxlog] at hlog
  simp only [ordAt]
  omega

/-- `ordAt` is normalised: some element has order exactly `1`. -/
lemma ordAt_normalised (v : HeightOneSpectrum A) : ∃ t : F, ordAt v t = 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  exact ⟨π, by simp [ordAt, hπ]⟩

section Const

variable [Algebra K A] [IsScalarTower K A F]

/-- A nonzero constant is a unit of `A`, so it has valuation `1`. -/
lemma valuation_algebraMap_eq_one (v : HeightOneSpectrum A) {a : K} (ha : a ≠ 0) :
    v.valuation F (algebraMap K F a) = 1 := by
  have hu : IsUnit (algebraMap K A a) :=
    isUnit_iff_exists_inv.2 ⟨algebraMap K A a⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ ha, map_one]⟩
  have hnm : algebraMap K A a ∉ v.asIdeal := fun hmem =>
    v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  rw [IsScalarTower.algebraMap_apply K A F]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hnm

lemma ordAt_algebraMap (v : HeightOneSpectrum A) (a : K) (ha : a ≠ 0) :
    ordAt (F := F) v (algebraMap K F a) = 0 := by
  simp [ordAt, valuation_algebraMap_eq_one (F := F) v ha]

/-- **The place attached to a height-one prime**, in the shape `IsPlaceFun` asks for. -/
theorem isPlaceFun_ordAt (v : HeightOneSpectrum A) :
    IsPlaceFun K F (ordAt (F := F) v) where
  map_zero := ordAt_zero v
  map_mul := ordAt_mul v
  ultra := ordAt_ultra v
  map_algebraMap := ordAt_algebraMap v
  normalised := ordAt_normalised v

/-- An element of the prime has strictly positive order. -/
lemma ordAt_pos_of_mem (v : HeightOneSpectrum A) {r : A} (hr : r ∈ v.asIdeal) (hr0 : r ≠ 0) :
    0 < ordAt (F := F) v (algebraMap A F r) := by
  have hlt : v.valuation F (algebraMap A F r) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v r).2 hr
  have hr0' : algebraMap A F r ≠ 0 :=
    (map_ne_zero_iff (algebraMap A F) (IsFractionRing.injective A F)).2 hr0
  have hne : v.valuation F (algebraMap A F r) ≠ 0 := valuation_ne_zero v hr0'
  have : WithZero.log (v.valuation F (algebraMap A F r)) < WithZero.log (1 : ℤᵐ⁰) :=
    (WithZero.log_lt_log hne one_ne_zero).2 hlt
  simp only [WithZero.log_one] at this
  simpa [ordAt] using this

end Const

/-! ### From a proper ideal of the ring of integers to a place -/

section Tower

variable {K F : Type} [Field K] [Field F]
  [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K K[X] F] [IsScalarTower K[X] (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

noncomputable instance : IsFractionRing (↥(integralClosure K[X] F)) F :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc K) F

noncomputable instance : IsDedekindDomain (↥(integralClosure K[X] F)) :=
  integralClosure.isDedekindDomain K[X] (RatFunc K) F

/-- **Every proper ideal of the ring of integers is cut out by a place.**  A maximal ideal
containing it is a nonzero prime of a Dedekind domain, hence a height-one prime, and its
adic valuation is a normalised `K`-trivial discrete valuation of `F` that is positive on
every nonzero member of the ideal. -/
theorem exists_isPlaceFun_of_ne_top (I : Ideal (↥(integralClosure K[X] F))) (hI : I ≠ ⊤)
    (hI0 : I ≠ ⊥) :
    ∃ o : F → ℤ, IsPlaceFun K F o ∧ ∀ z ∈ I, (z : F) ≠ 0 → 0 < o (z : F) := by
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  have hm0 : m ≠ ⊥ := fun h => hI0 (le_bot_iff.1 (h ▸ hIm))
  refine ⟨ordAt (F := F) ⟨m, hm.isPrime, hm0⟩, isPlaceFun_ordAt _, fun z hz hz0 => ?_⟩
  have : (z : F) = algebraMap (↥(integralClosure K[X] F)) F z := rfl
  rw [this]
  exact ordAt_pos_of_mem _ (hIm hz) (fun h => hz0 (by rw [h]; simp))

omit [Algebra K F] [IsScalarTower K K[X] F] in
/-- An integral element has nonnegative order at every place of the ring of integers. -/
lemma ordAt_nonneg_of_isIntegral
    (v : HeightOneSpectrum ↥(integralClosure K[X] F)) {z : F} (hz : IsIntegral K[X] z) :
    0 ≤ ordAt (F := F) v z := by
  have hzA : z = algebraMap ↥(integralClosure K[X] F) F ⟨z, hz⟩ := rfl
  have hle : v.valuation F z ≤ 1 := by
    rw [hzA]; exact v.valuation_le_one _
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [ordAt]
  · have := (WithZero.log_le_log (valuation_ne_zero v hz0) (one_ne_zero (α := ℤᵐ⁰))).2 hle
    simp only [WithZero.log_one] at this
    simpa [ordAt] using this

omit [Algebra K F] [IsScalarTower K K[X] F] [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F] in
lemma algebraMap_poly_injective : Function.Injective (algebraMap K[X] F) := by
  rw [IsScalarTower.algebraMap_eq K[X] (RatFunc K) F]
  exact (algebraMap (RatFunc K) F).injective.comp (IsFractionRing.injective K[X] (RatFunc K))

omit [Algebra K F] [IsScalarTower K K[X] F] in
/-- **Lying over**: every nonzero maximal ideal of `K[X]` is dominated by a place of `F`. -/
theorem exists_heightOneSpectrum_over_maximal (m : Ideal K[X]) [hm : m.IsMaximal]
    (hm0 : m ≠ ⊥) :
    ∃ v : HeightOneSpectrum ↥(integralClosure K[X] F),
      ∀ p ∈ m, algebraMap K[X] F p ≠ 0 → 0 < ordAt (F := F) v (algebraMap K[X] F p) := by
  have hinjF : Function.Injective (algebraMap K[X] F) := algebraMap_poly_injective (F := F)
  have hinj : Function.Injective (algebraMap K[X] ↥(integralClosure K[X] F)) :=
    fun p q hpq => hinjF (congrArg Subtype.val hpq)
  obtain ⟨Q, hQ, hQm⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥(integralClosure K[X] F)) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hm0 (by rw [← hQm, h, Ideal.comap_bot_of_injective _ hinj])
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, fun p hp hp0 => ?_⟩
  have hmem : (algebraMap K[X] ↥(integralClosure K[X] F) p) ∈ Q := by
    have hc : p ∈ Q.comap (algebraMap K[X] ↥(integralClosure K[X] F)) := by rw [hQm]; exact hp
    exact hc
  have hne : (algebraMap K[X] ↥(integralClosure K[X] F) p) ≠ 0 := fun h => hp0 (by
    have : algebraMap K[X] F p
        = algebraMap ↥(integralClosure K[X] F) F (algebraMap K[X] _ p) := rfl
    rw [this, h, map_zero])
  simpa using ordAt_pos_of_mem (F := F) ⟨Q, hQ.isPrime, hQ0⟩ hmem hne

omit [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F] in
lemma algebraMap_poly_eq_aeval {xx : F} (hxx : algebraMap K[X] F Polynomial.X = xx)
    (p : K[X]) : algebraMap K[X] F p = Polynomial.aeval xx p := by
  have h : (IsScalarTower.toAlgHom K K[X] F) = (Polynomial.aeval xx : K[X] →ₐ[K] F) :=
    Polynomial.algHom_ext (by simpa using hxx)
  exact congrArg (fun φ => φ p) h

/-- **The place of an affine rational point, up to the sign of the ordinate.**

Lying over `(X − a)` produces a place `v` at which `x − a` is positive; the factorisation
`(y − b)(y + b) = (x − a)·h(x)` then forces at least one of `y ∓ b` to be positive there,
since both are integral over `K[X]` and hence of nonnegative order.  Which of the two it is
is not decided here — that is the hyperelliptic involution's job. -/
theorem exists_isPlaceFun_of_affPt_upToSign {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ}
    {xx yy : F} (hxx : algebraMap K[X] F Polynomial.X = xx)
    (heqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx) (a b : K)
    (hab : b ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ a) :
    ∃ o : F → ℤ, IsPlaceFun K F o ∧ 0 < o (xx - algebraMap K F a) ∧
      (0 < o (yy - algebraMap K F b) ∨ 0 < o (yy + algebraMap K F b)) := by
  classical
  have hinjF : Function.Injective (algebraMap K[X] F) := algebraMap_poly_injective (F := F)
  have halg := algebraMap_poly_eq_aeval hxx
  have hCa : ∀ c : K, algebraMap K[X] F (Polynomial.C c) = algebraMap K F c := fun c => by
    rw [IsScalarTower.algebraMap_apply K K[X] F c]; rfl
  -- the maximal ideal `(X − a)` of `K[X]`
  have hirr : Irreducible (Polynomial.X - Polynomial.C a : K[X]) := Polynomial.irreducible_X_sub_C a
  have hXa0 : (Polynomial.X - Polynomial.C a : K[X]) ≠ 0 := hirr.ne_zero
  haveI hmax : (Ideal.span {Polynomial.X - Polynomial.C a} : Ideal K[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  have hm0 : (Ideal.span {Polynomial.X - Polynomial.C a} : Ideal K[X]) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hXa0
  obtain ⟨v, hv⟩ := exists_heightOneSpectrum_over_maximal (F := F) _ hm0
  refine ⟨ordAt (F := F) v, isPlaceFun_ordAt v, ?_, ?_⟩
  · have hXaF : algebraMap K[X] F (Polynomial.X - Polynomial.C a) = xx - algebraMap K F a := by
      rw [map_sub, hxx, hCa]
    have hne : algebraMap K[X] F (Polynomial.X - Polynomial.C a) ≠ 0 :=
      fun h => hXa0 (hinjF (by rw [h, map_zero]))
    have := hv _ (Ideal.mem_span_singleton_self _) hne
    rwa [hXaF] at this
  · -- the factorisation `(y − b)(y + b) = (x − a)·h(x)`
    have hroot : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K - Polynomial.C (sext c₀ c₁ c₂ c₃ c₄ c₅ a)).IsRoot a := by
      simp [Polynomial.IsRoot, eval_sextPoly]
    obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
    have hfac : (yy - algebraMap K F b) * (yy + algebraMap K F b)
        = (xx - algebraMap K F a) * Polynomial.aeval xx h := by
      have e1 : Polynomial.aeval xx (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
            - Polynomial.C (sext c₀ c₁ c₂ c₃ c₄ c₅ a))
          = Polynomial.aeval xx ((Polynomial.X - Polynomial.C a) * h) := by rw [hh]
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
        aeval_sextPoly] at e1
      have hb : (algebraMap K F b) ^ 2 = algebraMap K F (sext c₀ c₁ c₂ c₃ c₄ c₅ a) := by
        rw [← map_pow, hab]
      linear_combination heqn + e1 - hb
    -- everything in sight is integral over `K[X]`, so of nonnegative order
    have hyint : IsIntegral K[X] yy := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K),
        Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [halg, aeval_sextPoly, heqn, sub_self]
    have hbint : IsIntegral K[X] (algebraMap K F b) := by
      refine ⟨Polynomial.X - Polynomial.C (Polynomial.C b), Polynomial.monic_X_sub_C _, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [hCa, sub_self]
    have hhint : IsIntegral K[X] (Polynomial.aeval xx h) := by
      refine ⟨Polynomial.X - Polynomial.C h, Polynomial.monic_X_sub_C _, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      rw [halg, sub_self]
    have hn1 : 0 ≤ ordAt (F := F) v (yy - algebraMap K F b) :=
      ordAt_nonneg_of_isIntegral v (hyint.sub hbint)
    have hn2 : 0 ≤ ordAt (F := F) v (yy + algebraMap K F b) :=
      ordAt_nonneg_of_isIntegral v (hyint.add hbint)
    have hn3 : 0 ≤ ordAt (F := F) v (Polynomial.aeval xx h) :=
      ordAt_nonneg_of_isIntegral v hhint
    -- nonvanishing
    have hxa : xx - algebraMap K F a ≠ 0 := by
      intro hcon
      exact hXa0 (hinjF (by
        rw [map_zero, map_sub, hxx, hCa]; exact hcon))
    have hprod : (yy - algebraMap K F b) * (yy + algebraMap K F b) ≠ 0 := by
      rw [hfac]
      refine mul_ne_zero hxa (fun hcon => ?_)
      have hh0 : h = 0 := hinjF (by rw [map_zero, halg]; exact hcon)
      have : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K = Polynomial.C (sext c₀ c₁ c₂ c₃ c₄ c₅ a) := by
        have := hh; rw [hh0, mul_zero, sub_eq_zero] at this; exact this
      have hd := natDegree_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
      rw [this, Polynomial.natDegree_C] at hd
      simp at hd
    have h1 : yy - algebraMap K F b ≠ 0 := left_ne_zero_of_mul hprod
    have h2' : yy + algebraMap K F b ≠ 0 := right_ne_zero_of_mul hprod
    have hh0 : Polynomial.aeval xx h ≠ 0 := by
      intro hcon
      rw [hfac, hcon, mul_zero] at hprod
      exact hprod rfl
    have hpos : 0 < ordAt (F := F) v (xx - algebraMap K F a) := by
      have hXaF : algebraMap K[X] F (Polynomial.X - Polynomial.C a) = xx - algebraMap K F a := by
        rw [map_sub, hxx, hCa]
      have hne : algebraMap K[X] F (Polynomial.X - Polynomial.C a) ≠ 0 :=
        fun hq => hXa0 (hinjF (by rw [hq, map_zero]))
      have := hv _ (Ideal.mem_span_singleton_self _) hne
      rwa [hXaF] at this
    have hsum := ordAt_mul (F := F) v _ _ h1 h2'
    rw [hfac, ordAt_mul (F := F) v _ _ hxa hh0] at hsum
    omega

omit [Algebra K[X] F] [Algebra (RatFunc K) F] [IsScalarTower K K[X] F]
  [IsScalarTower K[X] (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F] in
/-- Precomposing a place with a `K`-fixing surjective endomorphism gives a place. -/
lemma isPlaceFun_comp {o : F → ℤ} (h : IsPlaceFun K F o) (σ : F →+* F)
    (hsurj : Function.Surjective σ) (hK : ∀ a : K, σ (algebraMap K F a) = algebraMap K F a) :
    IsPlaceFun K F (o ∘ σ) where
  map_zero := by simpa using h.map_zero
  map_mul a b ha hb := by
    simp only [Function.comp_apply, map_mul]
    exact h.map_mul _ _ (fun hc => ha (σ.injective (by rw [hc, map_zero])))
      (fun hc => hb (σ.injective (by rw [hc, map_zero])))
  ultra a b ha hb hab := by
    simp only [Function.comp_apply, map_add]
    exact h.ultra _ _ (fun hc => ha (σ.injective (by rw [hc, map_zero])))
      (fun hc => hb (σ.injective (by rw [hc, map_zero])))
      (fun hc => hab (σ.injective (by rw [map_add, map_zero]; exact hc)))
  map_algebraMap a ha := by
    simp only [Function.comp_apply, hK]
    exact h.map_algebraMap a ha
  normalised := by
    obtain ⟨t, ht⟩ := h.normalised
    obtain ⟨t', rfl⟩ := hsurj t
    exact ⟨t', ht⟩

end Tower

section Affine

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-- The `K[X]`-algebra structure on `E.F` given by `X ↦ E.xx`. -/
@[reducible] noncomputable def xAlg (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) : Algebra K[X] E.F :=
  (Polynomial.aeval E.xx : K[X] →ₐ[K] E.F).toRingHom.toAlgebra

/-- **LEAF (obligation 1c, AFFINE HALF), PROVEN**: an affine rational point carries a
valuation. -/
theorem exists_isPlaceFun_of_affPt' (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0)
    (q : AffPt c₀ c₁ c₂ c₃ c₄ c₅ K) :
    ∃ o : E.F → ℤ, IsPlaceFun K E.F o ∧
      0 < o (E.xx - algebraMap K E.F q.1.1) ∧ 0 < o (E.yy - algebraMap K E.F q.1.2) := by
  classical
  letI : Algebra K[X] E.F := xAlg E
  have halg : ∀ p : K[X], algebraMap K[X] E.F p = Polynomial.aeval E.xx p := fun _ => rfl
  haveI : IsScalarTower K K[X] E.F :=
    IsScalarTower.of_algebraMap_eq fun a => by simp [halg]
  have hinj : Function.Injective (algebraMap K[X] E.F) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    exact E.transcendental_xx ⟨p, hp0, by rw [← halg]; exact hp⟩
  letI : Algebra (RatFunc K) E.F := (IsFractionRing.lift (A := K[X]) hinj).toAlgebra
  haveI : IsScalarTower K[X] (RatFunc K) E.F :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hinj p).symm
  have hdown : ∀ p : K[X],
      algebraMap (RatFunc K) E.F (algebraMap K[X] (RatFunc K) p)
        = Polynomial.aeval E.xx p := fun p => by
    rw [← IsScalarTower.algebraMap_apply, halg]
  have hsext0 : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K ≠ 0 := fun h => by
    have hd := natDegree_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
    rw [h] at hd; simp at hd
  have hα₀F : algebraMap (RatFunc K) E.F
      (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) = E.yy ^ 2 := by
    rw [hdown, aeval_sextPoly, E.eqn]
  have hα₀0 : algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) ≠ 0 := fun h =>
    hsext0 ((IsFractionRing.injective K[X] (RatFunc K)) (by rw [h, map_zero]))
  have hroot : (Polynomial.aeval E.yy)
      (Polynomial.X ^ 2
        - Polynomial.C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
        : (RatFunc K)[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα₀F, sub_self]
  have hint : IsIntegral (RatFunc K) E.yy :=
    ⟨_, Polynomial.monic_X_pow_sub_C
      (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) two_ne_zero, by
      simpa [Polynomial.aeval_def] using hroot⟩
  have hadj : IntermediateField.adjoin (RatFunc K) {E.yy} = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨a, b, d, hd, hz⟩ := E.gen z
    refine (IntermediateField.mem_adjoin_simple_iff (RatFunc K) z).2
      ⟨Polynomial.C (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        + Polynomial.C (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
          * Polynomial.X, 1, ?_⟩
    have e1 : algebraMap (RatFunc K) E.F
        (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval E.xx a / Polynomial.aeval E.xx d := by rw [map_div₀, hdown, hdown]
    have e2 : algebraMap (RatFunc K) E.F
        (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval E.xx b / Polynomial.aeval E.xx d := by rw [map_div₀, hdown, hdown]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one, div_one, e1, e2]
    field_simp
    linear_combination hz
  haveI hfd : FiniteDimensional (RatFunc K) E.F := by
    have h1 := IntermediateField.adjoin.finiteDimensional hint
    rw [hadj] at h1
    exact (IntermediateField.topEquiv (F := RatFunc K) (E := E.F)).toLinearEquiv.finiteDimensional
  have hsepyy : IsSeparable (RatFunc K) E.yy := by
    have h2K : ((2 : ℕ) : K) ≠ 0 := by push_cast; exact h2
    have h2' : ((2 : ℕ) : RatFunc K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (RatFunc K)) 2]
      exact fun hh => h2K ((algebraMap K (RatFunc K)).injective (by rw [hh, map_zero]))
    exact (Polynomial.separable_X_pow_sub_C _ h2' hα₀0).of_dvd (minpoly.dvd _ _ hroot)
  haveI : Algebra.IsSeparable (RatFunc K) E.F := by
    have h1 : Algebra.IsSeparable (RatFunc K) (IntermediateField.adjoin (RatFunc K) {E.yy}) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc K) E.F).2 hsepyy
    rw [hadj] at h1
    exact Algebra.IsSeparable.of_algHom (F := RatFunc K) (E := E.F)
      (↥(⊤ : IntermediateField (RatFunc K) E.F))
      (f := (IntermediateField.topEquiv (F := RatFunc K) (E := E.F)).symm.toAlgHom)
  haveI : IsScalarTower K (RatFunc K) E.F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a, hdown]
      simp
  have hxx : algebraMap K[X] E.F Polynomial.X = E.xx := by rw [halg]; simp
  -- the place, up to the sign of the ordinate
  obtain ⟨o, ho, hx, hy⟩ :=
    exists_isPlaceFun_of_affPt_upToSign (F := E.F) hxx E.eqn q.1.1 q.1.2 q.2
  rcases hy with hy | hy
  · exact ⟨o, ho, hx, hy⟩
  -- the hyperelliptic involution swaps the two signs
  have hsqf : Squarefree (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := hsep.squarefree
  have hnu : ¬ IsUnit (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_sextPoly] at h1
    norm_num at h1
  have hirr : Irreducible (Polynomial.X ^ 2
      - Polynomial.C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
      : (RatFunc K)[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_isSquare_sextPoly hsqf hnu)
  haveI : Fact (Irreducible (Polynomial.X ^ 2
      - Polynomial.C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
      : (RatFunc K)[X])) := ⟨hirr⟩
  have hroot2 : (Polynomial.aeval (-E.yy))
      (Polynomial.X ^ 2
        - Polynomial.C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
        : (RatFunc K)[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα₀F]
    ring
  set gpoly : (RatFunc K)[X] := Polynomial.X ^ 2
    - Polynomial.C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) with hgpoly
  have hψ0 : gpoly.eval₂ (Algebra.ofId (RatFunc K) E.F).toRingHom E.yy = 0 := by
    simpa [Polynomial.aeval_def] using hroot
  have hτ0 : gpoly.eval₂ (Algebra.ofId (RatFunc K) E.F).toRingHom (-E.yy) = 0 := by
    simpa [Polynomial.aeval_def] using hroot2
  set ψ₀ : AdjoinRoot gpoly →ₐ[RatFunc K] E.F :=
    AdjoinRoot.liftAlgHom gpoly (Algebra.ofId (RatFunc K) E.F) E.yy hψ0 with hψ₀
  set τ : AdjoinRoot gpoly →ₐ[RatFunc K] E.F :=
    AdjoinRoot.liftAlgHom gpoly (Algebra.ofId (RatFunc K) E.F) (-E.yy) hτ0 with hτ
  have hψroot : ψ₀ (AdjoinRoot.root gpoly) = E.yy := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hτroot : τ (AdjoinRoot.root gpoly) = -E.yy := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψsurj : Function.Surjective ψ₀ := by
    intro z
    have hz : z ∈ IntermediateField.adjoin (RatFunc K) {E.yy} := by rw [hadj]; trivial
    have hle : IntermediateField.adjoin (RatFunc K) {E.yy} ≤ ψ₀.fieldRange :=
      IntermediateField.adjoin_le_iff.2 (by
        rintro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨AdjoinRoot.root gpoly, hψroot⟩)
    exact hle hz
  set ψ : AdjoinRoot gpoly ≃ₐ[RatFunc K] E.F :=
    AlgEquiv.ofBijective ψ₀ ⟨ψ₀.toRingHom.injective, hψsurj⟩ with hψ
  set σ₀ : E.F →ₐ[RatFunc K] E.F := τ.comp ψ.symm.toAlgHom with hσ₀
  have hσyy : σ₀ E.yy = -E.yy := by
    have hs : ψ.symm E.yy = AdjoinRoot.root gpoly := by
      rw [AlgEquiv.symm_apply_eq, hψ]
      simpa using hψroot.symm
    simp [hσ₀, hs, hτroot]
  have hσK : ∀ a : K, σ₀ (algebraMap K E.F a) = algebraMap K E.F a := fun a => by
    rw [IsScalarTower.algebraMap_apply K (RatFunc K) E.F a, AlgHom.commutes]
  have hxxc : E.xx
      = algebraMap (RatFunc K) E.F (algebraMap K[X] (RatFunc K) Polynomial.X) := by
    rw [hdown]; simp
  have hσxx : σ₀ E.xx = E.xx := by
    conv_lhs => rw [hxxc]
    rw [AlgHom.commutes, ← hxxc]
  have hσsurj : Function.Surjective σ₀ := (AlgHom.bijective σ₀).2
  -- transport the place along the involution
  refine ⟨o ∘ σ₀, isPlaceFun_comp ho (σ₀ : E.F →+* E.F) hσsurj hσK, ?_, ?_⟩
  · simpa [Function.comp_apply, map_sub, hσxx, hσK] using hx
  · have hne : E.yy + algebraMap K E.F q.1.2 ≠ 0 := by
      intro hc
      rw [hc, ho.map_zero] at hy
      exact lt_irrefl 0 hy
    have hm1 : (-1 : E.F) = algebraMap K E.F (-1) := by simp
    have : σ₀ (E.yy - algebraMap K E.F q.1.2)
        = algebraMap K E.F (-1) * (E.yy + algebraMap K E.F q.1.2) := by
      rw [map_sub, hσyy, hσK, ← hm1]; ring
    simp only [Function.comp_apply, this]
    rw [ho.map_mul _ _ (by rw [← hm1]; norm_num) hne, ho.map_algebraMap _ (by norm_num)]
    omega

end Affine

end PlaceFromDedekind

end PlacesFromDedekind

/-! ### The CLASSIFICATION of places, and the finiteness of the divisor (PROVEN, 2026-07-30)

`isPlaceFun_ordAt` above produces a place from a height-one prime of the ring of integers.  This
block proves the CONVERSE, which is what `finite_isPlaceFun` needs and what
`PlaceSystem.ord_complete` deliberately does not give: **every** normalised `K`-trivial discrete
valuation of `F` is an `ordAt`, in one of the two towers `K[x] ⊆ F` and `K[1/x] ⊆ F`.

Three steps, none of which needs the sextic or separability — only `2 ≠ 0`:

1. `isPlaceFun_eq_of_le` — a normalised place is determined by its valuation RING, and in fact
   by any place whose ring is contained in it.  Pure valuation theory: a uniformiser of the
   smaller ring has minimal positive order for the larger, and normalisation makes that `1`.
2. `isPlaceFun_nonneg_of_isIntegral` — the valuation ring is integrally closed, so it contains
   `A = integralClosure K[X] F`.  Proven by the standard ultrametric argument over a `Finset`
   sum (`isPlaceFun_sum_ge`) rather than through `IsIntegrallyClosed`, which would need an
   algebra instance on the valuation ring; `valSubring` is nevertheless built, since packaging
   the ring as a `ValuationSubring` is what makes `mem_or_inv_mem` available.
3. `exists_ordAt_eq` — combine: `placeIdeal` is `m_o ∩ A`, a height-one prime, and mathlib's
   `exists_primeCompl_mul_eq_of_integer` (`O_{ordAt v} = A_v`) gives the ring inclusion that
   step 1 turns into equality of places.

Then `finite_ordAt_ne_zero` is the finiteness of the divisor over `A` — `g = n/d` with
`n, d ∈ A`, and a prime where `g` is not a unit divides `(n)` or `(d)`, finitely many by
`Ideal.finite_factors` — and `finite_isPlaceFun_aux` packages the tower construction so that it
can be run twice: at `t = x`, and at `t = 1/x` where `Polynomial.reflect` converts `gen` and the
curve equation (`aeval_inv_reflect`).  A place with `o x < 0` has `o (1/x) > 0`, so the two
towers between them see every place.

**`hsep` IS NOT NEEDED for this leaf** and is underscored on it: the separability of `F/K(t)`
that the Dedekind machinery wants is separability of `Y² − c`, which for a quadratic extension
is exactly `2 ≠ 0`.  Separability of the SEXTIC is a statement about the curve, not about the
extension, and finiteness of a divisor does not see it.
-/

section PlaceClassify

namespace PlaceClassify

open IsDedekindDomain
open PlaceFromDedekind
open scoped WithZero

section Classify

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- **The valuation ring of a place**, as a `ValuationSubring` of `F`.  Packaging it this way
is what gives integral closedness for free (mathlib's
`instance (V : ValuationSubring K) : IsIntegrallyClosed V`), which is the one nontrivial
ingredient in the classification below. -/
def valSubring {o : F → ℤ} (h : IsPlaceFun K F o) : ValuationSubring F where
  carrier := {z | 0 ≤ o z}
  mul_mem' := by
    intro a b ha hb
    have ha' : 0 ≤ o a := ha
    have hb' : 0 ≤ o b := hb
    show 0 ≤ o (a * b)
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [zero_mul, h.map_zero]
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [mul_zero, h.map_zero]
    · rw [h.map_mul a b ha0 hb0]; omega
  one_mem' := by
    show 0 ≤ o 1
    rw [show (1 : F) = algebraMap K F 1 by simp, h.map_algebraMap 1 one_ne_zero]
  add_mem' := by
    intro a b ha hb
    have ha' : 0 ≤ o a := ha
    have hb' : 0 ≤ o b := hb
    show 0 ≤ o (a + b)
    rcases eq_or_ne a 0 with rfl | ha0
    · rwa [zero_add]
    rcases eq_or_ne b 0 with rfl | hb0
    · rwa [add_zero]
    rcases eq_or_ne (a + b) 0 with hab | hab
    · rw [hab, h.map_zero]
    · have := h.ultra a b ha0 hb0 hab; omega
  zero_mem' := by show 0 ≤ o 0; rw [h.map_zero]
  neg_mem' := by
    intro a ha
    have ha' : 0 ≤ o a := ha
    show 0 ≤ o (-a)
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [neg_zero, h.map_zero]
    · have hm : (-a) = algebraMap K F (-1) * a := by simp
      have hne : algebraMap K F (-1 : K) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K F).injective).mpr (by norm_num)
      rw [hm, h.map_mul _ _ hne ha0, h.map_algebraMap (-1) (by norm_num)]
      omega
  mem_or_inv_mem' := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · left; show 0 ≤ o 0; rw [h.map_zero]
    rcases le_or_gt 0 (o z) with hle | hlt
    · exact Or.inl hle
    · refine Or.inr ?_
      show 0 ≤ o z⁻¹
      have h1 := h.map_mul z z⁻¹ hz (inv_ne_zero hz)
      rw [mul_inv_cancel₀ hz,
        show (1 : F) = algebraMap K F 1 by simp, h.map_algebraMap 1 one_ne_zero] at h1
      omega

@[simp] lemma mem_valSubring {o : F → ℤ} (h : IsPlaceFun K F o) (z : F) :
    z ∈ valSubring h ↔ 0 ≤ o z := Iff.rfl

/-- `o (-z) = o z` (PROVEN). -/
lemma isPlaceFun_neg {o : F → ℤ} (h : IsPlaceFun K F o) (z : F) : o (-z) = o z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [neg_zero]
  · have hne : algebraMap K F (-1 : K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K F).injective).mpr (by norm_num)
    rw [show (-z) = algebraMap K F (-1) * z by simp, h.map_mul _ _ hne hz,
      h.map_algebraMap (-1) (by norm_num), zero_add]

/-- `o 1 = 0` (PROVEN). -/
lemma isPlaceFun_one {o : F → ℤ} (h : IsPlaceFun K F o) : o 1 = 0 := by
  rw [show (1 : F) = algebraMap K F 1 by simp, h.map_algebraMap 1 one_ne_zero]

/-- `o (z⁻¹) = − o z` (PROVEN). -/
lemma isPlaceFun_inv {o : F → ℤ} (h : IsPlaceFun K F o) {z : F} (hz : z ≠ 0) :
    o z⁻¹ = - o z := by
  have h1 := h.map_mul z z⁻¹ hz (inv_ne_zero hz)
  rw [mul_inv_cancel₀ hz, isPlaceFun_one h] at h1
  omega

/-- `o (zⁿ) = n · o z` (PROVEN). -/
lemma isPlaceFun_pow {o : F → ℤ} (h : IsPlaceFun K F o) {z : F} (hz : z ≠ 0) (n : ℕ) :
    o (z ^ n) = n * o z := by
  induction n with
  | zero => simpa using isPlaceFun_one h
  | succ m ih =>
    rw [pow_succ, h.map_mul _ _ (pow_ne_zero _ hz) hz, ih]
    push_cast; ring

/-- `o (z ^ (n : ℤ)) = n · o z` (PROVEN). -/
lemma isPlaceFun_zpow {o : F → ℤ} (h : IsPlaceFun K F o) {z : F} (hz : z ≠ 0) (n : ℤ) :
    o (z ^ n) = n * o z := by
  rcases n with (m | m)
  · simpa using isPlaceFun_pow h hz m
  · rw [zpow_negSucc, isPlaceFun_inv h (pow_ne_zero _ hz), isPlaceFun_pow h hz (m + 1),
      Int.negSucc_eq]
    push_cast; ring

/-- **Two normalised places with the same valuation ring are EQUAL** (PROVEN).

Only the inclusion of valuation rings is needed, and the argument is pure valuation theory:
a uniformiser of the smaller ring has minimal positive order for the larger one, and
normalisation makes that minimum `1`. -/
theorem isPlaceFun_eq_of_le {o w : F → ℤ} (ho : IsPlaceFun K F o) (hw : IsPlaceFun K F w)
    (hle : ∀ z : F, 0 ≤ w z → 0 ≤ o z) {π : F} (hπ0 : π ≠ 0) (hπ : w π = 1) : o = w := by
  have hoπ : o π = 1 := by
    -- `o π ≥ 0` because `w π = 1 ≥ 0`; and `o` is normalised, so `o π ≤ 1`
    have hge : 0 ≤ o π := hle π (by omega)
    obtain ⟨t, ht⟩ := ho.normalised
    have ht0 : t ≠ 0 := by intro h0; rw [h0, ho.map_zero] at ht; omega
    -- every element of `w`-order `0` is an `o`-unit
    have hunit : ∀ z : F, z ≠ 0 → w z = 0 → o z = 0 := by
      intro z hz hwz
      have h1 : 0 ≤ o z := hle z (by omega)
      have h2 : 0 ≤ o z⁻¹ := hle z⁻¹ (by rw [isPlaceFun_inv hw hz]; omega)
      rw [isPlaceFun_inv ho hz] at h2
      omega
    -- write `t = u · π ^ (w t)`
    have hkey : ∀ z : F, z ≠ 0 → o z = (w z) * o π := by
      intro z hz
      have hz' : z * (π ^ (w z))⁻¹ ≠ 0 := by
        exact mul_ne_zero hz (inv_ne_zero (zpow_ne_zero _ hπ0))
      have hw' : w (z * (π ^ (w z))⁻¹) = 0 := by
        rw [hw.map_mul _ _ hz (inv_ne_zero (zpow_ne_zero _ hπ0)),
          isPlaceFun_inv hw (zpow_ne_zero _ hπ0), isPlaceFun_zpow hw hπ0, hπ]
        ring
      have ho' := hunit _ hz' hw'
      rw [ho.map_mul _ _ hz (inv_ne_zero (zpow_ne_zero _ hπ0)),
        isPlaceFun_inv ho (zpow_ne_zero _ hπ0), isPlaceFun_zpow ho hπ0] at ho'
      omega
    have h1 := hkey t ht0
    rw [ht] at h1
    -- `1 = (w t) * o π` with `o π ≥ 0` forces `o π = 1`
    have hdvd : o π ∣ 1 := Dvd.intro_left (w t) h1.symm
    have hu := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
    omega
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [ho.map_zero, hw.map_zero]
  · have hunit : ∀ y : F, y ≠ 0 → w y = 0 → o y = 0 := by
      intro y hy hwy
      have h1 : 0 ≤ o y := hle y (by omega)
      have h2 : 0 ≤ o y⁻¹ := hle y⁻¹ (by rw [isPlaceFun_inv hw hy]; omega)
      rw [isPlaceFun_inv ho hy] at h2
      omega
    have hz' : z * (π ^ (w z))⁻¹ ≠ 0 := mul_ne_zero hz (inv_ne_zero (zpow_ne_zero _ hπ0))
    have hw' : w (z * (π ^ (w z))⁻¹) = 0 := by
      rw [hw.map_mul _ _ hz (inv_ne_zero (zpow_ne_zero _ hπ0)),
        isPlaceFun_inv hw (zpow_ne_zero _ hπ0), isPlaceFun_zpow hw hπ0, hπ]
      ring
    have ho' := hunit _ hz' hw'
    rw [ho.map_mul _ _ hz (inv_ne_zero (zpow_ne_zero _ hπ0)),
      isPlaceFun_inv ho (zpow_ne_zero _ hπ0), isPlaceFun_zpow ho hπ0, hoπ] at ho'
    omega


/-- The ultrametric inequality over a `Finset` sum (PROVEN). -/
lemma isPlaceFun_sum_ge {o : F → ℤ} (ho : IsPlaceFun K F o) {ι : Type*} (s : Finset ι)
    (f : ι → F) (c : ℤ) (hf : ∀ i ∈ s, f i = 0 ∨ c ≤ o (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ c ≤ o (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rcases eq_or_ne (f a) 0 with ha0 | ha0
    · rw [ha0, zero_add]; exact h2
    have h1 : c ≤ o (f a) := (hf a (Finset.mem_insert_self a s)).resolve_left ha0
    rcases eq_or_ne (∑ i ∈ s, f i) 0 with hs0 | hs0
    · rw [hs0, add_zero]; exact Or.inr h1
    have h2' : c ≤ o (∑ i ∈ s, f i) := h2.resolve_left hs0
    rcases eq_or_ne (f a + ∑ i ∈ s, f i) 0 with hsum | hsum
    · exact Or.inl hsum
    · have := ho.ultra _ _ ha0 hs0 hsum
      exact Or.inr (by omega)

variable [Algebra K[X] F] [IsScalarTower K K[X] F]

/-- Every polynomial in the abscissa has nonnegative order, when the abscissa does (PROVEN). -/
lemma isPlaceFun_algebraMap_poly_nonneg {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) (p : K[X]) :
    0 ≤ o (algebraMap K[X] F p) := by
  have hconst : ∀ c : K, 0 ≤ o (algebraMap K F c) := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, ho.map_zero]
    · rw [ho.map_algebraMap c hc]
  have hmem : (algebraMap K[X] F p) ∈ valSubring ho := by
    rw [algebraMap_poly_eq_aeval hxx]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa [map_add] using Subring.add_mem _ hp hq
    | monomial n c =>
      rw [Polynomial.aeval_monomial]
      refine Subring.mul_mem _ ?_ ?_
      · exact hconst c
      · exact Subring.pow_mem _ (show t ∈ valSubring ho from ht) n
  exact hmem

/-- **An element integral over `K[x]` has nonnegative order** (PROVEN) — the valuation ring is
integrally closed, proven here by the standard ultrametric argument rather than through
`IsIntegrallyClosed`, so that no extra algebra instance on the valuation ring is needed. -/
lemma isPlaceFun_nonneg_of_isIntegral {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) {z : F}
    (hz : IsIntegral K[X] z) : 0 ≤ o z := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmonic, hroot⟩ := hz
  have hz0 : z ≠ 0 := by intro h0; rw [h0, ho.map_zero] at hlt; omega
  set n := p.natDegree with hn
  -- expand the integral equation, splitting off the leading term
  have hexp : Polynomial.eval₂ (algebraMap K[X] F) z p
      = (∑ i ∈ Finset.range n, algebraMap K[X] F (p.coeff i) * z ^ i) + z ^ n := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, map_one,
      one_mul]
  rw [hexp] at hroot
  have hsum : (∑ i ∈ Finset.range n, algebraMap K[X] F (p.coeff i) * z ^ i) = - z ^ n := by
    linear_combination hroot
  have hbound : ∀ i ∈ Finset.range n,
      (algebraMap K[X] F (p.coeff i) * z ^ i) = 0 ∨
        ((n : ℤ) - 1) * o z ≤ o (algebraMap K[X] F (p.coeff i) * z ^ i) := by
    intro i hi
    rcases eq_or_ne (algebraMap K[X] F (p.coeff i)) 0 with h0 | h0
    · exact Or.inl (by rw [h0, zero_mul])
    refine Or.inr ?_
    rw [ho.map_mul _ _ h0 (pow_ne_zero _ hz0), isPlaceFun_pow ho hz0]
    have hc := isPlaceFun_algebraMap_poly_nonneg ho hxx ht (p.coeff i)
    have hi' : (i : ℤ) ≤ (n : ℤ) - 1 := by
      have := Finset.mem_range.mp hi
      omega
    nlinarith [hlt, hc, hi']
  have hzn : o (- z ^ n) = (n : ℤ) * o z := by
    rw [isPlaceFun_neg ho, isPlaceFun_pow ho hz0]
  rcases isPlaceFun_sum_ge ho (Finset.range n) _ (((n : ℤ) - 1) * o z) hbound with hc | hc
  · rw [hsum] at hc
    have : z ^ n = 0 := by linear_combination -hc
    exact (pow_ne_zero n hz0) this
  · rw [hsum, hzn] at hc
    nlinarith [hc, hlt]



section Tower2

variable [Algebra (RatFunc K) F] [IsScalarTower K[X] (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

/-- **The prime of the ring of integers cut out by a place** (PROVEN), for a place at which the
abscissa is regular. -/
def placeIdeal {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) :
    Ideal ↥(integralClosure K[X] F) where
  carrier := {a | (a : F) = 0 ∨ 0 < o (a : F)}
  add_mem' := by
    intro a b ha hb
    have ha' : (a : F) = 0 ∨ 0 < o (a : F) := ha
    have hb' : (b : F) = 0 ∨ 0 < o (b : F) := hb
    show ((a + b : ↥(integralClosure K[X] F)) : F) = 0 ∨ 0 < o ((a + b : ↥(integralClosure K[X] F)) : F)
    have hab : ((a + b : ↥(integralClosure K[X] F)) : F) = (a : F) + (b : F) := by push_cast; ring
    rw [hab]
    rcases ha' with ha' | ha'
    · rw [ha', zero_add]; exact hb'
    rcases hb' with hb' | hb'
    · rw [hb', add_zero]; exact Or.inr ha'
    have ha0 : (a : F) ≠ 0 := by intro h0; rw [h0, ho.map_zero] at ha'; omega
    have hb0 : (b : F) ≠ 0 := by intro h0; rw [h0, ho.map_zero] at hb'; omega
    rcases eq_or_ne ((a : F) + (b : F)) 0 with h0 | h0
    · exact Or.inl h0
    · have := ho.ultra _ _ ha0 hb0 h0
      exact Or.inr (by omega)
  zero_mem' := Or.inl (by push_cast; ring)
  smul_mem' := by
    intro c a ha
    have ha' : (a : F) = 0 ∨ 0 < o (a : F) := ha
    show ((c • a : ↥(integralClosure K[X] F)) : F) = 0 ∨ 0 < o ((c • a : ↥(integralClosure K[X] F)) : F)
    have hca : ((c • a : ↥(integralClosure K[X] F)) : F) = (c : F) * (a : F) := by
      simp [smul_eq_mul]
    rw [hca]
    rcases ha' with ha' | ha'
    · exact Or.inl (by rw [ha', mul_zero])
    have ha0 : (a : F) ≠ 0 := by intro h0; rw [h0, ho.map_zero] at ha'; omega
    rcases eq_or_ne (c : F) 0 with hc0 | hc0
    · exact Or.inl (by rw [hc0, zero_mul])
    · have hc : 0 ≤ o (c : F) := isPlaceFun_nonneg_of_isIntegral ho hxx ht c.2
      exact Or.inr (by rw [ho.map_mul _ _ hc0 ha0]; omega)

lemma mem_placeIdeal {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t)
    {a : ↥(integralClosure K[X] F)} :
    a ∈ placeIdeal ho hxx ht ↔ ((a : F) = 0 ∨ 0 < o (a : F)) := Iff.rfl

lemma placeIdeal_isPrime {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) :
    (placeIdeal ho hxx ht).IsPrime := by
  constructor
  · intro htop
    have h1 : (1 : ↥(integralClosure K[X] F)) ∈ placeIdeal ho hxx ht := by
      rw [htop]; exact Submodule.mem_top
    rw [mem_placeIdeal] at h1
    have hone : ((1 : ↥(integralClosure K[X] F)) : F) = 1 := by push_cast; ring
    rw [hone, isPlaceFun_one ho] at h1
    rcases h1 with h1 | h1
    · exact one_ne_zero h1
    · omega
  · intro a b hab
    rw [mem_placeIdeal] at hab
    have hprod : ((a * b : ↥(integralClosure K[X] F)) : F) = (a : F) * (b : F) := by
      push_cast; ring
    rw [hprod] at hab
    rcases hab with hab | hab
    · rcases mul_eq_zero.mp hab with h | h
      · exact Or.inl (by rw [mem_placeIdeal]; exact Or.inl h)
      · exact Or.inr (by rw [mem_placeIdeal]; exact Or.inl h)
    · have ha0 : (a : F) ≠ 0 := by
        intro h0; rw [h0, zero_mul, ho.map_zero] at hab; omega
      have hb0 : (b : F) ≠ 0 := by
        intro h0; rw [h0, mul_zero, ho.map_zero] at hab; omega
      rw [ho.map_mul _ _ ha0 hb0] at hab
      have hA : 0 ≤ o (a : F) := isPlaceFun_nonneg_of_isIntegral ho hxx ht a.2
      have hB : 0 ≤ o (b : F) := isPlaceFun_nonneg_of_isIntegral ho hxx ht b.2
      rcases lt_or_ge 0 (o (a : F)) with h | h
      · exact Or.inl (by rw [mem_placeIdeal]; exact Or.inr h)
      · exact Or.inr (by rw [mem_placeIdeal]; exact Or.inr (by omega))

lemma placeIdeal_ne_bot {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) :
    placeIdeal ho hxx ht ≠ ⊥ := by
  obtain ⟨τ, hτ⟩ := ho.normalised
  obtain ⟨n, d, hd0, hnd⟩ :=
    IsFractionRing.div_surjective (A := ↥(integralClosure K[X] F)) τ
  have hcoe : ∀ x : ↥(integralClosure K[X] F),
      algebraMap (↥(integralClosure K[X] F)) F x = (x : F) := fun _ => rfl
  rw [hcoe, hcoe] at hnd
  have hdF : ((d : ↥(integralClosure K[X] F)) : F) ≠ 0 := by
    simpa using hd0
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0, ho.map_zero] at hτ; omega
  have hnF : ((n : ↥(integralClosure K[X] F)) : F) ≠ 0 := by
    intro h0
    rw [← hnd] at hτ0
    exact hτ0 (by
      have : ((n : ↥(integralClosure K[X] F)) : F) / ((d : ↥(integralClosure K[X] F)) : F) = 0 := by
        rw [h0, zero_div]
      simpa using this)
  have hdnn : 0 ≤ o ((d : ↥(integralClosure K[X] F)) : F) :=
    isPlaceFun_nonneg_of_isIntegral ho hxx ht d.2
  have hon : 0 < o ((n : ↥(integralClosure K[X] F)) : F) := by
    have hsplit : o ((n : ↥(integralClosure K[X] F)) : F)
        = o τ + o ((d : ↥(integralClosure K[X] F)) : F) := by
      have hmul : ((n : ↥(integralClosure K[X] F)) : F)
          = τ * ((d : ↥(integralClosure K[X] F)) : F) := by
        rw [← hnd]; field_simp
      rw [hmul, ho.map_mul _ _ hτ0 hdF]
    rw [hsplit, hτ]
    omega
  intro hbot
  have hmem : (n : ↥(integralClosure K[X] F)) ∈ placeIdeal ho hxx ht := by
    rw [mem_placeIdeal]; exact Or.inr hon
  rw [hbot, Ideal.mem_bot] at hmem
  exact hnF (by rw [hmem]; push_cast; ring)


/-- `0 < ordAt v a` for an element of the ring of integers means `a ∈ v` (PROVEN), the converse
of `ordAt_pos_of_mem`. -/
lemma mem_of_ordAt_pos (v : HeightOneSpectrum ↥(integralClosure K[X] F))
    {a : ↥(integralClosure K[X] F)} (ha : (a : F) ≠ 0)
    (h : 0 < ordAt (F := F) v (a : F)) : a ∈ v.asIdeal := by
  have hne : v.valuation F (a : F) ≠ 0 := valuation_ne_zero v ha
  have hlt : v.valuation F (a : F) < 1 := by
    refine (WithZero.log_lt_log hne (one_ne_zero (α := ℤᵐ⁰))).1 ?_
    simp only [WithZero.log_one]
    simp only [ordAt] at h
    omega
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v a).1 hlt

/-- **THE CLASSIFICATION** (PROVEN): a normalised place at which the abscissa is regular IS the
adic valuation of a height-one prime of the ring of integers `A = integralClosure K[X] F`.

This is the direction `PlaceSystem.ord_complete` does NOT give: `isPlaceFun_ordAt` produces a
place from a prime, and this produces the prime from the place.  The two ingredients are
`isPlaceFun_nonneg_of_isIntegral` (`A ⊆ O_o`, integral closedness of a valuation ring) and
mathlib's `exists_primeCompl_mul_eq_of_integer` (`O_ordAt v = A_v`), and they combine through
`isPlaceFun_eq_of_le`, which says a normalised place is determined by its valuation ring. -/
theorem exists_ordAt_eq {o : F → ℤ} (ho : IsPlaceFun K F o) {t : F}
    (hxx : algebraMap K[X] F Polynomial.X = t) (ht : 0 ≤ o t) :
    ∃ v : HeightOneSpectrum ↥(integralClosure K[X] F), o = ordAt (F := F) v := by
  refine ⟨⟨placeIdeal ho hxx ht, placeIdeal_isPrime ho hxx ht, placeIdeal_ne_bot ho hxx ht⟩, ?_⟩
  obtain ⟨π, hπ⟩ := ordAt_normalised (F := F)
    (⟨placeIdeal ho hxx ht, placeIdeal_isPrime ho hxx ht, placeIdeal_ne_bot ho hxx ht⟩ :
      HeightOneSpectrum ↥(integralClosure K[X] F))
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, ordAt_zero] at hπ
    omega
  refine isPlaceFun_eq_of_le ho (isPlaceFun_ordAt _) ?_ hπ0 hπ
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [ho.map_zero]
  set v : HeightOneSpectrum ↥(integralClosure K[X] F) :=
    ⟨placeIdeal ho hxx ht, placeIdeal_isPrime ho hxx ht, placeIdeal_ne_bot ho hxx ht⟩ with hv
  have hval : v.valuation F z ≤ 1 := by
    have hne : v.valuation F z ≠ 0 := valuation_ne_zero v hz0
    refine (WithZero.log_le_log hne (one_ne_zero (α := ℤᵐ⁰))).1 ?_
    simp only [WithZero.log_one]
    simp only [ordAt] at hz
    omega
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer z hval
  have hcoe : ∀ x : ↥(integralClosure K[X] F),
      algebraMap (↥(integralClosure K[X] F)) F x = (x : F) := fun _ => rfl
  rw [hcoe, hcoe] at hnd
  have hdmem : (d : ↥(integralClosure K[X] F)) ∉ v.asIdeal := d.2
  have hd' : ¬ (((d : ↥(integralClosure K[X] F)) : F) = 0 ∨
      0 < o ((d : ↥(integralClosure K[X] F)) : F)) := by
    intro hcon
    exact hdmem ((mem_placeIdeal ho hxx ht).2 hcon)
  have hdF : ((d : ↥(integralClosure K[X] F)) : F) ≠ 0 := fun h0 => hd' (Or.inl h0)
  have hdle : o ((d : ↥(integralClosure K[X] F)) : F) ≤ 0 := by
    by_contra hcon
    exact hd' (Or.inr (by omega))
  have hdge : 0 ≤ o ((d : ↥(integralClosure K[X] F)) : F) :=
    isPlaceFun_nonneg_of_isIntegral ho hxx ht d.1.2
  have hnge : 0 ≤ o ((n : ↥(integralClosure K[X] F)) : F) :=
    isPlaceFun_nonneg_of_isIntegral ho hxx ht n.2
  have hsplit : o z + o ((d : ↥(integralClosure K[X] F)) : F)
      = o ((n : ↥(integralClosure K[X] F)) : F) := by
    rw [← ho.map_mul _ _ hz0 hdF, hnd]
  omega

/-- **The divisor of a nonzero function has finite support** (PROVEN), over the ring of
integers: a nonzero `g` is `n/d` with `n, d ∈ A`, and a prime at which `g` is not a unit
divides `(n)` or `(d)` — finitely many, by `Ideal.finite_factors`. -/
theorem finite_ordAt_ne_zero {g : F} (hg : g ≠ 0) :
    {v : HeightOneSpectrum ↥(integralClosure K[X] F) | ordAt (F := F) v g ≠ 0}.Finite := by
  obtain ⟨n, d, hd0, hnd⟩ := IsFractionRing.div_surjective (A := ↥(integralClosure K[X] F)) g
  have hcoe : ∀ x : ↥(integralClosure K[X] F),
      algebraMap (↥(integralClosure K[X] F)) F x = (x : F) := fun _ => rfl
  rw [hcoe, hcoe] at hnd
  have hdF : ((d : ↥(integralClosure K[X] F)) : F) ≠ 0 := by simpa using hd0
  have hnF : ((n : ↥(integralClosure K[X] F)) : F) ≠ 0 := by
    intro h0
    rw [← hnd, h0, zero_div] at hg
    exact hg rfl
  have hn0 : (n : ↥(integralClosure K[X] F)) ≠ 0 := by
    intro h0; exact hnF (by rw [h0]; push_cast; ring)
  have hd0' : (d : ↥(integralClosure K[X] F)) ≠ 0 := by
    intro h0; exact hdF (by rw [h0]; push_cast; ring)
  refine Set.Finite.subset (Set.Finite.union
    (Ideal.finite_factors (R := ↥(integralClosure K[X] F))
      (I := Ideal.span {(n : ↥(integralClosure K[X] F))}) (by
        simpa [Ideal.span_singleton_eq_bot] using hn0))
    (Ideal.finite_factors (R := ↥(integralClosure K[X] F))
      (I := Ideal.span {(d : ↥(integralClosure K[X] F))}) (by
        simpa [Ideal.span_singleton_eq_bot] using hd0))) ?_
  intro v hv
  have hvg : ordAt (F := F) v g ≠ 0 := hv
  have hgeq : g = ((n : ↥(integralClosure K[X] F)) : F) / ((d : ↥(integralClosure K[X] F)) : F) :=
    hnd.symm
  have hsplit : ordAt (F := F) v ((n : ↥(integralClosure K[X] F)) : F)
      = ordAt (F := F) v g + ordAt (F := F) v ((d : ↥(integralClosure K[X] F)) : F) := by
    have hmul : ((n : ↥(integralClosure K[X] F)) : F)
        = g * ((d : ↥(integralClosure K[X] F)) : F) := by
      rw [hgeq]; field_simp
    rw [hmul, ordAt_mul v _ _ hg hdF]
  have hnnn : 0 ≤ ordAt (F := F) v ((n : ↥(integralClosure K[X] F)) : F) :=
    ordAt_nonneg_of_isIntegral v n.2
  have hdnn : 0 ≤ ordAt (F := F) v ((d : ↥(integralClosure K[X] F)) : F) :=
    ordAt_nonneg_of_isIntegral v d.2
  rcases lt_or_ge 0 (ordAt (F := F) v ((n : ↥(integralClosure K[X] F)) : F)) with hn | hn
  · left
    show v.asIdeal ∣ Ideal.span {(n : ↥(integralClosure K[X] F))}
    rw [Ideal.dvd_span_singleton]
    exact mem_of_ordAt_pos v hnF hn
  · right
    show v.asIdeal ∣ Ideal.span {(d : ↥(integralClosure K[X] F))}
    rw [Ideal.dvd_span_singleton]
    refine mem_of_ordAt_pos v hdF ?_
    omega


/-- **Finiteness of the bad set among the places regular at the abscissa** (PROVEN): such a
place IS an `ordAt`, and the primes at which `g` is not a unit are finitely many. -/
theorem finite_isPlaceFun_of_nonneg {t : F} (hxx : algebraMap K[X] F Polynomial.X = t)
    {g : F} (hg : g ≠ 0) :
    {p : {o : F → ℤ // IsPlaceFun K F o} | 0 ≤ p.1 t ∧ p.1 g ≠ 0}.Finite := by
  refine Set.Finite.subset ((finite_ordAt_ne_zero (K := K) (F := F) hg).image
    (fun v : HeightOneSpectrum ↥(integralClosure K[X] F) =>
      (⟨ordAt (F := F) v, isPlaceFun_ordAt v⟩ : {o : F → ℤ // IsPlaceFun K F o}))) ?_
  intro p hp
  obtain ⟨v, hv⟩ := exists_ordAt_eq p.2 hxx hp.1
  refine ⟨v, ?_, ?_⟩
  · show ordAt (F := F) v g ≠ 0
    rw [← hv]
    exact hp.2
  · exact Subtype.ext hv.symm

end Tower2



end Classify

/-! ### The frontier of obligation 1b: finiteness of the divisor -/

section Finite

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-- The ordinate is nonzero (PROVEN): otherwise the abscissa would be a root of the sextic. -/
lemma yy_ne_zero (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) : E.yy ≠ 0 := by
  intro h0
  have hsext0 : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K ≠ 0 := fun hz => by
    have hd := natDegree_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
    rw [hz] at hd; simp at hd
  refine E.transcendental_xx ⟨sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K, hsext0, ?_⟩
  have := E.eqn
  rw [h0] at this
  rw [aeval_sextPoly, ← this]
  ring

/-- **Finiteness, in any generator of the abscissa's subfield** (PROVEN).

`t` plays the role of the abscissa: it must be transcendental, `F` must be generated over `K(t)`
by the ordinate, and the ordinate's square must lie in `K(t)`.  Both `t = x` and `t = 1/x`
qualify, and between them they cover every place — which is what closes `finite_isPlaceFun`. -/
theorem finite_isPlaceFun_aux (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (h2 : (2 : K) ≠ 0) {t : E.F} (htr : Transcendental K t)
    (hgen : ∀ z : E.F, ∃ a b d : K[X], aeval t d ≠ 0 ∧
      z * aeval t d = aeval t a + aeval t b * E.yy)
    {P Q : K[X]} (hQ : aeval t Q ≠ 0) (hPQ : E.yy ^ 2 * aeval t Q = aeval t P)
    {g : E.F} (hg : g ≠ 0) :
    {p : {o : E.F → ℤ // IsPlaceFun K E.F o} | 0 ≤ p.1 t ∧ p.1 g ≠ 0}.Finite := by
  classical
  letI : Algebra K[X] E.F := (Polynomial.aeval t : K[X] →ₐ[K] E.F).toRingHom.toAlgebra
  have halg : ∀ p : K[X], algebraMap K[X] E.F p = Polynomial.aeval t p := fun _ => rfl
  haveI : IsScalarTower K K[X] E.F := IsScalarTower.of_algebraMap_eq fun a => by simp [halg]
  have hinj : Function.Injective (algebraMap K[X] E.F) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    exact htr ⟨p, hp0, by rw [← halg]; exact hp⟩
  letI : Algebra (RatFunc K) E.F := (IsFractionRing.lift (A := K[X]) hinj).toAlgebra
  haveI : IsScalarTower K[X] (RatFunc K) E.F :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hinj p).symm
  have hdown : ∀ p : K[X], algebraMap (RatFunc K) E.F (algebraMap K[X] (RatFunc K) p)
      = Polynomial.aeval t p := fun p => by rw [← IsScalarTower.algebraMap_apply, halg]
  -- the ordinate's square is the nonzero constant `c = P/Q` of `K(t)`
  set c : RatFunc K :=
    algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q with hc
  have hQ0 : algebraMap K[X] (RatFunc K) Q ≠ 0 := fun h0 => hQ (by rw [← hdown, h0, map_zero])
  have hcF : algebraMap (RatFunc K) E.F c = E.yy ^ 2 := by
    rw [hc, map_div₀, hdown, hdown, ← hPQ]
    field_simp
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcF
    exact (pow_ne_zero 2 (yy_ne_zero E)) hcF.symm
  have hroot : (Polynomial.aeval E.yy)
      (Polynomial.X ^ 2 - Polynomial.C c : (RatFunc K)[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hcF, sub_self]
  have hint : IsIntegral (RatFunc K) E.yy :=
    ⟨_, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simpa [Polynomial.aeval_def] using hroot⟩
  have hadj : IntermediateField.adjoin (RatFunc K) {E.yy} = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨a, b, d, hd, hz⟩ := hgen z
    refine (IntermediateField.mem_adjoin_simple_iff (RatFunc K) z).2
      ⟨Polynomial.C (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        + Polynomial.C (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
          * Polynomial.X, 1, ?_⟩
    have e1 : algebraMap (RatFunc K) E.F
        (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval t a / Polynomial.aeval t d := by rw [map_div₀, hdown, hdown]
    have e2 : algebraMap (RatFunc K) E.F
        (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval t b / Polynomial.aeval t d := by rw [map_div₀, hdown, hdown]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one, div_one, e1, e2]
    field_simp
    linear_combination hz
  haveI hfd : FiniteDimensional (RatFunc K) E.F := by
    have h1 := IntermediateField.adjoin.finiteDimensional hint
    rw [hadj] at h1
    exact (IntermediateField.topEquiv (F := RatFunc K) (E := E.F)).toLinearEquiv.finiteDimensional
  have hsepyy : IsSeparable (RatFunc K) E.yy := by
    have h2K : ((2 : ℕ) : K) ≠ 0 := by push_cast; exact h2
    have h2' : ((2 : ℕ) : RatFunc K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (RatFunc K)) 2]
      exact fun hh => h2K ((algebraMap K (RatFunc K)).injective (by rw [hh, map_zero]))
    exact (Polynomial.separable_X_pow_sub_C _ h2' hc0).of_dvd (minpoly.dvd _ _ hroot)
  haveI : Algebra.IsSeparable (RatFunc K) E.F := by
    have h1 : Algebra.IsSeparable (RatFunc K) (IntermediateField.adjoin (RatFunc K) {E.yy}) :=
      (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc K) E.F).2 hsepyy
    rw [hadj] at h1
    exact Algebra.IsSeparable.of_algHom (F := RatFunc K) (E := E.F)
      (↥(⊤ : IntermediateField (RatFunc K) E.F))
      (f := (IntermediateField.topEquiv (F := RatFunc K) (E := E.F)).symm.toAlgHom)
  have hxxX : algebraMap K[X] E.F Polynomial.X = t := by rw [halg]; simp
  exact finite_isPlaceFun_of_nonneg hxxX hg

/-- `aeval` at `x⁻¹` of the reflected polynomial (PROVEN), mathlib's `eval₂_reflect_mul_pow`
in the form the chart at infinity wants. -/
lemma aeval_inv_reflect {F : Type*} [Field F] [Algebra K F] {x : F} (hx : x ≠ 0)
    (p : K[X]) (m : ℕ) (hp : p.natDegree ≤ m) :
    aeval x⁻¹ (Polynomial.reflect m p) = aeval x p * x⁻¹ ^ m := by
  haveI : Invertible x := invertibleOfNonzero hx
  have h := Polynomial.eval₂_reflect_mul_pow (algebraMap K F) x m p hp
  have hinv : (⅟x : F) = x⁻¹ := invOf_eq_inv x
  rw [hinv, ← Polynomial.aeval_def, ← Polynomial.aeval_def] at h
  have hxu : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  calc aeval x⁻¹ (Polynomial.reflect m p)
      = aeval x⁻¹ (Polynomial.reflect m p) * (x * x⁻¹) ^ m := by rw [hxu, one_pow, mul_one]
    _ = (aeval x⁻¹ (Polynomial.reflect m p) * x ^ m) * x⁻¹ ^ m := by ring
    _ = aeval x p * x⁻¹ ^ m := by rw [h]

/-- **The finiteness of the divisor** (PROVEN), in the two towers together: every place is
regular at `x` or at `1/x`, so the classification applies to it in one tower or the other. -/
theorem finite_isPlaceFun_core (E : FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K) (h2 : (2 : K) ≠ 0)
    (g : E.F) (hg : g ≠ 0) :
    {v : {o : E.F → ℤ // IsPlaceFun K E.F o} | v.1 g ≠ 0}.Finite := by
  have hxne : E.xx ≠ 0 := by
    intro h0
    exact E.transcendental_xx ⟨Polynomial.X, Polynomial.X_ne_zero, by simp [h0]⟩
  have hine : E.xx⁻¹ ≠ 0 := inv_ne_zero hxne
  -- the affine tower `t = x`
  have hA : {p : {o : E.F → ℤ // IsPlaceFun K E.F o} | 0 ≤ p.1 E.xx ∧ p.1 g ≠ 0}.Finite := by
    refine finite_isPlaceFun_aux E h2 E.transcendental_xx E.gen
      (P := sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) (Q := 1) (by simp) ?_ hg
    rw [map_one, mul_one, aeval_sextPoly]
    exact E.eqn
  -- the tower at infinity `t = 1/x`
  have htrinv : Transcendental K E.xx⁻¹ := by
    intro halg
    exact E.transcendental_xx (IsAlgebraic.inv_iff.1 halg)
  have hgeninf : ∀ z : E.F, ∃ a b d : K[X], aeval E.xx⁻¹ d ≠ 0 ∧
      z * aeval E.xx⁻¹ d = aeval E.xx⁻¹ a + aeval E.xx⁻¹ b * E.yy := by
    intro z
    obtain ⟨a, b, d, hd, hz⟩ := E.gen z
    set m : ℕ := max d.natDegree (max a.natDegree b.natDegree) with hm
    have hdm : d.natDegree ≤ m := by rw [hm]; exact le_max_left _ _
    have ham : a.natDegree ≤ m := by
      rw [hm]; exact le_trans (le_max_left _ b.natDegree) (le_max_right _ _)
    have hbm : b.natDegree ≤ m := by
      rw [hm]; exact le_trans (le_max_right a.natDegree _) (le_max_right _ _)
    refine ⟨Polynomial.reflect m a, Polynomial.reflect m b, Polynomial.reflect m d, ?_, ?_⟩
    · rw [aeval_inv_reflect hxne d m hdm]
      exact mul_ne_zero hd (pow_ne_zero _ hine)
    · rw [aeval_inv_reflect hxne d m hdm, aeval_inv_reflect hxne a m ham,
        aeval_inv_reflect hxne b m hbm]
      linear_combination (E.xx⁻¹ ^ m) * hz
  have hB : {p : {o : E.F → ℤ // IsPlaceFun K E.F o} |
      0 ≤ p.1 E.xx⁻¹ ∧ p.1 E.xx⁻¹ ≠ 0}.Finite := by
    refine finite_isPlaceFun_aux E h2 htrinv hgeninf
      (P := Polynomial.reflect 6 (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) (Q := Polynomial.X ^ 6) ?_ ?_ hine
    · rw [map_pow, Polynomial.aeval_X]
      exact pow_ne_zero _ hine
    · rw [aeval_inv_reflect hxne _ 6 (by rw [natDegree_sextPoly]), aeval_sextPoly, ← E.eqn,
        map_pow, Polynomial.aeval_X]
  -- every place is covered by one of the two
  refine Set.Finite.subset (Set.Finite.union hA hB) ?_
  intro p hp
  have hpg : p.1 g ≠ 0 := hp
  rcases le_or_gt 0 (p.1 E.xx) with h | h
  · exact Or.inl ⟨h, hpg⟩
  · have hinv : p.1 E.xx⁻¹ = - p.1 E.xx := isPlaceFun_inv p.2 hxne
    exact Or.inr ⟨by omega, by omega⟩


end Finite

end PlaceClassify

end PlaceClassify

/-- **LEAF (obligation 1b, RESIDUE), PROVEN 2026-07-30: a nonzero function has finitely many
zeros and poles.**

The route below is NOT the one that was taken: no norm and no counting of extensions of a place
of `K(x)` appears.  What replaces it is the CLASSIFICATION of places in the section above --
every place is an `ordAt` of a height-one prime of the ring of integers of one of the two
towers `K[x]` and `K[1/x]` -- together with the finiteness of the divisor over a Dedekind
domain.  See that section for the three steps, and note that `hsep` is NOT used.

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
    (_hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0)
    (g : E.F) (hg : g ≠ 0) :
    {v : {o : E.F → ℤ // IsPlaceFun K E.F o} | v.1 g ≠ 0}.Finite :=
  PlaceClassify.finite_isPlaceFun_core E h2 g hg


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
      0 < o (E.xx - algebraMap K E.F q.1.1) ∧ 0 < o (E.yy - algebraMap K E.F q.1.2) :=
  PlaceFromDedekind.exists_isPlaceFun_of_affPt' E hsep h2 q

/-! ### The place of a branch at infinity, via Laurent series (PROVEN, 2026-07-30)

The affine half above goes through the Dedekind ring of integers; that route CANNOT close the
infinite half, because `ord x = -1` is an EXACTNESS statement — the ramification index of
`1/x` at the place must be `1` — and lying over `(1/x)` only gives `ord (1/x) > 0`.  Getting
`e = 1` from the Dedekind side is the degree count `Σ eᵢfᵢ = [F : K(1/x)] = 2` over the two
branches.

So this half takes the route the docstring below always proposed, and the exactness becomes
true BY CONSTRUCTION: embed `F` into `K⸨t⸩` as a `K(x)`-algebra with `x ↦ t⁻¹` and pull back
the `t`-adic order.  Then `ord x = order (t⁻¹) = -1` because `t` is the uniformiser of
`K⸨t⸩`, with no ramification theory anywhere.

The embedding exists because the reversed sextic `revSext u = u⁶·f(1/u)` has constant term
`1` (the sextic is MONIC — the same fact that makes the two points at infinity rational), so
Hensel's lemma in `K⟦t⟧` — which mathlib has, `K⟦t⟧` being `t`-adically complete — gives
`√(revSext t) ≡ ±1`.  That square root is where `2 ≠ 0` is used, and it is the ONLY place.
Then `x ↦ t⁻¹`, `y ↦ ±√(revSext t)·t⁻³` is a root of the same `Y² − f` that
`exists_functionFieldData` built `F` from, so `AdjoinRoot.lift` produces the embedding and the
`Bool` is the sign.

Two turns of the API are worth recording, both of which cost a cycle:

* `Polynomial.reflect` is NOT needed.  The only fact wanted about the reversed sextic is
  `sext u⁻¹ = revSext u · u⁻⁶`, an identity of VALUES in a field, which `field_simp` proves
  from the two explicit definitions (`sext_inv_eq`).  Reflection lemmas about polynomials —
  and the squarefreeness of the reflected sextic, which would then be needed — are entirely
  avoidable.
* The `Algebra K (LaurentSeries K)` instance found by synthesis is
  `HahnSeries.powerSeriesAlgebra` (through `K⟦t⟧`), NOT the `C`-based `HahnSeries.instAlgebra`.
  The two are propositionally but not definitionally equal, so `HahnSeries.C_eq_algebraMap`
  and `ofPowerSeriesAlg` do not apply to it and there is no `IsScalarTower K K[X] K⸨t⸩`
  instance.  `order_algebraMap` and `aeval_TT_eq_algebraMap` are stated against the instance
  that is actually there.
-/

section PlaceAtInfinity

namespace PlaceAtInfinity

/-- The reversed sextic, evaluated. -/
def revSext (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [CommRing R] (u : R) : R :=
  1 + (c₅ : R) * u + (c₄ : R) * u ^ 2 + (c₃ : R) * u ^ 3
    + (c₂ : R) * u ^ 4 + (c₁ : R) * u ^ 5 + (c₀ : R) * u ^ 6

/-- The reversed sextic has constant term `1`: `revSext u − 1` is `u` times something. -/
lemma revSext_sub_one (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [CommRing R] (u : R) :
    revSext c₀ c₁ c₂ c₃ c₄ c₅ u - 1 =
      u * ((c₅ : R) + (c₄ : R) * u + (c₃ : R) * u ^ 2
        + (c₂ : R) * u ^ 3 + (c₁ : R) * u ^ 4 + (c₀ : R) * u ^ 5) := by
  simp only [revSext]; ring

/-- The reversed sextic as a POLYNOMIAL: `1 + c₅X + c₄X² + c₃X³ + c₂X⁴ + c₁X⁵ + c₀X⁶`. -/
noncomputable def revSextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (R : Type*) [CommRing R] : R[X] :=
  1 + (c₅ : R[X]) * X + (c₄ : R[X]) * X ^ 2 + (c₃ : R[X]) * X ^ 3
    + (c₂ : R[X]) * X ^ 4 + (c₁ : R[X]) * X ^ 5 + (c₀ : R[X]) * X ^ 6

lemma aeval_revSextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {K F : Type*} [CommRing K] [CommRing F]
    [Algebra K F] (u : F) :
    aeval u (revSextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)
      = revSext c₀ c₁ c₂ c₃ c₄ c₅ u := by
  simp [revSextPoly, revSext]

/-- `revSext (1/x) = sext x / x⁶` (PROVEN), the reflection identity in the other direction. -/
lemma revSext_inv_eq (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [Field R] {x : R} (hx : x ≠ 0) :
    revSext c₀ c₁ c₂ c₃ c₄ c₅ x⁻¹
      = sext c₀ c₁ c₂ c₃ c₄ c₅ x * (x⁻¹) ^ 6 := by
  simp only [revSext, sext]
  field_simp


/-- **The reflection identity, as an identity of VALUES in a field**: no `Polynomial.reflect`
is needed, because `u ≠ 0` lets `field_simp` do the work. -/
lemma sext_inv_eq (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [Field R] {u : R} (hu : u ≠ 0) :
    sext c₀ c₁ c₂ c₃ c₄ c₅ u⁻¹ = revSext c₀ c₁ c₂ c₃ c₄ c₅ u * (u⁻¹) ^ 6 := by
  simp only [sext, revSext]
  field_simp

/-! ## Square roots in `K⟦X⟧` by Hensel -/

/-- **Hensel's lemma gives the square root of a power series congruent to `1`.**  This is
the one place `2 ≠ 0` is used in the infinite half. -/
theorem exists_powerSeries_sqrt {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (G : PowerSeries K)
    (hG : G - 1 ∈ Ideal.span {(PowerSeries.X : PowerSeries K)}) :
    ∃ s : PowerSeries K, s ^ 2 = G ∧ s - 1 ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  have h2u : IsUnit (2 : PowerSeries K) := by
    have h : (2 : PowerSeries K) = PowerSeries.C (2 : K) :=
      (map_ofNat (PowerSeries.C (R := K)) 2).symm
    rw [h]
    exact (PowerSeries.C (R := K)).isUnit_map (isUnit_iff_ne_zero.2 h2)
  obtain ⟨a, ha, ha1⟩ :=
    HenselianRing.is_henselian (R := PowerSeries K) (I := Ideal.span {PowerSeries.X})
      (Polynomial.X ^ 2 - Polynomial.C G : (PowerSeries K)[X])
      (monic_X_pow_sub_C G two_ne_zero) 1
      (by
        simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow]
        have h : (1 : PowerSeries K) - G = -(G - 1) := by ring
        rw [h]
        exact neg_mem hG)
      (by
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
          eval_pow, eval_X, one_pow, mul_one, eval_C, Nat.cast_ofNat]
        exact h2u.map _)
  refine ⟨a, ?_, ha1⟩
  have := ha
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at this
  exact this

/-! ## The `t`-adic order on `K⸨X⸩` -/

section Order

variable {K : Type} [Field K]

/-- The image of a power series has nonnegative order. -/
lemma order_ofPowerSeries_nonneg (p : PowerSeries K) :
    0 ≤ (HahnSeries.ofPowerSeries ℤ K p).order := by
  rcases eq_or_ne (HahnSeries.ofPowerSeries ℤ K p) 0 with h | h
  · simp [h]
  · by_contra hlt
    have hc : (HahnSeries.ofPowerSeries ℤ K p).coeff
        (HahnSeries.ofPowerSeries ℤ K p).order ≠ 0 :=
      HahnSeries.coeff_order_eq_zero.not.2 h
    exact hc (by rw [PowerSeries.coeff_coe, if_pos (by omega)])

/-- A constant has order `0`.  (The `Algebra K (LaurentSeries K)` instance goes through
`K⟦X⟧`, so this is `PowerSeries.coe_C` and not `HahnSeries.C_eq_algebraMap`.) -/
lemma order_algebraMap (a : K) : (algebraMap K (LaurentSeries K) a).order = 0 := by
  show (algebraMap K (HahnSeries ℤ K) a).order = 0
  rw [HahnSeries.algebraMap_apply']
  simp only [show (algebraMap K (PowerSeries K) a) = PowerSeries.C a from rfl, PowerSeries.coe_C]
  exact HahnSeries.order_C

/-- `T := ofPowerSeries X` has order `1`. -/
lemma order_T : (HahnSeries.ofPowerSeries ℤ K PowerSeries.X).order = 1 := by
  rw [HahnSeries.ofPowerSeries_X]
  exact HahnSeries.order_single one_ne_zero

lemma T_ne_zero : (HahnSeries.ofPowerSeries ℤ K PowerSeries.X) ≠ 0 := by
  rw [HahnSeries.ofPowerSeries_X]
  intro h
  have := HahnSeries.order_single (a := (1 : ℤ)) (r := (1 : K)) one_ne_zero
  rw [h] at this
  simp at this

/-- The order of a product, over a field. -/
lemma order_mul' {x y : LaurentSeries K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order :=
  HahnSeries.order_mul_of_ne_zero
    (mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr hx) (HahnSeries.leadingCoeff_ne_zero.mpr hy))

/-- **The `t`-adic order, pulled back along a `K`-embedding, is a place.** -/
theorem isPlaceFun_order_comp {F : Type} [Field F] [Algebra K F]
    (φ : F →+* LaurentSeries K)
    (hK : ∀ a : K, φ (algebraMap K F a) = algebraMap K (LaurentSeries K) a)
    {t : F} (ht : (φ t).order = 1) :
    IsPlaceFun K F (fun z => (φ z).order) where
  map_zero := by simp
  map_mul a b ha hb := by
    have hφa : φ a ≠ 0 := (map_ne_zero_iff _ φ.injective).2 ha
    have hφb : φ b ≠ 0 := (map_ne_zero_iff _ φ.injective).2 hb
    simp only [map_mul]
    exact order_mul' hφa hφb
  ultra a b _ _ hab := by
    have hφab : φ a + φ b ≠ 0 := by
      rw [← map_add]
      exact (map_ne_zero_iff _ φ.injective).2 hab
    simpa only [map_add] using HahnSeries.min_order_le_order_add hφab
  map_algebraMap a _ := by
    rw [hK a]
    exact order_algebraMap a
  normalised := ⟨t, ht⟩

end Order

/-! ## The embedding `F ↪ K⸨t⸩` at a branch at infinity -/

section Laurent

variable {K : Type} [Field K]

/-- The uniformiser `t` of `K⸨X⸩`. -/
noncomputable def TT (K : Type) [Field K] : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K PowerSeries.X

lemma order_TT : (TT K).order = 1 := order_T

lemma TT_ne_zero : (TT K) ≠ 0 := T_ne_zero

lemma order_TT_inv : ((TT K)⁻¹).order = -1 := by
  have h1 : (TT K) * (TT K)⁻¹ = 1 := mul_inv_cancel₀ TT_ne_zero
  have h2 : ((TT K) * (TT K)⁻¹).order = (TT K).order + ((TT K)⁻¹).order :=
    order_mul' TT_ne_zero (inv_ne_zero TT_ne_zero)
  rw [h1] at h2
  have h3 : (1 : LaurentSeries K).order = 0 := by
    simp
  rw [h3, order_TT] at h2
  omega

/-- `aeval t` on `K[X]` IS the canonical algebra map into `K⸨X⸩`.  (Stated as an equality of
ring homs, because the `Algebra K (HahnSeries ℤ K)` instance found here is
`HahnSeries.powerSeriesAlgebra`, not the `C`-based `HahnSeries.instAlgebra`, so the two
`aeval`s are propositionally but not definitionally equal.) -/
lemma aeval_TT_eq_algebraMap :
    ((Polynomial.aeval (TT K) : K[X] →ₐ[K] LaurentSeries K) : K[X] →+* LaurentSeries K)
      = algebraMap K[X] (HahnSeries ℤ K) := by
  refine Polynomial.ringHom_ext ?_ ?_
  · intro a
    show Polynomial.aeval (TT K) (Polynomial.C a) = _
    rw [Polynomial.aeval_C, Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C]
    show (algebraMap K (HahnSeries ℤ K)) a = _
    rw [HahnSeries.algebraMap_apply']
    rfl
  · show Polynomial.aeval (TT K) Polynomial.X = _
    rw [Polynomial.aeval_X, Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_X, TT]

lemma aeval_TT_apply (p : K[X]) :
    Polynomial.aeval (TT K) p = algebraMap K[X] (HahnSeries ℤ K) p :=
  DFunLike.congr_fun aeval_TT_eq_algebraMap p

lemma aeval_TT_injective :
    Function.Injective (Polynomial.aeval (TT K) : K[X] →ₐ[K] LaurentSeries K) := by
  intro p q hpq
  refine Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) ?_
  rw [← aeval_TT_apply, ← aeval_TT_apply]
  exact hpq

lemma transcendental_TT_inv : Transcendental K ((TT K)⁻¹) := by
  intro halg
  obtain ⟨p, hp0, hp⟩ : IsAlgebraic K (TT K) := IsAlgebraic.inv_iff.1 halg
  exact hp0 (aeval_TT_injective (show Polynomial.aeval (TT K) p = Polynomial.aeval (TT K) 0 by
    rw [hp, map_zero]))

lemma aeval_TT_inv_ne_zero {p : K[X]} (hp : p ≠ 0) :
    Polynomial.aeval ((TT K)⁻¹) p ≠ 0 := fun h => transcendental_TT_inv ⟨p, hp, h⟩

/-- The embedding `K(x) ↪ K⸨t⸩` sending `x` to `t⁻¹`: the place at infinity. -/
noncomputable def rho (K : Type) [Field K] : RatFunc K →+* LaurentSeries K :=
  IsLocalization.lift (M := nonZeroDivisors K[X]) (S := RatFunc K)
    (g := (Polynomial.aeval ((TT K)⁻¹) : K[X] →ₐ[K] LaurentSeries K).toRingHom)
    (fun y => isUnit_iff_ne_zero.2 (aeval_TT_inv_ne_zero (nonZeroDivisors.coe_ne_zero y)))

@[simp] lemma rho_poly (p : K[X]) :
    rho K (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval ((TT K)⁻¹) p :=
  IsLocalization.lift_eq _ p

lemma rho_const (a : K) : rho K (algebraMap K (RatFunc K) a) = algebraMap K (LaurentSeries K) a := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a, rho_poly,
    show (algebraMap K K[X] a) = Polynomial.C a from rfl, Polynomial.aeval_C]

/-- **The square root at infinity.**  `revSext` has constant term `1`, so Hensel's lemma in
`K⟦t⟧` produces a square root congruent to `1` modulo `t`. -/
theorem exists_laurent_sqrt (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (h2 : (2 : K) ≠ 0) :
    ∃ w : LaurentSeries K, w ^ 2 = revSext c₀ c₁ c₂ c₃ c₄ c₅ (TT K) ∧
      (w = 1 ∨ 1 ≤ (w - 1).order) := by
  set G : PowerSeries K := revSext c₀ c₁ c₂ c₃ c₄ c₅ (PowerSeries.X : PowerSeries K) with hG
  have hGmem : G - 1 ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := by
    rw [hG, revSext_sub_one]
    exact Ideal.mem_span_singleton'.2 ⟨_, mul_comm _ _⟩
  obtain ⟨s, hs2, hs1⟩ := exists_powerSeries_sqrt h2 G hGmem
  refine ⟨HahnSeries.ofPowerSeries ℤ K s, ?_, ?_⟩
  · have h1 : (HahnSeries.ofPowerSeries ℤ K s) ^ 2 = HahnSeries.ofPowerSeries ℤ K (s ^ 2) := by
      rw [map_pow]
    rw [h1, hs2, hG]
    show HahnSeries.ofPowerSeries ℤ K (revSext c₀ c₁ c₂ c₃ c₄ c₅ PowerSeries.X) = _
    simp only [revSext, map_add, map_mul, map_pow, map_intCast, map_one]
    rfl
  · rcases eq_or_ne s 1 with rfl | hne
    · left; simp
    · right
      obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hs1
      have hsub : HahnSeries.ofPowerSeries ℤ K s - 1
          = (TT K) * HahnSeries.ofPowerSeries ℤ K h := by
        have hstep : HahnSeries.ofPowerSeries ℤ K (s - 1)
            = HahnSeries.ofPowerSeries ℤ K (h * PowerSeries.X) := by rw [hh]
        rw [map_sub, map_one, map_mul] at hstep
        rw [hstep, TT]
        ring
      have hh0 : h ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hh
        exact hne (sub_eq_zero.mp hh.symm)
      have hhne : HahnSeries.ofPowerSeries ℤ K h ≠ 0 := by
        intro hz
        exact hh0 (HahnSeries.ofPowerSeries_injective (by rw [hz, map_zero]))
      rw [hsub, order_mul' TT_ne_zero hhne, order_TT]
      have := order_ofPowerSeries_nonneg h
      omega

end Laurent

/-! ## The place of a branch at infinity -/

section InfTower

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K F : Type} [Field K] [Field F]
  [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K K[X] F] [IsScalarTower K[X] (RatFunc K) F]

/-- **The place of a branch at infinity, with `ord x = −1` EXACT.**

The embedding `F ↪ K⸨t⸩` is chosen with `x ↦ t⁻¹`, so the exactness is true by construction
rather than by a ramification count: `ord x = −1` because `t` is the uniformiser of `K⸨t⸩`.
Both branches are covered, the `Bool` being the sign of the square root of the reversed
sextic supplied by Hensel's lemma. -/
theorem exists_isPlaceFun_of_infPt_aux {xx yy : F}
    (hxx : algebraMap K[X] F Polynomial.X = xx)
    (heqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx)
    (hgen : ∀ z : F, ∃ a b d : K[X], Polynomial.aeval xx d ≠ 0 ∧
      z * Polynomial.aeval xx d = Polynomial.aeval xx a + Polynomial.aeval xx b * yy)
    (hsqf : Squarefree (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
    (hnu : ¬ IsUnit (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))
    (h2 : (2 : K) ≠ 0) (sgn : Bool) :
    ∃ o : F → ℤ, IsPlaceFun K F o ∧ o xx = -1 ∧
      -3 < o (yy - (if sgn then 1 else -1) * xx ^ 3) := by
  classical
  -- the tower, in the shape the affine half uses
  have halg : ∀ p : K[X], algebraMap K[X] F p = Polynomial.aeval xx p := fun p => by
    have h : (IsScalarTower.toAlgHom K K[X] F) = (Polynomial.aeval xx : K[X] →ₐ[K] F) :=
      Polynomial.algHom_ext (by simpa using hxx)
    exact congrArg (fun φ => φ p) h
  have hdown : ∀ p : K[X],
      algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval xx p :=
    fun p => by rw [← IsScalarTower.algebraMap_apply, halg]
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a, hdown,
      show (algebraMap K K[X] a) = Polynomial.C a from rfl, Polynomial.aeval_C]
  set α : RatFunc K := algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) with hα
  have hαF : algebraMap (RatFunc K) F α = yy ^ 2 := by
    rw [hα, hdown, aeval_sextPoly, heqn]
  -- `Y² − f` is irreducible over `K(x)`
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C α : (RatFunc K)[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_isSquare_sextPoly hsqf hnu)
  set gpoly : (RatFunc K)[X] := Polynomial.X ^ 2 - Polynomial.C α with hgpoly
  haveI : Fact (Irreducible gpoly) := ⟨hirr⟩
  have hroot : gpoly.eval₂ (Algebra.ofId (RatFunc K) F).toRingHom yy = 0 := by
    simp only [hgpoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    show yy ^ 2 - algebraMap (RatFunc K) F α = 0
    rw [hαF, sub_self]
  -- `F` is generated by `y` over `K(x)`
  have hadj : IntermediateField.adjoin (RatFunc K) {yy} = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨a, b, d, hd, hz⟩ := hgen z
    refine (IntermediateField.mem_adjoin_simple_iff (RatFunc K) z).2
      ⟨Polynomial.C (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        + Polynomial.C (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
          * Polynomial.X, 1, ?_⟩
    have e1 : algebraMap (RatFunc K) F
        (algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval xx a / Polynomial.aeval xx d := by rw [map_div₀, hdown, hdown]
    have e2 : algebraMap (RatFunc K) F
        (algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) d)
        = Polynomial.aeval xx b / Polynomial.aeval xx d := by rw [map_div₀, hdown, hdown]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one, div_one, e1, e2]
    field_simp
    linear_combination hz
  set ψ₀ : AdjoinRoot gpoly →ₐ[RatFunc K] F :=
    AdjoinRoot.liftAlgHom gpoly (Algebra.ofId (RatFunc K) F) yy hroot with hψ₀
  have hψroot : ψ₀ (AdjoinRoot.root gpoly) = yy := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hψsurj : Function.Surjective ψ₀ := by
    intro z
    have hz : z ∈ IntermediateField.adjoin (RatFunc K) {yy} := by rw [hadj]; trivial
    have hle : IntermediateField.adjoin (RatFunc K) {yy} ≤ ψ₀.fieldRange :=
      IntermediateField.adjoin_le_iff.2 (by
        rintro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨AdjoinRoot.root gpoly, hψroot⟩)
    exact hle hz
  set ψ : AdjoinRoot gpoly ≃ₐ[RatFunc K] F :=
    AlgEquiv.ofBijective ψ₀ ⟨ψ₀.toRingHom.injective, hψsurj⟩ with hψ
  -- the square root of the reversed sextic, and the point of `K⸨t⸩` over `t⁻¹`
  obtain ⟨w, hw2, hw1⟩ := exists_laurent_sqrt (K := K) c₀ c₁ c₂ c₃ c₄ c₅ h2
  set eL : LaurentSeries K := if sgn then 1 else -1 with heL
  have heLsq : eL ^ 2 = 1 := by cases sgn <;> simp [heL]
  have heL0 : eL ≠ 0 := by cases sgn <;> simp [heL]
  have heLord : eL.order = 0 := by
    rw [heL]; cases sgn <;> simp [HahnSeries.order_neg]
  set sL : LaurentSeries K := eL * w * ((TT K)⁻¹) ^ 3 with hsL
  have hTi0 : ((TT K)⁻¹) ≠ 0 := inv_ne_zero TT_ne_zero
  have hρα : rho K α = revSext c₀ c₁ c₂ c₃ c₄ c₅ (TT K) * ((TT K)⁻¹) ^ 6 := by
    rw [hα, rho_poly, aeval_sextPoly, sext_inv_eq _ _ _ _ _ _ TT_ne_zero]
  have hsroot : gpoly.eval₂ (rho K) sL = 0 := by
    simp only [hgpoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hρα, hsL]
    rw [mul_pow, mul_pow, heLsq, hw2, one_mul, ← pow_mul]
    ring
  -- the embedding `F ↪ K⸨t⸩`
  set φ : F →+* LaurentSeries K :=
    (AdjoinRoot.lift (rho K) sL hsroot).comp (ψ.symm : F →+* AdjoinRoot gpoly) with hφ
  have hφρ : ∀ c : RatFunc K, φ (algebraMap (RatFunc K) F c) = rho K c := fun c => by
    have h1 : ψ.symm (algebraMap (RatFunc K) F c) = AdjoinRoot.of gpoly c := by
      rw [AlgEquiv.commutes]
      rfl
    show (AdjoinRoot.lift (rho K) sL hsroot) (ψ.symm (algebraMap (RatFunc K) F c)) = rho K c
    rw [h1, AdjoinRoot.lift_of]
  have hφyy : φ yy = sL := by
    have h1 : ψ.symm yy = AdjoinRoot.root gpoly := by
      rw [AlgEquiv.symm_apply_eq, hψ]
      simpa using hψroot.symm
    show (AdjoinRoot.lift (rho K) sL hsroot) (ψ.symm yy) = sL
    rw [h1, AdjoinRoot.lift_root]
  have hxxc : xx = algebraMap (RatFunc K) F RatFunc.X := by
    rw [← RatFunc.algebraMap_X, hdown]
    simp
  have hφxx : φ xx = ((TT K)⁻¹) := by
    rw [hxxc, hφρ, ← RatFunc.algebraMap_X, rho_poly, Polynomial.aeval_X]
  -- the three conclusions
  refine ⟨fun z => (φ z).order, ?_, ?_, ?_⟩
  · refine isPlaceFun_order_comp φ (fun a => ?_) (t := xx⁻¹) ?_
    · rw [IsScalarTower.algebraMap_apply K (RatFunc K) F a, hφρ, rho_const]
    · have hxx0 : xx ≠ 0 := by
        intro h0
        rw [h0] at hφxx
        exact hTi0 (by rw [← hφxx, map_zero])
      rw [map_inv₀, hφxx, inv_inv, order_TT]
  · show (φ xx).order = -1
    rw [hφxx, order_TT_inv]
  · show -3 < (φ (yy - (if sgn then 1 else -1) * xx ^ 3)).order
    rcases eq_or_ne (yy - (if sgn then 1 else -1) * xx ^ 3) 0 with hz | hz
    · rw [hz, map_zero]
      simp
    · have hεF : φ ((if sgn then 1 else -1 : F)) = eL := by
        cases sgn <;> simp [heL]
      have hval : φ (yy - (if sgn then 1 else -1) * xx ^ 3) = eL * (w - 1) * ((TT K)⁻¹) ^ 3 := by
        rw [map_sub, map_mul, map_pow, hφyy, hφxx, hεF, hsL]
        ring
      rcases hw1 with hw | hw
      · rw [hval, hw, sub_self, mul_zero, zero_mul]
        simp
      · have hw0 : w - 1 ≠ 0 := by
          intro h0
          rw [h0] at hw
          simp at hw
        rw [hval, order_mul' (mul_ne_zero heL0 hw0) (pow_ne_zero _ hTi0),
          order_mul' heL0 hw0, heLord, HahnSeries.order_pow, order_TT_inv]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        omega

end InfTower

end PlaceAtInfinity

end PlaceAtInfinity

/-- **LEAF (obligation 1c, INFINITE HALF), PROVEN 2026-07-30**: each branch at infinity
carries a valuation, and `ord x = −1` is EXACT.

The route below is the one that was taken; see the section above for the construction and for
why the Dedekind route of the affine half cannot reach the exactness.  The proof is
`PlaceAtInfinity.exists_isPlaceFun_of_infPt_aux`, instantiated at the tower
`K[X] ⊆ K(x) ⊆ E.F` that `xAlg` installs — the SAME tower the affine half uses; only the
target of the embedding differs.

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
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (h2 : (2 : K) ≠ 0) (sgn : Bool) :
    ∃ o : E.F → ℤ, IsPlaceFun K E.F o ∧
      o E.xx = -1 ∧ -3 < o (E.yy - (if sgn then 1 else -1) * E.xx ^ 3) := by
  classical
  letI : Algebra K[X] E.F := PlaceFromDedekind.xAlg E
  have halg : ∀ p : K[X], algebraMap K[X] E.F p = Polynomial.aeval E.xx p := fun _ => rfl
  haveI : IsScalarTower K K[X] E.F :=
    IsScalarTower.of_algebraMap_eq fun a => by simp [halg]
  have hinj : Function.Injective (algebraMap K[X] E.F) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    exact E.transcendental_xx ⟨p, hp0, by rw [← halg]; exact hp⟩
  letI : Algebra (RatFunc K) E.F := (IsFractionRing.lift (A := K[X]) hinj).toAlgebra
  haveI : IsScalarTower K[X] (RatFunc K) E.F :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hinj p).symm
  have hxx : algebraMap K[X] E.F Polynomial.X = E.xx := by rw [halg]; simp
  have hsqf : Squarefree (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := hsep.squarefree
  have hnu : ¬ IsUnit (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [natDegree_sextPoly] at h1
    norm_num at h1
  exact PlaceAtInfinity.exists_isPlaceFun_of_infPt_aux hxx E.eqn E.gen hsqf hnu h2 sgn

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

Each of the other three carries `hsep` as well, because every consumer has it and because a
leaf that turns out to need it should not have to be restated.

**CORRECTION 2026-07-28: it is NOT true that the other three do not need `hsep`.**  The
paragraph that used to stand here said they were "expected NOT to need it" and that a proof
of one of them using it would show the cut had leaked the genus into the wrong leaf.  That
is wrong for `finrank_residue_pt_eq_one`, which is FALSE without `hsep`: for
`f = x⁶ + 2x²` over `ℚ` there is a `PlaceData` in which the rational point `(0, 0)` has
residue field `ℚ(√2)`.  The full witness is recorded on that theorem.  The reason is not the
genus at all but SMOOTHNESS of the plane model: `hsep` is what makes the local ring at an
affine rational point a DVR, and `exists_isPlaceOfPt` — which is where the places of
rational points are produced in the first place — has always said so in its own docstring.

So the separation is between GENUS and SMOOTHNESS, not between "uses `hsep`" and "does not":

* `not_isRationalGenerator` needs `hsep` for the GENUS (six distinct roots in the pencil
  argument); that is the leaf the section header is about.
* `finrank_residue_pt_eq_one` needs `hsep` for SMOOTHNESS at an affine rational point, and
  `isRationalGenerator_of_divisor_eq_sub_single` inherits that need through it (it uses
  `deg (pt P) = 1`; with a degree-`2` point the pole divisor has degree `2` and `g` does not
  generate).  Neither needs the genus.
* `degOf_divisor_eq_zero` is the only one of the four expected to need `hsep` for nothing at
  all: the degree formula holds in every function field of one variable.  **A proof of it
  that uses `hsep` should still be reported** — that one really would be a leak.

That last prediction now has a mechanical record: `degOf_divisor_eq_zero` is proven below
and its separability hypothesis is `_hsep`.

## RESTRUCTURED 2026-07-28 — three of those four are now PROVEN, over three new leaves

The count did not go down; the SHAPE did.  What used to be four bespoke statements about
this file's interface is now one classical theorem plus two local statements, with every
step between them written in Lean:

* `degOf_poleDivisor_eq_finrank` — **the fundamental identity** `[F : K(g)] = deg (div_∞ g)`,
  [Stichtenoth, Thm. 1.4.11] itself.  `degOf_divisor_eq_zero` follows by applying it to `g`
  and `g⁻¹`, and `isRationalGenerator_of_divisor_eq_sub_single` by applying it at the value
  `1`; both derivations are proven below.  This is now the single deep node of the layer.
* `exists_localDenom_affine`, `exists_localDenom_infinite` — that `O_v` at a rational point
  is the LOCALISATION of the coordinate ring of the relevant chart, not merely a valuation
  ring dominating it.  `finrank_residue_pt_eq_one` follows, over the residue computation
  proven at the end of the `PlaceData` namespace.

`not_isRationalGenerator` is untouched: it is the genus, it is where `hsep` is genuinely
about genus, and its characteristic-`2` audit stands.
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

/-! ### Residues at a place, and when they are constant (PROVEN)

Everything in this block is elementary valuation theory over the interface's axioms, and it
is what reduces `finrank_residue_pt_eq_one` to a purely LOCAL statement about the two charts
of the curve.  The chain is: the strict ultrametric equality (`ord_add_of_lt`) makes a
function congruent to a nonzero constant a unit (`ord_eq_zero_of_vanishesAt_sub`); a
polynomial in a function congruent to `α` is congruent to its value at `α`
(`vanishesAt_aeval_sub_eval`); hence a chart expression `a(t) + b(t)·s` is congruent to
`a(α) + b(α)·β` (`vanishesAt_chart_sub`); hence a QUOTIENT of two such with invertible
denominator is congruent to the quotient of the values (`exists_const_of_localDenom`); and a
place all of whose regular functions are congruent to constants has residue field `K`
(`finrank_residue_eq_one_of_forall_exists_const`). -/

/-- `ord v (−a) = ord v a` (PROVEN): `−1` is a nonzero constant. -/
lemma ord_neg (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) (a : D.F) (ha : a ≠ 0) :
    D.ord v (-a) = D.ord v a := by
  have h : (-a) = algebraMap K D.F (-1) * a := by simp
  have hm : algebraMap K D.F (-1 : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr (by norm_num)
  rw [h, D.ord_mul v _ _ hm ha, D.ord_algebraMap v (-1) (by norm_num), zero_add]

/-- `ord v 1 = 0` (PROVEN). -/
lemma ord_one (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) : D.ord v (1 : D.F) = 0 := by
  have h := D.ord_algebraMap v 1 one_ne_zero
  rwa [map_one] at h

/-- `ord v (aⁿ) = n · ord v a` (PROVEN). -/
lemma ord_pow (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) (a : D.F) (ha : a ≠ 0)
    (n : ℕ) : D.ord v (a ^ n) = n * D.ord v a := by
  induction n with
  | zero => simpa using ord_one D v
  | succ m ih =>
    rw [pow_succ, D.ord_mul v _ _ (pow_ne_zero _ ha) ha, ih]
    push_cast
    ring

/-- `ord v a⁻¹ = − ord v a` (PROVEN). -/
lemma ord_inv (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) (a : D.F) (ha : a ≠ 0) :
    D.ord v a⁻¹ = -D.ord v a := by
  have h1 : D.ord v (a * a⁻¹) = D.ord v a + D.ord v a⁻¹ := D.ord_mul v a a⁻¹ ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, ord_one D v] at h1
  omega

/-- **The ultrametric inequality is an EQUALITY when the two orders differ** (PROVEN).

`ord_add` alone gives only `min ≤`; the reverse comes from applying it again to `a + b` and
`−b`, whose sum is `a`.  This is the workhorse of the residue computation: it is what makes
a function congruent to a nonzero constant a unit of the local ring. -/
lemma ord_add_of_lt (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {a b : D.F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hlt : D.ord v a < D.ord v b) :
    D.ord v (a + b) = D.ord v a := by
  have hab : a + b ≠ 0 := by
    intro h
    have : b = -a := by linear_combination h
    rw [this, ord_neg D v a ha] at hlt
    exact lt_irrefl _ hlt
  have h1 := D.ord_add v a b ha hb hab
  have h2 := D.ord_add v (a + b) (-b) hab (neg_ne_zero.mpr hb) (by simpa using ha)
  rw [ord_neg D v b hb] at h2
  simp only [add_neg_cancel_right] at h2
  omega

/-- Membership in the valuation ring is nonnegativity of the order (PROVEN, definitional). -/
lemma mem_valRing_iff (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {z : D.F} :
    z ∈ D.valRing v ↔ 0 ≤ D.ord v z := Iff.rfl

/-- The valuation ring is a `K`-subalgebra, so it is closed under `aeval` (PROVEN). -/
lemma aeval_mem_valRing (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {t : D.F}
    (ht : t ∈ D.valRing v) (h : K[X]) : aeval t h ∈ D.valRing v := by
  have := Polynomial.aeval_algHom_apply (D.valRing v).val (⟨t, ht⟩ : D.valRing v) h
  simp only [Subalgebra.coe_val] at this
  rw [this]
  exact SetLike.coe_mem _

/-- If `t ≡ α` at `v` then `h(t) ≡ h(α)` at `v`, for every polynomial `h` over `K` (PROVEN):
`h − h(α)` is divisible by `X − α`. -/
lemma vanishesAt_aeval_sub_eval (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {t : D.F}
    {α : K} (ht : t ∈ D.valRing v) (hα : D.VanishesAt v (t - algebraMap K D.F α))
    (h : K[X]) : D.VanishesAt v (aeval t h - algebraMap K D.F (h.eval α)) := by
  obtain ⟨k, hk⟩ : (X - C α) ∣ (h - C (h.eval α)) :=
    dvd_iff_isRoot.mpr (by simp [IsRoot])
  have hev : aeval t h - algebraMap K D.F (h.eval α) = aeval t k * (t - algebraMap K D.F α) := by
    have := congrArg (fun p : K[X] => aeval t p) hk
    simp only [map_sub, map_mul, aeval_X, aeval_C] at this
    rw [this]; ring
  rw [hev]
  exact vanishesAt_mul_left (aeval_mem_valRing D v ht k) hα

/-- **A function congruent to a NONZERO constant at `v` is a unit there** (PROVEN). -/
lemma ord_eq_zero_of_vanishesAt_sub (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t : D.F} {α : K} (hα : α ≠ 0) (h : D.VanishesAt v (t - algebraMap K D.F α)) :
    t ≠ 0 ∧ D.ord v t = 0 := by
  have hαF : algebraMap K D.F α ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr hα
  have hordα : D.ord v (algebraMap K D.F α) = 0 := D.ord_algebraMap v α hα
  rcases h with h | h
  · have ht : t = algebraMap K D.F α := by linear_combination h
    exact ⟨by rw [ht]; exact hαF, by rw [ht, hordα]⟩
  · have hne : t - algebraMap K D.F α ≠ 0 := by
      intro hz; rw [hz, D.ord_zero] at h; exact lt_irrefl 0 h
    have ht : t ≠ 0 := by
      intro hz
      rw [hz, zero_sub, ord_neg D v _ hαF, hordα] at h
      exact lt_irrefl 0 h
    refine ⟨ht, ?_⟩
    have hsum := ord_add_of_lt D v (a := algebraMap K D.F α) (b := t - algebraMap K D.F α)
      hαF hne (by rw [hordα]; exact h)
    have hid : algebraMap K D.F α + (t - algebraMap K D.F α) = t := by ring
    rw [hid, hordα] at hsum
    exact hsum

/-- Vanishing is closed under negation (PROVEN). -/
lemma vanishesAt_neg {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K} {v : D.Places} {a : D.F}
    (ha : D.VanishesAt v a) : D.VanishesAt v (-a) := by
  rcases ha with rfl | ha
  · exact Or.inl neg_zero
  · have ha0 : a ≠ 0 := by rintro rfl; rw [D.ord_zero] at ha; exact lt_irrefl 0 ha
    exact Or.inr (by rw [ord_neg D v a ha0]; exact ha)

/-- Vanishing may be cancelled against a unit of the local ring (PROVEN). -/
lemma vanishesAt_of_mul_unit (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {w u : D.F}
    (hu : u ≠ 0) (hordu : D.ord v u = 0) (h : D.VanishesAt v (w * u)) : D.VanishesAt v w := by
  rcases h with h | h
  · exact Or.inl ((mul_eq_zero.mp h).resolve_right hu)
  · rcases eq_or_ne w 0 with rfl | hw
    · exact Or.inl rfl
    · exact Or.inr (by rw [D.ord_mul v _ _ hw hu, hordu] at h; omega)

/-- `t ≡ α` puts `t` in the valuation ring (PROVEN). -/
lemma mem_valRing_of_vanishesAt_sub (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t : D.F} {α : K} (h : D.VanishesAt v (t - algebraMap K D.F α)) : t ∈ D.valRing v := by
  have h1 : t - algebraMap K D.F α ∈ D.valRing v := by
    rcases h with h | h
    · rw [h]; exact zero_mem _
    · exact le_of_lt h
  have h2 : algebraMap K D.F α ∈ D.valRing v := (D.valRing v).algebraMap_mem α
  have h3 := (D.valRing v).add_mem h1 h2
  simpa using h3

/-- **A chart element has the residue its coordinates say it has** (PROVEN):
`a(t) + b(t)·s ≡ a(α) + b(α)·β` at `v`, whenever `t ≡ α` and `s ≡ β` there. -/
lemma vanishesAt_chart_sub (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t s : D.F} {α β : K}
    (ht : D.VanishesAt v (t - algebraMap K D.F α))
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) (a b : K[X]) :
    D.VanishesAt v (aeval t a + aeval t b * s
      - algebraMap K D.F (a.eval α + b.eval α * β)) := by
  have htm : t ∈ D.valRing v := mem_valRing_of_vanishesAt_sub D v ht
  have hA : D.VanishesAt v (aeval t a - algebraMap K D.F (a.eval α)) :=
    vanishesAt_aeval_sub_eval D v htm ht a
  have hB : D.VanishesAt v (aeval t b - algebraMap K D.F (b.eval α)) :=
    vanishesAt_aeval_sub_eval D v htm ht b
  have hB1 : D.VanishesAt v (aeval t b * (s - algebraMap K D.F β)) :=
    vanishesAt_mul_left (aeval_mem_valRing D v htm b) hs
  have hB2 : D.VanishesAt v (algebraMap K D.F β * (aeval t b - algebraMap K D.F (b.eval α))) :=
    vanishesAt_mul_left ((D.valRing v).algebraMap_mem β) hB
  have hid : aeval t a + aeval t b * s - algebraMap K D.F (a.eval α + b.eval α * β)
      = (aeval t a - algebraMap K D.F (a.eval α))
        + aeval t b * (s - algebraMap K D.F β)
        + algebraMap K D.F β * (aeval t b - algebraMap K D.F (b.eval α)) := by
    rw [map_add, map_mul]; ring
  rw [hid]
  exact vanishesAt_add (vanishesAt_add hA hB1) hB2

/-- **A local normal form forces the residue to be a constant** (PROVEN).

If `t ≡ α` and `s ≡ β` at `v`, and `z` can be written in the chart `K[t, s]` as a quotient
`(a(t) + b(t)·s)/(e₁(t) + e₂(t)·s)` whose DENOMINATOR does not vanish at `(α, β)`, then `z`
is congruent at `v` to the constant `(a(α) + b(α)·β)/(e₁(α) + e₂(α)·β)`.  Both charts of the
curve — the affine one `(t, s) = (x, y)` at `(α, β)`, and the one at infinity
`(t, s) = (1/x, y/x³)` at `(0, ±1)` — instantiate this.

**The denominator must be allowed to involve `s`.**  Restricting it to a polynomial `d(t)`
in the abscissa alone, with `d(α) ≠ 0`, makes the hypothesis unsatisfiable for some `z ∈ O_v`
and the leaf below FALSE: for `β ≠ 0` the function `1/(y + β)` is regular at `(α, β)` — its
denominator takes the value `2β ≠ 0` there — but has a pole at the conjugate point
`(α, −β)`, while every `(a(x) + b(x)y)/d(x)` with `d(α) ≠ 0` is regular at BOTH points above
`x = α`.  (This was found by auditing an earlier form of the leaf, which had exactly that
restriction.) -/
theorem exists_const_of_localDenom (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t s : D.F} {α β : K}
    (ht : D.VanishesAt v (t - algebraMap K D.F α))
    (hs : D.VanishesAt v (s - algebraMap K D.F β))
    {z : D.F} {a b e₁ e₂ : K[X]} (hd : e₁.eval α + e₂.eval α * β ≠ 0)
    (heq : z * (aeval t e₁ + aeval t e₂ * s) = aeval t a + aeval t b * s) :
    ∃ c : K, D.VanishesAt v (z - algebraMap K D.F c) := by
  have hN := vanishesAt_chart_sub D v ht hs a b
  have hU := vanishesAt_chart_sub D v ht hs e₁ e₂
  obtain ⟨hdne, hdord⟩ := ord_eq_zero_of_vanishesAt_sub D v hd hU
  refine ⟨(a.eval α + b.eval α * β) / (e₁.eval α + e₂.eval α * β), ?_⟩
  set δ : K := e₁.eval α + e₂.eval α * β with hδ
  set ν : K := a.eval α + b.eval α * β with hν
  set c : K := ν / δ with hc
  refine vanishesAt_of_mul_unit D v hdne hdord ?_
  have hconst : algebraMap K D.F ν = algebraMap K D.F c * algebraMap K D.F δ := by
    rw [← map_mul]
    congr 1
    rw [hc, div_mul_cancel₀ _ hd]
  have hC : D.VanishesAt v (algebraMap K D.F c
      * (aeval t e₁ + aeval t e₂ * s - algebraMap K D.F δ)) :=
    vanishesAt_mul_left ((D.valRing v).algebraMap_mem c) hU
  have hw : (z - algebraMap K D.F c) * (aeval t e₁ + aeval t e₂ * s)
      = (aeval t a + aeval t b * s - algebraMap K D.F ν)
        + (-(algebraMap K D.F c * (aeval t e₁ + aeval t e₂ * s - algebraMap K D.F δ))) := by
    linear_combination heq + hconst
  rw [hw]
  exact vanishesAt_add hN (vanishesAt_neg hC)

/-- The residue field at a place is nontrivial (PROVEN): `1` does not vanish. -/
lemma residue_nontrivial (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) :
    Nontrivial (D.residue v) := by
  refine Ideal.Quotient.nontrivial_iff.mpr (fun htop => ?_)
  have h1 : (1 : D.valRing v) ∈ D.valMax v := by rw [htop]; exact Submodule.mem_top
  have h1' : D.VanishesAt v (1 : D.F) := h1
  rcases h1' with h | h
  · exact one_ne_zero h
  · rw [ord_one D v] at h; exact lt_irrefl 0 h

/-- **`[κ(v) : K] = 1` as soon as every element of `O_v` is congruent to a constant** (PROVEN).

This is the whole of `finrank_residue_pt_eq_one` apart from the local statement at the point:
`K → κ(v)` is injective because `K` is a field and `κ(v)` is nontrivial, so surjectivity
makes it an isomorphism of `K`-algebras. -/
theorem finrank_residue_eq_one_of_forall_exists_const (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (v : D.Places)
    (hres : ∀ z : D.F, 0 ≤ D.ord v z → ∃ c : K, D.VanishesAt v (z - algebraMap K D.F c)) :
    Module.finrank K (D.residue v) = 1 := by
  haveI := residue_nontrivial D v
  have hbij : Function.Bijective (algebraMap K (D.residue v)) := by
    refine ⟨(algebraMap K (D.residue v)).injective, ?_⟩
    intro ξ
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective ξ
    obtain ⟨c, hc⟩ := hres (z : D.F) z.2
    refine ⟨c, ?_⟩
    show Ideal.Quotient.mk (D.valMax v) (algebraMap K (D.valRing v) c) = _
    refine Ideal.Quotient.eq.mpr ?_
    show D.VanishesAt v ((algebraMap K (D.valRing v) c : D.F) - (z : D.F))
    have hco : (algebraMap K (D.valRing v) c : D.F) = algebraMap K D.F c := rfl
    rw [hco]
    have := vanishesAt_neg hc
    rwa [neg_sub] at this
  have e : K ≃ₐ[K] D.residue v := AlgEquiv.ofBijective (Algebra.ofId K (D.residue v)) hbij
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-! ### Zeros and poles separately (PROVEN)

`div g` splits into its positive and negative parts, `div_0 g − div_∞ g`, and inverting `g`
exchanges them.  This is the bookkeeping that turns the fundamental identity
`[F : K(g)] = deg (div_∞ g)` into the degree formula `deg (div g) = 0`: apply it to `g` and
to `g⁻¹` and use `K(g) = K(g⁻¹)`. -/

/-- The **pole divisor** `div_∞ g = Σ_v max(−ord_v g, 0)·v`. -/
noncomputable def poleDivisor (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) : D.Divisors :=
  (D.divisor g).mapRange (fun n => max (-n) 0) (by simp)

/-- The **zero divisor** `div_0 g = Σ_v max(ord_v g, 0)·v`. -/
noncomputable def zeroDivisor (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) : D.Divisors :=
  (D.divisor g).mapRange (fun n => max n 0) (by simp)

@[simp] lemma poleDivisor_apply (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) (v : D.Places) :
    D.poleDivisor g v = max (-(D.divisor g v)) 0 := Finsupp.mapRange_apply

@[simp] lemma zeroDivisor_apply (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) (v : D.Places) :
    D.zeroDivisor g v = max (D.divisor g v) 0 := Finsupp.mapRange_apply

/-- `div g = div_0 g − div_∞ g` (PROVEN). -/
lemma divisor_eq_zeroDivisor_sub_poleDivisor (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) :
    D.divisor g = D.zeroDivisor g - D.poleDivisor g := by
  ext v
  simp only [Finsupp.sub_apply, zeroDivisor_apply, poleDivisor_apply]
  omega

/-- `div_∞ (g⁻¹) = div_0 g` (PROVEN); the junk conventions `0⁻¹ = 0` and `div 0 = 0` make
the degenerate case go through unchanged. -/
lemma poleDivisor_inv (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) :
    D.poleDivisor g⁻¹ = D.zeroDivisor g := by
  ext v
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · simp only [poleDivisor_apply, zeroDivisor_apply, divisor_apply D (inv_ne_zero hg) v,
      divisor_apply D hg v, ord_inv D v g hg]
    omega

/-- `K⟮g⁻¹⟯ = K⟮g⟯` (PROVEN), with no side condition — `0⁻¹ = 0` handles `g = 0`. -/
lemma adjoin_inv_eq {F : Type} [Field F] [Algebra K F] (g : F) :
    IntermediateField.adjoin K {g⁻¹} = IntermediateField.adjoin K {g} := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K g)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K g⁻¹)
    rwa [inv_inv] at h

/-! ### Purely inseparable descent: a `PlaceData` cannot exist in characteristic `2`

This block is the char-`2` half of `not_isRationalGenerator`, discharged once and for all
rather than left as prose in that leaf's falsity audit.  See `two_ne_zero`. -/

lemma aeval_xx_injective (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) :
    Function.Injective (Polynomial.aeval D.xx : K[X] →ₐ[K] D.F) :=
  transcendental_iff_injective.mp D.transcendental_xx

lemma aeval_xx_ne_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {p : K[X]} (hp : p ≠ 0) :
    aeval D.xx p ≠ 0 := fun h => hp (D.aeval_xx_injective (by simpa using h))

lemma xx_ne_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : D.xx ≠ 0 := by
  simpa using D.aeval_xx_ne_zero (p := (X : K[X])) X_ne_zero

/-- Auxiliary induction for `ord_aeval_of_ord_xx`. -/
lemma ord_aeval_of_ord_xx_aux (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    (hv : D.ord v D.xx = -1) (n : ℕ) :
    ∀ p : K[X], p.natDegree ≤ n → p ≠ 0 →
      D.ord v (aeval D.xx p) = -(p.natDegree : ℤ) := by
  induction n with
  | zero =>
      intro p hp hp0
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp (Nat.le_zero.mp hp)
      subst ha
      have ha0 : a ≠ 0 := by
        intro h
        rw [h] at hp0
        simp at hp0
      simp [D.ord_algebraMap v a ha0]
  | succ m ih =>
      intro p hp hp0
      rcases le_or_gt p.natDegree m with h | h
      · exact ih p h hp0
      have hxx := D.xx_ne_zero
      have ha0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
      have haF : algebraMap K D.F p.leadingCoeff ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr ha0
      have hleadval : aeval D.xx (C p.leadingCoeff * X ^ p.natDegree)
          = algebraMap K D.F p.leadingCoeff * D.xx ^ p.natDegree := by simp
      have hleadne : aeval D.xx (C p.leadingCoeff * X ^ p.natDegree) ≠ 0 := by
        rw [hleadval]
        exact mul_ne_zero haF (pow_ne_zero _ hxx)
      have hlead : D.ord v (aeval D.xx (C p.leadingCoeff * X ^ p.natDegree))
          = -(p.natDegree : ℤ) := by
        rw [hleadval, D.ord_mul v _ _ haF (pow_ne_zero _ hxx),
          D.ord_algebraMap v _ ha0, D.ord_pow v D.xx hxx, hv]
        ring
      have hsplit : aeval D.xx (C p.leadingCoeff * X ^ p.natDegree)
          + aeval D.xx p.eraseLead = aeval D.xx p := by
        rw [← map_add, add_comm]
        exact congrArg _ p.eraseLead_add_C_mul_X_pow
      rcases eq_or_ne p.eraseLead 0 with he | he
      · rw [← hsplit, he, map_zero, add_zero]
        exact hlead
      · have hle : p.eraseLead.natDegree ≤ m := by
          have h1 := Polynomial.eraseLead_natDegree_le p
          omega
        have herase := ih p.eraseLead hle he
        have hne : aeval D.xx p.eraseLead ≠ 0 := D.aeval_xx_ne_zero he
        have hltord : D.ord v (aeval D.xx (C p.leadingCoeff * X ^ p.natDegree))
            < D.ord v (aeval D.xx p.eraseLead) := by
          rw [hlead, herase]
          have c1 : (p.eraseLead.natDegree : ℤ) ≤ (m : ℤ) := by exact_mod_cast hle
          have c2 : (m : ℤ) < (p.natDegree : ℤ) := by exact_mod_cast h
          omega
        rw [← hsplit, D.ord_add_of_lt v hleadne hne hltord, hlead]

/-- **At a place where `x` has a simple pole, `ord (p(x)) = −deg p`** (PROVEN).

The strict ultrametric equality applied to the leading term: `ord (aₙxⁿ) = −n` while every
lower term has strictly larger order, so the sum has order exactly `−n`. -/
lemma ord_aeval_of_ord_xx (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    (hv : D.ord v D.xx = -1) {p : K[X]} (hp : p ≠ 0) :
    D.ord v (aeval D.xx p) = -(p.natDegree : ℤ) :=
  D.ord_aeval_of_ord_xx_aux v hv p.natDegree p le_rfl hp

/-- **In characteristic `2`, a place is determined by `ord x = −1`** (PROVEN).

The engine of `two_ne_zero`.  If `2 = 0` in `K` then squaring kills the cross term of the
normal form `z·d(x) = a(x) + b(x)·y` supplied by `gen`, so

    z² · d(x)² = a(x)² + b(x)²·f(x) = e(x),   e := a² + b²·f ∈ K[X],

i.e. every SQUARE in `F` already lies in `K(x)` — which is `F/K(x)` being purely inseparable.
At a place with `ord x = −1` the order of a polynomial in `x` is minus its degree
(`ord_aeval_of_ord_xx`), so `2·ord z = ord (z²) = deg (d²) − deg e` is computed from `d` and
`e` alone, with no reference to the place.  Two such places therefore have the same `ord`,
and `ord_injective` makes them equal. -/
lemma ord_eq_of_ord_xx_eq_neg_one (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (h2 : (2 : K) = 0)
    {v w : D.Places} (hv : D.ord v D.xx = -1) (hw : D.ord w D.xx = -1) : v = w := by
  refine D.ord_injective ?_
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [D.ord_zero, D.ord_zero]
  obtain ⟨a, b, d, hd, hgen⟩ := D.gen z
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hd rfl
  have h2F : (2 : D.F) = 0 := by
    have h : algebraMap K D.F (2 : K) = 0 := by rw [h2, map_zero]
    rwa [map_ofNat] at h
  set e : K[X] := a ^ 2 + b ^ 2 * sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K with he
  have hsq : z ^ 2 * aeval D.xx d ^ 2 = aeval D.xx e := by
    have hyy : D.yy ^ 2 = aeval D.xx (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
      rw [aeval_sextPoly]
      exact D.eqn
    have hg2 : (z * aeval D.xx d) ^ 2 = (aeval D.xx a + aeval D.xx b * D.yy) ^ 2 := by
      rw [hgen]
    have hexp : (aeval D.xx a + aeval D.xx b * D.yy) ^ 2
        = aeval D.xx a ^ 2 + aeval D.xx b ^ 2 * D.yy ^ 2
          + 2 * (aeval D.xx a * (aeval D.xx b * D.yy)) := by ring
    rw [hexp, h2F, zero_mul, add_zero, hyy] at hg2
    have hE : aeval D.xx e = aeval D.xx a ^ 2
        + aeval D.xx b ^ 2 * aeval D.xx (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
      rw [he]
      simp only [map_add, map_mul, map_pow]
    rw [hE, ← hg2]
    ring
  have hd2 : aeval D.xx d ^ 2 ≠ 0 := pow_ne_zero 2 (D.aeval_xx_ne_zero hd0)
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have he0 : e ≠ 0 := by
    intro h
    rw [h, map_zero] at hsq
    exact (mul_ne_zero hz2 hd2) hsq
  have hdsq0 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have hpow : aeval D.xx d ^ 2 = aeval D.xx (d ^ 2) := by rw [map_pow]
  have key : ∀ u : D.Places, D.ord u D.xx = -1 →
      2 * D.ord u z = ((d ^ 2).natDegree : ℤ) - (e.natDegree : ℤ) := by
    intro u hu
    have h1 : D.ord u (z ^ 2 * aeval D.xx d ^ 2) = D.ord u (aeval D.xx e) :=
      congrArg (D.ord u) hsq
    rw [D.ord_mul u _ _ hz2 hd2, D.ord_pow u z hz 2, hpow,
      D.ord_aeval_of_ord_xx u hu hdsq0, D.ord_aeval_of_ord_xx u hu he0] at h1
    push_cast at h1 ⊢
    omega
  have hfin := (key v hv).trans (key w hw).symm
  omega

/-- **A `PlaceData` forces `2 ≠ 0` in `K`** (PROVEN).

The two points at infinity are distinct places (`pt_injective`) at both of which `ord x = −1`
(`ord_pt_infinite`).  In characteristic `2` that is impossible:
`ord_eq_of_ord_xx_eq_neg_one` shows a place with `ord x = −1` is unique there, because
`F/K(x)` is purely inseparable and a purely inseparable extension has exactly one place above
each place of the base.

This is exactly the char-`2` half that the falsity audit above `not_isRationalGenerator`
predicted: that leaf is true in characteristic `2` not because the pencil argument covers it
— it does not, and over a perfect `K` of characteristic `2` the function field of a separable
sextic really IS rational — but because no `PlaceData` exists there at all.  Rather than
leaving that as prose, it is proven here once, so every consumer may simply use `2 ≠ 0`.

Separability is NOT needed. -/
theorem two_ne_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) : (2 : K) ≠ 0 := by
  intro h2
  have h := D.ord_eq_of_ord_xx_eq_neg_one h2
    (D.ord_pt_infinite true).1 (D.ord_pt_infinite false).1
  have hb : (Sum.inr true : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) = Sum.inr false := D.pt_injective h
  simp at hb

/-! ### `O_v` IS the local ring of a smooth chart point (PROVEN, 2026-07-30)

The two `exists_localDenom_*` leaves below both say the same thing in a different chart: a
function regular at the place of a rational point is a chart fraction whose DENOMINATOR does
not vanish at that point, i.e. `O_v` is not merely a valuation ring DOMINATING the local ring
of the plane model — it EQUALS it.

The classical proof of that is "a valuation ring of `Frac R` dominating a DVR `R` is `R`",
which needs the coordinate ring built as a Lean object, localised at the point, and shown to
be regular.  None of that is needed here.  What replaces it is a DESCENT on `ord_v` of the
denominator, over the interface's valuation axioms alone:

* `ord_chart_eq_zero_iff`: a chart expression is a unit at `v` exactly when its value at the
  point is nonzero.  So "admissible denominator" IS "denominator of order `0`", and the
  descent's stopping condition is the conclusion.
* if the denominator vanishes then so does the numerator (`chart_value_eq_zero`, since `z` is
  regular), and one uniformiser cancels from both — `exists_localDenom_step`.
* the order of the denominator drops by `ord_v` of that uniformiser, which is `≥ 1`, so the
  descent terminates: `exists_localDenom_chart`.

**Which uniformiser it is depends on the point, and this is exactly where smoothness enters.**
At a point with `2β ≠ 0` it is `t − α`, and the cancellation is made visible by multiplying by
the CONJUGATE `s + β`, a unit there, using `(s − β)(s + β) = g(t) − β² = (t − α)·h(t)`.  At a
point with `β = 0` that fails — `s + β = s` is not a unit — and the uniformiser is `s`
instead, with `t − α = s²/h(t)`; that needs `h(α) ≠ 0`, which for `β = 0` is `g'(α) ≠ 0`, i.e.
separability.  The disjunction `2β ≠ 0 ∨ (β = 0 ∧ h(α) ≠ 0)` is smoothness of the chart at the
point, and the audit on `finrank_residue_pt_eq_one` shows the leaf is FALSE without it.
-/

/-- A chart expression lies in the valuation ring (PROVEN). -/
lemma chart_mem_valRing (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {t s : D.F} {α β : K}
    (ht : D.VanishesAt v (t - algebraMap K D.F α))
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) (e₁ e₂ : K[X]) :
    0 ≤ D.ord v (aeval t e₁ + aeval t e₂ * s) := by
  have htm : t ∈ D.valRing v := mem_valRing_of_vanishesAt_sub D v ht
  have hsm : s ∈ D.valRing v := mem_valRing_of_vanishesAt_sub D v hs
  have h1 : aeval t e₁ ∈ D.valRing v := aeval_mem_valRing D v htm e₁
  have h2 : aeval t e₂ ∈ D.valRing v := aeval_mem_valRing D v htm e₂
  exact (D.valRing v).add_mem h1 ((D.valRing v).mul_mem h2 hsm)

/-- A vanishing constant is `0` (PROVEN). -/
lemma eq_zero_of_vanishesAt_algebraMap (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {c : K}
    (h : D.VanishesAt v (algebraMap K D.F c)) : c = 0 := by
  by_contra hc
  rcases h with h | h
  · exact hc ((map_eq_zero_iff _ (algebraMap K D.F).injective).1 h)
  · rw [D.ord_algebraMap v c hc] at h
    exact lt_irrefl 0 h

/-- **A chart expression is a unit at `v` exactly when its value at the point is nonzero**
(PROVEN).  This is what makes the induction below terminate in the right place: the order of
the denominator is `0` precisely when the denominator is admissible. -/
lemma ord_chart_eq_zero_iff (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {t s : D.F}
    {α β : K} (ht : D.VanishesAt v (t - algebraMap K D.F α))
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) {e₁ e₂ : K[X]}
    (hne : aeval t e₁ + aeval t e₂ * s ≠ 0) :
    D.ord v (aeval t e₁ + aeval t e₂ * s) = 0 ↔ e₁.eval α + e₂.eval α * β ≠ 0 := by
  have hV := vanishesAt_chart_sub D v ht hs e₁ e₂
  constructor
  · intro h0 hδ
    rw [hδ, map_zero, sub_zero] at hV
    rcases hV with hV | hV
    · exact hne hV
    · omega
  · intro hδ
    exact (ord_eq_zero_of_vanishesAt_sub D v hδ hV).2

/-- The value of a chart expression whose order is positive is `0` (PROVEN). -/
lemma chart_value_eq_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places) {t s : D.F}
    {α β : K} (ht : D.VanishesAt v (t - algebraMap K D.F α))
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) {e₁ e₂ : K[X]}
    (hpos : 0 < D.ord v (aeval t e₁ + aeval t e₂ * s)) :
    e₁.eval α + e₂.eval α * β = 0 := by
  have hV := vanishesAt_chart_sub D v ht hs e₁ e₂
  have hne : aeval t e₁ + aeval t e₂ * s ≠ 0 := by
    intro h0; rw [h0, D.ord_zero] at hpos; exact lt_irrefl 0 hpos
  refine eq_zero_of_vanishesAt_algebraMap D v (c := e₁.eval α + e₂.eval α * β) ?_
  have hsum := vanishesAt_add (D := D) (v := v) (Or.inr hpos) (vanishesAt_neg hV)
  have hid : (aeval t e₁ + aeval t e₂ * s)
      + -(aeval t e₁ + aeval t e₂ * s - algebraMap K D.F (e₁.eval α + e₂.eval α * β))
      = algebraMap K D.F (e₁.eval α + e₂.eval α * β) := by ring
  rwa [hid] at hsum

/-- **The identity that cancels the uniformiser at a point with `2β ≠ 0`** (PROVEN).

At such a point `t − α` is the uniformiser, and multiplying a chart expression that VANISHES
at the point by the conjugate `s + β` makes the factor `t − α` visible.  `s² = g(t)` and
`g − β² = (X − α)·h` are what turn `(s − β)(s + β)` into `(t − α)·h(t)`. -/
lemma chart_mul_conj (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t s : D.F} {α β : K} {g h : K[X]}
    (hcurve : s ^ 2 = aeval t g)
    (hg : g = Polynomial.C (β ^ 2) + (Polynomial.X - Polynomial.C α) * h)
    {P Q P₁ Q₁ : K[X]}
    (hP : P = Polynomial.C (P.eval α) + (Polynomial.X - Polynomial.C α) * P₁)
    (hQ : Q = Polynomial.C (Q.eval α) + (Polynomial.X - Polynomial.C α) * Q₁)
    (hPQ : P.eval α + Q.eval α * β = 0) :
    (aeval t P + aeval t Q * s) * (algebraMap K D.F β + s)
      = (t - algebraMap K D.F α)
        * (aeval t (P₁ * Polynomial.C β + Q₁ * g + Polynomial.C (Q.eval α) * h)
            + aeval t (P₁ + Q₁ * Polynomial.C β) * s) := by
  have hPe : aeval t P
      = algebraMap K D.F (P.eval α) + (t - algebraMap K D.F α) * aeval t P₁ := by
    rw [hP]; simp
  have hQe : aeval t Q
      = algebraMap K D.F (Q.eval α) + (t - algebraMap K D.F α) * aeval t Q₁ := by
    rw [hQ]; simp
  have hGe : aeval t g
      = (algebraMap K D.F β) ^ 2 + (t - algebraMap K D.F α) * aeval t h := by
    rw [hg]; simp [map_pow]
  have hPQF : algebraMap K D.F (P.eval α)
      + algebraMap K D.F (Q.eval α) * algebraMap K D.F β = 0 := by
    rw [← map_mul, ← map_add, hPQ, map_zero]
  rw [hGe] at hcurve
  simp only [map_add, map_mul, aeval_C, hGe]
  rw [hPe, hQe]
  linear_combination (algebraMap K D.F (Q.eval α)
      + (t - algebraMap K D.F α) * aeval t Q₁) * hcurve
    + (s + algebraMap K D.F β) * hPQF

/-- **The identity that cancels the uniformiser at a point with `β = 0` and `g'(α) ≠ 0`**
(PROVEN).  There the uniformiser is `s`, not `t − α`: `t − α = s²/h(t)` with `h(α) = g'(α)`
a unit, and multiplying by `h(t)` makes the factor `s` visible. -/
lemma chart_mul_deriv (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t s : D.F} {α : K} {g h : K[X]}
    (hcurve : s ^ 2 = aeval t g)
    (hg : g = (Polynomial.X - Polynomial.C α) * h)
    {P Q P₁ : K[X]}
    (hP : P = (Polynomial.X - Polynomial.C α) * P₁) :
    (aeval t P + aeval t Q * s) * aeval t h
      = s * (aeval t (Q * h) + aeval t P₁ * s) := by
  have hPe : aeval t P = (t - algebraMap K D.F α) * aeval t P₁ := by rw [hP]; simp
  have hGe : aeval t g = (t - algebraMap K D.F α) * aeval t h := by rw [hg]; simp
  rw [hGe] at hcurve
  simp only [map_mul]
  rw [hPe]
  linear_combination (-(aeval t P₁)) * hcurve


/-- Taylor's formula to first order (PROVEN): `P = P(α) + (X − α)·P₁`. -/
lemma exists_sub_eval_factor (P : K[X]) (α : K) :
    ∃ P₁ : K[X], P = Polynomial.C (P.eval α) + (Polynomial.X - Polynomial.C α) * P₁ := by
  obtain ⟨P₁, hP₁⟩ : (Polynomial.X - Polynomial.C α) ∣ (P - Polynomial.C (P.eval α)) :=
    dvd_iff_isRoot.2 (by simp [IsRoot])
  exact ⟨P₁, by rw [← hP₁]; ring⟩

/-- **One step of the descent on the denominator** (PROVEN).

If a chart fraction `z = (A(t) + B(t)s)/(e₁(t) + e₂(t)s)` has a denominator that VANISHES at
the point, then so does its numerator (because `z` is regular), and one uniformiser can be
cancelled from both — leaving another chart fraction for the SAME `z` whose denominator has
strictly smaller order.  Which uniformiser it is depends on the point: `t − α` where
`2β ≠ 0`, and `s` where `β = 0` and `g'(α) ≠ 0`.  Smoothness of the chart at the point is
exactly the disjunction of those two. -/
lemma exists_localDenom_step (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t s : D.F} {α β : K} {g h : K[X]}
    (hcurve : s ^ 2 = aeval t g)
    (hg : g = Polynomial.C (β ^ 2) + (Polynomial.X - Polynomial.C α) * h)
    (ht : D.VanishesAt v (t - algebraMap K D.F α)) (ht0 : t - algebraMap K D.F α ≠ 0)
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) (hs0 : s ≠ 0)
    (hsm : (2 : K) * β ≠ 0 ∨ (β = 0 ∧ h.eval α ≠ 0))
    {z : D.F} (hz0 : z ≠ 0) (hz : 0 ≤ D.ord v z)
    {A B e₁ e₂ : K[X]}
    (hden : aeval t e₁ + aeval t e₂ * s ≠ 0)
    (hdpos : 0 < D.ord v (aeval t e₁ + aeval t e₂ * s))
    (heq : z * (aeval t e₁ + aeval t e₂ * s) = aeval t A + aeval t B * s) :
    ∃ A' B' f₁ f₂ : K[X], (aeval t f₁ + aeval t f₂ * s ≠ 0) ∧
      D.ord v (aeval t f₁ + aeval t f₂ * s) < D.ord v (aeval t e₁ + aeval t e₂ * s) ∧
      z * (aeval t f₁ + aeval t f₂ * s) = aeval t A' + aeval t B' * s := by
  have hnum0 : aeval t A + aeval t B * s ≠ 0 := by rw [← heq]; exact mul_ne_zero hz0 hden
  have hnumpos : 0 < D.ord v (aeval t A + aeval t B * s) := by
    rw [← heq, D.ord_mul v _ _ hz0 hden]; omega
  have hδnum : A.eval α + B.eval α * β = 0 := chart_value_eq_zero D v ht hs hnumpos
  have hδden : e₁.eval α + e₂.eval α * β = 0 := chart_value_eq_zero D v ht hs hdpos
  have htm : t ∈ D.valRing v := mem_valRing_of_vanishesAt_sub D v ht
  have htpos : 0 < D.ord v (t - algebraMap K D.F α) := by
    rcases ht with hc | hc
    · exact absurd hc ht0
    · exact hc
  rcases hsm with h2β | ⟨hβ0, hhα⟩
  · -- the uniformiser is `t − α`; multiply by the conjugate `s + β`
    obtain ⟨A₁, hA⟩ := exists_sub_eval_factor A α
    obtain ⟨B₁, hB⟩ := exists_sub_eval_factor B α
    obtain ⟨E₁, he₁⟩ := exists_sub_eval_factor e₁ α
    obtain ⟨E₂, he₂⟩ := exists_sub_eval_factor e₂ α
    have hμ : algebraMap K D.F β + s ≠ 0 ∧ D.ord v (algebraMap K D.F β + s) = 0 := by
      refine ord_eq_zero_of_vanishesAt_sub D v (α := 2 * β) h2β ?_
      have hid : algebraMap K D.F β + s - algebraMap K D.F (2 * β)
          = s - algebraMap K D.F β := by
        rw [map_mul, show (algebraMap K D.F) (2 : K) = 2 from map_ofNat _ 2]; ring
      rw [hid]; exact hs
    have hN := chart_mul_conj D hcurve hg hA hB hδnum
    have hM := chart_mul_conj D hcurve hg he₁ he₂ hδden
    refine ⟨A₁ * Polynomial.C β + B₁ * g + Polynomial.C (B.eval α) * h,
      A₁ + B₁ * Polynomial.C β,
      E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h,
      E₁ + E₂ * Polynomial.C β, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, mul_zero] at hM
      exact (mul_ne_zero hden hμ.1) hM
    · have hMc0 : aeval t (E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h)
          + aeval t (E₁ + E₂ * Polynomial.C β) * s ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hM
        exact (mul_ne_zero hden hμ.1) hM
      have h3 : D.ord v (t - algebraMap K D.F α)
          + D.ord v (aeval t (E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h)
              + aeval t (E₁ + E₂ * Polynomial.C β) * s)
          = D.ord v (aeval t e₁ + aeval t e₂ * s) + D.ord v (algebraMap K D.F β + s) := by
        rw [← D.ord_mul v _ _ ht0 hMc0, ← D.ord_mul v _ _ hden hμ.1, hM]
      rw [hμ.2] at h3
      omega
    · have hMc0 : aeval t (E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h)
          + aeval t (E₁ + E₂ * Polynomial.C β) * s ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hM
        exact (mul_ne_zero hden hμ.1) hM
      refine mul_left_cancel₀ ht0 ?_
      calc (t - algebraMap K D.F α) * (z *
            (aeval t (E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h)
              + aeval t (E₁ + E₂ * Polynomial.C β) * s))
          = z * ((t - algebraMap K D.F α) *
            (aeval t (E₁ * Polynomial.C β + E₂ * g + Polynomial.C (e₂.eval α) * h)
              + aeval t (E₁ + E₂ * Polynomial.C β) * s)) := by ring
        _ = z * ((aeval t e₁ + aeval t e₂ * s) * (algebraMap K D.F β + s)) := by rw [← hM]
        _ = (z * (aeval t e₁ + aeval t e₂ * s)) * (algebraMap K D.F β + s) := by ring
        _ = (aeval t A + aeval t B * s) * (algebraMap K D.F β + s) := by rw [heq]
        _ = _ := hN
  · -- the uniformiser is `s`; multiply by `h(t)`, a unit because `h(α) = g'(α) ≠ 0`
    have hg' : g = (Polynomial.X - Polynomial.C α) * h := by
      rw [hg, hβ0]; simp
    have hAα : A.eval α = 0 := by rw [hβ0] at hδnum; simpa using hδnum
    have he₁α : e₁.eval α = 0 := by rw [hβ0] at hδden; simpa using hδden
    obtain ⟨A₁, hA⟩ : (Polynomial.X - Polynomial.C α) ∣ A := dvd_iff_isRoot.2 hAα
    obtain ⟨E₁, he₁⟩ : (Polynomial.X - Polynomial.C α) ∣ e₁ := dvd_iff_isRoot.2 he₁α
    have hμ : aeval t h ≠ 0 ∧ D.ord v (aeval t h) = 0 :=
      ord_eq_zero_of_vanishesAt_sub D v hhα (vanishesAt_aeval_sub_eval D v htm ht h)
    have hspos : 0 < D.ord v s := by
      rw [hβ0, map_zero, sub_zero] at hs
      rcases hs with hc | hc
      · exact absurd hc hs0
      · exact hc
    have hN := chart_mul_deriv D hcurve hg' (Q := B) hA
    have hM := chart_mul_deriv D hcurve hg' (Q := e₂) he₁
    refine ⟨B * h, A₁, e₂ * h, E₁, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, mul_zero] at hM
      exact (mul_ne_zero hden hμ.1) hM
    · have hMc0 : aeval t (e₂ * h) + aeval t E₁ * s ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hM
        exact (mul_ne_zero hden hμ.1) hM
      have h3 : D.ord v s + D.ord v (aeval t (e₂ * h) + aeval t E₁ * s)
          = D.ord v (aeval t e₁ + aeval t e₂ * s) + D.ord v (aeval t h) := by
        rw [← D.ord_mul v _ _ hs0 hMc0, ← D.ord_mul v _ _ hden hμ.1, hM]
      rw [hμ.2] at h3
      omega
    · refine mul_left_cancel₀ hs0 ?_
      calc s * (z * (aeval t (e₂ * h) + aeval t E₁ * s))
          = z * (s * (aeval t (e₂ * h) + aeval t E₁ * s)) := by ring
        _ = z * ((aeval t e₁ + aeval t e₂ * s) * aeval t h) := by rw [← hM]
        _ = (z * (aeval t e₁ + aeval t e₂ * s)) * aeval t h := by ring
        _ = (aeval t A + aeval t B * s) * aeval t h := by rw [heq]
        _ = _ := hN

/-- **`O_v` IS the local ring of the chart at the point** (PROVEN).

Every function regular at `v` is a chart fraction whose denominator does not vanish at the
point.  The proof is a descent on `ord_v` of the denominator: `exists_localDenom_step` cancels
one uniformiser whenever the denominator vanishes, and `ord_chart_eq_zero_iff` says order `0`
is exactly admissibility, so the descent stops precisely at the conclusion.

This is the statement that `O_v` DOMINATES the local ring of the chart and no more — the
classical route proves it by "a valuation ring dominating a DVR with the same fraction field
IS that DVR", which needs the local ring built as a Lean object and shown regular; the descent
needs neither, only the interface's valuation axioms and smoothness at the point. -/
theorem exists_localDenom_chart (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t s : D.F} {α β : K} {g h : K[X]}
    (hcurve : s ^ 2 = aeval t g)
    (hg : g = Polynomial.C (β ^ 2) + (Polynomial.X - Polynomial.C α) * h)
    (ht : D.VanishesAt v (t - algebraMap K D.F α)) (ht0 : t - algebraMap K D.F α ≠ 0)
    (hs : D.VanishesAt v (s - algebraMap K D.F β)) (hs0 : s ≠ 0)
    (hsm : (2 : K) * β ≠ 0 ∨ (β = 0 ∧ h.eval α ≠ 0))
    (hgen : ∀ z : D.F, ∃ A B e₁ e₂ : K[X], (aeval t e₁ + aeval t e₂ * s ≠ 0) ∧
      z * (aeval t e₁ + aeval t e₂ * s) = aeval t A + aeval t B * s)
    {z : D.F} (hz : 0 ≤ D.ord v z) :
    ∃ A B e₁ e₂ : K[X], e₁.eval α + e₂.eval α * β ≠ 0 ∧
      z * (aeval t e₁ + aeval t e₂ * s) = aeval t A + aeval t B * s := by
  have key : ∀ n : ℕ, ∀ A B e₁ e₂ : K[X], (aeval t e₁ + aeval t e₂ * s ≠ 0) →
      D.ord v (aeval t e₁ + aeval t e₂ * s) ≤ (n : ℤ) →
      z * (aeval t e₁ + aeval t e₂ * s) = aeval t A + aeval t B * s →
      ∃ A' B' f₁ f₂ : K[X], f₁.eval α + f₂.eval α * β ≠ 0 ∧
        z * (aeval t f₁ + aeval t f₂ * s) = aeval t A' + aeval t B' * s := by
    intro n
    induction n with
    | zero =>
      intro A B e₁ e₂ hden hle heq
      have h0 : D.ord v (aeval t e₁ + aeval t e₂ * s) = 0 :=
        le_antisymm (by exact_mod_cast hle) (chart_mem_valRing D v ht hs e₁ e₂)
      exact ⟨A, B, e₁, e₂, (ord_chart_eq_zero_iff D v ht hs hden).1 h0, heq⟩
    | succ m ih =>
      intro A B e₁ e₂ hden hle heq
      rcases eq_or_lt_of_le (chart_mem_valRing D v ht hs e₁ e₂) with h0 | hpos
      · exact ⟨A, B, e₁, e₂, (ord_chart_eq_zero_iff D v ht hs hden).1 h0.symm, heq⟩
      · rcases eq_or_ne z 0 with rfl | hz0
        · exact ⟨0, 0, 1, 0, by simp, by simp⟩
        · obtain ⟨A', B', f₁, f₂, hne', hlt', heq'⟩ :=
            exists_localDenom_step D v hcurve hg ht ht0 hs hs0 hsm hz0 hz hden hpos heq
          refine ih A' B' f₁ f₂ hne' ?_ heq'
          push_cast at hle ⊢
          omega
  obtain ⟨A, B, e₁, e₂, hne, heq⟩ := hgen z
  exact key (D.ord v (aeval t e₁ + aeval t e₂ * s)).toNat A B e₁ e₂ hne
    (by rw [Int.toNat_of_nonneg (chart_mem_valRing D v ht hs e₁ e₂)]) heq



end PlaceData

section Presentation

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-- `sextPoly` evaluated through a ring hom on the coefficients: the coefficients are
integers, so they are preserved. -/
lemma eval₂_sextPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {K A : Type*} [CommRing K] [CommRing A]
    (ψ : K →+* A) (x : A) :
    eval₂ ψ x (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) = sext c₀ c₁ c₂ c₃ c₄ c₅ x := by
  have h : ∀ n : ℤ, eval₂ ψ x (n : K[X]) = (n : A) := by
    intro n
    exact map_intCast (Polynomial.eval₂RingHom ψ x) n
  simp [sextPoly, sext, h]

/-- The defining polynomial `Y² − f(x)` of the function field over `K(x)`. -/
noncomputable def sextAdjoinPoly (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (K : Type) [Field K] :
    (RatFunc K)[X] :=
  X ^ 2 - C (algebraMap K[X] (RatFunc K) (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K))

lemma irreducible_sextAdjoinPoly (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) :
    Irreducible (sextAdjoinPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
  have hsqf : Squarefree (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := hsep.squarefree
  have hnu : ¬ IsUnit (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    intro h
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit h
    rw [natDegree_sextPoly] at h1
    exact absurd h1 (by norm_num)
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two (not_isSquare_sextPoly hsqf hnu)

/-- The hom `K(x) → A` sending `x` to a transcendental element `X'`. -/
noncomputable def ratFuncLift {A : Type} [Field A] (ψ : K →+* A) (X' : A)
    (htr : ∀ q : K[X], q ≠ 0 → eval₂ ψ X' q ≠ 0) : RatFunc K →+* A :=
  IsFractionRing.lift (g := Polynomial.eval₂RingHom ψ X') (by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hpne
    exact htr p hpne hp)

@[simp] lemma ratFuncLift_algebraMap {A : Type} [Field A] (ψ : K →+* A) (X' : A)
    (htr : ∀ q : K[X], q ≠ 0 → eval₂ ψ X' q ≠ 0) (p : K[X]) :
    ratFuncLift ψ X' htr (algebraMap K[X] (RatFunc K) p) = eval₂ ψ X' p :=
  IsFractionRing.lift_algebraMap _ _

/-- **A ring hom out of the function field is determined by the constants and by `xx`, `yy`**
(PROVEN from `gen` alone). -/
theorem ringHom_ext_of_gen {F A : Type} [Field F] [Algebra K F] [Field A] {xx yy : F}
    (gen : ∀ z : F, ∃ a b d : K[X], aeval xx d ≠ 0 ∧
      z * aeval xx d = aeval xx a + aeval xx b * yy)
    {φ φ' : F →+* A} (hc : ∀ a : K, φ (algebraMap K F a) = φ' (algebraMap K F a))
    (hx : φ xx = φ' xx) (hy : φ yy = φ' yy) : φ = φ' := by
  have hcomp : φ.comp (algebraMap K F) = φ'.comp (algebraMap K F) := RingHom.ext hc
  have hpoly : ∀ p : K[X], φ (aeval xx p) = φ' (aeval xx p) := by
    intro p
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.hom_eval₂, hx, hcomp]
  refine RingHom.ext fun z => ?_
  obtain ⟨a, b, d, hd, hz⟩ := gen z
  have hφd : φ (aeval xx d) ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr hd
  have h1 : φ z * φ (aeval xx d) = φ' z * φ (aeval xx d) := by
    rw [← map_mul, hz, map_add, map_mul, hpoly a, hpoly b, hy, hpoly d, ← map_mul, ← map_add,
      ← hz, map_mul]
  exact mul_right_cancel₀ hφd h1

/-- **The function field is presented by `xx`, `yy` and the relation `yy² = f(xx)`**: a ring
hom out of it exists for every choice of images of the constants, of `xx` and of `yy`
satisfying the same relation, with `xx`'s image transcendental (PROVEN).

The two lemmas together say `F = K(xx)[yy]/(yy² − f(xx))` in the only sense the rest of the
layer needs, and they are what makes the constant field extension constructible. -/
theorem exists_ringHom_of_gen {F : Type} [Field F] [Algebra K F] {xx yy : F}
    (eqn : yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ xx) (htrx : Transcendental K xx)
    (gen : ∀ z : F, ∃ a b d : K[X], aeval xx d ≠ 0 ∧
      z * aeval xx d = aeval xx a + aeval xx b * yy)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    {A : Type} [Field A] (ψ : K →+* A) (X' Y' : A)
    (heqn' : Y' ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ X')
    (htr' : ∀ q : K[X], q ≠ 0 → eval₂ ψ X' q ≠ 0) :
    ∃ φ : F →+* A, (∀ a : K, φ (algebraMap K F a) = ψ a) ∧ φ xx = X' ∧ φ yy = Y' := by
  classical
  have htrx' : ∀ q : K[X], q ≠ 0 → eval₂ (algebraMap K F) xx q ≠ 0 := fun q hq h =>
    htrx ⟨q, hq, by rwa [Polynomial.aeval_def]⟩
  haveI hfact : Fact (Irreducible (sextAdjoinPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) :=
    ⟨irreducible_sextAdjoinPoly hsep⟩
  set g : (RatFunc K)[X] := sextAdjoinPoly c₀ c₁ c₂ c₃ c₄ c₅ K with hgdef
  set ι : RatFunc K →+* F := ratFuncLift (algebraMap K F) xx htrx' with hιdef
  set ι' : RatFunc K →+* A := ratFuncLift ψ X' htr' with hι'def
  have hιpoly : ∀ p : K[X], ι (algebraMap K[X] (RatFunc K) p) = aeval xx p := by
    intro p; rw [hιdef, ratFuncLift_algebraMap, Polynomial.aeval_def]
  have hι'poly : ∀ p : K[X], ι' (algebraMap K[X] (RatFunc K) p) = eval₂ ψ X' p := by
    intro p; rw [hι'def, ratFuncLift_algebraMap]
  have hroot : eval₂ ι yy g = 0 := by
    rw [hgdef, sextAdjoinPoly, eval₂_sub, eval₂_X_pow, eval₂_C, hιpoly, aeval_sextPoly, eqn,
      sub_self]
  have hroot' : eval₂ ι' Y' g = 0 := by
    rw [hgdef, sextAdjoinPoly, eval₂_sub, eval₂_X_pow, eval₂_C, hι'poly, eval₂_sextPoly, heqn',
      sub_self]
  set Θ : AdjoinRoot g →+* F := AdjoinRoot.lift ι yy hroot with hΘdef
  set Θ' : AdjoinRoot g →+* A := AdjoinRoot.lift ι' Y' hroot' with hΘ'def
  -- the two maps on the generators
  have hΘof : ∀ r : RatFunc K, Θ (algebraMap (RatFunc K) (AdjoinRoot g) r) = ι r := by
    intro r; rw [AdjoinRoot.algebraMap_eq, hΘdef]; exact AdjoinRoot.lift_of _
  have hΘ'of : ∀ r : RatFunc K, Θ' (algebraMap (RatFunc K) (AdjoinRoot g) r) = ι' r := by
    intro r; rw [AdjoinRoot.algebraMap_eq, hΘ'def]; exact AdjoinRoot.lift_of _
  have hΘroot : Θ (AdjoinRoot.root g) = yy := by rw [hΘdef]; exact AdjoinRoot.lift_root _
  have hΘ'root : Θ' (AdjoinRoot.root g) = Y' := by rw [hΘ'def]; exact AdjoinRoot.lift_root _
  -- `Θ` is an isomorphism
  have hΘinj : Function.Injective Θ := Θ.injective
  have hΘsurj : Function.Surjective Θ := by
    intro z
    obtain ⟨a, b, d, hd, hz⟩ := gen z
    refine ⟨(algebraMap (RatFunc K) (AdjoinRoot g) (algebraMap K[X] (RatFunc K) a)
      + algebraMap (RatFunc K) (AdjoinRoot g) (algebraMap K[X] (RatFunc K) b)
        * AdjoinRoot.root g)
      / algebraMap (RatFunc K) (AdjoinRoot g) (algebraMap K[X] (RatFunc K) d), ?_⟩
    rw [map_div₀, map_add, map_mul, hΘof, hΘof, hΘof, hΘroot, hιpoly, hιpoly, hιpoly,
      ← hz, mul_div_assoc, div_self hd, mul_one]
  set e : AdjoinRoot g ≃+* F := RingEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩ with hedef
  have hecoe : ∀ u : AdjoinRoot g, e u = Θ u := fun u => rfl
  refine ⟨Θ'.comp (e.symm : F →+* AdjoinRoot g), ?_, ?_, ?_⟩
  · intro a
    have hkey : e.symm (algebraMap K F a)
        = algebraMap (RatFunc K) (AdjoinRoot g) (algebraMap K[X] (RatFunc K) (C a)) := by
      refine e.symm_apply_eq.mpr ?_
      rw [hecoe, hΘof, hιpoly, Polynomial.aeval_C]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, hkey, hΘ'of,
      hι'poly, eval₂_C]
  · have hkey : e.symm xx = algebraMap (RatFunc K) (AdjoinRoot g) RatFunc.X := by
      refine e.symm_apply_eq.mpr ?_
      rw [hecoe, hΘof, ← RatFunc.algebraMap_X, hιpoly, Polynomial.aeval_X]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, hkey, hΘ'of,
      ← RatFunc.algebraMap_X, hι'poly, eval₂_X]
  · have hkey : e.symm yy = AdjoinRoot.root g := e.symm_apply_eq.mpr (by rw [hecoe, hΘroot])
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom, hkey, hΘ'root]

/-! ### The places above `x = ∞` -/

/-- `PlaceData` contains a `FunctionFieldData` (PROVEN — the first block of its fields). -/
def PlaceData.toFunctionFieldData {K : Type} [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) :
    FunctionFieldData c₀ c₁ c₂ c₃ c₄ c₅ K where
  F := D.F
  xx := D.xx
  yy := D.yy
  eqn := D.eqn
  transcendental_xx := D.transcendental_xx
  gen := D.gen

/-- `PlaceData` contains a `PlaceSystem` (PROVEN — the second block of its fields). -/
def PlaceData.toPlaceSystem {K : Type} [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) :
    PlaceSystem K D.toFunctionFieldData.F where
  Places := D.Places
  ord := D.ord
  ord_zero := D.ord_zero
  ord_mul := D.ord_mul
  ord_add := D.ord_add
  ord_algebraMap := D.ord_algebraMap
  ord_surjective := D.ord_surjective
  ord_injective := D.ord_injective
  ord_complete := D.ord_complete
  ord_finite := D.ord_finite

/-- **LEAF: the only poles of the abscissa are the two points at infinity.**

`ord_v x < 0` forces `v ∈ {∞₊, ∞₋}`.  This is the fundamental inequality
`Σ_{v | ∞} e(v) f(v) ≤ [F : K(x)] = 2` ([Stichtenoth, *Algebraic Function Fields and Codes*,
III.1.11]) read at the infinite place of `K(x)`, and nothing more: the two rational points at
infinity are already exhibited by `PlaceData` (`ord_pt_infinite` gives `ord x = -1`, so
`e = 1`, and `finrank_residue_pt_eq_one` gives `f = 1`), they are distinct by `pt_injective`,
so they saturate the bound and there is no room for a third pole of `x`.

**Strictly weaker than the fundamental identity**
`degOf_poleDivisor_eq_finrank_of_transcendental`: it is one inequality, at one place, for the
one function `x` — no weak approximation and no dimension count.  Anyone proving that leaf
gets this one for free (`deg (div_∞ x) = [F : K(x)] = 2` with two degree-`1` poles already
present leaves no third), so it should be DELETED rather than proven separately if the
fundamental identity lands first.

**What would refute it**: a place with `ord_v x = -2` (`x = ∞` inert with `e = 2`) or one with
`f = 2`, in addition to `∞±`.  Neither can occur, because `∞±` alone already contribute
`1·1 + 1·1 = 2 = [F : K(x)]`; the *existence* of both is where the monic sextic and `2 ≠ 0`
are used, and both are `PlaceData` fields rather than things to prove. -/
theorem pt_infinite_of_ord_xx_neg {K : Type} [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (v : D.Places) (hv : D.ord v D.xx < 0) : ∃ s : Bool, v = D.pt (Sum.inr s) := sorry

/-- **PROVEN from `pt_infinite_of_ord_xx_neg`: a place with a simple pole of `x` lying on the
`s` branch at infinity IS `∞_s`.**  The branch separation is `isPlaceOfPt_injective`, whose
`2 ≠ 0` comes from `PlaceData.two_ne_zero`. -/
theorem pt_inr_eq_of_ord_xx {K : Type} [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (s : Bool) (v : D.Places) (h1 : D.ord v D.xx = -1)
    (h2 : -3 < D.ord v (D.yy - (if s then (1 : D.F) else -1) * D.xx ^ 3)) :
    v = D.pt (Sum.inr s) := by
  obtain ⟨s', rfl⟩ := pt_infinite_of_ord_xx_neg D v (by omega)
  have hbr : ∀ (t : Bool) (w : D.Places), D.ord w D.xx = -1 →
      -3 < D.ord w (D.yy - (if t then (1 : D.F) else -1) * D.xx ^ 3) →
      IsPlaceOfPt D.toFunctionFieldData D.toPlaceSystem (Sum.inr t) w :=
    fun _ _ ha hb => ⟨ha, hb⟩
  have hkey := isPlaceOfPt_injective D.toFunctionFieldData D.toPlaceSystem D.two_ne_zero
    (hbr s _ h1 h2)
    (hbr s' _ (D.ord_pt_infinite s').1 (D.ord_pt_infinite s').2)
  rw [Sum.inr.injEq] at hkey
  rw [hkey]

end Presentation

section Genus

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]

/-! ### Orders of polynomials at a pole, and the two consequences (PROVEN)

The one valuation-theoretic input the genus and the fundamental identity both need:
**at a place where `ord_v t < 0` the order of `p(t)` is `ord_v t · deg p`**
(`ord_aeval_of_ord_neg`).  It is an induction on the degree over `divX`, the inductive step
being the strict ultrametric equality `ord_add_of_lt` — the leading term `p.divX(t)·t` has
strictly smaller order than the constant term, which has order `0`.

Two things come out of it, and they are used in completely different places:

* `ord_eq_zero_of_isAlgebraic`: every element algebraic over `K` is a unit at every place
  (apply the above to `g` and to `g⁻¹`; a nonzero order of either sign produces a nonzero
  `aeval g p` from the minimal polynomial).  Hence `poleDivisor` and `K⟮g⟯`-codimension both
  vanish there, which is the **algebraic half of `degOf_poleDivisor_eq_finrank`** — the half
  the leaf's own docstring already asserted in prose;
* `ord_aeval_of_ord_eq_neg_one`, the `ord_v t = −1` case, is what pins a place in
  characteristic `2` and eliminates that characteristic altogether. -/

private theorem ord_aeval_aux (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t : D.F} {m : ℤ} (hm : m < 0) (ht : D.ord v t = m) :
    ∀ (n : ℕ) (p : K[X]), p ≠ 0 → p.natDegree ≤ n →
      aeval t p ≠ 0 ∧ D.ord v (aeval t p) = m * (p.natDegree : ℤ) := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, D.ord_zero] at ht
    omega
  intro n
  induction n with
  | zero =>
    intro p hp hdeg
    have hpc : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hdeg)
    have hc0 : p.coeff 0 ≠ 0 := by
      intro h
      exact hp (by rw [hpc, h, map_zero])
    have hval : aeval t p = algebraMap K D.F (p.coeff 0) := by
      conv_lhs => rw [hpc]
      simp
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr hc0
    · rw [hval, D.ord_algebraMap v _ hc0, Nat.le_zero.mp hdeg]
      simp
  | succ n ih =>
    intro p hp hdeg
    rcases eq_or_ne p.divX 0 with hq | hq
    · -- `p` is a constant
      have hpc : p = C (p.coeff 0) := Polynomial.divX_eq_zero_iff.mp hq
      have hc0 : p.coeff 0 ≠ 0 := by
        intro h
        exact hp (by rw [hpc, h, map_zero])
      have hdeg0 : p.natDegree = 0 := by
        conv_lhs => rw [hpc]
        exact Polynomial.natDegree_C _
      have hval : aeval t p = algebraMap K D.F (p.coeff 0) := by
        conv_lhs => rw [hpc]
        simp
      refine ⟨?_, ?_⟩
      · rw [hval]
        exact (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr hc0
      · rw [hval, D.ord_algebraMap v _ hc0, hdeg0]
        simp
    · have hdegpos : p.natDegree ≠ 0 := by
        intro h
        exact hq (Polynomial.divX_eq_zero_iff.mpr (Polynomial.eq_C_of_natDegree_eq_zero h))
      have hqdeg : p.divX.natDegree = p.natDegree - 1 :=
        Polynomial.natDegree_divX_eq_natDegree_tsub_one
      have hqle : p.divX.natDegree ≤ n := by omega
      obtain ⟨hqne, hqord⟩ := ih p.divX hq hqle
      have hmulne : aeval t p.divX * t ≠ 0 := mul_ne_zero hqne ht0
      have hmulord : D.ord v (aeval t p.divX * t) = m * (p.natDegree : ℤ) := by
        rw [D.ord_mul v _ _ hqne ht0, hqord, ht]
        have : (p.divX.natDegree : ℤ) + 1 = (p.natDegree : ℤ) := by omega
        nlinarith [this]
      have hneg : m * (p.natDegree : ℤ) < 0 := by
        have h1 : (1 : ℤ) ≤ (p.natDegree : ℤ) := by
          have : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hdegpos
          exact_mod_cast this
        nlinarith
      have hsplit : aeval t p = aeval t p.divX * t + algebraMap K D.F (p.coeff 0) := by
        conv_lhs => rw [← Polynomial.divX_mul_X_add p]
        simp
      rcases eq_or_ne (p.coeff 0) 0 with hc | hc
      · rw [hsplit, hc, map_zero, add_zero]
        exact ⟨hmulne, hmulord⟩
      · have hcne : algebraMap K D.F (p.coeff 0) ≠ 0 :=
          (map_ne_zero_iff _ (algebraMap K D.F).injective).mpr hc
        have hlt : D.ord v (aeval t p.divX * t) < D.ord v (algebraMap K D.F (p.coeff 0)) := by
          rw [hmulord, D.ord_algebraMap v _ hc]
          exact hneg
        have hne : aeval t p ≠ 0 := by
          rw [hsplit]
          intro h0
          have hcon := D.ord_add_of_lt v hmulne hcne hlt
          rw [h0, D.ord_zero, hmulord] at hcon
          omega
        refine ⟨hne, ?_⟩
        rw [hsplit, D.ord_add_of_lt v hmulne hcne hlt, hmulord]

/-- **With `ord_v t < 0`, the order of `p(t)` is `ord_v t` times `deg p`** (PROVEN). -/
theorem ord_aeval_of_ord_neg (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t : D.F} {m : ℤ} (hm : m < 0) (ht : D.ord v t = m) {p : K[X]} (hp : p ≠ 0) :
    aeval t p ≠ 0 ∧ D.ord v (aeval t p) = m * (p.natDegree : ℤ) :=
  ord_aeval_aux D v hm ht p.natDegree p hp le_rfl

/-- The `ord_v t = −1` case of `ord_aeval_of_ord_neg` (PROVEN). -/
theorem ord_aeval_of_ord_eq_neg_one (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {t : D.F} (ht : D.ord v t = -1) {p : K[X]} (hp : p ≠ 0) :
    aeval t p ≠ 0 ∧ D.ord v (aeval t p) = -(p.natDegree : ℤ) := by
  obtain ⟨h1, h2⟩ := ord_aeval_of_ord_neg D v (by norm_num) ht hp
  exact ⟨h1, by rw [h2]; ring⟩

/-- **Every element algebraic over `K` is a unit at every place** (PROVEN): a nonzero order of
either sign contradicts `ord_aeval_of_ord_neg` applied to the vanishing polynomial, at `g` or
at `g⁻¹`. -/
theorem ord_eq_zero_of_isAlgebraic (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (v : D.Places)
    {g : D.F} (hg : IsAlgebraic K g) : D.ord v g = 0 := by
  have main : ∀ z : D.F, IsAlgebraic K z → ¬ D.ord v z < 0 := by
    intro z hz hlt
    obtain ⟨p, hp0, hp⟩ := hz
    exact (ord_aeval_of_ord_neg D v hlt rfl hp0).1 hp
  rcases eq_or_ne g 0 with rfl | hg0
  · exact D.ord_zero v
  rcases lt_trichotomy (D.ord v g) 0 with h | h | h
  · exact absurd h (main g hg)
  · exact h
  · have hinv : IsAlgebraic K g⁻¹ := hg.inv
    have : D.ord v g⁻¹ < 0 := by rw [D.ord_inv v g hg0]; omega
    exact absurd this (main g⁻¹ hinv)

/-- `div_∞ g = 0` for `g` algebraic over `K` (PROVEN). -/
theorem poleDivisor_eq_zero_of_isAlgebraic (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    {g : D.F} (hg : IsAlgebraic K g) : D.poleDivisor g = 0 := by
  ext v
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · simp [PlaceData.divisor_apply D hg0 v, ord_eq_zero_of_isAlgebraic D v hg]

/-- `[F : K⟮g⟯] = 0` — `Module.finrank`'s junk value — for `g` algebraic over `K` (PROVEN):
otherwise `F` would be finite over `K⟮g⟯`, hence over `K`, contradicting
`transcendental_xx`. -/
theorem finrank_adjoin_eq_zero_of_isAlgebraic (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    {g : D.F} (hg : IsAlgebraic K g) :
    Module.finrank (IntermediateField.adjoin K {g}) D.F = 0 := by
  by_contra hne
  have hfin1 : Module.Finite (IntermediateField.adjoin K {g}) D.F :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hne)
  have hfin2 : FiniteDimensional K (IntermediateField.adjoin K {g}) :=
    IntermediateField.adjoin.finiteDimensional hg.isIntegral
  have : FiniteDimensional K D.F :=
    FiniteDimensional.trans K (IntermediateField.adjoin K {g}) D.F
  exact D.transcendental_xx ((Algebra.IsAlgebraic.of_finite K D.F).isAlgebraic D.xx)

/-! ### Characteristic `2` is vacuous (PROVEN)

The argument recorded on `not_isRationalGenerator` — `F/K(xx)` is purely inseparable, so
there is only one place above each place of `K(xx)`, while `ord_pt_infinite` supplies two
distinct ones over the infinite place — done by hand rather than through a theory of
inseparable extensions.  With `2 = 0` the cross term of `(a(xx) + b(xx)·yy)²` vanishes, so
every `z ∈ F` satisfies

    z² · d(xx)² = N(xx),   N = a² + b²·f,

by `gen` and `eqn`.  Taking `ord_v` of both sides at any place with `ord_v xx = −1` and using
`ord_aeval_of_ord_eq_neg_one` on `d` and `N` determines `2·ord_v z` from the degrees of `d`
and `N` alone — so any two such places have the same `ord`, and `ord_injective` collapses the
two points at infinity, contradicting `pt_injective`. -/

/-- In characteristic `2` a place is pinned by `ord_v xx = −1` (PROVEN). -/
theorem ord_eq_of_two_eq_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (h2 : (2 : K) = 0)
    {v w : D.Places} (hv : D.ord v D.xx = -1) (hw : D.ord w D.xx = -1) :
    D.ord v = D.ord w := by
  have h2F : (2 : D.F) = 0 := by
    rw [show (2 : D.F) = algebraMap K D.F 2 from (map_ofNat (algebraMap K D.F) 2).symm, h2,
      map_zero]
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [D.ord_zero, D.ord_zero]
  obtain ⟨a, b, d, hd, hab⟩ := D.gen z
  set N : K[X] := a ^ 2 + b ^ 2 * sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K with hN
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hd rfl
  have hkey : z ^ 2 * aeval D.xx d ^ 2 = aeval D.xx N := by
    have hsq : (z * aeval D.xx d) ^ 2
        = (aeval D.xx a) ^ 2 + (aeval D.xx b) ^ 2 * D.yy ^ 2 := by
      rw [hab]
      linear_combination (aeval D.xx a * (aeval D.xx b * D.yy)) * h2F
    rw [mul_pow] at hsq
    rw [hsq, D.eqn, hN, map_add, map_mul, map_pow, map_pow,
      aeval_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ D.xx]
  have hNne : aeval D.xx N ≠ 0 := by
    rw [← hkey]
    exact mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hd)
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, map_zero] at hNne
    exact hNne rfl
  have key : ∀ u : D.Places, D.ord u D.xx = -1 →
      2 * D.ord u z = -(N.natDegree : ℤ) + 2 * (d.natDegree : ℤ) := by
    intro u hu
    have hdo := (ord_aeval_of_ord_eq_neg_one D u hu hd0).2
    have hNo := (ord_aeval_of_ord_eq_neg_one D u hu hN0).2
    have hz2 : D.ord u (z ^ 2) = 2 * D.ord u z := by
      rw [D.ord_pow u z hz 2]; ring
    have hprod : D.ord u (z ^ 2 * aeval D.xx d ^ 2)
        = D.ord u (z ^ 2) + D.ord u (aeval D.xx d ^ 2) :=
      D.ord_mul u _ _ (pow_ne_zero _ hz) (pow_ne_zero _ hd)
    have hdd : D.ord u (aeval D.xx d ^ 2) = 2 * D.ord u (aeval D.xx d) := by
      rw [D.ord_pow u _ hd 2]; ring
    rw [hkey, hNo, hz2, hdd, hdo] at hprod
    omega
  have hkv := key v hv
  have hkw := key w hw
  omega

/-- **No `PlaceData` exists in characteristic `2`** (PROVEN) — the two points at infinity
collide.  This is what makes every `2 ≠ 0`-free statement in this layer safe: the
characteristic-`2` case of `not_isRationalGenerator`, `finrank_residue_pt_eq_one` and
`exists_localDenom_infinite` is not merely handled, it is empty. -/
theorem placeData_elim_of_two_eq_zero (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (h2 : (2 : K) = 0) : False := by
  have hv := (D.ord_pt_infinite true).1
  have hw := (D.ord_pt_infinite false).1
  have : D.pt (Sum.inr true) = D.pt (Sum.inr false) :=
    D.ord_injective (ord_eq_of_two_eq_zero D h2 hv hw)
  exact Bool.noConfusion (Sum.inr.injEq .. ▸ D.pt_injective this : (true : Bool) = false)

/-! ### Transport of a rational generator to `RatFunc K` (PROVEN)

A rational generator `t` generates (`adjoin_eq_top_of_isRationalGenerator`) and is
transcendental (`transcendental_of_isRationalGenerator`, since otherwise `F` would be finite
over `K`), so mathlib's `RatFunc.algEquivOfTranscendental` gives `F ≃ₐ[K] RatFunc K`.  The
two facts carried across are the curve equation and the transcendence of the abscissa, which
is exactly the hypothesis pair of `no_sextic_sq_of_ratFunc`. -/

/-- A rational generator generates (PROVEN). -/
theorem adjoin_eq_top_of_isRationalGenerator (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t : D.F}
    (h : D.IsRationalGenerator t) : IntermediateField.adjoin K {t} = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, hb, hab⟩ := h z
  have hz : z = aeval t a / aeval t b := by
    field_simp
    exact hab
  exact hz ▸ (IntermediateField.mem_adjoin_simple_iff K _).mpr ⟨a, b, rfl⟩

/-- A rational generator is transcendental over `K` (PROVEN). -/
theorem transcendental_of_isRationalGenerator (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t : D.F}
    (h : D.IsRationalGenerator t) : Transcendental K t := by
  rw [Transcendental]
  intro hal
  have hint : IsIntegral K t := hal.isIntegral
  have hfd : FiniteDimensional K (IntermediateField.adjoin K {t}) :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [adjoin_eq_top_of_isRationalGenerator D h] at hfd
  have : FiniteDimensional K D.F :=
    (IntermediateField.topEquiv (F := K) (E := D.F)).toLinearEquiv.finiteDimensional
  have halg : Algebra.IsAlgebraic K D.F := Algebra.IsAlgebraic.of_finite K D.F
  exact D.transcendental_xx (halg.isAlgebraic D.xx)

/-- `sext` commutes with any ring homomorphism (PROVEN). -/
theorem map_sext {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂] (f : A₁ →+* A₂) (x : A₁) :
    f (sext c₀ c₁ c₂ c₃ c₄ c₅ x) = sext c₀ c₁ c₂ c₃ c₄ c₅ (f x) := by
  simp [sext]

/-- A `PlaceData` with a rational generator is `K`-isomorphic to the rational function
field (PROVEN). -/
noncomputable def ratFuncEquivOfIsRationalGenerator (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    {t : D.F} (h : D.IsRationalGenerator t) : D.F ≃ₐ[K] RatFunc K :=
  (((RatFunc.algEquivOfTranscendental t (transcendental_of_isRationalGenerator D h)).trans
    ((IntermediateField.equivOfEq (adjoin_eq_top_of_isRationalGenerator D h)).trans
      IntermediateField.topEquiv))).symm

/-- The curve equation, transported to `RatFunc K` (PROVEN). -/
theorem ratFuncEquiv_yy_sq (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t : D.F}
    (h : D.IsRationalGenerator t) :
    ((ratFuncEquivOfIsRationalGenerator D h) D.yy) ^ 2
      = sext c₀ c₁ c₂ c₃ c₄ c₅ ((ratFuncEquivOfIsRationalGenerator D h) D.xx) := by
  set e := ratFuncEquivOfIsRationalGenerator D h
  rw [← map_pow, D.eqn]
  simpa using map_sext (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (c₃ := c₃) (c₄ := c₄) (c₅ := c₅)
    (e : D.F →+* RatFunc K) D.xx

/-- Transcendence of the abscissa, transported to `RatFunc K` (PROVEN). -/
theorem transcendental_ratFuncEquiv_xx (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {t : D.F}
    (h : D.IsRationalGenerator t) :
    Transcendental K ((ratFuncEquivOfIsRationalGenerator D h) D.xx) := by
  set e := ratFuncEquivOfIsRationalGenerator D h
  intro hal
  refine D.transcendental_xx ?_
  obtain ⟨p, hp0, hp⟩ := hal
  refine ⟨p, hp0, ?_⟩
  have hstep : e (aeval D.xx p) = 0 :=
    (Polynomial.aeval_algHom_apply (e : D.F →ₐ[K] RatFunc K) D.xx p).symm.trans hp
  simpa using hstep

end Genus

/-- **LEAF, PROVEN 2026-07-30: `O_v` at an affine rational point is the LOCAL RING of the
plane model there.**

The proof is `PlaceData.exists_localDenom_chart` in the chart `(t, s) = (x, y)` at `(α, β) = q`
— see the section docstring there for why the descent replaces the classical
"valuation ring dominating a DVR" argument.  `hsep` IS used, exactly as the audit below
predicted and only in the branch `β = 0`: there `2β = 0`, the conjugate `s + β` is not a unit,
and the uniformiser is `s` rather than `x − α`, which needs `f'(α) = h(α) ≠ 0`.  That is
supplied by `IsCoprime f f'` (which is what `Separable` unfolds to) together with
`not_isUnit_X_sub_C`: a common root of `f` and `f'` would make `X − α` a unit.  For `β ≠ 0` the
hypothesis is not needed, and `PlaceData.two_ne_zero` is what turns `β ≠ 0` into `2β ≠ 0`.

Every `z` without a pole at `v = pt (a, b)` is a quotient of two elements of the coordinate
ring `K[x, y] = K[x] ⊕ K[x]·y` whose denominator does not vanish at `(a, b)`.  This is the
one step of `finrank_residue_pt_eq_one` that is not formal: `O_v` visibly DOMINATES the
localisation `A_(a,b)` of the coordinate ring (the interface's `ord_pt_affine` says exactly
that `x − a` and `y − b` have positive order), and the content is that it EQUALS it.

The classical argument is that smoothness of `y² = f(x)` at `(a, b)` makes `A_(a,b)` a
regular local ring of dimension `1`, i.e. a DVR, and a valuation ring of `Frac A = F`
dominating a DVR with the same fraction field is that DVR.  **This is where `hsep` is used,
and it cannot be dropped**: without it the plane model can be singular at a rational point —
see the witness recorded on `finrank_residue_pt_eq_one`, where `[κ(v) : K] = 2`.

`hz` is what makes the statement non-vacuous; without it `z` may have a pole and no such
representation exists.  Note the denominator is `e₁(x) + e₂(x)·y`, NOT a polynomial in `x`
alone — see the warning on `PlaceData.exists_const_of_localDenom` for why the restricted
form is false. -/
theorem exists_localDenom_affine {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (q : AffPt c₀ c₁ c₂ c₃ c₄ c₅ K)
    {z : D.F} (hz : 0 ≤ D.ord (D.pt (Sum.inl q)) z) :
    ∃ a b e₁ e₂ : K[X],
      Polynomial.eval q.1.1 e₁ + Polynomial.eval q.1.1 e₂ * q.1.2 ≠ 0 ∧
      z * (aeval D.xx e₁ + aeval D.xx e₂ * D.yy)
        = aeval D.xx a + aeval D.xx b * D.yy := by
  set α : K := q.1.1 with hα
  set β : K := q.1.2 with hβ
  obtain ⟨hxo, hyo⟩ := D.ord_pt_affine q
  -- the curve equation in the chart
  have hcurve : D.yy ^ 2 = aeval D.xx (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    rw [aeval_sextPoly]; exact D.eqn
  -- the sextic factors through the point
  have hroot : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).eval α = β ^ 2 := by
    rw [eval_sextPoly, hα, hβ]; exact q.2.symm
  obtain ⟨h, hh⟩ : (Polynomial.X - Polynomial.C α)
      ∣ (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K - Polynomial.C (β ^ 2)) :=
    dvd_iff_isRoot.2 (by simp [IsRoot, hroot])
  have hg : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
      = Polynomial.C (β ^ 2) + (Polynomial.X - Polynomial.C α) * h := by
    rw [← hh]; ring
  -- the abscissa is not a constant, and the ordinate is not zero
  have hsext0 : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K ≠ 0 := fun h0 => by
    have hd := natDegree_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
    rw [h0] at hd; simp at hd
  have ht0 : D.xx - algebraMap K D.F α ≠ 0 := by
    intro h0
    refine D.transcendental_xx ⟨Polynomial.X - Polynomial.C α, ?_, ?_⟩
    · exact Polynomial.X_sub_C_ne_zero α
    · simpa using h0
  have hs0 : D.yy ≠ 0 := by
    intro h0
    refine D.transcendental_xx ⟨sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K, hsext0, ?_⟩
    rw [← hcurve, h0]
    ring
  -- smoothness at the point: `2β ≠ 0`, or `β = 0` and separability gives `h(α) = f'(α) ≠ 0`
  have hsm : (2 : K) * β ≠ 0 ∨ (β = 0 ∧ h.eval α ≠ 0) := by
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · refine Or.inr ⟨hβ0, fun hhα => ?_⟩
      have hgf : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K = (Polynomial.X - Polynomial.C α) * h := by
        rw [hg, hβ0]; simp
      have hdvd1 : (Polynomial.X - Polynomial.C α) ∣ h := dvd_iff_isRoot.2 hhα
      have hdvd2 : (Polynomial.X - Polynomial.C α)
          ∣ Polynomial.derivative (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
        rw [hgf, Polynomial.derivative_mul]
        exact dvd_add (Dvd.dvd.mul_left hdvd1 _) (Dvd.dvd.mul_right dvd_rfl _)
      have hdvd3 : (Polynomial.X - Polynomial.C α) ∣ sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K :=
        ⟨h, hgf⟩
      have hco : IsCoprime (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)
          (Polynomial.derivative (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K)) := hsep
      exact Polynomial.not_isUnit_X_sub_C α (hco.isUnit_of_dvd' hdvd3 hdvd2)
    · exact Or.inl (mul_ne_zero (D.two_ne_zero) hβ0)
  -- the chart generates, with a denominator in the abscissa alone
  have hgen : ∀ w : D.F, ∃ A B e₁ e₂ : K[X],
      (aeval D.xx e₁ + aeval D.xx e₂ * D.yy ≠ 0) ∧
      w * (aeval D.xx e₁ + aeval D.xx e₂ * D.yy) = aeval D.xx A + aeval D.xx B * D.yy := by
    intro w
    obtain ⟨A, B, d, hd, hw⟩ := D.gen w
    exact ⟨A, B, d, 0, by simpa using hd, by simpa using hw⟩
  exact PlaceData.exists_localDenom_chart D (D.pt (Sum.inl q)) hcurve hg (Or.inr hxo) ht0 (Or.inr hyo)
    hs0 hsm hgen hz

/-- **LEAF, PROVEN 2026-07-30: `O_v` at a point at infinity is the LOCAL RING of the chart at
infinity.**

`PlaceData.exists_localDenom_chart` again, in the chart `(t, s) = (1/x, y/x³)` at `(0, ±1)`,
with `g = revSextPoly` the reversed sextic.  **`hsep` is NOT used and is underscored**, as the
paragraph below predicted: the branch at infinity has `β = ±1`, so `2β ≠ 0` follows from
`PlaceData.two_ne_zero` and the `β = 0` branch — the only one that needs separability — is
never taken.

The one piece of real work beyond the affine instantiation is that the chart at infinity must
GENERATE: `gen` supplies `z = (a(x) + b(x)y)/d(x)`, and turning that into a fraction in
`(1/x, y/x³)` is `Polynomial.reflect` — `aeval (1/x) (reflect m p) = aeval x p · x^{-m}`, which
is mathlib's `eval₂_reflect_mul_pow` (`⅟x = x⁻¹`).  With `m` chosen `≥ deg d, deg a` and
`≥ deg b + 3`, the three reflections clear the denominator `x^m` simultaneously, the `+3` being
exactly the weight of `y`.

The same statement as `exists_localDenom_affine`, in the chart `u = 1/x`, `w = y/x³`, where
the curve becomes `w² = u⁶f(1/u) = 1 + c₅u + c₄u² + c₃u³ + c₂u⁴ + c₁u⁵ + c₀u⁶` and the two
points at infinity are the rational points `(u, w) = (0, ±1)`, the sign being the `Bool`.
`ord_pt_infinite` is exactly the statement that `u` and `w ∓ 1` have positive order at
`pt (Sum.inr s)`, so again `O_v` dominates the localisation and the content is equality.

Unlike the affine leaf this one is NOT expected to need `hsep`: the chart at infinity is
smooth at `(0, ±1)` for every monic sextic.  Writing `G(u, w) = w² − f*(u)`, the Jacobian
there is `(−c₅, ±2)`, whose second entry is nonzero whenever `2 ≠ 0` — and `2 = 0` is
vacuous here for the reason recorded on `not_isRationalGenerator`, that no `PlaceData`
exists in characteristic `2`.  That the two points are rational at all is the leading
coefficient `1` being a square, which is the whole reason `Pt` has a `Bool` summand.
The hypothesis is carried because every consumer has it and a weaker leaf is an easier one;
a proof that does not use it should underscore it. -/
theorem exists_localDenom_infinite {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (_hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (sgn : Bool)
    {z : D.F} (hz : 0 ≤ D.ord (D.pt (Sum.inr sgn)) z) :
    ∃ a b e₁ e₂ : K[X],
      Polynomial.eval 0 e₁ + Polynomial.eval 0 e₂ * (if sgn then (1 : K) else -1) ≠ 0 ∧
      z * (aeval D.xx⁻¹ e₁ + aeval D.xx⁻¹ e₂ * (D.yy * D.xx⁻¹ ^ 3))
        = aeval D.xx⁻¹ a + aeval D.xx⁻¹ b * (D.yy * D.xx⁻¹ ^ 3) := by
  set v := D.pt (Sum.inr sgn) with hv
  obtain ⟨hx1, hx2⟩ := D.ord_pt_infinite sgn
  rw [← hv] at hx1 hx2
  have hxne : D.xx ≠ 0 := by intro h0; rw [h0, D.ord_zero] at hx1; omega
  have hine : D.xx⁻¹ ≠ 0 := inv_ne_zero hxne
  have hiord : D.ord v D.xx⁻¹ = 1 := by rw [PlaceData.ord_inv D v _ hxne, hx1]; norm_num
  have hsext0 : sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K ≠ 0 := fun h0 => by
    have hd := natDegree_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
    rw [h0] at hd; simp at hd
  have hyne : D.yy ≠ 0 := by
    intro h0
    refine D.transcendental_xx ⟨sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K, hsext0, ?_⟩
    have := D.eqn
    rw [h0] at this
    rw [aeval_sextPoly, ← this]
    ring
  -- the curve equation in the chart at infinity
  have hcurve : (D.yy * D.xx⁻¹ ^ 3) ^ 2 = aeval D.xx⁻¹ (PlaceAtInfinity.revSextPoly c₀ c₁ c₂ c₃ c₄ c₅ K) := by
    rw [PlaceAtInfinity.aeval_revSextPoly, PlaceAtInfinity.revSext_inv_eq _ _ _ _ _ _ hxne,
      ← D.eqn]
    field_simp
  -- the chart sextic has constant term `1 = ε²`
  have hε2 : (if sgn then (1 : K) else -1) ^ 2 = 1 := by cases sgn <;> norm_num
  have hg : PlaceAtInfinity.revSextPoly c₀ c₁ c₂ c₃ c₄ c₅ K
      = Polynomial.C ((if sgn then (1 : K) else -1) ^ 2)
        + (Polynomial.X - Polynomial.C (0 : K))
          * ((c₅ : K[X]) + (c₄ : K[X]) * X + (c₃ : K[X]) * X ^ 2
              + (c₂ : K[X]) * X ^ 3 + (c₁ : K[X]) * X ^ 4 + (c₀ : K[X]) * X ^ 5) := by
    rw [hε2]
    simp only [PlaceAtInfinity.revSextPoly, map_one, map_zero, sub_zero]
    ring
  -- the two chart congruences
  have ht : D.VanishesAt v (D.xx⁻¹ - algebraMap K D.F (0 : K)) := by
    rw [map_zero, sub_zero]
    exact Or.inr (by rw [hiord]; norm_num)
  have ht0 : D.xx⁻¹ - algebraMap K D.F (0 : K) ≠ 0 := by
    rw [map_zero, sub_zero]; exact hine
  have hεF : (if sgn then (1 : D.F) else -1)
      = algebraMap K D.F (if sgn then (1 : K) else -1) := by cases sgn <;> simp
  have hchart : D.yy * D.xx⁻¹ ^ 3 - algebraMap K D.F (if sgn then (1 : K) else -1)
      = (D.yy - (if sgn then (1 : D.F) else -1) * D.xx ^ 3) * D.xx⁻¹ ^ 3 := by
    rw [← hεF]; field_simp
  have hs : D.VanishesAt v
      (D.yy * D.xx⁻¹ ^ 3 - algebraMap K D.F (if sgn then (1 : K) else -1)) := by
    rw [hchart]
    rcases eq_or_ne (D.yy - (if sgn then (1 : D.F) else -1) * D.xx ^ 3) 0 with hA | hA
    · exact Or.inl (by rw [hA, zero_mul])
    · refine Or.inr ?_
      rw [D.ord_mul v _ _ hA (pow_ne_zero _ hine), PlaceData.ord_pow D v _ hine 3, hiord]
      push_cast
      omega
  have hs0 : D.yy * D.xx⁻¹ ^ 3 ≠ 0 := mul_ne_zero hyne (pow_ne_zero _ hine)
  -- the chart at infinity is smooth at `(0, ±1)` because `2 ≠ 0`
  have hsm : (2 : K) * (if sgn then (1 : K) else -1) ≠ 0 := by
    have h2 := D.two_ne_zero
    cases sgn <;> simpa using h2
  -- the chart at infinity generates, by reflecting the polynomials of the affine chart
  have hkey : ∀ (p : K[X]) (m : ℕ), p.natDegree ≤ m →
      aeval D.xx⁻¹ (Polynomial.reflect m p) = aeval D.xx p * D.xx⁻¹ ^ m := by
    intro p m hp
    haveI : Invertible D.xx := invertibleOfNonzero hxne
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap K D.F) D.xx m p hp
    have hinv : (⅟D.xx : D.F) = D.xx⁻¹ := invOf_eq_inv D.xx
    rw [hinv, ← Polynomial.aeval_def, ← Polynomial.aeval_def] at h
    have hxu : D.xx * D.xx⁻¹ = 1 := mul_inv_cancel₀ hxne
    calc aeval D.xx⁻¹ (Polynomial.reflect m p)
        = aeval D.xx⁻¹ (Polynomial.reflect m p) * (D.xx * D.xx⁻¹) ^ m := by
          rw [hxu, one_pow, mul_one]
      _ = (aeval D.xx⁻¹ (Polynomial.reflect m p) * D.xx ^ m) * D.xx⁻¹ ^ m := by ring
      _ = aeval D.xx p * D.xx⁻¹ ^ m := by rw [h]
  have hgen : ∀ y : D.F, ∃ A B e₁ e₂ : K[X],
      (aeval D.xx⁻¹ e₁ + aeval D.xx⁻¹ e₂ * (D.yy * D.xx⁻¹ ^ 3) ≠ 0) ∧
      y * (aeval D.xx⁻¹ e₁ + aeval D.xx⁻¹ e₂ * (D.yy * D.xx⁻¹ ^ 3))
        = aeval D.xx⁻¹ A + aeval D.xx⁻¹ B * (D.yy * D.xx⁻¹ ^ 3) := by
    intro y
    obtain ⟨a, b, d, hd, hy⟩ := D.gen y
    set m : ℕ := max d.natDegree (max a.natDegree b.natDegree) with hm
    have hdm : d.natDegree ≤ m + 3 := by rw [hm]; omega
    have ham : a.natDegree ≤ m + 3 := by
      rw [hm]
      have : a.natDegree ≤ max d.natDegree (max a.natDegree b.natDegree) := by
        exact le_trans (le_max_left _ b.natDegree) (le_max_right _ _)
      omega
    have hbm : b.natDegree ≤ m := by
      rw [hm]
      exact le_trans (le_max_right a.natDegree _) (le_max_right _ _)
    refine ⟨Polynomial.reflect (m + 3) a, Polynomial.reflect m b,
      Polynomial.reflect (m + 3) d, 0, ?_, ?_⟩
    · rw [hkey d (m + 3) hdm]
      simp only [map_zero, zero_mul, add_zero]
      exact mul_ne_zero hd (pow_ne_zero _ hine)
    · rw [hkey d (m + 3) hdm, hkey a (m + 3) ham, hkey b m hbm]
      simp only [map_zero, zero_mul, add_zero]
      have hxu : D.xx * D.xx⁻¹ = 1 := mul_inv_cancel₀ hxne
      calc y * (aeval D.xx d * D.xx⁻¹ ^ (m + 3))
          = (y * aeval D.xx d) * D.xx⁻¹ ^ (m + 3) := by ring
        _ = (aeval D.xx a + aeval D.xx b * D.yy) * D.xx⁻¹ ^ (m + 3) := by rw [hy]
        _ = aeval D.xx a * D.xx⁻¹ ^ (m + 3)
              + aeval D.xx b * D.xx⁻¹ ^ m * (D.yy * D.xx⁻¹ ^ 3) := by
          rw [pow_add]; ring
  exact PlaceData.exists_localDenom_chart D v hcurve hg ht ht0 hs hs0 (Or.inl hsm) hgen hz

/-- **PROVEN: at an affine rational point every element of `O_v` is congruent to a constant.**

The local normal form of the leaf, fed to `PlaceData.exists_const_of_localDenom` with
`(t, s) = (x, y)` and `(α, β) = (a, b)`; `ord_pt_affine` supplies the two congruences. -/
theorem exists_const_sub_vanishesAt_affine {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (q : AffPt c₀ c₁ c₂ c₃ c₄ c₅ K)
    {z : D.F} (hz : 0 ≤ D.ord (D.pt (Sum.inl q)) z) :
    ∃ c : K, D.VanishesAt (D.pt (Sum.inl q)) (z - algebraMap K D.F c) := by
  obtain ⟨a, b, e₁, e₂, hd, heq⟩ := exists_localDenom_affine D hsep q hz
  obtain ⟨hxo, hyo⟩ := D.ord_pt_affine q
  exact PlaceData.exists_const_of_localDenom D _ (Or.inr hxo) (Or.inr hyo) hd heq

/-- **PROVEN: at a point at infinity every element of `O_v` is congruent to a constant.**

The chart congruences are computed here rather than read off an axiom: `ord u = 1` from
`ord x = −1`, and `w − ε = (y − ε·x³)·u³` has order `ord (y − ε·x³) + 3 > 0` by
`ord_pt_infinite`.  The degenerate branch `y = ε·x³` is the `z = 0` disjunct of
`VanishesAt`, not an omission. -/
theorem exists_const_sub_vanishesAt_infinite {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (s : Bool)
    {z : D.F} (hz : 0 ≤ D.ord (D.pt (Sum.inr s)) z) :
    ∃ c : K, D.VanishesAt (D.pt (Sum.inr s)) (z - algebraMap K D.F c) := by
  obtain ⟨a, b, e₁, e₂, hd, heq⟩ := exists_localDenom_infinite D hsep s hz
  obtain ⟨hx1, hx2⟩ := D.ord_pt_infinite s
  set v := D.pt (Sum.inr s) with hv
  have hxne : D.xx ≠ 0 := by
    intro h; rw [h, D.ord_zero] at hx1; omega
  have hine : D.xx⁻¹ ≠ 0 := inv_ne_zero hxne
  have hiord : D.ord v D.xx⁻¹ = 1 := by rw [PlaceData.ord_inv D v _ hxne, hx1]; norm_num
  have ht : D.VanishesAt v (D.xx⁻¹ - algebraMap K D.F 0) := by
    rw [map_zero, sub_zero]
    exact Or.inr (by rw [hiord]; norm_num)
  have hεF : (if s then (1 : D.F) else -1) = algebraMap K D.F (if s then (1 : K) else -1) := by
    cases s <;> simp
  have hchart : D.yy * D.xx⁻¹ ^ 3 - algebraMap K D.F (if s then (1 : K) else -1)
      = (D.yy - (if s then (1 : D.F) else -1) * D.xx ^ 3) * D.xx⁻¹ ^ 3 := by
    rw [← hεF]
    field_simp
  have hsv : D.VanishesAt v
      (D.yy * D.xx⁻¹ ^ 3 - algebraMap K D.F (if s then (1 : K) else -1)) := by
    rw [hchart]
    rcases eq_or_ne (D.yy - (if s then (1 : D.F) else -1) * D.xx ^ 3) 0 with hA | hA
    · exact Or.inl (by rw [hA, zero_mul])
    · refine Or.inr ?_
      rw [D.ord_mul v _ _ hA (pow_ne_zero _ hine), PlaceData.ord_pow D v _ hine 3, hiord]
      push_cast
      omega
  exact PlaceData.exists_const_of_localDenom D v ht hsv hd heq

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
[Stichtenoth, *Algebraic Function Fields and Codes*, §I.1].

## DECOMPOSED 2026-07-28 — now PROVEN over the two chart leaves below

The residue computation is now Lean rather than prose (`PlaceData.exists_const_of_localDenom`
and the block above it), and what is left is exactly the sentence the docstring called "the
step that a general `z ∈ O_v` reduces too": `O_v` is the LOCALIZATION of the chart's
coordinate ring at the point, not merely a valuation ring dominating it.  That is
`exists_localDenom_affine` in the chart `(x, y)` and `exists_localDenom_infinite` in the
chart `(1/x, y/x³)`.

**`hsep` IS load-bearing here — the module note above `mulRightHom` was wrong to expect
otherwise, and this leaf is FALSE without it.**  Witness: `K = ℚ`,
`f = x⁶ + 2x² = x²(x⁴ + 2)`, i.e. `c₂ = 2` and every other `cᵢ = 0`, which is not separable
(double root at `0`).  Then `y = x·y'` with `y'² = x⁴ + 2`, so `F` is the function field of
the genus-`1` curve `y'² = x⁴ + 2`; above `x = 0` the fibre is `y'² = 2`, and `2` is not a
square in `ℚ`, so there is exactly ONE place `v₀` there and its residue field is `ℚ(√2)`.
That place satisfies `ord_pt_affine` for the rational point `(0, 0)` of `y² = f(x)`
(`ord (x) = 1 > 0` and `ord (y) = ord (x·y') = 1 > 0`), the rest of a `PlaceData` is
available (the two points at infinity are unramified since `y'/x²  → ±1`, and `pt` is
injective because distinct rational points sit over distinct `x` or over distinct signs of
`y'`), and `[κ(v₀) : ℚ] = 2 ≠ 1`.  So the hypothesis cannot be dropped, and a proof of this
leaf that does NOT use it is wrong.  Concretely `hsep` enters as smoothness of the plane
model at `(α, β)`: a singular point would be `2β = 0` together with `f'(α) = 0`, and with
`β² = f(α)` that is a multiple root of `f`. -/
theorem finrank_residue_pt_eq_one {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ K) :
    Module.finrank K (D.residue (D.pt P)) = 1 := by
  rcases P with q | s
  · exact PlaceData.finrank_residue_eq_one_of_forall_exists_const D _
      fun z hz => exists_const_sub_vanishesAt_affine D hsep q hz
  · exact PlaceData.finrank_residue_eq_one_of_forall_exists_const D _
      fun z hz => exists_const_sub_vanishesAt_infinite D hsep s hz

/-! ### `F` is FINITE over `K⟮g⟯` for every transcendental `g` (PROVEN)

The first of the three pieces of [Stichtenoth, Thm. 1.4.11], and the one that is not an
inequality: without it the right-hand side of the fundamental identity is `Module.finrank`'s
junk value `0` and the identity is FALSE (`div_∞ g ≠ 0` for `g` transcendental), so this is
not bookkeeping — it is the statement that both sides are talking about the same thing.

The proof is the classical two-variable argument, and the only input beyond `gen` is that
`g` is transcendental:

* `gen` applied to `g` gives `a, b, d ∈ K[T]` with `d(x) ≠ 0` and `g·d(x) = a(x) + b(x)·y`.
  Squaring and using `eqn` kills `y`:
  `(g·d(x) − a(x))² = b(x)²·f(x)`, i.e. `x` is a root of
  `p = g²·d² − 2g·(a·d) + (a² − b²·f) ∈ K⟮g⟯[T]`;
* `p ≠ 0` **because `g` is transcendental**: its coefficient at `N = deg (d²)` is
  `g²·(d²)_N − 2g·(a·d)_N + (a² − b²f)_N` with `(d²)_N = lc(d)² ≠ 0`, so a vanishing
  coefficient exhibits `g` as a root of an honest quadratic over `K`.  This is the only step
  that uses `hg`, and it is where the statement would fail for `g ∈ K`: there `p` really is
  `0` (take `a = g·d`, `b = 0`) and `x` is not pinned at all;
* so `x` is integral over `K⟮g⟯`, hence so is `f(x) = y²` (it lies in `K⟮g⟯[x]`) and hence so
  is `y` (`IsIntegral.of_pow`).  `gen` says `K⟮g⟯⟮x, y⟯ = ⊤`, and adjoining two integral
  elements to a field is finite.

Note what is NOT used: no place, no valuation, no separability.  This is a statement about
the field `F` alone. -/

/-- Coefficientwise expansion of the quadratic combination `C (u²)·P̄ − C (2u)·Q̄ + R̄`
(PROVEN) — the shape the two-variable relation below takes over `K⟮g⟯`. -/
theorem coeff_quadCombination {K E : Type*} [CommRing K] [CommRing E] (φ : K →+* E) (u : E)
    (P Q R : K[X]) (N : ℕ) :
    (C (u ^ 2) * P.map φ - C (u * 2) * Q.map φ + R.map φ).coeff N
      = u ^ 2 * φ (P.coeff N) - u * 2 * φ (Q.coeff N) + φ (R.coeff N) := by
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_map]

/-- **The abscissa is integral over `K⟮g⟯` for every transcendental `g`** (PROVEN); see the
section note above for the argument. -/
theorem isIntegral_xx_adjoin_of_transcendental {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {g : D.F} (hg : Transcendental K g) :
    IsIntegral (IntermediateField.adjoin K {g}) D.xx := by
  set E := IntermediateField.adjoin K {g} with hEdef
  obtain ⟨a, b, d, hd, heq⟩ := D.gen g
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  set gE : E := ⟨g, IntermediateField.mem_adjoin_simple_self K g⟩ with hgE
  have hgEF : algebraMap E D.F gE = g := rfl
  set fp : K[X] := sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K with hfp
  set P : K[X] := d ^ 2 with hP
  set Q : K[X] := a * d with hQ
  set R : K[X] := a ^ 2 - b ^ 2 * fp with hR
  set p : E[X] := C (gE ^ 2) * P.map (algebraMap K E) - C (gE * 2) * Q.map (algebraMap K E)
    + R.map (algebraMap K E) with hp
  -- `xx` is a root of `p`
  have hroot : (aeval D.xx) p = 0 := by
    have hsx : (aeval D.xx) fp = sext c₀ c₁ c₂ c₃ c₄ c₅ D.xx :=
      aeval_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ D.xx
    have hyy : D.yy ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ D.xx := D.eqn
    rw [hp, hP, hQ, hR]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_C, hgEF, map_ofNat,
      aeval_map_algebraMap, hsx]
    linear_combination
      (g * (aeval D.xx) d - (aeval D.xx) a + (aeval D.xx) b * D.yy) * heq +
        ((aeval D.xx) b) ^ 2 * hyy
  -- `p ≠ 0`, because `g` is transcendental
  have hp0 : p ≠ 0 := by
    intro hzero
    set N : ℕ := P.natDegree with hN
    have hlc : P.coeff N ≠ 0 := by
      rw [hN, ← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr (by rw [hP]; exact pow_ne_zero 2 hd0)
    have hcoeff : gE ^ 2 * (algebraMap K E) (P.coeff N) - gE * 2 * (algebraMap K E) (Q.coeff N)
        + (algebraMap K E) (R.coeff N) = 0 := by
      rw [← coeff_quadCombination (algebraMap K E) gE P Q R N, ← hp, hzero, coeff_zero]
    set q : K[X] :=
      C (P.coeff N) * X ^ 2 - C (2 * Q.coeff N) * X + C (R.coeff N) with hq
    refine hg ⟨q, ?_, ?_⟩
    · intro hq0
      apply hlc
      have hc := congrArg (fun r : K[X] => r.coeff 2) hq0
      simpa [hq] using hc
    · have hF := congrArg (algebraMap E D.F) hcoeff
      have hAlg : ∀ k : K, algebraMap E D.F (algebraMap K E k) = algebraMap K D.F k := fun k =>
        (IsScalarTower.algebraMap_apply K E D.F k).symm
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, hgEF, hAlg] at hF
      simp only [hq, map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X, map_ofNat]
      linear_combination hF
  exact IsAlgebraic.isIntegral ⟨p, hp0, hroot⟩

/-- **`[F : K⟮g⟯] < ∞` for every transcendental `g`** (PROVEN): `x` is integral over `K⟮g⟯`,
`y² = f(x)` makes `y` integral too, and `gen` says the two of them generate `F`. -/
theorem finiteDimensional_adjoin_of_transcendental {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) {g : D.F} (hg : Transcendental K g) :
    FiniteDimensional (IntermediateField.adjoin K {g}) D.F := by
  set E := IntermediateField.adjoin K {g} with hEdef
  have hx : IsIntegral E D.xx := isIntegral_xx_adjoin_of_transcendental D hg
  have hsext : IsIntegral E (sext c₀ c₁ c₂ c₃ c₄ c₅ D.xx) := by
    have hmem : sext c₀ c₁ c₂ c₃ c₄ c₅ D.xx ∈ Algebra.adjoin E ({D.xx} : Set D.F) := by
      have h := Polynomial.aeval_mem_adjoin_singleton (↥E) D.xx
        (p := sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (↥E))
      rwa [aeval_sextPoly] at h
    exact adjoin_le_integralClosure hx hmem
  have hy : IsIntegral E D.yy :=
    IsIntegral.of_pow (n := 2) (by norm_num) (by rw [D.eqn]; exact hsext)
  haveI : Finite ({D.xx, D.yy} : Set D.F) :=
    ((Set.finite_singleton D.yy).insert D.xx).to_subtype
  have htop : IntermediateField.adjoin E ({D.xx, D.yy} : Set D.F) = ⊤ := by
    set A := IntermediateField.adjoin E ({D.xx, D.yy} : Set D.F) with hA
    have hxA : D.xx ∈ A := IntermediateField.subset_adjoin _ _ (by simp)
    have hyA : D.yy ∈ A := IntermediateField.subset_adjoin _ _ (by simp)
    have hpoly : ∀ r : K[X], (aeval D.xx) r ∈ A := by
      intro r
      have hle : Algebra.adjoin (↥E) ({D.xx} : Set D.F) ≤ A.toSubalgebra :=
        Algebra.adjoin_le (by simpa using hxA)
      have h := hle (Polynomial.aeval_mem_adjoin_singleton (↥E) D.xx
        (p := r.map (algebraMap K (↥E))))
      rwa [aeval_map_algebraMap] at h
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨a, b, d, hd, heq⟩ := D.gen z
    have hz : z = ((aeval D.xx) a + (aeval D.xx) b * D.yy) / (aeval D.xx) d := by
      field_simp
      linear_combination heq
    rw [hz]
    exact div_mem (add_mem (hpoly a) (mul_mem (hpoly b) hyA)) (hpoly d)
  have hfd : FiniteDimensional E (IntermediateField.adjoin E ({D.xx, D.yy} : Set D.F)) :=
    IntermediateField.finiteDimensional_adjoin (fun w hw => by
      rcases hw with h | h
      · exact h ▸ hx
      · simp only [Set.mem_singleton_iff] at h
        exact h ▸ hy)
  rw [htop] at hfd
  exact (IntermediateField.topEquiv (F := ↥E) (E := D.F)).toLinearEquiv.finiteDimensional

/-- **LEAF (fundamental identity, first inequality): `deg (div_∞ g) ≤ [F : K⟮g⟯]`.**

[Stichtenoth, *Algebraic Function Fields and Codes*, Thm. 1.4.11, part (a)]:
`Σ_{v} e_v f_v ≤ n` over the poles `v` of `g`, where `e_v = −ord_v g`, `f_v = [κ(v) : K]`
and `n = [F : K⟮g⟯]` — which is FINITE by
`finiteDimensional_adjoin_of_transcendental` above, so `n` here is a real number and not
`Module.finrank`'s junk `0`.

The classical proof exhibits `Σ e_v f_v` elements of `F` linearly independent over `K⟮g⟯`:
for each pole `v` a uniformiser `t_v` and elements `s_{v,1}, …, s_{v,f_v} ∈ O_v` whose
residues are a `K`-basis of `κ(v)`, and then the family `s_{v,i}·t_v^k`, `0 ≤ k < e_v`.

**Where the cost actually is, measured against the axioms rather than assumed** (2026-07-30).
The SINGLE-place case `e_v·f_v ≤ n` needs NO approximation theorem and is provable directly
from this file's interface, as follows — recorded because it is the half a prover should do
first, and because it already yields `f_v < ∞`, which the statement above needs to be
non-junk:

* a relation `Σ_{i,k} λ_{ik}·s_{v,i}·t_v^k = 0` with `λ_{ik} ∈ K⟮g⟯` may be cleared of
  denominators to `λ_{ik} ∈ K[g]`;
* `ord_v (p(g)) = −e_v·deg p` for `p ∈ K[X]` is exactly `ord_aeval_of_ord_neg`, ALREADY
  PROVEN in the `Genus` section above.  So every `ord_v λ_{ik}` is a multiple of `e_v`;
* hence `z_k := Σ_i λ_{ik} s_{v,i}` has `ord_v z_k = −e_v·d_k` (`d_k` the largest degree
  occurring), because `g^{−d_k}·z_k` lies in `O_v` with residue `Σ_i c_i·s̄_{v,i} ≠ 0` by the
  `K`-independence of the residues;
* so the `ord_v (z_k·t_v^k) = −e_v d_k + k` are pairwise DISTINCT mod `e_v` for
  `0 ≤ k < e_v`, and the strict ultrametric equality forbids the sum from vanishing.

What that argument cannot do is run at several places at once: it needs `t_v` and `s_{v,i}`
to be units at the OTHER poles, which is the approximation theorem
([Stichtenoth, Thm. 1.3.1]) and is the genuinely missing input.  A prover should expect to
have to prove approximation from `ord_injective` + `ord_complete` first, or to find a
route that sums the single-place bounds without it.

**What would refute it**: nothing about the sextic — this is general function-field theory,
so `hsep` is deliberately absent.  A counterexample would have to be a `PlaceData` with a
pole `v` of `g` where `e_v·f_v` alone exceeds `[F : K⟮g⟯]`, and the single-place argument
above rules that out. -/
theorem degOf_poleDivisor_le_finrank_of_transcendental {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type}
    [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) (hg : Transcendental K g) :
    degHom D D.degOf (D.poleDivisor g)
      ≤ (Module.finrank (IntermediateField.adjoin K {g}) D.F : ℤ) := sorry

/-- **LEAF (fundamental identity, second inequality): `[F : K⟮g⟯] ≤ deg (div_∞ g)`.**

[Stichtenoth, *Algebraic Function Fields and Codes*, Thm. 1.4.11, part (b)], the
dimension-count half.  With `A = div_∞ g` and `n = [F : K⟮g⟯]` (finite, by
`finiteDimensional_adjoin_of_transcendental`), the classical proof is:

1. take a `K⟮g⟯`-basis `u_1, …, u_n` of `F` and a divisor `B ≥ 0` with `div u_j + B ≥ 0` for
   every `j` — possible because each `u_j` has finitely many poles (`ord_finite`);
2. for every `m ≥ 0` the `n(m+1)` elements `g^k·u_j`, `0 ≤ k ≤ m`, lie in the Riemann space
   `L(mA + B)` and are `K`-linearly independent: a vanishing `K`-combination groups as
   `Σ_j (Σ_k c_{kj} g^k)·u_j = 0`, so each `Σ_k c_{kj} g^k = 0` in `K⟮g⟯`, so each
   `c_{kj} = 0` **because `g` is transcendental** — this is where `hg` is used;
3. `ℓ(C) ≤ deg C + 1` for `C ≥ 0`, and `ℓ(C + v) ≤ ℓ(C) + deg v`, both from the one
   structural fact `dim_K L(C + v)/L(C) ≤ [κ(v) : K]` (multiply by a power of a uniformiser
   and read the residue);
4. combining, `m·deg A + deg B + 1 ≥ n(m+1)` for every `m`, and letting `m → ∞` gives
   `deg A ≥ n`.

So the missing infrastructure is the Riemann space `L(C) = {z | div z + C ≥ 0}` as a
`K`-submodule of `F` together with step 3; approximation is NOT needed for this half, which
is why it is stated separately from the first inequality rather than bundled with it.

**Not vacuous, and the direction that carries the residue-degree finiteness.**  `degOf` is
`Module.finrank K (D.residue v)`, which is the junk `0` at a place of infinite residue
degree; an underestimate makes the FIRST inequality easier and this one harder, so it is
this leaf that has to know residue degrees are finite.  Step 3 supplies exactly that.

**What would refute it**: a `PlaceData` and a transcendental `g` whose pole divisor has
degree strictly smaller than `[F : K⟮g⟯]`.  Since `deg` is computed with the junk-tolerant
`degOf`, the cheapest place to look for such a thing is a place with an infinite-dimensional
residue field — which is why step 3 above is not optional bookkeeping. -/
theorem finrank_le_degOf_poleDivisor_of_transcendental {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type}
    [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) (hg : Transcendental K g) :
    (Module.finrank (IntermediateField.adjoin K {g}) D.F : ℤ)
      ≤ degHom D D.degOf (D.poleDivisor g) := sorry

/-- **The fundamental identity of function-field theory,**
`[F : K(g)] = deg (div_∞ g)`
([Stichtenoth, *Algebraic Function Fields and Codes*, Thm. 1.4.11] proper, proven there from
the weak approximation theorem plus a dimension count).

This is the single deep node of the whole Picard layer.  Everything else in obligation 2a is
bookkeeping over
it, and both of the leaves this file used to carry there — the degree formula and the
single-pole criterion — are now PROVEN from it.

No side condition on `g`, and none is needed: for `g` algebraic over `K` (in particular for
`g ∈ K` and for `g = 0`) the pole divisor is `0`, while `K⟮g⟯` is a FINITE extension of `K`
inside `F`, so `[F : K⟮g⟯]` is infinite and `Module.finrank`'s junk value is `0` as well.
The interesting case is `g` transcendental, and there the classical proof is weak
approximation plus a dimension count.

Applying it to `g` and to `g⁻¹` is what gives `deg (div_0 g) = deg (div_∞ g)`, since
`div_∞ (g⁻¹) = div_0 g` and `K(g⁻¹) = K(g)`; applying it at the single value
`deg (div_∞ g) = 1` is what gives `F = K(g)`.

## DECOMPOSED 2026-07-30 — the algebraic case is now Lean, and only this leaf remains

The paragraph above ("for `g` algebraic over `K` the pole divisor is `0` while `[F : K⟮g⟯]`
is `Module.finrank`'s junk value `0`") was prose; it is now
`poleDivisor_eq_zero_of_isAlgebraic` and `finrank_adjoin_eq_zero_of_isAlgebraic`,
both proven from `ord_aeval_of_ord_neg` in the `Genus` section above.  So the side condition
`Transcendental K g` here is free at every call site, and the transcendental case is the
whole of Stichtenoth I.4.11: weak approximation plus a dimension count.

## DECOMPOSED AGAIN 2026-07-30 — the three pieces of Stichtenoth I.4.11, one of them PROVEN

The transcendental case is not one argument but three, and they were bundled here only
because nobody had separated them.  They now sit immediately above, in the section
"`F` is FINITE over `K⟮g⟯`":

* `finiteDimensional_adjoin_of_transcendental` — **PROVEN**.  That `[F : K⟮g⟯]` is finite at
  all, so that the right-hand side of this identity is a number rather than
  `Module.finrank`'s junk `0`.  This is not part of either inequality; it is what makes both
  of them mean anything, and it is pure field theory (no place, no valuation, no `hsep`).
* `degOf_poleDivisor_le_finrank_of_transcendental` — Stichtenoth I.4.11(a).  The half that
  needs the APPROXIMATION theorem; its docstring records, with the proof, that the
  single-place case `e_v·f_v ≤ n` needs no approximation at all and is available from
  `ord_aeval_of_ord_neg` in the `Genus` section, so approximation is the only genuinely
  missing input.
* `finrank_le_degOf_poleDivisor_of_transcendental` — Stichtenoth I.4.11(b).  The half that
  needs the RIEMANN SPACES `L(C)` and the bound `ℓ(C) ≤ deg C + 1`; it needs no
  approximation.  It is also the half that carries finiteness of the residue degrees, since
  the junk value of `degOf` biases the inequality against it.

The two halves are therefore INDEPENDENT pieces of infrastructure — approximation on one
side, Riemann spaces on the other — which is the reason for cutting here rather than leaving
one leaf that needs both. -/
theorem degOf_poleDivisor_eq_finrank_of_transcendental {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type}
    [Field K] (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) (hg : Transcendental K g) :
    degHom D D.degOf (D.poleDivisor g)
      = (Module.finrank (IntermediateField.adjoin K {g}) D.F : ℤ) :=
  le_antisymm (degOf_poleDivisor_le_finrank_of_transcendental D g hg)
    (finrank_le_degOf_poleDivisor_of_transcendental D g hg)

/-- **The fundamental identity with no side condition, PROVEN 2026-07-30** from
`degOf_poleDivisor_eq_finrank_of_transcendental` together with the algebraic case; see the
docstring there. -/
theorem degOf_poleDivisor_eq_finrank {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K) (g : D.F) :
    degHom D D.degOf (D.poleDivisor g)
      = (Module.finrank (IntermediateField.adjoin K {g}) D.F : ℤ) := by
  by_cases hg : IsAlgebraic K g
  · rw [poleDivisor_eq_zero_of_isAlgebraic D hg, map_zero,
      finrank_adjoin_eq_zero_of_isAlgebraic D hg, Nat.cast_zero]
  · exact degOf_poleDivisor_eq_finrank_of_transcendental D g hg

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
uses it, and a weaker leaf is an easier leaf.)

## DECOMPOSED 2026-07-28 — now PROVEN from `degOf_poleDivisor_eq_finrank`

Steps 1, 3 and 4 of the route above are the bookkeeping block at the end of the `PlaceData`
namespace and are now Lean; step 2 is the leaf.  `hsep` is NOT used — as predicted, the
degree formula is a fact about every function field of one variable — so it is underscored,
which is the mechanical record that the separation held here. -/
theorem degOf_divisor_eq_zero {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (_hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (g : D.F) :
    degHom D D.degOf (D.divisor g) = 0 := by
  rw [PlaceData.divisor_eq_zeroDivisor_sub_poleDivisor, map_sub,
    ← PlaceData.poleDivisor_inv D g, degOf_poleDivisor_eq_finrank D g⁻¹,
    degOf_poleDivisor_eq_finrank D g, PlaceData.adjoin_inv_eq g, sub_self]

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
`not_isRationalGenerator`.

## PROVEN 2026-07-28 from `degOf_poleDivisor_eq_finrank` and `finrank_residue_pt_eq_one`

`div_∞ g = (P)` is read off `hg` coefficientwise (`pt` is injective, so `pt P ≠ pt Q`), its
degree is `deg (pt P) = 1`, and the identity turns that into `[F : K⟮g⟯] = 1`; a
one-dimensional extension is spanned by `1`, so every `w ∈ F` is a scalar `c ∈ K⟮g⟯` times
`1`, i.e. lies in `K⟮g⟯`, and `IntermediateField.mem_adjoin_simple_iff` turns membership into
the quotient of polynomials that `IsRationalGenerator` asks for.  The junk branch
`aeval g s = 0` of that quotient is answered with `(a, b) = (0, 1)`, since it forces `z = 0`.

`hsep` is used, but only through `finrank_residue_pt_eq_one`, i.e. for SMOOTHNESS and not
for the genus: with a rational point of residue degree `2` the pole divisor would have
degree `2` and `g` would not generate. -/
theorem isRationalGenerator_of_divisor_eq_sub_single
    {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    {P Q : Pt c₀ c₁ c₂ c₃ c₄ c₅ K} (hPQ : P ≠ Q) {g : D.F}
    (hg : D.divisor g = Finsupp.single (D.pt Q) (1 : ℤ) - Finsupp.single (D.pt P) (1 : ℤ)) :
    D.IsRationalGenerator g := by
  have hne : D.pt P ≠ D.pt Q := fun h => hPQ (D.pt_injective h)
  have hpole : D.poleDivisor g = Finsupp.single (D.pt P) (1 : ℤ) := by
    ext v
    rw [PlaceData.poleDivisor_apply, hg]
    simp only [Finsupp.sub_apply]
    by_cases hP : D.pt P = v
    · subst hP
      simp [hne]
    · simp [hP]
      by_cases hQ : D.pt Q = v <;> simp [hQ]
  have hdeg : degHom D D.degOf (D.poleDivisor g) = 1 := by
    rw [hpole, degHom_single, one_mul, PlaceData.degOf,
      finrank_residue_pt_eq_one D hsep P, Nat.cast_one]
  have hfr : Module.finrank (IntermediateField.adjoin K {g}) D.F = 1 := by
    have h := degOf_poleDivisor_eq_finrank D g
    rw [hdeg] at h
    exact_mod_cast h.symm
  have hspan := (finrank_eq_one_iff_of_nonzero' (K := IntermediateField.adjoin K {g})
    (V := D.F) (1 : D.F) one_ne_zero).mp hfr
  have htop : ∀ w : D.F, w ∈ IntermediateField.adjoin K {g} := by
    intro w
    obtain ⟨c, hc⟩ := hspan w
    have hcw : (c : D.F) = w := by simpa [Algebra.smul_def] using hc
    exact hcw ▸ c.2
  intro z
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K z).mp (htop z)
  rcases eq_or_ne (aeval g s) 0 with h0 | h0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, h0]
    simp
  · exact ⟨r, s, h0, by rw [hrs, div_mul_cancel₀ _ h0]⟩

section Genus2

variable {L : Type*} [Field L]

/-! ### The genus: the pencil count over an algebraically closed field (PROVEN)

The mathematical heart of `not_isRationalGenerator`, with no `PlaceData` and no sextic in
it: **if `A, B` are coprime polynomials over an algebraically closed field and six distinct
members `A − rᵢB` of their pencil are squares, then `A` and `B` are both constant.**

The count is the DERIVATIVE count, not the pencil count the old route note sketched.  From
`A − rᵢB = Cᵢ²` one gets `A' − rᵢB' = 2CᵢCᵢ'`, hence `Cᵢ` divides the Wronskian

    W := A'B − AB' = (A' − rᵢB')·B − (A − rᵢB)·B',

both terms being divisible by `Cᵢ`.  The `Cᵢ` are pairwise coprime (a common factor of
`A − rᵢB` and `A − rⱼB` divides `(rⱼ − rᵢ)B` and `A`), so `∏ Cᵢ ∣ W`.  At most ONE of the six
can drop degree — two of them dropping forces both `A` and `B` below `n = max (deg A) (deg B)`
— so `deg ∏ Cᵢ ≥ 5n/2`, while `deg W ≤ deg A + deg B ≤ 2n`.  In whole numbers: `5n ≤ 4n`,
so `n = 0`.

`W = 0` is the one case the count cannot see, and it is a genuine second branch rather than
a degenerate one.  `A'B = AB'` with `A, B` coprime forces `A ∣ A'` and `B ∣ B'`, hence
`A' = B' = 0`; a nonconstant polynomial with vanishing derivative has `(deg : L) = 0`, so the
characteristic is a prime `p ∣ n`, and over the PERFECT field `L` we get `A = Ã^p`, `B = B̃^p`
(Frobenius is bijective, and `expand_contract` supplies the `p`-th-power shape).  Then
`A − rᵢB = (Ã − rᵢ^{1/p}B̃)^p` by `sub_pow_char`, and **this is where `2 ≠ 0` is used and
nowhere else**: a `p`-th power that is a square is a square when `p` is ODD, so the same
hypotheses hold for `(Ã, B̃)` with `max (deg Ã) (deg B̃) = n/p < n`, and the induction closes.

In characteristic `2` the branch is not merely unavailable, it is forced: `2CᵢCᵢ' = 0` makes
`A' − rᵢB' = 0` for two distinct `rᵢ`, hence `B' = A' = 0`, hence `W = 0` always — which is
exactly why `no_sextic_sq_of_ratFunc` is false there.  See the witness on that leaf. -/

/-- Two distinct members of the pencil spanned by coprime `A, B` are coprime. -/
theorem isCoprime_pencil {A B : L[X]} (h : IsCoprime A B) {a b : L} (hab : a ≠ b) :
    IsCoprime (A - C a * B) (A - C b * B) := by
  obtain ⟨u, v, huv⟩ := h
  have hba : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
  have he : C ((b - a)⁻¹) * (C b - C a) = 1 := by
    rw [← C_sub, ← C_mul, inv_mul_cancel₀ hba, C_1]
  exact ⟨C ((b - a)⁻¹) * (u * C b + v), C ((b - a)⁻¹) * (-(u * C a) - v), by
    linear_combination (C ((b - a)⁻¹) * (C b - C a)) * huv + he⟩

/-- A square member of the pencil divides the Wronskian. -/
theorem dvd_wronskian_of_pencil_sq {A B G : L[X]} {a : L} (h : A - C a * B = G ^ 2) :
    G ∣ derivative A * B - A * derivative B := by
  have h1 := congrArg Polynomial.derivative h
  rw [derivative_sub, derivative_C_mul, pow_two, derivative_mul] at h1
  exact ⟨2 * derivative G * B - G * derivative B, by
    linear_combination B * h1 - derivative B * h⟩

/-- An odd power that is a square is a square. -/
theorem isSquare_of_odd_pow_eq_sq {E G : L[X]} (hE : E ≠ 0) {m : ℕ}
    (h : E ^ (2 * m + 1) = G ^ 2) : ∃ H : L[X], E = H ^ 2 := by
  have hdvd : (E ^ m) ^ 2 ∣ G ^ 2 := ⟨E, by rw [← h]; ring⟩
  obtain ⟨H, hH⟩ := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (two_ne_zero)).mp hdvd
  refine ⟨H, mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero m hE)) ?_⟩
  calc (E ^ m) ^ 2 * E = E ^ (2 * m + 1) := by ring
    _ = G ^ 2 := h
    _ = (E ^ m * H) ^ 2 := by rw [hH]
    _ = (E ^ m) ^ 2 * H ^ 2 := by ring

/-- **The core count**: coprime `A, B` cannot have six members of their pencil be squares
unless both are constant. -/
theorem pencil_elim [PerfectField L] (h2 : (2 : L) ≠ 0) :
    ∀ (N n : ℕ), n ≤ N → ∀ (A B : L[X]), max A.natDegree B.natDegree = n → IsCoprime A B →
      ∀ (r : Fin 6 → L), Function.Injective r →
        (∀ i, ∃ Ci : L[X], A - C (r i) * B = Ci ^ 2) → n = 0 := by
  intro N
  induction N with
  | zero => intro n hn _ _ _ _ _ _ _; omega
  | succ N ihN =>
    intro n hnN A B hn hAB r hr hsq
    classical
    by_contra hn0
    have hA0 : A ≠ 0 := by
      rintro rfl
      have hu : IsUnit B := isCoprime_zero_left.mp hAB
      have : n = 0 := by rw [← hn, natDegree_zero, natDegree_eq_zero_of_isUnit hu]; simp
      exact hn0 this
    have hB0 : B ≠ 0 := by
      rintro rfl
      have hu : IsUnit A := isCoprime_zero_right.mp hAB
      have : n = 0 := by rw [← hn, natDegree_zero, natDegree_eq_zero_of_isUnit hu]; simp
      exact hn0 this
    have hAn : A.natDegree ≤ n := hn ▸ le_max_left _ _
    have hBn : B.natDegree ≤ n := hn ▸ le_max_right _ _
    choose Ci hCi using hsq
    -- each `Cᵢ` is nonzero
    have hCine : ∀ i, Ci i ≠ 0 := by
      intro i hzero
      have hAeq : A = C (r i) * B := by
        have h := hCi i
        rw [hzero] at h
        simpa [sub_eq_zero] using h
      have hBu : IsUnit B := hAB.isUnit_of_dvd' ⟨C (r i), by rw [hAeq]; ring⟩ dvd_rfl
      have hBdeg : B.natDegree = 0 := natDegree_eq_zero_of_isUnit hBu
      have hAdeg : A.natDegree = 0 := by
        rw [hAeq]
        exact Nat.le_zero.mp (natDegree_mul_le.trans (by simp [hBdeg]))
      exact hn0 (by rw [← hn, hAdeg, hBdeg]; simp)
    -- pairwise coprime
    have hCicop : ∀ i j, i ≠ j → IsCoprime (Ci i) (Ci j) := by
      intro i j hij
      have hp := isCoprime_pencil hAB (a := r i) (b := r j) (fun h => hij (hr h))
      rw [hCi i, hCi j] at hp
      exact (hp.of_isCoprime_of_dvd_left (dvd_pow_self _ two_ne_zero)).of_isCoprime_of_dvd_right
        (dvd_pow_self _ two_ne_zero)
    -- degree of each member
    have hdegC : ∀ i, (A - C (r i) * B).natDegree = 2 * (Ci i).natDegree := by
      intro i; rw [hCi i, natDegree_pow]
    have hdegle : ∀ i, 2 * (Ci i).natDegree ≤ n := by
      intro i
      rw [← hdegC i]
      refine (natDegree_sub_le _ _).trans ?_
      rw [← hn]
      exact max_le_max le_rfl (natDegree_C_mul_le _ _)
    -- at most one member can drop degree
    have hbad : ∀ i j, i ≠ j → 2 * (Ci i).natDegree < n → 2 * (Ci j).natDegree < n → False := by
      intro i j hij hi hj
      have hab : r i ≠ r j := fun h => hij (hr h)
      have hba : r j - r i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
      have hdi : (A - C (r i) * B).natDegree < n := by rw [hdegC i]; exact hi
      have hdj : (A - C (r j) * B).natDegree < n := by rw [hdegC j]; exact hj
      have hBlt : B.natDegree < n := by
        have hdiff : C (r j - r i) * B = (A - C (r i) * B) - (A - C (r j) * B) := by
          rw [C_sub]; ring
        have h1 : (C (r j - r i) * B).natDegree < n := by
          rw [hdiff]
          exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdi hdj)
        rw [natDegree_mul (C_ne_zero.mpr hba) hB0, natDegree_C] at h1
        simpa using h1
      have hAlt : A.natDegree < n := by
        have hdiff : C (r j - r i) * A
            = C (r j) * (A - C (r i) * B) - C (r i) * (A - C (r j) * B) := by
          rw [C_sub]; ring
        have h1 : (C (r j - r i) * A).natDegree < n := by
          rw [hdiff]
          refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
          · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hdi
          · exact lt_of_le_of_lt (natDegree_C_mul_le _ _) hdj
        rw [natDegree_mul (C_ne_zero.mpr hba) hA0, natDegree_C] at h1
        simpa using h1
      have hlt := max_lt hAlt hBlt
      rw [hn] at hlt
      exact absurd hlt (lt_irrefl n)
    -- so at least five members have full degree
    have hcompl : (Finset.univ.filter
        (fun i : Fin 6 => ¬ (2 * (Ci i).natDegree = n))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      by_contra hij
      simp only [Finset.mem_filter] at hi hj
      exact hbad i j hij (lt_of_le_of_ne (hdegle i) hi.2) (lt_of_le_of_ne (hdegle j) hj.2)
    have hcard : 5 ≤ (Finset.univ.filter (fun i : Fin 6 => 2 * (Ci i).natDegree = n)).card := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 6))) (p := fun i => 2 * (Ci i).natDegree = n)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hsum : 5 * n ≤ 2 * ∑ i, (Ci i).natDegree := by
      calc 5 * n
          ≤ (Finset.univ.filter (fun i : Fin 6 => 2 * (Ci i).natDegree = n)).card * n :=
            Nat.mul_le_mul_right n hcard
        _ = ∑ _i ∈ Finset.univ.filter (fun i : Fin 6 => 2 * (Ci i).natDegree = n), n := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin 6 => 2 * (Ci i).natDegree = n),
              2 * (Ci i).natDegree :=
            Finset.sum_congr rfl (fun i hi => ((Finset.mem_filter.mp hi).2).symm)
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 6)), 2 * (Ci i).natDegree :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 2 * ∑ i, (Ci i).natDegree := by rw [Finset.mul_sum]
    by_cases hWne : derivative A * B - A * derivative B = 0
    · -- ### the `W = 0` branch: both derivatives vanish and we descend along Frobenius
      have hdvdA : A ∣ derivative A :=
        hAB.dvd_of_dvd_mul_right ⟨derivative B, by linear_combination hWne⟩
      have hdvdB : B ∣ derivative B :=
        hAB.symm.dvd_of_dvd_mul_right ⟨derivative A, by linear_combination -hWne⟩
      have hderiv : ∀ P : L[X], P ≠ 0 → P ∣ derivative P → derivative P = 0 := by
        intro P hP hd
        by_contra hne
        have h1 := natDegree_le_of_dvd hd hne
        have h2 := natDegree_derivative_le P
        have hP0 : P.natDegree = 0 := by omega
        rw [eq_C_of_natDegree_eq_zero hP0, derivative_C] at hne
        exact hne rfl
      have hA' : derivative A = 0 := hderiv A hA0 hdvdA
      have hB' : derivative B = 0 := hderiv B hB0 hdvdB
      -- the degree of a nonconstant polynomial with vanishing derivative dies in `L`
      have hdegcast : ∀ P : L[X], P ≠ 0 → derivative P = 0 → P.natDegree ≠ 0 →
          ((P.natDegree : ℕ) : L) = 0 := by
        intro P hP hd hne
        obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
        have h := coeff_derivative P k
        rw [hd, coeff_zero] at h
        have hlc : P.coeff (k + 1) ≠ 0 := by
          rw [← hk]; exact leadingCoeff_ne_zero.mpr hP
        have hkc : (k : L) + 1 = 0 := by
          rcases mul_eq_zero.mp h.symm with h' | h'
          · exact absurd h' hlc
          · exact h'
        rw [hk]; push_cast; exact hkc
      have hncast : ((n : ℕ) : L) = 0 := by
        rcases max_cases A.natDegree B.natDegree with ⟨he, _⟩ | ⟨he, _⟩
        · have hAeq : A.natDegree = n := by rw [← hn, he]
          rw [← hAeq]; exact hdegcast A hA0 hA' (by omega)
        · have hBeq : B.natDegree = n := by rw [← hn, he]
          rw [← hBeq]; exact hdegcast B hB0 hB' (by omega)
      -- the characteristic is an odd prime `p` dividing `n`
      haveI hchar : CharP L (ringChar L) := ringChar.charP L
      set p := ringChar L with hpdef
      have hpn : p ∣ n := (CharP.cast_eq_zero_iff L p n).mp hncast
      have hp0 : p ≠ 0 := by
        intro h
        rw [h] at hpn
        exact hn0 (Nat.eq_zero_of_zero_dvd hpn)
      haveI hpp : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero L hp0⟩
      have hp2 : p ≠ 2 := by
        intro h
        refine h2 ?_
        have : ((2 : ℕ) : L) = 0 := by rw [CharP.cast_eq_zero_iff L p 2, h]
        simpa using this
      obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
        obtain ⟨m, hm⟩ := (Fact.out (p := p.Prime)).odd_of_ne_two hp2
        exact ⟨m, by omega⟩
      haveI : ExpChar L p := ExpChar.prime (Fact.out (p := p.Prime))
      haveI : ExpChar L[X] p := ExpChar.prime (Fact.out (p := p.Prime))
      -- descend along Frobenius
      set σ : L →+* L := ((frobeniusEquiv L p).symm : L →+* L) with hσ
      have hfrob : ∀ x : L, (σ x) ^ p = x := fun x => frobenius_apply_frobeniusEquiv_symm L p x
      have hdesc : ∀ P : L[X], derivative P = 0 → P = (map σ (contract p P)) ^ p := by
        intro P hP
        have h1 : map (frobenius L p) P = (contract p P) ^ p := by
          conv_lhs => rw [← Polynomial.expand_contract (p := p) hP hp0]
          exact map_frobenius_expand p (contract p P)
        calc P = map σ (map (frobenius L p) P) := by
              rw [map_map, hσ, frobeniusEquiv_symm_comp_frobenius, map_id]
          _ = map σ ((contract p P) ^ p) := by rw [h1]
          _ = (map σ (contract p P)) ^ p := by rw [Polynomial.map_pow]
      set A' : L[X] := map σ (contract p A) with hA'def
      set B' : L[X] := map σ (contract p B) with hB'def
      have hAp : A = A' ^ p := hdesc A hA'
      have hBp : B = B' ^ p := hdesc B hB'
      -- the descended data
      have hcop' : IsCoprime A' B' := by
        rw [hAp, hBp] at hAB
        exact (hAB.of_isCoprime_of_dvd_left (dvd_pow_self _ hp0)).of_isCoprime_of_dvd_right
          (dvd_pow_self _ hp0)
      have hrinj : Function.Injective (fun i => σ (r i)) := by
        intro i j hij
        exact hr ((frobeniusEquiv L p).symm.injective hij)
      have hsq' : ∀ i, ∃ D : L[X], A' - C (σ (r i)) * B' = D ^ 2 := by
        intro i
        have hEp : (A' - C (σ (r i)) * B') ^ p = Ci i ^ 2 := by
          have hCr : C (r i) = (C (σ (r i))) ^ p := by
            rw [← C_pow, hfrob]
          calc (A' - C (σ (r i)) * B') ^ p
              = A' ^ p - (C (σ (r i)) * B') ^ p := sub_pow_char A' (C (σ (r i)) * B')
            _ = A - C (r i) * B := by rw [mul_pow, ← hCr, ← hAp, ← hBp]
            _ = Ci i ^ 2 := hCi i
        have hEne : A' - C (σ (r i)) * B' ≠ 0 := by
          intro h0
          rw [h0, zero_pow hp0] at hEp
          exact hCine i (pow_eq_zero_iff two_ne_zero |>.mp hEp.symm)
        rw [hm] at hEp
        exact isSquare_of_odd_pow_eq_sq hEne hEp
      -- the descended degree
      have hdegA : A.natDegree = p * A'.natDegree := by rw [hAp, natDegree_pow]
      have hdegB : B.natDegree = p * B'.natDegree := by rw [hBp, natDegree_pow]
      have hmaxmul : max (p * A'.natDegree) (p * B'.natDegree)
          = p * max A'.natDegree B'.natDegree := by
        rcases le_total A'.natDegree B'.natDegree with h | h
        · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul (le_refl p) h)]
        · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul (le_refl p) h)]
      have hnp : n = p * max A'.natDegree B'.natDegree := by
        rw [← hn, hdegA, hdegB, hmaxmul]
      have hp3 : 3 ≤ p := by
        have := (Fact.out (p := p.Prime)).two_le
        omega
      have hn'0 : max A'.natDegree B'.natDegree ≠ 0 := by
        intro h; rw [h, Nat.mul_zero] at hnp; exact hn0 hnp
      have hn'le : max A'.natDegree B'.natDegree ≤ N := by
        have : 2 * max A'.natDegree B'.natDegree + max A'.natDegree B'.natDegree ≤ n := by
          calc 2 * max A'.natDegree B'.natDegree + max A'.natDegree B'.natDegree
              = 3 * max A'.natDegree B'.natDegree := by ring
            _ ≤ p * max A'.natDegree B'.natDegree := Nat.mul_le_mul hp3 (le_refl _)
            _ = n := hnp.symm
        omega
      exact hn'0 (ihN _ hn'le A' B' rfl hcop' _ hrinj hsq')
    · -- ### the `W ≠ 0` branch: the degree count
      have hprod : (∏ i, Ci i) ∣ derivative A * B - A * derivative B :=
        Finset.prod_dvd_of_coprime (fun i _ j _ hij => hCicop i j hij)
          (fun i _ => dvd_wronskian_of_pencil_sq (hCi i))
      have hdegprod : (∏ i, Ci i).natDegree = ∑ i, (Ci i).natDegree :=
        natDegree_prod _ _ (fun i _ => hCine i)
      have h1 : ∑ i, (Ci i).natDegree ≤ (derivative A * B - A * derivative B).natDegree := by
        rw [← hdegprod]; exact natDegree_le_of_dvd hprod hWne
      have h2 : (derivative A * B - A * derivative B).natDegree
          ≤ A.natDegree + B.natDegree := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_mul_le.trans (by have := natDegree_derivative_le A; omega)
        · exact natDegree_mul_le.trans (by have := natDegree_derivative_le B; omega)
      omega

end Genus2

/-- The homogenised sextic `B⁶·f(A/B)` over any commutative ring. -/
noncomputable def hsextOf (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) {R : Type*} [CommRing R] (A B : R) : R :=
  A ^ 6 + (c₅ : R) * A ^ 5 * B + (c₄ : R) * A ^ 4 * B ^ 2 + (c₃ : R) * A ^ 3 * B ^ 3
    + (c₂ : R) * A ^ 2 * B ^ 4 + (c₁ : R) * A * B ^ 5 + (c₀ : R) * B ^ 6

section Genus2Reduce

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ}

/-! ### The reduction of the genus leaf to that count (PROVEN)

`ψ² = f(φ)` with `φ = A/B` in lowest terms gives, after clearing denominators,
`P²B⁶ = Q²·F(A, B)` with `ψ = P/Q` in lowest terms and `F` the HOMOGENISED sextic
(`hsextOf`, i.e. `B⁶·f(A/B)`).  `F(A, B) ≡ A⁶` modulo `B`, so `F` is coprime to `B`; hence
`Q² ∣ B⁶` and `B⁶ ∣ Q²`, the two are associate, and cancelling `B⁶` leaves
`F(A, B) = unit · P²`.

Base-changing to `L = AlgebraicClosure K` — only the POLYNOMIALS are base-changed, never
`RatFunc K`, which is what keeps this elementary — the unit becomes a nonzero constant, and a
constant is a square over `L`, so `F(A_L, B_L)` is a square.  Separability gives `f` SIX
distinct roots over `L` (`exists_six_roots`), and `F(A, B) = ∏ᵢ (A − rᵢB)` — checked in
`RatFunc L`, where it is `f(A/B)·B⁶` read two ways.  The six factors are pairwise coprime, so
each is a square up to a unit by `exists_associated_pow_of_mul_eq_pow'`, and again the unit is
a square over `L`.  That is exactly the hypothesis of `pencil_elim`, whose conclusion
`max (deg A) (deg B) = 0` contradicts transcendence of `φ`. -/

lemma map_hsextOf {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A B : R) :
    f (hsextOf c₀ c₁ c₂ c₃ c₄ c₅ A B) = hsextOf c₀ c₁ c₂ c₃ c₄ c₅ (f A) (f B) := by
  simp [hsextOf]

lemma hsextOf_of_mul {R : Type*} [CommRing R] {z A B : R} (h : z * B = A) :
    sext c₀ c₁ c₂ c₃ c₄ c₅ z * B ^ 6 = hsextOf c₀ c₁ c₂ c₃ c₄ c₅ A B := by
  subst h
  simp only [sext, hsextOf]
  ring

lemma map_sextPoly {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) :
    (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).map f = sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L := by
  simp [sextPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

lemma monic_sextPoly (K : Type*) [CommRing K] [Nontrivial K] :
    (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Monic := by
  unfold sextPoly
  monicity!

/-- A unit of `L[X]` over a field is a nonzero constant. -/
lemma polynomial_eq_C_of_isUnit {L : Type*} [Field L] {u : L[X]} (hu : IsUnit u) :
    ∃ d : L, d ≠ 0 ∧ u = C d := by
  have hdeg : u.degree = 0 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
  refine ⟨u.coeff 0, ?_, Polynomial.eq_C_of_degree_eq_zero hdeg⟩
  intro h
  rw [Polynomial.eq_C_of_degree_eq_zero hdeg, h, map_zero] at hu
  exact not_isUnit_zero hu

/-- A monic separable sextic over an algebraically closed field is a product of six
distinct linear factors. -/
lemma exists_six_roots {L : Type} [Field L] [IsAlgClosed L]
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L).Separable) :
    ∃ r : Fin 6 → L, Function.Injective r ∧
      sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L = ∏ i, (X - C (r i)) := by
  classical
  set f := sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L with hf
  have hmo : f.Monic := monic_sextPoly L
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hcard : Multiset.card f.roots = 6 := by
    rw [(Polynomial.splits_iff_card_roots).mp hsplit, hf, natDegree_sextPoly]
  have hnod : f.roots.Nodup := Polynomial.nodup_roots hsep
  set s : Finset L := f.roots.toFinset with hs
  have hscard : s.card = 6 := by
    rw [hs, Multiset.toFinset_card_of_nodup hnod, hcard]
  have hsval : s.val = f.roots := by rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnod]
  set e : {x // x ∈ s} ≃ Fin 6 := (Finset.equivFin s).trans (finCongr hscard) with he
  refine ⟨fun i => ((e.symm i : L)), ?_, ?_⟩
  · intro i j hij
    have : e.symm i = e.symm j := Subtype.ext hij
    simpa using congrArg e this
  · have h1 : f = (f.roots.map fun a => X - C a).prod := by
      have := hsplit.eq_prod_roots_of_monic hmo
      simpa using this
    rw [h1, ← hsval]
    rw [show (s.val.map fun a => X - C a).prod = ∏ a ∈ s, (X - C a) from rfl]
    rw [← Finset.prod_coe_sort s (fun a => X - C a)]
    exact Fintype.prod_equiv e _ _ (fun a => by simp)


lemma ratFunc_mul_denom_eq_num {K : Type} [Field K] (x : RatFunc K) :
    x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num := by
  have hd : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero x.denom_ne_zero
  have h := RatFunc.num_div_denom x
  rw [div_eq_iff hd] at h
  exact h.symm

lemma algebraMap_polynomial_C {K : Type} [Field K] (x : K) :
    algebraMap K[X] (RatFunc K) (Polynomial.C x) = algebraMap K (RatFunc K) x := by
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

/-- **A separable sextic takes no square value on a transcendental rational function**
(PROVEN 2026-07-30, over `pencil_elim`).

`ψ² = f(φ)` is impossible in `K(T)` for `φ` transcendental over `K`, `f` a separable monic
sextic and `2 ≠ 0`.  This is the whole content of `not_isRationalGenerator` — the genus —
with the `PlaceData` removed: a statement about `K(T)` alone.

**Both hypotheses are load-bearing, with explicit counterexamples.**

* Without `hsep`: `f = (x³ + 1)²`, i.e. `c₀ = c₃ = 1` (over `ℚ`, say) and the rest `0`.  Then
  `φ = T`, `ψ = T³ + 1` satisfies `ψ² = f(φ)` with `φ` transcendental.  This is the same
  witness the docstring on `not_isRationalGenerator` records.
* Without `h2` **the statement is FALSE, and separability does not save it** — this is the
  characteristic-`2` audit on `not_isRationalGenerator` made concrete.  Take `K = 𝔽₂` and
  `f = x⁶ + x`, i.e. `c₁ = 1` and the rest `0`.  It is separable: `f' = 6x⁵ + 1 = 1` in
  characteristic `2`, so `gcd(f, f') = 1`.  And `φ = T²` (transcendental), `ψ = T⁶ + T` give
  `ψ² = T¹² + T² = φ⁶ + φ = f(φ)`, the cross term `2·T⁷` vanishing.  So `h2` cannot be
  dropped here.  It costs `not_isRationalGenerator` nothing, because no `PlaceData` exists in
  characteristic `2` (`placeData_elim_of_two_eq_zero`).

The proof is the two blocks above: `pencil_elim` (the derivative count and its Frobenius
descent) and the reduction that feeds it.  Note where `2 ≠ 0` actually enters — **not** in
the divisibility `Cᵢ ∣ W`, which is characteristic-free, but in the `W = 0` branch, where a
`p`-th power that is a square must be a square.  In characteristic `2` that branch is
unavoidable, since `2CᵢCᵢ' = 0` forces `W = 0`; so the argument fails there exactly where the
statement does.  The earlier route note on this leaf attributed `2 ≠ 0` to the derivative
step, and that was wrong. -/
theorem no_sextic_sq_of_ratFunc {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable)
    {φ ψ : RatFunc K} (hφ : Transcendental K φ)
    (heq : ψ ^ 2 = sext c₀ c₁ c₂ c₃ c₄ c₅ φ) : False := by
  classical
  set A := φ.num with hAdef
  set B := φ.denom with hBdef
  set P := ψ.num with hPdef
  set Q := ψ.denom with hQdef
  have hBne : B ≠ 0 := φ.denom_ne_zero
  have hQne : Q ≠ 0 := ψ.denom_ne_zero
  have hιB : algebraMap K[X] (RatFunc K) B ≠ 0 := RatFunc.algebraMap_ne_zero hBne
  have hιQ : algebraMap K[X] (RatFunc K) Q ≠ 0 := RatFunc.algebraMap_ne_zero hQne
  have hφeq : φ * algebraMap K[X] (RatFunc K) B = algebraMap K[X] (RatFunc K) A := by
    rw [hAdef, hBdef]; exact ratFunc_mul_denom_eq_num φ
  have hψeq : ψ * algebraMap K[X] (RatFunc K) Q = algebraMap K[X] (RatFunc K) P := by
    rw [hPdef, hQdef]; exact ratFunc_mul_denom_eq_num ψ
  -- clear denominators: a polynomial identity
  have hRF : (algebraMap K[X] (RatFunc K) P) ^ 2 * (algebraMap K[X] (RatFunc K) B) ^ 6
      = (algebraMap K[X] (RatFunc K) Q) ^ 2
        * hsextOf c₀ c₁ c₂ c₃ c₄ c₅ (algebraMap K[X] (RatFunc K) A)
            (algebraMap K[X] (RatFunc K) B) := by
    rw [← hsextOf_of_mul hφeq, ← heq, ← hψeq]; ring
  have hkey : P ^ 2 * B ^ 6 = Q ^ 2 * hsextOf c₀ c₁ c₂ c₃ c₄ c₅ A B := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa [map_mul, map_pow, map_hsextOf] using hRF
  set Fh := hsextOf c₀ c₁ c₂ c₃ c₄ c₅ A B with hFhdef
  have hABcop : IsCoprime A B := φ.isCoprime_num_denom
  have hPQcop : IsCoprime P Q := ψ.isCoprime_num_denom
  have hFhB : IsCoprime Fh B := by
    have h1 : Fh = A ^ 6 + B * ((c₅ : K[X]) * A ^ 5 + (c₄ : K[X]) * A ^ 4 * B
        + (c₃ : K[X]) * A ^ 3 * B ^ 2 + (c₂ : K[X]) * A ^ 2 * B ^ 3
        + (c₁ : K[X]) * A * B ^ 4 + (c₀ : K[X]) * B ^ 5) := by
      rw [hFhdef, hsextOf]; ring
    rw [h1]
    exact hABcop.pow_left.add_mul_left_left _
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero _ hQne
  have hQ2dvd : Q ^ 2 ∣ B ^ 6 := hPQcop.symm.pow.dvd_of_dvd_mul_left ⟨Fh, hkey⟩
  have hB6dvd : B ^ 6 ∣ Q ^ 2 :=
    hFhB.symm.pow_left.dvd_of_dvd_mul_right ⟨P ^ 2, by rw [← hkey]; ring⟩
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hQ2dvd hB6dvd
  have hFheq : Fh = (u : K[X]) * P ^ 2 := by
    refine mul_left_cancel₀ hQ2 ?_
    calc Q ^ 2 * Fh = P ^ 2 * B ^ 6 := hkey.symm
      _ = P ^ 2 * (Q ^ 2 * (u : K[X])) := by rw [hu]
      _ = Q ^ 2 * ((u : K[X]) * P ^ 2) := by ring
  -- base change to an algebraic closure
  set L := AlgebraicClosure K with hLdef
  set g : K →+* L := algebraMap K L with hgdef
  have hginj : Function.Injective g := (algebraMap K L).injective
  set ρ : K[X] →+* L[X] := Polynomial.mapRingHom g with hρdef
  set AL : L[X] := A.map g with hALdef
  set BL : L[X] := B.map g with hBLdef
  set PL : L[X] := P.map g with hPLdef
  have hρA : ρ A = AL := rfl
  have hρB : ρ B = BL := rfl
  have hρP : ρ P = PL := rfl
  have h2L : (2 : L) ≠ 0 := by
    intro h
    refine h2 ((map_eq_zero_iff g hginj).mp ?_)
    rw [map_ofNat]
    exact h
  have hABLcop : IsCoprime AL BL := by
    have := hABcop.map ρ
    rwa [hρA, hρB] at this
  have hBLne : BL ≠ 0 := by
    rw [← hρB]
    exact fun h => hBne ((map_eq_zero_iff ρ (Polynomial.map_injective g hginj)).mp h)
  -- the homogenised sextic is a square over `L`
  obtain ⟨d, hdne, hdeq⟩ := polynomial_eq_C_of_isUnit (u.isUnit.map ρ)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq d (n := 2) (by norm_num)
  set χ : L[X] := Polynomial.C w * PL with hχdef
  have hFhLsq : hsextOf c₀ c₁ c₂ c₃ c₄ c₅ AL BL = χ ^ 2 := by
    have e1 : ρ Fh = hsextOf c₀ c₁ c₂ c₃ c₄ c₅ AL BL := by
      rw [hFhdef, map_hsextOf, hρA, hρB]
    rw [← e1, hFheq, map_mul, hdeq, map_pow, hρP, hχdef, mul_pow, ← Polynomial.C_pow, hw]
  -- the six roots
  have hsepL : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L).Separable := by
    have := hsep.map (f := g)
    rwa [map_sextPoly] at this
  obtain ⟨r, hrinj, hrfac⟩ := exists_six_roots hsepL
  -- the product formula
  have hprodeq : hsextOf c₀ c₁ c₂ c₃ c₄ c₅ AL BL = ∏ i, (AL - Polynomial.C (r i) * BL) := by
    have hκB : algebraMap L[X] (RatFunc L) BL ≠ 0 := RatFunc.algebraMap_ne_zero hBLne
    apply IsFractionRing.injective L[X] (RatFunc L)
    obtain ⟨z, hzm⟩ : ∃ z : RatFunc L,
        z * algebraMap L[X] (RatFunc L) BL = algebraMap L[X] (RatFunc L) AL :=
      ⟨algebraMap L[X] (RatFunc L) AL / algebraMap L[X] (RatFunc L) BL,
        div_mul_cancel₀ _ hκB⟩
    have hsplit : sext c₀ c₁ c₂ c₃ c₄ c₅ z
        = ∏ i, (z - algebraMap L (RatFunc L) (r i)) := by
      have h1 : Polynomial.aeval z (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ L)
          = sext c₀ c₁ c₂ c₃ c₄ c₅ z := aeval_sextPoly c₀ c₁ c₂ c₃ c₄ c₅ z
      rw [← h1, hrfac, map_prod]
      simp
    calc algebraMap L[X] (RatFunc L) (hsextOf c₀ c₁ c₂ c₃ c₄ c₅ AL BL)
        = hsextOf c₀ c₁ c₂ c₃ c₄ c₅ (algebraMap L[X] (RatFunc L) AL)
            (algebraMap L[X] (RatFunc L) BL) := map_hsextOf _ _ _
      _ = sext c₀ c₁ c₂ c₃ c₄ c₅ z * (algebraMap L[X] (RatFunc L) BL) ^ 6 :=
          (hsextOf_of_mul hzm).symm
      _ = (∏ i, (z - algebraMap L (RatFunc L) (r i)))
            * (algebraMap L[X] (RatFunc L) BL) ^ 6 := by rw [hsplit]
      _ = ∏ i, ((z - algebraMap L (RatFunc L) (r i))
            * algebraMap L[X] (RatFunc L) BL) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i, algebraMap L[X] (RatFunc L) (AL - Polynomial.C (r i) * BL) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [map_sub, map_mul, algebraMap_polynomial_C, ← hzm]
          ring
      _ = algebraMap L[X] (RatFunc L) (∏ i, (AL - Polynomial.C (r i) * BL)) := by rw [map_prod]
  -- each factor is a square
  have hsqfac : ∀ i, ∃ D : L[X], AL - Polynomial.C (r i) * BL = D ^ 2 := by
    intro i
    have hcop : IsCoprime (AL - Polynomial.C (r i) * BL)
        (∏ j ∈ Finset.univ.erase i, (AL - Polynomial.C (r j) * BL)) :=
      IsCoprime.prod_right (fun j hj =>
        isCoprime_pencil hABLcop (fun h => (Finset.mem_erase.mp hj).1 (hrinj h).symm))
    have hmul : (AL - Polynomial.C (r i) * BL)
        * (∏ j ∈ Finset.univ.erase i, (AL - Polynomial.C (r j) * BL)) = χ ^ 2 := by
      rw [Finset.mul_prod_erase Finset.univ (fun j => AL - Polynomial.C (r j) * BL)
        (Finset.mem_univ i), ← hprodeq, hFhLsq]
    obtain ⟨D, v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hcop hmul
    obtain ⟨d', hd'ne, hd'eq⟩ := polynomial_eq_C_of_isUnit v.isUnit
    exact ⟨D * Polynomial.C (Classical.choose (IsAlgClosed.exists_pow_nat_eq d' (n := 2)
        (by norm_num))), by
      rw [← hv, hd'eq, mul_pow, ← Polynomial.C_pow,
        Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq d' (n := 2) (by norm_num))]⟩
  -- the degrees, and the contradiction
  have hdegA : AL.natDegree = A.natDegree := by rw [hALdef]; exact Polynomial.natDegree_map g
  have hdegB : BL.natDegree = B.natDegree := by rw [hBLdef]; exact Polynomial.natDegree_map g
  have hmaxne : max A.natDegree B.natDegree ≠ 0 := by
    intro hmax
    have hAd : A.natDegree = 0 := Nat.le_zero.mp (hmax ▸ le_max_left _ _)
    have hBd : B.natDegree = 0 := Nat.le_zero.mp (hmax ▸ le_max_right _ _)
    have hAC : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hAd
    have hBC : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hBd
    have hbne : B.coeff 0 ≠ 0 := by
      intro h
      rw [hBC, h, map_zero] at hBne
      exact hBne rfl
    have hbne' : algebraMap K (RatFunc K) (B.coeff 0) ≠ 0 := by
      simpa using hbne
    have h1 : φ * algebraMap K (RatFunc K) (B.coeff 0)
        = algebraMap K (RatFunc K) (A.coeff 0) := by
      have h0 := hφeq
      rw [hAC, hBC, algebraMap_polynomial_C, algebraMap_polynomial_C] at h0
      exact h0
    have hφval : φ = algebraMap K (RatFunc K) (A.coeff 0 / B.coeff 0) := by
      rw [map_div₀, eq_div_iff hbne']
      exact h1
    refine hφ ⟨Polynomial.X - Polynomial.C (A.coeff 0 / B.coeff 0),
      Polynomial.X_sub_C_ne_zero _, ?_⟩
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hφval, sub_self]
  have hzero := pencil_elim h2L (max AL.natDegree BL.natDegree)
    (max AL.natDegree BL.natDegree) le_rfl AL BL rfl hABLcop r hrinj hsqfac
  rw [hdegA, hdegB] at hzero
  exact hmaxne hzero

end Genus2Reduce

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

**ROUTE NOTE 2026-07-28: the first step of the pencil argument IS in mathlib at this pin.**
`RatFunc.finrank_eq_max_natDegree` in `Mathlib/FieldTheory/RatFunc/IntermediateField.lean`
says `[K⟮X⟯ : K⟮φ⟯] = max φ.num.natDegree φ.denom.natDegree` — exactly the step
"`max (deg A) (deg B) = [K(t) : K(xx)]`" that the sketch above uses to pin the pencil to
binary QUADRATICS.  The same file supplies `RatFunc.transcendental_of_ne_C`,
`RatFunc.adjoin_X` and the minimal polynomial `RatFunc.minpolyX`, so the algebra of
`K(t) ⊇ K(A/B)` need not be rebuilt.  What is NOT there, and is the real work of this leaf:
transporting `IsRationalGenerator t` into an isomorphism `F ≃ₐ[K] RatFunc K`, computing
`[F : K(xx)] = 2` from `eqn` and `gen`, and the pencil count itself (a product of pairwise
coprime binary quadratics is a square only if each factor is, and at most two members of a
pencil of binary quadratics are singular).  Checked by `grep` on 2026-07-28; nothing above
claims otherwise, this is an addition rather than a correction.

The same remark applies to `finrank_residue_pt_eq_one`,
`isRationalGenerator_of_divisor_eq_sub_single` and hence to `sub_single_pt_notMem_princ`
itself, which has carried this since it was written: none of them says `2 ≠ 0`, and none of
them needs to.  **Do not "repair" these statements by adding a characteristic hypothesis** —
that would push a new obligation onto every consumer for a case that is already vacuous.

## DECOMPOSED 2026-07-30 — both halves of the split above are now Lean

The characteristic-`2` audit is no longer prose: `placeData_elim_of_two_eq_zero` in the
`Genus` section PROVES that no `PlaceData` exists there, by exactly the argument recorded
above.  And the transport half — "`IsRationalGenerator t` into an isomorphism
`F ≃ₐ[K] RatFunc K`", which the route note called the real work — is
`ratFuncEquivOfIsRationalGenerator` together with `ratFuncEquiv_yy_sq` and
`transcendental_ratFuncEquiv_xx`.  What is left is `no_sextic_sq_of_ratFunc` below, a
statement about `K(T)` with no `PlaceData` in it at all. -/
theorem not_isRationalGenerator {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {K : Type} [Field K]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ K)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ K).Separable) (t : D.F) :
    ¬ D.IsRationalGenerator t := by
  intro h
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · exact placeData_elim_of_two_eq_zero D h2
  · exact no_sextic_sq_of_ratFunc h2 hsep (transcendental_ratFuncEquiv_xx D h)
      (ratFuncEquiv_yy_sq D h)

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

A SECOND cut was made later the same day, in the same spirit and with the same bundling:
`exists_reductionFiltration` is now PROVEN from `exists_smoothModel`, which asks for the
divisor specialisation along the smooth `ℤ_p`-model together with the formal logarithm of
the Jacobian — again in ONE existential, so that `red` is derived from the model rather
than postulated.  See the section note before `padicLevel` below.

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

/-!
### The smooth `ℤ_p`-model and the formal logarithm

**DECOMPOSED 2026-07-28 (second cut).**  `exists_reductionFiltration` was itself decomposed,
one level further down and along the axis the geometry actually runs on.  Producing a
`ReductionFiltration` needs two things, and they are of completely different kinds:

* **specialisation of divisors** along the smooth proper model `𝒳/ℤ_p`.  A closed point of
  `X_ℚ` has a closure in `𝒳` that is finite flat over `ℤ_p`, and that closure meets the
  special fibre in an effective divisor of `X_𝔽ₚ`; extended `ℤ`-linearly this is
  `sp : Div(X_ℚ) → Div(X_𝔽ₚ)`.  It carries principal divisors to principal ones — the
  closure of `div g` is `div_𝒳(g)` minus a multiple of the special fibre, and the special
  fibre IS `div_𝒳(p)`, so the vertical part restricts to a principal divisor — and it
  carries the closure of a rational point, which is a SECTION of `𝒳 → Spec ℤ_p`, to the
  single point `redPt P`.  That is `Specialisation`, and `red` is **derived** from it
  below rather than postulated, which is what the section note above asks for.
* **the formal logarithm** of the Jacobian.  `ker red` sits inside
  `ker (J(ℚ_p) → J(𝔽ₚ)) = Ĵ(pℤ_p)`, and for `e < p − 1` — with `e = v_p(p) = 1` this is
  exactly `p ≠ 2` — the formal logarithm converges on `Ĵ(pℤ_p)` and is an injective
  homomorphism into `(pℤ_p)^g` with `g = 2`, the genus.  That is `log`, `log_injective`
  and `log_mem_one`, and it is the one place where `p ≠ 2` is genuinely used: at `p = 2`
  the series `log` does not converge on `Ĵ(2ℤ_2)`, and indeed `Ĵ(2ℤ_2)` can have
  `2`-torsion, so no such `log` exists.

**The two halves stay inside ONE existential** (`SmoothModel`), for exactly the reason the
section note above gives: `∀ compatible red, ∃ log …` is a different statement, satisfiable
or refutable by hand-built junk `red`s, and it is not the one we want.  What the cut buys is
that all four `ReductionFiltration` axioms — including `smul_p_notMem`, the sharp form of
"multiplication by `p` raises the level by exactly one" — become THEOREMS about
divisibility in `ℤ_p`, proven below, rather than assumptions.

**`log` is asked to be INJECTIVE and not surjective, and that is not laziness.**  Over
`ℤ_p` with `e < p − 1` the logarithm is an ISOMORPHISM `Ĵ(pℤ_p) ≅ (pℤ_p)^g`; but `ker red`
is only the group of `ℚ`-RATIONAL classes in there, which is finitely generated (Mordell–
Weil) and therefore never all of `Ĵ(pℤ_p)`, an uncountable group.  Demanding surjectivity
would make the leaf FALSE.  Injectivity is all the filtration argument uses.
-/

/-- The subgroup of `ℤ_[p] × ℤ_[p]` of pairs both divisible by `pⁿ` — the image under the
formal logarithm of the `n`-th step `Ĵ(pⁿℤ_p)` of the formal group. -/
def padicLevel (p : ℕ) [Fact p.Prime] (n : ℕ) : AddSubgroup (ℤ_[p] × ℤ_[p]) where
  carrier := {z | (p : ℤ_[p]) ^ n ∣ z.1 ∧ (p : ℤ_[p]) ^ n ∣ z.2}
  zero_mem' := ⟨dvd_zero _, dvd_zero _⟩
  add_mem' := fun ha hb => ⟨dvd_add ha.1 hb.1, dvd_add ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨(dvd_neg).mpr ha.1, (dvd_neg).mpr ha.2⟩

lemma mem_padicLevel {p : ℕ} [Fact p.Prime] {n : ℕ} {z : ℤ_[p] × ℤ_[p]} :
    z ∈ padicLevel p n ↔ (p : ℤ_[p]) ^ n ∣ z.1 ∧ (p : ℤ_[p]) ^ n ∣ z.2 := Iff.rfl

/-- **`ℤ_p` is separated for the `p`-adic filtration** (PROVEN): an element divisible by
every power of `p` is `0`.  A nonzero `x` has a finite `valuation`, and `pⁿ ∣ x` says
`n ≤ x.valuation`; taking `n = x.valuation + 1` is the contradiction.  This is what makes
`filt_separated` true below. -/
lemma padicInt_eq_zero_of_forall_pow_dvd {p : ℕ} [Fact p.Prime] (x : ℤ_[p])
    (h : ∀ n : ℕ, (p : ℤ_[p]) ^ n ∣ x) : x = 0 := by
  by_contra hx
  have key := fun n : ℕ =>
    (PadicInt.mem_span_pow_iff_le_valuation x hx n).mp (Ideal.mem_span_singleton.mpr (h n))
  exact absurd (key (x.valuation + 1)) (by omega)

/-- `p` is nonzero in `ℤ_[p]`, which has characteristic `0` (PROVEN). -/
lemma padicInt_p_ne_zero (p : ℕ) [hp : Fact p.Prime] : (p : ℤ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr hp.out.ne_zero

/-- **Specialisation of divisors along the smooth proper model over `ℤ_p`.**

`sp` sends a closed point of `X_ℚ` to its specialisation on `X_𝔽ₚ`: the closure of the
point in `𝒳` is finite flat over `ℤ_p`, and `sp` records the effective divisor it cuts on
the special fibre.  The two axioms are what the model provides and what the descent to
`Pic` needs:

* `sp_pt`: the closure of a `ℚ`-rational point is a SECTION of `𝒳 → Spec ℤ_p`, so it meets
  the special fibre in the single `𝔽ₚ`-point `redPt P` — the integral weighted-projective
  coordinates of `exists_int_coords` ARE that section;
* `sp_princ`: the closure of `div g` is `div_𝒳(g)` minus a multiple of the special fibre,
  and the special fibre is `div_𝒳(p)`, so the whole thing restricts to a principal divisor.

Nothing here mentions the formal group; that is the other half of `SmoothModel`. -/
structure Specialisation {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (p : ℕ) [Fact p.Prime]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)) where
  /-- specialisation of divisors, `Div(X_ℚ) → Div(X_𝔽ₚ)` -/
  sp : D.Divisors →+ D'.Divisors
  /-- a rational point specialises to its coordinate-wise reduction -/
  sp_pt : ∀ P : Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ,
      sp (Finsupp.single (D.pt P) 1) = Finsupp.single (D'.pt (redPt c₀ c₁ c₂ c₃ c₄ c₅ P)) 1
  /-- a principal divisor specialises to a principal divisor -/
  sp_princ : ∀ z ∈ D.princ, sp z ∈ D'.princ

namespace Specialisation

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime]
  {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ} {D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)}

/-- **PROVEN: `sp` respects the relation defining `Pic`.**  `picRel` is generated by the
principal divisors, handled by `sp_princ`, together with the class of the base point, and
`redPt` fixes `∞₊` — it is `Sum.inr` on the infinite summand by definition — so `sp_pt`
sends `[∞₊]` to `[∞₊]`.  This is exactly why the base point had to be one that reduction
preserves. -/
lemma picRel_le_comap (S : Specialisation p D D') :
    D.picRel ≤ AddSubgroup.comap S.sp D'.picRel := by
  refine sup_le (fun z hz => ?_) ?_
  · exact (le_sup_left : D'.princ ≤ D'.picRel) (S.sp_princ z hz)
  · rw [AddSubgroup.zmultiples_le]
    have hred : redPt c₀ c₁ c₂ c₃ c₄ c₅ (p := p) (PlaceData.infPlus) = PlaceData.infPlus := rfl
    show S.sp (Finsupp.single (D.pt PlaceData.infPlus) 1) ∈ D'.picRel
    rw [S.sp_pt, hred]
    exact (le_sup_right : AddSubgroup.zmultiples _ ≤ D'.picRel) (AddSubgroup.mem_zmultiples _)

/-- **Reduction of divisor CLASSES** (PROVEN, not postulated): `sp` descends to the
quotient by `picRel`. -/
noncomputable def red (S : Specialisation p D D') : D.Pic →+ D'.Pic :=
  QuotientAddGroup.map D.picRel D'.picRel S.sp S.picRel_le_comap

/-- `red` on the class of a divisor is the class of its specialisation (PROVEN, `rfl`). -/
lemma red_mk (S : Specialisation p D D') (z : D.Divisors) :
    S.red (QuotientAddGroup.mk z) = QuotientAddGroup.mk (S.sp z) := rfl

/-- **PROVEN: the compatibility square with the concrete reduction of points.**  This is
`ReductionFiltration.red_aj`, and it comes straight from `sp_pt`. -/
lemma red_aj (S : Specialisation p D D') (P : Pt c₀ c₁ c₂ c₃ c₄ c₅ ℚ) :
    S.red (D.aj P) = D'.aj (redPt c₀ c₁ c₂ c₃ c₄ c₅ P) := by
  show QuotientAddGroup.mk (S.sp (Finsupp.single (D.pt P) 1)) = _
  rw [S.sp_pt]
  rfl

end Specialisation

/-- **The smooth `ℤ_p`-model of the curve, as far as this file needs it**: specialisation of
divisors together with the formal logarithm of the Jacobian on the kernel of reduction.

See the section note above for why the two are bundled and why `log` is only asked to be
injective.  `log_mem_one` is the statement that the logarithm of an element of
`Ĵ(pℤ_p) = ker red` lies in `(pℤ_p)²`, which is what makes `filt 1 = ker red` below. -/
structure SmoothModel {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (p : ℕ) [Fact p.Prime]
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)) where
  /-- specialisation of divisors along the model, which gives `red` -/
  spec : Specialisation p D D'
  /-- the formal logarithm of the Jacobian, on the kernel of reduction -/
  log : ↥spec.red.ker →+ ℤ_[p] × ℤ_[p]
  /-- it is injective — this is where `p ≠ 2`, i.e. `e < p − 1`, is used -/
  log_injective : Function.Injective log
  /-- and it lands in `(pℤ_p)²`, the first step of the filtration -/
  log_mem_one : ∀ z : ↥spec.red.ker, log z ∈ padicLevel p 1

namespace SmoothModel

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime]
  {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ} {D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)}

/-- **The formal-group filtration**, `filt n = J(ℚ) ∩ Ĵ(pⁿℤ_p)`, defined as the elements of
`ker red` whose logarithm is divisible by `pⁿ` in both coordinates. -/
noncomputable def filt (M : SmoothModel p D D') (n : ℕ) : AddSubgroup D.Pic :=
  ((padicLevel p n).comap M.log).map M.spec.red.ker.subtype

/-- Membership in `filt n`, unfolded (PROVEN). -/
lemma mem_filt (M : SmoothModel p D D') (n : ℕ) (z : D.Pic) :
    z ∈ M.filt n ↔ ∃ h : z ∈ M.spec.red.ker, M.log ⟨z, h⟩ ∈ padicLevel p n := by
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := AddSubgroup.mem_map.mp hz
    subst hwz
    exact ⟨w.2, hw⟩
  · rintro ⟨h, hz⟩
    exact AddSubgroup.mem_map.mpr ⟨⟨z, h⟩, hz, rfl⟩

/-- **The logarithm turns multiplication by `p` into multiplication by `p`** (PROVEN) — it
is a homomorphism, and `p • ⟨z, h⟩` is `⟨p • z, _⟩` in the kernel. -/
lemma log_smul (M : SmoothModel p D D') {z : D.Pic} (h : z ∈ M.spec.red.ker)
    (hpz : p • z ∈ M.spec.red.ker) :
    M.log ⟨p • z, hpz⟩ = (p : ℤ_[p]) • M.log ⟨z, h⟩ := by
  have he : (⟨p • z, hpz⟩ : ↥M.spec.red.ker) = p • ⟨z, h⟩ := Subtype.ext rfl
  rw [he, map_nsmul]
  ext <;> simp [nsmul_eq_mul]

/-- **PROVEN: a `SmoothModel` yields a `ReductionFiltration`.**

All four filtration axioms are divisibility statements about the logarithm:

* `filt_one` is `log_mem_one`;
* `filt_antitone` is `pᵐ ∣ pⁿ` for `m ≤ n`;
* `filt_separated` is `padicInt_eq_zero_of_forall_pow_dvd` plus injectivity of `log`;
* `smul_p_mem` is `pⁿ ∣ a → pⁿ⁺¹ ∣ p·a`, and `smul_p_notMem` is its converse, cancelling
  the nonzero `p` in the domain `ℤ_[p]`.  The last is the sharp statement that
  multiplication by `p` raises the level by EXACTLY one, and it is what
  `ReductionFiltration.nsmul_ne_zero_of_notMem` consumes. -/
noncomputable def toReductionFiltration (M : SmoothModel p D D') :
    ReductionFiltration p D D' where
  red := M.spec.red
  red_aj := M.spec.red_aj
  filt := M.filt
  filt_one := by
    refine le_antisymm (fun z hz => ((M.mem_filt 1 z).mp hz).fst) (fun z hz => ?_)
    exact (M.mem_filt 1 z).mpr ⟨hz, M.log_mem_one ⟨z, hz⟩⟩
  filt_antitone := by
    intro m n hmn z hz
    obtain ⟨h, h1, h2⟩ := (M.mem_filt n z).mp hz
    exact (M.mem_filt m z).mpr
      ⟨h, dvd_trans (pow_dvd_pow _ hmn) h1, dvd_trans (pow_dvd_pow _ hmn) h2⟩
  filt_separated := by
    intro z hz
    obtain ⟨h, -⟩ := (M.mem_filt 1 z).mp (hz 1)
    have key : ∀ n : ℕ, M.log ⟨z, h⟩ ∈ padicLevel p n := by
      intro n
      obtain ⟨h', hn⟩ := (M.mem_filt n z).mp (hz n)
      -- `h'` and `h` are proofs of the same proposition, hence definitionally equal
      exact hn
    have h0 : M.log ⟨z, h⟩ = 0 :=
      Prod.ext (padicInt_eq_zero_of_forall_pow_dvd _ fun n => (key n).1)
        (padicInt_eq_zero_of_forall_pow_dvd _ fun n => (key n).2)
    have hzz : (⟨z, h⟩ : ↥M.spec.red.ker) = 0 := by
      apply M.log_injective
      rw [h0, map_zero]
    exact congrArg Subtype.val hzz
  smul_p_mem := by
    intro n _ z hz
    obtain ⟨h, h1, h2⟩ := (M.mem_filt n z).mp hz
    have hpz : p • z ∈ M.spec.red.ker := AddSubgroup.nsmul_mem _ h p
    refine (M.mem_filt (n + 1) (p • z)).mpr ⟨hpz, ?_, ?_⟩
    · rw [M.log_smul h hpz]
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, by simp only [Prod.smul_fst, smul_eq_mul, hc]; ring⟩
    · rw [M.log_smul h hpz]
      obtain ⟨c, hc⟩ := h2
      exact ⟨c, by simp only [Prod.smul_snd, smul_eq_mul, hc]; ring⟩
  smul_p_notMem := by
    intro n _ z hz hout hcon
    obtain ⟨h, -, -⟩ := (M.mem_filt n z).mp hz
    obtain ⟨hpz, k1, k2⟩ := (M.mem_filt (n + 2) (p • z)).mp hcon
    rw [M.log_smul h hpz] at k1 k2
    apply hout
    refine (M.mem_filt (n + 1) z).mpr ⟨h, ?_, ?_⟩
    · refine (mul_dvd_mul_iff_left (padicInt_p_ne_zero p)).mp ?_
      have he : (p : ℤ_[p]) * (p : ℤ_[p]) ^ (n + 1) = (p : ℤ_[p]) ^ (n + 2) := by ring
      rw [he]
      simpa only [Prod.smul_fst, smul_eq_mul] using k1
    · refine (mul_dvd_mul_iff_left (padicInt_p_ne_zero p)).mp ?_
      have he : (p : ℤ_[p]) * (p : ℤ_[p]) ^ (n + 1) = (p : ℤ_[p]) ^ (n + 2) := by ring
      rw [he]
      simpa only [Prod.smul_snd, smul_eq_mul] using k2

end SmoothModel

/-- **LEAF (obligation 3a): the smooth `ℤ_p`-model exists, with its specialisation of
divisors and the formal logarithm of its Jacobian.**

This is what remains of `exists_reductionFiltration` after the second cut of 2026-07-28; see
the section note above for why the two halves are bundled.  What has to be built:

* the smooth proper model `𝒳/ℤ_p` of `y² = f(x)`.  `hsep` says the sextic is separable mod
  `p`, i.e. `disc f ∈ ℤ_p^×`, and `hp` says `2 ∈ ℤ_p^×`, so the weighted-projective model of
  the file is already smooth over `ℤ_p` — no change of model is needed, which is why the
  integral coordinates of `exists_int_coords` are literally the `ℤ_p`-points;
* specialisation of divisors: the closure of a closed point of `X_ℚ` is finite flat over
  `ℤ_p` and cuts an effective divisor on `X_𝔽ₚ`.  `sp_pt` is that a rational point's
  closure is a section; `sp_princ` is that the vertical part of `div_𝒳(g)` is a multiple of
  `div_𝒳(p)`;
* the formal group `Ĵ` of the Jacobian along the identity section, `ker red ⊆ Ĵ(pℤ_p)`, and
  its logarithm.  For `e = 1 < p − 1`, i.e. `p ≠ 2`, `log = Σ (−1)ⁿ⁺¹ Tⁿ/n`-style series
  converge on `pℤ_p` and `log` is an isomorphism `Ĵ(pℤ_p) ≅ (pℤ_p)^g`, `g = 2`; only its
  injectivity and the containment `log(ker red) ⊆ (pℤ_p)²` are asked for here.  This is
  Silverman *AEC* IV.6.4 / VII.3.2 for a Jacobian rather than an elliptic curve.

**`hp : p ≠ 2` is load-bearing and not decorative.**  At `p = 2` with `e = 1` the series
does not converge on `Ĵ(2ℤ_2)`, and the conclusion genuinely fails: `Ĵ(2ℤ_2)` can contain
`2`-torsion, so no injective homomorphism into the torsion-free `ℤ_2²` exists.

This leaf is generic in the sextic and the prime, so proving it closes obligation 3 at both
levels at once.

## AXIS-BY-AXIS AUDIT 2026-07-28: this leaf STAYS ATOMIC

Faithfulness first, then each candidate cut and why it is not taken.

**FAITHFUL, and two candidate refutations closed.**

* *Rank.*  `ker red` sits inside `J(ℚ)`, whose rank is unbounded over the sextics this leaf
  quantifies over, while the target `ℤ_[p] × ℤ_[p]` has `ℤ_p`-rank `2`.  That is not a
  contradiction: `log` is injective on ALL of `Ĵ(pℤ_p)` (it is an isomorphism onto
  `(pℤ_p)²` for `e < p − 1`), and `ℤ_[p]` has INFINITE rank as an abelian group — `ℚ_p` is
  uncountable and `ℚ` is countable, so `ℚ_p` is an infinite-dimensional `ℚ`-vector space and
  `ℤ^k ↪ ℤ_[p]` for every finite `k`.  A positive-rank Jacobian does not refute the leaf.
* *`sp_pt` at a point with `p ∣ x.den`.*  Such a point's closure meets the special fibre at
  infinity, and `redPt` agrees: `redTriple` branches on `(b : ZMod p) ≠ 0` and returns
  `Sum.inr (decide (t / a³ = 1))` in the divisible case.  So `sp_pt` is not silently false
  on the points where the naive affine reduction would be.

**Axis 1 — split `Specialisation` off from `log` (`∀ S, ∃ log …`).  NOT TAKEN.**  The
section note above forbids it; here is the witness that `Specialisation` really is not
rigid.  If `λ : D.Divisors →+ ℤ` kills `D.princ` and kills `single (D.pt P) 1` for every
rational `P`, then for any `w : D'.Divisors` the map `sp + λ(·) • w` satisfies `sp_pt` and
`sp_princ` again.  A nonzero such `λ` exists exactly when `Pic⁰(X_ℚ)` modulo the subgroup
generated by the classes of rational points has positive rank — which happens already for
`rank J(ℚ) ≥ 2` with `X(ℚ)` the two points at infinity, since those generate a subgroup of
rank at most `1`.  Honesty about what this witness does and does not show:
it does NOT refute the split, because `λ` kills torsion (`ℤ` is torsion-free), so the junk
`red` has the same kernel torsion as the true one; and adding preservation of degree to
`Specialisation` would kill every member with `deg'(w) ≠ 0`, since `deg' (sp' v) = deg v`
forces `λ(v) · deg'(w) = 0`.  The decisive objection is a different one, and it survives any
amount of such pinning: the second half's prover, handed an arbitrary `S`, would have to
RECOVER the model from the axioms before it could produce a logarithm.  That is strictly
more work than the bundled leaf, not less, so this cut cannot pay even where it is sound.

**Axis 2 — replace `log` by "`ker red` is torsion-free", still in one existential.  NOT
TAKEN, and here is the honest accounting for the cut that was.**  Modulo the Mordell–Weil
already in this file (`fg_pic`, over `exists_descentHeight_pic` and
`finite_quotient_psmul_pic`) the two are EQUIVALENT: `⇒` because subgroups of
`ℤ_[p] × ℤ_[p]` are torsion-free, `⇐` because `ker red ≤ D.Pic` is then finitely generated,
hence free of some finite rank `k` when torsion-free, and `ℤ^k ↪ ℤ_[p] × ℤ_[p]` by the rank
remark above.  (`fg_pic` wants separability over `ℚ`, which `hsep` gives: the resultant of
`f` and `f'` is an integer, nonzero mod `p`.)  So this leaf is, modulo Mordell–Weil,
`exists_reduction` with `red` additionally required to lift to the divisor level: the second
cut of 2026-07-28 did NOT make the remaining obligation smaller.  What it bought is that the
group theory of Silverman *AEC* VII.3.2 — a separated filtration with `p`-killed graded
pieces on which `[p]` shifts the level by exactly one has no torsion — is now machine-checked
instead of asserted.  Recorded so that nobody re-cuts this leaf expecting a reduction in
content.

**Axis 3 — weaken to "`ker red` is a `p`-group", dropping `smul_p_notMem` and with it
`hp`.  REJECTED.**  It is genuinely weaker mathematics: the kernel of reduction is pro-`p`
for EVERY `p`, needing no convergence, and `filt_one`, `filt_separated` and `smul_p_mem`
alone already give "no prime-to-`p` torsion" by the same Bézout step used in
`nsmul_ne_zero_of_notMem`.  But it discharges the consumer only together with
`gcd(#J(ℚ), p) = 1`, i.e. with `#J(ℚ)` known exactly (`21` and `19`) — a strictly harder
arithmetic input than the finiteness this file proves.  That is the same reason
`card_coprime` is deliberately absent from `JacobianPackage`; do not "simplify" this way.

**`log_mem_one` is redundant** (noted, not removed): reindexing `filt` by
`padicLevel p (n − 1)` gives `filt 1 = ker red` from `padicLevel p 0 = ⊤`, and the four
remaining axioms shift with it.  It is kept because the true logarithm satisfies it for
free — `log (Ĵ(pℤ_p)) = (pℤ_p)²` — and because it is what makes `filt n` mean
`J(ℚ) ∩ Ĵ(pⁿℤ_p)` on the nose.

**And `sp` is not a way around building the model.**  `D.Divisors` is free on `D.Places`, so
any `ψ : D.Pic →+ D'.Pic` with `ψ (D.aj P) = D'.aj (redPt P)` lifts basis-wise to a map
satisfying `sp_pt`, and representatives can be corrected to the right degree by multiples of
`single (D'.pt infPlus) 1`, which is `0` in `D'.Pic` — so, given the degree maps of
`exists_degreeMap`, producing a `Specialisation` and producing a `redPt`-compatible
reduction homomorphism are interchangeable.  The content is the model and its formal group;
there is no cheaper packaging of it. -/
theorem exists_smoothModel {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p))
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)).Separable) :
    Nonempty (SmoothModel p D D') := sorry

/-- **LEAF (obligation 3a), now PROVEN from `exists_smoothModel` and
`SmoothModel.toReductionFiltration`.**

`red` is the descent of the divisor specialisation to `Pic`, and the four filtration axioms
are divisibility facts about the formal logarithm; see the section note above. -/
theorem exists_reductionFiltration {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) (D' : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p))
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (ZMod p)).Separable) :
    Nonempty (ReductionFiltration p D D') :=
  (exists_smoothModel hp D D' hsep).elim fun M => ⟨M.toReductionFiltration⟩

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

The bridge is nevertheless still **not cheap**, for a different and much better reason:
`D.Pic ≃+ RelPoint jstr (𝟙 SpecQ)` requires first CONSTRUCTING the abelian scheme `J` for
the hyperelliptic curve and then proving that the divisor-theoretic `Pic⁰` computes its
rational points — a comparison theorem, not an import.  That would replace two leaves by
one substantially harder one, plus a 50k-line module in this file's own build cone.  So the
right reading is: the bridge is a *scheme-theory* obligation, not an *import* obligation,
and it should be revisited when the Néron/abelian-scheme layer for this curve exists.

**Both leaves below were cut on 2026-07-28** and are now PROVEN assemblies:
`exists_descentHeight_pic` over `exists_cubeModel_pic` (all analysis removed), and
`finite_quotient_psmul_pic` over `exists_geomPic`, `geomPic_bc_injective`,
`geomPic_descent`, `geomPic_divisible` and `finite_kummerCochains_pic` (all cohomology
removed) — of which `geomPic_divisible` has since been proven in turn, over the
single-place, single-prime leaf `geomPic_divisible_place` (2026-07-30).  The `X0` siblings
remain the ones not to duplicate.
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

/-- **LEAF (Mordell–Weil, geometric half, ANALYSIS-FREE): `Pic⁰(X_ℚ)` embeds in projective
space over `ℚ` by a symmetric very ample bundle satisfying the theorem of the cube**, for
every separable monic sextic.

`Fermat.CubeModel` (`Fermat/FLT/Mathlib/NumberTheory/ProjectiveHeight.lean`) asks for
exactly three things and no more: homogeneous coordinates `coords : Pic⁰(X_ℚ) → ℚ^n`,
nonzero and injective up to scaling; the forms of the **theorem of the cube**, of bidegree
`(2,2)`, computing the Segre product of `coords (P + Q)` and `coords (P − Q)` from
`(coords P, coords Q)`; and homogeneous generators of the ideal of the Segre image together
with the statement that the cube forms have no common zero on it.

**WHY THIS CUT (2026-07-28), and what it removes.**  The consumer
`exists_descentHeight_pic` above is an `∃ C : ℝ` statement about a height — the
quasi-parallelogram law, one-sided quadraticity, and Northcott finiteness.  None of that is
what algebraic geometry produces, and it is *already proven* generically:

* `Fermat.CubeModel.nonempty_cubeEmbedding` manufactures the Nullstellensatz certificate
  from the geometric non-vanishing;
* `Fermat.CubeEmbedding.toProjectiveHeightSource` supplies the approximate parallelogram
  law from the theorem of the cube, over `Mathlib/NumberTheory/Height/MvPolynomial.lean`;
* `Fermat.ProjectiveHeightSource.toWeilHeight` supplies **Northcott** from
  `Mathlib`'s Northcott property for `ℚ`;
* `Fermat.ParallelogramHeight.toDescentHeight` supplies `translate`, `double` and `m = 2`.

So after this cut the leaf contains **no analysis at all** — no `ℝ`, no logarithm, no
finiteness of bounded-height sets.  It is the same cut `X0.lean` uses at
`exists_cubeModel_of_abelianScheme`, and the assembly above is compiler-checked.

**TRUE and classical.**  The sextic is separable of degree `6`, so the smooth projective
model is a curve of genus `2` and `Pic⁰` is its Jacobian, an abelian surface over `ℚ` with
a rational point.  Take `Θ` the theta divisor; `2Θ` is symmetric and ample, and `4Θ` is
symmetric and *very* ample (Lefschetz), embedding `J` in `ℙ^{15}` — so `dim = 16` works.
The theorem of the cube (Mumford, *Abelian Varieties* §6; Hindry–Silverman
*Diophantine Geometry* B.5.1) is `σ* L ⊗ δ* L ≅ p₁* L² ⊗ p₂* L²` on `J × J`, which in
coordinates is exactly `cube` / `cube_eval`.

**Do not cut this further in COORDINATES.**  The obvious next split — "any symmetric
projective embedding satisfies the theorem of the cube" — is FALSE, and the
counterexample is recorded on `CubeModel` itself: `E(ℚ) ≅ ℤ` with `coords n = (1, n³, n⁶)`
is injective up to scaling and `[−1]`-symmetric, and its height `6 log|n| + O(1)` violates
quadraticity. Any faithful further cut must be made at the level of the invertible sheaf
and its global sections, not in coordinates.

**Not vacuous.**  `CubeModel` on a FINITE group is cheap (`dim = 1`, `coords = 1`), so this
leaf carries no content when `Pic⁰(X_ℚ)` is finite — which is correct rather than a defect,
since a finite group is finitely generated and the consumer's conclusion holds anyway.  It
is the infinite (positive-rank) case that the leaf is for, and there `injective_of_smul`
plus `cube_eval` force a genuine projective embedding of the Jacobian. -/
theorem exists_cubeModel_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    Nonempty (CubeModel D.Pic) := sorry

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
proof produces (`Fermat.ParallelogramHeight.toDescentHeight` supplies `2`).

**Not vacuous, and not the conclusion in disguise.**  A `DescentHeight` on an infinite
group is a real object — it exists on `E(ℚ)` of any rank — and it says nothing on its own
about finite generation; the descent theorem needs the arithmetic half too.

**Do not prove this twice.**  `Fermat/FLT/ModularCurve/X0.lean`'s
`exists_cubeModel_of_abelianScheme` (feeding its PROVEN
`exists_descentHeight_of_abelianScheme`) is the same obligation for a scheme-theoretic
abelian variety; see the section docstring for the bridge that would make one of the two
redundant.

**NO LONGER A LEAF (2026-07-28).**  It is PROVEN below over `exists_cubeModel_pic`, which
is this statement with every trace of analysis removed; see that docstring. -/
theorem exists_descentHeight_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    Nonempty (DescentHeight D.Pic) := by
  obtain ⟨cm⟩ := exists_cubeModel_pic D hsep
  obtain ⟨ce⟩ := cm.nonempty_cubeEmbedding
  exact ⟨ce.toProjectiveHeightSource.toWeilHeight.toDescentHeight⟩

/-!
### The geometric Picard group and its Galois action

Weak Mordell–Weil is not a statement one attacks about `Pic⁰(X_ℚ) / p·Pic⁰(X_ℚ)` directly.
The classical proof (Silverman *AEC* VIII.1) passes to `Pic⁰(X_ℚ̄)`, where `[p]` is
surjective, and turns a class into a **Kummer cochain** on `Gal(ℚ̄/ℚ)`.  That reduction is
pure algebra and is PROVEN generically as `Fermat.finite_quotient_nsmul_of_kummerCochains`
(`Fermat/FLT/Mathlib/GroupTheory/Descent.lean`): no cohomology theory, no continuity, not
even a group structure on `Γ`.  What it consumes is a `Γ`-module `M`, an injection
`ι : Pic⁰(X_ℚ) → M` whose image is the fixed part, divisibility of `ι '' Pic⁰(X_ℚ)` in `M`,
and finiteness of the set of cochains.

`GeomPic` below supplies `M`.  **It is DATA that is PINNED, not an existentially quantified
package of properties** — the idiom this file already uses for `PlaceData` itself, and the
reason the four leaves after it may be safely `∀`-quantified over `gp`:

* `Dbar` is pinned up to isomorphism by `PlaceData`'s own axioms (section docstring above);
* `emb` is pinned by `emb_algebraMap`, `emb_xx`, `emb_yy` together with `PlaceData.gen`:
  `D.F = ℚ(xx, yy)`, so a ring map determined on `ℚ`, `xx` and `yy` is determined;
* `below` is pinned by `ord_emb` together with `D.ord_injective`: `below w` is *the* place
  whose valuation is `ord_w ∘ emb`;
* `fieldAct σ` is pinned the same way `emb` is — semilinear over `σ` on constants, fixing
  `emb '' D.F`, hence fixing `xx` and `yy`, hence determined on `Dbar.F = ℚ̄(xx, yy)`;
* `placeAct σ` is pinned by `ord_placeAct` together with `Dbar.ord_injective`.

Consequently `bcDiv`, `bc`, `divAct` and `act` below are **definitions**, and the four
obligations are model-independent facts about the curve.  This matters: the naive cut, in
which `act` is a field constrained only by "the fixed points are the image", is UNSOUND —
`act σ = 0` makes the descent field vacuously true (its hypothesis forces `y = 0`), and
then the cochain-finiteness sibling becomes FALSE, since the cochains `σ ↦ −Q` range over
all `p`-division points of `bc '' Pic⁰(X_ℚ)`.  Pinning `act` through `fieldAct` is exactly
what closes that hole, and `act_bc` — PROVEN below — is the compiler-checked witness that
the pinning does force the image into the invariants.

**Emptiness is not a hiding place either.**  If `GeomPic` were over-constrained and empty,
the three `∀`-leaves would be vacuous — but so would `exists_geomPic`, which is itself a
named leaf and is FALSE in that case.  Nothing is discharged by an empty structure.

The only field asserting something that is not forced is `below_infPlus`, and it is true
for the concrete reason the whole layer is stated as it is: `∞₊` is a `ℚ`-rational point of
degree `1`, so exactly one geometric place lies over it, unramified.
-/

/-- The absolute Galois group of `ℚ`, as the automorphisms of a fixed algebraic closure.

`Fermat.finite_quotient_nsmul_of_kummerCochains` deliberately does not ask this to be a
group — only a type indexing the action — so no profinite or continuous-cochain machinery
is on the path. -/
abbrev QbarGal : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- **The divisor theory of the curve over `ℚ̄`, together with the Galois action and the
base-change map from `ℚ`.**

See the section docstring immediately above for why every field is pinned, and why that is
what makes the four leaves below sound as `∀`-statements. -/
structure GeomPic (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) where
  /-- the SAME curve, over an algebraic closure of `ℚ` -/
  Dbar : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (AlgebraicClosure ℚ)
  /-- the inclusion of function fields `F ↪ F̄` -/
  emb : D.F →+* Dbar.F
  /-- `emb` is a `ℚ`-algebra map into `F̄` -/
  emb_algebraMap : ∀ a : ℚ, emb (algebraMap ℚ D.F a)
      = algebraMap (AlgebraicClosure ℚ) Dbar.F (algebraMap ℚ (AlgebraicClosure ℚ) a)
  /-- it sends the abscissa to the abscissa -/
  emb_xx : emb D.xx = Dbar.xx
  /-- and the ordinate to the ordinate; with `emb_algebraMap` and `PlaceData.gen` this
  determines `emb` -/
  emb_yy : emb D.yy = Dbar.yy
  /-- the place of `F` below a geometric place -/
  below : Dbar.Places → D.Places
  /-- **the constant field extension is unramified**: `ord_w ∘ emb = ord_{below w}` on the
  nose, with no ramification index.  This is what pins `below`, via `D.ord_injective` -/
  ord_emb : ∀ (w : Dbar.Places) (g : D.F), g ≠ 0 → Dbar.ord w (emb g) = D.ord (below w) g
  /-- a place of `F` of degree `d` has exactly `d` geometric places above it; only
  finiteness is used, and it is what makes base change of divisors well defined -/
  below_finite : ∀ v : D.Places, {w : Dbar.Places | below w = v}.Finite
  /-- **the rational base point has exactly one geometric place above it**, because `∞₊`
  has degree `1`.  This is what makes `bcDiv` respect `picRel` and what makes the Galois
  action fix the base point -/
  below_infPlus : ∀ w : Dbar.Places,
      below w = D.pt PlaceData.infPlus ↔ w = Dbar.pt PlaceData.infPlus
  /-- the action of `σ` on the geometric function field, semilinear over `σ` -/
  fieldAct : QbarGal → Dbar.F ≃+* Dbar.F
  /-- semilinearity: on constants, `fieldAct σ` IS `σ`.  This is the field that forbids
  the junk action `fieldAct σ = id`, and with it the junk `act σ = 0` -/
  fieldAct_algebraMap : ∀ (σ : QbarGal) (a : AlgebraicClosure ℚ),
      fieldAct σ (algebraMap (AlgebraicClosure ℚ) Dbar.F a)
        = algebraMap (AlgebraicClosure ℚ) Dbar.F (σ a)
  /-- Galois fixes the rational function field pointwise; with the previous field this
  determines `fieldAct σ` on `Dbar.F = ℚ̄(xx, yy)` -/
  fieldAct_emb : ∀ (σ : QbarGal) (g : D.F), fieldAct σ (emb g) = emb g
  /-- the induced permutation of geometric places -/
  placeAct : QbarGal → Dbar.Places ≃ Dbar.Places
  /-- which is pinned by this compatibility together with `Dbar.ord_injective` -/
  ord_placeAct : ∀ (σ : QbarGal) (v : Dbar.Places) (g : Dbar.F),
      Dbar.ord (placeAct σ v) (fieldAct σ g) = Dbar.ord v g

namespace GeomPic

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
  (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D)

/-- the finitely many geometric places above `v` (PROVEN well defined by `below_finite`) -/
noncomputable def fiber (v : D.Places) : Finset gp.Dbar.Places :=
  (gp.below_finite v).toFinset

lemma mem_fiber {v : D.Places} {w : gp.Dbar.Places} : w ∈ gp.fiber v ↔ gp.below w = v := by
  simp [fiber, Set.Finite.mem_toFinset]

open scoped Classical in
/-- **Base change of divisors** (PROVEN well defined): the pullback of `Σ n_v · v` is
`Σ n_v · Σ_{w | v} w`, which at a geometric place `w` reads off the coefficient at
`below w`.  Finitely supported because each fibre of `below` is finite. -/
noncomputable def bcDiv : D.Divisors →+ gp.Dbar.Divisors where
  toFun δ := Finsupp.onFinset (δ.support.biUnion gp.fiber) (fun w => δ (gp.below w)) (by
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨gp.below w, Finsupp.mem_support_iff.mpr hw,
      gp.mem_fiber.mpr rfl⟩)
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp

@[simp] lemma bcDiv_apply (δ : D.Divisors) (w : gp.Dbar.Places) :
    gp.bcDiv δ w = δ (gp.below w) := by
  simp [bcDiv]

lemma emb_injective : Function.Injective gp.emb := gp.emb.injective

/-- **Base change takes the divisor of `g` to the divisor of `emb g`** (PROVEN) — this is
`ord_emb` read at every geometric place at once. -/
lemma bcDiv_divisor (g : D.F) : gp.bcDiv (D.divisor g) = gp.Dbar.divisor (gp.emb g) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp [PlaceData.divisor]
  · have hg' : gp.emb g ≠ 0 := fun h => hg (gp.emb_injective (by simpa using h))
    ext w
    rw [bcDiv_apply]
    simp only [PlaceData.divisor, dif_neg hg, dif_neg hg', Finsupp.onFinset_apply]
    exact (gp.ord_emb w g hg).symm

/-- **Base change fixes the class of the base point** (PROVEN from `below_infPlus`). -/
lemma bcDiv_single_infPlus :
    gp.bcDiv (Finsupp.single (D.pt PlaceData.infPlus) 1)
      = Finsupp.single (gp.Dbar.pt PlaceData.infPlus) 1 := by
  ext w
  rw [bcDiv_apply]
  by_cases h : w = gp.Dbar.pt PlaceData.infPlus
  · subst h
    rw [(gp.below_infPlus _).mpr rfl, Finsupp.single_eq_same, Finsupp.single_eq_same]
  · have hR : gp.Dbar.pt PlaceData.infPlus ≠ w := fun hc => h hc.symm
    have hL : D.pt PlaceData.infPlus ≠ gp.below w :=
      fun hc => h ((gp.below_infPlus w).mp hc.symm)
    rw [Finsupp.single_eq_of_ne hL.symm, Finsupp.single_eq_of_ne hR.symm]

/-- **Base change respects `picRel`** (PROVEN), so it descends to `Pic⁰`. -/
lemma bcDiv_picRel : D.picRel ≤ (gp.Dbar.picRel).comap gp.bcDiv := by
  refine sup_le ?_ ?_
  · refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨g, rfl⟩
    show gp.bcDiv (D.divisor g) ∈ gp.Dbar.picRel
    rw [bcDiv_divisor]
    exact AddSubgroup.mem_sup_left (AddSubgroup.subset_closure ⟨gp.emb g, rfl⟩)
  · rw [AddSubgroup.zmultiples_le]
    show gp.bcDiv (Finsupp.single (D.pt PlaceData.infPlus) 1) ∈ gp.Dbar.picRel
    rw [bcDiv_single_infPlus]
    exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

/-- **Base change on `Pic⁰`**, `Pic⁰(X_ℚ) → Pic⁰(X_ℚ̄)` (PROVEN well defined). -/
noncomputable def bc : D.Pic →+ gp.Dbar.Pic :=
  QuotientAddGroup.map D.picRel gp.Dbar.picRel gp.bcDiv gp.bcDiv_picRel

/-- The action of `σ` on geometric divisors: permute the places by `placeAct σ`. -/
noncomputable def divAct (σ : QbarGal) : gp.Dbar.Divisors →+ gp.Dbar.Divisors where
  toFun δ := Finsupp.equivMapDomain (gp.placeAct σ) δ
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp

@[simp] lemma divAct_apply (σ : QbarGal) (δ : gp.Dbar.Divisors) (w : gp.Dbar.Places) :
    gp.divAct σ δ w = δ ((gp.placeAct σ).symm w) := by
  simp [divAct]

/-- **`σ` carries the divisor of `g` to the divisor of `fieldAct σ g`** (PROVEN) — this is
`ord_placeAct` read at every place at once. -/
lemma divAct_divisor (σ : QbarGal) (g : gp.Dbar.F) :
    gp.divAct σ (gp.Dbar.divisor g) = gp.Dbar.divisor (gp.fieldAct σ g) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp [PlaceData.divisor]
  · have hg' : gp.fieldAct σ g ≠ 0 := by
      intro h
      exact hg ((gp.fieldAct σ).injective (h.trans (map_zero (gp.fieldAct σ)).symm))
    ext w
    rw [divAct_apply]
    simp only [PlaceData.divisor, dif_neg hg, dif_neg hg', Finsupp.onFinset_apply]
    have := gp.ord_placeAct σ ((gp.placeAct σ).symm w) g
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **The Galois action does not move the place below** (PROVEN): `σ` fixes `F` pointwise,
so `ord_{σw} ∘ emb = ord_w ∘ emb`, and `D.ord_injective` finishes. -/
lemma below_placeAct (σ : QbarGal) (w : gp.Dbar.Places) :
    gp.below (gp.placeAct σ w) = gp.below w := by
  refine D.ord_injective (funext fun g => ?_)
  rcases eq_or_ne g 0 with rfl | hg
  · rw [D.ord_zero, D.ord_zero]
  · calc D.ord (gp.below (gp.placeAct σ w)) g
        = gp.Dbar.ord (gp.placeAct σ w) (gp.emb g) := (gp.ord_emb _ g hg).symm
      _ = gp.Dbar.ord (gp.placeAct σ w) (gp.fieldAct σ (gp.emb g)) := by rw [gp.fieldAct_emb]
      _ = gp.Dbar.ord w (gp.emb g) := gp.ord_placeAct σ w (gp.emb g)
      _ = D.ord (gp.below w) g := gp.ord_emb w g hg

/-- **Galois fixes the base point** (PROVEN): it is the unique geometric place over
`D.pt ∞₊`, and `below_placeAct` says `σ` stays in that fibre. -/
lemma placeAct_infPlus (σ : QbarGal) :
    gp.placeAct σ (gp.Dbar.pt PlaceData.infPlus) = gp.Dbar.pt PlaceData.infPlus := by
  refine (gp.below_infPlus _).mp ?_
  rw [gp.below_placeAct]
  exact (gp.below_infPlus _).mpr rfl

lemma divAct_single_infPlus (σ : QbarGal) :
    gp.divAct σ (Finsupp.single (gp.Dbar.pt PlaceData.infPlus) 1)
      = Finsupp.single (gp.Dbar.pt PlaceData.infPlus) 1 := by
  show Finsupp.equivMapDomain (gp.placeAct σ) _ = _
  rw [Finsupp.equivMapDomain_single, gp.placeAct_infPlus]

/-- **The Galois action respects `picRel`** (PROVEN), so it descends to `Pic⁰(X_ℚ̄)`. -/
lemma divAct_picRel (σ : QbarGal) :
    gp.Dbar.picRel ≤ (gp.Dbar.picRel).comap (gp.divAct σ) := by
  refine sup_le ?_ ?_
  · refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨g, rfl⟩
    show gp.divAct σ (gp.Dbar.divisor g) ∈ gp.Dbar.picRel
    rw [divAct_divisor]
    exact AddSubgroup.mem_sup_left (AddSubgroup.subset_closure ⟨gp.fieldAct σ g, rfl⟩)
  · rw [AddSubgroup.zmultiples_le]
    show gp.divAct σ (Finsupp.single (gp.Dbar.pt PlaceData.infPlus) 1) ∈ gp.Dbar.picRel
    rw [divAct_single_infPlus]
    exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)

/-- **The Galois action on `Pic⁰(X_ℚ̄)`** (PROVEN well defined) — a DEFINITION, not a
field, which is what makes the leaves below sound. -/
noncomputable def act (σ : QbarGal) : gp.Dbar.Pic →+ gp.Dbar.Pic :=
  QuotientAddGroup.map gp.Dbar.picRel gp.Dbar.picRel (gp.divAct σ) (gp.divAct_picRel σ)

/-- **The image of base change is Galois-invariant** (PROVEN).

This is the compiler-checked witness that the pinning does its job: with an unpinned `act`
this would be unprovable, and its failure is exactly the hole through which the junk action
`act σ = 0` would have made `geomPic_descent` vacuous.  Together with `geomPic_descent` it
says `bc` identifies `Pic⁰(X_ℚ)` with `Pic⁰(X_ℚ̄)^{Gal}`. -/
lemma act_bc (σ : QbarGal) (a : D.Pic) : gp.act σ (gp.bc a) = gp.bc a := by
  induction a using QuotientAddGroup.induction_on with
  | _ δ =>
    show QuotientAddGroup.mk (gp.divAct σ (gp.bcDiv δ)) = QuotientAddGroup.mk (gp.bcDiv δ)
    congr 1
    ext w
    rw [divAct_apply, bcDiv_apply, bcDiv_apply]
    rw [← gp.below_placeAct σ ((gp.placeAct σ).symm w), Equiv.apply_symm_apply]

end GeomPic

section ConstFieldExtension

variable {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ}

/-! ### The constant field extension -/

/-- **The constant field extension `F ↪ F̄ = F·ℚ̄`, together with the Galois action on `F̄`.**

This is exactly the part of `GeomPic` that is pure field theory — no valuations, no places —
and it is PROVEN to exist by `exists_constFieldExt` below.  What `GeomPic` adds to it is
`below`, `ord_emb`, `below_finite` and `below_infPlus`, i.e. the valuation-theoretic content
of the extension. -/
structure ConstFieldExt (c₀ c₁ c₂ c₃ c₄ c₅ : ℤ) (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ) where
  /-- the same curve over an algebraic closure of `ℚ` -/
  Dbar : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ (AlgebraicClosure ℚ)
  /-- the inclusion of function fields -/
  emb : D.F →+* Dbar.F
  /-- it is a `ℚ`-algebra map -/
  emb_algebraMap : ∀ a : ℚ, emb (algebraMap ℚ D.F a)
      = algebraMap (AlgebraicClosure ℚ) Dbar.F (algebraMap ℚ (AlgebraicClosure ℚ) a)
  /-- and sends the abscissa to the abscissa -/
  emb_xx : emb D.xx = Dbar.xx
  /-- and the ordinate to the ordinate -/
  emb_yy : emb D.yy = Dbar.yy
  /-- the semilinear action of `σ` on the geometric function field -/
  fieldAct : QbarGal → Dbar.F ≃+* Dbar.F
  /-- semilinearity over `σ` on the constants -/
  fieldAct_algebraMap : ∀ (σ : QbarGal) (a : AlgebraicClosure ℚ),
      fieldAct σ (algebraMap (AlgebraicClosure ℚ) Dbar.F a)
        = algebraMap (AlgebraicClosure ℚ) Dbar.F (σ a)
  /-- and triviality on the rational function field -/
  fieldAct_emb : ∀ (σ : QbarGal) (g : D.F), fieldAct σ (emb g) = emb g

/-- Separability of the sextic survives the passage to `ℚ̄`. -/
lemma separable_sextPoly_algebraicClosure
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ (AlgebraicClosure ℚ)).Separable := by
  have h := hsep.map (f := algebraMap ℚ (AlgebraicClosure ℚ))
  rwa [map_sextPoly] at h

open Polynomial in
/-- Transcendence of `Dbar.xx` over the small field, in the `eval₂` form
`exists_ringHom_of_gen` consumes.

Note the `open Polynomial in`: this section is outside the `open Polynomial` of `Picard`,
and without it `K[X]` parses as `GetElem` indexing rather than as `Polynomial K`. -/
lemma eval₂_ne_zero_of_transcendental {K L A : Type} [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra L A] {x : A} (htr : Transcendental L x) (τ : K →+* L)
    (hτ : Function.Injective τ) (q : K[X]) (hq : q ≠ 0) :
    eval₂ ((algebraMap L A).comp τ) x q ≠ 0 := by
  rw [← Polynomial.eval₂_map]
  intro h
  exact htr ⟨q.map τ, (Polynomial.map_ne_zero_iff hτ).mpr hq, by rwa [Polynomial.aeval_def]⟩

/-- **PROVEN: the constant field extension exists.**

`Dbar` is any `PlaceData` over `ℚ̄` — one exists by `exists_placeData`, whose two hypotheses
survive base change — and `emb`, `fieldAct` are then produced by the presentation lemma
`exists_ringHom_of_gen`, their defining properties by its uniqueness counterpart
`ringHom_ext_of_gen`.  In particular `fieldAct σ` is bijective because `fieldAct σ⁻¹` is a
two-sided inverse *by uniqueness*, so the arbitrary choices made here are harmless. -/
theorem exists_constFieldExt (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    Nonempty (ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D) := by
  classical
  have hsepbar := separable_sextPoly_algebraicClosure (c₀ := c₀) (c₁ := c₁) (c₂ := c₂)
    (c₃ := c₃) (c₄ := c₄) (c₅ := c₅) hsep
  obtain ⟨Dbar⟩ := exists_placeData c₀ c₁ c₂ c₃ c₄ c₅ (AlgebraicClosure ℚ) hsepbar
    (by norm_num)
  -- the embedding
  obtain ⟨emb, hembc, hembx, hemby⟩ := exists_ringHom_of_gen D.eqn D.transcendental_xx D.gen
    hsep ((algebraMap (AlgebraicClosure ℚ) Dbar.F).comp (algebraMap ℚ (AlgebraicClosure ℚ)))
    Dbar.xx Dbar.yy Dbar.eqn
    (eval₂_ne_zero_of_transcendental Dbar.transcendental_xx _
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective)
  -- the action of a single `σ`
  have hact : ∀ σ : QbarGal, ∃ φ : Dbar.F →+* Dbar.F,
      (∀ a : AlgebraicClosure ℚ, φ (algebraMap (AlgebraicClosure ℚ) Dbar.F a)
        = algebraMap (AlgebraicClosure ℚ) Dbar.F (σ a)) ∧ φ Dbar.xx = Dbar.xx ∧
      φ Dbar.yy = Dbar.yy := by
    intro σ
    obtain ⟨φ, h1, h2, h3⟩ := exists_ringHom_of_gen Dbar.eqn Dbar.transcendental_xx Dbar.gen
      hsepbar ((algebraMap (AlgebraicClosure ℚ) Dbar.F).comp (σ : AlgebraicClosure ℚ →+* _))
      Dbar.xx Dbar.yy Dbar.eqn
      (eval₂_ne_zero_of_transcendental (L := AlgebraicClosure ℚ) Dbar.transcendental_xx _
        σ.injective)
    exact ⟨φ, h1, h2, h3⟩
  choose φ hφc hφx hφy using hact
  -- the composite of `σ` and `τ` is the composite of the two maps, by uniqueness
  have hcomp : ∀ σ τ : QbarGal, (φ σ).comp (φ τ) = φ (σ * τ) := by
    intro σ τ
    refine ringHom_ext_of_gen Dbar.gen (fun a => ?_) (by simp [hφx]) (by simp [hφy])
    simp only [RingHom.coe_comp, Function.comp_apply, hφc]
    rfl
  have hone : φ 1 = RingHom.id Dbar.F := by
    refine ringHom_ext_of_gen Dbar.gen (fun a => ?_) (by simp [hφx]) (by simp [hφy])
    simpa using hφc 1 a
  refine ⟨{ Dbar := Dbar
            emb := emb
            emb_algebraMap := hembc
            emb_xx := hembx
            emb_yy := hemby
            fieldAct := fun σ => RingEquiv.ofRingHom (φ σ) (φ σ⁻¹) ?_ ?_
            fieldAct_algebraMap := hφc
            fieldAct_emb := ?_ }⟩
  · show (φ σ).comp (φ σ⁻¹) = RingHom.id _
    rw [hcomp, mul_inv_cancel, hone]
  · show (φ σ⁻¹).comp (φ σ) = RingHom.id _
    rw [hcomp, inv_mul_cancel, hone]
  · intro σ g
    show ((φ σ).comp emb) g = emb g
    have : (φ σ).comp emb = emb := by
      refine ringHom_ext_of_gen D.gen (fun a => ?_) ?_ ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, hembc, hφc]
        rw [AlgEquiv.commutes]
      · simp only [RingHom.coe_comp, Function.comp_apply, hembx, hφx]
      · simp only [RingHom.coe_comp, Function.comp_apply, hemby, hφy]
    rw [this]

namespace ConstFieldExt

variable {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ} (cf : ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D)

lemma emb_injective : Function.Injective cf.emb := cf.emb.injective

lemma emb_ne_zero {g : D.F} (hg : g ≠ 0) : cf.emb g ≠ 0 :=
  (map_ne_zero_iff cf.emb cf.emb_injective).mpr hg

/-- **Galois fixes the abscissa** (PROVEN): it is in the image of `emb`. -/
lemma fieldAct_xx (σ : QbarGal) : cf.fieldAct σ cf.Dbar.xx = cf.Dbar.xx := by
  rw [← cf.emb_xx, cf.fieldAct_emb]

/-- **Galois fixes the ordinate** (PROVEN). -/
lemma fieldAct_yy (σ : QbarGal) : cf.fieldAct σ cf.Dbar.yy = cf.Dbar.yy := by
  rw [← cf.emb_yy, cf.fieldAct_emb]

/-- **`fieldAct` is automatically an action** (PROVEN): the composite is a ring hom with the
same effect on the constants, on `xx` and on `yy`, and `ringHom_ext_of_gen` says there is only
one such.  This is why `ConstFieldExt` need not carry the action axioms. -/
lemma fieldAct_mul (σ τ : QbarGal) :
    ((cf.fieldAct σ : cf.Dbar.F →+* cf.Dbar.F).comp (cf.fieldAct τ : cf.Dbar.F →+* cf.Dbar.F))
      = (cf.fieldAct (σ * τ) : cf.Dbar.F →+* cf.Dbar.F) := by
  refine ringHom_ext_of_gen cf.Dbar.gen (fun a => ?_) ?_ ?_
  · show cf.fieldAct σ (cf.fieldAct τ (algebraMap (AlgebraicClosure ℚ) cf.Dbar.F a))
      = cf.fieldAct (σ * τ) (algebraMap (AlgebraicClosure ℚ) cf.Dbar.F a)
    rw [cf.fieldAct_algebraMap, cf.fieldAct_algebraMap, cf.fieldAct_algebraMap]
    rfl
  · show cf.fieldAct σ (cf.fieldAct τ cf.Dbar.xx) = cf.fieldAct (σ * τ) cf.Dbar.xx
    rw [cf.fieldAct_xx, cf.fieldAct_xx, cf.fieldAct_xx]
  · show cf.fieldAct σ (cf.fieldAct τ cf.Dbar.yy) = cf.fieldAct (σ * τ) cf.Dbar.yy
    rw [cf.fieldAct_yy, cf.fieldAct_yy, cf.fieldAct_yy]

lemma fieldAct_one : (cf.fieldAct 1 : cf.Dbar.F →+* cf.Dbar.F) = RingHom.id cf.Dbar.F := by
  refine ringHom_ext_of_gen cf.Dbar.gen (fun a => ?_) ?_ ?_
  · simpa using cf.fieldAct_algebraMap 1 a
  · simpa using cf.fieldAct_xx 1
  · simpa using cf.fieldAct_yy 1

lemma fieldAct_fieldAct (σ τ : QbarGal) (h : cf.Dbar.F) :
    cf.fieldAct σ (cf.fieldAct τ h) = cf.fieldAct (σ * τ) h :=
  congrFun (congrArg (fun φ : cf.Dbar.F →+* cf.Dbar.F => (φ : cf.Dbar.F → cf.Dbar.F))
    (cf.fieldAct_mul σ τ)) h

lemma fieldAct_inv_fieldAct (σ : QbarGal) (h : cf.Dbar.F) :
    cf.fieldAct σ⁻¹ (cf.fieldAct σ h) = h := by
  rw [cf.fieldAct_fieldAct, inv_mul_cancel]
  simpa using congrFun (congrArg (fun φ : cf.Dbar.F →+* cf.Dbar.F =>
    (φ : cf.Dbar.F → cf.Dbar.F)) cf.fieldAct_one) h

lemma fieldAct_algebraMap_inv (σ : QbarGal) (a : AlgebraicClosure ℚ) :
    cf.fieldAct σ⁻¹ (algebraMap (AlgebraicClosure ℚ) cf.Dbar.F a)
      = algebraMap (AlgebraicClosure ℚ) cf.Dbar.F (σ⁻¹ a) := cf.fieldAct_algebraMap σ⁻¹ a

end ConstFieldExt

/-- **LEAF (weak Mordell–Weil, 1a of 4): the constant field extension is UNRAMIFIED.**

`ord_w ∘ emb` is again a NORMALISED valuation of `F`: its value group is all of `ℤ`, i.e.
`e(w | w ∩ F) = 1`.  This is [Stichtenoth, *Algebraic Function Fields and Codes*, III.6.3(b)]
— a constant field extension `F·K'/F` is unramified at every place — and it is the only thing
standing between `ConstFieldExt` (PROVEN to exist above) and `below` together with `ord_emb`:
given it, `D.ord_complete` produces the place below and its defining property, and both are
Lean definitions rather than fields (see `ConstFieldExt.below` and `ConstFieldExt.ord_below`).

Route.  Reduce to a finite subextension: `emb t` for `t ∈ F` involves only finitely many
algebraic numbers, so `w` restricted to `F·K'` for a finite `K'/ℚ` suffices, and
`[F·K' : F] = [K' : ℚ]` because `ℚ` is algebraically closed in `F` (the curve is
geometrically irreducible: `Y² − f` stays irreducible over `ℚ̄(x)`, which is
`not_isSquare_sextPoly` over `ℚ̄`).  Then `Σ_{w' | v} e(w') f(w') ≤ [F·K' : F] = [K' : ℚ]`
while `f(w') ≥ [K'·κ(v) : κ(v)]`, and equality in the constant-field case forces `e = 1`.

**Not vacuous, and `hsep` is not needed**: the data of `ConstFieldExt` already pins `Dbar.F`
as `ℚ̄(xx, yy)` and `emb (D.F)` as `ℚ(xx, yy)` inside it, by `ringHom_ext_of_gen`, so this is
a statement about the honest constant field extension and about nothing else.

**What would refute it**: a `w` for which `ord_w (emb t)` is even for every `t ∈ F` — i.e. a
ramified geometric place.  That cannot happen for a CONSTANT field extension, but it does
happen for the geometric extension `ℚ̄(x) ⊆ ℚ̄(x)(√x)`, which is why the proof must use that
`Dbar.F` is generated over `emb (D.F)` by CONSTANTS. -/
theorem constFieldExt_exists_uniformizer {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (cf : ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D) (w : cf.Dbar.Places) :
    ∃ t : D.F, cf.Dbar.ord w (cf.emb t) = 1 := sorry

namespace ConstFieldExt

variable {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ} (cf : ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D)

/-- **The place of `F` below a geometric place exists** (PROVEN from
`constFieldExt_exists_uniformizer` and `D.ord_complete`). -/
lemma exists_below (w : cf.Dbar.Places) :
    ∃ v : D.Places, ∀ g : D.F, D.ord v g = cf.Dbar.ord w (cf.emb g) := by
  obtain ⟨v, hv⟩ := D.ord_complete (fun g => cf.Dbar.ord w (cf.emb g))
    (by simp only [map_zero, cf.Dbar.ord_zero])
    (fun a b ha hb => by
      simp only [map_mul]
      exact cf.Dbar.ord_mul _ _ _ (cf.emb_ne_zero ha) (cf.emb_ne_zero hb))
    (fun a b ha hb hab => by
      simp only [map_add]
      exact cf.Dbar.ord_add _ _ _ (cf.emb_ne_zero ha) (cf.emb_ne_zero hb)
        (by rw [← map_add]; exact cf.emb_ne_zero hab))
    (fun a ha => by
      rw [cf.emb_algebraMap]
      refine cf.Dbar.ord_algebraMap _ _ ?_
      simpa using ha)
    (constFieldExt_exists_uniformizer cf w)
  exact ⟨v, fun g => by rw [hv]⟩

/-- **The place of `F` below a geometric place** (PROVEN well defined). -/
noncomputable def below (w : cf.Dbar.Places) : D.Places := (cf.exists_below w).choose

/-- **`ord_emb`: the constant field extension does not move orders** (PROVEN). -/
lemma ord_below (w : cf.Dbar.Places) (g : D.F) :
    D.ord (cf.below w) g = cf.Dbar.ord w (cf.emb g) := (cf.exists_below w).choose_spec g

/-- **The Galois translate of a geometric place exists** (PROVEN from `Dbar.ord_complete`):
`ord_{σ·w} = ord_w ∘ (fieldAct σ)⁻¹`. -/
lemma exists_placeAct (σ : QbarGal) (w : cf.Dbar.Places) :
    ∃ v : cf.Dbar.Places, ∀ h : cf.Dbar.F,
      cf.Dbar.ord v h = cf.Dbar.ord w (cf.fieldAct σ⁻¹ h) := by
  obtain ⟨u, hu⟩ := cf.Dbar.ord_surjective w
  obtain ⟨v, hv⟩ := cf.Dbar.ord_complete (fun h => cf.Dbar.ord w (cf.fieldAct σ⁻¹ h))
    (by simp only [map_zero, cf.Dbar.ord_zero])
    (fun a b ha hb => by
      simp only [map_mul]
      exact cf.Dbar.ord_mul _ _ _
        ((map_ne_zero_iff _ (cf.fieldAct σ⁻¹).injective).mpr ha)
        ((map_ne_zero_iff _ (cf.fieldAct σ⁻¹).injective).mpr hb))
    (fun a b ha hb hab => by
      simp only [map_add]
      exact cf.Dbar.ord_add _ _ _
        ((map_ne_zero_iff _ (cf.fieldAct σ⁻¹).injective).mpr ha)
        ((map_ne_zero_iff _ (cf.fieldAct σ⁻¹).injective).mpr hb)
        (by rw [← map_add]; exact (map_ne_zero_iff _ (cf.fieldAct σ⁻¹).injective).mpr hab))
    (fun a ha => by
      rw [cf.fieldAct_algebraMap_inv]
      refine cf.Dbar.ord_algebraMap _ _ ?_
      simpa using ha)
    ⟨cf.fieldAct σ u, by rw [cf.fieldAct_inv_fieldAct]; exact hu⟩
  exact ⟨v, fun h => by rw [hv]⟩

/-- The Galois translate of a geometric place, as a function. -/
noncomputable def placeActFun (σ : QbarGal) (w : cf.Dbar.Places) : cf.Dbar.Places :=
  (cf.exists_placeAct σ w).choose

lemma ord_placeActFun (σ : QbarGal) (w : cf.Dbar.Places) (h : cf.Dbar.F) :
    cf.Dbar.ord (cf.placeActFun σ w) h = cf.Dbar.ord w (cf.fieldAct σ⁻¹ h) :=
  (cf.exists_placeAct σ w).choose_spec h

lemma placeActFun_mul (σ τ : QbarGal) (w : cf.Dbar.Places) :
    cf.placeActFun σ (cf.placeActFun τ w) = cf.placeActFun (σ * τ) w := by
  refine cf.Dbar.ord_injective (funext fun h => ?_)
  rw [cf.ord_placeActFun, cf.ord_placeActFun, cf.ord_placeActFun, cf.fieldAct_fieldAct,
    mul_inv_rev]

lemma placeActFun_one (w : cf.Dbar.Places) : cf.placeActFun 1 w = w := by
  refine cf.Dbar.ord_injective (funext fun h => ?_)
  rw [cf.ord_placeActFun, inv_one]
  exact congrArg (cf.Dbar.ord w) (congrFun (congrArg
    (fun φ : cf.Dbar.F →+* cf.Dbar.F => (φ : cf.Dbar.F → cf.Dbar.F)) cf.fieldAct_one) h)

/-- **The induced permutation of geometric places** (PROVEN to be a permutation). -/
noncomputable def placeAct (σ : QbarGal) : cf.Dbar.Places ≃ cf.Dbar.Places where
  toFun := cf.placeActFun σ
  invFun := cf.placeActFun σ⁻¹
  left_inv w := by rw [cf.placeActFun_mul, inv_mul_cancel, cf.placeActFun_one]
  right_inv w := by rw [cf.placeActFun_mul, mul_inv_cancel, cf.placeActFun_one]

/-- **`ord_placeAct`** (PROVEN). -/
lemma ord_placeAct (σ : QbarGal) (v : cf.Dbar.Places) (g : cf.Dbar.F) :
    cf.Dbar.ord (cf.placeAct σ v) (cf.fieldAct σ g) = cf.Dbar.ord v g := by
  show cf.Dbar.ord (cf.placeActFun σ v) (cf.fieldAct σ g) = cf.Dbar.ord v g
  rw [cf.ord_placeActFun, cf.fieldAct_inv_fieldAct]

end ConstFieldExt

/-- **PROVEN: a place of `F` has finitely many geometric places above it** — the
`below_finite` field of `GeomPic`.

The sharp statement is that the fibre has exactly `deg v = [κ(v) : ℚ]` elements
([Stichtenoth, *Algebraic Function Fields and Codes*, III.6.3(c)]), and that is what the
`GeomPic` docstring quotes; but only FINITENESS is used, and finiteness needs no residue
theory at all.  A uniformiser `t` at `v` — `D.ord_surjective` — has `ord_w (emb t) = 1 ≠ 0`
at every `w` above `v` by `ord_below`, so the whole fibre sits inside the zero-and-pole set
of the single function `emb t`, which is finite by `Dbar.ord_finite`.

Note this uses `ord_below` and hence the unramifiedness leaf, but only through the *existence*
of some function of nonzero order — so it would survive any `e ≥ 1`. -/
theorem constFieldExt_below_finite {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (cf : ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D) (v : D.Places) :
    {w : cf.Dbar.Places | cf.below w = v}.Finite := by
  obtain ⟨t, ht⟩ := D.ord_surjective v
  have htne : t ≠ 0 := by
    intro h
    rw [h, D.ord_zero] at ht
    omega
  refine Set.Finite.subset (cf.Dbar.ord_finite (cf.emb t) (cf.emb_ne_zero htne)) ?_
  intro w hw
  have hw' : cf.below w = v := hw
  simp only [Set.mem_setOf_eq, ← cf.ord_below, hw', ht]
  omega

/-- **PROVEN from `pt_infinite_of_ord_xx_neg`: the rational base point has exactly ONE
geometric place above it** — which is the `below_infPlus` field of `GeomPic`.

`∞₊` is a `ℚ`-rational point, hence a place of degree `1`, hence — by the sharp form of
`constFieldExt_below_finite` — has a single geometric place over it, which is then forced to
be `Dbar.pt ∞₊` since that one does lie over it.  This is the field of `GeomPic` that makes
`bcDiv` respect `picRel` and the Galois action fix the base point.

Both directions are the SAME statement `pt_inr_eq_of_ord_xx` applied once downstairs and once
upstairs, because `ord_below` transports the two branch conditions in both directions
verbatim: `emb` fixes `xx` and `yy`, so `ord_w (emb (yy − xx³)) = ord_{below w} (yy − xx³)`
is an identity between the very expressions the conditions are about.  Nothing about degrees
or fibre counts is needed after all, which is why this is no longer a leaf. -/
theorem constFieldExt_below_infPlus {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (cf : ConstFieldExt c₀ c₁ c₂ c₃ c₄ c₅ D) (w : cf.Dbar.Places) :
    cf.below w = D.pt PlaceData.infPlus ↔ w = cf.Dbar.pt PlaceData.infPlus := by
  have hemb3 : cf.emb (D.yy - (if true then (1 : D.F) else -1) * D.xx ^ 3)
      = cf.Dbar.yy - (if true then (1 : cf.Dbar.F) else -1) * cf.Dbar.xx ^ 3 := by
    simp only [if_true, one_mul, map_sub, map_pow, cf.emb_xx, cf.emb_yy]
  constructor
  · intro h
    refine pt_inr_eq_of_ord_xx cf.Dbar true w ?_ ?_
    · rw [← cf.emb_xx, ← cf.ord_below, h]
      exact (D.ord_pt_infinite true).1
    · rw [← hemb3, ← cf.ord_below, h]
      exact (D.ord_pt_infinite true).2
  · intro h
    subst h
    refine pt_inr_eq_of_ord_xx D true _ ?_ ?_
    · rw [cf.ord_below, cf.emb_xx]
      exact (cf.Dbar.ord_pt_infinite true).1
    · rw [cf.ord_below, hemb3]
      exact (cf.Dbar.ord_pt_infinite true).2

/-- **PROVEN 2026-07-30: the geometric divisor theory exists.**

This used to be the leaf "base change of the whole layer to `ℚ̄`, together with the Galois
action".  It is now assembled from `exists_constFieldExt` — which supplies every field of
`GeomPic` that is pure FIELD theory, and is proven above over the presentation lemmas
`exists_ringHom_of_gen` / `ringHom_ext_of_gen` — together with `ConstFieldExt.below`,
`ConstFieldExt.ord_below`, `constFieldExt_below_finite`, `constFieldExt_below_infPlus`,
`ConstFieldExt.placeAct` and `ConstFieldExt.ord_placeAct`, all proven above.

**What is left, and the honest accounting.**  Two leaves replace this one:

* `constFieldExt_exists_uniformizer` — the constant field extension is UNRAMIFIED
  (Stichtenoth III.6.3(b)).  It is what makes `below` and `ord_emb` definable at all.
* `pt_infinite_of_ord_xx_neg` — the only poles of `x` are the two points at infinity, i.e.
  the fundamental inequality `Σ_{v | ∞} e f ≤ [F : K(x)] = 2` at one place for one function.

So the count went `1 → 2`, and what was bought is that the 14 fields of `GeomPic` are no
longer an existence claim: `emb` and `fieldAct` are CONSTRUCTED (not chosen), `below` is a
definition rather than data, and `below_finite`, `below_infPlus`, `ord_emb`, `ord_placeAct`
are theorems.  Both new leaves are single valuation-theoretic facts with textbook references,
where the old one was a whole base-change theory. -/
theorem exists_geomPic (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) :
    Nonempty (GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) := by
  obtain ⟨cf⟩ := exists_constFieldExt D hsep
  exact ⟨{ Dbar := cf.Dbar
           emb := cf.emb
           emb_algebraMap := cf.emb_algebraMap
           emb_xx := cf.emb_xx
           emb_yy := cf.emb_yy
           below := cf.below
           ord_emb := fun w g _ => (cf.ord_below w g).symm
           below_finite := constFieldExt_below_finite cf
           below_infPlus := constFieldExt_below_infPlus cf
           fieldAct := cf.fieldAct
           fieldAct_algebraMap := cf.fieldAct_algebraMap
           fieldAct_emb := cf.fieldAct_emb
           placeAct := cf.placeAct
           ord_placeAct := cf.ord_placeAct }⟩

end ConstFieldExtension

/-- **LEAF (weak Mordell–Weil, 2 of 4): `Pic⁰(X_ℚ) → Pic⁰(X_ℚ̄)` is injective.**

TRUE and classical: for a smooth projective geometrically integral curve with a
`K`-rational point, `Pic(X_K) → Pic(X_K̄)^{Gal}` is an isomorphism (the obstruction lives in
`Br(K)` and is killed by the rational point).  Injectivity is the easy half: a `ℚ`-divisor
that becomes `div ḡ + n·[∞₊]` over `ℚ̄` has `ḡ` Galois-invariant up to `ℚ̄^×`, and Hilbert 90
descends it to `F`.

`X` has the rational point `∞₊` by construction — that is precisely why `PlaceData` carries
`pt` and why `picRel` quotients by `ℤ·[∞₊]`.

**Not vacuous.**  Without the rational point this can fail, and the failure is exactly the
Brauer obstruction; the hypothesis is carried by the structure rather than stated here. -/
theorem geomPic_bc_injective {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) : Function.Injective gp.bc := sorry

/-- **LEAF (weak Mordell–Weil, 3 of 4): Galois descent — an invariant geometric class is
rational.**

The surjectivity half of `Pic(X_ℚ) ≅ Pic(X_ℚ̄)^{Gal}`, and the half that genuinely uses the
rational base point `∞₊`.  `act_bc` above is the converse inclusion and is PROVEN, so the
two together say `bc` identifies `Pic⁰(X_ℚ)` with the invariants.

**This is the leaf the unsound cut would have destroyed.**  Had `act` been an unpinned
structure field, `act σ = 0` would satisfy every stated axiom and make this leaf vacuous —
its hypothesis `∀ σ, act σ y = y` would read `y = 0`.  It is `fieldAct_algebraMap` (which
forbids `fieldAct σ = id` for `σ ≠ 1`) plus the derivation of `act` from `placeAct` that
makes the hypothesis mean what it says.  See the section docstring above. -/
theorem geomPic_descent {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) (y : gp.Dbar.Pic)
    (hy : ∀ σ : QbarGal, gp.act σ y = y) : ∃ a : D.Pic, gp.bc a = y := sorry

/-- **Divisibility at every prime gives divisibility at every nonzero `n`** (PROVEN, pure
group theory, no hypothesis on `G` beyond `AddCommGroup`).

Induction on the number of prime factors, done as a bounded induction so that only
`Nat.minFac_prime` and `Nat.minFac_dvd` are needed.  This is the divisibility analogue of
`Fermat.finite_quotient_nsmul_of_prime`, which promotes finiteness of `A/pA` from primes to
every `n`, and it is here for the same reason: it lets the geometric leaf below be stated at
a PRIME, where the intended proof lives, rather than at a general `n`. -/
theorem divisible_of_prime {G : Type*} [AddCommGroup G]
    (h : ∀ p : ℕ, p.Prime → ∀ y : G, ∃ z : G, p • z = y) (n : ℕ) (hn : n ≠ 0) (y : G) :
    ∃ z : G, n • z = y := by
  have key : ∀ k m : ℕ, m ≤ k → m ≠ 0 → ∀ y : G, ∃ z : G, m • z = y := by
    intro k
    induction k with
    | zero => intro m hmk hm _; omega
    | succ k ih =>
      intro m hmk hm y
      rcases eq_or_ne m 1 with rfl | h1
      · exact ⟨y, one_smul ℕ y⟩
      · have hp : (m.minFac).Prime := Nat.minFac_prime h1
        obtain ⟨q, hq⟩ := m.minFac_dvd
        have hq0 : q ≠ 0 := by rintro rfl; simp at hq; omega
        have h2 := hp.two_le
        have hqlt : q < m := by
          rcases Nat.lt_or_ge q m with h | h
          · exact h
          · exfalso
            have : m.minFac * q ≥ 2 * m := Nat.mul_le_mul h2 h
            omega
        obtain ⟨w, hw⟩ := ih q (by omega) hq0 y
        obtain ⟨z, hz⟩ := h _ hp w
        refine ⟨z, ?_⟩
        have hm' : m = q * m.minFac := by rw [Nat.mul_comm q m.minFac]; exact hq
        rw [hm', mul_smul, hz, hw]
  exact key n n le_rfl hn y

/-- **Divisibility on the classes of the generators gives divisibility everywhere** (PROVEN).

`α →₀ ℤ` is FREE on `α`, so the classes of the `Finsupp.single a 1` generate every quotient
of it, and `{x | ∃ z, n • z = x}` is the range of an `AddMonoidHom`, hence a SUBGROUP — which
is what makes checking the generators enough.  Applied below with `α := Dbar.Places` and the
quotient `PlaceData.Pic`, so that the geometric leaf need only divide the class of a SINGLE
PLACE.

The two steps that are not formal: `Finsupp.single a b = b • Finsupp.single a 1`, and the
fact that a quotient map commutes with `zsmul` — both discharged here once and for all. -/
theorem divisible_of_finsuppSingle {α : Type*} {H : AddSubgroup (α →₀ ℤ)} (n : ℕ)
    (h : ∀ a : α, ∃ z : (α →₀ ℤ) ⧸ H, n • z = QuotientAddGroup.mk (Finsupp.single a 1))
    (y : (α →₀ ℤ) ⧸ H) : ∃ z : (α →₀ ℤ) ⧸ H, n • z = y := by
  set S : AddSubgroup ((α →₀ ℤ) ⧸ H) := (nsmulAddMonoidHom n).range
  have hmem : ∀ x : (α →₀ ℤ) ⧸ H, x ∈ S → ∃ z, n • z = x := by
    intro x hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz⟩
  have hsingle : ∀ (a : α) (c : ℤ),
      (QuotientAddGroup.mk (Finsupp.single a c) : (α →₀ ℤ) ⧸ H) ∈ S := by
    intro a c
    have hbase : (QuotientAddGroup.mk (Finsupp.single a 1) : (α →₀ ℤ) ⧸ H) ∈ S := h a
    have hz := S.zsmul_mem hbase c
    have hpush : (c : ℤ) • (QuotientAddGroup.mk (Finsupp.single a 1) : (α →₀ ℤ) ⧸ H)
        = QuotientAddGroup.mk (c • Finsupp.single a 1) :=
      (map_zsmul (QuotientAddGroup.mk' H) c (Finsupp.single a 1)).symm
    rw [hpush] at hz
    have hc : (c • Finsupp.single a 1 : α →₀ ℤ) = Finsupp.single a c := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rwa [hc] at hz
  refine hmem y ?_
  induction y using QuotientAddGroup.induction_on with
  | _ δ =>
    induction δ using Finsupp.induction with
    | zero => simp
    | @single_add a b δ _ _ ih =>
      have hsum : (QuotientAddGroup.mk (Finsupp.single a b + δ) : (α →₀ ℤ) ⧸ H)
          = QuotientAddGroup.mk (Finsupp.single a b) + QuotientAddGroup.mk δ := rfl
      rw [hsum]
      exact S.add_mem (hsingle a b) ih

/-- **LEAF (weak Mordell–Weil, 4 of 4, geometric): the class of a single geometric place is
`p`-divisible in `Pic⁰(X_ℚ̄)`, for every prime `p`.**

`[p] : J → J` is surjective on `K̄`-points for `p ≠ 0` and any abelian variety over an
algebraically closed field — it is a finite flat isogeny of degree `p^{2g}`, so surjective
on geometric points.  Equivalently, and closer to this presentation: a class of degree `0`
on a curve over an algebraically closed field is `p` times another, because `Pic⁰` is a
divisible group (it is the group of points of a connected algebraic group over an
algebraically closed field).

**RESTATED 2026-07-30, STRICTLY WEAKENED, no consumer changed.**  Until this cycle the leaf
was `geomPic_divisible` itself — `∀ n ≠ 0, ∀ y : Pic⁰(X_ℚ̄), ∃ z, n • z = y`.  That statement
is now PROVEN immediately below, from this leaf plus `divisible_of_prime` and
`divisible_of_finsuppSingle`, so the general form is a compiler-checked consequence and the
remaining obligation is an INSTANCE of the old one.  What the reduction removes, permanently:
the prime factorisation of `n`, the `Finsupp` generation argument, and the fact that
`n • Pic` is a subgroup.  What is left is exactly the geometry — `[p]` is surjective — asked
at one place at a time.

**FAITHFULNESS (re-run against this composite statement, per the standing rule that a second
restatement VOIDS the earlier audit).**  `p.Prime` gives `p ≥ 2`, so there is no `n = 0`
degeneracy to worry about here; the `n ≠ 0` discussion moved to `geomPic_divisible` below,
where `hn` still appears and is still load-bearing.  The statement is TRUE for every
`PlaceData` over `AlgebraicClosure ℚ`, including the degenerate ones: `PlaceData`'s
`ord_complete` pins `Places` as EXACTLY the normalised `ℚ̄`-trivial discrete valuations of
`F`, i.e. the closed points of the smooth projective model, so `Pic = Div/(princ + ℤ·[∞₊])`
is `Pic⁰` of that model (`deg [∞₊] = 1` because every point of a curve over an algebraically
closed field has degree `1`, which is what splits `Pic ≅ ℤ ⊕ Pic⁰`).  Note this does NOT
need the sextic to be separable: if `sextPoly` has a repeated root the model is a curve of
genus `< 2` — possibly `ℙ¹`, where `Pic⁰ = 0` — and a trivial or elliptic `Pic⁰` is divisible
too.  Note also that the statement mentions `Dbar` alone, not `bc`, so it carries none of the
arithmetic; the arithmetic is entirely in the cochain leaf.

## ATOMICITY AUDIT (2026-07-30) — which AXES were searched, and what would refute each

* **GENERATOR / PRIME-FACTORISATION axis — TAKEN, and it is the reduction above.**  It is
  the only axis on which anything was formal, and it is now spent: nothing further about `n`,
  about `Finsupp`, or about which elements of `Pic` are hit remains to be cut.
* **ELLIPTIC-ANALOGUE axis — the route is PROVEN IN THIS REPOSITORY at genus `1`, and does
  not transfer.**  `Fermat.EllipticCurve.nsmul_surjective` (`Fermat/FLT/EllipticCurve/
  Isogeny.lean`) is exactly this leaf for an elliptic curve over an algebraically closed
  field, and it is proven — from DIVISION POLYNOMIALS plus algebraic closedness: `ΨSqₙ` is a
  nonzero polynomial, `IsCoprime Φ ΨSq` keeps its value away from the pole, and a root of
  the resulting one-variable equation exists because the field is algebraically closed.  The
  argument is genuinely one-variable and genus-`1`-specific.  At genus `2` the analogue would
  need the duplication (and `n`-division) formulas on the KUMMER SURFACE, i.e. `2`-dimensional
  equation solving, where algebraic closedness alone no longer produces a solution — one needs
  the multiplication map to be finite/dominant, which is the Jacobian-as-a-variety input this
  leaf is trying to avoid.  *Refuting check*: a one-variable division polynomial for a genus-`2`
  Jacobian whose roots are the `x`-coordinates of the `n`-division points of a given class.
* **GEOMETRIC-SPLITTING axis — closed by GENERICITY, before any computation.**  If `J ⊗ ℚ̄`
  were isogenous to a product of elliptic curves the previous axis would apply through the
  isogeny; but this leaf is `∀`-quantified over the sextic, so no level-specific splitting is
  available to it, and specialising the whole generic Mordell–Weil chain (`fg_pic`,
  `finite_quotient_psmul_pic`) to the two levels would duplicate it and still need transport
  of divisibility across a `ℚ̄`-isogeny of Jacobians presented as `PlaceData` quotients —
  strictly more than the leaf.  For the record, and as an untrusted searcher only: PARI
  `hyperellcharpoly` gives Frobenius traces `a_p` on `J₁(18)` of `0, −2, 3, −2, −6, −2` at
  `p = 5, 7, 11, 13, 17, 19`, and on `J₁(13)` of `−2, 0, 0, 0, 3, −6` at `p = 3, 5, 7, 11,
  17, 19` (vanishing at `5` of the `15` good `p < 60`, namely `5, 7, 11, 31, 47`) — so no
  systematic vanishing at either level, hence no naive Weil-restriction pattern.  **This is
  NOT evidence about `End⁰`**: the quantity is the trace on the SURFACE, i.e. `2 Re a_p(f)`,
  which vanishes whenever `a_p(f)` is purely imaginary — so the level-`13` zeros are expected
  and prove nothing either way.  *Refuting check*: Magma
  `EndomorphismAlgebra`/`IsGeometricallySimple` on either Jacobian returning a split answer.
* **RIEMANN–ROCH axis — a restatement, not a cut.**  For genus `2` every class of `Pic⁰` is
  `[P + Q − 2∞₊]` (Riemann–Roch: `deg = g` forces effectivity), so one may reduce to dividing
  such classes; but the resulting obligation is `[n]` surjective on the image of `C^{(2)}`,
  which is all of `Pic⁰` — the same statement.  *Refuting check*: an argument that divides
  `[P + Q − 2∞₊]` using only the effectivity, with no surjectivity input.
* **SCHEME-THEORETIC axis — the same obligation exists in `X0.lean` and is also open there.**
  `exists_finiteIndex_divisible_of_abelianScheme` (`Fermat/FLT/ModularCurve/X0.lean`) is the
  scheme-theoretic form; it asks only for a finite-index divisible subgroup, which is weaker,
  but for `J(ℚ̄)` the two are equally hard, since the finite-index subgroup would itself have
  to be produced from `[n]`.  **Do not prove this twice** — see the `MordellWeil` section
  docstring for the bridge that would make one of the two redundant.
* **ANALYTIC axis — dead here as everywhere in this file.**  `J(ℂ) = ℂ²/Λ` is divisible on
  sight, and `ℚ̄ ⊆ ℂ` with `n`-division points of a `ℚ̄`-point being algebraic would finish it;
  but the uniformisation of an abelian variety by a complex torus exists neither in this
  project nor in mathlib.  *Refuting check*: grep either for a complex-torus uniformisation. -/
theorem geomPic_divisible_place {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) (p : ℕ) (hp : p.Prime) (w : gp.Dbar.Places) :
    ∃ z : gp.Dbar.Pic, p • z = QuotientAddGroup.mk (Finsupp.single w 1) := sorry

/-- **`Pic⁰(X_ℚ̄)` is divisible** — a LEAF from its creation until 2026-07-30, now PROVEN
over the strictly weaker leaf `geomPic_divisible_place` (one place, one prime) together with
`divisible_of_prime` and `divisible_of_finsuppSingle`.

**FAITHFULNESS.**  `hn` is load-bearing: at `n = 0` the statement reads `∃ z, 0 = y`, which
is false for every `y ≠ 0`, and `Pic⁰(X_ℚ̄)` is never trivial for a genus-`2` curve.  The
hypothesis survives the reduction as the `m ≠ 0` of `divisible_of_prime`; the leaf itself no
longer carries it, `p.Prime` being stronger. -/
theorem geomPic_divisible {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) (n : ℕ) (hn : n ≠ 0) (y : gp.Dbar.Pic) :
    ∃ z : gp.Dbar.Pic, n • z = y :=
  divisible_of_prime
    (fun p hp y => divisible_of_finsuppSingle p (geomPic_divisible_place gp p hp) y) n hn y

/-- **LEAF (weak Mordell–Weil, the arithmetic): only finitely many Kummer cochains occur.**

This is the whole arithmetic content of weak Mordell–Weil, isolated by
`Fermat.finite_quotient_nsmul_of_kummerCochains`, and it is the only one of the five leaves
in this cluster that needs a finiteness theorem of algebraic number theory.

Two routes, and the second is the one `X0.lean` found cheaper:

* the classical one — the cochains land in `J[p](ℚ̄) ≅ (ℤ/p)⁴` and are unramified outside
  the finite set `S` of places over `p·disc(f)`, so they are cut out by the `p`-Selmer group
  of `L = ℚ(J[p])`, finite by finiteness of `Cl(L)` and Dirichlet's unit theorem;
* **Hermite–Minkowski**, which `X0.lean` uses at
  `exists_finiteIndex_divisible_of_abelianScheme` after recording that the class group and
  the unit theorem are *not* what is needed: the assembly meets one division field
  `ℚ(J[p], y)` at a time, each of degree at most `#J[p]` over `ℚ(J[p])`, and there are only
  finitely many number fields of bounded degree and bounded discriminant.  A cochain is then
  determined by its restriction to a finite quotient of `Γ` and takes values in a finite
  group, so finitely many occur.

**FAITHFULNESS.**  `hp` is load-bearing at least through `p ≠ 0`: at `p = 0` the condition
`0 • Q = bc P` forces `bc P = 0`, hence `P = 0` by `geomPic_bc_injective`, but leaves `Q`
completely free, so the cochains `σ ↦ act σ Q − Q` range over an infinite set whenever
`Pic⁰(X_ℚ̄)` has a point with nontrivial Galois orbit — which it does.  Primality is not
needed for TRUTH, but it is what makes the intended proof available (`J[p]` is an
`𝔽_p`-vector space, and the sibling reduction `Fermat.finite_quotient_nsmul_of_prime`
supplies every other `n`), so it is kept rather than weakened to `p ≠ 0`. -/
theorem finite_kummerCochains_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} {D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ}
    (gp : GeomPic c₀ c₁ c₂ c₃ c₄ c₅ D) (p : ℕ) (hp : p.Prime) :
    {c : QbarGal → gp.Dbar.Pic | ∃ (P : D.Pic) (Q : gp.Dbar.Pic),
      p • Q = gp.bc P ∧ c = fun σ => gp.act σ Q - Q}.Finite := sorry

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
docstring.

**NO LONGER A LEAF (2026-07-28).**  It is PROVEN below over the four leaves cut
immediately above — `exists_geomPic`, `geomPic_bc_injective`, `geomPic_descent`,
`geomPic_divisible` and `finite_kummerCochains_pic` — assembled by the released reduction
`Fermat.finite_quotient_nsmul_of_kummerCochains`.  Of those four, `geomPic_divisible` became
PROVEN on 2026-07-30 in turn, so the open ones reached from here are `exists_geomPic`,
`geomPic_bc_injective`, `geomPic_descent`, `geomPic_divisible_place` and
`finite_kummerCochains_pic`.  Note what the assembly does NOT mention:
no group cohomology, no `H¹`, no profinite topology.  The Kummer cochain is a plain
function on `QbarGal` and the coboundary relation is never formed. -/
theorem finite_quotient_psmul_pic {c₀ c₁ c₂ c₃ c₄ c₅ : ℤ} (D : PlaceData c₀ c₁ c₂ c₃ c₄ c₅ ℚ)
    (hsep : (sextPoly c₀ c₁ c₂ c₃ c₄ c₅ ℚ).Separable) (p : ℕ) (hp : p.Prime) :
    Finite (D.Pic ⧸ (nsmulAddMonoidHom p : D.Pic →+ D.Pic).range) := by
  obtain ⟨gp⟩ := exists_geomPic D hsep
  exact finite_quotient_nsmul_of_kummerCochains p (fun σ y => gp.act σ y)
    (fun σ y z => map_sub (gp.act σ) y z)
    (fun a => gp.bc a) (map_zero gp.bc) (fun a b => map_add gp.bc a b)
    (geomPic_bc_injective gp) (geomPic_descent gp)
    (fun P => geomPic_divisible gp p hp.ne_zero (gp.bc P))
    (finite_kummerCochains_pic gp p hp)

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

RE-VERIFIED INDEPENDENTLY IN PARI, 2026-07-30 (a sixth run, and a different CAS): `f` is
irreducible (`polisirreducible = 1`); `poldisc f = −2¹⁵·3⁴`, matching `separable_sextPoly`'s
Bézout certificate above and differing from Magma's `Discriminant(C) = 2²³·3⁴` by exactly
the model factor `2⁸` — the same `2⁸` appears at level `13` (`poldisc f₁₃ = −2¹²·13²`
against Magma's `2²⁰·13²`), so the two normalisations are consistent and neither figure is
wrong; and `hyperellcharpoly(f mod 5) = T⁴ − 5T² + 25`, whose `T³` coefficient `0` gives
`#C(𝔽₅) = 5 + 1 + 0 = 6` (matching `card_X18_F5`) and whose value at `1` gives
`#J(𝔽₅) = 1 − 5 + 25 = 21`.  `rank J(ℚ) = 0` remains the one input no such check reaches.

## DECISION 2026-07-30: NOT DECOMPOSED, AND THE RE-CUT ARGUMENT RE-DERIVED

Dispatched at as an unowned leaf and deliberately left atomic again.  The recorded rejection
of the obvious re-cut — "`Pic` is torsion" plus "`J(ℚ)[2] = 0`" in place of `Pic = 2·Pic` —
was re-derived rather than taken on trust, and it is correct: those two together are
STRICTLY stronger.  They imply this leaf (no element of order `2` forces every order odd, so
`z = 2 • ((n+1)/2 • z)` for `n` the odd order of `z`), while the converse fails — `ℚ` is
`2`-divisible with `ℚ[2] = 0` and is not torsion.  So that re-cut trades one leaf for two
strictly harder ones, and the `2`-divisible phrasing in force is the right one.  The one
defect this pass found is in the DESCENT-axis bullet below: its target group was the
odd-degree one.  Corrected there.

**THAT JUSTIFICATION IS WRONG ONCE `fg_pic` IS AVAILABLE — THE VERDICT STILL STANDS
(2026-07-30, second pass the same day).**  The separating example above is `ℚ`, which is
`2`-divisible with `ℚ[2] = 0` and not torsion — but `ℚ` is not finitely generated, and
`fg_pic` (PROVEN) says `D.Pic` IS.  For a finitely generated abelian group `A` the three
conditions `A = 2·A`, "`A` is finite of odd order", and "`A` is torsion with `A[2] = 0`" are
EQUIVALENT: `A ≅ ℤ^r ⊕ T`, and `A = 2A` forces `r = 0` together with `T = 2T`, i.e. `#T` odd.
So in the presence of `fg_pic` the re-cut trades one leaf for two of the same total strength,
not for two strictly harder ones, and the reason not to make it is different from the recorded
one.

The better reason, and the verdict is unchanged: **the split leaves the hard half untouched.**
"`Pic` is torsion" IS `rank J(ℚ) = 0`, verbatim, so all the deep arithmetic is carried over
intact into the first of the two new leaves.  The second half is worth recording because it is
the only part of this cluster that is pure algebra: `Pic[2] = 0` follows from `f` being
IRREDUCIBLE over `ℚ` (PARI `polisirreducible`, recorded above), because `J[2]` is the group of
even-cardinality subsets of the six Weierstrass points modulo complementation — a Galois-stable
class `{S, Sᶜ}` other than `{∅, all}` needs either a stable even `S`, which transitivity
forbids, or `#S = #Sᶜ = 3`, which is odd and so not in the group at all.  But `PlaceData`
carries no description of `Pic[2]` in terms of the sextic, so even that half means building the
`2`-torsion theory of hyperelliptic Jacobians from the valuation axioms.  Two leaves, one of
them of unchanged difficulty and the other a fresh development: not a cut worth making.

## ATOMICITY AUDIT (2026-07-28) — which AXES were searched, and what would refute each

This leaf has now been left atomic by successive dispatches.  Per the standing rule that an
irreducibility verdict is only as wide as the axis its author searched, here are the axes,
so the next reader can re-check a claim instead of redoing the survey.

* **DESCENT axis (`2`-Selmer) — live, but blocked on MISSING STRUCTURE, not on difficulty.**
  The cut this leaf wants is `J(ℚ)/2J(ℚ) ↪ Sel₂ = 0`, over a descent map
  `δ : Pic → L*/(L*² · ℚ*)` with `L = ℚ[x]/(f)` (a degree-`6` field, `f` being
  irreducible), PINNED to be the genuine `∏ (x(Pᵢ) − θ)`.  **TARGET GROUP CORRECTED
  2026-07-30: this said `L*/L*²`, which is the ODD-degree formula and would make the
  leaf FALSE here.**  The model is the EVEN-degree one (`deg f = 6`), and `f` is
  irreducible over `ℚ`, so `f` has no rational root and the curve has no rational
  Weierstrass point — the hypothesis under which `x − θ` descends to `L*/L*²`.  Without
  one, changing the divisor representing a class multiplies `∏ (x(Pᵢ) − θ)` by an
  element of `ℚ*`, so `L*/L*²` is not a group the map lands in at all and only the
  further quotient by `ℚ*` is well defined (Cassels, *The Mordell–Weil group of curves
  of genus 2*, 1983; Schaefer, *2-descent on the Jacobians of hyperelliptic curves*,
  J. Number Theory 51 (1995), which is the reference for the general even-degree case).
  Note the axis verdict below is UNCHANGED by this: it turns on the genuine `δ` being
  identically zero on `J(ℚ)`, which is a statement about `δ`'s values and not about its
  target.  The cheap way to pin a map — constrain its
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

RE-VERIFIED INDEPENDENTLY IN PARI, 2026-07-30: `f` irreducible (`polisirreducible = 1`);
`poldisc f = −2¹²·13²`, i.e. Magma's `Discriminant(C) = 2²⁰·13²` divided by the model factor
`2⁸` — the SAME factor that relates the two normalisations at level `18`, which is why
neither figure is an error; and `hyperellcharpoly(f mod 3) = T⁴ + 2T³ + T² + 6T + 9`,
reproducing the quoted numerator exactly, hence `#C(𝔽₃) = 3 + 1 + 2 = 6` and
`#J(𝔽₃) = 1 + 2 + 1 + 6 + 9 = 19`.

## DECISION 2026-07-30: NOT DECOMPOSED

Left atomic for the reasons recorded at `X18.two_divisible_pic`, whose re-cut rejection was
re-derived this cycle and holds verbatim here ("`Pic` torsion" + "`J(ℚ)[2] = 0`" is strictly
stronger than `Pic = 2·Pic`, `ℚ` being the separating example).  The descent-axis target
group is corrected below, as at level `18`.

**The `ℚ` justification is WITHDRAWN there and here, and the verdict rests on a different
argument (2026-07-30, second pass)**: `ℚ` is not finitely generated and `fg_pic` (PROVEN) says
`D.Pic` is, and for a finitely generated group the re-cut is EQUIVALENT rather than stronger.
What actually rules the cut out is that "`Pic` is torsion" IS `rank J(ℚ) = 0` verbatim, so the
split carries the whole difficulty into one of its two halves; the other half, `Pic[2] = 0`,
does follow from `f` irreducible over `ℚ` (PARI, this cycle — the six Weierstrass points are a
single Galois orbit, and a stable class `{S, Sᶜ} ≠ {∅, all}` would need `#S` even and stable,
or `#S = 3`, which is odd) but needs a description of `Pic[2]` in terms of the sextic that
`PlaceData` does not carry.  See `X18.two_divisible_pic` for the full statement.

## ATOMICITY AUDIT (2026-07-28)

The axes searched, and the refuting check for each, are written out in full on
`X18.two_divisible_pic`; every one of them applies verbatim here, the two leaves differing
only in the sextic and the good prime.  The load-bearing item is the first: a `2`-descent
cut needs the map `δ : Pic → L*/(L*² · ℚ*)`, `L = ℚ[x]/(f)`, pinned by a CONSTRUCTION, and
pinning it by its values on rational points is powerless because `#Sel₂ = 1` makes the
genuine `δ` identically zero on `J(ℚ)` — so the junk model `δ = 0` meets every such
constraint and reduces the cut to this leaf's own conclusion.  Pinning needs residue fields
`κ(v)` and their norms, which `PlaceData` deliberately does not carry.

**TARGET GROUP CORRECTED 2026-07-30, same correction as at level `18` and for the same
reason**: this said `L*/L*²`, the ODD-degree formula.  `deg f = 6` and `f` is irreducible
over `ℚ` (PARI, `polisirreducible`, this cycle), so there is no rational root and hence no
rational Weierstrass point to move to infinity; the quotient by `ℚ*` is not optional and a
sub-leaf stated over `L*/L*²` would be false.  The axis verdict is unaffected.

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