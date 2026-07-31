/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Velu
-- The two geometric inputs (`nsmul_surjective`, `finite_nsmulKer`) are PROVEN
-- from the division-polynomial development. `PhiPsiCoprime` and
-- `DivisionPolynomial.Degree` are imported PUBLICLY rather than relied on
-- transitively: `TorsionCard.lean` imports both privately, so their lemmas
-- would be unavailable here even in proof bodies.
public import Fermat.FLT.EllipticCurve.TorsionCard
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
-- Only for the `𝔽₅` counterexample in the FALSITY AUDIT of `IsIsogeny.add`.
public import Mathlib.Algebra.Field.ZMod
-- Only for the `𝔽̄₂` counterexamples in the FALSITY AUDITs of `IsRationalMap.add`
-- and `Isogeny.isRationalMap_dualHom`.
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
-- For `exists_homogSubst_of_fibreInvariant`: the two-variable resultant
-- `Res_T (A − c·B, A₁ − w·B₁)` and its `resultant_eq_prod_eval` factorisation over the
-- roots, the `CharZero → Infinite` instance that promotes a cofinite identity to a
-- polynomial identity, and `gcd`/`gcdA`/`gcdB` for the reduction to `IsCoprime A B`.
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.RingTheory.EuclideanDomain

/-!
# Isogenies of elliptic curves as morphisms

This file supplies the vocabulary that the `X_0(N)` descent leaves in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` need and that neither mathlib (at this
pin) nor `~/cs/FLT` provides in any form: **an isogeny as a morphism**, with a
`degree`, a `dual`, a `comp`osition, and an endomorphism **ring**.

## Why a bare group homomorphism is not enough

Everything the development had until now — `exists_quotient_isogeny`,
`exists_velu_quotient_isogeny` — produces only an *additive, Galois-equivariant
map on `ℚ̄`-points*. That is provably too weak to state the conditions the
descent needs, and the failure is not a matter of difficulty: the statement one
would write is **empty**.

The concrete instance, which is the reason this file exists. The Atkin–Lehner
condition at level `125` is `ψ² = [−125]` with `ker ψ` cyclic of order `125`.
Written for an arbitrary additive endomorphism of the point group it says nothing
whatever: as an abstract group `E(ℚ̄)` has torsion `(ℚ/ℤ)²`, whose endomorphism
ring is `M₂(Ẑ)`, and the matrix

  `[[0, −125], [1, 0]]`

squares to `−125` and has cyclic kernel of order `125` **on every elliptic curve
over every field**. So the "condition" would be satisfied by all curves and would
carry none of the arithmetic it was supposed to.

What defeats that junk witness — and the whole class it belongs to — is
`IsRationalMap` below: the requirement that the map be given by *rational
functions in the coordinates*. An abstract endomorphism of `(ℚ/ℤ)²` admits no
such description, so it is not an element of `endSubring`, and `ψ * ψ = -125` in
`End W` is a genuine assertion of complex multiplication.

## Design, and why it is this one

The base is a field `F` (in the application, `AlgebraicClosure ℚ`). Two choices
are load-bearing:

* **The rational-function certificate is a `Prop`, not data.** `IsIsogeny φ` is a
  predicate on `φ : W.Point →+ W'.Point`, so `Isogeny W W'` is a *subtype* and two
  isogenies are equal exactly when their point maps are. Had the polynomials been
  fields of a structure, one map with two presentations would give two distinct
  terms and the ring axioms on `End` would fail.

* **`degree` is the cardinality of the kernel.** In characteristic zero every
  isogeny is separable, so this agrees with the classical degree, and — unlike a
  degree read off the presenting polynomials — it is manifestly a function of the
  point map alone, so it needs no well-definedness lemma. The pay-off is large:
  multiplicativity of the degree, the construction of the dual and
  `ψ̂ ∘ ψ = [deg ψ]` all become pure group theory over the two geometric inputs
  `nsmul_surjective` and `finite_nsmulKer`. **This file is therefore correct only
  in characteristic zero**, which is where all its consumers live.

## Main definitions

* `WeierstrassCurve.IsRationalMap` — the algebraicity certificate.
* `WeierstrassCurve.IsIsogeny` — rational, plus surjective with finite kernel
  away from the zero map.
* `WeierstrassCurve.Isogeny` — the subtype; `WeierstrassCurve.Isogeny.degree`.
* `WeierstrassCurve.endSubring` — `End W` as a `Subring (AddMonoid.End W.Point)`,
  hence a `Ring`, in which `(n : End W)` **is** multiplication by `n` (`rfl`, see
  `End.intCast_apply`).
* `WeierstrassCurve.Isogeny.dualHom` / `dual` — the dual isogeny, with
  `Isogeny.dualHom_comp` giving `ψ̂ ∘ ψ = [deg ψ]`.

## `IsIsogeny` is only usable over an algebraically closed base

`IsIsogeny.add` was FALSE as originally cut, and `endSubring` therefore did not
define a subring. The refutation is machine-checked in
`WeierstrassCurve.NotIsIsogenyAdd` and written out in the FALSITY AUDIT next to
`IsIsogeny.add`; in one line, `IsIsogeny.id` holds over every field, so the
unconditional `IsIsogeny.add` asserts that `[2] = id + id` is surjective on
`W(F)`, which fails already for `y² = x³ - x` over `𝔽₅`.

`IsIsogeny.add`, `endSubring`, `End` and the `End.*` API therefore carry
`[IsAlgClosed F]`, matching `nsmul_surjective`, `finite_nsmulKer` and
`Isogeny.dual`, which always did. All consumers work over `AlgebraicClosure ℚ`,
so nothing downstream changes. `IsIsogeny.zero`, `.id`, `.neg` and `.comp` remain
unconditional and remain proven.

## …and only for a NONSINGULAR `W`: `[W.IsElliptic]` is required too

**`[IsAlgClosed F]` alone is not enough** (2026-07-26). `Affine F` is *any*
Weierstrass curve, and mathlib gives `Affine.Point` its group structure with no
nonsingularity hypothesis, so `W` may be a singular cubic. Over `𝔽̄₂` the cuspidal
`y² = x³` has `negY x y = -y = y`, hence `-P = P`, hence an infinite point group of
exponent 2 — an `𝔽₂`-vector space, which is **not divisible** and so has subgroups
of index 2. Since `IsRationalMap φ` constrains only the points with `φ P ≠ 0`, a
homomorphism onto a two-element image satisfies it by a **constant** witness and
asserts nothing at all.

That refutes `IsRationalMap.add` and `IsRationalMap.isIsogeny` as they stood;
both refutations are machine-checked and axiom-clean in
`WeierstrassCurve.NotIsRationalMapAdd`. Those two leaves, and with them
`IsIsogeny.add`, `endSubring`, `End` and the whole `End.*` API, now carry
`[W.IsElliptic]` as well. `MazurTorsion.lean`'s consumers already work with a curve
carrying `[E.IsElliptic]`, so again nothing downstream is lost.

## …and the DUAL needs `CharZero`, which nothing used to enforce

`degree` is `Nat.card (ker φ)`, which equals the classical degree only for
*separable* isogenies — the design note above says exactly that, and until
2026-07-26 **no hypothesis anywhere enforced it**. `Isogeny.isRationalMap_dualHom`
is where that bites, and it made the leaf FALSE: over `𝔽̄₂` the Frobenius on the
nonsingular curve `y² + y = x³` is rational, surjective and injective on points, so
it is an isogeny of `degree 1`, and `dualHom` therefore descends `[1] = id` and
claims the *inverse Frobenius* `x ↦ √x` is a morphism. A parity argument on
`X · B(X²) = A(X²)` refutes that. Machine-checked and axiom-clean in
`WeierstrassCurve.Isogeny.NotIsRationalMapDualHom`; note that `[IsAlgClosed F]` and
`[W.IsElliptic]` are both satisfied there, so neither of the earlier repairs helps.

`isRationalMap_dualHom`, `dual`, `dual_toHom` and `dual_comp` therefore carry
`[CharZero F]`. Nothing else in the file needs it: `IsIsogeny.comp`, `endSubring`,
`End` and `End.sq_eq_intCast_iff` are about rational maps, surjectivity and finite
kernels, all of which behave in characteristic `p`.

## Open leaves left by this file

`exists_homogSubst_of_fibreInvariant`. That ONE is the whole remaining frontier of
this module; the list is stated from the file's ACTUAL sorry set as merged
(2026-07-27), not inherited from either side of a merge. Two earlier versions of
this paragraph were both stale — one still listed `IsRationalMap.add_of_x_ne`, the
other `Isogeny.isRationalMap_dualHom`, and BOTH of those are now proven.

**`Isogeny.isRationalMap_dualHom` is PROVEN** (2026-07-27), by descent — see
`IsRationalMap.descend` and the section docstring above it. Its replacement leaf,
`exists_homogSubst_of_fibreInvariant`, is PURE ONE-VARIABLE ALGEBRA over `F[X]`:
"a rational function constant on the fibres of `A/B` is a rational function of
`A/B`". Nothing about curves, groups, `Isogeny` or `End` survives into it, which
also means `#print axioms` says something useful about it — unlike anything phrased
through `End`, where the literal `rfl` lemma `End.coe_add_apply` already reports
`sorryAx`. Four new lemmas were proven on the way and are reusable:
`isRationalMap_mulByHom` (`[n]` is rational, for every `n`),
`IsRationalMap.of_cofinite` (a certificate valid off a finite set of `x`-values is a
certificate), `yCert_antiInvariant` (a `y`-certificate acts as a SCALAR on
`2y + a₁x + a₃`, with no additive term) and `eq_zero_of_constY`.

**`IsRationalMap.add` is PROVEN** (2026-07-27) and so, as of the same day, is
every one of its parts: both branches (`IsRationalMap.add_self` and
`IsRationalMap.add_of_ne`), the whole DOUBLING branch, and finally the CHORD
branch `IsRationalMap.add_of_x_ne`. The sum is closed.

How the chord branch closed. It rests on three pure-field identities stated away
from the curve — `chordAdd_slope_core` (the slope with its denominator cleared),
`chordAdd_x_core` (Step 2: `x` of the chord sum, with `y²` reduced by the source
curve's equation so that only `y¹` survives) and `chordAdd_y_core` (Step 4) — each
a single `linear_combination`. The geometry is entirely in Step 3, `U = 0`: apply
the Step-2 identity at `P` and at `-P`, whose sums have the SAME `x`, and subtract;
that gives `U(t) · (2y + a₁t + a₃) = 0`, and the second factor vanishes only on the
2-torsion, finite by `finite_nsmulKer`. Since `exists_point_veluPointX_eq` supplies
a point over every `t`, `U` has infinitely many roots and is `0`. Step 5 is
technique 1 of this docstring, with the bad locus cut out by
`B₁B₂E₁E₂G · ∏ (X - s)` over the `x`-coordinates of the two kernels
(`IsRationalMap.finite_ker`).

One recorded expectation turned out to be false and is corrected at the
declaration: `hsum` is **not** needed. Two points with different `x`-coordinates
cannot sum to `0`, so `(φ + ψ) P ≠ 0` is automatic on the good locus and
`ker (φ + ψ)` never enters.

How the doubling branch closed, since the route generalises. `φ + φ = φ ∘ [2]_W`
puts the doubling on the SOURCE curve, where `IsRationalMap.comp` applies and
`[W.IsElliptic]` is available — that is what removed the awkward `[W'.IsElliptic]`
question the branch used to carry. Then `[2]` splits into its two coordinates:
`veluPointX_nsmul` (PROVEN for general `n`, every characteristic, no hypothesis on
the field) transports `TorsionCard.exists_smul_some_eq` into the `veluPointX`
spelling, and `exists_y_witness_two` does the tangent-line algebra over
`addY_two_core`. **Mathlib's bivariate `ωₙ` — the general `y`-coordinate division
polynomial — is an explicit TODO in its own module docstring, and is absent from
`~/cs/FLT` and from this project too**; it was not needed, because only `n = 2` is
ever required here (general `[n]` follows from `IsRationalMap.add` by induction on
`[n] = [n-1] + [1]`, and `n = 2` is the one case that induction cannot reach).

`IsRationalMap.isIsogeny` was on this list and is now PROVEN and axiom-clean, as
are the two halves it was split into for ordering reasons —
`IsRationalMap.finite_ker` and `IsRationalMap.surjective`, which live in the
*Consequences of divisibility* section so that they are available BEFORE
`IsIsogeny` is defined. `IsRationalMap.add_of_ne` needs `finite_ker` and would
otherwise be blocked purely by declaration order.

**`IsRationalMap.isIsogeny` is PROVEN and axiom-clean**
(2026-07-27), so `IsIsogeny.add` is now open only through `IsRationalMap.add`.
Its proof rests on four new helpers collected under *Consequences of
divisibility* below — `exists_point_veluPointX_eq`,
`finite_veluPointX_preimage`, `finite_range_of_constX` and
`eq_zero_of_finite_range` — and on nothing else geometric. Two of them are worth
reusing: `finite_veluPointX_preimage` (fibres of `x` have ≤ 2 points, so a finite
set of `x`-values pulls back to a finite set of points, over ANY Weierstrass
curve) and `eq_zero_of_finite_range` (divisibility kills every homomorphism out
of `W.Point` with finite image — this is the single step that both `𝔽̄₂`
counterexamples below break).

That proof also forced the `### The two geometric inputs` section to move
ABOVE the leaves, since `eq_zero_of_finite_range` consumes `nsmul_surjective`.
The move is verbatim; nothing in that section was edited.

`IsRationalMap.neg` was on this list and is now PROVEN. So, as of 2026-07-26,
are `nsmul_surjective`, `finite_nsmulKer` and `Isogeny.degree_comp` (see the
two sections below), and `IsRationalMap.comp` — now **PROVEN and axiom-clean**,
hence so is `IsIsogeny.comp`. It rests on `homogSubst` (substitute `A/B`, clear
denominators), `eval_homogSubst`, `exists_const_of_homogSubst_eq_zero` (the
degeneracy criterion) and `IsRationalMap.comp_of_constX` (the constant-`x`
case) — all proven here. `IsIsogeny.add` was on this list too; it is now PROVEN
from `IsRationalMap.add` and `IsRationalMap.isIsogeny`, after being refuted and
restated (above).

**All three of those leaves were REFUTED as originally stated, and restated, on
2026-07-26** — machine-checked counterexamples in `NotIsIsogenyAdd`,
`NotIsRationalMapAdd` and `Isogeny.NotIsRationalMapDualHom`. Their present
hypotheses are load-bearing, not decoration; do not weaken them without reading
those audits.

## Correction to the characteristic caveat above

The design note says this file is "correct only in characteristic zero". That
remains true of the *interpretation* of `degree` as the classical degree (which
needs separability) — and the FALSITY AUDIT of `Isogeny.isRationalMap_dualHom`
below shows that caveat has real teeth, since Frobenius makes the dual
construction outright FALSE in characteristic `p`. But it is **not** a
restriction on the two geometric
inputs: both are proven below over an arbitrary algebraically closed field, in
every characteristic, with no hypothesis beyond `n ≠ 0`. The project's
`TorsionCard.smul_surjective` needs `(n : k) ≠ 0` only because it works over a
*separably* closed field, where the root is produced by
`exists_root_of_derivative_ne_zero` and the derivative of
`Φₙ − ξ·ΨSqₙ` genuinely vanishes when `char k ∣ n`. Over an algebraically closed
field no separability is needed: the polynomial is monic of degree `n²` (its
`n²`-coefficient is `1`, `WeierstrassCurve.coeff_Φ`, while `ΨSqₙ` has degree at
most `n² − 1`), so it has a root outright, and the `y`-fibre quadratic likewise.

## Two techniques from `IsRationalMap.comp` that the remaining leaves will want

1. **Kill a bad locus by multiplying the witness through by its defining
   polynomial.** `IsRationalMap`'s certificate must hold at *every* point, but a
   derivation typically only works where some denominator `B` is nonzero. Taking
   the witness pair to be `(A'' * B, B'' * B)` instead of `(A'', B'')` repairs this
   for free: where `B` vanishes both sides of the certificate become `0`. This is
   used in `comp_of_constX` and is why `eval_homogSubst` deliberately carries no
   nonvanishing hypothesis.

2. **The only obstruction to a substituted witness is a constant `x`-coordinate.**
   The `B ≠ 0` side condition of `IsRationalMap` is the whole difficulty in
   `comp`, and `exists_const_of_homogSubst_eq_zero` reduces it to a single
   degenerate case. Expect the same shape elsewhere.
-/


@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W W' W'' : Affine F}

/-! ### The algebraicity certificate -/

/-- `IsRationalMap φ` says that the map `φ` on points is computed, away from its
kernel, by **rational functions in the coordinates**: there are polynomials
`A, B, C, D, E` over the base field with

  `x(φ P) = A(x P) / B(x P)`,  `y(φ P) = (C(x P) · y P + D(x P)) / E(x P)`,

written multiplicatively so that no division is needed. This is the normal form
of a morphism of Weierstrass curves in characteristic zero.

This predicate is the entire faithfulness content of `IsIsogeny`. Without it,
`End W` would be the endomorphism ring of an abstract abelian group — see the
`M₂(Ẑ)` discussion in the module docstring — and every condition stated in it
would be vacuous. -/
def IsRationalMap (φ : W.Point →+ W'.Point) : Prop :=
  ∃ A B C D E : F[X], B ≠ 0 ∧ E ≠ 0 ∧
    ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) ∧
      veluPointY (φ P) * E.eval (veluPointX P)
        = C.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)

/-- The zero map is rational: its defining condition is vacuous. -/
theorem IsRationalMap.zero : IsRationalMap (0 : W.Point →+ W'.Point) :=
  ⟨0, 1, 0, 0, 1, one_ne_zero, one_ne_zero, fun P hP =>
    absurd (AddMonoidHom.zero_apply P) hP⟩

/-- The identity is rational, with `A = X`, `B = C = E = 1`, `D = 0`. -/
theorem IsRationalMap.id : IsRationalMap (AddMonoidHom.id W.Point) := by
  refine ⟨X, 1, 1, 0, 1, one_ne_zero, one_ne_zero, fun P _ => ?_⟩
  simp

/-- A negated rational map is rational.

`x(-Q) = x(Q)`, so `A, B` are unchanged; `y(-Q) = negY (x Q) (y Q)
= -y(Q) - a₁ x(Q) - a₃`, so substituting `x(φ P) = A/B` and clearing the extra
denominator gives the `y`-witness
`(C', D', E') = (-C·B, -D·B - a₁·A·E - a₃·B·E, E·B)`. -/
theorem IsRationalMap.neg {φ : W.Point →+ W'.Point} (h : IsRationalMap φ) :
    IsRationalMap (-φ) := by
  obtain ⟨A, B, C, D, E, hB, hE, hcert⟩ := h
  refine ⟨A, B, -(C * B),
    -(D * B) - Polynomial.C W'.a₁ * A * E - Polynomial.C W'.a₃ * B * E, E * B,
    hB, mul_ne_zero hE hB, fun P hP => ?_⟩
  have hφP : φ P ≠ 0 := fun hc => hP (by show -(φ P) = 0; rw [hc, neg_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  have hnegapp : (-φ) P = -(φ P) := rfl
  refine ⟨?_, ?_⟩
  · rw [hnegapp, velu_pointX_neg]
    exact hx
  · rw [hnegapp, velu_pointY_neg _ hφP]
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
      Polynomial.eval_C]
    linear_combination (-(B.eval (veluPointX P))) * hy
      - (W'.a₁ * E.eval (veluPointX P)) * hx

/-! #### Clearing denominators after substitution

`IsRationalMap.comp` needs to substitute `A/B` into the certificate of the second
map and clear denominators. `homogSubst A B d Q` is exactly that: `Q(A/B)`
multiplied through by `B ^ d`. The two facts about it that matter are
`eval_homogSubst` (what it computes) and `exists_const_of_homogSubst_eq_zero` (when
it degenerates to the zero polynomial, which is the only thing that can obstruct
the `B ≠ 0` side condition of `IsRationalMap`). -/

/-- `homogSubst A B d Q` is `Q(A/B)` with denominators cleared to degree `d`, i.e.
`B ^ d * Q (A / B)` written without division. -/
noncomputable def homogSubst (A B : F[X]) (d : ℕ) (Q : F[X]) : F[X] :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (Q.coeff i) * A ^ i * B ^ (d - i)

omit [DecidableEq F] in
/-- What `homogSubst` computes. Note there is **no** nonvanishing hypothesis on
`B.eval t`: the identity `u * B.eval t = A.eval t` is enough, and both sides
degenerate to `0` together when `B.eval t = 0`. That is what lets the composite
certificate hold at *every* point rather than away from a bad set. -/
theorem eval_homogSubst {A B Q : F[X]} {d : ℕ} (hd : Q.natDegree ≤ d) {t u : F}
    (hu : u * B.eval t = A.eval t) :
    (homogSubst A B d Q).eval t = (B.eval t) ^ d * Q.eval u := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd) (x := u), Finset.mul_sum]
  simp only [homogSubst, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hsplit : (B.eval t) ^ d = (B.eval t) ^ i * (B.eval t) ^ (d - i) := by
    rw [← pow_add]; congr 1; omega
  rw [← hu, mul_pow, hsplit]
  ring

omit [DecidableEq F] in
theorem homogSubst_eq_pow_mul {A B Q : F[X]} {d : ℕ} (hd : Q.natDegree ≤ d) :
    homogSubst A B d Q = B ^ (d - Q.natDegree) * homogSubst A B Q.natDegree Q := by
  have hsub : Finset.range (Q.natDegree + 1) ⊆ Finset.range (d + 1) := fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.succ_le_succ hd))
  have hzero : ∀ i ∈ Finset.range (d + 1), i ∉ Finset.range (Q.natDegree + 1) →
      Polynomial.C (Q.coeff i) * A ^ i * B ^ (d - i) = 0 := by
    intro i _ hi
    have hlt : Q.natDegree < i := by
      simp only [Finset.mem_range, not_lt] at hi; omega
    rw [Q.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul, zero_mul]
  unfold homogSubst
  rw [Finset.mul_sum, ← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hb : B ^ (d - i) = B ^ (d - Q.natDegree) * B ^ (Q.natDegree - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hb]; ring

omit [DecidableEq F] in
theorem homogSubst_mul_left (g A B Q : F[X]) (m : ℕ) :
    homogSubst (g * A) (g * B) m Q = g ^ m * homogSubst A B m Q := by
  unfold homogSubst
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hg : g ^ m = g ^ i * g ^ (m - i) := by rw [← pow_add]; congr 1; omega
  rw [mul_pow, mul_pow, hg]; ring

omit [DecidableEq F] in
/-- The coprime core of the degeneracy criterion: substituting a **coprime** pair
into a nonzero `Q` can only give `0` when both members of the pair are constants.

`B` divides the top term `C (Q.coeff m) * A ^ m` of the sum, so by coprimality it
divides the nonzero constant `Q.coeff m` and is a unit; the remaining identity is
then `Q.comp (C b⁻¹ * A) = 0`, which forces `A` constant by
`Polynomial.comp_eq_zero_iff`. -/
theorem natDegree_eq_zero_of_coprime_homogSubst {A B Q : F[X]} (hcop : IsCoprime A B)
    (hQ : Q ≠ 0) (h : homogSubst A B Q.natDegree Q = 0) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  set m := Q.natDegree with hm
  have hqm : Q.coeff m ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hQ
  have hsplit : homogSubst A B m Q
      = (∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i))
        + Polynomial.C (Q.coeff m) * A ^ m := by
    unfold homogSubst
    rw [Finset.sum_range_succ]
    simp
  have hdvdsum : B ∣ ∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i) := by
    refine Finset.dvd_sum fun i hi => ?_
    have : 1 ≤ m - i := by have := Finset.mem_range.1 hi; omega
    exact Dvd.dvd.mul_left (dvd_pow_self B (by omega)) _
  have hdvd : B ∣ Polynomial.C (Q.coeff m) * A ^ m := by
    have hrw : Polynomial.C (Q.coeff m) * A ^ m
        = homogSubst A B m Q
          - ∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i) := by
      rw [hsplit]; ring
    rw [hrw, h, zero_sub]
    exact dvd_neg.2 hdvdsum
  have hBdvd : B ∣ Polynomial.C (Q.coeff m) :=
    (hcop.symm.pow_right (n := m)).dvd_of_dvd_mul_right hdvd
  have hBunit : IsUnit B :=
    isUnit_of_dvd_unit hBdvd (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hqm))
  have hBdeg : B.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hBunit
  refine ⟨?_, hBdeg⟩
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.1 hBdeg
  have hbne : b ≠ 0 := by
    rintro rfl
    exact hBunit.ne_zero (by rw [← hb, map_zero])
  have hscalar : ∀ i ≤ m, b ^ m * Q.coeff i * b⁻¹ ^ i = Q.coeff i * b ^ (m - i) := by
    intro i hi
    have hsplitb : b ^ m = b ^ (m - i) * b ^ i := by rw [← pow_add]; congr 1; omega
    have hinv : b ^ i * b⁻¹ ^ i = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hbne, one_pow]
    calc b ^ m * Q.coeff i * b⁻¹ ^ i
        = Q.coeff i * b ^ (m - i) * (b ^ i * b⁻¹ ^ i) := by rw [hsplitb]; ring
      _ = Q.coeff i * b ^ (m - i) := by rw [hinv, mul_one]
  have hce : Q.comp (Polynomial.C b⁻¹ * A)
      = ∑ i ∈ Finset.range (m + 1), Polynomial.C (Q.coeff i) * (Polynomial.C b⁻¹ * A) ^ i :=
    Polynomial.eval₂_eq_sum_range' Polynomial.C (Nat.lt_succ_self m) (Polynomial.C b⁻¹ * A)
  have hcomp : Polynomial.C (b ^ m) * Q.comp (Polynomial.C b⁻¹ * A) = 0 := by
    rw [hce, Finset.mul_sum, ← h]
    unfold homogSubst
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [← hb, mul_pow, ← Polynomial.C_pow]
    calc Polynomial.C (b ^ m)
          * (Polynomial.C (Q.coeff i) * (Polynomial.C (b⁻¹ ^ i) * A ^ i))
        = Polynomial.C (b ^ m * Q.coeff i * b⁻¹ ^ i) * A ^ i := by
          simp only [Polynomial.C_mul]; ring
      _ = Polynomial.C (Q.coeff i * b ^ (m - i)) * A ^ i := by rw [hscalar i hi']
      _ = Polynomial.C (Q.coeff i) * A ^ i * Polynomial.C b ^ (m - i) := by
          simp only [Polynomial.C_mul, Polynomial.C_pow]; ring
  have hQcomp : Q.comp (Polynomial.C b⁻¹ * A) = 0 := by
    have hCb : (Polynomial.C (b ^ m) : F[X]) ≠ 0 := by simpa using pow_ne_zero m hbne
    exact (mul_eq_zero.1 hcomp).resolve_left hCb
  rcases Polynomial.comp_eq_zero_iff.1 hQcomp with h0 | ⟨_, hconst⟩
  · exact absurd h0 hQ
  · have hdeg : (Polynomial.C b⁻¹ * A).natDegree = 0 := by
      rw [hconst]; exact Polynomial.natDegree_C _
    rwa [Polynomial.natDegree_C_mul (inv_ne_zero hbne)] at hdeg

/-- **The degeneracy criterion.** `homogSubst A B d Q` can vanish for a nonzero `Q`
only when `A / B` is a *constant* rational function.

This is the whole reason `IsRationalMap.comp` needs a case split: the composite
witness is `homogSubst A B d B'`, and its `≠ 0` side condition can fail exactly when
the first map has a constant `x`-coordinate. -/
theorem exists_const_of_homogSubst_eq_zero {A B Q : F[X]} (hB : B ≠ 0) (hQ : Q ≠ 0)
    {d : ℕ} (hd : Q.natDegree ≤ d) (h : homogSubst A B d Q = 0) :
    ∃ c : F, A = Polynomial.C c * B := by
  classical
  have hm : homogSubst A B Q.natDegree Q = 0 := by
    rw [homogSubst_eq_pow_mul hd] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hB)
  letI : GCDMonoid F[X] := EuclideanDomain.gcdMonoid F[X]
  set g := GCDMonoid.gcd A B with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_right hB
  have hA : A = g * (A / g) :=
    (EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left A B)).symm
  have hBeq : B = g * (B / g) :=
    (EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right A B)).symm
  have hcop : IsCoprime (A / g) (B / g) := isCoprime_div_gcd_div_gcd hB
  have hsub : homogSubst (A / g) (B / g) Q.natDegree Q = 0 := by
    have hml := homogSubst_mul_left g (A / g) (B / g) Q Q.natDegree
    rw [← hA, ← hBeq, hm] at hml
    exact (mul_eq_zero.1 hml.symm).resolve_left (pow_ne_zero _ hgne)
  obtain ⟨hAd, hBd⟩ := natDegree_eq_zero_of_coprime_homogSubst hcop hQ hsub
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 hAd
  obtain ⟨b, hbb⟩ := Polynomial.natDegree_eq_zero.1 hBd
  have hbne : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hbb
    exact hB (by rw [hBeq, ← hbb, mul_zero])
  refine ⟨a / b, ?_⟩
  rw [hA, hBeq, ← ha, ← hbb, ← mul_assoc, mul_comm (Polynomial.C (a / b)) g, mul_assoc,
    ← Polynomial.C_mul, div_mul_cancel₀ a hbne]

omit [DecidableEq F] in
/-- A nonzero point is determined by its two coordinates. -/
theorem eq_of_veluPoint_eq {Q₁ Q₂ : W.Point} (h1 : Q₁ ≠ 0) (h2 : Q₂ ≠ 0)
    (hx : veluPointX Q₁ = veluPointX Q₂) (hy : veluPointY Q₁ = veluPointY Q₂) : Q₁ = Q₂ := by
  rcases Q₁ with _ | ⟨x₁, y₁, hh₁⟩
  · exact absurd rfl h1
  rcases Q₂ with _ | ⟨x₂, y₂, hh₂⟩
  · exact absurd rfl h2
  exact velu_point_some_eq hx hy

omit [DecidableEq F] in
/-- Two nonzero points with the same `x`-coordinate are equal or negatives — the
fibres of `x` have at most two elements. This is `Affine.Point.X_eq_iff` phrased
through `veluPointX`. -/
theorem eq_or_eq_neg_of_veluPointX_eq {Q₁ Q₂ : W.Point} (h1 : Q₁ ≠ 0) (h2 : Q₂ ≠ 0)
    (hx : veluPointX Q₁ = veluPointX Q₂) : Q₁ = Q₂ ∨ Q₁ = -Q₂ := by
  rcases Q₁ with _ | ⟨x₁, y₁, hh₁⟩
  · exact absurd rfl h1
  rcases Q₂ with _ | ⟨x₂, y₂, hh₂⟩
  · exact absurd rfl h2
  exact Affine.Point.X_eq_iff.1 hx

/-- The composite is rational in the degenerate case, where the first map has a
*constant* `x`-coordinate away from the zeros of `B`.

This is the residue of `IsRationalMap.comp` that the substitution argument cannot
reach, and it is genuinely different in kind: there is no denominator to clear,
because `x(φ P) = c` is already constant, and the content is instead the geometry of
the (at most two-point) fibre of `x` over `c`.

Note `ψ` needs **no** rationality hypothesis here: only two points of `W'` have
`x`-coordinate `c`, namely some `R` and `-R`, so `φ` maps `{P : B(x P) ≠ 0}` into
`{R, -R}` and `ψ ∘ φ` maps it into `{ψ R, -ψ R}` for a completely arbitrary
homomorphism `ψ`. Hence:

* `x (ψ (φ P))` is the single constant `e := x (ψ R)`, and `(C e * B, B)` is an
  `x`-witness — at the zeros of `B` both sides are `0`, which is why the factor `B`
  must be kept;
* `y (ψ (φ P))` takes the two values `y(ψ R)` and `y(-ψ R)`, and which one occurs is
  determined by `y(φ P)`, which is rational in `(x P, y P)` through `φ`'s own
  `y`-certificate. The affine interpolation `α · y(R) + β = y(ψ R)`,
  `α · y(-R) + β = y(-ψ R)` gives the `y`-witness `(α Cx B, (α D + β E) B, E B)`.

The interpolation needs no case split on `R = -R`: when `y(R) = y(-R)` the slope
`α` is `0/0 = 0` in Lean, and that is the correct answer, because `y(R) = y(-R)`
forces `R = -R`, hence `ψ R = ψ (-R) = -ψ R` and the two interpolation conditions
coincide. -/
theorem IsRationalMap.comp_of_constX {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    {B Cx D E : F[X]} (hB : B ≠ 0) (hE : E ≠ 0) (c : F)
    (hxc : ∀ P : W.Point, φ P ≠ 0 → B.eval (veluPointX P) ≠ 0 → veluPointX (φ P) = c)
    (hyc : ∀ P : W.Point, φ P ≠ 0 →
      veluPointY (φ P) * E.eval (veluPointX P)
        = Cx.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)) :
    IsRationalMap (ψ.comp φ) := by
  classical
  by_cases hex : ∃ P₀ : W.Point, ψ (φ P₀) ≠ 0 ∧ B.eval (veluPointX P₀) ≠ 0
  swap
  · -- No point contributes: `B` vanishes wherever the composite is nonzero.
    refine ⟨0, B, 0, 0, B, hB, hB, fun P hP => ?_⟩
    have hb : B.eval (veluPointX P) = 0 := by
      by_contra hb
      exact hex ⟨P, hP, hb⟩
    simp [hb]
  obtain ⟨P₀, hS₀, hB₀⟩ := hex
  have hR₀ : φ P₀ ≠ 0 := fun h => hS₀ (by rw [h, map_zero])
  -- Affine interpolation of `y ∘ ψ` across the two-element fibre `{φ P₀, -(φ P₀)}`.
  obtain ⟨α, β, hlin, hlin'⟩ : ∃ α β : F,
      α * veluPointY (φ P₀) + β = veluPointY (ψ (φ P₀)) ∧
        α * veluPointY (-(φ P₀)) + β = veluPointY (-(ψ (φ P₀))) := by
    set yR := veluPointY (φ P₀) with hyRdef
    set yR' := veluPointY (-(φ P₀)) with hyRdef'
    set yS := veluPointY (ψ (φ P₀)) with hySdef
    set yS' := veluPointY (-(ψ (φ P₀))) with hySdef'
    refine ⟨(yS - yS') / (yR - yR'), yS - (yS - yS') / (yR - yR') * yR, by ring, ?_⟩
    by_cases hyy : yR - yR' = 0
    · -- `y(R) = y(-R)` forces `R = -R`, hence `ψ R = -ψ R` and the two conditions agree.
      have hRR : φ P₀ = -(φ P₀) :=
        eq_of_veluPoint_eq hR₀ (neg_ne_zero.2 hR₀) (velu_pointX_neg _).symm (sub_eq_zero.1 hyy)
      have hSS : ψ (φ P₀) = -(ψ (φ P₀)) := by
        conv_lhs => rw [hRR]
        rw [map_neg]
      have hy : yS = yS' := congrArg veluPointY hSS
      rw [hyy, div_zero, hy]
      ring
    · have hmul : (yS - yS') / (yR - yR') * (yR - yR') = yS - yS' := div_mul_cancel₀ _ hyy
      linear_combination -hmul
  -- The pointwise description of the composite on the good locus.
  have key : ∀ P : W.Point, ψ (φ P) ≠ 0 → B.eval (veluPointX P) ≠ 0 →
      veluPointX (ψ (φ P)) = veluPointX (ψ (φ P₀)) ∧
        veluPointY (ψ (φ P)) = α * veluPointY (φ P) + β := by
    intro P hP hBP
    have hφP : φ P ≠ 0 := fun h => hP (by rw [h, map_zero])
    have hxeq : veluPointX (φ P) = veluPointX (φ P₀) := by
      rw [hxc P hφP hBP, hxc P₀ hR₀ hB₀]
    rcases eq_or_eq_neg_of_veluPointX_eq hφP hR₀ hxeq with h | h
    · rw [h]
      exact ⟨rfl, hlin.symm⟩
    · have hψeq : ψ (φ P) = -(ψ (φ P₀)) := by rw [h, map_neg]
      rw [hψeq, h]
      exact ⟨velu_pointX_neg _, hlin'.symm⟩
  refine ⟨Polynomial.C (veluPointX (ψ (φ P₀))) * B, B,
    Polynomial.C α * Cx * B, (Polynomial.C α * D + Polynomial.C β * E) * B, E * B,
    hB, mul_ne_zero hE hB, fun P hP => ?_⟩
  by_cases hBP : B.eval (veluPointX P) = 0
  · simp [hBP]
  have hPc : ψ (φ P) ≠ 0 := hP
  have hφP : φ P ≠ 0 := fun h => hPc (by rw [h, map_zero])
  obtain ⟨hkx, hky⟩ := key P hPc hBP
  refine ⟨?_, ?_⟩
  · simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show veluPointX ((ψ.comp φ) P) = veluPointX (ψ (φ P)) from rfl, hkx]
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
    rw [show veluPointY ((ψ.comp φ) P) = veluPointY (ψ (φ P)) from rfl, hky]
    linear_combination (α * B.eval (veluPointX P)) * (hyc P hφP)

/-- The composite of two rational maps is rational.

Away from the degenerate case this is exactly substitution: `x (ψ (φ P))` satisfies
`ψ`'s certificate at `u = x (φ P)`, and `u` satisfies `φ`'s certificate at
`t = x P`, so multiplying `ψ`'s certificate through by `B(t) ^ d` replaces every
`A'(u)`, `B'(u)` by `homogSubst A B d A'`, `homogSubst A B d B'` evaluated at `t`.
The same computation on the `y`-side uses `φ`'s `y`-certificate to rewrite
`y(φ P) · E(t)` as `C(t) y(P) + D(t)`.

The side conditions `B'' ≠ 0`, `E'' ≠ 0` are where the work is, and
`exists_const_of_homogSubst_eq_zero` shows they can only fail when `x ∘ φ` is
constant — which is `IsRationalMap.comp_of_constX`. -/
theorem IsRationalMap.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (ψ.comp φ) := by
  obtain ⟨A, B, Cx, D, E, hB, hE, hcert⟩ := hφ
  by_cases hconst : ∃ c : F, A = Polynomial.C c * B
  · obtain ⟨c, hcc⟩ := hconst
    refine IsRationalMap.comp_of_constX (Cx := Cx) (D := D) hB hE c
      (fun P hP hBP => ?_) (fun P hP => (hcert P hP).2)
    have hx := (hcert P hP).1
    rw [hcc] at hx
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact mul_right_cancel₀ hBP hx
  obtain ⟨A', B', C', D', E', hB', hE', hcert'⟩ := hψ
  set d := max A'.natDegree B'.natDegree with hd
  set d' := max (max C'.natDegree D'.natDegree) E'.natDegree with hd'
  have hne : ∀ Q : F[X], Q ≠ 0 → ∀ n : ℕ, Q.natDegree ≤ n → homogSubst A B n Q ≠ 0 :=
    fun Q hQ n hn hz => hconst (exists_const_of_homogSubst_eq_zero hB hQ hn hz)
  refine ⟨homogSubst A B d A', homogSubst A B d B',
    homogSubst A B d' C' * Cx,
    homogSubst A B d' C' * D + homogSubst A B d' D' * E,
    homogSubst A B d' E' * E,
    hne B' hB' d (le_max_right _ _),
    mul_ne_zero (hne E' hE' d' (le_max_right _ _)) hE, fun P hP => ?_⟩
  have hφP : φ P ≠ 0 := fun hcz => hP (by show ψ (φ P) = 0; rw [hcz, map_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  obtain ⟨hx', hy'⟩ := hcert' (φ P) hP
  have hxA : (homogSubst A B d A').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d * A'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_left _ _) hx
  have hxB : (homogSubst A B d B').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d * B'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_right _ _) hx
  have hyC : (homogSubst A B d' C').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * C'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hyD : (homogSubst A B d' D').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * D'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hyE : (homogSubst A B d' E').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * E'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_right _ _) hx
  refine ⟨?_, ?_⟩
  · rw [hxA, hxB]
    linear_combination (B.eval (veluPointX P)) ^ d * hx'
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, hyC, hyD, hyE]
    linear_combination
      ((B.eval (veluPointX P)) ^ d' * E.eval (veluPointX P)) * hy'
        + ((B.eval (veluPointX P)) ^ d' * C'.eval (veluPointX (φ P))) * hy

/-! ### The two geometric inputs -/

/-! Both inputs are PROVEN (2026-07-26) from the division-polynomial development
in `TorsionCard.lean` / `PhiPsiCoprime.lean`, over an arbitrary algebraically
closed field and in every characteristic.

Note on the `(V⁄F)` spelling below. `TorsionCard.lean` states everything for the
base-changed curve `(E⁄k)`, and `(V⁄F) = V` holds by `rfl` — but the two are not
*syntactically* equal, so `rw` cannot cross between them. The helpers are
therefore written uniformly in the `(V⁄F)` form, matching `TorsionCard`, and the
one crossing into the `W.Point` form the rest of this file uses is made by
`exact` (which goes through `whnf`) in the two leaves themselves. -/

omit [DecidableEq F] in
/-- `ΨSqₙ ≠ 0` in ANY characteristic, needing only `n ≠ 0`.

The leading-coefficient route fails at `n = p` in characteristic `p`, where
`coeff_ΨSq n = n²` vanishes. Instead: `IsCoprime a 0` forces `a` to be a unit,
while `Φₙ` has degree `n² > 0`. (This is `TorsionCharP.ΨSq_ne_zero`, inlined
here so that this file's import cone need not grow by the whole
`TorsionCharP`/`WronskianInduction` subtree.) -/
theorem ΨSq_ne_zero' (V : Affine F) [V.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    V.ΨSq n ≠ 0 := by
  intro h0
  have hcop : IsCoprime (V.Φ n) (V.ΨSq n) :=
    WeierstrassCurve.isCoprime_Φ_ΨSq V hn V.isUnit_Δ
  rw [h0] at hcop
  have hdeg0 : (V.Φ n).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp hcop)
  rw [WeierstrassCurve.natDegree_Φ V n] at hdeg0
  exact hn (Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hdeg0))

omit [DecidableEq F] in
/-- **The fibre node over an algebraically closed field.** Given any `ξ`, there
is a curve point `(x₀, y₀)` with `Φₙ(x₀) = ξ · ΨSqₙ(x₀)`.

This is `TorsionCard.exists_point_x_smul` with its `(n : F) ≠ 0` hypothesis
REMOVED, which is exactly what algebraic (rather than separable) closure buys.
That hypothesis is used there only to show the derivative of `Φₙ − C ξ · ΨSqₙ`
is nonzero, so that a root exists over a separably closed field. Here the
polynomial is monic of degree `n² ≥ 1` — its `n²`-coefficient is `1` by
`coeff_Φ`, and `ΨSqₙ` cannot contribute there since its degree is at most
`n² − 1` — so `IsAlgClosed.exists_root` applies directly. The `y`-coordinate is
then a root of the degree-`2` fibre quadratic, again with no separability. -/
theorem exists_point_x_smul_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) (ξ : F) :
    ∃ (x₀ y₀ : F) (_ : (V⁄F).toAffine.Nonsingular x₀ y₀),
      ((V⁄F).Φ n).eval x₀ = ξ * ((V⁄F).ΨSq n).eval x₀ := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hD1 : 1 ≤ n.natAbs ^ 2 := by
    have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    have := pow_ne_zero 2 hna
    omega
  set f : F[X] := (V⁄F).Φ n - Polynomial.C ξ * (V⁄F).ΨSq n with hf
  have hcoeff : f.coeff (n.natAbs ^ 2) = 1 := by
    rw [hf, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      WeierstrassCurve.coeff_Φ,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt ((V⁄F).natDegree_ΨSq_le n) (by omega)),
      mul_zero, sub_zero]
  have hf0 : f ≠ 0 := by
    intro hc
    rw [hc, Polynomial.coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hle : n.natAbs ^ 2 ≤ f.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)
  have hdeg : f.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hf0]
    intro hc
    have hnd : f.natDegree = 0 := by exact_mod_cast hc
    omega
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root f hdeg
  have hrel : ((V⁄F).Φ n).eval x₀ = ξ * ((V⁄F).ΨSq n).eval x₀ := by
    have hx := hx₀
    rw [Polynomial.IsRoot, hf, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hx
    linear_combination hx
  have hydeg : (TorsionCard.yQuad V x₀).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero V x₀),
      TorsionCard.yQuad_natDegree]
    norm_num
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (TorsionCard.yQuad V x₀) hydeg
  refine ⟨x₀, y₀, ?_, hrel⟩
  exact (V⁄F).toAffine.equation_iff_nonsingular.mp
    ((TorsionCard.eval_yQuad_eq_zero_iff_equation V x₀ y₀).mp hy₀)

/-- **Divisibility of the point group over an algebraically closed field**, for
every nonzero integer and in every characteristic.

Same argument as `TorsionCard.smul_surjective`, over the stronger fibre node
above: `ΨSqₙ(x₀) ≠ 0` by the Bézout identity `isCoprime_Φ_ΨSq` (a common root
would contradict `A·Φ + B·ΨSq = 1`), so `TorsionCard.exists_smul_some_eq`
computes `n • (x₀, y₀)` as an affine point with `x`-coordinate `ξ`; its
`y`-coordinate is `η` or `negY ξ η`, and in the latter case negating the
preimage fixes it. -/
theorem zsmul_surjective_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) : Function.Surjective (fun P : (V⁄F).Point => n • P) := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hpoint : ∀ {x₁ y₁ x₂ y₂ : F} (h₁ : (V⁄F).toAffine.Nonsingular x₁ y₁)
      (h₂ : (V⁄F).toAffine.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
      (Affine.Point.some x₁ y₁ h₁ : (V⁄F).Point) = Affine.Point.some x₂ y₂ h₂ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    subst hx; subst hy; rfl
  intro P₀
  cases P₀ with
  | zero => exact ⟨0, smul_zero _⟩
  | some ξ η h₀ =>
    obtain ⟨x₀, y₀, hns, hrel⟩ := exists_point_x_smul_algClosed V hn ξ
    have hΨ : ((V⁄F).ΨSq n).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨A, B, hAB⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq (V⁄F) hn (V⁄F).isUnit_Δ
      have hev := congrArg (Polynomial.eval x₀) hAB
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_one, hrel, h0] at hev
      simp at hev
    obtain ⟨x', y', h', hsmul, hx'⟩ := TorsionCard.exists_smul_some_eq V hn hns hΨ
    have hx : x' = ξ := by
      rw [hrel] at hx'
      exact mul_right_cancel₀ hΨ hx'
    rcases Affine.Y_eq_of_X_eq h'.1 h₀.1 hx with hy | hy
    · exact ⟨Affine.Point.some x₀ y₀ hns, hsmul.trans (hpoint h' h₀ hx hy)⟩
    · refine ⟨-(Affine.Point.some x₀ y₀ hns), ?_⟩
      show n • (-(Affine.Point.some x₀ y₀ hns) : (V⁄F).Point) = _
      rw [smul_neg, hsmul, Affine.Point.neg_some]
      exact hpoint _ h₀ hx (by rw [hy, hx, Affine.negY_negY])

/-- **Finiteness of the `n`-torsion over an algebraically closed field**, in
every characteristic.

A nonzero `n`-torsion point `(x, y)` has `ΨSqₙ(x) = 0`
(`TorsionCard.smul_some_eq_zero_iff`); `ΨSqₙ ≠ 0` by `ΨSq_ne_zero'`, so there are
finitely many such `x`, and at most two points lie over each
(`TorsionCard.pointsAt`). -/
theorem finite_zsmul_torsion_algClosed [IsAlgClosed F] (V : Affine F) [V.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) : {P : (V⁄F).Point | n • P = 0}.Finite := by
  classical
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hΨ : (V⁄F).ΨSq n ≠ 0 := ΨSq_ne_zero' (V⁄F) hn
  refine Set.Finite.subset (Finset.finite_toSet (insert (0 : (V⁄F).Point)
    (((V⁄F).ΨSq n).roots.toFinset.biUnion (TorsionCard.pointsAt V)))) ?_
  intro P hP
  simp only [Set.mem_setOf_eq] at hP
  rw [Finset.mem_coe]
  cases P with
  | zero => exact Finset.mem_insert_self _ _
  | some x y h =>
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩)
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hΨ, Polynomial.IsRoot]
      exact (TorsionCard.smul_some_eq_zero_iff V hn h).mp hP
    · exact (TorsionCard.mem_pointsAt_iff V).mpr ⟨y, h, rfl⟩

/-- **PROVEN.** Multiplication by a nonzero integer is surjective on the points of
an elliptic curve over an algebraically closed field.

This is the divisibility of `E(F)`, and it is one of the two geometric inputs on
which the degree/dual arithmetic rests. It is *not* formal: a homomorphic image
of a divisible group need not be the whole target. -/
theorem nsmul_surjective [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun P : W.Point => n • P) := by
  have h : Function.Surjective (fun P : W.Point => (n : ℤ) • P) :=
    zsmul_surjective_algClosed W (Int.natCast_ne_zero.mpr hn)
  intro Q
  obtain ⟨P, hP⟩ := h Q
  exact ⟨P, by simpa only [natCast_zsmul] using hP⟩

/-- **PROVEN.** The `n`-torsion of an elliptic curve is finite.

The second geometric input. Over an algebraically closed field of characteristic
zero it is in fact `(ℤ/n)²`; only finiteness is used here — and, unlike the
count, finiteness needs no hypothesis on the characteristic. -/
theorem finite_nsmulKer [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.Point | n • P = 0}.Finite := by
  have h : {P : W.Point | (n : ℤ) • P = 0}.Finite :=
    finite_zsmul_torsion_algClosed W (Int.natCast_ne_zero.mpr hn)
  refine h.subset ?_
  intro P hP
  simpa only [Set.mem_setOf_eq, natCast_zsmul] using hP

/-! ### Consequences of divisibility, for the geometric leaves

Four small facts that `IsRationalMap.isIsogeny` rests on. Two are about the
`x`-map alone — every element of the base field is an `x`-coordinate, and the
fibres of `x` have at most two points — and two convert those into statements
about a homomorphism: a rational map with a **constant** `x`-coordinate has
finite image, and a homomorphism out of `W.Point` with finite image is zero.

The last of these is where divisibility enters, and it is the whole reason
`[IsAlgClosed F]` and `[W.IsElliptic]` are not decoration: `n := #(im φ)` kills
the image by Lagrange, while `nsmul_surjective` writes every `P` as `n • P'`,
so `φ P = n • φ P' = 0`. This is exactly the step that the two FALSITY AUDITs
above break — over the singular cuspidal cubic `W.Point` is not divisible and a
homomorphism onto a two-element image survives. -/

omit [DecidableEq F] in
/-- Over an algebraically closed field every element of `F` is the `x`-coordinate of a
nonzero point of an elliptic curve: the `y`-fibre quadratic `TorsionCard.yQuad` has
degree `2`, hence a root. -/
theorem exists_point_veluPointX_eq [IsAlgClosed F] [W.IsElliptic] (t : F) :
    ∃ P : W.Point, P ≠ 0 ∧ veluPointX P = t := by
  haveI : (W⁄F).IsElliptic := inferInstanceAs W.IsElliptic
  have hydeg : (TorsionCard.yQuad W t).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero W t),
      TorsionCard.yQuad_natDegree]
    norm_num
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (TorsionCard.yQuad W t) hydeg
  have hns : W.Nonsingular t y₀ :=
    (W⁄F).toAffine.equation_iff_nonsingular.mp
      ((TorsionCard.eval_yQuad_eq_zero_iff_equation W t y₀).mp hy₀)
  exact ⟨Affine.Point.some t y₀ hns, Affine.Point.some_ne_zero _, rfl⟩

omit [DecidableEq F] in
/-- The nonzero points whose `x`-coordinate lies in a finite set form a finite set,
because the fibres of `x` have at most two elements
(`eq_or_eq_neg_of_veluPointX_eq`). No hypothesis on `F` or `W` is needed. -/
theorem finite_veluPointX_preimage {T : Set F} (hT : T.Finite) :
    {P : W.Point | P ≠ 0 ∧ veluPointX P ∈ T}.Finite := by
  classical
  have hsub : {P : W.Point | P ≠ 0 ∧ veluPointX P ∈ T}
      ⊆ ⋃ t ∈ T, {P : W.Point | P ≠ 0 ∧ veluPointX P = t} := by
    rintro P ⟨hP, hx⟩
    exact Set.mem_biUnion hx ⟨hP, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion hT ?_) hsub
  intro t _
  by_cases hne : ∃ P₁ : W.Point, P₁ ≠ 0 ∧ veluPointX P₁ = t
  · obtain ⟨P₁, hP₁, hx₁⟩ := hne
    refine Set.Finite.subset ((Set.finite_singleton (-P₁)).insert P₁) ?_
    rintro P ⟨hP, hx⟩
    rcases eq_or_eq_neg_of_veluPointX_eq hP hP₁ (by rw [hx, hx₁]) with h | h
    · exact Set.mem_insert_iff.2 (Or.inl h)
    · exact Set.mem_insert_iff.2 (Or.inr h)
  · push Not at hne
    have hempty : {P : W.Point | P ≠ 0 ∧ veluPointX P = t} = ∅ := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact hne P
    rw [hempty]
    exact Set.finite_empty

/-- **A homomorphism out of `W.Point` with FINITE image is zero.**

This is divisibility doing the work: with `n := #(im φ)`, Lagrange gives
`n • Q = 0` for every `Q` in the image, while `nsmul_surjective` writes an
arbitrary `P` as `n • P'`, so `φ P = n • φ P' = 0`.

Both instance hypotheses are load-bearing here and nowhere else in the
`isIsogeny` argument — see the FALSITY AUDIT in `NotIsRationalMapAdd`, where the
singular cuspidal cubic has an exponent-2 point group and this conclusion
fails. -/
theorem eq_zero_of_finite_range [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    (hfin : (Set.range φ).Finite) : φ = 0 := by
  classical
  have hcoe : ((AddMonoidHom.range φ : AddSubgroup W'.Point) : Set W'.Point) = Set.range φ :=
    AddMonoidHom.coe_range φ
  haveI : Finite (AddMonoidHom.range φ) := by
    have h := hfin.to_subtype
    rwa [← hcoe] at h
  haveI : Nonempty (AddMonoidHom.range φ) := ⟨0⟩
  have hn0 : Nat.card (AddMonoidHom.range φ) ≠ 0 := Nat.card_pos.ne'
  have hkill : ∀ Q ∈ AddMonoidHom.range φ,
      Nat.card (AddMonoidHom.range φ) • Q = 0 := by
    intro Q hQ
    have h := card_nsmul_eq_zero' (x := (⟨Q, hQ⟩ : AddMonoidHom.range φ))
    simpa using congrArg (Subtype.val) h
  ext P
  obtain ⟨P', hP'⟩ := nsmul_surjective (W := W) hn0 P
  have hstep : φ P = Nat.card (AddMonoidHom.range φ) • φ P' := by
    rw [← hP']
    simp
  rw [hstep, hkill _ ⟨P', rfl⟩]
  simp

/-- If the `x`-coordinate of the image is a single constant `c` away from the zeros of
`B`, the image is finite: it meets `{0}`, the (at most two) points with `x = c`, and
the image of the finitely many points where `B` vanishes. -/
theorem finite_range_of_constX {φ : W.Point →+ W'.Point} {B : F[X]} (hB : B ≠ 0) (c : F)
    (hc : ∀ P : W.Point, φ P ≠ 0 → B.eval (veluPointX P) ≠ 0 → veluPointX (φ P) = c) :
    (Set.range φ).Finite := by
  classical
  have hbad : {P : W.Point | P ≠ 0 ∧ veluPointX P ∈ {t : F | B.eval t = 0}}.Finite :=
    finite_veluPointX_preimage (Polynomial.finite_setOf_isRoot hB)
  have hfib : {R : W'.Point | R ≠ 0 ∧ veluPointX R ∈ ({c} : Set F)}.Finite :=
    finite_veluPointX_preimage (Set.finite_singleton c)
  refine Set.Finite.subset (((hbad.image φ).union hfib).insert 0) ?_
  rintro Q ⟨P, rfl⟩
  by_cases hQ : φ P = 0
  · exact Set.mem_insert_iff.2 (Or.inl hQ)
  refine Set.mem_insert_iff.2 (Or.inr ?_)
  have hP0 : P ≠ 0 := by rintro rfl; exact hQ (map_zero φ)
  by_cases hBP : B.eval (veluPointX P) = 0
  · exact Set.mem_union_left _ ⟨P, ⟨hP0, hBP⟩, rfl⟩
  · exact Set.mem_union_right _ ⟨hQ, hc P hQ hBP⟩

/-- **A rational map whose `x`-witness is a CONSTANT rational function `A = c · B` is
zero.** The degenerate case of the two arguments below, and the reason the whole
`isIsogeny` proof can assume `A / B` nonconstant. -/
theorem eq_zero_of_constX [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    {A B : F[X]} (hB : B ≠ 0) (c : F) (hAc : A = Polynomial.C c * B)
    (hcertx : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P)) :
    φ = 0 := by
  refine eq_zero_of_finite_range (finite_range_of_constX hB c ?_)
  intro P hP hBP
  have hx := hcertx P hP
  rw [hAc] at hx
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hx
  exact mul_right_cancel₀ hBP hx

/-- **`W.Point` is not the union of two proper subgroups plus a finite set.**

If `φ P` and `ψ P` agree UP TO SIGN at all but finitely many `P`, then they agree
up to sign identically: `φ = ψ` or `φ + ψ = 0`. Equivalently, the two subgroups
`ker (φ - ψ)` and `ker (φ + ψ)` cannot cover `W.Point` off a finite set unless one
of them is everything.

This is Step 1 of the chord branch of `IsRationalMap.add`, where it rules out the
degenerate case `A₂B₁ - A₁B₂ = 0` — i.e. `x ∘ φ` and `x ∘ ψ` being the SAME
rational function, which is the one case technique 1 of the module docstring
cannot absorb.

The proof has three cases, and only the third is the classical covering argument.
If `ker (φ - ψ)` is finite then the complement of `ker (φ + ψ)` is finite, so
`φ + ψ` has finite image and is zero by `eq_zero_of_finite_range`; symmetrically
with the roles swapped. Otherwise pick `a` outside `ker (φ - ψ)` and off the
exceptional set — so `a ∈ ker (φ + ψ)` — and note that for every `b` outside
`ker (φ + ψ)` and off the exceptional set (an INFINITE supply, since a finite
complement would again force `φ + ψ = 0`) the sum `a + b` lies in neither
subgroup, hence in the finite exceptional set. Translation by `a` is injective, so
that is an injection of an infinite set into a finite one. -/
theorem eq_or_add_eq_zero_of_finite_compl [IsAlgClosed F] [W.IsElliptic]
    {φ ψ : W.Point →+ W'.Point}
    (hfin : {P : W.Point | φ P ≠ ψ P ∧ φ P ≠ -(ψ P)}.Finite) :
    φ = ψ ∨ φ + ψ = 0 := by
  classical
  set T : Set W.Point := {P : W.Point | φ P ≠ ψ P ∧ φ P ≠ -(ψ P)} with hTdef
  set Sp : Set W.Point := {P : W.Point | φ P = ψ P} with hSpdef
  set Sm : Set W.Point := {P : W.Point | φ P = -(ψ P)} with hSmdef
  have hSpk : ∀ P : W.Point, P ∈ Sp ↔ (φ - ψ) P = 0 := by
    intro P; simp [hSpdef, sub_eq_zero]
  have hSmk : ∀ P : W.Point, P ∈ Sm ↔ (φ + ψ) P = 0 := by
    intro P
    simp only [hSmdef, Set.mem_setOf_eq, AddMonoidHom.add_apply]
    constructor
    · intro h; rw [h]; exact neg_add_cancel _
    · intro h; exact eq_neg_of_add_eq_zero_left h
  have hout_p : (Set.range (φ - ψ)).Finite → φ = ψ := by
    intro hf
    have h := eq_zero_of_finite_range (W := W) (φ := φ - ψ) hf
    exact sub_eq_zero.1 h
  have hout_m : (Set.range (φ + ψ)).Finite → φ + ψ = 0 := fun hf =>
    eq_zero_of_finite_range (W := W) (φ := φ + ψ) hf
  have hcase_m : (Smᶜ).Finite → φ + ψ = 0 := by
    intro hf
    refine hout_m (Set.Finite.subset ((hf.image (φ + ψ)).insert 0) ?_)
    rintro _ ⟨P, rfl⟩
    by_cases hP : P ∈ Sm
    · exact Set.mem_insert_iff.2 (Or.inl ((hSmk P).1 hP))
    · exact Set.mem_insert_iff.2 (Or.inr ⟨P, hP, rfl⟩)
  have hcase_p : (Spᶜ).Finite → φ = ψ := by
    intro hf
    refine hout_p (Set.Finite.subset ((hf.image (φ - ψ)).insert 0) ?_)
    rintro _ ⟨P, rfl⟩
    by_cases hP : P ∈ Sp
    · exact Set.mem_insert_iff.2 (Or.inl ((hSpk P).1 hP))
    · exact Set.mem_insert_iff.2 (Or.inr ⟨P, hP, rfl⟩)
  have hcov_p : Spᶜ \ T ⊆ Sm := by
    intro P hP
    by_contra hc
    exact hP.2 ⟨hP.1, hc⟩
  have hcov_m : Smᶜ \ T ⊆ Sp := by
    intro P hP
    by_contra hc
    exact hP.2 ⟨hc, hP.1⟩
  by_cases hSpfin : Sp.Finite
  · refine Or.inr (hcase_m (Set.Finite.subset (hSpfin.union hfin) ?_))
    intro P hP
    by_cases hc : P ∈ Sp
    · exact Set.mem_union_left _ hc
    · exact Set.mem_union_right _ ⟨hc, hP⟩
  by_cases hSmfin : Sm.Finite
  · refine Or.inl (hcase_p (Set.Finite.subset (hSmfin.union hfin) ?_))
    intro P hP
    by_cases hc : P ∈ Sm
    · exact Set.mem_union_left _ hc
    · exact Set.mem_union_right _ ⟨hP, hc⟩
  by_cases hp : φ = ψ
  · exact Or.inl hp
  by_cases hm : φ + ψ = 0
  · exact Or.inr hm
  exfalso
  have hSpcinf : (Spᶜ).Infinite := fun hf => hp (hcase_p hf)
  have hSmcinf : (Smᶜ).Infinite := fun hf => hm (hcase_m hf)
  obtain ⟨a, ha⟩ : (Spᶜ \ T).Nonempty := (hSpcinf.sdiff hfin).nonempty
  have haSm : a ∈ Sm := hcov_p ha
  have haSp : a ∉ Sp := ha.1
  have hXinf : (Smᶜ \ T).Infinite := hSmcinf.sdiff hfin
  have himg : (fun b : W.Point => a + b) '' (Smᶜ \ T) ⊆ T := by
    rintro _ ⟨b, hb, rfl⟩
    have hbSp : b ∈ Sp := hcov_m hb
    have hbSm : b ∉ Sm := hb.1
    refine ⟨?_, ?_⟩
    · intro hc
      refine haSp ?_
      have hb' : φ b = ψ b := hbSp
      have hsum' : φ (a + b) = ψ (a + b) := hc
      rw [map_add, map_add, hb'] at hsum'
      exact add_right_cancel hsum'
    · intro hc
      refine hbSm ?_
      have ha' : φ a = -(ψ a) := haSm
      have hsum' : φ (a + b) = -(ψ (a + b)) := hc
      rw [map_add, map_add, neg_add, ha'] at hsum'
      exact add_left_cancel hsum'
  exact (hXinf.image (Set.injOn_of_injective (add_right_injective a))) (hfin.subset himg)

/-- **The kernel of a nonzero rational map is finite.**

Fix `P₀ ∉ ker φ`. Translating by `k ∈ ker φ` does not move `φ P₀`, so every
`x (P₀ + k)` is a root of `A - C (x (φ P₀)) · B`. If that polynomial vanishes
identically then `A / B` is constant and `eq_zero_of_constX` forces `φ = 0`;
otherwise its root set is finite and `k ↦ P₀ + k` is an injection of `ker φ` into
`{0} ∪ {P ≠ 0 : x P ∈ roots}`, finite by `finite_veluPointX_preimage`.

Extracted from `IsRationalMap.isIsogeny` so that it is usable EARLIER in the file
than `IsIsogeny` itself is defined — `IsRationalMap.add_of_ne` needs exactly this
and nothing else about isogenies. -/
theorem IsRationalMap.finite_ker [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    (h : IsRationalMap φ) (hφ0 : φ ≠ 0) : (AddMonoidHom.ker φ : Set W.Point).Finite := by
  classical
  obtain ⟨A, B, _Cp, _Dp, _Ep, hB, _hE, hcert⟩ := h
  have hcertx : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) :=
    fun P hP => (hcert P hP).1
  obtain ⟨P₀, hP₀⟩ : ∃ P : W.Point, φ P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (AddMonoidHom.ext fun P => by simpa using hcon P)
  by_cases hAc : A = Polynomial.C (veluPointX (φ P₀)) * B
  · exact absurd (eq_zero_of_constX hB _ hAc hcertx) hφ0
  have hne : A - Polynomial.C (veluPointX (φ P₀)) * B ≠ 0 := sub_ne_zero.2 hAc
  have hroots : {t : F | (A - Polynomial.C (veluPointX (φ P₀)) * B).eval t = 0}.Finite :=
    Polynomial.finite_setOf_isRoot hne
  have himg : ((fun k : W.Point => P₀ + k) '' (AddMonoidHom.ker φ : Set W.Point)) ⊆
      insert (0 : W.Point) {P : W.Point | P ≠ 0 ∧ veluPointX P ∈
        {t : F | (A - Polynomial.C (veluPointX (φ P₀)) * B).eval t = 0}} := by
    rintro _ ⟨k, hk, rfl⟩
    by_cases hz : P₀ + k = 0
    · exact Set.mem_insert_iff.2 (Or.inl hz)
    refine Set.mem_insert_iff.2 (Or.inr ⟨hz, ?_⟩)
    have hkk : φ k = 0 := (AddMonoidHom.mem_ker).1 hk
    have hval : φ (P₀ + k) = φ P₀ := by rw [map_add, hkk, add_zero]
    have hx := hcertx (P₀ + k) (by rw [hval]; exact hP₀)
    rw [hval] at hx
    show (A - Polynomial.C (veluPointX (φ P₀)) * B).eval (veluPointX (P₀ + k)) = 0
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hx
  refine Set.Finite.of_finite_image
    (Set.Finite.subset ((finite_veluPointX_preimage hroots).insert 0) himg) ?_
  intro a _ b _ hab
  exact add_left_cancel hab

/-- **A nonzero rational map is surjective on points.**

Cancel `g = gcd A B` to a COPRIME pair `(A₀, B₀)`, which is nonconstant (else
`eq_zero_of_constX`). Then `A₀ - C s · B₀` is nonzero for every `s`, has degree `0`
for at most one `s`, and by coprimality each of its roots `t` has `B₀(t) ≠ 0`, so
`s = A₀(t) / B₀(t)` is DETERMINED by `t` — distinct `s` therefore have disjoint root
sets. Away from the finite bad locus (zeros of `g`, plus the `x`-coordinates of the
finite kernel) a root lifts to a point of the image with `x = s`, by
`exists_point_veluPointX_eq`. So the unattained `s` inject into that locus and form
a finite set; pulling back along the (≤ 2)-to-one `x` makes the complement of the
image finite, while for `Q₀` outside the image the coset `Q₀ + im φ` is an infinite
subset of that finite complement.

Extracted from `IsRationalMap.isIsogeny`; see the note there. -/
theorem IsRationalMap.surjective [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    (h : IsRationalMap φ) (hφ0 : φ ≠ 0) : Function.Surjective φ := by
  classical
  have hc := h
  obtain ⟨A, B, _Cp, _Dp, _Ep, hB, _hE, hcert⟩ := hc
  have hcertx : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) :=
    fun P hP => (hcert P hP).1
  have hker := IsRationalMap.finite_ker h hφ0
  obtain ⟨g, A₀, B₀, hgne, hA, hBeq, hcop⟩ :
      ∃ g A₀ B₀ : F[X], g ≠ 0 ∧ A = g * A₀ ∧ B = g * B₀ ∧ IsCoprime A₀ B₀ := by
    letI : GCDMonoid F[X] := EuclideanDomain.gcdMonoid F[X]
    exact ⟨GCDMonoid.gcd A B, A / GCDMonoid.gcd A B, B / GCDMonoid.gcd A B,
      gcd_ne_zero_of_right hB,
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hB) (gcd_dvd_left A B)).symm,
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hB) (gcd_dvd_right A B)).symm,
      isCoprime_div_gcd_div_gcd hB⟩
  have hB₀ : B₀ ≠ 0 := by rintro rfl; rw [mul_zero] at hBeq; exact hB hBeq
  have hcert₀ : ∀ P : W.Point, φ P ≠ 0 → g.eval (veluPointX P) ≠ 0 →
      veluPointX (φ P) * B₀.eval (veluPointX P) = A₀.eval (veluPointX P) := by
    intro P hP hg
    have hx := hcertx P hP
    rw [hA, hBeq] at hx
    simp only [Polynomial.eval_mul] at hx
    refine mul_left_cancel₀ hg ?_
    linear_combination hx
  have hnocommon : ∀ t : F, A₀.eval t = 0 → B₀.eval t = 0 → False := by
    intro t h1 h2
    obtain ⟨u, v, huv⟩ := hcop
    have hev := congrArg (Polynomial.eval t) huv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, h1, h2,
      mul_zero, add_zero] at hev
    exact zero_ne_one hev
  have hnc : ∀ s : F, A₀ ≠ Polynomial.C s * B₀ := by
    intro s hs
    refine hφ0 (eq_zero_of_constX hB s ?_ hcertx)
    rw [hA, hs, hBeq]; ring
  have hdpos : 0 < max A₀.natDegree B₀.natDegree := by
    rcases Nat.eq_zero_or_pos (max A₀.natDegree B₀.natDegree) with h0 | h0
    · exfalso
      have hA0 : A₀.natDegree = 0 := by omega
      have hB0 : B₀.natDegree = 0 := by omega
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 hA0
      obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.1 hB0
      have hbne : b ≠ 0 := by
        rintro rfl
        rw [map_zero] at hb
        exact hB₀ hb.symm
      refine hnc (a / b) ?_
      rw [← ha, ← hb, ← Polynomial.C_mul, div_mul_cancel₀ a hbne]
    · exact h0
  -- At most one `s` degenerates the degree of `A₀ - C s * B₀`.
  have hdegs : ∀ s s' : F, (A₀ - Polynomial.C s * B₀).natDegree = 0 →
      (A₀ - Polynomial.C s' * B₀).natDegree = 0 → s = s' := by
    intro s s' h1 h2
    by_contra hss
    have hd : Polynomial.C (s' - s) * B₀ =
        (A₀ - Polynomial.C s * B₀) - (A₀ - Polynomial.C s' * B₀) := by
      rw [Polynomial.C_sub]; ring
    have hle : (Polynomial.C (s' - s) * B₀).natDegree = 0 := by
      rw [hd]
      exact Nat.le_zero.1 (le_trans (Polynomial.natDegree_sub_le _ _) (by omega))
    have hsub : s' - s ≠ 0 := sub_ne_zero.2 (Ne.symm hss)
    have hB0d : B₀.natDegree = 0 := by
      rwa [Polynomial.natDegree_C_mul hsub] at hle
    have h3 : (Polynomial.C s * B₀).natDegree = 0 :=
      Nat.le_zero.1 (le_trans (Polynomial.natDegree_C_mul_le s B₀) (le_of_eq hB0d))
    have hA0d : A₀.natDegree = 0 := by
      have heq : A₀ = (A₀ - Polynomial.C s * B₀) + Polynomial.C s * B₀ := by ring
      rw [heq]
      exact Nat.le_zero.1 (le_trans (Polynomial.natDegree_add_le _ _) (by omega))
    omega
  -- The finite "bad locus" in the source: zeros of the cancelled factor `g`,
  -- together with the `x`-coordinates of the (finite) kernel.
  have hZ : ({t : F | g.eval t = 0} ∪
      veluPointX '' (AddMonoidHom.ker φ : Set W.Point)).Finite :=
    (Polynomial.finite_setOf_isRoot hgne).union (hker.image _)
  -- The unattained `x`-coordinates form a finite set.
  have hT : {s : F | ∀ P : W.Point, φ P ≠ 0 → veluPointX (φ P) ≠ s}.Finite := by
    have hsub : {s : F | ∀ P : W.Point, φ P ≠ 0 → veluPointX (φ P) ≠ s} ⊆
        {s : F | (A₀ - Polynomial.C s * B₀).natDegree = 0} ∪
          (fun t : F => A₀.eval t / B₀.eval t) ''
            ({t : F | g.eval t = 0} ∪ veluPointX '' (AddMonoidHom.ker φ : Set W.Point)) := by
      intro s hs
      by_cases hdeg0 : (A₀ - Polynomial.C s * B₀).natDegree = 0
      · exact Set.mem_union_left _ hdeg0
      refine Set.mem_union_right _ ?_
      have hdegne : (A₀ - Polynomial.C s * B₀).degree ≠ 0 := by
        intro h0
        exact hdeg0 (Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 (le_of_eq h0))
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (A₀ - Polynomial.C s * B₀) hdegne
      have hteq : A₀.eval t = s * B₀.eval t := by
        have h := ht
        rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C] at h
        linear_combination h
      have hBt : B₀.eval t ≠ 0 := by
        intro h0
        exact hnocommon t (by rw [hteq, h0, mul_zero]) h0
      refine ⟨t, ?_, ?_⟩
      · -- `t` must lie in the bad locus, else `s` would be attained.
        by_contra htbad
        have hg : g.eval t ≠ 0 := fun hc => htbad (Set.mem_union_left _ hc)
        obtain ⟨P, hP0, hxP⟩ := exists_point_veluPointX_eq (W := W) t
        have hPk : φ P ≠ 0 := by
          intro hc
          exact htbad (Set.mem_union_right _ ⟨P, (AddMonoidHom.mem_ker).2 hc, hxP⟩)
        have hval := hcert₀ P hPk (by rw [hxP]; exact hg)
        rw [hxP, hteq] at hval
        exact hs P hPk (mul_right_cancel₀ hBt hval)
      · field_simp
        linear_combination hteq
    refine Set.Finite.subset (Set.Finite.union ?_ (hZ.image _)) hsub
    exact Set.Subsingleton.finite (fun s hs s' hs' => hdegs s s' hs hs')
  -- Hence the complement of the image is finite.
  have hrcfin : ((Set.range φ)ᶜ).Finite := by
    refine Set.Finite.subset
      (finite_veluPointX_preimage (W := W')
        (T := {s : F | ∀ P : W.Point, φ P ≠ 0 → veluPointX (φ P) ≠ s}) hT) ?_
    intro R hR
    have hR0 : R ≠ 0 := by
      rintro rfl
      exact hR ⟨0, map_zero φ⟩
    refine ⟨hR0, ?_⟩
    intro P hP hxeq
    rcases eq_or_eq_neg_of_veluPointX_eq hR0 hP hxeq.symm with hcase | hcase
    · exact hR ⟨P, hcase.symm⟩
    · exact hR ⟨-P, by rw [map_neg, ← hcase]⟩
  by_contra hnsurj
  obtain ⟨Q₀, hQ₀'⟩ : ∃ Q₀ : W'.Point, Q₀ ∉ Set.range φ := by
    by_contra hc
    push Not at hc
    exact hnsurj hc
  have hinf : (Set.range φ).Infinite := by
    intro hfin
    exact hφ0 (eq_zero_of_finite_range hfin)
  have hsubset : (fun R : W'.Point => Q₀ + R) '' (Set.range φ) ⊆ (Set.range φ)ᶜ := by
    rintro _ ⟨R, ⟨P, rfl⟩, rfl⟩
    rintro ⟨P', hP'⟩
    exact hQ₀' ⟨P' - P, by rw [map_sub, hP']; simp⟩
  exact (hinf.image (Set.injOn_of_injective (add_right_injective Q₀)))
    (hrcfin.subset hsubset)

/-- Multiplication by `n` on the points of `W`, as a homomorphism. This is the
`[n]` that appears in `ψ̂ ∘ ψ = [deg ψ]`; it agrees with the image of `n` in
`End W` (`End.natCast_apply`). -/
def mulByHom (W : Affine F) (n : ℕ) : W.Point →+ W.Point :=
  AddMonoidHom.mk' (fun P => n • P) (fun a b => by simp [smul_add])

@[simp] theorem mulByHom_apply (n : ℕ) (P : W.Point) : mulByHom W n P = n • P := rfl

/-! ### The two branches of `IsRationalMap.add`

`IsRationalMap.add` below is now an ASSEMBLY, and so are both of its branches. The
whole sum reduces to exactly TWO open statements, `exists_y_witness_two` (the
doubling branch, via `add_self` and `isRationalMap_mulByHom_two`) and
`IsRationalMap.add_of_x_ne` (the chord branch, via `add_of_ne`), plus three free
reductions (`φ = 0`, `ψ = 0`, `φ + ψ = 0`).

Why this is the right cut, and not an arbitrary one. The affine group law on `W'`
has two formulas, and which applies at `P` is decided by whether
`x (φ P) = x (ψ P)`. That condition is `A₁ B₂ - A₂ B₁ = 0` at `x P`, a polynomial
condition — so on the chord branch its vanishing locus is a *finite* set of
`x`-values and technique 1 of the module docstring absorbs it (multiply the witness
through by `A₁ B₂ - A₂ B₁`). What technique 1 cannot absorb is the case where that
polynomial vanishes IDENTICALLY, i.e. `x ∘ φ` and `x ∘ ψ` are the same rational
function. Since `x (φ P) = x (ψ P)` forces `φ P = ψ P` or `φ P = -(ψ P)`
(`eq_or_eq_neg_of_veluPointX_eq`), and `W.Point` is not the union of two proper
subgroups plus a finite set, that happens exactly when `φ = ψ` or `φ = -ψ`. The
second is the free reduction `φ + ψ = 0`; the first is genuinely a different
formula and is `add_self`. So the split is forced by the geometry, not chosen.

Each branch then collapses further. The doubling branch is not a second formula to
grind out at all: `φ + φ = φ ∘ [2]_W` puts the doubling on the SOURCE curve, where
`IsRationalMap.comp` applies and `[W.IsElliptic]` is available — so it needs only
`isRationalMap_mulByHom_two`, whose `x`-half is already proven, leaving
`exists_y_witness_two`. The chord branch keeps its formula but loses its
degenerate case to `IsRationalMap.add_of_ne`, and what is left is
`IsRationalMap.add_of_x_ne`.

The two remaining leaves are INDEPENDENT and can be owned separately. -/

/-- **PROVEN.** The `x`-coordinate half of "multiplication by `n` is a rational
map": `x ([n] P) · ΨSqₙ (x P) = Φₙ (x P)`, the classical `x([n]P) = Φₙ/ψₙ²` in
multiplied-out form, in every characteristic and with no hypothesis on the field.

This is `TorsionCard.exists_smul_some_eq` transported from the `(W⁄F)` spelling to
the `veluPointX` spelling this file uses, with the degenerate branch supplied by
`TorsionCard.smul_some_eq_zero_iff`: where `ΨSqₙ (x P) = 0` we have `n • P = 0` and
there is nothing to certify, which is exactly the shape `IsRationalMap` wants. -/
theorem veluPointX_nsmul [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) (P : W.Point)
    (hP : n • P ≠ 0) :
    veluPointX (n • P) * (W.ΨSq (n : ℤ)).eval (veluPointX P)
      = (W.Φ (n : ℤ)).eval (veluPointX P) := by
  haveI : (W⁄F).IsElliptic := inferInstanceAs W.IsElliptic
  have hn' : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hn
  cases P with
  | zero => exact absurd (smul_zero n) hP
  | some x y h =>
    have h' : (W⁄F).toAffine.Nonsingular x y := h
    have hzs : ((n : ℤ)) • (Affine.Point.some x y h' : (W⁄F).Point)
        = (n • (Affine.Point.some x y h : W.Point) : W.Point) := natCast_zsmul _ _
    have hne : ((n : ℤ)) • (Affine.Point.some x y h' : (W⁄F).Point) ≠ 0 := by
      rw [hzs]; exact hP
    have hΨ : ((W⁄F).ΨSq (n : ℤ)).eval x ≠ 0 := fun hc =>
      hne ((TorsionCard.smul_some_eq_zero_iff W hn' h').2 hc)
    obtain ⟨x', y', h'', hsmul, hx'⟩ := TorsionCard.exists_smul_some_eq W hn' h' hΨ
    have hval : (n • (Affine.Point.some x y h : W.Point) : W.Point)
        = Affine.Point.some x' y' h'' := by rw [← hzs]; exact hsmul
    rw [hval]
    show x' * (W.ΨSq (n : ℤ)).eval x = (W.Φ (n : ℤ)).eval x
    exact hx'

omit [DecidableEq F] in
/-- **The ring identity behind the duplication `y`-witness**, isolated from the
curve so that it is a statement about a field and nothing else.

`L` stands for the tangent slope, constrained only by `hLd : L · ψ₂ = 3x² + 2a₂x +
a₄ - a₁y`; the left-hand side is `Affine.addY x x y L` written out through
`negY`/`negAddY`/`addX`, and the right-hand side is `C(x) · y + D(x)` with the two
coefficients that `exists_y_witness_two` uses. Everything is cleared by `ψ₂⁴ =
Ψ₂Sq²`, which is what makes the right-hand side `y`-affine.

Three steps, each a one-line `linear_combination`, and the curve equation is used
exactly TWICE — once with coefficient `-a₁²` to make `addX · ψ₂²` `y`-free, and
once with coefficient `-2a₁` to make `ψ₂ · Ng` `y`-affine. Everything after that is
pure algebra over `hLd`. -/
theorem addY_two_core (a₁ a₂ a₃ a₄ a₆ x y L : F)
    (hEq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hLd : L * (2 * y + a₁ * x + a₃) = (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) :
    (-(L * ((L ^ 2 + a₁ * L - a₂ - x - x) - x) + y) - a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) - a₃) * ((2 * y + a₁ * x + a₃) ^ 2) ^ 2
      = (-(2 * (3 * x ^ 2 + 2 * a₂ * x + a₄) + a₁ * (a₁ * x + a₃)) * (((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) - x * (2 * y + a₁ * x + a₃) ^ 2) - ((2 * y + a₁ * x + a₃) ^ 2) ^ 2) * y
        + (-((a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - 2 * a₁ * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)) * (((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) - x * (2 * y + a₁ * x + a₃) ^ 2)
            - a₁ * ((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) * (2 * y + a₁ * x + a₃) ^ 2 - a₃ * ((2 * y + a₁ * x + a₃) ^ 2) ^ 2) := by
  have hAX : (L ^ 2 + a₁ * L - a₂ - x - x) * (2 * y + a₁ * x + a₃) ^ 2 = ((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) := by
    linear_combination (L * (2 * y + a₁ * x + a₃) + (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) + a₁ * (2 * y + a₁ * x + a₃)) * hLd + (-a₁ ^ 2) * hEq
  have hB : (2 * y + a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) = (2 * (3 * x ^ 2 + 2 * a₂ * x + a₄) + a₁ * (a₁ * x + a₃)) * y + ((a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - 2 * a₁ * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)) := by
    linear_combination (-2 * a₁) * hEq
  have hAY : (-(L * ((L ^ 2 + a₁ * L - a₂ - x - x) - x) + y) - a₁ * (L ^ 2 + a₁ * L - a₂ - x - x) - a₃) * ((2 * y + a₁ * x + a₃) ^ 2) ^ 2
      = -((2 * y + a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) * (((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) - x * (2 * y + a₁ * x + a₃) ^ 2) - y * ((2 * y + a₁ * x + a₃) ^ 2) ^ 2
        - a₁ * ((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) * (2 * y + a₁ * x + a₃) ^ 2 - a₃ * ((2 * y + a₁ * x + a₃) ^ 2) ^ 2 := by
    linear_combination ((2 * y + a₁ * x + a₃) ^ 3 * (x - (L ^ 2 + a₁ * L - a₂ - x - x))) * hLd
      + (-((2 * y + a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) + a₁ * (2 * y + a₁ * x + a₃) ^ 2)) * hAX
  linear_combination hAY + (-(((3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 + a₁ * (a₁ * x + a₃) * (3 * x ^ 2 + 2 * a₂ * x + a₄) - a₁ ^ 2 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) - (a₂ + 2 * x) * (2 * y + a₁ * x + a₃) ^ 2) - x * (2 * y + a₁ * x + a₃) ^ 2)) * hB

/-- **PROVEN** (2026-07-27). The `y`-coordinate witness for DUPLICATION: `y ([2] P)`
is affine in `y P` with coefficients rational in `x P`. With `veluPointX_nsmul` this
closes `isRationalMap_mulByHom_two`, hence `IsRationalMap.add_self`, hence the whole
doubling branch of `IsRationalMap.add`.

**Why this is stated at `n = 2` and not for general `n`.** General `n` is FREE once
`IsRationalMap.add` is closed: `mulByHom W n = mulByHom W (n-1) + mulByHom W 1` and
`mulByHom W 1 = AddMonoidHom.id _` is `IsRationalMap.id`, so induction on `n` gives
every `[n]` from `add` alone. The one case that induction cannot produce is the one
`add` itself consumes — `[2]`, which is exactly the doubling branch. So `[2]` is the
atom and everything else is a corollary. Do not state or prove this for general `n`;
it is strictly more work for nothing.

**`ωₙ` IS MISSING FROM THE PIN — and it turned out not to be needed** (checked
2026-07-27; the check that would refute the absence claim is
`grep -rn "ω" .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`).
Mathlib defines `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, `φ` — everything needed for the
`x`-coordinate, which is why `veluPointX_nsmul` above is already PROVEN — but it
does **not** define the bivariate `ωₙ` that carries the `y`-coordinate. Its own
module docstring lists `ωₙ := (ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2` and then records
"TODO: the bivariate polynomials `ωₙ`". It is absent from `~/cs/FLT` and from this
project's `Fermat/FLT/Mathlib/` shim tree as well.

That absence did not block anything, precisely because only `n = 2` is wanted: at
`n = 2` there is no general `ωₙ` theory to build, only the tangent-line formula.
`2 • P = P + P` is `Affine.Point.add_self_of_Y_ne`, whose `y` is `Affine.addY` at
slope `ℓ = (3x² + 2a₂x + a₄ - a₁y) / (2y + a₁x + a₃)`; substituting and clearing the
denominator `ψ₂ = 2y + a₁x + a₃` gives a `y`-affine expression once `y²` is reduced
by the Weierstrass equation. That reduction is `addY_two_core` above, where the
curve equation is used exactly twice, with coefficients `-a₁²` and `-2a₁`.

The `E ≠ 0` side condition comes out as `Ψ₂Sq²`, nonzero by `ΨSq_ne_zero'` and
`ΨSq_two` in every characteristic, and the points where `ψ₂` vanishes are the
2-torsion, where `2 • P = 0` and the certificate is vacuous — so no bad-locus
multiplier is needed. **Note this holds in characteristic 2 as well**: nothing here
divides by `2`, and `ψ₂ = a₁x + a₃` there, which is nonzero exactly off the (still
finite) 2-torsion. -/
theorem exists_y_witness_two [W.IsElliptic] :
    ∃ C D E : F[X], E ≠ 0 ∧ ∀ P : W.Point, mulByHom W 2 P ≠ 0 →
      veluPointY (mulByHom W 2 P) * E.eval (veluPointX P)
        = C.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P) := by
  classical
  have hQ0 : W.Ψ₂Sq ≠ 0 := by
    have hq := ΨSq_ne_zero' W (n := 2) two_ne_zero
    rwa [WeierstrassCurve.ΨSq_two] at hq
  refine ⟨-(Polynomial.C 2 * (Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄) + Polynomial.C W.a₁ * (Polynomial.C W.a₁ * X + Polynomial.C W.a₃))
          * (((Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄) ^ 2
            + Polynomial.C W.a₁ * (Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * (Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄)
            - Polynomial.C (W.a₁ ^ 2) * (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X + Polynomial.C W.a₆)
            - (Polynomial.C W.a₂ + Polynomial.C 2 * X) * W.Ψ₂Sq)
            - X * W.Ψ₂Sq)
          - W.Ψ₂Sq ^ 2,
    -((Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * (Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄) - Polynomial.C (2 * W.a₁) * (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X + Polynomial.C W.a₆))
          * (((Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄) ^ 2
            + Polynomial.C W.a₁ * (Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * (Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄)
            - Polynomial.C (W.a₁ ^ 2) * (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X + Polynomial.C W.a₆)
            - (Polynomial.C W.a₂ + Polynomial.C 2 * X) * W.Ψ₂Sq)
            - X * W.Ψ₂Sq)
          - Polynomial.C W.a₁ * ((Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄) ^ 2
            + Polynomial.C W.a₁ * (Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * (Polynomial.C 3 * X ^ 2 + Polynomial.C (2 * W.a₂) * X + Polynomial.C W.a₄)
            - Polynomial.C (W.a₁ ^ 2) * (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X + Polynomial.C W.a₆)
            - (Polynomial.C W.a₂ + Polynomial.C 2 * X) * W.Ψ₂Sq) * W.Ψ₂Sq
          - Polynomial.C W.a₃ * W.Ψ₂Sq ^ 2,
    W.Ψ₂Sq ^ 2, pow_ne_zero 2 hQ0, ?_⟩
  intro P hP
  simp only [mulByHom_apply] at hP ⊢
  cases P with
  | zero => exact absurd (smul_zero 2) hP
  | some x y h =>
    have hEq : y ^ 2 + W.a₁ * x * y + W.a₃ * y
        = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := (Affine.equation_iff ..).1 h.1
    by_cases hy2 : y = -y - W.a₁ * x - W.a₃
    · refine absurd ?_ hP
      rw [two_nsmul]
      exact Affine.Point.add_self_of_Y_eq (by simpa [Affine.negY] using hy2)
    have hd : (2 * y + W.a₁ * x + W.a₃) ≠ 0 := by
      intro hc
      exact hy2 (by linear_combination hc)
    have hy2' : y ≠ W.negY x y := by simpa [Affine.negY] using hy2
    have hLd : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃)
        = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [Affine.slope_of_Y_ne' hy2,
        show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ from by ring]
      exact div_mul_cancel₀ _ hd
    have hQev : W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
      haveI : (W⁄F).IsElliptic := inferInstanceAs W.IsElliptic
      have hq := TorsionCard.eval_Ψ₂Sq_eq_sq W h.1
      rw [show (2 * y + W.a₁ * x + W.a₃) = (2 * y + (W.a₁ * x + W.a₃)) from by ring]
      exact hq
    have hY : veluPointY ((2 : ℕ) • (Affine.Point.some x y h : W.Point))
        = W.addY x x y (W.slope x x y y) := by
      rw [two_nsmul, Affine.Point.add_self_of_Y_ne hy2', veluPointY_some]
    rw [hY]
    simp only [veluPointX_some, veluPointY_some, Affine.addY, Affine.negAddY, Affine.addX,
      Affine.negY, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, hQev]
    linear_combination addY_two_core W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ x y (W.slope x x y y) hEq hLd


/-- **PROVEN** (2026-07-27). Duplication is a rational map.

The `x`-witness is `(Φ 2, ΨSq 2)` by `veluPointX_nsmul` and the `y`-witness is
`exists_y_witness_two`; `ΨSq 2 ≠ 0` by `ΨSq_ne_zero'` in every characteristic. No
hypothesis on the field. By the note on `exists_y_witness_two`, `[n]` for every `n`
now follows from `IsRationalMap.add` by induction, so nothing further about
division polynomials is needed anywhere in this file. -/
theorem isRationalMap_mulByHom_two [W.IsElliptic] : IsRationalMap (mulByHom W 2) := by
  obtain ⟨C, D, E, hE, hy⟩ := exists_y_witness_two (W := W)
  exact ⟨W.Φ ((2 : ℕ) : ℤ), W.ΨSq ((2 : ℕ) : ℤ), C, D, E,
    ΨSq_ne_zero' W (by norm_num), hE,
    fun P hP => ⟨veluPointX_nsmul (by norm_num) P hP, hy P hP⟩⟩

/-- **PROVEN** (2026-07-27). The doubling branch of `IsRationalMap.add`: twice a
rational map is rational.

The cut that makes this free is to push the doubling onto the SOURCE curve rather
than the target:

  `(φ + φ) P = 2 • φ P = φ (2 • P) = (φ.comp (mulByHom W 2)) P`

so `φ + φ` is a COMPOSITE, and `IsRationalMap.comp` is already proven. That matters
for more than elegance: the ambient statement carries `[W.IsElliptic]` and says
nothing whatever about `W'`, so a route through `[2]` on `W'` would have needed a
hypothesis this theorem does not have (or a proof that a curve admitting a nonzero
rational map FROM an elliptic curve is itself nonsingular). Pushing the doubling to
`W` makes that question disappear.

What is left is `isRationalMap_mulByHom_two` above, and inside it only the
`y`-witness `exists_y_witness_two` — the `x`-witness is `veluPointX_nsmul`, proven. -/
theorem IsRationalMap.add_self [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    (hφ : IsRationalMap φ) : IsRationalMap (φ + φ) := by
  have hcomp : IsRationalMap (φ.comp (mulByHom W 2)) :=
    IsRationalMap.comp isRationalMap_mulByHom_two hφ
  have heq : φ.comp (mulByHom W 2) = φ + φ := by
    ext P
    show φ ((2 : ℕ) • P) = φ P + φ P
    rw [map_nsmul, two_nsmul]
  rwa [heq] at hcomp

omit [DecidableEq F] in
/-- **The chord slope, cleared of denominators.** With `t = x P` fixed and all
polynomials evaluated at `t`, the two certificates turn `L = (y₁ - y₂)/(x₁ - x₂)`
into `L · H = K · (N y + M)` in the notation of `IsRationalMap.add_of_x_ne`:
`K = b₁b₂`, `H = e₁e₂(A₂b₁ - A₁b₂)`, `N = c₂e₁ - c₁e₂`, `M = d₂e₁ - d₁e₂`.

Isolated from the curve as a statement about a field and nothing else, so that the
only geometric input is `hL`, i.e. `Affine.slope_of_X_ne` with its denominator
cleared. One `linear_combination`. -/
theorem chordAdd_slope_core (A₁ b₁ c₁ d₁ e₁ A₂ b₂ c₂ d₂ e₂ x₁ y₁ x₂ y₂ y L : F)
    (hx₁ : x₁ * b₁ = A₁) (hx₂ : x₂ * b₂ = A₂)
    (hy₁ : y₁ * e₁ = c₁ * y + d₁) (hy₂ : y₂ * e₂ = c₂ * y + d₂)
    (hL : L * (x₁ - x₂) = y₁ - y₂) :
    L * (e₁ * e₂ * (A₂ * b₁ - A₁ * b₂))
      = b₁ * b₂ * ((c₂ * e₁ - c₁ * e₂) * y + (d₂ * e₁ - d₁ * e₂)) := by
  linear_combination (-(e₁ * e₂ * b₁ * b₂)) * hL + (L * e₁ * e₂ * b₂) * hx₁
    + (-(L * e₁ * e₂ * b₁)) * hx₂ + (-(e₂ * b₁ * b₂)) * hy₁ + (e₁ * b₁ * b₂) * hy₂

omit [DecidableEq F] in
/-- **The `x`-coordinate of a chord sum, cleared of denominators and reduced to
degree ONE in `y`.** This is Step 2 of `IsRationalMap.add_of_x_ne`, isolated from
the curve: `α₁, α₂` are the TARGET curve's coefficients (they enter through
`Affine.addX`) and `a₁ … a₆` the SOURCE curve's (they enter only through `hEq`,
which is what reduces the `y²` produced by `L²`).

The two side inputs are `hLh` — the cleared slope, `chordAdd_slope_core` — and
`hkx : (x₁ + x₂) · k = S`, which is where the two `x`-certificates are consumed.
The `y`-coefficient of the right-hand side is the polynomial called `U` in
`add_of_x_ne`, and the constant one is `V`; that `U` VANISHES identically is the
crux of that theorem and is not visible here. One `linear_combination`, using the
curve equation exactly once, with coefficient `k³n²`. -/
theorem chordAdd_x_core (α₁ α₂ a₁ a₂ a₃ a₄ a₆ t y x₁ x₂ L k h n m S : F)
    (hkx : (x₁ + x₂) * k = S)
    (hEq : y ^ 2 + a₁ * t * y + a₃ * y = t ^ 3 + a₂ * t ^ 2 + a₄ * t + a₆)
    (hLh : L * h = k * (n * y + m)) :
    (L ^ 2 + α₁ * L - α₂ - x₁ - x₂) * (h ^ 2 * k)
      = (k ^ 3 * (2 * n * m - n ^ 2 * (a₁ * t + a₃)) + α₁ * k ^ 2 * h * n) * y
        + (k ^ 3 * (n ^ 2 * (t ^ 3 + a₂ * t ^ 2 + a₄ * t + a₆) + m ^ 2)
            + α₁ * k ^ 2 * h * m - α₂ * h ^ 2 * k - S * h ^ 2) := by
  linear_combination (k * (L * h + k * (n * y + m)) + α₁ * h * k) * hLh
    + (-(h ^ 2)) * hkx + (k ^ 3 * n ^ 2) * hEq

omit [DecidableEq F] in
/-- **The `y`-coordinate of a chord sum, cleared of denominators.** Step 4 of
`IsRationalMap.add_of_x_ne`. Unlike the `x`-side there is no `y²` to reduce: `y₃`
is `-(L (x₃ - x₁) + y₁) - α₁ x₃ - α₃` and every factor is already affine in `y`,
so the curve equation does not appear at all.

What it does need is `hx3`, the `x`-identity **after** `U = 0` has been proven —
i.e. `x₃ · h²k = v` with no `y` on the right. That is why this step comes last:
with `U` still present, `L · (x₃ - x₁)` would be quadratic in `y`. `R` abbreviates
`A₁ b₂ h²`, which is `x₁ · h²k` by the first `x`-certificate. -/
theorem chordAdd_y_core (α₁ α₃ y y₁ x₁ x₃ L k h n m v c₁ d₁ e₁ R : F)
    (hR : x₁ * (h ^ 2 * k) = R)
    (hy₁ : y₁ * e₁ = c₁ * y + d₁)
    (hLh : L * h = k * (n * y + m))
    (hx3 : x₃ * (h ^ 2 * k) = v) :
    (-(L * (x₃ - x₁) + y₁) - α₁ * x₃ - α₃) * (h ^ 3 * k * e₁)
      = (-(n * (v - R) * k * e₁) - c₁ * h ^ 3 * k) * y
        + (-(m * (v - R) * k * e₁) - d₁ * h ^ 3 * k - α₁ * v * h * e₁
            - α₃ * h ^ 3 * k * e₁) := by
  linear_combination (-(e₁ * h ^ 2 * k * (x₃ - x₁))) * hLh
    + (-(e₁ * k * (n * y + m)) - α₁ * h * e₁) * hx3
    + (e₁ * k * (n * y + m)) * hR
    + (-(h ^ 3 * k)) * hy₁

/-- **PROVEN** (2026-07-27). The chord branch, **with its one degenerate case
already excluded**:
the sum of two rational maps whose `x`-coordinate functions `A₁ / B₁` and
`A₂ / B₂` are genuinely different, expressed as `A₂ B₁ - A₁ B₂ ≠ 0`.

The certificates are taken apart into their five polynomials rather than passed as
`IsRationalMap`, because `hG` has to talk about `A₁, B₁, A₂, B₂` — the whole point
of this cut is that a witness has been FIXED and the degenerate one ruled out.
`IsRationalMap.add_of_ne` below reassembles it and discharges `hG`, so this leaf
is a statement about a chosen witness only, never about the map.

**The proof, from having closed `IsRationalMap.comp` and `IsRationalMap.isIsogeny`.**
Write `t = x P`, `y = y P`, and abbreviate the two certificates as
`x₁ B₁ = A₁`, `y₁ E₁ = C₁ y + D₁` and likewise with subscript `2`, all evaluated at
`t`. Put

  `K = B₁ B₂`,  `G = A₂ B₁ - A₁ B₂`,  `H = E₁ E₂ G`,
  `N = C₂ E₁ - C₁ E₂`,  `M = D₂ E₁ - D₁ E₂`,

so that the chord slope is `λ = K (N y + M) / H`. `hG` is exactly `G ≠ 0`, hence
`H ≠ 0`, which is what makes the witness below nondegenerate.

*Step 2: the pointwise identity.* Substituting into `Affine.addX` and clearing
denominators gives, on the locus where `K H ≠ 0` and all four points are nonzero,

  `x ((φ + ψ) P) · (H² K) (t) = U(t) · y + V(t)`

with `U = K³ (2 N M - N² (a₁ t + a₃)) + a₁ K² H N` and `V` the corresponding
`y`-free part; the `y²` produced by `λ²` is reduced by the Weierstrass equation
`y² = -(a₁ t + a₃) y + (t³ + a₂ t² + a₄ t + a₆)`, which is what leaves `y` to
degree ONE.

*Step 3: `U = 0`, and this is the crux.* Apply the identity at `-P` as well:
`x (-P) = x P`, `y (-P) = -y - a₁ t - a₃`, and `(φ + ψ) (-P) = -((φ + ψ) P)` has
the SAME `x`. Subtracting the two identities gives `U(t) · (2 y + a₁ t + a₃) = 0`,
and `2 y + a₁ t + a₃ = y - negY (x P) (y P)` vanishes exactly on the 2-torsion,
which is FINITE (`finite_nsmulKer` at `n = 2`). So `U` vanishes at infinitely many
`t` — `exists_point_veluPointX_eq` supplies a point over every `t` — hence `U = 0`.
This is the step the leaf's difficulty really lives in; it is not the branch
analysis, and note it needs BOTH ambient instances, through `finite_nsmulKer` and
through `exists_point_veluPointX_eq`.

*Step 4:* `(V, H² K)` is then the `x`-witness, `H² K ≠ 0` by `hG`, and the
`y`-witness comes out of `Affine.negAddY` by the same substitution, this time with
no cancellation needed because `y ((φ + ψ) P)` is genuinely affine in `y P`. That
last computation is `chordAdd_y_core`, and it consumes Step 3 in an essential way:
its hypothesis `hx3` is the `x`-identity **with `U` already zero**, since with `U`
present `L · (x₃ - x₁)` would be quadratic in `y` again.

*Step 5:* multiply both witnesses through by the polynomial cutting out the finite
bad locus (technique 1 of the module docstring), so that the certificate holds at
EVERY point rather than off it. Here that polynomial is
`Z = B₁ B₂ E₁ E₂ G · ∏ (X - s)`, the product ranging over the `x`-coordinates of
`ker φ ∪ ker ψ` — finite by `IsRationalMap.finite_ker`, using `h0φ` / `h0ψ`. Where
`Z(t) = 0` both sides of each certificate are `0`; where `Z(t) ≠ 0` every
denominator is invertible and `P` lies in neither kernel, which is exactly the
good locus of Step 2.

**`hsum` is NOT consumed, and that is a fact about the geometry rather than
slack.** Underscore-prefixed accordingly, and kept in the signature because
`IsRationalMap.add_of_ne` has it to hand and because it records the intent of the
cut. The reason it is unnecessary: on the good locus `x (φ P) ≠ x (ψ P)`, and two
points of a Weierstrass curve with DIFFERENT `x`-coordinates can never sum to `0`
— `Affine.Point.add_of_X_ne` returns a `some` outright. So `(φ + ψ) P ≠ 0` is
automatic wherever the chord formula applies, and `ker (φ + ψ)` never has to be
handled at all. (Nor could it be handled the same way as the other two kernels:
`IsRationalMap.finite_ker` needs `IsRationalMap (φ + ψ)`, which is the conclusion.) -/
theorem IsRationalMap.add_of_x_ne [IsAlgClosed F] [W.IsElliptic] {φ ψ : W.Point →+ W'.Point}
    {A₁ B₁ C₁ D₁ E₁ A₂ B₂ C₂ D₂ E₂ : F[X]}
    (hB₁ : B₁ ≠ 0) (hE₁ : E₁ ≠ 0)
    (hcert₁ : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B₁.eval (veluPointX P) = A₁.eval (veluPointX P) ∧
        veluPointY (φ P) * E₁.eval (veluPointX P)
          = C₁.eval (veluPointX P) * veluPointY P + D₁.eval (veluPointX P))
    (hB₂ : B₂ ≠ 0) (hE₂ : E₂ ≠ 0)
    (hcert₂ : ∀ P : W.Point, ψ P ≠ 0 →
      veluPointX (ψ P) * B₂.eval (veluPointX P) = A₂.eval (veluPointX P) ∧
        veluPointY (ψ P) * E₂.eval (veluPointX P)
          = C₂.eval (veluPointX P) * veluPointY P + D₂.eval (veluPointX P))
    (h0φ : φ ≠ 0) (h0ψ : ψ ≠ 0) (_hsum : φ + ψ ≠ 0)
    (hG : A₂ * B₁ - A₁ * B₂ ≠ 0) :
    IsRationalMap (φ + ψ) := by
  classical
  -- The auxiliary polynomials of the chord formula, and the two witnesses `U`, `V`.
  obtain ⟨G, hGd⟩ : ∃ p : F[X], p = A₂ * B₁ - A₁ * B₂ := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ p : F[X], p = B₁ * B₂ := ⟨_, rfl⟩
  obtain ⟨Hp, hHd⟩ : ∃ p : F[X], p = E₁ * E₂ * G := ⟨_, rfl⟩
  obtain ⟨Nn, hNd⟩ : ∃ p : F[X], p = C₂ * E₁ - C₁ * E₂ := ⟨_, rfl⟩
  obtain ⟨Mm, hMd⟩ : ∃ p : F[X], p = D₂ * E₁ - D₁ * E₂ := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ p : F[X], p =
      K ^ 3 * (Polynomial.C 2 * Nn * Mm
          - Nn ^ 2 * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
        + Polynomial.C W'.a₁ * K ^ 2 * Hp * Nn := ⟨_, rfl⟩
  obtain ⟨V, hVd⟩ : ∃ p : F[X], p =
      K ^ 3 * (Nn ^ 2 * (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
            + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆) + Mm ^ 2)
        + Polynomial.C W'.a₁ * K ^ 2 * Hp * Mm - Polynomial.C W'.a₂ * Hp ^ 2 * K
        - (A₁ * B₂ + A₂ * B₁) * Hp ^ 2 := ⟨_, rfl⟩
  obtain ⟨Cy, hCyd⟩ : ∃ p : F[X],
      p = -(Nn * (V - A₁ * B₂ * Hp ^ 2) * K * E₁) - C₁ * Hp ^ 3 * K := ⟨_, rfl⟩
  obtain ⟨Dy, hDyd⟩ : ∃ p : F[X],
      p = -(Mm * (V - A₁ * B₂ * Hp ^ 2) * K * E₁) - D₁ * Hp ^ 3 * K
        - Polynomial.C W'.a₁ * V * Hp * E₁ - Polynomial.C W'.a₃ * Hp ^ 3 * K * E₁ := ⟨_, rfl⟩
  have hG0 : G ≠ 0 := by rw [hGd]; exact hG
  have hK0 : K ≠ 0 := by rw [hKd]; exact mul_ne_zero hB₁ hB₂
  have hH0 : Hp ≠ 0 := by rw [hHd]; exact mul_ne_zero (mul_ne_zero hE₁ hE₂) hG0
  -- **Step 2**: the pointwise chord identity on the good locus. The second
  -- component is the `y`-identity, stated as an implication so that it can consume
  -- Step 3 (`U = 0`) once that is available.
  have hkey : ∀ P : W.Point, P ≠ 0 → φ P ≠ 0 → ψ P ≠ 0 →
      B₁.eval (veluPointX P) ≠ 0 → B₂.eval (veluPointX P) ≠ 0 →
      E₁.eval (veluPointX P) ≠ 0 → E₂.eval (veluPointX P) ≠ 0 →
      G.eval (veluPointX P) ≠ 0 →
      veluPointX (φ P + ψ P) * (Hp ^ 2 * K).eval (veluPointX P)
            = U.eval (veluPointX P) * veluPointY P + V.eval (veluPointX P)
        ∧ (veluPointX (φ P + ψ P) * (Hp ^ 2 * K).eval (veluPointX P)
              = V.eval (veluPointX P) →
            veluPointY (φ P + ψ P) * (Hp ^ 3 * K * E₁).eval (veluPointX P)
              = Cy.eval (veluPointX P) * veluPointY P + Dy.eval (veluPointX P)) := by
    rintro (_ | ⟨t, y, hns⟩) hP0 hφP hψP hb₁ hb₂ he₁ he₂ hg
    · exact absurd rfl hP0
    simp only [veluPointX_some, veluPointY_some] at hb₁ hb₂ he₁ he₂ hg ⊢
    obtain ⟨hx₁, hy₁⟩ := hcert₁ (Affine.Point.some t y hns) hφP
    obtain ⟨hx₂, hy₂⟩ := hcert₂ (Affine.Point.some t y hns) hψP
    simp only [veluPointX_some, veluPointY_some] at hx₁ hy₁ hx₂ hy₂
    rcases hφ' : φ (Affine.Point.some t y hns) with _ | ⟨x₁, y₁', hns₁⟩
    · exact absurd hφ' hφP
    rcases hψ' : ψ (Affine.Point.some t y hns) with _ | ⟨x₂, y₂', hns₂⟩
    · exact absurd hψ' hψP
    rw [hφ'] at hx₁ hy₁
    rw [hψ'] at hx₂ hy₂
    simp only [veluPointX_some, veluPointY_some] at hx₁ hy₁ hx₂ hy₂
    -- `hG` is exactly what makes the two `x`-coordinates differ at `t`.
    have hxne : x₁ ≠ x₂ := by
      intro hc
      refine hg ?_
      rw [hGd]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul]
      rw [← hx₁, ← hx₂, hc]
      ring
    have hx3form : veluPointX (Affine.Point.some x₁ y₁' hns₁ + Affine.Point.some x₂ y₂' hns₂)
        = W'.addX x₁ x₂ (W'.slope x₁ x₂ y₁' y₂') := by
      rw [Affine.Point.add_of_X_ne hxne]; rfl
    have hy3form : veluPointY (Affine.Point.some x₁ y₁' hns₁ + Affine.Point.some x₂ y₂' hns₂)
        = W'.addY x₁ x₂ y₁' (W'.slope x₁ x₂ y₁' y₂') := by
      rw [Affine.Point.add_of_X_ne hxne]; rfl
    have hL : W'.slope x₁ x₂ y₁' y₂' * (x₁ - x₂) = y₁' - y₂' := by
      rw [Affine.slope_of_X_ne hxne]
      exact div_mul_cancel₀ _ (sub_ne_zero.2 hxne)
    have hEq : y ^ 2 + W.a₁ * t * y + W.a₃ * y
        = t ^ 3 + W.a₂ * t ^ 2 + W.a₄ * t + W.a₆ := (Affine.equation_iff ..).1 hns.1
    have hLh := chordAdd_slope_core (A₁.eval t) (B₁.eval t) (C₁.eval t) (D₁.eval t) (E₁.eval t)
      (A₂.eval t) (B₂.eval t) (C₂.eval t) (D₂.eval t) (E₂.eval t)
      x₁ y₁' x₂ y₂' y (W'.slope x₁ x₂ y₁' y₂') hx₁ hx₂ hy₁ hy₂ hL
    have hkx : (x₁ + x₂) * (B₁.eval t * B₂.eval t)
        = A₁.eval t * B₂.eval t + A₂.eval t * B₁.eval t := by
      linear_combination (B₂.eval t) * hx₁ + (B₁.eval t) * hx₂
    have hR : x₁ * ((E₁.eval t * E₂.eval t
          * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t)) ^ 2 * (B₁.eval t * B₂.eval t))
        = A₁.eval t * B₂.eval t * (E₁.eval t * E₂.eval t
          * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t)) ^ 2 := by
      linear_combination (B₂.eval t * (E₁.eval t * E₂.eval t
        * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t)) ^ 2) * hx₁
    refine ⟨?_, ?_⟩
    · have hcore := chordAdd_x_core W'.a₁ W'.a₂ W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ t y x₁ x₂
        (W'.slope x₁ x₂ y₁' y₂') (B₁.eval t * B₂.eval t)
        (E₁.eval t * E₂.eval t * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t))
        (C₂.eval t * E₁.eval t - C₁.eval t * E₂.eval t)
        (D₂.eval t * E₁.eval t - D₁.eval t * E₂.eval t)
        (A₁.eval t * B₂.eval t + A₂.eval t * B₁.eval t) hkx hEq hLh
      rw [hx3form, hUd, hVd, hHd, hKd, hNd, hMd, hGd]
      simp only [Affine.addX, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
      linear_combination hcore
    · intro hx3
      rw [hx3form, hHd, hKd, hGd] at hx3
      simp only [Affine.addX, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub]
        at hx3
      have hycore := chordAdd_y_core W'.a₁ W'.a₃ y y₁' x₁
        (W'.slope x₁ x₂ y₁' y₂' ^ 2 + W'.a₁ * W'.slope x₁ x₂ y₁' y₂' - W'.a₂ - x₁ - x₂)
        (W'.slope x₁ x₂ y₁' y₂') (B₁.eval t * B₂.eval t)
        (E₁.eval t * E₂.eval t * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t))
        (C₂.eval t * E₁.eval t - C₁.eval t * E₂.eval t)
        (D₂.eval t * E₁.eval t - D₁.eval t * E₂.eval t)
        (V.eval t) (C₁.eval t) (D₁.eval t) (E₁.eval t)
        (A₁.eval t * B₂.eval t * (E₁.eval t * E₂.eval t
          * (A₂.eval t * B₁.eval t - A₁.eval t * B₂.eval t)) ^ 2) hR hy₁ hLh hx3
      rw [hy3form, hCyd, hDyd, hHd, hKd, hNd, hMd, hGd]
      simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_neg]
      linear_combination hycore
  -- The three finiteness inputs.
  have hkerφ : (AddMonoidHom.ker φ : Set W.Point).Finite :=
    IsRationalMap.finite_ker ⟨A₁, B₁, C₁, D₁, E₁, hB₁, hE₁, hcert₁⟩ h0φ
  have hkerψ : (AddMonoidHom.ker ψ : Set W.Point).Finite :=
    IsRationalMap.finite_ker ⟨A₂, B₂, C₂, D₂, E₂, hB₂, hE₂, hcert₂⟩ h0ψ
  have htors : {P : W.Point | (2 : ℕ) • P = 0}.Finite := finite_nsmulKer two_ne_zero
  have hprod0 : B₁ * B₂ * E₁ * E₂ * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hB₁ hB₂) hE₁) hE₂) hG0
  have hbad : ({t : F | (B₁ * B₂ * E₁ * E₂ * G).eval t = 0}
      ∪ (veluPointX '' (AddMonoidHom.ker φ : Set W.Point)
        ∪ (veluPointX '' (AddMonoidHom.ker ψ : Set W.Point)
          ∪ veluPointX '' {P : W.Point | (2 : ℕ) • P = 0}))).Finite :=
    (Polynomial.finite_setOf_isRoot hprod0).union
      ((hkerφ.image _).union ((hkerψ.image _).union (htors.image _)))
  -- **Step 3**: `U = 0`, the crux. Compare the identity at `P` and at `-P`.
  have hU : U = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot U (Set.Infinite.mono ?_ hbad.infinite_compl)
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    obtain ⟨P, hP0, hPx⟩ := exists_point_veluPointX_eq (W := W) t
    obtain ⟨x0, y0, hns0, rfl⟩ :
        ∃ (x0 : F) (y0 : F) (h : W.Nonsingular x0 y0), P = Affine.Point.some x0 y0 h := by
      cases P with
      | zero => exact absurd rfl hP0
      | some a b h => exact ⟨a, b, h, rfl⟩
    simp only [veluPointX_some] at hPx
    subst hPx
    have hφP : φ (Affine.Point.some x0 y0 hns0) ≠ 0 := fun hc =>
      h2 ⟨_, AddMonoidHom.mem_ker.2 hc, rfl⟩
    have hψP : ψ (Affine.Point.some x0 y0 hns0) ≠ 0 := fun hc =>
      h3 ⟨_, AddMonoidHom.mem_ker.2 hc, rfl⟩
    have htor : (2 : ℕ) • (Affine.Point.some x0 y0 hns0 : W.Point) ≠ 0 := fun hc =>
      h4 ⟨_, hc, rfl⟩
    have hprod : (B₁ * B₂ * E₁ * E₂ * G).eval x0 ≠ 0 := h1
    simp only [Polynomial.eval_mul, mul_ne_zero_iff] at hprod
    obtain ⟨⟨⟨⟨hb₁, hb₂⟩, he₁⟩, he₂⟩, hg⟩ := hprod
    have hP0' : (Affine.Point.some x0 y0 hns0 : W.Point) ≠ 0 := hP0
    have hnegP0 : (-(Affine.Point.some x0 y0 hns0 : W.Point)) ≠ 0 := neg_ne_zero.2 hP0'
    have hnegx : veluPointX (-(Affine.Point.some x0 y0 hns0 : W.Point)) = x0 := by
      rw [velu_pointX_neg]; rfl
    have hA := (hkey (Affine.Point.some x0 y0 hns0) hP0' hφP hψP
      (by simpa using hb₁) (by simpa using hb₂) (by simpa using he₁) (by simpa using he₂)
      (by simpa using hg)).1
    have hB := (hkey (-(Affine.Point.some x0 y0 hns0 : W.Point)) hnegP0
      (by rw [map_neg]; exact neg_ne_zero.2 hφP)
      (by rw [map_neg]; exact neg_ne_zero.2 hψP)
      (by rw [hnegx]; exact hb₁) (by rw [hnegx]; exact hb₂) (by rw [hnegx]; exact he₁)
      (by rw [hnegx]; exact he₂) (by rw [hnegx]; exact hg)).1
    have hnegsum : φ (-(Affine.Point.some x0 y0 hns0 : W.Point))
        + ψ (-(Affine.Point.some x0 y0 hns0 : W.Point))
        = -(φ (Affine.Point.some x0 y0 hns0) + ψ (Affine.Point.some x0 y0 hns0)) := by
      rw [map_neg, map_neg]; abel
    rw [hnegsum, velu_pointX_neg, hnegx, velu_pointY_neg _ hP0'] at hB
    simp only [veluPointX_some, veluPointY_some] at hA hB
    have hzero : U.eval x0 * (2 * y0 + W.a₁ * x0 + W.a₃) = 0 := by
      linear_combination hB - hA
    -- `2 y + a₁ x + a₃ = y - negY x y` vanishes exactly on the 2-torsion.
    have hne2 : 2 * y0 + W.a₁ * x0 + W.a₃ ≠ 0 := by
      intro hc
      refine htor ?_
      rw [two_nsmul]
      refine Affine.Point.add_self_of_Y_eq ?_
      show y0 = W.negY x0 y0
      simp only [Affine.negY]
      linear_combination hc
    show U.eval x0 = 0
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exact absurd h hne2
  -- **Step 5**: the polynomial cutting out the finite bad locus.
  have hSk : (veluPointX '' (AddMonoidHom.ker φ : Set W.Point)
      ∪ veluPointX '' (AddMonoidHom.ker ψ : Set W.Point)).Finite :=
    (hkerφ.image _).union (hkerψ.image _)
  obtain ⟨Zk, hZk0, hZkroot⟩ : ∃ Zk : F[X], Zk ≠ 0 ∧
      ∀ s ∈ veluPointX '' (AddMonoidHom.ker φ : Set W.Point)
        ∪ veluPointX '' (AddMonoidHom.ker ψ : Set W.Point), Zk.eval s = 0 := by
    refine ⟨∏ s ∈ hSk.toFinset, (Polynomial.X - Polynomial.C s),
      Finset.prod_ne_zero_iff.2 fun s _ => Polynomial.X_sub_C_ne_zero s, ?_⟩
    intro s hs
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (hSk.mem_toFinset.2 hs) (by simp)
  obtain ⟨Z, hZd⟩ : ∃ p : F[X], p = B₁ * B₂ * E₁ * E₂ * G * Zk := ⟨_, rfl⟩
  have hZ0 : Z ≠ 0 := by rw [hZd]; exact mul_ne_zero hprod0 hZk0
  refine ⟨V * Z, Hp ^ 2 * K * Z, Cy * Z, Dy * Z, Hp ^ 3 * K * E₁ * Z,
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hH0) hK0) hZ0,
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hH0) hK0) hE₁) hZ0, ?_⟩
  intro P hP
  simp only [AddMonoidHom.add_apply] at hP ⊢
  by_cases hz : Z.eval (veluPointX P) = 0
  · constructor <;> simp [Polynomial.eval_mul, hz]
  have hz' : (B₁ * B₂ * E₁ * E₂ * G * Zk).eval (veluPointX P) ≠ 0 := by rw [← hZd]; exact hz
  simp only [Polynomial.eval_mul, mul_ne_zero_iff] at hz'
  obtain ⟨⟨⟨⟨⟨hb₁, hb₂⟩, he₁⟩, he₂⟩, hg⟩, hzk⟩ := hz'
  have hP0 : P ≠ 0 := by rintro rfl; exact hP (by simp)
  have hφP : φ P ≠ 0 := fun hc =>
    hzk (hZkroot _ (Or.inl ⟨P, AddMonoidHom.mem_ker.2 hc, rfl⟩))
  have hψP : ψ P ≠ 0 := fun hc =>
    hzk (hZkroot _ (Or.inr ⟨P, AddMonoidHom.mem_ker.2 hc, rfl⟩))
  obtain ⟨hxid, hyid⟩ := hkey P hP0 hφP hψP hb₁ hb₂ he₁ he₂ hg
  rw [hU] at hxid
  simp only [Polynomial.eval_zero, zero_mul, zero_add] at hxid
  have hyid' := hyid hxid
  simp only [Polynomial.eval_mul] at hxid hyid' ⊢
  exact ⟨by linear_combination (Z.eval (veluPointX P)) * hxid,
    by linear_combination (Z.eval (veluPointX P)) * hyid'⟩

/-- **PROVEN** (Step 1 of the chord branch, 2026-07-27). The sum of two rational
maps that are not `0` and not equal or opposite to one another is rational,
**given `IsRationalMap.add_of_x_ne`** — that is, this theorem discharges the
degenerate case in which the two `x`-coordinate functions coincide.

The four hypotheses are exactly what makes `x ∘ φ` and `x ∘ ψ` DIFFERENT rational
functions, so that the chord formula applies away from a finite set. See the
section docstring above for why that is the correct dividing line.

*The proof.* Suppose the chosen witnesses satisfy `A₂ B₁ - A₁ B₂ = 0`. At any `P`
outside the finite set `ker φ ∪ ker ψ ∪ {P ≠ 0 : (B₁B₂)(x P) = 0} ∪ {0}` — finite
because `IsRationalMap.isIsogeny` makes both kernels finite and
`finite_veluPointX_preimage` handles the roots of `B₁ B₂` — the two certificates
give `x (φ P) (B₁B₂)(x P) = x (ψ P) (B₁B₂)(x P)`, hence `x (φ P) = x (ψ P)`, hence
`φ P = ψ P` or `φ P = -(ψ P)` by `eq_or_eq_neg_of_veluPointX_eq`. So `φ` and `ψ`
agree up to sign off a finite set, and
`eq_or_add_eq_zero_of_finite_compl` upgrades that to `φ = ψ` or `φ + ψ = 0`,
contradicting `hdiff` or `hsum`.

Both of `hdiff` and `hsum` are therefore consumed HERE, and neither is passed on
to `add_of_x_ne` (which gets `hG` instead) — the degenerate case is the only place
they were ever needed. -/
theorem IsRationalMap.add_of_ne [IsAlgClosed F] [W.IsElliptic] {φ ψ : W.Point →+ W'.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ)
    (h0φ : φ ≠ 0) (h0ψ : ψ ≠ 0) (hsum : φ + ψ ≠ 0) (hdiff : φ ≠ ψ) :
    IsRationalMap (φ + ψ) := by
  classical
  have hφc := hφ
  have hψc := hψ
  obtain ⟨A₁, B₁, C₁, D₁, E₁, hB₁, hE₁, hcert₁⟩ := hφc
  obtain ⟨A₂, B₂, C₂, D₂, E₂, hB₂, hE₂, hcert₂⟩ := hψc
  refine IsRationalMap.add_of_x_ne hB₁ hE₁ hcert₁ hB₂ hE₂ hcert₂ h0φ h0ψ hsum ?_
  intro hG
  have hkerφ : (AddMonoidHom.ker φ : Set W.Point).Finite := IsRationalMap.finite_ker hφ h0φ
  have hkerψ : (AddMonoidHom.ker ψ : Set W.Point).Finite := IsRationalMap.finite_ker hψ h0ψ
  have hBz : {P : W.Point | P ≠ 0 ∧ veluPointX P ∈ {t : F | (B₁ * B₂).eval t = 0}}.Finite :=
    finite_veluPointX_preimage (Polynomial.finite_setOf_isRoot (mul_ne_zero hB₁ hB₂))
  have hfin : {P : W.Point | φ P ≠ ψ P ∧ φ P ≠ -(ψ P)}.Finite := by
    refine Set.Finite.subset (((hkerφ.union hkerψ).union hBz).insert 0) ?_
    intro P hP
    by_cases hP0 : P = 0
    · exact Set.mem_insert_iff.2 (Or.inl hP0)
    refine Set.mem_insert_iff.2 (Or.inr ?_)
    by_cases hφP : φ P = 0
    · exact Set.mem_union_left _ (Set.mem_union_left _ ((AddMonoidHom.mem_ker).2 hφP))
    by_cases hψP : ψ P = 0
    · exact Set.mem_union_left _ (Set.mem_union_right _ ((AddMonoidHom.mem_ker).2 hψP))
    by_cases hBP : (B₁ * B₂).eval (veluPointX P) = 0
    · exact Set.mem_union_right _ ⟨hP0, hBP⟩
    exfalso
    simp only [Polynomial.eval_mul, mul_eq_zero, not_or] at hBP
    obtain ⟨hb1, hb2⟩ := hBP
    have hx1 := (hcert₁ P hφP).1
    have hx2 := (hcert₂ P hψP).1
    have hGev : A₂.eval (veluPointX P) * B₁.eval (veluPointX P)
        - A₁.eval (veluPointX P) * B₂.eval (veluPointX P) = 0 := by
      have h := congrArg (Polynomial.eval (veluPointX P)) hG
      simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_zero] using h
    have hkey : veluPointX (ψ P) * (B₂.eval (veluPointX P) * B₁.eval (veluPointX P))
        = veluPointX (φ P) * (B₂.eval (veluPointX P) * B₁.eval (veluPointX P)) := by
      linear_combination B₁.eval (veluPointX P) * hx2 - B₂.eval (veluPointX P) * hx1 + hGev
    have hxx : veluPointX (φ P) = veluPointX (ψ P) :=
      (mul_right_cancel₀ (mul_ne_zero hb2 hb1) hkey).symm
    rcases eq_or_eq_neg_of_veluPointX_eq hφP hψP hxx with h | h
    · exact hP.1 h
    · exact hP.2 h
  rcases eq_or_add_eq_zero_of_finite_compl hfin with h | h
  · exact hdiff h
  · exact hsum h

/-- **PROVEN** (assembly, 2026-07-27). The pointwise sum of two rational maps is
rational, over an algebraically closed field and for an **elliptic** `W`.

**Both hypotheses were added on 2026-07-26 after the unqualified statement was
REFUTED.** See the FALSITY AUDIT of `IsRationalMap.add` below (namespace
`WeierstrassCurve.NotIsRationalMapAdd`, machine-checked as
`isRationalMap_add_is_false`, axiom-clean). In one line: `Affine F` contains
*singular* Weierstrass curves, and over `𝔽̄₂` the cuspidal cubic `y² = x³` has an
infinite point group in which every element is 2-torsion — so the group is not
divisible, it has index-2 subgroups, and a homomorphism onto a two-element
subgroup is rational **by the constant witness**. Two such maps with different
target `x`-coordinates have a non-rational sum.

`[W.IsElliptic]` and `[IsAlgClosed F]` are exactly what kills that class: together
they make `W.Point` divisible (`nsmul_surjective`), hence free of proper
finite-index subgroups, hence free of homomorphisms with finite image.

**What is left open, and what is not.** The statement itself is CLOSED here: the
three free reductions (`φ = 0` gives `ψ`, `ψ = 0` gives `φ`, `φ + ψ = 0` gives `0`,
all already rational) are discharged below, and the two remaining branches are the
named leaves `IsRationalMap.add_self` and `IsRationalMap.add_of_ne` immediately
above, where the geometry actually lives. The instance hypotheses are unchanged and
are still exactly what the FALSITY AUDIT requires: they enter through
`eq_zero_of_finite_range`, inside `add_of_ne`'s Step 1.

Note the case split is on the HOMOMORPHISMS, not pointwise on `P` — `φ = ψ` as
maps, not `φ P = ψ P` — which is what makes each branch a statement with a single
uniform formula and therefore a single pair of witness polynomials. -/
theorem IsRationalMap.add [IsAlgClosed F] [W.IsElliptic] {φ ψ : W.Point →+ W'.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (φ + ψ) := by
  classical
  by_cases hφ0 : φ = 0
  · rw [hφ0, zero_add]; exact hψ
  by_cases hψ0 : ψ = 0
  · rw [hψ0, add_zero]; exact hφ
  by_cases hsum : φ + ψ = 0
  · rw [hsum]; exact IsRationalMap.zero
  by_cases hdiff : φ = ψ
  · rw [hdiff]; exact hψ.add_self
  exact hφ.add_of_ne hψ hφ0 hψ0 hsum hdiff

/-! ### Isogenies -/

/-- An **isogeny** `W → W'`: a homomorphism of point groups given by rational
functions in the coordinates which, unless it is the zero map, is surjective with
finite kernel.

The zero map is admitted, with degree `0`, so that `End W` is a ring.

`surjective` and `finite_ker` are *fields* rather than consequences on purpose.
Both are genuinely geometric — surjectivity of a non-constant morphism of curves
is properness, and it is false for a general group homomorphism with divisible
image — so a construction that produces an isogeny must discharge them, and the
cost is paid where the geometry is rather than silently. -/
structure IsIsogeny (φ : W.Point →+ W'.Point) : Prop where
  /-- The map is given by rational functions in the coordinates. -/
  isRationalMap : IsRationalMap φ
  /-- A nonzero isogeny is surjective on points. -/
  surjective : φ ≠ 0 → Function.Surjective φ
  /-- A nonzero isogeny has finite kernel. -/
  finite_ker : φ ≠ 0 → (AddMonoidHom.ker φ : Set W.Point).Finite

theorem IsIsogeny.zero : IsIsogeny (0 : W.Point →+ W'.Point) where
  isRationalMap := IsRationalMap.zero
  surjective h := absurd rfl h
  finite_ker h := absurd rfl h

theorem IsIsogeny.id : IsIsogeny (AddMonoidHom.id W.Point) where
  isRationalMap := IsRationalMap.id
  surjective _ := Function.surjective_id
  finite_ker _ := by
    have h : (AddMonoidHom.ker (AddMonoidHom.id W.Point) : Set W.Point) = {0} := by
      ext P; simp
    rw [h]; exact Set.finite_singleton _

theorem IsIsogeny.neg {φ : W.Point →+ W'.Point} (h : IsIsogeny φ) : IsIsogeny (-φ) where
  isRationalMap := h.isRationalMap.neg
  surjective hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    intro Q
    obtain ⟨P, hP⟩ := h.surjective hφ (-Q)
    exact ⟨P, by simp [hP]⟩
  finite_ker hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    have hker : (AddMonoidHom.ker (-φ) : Set W.Point) = (AddMonoidHom.ker φ : Set W.Point) := by
      ext P; simp [AddMonoidHom.mem_ker]
    rw [hker]; exact h.finite_ker hφ

/-! ### FALSITY AUDIT: `IsIsogeny.add` was FALSE, and is repaired here

**Refuted 2026-07-26 by the machine-checked counterexample below; the axiom audit
of `NotIsIsogenyAdd.isIsogeny_add_is_false` is `[propext, Classical.choice,
Quot.sound]`, so this is a genuine refutation and not a vacuous one.**

The statement as originally cut carried no hypothesis on `F`:

  `theorem IsIsogeny.add {φ ψ : W.Point →+ W'.Point}`
  `    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ)`

Instantiate it at `φ = ψ = AddMonoidHom.id`. That *is* an isogeny over **every**
field — `IsIsogeny.id` is proven unconditionally, because the identity is rational,
surjective, and has kernel `{0}` — so the conclusion asserts that
`[2] : W(F) → W(F)` is surjective whenever it is nonzero, i.e. that `W(F)` is
2-divisible. That is false for most curves over most fields: `E(ℚ)` of positive
rank is the familiar instance, and a finite field gives the cheapest formalisable
one.

Take `W₅ : y² = x³ - x` over `𝔽₅`, whose group of points is `ℤ/2 × ℤ/4`:

* `T = (0,0)` has `y = W₅.negY x y`, so `T + T = 0` while `T ≠ 0`;
* `P = (2,1)` has `y ≠ W₅.negY x y`, so `P + P ≠ 0`, hence `[2] ≠ 0`.

`W₅(𝔽₅)` is finite (via `Affine.nonsingularPointEquiv`), so `[2]` — not injective,
because it kills both `0` and `T` — cannot be surjective either.

**Why it is false, in one line.** Surjectivity *on `F`-points* is not a property of
a morphism of curves at all; it is a property of the base field. The file already
knows this: `nsmul_surjective` carries `[IsAlgClosed F]` for exactly this reason,
and `[2]` is the very map that leaf is about. `IsIsogeny.add` simply failed to
carry the same hypothesis.

**The repair, below.** `IsIsogeny.add` is restated with `[IsAlgClosed F]` and is
then a theorem, proven from `IsRationalMap.add` together with one new leaf,
`IsRationalMap.isIsogeny`, which isolates the honest geometric content: over an
algebraically closed field the `surjective` and `finite_ker` fields of `IsIsogeny`
are automatic.

**Consequence for consumers.** `endSubring` — and hence `End W`,
`End.sq_eq_intCast_iff`, `End.toIsogeny` — inherit `[IsAlgClosed F]`. Every
existing consumer (`MazurTorsion.lean`'s Atkin–Lehner leaves at levels 125 and
169) already works over `AlgebraicClosure ℚ`, so nothing downstream is lost.
`IsIsogeny.zero`, `IsIsogeny.id`, `IsIsogeny.neg` and `IsIsogeny.comp` are
untouched: each is true over an arbitrary field, and each is proven.
-/

namespace NotIsIsogenyAdd

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `y² = x³ - x` over `𝔽₅`. Its group of points is `ℤ/2 × ℤ/4`. -/
def W₅ : Affine (ZMod 5) := ⟨0, 0, 0, -1, 0⟩

theorem nonsingular_zero_zero : W₅.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

theorem nonsingular_two_one : W₅.Nonsingular 2 1 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

/-- The 2-torsion point `(0,0)`. -/
def T : W₅.Point := Affine.Point.some 0 0 nonsingular_zero_zero

/-- A point of order 4, witnessing that `[2] ≠ 0`. -/
def P : W₅.Point := Affine.Point.some 2 1 nonsingular_two_one

theorem T_ne_zero : T ≠ 0 := Affine.Point.some_ne_zero _

theorem T_add_T : T + T = 0 :=
  Affine.Point.add_self_of_Y_eq (h₁ := nonsingular_zero_zero)
    (show (0 : ZMod 5) = W₅.negY 0 0 by decide)

theorem P_add_P_ne_zero : P + P ≠ 0 := by
  rw [show P + P = _ from Affine.Point.add_self_of_Y_ne (h₁ := nonsingular_two_one)
    (show (1 : ZMod 5) ≠ W₅.negY 2 1 by decide)]
  exact Affine.Point.some_ne_zero _

/-- Doubling on `W₅(𝔽₅)` is not an isogeny: it is nonzero, but on a finite group it
is not injective, hence not surjective. -/
theorem not_isIsogeny_add :
    ¬ IsIsogeny (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) := by
  intro h
  haveI : Finite W₅.Point := by
    haveI : Finite (WithZero {xy : ZMod 5 × ZMod 5 // W₅.Nonsingular xy.1 xy.2}) :=
      inferInstanceAs (Finite (Option _))
    exact Finite.of_equiv _ (Affine.nonsingularPointEquiv W₅).symm
  have happ : ∀ Q : W₅.Point,
      (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q = Q + Q := fun Q => rfl
  have hne : AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point ≠ 0 := by
    intro hc
    have hc' := congrArg (fun f : W₅.Point →+ W₅.Point => f P) hc
    simp only [AddMonoidHom.zero_apply, happ] at hc'
    exact P_add_P_ne_zero hc'
  have hinj : Function.Injective (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) :=
    (Finite.injective_iff_surjective
      (f := fun Q => (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q)).2
      (h.surjective hne)
  exact T_ne_zero (hinj (by simp only [happ, T_add_T, add_zero]))

/-- **The refutation, assembled.** Both hypotheses of the original `IsIsogeny.add`
are discharged by `IsIsogeny.id`, so the unconditional statement is false. -/
theorem isIsogeny_add_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] {W W' : Affine F}
        {φ ψ : W.Point →+ W'.Point}, IsIsogeny φ → IsIsogeny ψ → IsIsogeny (φ + ψ) :=
  fun h => not_isIsogeny_add (h IsIsogeny.id IsIsogeny.id)

end NotIsIsogenyAdd

/-! ### FALSITY AUDIT: `[IsAlgClosed F]` IS NOT ENOUGH — `Affine F` CONTAINS SINGULAR CURVES

**Refuted 2026-07-26.** The audit above repaired `IsIsogeny.add` by adding
`[IsAlgClosed F]`, on the reasoning that the failure was surjectivity *on
`F`-points* and that algebraic closure repairs it. That reasoning is correct as far
as it goes and it is **not sufficient**, because it silently assumes `W` is an
elliptic curve. It need not be: `Affine F` is *any* Weierstrass curve, and mathlib
gives `Affine.Point` its `AddCommGroup` structure with **no** nonsingularity
hypothesis (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`), because
the nonsingular points of a singular cubic form a group too.

**The counterexample.** Let `K = 𝔽̄₂` and let `Wc : y² = x³` be the cuspidal cubic
over it — a *singular* Weierstrass curve, so `Wc.IsElliptic` is false, but
`Wc.Point` is a perfectly good abelian group. Two facts about it:

* `negY x y = -y - a₁x - a₃ = -y = y` in characteristic 2, so `-P = P` and **every
  point is 2-torsion**: `Wc.Point` is an `𝔽₂`-vector space.
* `s ↦ (s², s³)` is an injection from `K \ {0}` into the nonsingular points, so
  `Wc.Point` is **infinite**.

An infinite `𝔽₂`-vector space is not divisible — `2 · G = 0 ≠ G` — so it has proper
subgroups of index 2, in abundance. And that is fatal, because of what
`IsRationalMap` does *not* say:

> **`IsRationalMap φ` constrains only the points `P` with `φ P ≠ 0`.**

So if the image of `φ` is the two-element subgroup `{0, Q}`, every constrained
point has the *same* image, and the constant tuple
`(A, B, C, D, E) = (C x(Q), 1, 0, C y(Q), 1)` satisfies the certificate. No
algebraicity whatsoever is being asserted.

Both refutations below are machine-checked and axiom-clean:

* `isRationalMap_isIsogeny_is_false` — such a `φ` is rational and nonzero but has
  two-element image, so it is not surjective on the infinite `Wc.Point`.
* `isRationalMap_add_is_false` — take `φ = f₁ ⊗ Q₁` and `ψ = f₂ ⊗ Q₂` for two
  independent coordinate functionals of an `𝔽₂`-basis. Each is rational. Their sum
  is `Q₁` on one infinite level set and `Q₂` on another, so its `x`-witness would
  need `A/B ≡ x(Q₁)` and `A/B ≡ x(Q₂)` — each forced by a polynomial with infinitely
  many roots — and `x(Q₁) ≠ x(Q₂)`.

**The repair.** `IsRationalMap.add` and `IsRationalMap.isIsogeny` carry
`[W.IsElliptic]` (and `IsRationalMap.add` also `[IsAlgClosed F]`), which is
inherited by `IsIsogeny.add`, `endSubring`, `End` and the `End.*` API. Over an
algebraically closed field an elliptic curve's point group is divisible — that is
`nsmul_surjective`, already a leaf of this file with exactly these two hypotheses —
so it has no proper finite-index subgroup and no homomorphism with finite image.
Every consumer (`MazurTorsion.lean`'s Atkin–Lehner leaves) works with a curve
carrying `[E.IsElliptic]` over `AlgebraicClosure ℚ`, so nothing downstream is lost.

**What is NOT claimed.** `[W'.IsElliptic]` is deliberately not added: no
counterexample is known that needs it, and an unnecessary hypothesis on a leaf is a
cost to its consumers. Also unformalised, but worth recording because it shows
`[IsAlgClosed F]` on `IsRationalMap.add` is doing real work and is not mere
symmetry with its consumer: the statement is false for *genuinely elliptic* curves
over `ℚ` too. Take `E : y² = x³ - 25x`, which has rank 1 and full rational
2-torsion, so `E(ℚ) ≅ ℤ × (ℤ/2)²`; let `f₁, f₂ : E(ℚ) → ℤ/2` be two independent
functionals and `T₁ = (0,0)`, `T₂ = (5,0)`. The same constant-witness argument
applies verbatim. The refuting check is one line: `E(ℚ)` has a subgroup of index 2
exactly when `E(ℚ)/2E(ℚ) ≠ 0`, which holds for every curve of positive rank.
-/

namespace NotIsRationalMapAdd

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- An algebraic closure of `𝔽₂`. -/
abbrev K := AlgebraicClosure (ZMod 2)

noncomputable local instance : DecidableEq K := Classical.decEq _

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem two_eq_zero : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

/-- The **cuspidal cubic** `y² = x³` over `𝔽̄₂`: a singular Weierstrass curve, so
`IsElliptic` fails, but `Affine.Point` still makes its nonsingular points a group. -/
noncomputable def Wc : Affine K := ⟨0, 0, 0, 0, 0⟩

theorem Wc_a₁ : Wc.a₁ = 0 := rfl
theorem Wc_a₂ : Wc.a₂ = 0 := rfl
theorem Wc_a₃ : Wc.a₃ = 0 := rfl
theorem Wc_a₄ : Wc.a₄ = 0 := rfl
theorem Wc_a₆ : Wc.a₆ = 0 := rfl

/-- The point group of the cuspidal cubic. -/
abbrev G := Wc.Point

/-- `(s², s³)` is a nonsingular point of `Wc` for every `s ≠ 0`: it satisfies
`y² = x³`, and the only singular point of `Wc` is the cusp `x = 0`. -/
theorem nonsing {s : K} (hs : s ≠ 0) : Wc.Nonsingular (s ^ 2) (s ^ 3) := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  refine ⟨by simp only [Wc_a₁, Wc_a₂, Wc_a₃, Wc_a₄, Wc_a₆]; ring, Or.inl ?_⟩
  simp only [Wc_a₁, Wc_a₂, Wc_a₄, zero_mul]
  intro hc
  exact pow_ne_zero 4 hs (by linear_combination -hc - (s ^ 4) * two_eq_zero)

/-- **Every point of `Wc` is 2-torsion**, because `negY x y = -y = y` in
characteristic 2, so `-P = P`. This is what makes `G` an `𝔽₂`-vector space. -/
theorem two_nsmul_eq_zero (P : G) : (2 : ℕ) • P = 0 := by
  rw [two_nsmul]
  cases P with
  | zero => show (0 : G) + (0 : G) = 0; exact add_zero 0
  | some x y h =>
      refine Affine.Point.add_self_of_Y_eq (h₁ := h) ?_
      show y = Wc.negY x y
      simp only [Affine.negY, Wc_a₁, Wc_a₃]
      linear_combination y * two_eq_zero

noncomputable local instance : Module (ZMod 2) G := AddCommGroup.zmodModule two_nsmul_eq_zero

/-- `veluPointX` is injective on the nonzero points of `Wc`: `y` is determined by
`x` because `y ↦ y²` is injective in characteristic 2. -/
theorem veluPointX_inj {P Q : G} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : veluPointX P = veluPointX Q) : P = Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some x₂ y₂ h₂ =>
      simp only [veluPointX_some] at h
      subst h
      have e₁ : y₁ ^ 2 = x₁ ^ 3 := by
        have := h₁.1
        rw [Affine.equation_iff] at this
        simpa [Wc_a₁, Wc_a₂, Wc_a₃, Wc_a₄, Wc_a₆] using this
      have e₂ : y₂ ^ 2 = x₁ ^ 3 := by
        have := h₂.1
        rw [Affine.equation_iff] at this
        simpa [Wc_a₁, Wc_a₂, Wc_a₃, Wc_a₄, Wc_a₆] using this
      have hsq : (y₁ - y₂) ^ 2 = 0 := by
        linear_combination e₁ - e₂ + (y₂ ^ 2 - y₁ * y₂) * two_eq_zero
      have hy : y₁ = y₂ :=
        sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq)
      subst hy
      rfl

/-- `Wc.Point` is infinite: `s ↦ (s², s³)` injects `K \ {0}` into it. -/
theorem infinite_G : Infinite G := by
  haveI : Infinite ↥((({0} : Set K))ᶜ) :=
    ((Set.finite_singleton (0 : K)).infinite_compl).to_subtype
  refine Infinite.of_injective
    (fun s : ↥((({0} : Set K))ᶜ) =>
      (Point.some ((s : K) ^ 2) ((s : K) ^ 3) (nonsing s.2) : G)) ?_
  intro s t hst
  have hst' : ((s : K) ^ 2) = ((t : K) ^ 2) := by
    simpa using congrArg veluPointX hst
  have hsq : ((s : K) - (t : K)) ^ 2 = 0 := by
    linear_combination hst' + ((t : K) ^ 2 - (s : K) * (t : K)) * two_eq_zero
  exact Subtype.ext (sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq))

/-- **The pathological data.** `G` is an infinite `𝔽₂`-vector space, so it has two
coordinate functionals of an `𝔽₂`-basis together with the two basis vectors they
detect; the vectors have distinct `x`-coordinates, and each of the two joint level
sets is infinite. -/
theorem exists_pathological :
    ∃ (Q₁ Q₂ : G) (f₁ f₂ : G →ₗ[ZMod 2] ZMod 2),
      veluPointX Q₁ ≠ veluPointX Q₂ ∧ Q₁ ≠ 0 ∧ Q₂ ≠ 0 ∧
      {P : G | f₁ P = 1 ∧ f₂ P = 0}.Infinite ∧
      {P : G | f₁ P = 0 ∧ f₂ P = 1}.Infinite := by
  haveI := infinite_G
  let ι := Module.Basis.ofVectorSpaceIndex (ZMod 2) G
  let b : Module.Basis ι (ZMod 2) G := Module.Basis.ofVectorSpace (ZMod 2) G
  have hcoord : ∀ m n : ι, b.coord m (b n) = if n = m then 1 else 0 := by
    intro m n
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  haveI : Infinite ι := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI := Fintype.ofFinite ι
    haveI : Finite G := Finite.of_equiv _ b.equivFun.symm.toEquiv
    exact not_finite G
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have hbne : ∀ m : ι, b m ≠ 0 := fun m => b.ne_zero m
  have hlevel : ∀ m n : ι, m ≠ n →
      {P : G | b.coord m P = 1 ∧ b.coord n P = 0}.Infinite := by
    intro m n hmn
    haveI : Infinite ↥(({m, n} : Set ι)ᶜ) :=
      (((Set.finite_insert (a := m) (s := ({n} : Set ι))).2
        (Set.finite_singleton n)).infinite_compl).to_subtype
    refine Set.infinite_of_injective_forall_mem
      (f := fun k : ↥(({m, n} : Set ι)ᶜ) => b m + b (k : ι)) ?_ ?_
    · intro k l hkl
      exact Subtype.ext (b.injective (add_left_cancel hkl))
    · intro k
      have hk : (k : ι) ≠ m ∧ (k : ι) ≠ n := by
        have := k.2
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at this
        exact this
      refine ⟨?_, ?_⟩
      · rw [map_add, hcoord m m, hcoord m (k : ι), if_pos rfl, if_neg hk.1, add_zero]
      · rw [map_add, hcoord n m, hcoord n (k : ι), if_neg hmn, if_neg hk.2, add_zero]
  refine ⟨b i, b j, b.coord i, b.coord j, ?_, hbne i, hbne j, hlevel i j hij, ?_⟩
  · intro hc
    exact hij (b.injective (veluPointX_inj (hbne i) (hbne j) hc))
  · simpa [and_comm] using hlevel j i hij.symm

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

section Refute

variable (Q : G) (f : G →ₗ[ZMod 2] ZMod 2)

/-- `P ↦ f P • Q`, as a homomorphism of point groups. Its image is `{0, Q}`. -/
noncomputable def mk (Q : G) (f : G →ₗ[ZMod 2] ZMod 2) : G →+ G :=
  ((LinearMap.toSpanSingleton (ZMod 2) G Q).comp f).toAddMonoidHom

theorem mk_apply (P : G) : mk Q f P = f P • Q := rfl

/-- **A map with a two-element image is rational**, by the constant witness. This is
the whole pathology: `IsRationalMap` constrains only the points *outside* the
kernel, and here they all have the same image, so a constant tuple discharges it. -/
theorem isRationalMap_mk : IsRationalMap (mk Q f) := by
  refine ⟨Polynomial.C (veluPointX Q), 1, 0, Polynomial.C (veluPointY Q), 1,
    one_ne_zero, one_ne_zero, fun P hP => ?_⟩
  have hf : f P = 1 := by
    rcases zmod_two_cases (f P) with h | h
    · exact absurd (by rw [mk_apply, h]; exact zero_smul _ _) hP
    · exact h
  rw [mk_apply, hf, one_smul]
  simp

end Refute

/-- **REFUTATION 1: `IsRationalMap.isIsogeny` is FALSE without `[W.IsElliptic]`.**
On the singular curve `Wc` over the algebraically closed `𝔽̄₂`, the map
`f₁ ⊗ Q₁` is rational and nonzero, but its image is the two-element set `{0, Q₁}`
while `Wc.Point` is infinite, so it is not surjective. -/
theorem isRationalMap_isIsogeny_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] [IsAlgClosed F] {W W' : Affine F}
        {φ : W.Point →+ W'.Point}, IsRationalMap φ → IsIsogeny φ := by
  intro h
  obtain ⟨Q₁, Q₂, f₁, _f₂, hx, hQ₁, hQ₂, hS₁, _hS₂⟩ := exists_pathological
  obtain ⟨P₀, hP₀⟩ := hS₁.nonempty
  have hne : mk Q₁ f₁ ≠ 0 := by
    intro hc
    have := congrArg (fun g : G →+ G => g P₀) hc
    simp only [mk_apply, hP₀.1, one_smul, AddMonoidHom.zero_apply] at this
    exact hQ₁ this
  obtain ⟨P, hP⟩ := (h (isRationalMap_mk Q₁ f₁)).surjective hne Q₂
  rw [mk_apply] at hP
  rcases zmod_two_cases (f₁ P) with hc | hc
  · rw [hc, zero_smul (ZMod 2) Q₁] at hP; exact hQ₂ hP.symm
  · rw [hc, one_smul] at hP; exact hx (congrArg veluPointX hP)

/-- **REFUTATION 2: `IsRationalMap.add` is FALSE without `[W.IsElliptic]`.**
`φ = f₁ ⊗ Q₁` and `ψ = f₂ ⊗ Q₂` are each rational by the constant witness, but
`φ + ψ` equals `Q₁` on one infinite level set and `Q₂` on another, so its
`x`-witness `A/B` would have to be two different constants at once. -/
theorem isRationalMap_add_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] {W W' : Affine F}
        {φ ψ : W.Point →+ W'.Point},
        IsRationalMap φ → IsRationalMap ψ → IsRationalMap (φ + ψ) := by
  intro h
  obtain ⟨Q₁, Q₂, f₁, f₂, hx, hQ₁, hQ₂, hS₁, hS₂⟩ := exists_pathological
  obtain ⟨A, B, C, D, E, hB, _hE, hcert⟩ :=
    h (isRationalMap_mk Q₁ f₁) (isRationalMap_mk Q₂ f₂)
  -- On an infinite set where `φ + ψ` is the constant `Q`, the `x`-witness is forced.
  have key : ∀ (Q : G) (S : Set G), S.Infinite → Q ≠ 0 →
      (∀ P ∈ S, (mk Q₁ f₁ + mk Q₂ f₂) P = Q) →
      A = Polynomial.C (veluPointX Q) * B := by
    intro Q S hS hQ hval
    have hP0 : ∀ P ∈ S, P ≠ 0 := by
      intro P hPS hc
      exact hQ (by rw [← hval P hPS, hc, map_zero])
    have hroot : (veluPointX '' S)
        ⊆ {x : K | (A - Polynomial.C (veluPointX Q) * B).IsRoot x} := by
      rintro _ ⟨P, hPS, rfl⟩
      have := (hcert P (by rw [hval P hPS]; exact hQ)).1
      rw [hval P hPS] at this
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination -this
    have himg : (veluPointX '' S).Infinite :=
      hS.image (fun P hPS Q' hQS hEq => veluPointX_inj (hP0 P hPS) (hP0 Q' hQS) hEq)
    have := Polynomial.eq_zero_of_infinite_isRoot _ (himg.mono hroot)
    linear_combination this
  have h₁ : A = Polynomial.C (veluPointX Q₁) * B := by
    refine key Q₁ _ hS₁ hQ₁ (fun P hP => ?_)
    simp only [AddMonoidHom.add_apply, mk_apply, hP.1, hP.2]
    rw [one_smul, zero_smul (ZMod 2) Q₂, add_zero]
  have h₂ : A = Polynomial.C (veluPointX Q₂) * B := by
    refine key Q₂ _ hS₂ hQ₂ (fun P hP => ?_)
    simp only [AddMonoidHom.add_apply, mk_apply, hP.1, hP.2]
    rw [one_smul, zero_smul (ZMod 2) Q₁, zero_add]
  have : (Polynomial.C (veluPointX Q₁) - Polynomial.C (veluPointX Q₂)) * B = 0 := by
    linear_combination h₂ - h₁
  rcases mul_eq_zero.1 this with hc | hc
  · exact hx (Polynomial.C_inj.1 (sub_eq_zero.1 hc))
  · exact hB hc

end NotIsRationalMapAdd

/-- **PROVEN** (2026-07-27). Over an **algebraically closed** field and for an
**elliptic** `W`, a homomorphism of point groups that is given by rational functions
in the coordinates already **is** an isogeny: the `surjective` and `finite_ker` fields
of `IsIsogeny` come for free there.

This is the honest geometric content that the unconditional `IsIsogeny.add`
silently assumed, and the first FALSITY AUDIT above is the proof that
`[IsAlgClosed F]` cannot be dropped.

**`[W.IsElliptic]` was added 2026-07-26 and cannot be dropped either**: see the
second FALSITY AUDIT above, machine-checked as
`NotIsRationalMapAdd.isRationalMap_isIsogeny_is_false`. Over `𝔽̄₂` the singular
cuspidal cubic has an infinite point group of exponent 2, hence an index-2 subgroup,
and a homomorphism onto a two-element image is rational by the constant witness
while being wildly non-surjective. Algebraic closure does not help, because the
obstruction is that the *curve* is singular, not that the field is small.

**The proof, as written.** Everything runs off the four helpers in
*Consequences of divisibility* above, and the single place divisibility is used is
`eq_zero_of_finite_range` (a homomorphism out of `W.Point` with finite image is
zero). Note `W'` is NOT assumed elliptic and does not need to be: the target only
ever contributes `eq_or_eq_neg_of_veluPointX_eq`, which holds for any Weierstrass
curve.

*Kernel finiteness.* Fix `P₀ ∉ ker φ`. Translation by `k ∈ ker φ` does not move
`φ P₀`, so `x (P₀ + k)` is a root of `A - C (x (φ P₀)) · B`. If that polynomial
vanishes identically then `A / B` is constant and `eq_zero_of_constX` gives `φ = 0`;
otherwise its root set is finite, and `k ↦ P₀ + k` is injective into
`{0} ∪ {P ≠ 0 : x P ∈ roots}`, which is finite by `finite_veluPointX_preimage`.

*Surjectivity.* Cancel `g = gcd A B` to get a **coprime** pair `(A₀, B₀)`, which is
nonconstant (else `eq_zero_of_constX` again). Then for each `s` the polynomial
`A₀ - C s · B₀` is nonzero; it has degree `0` for at most one `s` (a difference of
two such is `C (s' - s) · B₀`), and by coprimality every root `t` of it has
`B₀(t) ≠ 0`, so `s = A₀(t) / B₀(t)` is DETERMINED by `t` — distinct `s` therefore
have disjoint root sets. Away from the finite bad locus `Z` (zeros of `g`, plus the
`x`-coordinates of the finite kernel) a root `t` lifts to a point `P` with
`φ P ≠ 0` and `x (φ P) = s`, via `exists_point_veluPointX_eq`. Hence the unattained
`s` inject into `Z` through `t ↦ A₀(t) / B₀(t)` and form a finite set; pulling back
along `x` (fibres of size ≤ 2) makes the complement of the image finite. Finally the
image is infinite — else `eq_zero_of_finite_range` — while for `Q₀` outside it the
coset `Q₀ + im φ` is an infinite subset of that finite complement. Contradiction.

Relation to the other geometric leaves of this file: this statement SUBSUMES
`nsmul_surjective`, and the `n`-torsion half of `finite_nsmulKer`, as soon as
`mulByHom W n` is known to be rational (division polynomials). Consolidating them is
a cut-level decision, not one to make here — and note the dependency runs the other
way in the present proof, which CONSUMES `nsmul_surjective`, so the two are not
interchangeable as written. -/
theorem IsRationalMap.isIsogeny [IsAlgClosed F] [W.IsElliptic] {φ : W.Point →+ W'.Point}
    (h : IsRationalMap φ) : IsIsogeny φ :=
  ⟨h, fun hne => IsRationalMap.surjective h hne, fun hne => IsRationalMap.finite_ker h hne⟩

/-- The pointwise sum of two isogenies over an **algebraically closed** field is an
isogeny — this is the statement that `Hom(W, W')` is a group under addition in the
category of curves.

`[IsAlgClosed F]` is NOT removable: see the FALSITY AUDIT above, where dropping it
makes the statement false already for `φ = ψ = id` over `𝔽₅`. -/
theorem IsIsogeny.add [IsAlgClosed F] [W.IsElliptic] {φ ψ : W.Point →+ W'.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ) :=
  (hφ.isRationalMap.add hψ.isRationalMap).isIsogeny

/-- The composite of two isogenies is an isogeny. -/
theorem IsIsogeny.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (ψ.comp φ) where
  isRationalMap := hφ.isRationalMap.comp hψ.isRationalMap
  surjective hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    exact (hψ.surjective hψ0).comp (hφ.surjective hφ0)
  finite_ker hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    -- `ker (ψ ∘ φ)` is contained in the union, over the finite set `ker ψ`, of the
    -- fibres of `φ`; each nonempty fibre of `φ` is a coset of the finite `ker φ`.
    have hfib : ∀ Q : W'.Point, {P : W.Point | φ P = Q}.Finite := by
      intro Q
      by_cases hQ : ∃ P₀ : W.Point, φ P₀ = Q
      · obtain ⟨P₀, hP₀⟩ := hQ
        have hcoset : {P : W.Point | φ P = Q}
            = (fun k : W.Point => P₀ + k) '' (AddMonoidHom.ker φ : Set W.Point) := by
          ext P
          simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, AddMonoidHom.mem_ker]
          constructor
          · intro hp
            exact ⟨P - P₀, by rw [map_sub, hp, hP₀, sub_self], by abel⟩
          · rintro ⟨k, hk, rfl⟩
            rw [map_add, hk, add_zero, hP₀]
        rw [hcoset]
        exact Set.Finite.image _ (hφ.finite_ker hφ0)
      · simp only [not_exists] at hQ
        have hempty : {P : W.Point | φ P = Q} = ∅ := by
          ext P; simpa using hQ P
        rw [hempty]; exact Set.finite_empty
    have hsub : (AddMonoidHom.ker (ψ.comp φ) : Set W.Point) ⊆
        ⋃ Q ∈ (AddMonoidHom.ker ψ : Set W'.Point), {P : W.Point | φ P = Q} := by
      intro P hP
      have hQ : φ P ∈ (AddMonoidHom.ker ψ : Set W'.Point) := by
        have := (AddMonoidHom.mem_ker (f := ψ.comp φ)).1 hP
        simpa [SetLike.mem_coe, AddMonoidHom.mem_ker] using this
      exact Set.mem_biUnion hQ rfl
    exact Set.Finite.subset
      (Set.Finite.biUnion (hψ.finite_ker hψ0) (fun Q _ => hfib Q)) hsub

/-- The type of isogenies `W → W'`.

A one-field-plus-proof structure, so that two isogenies are equal precisely when
their maps on points are — which is what makes `End W` a ring. -/
structure Isogeny (W W' : Affine F) where
  /-- The underlying homomorphism of point groups. -/
  toHom : W.Point →+ W'.Point
  /-- The proof that it is an isogeny. -/
  isIsogeny : IsIsogeny toHom

namespace Isogeny

instance : CoeFun (Isogeny W W') (fun _ => W.Point → W'.Point) := ⟨fun φ => φ.toHom⟩

@[ext] theorem ext {φ ψ : Isogeny W W'} (h : ∀ P, φ.toHom P = ψ.toHom P) : φ = ψ := by
  cases φ; cases ψ; simp only [Isogeny.mk.injEq]; exact AddMonoidHom.ext h

/-- The zero isogeny. -/
def zero : Isogeny W W' := ⟨0, IsIsogeny.zero⟩

/-- The identity isogeny. -/
def id (W : Affine F) : Isogeny W W := ⟨AddMonoidHom.id W.Point, IsIsogeny.id⟩

/-- Composition of isogenies. -/
def comp (ψ : Isogeny W' W'') (φ : Isogeny W W') : Isogeny W W'' :=
  ⟨ψ.toHom.comp φ.toHom, IsIsogeny.comp φ.isIsogeny ψ.isIsogeny⟩

@[simp] theorem comp_toHom (ψ : Isogeny W' W'') (φ : Isogeny W W') :
    (ψ.comp φ).toHom = ψ.toHom.comp φ.toHom := rfl

@[simp] theorem comp_apply (ψ : Isogeny W' W'') (φ : Isogeny W W') (P : W.Point) :
    (ψ.comp φ).toHom P = ψ.toHom (φ.toHom P) := rfl

section Degree

open scoped Classical

/-- The **degree** of an isogeny: the cardinality of its kernel, and `0` for the
zero map.

In characteristic zero every isogeny is separable, so this is the classical
degree; see the module docstring for why it is defined this way rather than read
off the presenting polynomials. -/
noncomputable def degree (φ : Isogeny W W') : ℕ :=
  if φ.toHom = 0 then 0 else Nat.card (AddMonoidHom.ker φ.toHom)

theorem degree_of_ne_zero {φ : Isogeny W W'} (h : φ.toHom ≠ 0) :
    φ.degree = Nat.card (AddMonoidHom.ker φ.toHom) := by
  rw [degree, if_neg h]

theorem degree_of_eq_zero {φ : Isogeny W W'} (h : φ.toHom = 0) : φ.degree = 0 := by
  rw [degree, if_pos h]

end Degree

@[simp] theorem degree_zero : (zero : Isogeny W W').degree = 0 := degree_of_eq_zero rfl

/-- An isogeny has degree `0` exactly when it is the zero map. -/
theorem degree_eq_zero_iff (φ : Isogeny W W') : φ.degree = 0 ↔ φ.toHom = 0 := by
  refine ⟨fun h => by_contra fun hne => ?_, degree_of_eq_zero⟩
  rw [degree_of_ne_zero hne] at h
  haveI : Finite (AddMonoidHom.ker φ.toHom) :=
    Set.Finite.to_subtype (φ.isIsogeny.finite_ker hne)
  haveI : Nonempty (AddMonoidHom.ker φ.toHom) := ⟨0⟩
  exact absurd h Nat.card_pos.ne'

theorem degree_pos {φ : Isogeny W W'} (h : φ.toHom ≠ 0) : 0 < φ.degree :=
  Nat.pos_of_ne_zero fun hc => h ((degree_eq_zero_iff φ).1 hc)

/-- The identity has degree `1`.

The hypothesis is not removable: if `W` had only the point at infinity then the
identity *would be* the zero map, of degree `0`. Over an algebraically closed
field it is of course always satisfied. -/
theorem degree_id (h : ∃ P : W.Point, P ≠ 0) : (Isogeny.id W).degree = 1 := by
  obtain ⟨P, hP⟩ := h
  have hne : (Isogeny.id W).toHom ≠ 0 := by
    intro hc
    have hPc := congrArg (fun f : W.Point →+ W.Point => f P) hc
    simp only [Isogeny.id, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at hPc
    exact hP hPc
  rw [degree_of_ne_zero hne]
  have hker : AddMonoidHom.ker (Isogeny.id W).toHom = ⊥ := by
    ext Q; simp [Isogeny.id]
  rw [hker]
  simp

/-- Every element of the kernel of an isogeny is killed by its degree. Lagrange's
theorem in the kernel; it is what lets `[deg φ]` factor through `φ` in the
construction of the dual. -/
theorem degree_nsmul_eq_zero {φ : Isogeny W W'} {k : W.Point}
    (hk : k ∈ AddMonoidHom.ker φ.toHom) (h0 : φ.toHom ≠ 0) : φ.degree • k = 0 := by
  have h : Nat.card (AddMonoidHom.ker φ.toHom) • (⟨k, hk⟩ : AddMonoidHom.ker φ.toHom) = 0 :=
    card_nsmul_eq_zero'
  rw [degree_of_ne_zero h0]
  simpa using congrArg (Subtype.val) h

end Isogeny

/-! ### The endomorphism ring -/

/-- The endomorphisms of `W` that are isogenies form a subring of the endomorphism
ring of the abstract point group.

The `Ring` structure is inherited, and it is the *right* one: multiplication is
composition and, crucially, `((n : ℤ) : End W)` is multiplication by `n` on points
**definitionally** (`End.intCast_apply` below is `rfl`). So `ψ * ψ = -125` in
`End W` says exactly `ψ (ψ P) = -125 • P` for all `P`, with `ψ` an honest
morphism.

`[IsAlgClosed F]` is inherited from `IsIsogeny.add`, which is FALSE without it —
see the FALSITY AUDIT above. Over a general field the isogenies among the
endomorphisms of `W.Point` are **not** closed under addition, so there is no such
subring; `[2] = id + id` on `W₅(𝔽₅)` is an explicit failure of `add_mem'`. -/
def endSubring [IsAlgClosed F] (W : Affine F) [W.IsElliptic] :
    Subring (AddMonoid.End W.Point) where
  carrier := {f | IsIsogeny (f : W.Point →+ W.Point)}
  zero_mem' := IsIsogeny.zero
  one_mem' := IsIsogeny.id
  add_mem' hf hg := IsIsogeny.add hf hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := IsIsogeny.comp hg hf

/-- `End W`, the endomorphism ring of `W`. -/
abbrev End [IsAlgClosed F] (W : Affine F) [W.IsElliptic] : Type _ := ↥(endSubring W)

/-- **The soundness lemma of this file.** In `End W` the integer `n` acts as
multiplication by `n` on points — definitionally. Together with `IsRationalMap`
inside `IsIsogeny`, this is what makes `ψ * ψ = (-125 : End W)` a statement about
complex multiplication rather than about `M₂(Ẑ)`. -/
@[simp] theorem End.intCast_apply [IsAlgClosed F] [W.IsElliptic] (n : ℤ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.natCast_apply [IsAlgClosed F] [W.IsElliptic] (n : ℕ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.mul_apply [IsAlgClosed F] [W.IsElliptic] (f g : End W) (P : W.Point) :
    ((f * g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) ((g : AddMonoid.End W.Point) P) := rfl

/-- **The consumer-facing form of the Atkin–Lehner condition.** `ψ * ψ = (n : End W)`
in the endomorphism ring says exactly that `ψ` applied twice is multiplication by
`n` on points.

This is the lemma the `X_0(N)` descent leaves use: `ψ * ψ = (-125 : End W)` unfolds
to `ψ (ψ P) = -125 • P` for every `P`, with `ψ` carrying its `IsIsogeny` witness —
so the condition is about an actual morphism, not about `M₂(Ẑ)`. -/
theorem End.sq_eq_intCast_iff [IsAlgClosed F] [W.IsElliptic] (ψ : End W) (n : ℤ) :
    ψ * ψ = (n : End W) ↔ ∀ P : W.Point,
      (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) = n • P := by
  constructor
  · intro h P
    have hc := congrArg (fun f : End W => (f : AddMonoid.End W.Point) P) h
    simpa using hc
  · intro h
    refine Subtype.ext (AddMonoidHom.ext fun P => ?_)
    exact h P

/-- Every element of `End W` is an isogeny, so the endomorphism ring maps into the
type of isogenies. -/
def End.toIsogeny [IsAlgClosed F] [W.IsElliptic] (f : End W) : Isogeny W W :=
  ⟨(f : AddMonoid.End W.Point), f.2⟩

@[simp] theorem End.toIsogeny_toHom [IsAlgClosed F] [W.IsElliptic] (f : End W) :
    (End.toIsogeny f).toHom = (f : AddMonoid.End W.Point) := rfl

/-! ### Descent of a rational map along a rational surjection

**The cut of `Isogeny.isRationalMap_dualHom`, 2026-07-27.** The dual is *defined*
as the descent of `[deg φ]` along `φ` (`dualHom`, `dualHom_comp`), so the leaf
"the dual is rational" is literally an instance of

> if `π` is a rational surjection, `ψ` is rational, and `ψ` factors through `π` as
> a homomorphism, then the factored map is rational

with `π := φ` and `ψ := [deg φ]`. That is `IsRationalMap.descend` below, and it is
**PROVEN** here; `[deg φ]` is rational by `isRationalMap_mulByHom`, also proven
here. What remains open is a single statement of ONE-VARIABLE POLYNOMIAL ALGEBRA
with no curve, no `Isogeny`, no `End` and no group in it —
`exists_homogSubst_of_fibreInvariant` — so an `#print axioms` certificate on it is
meaningful (recall `End.coe_add_apply`, a literal `rfl`, reports `sorryAx`, so
anything phrased through `End` cannot be audited).

**Why the cut is faithful, and where `[CharZero F]` sits.** `descend` is FALSE in
characteristic `2` for exactly the reason `isRationalMap_dualHom` is: take
`π := ` Frobenius on `y² + y = x³` over `𝔽̄₂` (rational, surjective, injective),
`ψ := id`, `χ := ` inverse Frobenius. Every hypothesis of `descend` holds and the
conclusion is refuted by `Isogeny.NotIsRationalMapDualHom.isRationalMap_dualHom_is_false`.
So the characteristic hypothesis is not inherited decoration: it is consumed twice
below, in `eq_zero_of_constY` (which divides by `2`) and in the algebraic leaf
(whose proof divides by the degree of the covering).

**How the proof runs**, so that the leaf can be judged in isolation. Write
`s = x(P)`, `u = x(π P)`, and let `(Ap, Bp, Cp, Dp, Ep)`, `(A₁, B₁, C₁, D₁, E₁)` be
certificates for `π` and `ψ`.

* *The `x`-half.* `x(χ Q)` is `A₁/B₁` at any `P` above `Q`, and `x(Q)` is `Ap/Bp`
  there, so what has to be produced is a rational function of `Ap/Bp` equal to
  `A₁/B₁`. The hypothesis that makes that possible is FIBRE INVARIANCE: two points
  `P`, `P'` with `Ap/Bp` equal have `π P = ±π P'` (`eq_or_eq_neg_of_veluPointX_eq`),
  hence `ψ P = ±ψ P'`, hence the same `A₁/B₁`. That is `hinv1`, and the leaf turns
  it into polynomials.
* *The `y`-half* needs no second descent principle, only the same leaf applied
  once more, because of the identity `yCert_antiInvariant`:
  `(2y(φP) + a₁' x(φP) + a₃')·E(s) = C(s)·(2y(P) + a₁ s + a₃)`. It says the
  `±`-anti-invariant coordinate is multiplied by the SCALAR `C(s)/E(s)`, with no
  additive term — which is what removes the classical "and the constant term
  matches" obligation. Descending `C₁·Ep / (E₁·Cp)` then gives the `y`-witness
  outright. `Cp ≠ 0` is needed for that denominator and is supplied by
  `eq_zero_of_constY`.
* *Generic to everywhere.* Both halves are only available off a finite set of
  `x`-values (zeros of the certificates, the two kernels, and the `2`-torsion).
  `IsRationalMap.of_cofinite` closes that gap by multiplying every witness by
  `∏ (X - c)` over the bad set: at a bad point both sides of both clauses become
  `0`, and `B ≠ 0`, `E ≠ 0` survive. -/

/-- **PROVEN.** Multiplication by `n` is a rational map, for every `n`.

Induction on `n` off `IsRationalMap.add` and `IsRationalMap.id`; nothing else is
involved. This is what supplies the `ψ` of `IsRationalMap.descend` at the dual. -/
theorem isRationalMap_mulByHom [IsAlgClosed F] [W.IsElliptic] (n : ℕ) :
    IsRationalMap (mulByHom W n) := by
  induction n with
  | zero =>
    have h : mulByHom W 0 = 0 := by ext P; simp
    rw [h]; exact IsRationalMap.zero
  | succ n ih =>
    have h : mulByHom W (n + 1) = mulByHom W n + AddMonoidHom.id W.Point := by
      ext P; simp [succ_nsmul]
    rw [h]
    exact IsRationalMap.add ih IsRationalMap.id

/-- **PROVEN.** A certificate valid away from a FINITE set of `x`-coordinates is
already a certificate: multiply all five witnesses by `G = ∏ (X - c)` over the bad
set. At a bad `Q` the `x`-clause reads `x(χ Q) · 0 = 0` and the `y`-clause reads
`y(χ Q) · 0 = 0 · y Q + 0`, both true; away from it the clauses are the given ones
scaled by `G.eval (x Q)`. The two side conditions survive because `G ≠ 0`.

This is what lets a descent argument work with generic points and still deliver
`IsRationalMap`, whose clauses are quantified over EVERY point outside the
kernel. -/
theorem IsRationalMap.of_cofinite {χ : W'.Point →+ W''.Point} {T : Set F} (hT : T.Finite)
    (h : ∃ A B C D E : F[X], B ≠ 0 ∧ E ≠ 0 ∧
      ∀ Q : W'.Point, χ Q ≠ 0 → veluPointX Q ∉ T →
        veluPointX (χ Q) * B.eval (veluPointX Q) = A.eval (veluPointX Q) ∧
        veluPointY (χ Q) * E.eval (veluPointX Q)
          = C.eval (veluPointX Q) * veluPointY Q + D.eval (veluPointX Q)) :
    IsRationalMap χ := by
  classical
  obtain ⟨A, B, Cy, D, E, hB, hE, hcert⟩ := h
  set G : F[X] := ∏ t ∈ hT.toFinset, (Polynomial.X - Polynomial.C t) with hGdef
  have hGne : G ≠ 0 := by
    rw [hGdef]
    exact Finset.prod_ne_zero_iff.2 fun t _ => Polynomial.X_sub_C_ne_zero t
  have hGzero : ∀ u : F, u ∈ T → G.eval u = 0 := by
    intro u hu
    rw [hGdef, Polynomial.eval_prod]
    refine Finset.prod_eq_zero ((Set.Finite.mem_toFinset hT).2 hu) ?_
    simp
  refine ⟨A * G, B * G, Cy * G, D * G, E * G, mul_ne_zero hB hGne, mul_ne_zero hE hGne,
    fun Q hQ => ?_⟩
  by_cases hmem : veluPointX Q ∈ T
  · have h0 : G.eval (veluPointX Q) = 0 := hGzero _ hmem
    simp [Polynomial.eval_mul, h0]
  · obtain ⟨hx, hy⟩ := hcert Q hQ hmem
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul]
      linear_combination G.eval (veluPointX Q) * hx
    · simp only [Polynomial.eval_mul]
      linear_combination G.eval (veluPointX Q) * hy

/-- **PROVEN: the `y`-certificate of a rational map is a SCALAR on the
anti-invariant coordinate.**

Writing `Y(P) = 2 y(P) + a₁ x(P) + a₃` — the coordinate that changes sign under
`P ↦ -P` — a `y`-certificate `(C, D, E)` satisfies `Y(φ P) · E(x P) = C(x P) · Y(P)`
with **no additive term**: the `D` cancels between `P` and `-P`.

This is the observation that makes the `y`-half of `IsRationalMap.descend` cost one
more application of the SAME algebraic leaf rather than a separate argument. In the
classical treatment one descends the ratio `Y(χ Q)/Y(Q)` and then has to check that
the constant terms match; here the constant term is not there to begin with. -/
theorem yCert_antiInvariant {φ : W.Point →+ W'.Point} {Cp Dp Ep : F[X]}
    (hcert : ∀ P : W.Point, φ P ≠ 0 →
      veluPointY (φ P) * Ep.eval (veluPointX P)
        = Cp.eval (veluPointX P) * veluPointY P + Dp.eval (veluPointX P))
    {P : W.Point} (hP : P ≠ 0) (hφP : φ P ≠ 0) :
    (2 * veluPointY (φ P) + W'.a₁ * veluPointX (φ P) + W'.a₃) * Ep.eval (veluPointX P)
      = Cp.eval (veluPointX P) * (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) := by
  have h1 := hcert P hφP
  have hnegφ : φ (-P) ≠ 0 := by rw [map_neg]; exact neg_ne_zero.2 hφP
  have h2 := hcert (-P) hnegφ
  rw [velu_pointX_neg, velu_pointY_neg P hP, map_neg, velu_pointY_neg (φ P) hφP] at h2
  linear_combination h1 - h2

/-- **PROVEN.** If the `y`-coordinate of the image is a function of `x P` ALONE —
i.e. the certificate has `C = 0` — then the map is zero.

Comparing the certificate at `P` and at `-P` gives `Y(φ P) = 0`, i.e.
`φ P = -φ P`, i.e. `φ (2 • P) = 0`, at every `P` off the zeros of `E`. So
`φ ∘ [2]` has FINITE range, hence is `0` by `eq_zero_of_finite_range`, hence `φ = 0`
by `2`-divisibility (`nsmul_surjective`).

`[CharZero F]` is used to divide by `2`, and it is genuinely needed: in
characteristic `2` the Frobenius of `NotIsRationalMapDualHom` has
`C = 1`, but the *cuspidal* pathology of `NotIsRationalMapAdd` shows what goes
wrong once `W.Point` stops being divisible.

Used by `IsRationalMap.descend` to get `Cp ≠ 0`, which is the denominator of the
ratio whose descent produces the `y`-witness. -/
theorem eq_zero_of_constY [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    {φ : W.Point →+ W'.Point} {D E : F[X]} (hE : E ≠ 0)
    (hy : ∀ P : W.Point, φ P ≠ 0 →
      veluPointY (φ P) * E.eval (veluPointX P) = D.eval (veluPointX P)) :
    φ = 0 := by
  classical
  have hstep : ∀ P : W.Point, E.eval (veluPointX P) ≠ 0 → φ ((2 : ℕ) • P) = 0 := by
    intro P hEP
    by_cases hP : φ P = 0
    · rw [two_nsmul, map_add, hP, add_zero]
    have hnegφ : φ (-P) ≠ 0 := by rw [map_neg]; exact neg_ne_zero.2 hP
    have h1 := hy P hP
    have h2 := hy (-P) hnegφ
    rw [velu_pointX_neg, map_neg, velu_pointY_neg (φ P) hP] at h2
    have hb : 2 * veluPointY (φ P) + W'.a₁ * veluPointX (φ P) + W'.a₃ = 0 := by
      have hmul : (2 * veluPointY (φ P) + W'.a₁ * veluPointX (φ P) + W'.a₃)
          * E.eval (veluPointX P) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.1 hmul with h | h
      · exact h
      · exact absurd h hEP
    have hself : φ P = -(φ P) := by
      refine eq_of_veluPoint_eq hP (neg_ne_zero.2 hP) (velu_pointX_neg _).symm ?_
      rw [velu_pointY_neg (φ P) hP]
      linear_combination hb
    rw [two_nsmul, map_add]
    nth_rewrite 2 [hself]
    exact add_neg_cancel _
  have hbad : {P : W.Point | E.eval (veluPointX P) = 0}.Finite := by
    refine Set.Finite.subset (Set.Finite.insert (0 : W.Point)
      (finite_veluPointX_preimage (W := W) (Polynomial.finite_setOf_isRoot hE))) ?_
    intro P hP
    by_cases h0 : P = 0
    · exact Set.mem_insert_iff.2 (Or.inl h0)
    · exact Set.mem_insert_iff.2 (Or.inr ⟨h0, hP⟩)
  have hrange : (Set.range (φ.comp (mulByHom W 2))).Finite := by
    refine Set.Finite.subset (Set.Finite.insert (0 : W'.Point)
      (hbad.image (fun P => φ ((2 : ℕ) • P)))) ?_
    rintro _ ⟨P, rfl⟩
    refine Set.mem_insert_iff.2 ?_
    by_cases hEP : E.eval (veluPointX P) = 0
    · exact Or.inr ⟨P, hEP, rfl⟩
    · exact Or.inl (hstep P hEP)
  have hz := eq_zero_of_finite_range (W := W) hrange
  refine AddMonoidHom.ext fun Q => ?_
  obtain ⟨P, hP⟩ := nsmul_surjective (W := W) (n := 2) (by norm_num) Q
  have hzP := congrArg (fun f : W.Point →+ W'.Point => f P) hz
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, mulByHom_apply,
    AddMonoidHom.zero_apply] at hzP
  simp only [AddMonoidHom.zero_apply]
  rw [← hP]
  exact hzP

/-! #### The fibre-invariance descent: a function constant on the fibres of `A/B`

The last input of `Isogeny.isRationalMap_dualHom`, and pure `F[X]` algebra. See the
docstring of `exists_homogSubst_of_fibreInvariant` below for the whole argument; the
declarations here are its three ingredients — the two-variable resultant
`Res_T (A − c·B, A₁ − w·B₁)` viewed in `(F[c])[w]`, the coefficient extraction that reads
the common fibre value off its top two `w`-coefficients, and the degenerate and coprime
branches of the induction on `gcd A B`. -/

/-- The embedding `F ↪ (F[c])[w]` of constants. -/
noncomputable def fibreC (F : Type*) [Field F] : F →+* (F[X])[X] :=
  (Polynomial.C : F[X] →+* (F[X])[X]).comp (Polynomial.C : F →+* F[X])

/-- Specialisation `c ↦ γ`, `w ↦ ω`. -/
noncomputable def fibreEval (γ ω : F) : (F[X])[X] →+* F :=
  (Polynomial.evalRingHom ω).comp (Polynomial.mapRingHom (Polynomial.evalRingHom γ))

omit [DecidableEq F] in
theorem fibreEval_comp_fibreC (γ ω : F) :
    (fibreEval γ ω).comp (fibreC F) = RingHom.id F :=
  RingHom.ext fun a => by simp [fibreEval, fibreC]

omit [DecidableEq F] in
theorem fibreEval_apply (γ ω : F) (p : (F[X])[X]) :
    fibreEval γ ω p = (p.map (Polynomial.evalRingHom γ)).eval ω := rfl

/-- `Res_T (A - c·B, A₁ - w·B₁)`, an element of `(F[c])[w]`. -/
noncomputable def fibreRes (A B A₁ B₁ : F[X]) (d d₁ : ℕ) : (F[X])[X] :=
  Polynomial.resultant
    (A.map (fibreC F) -
      Polynomial.C (Polynomial.C (Polynomial.X : F[X])) * B.map (fibreC F))
    (A₁.map (fibreC F) - Polynomial.C (Polynomial.X : (F[X])[X]) * B₁.map (fibreC F))
    d d₁

omit [DecidableEq F] in
theorem fibreEval_fibreRes (A B A₁ B₁ : F[X]) (d d₁ : ℕ) (γ ω : F) :
    fibreEval γ ω (fibreRes A B A₁ B₁ d d₁)
      = Polynomial.resultant (A - Polynomial.C γ * B) (A₁ - Polynomial.C ω * B₁) d d₁ := by
  have hmap : ∀ P : F[X], (P.map (fibreC F)).map (fibreEval γ ω) = P := by
    intro P
    rw [Polynomial.map_map, fibreEval_comp_fibreC, Polynomial.map_id]
  rw [fibreRes, ← Polynomial.resultant_map_map (φ := fibreEval γ ω)]
  congr 1
  · rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, hmap, hmap]
    congr 2
    simp [fibreEval]
  · rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, hmap, hmap]
    congr 2
    simp [fibreEval]

omit [DecidableEq F] in
theorem fibreEval_fibreRes_eq [IsAlgClosed F] {A B A₁ B₁ : F[X]} {d d₁ : ℕ}
    (hA₁ : A₁.natDegree ≤ d₁) (hB₁ : B₁.natDegree ≤ d₁) {γ : F}
    (hdeg : (A - Polynomial.C γ * B).natDegree = d) {v : F}
    (hv : ∀ t : F, (A - Polynomial.C γ * B).eval t = 0 → A₁.eval t = v * B₁.eval t) (ω : F) :
    fibreEval γ ω (fibreRes A B A₁ B₁ d d₁)
      = ((A - Polynomial.C γ * B).leadingCoeff ^ d₁
          * ((A - Polynomial.C γ * B).roots.map B₁.eval).prod) * (v - ω) ^ d := by
  classical
  have hsp : (A - Polynomial.C γ * B).Splits := IsAlgClosed.splits _
  have hgle : (A₁ - Polynomial.C ω * B₁).natDegree ≤ d₁ :=
    le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le hA₁ (le_trans (Polynomial.natDegree_C_mul_le _ _) hB₁))
  have key := Polynomial.resultant_eq_prod_eval (A - Polynomial.C γ * B)
    (A₁ - Polynomial.C ω * B₁) d₁ hgle hsp
  rw [hdeg] at key
  have hmap : (A - Polynomial.C γ * B).roots.map (A₁ - Polynomial.C ω * B₁).eval
      = (A - Polynomial.C γ * B).roots.map (fun t => B₁.eval t * (v - ω)) := by
    refine Multiset.map_congr rfl fun t ht => ?_
    have hr : (A - Polynomial.C γ * B).eval t = 0 := (Polynomial.mem_roots'.1 ht).2
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hv t hr]; ring
  have hcard : ((A - Polynomial.C γ * B).roots.map (fun _ : F => v - ω)).prod = (v - ω) ^ d := by
    rw [Multiset.map_const', Multiset.prod_replicate, ← hsp.natDegree_eq_card_roots, hdeg]
  rw [fibreEval_fibreRes, key, hmap, Multiset.prod_map_mul, hcard, mul_assoc]

/-- If a polynomial evaluates like `K·(v − ω)^d` everywhere, its top two coefficients
pin down `v`. -/
theorem coeff_of_eval_eq_pow {F : Type*} [Field F] [Infinite F] {P : F[X]} {K v : F} {d : ℕ}
    (hK : K ≠ 0) (hd : d ≠ 0) (hP : ∀ ω : F, P.eval ω = K * (v - ω) ^ d) :
    P.coeff d ≠ 0 ∧ P.coeff (d - 1) = -((d : F) * v) * P.coeff d := by
  have hstruct : P = Polynomial.C (K * (-1) ^ d) * (Polynomial.X - Polynomial.C v) ^ d := by
    refine Polynomial.funext fun ω => ?_
    rw [hP ω]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [mul_assoc, ← mul_pow]
    congr 2
    ring
  have hMm : ((Polynomial.X - Polynomial.C v : F[X]) ^ d).Monic :=
    (Polynomial.monic_X_sub_C v).pow d
  have hMdeg : ((Polynomial.X - Polynomial.C v : F[X]) ^ d).natDegree = d := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hKne : K * (-1 : F) ^ d ≠ 0 := mul_ne_zero hK (pow_ne_zero _ (by norm_num))
  have hPdeg : P.natDegree = d := by
    rw [hstruct, Polynomial.natDegree_C_mul hKne, hMdeg]
  have hMcoeff : ((Polynomial.X - Polynomial.C v : F[X]) ^ d).coeff d = 1 := by
    have h := hMm.coeff_natDegree
    rwa [hMdeg] at h
  have hcd : P.coeff d = K * (-1 : F) ^ d := by
    rw [hstruct, Polynomial.coeff_C_mul, hMcoeff, mul_one]
  have hnextM : ((Polynomial.X - Polynomial.C v : F[X]) ^ d).nextCoeff = -((d : F) * v) := by
    rw [(Polynomial.monic_X_sub_C v).nextCoeff_pow d, Polynomial.nextCoeff_X_sub_C,
      nsmul_eq_mul]
    ring
  have hnext : P.nextCoeff = (K * (-1 : F) ^ d) * -((d : F) * v) := by
    rw [hstruct, Polynomial.nextCoeff_C_mul, hnextM]
  have hnext' : P.nextCoeff = P.coeff (d - 1) := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by omega : 0 < P.natDegree), hPdeg]
  refine ⟨by rw [hcd]; exact hKne, ?_⟩
  rw [← hnext', hnext, hcd]; ring

/-! ### The degenerate branch: `A₁/B₁` constant off a finite set -/

omit [DecidableEq F] in
theorem exists_homogSubst_of_fibreConst [CharZero F]
    {A B A₁ B₁ : F[X]} (hB₁ : B₁ ≠ 0) {S : Set F} (hS : S.Finite)
    (hinv : ∀ s t : F, s ∉ S → t ∉ S →
      A₁.eval s * B₁.eval t = A₁.eval t * B₁.eval s) :
    ∃ (A' B' : F[X]) (d : ℕ), B' ≠ 0 ∧ A'.natDegree ≤ d ∧ B'.natDegree ≤ d ∧
      A₁ * homogSubst A B d B' = B₁ * homogSubst A B d A' := by
  classical
  obtain ⟨t₀, ht₀S, ht₀B⟩ : ∃ t₀ : F, t₀ ∉ S ∧ B₁.eval t₀ ≠ 0 := by
    have hfin : (S ∪ {t : F | B₁.eval t = 0}).Finite :=
      hS.union (Polynomial.finite_setOf_isRoot hB₁)
    obtain ⟨t₀, ht₀⟩ := hfin.infinite_compl.nonempty
    exact ⟨t₀, fun h => ht₀ (Or.inl h), fun h => ht₀ (Or.inr h)⟩
  have hkey : A₁ * Polynomial.C (B₁.eval t₀) = B₁ * Polynomial.C (A₁.eval t₀) := by
    refine sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    refine hS.infinite_compl.mono fun s hs => ?_
    have h := hinv s t₀ hs ht₀S
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination h
  have hA₁ : A₁ = B₁ * Polynomial.C (A₁.eval t₀ / B₁.eval t₀) := by
    calc A₁ = A₁ * Polynomial.C (B₁.eval t₀) * Polynomial.C (B₁.eval t₀)⁻¹ := by
              rw [mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ ht₀B,
                Polynomial.C_1, mul_one]
      _ = B₁ * Polynomial.C (A₁.eval t₀) * Polynomial.C (B₁.eval t₀)⁻¹ := by rw [hkey]
      _ = B₁ * Polynomial.C (A₁.eval t₀ / B₁.eval t₀) := by
              rw [mul_assoc, ← Polynomial.C_mul, div_eq_mul_inv]
  refine ⟨Polynomial.C (A₁.eval t₀ / B₁.eval t₀), 1, 0, one_ne_zero, by simp, by simp, ?_⟩
  have h1 : homogSubst A B 0 (1 : F[X]) = 1 := by simp [homogSubst]
  have h2 : homogSubst A B 0 (Polynomial.C (A₁.eval t₀ / B₁.eval t₀))
      = Polynomial.C (A₁.eval t₀ / B₁.eval t₀) := by simp [homogSubst]
  rw [h1, h2, mul_one]
  exact hA₁

/-! ### The coprime case -/

omit [DecidableEq F] in
theorem exists_homogSubst_of_fibreInvariant_coprime [IsAlgClosed F] [CharZero F]
    {A B A₁ B₁ : F[X]} (hcop : IsCoprime A B) (hB : B ≠ 0) (hB₁ : B₁ ≠ 0)
    {S : Set F} (hS : S.Finite)
    (hinv : ∀ s t : F, s ∉ S → t ∉ S →
      A.eval s * B.eval t = A.eval t * B.eval s →
      A₁.eval s * B₁.eval t = A₁.eval t * B₁.eval s) :
    ∃ (A' B' : F[X]) (d : ℕ), B' ≠ 0 ∧ A'.natDegree ≤ d ∧ B'.natDegree ≤ d ∧
      A₁ * homogSubst A B d B' = B₁ * homogSubst A B d A' := by
  classical
  by_cases hd0 : max A.natDegree B.natDegree = 0
  · refine exists_homogSubst_of_fibreConst hB₁ hS fun s t hs ht => hinv s t hs ht ?_
    have hA : A = Polynomial.C (A.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.1 (hd0 ▸ le_max_left _ _))
    have hBc : B = Polynomial.C (B.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.1 (hd0 ▸ le_max_right _ _))
    rw [hA, hBc]; simp
  set d : ℕ := max A.natDegree B.natDegree with hdd
  set d₁ : ℕ := max A₁.natDegree B₁.natDegree with hdd₁
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hnocom : ∀ t : F, A.eval t = 0 → B.eval t = 0 → False := by
    intro t hAt hBt
    obtain ⟨u, v, huv⟩ := hcop
    have h := congrArg (Polynomial.eval t) huv
    simp [hAt, hBt] at h
  have hfne : ∀ γ : F, A - Polynomial.C γ * B ≠ 0 := by
    intro γ h
    have hAeq : A = Polynomial.C γ * B := sub_eq_zero.1 h
    have hunit : IsUnit B := by
      obtain ⟨u, v, huv⟩ := hcop
      refine isUnit_of_dvd_one ⟨u * Polynomial.C γ + v, ?_⟩
      rw [hAeq] at huv; linear_combination -huv
    have hBdeg : B.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    have hAdeg : A.natDegree = 0 := by
      rw [hAeq]
      exact Nat.le_zero.1 (le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hBdeg))
    exact hd0 (by rw [hdd, hAdeg, hBdeg]; simp)
  have hdegle : ∀ γ : F, (A - Polynomial.C γ * B).natDegree ≤ d :=
    fun γ => le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (le_max_left _ _)
        (le_trans (Polynomial.natDegree_C_mul_le _ _) (le_max_right _ _)))
  set T : Set F := S ∪ {t : F | B₁.eval t = 0} with hTdef
  have hTfin : T.Finite := hS.union (Polynomial.finite_setOf_isRoot hB₁)
  set Γbad : Set F :=
    {γ : F | (A - Polynomial.C γ * B).coeff d = 0} ∪
      {γ : F | ∃ t ∈ T, (A - Polynomial.C γ * B).eval t = 0}
    with hΓdef
  have hone : A.coeff d ≠ 0 ∨ B.coeff d ≠ 0 := by
    rcases max_choice A.natDegree B.natDegree with h | h
    · left
      have hda : d = A.natDegree := hdd.trans h
      have hA0 : A ≠ 0 := by
        intro hz
        exact hd0 (by rw [hda, hz, Polynomial.natDegree_zero])
      rw [hda]
      exact Polynomial.leadingCoeff_ne_zero.2 hA0
    · right
      have hdb : d = B.natDegree := hdd.trans h
      rw [hdb]
      exact Polynomial.leadingCoeff_ne_zero.2 hB
  have hΓ1 : {γ : F | (A - Polynomial.C γ * B).coeff d = 0}.Finite := by
    have hq : (Polynomial.C (A.coeff d) - Polynomial.C (B.coeff d) * Polynomial.X : F[X]) ≠ 0 := by
      intro hz
      rcases hone with h | h
      · exact h (by simpa using congrArg (fun p : F[X] => p.coeff 0) hz)
      · exact h (by simpa using congrArg (fun p : F[X] => p.coeff 1) hz)
    refine (Polynomial.finite_setOf_isRoot hq).subset fun γ hγ => ?_
    simp only [Set.mem_setOf_eq, Polynomial.coeff_sub, Polynomial.coeff_C_mul] at hγ
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hγ
  have hΓ2 : {γ : F | ∃ t ∈ T, (A - Polynomial.C γ * B).eval t = 0}.Finite := by
    refine (hTfin.image fun t => A.eval t / B.eval t).subset ?_
    rintro γ ⟨t, htT, ht⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at ht
    have h1 : A.eval t = γ * B.eval t := by linear_combination ht
    have h2 : B.eval t ≠ 0 := fun h => hnocom t (by rw [h1, h, mul_zero]) h
    exact ⟨t, htT, by simp only [h1]; field_simp⟩
  have hΓfin : Γbad.Finite := hΓ1.union hΓ2
  set 𝓡 : (F[X])[X] := fibreRes A B A₁ B₁ d d₁ with h𝓡
  set A' : F[X] := -(𝓡.coeff (d - 1)) with hA'def
  set B' : F[X] := Polynomial.C (d : F) * 𝓡.coeff d with hB'def
  have hdF : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd0
  have hgood : ∀ γ : F, γ ∉ Γbad → B'.eval γ ≠ 0 ∧ ∃ v : F,
      A'.eval γ = v * B'.eval γ ∧
      ∀ t : F, (A - Polynomial.C γ * B).eval t = 0 → A₁.eval t = v * B₁.eval t := by
    intro γ hγ
    have hcoeff : (A - Polynomial.C γ * B).coeff d ≠ 0 := fun h => hγ (Or.inl h)
    have hrootT : ∀ t : F, (A - Polynomial.C γ * B).eval t = 0 → t ∉ T :=
      fun t ht hmem => hγ (Or.inr ⟨t, hmem, ht⟩)
    have hdeg : (A - Polynomial.C γ * B).natDegree = d :=
      le_antisymm (hdegle γ) (Polynomial.le_natDegree_of_ne_zero hcoeff)
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : F, (A - Polynomial.C γ * B).eval t₀ = 0 :=
      (IsAlgClosed.splits (A - Polynomial.C γ * B)).exists_eval_eq_zero
        (Polynomial.degree_ne_of_natDegree_ne (by rw [hdeg]; exact hd0))
    have ht₀T := hrootT t₀ ht₀
    have hB₁t₀ : B₁.eval t₀ ≠ 0 := fun h => ht₀T (Or.inr h)
    have ht₀S : t₀ ∉ S := fun h => ht₀T (Or.inl h)
    have hvall : ∀ t : F, (A - Polynomial.C γ * B).eval t = 0 →
        A₁.eval t = (A₁.eval t₀ / B₁.eval t₀) * B₁.eval t := by
      intro t ht
      have htT := hrootT t ht
      have hB₁t : B₁.eval t ≠ 0 := fun h => htT (Or.inr h)
      have htS : t ∉ S := fun h => htT (Or.inl h)
      have e0 : A.eval t₀ = γ * B.eval t₀ := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at ht₀
        linear_combination ht₀
      have e1 : A.eval t = γ * B.eval t := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at ht
        linear_combination ht
      have h2 := hinv t₀ t ht₀S htS (by rw [e0, e1]; ring)
      field_simp
      linear_combination -h2
    have hKne : (A - Polynomial.C γ * B).leadingCoeff ^ d₁
        * ((A - Polynomial.C γ * B).roots.map B₁.eval).prod ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.2 (hfne γ))) ?_
      refine Multiset.prod_ne_zero ?_
      intro hmem
      obtain ⟨t, ht, hte⟩ := Multiset.mem_map.1 hmem
      have hr : (A - Polynomial.C γ * B).eval t = 0 := (Polynomial.mem_roots'.1 ht).2
      exact hrootT t hr (Or.inr hte)
    have hPeval : ∀ ω : F, (𝓡.map (Polynomial.evalRingHom γ)).eval ω
        = ((A - Polynomial.C γ * B).leadingCoeff ^ d₁
            * ((A - Polynomial.C γ * B).roots.map B₁.eval).prod)
          * ((A₁.eval t₀ / B₁.eval t₀) - ω) ^ d := by
      intro ω
      rw [← fibreEval_apply, h𝓡]
      exact fibreEval_fibreRes_eq (le_max_left _ _) (le_max_right _ _) hdeg hvall ω
    obtain ⟨hc1, hc2⟩ := coeff_of_eval_eq_pow hKne hd0 hPeval
    simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] at hc1 hc2
    have hB'γ : B'.eval γ = (d : F) * (𝓡.coeff d).eval γ := by
      rw [hB'def]; simp
    refine ⟨by rw [hB'γ]; exact mul_ne_zero hdF hc1, A₁.eval t₀ / B₁.eval t₀, ?_, hvall⟩
    rw [hA'def, hB'γ, Polynomial.eval_neg, hc2]
    ring
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ : F, γ ∉ Γbad := hΓfin.infinite_compl.nonempty
  have hB'ne : B' ≠ 0 := fun h => (hgood γ₀ hγ₀).1 (by rw [h]; simp)
  refine ⟨A', B', max A'.natDegree B'.natDegree, hB'ne, le_max_left _ _, le_max_right _ _, ?_⟩
  set d' : ℕ := max A'.natDegree B'.natDegree with hd'def
  have hSbadfin : (S ∪ {s : F | B.eval s = 0} ∪ {s : F | B₁.eval s = 0} ∪
      {s : F | ∃ γ ∈ Γbad, (A - Polynomial.C γ * B).eval s = 0}).Finite := by
    refine ((hS.union (Polynomial.finite_setOf_isRoot hB)).union
      (Polynomial.finite_setOf_isRoot hB₁)).union ?_
    have hrw : {s : F | ∃ γ ∈ Γbad, (A - Polynomial.C γ * B).eval s = 0}
        = ⋃ γ ∈ Γbad, {s : F | (A - Polynomial.C γ * B).eval s = 0} := by ext s; simp
    rw [hrw]
    exact hΓfin.biUnion fun γ _ => Polynomial.finite_setOf_isRoot (hfne γ)
  refine sub_eq_zero.1 (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
  refine hSbadfin.infinite_compl.mono fun s hs => ?_
  have hsS : s ∉ S := fun h => hs (Or.inl (Or.inl (Or.inl h)))
  have hBs : B.eval s ≠ 0 := fun h => hs (Or.inl (Or.inl (Or.inr h)))
  have hB₁s : B₁.eval s ≠ 0 := fun h => hs (Or.inl (Or.inr h))
  have hu : (A.eval s / B.eval s) * B.eval s = A.eval s := by field_simp
  have hroot : (A - Polynomial.C (A.eval s / B.eval s) * B).eval s = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hu
  have hγbad : (A.eval s / B.eval s) ∉ Γbad := fun h => hs (Or.inr ⟨_, h, hroot⟩)
  obtain ⟨hB'γ, v, hA'γ, hvall⟩ := hgood _ hγbad
  have hA₁s : A₁.eval s = v * B₁.eval s := hvall s hroot
  show (A₁ * homogSubst A B d' B' - B₁ * homogSubst A B d' A').eval s = 0
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_homogSubst (le_max_right _ _) hu, eval_homogSubst (le_max_left _ _) hu,
    hA₁s, hA'γ]
  ring

/-! ### The general case, by dividing out `gcd A B` -/

/-- **PROVEN (2026-07-27), and it is PURE ONE-VARIABLE ALGEBRA over `F[X]`.** No
curve, no group, no `Isogeny`, no `End`: this is the only thing
`Isogeny.isRationalMap_dualHom` rested on, and the `#print axioms` audit of it is
therefore meaningful — it returns exactly `[propext, Classical.choice, Quot.sound]`.

**What it says.** `A/B` is a rational function of degree `d = max (deg A) (deg B)`;
its generic fibre is the `d`-element root set of `A - c·B`. The hypothesis `hinv`
says the rational function `A₁/B₁` is CONSTANT ON THOSE FIBRES, away from a finite
set `S` (which in the application collects the zeros of the certificates, the two
kernels and the `2`-torsion). The conclusion says `A₁/B₁` is then a rational
function OF `A/B`. Denominators are cleared with the file's own `homogSubst`, so the
statement is a polynomial identity: `homogSubst A B d Q` is `B ^ d · Q (A / B)`, and
`eval_homogSubst` turns the identity into
`A₁(s) · B'(u) = B₁(s) · A'(u)` at every `s` with `B.eval s ≠ 0`, where
`u = A(s)/B(s)`. The degree bounds `A'.natDegree ≤ d`, `B'.natDegree ≤ d` are
exactly what `eval_homogSubst` consumes.

**The proof as carried out — one resultant, and NO divisor theory.** Three steps.

1. *Reduction to `IsCoprime A B`* (this theorem). Divide out `g = EuclideanDomain.gcd A B`;
   `homogSubst_mul_left` transports the conclusion back through `g ^ d`, and the fibre
   hypothesis transports forward just by multiplying by `g(s)·g(t)`, so `S` need not be
   enlarged. Coprimality is exactly what removes the BASE POINT of the pencil: a common
   root of `A` and `B` is a root of `A - γ·B` for *every* `γ`, and would make every
   parameter bad.

2. *The degenerate branch* (`exists_homogSubst_of_fibreConst`). If
   `max (deg A) (deg B) = 0` then `A` and `B` are constants, `hinv`'s hypothesis is
   automatic, so `A₁/B₁` is constant off `S`, and `(A', B', d) := (C e, 1, 0)` works.

3. *The main branch* (`exists_homogSubst_of_fibreInvariant_coprime`). `fibreRes A B A₁ B₁ d d₁`
   is `Res_T (A(T) − c·B(T), A₁(T) − w·B₁(T))`, formed ONCE in the two-variable ring
   `(F[c])[w]` and specialised by the ring hom `fibreEval γ ω`. Outside a finite set `Γbad`
   — the at most one `γ` that kills the leading coefficient, plus the finitely many values
   `A(t)/B(t)` for `t ∈ S ∪ B₁⁻¹(0)` — the polynomial `A − γ·B` has degree exactly `d`, and
   every one of its roots lies off `S` with `B₁ ≠ 0` there; `hinv` applied to two such roots
   gives `A₁(t) = v·B₁(t)` for ONE value `v = v(γ)`. Since `F` is algebraically closed,
   `Polynomial.resultant_eq_prod_eval` turns the specialised resultant into
   `K(γ)·(v(γ) − ω) ^ d` with `K(γ) ≠ 0`, so by `Polynomial.funext` the `w`-polynomial IS
   `C K · (C v − X) ^ d`, and its top two coefficients read `v` off:
   `coeff (d−1) = −(d·v) · coeff d` (`coeff_of_eval_eq_pow`). Hence
   `A' := −𝓡.coeff (d−1)` and `B' := C (d : F) · 𝓡.coeff d`, polynomials in `c`, satisfy
   `A'(γ) = v(γ)·B'(γ)` and `B'(γ) ≠ 0` at every good `γ`. The target identity then holds at
   every `s` outside a finite set (take `γ = A(s)/B(s)`, of which `s` is a root of `A − γ·B`),
   and an identity valid off a finite subset of an infinite field is an identity
   (`Polynomial.eq_zero_of_infinite_isRoot`).

Note that SEPARABILITY of `A − γ·B` is never needed: the roots are counted WITH
multiplicity throughout, and the factorisation `∏ (A₁(t) − ω·B₁(t)) = ∏ B₁(t) · (v − ω) ^ d`
does not care. That is what removes the discriminant/Wronskian genericity argument the
trace formulation would have required.

**Where the two type-class hypotheses are consumed.** `[CharZero F]` twice: `(d : F) ≠ 0`
is what makes `B' = C (d : F) · 𝓡.coeff d` nonzero — this is the "division by `d`" of the
trace formula — and `Infinite F` (which `CharZero` supplies) is what promotes a cofinite
identity to a polynomial identity. It is genuinely needed: in characteristic `p` an
inseparable `A/B = X ^ p` has every fibre a single point, so `hinv` is vacuous while
`A₁/B₁ = X` is not a rational function of `X ^ p`. `[IsAlgClosed F]` is what makes `hinv`,
a hypothesis about `F`-POINTS, say anything about the generic fibre: it supplies the roots
of `A − γ·B` as elements of `F` and the `Splits` hypothesis without which the resultant
does not factor. Over a small field `hinv` would be vacuous and the statement false.

**ROUTE CORRECTION, recorded because an earlier version of this docstring said the
opposite.** That version said `homogSubst` "will not help directly" and pointed at `Pic⁰`
and divisor theory. Its premise — that this is not a composition — is right; its conclusion
was wrong. What has to be produced is a rational function **of** `x ∘ φ`, not a substitution
**into** one, and `homogSubst A B d Q = B ^ d · Q (A / B)` is exactly that. **No divisor
theory appears anywhere in the proof.** -/
theorem exists_homogSubst_of_fibreInvariant [IsAlgClosed F] [CharZero F]
    {A B A₁ B₁ : F[X]} (hB : B ≠ 0) (hB₁ : B₁ ≠ 0) {S : Set F} (hS : S.Finite)
    (hinv : ∀ s t : F, s ∉ S → t ∉ S →
      A.eval s * B.eval t = A.eval t * B.eval s →
      A₁.eval s * B₁.eval t = A₁.eval t * B₁.eval s) :
    ∃ (A' B' : F[X]) (d : ℕ), B' ≠ 0 ∧ A'.natDegree ≤ d ∧ B'.natDegree ≤ d ∧
      A₁ * homogSubst A B d B' = B₁ * homogSubst A B d A' := by
  classical
  set g : F[X] := EuclideanDomain.gcd A B with hgdef
  have hgne : g ≠ 0 := fun h => hB (EuclideanDomain.gcd_eq_zero_iff.1 h).2
  set Aa : F[X] := A / g with hAadef
  set Bb : F[X] := B / g with hBbdef
  have hAeq : A = g * Aa :=
    (EuclideanDomain.mul_div_cancel' hgne (EuclideanDomain.gcd_dvd_left A B)).symm
  have hBeq : B = g * Bb :=
    (EuclideanDomain.mul_div_cancel' hgne (EuclideanDomain.gcd_dvd_right A B)).symm
  have hbez : g = A * EuclideanDomain.gcdA A B + B * EuclideanDomain.gcdB A B :=
    EuclideanDomain.gcd_eq_gcd_ab A B
  have hcop : IsCoprime Aa Bb := by
    refine ⟨EuclideanDomain.gcdA A B, EuclideanDomain.gcdB A B, mul_left_cancel₀ hgne ?_⟩
    rw [mul_one]
    calc g * (EuclideanDomain.gcdA A B * Aa + EuclideanDomain.gcdB A B * Bb)
        = (g * Aa) * EuclideanDomain.gcdA A B + (g * Bb) * EuclideanDomain.gcdB A B := by ring
      _ = A * EuclideanDomain.gcdA A B + B * EuclideanDomain.gcdB A B := by
            rw [← hAeq, ← hBeq]
      _ = g := hbez.symm
  have hBbne : Bb ≠ 0 := by
    intro h
    rw [h, mul_zero] at hBeq
    exact hB hBeq
  obtain ⟨A', B', d', hB'ne, hA'd, hB'd, hkey⟩ :=
    exists_homogSubst_of_fibreInvariant_coprime hcop hBbne hB₁ hS
      (fun s t hs ht hst => hinv s t hs ht (by
        rw [hAeq, hBeq]
        simp only [Polynomial.eval_mul]
        linear_combination (g.eval s * g.eval t) * hst))
  refine ⟨A', B', d', hB'ne, hA'd, hB'd, ?_⟩
  rw [hAeq, hBeq, homogSubst_mul_left, homogSubst_mul_left]
  linear_combination (g ^ d') * hkey


/-- **PROVEN: descent of a rational map along a rational surjection.**

If `ψ = χ ∘ π` with `π` a rational SURJECTION and `ψ` rational, then the factored
`χ` is rational. This is the general form of `Isogeny.isRationalMap_dualHom`, which
is the case `π := φ`, `ψ := [deg φ]`.

**`[CharZero F]` is load-bearing, not inherited.** In characteristic `2` take
`π := ` Frobenius on `y² + y = x³` over `𝔽̄₂` (rational, surjective and injective —
see `Isogeny.NotIsRationalMapDualHom`), `ψ := id` and `χ := π⁻¹`: every other
hypothesis holds and `isRationalMap_dualHom_is_false` refutes the conclusion.

No hypothesis is imposed on `W'` or `W''`: the proof reduces every statement about
points of `W'` to a statement about points of `W` through the surjection, so only
`W` needs `[W.IsElliptic]` (for `2`-divisibility, finiteness of `2`-torsion, and
existence of a point with prescribed `x`).

See the section docstring above for the shape of the proof; the only unproven input
is `exists_homogSubst_of_fibreInvariant`, applied twice — once to `(A₁, B₁)` for the
`x`-witness and once to `(C₁·Ep, E₁·Cp)` for the `y`-witness. -/
theorem IsRationalMap.descend [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    {π : W.Point →+ W'.Point} (hπ : IsRationalMap π) (hsurj : Function.Surjective π)
    {ψ : W.Point →+ W''.Point} (hψ : IsRationalMap ψ)
    {χ : W'.Point →+ W''.Point} (hfac : ∀ P : W.Point, χ (π P) = ψ P) :
    IsRationalMap χ := by
  classical
  by_cases hψ0 : ψ = 0
  · have hχ : χ = 0 := by
      refine AddMonoidHom.ext fun Q => ?_
      obtain ⟨P, rfl⟩ := hsurj Q
      simp [hfac P, hψ0]
    rw [hχ]; exact IsRationalMap.zero
  have hπ0 : π ≠ 0 := by
    intro h
    refine hψ0 (AddMonoidHom.ext fun P => ?_)
    rw [← hfac P, h]
    simp
  -- copies, because `obtain` consumes the hypothesis and the kernels are needed later
  have hπcopy : IsRationalMap π := hπ
  have hψcopy : IsRationalMap ψ := hψ
  obtain ⟨Ap, Bp, Cp, Dp, Ep, hBp, hEp, hcert⟩ := hπcopy
  obtain ⟨A₁, B₁, C₁, D₁, E₁, hB₁, hE₁, hcert₁⟩ := hψcopy
  have hCp : Cp ≠ 0 := by
    intro hc
    refine hπ0 (eq_zero_of_constY (D := Dp) (E := Ep) hEp fun P hP => ?_)
    have h := (hcert P hP).2
    rw [hc] at h
    simpa using h
  have hZne : Bp * Ep * B₁ * E₁ * Cp ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hBp hEp) hB₁) hE₁) hCp
  have hkerπ : {P : W.Point | π P = 0}.Finite := by
    refine (IsRationalMap.finite_ker hπ hπ0).subset fun P hP => ?_
    simpa using hP
  have hkerψ : {P : W.Point | ψ P = 0}.Finite := by
    refine (IsRationalMap.finite_ker hψ hψ0).subset fun P hP => ?_
    simpa using hP
  have htors : {P : W.Point | (2 : ℕ) • P = 0}.Finite :=
    finite_nsmulKer (W := W) (n := 2) (by norm_num)
  -- the finite set of bad `x`-coordinates, packaged so that it stays opaque below
  obtain ⟨Sbad, hSfin, hgoodP⟩ :
      ∃ Sbad : Set F, Sbad.Finite ∧ ∀ P : W.Point, P ≠ 0 → veluPointX P ∉ Sbad →
        π P ≠ 0 ∧ ψ P ≠ 0 ∧ (2 : ℕ) • P ≠ 0 ∧
        (Bp * Ep * B₁ * E₁ * Cp).eval (veluPointX P) ≠ 0 := by
    refine ⟨{t : F | (Bp * Ep * B₁ * E₁ * Cp).eval t = 0} ∪
      veluPointX '' ({P : W.Point | π P = 0} ∪ {P : W.Point | ψ P = 0} ∪
        {P : W.Point | (2 : ℕ) • P = 0}), ?_, ?_⟩
    · exact Set.Finite.union (Polynomial.finite_setOf_isRoot hZne)
        (Set.Finite.image _ (Set.Finite.union (Set.Finite.union hkerπ hkerψ) htors))
    · intro P _ hPS
      exact ⟨fun hc => hPS (Or.inr ⟨P, Or.inl (Or.inl hc), rfl⟩),
        fun hc => hPS (Or.inr ⟨P, Or.inl (Or.inr hc), rfl⟩),
        fun hc => hPS (Or.inr ⟨P, Or.inr hc, rfl⟩),
        fun hc => hPS (Or.inl hc)⟩
  -- off the `2`-torsion the anti-invariant coordinate does not vanish
  have hYne : ∀ P : W.Point, P ≠ 0 → (2 : ℕ) • P ≠ 0 →
      2 * veluPointY P + W.a₁ * veluPointX P + W.a₃ ≠ 0 := by
    intro P hP0 hP2 hc
    refine hP2 ?_
    have hself : P = -P := by
      refine eq_of_veluPoint_eq hP0 (neg_ne_zero.2 hP0) (velu_pointX_neg P).symm ?_
      rw [velu_pointY_neg P hP0]
      linear_combination hc
    rw [two_nsmul]
    nth_rewrite 2 [hself]
    exact add_neg_cancel P
  -- two points in the same fibre of `Ap/Bp` have `π`-images equal up to sign
  have hpair : ∀ P P' : W.Point, π P ≠ 0 → π P' ≠ 0 →
      Bp.eval (veluPointX P) ≠ 0 → Bp.eval (veluPointX P') ≠ 0 →
      Ap.eval (veluPointX P) * Bp.eval (veluPointX P')
        = Ap.eval (veluPointX P') * Bp.eval (veluPointX P) →
      π P = π P' ∨ π P = -(π P') := by
    intro P P' hπP hπP' hBs hBt hfib
    refine eq_or_eq_neg_of_veluPointX_eq hπP hπP' ?_
    have h1 := (hcert P hπP).1
    have h2 := (hcert P' hπP').1
    refine mul_right_cancel₀ (mul_ne_zero hBs hBt) ?_
    linear_combination Bp.eval (veluPointX P') * h1 - Bp.eval (veluPointX P) * h2 + hfib
  -- fibre invariance of `A₁/B₁` (the `x`-half)
  have hinv1 : ∀ s t : F, s ∉ Sbad → t ∉ Sbad →
      Ap.eval s * Bp.eval t = Ap.eval t * Bp.eval s →
      A₁.eval s * B₁.eval t = A₁.eval t * B₁.eval s := by
    intro s t hs ht hfib
    obtain ⟨P, hP0, hPx⟩ := exists_point_veluPointX_eq (W := W) s
    obtain ⟨P', hP'0, hP'x⟩ := exists_point_veluPointX_eq (W := W) t
    subst hPx; subst hP'x
    obtain ⟨hπP, hψP, _, hZs⟩ := hgoodP P hP0 hs
    obtain ⟨hπP', hψP', _, hZt⟩ := hgoodP P' hP'0 ht
    simp only [Polynomial.eval_mul, mul_ne_zero_iff] at hZs hZt
    obtain ⟨⟨⟨⟨hBs, _⟩, _⟩, _⟩, _⟩ := hZs
    obtain ⟨⟨⟨⟨hBt, _⟩, _⟩, _⟩, _⟩ := hZt
    have hpm := hpair P P' hπP hπP' hBs hBt hfib
    have hxψ : veluPointX (ψ P) = veluPointX (ψ P') := by
      rcases hpm with h | h
      · rw [← hfac P, ← hfac P', h]
      · rw [← hfac P, ← hfac P', h, map_neg, velu_pointX_neg]
    have h1 := (hcert₁ P hψP).1
    have h2 := (hcert₁ P' hψP').1
    rw [hxψ] at h1
    linear_combination B₁.eval (veluPointX P) * h2 - B₁.eval (veluPointX P') * h1
  -- fibre invariance of `C₁·Ep / (E₁·Cp)` (the `y`-half)
  have hinv2 : ∀ s t : F, s ∉ Sbad → t ∉ Sbad →
      Ap.eval s * Bp.eval t = Ap.eval t * Bp.eval s →
      (C₁ * Ep).eval s * (E₁ * Cp).eval t = (C₁ * Ep).eval t * (E₁ * Cp).eval s := by
    intro s t hs ht hfib
    obtain ⟨P, hP0, hPx⟩ := exists_point_veluPointX_eq (W := W) s
    obtain ⟨P', hP'0, hP'x⟩ := exists_point_veluPointX_eq (W := W) t
    subst hPx; subst hP'x
    obtain ⟨hπP, hψP, hP2, hZs⟩ := hgoodP P hP0 hs
    obtain ⟨hπP', hψP', hP'2, hZt⟩ := hgoodP P' hP'0 ht
    simp only [Polynomial.eval_mul, mul_ne_zero_iff] at hZs hZt
    obtain ⟨⟨⟨⟨hBs, _⟩, _⟩, _⟩, _⟩ := hZs
    obtain ⟨⟨⟨⟨hBt, _⟩, _⟩, _⟩, _⟩ := hZt
    have hpm := hpair P P' hπP hπP' hBs hBt hfib
    have hYP := hYne P hP0 hP2
    have hYP' := hYne P' hP'0 hP'2
    have haψ := yCert_antiInvariant (fun R hR => (hcert₁ R hR).2) hP0 hψP
    have haψ' := yCert_antiInvariant (fun R hR => (hcert₁ R hR).2) hP'0 hψP'
    have haπ := yCert_antiInvariant (fun R hR => (hcert R hR).2) hP0 hπP
    have haπ' := yCert_antiInvariant (fun R hR => (hcert R hR).2) hP'0 hπP'
    -- the anti-invariant values at `P` and `P'` are proportional with the SAME sign
    have hprop : (2 * veluPointY (ψ P) + W''.a₁ * veluPointX (ψ P) + W''.a₃)
          * (2 * veluPointY (π P') + W'.a₁ * veluPointX (π P') + W'.a₃)
        = (2 * veluPointY (ψ P') + W''.a₁ * veluPointX (ψ P') + W''.a₃)
          * (2 * veluPointY (π P) + W'.a₁ * veluPointX (π P) + W'.a₃) := by
      rcases hpm with h | h
      · have hψeq : ψ P = ψ P' := by rw [← hfac P, ← hfac P', h]
        rw [hψeq, h]
      · have hψeq : ψ P = -(ψ P') := by rw [← hfac P, ← hfac P', h, map_neg]
        rw [hψeq, h, velu_pointX_neg, velu_pointX_neg,
          velu_pointY_neg _ hψP', velu_pointY_neg _ hπP']
        ring
    simp only [Polynomial.eval_mul]
    refine mul_right_cancel₀ (mul_ne_zero hYP hYP') ?_
    linear_combination
      (Ep.eval (veluPointX P) * E₁.eval (veluPointX P') * Ep.eval (veluPointX P')
        * E₁.eval (veluPointX P)) * hprop
      - (Ep.eval (veluPointX P) * E₁.eval (veluPointX P') * Cp.eval (veluPointX P')
        * (2 * veluPointY P' + W.a₁ * veluPointX P' + W.a₃)) * haψ
      - (Ep.eval (veluPointX P) * E₁.eval (veluPointX P')
        * (2 * veluPointY (ψ P) + W''.a₁ * veluPointX (ψ P) + W''.a₃)
        * E₁.eval (veluPointX P)) * haπ'
      + (Ep.eval (veluPointX P') * E₁.eval (veluPointX P) * Cp.eval (veluPointX P)
        * (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)) * haψ'
      + (Ep.eval (veluPointX P') * E₁.eval (veluPointX P)
        * (2 * veluPointY (ψ P') + W''.a₁ * veluPointX (ψ P') + W''.a₃)
        * E₁.eval (veluPointX P')) * haπ
  obtain ⟨A', B', d, hB'ne, hA'deg, hB'deg, hid1⟩ :=
    exists_homogSubst_of_fibreInvariant (A := Ap) (B := Bp) (A₁ := A₁) (B₁ := B₁)
      hBp hB₁ hSfin hinv1
  obtain ⟨C₂, E₂, d₂, hE₂ne, hC₂deg, hE₂deg, hid2⟩ :=
    exists_homogSubst_of_fibreInvariant (A := Ap) (B := Bp) (A₁ := C₁ * Ep) (B₁ := E₁ * Cp)
      hBp (mul_ne_zero hE₁ hCp) hSfin hinv2
  refine IsRationalMap.of_cofinite
    (T := veluPointX '' (π '' (insert (0 : W.Point)
      {R : W.Point | R ≠ 0 ∧ veluPointX R ∈ Sbad})))
    (Set.Finite.image _ (Set.Finite.image _
      (Set.Finite.insert _ (finite_veluPointX_preimage hSfin))))
    ⟨A', B', Polynomial.C 2 * C₂ * B',
      C₂ * (Polynomial.C W'.a₁ * Polynomial.X + Polynomial.C W'.a₃) * B'
        - Polynomial.C W''.a₁ * A' * E₂ - Polynomial.C W''.a₃ * B' * E₂,
      Polynomial.C 2 * E₂ * B', hB'ne,
      mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.2 (by norm_num)) hE₂ne) hB'ne, ?_⟩
  intro Q hQ hQT
  obtain ⟨P, rfl⟩ := hsurj Q
  have hPnot : P ∉ insert (0 : W.Point) {R : W.Point | R ≠ 0 ∧ veluPointX R ∈ Sbad} := by
    intro hc
    exact hQT ⟨π P, ⟨P, hc, rfl⟩, rfl⟩
  have hP0 : P ≠ 0 := fun hc => hPnot (Set.mem_insert_iff.2 (Or.inl hc))
  have hPS : veluPointX P ∉ Sbad := fun hc =>
    hPnot (Set.mem_insert_iff.2 (Or.inr ⟨hP0, hc⟩))
  obtain ⟨hπP, hψP, _, hZs⟩ := hgoodP P hP0 hPS
  simp only [Polynomial.eval_mul, mul_ne_zero_iff] at hZs
  obtain ⟨⟨⟨⟨hBs, hEs⟩, hB₁s⟩, hE₁s⟩, _⟩ := hZs
  have hu : veluPointX (π P) * Bp.eval (veluPointX P) = Ap.eval (veluPointX P) :=
    (hcert P hπP).1
  have hev1 := eval_homogSubst (A := Ap) (B := Bp) (Q := B') hB'deg hu
  have hev2 := eval_homogSubst (A := Ap) (B := Bp) (Q := A') hA'deg hu
  have hev3 := eval_homogSubst (A := Ap) (B := Bp) (Q := E₂) hE₂deg hu
  have hev4 := eval_homogSubst (A := Ap) (B := Bp) (Q := C₂) hC₂deg hu
  have hid1' := congrArg (Polynomial.eval (veluPointX P)) hid1
  have hid2' := congrArg (Polynomial.eval (veluPointX P)) hid2
  simp only [Polynomial.eval_mul, hev1, hev2] at hid1'
  simp only [Polynomial.eval_mul, hev3, hev4] at hid2'
  have hkey1 : A₁.eval (veluPointX P) * B'.eval (veluPointX (π P))
      = B₁.eval (veluPointX P) * A'.eval (veluPointX (π P)) :=
    mul_left_cancel₀ (pow_ne_zero d hBs) (by linear_combination hid1')
  have hkey2 : C₁.eval (veluPointX P) * Ep.eval (veluPointX P)
        * E₂.eval (veluPointX (π P))
      = E₁.eval (veluPointX P) * Cp.eval (veluPointX P)
        * C₂.eval (veluPointX (π P)) :=
    mul_left_cancel₀ (pow_ne_zero d₂ hBs) (by linear_combination hid2')
  have hx₁ := (hcert₁ P hψP).1
  rw [hfac P]
  have hxc : veluPointX (ψ P) * B'.eval (veluPointX (π P))
      = A'.eval (veluPointX (π P)) :=
    mul_right_cancel₀ hB₁s (by linear_combination B'.eval (veluPointX (π P)) * hx₁ + hkey1)
  refine ⟨hxc, ?_⟩
  have haψ := yCert_antiInvariant (fun R hR => (hcert₁ R hR).2) hP0 hψP
  have haπ := yCert_antiInvariant (fun R hR => (hcert R hR).2) hP0 hπP
  have hNM : (2 * veluPointY (ψ P) + W''.a₁ * veluPointX (ψ P) + W''.a₃)
        * E₂.eval (veluPointX (π P))
      = (2 * veluPointY (π P) + W'.a₁ * veluPointX (π P) + W'.a₃)
        * C₂.eval (veluPointX (π P)) := by
    refine mul_right_cancel₀ (mul_ne_zero hE₁s hEs) ?_
    linear_combination (E₂.eval (veluPointX (π P)) * Ep.eval (veluPointX P)) * haψ
      - (C₂.eval (veluPointX (π P)) * E₁.eval (veluPointX P)) * haπ
      + (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) * hkey2
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_X]
  linear_combination B'.eval (veluPointX (π P)) * hNM
    - (W''.a₁ * E₂.eval (veluPointX (π P))) * hxc

/-! ### The dual isogeny -/

namespace Isogeny

/-- The dual of a nonzero isogeny, as a homomorphism of point groups.

Construction: `ker φ` is a group of order `n = deg φ`, so `n • k = 0` for every
`k ∈ ker φ` (`degree_nsmul_eq_zero`); hence multiplication by `n` on `W` kills
`ker φ` and descends along the isomorphism `W.Point ⧸ ker φ ≃+ W'.Point` supplied
by surjectivity. That the result is again an isogeny is `isRationalMap_dualHom`
plus the two geometric leaves — see `dual`. -/
noncomputable def dualHom (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) : W'.Point →+ W.Point :=
  (QuotientAddGroup.lift (AddMonoidHom.ker φ.toHom) (mulByHom W φ.degree)
      (fun k hk => by
        simpa using degree_nsmul_eq_zero hk h0)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm.toAddMonoidHom

/-- **`ψ̂ ∘ ψ = [deg ψ]`** — the defining property of the dual isogeny. -/
theorem dualHom_comp (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) (P : W.Point) :
    φ.dualHom h0 (φ.toHom P) = φ.degree • P := by
  have hsymm : (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm (φ.toHom P)
      = (QuotientAddGroup.mk P : W.Point ⧸ AddMonoidHom.ker φ.toHom) :=
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm_apply_eq.2 rfl
  simp only [dualHom, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, hsymm]
  rfl

/-! ### FALSITY AUDIT: the dual is not rational in characteristic `p`

**Refuted 2026-07-26**, machine-checked and axiom-clean below. `degree` is
`Nat.card (ker φ)`, which counts kernel *points*; for a purely inseparable isogeny
that is `1` however large the scheme-theoretic degree. The Frobenius is exactly such
an isogeny, and it satisfies every field of `IsIsogeny` — so `dualHom` descends
`[1] = id` and produces the *inverse Frobenius*, which is not a morphism.

Concretely, over `K = 𝔽̄₂` take `Ec : y² + y = x³`, which is nonsingular (`Δ = -27 = 1`),
so `[IsAlgClosed K]` and `[Ec.IsElliptic]` both hold — this is *not* the singular-curve
pathology of the audit further up, and neither of those hypotheses helps. Frobenius
`(x, y) ↦ (x², y²)` is:

* **rational** — `A = X², B = 1` for the `x`-part, and the curve relation `y² = x³ + y`
  turns the *quadratic* `y ↦ y²` into the *linear* witness `C = 1, D = X³, E = 1`;
* **surjective** on `K`-points, because `(√x, √y)` lies on `Ec` whenever `(x, y)` does;
* **injective**, so `ker = ⊥` and `degree = 1` (`frobIsog_degree`).

Hence `dualHom` is `x ↦ √x`, and a witness for it would give `s · B(s²) = A(s²)` for
every `s ∈ K`, i.e. the polynomial identity `X · B(X²) = A(X²)`. The left side has odd
degree and the right side even, so `B = 0`, contradicting `B ≠ 0`. -/

namespace NotIsRationalMapDualHom

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- An algebraic closure of `𝔽₂`. -/
abbrev K := AlgebraicClosure (ZMod 2)

noncomputable local instance : DecidableEq K := Classical.decEq _

local instance : CharP K 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem two_eq_zero : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2

/-- `y² + y = x³` over `𝔽₂`: supersingular, and **nonsingular**. -/
def Ec : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

theorem Ec_Δ : Ec.Δ = 1 := by decide

instance : Ec.IsElliptic := ⟨by rw [Ec_Δ]; exact isUnit_one⟩

/-- The Frobenius `x ↦ x²`, as a `𝔽₂`-algebra endomorphism of `𝔽̄₂`. -/
noncomputable def frob : K →ₐ[ZMod 2] K where
  toFun x := x ^ 2
  map_one' := one_pow 2
  map_mul' a b := mul_pow a b 2
  map_zero' := zero_pow (by norm_num)
  map_add' a b := by linear_combination (a * b) * two_eq_zero
  commutes' r := by
    show (algebraMap (ZMod 2) K r) ^ 2 = _
    rw [← map_pow]
    congr 1
    revert r
    decide

theorem frob_apply (x : K) : frob x = x ^ 2 := rfl

/-- The curve over `𝔽̄₂`. -/
noncomputable abbrev E : Affine K := (Ec⁄K).toAffine

/-- Frobenius on points. -/
noncomputable def frobPt : E.Point →+ E.Point := Affine.Point.map (W' := Ec) frob

theorem veluPointX_frobPt (P : E.Point) : veluPointX (frobPt P) = (veluPointX P) ^ 2 := by
  cases P with
  | zero =>
      show veluPointX (frobPt (0 : E.Point)) = veluPointX (0 : E.Point) ^ 2
      rw [map_zero]; simp
  | some x y h => rw [frobPt, Point.map_some]; simp [frob_apply]

theorem veluPointY_frobPt (P : E.Point) : veluPointY (frobPt P) = (veluPointY P) ^ 2 := by
  cases P with
  | zero =>
      show veluPointY (frobPt (0 : E.Point)) = veluPointY (0 : E.Point) ^ 2
      rw [map_zero]; simp
  | some x y h => rw [frobPt, Point.map_some]; simp [frob_apply]

instance : E.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have hd : E.Δ = 1 := by
    show (Ec.map (algebraMap (ZMod 2) K)).Δ = 1
    rw [WeierstrassCurve.map_Δ, Ec_Δ, map_one]
  rw [hd]; exact isUnit_one

theorem E_a₁ : E.a₁ = 0 := by simp [E, Ec]
theorem E_a₂ : E.a₂ = 0 := by simp [E, Ec]
theorem E_a₃ : E.a₃ = 1 := by simp [E, Ec]
theorem E_a₄ : E.a₄ = 0 := by simp [E, Ec]
theorem E_a₆ : E.a₆ = 0 := by simp [E, Ec]

/-- The curve relation, in the form the `y`-witness needs: `y² = x³ + y`. -/
theorem eqn {P : E.Point} (hP : P ≠ 0) :
    (veluPointY P) ^ 2 = (veluPointX P) ^ 3 + veluPointY P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
      have := h.1
      rw [Affine.equation_iff] at this
      simp only [E_a₁, E_a₂, E_a₃, E_a₄, E_a₆, veluPointX_some, veluPointY_some] at this ⊢
      linear_combination this - y * two_eq_zero

/-- Every element of `K` is the `x`-coordinate of a nonzero point: `Y² + Y - x³`
has a root, `K` being algebraically closed. -/
theorem exists_point (x₀ : K) : ∃ P : E.Point, P ≠ 0 ∧ veluPointX P = x₀ := by
  have hdeg : (X ^ 2 + X - Polynomial.C (x₀ ^ 3) : K[X]).degree = 2 := by compute_degree!
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (k := K)
    (p := X ^ 2 + X - Polynomial.C (x₀ ^ 3)) (by rw [hdeg]; decide)
  have heq : E.Equation x₀ y₀ := by
    rw [Affine.equation_iff]
    simp only [E_a₁, E_a₂, E_a₃, E_a₄, E_a₆]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hy₀
    linear_combination hy₀
  exact ⟨Point.some x₀ y₀ (Affine.equation_iff_nonsingular.1 heq),
    Point.some_ne_zero _, veluPointX_some _⟩

theorem frobPt_injective : Function.Injective frobPt := Point.map_injective frob

theorem frobPt_surjective : Function.Surjective frobPt := by
  intro Q
  cases Q with
  | zero => exact ⟨0, map_zero _⟩
  | some x y h =>
      obtain ⟨x₀, rfl⟩ := IsAlgClosed.exists_pow_nat_eq (k := K) x (n := 2) two_pos
      obtain ⟨y₀, rfl⟩ := IsAlgClosed.exists_pow_nat_eq (k := K) y (n := 2) two_pos
      have h4 : (y₀ ^ 2) ^ 2 + y₀ ^ 2 = (x₀ ^ 2) ^ 3 := by
        have := h.1
        rw [Affine.equation_iff] at this
        simp only [E_a₁, E_a₂, E_a₃, E_a₄, E_a₆] at this
        linear_combination this
      have hsq : (y₀ ^ 2 + y₀ - x₀ ^ 3) ^ 2 = 0 := by
        linear_combination h4 + (x₀ ^ 6 + y₀ ^ 3 - y₀ ^ 2 * x₀ ^ 3 - y₀ * x₀ ^ 3) * two_eq_zero
      have heq : E.Equation x₀ y₀ := by
        rw [Affine.equation_iff]
        simp only [E_a₁, E_a₂, E_a₃, E_a₄, E_a₆]
        linear_combination sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq)
      exact ⟨Point.some x₀ y₀ (Affine.equation_iff_nonsingular.1 heq), rfl⟩

/-- Frobenius is rational. The `y`-part is the interesting one: `y ↦ y²` is
quadratic, but the curve relation `y² = x³ + y` makes it linear in `y`. -/
theorem isRationalMap_frobPt : IsRationalMap frobPt := by
  refine ⟨X ^ 2, 1, 1, X ^ 3, 1, one_ne_zero, one_ne_zero, fun P hP => ?_⟩
  have hP0 : P ≠ 0 := fun hc => hP (by rw [hc, map_zero])
  refine ⟨?_, ?_⟩
  · simp only [veluPointX_frobPt, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X, mul_one]
  · simp only [veluPointY_frobPt, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X, mul_one, one_mul]
    linear_combination eqn hP0

theorem isIsogeny_frobPt : IsIsogeny frobPt where
  isRationalMap := isRationalMap_frobPt
  surjective _ := frobPt_surjective
  finite_ker _ := by
    have : (AddMonoidHom.ker frobPt : Set E.Point) = {0} := by
      ext P
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      exact ⟨fun h => frobPt_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    rw [this]; exact Set.finite_singleton _

/-- Frobenius as an isogeny. -/
noncomputable def frobIsog : Isogeny E E := ⟨frobPt, isIsogeny_frobPt⟩

theorem frobIsog_ne_zero : frobIsog.toHom ≠ 0 := by
  obtain ⟨P, hP0, _⟩ := exists_point 1
  intro hc
  have := congrArg (fun g : E.Point →+ E.Point => g P) hc
  simp only [AddMonoidHom.zero_apply] at this
  exact hP0 (frobPt_injective (by rw [show frobPt P = 0 from this, map_zero]))

/-- **`degree = 1`.** Frobenius is purely inseparable, so its kernel *of points* is
trivial — and this file's `degree` counts exactly that. This is the whole defect. -/
theorem frobIsog_degree : frobIsog.degree = 1 := by
  rw [Isogeny.degree_of_ne_zero frobIsog_ne_zero]
  have hker : AddMonoidHom.ker frobIsog.toHom = ⊥ := by
    ext P
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_bot]
    exact ⟨fun h => frobPt_injective (by rw [show frobPt P = 0 from h, map_zero]),
      fun h => by rw [show frobIsog.toHom = frobPt from rfl, h, map_zero]⟩
  rw [hker]
  exact Nat.card_unique

/-- Hence the "dual" is the *inverse* Frobenius. -/
theorem dualHom_frob (P : E.Point) :
    frobIsog.dualHom frobIsog_ne_zero (frobPt P) = P := by
  have := Isogeny.dualHom_comp frobIsog frobIsog_ne_zero P
  rw [frobIsog_degree, one_nsmul] at this
  exact this

/-- **REFUTATION 3.** `Isogeny.isRationalMap_dualHom` is FALSE in characteristic 2
even with `[IsAlgClosed F]` and `[W.IsElliptic]`: the dual of Frobenius is the
inverse Frobenius `x ↦ √x`, and no pair of polynomials computes a square root. -/
theorem isRationalMap_dualHom_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] [IsAlgClosed F] {W W' : Affine F}
        [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0),
        IsRationalMap (φ.dualHom h0) := by
  intro h
  obtain ⟨A, B, C, D, Ee, hB, _hEe, hcert⟩ := h frobIsog frobIsog_ne_zero
  -- every `x₀ : K` satisfies `x₀ · B(x₀²) = A(x₀²)`
  have key : ∀ x₀ : K, x₀ * B.eval (x₀ ^ 2) = A.eval (x₀ ^ 2) := by
    intro x₀
    obtain ⟨P, hP0, hPx⟩ := exists_point x₀
    have hd : frobIsog.dualHom frobIsog_ne_zero (frobPt P) = P := dualHom_frob P
    have hne : frobIsog.dualHom frobIsog_ne_zero (frobPt P) ≠ 0 := by rw [hd]; exact hP0
    have := (hcert (frobPt P) hne).1
    rw [hd, veluPointX_frobPt, hPx] at this
    exact this
  -- so `X · B(X²) − A(X²)` vanishes identically
  have hpoly : X * B.comp (X ^ 2) = A.comp (X ^ 2) := by
    have hz : X * B.comp (X ^ 2) - A.comp (X ^ 2) = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
        (f := fun x₀ : K => x₀) Function.injective_id ?_)
      intro x₀
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_pow]
      linear_combination key x₀
    linear_combination hz
  -- but the two sides have degrees of opposite parity
  have hBc : B.comp (X ^ 2) ≠ 0 := by
    intro hc
    refine hB (Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun u : K => u) Function.injective_id ?_))
    intro u
    obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq (k := K) u (n := 2) two_pos
    have := congrArg (fun p : K[X] => p.eval s) hc
    simpa [Polynomial.eval_comp] using this
  have hAc : A.comp (X ^ 2) ≠ 0 := by
    rw [← hpoly]; exact mul_ne_zero Polynomial.X_ne_zero hBc
  have hdeg := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hBc, Polynomial.natDegree_X,
    Polynomial.natDegree_comp, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow] at hdeg
  omega

end NotIsRationalMapDualHom

/-- **PROVEN 2026-07-27**, by descent — see `IsRationalMap.descend` and the section
docstring above it. The dual is *defined* as the descent of `[deg φ]` along `φ`
(`dualHom`, `dualHom_comp`), so this is literally the descent principle at
`π := φ.toHom`, `ψ := mulByHom W φ.degree`; `[deg φ]` is rational by
`isRationalMap_mulByHom`. Everything below the `descend` line is closed except ONE
statement of one-variable polynomial algebra,
`exists_homogSubst_of_fibreInvariant` — no curve, no group, no `End` in it.

The historical audit of this leaf follows; it is still accurate about *why* the
hypotheses are what they are.

**LEAF (historical).** The dual of an isogeny is again given by rational functions.

This is the one genuinely geometric half of the dual construction: the map
induced on the quotient is a morphism of curves.

`[IsAlgClosed F]` and `[W.IsElliptic]` were added 2026-07-26, matching `dual` — the
only consumer, which always carried them. The previous owner had recorded that the
unqualified form was stated for a `φ` whose `IsIsogeny` witness asserts surjectivity
*on `F`-points*, which over a general field is an extremely strong and surprising
hypothesis (the FALSITY AUDIT of `IsIsogeny.add` shows `[2]` on `W(𝔽₅)` fails it),
and correctly declined to change someone else's declaration; the change is made here.

**CHARACTERISTIC AUDIT — the leaf was FALSE without `[CharZero F]`, which is now
present.** (Refuted 2026-07-26; the counterexample is machine-checked and
axiom-clean in `NotIsRationalMapDualHom` immediately above.)

The module docstring already says this file "is therefore correct only in
characteristic zero", because `degree` is defined as `Nat.card (ker φ)` and that
agrees with the classical degree only for *separable* isogenies. No hypothesis
anywhere enforces it, and `dualHom` is where the omission bites, because its whole
construction is "descend `[degree φ]` along `W.Point ⧸ ker φ ≃ W'.Point`".

The counterexample. Let `F = 𝔽̄₂` and `E : y² + y = x³`, which is nonsingular
(`Δ = -27 = 1`), so `[IsAlgClosed F]` and `[W.IsElliptic]` both hold. Let `φ` be the
Frobenius `(x, y) ↦ (x², y²)`; it is an additive map because the coefficients lie in
`𝔽₂`. It is an isogeny in this file's sense:

* rational — `x(φ P) = x(P)²` gives `A = X², B = 1`, and the curve relation
  `y² = x³ + y` turns the *quadratic* `y(φ P) = y(P)²` into the *linear* witness
  `C = 1, D = X³, E = 1`;
* surjective on `F`-points, since `(√x, √y)` lies on `E` whenever `(x, y)` does;
* `ker φ = {0}`, since `x ↦ x²` is injective. Hence `degree φ = 1`.

So `dualHom φ h0` is the descent of `[1] = id`, i.e. `φ⁻¹`, the *inverse* Frobenius
`(x, y) ↦ (√x, √y)`. That is not rational: a witness would give
`√u · B(u) = A(u)` for all `u` in the (cofinite) `x`-range, i.e. after `u = s²` the
polynomial identity `X · B(X²) = A(X²)`; but `A(X²)` has only even-degree terms and
`X · B(X²)` only odd-degree ones, so both sides vanish and `B = 0`, contradiction.

**In one line:** `degree` counts kernel *points*, so it is `1` for every purely
inseparable isogeny, and `dualHom` then claims `φ⁻¹` is a morphism.

**The repair.** `[CharZero F]` on `isRationalMap_dualHom`, `dual`, `dual_toHom` and
`dual_comp`. In characteristic zero every isogeny is separable, so `Nat.card (ker φ)`
*is* the classical degree and the descent of `[deg φ]` is the classical dual. This
costs nothing: every consumer works over `AlgebraicClosure ℚ`, and the module
docstring already declared characteristic zero to be this file's domain — it simply
had no hypothesis enforcing it anywhere. A separability hypothesis on `φ` would be
the sharper repair, but this file has no notion of separability and its `degree`
would still be the wrong invariant without one.

**ROUTE AUDIT, CORRECTED 2026-07-27** (the previous version of this paragraph sent
readers at divisor theory, and that was not necessary). It said: "the mathematics is
not the substitution algebra of `IsRationalMap.comp`, so `homogSubst` will not help
directly; the classical route is via divisors, `φ̂ = ι ∘ φ^* ∘ ι'⁻¹` through
`E ≅ Pic⁰(E)`, and nothing in the tree provides `Pic⁰`." The first clause is right —
this is not a composition — but the conclusion does not follow. `homogSubst` is
exactly the right tool, because what has to be produced is a rational function OF
`x ∘ φ` rather than a substitution INTO one, and `homogSubst A B d Q = B ^ d · Q(A/B)`
is precisely "a rational function of `A/B` with denominators cleared". No `Pic⁰` and
no divisor theory appear anywhere in the proof that replaced the `sorry`.

What the route does need is one honest input, isolated as
`exists_homogSubst_of_fibreInvariant`: a rational function constant on the fibres of
`A/B` is a rational function of `A/B` (Lüroth, or the trace/resultant formula
recorded in that leaf's docstring). `Affine.Point.toClass` into
`ClassGroup W.CoordinateRing` remains unused and is no longer needed here. -/
theorem isRationalMap_dualHom [IsAlgClosed F] [CharZero F] [W.IsElliptic] (φ : Isogeny W W')
    (h0 : φ.toHom ≠ 0) : IsRationalMap (φ.dualHom h0) :=
  IsRationalMap.descend φ.isIsogeny.isRationalMap (φ.isIsogeny.surjective h0)
    (isRationalMap_mulByHom φ.degree) (fun P => dualHom_comp φ h0 P)

/-- The dual isogeny, as an isogeny. -/
noncomputable def dual [IsAlgClosed F] [CharZero F] [W.IsElliptic] (φ : Isogeny W W')
    (h0 : φ.toHom ≠ 0) :
    Isogeny W' W :=
  ⟨φ.dualHom h0,
   { isRationalMap := isRationalMap_dualHom φ h0
     surjective := fun _ Q => by
       obtain ⟨P, hP⟩ := nsmul_surjective (W := W) (degree_pos h0).ne' Q
       exact ⟨φ.toHom P, by rw [dualHom_comp]; exact hP⟩
     finite_ker := fun _ => by
       -- `ker φ̂ = φ (W[n])`, the image of the finite `n`-torsion.
       refine Set.Finite.subset
         ((finite_nsmulKer (W := W) (n := φ.degree) (degree_pos h0).ne').image φ.toHom) ?_
       intro Q hQ
       obtain ⟨P, rfl⟩ := φ.isIsogeny.surjective h0 Q
       refine ⟨P, ?_, rfl⟩
       have hd := dualHom_comp φ h0 P
       have hz : φ.dualHom h0 (φ.toHom P) = 0 := hQ
       rw [hd] at hz
       exact hz }⟩

@[simp] theorem dual_toHom [IsAlgClosed F] [CharZero F] [W.IsElliptic] (φ : Isogeny W W')
    (h0 : φ.toHom ≠ 0) : (φ.dual h0).toHom = φ.dualHom h0 := rfl

/-- **`ψ̂ ∘ ψ = [deg ψ]`**, packaged as an equation of isogenies. -/
theorem dual_comp [IsAlgClosed F] [CharZero F] [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0)
    (P : W.Point) : ((φ.dual h0).comp φ).toHom P = φ.degree • P :=
  dualHom_comp φ h0 P

/-- The group-theoretic core of `degree_comp`, isolated from the curves: for a
composite `h ∘ f` with `f` SURJECTIVE, the kernel cardinalities multiply.

`ker f ↪ ker (h ∘ f) ↠ ker h` is exact — the second map is `f` restricted, which
is onto `ker h` precisely because `f` is onto — so Lagrange in `ker (h ∘ f)`
gives the product. Surjectivity of `f` is not decoration: without it the image
of `f` may meet `ker h` in a proper subgroup and the identity fails. -/
theorem card_ker_comp {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (h : B →+ C) (hf : Function.Surjective f) :
    Nat.card (AddMonoidHom.ker (h.comp f)) =
      Nat.card (AddMonoidHom.ker h) * Nat.card (AddMonoidHom.ker f) := by
  classical
  set K : AddSubgroup A := AddMonoidHom.ker (h.comp f)
  have hmem : ∀ x : K, f (x : A) ∈ AddMonoidHom.ker h := by
    intro x
    have hx : (h.comp f) (x : A) = 0 := (AddMonoidHom.mem_ker).1 x.2
    exact (AddMonoidHom.mem_ker).2 hx
  set g : K →+ AddMonoidHom.ker h :=
    AddMonoidHom.codRestrict (f.comp K.subtype) _ hmem
  have hgapp : ∀ x : K, (g x : B) = f (x : A) := fun _ => rfl
  have hgsurj : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hf b
    have haK : a ∈ K := by
      refine (AddMonoidHom.mem_ker).2 ?_
      show h (f a) = 0
      rw [ha]
      exact (AddMonoidHom.mem_ker).1 hb
    exact ⟨⟨a, haK⟩, Subtype.ext ha⟩
  have hcard1 : Nat.card (K ⧸ AddMonoidHom.ker g) = Nat.card (AddMonoidHom.ker h) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hgsurj).toEquiv
  have hfwd : ∀ x : AddMonoidHom.ker g, ((x : K) : A) ∈ AddMonoidHom.ker f := by
    intro x
    refine (AddMonoidHom.mem_ker).2 ?_
    rw [← hgapp]
    exact congrArg Subtype.val ((AddMonoidHom.mem_ker).1 x.2)
  have hbwd : ∀ y : AddMonoidHom.ker f, ((y : A) ∈ K) := by
    intro y
    refine (AddMonoidHom.mem_ker).2 ?_
    show h (f (y : A)) = 0
    rw [(AddMonoidHom.mem_ker).1 y.2, map_zero]
  have hbwd2 : ∀ y : AddMonoidHom.ker f,
      (⟨(y : A), hbwd y⟩ : K) ∈ AddMonoidHom.ker g := by
    intro y
    refine (AddMonoidHom.mem_ker).2 (Subtype.ext ?_)
    rw [hgapp]
    exact (AddMonoidHom.mem_ker).1 y.2
  have hcard2 : Nat.card (AddMonoidHom.ker g) = Nat.card (AddMonoidHom.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨((x : K) : A), hfwd x⟩
        invFun := fun y => ⟨⟨(y : A), hbwd y⟩, hbwd2 y⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  calc Nat.card K
      = Nat.card (K ⧸ AddMonoidHom.ker g) * Nat.card (AddMonoidHom.ker g) :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card (AddMonoidHom.ker h) * Nat.card (AddMonoidHom.ker f) := by
        rw [hcard1, hcard2]

/-- **PROVEN.** The degree is multiplicative under composition.

Group-theoretically this is `#ker (ψ ∘ φ) = #ker φ · #ker ψ`, from the short exact
sequence `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ` whose surjectivity is surjectivity of
`φ` — that is `card_ker_comp`. The three degenerate cases are handled first: if
either factor is the zero map the composite is too, and both sides are `0`;
conversely if both are nonzero then so is the composite, again by surjectivity
of `φ`. No hypothesis on the base field is needed, because `degree` is *defined*
as the kernel cardinality.

**AXIOM NOTE.** `#print axioms` on this theorem still reports `sorryAx`, and that
is inherited from the STATEMENT, not from the proof: `Isogeny.comp` is a
structure whose `IsIsogeny` field routes through `IsIsogeny.comp`, whose
`isRationalMap` field is the still-open `IsRationalMap.comp`. So every statement
mentioning `Isogeny.comp` is tainted until that leaf closes, and this one will
become clean automatically when it does. Verified by the control
`Nat.card (ker (ψ.toHom.comp φ.toHom)) = Nat.card (ker ψ.toHom) * Nat.card (ker φ.toHom)`,
which is the same content with `Isogeny.comp` expanded away and reports exactly
`[propext, Classical.choice, Quot.sound]`; `card_ker_comp` itself is clean. -/
theorem degree_comp (φ : Isogeny W W') (ψ : Isogeny W' W'') :
    (ψ.comp φ).degree = ψ.degree * φ.degree := by
  by_cases hφ : φ.toHom = 0
  · have hc : (ψ.comp φ).toHom = 0 := by
      ext P
      show ψ.toHom (φ.toHom P) = 0
      rw [hφ, AddMonoidHom.zero_apply, map_zero]
    rw [degree_of_eq_zero hc, degree_of_eq_zero hφ, mul_zero]
  · by_cases hψ : ψ.toHom = 0
    · have hc : (ψ.comp φ).toHom = 0 := by
        ext P
        show ψ.toHom (φ.toHom P) = 0
        rw [hψ, AddMonoidHom.zero_apply]
      rw [degree_of_eq_zero hc, degree_of_eq_zero hψ, zero_mul]
    · have hcomp : (ψ.comp φ).toHom ≠ 0 := by
        intro hc
        refine hψ (AddMonoidHom.ext fun Q => ?_)
        obtain ⟨P, rfl⟩ := φ.isIsogeny.surjective hφ Q
        exact congrArg (fun f : W.Point →+ W''.Point => f P) hc
      rw [degree_of_ne_zero hcomp, degree_of_ne_zero hψ, degree_of_ne_zero hφ,
        comp_toHom]
      exact card_ker_comp φ.toHom ψ.toHom (φ.isIsogeny.surjective hφ)

end Isogeny

/-! ### The Vélu quotient map is a rational map

**The bridge from `Velu.lean` to `IsIsogeny`, PROVEN 2026-07-27.** Everything in
this section is closed. An earlier version of this header listed
`IsRationalMap.add`, `IsRationalMap.isIsogeny` and `Isogeny.isRationalMap_dualHom`
as "the three open leaves of this file"; **all three are now PROVEN**, the last of
them via `IsRationalMap.descend` and `exists_homogSubst_of_fibreInvariant`. So the
old caveat about `isIsogeny_of_veluMap` consuming an open leaf no longer applies —
it consumes `IsRationalMap.isIsogeny`, which is closed.

**Why this is the missing link.** `Velu.lean` builds the quotient of a curve by a
finite subgroup and proves its map on points is an additive, Galois-equivariant
homomorphism with prescribed kernel — but it never certifies that the map is given
by *rational functions*, which is the entire content of `IsRationalMap` and hence
of `IsIsogeny`. Without that certificate the Vélu route has no composition
theorem, because `IsIsogeny.comp` (proven, in this file) is the only composition
theorem in the tree; a Vélu-specific one would need Vélu-sum additivity
`veluT ⟨h⟩ = t₁ + t₂`, which is a theory rather than a lemma. With the certificate,
composites of Vélu quotients compose for free.

**The certificate, explicitly.** All five polynomials already exist in `Velu.lean`;
this section only assembles them. Writing `H = veluH S`, `Ξ = veluXi S`,
`N = veluXNum S`, `x = veluPointX P`, `y = veluPointY P`, and `X'`, `Y'` for the
Vélu coordinates `veluCoordX S P`, `veluCoordY S P`:

* `A = N`, `B = H`, from `veluXNum_eval : N(x) = H(x)·X'`;
* `C = 2Ξ`, `E = 2H²`, and
  `D = (a₁·T + a₃)·Ξ − a₁·H·N − a₃·H²`.

The `y`-half is Vélu's completed square. `velu_pole_V` gives
`2Y' + a₁X' + a₃ = (2y + a₁x + a₃)·(1 − ΣV)` and `veluXi_eval` gives
`Ξ(x) = H(x)²·(1 − ΣV)`; eliminating `(1 − ΣV)` between them and substituting
`X' = N(x)/H(x)` yields `Y'·2H(x)² = 2Ξ(x)·y + D(x)` — which is exactly the
`y`-clause with no division anywhere. So the whole section is `linear_combination`
over three already-proven `Velu.lean` identities.

`B ≠ 0` and `E ≠ 0` are free: `veluH` is a product of monic linear factors, hence
monic, hence nonzero, and `2 ≠ 0` in characteristic zero. This is worth noting
because the module docstring records the `B ≠ 0` side condition as "the whole
difficulty" in the *composition* lemma — it is no difficulty at all here, since
the Vélu denominator is monic by construction.

**Faithfulness.** No hypothesis is weakened anywhere below. `[CharZero F]` is
genuine (`veluT`, `veluW` and `veluCoordX` are defined by halving `±`-invariant
sums), and `[IsAlgClosed F]`/`[W.IsElliptic]` appear only on
`isIsogeny_of_veluMap`, inherited verbatim from `IsRationalMap.isIsogeny` — the
stronger side, as the refutations recorded above require. -/

/-- **PROVEN: the Vélu-quotient bridge, in its most general form.** Any
homomorphism whose coordinates, away from its kernel, are Vélu's coordinates for a
finite point subgroup `S` of odd order is an `IsRationalMap`.

Stated for an arbitrary target curve `W'` rather than for `W.veluCurve S` itself,
because every consumer in this development transports the Vélu map along an
equality of curves (`pointAddEquivOfEq`) before using it, and transport preserves
coordinates. -/
theorem isRationalMap_of_veluCoords [CharZero F] {S : Finset W.Point}
    (hS : IsPointSubgroup S) (hodd : Odd S.card) {φ : W.Point →+ W'.Point}
    (hcoord : ∀ P : W.Point, φ P ≠ 0 →
      P ∉ S ∧ veluPointX (φ P) = W.veluCoordX S P ∧
        veluPointY (φ P) = W.veluCoordY S P) :
    IsRationalMap φ := by
  refine ⟨veluXNum S, veluH S,
    Polynomial.C (2 : F) * veluXi S,
    (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) * veluXi S
      - Polynomial.C W.a₁ * veluH S * veluXNum S
      - Polynomial.C W.a₃ * (veluH S) ^ 2,
    Polynomial.C (2 : F) * (veluH S) ^ 2,
    (veluH_monic S).ne_zero,
    mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (pow_ne_zero 2 (veluH_monic S).ne_zero),
    fun P hP => ?_⟩
  obtain ⟨hPS, hx, hy⟩ := hcoord P hP
  have hXNum := veluXNum_eval hS hodd hPS
  have hXi := veluXi_eval hS hodd hPS
  have hV : 2 * W.veluCoordY S P + W.a₁ * W.veluCoordX S P + W.a₃
      = (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃)
        * (1 - ∑ Q ∈ S, veluPoleV W (veluPointX P) Q) := by
    rw [velu_coordX_eq hS hPS, velu_coordY_eq hS hPS]
    exact velu_pole_V hS hPS
  refine ⟨?_, ?_⟩
  · rw [hx]
    linear_combination -hXNum
  · rw [hy]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination ((veluH S).eval (veluPointX P)) ^ 2 * hV
      - (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) * hXi
      + (W.a₁ * (veluH S).eval (veluPointX P)) * hXNum

/-- **PROVEN.** The form of `isRationalMap_of_veluCoords` that a consumer actually
holds: the kernel is known to be exactly `S`, and the two coordinate identities are
known outside `S`. This is precisely the shape produced by
`exists_velu_quotient_isogeny_model` once its `φ` is unfolded — see the note on
`isRationalMap_veluMap` below. -/
theorem isRationalMap_of_veluMap [CharZero F] {S : Finset W.Point}
    (hS : IsPointSubgroup S) (hodd : Odd S.card) {φ : W.Point →+ W'.Point}
    (hker : ∀ P : W.Point, φ P = 0 ↔ P ∈ S)
    (hx : ∀ P : W.Point, P ∉ S → veluPointX (φ P) = W.veluCoordX S P)
    (hy : ∀ P : W.Point, P ∉ S → veluPointY (φ P) = W.veluCoordY S P) :
    IsRationalMap φ :=
  isRationalMap_of_veluCoords hS hodd fun P hP =>
    have h : P ∉ S := fun hc => hP ((hker P).mpr hc)
    ⟨h, hx P h, hy P h⟩

/-- **PROVEN: the canonical Vélu quotient map is an `IsRationalMap`.** This is the
bridge instantiated at `Velu.lean`'s own `veluMap`, so it is the literal statement
"the Vélu quotient map is a rational map" rather than a statement about an abstract
map satisfying coordinate hypotheses.

`φ` is taken as a hypothesised `AddMonoidHom` agreeing pointwise with `veluMap`,
rather than `veluMap` being bundled here, because bundling needs `velu_map_add` —
additivity — which is a separate concern this lemma does not depend on. Every
consumer already has the bundled hom in hand (both `exists_velu_quotient_isogeny_model`
and `exists_velu_quotient_isogeny_model_of_subgroup` build one with
`AddMonoidHom.mk'`), so `hφ` is discharged by `rfl` at each. -/
theorem isRationalMap_veluMap [CharZero F] [W.IsElliptic] {S : Finset W.Point}
    (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {φ : W.Point →+ (W.veluCurve S).Point}
    (hφ : ∀ P : W.Point, φ P = W.veluMap S hS hodd P) :
    IsRationalMap φ := by
  haveI : (W.veluCurve S).IsElliptic := W.velu_isElliptic S hS hodd
  refine isRationalMap_of_veluMap hS hodd (fun P => ?_) (fun P hP => ?_) (fun P hP => ?_)
  · rw [hφ]; exact W.veluMap_eq_zero_iff S hS hodd P
  · rw [hφ, W.veluMap_of_notMem hS hodd hP]; rfl
  · rw [hφ, W.veluMap_of_notMem hS hodd hP]; rfl

/-- **PROVEN, unconditionally.** A homomorphism whose kernel is a `Finset` has
finite kernel. Trivial, and recorded because it pins down exactly how much of
`IsIsogeny` the Vélu map still owes to an open leaf: of the three fields,
`isRationalMap` is `isRationalMap_veluMap` above and `finite_ker` is this, so
**`surjective` is the only one that is not already available** — and surjectivity
on `F`-points is a property of the base field, not of the morphism, which is why
it is gated on `[IsAlgClosed F]` in `IsRationalMap.isIsogeny`. -/
theorem finite_ker_of_ker_eq {S : Finset W.Point} {φ : W.Point →+ W'.Point}
    (hker : ∀ P : W.Point, φ P = 0 ↔ P ∈ S) :
    (AddMonoidHom.ker φ : Set W.Point).Finite := by
  have h : (AddMonoidHom.ker φ : Set W.Point) = (S : Set W.Point) := by
    ext P
    exact hker P
  rw [h]
  exact S.finite_toSet

/-- **The payoff: the Vélu quotient map is an `IsIsogeny`**, hence composes with
any other isogeny through the proven `IsIsogeny.comp`.

**BOOKKEEPING CORRECTION, 2026-07-27.** An earlier version of this docstring said
"this declaration consumes the open leaf `IsRationalMap.isIsogeny`". That is
STALE: `IsRationalMap.isIsogeny` has been PROVEN and axiom-clean since
2026-07-27 (see it above, and the module header at the top of this file, which
already recorded it). Nothing in this section is open; the note is corrected in
place because leaf lists get harvested from docstrings for dispatch, and this one
would have manufactured phantom work at a proven declaration.

What remains true of the old note is the *dependence structure*: this lemma
reaches the geometry only through `IsRationalMap.isIsogeny`, and exactly through
its `surjective` field, as `finite_ker_of_ker_eq` records. `[IsAlgClosed F]` and
`[W.IsElliptic]` are inherited verbatim from that theorem, both of which were
established as necessary by the refutations earlier in this file; the consumers of
interest work over `AlgebraicClosure ℚ` with `E` elliptic, so neither costs
anything downstream. -/
theorem isIsogeny_of_veluMap [CharZero F] [IsAlgClosed F] [W.IsElliptic]
    {S : Finset W.Point} (hS : IsPointSubgroup S) (hodd : Odd S.card)
    {φ : W.Point →+ (W.veluCurve S).Point}
    (hφ : ∀ P : W.Point, φ P = W.veluMap S hS hodd P) :
    IsIsogeny φ :=
  (isRationalMap_veluMap hS hodd hφ).isIsogeny

/-! ### Galois transport: conjugating a curve by an isomorphism of the base field

**Why this is not `WeierstrassCurve.Affine.Point.map` (checked against the pin,
2026-07-31).** Mathlib's `Point.map` maps between BASE CHANGES `(W'⁄F).Point →
(W'⁄K).Point` of ONE curve `W'` defined over a fixed base ring, along an
`f : F →ₐ[S] K`. That is the right tool when the curve is already defined over the
smaller field and only the field of coefficients of the POINTS grows — which is how
`MoretBailly.lean` uses it, and it is why `σ` there is an `S`-algebra map: it must
fix the coefficients of `W'`.

Here the curve itself is the thing being moved. `W : Affine (ℚ̄)` has arbitrary
coefficients, so a `σ ∈ Gal(ℚ̄/ℚ)` does NOT fix them; it carries `W` to the
CONJUGATE curve `W.map σ`, a different curve. The absence in mathlib is real rather
than a naming problem: no declaration relates `W.Point` to `(W.map f).Point`.

**What it costs, and what already exists.** Very little, because mathlib's affine
formulas are stated twice — once for algebra maps (`baseChange_addX`, …) and once
for plain RING HOMOMORPHISMS (`map_nonsingular`, `map_negY`, `map_addX`, `map_addY`,
`map_slope` in `Affine/Basic.lean` and `Affine/Formula.lean`). The ring-hom half is
exactly what a curve conjugation needs, so `Point.mapRingHom` below is mathlib's own
`Point.map` proof with `baseChange_*` replaced by `map_*` throughout.

The rest is bookkeeping: `IsRationalMap`'s certificate is a tuple of polynomials over
the base field, and applying `σ` coefficientwise (`Polynomial.map σ`) carries a
certificate for `φ` to one for the conjugated map, because `σ` is a ring
isomorphism and `veluPointX`/`veluPointY` commute with the point transport.
`IsIsogeny`'s other two fields transport along a bijection. Both are stated below in
the general "coordinate-compatible equivalences" form (`IsRationalMap.transport`,
`IsIsogeny.transport`) so that the SAME lemma proves both directions of the
resulting iff, applied once at `σ` and once at `σ.symm` — which is what makes
`End.mapRingEquiv` an isomorphism rather than merely a homomorphism, and avoids
having to cast along `(W.map σ).map σ.symm = W`.

**The intended consumer** is `Fermat/FLT/FreyCurve/MazurTorsion.lean`'s
`MazurCMForm.IsCMJInvariant.map`: with `WeierstrassCurve.map_j` giving
`j (W.map σ) = σ (j W)`, the CM `j`-invariants of a fixed order are stable under
`Gal(ℚ̄/ℚ)`, so "two distinct CM `j`-invariants" collapses to "one irrational CM
`j`-invariant". -/

section GaloisTransport

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The point map of a curve conjugation.** The additive homomorphism on points
induced by a ring homomorphism of fields `f : F →+* K`, from `W` to the CONJUGATED
curve `W.map f`.

This is mathlib's `WeierstrassCurve.Affine.Point.map` with the base-change formulas
replaced by their ring-homomorphism counterparts; see the section docstring for why
the two are genuinely different statements. `f` is injective automatically (a
homomorphism of fields), which is what discharges `map_nonsingular`. -/
noncomputable def Affine.Point.mapRingHom (W : Affine F) (f : F →+* K) :
    W.Point →+ (W.map f).Point where
  toFun P := match P with
    | .zero => 0
    | .some x y h => .some (f x) (f y) ((W.map_nonsingular f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right,
        Affine.Point.add_of_Y_eq (congrArg f hxy.left)
          (by rw [hxy.right, map_negY])]
    · simpa only [Affine.Point.add_some hxy, ← map_addX, ← map_addY, ← map_slope] using!
        (Affine.Point.add_some fun h =>
          hxy ⟨f.injective h.1, f.injective (map_negY f x₂ y₂ ▸ h).2⟩).symm

@[simp] theorem veluPointX_mapRingHom (W : Affine F) (f : F →+* K) (P : W.Point) :
    veluPointX (Affine.Point.mapRingHom W f P) = f (veluPointX P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

@[simp] theorem veluPointY_mapRingHom (W : Affine F) (f : F →+* K) (P : W.Point) :
    veluPointY (Affine.Point.mapRingHom W f P) = f (veluPointY P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

/-- **Item (1) of the Galois transport: `W.Point ≃+ (W.map σ).Point`.** The inverse
is written out by hand rather than obtained from `Point.mapRingHom (W.map σ) σ.symm`,
because that lands in `(W.map σ).map σ.symm`, which is only PROPOSITIONALLY equal to
`W`; casting `Point` along an equality of curves would then infect every downstream
computation. -/
noncomputable def Affine.Point.mapRingEquiv (W : Affine F) (σ : F ≃+* K) :
    W.Point ≃+ (W.map (σ : F →+* K)).Point where
  toFun := Affine.Point.mapRingHom W (σ : F →+* K)
  invFun P := match P with
    | .zero => 0
    | .some x y h => .some (σ.symm x) (σ.symm y)
        ((W.map_nonsingular (σ : F →+* K).injective (σ.symm x) (σ.symm y)).mp (by
          rw [show ((σ : F →+* K) (σ.symm x)) = x from σ.apply_symm_apply x,
            show ((σ : F →+* K) (σ.symm y)) = y from σ.apply_symm_apply y]
          exact h))
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · exact velu_point_some_eq (σ.symm_apply_apply x) (σ.symm_apply_apply y)
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · exact velu_point_some_eq (σ.apply_symm_apply x) (σ.apply_symm_apply y)
  map_add' := (Affine.Point.mapRingHom W (σ : F →+* K)).map_add

theorem veluPointX_mapRingEquiv_symm (W : Affine F) (σ : F ≃+* K)
    (Q : (W.map (σ : F →+* K)).Point) :
    veluPointX ((Affine.Point.mapRingEquiv W σ).symm Q) = σ.symm (veluPointX Q) := by
  have h1 := veluPointX_mapRingHom W (σ : F →+* K) ((Affine.Point.mapRingEquiv W σ).symm Q)
  rw [show Affine.Point.mapRingHom W (σ : F →+* K) ((Affine.Point.mapRingEquiv W σ).symm Q) = Q
    from (Affine.Point.mapRingEquiv W σ).apply_symm_apply Q] at h1
  rw [h1]
  exact (σ.symm_apply_apply _).symm

theorem veluPointY_mapRingEquiv_symm (W : Affine F) (σ : F ≃+* K)
    (Q : (W.map (σ : F →+* K)).Point) :
    veluPointY ((Affine.Point.mapRingEquiv W σ).symm Q) = σ.symm (veluPointY Q) := by
  have h1 := veluPointY_mapRingHom W (σ : F →+* K) ((Affine.Point.mapRingEquiv W σ).symm Q)
  rw [show Affine.Point.mapRingHom W (σ : F →+* K) ((Affine.Point.mapRingEquiv W σ).symm Q) = Q
    from (Affine.Point.mapRingEquiv W σ).apply_symm_apply Q] at h1
  rw [h1]
  exact (σ.symm_apply_apply _).symm

/-- The conjugate `φ^σ` of an additive map of point groups along a field
isomorphism: transport the argument back along `σ`, apply `φ`, transport forward. -/
noncomputable def conjHom (σ : F ≃+* K) {W W' : Affine F} (φ : W.Point →+ W'.Point) :
    (W.map (σ : F →+* K)).Point →+ (W'.map (σ : F →+* K)).Point :=
  ((Affine.Point.mapRingEquiv W' σ).toAddMonoidHom.comp φ).comp
    (Affine.Point.mapRingEquiv W σ).symm.toAddMonoidHom

theorem conjHom_apply (σ : F ≃+* K) {W W' : Affine F} (φ : W.Point →+ W'.Point)
    (Q : (W.map (σ : F →+* K)).Point) :
    conjHom σ φ Q
      = Affine.Point.mapRingEquiv W' σ (φ ((Affine.Point.mapRingEquiv W σ).symm Q)) := rfl

/-- The defining intertwining property of `conjHom`: `φ^σ ∘ σ_* = σ_* ∘ φ`. -/
theorem conjHom_mapRingEquiv (σ : F ≃+* K) {W W' : Affine F} (φ : W.Point →+ W'.Point)
    (P : W.Point) :
    conjHom σ φ (Affine.Point.mapRingEquiv W σ P) = Affine.Point.mapRingEquiv W' σ (φ P) := by
  rw [conjHom_apply, AddEquiv.symm_apply_apply]

/-- **Transport of `IsRationalMap` along coordinate-compatible equivalences.**

Stated in this general form — arbitrary additive equivalences of point groups that
intertwine `φ` with `ψ` and carry coordinates by a fixed ring homomorphism `f` —
because it is then applied TWICE to prove `isRationalMap_conjHom_iff`: once at `σ`
and once at `σ.symm`. A version phrased directly in terms of `conjHom σ` could only
prove the forward direction, and the reverse direction cannot be obtained by
conjugating a second time (that lands at `(W.map σ).map σ.symm`, not `W`).

`f` is injective automatically, which is what keeps the transported denominators
`B.map f` and `E.map f` nonzero — the only side condition of `IsRationalMap`. -/
theorem IsRationalMap.transport {V V' : Affine K} (f : F →+* K)
    (e : W.Point ≃+ V.Point) (e' : W'.Point ≃+ V'.Point)
    (hex : ∀ P : W.Point, veluPointX (e P) = f (veluPointX P))
    (hey : ∀ P : W.Point, veluPointY (e P) = f (veluPointY P))
    (hex' : ∀ P : W'.Point, veluPointX (e' P) = f (veluPointX P))
    (hey' : ∀ P : W'.Point, veluPointY (e' P) = f (veluPointY P))
    {φ : W.Point →+ W'.Point} {ψ : V.Point →+ V'.Point}
    (hcomm : ∀ P : W.Point, ψ (e P) = e' (φ P))
    (h : IsRationalMap φ) : IsRationalMap ψ := by
  obtain ⟨A, B, C, D, E, hB, hE, hcert⟩ := h
  have hev : ∀ (p : F[X]) (t : F), (p.map f).eval (f t) = f (p.eval t) := fun p t => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  refine ⟨A.map f, B.map f, C.map f, D.map f, E.map f,
    (Polynomial.map_ne_zero_iff f.injective).mpr hB,
    (Polynomial.map_ne_zero_iff f.injective).mpr hE, fun Q hQ => ?_⟩
  obtain ⟨P, rfl⟩ : ∃ P : W.Point, e P = Q := ⟨e.symm Q, e.apply_symm_apply Q⟩
  rw [hcomm P] at hQ ⊢
  have hφP : φ P ≠ 0 := fun hc => hQ (by rw [hc, map_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  refine ⟨?_, ?_⟩
  · rw [hex' (φ P), hex P, hev, hev, ← map_mul]
    exact congrArg f hx
  · rw [hey' (φ P), hex P, hey P, hev, hev, hev, ← map_mul, ← map_mul, ← map_add]
    exact congrArg f hy

/-- **Transport of `IsIsogeny` along an intertwining pair of equivalences.**

Note what is NOT here: no coordinate hypotheses. The `surjective` and `finite_ker`
fields are pure bijection bookkeeping — the kernel of `ψ` is the `e`-image of the
kernel of `φ` — and the only field that sees the base field at all is
`isRationalMap`, which is therefore taken as the argument `hrat` rather than
re-derived. That is what keeps this lemma and `IsRationalMap.transport` from
duplicating each other's hypothesis lists. -/
theorem IsIsogeny.transport {V V' : Affine K}
    (e : W.Point ≃+ V.Point) (e' : W'.Point ≃+ V'.Point)
    {φ : W.Point →+ W'.Point} {ψ : V.Point →+ V'.Point}
    (hcomm : ∀ P : W.Point, ψ (e P) = e' (φ P))
    (hrat : IsRationalMap ψ) (h : IsIsogeny φ) : IsIsogeny ψ := by
  have key : ψ ≠ 0 → φ ≠ 0 := by
    intro hne hc
    refine hne (AddMonoidHom.ext fun Q => ?_)
    obtain ⟨P, rfl⟩ : ∃ P : W.Point, e P = Q := ⟨e.symm Q, e.apply_symm_apply Q⟩
    rw [hcomm P, hc]
    simp
  refine ⟨hrat, fun hne R => ?_, fun hne => ?_⟩
  · obtain ⟨S, hS⟩ := h.surjective (key hne) (e'.symm R)
    exact ⟨e S, by rw [hcomm S, hS, e'.apply_symm_apply]⟩
  · have hset : (AddMonoidHom.ker ψ : Set V.Point) = e '' (AddMonoidHom.ker φ : Set W.Point) := by
      ext Q
      constructor
      · intro hQ
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hQ
        refine ⟨e.symm Q, ?_, e.apply_symm_apply Q⟩
        have h1 : ψ (e (e.symm Q)) = e' (φ (e.symm Q)) := hcomm _
        rw [e.apply_symm_apply, hQ] at h1
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker]
        exact e'.injective (by rw [map_zero, ← h1])
      · rintro ⟨P, hP, rfl⟩
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hP ⊢
        rw [hcomm P, hP, map_zero]
    rw [hset]
    exact (h.finite_ker (key hne)).image e

/-- **Item (2), first half: `IsRationalMap` is a Galois-invariant condition.** -/
theorem isRationalMap_conjHom_iff (σ : F ≃+* K) {W W' : Affine F} (φ : W.Point →+ W'.Point) :
    IsRationalMap (conjHom σ φ) ↔ IsRationalMap φ := by
  constructor
  · intro h
    exact h.transport (σ.symm : K →+* F) (Affine.Point.mapRingEquiv W σ).symm
      (Affine.Point.mapRingEquiv W' σ).symm
      (veluPointX_mapRingEquiv_symm W σ) (veluPointY_mapRingEquiv_symm W σ)
      (veluPointX_mapRingEquiv_symm W' σ) (veluPointY_mapRingEquiv_symm W' σ)
      (fun Q => ((Affine.Point.mapRingEquiv W' σ).symm_apply_apply _).symm)
  · intro h
    exact h.transport (σ : F →+* K) (Affine.Point.mapRingEquiv W σ)
      (Affine.Point.mapRingEquiv W' σ)
      (veluPointX_mapRingHom W (σ : F →+* K)) (veluPointY_mapRingHom W (σ : F →+* K))
      (veluPointX_mapRingHom W' (σ : F →+* K)) (veluPointY_mapRingHom W' (σ : F →+* K))
      (conjHom_mapRingEquiv σ φ)

/-- **Item (2), second half: `IsIsogeny` is a Galois-invariant condition.** -/
theorem isIsogeny_conjHom_iff (σ : F ≃+* K) {W W' : Affine F} (φ : W.Point →+ W'.Point) :
    IsIsogeny (conjHom σ φ) ↔ IsIsogeny φ := by
  constructor
  · intro h
    exact h.transport (Affine.Point.mapRingEquiv W σ).symm
      (Affine.Point.mapRingEquiv W' σ).symm
      (fun Q => ((Affine.Point.mapRingEquiv W' σ).symm_apply_apply _).symm)
      ((isRationalMap_conjHom_iff σ φ).mp h.isRationalMap)
  · intro h
    exact h.transport (Affine.Point.mapRingEquiv W σ) (Affine.Point.mapRingEquiv W' σ)
      (conjHom_mapRingEquiv σ φ)
      ((isRationalMap_conjHom_iff σ φ).mpr h.isRationalMap)

/-- Conjugation of additive endomorphisms along an additive equivalence, as a ring
isomorphism `AddMonoid.End A ≃+* AddMonoid.End B`. Purely general; it is here rather
than in `Fermat/FLT/Mathlib/` only to keep the blast radius of this addition inside
one file. -/
def _root_.AddEquiv.conjAddMonoidEnd {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (e : A ≃+ B) : AddMonoid.End A ≃+* AddMonoid.End B where
  toFun g := (e.toAddMonoidHom.comp (g : A →+ A)).comp e.symm.toAddMonoidHom
  invFun g := (e.symm.toAddMonoidHom.comp (g : B →+ B)).comp e.toAddMonoidHom
  left_inv g := AddMonoidHom.ext fun a => by
    show e.symm (e (g (e.symm (e a)))) = g a
    rw [e.symm_apply_apply, e.symm_apply_apply]
  right_inv g := AddMonoidHom.ext fun b => by
    show e (e.symm (g (e (e.symm b)))) = g b
    rw [e.apply_symm_apply, e.apply_symm_apply]
  map_mul' g h := AddMonoidHom.ext fun b => by
    show e ((g * h) (e.symm b)) = e (g (e.symm (e (h (e.symm b)))))
    rw [e.symm_apply_apply]
    rfl
  map_add' g h := AddMonoidHom.ext fun b => by
    show e ((g + h) (e.symm b)) = e (g (e.symm b)) + e (h (e.symm b))
    rw [show (g + h) (e.symm b) = g (e.symm b) + h (e.symm b) from rfl, map_add]

/-- **Item (2), the payoff: `End W ≃+* End (W.map σ)`.**

A ring isomorphism, so it carries `ψ * ψ = (n : End W)` to `ψ^σ * ψ^σ = (n : End Wᵒ)`
and `Subring.closure {ψ} = ⊤` to `Subring.closure {ψ^σ} = ⊤` — which is the whole of
what `MazurCMForm.IsCMJInvariant` asks of `ψ`, and hence the whole of why that
predicate is `Gal(ℚ̄/ℚ)`-stable.

`[IsAlgClosed K]` is not decoration: `endSubring` exists only over an algebraically
closed field (`IsIsogeny.add` is FALSE otherwise — see the `𝔽₅` refutation earlier in
this file), so the TARGET needs its own instance. In the intended application
`K = F = ℚ̄` and both are the same instance. -/
noncomputable def End.mapRingEquiv [IsAlgClosed F] [IsAlgClosed K] (W : Affine F) [W.IsElliptic]
    (σ : F ≃+* K) : End W ≃+* End (W.map (σ : F →+* K)) :=
  RingEquiv.restrict (Affine.Point.mapRingEquiv W σ).conjAddMonoidEnd
    (endSubring W) (endSubring (W.map (σ : F →+* K)))
    (fun g => (isIsogeny_conjHom_iff σ (g : W.Point →+ W.Point)).symm)

/-! **Deliberately no `@[simp]` unfolding lemmas here** (`mapRingHom_zero`,
`mapRingHom_some`, `mapRingEquiv_apply`, `conjAddMonoidEnd_apply`,
`End.coe_mapRingEquiv`). Each is `rfl`, and each was written and then removed
because nothing in the tree consumes it, which makes it free-floating (see the
policy in `CLAUDE.md`). Add one back in the SAME commit as its first consumer —
the definitions above are transparent enough that `rfl`, `show`, or
`Affine.Point.mapRingEquiv W σ P = Affine.Point.mapRingHom W ↑σ P := rfl`
inline does the job until then. -/

end GaloisTransport

end WeierstrassCurve
