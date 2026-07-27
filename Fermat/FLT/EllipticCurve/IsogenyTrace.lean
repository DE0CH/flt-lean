/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Isogeny
-- `End W` is a NONcommutative ring, so the expansions of `(1 + Dψ)(1 + ψ)` and
-- of `χ²` below need `noncomm_ring`; `ring` does not apply.
public import Mathlib.Tactic.NoncommRing

/-!
# The trace of an endomorphism, and the Atkin–Lehner square identity

This file adds the **characteristic-polynomial layer** to
`Fermat/FLT/EllipticCurve/Isogeny.lean`, and uses it to prove the one algebraic
step that the Atkin–Lehner descent leaves of `MazurTorsion.lean` were carrying
inside themselves.

## What this file is for

The level-`N` nodes of Kenku's prime-power determination (`N = 125`, `169`, and
the prime range `p ≥ 23`) all end at the same place: a rational point of
`X_0(N)` that is fixed by the Atkin–Lehner involution `w_N` yields an
**endomorphism** `ψ` of `E` with `ψ² = [−N]`, whence `E` has complex
multiplication by the order of discriminant `−4N`.

Those leaves were previously stated with the conclusion `ψ * ψ = (−N)` directly,
which bundled two quite different things:

* a **modular** input — that the point is `w_N`-fixed at all, which needs
  `X_0(N)`, `J_0(N)`, the Atkin–Lehner involution and a rank computation; and
* an **algebraic** step — that `w_N`-fixedness forces `ψ² = [−N]` rather than
  merely `E ≅ E/C`.

`End.sq_eq_neg_natCast_of_atkinLehner` below discharges the second, from the
characteristic polynomial. That is a genuine reduction and not a renaming: see
the audit note on the hypothesis `himg` for the explicit curve which satisfies
`E ≅ E/C` with `C` cyclic of order `125` and yet has `ψ² ≠ [−125]`.

## Why this could not be written before

`WeierstrassCurve.End` — an endomorphism ring whose members carry an
`IsRationalMap` certificate — arrived only with `Isogeny.lean`. A
`CUT-OBSTRUCTION AUDIT` in `MazurTorsion.lean` recorded these nodes as atoms on
the ground that "there is no degree, no dual isogeny, no composition and no
endomorphism ring anywhere in the tree". That was true when written and is now
false; the present file is the consequence.

The audit's *other* objection stands and is respected here. It refuted the cut
that replaces the descent by the bare isomorphism `E ≅ E/C`, i.e. by
`j(E) = j(E/C)`, with the counterexample recalled under `himg`. The cut taken
here is strictly stronger than that one — it retains the action on the
`N`-torsion — and the counterexample does not satisfy it.
-/

@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ### Infinitely many points -/

omit [DecidableEq F] in
/-- Over an algebraically closed field **every `x`-coordinate is realised by a
point of the curve**.

The `y`-fibre above `ξ` is cut out by `TorsionCard.yQuad ξ`, a monic quadratic in
`y`; over an algebraically closed field it has a root, and a root of it is
precisely a solution of the Weierstrass equation above `ξ`
(`TorsionCard.eval_yQuad_eq_zero_iff_equation`), nonsingular because the curve is
elliptic. This is the `n`-free half of the fibre node
`Isogeny.exists_point_x_smul_algClosed`. -/
theorem exists_nonsingular_of_x [IsAlgClosed F] (V : Affine F) [V.IsElliptic] (ξ : F) :
    ∃ y₀ : F, (V⁄F).toAffine.Nonsingular ξ y₀ := by
  haveI : (V⁄F).IsElliptic := inferInstanceAs V.IsElliptic
  have hydeg : (TorsionCard.yQuad V ξ).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero V ξ),
      TorsionCard.yQuad_natDegree]
    norm_num
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root (TorsionCard.yQuad V ξ) hydeg
  exact ⟨y₀, (V⁄F).toAffine.equation_iff_nonsingular.mp
    ((TorsionCard.eval_yQuad_eq_zero_iff_equation V ξ y₀).mp hy₀)⟩

omit [DecidableEq F] in
/-- **The point group of an elliptic curve over an algebraically closed field is
infinite.**

The `x`-coordinate hits every element of `F` (`exists_nonsingular_of_x`), and an
algebraically closed field is infinite, so a choice of `y` over each `x` embeds
`F` into `V.Point`.

This is what pins the integers *inside* `End W`: without it `[m] = [m']` could
hold for `m ≠ m'` and the degree form below would carry no arithmetic. -/
theorem infinite_point [IsAlgClosed F] (V : Affine F) [V.IsElliptic] :
    Infinite V.Point := by
  classical
  choose y hy using exists_nonsingular_of_x V
  refine Infinite.of_injective
    (fun ξ : F => (Affine.Point.some ξ (y ξ) (hy ξ) : (V⁄F).Point)) ?_
  intro a b hab
  injection hab

/-- **`ℤ ↪ End W`.** Distinct integers act differently on points.

If `[c] = 0` then the whole point group is `|c|`-torsion, hence finite by
`finite_nsmulKer` — contradicting `infinite_point`. This is the step that turns
an identity in `End W` between integer casts into an identity in `ℤ`, and it is
what makes the Hasse bound below a statement about numbers rather than about
`End W`. -/
theorem End.intCast_injective [IsAlgClosed F] [W.IsElliptic] {a b : ℤ}
    (h : ((a : ℤ) : End W) = ((b : ℤ) : End W)) : a = b := by
  by_contra hne
  have hc0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hcz : (((a - b : ℤ)) : End W) = 0 := by rw [Int.cast_sub, h, sub_self]
  have hzero : ∀ P : W.Point, (a - b) • P = 0 := by
    intro P
    have hap : (((a - b : ℤ) : End W) : AddMonoid.End W.Point) P
        = ((0 : End W) : AddMonoid.End W.Point) P :=
      congrArg (fun f : End W => (f : AddMonoid.End W.Point) P) hcz
    rw [End.intCast_apply] at hap
    simpa using hap
  have hfin : (Set.univ : Set W.Point).Finite := by
    have hker := finite_nsmulKer (W := W) (n := (a - b).natAbs)
      (Int.natAbs_ne_zero.mpr hc0)
    refine hker.subset (fun P _ => ?_)
    have hcp : (((a - b).natAbs : ℤ)) • P = 0 := by
      rcases Int.natAbs_eq (a - b) with hEq | hEq
      · rw [← hEq]; exact hzero P
      · have h1 := hzero P
        rw [hEq, neg_smul, neg_eq_zero] at h1
        exact h1
    simpa only [Set.mem_setOf_eq, natCast_zsmul] using hcp
  haveI := infinite_point W
  exact (Set.infinite_univ (α := W.Point)) hfin

/-- The additive companion of `End.mul_apply`: a sum in `End W` acts pointwise.

`Isogeny.lean` records `End.mul_apply`, `End.intCast_apply` and `End.natCast_apply`
but not this one, and without it `simp only` cannot cross the subring coercion in
a sum such as `ψ * ψ + [n]`. Like its siblings it is `rfl`.

Deliberately **not** `@[simp]`, unlike `End.mul_apply` and friends: it is used
only through an explicit `simp only` below, so marking it would perturb the
ambient simp set of every downstream file for no gain. -/
theorem End.coe_add_apply [IsAlgClosed F] (f g : End W) (P : W.Point) :
    ((f + g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) P + (g : AddMonoid.End W.Point) P := rfl

/-! ### The characteristic polynomial of an endomorphism -/

/-- **LEAF — the one remaining input: the dual isogeny is ADDITIVE.**

There is an additive map `D : End W →+ End W` with `D ψ ∘ ψ = [deg ψ]` for every
`ψ`, including `ψ = 0` (where both sides are `0`).

This is Silverman *AEC* III.6.2, (a) and (b) together, and it is the whole of
what `End.exists_charPoly` below still needs.

**`D` is not an arbitrary choice: it is forced to be the dual.** For `ψ ≠ 0` the
map `ψ` is surjective on points (`IsIsogeny.surjective`), so `D ψ (ψ P) = deg ψ • P`
determines `D ψ` on every point; and `D 0 = 0` is forced by additivity. So this
existential is exactly the assertion that `Isogeny.dual` — already constructed in
`Isogeny.lean` with `dualHom_comp : ψ̂ (ψ P) = deg ψ • P`, which is the same
defining property — is additive in `ψ`. Nothing weaker is being asserted, and the
statement is not vacuous: a `D` satisfying it is unique.

**What is missing at this pin, precisely.** Additivity of `φ ↦ φ̂` is equivalent
to the parallelogram law for the degree,
`deg (φ + ψ) + deg (φ − ψ) = 2 deg φ + 2 deg ψ`, i.e. to `deg` being a
positive-definite quadratic form on `Hom(E, E')` (III.6.3). `Isogeny.degree` is
defined here as `Nat.card (ker ·)`, and nothing in the tree yet relates the
kernel of `φ + ψ` to those of `φ` and `ψ`. The classical route is divisor
theory — `deg` is `Pic⁰`-functorial and the parallelogram law is the theorem of
the cube — and the closest existing handle in this development is
`Affine.Point.toClass` into `ClassGroup W.CoordinateRing`, the same handle named
by `Isogeny.isRationalMap_dualHom`. Those two leaves are the divisor-theoretic
frontier of this cluster and should probably be attacked together.

**A correction to an earlier note.** A previous version of this docstring said
that `Isogeny.degree_comp` wants the same input. It does not, and it is now
PROVEN: multiplicativity of the degree under composition is pure group theory
(`Isogeny.card_ker_comp`, from `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ`) and needs nothing
about quadratic forms. Only the parallelogram law is still open. -/
theorem End.exists_dual [IsAlgClosed F] [W.IsElliptic] :
    ∃ D : End W →+ End W,
      ∀ ψ : End W, D ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) :=
  sorry

/-- **LEAF.** Every endomorphism of an elliptic curve satisfies a monic quadratic
over `ℤ` whose constant term is its degree and whose linear coefficient — the
**trace** `t` — obeys the Hasse bound `t² ≤ 4 · deg ψ`:

  `ψ² − [t] ∘ ψ + [deg ψ] = 0`,  `t² ≤ 4 · deg ψ`.

Both halves are Silverman *AEC* III.6: the degree is a positive-definite
quadratic form on `Hom(E, E')` (III.6.3), `ψ + ψ̂ = [t]` with
`t = 1 + deg ψ − deg(ψ − 1) ∈ ℤ` (III.6.2), and `ψ̂ ∘ ψ = [deg ψ]` — which is
already available here as `Isogeny.dual_comp`. The bound `t² ≤ 4 deg ψ` is
non-negativity of the discriminant of the binary quadratic form
`(m, k) ↦ deg (m + k ψ) = m² + t m k + (deg ψ) k²`, i.e. exactly the
Cauchy–Schwarz inequality for that form; it is the same computation that gives
the Hasse bound for Frobenius, with Frobenius replaced by `ψ`.

**PROVEN (2026-07-27) over the single leaf `End.exists_dual`** — additivity of
the dual. Given an additive `D` with `D ψ ∘ ψ = [deg ψ]`, everything here is
formal ring arithmetic in `End W`:

* `D 1 = 1`, since `deg (id) = 1` (`Isogeny.degree_id`, whose side condition
  `∃ P ≠ 0` comes from `infinite_point`), and `D [m] = [m]` for every integer
  `m`, since `[m] = m • 1` and `D` is additive.
* Expanding `D (1 + ψ) ∘ (1 + ψ) = [deg (1 + ψ)]` gives
  `1 + ψ + D ψ + [deg ψ] = [deg (1 + ψ)]`, i.e. `ψ + D ψ = [t]` with
  **`t := deg (1 + ψ) − 1 − deg ψ`** — the trace, exactly Silverman's
  `t = 1 + deg ψ − deg (1 − ψ)` up to the sign of `ψ`.
* Multiplying `ψ + D ψ = [t]` on the right by `ψ` and using `D ψ ∘ ψ = [n]`
  gives `[t] ψ = ψ² + [n]`, which is the first conjunct pointwise.
* For the Hasse bound take **`χ := 2ψ − [t]`**. Then `D χ = 2 D ψ − [t] = −χ`
  (using `D ψ = [t] − ψ`), so `[deg χ] = D χ ∘ χ = −χ²`, and expanding `χ²` with
  `[t] ψ = ψ² + [n]` gives `χ² = [t² − 4n]`. Hence `[4n − t²] = [deg χ]` with
  `deg χ` a **cardinality**, so `4n − t² ≥ 0` — by `End.intCast_injective`, which
  is where `infinite_point` is really used.

  Note this needs no density/approximation argument: the single choice
  `(m, k) = (−t, 2)` in the form `deg (m + kψ) = m² + tmk + nk²` already gives
  `4n − t² ≥ 0`, because `2` clears the denominator in the completion of the
  square.

**The `4` is not decoration.** With only `∃ t, ψ² − tψ + deg ψ = 0` and no bound
on `t`, the consumer below is FALSE: `ψ = [m]` satisfies `ψ² − 2mψ + m² = 0`
with `t = 2m` unbounded. The Hasse bound is what forces `t = 0` there. -/
theorem End.exists_charPoly [IsAlgClosed F] [W.IsElliptic] (ψ : End W) (n : ℕ)
    (hdeg : Nat.card (AddMonoidHom.ker ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point)) = n)
    (h0 : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) ≠ 0) :
    ∃ t : ℤ,
      (∀ P : W.Point,
        (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) + n • P
          = t • (ψ : AddMonoid.End W.Point) P)
      ∧ t ^ 2 ≤ 4 * (n : ℤ) := by
  classical
  haveI := infinite_point W
  obtain ⟨D, hD⟩ := End.exists_dual (W := W)
  -- The degree of `ψ` is `n`.
  have hdegψ : Isogeny.degree (End.toIsogeny ψ) = n := by
    rw [Isogeny.degree_of_ne_zero (φ := End.toIsogeny ψ) h0]
    exact hdeg
  have hDψ : D ψ * ψ = (n : End W) := by rw [hD ψ, hdegψ]
  -- `D` fixes `1`, because the identity has degree one.
  have hD1 : D 1 = 1 := by
    have hid : End.toIsogeny (1 : End W) = Isogeny.id W := Isogeny.ext (fun _ => rfl)
    have hone : Isogeny.degree (End.toIsogeny (1 : End W)) = 1 := by
      rw [hid]; exact Isogeny.degree_id (exists_ne (0 : W.Point))
    have h := hD 1
    rw [mul_one, hone, Nat.cast_one] at h
    exact h
  -- `D` fixes every integer.
  have hDint : ∀ m : ℤ, D ((m : ℤ) : End W) = ((m : ℤ) : End W) := by
    intro m
    have hm : ((m : ℤ) : End W) = m • (1 : End W) := by rw [zsmul_eq_mul, mul_one]
    rw [hm, map_zsmul, hD1]
  -- The trace.
  set t : ℤ := (Isogeny.degree (End.toIsogeny (1 + ψ)) : ℤ) - 1 - (n : ℤ) with ht
  have hsum : ψ + D ψ = ((t : ℤ) : End W) := by
    have h := hD (1 + ψ)
    rw [map_add, hD1] at h
    have hexp : (1 + D ψ) * (1 + ψ) = 1 + ψ + D ψ + D ψ * ψ := by noncomm_ring
    rw [hexp, hDψ] at h
    have hcast : ((t : ℤ) : End W)
        = ((Isogeny.degree (End.toIsogeny (1 + ψ)) : ℕ) : End W) - 1 - (n : End W) := by
      rw [ht]; push_cast; abel
    rw [hcast, ← h]; abel
  -- The characteristic polynomial, as an identity in `End W`.
  have hchar : ((t : ℤ) : End W) * ψ = ψ * ψ + (n : End W) := by
    rw [← hsum, add_mul, hDψ]
  refine ⟨t, fun P => ?_, ?_⟩
  · have hap := congrArg (fun f : End W => (f : AddMonoid.End W.Point) P) hchar
    simp only [End.coe_add_apply, End.mul_apply, End.intCast_apply,
      End.natCast_apply] at hap
    exact hap.symm
  -- The Hasse bound, from `χ := 2ψ − [t]`.
  · have hDψ' : D ψ = ((t : ℤ) : End W) - ψ := by rw [← hsum]; abel
    set χ : End W := ψ + ψ - ((t : ℤ) : End W) with hχ
    have hDχ : D χ = -χ := by
      rw [hχ, map_sub, map_add, hDint, hDψ']; abel
    have hcomm : ((t : ℤ) : End W) * ψ = ψ * ((t : ℤ) : End W) := (Int.cast_commute t ψ).eq
    have hχsq : χ * χ = ((t ^ 2 - 4 * (n : ℤ) : ℤ) : End W) := by
      have hexp : χ * χ
          = ψ * ψ + ψ * ψ + ψ * ψ + ψ * ψ
            - (((t : ℤ) : End W) * ψ + ((t : ℤ) : End W) * ψ)
            - (ψ * ((t : ℤ) : End W) + ψ * ((t : ℤ) : End W))
            + ((t : ℤ) : End W) * ((t : ℤ) : End W) := by
        rw [hχ]; noncomm_ring
      rw [hexp, ← hcomm, hchar]
      have hrhs : ((t ^ 2 - 4 * (n : ℤ) : ℤ) : End W)
          = ((t : ℤ) : End W) * ((t : ℤ) : End W)
            - ((n : End W) + (n : End W) + (n : End W) + (n : End W)) := by
        push_cast; noncomm_ring
      rw [hrhs]; abel
    have hkey : D χ * χ = ((4 * (n : ℤ) - t ^ 2 : ℤ) : End W) := by
      rw [hDχ, neg_mul, hχsq]; push_cast; abel
    have hdegχ := hD χ
    rw [hkey] at hdegχ
    have hnat : ((Isogeny.degree (End.toIsogeny χ) : ℕ) : End W)
        = (((Isogeny.degree (End.toIsogeny χ) : ℕ) : ℤ) : End W) := by push_cast; rfl
    rw [hnat] at hdegχ
    have hint := End.intCast_injective (W := W) hdegχ
    have hnn : (0 : ℤ) ≤ ((Isogeny.degree (End.toIsogeny χ) : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith [hint, hnn]

/-! ### The Atkin–Lehner square identity -/

/-- **`ψ² = [−N]` from Atkin–Lehner fixedness** (PROVEN 2026-07-26).

Let `ψ` be an endomorphism of an elliptic curve `W` over an algebraically closed
field, let `N > 4`, and suppose

* `hker` — `ker ψ = ⟨g⟩` with `g` of order exactly `N`, so `ψ` has degree `N`
  and cyclic kernel; and
* `himg` — `ψ (W[N]) = ⟨g⟩`, i.e. `ψ` maps the full `N`-torsion **onto its own
  kernel**.

Then `ψ * ψ = −[N]`.

The proof is three lines of arithmetic on the characteristic polynomial
`ψ² − tψ + N = 0` of `End.exists_charPoly`:

1. for `P ∈ W[N]` the relation reads `ψ(ψ P) + N • P = t • ψ P`, and both
   `N • P = 0` and — by `himg`, since `ψ P` then lies in `ker ψ` — `ψ(ψ P) = 0`;
   so `t • ψ P = 0` for every `N`-torsion `P`;
2. `himg` is onto `⟨g⟩`, so some such `ψ P` equals `g`, giving `t • g = 0` and
   hence `N = addOrderOf g ∣ t`;
3. `t ≠ 0` would force `N ≤ |t|`, so `N² ≤ t² ≤ 4N` by the Hasse bound and
   `N ≤ 4`, contradicting `hn`. So `t = 0` and `ψ² = −[N]`.

**FAITHFULNESS AUDIT: `himg` is what carries the Atkin–Lehner content, and
dropping it makes the statement FALSE.** The weaker hypothesis "`E ≅ E/C`", i.e.
`j(E) = j(E/C)`, does **not** suffice, and the counterexample is the one recorded
in `MazurTorsion.lean`'s cut-obstruction audit: over `ℚ̄` take `j = 1728`, with CM
by `ℤ[i]`, and `α = 11 + 2i`, of norm `125`. Then `α = i · (2 − i)³` with `(2 − i)`
a degree-one prime above the split prime `5`, so `ℤ[i]/(α) ≅ ℤ/125` and
`C := ker α` is cyclic of order `125` with `E/C ≅ E` — yet
`α² = 117 + 44i ≠ −125`.

That curve fails `himg`, which is the point: `α (E[125]) = ker ᾱ`, whereas
`ker α = C`, and `(α) ≠ (ᾱ)` because `5` splits. So `himg` excludes it, as it
must. Geometrically `himg` says the isomorphism `E/C ≅ E` carries `E[N]/C` back
onto `C` — which is exactly what it means for `(E, C)` to be a **fixed point of
`w_N`**, rather than merely a point whose image under `w_N` has the same
`j`-invariant.

**Non-vacuity.** The hypotheses are satisfiable: over `ℚ̄` any elliptic curve with
CM by the order of discriminant `−500` and `ψ = √−125` satisfies all of them at
`N = 125` (`ker ψ` is cyclic of order `125` because `√−125` generates a
non-invertible ideal of that order, and `ψ (E[125]) = ker ψ̂ = ker (−ψ) = ker ψ`).
So this lemma is not discharged by its own hypotheses being empty. -/
theorem End.sq_eq_neg_natCast_of_atkinLehner [IsAlgClosed F] [W.IsElliptic]
    (ψ : End W) (n : ℕ) (hn : 4 < n) (g : W.Point) (hg : addOrderOf g = n)
    (hker : AddMonoidHom.ker ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point)
      = AddSubgroup.zmultiples g)
    (himg : (fun P => (ψ : AddMonoid.End W.Point) P) '' {P : W.Point | n • P = 0}
      = (AddSubgroup.zmultiples g : Set W.Point)) :
    ψ * ψ = -(n : End W) := by
  -- `g` is hit by the `N`-torsion: choose a preimage `P₀`.
  have hgmem : g ∈ (fun P => (ψ : AddMonoid.End W.Point) P) '' {P : W.Point | n • P = 0} := by
    rw [himg]; exact AddSubgroup.mem_zmultiples g
  obtain ⟨P₀, hP₀tor, hP₀⟩ := hgmem
  -- `ψ` is not the zero map: otherwise `g = ψ P₀ = 0` and `addOrderOf g = 1 ≠ n`.
  have hne0 : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) ≠ 0 := by
    intro hzero
    have hg0 : g = 0 := by
      rw [← hP₀]
      exact congrFun (congrArg (fun f : W.Point →+ W.Point => (f : W.Point → W.Point)) hzero) P₀
    rw [hg0, addOrderOf_zero] at hg
    omega
  -- The degree of `ψ` is `n`.
  have hdeg : Nat.card (AddMonoidHom.ker ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point))
      = n := by
    rw [hker, Nat.card_zmultiples, hg]
  obtain ⟨t, hchar, hbound⟩ := End.exists_charPoly ψ n hdeg hne0
  -- Pointwise form of the characteristic polynomial on the `n`-torsion.
  have hpt : ∀ P : W.Point, n • P = 0 → t • (ψ : AddMonoid.End W.Point) P = 0 := by
    intro P hP
    -- `ψ P` lies in the image of the `n`-torsion, hence in `ker ψ`.
    have hmem : (ψ : AddMonoid.End W.Point) P ∈ AddSubgroup.zmultiples g := by
      have : (ψ : AddMonoid.End W.Point) P
          ∈ (fun Q => (ψ : AddMonoid.End W.Point) Q) '' {Q : W.Point | n • Q = 0} :=
        ⟨P, hP, rfl⟩
      rwa [himg] at this
    have hzz : (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) = 0 := by
      have := hker ▸ hmem
      exact this
    have hc := hchar P
    rw [hzz, hP] at hc
    simpa using hc.symm
  -- Hence `t • g = 0`, so `n ∣ t`.
  have htg : t • g = 0 := by rw [← hP₀]; exact hpt P₀ hP₀tor
  have hdvd : (n : ℤ) ∣ t := by
    rw [← hg]
    exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 htg
  -- The Hasse bound forces `t = 0`.
  have ht0 : t = 0 := by
    by_contra hne
    obtain ⟨k, rfl⟩ := hdvd
    have hk : k ≠ 0 := by rintro rfl; simp at hne
    have h1 : (1 : ℤ) ≤ k ^ 2 := by
      rcases lt_or_gt_of_ne hk with h | h <;> nlinarith
    -- `n² ≤ n²k² = t² ≤ 4n`, so `n ≤ 4`.
    have h2 : (n : ℤ) ^ 2 ≤ 4 * (n : ℤ) := by
      calc (n : ℤ) ^ 2 = (n : ℤ) ^ 2 * 1 := by ring
        _ ≤ (n : ℤ) ^ 2 * k ^ 2 := by
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((n : ℤ) * k) ^ 2 := by ring
        _ ≤ 4 * (n : ℤ) := hbound
    have h3 : (n : ℤ) ≤ 4 := by nlinarith
    have : (4 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    omega
  -- Conclude: with `t = 0` the characteristic polynomial reads `ψ² = [−n]`.
  have hfin : ∀ P : W.Point,
      (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) = (-(n : ℤ)) • P := by
    intro P
    have hc := hchar P
    rw [ht0, zero_smul] at hc
    rw [neg_smul, natCast_zsmul]
    exact eq_neg_of_add_eq_zero_left hc
  have hcast : (-(n : End W)) = ((-(n : ℤ) : ℤ) : End W) := by
    rw [Int.cast_neg, Int.cast_natCast]
  rw [hcast, End.sq_eq_intCast_iff]
  exact hfin

end WeierstrassCurve
