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

## Characteristic zero is required, and that is a 2026-07-27 repair

Everything in the trace layer carries `[CharZero F]`. This is not decoration and
not inherited caution: the file's original single leaf, `End.exists_dual`, was
stated without it and is **FALSE** that way — over `𝔽̄₂` the Frobenius of
`y² + y = x³` is an endomorphism of `Isogeny.degree = 1` with no rational inverse,
so no `D` with `D ψ ∘ ψ = [deg ψ]` can land in `End W`. The refutation is
machine-checked in `NotExistsDual` below, with an axiom-clean `End`-free core.

The repair also splits the leaf. In characteristic zero `Isogeny.dual` already
supplies the dual *with* its `IsIsogeny` witness, so `End.dualEnd` can be defined
outright and `End.exists_dual` becomes a theorem over additivity of the dual,
`End.dualEnd_add`. Rationality of the dual is no longer bundled in here; it is
`Isogeny.isRationalMap_dualHom`, owned in `Isogeny.lean`.

## The two open leaves, and a 2026-07-27 correction

`End.dualEnd_add` is now PROVEN, over the two leaves it decomposes into:

* `End.degree_add_add_degree_sub` — the parallelogram law, *AEC* III.6.3;
* `End.self_add_dualEnd` — the trace formula `ψ + ψ̂ = [deg(ψ+1) − deg ψ − 1]`,
  *AEC* III.6.2.

They are jointly equivalent to additivity and **neither alone suffices**: the
previous docstring's "additivity is equivalent to the parallelogram law" is wrong
in the direction it was being used. The CUT note above `End.degree_add_add_degree_sub`
records the circularity, the quantitative form of the obstruction, and the route —
through the torsion representation `End W → M₂(ZMod N)`, whose two inputs
`n_torsion_card` and `n_torsion_dimension` are already PROVEN in
`Fermat/FLT/EllipticCurve/Torsion.lean`.
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
ambient simp set of every downstream file for no gain.

`[W.IsElliptic]` is required because `End W` itself is (integrator, 2026-07-27):
`Isogeny.lean`'s `abbrev End [IsAlgClosed F] (W : Affine F) [W.IsElliptic]`
acquired that binder in the falsity repair that refuted the three `Isogeny.lean`
leaves over `𝔽̄₂`. This declaration was written against the older signature and
was the only one in this file missing the binder; every sibling here already
carries `[IsAlgClosed F] [W.IsElliptic]`. -/
theorem End.coe_add_apply [IsAlgClosed F] [W.IsElliptic] (f g : End W) (P : W.Point) :
    ((f + g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) P + (g : AddMonoid.End W.Point) P := rfl

/-! ### The characteristic polynomial of an endomorphism -/

/-! ### FALSITY AUDIT: `End.exists_dual` was FALSE without `[CharZero F]`

**Refuted 2026-07-27**, machine-checked below, with an axiom-clean core.

As originally cut, this leaf carried only `[IsAlgClosed F]` and `[W.IsElliptic]`.
It is false, and it fails for exactly the reason `Isogeny.isRationalMap_dualHom`
fails — a reason already refuted and machine-checked in `Isogeny.lean`'s own
`FALSITY AUDIT: the dual is not rational in characteristic p`, but not carried
across when this file was cut. `Isogeny.dual` and `Isogeny.dual_comp` both carry
`[CharZero F]`; the leaf asserted the very same content — its own docstring said
"any such `D` IS the dual" — without it.

The mechanism. `Isogeny.degree` is `Nat.card (ker ·)`, which counts kernel
*points*, so a purely inseparable isogeny has degree `1` however large its
scheme-theoretic degree. Over `K = 𝔽̄₂` the curve `E : y² + y = x³` is elliptic
and its Frobenius `φ : (x, y) ↦ (x², y²)` is an isogeny of degree `1`
(`Isogeny.NotIsRationalMapDualHom.frobIsog_degree`), hence an element `frobEnd`
of `End E`. Any `D` as in the leaf gives `D frobEnd ∘ φ = [1] = id`, i.e. an
element of `End E` — in particular a map given by rational functions — inverting
Frobenius. A rational left inverse of `φ` forces the polynomial identity
`X · B(X²) = A(X²)`, whose sides have `natDegree`s of opposite parity, so `B = 0`,
contradicting `B ≠ 0`.

**The `CharZero` repair costs the consumers nothing.** Both consumers of this
cluster — `MazurTorsion.lean`'s level-`125` and level-`169` Atkin–Lehner nodes —
work over `AlgebraicClosure ℚ`, where `CharZero` is found by instance synthesis,
so the added binder is discharged at every call site with no edit.

**The grep that would refute this audit**: a proof of
`Isogeny.isRationalMap_dualHom` that does not need `[CharZero F]`, or any
separability handle making `Isogeny.degree` the scheme-theoretic degree —

    grep -rn 'isRationalMap_dualHom\|[Ii]nseparable\|separableDegree' Fermat/

Neither exists at this pin. If one lands, the `CharZero` binders added here
should be revisited rather than treated as permanent. -/

namespace NotExistsDual

open WeierstrassCurve.Isogeny.NotIsRationalMapDualHom

noncomputable local instance : DecidableEq K := Classical.decEq _

/-- Frobenius over `𝔽̄₂`, as an element of the endomorphism ring. -/
noncomputable def frobEnd : End E := ⟨(frobPt : AddMonoid.End E.Point), isIsogeny_frobPt⟩

theorem toIsogeny_frobEnd : End.toIsogeny frobEnd = frobIsog := rfl

/-- **The `End`-free core of the refutation: no rational map inverts Frobenius.**

Stated without mentioning `End` on purpose. Everything mentioning `End` reports
`sorryAx` under `#print axioms` at carrier level — `endSubring`'s `add_mem'` field
routes through the still-open `IsIsogeny.add`, so even a literal `rfl` such as
`End.coe_add_apply` reports it. This statement therefore carries the mathematical
content of the refutation in a form where `#print axioms` is informative, and it
comes back `[propext, Classical.choice, Quot.sound]`.

The argument is the one in `Isogeny.isRationalMap_dualHom_is_false`, run against
an arbitrary rational left inverse rather than against `dualHom` specifically. -/
theorem not_isRationalMap_leftInverse_frob :
    ¬ ∃ g : E.Point →+ E.Point, IsRationalMap g ∧ ∀ P : E.Point, g (frobPt P) = P := by
  rintro ⟨g, hgrat, hgfrob⟩
  obtain ⟨A, B, C, Dp, Ee, hB, _hEe, hcert⟩ := hgrat
  -- every `x₀ : K` satisfies `x₀ · B(x₀²) = A(x₀²)`
  have key : ∀ x₀ : K, x₀ * B.eval (x₀ ^ 2) = A.eval (x₀ ^ 2) := by
    intro x₀
    obtain ⟨P, hP0, hPx⟩ := exists_point x₀
    have hd := hgfrob P
    have hne : g (frobPt P) ≠ 0 := by rw [hd]; exact hP0
    have h1 := (hcert (frobPt P) hne).1
    rw [hd, veluPointX_frobPt, hPx] at h1
    exact h1
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
  -- but the two sides have `natDegree`s of opposite parity
  have hBc : B.comp (X ^ 2) ≠ 0 := by
    intro hc
    refine hB (Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun u : K => u) Function.injective_id ?_))
    intro u
    obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq (k := K) u (n := 2) two_pos
    have := congrArg (fun p : K[X] => p.eval s) hc
    simpa [Polynomial.eval_comp] using this
  have hdegp := congrArg Polynomial.natDegree hpoly
  rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hBc, Polynomial.natDegree_X,
    Polynomial.natDegree_comp, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow] at hdegp
  omega

/-- **REFUTATION.** The old form of `End.exists_dual` fails over `𝔽̄₂`. -/
theorem not_exists_dual :
    ¬ ∃ D : End E →+ End E,
        ∀ ψ : End E, D ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End E) := by
  rintro ⟨D, hD⟩
  have hdeg : Isogeny.degree (End.toIsogeny frobEnd) = 1 := by
    rw [toIsogeny_frobEnd]; exact frobIsog_degree
  have hone := hD frobEnd
  rw [hdeg] at hone
  refine not_isRationalMap_leftInverse_frob
    ⟨((D frobEnd : AddMonoid.End E.Point) : E.Point →+ E.Point),
      ((D frobEnd).2 : IsIsogeny _).isRationalMap, fun P => ?_⟩
  have h2 := congrArg (fun f : End E => (f : AddMonoid.End E.Point) P) hone
  simp only [End.mul_apply, End.natCast_apply, one_smul] at h2
  exact h2

/-- **REFUTATION, in the shape of the leaf as it was stated.** `End.exists_dual`
without `[CharZero F]` is false. -/
theorem exists_dual_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic],
        ∃ D : End W →+ End W,
          ∀ ψ : End W, D ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) :=
  fun h => not_exists_dual h

end NotExistsDual

/-! ### The dual as a map on `End W`, in characteristic zero -/

open scoped Classical in
/-- **The dual of an endomorphism, as an endomorphism.**

In characteristic zero `Isogeny.dual` already packages `dualHom` together with its
`IsIsogeny` witness, so no new geometry is needed to land back in `End W`: the
only thing to add is the zero case, which `Isogeny.dual` excludes because a dual
of the zero map has no defining property to satisfy.

This is where the `[CharZero F]` of `Isogeny.dual` enters, and it is not
removable — see the FALSITY AUDIT above. -/
noncomputable def End.dualEnd [IsAlgClosed F] [CharZero F] [W.IsElliptic] (ψ : End W) : End W :=
  if h : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) = 0 then 0
  else ⟨((Isogeny.dual (End.toIsogeny ψ) h).toHom : AddMonoid.End W.Point),
    (Isogeny.dual (End.toIsogeny ψ) h).isIsogeny⟩

theorem End.dualEnd_of_eq_zero [IsAlgClosed F] [CharZero F] [W.IsElliptic] {ψ : End W}
    (h : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) = 0) : End.dualEnd ψ = 0 := by
  classical
  rw [End.dualEnd, dif_pos h]

theorem End.dualEnd_of_ne_zero [IsAlgClosed F] [CharZero F] [W.IsElliptic] {ψ : End W}
    (h : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) ≠ 0) :
    ((End.dualEnd ψ : AddMonoid.End W.Point) : W.Point →+ W.Point)
      = (End.toIsogeny ψ).dualHom h := by
  classical
  rw [End.dualEnd, dif_neg h]
  rfl

/-- **`ψ̂ ∘ ψ = [deg ψ]`** on `End W`, including at `ψ = 0` where both sides are `0`
(`deg 0 = 0` by `Isogeny.degree_of_eq_zero`). Away from `0` this is
`Isogeny.dualHom_comp` transported across the subring coercion. -/
theorem End.dualEnd_comp [IsAlgClosed F] [CharZero F] [W.IsElliptic] (ψ : End W) :
    End.dualEnd ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) := by
  by_cases h : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) = 0
  · have hz : ψ = 0 := Subtype.ext h
    have hd : Isogeny.degree (End.toIsogeny ψ) = 0 := Isogeny.degree_of_eq_zero h
    rw [hd, Nat.cast_zero, hz, mul_zero]
  · refine Subtype.ext (AddMonoidHom.ext fun P => ?_)
    show ((End.dualEnd ψ : AddMonoid.End W.Point) : W.Point →+ W.Point)
        (((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) P)
        = Isogeny.degree (End.toIsogeny ψ) • P
    rw [End.dualEnd_of_ne_zero h]
    exact Isogeny.dualHom_comp (End.toIsogeny ψ) h P

/-! ### CUT (2026-07-27): additivity of the dual splits into TWO independent leaves

`End.dualEnd_add` was a single leaf whose docstring recorded it as "equivalent to
the parallelogram law". **That equivalence is false in the direction it was being
used**, and the correction is the substance of this cut.

Additivity of `ψ ↦ ψ̂` is now PROVEN below over exactly two leaves:

* `End.degree_add_add_degree_sub` — the **parallelogram law** for the degree,
  Silverman *AEC* III.6.3;
* `End.self_add_dualEnd` — the **trace formula** `ψ + ψ̂ = [deg (ψ+1) − deg ψ − 1]`,
  Silverman *AEC* III.6.2, i.e. that `ψ` satisfies a monic quadratic over `ℤ`.

**These two are JOINTLY equivalent to `End.dualEnd_add`, and neither alone
suffices.** The trace formula follows from additivity by the very computation
`End.exists_charPoly` performs below (`hsum`), and the parallelogram law follows
from additivity together with the trace formula; conversely the assembly below
derives additivity from the two. So this is a conjunction split, not a renaming.

**Why the parallelogram law ALONE does not give additivity.** The natural attempt
is to verify the defining property for `φ̂ + ψ̂`, which after expanding
`(φ̂ + ψ̂)(φ + ψ)` and cancelling the surjective `φ + ψ` reduces to the bilinear
identity `φ̂ψ + ψ̂φ = [deg (φ+ψ) − deg φ − deg ψ]`. That identity's left-hand side
is additive in each slot **only if `ψ ↦ ψ̂` already is** — so the reduction is
circular, and no amount of parallelogram law repairs it.

The obstruction can be made quantitative, and it is worth recording because it
also shows the parallelogram law is not derivable from the trace formula alone.
Write `q χ := deg χ` and `t χ := q (χ+1) − q χ − 1`. The trace formula plus
right-cancellation gives the characteristic polynomial `χ² = [t χ] χ − [q χ]` for
every `χ`. Summing that at `φ+ψ` and `φ−ψ` and subtracting twice its values at
`φ` and at `ψ` — the cross terms `φψ + ψφ` cancel — leaves exactly

    [A] φ + [B] ψ = [C],   A := 2 t φ − t(φ+ψ) − t(φ−ψ),
                           B := 2 t ψ − t(φ+ψ) + t(φ−ψ),
                           C := 2 q φ + 2 q ψ − q(φ+ψ) − q(φ−ψ),

with `C` precisely the parallelogram defect. Substituting `ψ ↦ −ψ` or `φ ↦ −φ`
reproduces the same equation (`A`, `C` are even and `B` is odd under those), and
the one-parameter family `φ + mψ` gives back the `m = ±1` case; so no substitution
separates the three integers, and `C = 0` does not follow. An independence input
is genuinely required. (The diagonal `ψ = φ` *is* closable this way: there
`C = 4 q φ − q(2φ) = 0` because `q(2φ) = deg[2] · q φ = 4 q φ` by
`Isogeny.degree_comp` and `deg[2] = 4`.)

**THE ROUTE, and a correction to the old "nothing in the tree" note.** The old
docstring said `Isogeny.degree` is `Nat.card (ker ·)` and "nothing in the tree
relates `ker (φ+ψ)` to `ker φ` and `ker ψ`", then sent the reader to divisor
theory and `Affine.Point.toClass`. The divisor route is one route; it is not the
only one, and the arithmetic route is much better supported here **because the
torsion structure theorem is already PROVEN in this tree**:

* `WeierstrassCurve.n_torsion_card` (`Fermat/FLT/EllipticCurve/Torsion.lean`) —
  `Nat.card (E.nTorsion n) = n ^ 2`, over `[IsSepClosed k]`;
* `WeierstrassCurve.n_torsion_dimension` (same file) —
  `Nonempty (E.nTorsion n ≃+ ZMod n × ZMod n)`.

So `End W` acts on the free rank-`2` `ZMod N`-module `E[N]`, giving a *ring*
homomorphism `ρ_N : End W → M₂(ZMod N)`. Over that representation both leaves are
formal:

* `Matrix.adjugate` in dimension two is `adj A = (tr A) • 1 − A`
  (`Matrix.adjugate_fin_two`), which is **additive**; and `ρ_N ψ̂ = adj (ρ_N ψ)`
  because `ρ_N ψ̂ · ρ_N ψ = deg ψ · 1` and `adj A · A = det A · 1`;
* `det` on `2 × 2` matrices is a quadratic form over any commutative ring, so it
  satisfies the parallelogram law identically.

Both then transfer back because an element of `End W` killing every `E[N]` kills
an infinite set and so is `0` (an isogeny has finite kernel,
`IsIsogeny.finite_ker`, and `infinite_point` gives the contradiction).

**The single remaining input is therefore `deg ψ ≡ det (ρ_N ψ) (mod N)`** — the
classical `deg = det` on the Tate module — and the standard proof of *that* is the
Weil pairing identity `e_N (ψ P, ψ Q) = e_N (P, Q) ^ deg ψ` against
`e_N (A P, A Q) = e_N (P, Q) ^ det A`. This development has a large Weil-pairing
subtree (`WeilPairing*.lean`), so that is where the next owner should look first.

**The greps that would refute this analysis**:

    grep -rn 'weilPairing.*degree\|degree.*weilPairing' Fermat/
    grep -rn 'parallelogram\|adjugate\|Tate module' Fermat/ ~/cs/FLT/FLT/

**A correction to an earlier note that is still worth keeping.** A previous
version said `Isogeny.degree_comp` wants the same input. It does not, and it is
PROVEN: multiplicativity of the degree under composition is pure group theory
(`Isogeny.card_ker_comp`, from `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ`) and needs nothing
about quadratic forms. -/

/-- **LEAF — the parallelogram law for the degree.** Silverman *AEC* III.6.3: the
degree is a quadratic form on `End W`.

    deg (φ + ψ) + deg (φ − ψ) = 2 deg φ + 2 deg ψ.

Stated in `ℕ` because `Isogeny.degree` is `Nat.card (ker ·)`; every term is a
cardinality, and the assembly below casts to `ℤ` once.

This is one of the two leaves the additivity of the dual splits into — see the
CUT note above for why it is not sufficient by itself, and for the route through
`ρ_N : End W → M₂(ZMod N)` where it becomes the `2 × 2` determinant identity
`det (A+B) + det (A−B) = 2 det A + 2 det B`.

**Sanity check of the statement**, from the CM case: over `ℚ̄` with `End W ⊇ ℤ[i]`
and `deg = N` the field norm, `φ = 1`, `ψ = i` gives `N(1+i) + N(1−i) = 2 + 2 = 4`
and `2 N(1) + 2 N(i) = 2 + 2 = 4`. The degenerate cases are consistent too:
`ψ = 0` reads `2 deg φ = 2 deg φ`, and `ψ = φ` reads `deg (2φ) = 4 deg φ`, which is
independently PROVEN here (`Isogeny.degree_comp` with `deg [2] = 4`). -/
theorem End.degree_add_add_degree_sub [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (φ ψ : End W) :
    Isogeny.degree (End.toIsogeny (φ + ψ)) + Isogeny.degree (End.toIsogeny (φ - ψ))
      = 2 * Isogeny.degree (End.toIsogeny φ) + 2 * Isogeny.degree (End.toIsogeny ψ) :=
  sorry

/-- **LEAF — the trace formula.** Silverman *AEC* III.6.2: `ψ + ψ̂` is an integer,
and that integer is `deg (ψ + 1) − deg ψ − 1`:

    ψ + ψ̂ = [deg (ψ + 1) − deg ψ − 1].

Equivalently — multiply on the right by `ψ` and use `End.dualEnd_comp` — every
endomorphism satisfies the monic quadratic `ψ² − [t] ψ + [deg ψ] = 0` over `ℤ`.
This is the content `End.exists_charPoly` below currently obtains *from*
additivity; the cut turns it into an input, which is what makes the split honest
rather than a renaming (see the CUT note above).

**The formula is stated with an explicit trace rather than existentially** on
purpose: `∃ t, ψ + ψ̂ = [t]` would leave the assembly needing to know that `t` is
additive in `ψ`, which is exactly the missing content. Pinning `t = deg(ψ+1) − deg ψ − 1`
makes additivity of `t` a consequence of the parallelogram law alone, by
polarisation.

**Sanity checks**, all four of which the statement passes:
`ψ = 0` gives `0 = deg 1 − 0 − 1 = 0`; `ψ = [k]` gives `2k = (k+1)² − k² − 1`;
`ψ = i` on the curve with CM by `ℤ[i]` gives `i + î = i − i = 0` against
`N(1+i) − N(i) − 1 = 2 − 1 − 1 = 0`; and `ψ = 11 + 2i`, of norm `125` — the
Atkin–Lehner witness recalled under `End.sq_eq_neg_natCast_of_atkinLehner` — gives
`ψ + ψ̄ = 22` against `N(12+2i) − 125 − 1 = 148 − 126 = 22`.

`[CharZero F]` is required: `End.dualEnd` does not exist without it, the leaf
being false over `𝔽̄₂` (see the FALSITY AUDIT above). -/
theorem End.self_add_dualEnd [IsAlgClosed F] [CharZero F] [W.IsElliptic] (ψ : End W) :
    ψ + End.dualEnd ψ
      = (((Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1 : ℤ) : End W) :=
  sorry

/-- **The dual isogeny is ADDITIVE** — Silverman *AEC* III.6.2(b).

**PROVEN (2026-07-27)** over the two leaves `End.degree_add_add_degree_sub` (the
parallelogram law) and `End.self_add_dualEnd` (the trace formula); see the CUT
note above for why both are needed and for the route to closing them.

The proof is polarisation and nothing else. Write `q χ := deg χ`. The trace
formula rearranges to `ψ̂ = [q (ψ+1) − q ψ − 1] − ψ`, so additivity of `ψ ↦ ψ̂` is
exactly additivity of `t ψ := q (ψ+1) − q ψ − 1`. The parallelogram law gives
`q (−χ) = q χ` (take `φ = 0`) and then, by the standard four instances at
`(x−y, z)`, `(x+z, y)`, `(x, y)` and `(y+z, x)`, the three-variable identity

    q (x+y+z) = q (x+y) + q (y+z) + q (x+z) − q x − q y − q z,

which at `z = 1` — where `q 1 = 1` by `Isogeny.degree_id`, whose side condition
`∃ P ≠ 0` is `infinite_point` — reads `t (x+y) = t x + t y`. Rationality never
enters: it is carried by `End.dualEnd` itself, through `Isogeny.dual`. -/
theorem End.dualEnd_add [IsAlgClosed F] [CharZero F] [W.IsElliptic] (φ ψ : End W) :
    End.dualEnd (φ + ψ) = End.dualEnd φ + End.dualEnd ψ := by
  classical
  haveI := infinite_point W
  -- Polarisation, as a statement about an arbitrary `ℤ`-valued parallelogram
  -- function on an additive group: the trace `x ↦ q (x+1) − q x − 1` is additive.
  have main : ∀ q : End W → ℤ, (∀ a b : End W, q (a + b) + q (a - b) = 2 * q a + 2 * q b) →
      q 0 = 0 → q 1 = 1 → ∀ x y : End W,
        q (x + y + 1) - q (x + y) - 1
          = (q (x + 1) - q x - 1) + (q (y + 1) - q y - 1) := by
    intro q hpar hq0 hq1 x y
    have hneg : ∀ a : End W, q (-a) = q a := by
      intro a
      have h := hpar 0 a
      rw [zero_add, zero_sub, hq0] at h
      linarith
    have hthree : ∀ x y z : End W,
        q (x + y + z) = q (x + y) + q (y + z) + q (x + z) - q x - q y - q z := by
      intro x y z
      have h2 := hpar (x - y) z
      have h3 := hpar (x + z) y
      have h5 := hpar x y
      have h7 := hpar (y + z) x
      have e3a : x + z + y = x + y + z := by abel
      have e3b : x + z - y = x - y + z := by abel
      have e7a : y + z + x = x + y + z := by abel
      have e7b : y + z - x = -(x - y - z) := by abel
      rw [e3a, e3b] at h3
      rw [e7a, e7b, hneg] at h7
      linarith
    have h := hthree x y 1
    rw [hq1] at h
    linarith
  have hpar : ∀ a b : End W,
      (Isogeny.degree (End.toIsogeny (a + b)) : ℤ) + (Isogeny.degree (End.toIsogeny (a - b)) : ℤ)
        = 2 * (Isogeny.degree (End.toIsogeny a) : ℤ)
          + 2 * (Isogeny.degree (End.toIsogeny b) : ℤ) := by
    intro a b
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (End.degree_add_add_degree_sub a b)
  have hq0 : (Isogeny.degree (End.toIsogeny (0 : End W)) : ℤ) = 0 := by
    have hz : End.toIsogeny (0 : End W) = Isogeny.zero := rfl
    rw [hz, Isogeny.degree_zero]
    norm_num
  have hq1 : (Isogeny.degree (End.toIsogeny (1 : End W)) : ℤ) = 1 := by
    have hid : End.toIsogeny (1 : End W) = Isogeny.id W := Isogeny.ext (fun _ => rfl)
    rw [hid, Isogeny.degree_id (exists_ne (0 : W.Point))]
    norm_num
  have hkey := main (fun χ => (Isogeny.degree (End.toIsogeny χ) : ℤ)) hpar hq0 hq1 φ ψ
  have hdual : ∀ χ : End W, End.dualEnd χ
      = (((Isogeny.degree (End.toIsogeny (χ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny χ) : ℤ) - 1 : ℤ) : End W) - χ :=
    fun χ => eq_sub_of_add_eq' (End.self_add_dualEnd χ)
  rw [hdual (φ + ψ), hdual φ, hdual ψ, hkey]
  push_cast
  abel

/-- **The dual isogeny is ADDITIVE** — Silverman *AEC* III.6.2, (a) and (b)
together, and the whole of what `End.exists_charPoly` below needs.

There is an additive `D : End W →+ End W` with `D ψ ∘ ψ = [deg ψ]` for every `ψ`,
including `ψ = 0` (where both sides are `0`).

**`D` is not an arbitrary choice: it is forced to be the dual.** For `ψ ≠ 0` the
map `ψ` is surjective on points (`IsIsogeny.surjective`), so `D ψ (ψ P) = deg ψ • P`
determines `D ψ` on every point; and `D 0 = 0` is forced by additivity. So the
existential is exactly the assertion that `Isogeny.dual` is additive in `ψ`.
Nothing weaker is being asserted, and the statement is not vacuous: a `D`
satisfying it is unique.

**PROVEN (2026-07-27)** by taking `D = End.dualEnd`: `End.dualEnd_comp` supplies
the defining property outright and `End.dualEnd_add` the additivity, itself PROVEN
over the two leaves `End.degree_add_add_degree_sub` (the parallelogram law) and
`End.self_add_dualEnd` (the trace formula). `[CharZero F]` is REQUIRED — without
it the statement is false, refuted over `𝔽̄₂` in `NotExistsDual` above. -/
theorem End.exists_dual [IsAlgClosed F] [CharZero F] [W.IsElliptic] :
    ∃ D : End W →+ End W,
      ∀ ψ : End W, D ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) :=
  ⟨AddMonoidHom.mk' End.dualEnd End.dualEnd_add, End.dualEnd_comp⟩

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

**PROVEN (2026-07-27)** over the two leaves `End.degree_add_add_degree_sub` (the
parallelogram law) and `End.self_add_dualEnd` (the trace formula), reached through
`End.dualEnd_add` and `End.exists_dual`. Note the `hsum` step below is exactly the
trace formula recovered from additivity — which is why the two are jointly
equivalent to it, and why the split is a conjunction split rather than a renaming.
Given an additive `D` with
`D ψ ∘ ψ = [deg ψ]`, everything here is formal ring arithmetic in `End W`:

`[CharZero F]` was added 2026-07-27 with the falsity repair of `End.exists_dual`:
that leaf is FALSE in characteristic `p` (Frobenius has `Isogeny.degree = 1` and
no rational inverse), so every consumer of it inherits the binder. Both consumers
in `MazurTorsion.lean` work over `AlgebraicClosure ℚ` and discharge it by instance
synthesis.

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
theorem End.exists_charPoly [IsAlgClosed F] [CharZero F] [W.IsElliptic] (ψ : End W) (n : ℕ)
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
So this lemma is not discharged by its own hypotheses being empty.

**`[CharZero F]` added 2026-07-27**, inherited from `End.exists_charPoly` and
ultimately from the falsity repair of `End.exists_dual` (see the FALSITY AUDIT
above). It is discharged by synthesis at both call sites in `MazurTorsion.lean`,
which work over `AlgebraicClosure ℚ`. The non-vacuity witness recalled just above
is a CM curve over `ℚ̄`, so it is unaffected. -/
theorem End.sq_eq_neg_natCast_of_atkinLehner [IsAlgClosed F] [CharZero F] [W.IsElliptic]
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
