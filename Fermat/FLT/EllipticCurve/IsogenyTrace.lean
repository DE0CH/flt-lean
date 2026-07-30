/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Isogeny
-- `End W` is a NONcommutative ring, so the expansions of `(1 + Dψ)(1 + ψ)` and
-- of `χ²` below need `noncomm_ring`; `ring` does not apply.
public import Mathlib.Tactic.NoncommRing
-- The mod-`ℓ` torsion representation `End.torsionRep`, over which the
-- parallelogram law becomes the `2 × 2` determinant identity: `Torsion.lean`
-- supplies `nTorsion`, its `ZMod ℓ`-module structure and `p_torsion_rank`,
-- and `TorsionCounting.endRestrict` restricts an additive endomorphism to it.
-- COST AUDIT: this file's only consumer is `MazurTorsion.lean`, which already
-- imports `Fermat.FLT.EllipticCurve.Torsion` (its own import line 70), so the
-- addition puts no new module into any cone.
public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.LinearAlgebra.Determinant

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

## The ONE open leaf, and a 2026-07-27 correction to the correction

`End.dualEnd_add` is PROVEN, and so — as of the second pass of 2026-07-27 — is the
trace formula `End.self_add_dualEnd`. **As of the third pass (2026-07-27) so is the
parallelogram law `End.degree_add_add_degree_sub` itself**, over the mod-`ℓ` torsion
representation. **As of the fourth pass (2026-07-27)** `deg = det` is split at the
prime, with the divisible case discharged. **As of the fifth pass (2026-07-28) the
`deg = det` statement is PROVEN too**, over `End.exists_trace_charPoly_degree_sub`.
**As of the sixth pass (2026-07-28) that statement is PROVEN as well**, leaving
`End.exists_trace_charPoly` (`ψ² + [deg ψ] = [t] ψ`, Silverman *AEC* III.6.2) as the
leaf. **As of the SEVENTH pass (2026-07-28) that is PROVEN too**, over the existence
of an adjoint Weil pairing on `W[ℓ]`. **As of the EIGHTH pass (2026-07-30) THAT is
PROVEN as well** — see below, it was never outside the circle — and the file's two
remaining leaves are the two sub-steps of the elementary `x`-coordinate route:

* `End.exists_isXNormalForm_degree` — for a nonzero `φ ∈ End W`, writing
  `x ∘ φ = A / B` in lowest terms, `deg φ = max (deg A) (deg B)`. Silverman *AEC*
  II.2.4.1 + III.4.10; Washington *Elliptic Curves* §2.9.
* `End.isXNormalForm_natDegree_parallelogram` — that `max`-degree is a quadratic
  form on `End W`, by the `x`-only addition law and a coprimality count. A statement
  about `F[X]` alone.

**Passes one through SEVEN all stayed inside the circle.** They moved the `sorry`
between equivalent identities about *degrees*; the audit below proves that circle
cannot be broken from inside, because `ℤ[√2]` with `q := |N|` satisfies every fact
available about `deg` and violates all of them. The seventh pass replaced the
identity by the existence of a bilinear form and recorded that as "a genuinely
geometric input" — but on a rank-`2` space an alternating form is unique up to a
scalar, so the pairing carries no information beyond the determinant **in both
directions**, and the eighth pass proves it outright from the trace formula plus
`deg = det` (`altPairing_trace` supplies the adjugate identity; see
`exists_weilPairing_torsionRep_adjoint` at the foot of the file). The eighth pass is
the one that leaves the circle, by leaving the *language* of kernel cardinalities:
leaf (A) equates a kernel cardinality with a **polynomial degree**, and leaf (B) is
then pure `F[X]`.

The sixth pass is a **strict reduction**, not a reshuffle: the fifth-pass leaf
carried a second conjunct, the integer-shift expansion
`deg (ψ − [m]) = m² − t m + deg ψ`, and that conjunct follows from the first one
applied to the shifts `ψ − [m]` themselves — so it is now a theorem
(`End.exists_trace_charPoly_degree_sub`) rather than an obligation. The two new
supporting facts it needed, `End.degree_intCast` (`deg [c] = c²` — three docstrings
here had sketched it and none had named it) and `End.degree_mul`, are also PROVEN.

Alongside: `End.det_torsionRep_eq_zero_of_dvd` (the case `ℓ ∣ deg ψ`, where both
sides vanish — Cauchy's theorem in `ker ψ`) PROVEN, the previous leaf
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` PROVEN over the fifth-pass
statement, and the consumer-facing `End.natCast_degree_eq_det_torsionRep`
assembling the two cases.

**Every statement in this circle is equivalent** — `deg = det` mod `ℓ`, the
parallelogram law, the trace formula, additivity of the dual, and (as the eighth
pass showed, machine-checked) Weil-pairing adjointness too — so passes four through
seven made nothing mathematically easier. What the fifth pass did is machine-check
the implication `parallelogram law ⟹ deg = det`, which the fourth pass could only
sketch (it was a literal cycle while the `sorry` sat below it); what the sixth pass
did is remove the shift conjunct, so the next prover has ONE identity to establish
rather than an identity and an `m`-indexed family. Either way **any** proof of the
parallelogram law discharges the whole file in a few lines — which is what the
eighth pass finally arranged, by decomposing the parallelogram law into the two
leaves above rather than restating it. See the ROUTE section on
`End.exists_trace_charPoly_degree_sub` for the route audit that selected this, and
for the proof that no *counting* argument can ever supply any face of the circle.
The other route recorded there, Weil-pairing adjointness (*AEC* III.8.2), turned out
to be a face of the circle rather than an input to it, and is now PROVEN at the foot
of this file; the ROUTE 2 section marks where the divisor-theoretic construction it
seemed to require was taken off the critical path.

An earlier version of this docstring recorded the trace formula as a SECOND,
independent leaf, on the ground that the two are "jointly equivalent to additivity
and **neither alone suffices**". The *jointly equivalent* half is right; the
*neither alone suffices* half is **wrong**, and correcting it is the substance of
the second pass. That analysis ranged only over `deg` regarded as an abstract
`ℤ`-valued function on the additive group `End W` — and `deg` is also
**multiplicative** (`Isogeny.degree_comp`, PROVEN, pure group theory). With
multiplicativity in hand the trace formula is a THEOREM over the parallelogram
law, by the classical composition-algebra argument; see
`charPoly_of_multiplicative_parallelogram` below, which is stated `End`-free
precisely so that `#print axioms` can certify it, and does
(`[propext, Classical.choice, Quot.sound]`).
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

Stated without mentioning `End` on purpose, and it comes back
`[propext, Classical.choice, Quot.sound]`.

**RETIRED JUSTIFICATION (2026-07-27, fourth pass).** This paragraph used to say
that "everything mentioning `End` reports `sorryAx` under `#print axioms` at
carrier level", because `endSubring`'s `add_mem'` field routed through a then-open
`IsIsogeny.add`, so even a literal `rfl` such as `End.coe_add_apply` reported it.
**That is no longer true**: `IsIsogeny.add` is PROVEN, and all three of
`#print axioms WeierstrassCurve.IsIsogeny.add`,
`#print axioms WeierstrassCurve.End.coe_add_apply` and
`#print axioms WeierstrassCurve.End.torsionRep` return
`[propext, Classical.choice, Quot.sound]` (checked 2026-07-27). So `#print axioms`
is now informative on `End`-mentioning statements too, and the `End`-free phrasing
here — and in `charPoly_of_multiplicative_parallelogram` below — is preserved for
readability rather than out of necessity. Do not cite this file as evidence that
`End` statements cannot be axiom-audited.

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

/-! ### CUT (2026-07-27, revised the same day): additivity reduces to ONE leaf

`End.dualEnd_add` was a single leaf whose docstring recorded it as "equivalent to
the parallelogram law". **That equivalence is false in the direction it was being
used** — verifying the defining property for `φ̂ + ψ̂` reduces, after expanding
`(φ̂ + ψ̂)(φ + ψ)` and cancelling the surjective `φ + ψ`, to the bilinear identity
`φ̂ψ + ψ̂φ = [deg (φ+ψ) − deg φ − deg ψ]`, whose left-hand side is additive in each
slot **only if `ψ ↦ ψ̂` already is**. That circularity is real and is what this cut
exists to route around.

The first pass therefore split additivity into two leaves, the parallelogram law
and the trace formula. **The second pass proved the trace formula**; **the third
pass (2026-07-27) executed the `ρ_ℓ` route recorded below and proved the
parallelogram law too**, so the file now stands on exactly one open leaf:

* `End.natCast_degree_eq_det_torsionRep_of_not_dvd` — `deg ψ ≡ det (ρ_ℓ ψ) (mod ℓ)`
  at the primes `ℓ ∤ deg ψ`, Silverman *AEC* III.8.6. (The fourth pass, the
  same day, discharged the complementary case `ℓ ∣ deg ψ` outright as
  `End.det_torsionRep_eq_zero_of_dvd`, and proved the hypothesis-free
  `End.natCast_degree_eq_det_torsionRep` over the two.) **The fifth pass
  (2026-07-28) PROVED it**, over the then-new leaf
  `End.exists_trace_charPoly_degree_sub` — `ψ² + [deg ψ] = [t] ψ` together with
  `deg (ψ − [m]) = m² − t m + deg ψ` — by formalising the fourth pass's
  equivalence sketch. **The sixth pass (2026-07-28) proved that too**, from its
  first conjunct alone, leaving `End.exists_trace_charPoly` —
  `ψ² + [deg ψ] = [t] ψ`, `ℓ`-free. **The seventh pass (2026-07-28) proved that as
  well**, over the Weil-pairing leaf `exists_weilPairing_torsionRep_adjoint`, which
  it recorded as the first statement in this sequence that is not an identity
  between degrees. **That was wrong, and the eighth pass (2026-07-30) proved the
  pairing too** — it is a face of the same circle; see the ROUTE 2 section. The
  file's leaves are now `End.exists_isXNormalForm_degree` and
  `End.isXNormalForm_natDegree_parallelogram`, and `End.exists_trace_charPoly` is
  proven over the parallelogram law, which is proven over those two.

with

* `End.degree_add_add_degree_sub` — the **parallelogram law** for the degree,
  Silverman *AEC* III.6.3 — PROVEN below, over that leaf;
* `End.self_add_dualEnd` — the **trace formula** `ψ + ψ̂ = [deg (ψ+1) − deg ψ − 1]`,
  Silverman *AEC* III.6.2, i.e. that `ψ` satisfies a monic quadratic over `ℤ` —
  PROVEN below, over the parallelogram law.

**WHY THE FIRST PASS THOUGHT THE TRACE FORMULA WAS INDEPENDENT, AND WHY IT IS
NOT.** Its independence argument is reproduced below and every line of it is
correct; the defect is the SEARCH SPACE. It ranges only over `deg` regarded as an
abstract `ℤ`-valued function on the additive group `End W`, using nothing but the
parallelogram law and the characteristic polynomial. But `deg` carries a third
property that argument never touches: it is **multiplicative**,
`deg (φ ∘ ψ) = deg φ · deg ψ` (`Isogeny.degree_comp` — PROVEN, and pure group
theory, so not itself an independence input). A multiplicative parallelogram form
on a ring is a classical composition-algebra situation, and in that situation the
characteristic polynomial is forced. See
`charPoly_of_multiplicative_parallelogram`.

The moral, and it is the one the fleet doctrine states: an irreducibility verdict
is only as wide as the axis its author searched, so record the axis. The axis here
was *additive*; the missing one was *multiplicative*.

**The first pass's argument, preserved, and still valid on its own axis.**
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
of that shape separates the three integers, and `C = 0` does not follow **from the
characteristic polynomial alone**. That is still a correct obstruction, and it is
the reason the parallelogram law remains open: the trace formula does not give it
back. (The diagonal `ψ = φ` *is* closable this way: there
`C = 4 q φ − q(2φ) = 0` because `q(2φ) = deg[2] · q φ = 4 q φ` by
`Isogeny.degree_comp` and `deg[2] = 4`.)

**THE ROUTE — EXECUTED 2026-07-27, and a correction to the old "nothing in the
tree" note.** The old docstring said `Isogeny.degree` is `Nat.card (ker ·)` and
"nothing in the tree relates `ker (φ+ψ)` to `ker φ` and `ker ψ`", then sent the
reader to divisor theory and `Affine.Point.toClass`. The divisor route is one
route; it is not the only one, and the arithmetic route is much better supported
here **because the torsion structure theorem is already PROVEN in this tree**:

* `WeierstrassCurve.n_torsion_card` (`Fermat/FLT/EllipticCurve/Torsion.lean`) —
  `Nat.card (E.nTorsion n) = n ^ 2`, over `[IsSepClosed k]`;
* `WeierstrassCurve.n_torsion_dimension` (same file) —
  `Nonempty (E.nTorsion n ≃+ ZMod n × ZMod n)`.

So `End W` acts on the free rank-`2` `ZMod ℓ`-module `E[ℓ]`, giving a *ring*
homomorphism `ρ_ℓ : End W → End_{ZMod ℓ}(E[ℓ])`. That is `End.torsionRep` below —
`TorsionCounting.endRestrict` for the restriction, `AddMonoidHom.toZModLinearMap`
for the linearity, and all four `RingHom` fields are `rfl` after `ext`. Over that
representation the parallelogram law is formal: `det` on `2 × 2` matrices is a
quadratic form over any commutative ring (`det_add_add_det_sub` below,
`Matrix.det_fin_two` and `ring`), so it satisfies the parallelogram law
identically, and

    deg (φ+ψ) + deg (φ−ψ) − 2 deg φ − 2 deg ψ ≡ 0  (mod ℓ)

for every prime `ℓ`; an integer congruent to `0` modulo arbitrarily large primes
is `0` (`Nat.exists_infinite_primes` at `max A B + 1`, then
`Nat.ModEq.eq_of_lt_of_lt`). Note the second-pass proof means the adjugate half of
the old plan — `ρ_ℓ ψ̂ = adj (ρ_ℓ ψ)`, `Matrix.adjugate_fin_two`, additivity of
`adj` in dimension two — is **no longer needed for anything**: additivity of the
dual now follows from the parallelogram law alone. Only `det = deg` is wanted.

**`ℓ` PRIME, not general `N`.** The basis is what turns `LinearMap.det` into
`Matrix.det_fin_two`, and it comes from `WeierstrassCurve.p_torsion_rank`
(PROVEN, prime level) through `Module.finBasisOfFinrankEq`, which needs the
scalars to be a division ring. Since the conclusion is an identity between
integers, holding modulo arbitrarily large primes suffices, so nothing is lost.

Note the transfer back is *not* needed: an element of `End W` killing every `E[N]`
kills an infinite set and so is `0` (`IsIsogeny.finite_ker` against
`infinite_point`), but for the parallelogram law that is unnecessary, since the
conclusion is an identity between integers rather than between endomorphisms.

**The single remaining input of THIS route is `deg ψ ≡ det (ρ_ℓ ψ) (mod ℓ)`** — the
classical `deg = det` on the Tate module,
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` (its `ℓ ∣ deg ψ` half being
PROVEN as `End.det_torsionRep_eq_zero_of_dvd`). **As of 2026-07-28 that is PROVEN
too**, over `End.exists_trace_charPoly_degree_sub`, itself PROVEN the same day over
`End.exists_trace_charPoly` — which the seventh pass proved over the Weil pairing
`exists_weilPairing_torsionRep_adjoint` and the eighth pass reproved over the
parallelogram law, the pairing itself having turned out to be a face of the circle
rather than an input to it (it is PROVEN at the foot of this file); see the
ROUTE section on
`End.exists_trace_charPoly_degree_sub`, and the audits kept on the `deg = det`
theorem for the Weil-pairing half of the picture and the greps that would refute
them.

**A correction to an earlier note that is still worth keeping.** A previous
version said `Isogeny.degree_comp` wants the same input. It does not, and it is
PROVEN: multiplicativity of the degree under composition is pure group theory
(`Isogeny.card_ker_comp`, from `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ`) and needs nothing
about quadratic forms. -/

/-! ### The mod-`ℓ` torsion representation, and the determinant as a quadratic form -/

/-- **The determinant is a quadratic form in rank two**, over an arbitrary
commutative ring:

    det (f + g) + det (f − g) = 2 det f + 2 det g.

This is the whole "formal" half of the parallelogram law: transported through a
basis, `LinearMap.det` becomes `Matrix.det` of a `2 × 2` matrix
(`LinearMap.det_toMatrix`), `LinearMap.toMatrix` is additive, `Matrix.det_fin_two`
turns the two determinants into `a d − b c`, and `ring` closes it.

Stated for an arbitrary `R`-module with a `Fin 2`-basis rather than for
`Matrix (Fin 2) (Fin 2) R`, because the consumer's module — the `ℓ`-torsion — is
not literally a matrix algebra and its basis is not canonical. Nothing about
curves enters. -/
theorem det_add_add_det_sub {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (f g : Module.End R M) :
    LinearMap.det (f + g) + LinearMap.det (f - g)
      = 2 * LinearMap.det f + 2 * LinearMap.det g := by
  have h : ∀ h : Module.End R M, LinearMap.det h = Matrix.det (LinearMap.toMatrix b b h) :=
    fun h => (LinearMap.det_toMatrix b h).symm
  rw [h (f + g), h (f - g), h f, h g, map_add, map_sub]
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply]
  ring

/-- **`ρ_n : End W → End_{ZMod n}(W[n])`, the mod-`n` torsion representation**, as a
ring homomorphism.

An element of `End W` is in particular an additive endomorphism of `W.Point`, so it
restricts to the `n`-torsion (`TorsionCounting.endRestrict`), and an additive map
between `n`-torsion modules is automatically `ZMod n`-linear
(`AddMonoidHom.toZModLinearMap`). Both operations are transparent enough that all
four `RingHom` fields are `rfl` after `ext` — in particular `map_mul'` is `rfl`
because multiplication in `End W` is composition (`End.mul_apply`) and so is
multiplication in `Module.End`.

This is the object the parallelogram law is proved over, and it is the natural home
for anything else that wants `End W` as matrices: `det ∘ ρ_ℓ` is the degree mod `ℓ`
(the leaf below), and `trace ∘ ρ_ℓ` is then the trace of `End.self_add_dualEnd` mod
`ℓ`, which is what a Hasse-bound or Lefschetz-fixed-point consumer needs. It is
deliberately stated at every `n`, not only at primes; only the *basis* below needs
`n` prime. -/
noncomputable def End.torsionRep [IsAlgClosed F] (V : Affine F) [V.IsElliptic] (n : ℕ) :
    End V →+* Module.End (ZMod n) (V.nTorsion n) where
  toFun f := AddMonoidHom.toZModLinearMap n
    (TorsionCounting.endRestrict ((f : AddMonoid.End V.Point) : V.Point →+ V.Point) (n : ℤ))
  map_one' := by ext P; rfl
  map_mul' f g := by ext P; rfl
  map_zero' := by ext P; rfl
  map_add' f g := by ext P; rfl

/-- The `ℓ`-torsion is `2`-dimensional over `ZMod ℓ`, in `finrank` rather than
`rank` form. `WeierstrassCurve.p_torsion_rank` (`Torsion.lean`, PROVEN) gives the
`Module.rank`; `[CharZero F]` is what discharges its hypothesis `(ℓ : F) ≠ 0`. -/
theorem finrank_nTorsion [IsAlgClosed F] [CharZero F] (V : Affine F) [V.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Module.finrank (ZMod ℓ) (V.nTorsion ℓ) = 2 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact Module.finrank_eq_of_rank_eq (by
    rw [WeierstrassCurve.p_torsion_rank (E := V)
      (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)]
    norm_num)

/-- A basis of the `ℓ`-torsion over `ZMod ℓ`, for `ℓ` prime.

`ℓ` must be PRIME rather than a general modulus: `Module.finBasisOfFinrankEq` needs
the scalars to be a division ring, and it is the basis that turns `LinearMap.det`
into the explicit `Matrix.det_fin_two` polynomial in `det_add_add_det_sub`. Nothing
is lost, because the conclusion of the parallelogram law is an identity between
integers and so may be tested modulo arbitrarily large primes. -/
noncomputable def nTorsionBasis [IsAlgClosed F] [CharZero F] (V : Affine F) [V.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] : Module.Basis (Fin 2) (ZMod ℓ) (V.nTorsion ℓ) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  Module.finBasisOfFinrankEq (ZMod ℓ) (V.nTorsion ℓ) (finrank_nTorsion V ℓ)

/-- **The vanishing half of `deg = det`, PROVEN (2026-07-27, fourth pass).** If
`ℓ ∣ deg ψ` then `det (ρ_ℓ ψ) = 0`; since `deg ψ ≡ 0 (mod ℓ)` too, the leaf below
holds outright at every such `ℓ`, which is why that leaf carries the hypothesis
`¬ ℓ ∣ deg ψ`.

`ker (ρ_ℓ ψ) = ker ψ ∩ W[ℓ]`, so this is **Cauchy's theorem in the finite group
`ker ψ`**: a prime `ℓ` dividing `#ker ψ = deg ψ` produces an element of order
exactly `ℓ` (`exists_prime_addOrderOf_dvd_card`, against `IsIsogeny.finite_ker`),
i.e. a nonzero `ℓ`-torsion point killed by `ψ`, i.e. a nonzero vector in
`ker (ρ_ℓ ψ)`; over the field `ZMod ℓ` a nontrivial kernel is exactly a vanishing
determinant (`LinearMap.det_eq_zero_iff_ker_ne_bot`).

The zero endomorphism is separated out first, because `Isogeny.degree` is defined
by a case split at `0` and `IsIsogeny.finite_ker` needs a nonzero map; there
`ρ_ℓ ψ = 0` and the determinant of the zero endomorphism of a rank-`2` module is
`0` (`LinearMap.det_zero'` against `nTorsionBasis`).

This is exactly the half of the ROUTE AUDIT's "what IS cheaply available" that the
assembly consumes. The converse — `det (ρ_ℓ ψ) = 0 → ℓ ∣ deg ψ`, by Lagrange in
`ker ψ` applied to the order-`ℓ` point produced by a nontrivial kernel — is true by
the same dictionary and is deliberately **not** stated, because nothing consumes
it. -/
theorem End.det_torsionRep_eq_zero_of_dvd [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (ψ : End W)
    (hdvd : ℓ ∣ Isogeny.degree (End.toIsogeny ψ)) :
    LinearMap.det (End.torsionRep W ℓ ψ) = 0 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  by_cases h0 : (End.toIsogeny ψ).toHom = 0
  · -- the zero endomorphism: `ρ_ℓ 0 = 0`, and `det 0 = 0` in rank `2`
    have hψ : ψ = 0 := Subtype.ext h0
    rw [hψ, map_zero]
    exact LinearMap.det_zero' (nTorsionBasis W ℓ)
  · -- Cauchy in the finite group `ker ψ` produces a point of order exactly `ℓ`
    haveI hfin : Finite (AddMonoidHom.ker (End.toIsogeny ψ).toHom) :=
      Set.Finite.to_subtype ((End.toIsogeny ψ).isIsogeny.finite_ker h0)
    haveI : Fintype (AddMonoidHom.ker (End.toIsogeny ψ).toHom) := Fintype.ofFinite _
    have hcard : ℓ ∣ Fintype.card (AddMonoidHom.ker (End.toIsogeny ψ).toHom) := by
      rw [← Nat.card_eq_fintype_card, ← Isogeny.degree_of_ne_zero h0]
      exact hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card ℓ hcard
    have hxtor : ((ℓ : ℤ)) • ((x : W.Point)) = 0 := by
      have h1 : ℓ • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
      have h2 : ℓ • ((x : W.Point)) = 0 := by
        exact_mod_cast congrArg (Subtype.val) h1
      rw [← h2, natCast_zsmul]
    refine (LinearMap.det_eq_zero_iff_ker_ne_bot).2 ?_
    intro hker
    have hmem : ((x : W.Point)) ∈ Submodule.torsionBy ℤ W.Point (ℓ : ℤ) :=
      (Submodule.mem_torsionBy_iff _ _).2 hxtor
    set Q : W.nTorsion ℓ := ⟨(x : W.Point), hmem⟩ with hQ
    have hQker : End.torsionRep W ℓ ψ Q = 0 := by
      apply Subtype.ext
      show (ψ : AddMonoid.End W.Point) ((x : W.Point)) = 0
      exact x.2
    have hQ0 : Q = 0 := by
      have h : Q ∈ LinearMap.ker (End.torsionRep W ℓ ψ) := hQker
      rw [hker, Submodule.mem_bot] at h
      exact h
    have hxval : ((x : W.Point)) = 0 := congrArg Subtype.val hQ0
    have hx0 : x = 0 := Subtype.ext hxval
    rw [hx0, addOrderOf_zero] at hx
    exact (Fact.out : ℓ.Prime).ne_one hx.symm

/-- **`deg [c] = c²` — PROVEN (2026-07-28, sixth pass).** The degree of an integer.

`((c : ℤ) : End W)` acts as `c • ·` on points **definitionally**
(`End.intCast_apply` is `rfl`), so its kernel is the torsion subgroup `W[|c|]`, and
`WeierstrassCurve.n_torsion_card` counts that as `|c|² = c²`. The hypothesis
`(|c| : F) ≠ 0` of the count is discharged by `[CharZero F]`; `c = 0` is separated
out because `Isogeny.degree` is defined by a case split at the zero map.

This is the **"forgotten fifth fact"** of the audit on
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` below — the one whose omission
made that audit's original `q n := n⁴` counterexample invalid. It had a proof
sketch in three docstrings of this file and no name until now, which is why the
sketches kept having to re-derive it; `End.exists_trace_charPoly_degree_sub` below
is its first consumer, where it is what turns a linear relation `[a] χ = [b]` in
`End W` into an arithmetic one in `ℤ`. -/
theorem End.degree_intCast [IsAlgClosed F] [CharZero F] [W.IsElliptic] (c : ℤ) :
    (Isogeny.degree (End.toIsogeny (((c : ℤ)) : End W)) : ℤ) = c ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : (End.toIsogeny (((0 : ℤ)) : End W)).toHom = 0 := by
      ext P
      show ((((0 : ℤ)) : End W) : AddMonoid.End W.Point) P = 0
      rw [End.intCast_apply]
      simp
    rw [Isogeny.degree_of_eq_zero h0]
    norm_num
  · have h0 : (End.toIsogeny (((c : ℤ)) : End W)).toHom ≠ 0 := by
      intro hcon
      refine hc (End.intCast_injective (W := W) (a := c) (b := 0) ?_)
      rw [Int.cast_zero]
      exact Subtype.ext hcon
    rw [Isogeny.degree_of_ne_zero h0]
    have hnat : ((c.natAbs : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc)
    have hcard : Nat.card (W.nTorsion c.natAbs) = c.natAbs ^ 2 :=
      WeierstrassCurve.n_torsion_card (E := W) hnat
    have hiff : ∀ P : W.Point,
        P ∈ AddMonoidHom.ker (End.toIsogeny (((c : ℤ)) : End W)).toHom
          ↔ P ∈ Submodule.torsionBy ℤ W.Point ((c.natAbs : ℕ) : ℤ) := by
      intro P
      rw [AddMonoidHom.mem_ker, Submodule.mem_torsionBy_iff]
      show ((((c : ℤ)) : End W) : AddMonoid.End W.Point) P = 0 ↔ _
      rw [End.intCast_apply]
      rcases Int.natAbs_eq c with he | he
      · nth_rewrite 1 [he]
        rfl
      · nth_rewrite 1 [he]
        rw [neg_smul, neg_eq_zero]
    have hEq : Nat.card (AddMonoidHom.ker (End.toIsogeny (((c : ℤ)) : End W)).toHom)
        = Nat.card (W.nTorsion c.natAbs) :=
      Nat.card_congr (Equiv.subtypeEquivRight hiff)
    rw [hEq, hcard]
    push_cast
    rw [sq_abs]

/-- **The degree is multiplicative on `End W`.** `Isogeny.degree_comp` (PROVEN in
`Isogeny.lean`, pure group theory) transported across `End.toIsogeny`, which carries
multiplication in `End W` — composition — to `Isogeny.comp` definitionally.

Stated in `ℤ` because every consumer of it here is solving an integer equation. It
was an anonymous `have` inside `End.self_add_dualEnd` below; naming it is what lets
`End.exists_trace_charPoly_degree_sub` use `End W` as a domain. -/
theorem End.degree_mul [IsAlgClosed F] [W.IsElliptic] (a c : End W) :
    (Isogeny.degree (End.toIsogeny (a * c)) : ℤ)
      = (Isogeny.degree (End.toIsogeny a) : ℤ) * (Isogeny.degree (End.toIsogeny c) : ℤ) := by
  have hc : End.toIsogeny (a * c) = (End.toIsogeny a).comp (End.toIsogeny c) :=
    Isogeny.ext (fun _ => rfl)
  rw [hc, Isogeny.degree_comp]
  push_cast
  ring

/-! ### Rank-two linear algebra for the `ℓ`-torsion

Everything from here to the end of the file is an algebraic consequence of the two
route-2 leaves stated in the ROUTE 2 section below. The audits on
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` further down record *why* a
geometric input is unavoidable — in particular the `ℤ[√2]`, `q := |N|` model,
which satisfies multiplicativity, definiteness and `q m = m²` and still violates
everything in this circle.

Three facts about alternating forms on a rank-`2` space live here, and they are what
make the Weil pairing at the foot of this file a theorem rather than an input:
`altPairing_map_eq_det_smul` (`f` scales the form by `det f`),
`det_eq_of_altPairing_conj` (its converse, cancelling the scalar) and
`altPairing_trace` (`f` and `tr f − f` are adjoint). -/

section AltPairing

variable {R : Type*} [Field R] {V : Type*} [AddCommGroup V] [Module R V]

set_option backward.isDefEq.respectTransparency false in
/-- On a rank-`2` space an alternating bilinear form transforms under any
endomorphism by the determinant: `e (f x) (f y) = det f · e x y`.

Pure linear algebra: expand `x` and `y` in a basis, where alternation collapses
`e` to a multiple of the `2 × 2` determinant form.

**Deliberately duplicated, not imported.** This is `WeilPairing.pairing_map_eq_det_smul`
(`Fermat/FLT/EllipticCurve/WeilPairing.lean`, PROVEN) restated with the rank
hypothesis in the same form. `WeilPairing.lean` is a 15k-line module whose import
cone includes `Chebotarev`; importing it here would push that cone onto
`MazurTorsion.lean` and `ModThree.lean`, the two consumers of this file, to reuse
fifty lines of `Matrix.det_fin_two`. If a common home is ever wanted, the right one
is a small `Fermat/FLT/Mathlib/` shim that both import — not an edge between these
two modules. -/
theorem altPairing_map_eq_det_smul (hrank : Module.rank R V = 2)
    (e : V →ₗ[R] V →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (f : V →ₗ[R] V) (x y : V) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite R V :=
    Module.finite_of_rank_eq_nat (by exact_mod_cast hrank)
  have hfr : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  let b : Module.Basis (Fin 2) R V := Module.finBasisOfFinrankEq R V hfr
  have hskew : ∀ v w : V, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add,
      add_zero] at h
    linear_combination h
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ f f = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : V →ₗ[R] V →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- An endomorphism that scales a **nonzero** alternating form on a rank-`2` space
by `c` has determinant `c`. The nondegeneracy hypothesis is used only to cancel one
nonzero scalar, which is why the weak form `∃ x y, e x y ≠ 0` suffices. -/
theorem det_eq_of_altPairing_conj (hrank : Module.rank R V = 2)
    (e : V →ₗ[R] V →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (hnd : ∃ x y, e x y ≠ 0)
    {f : V →ₗ[R] V} {c : R} (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h1 := altPairing_map_eq_det_smul hrank e halt f x y
  exact mul_right_cancel₀ hxy (h1.symm.trans (hc x y))

set_option backward.isDefEq.respectTransparency false in
/-- **The ADJUGATE identity for an alternating form in rank two**, and the reason
`exists_weilPairing_torsionRep_adjoint` below is not an input at all:

    e (f x) y + e x (f y) = (det (f + 1) − det f − 1) · e x y.

The bracket is the trace (`det (f + 1) = det f + tr f + 1` in rank two), so this
says that `f` and `tr f − f` — the classical adjugate of a `2 × 2` matrix — are
**adjoint** for any alternating form. Combined with the trace formula
`ψ + ψ̂ = [t]` and `deg = det`, which together identify `ρ_ℓ ψ̂` with `tr (ρ_ℓ ψ) − ρ_ℓ ψ`,
it produces Weil-pairing adjointness out of nothing geometric; see
`exists_weilPairing_torsionRep_adjoint` at the foot of this file.

Companion to `altPairing_map_eq_det_smul` above and proved the same way: the
identity is bilinear in `(x, y)`, so it is enough to check it on a basis, where
alternation kills the diagonal entries and leaves `M 0 0 + M 1 1`. Only a
`Fin 2`-basis is needed, not the `Module.rank` form of the hypothesis. -/
theorem altPairing_trace (b : Module.Basis (Fin 2) R V)
    (e : V →ₗ[R] V →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (f : V →ₗ[R] V) (x y : V) :
    e (f x) y + e x (f y)
      = (LinearMap.det (f + 1) - LinearMap.det f - 1) * e x y := by
  classical
  have hskew : ∀ v w : V, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add,
      add_zero] at h
    linear_combination h
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have htr : LinearMap.det (f + 1) - LinearMap.det f - 1
      = LinearMap.toMatrix b b f 0 0 + LinearMap.toMatrix b b f 1 1 := by
    have hd : LinearMap.det f
        = LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1
          - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
      rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
    have hd1 : LinearMap.det (f + 1)
        = (LinearMap.toMatrix b b f 0 0 + 1) * (LinearMap.toMatrix b b f 1 1 + 1)
          - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
      rw [← LinearMap.det_toMatrix b (f + 1), Matrix.det_fin_two]
      simp [map_add, LinearMap.toMatrix_one]
    rw [hd, hd1]; ring
  suffices hb : ∀ i j, e (f (b i)) (b j) + e (b i) (f (b j))
      = (LinearMap.det (f + 1) - LinearMap.det f - 1) * e (b i) (b j) by
    have hBB : e.comp f + e.compl₂ f
        = (LinearMap.det (f + 1) - LinearMap.det f - 1) • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : V →ₗ[R] V →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, htr, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

end AltPairing

/-- **Cayley–Hamilton on a rank-`2` module, in trace-free form.**

    f² + [det f] = [det (f + 1) − det f − 1] · f.

For a `2 × 2` matrix `det (A + 1) = det A + tr A + 1`, so the bracket on the right
**is** the trace; writing it as a difference of determinants avoids introducing
`Matrix.trace` and — more to the point — makes the statement match the shape of
`End.exists_trace_charPoly` below term for term, with `det` in the slot where the
degree will go. The proof transports along `LinearMap.toMatrix b b` and is
`Matrix.det_fin_two` plus `ring`. -/
theorem det_charPoly_rank_two {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (f : Module.End R M) :
    f * f + (LinearMap.det f) • (1 : Module.End R M)
      = (LinearMap.det (f + 1) - LinearMap.det f - 1) • f := by
  have hd : LinearMap.det f
      = LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1
        - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  have hd1 : LinearMap.det (f + 1)
      = (LinearMap.toMatrix b b f 0 0 + 1) * (LinearMap.toMatrix b b f 1 1 + 1)
        - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b (f + 1), Matrix.det_fin_two]
    simp [map_add, LinearMap.toMatrix_one]
  rw [hd, hd1]
  apply (LinearMap.toMatrix b b).injective
  simp only [map_add, map_smul, LinearMap.toMatrix_mul, LinearMap.toMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.add_apply] <;> ring

/-- **Cayley–Hamilton for a multiplicative parallelogram form**, and the reason the
trace formula is not a second leaf.

Let `R` be a ring and `q : R → ℤ` satisfy

* `q 0 = 0`, `q 1 = 1`;
* the **parallelogram law** `q (a+c) + q (a−c) = 2 q a + 2 q c`;
* **multiplicativity** `q (a c) = q a · q c`;
* **positive definiteness in the weak form** `q a = 0 → a = 0`.

Then every `x : R` satisfies its characteristic polynomial

    x² + [q x] = [q (x+1) − q x − 1] · x.

This is the classical composition-algebra argument, and it is what refutes the
first pass's "the parallelogram law alone does not suffice". Writing
`b u v := q (u+v) − q u − q v` for the polar form:

1. the parallelogram law makes `b` **biadditive** (polarisation: `q (u+v+w)` has
   the symmetric three-variable expansion, whence `b (u+v) w = b u w + b v w`, and
   `b` is symmetric by `add_comm`);
2. linearising `q (u (v+w)) = q u · q (v+w)` in the second slot gives
   `b (u v) (u w) = q u · b v w`;
3. linearising *that* in `u` gives the four-term identity
   `b (u v) (w z) + b (w v) (u z) = b u w · b v z`;
4. specialising (3) at `w = 1, v := u, z := v` and (2) at `v = 1` gives
   `b (x²) v = b x 1 · b x v − q x · b 1 v`, so the element
   `u := x² − [b x 1] x + [q x]` satisfies `b u v = 0` for **every** `v`;
5. taking `v = u` and using `b a a = 2 q a` (parallelogram at `a, a`) gives
   `q u = 0`, hence `u = 0`.

Only step 5 uses definiteness, and only steps 2–3 use multiplicativity — which is
exactly the hypothesis the first pass's independence analysis did not have in view.

**Stated `End`-free on purpose** — for readability, and because the statement is
about any ring with a multiplicative parallelogram form, not about curves. This one
reports `[propext, Classical.choice, Quot.sound]`. (An earlier version justified the
`End`-free phrasing by the claim that everything mentioning `End W` reports
`sorryAx` at carrier level. That justification is RETIRED and was stale; see the
retraction on `not_isRationalMap_leftInverse_frob` above.) -/
theorem charPoly_of_multiplicative_parallelogram {R : Type*} [Ring R] (q : R → ℤ)
    (hq0 : q 0 = 0) (hq1 : q 1 = 1)
    (hpar : ∀ a c : R, q (a + c) + q (a - c) = 2 * q a + 2 * q c)
    (hmul : ∀ a c : R, q (a * c) = q a * q c)
    (hzero : ∀ a : R, q a = 0 → a = 0) (x : R) :
    x * x + ((q x : ℤ) : R) = ((q (x + 1) - q x - 1 : ℤ) : R) * x := by
  obtain ⟨b, hbv⟩ : ∃ b : R → R → ℤ, ∀ u v : R, b u v = q (u + v) - q u - q v :=
    ⟨_, fun _ _ => rfl⟩
  -- `q` is even.
  have hneg : ∀ a : R, q (-a) = q a := by
    intro a
    have h := hpar 0 a
    rw [zero_add, zero_sub, hq0] at h
    linarith
  -- the symmetric three-variable polarisation identity
  have hthree : ∀ u v w : R,
      q (u + v + w) = q (u + v) + q (v + w) + q (u + w) - q u - q v - q w := by
    intro u v w
    have h3 := hpar (u + w) v
    have h5 := hpar u v
    have h7 := hpar (v + w) u
    have h2 := hpar (u - v) w
    have e3a : u + w + v = u + v + w := by abel
    have e3b : u + w - v = u - v + w := by abel
    have e7a : v + w + u = u + v + w := by abel
    have e7b : v + w - u = -(u - v - w) := by abel
    rw [e3a, e3b] at h3
    rw [e7a, e7b, hneg] at h7
    linarith
  -- the polar form is biadditive
  have hbaddl : ∀ u v w : R, b (u + v) w = b u w + b v w := by
    intro u v w
    rw [hbv, hbv, hbv, hthree]
    ring
  have hbsymm : ∀ u v : R, b u v = b v u := by
    intro u v
    rw [hbv, hbv, add_comm u v]; ring
  have hbaddr : ∀ u v w : R, b u (v + w) = b u v + b u w := by
    intro u v w
    rw [hbsymm u (v + w), hbaddl, hbsymm v u, hbsymm w u]
  have hb0 : ∀ v : R, b 0 v = 0 := by
    intro v; rw [hbv, zero_add, hq0]; ring
  have hbnegl : ∀ a v : R, b (-a) v = -b a v := by
    intro a v
    have h := hbaddl a (-a) v
    rw [add_neg_cancel, hb0] at h
    linarith
  have hbsubl : ∀ a c v : R, b (a - c) v = b a v - b c v := by
    intro a c v
    rw [sub_eq_add_neg, hbaddl, hbnegl]; ring
  have hhom : ∀ (n : ℤ) (a v : R), b (n • a) v = n * b a v := by
    intro n a v
    let f : R →+ ℤ := AddMonoidHom.mk' (fun u : R => b u v) (fun p r => hbaddl p r v)
    have hf : ∀ u : R, f u = b u v := fun _ => rfl
    have h := map_zsmul f n a
    rw [hf, hf] at h
    simpa [zsmul_eq_mul] using h
  -- first linearisation of multiplicativity
  have hE1 : ∀ u v w : R, b (u * v) (u * w) = q u * b v w := by
    intro u v w
    have h := hmul u (v + w)
    rw [mul_add] at h
    rw [hbv, hbv, h, hmul, hmul]
    ring
  -- second linearisation
  have hE2 : ∀ u w v z : R, b (u * v) (w * z) + b (w * v) (u * z) = b u w * b v z := by
    intro u w v z
    have h := hE1 (u + w) v z
    have hq : q (u + w) = b u w + q u + q w := by rw [hbv]; ring
    rw [add_mul, add_mul, hbaddl, hbaddr, hbaddr, hE1 u v z, hE1 w v z, hq] at h
    linear_combination h
  -- the key identity for `b (x * x) ·`
  have hE3 : ∀ u v : R, b (u * u) v = b u 1 * b u v - q u * b 1 v := by
    intro u v
    have h := hE2 u 1 u v
    rw [one_mul, one_mul] at h
    have h2 := hE1 u 1 v
    rw [mul_one] at h2
    linarith
  -- the candidate is `b`-orthogonal to everything
  have hkey : ∀ v : R,
      b (x * x - ((b x 1 : ℤ) : R) * x + ((q x : ℤ) : R)) v = 0 := by
    intro v
    have htx : b (((b x 1 : ℤ) : R) * x) v = b x 1 * b x v := by
      rw [← zsmul_eq_mul]; exact hhom (b x 1) x v
    have hqx : b (((q x : ℤ) : R)) v = q x * b 1 v := by
      have hc : ((q x : ℤ) : R) = (q x) • (1 : R) := by rw [zsmul_eq_mul, mul_one]
      rw [hc]; exact hhom (q x) 1 v
    rw [hbaddl, hbsubl, hE3 x v, htx, hqx]
    ring
  -- hence it is `0`
  have hdiag : ∀ a : R, b a a = 2 * q a := by
    intro a
    have hp := hpar a a
    rw [sub_self, hq0] at hp
    rw [hbv]
    linarith
  have hzeroU : x * x - ((b x 1 : ℤ) : R) * x + ((q x : ℤ) : R) = 0 := by
    refine hzero _ ?_
    have h := hkey (x * x - ((b x 1 : ℤ) : R) * x + ((q x : ℤ) : R))
    rw [hdiag] at h
    linarith
  have hbx1 : b x 1 = q (x + 1) - q x - 1 := by rw [hbv, hq1]
  rw [← hbx1]
  have h : x * x + ((q x : ℤ) : R) - ((b x 1 : ℤ) : R) * x = 0 := by
    rw [← hzeroU]; abel
  exact sub_eq_zero.mp h

/-! ### ROUTE 2 (2026-07-30, eighth pass): the elementary `x`-coordinate degree count

**The seventh pass's leaf was inside the circle after all, and this pass proves it.**
`exists_weilPairing_torsionRep_adjoint` — "there is an alternating nondegenerate
pairing on `W[ℓ]` for which every `ψ` and its dual are adjoint" — was introduced as
the first statement in this file's sequence of leaves that "is *not* a statement
about degrees at all", hence "a reduction rather than the eighth lap of the circle".
That claim is **refuted, machine-checked**: the theorem now stands at the foot of
this file, PROVEN, with no geometric input beyond what the circle already contains.
The three lines of it are

* build `e` as the coordinate determinant form in `nTorsionBasis W ℓ` — alternation
  and nondegeneracy are then `ring` and `Finsupp.single_apply`, exactly as in
  `WeilPairing.exists_weilPairing`;
* `altPairing_trace` above: for **any** alternating form on a rank-`2` space, `f` and
  `tr f − f` (the `2 × 2` adjugate) are adjoint;
* `End.self_add_dualEnd` gives `ρ_ℓ ψ̂ = [t] − ρ_ℓ ψ` and
  `End.natCast_degree_eq_det_torsionRep` gives `t ≡ tr (ρ_ℓ ψ)`, which is exactly
  the substitution the previous item needs.

So the pairing face is interderivable with `deg = det` like every other face, and
the audit's rigidity observation — on a rank-`2` space an alternating form is unique
up to a scalar — is precisely *why*: it forces the pairing to carry no information
beyond the determinant, in **both** directions, not only the one the audit used.
Nothing is lost by knowing this; what it removes is the belief that a
characteristic-zero divisor-theoretic construction (redoing
`WeilPairingStageB.lean`'s genericity layer over a char-`0` base, then adding
isogeny naturality on divisors) is on the critical path. It is not.

**The genuinely non-circular input is route 2**, recorded but never stated in the
seventh pass's ROUTE AUDIT (see `End.exists_trace_charPoly_degree_sub` below, which
still holds and is not retracted): for a nonzero `φ` with `x ∘ φ = A/B` in lowest
terms, `deg φ = max (deg A) (deg B)`, and the `x`-only addition law turns the
parallelogram law into a count of polynomial degrees. It needs no divisors, no Weil
pairing and no function fields — only the `IsRationalMap` normal form that
`Isogeny.lean` already carries (`homogSubst`,
`natDegree_eq_zero_of_coprime_homogSubst`, `exists_const_of_homogSubst_eq_zero`).
Its two sub-steps are now the file's two leaves, `End.exists_isXNormalForm_degree`
and `End.isXNormalForm_natDegree_parallelogram`, and everything else in the trace
layer — including the Weil pairing itself — is PROVEN over them.

**Why the count is not a lap of the circle.** The circle consists of identities
between `Isogeny.degree`s of endomorphisms; the ROUTE AUDIT proves it cannot be
broken from inside, because every kernel-cardinality invariant sees only the
`ℓ`-adic valuation of `deg`. Leaf (A) leaves that language: it equates a kernel
cardinality with a **polynomial degree**, which is not a kernel invariant, and it is
where the geometry (separability of `A − tB` over `F(t)`, in characteristic zero)
actually enters. Leaf (B) is then a statement about `F[X]` alone.
-/

/-- `deg 0 = 0`, in the `End W` spelling. `Isogeny.degree` is defined by a case
split at the zero map, and `End.toIsogeny 0` is that map by `rfl`. -/
theorem End.degree_toIsogeny_zero [IsAlgClosed F] [W.IsElliptic] :
    Isogeny.degree (End.toIsogeny (0 : End W)) = 0 := by
  have hz : End.toIsogeny (0 : End W) = Isogeny.zero := rfl
  rw [hz, Isogeny.degree_zero]

/-- `deg (−χ) = deg χ`. Multiplicativity against `deg [−1] = (−1)² = 1`; the kernel
of `−χ` is literally the kernel of `χ`, but this route needs no new lemma. -/
theorem End.degree_neg [IsAlgClosed F] [CharZero F] [W.IsElliptic] (χ : End W) :
    Isogeny.degree (End.toIsogeny (-χ)) = Isogeny.degree (End.toIsogeny χ) := by
  have h : (-χ : End W) = (((-1 : ℤ)) : End W) * χ := by
    rw [Int.cast_neg, Int.cast_one, neg_one_mul]
  have hm := End.degree_mul (((-1 : ℤ)) : End W) χ
  rw [← h, End.degree_intCast] at hm
  have hz : ((Isogeny.degree (End.toIsogeny (-χ)) : ℤ))
      = ((Isogeny.degree (End.toIsogeny χ) : ℤ)) := by rw [hm]; ring
  exact_mod_cast hz

/-- `deg (χ + χ) = 4 · deg χ`. Multiplicativity against `deg [2] = 4`. This is the
degenerate case of the parallelogram law at `φ = ψ`, and is what discharges the two
diagonal cases of it below without any appeal to the leaves. -/
theorem End.degree_add_self [IsAlgClosed F] [CharZero F] [W.IsElliptic] (χ : End W) :
    Isogeny.degree (End.toIsogeny (χ + χ)) = 4 * Isogeny.degree (End.toIsogeny χ) := by
  have h : (χ + χ : End W) = (((2 : ℤ)) : End W) * χ := by
    push_cast; rw [two_mul]
  have hm := End.degree_mul (((2 : ℤ)) : End W) χ
  rw [← h, End.degree_intCast] at hm
  have hz : ((Isogeny.degree (End.toIsogeny (χ + χ)) : ℤ))
      = 4 * ((Isogeny.degree (End.toIsogeny χ) : ℤ)) := by rw [hm]; ring
  exact_mod_cast hz

/-- **The reduced `x`-coordinate normal form of an endomorphism.**
`IsXNormalForm φ A B` says that `(A, B)` is a **coprime** pair of polynomials with
`x (φ P) = A (x P) / B (x P)` at every point where `φ P ≠ 0`, written
multiplicatively so that no division is needed — that is, the `A, B` half of
`IsRationalMap` (`Isogeny.lean`) with `IsCoprime A B` added.

The `y`-witness of `IsRationalMap` is deliberately dropped: route 2 counts degrees
of the `x`-coordinate map only.

**Coprimality makes the pair unique up to a unit**, which is what makes
`max A.natDegree B.natDegree` a well-defined invariant of `φ` and hence makes leaf
(B) below a statement rather than a family of statements. The argument: `ker φ` is
finite (`IsIsogeny.finite_ker`) and `W.Point` is infinite (`infinite_point`), so the
certificate holds at infinitely many points; two pairs `(A, B)`, `(A₀, B₀)`
satisfying it give `A B₀ = A₀ B` at infinitely many `x`-values, hence as
polynomials, and coprimality then forces `(A, B) = c · (A₀, B₀)`.

**Note the certificate is stated at EVERY point with `φ P ≠ 0`, with no
nonvanishing hypothesis on `B`, and that is not an oversight.** For a coprime pair
it is automatic: if `B (x P) = 0` then the certificate forces `A (x P) = 0`,
contradicting coprimality — so `B` cannot vanish at the abscissa of any point
outside `ker φ`. Geometrically, `B`'s roots are exactly the abscissae of `ker φ`,
where `x ∘ φ` has its poles. -/
def End.IsXNormalForm [IsAlgClosed F] [W.IsElliptic] (φ : End W) (A B : F[X]) : Prop :=
  IsCoprime A B ∧ B ≠ 0 ∧
    ∀ P : W.Point, (φ : AddMonoid.End W.Point) P ≠ 0 →
      veluPointX ((φ : AddMonoid.End W.Point) P) * B.eval (veluPointX P)
        = A.eval (veluPointX P)

/-- **LEAF (A) (2026-07-30, eighth pass) — the degree is the degree of the
`x`-coordinate map.** Silverman *AEC* II.2.4.1 together with III.4.10, or Washington
*Elliptic Curves* §2.9: for a nonzero `φ ∈ End W`, writing `x ∘ φ = A / B` in lowest
terms,

    deg φ = max (deg A) (deg B).

### ROUTE

`IsRationalMap` (inside `IsIsogeny`, so carried by every element of `End W`) already
supplies **some** pair `(A₀, B₀)` with `B₀ ≠ 0` satisfying the certificate; dividing
by `gcd (A₀, B₀)` gives the coprime pair. The certificate survives the division at
every abscissa where the gcd does not vanish, which is a cofinite set; at the
finitely many remaining abscissae it is recovered from the coprime pair itself, as
the docstring on `End.IsXNormalForm` explains (if the reduced denominator vanishes
the point is in `ker φ`, and the hypothesis `φ P ≠ 0` is vacuous there).

The degree equality is the fibre count. `x : W.Point → F` is `2 : 1` off the
`2`-torsion, and `φ` is `#ker φ : 1` (its fibres are the cosets of `ker φ`,
`IsIsogeny.surjective` giving surjectivity); so for all but finitely many `t : F`
the set `{P | A (x P) = t · B (x P)}` has `2 · deg φ` elements, while it is the
preimage under `x` of the root set of `A − C t · B`, which has `2 · max (deg A)
(deg B)` elements once `A − C t · B` is separable of full degree. Separability for
generic `t` is where **characteristic zero** enters, and it is the only place: over
`F(t)` the polynomial `A − t B` is separable because `F(t)` is perfect and
`A − t B` is not a `p`-th power, `p = char F` being `0`.

### FAITHFULNESS AUDIT (2026-07-30)

*Not vacuous.* `IsXNormalForm` is inhabited for every nonzero `φ` — that is the
first half of the route, and `IsRationalMap` is what makes it so. For `φ = 1` the
pair is `(X, 1)` and `max = 1 = deg 1`; for `φ = [n]` it is `(Φₙ, ΨSqₙ)` with
degrees `n²` and `n² − 1`, and `max = n² = deg [n]` (`End.degree_intCast`).

*The nonzero hypothesis is load-bearing.* At `φ = 0` the certificate is vacuous, so
**every** coprime pair satisfies `IsXNormalForm 0 A B` while `deg 0 = 0`; the
conclusion would be refuted by `(X, 1)`.

*`max` and not `+`, and `natDegree` and not `degree`.* `natDegree` of a nonzero
constant is `0`, so `(X, 1)` has `max = 1`: correct. Using `A.natDegree +
B.natDegree` would give `1` here too but `2 n² − 1` at `[n]`, which is wrong.

*Characteristic zero is required as stated.* Over `𝔽̄_p` the Frobenius has `deg = 1`
in this file's sense (`Isogeny.degree` counts kernel *points*,
`Isogeny.NotIsRationalMapDualHom.frobIsog_degree`) while `x ∘ frob = X^p / 1` has
`max = p`. So the leaf is FALSE without `[CharZero F]`, by the same defect that
`Isogeny.isRationalMap_dualHom`'s audit records — and for the same reason:
`Isogeny.degree` is the separable degree.

*It is not a lap of the circle.* Every statement in the circle equates two
`Isogeny.degree`s; this one equates a `Isogeny.degree` with a polynomial degree.
The ROUTE AUDIT on `End.exists_trace_charPoly_degree_sub` shows the circle cannot be
broken by kernel-cardinality arguments, and this leaf is exactly the step that
leaves that language. -/
theorem End.exists_isXNormalForm_degree [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    {φ : End W} (hφ : φ ≠ 0) :
    ∃ A B : F[X], End.IsXNormalForm φ A B ∧
      Isogeny.degree (End.toIsogeny φ) = max A.natDegree B.natDegree :=
  sorry

/-- **LEAF (B) (2026-07-30, eighth pass) — the `x`-degree is a quadratic form**, by
the `x`-only addition law and a coprimality count. Washington *Elliptic Curves*,
§9.? (the proof of the parallelogram law that uses no divisors); Silverman *AEC*
III.6.3 is the same identity by the Weil-pairing route.

    max(deg A₁, deg B₁) + max(deg A₂, deg B₂)
        = 2 max(deg A, deg B) + 2 max(deg C, deg D)

for reduced `x`-normal forms `(A, B)` of `φ`, `(C, D)` of `ψ`, `(A₁, B₁)` of
`φ + ψ` and `(A₂, B₂)` of `φ − ψ`.

### ROUTE

Everything is polynomial algebra in `F[X]` once the addition law is written down.
With `u := x ((φ + ψ) P)` and `v := x ((φ − ψ) P)`, the `x`-only addition law gives

    u + v  and  u · v   as rational functions of  x (φ P)  and  x (ψ P)

of bidegree `(2, 2)`. Substituting `x (φ P) = A/B` and `x (ψ P) = C/D` and writing
`S := A D + C B`, `P := A C`, `Q := B D`, the common denominator is
`S² − 4 P Q = (A D − C B)²`, so

    u + v = N₁ / (A D − C B)²,    u · v = N₂ / (A D − C B)²

with `N₁, N₂` of degree at most `2 (max(deg A, deg B) + max(deg C, deg D))`. On the
other side `u + v = (A₁ B₂ + A₂ B₁)/(B₁ B₂)` and `u v = A₁ A₂/(B₁ B₂)`. The content
is the **coprimality count**: `gcd (A₁ B₂ + A₂ B₁, A₁ A₂, B₁ B₂) = 1`, which makes
the two presentations agree up to a unit and turns the degree bookkeeping into the
stated identity.

### FAITHFULNESS AUDIT (2026-07-30)

*All four nonvanishing hypotheses are load-bearing.* At `φ = 0` every coprime pair
is an `x`-normal form (the certificate is vacuous), so the identity is refuted by
taking `(A, B) := (X, 1)`; the same at `ψ = 0`, `φ + ψ = 0` and `φ − ψ = 0`. The
degenerate cases are **not** lost: they are discharged outright in
`End.degree_add_add_degree_sub` below from `End.degree_neg` and
`End.degree_add_self`, which are multiplicativity of the degree against
`deg [±1] = 1` and `deg [2] = 4`.

*Well-posed.* `max A.natDegree B.natDegree` depends only on `φ`, because a reduced
pair is unique up to a unit; see the docstring on `End.IsXNormalForm` for the
argument. So the universally quantified pairs cannot be chosen adversarially.

*Not vacuous.* Leaf (A) inhabits every hypothesis, which is exactly how
`End.degree_add_add_degree_sub` below consumes the two together.

*Sanity check.* `W : y² = x³ − x` with CM by `ℤ[i]`, `φ := 1`, `ψ := i`. Normal
forms `(X, 1)` and `(−X, 1)`, both of `max = 1`; `1 ± i` have norm `2`, and their
`x`-maps have `max = 2`. The identity reads `2 + 2 = 2 · 1 + 2 · 1`. A second check
inside `ℤ ⊆ End W`, where every term is computable from `End.degree_intCast` alone:
`φ := 1`, `ψ := [2]` gives `φ + ψ = [3]` and `φ − ψ = [−1]`, so
`9 + 1 = 2 · 1 + 2 · 4`. Both hold.

*The statement is about `F[X]` only.* No `Isogeny.degree` occurs in it. That is the
point of the cut: this half of route 2 can be attacked with no elliptic-curve
geometry at all, once the addition law is available. -/
theorem End.isXNormalForm_natDegree_parallelogram [IsAlgClosed F] [CharZero F]
    [W.IsElliptic] {φ ψ : End W} (hφ : φ ≠ 0) (hψ : ψ ≠ 0)
    (hadd : φ + ψ ≠ 0) (hsub : φ - ψ ≠ 0)
    {A B C D A₁ B₁ A₂ B₂ : F[X]}
    (hf : End.IsXNormalForm φ A B) (hg : End.IsXNormalForm ψ C D)
    (h₁ : End.IsXNormalForm (φ + ψ) A₁ B₁) (h₂ : End.IsXNormalForm (φ - ψ) A₂ B₂) :
    max A₁.natDegree B₁.natDegree + max A₂.natDegree B₂.natDegree
      = 2 * max A.natDegree B.natDegree + 2 * max C.natDegree D.natDegree :=
  sorry

/-- **The parallelogram law for the degree — PROVEN (2026-07-30, eighth pass)** over
the two route-2 leaves above. Silverman *AEC* III.6.3: the degree is a quadratic
form on `End W`.

    deg (φ + ψ) + deg (φ − ψ) = 2 deg φ + 2 deg ψ.

Stated in `ℕ` because `Isogeny.degree` is `Nat.card (ker ·)`; every term is a
cardinality.

**The proof.** Four applications of leaf (A) turn each degree into the `max` of the
`natDegree`s of a reduced `x`-normal form, and leaf (B) is the resulting identity.
The four degenerate cases — `φ = 0`, `ψ = 0`, `ψ = −φ`, `ψ = φ`, exactly the cases
leaf (B) must exclude — are discharged first and outright, from `End.degree_neg`
and `End.degree_add_self` (multiplicativity against `deg [±1] = 1`, `deg [2] = 4`).

**This supersedes the third pass's proof** (2026-07-27), which derived the law from
`End.natCast_degree_eq_det_torsionRep` by testing the identity modulo arbitrarily
large primes. That derivation was correct and is now *inverted*: the whole `ρ_ℓ`
layer — `End.exists_trace_charPoly`, `End.exists_trace_charPoly_degree_sub`,
`End.natCast_degree_eq_det_torsionRep_of_not_dvd`,
`End.natCast_degree_eq_det_torsionRep` — is proven **over this law**, so keeping the
old direction as well would be a cycle. What is lost by the inversion is nothing:
the old proof consumed exactly the statement that this file's leaf sequence had been
circling, and this one consumes a statement outside that circle.

Everything else in the trace layer — `End.self_add_dualEnd`, `End.dualEnd_add`,
`End.exists_dual`, `End.exists_charPoly`,
`End.sq_eq_neg_natCast_of_atkinLehner`, and now
`exists_weilPairing_torsionRep_adjoint` too — is proven over this. -/
theorem End.degree_add_add_degree_sub [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (φ ψ : End W) :
    Isogeny.degree (End.toIsogeny (φ + ψ)) + Isogeny.degree (End.toIsogeny (φ - ψ))
      = 2 * Isogeny.degree (End.toIsogeny φ) + 2 * Isogeny.degree (End.toIsogeny ψ) := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · rw [zero_add, zero_sub, End.degree_neg, End.degree_toIsogeny_zero]
    ring
  rcases eq_or_ne ψ 0 with rfl | hψ
  · rw [add_zero, sub_zero, End.degree_toIsogeny_zero]
    ring
  rcases eq_or_ne (φ + ψ) 0 with hadd | hadd
  · have hψφ : ψ = -φ := eq_neg_of_add_eq_zero_right hadd
    subst hψφ
    rw [hadd, End.degree_toIsogeny_zero, sub_neg_eq_add, End.degree_add_self,
      End.degree_neg]
    ring
  rcases eq_or_ne (φ - ψ) 0 with hsub | hsub
  · have hψφ : ψ = φ := (sub_eq_zero.mp hsub).symm
    subst hψφ
    rw [hsub, End.degree_toIsogeny_zero, End.degree_add_self]
    ring
  obtain ⟨A, B, hf, hdf⟩ := End.exists_isXNormalForm_degree hφ
  obtain ⟨C, D, hg, hdg⟩ := End.exists_isXNormalForm_degree hψ
  obtain ⟨A₁, B₁, h₁, hd₁⟩ := End.exists_isXNormalForm_degree hadd
  obtain ⟨A₂, B₂, h₂, hd₂⟩ := End.exists_isXNormalForm_degree hsub
  rw [hdf, hdg, hd₁, hd₂]
  exact End.isXNormalForm_natDegree_parallelogram hφ hψ hadd hsub hf hg h₁ h₂

/-- **The characteristic polynomial of a single endomorphism — PROVEN (2026-07-30,
eighth pass).** Silverman *AEC* III.6.2. Writing `n := deg ψ`, there is an integer
`t` with

    ψ² + [n] = [t] ψ.

**No longer a leaf.** It was the leaf through the sixth pass. The seventh moved the
`sorry` onto `exists_weilPairing_torsionRep_adjoint` and proved this from it; the
eighth **inverted that edge** — the pairing is proven at the foot of this file, over
the very statements it used to supply — and proves this instead from the
parallelogram law `End.degree_add_add_degree_sub` above, which now rests on the two
route-2 leaves. See the ROUTE 2 section above.

### The proof, in one move

`charPoly_of_multiplicative_parallelogram` (PROVEN above, pure ring theory) applied
to `q χ := (deg χ : ℤ)`. Its five hypotheses are discharged by, in order:
`End.degree_toIsogeny_zero`; `Isogeny.degree_id` (side condition `∃ P ≠ 0` from
`infinite_point`); `End.degree_add_add_degree_sub`; `Isogeny.degree_comp`
(as `End.degree_mul`); and `Isogeny.degree_eq_zero_iff`. The `t` it produces is
`deg (ψ + 1) − deg ψ − 1`, Silverman's trace — the same `t` as before. This is
verbatim how `End.self_add_dualEnd` below consumes the same lemma, and the two
proofs are deliberately parallel.

### The seventh pass's proof, retired

It ran through `ρ_ℓ`: `det_charPoly_rank_two` gives Cayley–Hamilton for `2 × 2`
identically, `End.natCast_degree_eq_det_torsionRep_of_weilPairing` converts both
determinants into degrees so that `ρ_ℓ χ = 0` for `χ := ψ² + [n] − [t] ψ` at every
prime, and then a prime `ℓ` with `ℓ² > deg χ` contradicts `W[ℓ] ⊆ ker χ`
(`n_torsion_card` against `IsIsogeny.finite_ker`). That argument is correct and is
**not** deleted — it survives one level down as the proof of
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` below, which is the same
transport with the same prime-size trick. What is retired is only its *use here*,
because its input is now downstream of its output.

### Why this is a strict reduction of the fifth pass's leaf, not a reshuffle

The fifth-pass leaf was this statement **conjoined with** the integer-shift
expansion `deg (ψ − [m]) = m² − t m + n` for every `m : ℤ`. That second conjunct is
**not an independent input**: it follows from this one applied to the shifts
`ψ − [m]` themselves, and `End.exists_trace_charPoly_degree_sub` below is now
exactly that derivation, machine-checked. With `χ := ψ − [m]`:

* expanding `χ²` with `ψ² = [t] ψ − [n]` gives `χ² = [t − 2m] χ + [t m − m² − n]`;
* this leaf applied to `χ` gives `χ² + [deg χ] = [s] χ` for some `s`; subtracting
  leaves the **linear** relation `[a] χ = [b]`, with `a := s − t + 2m` and
  `b := t m − m² − n + deg χ`, and the shift expansion is precisely `b = 0`;
* if `a = 0` then `[b] = 0`, so `b = 0` by `End.intCast_injective`;
* if `a ≠ 0`, taking degrees (`End.degree_mul`, `End.degree_intCast`) gives
  `a² · deg χ = b²`, hence `a ∣ b`; writing `b = a k` and cancelling `[a]` in the
  domain `End W` gives `χ = [k]`, so `ψ = [k + m]` is itself an integer — and then
  `n = (k+m)²`, `t = 2(k+m)` and `b = 0` by direct computation.

The fifth pass instead derived the expansion from the **parallelogram law** by
polarisation. That derivation is correct, but it consumes a strictly stronger input
(the law for arbitrary *pairs*), whereas the argument above consumes only the
single-endomorphism statement — which is why the conjunct can be dropped from the
leaf outright rather than merely re-proved.

**Do not re-conjoin them.** The shift expansion is now a theorem; adding it back to
the leaf would hand the next prover an obligation the file already discharges.

### The equivalent dual form

Multiplying on the right by `ψ` and using `End.dualEnd_comp` (`ψ̂ ψ = [deg ψ]`,
PROVEN above) turns this into **`ψ + ψ̂ = [t]`**; conversely `ψ` right-cancels in the
domain `End W` (and `ψ = 0` is the degenerate case `t = 0`). The two faces are
interderivable in a few lines. The polynomial face is stated here because it is the
one `End.natCast_degree_eq_det_torsionRep_of_not_dvd` transports through `ρ_ℓ`. -/
theorem End.exists_trace_charPoly [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (ψ : End W) :
    ∃ t : ℤ,
      ψ * ψ + ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) = ((t : ℤ) : End W) * ψ := by
  classical
  haveI := infinite_point W
  have hq0 : ((Isogeny.degree (End.toIsogeny (0 : End W)) : ℤ)) = 0 := by
    rw [End.degree_toIsogeny_zero]; norm_num
  have hq1 : ((Isogeny.degree (End.toIsogeny (1 : End W)) : ℤ)) = 1 := by
    have hid : End.toIsogeny (1 : End W) = Isogeny.id W := Isogeny.ext (fun _ => rfl)
    rw [hid, Isogeny.degree_id (exists_ne (0 : W.Point))]; norm_num
  have hpar : ∀ a c : End W,
      (Isogeny.degree (End.toIsogeny (a + c)) : ℤ) + (Isogeny.degree (End.toIsogeny (a - c)) : ℤ)
        = 2 * (Isogeny.degree (End.toIsogeny a) : ℤ)
          + 2 * (Isogeny.degree (End.toIsogeny c) : ℤ) := by
    intro a c
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (End.degree_add_add_degree_sub a c)
  have hmul : ∀ a c : End W,
      (Isogeny.degree (End.toIsogeny (a * c)) : ℤ)
        = (Isogeny.degree (End.toIsogeny a) : ℤ) * (Isogeny.degree (End.toIsogeny c) : ℤ) :=
    fun a c => End.degree_mul a c
  have hzero : ∀ a : End W, (Isogeny.degree (End.toIsogeny a) : ℤ) = 0 → a = 0 := by
    intro a ha
    have h0 : Isogeny.degree (End.toIsogeny a) = 0 := by exact_mod_cast ha
    exact Subtype.ext ((Isogeny.degree_eq_zero_iff _).1 h0)
  refine ⟨(Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
    - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1, ?_⟩
  have hCH := charPoly_of_multiplicative_parallelogram
    (fun χ : End W => (Isogeny.degree (End.toIsogeny χ) : ℤ)) hq0 hq1 hpar hmul hzero ψ
  have hcast : (((Isogeny.degree (End.toIsogeny ψ) : ℕ)) : End W)
      = (((Isogeny.degree (End.toIsogeny ψ) : ℤ)) : End W) := by push_cast; rfl
  rw [hcast]
  exact hCH

/-- **The characteristic polynomial of a single endomorphism, with its integer
shifts — PROVEN (2026-07-28, sixth pass)** over `End.exists_trace_charPoly`
immediately above. Silverman *AEC* III.6.2 together with the polarisation of
III.6.3. Writing `n := deg ψ`, there is an integer `t` with

    ψ² + [n] = [t] ψ      and      deg (ψ − [m]) = m² − t m + n   for every m : ℤ.

**No longer a leaf.** The second conjunct is a consequence of the first applied to
the shifts `ψ − [m]`; see the reduction outline on `End.exists_trace_charPoly`
above, which is this proof. Everything else in the trace layer — starting with
`End.natCast_degree_eq_det_torsionRep_of_not_dvd` immediately below, which was the
leaf before that — is PROVEN over this.

### What it is, and its exact relation to the two statements it replaces

`t` is not free: instantiating the second conjunct at `m = −1` forces
`t = deg (ψ + 1) − n − 1`, which is Silverman's trace. So the existential is a
convenience for the prover, not a weakening — the statement pins `t` and then
asserts two genuine identities about it. Sanity checks: at `ψ = [k]` we get
`n = k²`, `t = 2k` and `deg ([k] − [m]) = (k − m)²`; at `ψ = 0` we get `n = 0`,
`t = 0` and `deg (−[m]) = m²`; at a CM `ψ` of norm `n` it is the minimal
polynomial of `ψ` over `ℤ` together with `N(ψ − m) = m² − t m + n`.

**Both conjuncts are consequences of the parallelogram law
`End.degree_add_add_degree_sub`**, which is what the fifth pass recorded and is
still true:

* conjunct 1 is `charPoly_of_multiplicative_parallelogram` (PROVEN below,
  axiom-clean) applied to `q χ := (deg χ : ℤ)`, exactly as `End.self_add_dualEnd`
  applies it — and that is exactly how `End.exists_trace_charPoly` above is proven
  since the eighth pass (2026-07-30);
* conjunct 2 is polarisation: for a parallelogram form `q` with `q 0 = 0` one has
  `q (x + m • y) = q x + m · b x y + m² · q y` with `b x y := q (x+y) − q x − q y`,
  by two-sided induction on `m` (`Int.induction_on`) from
  `q (z + y) + q (z − y) = 2 q z + 2 q y`; take `y := −1`, `q 1 = 1`
  (`Isogeny.degree_id`, side condition `infinite_point`).

**The sixth pass supersedes the second bullet**, and that is the substance of the
present proof: conjunct 2 needs only conjunct 1, at the shifts `ψ − [m]`, so it is
derived here from `End.exists_trace_charPoly` alone and the parallelogram law is
not consumed. The bullet is kept because it is a correct alternative derivation and
because it records what polarisation costs.

So **anyone who proves the parallelogram law by any route closes the leaf above,
and hence the whole file**, without having to redo the `ρ_ℓ` argument below.

### Why this leaf and not `deg ψ ≡ det (ρ_ℓ ψ)` (the previous one)

The two are equivalent — every statement in this circle is (see the EQUIVALENCE
section on the theorem below) — so the choice is about which face the next prover
is asked to attack. This one is **ℓ-free, about ONE endomorphism, and phrased
purely in degrees and integers**: no torsion module, no basis, no determinant. It
is also the exact output of the classical elementary route (below), whereas
`deg = det` is the output of the Weil-pairing route only.

The earlier docstring on the theorem below recorded the implication
`parallelogram law ⟹ deg = det` as "a proof sketch, not machine-checked", on the
ground that formalising it here "would be a literal cycle". It is not a cycle once
the `sorry` is moved: that implication is now **machine-checked**, and it is the
proof of the theorem below.

### ROUTE (2026-07-28): the elementary `x`-coordinate degree count

**This section is the route audit for `End.exists_trace_charPoly` above**, written
while that statement was the file's open leaf. It is NOT retracted, and the eighth
pass (2026-07-30) is the vindication of its second half: the seventh pass took route
(1) below, Weil-pairing adjointness, and that turned out to be a *face of the circle*
rather than an input — it is PROVEN at the foot of this file from the trace formula
and `deg = det`. **Route (2), the elementary `x`-coordinate degree count, is the
route the file now stands on**; its two sub-steps, which this section correctly
identified as "not stated in this tree yet", are the file's two leaves
`End.exists_isXNormalForm_degree` and
`End.isXNormalForm_natDegree_parallelogram` (see the ROUTE 2 section above). What
still stands unchanged is the proof below that no *counting* argument can supply any
face of the circle.

A **counting** proof is impossible, and this is worth recording because it closes
an entire axis. Every invariant this development can form from kernels —
`Nat.card (ker χ)`, the order of a point, Lagrange, Cauchy — sees only the
**ℓ-adic valuation** of `deg`. Concretely, for a `ZMod N`-endomorphism `M` of
`(ZMod N)²` lifted to an integer matrix with Smith normal form `diag(d₁, d₂)`,
`#ker M = gcd(d₁,N) · gcd(d₂,N)`; knowing that number for every `N` pins
`v_p (det)` at every prime `p` and pins **no value** modulo a prime `ℓ ∤ deg ψ`.
That is exactly why `End.det_torsionRep_eq_zero_of_dvd` above (Cauchy in `ker ψ`)
gets the divisible case and can never get more. So a genuinely non-counting input
is needed, and the two candidates are:

1. **Weil-pairing adjointness** (*AEC* III.8.2) — see the audit on the theorem
   below for what is and is not available for it here. **RETRACTED as a candidate,
   2026-07-30: this is not a non-counting input, it is a face of the circle.** On a
   rank-`2` space an alternating form is unique up to a scalar, so adjointness for
   the dual is interderivable with `deg = det` — `altPairing_trace` above plus
   `End.self_add_dualEnd` prove the pairing outright, at the foot of this file. The
   *counting* impossibility argument in this section is unaffected; what is refuted
   is only the classification of route (1) as an input;
2. **the elementary `x`-coordinate degree count**, which is the route this leaf is
   shaped for and which is *not* recorded anywhere else in this file. For a
   nonzero `φ` with `x ∘ φ = A/B` in lowest terms, `deg φ = max (deg A) (deg B)`;
   the `x`-only addition law expresses `x(P+Q) + x(P−Q)` and `x(P+Q)·x(P−Q)` as
   rational functions of `x P` and `x Q` of bidegree `(2,2)`, and the numerator /
   denominator of the resulting expressions for `x ∘ (φ ± ψ)` are coprime, which
   gives `deg (φ+ψ) + deg (φ−ψ) = 2 deg φ + 2 deg ψ` by counting degrees of
   polynomials only. This is the proof in Washington, *Elliptic Curves*, and it
   needs no divisors, no Weil pairing and no function fields — only the
   `IsRationalMap` normal form, which `Isogeny.lean` already carries
   (`homogSubst`, `natDegree_eq_zero_of_coprime_homogSubst`,
   `exists_const_of_homogSubst_eq_zero`). Its two sub-steps are
   `deg φ = max (deg A) (deg B)` (in characteristic zero, from separability of
   `A − t B` over `F(t)`) and the coprimality count. **Neither is stated in this
   tree yet**, and stating them is the natural next decomposition. -/
theorem End.exists_trace_charPoly_degree_sub [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (ψ : End W) :
    ∃ t : ℤ,
      ψ * ψ + ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) = ((t : ℤ) : End W) * ψ ∧
        ∀ m : ℤ, (Isogeny.degree (End.toIsogeny (ψ - ((m : ℤ) : End W))) : ℤ)
          = m ^ 2 - t * m + (Isogeny.degree (End.toIsogeny ψ) : ℤ) := by
  classical
  have hzero : ∀ a : End W, (Isogeny.degree (End.toIsogeny a) : ℤ) = 0 → a = 0 := by
    intro a ha
    have h0 : Isogeny.degree (End.toIsogeny a) = 0 := by exact_mod_cast ha
    exact Subtype.ext ((Isogeny.degree_eq_zero_iff _).1 h0)
  have hdeg0 : (Isogeny.degree (End.toIsogeny (0 : End W)) : ℤ) = 0 := by
    have h := End.degree_intCast (W := W) 0
    rw [Int.cast_zero] at h
    simpa using h
  -- the square of an integer shift, in the noncommutative ring `End W`
  have expand : ∀ (a : ℤ) (x : End W),
      (x - ((a : ℤ) : End W)) * (x - ((a : ℤ) : End W))
        = x * x - ((2 * a : ℤ) : End W) * x + ((a ^ 2 : ℤ) : End W) := by
    intro a x
    have h1 : x * ((a : ℤ) : End W) = ((a : ℤ) : End W) * x := ((Int.cast_commute a x).eq).symm
    rw [sub_mul, mul_sub, mul_sub, h1]
    push_cast
    noncomm_ring
  by_cases hψ0 : ψ = 0
  · -- the zero endomorphism, where the trace must be `0` rather than merely exist
    subst hψ0
    refine ⟨0, ?_, ?_⟩
    · have h : Isogeny.degree (End.toIsogeny (0 : End W)) = 0 := by exact_mod_cast hdeg0
      rw [h]
      simp
    · intro m
      have hrw : (0 : End W) - ((m : ℤ) : End W) = (((-m : ℤ)) : End W) := by
        push_cast
        abel
      rw [hrw, End.degree_intCast]
      have h : Isogeny.degree (End.toIsogeny (0 : End W)) = 0 := by exact_mod_cast hdeg0
      rw [h]
      push_cast
      ring
  · obtain ⟨t, ht⟩ := End.exists_trace_charPoly ψ
    refine ⟨t, ht, ?_⟩
    intro m
    set n : ℤ := (Isogeny.degree (End.toIsogeny ψ) : ℤ) with hn
    set χ : End W := ψ - ((m : ℤ) : End W) with hχ
    obtain ⟨s, hs⟩ := End.exists_trace_charPoly χ
    set d : ℤ := (Isogeny.degree (End.toIsogeny χ) : ℤ) with hd
    have hψsq : ψ * ψ = ((t : ℤ) : End W) * ψ - ((n : ℤ) : End W) := by
      have hcast : ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) = ((n : ℤ) : End W) := by
        rw [hn]; push_cast; rfl
      rw [hcast] at ht
      rw [← ht]
      abel
    -- expand `χ²` and rewrite it back in terms of `χ`
    have hchisq : χ * χ
        = ((t - 2 * m : ℤ) : End W) * χ + (((t * m - m ^ 2 - n : ℤ)) : End W) := by
      have hψχ : ψ = χ + ((m : ℤ) : End W) := by rw [hχ]; abel
      rw [hχ, expand, hψsq]
      rw [hψχ]
      push_cast
      noncomm_ring
    -- subtracting the two characteristic polynomials leaves a LINEAR relation
    set a : ℤ := s - t + 2 * m with ha
    set b : ℤ := t * m - m ^ 2 - n + d with hb
    have key : ((a : ℤ) : End W) * χ = ((b : ℤ) : End W) := by
      have hcastd : ((Isogeny.degree (End.toIsogeny χ) : ℕ) : End W) = ((d : ℤ) : End W) := by
        rw [hd]; push_cast; rfl
      rw [hcastd, hchisq] at hs
      have h : ((a : ℤ) : End W) * χ - ((b : ℤ) : End W) = 0 := by
        have hsplit : ((a : ℤ) : End W) * χ
            = ((s : ℤ) : End W) * χ - ((t - 2 * m : ℤ) : End W) * χ := by
          rw [← sub_mul]
          congr 1
          rw [ha]
          push_cast
          abel
        rw [hsplit, ← hs, hb]
        push_cast
        abel
      exact sub_eq_zero.mp h
    -- and the shift expansion is exactly `b = 0`
    have hb0 : b = 0 := by
      by_cases ha0 : a = 0
      · rw [ha0, Int.cast_zero, zero_mul] at key
        have hz : ((b : ℤ) : End W) = ((0 : ℤ) : End W) := by
          rw [Int.cast_zero]; exact key.symm
        exact End.intCast_injective hz
      · -- `a ≠ 0` forces `ψ` to be an integer, where both sides are computed outright
        have hdegkey : (Isogeny.degree (End.toIsogeny (((a : ℤ) : End W) * χ)) : ℤ)
            = (Isogeny.degree (End.toIsogeny (((b : ℤ) : End W))) : ℤ) := by rw [key]
        rw [End.degree_mul, End.degree_intCast, End.degree_intCast, ← hd] at hdegkey
        have hdvd : a ∣ b := by
          have h2 : a ^ 2 ∣ b ^ 2 := ⟨d, hdegkey.symm⟩
          exact (Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h2
        obtain ⟨k, hk⟩ := hdvd
        have ha2 : (a : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ ha0
        have hdk : d = k ^ 2 := by
          have h3 : a ^ 2 * d = a ^ 2 * k ^ 2 := by rw [hdegkey, hk]; ring
          exact mul_left_cancel₀ ha2 h3
        have hχk : χ = ((k : ℤ) : End W) := by
          have h4 : ((a : ℤ) : End W) * (χ - ((k : ℤ) : End W)) = 0 := by
            rw [mul_sub, key, ← Int.cast_mul, hk]
            abel
          have h5 : (Isogeny.degree (End.toIsogeny (((a : ℤ) : End W))) : ℤ)
              * (Isogeny.degree (End.toIsogeny (χ - ((k : ℤ) : End W))) : ℤ) = 0 := by
            rw [← End.degree_mul, h4, hdeg0]
          rw [End.degree_intCast] at h5
          have h6 : (Isogeny.degree (End.toIsogeny (χ - ((k : ℤ) : End W))) : ℤ) = 0 := by
            rcases mul_eq_zero.mp h5 with h | h
            · exact absurd h ha2
            · exact h
          have h7 := hzero _ h6
          rw [sub_eq_zero] at h7
          exact h7
        have hψc : ψ = (((k + m : ℤ)) : End W) := by
          have hsplit : ψ = χ + ((m : ℤ) : End W) := by rw [hχ]; abel
          rw [hsplit, hχk]
          push_cast
          abel
        set c : ℤ := k + m with hc
        have hcne : c ≠ 0 := by
          intro hc0
          exact hψ0 (by rw [hψc, hc0, Int.cast_zero])
        have hnc : n = c ^ 2 := by
          rw [hn, hψc, End.degree_intCast]
        have hcast : ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) = ((n : ℤ) : End W) := by
          rw [hn]; push_cast; rfl
        have ht2 : t = 2 * c := by
          rw [hcast, hψc] at ht
          have h8 : (((c * c + n : ℤ)) : End W) = (((t * c : ℤ)) : End W) := by
            push_cast
            exact ht
          have h9 : c * c + n = t * c := End.intCast_injective h8
          rw [hnc] at h9
          have h10 : (2 * c - t) * c = 0 := by linear_combination h9
          rcases mul_eq_zero.mp h10 with h | h
          · linarith
          · exact absurd h hcne
        rw [hb, hdk, hnc, ht2]
        have hkc : k = c - m := by rw [hc]; ring
        rw [hkc]
        ring
    rw [hb] at hb0
    linarith

/-- **`deg = det` on the `ℓ`-torsion, at the primes that do not divide the
degree — PROVEN (2026-07-28).** Silverman *AEC* III.8.6: for every prime `ℓ`,

    deg ψ ≡ det (ρ_ℓ ψ)   (mod ℓ).

**No longer a leaf: PROVEN 2026-07-28** over
`End.exists_trace_charPoly_degree_sub` immediately above, which is the sketch of
the fourth pass (recorded below and until now unformalised) turned into the actual
proof. The complementary case `ℓ ∣ deg ψ` is PROVEN
just above (`End.det_torsionRep_eq_zero_of_dvd`: both sides vanish), and
`End.natCast_degree_eq_det_torsionRep` below assembles the two; over that,
`End.degree_add_add_degree_sub` and then the whole trace layer —
`End.self_add_dualEnd`, `End.dualEnd_add`, `End.exists_dual`,
`End.exists_charPoly`, `End.sq_eq_neg_natCast_of_atkinLehner` — are proven.

The hypothesis `¬ ℓ ∣ deg ψ` is genuinely **unused** — the proof below never looks
at it, hence the underscore on its binder — and is kept only because the statement
was written that way and its consumer supplies it for free (it tests the identity
at primes larger than every degree in sight). It is *not* removed here, because
that would be a gratuitous signature change to a name two modules import.

### EQUIVALENCE WITH THE PARALLELOGRAM LAW (2026-07-27, fourth pass;
### the converse is MACHINE-CHECKED as of 2026-07-28)

An earlier version of this docstring said this statement "is about ONE
endomorphism rather than about a pair, which is why it is a better leaf than the
parallelogram law was". The first clause is true and the second is **misleading**:
the two statements are **equivalent**, so nothing is gained or lost by moving
between them, and a future pass should not shuffle them again.

The direction `this ⟹ parallelogram law` is `End.degree_add_add_degree_sub` below.
Here is the converse — which the fourth pass could only sketch, calling it "a proof
sketch, not machine-checked", because inside this file it *was* a cycle. Moving the
`sorry` up to `End.exists_trace_charPoly_degree_sub` breaks the cycle, and the
sketch below is now literally the proof of this theorem. Assume the parallelogram
law. Then `charPoly_of_multiplicative_parallelogram` (below, and it needs only the
parallelogram law plus `Isogeny.degree_comp`) gives `ψ² = [t] ψ − [n]` in `End W`
with `n := deg ψ` and `t := deg (ψ+1) − deg ψ − 1`, and polarisation gives the
integer-shift expansion `deg (ψ − m) = n − m t + m²` for every `m : ℤ` — those two
facts together are exactly `End.exists_trace_charPoly_degree_sub`. Fix a prime
`ℓ`, write `M := ρ_ℓ ψ`, and apply the ring homomorphism `ρ_ℓ`:

    M² − t M + n = 0,      and (Cayley–Hamilton, rank 2)  M² − (tr M) M + det M = 0,

so `(tr M − t) · M = (det M − n) · 1`.

* If `tr M = t`, then `(det M − n) · 1 = 0` and hence `det M = n`, which is the
  leaf.
* Otherwise `M = c · 1` is a scalar, with `tr M = 2c`. Take an integer lift `c̃`
  of `c`: then `ρ_ℓ (ψ − [c̃]) = 0`, i.e. `W[ℓ] ⊆ ker (ψ − [c̃])`, so if
  `ψ − [c̃] ≠ 0` Lagrange against `#W[ℓ] = ℓ²` (`n_torsion_card`) gives
  `ℓ² ∣ deg (ψ − c̃) = c̃² − t c̃ + n`. The **same holds for the lift `c̃ + ℓ`**, and
  subtracting the two divisibilities leaves `ℓ² ∣ ℓ (2c̃ + ℓ − t)`, i.e.
  `ℓ ∣ 2c̃ − t`, i.e. `t = 2c = tr M` — contradicting the case assumption. So this
  branch is empty.

**One correction to the fourth pass's sketch, found while formalising it.** The
sketch disposed of the possibility `ψ − [c̃] = 0` by a separate case "if `ψ = [m]`
then `n = m²` and `det M = m²` directly", which needs `deg [m] = m²` as an extra
input. That case is not needed at all: `End.intCast_injective` says **at most one**
integer can equal `ψ`, so among the four lifts `c̃, c̃ + ℓ, c̃ + 2ℓ, c̃ + 3ℓ` at
least one of the two disjoint consecutive pairs `(c̃, c̃ + ℓ)`, `(c̃ + 2ℓ, c̃ + 3ℓ)`
consists of two lifts with `ψ − [·] ≠ 0`, and the two-lift step runs on that pair.
(Three lifts would *not* suffice: the two consecutive pairs among them share their
middle element.) That is the only place the formalisation departs from the sketch.

The two-lift step is the only non-routine move, and it is the reason the scalar
case does not need a separate geometric input.

**What the equivalence means for dispatch.** The route search must NOT be confined
to Weil-pairing adjointness: **any independent proof of the parallelogram law
closes this whole file**, and conversely. That warning was written on 2026-07-28 and
2026-07-30 confirmed it in the sharpest possible way — Weil-pairing adjointness is
itself a member of the equivalence class, not an alternative to it. Silverman *AEC*
III.6.3's own inputs (the theorem of the square / seesaw, or the classical degree
count of the `x`-coordinate map) are the live alternatives, and the file now stands
on the second of those.

### READING THE AUDITS BELOW AFTER THE 2026-07-28 AND 2026-07-30 RELOCATIONS

Everything from here down was written while this statement *was* the file's open
leaf. It is all still valid and none of it is retracted — but "this leaf" in it now
means whichever member of the degree circle was open at the time of writing; ALL of
them are now PROVEN, over the two route-2 leaves
`End.exists_isXNormalForm_degree` and
`End.isXNormalForm_natDegree_parallelogram` (ROUTE 2 section above). In
particular the Weil-pairing audit is the audit of route (1) recorded there — read it
as a record of a *withdrawn* candidate — and the `x`-coordinate degree count is
route (2), which is where the leaves now are.

### Why the `deg = det` shape, and not the parallelogram law itself

**(a) The parallelogram law is NOT reducible to algebra, so a genuinely geometric
input is unavoidable; this is the smallest one.** The facts available about `deg`
without any new input are: `deg 0 = 0`, `deg 1 = 1`, multiplicativity
(`Isogeny.degree_comp`), definiteness (`Isogeny.degree_eq_zero_iff`) — **and a
fifth that an earlier version of this paragraph forgot**, `deg [m] = m ^ 2`
(`n_torsion_card`, since `ker [m] = W[m]` has `m²` elements).

**The forgotten fifth fact kills the counterexample that was recorded here.** It
was `R = ℤ` with `q n := n ^ 4`, which satisfies the four listed facts and violates
the parallelogram law — but it also has `q m = m ^ 4 ≠ m ^ 2`, so it never was a
model of everything available, and the paragraph's conclusion did not follow from
its own example. A **repaired counterexample**, satisfying all *five* facts:

    R = ℤ[√2],   q (a + b√2) := |a² − 2b²| = |N(a + b√2)|.

`|N|` is multiplicative, vanishes only at `0` (a domain), and `q m = m²` on `ℤ`;
yet `q (1+√2) + q (1−√2) = 1 + 1 = 2` while `2 q 1 + 2 q √2 = 2 + 4 = 6`. So the
conclusion stands — the absolute value of an indefinite norm form is exactly what
the five facts cannot exclude, and only positivity of `deg` as a *quadratic* form
(the geometric input) does. (Contrast the trace formula, which the available facts
*do* give once the parallelogram law is assumed — that is
`charPoly_of_multiplicative_parallelogram`.)

**(b) The dual does not give it either, and here is why the obvious try fails.**
`End.dualEnd_comp` (PROVEN) is `ψ̂ψ = [deg ψ]`; applying the ring homomorphism
`End.torsionRep` gives `ρ_ℓ(ψ̂) · ρ_ℓ(ψ) = deg ψ · 1`, whence
`det ρ_ℓ(ψ̂) · det ρ_ℓ(ψ) = (deg ψ)²`. That is symmetric in the two factors and does
**not** separate them: `A = 1`, `B = c · 1` satisfies `BA = c · 1` with
`det A = 1 ≠ c`. What would separate them is `ρ_ℓ(ψ̂) = adj (ρ_ℓ ψ)`, i.e. the trace
formula — which is proven here only *over* the parallelogram law, so that route is
circular.

### ROUTE AUDIT (2026-07-27, third pass; corrects the second pass on one point)

**What supplies this leaf.** The classical proof is *AEC* III.8.2, adjointness of
the Weil pairing: `e_ℓ (ψ P, Q) = e_ℓ (P, ψ̂ Q)`. Given that, and *only* that, the
rest is already in this tree:

* `e_ℓ (ψ P, ψ Q) = e_ℓ (P, ψ̂ ψ Q) = e_ℓ (P, [deg ψ] Q) = deg ψ • e_ℓ (P, Q)` by
  `End.dualEnd_comp`, PROVEN above;
* an endomorphism scaling an alternating nondegenerate form on a rank-`2` space by
  `c` has determinant `c` — `WeilPairing.det_eq_of_conj` (`WeilPairing.lean:100`,
  PROVEN), over `WeilPairing.pairing_map_eq_det_smul` (ibid.:54, PROVEN), against
  `Module.rank (ZMod ℓ) (W.nTorsion ℓ) = 2` (`p_torsion_rank`, PROVEN).

So the leaf is exactly one Weil-pairing property away, and that property is about a
single pairing rather than about degrees.

**CORRECTION to the second pass.** It recorded `WeilPairing*.lean` as a flat DEAD
END on the ground that `WeilPairing.exists_weilPairing` is "constructed as the
coordinate determinant form in a basis", carrying no arithmetic. That was too
strong. `WeilPairing.exists_weilPairing_mu` (`WeilPairing.lean:6057`, PROVEN, and
its in-proof construction plan is explicitly the divisor-theoretic *AEC* III.8) is
a genuine `μ_p`-valued Weil pairing — **but over a finite base field `𝔽_q`, and its
naturality clause is for the `q`-power Frobenius of the base**, i.e. for a
semilinear automorphism of the coefficients, not for an isogeny of the curve. Our
base is algebraically closed of characteristic zero and our `ψ` is an isogeny, so
that theorem does not apply and does not specialise; the *construction* in it is
nevertheless the thing to reuse, which the flat "dead end" verdict would have
discouraged. The conclusion is unchanged, the reason is not.

**The greps that would refute this audit** — a pairing statement quantified over
isogenies rather than over field automorphisms, or a Tate module:

    grep -rn 'weilPairing.*degree\|degree.*weilPairing' Fermat/
    grep -rn 'Isogeny\|dualHom\|degree' Fermat/FLT/EllipticCurve/WeilPairing*.lean
    grep -rn 'Tate module\|tateModule\|adjugate' Fermat/ ~/cs/FLT/FLT/

All three were run on 2026-07-27 and none returns anything relevant. `~/cs/FLT`
does not help: its `FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean` is a 42-line
stub whose single declaration `WeierstrassCurve.weilPairing` is a `def` with a
`sorry` body, so there is nothing to vendor.

**What IS cheaply available, and is not enough.** `ker (ρ_ℓ ψ) = ker ψ ∩ W[ℓ]`, so
by Cauchy's theorem in the finite group `ker ψ`, `det (ρ_ℓ ψ) = 0 ↔ ℓ ∣ deg ψ`.
That pins the *vanishing* of the determinant but not its value — which is exactly
why it discharges the case `ℓ ∣ deg ψ` and no more; the `→` half is now PROVEN as
`End.det_torsionRep_eq_zero_of_dvd` above, and is the reason this leaf may assume
`¬ ℓ ∣ deg ψ`. Likewise the `ℓ`-adic Smith-normal-form argument pins
`v_ℓ (deg ψ) = v_ℓ (det T_ℓ ψ)` — a valuation, again not a value — so it does not
shortcut the leaf either.

### FOURTH-PASS AUDIT (2026-07-27): where the reusable machinery actually stops

The greps above were re-run and still return nothing; two further checks were added,
and both are worth recording because they narrow the missing work rather than
merely restating that it is missing.

* **mathlib has no Weil pairing at all** — `grep -rln 'weilPairing\|WeilPairing'`
  over `.lake/packages/mathlib/Mathlib/` returns **zero** files. So this is not a
  "look upstream" situation; the pairing exists in this repository only.
* **This tree's divisor-theoretic Miller machinery is only PARTLY char-generic, and
  the boundary is sharp.** `WeilPairingDescent.lean` and `WeilPairingStageB.lean`
  are stated over `{F} [Field F] [DecidableEq F] [IsAlgClosed F]` with `(p : F) ≠ 0`
  — no finite-field hypothesis — and `exists_millerValue_alternating` and
  `millerRatio_eval_pow_of_pullback` really do carry none. But
  `exists_generic_pDivision_offset` and `exists_millerRatio_eval_translationChar`
  take `{F₁ F₂ : Subfield F}` with `(F₁ : Set F).Finite`, and a **finite** subfield
  containing the curve's coefficients exists only in characteristic `p`
  (`exists_finite_subfield_containing`, which is where `exists_weilValueSetup_avoiding`
  gets it). So the honest statement of the missing work is: the *genericity /
  avoidance* layer must be redone over a characteristic-zero base — the alternation
  and pullback cores transfer unchanged — and isogeny-naturality must then be added
  on top. Reporting "the Weil pairing is finite-field-only here" without that split
  overstates the job.

**Sanity check of the statement.** At `ψ = [n]`, `ρ_ℓ ψ = n · id` has determinant
`n²` and `deg [n] = # W[n] = n²` (`n_torsion_card`). At `ψ = 0` both sides are `0`
(`Isogeny.degree_of_eq_zero`, and the determinant of the zero endomorphism of a
rank-`2` module is `0`) — and that case is now PROVEN rather than merely checked,
inside `End.det_torsionRep_eq_zero_of_dvd`. Over `ℚ̄` with `End W ⊇ ℤ[i]` and `deg`
the field norm, `ψ = i` has `deg = 1` and `ρ_ℓ i` is a square root of `−1` in
`M₂(ZMod ℓ)`, of determinant `1`. -/
theorem End.natCast_degree_eq_det_torsionRep_of_not_dvd [IsAlgClosed F] [CharZero F]
    [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (ψ : End W)
    (_hnd : ¬ ℓ ∣ Isogeny.degree (End.toIsogeny ψ)) :
    ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : ZMod ℓ)
      = LinearMap.det (End.torsionRep W ℓ ψ) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨t, hchar, hdegsub⟩ := End.exists_trace_charPoly_degree_sub ψ
  set n : ℕ := Isogeny.degree (End.toIsogeny ψ) with hn
  set b := nTorsionBasis W ℓ with hb
  set M : Module.End (ZMod ℓ) (W.nTorsion ℓ) := End.torsionRep W ℓ ψ with hM
  set A : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := LinearMap.toMatrix b b M with hA
  have hdet : A.det = LinearMap.det M := LinearMap.det_toMatrix b M
  rw [← hdet]
  -- `ρ_ℓ` carries an integer or natural cast to the corresponding scalar
  have hrhoInt : ∀ m : ℤ, End.torsionRep W ℓ ((m : ℤ) : End W)
      = ((m : ZMod ℓ)) • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) := by
    intro m
    rw [map_intCast]
    rw [show (((m : ℤ)) : Module.End (ZMod ℓ) (W.nTorsion ℓ))
        = m • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) by rw [zsmul_eq_mul, mul_one]]
    exact (Int.cast_smul_eq_zsmul (ZMod ℓ) m (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ))).symm
  have hrhoNat : End.torsionRep W ℓ ((n : ℕ) : End W)
      = ((n : ZMod ℓ)) • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) := by
    rw [map_natCast]
    rw [show (((n : ℕ)) : Module.End (ZMod ℓ) (W.nTorsion ℓ))
        = n • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) by rw [nsmul_eq_mul, mul_one]]
    exact (Nat.cast_smul_eq_nsmul (ZMod ℓ) n (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ))).symm
  -- transport the characteristic polynomial through `ρ_ℓ` and then to matrices
  have hMchar : M * M + ((n : ZMod ℓ)) • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ))
      = ((t : ZMod ℓ)) • M := by
    have h := congrArg (End.torsionRep W ℓ) hchar
    rw [map_add, map_mul, map_mul, hrhoNat, hrhoInt t] at h
    rw [← hM] at h
    rw [h, smul_mul_assoc, one_mul]
  have h1 : A * A + ((n : ZMod ℓ)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
      = ((t : ZMod ℓ)) • A := by
    have h := congrArg (LinearMap.toMatrix b b) hMchar
    rw [map_add, LinearMap.toMatrix_mul, map_smul, LinearMap.toMatrix_one, map_smul] at h
    rw [← hA] at h
    exact h
  -- Cayley–Hamilton in rank two, by hand from `det_fin_two` and `trace_fin_two`
  have hCH : A * A
      = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
        Matrix.det_fin_two] <;> ring
  have h2 : A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))
      + ((n : ZMod ℓ)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = ((t : ZMod ℓ)) • A := by
    rw [← hCH]; exact h1
  have hkey : (A.trace - (t : ZMod ℓ)) • A
      = (A.det - (n : ZMod ℓ)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ← h2]
    abel
  by_cases hcase : A.trace = (t : ZMod ℓ)
  · -- the traces agree, so the determinants do
    have h4 : (A.det - (n : ZMod ℓ)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0 := by
      rw [← hkey, hcase, sub_self, zero_smul]
    have h5 : A.det - (n : ZMod ℓ) = 0 := by
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h one_ne_zero
    exact (sub_eq_zero.mp h5).symm
  · -- otherwise `M` is a scalar, and the two-lift argument contradicts that
    exfalso
    apply hcase
    set c : ZMod ℓ := (A.trace - (t : ZMod ℓ))⁻¹ * (A.det - (n : ZMod ℓ)) with hc
    have hu : (A.trace - (t : ZMod ℓ)) ≠ 0 := sub_ne_zero.mpr hcase
    have hA1 : A = c • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
      calc A = (A.trace - (t : ZMod ℓ))⁻¹ • ((A.trace - (t : ZMod ℓ)) • A) := by
              rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
        _ = (A.trace - (t : ZMod ℓ))⁻¹
              • ((A.det - (n : ZMod ℓ)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ))) := by
              rw [hkey]
        _ = c • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by rw [smul_smul, hc]
    have htr : A.trace = c + c := by
      rw [hA1]
      simp only [Matrix.trace_fin_two, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one]
    have hM1 : M = c • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) := by
      apply (LinearMap.toMatrix b b).injective
      rw [map_smul, LinearMap.toMatrix_one, ← hA]
      exact hA1
    -- an endomorphism with vanishing torsion representation kills the whole `ℓ`-torsion
    have hkill : ∀ χ : End W, End.torsionRep W ℓ χ = 0 →
        ∀ P : W.Point, ((ℓ : ℤ) • P = 0) → (χ : AddMonoid.End W.Point) P = 0 := by
      intro χ hχ P hP
      have hmem : P ∈ Submodule.torsionBy ℤ W.Point (ℓ : ℤ) :=
        (Submodule.mem_torsionBy_iff _ _).2 hP
      have h0 : (End.torsionRep W ℓ χ) (⟨P, hmem⟩ : W.nTorsion ℓ) = 0 := by
        rw [hχ]; simp
      exact congrArg Subtype.val h0
    -- Lagrange: `W[ℓ] ≤ ker χ` and `#W[ℓ] = ℓ²` force `ℓ² ∣ deg χ`
    have hlag : ∀ χ : End W, End.torsionRep W ℓ χ = 0 →
        (End.toIsogeny χ).toHom ≠ 0 →
        (ℓ : ℤ) ^ 2 ∣ (Isogeny.degree (End.toIsogeny χ) : ℤ) := by
      intro χ hχ hne
      have hle : (Submodule.torsionBy ℤ W.Point (ℓ : ℤ)).toAddSubgroup
          ≤ AddMonoidHom.ker (End.toIsogeny χ).toHom := by
        intro P hP
        exact hkill χ hχ P ((Submodule.mem_torsionBy_iff _ _).1 hP)
      have hcard := AddSubgroup.card_dvd_of_le hle
      have hℓF : ((ℓ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
      have hcard2 : Nat.card (W.nTorsion ℓ) = ℓ ^ 2 :=
        WeierstrassCurve.n_torsion_card (E := W) hℓF
      rw [Isogeny.degree_of_ne_zero (φ := End.toIsogeny χ) hne]
      have hnat : ℓ ^ 2 ∣ Nat.card (AddMonoidHom.ker (End.toIsogeny χ).toHom) := by
        rw [← hcard2]; exact hcard
      exact_mod_cast hnat
    -- at most one integer can equal `ψ`, so two consecutive good lifts exist
    have huniq : ∀ m₁ m₂ : ℤ, ψ - ((m₁ : ℤ) : End W) = 0 → ψ - ((m₂ : ℤ) : End W) = 0 →
        m₁ = m₂ := by
      intro m₁ m₂ h₁ h₂
      exact End.intCast_injective ((sub_eq_zero.mp h₁).symm.trans (sub_eq_zero.mp h₂))
    have hc0 : ((((c.val : ℕ) : ℤ)) : ZMod ℓ) = c := by
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    obtain ⟨m, hmc, hm1, hm2⟩ : ∃ m : ℤ, ((m : ℤ) : ZMod ℓ) = c ∧
        ψ - ((m : ℤ) : End W) ≠ 0 ∧ ψ - ((m + (ℓ : ℤ) : ℤ) : End W) ≠ 0 := by
      by_cases h1 : ψ - ((((c.val : ℕ) : ℤ) : ℤ) : End W) = 0
      · refine ⟨((c.val : ℕ) : ℤ) + 2 * (ℓ : ℤ), ?_, ?_, ?_⟩
        · push_cast
          push_cast at hc0
          simp [hc0]
        · intro hbad
          have := huniq _ _ h1 hbad
          omega
        · intro hbad
          have := huniq _ _ h1 hbad
          omega
      · by_cases h2 : ψ - ((((c.val : ℕ) : ℤ) + (ℓ : ℤ) : ℤ) : End W) = 0
        · refine ⟨((c.val : ℕ) : ℤ) + 2 * (ℓ : ℤ), ?_, ?_, ?_⟩
          · push_cast
            push_cast at hc0
            simp [hc0]
          · intro hbad
            have := huniq _ _ h2 hbad
            omega
          · intro hbad
            have := huniq _ _ h2 hbad
            omega
        · exact ⟨((c.val : ℕ) : ℤ), hc0, h1, h2⟩
    have hmc2 : ((m + (ℓ : ℤ) : ℤ) : ZMod ℓ) = c := by
      push_cast
      simp
      exact hmc
    have hzero : ∀ k : ℤ, ((k : ℤ) : ZMod ℓ) = c →
        End.torsionRep W ℓ (ψ - ((k : ℤ) : End W)) = 0 := by
      intro k hk
      rw [map_sub, hrhoInt k, hk, ← hM, hM1, sub_self]
    have hdvd1 : (ℓ : ℤ) ^ 2 ∣ (m ^ 2 - t * m + (n : ℤ)) := by
      have h := hlag _ (hzero m hmc) (fun h => hm1 (Subtype.ext h))
      rwa [hdegsub m] at h
    have hdvd2 : (ℓ : ℤ) ^ 2 ∣ ((m + (ℓ : ℤ)) ^ 2 - t * (m + (ℓ : ℤ)) + (n : ℤ)) := by
      have h := hlag _ (hzero (m + (ℓ : ℤ)) hmc2) (fun h => hm2 (Subtype.ext h))
      rwa [hdegsub (m + (ℓ : ℤ))] at h
    have hdiff : (ℓ : ℤ) ^ 2 ∣ (ℓ : ℤ) * (2 * m + (ℓ : ℤ) - t) := by
      have h := dvd_sub hdvd2 hdvd1
      have he : ((m + (ℓ : ℤ)) ^ 2 - t * (m + (ℓ : ℤ)) + (n : ℤ))
          - (m ^ 2 - t * m + (n : ℤ)) = (ℓ : ℤ) * (2 * m + (ℓ : ℤ) - t) := by ring
      rwa [he] at h
    have hdvd3 : (ℓ : ℤ) ∣ (2 * m - t) := by
      obtain ⟨k, hk⟩ := hdiff
      have hcancel : (ℓ : ℤ) * (2 * m + (ℓ : ℤ) - t) = (ℓ : ℤ) * ((ℓ : ℤ) * k) := by
        rw [hk]; ring
      have hq := mul_left_cancel₀ hℓ0 hcancel
      refine ⟨k - 1, ?_⟩
      linarith [hq]
    have hfin : ((2 * m - t : ℤ) : ZMod ℓ) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd3
    push_cast at hfin
    rw [hmc] at hfin
    rw [htr]
    linear_combination hfin

/-- **`deg = det` on the `ℓ`-torsion, for every prime `ℓ`** — Silverman *AEC*
III.8.6, in the form the parallelogram law below consumes:

    deg ψ ≡ det (ρ_ℓ ψ)   (mod ℓ).

Assembly of the two cases. When `ℓ ∣ deg ψ` both sides vanish — the left by
`ZMod.natCast_eq_zero_iff`, the right by `End.det_torsionRep_eq_zero_of_dvd`
(PROVEN above, Cauchy in `ker ψ`). Otherwise it is the leaf
`End.natCast_degree_eq_det_torsionRep_of_not_dvd`.

The hypothesis-free form is kept as the consumer-facing name because
`End.degree_add_add_degree_sub` and everything above it were written against it,
and because at the primes the consumer actually uses — larger than every degree in
sight — the divisibility case is vacuous anyway. -/
theorem End.natCast_degree_eq_det_torsionRep [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (ψ : End W) :
    ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : ZMod ℓ)
      = LinearMap.det (End.torsionRep W ℓ ψ) := by
  by_cases hdvd : ℓ ∣ Isogeny.degree (End.toIsogeny ψ)
  · rw [(ZMod.natCast_eq_zero_iff _ _).2 hdvd, End.det_torsionRep_eq_zero_of_dvd ℓ ψ hdvd]
  · exact End.natCast_degree_eq_det_torsionRep_of_not_dvd ℓ ψ hdvd

/-- **The trace formula.** Silverman *AEC* III.6.2: `ψ + ψ̂` is an integer,
and that integer is `deg (ψ + 1) − deg ψ − 1`:

    ψ + ψ̂ = [deg (ψ + 1) − deg ψ − 1].

Equivalently — multiply on the right by `ψ` and use `End.dualEnd_comp` — every
endomorphism satisfies the monic quadratic `ψ² − [t] ψ + [deg ψ] = 0` over `ℤ`.

**PROVEN (2026-07-27, second pass)** over the parallelogram law
`End.degree_add_add_degree_sub` alone. The first pass recorded this as an
independent second leaf; it is not. The proof is
`charPoly_of_multiplicative_parallelogram` applied to
`q χ := (Isogeny.degree (End.toIsogeny χ) : ℤ)`, whose five hypotheses are
discharged here by, in order: `Isogeny.degree_zero`; `Isogeny.degree_id` (side
condition `∃ P ≠ 0` from `infinite_point`); the leaf; `Isogeny.degree_comp`; and
`Isogeny.degree_eq_zero_iff`. That yields `ψ² + [deg ψ] = [t] ψ`, and then
`([t] − ψ) ψ = [deg ψ] = ψ̂ ψ` with `ψ` surjective on points
(`IsIsogeny.surjective`), so `ψ` right-cancels and `ψ̂ = [t] − ψ`. The zero case is
separate and degenerate: `dualEnd 0 = 0` and `t = deg 1 − deg 0 − 1 = 0`.

**The formula is stated with an explicit trace rather than existentially** on
purpose: `∃ t, ψ + ψ̂ = [t]` would leave the assembly needing to know that `t` is
additive in `ψ`. Pinning `t = deg(ψ+1) − deg ψ − 1` makes additivity of `t` a
consequence of the parallelogram law alone, by polarisation — which is exactly how
`End.dualEnd_add` below consumes it.

**Sanity checks**, all four of which the statement passes:
`ψ = 0` gives `0 = deg 1 − 0 − 1 = 0`; `ψ = [k]` gives `2k = (k+1)² − k² − 1`;
`ψ = i` on the curve with CM by `ℤ[i]` gives `i + î = i − i = 0` against
`N(1+i) − N(i) − 1 = 2 − 1 − 1 = 0`; and `ψ = 11 + 2i`, of norm `125` — the
Atkin–Lehner witness recalled under `End.sq_eq_neg_natCast_of_atkinLehner` — gives
`ψ + ψ̄ = 22` against `N(12+2i) − 125 − 1 = 148 − 126 = 22`.

`[CharZero F]` is required: `End.dualEnd` does not exist without it, the statement
being false over `𝔽̄₂` (see the FALSITY AUDIT above). -/
theorem End.self_add_dualEnd [IsAlgClosed F] [CharZero F] [W.IsElliptic] (ψ : End W) :
    ψ + End.dualEnd ψ
      = (((Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1 : ℤ) : End W) := by
  classical
  haveI := infinite_point W
  have hq0 : ((Isogeny.degree (End.toIsogeny (0 : End W)) : ℤ)) = 0 := by
    have hz : End.toIsogeny (0 : End W) = Isogeny.zero := rfl
    rw [hz, Isogeny.degree_zero]; norm_num
  have hq1 : ((Isogeny.degree (End.toIsogeny (1 : End W)) : ℤ)) = 1 := by
    have hid : End.toIsogeny (1 : End W) = Isogeny.id W := Isogeny.ext (fun _ => rfl)
    rw [hid, Isogeny.degree_id (exists_ne (0 : W.Point))]; norm_num
  have hpar : ∀ a c : End W,
      (Isogeny.degree (End.toIsogeny (a + c)) : ℤ) + (Isogeny.degree (End.toIsogeny (a - c)) : ℤ)
        = 2 * (Isogeny.degree (End.toIsogeny a) : ℤ)
          + 2 * (Isogeny.degree (End.toIsogeny c) : ℤ) := by
    intro a c
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (End.degree_add_add_degree_sub a c)
  have hmul : ∀ a c : End W,
      (Isogeny.degree (End.toIsogeny (a * c)) : ℤ)
        = (Isogeny.degree (End.toIsogeny a) : ℤ) * (Isogeny.degree (End.toIsogeny c) : ℤ) := by
    intro a c
    have hc : End.toIsogeny (a * c) = (End.toIsogeny a).comp (End.toIsogeny c) :=
      Isogeny.ext (fun _ => rfl)
    rw [hc, Isogeny.degree_comp]
    push_cast; ring
  have hzero : ∀ a : End W, (Isogeny.degree (End.toIsogeny a) : ℤ) = 0 → a = 0 := by
    intro a ha
    have h0 : Isogeny.degree (End.toIsogeny a) = 0 := by exact_mod_cast ha
    exact Subtype.ext ((Isogeny.degree_eq_zero_iff _).1 h0)
  have hCH : ψ * ψ + ((Isogeny.degree (End.toIsogeny ψ) : ℤ) : End W)
      = (((Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1 : ℤ) : End W) * ψ :=
    charPoly_of_multiplicative_parallelogram
      (fun χ : End W => (Isogeny.degree (End.toIsogeny χ) : ℤ)) hq0 hq1 hpar hmul hzero ψ
  by_cases h0 : ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) = 0
  · have hψ0 : ψ = 0 := Subtype.ext h0
    subst hψ0
    rw [End.dualEnd_of_eq_zero h0, add_zero, zero_add, hq1, hq0]
    norm_num
  · have hsurj : Function.Surjective ((ψ : AddMonoid.End W.Point) : W.Point →+ W.Point) :=
      ψ.2.surjective h0
    have hcancel : ∀ f g : End W, f * ψ = g * ψ → f = g := by
      intro f g hfg
      refine Subtype.ext (AddMonoidHom.ext fun P => ?_)
      obtain ⟨Q, hQ⟩ := hsurj P
      have hc := congrArg (fun h : End W => (h : AddMonoid.End W.Point) Q) hfg
      simp only [End.mul_apply] at hc
      rw [← hQ]
      exact hc
    have hcast : (((Isogeny.degree (End.toIsogeny ψ) : ℕ)) : End W)
        = (((Isogeny.degree (End.toIsogeny ψ) : ℤ)) : End W) := by push_cast; rfl
    have hmul2 : ((((Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1 : ℤ) : End W) - ψ) * ψ
        = End.dualEnd ψ * ψ := by
      rw [End.dualEnd_comp, hcast, sub_mul, ← hCH]
      abel
    have hfin := hcancel _ _ hmul2
    rw [← hfin]
    abel

/-- **The dual isogeny is ADDITIVE** — Silverman *AEC* III.6.2(b).

**PROVEN (2026-07-27)** over the parallelogram law
`End.degree_add_add_degree_sub` — itself PROVEN since the eighth pass of 2026-07-30
over the two route-2 leaves `End.exists_isXNormalForm_degree` and
`End.isXNormalForm_natDegree_parallelogram` — through the
trace formula `End.self_add_dualEnd`, proven over that same parallelogram law in
the second pass. See the CUT note above for why the first pass believed the trace
formula was independent, and the ROUTE 2 section for why the third pass's
derivation of the parallelogram law from `deg = det` had to be inverted.

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
over the parallelogram law `End.degree_add_add_degree_sub` (itself PROVEN since the
eighth pass of 2026-07-30, over the two route-2 leaves
`End.exists_isXNormalForm_degree` and
`End.isXNormalForm_natDegree_parallelogram`), via the trace formula
`End.self_add_dualEnd`. `[CharZero F]` is REQUIRED — without
it the statement is false, refuted over `𝔽̄₂` in `NotExistsDual` above. -/
theorem End.exists_dual [IsAlgClosed F] [CharZero F] [W.IsElliptic] :
    ∃ D : End W →+ End W,
      ∀ ψ : End W, D ψ * ψ = ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : End W) :=
  ⟨AddMonoidHom.mk' End.dualEnd End.dualEnd_add, End.dualEnd_comp⟩

/-- Every endomorphism of an elliptic curve satisfies a monic quadratic
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

**PROVEN (2026-07-27)** over the parallelogram law
`End.degree_add_add_degree_sub` — itself PROVEN since the eighth pass of 2026-07-30
over the two route-2 leaves `End.exists_isXNormalForm_degree` and
`End.isXNormalForm_natDegree_parallelogram` — reached through
`End.self_add_dualEnd`, `End.dualEnd_add` and `End.exists_dual`. Note the `hsum` step below recovers the trace formula *from*
additivity — which is why the two are equivalent given the rest, and why the
first pass could see no way to get either without the other. (The direct route is
`charPoly_of_multiplicative_parallelogram` applied to `deg`, which reaches the
first conjunct here without going through `D` at all; this proof is left as it
stands because it also produces the Hasse bound.)
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

/-! ### The Weil pairing on the `ℓ`-torsion

The seventh pass (2026-07-28) made the existence of this pairing the file's only
leaf, on the ground that it "is *not* a statement about degrees at all", so that
moving the `sorry` onto it was "a reduction rather than the eighth lap of the
circle". The two theorems below **refute that**: both are proven, from the trace
formula and `deg = det` — the two faces of the circle the file already carries — with
no divisor theory, no Weil reciprocity and no characteristic-zero genericity layer.
See the ROUTE 2 section above for what this changes and what it does not.
-/

set_option backward.isDefEq.respectTransparency false in
/-- **The Weil pairing on the `ℓ`-torsion, adjoint for the dual isogeny — PROVEN
(2026-07-30, eighth pass).** Silverman *AEC* III.8.1 (existence, alternation,
nondegeneracy) together with III.8.2 (adjointness). For every prime `ℓ` there is an
alternating, nonzero, `ZMod ℓ`-bilinear pairing `e` on `W[ℓ]` with

    e (ψ x) y = e x (ψ̂ y)     for every ψ : End W.

### The proof, in three moves

1. **`e` is the coordinate determinant form** in `nTorsionBasis W ℓ`, which exists
   because the `ℓ`-torsion has rank `2` (`finrank_nTorsion`). Alternation is `ring`
   and nondegeneracy is `Finsupp.single_apply` on `e (b 0) (b 1) = 1`. This is
   verbatim the construction of `WeilPairing.exists_weilPairing`, whose Galois clause
   is obtained the same way from a determinant.
2. **`altPairing_trace`** (above): on a rank-`2` space *any* alternating form makes
   `f` and `tr f − f` adjoint, `tr f` being written `det (f + 1) − det f − 1`. The
   endomorphism `tr f − f` is the classical `2 × 2` adjugate, and `adj f · f = det f`
   is the only reason adjointness can hold at all.
3. **`ρ_ℓ ψ̂` IS that adjugate.** `End.self_add_dualEnd` gives `ψ + ψ̂ = [t]` with
   `t = deg (ψ + 1) − deg ψ − 1`, so applying the ring homomorphism `End.torsionRep`
   gives `ρ_ℓ ψ̂ = t − ρ_ℓ ψ`; and `End.natCast_degree_eq_det_torsionRep` converts
   both degrees in `t` into determinants, so `t ≡ det (ρ_ℓ ψ + 1) − det (ρ_ℓ ψ) − 1`
   in `ZMod ℓ`, which is exactly the bracket of move 2.

### What this says about the seventh pass's audit

The audit argued that the leaf could not be satisfied junkily because "on a rank-`2`
space an alternating bilinear form is determined up to a scalar, so the *only*
freedom in `e` is that scalar". That is correct, and it is also the reason the leaf
is **equivalent** to `deg = det` rather than stronger than it: a statement whose only
freedom is a scalar that the consumer then cancels cannot carry geometric
information. The audit used the implication in one direction and inferred that the
statement was outside the circle; the missing direction is the three moves above.

Consequently **the divisor-theoretic construction described in the seventh pass's
"Where to construct it" section is not on the critical path.** That section remains
accurate about the *state of this repository* — `mathlib` has no Weil pairing,
`~/cs/FLT`'s is a `sorry`ed `def`, and `WeilPairing.exists_weilPairing_mu` is over
`𝔽̄_q` with a Frobenius naturality clause — and it remains the right description of
what a genuinely divisor-theoretic pairing would cost. It is simply not what this
file needs. What it needs is route 2; see the ROUTE 2 section above. -/
theorem exists_weilPairing_torsionRep_adjoint [IsAlgClosed F] [CharZero F] [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ e : W.nTorsion ℓ →ₗ[ZMod ℓ] W.nTorsion ℓ →ₗ[ZMod ℓ] ZMod ℓ,
      (∀ v, e v v = 0) ∧ (∃ x y, e x y ≠ 0) ∧
        ∀ ψ : End W, ∀ x y, e (End.torsionRep W ℓ ψ x) y
          = e x (End.torsionRep W ℓ (End.dualEnd ψ) y) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  set b := nTorsionBasis W ℓ with hb
  set e : W.nTorsion ℓ →ₗ[ZMod ℓ] W.nTorsion ℓ →ₗ[ZMod ℓ] ZMod ℓ :=
    LinearMap.mk₂ (ZMod ℓ)
      (fun x y => b.coord 0 x * b.coord 1 y - b.coord 1 x * b.coord 0 y)
      (by intro m₁ m₂ n; simp only [map_add]; ring)
      (by intro c m n; simp only [map_smul, smul_eq_mul]; ring)
      (by intro m n₁ n₂; simp only [map_add]; ring)
      (by intro c m n; simp only [map_smul, smul_eq_mul]; ring) with he
  have halt : ∀ v, e v v = 0 := by
    intro v
    show b.coord 0 v * b.coord 1 v - b.coord 1 v * b.coord 0 v = 0
    ring
  refine ⟨e, halt, ⟨b 0, b 1, ?_⟩, ?_⟩
  · show b.coord 0 (b 0) * b.coord 1 (b 1) -
      b.coord 1 (b 0) * b.coord 0 (b 1) ≠ 0
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num [Finsupp.single_apply]
  · intro ψ x y
    set A := End.torsionRep W ℓ ψ with hA
    set c : ZMod ℓ := LinearMap.det (A + 1) - LinearMap.det A - 1 with hc
    have hstep : ∀ m : ℤ, ((m : ℤ) : Module.End (ZMod ℓ) (W.nTorsion ℓ))
        = ((m : ZMod ℓ)) • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) := by
      intro m; rw [← Algebra.algebraMap_eq_smul_one, map_intCast]
    -- move 3: on the torsion the dual is the adjugate `c − A`
    have hdual : End.torsionRep W ℓ (End.dualEnd ψ)
        = c • (1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) - A := by
      have ht := End.self_add_dualEnd (W := W) ψ
      have hmap := congrArg (End.torsionRep W ℓ) ht
      rw [map_add, map_intCast, hstep] at hmap
      have hcc : ((((Isogeny.degree (End.toIsogeny (ψ + 1)) : ℤ)
          - (Isogeny.degree (End.toIsogeny ψ) : ℤ) - 1 : ℤ) : ZMod ℓ)) = c := by
        rw [hc]
        push_cast
        rw [End.natCast_degree_eq_det_torsionRep ℓ (ψ + 1),
          End.natCast_degree_eq_det_torsionRep ℓ ψ, map_add, map_one, ← hA]
      rw [hcc, ← hA] at hmap
      rw [← hmap]
      abel
    rw [hdual]
    -- move 2: the adjugate identity for an alternating form in rank two
    have htr := altPairing_trace b e halt A x y
    have hone : ((1 : Module.End (ZMod ℓ) (W.nTorsion ℓ)) y) = y := rfl
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hone, map_sub,
      map_smul, smul_eq_mul]
    rw [← hc] at htr
    linear_combination htr

/-- **`deg ψ = det (ρ_ℓ ψ)` in `ZMod ℓ`, for every prime `ℓ`, by the Weil-pairing
route** — Silverman *AEC* III.8.6.

Three lines of mathematics: adjointness turns `e (ρ_ℓ ψ x) (ρ_ℓ ψ y)` into
`e x (ρ_ℓ (ψ̂ ψ) y)`; `End.dualEnd_comp` says `ψ̂ ψ = [deg ψ]`, so the pairing is
scaled by `deg ψ`; and an endomorphism scaling a nonzero alternating form on a
rank-`2` space by `c` has determinant `c` (`det_eq_of_altPairing_conj`, against
`p_torsion_rank`).

**The statement is `End.natCast_degree_eq_det_torsionRep` above, and this is a
SECOND proof of it, kept for the record rather than for a consumer.** Through the
seventh pass the two were separated by the direction of the argument: this one came
from the pairing and closed `End.exists_trace_charPoly`, while the other came from
the characteristic polynomial via the `ℓ`-adic argument. The eighth pass proves the
pairing itself over `End.natCast_degree_eq_det_torsionRep`, so this derivation is now
a round trip — the pairing's own audit predicts exactly that, since "any `e` meeting
the three clauses forces `deg ψ = det (ρ_ℓ ψ)`". It is retained because it is the
machine-checked half of the equivalence that the audits in this file describe, and
because deleting it would erase the evidence that the pairing carries no information
beyond the determinant.

Note there is **no case split on `ℓ ∣ deg ψ`** here — the pairing argument is uniform
in `ℓ`, whereas `End.natCast_degree_eq_det_torsionRep` assembles two cases. -/
theorem End.natCast_degree_eq_det_torsionRep_of_weilPairing [IsAlgClosed F] [CharZero F]
    [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (ψ : End W) :
    ((Isogeny.degree (End.toIsogeny ψ) : ℕ) : ZMod ℓ)
      = LinearMap.det (End.torsionRep W ℓ ψ) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨e, halt, hnd, hadj⟩ := exists_weilPairing_torsionRep_adjoint (W := W) ℓ
  have hrank : Module.rank (ZMod ℓ) (W.nTorsion ℓ) = 2 :=
    WeierstrassCurve.p_torsion_rank (E := W)
      (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  refine (det_eq_of_altPairing_conj hrank e halt hnd ?_).symm
  intro x y
  have h1 : e (End.torsionRep W ℓ ψ x) (End.torsionRep W ℓ ψ y)
      = e x (End.torsionRep W ℓ (End.dualEnd ψ) (End.torsionRep W ℓ ψ y)) :=
    hadj ψ x (End.torsionRep W ℓ ψ y)
  have h2 : End.torsionRep W ℓ (End.dualEnd ψ) (End.torsionRep W ℓ ψ y)
      = End.torsionRep W ℓ (End.dualEnd ψ * ψ) y := by
    rw [map_mul]; rfl
  rw [h1, h2, End.dualEnd_comp, map_natCast]
  simp [Module.End.natCast_apply, map_nsmul, nsmul_eq_mul]

end WeierstrassCurve
