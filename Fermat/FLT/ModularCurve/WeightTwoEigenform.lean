/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.Analysis.Analytic.Basic

/-!
# Weight-two Hecke eigenforms on `Γ₀(N)` and their `L`-functions

This module writes down the *statement layer* that
`ModularCurve/X0.lean` needs in order to state Kolyvagin–Logachev, and
nothing else: it defines what it means for a `ℕ → ℂ` sequence to be the
normalized Hecke-eigenform `q`-expansion of a genuine weight-two cusp
form on `Γ₀(N)`, and what it means for a function `ℂ → ℂ` to be *the*
`L`-function of such a sequence.

Nothing here is a new theory: `CuspForm`, `CongruenceSubgroup.Gamma0`
and `LSeries` are all mathlib's.  What is new is only the packaging,
and the packaging is what makes the seam

> analytic input (`L(f, 1) ≠ 0`)  ⟶  arithmetic output (`J₀(N)(ℚ)` is torsion)

statable at all.

## Why the form itself is carried, and not just its coefficients

The single most dangerous way to write this interface is to define an
"eigenform" as a bare sequence `a : ℕ → ℂ` satisfying the Hecke
recursions.  That interface is **junk-satisfiable**: `a p := 0` for every
prime `p`, extended by the recursions, satisfies every displayed axiom
and is the `q`-expansion of no modular form whatsoever.  A leaf
quantifying universally over such sequences is FALSE; a leaf taking that
quantification as a hypothesis is VACUOUS.  Both failure modes are
recorded in the fleet doctrine and both are fatal.

So `IsWeightTwoEigenform` carries an actual
`f : CuspForm ↑(Γ₀ N) 2` — mathlib's honest object, holomorphic on `ℍ`,
weight-two invariant under `Γ₀(N)` and vanishing at every cusp — and
`a` is pinned to be its Fourier expansion.

### SOUNDNESS AUDIT (2026-07-27): carrying `f` was NOT by itself enough

The paragraph above used to end "there is then no junk witness", and
**that was false**, for a reason that only shows up once one remembers
what `∑'` means.  `tsum` of a family that is *not summable* is `0`.  So
the `qExpansion` field was satisfied by

> `f := 0`, and `a` the completely multiplicative sequence with
> `a_p := 2^{p²}` at every prime (extended by the Hecke recursions,
> which constrain nothing about the size of `a_p`),

because at every `τ ∈ ℍ` the terms `a_p q^p = 2^{p²} e^{-2πp·Im τ}` tend
to `∞`, the family is not summable, both sides are `0`, and `a 1 = 1`
holds.  A sequence growing that fast is the `q`-expansion of no modular
form whatsoever — exactly the failure mode this section claims to rule
out, reintroduced through the junk value of `tsum`.

It also made the sibling `lFunction_apply_one_ne_zero_of_kenkuLevel`
**FALSE as stated**: for that `a` the Dirichlet series diverges at every
`s`, so `LSeries a = 0`, so `L := 0` satisfies `IsLFunctionOf a L`, and
`L 1 = 0`.

**The repair is the `qExpansionSummable` field.**  With it, the
`q`-series converges on all of `ℍ`, hence defines a holomorphic function
of `q` on the punctured unit disc whose Taylor coefficients are unique;
so `a` really is determined by `f`, `f = 0` forces `a = 0`, and `a 1 = 1`
rules the junk out.  Adding a field only STRENGTHENS the hypothesis, so
every consumer in `X0.lean` — all of which take
`IsWeightTwoEigenform` as a hypothesis and none of which construct one —
is unaffected except that it becomes easier to prove.

## What the interface admits, exactly

By Atkin–Lehner theory the normalized simultaneous eigenvectors of
*all* of `T_p (p ∤ N)` and `U_p (p ∣ N)` in `S₂(Γ₀(N))` are exactly

* the newforms `g` of every level `M ∣ N` (each is literally an element
  of `S₂(Γ₀(N))`, since `Γ₀(N) ≤ Γ₀(M)`), and
* their `p`-stabilizations at the primes `p ∣ N`, `p ∤ M`.

That is a *larger* set than the newforms, and it is deliberate: it is
the set that can be pinned without first building the old/new
decomposition, which does not exist at this pin.  The enlargement is
**harmless for the `L`-value question**, and here is the check, because
a prover of `lFunction_apply_one_ne_zero_of_kenkuLevel` will need it.

A `p`-stabilization of `g` has
`L(f, s) = L(g, s) · ∏_{p ∣ N} (1 - β_p p^{-s})` where each `β_p` is a
root of the Hecke polynomial `X² - a_p(g) X + p` (or `0`).  By Deligne
`|β_p| ≤ √p < p`, so every correction factor at `s = 1` is
`1 - β_p / p ≠ 0`.  Hence

> `L(f, 1) ≠ 0` for every eigenform `f` in the sense below
> ⟺ `L(g, 1) ≠ 0` for every newform `g` of every level `M ∣ N`.

which is exactly the numerical statement that PARI/GP verifies.

## The `L`-function is pinned, not chosen

`IsLFunctionOf a L` asks `L` to be entire and to agree with the
Dirichlet series `∑ aₙ n^{-s}` on the half plane `Re s > 2`, where the
series converges absolutely by the trivial bound `|aₙ| = O(n)` for a
weight-two cusp form (Deligne's `O(n^{1/2+ε})` is *not* needed, which is
why the half plane is `Re s > 2` and not `Re s > 3/2`).  Two entire
functions agreeing on a nonempty open set agree everywhere, so `L 1` is
determined by `a`; that is checked by the (machine-verified, but
deliberately unstated — see its docstring) uniqueness argument recorded
on `IsLFunctionOf`, so the interface is demonstrably a *definition* of
`L(f, 1)` rather than a choice.

## RIVAL CARRIERS: WHAT IS ACTUALLY DUPLICATED, MEASURED (2026-07-28)

This tree carries **three** weight-two eigenform predicates, **two**
newform predicates and **two** `Gamma0GL`s.  A cut-level survey was run
on 2026-07-28; its conclusions are below so that nobody re-derives them,
and so that nobody performs the expensive half by mistake.

### `Gamma0GL`: NOT a duplication in any sense that costs anything

`Fermat.Gamma0GL` (here) and `GaloisRepresentation.Modularity.Gamma0GL`
(`Modularity/HeckeOperator.lean`) are **the same term**: mathlib's
coercion `Subgroup SL(2, ℤ) → Subgroup (GL (Fin 2) ℝ)` used here is
`coe := map (mapGL ℝ)` (`Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean:83`),
which is verbatim the other's body.  Machine-checked in a scratch
importing both: the equation is `rfl`, `CuspForm` over either is the
same type in both directions with no cast, and `heckeOp N n` applies
directly to a `CuspForm (Gamma0GL N) 2` written with the abbreviation
here.  **Do not unify them and do not write a bridge lemma** — see the
`Modularity/HeckeOperator.lean` module docstring for the full check and
for the one (harmless) reducibility asymmetry.

### The eigenform carriers: a REAL duplication, and its price

| carrier | where | shape | declarations mentioning it |
| --- | --- | --- | --- |
| `Fermat.IsWeightTwoEigenform N f a` | here | coefficients CARRIED, `qExpansion` + `qExpansionSummable` + general-`n` Hecke recursion | 6 here, 6 in `X0.lean` |
| `Fermat.IsWeightTwoEigenformOn G N χ f a` | `X1.lean` | the same with the group and a nebentypus as parameters; SUBSUMES the row above | 4 |
| `GaloisRepresentation.Modularity.IsWeightTwoEigenform N f` | `Interface.lean` | coefficients read off `qCoeff`; multiplicativity + prime-power recursions | 60 |
| `GaloisRepresentation.Modularity.IsWeightTwoNewform M g` | `Interface.lean` | the above + minimal-level | 63 |

Of the 60 `Interface.lean` declarations, **15 are PRODUCERS** (they
conclude `∃ f, IsWeightTwoEigenform …`) and 45 are consumers; for
`IsWeightTwoNewform` the split is 2 / 61.

### Two structural facts that decide the direction

1. **No hoist is needed to make the CARRIED carrier available downstream.**
   This module has no project imports and reaches `Interface.lean` through
   an unbroken chain of `public import`s
   (`X0` ← `FreyCurve/MazurTorsion` ← … ← `Interface`), so
   `Fermat.IsWeightTwoEigenform` is *already* nameable inside
   `Interface.lean`.  The reverse is impossible: `qCoeff` and
   `Modularity.IsWeightTwoEigenform` live in `Interface.lean`, which is
   downstream of `X0.lean`.
2. **Hoisting the `Interface.lean` carrier is feasible but buys nothing
   on its own.**  Reference scan (2026-07-28): the block
   `{qCoeff, IsWeightTwoEigenform, IsWeightTwoNewform,
   exists_weightTwoNewform_of_weightTwoEigenform}` references only
   `Gamma0GL`, mathlib's `UpperHalfPlane.qExpansion`, and itself — so it
   moves verbatim into `Modularity/HeckeOperator.lean` (same namespace,
   `public import`ed by `Interface.lean`) with **zero consumer text
   changed**.  But `X0.lean` still could not USE the result, because its
   leaves hold `(f, a, hf : IsWeightTwoEigenform N f a)` and the hoisted
   predicates speak about `qCoeff N f`.  Availability was never the whole
   blocker; the carrier mismatch is.

### The reconciliation, and its cost

Make the CARRIED carrier primitive — it is the stronger and safer one
(its `qExpansionSummable` field is what kills the junk witness recorded
in the `SOUNDNESS AUDIT` above, and its `hecke` field is the general-`n`
recursion rather than the prime-power one) — and restate
`Modularity.IsWeightTwoEigenform N f` as
`Fermat.IsWeightTwoEigenform N f (qCoeff N f)`.  Everything downstream
of `Interface.lean` that merely *consumes* a carrier is unaffected.

What it costs, and why it is not a one-agent job:

* one genuinely analytic new leaf — `IsWeightTwoEigenform N f a → qCoeff N f n = a n`,
  i.e. uniqueness of Fourier coefficients, identifying the carried `a`
  with mathlib's `UpperHalfPlane.qExpansion`;
* one elementary but real leaf — the general-`n` Hecke recursion is
  equivalent to multiplicativity plus the prime-power recursions;
* **15 + 2 producer proofs in `Interface.lean` must be extended** to
  supply the two extra fields, and 106 consumer statements retyped, in a
  60k-line file under concurrent ownership whose full build is measured
  in tens of minutes.

Until that is scheduled as its own task, the honest state is: the
carriers are *both* correct, they are *not* interchangeable, and any
statement needing both must go through the two leaves above.  A fourth
predicate (`IsNewEigenformAt`, `X0.lean`) exists precisely because of
this and should be retired by the reconciliation, not before it.

### One thing that IS cheap and is still undone

`X1.lean`'s `isWeightTwoEigenformOn_gamma0_iff` —
`IsWeightTwoEigenformOn (Gamma0GL N) N 1 f a ↔ IsWeightTwoEigenform N f a` —
is written out and machine-checked, but only inside a docstring code
block, so the two `Fermat`-side carriers are still formally unrelated.
Landing it as a declaration costs nothing once it has a consumer.
-/

@[expose] public section

open CongruenceSubgroup UpperHalfPlane Complex Matrix

open scoped MatrixGroups

noncomputable section

namespace Fermat

/-- `Γ₀(N)`, viewed inside `GL(2, ℝ)`, which is where mathlib's
`CuspForm` wants its group.  The coercion is `Subgroup.map (mapGL ℝ)`
and is injective, so this loses nothing. -/
abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- **`a` is the `q`-expansion of the normalized Hecke eigenform `f` in
`S₂(Γ₀(N))`.**

The fields are, in order: `a` is the Fourier expansion of `f`; that
expansion converges; `a₀ = 0`; `f` is normalized; `f` is an eigenvector
of `T_p` for `p ∤ N`; `f` is an eigenvector of `U_p` for `p ∣ N`.  In
both eigen-conditions the eigenvalue is forced to be `a p` by evaluating
at `n = 1`, so no eigenvalue is quantified.

`qExpansion` **together with** `qExpansionSummable` is what rules out
junk sequences, and neither may be dropped — see the `SOUNDNESS AUDIT`
in the module docstring, which records the junk witness that the first
alone admits. -/
structure IsWeightTwoEigenform (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) : Prop where
  /-- `a` is the Fourier expansion of `f`; the constant term is `0`
  because `f` is a cusp form, so the sum starts at `n = 1`. -/
  qExpansion : ∀ τ : ℍ,
    f τ = ∑' n : ℕ, a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))
  /-- The `q`-expansion CONVERGES.  Without this field the previous one
  is junk-satisfiable and the interface is unsound — see the
  `SOUNDNESS AUDIT` heading in the module docstring. -/
  qExpansionSummable : ∀ τ : ℍ,
    Summable fun n : ℕ => a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))
  /-- The `0`-th coefficient is `0`; `f` is a cusp form. -/
  zero : a 0 = 0
  /-- `f` is normalized. -/
  one : a 1 = 1
  /-- `f` is a `T_p`-eigenform for every prime `p ∤ N`, with eigenvalue
  `a p`.  For weight two `T_p` acts on `q`-expansions by
  `(T_p f)_n = a_{np} + p · a_{n/p}`. -/
  hecke : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, 0 < n →
    a (n * p) + (p : ℂ) * (if p ∣ n then a (n / p) else 0) = a p * a n
  /-- `f` is a `U_p`-eigenform for every prime `p ∣ N`, with eigenvalue
  `a p`.  `U_p` acts by `(U_p f)_n = a_{np}`. -/
  atkin : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, 0 < n → a (n * p) = a p * a n

/-! ### The carried sequence IS mathlib's `q`-expansion

Added 2026-07-31.  `IsWeightTwoEigenform` carries its coefficients as a
bare function `a : ℕ → ℂ` and ties them to `f` only through the
`qExpansion`/`qExpansionSummable` fields, i.e. analytically.  The three
lemmas below turn that analytic tie into the *identity*
`(UpperHalfPlane.qExpansion 1 f).coeff m = a m`, which is what makes any
statement about this carrier interchangeable with the same statement
about mathlib's `qExpansion` — and hence with
`GaloisRepresentation.Modularity.qCoeff N f m`, which is
`(UpperHalfPlane.qExpansion 1 f).coeff m` **by definition**
(`Modularity/Interface.lean`).

This is the "one genuinely analytic new leaf" that the RIVAL CARRIERS
survey in the module docstring above listed as the first cost of
reconciling the two carriers.  It is **not** a leaf: mathlib's
`ModularFormClass.qExpansion_coeff_unique` does the whole job, and the
only work is repackaging the tsum in the `qExpansion` field as a
`HasSum` over all of `ℕ` (the `m = 0` term vanishes by `zero`).  The
survey's cost estimate for that item should be read as discharged. -/

/-- `1` is a strict period of `Γ₀(N)` viewed in `GL(2, ℝ)`: the
translation `τ ↦ τ + 1` lies in `Γ₀(N)` for every `N`, so the width-`1`
`q`-expansion at the cusp `∞` is the classical Fourier expansion. -/
theorem one_mem_strictPeriods_Gamma0GL (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
  show (1 : ℝ) ∈
    (↑(CongruenceSubgroup.Gamma0 N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- The width-`1` `q`-parameter to the `m`-th power is `e(mτ)`, which is
the shape the `qExpansion` field of `IsWeightTwoEigenform` is written in. -/
theorem qParam_one_pow (τ : ℍ) (m : ℕ) :
    Function.Periodic.qParam 1 (τ : ℂ) ^ m
      = Complex.exp (2 * Real.pi * Complex.I * m * (τ : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Fourier series of `f` with the carried coefficients, as a
`HasSum` over ALL of `ℕ` — which is the hypothesis shape mathlib's
uniqueness lemma wants.  The `m = 0` summand is `a 0 • 1 = 0` by the
`zero` field, so extending the `qExpansion` field's sum over `n ≥ 1`
costs nothing. -/
theorem hasSum_qExpansion_of_isWeightTwoEigenform {N : ℕ} {f : CuspForm (Gamma0GL N) 2}
    {a : ℕ → ℂ} (hf : IsWeightTwoEigenform N f a) (τ : ℍ) :
    HasSum (fun m : ℕ => a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  have hfun : ∀ n : ℕ,
      a (n + 1) • Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1)
        = a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)) := by
    intro n
    rw [smul_eq_mul, qParam_one_pow]
    push_cast
    ring_nf
  have h1 : HasSum
      (fun n : ℕ => a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)))
      (f τ) := by
    rw [hf.qExpansion τ]
    exact (hf.qExpansionSummable τ).hasSum
  have h2 : HasSum
      (fun n : ℕ => a (n + 1) • Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1)) (f τ) := by
    simpa only [funext hfun] using h1
  have h3 := (hasSum_nat_add_iff (f := fun m : ℕ =>
    a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) 1).mp h2
  simpa [hf.zero] using h3

/-- **FOURIER UNIQUENESS: the carried sequence is mathlib's
`q`-expansion** (PROVEN 2026-07-31).

Both `qExpansion` and `qExpansionSummable` are used — the first supplies
the value of the sum, the second makes it a `HasSum` — which is a second,
independent reason neither field may be dropped (the `SOUNDNESS AUDIT`
in the module docstring gives the first).

Consumed by `isIntegral_coeff_prime_of_isWeightTwoEigenform` in
`ModularCurve/X0.lean`, which is now an assembly over
`isIntegral_qExpansionCoeff_prime` below. -/
theorem qExpansion_coeff_eq_of_isWeightTwoEigenform {N : ℕ} {f : CuspForm (Gamma0GL N) 2}
    {a : ℕ → ℂ} (hf : IsWeightTwoEigenform N f a) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 f).coeff m = a m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_Gamma0GL N)
    (hasSum_qExpansion_of_isWeightTwoEigenform hf) m).symm

/-- **SHIMURA'S ALGEBRAICITY THEOREM AT A PRIME, CARRIER-FREE** (sorry
leaf, new 2026-07-31) — `a_p` is an algebraic integer for every prime
`p`, stated about mathlib's own `q`-expansion coefficients and about no
project predicate at all.

TRUE, and classical (Shimura, *Introduction to the arithmetic theory of
automorphic functions* §3.5 and §7.5; Diamond–Shurman §6.5).  `T_n`
preserves the integral homology `H₁(X₀(N), ℤ)`, a lattice on which the
anemic Hecke algebra therefore acts by integer matrices, and `a p` is an
eigenvalue of one of them — so it is a root of a monic integer
characteristic polynomial.

**WHY THIS STATEMENT AND NOT THE CARRIED ONE — THE PROJECT HELD TWO
COPIES OF THIS THEOREM AND THIS IS THE COMMON REFINEMENT.**  As of
2026-07-31 the tree contained

* `Fermat.isIntegral_coeff_prime_of_isWeightTwoEigenform`
  (`ModularCurve/X0.lean`), over the CARRIED carrier, and
* `GaloisRepresentation.Modularity.isIntegral_qCoeff_prime_of_isWeightTwoEigenform`
  (`Modularity/Interface.lean`), over `qCoeff` and
  `Modularity.IsWeightTwoEigenform`,

both sorried, in two files with two eigenform predicates, so that closing
either closed nothing about the other.  The four hypotheses below are
*exactly* the four fields of `Modularity.IsWeightTwoEigenform` with
`qCoeff N f` unfolded to `(UpperHalfPlane.qExpansion 1 f).coeff` — which
is its definition — so that leaf is a one-line consequence of this one;
and `X0.lean`'s is now a PROVEN assembly over this one, through
`qExpansion_coeff_eq_of_isWeightTwoEigenform` above plus the two
prime-power specialisations of `hecke`/`atkin`.  **Closing this leaf
closes both.**  This module is upstream of both files, which is why the
common refinement can live here at all.

**THE HYPOTHESES ARE THE WEAKER (Modularity) SET, DELIBERATELY.**  The
carried carrier's general-`n` `hecke`/`atkin` fields IMPLY the two
prime-power recursions below, not conversely — the converse is the
second, elementary item in the RIVAL CARRIERS survey and is still
unwritten.  Taking the weaker hypotheses is what makes this statement
serve both consumers; it costs nothing, because every classical proof
of the theorem uses only these.

**FALSITY AUDIT, RUN AGAINST THIS STATEMENT AND NOT INHERITED**
(2026-07-31), per the standing rule that a restatement voids the earlier
audit.

`hN : N ≠ 0` IS LOAD-BEARING, and the level-`0` witness recorded on
`X0.lean`'s version transports here unchanged *because of Fourier
uniqueness*: `a (2 ^ k) := π ^ k`, `a n := 0` off the powers of `2`,
carried by `g τ = ∑_{k ≥ 1} π^k q^{2^k}`, has
`(qExpansion 1 g).coeff m = a m` by the lemma above, so it satisfies
`hone` (`a 1 = 1`), `hmul` (two coprime powers of `2` force one of them
to be `1`), `hgood` VACUOUSLY (`q ∣ 0` for every `q`, so no `q` passes
`¬ q ∣ N`) and `hbad` (`π^{r+1} = π · π^r` at `q = 2`, and `0 = 0 · 0`
at odd `q`).  `π` is transcendental and `2` is prime, so the conclusion
fails outright.

**The eigenform hypotheses are jointly load-bearing** for the obvious
reason: drop them and `f` is an arbitrary cusp form, whose coefficients
may be scaled by any transcendental.

**WHAT THIS STATEMENT NO LONGER NEEDS TO AUDIT.**  `X0.lean`'s version
carries a paragraph on both `q`-expansion fields of the carrier being
load-bearing, because without them the sequence `a` is junk-satisfiable
and unattached to `f`.  Here the coefficients ARE read off `f`, so that
failure mode does not exist and the audit item is discharged rather than
inherited.

**WHAT REMAINS GENUINELY MISSING** (re-checked 2026-07-31): the integral
homology `H₁(X₀(N), ℤ)` as a Hecke module exists neither here, nor in
mathlib at this pin, nor in `~/cs/FLT`.  Archimedean bounds cannot
substitute — `X0.lean` has `‖a_p‖ ≤ 2√p` and integrality is not an
archimedean condition; `1/2` satisfies every such bound.  A Hecke-stable
lattice and `IsIntegral ℤ (heckeEndo N q)` DO exist in
`Modularity/Interface.lean` and are sorry-free in source, but that file
is strictly downstream of this one AND its chain is circular against its
own copy of this theorem — read the CUT-OBSTRUCTION AUDIT on
`exists_trace_heckeOpN_int` there, which exhibits the cycle and
identifies the Eichler–Selberg trace formula (`Tr(T_m) ∈ ℤ`) as the
single non-circular arithmetic entry point.  A prover sent here should
take Eichler–Selberg or `H₁(X₀(N), ℤ)`, and should NOT start by building
a Hecke-stable lattice. -/
theorem isIntegral_qExpansionCoeff_prime (N : ℕ) (hN : N ≠ 0)
    (f : CuspForm (Gamma0GL N) 2)
    (hone : (UpperHalfPlane.qExpansion 1 f).coeff 1 = 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n →
      (UpperHalfPlane.qExpansion 1 f).coeff (m * n)
        = (UpperHalfPlane.qExpansion 1 f).coeff m * (UpperHalfPlane.qExpansion 1 f).coeff n)
    (hgood : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ r : ℕ,
      (UpperHalfPlane.qExpansion 1 f).coeff (q ^ (r + 2))
        = (UpperHalfPlane.qExpansion 1 f).coeff q
            * (UpperHalfPlane.qExpansion 1 f).coeff (q ^ (r + 1))
          - q * (UpperHalfPlane.qExpansion 1 f).coeff (q ^ r))
    (hbad : ∀ q : ℕ, q.Prime → q ∣ N → ∀ r : ℕ,
      (UpperHalfPlane.qExpansion 1 f).coeff (q ^ (r + 1))
        = (UpperHalfPlane.qExpansion 1 f).coeff q
            * (UpperHalfPlane.qExpansion 1 f).coeff (q ^ r))
    (p : ℕ) (hp : p.Prime) :
    IsIntegral ℤ ((UpperHalfPlane.qExpansion 1 f).coeff p) :=
  sorry

/-- **`L` is *the* `L`-function of the coefficient sequence `a`.**

Entire, and equal to the Dirichlet series `∑ aₙ n^{-s}` wherever that
series converges absolutely for a weight-two cusp form.

**This is a definition, not a choice, and the fact is MACHINE-CHECKED**
(2026-07-27): two entire functions agreeing on the nonempty open half
plane `Re s > 2` agree on all of `ℂ` by the identity theorem, so `L 1`
is determined by `a` and `IsLFunctionOf` is not a junk-satisfiable
recognition predicate.  That argument used to be recorded HERE, as a
docstring rather than a declaration, because it had no consumer and a
proven-but-unconsumed declaration is free-floating.  **It has a consumer
now** — `isTorsion_jacobian_of_lFunction_ne_zero` in
`ModularCurve/X0.lean` was decomposed on 2026-07-27 and its assembly uses
uniqueness to turn the `∃`-form of the analytic hypothesis (an
`L`-function it CHOSE) into the `∀`-form its leaves take ("*the*
`L`-function does not vanish at `1`") — so it is pasted back as
`isLFunctionOf_apply_eq` immediately below. -/
structure IsLFunctionOf (a : ℕ → ℂ) (L : ℂ → ℂ) : Prop where
  /-- `L` is entire. -/
  entire : AnalyticOnNhd ℂ L Set.univ
  /-- `L` agrees with the Dirichlet series on `Re s > 2`. -/
  eq_lseries : ∀ s : ℂ, 2 < s.re → L s = LSeries a s

/-- **The `L`-function of a coefficient sequence is UNIQUE** (PROVEN; the
identity theorem).

`IsLFunctionOf a L` pins `L` on the half plane `Re s > 2` and asks it to
be entire; two entire functions agreeing on a nonempty open subset of the
connected set `ℂ` agree everywhere.  Hence `L 1` is a function of `a`
alone, and `IsLFunctionOf` is a definition of `L(f, s)` rather than a
recognition predicate that several witnesses could satisfy differently.

Consumed by `isTorsion_jacobian_of_lFunction_ne_zero`; see the docstring
of `IsLFunctionOf` above for why it lived as a comment until then. -/
theorem isLFunctionOf_apply_eq {a : ℕ → ℂ} {L L' : ℂ → ℂ}
    (h : IsLFunctionOf a L) (h' : IsLFunctionOf a L') (s : ℂ) : L s = L' s := by
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (3 : ℂ) ∈ {z : ℂ | 2 < z.re} := by norm_num
  have key : Set.EqOn L L' Set.univ := by
    refine (h.entire.eqOn_of_preconnected_of_eventuallyEq h'.entire
      (isPreconnected_univ) (Set.mem_univ (3 : ℂ)) ?_)
    filter_upwards [hopen.mem_nhds hmem] with z hz
    rw [h.eq_lseries z hz, h'.eq_lseries z hz]
  exact key (Set.mem_univ s)

/-!
### Hecke's argument, decomposed

The classical proof is: restrict `f` to the imaginary axis, take the
Mellin transform, recognise it as `Γ(s)` times the Dirichlet series, and
get the continuation from the Fricke involution `W_N`, which converts
the behaviour at `y → 0` into the behaviour at `y → ∞`.

Mathlib carries the *analysis* of that argument already, in group-free
form: `WeakFEPair` (a pair of functions on `(0, ∞)` with rapid decay at
`∞` and `F (1/x) = ε x^k G x`), `IsStrongFEPair.differentiable_Λ` (the
Mellin transform of such an `F` is ENTIRE) and `hasSum_mellin` (the
Mellin transform of `∑ aₙ e^{-pₙ x}` is `Γ(s) ∑ aₙ pₙ^{-s}`).

So everything below is bookkeeping except the modular input mathlib does
not have:

* `exists_frickeInvolution` — the Fricke involution `W_N`.  **PROVEN
  2026-07-28**, from `frickeMatrix`/`frickeSlash` below;
* `isBigO_atTop_axisRestrict` — a cusp form decays rapidly at `i∞`.
  **PROVEN 2026-07-28**, and it needed no theory at all;
* `isBigO_atTop_coeff` — Hecke's bound `|aₙ| = O(n)`.  **PROVEN
  2026-07-28**, likewise;

**Correction, 2026-07-28, and it is worth reading before starting work in
this file.**  This section used to say that three of the four statements
below were "exactly the modular input mathlib does not have".  **Two of
those three were already in mathlib when that was written**, so the note
sent work at a theory that did not need building:

* the rapid decay of a cusp form at `i∞` is
  `CuspFormClass.exp_decay_atImInfty`
  (`Mathlib/NumberTheory/ModularForms/QExpansion.lean`), needing only
  `1 ∈ Γ.strictPeriods`, i.e. `T ∈ Γ₀(N)`;
* Hecke's bound is `CuspFormClass.qExpansion_isBigO`
  (`Mathlib/NumberTheory/ModularForms/Bounds.lean`), the endpoint of a
  chain `petersson_bounded_left → exists_bound → qExpansion_isBigO`
  that needs `[Γ.IsArithmetic]` — which is where, and only where, the
  hypothesis `N ≠ 0` enters.

Only `exists_frickeInvolution` was genuinely absent, and it too is now
closed.  The list that follows is retained for its statements:

All three of those leaves are now PROVEN.  **The one genuinely missing
piece of modular input is `exists_frickeInvolution`**: mathlib has no
Atkin–Lehner / Fricke involution at all (`grep -rn "Fricke\|AtkinLehner"`
over `Fermat/`, the pin and `~/cs/FLT`: no hits, re-checked 2026-07-28).
-/

section Hecke

open Filter Asymptotics MeasureTheory

/-- The point `i·y/√N` of the upper half plane.  The `√N` rescaling is
what turns the level-`N` Fricke involution `z ↦ -1/(Nz)` into the
level-free inversion `y ↦ 1/y` that `WeakFEPair` asks for. -/
def axisPoint (N : ℕ) (y : ℝ) (h : 0 < y ∧ N ≠ 0) : ℍ :=
  ⟨Complex.I * ((y / Real.sqrt N : ℝ) : ℂ), by
    have hs : (0 : ℝ) < Real.sqrt N :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero h.2)
    simpa using div_pos h.1 hs⟩

@[simp] lemma coe_axisPoint (N : ℕ) (y : ℝ) (h : 0 < y ∧ N ≠ 0) :
    ((axisPoint N y h : ℍ) : ℂ) = Complex.I * ((y / Real.sqrt N : ℝ) : ℂ) := rfl

/-- `f` restricted to the rescaled imaginary axis: `y ↦ f (i y / √N)`
for `y > 0`, and `0` elsewhere.  This is the function whose Mellin
transform is the completed `L`-function. -/
def axisRestrict (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (y : ℝ) : ℂ :=
  if h : 0 < y ∧ N ≠ 0 then f (axisPoint N y h) else 0

lemma axisRestrict_of_pos {N : ℕ} (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) {y : ℝ}
    (hy : 0 < y) : axisRestrict N f y = f (axisPoint N y ⟨hy, hN⟩) := dif_pos ⟨hy, hN⟩

/-!
#### The Fricke involution `W_N`

The one piece of modular input that carries the continuation.  Everything
in this subsection is PROVEN (2026-07-28).

An earlier version of this file recorded, as the work required, "`W_N` as
an element of `GL(2, ℝ)`, the conjugation `W_N⁻¹ Γ₀(N) W_N = Γ₀(N)`, and
the fact that slashing by a normalising element preserves `CuspForm` —
for the last one the cusp condition is the only real work, since `W_N γ`
must be put in Hermite normal form to see that zero-at-`∞` is preserved".

**The Hermite-normal-form step is NOT needed at this pin, and that is
what made this leaf cheap.**  Mathlib's `CuspForm Γ k` no longer asks for
vanishing at `∞` alone: its field is
`zero_at_cusps' : ∀ {c}, IsCusp c Γ → c.IsZeroAt toFun k`, quantified over
*every* cusp, and `OnePoint.IsZeroAt.smul_iff` says
`IsZeroAt (g • c) f k ↔ IsZeroAt c (f ∣[k] g) k` for **every**
`g : GL(2, ℝ)`.  So "`f ∣[2] W_N` vanishes at every cusp of `Γ₀(N)`" is
exactly "`f` vanishes at every `W_N`-translate of a cusp", and the whole
cusp obligation reduces to `isCusp_frickeMatrix_smul` — that `W_N`
permutes the cusps — which follows from the conjugation alone.  Nothing
has to be expanded at a cusp.

Likewise holomorphy is mathlib's `MDifferentiable.slash`, which holds for
the full `GL(2, ℝ)` slash action, not merely for `SL(2, ℤ)`.
-/

section Fricke

open scoped ModularForm

/-- **The Fricke matrix** `W_N = ![![0, -1], ![N, 0]]`, of determinant
`N` (PROVEN — a definition).

The determinant is positive, which is what makes `σ W_N` the identity and
keeps the slash action free of complex conjugation. -/
def frickeMatrix (N : ℕ) (hN : N ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0] (by
    have h : Matrix.det !![(0 : ℝ), -1; (N : ℝ), 0] = (N : ℝ) := by
      rw [Matrix.det_fin_two_of]; ring
    rw [h]
    exact_mod_cast hN)

@[simp] lemma frickeMatrix_coe (N : ℕ) (hN : N ≠ 0) :
    ((frickeMatrix N hN : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (N : ℝ), 0] :=
  rfl

@[simp] lemma frickeMatrix_det (N : ℕ) (hN : N ≠ 0) :
    ((frickeMatrix N hN).det : ℝ) = (N : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, frickeMatrix_coe, Matrix.det_fin_two_of]; ring

lemma frickeMatrix_det_pos (N : ℕ) (hN : N ≠ 0) : (0 : ℝ) < ((frickeMatrix N hN).det : ℝ) := by
  rw [frickeMatrix_det]
  exact_mod_cast Nat.pos_of_ne_zero hN

/-- **`W_N` normalises `Γ₀(N)`** (PROVEN).

If `γ = ![![a, b], ![c, d]]` lies in `Γ₀(N)`, so `N ∣ c` and `ad - bc = 1`,
then `W_N γ W_N⁻¹ = ![![d, -c/N], ![-N b, a]]`, whose determinant is
`da - (c/N)(N b) = ad - bc = 1` and whose lower-left entry `-N b` is
divisible by `N`.  The proof avoids `W_N⁻¹` by verifying the equivalent
identity `W_N γ = γ' W_N` on matrices.

Only this ONE inclusion is needed downstream — never the reverse
inclusion, and never the equality of subgroups — because both consumers
(`frickeSlash`'s slash-invariance and `isCusp_frickeMatrix_smul`) push
forward along `γ ↦ W_N γ W_N⁻¹`. -/
lemma frickeMatrix_conj_mem (N : ℕ) (hN : N ≠ 0) {g : GL (Fin 2) ℝ} (hg : g ∈ Gamma0GL N) :
    frickeMatrix N hN * g * (frickeMatrix N hN)⁻¹ ∈ Gamma0GL N := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨c', hc'⟩ : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  refine ⟨⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -c';
      -((N : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1), (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0], ?_⟩,
    ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc'
  · exact Gamma0_mem.mpr (by simp)
  · rw [eq_comm, mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc'] <;> ring

/-- **`W_N` maps cusps of `Γ₀(N)` to cusps of `Γ₀(N)`** (PROVEN).

`IsCusp c 𝒢` is `∃ g ∈ 𝒢, g.IsParabolic ∧ g • c = c`; the witness for
`W_N • c` is `W_N p W_N⁻¹`, which lies in `Γ₀(N)` by
`frickeMatrix_conj_mem`, is parabolic because parabolicity is a
conjugation invariant, and fixes `W_N • c` by the group action. -/
lemma isCusp_frickeMatrix_smul (N : ℕ) (hN : N ≠ 0) {c : OnePoint ℝ}
    (hc : IsCusp c (Gamma0GL N)) : IsCusp (frickeMatrix N hN • c) (Gamma0GL N) := by
  obtain ⟨p, hpΓ, hpar, hpc⟩ := hc
  refine ⟨frickeMatrix N hN * p * (frickeMatrix N hN)⁻¹, frickeMatrix_conj_mem N hN hpΓ,
    by simpa using hpar, ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, hpc]

/-- **The Fricke transform `f ∣[2] W_N` of a cusp form is again a cusp
form on `Γ₀(N)`** (PROVEN).

Slash-invariance: `(f ∣ W_N) ∣ γ = f ∣ (W_N γ) = f ∣ ((W_N γ W_N⁻¹) W_N)
= (f ∣ (W_N γ W_N⁻¹)) ∣ W_N = f ∣ W_N`.
Holomorphy: `MDifferentiable.slash`.
Vanishing at the cusps: `OnePoint.IsZeroAt.smul_iff` plus
`isCusp_frickeMatrix_smul`. -/
def frickeSlash (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) : CuspForm (Gamma0GL N) 2 where
  toFun := (f : ℍ → ℂ) ∣[(2 : ℤ)] frickeMatrix N hN
  slash_action_eq' γ hγ := by
    have key : frickeMatrix N hN * γ
        = frickeMatrix N hN * γ * (frickeMatrix N hN)⁻¹ * frickeMatrix N hN := by
      group
    rw [← SlashAction.slash_mul, key, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq (Γ := Gamma0GL N) (k := 2) f _
        (frickeMatrix_conj_mem N hN hγ)]
  holo' := (CuspFormClass.holo f).slash 2 (frickeMatrix N hN)
  zero_at_cusps' hc := by
    rw [← OnePoint.IsZeroAt.smul_iff]
    exact CuspFormClass.zero_at_cusps f (isCusp_frickeMatrix_smul N hN hc)

@[simp] lemma coe_frickeSlash (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) :
    (frickeSlash N hN f : ℍ → ℂ) = (f : ℍ → ℂ) ∣[(2 : ℤ)] frickeMatrix N hN := rfl

/-- **`W_N` sends `i y/√N` to `i (1/y)/√N`** (PROVEN) — the reason for the
`√N` rescaling in `axisPoint`.

`W_N • z = -1/(N z)`, and at `z = i y/√N` one has `N z = i y √N`, so
`-1/(N z) = i/(y √N)`. -/
lemma frickeMatrix_smul_axisPoint (N : ℕ) (hN : N ≠ 0) {y : ℝ} (hy : 0 < y) :
    frickeMatrix N hN • axisPoint N y ⟨hy, hN⟩ = axisPoint N (1 / y) ⟨by positivity, hN⟩ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (frickeMatrix_det_pos N hN), coe_axisPoint]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, frickeMatrix_coe, coe_axisPoint]
  norm_num
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hsC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hyC : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hs2 : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  rw [← hs2]
  field_simp
  exact Complex.I_sq.symm

/-- At level `N = 0` the axis restriction is identically `0`, because
`axisPoint` — and with it `axisRestrict` — is gated on `N ≠ 0`
(`Real.sqrt 0 = 0` would put the point on the real axis).  This is what
makes the two analytic leaves below true without a level hypothesis. -/
@[simp] lemma axisRestrict_zero_level (f : CuspForm (Gamma0GL 0) 2) :
    axisRestrict 0 f = fun _ : ℝ => (0 : ℂ) := by
  funext y
  simp [axisRestrict]

/-- **`1` is a strict period of `Γ₀(N)`, for every `N`** — the translation
`T = ![![1, 1], ![0, 1]]` lies in `Γ₀(N)` because its lower-left entry is
`0`.  This is the hypothesis that mathlib's `q`-expansion API takes in
place of "the width of the cusp `∞` is `1`", and it is what lets
`CuspFormClass.exp_decay_atImInfty` and
`ModularFormClass.qExpansion_coeff_unique` be applied at `h = 1`. -/
lemma one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
  rw [show (Gamma0GL N).strictPeriods = AddSubgroup.zmultiples (1 : ℝ) from
    CongruenceSubgroup.strictPeriods_Gamma0 N]
  exact AddSubgroup.mem_zmultiples 1

/-- The imaginary part of `i y/√N` is `y/√N`. -/
lemma im_axisPoint (N : ℕ) (y : ℝ) (h : 0 < y ∧ N ≠ 0) :
    (axisPoint N y h).im = y / Real.sqrt N := by
  simp [UpperHalfPlane.im]

/-- **The Fricke involution `W_N`** (PROVEN 2026-07-28) — the ONE piece of
modular input that carries the continuation.

`W_N = ![![0, -1], ![N, 0]]` normalises `Γ₀(N)`, so `f ∣[2] W_N` is
again a cusp form on `Γ₀(N)`; writing `g` for it, the slash identity
`f (-1/(Nz)) = N z² g z` at `z = i y/√N` — where `-1/(Nz) = i/(√N y)`
and `N z² = -y²` — is exactly the displayed statement.

Classical (Atkin–Lehner; Diamond–Shurman §5.2).  The witness is
`frickeSlash N hN f`; the sign `-1` and the weight `y²` come out of
`|det W_N|^{k-1} · denom(W_N, z)^{-k} = N · (i y √N)^{-2} = -1/y²`.

This is the root number `ε = -1` of `cuspFEPair`, and it is what makes
`Λ` entire, hence `L(f, ·)` entire. -/
theorem exists_frickeInvolution (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) :
    ∃ g : CuspForm (Gamma0GL N) 2, ∀ y : ℝ, 0 < y →
      axisRestrict N f (1 / y) = -((y ^ (2 : ℝ) : ℝ) : ℂ) * axisRestrict N g y := by
  refine ⟨frickeSlash N hN f, fun y hy => ?_⟩
  have hy' : (0 : ℝ) < 1 / y := by positivity
  rw [axisRestrict_of_pos hN f hy', axisRestrict_of_pos hN _ hy]
  simp only [coe_frickeSlash, ModularForm.slash_apply, frickeMatrix_smul_axisPoint N hN hy,
    UpperHalfPlane.σ, UpperHalfPlane.denom, frickeMatrix_coe, frickeMatrix_det, coe_axisPoint]
  norm_num
  rw [if_pos (Nat.pos_of_ne_zero hN), ContinuousAlgEquiv.refl_apply]
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hsC : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hyC : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hs2 : ((Real.sqrt N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg N)
  rw [← hs2]
  field_simp
  rw [Complex.I_sq]
  ring

end Fricke

/-- **A cusp form decays faster than every power at `i∞`** (PROVEN
2026-07-28).

`f (i y/√N)` is `O(e^{-2πy/√N})`, which beats `y ^ r` for every real
`r`.  It is stated for an arbitrary cusp form rather than for an
eigenform because the Fricke partner `g` above needs it too and is not
known to be an eigenform.

**The exponential decay is mathlib's**, not new modular input: the
docstring of the `Hecke's argument, decomposed` section above used to
list this leaf among "the modular input mathlib does not have", and that
was already false when written.  `CuspFormClass.exp_decay_atImInfty`
(`Mathlib/NumberTheory/ModularForms/QExpansion.lean`) gives
`f =O[atImInfty] fun τ ↦ exp (-2π (im τ)/h)` from nothing but `0 < h`
and `h ∈ Γ.strictPeriods`; here `h = 1` by `one_mem_strictPeriods`.  The
rest is transport along `y ↦ i y/√N` (whose imaginary part is `y/√N`,
so `atTop` pushes forward into `atImInfty`) followed by
`isLittleO_exp_neg_mul_rpow_atTop`.

No level hypothesis is needed: at `N = 0` the left-hand side is
identically `0` by `axisRestrict_zero_level`. -/
theorem isBigO_atTop_axisRestrict (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (r : ℝ) :
    axisRestrict N f =O[atTop] fun y : ℝ => y ^ r := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [axisRestrict_zero_level]
    exact isBigO_zero _ _
  · have hsq : (0 : ℝ) < Real.sqrt N :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
    have hdecay : (f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / 1) :=
      CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos (one_mem_strictPeriods N)
    rw [Asymptotics.isBigO_iff] at hdecay
    obtain ⟨c, hc⟩ := hdecay
    rw [UpperHalfPlane.atImInfty, Filter.eventually_comap, Filter.eventually_atTop] at hc
    obtain ⟨A, hA⟩ := hc
    have h1 : axisRestrict N f =O[atTop]
        fun y : ℝ => Real.exp (-(2 * Real.pi / Real.sqrt N) * y) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨c, ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (max 1 (A * Real.sqrt N))] with y hy
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hy)
      have hyA : A ≤ y / Real.sqrt N :=
        (le_div_iff₀ hsq).mpr ((le_max_right _ _).trans hy)
      have him : (axisPoint N y ⟨hy0, hN⟩).im = y / Real.sqrt N := im_axisPoint N y _
      have hb := hA (y / Real.sqrt N) hyA (axisPoint N y ⟨hy0, hN⟩) him
      rw [him] at hb
      rw [axisRestrict_of_pos hN f hy0]
      refine hb.trans_eq ?_
      rw [show -2 * Real.pi * (y / Real.sqrt N) / 1
        = -(2 * Real.pi / Real.sqrt N) * y from by ring]
    exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- **`f` restricted to the imaginary axis is locally integrable on
`(0, ∞)`** (PROVEN 2026-07-28) — it is continuous there, `f` being
holomorphic; the only content is transporting continuity through the
`ℍ`-coercion, which is an `IsEmbedding` (`UpperHalfPlane.isEmbedding_coe`),
so continuity into `ℍ` is continuity of the `ℂ`-valued composite.

No level hypothesis is needed: at `N = 0` the function is identically
`0` by `axisRestrict_zero_level`. -/
theorem locallyIntegrableOn_axisRestrict (N : ℕ) (f : CuspForm (Gamma0GL N) 2) :
    LocallyIntegrableOn (axisRestrict N f) (Set.Ioi 0) := by
  rcases eq_or_ne N 0 with rfl | hN
  · rw [axisRestrict_zero_level]
    exact (locallyIntegrable_const (0 : ℂ)).locallyIntegrableOn _
  · refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Ioi (0 : ℝ)) (axisRestrict N f)
        = fun y : Set.Ioi (0 : ℝ) => f (axisPoint N y.1 ⟨y.2, hN⟩) :=
      funext fun y => axisRestrict_of_pos hN f y.2
    rw [heq]
    refine (ModularFormClass.continuous f).comp ?_
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    simp only [Function.comp_def, coe_axisPoint]
    fun_prop

/-- The strong FE-pair attached to `f`: the pair `(f, f ∣ W_N)` read
along the rescaled imaginary axis, with weight `k = 2` and root number
`ε = -1`. -/
def cuspFEPair (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) : WeakFEPair ℂ where
  f := axisRestrict N f
  g := axisRestrict N (exists_frickeInvolution N hN f).choose
  k := 2
  ε := -1
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_axisRestrict N f
  hg_int := locallyIntegrableOn_axisRestrict N _
  hk := two_pos
  hε := by norm_num
  h_feq := fun x hx => by
    simpa [smul_eq_mul] using (exists_frickeInvolution N hN f).choose_spec x hx
  hf_top := fun r => by simpa using isBigO_atTop_axisRestrict N f r
  hg_top := fun r => by simpa using isBigO_atTop_axisRestrict N _ r

lemma isStrongFEPair_cuspFEPair (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) :
    IsStrongFEPair (cuspFEPair N hN f) := ⟨rfl, rfl⟩

/-- **`a` is the `q`-expansion coefficient sequence of `f` in mathlib's
sense** (PROVEN) — the bridge between this file's `IsWeightTwoEigenform`
packaging and `UpperHalfPlane.qExpansion`.

The two `qExpansion` fields say exactly that `∑_{n ≥ 1} aₙ qⁿ` converges
to `f τ` at every `τ ∈ ℍ` with `q = e^{2πiτ}`; adding the vanishing
constant term `a 0 = 0` turns that into a `HasSum` over all of `ℕ`, and
`ModularFormClass.qExpansion_coeff_unique` (the Taylor coefficients of a
holomorphic function on the punctured disc are unique) identifies it with
mathlib's `qExpansion 1 f`.  `h = 1` is legitimate by
`one_mem_strictPeriods`. -/
theorem coeff_eq_qExpansion_coeff {N : ℕ} {f : CuspForm (Gamma0GL N) 2} {a : ℕ → ℂ}
    (hf : IsWeightTwoEigenform N f a) (m : ℕ) :
    a m = (UpperHalfPlane.qExpansion 1 (f : ℍ → ℂ)).coeff m := by
  refine ModularFormClass.qExpansion_coeff_unique (k := 2) (h := 1) one_pos
    (one_mem_strictPeriods N) (fun τ => ?_) m
  have h0 : HasSum (fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))) ((f : ℍ → ℂ) τ) := by
    rw [hf.qExpansion τ]
    exact (hf.qExpansionSummable τ).hasSum
  have hfun : (fun n : ℕ => a (n + 1) • Function.Periodic.qParam 1 (τ : ℂ) ^ (n + 1))
      = fun n : ℕ => a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ)) := by
    funext n
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  refine (hasSum_nat_add_iff' (f := fun m : ℕ =>
    a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) 1).mp ?_
  have hzero : ∑ i ∈ Finset.range 1, a i • Function.Periodic.qParam 1 (τ : ℂ) ^ i = 0 := by
    simp [hf.zero]
  rw [hzero, sub_zero]
  simpa only [hfun] using h0

/-- **Hecke's bound `|aₙ| = O(n)`** (PROVEN 2026-07-28, after a FALSITY
REPAIR — see below).

TRUE for every weight-two cusp form on a genuine level, by the
contour-integral estimate
`aₙ = ∫₀¹ f(x + i/n) e^{-2πin(x+i/n)} dx` together with the fact that
`y |f(x+iy)|` is bounded on `ℍ` (the Petersson function of a cusp form
is bounded).  Deligne's `|aₙ| ≤ d(n) √n` is *not* needed, which is why
the half plane in `IsLFunctionOf` is `Re s > 2` rather than `Re s > 3/2`.

**All of that is in mathlib** and the docstring above claiming otherwise
("mathlib has `petersson` but not its boundedness") was already stale:
`Mathlib/NumberTheory/ModularForms/Bounds.lean` proves
`CuspFormClass.petersson_bounded_left`, `CuspFormClass.exists_bound` and
finally `CuspFormClass.qExpansion_isBigO`, which IS Hecke's bound,
`O(n^{k/2})`, for any **arithmetic** `Γ`.  All that is left here is the
identification of `a` with mathlib's coefficients
(`coeff_eq_qExpansion_coeff`) and `(2 : ℤ)/2 = 2 - 1`.

### FALSITY AUDIT (2026-07-28): `hN : N ≠ 0` is NOT decoration here either

The statement used to be quantified over every `N : ℕ`, and **at `N = 0`
it is FALSE**, by a counterexample of exactly the shape the module's
other `FALSITY AUDIT` uses.  Recall from there that the only cusp of
`Gamma0GL 0 = ⟨-I, T⟩` is `∞`, so — mathlib's `CuspForm.zero_at_cusps'`
being quantified over the cusps *of `Γ`* — a `CuspForm (Gamma0GL 0) 2`
is precisely a holomorphic, `1`-periodic `f : ℍ → ℂ` tending to `0` at
`i∞`.  Now take

> `a n := n ^ 10` for `n ≥ 1`, `a 0 := 0`, and
> `f τ := ∑_{n ≥ 1} n^10 e^{2πinτ}`.

Then `f` is holomorphic on `ℍ` (the series converges locally uniformly,
being dominated by a geometric series), `1`-periodic, and `→ 0` at
`i∞`, so `f ∈ CuspForm (Gamma0GL 0) 2`; the weight-two slash by `-I` is
trivial since `(cτ+d)^2 = 1` there.  Every field of
`IsWeightTwoEigenform 0 f a` holds: `qExpansion` and
`qExpansionSummable` by construction, `a 0 = 0`, `a 1 = 1`, `hecke` is
**vacuous** (`p ∣ 0` for every `p`, so `¬ p ∣ N` is never satisfied),
and `atkin` asks exactly that `a` be completely multiplicative, which
`n ↦ n^10` is.  But `a p = p^10` is not `O(p)`.

The defect is the same one the sibling audit records: `Γ₀(N)` has finite
index in `SL(2, ℤ)` exactly for `N ≥ 1`, so `Gamma0GL 0` is not an
arithmetic subgroup, its quotient has infinite volume, and every bound
that makes coefficients polynomially controlled fails.  Mechanically,
`CuspFormClass.qExpansion_isBigO` requires `[Γ.IsArithmetic]`, which is
available for `Gamma0GL N` exactly through `NeZero N`.  The repair is
therefore the hypothesis `hN`; the one consumer,
`lSeriesSummable_of_isWeightTwoEigenform`, is used only from
`mellin_axisRestrict`, which already carries `hN`. -/
theorem isBigO_atTop_coeff {N : ℕ} (hN : N ≠ 0) {f : CuspForm (Gamma0GL N) 2} {a : ℕ → ℂ}
    (hf : IsWeightTwoEigenform N f a) : a =O[atTop] fun n : ℕ => (n : ℝ) ^ (2 - 1 : ℝ) := by
  haveI : NeZero N := ⟨hN⟩
  have hbig := CuspFormClass.qExpansion_isBigO (Γ := Gamma0GL N) (k := 2) f
  rw [show (Gamma0GL N).strictWidthInfty = 1 from CongruenceSubgroup.strictWidthInfty_Gamma0 N,
    show ((2 : ℤ) : ℝ) / 2 = (2 - 1 : ℝ) from by norm_num] at hbig
  rw [show a = fun m : ℕ => (UpperHalfPlane.qExpansion 1 (f : ℍ → ℂ)).coeff m from
    funext (coeff_eq_qExpansion_coeff hf)]
  exact hbig

/-- The Dirichlet series of a weight-two cusp form converges absolutely
on `Re s > 2` (PROVEN, from `isBigO_atTop_coeff`). -/
theorem lSeriesSummable_of_isWeightTwoEigenform {N : ℕ} (hN : N ≠ 0)
    {f : CuspForm (Gamma0GL N) 2}
    {a : ℕ → ℂ} (hf : IsWeightTwoEigenform N f a) {s : ℂ} (hs : 2 < s.re) :
    LSeriesSummable a s :=
  LSeriesSummable_of_isBigO_rpow hs (isBigO_atTop_coeff hN hf)

/-- Along the rescaled imaginary axis the `q`-expansion is a genuine
convergent sum of real exponentials — the shape `hasSum_mellin` wants
(PROVEN, from the two `qExpansion` fields). -/
theorem hasSum_axisRestrict {N : ℕ} (hN : N ≠ 0) {f : CuspForm (Gamma0GL N) 2} {a : ℕ → ℂ}
    (hf : IsWeightTwoEigenform N f a) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ =>
        a (n + 1) * ((Real.exp (-(2 * Real.pi / Real.sqrt N * (n + 1)) * y) : ℝ) : ℂ))
      (axisRestrict N f y) := by
  have h := (hf.qExpansionSummable (axisPoint N y ⟨hy, hN⟩)).hasSum
  rw [← hf.qExpansion] at h
  rw [axisRestrict_of_pos hN f hy]
  have hEq : (fun n : ℕ =>
        a (n + 1) * ((Real.exp (-(2 * Real.pi / Real.sqrt N * (n + 1)) * y) : ℝ) : ℂ))
      = fun n : ℕ => a (n + 1) *
        Complex.exp (2 * Real.pi * Complex.I * (n + 1) * ((axisPoint N y ⟨hy, hN⟩ : ℍ) : ℂ)) := by
    funext n
    congr 1
    rw [Complex.ofReal_exp, coe_axisPoint]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (y : ℂ)) /
      ((Real.sqrt N : ℝ) : ℂ)) * Complex.I_sq
  rw [hEq]
  exact h

/-- **The Mellin transform of `f` on the axis is `Γ(s) (2π/√N)^{-s} L(f, s)`**
(PROVEN) — termwise integration of the `q`-expansion, i.e. mathlib's
`hasSum_mellin`. -/
theorem mellin_axisRestrict {N : ℕ} (hN : N ≠ 0) {f : CuspForm (Gamma0GL N) 2} {a : ℕ → ℂ}
    (hf : IsWeightTwoEigenform N f a) {s : ℂ} (hs : 2 < s.re) :
    mellin (axisRestrict N f) s =
      Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  set c : ℝ := 2 * Real.pi / Real.sqrt N with hcdef
  have hcpos : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hsummable : LSeriesSummable a s := lSeriesSummable_of_isWeightTwoEigenform hN hf hs
  -- the four hypotheses of `hasSum_mellin`
  have hp : ∀ n : ℕ, a (n + 1) = 0 ∨ 0 < c * (n + 1) := fun n => Or.inr (by positivity)
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ), HasSum
      (fun n : ℕ => a (n + 1) * ((Real.exp (-(c * (n + 1)) * t) : ℝ) : ℂ)) (axisRestrict N f t) :=
    fun t ht => hasSum_axisRestrict hN hf ht
  have hnorm : ∀ n : ℕ, ‖LSeries.term a s (n + 1)‖ = ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ s.re := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
    push_cast
    ring_nf
  have hsum : Summable fun n : ℕ => ‖a (n + 1)‖ / (c * ((n : ℝ) + 1)) ^ s.re := by
    have h1 : Summable fun n : ℕ => ‖LSeries.term a s (n + 1)‖ :=
      (summable_nat_add_iff 1).mpr (summable_norm_iff.mpr hsummable)
    refine (h1.mul_left (c ^ s.re)⁻¹).congr fun n => ?_
    rw [hnorm n, Real.mul_rpow hcpos.le (by positivity)]
    field_simp
  have H := hasSum_mellin hp hs0 hF hsum
  -- rewrite the summand as `(Γ s * c^{-s}) * term a s (n+1)`
  have Hterm : HasSum (fun n : ℕ => LSeries.term a s (n + 1)) (LSeries a s) := by
    have h0 : HasSum (LSeries.term a s) (LSeries a s) := hsummable.hasSum
    have h1 := (hasSum_nat_add_iff' (f := LSeries.term a s) 1).mpr h0
    rwa [Finset.sum_range_one, LSeries.term_zero, sub_zero] at h1
  have H2 := Hterm.mul_left (Complex.Gamma s * ((c : ℝ) : ℂ) ^ (-s))
  have hcs : ((c : ℝ) : ℂ) ^ s ≠ 0 := fun h => hcC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hEq : (fun n : ℕ =>
        Complex.Gamma s * a (n + 1) / ((c * ((n : ℝ) + 1) : ℝ) : ℂ) ^ s)
      = fun n : ℕ =>
        Complex.Gamma s * ((c : ℝ) : ℂ) ^ (-s) * LSeries.term a s (n + 1) := by
    funext n
    have hn0 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hns : (((n : ℝ) + 1 : ℝ) : ℂ) ^ s ≠ 0 :=
      fun h => hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hcpos.le (by positivity),
      LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg]
    rw [show (((n : ℕ) + 1 : ℕ) : ℂ) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [hEq] at H
  exact H.unique H2

end Hecke

/-- **Hecke: the `L`-function of a weight-two eigenform exists**
(DECOMPOSED 2026-07-27) — LEVEL-FREE, and one of the three theories
under `isTorsion_jacobian_of_kenkuLevel`.

TRUE and classical (Hecke, 1936).  The Mellin transform
`Λ(s) = ∫₀^∞ f(iy) y^{s-1} dy` converges for `Re s` large because `f`
decays exponentially at `i∞`, equals `(2π)^{-s} Γ(s) L(f, s)` there by
termwise integration of the `q`-expansion, and continues to an entire
function of `s` by splitting the integral at `y = 1/√N` and applying the
Fricke involution `f(i/(Ny)) = ± N y² f(iy)` to the piece near `0`.
Both remaining integrals converge for every `s`, so `Λ`, and therefore
`L`, is entire.  (`Λ` has no poles precisely because `f` is *cuspidal*;
for a non-cuspidal form one picks up poles from the constant terms.)

Absolute convergence on `Re s > 2` is the trivial bound: `y |f(x+iy)|`
is bounded on `ℍ` for a weight-two cusp form, so `|aₙ| = O(n)` by the
usual contour-integral estimate for Fourier coefficients.  Deligne's
`|aₙ| ≤ d(n) √n` would give `Re s > 3/2` and is **not** needed here.

`hf` is load-bearing in only one direction: `f` must be a genuine cusp
form.  The eigenform conditions are not used by Hecke's argument at all
— they are carried because this leaf's only consumer wants them — so a
prover may `omit` them, or generalize the statement to an arbitrary
`f : CuspForm (Gamma0GL N) 2` with `a` its `q`-expansion, and that
generalization is welcome.

### FALSITY AUDIT (2026-07-27): `hN : N ≠ 0` is NOT decoration

The statement used to be quantified over every `N : ℕ`, and **at
`N = 0` it is FALSE**.  The counterexample is completely explicit:

* `Gamma0 0 = {γ ∈ SL(2, ℤ) | γ 1 0 ≡ 0 [ZMOD 0]} = {γ | γ 1 0 = 0}`,
  i.e. `⟨-I, T⟩`.  Its parabolic elements are the `± Tⁿ`, `n ≠ 0`, all
  of which fix only `∞`, so by mathlib's `IsCusp c 𝒢 ↔ ∃ g ∈ 𝒢,
  g.IsParabolic ∧ g • c = c` the ONLY cusp of `Gamma0GL 0` is `∞`.
  Hence `CuspForm (Gamma0GL 0) 2` is just "holomorphic, `1`-periodic,
  `→ 0` at `i∞`" — an infinite-dimensional space with no arithmetic in
  it at all.
* `hecke` is **vacuous** at `N = 0`, since `p ∣ 0` for every `p`; and
  `atkin` then says exactly that `a` is completely multiplicative, with
  the `a_p` unconstrained.
* So take `a_p := 1` for every prime, i.e. `a n = 1` for `n ≥ 1` and
  `a 0 = 0`, and `f (τ) := ∑_{n≥1} qⁿ = q/(1 − q)`, which is
  holomorphic on `ℍ`, `1`-periodic, and vanishes at `i∞`.  Every field
  of `IsWeightTwoEigenform 0 f a` holds, `qExpansionSummable` included.
* But `LSeries a = riemannZeta` on `Re s > 1`, and `ζ` has a **pole at
  `s = 1`**: any entire `L` agreeing with `ζ` on `Re s > 2` would agree
  with `ζ` on the connected set `ℂ \ {1}` by the identity theorem, and
  then `(s − 1) L s → 0` while `(s − 1) ζ s → 1` (mathlib's
  `riemannZeta_residue_one`).  Contradiction, so no such `L` exists.

The defect is not in Hecke's theorem, it is in `Gamma0 0` not being a
level: `Γ₀(N)` has finite index in `SL(2, ℤ)` exactly for `N ≥ 1`, and
everything that makes `S₂(Γ₀(N))` finite-dimensional and its members'
coefficients polynomially bounded fails at `N = 0`.  The repair is
therefore the hypothesis `hN`, not a change of conclusion; the theorem
remains LEVEL-FREE among genuine levels.  The one consumer,
`isTorsion_jacobian_of_kenkuLevel`, supplies `N ≠ 0` from
`N ∈ kenkuLevels` in one line.

**The old IRREDUCIBILITY verdict is RETIRED (2026-07-27).**  It was
recorded along one axis — "mathlib has no continuation for the
`L`-series of a cusp form" — which is true and not the question.  The
axis NOT searched was the *abstract* one:
`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean` packages exactly
Hecke's argument in group-free form (`WeakFEPair`, `IsStrongFEPair`,
`IsStrongFEPair.differentiable_Λ`, `IsStrongFEPair.Λ_eq`), and
`Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean`'s `hasSum_mellin`
is the termwise integration.  Between them the *analysis* is done; what
remains is modular input, and that is what the four leaves above
isolate.  The node is therefore DECOMPOSED, not irreducible. -/
theorem exists_isLFunctionOf_of_isWeightTwoEigenform (N : ℕ) (hN : N ≠ 0)
    (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) (hf : IsWeightTwoEigenform N f a) :
    ∃ L : ℂ → ℂ, IsLFunctionOf a L := by
  have hstrong : IsStrongFEPair (cuspFEPair N hN f) := isStrongFEPair_cuspFEPair N hN f
  have hsq : (0 : ℝ) < Real.sqrt N :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN)
  have hcpos : (0 : ℝ) < 2 * Real.pi / Real.sqrt N := by positivity
  have hcC : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcpos.ne'
  refine ⟨fun s => ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s * (cuspFEPair N hN f).Λ s *
    (Complex.Gamma s)⁻¹, ?_, ?_⟩
  · -- entirety: a product of three entire functions
    rw [analyticOnNhd_univ_iff_differentiable]
    exact ((differentiable_id.const_cpow (Or.inl hcC)).mul
      hstrong.differentiable_Λ).mul Complex.differentiable_one_div_Gamma
  · -- agreement with the Dirichlet series on `Re s > 2`
    intro s hs
    have hΛ : (cuspFEPair N hN f).Λ s =
        Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s := by
      rw [congr_fun hstrong.Λ_eq s]
      exact mellin_axisRestrict hN hf hs
    have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcancel : ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hcC, add_neg_cancel, Complex.cpow_zero]
    show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s * (cuspFEPair N hN f).Λ s *
      (Complex.Gamma s)⁻¹ = LSeries a s
    rw [hΛ, show ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
        (Complex.Gamma s * ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s) * LSeries a s) *
        (Complex.Gamma s)⁻¹
      = (((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ s *
          ((2 * Real.pi / Real.sqrt N : ℝ) : ℂ) ^ (-s)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) * LSeries a s from by ring,
      hcancel, mul_inv_cancel₀ hΓ, one_mul, one_mul]


/-! ### Finite-dimensionality of `S₂(Γ₀(N))`

HOISTED here 2026-07-31 from `Modularity/Interface.lean`, where it was
proven 2026-07-24 and where it remains reachable under its old name (that
copy is now a one-line delegation to this one, so there is exactly one
proof).  The move is a HOIST and not a duplication: the argument is pure
mathlib — `ModularForm.norm` to level one, `sturm_bound_levelOne`, and the
`q`-expansion API — and it mentions no eigenform, no Hecke operator and no
scheme, so `Interface.lean` was never its natural home.

It was hoisted because `ModularCurve/X0.lean` needs it and is UPSTREAM of
`Interface.lean` (which carries `public import Fermat.FLT.ModularCurve.X0`),
so nothing in that file is nameable there: `finite_setOf_isWeightTwoEigenform`
is proven over this.  That leaf's docstring said mathlib at this pin "has no
finite-dimensionality of `CuspForm`" and that a prover would have to build the
valence formula or a degree bound.  The first clause is true and the second is
not — the project has had the theorem for a week, in a file that could not be
cited.  Standing lesson: an inventory audit is reliable about what MATHLIB
lacks and unreliable about what the PROJECT has, because a downstream file is
invisible to a `grep` that stops at "is it in scope here".
-/

section SturmFiniteness

open ModularForm Matrix.SpecialLinearGroup
open scoped Manifold

/-- The `m`-th `q`-expansion coefficient of a weight-`2` level-`N` cusp form,
as a `ℂ`-linear functional — additivity and scalar equivariance through the
pin's `qExpansion_add`/`qExpansion_smul`, which need analyticity of the cusp
function and hence `1` being a strict period. -/
noncomputable def qExpansionCoeffL (N m : ℕ) : CuspForm (Gamma0GL N) 2 →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 ⇑f).coeff m
  map_add' f g := by
    have hfa := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    have hga := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    show (qExpansion 1 ⇑(f + g)).coeff m = _
    rw [CuspForm.coe_add, qExpansion_add hfa hga]
    simp
  map_smul' c f := by
    have hfa := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    show (qExpansion 1 ⇑(c • f)).coeff m = _
    rw [CuspForm.IsGLPos.coe_smul, qExpansion_smul hfa]
    simp

@[simp] theorem qExpansionCoeffL_apply (N m : ℕ) (f : CuspForm (Gamma0GL N) 2) :
    qExpansionCoeffL N m f = (qExpansion 1 ⇑f).coeff m := rfl

/-- **Sturm bound for `S₂(Γ₀(N))`**: there is a finite bound `B` — here
`2·[SL(2,ℤ):Γ₀(N)]/12 + 1` — such that a weight-2 level-`N` cusp form whose
`q`-expansion coefficients `a_m` vanish for all `m < B` is zero.
General-level analogue of the classical Sturm bound, proven by the
norm-to-level-1 route made quantitative through the factorization
`norm f = f · (complementary product)`. -/
theorem exists_cuspForm_sturm_bound (N : ℕ) (hN : N ≠ 0) :
    ∃ B : ℕ, ∀ f : CuspForm (Gamma0GL N) 2,
      (∀ m < B, (qExpansion 1 ⇑f).coeff m = 0) → f = 0 := by
  classical
  haveI : NeZero N := ⟨hN⟩
  refine ⟨2 * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) / 12 + 1, fun f hcoeff => ?_⟩
  suffices hf0 : ⇑f = 0 from DFunLike.coe_injective (by rw [hf0, CuspForm.coe_zero])
  by_contra hf
  refine ModularForm.norm_ne_zero 𝒮ℒ hf ?_
  apply ModularForm.sturm_bound_levelOne
  letI := Fintype.ofFinite (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ)
  set q₀ : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ := ⟦1⟧ with hq₀
  set g : ℍ → ℂ :=
    ∏ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q with hgdef
  -- every element of `Γ₀(N)` stabilizes the identity coset
  have hfix : ∀ (γ : GL (Fin 2) ℝ) (hγSL : γ ∈ 𝒮ℒ), γ ∈ Gamma0GL N →
      (⟨γ, hγSL⟩ : 𝒮ℒ)⁻¹ • q₀ = q₀ := by
    intro γ hγSL hγ
    rw [hq₀]
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
      simpa [Subgroup.mem_subgroupOf] using hγ))
  have hfix' : ∀ (γ : GL (Fin 2) ℝ) (hγSL : γ ∈ 𝒮ℒ), γ ∈ Gamma0GL N →
      (⟨γ, hγSL⟩ : 𝒮ℒ) • q₀ = q₀ := by
    intro γ hγSL hγ
    conv_lhs => rw [← hfix γ hγSL hγ]
    rw [smul_inv_smul]
  -- hence permutes the complementary cosets: `g` is `Γ₀(N)`-slash-invariant
  have hslash : ∀ γ ∈ Gamma0GL N,
      g ∣[(2 * ((Finset.univ.erase q₀).card : ℤ))] γ = g := by
    intro γ hγ
    have hγSL : γ ∈ 𝒮ℒ := by
      rcases Subgroup.mem_map.mp hγ with ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    have habs : |γ.det.val| = 1 := Subgroup.HasDetPlusMinusOne.abs_det hγSL
    rw [hgdef, ModularForm.prod_slash, habs, _root_.one_zpow, one_smul]
    refine Finset.prod_equiv (MulAction.toPerm ((⟨γ, hγSL⟩ : 𝒮ℒ)⁻¹))
      (fun q => ?_) (fun q _ => ?_)
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true, MulAction.toPerm_apply]
      rw [not_iff_not, inv_smul_eq_iff, hfix' γ hγSL hγ]
    · simpa [MulAction.toPerm_apply] using
        SlashInvariantForm.quotientFunc_smul f hγSL q
  let G : SlashInvariantForm (Gamma0GL N) (2 * ((Finset.univ.erase q₀).card : ℤ)) :=
    ⟨g, hslash⟩
  have hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex G (one_mem_strictPeriods_Gamma0GL N)
  have hhol : MDiff g := by
    rw [hgdef]
    exact MDifferentiable.prod (Quotient.forall.mpr fun ⟨r, _⟩ _ =>
      (ModularForm.translate f r⁻¹).holo')
  have hqzero : ∀ q : 𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ,
      IsZeroAtImInfty (SlashInvariantForm.quotientFunc f q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      rw [SlashInvariantForm.quotientFunc_mk]
      have hinf : IsCusp OnePoint.infty 𝒮ℒ := isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩
      have hcusp : IsCusp ((r.val)⁻¹ • OnePoint.infty) (Gamma0GL N) :=
        (hinf.smul_of_mem (inv_mem r.2)).of_isFiniteRelIndex
      exact CuspFormClass.zero_at_cusps f hcusp _ rfl
  have hbdd : IsBoundedAtImInfty g := by
    rw [hgdef]
    exact Filter.BoundedAtFilter.prod _ fun q _ =>
      Filter.ZeroAtFilter.boundedAtFilter (hqzero q)
  have hganal : AnalyticAt ℂ (cuspFunction 1 g) 0 :=
    analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  have hfanal : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0GL N)
  have hfac : ⇑(ModularForm.norm 𝒮ℒ f) = ⇑f * g := by
    rw [ModularForm.coe_norm,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀), ← hgdef]
    congr 1
    rw [hq₀, SlashInvariantForm.quotientFunc_mk]
    simp
  rw [hfac, qExpansion_mul hfanal hganal]
  have horderf : ((2 * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) / 12 + 1 : ℕ) : ℕ∞)
      ≤ (qExpansion 1 ⇑f).order :=
    PowerSeries.nat_le_order _ _ fun i hi => hcoeff i hi
  have hcast : ((2 : ℤ) * (Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) : ℤ)).toNat
      = 2 * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) := by omega
  calc ((((2 : ℤ) * (Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12 : ℕ) : ℕ∞)
      < ((2 * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) / 12 + 1 : ℕ) : ℕ∞) := by
        rw [hcast]
        exact_mod_cast Nat.lt_succ_self _
    _ ≤ (qExpansion 1 ⇑f).order := horderf
    _ ≤ (qExpansion 1 ⇑f).order + (qExpansion 1 g).order := self_le_add_right _ _
    _ ≤ ((qExpansion 1 ⇑f) * qExpansion 1 g).order := PowerSeries.le_order_mul _ _


/-- **Finite dimensionality of `S₂(Γ₀(N))`**: the Sturm bound makes the
finitely many coefficient functionals `qExpansionCoeffL N 0, …,
qExpansionCoeffL N (B−1)` jointly injective, so the weight-2 cusp space
embeds `ℂ`-linearly into `Fin B → ℂ`.  This is the content of the
Diamond–Shurman ch. 3 dimension theory actually needed downstream, obtained
with no modular-curve geometry. -/
theorem cuspForm_finiteDimensional (N : ℕ) (hN : N ≠ 0) :
    FiniteDimensional ℂ (CuspForm (Gamma0GL N) 2) := by
  obtain ⟨B, hB⟩ := exists_cuspForm_sturm_bound N hN
  refine FiniteDimensional.of_injective
    (LinearMap.pi (fun i : Fin B => qExpansionCoeffL N (i : ℕ)))
    ((injective_iff_map_eq_zero _).mpr fun f hf => ?_)
  refine hB f fun m hm => ?_
  simpa [LinearMap.pi_apply] using congrFun hf ⟨m, hm⟩

end SturmFiniteness

end Fermat

end
