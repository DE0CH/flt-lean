/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.LSeries.Basic
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
`a` is pinned to be its Fourier expansion.  There is then no junk
witness: `a` is the `q`-expansion of a real cusp form or the structure
is uninhabited.

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

The four fields are, in order: `a` is the Fourier expansion of `f`; `f`
is normalized; `f` is an eigenvector of `T_p` for `p ∤ N`; `f` is an
eigenvector of `U_p` for `p ∣ N`.  In both eigen-conditions the
eigenvalue is forced to be `a p` by evaluating at `n = 1`, so no
eigenvalue is quantified.

`qExpansion` is what rules out junk sequences, and it may not be
dropped — see the module docstring. -/
structure IsWeightTwoEigenform (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) : Prop where
  /-- `a` is the Fourier expansion of `f`; the constant term is `0`
  because `f` is a cusp form, so the sum starts at `n = 1`. -/
  qExpansion : ∀ τ : ℍ,
    f τ = ∑' n : ℕ, a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * (n + 1) * (τ : ℂ))
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

/-- **Hecke: the `L`-function of a weight-two eigenform exists** (sorry
node) — LEVEL-FREE, and one of the three theories under
`isTorsion_jacobian_of_kenkuLevel`.

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

IRREDUCIBLE at this pin along the axis searched (Mellin transforms of
modular forms): mathlib has `mellin`, `Complex.Gamma`, and the
Hurwitz-zeta continuation machinery in `Mathlib/NumberTheory/LSeries/`,
but nothing that continues the `L`-series of a cusp form; the Fricke
involution `W_N` does not exist either.  The check that would refute
this: `grep -rn "mellin\|Fricke\|AtkinLehner" Fermat/
.lake/packages/mathlib/ ~/cs/FLT/`.  Note the *axis not searched*: a
converse-theorem or Eisenstein-regularization route, and the possibility
of avoiding continuation entirely by defining `L(f, 1)` as the period
integral `2π ∫₀^∞ f(iy) dy` — that would remove this leaf and change the
statement of `IsLFunctionOf`, and is a legitimate cut-level repair. -/
theorem exists_isLFunctionOf_of_isWeightTwoEigenform (N : ℕ)
    (f : CuspForm (Gamma0GL N) 2) (a : ℕ → ℂ) (hf : IsWeightTwoEigenform N f a) :
    ∃ L : ℂ → ℂ, IsLFunctionOf a L :=
  sorry

end Fermat

end
