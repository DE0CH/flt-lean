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

**Correction, 2026-07-28.**  This section used to say that everything
below is bookkeeping except four statements, "three of which are exactly
the modular input mathlib does not have":
`exists_frickeInvolution`, `isBigO_atTop_axisRestrict` and
`isBigO_atTop_coeff`, with `locallyIntegrableOn_axisRestrict` routine.
**Two of those three were already in mathlib when that was written**, so
the note sent work at a theory that did not need building:

* the rapid decay of a cusp form at `i∞` is
  `CuspFormClass.exp_decay_atImInfty`
  (`Mathlib/NumberTheory/ModularForms/QExpansion.lean`), needing only
  `1 ∈ Γ.strictPeriods`, i.e. `T ∈ Γ₀(N)`;
* Hecke's bound is `CuspFormClass.qExpansion_isBigO`
  (`Mathlib/NumberTheory/ModularForms/Bounds.lean`), the endpoint of a
  chain `petersson_bounded_left → exists_bound → qExpansion_isBigO`
  that needs `[Γ.IsArithmetic]` — which is where, and only where, the
  hypothesis `N ≠ 0` enters.

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

/-- **The Fricke involution `W_N`** (sorry leaf) — the ONE piece of
modular input that carries the continuation.

`W_N = ![![0, -1], ![N, 0]]` normalises `Γ₀(N)`, so `f ∣[2] W_N` is
again a cusp form on `Γ₀(N)`; writing `g` for it, the slash identity
`f (-1/(Nz)) = N z² g z` at `z = i y/√N` — where `-1/(Nz) = i/(√N y)`
and `N z² = -y²` — is exactly the displayed statement.

TRUE and classical (Atkin–Lehner; Diamond–Shurman §5.2).  What has to be
built for it, none of which exists at this pin: `W_N` as an element of
`GL(2, ℝ)`, the conjugation `W_N⁻¹ Γ₀(N) W_N = Γ₀(N)`, and the fact
that slashing by a normalising element preserves `CuspForm` — for the
last one the cusp condition is the only real work, since `W_N γ` for
`γ ∈ SL(2, ℤ)` is an integral matrix of determinant `N` and must be put
in Hermite normal form `γ' ![![α, β], ![0, δ]]` to see that zero-at-`∞`
is preserved.  The check that would refute this being missing:
`grep -rn "Fricke\|AtkinLehner\|atkinLehner" Fermat/
.lake/packages/mathlib/ ~/cs/FLT/` (run 2026-07-27: no hits). -/
theorem exists_frickeInvolution (N : ℕ) (hN : N ≠ 0) (f : CuspForm (Gamma0GL N) 2) :
    ∃ g : CuspForm (Gamma0GL N) 2, ∀ y : ℝ, 0 < y →
      axisRestrict N f (1 / y) = -((y ^ (2 : ℝ) : ℝ) : ℂ) * axisRestrict N g y :=
  sorry

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

end Fermat

end
