module

/-
Descent.lean — the descent theorem, REWIRED ONTO MATHLIB (2026-07-28).

# What this module is now

`Mathlib/GroupTheory/Descent.lean` (Michael Stoll) **is** the descent
theorem, in three strengths, all proven upstream at pin `a3364fa`.  This
module used to re-prove it.  It no longer does: `fg_of_descentHeight` is
now a ten-line adapter over `AddCommGroup.fg_of_descent`, and what
survives here is exactly the material that has no upstream analogue,
plus the two interface structures the rest of this development consumes.

Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), Theorem
VIII.3.1 (the *Descent Theorem*), reads:

> Let `A` be an abelian group.  Suppose there is a function
> `h : A → ℝ` with
>
> (i) for each `Q ∈ A` there is a constant `C₁` with
>     `h (P + Q) ≤ 2 * h P + C₁` for all `P ∈ A`;
> (ii) there are an integer `m ≥ 2` and a constant `C₂` with
>     `h (m • P) ≥ m ^ 2 * h P − C₂` for all `P ∈ A`;
> (iii) for every `C₃` the set `{P ∈ A | h P ≤ C₃}` is finite.
>
> Suppose further that `A / mA` is finite.  Then `A` is finitely
> generated.

`DescentHeight A` bundles (i), (ii) and (iii) — with (iii) supplied by
`Mathlib`'s own `Northcott` class, which is literally this condition —
and `fg_of_descentHeight` is the theorem, obtained from upstream.

## Why the interface structures stay

The Mordell–Weil theorem for an abelian variety over `ℚ` is the
conjunction of three genuinely different things:

* **weak Mordell–Weil** — `A(ℚ) / n A(ℚ)` is finite;
* **the theory of heights** — a Weil height attached to a symmetric ample
  line bundle, with the quasi-parallelogram law, the quadraticity
  `h (m • P) = m² h P + O(1)` and Northcott's finiteness theorem;
* **the descent argument** itself, which combines the two.

Mathlib now supplies the third outright, and most of the second
(`Mathlib/NumberTheory/Height/`, six modules).  What it states the third
over is a *loose tuple of hypotheses*; `DescentHeight` and `WeilHeight`
bundle them, and it is those bundles — not the loose form — that the
sorried leaves of `ModularCurve/X0.lean` and
`ModularCurve/HyperellipticJacobian.lean` are stated against
(`Nonempty (DescentHeight …)`).  They are the consumed API, so they stay.

## THE RETIREMENT (2026-07-28) — what was deleted, and what replaced it

* **the 50-line minimal-counterexample proof of `fg_of_descentHeight`** →
  `AddCommGroup.fg_of_descent` at `a = 2`, `b = m²`, `n = m`, `c q = ` the
  translation constant of `−q`, `c₀ = ` the quadraticity constant.  The
  hypothesis shapes line up one-for-one; see the proof below.
* **`exists_finset_nsmul_repr`** — the coset-representative step.  It
  existed only to feed that proof; upstream does the same work internally
  from `(nsmulAddMonoidHom n).range.FiniteIndex`, and
  `AddSubgroup.finiteIndex_of_finite_quotient` bridges the two forms.
* **`ParallelogramHeight`, `ParallelogramHeight.exists_lowerBound`,
  `ParallelogramHeight.toDescentHeight`** — a field-for-field duplicate of
  `WeilHeight` inside this same file (`height`, an approximate
  parallelogram law, `Northcott`), differing only in whether the law was
  written `− 2 h P − 2 h Q` or `− (2 h P + 2 h Q)`.  Producers now target
  `WeilHeight`; `ProjectiveHeightSource.toParallelogramHeight` was renamed
  to `ProjectiveHeightSource.toWeilHeight` accordingly.

## What is genuinely OURS, and is why this file is not simply deleted

1. **`exists_lowerBound_of_northcott`, and with it the fact that
   `WeilHeight` needs NO nonnegativity hypothesis.**  Mathlib's
   `AddCommGroup.fg_of_descent'` assumes `H₂ : ∀ x, 0 ≤ h x`;
   `WeilHeight` does not, because Northcott already forces a lower bound
   (`{P | h P ≤ 0}` is finite, hence its image under `h` has a minimum).
   So `WeilHeight` is strictly the weaker ask of a producer.  That is
   also why the adapter below goes through `AddCommGroup.fg_of_descent`
   and not through the shorter `fg_of_descent'`: the primed version would
   re-impose the hypothesis this module exists to remove, and would also
   pin `m = 2`, which `DescentHeight` deliberately leaves free.
2. **`finite_quotient_nsmul_of_prime` / `finite_quotient_nsmul_mul`** —
   the reduction of weak Mordell–Weil from a general `n` to the primes:
   `A / (m k) A` sits in an extension of `A / mA` by a quotient of
   `A / kA`, and an induction on the prime factorisation does the rest.
   Nothing upstream does this.  It matters because the arithmetic input
   is much better behaved at a prime, where `A[p]` is an `𝔽_p`-vector
   space and so is every cohomology group built from it.
3. **`finite_quotient_nsmul_of_kummerCochains`** — the pure-algebra half
   of the Kummer reduction.  Also not upstream.  **It currently has no
   consumer**: release 12 (`d1a3ee9b`) cut weak Mordell–Weil a second way
   in `X0.lean` and rewired the assembly off it.  It is left in place
   rather than deleted, and reported, because deleting a sibling out from
   under a concurrent branch is the more expensive mistake.

Everything in this module is PROVEN; it contains no `sorry`.

## Upstream material NOT taken, and why

`AddCommGroup.finite_torsion_of_descent'` — the torsion subgroup is
finite from the parallelogram law alone, with **no** `G/2G` hypothesis —
has no analogue here and would be a natural `WeilHeight.finite_torsion`.
It was deliberately **not** added: nothing in this development consumes
finiteness of the torsion of a Mordell–Weil group.  The torsion leaves
that do exist (`finite_torsion_geomPt_of_abelianScheme` in `X0.lean`,
`finite_torsion_span_natCast` in `Modularity/TateModule.lean`) are about
`A[n](ℚ̄)` and about torsion submodules over a ring, neither of which is
`torsion (A(ℚ))` under a height.  Adding it now would be free-floating
code, which this project forbids.  Wire it in at the moment a consumer
is written — one line, `AddCommGroup.finite_torsion_of_descent' w.2`.

## The rest of the 2026-07-28 upstream survey, retained

**`Mathlib/NumberTheory/Height/` is the theory of heights** — six
modules: `Basic`, `Northcott`, `NumberField`, `Projectivization`,
`MvPolynomial`, `EllipticCurve`.  `Height.mulHeight` / `logHeight` on
tuples over any field with `Height.AdmissibleAbsValues`; that instance
holds for **every number field**, hence for `ℚ`; Northcott as a genuine
instance (`instance : Northcott (mulHeight₁ (K := K))`,
`Height/NumberField.lean:393`, and `Northcott (logHeight₁ (K := K))`
derived from it); `Rat.logHeight_eq_max_abs_of_gcd_eq_one`;
`Projectivization.mulHeight` / `logHeight`, well defined on projective
space; and the height machine for a family of homogeneous forms in BOTH
directions, `Height.logHeight_eval_le'` and `Height.logHeight_eval_ge'`.

`Height/EllipticCurve.lean` runs the elliptic-curve case in four lines
(`abs_logHeight_addSubMap_sub_two_mul_logHeight_le`), and is the model to
copy for anyone assembling a `WeilHeight` on `E(ℚ)`.

Both absences were originally recorded here as real, and both readings
came from grepping for `MordellWeil` / `NeronTateHeight` / `WeilHeight` —
none of which occurs anywhere in mathlib, which is exactly why the
absence read as real.

**What IS still genuinely absent, so this is not read too widely:**

* the **canonical (Néron–Tate) height** — mathlib has only the naive
  height; `canonicalHeight` and `neronTate` return nothing;
* the **naive height on an elliptic curve as a function on points**, and
  the approximate parallelogram law for it: `Height/EllipticCurve.lean`
  lists all three as `TODO`, and supplies only the morphism bound above;
* **Northcott on `Projectivization`** — `Height/Northcott.lean` lists it
  as `TODO`;
* **ampleness of line bundles and the theorem of the cube**
  (`grep -rn "TheoremOfTheCube\|VeryAmple\|IsAmple"` finds nothing in
  mathlib), which is what
  `exists_segreCoordinates_of_abelianScheme` in `ModularCurve/X0.lean`
  still carries;
* **weak Mordell–Weil** in any form, and the Mordell–Weil theorem itself;
* everything in `~/cs/FLT`: it really does have no height material at
  all (`grep -rlniE 'mulHeight|logHeight|northcott|weil height'` over the
  whole tree returns nothing).

Companion corrections: `Fermat/FLT/Mathlib/NumberTheory/IntegralHeight.lean`
and `Fermat/FLT/Mathlib/NumberTheory/SegreHeight.lean`.
-/

public import Mathlib.GroupTheory.Descent
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Order.Northcott
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Fermat

/-- **A height function for descent on an additive abelian group.**

The three hypotheses of Silverman's descent theorem (AEC VIII.3.1),
bundled with the integer `m` of hypothesis (ii):

* `translate` is (i), the quasi-parallelogram bound — for each `Q` the
  translate `P ↦ height (P + Q)` is bounded by `2 * height P` up to a
  constant depending on `Q`;
* `double` is (ii), quadraticity of the height in the direction that
  descent needs — multiplication by `m` multiplies the height by `m²`,
  up to a constant, and only the inequality `≥` is used;
* `northcott` is (iii), Northcott's finiteness property, taken from
  `Mathlib`'s `Northcott` class, whose `finite_le` field is exactly
  "`{P | height P ≤ C}` is finite for every `C`".

For an abelian variety over a number field, `height` is the Weil height
attached to a symmetric ample line bundle. -/
structure DescentHeight (A : Type*) [AddCommGroup A] where
  /-- the height function -/
  height : A → ℝ
  /-- the integer of the quadraticity hypothesis; descent needs `2 ≤ m` -/
  m : ℕ
  /-- descent needs `m` at least `2` -/
  two_le : 2 ≤ m
  /-- **(i)** for each `Q` there is a constant `C` with
  `height (P + Q) ≤ 2 * height P + C` for all `P` -/
  translate : ∀ Q : A, ∃ C : ℝ, ∀ P : A, height (P + Q) ≤ 2 * height P + C
  /-- **(ii)** there is a constant `C` with
  `m ^ 2 * height P ≤ height (m • P) + C` for all `P` -/
  double : ∃ C : ℝ, ∀ P : A, (m : ℝ) ^ 2 * height P ≤ height (m • P) + C
  /-- **(iii)** every set `{P | height P ≤ C}` is finite -/
  northcott : Northcott height

/-- **The descent theorem** (PROVEN) — Silverman, *AEC* Theorem VIII.3.1.

An abelian group carrying a height function in the sense of
`DescentHeight`, and whose quotient by `m A` is finite for the `m` of
that height, is finitely generated.

This is the group-theoretic half of the Mordell–Weil theorem: given weak
Mordell–Weil (the `hq` hypothesis) and a theory of heights (the `dh`
hypothesis), finite generation follows with no further arithmetic.

**RETIRED ONTO MATHLIB, 2026-07-28.**  This used to be a 50-line
minimal-counterexample argument (choose coset representatives, take a
non-generated point of least height, descend one step, contradict
minimality).  `Mathlib/GroupTheory/Descent.lean` proves exactly that, so
all that is left here is the translation of `DescentHeight`'s three
fields into `AddCommGroup.fg_of_descent`'s five hypotheses:

| here | upstream |
|---|---|
| `dh.height` | `h` |
| `dh.m` | `n` |
| `2` (the coefficient in `translate`) | `a` |
| `(dh.m : ℝ) ^ 2` (from `double`) | `b` |
| `dh.two_le` | `0 ≤ a < b`, since `m ≥ 2` gives `m² ≥ 4 > 2` |
| `dh.translate (-g)` | `H₂ : ∀ g x, h x ≤ a * h (g + x) + c g` |
| `dh.double` | `H₃ : ∀ x, b * h x - c₀ ≤ h (n • x)` |
| `hq` | `H₁ : (nsmulAddMonoidHom n).range.FiniteIndex` |
| `dh.northcott` | `[Northcott h]` |

Two of those are not verbatim.  `H₂` wants the *inverse* direction of
`translate` — a bound on `h x` in terms of `h (g + x)`, not the other way
round — and it is obtained by instantiating `translate (-g)` at `g + x`,
which is why `c g` is the constant attached to `−g` rather than to `g`.
And `hq` is stated as finiteness of the quotient rather than as
`FiniteIndex` of the subgroup; `AddSubgroup.finiteIndex_of_finite_quotient`
is the bridge.

Note this goes through `AddCommGroup.fg_of_descent` and **not** through
the shorter `AddCommGroup.fg_of_descent'`: the primed version fixes
`n = 2`, which `DescentHeight` deliberately leaves free, and assumes
`0 ≤ h`, which is the hypothesis `WeilHeight` exists to avoid. -/
theorem fg_of_descentHeight {A : Type*} [AddCommGroup A] (dh : DescentHeight A)
    (hq : Finite (A ⧸ (nsmulAddMonoidHom dh.m : A →+ A).range)) :
    AddGroup.FG A := by
  haveI := dh.northcott
  haveI := hq
  haveI : ((nsmulAddMonoidHom dh.m : A →+ A).range).FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite_quotient
  obtain ⟨C₂, hC₂⟩ := dh.double
  choose Cf hCf using fun q : A => dh.translate (-q)
  have hab : (2 : ℝ) < (dh.m : ℝ) ^ 2 := by
    have h2m : (2 : ℝ) ≤ (dh.m : ℝ) := by exact_mod_cast dh.two_le
    nlinarith
  refine AddCommGroup.fg_of_descent (n := dh.m) (h := dh.height) (a := 2)
    (b := (dh.m : ℝ) ^ 2) (c₀ := C₂) (c := Cf) (by norm_num) hab inferInstance
    (fun g x => ?_) (fun x => ?_)
  · have h := hCf g (g + x)
    have hx : g + x + -g = x := by abel
    rwa [hx] at h
  · linarith [hC₂ x]

/-! ## From a quasi-parallelogram law to a descent height -/

/-- **A Northcott height is bounded below** (PROVEN).

Northcott's property is a finiteness statement, not an inequality, but it
forces a lower bound all the same: `{P | height P ≤ 0}` is finite, so
`height` takes only finitely many values `≤ 0` and they have a minimum.

This is the one step of `WeilHeight.toDescentHeight` that is not pure
rearrangement, and it is what lets the *two-sided* parallelogram bound
below imply the *one-sided* translation bound of `DescentHeight`. -/
theorem exists_lowerBound_of_northcott {A : Type*} (height : A → ℝ) [Northcott height] :
    ∃ B : ℝ, ∀ P : A, B ≤ height P := by
  obtain ⟨b, hb⟩ := ((Northcott.finite_le (h := height) 0).image height).bddBelow
  refine ⟨min b 0, fun P => ?_⟩
  by_cases hP : height P ≤ 0
  · exact le_trans (min_le_left _ _) (hb ⟨P, hP, rfl⟩)
  · exact le_trans (min_le_right _ _) (not_le.mp hP).le

/-- **A Weil height on an additive abelian group**: the
quasi-parallelogram law plus Northcott's finiteness property.

This is the shape in which the theory of heights on an abelian variety
actually delivers its output, and it is strictly easier to supply than
`DescentHeight`:

* one constant instead of a family, and it is uniform in *both*
  variables — `translate` in `DescentHeight` allows the constant to
  depend on `Q`, and here it does not;
* two-sided, so the producer never has to think about which direction of
  quadraticity descent consumes;
* no choice of `m` — `toDescentHeight` takes `m = 2`.

For an abelian variety `A` over a number field with a symmetric ample
line bundle `L`, `height` is the Weil height `h_L` and
`quasiParallelogram` is the theorem of the cube; `northcott` is
Northcott's theorem.  Note that `quasiParallelogram` at `Q = P` already
contains the quadraticity `h (2 P) = 4 h P + O(1)` that descent needs, so
nothing else has to be assumed. -/
structure WeilHeight (A : Type*) [AddCommGroup A] where
  /-- the height function -/
  height : A → ℝ
  /-- the **quasi-parallelogram law**: one constant, uniform in `P` and `Q` -/
  quasiParallelogram : ∃ C : ℝ, ∀ P Q : A,
    |height (P + Q) + height (P - Q) - (2 * height P + 2 * height Q)| ≤ C
  /-- every set `{P | height P ≤ C}` is finite -/
  northcott : Northcott height

/-- **A Weil height is a descent height, with `m = 2`** (PROVEN).

`translate`: the `≤` half of the parallelogram law gives
`h (P + Q) ≤ 2 h P + 2 h Q + C − h (P − Q)`, and `h` is bounded below by
`exists_lowerBound_of_northcott`, so the last term is bounded uniformly
in `P`.

`double`: the `≥` half at `Q = P` gives
`4 h P ≤ h (P + P) + h 0 + C`, which is the quadraticity bound for
`m = 2` with constant `h 0 + C`. -/
def WeilHeight.toDescentHeight {A : Type*} [AddCommGroup A] (w : WeilHeight A) :
    DescentHeight A where
  height := w.height
  m := 2
  two_le := le_refl 2
  translate := by
    haveI := w.northcott
    obtain ⟨C, hC⟩ := w.quasiParallelogram
    obtain ⟨B, hB⟩ := exists_lowerBound_of_northcott w.height
    intro Q
    refine ⟨2 * w.height Q + C - B, fun P => ?_⟩
    have h := abs_le.mp (hC P Q)
    have hb := hB (P - Q)
    linarith [h.1, h.2]
  double := by
    obtain ⟨C, hC⟩ := w.quasiParallelogram
    refine ⟨w.height 0 + C, fun P => ?_⟩
    have h := abs_le.mp (hC P P)
    rw [sub_self] at h
    have hcast : ((2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num
    rw [hcast, two_nsmul]
    linarith [h.1]
  northcott := w.northcott

/-! ## Reducing `A / nA` to the prime case -/

/-- **`A / 1·A` is trivial, hence finite** (PROVEN) — the base case of the
induction in `finite_quotient_nsmul_of_prime`. -/
theorem finite_quotient_nsmul_one {A : Type*} [AddCommGroup A] :
    Finite (A ⧸ (nsmulAddMonoidHom 1 : A →+ A).range) := by
  have htop : (nsmulAddMonoidHom 1 : A →+ A).range = ⊤ :=
    eq_top_iff.mpr fun x _ => ⟨x, by simp⟩
  rw [htop]
  haveI := QuotientAddGroup.subsingleton_quotient_top (G := A)
  exact Finite.of_subsingleton

/-- **`A / nA` is multiplicative in `n`** (PROVEN).

Write `N = (m k) A ≤ M = m A`.  Noether's third isomorphism theorem
identifies `(A / N) / (M / N)` with `A / M`, which is finite by
hypothesis; and `M / N` — the image of `M` in `A / N` — is the range of
`P ↦ m • P mod N`, a homomorphism killing `k A`, hence a quotient of
`A / kA` and finite too.  A group with a finite subgroup and a finite
quotient by it is finite. -/
theorem finite_quotient_nsmul_mul {A : Type*} [AddCommGroup A] {m k : ℕ}
    (hm : Finite (A ⧸ (nsmulAddMonoidHom m : A →+ A).range))
    (hk : Finite (A ⧸ (nsmulAddMonoidHom k : A →+ A).range)) :
    Finite (A ⧸ (nsmulAddMonoidHom (m * k) : A →+ A).range) := by
  classical
  haveI := hm
  haveI := hk
  have hle : (nsmulAddMonoidHom (m * k) : A →+ A).range
      ≤ (nsmulAddMonoidHom m : A →+ A).range := by
    rintro _ ⟨P, rfl⟩
    exact ⟨k • P, by simp [smul_smul]⟩
  set N : AddSubgroup A := (nsmulAddMonoidHom (m * k) : A →+ A).range with hNdef
  set M : AddSubgroup A := (nsmulAddMonoidHom m : A →+ A).range with hMdef
  set K : AddSubgroup A := (nsmulAddMonoidHom k : A →+ A).range with hKdef
  set φ : A →+ (A ⧸ N) := (QuotientAddGroup.mk' N).comp (nsmulAddMonoidHom m) with hφdef
  have hker : K ≤ φ.ker := by
    rintro _ ⟨P, rfl⟩
    have hmem : ((m * k) • P : A) ∈ N := ⟨P, rfl⟩
    have h0 : ((((m * k) • P : A) : A ⧸ N)) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hmem
    simpa [hφdef, smul_smul] using h0
  have hsub : ((M.map (QuotientAddGroup.mk' N) : AddSubgroup (A ⧸ N)) : Set (A ⧸ N))
      ⊆ Set.range (QuotientAddGroup.lift K φ hker) := by
    rintro y ⟨x, ⟨P, rfl⟩, rfl⟩
    exact ⟨QuotientAddGroup.mk P, rfl⟩
  haveI : Finite (M.map (QuotientAddGroup.mk' N)) :=
    Set.Finite.to_subtype ((Set.finite_range _).subset hsub)
  haveI : Finite ((A ⧸ N) ⧸ M.map (QuotientAddGroup.mk' N)) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientQuotientEquivQuotient N M hle).symm.toEquiv
  exact Finite.of_addSubgroup_quotient (M.map (QuotientAddGroup.mk' N))

/-- **Weak Mordell–Weil at every `n ≠ 0` follows from weak Mordell–Weil at
every prime** (PROVEN).

Induct on the prime factorisation of `n` using
`finite_quotient_nsmul_mul`, with `finite_quotient_nsmul_one` as the base
case.  `n ≠ 0` is load-bearing and cannot be dropped: `A / 0·A = A`, which
is infinite for every abelian variety of positive rank. -/
theorem finite_quotient_nsmul_of_prime {A : Type*} [AddCommGroup A]
    (hp : ∀ p : ℕ, p.Prime → Finite (A ⧸ (nsmulAddMonoidHom p : A →+ A).range))
    (n : ℕ) (hn : n ≠ 0) :
    Finite (A ⧸ (nsmulAddMonoidHom n : A →+ A).range) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · rw [← h1]; exact finite_quotient_nsmul_one
    · obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      obtain ⟨q, rfl⟩ := hpd
      have hq0 : q ≠ 0 := by rintro rfl; simp at hn
      have hp2 : 2 ≤ p := hpp.two_le
      have hqlt : q < p * q :=
        calc q = 1 * q := (one_mul q).symm
        _ < p * q := Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl q) (Nat.pos_of_ne_zero hq0)
      exact finite_quotient_nsmul_mul (hp p hpp) (ih q hqlt hq0)

/-! ## The Kummer reduction of weak Mordell–Weil

Weak Mordell–Weil is `A(K) / nA(K)` finite.  Its classical proof
(Silverman, *AEC* VIII.1) never argues about that quotient directly: it
builds the **Kummer map**, which turns an element of the quotient into a
cochain on the Galois group, and then proves that only finitely many
such cochains occur.  The theorem below is the *reduction* — the step
that converts "finitely many cochains" into "finite quotient" — and it
is pure algebra: no fields, no schemes, no topology, no cohomology
theory.

The arithmetic of weak Mordell–Weil is entirely in the hypothesis
`hfin`, and this theorem carries none of it. -/

/-- **The Kummer reduction: `A / nA` is finite as soon as only finitely
many Kummer cochains occur** (PROVEN) — Silverman, *AEC* VIII.1, in the
form the abelian-scheme development consumes.

The setting is the algebraic skeleton of the classical argument.  `M`
plays the role of `A(K̄)`, `Γ` of the Galois group, `act` of the Galois
action, and `ι` of the inclusion `A(K) ↪ A(K̄)`:

* `hact` — `act σ` is subtractive.  It is all that is used of the action:
  no group law on `Γ`, no action axioms, no continuity.  (`Γ` is not even
  assumed to be a group, precisely to make that visible.)
* `hzero`, `hadd` — `ι` is additive.  Bundling `ι` as an `A →+ M` in the
  statement would force every caller to build the bundled map first; the
  two field equations are what a functor-of-points producer actually has
  in hand.
* `hinj` — `ι` is injective, i.e. `A(K) → A(K̄)` loses nothing.
* `hfix` — **Galois descent**: an `act`-invariant element of `M` comes
  from `A`.  Together with `hinj` this says `ι` identifies `A` with
  `M^Γ`; only the stated inclusion is used.
* `hdiv` — **divisibility**: every element of `ι '' A` is `n` times
  something in `M`.  Over an algebraically closed field this is
  surjectivity of the isogeny `[n]`.
* `hfin` — **the arithmetic**: only finitely many *Kummer cochains*
  `σ ↦ act σ Q - Q` (over all `P : A` and all `Q : M` with `n • Q = ι P`)
  occur.

**The argument.**  Choose, for each `P`, some `Q P` with `n • Q P = ι P`,
and let `c P` be its Kummer cochain.  If `c P = c P'` then
`act σ (Q P - Q P') = Q P - Q P'` for every `σ`, so by `hfix` the
difference is `ι a` for some `a : A`; applying `n •` and `hinj` gives
`P - P' = n • a`.  Hence `P ↦ c P` separates the cosets of `nA`, and
`A ⧸ nA` embeds into the finite set of cochains by sending a coset to the
cochain of a chosen representative.

**What this theorem is NOT.**  It is not weak Mordell–Weil: `hfin` is the
whole arithmetic input, and over a number field it is what the finiteness
of the class group and Dirichlet's unit theorem are for.  What is proven
here is that *nothing else* is needed — in particular no cohomology
theory, since a Kummer cochain is written down as a plain function and
the coboundary relation never has to be formed. -/
theorem finite_quotient_nsmul_of_kummerCochains
    {A : Type*} [AddCommGroup A] {M : Type*} [AddCommGroup M] {Γ : Type*}
    (n : ℕ) (act : Γ → M → M)
    (hact : ∀ (σ : Γ) (y z : M), act σ (y - z) = act σ y - act σ z)
    (ι : A → M) (hzero : ι 0 = 0) (hadd : ∀ a b : A, ι (a + b) = ι a + ι b)
    (hinj : Function.Injective ι)
    (hfix : ∀ y : M, (∀ σ : Γ, act σ y = y) → ∃ a : A, ι a = y)
    (hdiv : ∀ P : A, ∃ Q : M, n • Q = ι P)
    (hfin : {c : Γ → M | ∃ (P : A) (Q : M), n • Q = ι P ∧
      c = fun σ => act σ Q - Q}.Finite) :
    Finite (A ⧸ (nsmulAddMonoidHom n : A →+ A).range) := by
  classical
  set ιh : A →+ M := { toFun := ι, map_zero' := hzero, map_add' := hadd } with hιh
  set C : Set (Γ → M) := {c : Γ → M | ∃ (P : A) (Q : M), n • Q = ι P ∧
    c = fun σ => act σ Q - Q} with hC
  haveI : Finite C := hfin.to_subtype
  choose Q hQ using hdiv
  set c : A → (Γ → M) := fun P => fun σ => act σ (Q P) - Q P with hc
  have hcC : ∀ P : A, c P ∈ C := fun P => ⟨P, Q P, hQ P, rfl⟩
  have key : ∀ P P' : A, c P = c P' → P - P' ∈ (nsmulAddMonoidHom n : A →+ A).range := by
    intro P P' h
    have hfixed : ∀ σ : Γ, act σ (Q P - Q P') = Q P - Q P' := by
      intro σ
      have h1 : act σ (Q P) - Q P = act σ (Q P') - Q P' := congrFun h σ
      rw [hact]
      exact sub_eq_sub_iff_sub_eq_sub.mp h1
    obtain ⟨a, ha⟩ := hfix _ hfixed
    refine ⟨a, hinj ?_⟩
    show ι (n • a) = ι (P - P')
    have h2 : ι (n • a) = n • ι a := map_nsmul ιh n a
    have h3 : ι (P - P') = ι P - ι P' := map_sub ιh P P'
    rw [h2, ha, h3, ← hQ P, ← hQ P', nsmul_sub]
  set F : A ⧸ (nsmulAddMonoidHom n : A →+ A).range → C :=
    fun x => ⟨c (Quotient.out x), hcC _⟩ with hF
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h : c (Quotient.out x) = c (Quotient.out y) := congrArg Subtype.val hxy
    have hmem : Quotient.out x - Quotient.out y ∈
        (nsmulAddMonoidHom n : A →+ A).range := key _ _ h
    have hmem' : -(Quotient.out x) + Quotient.out y ∈
        (nsmulAddMonoidHom n : A →+ A).range := by
      have := neg_mem hmem
      simpa [neg_sub, sub_eq_neg_add] using this
    have h2 : ((Quotient.out x : A) : A ⧸ (nsmulAddMonoidHom n : A →+ A).range)
        = ((Quotient.out y : A) : A ⧸ (nsmulAddMonoidHom n : A →+ A).range) :=
      QuotientAddGroup.eq.mpr hmem'
    calc x = ((Quotient.out x : A) : A ⧸ (nsmulAddMonoidHom n : A →+ A).range) :=
          (Quotient.out_eq x).symm
      _ = ((Quotient.out y : A) : A ⧸ (nsmulAddMonoidHom n : A →+ A).range) := h2
      _ = y := Quotient.out_eq y
  exact Finite.of_injective F hFinj

end Fermat
