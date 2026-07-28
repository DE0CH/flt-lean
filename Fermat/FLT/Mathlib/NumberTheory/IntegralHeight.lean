module

/-
IntegralHeight.lean — own work for the Fermat project (neither `Mathlib`
nor `~/cs/FLT` contains a height function or Northcott's theorem; the
only thing upstream is `Mathlib/Order/Northcott.lean`, the *class*
`Northcott`, with no instance for any height).

# The naive height on integral coordinates, and Northcott's theorem for it

This module supplies the **finiteness half** of the theory of heights
over `ℚ`, in the one form the Mordell–Weil argument needs it, and it
supplies it PROVEN.

## What is here

* `Fermat.intHeight (v : Fin d → ℤ) = Real.log (1 + ∑ i, |v i|)`, the
  logarithmic naive height of an integer vector (nonnegative, since the
  argument of the logarithm is at least `1`);
* `Fermat.instNorthcottIntHeight`, **Northcott's property for it**: there
  are only finitely many integer vectors of bounded height, because a
  bound on the height is a bound on the `ℓ¹`-norm and an integer box is
  finite;
* `Fermat.IntegralCoordinates A`, an *integral coordinate system* on an
  additive abelian group: an injection `A ↪ ℤ^d` whose naive height obeys
  the quasi-parallelogram law;
* `Fermat.IntegralCoordinates.toWeilHeight`, which turns one into a
  `Fermat.WeilHeight` — and hence, through
  `Fermat.WeilHeight.toDescentHeight`, into a `Fermat.DescentHeight`.

## Why this is the right interface for an abelian variety over `ℚ`

Let `A` be an abelian variety over `ℚ`.  Choose a symmetric ample line
bundle `L` (take any ample `L₀` and set `L = L₀ ⊗ [−1]^* L₀`), replace it
by a power so that it is very ample, and let `φ_L : A ↪ ℙ^N_ℚ` be the
resulting closed immersion.  A point of `ℙ^N(ℚ)` has an integral
representative `(x_0 : … : x_N)` with `gcd(x_i) = 1`, unique up to sign,
and the sign is pinned by requiring the first nonzero coordinate to be
positive.  Sending `P ∈ A(ℚ)` to that vector gives an **injection**
`A(ℚ) ↪ ℤ^{N+1}` — injective because a closed immersion is injective on
`ℚ`-points — and

  `intHeight (coords P) = log max_i |x_i| + O(1)`,

since `max_i |x_i| ≤ 1 + ∑_i |x_i| ≤ (N + 2) · max_i |x_i|` for a
primitive vector (whose maximum is at least `1`).  The right-hand side is
the standard Weil height `h_L(P)`, and the theorem of the cube says
exactly that `h_L` obeys the quasi-parallelogram law.  So an
`IntegralCoordinates` structure on `A(ℚ)` is precisely the data the
theory of heights produces, transcribed into elementary terms.

**This is `ℚ`-specific by design.**  Over a general number field the
naive height is a sum over places and its level sets are finite for a
genuinely arithmetic reason (finiteness of the class group enters when
one normalises coordinates); over `ℚ`, primitive integral coordinates
exist and Northcott's theorem is the finiteness of an integer box, which
is why it can be proven here outright.  Mordell–Weil is only needed over
`ℚ` in this development.

## What is NOT here

The geometry: existence of the symmetric very ample `L`, and the theorem
of the cube.  Those are the content of the single remaining leaf
`Fermat.exists_integralCoordinates_of_abelianScheme` in
`Fermat/FLT/ModularCurve/X0.lean`.

Everything in this module is PROVEN; it contains no `sorry`.

## CORRECTION (2026-07-27): the pin DOES have a theory of heights

The opening line above — "neither `Mathlib` nor `~/cs/FLT` contains a
height function or Northcott's theorem; the only thing upstream is
`Mathlib/Order/Northcott.lean`" — is FALSE at this pin, and nothing in
this module was checked against the upstream theory before it was
written.  `Mathlib/NumberTheory/Height/` contains `Height.mulHeight` and
`Height.logHeight` on tuples over any field with
`Height.AdmissibleAbsValues` (instance: every number field, hence `ℚ`),
Northcott (`Height.finite_setOf_logHeight₁_le`), the comparison
`Rat.logHeight_eq_max_abs_of_gcd_eq_one` for primitive integer tuples,
and the height machine for families of homogeneous forms in both
directions (`Height.logHeight_eval_le'`, `Height.logHeight_eval_ge'`).

Nothing here is wrong or wasted — `intHeight` and `IntegralCoordinates`
are the interface the descent theorem consumes, and they are proven —
but a reader must not conclude from the text above that the upstream
theory is missing.  It is what makes the elementary half of
`Fermat/FLT/Mathlib/NumberTheory/SegreHeight.lean` a derivation rather
than a theory to be built.
-/

public import Fermat.FLT.Mathlib.GroupTheory.Descent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace Fermat

/-- **The logarithmic naive height of an integer vector**,
`log (1 + ∑ i, |v i|)`.

The `1 +` is there to make the argument of the logarithm positive at
`v = 0` (and, incidentally, to make the height nonnegative everywhere).
Using the `ℓ¹`-norm rather than the sup-norm changes the value by at most
`log d`, so it makes no difference to any statement that is only asked to
hold up to a constant — which is all the descent argument ever asks.

Note `0 ≤ intHeight v` always, since `1 ≤ 1 + ∑ i, |v i|`; no consumer
needs that as a lemma, so it is recorded here rather than stated (a
`theorem` nothing consumes would be free-floating). -/
def intHeight {d : ℕ} (v : Fin d → ℤ) : ℝ := Real.log (1 + ∑ i, ((v i).natAbs : ℝ))

/-- **Northcott's theorem for the naive height on `ℤ^d`** (PROVEN).

`intHeight v ≤ c` bounds `∑ i, |v i|` by `exp c`, hence bounds every
coordinate by `⌈exp c⌉`, so the level set is contained in a box
`[−B, B]^d`, which is finite. -/
instance instNorthcottIntHeight {d : ℕ} : Northcott (intHeight (d := d)) where
  finite_le c := by
    classical
    set B : ℕ := ⌈Real.exp c⌉₊ with hB
    have hsub : {v : Fin d → ℤ | intHeight v ≤ c}
        ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (-(B : ℤ)) (B : ℤ)) := by
      intro v hv
      have hv' : Real.log (1 + ∑ i, ((v i).natAbs : ℝ)) ≤ c := hv
      have hpos : (0 : ℝ) < 1 + ∑ i, ((v i).natAbs : ℝ) := by
        have : (0 : ℝ) ≤ ∑ i, ((v i).natAbs : ℝ) :=
          Finset.sum_nonneg fun i _ => by positivity
        linarith
      have hle : 1 + ∑ i, ((v i).natAbs : ℝ) ≤ Real.exp c :=
        (Real.log_le_iff_le_exp hpos).mp hv'
      intro j _
      have hj : ((v j).natAbs : ℝ) ≤ ∑ i, ((v i).natAbs : ℝ) :=
        Finset.single_le_sum (f := fun i => ((v i).natAbs : ℝ))
          (fun i _ => by positivity) (Finset.mem_univ j)
      have hjb : ((v j).natAbs : ℝ) ≤ (B : ℝ) := by
        have h1 : ((v j).natAbs : ℝ) ≤ Real.exp c := by linarith
        have h2 : Real.exp c ≤ (B : ℝ) := Nat.le_ceil _
        linarith
      have hjb' : (v j).natAbs ≤ B := by exact_mod_cast hjb
      simp only [Set.mem_Icc]
      omega
    exact Set.Finite.subset (Set.Finite.pi fun _ => Set.finite_Icc _ _) hsub

/-- **An integral coordinate system on an additive abelian group**: an
injection into `ℤ^d` whose naive height obeys the quasi-parallelogram
law.

This is the elementary transcription of "a symmetric very ample line
bundle and its Weil height" — see the module docstring.  Two remarks on
what it does and does not say:

* it is NOT trivially satisfiable.  Any injection into `ℤ^d` at all gives
  a Northcott height, but the quasi-parallelogram law forces that height
  to be a quadratic form up to `O(1)`, which pins the *growth rate* of
  the coordinates along every cyclic subgroup.  For `A = ℤ` a linear
  parametrisation such as `n ↦ (n)` fails it outright: the defect
  `log|n+m| + log|n−m| − 2 log|n| − 2 log|m|` is unbounded;
* it says nothing about the geometry.  Only injectivity and one
  inequality are asked for, so a producer is free to normalise
  coordinates however it likes. -/
structure IntegralCoordinates (A : Type*) [AddCommGroup A] where
  /-- the number of coordinates -/
  dim : ℕ
  /-- the coordinate map -/
  coords : A → (Fin dim → ℤ)
  /-- the coordinates separate points -/
  injective : Function.Injective coords
  /-- the naive height of the coordinates obeys the quasi-parallelogram law -/
  quasiParallelogram : ∃ C : ℝ, ∀ P Q : A,
    |intHeight (coords (P + Q)) + intHeight (coords (P - Q))
      - (2 * intHeight (coords P) + 2 * intHeight (coords Q))| ≤ C

/-- **An integral coordinate system is a Weil height** (PROVEN).

The quasi-parallelogram law is carried over verbatim; Northcott's
property is `instNorthcottIntHeight` pulled back along an injection,
which preserves finiteness of preimages. -/
def IntegralCoordinates.toWeilHeight {A : Type*} [AddCommGroup A]
    (ic : IntegralCoordinates A) : WeilHeight A where
  height := fun P => intHeight (ic.coords P)
  quasiParallelogram := ic.quasiParallelogram
  northcott := by
    refine ⟨fun c => ?_⟩
    have hpre : {P : A | intHeight (ic.coords P) ≤ c}
        = ic.coords ⁻¹' {v : Fin ic.dim → ℤ | intHeight v ≤ c} := rfl
    rw [hpre]
    exact Set.Finite.preimage ic.injective.injOn (Northcott.finite_le (h := intHeight) c)

/-- **An integral coordinate system is a descent height** (PROVEN) — the
composite `IntegralCoordinates → WeilHeight → DescentHeight`, with
`m = 2`.  This is the form the Mordell–Weil assembly in
`Fermat/FLT/ModularCurve/X0.lean` consumes. -/
def IntegralCoordinates.toDescentHeight {A : Type*} [AddCommGroup A]
    (ic : IntegralCoordinates A) : DescentHeight A :=
  ic.toWeilHeight.toDescentHeight

end Fermat
