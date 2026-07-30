/-
Fermat/FLT/Mathlib/Analysis/WeilBoundDescent.lean — own work for the Fermat
project (not vendored).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Common

/-!
# Descent of the Weil / Ramanujan–Petersson bound along a `p`-th power

Let `α, β` be complex numbers with `α * β = N` for a positive real `N` — the
Satake parameters of a degree-two Hecke eigensystem at a place of residue norm
`N`.  The Ramanujan–Petersson bound at that place says `‖α + β‖ ≤ 2 √N`.

The main theorem `norm_add_le_two_mul_sqrt_of_norm_pow_add_le` says that this
bound **descends along `p`-th powers**: if the bound holds for the pair
`(α ^ p, β ^ p)` at the norm `N ^ p`, then it holds for `(α, β)` at `N`.

This is exactly what an INERT place `w` of a degree-`p` extension `L / M`
needs.  The unique place `W` of `L` above `w` has residue norm `N w ^ p`, and
the Satake parameters upstairs are the `p`-th powers of those downstairs, so
the eigenvalue upstairs is the Dickson value `D_p(a_w, N w)`.  A bound known
upstairs therefore transfers downstairs — **with no automorphic input
whatsoever**.

## The proof

Writing `z = α / √N` (so `β / √N = z⁻¹`), the bound `‖α + β‖ ≤ 2 √N` becomes
`‖z + z⁻¹‖ ≤ 2`.  In polar coordinates `z = e ^ (s + i θ)` one computes

`‖z + z⁻¹‖ ^ 2 = (‖z‖ - ‖z‖⁻¹) ^ 2 + 4 (cos θ) ^ 2`,

so `‖z + z⁻¹‖ ≤ 2` is equivalent to `|sinh s| ≤ |sin θ|`
(`norm_add_inv_le_two_iff`, stated here in the equivalent Cartesian form
`|‖z‖ ^ 2 - 1| ≤ 2 |Im z|` to avoid polar coordinates in Lean).  The descent
is then just two elementary inequalities,

* `p * |sinh s| ≤ |sinh (p s)|` (superadditivity of `sinh`), and
* `|sin (p θ)| ≤ p * |sin θ|`,

which together give `|sinh s| ≤ |sin θ|` from `|sinh (p s)| ≤ |sin (p θ)|`.
The second is proved here in the Cartesian disguise
`‖z‖ * |Im (z ^ n)| ≤ n ‖z‖ ^ n |Im z|` (`norm_mul_abs_im_pow_le`), a bare
induction that needs no trigonometry at all.

## THIS REFUTES A CLAIM RECORDED ELSEWHERE IN THE TREE (2026-07-29)

`PotentialModularityWitness.weilBoundDescent` (`Modularity/MoretBailly.lean`)
carries, in its field docstring, the assertion:

> At an inert place the eigenvalue downstairs is related to the one upstairs
> only by the Dickson identity `a_W = D_f(a_w, Nw)`, from which the bound
> upstairs does NOT follow (that step needs the SHARP form of Deligne's
> bound, i.e. reality of the Hecke field, which is not recorded here).

**That is false, and `norm_add_le_two_mul_sqrt_of_norm_pow_add_le` is the
counterexample to it.**  The bound downstairs DOES follow from the bound
upstairs through the Dickson identity, with no sharpness, no reality of the
Hecke field, and no automorphic input — only `α β = N w` (the cyclotomic
determinant, already proven in-tree as
`charFrob_baseChange_coeff_zero_eq_absNorm`) and `p ≥ 1`.  Nor is there a
parity restriction: `p = 2` is covered exactly like odd `p`.

CONSEQUENCE A FUTURE OWNER SHOULD CHECK (not acted on here, because it moves
another module's structure).  If `W` is a place of `F` above the place `w` of
`L = F^C` with residue degree `f`, then `N W = N w ^ f` and
`ρ(Frob_W) = ρ(Frob_w) ^ f`, so the `F`-level bound `weilBoundF` at `W`
descends to `w` by this theorem — at EVERY place, matching or not.  That is
precisely the case the quoted docstring says is unavailable, so
`weilBoundDescent` looks DERIVABLE from `weilBoundF`, which would retire both
the field and the automorphic input (`IsQuaternionicEigensystem`) that its
discharge `weilBound_descended_of_heckePackage` currently consumes.  The check
that refutes this: exhibit a place `w` of `L` under no place of `F` — there is
none, `L ⊆ F` is a finite extension.
-/

@[expose] public section

namespace Fermat

open Real Complex

private theorem abs_le_of_sq_le_sq' {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  by_contra hc
  rw [not_le] at hc
  have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
  nlinarith [abs_nonneg a]

private theorem sq_le_sq_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
  nlinarith [abs_nonneg a]

private theorem abs_add' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using norm_add_le a b

/-- `n * |sinh s| ≤ |sinh (n * s)|` — superadditivity of `sinh` on `[0, ∞)`,
extended to all of `ℝ` by oddness. -/
theorem nat_mul_abs_sinh_le (n : ℕ) (s : ℝ) :
    n * |Real.sinh s| ≤ |Real.sinh (n * s)| := by
  have key : ∀ t : ℝ, 0 ≤ t → (n : ℝ) * Real.sinh t ≤ Real.sinh ((n : ℝ) * t) := by
    intro t ht
    induction n with
    | zero => simp
    | succ k ih =>
      have hkt : (0 : ℝ) ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg k) ht
      have hsk : (0 : ℝ) ≤ Real.sinh ((k : ℝ) * t) := Real.sinh_nonneg_iff.mpr hkt
      have hst : (0 : ℝ) ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
      have hstep : Real.sinh (((k : ℕ) + 1 : ℕ) * t) =
          Real.sinh ((k : ℝ) * t) * Real.cosh t + Real.cosh ((k : ℝ) * t) * Real.sinh t := by
        have hrw : (((k : ℕ) + 1 : ℕ) : ℝ) * t = (k : ℝ) * t + t := by push_cast; ring
        rw [hrw, Real.sinh_add]
      rw [hstep]
      have h1 : Real.sinh ((k : ℝ) * t) ≤ Real.sinh ((k : ℝ) * t) * Real.cosh t :=
        le_mul_of_one_le_right hsk (Real.one_le_cosh t)
      have h2 : Real.sinh t ≤ Real.cosh ((k : ℝ) * t) * Real.sinh t :=
        le_mul_of_one_le_left hst (Real.one_le_cosh _)
      push_cast
      linarith
  rcases le_total 0 s with hs | hs
  · have h := key s hs
    have hsn : (0 : ℝ) ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs
    have hsm : (0 : ℝ) ≤ Real.sinh ((n : ℝ) * s) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg (Nat.cast_nonneg n) hs)
    rw [abs_of_nonneg hsn, abs_of_nonneg hsm]
    exact h
  · have h := key (-s) (by linarith)
    rw [Real.sinh_neg, show ((n : ℝ) * -s) = -((n : ℝ) * s) by ring, Real.sinh_neg] at h
    have hsn : Real.sinh s ≤ 0 := Real.sinh_nonpos_iff.mpr hs
    have hsm : Real.sinh ((n : ℝ) * s) ≤ 0 :=
      Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hs)
    rw [abs_of_nonpos hsn, abs_of_nonpos hsm]
    linarith

/-- `nat_mul_abs_sinh_le` in multiplicative form: for `0 < r`,
`n * r ^ n * |r ^ 2 - 1| ≤ r * |r ^ (2 * n) - 1|`. -/
theorem nat_mul_pow_mul_abs_sub_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (n : ℝ) * r ^ n * |r ^ 2 - 1| ≤ r * |r ^ (2 * n) - 1| := by
  have hrn : (0 : ℝ) < r ^ n := pow_pos hr n
  have hlogn : Real.sinh ((n : ℝ) * Real.log r) = (r ^ n - (r ^ n)⁻¹) / 2 := by
    rw [← Real.log_pow, Real.sinh_log hrn]
  have base := nat_mul_abs_sinh_le n (Real.log r)
  rw [Real.sinh_log hr, hlogn] at base
  have habs1 : |(r - r⁻¹) / 2| = |r - r⁻¹| / 2 := by rw [abs_div]; simp
  have habs2 : |(r ^ n - (r ^ n)⁻¹) / 2| = |r ^ n - (r ^ n)⁻¹| / 2 := by rw [abs_div]; simp
  rw [habs1, habs2] at base
  have base' : (n : ℝ) * |r - r⁻¹| ≤ |r ^ n - (r ^ n)⁻¹| := by linarith
  have hpos : (0 : ℝ) ≤ r ^ (n + 1) := le_of_lt (pow_pos hr _)
  have hmul := mul_le_mul_of_nonneg_left base' hpos
  have key1 : r * |r - r⁻¹| = |r ^ 2 - 1| := by
    have hx : r * (r - r⁻¹) = r ^ 2 - 1 := by
      rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hr), ← sq]
    calc r * |r - r⁻¹| = |r| * |r - r⁻¹| := by rw [abs_of_pos hr]
      _ = |r * (r - r⁻¹)| := (abs_mul r (r - r⁻¹)).symm
      _ = |r ^ 2 - 1| := by rw [hx]
  have key2 : r ^ n * |r ^ n - (r ^ n)⁻¹| = |r ^ (2 * n) - 1| := by
    have hne : (r ^ n) ≠ 0 := ne_of_gt hrn
    have hx : r ^ n * (r ^ n - (r ^ n)⁻¹) = r ^ (2 * n) - 1 := by
      rw [mul_sub, mul_inv_cancel₀ hne, ← sq, ← pow_mul, mul_comm n 2]
    calc r ^ n * |r ^ n - (r ^ n)⁻¹| = |r ^ n| * |r ^ n - (r ^ n)⁻¹| := by
          rw [abs_of_pos hrn]
      _ = |r ^ n * (r ^ n - (r ^ n)⁻¹)| := (abs_mul _ _).symm
      _ = |r ^ (2 * n) - 1| := by rw [hx]
  have e1 : r ^ (n + 1) * ((n : ℝ) * |r - r⁻¹|) = (n : ℝ) * r ^ n * |r ^ 2 - 1| := by
    rw [pow_succ, ← key1]; ring
  have e2 : r ^ (n + 1) * |r ^ n - (r ^ n)⁻¹| = r * |r ^ (2 * n) - 1| := by
    rw [pow_succ, ← key2]; ring
  rw [e1, e2] at hmul
  exact hmul

/-- `‖z‖ * |Im (z ^ n)| ≤ n * ‖z‖ ^ n * |Im z|` — the Cartesian substitute for
`|sin (n θ)| ≤ n |sin θ|`, proved by a bare induction on `n`. -/
theorem norm_mul_abs_im_pow_le (z : ℂ) (n : ℕ) :
    ‖z‖ * |(z ^ n).im| ≤ (n : ℝ) * ‖z‖ ^ n * |z.im| := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hre : |(z ^ k).re| ≤ ‖z‖ ^ k := by
      calc |(z ^ k).re| ≤ ‖z ^ k‖ := Complex.abs_re_le_norm _
        _ = ‖z‖ ^ k := by rw [norm_pow]
    have hexp : (z ^ (k + 1)).im = (z ^ k).im * z.re + (z ^ k).re * z.im := by
      rw [pow_succ, Complex.mul_im]; ring
    rw [hexp]
    have habs : |(z ^ k).im * z.re + (z ^ k).re * z.im|
        ≤ |(z ^ k).im| * ‖z‖ + ‖z‖ ^ k * |z.im| := by
      refine (abs_add' _ _).trans ?_
      rw [abs_mul, abs_mul]
      have hA : |(z ^ k).im| * |z.re| ≤ |(z ^ k).im| * ‖z‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)
      have hB : |(z ^ k).re| * |z.im| ≤ ‖z‖ ^ k * |z.im| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg _)
      linarith
    have hmul : ‖z‖ * |(z ^ k).im * z.re + (z ^ k).re * z.im|
        ≤ ‖z‖ * (|(z ^ k).im| * ‖z‖ + ‖z‖ ^ k * |z.im|) :=
      mul_le_mul_of_nonneg_left habs hz
    have hih := mul_le_mul_of_nonneg_right ih hz
    have hfin : (k : ℝ) * ‖z‖ ^ k * |z.im| * ‖z‖ + ‖z‖ * (‖z‖ ^ k * |z.im|)
        = ((k : ℝ) + 1) * ‖z‖ ^ (k + 1) * |z.im| := by rw [pow_succ]; ring
    push_cast
    nlinarith [hmul, hih, hfin]

/-- **The Joukowski characterisation.**  For `z ≠ 0`, `‖z + z⁻¹‖ ≤ 2` holds exactly
when `|‖z‖ ^ 2 - 1| ≤ 2 * |Im z|`.  In polar form both sides read `|sinh s| ≤ |sin θ|`;
the proof is the polynomial identity
`‖z ^ 2 + 1‖ ^ 2 - 4 * ‖z‖ ^ 2 = (‖z‖ ^ 2 - 1) ^ 2 - 4 * (Im z) ^ 2`. -/
theorem norm_add_inv_le_two_iff {z : ℂ} (hz : z ≠ 0) :
    ‖z + z⁻¹‖ ≤ 2 ↔ |‖z‖ ^ 2 - 1| ≤ 2 * |z.im| := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hprodz : (z + z⁻¹) * z = z ^ 2 + 1 := by
    rw [add_mul, inv_mul_cancel₀ hz, ← sq]
  have hclear : ‖z + z⁻¹‖ * ‖z‖ = ‖z ^ 2 + 1‖ := by rw [← norm_mul, hprodz]
  have hz2 : ‖z ^ 2 + 1‖ ^ 2 = (z.re ^ 2 - z.im ^ 2 + 1) ^ 2 + (2 * z.re * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im]
    ring
  have hident : ‖z ^ 2 + 1‖ ^ 2 - 4 * ‖z‖ ^ 2 = (‖z‖ ^ 2 - 1) ^ 2 - 4 * z.im ^ 2 := by
    rw [hz2, hnsq]; ring
  constructor
  · intro h
    have h1 : ‖z ^ 2 + 1‖ ≤ 2 * ‖z‖ := by
      rw [← hclear]
      nlinarith [h, hr]
    have h2 : ‖z ^ 2 + 1‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
      nlinarith [h1, norm_nonneg (z ^ 2 + 1), hr]
    have h3 : (‖z‖ ^ 2 - 1) ^ 2 ≤ (2 * |z.im|) ^ 2 := by
      have hb : (2 * |z.im|) ^ 2 = 4 * z.im ^ 2 := by rw [mul_pow, sq_abs]; ring
      rw [hb]; linarith [hident, h2]
    exact abs_le_of_sq_le_sq' h3 (by positivity)
  · intro h
    have h3 : (‖z‖ ^ 2 - 1) ^ 2 ≤ 4 * z.im ^ 2 := by
      have := sq_le_sq_of_abs_le h
      have hb : (2 * |z.im|) ^ 2 = 4 * z.im ^ 2 := by rw [mul_pow, sq_abs]; ring
      rw [hb] at this
      exact this
    have h2 : ‖z ^ 2 + 1‖ ^ 2 ≤ (2 * ‖z‖) ^ 2 := by
      have hb : (2 * ‖z‖) ^ 2 = 4 * ‖z‖ ^ 2 := by ring
      rw [hb]; linarith [hident, h3]
    have h1 : ‖z ^ 2 + 1‖ ≤ 2 * ‖z‖ := by
      have := abs_le_of_sq_le_sq' h2 (by positivity)
      rwa [abs_of_nonneg (norm_nonneg _)] at this
    rw [← hclear] at h1
    nlinarith [h1, hr]

/-- **THE WEIL-BOUND DESCENT, normalised form.**  If `z ≠ 0` and `z ^ p` satisfies
`‖z ^ p + (z ^ p)⁻¹‖ ≤ 2`, then so does `z` itself. -/
theorem norm_add_inv_le_two_of_pow {z : ℂ} (hz : z ≠ 0) {p : ℕ} (hp : 1 ≤ p)
    (h : ‖z ^ p + (z ^ p)⁻¹‖ ≤ 2) : ‖z + z⁻¹‖ ≤ 2 := by
  have hzp : z ^ p ≠ 0 := pow_ne_zero _ hz
  rw [norm_add_inv_le_two_iff hzp] at h
  rw [norm_add_inv_le_two_iff hz]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnp : ‖z ^ p‖ ^ 2 = ‖z‖ ^ (2 * p) := by rw [norm_pow, ← pow_mul, mul_comm]
  rw [hnp] at h
  have i1 := nat_mul_pow_mul_abs_sub_le hr p
  have i2 := norm_mul_abs_im_pow_le z p
  have hchain : (p : ℝ) * ‖z‖ ^ p * |‖z‖ ^ 2 - 1| ≤ 2 * ((p : ℝ) * ‖z‖ ^ p * |z.im|) := by
    have step : ‖z‖ * |‖z‖ ^ (2 * p) - 1| ≤ ‖z‖ * (2 * |(z ^ p).im|) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hr)
    nlinarith [i1, i2, step, hr]
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hp
  have hposc : (0 : ℝ) < (p : ℝ) * ‖z‖ ^ p := by positivity
  nlinarith [hchain, hposc]

/-- **THE WEIL-BOUND DESCENT** (normalised at `c` with `α β = c ^ 2`). -/
theorem norm_add_le_two_mul_of_norm_pow_add_le {α β : ℂ} {c : ℝ} (hc : 0 < c)
    (hprod : α * β = ((c * c : ℝ) : ℂ)) {p : ℕ} (hp : 1 ≤ p)
    (h : ‖α ^ p + β ^ p‖ ≤ 2 * c ^ p) : ‖α + β‖ ≤ 2 * c := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hcnorm : ‖((c : ℝ) : ℂ)‖ = c := by simp [abs_of_pos hc]
  have hαne : α ≠ 0 := by
    intro hα
    rw [hα, zero_mul] at hprod
    have hcc : (c * c : ℝ) = 0 := by exact_mod_cast hprod.symm
    nlinarith [hc]
  set z : ℂ := α / ((c : ℝ) : ℂ) with hzdef
  have hzne : z ≠ 0 := div_ne_zero hαne hcne
  have hα' : ((c : ℝ) : ℂ) * z = α := by rw [hzdef]; field_simp
  have hβ' : ((c : ℝ) : ℂ) * z⁻¹ = β := by
    have hb : β = ((c * c : ℝ) : ℂ) / α := by rw [eq_div_iff hαne, mul_comm]; exact hprod
    rw [hzdef, inv_div, hb, Complex.ofReal_mul]
    ring
  have hsum : α + β = ((c : ℝ) : ℂ) * (z + z⁻¹) := by rw [← hα', ← hβ']; ring
  have hpowsum : α ^ p + β ^ p = ((c : ℝ) : ℂ) ^ p * (z ^ p + (z ^ p)⁻¹) := by
    rw [← hα', ← hβ', mul_pow, mul_pow, ← inv_pow]; ring
  have hcp : (0 : ℝ) < c ^ p := pow_pos hc p
  rw [hpowsum, norm_mul, norm_pow, hcnorm] at h
  have hnorm2 : ‖z ^ p + (z ^ p)⁻¹‖ ≤ 2 := by
    have := h
    nlinarith [this, hcp, norm_nonneg (z ^ p + (z ^ p)⁻¹)]
  have hfin := norm_add_inv_le_two_of_pow hzne hp hnorm2
  rw [hsum, norm_mul, hcnorm]
  nlinarith [hfin, hc, norm_nonneg (z + z⁻¹)]

/-- **THE WEIL-BOUND DESCENT.**  Let `α β : ℂ` with `α * β = N` for a positive real
`N`, and let `p ≥ 1`.  If `‖α ^ p + β ^ p‖ ≤ 2 * (√N) ^ p`, then `‖α + β‖ ≤ 2 * √N`.

This is what makes the archimedean (Ramanujan–Petersson) bound DESCEND along an inert
place of a degree-`p` extension: upstairs the eigenvalue is
`α ^ p + β ^ p = D_p(α + β, N)` and the residue norm is `N ^ p`.  It needs no
automorphic input — it is `p |sinh s| ≤ |sinh (p s)|` and `|sin (p θ)| ≤ p |sin θ|`
in disguise. -/
theorem norm_add_le_two_mul_sqrt_of_norm_pow_add_le {α β : ℂ} {N : ℝ} (hN : 0 < N)
    (hprod : α * β = (N : ℂ)) {p : ℕ} (hp : 1 ≤ p)
    (h : ‖α ^ p + β ^ p‖ ≤ 2 * Real.sqrt N ^ p) :
    ‖α + β‖ ≤ 2 * Real.sqrt N := by
  have hcpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hcc : (Real.sqrt N * Real.sqrt N : ℝ) = N := Real.mul_self_sqrt (le_of_lt hN)
  refine norm_add_le_two_mul_of_norm_pow_add_le hcpos ?_ hp h
  rw [hcc]
  exact hprod

/-- `traceSum x N p` is the `p`-th power sum `α ^ p + β ^ p` of the two roots of
`X ^ 2 - x * X + N`, written by the Newton recursion so that it makes sense over any
commutative ring (the roots themselves need not exist there).  This is the Dickson
polynomial `D_p(x, N)`. -/
def traceSum {R : Type*} [CommRing R] (x N : R) : ℕ → R
  | 0 => 2
  | 1 => x
  | (n + 2) => x * traceSum x N (n + 1) - N * traceSum x N n

theorem traceSum_eq_add_pow {R : Type*} [CommRing R] (α β : R) :
    ∀ n, traceSum (α + β) (α * β) n = α ^ n + β ^ n
  | 0 => by simp [traceSum]; norm_num
  | 1 => by simp [traceSum]
  | (n + 2) => by
      rw [traceSum, traceSum_eq_add_pow α β (n + 1), traceSum_eq_add_pow α β n]
      ring

theorem map_traceSum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x N : R) :
    ∀ n, f (traceSum x N n) = traceSum (f x) (f N) n
  | 0 => by simp [traceSum, map_ofNat]
  | 1 => by simp [traceSum]
  | (n + 2) => by
      rw [traceSum, map_sub, map_mul, map_mul, map_traceSum f x N (n + 1),
        map_traceSum f x N n, traceSum]

/-- Over `ℂ`, `X ^ 2 - x * X + N` always factors. -/
theorem exists_add_mul_eq (x N : ℂ) : ∃ α β : ℂ, α + β = x ∧ α * β = N := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 2 - 4 * N) (n := 2) two_pos
  refine ⟨(x + s) / 2, (x - s) / 2, by ring, ?_⟩
  field_simp
  linear_combination -hs

/-- **THE RAMANUJAN DESCENT, in the form the base-change step consumes.**  If the
`p`-th Dickson value `traceSum x N p` satisfies the Weil bound at `N ^ p`, then `x`
satisfies it at `N`. -/
theorem norm_le_two_mul_sqrt_of_norm_traceSum_le {x : ℂ} {N : ℝ} (hN : 0 < N) {p : ℕ}
    (hp : 1 ≤ p) (h : ‖traceSum x (N : ℂ) p‖ ≤ 2 * Real.sqrt N ^ p) :
    ‖x‖ ≤ 2 * Real.sqrt N := by
  obtain ⟨α, β, hsum, hprod⟩ := exists_add_mul_eq x (N : ℂ)
  rw [← hsum]
  refine norm_add_le_two_mul_sqrt_of_norm_pow_add_le hN hprod hp ?_
  rw [← traceSum_eq_add_pow α β p, hsum, hprod]
  exact h

/-- **The shape a cyclic base-change step at an INERT place consumes.**

`aw : EM` is (minus) the descended Frobenius trace at a place `w` of the lower
field, of residue norm `Nw`; `bL : EL` is the coefficient the upstream
eigensystem records at the unique place above `w`, whose residue norm is
`Nw ^ p`; `hdick` is the Dickson relation between them; and `hbound` is the
Ramanujan–Petersson bound UPSTAIRS.  The conclusion is the bound DOWNSTAIRS.

The point is that the descent of the archimedean bound needs no automorphic
input at all — only the Dickson relation, which is Galois theory. -/
theorem norm_le_two_mul_sqrt_of_dickson_of_norm_le
    {EL EM : Type*} [Field EL] [Field EM] (ιM : EL →+* EM)
    {Nw : ℕ} (hNw : 0 < Nw) {p : ℕ} (hp : 1 ≤ p) (aw : EM) (bL : EL)
    (hdick : ιM bL = - traceSum (-aw) ((Nw : ℕ) : EM) p)
    (hbound : ∀ ψ : EL →+* ℂ, ‖ψ bL‖ ≤ 2 * Real.sqrt ((Nw ^ p : ℕ) : ℝ))
    (φ : EM →+* ℂ) :
    ‖φ aw‖ ≤ 2 * Real.sqrt ((Nw : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < ((Nw : ℕ) : ℝ) := by exact_mod_cast hNw
  -- the Dickson value, pushed into `ℂ` along `φ`
  have hmap : traceSum (φ (-aw)) (((Nw : ℕ) : ℝ) : ℂ) p = - (φ.comp ιM) bL := by
    have h1 : φ (traceSum (-aw) ((Nw : ℕ) : EM) p)
        = traceSum (φ (-aw)) (φ ((Nw : ℕ) : EM)) p := map_traceSum φ _ _ p
    have h2 : φ ((Nw : ℕ) : EM) = (((Nw : ℕ) : ℝ) : ℂ) := by
      rw [map_natCast]; norm_cast
    rw [h2] at h1
    rw [← h1]
    have h3 : traceSum (-aw) ((Nw : ℕ) : EM) p = - ιM bL := by rw [hdick]; ring
    rw [h3, map_neg]
    rfl
  -- the bound upstairs, rewritten at `(√Nw) ^ p`
  have hsq : (Real.sqrt ((Nw : ℕ) : ℝ) ^ p) ^ 2 = ((Nw : ℕ) : ℝ) ^ p := by
    rw [← pow_mul, mul_comm p 2, pow_mul, Real.sq_sqrt (le_of_lt hN)]
  have hsqrt : Real.sqrt ((Nw ^ p : ℕ) : ℝ) = Real.sqrt ((Nw : ℕ) : ℝ) ^ p := by
    rw [Nat.cast_pow, ← hsq, Real.sqrt_sq (by positivity)]
  have hup : ‖traceSum (φ (-aw)) (((Nw : ℕ) : ℝ) : ℂ) p‖
      ≤ 2 * Real.sqrt ((Nw : ℕ) : ℝ) ^ p := by
    rw [hmap, norm_neg, ← hsqrt]
    exact hbound (φ.comp ιM)
  have := norm_le_two_mul_sqrt_of_norm_traceSum_le hN hp hup
  rwa [map_neg, norm_neg] at this

end Fermat
