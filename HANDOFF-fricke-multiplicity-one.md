# HANDOFF — the Fricke multiplicity-one route, COMPILED

Written by `flt-lean-148`, 2026-07-31, against `main` at `9a2ca10d`.

This file exists because the leaf it is about,
`exists_frickeSlash_eq_smul_of_isNewEigenformAt` in
`Fermat/FLT/ModularCurve/X0.lean`, is blocked by the MODULE DIRECTION and by
nothing else, so no agent sent at it in `X0.lean` can make progress — while the
entire route can be, and now has been, verified one module DOWNSTREAM of the
blocker.

**The technique is the reusable part**: when a leaf is blocked because the
theory it needs sits in a module that IMPORTS the leaf's file, you cannot prove
the leaf, but you can prove *the theorem the leaf will become* in a scratch
module that imports the downstream file. That converts an unbounded hoist
("move 8 000 lines and hope the route closes") into a bounded one ("move
8 000 lines and paste in this compiled 557-line block").

## STATUS OF THE ROUTE — ONE SORRY LEFT, AND IT IS NAMED

The code block at the end of this file is 557 lines and **compiles with exactly
one `declaration uses 'sorry'` warning** (`lake env lean`, `EXIT=0`, zero
errors). It contains, in order:

* **steps 1–4** of the route recorded on the leaf's docstring (as rewritten at
  `82ea7ac7`, on `merger`), ending at

  ```
  theorem exists_frickeSlash_eq_smul_of_isWeightTwoNewform {M : ℕ} (hM : M ≠ 0)
      (g : CuspForm (Gamma0GL M) 2) (hg : IsWeightTwoNewform M g) :
      ∃ c : ℂ, Fermat.frickeSlash M hM g = c • g
  ```

  — the leaf's conclusion, over `Modularity.IsWeightTwoNewform`;

* the **coefficient half of the carrier bridge**, PROVEN and not sorried:
  `qCoeff_eq_of_isWeightTwoEigenform` (the carried sequence `b` IS the pin's
  `q`-expansion coefficient sequence, through
  `ModularFormClass.qExpansion_coeff_unique`), the multiplicativity induction
  `carrier_pow_mul` / `carrier_mul_coprime`, and

  ```
  isWeightTwoEigenform_of_carrier :
      Fermat.IsWeightTwoEigenform M g b → IsWeightTwoEigenform M g
  ```

* the **one residue**, as a named leaf and the file's only `sorry`:

  ```
  eigensystem_minimal_of_isNewEigenformAt {M : ℕ} (hM : M ≠ 0)
      {g : CuspForm (Gamma0GL M) 2} {b : ℕ → ℂ}
      (hb : Fermat.IsWeightTwoEigenform M g b) (hnew : Fermat.IsNewEigenformAt M b) :
      ∀ M' : ℕ, M' ∣ M → M' ≠ M →
        ∀ g' : CuspForm (Gamma0GL M') 2, IsWeightTwoEigenform M' g' →
          ¬ ∀ q : ℕ, q.Prime → ¬ q ∣ M → qCoeff M' g' q = qCoeff M g q
  ```

  This is Atkin–Lehner 1970 Theorem 1 / Diamond–Shurman Thm 5.8.3 and it is the
  ONLY mathematics still missing under the leaf;

* and the assembled leaf itself,
  `exists_frickeSlash_eq_smul_of_isNewEigenformAt'`, over exactly those two.

So the leaf is a `−1 +1` on the frontier, with the surviving leaf being real
mathematics rather than a module-direction artefact. No new sorry is inherited
from the Atkin–Lehner side: its closure in `Interface.lean` is sorry-free.

Note the `sorry` above is honest under CLAUDE.md's rule — it replaces the proof
of an explicitly written proposition that is classical and true — but it is
*not* to be committed under `Fermat/` as-is: it lands only when the hoist lands,
as a properly docstring'd leaf.

## THE STEP-2 FINDING (the one the route asked for)

The route said: generalise `heckeTransform_slash_atkinLehnerRep` from a PRIME
`q ‖ M` to `Q = M`, and expect to have to weaken the same hypothesis on
`atkinLehnerConjIndex_injective`, `atkinLehnerConjIndex_some_ne_none` and
`exists_gamma0_atkinLehner_conj`. That is right, and the generalisation is
sharper than "replace prime by `Q = M`":

> In all five declarations, `hq : q.Prime` and `hrq : r ≠ q` are used
> **only** to produce `((q : ℕ) : ZMod r) ≠ 0` — i.e. `¬ r ∣ q` — plus
> `(q : ℤ) ≠ 0` / `(q : ℝ) ≠ 0`.

So the correct weakening is

    (hq : q.Prime) (hrq : r ≠ q)   ⟶   (hq0n : q ≠ 0) (hqr : ¬ r ∣ q)

with `hr : r.Prime` genuinely needed (it gives `Fact r.Prime`, hence the field
structure on `ZMod r` used by `div_eq_div_iff` and `inv_mul_cancel₀`, and it is
consumed by `exists_gamma0_factor_inf` and `Nat.prime_iff_prime_int`).

**No step needs `q` prime.** At `Q = M` the new hypotheses are `M ≠ 0` and
`¬ r ∣ M`, both of which the Hecke side supplies anyway.

Existing consumers keep working with
`hq.ne_zero` and `fun h => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)`.

## THE ALTERNATIVE TO THE HOIST, CHECKED AND CLOSED

Before dispatching the hoist, one asks whether the Fricke/newform cluster could
instead move DOWNSTREAM of `Interface.lean` (a much smaller move). It cannot,
and the reason is worth the two minutes it costs to establish, because the
naive form of the check says the opposite.

`Interface → HardlyRamified/ModThree → FreyCurve/MazurTorsion → X0`
(`MazurTorsion.lean:289` and `ModThree.lean:51` both `public import` `X0.lean`;
`Interface.lean:170` imports it directly as well). So `MazurTorsion.lean` sits
between `X0.lean` and `Interface.lean`, and anything it uses must stay upstream
of `Interface.lean`.

The naive check — "does `MazurTorsion.lean` mention the cluster?" — says NO:
in comment-stripped source, `kenkuLevels`, `cuspPeriod`, `frickeSlash` and
`isFrickeEigenform` each occur **zero** times there (all 18 textual hits are
docstring). The real answer is the TRANSITIVE one. Inside `X0.lean` the cluster
runs down a 14-link thread, each link occurring exactly twice in comment-stripped
source (its declaration plus its single consumer):

    exists_frickeSlash_eq_smul_of_isNewEigenformAt
      → isFrickeEigenform_of_isNewEigenformAt
      → cuspPeriod_ne_zero_of_isNewEigenformAt
      → cuspPeriod_ne_zero_of_kenkuLevel
      → lFunction_apply_one_ne_zero_of_kenkuLevel
      → isTorsion_jacobian_of_kenkuLevel
      → finite_jacobian_of_kenkuLevel
      → hasRankZeroJacobian_of_kenkuLevel
      → {card_le_x0TwentySix, y0HasNoRationalPoint_of_sieveLevel,
         y0HasNoRationalPoint_of_witnessPrime}
      → the twelve  y0HasNoRationalPoint_*

and `MazurTorsion.lean` uses `y0HasNoRationalPoint` **32 times in non-comment
source**. So the cluster must stay upstream of `MazurTorsion.lean`, hence
upstream of `Interface.lean`. The hoist is the only direction.

## THE VERIFIED TEXT

Verified with `lake env lean` on a scratch module whose only import is
`Fermat.FLT.Modularity.Interface`, in worktree `flt-lean-148` on host
`cyclops`. Baseline for the worktree: `lake build Fermat.FLT.ModularCurve.X0`
= `Build completed successfully (4973 jobs)`, `EXIT=0`, 110
`declaration uses 'sorry'` warnings in `X0.lean`.

Everything below is namespace `GaloisRepresentation.Modularity`, with

```lean
open scoped ModularForm MatrixGroups Matrix
open Matrix.SpecialLinearGroup CongruenceSubgroup
```

The full text is in the code block at the end of this file. After the hoist,
paste steps 1–3 beside the Atkin–Lehner block and step 4 beside
`exists_smul_of_heckeOp_eq_smul_of_not_dvd_level`; the carrier-bridge section
and `eigensystem_minimal_of_isNewEigenformAt` must go in a module that sees BOTH
`Fermat.IsWeightTwoEigenform`/`Fermat.IsNewEigenformAt` (i.e. `X0.lean` or
upstream) and `qCoeff`/`IsWeightTwoNewform` (i.e. the new Atkin–Lehner module) —
after the hoist that is `X0.lean` itself. Then `X0.lean`'s leaf becomes the
last declaration of the block, with `eigensystem_minimal_of_isNewEigenformAt`
the only remaining `sorry`.

Two mechanical notes, both cost a cycle if rediscovered:

* `Fermat.Gamma0GL` and `Modularity.Gamma0GL` ARE defeq (the machine-checked
  note in `HeckeOperator.lean`), but they are not *syntactically* equal, so a
  `rw` chain that mixes them produces
  `Application type mismatch … in the application ⇑g` and a
  "not type-correct under the `instances` transparency level" note. Build the
  two coercion equations as separate `have`s and combine them with
  `Eq.trans` — `exact` unifies them at default transparency where `rw` will
  not. That is what `frickeSlash_eq_atkinLehnerOp` below does, and the naive
  `rw`-only version fails.
* `Function.Periodic.qParam 1` leaves a `((1 : ℝ) : ℂ)` that `ring_nf` will
  not clear; `rw [Complex.ofReal_one, div_one]` first.

```lean
import Fermat.FLT.Modularity.Interface

open scoped ModularForm MatrixGroups Matrix

namespace GaloisRepresentation.Modularity

open Matrix.SpecialLinearGroup CongruenceSubgroup

/-! ## STEP 1 — the Fricke involution IS `atkinLehnerOp M M`. -/

/-- The Fricke matrix as an Atkin–Lehner matrix for `Q = M`. -/
def frickeAL (M : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; (M : ℤ), 0]

theorem isAtkinLehnerMatrix_frickeAL (M : ℕ) : IsAtkinLehnerMatrix M M (frickeAL M) where
  det_eq := by rw [frickeAL, Matrix.det_fin_two_of]; ring
  dvd_zero_zero := by simp [frickeAL]
  dvd_one_zero := by simp [frickeAL]
  dvd_one_one := by simp [frickeAL]

theorem coprime_self_div_self {M : ℕ} (hM : M ≠ 0) : Nat.Coprime M (M / M) := by
  rw [Nat.div_self (Nat.pos_of_ne_zero hM)]; exact Nat.coprime_one_right M

theorem frickeAL_map_det {M : ℕ} :
    ((frickeAL M).map (Int.cast : ℤ → ℝ)).det = (M : ℝ) := by
  rw [Matrix.det_fin_two]
  simp [frickeAL]

theorem atkinLehnerRep_frickeAL {M : ℕ} (hM : M ≠ 0) :
    atkinLehnerRep (frickeAL M) = Fermat.frickeMatrix M hM := by
  have hne : ((frickeAL M).map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [frickeAL_map_det]; exact_mod_cast hM
  apply Units.ext
  rw [atkinLehnerRep_coe hne, Fermat.frickeMatrix_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeAL]

/-- **STEP 1**: `frickeSlash M hM g = atkinLehnerOp M M g`. -/
theorem frickeSlash_eq_atkinLehnerOp {M : ℕ} (hM : M ≠ 0)
    (g : CuspForm (Gamma0GL M) 2) :
    Fermat.frickeSlash M hM g = atkinLehnerOp M M g := by
  have h1 : ⇑(atkinLehnerOp M M g) = ⇑g ∣[(2 : ℤ)] atkinLehnerRep (frickeAL M) :=
    atkinLehnerOp_coe (Nat.pos_of_ne_zero hM) (dvd_refl M) (coprime_self_div_self hM)
      (isAtkinLehnerMatrix_frickeAL M) g
  have h2 : ⇑(Fermat.frickeSlash M hM g) = ⇑g ∣[(2 : ℤ)] atkinLehnerRep (frickeAL M) := by
    rw [atkinLehnerRep_frickeAL hM]
    exact Fermat.coe_frickeSlash M hM g
  exact DFunLike.coe_injective (h2.trans h1.symm)

/-! ## STEP 2 — the `q`-prime hypothesis is only ever `¬ r ∣ q`. -/

theorem atkinLehnerConjIndex_injective' {M q r : ℕ} (hr : r.Prime) (hqr : ¬ r ∣ q)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A) :
    Function.Injective (atkinLehnerConjIndex r A) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : ((q : ℕ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqr
  have hdet := atkinLehner_det_cast (r := r) hA
  intro x y hxy
  have key : atkinLehnerConjU r A x * atkinLehnerConjV r A y
      - atkinLehnerConjV r A x * atkinLehnerConjU r A y = 0 := by
    unfold atkinLehnerConjIndex at hxy
    by_cases h1 : atkinLehnerConjU r A x = 0
    · by_cases h2 : atkinLehnerConjU r A y = 0
      · rw [h1, h2]; ring
      · rw [if_pos h1, if_neg h2] at hxy; exact absurd hxy (by simp)
    · by_cases h2 : atkinLehnerConjU r A y = 0
      · rw [if_neg h1, if_pos h2] at hxy; exact absurd hxy (by simp)
      · rw [if_neg h1, if_neg h2] at hxy
        have h3 := Option.some.inj hxy
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h1 h2] at h3
        linear_combination -h3
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some jy =>
      exact absurd (by
        simp only [atkinLehnerConjU, atkinLehnerConjV] at key
        linear_combination -key - hdet : ((q : ℕ) : ZMod r) = 0) hq0
  | some jx =>
    cases y with
    | none =>
      exact absurd (by
        simp only [atkinLehnerConjU, atkinLehnerConjV] at key
        linear_combination key - hdet : ((q : ℕ) : ZMod r) = 0) hq0
    | some jy =>
      simp only [atkinLehnerConjU, atkinLehnerConjV] at key
      have : (jy - jx) * ((q : ℕ) : ZMod r) = 0 := by linear_combination key - (jy - jx) * hdet
      rcases mul_eq_zero.mp this with h | h
      · rw [sub_eq_zero] at h; rw [h]
      · exact absurd h hq0

theorem atkinLehnerConjIndex_some_ne_none' {M q r : ℕ} (hr : r.Prime) (hqr : ¬ r ∣ q)
    (hrM : r ∣ M) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    (j : ZMod r) : atkinLehnerConjIndex r A (some j) ≠ none := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : ((q : ℕ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hqr
  have hc : ((A 1 0 : ℤ) : ZMod r) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (Int.natCast_dvd_natCast.mpr hrM).trans hA.dvd_one_zero
  have hdet := atkinLehner_det_cast (r := r) hA
  rw [hc] at hdet
  have hu : atkinLehnerConjU r A (some j) ≠ 0 := by
    simp only [atkinLehnerConjU, hc, mul_zero, sub_zero]
    intro h
    apply hq0
    rw [← hdet, h]
    ring
  rw [atkinLehnerConjIndex, if_neg hu]
  simp

theorem exists_gamma0_atkinLehner_conj_core' {M q r : ℕ} (hq0n : q ≠ 0) (hr : r.Prime)
    (hqr : ¬ r ∣ q)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    {α : Matrix (Fin 2) (Fin 2) ℤ} (hαdet : α.det = (r : ℤ))
    {p0 p1 uZ vZ w00 w01 w10 w11 : ℤ}
    (hC00 : (A * α * Matrix.adjugate A) 0 0 = p0 * uZ + (r : ℤ) * w00)
    (hC01 : (A * α * Matrix.adjugate A) 0 1 = p0 * vZ + (r : ℤ) * w01)
    (hC10 : (A * α * Matrix.adjugate A) 1 0 = p1 * uZ + (r : ℤ) * w10)
    (hC11 : (A * α * Matrix.adjugate A) 1 1 = p1 * vZ + (r : ℤ) * w11)
    (hd00 : (q : ℤ) ∣ (A * α * Matrix.adjugate A) 0 0)
    (hd01 : (q : ℤ) ∣ (A * α * Matrix.adjugate A) 0 1)
    (hd10 : ((q : ℤ) * (M : ℤ)) ∣ (A * α * Matrix.adjugate A) 1 0)
    (hd11 : (q : ℤ) ∣ (A * α * Matrix.adjugate A) 1 1)
    (k : Option (ZMod r))
    (hk : k = if ((uZ : ZMod r)) = 0 then none
              else some ((vZ : ZMod r) * ((uZ : ZMod r))⁻¹))
    (hgood : k = none → ¬ (r ∣ M)) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      A * α = (γ : Matrix (Fin 2) (Fin 2) ℤ) * (heckeIndexMat r k * A) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq0n
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hr.ne_zero
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have hrq' : ¬ ((r : ℤ) ∣ (q : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    exact hqr
  have hcancel : ∀ z : ℤ, (r : ℤ) ∣ (q : ℤ) * z → (r : ℤ) ∣ z := by
    intro z hz
    rcases hrp.dvd_mul.mp hz with h | h
    · exact absurd h hrq'
    · exact h
  have hdetC : (A * α * Matrix.adjugate A).det = (q : ℤ) ^ 2 * (r : ℤ) := by
    rw [Matrix.det_mul, Matrix.det_mul, hA.det_eq, hαdet, det_adjugate_of_det_eq hA.det_eq]
    ring
  obtain ⟨B, hBsmul, hBdet, hB10⟩ :=
    exists_intMatrix_of_smul_dvd_det (M := M) hq0 hdetC hd00 hd01 hd10 hd11
  have hBe : ∀ i j, (A * α * Matrix.adjugate A) i j = (q : ℤ) * B i j := by
    intro i j; rw [hBsmul]; simp
  have hB00e : (q : ℤ) * B 0 0 = p0 * uZ + (r : ℤ) * w00 := (hBe 0 0).symm.trans hC00
  have hB01e : (q : ℤ) * B 0 1 = p0 * vZ + (r : ℤ) * w01 := (hBe 0 1).symm.trans hC01
  have hB10e : (q : ℤ) * B 1 0 = p1 * uZ + (r : ℤ) * w10 := (hBe 1 0).symm.trans hC10
  have hB11e : (q : ℤ) * B 1 1 = p1 * vZ + (r : ℤ) * w11 := (hBe 1 1).symm.trans hC11
  have hBA : B * A = A * α := by
    have h1 : ((q : ℤ) • B) * A = A * α * (Matrix.adjugate A * A) := by
      rw [← hBsmul, Matrix.mul_assoc]
    rw [Matrix.adjugate_mul, hA.det_eq] at h1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one] at h1
    exact smul_right_injective _ hq0 h1
  by_cases hu : ((uZ : ZMod r)) = 0
  · rw [if_pos hu] at hk
    subst hk
    have hru : (r : ℤ) ∣ uZ := by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hu
    have h1 : (r : ℤ) ∣ B 0 0 := by
      refine hcancel _ ?_
      rw [hB00e]
      exact dvd_add (hru.mul_left p0) (dvd_mul_right _ _)
    have h2 : (r : ℤ) ∣ B 1 0 := by
      refine hcancel _ ?_
      rw [hB10e]
      exact dvd_add (hru.mul_left p1) (dvd_mul_right _ _)
    obtain ⟨γ, hγ, hBγ⟩ := exists_gamma0_factor_inf hr (hgood rfl) hBdet hB10 h1 h2
    exact ⟨γ, hγ, by rw [← hBA, hBγ, Matrix.mul_assoc]⟩
  · rw [if_neg hu] at hk
    set kk : ZMod r := (vZ : ZMod r) * ((uZ : ZMod r))⁻¹ with hkk
    have hK : (r : ℤ) ∣ vZ - (kk.val : ℤ) * uZ := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id, hkk, mul_assoc, inv_mul_cancel₀ hu, mul_one, sub_self]
    have hd1 : (r : ℤ) ∣ B 0 1 - (kk.val : ℤ) * B 0 0 := by
      refine hcancel _ ?_
      have hexp : (q : ℤ) * (B 0 1 - (kk.val : ℤ) * B 0 0)
          = p0 * (vZ - (kk.val : ℤ) * uZ) + (r : ℤ) * (w01 - (kk.val : ℤ) * w00) := by
        linear_combination hB01e - (kk.val : ℤ) * hB00e
      rw [hexp]
      exact dvd_add (hK.mul_left p0) (dvd_mul_right _ _)
    have hd2 : (r : ℤ) ∣ B 1 1 - (kk.val : ℤ) * B 1 0 := by
      refine hcancel _ ?_
      have hexp : (q : ℤ) * (B 1 1 - (kk.val : ℤ) * B 1 0)
          = p1 * (vZ - (kk.val : ℤ) * uZ) + (r : ℤ) * (w11 - (kk.val : ℤ) * w10) := by
        linear_combination hB11e - (kk.val : ℤ) * hB10e
      rw [hexp]
      exact dvd_add (hK.mul_left p1) (dvd_mul_right _ _)
    obtain ⟨γ, hγ, hBγ⟩ := exists_gamma0_factor_finite hr0 kk hBdet hB10 hd1 hd2
    exact ⟨γ, hγ, by rw [← hBA, hBγ, hk, Matrix.mul_assoc]⟩

theorem exists_gamma0_atkinLehner_conj' {M q r : ℕ} (hq0n : q ≠ 0) (hqM : q ∣ M)
    (hr : r.Prime) (hqr : ¬ r ∣ q)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    (x : Option (ZMod r))
    (hgood : atkinLehnerConjIndex r A x = none → ¬ (r ∣ M)) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      A * heckeIndexMat r x
        = (γ : Matrix (Fin 2) (Fin 2) ℤ)
            * (heckeIndexMat r (atkinLehnerConjIndex r A x) * A) := by
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  have hqMz : (q : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hqM
  have hqa := hA.dvd_zero_zero
  have hMc := hA.dvd_one_zero
  have hqd := hA.dvd_one_one
  have hqc : (q : ℤ) ∣ A 1 0 := hqMz.trans hMc
  cases x with
  | some j =>
    have e00 : (A * heckeIndexMat r (some j) * Matrix.adjugate A) 0 0
        = A 0 0 * (A 1 1 - (j.val : ℤ) * A 1 0) + (r : ℤ) * (-(A 0 1 * A 1 0)) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e01 : (A * heckeIndexMat r (some j) * Matrix.adjugate A) 0 1
        = A 0 0 * ((j.val : ℤ) * A 0 0 - A 0 1) + (r : ℤ) * (A 0 0 * A 0 1) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e10 : (A * heckeIndexMat r (some j) * Matrix.adjugate A) 1 0
        = A 1 0 * (A 1 1 - (j.val : ℤ) * A 1 0) + (r : ℤ) * (-(A 1 1 * A 1 0)) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e11 : (A * heckeIndexMat r (some j) * Matrix.adjugate A) 1 1
        = A 1 0 * ((j.val : ℤ) * A 0 0 - A 0 1) + (r : ℤ) * (A 0 0 * A 1 1) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    refine exists_gamma0_atkinLehner_conj_core' hq0n hr hqr hA (heckeIndexMat_det r (some j))
      e00 e01 e10 e11 ?_ ?_ ?_ ?_ _ ?_ hgood
    · rw [e00]
      exact dvd_add (hqa.mul_right _) ((dvd_neg.mpr (hqc.mul_left _)).mul_left _)
    · rw [e01]
      exact dvd_add (hqa.mul_right _) ((hqa.mul_right _).mul_left _)
    · rw [e10]
      obtain ⟨m, hm⟩ := hMc
      obtain ⟨dd, hdd⟩ := hqd
      obtain ⟨mm, hmm⟩ := hqMz
      refine ⟨m * dd - (j.val : ℤ) * mm * m ^ 2 - (r : ℤ) * dd * m, ?_⟩
      rw [hm, hdd, hmm]
      ring
    · rw [e11]
      exact dvd_add (hqc.mul_right _) ((hqa.mul_right _).mul_left _)
    · have hcu : (((A 1 1 - (j.val : ℤ) * A 1 0 : ℤ)) : ZMod r) = atkinLehnerConjU r A (some j) := by
        simp [atkinLehnerConjU, ZMod.natCast_val, ZMod.cast_id]
      have hcv : ((((j.val : ℤ) * A 0 0 - A 0 1 : ℤ)) : ZMod r) = atkinLehnerConjV r A (some j) := by
        simp [atkinLehnerConjV, ZMod.natCast_val, ZMod.cast_id]
      rw [hcu, hcv, atkinLehnerConjIndex]
  | none =>
    have e00 : (A * heckeIndexMat r none * Matrix.adjugate A) 0 0
        = A 0 1 * (-(A 1 0)) + (r : ℤ) * (A 0 0 * A 1 1) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e01 : (A * heckeIndexMat r none * Matrix.adjugate A) 0 1
        = A 0 1 * (A 0 0) + (r : ℤ) * (-(A 0 0 * A 0 1)) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e10 : (A * heckeIndexMat r none * Matrix.adjugate A) 1 0
        = A 1 1 * (-(A 1 0)) + (r : ℤ) * (A 1 1 * A 1 0) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    have e11 : (A * heckeIndexMat r none * Matrix.adjugate A) 1 1
        = A 1 1 * (A 0 0) + (r : ℤ) * (-(A 0 1 * A 1 0)) := by
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      ring
    refine exists_gamma0_atkinLehner_conj_core' hq0n hr hqr hA (heckeIndexMat_det r none)
      e00 e01 e10 e11 ?_ ?_ ?_ ?_ _ ?_ hgood
    · rw [e00]
      exact dvd_add ((dvd_neg.mpr hqc).mul_left _) ((hqa.mul_right _).mul_left _)
    · rw [e01]
      exact dvd_add (hqa.mul_left _) ((dvd_neg.mpr (hqa.mul_right _)).mul_left _)
    · rw [e10]
      obtain ⟨m, hm⟩ := hMc
      obtain ⟨dd, hdd⟩ := hqd
      refine ⟨-(dd * m) + (r : ℤ) * dd * m, ?_⟩
      rw [hm, hdd]
      ring
    · rw [e11]
      exact dvd_add (hqa.mul_left _) ((dvd_neg.mpr (hqc.mul_left _)).mul_left _)
    · have hcu : (((-(A 1 0) : ℤ)) : ZMod r) = atkinLehnerConjU r A none := by
        simp [atkinLehnerConjU]
      have hcv : (((A 0 0 : ℤ)) : ZMod r) = atkinLehnerConjV r A none := by
        simp [atkinLehnerConjV]
      rw [hcu, hcv, atkinLehnerConjIndex]

theorem heckeTransform_slash_atkinLehnerRep' {M q : ℕ} (hq0n : q ≠ 0) (hqM : q ∣ M)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    {r : ℕ} (hr : r.Prime) (hqr : ¬ r ∣ q) (f : CuspForm (Gamma0GL M) 2) :
    heckeTransform M r (⇑f ∣[(2 : ℤ)] atkinLehnerRep A)
      = (heckeTransform M r ⇑f) ∣[(2 : ℤ)] atkinLehnerRep A := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  have hq0R : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq0n
  have hr0R : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  have hAne : ((A.map (Int.cast : ℤ → ℝ)).det) ≠ 0 := det_map_cast_ne_zero_isAL hq0R hA
  have hbij : Function.Bijective (atkinLehnerConjIndex r A) :=
    Finite.injective_iff_bijective.mp (atkinLehnerConjIndex_injective' hr hqr hA)
  have hmem : ∀ x : Option (ZMod r), x ∈ heckeIndexSet M r ↔
      atkinLehnerConjIndex r A x ∈ heckeIndexSet M r := by
    intro x
    unfold heckeIndexSet
    split_ifs with h
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        rcases Option.ne_none_iff_exists.mp
          (atkinLehnerConjIndex_some_ne_none' hr hqr h hA j) with ⟨k, hk⟩
        exact ⟨k, hk⟩
      · rintro ⟨k, hk⟩
        cases x with
        | none => rw [atkinLehnerConjIndex_none h hA] at hk; exact absurd hk (by simp)
        | some j => exact ⟨j, rfl⟩
    · simp
  rw [heckeTransform_eq_sum_heckeIndexSet, heckeTransform_eq_sum_heckeIndexSet, finset_sum_slash]
  refine Finset.sum_bijective (atkinLehnerConjIndex r A) hbij hmem ?_
  intro x hx
  have hgood : atkinLehnerConjIndex r A x = none → ¬ (r ∣ M) := by
    intro hnone hrM
    unfold heckeIndexSet at hx
    rw [if_pos hrM] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    exact atkinLehnerConjIndex_some_ne_none' hr hqr hrM hA j hnone
  obtain ⟨γ, hγ, hmat⟩ := exists_gamma0_atkinLehner_conj' hq0n hqM hr hqr hA x hgood
  have hGL : atkinLehnerRep A * heckeIndexRep r x
      = mapGL ℝ γ * (heckeIndexRep r (atkinLehnerConjIndex r A x) * atkinLehnerRep A) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul,
      atkinLehnerRep_coe hAne, heckeIndexRep_coe hr0R, heckeIndexRep_coe hr0R,
      mapGL_coe_matrix_int, ← intMatrix_map_cast_mul, ← intMatrix_map_cast_mul,
      ← intMatrix_map_cast_mul, hmat]
  rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq f (mapGL ℝ γ) (mem_Gamma0GL_iff.mpr ⟨γ, hγ, rfl⟩),
    SlashAction.slash_mul]

/-! ## STEP 3 — `T_r` commutes with the FRICKE involution `W_M`, for `r ∤ M`. -/

theorem heckeOp_comm_atkinLehnerOp_self {M : ℕ} (hM : 0 < M)
    {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ M) (f : CuspForm (Gamma0GL M) 2) :
    heckeOp M r (atkinLehnerOp M M f) = atkinLehnerOp M M (heckeOp M r f) := by
  have hM0 : M ≠ 0 := hM.ne'
  have hcop := coprime_self_div_self hM0
  have hA := isAtkinLehnerMatrix_frickeAL M
  apply DFunLike.coe_injective
  have h1 : ⇑(heckeOp M r (atkinLehnerOp M M f))
      = heckeTransform M r (⇑f ∣[(2 : ℤ)] atkinLehnerRep (frickeAL M)) := by
    rw [heckeOp_coe hM hr, atkinLehnerOp_coe hM (dvd_refl M) hcop hA]
  have h2 : ⇑(atkinLehnerOp M M (heckeOp M r f))
      = (heckeTransform M r ⇑f) ∣[(2 : ℤ)] atkinLehnerRep (frickeAL M) := by
    rw [atkinLehnerOp_coe hM (dvd_refl M) hcop hA, heckeOp_coe hM hr]
  rw [h1, h2]
  exact heckeTransform_slash_atkinLehnerRep' hM0 (dvd_refl M) hA hr hrM f

/-! ## STEP 4 — assembly. -/

/-- **ATKIN–LEHNER MULTIPLICITY ONE FOR THE FRICKE INVOLUTION**: on a
weight-two NEWFORM of level `M`, the Fricke partner is a scalar multiple. -/
theorem exists_frickeSlash_eq_smul_of_isWeightTwoNewform {M : ℕ} (hM : M ≠ 0)
    (g : CuspForm (Gamma0GL M) 2) (hg : IsWeightTwoNewform M g) :
    ∃ c : ℂ, Fermat.frickeSlash M hM g = c • g := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hv : ∀ q : ℕ, q.Prime → ¬ q ∣ M →
      heckeOp M q (atkinLehnerOp M M g) = qCoeff M g q • atkinLehnerOp M M g := by
    intro q hq hqM
    rw [heckeOp_comm_atkinLehnerOp_self hMpos hq hqM,
      heckeOp_apply_eq_smul_of_isWeightTwoEigenform hMpos hg.toIsWeightTwoEigenform hq,
      map_smul]
  obtain ⟨c, hc⟩ := exists_smul_of_heckeOp_eq_smul_of_not_dvd_level hMpos hg hv
  exact ⟨c, by rw [frickeSlash_eq_atkinLehnerOp hM g, hc]⟩


open Complex UpperHalfPlane

local notation "𝕢" => Function.Periodic.qParam

/-- The carrier sequence of `Fermat.IsWeightTwoEigenform` IS the pin's
`q`-expansion coefficient sequence. -/
theorem qCoeff_eq_of_isWeightTwoEigenform {M : ℕ} {g : CuspForm (Gamma0GL M) 2} {b : ℕ → ℂ}
    (hb : Fermat.IsWeightTwoEigenform M g b) (n : ℕ) : qCoeff M g n = b n := by
  have hq : ∀ (τ : ℍ) (m : ℕ),
      b m • (𝕢 1 (τ : ℂ)) ^ m
        = b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (τ : ℂ)) := by
    intro τ m
    rw [smul_eq_mul, Function.Periodic.qParam, Complex.ofReal_one, div_one,
      ← Complex.exp_nat_mul]
    ring_nf
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => b m • (𝕢 1 (τ : ℂ)) ^ m) (g τ) := by
    intro τ
    have h1 : HasSum
        (fun n : ℕ => b (n + 1) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) * (τ : ℂ))) (g τ) := by
      have hs := (hb.qExpansionSummable τ).hasSum
      rwa [← hb.qExpansion τ] at hs
    have h2 : HasSum (fun n : ℕ => (fun m : ℕ => b m • (𝕢 1 (τ : ℂ)) ^ m) (n + 1)) (g τ) := by
      refine h1.congr_fun ?_
      intro n
      show b (n + 1) • (𝕢 1 (τ : ℂ)) ^ (n + 1)
          = b (n + 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) * (τ : ℂ))
      rw [hq τ (n + 1)]
      push_cast
      ring_nf
    have h3 := (hasSum_nat_add_iff (f := fun m : ℕ => b m • (𝕢 1 (τ : ℂ)) ^ m) 1).mp h2
    simpa [hb.zero] using h3
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0GL M) hsum n).symm

section Carrier

variable {M : ℕ} {g : CuspForm (Gamma0GL M) 2} {b : ℕ → ℂ}

/-- A prime not dividing `n` multiplies out of the carrier. -/
theorem carrier_mul_prime_of_not_dvd (hb : Fermat.IsWeightTwoEigenform M g b)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) :
    b (n * p) = b p * b n := by
  by_cases hpM : p ∣ M
  · exact hb.atkin p hp hpM n hn
  · have h := hb.hecke p hp hpM n hn
    rw [if_neg hpn] at h
    simpa using h

/-- `b (p^k * n) = b (p^k) * b n` when `p ∤ n`. -/
theorem carrier_pow_mul (hb : Fermat.IsWeightTwoEigenform M g b)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n) :
    ∀ k : ℕ, b (p ^ k * n) = b (p ^ k) * b n := by
  have key : ∀ k : ℕ, b (p ^ k * n) = b (p ^ k) * b n ∧
      b (p ^ (k + 1) * n) = b (p ^ (k + 1)) * b n := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [hb.one], ?_⟩
      rw [pow_one, mul_comm p n]
      exact carrier_mul_prime_of_not_dvd hb hp hn hpn
    | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨ih1, ?_⟩
      show b (p ^ (k + 2) * n) = b (p ^ (k + 2)) * b n
      have hppos : 0 < p ^ (k + 1) * n := Nat.mul_pos (pow_pos hp.pos _) hn
      have hpdvd : p ∣ p ^ (k + 1) * n :=
        Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero k)) n
      have hdiv : p ^ (k + 1) * n / p = p ^ k * n := by
        rw [pow_succ, mul_comm (p ^ k) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      have hpdvd' : p ∣ p ^ (k + 1) := dvd_pow_self p (Nat.succ_ne_zero k)
      have hdiv' : p ^ (k + 1) / p = p ^ k := by
        rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
      have hshape : p ^ (k + 1) * n * p = p ^ (k + 2) * n := by ring
      have hshape' : p ^ (k + 1) * p = p ^ (k + 2) := by ring
      by_cases hpM : p ∣ M
      · have h1 := hb.atkin p hp hpM (p ^ (k + 1) * n) hppos
        have h2 := hb.atkin p hp hpM (p ^ (k + 1)) (pow_pos hp.pos _)
        rw [hshape] at h1
        rw [hshape'] at h2
        rw [h1, h2, ih1]
        ring
      · have h1 := hb.hecke p hp hpM (p ^ (k + 1) * n) hppos
        have h2 := hb.hecke p hp hpM (p ^ (k + 1)) (pow_pos hp.pos _)
        rw [if_pos hpdvd, hdiv, hshape] at h1
        rw [if_pos hpdvd', hdiv', hshape'] at h2
        have e1 : b (p ^ (k + 2) * n) = b p * b (p ^ (k + 1) * n) - p * b (p ^ k * n) := by
          linear_combination h1
        have e2 : b (p ^ (k + 2)) = b p * b (p ^ (k + 1)) - p * b (p ^ k) := by
          linear_combination h2
        rw [e1, e2, ih0, ih1]
        ring
  exact fun k => (key k).1

/-- **Full multiplicativity of the carrier at coprime arguments.** -/
theorem carrier_mul_coprime (hb : Fermat.IsWeightTwoEigenform M g b) :
    ∀ m n : ℕ, m.Coprime n → 0 < n → b (m * n) = b m * b n := by
  intro m
  induction m using Nat.recOnPrimePow with
  | zero =>
    intro n hcop _
    have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hcop
    subst hn1
    simp [hb.one]
  | one => intro n _ _; simp [hb.one]
  | prime_pow_mul a p k hp hpa hk ih =>
    intro n hcop hn
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hpa (dvd_zero p))
    have hppa : p ∣ p ^ k * a := Dvd.dvd.mul_right (dvd_pow_self p hk.ne') a
    have hpn : ¬ p ∣ n := by
      intro hd
      have hg : p ∣ Nat.gcd (p ^ k * a) n := Nat.dvd_gcd hppa hd
      rw [Nat.Coprime] at hcop
      rw [hcop] at hg
      exact hp.ne_one (Nat.dvd_one.mp hg)
    have hpan : ¬ p ∣ a * n := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact hpa h
      · exact hpn h
    have hcopan : a.Coprime n :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left a (p ^ k)) hcop
    have h1 : b (p ^ k * a * n) = b (p ^ k) * b (a * n) := by
      rw [mul_assoc]
      exact carrier_pow_mul hb hp (Nat.mul_pos ha hn) hpan k
    have h2 : b (p ^ k * a) = b (p ^ k) * b a := carrier_pow_mul hb hp ha hpa k
    rw [h1, ih n hcopan hn, h2]
    ring

/-- **THE CARRIER BRIDGE, coefficient half**: the carried-coefficient
eigenform predicate implies the `qCoeff`-based one. -/
theorem isWeightTwoEigenform_of_carrier (hb : Fermat.IsWeightTwoEigenform M g b) :
    IsWeightTwoEigenform M g where
  qCoeff_one := by rw [qCoeff_eq_of_isWeightTwoEigenform hb]; exact hb.one
  qCoeff_mul_coprime := by
    intro m n hmn
    simp only [qCoeff_eq_of_isWeightTwoEigenform hb]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
      subst hm1
      simp [hb.one]
    · exact carrier_mul_coprime hb m n hmn hn
  qCoeff_prime_pow_of_not_dvd := by
    intro q hq hqM r
    simp only [qCoeff_eq_of_isWeightTwoEigenform hb]
    have h := hb.hecke q hq hqM (q ^ (r + 1)) (pow_pos hq.pos _)
    rw [if_pos (dvd_pow_self q (Nat.succ_ne_zero r)),
      show q ^ (r + 1) / q = q ^ r by rw [pow_succ, Nat.mul_div_cancel _ hq.pos],
      show q ^ (r + 1) * q = q ^ (r + 2) by ring] at h
    linear_combination h
  qCoeff_prime_pow_of_dvd := by
    intro q hq hqM r
    simp only [qCoeff_eq_of_isWeightTwoEigenform hb]
    have h := hb.atkin q hq hqM (q ^ r) (pow_pos hq.pos r)
    rw [show q ^ r * q = q ^ (r + 1) by ring] at h
    exact h

end Carrier

/-! ## THE RESIDUE — the ONE genuine gap, as a named leaf. -/

theorem eigensystem_minimal_of_isNewEigenformAt {M : ℕ} (hM : M ≠ 0)
    {g : CuspForm (Gamma0GL M) 2} {b : ℕ → ℂ}
    (hb : Fermat.IsWeightTwoEigenform M g b) (hnew : Fermat.IsNewEigenformAt M b) :
    ∀ M' : ℕ, M' ∣ M → M' ≠ M →
      ∀ g' : CuspForm (Gamma0GL M') 2, IsWeightTwoEigenform M' g' →
        ¬ ∀ q : ℕ, q.Prime → ¬ q ∣ M → qCoeff M' g' q = qCoeff M g q :=
  sorry

/-! ## THE LEAF ITSELF, assembled. -/

theorem exists_frickeSlash_eq_smul_of_isNewEigenformAt' {M : ℕ} (hM : M ≠ 0)
    (g : CuspForm (Gamma0GL M) 2) (b : ℕ → ℂ)
    (hb : Fermat.IsWeightTwoEigenform M g b) (hnew : Fermat.IsNewEigenformAt M b) :
    ∃ c : ℂ, Fermat.frickeSlash M hM g = c • g :=
  exists_frickeSlash_eq_smul_of_isWeightTwoNewform hM g
    { toIsWeightTwoEigenform := isWeightTwoEigenform_of_carrier hb
      eigensystem_minimal := eigensystem_minimal_of_isNewEigenformAt hM hb hnew }

end GaloisRepresentation.Modularity
```

