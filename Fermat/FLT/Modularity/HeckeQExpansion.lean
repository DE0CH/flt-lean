/-
Modularity/HeckeQExpansion.lean — own work for the Fermat project.

# The `q`-expansion layer of `S₂(Γ₀(N))` and of the weight-2 Hecke slash-sum

This module exists for exactly one reason: **`ModularCurve/X0.lean` needs
`qCoeff` and `qExpansion_heckeTransform_coeff`, and they lived in
`Modularity/Interface.lean`, which is DOWNSTREAM of `X0.lean`.**  Every
declaration below was hoisted VERBATIM out of `Interface.lean` on
2026-07-31; none of it was written here and none of it was changed in the
move.  The namespace is unchanged (`GaloisRepresentation.Modularity`), so
no consumer anywhere in the tree needs editing — the names resolve exactly
as before.

## Why a NEW module rather than more of `HeckeOperator.lean`

`Modularity/HeckeOperator.lean` breaks the module cycle
`Interface → ModThree → MazurTorsion → X0` for `Gamma0GL`/`heckeOp`, and
its own docstring asks, in terms, that it stay SMALL and not grow into a
second modular-forms file.  This module honours that: it imports
`HeckeOperator` and adds the `q`-expansion layer on top, so the two
concerns stay separable and a future reader can see at a glance which
block moved.

## The reference scan that justified the cut (re-run 2026-07-31)

The moved block references, outside itself and outside mathlib, ONLY:
`Gamma0GL`, `heckeRep`, `heckeRepInf`, `heckeRep_coe`, `heckeRepInf_coe`,
`σ_heckeRep`, `σ_heckeRepInf`, `heckeTransform` and
`exists_cuspForm_heckeTransform` — all nine in `HeckeOperator.lean`.
Nothing in it mentions anything defined in `Interface.lean`.  That is what
made the move a cut and paste rather than a port, and it is the scan the
audit on `charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable` (`X0.lean`)
told its next owner to re-run before moving anything.

## WHAT IS HERE, and what deliberately is NOT

Here: `qCoeff` (the width-1 Fourier coefficient at `∞`), its vanishing at
`n = 0`, its linear-functional form `qCoeffL`, the `q`-expansion principle
`cuspForm_eq_of_forall_qCoeff_eq`, and the whole `HeckeQExpansion`
toolkit culminating in `qExpansion_heckeTransform_coeff` — Diamond–Shurman
Proposition 5.2.2 at weight 2.

NOT here, and deliberately left in `Interface.lean`: `IsWeightTwoEigenform`
and the eigenform carriers, `heckeField`, the Sturm bound
`exists_cuspForm_sturm_bound`, `cuspForm_finiteDimensional`, the Hecke
algebra and `EichlerShimuraPackage`.  None of those is needed by `X0.lean`:
the Hecke leaf there takes a `Module.Basis (Fin d)` as a HYPOTHESIS, so
finite dimensionality is a consequence rather than a prerequisite, which is
what shrank this hoist from "the whole `q`-expansion layer" to the block
below.  Do not migrate more here without re-running the scan above.

## WHAT THIS BUYS, stated plainly, so nobody re-derives it

With this module upstream, the two open leaves of `x0HeckeCharpolyTable`
can be attacked through `q`-expansions inside `X0.lean` itself.  The bridge
`charpoly_toMatrix_heckeOp_of_qCoeff` in `X0.lean` is built directly on
`qCoeffL`, `cuspForm_eq_of_forall_qCoeff_eq` and
`qExpansion_heckeTransform_coeff` from here, and it reduces
`charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable` to a statement with no
modular forms in it at all — a linear-algebra identity among the numbers
`aₘ(bᵢ)`.  The hoist CLOSES NOTHING by itself; it is what makes the closing
argument expressible.
-/
module

public import Fermat.FLT.Modularity.HeckeOperator
-- `Complex.exp_two_pi_mul_I_mul_div_eq_one_iff`, the root-of-unity criterion
-- behind `heckeRep_char_sum`.
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
-- `geom_sum_eq`, same proof.  NOTE the module path: at this pin the lemma is in
-- `Mathlib/Algebra/Field/GeomSum.lean`, NOT `Mathlib/Algebra/GeomSum.lean`,
-- which does not exist.
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

namespace GaloisRepresentation.Modularity

open scoped MatrixGroups Matrix

open UpperHalfPlane ModularForm

/-- The `n`-th `q`-expansion coefficient `aₙ(f)` of a weight-2 level-`N`
cusp form, through the pin's `UpperHalfPlane.qExpansion` at width `1`
(the translation `τ ↦ τ + 1` lies in `Γ₀(N)` for every `N`, so `1` is a
strict period and this is the classical Fourier coefficient at the cusp
`∞`). -/
noncomputable def qCoeff (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

/-- `1` is a strict period of `Γ₀(N)` in its `GL₂(ℝ)` incarnation: the
translation matrix `[1, 1; 0, 1]` lies in `Γ₀(N)` for every `N`. This
is what makes `qCoeff` (the width-1 `q`-expansion coefficient) the
classical Fourier coefficient, and it feeds the cusp-vanishing
computation `qCoeff_zero` below. -/
theorem one_mem_strictPeriods_Gamma0GL (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0GL N).strictPeriods := by
  show (1 : ℝ) ∈
    (↑(CongruenceSubgroup.Gamma0 N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- `a₀(f) = 0` for a weight-2 level-`N` cusp form: the constant term
of the `q`-expansion is the value at the cusp `i∞`, which vanishes for
a cusp form. Needed because `heckeField` adjoins ALL coefficients,
including the zeroth. -/
theorem qCoeff_zero (N : ℕ) (f : CuspForm (Gamma0GL N) 2) :
    qCoeff N f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero (Γ := Gamma0GL N) (k := 2) f
    one_pos (one_mem_strictPeriods_Gamma0GL N)

/-! #### The `q`-expansion of the Hecke slash-sum

Diamond–Shurman Proposition 5.2.2 at weight 2, trivial character,
computed entirely on the pin's `hasSum_qExpansion` /
`qExpansion_coeff_unique` API. The toolkit below evaluates the slash
summands pointwise (`heckeRep_slash_apply` — with mathlib's
normalization the `[1, j; 0, q]` summand is `f((τ+j)/q)/q` and the
`[q, 0; 0, 1]` summand is `q·f(qτ)`), sums the additive character
(`heckeRep_char_sum`: `Σ_{j<q} e^{2πinj/q} = q·1_{q∣n}`), and moves
between the width-`q` and width-1 `q`-parameters
(`qParam_nat_pow`/`qParam_shift`/`qParam_nat_mul`). -/
section HeckeQExpansion

open Complex

/-- The determinant of the Hecke representative is `q`. -/
theorem heckeRep_det_val {q : ℕ} (hq0 : (q : ℝ) ≠ 0) (j : ℕ) :
    ((heckeRep q j).det.val : ℝ) = q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, heckeRep_coe hq0,
    Matrix.det_fin_two_of]
  simp

/-- The determinant of the extra Hecke representative is `q`. -/
theorem heckeRepInf_det_val {q : ℕ} (hq0 : (q : ℝ) ≠ 0) :
    ((heckeRepInf q).det.val : ℝ) = q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, heckeRepInf_coe hq0,
    Matrix.det_fin_two_of]
  simp

/-- The Möbius action of the Hecke representative: `τ ↦ (τ + j)/q`. -/
theorem heckeRep_smul_coe {q : ℕ} (hqpos : 0 < q) (j : ℕ) (τ : ℍ) :
    ((heckeRep q j • τ : ℍ) : ℂ) = ((τ : ℂ) + j) / q := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  have hdet : (0 : ℝ) < (heckeRep q j).det.val := by
    rw [heckeRep_det_val hq0]
    exact_mod_cast hqpos
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num,
    UpperHalfPlane.denom, heckeRep_coe hq0]
  show (((1 : ℝ) : ℂ) * ↑τ + ((j : ℝ) : ℂ)) / (((0 : ℝ) : ℂ) * ↑τ + ((q : ℝ) : ℂ)) = _
  push_cast
  try ring

/-- The Möbius action of the extra Hecke representative: `τ ↦ qτ`. -/
theorem heckeRepInf_smul_coe {q : ℕ} (hqpos : 0 < q) (τ : ℍ) :
    ((heckeRepInf q • τ : ℍ) : ℂ) = q * (τ : ℂ) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  have hdet : (0 : ℝ) < (heckeRepInf q).det.val := by
    rw [heckeRepInf_det_val hq0]
    exact_mod_cast hqpos
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num,
    UpperHalfPlane.denom, heckeRepInf_coe hq0]
  show (((q : ℝ) : ℂ) * ↑τ + ((0 : ℝ) : ℂ)) / (((0 : ℝ) : ℂ) * ↑τ + ((1 : ℝ) : ℂ)) = _
  push_cast
  try ring

/-- Pointwise value of the weight-2 slash by `[1, j; 0, q]`:
`(f ∣[2] heckeRep q j)(τ) = f(heckeRep q j • τ)/q` (mathlib
normalization: `det^{k−1}·denom^{−k} = q·q^{−2} = 1/q`). -/
theorem heckeRep_slash_apply {q : ℕ} (hqpos : 0 < q) (j : ℕ) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[(2 : ℤ)] heckeRep q j) τ = (1 / q : ℂ) * f (heckeRep q j • τ) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  rw [ModularForm.slash_apply]
  have hdetpos : (0 : ℝ) < (heckeRep q j).det.val := by
    rw [heckeRep_det_val hq0]; exact_mod_cast hqpos
  have hσ : σ (heckeRep q j) (f (heckeRep q j • τ)) = f (heckeRep q j • τ) :=
    σ_heckeRep q j _
  have hdenom : denom (heckeRep q j) ↑τ = (q : ℂ) := by
    rw [UpperHalfPlane.denom, heckeRep_coe hq0]
    show ((0 : ℝ) : ℂ) * ↑τ + ((q : ℝ) : ℂ) = _
    push_cast
    ring
  rw [hσ, hdenom, heckeRep_det_val hq0, abs_of_pos (by exact_mod_cast hqpos)]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  push_cast
  field_simp

/-- Pointwise value of the weight-2 slash by `[q, 0; 0, 1]`:
`(f ∣[2] heckeRepInf q)(τ) = q·f(heckeRepInf q • τ)`. -/
theorem heckeRepInf_slash_apply {q : ℕ} (hqpos : 0 < q) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[(2 : ℤ)] heckeRepInf q) τ = (q : ℂ) * f (heckeRepInf q • τ) := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
  rw [ModularForm.slash_apply]
  have hσ : σ (heckeRepInf q) (f (heckeRepInf q • τ)) = f (heckeRepInf q • τ) :=
    σ_heckeRepInf q _
  have hdenom : denom (heckeRepInf q) ↑τ = (1 : ℂ) := by
    rw [UpperHalfPlane.denom, heckeRepInf_coe hq0]
    show ((0 : ℝ) : ℂ) * ↑τ + ((1 : ℝ) : ℂ) = _
    push_cast
    ring
  rw [hσ, hdenom, heckeRepInf_det_val hq0, abs_of_pos (by exact_mod_cast hqpos)]
  push_cast
  simp [zpow_one, mul_comm]

/-- The additive character sum: `Σ_{j<q} e^{2πin/q·j} = q·1_{q ∣ n}`
(geometric series; the ratio is a `q`-th root of unity, equal to `1`
exactly when `q ∣ n`). -/
theorem heckeRep_char_sum {q : ℕ} (hqpos : 0 < q) (n : ℕ) :
    ∑ j ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j
      = if q ∣ n then (q : ℂ) else 0 := by
  by_cases h : q ∣ n
  · rw [if_pos h]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * n / q) = 1 :=
      (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hqpos.ne').mpr h
    simp [h1]
  · rw [if_neg h]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * n / q) ≠ 1 := fun hc =>
      h ((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hqpos.ne').mp hc)
    rw [geom_sum_eq h1]
    have h3 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
    have h2 : Complex.exp (2 * Real.pi * Complex.I * n / q) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have h4 : (q : ℂ) * (2 * Real.pi * Complex.I * n / q)
          = 2 * Real.pi * Complex.I * n / ((1 : ℕ) : ℂ) := by
        push_cast
        field_simp
      rw [h4]
      exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff one_ne_zero).mpr
        (one_dvd n)
    rw [h2]
    simp

/-- The width-`q` `q`-parameter, raised to the `q`, is the width-1
parameter: `e^{2πiz/q·q} = e^{2πiz}`. -/
theorem qParam_nat_pow {q : ℕ} (hq0 : (q : ℝ) ≠ 0) (z : ℂ) :
    Function.Periodic.qParam (q : ℝ) z ^ q = Function.Periodic.qParam 1 z := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  have h3 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  push_cast
  field_simp

/-- The width-1 parameter at the moved point `(z + j)/q` splits as the
width-`q` parameter times a root of unity. -/
theorem qParam_shift {q : ℕ} (hq0 : (q : ℝ) ≠ 0) (j : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((z + j) / q)
      = Function.Periodic.qParam (q : ℝ) z *
          Complex.exp (2 * Real.pi * Complex.I * j / q) := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_add]
  congr 1
  have h3 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  push_cast
  field_simp
  try ring

/-- The width-1 parameter at `qz` is the `q`-th power of the width-1
parameter. -/
theorem qParam_nat_mul (q : ℕ) (z : ℂ) :
    Function.Periodic.qParam 1 ((q : ℂ) * z)
      = Function.Periodic.qParam 1 z ^ q := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The `q`-expansion of the Hecke slash-sum** (Diamond–Shurman
Proposition 5.2.2 at weight 2, trivial character):
`a_m(T_q f) = a_{qm}(f)` for `q ∣ N`, and
`a_m(T_q f) = a_{qm}(f) + q·a_{m/q}(f)` (second term only when
`q ∣ m`) for `q ∤ N`. Proof, entirely analytic on this pin's
`hasSum_qExpansion` API: substituting the width-1 `q`-expansion of `f`
into the finite slash-sum, the `q` upper-triangular representatives
average the additive character (`heckeRep_char_sum`), reindexing
`m ↦ qm`, while the extra representative contributes `q·f(qτ)`,
reindexing `m ↦ m/q`; the resulting everywhere-convergent expansion is
THE `q`-expansion by `ModularFormClass.qExpansion_coeff_unique`
(analyticity of the cusp function coming from
`exists_cuspForm_heckeTransform`). -/
theorem qExpansion_heckeTransform_coeff {N : ℕ} (hN : 0 < N) {q : ℕ}
    (hq : q.Prime) (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    (qExpansion 1 (heckeTransform N q ⇑f)).coeff m =
      qCoeff N f (q * m) +
        (if q ∣ N then 0 else if q ∣ m then (q : ℂ) * qCoeff N f (m / q) else 0) := by
  have hqpos : 0 < q := hq.pos
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  -- the `q`-expansion of `f` itself, as a `HasSum` at every point
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f
      (one_mem_strictPeriods_Gamma0GL N)
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty ⇑f := by
    have hc : IsCusp OnePoint.infty (Gamma0GL N) :=
      (Gamma0GL N).isCusp_of_mem_strictPeriods one_pos
        (one_mem_strictPeriods_Gamma0GL N)
    exact (OnePoint.isZeroAt_infty_iff.mp
      (CuspFormClass.zero_at_cusps f hc)).boundedAtFilter
  have hsumf : ∀ τ : ℍ, HasSum
      (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 ↑τ ^ n) (f τ) :=
    fun τ => hasSum_qExpansion one_pos hper (CuspFormClass.holo f) hbdd τ
  have hinj : Function.Injective (fun m : ℕ => q * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hqpos h
  -- the master `HasSum` for the transform, at every point
  have hmaster : ∀ τ : ℍ, HasSum (fun n : ℕ =>
      (qCoeff N f (q * n) +
        (if q ∣ N then 0 else if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0)) •
        Function.Periodic.qParam 1 ↑τ ^ n)
      (heckeTransform N q ⇑f τ) := by
    intro τ
    -- part 1: the `q` upper-triangular representatives
    have hj : ∀ j : ℕ, HasSum (fun n : ℕ =>
        (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
          (Function.Periodic.qParam (q : ℝ) ↑τ ^ n *
            Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j)))
        ((⇑f ∣[(2 : ℤ)] heckeRep q j) τ) := by
      intro j
      have hs := hsumf (heckeRep q j • τ)
      rw [heckeRep_smul_coe hqpos j τ] at hs
      have hs2 := hs.mul_left (1 / q : ℂ)
      rw [← heckeRep_slash_apply hqpos j ⇑f τ] at hs2
      have hfun : (fun n : ℕ => (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n •
          Function.Periodic.qParam 1 (((τ : ℂ) + j) / q) ^ n))
          = fun n : ℕ => (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
              (Function.Periodic.qParam (q : ℝ) ↑τ ^ n *
                Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j)) := by
        funext n
        rw [smul_eq_mul, qParam_shift hq0 j ↑τ, mul_pow]
        congr 2
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
        congr 1
        ring_nf
      rw [hfun] at hs2
      exact hs2
    have h13 := hasSum_sum (fun j (_ : j ∈ Finset.range q) => hj j)
    have hterm : ∀ n : ℕ, (∑ j ∈ Finset.range q,
        (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
          (Function.Periodic.qParam (q : ℝ) ↑τ ^ n *
            Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j)))
        = if q ∣ n then (qExpansion 1 ⇑f).coeff n *
            Function.Periodic.qParam (q : ℝ) ↑τ ^ n else 0 := by
      intro n
      have hfac : ∀ j ∈ Finset.range q,
          (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
            (Function.Periodic.qParam (q : ℝ) ↑τ ^ n *
              Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j))
          = ((1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
              Function.Periodic.qParam (q : ℝ) ↑τ ^ n)) *
              Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j :=
        fun j _ => by ring
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
        heckeRep_char_sum hqpos n]
      by_cases hdvd : q ∣ n
      · rw [if_pos hdvd, if_pos hdvd]
        field_simp
      · rw [if_neg hdvd, if_neg hdvd, mul_zero]
    have h14 : (fun n : ℕ => ∑ j ∈ Finset.range q,
        (1 / q : ℂ) * ((qExpansion 1 ⇑f).coeff n *
          (Function.Periodic.qParam (q : ℝ) ↑τ ^ n *
            Complex.exp (2 * Real.pi * Complex.I * n / q) ^ j)))
        = fun n : ℕ => if q ∣ n then (qExpansion 1 ⇑f).coeff n *
            Function.Periodic.qParam (q : ℝ) ↑τ ^ n else 0 := funext hterm
    rw [h14] at h13
    have h0 : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) →
        (if q ∣ n then (qExpansion 1 ⇑f).coeff n *
          Function.Periodic.qParam (q : ℝ) ↑τ ^ n else 0) = 0 := by
      intro n hn
      rw [if_neg]
      rintro ⟨t, ht⟩
      exact hn ⟨t, ht.symm⟩
    have h15 := (Function.Injective.hasSum_iff hinj h0).mpr h13
    have h16 : ((fun n : ℕ => if q ∣ n then (qExpansion 1 ⇑f).coeff n *
        Function.Periodic.qParam (q : ℝ) ↑τ ^ n else 0) ∘ (fun m : ℕ => q * m))
        = fun n : ℕ => qCoeff N f (q * n) •
            Function.Periodic.qParam 1 ↑τ ^ n := by
      funext n
      simp only [Function.comp_apply]
      rw [if_pos ⟨n, rfl⟩, pow_mul, qParam_nat_pow hq0, smul_eq_mul]
      rfl
    rw [h16] at h15
    -- part 2 and assembly, by cases on `q ∣ N`
    by_cases hqN : q ∣ N
    · have hval : heckeTransform N q ⇑f τ
          = ∑ j ∈ Finset.range q, (⇑f ∣[(2 : ℤ)] heckeRep q j) τ := by
        unfold heckeTransform
        rw [if_pos hqN, add_zero, Finset.sum_apply]
      rw [hval]
      have hcoeff : (fun n : ℕ =>
          (qCoeff N f (q * n) +
            (if q ∣ N then 0 else if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0)) •
            Function.Periodic.qParam 1 ↑τ ^ n)
          = fun n : ℕ => qCoeff N f (q * n) •
              Function.Periodic.qParam 1 ↑τ ^ n := by
        funext n
        rw [if_pos hqN, add_zero]
      rw [hcoeff]
      exact h15
    · -- the extra representative
      have h2 : HasSum (fun n : ℕ =>
          (if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0) •
            Function.Periodic.qParam 1 ↑τ ^ n)
          ((⇑f ∣[(2 : ℤ)] heckeRepInf q) τ) := by
        have hs := hsumf (heckeRepInf q • τ)
        rw [heckeRepInf_smul_coe hqpos τ] at hs
        have hs2 := hs.mul_left (q : ℂ)
        rw [← heckeRepInf_slash_apply hqpos ⇑f τ] at hs2
        have hfun : (fun n : ℕ => (q : ℂ) * ((qExpansion 1 ⇑f).coeff n •
            Function.Periodic.qParam 1 ((q : ℂ) * ↑τ) ^ n))
            = (fun n : ℕ => (if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0) •
                Function.Periodic.qParam 1 ↑τ ^ n) ∘ (fun n : ℕ => q * n) := by
          funext n
          simp only [Function.comp_apply]
          rw [if_pos ⟨n, rfl⟩, Nat.mul_div_cancel_left n hqpos,
            qParam_nat_mul q ↑τ, ← pow_mul, smul_eq_mul, smul_eq_mul]
          simp only [qCoeff]
          ring
        rw [hfun] at hs2
        have h0' : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) →
            ((if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0) •
              Function.Periodic.qParam 1 ↑τ ^ n) = 0 := by
          intro n hn
          rw [if_neg, zero_smul]
          rintro ⟨t, ht⟩
          exact hn ⟨t, ht.symm⟩
        exact (Function.Injective.hasSum_iff hinj h0').mp hs2
      have hval : heckeTransform N q ⇑f τ
          = (∑ j ∈ Finset.range q, (⇑f ∣[(2 : ℤ)] heckeRep q j) τ)
            + (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
        unfold heckeTransform
        rw [if_neg hqN, Pi.add_apply, Finset.sum_apply]
      rw [hval]
      have h17 := h15.add h2
      have hcoeff : (fun n : ℕ =>
          (qCoeff N f (q * n) +
            (if q ∣ N then 0 else if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0)) •
            Function.Periodic.qParam 1 ↑τ ^ n)
          = fun n : ℕ => qCoeff N f (q * n) •
              Function.Periodic.qParam 1 ↑τ ^ n +
            (if q ∣ n then (q : ℂ) * qCoeff N f (n / q) else 0) •
              Function.Periodic.qParam 1 ↑τ ^ n := by
        funext n
        rw [if_neg hqN, add_smul]
      rw [hcoeff]
      exact h17
  -- uniqueness of `q`-expansions through the cusp form of
  -- `exists_cuspForm_heckeTransform`
  obtain ⟨g, hg⟩ := exists_cuspForm_heckeTransform hN hq f
  have huniq := ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0GL N) (f := g)
    (fun τ => by rw [show ⇑g = heckeTransform N q ⇑f from hg]; exact hmaster τ) m
  rw [← hg]
  exact huniq.symm

end HeckeQExpansion

/-- The `q`-expansion coefficients of the zero cusp form vanish. -/
theorem qCoeff_zero_cuspForm (N m : ℕ) :
    qCoeff N (0 : CuspForm (Gamma0GL N) 2) m = 0 := by
  show (qExpansion 1 ⇑(0 : CuspForm (Gamma0GL N) 2)).coeff m = 0
  rw [CuspForm.coe_zero, qExpansion_zero]
  simp

/-- The `m`-th `q`-expansion coefficient as a `ℂ`-linear functional on
`S₂(Γ₀(N))` — additivity and scalar equivariance through the pin's
`qExpansion_add`/`qExpansion_smul`. -/
noncomputable def qCoeffL (N m : ℕ) : CuspForm (Gamma0GL N) 2 →ₗ[ℂ] ℂ where
  toFun f := qCoeff N f m
  map_add' f g := by
    have hfa := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    have hga := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    show (qExpansion 1 ⇑(f + g)).coeff m = _
    rw [CuspForm.coe_add, qExpansion_add hfa hga]
    simp [qCoeff]
  map_smul' c f := by
    have hfa := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
      (one_mem_strictPeriods_Gamma0GL N)
    show (qExpansion 1 ⇑(c • f)).coeff m = _
    rw [CuspForm.IsGLPos.coe_smul, qExpansion_smul hfa]
    simp [qCoeff]

@[simp] theorem qCoeffL_apply (N m : ℕ) (f : CuspForm (Gamma0GL N) 2) :
    qCoeffL N m f = qCoeff N f m := rfl

/-- **`q`-expansion principle** for weight-2 level-`N` cusp forms: the
coefficient system determines the form. Proven from the pin's
`qExpansion_eq_zero_iff` (Taylor-series vanishing at the cusp forces
functional vanishing) applied to the difference. -/
theorem cuspForm_eq_of_forall_qCoeff_eq {N : ℕ}
    {f g : CuspForm (Gamma0GL N) 2} (h : ∀ m, qCoeff N f m = qCoeff N g m) :
    f = g := by
  haveI : Fact (IsCusp OnePoint.infty (Gamma0GL N)) :=
    ⟨(Gamma0GL N).isCusp_of_mem_strictPeriods one_pos
      (one_mem_strictPeriods_Gamma0GL N)⟩
  have hfa := ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (one_mem_strictPeriods_Gamma0GL N)
  have hga := ModularFormClass.analyticAt_cuspFunction_zero g one_pos
    (one_mem_strictPeriods_Gamma0GL N)
  have hsub : qExpansion 1 ⇑(f - g) = 0 := by
    rw [CuspForm.coe_sub, qExpansion_sub hfa hga]
    ext m
    have := h m
    simp only [qCoeff] at this
    simp [this]
  have h0 : ⇑(f - g) = 0 := by
    rw [← qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex (f - g)
        (one_mem_strictPeriods_Gamma0GL N))
      (ModularFormClass.holo (f - g)) (ModularFormClass.bdd_at_infty (f - g))]
    exact hsub
  have hfg : f - g = 0 := DFunLike.coe_injective (by rw [h0, CuspForm.coe_zero])
  exact sub_eq_zero.mp hfg

/-- **THE `q`-EXPANSION OF `heckeOp`** (PROVEN): the bundled operator's
coefficients, rather than the raw slash-sum's.  This is
`qExpansion_heckeTransform_coeff` composed with `heckeOp_coe`, and it is
the form every consumer actually wants — `heckeOp` is what
`Module.End`-valued statements are written against.

`a_m(T_q f) = a_{qm}(f) + 1_{q ∤ N}·1_{q ∣ m}·q·a_{m/q}(f)`. -/
theorem qCoeff_heckeOp {N : ℕ} (hN : 0 < N) {q : ℕ} (hq : q.Prime)
    (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff N (heckeOp N q f) m =
      qCoeff N f (q * m) +
        (if q ∣ N then 0 else if q ∣ m then (q : ℂ) * qCoeff N f (m / q) else 0) := by
  show (qExpansion 1 ⇑(heckeOp N q f)).coeff m = _
  rw [heckeOp_coe hN hq f]
  exact qExpansion_heckeTransform_coeff hN hq f m

end GaloisRepresentation.Modularity
