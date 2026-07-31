/-
Modularity/HeckeAtkinLehner.lean — own work for the Fermat project.

# The Hecke / Petersson / Atkin–Lehner block of `Interface.lean`, hoisted upstream of `X0.lean`

This module exists to BREAK A MODULE CYCLE, and that is its only reason for
existing.  Every declaration below was hoisted VERBATIM out of
`Fermat/FLT/Modularity/Interface.lean` on 2026-07-31; none of it was written
here and none of it was changed in the move.  It is the second such hoist, and
it follows `Fermat/FLT/Modularity/HeckeOperator.lean` exactly (see the
`THE CYCLE IS BROKEN (2026-07-27)` note in `ModularCurve/X0.lean`).

The cycle it breaks:

    Modularity/Interface  →  GaloisRepresentation/HardlyRamified/ModThree
                          →  FreyCurve/MazurTorsion  →  ModularCurve/X0

`ModularCurve/X0.lean` carries `exists_frickeSlash_eq_smul_of_isNewEigenformAt`
(Atkin–Lehner multiplicity one for the Fricke involution) and
`frickeSign_eq_neg_one_of_isNewEigenformAt` as open leaves, and their whole
mathematical content is already PROVEN in `Interface.lean` — which is
DOWNSTREAM of `X0.lean` through the chain above, so `X0.lean` could not use it.

WHAT IS HERE: the transitive closure inside `Interface.lean` of

  * `heckeTransform_slash_atkinLehnerRep` — `T_r (f ∣ W_q) = (T_r f) ∣ W_q` for
    primes `r ≠ q`, the double-coset computation;
  * `heckeOp_comm_atkinLehnerOp` — the same as endomorphisms;
  * `heckeOp_apply_eq_smul_of_isWeightTwoEigenform`;
  * `exists_smul_of_heckeOp_eq_smul_of_not_dvd_level` — strong multiplicity one;
  * `eq_qCoeff_one_smul_of_heckeOp_eigen`, `atkinLehnerOp`, `atkinLehnerOp_coe`,
    `IsWeightTwoNewform`.

That closure is NOT the short Atkin–Lehner shortlist the section headings
suggest: it drags in `qCoeff` and the `q`-expansion of the slash-sum, the
degeneracy operators and the oldform subspace, the Sturm bound and
`cuspForm_finiteDimensional`, the Miyake trace bookkeeping, and — the bulk of
it — the Petersson inner product with its fundamental-domain measure theory
(`exists_peterssonProduct_selfAdjoint_heckeOp`,
`peterssonSelfAdjoint_of_gamma0FundamentalDomain`, `gamma0Domain`, and the
volume lemmas underneath them).  196 declarations, none of them sorried.

## HOW THE MOVE WAS JUSTIFIED

A comment-stripped, `isalnum`-tokenised transitive-closure scan over
`Interface.lean` (CLAUDE.md records why a unicode-range identifier regex is
wrong here: `À-￿` swallows `⟨⟩`, so names inside anonymous constructors are
missed).  The scan showed the closure references NOTHING in `Interface.lean`
outside itself, and in particular nothing from `X0.lean` — `Interface.lean`'s
uses of `X0.lean` are confined to its Eichler–Shimura and Jacobian material
(`IsJacobianOf`, `IsX0Compactification`, `exists_jacobianOf_x0`, …), which the
moved block lies between and touches neither.  The only project module this one
needs is `Fermat.FLT.Modularity.HeckeOperator`.

**Two scan bugs the build caught, recorded because they will recur.**  (i) A
whole-token scan cannot see DOT NOTATION: `hA.gamma0_mul` never contains the
string `IsAtkinLehnerMatrix.gamma0_mul`, so two theorems were missed and the
first build failed on `Invalid field 'gamma0_mul'`.  Index dotted declarations
by last component, but require the PREFIX to appear in the same body too — a
bare suffix match on `.one`/`.mul`/`.prod` dragged in an unrelated power-series
cluster.  (ii) A Lean command continues onto INDENTED following lines, so
`open A B C` with `ConjAct` on the next line is one command; reading only the
first line silently loses `open ConjAct` and the build fails ~12 lines later
on an unknown identifier that looks like a missing import.

## WHAT IS DELIBERATELY NOT REPRODUCED FROM `Interface.lean`

Three kinds of context line in scope at the moved blocks' original positions
name declarations that stay behind, and no moved declaration references any of
them (checked on the comment-stripped source):

* the four `attribute [instance] …Package.addCommGroup` lines;
* the three `local notation "𝔭ᵥ"/"𝒪ᵖᵥ"/"ℚᵖᵥ"` abbreviations;
* the `variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime] {R : Type u} …
  {ρ : GaloisRep ℚ R V}` package for the hardly-ramified representation.

The `variable` one is worth spelling out because it looks load-bearing and is
not.  Lean includes a section variable only where it is REFERENCED, and every
`p`, `hp` and `hv` in the moved text is a binder of its own that shadows it
(`obtain ⟨p, hp, u, …⟩`, `⨆ p ∈ M.primeFactors`, and an explicit
`(hv : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q v = qCoeff M g q • v)`).  So
dropping it is semantically identical here — and reproducing it is not an
option, since it mentions `GaloisRep`, `ℤ_[p]` and `IsModuleTopology`, none of
which this module may import.

## IMPORTS

The Mathlib import list is `Interface.lean`'s, verbatim and in order, with each
entry made `public` (as in `HeckeOperator.lean`).  It is certainly larger than
this module needs; it was not pruned because pruning costs a build cycle per
attempt and an over-wide import list cannot make the move wrong.  Pruning it is
safe follow-on work — do it against a build, not against a scan.

Do not migrate more here without re-running the reference scan: the point of
this module is to be upstream of `X0.lean`, not to become a second
modular-forms file.
-/
module

public import Fermat.FLT.Modularity.HeckeOperator
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.Petersson
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.NumberTheory.Modular
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain
open scoped MatrixGroups

universe u v

/-- The `n`-th `q`-expansion coefficient `aₙ(f)` of a weight-2 level-`N`
cusp form, through the pin's `UpperHalfPlane.qExpansion` at width `1`
(the translation `τ ↦ τ + 1` lies in `Γ₀(N)` for every `N`, so `1` is a
strict period and this is the classical Fourier coefficient at the cusp
`∞`). -/
noncomputable def qCoeff (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

/-- **The eigenform carrier**: `f ∈ S₂(Γ₀(N))` is a *normalized Hecke
eigenform*, stated through the coefficient characterization of
Diamond–Shurman Proposition 5.8.5 (weight 2, trivial character) — the
only spelling of eigenform-ness available on a pin with no Hecke
operators, and the exact one the future Hecke-action construction will
connect to eigenvectors (see the DECOMPOSITION PLAN in the file
docstring, where the soundness of this choice is audited: inhabitants
are precisely the classical normalized full-Hecke eigenforms). -/
structure IsWeightTwoEigenform (N : ℕ) (f : CuspForm (Gamma0GL N) 2) : Prop where
  /-- `a₁ = 1`: the eigenform is normalized. -/
  qCoeff_one : qCoeff N f 1 = 1
  /-- `a_{mn} = a_m a_n` for coprime `m, n`. -/
  qCoeff_mul_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff N f (m * n) = qCoeff N f m * qCoeff N f n
  /-- `a_{q^{r+2}} = a_q · a_{q^{r+1}} − q · a_{q^r}` at good primes
  `q ∤ N` (the weight-2 Hecke recursion, `q^{k−1} = q`). -/
  qCoeff_prime_pow_of_not_dvd : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ r : ℕ,
    qCoeff N f (q ^ (r + 2)) =
      qCoeff N f q * qCoeff N f (q ^ (r + 1)) - q * qCoeff N f (q ^ r)
  /-- `a_{q^{r+1}} = a_q · a_{q^r}` at bad primes `q ∣ N` (the `U_q`
  recursion). -/
  qCoeff_prime_pow_of_dvd : ∀ q : ℕ, q.Prime → q ∣ N → ∀ r : ℕ,
    qCoeff N f (q ^ (r + 1)) = qCoeff N f q * qCoeff N f (q ^ r)

section HeckeFieldFiniteness
open scoped Matrix

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

section HeckeOperator
open UpperHalfPlane ModularForm

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

/-- **The eigenform coefficient identity**: for a normalized weight-2
eigenform, the Hecke-transform coefficient
`a_{qm} + 1_{q ∤ N}·1_{q ∣ m}·q·a_{m/q}` collapses to `a_q·a_m` —
i.e. `T_q f = a_q·f` at the level of coefficient systems. This is the
converse half of Diamond–Shurman Proposition 5.8.5 at weight 2,
proven here from the four `IsWeightTwoEigenform` accessor fields by
splitting `m = q^r·m'` with `q ∤ m'`. -/
theorem hecke_eigen_coeff_identity {N : ℕ} {f : CuspForm (Gamma0GL N) 2}
    (hf : IsWeightTwoEigenform N f) {q : ℕ} (hq : q.Prime) (m : ℕ) :
    qCoeff N f (q * m) +
      (if q ∣ N then 0 else if q ∣ m then (q : ℂ) * qCoeff N f (m / q) else 0) =
      qCoeff N f q * qCoeff N f m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [qCoeff_zero, Nat.zero_div]
  · set r := m.factorization q with hrdef
    set m' := m / q ^ r with hm'def
    have hsplit : q ^ r * m' = m := Nat.ordProj_mul_ordCompl_eq_self m q
    have hqm' : ¬ q ∣ m' := Nat.not_dvd_ordCompl hq hm
    have hcop : ∀ s : ℕ, (q ^ s).Coprime m' :=
      fun s => Nat.Coprime.pow_left s (hq.coprime_iff_not_dvd.mpr hqm')
    by_cases hqN : q ∣ N
    · rw [if_pos hqN, add_zero]
      have h1 : q * m = q ^ (r + 1) * m' := by rw [← hsplit]; ring
      rw [h1, ← hsplit, hf.qCoeff_mul_coprime _ _ (hcop (r + 1)),
        hf.qCoeff_mul_coprime _ _ (hcop r),
        hf.qCoeff_prime_pow_of_dvd q hq hqN r, mul_assoc]
    · rw [if_neg hqN]
      by_cases hqm : q ∣ m
      · have hr1 : 1 ≤ r := hq.factorization_pos_of_dvd hm hqm
        rw [if_pos hqm]
        have e2 : r - 1 + 1 = r := Nat.sub_add_cancel hr1
        have h1 : q * m = q ^ (r + 1) * m' := by rw [← hsplit]; ring
        have h2 : m / q = q ^ (r - 1) * m' := by
          have hm2 : m = q * (q ^ (r - 1) * m') := by
            calc m = q ^ r * m' := hsplit.symm
              _ = q ^ (r - 1 + 1) * m' := by rw [e2]
              _ = q * (q ^ (r - 1) * m') := by rw [pow_succ']; ring
          rw [hm2, Nat.mul_div_cancel_left _ hq.pos]
        rw [h1, h2, ← hsplit, hf.qCoeff_mul_coprime _ _ (hcop (r + 1)),
          hf.qCoeff_mul_coprime _ _ (hcop (r - 1)),
          hf.qCoeff_mul_coprime _ _ (hcop r)]
        have hrec := hf.qCoeff_prime_pow_of_not_dvd q hq hqN (r - 1)
        have e1 : r - 1 + 2 = r + 1 := by omega
        rw [e1, e2] at hrec
        rw [hrec]
        ring
      · rw [if_neg hqm, add_zero,
          hf.qCoeff_mul_coprime q m (hq.coprime_iff_not_dvd.mpr hqm)]

section DegeneracyOperator
open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
  ConjAct
open scoped Pointwise

/-- **The conjugation containment behind `V_d`**: for `α = [d, 0; 0, 1]` and
`d·N ∣ M` one has `Γ₀(M) ≤ α⁻¹ Γ₀(N) α`, i.e. `α Γ₀(M) α⁻¹ ⊆ Γ₀(N)`.

Conjugation by `α` multiplies the upper-right entry by `d` and DIVIDES the
lower-left entry by `d`; so integrality of the conjugate plus its
`Γ₀(N)`-condition is exactly `d·N ∣ c`, which `d·N ∣ M ∣ c` supplies.  This is
the `V_d` analogue of `heckeRep_conj_mem_iff` above, and it is what lets a cusp
form on the conjugate group be RESTRICTED to `Γ₀(M)`. -/
theorem Gamma0GL_le_conj_heckeRepInf {N M d : ℕ} (hd : 0 < d)
    (hdvd : d * N ∣ M) :
    Gamma0GL M ≤ toConjAct (heckeRepInf d)⁻¹ • Gamma0GL N := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  intro x hx
  rw [mem_conjAct_inv_smul_iff]
  obtain ⟨ρ, hρ, rfl⟩ := mem_Gamma0GL_iff.mp hx
  have hcM : (M : ℤ) ∣ ρ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hρ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρ
  have hdN : ((d : ℤ) * N) ∣ ρ 1 0 := dvd_trans (by exact_mod_cast hdvd) hcM
  obtain ⟨t, ht⟩ : (d : ℤ) ∣ ρ 1 0 := dvd_trans (Dvd.intro _ rfl) hdN
  have hNt : (N : ℤ) ∣ t := by
    rcases hdN with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hd0' : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd.ne'
    have hds : (d : ℤ) * t = (d : ℤ) * ((N : ℤ) * s) := by rw [← ht, hs]; ring
    exact mul_left_cancel₀ hd0' hds
  have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have h2 := ρ.2
    rwa [Matrix.det_fin_two] at h2
  refine mem_Gamma0GL_iff.mpr ⟨⟨!![ρ 0 0, (d : ℤ) * ρ 0 1; t, ρ 1 1], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hb : ρ 0 0 * ρ 1 1 - ρ 0 1 * ((d : ℤ) * t) = 1 := by rw [← ht]; exact hdet
    linarith [hb]
  · rw [CongruenceSubgroup.Gamma0_mem]
    show ((t : ℤ) : ZMod N) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNt
  · rw [eq_mul_inv_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp [heckeRepInf_coe hd0, mapGL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply,
          Fin.sum_univ_two, ht]
        try push_cast
        try ring

/-- **Restriction of a cusp form along a subgroup inclusion**: a cusp form for a
LARGER group is one for a smaller.  Slash invariance is demanded at fewer
elements, holomorphy is unchanged, and every cusp of the smaller group is a cusp
of the larger (`IsCusp.mono`), so the vanishing condition transfers. -/
def cuspFormOfLe {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ ≤ Γ')
    (f : CuspForm Γ' k) : CuspForm Γ k where
  toFun := f
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

/-- **`(V_d f)(τ) = f(dτ)` as a function on `ℍ`**: the weight-2 slash by
`heckeRepInf d = [d, 0; 0, 1]`, divided by `d` to cancel the `det^{k−1} = d`
that mathlib's slash normalization contributes. -/
noncomputable def degeneracyTransform (d : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  (d : ℂ)⁻¹ • (f ∣[(2 : ℤ)] heckeRepInf d)

/-- `V_d` is additive (the slash is). -/
theorem degeneracyTransform_add (d : ℕ) (f g : ℍ → ℂ) :
    degeneracyTransform d (f + g) =
      degeneracyTransform d f + degeneracyTransform d g := by
  unfold degeneracyTransform
  rw [SlashAction.add_slash, smul_add]

/-- `V_d` commutes with complex scalars (its representative has positive
determinant, so the slash conjugation factor `σ` is the identity). -/
theorem degeneracyTransform_smul (d : ℕ) (c : ℂ) (f : ℍ → ℂ) :
    degeneracyTransform d (c • f) = c • degeneracyTransform d f := by
  unfold degeneracyTransform
  rw [ModularForm.smul_slash, σ_heckeRepInf, smul_comm]

/-- **`V_d` preserves the cusp space**: `f ∣[2] α` is a cusp form on the
conjugate group `α⁻¹Γ₀(N)α`, which CONTAINS `Γ₀(M)` when `d·N ∣ M`
(`Gamma0GL_le_conj_heckeRepInf`); restrict along that inclusion. -/
theorem exists_cuspForm_degeneracyTransform {N M d : ℕ} (hd : 0 < d)
    (hdvd : d * N ∣ M) (f : CuspForm (Gamma0GL N) 2) :
    ∃ F : CuspForm (Gamma0GL M) 2, ⇑F = degeneracyTransform d ⇑f :=
  ⟨(d : ℂ)⁻¹ • cuspFormOfLe (Gamma0GL_le_conj_heckeRepInf hd hdvd)
    (CuspForm.translate f (heckeRepInf d)), rfl⟩

/-- **The `q`-expansion of `V_d f`**: `a_n(V_d f) = a_{n/d}(f)` when `d ∣ n`, and
`0` otherwise — the coefficients of `f` spread out over the multiples of `d`.
This is the entire arithmetic content of `f ↦ f(dz)`, and it is what makes the
old subspace visible coefficientwise.

Proof: `qParam 1 (dτ) = (qParam 1 τ)^d`, so the `q`-expansion of `f` at `dτ`
reindexes along the injection `n ↦ d·n`; uniqueness of `q`-expansions
(`ModularFormClass.qExpansion_coeff_unique`) then reads off the coefficients. -/
theorem qCoeff_degeneracy {N M d : ℕ} (hd : 0 < d)
    (f : CuspForm (Gamma0GL N) 2) (F : CuspForm (Gamma0GL M) 2)
    (hF : ⇑F = degeneracyTransform d ⇑f) (m : ℕ) :
    qCoeff M F m = if d ∣ m then qCoeff N f (m / d) else 0 := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
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
  have hinj : Function.Injective (fun m : ℕ => d * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hd h
  have hmaster : ∀ τ : ℍ, HasSum
      (fun n : ℕ => (if d ∣ n then qCoeff N f (n / d) else 0) •
        Function.Periodic.qParam 1 ↑τ ^ n) (degeneracyTransform d ⇑f τ) := by
    intro τ
    have hval : degeneracyTransform d ⇑f τ = f (heckeRepInf d • τ) := by
      show (d : ℂ)⁻¹ * (⇑f ∣[(2 : ℤ)] heckeRepInf d) τ = _
      rw [heckeRepInf_slash_apply hd ⇑f τ, ← mul_assoc, inv_mul_cancel₀ hdC,
        one_mul]
    rw [hval]
    have hs := hsumf (heckeRepInf d • τ)
    rw [heckeRepInf_smul_coe hd τ] at hs
    have hfun : (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 ((d : ℂ) * ↑τ) ^ n)
        = (fun n : ℕ => (if d ∣ n then qCoeff N f (n / d) else 0) •
            Function.Periodic.qParam 1 ↑τ ^ n) ∘ (fun n : ℕ => d * n) := by
      funext n
      simp only [Function.comp_apply]
      rw [if_pos ⟨n, rfl⟩, Nat.mul_div_cancel_left n hd,
        qParam_nat_mul d ↑τ, ← pow_mul]
      rfl
    rw [hfun] at hs
    have h0 : ∀ n, n ∉ Set.range (fun m : ℕ => d * m) →
        ((if d ∣ n then qCoeff N f (n / d) else 0) •
          Function.Periodic.qParam 1 ↑τ ^ n) = 0 := by
      intro n hn
      rw [if_neg, zero_smul]
      rintro ⟨t, ht⟩
      exact hn ⟨t, ht.symm⟩
    exact (Function.Injective.hasSum_iff hinj h0).mp hs
  have huniq := ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0GL M) (f := F)
    (fun τ => by rw [hF]; exact hmaster τ) m
  exact huniq.symm

/-- **`V_d` as a bundled `ℂ`-linear map** `S₂(Γ₀(N)) → S₂(Γ₀(M))`, for
`d·N ∣ M`: the degeneracy transform preserves the cusp space, is additive and
`ℂ`-homogeneous, and the underlying function determines the cusp form. -/
theorem exists_degeneracyOpLinear {N M d : ℕ} (hd : 0 < d) (hdvd : d * N ∣ M) :
    ∃ V : CuspForm (Gamma0GL N) 2 →ₗ[ℂ] CuspForm (Gamma0GL M) 2,
      ∀ f : CuspForm (Gamma0GL N) 2, ⇑(V f) = degeneracyTransform d ⇑f := by
  classical
  choose V hV using fun f : CuspForm (Gamma0GL N) 2 =>
    exists_cuspForm_degeneracyTransform hd hdvd f
  refine ⟨{ toFun := V, map_add' := ?_, map_smul' := ?_ }, hV⟩
  · intro f₁ f₂
    apply DFunLike.coe_injective
    simp only [CuspForm.coe_add, hV, degeneracyTransform_add]
  · intro c f
    apply DFunLike.coe_injective
    simp only [RingHom.id_apply, CuspForm.IsGLPos.coe_smul, hV,
      degeneracyTransform_smul]

/-- The unconditional form of `exists_degeneracyOpLinear`, so that `V_d` can be
DEFINED at every triple `(N, M, d)` (junk — the zero map — outside the
meaningful range `0 < d`, `d·N ∣ M`, which is all any statement below
quantifies over).  The COEFFICIENT IDENTITY is bundled into the specification
rather than left as a separate lemma, so that it belongs to the operator by
construction. -/
theorem exists_degeneracyOpLinear_total (N M d : ℕ) :
    ∃ V : CuspForm (Gamma0GL N) 2 →ₗ[ℂ] CuspForm (Gamma0GL M) 2,
      0 < d → d * N ∣ M →
        (∀ f : CuspForm (Gamma0GL N) 2, ⇑(V f) = degeneracyTransform d ⇑f) ∧
        (∀ (f : CuspForm (Gamma0GL N) 2) (m : ℕ),
          qCoeff M (V f) m = if d ∣ m then qCoeff N f (m / d) else 0) := by
  by_cases h : 0 < d ∧ d * N ∣ M
  · obtain ⟨V, hV⟩ := exists_degeneracyOpLinear h.1 h.2
    exact ⟨V, fun _ _ => ⟨hV, fun f m => qCoeff_degeneracy h.1 f (V f) (hV f) m⟩⟩
  · exact ⟨0, fun hd hdvd => absurd ⟨hd, hdvd⟩ h⟩

/-- **The degeneracy operator `V_d : S₂(Γ₀(N)) → S₂(Γ₀(M))`, `f ↦ f(dz)`.**  At
`0 < d` and `d·N ∣ M` it is the bundled `degeneracyTransform d`
(`degeneracyOp_coe`), with coefficients `a_n(V_d f) = a_{n/d}(f)`
(`qCoeff_degeneracyOp`); elsewhere it is junk, which no statement about it looks
at.  The OLD SUBSPACE of `S₂(Γ₀(M))` is `Σ_{p ∣ M} range (V_p)` with `p` prime,
and that is the shape in which the Atkin–Lehner leaves below consume it. -/
noncomputable def degeneracyOp (N M d : ℕ) :
    CuspForm (Gamma0GL N) 2 →ₗ[ℂ] CuspForm (Gamma0GL M) 2 :=
  (exists_degeneracyOpLinear_total N M d).choose

/-- `V_d` acts by the degeneracy transform, i.e. `(V_d f)(τ) = f(dτ)`. -/
theorem degeneracyOp_coe {N M d : ℕ} (hd : 0 < d) (hdvd : d * N ∣ M)
    (f : CuspForm (Gamma0GL N) 2) :
    ⇑(degeneracyOp N M d f) = degeneracyTransform d ⇑f :=
  (((exists_degeneracyOpLinear_total N M d).choose_spec hd hdvd).1) f

/-- **The coefficients of `V_d f`**: `a_n(V_d f) = a_{n/d}(f)` for `d ∣ n`, and
`0` otherwise. -/
theorem qCoeff_degeneracyOp {N M d : ℕ} (hd : 0 < d) (hdvd : d * N ∣ M)
    (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff M (degeneracyOp N M d f) m =
      if d ∣ m then qCoeff N f (m / d) else 0 :=
  (((exists_degeneracyOpLinear_total N M d).choose_spec hd hdvd).2) f m

end DegeneracyOperator

section SturmFiniteness
open scoped Manifold

/-- **Sturm bound for `S₂(Γ₀(N))`** (PROVEN, 2026-07-24): there is a
finite bound `B` — here `2·[SL(2,ℤ):Γ₀(N)]/12 + 1` — such that a
weight-2 level-`N` cusp form whose `q`-expansion coefficients `a_m`
vanish for all `m < B` is zero. General-level analogue of the
classical Sturm bound, proven by the norm-to-level-1 route of
`cuspForm_level_two_coe_eq_zero` made quantitative through the
factorization `norm f = f · (complementary product)` described in the
section header. -/
theorem exists_cuspForm_sturm_bound (N : ℕ) (hN : 0 < N) :
    ∃ B : ℕ, ∀ f : CuspForm (Gamma0GL N) 2,
      (∀ m < B, qCoeff N f m = 0) → f = 0 := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  refine ⟨2 * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ) / 12 + 1, fun f hcoeff => ?_⟩
  suffices hf0 : ⇑f = 0 from DFunLike.coe_injective (by rw [hf0, CuspForm.coe_zero])
  by_contra hf
  refine ModularForm.norm_ne_zero 𝒮ℒ hf ?_
  apply sturm_bound_levelOne
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
    rw [hgdef, ModularForm.prod_slash, habs, one_zpow, one_smul]
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

/-- **Finite dimensionality of `S₂(Γ₀(N))`** (PROVEN, 2026-07-24): the
Sturm bound `exists_cuspForm_sturm_bound` makes the finitely many
coefficient functionals `qCoeffL N 0, …, qCoeffL N (B−1)` jointly
injective, so the weight-2 cusp space embeds `ℂ`-linearly into
`Fin B → ℂ`. This is the content of the Diamond–Shurman ch. 3
dimension theory actually needed downstream, obtained with no
modular-curve geometry. -/
theorem cuspForm_finiteDimensional (N : ℕ) (hN : 0 < N) :
    FiniteDimensional ℂ (CuspForm (Gamma0GL N) 2) := by
  obtain ⟨B, hB⟩ := exists_cuspForm_sturm_bound N hN
  refine FiniteDimensional.of_injective
    (LinearMap.pi (fun i : Fin B => qCoeffL N (i : ℕ)))
    ((injective_iff_map_eq_zero _).mpr fun f hf => ?_)
  refine hB f fun m hm => ?_
  simpa [LinearMap.pi_apply] using congrFun hf ⟨m, hm⟩

end SturmFiniteness

end HeckeOperator

end HeckeFieldFiniteness

section ComplexHeckeAlgebra

/-- Scalar homogeneity of the `q`-expansion coefficients (through the
functional `qCoeffL`). -/
theorem qCoeff_smul {N : ℕ} (c : ℂ) (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff N (c • f) m = c * qCoeff N f m := by
  -- NOT `simpa using …`: `map_smul` is itself a `simp` lemma, so simp normalises
  -- the LHS of `(qCoeffL N m).map_smul c f` to its own RHS and collapses the whole
  -- term to `True`, while the goal — phrased in `qCoeff` rather than `qCoeffL` —
  -- is untouched, so nothing is left to close it with.  Rewrite with the
  -- definitional bridge `qCoeffL_apply` explicitly instead.
  have h := (qCoeffL N m).map_smul c f
  simp only [qCoeffL_apply, RingHom.id_apply, smul_eq_mul] at h
  exact h

/-- **A normalized weight-2 eigenform is an eigenvector of the Hecke
operator** (PROVEN — the eigenform carrier `IsWeightTwoEigenform`,
which on this pin is a COEFFICIENT condition, meets the honest
operator): `T_q g = a_q(g)·g` in `S₂(Γ₀(M))`. Proof: the two sides
have the same `q`-expansion, by `qExpansion_heckeTransform_coeff`
(the coefficients of the slash-sum) followed by
`hecke_eigen_coeff_identity` (the coefficient collapse
`a_{qm} + 1_{q∤M}1_{q∣m}·q·a_{m/q} = a_q·a_m`), and a weight-2 cusp
form is determined by its `q`-expansion
(`cuspForm_eq_of_forall_qCoeff_eq`). -/
theorem heckeOp_apply_eq_smul_of_isWeightTwoEigenform {M : ℕ} (hM : 0 < M)
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoEigenform M g)
    {q : ℕ} (hq : q.Prime) :
    heckeOp M q g = qCoeff M g q • g := by
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  have h1 : qCoeff M (heckeOp M q g) m =
      qCoeff M g (q * m) +
        (if q ∣ M then 0
          else if q ∣ m then (q : ℂ) * qCoeff M g (m / q) else 0) := by
    have h2 := qExpansion_heckeTransform_coeff hM hq g m
    rw [← heckeOp_coe hM hq g] at h2
    exact h2
  rw [h1, hecke_eigen_coeff_identity hg hq m, qCoeff_smul]

/-- A normalized eigenform is nonzero (its first coefficient is `1`). -/
theorem ne_zero_of_isWeightTwoEigenform {M : ℕ}
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoEigenform M g) :
    g ≠ 0 := by
  intro h
  have h1 := hg.qCoeff_one
  rw [h, qCoeff_zero_cuspForm] at h1
  exact zero_ne_one h1

/-- **The `q`-expansion of `T_q f`** for the BUNDLED Hecke operator
(PROVEN — `qExpansion_heckeTransform_coeff` read through `heckeOp_coe`):
`a_m(T_q f) = a_{qm}(f)` at `q ∣ M`, with the extra `q·a_{m/q}(f)` at
`q ∤ M`, `q ∣ m`. This is the form in which the operator's coefficients
are consumed below. -/
theorem qCoeff_heckeOp {M : ℕ} (hM : 0 < M) {q : ℕ} (hq : q.Prime)
    (f : CuspForm (Gamma0GL M) 2) (m : ℕ) :
    qCoeff M (heckeOp M q f) m =
      qCoeff M f (q * m) +
        (if q ∣ M then 0
          else if q ∣ m then (q : ℂ) * qCoeff M f (m / q) else 0) := by
  have h2 := qExpansion_heckeTransform_coeff hM hq f m
  rw [← heckeOp_coe hM hq f] at h2
  exact h2

/-- **The complex Hecke operators COMMUTE** (PROVEN, 2026-07-25 — this
discharges the DECOMPOSITION POINTER that
`exists_heckeOp_newform_etaleIdempotent` recorded): `T_q T_r = T_r T_q`
on `S₂(Γ₀(M))` for all primes `q, r`.

Proof: a `q`-expansion computation — the forms agree coefficientwise
(`cuspForm_eq_of_forall_qCoeff_eq`), each side expanded twice by
`qCoeff_heckeOp`. At `q = r` there is nothing to prove. For `q ≠ r` the
two distinct primes are coprime, which normalizes every divisibility
side condition — `r ∣ qm ↔ r ∣ m`, and `r ∣ m/q ↔ r ∣ m` given `q ∣ m`
— and identifies the indices `qm/r = q(m/r)`, `rm/q = r(m/q)`,
`m/q/r = m/(qr) = m/r/q`. Both iterated formulas then collapse to the
manifestly symmetric

  `a_{qrm} + 1_{r∤M}1_{r∣m}·r·a_{qm/r} + 1_{q∤M}1_{q∣m}·q·a_{rm/q}
     + 1_{q∤M}1_{r∤M}1_{qr∣m}·qr·a_{m/qr}`.

This is what makes `heckeSubalgebra (heckeOp M)` a COMMUTATIVE
subalgebra of `End ℂ S₂(Γ₀(M))`, unlocking the entire pure-algebra half
of the étale-idempotent node below. -/
theorem heckeOp_mul_comm {M : ℕ} (hM : 0 < M) {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) :
    heckeOp M q * heckeOp M r = heckeOp M r * heckeOp M q := by
  rcases eq_or_ne q r with rfl | hne
  · rfl
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hne
  have hcop' : Nat.Coprime r q := hcop.symm
  have hrqx : ∀ x : ℕ, r ∣ q * x ↔ r ∣ x := fun x =>
    ⟨fun h => hcop'.dvd_of_dvd_mul_left h, fun h => h.mul_left q⟩
  have hqrx : ∀ x : ℕ, q ∣ r * x ↔ q ∣ x := fun x =>
    ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left r⟩
  have hdivr : ∀ x : ℕ, q ∣ x → (r ∣ x / q ↔ r ∣ x) := by
    intro x hx
    constructor
    · intro h
      have h2 := h.mul_left q
      rwa [Nat.mul_div_cancel' hx] at h2
    · intro h
      refine hcop'.dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' hx]
  have hdivq : ∀ x : ℕ, r ∣ x → (q ∣ x / r ↔ q ∣ x) := by
    intro x hx
    constructor
    · intro h
      have h2 := h.mul_left r
      rwa [Nat.mul_div_cancel' hx] at h2
    · intro h
      refine hcop.dvd_of_dvd_mul_left ?_
      rwa [Nat.mul_div_cancel' hx]
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply]
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  simp only [qCoeff_heckeOp hM hq, qCoeff_heckeOp hM hr, hrqx, hqrx]
  have hrq : r * q = q * r := Nat.mul_comm r q
  by_cases hqM : q ∣ M
  · by_cases hrM : r ∣ M
    · simp only [hqM, hrM, if_true]
      all_goals ring_nf
    · by_cases hrm : r ∣ m
      · simp only [hqM, hrM, hrm, if_true, if_false,
          Nat.mul_div_assoc q hrm]
        all_goals ring_nf
      · simp only [hqM, hrM, hrm, if_true, if_false]
        all_goals ring_nf
  · by_cases hrM : r ∣ M
    · by_cases hqm : q ∣ m
      · simp only [hqM, hrM, hqm, if_true, if_false,
          Nat.mul_div_assoc r hqm]
        all_goals ring_nf
      · simp only [hqM, hrM, hqm, if_true, if_false]
        all_goals ring_nf
    · by_cases hqm : q ∣ m
      · by_cases hrm : r ∣ m
        · have h1 : r ∣ m / q := (hdivr m hqm).mpr hrm
          have h2 : q ∣ m / r := (hdivq m hrm).mpr hqm
          simp only [hqM, hrM, hqm, hrm, h1, h2, if_true, if_false,
            Nat.mul_div_assoc q hrm, Nat.mul_div_assoc r hqm,
            Nat.div_div_eq_div_mul, hrq]
          all_goals ring_nf
        · have h1 : ¬ r ∣ m / q := fun h => hrm ((hdivr m hqm).mp h)
          simp only [hqM, hrM, hqm, hrm, h1, if_true, if_false,
            Nat.mul_div_assoc r hqm]
          all_goals ring_nf
      · by_cases hrm : r ∣ m
        · have h2 : ¬ q ∣ m / r := fun h => hqm ((hdivq m hrm).mp h)
          simp only [hqM, hrM, hqm, hrm, h2, if_true, if_false,
            Nat.mul_div_assoc q hrm]
          all_goals ring_nf
        · simp only [hqM, hrM, hqm, hrm, if_false]
          all_goals ring_nf

/-- **Multiplicity one for HONEST joint Hecke eigenvectors, at the
coefficient level** (PROVEN 2026-07-26): if `v ∈ S₂(Γ₀(M))` satisfies
`T_q v = a_q(g)·v` at EVERY prime `q` — the bad primes `q ∣ M` included,
where `T_q` is `U_q` — for a normalized weight-2 eigenform `g`, then
`a_m(v) = a_1(v)·a_m(g)` for every `m`.

This is the first of the two classical statements that
`exists_smul_of_heckeOp_generalizedEigen_of_newform` was cut over
(Diamond–Shurman Thm 5.8.2), and the point worth recording is that on
this pin it needs **no Atkin–Lehner theory at all** — no Petersson
product, no oldform/newform decomposition, not even
`eigensystem_minimal`. The reason is that the hypothesis ranges over
ALL primes, `U_q` at `q ∣ M` included, so the coefficients of `v` are
pinned by a bare recursion rather than by a spectral separation
argument.

PROOF: strong induction on `m`, the whole content being that
`qCoeff_heckeOp` and `hecke_eigen_coeff_identity` are the SAME
recursion, one for `v` and one for `g`. At `m = 0` both sides vanish
(`qCoeff_zero`); at `m = 1` the claim is `a_1(v) = a_1(v)·1`
(`hg.qCoeff_one`). For `m ≥ 2` pick any prime `q ∣ m`, write `m = q·m'`,
and read the eigen-equation `T_q v = a_q(g)·v` in the `m'`-th
coefficient:

  `a_{q m'}(v) + 1_{q∤M} 1_{q∣m'}·q·a_{m'/q}(v) = a_q(g)·a_{m'}(v)`,

which is `hecke_eigen_coeff_identity`'s identity with `v` in place of
`g` on the left and `a_q(g)` — NOT `a_q(v)` — on the right. Solving
both for the top index gives `a_m` as the same `ℂ`-linear expression in
`a_{m'}` and `a_{m'/q}` for `v` and for `g`, and `m' < m`,
`m'/q < m`, so the induction hypothesis closes it by `ring`. -/
theorem qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen {M : ℕ} (hM : 0 < M)
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoEigenform M g)
    {v : CuspForm (Gamma0GL M) 2}
    (hv : ∀ q : ℕ, q.Prime → heckeOp M q v = qCoeff M g q • v) :
    ∀ m : ℕ, qCoeff M v m = qCoeff M v 1 * qCoeff M g m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · rw [qCoeff_zero, qCoeff_zero]; ring
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [hg.qCoeff_one]; ring
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m', rfl⟩ := hqm
    have hq2 : 2 ≤ q := hq.two_le
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | h
      · exact absurd (by ring) hm0
      · exact h
    have hm'lt : m' < q * m' := by
      have h2 : 2 * m' ≤ q * m' := Nat.mul_le_mul_right m' hq2
      omega
    have hdivlt : m' / q < q * m' := lt_of_le_of_lt (Nat.div_le_self _ _) hm'lt
    have hvq : qCoeff M (heckeOp M q v) m' = qCoeff M (qCoeff M g q • v) m' := by
      rw [hv q hq]
    rw [qCoeff_heckeOp hM hq v m', qCoeff_smul] at hvq
    have hgq := hecke_eigen_coeff_identity hg hq m'
    have e1 := ih m' hm'lt
    by_cases hqM : q ∣ M
    · rw [if_pos hqM] at hvq hgq
      linear_combination hvq - qCoeff M v 1 * hgq + qCoeff M g q * e1
    · rw [if_neg hqM] at hvq hgq
      by_cases hqmm : q ∣ m'
      · rw [if_pos hqmm] at hvq hgq
        have e2 := ih (m' / q) hdivlt
        linear_combination hvq - qCoeff M v 1 * hgq + qCoeff M g q * e1
          - (q : ℂ) * e2
      · rw [if_neg hqmm] at hvq hgq
        linear_combination hvq - qCoeff M v 1 * hgq + qCoeff M g q * e1

/-- **Multiplicity one for HONEST joint Hecke eigenvectors** (PROVEN
2026-07-26): the joint EIGENSPACE of the complex Hecke operators at a
normalized eigenform `g`'s full prime eigensystem `{a_q(g)}` is exactly
the line `ℂ·g`, and the scalar is read off the first coefficient.
Immediate from `qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen` and
`cuspForm_eq_of_forall_qCoeff_eq`, since a weight-2 cusp form is
determined by its `q`-expansion. -/
theorem eq_qCoeff_one_smul_of_heckeOp_eigen {M : ℕ} (hM : 0 < M)
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoEigenform M g)
    {v : CuspForm (Gamma0GL M) 2}
    (hv : ∀ q : ℕ, q.Prime → heckeOp M q v = qCoeff M g q • v) :
    v = qCoeff M v 1 • g := by
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  rw [qCoeff_smul]
  exact qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen hM hg hv m

/-- **A SELF-ADJOINT OPERATOR FOR A DEFINITE HERMITIAN FORM HAS NO
GENERALIZED EIGENVECTORS BEYOND ITS EIGENVECTORS** (PROVEN 2026-07-26 —
the pure linear algebra behind
`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level`, stated over an
arbitrary `ℂ`-module so that the analytic input enters only through the
form `B`).

`B` is assumed additive and `ℂ`-homogeneous in its FIRST slot,
conjugate-symmetric, and DEFINITE (`B x x = 0 → x = 0`); `T` is assumed
self-adjoint for it. Then `(T − c)ⁿ x = 0` forces `(T − c) x = 0`, for
every complex `c` and every `n`.

WHAT THIS DOES *NOT* NEED, deliberately: no positivity (definiteness
alone), no finite-dimensionality, no spectral theorem, no
`InnerProductSpace` instance — so no norm has to be manufactured on the
carrier and no instance diamond can arise. The argument is the standard
one for a NORMAL operator, unwound by hand:

* conjugate symmetry upgrades slot-one additivity/homogeneity to
  slot-two additivity/conjugate-homogeneity;
* `N = T − c` has adjoint `N' = T − c̄` (both are polynomials in the
  self-adjoint `T`), and `N N' = N' N`;
* hence `B (N x) (N x) = B x (N' N x)` and `B (N' x) (N' x) =
  B x (N N' x)` agree, so `ker N = ker N'` by definiteness;
* if `N (N x) = 0` then `N' (N x) = 0`, so
  `B (N x) (N x) = B x (N' (N x)) = 0` and `N x = 0`;
* induction on `n` reduces `Nⁿ x = 0` to that case. -/
theorem eq_smul_of_pow_sub_smul_apply_eq_zero_of_selfAdjointForm
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {B : V → V → ℂ}
    (hadd : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (a : ℂ) (x y : V), B (a • x) y = a * B x y)
    (hsymm : ∀ x y : V, B y x = starRingEnd ℂ (B x y))
    (hdef : ∀ x : V, B x x = 0 → x = 0)
    {T : Module.End ℂ V} (hT : ∀ x y : V, B (T x) y = B x (T y))
    {c : ℂ} {v : V} {n : ℕ}
    (hv : ((T - c • (1 : Module.End ℂ V)) ^ n) v = 0) :
    T v = c • v := by
  -- Second-slot additivity and conjugate-homogeneity, from conjugate symmetry.
  have hadd₂ : ∀ x y z : V, B x (y + z) = B x y + B x z := by
    intro x y z
    rw [hsymm (y + z) x, hadd y z x, map_add, ← hsymm y x, ← hsymm z x]
  have hsmul₂ : ∀ (a : ℂ) (x y : V), B x (a • y) = starRingEnd ℂ a * B x y := by
    intro a x y
    rw [hsymm (a • y) x, hsmul a y x, map_mul, ← hsymm y x]
  have hzero₂ : ∀ x : V, B x 0 = 0 := by
    intro x
    have h := hsmul₂ 0 x 0
    simpa using h
  have hsub : ∀ x y z : V, B (x - y) z = B x z - B y z := by
    intro x y z
    have h : B (x + (-1 : ℂ) • y) z = B x z + (-1 : ℂ) * B y z := by
      rw [hadd, hsmul]
    simpa [sub_eq_add_neg] using h
  have hsub₂ : ∀ x y z : V, B x (y - z) = B x y - B x z := by
    intro x y z
    have h : B x (y + (-1 : ℂ) • z) = B x y + starRingEnd ℂ (-1 : ℂ) * B x z := by
      rw [hadd₂, hsmul₂]
    simpa [sub_eq_add_neg] using h
  -- The operator `N = T − c` and its adjoint `N' = T − c̄`.
  set N : Module.End ℂ V := T - c • (1 : Module.End ℂ V) with hNdef
  set N' : Module.End ℂ V := T - (starRingEnd ℂ c) • (1 : Module.End ℂ V) with hN'def
  have hNapp : ∀ x : V, N x = T x - c • x := by
    intro x; simp [hNdef]
  have hN'app : ∀ x : V, N' x = T x - (starRingEnd ℂ c) • x := by
    intro x; simp [hN'def]
  have hAdj : ∀ x y : V, B (N x) y = B x (N' y) := by
    intro x y
    rw [hNapp, hN'app, hsub, hsmul, hT, hsub₂, hsmul₂, Complex.conj_conj]
  have hAdj' : ∀ x y : V, B (N' x) y = B x (N y) := by
    intro x y
    rw [hNapp, hN'app, hsub, hsmul, hT, hsub₂, hsmul₂]
  have hcomm : ∀ x : V, N (N' x) = N' (N x) := by
    intro x
    simp only [hNapp, hN'app, map_sub, map_smul, smul_sub, smul_smul]
    module
  -- `N` and its adjoint have the same kernel, and `N` is injective off its kernel.
  have hker : ∀ x : V, N x = 0 → N' x = 0 := by
    intro x hx
    refine hdef _ ?_
    rw [hAdj' x (N' x), hcomm x, hx, map_zero, hzero₂]
  have hsq : ∀ x : V, N (N x) = 0 → N x = 0 := by
    intro x hx
    refine hdef _ ?_
    rw [hAdj x (N x), hker (N x) hx, hzero₂]
  have hpow : ∀ (m : ℕ) (x : V), (N ^ m) x = 0 → N x = 0 := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp only [pow_zero, Module.End.one_apply] at hx
      rw [hx, map_zero]
    | succ k ih =>
      intro x hx
      have h : (N ^ k) (N x) = 0 := by
        rw [pow_succ, Module.End.mul_apply] at hx
        exact hx
      exact hsq x (ih (N x) h)
  have hfin := hpow n v hv
  rw [hNapp] at hfin
  exact sub_eq_zero.mp hfin

section PeterssonProduct
open _root_.MeasureTheory _root_.UpperHalfPlane

/-- **THE INVARIANT MEASURE ON `ℍ` IS OPEN-POSITIVE** (PROVEN 2026-07-26 —
NOT in the pin, and needed by every "a form vanishing a.e. vanishes"
argument): a nonempty open subset of the upper half plane has nonzero
`dx dy / y²`-measure.

Proof: `UpperHalfPlane.coe` is an open embedding (`isOpenEmbedding_coe`), so
the comap of Lebesgue measure on `ℂ` is open-positive
(`Measure.IsOpenPosMeasure.comap`); and `(volume : Measure ℍ)` is that comap
`withDensity (1/y)²` (`UpperHalfPlane.volume_def`), a density that is
everywhere nonzero because `y > 0` on `ℍ`, so the comap is absolutely
continuous with respect to it (`withDensity_absolutelyContinuous'`) and
open-positivity transfers along `≪`.

Deliberately a `theorem` and not an `instance`: it is wanted at exactly one
place (`cuspForm_eq_zero_of_setIntegral_petersson_self_eq_zero` below, via
`haveI`), and registering it globally would put a measure-theoretic instance
into the search path of this 37k-line module for no other consumer. -/
theorem upperHalfPlane_volume_isOpenPosMeasure :
    (volume : Measure ℍ).IsOpenPosMeasure := by
  haveI h1 : ((volume : Measure ℂ).comap UpperHalfPlane.coe).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  rw [UpperHalfPlane.volume_def]
  refine Measure.AbsolutelyContinuous.isOpenPosMeasure
    (μ := (volume : Measure ℂ).comap UpperHalfPlane.coe) ?_
  have hmk : Measurable (fun z : ℍ ↦ (NNReal.mk z.im z.im_pos.le : NNReal)) := by
    rw [← measurable_coe_nnreal_real_iff]
    exact Complex.measurable_im.comp UpperHalfPlane.measurable_coe
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (((measurable_const.div hmk).pow_const 2).coe_nnreal_ennreal).aemeasurable
  · filter_upwards with z
    simp only [ne_eq, ENNReal.coe_eq_zero, one_div]
    intro hcon
    exact absurd (congrArg NNReal.toReal hcon) (by simpa using z.im_pos.ne')

/-- **THE PETERSSON INTEGRAND IS INTEGRABLE OVER ANY FINITE-VOLUME SET**
(PROVEN 2026-07-26): no fundamental-domain property is needed, only that
`volume D < ∞`.  The integrand is continuous
(`UpperHalfPlane.petersson_continuous` on the continuity of a modular form,
`ModularFormClass.continuous`) and GLOBALLY BOUNDED for a cusp form
(`CuspFormClass.petersson_bounded_left`, which needs the arithmeticity
instance on `Gamma0GL M` and hence `0 < M`), and a bounded measurable
function on a finite-measure set is integrable
(`Measure.integrableOn_of_bounded`). -/
theorem peterssonIntegrableOn {M : ℕ} (hM : 0 < M) {D : Set ℍ}
    (hD : volume D ≠ ⊤) (f g : CuspForm (Gamma0GL M) 2) :
    IntegrableOn (petersson (2 : ℤ) ⇑g ⇑f) D volume := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (2 : ℤ) (Gamma0GL M) g f
  refine Measure.integrableOn_of_bounded hD ?_ (M := C) ?_
  · exact (UpperHalfPlane.petersson_continuous (2 : ℤ) (ModularFormClass.continuous g)
      (ModularFormClass.continuous f)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun τ => hC τ

/-- The diagonal Petersson integrand is a NONNEGATIVE REAL:
`petersson 2 f f τ = |f τ|² · y²`.  This is what turns definiteness into a
statement about a real integral of a nonnegative function. -/
theorem petersson_self_eq_ofReal {M : ℕ} (f : CuspForm (Gamma0GL M) 2) (τ : ℍ) :
    petersson (2 : ℤ) ⇑f ⇑f τ = ((Complex.normSq (f τ) * τ.im ^ (2 : ℤ) : ℝ) : ℂ) := by
  simp only [petersson, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_zpow]

/-- **DEFINITENESS OF THE PETERSSON PRODUCT, PROVEN — and it needs only that
the domain has INTERIOR** (2026-07-26).  If `∫_D petersson 2 f f = 0` and
`D` contains a nonempty open `U`, then `f = 0`.

This is the observation that removes definiteness from the analytic leaf
entirely, and it is worth stating why it is cheap.  The integrand is
`|f τ|²y² ≥ 0`, so a vanishing integral forces it to vanish ALMOST
EVERYWHERE on `D` (`setIntegral_eq_zero_iff_of_nonneg_ae`, using
`peterssonIntegrableOn`).  Restricting to `U` and using that `volume` is
open-positive on `ℍ` (`upperHalfPlane_volume_isOpenPosMeasure` above) plus
continuity of `f`, the a.e. statement upgrades to `f = 0` ON `U`
(`Measure.eqOn_open_of_ae_eq`).  A holomorphic function on `ℍ` vanishing on
a nonempty open set vanishes identically — `ℍ` is connected, which is
packaged as `UpperHalfPlane.eq_zero_of_frequently`.

So NO positivity of the Petersson product, NO fundamental-domain property
and NO finite-dimensionality is used: an open subset of the domain suffices.
(`hM` is consumed only through `peterssonIntegrableOn`.) -/
theorem cuspForm_eq_zero_of_setIntegral_petersson_self_eq_zero {M : ℕ} (hM : 0 < M)
    {D : Set ℍ} (hDvol : volume D ≠ ⊤) {U : Set ℍ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (hUD : U ⊆ D) {f : CuspForm (Gamma0GL M) 2}
    (h : (∫ τ in D, petersson (2 : ℤ) ⇑f ⇑f τ) = 0) : f = 0 := by
  haveI := upperHalfPlane_volume_isOpenPosMeasure
  set F : ℍ → ℝ := fun τ => Complex.normSq (f τ) * τ.im ^ (2 : ℤ) with hFdef
  have hpt : ∀ τ : ℍ, petersson (2 : ℤ) ⇑f ⇑f τ = ((F τ : ℝ) : ℂ) :=
    petersson_self_eq_ofReal f
  have hfun : petersson (2 : ℤ) ⇑f ⇑f = fun τ : ℍ => ((F τ : ℝ) : ℂ) := funext hpt
  have hintC : IntegrableOn (fun τ : ℍ => ((F τ : ℝ) : ℂ)) D volume := by
    have h1 := peterssonIntegrableOn hM hDvol f f
    rwa [hfun] at h1
  have hintF : IntegrableOn F D volume := by
    show Integrable F (volume.restrict D)
    simpa using hintC.re
  have h0 : (∫ τ in D, F τ) = 0 := by
    rw [hfun, integral_complex_ofReal] at h
    exact_mod_cast h
  have hnn : (0 : ℍ → ℝ) ≤ᵐ[volume.restrict D] F := by
    filter_upwards with τ
    have h1 : (0 : ℝ) < τ.im ^ (2 : ℤ) := by positivity
    exact mul_nonneg (Complex.normSq_nonneg _) h1.le
  have hae : F =ᵐ[volume.restrict D] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae hnn hintF).mp h0
  have haef : (⇑f : ℍ → ℂ) =ᵐ[volume.restrict D] 0 := by
    filter_upwards [hae] with τ hτ
    have him : (τ.im : ℝ) ^ (2 : ℤ) ≠ 0 := by positivity
    have hns : Complex.normSq (f τ) = 0 := by
      have h1 := hτ
      simp only [hFdef, Pi.zero_apply] at h1
      exact (mul_eq_zero.mp h1).resolve_right him
    simpa [Complex.normSq_eq_zero] using hns
  have haeU : (⇑f : ℍ → ℂ) =ᵐ[volume.restrict U] 0 :=
    ae_mono (Measure.restrict_mono hUD le_rfl) haef
  have heq : Set.EqOn (⇑f : ℍ → ℂ) 0 U :=
    Measure.eqOn_open_of_ae_eq haeU hUo
      (ModularFormClass.continuous f).continuousOn continuousOn_const
  obtain ⟨τ₀, hτ₀⟩ := hUne
  have hfreq : ∃ᶠ z in nhdsWithin τ₀ {τ₀}ᶜ, (⇑f : ℍ → ℂ) z = 0 := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds (hUo.mem_nhds hτ₀)] with z hz
    exact heq hz
  have hzero : (⇑f : ℍ → ℂ) = 0 :=
    UpperHalfPlane.eq_zero_of_frequently (ModularFormClass.holo f) hfreq
  exact DFunLike.coe_injective (by simpa using hzero)

section Gamma0FundamentalDomain
open scoped Pointwise NNReal ENNReal

/-- **THE MODULAR DOMAIN SITS IN A VERTICAL STRIP** (PROVEN 2026-07-26):
`𝒟 = {z : 1 ≤ |z|, |re z| ≤ 1/2}` is contained in `{|x| ≤ 1/2, y ≥ 1/2}`,
because `|z| ≥ 1` together with `re z ² ≤ 1/4` forces `im z ² ≥ 3/4 > 1/4`.
(The sharp bound is `y ≥ √3/2`, which is what
`ModularGroup.three_le_four_mul_im_sq_of_mem_fd` records; `1/2` is all the
volume estimate needs and it avoids carrying a square root.)

The strip is written as a PREIMAGE under `Complex.measurableEquivRealProd`
rather than as a set-builder, because that is the shape in which
`Complex.volume_preserving_equiv_real_prod` transports the integral to
`ℝ × ℝ`, where Tonelli applies. -/
theorem coe_modularFd_subset_strip :
    ((↑) '' (ModularGroup.fd) : Set ℂ) ⊆
      Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Ici (1/2 : ℝ)) := by
  rw [ModularGroup.coe_fd]
  rintro z ⟨him, hnorm, hre⟩
  have hre' := abs_le.mp hre
  have hns' : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnorm2 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hre2 : z.re ^ 2 ≤ 1 / 4 := by nlinarith [hre'.1, hre'.2]
  have him2 : (1 / 2 : ℝ) ≤ z.im := by nlinarith [him]
  exact ⟨Set.mem_Icc.mpr hre', him2⟩

/-- **`∫_{1/2}^∞ dy/y² < ∞`** (PROVEN 2026-07-26), in the `ℝ≥0∞` form in
which `UpperHalfPlane.volume_eq_lintegral` presents the invariant density.
Obtained from `integrableOn_Ioi_rpow_of_lt` at the exponent `-2 < -1` on
`(1/4, ∞) ⊇ [1/2, ∞)`, whose `HasFiniteIntegral` field IS this
`lintegral < ⊤` once `‖y ^ (-2 : ℝ)‖ₑ` is identified with `(1/‖y‖₊)²`. -/
theorem lintegral_Ici_inv_sq_lt_top :
    (∫⁻ y : ℝ in Set.Ici (1/2 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞)) < ⊤ := by
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Set.Ioi (1/4 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hfin : (∫⁻ y : ℝ in Set.Ioi (1/4 : ℝ), ‖y ^ (-2 : ℝ)‖ₑ) < ⊤ := hint.2
  have hsub : Set.Ici (1/2 : ℝ) ⊆ Set.Ioi (1/4 : ℝ) := fun y hy =>
    lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)
  have hcongr : (∫⁻ y : ℝ in Set.Ioi (1/4 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞))
      = ∫⁻ y : ℝ in Set.Ioi (1/4 : ℝ), ‖y ^ (-2 : ℝ)‖ₑ := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans (by norm_num) hy
    have h1 : y ^ (-2 : ℝ) = (y ^ (2 : ℕ))⁻¹ := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hy0.le,
        Real.rpow_natCast]
    rw [h1, enorm_eq_nnnorm]
    congr 1
    rw [nnnorm_inv, nnnorm_pow, one_div, inv_pow]
  calc (∫⁻ y : ℝ in Set.Ici (1/2 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞))
      ≤ ∫⁻ y : ℝ in Set.Ioi (1/4 : ℝ), (((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y : ℝ in Set.Ioi (1/4 : ℝ), ‖y ^ (-2 : ℝ)‖ₑ := hcongr
    _ < ⊤ := hfin

/-- **THE STRIP HAS FINITE INVARIANT VOLUME** (PROVEN 2026-07-26): the
hyperbolic area `∫∫ dx dy / y²` of `{|x| ≤ 1/2, y ≥ 1/2}` is finite.

Transport to `ℝ × ℝ` by `Complex.volume_preserving_equiv_real_prod`, apply
Tonelli (`setLIntegral_prod`), and the `x`-integral is a constant over an
interval of length `1` while the `y`-integral is
`lintegral_Ici_inv_sq_lt_top`. -/
theorem lintegral_strip_lt_top :
    (∫⁻ z : ℂ in Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Ici (1/2 : ℝ)),
      (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞)) < ⊤ := by
  have hmeas : Measurable (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : NNReal) : ℝ≥0∞)) := by
    fun_prop
  have key : (∫⁻ z : ℂ in Complex.measurableEquivRealProd ⁻¹'
        (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Ici (1/2 : ℝ)),
        (((1 / ‖z.im‖₊) ^ 2 : NNReal) : ℝ≥0∞))
      = ∫⁻ p : ℝ × ℝ in (Set.Icc (-(1/2) : ℝ) (1/2) ×ˢ Set.Ici (1/2 : ℝ)),
          (((1 / ‖p.2‖₊) ^ 2 : NNReal) : ℝ≥0∞) :=
    Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : NNReal) : ℝ≥0∞)) _
  rw [key, Measure.volume_eq_prod, setLIntegral_prod _ hmeas.aemeasurable]
  dsimp only
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top lintegral_Ici_inv_sq_lt_top (by simp)

/-- **THE STANDARD MODULAR DOMAIN HAS FINITE HYPERBOLIC AREA**
(PROVEN 2026-07-26 — the fact the pin does NOT have, and the reason no
`Γ₀(M)`-domain of finite volume could previously be exhibited):
`volume 𝒟 ≠ ⊤` for the invariant measure `dx dy / y²` on `ℍ`.

`UpperHalfPlane.volume_eq_lintegral` turns `volume 𝒟` into a Lebesgue
integral of the density over `(↑) '' 𝒟 ⊆ ℂ`; `coe_modularFd_subset_strip`
puts that inside the strip and `lintegral_strip_lt_top` bounds it.  (The
true value is `π/3`; only finiteness is used anywhere below.) -/
theorem volume_modularFd_ne_top : volume (ModularGroup.fd) ≠ ⊤ := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact (lt_of_le_of_lt (lintegral_mono_set coe_modularFd_subset_strip)
    lintegral_strip_lt_top).ne

open scoped Classical in
/-- Chosen representatives for the LEFT cosets `SL(2,ℤ) ⧸ Γ₀(M)`, normalised so
that the trivial coset is represented by `1` (which is what puts `𝒟` itself,
hence an open set, inside `gamma0Domain M`).  `Quotient.out` alone would not:
its representative of the trivial coset is an arbitrary element of `Γ₀(M)`. -/
noncomputable def gamma0Rep (M : ℕ) (c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) :
    SL(2, ℤ) :=
  if c = QuotientGroup.mk 1 then 1 else Quotient.out c

/-- `gamma0Rep M c` really does represent the coset `c`. -/
theorem gamma0Rep_spec (M : ℕ) (c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) :
    (QuotientGroup.mk (gamma0Rep M c) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) = c := by
  classical
  rw [gamma0Rep]
  split_ifs with h
  · exact h.symm
  · exact Quotient.out_eq c

/-- The trivial coset is represented by `1`. -/
theorem gamma0Rep_one (M : ℕ) :
    gamma0Rep M (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) = 1 := by
  classical
  rw [gamma0Rep, if_pos rfl]

/-- **THE `Γ₀(M)` FUNDAMENTAL DOMAIN**: `⋃_c γ_c⁻¹ 𝒟`, over the (finitely
many) left cosets `c = γ_c Γ₀(M)` of `Γ₀(M)` in `SL(2,ℤ)`.

The inverses are what makes the covering property come out on the correct
side: if `g • τ ∈ 𝒟` and `g = γ_c h` with `h ∈ Γ₀(M)`, then
`h • τ = γ_c⁻¹ • (g • τ) ∈ γ_c⁻¹ 𝒟`, so it is `Γ₀(M)` — not `SL(2,ℤ)` —
that moves an arbitrary `τ` into this set. -/
noncomputable def gamma0Domain (M : ℕ) : Set ℍ :=
  ⋃ c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M, (gamma0Rep M c)⁻¹ • (ModularGroup.fd)

/-- The invariant measure is `SL(2,ℤ)`-invariant, the action being the
restriction along `Matrix.SpecialLinearGroup.mapGL` of the `GL(2,ℝ)` action for
which the pin registers `SMulInvariantMeasure`. -/
theorem volume_smul_specialLinearGroup (g : SL(2, ℤ)) (s : Set ℍ) :
    volume (g • s) = volume s := by
  have h : g • s = (Matrix.SpecialLinearGroup.mapGL ℝ g) • s := rfl
  rw [h]
  exact measure_smul volume _ s

/-- **THE `Γ₀(M)` DOMAIN HAS FINITE VOLUME** (PROVEN 2026-07-26): a finite
union — `[SL(2,ℤ) : Γ₀(M)] < ∞` by `CongruenceSubgroup.instFiniteIndexGamma0` —
of isometric copies of `𝒟`, each of finite volume by
`volume_modularFd_ne_top`. -/
theorem volume_gamma0Domain_ne_top (M : ℕ) [NeZero M] :
    volume (gamma0Domain M) ≠ ⊤ := by
  have hle : volume (gamma0Domain M)
      ≤ ∑' c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M,
          volume ((gamma0Rep M c)⁻¹ • (ModularGroup.fd)) := measure_iUnion_le _
  classical
  letI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M)
  refine ne_of_lt (lt_of_le_of_lt hle ?_)
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr (fun c _ => ?_)
  rw [volume_smul_specialLinearGroup]
  exact volume_modularFd_ne_top.lt_top

/-- **THE `Γ₀(M)` DOMAIN IS MEASURABLE** (PROVEN 2026-07-27): a FINITE union
(`[SL(2,ℤ) : Γ₀(M)] < ∞`) of images of the CLOSED set `𝒟`
(`ModularGroup.isClosed_fd`) under the measurable embeddings `τ ↦ γ • τ`
(`measurableEmbedding_const_smul`).

This is what `setIntegral_heckeRep_unfold` below consumes as its `hDmeas`
hypothesis; see the MEASURABILITY AUDIT there for why that hypothesis is
genuinely needed rather than cosmetic. -/
theorem measurableSet_gamma0Domain (M : ℕ) [NeZero M] :
    MeasurableSet (gamma0Domain M) := by
  classical
  refine MeasurableSet.iUnion (fun c => ?_)
  have h : ((gamma0Rep M c)⁻¹ • (ModularGroup.fd) : Set ℍ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((gamma0Rep M c)⁻¹)) • (ModularGroup.fd) := rfl
  rw [h, ← Set.image_smul]
  exact (measurableEmbedding_const_smul _).measurableSet_image.mpr
    ModularGroup.isClosed_fd.measurableSet

/-- `𝒟 ⊆ gamma0Domain M` — the trivial coset contributes `1⁻¹ 𝒟 = 𝒟`.  This is
exactly what `gamma0Rep`'s normalisation at the trivial coset buys. -/
theorem modularFd_subset_gamma0Domain (M : ℕ) :
    (ModularGroup.fd) ⊆ gamma0Domain M := by
  refine le_trans (le_of_eq ?_)
    (Set.subset_iUnion _ (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M))
  rw [gamma0Rep_one, inv_one, one_smul]

/-- **THE `Γ₀(M)` DOMAIN HAS INTERIOR** (PROVEN 2026-07-26): it contains the
open modular domain `𝒟ᵒ`, which is nonempty (`2i ∈ 𝒟ᵒ`). -/
theorem exists_open_subset_gamma0Domain (M : ℕ) :
    ∃ U : Set ℍ, IsOpen U ∧ U.Nonempty ∧ U ⊆ gamma0Domain M := by
  have hz : (⟨2 * Complex.I, by norm_num⟩ : ℍ) ∈ ModularGroup.fdo := by
    constructor <;> norm_num [Complex.normSq_apply, UpperHalfPlane.re]
  exact ⟨ModularGroup.fdo, ModularGroup.isOpen_fdo, ⟨_, hz⟩,
    le_trans ModularGroup.fdo_subset_fd (modularFd_subset_gamma0Domain M)⟩

/-- **THE `Γ₀(M)` DOMAIN COVERS `ℍ` UNDER `Γ₀(M)`** (PROVEN 2026-07-26): every
`τ ∈ ℍ` is moved into `gamma0Domain M` by an element of `Gamma0GL M`.

`ModularGroup.exists_smul_mem_fd` supplies `g ∈ SL(2,ℤ)` with `g • τ ∈ 𝒟`;
writing `c` for its coset and `h = γ_c⁻¹ g ∈ Γ₀(M)` (which is exactly
`QuotientGroup.eq` for `gamma0Rep_spec`), `h • τ = γ_c⁻¹ • (g • τ)` lands in
the `c`-th piece.  The `Gamma0GL` element is the `mapGL` image of `h`, and the
two actions agree definitionally since the `SL` action is `compHom` along
`mapGL`. -/
theorem exists_mem_gamma0Domain (M : ℕ) (τ : ℍ) :
    ∃ γ ∈ Gamma0GL M, γ • τ ∈ gamma0Domain M := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  set c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M := QuotientGroup.mk g with hc
  have hout : (QuotientGroup.mk (gamma0Rep M c) :
      SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) = c := gamma0Rep_spec M c
  have hmem : (gamma0Rep M c)⁻¹ * g ∈ CongruenceSubgroup.Gamma0 M := by
    rw [← QuotientGroup.eq, hout, hc]
  refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ ((gamma0Rep M c)⁻¹ * g), ⟨_, hmem, rfl⟩, ?_⟩
  have hact : (Matrix.SpecialLinearGroup.mapGL ℝ ((gamma0Rep M c)⁻¹ * g)) • τ
      = ((gamma0Rep M c)⁻¹ * g) • τ := rfl
  rw [hact, mul_smul]
  exact Set.mem_iUnion.mpr ⟨c, Set.smul_mem_smul_set hg⟩

/-- **A VERTICAL LINE IN `ℂ` IS LEBESGUE-NULL** (PROVEN 2026-07-27):
`volume {z : ℂ | z.re = c} = 0`.

Transport by `Complex.volume_preserving_equiv_real_prod` — the same route
`lintegral_strip_lt_top` above takes — turns the line into `{c} ×ˢ univ` in
`ℝ × ℝ`, whose product measure is `0 * ⊤ = 0`.  (`Measure.addHaar_submodule`
applied to `LinearMap.ker Complex.reLm`, plus a translation, is an equally
short alternative; the transport route is used here because the
`measurableEquivRealProd` machinery is already in scope.) -/
theorem volume_complex_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c}
      = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- **THE BOUNDARY OF THE MODULAR DOMAIN IS NULL** (PROVEN 2026-07-27 — this
was recorded as "THE ONE MISSING FACT" of the a.e.-disjointness leaf below, and
it is the only measure-theoretic input that leaf needs):
`volume (𝒟 \ 𝒟ᵒ) = 0` for the invariant measure `dx dy / y²` on `ℍ`.

`𝒟 = {1 ≤ normSq z, |re z| ≤ 1/2}` and `𝒟ᵒ` is the same with both
inequalities strict, so a point of `𝒟 \ 𝒟ᵒ` has `normSq z = 1` or
`|re z| = 1/2` — i.e. its image in `ℂ` lies on the unit circle or on one of the
two vertical lines `re = ±1/2`.  The circle is null by
`Measure.addHaar_sphere` and the lines by `volume_complex_re_eq_zero`, and
`UpperHalfPlane.volume_eq_lintegral` (the same bridge
`volume_modularFd_ne_top` uses) turns a null image in `ℂ` into a null set in
`ℍ` through `setLIntegral_measure_zero`: the density `1/y²` is irrelevant once
the underlying planar set is null. -/
theorem volume_modularFd_sdiff_fdo_eq_zero :
    volume (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  refine setLIntegral_measure_zero _ _ ?_
  have hsub : ((↑) '' (ModularGroup.fd \ ModularGroup.fdo) : Set ℂ) ⊆
      Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1/2} ∪ {z : ℂ | z.re = -(1/2)}) := by
    rintro _ ⟨z, ⟨hz, hzo⟩, rfl⟩
    obtain ⟨hz1, hz2⟩ := hz
    rw [ModularGroup.fdo, Set.mem_setOf_eq, not_and_or, not_lt, not_lt] at hzo
    rcases hzo with hno | hre
    · left
      have hns : Complex.normSq (z : ℂ) = 1 := le_antisymm hno hz1
      have h2 : ‖(z : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hns
      have hnorm : ‖(z : ℂ)‖ = 1 := by nlinarith [norm_nonneg ((z : ℂ))]
      simpa [Metric.mem_sphere] using hnorm
    · right
      have habs : |(z : ℂ).re| = 1/2 := le_antisymm hz2 hre
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp habs with h | h
      · exact Or.inl h
      · exact Or.inr h
  refine measure_mono_null hsub ?_
  rw [measure_union_null_iff, measure_union_null_iff]
  exact ⟨Measure.addHaar_sphere volume _ _, volume_complex_re_eq_zero _,
    volume_complex_re_eq_zero _⟩

/-- `x ∈ g⁻¹ • s ↔ g • x ∈ s` for the `SL(2,ℤ)`-action on `ℍ`, in the exact
shape the coset bookkeeping below consumes. -/
theorem mem_inv_smul_set_upperHalfPlane_iff (g : SL(2, ℤ)) (s : Set ℍ) (x : ℍ) :
    x ∈ g⁻¹ • s ↔ g • x ∈ s := by
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨g • x, hx, by simp⟩

/-- **A.E.-DISJOINTNESS OF THE `Γ₀(M)` DOMAIN** (PROVEN 2026-07-27 — cut 2026-07-26
out of `exists_peterssonDomain` below, together with
`peterssonSelfAdjoint_of_gamma0FundamentalDomain`): distinct `Γ₀(M)`-translates
of `gamma0Domain M` meet in a null set, once the two elements acting trivially
on `ℍ` are excluded.

WHY `±1` MUST BE EXCLUDED, and why this is not
`MeasureTheory.IsFundamentalDomain`.  `Gamma0GL M` contains `-1` (the image of
`-I ∈ Γ₀(M) ⊆ SL(2,ℤ)`), which acts TRIVIALLY on `ℍ`.  So
`IsFundamentalDomain (Gamma0GL M) D volume` is FALSE for every `D` of positive
measure: its `aedisjoint` field would demand `AEDisjoint volume ((-1) • D) D`,
i.e. `volume D = 0`.  A fundamental domain here exists only for the quotient by
`±1`, and the pin has no action of that quotient on `ℍ` — hence this
hand-rolled conjunct.  (Checked against this pin: `IsFundamentalDomain` occurs
nowhere in `Mathlib/NumberTheory`, and no subset of `ℍ` is registered as one.)
Note `±1` are the ONLY trivially-acting elements: the kernel of the `SL(2,ℝ)`
action on `ℍ` is `{±I}`, so nothing else has to be excluded and the statement
is not weakened by the exclusion.

PROOF PLAN (the mathematics is settled; what is missing is one measure fact).
Let `h ∈ Γ₀(M)`, `h ≠ ±1`, and suppose `z ∈ (h • D) ∩ D` with
`D = ⋃_c γ_c⁻¹ 𝒟`.  Then `z ∈ γ_{c'}⁻¹ 𝒟` and `h⁻¹ z ∈ γ_c⁻¹ 𝒟` for some
cosets `c, c'`.  Put `w = γ_{c'} z ∈ 𝒟` and `g = γ_c h⁻¹ γ_{c'}⁻¹ ∈ SL(2,ℤ)`,
so that `g • w ∈ 𝒟`.  If `w ∈ 𝒟ᵒ` then
`ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd` forces `g = ±1`; since
`-1 ∈ Γ₀(M)`, `g = ±1` gives `γ_c Γ₀(M) = γ_{c'} Γ₀(M)`, i.e. `c = c'`, and
then `γ_c h⁻¹ γ_c⁻¹ = ±1`, i.e. `h = ±1` — excluded.  So the intersection is
contained in `⋃_{c'} γ_{c'}⁻¹ (𝒟 \ 𝒟ᵒ)`, a finite union of translates of the
BOUNDARY of `𝒟`.

THE ONE MISSING FACT was `volume (𝒟 \ 𝒟ᵒ) = 0` — the boundary of the modular
domain is null — and it is now PROVEN just above as
`volume_modularFd_sdiff_fdo_eq_zero`: the boundary is contained in the union of
the vertical lines `re z = ±1/2` and the unit circle `|z| = 1`, each null for
planar Lebesgue measure, and `UpperHalfPlane.volume_eq_lintegral` moves that to
`volume` on `ℍ`.  With it the leaf closes, and the proof below is exactly the
plan above.

ON THE `±1` BOOKKEEPING, which is the one place care is needed.  `ε = ±1` is
CENTRAL in `SL(2,ℤ)` (`Matrix.SpecialLinearGroup.instHasDistribNeg` gives
`(-1) * x = -x = x * (-1)`) and lies in `Γ₀(M)` (`-I` has lower-left entry `0`).
Both facts are used twice: to turn `γ_c h⁻¹ γ_{c'}⁻¹ = ε` into
`γ_{c'}⁻¹ γ_c = h ε ∈ Γ₀(M)`, hence `c = c'` by `QuotientGroup.eq`; and then to
collapse `γ_c h⁻¹ γ_c⁻¹ = ε` to `h⁻¹ = ε`, i.e. `h = ε ∈ {1, -1}` — the excluded
case.  Handling `ε = 1` and `ε = -1` uniformly through those three properties
(`ε ∈ Γ₀(M)`, centrality, `ε² = 1`) is what keeps the two branches from
duplicating. -/
theorem volume_smul_inter_gamma0Domain_eq_zero {M : ℕ} (hM : 0 < M)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL M) (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    volume ((γ • gamma0Domain M) ∩ gamma0Domain M) = 0 := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Countable (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) := Finite.to_countable
  have hmapneg : Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) = (-1 : GL (Fin 2) ℝ) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have hnegmem : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [Matrix.SpecialLinearGroup.coe_neg]
  obtain ⟨h, hhmem, rfl⟩ := hγ
  have hh1 : h ≠ 1 := fun he => h1 (by rw [he, map_one])
  have hh2 : h ≠ -1 := fun he => h2 (by rw [he, hmapneg])
  have hsub : ((Matrix.SpecialLinearGroup.mapGL ℝ h) • gamma0Domain M) ∩ gamma0Domain M
      ⊆ ⋃ c : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M,
          (gamma0Rep M c)⁻¹ • (ModularGroup.fd \ ModularGroup.fdo) := by
    rintro z ⟨hzL, hzR⟩
    obtain ⟨c', hzc'⟩ := Set.mem_iUnion.mp hzR
    have hw : (gamma0Rep M c') • z ∈ ModularGroup.fd :=
      (mem_inv_smul_set_upperHalfPlane_iff _ _ _).mp hzc'
    refine Set.mem_iUnion.mpr
      ⟨c', (mem_inv_smul_set_upperHalfPlane_iff _ _ _).mpr ⟨hw, ?_⟩⟩
    intro hwo
    have hzL' : (Matrix.SpecialLinearGroup.mapGL ℝ h)⁻¹ • z ∈ gamma0Domain M :=
      Set.mem_smul_set_iff_inv_smul_mem.mp hzL
    obtain ⟨c, hzc⟩ := Set.mem_iUnion.mp hzL'
    have hv : (gamma0Rep M c) • ((Matrix.SpecialLinearGroup.mapGL ℝ h)⁻¹ • z)
        ∈ ModularGroup.fd := (mem_inv_smul_set_upperHalfPlane_iff _ _ _).mp hzc
    have hgw : (gamma0Rep M c * h⁻¹ * (gamma0Rep M c')⁻¹) • ((gamma0Rep M c') • z)
        ∈ ModularGroup.fd := by
      have hrw : (gamma0Rep M c * h⁻¹ * (gamma0Rep M c')⁻¹) • ((gamma0Rep M c') • z)
          = (gamma0Rep M c) • (h⁻¹ • z) := by
        rw [mul_smul, mul_smul, inv_smul_smul]
      rw [hrw]
      have hact : (h⁻¹ : SL(2, ℤ)) • z = (Matrix.SpecialLinearGroup.mapGL ℝ h)⁻¹ • z := by
        rw [← map_inv]; rfl
      rw [hact]; exact hv
    obtain ⟨ε, hεne, hεmem, hεcent, hεsq, hεinv, hgeq⟩ :
        ∃ ε : SL(2, ℤ), h ≠ ε ∧ ε ∈ CongruenceSubgroup.Gamma0 M ∧
          (∀ x : SL(2, ℤ), ε * x = x * ε) ∧ ε * ε = 1 ∧ ε⁻¹ = ε ∧
          gamma0Rep M c * h⁻¹ * (gamma0Rep M c')⁻¹ = ε := by
      rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hwo hgw with hg | hg
      · exact ⟨1, hh1, one_mem _, fun x => by rw [one_mul, mul_one], one_mul 1, inv_one, hg⟩
      · refine ⟨-1, hh2, hnegmem, fun x => by rw [neg_one_mul, mul_neg_one], ?_, ?_, hg⟩
        · rw [neg_mul_neg, one_mul]
        · exact inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, one_mul])
    have hkey : gamma0Rep M c * h⁻¹ = ε * gamma0Rep M c' := by
      rw [← hgeq]; group
    have hc'eq : gamma0Rep M c' = ε * gamma0Rep M c * h⁻¹ := by
      rw [mul_assoc, hkey, ← mul_assoc, hεsq, one_mul]
    have hcc : c' = c := by
      rw [← gamma0Rep_spec M c', ← gamma0Rep_spec M c, QuotientGroup.eq]
      have hprod : (gamma0Rep M c')⁻¹ * gamma0Rep M c = h * ε := by
        rw [hc'eq, mul_inv_rev, mul_inv_rev, inv_inv, hεinv, mul_assoc, mul_assoc,
          hεcent (gamma0Rep M c), ← mul_assoc ((gamma0Rep M c)⁻¹), inv_mul_cancel, one_mul]
      rw [hprod]
      exact mul_mem hhmem hεmem
    subst hcc
    rw [hεcent] at hkey
    have hinv : h⁻¹ = ε := mul_left_cancel hkey
    exact hεne (by rw [← inv_inv h, hinv, hεinv])
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null (fun c => ?_)
  rw [volume_smul_specialLinearGroup]
  exact volume_modularFd_sdiff_fdo_eq_zero

section PeterssonSlashAdjoint
open scoped _root_.ModularForm

/-- **THE WEIGHT-2 DEGENERATION OF `petersson_slash`** (PROVEN 2026-07-27).
At `k = 2` the determinant factor of the pin's full `GL₂⁺` transformation law
is `|det γ|^{k-2} = |det γ|⁰ = 1`, and `σ γ = id` because `det γ > 0`.  So the
law collapses to `petersson 2 (f∣γ) (f'∣γ) τ = petersson 2 f f' (γ • τ)` — the
single identity the whole unfolding runs on, and weight `2` is exactly the
weight at which it is free of determinant bookkeeping. -/
theorem petersson_slash_two (f f' : ℍ → ℂ) {g : GL (Fin 2) ℝ}
    (hg : 0 < g.det.val) (τ : ℍ) :
    petersson (2 : ℤ) (f ∣[(2 : ℤ)] g) (f' ∣[(2 : ℤ)] g) τ
      = petersson (2 : ℤ) f f' (g • τ) := by
  rw [petersson_slash]
  simp only [sub_self, zpow_zero, one_mul, σ, if_pos hg, ContinuousAlgEquiv.refl_apply]

/-- **CHANGE OF VARIABLES FOR THE INVARIANT MEASURE** (PROVEN 2026-07-27):
`∫_{γ D} F = ∫_D F ∘ γ` for every `γ ∈ GL(2,ℝ)` and every set `D`.

This is the pin's `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume` in integral
form, obtained from `measurePreserving_smul` through
`MeasurePreserving.setIntegral_image_emb`.  No measurability hypothesis on `D`
is needed because the action is by measurable equivalences. -/
theorem setIntegral_smul_set_upperHalfPlane (g : GL (Fin 2) ℝ) (F : ℍ → ℂ)
    (D : Set ℍ) :
    (∫ τ in g • D, F τ) = ∫ τ in D, F (g • τ) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g (volume : Measure ℍ)).setIntegral_image_emb
    (measurableEmbedding_const_smul g) F D

/-- **THE ADJOINT IDENTITY FOR A SINGLE SLASH** (PROVEN 2026-07-27;
Diamond–Shurman *A First Course in Modular Forms* Proposition 5.5.2): moving a
slash across the Petersson integrand replaces it by the inverse slash on the
other argument, at the cost of moving the domain:

  `∫_D petersson 2 (F∣δ) F' = ∫_{δ D} petersson 2 F (F'∣δ⁻¹)`.

Proof: put `G = F'∣δ⁻¹`, so `G∣δ = F'` by `SlashAction.slash_mul` and
`SlashAction.slash_one`; then `petersson_slash_two` reads
`petersson 2 (F∣δ) F' τ = petersson 2 F G (δ • τ)` pointwise, and
`setIntegral_smul_set_upperHalfPlane` turns `∫_D (·) ∘ δ` into `∫_{δ D} (·)`.

Note this is UNCONDITIONAL on `D` — it is a change of variables, not a
fundamental-domain statement.  At weight `2` scalars act trivially
(`F∣(cI) = c^{k-2} F = F`), so `δ⁻¹` may freely be replaced by the INTEGRAL
matrix `det(δ)·δ⁻¹`, which is how the `α' = det(α)α⁻¹` of the textbook
argument appears. -/
theorem setIntegral_petersson_slash_adjoint (F F' : ℍ → ℂ) {δ : GL (Fin 2) ℝ}
    (hδ : 0 < δ.det.val) (D : Set ℍ) :
    (∫ τ in D, petersson (2 : ℤ) (F ∣[(2 : ℤ)] δ) F' τ)
      = ∫ τ in δ • D, petersson (2 : ℤ) F (F' ∣[(2 : ℤ)] δ⁻¹) τ := by
  have hback : (F' ∣[(2 : ℤ)] δ⁻¹) ∣[(2 : ℤ)] δ = F' := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have hfun : (fun τ : ℍ => petersson (2 : ℤ) (F ∣[(2 : ℤ)] δ) F' τ)
      = fun τ : ℍ => petersson (2 : ℤ) F (F' ∣[(2 : ℤ)] δ⁻¹) (δ • τ) := by
    funext τ
    rw [← petersson_slash_two F (F' ∣[(2 : ℤ)] δ⁻¹) hδ τ, hback]
  rw [setIntegral_smul_set_upperHalfPlane, hfun]

/-- The finite Hecke representative `[1, j; 0, q]` has determinant `q > 0`. -/
theorem det_heckeRep_pos {q : ℕ} (hq : q.Prime) (j : ℕ) :
    0 < (heckeRep q j).det.val := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hq' : (0 : ℝ) < q := lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hq0)
  unfold heckeRep
  rw [dif_pos hq0]
  simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of] using hq'

/-- The extra Hecke representative `[q, 0; 0, 1]` has determinant `q > 0`. -/
theorem det_heckeRepInf_pos {q : ℕ} (hq : q.Prime) :
    0 < (heckeRepInf q).det.val := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hq' : (0 : ℝ) < q := lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hq0)
  unfold heckeRepInf
  rw [dif_pos hq0]
  simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of] using hq'

/-- **INTEGRABILITY OF THE SLASHED PETERSSON INTEGRAND** (PROVEN 2026-07-27; cut
2026-07-27 out of `peterssonSelfAdjoint_of_gamma0FundamentalDomain` below,
which is PROVEN over it and over `setIntegral_heckeRep_unfold`): the
generalisation of `peterssonIntegrableOn` above from a pair of cusp forms to a
pair of `GL₂⁺`-TRANSLATES of cusp forms.  It is what lets the integral of the
Hecke slash-sum be split term by term.

WHY IT IS TRUE, and why it is a boundedness statement and nothing more.
`peterssonIntegrableOn` needs only two things — continuity, and a GLOBAL bound
on the integrand — and both survive slashing.  Continuity: a slash is a
continuous function times a precomposition with the (continuous) Möbius
action.  Boundedness is the substantive half, and it is an exact identity
rather than an estimate: for `δ` of positive determinant,

  `|(g∣[2]δ)(τ)| · Im τ = |g(δ • τ)| · Im (δ • τ)`,

because `(g∣[2]δ)(τ) = det(δ)·j(δ,τ)^{-2}·g(δ • τ)` while
`Im (δ • τ) = det(δ)·Im τ / |j(δ,τ)|²` (`UpperHalfPlane.im_smul_eq_div_normSq`).
So the slashed quantity `|g∣δ| · y` is the UNSLASHED quantity `|g| · y`
evaluated at another point of `ℍ`, hence bounded by the SAME constant that
`CuspFormClass.petersson_bounded_left` supplies for `g` itself — no new
analysis, and in particular no cusp condition for the conjugated group is
needed.  The integrand is the product of two such factors, so
`Measure.integrableOn_of_bounded` applies verbatim as in
`peterssonIntegrableOn`.

The lemma is stated with a slash in BOTH slots, with `δ = 1` (and
`SlashAction.slash_one`) recovering the one-sided cases; that is what makes a
single leaf cover all four uses in the assembly below.

HOW THE EXACT IDENTITY IS OBTAINED, which is the one trick in the proof.
Rather than expanding `ModularForm.slash_def` and juggling `denom` and
`im_smul_eq_div_normSq` by hand, take NORMS in `petersson_slash_two` with the
SAME function in both slots: it reads
`‖(u∣δ)(τ)‖² · y² = ‖u(δ•τ)‖² · Im(δ•τ)²`, i.e. the squares of the two
nonnegative quantities `‖(u∣δ)(τ)‖·y` and `‖u(δ•τ)‖·Im(δ•τ)` agree, whence
`mul_self_inj` gives the identity itself.  The global bound `‖u τ‖·y ≤ √C` for
a weight-`2` cusp form is `CuspFormClass.petersson_bounded_left` applied to the
DIAGONAL pair `(u, u)`, since `‖petersson 2 u u τ‖ = (‖u τ‖·y)²`. -/
theorem peterssonIntegrableOn_slash {M : ℕ} (hM : 0 < M) {D : Set ℍ}
    (hD : volume D ≠ ⊤) (f g : CuspForm (Gamma0GL M) 2)
    {δ₁ δ₂ : GL (Fin 2) ℝ} (hδ₁ : 0 < δ₁.det.val) (hδ₂ : 0 < δ₂.det.val) :
    IntegrableOn
      (petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] δ₁) (⇑f ∣[(2 : ℤ)] δ₂)) D volume := by
  haveI : NeZero M := ⟨hM.ne'⟩
  -- At weight `2` the norm of the Petersson integrand factors as the product of
  -- the two quantities `‖·‖ · y`.
  have hnorm : ∀ (u v : ℍ → ℂ) (τ : ℍ),
      ‖petersson (2 : ℤ) u v τ‖ = (‖u τ‖ * τ.im) * (‖v τ‖ * τ.im) := by
    intro u v τ
    simp only [petersson, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg τ.im_pos.le, zpow_two]
    ring
  -- `‖(u∣δ)(τ)‖ · Im τ = ‖u(δ•τ)‖ · Im (δ•τ)`, EXACTLY.
  have hslash : ∀ (u : ℍ → ℂ) {δ : GL (Fin 2) ℝ}, 0 < δ.det.val → ∀ τ : ℍ,
      ‖(u ∣[(2 : ℤ)] δ) τ‖ * τ.im = ‖u (δ • τ)‖ * (δ • τ).im := by
    intro u δ hδ τ
    have h := congrArg norm (petersson_slash_two u u hδ τ)
    rw [hnorm, hnorm] at h
    exact (mul_self_inj (mul_nonneg (norm_nonneg _) τ.im_pos.le)
      (mul_nonneg (norm_nonneg _) (δ • τ).im_pos.le)).mp h
  -- The global bound for a weight-`2` cusp form, from the DIAGONAL Petersson bound.
  have hbound : ∀ h : CuspForm (Gamma0GL M) 2,
      ∃ C : ℝ, ∀ τ : ℍ, ‖(h : ℍ → ℂ) τ‖ * τ.im ≤ C := by
    intro h
    obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (2 : ℤ) (Gamma0GL M) h h
    refine ⟨Real.sqrt C, fun τ => ?_⟩
    have hCτ := hC τ
    rw [hnorm] at hCτ
    have hnn : (0 : ℝ) ≤ ‖(h : ℍ → ℂ) τ‖ * τ.im := mul_nonneg (norm_nonneg _) τ.im_pos.le
    calc ‖(h : ℍ → ℂ) τ‖ * τ.im
        = Real.sqrt ((‖(h : ℍ → ℂ) τ‖ * τ.im) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt (by rw [sq]; exact hCτ)
  obtain ⟨Cg, hCg⟩ := hbound g
  obtain ⟨Cf, hCf⟩ := hbound f
  refine Measure.integrableOn_of_bounded hD ?_ (M := Cg * Cf) ?_
  · have hc1 : Continuous (⇑g ∣[(2 : ℤ)] δ₁) :=
      ((ModularFormClass.holo g).slash (2 : ℤ) δ₁).continuous
    have hc2 : Continuous (⇑f ∣[(2 : ℤ)] δ₂) :=
      ((ModularFormClass.holo f).slash (2 : ℤ) δ₂).continuous
    exact (UpperHalfPlane.petersson_continuous (2 : ℤ) hc1 hc2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun τ => ?_
    rw [hnorm, hslash _ hδ₁, hslash _ hδ₂]
    exact mul_le_mul (hCg _) (hCf _)
      (mul_nonneg (norm_nonneg _) (δ₂ • τ).im_pos.le)
      (le_trans (mul_nonneg (norm_nonneg _) (δ₁ • τ).im_pos.le) (hCg (δ₁ • τ)))

/-- **SLASHING BY A POSITIVE SCALAR IS TRIVIAL AT WEIGHT `2`** (PROVEN 2026-07-27).
`(cI) • τ = τ`, `det (cI) = c²` and `denom (cI) τ = c`, so mathlib's
`f ∣[k] g = σ g (f (g • τ)) · |det g|^{k-1} · denom g τ^{-k}` collapses to
`f τ · c² · c^{-2} = f τ` at `k = 2`.  This is the ONE place the weight-2
hypothesis is used to identify `α⁻¹` with the INTEGRAL adjugate
`α' = det(α)·α⁻¹`, which is what makes the whole unfolding run over integral
matrices. -/
theorem slash_two_of_coe_eq_smul_one (F : ℍ → ℂ) {c : ℝ} (hc : 0 < c)
    {g : GL (Fin 2) ℝ} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = c • 1) :
    F ∣[(2 : ℤ)] g = F := by
  have hdet : g.det.val = c ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg]
    simp [pow_two]
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = c := by rw [hg]; simp
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg]; simp
  have hdenom : ∀ z : ℂ, UpperHalfPlane.denom g z = (c : ℂ) := by
    intro z
    simp [UpperHalfPlane.denom, hg]
  have hsmul : ∀ τ : ℍ, g • τ = τ := by
    intro τ
    have hgpos : 0 < g.det.val := by rw [hdet]; positivity
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hgpos]
    rw [UpperHalfPlane.num, hdenom, h00, h01]
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
    norm_num
  funext τ
  rw [ModularForm.slash_apply, hsmul, hdenom, hdet, σ, if_pos (by rw [hdet]; positivity)]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [abs_of_pos (by positivity)]
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  rw [zpow_neg]
  norm_num
  field_simp

/-- `α'·α = q·I`, so at weight `2` the two Hecke representatives are mutually
inverse under the slash action. -/
theorem heckeRepInf_mul_heckeRep_zero_coe {q : ℕ} (hq0 : (q : ℝ) ≠ 0) :
    ((heckeRepInf q * heckeRep q 0 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (q : ℝ) • 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [heckeRep_coe hq0, heckeRepInf_coe hq0, Matrix.mul_apply, Fin.sum_univ_two]

/-- `α·α' = q·I`. -/
theorem heckeRep_zero_mul_heckeRepInf_coe {q : ℕ} (hq0 : (q : ℝ) ≠ 0) :
    ((heckeRep q 0 * heckeRepInf q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (q : ℝ) • 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [heckeRep_coe hq0, heckeRepInf_coe hq0, Matrix.mul_apply, Fin.sum_univ_two]

/-- **PEELING A `Γ₀(M)`-ELEMENT OFF THE SECOND SLOT MOVES THE DOMAIN**
(PROVEN 2026-07-27): `∫_D petersson 2 g (f∣(δγ)) = ∫_{γ•D} petersson 2 g (f∣δ)`
for `γ ∈ Γ₀(M)`, since `g∣γ = g` and `petersson_slash_two` has determinant `1`. -/
theorem setIntegral_petersson_slash_mul_right {M : ℕ} (f g : CuspForm (Gamma0GL M) 2)
    (δ : GL (Fin 2) ℝ) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL M) (D : Set ℍ) :
    (∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (δ * γ)) τ)
      = ∫ τ in γ • D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] δ) τ := by
  have hpos : 0 < γ.det.val := by
    rw [Subgroup.HasDetOne.det_eq hγ]; norm_num
  have hg : ⇑g ∣[(2 : ℤ)] γ = ⇑g := SlashInvariantFormClass.slash_action_eq g γ hγ
  have hfun : (fun τ : ℍ => petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (δ * γ)) τ)
      = fun τ : ℍ => petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] δ) (γ • τ) := by
    funext τ
    rw [SlashAction.slash_mul, ← petersson_slash_two ⇑g (⇑f ∣[(2 : ℤ)] δ) hpos τ, hg]
  rw [hfun, setIntegral_smul_set_upperHalfPlane]

/-- **PEELING A `Γ₀(M)`-ELEMENT OFF THE FIRST SLOT MOVES THE DOMAIN**
(PROVEN 2026-07-27), the mirror image of the previous lemma. -/
theorem setIntegral_petersson_slash_mul_left {M : ℕ} (f g : CuspForm (Gamma0GL M) 2)
    (δ : GL (Fin 2) ℝ) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL M) (D : Set ℍ) :
    (∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] (δ * γ)) ⇑f τ)
      = ∫ τ in γ • D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] δ) ⇑f τ := by
  have hpos : 0 < γ.det.val := by
    rw [Subgroup.HasDetOne.det_eq hγ]; norm_num
  have hf : ⇑f ∣[(2 : ℤ)] γ = ⇑f := SlashInvariantFormClass.slash_action_eq f γ hγ
  have hfun : (fun τ : ℍ => petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] (δ * γ)) ⇑f τ)
      = fun τ : ℍ => petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] δ) ⇑f (γ • τ) := by
    funext τ
    rw [SlashAction.slash_mul, ← petersson_slash_two (⇑g ∣[(2 : ℤ)] δ) ⇑f hpos τ, hf]
  rw [hfun, setIntegral_smul_set_upperHalfPlane]

/-- **`F ∣ α⁻¹ = F ∣ α'` AT WEIGHT `2`** — the textbook's `α' = det(α)·α⁻¹`,
which is how an INTEGRAL matrix replaces the rational inverse. -/
theorem slash_heckeRep_zero_inv (F : ℍ → ℂ) {q : ℕ} (hq : q.Prime) :
    F ∣[(2 : ℤ)] (heckeRep q 0)⁻¹ = F ∣[(2 : ℤ)] heckeRepInf q := by
  conv_rhs => rw [show heckeRepInf q
      = (heckeRep q 0)⁻¹ * (heckeRep q 0 * heckeRepInf q) by group]
  rw [SlashAction.slash_mul]
  exact (slash_two_of_coe_eq_smul_one _
    (lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm (Nat.cast_ne_zero.mpr hq.ne_zero)))
    (heckeRep_zero_mul_heckeRepInf_coe (Nat.cast_ne_zero.mpr hq.ne_zero))).symm

/-- `F ∣ α'⁻¹ = F ∣ α` at weight `2`. -/
theorem slash_heckeRepInf_inv (F : ℍ → ℂ) {q : ℕ} (hq : q.Prime) :
    F ∣[(2 : ℤ)] (heckeRepInf q)⁻¹ = F ∣[(2 : ℤ)] heckeRep q 0 := by
  conv_rhs => rw [show heckeRep q 0
      = (heckeRepInf q)⁻¹ * (heckeRepInf q * heckeRep q 0) by group]
  rw [SlashAction.slash_mul]
  exact (slash_two_of_coe_eq_smul_one _
    (lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm (Nat.cast_ne_zero.mpr hq.ne_zero)))
    (heckeRepInf_mul_heckeRep_zero_coe (Nat.cast_ne_zero.mpr hq.ne_zero))).symm

/-- **TWO `G`-DOMAINS CARRY THE SAME INTEGRAL OF A `G`-INVARIANT FUNCTION**
(PROVEN 2026-07-27; the measure-theoretic core of the Hecke unfolding).

`U` and `V` are "domains" for `G` in the hand-rolled sense used throughout this
section: each MEETS every `G`-orbit (`hUcov`/`hVcov`) and is a.e. disjoint from
each of its `G`-translates other than the two that act trivially
(`hUdisj`/`hVdisj`).  That is weaker than `MeasureTheory.IsFundamentalDomain`,
which is UNSATISFIABLE here: `-1` acts trivially on `ℍ`, so `(-1) • U = U`
always has full measure.  The `±1` exclusions are exactly the price.

PROOF, and why the `±1` degeneracy costs nothing.  Index the pieces by the
QUOTIENT SET `G/±`, i.e. by `Quotient rel` for `rel a b ↔ a = b ∨ a = -b` — an
equivalence relation on `G` whose classes are precisely the fibres of
`γ ↦ γ • S`.  Then
* `U = ⋃_{[γ]} (U ∩ γ • V)` (covering by translates of `V`), the pieces being
  pairwise a.e. disjoint because distinct classes give `δ⁻¹γ ≠ ±1`;
* `V = ⋃_{[γ]} (γ⁻¹ • U ∩ V)` symmetrically;
* the two families match term by term: `γ⁻¹ • U ∩ V = γ⁻¹ • (U ∩ γ • V)`, and
  the change of variables `setIntegral_smul_set_upperHalfPlane` together with
  `hHinv` at `γ⁻¹` identifies the integrals.
`integral_iUnion_ae` then gives both sides as the SAME `tsum`.

Passing to `G/±` (rather than choosing coset representatives) is what removes
every appeal to `V` being non-null: well-definedness of `[γ] ↦ γ • V` is the
relation itself, not a stabilizer computation.

MEASURABILITY IS LOAD-BEARING (`hUm`, `hVm`).  See the counterexample recorded
on `setIntegral_heckeRep_unfold` below: for a non-measurable `U` the hypothesis
`hUdisj` is not an invariant of `volume.restrict U`, and the conclusion of this
lemma is FALSE — a Vitali-style rearrangement of the standard domain satisfies
every other hypothesis and doubles the integral. -/
theorem setIntegral_eq_of_smulDomain_of_invariant
    {G : Subgroup (GL (Fin 2) ℝ)} (hGc : Countable G)
    {U V : Set ℍ} (hUm : MeasurableSet U) (hVm : MeasurableSet V)
    (hUcov : ∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ U)
    (hUdisj : ∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • U) ∩ U) = 0)
    (hVcov : ∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ V)
    (hVdisj : ∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • V) ∩ V) = 0)
    {H : ℍ → ℂ} (hHU : IntegrableOn H U volume) (hHV : IntegrableOn H V volume)
    (hHinv : ∀ γ ∈ G, ∀ τ : ℍ, H (γ • τ) = H τ) :
    (∫ τ in U, H τ) = ∫ τ in V, H τ := by
  classical
  -- `-1` acts trivially on `ℍ`, hence on subsets of `ℍ`.
  have hnegset : ∀ (g : GL (Fin 2) ℝ) (S : Set ℍ), (-g) • S = g • S := by
    intro g S
    ext x
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (UpperHalfPlane.neg_smul g y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, UpperHalfPlane.neg_smul g y⟩
  have hneginv : ∀ g : GL (Fin 2) ℝ, (-g)⁻¹ = -g⁻¹ := by
    intro g
    refine inv_eq_of_mul_eq_one_right ?_
    rw [neg_mul_neg, mul_inv_cancel]
  have hsm : ∀ (g : GL (Fin 2) ℝ) (S : Set ℍ), MeasurableSet S → MeasurableSet (g • S) := by
    intro g S hS
    rw [← Set.image_smul]
    exact (measurableEmbedding_const_smul g).measurableSet_image.mpr hS
  -- The `±`-identification on `G`: two elements give the same translate of any set.
  let rel : Setoid ↥G :=
    { r := fun a b => (a : GL (Fin 2) ℝ) = b ∨ (a : GL (Fin 2) ℝ) = -b
      iseqv := by
        refine ⟨fun a => Or.inl rfl, ?_, ?_⟩
        · rintro a b (h | h)
          · exact Or.inl h.symm
          · exact Or.inr (by rw [h, neg_neg])
        · rintro a b c (h1 | h1) (h2 | h2)
          · exact Or.inl (h1.trans h2)
          · exact Or.inr (h1.trans h2)
          · exact Or.inr (by rw [h1, h2])
          · exact Or.inl (by rw [h1, h2, neg_neg]) }
  -- The two families of pieces, indexed by `G/±`.
  let sU : Quotient rel → Set ℍ := fun c =>
    Quotient.liftOn c (fun γ : ↥G => U ∩ ((γ : GL (Fin 2) ℝ) • V)) (by
      rintro a b (h | h)
      · rw [h]
      · rw [h, hnegset])
  let sV : Quotient rel → Set ℍ := fun c =>
    Quotient.liftOn c (fun γ : ↥G => (((γ : GL (Fin 2) ℝ))⁻¹ • U) ∩ V) (by
      rintro a b (h | h)
      · rw [h]
      · rw [h, hneginv, hnegset])
  have hsUmk : ∀ γ : ↥G, sU (Quotient.mk rel γ) = U ∩ ((γ : GL (Fin 2) ℝ) • V) :=
    fun _ => rfl
  have hsVmk : ∀ γ : ↥G, sV (Quotient.mk rel γ)
      = (((γ : GL (Fin 2) ℝ))⁻¹ • U) ∩ V := fun _ => rfl
  -- Distinct classes are `≠ 1` and `≠ -1` apart.
  have hne : ∀ a b : ↥G, Quotient.mk rel a ≠ Quotient.mk rel b →
      (a : GL (Fin 2) ℝ) ≠ b ∧ (a : GL (Fin 2) ℝ) ≠ -b := fun a b hab =>
    ⟨fun h => hab (Quotient.sound (Or.inl h)),
      fun h => hab (Quotient.sound (Or.inr h))⟩
  -- The `U`-side tiling.
  have hUunion : U = ⋃ c : Quotient rel, sU c := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨γ, hγ, hmem⟩ := hVcov x
      refine ⟨Quotient.mk rel ⟨γ⁻¹, inv_mem hγ⟩, ?_⟩
      rw [hsUmk]
      exact ⟨hx, Set.mem_smul_set_iff_inv_smul_mem.mpr (by simpa using hmem)⟩
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with
      | h γ => exact (hsUmk γ ▸ hc).1
  have hVunion : V = ⋃ c : Quotient rel, sV c := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨γ, hγ, hmem⟩ := hUcov x
      refine ⟨Quotient.mk rel ⟨γ, hγ⟩, ?_⟩
      rw [hsVmk]
      exact ⟨Set.mem_smul_set_iff_inv_smul_mem.mpr (by simpa using hmem), hx⟩
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with
      | h γ => exact (hsVmk γ ▸ hc).2
  -- Measurability of the pieces.
  have hsUm : ∀ c, MeasurableSet (sU c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h γ => exact (hsUmk γ ▸ hUm.inter (hsm _ _ hVm))
  have hsVm : ∀ c, MeasurableSet (sV c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h γ => exact (hsVmk γ ▸ (hsm _ _ hUm).inter hVm)
  -- Pairwise a.e. disjointness of the pieces.
  have hsUd : Pairwise (Function.onFun (AEDisjoint volume) sU) := by
    intro c d hcd
    revert hcd
    refine Quotient.inductionOn₂ c d ?_
    intro a b hcd
    obtain ⟨h1, h2⟩ := hne a b hcd
    have k1 : ((b : GL (Fin 2) ℝ))⁻¹ * (a : GL (Fin 2) ℝ) ≠ 1 := fun h => h1 (by
      have := congrArg (fun x => (b : GL (Fin 2) ℝ) * x) h
      simpa [← mul_assoc] using this)
    have k2 : ((b : GL (Fin 2) ℝ))⁻¹ * (a : GL (Fin 2) ℝ) ≠ -1 := fun h => h2 (by
      have := congrArg (fun x => (b : GL (Fin 2) ℝ) * x) h
      simpa [← mul_assoc] using this)
    have hkey : ((a : GL (Fin 2) ℝ) • V) ∩ ((b : GL (Fin 2) ℝ) • V)
        = (b : GL (Fin 2) ℝ) •
            ((((b : GL (Fin 2) ℝ))⁻¹ * (a : GL (Fin 2) ℝ)) • V ∩ V) := by
      rw [Set.smul_set_inter, smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
    have hz : volume (((a : GL (Fin 2) ℝ) • V) ∩ ((b : GL (Fin 2) ℝ) • V)) = 0 := by
      rw [hkey, measure_smul]
      exact hVdisj _ (mul_mem (inv_mem b.2) a.2) k1 k2
    exact measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_right Set.inter_subset_right) hz
  have hsVd : Pairwise (Function.onFun (AEDisjoint volume) sV) := by
    intro c d hcd
    revert hcd
    refine Quotient.inductionOn₂ c d ?_
    intro a b hcd
    obtain ⟨h1, h2⟩ := hne a b hcd
    have k1 : (a : GL (Fin 2) ℝ) * ((b : GL (Fin 2) ℝ))⁻¹ ≠ 1 := fun h => h1 (by
      have := congrArg (fun x => x * (b : GL (Fin 2) ℝ)) h
      simpa [mul_assoc] using this)
    have k2 : (a : GL (Fin 2) ℝ) * ((b : GL (Fin 2) ℝ))⁻¹ ≠ -1 := fun h => h2 (by
      have := congrArg (fun x => x * (b : GL (Fin 2) ℝ)) h
      simpa [mul_assoc] using this)
    have hkey : (((a : GL (Fin 2) ℝ))⁻¹ • U) ∩ (((b : GL (Fin 2) ℝ))⁻¹ • U)
        = ((a : GL (Fin 2) ℝ))⁻¹ •
            (U ∩ ((a : GL (Fin 2) ℝ) * ((b : GL (Fin 2) ℝ))⁻¹) • U) := by
      rw [Set.smul_set_inter, smul_smul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hz : volume ((((a : GL (Fin 2) ℝ))⁻¹ • U) ∩ (((b : GL (Fin 2) ℝ))⁻¹ • U)) = 0 := by
      rw [hkey, measure_smul, Set.inter_comm]
      exact hUdisj _ (mul_mem a.2 (inv_mem b.2)) k1 k2
    exact measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) hz
  -- Matching the two families term by term.
  have hterm : ∀ c, (∫ τ in sU c, H τ) = ∫ τ in sV c, H τ := by
    intro c
    induction c using Quotient.inductionOn with
    | h γ =>
      rw [hsUmk, hsVmk]
      have hset : (((γ : GL (Fin 2) ℝ))⁻¹ • U) ∩ V
          = ((γ : GL (Fin 2) ℝ))⁻¹ • (U ∩ ((γ : GL (Fin 2) ℝ) • V)) := by
        rw [Set.smul_set_inter, smul_smul, inv_mul_cancel, one_smul]
      rw [hset, setIntegral_smul_set_upperHalfPlane]
      exact setIntegral_congr_fun (hUm.inter (hsm _ _ hVm))
        (fun τ _ => (hHinv _ (inv_mem γ.2) τ).symm)
  rw [hUunion, hVunion,
    integral_iUnion_ae (fun c => (hsUm c).nullMeasurableSet) hsUd (by rwa [← hUunion]),
    integral_iUnion_ae (fun c => (hsVm c).nullMeasurableSet) hsVd (by rwa [← hVunion])]
  exact tsum_congr hterm

section GammaPrimeTiling
open _root_.Matrix.SpecialLinearGroup _root_.CongruenceSubgroup _root_.ConjAct

/-- **CONJUGATION BY `α = heckeRep q 0 = [1, 0; 0, q]`, INVERSE-FREE** (PROVEN
2026-07-27): `α · [a, q b; c, d] = [a, b; q c, d] · α`.  Conjugation by `α`
divides the upper-right entry by `q` and multiplies the lower-left by `q`; this
is the equational form of that, stated so that no rational inverse ever appears
and both directions (`α ρ α⁻¹` and `α⁻¹ ρ α`) are instances of the SAME lemma —
read left-to-right it computes `α ρ α⁻¹` from `ρ = x`, read right-to-left it
computes `α⁻¹ σ α` from `σ = y`. -/
theorem heckeRep_zero_mul_mapGL_comm {q : ℕ} (hq0 : (q : ℝ) ≠ 0) {a b c d : ℤ}
    {x y : SL(2, ℤ)}
    (hx : (x : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (q : ℤ) * b; c, d])
    (hy : (y : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; (q : ℤ) * c, d]) :
    heckeRep q 0 * mapGL ℝ x = mapGL ℝ y * heckeRep q 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    · simp [heckeRep_coe hq0, mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
      try push_cast
      try ring

/-- **A COSET ENUMERATION TURNS A `Γ`-DOMAIN INTO A `G`-DOMAIN** (PROVEN
2026-07-27): if `D` is a domain for `Γ` in the hand-rolled `hcov`/`hdisj` sense
used throughout this section, and `r : ι → Γ` is a FINITE family which
enumerates `Γ/G` — every `γ ∈ Γ` has `r o * γ ∈ G` for some `o` (surjectivity),
and `r p * (r o)⁻¹ ∈ G` forces `o = p` (injectivity) — then

  `U = ⋃ o, r o • D`

is a domain for `G`, of finite volume, and its tiles are pairwise a.e.
disjoint (so the integral over `U` is the finite sum of the tile integrals).

WHY.  Covering: given `τ`, `hcov` supplies `γ ∈ Γ` with `γ • τ ∈ D`; picking `o`
with `ρ = r o * γ ∈ G` gives `ρ • τ ∈ r o • D ⊆ U`.  Disjointness: `(γ • U) ∩ U`
decomposes into the pieces `(γ • r o • D) ∩ (r p • D) = r p • (((r p)⁻¹ γ r o) • D ∩ D)`,
each of which is null by `hdisj` unless `(r p)⁻¹ γ r o = ±1`; and that equality
forces `r p * (r o)⁻¹ = ±γ ∈ G`, hence `o = p` by injectivity, hence `γ = ±1`.
The SAME computation at `γ = 1` gives the pairwise tile disjointness.

`-1 ∈ G` is what makes the `±1` exclusions cost nothing — see
`setIntegral_eq_of_smulDomain_of_invariant` above for why they cannot be
dropped (`-1` acts trivially on `ℍ`, so no honest `IsFundamentalDomain`
exists). -/
theorem smulDomain_of_cosetReps {Γ G : Subgroup (GL (Fin 2) ℝ)} (hGΓ : G ≤ Γ)
    (hneg : (-1 : GL (Fin 2) ℝ) ∈ G)
    {D : Set ℍ} (hDmeas : MeasurableSet D) (hDvol : volume D ≠ ⊤)
    (hcov : ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ D)
    (hdisj : ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → volume ((γ • D) ∩ D) = 0)
    {ι : Type} [Fintype ι] (r : ι → GL (Fin 2) ℝ) (hrΓ : ∀ o, r o ∈ Γ)
    (hfind : ∀ γ ∈ Γ, ∃ o, r o * γ ∈ G)
    (hinj : ∀ o p : ι, r p * (r o)⁻¹ ∈ G → o = p) :
    MeasurableSet (⋃ o, r o • D) ∧ volume (⋃ o, r o • D) ≠ ⊤ ∧
      (∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ ⋃ o, r o • D) ∧
      (∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 →
        volume ((γ • (⋃ o, r o • D)) ∩ (⋃ o, r o • D)) = 0) ∧
      Pairwise (Function.onFun (AEDisjoint volume) (fun o => r o • D)) := by
  classical
  have hsm : ∀ (h : GL (Fin 2) ℝ) (S : Set ℍ), MeasurableSet S → MeasurableSet (h • S) := by
    intro h S hS
    rw [← Set.image_smul]
    exact (measurableEmbedding_const_smul h).measurableSet_image.mpr hS
  have hnegmem : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    have hmm := mul_mem hneg hx
    rwa [neg_one_mul] at hmm
  have hkey0 : ∀ (o p : ι) (γ : GL (Fin 2) ℝ),
      (γ • (r o • D)) ∩ (r p • D) = r p • ((((r p)⁻¹ * (γ * r o)) • D) ∩ D) := by
    intro o p γ
    rw [smul_smul, Set.smul_set_inter, smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
  have hpm : ∀ (o p : ι) (γ : GL (Fin 2) ℝ), γ ∈ G →
      ((r p)⁻¹ * (γ * r o) = 1 ∨ (r p)⁻¹ * (γ * r o) = -1) →
      o = p ∧ (γ = 1 ∨ γ = -1) := by
    intro o p γ hγ hcase
    have hrp : r p * ((r p)⁻¹ * (γ * r o)) = γ * r o := by group
    rcases hcase with h | h
    · rw [h, mul_one] at hrp
      have hg : r p * (r o)⁻¹ = γ := by rw [hrp]; group
      have hop := hinj o p (by rw [hg]; exact hγ)
      subst hop
      refine ⟨rfl, Or.inl ?_⟩
      have h1 : γ * r o = 1 * r o := by rw [one_mul]; exact hrp.symm
      exact mul_right_cancel h1
    · rw [h, mul_neg_one] at hrp
      have hg : -(r p * (r o)⁻¹) = γ := by rw [← neg_mul, hrp]; group
      have hg2 : r p * (r o)⁻¹ = -γ := by rw [← hg, neg_neg]
      have hop := hinj o p (by rw [hg2]; exact hnegmem γ hγ)
      subst hop
      refine ⟨rfl, Or.inr ?_⟩
      have h1 : γ * r o = (-1 : GL (Fin 2) ℝ) * r o := by
        rw [neg_one_mul]; exact hrp.symm
      exact mul_right_cancel h1
  have hmain : ∀ (o p : ι) (γ : GL (Fin 2) ℝ), γ ∈ G → γ ≠ 1 → γ ≠ -1 →
      volume ((γ • (r o • D)) ∩ (r p • D)) = 0 := by
    intro o p γ hγ h1 h2
    rw [hkey0, measure_smul]
    refine hdisj _ (mul_mem (inv_mem (hrΓ p)) (mul_mem (hGΓ hγ) (hrΓ o))) ?_ ?_
    · intro he
      rcases (hpm o p γ hγ (Or.inl he)).2 with h | h
      · exact h1 h
      · exact h2 h
    · intro he
      rcases (hpm o p γ hγ (Or.inr he)).2 with h | h
      · exact h1 h
      · exact h2 h
  refine ⟨MeasurableSet.iUnion fun o => hsm _ _ hDmeas, ?_, ?_, ?_, ?_⟩
  · refine ne_of_lt (lt_of_le_of_lt (measure_iUnion_le _) ?_)
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.mpr fun o _ => ?_
    rw [measure_smul]
    exact hDvol.lt_top
  · intro τ
    obtain ⟨γ, hγΓ, hmem⟩ := hcov τ
    obtain ⟨o, ho⟩ := hfind γ hγΓ
    refine ⟨r o * γ, ho, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨o, ?_⟩
    rw [← smul_smul]
    exact Set.smul_mem_smul_set hmem
  · intro γ hγ h1 h2
    rw [Set.smul_set_iUnion, Set.iUnion_inter]
    refine measure_iUnion_null fun o => ?_
    rw [Set.inter_iUnion]
    exact measure_iUnion_null fun p => hmain o p γ hγ h1 h2
  · intro o p hop
    show volume ((r o • D) ∩ (r p • D)) = 0
    have h0 := hkey0 o p 1
    rw [one_smul] at h0
    rw [h0, measure_smul]
    refine hdisj _ (mul_mem (inv_mem (hrΓ p)) (by rw [one_mul]; exact hrΓ o)) ?_ ?_
    · intro he; exact hop (hpm o p 1 (one_mem G) (Or.inl he)).1
    · intro he; exact hop (hpm o p 1 (one_mem G) (Or.inr he)).1

/-- **A `G`-DOMAIN TRANSPORTS ALONG ANY ELEMENT NORMALIZING `G`** (PROVEN
2026-07-27): if `η G η⁻¹ ⊆ G` and `η⁻¹ G η ⊆ G`, then `η • U` is a `G`-domain
whenever `U` is.  Covering transports by applying `hUcov` at `η⁻¹ • τ` and
conjugating; disjointness by
`(γ • η • U) ∩ (η • U) = η • (((η⁻¹ γ η) • U) ∩ U)` and invariance of the
measure under the `GL₂⁺`-action.  Both inclusions are needed and neither
follows from the other by finiteness.

(The normalising element is called `etaW` in the Lean text, not `η`: this
section is under `open scoped ModularForm`, where `η` is mathlib's RESERVED
notation for the Dedekind eta function, and a binder named `η` is a PARSE
error here even though it is fine elsewhere in this file.  The prose keeps
`η`, which is what the surrounding docstrings use.) -/
theorem smulDomain_smul_of_normalizes {G : Subgroup (GL (Fin 2) ℝ)} {U : Set ℍ}
    {etaW : GL (Fin 2) ℝ}
    (hn : ∀ γ ∈ G, etaW * γ * etaW⁻¹ ∈ G) (hn' : ∀ γ ∈ G, etaW⁻¹ * γ * etaW ∈ G)
    (hUcov : ∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ U)
    (hUdisj : ∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • U) ∩ U) = 0) :
    (∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ etaW • U) ∧
      (∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • (etaW • U)) ∩ (etaW • U)) = 0) := by
  constructor
  · intro τ
    obtain ⟨γ, hγ, hmem⟩ := hUcov (etaW⁻¹ • τ)
    refine ⟨etaW * γ * etaW⁻¹, hn γ hγ, ?_⟩
    have hrw : (etaW * γ * etaW⁻¹) • τ = etaW • (γ • (etaW⁻¹ • τ)) := by
      rw [smul_smul, smul_smul, mul_assoc]
    rw [hrw]
    exact Set.smul_mem_smul_set hmem
  · intro γ hγ h1 h2
    have hkey : (γ • (etaW • U)) ∩ (etaW • U) = etaW • (((etaW⁻¹ * γ * etaW) • U) ∩ U) := by
      rw [smul_smul, Set.smul_set_inter, smul_smul, ← mul_assoc, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [hkey, measure_smul]
    refine hUdisj _ (hn' γ hγ) ?_ ?_
    · intro he
      refine h1 ?_
      have hb : γ = etaW * (etaW⁻¹ * γ * etaW) * etaW⁻¹ := by group
      rw [he, mul_one, mul_inv_cancel] at hb
      exact hb
    · intro he
      refine h2 ?_
      have hb : γ = etaW * (etaW⁻¹ * γ * etaW) * etaW⁻¹ := by group
      rw [he, mul_neg_one, neg_mul, mul_inv_cancel] at hb
      exact hb

/-- **THE Γ'-COSET TILING OF THE HECKE DOUBLE COSET** (PROVEN 2026-07-27 over
`smulDomain_of_cosetReps` and `smulDomain_smul_of_normalizes` above; cut
2026-07-27 out of `setIntegral_heckeRep_unfold` below, which is PROVEN over it
and over `setIntegral_eq_of_smulDomain_of_invariant` above): the two families
of `q + 1` translates of `D` occurring in the unfolding identity are both
tilings of a fundamental domain for `Γ' = Γ₀(M) ∩ α⁻¹Γ₀(M)α`, over which the
integrand `petersson 2 g (f∣α)` is invariant.

This leaf carries ALL the remaining group theory and ALL the remaining
finite-additivity bookkeeping.  Nothing analytic is left in it: the weight-2
degeneration, the change of variables, the adjoint identity and the
two-domain comparison are all proven around it.

**THE WITNESSES**, in full, so that this is a construction task and not a
search.  Write `α = heckeRep q 0 = [1,0;0,q]`, `α' = heckeRepInf q = [q,0;0,1]`,
`T^j = mapGL (heckeTMat j) = [1,j;0,1]`.

* `G = Γ' = Γ₀(M) ∩ α⁻¹Γ₀(M)α`.  By `heckeRep_conj_mem_iff` (§HeckeStability
  above) this is `{ρ ∈ Γ₀(M) : q ∣ ρ₀₁}`, i.e. `Γ₀(M) ∩ Γ⁰(q)`; the second
  conjunct of this statement is exactly its membership predicate, spelled out
  so that no new subgroup definition is needed.  `-1 ∈ Γ'`, which is why the
  `±1` exclusions in `hdisj` cost nothing.
* `qu − Mv = 1` (solvable EXACTLY because `q ∤ M` — THIS is where `hqM` enters),
  `W = mapGL [uq, v; M, 1] ∈ Γ₀(M)`, `D₀ = mapGL [u, v; M, q] ∈ Γ₀(M)`, with
  `α · W = D₀ · α'`.  These three are already constructed inside the proof of
  `exists_cuspForm_heckeTransform` (§HeckeStability) as `W`/`D`/`hkey`.
* `U = (⋃_{j<q} T^j • D) ∪ W • D`, and `V = η • U` for `η = W · α`.

**WHY `U` IS A Γ'-DOMAIN**, with the two facts to hoist rather than redo.
`Γ₀(M) = ⊔_{o : Option (Fin q)} γ_o Γ'` with `γ_j = T^{-j}` and `γ_∞ = W⁻¹`, so
`U = ⊔_o γ_o⁻¹ • D`.
* COVERING: given `τ`, `hcov` supplies `γ ∈ Γ₀(M)` with `γ • τ ∈ D`; writing
  `γ = γ_o γ'` gives `γ' • τ ∈ γ_o⁻¹ • D ⊆ U`.  The case split is the one in
  `hfind`/`hsurj` of `exists_cuspForm_heckeTransform`: if `q ∤ γ₁₁` then
  `T^j γ ∈ Γ'` for `j ≡ −γ₀₁γ₁₁⁻¹ (mod q)`; if `q ∣ γ₁₁` then `W γ ∈ Γ'`
  because `(Wγ)₀₁ = uq·γ₀₁ + v·γ₁₁`.
* DISJOINTNESS: `γ' • U ∩ U` decomposes into the `γ_p γ' γ_o⁻¹ • D ∩ D`, and
  `γ_p γ' γ_o⁻¹ = ±1` forces `o = p` and `γ' = ±1` — the `hEinj`/`hmix`
  computations of `exists_cuspForm_heckeTransform` (`q ∤ (j − k)` for
  `0 ≤ j, k < q`; and `q ∤ v` because `qu − Mv = 1`).

**WHY `V = η • U` IS A Γ'-DOMAIN**: `η = Wα` NORMALIZES `Γ'`.  Explicitly, for
`ρ = [a,b;c,d] ∈ Γ'` (so `q ∣ b`, `M ∣ c`), `η ρ η⁻¹` is the INTEGRAL matrix

  `[ qua + qvc − Mub − Mvd ,  q(u²b + uvd − uva − v²c) ;
     Ma + qc − M²(b/q) − Md ,  uMb + uqd − vMa − vqc ]`,

whose lower-left is divisible by `M` and whose upper-right is divisible by `q`,
so it lies in `Γ'` again.  Verify it in the equivalent inverse-free form
`η · mapGL ρ = mapGL ρ' · η`.  Covering and disjointness for `V` then transport
from `U` along `η` in three lines each.

**WHY THE TWO INTEGRAL IDENTITIES HOLD** (the last two conjuncts).  Write
`H = petersson 2 g (f∣α)` and `L = petersson 2 g (f∣α')`.
* `L = H ∘ W`: `H (W • τ) = petersson 2 (g∣W) ((f∣α)∣W) τ = petersson 2 g
  (f∣(αW)) τ = petersson 2 g (f∣(D₀α')) τ = L τ`, using `g∣W = g`, `f∣D₀ = f`
  and `αW = D₀α'`.  Hence `∫_{W • D} H = ∫_D L`, which is the `∞`-tile of the
  first identity; the finite tiles are literal.
* `η • (T^j • D) = (W α T^j) • D` and `∫_{(WαT^j) • D} H = ∫_{(αT^j) • D} L`
  by the same substitution; and `η • (W • D) = (W D₀) • (α' • D)` with
  `W D₀ ∈ Γ'` (lower-left `M(u+1)`, upper-right `vq(u+1)`), so Γ'-invariance of
  `H` turns that tile into `∫_{α' • D} H`.  Those are the two tiles of the
  second identity.
* Both identities are then finite additivity over the a.e.-disjoint tiles,
  which is where `hDmeas` is consumed.

`volume U ≠ ⊤` and `volume V ≠ ⊤` are `hDvol` plus `measure_smul`; `Countable G`
holds because `Γ' ≤ Gamma0GL M`, the injective `mapGL`-image of a subgroup of
the countable group `SL(2, ℤ)`.

FAITHFULNESS.  Every hypothesis of the consumer is present, and `hqM` is
LOAD-BEARING: without `qu − Mv = 1` there is no `W`, `α' ∉ Γ₀(M)αΓ₀(M)`, and
the unfolding identity is FALSE (at `q ∣ M` the operator `U_q` is genuinely
non-self-adjoint).

NOTE ON SPELLING: `η` is written `etaW` in the proof below.  This section is
under `open scoped ModularForm`, where `η` is mathlib's reserved notation for
the Dedekind eta function, so a binder named `η` is a PARSE error here — even
though `η` is used freely as an identifier earlier in this same file, outside
that `open scoped`. -/
theorem exists_gammaPrimeTiling {M : ℕ} (hM : 0 < M)
    {D : Set ℍ} (hDvol : volume D ≠ ⊤) (hDmeas : MeasurableSet D)
    (hcov : ∀ τ : ℍ, ∃ γ ∈ Gamma0GL M, γ • τ ∈ D)
    (hdisj : ∀ γ ∈ Gamma0GL M, γ ≠ 1 → γ ≠ -1 → volume ((γ • D) ∩ D) = 0)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (f g : CuspForm (Gamma0GL M) 2) :
    ∃ (G : Subgroup (GL (Fin 2) ℝ)) (U V : Set ℍ),
      Countable G ∧
      (∀ γ ∈ G, γ ∈ Gamma0GL M ∧
        heckeRep q 0 * γ * (heckeRep q 0)⁻¹ ∈ Gamma0GL M) ∧
      MeasurableSet U ∧ volume U ≠ ⊤ ∧
      (∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ U) ∧
      (∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • U) ∩ U) = 0) ∧
      MeasurableSet V ∧ volume V ≠ ⊤ ∧
      (∀ τ : ℍ, ∃ γ ∈ G, γ • τ ∈ V) ∧
      (∀ γ ∈ G, γ ≠ 1 → γ ≠ -1 → volume ((γ • V) ∩ V) = 0) ∧
      (∫ τ in U, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = (∑ j ∈ Finset.range q, ∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat j)) • D,
              petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
          + ∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ ∧
      (∫ τ in V, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = (∑ j ∈ Finset.range q,
              ∫ τ in (heckeRep q 0 * Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat j)) • D,
              petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ)
          + ∫ τ in (heckeRepInf q) • D,
              petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hFact : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hsm : ∀ (h : GL (Fin 2) ℝ) (S : Set ℍ), MeasurableSet S → MeasurableSet (h • S) := by
    intro h S hS
    rw [← Set.image_smul]
    exact (measurableEmbedding_const_smul h).measurableSet_image.mpr hS
  -- `qu − Mv = 1`, solvable exactly because `q ∤ M`: THIS is where `hqM` enters.
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * q - v * M = 1 := by
    have hcop : Nat.Coprime q M := (hq.coprime_iff_not_dvd).mpr hqM
    have hb := Nat.gcd_eq_gcd_ab q M
    rw [hcop] at hb
    refine ⟨Nat.gcdA q M, -(Nat.gcdB q M), ?_⟩
    push_cast at hb
    linarith [hb]
  set W : SL(2, ℤ) := ⟨!![u * q, v; (M : ℤ), 1], by
    rw [Matrix.det_fin_two_of]; linarith [huv]⟩ with hW
  set Dz : SL(2, ℤ) := ⟨!![u, v; (M : ℤ), (q : ℤ)], by
    rw [Matrix.det_fin_two_of]; linarith [huv]⟩ with hDz
  have hWmem : W ∈ Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    push_cast
    exact ZMod.natCast_self M
  have hDzmem : Dz ∈ Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    push_cast
    exact ZMod.natCast_self M
  have hWinv : W⁻¹ = ⟨!![1, -v; -(M : ℤ), u * q], by
      rw [Matrix.det_fin_two_of]; linarith [huv]⟩ := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hW]
  -- `α W = D₀ α'`.
  have hkey : heckeRep q 0 * mapGL ℝ W = mapGL ℝ Dz * heckeRepInf q := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      · simp [heckeRep_coe hq0, heckeRepInf_coe hq0, hW, hDz, mapGL_coe_matrix,
          Matrix.mul_apply, Fin.sum_univ_two]
        try ring
  have hqv : ¬ (q : ℤ) ∣ v := by
    intro hdv
    have h9 : (q : ℤ) ∣ u * q := ⟨u, mul_comm _ _⟩
    have h10 : (q : ℤ) ∣ v * M := hdv.mul_right _
    have h11 := dvd_sub h9 h10
    rw [huv] at h11
    exact absurd (Int.le_of_dvd one_pos h11) (by exact_mod_cast hq.one_lt.not_ge)
  -- `Γ' = Γ₀(M) ∩ α⁻¹Γ₀(M)α`, with its divisibility description.
  set Gp : Subgroup (GL (Fin 2) ℝ) :=
    Gamma0GL M ⊓ (toConjAct (heckeRep q 0)⁻¹ • Gamma0GL M) with hGp
  have hGpiff : ∀ ρ : SL(2, ℤ), ρ ∈ Gamma0 M → (mapGL ℝ ρ ∈ Gp ↔ (q : ℤ) ∣ ρ 0 1) := by
    intro ρ hρ
    rw [hGp, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h2⟩
      exact (heckeRep_conj_mem_iff hq hρ).mp (mem_conjAct_inv_smul_iff.mp h2)
    · intro h
      exact ⟨mem_Gamma0GL_iff.mpr ⟨ρ, hρ, rfl⟩,
        mem_conjAct_inv_smul_iff.mpr ((heckeRep_conj_mem_iff hq hρ).mpr h)⟩
  have hGpΓ : Gp ≤ Gamma0GL M := by rw [hGp]; exact inf_le_left
  have hGpconj : ∀ γ ∈ Gp, heckeRep q 0 * γ * (heckeRep q 0)⁻¹ ∈ Gamma0GL M := by
    intro γ hγ
    rw [hGp, Subgroup.mem_inf] at hγ
    exact mem_conjAct_inv_smul_iff.mp hγ.2
  -- `-1 ∈ Γ'`: this is why the `±1` exclusions cost nothing.
  have hnegdet : Matrix.det !![(-1 : ℤ), 0; 0, -1] = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  have hnegSL : mapGL ℝ (⟨!![(-1 : ℤ), 0; 0, -1], hnegdet⟩ : SL(2, ℤ))
      = (-1 : GL (Fin 2) ℝ) := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply]
  have hnegGp : (-1 : GL (Fin 2) ℝ) ∈ Gp := by
    rw [← hnegSL]
    refine (hGpiff _ ?_).mpr ?_
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((0 : ℤ)) : ZMod M) = 0
      simp
    · show (q : ℤ) ∣ (0 : ℤ)
      exact dvd_zero _
  -- the coset representatives `γ_j⁻¹ = T^j`, `γ_∞⁻¹ = W`
  obtain ⟨r, hrnone, hrsome⟩ : ∃ r : Option (Fin q) → GL (Fin 2) ℝ,
      r none = mapGL ℝ W ∧
        ∀ j : Fin q, r (some j) = mapGL ℝ (heckeTMat ((j : ℕ) : ℤ)) :=
    ⟨fun o => Option.elim o (mapGL ℝ W) (fun j => mapGL ℝ (heckeTMat ((j : ℕ) : ℤ))),
      rfl, fun _ => rfl⟩
  have hrΓ : ∀ o, r o ∈ Gamma0GL M := by
    rintro (_ | j)
    · rw [hrnone]; exact mem_Gamma0GL_iff.mpr ⟨W, hWmem, rfl⟩
    · rw [hrsome]; exact mem_Gamma0GL_iff.mpr ⟨_, heckeTMat_mem_Gamma0 M _, rfl⟩
  -- SURJECTIVITY of the enumeration (the `hfind`/`hsurj` case split).
  have hfind : ∀ γ ∈ Gamma0GL M, ∃ o, r o * γ ∈ Gp := by
    intro γ hγ
    obtain ⟨δ, hδ, hδeq⟩ := mem_Gamma0GL_iff.mp hγ
    by_cases hqd : (q : ℤ) ∣ δ 1 1
    · refine ⟨none, ?_⟩
      have hmul : r none * γ = mapGL ℝ (W * δ) := by rw [map_mul, hδeq, hrnone]
      rw [hmul]
      refine (hGpiff _ (mul_mem hWmem hδ)).mpr ?_
      have hval : (W * δ) 0 1 = u * q * δ 0 1 + v * δ 1 1 := by
        rw [SL2_mul_apply_zero_one]; simp [hW]
      rw [hval]
      exact dvd_add ⟨u * δ 0 1, by ring⟩ (hqd.mul_left v)
    · have hdbar : ((δ 1 1 : ℤ) : ZMod q) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨some ⟨(-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val,
        ZMod.val_lt _⟩, ?_⟩
      have hmul : r (some ⟨(-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val,
            ZMod.val_lt _⟩) * γ
          = mapGL ℝ (heckeTMat
              (((-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val : ℕ) : ℤ) * δ) := by
        rw [map_mul, hδeq, hrsome]
      rw [hmul]
      refine (hGpiff _ (mul_mem (heckeTMat_mem_Gamma0 M _) hδ)).mpr ?_
      have hval : (heckeTMat
            (((-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val : ℕ) : ℤ) * δ) 0 1
          = δ 0 1 +
            (((-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val : ℕ) : ℤ) * δ 1 1 := by
        rw [SL2_mul_apply_zero_one]
        simp [heckeTMat]
      rw [hval, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id]
      field_simp
      ring
  -- INJECTIVITY of the enumeration (`hEinj`/`hmix`: `q ∤ (j − k)` and `q ∤ v`).
  have hinj : ∀ o p : Option (Fin q), r p * (r o)⁻¹ ∈ Gp → o = p := by
    rintro (_ | j) (_ | k) h
    · rfl
    · exfalso
      have hmul : r (some k) * (r none)⁻¹ = mapGL ℝ (heckeTMat ((k : ℕ) : ℤ) * W⁻¹) := by
        rw [map_mul, map_inv, hrsome, hrnone]
      rw [hmul] at h
      have hd := (hGpiff _ (mul_mem (heckeTMat_mem_Gamma0 M _) (inv_mem hWmem))).mp h
      have hval : (heckeTMat ((k : ℕ) : ℤ) * W⁻¹) 0 1 = -v + ((k : ℕ) : ℤ) * (u * q) := by
        rw [hWinv, SL2_mul_apply_zero_one]
        simp [heckeTMat]
      rw [hval] at hd
      refine hqv ?_
      have h7 : (q : ℤ) ∣ ((k : ℕ) : ℤ) * (u * q) := ⟨((k : ℕ) : ℤ) * u, by ring⟩
      have h8 := dvd_sub h7 hd
      have h9 : ((k : ℕ) : ℤ) * (u * q) - (-v + ((k : ℕ) : ℤ) * (u * q)) = v := by ring
      rwa [h9] at h8
    · exfalso
      have hmul : r none * (r (some j))⁻¹ = mapGL ℝ (W * (heckeTMat ((j : ℕ) : ℤ))⁻¹) := by
        rw [map_mul, map_inv, hrsome, hrnone]
      rw [hmul] at h
      have hd := (hGpiff _ (mul_mem hWmem (inv_mem (heckeTMat_mem_Gamma0 M _)))).mp h
      have hval : (W * (heckeTMat ((j : ℕ) : ℤ))⁻¹) 0 1
          = u * q * (-((j : ℕ) : ℤ)) + v := by
        rw [heckeTMat_inv, SL2_mul_apply_zero_one]
        simp [hW, heckeTMat]
      rw [hval] at hd
      refine hqv ?_
      have h7 : (q : ℤ) ∣ u * q * (-((j : ℕ) : ℤ)) := ⟨u * (-((j : ℕ) : ℤ)), by ring⟩
      have h8 := dvd_sub hd h7
      have h9 : u * q * (-((j : ℕ) : ℤ)) + v - u * q * (-((j : ℕ) : ℤ)) = v := by ring
      rwa [h9] at h8
    · have hmul : r (some k) * (r (some j))⁻¹
          = mapGL ℝ (heckeTMat (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
        rw [hrsome, hrsome, ← map_inv, ← map_mul, heckeTMat_inv, heckeTMat_mul,
          ← sub_eq_add_neg]
      rw [hmul] at h
      have hd := (hGpiff _ (heckeTMat_mem_Gamma0 M _)).mp h
      have hd' : (q : ℤ) ∣ ((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by simpa [heckeTMat] using hd
      obtain ⟨t, ht⟩ := hd'
      have hjq : ((j : ℕ) : ℤ) < q := by exact_mod_cast j.isLt
      have hkq : ((k : ℕ) : ℤ) < q := by exact_mod_cast k.isLt
      have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
      have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
      have h1 : t < 1 := by
        by_contra hcon
        have hcon' : (1 : ℤ) ≤ t := not_lt.mp hcon
        have h2 : (q : ℤ) * 1 ≤ q * t := mul_le_mul_of_nonneg_left hcon' hqpos.le
        linarith
      have h3 : -1 < t := by
        by_contra hcon
        have hcon' : t ≤ -1 := not_lt.mp hcon
        have h4 : (q : ℤ) * t ≤ q * (-1) := mul_le_mul_of_nonneg_left hcon' hqpos.le
        linarith
      have ht0 : t = 0 := by omega
      rw [ht0, mul_zero] at ht
      have hjk : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) := by linarith
      exact congrArg some (Fin.ext (by exact_mod_cast hjk))
  -- entries of a `Γ'`-element: `ρ = [a, qb; Mc, d]`.
  have hentries : ∀ γ ∈ Gp, ∃ (ρ : SL(2, ℤ)) (a b c d : ℤ),
      mapGL ℝ ρ = γ ∧ ρ ∈ Gamma0 M ∧
      (ρ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (q : ℤ) * b; (M : ℤ) * c, d] := by
    intro γ hγ
    obtain ⟨ρ, hρ, hρeq⟩ := mem_Gamma0GL_iff.mp (hGpΓ hγ)
    have hb : (q : ℤ) ∣ ρ 0 1 := (hGpiff ρ hρ).mp (by rw [hρeq]; exact hγ)
    have hc : ((M : ℤ)) ∣ ρ 1 0 := by
      have hg := hρ
      rw [CongruenceSubgroup.Gamma0_mem] at hg
      rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨b, hbe⟩ := hb
    obtain ⟨c, hce⟩ := hc
    refine ⟨ρ, ρ 0 0, b, c, ρ 1 1, hρeq, hρ, ?_⟩
    conv_lhs => rw [Matrix.eta_fin_two (ρ : Matrix (Fin 2) (Fin 2) ℤ)]
    rw [hbe, hce]
  -- `η = W α` NORMALIZES `Γ'` — both inclusions, each inverse-free.
  set etaW : GL (Fin 2) ℝ := mapGL ℝ W * heckeRep q 0 with hetaW
  have hN1 : ∀ γ ∈ Gp, etaW * γ * etaW⁻¹ ∈ Gp := by
    intro γ hγ
    obtain ⟨ρ, a, b, c, d, hρeq, hρmem, hρmat⟩ := hentries γ hγ
    have hdetρ : a * d - (q : ℤ) * b * ((M : ℤ) * c) = 1 := by
      have h2 := ρ.2
      rw [hρmat, Matrix.det_fin_two_of] at h2
      exact h2
    have hdetε : Matrix.det !![a, b; (q : ℤ) * ((M : ℤ) * c), d] = 1 := by
      rw [Matrix.det_fin_two_of]; linear_combination hdetρ
    set ε : SL(2, ℤ) := ⟨!![a, b; (q : ℤ) * ((M : ℤ) * c), d], hdetε⟩ with hε
    have hαρ : heckeRep q 0 * mapGL ℝ ρ = mapGL ℝ ε * heckeRep q 0 :=
      heckeRep_zero_mul_mapGL_comm hq0 hρmat (by rw [hε])
    have hεmem : ε ∈ Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem, hε]
      show (((q : ℤ) * ((M : ℤ) * c) : ℤ) : ZMod M) = 0
      push_cast
      simp
    have hconj : etaW * γ * etaW⁻¹ = mapGL ℝ (W * ε * W⁻¹) := by
      rw [map_mul, map_mul, map_inv, hetaW, ← hρeq]
      calc mapGL ℝ W * heckeRep q 0 * mapGL ℝ ρ * (mapGL ℝ W * heckeRep q 0)⁻¹
          = mapGL ℝ W * (heckeRep q 0 * mapGL ℝ ρ) * (heckeRep q 0)⁻¹ * (mapGL ℝ W)⁻¹ := by
            rw [mul_inv_rev]; group
        _ = mapGL ℝ W * (mapGL ℝ ε * heckeRep q 0) * (heckeRep q 0)⁻¹ * (mapGL ℝ W)⁻¹ := by
            rw [hαρ]
        _ = mapGL ℝ W * mapGL ℝ ε * (mapGL ℝ W)⁻¹ := by group
    rw [hconj]
    refine (hGpiff _ (mul_mem (mul_mem hWmem hεmem) (inv_mem hWmem))).mpr ?_
    have hval : (W * ε * W⁻¹) 0 1
        = (q : ℤ) * (-(u * v * a) - v ^ 2 * ((M : ℤ) * c) + u ^ 2 * q * b + u * v * d) := by
      simp [Matrix.SpecialLinearGroup.coe_mul, hW, hε, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring
    rw [hval]
    exact dvd_mul_right _ _
  have hN2 : ∀ γ ∈ Gp, etaW⁻¹ * γ * etaW ∈ Gp := by
    intro γ hγ
    obtain ⟨ρ, a, b, c, d, hρeq, hρmem, hρmat⟩ := hentries γ hγ
    set kk : ℤ := -(u * M * a) + u ^ 2 * q * ((M : ℤ) * c) - (M : ℤ) ^ 2 * b + u * M * d
      with hkk
    set ε₂ : SL(2, ℤ) := W⁻¹ * ρ * W with hε₂
    have hε₂mem : ε₂ ∈ Gamma0 M := mul_mem (mul_mem (inv_mem hWmem) hρmem) hWmem
    have hε₂10 : (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (q : ℤ) * kk := by
      rw [hε₂, hkk]
      simp [Matrix.SpecialLinearGroup.coe_mul, hW, hρmat, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring
    have hdet2 : (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        - (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((q : ℤ) * kk) = 1 := by
      have h2 := ε₂.2
      rw [Matrix.det_fin_two] at h2
      rw [← hε₂10]
      exact h2
    have hdet3 : Matrix.det !![(ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
        (q : ℤ) * (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        kk, (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1] = 1 := by
      rw [Matrix.det_fin_two_of]; linear_combination hdet2
    set ρ'' : SL(2, ℤ) := ⟨!![(ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
      (q : ℤ) * (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      kk, (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], hdet3⟩ with hρ''
    have hε₂mat : (ε₂ : Matrix (Fin 2) (Fin 2) ℤ)
        = !![(ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
            (q : ℤ) * kk, (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := by
      conv_lhs => rw [Matrix.eta_fin_two (ε₂ : Matrix (Fin 2) (Fin 2) ℤ)]
      rw [hε₂10]
    have hαρ'' : heckeRep q 0 * mapGL ℝ ρ'' = mapGL ℝ ε₂ * heckeRep q 0 :=
      heckeRep_zero_mul_mapGL_comm hq0 (by rw [hρ'']) hε₂mat
    have hmapε₂ : mapGL ℝ ε₂ = (mapGL ℝ W)⁻¹ * mapGL ℝ ρ * mapGL ℝ W := by
      rw [hε₂, map_mul, map_mul, map_inv]
    have hconj : etaW⁻¹ * γ * etaW = mapGL ℝ ρ'' := by
      have h1 : heckeRep q 0 * (etaW⁻¹ * γ * etaW) = mapGL ℝ ε₂ * heckeRep q 0 := by
        rw [hmapε₂, hetaW, ← hρeq]
        group
      rw [← hαρ''] at h1
      exact mul_left_cancel h1
    have hMkk : ((M : ℤ)) ∣ kk := by
      rw [hkk]
      exact ⟨-(u * a) + u ^ 2 * q * c - (M : ℤ) * b + u * d, by ring⟩
    rw [hconj]
    refine (hGpiff _ ?_).mpr ?_
    · rw [CongruenceSubgroup.Gamma0_mem, hρ'']
      show ((kk : ℤ) : ZMod M) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hMkk
    · rw [hρ'']
      show (q : ℤ) ∣ (q : ℤ) * (ε₂ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      exact dvd_mul_right _ _
  obtain ⟨hUm, hUvol, hUcov, hUdisj, hUpw⟩ :=
    smulDomain_of_cosetReps hGpΓ hnegGp hDmeas hDvol hcov hdisj r hrΓ hfind hinj
  obtain ⟨hVcov, hVdisj⟩ := smulDomain_smul_of_normalizes hN1 hN2 hUcov hUdisj
  have hint : ∀ E : Set ℍ, volume E ≠ ⊤ →
      IntegrableOn (petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0)) E volume := by
    intro E hE
    have h := peterssonIntegrableOn_slash hM hE f g
      (by simp : (0 : ℝ) < (1 : GL (Fin 2) ℝ).det.val) (det_heckeRep_pos hq 0)
    rwa [SlashAction.slash_one (2 : ℤ) ⇑g] at h
  have hadditive : ∀ s : Option (Fin q) → Set ℍ, (∀ o, MeasurableSet (s o)) →
      Pairwise (Function.onFun (AEDisjoint volume) s) →
      IntegrableOn (petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0)) (⋃ o, s o) volume →
      (∫ τ in ⋃ o, s o, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = ∑ o, ∫ τ in s o, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
    intro s hm hd hi
    rw [integral_iUnion_ae (fun o => (hm o).nullMeasurableSet) hd hi, tsum_fintype]
  have hWΓ : mapGL ℝ W ∈ Gamma0GL M := mem_Gamma0GL_iff.mpr ⟨W, hWmem, rfl⟩
  -- `H ∘ W = L`, in the form `f∣(αW) = f∣α'`.
  have hslashW : (⇑f ∣[(2 : ℤ)] (heckeRep q 0 * mapGL ℝ W)) = ⇑f ∣[(2 : ℤ)] heckeRepInf q := by
    rw [hkey, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ Dz)
        (mem_Gamma0GL_iff.mpr ⟨Dz, hDzmem, rfl⟩)]
  have hWmove : ∀ S : Set ℍ,
      (∫ τ in (mapGL ℝ W) • S, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = ∫ τ in S, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
    intro S
    rw [← setIntegral_petersson_slash_mul_right f g (heckeRep q 0) hWΓ S, hslashW]
  -- `W D₀ ∈ Γ'` (lower-left `M(u+1)`, upper-right `vq(u+1)`).
  have hWDzGp : mapGL ℝ (W * Dz) ∈ Gp := by
    refine (hGpiff _ (mul_mem hWmem hDzmem)).mpr ?_
    have hval : (W * Dz) 0 1 = (q : ℤ) * (v * (u + 1)) := by
      rw [SL2_mul_apply_zero_one]
      simp [hW, hDz]
      ring
    rw [hval]
    exact dvd_mul_right _ _
  have hWDzΓ : mapGL ℝ (W * Dz) ∈ Gamma0GL M := hGpΓ hWDzGp
  have hslashWDz : (⇑f ∣[(2 : ℤ)] (heckeRep q 0 * mapGL ℝ (W * Dz)))
      = ⇑f ∣[(2 : ℤ)] heckeRep q 0 := by
    have hc := hGpconj _ hWDzGp
    have hrw : heckeRep q 0 * mapGL ℝ (W * Dz)
        = heckeRep q 0 * mapGL ℝ (W * Dz) * (heckeRep q 0)⁻¹ * heckeRep q 0 := by group
    rw [hrw, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ hc]
  have hWDzmove : ∀ S : Set ℍ,
      (∫ τ in (mapGL ℝ (W * Dz)) • S, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = ∫ τ in S, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
    intro S
    rw [← setIntegral_petersson_slash_mul_right f g (heckeRep q 0) hWDzΓ S, hslashWDz]
  have hVeq : etaW • (⋃ o, r o • D) = ⋃ o, (etaW * r o) • D := by
    rw [Set.smul_set_iUnion]
    exact Set.iUnion_congr fun o => by rw [smul_smul]
  have hVpw : Pairwise (Function.onFun (AEDisjoint volume) (fun o => (etaW * r o) • D)) := by
    intro o p hop
    show volume (((etaW * r o) • D) ∩ ((etaW * r p) • D)) = 0
    have hrw : ((etaW * r o) • D) ∩ ((etaW * r p) • D) = etaW • ((r o • D) ∩ (r p • D)) := by
      rw [Set.smul_set_inter, smul_smul, smul_smul]
    rw [hrw, measure_smul]
    exact hUpw hop
  have hVm : MeasurableSet (etaW • (⋃ o, r o • D)) := hsm _ _ hUm
  have hVvol : volume (etaW • (⋃ o, r o • D)) ≠ ⊤ := by rw [measure_smul]; exact hUvol
  have htilenone : etaW * r none = mapGL ℝ (W * Dz) * heckeRepInf q := by
    rw [hrnone, hetaW, mul_assoc, hkey, ← mul_assoc, ← map_mul]
  have htilesome : ∀ j : Fin q,
      etaW * r (some j) = mapGL ℝ W * (heckeRep q 0 * mapGL ℝ (heckeTMat ((j : ℕ) : ℤ))) := by
    intro j
    rw [hrsome, hetaW, mul_assoc]
  refine ⟨Gp, ⋃ o, r o • D, etaW • (⋃ o, r o • D), ?_, ?_, hUm, hUvol, hUcov, hUdisj,
    hVm, hVvol, hVcov, hVdisj, ?_, ?_⟩
  · haveI hcountSL : Countable SL(2, ℤ) := by
      have hinjc : Function.Injective
          (fun A : SL(2, ℤ) => (fun i j => (A : Matrix (Fin 2) (Fin 2) ℤ) i j :
            Fin 2 → Fin 2 → ℤ)) := by
        intro A B hAB
        refine Subtype.ext ?_
        ext i k
        exact congrFun (congrFun hAB i) k
      exact hinjc.countable
    have hc : (Gamma0GL M : Set (GL (Fin 2) ℝ)).Countable := by
      refine Set.Countable.mono (fun x hx => ?_)
        (Set.countable_range (fun δ : SL(2, ℤ) => mapGL ℝ δ))
      obtain ⟨δ, -, hδ⟩ := mem_Gamma0GL_iff.mp hx
      exact ⟨δ, hδ⟩
    exact (Set.Countable.mono (fun x hx => hGpΓ hx) hc).to_subtype
  · intro γ hγ
    exact ⟨hGpΓ hγ, hGpconj γ hγ⟩
  · rw [hadditive _ (fun o => hsm _ _ hDmeas) hUpw (hint _ hUvol), Fintype.sum_option,
      hrnone, hWmove D]
    have hsum : (∑ j : Fin q,
          ∫ τ in r (some j) • D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = ∑ j ∈ Finset.range q, ∫ τ in (mapGL ℝ (heckeTMat (j : ℤ))) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => by rw [hrsome]
    rw [hsum]
    exact add_comm _ _
  · rw [hVeq, hadditive _ (fun o => hsm _ _ hDmeas) hVpw
      (by rw [← hVeq]; exact hint _ hVvol), Fintype.sum_option, htilenone, ← smul_smul,
      hWDzmove]
    have hsum : (∑ j : Fin q,
          ∫ τ in (etaW * r (some j)) • D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        = ∑ j ∈ Finset.range q,
            ∫ τ in (heckeRep q 0 * mapGL ℝ (heckeTMat (j : ℤ))) • D,
              petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htilesome, ← smul_smul, hWmove]
    rw [hsum]
    exact add_comm _ _

end GammaPrimeTiling

/-- **THE α-TILING IDENTITY** (PROVEN 2026-07-27 over
`setIntegral_eq_of_smulDomain_of_invariant` and `exists_gammaPrimeTiling`
above): the unfolding identity after every slash has been normalised onto the
single pair `α = heckeRep q 0`, `α' = heckeRepInf q`, so that the only
remaining content is the tiling of a `Γ'`-fundamental domain by the `q + 1`
translates `T^j • D` and `D`.

Both sides are `∫` of `petersson 2 g (f∣α)` over a `Γ'`-domain: the left over
`U = ⊔_j T^j • D ⊔ W • D`, the right over `η • U` with `η = Wα` — the two
domains are genuinely DIFFERENT, which is why the comparison lemma above, and
not mere additivity, is the crux. -/
theorem setIntegral_alphaTiling {M : ℕ} (hM : 0 < M)
    {D : Set ℍ} (hDvol : volume D ≠ ⊤) (hDmeas : MeasurableSet D)
    (hcov : ∀ τ : ℍ, ∃ γ ∈ Gamma0GL M, γ • τ ∈ D)
    (hdisj : ∀ γ ∈ Gamma0GL M, γ ≠ 1 → γ ≠ -1 → volume ((γ • D) ∩ D) = 0)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (f g : CuspForm (Gamma0GL M) 2) :
    ((∑ j ∈ Finset.range q, ∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat j)) • D,
        petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ)
        + ∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ)
      = (∑ j ∈ Finset.range q, ∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat j)) • D,
            petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q 0) ⇑f τ)
        + ∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRepInf q) ⇑f τ := by
  classical
  obtain ⟨G, U, V, hGc, hGmem, hUm, hUvol, hUcov, hUdisj, hVm, hVvol, hVcov, hVdisj,
    hUval, hVval⟩ := exists_gammaPrimeTiling hM hDvol hDmeas hcov hdisj hq hqM f g
  -- Move the `α`-slash across the pairing on the right-hand side.
  have hswapR : ∀ (E : Set ℍ),
      (∫ τ in E, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q 0) ⇑f τ)
        = ∫ τ in (heckeRep q 0) • E,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
    intro E
    rw [setIntegral_petersson_slash_adjoint ⇑g ⇑f (det_heckeRep_pos hq 0) E,
      slash_heckeRep_zero_inv ⇑f hq]
  have hswapRinf : ∀ (E : Set ℍ),
      (∫ τ in E, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRepInf q) ⇑f τ)
        = ∫ τ in (heckeRepInf q) • E,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
    intro E
    rw [setIntegral_petersson_slash_adjoint ⇑g ⇑f (det_heckeRepInf_pos hq) E,
      slash_heckeRepInf_inv ⇑f hq]
  have hVrw : ∀ j : ℕ,
      (∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat (j : ℤ))) • D,
          petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q 0) ⇑f τ)
        = ∫ τ in (heckeRep q 0 * Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat (j : ℤ))) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
    intro j
    rw [hswapR, mul_smul]
  rw [Finset.sum_congr rfl (fun j _ => hVrw j), hswapRinf, ← hUval, ← hVval]
  -- Integrability of the common integrand on both tilings.
  have hint : ∀ E : Set ℍ, volume E ≠ ⊤ →
      IntegrableOn (petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0)) E volume := by
    intro E hE
    have h := peterssonIntegrableOn_slash hM hE f g
      (by simp : (0 : ℝ) < (1 : GL (Fin 2) ℝ).det.val) (det_heckeRep_pos hq 0)
    rwa [SlashAction.slash_one (2 : ℤ) ⇑g] at h
  -- `Γ'`-invariance of the integrand.
  have hHinv : ∀ γ ∈ G, ∀ τ : ℍ,
      petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) (γ • τ)
        = petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
    intro γ hγ τ
    obtain ⟨hγΓ, hconj⟩ := hGmem γ hγ
    have hpos : 0 < γ.det.val := by
      rw [Subgroup.HasDetOne.det_eq hγΓ]; norm_num
    have hgs : ⇑g ∣[(2 : ℤ)] γ = ⇑g := SlashInvariantFormClass.slash_action_eq g γ hγΓ
    have hfs : (⇑f ∣[(2 : ℤ)] heckeRep q 0) ∣[(2 : ℤ)] γ
        = ⇑f ∣[(2 : ℤ)] heckeRep q 0 := by
      rw [← SlashAction.slash_mul]
      conv_lhs => rw [show heckeRep q 0 * γ
        = (heckeRep q 0 * γ * (heckeRep q 0)⁻¹) * heckeRep q 0 by group]
      rw [SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq f _ hconj]
    rw [← petersson_slash_two ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) hpos τ, hgs, hfs]
  exact setIntegral_eq_of_smulDomain_of_invariant hGc hUm hVm hUcov hUdisj hVcov hVdisj
    (hint U hUvol) (hint V hVvol) hHinv

/-- **THE UNFOLDING IDENTITY** (PROVEN 2026-07-27 over `setIntegral_alphaTiling`
above, itself proven over `setIntegral_eq_of_smulDomain_of_invariant` and the
coset tiling `exists_gammaPrimeTiling`, which is now PROVEN too; cut 2026-07-27 out of
`peterssonSelfAdjoint_of_gamma0FundamentalDomain` below, which is PROVEN over
it and over `peterssonIntegrableOn_slash`): ALL of the remaining content of
Diamond–Shurman Theorem 5.5.3, and the only place the fundamental-domain
hypotheses `hcov`/`hdisj` and the good-prime hypothesis `hqM` are consumed.

The analytic reduction is DONE: the assembly below expands `T_q` into its
`q + 1` explicit representatives, splits the integral, and applies
`setIntegral_petersson_slash_adjoint` to each right-hand term.  What survives
is exactly this: the SAME `q + 1` integrands, integrated over `D` on the left
and over the TRANSLATES `δ • D` on the right.

WHY IT IS TRUE (D–S §5.5, and this is the classical argument in the shape the
statement now has).  Write `Γ = Γ₀(M)`, `α = [1,0;0,q]`, `Γ' = Γ ∩ α⁻¹Γα`, and
`Γ = ⊔_i Γ'γ_i`, so that the `q + 1` representatives are `δ_i = αγ_i` and
`petersson 2 g (f∣α)` is `Γ'`-invariant.  Then `⊔_i γ_i D` is a fundamental
domain for `Γ'`, and both sides compute the integral of that `Γ'`-invariant
function over it — the left side by summing translates of `D`, the right side
by summing over the `δ • D`.  The passage between the two families of
representatives is `α' = det(α)·α⁻¹ = [q,0;0,1]` together with `α' ∈ ΓαΓ`,
which holds because `qu − Mv = 1` is solvable EXACTLY when `q ∤ M`
(`α' = γ₁ α γ₂` with `γ₁ = [q,v;M,u]`, `γ₂ = [uq,−v;−M,1]`, both of
determinant `1` with lower-left divisible by `M`).  Classically: the diamond
operator `⟨q⟩` is the identity at weight 2 with trivial character.

WHAT THE PIN ALREADY SUPPLIES FOR THIS, which is more than the earlier audit
recorded.  The coset enumeration this argument needs is ALREADY CARRIED OUT in
this file, inside the proof of `exists_cuspForm_heckeTransform` (§HeckeStability
above): `heckeRep_conj_mem_iff` is the divisibility criterion `α ρ α⁻¹ ∈ Γ₀(N)
↔ q ∣ ρ₀₁`, `heckeConj_isFiniteRelIndex` gives finiteness of
`Γ₀(N) ⧸ (Γ₀(N) ∩ α⁻¹Γ₀(N)α)`, and the `have`s `hcrit`/`hEval`/`hEinj`/`hfind`
there enumerate that coset space by the `q` translations `[1,j;0,1]`.  A prover
attacking this leaf should HOIST those `have`s to top-level lemmas rather than
redo them — that is the single largest piece of reusable work available here.

WHAT IS GENUINELY MISSING is the measure-theoretic half: `⊔_i γ_i D` is a
`Γ'`-fundamental domain, and the integral of a `Γ'`-invariant function over it
is the sum of the integrals over the `γ_i D`.  Note this CANNOT be phrased
through `MeasureTheory.IsFundamentalDomain` — `−1` acts trivially on `ℍ`, so
that class is unsatisfiable here for any set of positive measure (see the
discussion on `volume_smul_inter_gamma0Domain_eq_zero` above), which is why
`hcov`/`hdisj` appear as hand-rolled conjuncts.

FAITHFULNESS.  This leaf is EQUIVALENT to the consumer given
`peterssonIntegrableOn_slash`: the assembly below derives the consumer from it
by proven equalities only, so it can be neither weaker nor stronger, and it
carries every hypothesis of the consumer.  In particular `hqM` is
LOAD-BEARING and the identity is FALSE at `q ∣ M`.

**MEASURABILITY AUDIT (2026-07-27) — WHY `hDmeas` WAS ADDED, with the explicit
construction that forces it.**  `hcov`/`hdisj`/`hDvol` alone do NOT make `D`
behave like a fundamental domain, because for a NON-measurable `D` the
hypothesis `hdisj` is not an invariant of `volume.restrict D` — which is the
only thing the conclusion sees.  Concretely, let `𝒟` be mathlib's standard
domain, let `V ⊆ 𝒟` be a Vitali-style set of inner measure `0` and outer
measure `volume 𝒟`, fix `γ₀ ∈ Γ₀(M)`, `γ₀ ≠ ±1`, and put

  `D = (𝒟 \ V) ∪ γ₀ • V`.

Then `D` satisfies `hDvol`, `hcov` (it contains a transversal: `z ∈ 𝒟 \ V`
stays, `z ∈ V` is moved by `γ₀`) and `hdisj` (every cross term is contained in
`γ 𝒟 ∩ 𝒟` for some `γ ≠ ±1`, or is literally empty by `V ∩ (𝒟 \ V) = ∅`).
Yet outer measure is superadditive across the two non-measurable pieces, so
`volume.restrict D = volume.restrict (𝒟 ∪ γ₀ • 𝒟)` and `∫_D H = 2 ∫_𝒟 H` for
every `Γ₀(M)`-invariant `H` — twice a fundamental-domain integral, from a set
that satisfies every hypothesis.  (The CONCLUSION survives this, both sides
being scaled by the same `2`; what does not survive is any proof route through
"`D` is a.e. a fundamental domain", and in particular the natural auxiliary
lemma *"any two such `D` give the same integral of a `Γ₀(M)`-invariant
function"* is FALSE — `𝒟` itself is another such set and gives half.)

So `hDmeas` is not a convenience: without it every measure-theoretic step
below (a.e.-disjoint additivity, `Measure.restrict_iUnion₀`, all of which need
at least `NullMeasurableSet`) is unavailable, and the pathological `D` above is
a live counterexample to the natural reduction.  It costs the consumer nothing:
`measurableSet_gamma0Domain` above discharges it for the only witness ever used.

**ROUTE AUDIT (2026-07-27, SUPERSEDED AND CORRECTED — the leaf is now PROVEN;
kept because its step 4 UNDERSTATED the crux and the correction is what a
prover at `exists_gammaPrimeTiling` needs).**

The earlier version of this audit listed four steps and called step 4
"`⊔_i γ_i • D` is a `Γ'`-domain and the integral of a `Γ'`-invariant function
over it is `Σ_i ∫_{γ_i • D}`", i.e. FINITE ADDITIVITY.  That is true and easy,
and it is NOT what was missing.  Carrying the reduction out shows that after
steps 1–3 the identity reads

  `∫_U H = ∫_{η • U} H`,  `H = petersson 2 g (f∣α)`,  `η = W·α`,

where `U = ⊔_{j<q} T^j • D ⊔ W • D` is a `Γ'`-domain, `η` NORMALIZES `Γ'`, and
`η • U` is therefore a SECOND, genuinely different `Γ'`-domain.  So the crux is
the comparison of TWO `Γ'`-domains — the general lemma
`setIntegral_eq_of_smulDomain_of_invariant` above, now proven — and not
additivity.  An agent who had implemented only step 4 as written would have
found the goal unchanged.

The four steps, as actually realised in the proof below:

1. (PROVEN, `setIntegral_petersson_slash_adjoint` backwards) each right-hand
   term folds onto `D`: `∫_{δ•D} petersson 2 g (f∣δ⁻¹) = ∫_D petersson 2 (g∣δ) f`.
2. (PROVEN, `setIntegral_petersson_slash_mul_right`/`_left`) `δ_j = α·T^j` with
   `T^j ∈ Γ₀(M)`, so every slash normalises onto the single pair `α`, `α'` and
   the `T^j` move onto the domain.  This is `setIntegral_alphaTiling`'s
   statement.
3. (PROVEN, `slash_two_of_coe_eq_smul_one`) at weight `2` scalars act trivially,
   so `α⁻¹` is the INTEGRAL adjugate `α' = det(α)·α⁻¹ = heckeRepInf q`
   (`slash_heckeRep_zero_inv`, `slash_heckeRepInf_inv`).
4. (PROVEN 2026-07-27, `exists_gammaPrimeTiling`) the group theory and the
   finite additivity: `U` and `η • U` are `Γ'`-domains and the two tilings
   compute the two sides.  See that node's docstring for the explicit
   witnesses — `Γ'`, the Bézout matrices `W`, `D₀`, the normalising `η = Wα`
   and its conjugation formula — all of which are recorded there in full, and
   the two general lemmas `smulDomain_of_cosetReps` /
   `smulDomain_smul_of_normalizes` above it, which carry the tiling argument.

The arithmetic input `α' ∈ ΓαΓ` is `qu − Mv = 1`, solvable exactly at `q ∤ M`
— which is where `hqM` enters and why the identity fails at `q ∣ M`. -/
theorem setIntegral_heckeRep_unfold {M : ℕ} (hM : 0 < M)
    {D : Set ℍ} (hDvol : volume D ≠ ⊤) (hDmeas : MeasurableSet D)
    (hcov : ∀ τ : ℍ, ∃ γ ∈ Gamma0GL M, γ • τ ∈ D)
    (hdisj : ∀ γ ∈ Gamma0GL M, γ ≠ 1 → γ ≠ -1 → volume ((γ • D) ∩ D) = 0)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (f g : CuspForm (Gamma0GL M) 2) :
    ((∑ j ∈ Finset.range q,
        ∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q j) τ)
        + ∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ)
      = (∑ j ∈ Finset.range q, ∫ τ in (heckeRep q j) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (heckeRep q j)⁻¹) τ)
        + ∫ τ in (heckeRepInf q) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (heckeRepInf q)⁻¹) τ := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hTmem : ∀ j : ℕ, Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat (j : ℤ)) ∈ Gamma0GL M := fun j =>
    mem_Gamma0GL_iff.mpr ⟨heckeTMat (j : ℤ), heckeTMat_mem_Gamma0 M _, rfl⟩
  -- Fold the right-hand terms back onto `D` (D–S 5.5.2, run backwards).
  have hR : ∀ δ : GL (Fin 2) ℝ, 0 < δ.det.val →
      (∫ τ in δ • D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] δ⁻¹) τ)
        = ∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] δ) ⇑f τ :=
    fun δ hδ => (setIntegral_petersson_slash_adjoint ⇑g ⇑f hδ D).symm
  rw [hR _ (det_heckeRepInf_pos hq),
    Finset.sum_congr rfl (fun j _ => hR _ (det_heckeRep_pos hq j))]
  -- Split each finite representative as `α · T^j` and move `T^j` onto the domain.
  have hLj : ∀ j ∈ Finset.range q,
      (∫ τ in D, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q j) τ)
        = ∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat (j : ℤ))) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q 0) τ := by
    intro j _
    rw [← heckeRep_zero_mul_heckeTMat hq0 j,
      setIntegral_petersson_slash_mul_right f g (heckeRep q 0) (hTmem j) D]
  have hRj : ∀ j ∈ Finset.range q,
      (∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q j) ⇑f τ)
        = ∫ τ in (Matrix.SpecialLinearGroup.mapGL ℝ (heckeTMat (j : ℤ))) • D,
            petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q 0) ⇑f τ := by
    intro j _
    rw [← heckeRep_zero_mul_heckeTMat hq0 j,
      setIntegral_petersson_slash_mul_left f g (heckeRep q 0) (hTmem j) D]
  rw [Finset.sum_congr rfl hLj, Finset.sum_congr rfl hRj]
  exact setIntegral_alphaTiling hM hDvol hDmeas hcov hdisj hq hqM f g

/-- **SELF-ADJOINTNESS OF THE GOOD HECKE OPERATORS OVER A `Γ₀(M)` FUNDAMENTAL
DOMAIN** (PROVEN 2026-07-27 over the two leaves `peterssonIntegrableOn_slash`
and `setIntegral_heckeRep_unfold` above; cut 2026-07-26 out of
`exists_peterssonDomain` below;
Diamond–Shurman *A First Course in Modular Forms* §5.5, Theorem 5.5.3, and
Shimura, *Introduction to the arithmetic theory of automorphic functions*, for
the double-coset computation): over ANY set `D` of finite volume that covers
`ℍ` under `Γ₀(M)` and is a.e.-disjoint from its nontrivial `Γ₀(M)`-translates,
the Petersson integrand pairs `T_q` self-adjointly at every good prime `q ∤ M`.

This is the whole analytic content that survives the cut: `exists_peterssonDomain`
below supplies the domain (`gamma0Domain M`, whose finite volume, interior and
covering property are PROVEN above and whose a.e.-disjointness is the sibling
leaf `volume_smul_inter_gamma0Domain_eq_zero`), and everything the Petersson
product needs BEYOND self-adjointness — integrability, additivity, homogeneity,
conjugate symmetry and DEFINITENESS — is proven below from finite volume and
interior alone.

WHAT THE PIN SUPPLIES (checked 2026-07-26):

* `Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean` — the INVARIANT
  measure `dx dy / y²` as `(volume : Measure ℍ)`, with the instance
  `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume`.  The change of variables is
  therefore DONE;
* `Mathlib/NumberTheory/ModularForms/Petersson.lean` — `petersson_slash`,
  the full `GL₂⁺` transformation law
  `petersson k (f∣γ) (f'∣γ) τ = |det γ|^{k-2} · σ γ (petersson k f f' (γ • τ))`.
  **At `k = 2` the determinant factor is `|det γ|⁰ = 1`**, and `σ γ = id` for
  `det γ > 0`, so the law degenerates to the clean
  `petersson 2 (f∣γ) (f'∣γ) τ = petersson 2 f f' (γ • τ)`.  That is the single
  identity the whole unfolding runs on, and weight `2` is exactly the weight at
  which it is free of determinant bookkeeping;
* `heckeTransform`/`heckeOp_coe` above — `T_q f = Σ_{j<q} f∣[1,j;0,q] + f∣[q,0;0,1]`
  at `q ∤ M`, with the representatives explicit.

PROOF PLAN (reconstructed 2026-07-26; D–S Thm 5.5.3).  Write `Γ = Γ₀(M)`,
`α = [1,0;0,q]`, `Γ' = Γ ∩ α⁻¹Γα`, and `Γ = ⊔_i Γ' γ_i`, so that
`T_q f = Σ_i (f∣α)∣γ_i`.  Three steps, each a change of variables under the
invariant measure:

1. FOLD UP.  For `γ ∈ Γ`, `petersson 2 g (h∣γ) = petersson 2 (g∣γ) (h∣γ)
   = (petersson 2 g h) ∘ γ`, so `∫_D petersson 2 g ((f∣α)∣γ_i) = ∫_{γ_i D}
   petersson 2 g (f∣α)`; and `petersson 2 g (f∣α)` is `Γ'`-invariant, so the sum
   over `i` is `∫_{D'} petersson 2 g (f∣α)` for `D' = ⊔_i γ_i D`, a fundamental
   domain for `Γ'`.  (This is where the covering and a.e.-disjointness
   hypotheses are consumed, via additivity of the integral over an essentially
   disjoint union.)
2. MOVE BY `α`.  `petersson 2 g (f∣α) = petersson 2 (g∣α⁻¹) f ∘ α`, so the
   integral becomes `∫_{αD'} petersson 2 (g∣α⁻¹) f`, and `α D'` is a
   fundamental domain for `Γ'' = αΓα⁻¹ ∩ Γ`.  At weight `2` scalar matrices act
   trivially (`f∣(cI) = c^{k-2} f = f`), so `g∣α⁻¹ = g∣α'` with
   `α' = det(α)·α⁻¹ = [q,0;0,1]` INTEGRAL.
3. FOLD DOWN, AND `α' ∼ α`.  Running step 1 backwards for the double coset
   `Γα'Γ` returns `∫_D petersson 2 ([Γα'Γ] g) f`.  It remains that
   `[Γα'Γ] = [ΓαΓ] = T_q` on `S₂(Γ₀(M))`, which holds because `α' ∈ ΓαΓ`:
   with `qu − Mv = 1` (available exactly because `q ∤ M` — THIS is where the
   good-prime hypothesis enters, and the identity is false at `q ∣ M`),
   `α' = γ₁ α γ₂` with `γ₁ = [q,v;M,u]` and `γ₂ = [uq,−v;−M,1]`, both of
   determinant `1` with lower-left divisible by `M`, hence both in `Γ₀(M)`.
   Classically this last step is "the diamond operator `⟨q⟩` is the identity at
   weight 2 with trivial character".

FAITHFULNESS.  `hqM` is LOAD-BEARING (see the FAITHFULNESS AUDIT on the
consumer `heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level` below: at
`q ∣ M` the operator `U_q` is genuinely non-semisimple), and the `±1`
exclusions in `hdisj` are forced, not cosmetic — see
`volume_smul_inter_gamma0Domain_eq_zero` above. -/
theorem peterssonSelfAdjoint_of_gamma0FundamentalDomain {M : ℕ} (hM : 0 < M)
    {D : Set ℍ} (hDvol : volume D ≠ ⊤) (hDmeas : MeasurableSet D)
    (hcov : ∀ τ : ℍ, ∃ γ ∈ Gamma0GL M, γ • τ ∈ D)
    (hdisj : ∀ γ ∈ Gamma0GL M, γ ≠ 1 → γ ≠ -1 → volume ((γ • D) ∩ D) = 0)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (f g : CuspForm (Gamma0GL M) 2) :
    (∫ τ in D, petersson (2 : ℤ) ⇑g ⇑(heckeOp M q f) τ)
      = ∫ τ in D, petersson (2 : ℤ) ⇑(heckeOp M q g) ⇑f τ := by
  classical
  have hone : ∀ F : ℍ → ℂ, F ∣[(2 : ℤ)] (1 : GL (Fin 2) ℝ) = F := fun F =>
    SlashAction.slash_one (2 : ℤ) F
  have hdet1 : (0 : ℝ) < (1 : GL (Fin 2) ℝ).det.val := by simp
  -- Expand `T_q` into its `q + 1` explicit representatives, pointwise on each
  -- side.  `petersson` is additive in its second slot outright, and in its
  -- first slot because `conj` is additive.
  have hLpt : (fun τ : ℍ => petersson (2 : ℤ) ⇑g ⇑(heckeOp M q f) τ)
      = fun τ : ℍ =>
        (∑ j ∈ Finset.range q, petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q j) τ)
          + petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ := by
    funext τ
    rw [heckeOp_coe hM hq f]
    simp only [heckeTransform, if_neg hqM, petersson, Pi.add_apply, Finset.sum_apply,
      Finset.sum_mul, mul_add, add_mul, Finset.mul_sum]
  have hRpt : (fun τ : ℍ => petersson (2 : ℤ) ⇑(heckeOp M q g) ⇑f τ)
      = fun τ : ℍ =>
        (∑ j ∈ Finset.range q, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q j) ⇑f τ)
          + petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRepInf q) ⇑f τ := by
    funext τ
    rw [heckeOp_coe hM hq g]
    simp only [heckeTransform, if_neg hqM, petersson, Pi.add_apply, Finset.sum_apply,
      map_add, map_sum, Finset.sum_mul, add_mul]
  rw [hLpt, hRpt]
  -- Every term is integrable, so the two integrals split.
  have hintL : ∀ j ∈ Finset.range q,
      IntegrableOn (fun τ : ℍ => petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRep q j) τ)
        D volume := by
    intro j _
    have h := peterssonIntegrableOn_slash hM hDvol f g hdet1 (det_heckeRep_pos hq j)
    rwa [hone ⇑g] at h
  have hintLinf : IntegrableOn
      (fun τ : ℍ => petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] heckeRepInf q) τ) D volume := by
    have h := peterssonIntegrableOn_slash hM hDvol f g hdet1 (det_heckeRepInf_pos hq)
    rwa [hone ⇑g] at h
  have hintR : ∀ j ∈ Finset.range q,
      IntegrableOn (fun τ : ℍ => petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q j) ⇑f τ)
        D volume := by
    intro j _
    have h := peterssonIntegrableOn_slash hM hDvol f g (det_heckeRep_pos hq j) hdet1
    rwa [hone ⇑f] at h
  have hintRinf : IntegrableOn
      (fun τ : ℍ => petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRepInf q) ⇑f τ) D volume := by
    have h := peterssonIntegrableOn_slash hM hDvol f g (det_heckeRepInf_pos hq) hdet1
    rwa [hone ⇑f] at h
  rw [integral_add (integrable_finsetSum _ hintL) hintLinf,
    integral_add (integrable_finsetSum _ hintR) hintRinf,
    integral_finsetSum _ hintL, integral_finsetSum _ hintR]
  -- Move each slash on the right across the pairing (D–S 5.5.2).
  have hadjj : ∀ j ∈ Finset.range q,
      (∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRep q j) ⇑f τ)
        = ∫ τ in (heckeRep q j) • D,
            petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (heckeRep q j)⁻¹) τ :=
    fun j _ => setIntegral_petersson_slash_adjoint _ _ (det_heckeRep_pos hq j) D
  have hadjinf : (∫ τ in D, petersson (2 : ℤ) (⇑g ∣[(2 : ℤ)] heckeRepInf q) ⇑f τ)
      = ∫ τ in (heckeRepInf q) • D,
          petersson (2 : ℤ) ⇑g (⇑f ∣[(2 : ℤ)] (heckeRepInf q)⁻¹) τ :=
    setIntegral_petersson_slash_adjoint _ _ (det_heckeRepInf_pos hq) D
  rw [Finset.sum_congr rfl hadjj, hadjinf]
  -- What remains is exactly the coset tiling.
  exact setIntegral_heckeRep_unfold hM hDvol hDmeas hcov hdisj hq hqM f g

end PeterssonSlashAdjoint

/-- **THE PETERSSON DOMAIN** (PROVEN 2026-07-26; cut 2026-07-26 out of
`exists_peterssonProduct_selfAdjoint_heckeOp` below, which is PROVEN over it;
Diamond–Shurman §5.4–§5.5, Theorem 5.5.3): there is a set `D ⊆ ℍ` of FINITE
invariant volume, containing a nonempty open set, over which the Petersson
integrand pairs the good Hecke operators `T_q`, `q ∤ M`, self-adjointly.

The witness is `gamma0Domain M`, the union of the `[SL(2,ℤ) : Γ₀(M)]` translates
of mathlib's standard domain `𝒟`.  ALL THREE conjuncts are now proven here:
finite volume by `volume_gamma0Domain_ne_top` (over `volume_modularFd_ne_top`),
interior by `exists_open_subset_gamma0Domain`, and self-adjointness by
`peterssonSelfAdjoint_of_gamma0FundamentalDomain` applied through the covering
property `exists_mem_gamma0Domain` and the a.e.-disjointness
`volume_smul_inter_gamma0Domain_eq_zero` (PROVEN 2026-07-27).

CURRENT LEAF INVENTORY BELOW THIS NODE (2026-07-27, updated).  The whole
subtree is now PROVEN — `exists_gammaPrimeTiling` (the coset tiling, which is
where `hcov`, `hdisj` and `q ∤ M` are consumed) closed 2026-07-27 over the two
general lemmas `smulDomain_of_cosetReps` and `smulDomain_smul_of_normalizes`.
`setIntegral_heckeRep_unfold` itself is PROVEN, over that node and over
the general two-domain comparison
`setIntegral_eq_of_smulDomain_of_invariant` (also PROVEN — the
measure-theoretic core, which sidesteps
`MeasureTheory.IsFundamentalDomain`'s unsatisfiability at `−1` by indexing the
pieces over `Γ'/±` rather than over `Γ'`).  Its sibling
`peterssonIntegrableOn_slash` is PROVEN (the boundedness statement — `|g∣δ|·y`
equals `|g|·y` at another point, so the constant from
`CuspFormClass.petersson_bounded_left` is reused verbatim).  The geometry,
the measurability of the domain (`measurableSet_gamma0Domain`) and ALL of the
weight-2 analysis are done.  What `exists_gammaPrimeTiling` supplied is
pure group theory (`Γ' = Γ₀(M) ∩ Γ⁰(q)`, the Bézout matrices, and that
`η = Wα` normalizes `Γ'`) plus finite additivity over the tiles.

Everything ELSE that the Petersson product needs — integrability, additivity,
homogeneity, conjugate symmetry and DEFINITENESS — is proven below from the
first two conjuncts.

`~/cs/FLT` does NOT help: its only inner-product material,
`AutomorphicForm/QuaternionAlgebra/InnerProduct.lean`, is the definite
quaternionic setting where the "integral" is a finite sum over a class set.

FAITHFULNESS.  A degenerate witness cannot cheapen the consumer: the conclusion
of `exists_peterssonProduct_selfAdjoint_heckeOp` is UNCHANGED by this cut, and
definiteness of the resulting form is DERIVED below rather than assumed, so any
`D` satisfying these three conjuncts really does prove the consumer.  In
particular `D = ∅` is ruled out by the second conjunct. -/
theorem exists_peterssonDomain {M : ℕ} (hM : 0 < M) :
    ∃ D : Set ℍ,
      volume D ≠ ⊤ ∧
      (∃ U : Set ℍ, IsOpen U ∧ U.Nonempty ∧ U ⊆ D) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ M → ∀ f g : CuspForm (Gamma0GL M) 2,
        (∫ τ in D, petersson (2 : ℤ) ⇑g ⇑(heckeOp M q f) τ)
          = ∫ τ in D, petersson (2 : ℤ) ⇑(heckeOp M q g) ⇑f τ) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨gamma0Domain M, volume_gamma0Domain_ne_top M,
    exists_open_subset_gamma0Domain M, fun q hq hqM f g => ?_⟩
  exact peterssonSelfAdjoint_of_gamma0FundamentalDomain hM
    (volume_gamma0Domain_ne_top M) (measurableSet_gamma0Domain M)
    (exists_mem_gamma0Domain M)
    (fun γ hγ hne1 hne2 => volume_smul_inter_gamma0Domain_eq_zero hM hγ hne1 hne2)
    hq hqM f g

end Gamma0FundamentalDomain

/-- **THE PETERSSON PRODUCT ON `S₂(Γ₀(M))`, WITH THE GOOD HECKE
OPERATORS SELF-ADJOINT FOR IT** (PROVEN 2026-07-26 over the single leaf
`exists_peterssonDomain` above; cut 2026-07-26 out of
`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level`, which is PROVEN
over it; Diamond–Shurman *A First Course in Modular Forms* §5.5,
Theorem 5.5.3): there is a form `B` on `S₂(Γ₀(M))` that is additive and
`ℂ`-homogeneous in its first slot, conjugate-symmetric, DEFINITE, and
for which every GOOD Hecke operator `T_q`, `q ∤ M`, is self-adjoint.

This is the whole analytic content of the semisimplicity leaf; the
linear algebra that consumes it is
`eq_smul_of_pow_sub_smul_apply_eq_zero_of_selfAdjointForm`, PROVEN above.

WHY ONE EXISTENTIAL AND NOT TWO (anti-vacuity design note — read before
"simplifying" this). The tempting cut is "there is a definite Hermitian
form" plus "the Hecke operators are self-adjoint for it". The first half
is then TRIVIALLY TRUE and carries NO arithmetic — on a
finite-dimensional space (`cuspForm_finiteDimensional`, PROVEN above)
ANY basis manufactures a definite Hermitian form — and the second half,
quantified over a form obtained by `choice` from it, becomes FALSE.
Self-adjointness is a statement about the *Petersson* form specifically,
so the existential must bind the form ONCE and assert both properties of
the same `B`. The alternative honest cut is to DEFINE the form as an
integral, which needs a fundamental domain for `Γ₀(M)` (see below);
until that exists, this conjunction is the faithful shape.

CLASSICAL PROOF (the intended witness). `B f g = ⟨f, g⟩ =
∫_{Γ₀(M)\ℍ} f(τ) conj(g(τ)) y² dμ`, `dμ = dx dy / y²`, the Petersson
product. Convergence is the exponential decay of a cusp form at the
cusps, definiteness (indeed positivity, `⟨f, f⟩ > 0` for `f ≠ 0`) is
positivity of the integrand, and self-adjointness of `T_q` at `q ∤ M` is
D–S Theorem 5.5.3: for `α ∈ GL₂⁺(ℚ)` the Petersson adjoint of the
double-coset operator `[Γ₀(M) α Γ₀(M)]` is `[Γ₀(M) α' Γ₀(M)]` with
`α' = det(α)·α⁻¹`, and at `q ∤ M` this returns `⟨q⟩⁻¹T_q`, where the
diamond operator `⟨q⟩` is the IDENTITY on `S₂(Γ₀(M))` (weight 2, trivial
character). At `q ∣ M` the same computation gives no such identity, and
indeed `U_q` is genuinely non-semisimple — see the FAITHFULNESS AUDIT on
the consumer below, whose counterexample lives at `M = M'q³`.

PROOF (2026-07-26).  The form is the honest integral,
`B f g = ∫_D petersson 2 g f`, over the domain supplied by
`exists_peterssonDomain` above — so the "intended witness" is now written
in Lean rather than described in prose.  Of the five conjuncts, FOUR are
discharged here and only self-adjointness comes from the leaf:

* ADDITIVITY is `integral_add` over `peterssonIntegrableOn` (which needs
  only that `D` has finite volume);
* HOMOGENEITY is `integral_const_mul`, which holds UNCONDITIONALLY — no
  integrability hypothesis, since the Bochner integral of a
  non-integrable function is `0`;
* CONJUGATE SYMMETRY is `UpperHalfPlane.petersson_symm` followed by
  `integral_conj`, also unconditional;
* DEFINITENESS is `cuspForm_eq_zero_of_setIntegral_petersson_self_eq_zero`
  above — and the point of that lemma is that definiteness needs NO
  positivity of the product and NO fundamental-domain property, only that
  `D` has nonempty interior, because a holomorphic function vanishing a.e.
  on an open subset of the connected space `ℍ` vanishes identically.

That last item is why the leaf below is weaker than the "there is a
positive-definite inner product" statement one would expect: the analysis
that survives is exactly finite volume, interior, and the unfolding.

FORMAL-CONTENT NOTE. The consumer uses DEFINITENESS only (not
positivity) and does NOT use finite-dimensionality; both are stated
here at the weakest form that the argument consumes, so that the future
prover owes as little as possible. The witness of course satisfies the
stronger properties. -/
theorem exists_peterssonProduct_selfAdjoint_heckeOp {M : ℕ} (hM : 0 < M) :
    ∃ B : CuspForm (Gamma0GL M) 2 → CuspForm (Gamma0GL M) 2 → ℂ,
      (∀ f₁ f₂ g : CuspForm (Gamma0GL M) 2, B (f₁ + f₂) g = B f₁ g + B f₂ g) ∧
      (∀ (a : ℂ) (f g : CuspForm (Gamma0GL M) 2), B (a • f) g = a * B f g) ∧
      (∀ f g : CuspForm (Gamma0GL M) 2, B g f = starRingEnd ℂ (B f g)) ∧
      (∀ f : CuspForm (Gamma0GL M) 2, B f f = 0 → f = 0) ∧
      (∀ q : ℕ, q.Prime → ¬ q ∣ M →
        ∀ f g : CuspForm (Gamma0GL M) 2,
          B (heckeOp M q f) g = B f (heckeOp M q g)) := by
  obtain ⟨D, hDvol, ⟨U, hUo, hUne, hUD⟩, hDsa⟩ := exists_peterssonDomain hM
  refine ⟨fun f g => ∫ τ in D, petersson (2 : ℤ) ⇑g ⇑f τ, ?_, ?_, ?_, ?_, ?_⟩
  · intro f₁ f₂ g
    have hpt : ∀ τ : ℍ, petersson (2 : ℤ) ⇑g ⇑(f₁ + f₂) τ
        = petersson (2 : ℤ) ⇑g ⇑f₁ τ + petersson (2 : ℤ) ⇑g ⇑f₂ τ := by
      intro τ
      simp only [petersson, CuspForm.coe_add, Pi.add_apply]
      ring
    simp only [hpt]
    exact integral_add (peterssonIntegrableOn hM hDvol f₁ g)
      (peterssonIntegrableOn hM hDvol f₂ g)
  · intro a f g
    have hpt : ∀ τ : ℍ, petersson (2 : ℤ) ⇑g ⇑(a • f) τ
        = a * petersson (2 : ℤ) ⇑g ⇑f τ := by
      intro τ
      simp only [petersson, CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [hpt]
    exact integral_const_mul a _
  · intro f g
    have hpt : ∀ τ : ℍ, petersson (2 : ℤ) ⇑f ⇑g τ
        = starRingEnd ℂ (petersson (2 : ℤ) ⇑g ⇑f τ) := fun τ =>
      UpperHalfPlane.petersson_symm (2 : ℤ) ⇑g ⇑f τ
    simp only [hpt]
    exact integral_conj
  · intro f hf
    exact cuspForm_eq_zero_of_setIntegral_petersson_self_eq_zero hM hDvol hUo hUne hUD hf
  · intro q hq hqM f g
    exact hDsa q hq hqM f g

end PeterssonProduct

/-- **SEMISIMPLICITY OF THE GOOD HECKE OPERATORS on `S₂(Γ₀(M))`** (PROVEN
2026-07-26 over the single analytic leaf
`exists_peterssonProduct_selfAdjoint_heckeOp` — the Petersson product
with the good Hecke operators self-adjoint for it — and the general
linear algebra `eq_smul_of_pow_sub_smul_apply_eq_zero_of_selfAdjointForm`;
cut 2026-07-26 out of
`heckeOp_apply_eq_smul_of_generalizedEigen_of_newform`; Diamond–Shurman
Theorem 5.5.3 — self-adjointness of `T_q` for the Petersson product):
at a GOOD prime `q ∤ M`, the operator `T_q` is semisimple,
i.e. its GENERALIZED eigenspaces are already honest eigenspaces. Stated
elementwise, at an arbitrary scalar `c` and with the exponent existential
already instantiated by the consumer: a cusp form killed by a POWER of
`T_q − c` is killed by `T_q − c` itself.

This is the ANALYTIC half of the two-leaf cut of the reducedness node.
It knows nothing about newforms, and the eigenvalue `c` is arbitrary —
no `IsWeightTwoEigenform`, no `eigensystem_minimal`, no `g`.

PROOF (2026-07-26). Take the Petersson product `B` and the
self-adjointness of `T_q` at `q ∤ M` from
`exists_peterssonProduct_selfAdjoint_heckeOp`, and feed them to
`eq_smul_of_pow_sub_smul_apply_eq_zero_of_selfAdjointForm`: a
self-adjoint operator for a DEFINITE conjugate-symmetric form has no
generalized eigenvector that is not an eigenvector, because
`N = T_q − c` and its adjoint `N' = T_q − c̄` commute and have equal
kernels, whence `Nⁿ v = 0 ⇒ N v = 0`.

Two things the classical account uses and this proof does NOT: the
SPECTRAL THEOREM (the normal-operator kernel argument replaces it) and
FINITE-DIMENSIONALITY (`cuspForm_finiteDimensional` is not consumed
here). Definiteness of the Petersson product alone suffices, which is
why the leaf above asks only for that.

FAITHFULNESS AUDIT (2026-07-26). `hqM : ¬ q ∣ M` is LOAD-BEARING and the
statement is FALSE without it: at `q ∣ M` the operator is `U_q`, which is
genuinely NON-semisimple, and a size-`2` Jordan block at the eigenvalue
`0` is available at every level divisible by a cube.

Explicit counterexample. Let `f` be a newform of level `M'`, let `q ∤ M'`
be prime, and put `M = M'·q³`. On the old block
`span{f(qⁱz) : 0 ≤ i ≤ 3} ⊆ S₂(Γ₀(M))` the operator `U_q` acts by
`f ↦ a_q(f)·f − q·f(q·)` (this is `T_q = U_q + q·V_q` at level `M'`) and
`f(qⁱ·) ↦ f(q^{i−1}·)` for `i ≥ 1`, so in the basis
`(f, f(q·), f(q²·), f(q³·))` its matrix has characteristic polynomial
`X²·(X² − a_q X + q)` while its KERNEL is only the line spanned by the
`q`-depleted form `h = f − a_q(f)·f(q·) + q·f(q²·)`. Since `q ≠ 0`, `X²
− a_q X + q` does not vanish at `0`, so `0` has algebraic multiplicity
exactly `2` against geometric multiplicity `1`.

The generalized `0`-eigenvector is visible without any matrix: `h` has
level `M'·q²`, so `h(q·) ∈ S₂(Γ₀(M))`, and `U_q ∘ V_q = id` gives
`U_q (h(q·)) = h ≠ 0` while `U_q² (h(q·)) = U_q h = 0`. So the
good-prime hypothesis is not decoration; the same phenomenon is exactly
what makes the consumer node's own counterexample work.

DEPENDENCY NOTE (updated 2026-07-27 — SUPERSEDES the 2026-07-26 version,
which said the analysis under this node was "a `Γ₀(M)`-fundamental domain of
finite volume, plus the double-coset unfolding", and that the pin had no
computation of `volume 𝒟`).  BOTH halves of that are now out of date.
`exists_peterssonProduct_selfAdjoint_heckeOp` is PROVEN over
`exists_peterssonDomain`, which is itself now PROVEN over TWO leaves, the
domain having been constructed (`gamma0Domain`, the union of the
`[SL(2,ℤ) : Γ₀(M)]` translates of `𝒟`) with its FINITE VOLUME
(`volume_gamma0Domain_ne_top`, over the new `volume_modularFd_ne_top` —
`volume 𝒟 ≠ ⊤` is no longer missing from this development), its INTERIOR and
its `Γ₀(M)`-COVERING property all proven.  So the analysis remaining under
this node is exactly: `volume (𝒟 \ 𝒟ᵒ) = 0` — the boundary of the modular
domain is null, which is all that
`volume_smul_inter_gamma0Domain_eq_zero` still needs — plus the double-coset
unfolding `peterssonSelfAdjoint_of_gamma0FundamentalDomain`. -/
theorem heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level {M : ℕ} (hM : 0 < M)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (c : ℂ)
    {v : CuspForm (Gamma0GL M) 2} {n : ℕ}
    (hv : ((heckeOp M q -
      c • (1 : Module.End ℂ (CuspForm (Gamma0GL M) 2))) ^ n) v = 0) :
    heckeOp M q v = c • v := by
  obtain ⟨B, hadd, hsmul, hsymm, hdef, hadj⟩ :=
    exists_peterssonProduct_selfAdjoint_heckeOp hM
  exact eq_smul_of_pow_sub_smul_apply_eq_zero_of_selfAdjointForm hadd hsmul hsymm
    hdef (hadj q hq hqM) hv

/-- **MULTIPLICITY ONE AT THE INDICES COPRIME TO THE LEVEL** (PROVEN
2026-07-26): if `v ∈ S₂(Γ₀(M))` is an honest eigenvector of every GOOD
Hecke operator `T_q`, `q ∤ M`, at a normalized weight-2 eigenform `g`'s
eigenvalue `a_q(g)`, then `a_n(v) = a_1(v)·a_n(g)` for every `n` COPRIME
to `M`.

This is the good-prime analogue of
`qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen` above, and it is EXACTLY what
the Hecke recursion alone can deliver once the bad primes are dropped
from the hypothesis: `qCoeff_heckeOp` computes `a_{qm}` from `a_m` and
`a_{m/q}` only at primes `q` where the eigen-equation is available, so
the indices reachable from `a_1` are precisely the `n` with
`gcd(n, M) = 1`. Everything past that — the coefficients at the bad
primes, and with them the conclusion `v ∈ ℂ·g` — is genuine Atkin–Lehner
theory, and is isolated in
`exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`
below.

PROOF: strong induction on `n`, in the same shape as
`qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen` but carrying coprimality
along. A prime `q ∣ n` is automatically GOOD (it divides an `n` coprime
to `M`), so the eigen-equation is available at it, and the two smaller
indices `n/q` and `n/q²` are again coprime to `M`. -/
theorem qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen_of_coprime {M : ℕ}
    (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoEigenform M g)
    {v : CuspForm (Gamma0GL M) 2}
    (hv : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q v = qCoeff M g q • v) :
    ∀ n : ℕ, Nat.Coprime n M → qCoeff M v n = qCoeff M v 1 * qCoeff M g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hcop
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [qCoeff_zero, qCoeff_zero]; ring
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [hg.qCoeff_one]; ring
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m', rfl⟩ := hqn
    have hq2 : 2 ≤ q := hq.two_le
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | h
      · exact absurd (by ring) hn0
      · exact h
    have hm'lt : m' < q * m' := by
      have h2 : 2 * m' ≤ q * m' := Nat.mul_le_mul_right m' hq2
      omega
    have hdivlt : m' / q < q * m' := lt_of_le_of_lt (Nat.div_le_self _ _) hm'lt
    -- a prime factor of an index coprime to `M` is a GOOD prime
    have hqM : ¬ q ∣ M := by
      intro hd
      have h1 : q ∣ Nat.gcd (q * m') M := Nat.dvd_gcd (dvd_mul_right q m') hd
      rw [Nat.Coprime] at hcop
      rw [hcop] at h1
      exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
    have hcm' : Nat.Coprime m' M :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left m' q) hcop
    have hvq : qCoeff M (heckeOp M q v) m' = qCoeff M (qCoeff M g q • v) m' := by
      rw [hv q hq hqM]
    rw [qCoeff_heckeOp hM hq v m', qCoeff_smul] at hvq
    have hgq := hecke_eigen_coeff_identity hg hq m'
    have e1 := ih m' hm'lt hcm'
    rw [if_neg hqM] at hvq hgq
    by_cases hqmm : q ∣ m'
    · rw [if_pos hqmm] at hvq hgq
      have hcd : Nat.Coprime (m' / q) M :=
        Nat.Coprime.coprime_dvd_left
          ((Nat.div_dvd_of_dvd hqmm).trans (dvd_mul_left m' q)) hcop
      have e2 := ih (m' / q) hdivlt hcd
      linear_combination hvq - qCoeff M v 1 * hgq + qCoeff M g q * e1
        - (q : ℂ) * e2
    · rw [if_neg hqmm] at hvq hgq
      linear_combination hvq - qCoeff M v 1 * hgq + qCoeff M g q * e1

section DegeneracyOperator
open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
  ConjAct
open scoped Pointwise

/-- **The arithmetic core of `T_q ∘ V_d = V_d ∘ T_q`.**  Purely a statement
about `ℕ`-indexed coefficient families: substituting the degeneracy formula
`a_n(V_d u) = 1_{d ∣ n}·a_{n/d}(u)` into the good-prime Hecke formula
`a_m(T_q f) = a_{qm}(f) + 1_{q ∣ m}·q·a_{m/q}(f)` gives the same expression in
either order, because `q ∤ d` makes `q` and `d` coprime and so lets every
divisibility side-condition and every index be exchanged:
`d ∣ qm ↔ d ∣ m`, `qm/d = q(m/d)`, and, given `d ∣ m`, `q ∣ m ↔ q ∣ m/d`
with `m/q/d = m/d/q`. -/
theorem degeneracy_hecke_coeff_identity {d q : ℕ} (hd : 0 < d) (hq : q.Prime)
    (hqd : ¬ q ∣ d) (a : ℕ → ℂ) (m : ℕ) :
    ((if d ∣ q * m then a (q * m / d) else 0)
        + (if q ∣ m then (q : ℂ) * (if d ∣ m / q then a (m / q / d) else 0) else 0))
      = if d ∣ m then
          (a (q * (m / d)) + (if q ∣ m / d then (q : ℂ) * a (m / d / q) else 0))
        else 0 := by
  have hcopqd : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd
  have hcopdq : Nat.Coprime d q := hcopqd.symm
  by_cases hdm : d ∣ m
  · obtain ⟨t, rfl⟩ := hdm
    have hdt : d * t / d = t := Nat.mul_div_cancel_left t hd
    have h1 : d ∣ q * (d * t) := (dvd_mul_right d t).mul_left q
    have h2 : q * (d * t) / d = q * t := by
      rw [show q * (d * t) = d * (q * t) by ring, Nat.mul_div_cancel_left _ hd]
    rw [if_pos h1, if_pos (dvd_mul_right d t), h2, hdt]
    by_cases hqt : q ∣ t
    · have hqm : q ∣ d * t := hqt.mul_left d
      have hdiv : d * t / q = d * (t / q) := by
        obtain ⟨s, rfl⟩ := hqt
        rw [show d * (q * s) = q * (d * s) by ring, Nat.mul_div_cancel_left _ hq.pos,
          Nat.mul_div_cancel_left _ hq.pos]
      rw [if_pos hqm, if_pos hqt, hdiv, if_pos (dvd_mul_right d (t / q)),
        Nat.mul_div_cancel_left _ hd]
    · have hqm : ¬ q ∣ d * t := fun h => hqt (hcopqd.dvd_of_dvd_mul_left h)
      rw [if_neg hqm, if_neg hqt]
  · have h1 : ¬ d ∣ q * m := fun h => hdm (hcopdq.dvd_of_dvd_mul_left h)
    rw [if_neg h1, if_neg hdm]
    by_cases hqm : q ∣ m
    · have h2 : ¬ d ∣ m / q := fun h => hdm (h.trans (Nat.div_dvd_of_dvd hqm))
      rw [if_pos hqm, if_neg h2, mul_zero, zero_add]
    · rw [if_neg hqm, zero_add]

/-- **`V_d` COMMUTES with the good Hecke operators** (PROVEN 2026-07-26):
for `d·N ∣ M` and a prime `q ∤ M`,
`T_q^{(M)} ∘ V_d = V_d ∘ T_q^{(N)}`.

Note `q ∤ M` forces `q ∤ d` and `q ∤ N` (both divide `M`), so `q` is a GOOD
prime at BOTH levels and the two Hecke formulas carry the same `q·a_{m/q}`
correction term; the identity is then `degeneracy_hecke_coeff_identity`
coefficientwise, and a weight-2 cusp form is determined by its `q`-expansion. -/
theorem heckeOp_degeneracyOp {N M d q : ℕ} (hN : 0 < N) (hM : 0 < M) (hd : 0 < d)
    (hdvd : d * N ∣ M) (hq : q.Prime) (hqM : ¬ q ∣ M)
    (u : CuspForm (Gamma0GL N) 2) :
    heckeOp M q (degeneracyOp N M d u) = degeneracyOp N M d (heckeOp N q u) := by
  have hNdvd : N ∣ M := (Dvd.intro_left d rfl).trans hdvd
  have hddvd : d ∣ M := (Dvd.intro N rfl).trans hdvd
  have hqN : ¬ q ∣ N := fun h => hqM (h.trans hNdvd)
  have hqd : ¬ q ∣ d := fun h => hqM (h.trans hddvd)
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  rw [qCoeff_heckeOp hM hq (degeneracyOp N M d u) m, if_neg hqM,
    qCoeff_degeneracyOp hd hdvd u (q * m), qCoeff_degeneracyOp hd hdvd u (m / q),
    qCoeff_degeneracyOp hd hdvd (heckeOp N q u) m, qCoeff_heckeOp hN hq u (m / d),
    if_neg hqN]
  exact degeneracy_hecke_coeff_identity hd hq hqd (qCoeff N u) m

/-- **`V_d` is INJECTIVE** (PROVEN 2026-07-26): immediate from
`a_{d·m}(V_d u) = a_m(u)`, since a weight-2 cusp form is determined by its
`q`-expansion. -/
theorem degeneracyOp_injective {N M d : ℕ} (hd : 0 < d) (hdvd : d * N ∣ M) :
    Function.Injective (degeneracyOp N M d) := by
  intro u₁ u₂ h
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  have h1 := congrArg (fun F => qCoeff M F (d * m)) h
  simp only [qCoeff_degeneracyOp hd hdvd, if_pos (dvd_mul_right d m),
    Nat.mul_div_cancel_left m hd] at h1
  exact h1

/-- **THE ELEMENTARY CONVERSE OF THE MAIN LEMMA** (PROVEN 2026-07-26): every
form in the OLD subspace has vanishing `q`-expansion coefficients at all
indices COPRIME to the level.

`a_n(V_p u) = 0` unless `p ∣ n` (`qCoeff_degeneracyOp`), and an `n` coprime to
`M` is divisible by NO prime factor `p` of `M`.  Vanishing at a fixed `n` is
the kernel of the linear functional `qCoeffL M n`, hence a submodule, so it
suffices to check it on each generating image — which is what makes this
direction elementary while the converse
(`mem_oldSubspace_of_qCoeff_coprime_eq_zero`) is genuine analysis.

`0 < M` is retained for API uniformity with the siblings but is NOT used by
the proof, hence the underscore: at `M = 0` the statement is vacuously fine
because `Nat.primeFactors 0 = ∅` makes the old subspace `⊥`. -/
theorem qCoeff_eq_zero_of_mem_oldSubspace {M : ℕ} (_hM : 0 < M)
    {v : CuspForm (Gamma0GL M) 2}
    (hv : v ∈ ⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p))
    {n : ℕ} (hn : Nat.Coprime n M) : qCoeff M v n = 0 := by
  have hle : (⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p))
      ≤ LinearMap.ker (qCoeffL M n) := by
    refine iSup₂_le fun p hp => ?_
    rintro _ ⟨u, rfl⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ M := Nat.dvd_of_mem_primeFactors hp
    have hdvd : p * (M / p) ∣ M := by rw [Nat.mul_div_cancel' hpd]
    have hpn : ¬ p ∣ n := by
      intro h
      have hp1 : p ∣ 1 := hn ▸ Nat.dvd_gcd h hpd
      exact hpp.one_lt.ne' (Nat.dvd_one.mp hp1)
    rw [LinearMap.mem_ker, qCoeffL_apply, qCoeff_degeneracyOp hpp.pos hdvd,
      if_neg hpn]
  have := hle hv
  rwa [LinearMap.mem_ker, qCoeffL_apply] at this

end DegeneracyOperator

/-- **SPECTRAL DESCENT THROUGH A SUM OF STABLE SUBSPACES** (PROVEN
2026-07-26, pure linear algebra over an algebraically closed field).

Let a family `T i` of COMMUTING endomorphisms of a finite-dimensional space
`V` preserve each member of a family `U k` of subspaces, and let `w ≠ 0` lie
in `⨆ k, U k` and in the simultaneous generalized eigenspace at the character
`χ`.  Then SOME single `U k` already contains a nonzero vector of that same
simultaneous generalized eigenspace.

This is what lets a joint Hecke eigenvector in the OLD subspace — which is a
SUM of the images of the degeneracy maps `V_p`, and in general lies in no
single one of them — be traced back to ONE prime `p`.

PROOF.  Simultaneous triangularizability
(`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`)
applied to the operators RESTRICTED to `U k`, pushed forward along the
inclusion via `Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`, writes
each `U k` as `⨆ ψ, U k ⊓ E ψ` where `E ψ` is the simultaneous generalized
eigenspace at `ψ`.  Hence `⨆ k, U k = ⨆ ψ, ⨆ k, (U k ⊓ E ψ)`.  Splitting that
sup at `ψ = χ` and using INDEPENDENCE of the `E ψ`
(`Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`) kills the
`ψ ≠ χ` part of `w`, because `w` itself lies in `E χ`.  So
`w ∈ ⨆ k, (U k ⊓ E χ)`, and `w ≠ 0` forces some summand to be nonzero. -/
theorem exists_ne_zero_mem_inf_iInf_maxGenEigenspace
    {K V ι κ : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (U : κ → Submodule K V) (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hstab : ∀ i k, Set.MapsTo (T i) (U k) (U k))
    (χ : ι → K) {w : V} (hw : w ≠ 0) (hwU : w ∈ ⨆ k, U k)
    (hwχ : w ∈ ⨅ i, (T i).maxGenEigenspace (χ i)) :
    ∃ k, ∃ v ∈ U k, v ≠ 0 ∧ v ∈ ⨅ i, (T i).maxGenEigenspace (χ i) := by
  classical
  set E : (ι → K) → Submodule K V :=
    fun ψ => ⨅ i, (T i).maxGenEigenspace (ψ i) with hEdef
  have hmaps : ∀ i j φ,
      Set.MapsTo (T i) ((T j).maxGenEigenspace φ) ((T j).maxGenEigenspace φ) :=
    fun i j φ => (T j).mapsTo_maxGenEigenspace_of_comm (hcomm i j).eq.symm φ
  have hindep : iSupIndep E :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T hmaps
  -- Every stable subspace is the sum of its intersections with the joint
  -- generalized eigenspaces.
  have hUdecomp : ∀ k, U k = ⨆ ψ : ι → K, U k ⊓ E ψ := by
    intro k
    have hp : ∀ i, Set.MapsTo (T i) (U k) (U k) := fun i => hstab i k
    have hcomm' : ∀ i j, Commute ((T i).restrict (hp i)) ((T j).restrict (hp j)) := by
      intro i j
      refine LinearMap.ext fun x => Subtype.ext ?_
      have hx := LinearMap.congr_fun (hcomm i j).eq (x : V)
      simpa [LinearMap.restrict_apply, Module.End.mul_apply] using hx
    have htop : ⨆ ψ : ι → K,
        ⨅ i, Module.End.maxGenEigenspace ((T i).restrict (hp i)) (ψ i) = ⊤ :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        _ (fun i j _ => hcomm' i j)
        (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
    have hmap := congrArg (Submodule.map (U k).subtype) htop
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype] at hmap
    simp only [← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo T (U k) hp] at hmap
    exact hmap.symm
  set F : (ι → K) → Submodule K V := fun ψ => ⨆ k, U k ⊓ E ψ with hFdef
  have hFle : ∀ ψ, F ψ ≤ E ψ := fun ψ => iSup_le fun _ => inf_le_right
  have hwF : w ∈ ⨆ ψ : ι → K, F ψ := by
    have h1 : (⨆ k, U k) = ⨆ k, ⨆ ψ : ι → K, U k ⊓ E ψ := iSup_congr hUdecomp
    have h2 : (⨆ ψ : ι → K, F ψ) = ⨆ k, ⨆ ψ : ι → K, U k ⊓ E ψ := iSup_comm
    rw [h2, ← h1]
    exact hwU
  -- Split off the `χ`-component; independence kills the rest, since `w ∈ E χ`.
  have hwFχ : w ∈ F χ := by
    rw [iSup_split_single F χ] at hwF
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hwF
    have hbE : b ∈ E χ := by
      rw [eq_sub_of_add_eq' hab]
      exact Submodule.sub_mem _ hwχ (hFle χ ha)
    have hbrest : b ∈ ⨆ (ψ : ι → K) (_ : ψ ≠ χ), E ψ :=
      (iSup₂_mono fun ψ _ => hFle ψ) hb
    have hb0 : b = 0 := by
      have hbot := (hindep χ).le_bot ⟨hbE, hbrest⟩
      simpa using hbot
    have haw : a = w := by rw [← hab, hb0, add_zero]
    exact haw ▸ ha
  -- A nonzero vector in a supremum forces one summand to be nonzero.
  have hex : ∃ k, U k ⊓ E χ ≠ ⊥ := by
    by_contra hcon
    have hcon' : ∀ k, U k ⊓ E χ = ⊥ := fun k => by
      by_contra hk
      exact hcon ⟨k, hk⟩
    have hbot : F χ = ⊥ := by simp [hFdef, hcon']
    rw [hbot] at hwFχ
    exact hw (Submodule.mem_bot K |>.mp hwFχ)
  obtain ⟨k, hk⟩ := hex
  obtain ⟨v, hv, hv0⟩ := (U k ⊓ E χ).ne_bot_iff.mp hk
  obtain ⟨hvU, hvE⟩ := Submodule.mem_inf.mp hv
  exact ⟨k, v, hvU, hv0, hvE⟩

/-- **DESCENT OUT OF THE OLD SUBSPACE TO A SINGLE PRIME** (PROVEN
2026-07-26): a NONZERO joint eigenvector `w` of the good Hecke operators
lying in the old subspace `Σ_{p ∣ M} V_p S₂(Γ₀(M/p))` comes, for SOME prime
`p ∣ M`, from a NONZERO joint eigenvector `u ∈ S₂(Γ₀(M/p))` with the SAME
eigenvalues.

This is the step that the file docstring's "pure coefficient computation"
remark under-describes: `w` lies in a SUM of the images `V_p`, and those
images are NOT independent (e.g. `V_{pq}f` lies in both `V_p` and `V_q`), so
one cannot simply read off a component.  What makes it work is spectral, not
coefficientwise — each `range V_p` is stable under the good `T_q`
(`heckeOp_degeneracyOp`), so the simultaneous generalized eigenspace
decomposition can be intersected with it
(`exists_ne_zero_mem_inf_iInf_maxGenEigenspace`).

The generalized eigenvector this produces is upgraded to an HONEST one by
`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level` (good-prime
semisimplicity, the Petersson leaf), and then pushed down through the
INJECTIVITY of `V_p`. -/
theorem exists_heckeOp_eigen_of_mem_oldSubspace {M : ℕ} (hM : 0 < M) {c : ℕ → ℂ}
    {w : CuspForm (Gamma0GL M) 2} (hw : w ≠ 0)
    (hwe : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q w = c q • w)
    (hold : w ∈ ⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p)) :
    ∃ p ∈ M.primeFactors, ∃ u : CuspForm (Gamma0GL (M / p)) 2, u ≠ 0 ∧
      ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp (M / p) q u = c q • u := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (Gamma0GL M) 2) :=
    cuspForm_finiteDimensional M hM
  -- Basic facts about a prime factor `p` of `M`.
  have hfac : ∀ p : ℕ, p ∈ M.primeFactors →
      p.Prime ∧ 0 < M / p ∧ p * (M / p) ∣ M := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ M := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpp, Nat.div_pos (Nat.le_of_dvd hM hpd) hpp.pos, ?_⟩
    rw [Nat.mul_div_cancel' hpd]
  set T : {q : ℕ // q.Prime ∧ ¬ q ∣ M} → Module.End ℂ (CuspForm (Gamma0GL M) 2) :=
    fun q => heckeOp M q.1 with hTdef
  set U : {p : ℕ // p ∈ M.primeFactors} → Submodule ℂ (CuspForm (Gamma0GL M) 2) :=
    fun p => LinearMap.range (degeneracyOp (M / p.1) M p.1) with hUdef
  have hcomm : ∀ i j, Commute (T i) (T j) := fun i j =>
    heckeOp_mul_comm hM i.2.1 j.2.1
  have hstab : ∀ i k, Set.MapsTo (T i) (U k) (U k) := by
    intro i k x hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨hpp, hpos, hdvd⟩ := hfac k.1 k.2
    exact ⟨heckeOp (M / k.1) i.1 u,
      (heckeOp_degeneracyOp hpos hM hpp.pos hdvd i.2.1 i.2.2 u).symm⟩
  have hwU : w ∈ ⨆ k, U k := by
    have hle : (⨆ p ∈ M.primeFactors,
        LinearMap.range (degeneracyOp (M / p) M p)) ≤ ⨆ k, U k :=
      iSup₂_le fun p hp => le_iSup U ⟨p, hp⟩
    exact hle hold
  have hwχ : w ∈ ⨅ i, (T i).maxGenEigenspace ((fun q => c q.1) i) := by
    rw [Module.End.mem_iInf_maxGenEigenspace_iff]
    intro j
    refine ⟨1, ?_⟩
    have hj := hwe j.1 j.2.1 j.2.2
    simp only [pow_one, LinearMap.sub_apply, hTdef]
    rw [hj]
    simp
  obtain ⟨k, v, hvU, hv0, hvE⟩ :=
    exists_ne_zero_mem_inf_iInf_maxGenEigenspace U T hcomm hstab
      (fun q => c q.1) hw hwU hwχ
  obtain ⟨hpp, hpos, hdvd⟩ := hfac k.1 k.2
  obtain ⟨u, hu⟩ := hvU
  refine ⟨k.1, k.2, u, ?_, ?_⟩
  · intro hu0
    exact hv0 (by rw [← hu, hu0, map_zero])
  · intro q hq hqM
    -- generalized eigenvector upstairs, made honest by semisimplicity
    obtain ⟨n, hn⟩ :=
      (Module.End.mem_iInf_maxGenEigenspace_iff T (fun q => c q.1) v).mp hvE
        ⟨q, hq, hqM⟩
    have hvsmul : heckeOp M q v = c q • v :=
      heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level hM hq hqM (c q)
        (n := n) (by simpa [hTdef] using hn)
    -- push the identity down through the injective `V_p`
    refine degeneracyOp_injective hpp.pos hdvd ?_
    rw [← heckeOp_degeneracyOp hpos hM hpp.pos hdvd hq hqM u, hu, hvsmul, ← hu,
      map_smul]

/-- **A FINITE COMMUTING FAMILY OF ENDOMORPHISMS HAS A COMMON EIGENVECTOR IN
EVERY NONZERO INVARIANT SUBSPACE** (PROVEN 2026-07-27): pure linear algebra
over an arbitrary finite-dimensional complex vector space — no modular-forms
input enters, deliberately, so that the modular application below is a one-line
instantiation.

Induction on the finset.  At the step, `A` restricts to an endomorphism of the
invariant `W`, which is finite-dimensional and nontrivial, so over the
algebraically closed `ℂ` it has an eigenvalue `μ`
(`Module.End.exists_eigenvalue`); the smaller subspace `W ⊓ eigenspace A μ` is
again nonzero (it contains the eigenvector) and is still invariant under every
`B` in the rest of the family, because `B` commutes with `A` and preserves `W`.
The induction hypothesis applied there returns a vector that is simultaneously
an eigenvector of the rest AND, by construction, of `A`. -/
theorem exists_ne_zero_mem_forall_eq_smul_of_commuting_finset
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    ∀ S : Finset (Module.End ℂ V), (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) →
      ∀ W : Submodule ℂ V, W ≠ ⊥ → (∀ A ∈ S, ∀ x ∈ W, A x ∈ W) →
      ∃ w ∈ W, w ≠ 0 ∧ ∀ A ∈ S, ∃ μ : ℂ, A w = μ • w := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ W hW _
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
    exact ⟨w, hw, hw0, by simp⟩
  | insert A S hAS ih =>
    intro hcomm W hW hstab
    have hAW : ∀ x ∈ W, A x ∈ W := hstab A (Finset.mem_insert_self A S)
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot (p := W)).mpr hW
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (LinearMap.restrict A hAW)
    obtain ⟨v, hvmem, hv0⟩ := hμ.exists_hasEigenvector
    have hvA : A (v : V) = μ • (v : V) := by
      have h1 : LinearMap.restrict A hAW v = μ • v := Module.End.mem_eigenspace_iff.mp hvmem
      have h2 := congrArg (fun z : W => (z : V)) h1
      simpa using h2
    have hv0' : (v : V) ≠ 0 := fun h => hv0 (Submodule.coe_eq_zero.mp h)
    have hvW' : (v : V) ∈ W ⊓ Module.End.eigenspace A μ :=
      Submodule.mem_inf.mpr ⟨v.2, Module.End.mem_eigenspace_iff.mpr hvA⟩
    have hW'bot : W ⊓ Module.End.eigenspace A μ ≠ ⊥ :=
      (Submodule.ne_bot_iff _).mpr ⟨_, hvW', hv0'⟩
    have hstab' : ∀ B ∈ S, ∀ x ∈ W ⊓ Module.End.eigenspace A μ,
        B x ∈ W ⊓ Module.End.eigenspace A μ := by
      intro B hB x hx
      obtain ⟨hxW, hxe⟩ := Submodule.mem_inf.mp hx
      have hxe' : A x = μ • x := Module.End.mem_eigenspace_iff.mp hxe
      have hcm : A * B = B * A :=
        hcomm A (Finset.mem_insert_self A S) B (Finset.mem_insert_of_mem hB)
      have hAB : A (B x) = B (A x) := by
        have h : (A * B) x = (B * A) x := by rw [hcm]
        simpa using h
      refine Submodule.mem_inf.mpr ⟨hstab B (Finset.mem_insert_of_mem hB) x hxW, ?_⟩
      exact Module.End.mem_eigenspace_iff.mpr (by rw [hAB, hxe', map_smul])
    obtain ⟨w, hwW', hw0, hws⟩ :=
      ih (fun B hB C hC =>
        hcomm B (Finset.mem_insert_of_mem hB) C (Finset.mem_insert_of_mem hC))
        (W ⊓ Module.End.eigenspace A μ) hW'bot hstab'
    obtain ⟨hwW, hwe⟩ := Submodule.mem_inf.mp hwW'
    refine ⟨w, hwW, hw0, ?_⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC'
    · exact ⟨μ, Module.End.mem_eigenspace_iff.mp hwe⟩
    · exact hws C hC'

/-- **SIMULTANEOUS DIAGONALISATION OF THE FULL HECKE FAMILY** (PROVEN
2026-07-27): a nonzero subspace `W ⊆ S₂(Γ₀(N))` stable under EVERY Hecke
operator `T_q` — the good ones `q ∤ N` and the bad ones `U_q`, `q ∣ N`, alike —
contains a nonzero common eigenvector of all of them.

The family is infinite, so the finset lemma above does not apply directly.  The
bridge is that `End ℂ S₂(Γ₀(N))` is FINITE-DIMENSIONAL
(`cuspForm_finiteDimensional`), so the set `{T_q : q prime}` has a finite subset
`b` with the same span (`exists_linearIndependent` plus
`LinearIndependent.setFinite`).  A common eigenvector of `b` is automatically an
eigenvector of everything in `span b`, since for fixed `w ≠ 0` the operators
having `w` as an eigenvector form a SUBMODULE of `End ℂ S₂(Γ₀(N))` —
`Submodule.span_induction`.  Commutativity of the whole family is
`heckeOp_mul_comm`, which holds for ALL pairs of primes, bad ones included. -/
theorem exists_ne_zero_mem_forall_prime_heckeOp_eq_smul {N : ℕ} (hN : 0 < N)
    {W : Submodule ℂ (CuspForm (Gamma0GL N) 2)} (hW : W ≠ ⊥)
    (hstab : ∀ q : ℕ, q.Prime → ∀ x ∈ W, heckeOp N q x ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∃ lam : ℕ → ℂ,
      ∀ q : ℕ, q.Prime → heckeOp N q w = lam q • w := by
  classical
  haveI := cuspForm_finiteDimensional N hN
  obtain ⟨b, hbP, hspan, hli⟩ :=
    exists_linearIndependent ℂ
      ((fun q : ℕ => heckeOp N q) '' {q : ℕ | q.Prime})
  have hbfin : b.Finite := hli.setFinite
  have hSb : ∀ A ∈ hbfin.toFinset, ∃ q : ℕ, q.Prime ∧ heckeOp N q = A := by
    intro A hA
    obtain ⟨q, hq, hqA⟩ := hbP (hbfin.mem_toFinset.mp hA)
    exact ⟨q, hq, hqA⟩
  have hcomm : ∀ A ∈ hbfin.toFinset, ∀ B ∈ hbfin.toFinset, A * B = B * A := by
    intro A hA B hB
    obtain ⟨q, hq, rfl⟩ := hSb A hA
    obtain ⟨r, hr, rfl⟩ := hSb B hB
    exact heckeOp_mul_comm hN hq hr
  have hstabS : ∀ A ∈ hbfin.toFinset, ∀ x ∈ W, A x ∈ W := by
    intro A hA x hx
    obtain ⟨q, hq, rfl⟩ := hSb A hA
    exact hstab q hq x hx
  obtain ⟨w, hwW, hw0, hws⟩ :=
    exists_ne_zero_mem_forall_eq_smul_of_commuting_finset hbfin.toFinset hcomm W hW hstabS
  have hkey : ∀ A ∈ Submodule.span ℂ b, ∃ μ : ℂ, A w = μ • w := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact hws A (hbfin.mem_toFinset.mpr hA)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by simp [ha, hc, add_smul]⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c * a, by simp [ha, mul_smul]⟩
  have hprime : ∀ q : ℕ, q.Prime → ∃ μ : ℂ, heckeOp N q w = μ • w := by
    intro q hq
    refine hkey _ ?_
    rw [hspan]
    exact Submodule.subset_span ⟨q, hq, rfl⟩
  refine ⟨w, hwW, hw0, fun q => if h : q.Prime then (hprime q h).choose else 0, ?_⟩
  intro q hq
  simp only [dif_pos hq]
  exact (hprime q hq).choose_spec

/-- **THE COEFFICIENT RECURSION CARRIED BY A JOINT HECKE EIGENVECTOR** (PROVEN
2026-07-27): reading `T_q w = λ_q · w` in the `m`-th `q`-expansion coefficient
through `qCoeff_heckeOp` gives

  `a_{qm}(w) + 1_{q∤N} 1_{q∣m} · q · a_{m/q}(w) = λ_q · a_m(w)`,

for EVERY prime `q`, bad primes included (where the correction term is absent).
This one identity drives both consequences below. -/
theorem qCoeff_heckeOp_eigen_rel {N : ℕ} (hN : 0 < N) {lam : ℕ → ℂ}
    {w : CuspForm (Gamma0GL N) 2}
    (hw : ∀ q : ℕ, q.Prime → heckeOp N q w = lam q • w)
    {q : ℕ} (hq : q.Prime) (m : ℕ) :
    qCoeff N w (q * m) +
        (if q ∣ N then 0 else if q ∣ m then (q : ℂ) * qCoeff N w (m / q) else 0)
      = lam q * qCoeff N w m := by
  have h : qCoeff N (heckeOp N q w) m = qCoeff N (lam q • w) m := by rw [hw q hq]
  rw [qCoeff_heckeOp hN hq w m, qCoeff_smul] at h
  exact h

/-- **A JOINT EIGENVECTOR OF EVERY HECKE OPERATOR WITH `a₁ = 0` IS ZERO**
(PROVEN 2026-07-27).  Strong induction on `m`: for `m ≥ 2` pick a prime `q ∣ m`,
write `m = q·m'`, and solve `qCoeff_heckeOp_eigen_rel` at `m'` for the top
index; both `m'` and `m'/q` are smaller, so the induction hypothesis kills the
right-hand side.  A cusp form is determined by its `q`-expansion
(`cuspForm_eq_of_forall_qCoeff_eq`).

This is what makes the normalisation step below unconditional: the eigenvector
produced by simultaneous diagonalisation NEVER has vanishing first
coefficient. -/
theorem eq_zero_of_forall_heckeOp_eq_smul_of_qCoeff_one_eq_zero {N : ℕ} (hN : 0 < N)
    {lam : ℕ → ℂ} {w : CuspForm (Gamma0GL N) 2}
    (hw : ∀ q : ℕ, q.Prime → heckeOp N q w = lam q • w)
    (h1 : qCoeff N w 1 = 0) : w = 0 := by
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  rw [qCoeff_zero_cuspForm]
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · exact qCoeff_zero N w
    rcases eq_or_ne m 1 with rfl | hm1
    · exact h1
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m', rfl⟩ := hqm
    have hq2 : 2 ≤ q := hq.two_le
    have hm'pos : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with rfl | h
      · exact absurd (by ring) hm0
      · exact h
    have hm'lt : m' < q * m' := by
      have h2 : 2 * m' ≤ q * m' := Nat.mul_le_mul_right m' hq2
      omega
    have hdivlt : m' / q < q * m' := lt_of_le_of_lt (Nat.div_le_self _ _) hm'lt
    have hrel := qCoeff_heckeOp_eigen_rel hN hw hq m'
    have e1 := ih m' hm'lt
    have e2 := ih (m' / q) hdivlt
    simp only [e1, e2, mul_zero, ite_self, add_zero] at hrel
    exact hrel

/-- **A NORMALIZED JOINT EIGENVECTOR OF EVERY HECKE OPERATOR IS A WEIGHT-TWO
EIGENFORM** (PROVEN 2026-07-27 — the converse of
`heckeOp_apply_eq_smul_of_isWeightTwoEigenform`, and the step that makes the
Atkin–Lehner apparatus unnecessary at the node below).

The point is that `IsWeightTwoEigenform` on this pin is the FULL-Hecke
coefficient condition of Diamond–Shurman Prop. 5.8.5 — normalisation,
multiplicativity at coprime indices, and BOTH prime-power recursions, the good
one at `q ∤ N` and the `U_q` one at `q ∣ N`.  It does NOT demand newness.  So
an eigenvector of the whole family, normalized, satisfies it verbatim, and the
inhabitant produced here is in general OLD — a `q`-stabilisation of a newform
of smaller level — which is exactly what the consumers of this notion allow.

The four fields all fall out of `qCoeff_heckeOp_eigen_rel`:

* `a_q(w) = λ_q` at `m = 1` (a prime divides no `1`), so the eigenvalues ARE
  the prime coefficients;
* the two prime-power recursions are the relation at `m = q^{r+1}` resp.
  `m = q^r`;
* multiplicativity is a two-stage induction: first
  `a_{q^r n} = a_{q^r}·a_n` for `q ∤ n` — proved by a simple induction on `r`
  carrying the pair `(r, r+1)`, since the relation at `q^{r+1}n` refers back to
  both `q^{r+1}n` and `q^r n` — and then the general coprime statement by
  `Nat.recOnPrimePow`, peeling one prime power at a time. -/
theorem isWeightTwoEigenform_of_forall_heckeOp_eq_smul {N : ℕ} (hN : 0 < N)
    {lam : ℕ → ℂ} {w : CuspForm (Gamma0GL N) 2}
    (hw : ∀ q : ℕ, q.Prime → heckeOp N q w = lam q • w)
    (h1 : qCoeff N w 1 = 1) :
    IsWeightTwoEigenform N w := by
  have hdvd1 : ∀ q : ℕ, q.Prime → ¬ q ∣ 1 := fun q hq h => hq.ne_one (Nat.dvd_one.mp h)
  have hlam : ∀ q : ℕ, q.Prime → lam q = qCoeff N w q := by
    intro q hq
    have h := qCoeff_heckeOp_eigen_rel hN hw hq 1
    simp only [mul_one, h1, if_neg (hdvd1 q hq), ite_self, add_zero] at h
    exact h.symm
  have hbad : ∀ q : ℕ, q.Prime → q ∣ N → ∀ m : ℕ,
      qCoeff N w (q * m) = lam q * qCoeff N w m := by
    intro q hq hqN m
    have h := qCoeff_heckeOp_eigen_rel hN hw hq m
    rwa [if_pos hqN, add_zero] at h
  have hgood : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ m : ℕ, q ∣ m →
      qCoeff N w (q * m) = lam q * qCoeff N w m - (q : ℂ) * qCoeff N w (m / q) := by
    intro q hq hqN m hqm
    have h := qCoeff_heckeOp_eigen_rel hN hw hq m
    rw [if_neg hqN, if_pos hqm] at h
    linear_combination h
  have hgood' : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ m : ℕ, ¬ q ∣ m →
      qCoeff N w (q * m) = lam q * qCoeff N w m := by
    intro q hq hqN m hqm
    have h := qCoeff_heckeOp_eigen_rel hN hw hq m
    rwa [if_neg hqN, if_neg hqm, add_zero] at h
  have hppbad : ∀ q : ℕ, q.Prime → q ∣ N → ∀ r : ℕ,
      qCoeff N w (q ^ (r + 1)) = lam q * qCoeff N w (q ^ r) := by
    intro q hq hqN r
    have e : q * q ^ r = q ^ (r + 1) := by ring
    rw [← e]
    exact hbad q hq hqN (q ^ r)
  have hppgood : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ r : ℕ,
      qCoeff N w (q ^ (r + 1 + 1)) =
        lam q * qCoeff N w (q ^ (r + 1)) - (q : ℂ) * qCoeff N w (q ^ r) := by
    intro q hq hqN r
    have e : q * q ^ (r + 1) = q ^ (r + 1 + 1) := by ring
    have e2 : q ^ (r + 1) / q = q ^ r := by
      rw [pow_succ, Nat.mul_div_cancel _ hq.pos]
    have hd : q ∣ q ^ (r + 1) := dvd_pow_self q (Nat.succ_ne_zero r)
    have h := hgood q hq hqN (q ^ (r + 1)) hd
    rw [e, e2] at h
    exact h
  -- Multiplicativity across a prime power and a factor prime to it.
  have hD1 : ∀ q : ℕ, q.Prime → ∀ n : ℕ, ¬ q ∣ n → ∀ r : ℕ,
      qCoeff N w (q ^ r * n) = qCoeff N w (q ^ r) * qCoeff N w n ∧
      qCoeff N w (q ^ (r + 1) * n) = qCoeff N w (q ^ (r + 1)) * qCoeff N w n := by
    intro q hq n hn r
    induction r with
    | zero =>
      refine ⟨by simp [h1], ?_⟩
      simp only [zero_add, pow_one]
      by_cases hqN : q ∣ N
      · rw [hbad q hq hqN n, hlam q hq]
      · rw [hgood' q hq hqN n hn, hlam q hq]
    | succ s ihs =>
      obtain ⟨ih0, ih1⟩ := ihs
      refine ⟨ih1, ?_⟩
      have e1 : q ^ (s + 1 + 1) * n = q * (q ^ (s + 1) * n) := by ring
      by_cases hqN : q ∣ N
      · rw [e1, hbad q hq hqN (q ^ (s + 1) * n), ih1, hppbad q hq hqN (s + 1)]
        ring
      · have hd : q ∣ q ^ (s + 1) * n :=
          dvd_mul_of_dvd_left (dvd_pow_self q (Nat.succ_ne_zero s)) n
        have e2 : q ^ (s + 1) * n / q = q ^ s * n := by
          rw [pow_succ, mul_right_comm, Nat.mul_div_cancel _ hq.pos]
        rw [e1, hgood q hq hqN (q ^ (s + 1) * n) hd, e2, ih1, ih0,
          hppgood q hq hqN s]
        ring
  have hD1' : ∀ q : ℕ, q.Prime → ∀ r n : ℕ, ¬ q ∣ n →
      qCoeff N w (q ^ r * n) = qCoeff N w (q ^ r) * qCoeff N w n :=
    fun q hq r n hn => (hD1 q hq n hn r).1
  -- Full multiplicativity at coprime arguments.
  have hD2 : ∀ m n : ℕ, Nat.Coprime m n →
      qCoeff N w (m * n) = qCoeff N w m * qCoeff N w n := by
    intro m
    induction m using Nat.recOnPrimePow with
    | zero => intro n _; simp [qCoeff_zero]
    | one => intro n _; simp [h1]
    | prime_pow_mul a p k hp hpa hk iha =>
      intro n hcop
      have hpd : p ∣ p ^ k * a := dvd_mul_of_dvd_left (dvd_pow_self p hk.ne') a
      have hpn : ¬ p ∣ n :=
        (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpd hcop)
      have hcopa : Nat.Coprime a n :=
        Nat.Coprime.coprime_dvd_left (dvd_mul_left a (p ^ k)) hcop
      have hpan : ¬ p ∣ a * n := by
        intro hd
        rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
        · exact hpa h
        · exact hpn h
      calc qCoeff N w (p ^ k * a * n)
          = qCoeff N w (p ^ k * (a * n)) := by rw [mul_assoc]
        _ = qCoeff N w (p ^ k) * qCoeff N w (a * n) := hD1' p hp k (a * n) hpan
        _ = qCoeff N w (p ^ k) * (qCoeff N w a * qCoeff N w n) := by rw [iha n hcopa]
        _ = qCoeff N w (p ^ k) * qCoeff N w a * qCoeff N w n := by ring
        _ = qCoeff N w (p ^ k * a) * qCoeff N w n := by rw [hD1' p hp k a hpa]
  refine ⟨h1, hD2, ?_, ?_⟩
  · intro q hq hqN r
    have h := hppgood q hq hqN r
    rw [hlam q hq] at h
    exact h
  · intro q hq hqN r
    have h := hppbad q hq hqN r
    rw [hlam q hq] at h
    exact h

/-- **EIGENSYSTEM REALIZATION AT A DIVISOR LEVEL** (PROVEN 2026-07-27 — cut
2026-07-26 out of `exists_weightTwoEigenform_of_mem_oldSubspace`;
Diamond–Shurman Theorem 5.8.2 together with Proposition 5.8.5): a NONZERO
`u ∈ S₂(Γ₀(N))`, with `N ∣ M`, which is an honest eigenvector of every Hecke
operator `T_q` at a prime `q ∤ M`, with eigenvalues `c q`, has `c` realized on
those primes by a normalized weight-2 eigenform of some level `M' ∣ N`.

**CORRECTION OF THIS NODE'S OWN 2026-07-26 ROUTE AUDIT**, which is why the
proof is short.  The audit recorded here said the leaf "is genuinely downstream
of the analytic half; it is not dischargeable by coefficient bookkeeping
alone", because it read the conclusion as demanding a NEWFORM and therefore the
newform decomposition — i.e. the Main Lemma
`mem_oldSubspace_of_qCoeff_coprime_eq_zero` at every level dividing `N`.  That
is false of the statement as written: `IsWeightTwoEigenform M'` is the
FULL-Hecke coefficient condition, with no minimality clause, so an OLD form —
a `q`-stabilisation — is a perfectly good witness, and `M' = N` always works.
Neither the old subspace, nor the degeneracy maps, nor the Petersson product
appears anywhere below.  (The sibling
`exists_weightTwoEigenform_of_mem_oldSubspace` does still need the descent, but
only for its extra conclusion `M' ≠ M`, which it obtains ARITHMETICALLY from
`M' ∣ M/p < M` — not from newness either.)

PROOF, in three moves.

1. The joint `c`-eigenspace `E` of the good operators `{T_q : q ∤ M}` is
   nonzero (it contains `u`) and is stable under EVERY `T_q`, because the
   Hecke operators commute (`heckeOp_mul_comm`, valid at bad primes too).
2. `E` therefore contains a nonzero common eigenvector `w` of the WHOLE Hecke
   family — good `T_q` and bad `U_q` alike — by
   `exists_ne_zero_mem_forall_prime_heckeOp_eq_smul`.  This is the move the
   audit missed: the bad-prime eigenvalues are not read off the arithmetic,
   they are MANUFACTURED by diagonalising a commuting family over `ℂ`.
3. `a_1(w) ≠ 0`, since otherwise every coefficient vanishes
   (`eq_zero_of_forall_heckeOp_eq_smul_of_qCoeff_one_eq_zero`) and `w = 0`.  So
   `g = a_1(w)⁻¹ · w` is normalized, hence an eigenform
   (`isWeightTwoEigenform_of_forall_heckeOp_eq_smul`), and its prime
   coefficients are its eigenvalues, which at `q ∤ M` are `c q` because `w ∈ E`.

FAITHFULNESS.  `hu : u ≠ 0` is load-bearing: for `u = 0` the conclusion asserts
an eigenform matching an unconstrained `c`, and at `N = 1` there is no
eigenform at all (`S₂(Γ₀(1)) = 0`, `isWeightTwoEigenform_one_elim`).  The
statement is NOT vacuous: `N = M'` with `u = f` a newform and `c q = a_q(f)`
satisfies every hypothesis.

`_hNM : N ∣ M` is UNUSED and underscored to make that mechanically visible.
It is not a sign of weakness: the divisibility was recorded because it is the
shape the descent produces, and the audit expected an induction on the level
that would need it.  The route above never inducts on the level, so it never
consumes the relation between `N` and `M`; the leaf is simply true without
it.  Callers keep passing it — the signature is unchanged — so nothing
downstream moves. -/
theorem exists_weightTwoEigenform_of_heckeOp_eigen_of_level_dvd {N M : ℕ}
    (hN : 0 < N) (_hNM : N ∣ M) {c : ℕ → ℂ} {u : CuspForm (Gamma0GL N) 2}
    (hu : u ≠ 0)
    (hue : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp N q u = c q • u) :
    ∃ M' : ℕ, M' ∣ N ∧ ∃ g' : CuspForm (Gamma0GL M') 2,
      IsWeightTwoEigenform M' g' ∧
        ∀ q : ℕ, q.Prime → ¬ q ∣ M → qCoeff M' g' q = c q := by
  classical
  have hmemE : ∀ x : CuspForm (Gamma0GL N) 2,
      x ∈ (⨅ p : {p : ℕ // p.Prime ∧ ¬ p ∣ M},
            Module.End.eigenspace (heckeOp N p.1) (c p.1)) ↔
        ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp N q x = c q • x := by
    intro x
    rw [Submodule.mem_iInf]
    constructor
    · intro h q hq hqM
      exact Module.End.mem_eigenspace_iff.mp (h ⟨q, hq, hqM⟩)
    · intro h i
      exact Module.End.mem_eigenspace_iff.mpr (h i.1 i.2.1 i.2.2)
  have huE := (hmemE u).mpr hue
  have hEbot : (⨅ p : {p : ℕ // p.Prime ∧ ¬ p ∣ M},
      Module.End.eigenspace (heckeOp N p.1) (c p.1)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨u, huE, hu⟩
  have hstab : ∀ q : ℕ, q.Prime → ∀ x ∈ (⨅ p : {p : ℕ // p.Prime ∧ ¬ p ∣ M},
      Module.End.eigenspace (heckeOp N p.1) (c p.1)),
      heckeOp N q x ∈ (⨅ p : {p : ℕ // p.Prime ∧ ¬ p ∣ M},
        Module.End.eigenspace (heckeOp N p.1) (c p.1)) := by
    intro q hq x hx
    refine (hmemE _).mpr fun r hr hrM => ?_
    have hxr : heckeOp N r x = c r • x := (hmemE x).mp hx r hr hrM
    have hcm : heckeOp N r * heckeOp N q = heckeOp N q * heckeOp N r :=
      heckeOp_mul_comm hN hr hq
    have h1 : heckeOp N r (heckeOp N q x) = heckeOp N q (heckeOp N r x) := by
      have h := congrArg (fun T : Module.End ℂ (CuspForm (Gamma0GL N) 2) => T x) hcm
      simpa using h
    rw [h1, hxr, map_smul]
  obtain ⟨w, hwE, hw0, lam, hlam⟩ :=
    exists_ne_zero_mem_forall_prime_heckeOp_eq_smul hN hEbot hstab
  have hone : qCoeff N w 1 ≠ 0 := fun h0 =>
    hw0 (eq_zero_of_forall_heckeOp_eq_smul_of_qCoeff_one_eq_zero hN hlam h0)
  have hg1 : qCoeff N ((qCoeff N w 1)⁻¹ • w) 1 = 1 := by
    rw [qCoeff_smul, inv_mul_cancel₀ hone]
  have hgl : ∀ q : ℕ, q.Prime →
      heckeOp N q ((qCoeff N w 1)⁻¹ • w) = lam q • ((qCoeff N w 1)⁻¹ • w) := by
    intro q hq
    rw [map_smul, hlam q hq, smul_comm]
  have hgE : IsWeightTwoEigenform N ((qCoeff N w 1)⁻¹ • w) :=
    isWeightTwoEigenform_of_forall_heckeOp_eq_smul hN hgl hg1
  refine ⟨N, dvd_refl N, (qCoeff N w 1)⁻¹ • w, hgE, ?_⟩
  intro q hq hqM
  have h1 : heckeOp N q w = c q • w := (hmemE w).mp hwE q hq hqM
  have h2 : lam q = c q := by
    have h3 : (lam q - c q) • w = 0 := by
      rw [sub_smul, ← hlam q hq, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h hw0
  have h4 : heckeOp N q ((qCoeff N w 1)⁻¹ • w) =
      qCoeff N ((qCoeff N w 1)⁻¹ • w) q • ((qCoeff N w 1)⁻¹ • w) :=
    heckeOp_apply_eq_smul_of_isWeightTwoEigenform hN hgE hq
  have hg0 : ((qCoeff N w 1)⁻¹ • w) ≠ 0 := ne_zero_of_isWeightTwoEigenform hgE
  have h5 : (qCoeff N ((qCoeff N w 1)⁻¹ • w) q - lam q) • ((qCoeff N w 1)⁻¹ • w) = 0 := by
    rw [sub_smul, ← h4, hgl q hq, sub_self]
  rcases smul_eq_zero.mp h5 with h | h
  · linear_combination h + h2
  · exact absurd h hg0

/-- **A STABLE SUBSPACE IS THE SUM OF ITS SIMULTANEOUS GENERALIZED
EIGENCOMPONENTS** (PROVEN 2026-07-26, pure linear algebra over an
algebraically closed field): if a family `T i` of COMMUTING endomorphisms of a
finite-dimensional space `V` preserves a submodule `U`, then `U` is the
supremum of its intersections with the simultaneous maximal generalized
eigenspaces of the family.

This is the companion of `exists_ne_zero_mem_inf_iInf_maxGenEigenspace` above,
and it is what lets a CONTAINMENT between two Hecke-stable subspaces be checked
on joint EIGENVECTORS alone: both sides decompose, so the containment holds iff
it holds in each joint generalized eigenspace.

PROOF.  Simultaneous triangularizability
(`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`)
applied to the operators RESTRICTED to `U` writes the top of `U` as a supremum
of joint generalized eigenspaces of the restrictions; pushing that forward along
the inclusion `U.subtype` with
`Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo` turns each summand into
`U ⊓ E ψ`. -/
theorem eq_iSup_inf_iInf_maxGenEigenspace_of_mapsTo
    {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) (U : Submodule K V)
    (hp : ∀ i, Set.MapsTo (T i) U U) :
    U = ⨆ ψ : ι → K, U ⊓ ⨅ i, (T i).maxGenEigenspace (ψ i) := by
  have hcomm' : ∀ i j, Commute ((T i).restrict (hp i)) ((T j).restrict (hp j)) := by
    intro i j
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx := LinearMap.congr_fun (hcomm i j).eq (x : V)
    simpa [LinearMap.restrict_apply, Module.End.mul_apply] using hx
  have htop : ⨆ ψ : ι → K,
      ⨅ i, Module.End.maxGenEigenspace ((T i).restrict (hp i)) (ψ i) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      _ (fun i j _ => hcomm' i j)
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hmap := congrArg (Submodule.map U.subtype) htop
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype] at hmap
  simp only [← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo T U hp] at hmap
  exact hmap.symm

section MiyakeDescent
open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup
  ConjAct
open scoped Pointwise

/-- Two ARITHMETIC subgroups of `GL(2, ℝ)` have finite relative index: both are
commensurable with `SL(2, ℤ)`, and commensurability is transitive. -/
theorem isFiniteRelIndex_of_isArithmetic (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsArithmetic] [ℋ.IsArithmetic] : Subgroup.IsFiniteRelIndex 𝒢 ℋ :=
  ⟨(Subgroup.IsArithmetic.is_commensurable.trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := ℋ)).symm).1⟩

/-- **UPGRADING THE LEVEL OF A CUSP FORM.**  A cusp form for `Γ₁` that happens to
be slash-invariant under a possibly LARGER group `Γ₂` is a cusp form for `Γ₂`.

Holomorphy is unconditional, and the cusp condition transfers because both groups
are arithmetic, so `IsCusp c Γ₁ ↔ IsCusp c 𝒮ℒ ↔ IsCusp c Γ₂`
(`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`); note that NO inclusion between
`Γ₁` and `Γ₂` is needed. -/
theorem exists_cuspForm_of_slash_invariant
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} [Γ₁.IsArithmetic] [Γ₂.IsArithmetic] {k : ℤ}
    (F : CuspForm Γ₁ k) (hinv : ∀ γ ∈ Γ₂, (⇑F : ℍ → ℂ) ∣[k] γ = ⇑F) :
    ∃ G : CuspForm Γ₂ k, ⇑G = ⇑F :=
  ⟨{ toFun := ⇑F
     slash_action_eq' := hinv
     holo' := F.holo'
     zero_at_cusps' := fun hc =>
       F.zero_at_cusps'
         ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁).mpr
           ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₂).mp hc)) }, rfl⟩

/-- **The conjugation criterion for the descent matrix**, in the form Miyake's
Theorem 4.6.4 needs it: for `ρ ∈ Γ₀(N)` whose upper-right entry is divisible by
`p`, the conjugate `δ_p ρ δ_p⁻¹` by `δ_p = [1, 0; 0, p] = heckeRep p 0` lies in
`Γ₀(pN)`.

Conjugation by `δ_p` divides the upper-right entry by `p` (integrality is exactly
`p ∣ ρ₀₁`) and multiplies the lower-left by `p` (so `N ∣ ρ₁₀` becomes
`pN ∣ pρ₁₀`).  This is the level-raising companion of `heckeRep_conj_mem_iff`,
which is the same computation at a single level. -/
theorem heckeRep_zero_conj_mem_Gamma0GL {N p : ℕ} (hp : p.Prime) {ρ : SL(2, ℤ)}
    (hρ : ρ ∈ CongruenceSubgroup.Gamma0 N) (hb : (p : ℤ) ∣ ρ 0 1) :
    heckeRep p 0 * mapGL ℝ ρ * (heckeRep p 0)⁻¹ ∈ Gamma0GL (p * N) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨t, ht⟩ := hb
  have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have h2 := ρ.2
    rwa [Matrix.det_fin_two] at h2
  have hc : ((ρ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hρ
    exact_mod_cast hρ
  have hcz : ((N : ℕ) : ℤ) ∣ ρ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (ρ 1 0) N).mp hc
  have hpc : ((p * N : ℕ) : ℤ) ∣ (p : ℤ) * ρ 1 0 := by
    push_cast
    exact mul_dvd_mul_left (p : ℤ) (by exact_mod_cast hcz)
  refine mem_Gamma0GL_iff.mpr ⟨⟨!![ρ 0 0, t; (p : ℤ) * ρ 1 0, ρ 1 1], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hqt : ρ 0 0 * ρ 1 1 - ((p : ℤ) * t) * ρ 1 0 = 1 := ht ▸ hdet
    linarith [hqt]
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((p : ℤ) * ρ 1 0 : ℤ) : ZMod (p * N)) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpc
  · rw [eq_mul_inv_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      · simp [heckeRep_coe hp0, mapGL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
          Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply,
          Fin.sum_univ_two, ht]
        try ring

/-- **`Γ₀(N)` IS GENERATED BY ITS `p`-INTEGRAL PART TOGETHER WITH THE
TRANSLATIONS**, in the effective form the descent needs: every `ρ ∈ SL(2, ℤ)` can
be moved by translations on BOTH sides into one whose upper-right entry is
divisible by `p`.

Explicitly `T^k ρ T^l` has upper-right entry `(ρ₀₀ + kρ₁₀)·l + (ρ₀₁ + kρ₁₁)`, and
`k ∈ {0, 1}` already suffices to make the coefficient `A = ρ₀₀ + kρ₁₀` a unit mod
`p`: if `p ∤ ρ₀₀` take `k = 0`; otherwise `ρ₀₀ρ₁₁ − ρ₀₁ρ₁₀ = 1` forces `p ∤ ρ₁₀`,
so `k = 1` gives `A ≡ ρ₁₀ ≢ 0`.  Then `l` solves `A·l + B ≡ 0 (mod p)` in the
field `ZMod p`.

Note the lower-left entry is UNCHANGED by this move, so the result stays in
`Γ₀(N)` — that is what makes the two-sided translation legitimate. -/
theorem exists_heckeTMat_mul_mul_dvd_upperRight {p : ℕ} (hp : p.Prime)
    (ρ : SL(2, ℤ)) :
    ∃ k l : ℤ, (p : ℤ) ∣ (heckeTMat k * ρ * heckeTMat l) 0 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have h2 := ρ.2
    rwa [Matrix.det_fin_two] at h2
  -- the upper-right entry of `T^k ρ T^l`, explicitly
  have hmul : ∀ (x y : SL(2, ℤ)) (i j : Fin 2),
      (x * y) i j = x i 0 * y 0 j + x i 1 * y 1 j := by
    intro x y i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hTe : ∀ m : ℤ, (heckeTMat m) 0 0 = 1 ∧ (heckeTMat m) 0 1 = m ∧
      (heckeTMat m) 1 1 = 1 := by
    intro m
    refine ⟨?_, ?_, ?_⟩ <;> simp [heckeTMat]
  have hentry : ∀ k l : ℤ, (heckeTMat k * ρ * heckeTMat l) 0 1
      = (ρ 0 0 + k * ρ 1 0) * l + (ρ 0 1 + k * ρ 1 1) := by
    intro k l
    obtain ⟨hk0, hk1, -⟩ := hTe k
    obtain ⟨-, hl1, hl3⟩ := hTe l
    rw [hmul (heckeTMat k * ρ) (heckeTMat l) 0 1, hmul (heckeTMat k) ρ 0 0,
      hmul (heckeTMat k) ρ 0 1, hk0, hk1, hl1, hl3]
    ring
  -- choose `k ∈ {0, 1}` making the coefficient `A` prime to `p`
  have hk : ∃ k : ℤ, ¬ (p : ℤ) ∣ (ρ 0 0 + k * ρ 1 0) := by
    by_cases h00 : (p : ℤ) ∣ ρ 0 0
    · have h10 : ¬ (p : ℤ) ∣ ρ 1 0 := by
        intro h10
        have : (p : ℤ) ∣ 1 := by
          rw [← hdet]
          exact dvd_sub (Dvd.dvd.mul_right h00 _) (Dvd.dvd.mul_left h10 _)
        have hp1 : ((p : ℕ) : ℤ) = 1 :=
          Int.eq_one_of_dvd_one (by positivity) this
        exact hp.one_lt.ne' (by exact_mod_cast hp1)
      refine ⟨1, fun hcon => h10 ?_⟩
      have hsub : (p : ℤ) ∣ (ρ 0 0 + 1 * ρ 1 0) - ρ 0 0 := dvd_sub hcon h00
      simpa using hsub
    · exact ⟨0, by simpa using h00⟩
  obtain ⟨k, hA⟩ := hk
  set A : ℤ := ρ 0 0 + k * ρ 1 0 with hAdef
  set B : ℤ := ρ 0 1 + k * ρ 1 1 with hBdef
  -- solve `A·l + B ≡ 0 (mod p)` in the field `ZMod p`
  have hAne : (A : ZMod p) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hA
  refine ⟨k, ((-(B : ZMod p) * (A : ZMod p)⁻¹).val : ℤ), ?_⟩
  rw [hentry, ← hAdef, ← hBdef, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  field_simp
  ring

/-- **THE ANALYTIC HEART OF MIYAKE 4.6.4**: a cusp form supported on the
multiples of `p` is invariant under the FRACTIONAL translation `z ↦ z + 1/p`, in
the slash form `f ∣₂ [1,1;0,p] = f ∣₂ [1,0;0,p]`.

Both sides are `f((τ+j)/p)/p` for `j = 1, 0`; substituting the `q`-expansion of
`f` and using `qParam 1 ((z+j)/p) = qParam p z · e^{2πij/p}`, the two summand
families agree TERMWISE: at an index `n` with `p ∣ n` the root of unity
`e^{2πin/p}` is `1`, and at every other `n` the coefficient `a_n(f)` VANISHES by
hypothesis.  `HasSum.unique` then equates the values.

This is the only place the coefficient hypothesis is used, and it is exactly why
the descended function is `1`-periodic. -/
theorem heckeRep_one_slash_eq_of_qCoeff_eq_zero_of_not_dvd {M p : ℕ}
    (hp : p.Prime) {f : CuspForm (Gamma0GL M) 2}
    (hf : ∀ n : ℕ, ¬ p ∣ n → qCoeff M f n = 0) :
    (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 1 = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
  have hppos : 0 < p := hp.pos
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f
      (one_mem_strictPeriods_Gamma0GL M)
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty ⇑f := by
    have hc : IsCusp OnePoint.infty (Gamma0GL M) :=
      (Gamma0GL M).isCusp_of_mem_strictPeriods one_pos
        (one_mem_strictPeriods_Gamma0GL M)
    exact (OnePoint.isZeroAt_infty_iff.mp
      (CuspFormClass.zero_at_cusps f hc)).boundedAtFilter
  have hsumf : ∀ τ : ℍ, HasSum
      (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 ↑τ ^ n) (f τ) :=
    fun τ => hasSum_qExpansion one_pos hper (CuspFormClass.holo f) hbdd τ
  funext τ
  rw [heckeRep_slash_apply hppos 1 ⇑f τ, heckeRep_slash_apply hppos 0 ⇑f τ]
  congr 1
  have h1 := hsumf (heckeRep p 1 • τ)
  have h0 := hsumf (heckeRep p 0 • τ)
  rw [heckeRep_smul_coe hppos 1 τ] at h1
  rw [heckeRep_smul_coe hppos 0 τ] at h0
  have hfun : (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 (((τ : ℂ) + ((1 : ℕ) : ℂ)) / (p : ℂ)) ^ n)
      = (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 (((τ : ℂ) + ((0 : ℕ) : ℂ)) / (p : ℂ)) ^ n) := by
    funext n
    by_cases hd : p ∣ n
    · rw [qParam_shift hp0 1 ↑τ, qParam_shift hp0 0 ↑τ, mul_pow, mul_pow]
      have hzeta : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) : ℂ) / (p : ℂ)) ^ n
          = 1 := by
        rw [← Complex.exp_nat_mul]
        have : (n : ℂ) * (2 * Real.pi * Complex.I * ((1 : ℕ) : ℂ) / (p : ℂ))
            = 2 * Real.pi * Complex.I * (n : ℂ) / (p : ℂ) := by
          push_cast; ring
        rw [this]
        exact (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hppos.ne').mpr hd
      have hzero : Complex.exp (2 * Real.pi * Complex.I * ((0 : ℕ) : ℂ) / (p : ℂ)) ^ n
          = 1 := by
        norm_num
      rw [hzeta, hzero]
    · rw [show (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n = qCoeff M f n from rfl,
        hf n hd]
      simp
  rw [hfun] at h1
  exact HasSum.unique h1 h0

/-- **MIYAKE THEOREM 4.6.4: A FORM SUPPORTED ON THE MULTIPLES OF `p` DESCENDS TO
LEVEL `M/p`**, in the shape the Main Lemma consumes it: the function
`z ↦ f(z/p)` is a cusp form for `Γ₀(M/p)`, and its `q`-expansion coefficients are
`a_m ↦ a_{pm}(f)`.

The three ingredients are
`heckeRep_one_slash_eq_of_qCoeff_eq_zero_of_not_dvd` (invariance under the
translation `T`, the ONLY step using the coefficient hypothesis),
`heckeRep_zero_conj_mem_Gamma0GL` (invariance under the elements of `Γ₀(M/p)`
whose upper-right entry is divisible by `p`), and
`exists_heckeTMat_mul_mul_dvd_upperRight` (those two together already exhaust
`Γ₀(M/p)`).  Holomorphy and cusp vanishing travel along `CuspForm.translate` and
`exists_cuspForm_of_slash_invariant`. -/
theorem exists_cuspForm_descent_of_qCoeff_eq_zero_of_not_dvd {M p : ℕ}
    (hM : 0 < M) (hp : p.Prime) (hpM : p ∣ M)
    {f : CuspForm (Gamma0GL M) 2}
    (hf : ∀ n : ℕ, ¬ p ∣ n → qCoeff M f n = 0) :
    ∃ g : CuspForm (Gamma0GL (M / p)) 2,
      ∀ m : ℕ, qCoeff (M / p) g m = qCoeff M f (p * m) := by
  have hppos : 0 < p := hp.pos
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set N : ℕ := M / p with hNdef
  have hMN : p * N = M := Nat.mul_div_cancel' hpM
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, mul_zero] at hMN; omega
    · exact h
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI hΓc := heckeConj_isArithmetic (N := M) hp
  -- the translate of `f` by `δ_p = [1, 0; 0, p]`, a cusp form on the conjugate
  set F₀ : CuspForm (toConjAct (heckeRep p 0)⁻¹ • Gamma0GL M) 2 :=
    CuspForm.translate f (heckeRep p 0) with hF₀
  have hF₀coe : (⇑F₀ : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := rfl
  -- invariance under the translations `T^m`
  have hT : ∀ m : ℤ, ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0) ∣[(2 : ℤ)]
      mapGL ℝ (heckeTMat m) = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
    have hone : ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0) ∣[(2 : ℤ)]
        mapGL ℝ (heckeTMat 1) = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
      rw [← SlashAction.slash_mul]
      have : heckeRep p 0 * mapGL ℝ (heckeTMat ((1 : ℕ) : ℤ)) = heckeRep p 1 :=
        heckeRep_zero_mul_heckeTMat hp0 1
      simp only [Nat.cast_one] at this
      rw [this]
      exact heckeRep_one_slash_eq_of_qCoeff_eq_zero_of_not_dvd hp hf
    have hzeroT : heckeTMat (0 : ℤ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [heckeTMat]
    have hnegone : ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0) ∣[(2 : ℤ)]
        mapGL ℝ (heckeTMat (-1)) = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
      have hcancel : (((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0) ∣[(2 : ℤ)]
          mapGL ℝ (heckeTMat 1)) ∣[(2 : ℤ)] mapGL ℝ (heckeTMat (-1))
          = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
        rw [← SlashAction.slash_mul, ← map_mul, heckeTMat_mul, add_neg_cancel,
          hzeroT, map_one, SlashAction.slash_one]
      rwa [hone] at hcancel
    intro m
    induction m using Int.induction_on with
    | zero => rw [hzeroT, map_one, SlashAction.slash_one]
    | succ n ih =>
      have hsplit : heckeTMat ((n : ℤ) + 1) = heckeTMat (n : ℤ) * heckeTMat 1 :=
        (heckeTMat_mul (n : ℤ) 1).symm
      rw [hsplit, map_mul, SlashAction.slash_mul, ih, hone]
    | pred n ih =>
      have hsplit : heckeTMat (-(n : ℤ) - 1) =
          heckeTMat (-(n : ℤ)) * heckeTMat (-1) := by
        rw [heckeTMat_mul]; ring_nf
      rw [hsplit, map_mul, SlashAction.slash_mul, ih, hnegone]
  -- invariance under all of `Γ₀(N)`
  have hinv : ∀ γ ∈ Gamma0GL N, (⇑F₀ : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑F₀ := by
    intro γ hγ
    obtain ⟨ρ, hρ, rfl⟩ := mem_Gamma0GL_iff.mp hγ
    obtain ⟨k, l, hkl⟩ := exists_heckeTMat_mul_mul_dvd_upperRight hp ρ
    set ρ' : SL(2, ℤ) := heckeTMat k * ρ * heckeTMat l with hρ'def
    have hρ'mem : ρ' ∈ CongruenceSubgroup.Gamma0 N :=
      Subgroup.mul_mem _
        (Subgroup.mul_mem _ (heckeTMat_mem_Gamma0 N k) hρ) (heckeTMat_mem_Gamma0 N l)
    -- `f ∣ δ_p` is invariant under `ρ'`
    have hρ'inv : ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0) ∣[(2 : ℤ)] mapGL ℝ ρ'
        = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] heckeRep p 0 := by
      have hconj : heckeRep p 0 * mapGL ℝ ρ' * (heckeRep p 0)⁻¹ ∈ Gamma0GL M := by
        rw [← hMN]
        exact heckeRep_zero_conj_mem_Gamma0GL hp hρ'mem hkl
      have hsplit : heckeRep p 0 * mapGL ℝ ρ'
          = (heckeRep p 0 * mapGL ℝ ρ' * (heckeRep p 0)⁻¹) * heckeRep p 0 := by
        group
      rw [← SlashAction.slash_mul, hsplit, SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq f _ hconj]
    -- decompose `ρ = T^{-k} ρ' T^{-l}`
    have hdecomp : ρ = heckeTMat (-k) * ρ' * heckeTMat (-l) := by
      rw [hρ'def]
      rw [← mul_assoc, ← mul_assoc, heckeTMat_mul, neg_add_cancel]
      have h1 : heckeTMat (0 : ℤ) = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [heckeTMat]
      rw [h1, one_mul, mul_assoc, heckeTMat_mul, add_neg_cancel, h1, mul_one]
    rw [hF₀coe, hdecomp, map_mul, map_mul, SlashAction.slash_mul,
      SlashAction.slash_mul, hT (-k), hρ'inv, hT (-l)]
  obtain ⟨G₀, hG₀⟩ := exists_cuspForm_of_slash_invariant (Γ₂ := Gamma0GL N) F₀ hinv
  refine ⟨(p : ℂ) • G₀, ?_⟩
  -- the `q`-expansion of `p · (f ∣ δ_p)`, i.e. of `z ↦ f(z/p)`
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f
      (one_mem_strictPeriods_Gamma0GL M)
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty ⇑f := by
    have hc : IsCusp OnePoint.infty (Gamma0GL M) :=
      (Gamma0GL M).isCusp_of_mem_strictPeriods one_pos
        (one_mem_strictPeriods_Gamma0GL M)
    exact (OnePoint.isZeroAt_infty_iff.mp
      (CuspFormClass.zero_at_cusps f hc)).boundedAtFilter
  have hsumf : ∀ τ : ℍ, HasSum
      (fun n : ℕ => (qExpansion 1 ⇑f).coeff n •
        Function.Periodic.qParam 1 ↑τ ^ n) (f τ) :=
    fun τ => hasSum_qExpansion one_pos hper (CuspFormClass.holo f) hbdd τ
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hppos h
  have hmaster : ∀ τ : ℍ, HasSum
      (fun m : ℕ => qCoeff M f (p * m) •
        Function.Periodic.qParam 1 ↑τ ^ m) (((p : ℂ) • G₀) τ) := by
    intro τ
    have hval : ((p : ℂ) • G₀) τ = f (heckeRep p 0 • τ) := by
      rw [CuspForm.IsGLPos.coe_smul]
      show (p : ℂ) * G₀ τ = _
      rw [hG₀, hF₀coe, heckeRep_slash_apply hppos 0 ⇑f τ]
      field_simp
    rw [hval]
    have hs := hsumf (heckeRep p 0 • τ)
    rw [heckeRep_smul_coe hppos 0 τ] at hs
    -- rewrite the parameter: `qParam 1 ((τ+0)/p) = qParam p τ`
    have hq : Function.Periodic.qParam 1 (((τ : ℂ) + ((0 : ℕ) : ℂ)) / (p : ℂ))
        = Function.Periodic.qParam (p : ℝ) (τ : ℂ) := by
      rw [qParam_shift hp0 0 ↑τ]
      norm_num
    rw [hq] at hs
    -- drop the indices not divisible by `p`, then reindex `n = p·m`
    have h0 : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => p * m) →
        ((qExpansion 1 ⇑f).coeff n •
          Function.Periodic.qParam (p : ℝ) (τ : ℂ) ^ n) = 0 := by
      intro n hn
      have hnd : ¬ p ∣ n := fun ⟨t, ht⟩ => hn ⟨t, ht.symm⟩
      rw [show (qExpansion 1 ⇑f).coeff n = qCoeff M f n from rfl, hf n hnd,
        zero_smul]
    have hs2 := (Function.Injective.hasSum_iff hinj h0).mpr hs
    have hfun : (fun m : ℕ => (qExpansion 1 ⇑f).coeff (p * m) •
          Function.Periodic.qParam (p : ℝ) (τ : ℂ) ^ (p * m))
        = fun m : ℕ => qCoeff M f (p * m) •
            Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
      funext m
      rw [pow_mul, qParam_nat_pow hp0 (τ : ℂ)]
      rfl
    rw [Function.comp_def, hfun] at hs2
    exact hs2
  intro m
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma0GL N) (f := (p : ℂ) • G₀) hmaster m).symm

/-- The slash conjugation factor `σ` is trivial on `Γ₀(N)`: its elements have
determinant `1 > 0`. -/
theorem σ_Gamma0GL {N : ℕ} {x : GL (Fin 2) ℝ} (hx : x ∈ Gamma0GL N) (c : ℂ) :
    σ x c = c := by
  have hdet : (0 : ℝ) < (x.det.val : ℝ) := by
    simp [Subgroup.HasDetOne.det_eq hx]
  simp only [σ, if_pos hdet, ContinuousAlgEquiv.refl_apply]

/-- Additivity of `SlashInvariantForm.quotientFunc` in the form. -/
theorem quotientFunc_add {M N : ℕ}
    (f g : CuspForm (Gamma0GL M) 2)
    (q : Gamma0GL N ⧸ (Gamma0GL M).subgroupOf (Gamma0GL N)) :
    SlashInvariantForm.quotientFunc (f + g) q =
      SlashInvariantForm.quotientFunc f q + SlashInvariantForm.quotientFunc g q := by
  induction q using Quotient.inductionOn with
  | h r => simp

/-- Homogeneity of `SlashInvariantForm.quotientFunc` in the form (the coset
representatives lie in `Γ₀(N)`, so the `σ`-factor is trivial). -/
theorem quotientFunc_smul_complex {M N : ℕ} (c : ℂ)
    (f : CuspForm (Gamma0GL M) 2)
    (q : Gamma0GL N ⧸ (Gamma0GL M).subgroupOf (Gamma0GL N)) :
    SlashInvariantForm.quotientFunc (c • f) q =
      c • SlashInvariantForm.quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    have hmem : ((r : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ ∈ Gamma0GL N := inv_mem r.2
    simp only [SlashInvariantForm.quotientFunc_mk, CuspForm.IsGLPos.coe_smul]
    rw [ModularForm.smul_slash, σ_Gamma0GL hmem]

/-- **THE TRACE OPERATOR `Tr : S₂(Γ₀(M)) → S₂(Γ₀(N))`** — Miyake, *Modular
Forms*, Lemma 4.6.6's double-coset operator `[Γ₀(M) · 1 · Γ₀(N)]`, i.e.
`h ↦ Σ_v h ∣₂ γ_v` summed over the finite coset space `Γ₀(M) \ Γ₀(N)`.

**AUDIT CORRECTION (2026-07-27).**  The docstrings below record that "the one
genuinely missing piece of INFRASTRUCTURE is the TRACE operator
`S₂(Γ₀(N)) → S₂(Γ₀(N/p))`, which this file does not yet have".  That is FALSE
twice over: the trace is in the PIN as `CuspForm.trace`
(`Mathlib/NumberTheory/ModularForms/NormTrace.lean`, David Loeffler), and this
file has been CONSUMING it since the Hecke operator was built —
`exists_cuspForm_heckeTransform` above is proven by identifying the Hecke
slash-sum with exactly this trace.  All that was missing is the present wrapper,
which packages it as a `ℂ`-linear map between the two level-indexed spaces.

The finiteness hypothesis `CuspForm.trace` needs is
`(Γ₀(M)).IsFiniteRelIndex (Γ₀(N))`, supplied by
`isFiniteRelIndex_of_isArithmetic`: both groups are arithmetic, hence
commensurable through `SL(2, ℤ)`.  NOTE this needs NO divisibility relation
between `M` and `N` — the trace is defined from `Γ₀(M) ⊓ Γ₀(N)` up to `Γ₀(N)`,
and it is only for `N ∣ M` (where `Γ₀(M) ≤ Γ₀(N)`) that it is the classical
trace. -/
noncomputable def traceOp (M N : ℕ) [NeZero M] [NeZero N] :
    CuspForm (Gamma0GL M) 2 →ₗ[ℂ] CuspForm (Gamma0GL N) 2 :=
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL M) (Gamma0GL N) :=
    isFiniteRelIndex_of_isArithmetic _ _
  { toFun := fun f => CuspForm.trace (Gamma0GL N) f
    map_add' := by
      intro f g
      refine DFunLike.coe_injective ?_
      letI : Fintype (Gamma0GL N ⧸ (Gamma0GL M).subgroupOf (Gamma0GL N)) :=
        Fintype.ofFinite _
      simp only [CuspForm.coe_trace, CuspForm.coe_add]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => quotientFunc_add f g q
    map_smul' := by
      intro c f
      refine DFunLike.coe_injective ?_
      letI : Fintype (Gamma0GL N ⧸ (Gamma0GL M).subgroupOf (Gamma0GL N)) :=
        Fintype.ofFinite _
      simp only [CuspForm.coe_trace, RingHom.id_apply, CuspForm.IsGLPos.coe_smul,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ => quotientFunc_smul_complex c f q }

end MiyakeDescent

/-- **MIYAKE THEOREM 4.6.4: A FORM SUPPORTED ON THE MULTIPLES OF `p` DESCENDS TO
LEVEL `M/p`** (PROVEN 2026-07-27 over the Miyake toolkit above; cut out of
`mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero` below; Miyake,
*Modular Forms*, Theorem 4.6.4, at `l = p` prime, weight `2`, trivial
character): if every `q`-expansion coefficient of `f ∈ S₂(Γ₀(M))` at an index
NOT divisible by the prime `p ∣ M` vanishes, then `f = V_p g` for some
`g ∈ S₂(Γ₀(M/p))`.

This is the single-prime case of the Main Lemma and the engine of the general
case: it is the ONLY place where the descent from level `M` to level `M/p`
actually happens.

PROOF AS FORMALIZED (Miyake, pp. 155–157, with the group-generation step
rearranged into the two-sided form that is effective in Lean).  The witness is
the honest function `g(z) = f(z/p)`, i.e. `p · (f ∣₂ δ_p)` for
`δ_p = [1, 0; 0, p] = heckeRep p 0`, packaged by
`exists_cuspForm_descent_of_qCoeff_eq_zero_of_not_dvd` above.  Its three
ingredients are:

* **holomorphy and cusp vanishing** travel along the pin's `CuspForm.translate`
  (a cusp form on the arithmetic conjugate `δ_p⁻¹Γ₀(M)δ_p`,
  `heckeConj_isArithmetic`) and then along
  `exists_cuspForm_of_slash_invariant`, which upgrades the level using only
  that BOTH groups are arithmetic — `IsCusp` is then the same condition on
  both sides (`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`);
* **invariance under the `γ ∈ Γ₀(M/p)` with `p ∣ γ₀₁`** is the direct
  conjugation computation `δ_p γ δ_p⁻¹ ∈ Γ₀(M)`
  (`heckeRep_zero_conj_mem_Gamma0GL`: conjugation divides `γ₀₁` by `p` and
  multiplies `γ₁₀` by `p`, and `M/p ∣ γ₁₀` becomes `M ∣ pγ₁₀`);
* **invariance under the remaining `γ`** because translations on BOTH sides
  move any `γ` into that subgroup — `T^k γ T^l` has upper-right entry
  `(γ₀₀ + kγ₁₀)·l + (γ₀₁ + kγ₁₁)` and leaves `γ₁₀` alone, so `k ∈ {0, 1}` makes
  the coefficient a unit mod `p` and `l` then solves the congruence
  (`exists_heckeTMat_mul_mul_dvd_upperRight`).  Invariance under `T` itself is
  where — and the ONLY place where — the coefficient hypothesis enters
  (`heckeRep_one_slash_eq_of_qCoeff_eq_zero_of_not_dvd`): `f(z + 1/p) = f(z)`
  because the two `q`-expansions agree TERMWISE, the root of unity `e^{2πin/p}`
  being `1` at `p ∣ n` and the coefficient `a_n(f)` vanishing otherwise.

Finally `a_m(g) = a_{pm}(f)` by reindexing that same expansion along `n = pm`,
and `V_p g = f` follows coefficientwise from `qCoeff_degeneracyOp`.

`p ∤ M` is the other branch of Miyake's theorem and gives `f = 0` via Hecke's
Lemma 4.6.3; it is not needed here, since the consumer only ever peels a prime
that divides the level.

FAITHFULNESS.  `0 < M` is load-bearing: at `M = 0` the statement would assert a
descent to `Γ₀(0)`.  The statement is NOT vacuous — `f = V_p g` for any
`g ∈ S₂(Γ₀(M/p))` satisfies the hypothesis by `qCoeff_degeneracyOp`, and such
`g` are nonzero for suitable `M` (e.g. `M = 2·11²` over `M/p = 11²`). -/
theorem mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd {M p : ℕ}
    (hM : 0 < M) (hp : p.Prime) (hpM : p ∣ M)
    {f : CuspForm (Gamma0GL M) 2}
    (hf : ∀ n : ℕ, ¬ p ∣ n → qCoeff M f n = 0) :
    f ∈ LinearMap.range (degeneracyOp (M / p) M p) := by
  obtain ⟨g, hg⟩ :=
    exists_cuspForm_descent_of_qCoeff_eq_zero_of_not_dvd hM hp hpM hf
  have hdvd : p * (M / p) ∣ M := by
    rw [Nat.mul_div_cancel' hpM]
  refine ⟨g, cuspForm_eq_of_forall_qCoeff_eq fun n => ?_⟩
  rw [qCoeff_degeneracyOp hp.pos hdvd g n]
  by_cases hn : p ∣ n
  · rw [if_pos hn, hg (n / p), Nat.mul_div_cancel' hn]
  · rw [if_neg hn, (hf n hn).symm]

section MiyakeTraceBookkeeping
open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup

/-- `V_1` is the identity transform on functions: `heckeRepInf 1` is the identity
matrix and the slash by it is trivial. -/
theorem degeneracyTransform_one (f : ℍ → ℂ) : degeneracyTransform 1 f = f := by
  have hne : ((1 : ℕ) : ℝ) ≠ 0 := by norm_num
  have h1 : heckeRepInf 1 = 1 := by
    have hc := heckeRepInf_coe hne
    ext i j
    rw [hc]
    fin_cases i <;> fin_cases j <;> simp
  unfold degeneracyTransform
  rw [h1]
  simp

/-- **`V_1` IS THE LEVEL-RAISING INCLUSION, ON COEFFICIENTS**: `a_m(V_1 f) =
a_m(f)`.  This is the operator that views a level-`N` form at the larger level
`M`, and it is how Miyake's argument moves `f` up to level `M L²` and the answer
back down. -/
theorem qCoeff_degeneracyOp_one {N M : ℕ} (hdvd : N ∣ M)
    (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff M (degeneracyOp N M 1 f) m = qCoeff N f m := by
  rw [qCoeff_degeneracyOp one_pos (by simpa using hdvd) f m]
  simp

/-- `V_1` does not change the underlying function either. -/
theorem coe_degeneracyOp_one {N M : ℕ} (hdvd : N ∣ M) (f : CuspForm (Gamma0GL N) 2) :
    ⇑(degeneracyOp N M 1 f) = ⇑f := by
  rw [degeneracyOp_coe one_pos (by simpa using hdvd) f, degeneracyTransform_one]

/-- Additivity of the `q`-expansion coefficients, through `qCoeffL`. -/
theorem qCoeff_add {N : ℕ} (f g : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff N (f + g) m = qCoeff N f m + qCoeff N g m := by
  have h := (qCoeffL N m).map_add f g
  simpa using h

/-- Subtractivity of the `q`-expansion coefficients, through `qCoeffL`. -/
theorem qCoeff_sub {N : ℕ} (f g : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    qCoeff N (f - g) m = qCoeff N f m - qCoeff N g m := by
  have h := (qCoeffL N m).map_sub f g
  simpa using h

/-- **THE TRACE OF A FORM INDUCED FROM THE SMALLER LEVEL IS A NONZERO MULTIPLE OF
IT** (PROVEN): `Tr^A_B (V_1 u) = [Γ₀(B) : Γ₀(A)] · u`.

`CuspForm.trace` sums `⇑F ∣[2] γ⁻¹` over `Γ₀(B) ⧸ Γ₀(A).subgroupOf Γ₀(B)`, and
when `F` is induced from level `B` every summand is `⇑u` itself, so the sum is
the index times `u`.  The index is a nonzero natural number because the quotient
is finite (`isFiniteRelIndex_of_isArithmetic`) and nonempty.

This is the lemma that makes the trace COMPUTABLE at the one place Miyake needs
it, and it is also exactly what refutes the `traceOp`-pinned leaf below: a form
that is already `Γ₀(M/p)`-invariant has trace a multiple of ITSELF, which is far
too little information to recover `a_{pm}(f)`. -/
theorem exists_smul_traceOp_degeneracyOp_one {A B : ℕ} [NeZero A] [NeZero B]
    (hdvd : B ∣ A) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ u : CuspForm (Gamma0GL B) 2,
      traceOp A B (degeneracyOp B A 1 u) = κ • u := by
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL A) (Gamma0GL B) :=
    isFiniteRelIndex_of_isArithmetic _ _
  letI : Fintype (Gamma0GL B ⧸ (Gamma0GL A).subgroupOf (Gamma0GL B)) := Fintype.ofFinite _
  refine ⟨(Fintype.card (Gamma0GL B ⧸ (Gamma0GL A).subgroupOf (Gamma0GL B)) : ℂ), ?_, ?_⟩
  · have : 0 < Fintype.card (Gamma0GL B ⧸ (Gamma0GL A).subgroupOf (Gamma0GL B)) :=
      Fintype.card_pos
    exact_mod_cast this.ne'
  · intro u
    refine DFunLike.coe_injective ?_
    have hcoe : ⇑(degeneracyOp B A 1 u) = ⇑u := coe_degeneracyOp_one hdvd u
    show ⇑(CuspForm.trace (Gamma0GL B) (degeneracyOp B A 1 u)) = _
    rw [CuspForm.coe_trace, CuspForm.IsGLPos.coe_smul]
    have hq : ∀ q : Gamma0GL B ⧸ (Gamma0GL A).subgroupOf (Gamma0GL B),
        SlashInvariantForm.quotientFunc (degeneracyOp B A 1 u) q = ⇑u := by
      intro q
      induction q using Quotient.inductionOn with
      | h r =>
        rw [SlashInvariantForm.quotientFunc_mk, hcoe]
        exact SlashInvariantFormClass.slash_action_eq u r.val⁻¹ (inv_mem r.2)
    rw [Finset.sum_congr rfl fun q _ => hq q]
    funext x
    simp [Finset.sum_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **MIYAKE LEMMA 4.6.5 AT A PRIME — THE `p`-SIEVE, AT LEVEL `A p²`** (PROVEN
2026-07-28): for `f ∈ S₂(Γ₀(A))` and a prime `p`, the series obtained by DELETING
the coefficients at indices divisible by `p` is a cusp form of level `A p²`.

PROOF AS FORMALIZED, which replaces Miyake's `f ∣ T(p)` Fourier computation by
the `q`-expansion toolkit already proven above.  The witness is

    g  =  V_1 f  −  V_p (U_p^{(pA)} (V_1 f))       in  S₂(Γ₀(A p²)).

`V_1` first lifts `f` to level `pA`, which is exactly what makes the Hecke
operator there a plain `U_p`: `qCoeff_heckeOp` carries the correction term
`p·a_{m/p}` only at `p ∤ M`, and here `p ∣ pA`, so
`a_m(U_p V_1 f) = a_{pm}(f)` with no correction.  Pushing that back up by `V_p`
gives `a_n(V_p U_p V_1 f) = a_n(f)` at `p ∣ n` and `0` otherwise
(`qCoeff_degeneracyOp`), i.e. EXACTLY the part being removed.  The level is
forced by `V_p` out of level `pA`, which needs `p·(pA) = A p² ∣ B`. -/
theorem exists_cuspForm_qCoeff_sieve_prime {A B p : ℕ} (hA : 0 < A) (hp : p.Prime)
    (hB : A * p ^ 2 = B) (f : CuspForm (Gamma0GL A) 2) :
    ∃ g : CuspForm (Gamma0GL B) 2,
      ∀ n : ℕ, qCoeff B g n = if p ∣ n then 0 else qCoeff A f n := by
  have hA' : 0 < p * A := Nat.mul_pos hp.pos hA
  have hAA' : A ∣ p * A := ⟨p, mul_comm p A⟩
  have hpA' : p ∣ p * A := ⟨A, rfl⟩
  have hAB : A ∣ B := ⟨p ^ 2, hB.symm⟩
  have hpA'B : p * (p * A) ∣ B := ⟨1, by rw [← hB]; ring⟩
  have hucoeff : ∀ m : ℕ,
      qCoeff (p * A) (heckeOp (p * A) p (degeneracyOp A (p * A) 1 f)) m
        = qCoeff A f (p * m) := by
    intro m
    rw [qCoeff_heckeOp hA' hp _ m, if_pos hpA', add_zero,
      qCoeff_degeneracyOp_one hAA' f (p * m)]
  refine ⟨degeneracyOp A B 1 f
    - degeneracyOp (p * A) B p (heckeOp (p * A) p (degeneracyOp A (p * A) 1 f)), fun n => ?_⟩
  rw [qCoeff_sub, qCoeff_degeneracyOp_one hAB f n, qCoeff_degeneracyOp hp.pos hpA'B _ n]
  by_cases hn : p ∣ n
  · rw [if_pos hn, if_pos hn, hucoeff (n / p), Nat.mul_div_cancel' hn, sub_self]
  · rw [if_neg hn, if_neg hn, sub_zero]

/-- **MIYAKE LEMMA 4.6.5 — THE `L`-SIEVE RAISES THE LEVEL BY `L²`** (PROVEN
2026-07-28 over `exists_cuspForm_qCoeff_sieve_prime`; Miyake, *Modular Forms*,
Lemma 4.6.5, pp. 157–158): for
`f ∈ S₂(Γ₀(A))` and `L ≥ 1`, the series obtained by KEEPING ONLY the coefficients
at indices coprime to `L`,

    g(z) = Σ_{(n, L) = 1} a_n(f) qⁿ,

is again a cusp form, of level `A L²`.

Miyake's level is the sharper `A · Π_{p ∣ L, p ∣ A} p · Π_{p ∣ L, p ∤ A} p²`,
which divides `A L²`; `A L²` is all the peeling step needs and it keeps the
statement free of factorization bookkeeping.  The level is passed as a VARIABLE
`B` with the defining equation `A * L ^ 2 = B` so that consumers can instantiate
it at whatever normal form their arithmetic produces, without a dependent-type
rewrite of `CuspForm (Gamma0GL ·) 2`.

PROOF AS FORMALIZED: strong induction on `L`, one prime at a time.  `L = 1` is
`V_1`.  Otherwise pick a prime `p ∣ L`, write `L = p·L'`, apply the single-prime
sieve `exists_cuspForm_qCoeff_sieve_prime` to reach level `A p²`, and apply the
induction hypothesis at `L' < L` from there to level `A p² L'² = A L² = B`.  The
coefficient bookkeeping is `Nat.coprime_mul_iff_right`: `(n, p·L') = 1` iff
`p ∤ n` and `(n, L') = 1`, which is exactly the composition of the two sieves.
Iterating over the prime factors WITH MULTIPLICITY is harmless — a repeated
prime only inflates the level, and the level `A L²` is stated as an upper bound
rather than the sharp one.

WHY THE LEVEL MUST GO UP, and why the naive inclusion–exclusion sieve fails: this
is the only step of Miyake's induction that leaves level `A`, and move 3 is what
brings the answer back down.  Recorded because two audits of the peeling step
mistook it for avoidable. -/
theorem exists_cuspForm_qCoeff_sieve {A B L : ℕ} (hA : 0 < A) (hL : 0 < L)
    (hB : A * L ^ 2 = B) (f : CuspForm (Gamma0GL A) 2) :
    ∃ g : CuspForm (Gamma0GL B) 2,
      ∀ n : ℕ, qCoeff B g n = if Nat.Coprime n L then qCoeff A f n else 0 := by
  suffices H : ∀ K : ℕ, 0 < K → ∀ A B : ℕ, 0 < A → A * K ^ 2 = B →
      ∀ f : CuspForm (Gamma0GL A) 2, ∃ g : CuspForm (Gamma0GL B) 2,
        ∀ n : ℕ, qCoeff B g n = if Nat.Coprime n K then qCoeff A f n else 0 by
    exact H L hL A B hA hB f
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro hK A B hA hB f
    rcases eq_or_ne K 1 with hK1 | hK1
    · subst hK1
      refine ⟨degeneracyOp A B 1 f, fun n => ?_⟩
      rw [qCoeff_degeneracyOp_one ⟨1, by rw [← hB]; ring⟩ f n,
        if_pos (Nat.coprime_one_right n)]
    · obtain ⟨p, hp, hpK⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ K :=
        ⟨K.minFac, Nat.minFac_prime hK1, Nat.minFac_dvd K⟩
      obtain ⟨K', hK'⟩ := hpK
      have hK'0 : 0 < K' := Nat.pos_of_ne_zero (by
        rintro rfl
        rw [hK'] at hK
        simp at hK)
      have hK'lt : K' < K := by
        have h2 : 2 * K' ≤ p * K' := Nat.mul_le_mul hp.two_le le_rfl
        have h3 : K' < 2 * K' := by omega
        rw [hK']
        exact lt_of_lt_of_le h3 h2
      obtain ⟨g₁, hg₁⟩ :=
        exists_cuspForm_qCoeff_sieve_prime hA hp (rfl : A * p ^ 2 = A * p ^ 2) f
      obtain ⟨g₂, hg₂⟩ := ih K' hK'lt hK'0 (A * p ^ 2) B (Nat.mul_pos hA (pow_pos hp.pos 2))
        (by rw [← hB, hK']; ring) g₁
      refine ⟨g₂, fun n => ?_⟩
      rw [hg₂ n, hg₁ n]
      have hiff : Nat.Coprime n p ↔ ¬ p ∣ n := by
        rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
      have hcop : Nat.Coprime n K ↔ (¬ p ∣ n ∧ Nat.Coprime n K') := by
        rw [hK', Nat.coprime_mul_iff_right, hiff]
      by_cases hpn : p ∣ n
      · by_cases hc : Nat.Coprime n K'
        · rw [if_pos hc, if_pos hpn, if_neg (fun h => (hcop.mp h).1 hpn)]
        · rw [if_neg hc, if_neg (fun h => hc (hcop.mp h).2)]
      · by_cases hc : Nat.Coprime n K'
        · rw [if_pos hc, if_neg hpn, if_pos (hcop.mpr ⟨hpn, hc⟩)]
        · rw [if_neg hc, if_neg (fun h => hc (hcop.mp h).2)]

/-- **THE COPRIME SHIFT** (PROVEN 2026-07-28): for coprime `a, c` and any
positive modulus `M`, some member `a + b·c` of the arithmetic progression is
coprime to `M`.

Witness: `b = ∏ ℓ` over the primes `ℓ ∣ M` with `ℓ ∤ a`.  At a prime `ℓ ∣ M`
either `ℓ ∤ a`, and then `ℓ ∣ b` so `a + bc ≡ a ≢ 0`; or `ℓ ∣ a`, and then `ℓ ∤ b`
by construction and `ℓ ∤ c` by coprimality, so `a + bc ≡ bc ≢ 0`.

This is the one piece of arithmetic that `exists_gamma0_mul_dvd_lowerLeft` below
needs and that neither mathlib nor `~/cs/FLT` carries; it is the `SL(2, ℤ)`
stable-range statement in the only form this development uses it. -/
theorem exists_add_mul_isCoprime {a c : ℤ} (h : IsCoprime a c) {M : ℕ} (hM : 0 < M) :
    ∃ b : ℤ, IsCoprime (a + b * c) (M : ℤ) := by
  classical
  set S : Finset ℕ := M.primeFactors.filter (fun ℓ => ¬ ((ℓ : ℤ) ∣ a)) with hS
  refine ⟨∏ ℓ ∈ S, (ℓ : ℤ), ?_⟩
  set b : ℤ := ∏ ℓ ∈ S, (ℓ : ℤ) with hb
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_prime_and_dvd hne
  have hℓz : Prime ((ℓ : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hℓp
  have hℓ' : ((ℓ : ℕ) : ℤ) ∣ ((Int.gcd (a + b * c) (M : ℤ) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hℓ
  have h1 : (ℓ : ℤ) ∣ a + b * c := hℓ'.trans (Int.gcd_dvd_left _ _)
  have h2 : (ℓ : ℤ) ∣ (M : ℤ) := hℓ'.trans (Int.gcd_dvd_right _ _)
  have hℓM : ℓ ∈ M.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hℓp, Int.ofNat_dvd.mp h2, hM.ne'⟩
  by_cases ha : ((ℓ : ℤ) ∣ a)
  · have hnotS : ℓ ∉ S := by
      rw [hS, Finset.mem_filter]
      exact fun hc => hc.2 ha
    have hnb : ¬ ((ℓ : ℤ) ∣ b) := by
      intro hdvd
      obtain ⟨m, hmS, hm⟩ := hℓz.exists_mem_finset_dvd hdvd
      have hmp : m.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hS ▸ hmS)).1
      have hdm : ℓ ∣ m := Int.ofNat_dvd.mp hm
      exact hnotS (((Nat.prime_dvd_prime_iff_eq hℓp hmp).mp hdm) ▸ hmS)
    have hbc : (ℓ : ℤ) ∣ b * c := (dvd_add_right ha).mp h1
    rcases hℓz.2.2 _ _ hbc with hcon | hcon
    · exact hnb hcon
    · have hu : IsUnit ((ℓ : ℕ) : ℤ) := h.isUnit_of_dvd' ha hcon
      rw [Int.isUnit_iff] at hu
      rcases hu with hu | hu
      · exact hℓp.one_lt.ne' (by exact_mod_cast hu)
      · have h5 : (0 : ℤ) ≤ (ℓ : ℤ) := Int.natCast_nonneg ℓ
        omega
  · have hbS : (ℓ : ℤ) ∣ b :=
      Finset.dvd_prod_of_mem _ (by rw [hS, Finset.mem_filter]; exact ⟨hℓM, ha⟩)
    have h4 : (ℓ : ℤ) ∣ b * c := hbS.mul_right c
    exact ha (by simpa using dvd_sub h1 h4)

/-- **THE INJECTIVITY INPUT FOR MIYAKE 4.6.6(1)** (PROVEN 2026-07-28): at `p ∤ L`
the two levels `Ap L²` and `p Ap` generate `p Ap L²`, i.e.
`lcm(Ap L², p Ap) = p Ap L²`.

`p ∤ L` is exactly what this needs: at `p ∣ L` the least common multiple is
smaller (e.g. `Ap = 1, p = 2, L = 2` gives `lcm(4, 2) = 4 ≠ 8`), and the coset
map of 4.6.6(1) is then genuinely NOT injective. -/
theorem dvd_mul_sq_of_dvd_mul_sq_of_dvd_mul {Ap p L : ℕ} (hp : p.Prime) (hpL : ¬ p ∣ L)
    (hAp : 0 < Ap) {c : ℤ} (h1 : ((Ap * L ^ 2 : ℕ) : ℤ) ∣ c)
    (h2 : ((p * Ap : ℕ) : ℤ) ∣ c) : ((p * Ap * L ^ 2 : ℕ) : ℤ) ∣ c := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hApz : ((Ap : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hAp.ne'
  have hpz : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcancel : (Ap : ℤ) * ((L : ℤ) ^ 2 * s) = (Ap : ℤ) * ((p : ℤ) * t) := by
    have e1 : c = (Ap : ℤ) * ((L : ℤ) ^ 2 * s) := by rw [hs]; push_cast; ring
    have e2 : c = (Ap : ℤ) * ((p : ℤ) * t) := by rw [ht]; push_cast; ring
    rw [← e1, ← e2]
  have hdvd : ((p : ℤ)) ∣ (L : ℤ) ^ 2 * s := ⟨t, mul_left_cancel₀ hApz hcancel⟩
  have hnpL : ¬ ((p : ℤ)) ∣ (L : ℤ) ^ 2 := by
    intro hc
    exact hpL (Int.ofNat_dvd.mp (hpz.dvd_of_dvd_pow hc))
  have hps : ((p : ℤ)) ∣ s := (hpz.2.2 _ _ hdvd).resolve_left hnpL
  obtain ⟨w, hw⟩ := hps
  exact ⟨w, by rw [hs, hw]; push_cast; ring⟩

/-- The lower-left entry of an `SL(2, ℤ)` product, explicitly — the companion of
`SL2_mul_apply_zero_one`. -/
theorem SL2_mul_apply_one_zero (x y : SL(2, ℤ)) :
    (x * y) 1 0 = x 1 0 * y 0 0 + x 1 1 * y 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **THE SURJECTIVITY INPUT FOR MIYAKE 4.6.6(1)** (PROVEN 2026-07-28): for
`ρ ∈ Γ₀(Ap)`, `p` prime and `p ∤ L`, the coset `ρ Γ₀(p·Ap)` contains a matrix
whose lower-left entry is divisible by `Ap L²`.

This is what makes the coset map of 4.6.6(1) SURJECTIVE without any index
computation — the same device the `V_q` companion `traceOp_degeneracyOp_comm`
below uses, transposed from the upper-right entry to the lower-left one.

PROOF.  Right-multiplication by `[1 + b·A·j, b; A·j, 1] ∈ Γ₀(A)` (`A = p·Ap`)
sends the lower-left entry `ρ₁₀ = Ap·r` to `Ap·(r + p·j·(ρ₁₁ + b·ρ₁₀))`, so it is
enough to solve `r + p·j·X ≡ 0 (mod L²)` with `X = ρ₁₁ + b·ρ₁₀`.  `det ρ = 1`
gives `(ρ₁₁, ρ₁₀) = 1`, so `exists_add_mul_isCoprime` supplies a `b` with
`X` coprime to `L²`; `p ∤ L` makes `p` coprime to `L²` as well; and the two
Bézout identities then produce `j = −r·u·u'` explicitly, with no `ZMod`
inversion.  `p ∤ L` is consumed exactly here and in the injectivity input. -/
theorem exists_gamma0_mul_dvd_lowerLeft {Ap p L : ℕ} (hp : p.Prime) (hpL : ¬ p ∣ L)
    (hL : 0 < L) {ρ : SL(2, ℤ)} (hρ : ρ ∈ CongruenceSubgroup.Gamma0 Ap) :
    ∃ γ ∈ CongruenceSubgroup.Gamma0 (p * Ap), ((Ap * L ^ 2 : ℕ) : ℤ) ∣ (ρ * γ) 1 0 := by
  have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have h2 := ρ.2
    rwa [Matrix.det_fin_two] at h2
  have hcop : IsCoprime (ρ 1 1) (ρ 1 0) := ⟨ρ 0 0, -ρ 0 1, by linear_combination hdet⟩
  obtain ⟨r, hr⟩ : (Ap : ℤ) ∣ ρ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hρ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρ
  obtain ⟨b, hb⟩ := exists_add_mul_isCoprime hcop (M := L ^ 2) (by positivity)
  set X : ℤ := ρ 1 1 + b * ρ 1 0 with hX
  obtain ⟨u, v, huv⟩ := hb
  have hpL2 : IsCoprime ((p : ℕ) : ℤ) ((L ^ 2 : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpL)
  obtain ⟨u', v', huv'⟩ := hpL2
  have hcast : ((L ^ 2 : ℕ) : ℤ) = (L : ℤ) ^ 2 := by push_cast; ring
  rw [hcast] at huv huv'
  set j : ℤ := -(r * u * u') with hj
  have hkey : r + (p : ℤ) * j * X = (L : ℤ) ^ 2 * (r * (v + v' - v * v' * (L : ℤ) ^ 2)) := by
    rw [hj]
    linear_combination (-(r * (u' * (p : ℤ)))) * huv + (-(r * (1 - v * (L : ℤ) ^ 2))) * huv'
  have hdetγ : (!![(1 : ℤ) + b * ((p : ℤ) * (Ap : ℤ)) * j, b;
      ((p : ℤ) * (Ap : ℤ)) * j, 1]).det = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  set γ : SL(2, ℤ) := ⟨!![(1 : ℤ) + b * ((p : ℤ) * (Ap : ℤ)) * j, b;
    ((p : ℤ) * (Ap : ℤ)) * j, 1], hdetγ⟩ with hγ
  have h00 : γ 0 0 = 1 + b * ((p : ℤ) * (Ap : ℤ)) * j := by rw [hγ]; simp
  have h10 : γ 1 0 = ((p : ℤ) * (Ap : ℤ)) * j := by rw [hγ]; simp
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, h10]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨j, by push_cast; ring⟩
  · rw [SL2_mul_apply_one_zero, h00, h10]
    have hsplit : ρ 1 0 * (1 + b * ((p : ℤ) * (Ap : ℤ)) * j)
        + ρ 1 1 * (((p : ℤ) * (Ap : ℤ)) * j)
        = (Ap : ℤ) * (r + (p : ℤ) * j * X) := by
      rw [hX, hr]; ring
    rw [hsplit, hkey]
    exact ⟨r * (v + v' - v * v' * (L : ℤ) ^ 2), by push_cast; ring⟩

/-- `Γ₀` is antitone in the level: `N ∣ M` gives `Γ₀(M) ≤ Γ₀(N)`. -/
theorem Gamma0GL_le_of_dvd {N M : ℕ} (h : N ∣ M) : Gamma0GL M ≤ Gamma0GL N := by
  intro x hx
  obtain ⟨ρ, hρ, rfl⟩ := mem_Gamma0GL_iff.mp hx
  refine mem_Gamma0GL_iff.mpr ⟨ρ, ?_, rfl⟩
  rw [CongruenceSubgroup.Gamma0_mem] at hρ ⊢
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((Int.natCast_dvd_natCast.mpr h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρ))

/-- `mapGL` reflects `Γ₀`-membership, since it is injective (`mapGL_injective`). -/
theorem mem_Gamma0GL_mapGL_iff {N : ℕ} {ρ : SL(2, ℤ)} :
    (mapGL ℝ ρ : GL (Fin 2) ℝ) ∈ Gamma0GL N ↔ ρ ∈ CongruenceSubgroup.Gamma0 N := by
  refine ⟨fun h => ?_, fun h => mem_Gamma0GL_iff.mpr ⟨ρ, h, rfl⟩⟩
  obtain ⟨σ, hσ, hEq⟩ := mem_Gamma0GL_iff.mp h
  exact (mapGL_injective hEq) ▸ hσ

/-- **MIYAKE LEMMA 4.6.6(1) — THE TRACE COMMUTES WITH LEVEL-RAISING BY `L²` WHEN
`p ∤ L`** (PROVEN 2026-07-28; Miyake, *Modular Forms*, Lemma 4.6.6(1),
p. 158, and the step (4.6.13) that uses it):

    Tr^{A L²}_{Ap L²} ∘ V_1  =  V_1 ∘ Tr^A_{Ap}        (`A = p · Ap`,  `p ∤ L`).

This is the move that lets Miyake compute the trace at the RAISED level `A L²`
— where Theorem 4.6.4 is available — and read the answer off at level `A`, where
the peeling step's witness must live.

PROOF AS FORMALIZED, and NOTE IT NEEDS NO INDEX FORMULA FOR `Γ₀`.  `V_1` does not
change the underlying function at all (`coe_degeneracyOp_one`), so BOTH sides are
literally the same kind of sum of slashes `⇑F ∣[2] γ⁻¹` — the left one over
`Γ₀(Bp)/Γ₀(B)`, the right one over `Γ₀(Ap)/Γ₀(A)` — and the identity is exactly
the statement that the inclusion `Γ₀(Bp) ↪ Γ₀(Ap)` (`Gamma0GL_le_of_dvd`, from
`Ap ∣ Bp`) induces a BIJECTION between those two coset spaces.  Along that
bijection the summands are termwise equal, so the identity is exact and no index
constant appears.

* INJECTIVE: `γ ∈ Γ₀(Bp)` lying in `Γ₀(A)` has `Ap L² ∣ γ₁₀` and `p Ap ∣ γ₁₀`,
  and `p ∤ L` makes `lcm(Ap L², p Ap) = p Ap L² = B`
  (`dvd_mul_sq_of_dvd_mul_sq_of_dvd_mul`), so `γ ∈ Γ₀(B)`.
* SURJECTIVE: `exists_gamma0_mul_dvd_lowerLeft` — for `ρ ∈ Γ₀(Ap)`,
  right-multiplying by `[1 + bAj, b; Aj, 1] ∈ Γ₀(A)` turns `ρ₁₀ = Ap r` into
  `Ap(r + p j (ρ₁₁ + b ρ₁₀))`, and `(ρ₁₁, ρ₁₀) = 1` plus `p ∤ L` let `b` and `j`
  solve `r + p j X ≡ 0 (mod L²)` by two Bézout identities.

Miyake instead compares the index dichotomy `[Γ₀(N) : Γ₀(Np)] = p` at `p ∣ N`,
`p + 1` otherwise, which `p ∤ L` makes agree at the two levels
(`p ∣ Ap ↔ p ∣ Ap L²`).  That route needs an index formula for `Γ₀` that this
project does not have; the direct argument above avoids it, exactly as
`traceOp_degeneracyOp_comm` below does for `V_q`.

`p ∤ L` is consumed in the two places named above, and the statement is FALSE
without it: at `Ap = 1, p = 2, L = 2` the map `Γ₀(4)/Γ₀(8) → Γ₀(1)/Γ₀(2)` is not
injective (`lcm(2,4) = 4 ≠ 8`, so `[[1,0],[4,1]] ∈ Γ₀(4) ∖ Γ₀(8)` maps to the
identity coset; the map is also not surjective, the indices being 2 and 3).

The four levels are passed as VARIABLES with defining equations rather than as
`A / p`, `A * L ^ 2`, … so that instantiating this needs no rewriting inside
`CuspForm (Gamma0GL ·) 2`.

`0 < A` is carried for the consumer's convenience only; the proof uses the
strictly stronger `[NeZero A]` instance instead, hence the underscore. -/
theorem traceOp_degeneracyOp_one_comm {A Ap B Bp L p : ℕ}
    [NeZero A] [NeZero Ap] [NeZero B] [NeZero Bp]
    (_hA : 0 < A) (hp : p.Prime) (hpL : ¬ p ∣ L) (hL : 0 < L)
    (hAp : p * Ap = A) (hB : A * L ^ 2 = B) (hBp : Ap * L ^ 2 = Bp)
    (F : CuspForm (Gamma0GL A) 2) :
    traceOp B Bp (degeneracyOp A B 1 F) = degeneracyOp Ap Bp 1 (traceOp A Ap F) := by
  classical
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL B) (Gamma0GL Bp) :=
    isFiniteRelIndex_of_isArithmetic _ _
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL A) (Gamma0GL Ap) :=
    isFiniteRelIndex_of_isArithmetic _ _
  letI : Fintype (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)) := Fintype.ofFinite _
  letI : Fintype (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) := Fintype.ofFinite _
  have hAp0 : 0 < Ap := Nat.pos_of_ne_zero (NeZero.ne Ap)
  have hAB : A ∣ B := ⟨L ^ 2, hB.symm⟩
  have hApBp : Ap ∣ Bp := ⟨L ^ 2, hBp.symm⟩
  -- the inclusion `Γ₀(Bp) → Γ₀(Ap)`
  set φ : Gamma0GL Bp →* Gamma0GL Ap := Subgroup.inclusion (Gamma0GL_le_of_dvd hApBp) with hφ
  have hcoeφ : ∀ r : Gamma0GL Bp,
      ((φ r : Gamma0GL Ap) : GL (Fin 2) ℝ) = (r : GL (Fin 2) ℝ) := by
    intro r
    rw [hφ]
    exact Subgroup.coe_inclusion _ r
  have hφval : ∀ x y : Gamma0GL Bp,
      (((φ x)⁻¹ * φ y : Gamma0GL Ap) : GL (Fin 2) ℝ)
        = ((x⁻¹ * y : Gamma0GL Bp) : GL (Fin 2) ℝ) := by
    intro x y
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcoeφ]
  have hwd : ∀ x y : Gamma0GL Bp,
      ((x⁻¹ * y : Gamma0GL Bp) : GL (Fin 2) ℝ) ∈ Gamma0GL B →
      ((φ x : Gamma0GL Ap) : Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap))
        = (φ y : Gamma0GL Ap) := by
    intro x y hxy
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf, hφval x y]
    exact Gamma0GL_le_of_dvd hAB hxy
  set Φ : (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)) →
      (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) := fun x =>
    Quotient.liftOn x
      (fun r => ((φ r : Gamma0GL Ap) :
        Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)))
      (fun a b hab => hwd a b (by
        rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply,
          Subgroup.mem_subgroupOf] at hab
        exact hab)) with hΦ
  have hΦmk : ∀ r : Gamma0GL Bp,
      Φ ((r : Gamma0GL Bp) : Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp))
        = ((φ r : Gamma0GL Ap) :
            Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) := fun _ => rfl
  -- injectivity: `Ap L² ∣ c` and `p Ap ∣ c` give `p Ap L² ∣ c`
  have hback : ∀ z : GL (Fin 2) ℝ, z ∈ Gamma0GL Bp → z ∈ Gamma0GL A → z ∈ Gamma0GL B := by
    intro z hzBp hzA
    obtain ⟨ρ, hρ, rfl⟩ := mem_Gamma0GL_iff.mp hzBp
    have h1 : ((Ap * L ^ 2 : ℕ) : ℤ) ∣ ρ 1 0 := by
      rw [← hBp, CongruenceSubgroup.Gamma0_mem] at hρ
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρ
    have h2 : ((p * Ap : ℕ) : ℤ) ∣ ρ 1 0 := by
      have hρA := mem_Gamma0GL_mapGL_iff.mp hzA
      rw [← hAp, CongruenceSubgroup.Gamma0_mem] at hρA
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρA
    refine mem_Gamma0GL_mapGL_iff.mpr ?_
    rw [CongruenceSubgroup.Gamma0_mem]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    have h3 := dvd_mul_sq_of_dvd_mul_sq_of_dvd_mul hp hpL hAp0 h1 h2
    have hBeq : B = p * Ap * L ^ 2 := by rw [← hB, ← hAp]
    rw [hBeq]
    exact h3
  have hinj : ∀ a b, Φ a = Φ b → a = b := by
    refine QuotientGroup.forall_mk.mpr fun x =>
      QuotientGroup.forall_mk.mpr fun y hxy => ?_
    rw [hΦmk, hΦmk] at hxy
    have h1 := QuotientGroup.eq.mp hxy
    rw [Subgroup.mem_subgroupOf, hφval x y] at h1
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact hback _ (x⁻¹ * y).2 h1
  have hsurj : Function.Surjective Φ := by
    refine QuotientGroup.forall_mk.mpr fun s => ?_
    obtain ⟨ρ, hρ, hρeq⟩ := mem_Gamma0GL_iff.mp s.2
    obtain ⟨γ, hγ, hdvd10⟩ := exists_gamma0_mul_dvd_lowerLeft hp hpL hL hρ
    rw [hAp] at hγ
    have hσmem : (ρ * γ) ∈ CongruenceSubgroup.Gamma0 Bp := by
      rw [CongruenceSubgroup.Gamma0_mem]
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
      rw [← hBp]
      exact hdvd10
    have hσGL : (mapGL ℝ (ρ * γ) : GL (Fin 2) ℝ) ∈ Gamma0GL Bp :=
      mem_Gamma0GL_mapGL_iff.mpr hσmem
    refine ⟨((⟨mapGL ℝ (ρ * γ), hσGL⟩ : Gamma0GL Bp) :
      Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)), ?_⟩
    rw [hΦmk]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hval : (((φ ⟨mapGL ℝ (ρ * γ), hσGL⟩)⁻¹ * s : Gamma0GL Ap) : GL (Fin 2) ℝ)
        = (mapGL ℝ γ)⁻¹ := by
      simp only [hφ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        ← hρeq, map_mul]
      group
    rw [hval]
    exact inv_mem (mem_Gamma0GL_iff.mpr ⟨γ, hγ, rfl⟩)
  -- assembly
  refine DFunLike.coe_injective ?_
  have hLHS : ⇑(traceOp B Bp (degeneracyOp A B 1 F))
      = ∑ x : (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)),
          SlashInvariantForm.quotientFunc (degeneracyOp A B 1 F) x := by
    show ⇑(CuspForm.trace (Gamma0GL Bp) (degeneracyOp A B 1 F)) = _
    rw [CuspForm.coe_trace]
  have hTrA : ⇑(traceOp A Ap F)
      = ∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          SlashInvariantForm.quotientFunc F y := by
    show ⇑(CuspForm.trace (Gamma0GL Ap) F) = _
    rw [CuspForm.coe_trace]
  have hRHS : ⇑(degeneracyOp Ap Bp 1 (traceOp A Ap F)) = ⇑(traceOp A Ap F) :=
    coe_degeneracyOp_one hApBp _
  have hterm : ∀ x : (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)),
      SlashInvariantForm.quotientFunc (degeneracyOp A B 1 F) x
        = SlashInvariantForm.quotientFunc F (Φ x) := by
    refine QuotientGroup.forall_mk.mpr fun r => ?_
    rw [hΦmk]
    show ⇑(degeneracyOp A B 1 F) ∣[(2 : ℤ)] ((r : Gamma0GL Bp) : GL (Fin 2) ℝ)⁻¹
      = ⇑F ∣[(2 : ℤ)] ((φ r : Gamma0GL Ap) : GL (Fin 2) ℝ)⁻¹
    rw [coe_degeneracyOp_one hAB F, hcoeφ r]
  rw [hLHS, hRHS, hTrA]
  calc ∑ x : (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)),
        SlashInvariantForm.quotientFunc (degeneracyOp A B 1 F) x
      = ∑ x : (Gamma0GL Bp ⧸ (Gamma0GL B).subgroupOf (Gamma0GL Bp)),
          SlashInvariantForm.quotientFunc F (Φ x) :=
        Finset.sum_congr rfl fun x _ => hterm x
    _ = ∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          SlashInvariantForm.quotientFunc F y :=
        Fintype.sum_equiv (Equiv.ofBijective Φ ⟨fun a b h => hinj a b h, hsurj⟩) _ _
          fun _ => rfl

/-- **`U_p` COMMUTES WITH `V_d` AT A BAD PRIME** (PROVEN 2026-07-27): for
`d·N ∣ M`, a prime `p ∣ N` and `p ∤ d`,

    U_p^{(M)} ∘ V_d  =  V_d ∘ U_p^{(N)}.

This is the BAD-prime companion of `heckeOp_degeneracyOp` above, which is stated
at `q ∤ M` and therefore carries the extra `q·a_{m/q}` correction term on both
sides.  Here `p` divides BOTH levels (`p ∣ N ∣ M`), so `qCoeff_heckeOp` reads
`a_m(U_p f) = a_{pm}(f)` with no correction at either level, and the identity
collapses to the two index computations `d ∣ p·m ↔ d ∣ m` and
`p·m/d = p·(m/d)` — both valid exactly because `p ∤ d` makes `d` and `p`
coprime.

This is what lets Miyake's move 4 push `U_p` past a `V_q` (`q ∣ L`, `p ∤ L`, so
`q ≠ p`) and past the level-raising inclusion `V_1`; it is consumed twice in
`qCoeff_traceOp_heckeOp_eq_zero_aux` below. -/
theorem heckeOp_degeneracyOp_of_dvd {N M d p : ℕ} (hN : 0 < N) (hM : 0 < M) (hd : 0 < d)
    (hdvd : d * N ∣ M) (hp : p.Prime) (hpN : p ∣ N) (hpd : ¬ p ∣ d)
    (u : CuspForm (Gamma0GL N) 2) :
    heckeOp M p (degeneracyOp N M d u) = degeneracyOp N M d (heckeOp N p u) := by
  have hNM : N ∣ M := (Dvd.intro_left d rfl).trans hdvd
  have hpM : p ∣ M := hpN.trans hNM
  have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm
  refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
  rw [qCoeff_heckeOp hM hp (degeneracyOp N M d u) m, if_pos hpM, add_zero,
    qCoeff_degeneracyOp hd hdvd u (p * m),
    qCoeff_degeneracyOp hd hdvd (heckeOp N p u) m]
  by_cases hdm : d ∣ m
  · obtain ⟨t, rfl⟩ := hdm
    have h1 : d ∣ p * (d * t) := (dvd_mul_right d t).mul_left p
    have h2 : p * (d * t) / d = p * t := by
      rw [show p * (d * t) = d * (p * t) by ring, Nat.mul_div_cancel_left _ hd]
    rw [if_pos h1, if_pos (dvd_mul_right d t), h2, Nat.mul_div_cancel_left t hd,
      qCoeff_heckeOp hN hp u t, if_pos hpN, add_zero]
  · have h1 : ¬ d ∣ p * m := fun hh => hdm (hcop.dvd_of_dvd_mul_left hh)
    rw [if_neg h1, if_neg hdm]

/-- **THE CONVERSE OF `Gamma0GL_le_conj_heckeRepInf`, ON THE LOWER-LEFT ENTRY**
(PROVEN 2026-07-27): if `δ_q γ δ_q⁻¹ ∈ Γ₀(N)` for `δ_q = [q, 0; 0, 1]` and
`γ = mapGL ρ`, then `N q ∣ ρ₁₀`.

Conjugation by `δ_q` multiplies the upper-right entry by `q` and DIVIDES the
lower-left entry by `q`, so writing the conjugate as `mapGL ε` and comparing the
`(1, 0)` entries of `ε δ_q = δ_q ρ` gives `ρ₁₀ = q ε₁₀`; `N ∣ ε₁₀` then yields
`N q ∣ ρ₁₀`.

This is the injectivity half of Miyake's coset bijection in
`traceOp_degeneracyOp_comm` below: it is exactly the step "`δ_q γ δ_q⁻¹ ∈ Γ₀(A)`
says `A ∣ c/q`, i.e. `Aq ∣ c`". -/
theorem dvd_of_conj_heckeRepInf_mem_Gamma0GL {N q : ℕ} (hq : 0 < q) {ρ : SL(2, ℤ)}
    (h : heckeRepInf q * mapGL ℝ ρ * (heckeRepInf q)⁻¹ ∈ Gamma0GL N) :
    ((N * q : ℕ) : ℤ) ∣ ρ 1 0 := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  obtain ⟨ε, hε, hεeq⟩ := mem_Gamma0GL_iff.mp h
  have heq : mapGL ℝ ε * heckeRepInf q = heckeRepInf q * mapGL ℝ ρ := by
    rw [hεeq]; group
  have h10 := congr_arg
    (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) heq
  simp [heckeRepInf_coe hq0, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two] at h10
  have hcast : ((ρ 1 0 : ℤ) : ℝ) = (((q : ℤ) * ε 1 0 : ℤ) : ℝ) := by
    push_cast
    linear_combination -h10
  have hz : ρ 1 0 = (q : ℤ) * ε 1 0 := by exact_mod_cast hcast
  have hNε : (N : ℤ) ∣ ε 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hε
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hε
  obtain ⟨t, ht⟩ := hNε
  exact ⟨t, by rw [hz, ht]; push_cast; ring⟩

/-- **THE SURJECTIVITY INPUT FOR MIYAKE 4.6.6(2)** (PROVEN 2026-07-27): for
`ρ ∈ Γ₀(Ap)` and DISTINCT primes `p ≠ q`, the coset `ρ Γ₀(p·Ap)` contains a
matrix whose upper-right entry is divisible by `q`.

This is what makes the conjugation map on cosets SURJECTIVE without any index
computation: the image of `Γ₀(Ap q)` under `γ ↦ δ_q γ δ_q⁻¹` is exactly
`{γ ∈ Γ₀(Ap) : q ∣ γ₀₁}`, so surjectivity onto `Γ₀(Ap)/Γ₀(p Ap)` is precisely the
statement below.

PROOF.  Right multiplication by `[1, 0; A, 1]^j · [1, l; 0, 1] = [1, l; Aj, Ajl+1]`
(with `A = p·Ap`, so this lies in `Γ₀(A)`) sends the upper-right entry to
`(ρ₀₀ + ρ₀₁ A j)·l + ρ₀₁`, and some `j ∈ {0, 1}` makes the coefficient a unit
mod `q`: if `q ∤ ρ₀₀` take `j = 0`; otherwise `det ρ = 1` gives `q ∤ ρ₀₁`, and
`q ∤ A` because `q ∣ A = p Ap` would force `q ∣ Ap ∣ ρ₁₀` (as `q ≠ p`) and hence
`q ∣ ρ₀₀ρ₁₁ − ρ₀₁ρ₁₀ = 1`.  Then `l` solves the linear congruence in the field
`ZMod q`.

`p ≠ q` is consumed EXACTLY here, and nowhere else in Lemma 4.6.6(2). -/
theorem exists_gamma0_mul_dvd_upperRight {Ap p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ρ : SL(2, ℤ)} (hρ : ρ ∈ CongruenceSubgroup.Gamma0 Ap) :
    ∃ γ ∈ CongruenceSubgroup.Gamma0 (p * Ap), (q : ℤ) ∣ (ρ * γ) 0 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqz : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have h2 := ρ.2
    rwa [Matrix.det_fin_two] at h2
  have hc : (Ap : ℤ) ∣ ρ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hρ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hρ
  have hqone : ¬ ((q : ℕ) : ℤ) ∣ 1 := fun hcon => by
    have h1 : ((q : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hcon
    exact hq.one_lt.ne' (by exact_mod_cast h1)
  obtain ⟨j, hj⟩ : ∃ j : ℤ,
      ¬ (q : ℤ) ∣ (ρ 0 0 + ρ 0 1 * ((p : ℤ) * (Ap : ℤ)) * j) := by
    by_cases h00 : (q : ℤ) ∣ ρ 0 0
    · have h01 : ¬ (q : ℤ) ∣ ρ 0 1 := by
        intro h01
        exact hqone (by rw [← hdet]; exact dvd_sub (h00.mul_right _) (h01.mul_right _))
      have hqA : ¬ (q : ℤ) ∣ ((p : ℤ) * (Ap : ℤ)) := by
        intro hA
        rcases hqz.2.2 _ _ hA with h | h
        · have hnat : q ∣ p := by exact_mod_cast h
          exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hnat).symm
        · have hq10 : (q : ℤ) ∣ ρ 1 0 := h.trans hc
          exact hqone (by
            rw [← hdet]; exact dvd_sub (h00.mul_right _) (hq10.mul_left _))
      refine ⟨1, ?_⟩
      rw [mul_one]
      intro hcon
      rcases hqz.2.2 _ _ ((dvd_add_right h00).mp hcon) with h | h
      · exact h01 h
      · exact hqA h
    · exact ⟨0, by simpa using h00⟩
  set a' : ℤ := ρ 0 0 + ρ 0 1 * ((p : ℤ) * (Ap : ℤ)) * j with ha'
  obtain ⟨l, hl⟩ : ∃ l : ℤ, (q : ℤ) ∣ a' * l + ρ 0 1 := by
    have ha'ne : ((a' : ℤ) : ZMod q) ≠ 0 := fun h =>
      hj ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    obtain ⟨l, hlz⟩ := ZMod.intCast_surjective (n := q)
      (-((ρ 0 1 : ℤ) : ZMod q) * ((a' : ℤ) : ZMod q)⁻¹)
    refine ⟨l, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hlz]
    field_simp
    ring
  have hdetγ : (!![(1 : ℤ), l; (p : ℤ) * (Ap : ℤ) * j,
      (p : ℤ) * (Ap : ℤ) * j * l + 1]).det = 1 := by
    rw [Matrix.det_fin_two_of]; ring
  set G : SL(2, ℤ) := ⟨!![(1 : ℤ), l; (p : ℤ) * (Ap : ℤ) * j,
    (p : ℤ) * (Ap : ℤ) * j * l + 1], hdetγ⟩ with hG
  refine ⟨G, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    have hentry : G 1 0 = (p : ℤ) * (Ap : ℤ) * j := by rw [hG]; simp
    rw [hentry]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨j, by push_cast; ring⟩
  · rw [SL2_mul_apply_zero_one]
    have h01 : G 0 1 = l := by rw [hG]; simp
    have h11 : G 1 1 = (p : ℤ) * (Ap : ℤ) * j * l + 1 := by rw [hG]; simp
    rw [h01, h11]
    have hrw : ρ 0 0 * l + ρ 0 1 * ((p : ℤ) * (Ap : ℤ) * j * l + 1)
        = a' * l + ρ 0 1 := by rw [ha']; ring
    rw [hrw]
    exact hl

/-- **MIYAKE LEMMA 4.6.6(2) — THE TRACE COMMUTES WITH `V_q` AT A PRIME `q ≠ p`**
(PROVEN 2026-07-27; Miyake, *Modular Forms*, Lemma 4.6.6(2), p. 158):
for `A = p·Ap`, `C = A·q`, `Cp = Ap·q` with `p ≠ q` both prime,

    Tr^{Aq}_{Ap q} ∘ V_q  =  V_q ∘ Tr^A_{Ap}.

This is the `V_q`-analogue of `traceOp_degeneracyOp_one_comm` above (which is
Lemma 4.6.6(1), the `V_1`-and-`L²` version), and the two together are what let
Miyake compute a trace at a level where the descent theorem is available and
read the answer off at the level where the witness must live.

PROOF (the coset bijection, which is exact — there is NO constant).  Write
`δ_q = [q, 0; 0, 1]`, so that `V_q f = q⁻¹ (f ∣₂ δ_q)` in weight `2`.  Then

* `δ_q Γ₀(Nq) δ_q⁻¹ ⊆ Γ₀(N)` for every `N`, since conjugation sends
  `[a, b; c, d]` to `[a, qb; c/q, d]`;
* the induced map on cosets `Γ₀(Ap q)/Γ₀(A q) → Γ₀(Ap)/Γ₀(A)` is INJECTIVE,
  because `δ_q γ δ_q⁻¹ ∈ Γ₀(A)` says `A ∣ c/q`, i.e. `Aq ∣ c`;
* it is SURJECTIVE as well, and — this is the one place the formalization
  departs from the textbook — that is proven DIRECTLY rather than by matching
  the two indices.  The image of `Γ₀(Ap q)` in `Γ₀(Ap)` is
  `{γ ∈ Γ₀(Ap) : q ∣ γ₀₁}`, so surjectivity onto `Γ₀(Ap)/Γ₀(A)` is exactly
  `exists_gamma0_mul_dvd_upperRight` above: right-multiply by
  `[1, l; Aj, Ajl+1] ∈ Γ₀(A)`.  The index dichotomy
  `[Γ₀(N) : Γ₀(Np)] = p` at `p ∣ N`, `p + 1` otherwise — which is what Miyake
  compares, and which `q ≠ p` makes agree through `p ∣ Ap ↔ p ∣ Ap q` — is
  therefore NOT needed anywhere, and no index formula for `Γ₀` had to be built.

Summing `F ∣ δ_q γ = F ∣ (δ_q γ δ_q⁻¹) δ_q` over that bijection is the claim; on
the nose, `δ_q γ⁻¹ = (δ_q γ δ_q⁻¹)⁻¹ δ_q`, so the two sums are TERMWISE equal
along the bijection and the identity is exact — there is no index constant.

`p ≠ q` is consumed in exactly ONE place, `exists_gamma0_mul_dvd_upperRight`:
at `q ∣ A` the coefficient `ρ₀₀ + ρ₀₁ A j` is `≡ ρ₀₀` for every `j`, and a
`ρ ∈ Γ₀(Ap)` with `q ∣ ρ₀₀` then has `q ∣ γ₀₁` for NO `γ ∈ ρ Γ₀(A)` — so
surjectivity genuinely fails without it.

The four levels are passed as VARIABLES with defining equations rather than as
`A * q`, `A / p`, … so that instantiating this needs no dependent-type rewriting
inside `CuspForm (Gamma0GL ·) 2` — the same convention as
`traceOp_degeneracyOp_one_comm` above, and the reason its consumer below can
instantiate `A := C / q` without ever rewriting a level.

`0 < A` is carried for the consumer's convenience only; the proof uses the
strictly stronger `[NeZero A]` instance instead, hence the underscore. -/
theorem traceOp_degeneracyOp_comm {A Ap C Cp p q : ℕ}
    [NeZero A] [NeZero Ap] [NeZero C] [NeZero Cp]
    (_hA : 0 < A) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hAp : p * Ap = A) (hC : A * q = C) (hCp : Ap * q = Cp)
    (F : CuspForm (Gamma0GL A) 2) :
    traceOp C Cp (degeneracyOp A C q F) = degeneracyOp Ap Cp q (traceOp A Ap F) := by
  classical
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL C) (Gamma0GL Cp) :=
    isFiniteRelIndex_of_isArithmetic _ _
  haveI : Subgroup.IsFiniteRelIndex (Gamma0GL A) (Gamma0GL Ap) :=
    isFiniteRelIndex_of_isArithmetic _ _
  letI : Fintype (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)) :=
    Fintype.ofFinite _
  letI : Fintype (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) :=
    Fintype.ofFinite _
  have hqAC : q * A ∣ C := ⟨1, by rw [← hC]; ring⟩
  have hqApCp : q * Ap ∣ Cp := ⟨1, by rw [← hCp]; ring⟩
  -- `δ_q Γ₀(Nq) δ_q⁻¹ ⊆ Γ₀(N)`, at the two levels the diagram needs
  have hconjAp : ∀ x : GL (Fin 2) ℝ, x ∈ Gamma0GL Cp →
      heckeRepInf q * x * (heckeRepInf q)⁻¹ ∈ Gamma0GL Ap := fun x hx =>
    mem_conjAct_inv_smul_iff.mp (Gamma0GL_le_conj_heckeRepInf hq.pos hqApCp hx)
  have hconjA : ∀ x : GL (Fin 2) ℝ, x ∈ Gamma0GL C →
      heckeRepInf q * x * (heckeRepInf q)⁻¹ ∈ Gamma0GL A := fun x hx =>
    mem_conjAct_inv_smul_iff.mp (Gamma0GL_le_conj_heckeRepInf hq.pos hqAC hx)
  -- and its converse, which is the injectivity of the coset map
  have hconjBack : ∀ x : GL (Fin 2) ℝ, x ∈ Gamma0GL Cp →
      heckeRepInf q * x * (heckeRepInf q)⁻¹ ∈ Gamma0GL A → x ∈ Gamma0GL C := by
    intro x hx hxa
    obtain ⟨ρ, hρ, rfl⟩ := mem_Gamma0GL_iff.mp hx
    have hdv := dvd_of_conj_heckeRepInf_mem_Gamma0GL (N := A) hq.pos hxa
    refine mem_Gamma0GL_iff.mpr ⟨ρ, ?_, rfl⟩
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by rw [← hC]; exact hdv)
  -- conjugation as a map `Γ₀(Ap q) → Γ₀(Ap)`, and its descent to cosets
  set φ : Gamma0GL Cp → Gamma0GL Ap := fun x =>
    ⟨heckeRepInf q * (x : GL (Fin 2) ℝ) * (heckeRepInf q)⁻¹, hconjAp x x.2⟩ with hφ
  have hφval : ∀ x y : Gamma0GL Cp,
      (((φ x)⁻¹ * φ y : Gamma0GL Ap) : GL (Fin 2) ℝ)
        = heckeRepInf q * ((x⁻¹ * y : Gamma0GL Cp) : GL (Fin 2) ℝ)
            * (heckeRepInf q)⁻¹ := by
    intro x y
    simp only [hφ, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hwd : ∀ x y : Gamma0GL Cp,
      ((x⁻¹ * y : Gamma0GL Cp) : GL (Fin 2) ℝ) ∈ Gamma0GL C →
      ((φ x : Gamma0GL Ap) : Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap))
        = (φ y : Gamma0GL Ap) := by
    intro x y hxy
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf, hφval x y]
    exact hconjA _ hxy
  set Φ : (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)) →
      (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) := fun x =>
    Quotient.liftOn x
      (fun r => ((φ r : Gamma0GL Ap) :
        Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)))
      (fun a b hab => hwd a b (by
        rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply,
          Subgroup.mem_subgroupOf] at hab
        exact hab)) with hΦ
  have hΦmk : ∀ r : Gamma0GL Cp,
      Φ ((r : Gamma0GL Cp) : Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp))
        = ((φ r : Gamma0GL Ap) :
            Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)) := fun _ => rfl
  have hinj : ∀ a b, Φ a = Φ b → a = b := by
    refine QuotientGroup.forall_mk.mpr fun x =>
      QuotientGroup.forall_mk.mpr fun y hxy => ?_
    rw [hΦmk, hΦmk] at hxy
    have h1 := QuotientGroup.eq.mp hxy
    rw [Subgroup.mem_subgroupOf, hφval x y] at h1
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact hconjBack _ (x⁻¹ * y).2 h1
  have hsurj : Function.Surjective Φ := by
    refine QuotientGroup.forall_mk.mpr fun s => ?_
    obtain ⟨ρ, hρ, hρeq⟩ := mem_Gamma0GL_iff.mp s.2
    obtain ⟨γ, hγ, hdvd01⟩ := exists_gamma0_mul_dvd_upperRight hp hq hpq hρ
    rw [hAp] at hγ
    obtain ⟨σ, hσdef⟩ : ∃ σ : SL(2, ℤ), σ = ρ * γ := ⟨ρ * γ, rfl⟩
    rw [← hσdef] at hdvd01
    have hApA : (Ap : ℤ) ∣ (A : ℤ) := ⟨(p : ℤ), by rw [← hAp]; push_cast; ring⟩
    have hγAp : γ ∈ CongruenceSubgroup.Gamma0 Ap := by
      rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (hApA.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ))
    have hσAp : σ ∈ CongruenceSubgroup.Gamma0 Ap := by
      rw [hσdef]; exact mul_mem hρ hγAp
    have hσ10 : (Ap : ℤ) ∣ σ 1 0 := by
      rw [CongruenceSubgroup.Gamma0_mem] at hσAp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσAp
    obtain ⟨t, ht⟩ := hdvd01
    have hdetσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
      have h2 := σ.2
      rwa [Matrix.det_fin_two] at h2
    rw [ht] at hdetσ
    have hdetτ : (!![σ 0 0, t; (q : ℤ) * σ 1 0, σ 1 1]).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hdetσ
    set τ : SL(2, ℤ) := ⟨_, hdetτ⟩ with hτ
    have hτmem : τ ∈ CongruenceSubgroup.Gamma0 Cp := by
      rw [CongruenceSubgroup.Gamma0_mem]
      have hentry : τ 1 0 = (q : ℤ) * σ 1 0 := by rw [hτ]; simp
      rw [hentry]
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
      obtain ⟨u, hu⟩ := hσ10
      exact ⟨u, by rw [hu, ← hCp]; push_cast; ring⟩
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    have hconjτ : heckeRepInf q * mapGL ℝ τ * (heckeRepInf q)⁻¹ = mapGL ℝ σ := by
      rw [mul_inv_eq_iff_eq_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        · simp [hτ, heckeRepInf_coe hq0, mapGL_coe_matrix,
            Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
            Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply,
            Fin.sum_univ_two, ht]
          try push_cast
          try ring
    have hτGL : (mapGL ℝ τ : GL (Fin 2) ℝ) ∈ Gamma0GL Cp :=
      mem_Gamma0GL_iff.mpr ⟨τ, hτmem, rfl⟩
    refine ⟨((⟨mapGL ℝ τ, hτGL⟩ : Gamma0GL Cp) :
      Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)), ?_⟩
    rw [hΦmk]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hval : (((φ ⟨mapGL ℝ τ, hτGL⟩)⁻¹ * s : Gamma0GL Ap) : GL (Fin 2) ℝ)
        = (mapGL ℝ γ)⁻¹ := by
      simp only [hφ, Subgroup.coe_mul, Subgroup.coe_inv, hconjτ,
        ← hρeq, hσdef, map_mul]
      group
    rw [hval]
    exact inv_mem (mem_Gamma0GL_iff.mpr ⟨γ, hγ, rfl⟩)
  -- the termwise identity `δ_q γ⁻¹ = (δ_q γ δ_q⁻¹)⁻¹ δ_q`
  have hmat : ∀ r : Gamma0GL Cp,
      heckeRepInf q * ((r : Gamma0GL Cp) : GL (Fin 2) ℝ)⁻¹
        = ((φ r : Gamma0GL Ap) : GL (Fin 2) ℝ)⁻¹ * heckeRepInf q := by
    intro r
    show heckeRepInf q * ((r : Gamma0GL Cp) : GL (Fin 2) ℝ)⁻¹
      = (heckeRepInf q * ((r : Gamma0GL Cp) : GL (Fin 2) ℝ) * (heckeRepInf q)⁻¹)⁻¹
          * heckeRepInf q
    group
  refine DFunLike.coe_injective ?_
  have hLHS : ⇑(traceOp C Cp (degeneracyOp A C q F))
      = ∑ x : (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)),
          SlashInvariantForm.quotientFunc (degeneracyOp A C q F) x := by
    show ⇑(CuspForm.trace (Gamma0GL Cp) (degeneracyOp A C q F)) = _
    rw [CuspForm.coe_trace]
  have hTrA : ⇑(traceOp A Ap F)
      = ∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          SlashInvariantForm.quotientFunc F y := by
    show ⇑(CuspForm.trace (Gamma0GL Ap) F) = _
    rw [CuspForm.coe_trace]
  have hRHS : ⇑(degeneracyOp Ap Cp q (traceOp A Ap F))
      = (q : ℂ)⁻¹ • ((∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          SlashInvariantForm.quotientFunc F y) ∣[(2 : ℤ)] heckeRepInf q) := by
    rw [degeneracyOp_coe hq.pos hqApCp, hTrA]
    rfl
  have hterm : ∀ x : (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)),
      SlashInvariantForm.quotientFunc (degeneracyOp A C q F) x
        = (q : ℂ)⁻¹ • (SlashInvariantForm.quotientFunc F (Φ x)
            ∣[(2 : ℤ)] heckeRepInf q) := by
    refine QuotientGroup.forall_mk.mpr fun r => ?_
    rw [hΦmk]
    show ⇑(degeneracyOp A C q F) ∣[(2 : ℤ)] ((r : Gamma0GL Cp) : GL (Fin 2) ℝ)⁻¹
      = (q : ℂ)⁻¹ • ((⇑F ∣[(2 : ℤ)] ((φ r : Gamma0GL Ap) : GL (Fin 2) ℝ)⁻¹)
          ∣[(2 : ℤ)] heckeRepInf q)
    rw [degeneracyOp_coe hq.pos hqAC F]
    show ((q : ℂ)⁻¹ • (⇑F ∣[(2 : ℤ)] heckeRepInf q)) ∣[(2 : ℤ)]
        ((r : Gamma0GL Cp) : GL (Fin 2) ℝ)⁻¹ = _
    rw [ModularForm.smul_slash, σ_Gamma0GL (inv_mem r.2), ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, hmat r]
  rw [hLHS, hRHS]
  calc ∑ x : (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)),
        SlashInvariantForm.quotientFunc (degeneracyOp A C q F) x
      = ∑ x : (Gamma0GL Cp ⧸ (Gamma0GL C).subgroupOf (Gamma0GL Cp)),
          (q : ℂ)⁻¹ • (SlashInvariantForm.quotientFunc F (Φ x)
            ∣[(2 : ℤ)] heckeRepInf q) :=
        Finset.sum_congr rfl fun x _ => hterm x
    _ = ∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          (q : ℂ)⁻¹ • (SlashInvariantForm.quotientFunc F y
            ∣[(2 : ℤ)] heckeRepInf q) :=
        Fintype.sum_equiv (Equiv.ofBijective Φ ⟨fun a b h => hinj a b h, hsurj⟩) _ _
          fun _ => rfl
    _ = (q : ℂ)⁻¹ • ∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          (SlashInvariantForm.quotientFunc F y ∣[(2 : ℤ)] heckeRepInf q) :=
        (Finset.smul_sum).symm
    _ = (q : ℂ)⁻¹ • ((∑ y : (Gamma0GL Ap ⧸ (Gamma0GL A).subgroupOf (Gamma0GL Ap)),
          SlashInvariantForm.quotientFunc F y) ∣[(2 : ℤ)] heckeRepInf q) := by
        rw [SlashAction.sum_slash]

/-- **MIYAKE MOVE 4, AS A SIEVE INDUCTION ON `L`** (PROVEN 2026-07-27 over
`exists_cuspForm_qCoeff_sieve`, `traceOp_degeneracyOp_one_comm` and
`traceOp_degeneracyOp_comm`): this is `qCoeff_traceOp_heckeOp_eq_zero` below with
`1 < L` DROPPED and `B`, `Bp`, `h` universally quantified, which is what makes
the induction go through.

**HOW THIS REPLACES MIYAKE'S LEMMA 4.6.7.**  Miyake proves move 4 by first
decomposing `h = Σ_{q ∣ L prime} h_q(qz)` (Lemma 4.6.7 — a form supported off
the prime-to-`L` indices is a sum of `V_q`-images) and then commuting the trace
past each `V_q`.  Formalizing that decomposition means carrying a FAMILY of
forms at a family of DIFFERENT levels, i.e. a dependent-type family indexed by
`L.primeFactors`.  The induction below removes the family entirely: peel ONE
prime `q = L.minFac` at a time, and let the induction hypothesis at `L / q`
handle everything else.  Concretely, at level `C = B q²`:

1. `g` := the `q`-sieve of `h` (`exists_cuspForm_qCoeff_sieve`, PROVEN), so
   `a_n(g) = 1_{(n,q)=1}·a_n(h)`.  It satisfies the hypothesis at `L / q`,
   because `(n, q) = 1` and `(n, L/q) = 1` together give `(n, L) = 1`
   (`L = q·(L/q)`).  So the INDUCTION HYPOTHESIS applies to it — and `L/q < L`.
2. `w := V_1 h − g` is supported on the multiples of `q`, hence `w = V_q k` by
   Theorem 4.6.4 (`mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd`,
   PROVEN).  Then `U_p w = V_q (U_p k)` (`heckeOp_degeneracyOp_of_dvd`, since
   `p ≠ q`) and `Tr(V_q (U_p k)) = V_q (Tr (U_p k))` (Lemma 4.6.6(2),
   `traceOp_degeneracyOp_comm`), whose `m`-th coefficient vanishes because
   `q ∣ L` and `(m, L) = 1` force `q ∤ m`.
3. Lemma 4.6.6(1) (`traceOp_degeneracyOp_one_comm`, PROVEN) at `L := q` identifies
   the trace computed at level `C` with the one at level `B`, and
   `heckeOp_degeneracyOp_of_dvd` at `d = 1` moves `U_p` past `V_1`.

BASE CASE `L = 1`: the hypothesis then says `a_n(h) = 0` for EVERY `n`, so
`h = 0` by the `q`-expansion principle and both sides vanish.  `L = 0` cannot
occur, since `p ∣ 0` contradicts `¬ p ∣ L`.  Note this is why `1 < L` is not
needed: the statement is TRUE at `L = 1`, just vacuously about a zero form.

FAITHFULNESS.  `¬ p ∣ L` is load-bearing twice: it excludes `L = 0` (where
`(n, 0) = 1` means `n = 1` and the statement would be false), and it gives
`p ≠ L.minFac`, which every one of the three commutation steps consumes. -/
theorem qCoeff_traceOp_heckeOp_eq_zero_aux {p : ℕ} (hp : p.Prime) :
    ∀ L : ℕ, ¬ p ∣ L → ∀ B Bp : ℕ, ∀ [NeZero B] [NeZero Bp], 0 < B → p * Bp = B →
      ∀ h : CuspForm (Gamma0GL B) 2,
        (∀ n : ℕ, Nat.Coprime n L → qCoeff B h n = 0) →
        ∀ m : ℕ, Nat.Coprime m L →
          qCoeff Bp (traceOp B Bp (heckeOp B p h)) m = 0 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro hpL B Bp instB instBp hB hBp h hh m hm
    haveI : NeZero B := instB
    haveI : NeZero Bp := instBp
    have hL0 : L ≠ 0 := by rintro rfl; exact hpL (dvd_zero p)
    rcases eq_or_ne L 1 with rfl | hL1
    · -- BASE CASE: the hypothesis kills every coefficient, so `h = 0`.
      have hzero : h = 0 := cuspForm_eq_of_forall_qCoeff_eq fun n => by
        rw [hh n (Nat.coprime_one_right n), qCoeff_zero_cuspForm]
      rw [hzero, map_zero, map_zero, qCoeff_zero_cuspForm]
    · have hpB : p ∣ B := ⟨Bp, hBp.symm⟩
      have hBp0 : 0 < Bp := by
        rcases Nat.eq_zero_or_pos Bp with h0 | h0
        · rw [h0, mul_zero] at hBp; omega
        · exact h0
      have hq : (L.minFac).Prime := Nat.minFac_prime hL1
      have hqL : L.minFac ∣ L := Nat.minFac_dvd L
      set q := L.minFac
      have hpqne : p ≠ q := by rintro rfl; exact hpL hqL
      have hpq : ¬ p ∣ q := fun hd => hpqne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
      have hq0 : 0 < q := hq.pos
      have hp1 : ¬ p ∣ 1 := fun hd =>
        absurd (Nat.le_of_dvd one_pos hd) (by have := hp.two_le; omega)
      -- The raised levels, as VARIABLES with defining equations.
      obtain ⟨C, hCdef⟩ : ∃ C : ℕ, B * q ^ 2 = C := ⟨_, rfl⟩
      obtain ⟨Cp, hCpdef⟩ : ∃ Cp : ℕ, Bp * q ^ 2 = Cp := ⟨_, rfl⟩
      have hC0 : 0 < C := by rw [← hCdef]; exact Nat.mul_pos hB (pow_pos hq0 2)
      have hCp0 : 0 < Cp := by rw [← hCpdef]; exact Nat.mul_pos hBp0 (pow_pos hq0 2)
      haveI : NeZero C := ⟨hC0.ne'⟩
      haveI : NeZero Cp := ⟨hCp0.ne'⟩
      have hpCp : p * Cp = C := by rw [← hCdef, ← hCpdef, ← hBp]; ring
      have hBC : B ∣ C := ⟨q ^ 2, hCdef.symm⟩
      have hBpCp : Bp ∣ Cp := ⟨q ^ 2, hCpdef.symm⟩
      have hqC : q ∣ C := ⟨B * q, by rw [← hCdef]; ring⟩
      have hqCp : q ∣ Cp := ⟨Bp * q, by rw [← hCpdef]; ring⟩
      have hqm : ¬ q ∣ m :=
        (Nat.Prime.coprime_iff_not_dvd hq).mp (Nat.Coprime.coprime_dvd_right hqL hm).symm
      -- STEP 1: the `q`-sieve of `h`, at level `C = B q²`, and its complement.
      obtain ⟨g, hg⟩ := exists_cuspForm_qCoeff_sieve hB hq0 hCdef h
      obtain ⟨w, hw, hwz⟩ : ∃ w : CuspForm (Gamma0GL C) 2,
          degeneracyOp B C 1 h = g + w ∧ ∀ n : ℕ, ¬ q ∣ n → qCoeff C w n = 0 := by
        refine ⟨degeneracyOp B C 1 h - g, by abel, fun n hn => ?_⟩
        have hcq : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hn).symm
        rw [qCoeff_sub, qCoeff_degeneracyOp_one hBC h n, hg n, if_pos hcq, sub_self]
      -- STEP 2: the complement is supported on multiples of `q`, so it is `V_q k`.
      obtain ⟨k, hk⟩ := mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd hC0 hq hqC hwz
      have e1 : C / q = B * q := by
        rw [← hCdef, pow_two, show B * (q * q) = q * (B * q) from by ring,
          Nat.mul_div_cancel_left _ hq0]
      have e2 : Cp / q = Bp * q := by
        rw [← hCpdef, pow_two, show Bp * (q * q) = q * (Bp * q) from by ring,
          Nat.mul_div_cancel_left _ hq0]
      have hCq : C / q * q = C := Nat.div_mul_cancel hqC
      have hCpq : Cp / q * q = Cp := Nat.div_mul_cancel hqCp
      have hCq0 : 0 < C / q := Nat.div_pos (Nat.le_of_dvd hC0 hqC) hq0
      have hCpq0 : 0 < Cp / q := Nat.div_pos (Nat.le_of_dvd hCp0 hqCp) hq0
      haveI : NeZero (C / q) := ⟨hCq0.ne'⟩
      haveI : NeZero (Cp / q) := ⟨hCpq0.ne'⟩
      have hpCpq : p * (Cp / q) = C / q := by rw [e1, e2, ← mul_assoc, hBp]
      have hqCCq : q * (C / q) ∣ C := ⟨1, by rw [mul_one, mul_comm q (C / q), hCq]⟩
      have hqCpCp : q * (Cp / q) ∣ Cp := ⟨1, by rw [mul_one, mul_comm q (Cp / q), hCpq]⟩
      have hpCq : p ∣ C / q := ⟨Cp / q, hpCpq.symm⟩
      -- STEP 3: `U_p` and the trace both pass through `V_q`, so the complement
      -- contributes only at multiples of `q`.
      have hUw : heckeOp C p w = degeneracyOp (C / q) C q (heckeOp (C / q) p k) := by
        rw [← hk]
        exact heckeOp_degeneracyOp_of_dvd hCq0 hC0 hq0 hqCCq hp hpCq hpq k
      have hTrw : traceOp C Cp (heckeOp C p w)
          = degeneracyOp (Cp / q) Cp q (traceOp (C / q) (Cp / q) (heckeOp (C / q) p k)) := by
        rw [hUw]
        exact traceOp_degeneracyOp_comm (A := C / q) (Ap := Cp / q) (C := C) (Cp := Cp)
          hCq0 hp hq hpqne hpCpq hCq hCpq _
      have hwzero : qCoeff Cp (traceOp C Cp (heckeOp C p w)) m = 0 := by
        rw [hTrw, qCoeff_degeneracyOp hq0 hqCpCp _ m, if_neg hqm]
      -- STEP 4: the sieved part falls to the induction hypothesis at `L / q`.
      have hgL0 : ∀ n : ℕ, Nat.Coprime n (L / q) → qCoeff C g n = 0 := by
        intro n hn
        rw [hg n]
        split_ifs with hcq
        · have hqLq : q * (L / q) = L := Nat.mul_div_cancel' hqL
          have hcop := Nat.Coprime.mul_right hcq hn
          rw [hqLq] at hcop
          exact hh n hcop
        · rfl
      have hLqL : L / q ∣ L := ⟨q, (Nat.div_mul_cancel hqL).symm⟩
      have hLq : L / q < L := Nat.div_lt_self (Nat.pos_of_ne_zero hL0) hq.one_lt
      have hpLq : ¬ p ∣ L / q := fun hd => hpL (hd.trans hLqL)
      have hmLq : Nat.Coprime m (L / q) := Nat.Coprime.coprime_dvd_right hLqL hm
      have hgzero : qCoeff Cp (traceOp C Cp (heckeOp C p g)) m = 0 :=
        ih (L / q) hLq hpLq C Cp hC0 hpCp g hgL0 m hmLq
      -- ASSEMBLY: (4.6.13) brings the trace back down from level `C` to level `B`.
      have hUV1 : heckeOp C p (degeneracyOp B C 1 h) = degeneracyOp B C 1 (heckeOp B p h) :=
        heckeOp_degeneracyOp_of_dvd hB hC0 one_pos (by rwa [one_mul]) hp hpB hp1 h
      have h461 := traceOp_degeneracyOp_one_comm (A := B) (Ap := Bp) (B := C) (Bp := Cp)
        (L := q) (p := p) hB hp hpq hq0 hBp hCdef hCpdef (heckeOp B p h)
      have hfinal : qCoeff Cp (degeneracyOp Bp Cp 1 (traceOp B Bp (heckeOp B p h))) m = 0 := by
        rw [← h461, ← hUV1, hw, map_add, map_add, qCoeff_add, hgzero, hwzero, add_zero]
      rwa [qCoeff_degeneracyOp_one hBpCp _ m] at hfinal

/-- **MIYAKE LEMMA 4.6.7 + LEMMA 4.6.6(2) — THE TRACE OF THE COMPLEMENTARY PART
STILL HAS NO PRIME-TO-`L` COEFFICIENTS** (PROVEN 2026-07-27 over
`qCoeff_traceOp_heckeOp_eq_zero_aux` above; Miyake, *Modular Forms*, Lemma 4.6.7
p. 159 and the estimate closing (4.6.14), pp. 161–162): if every `q`-expansion
coefficient of `h ∈ S₂(Γ₀(B))` at an index COPRIME TO `L` vanishes, then the same
is true of `Tr^B_{Bp}(U_p h)`.

This is move 4, and it is the whole reason the peeling step's error term is
invisible: `h` is `f` minus its `L`-sieve, so by construction `h` is supported on
the indices NOT coprime to `L`, and the claim is that neither `U_p` nor the trace
can move mass back onto the coprime indices.

PROOF AS FORMALIZED — **Lemma 4.6.7 IS NOT NEEDED; A SIEVE INDUCTION REPLACES
IT.**  Miyake first decomposes `h = Σ_{q ∣ L, q prime} h_q(qz)` (Lemma 4.6.7: a
form supported off the prime-to-`L` indices is a sum of `V_q`-images), then
commutes the trace past each `V_q` by Lemma 4.6.6(1)–(2).  In Lean that
decomposition is a FAMILY of cusp forms living at a family of DIFFERENT levels,
indexed by `L.primeFactors` — a dependent-type family, and by far the most
expensive part of the argument.  `qCoeff_traceOp_heckeOp_eq_zero_aux` above
removes it: peel the single prime `q = L.minFac`, send the `q`-sieve of `h` to
the induction hypothesis at `L / q`, and handle the complement — which is
supported on the multiples of `q`, hence a single `V_q`-image by Theorem 4.6.4 —
with Lemma 4.6.6(2) alone.  So of Miyake's inputs to move 4 only **4.6.6(1)**
(`traceOp_degeneracyOp_one_comm`) and **4.6.6(2)** (`traceOp_degeneracyOp_comm`)
are consumed at all; **4.6.7 does not appear anywhere in the finished proof.**
Of those two, **4.6.6(2) is PROVEN** (2026-07-27, by the coset bijection, with
surjectivity done directly so that no `Γ₀`-index formula was needed).

`1 < L` is NOT consumed (it is written `_hL`), and that is not an oversight: the
statement is true at `L = 1` as well, where the hypothesis forces `h = 0`.  It is
kept in the signature because it marks the composite case of Miyake's induction
and because the consumer
`exists_smul_traceOp_heckeOp_qCoeff_coprime_eq_zero` supplies it anyway.  What IS
load-bearing is `¬ p ∣ L`: it excludes `L = 0` (where `(n, 0) = 1` means `n = 1`
and the statement would be false) and it gives `p ≠ L.minFac`, consumed by all
three commutation steps.

Note `U_p` is spelled `heckeOp B p` here, which is legitimate exactly because
`p ∣ B`: `qCoeff_heckeOp` then reads `a_m(heckeOp B p h) = a_{pm}(h)` with no
correction term, i.e. `heckeOp B p` IS `U_p` at that level. -/
theorem qCoeff_traceOp_heckeOp_eq_zero {B Bp p L : ℕ} [NeZero B] [NeZero Bp]
    (hB : 0 < B) (hp : p.Prime) (hBp : p * Bp = B) (_hL : 1 < L) (hpL : ¬ p ∣ L)
    {h : CuspForm (Gamma0GL B) 2}
    (hh : ∀ n : ℕ, Nat.Coprime n L → qCoeff B h n = 0) :
    ∀ m : ℕ, Nat.Coprime m L →
      qCoeff Bp (traceOp B Bp (heckeOp B p h)) m = 0 :=
  qCoeff_traceOp_heckeOp_eq_zero_aux hp L hpL B Bp hB hBp h hh

/-- **MIYAKE'S PEELING RESIDUE, REPAIRED: MOVES 3–4, THE COEFFICIENT BOOKKEEPING
OF THE TRACE** (PROVEN 2026-07-27 over the three Miyake leaves above; Miyake,
*Modular Forms*, (4.6.12)–(4.6.14), pp. 160–162).

This replaces `exists_smul_traceOp_qCoeff_coprime_eq_zero`, which was FALSE — see
the FALSITY AUDIT on `not_exists_smul_traceOp_qCoeff_coprime_eq_zero` above.  The
witness traces `U_p f = heckeOp M p f`, not `f`: Miyake's operator is the double
coset `Γ₀(M) [1, 0; 0, p] Γ₀(M/p)`, and `Tr ∘ U_p` is `p` times it (their product
is a single double coset, with multiplicity `p(d+1)/(d+1) = p`), so with the
constant existential this IS Miyake's witness.

PROOF, in Miyake's four moves.  The only inputs still cited from Miyake are
`exists_cuspForm_qCoeff_sieve` (Lemma 4.6.5, move 1),
`traceOp_degeneracyOp_one_comm` (Lemma 4.6.6(1), move 3) and
`traceOp_degeneracyOp_comm` (Lemma 4.6.6(2)), which move 4 consumes; the last of
these is PROVEN (2026-07-27).  Move 4 itself,
`qCoeff_traceOp_heckeOp_eq_zero`, is PROVEN over those, and Miyake's Lemma 4.6.7
turned out not to be needed at all (see its docstring).  Check the current
open/closed status of the other two with the compiler, not with this note.

1. `g` = the `L`-sieve of `f` at level `B = M L²`
   (`exists_cuspForm_qCoeff_sieve`, PROVEN).  Its coefficients vanish at every
   `p ∤ n`: at `(n, L) = 1` by the hypothesis `hf`, and off that by construction.
2. Theorem 4.6.4 at level `B` — `mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd`
   above, PROVEN — writes `g = V_p g_p` with `g_p ∈ S₂(Γ₀(Bp))`, `Bp = (M/p) L²`.
3. `U_p g = V_1 g_p` (a two-line coefficient computation: `a_m(U_p g) = a_{pm}(g)
   = a_m(g_p)`), so `Tr^B_{Bp}(U_p g) = κ · g_p` with `κ ≠ 0` by
   `exists_smul_traceOp_degeneracyOp_one`.  This is (4.6.12), and it is where the
   level comes back DOWN.  Lemma 4.6.6(1) (`traceOp_degeneracyOp_one_comm`, PROVEN)
   then identifies the trace computed at level `B` with the one at level `M`,
   which is (4.6.13) and the only place `p ∤ L` is used.
4. `h = V_1 f − g` is the complementary part, supported off the indices coprime to
   `L`; `qCoeff_traceOp_heckeOp_eq_zero` (PROVEN, over Lemma 4.6.6(2)) says its
   trace contributes nothing at those indices.  That is (4.6.14), and it closes
   the estimate.

Assembling: for `m` coprime to `L`, `a_m(Tr^M_{M/p}(U_p f)) = κ · a_{pm}(f)`, so
`c = κ⁻¹` works — at `p ∤ n` the conclusion is the hypothesis `hf` itself, and at
`n = pm` it is that identity.

FAITHFULNESS.  The constant is left existential deliberately, so no normalization
convention can make the leaf false; the OPERATOR is what the previous cut got
wrong, and `not_exists_smul_traceOp_qCoeff_coprime_eq_zero` is the machine-checked
record of that.  `1 < L` marks the composite case of Miyake's induction and `¬ p ∣ L`
is his square-freeness reduction, consumed in move 3.  NOT vacuous: `f = 0` gives
`c` arbitrary, and for `f = V_p u + V_q w` with `q ∣ L` the trace genuinely
recovers `u`. -/
theorem exists_smul_traceOp_heckeOp_qCoeff_coprime_eq_zero {M p L : ℕ}
    [NeZero M] [NeZero (M / p)]
    (hM : 0 < M) (hp : p.Prime) (hpM : p ∣ M) (hL : 1 < L) (hpL : ¬ p ∣ L)
    {f : CuspForm (Gamma0GL M) 2}
    (hf : ∀ n : ℕ, ¬ p ∣ n → Nat.Coprime n L → qCoeff M f n = 0) :
    ∃ c : ℂ, ∀ n : ℕ, Nat.Coprime n L →
      qCoeff M (f - degeneracyOp (M / p) M p
        (c • traceOp M (M / p) (heckeOp M p f))) n = 0 := by
  have hL0 : 0 < L := by omega
  set N := M / p with hNdef
  have hpN : p * N = M := Nat.mul_div_cancel' hpM
  have hN0 : 0 < N := Nat.div_pos (Nat.le_of_dvd hM hpM) hp.pos
  set B := M * L ^ 2 with hBdef
  set Bp := N * L ^ 2 with hBpdef
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hBp0 : 0 < Bp := by rw [hBpdef]; positivity
  haveI : NeZero B := ⟨hB0.ne'⟩
  haveI : NeZero Bp := ⟨hBp0.ne'⟩
  have hpBp : p * Bp = B := by rw [hBdef, hBpdef, ← hpN]; ring
  have hpB : p ∣ B := ⟨Bp, hpBp.symm⟩
  have hBdiv : B / p = Bp := by rw [← hpBp, Nat.mul_div_cancel_left _ hp.pos]
  have hBpdvdB : Bp ∣ B := ⟨p, by rw [← hpBp]; ring⟩
  have hMB : M ∣ B := ⟨L ^ 2, hBdef⟩
  have hNBp : N ∣ Bp := ⟨L ^ 2, hBpdef⟩
  have hpcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpL
  -- MOVE 1: the `L`-sieve of `f`, at level `B = M L²`
  obtain ⟨g, hg⟩ := exists_cuspForm_qCoeff_sieve hM hL0 hBdef.symm f
  have hgz : ∀ n : ℕ, ¬ p ∣ n → qCoeff B g n = 0 := by
    intro n hn
    rw [hg n]
    split_ifs with hc
    · exact hf n hn hc
    · rfl
  -- MOVE 2: Theorem 4.6.4 at level `B`
  have hmem := mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd hB0 hp hpB hgz
  rw [hBdiv] at hmem
  obtain ⟨gp, hgp⟩ := hmem
  have hpBpdvd : p * Bp ∣ B := ⟨1, by rw [mul_one]; exact hpBp.symm⟩
  -- MOVE 3: `U_p g` is induced from level `Bp`, so its trace is `κ · g_p`
  have hUg : heckeOp B p g = degeneracyOp Bp B 1 gp := by
    refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
    rw [qCoeff_heckeOp hB0 hp g m, if_pos hpB, add_zero, ← hgp,
      qCoeff_degeneracyOp hp.pos hpBpdvd gp (p * m), if_pos ⟨m, rfl⟩,
      Nat.mul_div_cancel_left m hp.pos, qCoeff_degeneracyOp_one hBpdvdB gp m]
  obtain ⟨κ, hκ0, hκ⟩ := exists_smul_traceOp_degeneracyOp_one (A := B) (B := Bp) hBpdvdB
  have htrg : traceOp B Bp (heckeOp B p g) = κ • gp := by rw [hUg, hκ]
  -- MOVE 4: the complementary part contributes nothing at indices coprime to `L`
  set h := degeneracyOp M B 1 f - g with hhdef
  have hh : ∀ n : ℕ, Nat.Coprime n L → qCoeff B h n = 0 := by
    intro n hc
    rw [hhdef, qCoeff_sub, qCoeff_degeneracyOp_one hMB f n, hg n, if_pos hc, sub_self]
  have hC := qCoeff_traceOp_heckeOp_eq_zero hB0 hp hpBp hL hpL hh
  have hsplit : degeneracyOp M B 1 f = g + h := by rw [hhdef]; abel
  have hkey : traceOp B Bp (heckeOp B p (degeneracyOp M B 1 f))
      = κ • gp + traceOp B Bp (heckeOp B p h) := by
    rw [hsplit, map_add, map_add, htrg]
  -- (4.6.13): the trace at level `B` is the trace at level `M`, since `p ∤ L`
  have hB6 := traceOp_degeneracyOp_one_comm (A := M) (Ap := N) (B := B) (Bp := Bp)
    (L := L) (p := p) hM hp hpL hL0 hpN hBdef.symm hBpdef.symm (heckeOp M p f)
  have hcomm : heckeOp B p (degeneracyOp M B 1 f)
      = degeneracyOp M B 1 (heckeOp M p f) := by
    refine cuspForm_eq_of_forall_qCoeff_eq fun m => ?_
    rw [qCoeff_heckeOp hB0 hp _ m, if_pos hpB, add_zero,
      qCoeff_degeneracyOp_one hMB f (p * m),
      qCoeff_degeneracyOp_one hMB (heckeOp M p f) m,
      qCoeff_heckeOp hM hp f m, if_pos hpM, add_zero]
  have hmain : ∀ m : ℕ, Nat.Coprime m L →
      qCoeff N (traceOp M N (heckeOp M p f)) m = κ * qCoeff M f (p * m) := by
    intro m hm
    have h1 : qCoeff Bp (degeneracyOp N Bp 1 (traceOp M N (heckeOp M p f))) m
        = qCoeff N (traceOp M N (heckeOp M p f)) m :=
      qCoeff_degeneracyOp_one hNBp _ m
    have hpm : Nat.Coprime (p * m) L := Nat.coprime_mul_iff_left.mpr ⟨hpcop, hm⟩
    have hgpm : qCoeff Bp gp m = qCoeff M f (p * m) := by
      have h2 := hg (p * m)
      rw [if_pos hpm] at h2
      rw [← h2, ← hgp, qCoeff_degeneracyOp hp.pos hpBpdvd gp (p * m), if_pos ⟨m, rfl⟩,
        Nat.mul_div_cancel_left m hp.pos]
    rw [← h1, ← hB6, ← hcomm, hkey, qCoeff_add, qCoeff_smul, hC m hm, add_zero, hgpm]
  refine ⟨κ⁻¹, fun n hn => ?_⟩
  rw [qCoeff_sub, qCoeff_degeneracyOp hp.pos ⟨1, by rw [mul_one]; exact hpN.symm⟩ _ n]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, qCoeff_smul]
    obtain ⟨m, rfl⟩ := hpn
    rw [Nat.mul_div_cancel_left m hp.pos]
    have hm : Nat.Coprime m L := Nat.Coprime.coprime_dvd_left ⟨p, mul_comm p m⟩ hn
    rw [hmain m hm, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul, sub_self]
  · rw [if_neg hpn, sub_zero]
    exact hf n hpn hn

end MiyakeTraceBookkeeping

/-- **MIYAKE'S PEELING STEP** (Theorem 4.6.8's induction step), assembled from
the residual leaf above: the witness is Miyake's own,
`f_p = p(d+1)⁻¹ · (f ∣ Γ₀(M) · [1, 0; 0, p] · Γ₀(M/p))` — a scalar multiple of the
trace of `U_p f`, not of `f` itself (see the FALSITY AUDIT above) and not of
anything built from the sieve. -/
theorem exists_sub_degeneracyOp_qCoeff_coprime_eq_zero {M p L : ℕ}
    (hM : 0 < M) (hp : p.Prime) (hpM : p ∣ M) (hL : 1 < L) (hpL : ¬ p ∣ L)
    {f : CuspForm (Gamma0GL M) 2}
    (hf : ∀ n : ℕ, ¬ p ∣ n → Nat.Coprime n L → qCoeff M f n = 0) :
    ∃ g : CuspForm (Gamma0GL (M / p)) 2,
      ∀ n : ℕ, Nat.Coprime n L →
        qCoeff M (f - degeneracyOp (M / p) M p g) n = 0 := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd hM hpM) hp.pos).ne'⟩
  obtain ⟨c, hc⟩ :=
    exists_smul_traceOp_heckeOp_qCoeff_coprime_eq_zero hM hp hpM hL hpL hf
  exact ⟨c • traceOp M (M / p) (heckeOp M p f), hc⟩

/-- **THE MAIN LEMMA, INDUCTED OVER THE PRIME FACTORS OF A DIVISOR OF THE LEVEL**
(PROVEN 2026-07-27 over the two leaves above; Miyake, *Modular Forms*, Theorem
4.6.8): if the `q`-expansion coefficients of `f ∈ S₂(Γ₀(M))` vanish at every
index coprime to a divisor `L ∣ M`, then `f` lies in the sum of the images
`V_p S₂(Γ₀(M/p))` over the PRIME FACTORS OF `L`.

At `L = M` this is the Atkin–Lehner Main Lemma itself.  The extra generality in
`L` is not decoration: it is exactly what the induction needs, since peeling one
prime off replaces `L` by its prime-to-`p` part.

PROOF.  Strong induction on `L`.

* `L = 1`: every index is coprime to `1`, so every coefficient vanishes and
  `f = 0` (`cuspForm_eq_of_forall_qCoeff_eq`); the empty supremum is `⊥`.
* `L > 1`: pick `p ∈ L.primeFactors` and split `L = p^k · L'` with
  `L' = ordCompl[p] L` prime to `p`.  An `n` with `p ∤ n` and `(n, L') = 1` is
  coprime to `L`, so `f` satisfies the peeling hypothesis at `(p, L')`.
  - If `L' = 1` then `L` is a prime power and
    `mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd` puts `f` in
    `range V_p` directly.
  - Otherwise `exists_sub_degeneracyOp_qCoeff_coprime_eq_zero` produces `g` with
    `f − V_p g` satisfying the hypothesis for `L' < L`; the induction hypothesis
    puts `f − V_p g` in the supremum over `L'.primeFactors ⊆ L.primeFactors`,
    and `V_p g` is in the `p`-summand, so the sum `f` is in the supremum. -/
theorem mem_oldSubspace_of_qCoeff_coprime_eq_zero_of_dvd {M : ℕ} (hM : 0 < M) :
    ∀ L : ℕ, L ∣ M → ∀ f : CuspForm (Gamma0GL M) 2,
      (∀ n : ℕ, Nat.Coprime n L → qCoeff M f n = 0) →
      f ∈ ⨆ p ∈ L.primeFactors, LinearMap.range (degeneracyOp (M / p) M p) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro hLM f hf
    have hL0 : 0 < L := Nat.pos_of_dvd_of_pos hLM hM
    rcases eq_or_ne L 1 with rfl | hL1
    · -- `L = 1`: every coefficient vanishes, so `f = 0`.
      have hf0 : f = 0 := by
        refine cuspForm_eq_of_forall_qCoeff_eq fun n => ?_
        rw [qCoeff_zero_cuspForm]
        exact hf n (Nat.coprime_one_right n)
      simp [hf0]
    -- `1 < L`: pick a prime factor `p` of `L`.
    have hLgt : 1 < L := lt_of_le_of_ne hL0 (Ne.symm hL1)
    obtain ⟨p, hpmem⟩ := Nat.nonempty_primeFactors.mpr hLgt
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hpmem
    have hpM : p ∣ M := hpL.trans hLM
    -- the prime-to-`p` part of `L`
    set L' : ℕ := ordCompl[p] L with hL'def
    have hsplit : p ^ L.factorization p * L' = L :=
      Nat.ordProj_mul_ordCompl_eq_self L p
    have hL'dvdL : L' ∣ L := Nat.ordCompl_dvd L p
    have hL'M : L' ∣ M := hL'dvdL.trans hLM
    have hpL' : ¬ p ∣ L' := Nat.not_dvd_ordCompl hpp hL0.ne'
    have hL'0 : 0 < L' := Nat.ordCompl_pos p hL0.ne'
    have hL'ltL : L' < L := by
      refine lt_of_le_of_ne (Nat.le_of_dvd hL0 hL'dvdL) ?_
      intro h
      exact hpL' (h ▸ hpL)
    -- coprimality transfer: `¬ p ∣ n` and `(n, L') = 1` give `(n, L) = 1`
    have hcop : ∀ n : ℕ, ¬ p ∣ n → Nat.Coprime n L' → Nat.Coprime n L := by
      intro n hpn hnL'
      rw [← hsplit]
      exact Nat.Coprime.mul_right
        (Nat.Coprime.pow_right _
          ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpn).symm) hnL'
    have hfA : ∀ n : ℕ, ¬ p ∣ n → Nat.Coprime n L' → qCoeff M f n = 0 :=
      fun n h1 h2 => hf n (hcop n h1 h2)
    -- `range V_p` sits inside the target supremum
    have hVp : LinearMap.range (degeneracyOp (M / p) M p) ≤
        ⨆ q ∈ L.primeFactors, LinearMap.range (degeneracyOp (M / q) M q) :=
      le_iSup₂ (f := fun q (_ : q ∈ L.primeFactors) =>
        LinearMap.range (degeneracyOp (M / q) M q)) p hpmem
    rcases eq_or_ne L' 1 with hL'1 | hL'1
    · -- `L` is a prime power: Miyake Theorem 4.6.4 applies directly.
      refine hVp (mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd hM hpp hpM
        (f := f) fun n hpn => ?_)
      exact hfA n hpn (by rw [hL'1]; exact Nat.coprime_one_right n)
    · -- `L` has another prime factor: peel `p` and recurse on `L'`.
      have hL'gt : 1 < L' := lt_of_le_of_ne hL'0 (Ne.symm hL'1)
      obtain ⟨g, hg⟩ := exists_sub_degeneracyOp_qCoeff_coprime_eq_zero hM hpp hpM
        hL'gt hpL' (f := f) hfA
      have hrec := ih L' hL'ltL hL'M (f - degeneracyOp (M / p) M p g) hg
      have hmono : (⨆ q ∈ L'.primeFactors,
            LinearMap.range (degeneracyOp (M / q) M q)) ≤
          ⨆ q ∈ L.primeFactors, LinearMap.range (degeneracyOp (M / q) M q) :=
        iSup₂_le fun q hq =>
          le_iSup₂ (f := fun r (_ : r ∈ L.primeFactors) =>
            LinearMap.range (degeneracyOp (M / r) M r)) q
            (Nat.primeFactors_mono hL'dvdL hL0.ne' hq)
      have h1 := hmono hrec
      have h2 : degeneracyOp (M / p) M p g ∈
          ⨆ q ∈ L.primeFactors, LinearMap.range (degeneracyOp (M / q) M q) :=
        hVp ⟨g, rfl⟩
      have h3 := Submodule.add_mem _ h1 h2
      simpa using h3

/-- **THE ATKIN–LEHNER MAIN LEMMA FOR A JOINT GOOD-HECKE EIGENVECTOR** (PROVEN
2026-07-27 over the two Miyake leaves above; cut 2026-07-26 out of
`exists_oldSubspace_complement_vanishing` below;
Diamond–Shurman Theorem 5.7.1 read through Corollary 5.6.3 and §5.8,
Atkin–Lehner 1970 Lemma 18): a cusp form `v ∈ S₂(Γ₀(M))` that is an HONEST
eigenvector of every GOOD Hecke operator `T_q`, `q ∤ M`, and whose
`q`-expansion coefficients vanish at every index COPRIME to `M`, lies in the
old subspace `Σ_{p ∣ M} V_p S₂(Γ₀(M/p))`.

WHY THIS WAS CUT AS A REDUCTION AND NOT A RESTATEMENT (the previous owner's
justification, PRESERVED but NO LONGER LOAD-BEARING — the proof now given uses
none of it, because Miyake's elementary route needs no eigenvector hypothesis;
see the correction at the end of this docstring).  The consumer
`exists_oldSubspace_complement_vanishing` quantifies over ALL cusp forms; this
leaf quantifies only over JOINT EIGENVECTORS of the good Hecke algebra.  The
passage between the two is not bookkeeping: it is the spectral decomposition of
`S₂(Γ₀(M))` under the commuting family `{T_q : q ∤ M}`, and it consumes

* commutativity, `heckeOp_mul_comm` (PROVEN);
* SEMISIMPLICITY at the good primes,
  `heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level` (PROVEN over
  `exists_peterssonProduct_selfAdjoint_heckeOp`, itself PROVEN over the single
  domain leaf `exists_peterssonDomain`) — this is what turns the generalized
  eigenvectors the decomposition produces into honest ones, and it is FALSE at
  the bad primes, where `U_q` has genuine Jordan blocks;
* finite-dimensionality, `cuspForm_finiteDimensional` (PROVEN);
* stability of BOTH subspaces: the old subspace by `heckeOp_degeneracyOp`, and
  the vanishing-coefficient submodule because `a_n(T_q v) = a_{qn}(v) +
  q·a_{n/q}(v)` and `n` coprime to `M` forces `qn` and `n/q` coprime to `M`
  as well (this is where `q ∤ M` is used a second time).

So the analytic input this cut needs was ALREADY isolated in the tree, in
`exists_peterssonProduct_selfAdjoint_heckeOp`; the cut adds no new analytic
obligation and strictly shrinks the quantifier.  (The docstring of
`exists_oldSubspace_complement_vanishing` previously asserted that no
`exists_peterssonProduct_selfAdjoint_heckeOp` declaration exists in this tree.
That was already false when written — it is declared above in this same file —
and the claim is corrected here.)

WHAT REMAINS, in the two sorried Miyake leaves above:
`mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd` (Theorem 4.6.4, the
single-prime descent) and `exists_sub_degeneracyOp_qCoeff_coprime_eq_zero`
(the peeling step of Theorem 4.6.8, which needs the TRACE operator
`S₂(Γ₀(N)) → S₂(Γ₀(N/p))` built first).  The induction between them is PROVEN
in `mem_oldSubspace_of_qCoeff_coprime_eq_zero_of_dvd` above.

THE NEWFORM-DECOMPOSITION ROUTE, recorded because it is the classical
alternative and it is what the previous audits had in mind — it is NOT the route
taken, and pursuing it would re-enter the circularity noted below (D–S derive
multiplicity one FROM the Main Lemma, §5.8, not the other way round).
Classically: `S₂(Γ₀(M)) = ⊕_{M' ∣ M} ⊕_{f newform of level M'}
span{V_d f : d ∣ M/M'}`, each block stable under every `T_q`, `q ∤ M`, and
acted on by the SCALAR `a_q(f)` there (`heckeOp_degeneracyOp`).  A joint
good-eigenvector therefore lives in the span of the blocks with a fixed
eigensystem; writing `v = Σ_{d} c_d V_d f`, the hypothesis `a_n(v) = 0` at the
indices coprime to `M` forces `c_1 = 0` (it forces `a_1(v) = 0`, and `a_1` is
nonzero only on the `d = 1` component, where the newform is normalized), so `v`
is supported on the `d > 1` components, and each `V_d f` with `d > 1` factors
as `V_p (V_{d/p} f)` for any prime `p ∣ d`, with `V_{d/p} f` of level
`M'·(d/p) ∣ M/p`.  That is exactly membership in the old subspace.

WHY CARLTON'S PROOF DOES NOT WORK HERE — AND WHY THAT IS NOT THE END OF IT
(paragraph CORRECTED 2026-07-27; the previous version concluded, wrongly, that
no textbook route is available in this file's vocabulary).  Diamond–Shurman's
own proof of Theorem 5.7.1 (due to Carlton) does not run at `Γ₀` at all: it uses
the projections `π_d f = (1/d)·Σ_{b<d} f|[1, bN/d; 0, 1]`, which sieve the
`q`-expansion down to the indices divisible by `d`.  Those do NOT preserve
`S₂(Γ₀(M))` — for a newform `f` of level `M` with `p ∣ M`, `π_p f = a_p(f)·f(pτ)`
has level `Mp` and `a_p(f) ≠ 0` when `p ‖ M` — which is why D–S first conjugates
to `Γ¹(N)` and then descends to `Γ(N)`, where the argument becomes the
representation theory of `SL₂(ℤ/Nℤ)` (D–S Prop. 5.7.7) and the group-theoretic
Lemma 5.7.6.  Reproducing THAT route needs cusp forms for `Γ(N)`, which this
file's `Gamma0GL`-only vocabulary cannot express.

But D–S themselves record, on the same page, that Carlton's is not the only
proof: "An elementary proof of the Main Lemma is in [Lan76], and see also
[Miy89]."  Miyake, *Modular Forms*, §4.6 proves it ENTIRELY AT `Γ₀(N)` with a
nebentypus, by induction on the prime factors of the modulus, and that is the
route taken above — see the section header before
`mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd`.  Miyake's argument does
NOT sieve inside a fixed level: it lets the level go UP (the sieve is Miyake
Lemma 4.6.5) and then comes back down with a TRACE operator (Lemma 4.6.6), which
is exactly the move the `π_d` objection above shows to be unavoidable.

CONSEQUENCE FOR THIS NODE.  Miyake's proof consumes no eigenvector hypothesis,
so `hve` is NOT used here and is underscored.  The quantifier-shrinking that
justified this cut is therefore not load-bearing along the route actually taken;
the statement is unchanged and its consumer is untouched, but a future owner
should know that the general Main Lemma
(`mem_oldSubspace_of_qCoeff_coprime_eq_zero_of_dvd` above, at `L = M`) is what
is really being proven.

FAITHFULNESS.  No `v ≠ 0` hypothesis is needed or wanted: at `v = 0` the
conclusion is trivially true, so adding it would only weaken the leaf.  The
statement is NOT vacuous — its hypotheses are satisfiable by a nonzero form,
e.g. `v = V_p g` for any nonzero `g ∈ S₂(Γ₀(M/p))` that is a good-prime
eigenvector, whose coprime-index coefficients vanish by
`qCoeff_eq_zero_of_mem_oldSubspace` and which is a good-prime eigenvector at
level `M` by `heckeOp_degeneracyOp`. -/
theorem mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero {M : ℕ}
    (hM : 0 < M) {c : ℕ → ℂ} {v : CuspForm (Gamma0GL M) 2}
    (_hve : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q v = c q • v)
    (hvc : ∀ n : ℕ, Nat.Coprime n M → qCoeff M v n = 0) :
    v ∈ ⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p) :=
  mem_oldSubspace_of_qCoeff_coprime_eq_zero_of_dvd hM M dvd_rfl v hvc

/-- **THE NEW SUBSPACE DETECTS NO FORM WITH VANISHING GOOD COEFFICIENTS**
(PROVEN 2026-07-26 over the single leaf
`mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero` above; Diamond–Shurman
Theorem 5.7.1, Atkin–Lehner 1970 Lemma 18): the old subspace admits a COMPLEMENT `W`
inside which the only form whose `q`-expansion coefficients all vanish at indices
COPRIME to `M` is `0`.

AUDIT CORRECTION, 2026-07-26.  This node was previously a sorry leaf carrying
the whole analytic content, with `W` intended to be the *new* subspace — the
PETERSSON-orthogonal complement of the old subspace — and its docstring
recorded that "no `exists_peterssonProduct_selfAdjoint_heckeOp` declaration
exists in this tree".  That claim was FALSE at the time it was written: the
Petersson leaf is declared above in this very file, and the good-prime
semisimplicity it feeds (`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level`)
is PROVEN over it.  With that in hand the node is no longer analytic at all.

The previous owner's audit was nevertheless correct on its own terms and is
worth preserving, because it rules out the obvious cut: this statement is
LOGICALLY EQUIVALENT to its own consumer
`mem_oldSubspace_of_qCoeff_coprime_eq_zero`, and no cleverness in choosing `W`
can help, because if the vanishing-coefficient submodule strictly contained the
old subspace then EVERY complement would fail by a dimension count.  So the
reduction cannot come from the choice of `W`; it has to come from shrinking the
QUANTIFIER, which is what is done here.

PROOF.  Let `Kv = ⋂_{(n,M)=1} ker a_n` be the vanishing-coefficient submodule.

* `Kv` is stable under every good Hecke operator `T_q`, `q ∤ M`: by
  `qCoeff_heckeOp`, `a_n(T_q v) = a_{qn}(v) + q·a_{n/q}(v)`, and for `n` coprime
  to `M` both `qn` and `n/q` are again coprime to `M` — the first because
  `q ∤ M` makes `q` coprime to `M`, the second because `n/q ∣ n`.
* The good `T_q` commute (`heckeOp_mul_comm`) and `S₂(Γ₀(M))` is
  finite-dimensional (`cuspForm_finiteDimensional`), so
  `eq_iSup_inf_iInf_maxGenEigenspace_of_mapsTo` writes `Kv` as the supremum of
  its intersections with the simultaneous maximal generalized eigenspaces.
* Each such intersection consists of GENERALIZED joint eigenvectors, which
  good-prime semisimplicity
  (`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level`, PROVEN over the
  Petersson leaf) upgrades to HONEST joint eigenvectors; the single remaining
  leaf `mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero` then puts
  them in the old subspace.  Hence `Kv ≤ old`.
* Finally take for `W` ANY vector-space complement of the old subspace
  (`Submodule.exists_isCompl`).  The first conjunct is `IsCompl.sup_eq_top`;
  for the second, a `v ∈ W` with vanishing coprime coefficients lies in `Kv`,
  hence in the old subspace, hence in `old ⊓ W = ⊥`.

WHY ONLY `⊔ = ⊤` IS DEMANDED, not `IsCompl`.  Directness is not needed by
the consumer — only that every form splits — so the weaker requirement is
stated.  The statement is NOT thereby vacuous: `W = ⊤` satisfies `⊔ = ⊤` but
violates the second conjunct, since a nonzero old form has vanishing
coefficients at every index coprime to `M`
(`qCoeff_eq_zero_of_mem_oldSubspace`).  The two conjuncts together still force
`W` to meet the old subspace trivially.

THE PRIOR AUDIT, AND EXACTLY WHICH HALF OF IT SURVIVES.  A "THIS CUT IS A
RESTATEMENT, NOT A REDUCTION" audit stood here, and it was right about the
statement and wrong only about what follows from that.  Its content, preserved
because it still rules out the obvious attack: writing
`K := {v | ∀ n, n.Coprime M → qCoeff M v n = 0}` (a submodule, an intersection
of kernels of the functionals `qCoeffL M n`), the consumer
`mem_oldSubspace_of_qCoeff_coprime_eq_zero` below is exactly `K ≤ old`, the
converse `old ≤ K` is PROVEN (`qCoeff_eq_zero_of_mem_oldSubspace`), and this
node and that consumer are LOGICALLY EQUIVALENT — `(consumer ⇒ node)` by taking
any complement, `(node ⇒ consumer)` by the splitting argument below.  Hence
nothing whatever is gained by choosing `W` cleverly: if `K ⊋ old` then EVERY
complement of `old` fails the second conjunct, by the dimension count
`dim (W ⊓ K) ≥ dim W + dim K − dim S₂ = dim K − dim old > 0`.

What the audit then inferred — that a prover "must actually produce"
Diamond–Shurman 5.7.1 in full, via the Petersson-orthogonal complement and the
Atkin–Lehner involutions `W_Q` — does NOT follow, and is what the proof below
refutes.  Equivalence with the consumer blocks a reduction that comes from the
SHAPE of the statement; it says nothing about one that comes from shrinking the
QUANTIFIER.  Both this node and the consumer quantify over all cusp forms, and
the spectral decomposition of `S₂(Γ₀(M))` under the good Hecke algebra reduces
both to JOINT EIGENVECTORS — a strictly smaller class — at the cost of no new
analytic obligation.  The involutions `W_Q` are not used anywhere below.

WHAT THE PIN LACKS.  Nothing of the Petersson theory beyond the integrand
`petersson` and its `SL(2,ℤ)`-invariance and exponential decay exists in
`Mathlib.NumberTheory.ModularForms.Petersson`: the integral over a
fundamental domain, positive-definiteness, the inner-product structure and
the adjointness computation all have to be built, and there is no
Atkin–Lehner material in mathlib or in `~/cs/FLT`.  That machinery is not
needed for THIS node (see the paragraph above), but it is needed by the
sibling leaf `heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level`
(good-prime semisimplicity), which wants the same inner product and
self-adjointness of `T_q`.  As of 2026-07-26 that prerequisite is CUT DOWN
to `exists_peterssonDomain` above: the Petersson product itself
(`exists_peterssonProduct_selfAdjoint_heckeOp`) is PROVEN over it,
definiteness included.  (2026-07-27: `exists_peterssonDomain` is now PROVEN
in turn, over the two leaves `volume_smul_inter_gamma0Domain_eq_zero` and
`peterssonSelfAdjoint_of_gamma0FundamentalDomain`, with the domain itself
constructed and its finite volume, interior and covering property proven.) -/
theorem exists_oldSubspace_complement_vanishing (M : ℕ) (hM : 0 < M) :
    ∃ W : Submodule ℂ (CuspForm (Gamma0GL M) 2),
      (⨆ p ∈ M.primeFactors,
        LinearMap.range (degeneracyOp (M / p) M p)) ⊔ W = ⊤ ∧
      ∀ v ∈ W, (∀ n : ℕ, Nat.Coprime n M → qCoeff M v n = 0) → v = 0 := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (Gamma0GL M) 2) :=
    cuspForm_finiteDimensional M hM
  -- The submodule cut out by vanishing of every coefficient at an index
  -- coprime to `M`.
  set Kv : Submodule ℂ (CuspForm (Gamma0GL M) 2) :=
    ⨅ n : {n : ℕ // Nat.Coprime n M}, LinearMap.ker (qCoeffL M n.1) with hKvdef
  have hmemKv : ∀ v : CuspForm (Gamma0GL M) 2,
      v ∈ Kv ↔ ∀ n : ℕ, Nat.Coprime n M → qCoeff M v n = 0 := by
    intro v
    simp only [hKvdef, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffL_apply,
      Subtype.forall]
  -- The good Hecke operators commute and preserve `Kv`.
  have hcomm : ∀ i j : {q : ℕ // q.Prime ∧ ¬ q ∣ M},
      Commute (heckeOp M i.1) (heckeOp M j.1) := fun i j =>
    heckeOp_mul_comm hM i.2.1 j.2.1
  have hst : ∀ i : {q : ℕ // q.Prime ∧ ¬ q ∣ M},
      Set.MapsTo (heckeOp M i.1) Kv Kv := by
    intro i x hx
    have hx' : ∀ n : ℕ, Nat.Coprime n M → qCoeff M x n = 0 := (hmemKv x).mp hx
    refine (hmemKv _).mpr fun n hn => ?_
    have hqc : Nat.Coprime i.1 M := (Nat.Prime.coprime_iff_not_dvd i.2.1).mpr i.2.2
    have h1 : qCoeff M x (i.1 * n) = 0 :=
      hx' _ (Nat.coprime_mul_iff_left.mpr ⟨hqc, hn⟩)
    rw [qCoeff_heckeOp hM i.2.1 x n, h1, if_neg i.2.2]
    by_cases hdvd : i.1 ∣ n
    · have h2 : qCoeff M x (n / i.1) = 0 :=
        hx' _ (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd) hn)
      rw [if_pos hdvd, h2]
      ring
    · rw [if_neg hdvd]
      ring
  -- Every form with vanishing coprime coefficients is old: decompose `Kv` along
  -- the joint generalized eigenspaces of the good Hecke operators, upgrade each
  -- generalized eigenvector to an honest one by good-prime semisimplicity, and
  -- apply the eigenvector case.
  have hKO : Kv ≤ ⨆ p ∈ M.primeFactors,
      LinearMap.range (degeneracyOp (M / p) M p) := by
    refine le_trans (le_of_eq (eq_iSup_inf_iInf_maxGenEigenspace_of_mapsTo
      (fun q : {q : ℕ // q.Prime ∧ ¬ q ∣ M} => heckeOp M q.1) hcomm Kv hst)) ?_
    refine iSup_le fun ψ => ?_
    intro v hv
    obtain ⟨hvK, hvE⟩ := Submodule.mem_inf.mp hv
    refine mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero hM
      (c := fun q => if h : q.Prime ∧ ¬ q ∣ M then ψ ⟨q, h⟩ else 0)
      (fun q hq hqM => ?_) ((hmemKv v).mp hvK)
    obtain ⟨k, hk⟩ := (Module.End.mem_iInf_maxGenEigenspace_iff
      (fun q : {q : ℕ // q.Prime ∧ ¬ q ∣ M} => heckeOp M q.1) ψ v).mp hvE
        ⟨q, hq, hqM⟩
    rw [dif_pos (show q.Prime ∧ ¬ q ∣ M from ⟨hq, hqM⟩)]
    exact heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level hM hq hqM _
      (n := k) (by simpa using hk)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl
    (⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p))
  refine ⟨W, hW.sup_eq_top, fun v hvW hvc => ?_⟩
  simpa using hW.disjoint.le_bot
    (Submodule.mem_inf.mpr ⟨hKO ((hmemKv v).mpr hvc), hvW⟩)

/-- **ATKIN–LEHNER MAIN LEMMA: no coefficients away from the level forces a form
into the OLD SUBSPACE** (PROVEN 2026-07-26 over the single analytic leaf
`exists_oldSubspace_complement_vanishing` above; cut 2026-07-26 out of
`exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`;
Diamond–Shurman Theorem 5.7.1, Atkin–Lehner 1970 Lemma 18): if every
`q`-expansion coefficient `a_n(w)` at an index `n` COPRIME to `M` vanishes, then
`w` lies in the old subspace `Σ_{p ∣ M, p prime} V_p S₂(Γ₀(M/p))`.

This is the ANALYTIC half of the Atkin–Lehner content, and it is the half with
no elementary substitute: the classical proof runs through the Petersson inner
product and the Atkin–Lehner involutions `W_Q`.  (CORRECTED 2026-07-27: this
sentence used to end "neither of which exists on this pin".  FALSE — both exist
HERE and are proven: the Petersson inner product with `T_q` self-adjoint is
`exists_peterssonProduct_selfAdjoint_heckeOp` (~32056) over `exists_peterssonDomain`
(~31971), and `W_Q` is `atkinLehnerOp` (~39586) over `exists_atkinLehnerOp`
(~39501).  The claim was only ever true of mathlib and of `~/cs/FLT`.)  Note it
needs NO eigenvector hypothesis — it is a statement about a single
cusp form, exactly as in Diamond–Shurman.

STATUS 2026-07-26 (SUPERSEDES the paragraph this replaces).  This node is still
a three-line splitting argument over `exists_oldSubspace_complement_vanishing`
above — `w = a + b` with `a` old and `b` in the complement; `a` has vanishing
good coefficients by the elementary converse
`qCoeff_eq_zero_of_mem_oldSubspace`, hence so does `b = w − a`, hence `b = 0` —
but that node is now itself PROVEN, so the whole cluster rests on the single
leaf `mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`: the same
statement restricted to JOINT EIGENVECTORS of the good Hecke operators.

DEPENDENCY NOTE (corrected 2026-07-26 — the previous version of this paragraph
was STALE and said the opposite; two owners caught it independently).  `V_p`
itself is BUILT and sorry-free (`degeneracyOp` above, with `degeneracyOp_coe`
and `qCoeff_degeneracyOp`), so nothing definitional remains anywhere in this
cluster.  Contrary to the note that stood here,
`exists_peterssonProduct_selfAdjoint_heckeOp` DOES exist in this tree and is
PROVEN, over `exists_peterssonDomain` — which as of 2026-07-27 is itself
PROVEN, over the two leaves `volume_smul_inter_gamma0Domain_eq_zero`
(a.e.-disjointness, reduced to `volume (𝒟 \ 𝒟ᵒ) = 0`) and
`peterssonSelfAdjoint_of_gamma0FundamentalDomain` (the double-coset
unfolding).  So the Petersson product is available as a definite
conjugate-symmetric form as soon as those two are discharged, and they are
SHARED with the sibling
`heckeOp_eq_smul_of_generalizedEigen_of_not_dvd_level` (good-prime
semisimplicity).

Consequently the passage from "all cusp forms" to "joint good-Hecke
eigenvectors" is available and has been taken in
`exists_oldSubspace_complement_vanishing` above.  What remains under this
cluster is therefore NOT the Petersson product and NOT the involutions `W_Q` —
neither is used in the eigenvector case — but the newform decomposition itself,
isolated in `mem_oldSubspace_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`. -/
theorem mem_oldSubspace_of_qCoeff_coprime_eq_zero {M : ℕ} (hM : 0 < M)
    {w : CuspForm (Gamma0GL M) 2}
    (hwc : ∀ n : ℕ, Nat.Coprime n M → qCoeff M w n = 0) :
    w ∈ ⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p) := by
  obtain ⟨W, hsup, hW⟩ := exists_oldSubspace_complement_vanishing M hM
  have hmem : w ∈ (⨆ p ∈ M.primeFactors,
      LinearMap.range (degeneracyOp (M / p) M p)) ⊔ W := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hb0 : b = 0 := by
    refine hW b hb fun n hn => ?_
    rw [eq_sub_of_add_eq' hab]
    have hsub : qCoeff M (w - a) n = qCoeff M w n - qCoeff M a n := by
      simpa using (qCoeffL M n).map_sub w a
    rw [hsub, hwc n hn, qCoeff_eq_zero_of_mem_oldSubspace hM ha hn, sub_zero]
  have haw : a = w := by rw [← hab, hb0, add_zero]
  exact haw ▸ ha

end ComplexHeckeAlgebra

open scoped TensorProduct

section ConductorCut

/-- **The newform carrier** (Diamond–Shurman §5.8, coefficient-level):
`g ∈ S₂(Γ₀(M))` is a normalized full-Hecke eigenform
(`IsWeightTwoEigenform`, Prop. 5.8.5) whose away-from-`M` prime
eigensystem does not arise from any normalized eigenform of a strictly
smaller level dividing `M` — the *minimal-level* characterization of
newform-ness.

WHY THIS SPELLING, AND A CORRECTION (2026-07-27; the sentence corrected
here was harvested verbatim by at least one route audit far below, which
is exactly the damage a stale absence claim does).  The original version
of this paragraph justified the spelling by saying it was "the only
spelling available on a pin with no newform theory, no Petersson product
and no oldform degeneracy maps".  **The second and third clauses were
true when written (2026-07-24) and are now FALSE**: the degeneracy block
landed 2026-07-26 and the Petersson section closed out 2026-07-26/27, in
THIS FILE.  What is actually true:

* the OLDFORM DEGENERACY MAPS exist here and are PROVEN — `degeneracyOp
  N M d` (~32464) is `V_d : S₂(Γ₀(N)) → S₂(Γ₀(M))`, `f ↦ (z ↦ f(dz))`,
  with `degeneracyOp_coe`, the coefficient identity `qCoeff_degeneracyOp`
  (`a_m(V_d f) = a_{m/d}(f)`, `0` unless `d ∣ m`), `degeneracyOp_injective`
  and `heckeOp_degeneracyOp` (`T_q ∘ V_d = V_d ∘ T_q` at `q ∤ M`).  The
  old subspace is `⨆ p ∈ M.primeFactors, range (degeneracyOp (M/p) M p)`,
  and the Atkin–Lehner Main Lemma over it —
  `mem_oldSubspace_of_qCoeff_coprime_eq_zero` (~34727), its converse
  `qCoeff_eq_zero_of_mem_oldSubspace` (~32580), and
  `mem_range_degeneracyOp_of_qCoeff_eq_zero_of_not_dvd` (~33817) — is
  PROVEN;
* the PETERSSON PRODUCT exists here too, in the `PeterssonProduct`
  section (~30963–32090), over mathlib's integrand
  `Mathlib/NumberTheory/ModularForms/Petersson.lean`.  PROVEN:
  `peterssonIntegrableOn`, `petersson_self_eq_ofReal`,
  `cuspForm_eq_zero_of_setIntegral_petersson_self_eq_zero` (definiteness),
  `petersson_slash_two`, `setIntegral_petersson_slash_adjoint`,
  `peterssonIntegrableOn_slash`,
  `peterssonSelfAdjoint_of_gamma0FundamentalDomain`,
  `exists_peterssonDomain` and `exists_peterssonProduct_selfAdjoint_heckeOp`
  (the inner product with `T_q` self-adjoint at every `q ∤ M`, definiteness
  included).  The ONE open leaf left in that section is
  `setIntegral_heckeRep_unfold` (~31782, the coset tiling of the Hecke
  integral); the Atkin–Lehner involution `atkinLehnerOp M Q` (~39586) and
  `exists_atkinLehnerOp` (~39501) are PROVEN as well, with open leaves
  `heckeTransform_slash_atkinLehnerRep` (~39675),
  `heckeOp_self_atkinLehnerOp_eigen_of_newform` (~39756) and
  `qCoeff_one_atkinLehnerOp_of_newform` (~39834).

So the honest justification is narrower, and it survives the correction:
what is still missing is not the product or the maps but the OLD ⊕ NEW
DIRECT-SUM DECOMPOSITION itself — `S₂(Γ₀(M)) = old ⊕ new` with the new
part the Petersson-orthogonal complement and multiplicity one on it.
Without that decomposition there is no `S₂(Γ₀(M))^new` to be a member of,
so the minimal-level spelling is what this carrier uses; the soundness
audit below is what pins it to the classical notion.  A future owner who
wants the classical spelling should build the decomposition, NOT the
degeneracy maps or the Petersson product.

SOUNDNESS AUDIT (2026-07-24, both directions):

* every classical newform `g` of level `M` inhabits the carrier: it is
  a normalized full-Hecke eigenform (D–S Theorem 5.8.2 with
  Prop. 5.8.5), and no eigenform `g'` of a proper divisor level
  `M' ∣ M` shares its eigensystem away from `M` — behind `g'` lies a
  newform of level `M₀ ∣ M'` with the same away-from-`M'` eigensystem
  (Prop. 5.8.4), which would then share `g`'s eigensystem away from
  `M`, and two distinct newforms never do (strong multiplicity one,
  the Main Lemma engine behind D–S Theorem 5.8.3), while a newform of
  level `M₀ ∣ M' < M` is certainly distinct from `g`;
* conversely every inhabitant is a classical newform: behind it lies a
  newform `g₀` of level `M₀ ∣ M` with the same eigensystem away from
  `M` (Prop. 5.8.4); were `M₀ ≠ M`, then `g₀` itself — a normalized
  full-Hecke eigenform of level `M₀` — would witness exactly what
  `eigensystem_minimal` excludes, so `M₀ = M`; and a normalized
  full-Hecke eigenform of level `M` sharing a level-`M` newform's
  eigensystem away from `M` IS that newform (strong multiplicity one
  again, in the full-eigenvalue form).

Consequently the two nodes below that quantify over this carrier
(`exists_galoisRep_charFrob_of_weightTwoNewform` ~44161 and
`weightTwoNewform_level_dvd_two_of_isHardlyRamified` ~52096) quantify
exactly over the forms for which the classical theory provides attached
representations and conductor control.  (This sentence used to call them
"the two sorried leaves below"; corrected 2026-07-27 — both are now
PROVEN assemblies over named sub-leaves of their own, so the audit above
is what justifies THEIR statements, not what justifies dispatching
anyone at them.) -/
structure IsWeightTwoNewform (M : ℕ) (g : CuspForm (Gamma0GL M) 2) : Prop
    extends IsWeightTwoEigenform M g where
  /-- The away-from-`M` eigensystem of `g` occurs at no strictly
  smaller level dividing `M`. -/
  eigensystem_minimal : ∀ M' : ℕ, M' ∣ M → M' ≠ M →
    ∀ g' : CuspForm (Gamma0GL M') 2, IsWeightTwoEigenform M' g' →
      ¬ ∀ (q : ℕ), q.Prime → ¬ q ∣ M → qCoeff M' g' q = qCoeff M g q

section ComplexHeckeAlgebra

/-- **NEWFORM DECOMPOSITION: an eigenvector in the old subspace has its
eigensystem realized at a PROPER divisor level** (PROVEN — label
corrected 2026-07-26, formerly the sorry leaf cut 2026-07-26
out of `exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`;
Diamond–Shurman Theorem 5.8.2 with Proposition 5.8.5): a NONZERO `w` in the old
subspace which is an honest eigenvector of every GOOD Hecke operator `T_q`,
`q ∤ M`, with eigenvalues `c q`, has `c` realized by a normalized weight-2
eigenform of some level `M' ∣ M` with `M' ≠ M`.

This is the ALGEBRAIC half of the Atkin–Lehner content.  The classical argument:
`S₂(Γ₀(M))` is the direct sum, over divisors `M' ∣ M` and newforms `f` of level
`M'`, of the blocks `span{V_d f : d ∣ M/M'}`; each block is stable under every
`T_q` with `q ∤ M` and that operator acts on it by the SCALAR `a_q(f)` (because
`V_d` commutes with `T_q` for `q ∤ d`, and `d ∣ M`).  The old subspace is exactly
the sum of the blocks with `M' ≠ M`.  So a nonzero joint good-prime eigenvector
lying in it has a nonzero component in some block with `M' ≠ M`, and comparing
eigenvalues gives `a_q(f) = c q` for every `q ∤ M`; a newform of level `M'` is in
particular a normalized weight-2 eigenform (Prop. 5.8.5), i.e. an inhabitant of
`IsWeightTwoEigenform M'`.

FAITHFULNESS.  All three of `hw`, `hwe`, `hold` are load-bearing, and for the
same reasons audited on the parent node below: without `hw` the conclusion is
false at `M = 1`; without `hold` a level-`M` newform `w = g` is a counterexample,
since `eigensystem_minimal` forbids any proper divisor level from realizing its
eigensystem; without `hwe` the eigensystem `c` is unconstrained by the hypotheses
while the conclusion constrains it.

STATUS 2026-07-26: **PROVEN**, over the single leaf
`exists_weightTwoEigenform_of_heckeOp_eigen_of_level_dvd` above.  The
degeneracy calculus this node was expected to need is now all PROVEN and
consumed here: `heckeOp_degeneracyOp` (commutation of `V_d` with the good
`T_q`), `degeneracyOp_injective`, and the SPECTRAL DESCENT
`exists_heckeOp_eigen_of_mem_oldSubspace`, which trades membership in the
SUM `Σ_p V_p S₂(Γ₀(M/p))` for a nonzero joint eigenvector at ONE level
`M/p`.  Given that, the remaining content is exactly "an eigensystem carried
by a nonzero joint eigenvector at level `M/p` is realized by a normalized
eigenform of a divisor level", which is the leaf.

A CORRECTION to the earlier note here, worth recording because it drove the
cut: descent out of the old subspace is NOT a pure coefficient computation.
The images `range V_p` are not independent — `V_{pq}f` lies in `range V_p`
and in `range V_q` — so a joint eigenvector in their SUM has no readable
component.  The step is spectral: each image is `T_q`-stable, so the
simultaneous generalized eigenspace decomposition of a commuting family can
be intersected with it.  Injectivity and commutation ARE pure coefficient
computations, and they are proven above; the descent is not, and it is
proven above too.

The level bound is arithmetic: `M' ∣ M/p` and `M/p < M` give `M' ≠ M`. -/
theorem exists_weightTwoEigenform_of_mem_oldSubspace {M : ℕ} (hM : 0 < M)
    {c : ℕ → ℂ} {w : CuspForm (Gamma0GL M) 2} (hw : w ≠ 0)
    (hwe : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q w = c q • w)
    (hold : w ∈ ⨆ p ∈ M.primeFactors, LinearMap.range (degeneracyOp (M / p) M p)) :
    ∃ M' : ℕ, M' ∣ M ∧ M' ≠ M ∧ ∃ g' : CuspForm (Gamma0GL M') 2,
      IsWeightTwoEigenform M' g' ∧
        ∀ q : ℕ, q.Prime → ¬ q ∣ M → qCoeff M' g' q = c q := by
  obtain ⟨p, hp, u, hu0, hue⟩ :=
    exists_heckeOp_eigen_of_mem_oldSubspace hM hw hwe hold
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ M := Nat.dvd_of_mem_primeFactors hp
  have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd hM hpd) hpp.pos
  have hdvdM : M / p ∣ M := Nat.div_dvd_of_dvd hpd
  have hlt : M / p < M := Nat.div_lt_self hM hpp.one_lt
  obtain ⟨M', hM'dvd, g', hg', hgc⟩ :=
    exists_weightTwoEigenform_of_heckeOp_eigen_of_level_dvd hpos hdvdM hu0 hue
  refine ⟨M', hM'dvd.trans hdvdM, ?_, g', hg', hgc⟩
  have hle : M' ≤ M / p := Nat.le_of_dvd hpos hM'dvd
  omega

/-- **ATKIN–LEHNER: a good-prime joint eigenvector with no coefficients
away from the level comes from a SMALLER level** (PROVEN 2026-07-26 over
the two classical halves `mem_oldSubspace_of_qCoeff_coprime_eq_zero`
(the analytic Main Lemma) and `exists_weightTwoEigenform_of_mem_oldSubspace`
(the algebraic newform decomposition), which meet at the OLD SUBSPACE
`Σ_{p ∣ M} V_p S₂(Γ₀(M/p))` — now expressible because the degeneracy
operator `degeneracyOp` is built above.  Cut
2026-07-26 out of `exists_smul_of_heckeOp_eq_smul_of_not_dvd_level`;
Atkin–Lehner 1970, Diamond–Shurman Theorem 5.7.1 — the *Main Lemma* —
together with Theorem 5.8.2, the newform decomposition): a NONZERO
`w ∈ S₂(Γ₀(M))` which is an honest eigenvector of every GOOD Hecke
operator `T_q`, `q ∤ M`, with eigenvalues `c q`, and ALL of whose
`q`-expansion coefficients `a_n(w)` at indices `n` COPRIME to `M`
vanish, forces the eigensystem `c` to be realized by a normalized
weight-2 eigenform of a PROPER divisor level `M' ∣ M`, `M' ≠ M`.

This is the entire Atkin–Lehner content of strong multiplicity one, and
it is deliberately stated with NO reference to newforms, to `g`, or to
minimality: it is a statement about the OLD subspace alone. Its single
consumer `exists_smul_of_heckeOp_eq_smul_of_not_dvd_level` supplies the
newform and reads the conclusion straight into
`IsWeightTwoNewform.eigensystem_minimal`.

CLASSICAL PROOF, and the DECOMPOSITION POINTER for whoever attacks it.
Two classical theorems, in this order.

* (Main Lemma; D–S Thm 5.7.1, Atkin–Lehner 1970 Lemma 18) `a_n(w) = 0`
  for every `n` coprime to `M` forces `w` into the OLD subspace
  `Σ_{p ∣ M} V_p S₂(Γ₀(M/p))`, where `(V_p f)(z) = f(pz)`. This is the
  analytic half; it goes through the Petersson product and the
  Atkin–Lehner involutions `W_Q`, and has no elementary substitute on a
  coefficient-only pin.
* (newform decomposition; D–S Thm 5.8.2 with Prop. 5.8.5) `S₂(Γ₀(M))` is
  the direct sum, over divisors `M' ∣ M` and newforms `f` of level `M'`,
  of the blocks `span{V_d f : d ∣ M/M'}`; each block is stable under
  every `T_q` with `q ∤ M` and that operator acts on it by the SCALAR
  `a_q(f)` (because `V_d` commutes with `T_q` for `q ∤ d`, and `d ∣ M`).
  The old subspace is exactly the sum of the blocks with `M' ≠ M`. So a
  nonzero joint good-prime eigenvector lying in it has a nonzero
  component in some block with `M' ≠ M`, and comparing eigenvalues gives
  `a_q(f) = c q` for every `q ∤ M`; a newform of level `M'` is in
  particular a normalized weight-2 eigenform (Prop. 5.8.5), i.e. an
  inhabitant of `IsWeightTwoEigenform M'`.

WHAT THE PIN LACKED, and what has since been BUILT (updated 2026-07-26).
The 2026-07-26 audit against mathlib `Mathlib/NumberTheory/ModularForms/`
and against `~/cs/FLT` — BOTH of which have zero newform, oldform or
Atkin–Lehner material — named four missing items: the degeneracy operator
`V_d`, the oldform subspace, the Petersson product, and the involutions
`W_Q`.

The first two are now DONE and sorry-free. `degeneracyOp` above is
`V_d : S₂(Γ₀(N)) → S₂(Γ₀(M))`, `f ↦ (z ↦ f(dz))` — the weight-2 slash by
`[[d,0],[0,1]]`, renormalized by `d⁻¹` — together with its coefficient
identity `a_n(V_d f) = a_{n/d}(f)`, `0` when `d ∤ n`
(`qCoeff_degeneracyOp`); and the old subspace is then simply
`⨆ p ∈ M.primeFactors, range (degeneracyOp (M/p) M p)`, which is what the
two leaves below are stated over. It cost no new analysis: `heckeRepInf d`
already IS the matrix `[[d,0],[0,1]]`, and this file's existing
`smul`/`slash`/`σ` lemmas for it are stated at arbitrary POSITIVE `d`
rather than at a prime, so they applied verbatim.

SUPERSEDED 2026-07-27, and the superseded sentence is recorded because it
was harvested: this paragraph used to end "what remains genuinely missing
is therefore only the Petersson product and the involutions `W_Q`".  All
FOUR items are now present and none of them is missing.  The Petersson
product is `exists_peterssonProduct_selfAdjoint_heckeOp` (~32056, PROVEN
over `exists_peterssonDomain`, itself PROVEN 2026-07-27), and `W_Q` is
`atkinLehnerOp` (~39586, PROVEN over `exists_atkinLehnerOp`).  The analytic
consumer `mem_oldSubspace_of_qCoeff_coprime_eq_zero` is itself PROVEN, over
`exists_oldSubspace_complement_vanishing`.  The residual open leaves in this
whole cluster are `setIntegral_heckeRep_unfold` (~31782, the coset tiling of
the Hecke integral) and, on the Atkin–Lehner side,
`heckeTransform_slash_atkinLehnerRep` (~39675),
`heckeOp_self_atkinLehnerOp_eigen_of_newform` (~39756) and
`qCoeff_one_atkinLehnerOp_of_newform` (~39834) — a materially different and
much shorter list than "the Petersson product and `W_Q`".  The algebraic side
(`exists_weightTwoEigenform_of_mem_oldSubspace`) needs no analysis at all
beyond what is now present: injectivity of `V_d` and its commutation with
`T_q` at `q ∤ d` both follow from `qCoeff_degeneracyOp` against
`qCoeff_heckeOp` by pure coefficient computation.

FAITHFULNESS AUDIT (2026-07-26). Every hypothesis is load-bearing.

* `hw : w ≠ 0` — for `w = 0` the conclusion is outright FALSE at `M = 1`
  (no `M' ∣ 1` has `M' ≠ 1`), and at any `M` it asserts an eigenform
  matching an unconstrained `c`.
* the vanishing hypothesis `hwc` — without it, `w = g` for a level-`M`
  newform `g` is a counterexample: it is a good-prime eigenvector at its
  own eigensystem, and `eigensystem_minimal` says outright that no
  proper divisor level realizes that eigensystem.
* the eigenvector hypothesis `hwe` — without it `w` may be an arbitrary
  element of the old subspace, and `c` is then unconstrained by the
  hypotheses while the conclusion constrains it.

NON-VACUITY. The hypotheses are jointly satisfiable, so this is not a
leaf that can be discharged by refuting its premises. Take `f` a newform
of level `M'`, `q ∤ M'` prime, `M = M'·q³`, and
`w(z) = f(qz) − a_q(f)·f(q²z) + q·f(q³z)` — the image under `V_q` of the
`q`-depleted form of `f`. Then `w ≠ 0`; every `T_r` with `r ∤ M` acts on
the whole block `span{f(qⁱz) : i ≤ 3}` by the scalar `a_r(f)`, so `w` is
a good-prime eigenvector at `c r = a_r(f)`; and the coefficients of `w`
are supported on multiples of `q`, hence vanish at every index coprime
to `M`. The conclusion is witnessed by `M' ∣ M`, `M' ≠ M` and `f`
itself. -/
theorem exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero
    {M : ℕ} (hM : 0 < M) {c : ℕ → ℂ} {w : CuspForm (Gamma0GL M) 2}
    (hw : w ≠ 0)
    (hwe : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q w = c q • w)
    (hwc : ∀ n : ℕ, Nat.Coprime n M → qCoeff M w n = 0) :
    ∃ M' : ℕ, M' ∣ M ∧ M' ≠ M ∧ ∃ g' : CuspForm (Gamma0GL M') 2,
      IsWeightTwoEigenform M' g' ∧
        ∀ q : ℕ, q.Prime → ¬ q ∣ M → qCoeff M' g' q = c q :=
  exists_weightTwoEigenform_of_mem_oldSubspace hM hw hwe
    (mem_oldSubspace_of_qCoeff_coprime_eq_zero hM hwc)

/-- **STRONG MULTIPLICITY ONE for the AWAY-FROM-`M` eigensystem of a
newform** (PROVEN 2026-07-26 over the single Atkin–Lehner leaf
`exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`;
itself cut 2026-07-26 out of
`heckeOp_apply_eq_smul_of_generalizedEigen_of_newform`; Atkin–Lehner
1970, Diamond–Shurman Theorem 5.8.3 with §5.8): if `g` is a weight-2
level-`M` NEWFORM and `v ∈ S₂(Γ₀(M))` is an honest eigenvector of every
GOOD Hecke operator `T_q`, `q ∤ M`, with `g`'s eigenvalue `a_q(g)`, then
`v ∈ ℂ·g`. Note the hypothesis says NOTHING at the bad primes `q ∣ M`:
that is the whole point, and it is why this is *strong* multiplicity one
rather than the elementary `eq_qCoeff_one_smul_of_heckeOp_eigen` above
(which needs the full prime eigensystem and is PROVEN).

This is the ATKIN–LEHNER half of the two-leaf cut of the reducedness
node. It knows nothing about generalized eigenvectors or nilpotents.

CLASSICAL PROOF. The Atkin–Lehner decomposition
`S₂(Γ₀(M)) = ⨁_{M'∣M} ⨁_{f new of level M'} ⨁_{d ∣ M/M'} ℂ·f(dz)`
is stable under every `T_q` with `q ∤ M`, which acts on the block of `f`
by the SCALAR `a_q(f)`. So a joint eigenvector for the good operators at
`{a_q(g)}` lies in the sum of the blocks with `a_q(f) = a_q(g)` for all
`q ∤ M`. At a proper divisor level `M' ≠ M` such an `f` is a normalized
weight-2 eigenform of level `M' ∣ M` realizing `g`'s away-from-`M`
eigensystem, which `hg.eigensystem_minimal` forbids outright; at
`M' = M`, `d ∣ M/M' = 1` and the block is the LINE `ℂ·f`, and two
newforms of level `M` agreeing at all `q ∤ M` are equal, so `f = g`.

FAITHFULNESS AUDIT (2026-07-26). `hg`'s minimality is LOAD-BEARING:
weakening `IsWeightTwoNewform` to `IsWeightTwoEigenform` makes this
FALSE. Explicit counterexample: `f` a newform of level `M'`, `q ∤ M'`
prime, `M = M'·q³`, and `g = f(z) − a_q(f)·f(qz) + q·f(q²z)` the
`q`-depleted form — a normalized weight-2 eigenform of level `M` with
`a_q(g) = 0`. Every `T_r` with `r ∤ M` acts on the whole 4-dimensional
old block `span{f(qⁱz) : i ≤ 3}` by the scalar `a_r(f) = a_r(g)`, so the
joint good-prime eigenspace at `g`'s eigensystem is 4-dimensional while
`ℂ·g` is a line. `g` is of course not a newform of level `M`: its
away-from-`M` eigensystem is `f`'s, realized at the proper divisor level
`M'`, which is exactly what `eigensystem_minimal` excludes.

ASSEMBLY (2026-07-26 — this node is now PROVEN; the classical residue it
carried has been isolated, and the elementary half of it discharged).
The scalar is `a_1(v)`, as it must be, and the proof is a contradiction
argument on the difference `w = v − a_1(v)·g`:

* `w` is again an honest eigenvector of every GOOD `T_q` at `a_q(g)` —
  `v` is by hypothesis and `g` is at EVERY prime by
  `heckeOp_apply_eq_smul_of_isWeightTwoEigenform`, and the two complex
  scalars commute;
* `w` has NO coefficients away from the level: `a_n(w) = 0` for every
  `n` coprime to `M`. That is the PROVEN
  `qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen_of_coprime` above, which is
  exactly as far as the bare Hecke recursion reaches when the bad primes
  are dropped from the hypothesis;
* so if `w ≠ 0`, the Atkin–Lehner leaf
  `exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero`
  produces a normalized weight-2 eigenform of a PROPER divisor level
  `M' ∣ M` realizing `g`'s away-from-`M` eigensystem — which is verbatim
  what `hg.eigensystem_minimal` forbids. Hence `w = 0`.

So `eigensystem_minimal` is consumed here, in the GLUE, and the leaf
below it knows nothing about newforms: the split is exactly along the
line between the analytic Atkin–Lehner theory (which the pin lacks
entirely) and the minimality bookkeeping (which is pure carrier
arithmetic). -/
theorem exists_smul_of_heckeOp_eq_smul_of_not_dvd_level {M : ℕ} (hM : 0 < M)
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoNewform M g)
    {v : CuspForm (Gamma0GL M) 2}
    (hv : ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeOp M q v = qCoeff M g q • v) :
    ∃ c : ℂ, v = c • g := by
  refine ⟨qCoeff M v 1, sub_eq_zero.mp ?_⟩
  by_contra hne
  -- the difference is again a good-prime eigenvector at `g`'s eigensystem
  have hwe : ∀ q : ℕ, q.Prime → ¬ q ∣ M →
      heckeOp M q (v - qCoeff M v 1 • g) =
        qCoeff M g q • (v - qCoeff M v 1 • g) := by
    intro q hq hqM
    rw [map_sub, map_smul, hv q hq hqM,
      heckeOp_apply_eq_smul_of_isWeightTwoEigenform hM
        hg.toIsWeightTwoEigenform hq,
      smul_sub, smul_comm (qCoeff M g q) (qCoeff M v 1) g]
  -- and it has no coefficients at the indices coprime to the level
  have hwc : ∀ n : ℕ, Nat.Coprime n M →
      qCoeff M (v - qCoeff M v 1 • g) n = 0 := by
    intro n hn
    have h := (qCoeffL M n).map_sub v (qCoeff M v 1 • g)
    simp only [qCoeffL_apply] at h
    rw [h, qCoeff_smul,
      qCoeff_eq_qCoeff_one_mul_of_heckeOp_eigen_of_coprime hM
        hg.toIsWeightTwoEigenform hv n hn, sub_self]
  -- Atkin–Lehner then contradicts the newform's minimality
  obtain ⟨M', hM'dvd, hM'ne, g', hg', hg'c⟩ :=
    exists_weightTwoEigenform_of_heckeOp_eigen_of_qCoeff_coprime_eq_zero
      (c := fun q => qCoeff M g q) hM hne hwe hwc
  exact hg.eigensystem_minimal M' hM'dvd hM'ne g' hg' hg'c

end ComplexHeckeAlgebra

section AtkinLehner
open scoped Matrix ModularForm Pointwise
open Matrix.SpecialLinearGroup CongruenceSubgroup ConjAct

/-- An integral matrix is an **Atkin–Lehner matrix** for the exact
divisor `Q ‖ M` when it has the classical shape `!![Q x, y; M z, Q w]`
and determinant exactly `Q`.

The three divisibility clauses plus `det A = Q` are equivalent to that
shape: `Q ∣ A 0 0` and `Q ∣ A 1 1` give the diagonal, `M ∣ A 1 0` gives
the lower-left, and `A 0 1` is unconstrained.  Stating it this way
avoids existentially quantifying the four auxiliary integers, which
keeps every consumer free of them. -/
structure IsAtkinLehnerMatrix (M Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  /-- `det A = Q`. -/
  det_eq : A.det = (Q : ℤ)
  /-- The upper-left entry is divisible by `Q`. -/
  dvd_zero_zero : (Q : ℤ) ∣ A 0 0
  /-- The lower-left entry is divisible by `M` — this is what makes
  conjugation preserve `Γ₀(M)`. -/
  dvd_one_zero : (M : ℤ) ∣ A 1 0
  /-- The lower-right entry is divisible by `Q`. -/
  dvd_one_one : (Q : ℤ) ∣ A 1 1

/-- **Atkin–Lehner matrices exist at every exact divisor `Q ‖ M`**
(PROVEN): with `u·Q + v·(M/Q) = 1` from Bézout — available exactly
because `Q` and `M/Q` are coprime, which is what `Q ‖ M` means — the
matrix `!![Q, −v; M, Q u]` has determinant
`Q²u + Mv = Q·(uQ + v(M/Q)) = Q` and the three divisibilities on the
nose.

This lemma is what makes `exists_atkinLehnerOp` below NON-VACUOUS:
that leaf characterizes `W_Q` by its action for every Atkin–Lehner
matrix, and a characterization quantified over an empty set would pin
nothing at all. -/
theorem exists_isAtkinLehnerMatrix {M Q : ℕ} (hQ : Q ∣ M)
    (hcop : Nat.Coprime Q (M / Q)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ, IsAtkinLehnerMatrix M Q A := by
  obtain ⟨u, v, huv⟩ : IsCoprime (Q : ℤ) ((M / Q : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hMQ : (Q : ℤ) * ((M / Q : ℕ) : ℤ) = (M : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.mul_div_cancel' hQ)
  refine ⟨!![(Q : ℤ), -v; (M : ℤ), (Q : ℤ) * u], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    have hexp : (Q : ℤ) * ((Q : ℤ) * u) - -v * (M : ℤ)
        = (Q : ℤ) * (u * (Q : ℤ) + v * ((M / Q : ℕ) : ℤ)) := by
      rw [← hMQ]; ring
    rw [hexp, huv, mul_one]
  · simp
  · simp
  · simp

/-- The Atkin–Lehner matrix as an element of `GL₂(ℝ)` (junk value `1`
when the determinant vanishes, which never happens for an actual
Atkin–Lehner matrix, whose determinant is the positive integer `Q`). -/
noncomputable def atkinLehnerRep (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h
  else 1

/-- The underlying real matrix of `atkinLehnerRep A` is `A` itself
(PROVEN).  Needed by any successor proving `exists_atkinLehnerOp`, since
every step there is a matrix identity. -/
theorem atkinLehnerRep_coe {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0) :
    ((atkinLehnerRep A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = A.map (Int.cast : ℤ → ℝ) := by
  rw [atkinLehnerRep, dif_pos h]
  rfl

/-- `Γ₀(M)`-membership as an integral divisibility of the lower-left
entry (PROVEN). -/
theorem Gamma0_mem_iff_intDvd {M : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma0 M ↔ (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- **The single integral lemma behind the whole Atkin–Lehner section**
(PROVEN): an integral `2 × 2` matrix with all entries divisible by `Q`,
lower-left entry divisible by `Q·M`, and determinant `Q²`, is `Q` times
an element of `Γ₀(M)`. -/
theorem exists_gamma0_of_smul_atkinLehner {M Q : ℕ} (hQ0 : (Q : ℤ) ≠ 0)
    {C : Matrix (Fin 2) (Fin 2) ℤ} (hdet : C.det = (Q : ℤ) ^ 2)
    (h00 : (Q : ℤ) ∣ C 0 0) (h01 : (Q : ℤ) ∣ C 0 1)
    (h10 : ((Q : ℤ) * (M : ℤ)) ∣ C 1 0) (h11 : (Q : ℤ) ∣ C 1 1) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      C = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨a, ha⟩ := h00
  obtain ⟨b, hb⟩ := h01
  obtain ⟨c, hc⟩ := h10
  obtain ⟨d, hd⟩ := h11
  have hCD : C = (Q : ℤ) • (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hd, hc, mul_assoc]
  have hdetD : (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have h1 : ((Q : ℤ) • (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ)).det
        = (Q : ℤ) ^ 2 * (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [Matrix.det_smul]
      norm_num
    have hkey : (Q : ℤ) ^ 2 * (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det
        = (Q : ℤ) ^ 2 * 1 := by
      rw [← h1, ← hCD, hdet, mul_one]
    exact mul_left_cancel₀ (pow_ne_zero _ hQ0) hkey
  refine ⟨⟨_, hdetD⟩, ?_, hCD⟩
  rw [Gamma0_mem_iff_intDvd]
  exact ⟨c, by simp⟩

/-- The four entries of a `2 × 2` adjugate (PROVEN). -/
theorem adjugate_fin_two_entries (A : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix.adjugate A 0 0 = A 1 1 ∧ Matrix.adjugate A 0 1 = -A 0 1 ∧
      Matrix.adjugate A 1 0 = -A 1 0 ∧ Matrix.adjugate A 1 1 = A 0 0 := by
  rw [Matrix.adjugate_fin_two A]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- The four entries of a `2 × 2` integral matrix product (PROVEN). -/
theorem matrix_fin_two_mul_entries (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
    (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `det (adj A) = det A` in dimension two (PROVEN). -/
theorem det_adjugate_of_det_eq {A : Matrix (Fin 2) (Fin 2) ℤ} {Q : ℕ}
    (hA : A.det = (Q : ℤ)) : (Matrix.adjugate A).det = (Q : ℤ) := by
  rw [Matrix.det_adjugate, hA]
  norm_num

/-- The Atkin–Lehner matrices are stable under RIGHT multiplication by
`Γ₀(M)` (PROVEN). -/
theorem IsAtkinLehnerMatrix.mul_gamma0 {M Q : ℕ} (hQM : (Q : ℤ) ∣ (M : ℤ))
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    IsAtkinLehnerMatrix M Q (A * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hg10 : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := Gamma0_mem_iff_intDvd.mp hγ
  obtain ⟨m00, m01, m10, m11⟩ := matrix_fin_two_mul_entries A (γ : Matrix (Fin 2) (Fin 2) ℤ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hA.det_eq, γ.2, mul_one]
  · rw [m00]
    exact dvd_add (hA.dvd_zero_zero.mul_right _) ((hQM.trans hg10).mul_left _)
  · rw [m10]
    exact dvd_add (hA.dvd_one_zero.mul_right _) (hg10.mul_left _)
  · rw [m11]
    exact dvd_add ((hQM.trans hA.dvd_one_zero).mul_right _) (hA.dvd_one_one.mul_right _)

/-- The Atkin–Lehner matrices are stable under LEFT multiplication by
`Γ₀(M)` (PROVEN). -/
theorem IsAtkinLehnerMatrix.gamma0_mul {M Q : ℕ} (hQM : (Q : ℤ) ∣ (M : ℤ))
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    IsAtkinLehnerMatrix M Q ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A) := by
  have hg10 : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := Gamma0_mem_iff_intDvd.mp hγ
  obtain ⟨m00, m01, m10, m11⟩ := matrix_fin_two_mul_entries (γ : Matrix (Fin 2) (Fin 2) ℤ) A
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hA.det_eq, γ.2, one_mul]
  · rw [m00]
    exact dvd_add (hA.dvd_zero_zero.mul_left _) ((hQM.trans hA.dvd_one_zero).mul_left _)
  · rw [m10]
    exact dvd_add (hg10.mul_right _) (hA.dvd_one_zero.mul_left _)
  · rw [m11]
    exact dvd_add ((hQM.trans hg10).mul_right _) (hA.dvd_one_one.mul_left _)

/-- **The Atkin–Lehner matrices form ONE left `Γ₀(M)`-coset** (PROVEN):
any two of them for the same `(M, Q)` differ by a left factor in
`Γ₀(M)`. This is what makes the operator independent of the choice. -/
theorem atkinLehner_exists_gamma0_left {M Q : ℕ} (hQ0 : (Q : ℤ) ≠ 0)
    (hQM : (Q : ℤ) ∣ (M : ℤ))
    {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A)
    (hB : IsAtkinLehnerMatrix M Q B) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      B = (γ : Matrix (Fin 2) (Fin 2) ℤ) * A := by
  obtain ⟨a00, a01, a10, a11⟩ := adjugate_fin_two_entries A
  obtain ⟨e00, e01, e10, e11⟩ := matrix_fin_two_mul_entries B (Matrix.adjugate A)
  rw [a00, a10] at e00
  rw [a01, a11] at e01
  rw [a00, a10] at e10
  rw [a01, a11] at e11
  have hdet : (B * Matrix.adjugate A).det = (Q : ℤ) ^ 2 := by
    rw [Matrix.det_mul, det_adjugate_of_det_eq hA.det_eq, hB.det_eq, sq]
  have h00 : (Q : ℤ) ∣ (B * Matrix.adjugate A) 0 0 := by
    rw [e00]
    exact dvd_add (hA.dvd_one_one.mul_left _)
      (((hQM.trans hA.dvd_one_zero).neg_right).mul_left _)
  have h01 : (Q : ℤ) ∣ (B * Matrix.adjugate A) 0 1 := by
    rw [e01]
    exact dvd_add (hB.dvd_zero_zero.mul_right _) (hA.dvd_zero_zero.mul_left _)
  have h10 : ((Q : ℤ) * (M : ℤ)) ∣ (B * Matrix.adjugate A) 1 0 := by
    rw [e10]
    refine dvd_add ?_ ?_
    · rw [mul_comm (Q : ℤ)]
      exact mul_dvd_mul hB.dvd_one_zero hA.dvd_one_one
    · exact mul_dvd_mul hB.dvd_one_one hA.dvd_one_zero.neg_right
  have h11 : (Q : ℤ) ∣ (B * Matrix.adjugate A) 1 1 := by
    rw [e11]
    exact dvd_add ((hQM.trans hB.dvd_one_zero).mul_right _) (hA.dvd_zero_zero.mul_left _)
  obtain ⟨γ, hγ, hCγ⟩ := exists_gamma0_of_smul_atkinLehner (M := M) hQ0 hdet h00 h01 h10 h11
  refine ⟨γ, hγ, ?_⟩
  have hmul : (B * Matrix.adjugate A) * A
      = (Q : ℤ) • ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A) := by
    rw [hCγ, Matrix.smul_mul]
  have hCA : (B * Matrix.adjugate A) * A = (Q : ℤ) • B := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, hA.det_eq, Matrix.mul_smul, Matrix.mul_one]
  rw [hCA] at hmul
  exact smul_right_injective _ hQ0 hmul

/-- **The Atkin–Lehner matrices form ONE right `Γ₀(M)`-coset** (PROVEN).
Together with `atkinLehner_exists_gamma0_left` this gives BOTH
inclusions of `A Γ₀(M) A⁻¹ = Γ₀(M)`. -/
theorem atkinLehner_exists_gamma0_right {M Q : ℕ} (hQ0 : (Q : ℤ) ≠ 0)
    (hQM : (Q : ℤ) ∣ (M : ℤ))
    {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A)
    (hB : IsAtkinLehnerMatrix M Q B) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      B = A * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨a00, a01, a10, a11⟩ := adjugate_fin_two_entries A
  obtain ⟨e00, e01, e10, e11⟩ := matrix_fin_two_mul_entries (Matrix.adjugate A) B
  rw [a00, a01] at e00
  rw [a00, a01] at e01
  rw [a10, a11] at e10
  rw [a10, a11] at e11
  have hdet : (Matrix.adjugate A * B).det = (Q : ℤ) ^ 2 := by
    rw [Matrix.det_mul, det_adjugate_of_det_eq hA.det_eq, hB.det_eq, sq]
  have h00 : (Q : ℤ) ∣ (Matrix.adjugate A * B) 0 0 := by
    rw [e00]
    exact dvd_add (hA.dvd_one_one.mul_right _) ((hQM.trans hB.dvd_one_zero).mul_left _)
  have h01 : (Q : ℤ) ∣ (Matrix.adjugate A * B) 0 1 := by
    rw [e01]
    exact dvd_add (hA.dvd_one_one.mul_right _) (hB.dvd_one_one.mul_left _)
  have h10 : ((Q : ℤ) * (M : ℤ)) ∣ (Matrix.adjugate A * B) 1 0 := by
    rw [e10]
    refine dvd_add ?_ ?_
    · rw [mul_comm (Q : ℤ)]
      exact mul_dvd_mul hA.dvd_one_zero.neg_right hB.dvd_zero_zero
    · exact mul_dvd_mul hA.dvd_zero_zero hB.dvd_one_zero
  have h11 : (Q : ℤ) ∣ (Matrix.adjugate A * B) 1 1 := by
    rw [e11]
    exact dvd_add ((hQM.trans hA.dvd_one_zero).neg_right.mul_right _)
      (hA.dvd_zero_zero.mul_right _)
  obtain ⟨γ, hγ, hCγ⟩ := exists_gamma0_of_smul_atkinLehner (M := M) hQ0 hdet h00 h01 h10 h11
  refine ⟨γ, hγ, ?_⟩
  have hmul : A * (Matrix.adjugate A * B)
      = (Q : ℤ) • (A * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rw [hCγ, Matrix.mul_smul]
  have hCA : A * (Matrix.adjugate A * B) = (Q : ℤ) • B := by
    rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hA.det_eq, Matrix.smul_mul, Matrix.one_mul]
  rw [hCA] at hmul
  exact smul_right_injective _ hQ0 hmul

/-- **`A² = Q·γ₀` with `γ₀ ∈ Γ₀(M)`** (PROVEN) — the integral half of
the involutivity. -/
theorem atkinLehner_exists_gamma0_sq {M Q : ℕ} (hQ0 : (Q : ℤ) ≠ 0)
    (hQM : (Q : ℤ) ∣ (M : ℤ))
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      A * A = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨e00, e01, e10, e11⟩ := matrix_fin_two_mul_entries A A
  have hdet : (A * A).det = (Q : ℤ) ^ 2 := by
    rw [Matrix.det_mul, hA.det_eq, sq]
  have h00 : (Q : ℤ) ∣ (A * A) 0 0 := by
    rw [e00]
    exact dvd_add (hA.dvd_zero_zero.mul_right _) ((hQM.trans hA.dvd_one_zero).mul_left _)
  have h01 : (Q : ℤ) ∣ (A * A) 0 1 := by
    rw [e01]
    exact dvd_add (hA.dvd_zero_zero.mul_right _) (hA.dvd_one_one.mul_left _)
  have h10 : ((Q : ℤ) * (M : ℤ)) ∣ (A * A) 1 0 := by
    rw [e10]
    refine dvd_add ?_ ?_
    · rw [mul_comm (Q : ℤ)]
      exact mul_dvd_mul hA.dvd_one_zero hA.dvd_zero_zero
    · exact mul_dvd_mul hA.dvd_one_one hA.dvd_one_zero
  have h11 : (Q : ℤ) ∣ (A * A) 1 1 := by
    rw [e11]
    exact dvd_add ((hQM.trans hA.dvd_one_zero).mul_right _) (hA.dvd_one_one.mul_right _)
  exact exists_gamma0_of_smul_atkinLehner (M := M) hQ0 hdet h00 h01 h10 h11

/-- Casting an integral matrix product to `ℝ` (PROVEN). -/
theorem intMatrix_map_cast_mul (X Y : Matrix (Fin 2) (Fin 2) ℤ) :
    (X * Y).map (Int.cast : ℤ → ℝ)
      = X.map (Int.cast : ℤ → ℝ) * Y.map (Int.cast : ℤ → ℝ) := by
  simpa using Matrix.map_mul (L := X) (M := Y) (f := Int.castRingHom ℝ)

/-- Casting an integral scalar multiple to `ℝ` (PROVEN). -/
theorem intMatrix_map_cast_smul (q : ℤ) (X : Matrix (Fin 2) (Fin 2) ℤ) :
    (q • X).map (Int.cast : ℤ → ℝ) = (q : ℝ) • X.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

/-- The real matrix of `mapGL ℝ γ` for `γ ∈ SL(2, ℤ)` (PROVEN). -/
theorem mapGL_coe_matrix_int (γ : SL(2, ℤ)) :
    ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := by
  rw [mapGL_coe_matrix]
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

/-- The real determinant of an Atkin–Lehner matrix is `Q` (PROVEN). -/
theorem det_map_cast_of_isAtkinLehnerMatrix {M Q : ℕ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M Q A) :
    (A.map (Int.cast : ℤ → ℝ)).det = (Q : ℝ) := by
  have h := RingHom.map_det (Int.castRingHom ℝ) A
  rw [hA.det_eq] at h
  simpa [RingHom.mapMatrix_apply] using h.symm

/-- ... and in particular nonzero, so `atkinLehnerRep` is not junk
(PROVEN). -/
theorem det_map_cast_ne_zero_isAL {M Q : ℕ} (hQ0 : (Q : ℝ) ≠ 0)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A) :
    (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  rw [det_map_cast_of_isAtkinLehnerMatrix hA]; exact hQ0

/-- Transfer of a LEFT `Γ₀(M)`-factorization to `GL₂(ℝ)` (PROVEN). -/
theorem atkinLehnerRep_of_gamma0_mul {M Q : ℕ} (hQ0 : (Q : ℝ) ≠ 0)
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M Q A) (hB : IsAtkinLehnerMatrix M Q B)
    {γ : SL(2, ℤ)} (hBA : B = (γ : Matrix (Fin 2) (Fin 2) ℤ) * A) :
    atkinLehnerRep B = mapGL ℝ γ * atkinLehnerRep A := by
  apply Units.ext
  rw [Units.val_mul, atkinLehnerRep_coe (det_map_cast_ne_zero_isAL hQ0 hB),
    atkinLehnerRep_coe (det_map_cast_ne_zero_isAL hQ0 hA), mapGL_coe_matrix_int, hBA,
    intMatrix_map_cast_mul]

/-- Transfer of a RIGHT `Γ₀(M)`-factorization to `GL₂(ℝ)` (PROVEN). -/
theorem atkinLehnerRep_of_mul_gamma0 {M Q : ℕ} (hQ0 : (Q : ℝ) ≠ 0)
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M Q A) (hB : IsAtkinLehnerMatrix M Q B)
    {γ : SL(2, ℤ)} (hBA : B = A * (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    atkinLehnerRep B = atkinLehnerRep A * mapGL ℝ γ := by
  apply Units.ext
  rw [Units.val_mul, atkinLehnerRep_coe (det_map_cast_ne_zero_isAL hQ0 hB),
    atkinLehnerRep_coe (det_map_cast_ne_zero_isAL hQ0 hA), mapGL_coe_matrix_int, hBA,
    intMatrix_map_cast_mul]

/-- Transfer of `A² = Q·γ₀` to `GL₂(ℝ)` (PROVEN): the square of the
Atkin–Lehner element is the SCALAR `Q` times an element of `Γ₀(M)`. -/
theorem atkinLehnerRep_mul_self {M Q : ℕ} (hQ0 : (Q : ℝ) ≠ 0)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A) {γ : SL(2, ℤ)}
    (hsq : A * A = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    atkinLehnerRep A * atkinLehnerRep A
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Q : ℝ) hQ0) * mapGL ℝ γ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, atkinLehnerRep_coe (det_map_cast_ne_zero_isAL hQ0 hA),
    mapGL_coe_matrix_int, ← intMatrix_map_cast_mul, hsq, intMatrix_map_cast_smul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  rw [Matrix.diagonal_mul]
  simp

/-- **Slash by a positive SCALAR matrix is trivial at weight two**
(PROVEN): `|det|^{k−1}·denom^{−k} = u²·u^{−2} = 1` at `k = 2`, and
`σ` is the identity since the determinant `u²` is positive. This is
exactly why the weight-two Atkin–Lehner slash needs no renormalization
and why `A² = Q·γ₀` gives an involution. -/
theorem weightTwo_slash_scalar (u : ℝˣ) (f : UpperHalfPlane → ℂ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by
  have hune : (u : ℝ) ≠ 0 := u.ne_zero
  have hdetv : (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u)).val = (u : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp
  have hpos : (0 : ℝ) < (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u)).val := by
    rw [hdetv]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hune))
  have hc : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hune
  funext τ
  rw [ModularForm.slash_apply, UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [UpperHalfPlane.σ]
  rw [if_pos hpos, hdetv, abs_of_nonneg (sq_nonneg _)]
  push_cast
  field_simp
  rfl

/-- The `σ` twist is trivial for an Atkin–Lehner matrix, whose
determinant `Q` is positive (PROVEN) — so no complex conjugation
enters the weight-two slash. -/
theorem sigma_atkinLehnerRep {M Q : ℕ} (hQpos : (0 : ℝ) < (Q : ℝ))
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M Q A) (z : ℂ) :
    UpperHalfPlane.σ (atkinLehnerRep A) z = z := by
  have hne : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 :=
    det_map_cast_ne_zero_isAL (ne_of_gt hQpos) hA
  have hdetv : (Matrix.GeneralLinearGroup.det (atkinLehnerRep A)).val = (Q : ℝ) := by
    show ((atkinLehnerRep A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = (Q : ℝ)
    rw [atkinLehnerRep_coe hne, det_map_cast_of_isAtkinLehnerMatrix hA]
  simp only [UpperHalfPlane.σ]
  rw [if_pos (by rw [hdetv]; exact hQpos)]
  rfl

/-- **AN ATKIN–LEHNER MATRIX NORMALIZES `Γ₀(M)`** (PROVEN): the
`ConjAct`-conjugate group is `Γ₀(M)` itself, which is component 1 of
the operator leaf and is what lets `CuspForm.translate` be transported
back to level `M` with no `CuspForm.trace` over a coset enumeration —
unlike the Hecke case. Both inclusions come from the coset lemmas: `A γ`
is again an Atkin–Lehner matrix, hence `= γ' A`; and `γ A` is one too,
hence `= A γ'`. -/
theorem atkinLehnerRep_conj_Gamma0GL {M Q : ℕ} (hQ0 : (Q : ℝ) ≠ 0) (hQ0' : (Q : ℤ) ≠ 0)
    (hQM : (Q : ℤ) ∣ (M : ℤ)) {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M Q A) :
    toConjAct (atkinLehnerRep A)⁻¹ • Gamma0GL M = Gamma0GL M := by
  ext x
  rw [mem_conjAct_inv_smul_iff]
  constructor
  · intro h
    obtain ⟨δ, hδ, hδeq⟩ := mem_Gamma0GL_iff.mp h
    have hδA : IsAtkinLehnerMatrix M Q ((δ : Matrix (Fin 2) (Fin 2) ℤ) * A) :=
      hA.gamma0_mul hQM hδ
    obtain ⟨γ', hγ', hEq⟩ := atkinLehner_exists_gamma0_right hQ0' hQM hA hδA
    have h1 := atkinLehnerRep_of_gamma0_mul hQ0 hA hδA (γ := δ) rfl
    have h2 := atkinLehnerRep_of_mul_gamma0 hQ0 hA hδA hEq
    have h3 : mapGL ℝ δ * atkinLehnerRep A = atkinLehnerRep A * mapGL ℝ γ' := by
      rw [← h1, h2]
    refine mem_Gamma0GL_iff.mpr ⟨γ', hγ', ?_⟩
    have hxe : x = (atkinLehnerRep A)⁻¹ * (mapGL ℝ δ) * atkinLehnerRep A := by
      rw [hδeq]; group
    rw [hxe, mul_assoc, h3, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro h
    obtain ⟨γ, hγ, hγeq⟩ := mem_Gamma0GL_iff.mp h
    have hAγ : IsAtkinLehnerMatrix M Q (A * (γ : Matrix (Fin 2) (Fin 2) ℤ)) :=
      hA.mul_gamma0 hQM hγ
    obtain ⟨γ', hγ', hEq⟩ := atkinLehner_exists_gamma0_left hQ0' hQM hA hAγ
    have h1 := atkinLehnerRep_of_mul_gamma0 hQ0 hA hAγ (γ := γ) rfl
    have h2 := atkinLehnerRep_of_gamma0_mul hQ0 hA hAγ hEq
    have h3 : atkinLehnerRep A * mapGL ℝ γ = mapGL ℝ γ' * atkinLehnerRep A := by
      rw [← h1, h2]
    refine mem_Gamma0GL_iff.mpr ⟨γ', hγ', ?_⟩
    rw [← hγeq, h3, mul_assoc, mul_inv_cancel, mul_one]

/-- **THE ATKIN–LEHNER OPERATOR `W_Q`** (PROVEN 2026-07-27; it was the
sorry node of the TWELFTH decomposition 2026-07-26): at an exact
divisor `Q ‖ M` there is a
`ℂ`-linear endomorphism of `S₂(Γ₀(M))` which acts as the weight-two
slash by EVERY Atkin–Lehner matrix for `(M, Q)`, and which squares to
the identity.

This is the leaf that pins `W_Q`, and it mentions no cusp form's
coefficients and no eigenvalue — that is the whole point of it.  Its
three components, with the explicit integral-matrix computations
discharging each, are recorded in the section docstring above:
normalization of `Γ₀(M)` by an Atkin–Lehner matrix, independence of the
choice of matrix (they form one `Γ₀(M)`-coset), and `A² = Q·γ₀` with
`γ₀ ∈ Γ₀(M)` together with the triviality of the scalar `Q·1` at weight
two.

WHY IT IS BUNDLED rather than cut into those three.  The three facts
cannot be stated separately until the operator exists, and the operator
cannot be built without the first of them — so a split here would be
circular.  A successor should prove this one leaf and then, if a finer
API is wanted, DERIVE the three parts from it.

The natural Lean route, given what this file already carries: mathlib's
`CuspForm.translate f (atkinLehnerRep A)` is a cusp form on the
CONJUGATE group `toConjAct (atkinLehnerRep A)⁻¹ • Γ₀(M)`, exactly as in
`exists_cuspForm_heckeTransform` above; component 1 says that conjugate
group IS `Γ₀(M)`, so — unlike the Hecke case, which needs
`CuspForm.trace` over a coset enumeration — no trace is required and the
translate can simply be transported along a subgroup equality.  That
makes this materially cheaper than the Hecke stability already proven in
this file.

Missing from the pin: `Mathlib.NumberTheory.ModularForms` has no
`AtkinLehner`, no `newform` and no `U_q`; `SlashActions.lean` plus the
`CuspForm.translate` API is the whole starting point, and `~/cs/FLT` has
nothing transferable (only the definite quaternionic inner product).

HOW IT IS PROVEN (2026-07-27), for the record. `W` is the transport of
`CuspForm.translate f (atkinLehnerRep A₀)` along
`atkinLehnerRep_conj_Gamma0GL` for ONE choice `A₀` (which exists by
`exists_isAtkinLehnerMatrix`, so nothing here is vacuous); its
underlying function is `⇑f ∣[2] atkinLehnerRep A₀` by construction.
Linearity is `SlashAction.add_slash` and `ModularForm.smul_slash` with
`sigma_atkinLehnerRep` discharging the `σ`-twist. Choice-independence
is `atkinLehner_exists_gamma0_left` plus slash-invariance of `f`.
Involutivity is `atkinLehnerRep_mul_self` plus
`weightTwo_slash_scalar`. No trace, no coset enumeration, no Bézout
beyond the one already in `exists_isAtkinLehnerMatrix`. -/
theorem exists_atkinLehnerOp {M Q : ℕ} (hM : 0 < M) (hQ : Q ∣ M)
    (hcop : Nat.Coprime Q (M / Q)) :
    ∃ W : Module.End ℂ (CuspForm (Gamma0GL M) 2),
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ, IsAtkinLehnerMatrix M Q A →
          ∀ f : CuspForm (Gamma0GL M) 2,
            ⇑(W f) = ⇑f ∣[(2 : ℤ)] atkinLehnerRep A) ∧
        W * W = 1 := by
  have hQpos : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hQ) hM.ne'
    · exact h
  have hQ0R : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQpos.ne'
  have hQ0Rpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
  have hQ0Z : (Q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hQpos.ne'
  have hQMz : (Q : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hQ
  obtain ⟨A₀, hA₀⟩ := exists_isAtkinLehnerMatrix hQ hcop
  have hnorm := atkinLehnerRep_conj_Gamma0GL hQ0R hQ0Z hQMz hA₀
  have htrans : ∀ (Γ Γ' : Subgroup (GL (Fin 2) ℝ)) (h : Γ = Γ') (x : CuspForm Γ 2),
      ⇑(h ▸ x : CuspForm Γ' 2) = ⇑x := by
    rintro Γ Γ' rfl x
    rfl
  set T : CuspForm (Gamma0GL M) 2 → CuspForm (Gamma0GL M) 2 :=
    fun f => hnorm ▸ (CuspForm.translate f (atkinLehnerRep A₀)) with hT
  have hTcoe : ∀ f : CuspForm (Gamma0GL M) 2,
      ⇑(T f) = ⇑f ∣[(2 : ℤ)] atkinLehnerRep A₀ := by
    intro f
    rw [hT]
    exact htrans _ _ hnorm (CuspForm.translate f (atkinLehnerRep A₀))
  have hindep : ∀ A : Matrix (Fin 2) (Fin 2) ℤ, IsAtkinLehnerMatrix M Q A →
      ∀ f : CuspForm (Gamma0GL M) 2,
        ⇑f ∣[(2 : ℤ)] atkinLehnerRep A = ⇑f ∣[(2 : ℤ)] atkinLehnerRep A₀ := by
    intro A hA f
    obtain ⟨γ, hγ, hEq⟩ := atkinLehner_exists_gamma0_left hQ0Z hQMz hA₀ hA
    rw [atkinLehnerRep_of_gamma0_mul hQ0R hA₀ hA hEq, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ γ)
        (mem_Gamma0GL_iff.mpr ⟨γ, hγ, rfl⟩)]
  obtain ⟨γ₀, hγ₀, hsq⟩ := atkinLehner_exists_gamma0_sq hQ0Z hQMz hA₀
  have hinv : ∀ f : CuspForm (Gamma0GL M) 2, T (T f) = f := by
    intro f
    apply DFunLike.coe_injective
    rw [hTcoe, hTcoe, ← SlashAction.slash_mul, atkinLehnerRep_mul_self hQ0R hA₀ hsq,
      SlashAction.slash_mul, weightTwo_slash_scalar,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ γ₀)
        (mem_Gamma0GL_iff.mpr ⟨γ₀, hγ₀, rfl⟩)]
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro f g
    apply DFunLike.coe_injective
    have h2 := hTcoe f
    have h3 := hTcoe g
    rw [hTcoe, CuspForm.coe_add, SlashAction.add_slash, ← h2, ← h3, ← CuspForm.coe_add]
  · intro c f
    apply DFunLike.coe_injective
    have h2 := hTcoe f
    rw [RingHom.id_apply, hTcoe, CuspForm.IsGLPos.coe_smul, ModularForm.smul_slash,
      sigma_atkinLehnerRep hQ0Rpos hA₀, ← h2, ← CuspForm.IsGLPos.coe_smul]
  · intro A hA f
    show ⇑(T f) = _
    rw [hTcoe f]
    exact (hindep A hA f).symm
  · apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply, Module.End.one_apply]
    exact hinv f

/-- The unconditional form of `exists_atkinLehnerOp`, so that `W_Q` can
be DEFINED at every pair `(M, Q)` (junk — the zero endomorphism —
outside the meaningful range `0 < M`, `Q ‖ M`, which is all any
statement below quantifies over).  Same pattern as
`exists_heckeOpLinear_total` for `T_q`. -/
theorem exists_atkinLehnerOp_total (M Q : ℕ) :
    ∃ W : Module.End ℂ (CuspForm (Gamma0GL M) 2),
      0 < M → Q ∣ M → Nat.Coprime Q (M / Q) →
        ((∀ A : Matrix (Fin 2) (Fin 2) ℤ, IsAtkinLehnerMatrix M Q A →
            ∀ f : CuspForm (Gamma0GL M) 2,
              ⇑(W f) = ⇑f ∣[(2 : ℤ)] atkinLehnerRep A) ∧
          W * W = 1) := by
  by_cases h : 0 < M ∧ Q ∣ M ∧ Nat.Coprime Q (M / Q)
  · obtain ⟨W, hW⟩ := exists_atkinLehnerOp h.1 h.2.1 h.2.2
    exact ⟨W, fun _ _ _ => hW⟩
  · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

/-- **The Atkin–Lehner involution `W_Q` on `S₂(Γ₀(M))`** at an exact
divisor `Q ‖ M` — the weight-two slash by an Atkin–Lehner matrix,
bundled as an endomorphism.  Junk outside the meaningful range, which no
statement about it looks at. -/
noncomputable def atkinLehnerOp (M Q : ℕ) : Module.End ℂ (CuspForm (Gamma0GL M) 2) :=
  (exists_atkinLehnerOp_total M Q).choose

/-- `W_Q` acts by the slash by any Atkin–Lehner matrix (PROVEN from the
leaf).  Together with `exists_isAtkinLehnerMatrix` this determines `W_Q`
uniquely, which is what makes
`atkinLehnerOp_apply_eq_neg_qCoeff_smul` below a theorem with content
rather than a restatement. -/
theorem atkinLehnerOp_coe {M Q : ℕ} (hM : 0 < M) (hQ : Q ∣ M)
    (hcop : Nat.Coprime Q (M / Q)) {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M Q A) (f : CuspForm (Gamma0GL M) 2) :
    ⇑(atkinLehnerOp M Q f) = ⇑f ∣[(2 : ℤ)] atkinLehnerRep A :=
  ((exists_atkinLehnerOp_total M Q).choose_spec hM hQ hcop).1 A hA f

/-- The integral degree-`r` coset representative indexed by a point of `ℙ¹(𝔽_r)`:
`some j ↦ !![1, j; 0, r]` and `none ↦ !![r, 0; 0, 1]`. -/
def heckeIndexMat (r : ℕ) : Option (ZMod r) → Matrix (Fin 2) (Fin 2) ℤ
  | some j => !![1, (j.val : ℤ); 0, (r : ℤ)]
  | none => !![(r : ℤ), 0; 0, 1]

theorem heckeIndexMat_det (r : ℕ) (x : Option (ZMod r)) :
    (heckeIndexMat r x).det = (r : ℤ) := by
  cases x <;> simp [heckeIndexMat, Matrix.det_fin_two_of]

/-- The `GL₂(ℝ)` incarnation of `heckeIndexMat`. -/
noncomputable def heckeIndexRep (r : ℕ) : Option (ZMod r) → GL (Fin 2) ℝ
  | some j => heckeRep r j.val
  | none => heckeRepInf r

theorem heckeIndexRep_coe {r : ℕ} (hr0 : (r : ℝ) ≠ 0) (x : Option (ZMod r)) :
    ((heckeIndexRep r x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (heckeIndexMat r x).map (Int.cast : ℤ → ℝ) := by
  cases x with
  | none =>
    show ((heckeRepInf r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [heckeRepInf_coe hr0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeIndexMat]
  | some j =>
    show ((heckeRep r j.val : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [heckeRep_coe hr0]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [heckeIndexMat]

/-- The index set of the weight-two Hecke slash-sum at level `M` and prime `r`. -/
def heckeIndexSet (M r : ℕ) [NeZero r] : Finset (Option (ZMod r)) :=
  if r ∣ M then Finset.univ.image some else Finset.univ

theorem zmodVal_image_univ_eq_range (r : ℕ) [NeZero r] :
    (Finset.univ : Finset (ZMod r)).image ZMod.val = Finset.range r := by
  ext n
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact ZMod.val_lt j
  · intro h
    exact ⟨(n : ZMod r), ZMod.val_natCast_of_lt h⟩

theorem finset_sum_slash {ι : Type*} (s : Finset ι) (F : ι → (UpperHalfPlane → ℂ))
    (γ : GL (Fin 2) ℝ) :
    (∑ i ∈ s, F i) ∣[(2 : ℤ)] γ = ∑ i ∈ s, (F i) ∣[(2 : ℤ)] γ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, SlashAction.add_slash, ih, Finset.sum_insert ha]

theorem heckeTransform_eq_sum_heckeIndexSet (M r : ℕ) [NeZero r] (g : UpperHalfPlane → ℂ) :
    heckeTransform M r g = ∑ x ∈ heckeIndexSet M r, g ∣[(2 : ℤ)] heckeIndexRep r x := by
  classical
  have hre : ∑ j ∈ Finset.range r, g ∣[(2 : ℤ)] heckeRep r j
      = ∑ j : ZMod r, g ∣[(2 : ℤ)] heckeIndexRep r (some j) := by
    rw [← zmodVal_image_univ_eq_range r,
      Finset.sum_image (fun x _ y _ h => ZMod.val_injective r h)]
    rfl
  unfold heckeTransform heckeIndexSet
  split_ifs with h
  · rw [Finset.sum_image (fun x _ y _ h => Option.some_injective _ h), add_zero, hre]
  · rw [Fintype.sum_option, hre]
    show _ = g ∣[(2 : ℤ)] heckeRepInf r + _
    rw [add_comm]

/-- First coordinate of `(row x) · adj Ā` over `𝔽_r`. -/
def atkinLehnerConjU (r : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod r) → ZMod r
  | some j => ((A 1 1 : ℤ) : ZMod r) - j * ((A 1 0 : ℤ) : ZMod r)
  | none => -((A 1 0 : ℤ) : ZMod r)

/-- Second coordinate of `(row x) · adj Ā` over `𝔽_r`. -/
def atkinLehnerConjV (r : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Option (ZMod r) → ZMod r
  | some j => j * ((A 0 0 : ℤ) : ZMod r) - ((A 0 1 : ℤ) : ZMod r)
  | none => ((A 0 0 : ℤ) : ZMod r)

/-- The Möbius action of `Ā⁻¹` on `ℙ¹(𝔽_r)`. -/
noncomputable def atkinLehnerConjIndex (r : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (x : Option (ZMod r)) : Option (ZMod r) :=
  if atkinLehnerConjU r A x = 0 then none
  else some (atkinLehnerConjV r A x * (atkinLehnerConjU r A x)⁻¹)

theorem atkinLehner_det_cast {M q r : ℕ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsAtkinLehnerMatrix M q A) :
    ((A 0 0 : ℤ) : ZMod r) * ((A 1 1 : ℤ) : ZMod r)
      - ((A 0 1 : ℤ) : ZMod r) * ((A 1 0 : ℤ) : ZMod r) = ((q : ℕ) : ZMod r) := by
  have h : A 0 0 * A 1 1 - A 0 1 * A 1 0 = (q : ℤ) := by
    rw [← Matrix.det_fin_two A]; exact hA.det_eq
  have h2 := congrArg (fun z : ℤ => (z : ZMod r)) h
  push_cast at h2
  exact h2

theorem atkinLehnerConjIndex_injective {M q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r ≠ q)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A) :
    Function.Injective (atkinLehnerConjIndex r A) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : ((q : ℕ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
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

theorem atkinLehnerConjU_none_eq_zero {M q r : ℕ} (hrM : r ∣ M)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A) :
    atkinLehnerConjU r A none = 0 := by
  have hc : ((A 1 0 : ℤ) : ZMod r) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (Int.natCast_dvd_natCast.mpr hrM).trans hA.dvd_one_zero
  simp [atkinLehnerConjU, hc]

theorem atkinLehnerConjIndex_none {M q r : ℕ} (hrM : r ∣ M)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A) :
    atkinLehnerConjIndex r A none = none := by
  rw [atkinLehnerConjIndex, if_pos (atkinLehnerConjU_none_eq_zero hrM hA)]

theorem atkinLehnerConjIndex_some_ne_none {M q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r ≠ q)
    (hrM : r ∣ M) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    (j : ZMod r) : atkinLehnerConjIndex r A (some j) ≠ none := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hq0 : ((q : ℕ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
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

theorem exists_intMatrix_of_smul_dvd_det {M : ℕ} {Q D : ℤ} (hQ0 : Q ≠ 0)
    {C : Matrix (Fin 2) (Fin 2) ℤ} (hdet : C.det = Q ^ 2 * D)
    (h00 : Q ∣ C 0 0) (h01 : Q ∣ C 0 1) (h10 : (Q * (M : ℤ)) ∣ C 1 0) (h11 : Q ∣ C 1 1) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ, C = Q • B ∧ B.det = D ∧ (M : ℤ) ∣ B 1 0 := by
  obtain ⟨a, ha⟩ := h00
  obtain ⟨b, hb⟩ := h01
  obtain ⟨c, hc⟩ := h10
  obtain ⟨d, hd⟩ := h11
  refine ⟨!![a, b; (M : ℤ) * c, d], ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hd, hc, mul_assoc]
  · have h1 : (Q • (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ)).det
        = Q ^ 2 * (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [Matrix.det_smul]; norm_num
    have hCD : C = Q • (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hd, hc, mul_assoc]
    have hkey : Q ^ 2 * (!![a, b; (M : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det
        = Q ^ 2 * D := by rw [← h1, ← hCD, hdet]
    exact mul_left_cancel₀ (pow_ne_zero _ hQ0) hkey
  · exact ⟨c, by simp⟩

theorem exists_gamma0_factor_finite {M r : ℕ} (hr0 : (r : ℤ) ≠ 0) (k : ZMod r)
    {B : Matrix (Fin 2) (Fin 2) ℤ} (hdetB : B.det = (r : ℤ)) (hB10 : (M : ℤ) ∣ B 1 0)
    (h1 : (r : ℤ) ∣ B 0 1 - (k.val : ℤ) * B 0 0)
    (h2 : (r : ℤ) ∣ B 1 1 - (k.val : ℤ) * B 1 0) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      B = (γ : Matrix (Fin 2) (Fin 2) ℤ) * heckeIndexMat r (some k) := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hprod : (!![B 0 0, s; B 1 0, t] : Matrix (Fin 2) (Fin 2) ℤ)
      * heckeIndexMat r (some k) = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hs
    · linear_combination -ht
  have hdetg : (!![B 0 0, s; B 1 0, t] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have hh : (!![B 0 0, s; B 1 0, t] : Matrix (Fin 2) (Fin 2) ℤ).det * (r : ℤ) = 1 * (r : ℤ) := by
      rw [one_mul]
      conv_rhs => rw [← hdetB, ← hprod]
      rw [Matrix.det_mul, heckeIndexMat_det]
    exact mul_right_cancel₀ hr0 hh
  refine ⟨⟨_, hdetg⟩, ?_, hprod.symm⟩
  rw [Gamma0_mem_iff_intDvd]
  simpa using hB10

theorem exists_gamma0_factor_inf {M r : ℕ} (hr : r.Prime) (hrM : ¬ (r ∣ M))
    {B : Matrix (Fin 2) (Fin 2) ℤ} (hdetB : B.det = (r : ℤ)) (hB10 : (M : ℤ) ∣ B 1 0)
    (h1 : (r : ℤ) ∣ B 0 0) (h2 : (r : ℤ) ∣ B 1 0) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧
      B = (γ : Matrix (Fin 2) (Fin 2) ℤ) * heckeIndexMat r none := by
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hr.ne_zero
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hprod : (!![s, B 0 1; t, B 1 1] : Matrix (Fin 2) (Fin 2) ℤ)
      * heckeIndexMat r none = B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeIndexMat, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -hs
    · linear_combination -ht
  have hdetg : (!![s, B 0 1; t, B 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    have hh : (!![s, B 0 1; t, B 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det * (r : ℤ) = 1 * (r : ℤ) := by
      rw [one_mul]
      conv_rhs => rw [← hdetB, ← hprod]
      rw [Matrix.det_mul, heckeIndexMat_det]
    exact mul_right_cancel₀ hr0 hh
  refine ⟨⟨_, hdetg⟩, ?_, hprod.symm⟩
  rw [Gamma0_mem_iff_intDvd]
  have hcop : IsCoprime ((M : ℕ) : ℤ) ((r : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrM).symm
  have hMt : (M : ℤ) ∣ (r : ℤ) * t := by rw [← ht]; exact hB10
  simpa using hcop.dvd_of_dvd_mul_left hMt

theorem exists_gamma0_atkinLehner_conj_core {M q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r ≠ q)
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
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.ne_zero
  have hr0 : (r : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hr.ne_zero
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  have hrq' : ¬ ((r : ℤ) ∣ (q : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
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

theorem exists_gamma0_atkinLehner_conj {M q r : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (hr : r.Prime) (hrq : r ≠ q)
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
    refine exists_gamma0_atkinLehner_conj_core hq hr hrq hA (heckeIndexMat_det r (some j))
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
    refine exists_gamma0_atkinLehner_conj_core hq hr hrq hA (heckeIndexMat_det r none)
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

/-- **`W_q` COMMUTES WITH `T_r` AT EVERY PRIME `r ≠ q`, at the level of
FUNCTIONS on `ℍ`** (PROVEN 2026-07-27; it was the sorry leaf of the
FOURTEENTH decomposition 2026-07-27) —
Atkin–Lehner 1970, Lemma 17 (`W_Q` commutes with `T_p` and with `U_p`
for every `p ∤ Q`).  This is the `r ≠ q` half of the spectral node
below, stripped of every newform hypothesis: a pure identity between
two finite slash-sums, true for every level-`M` weight-two cusp form.

WHY IT IS TRUE, with the permutation made explicit so a successor need
not rediscover it.  Both sides expand by `SlashAction.slash_mul` into
sums of `⇑f ∣[2] (·)` over the products `A · α_j` (left side) and
`α_k · A` (right side), where `α_j = heckeRep r j = !![1, j; 0, r]` and
`α_∞ = heckeRepInf r = !![r, 0; 0, 1]`.  Since `⇑f ∣[2] γ = ⇑f` for
`γ ∈ Γ₀(M)` (`SlashInvariantFormClass.slash_action_eq`, applied through
`mem_Gamma0GL_iff`), it suffices to produce a PERMUTATION `π` of the
index set together with matrices `γ_j ∈ Γ₀(M)` satisfying

    A · α_j = γ_j · α_{π j} · A .

The permutation is the Möbius action of `Ā⁻¹` on `ℙ¹(𝔽_r)`, and it is
well defined exactly because `r ≠ q`.  Three steps, each elementary:

1. `det A = q` and `r ≠ q` are distinct primes, so `r ∤ q` and
   `Ā := A mod r` is INVERTIBLE over `ZMod r`.
2. Conjugation `β ↦ A β A⁻¹` carries the set `Δ₀(M,r)` of integral
   determinant-`r` matrices with `M ∣ β 1 0` into itself.  This is the
   same pure `Dvd` bookkeeping as `exists_gamma0_of_smul_atkinLehner`
   above: for `C := A * β * A.adjugate` one gets `det C = q ^ 2 * r`,
   `q ∣ C 0 0`, `q ∣ C 0 1`, `q ∣ C 1 1` and `q * M ∣ C 1 0`, using
   ONLY `q ∣ M`, `M ∣ A 1 0`, `M ∣ β 1 0`, `q ∣ A 0 0`, `q ∣ A 1 1` —
   no Bézout relation anywhere.  Since `A * A.adjugate = q • 1`, this
   says `A β A⁻¹` is again integral, determinant `r`, lower-left
   divisible by `M`.
3. Modulo `r`, `α_j ≡ !![1, j; 0, 0]`, which is the RANK-ONE matrix
   `e₀ ⬝ (1, j)`.  Hence `A α_j A⁻¹ ≡ (Ā e₀) ⬝ ((1, j) Ā⁻¹)` is rank
   one too, and writing `(s, t) := (1, j) Ā⁻¹` the class
   `π j := t / s ∈ ℙ¹(𝔽_r)` is exactly the index `k` making
   `γ_j := A α_j A⁻¹ α_k⁻¹` INTEGRAL: with `β := A α_j A⁻¹`, that
   matrix is `!![β 0 0, (β 0 1 - k * β 0 0)/r; β 1 0,
   (β 1 1 - k * β 1 0)/r]`, so integrality is the pair of
   divisibilities `r ∣ β 0 1 - k * β 0 0` and `r ∣ β 1 1 - k * β 1 0`.
   The two are equivalent to each other because `det β = r ≡ 0 mod r`
   (whichever of `β 0 0`, `β 1 0` is invertible mod `r` transports one
   to the other, and they cannot both vanish mod `r`, since then `r^2`
   would divide `det β = r`).  `det γ_j = 1` is a determinant count and
   `M ∣ γ_j 1 0 = β 1 0` is step 2, so `γ_j ∈ Γ₀(M)`.

WHY THE `r ∣ M` CASE LOSES NOTHING.  When `r ∣ M` the sum carries no
`α_∞` term (`heckeTransform`'s `if r ∣ N then 0`), so `π` must preserve
`𝔽_r ⊆ ℙ¹(𝔽_r)`.  It does: `r ∣ M ∣ A 1 0`, so `Ā` is UPPER TRIANGULAR
mod `r` and therefore fixes `∞`, hence permutes the finite points.
That is the only place the shape of `heckeTransform` enters, and it is
why the `U_r` case needs no extra representative.

REFUTING CHECK, so the next owner need not redo the survey: exhibit a
prime `r ≠ q` and a level-`M` weight-two cusp form with
`T_r (f ∣[2] W_q) ≠ (T_r f) ∣[2] W_q`; equivalently, a prime `r ≠ q`
for which conjugation by an Atkin–Lehner matrix fails to permute the
`Γ₀(M)`-cosets inside `Δ₀(M,r)`.  At `r = q` the statement is FALSE in
general — `U_q` and `W_q` do not commute, which is precisely why
Atkin–Lehner restrict Lemma 17 to `p ∤ Q` and why the `r = q` half is a
separate leaf below rather than an instance of this one.

HOW IT IS PROVEN (2026-07-27), for the record.  Exactly the route above,
mechanised by the `ℙ¹(𝔽_r)` toolkit immediately preceding this
declaration.  Both sides become sums over the finset `heckeIndexSet M r`
(`heckeTransform_eq_sum_heckeIndexSet`, plus `finset_sum_slash` to push the
outer slash inside the sum on the right), and `Finset.sum_bijective` closes
the goal from two inputs: `atkinLehnerConjIndex` is bijective and preserves
the index set, and for every index `x` the matrix identity
`A · α_x = γ · α_{π x} · A` of `exists_gamma0_atkinLehner_conj` transports
to `GL₂(ℝ)` and kills `γ` through
`SlashInvariantFormClass.slash_action_eq`.  Nothing here uses newness,
holomorphy or any coefficient — it is an identity of finite slash-sums for
every level-`M` weight-two cusp form, as advertised.  Axiom audit:
`propext, Classical.choice, Quot.sound`. -/
theorem heckeTransform_slash_atkinLehnerRep {M q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : IsAtkinLehnerMatrix M q A)
    {r : ℕ} (hr : r.Prime) (hrq : r ≠ q) (f : CuspForm (Gamma0GL M) 2) :
    heckeTransform M r (⇑f ∣[(2 : ℤ)] atkinLehnerRep A)
      = (heckeTransform M r ⇑f) ∣[(2 : ℤ)] atkinLehnerRep A := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.pos.ne'⟩
  have hq0R : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hr0R : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  have hAne : ((A.map (Int.cast : ℤ → ℝ)).det) ≠ 0 := det_map_cast_ne_zero_isAL hq0R hA
  have hbij : Function.Bijective (atkinLehnerConjIndex r A) :=
    Finite.injective_iff_bijective.mp (atkinLehnerConjIndex_injective hq hr hrq hA)
  have hmem : ∀ x : Option (ZMod r), x ∈ heckeIndexSet M r ↔
      atkinLehnerConjIndex r A x ∈ heckeIndexSet M r := by
    intro x
    unfold heckeIndexSet
    split_ifs with h
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        rcases Option.ne_none_iff_exists.mp
          (atkinLehnerConjIndex_some_ne_none hq hr hrq h hA j) with ⟨k, hk⟩
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
    exact atkinLehnerConjIndex_some_ne_none hq hr hrq hrM hA j hnone
  obtain ⟨γ, hγ, hmat⟩ := exists_gamma0_atkinLehner_conj hq hqM hr hrq hA x hgood
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

/-- **`T_r` and `W_q` commute as ENDOMORPHISMS of `S₂(Γ₀(M))` for
`r ≠ q`** (PROVEN over `heckeTransform_slash_atkinLehnerRep`).  Pure
glue: `heckeOp_coe` and `atkinLehnerOp_coe` unfold both operators to
the function-level identity, and a cusp form is determined by its
underlying function.  `atkinLehnerOp_coe` holds for EVERY Atkin–Lehner
matrix, so the particular one supplied by `exists_isAtkinLehnerMatrix`
is harmless — that is exactly the content the operator leaf bundles. -/
theorem heckeOp_comm_atkinLehnerOp {M : ℕ} (hM : 0 < M) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) (hqM2 : ¬ q ^ 2 ∣ M)
    {r : ℕ} (hr : r.Prime) (hrq : r ≠ q) (f : CuspForm (Gamma0GL M) 2) :
    heckeOp M r (atkinLehnerOp M q f) = atkinLehnerOp M q (heckeOp M r f) := by
  have hcop : Nat.Coprime q (M / q) := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hdvd => hqM2 ?_
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, ?_⟩
    have h := Nat.mul_div_cancel' hqM
    rw [ht] at h
    rw [← h]; ring
  obtain ⟨A, hA⟩ := exists_isAtkinLehnerMatrix hqM hcop
  apply DFunLike.coe_injective
  have h1 : ⇑(heckeOp M r (atkinLehnerOp M q f))
      = heckeTransform M r (⇑f ∣[(2 : ℤ)] atkinLehnerRep A) := by
    rw [heckeOp_coe hM hr, atkinLehnerOp_coe hM hqM hcop hA]
  have h2 : ⇑(atkinLehnerOp M q (heckeOp M r f))
      = (heckeTransform M r ⇑f) ∣[(2 : ℤ)] atkinLehnerRep A := by
    rw [atkinLehnerOp_coe hM hqM hcop hA, heckeOp_coe hM hr]
  rw [h1, h2]
  exact heckeTransform_slash_atkinLehnerRep hq hqM hA hr hrq f

end AtkinLehner

end ConductorCut

end GaloisRepresentation.Modularity
