/-
Modularity/HeckeOperator.lean — own work for the Fermat project.

# `Γ₀(N)` in `GL₂(ℝ)`, the weight-2 Hecke slash-sum, and `T_q` on `S₂(Γ₀(N))`

This module exists to BREAK A MODULE CYCLE, and that is its only reason
for existing.  Every declaration below was hoisted VERBATIM out of
`Fermat/FLT/Modularity/Interface.lean` on 2026-07-27; none of it was
written here and none of it was changed in the move.

The cycle it breaks:

    Modularity/Interface  →  GaloisRepresentation/HardlyRamified/ModThree
                          →  FreyCurve/MazurTorsion  →  ModularCurve/X0

`ModularCurve/X0.lean` needs `S₂(Γ₀(N))` and `T_q` for the
Eichler–Shimura point count `#X₀(N)(𝔽_ℓ) = ℓ + 1 − Tr(T_ℓ)`
(`card_relPoint_x0_finiteField`), and `heckeOp` lived in `Interface.lean`,
which is DOWNSTREAM of `X0.lean` through the chain above.  So `X0.lean`
could not import it.  The route audit recorded on that leaf named this
hoist as the repair and warned against the tempting workaround — a
definition-free `traceHeckeT : ℕ → ℕ → ℤ` — because that would make the
trace table an equation in an `opaque` constant, unprovable in principle.

WHAT IS HERE, and nothing else: `Gamma0GL` and its two instances, the
Hecke coset representatives `heckeRep`/`heckeRepInf`, the slash-sum
`heckeTransform` with its additivity and homogeneity, the stability
argument `exists_cuspForm_heckeTransform` (the slash-sum of a cusp form
is a cusp form), and the bundled operator `heckeOp` with `heckeOp_coe`.
The dependency scan that justified the cut: the moved block references
NOTHING defined in `Interface.lean` outside itself.

Everything else about modular forms — `qCoeff`, `IsWeightTwoEigenform`,
the `q`-expansion of the slash-sum, the Sturm bound, the Hecke algebra,
`EichlerShimuraPackage` — stays in `Interface.lean`, which now `public
import`s this module.  Do not migrate more here without re-running the
reference scan: the point of this module is to be SMALL and upstream of
`X0.lean`, not to become a second modular-forms file.

## THE SECOND `Gamma0GL` IS THE SAME TERM — do not bridge it, do not copy it

(2026-07-28, measured and MACHINE-CHECKED; this note exists because the
duplication has already been read as an incompatibility and cost work.)

There is a second `Gamma0GL` in this tree,
`Fermat.Gamma0GL` in `ModularCurve/WeightTwoEigenform.lean`, written as
the mathlib coercion `((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))`.
That coercion instance is `Mathlib/NumberTheory/ModularForms/ArithmeticSubgroups.lean:83`,
`coe := map (mapGL ℝ)` — i.e. **verbatim the body of the `Gamma0GL`
below**.  Verified in a scratch importing both modules:

* `Fermat.Gamma0GL N = GaloisRepresentation.Modularity.Gamma0GL N := rfl`;
* a term of `CuspForm (Fermat.Gamma0GL N) 2` **is** a term of
  `CuspForm (GaloisRepresentation.Modularity.Gamma0GL N) 2`, in both
  directions, with no cast, no `show` and no bridge lemma;
* `heckeOp N n` (defined here) applies **directly** to a
  `CuspForm (Fermat.Gamma0GL N) 2`.

So the "two rival `Gamma0GL`s" cost exactly nothing at the type level, and
`X0.lean` needs no reconciliation in order to state the Eichler–Shimura
point count over `heckeOp` — the note far down `X0.lean` that spells that
leaf with an explicit `_root_.GaloisRepresentation.Modularity.Gamma0GL`
could equally use its own bare `Gamma0GL`.

**Do not unify the two definitions.** It would retype 289 declarations'
worth of elaboration in the 60k-line `Interface.lean` for zero
mathematical gain, and the compiler already identifies them.  The one
real asymmetry, also checked: `Fermat.Gamma0GL` is an `abbrev`, so
mathlib's generic `IsArithmetic` instance is reachable through it at a
literal level with no `NeZero`, whereas the semireducible `def` here
needs the `[NeZero N]` instance restated below.  Neither side synthesizes
`IsArithmetic` at `N = 0`, so nothing is lost by the difference.

## THE EIGENFORM CARRIER IS A REAL DUPLICATION.  It is NOT this file's.

`Interface.lean` has `IsWeightTwoEigenform N f` (coefficients read off
`qCoeff`) and `IsWeightTwoNewform M g`; `WeightTwoEigenform.lean` has
`Fermat.IsWeightTwoEigenform N f a` (coefficients CARRIED, with a
summability field), and `X1.lean` has `IsWeightTwoEigenformOn G N χ f a`
which subsumes the latter.  Those are genuinely different predicates and
bridging them is a theorem, not a `rfl`.  See the reconciliation plan
recorded in `ModularCurve/WeightTwoEigenform.lean`'s module docstring —
including the reference scan for the hoist of `qCoeff`/the carriers into
THIS module, which is feasible but by itself buys nothing.
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace GaloisRepresentation.Modularity

open scoped MatrixGroups

/-- The congruence subgroup `Γ₀(N)` of `SL₂(ℤ)`, viewed inside
`GL₂(ℝ)` — the shape the pin's analytic `CuspForm` bundle takes its
level in. (The pin's `CongruenceSubgroup.Gamma0` lives in `SL(2, ℤ)`;
`Matrix.SpecialLinearGroup.mapGL` is the canonical inclusion used by
the pin's own congruence-subgroup theory.) -/
def Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- `Γ₀(N)` (in its `GL₂(ℝ)` incarnation) is an arithmetic subgroup for
`N ≠ 0` — mathlib's instance for GL-images of finite-index subgroups of
`SL(2, ℤ)`, restated so that instance search sees through the `Gamma0GL`
definition. This is what feeds the finite-relative-index and cusp
theory (norms/traces to level 1) used in the level-2 emptiness proof
below. -/
instance (N : ℕ) [NeZero N] : (Gamma0GL N).IsArithmetic :=
  inferInstanceAs
    ((↑(CongruenceSubgroup.Gamma0 N) : Subgroup (GL (Fin 2) ℝ)).IsArithmetic)

section HeckeOperator

open UpperHalfPlane ModularForm

/-- `Γ₀(N)` in its `GL₂(ℝ)` incarnation consists of determinant-one
matrices — the `mapGL`-image instance, restated so that instance
search sees through the `Gamma0GL` definition. This is what puts the
`ℂ`-module structure on `CuspForm (Gamma0GL N) 2`, used throughout
the Hecke-basis material below. -/
instance (N : ℕ) : (Gamma0GL N).HasDetOne :=
  inferInstanceAs
    ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)).HasDetOne

/-- The `j`-th upper-triangular coset representative `[1, j; 0, q]` of
the weight-2 Hecke operator `T_q`, viewed in `GL(2, ℝ)` (junk value
`1` when `q = 0`; all uses have `q` prime). Under the slash action it
contributes `τ ↦ f((τ + j)/q)/q` (Diamond–Shurman §5.2: the
representatives `[1, j; 0, q]`, `0 ≤ j < q`, together with
`heckeRepInf q` for `q ∤ N`, form a complete system of right-coset
representatives of `Γ₀(N)` in the degree-`q` double coset). -/
noncomputable def heckeRep (q j : ℕ) : GL (Fin 2) ℝ :=
  if hq : (q : ℝ) ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, (j : ℝ); 0, (q : ℝ)]
      (by rw [Matrix.det_fin_two_of]; simpa using hq)
  else 1

/-- The extra coset representative `[q, 0; 0, 1]` of the weight-2
Hecke operator `T_q` at a good prime `q ∤ N` (junk value `1` when
`q = 0`). Under the slash action it contributes `τ ↦ q·f(qτ)`. At
level `N` with `q ∤ N` the classical representative is
`[m, n; N, q]·[q, 0; 0, 1]` with `mq − nN = 1`, and `[m, n; N, q]`
lies in `Γ₀(N)`, so on `Γ₀(N)`-invariant forms the two choices give
the same slash-sum: this plain matrix is the honest representative of
the same right coset. -/
noncomputable def heckeRepInf (q : ℕ) : GL (Fin 2) ℝ :=
  if hq : (q : ℝ) ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, 1]
      (by rw [Matrix.det_fin_two_of]; simpa using hq)
  else 1

/-- **The weight-2 Hecke slash-sum** (DECOMPOSITION PLAN item 1: the
double-coset operator `T_q` — `U_q` when `q ∣ N` — on functions on the
upper half plane): `f ↦ Σ_{j<q} f∣[2] [1,j;0,q] + 1_{q ∤ N} · f∣[2]
[q,0;0,1]`. With mathlib's slash normalization
(`f∣[k]γ = det(γ)^{k−1}·j(γ,τ)^{−k}·f(γτ)`, and `σ γ = id` since all
representatives have determinant `q > 0`) this is exactly the
classical `T_q` of Diamond–Shurman (5.10) at weight `k = 2`; its
`q`-expansion is computed by `qExpansion_heckeTransform_coeff` below,
and its stability on cusp forms is `exists_cuspForm_heckeTransform`
(both PROVEN). -/
noncomputable def heckeTransform (N q : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  (∑ j ∈ Finset.range q, f ∣[(2 : ℤ)] heckeRep q j) +
    if q ∣ N then 0 else f ∣[(2 : ℤ)] heckeRepInf q

/-- The Hecke slash-sum is additive in the form (each slash is). -/
theorem heckeTransform_add (N q : ℕ) (f g : ℍ → ℂ) :
    heckeTransform N q (f + g) = heckeTransform N q f + heckeTransform N q g := by
  unfold heckeTransform
  split_ifs with h
  · simp [Finset.sum_add_distrib]
  · simp only [SlashAction.add_slash, Finset.sum_add_distrib]
    abel

/-- The slash conjugation factor `σ` of the upper-triangular Hecke
representatives is the identity (their determinants are positive), so
their slash action commutes with COMPLEX scalars. -/
theorem σ_heckeRep (q j : ℕ) (c : ℂ) : σ (heckeRep q j) c = c := by
  have hdet : 0 < (heckeRep q j).det.val := by
    unfold heckeRep
    split_ifs with hq
    · have hq' : (0 : ℝ) < q := lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hq)
      simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of] using hq'
    · simp
  simp only [σ, if_pos hdet, ContinuousAlgEquiv.refl_apply]

/-- The slash conjugation factor `σ` of the extra Hecke representative
is the identity (its determinant is positive). -/
theorem σ_heckeRepInf (q : ℕ) (c : ℂ) : σ (heckeRepInf q) c = c := by
  have hdet : 0 < (heckeRepInf q).det.val := by
    unfold heckeRepInf
    split_ifs with hq
    · have hq' : (0 : ℝ) < q := lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hq)
      simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of] using hq'
    · simp
  simp only [σ, if_pos hdet, ContinuousAlgEquiv.refl_apply]

/-- The Hecke slash-sum commutes with complex scalars (each slash
does, the representatives having positive determinant). -/
theorem heckeTransform_smul (N q : ℕ) (c : ℂ) (f : ℍ → ℂ) :
    heckeTransform N q (c • f) = c • heckeTransform N q f := by
  unfold heckeTransform
  split_ifs with h
  · simp [ModularForm.smul_slash, Finset.smul_sum, σ_heckeRep]
  · simp [ModularForm.smul_slash, Finset.smul_sum, smul_add, σ_heckeRep, σ_heckeRepInf]

/-! #### Hecke stability: the trace identification toolkit

`exists_cuspForm_heckeTransform` below is proven by identifying the
Hecke slash-sum with mathlib's `CuspForm.trace`: for
`α = heckeRep q 0 = [1, 0; 0, q]` the translate `f ∣[2] α` is a cusp
form on the conjugate group `α⁻¹ Γ₀(N) α` (`CuspForm.translate` —
holomorphy and cusp vanishing travel along), and its trace back to
`Γ₀(N)` is a bona fide `CuspForm` whose underlying function is
EXACTLY `heckeTransform N q f`, once the coset space
`Γ₀(N) ⧸ (Γ₀(N) ∩ α⁻¹Γ₀(N)α)` is enumerated by the classical Hecke
representatives. The finiteness of that coset space is mathlib's
`Subgroup.IsArithmetic.conj` (conjugation by `GL(2, ℚ)` preserves
arithmeticity). The enumeration itself is driven by one divisibility
criterion, `heckeRep_conj_mem_iff`: for `ρ ∈ Γ₀(N)`, the conjugate
`α ρ α⁻¹` lies in `Γ₀(N)` iff `q ∣ ρ₀₁` — conjugation by `α` divides
the upper-right entry by `q` and multiplies the lower-left by `q`, so
integrality is exactly that divisibility. -/
section HeckeStability

open Matrix.SpecialLinearGroup CongruenceSubgroup ConjAct
open scoped Pointwise

/-- The matrix entries of the Hecke representative (any `q ≠ 0`). -/
theorem heckeRep_coe {q : ℕ} (hq0 : (q : ℝ) ≠ 0) (j : ℕ) :
    (heckeRep q j : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (j : ℝ); 0, (q : ℝ)] := by
  unfold heckeRep
  rw [dif_pos hq0]
  rfl

/-- The matrix entries of the extra Hecke representative (any `q ≠ 0`). -/
theorem heckeRepInf_coe {q : ℕ} (hq0 : (q : ℝ) ≠ 0) :
    (heckeRepInf q : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, 1] := by
  unfold heckeRepInf
  rw [dif_pos hq0]
  rfl

/-- The integral translation matrix `[1, j; 0, 1]` — the `SL(2, ℤ)`
carrier of (the inverses of) the finite Hecke coset representatives. -/
def heckeTMat (j : ℤ) : SL(2, ℤ) :=
  ⟨!![1, j; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- Translations lie in `Γ₀(N)` for every `N`. -/
theorem heckeTMat_mem_Gamma0 (N : ℕ) (j : ℤ) :
    heckeTMat j ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, heckeTMat]

/-- Translations compose additively. -/
theorem heckeTMat_mul (a b : ℤ) :
    heckeTMat a * heckeTMat b = heckeTMat (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeTMat, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The inverse of a translation is the opposite translation. -/
theorem heckeTMat_inv (a : ℤ) : (heckeTMat a)⁻¹ = heckeTMat (-a) := by
  have h1 : heckeTMat a * heckeTMat (-a) = 1 := by
    rw [heckeTMat_mul, add_neg_cancel]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeTMat]
  exact inv_eq_of_mul_eq_one_right h1

/-- The upper-right entry of an `SL(2, ℤ)` product, explicitly. -/
theorem SL2_mul_apply_zero_one (x y : SL(2, ℤ)) :
    (x * y) 0 1 = x 0 0 * y 0 1 + x 0 1 * y 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `Γ₀(N)` in `GL(2, ℝ)` is exactly the `mapGL`-image of the integral
`Γ₀(N)` — membership unfolded. -/
theorem mem_Gamma0GL_iff {N : ℕ} {x : GL (Fin 2) ℝ} :
    x ∈ Gamma0GL N ↔ ∃ δ ∈ CongruenceSubgroup.Gamma0 N, mapGL ℝ δ = x := by
  unfold Gamma0GL
  exact Subgroup.mem_map

/-- Membership in the `ConjAct`-conjugate subgroup, unfolded to a
conjugation condition. -/
theorem mem_conjAct_inv_smul_iff {α x : GL (Fin 2) ℝ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} :
    x ∈ toConjAct α⁻¹ • Γ ↔ α * x * α⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv,
    toConjAct_smul]

/-- **The Hecke coset criterion**: for `ρ ∈ Γ₀(N)` and `q` prime, the
conjugate `α ρ α⁻¹` by `α = heckeRep q 0 = [1, 0; 0, q]` lies in
`Γ₀(N)` iff `q ∣ ρ₀₁`. Conjugation by `α` divides the upper-right
entry by `q` and multiplies the lower-left by `q`, so integrality of
the conjugate is exactly the divisibility of `ρ₀₁`. This single
equivalence drives both injectivity and surjectivity of the Hecke
coset enumeration in `exists_cuspForm_heckeTransform`. -/
theorem heckeRep_conj_mem_iff {N q : ℕ} (hq : q.Prime) {ρ : SL(2, ℤ)}
    (hρ : ρ ∈ CongruenceSubgroup.Gamma0 N) :
    heckeRep q 0 * mapGL ℝ ρ * (heckeRep q 0)⁻¹ ∈ Gamma0GL N ↔
      (q : ℤ) ∣ ρ 0 1 := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  constructor
  · intro h
    obtain ⟨ε, -, hεeq⟩ := mem_Gamma0GL_iff.mp h
    have heq : mapGL ℝ ε * heckeRep q 0 = heckeRep q 0 * mapGL ℝ ρ := by
      rw [hεeq]; group
    have h01 := congr_arg
      (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) heq
    simp [heckeRep_coe hq0,
      mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
    refine ⟨ε 0 1, ?_⟩
    have hcast : ((ρ 0 1 : ℤ) : ℝ) = (((q : ℤ) * ε 0 1 : ℤ) : ℝ) := by
      push_cast
      linarith [h01]
    exact_mod_cast hcast
  · rintro ⟨t, ht⟩
    have hdet : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
      have h2 := ρ.2
      rwa [Matrix.det_fin_two] at h2
    have hc : ((ρ 1 0 : ℤ) : ZMod N) = 0 := by
      rw [CongruenceSubgroup.Gamma0_mem] at hρ
      exact_mod_cast hρ
    refine mem_Gamma0GL_iff.mpr ⟨⟨!![ρ 0 0, t; (q : ℤ) * ρ 1 0, ρ 1 1], ?_⟩,
      ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      have hqt : ρ 0 0 * ρ 1 1 - ((q : ℤ) * t) * ρ 1 0 = 1 := ht ▸ hdet
      linarith [hqt]
    · rw [CongruenceSubgroup.Gamma0_mem]
      show (((q : ℤ) * ρ 1 0 : ℤ) : ZMod N) = 0
      push_cast
      rw [hc, mul_zero]
    · rw [eq_mul_inv_iff_mul_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        · simp [heckeRep_coe hq0, mapGL_coe_matrix,
            Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
            Int.coe_castRingHom, Matrix.map_apply, Matrix.mul_apply,
            Fin.sum_univ_two, ht]
          try ring

/-- The rational carrier of `heckeRep q 0`, witnessing that
conjugation by it preserves arithmeticity (junk value `1` at
`q = 0`). -/
noncomputable def heckeRepQ (q : ℕ) : GL (Fin 2) ℚ :=
  if hq : (q : ℚ) ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (q : ℚ)]
      (by rw [Matrix.det_fin_two_of]; simpa using hq)
  else 1

/-- `heckeRep q 0` is the real image of its rational carrier. -/
theorem heckeRepQ_map {q : ℕ} (hq0 : (q : ℝ) ≠ 0) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (heckeRepQ q) =
      heckeRep q 0 := by
  have hqQ : (q : ℚ) ≠ 0 := fun h => hq0 (by exact_mod_cast h)
  have hcoe : (heckeRepQ q : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (q : ℚ)] := by
    unfold heckeRepQ
    rw [dif_pos hqQ]
    rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, hcoe, heckeRep_coe hq0]

/-- The `α⁻¹Γ₀(N)α`-conjugate of `Γ₀(N)` is arithmetic — mathlib's
`Subgroup.IsArithmetic.conj` applied to the rational carrier of the
Hecke matrix. -/
theorem heckeConj_isArithmetic {N q : ℕ} [NeZero N] (hq : q.Prime) :
    (toConjAct (heckeRep q 0)⁻¹ • Gamma0GL N).IsArithmetic := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have h := Subgroup.IsArithmetic.conj (Gamma0GL N) (heckeRepQ q)⁻¹
  rwa [Matrix.GeneralLinearGroup.map_inv, heckeRepQ_map hq0] at h

/-- The conjugate `α⁻¹Γ₀(N)α` has finite relative index in `Γ₀(N)`
(both are arithmetic, hence commensurable through `SL(2, ℤ)`). This is
the hypothesis powering `CuspForm.trace` in
`exists_cuspForm_heckeTransform`. -/
theorem heckeConj_isFiniteRelIndex {N q : ℕ} [NeZero N] (hq : q.Prime) :
    Subgroup.IsFiniteRelIndex (toConjAct (heckeRep q 0)⁻¹ • Gamma0GL N)
      (Gamma0GL N) :=
  haveI := heckeConj_isArithmetic (N := N) hq
  ⟨(Subgroup.IsArithmetic.is_commensurable.trans
      Subgroup.IsArithmetic.is_commensurable.symm).1⟩

/-- The finite Hecke representatives as products: `α · [1, j; 0, 1] =
[1, j; 0, q]`. -/
theorem heckeRep_zero_mul_heckeTMat {q : ℕ} (hq0 : (q : ℝ) ≠ 0) (j : ℕ) :
    heckeRep q 0 * mapGL ℝ (heckeTMat (j : ℤ)) = heckeRep q j := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [heckeRep_coe hq0, heckeTMat, mapGL_coe_matrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- **Hecke stability of cusp forms** (Diamond–Shurman Propositions
5.1.5 and 5.2.1–5.2.2 for `Γ₀(N)`, weight 2): the Hecke slash-sum of a
weight-2 level-`N` cusp form is again a weight-2 level-`N` cusp form.
Proof: the slash-sum is the `CuspForm.trace` back to `Γ₀(N)` of the
`α`-translate of `f` (`α = [1, 0; 0, q]`), a cusp form on the
arithmetic conjugate group; the coset space is enumerated by the
classical representatives through the divisibility criterion
`heckeRep_conj_mem_iff` — the `q` translations `[1, j; 0, q]`, plus
`[q, 0; 0, 1]` at good primes via a Bézout matrix in `Γ₀(N)`. -/
theorem exists_cuspForm_heckeTransform {N : ℕ} (hN : 0 < N) {q : ℕ}
    (hq : q.Prime) (f : CuspForm (Gamma0GL N) 2) :
    ∃ g : CuspForm (Gamma0GL N) 2, ⇑g = heckeTransform N q ⇑f := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hFact : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  haveI hFRI := heckeConj_isFiniteRelIndex (N := N) hq
  refine ⟨CuspForm.trace (Gamma0GL N) (CuspForm.translate f (heckeRep q 0)), ?_⟩
  rw [CuspForm.coe_trace]
  set Γc : Subgroup (GL (Fin 2) ℝ) := toConjAct (heckeRep q 0)⁻¹ • Gamma0GL N
    with hΓc
  letI instQ : Fintype ((Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) :=
    Fintype.ofFinite _
  -- membership of the translation representatives
  have hTmem : ∀ j : ℤ, mapGL ℝ (heckeTMat j) ∈ Gamma0GL N := fun j =>
    mem_Gamma0GL_iff.mpr ⟨heckeTMat j, heckeTMat_mem_Gamma0 N j, rfl⟩
  -- the packaged coset criterion
  have hcrit : ∀ (x y : Gamma0GL N) (ρ : SL(2, ℤ)),
      ρ ∈ CongruenceSubgroup.Gamma0 N →
      mapGL ℝ ρ = (x : GL (Fin 2) ℝ)⁻¹ * y →
      ((⟦x⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) = ⟦y⟧ ↔
        (q : ℤ) ∣ ρ 0 1) := by
    intro x y ρ hρ hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcoe : ((x⁻¹ * y : Gamma0GL N) : GL (Fin 2) ℝ) = mapGL ℝ ρ := by
      rw [hxy]; rfl
    rw [hcoe, hΓc, mem_conjAct_inv_smul_iff]
    exact heckeRep_conj_mem_iff hq hρ
  -- the finite coset representatives
  set E : Fin q → Gamma0GL N := fun j =>
    ⟨mapGL ℝ (heckeTMat (-(j : ℤ))), hTmem _⟩ with hE
  have hEinv : ∀ j : Fin q,
      ((E j : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ = mapGL ℝ (heckeTMat (j : ℤ)) := by
    intro j
    show (mapGL ℝ (heckeTMat (-(j : ℤ))))⁻¹ = _
    rw [← map_inv, heckeTMat_inv, neg_neg]
  -- value of each finite coset under quotientFunc
  have hEval : ∀ j : Fin q,
      SlashInvariantForm.quotientFunc (CuspForm.translate f (heckeRep q 0)) ⟦E j⟧
        = ⇑f ∣[(2 : ℤ)] heckeRep q (j : ℕ) := by
    intro j
    rw [SlashInvariantForm.quotientFunc_mk]
    show (⇑f ∣[(2 : ℤ)] heckeRep q 0) ∣[(2 : ℤ)]
      ((E j : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ = _
    rw [hEinv j, ← SlashAction.slash_mul, heckeRep_zero_mul_heckeTMat hq0]
  -- injectivity of the finite enumeration
  have hEinj : ∀ j j' : Fin q,
      ((⟦E j⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) = ⟦E j'⟧) →
      j = j' := by
    intro j j' hjj'
    have hρ : mapGL ℝ (heckeTMat ((j : ℤ) - (j' : ℤ))) =
        ((E j : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ * (E j') := by
      rw [hEinv j]
      show _ = mapGL ℝ (heckeTMat (j : ℤ)) * mapGL ℝ (heckeTMat (-(j' : ℤ)))
      rw [← map_mul, heckeTMat_mul, sub_eq_add_neg]
    have hd := (hcrit _ _ _ (heckeTMat_mem_Gamma0 N _) hρ).mp hjj'
    have hd' : (q : ℤ) ∣ (j : ℤ) - (j' : ℤ) := by simpa [heckeTMat] using hd
    obtain ⟨t, ht⟩ := hd'
    have hjq : ((j : ℕ) : ℤ) < q := by exact_mod_cast j.isLt
    have hj'q : ((j' : ℕ) : ℤ) < q := by exact_mod_cast j'.isLt
    have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
    have hj'0 : (0 : ℤ) ≤ ((j' : ℕ) : ℤ) := Int.natCast_nonneg _
    have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.pos
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
    have hjj : ((j : ℕ) : ℤ) = ((j' : ℕ) : ℤ) := by linarith
    exact Fin.ext (by exact_mod_cast hjj)
  -- the finite-representative finder: whenever `q ∤ δ₁₁`, the coset of
  -- `mapGL δ` is one of the `q` translation cosets
  have hfind : ∀ (y : Gamma0GL N) (δ : SL(2, ℤ)),
      δ ∈ CongruenceSubgroup.Gamma0 N → mapGL ℝ δ = (y : GL (Fin 2) ℝ) →
      ¬ (q : ℤ) ∣ δ 1 1 →
      ∃ j : Fin q,
        (⟦E j⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) = ⟦y⟧ := by
    intro y δ hδ hδeq hqd
    have hdbar : ((δ 1 1 : ℤ) : ZMod q) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨⟨(-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val,
      ZMod.val_lt _⟩, ?_⟩
    have hρmem : heckeTMat
          (((-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val : ℕ) : ℤ) * δ
        ∈ CongruenceSubgroup.Gamma0 N :=
      mul_mem (heckeTMat_mem_Gamma0 N _) hδ
    have hρeq : mapGL ℝ (heckeTMat
          (((-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val : ℕ) : ℤ) * δ) =
        ((E ⟨(-((δ 0 1 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q)⁻¹).val,
          ZMod.val_lt _⟩ : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ * y := by
      rw [map_mul, hEinv, hδeq]
    refine (hcrit _ _ _ hρmem hρeq).mpr ?_
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
  by_cases hqN : q ∣ N
  · -- `U_q`: exactly the `q` translation cosets
    have hEsurj : Function.Surjective (fun j : Fin q =>
        (⟦E j⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N))) := by
      intro x
      induction x using Quotient.inductionOn with
      | h y =>
        obtain ⟨δ, hδ, hδeq⟩ := mem_Gamma0GL_iff.mp y.2
        have hNc : ((N : ℤ)) ∣ δ 1 0 := by
          have hg := hδ
          rw [CongruenceSubgroup.Gamma0_mem] at hg
          rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hqd : ¬ (q : ℤ) ∣ δ 1 1 := by
          intro hdvd
          have hqc : (q : ℤ) ∣ δ 1 0 :=
            dvd_trans (Int.natCast_dvd_natCast.mpr hqN) hNc
          have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
            have h2 := δ.2
            rwa [Matrix.det_fin_two] at h2
          have hone : (q : ℤ) ∣ 1 := by
            have h5 : (q : ℤ) ∣ δ 0 0 * δ 1 1 := hdvd.mul_left _
            have h6 : (q : ℤ) ∣ δ 0 1 * δ 1 0 := hqc.mul_left _
            have h7 := dvd_sub h5 h6
            rwa [hdet] at h7
          have hle := Int.le_of_dvd one_pos hone
          exact absurd hle (by exact_mod_cast hq.one_lt.not_ge)
        exact hfind y δ hδ hδeq hqd
    have hbij : Function.Bijective (fun j : Fin q =>
        (⟦E j⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N))) :=
      ⟨fun a b hab => hEinj a b hab, hEsurj⟩
    have h11 : (∑ j : Fin q, SlashInvariantForm.quotientFunc
          (CuspForm.translate f (heckeRep q 0)) ⟦E j⟧)
        = ∑ x : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N),
            SlashInvariantForm.quotientFunc
              (CuspForm.translate f (heckeRep q 0)) x :=
      Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    have h12 : (∑ j : Fin q, SlashInvariantForm.quotientFunc
          (CuspForm.translate f (heckeRep q 0)) ⟦E j⟧)
        = heckeTransform N q ⇑f := by
      unfold heckeTransform
      rw [if_pos hqN, add_zero, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => hEval j
    exact h11.symm.trans h12
  · -- `T_q` at a good prime: the `q` translation cosets plus the `∞` coset
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * q - v * N = 1 := by
      have hcop : Nat.Coprime q N := (hq.coprime_iff_not_dvd).mpr hqN
      have hb := Nat.gcd_eq_gcd_ab q N
      rw [hcop] at hb
      refine ⟨Nat.gcdA q N, -(Nat.gcdB q N), ?_⟩
      push_cast at hb
      linarith [hb]
    set W : SL(2, ℤ) := ⟨!![u * q, v; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]; linarith [huv]⟩ with hW
    have hWmem : W ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      show (((N : ℤ)) : ZMod N) = 0
      push_cast
      exact ZMod.natCast_self N
    set D : SL(2, ℤ) := ⟨!![u, v; (N : ℤ), (q : ℤ)], by
      rw [Matrix.det_fin_two_of]; linarith [huv]⟩ with hD
    have hDmem : D ∈ CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      show (((N : ℤ)) : ZMod N) = 0
      push_cast
      exact ZMod.natCast_self N
    have hWinvmem : mapGL ℝ W⁻¹ ∈ Gamma0GL N :=
      mem_Gamma0GL_iff.mpr ⟨W⁻¹, inv_mem hWmem, rfl⟩
    set Einf : Gamma0GL N := ⟨mapGL ℝ W⁻¹, hWinvmem⟩ with hEinf
    have hEinfinv : ((Einf : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ = mapGL ℝ W := by
      show (mapGL ℝ W⁻¹)⁻¹ = _
      rw [← map_inv, inv_inv]
    -- the explicit inverse of the Bézout matrix
    have hWinv : W⁻¹ = ⟨!![1, -v; -(N : ℤ), u * q], by
        rw [Matrix.det_fin_two_of]; linarith [huv]⟩ := by
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [hW]
    -- α · W = D · heckeRepInf q
    have hkey : heckeRep q 0 * mapGL ℝ W = mapGL ℝ D * heckeRepInf q := by
      ext i k
      fin_cases i <;> fin_cases k <;>
        · simp [heckeRep_coe hq0, heckeRepInf_coe hq0, hW, hD, mapGL_coe_matrix,
            Matrix.mul_apply, Fin.sum_univ_two]
          try ring
    -- value at the `∞` coset
    have hEinfval : SlashInvariantForm.quotientFunc
        (CuspForm.translate f (heckeRep q 0)) ⟦Einf⟧
          = ⇑f ∣[(2 : ℤ)] heckeRepInf q := by
      rw [SlashInvariantForm.quotientFunc_mk]
      show (⇑f ∣[(2 : ℤ)] heckeRep q 0) ∣[(2 : ℤ)]
        ((Einf : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ = _
      rw [hEinfinv, ← SlashAction.slash_mul, hkey, SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq f (mapGL ℝ D)
          (mem_Gamma0GL_iff.mpr ⟨D, hDmem, rfl⟩)]
    -- the full enumeration
    have hinj : Function.Injective (fun o : Option (Fin q) =>
        Option.elim o
          (⟦Einf⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N))
          (fun j => ⟦E j⟧)) := by
      intro o o' hoo'
      -- the mixed case is impossible: `q ∤ v`
      have hmix : ∀ j : Fin q,
          (⟦E j⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) ≠ ⟦Einf⟧ := by
        intro j hjinf
        have hρ : mapGL ℝ (heckeTMat (j : ℤ) * W⁻¹) =
            ((E j : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ * Einf := by
          rw [map_mul, hEinv j]
        have hd := (hcrit _ _ _
          (mul_mem (heckeTMat_mem_Gamma0 N _) (inv_mem hWmem)) hρ).mp hjinf
        have hval : (heckeTMat (j : ℤ) * W⁻¹) 0 1 = -v + (j : ℤ) * (u * q) := by
          rw [hWinv, SL2_mul_apply_zero_one]
          simp [heckeTMat]
        rw [hval] at hd
        have hqv : (q : ℤ) ∣ v := by
          have h7 : (q : ℤ) ∣ (j : ℤ) * (u * q) := ⟨(j : ℤ) * u, by ring⟩
          have h8 := dvd_sub h7 hd
          have h9 : (j : ℤ) * (u * q) - (-v + (j : ℤ) * (u * q)) = v := by ring
          rwa [h9] at h8
        have hone : (q : ℤ) ∣ 1 := by
          have h9 : (q : ℤ) ∣ u * q := ⟨u, mul_comm _ _⟩
          have h10 : (q : ℤ) ∣ v * N := hqv.mul_right _
          have h11 := dvd_sub h9 h10
          rwa [huv] at h11
        have hle := Int.le_of_dvd one_pos hone
        exact absurd hle (by exact_mod_cast hq.one_lt.not_ge)
      match o, o' with
      | none, none => rfl
      | none, some j' => exact absurd hoo'.symm (hmix j')
      | some j, none => exact absurd hoo' (hmix j)
      | some j, some j' => exact congrArg some (hEinj j j' hoo')
    have hsurj : Function.Surjective (fun o : Option (Fin q) =>
        Option.elim o
          (⟦Einf⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N))
          (fun j => ⟦E j⟧)) := by
      intro x
      induction x using Quotient.inductionOn with
      | h y =>
        obtain ⟨δ, hδ, hδeq⟩ := mem_Gamma0GL_iff.mp y.2
        by_cases hqd : (q : ℤ) ∣ δ 1 1
        · refine ⟨none, ?_⟩
          show (⟦Einf⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N)) = ⟦y⟧
          have hρeq : mapGL ℝ (W * δ) =
              ((Einf : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ * y := by
            rw [map_mul, hEinfinv, hδeq]
          refine (hcrit _ _ _ (mul_mem hWmem hδ) hρeq).mpr ?_
          have hval : (W * δ) 0 1 = u * q * δ 0 1 + v * δ 1 1 := by
            rw [SL2_mul_apply_zero_one]
            simp [hW]
          rw [hval]
          exact dvd_add ⟨u * δ 0 1, by ring⟩ (hqd.mul_left v)
        · obtain ⟨j, hj⟩ := hfind y δ hδ hδeq hqd
          exact ⟨some j, hj⟩
    have hbij : Function.Bijective (fun o : Option (Fin q) =>
        Option.elim o
          (⟦Einf⟧ : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N))
          (fun j => ⟦E j⟧)) := ⟨hinj, hsurj⟩
    have h11 : (∑ o : Option (Fin q), SlashInvariantForm.quotientFunc
          (CuspForm.translate f (heckeRep q 0))
          (Option.elim o ⟦Einf⟧ (fun j => ⟦E j⟧)))
        = ∑ x : (Gamma0GL N) ⧸ Γc.subgroupOf (Gamma0GL N),
            SlashInvariantForm.quotientFunc
              (CuspForm.translate f (heckeRep q 0)) x :=
      Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    have h12 : (∑ o : Option (Fin q), SlashInvariantForm.quotientFunc
          (CuspForm.translate f (heckeRep q 0))
          (Option.elim o ⟦Einf⟧ (fun j => ⟦E j⟧)))
        = heckeTransform N q ⇑f := by
      have hsum : (∑ j : Fin q, SlashInvariantForm.quotientFunc
            (CuspForm.translate f (heckeRep q 0)) ⟦E j⟧)
          = ∑ j ∈ Finset.range q, ⇑f ∣[(2 : ℤ)] heckeRep q j := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_congr rfl fun j _ => hEval j
      rw [Fintype.sum_option]
      show SlashInvariantForm.quotientFunc (CuspForm.translate f (heckeRep q 0)) ⟦Einf⟧
          + (∑ j : Fin q, SlashInvariantForm.quotientFunc
              (CuspForm.translate f (heckeRep q 0)) ⟦E j⟧) = _
      rw [hEinfval, hsum]
      unfold heckeTransform
      rw [if_neg hqN]
      exact add_comm _ _
    exact h11.symm.trans h12

end HeckeStability

/-- **The Hecke operator `T_q` on `S₂(Γ₀(M))` as a bundled linear
endomorphism** (PROVEN): the Hecke slash-sum `heckeTransform M q`
preserves the weight-2 level-`M` cusp space
(`exists_cuspForm_heckeTransform`), is additive and `ℂ`-homogeneous
(`heckeTransform_add`, `heckeTransform_smul`), and the underlying
function determines the cusp form, so the pointwise choice of
preimages assembles into a `ℂ`-linear endomorphism. -/
theorem exists_heckeOpLinear {M : ℕ} (hM : 0 < M) {q : ℕ} (hq : q.Prime) :
    ∃ F : Module.End ℂ (CuspForm (Gamma0GL M) 2),
      ∀ f : CuspForm (Gamma0GL M) 2, ⇑(F f) = heckeTransform M q ⇑f := by
  classical
  choose T hT using fun f : CuspForm (Gamma0GL M) 2 =>
    exists_cuspForm_heckeTransform hM hq f
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, hT⟩
  · intro f₁ f₂
    apply DFunLike.coe_injective
    simp only [CuspForm.coe_add, hT, heckeTransform_add]
  · intro c f
    apply DFunLike.coe_injective
    simp only [RingHom.id_apply, CuspForm.IsGLPos.coe_smul, hT,
      heckeTransform_smul]

/-- The unconditional form of `exists_heckeOpLinear`, so that the Hecke
operator can be DEFINED at every pair `(M, q)` (junk — the zero
endomorphism — outside the meaningful range `0 < M`, `q` prime, which
is all any statement below quantifies over). -/
theorem exists_heckeOpLinear_total (M q : ℕ) :
    ∃ F : Module.End ℂ (CuspForm (Gamma0GL M) 2),
      0 < M → q.Prime →
        ∀ f : CuspForm (Gamma0GL M) 2, ⇑(F f) = heckeTransform M q ⇑f := by
  by_cases h : 0 < M ∧ q.Prime
  · obtain ⟨F, hF⟩ := exists_heckeOpLinear h.1 h.2
    exact ⟨F, fun _ _ => hF⟩
  · exact ⟨0, fun hM hq => absurd ⟨hM, hq⟩ h⟩

/-- **The Hecke operator `T_q` on `S₂(Γ₀(M))`** — the complex side of
the Eichler–Shimura seam. At `0 < M` and `q` prime it is the bundled
`heckeTransform M q` (`heckeOp_coe`); elsewhere it is junk, which no
statement about it looks at (all quantify over primes). -/
noncomputable def heckeOp (M q : ℕ) : Module.End ℂ (CuspForm (Gamma0GL M) 2) :=
  (exists_heckeOpLinear_total M q).choose

/-- The Hecke operator acts by the Hecke slash-sum. -/
theorem heckeOp_coe {M : ℕ} (hM : 0 < M) {q : ℕ} (hq : q.Prime)
    (f : CuspForm (Gamma0GL M) 2) :
    ⇑(heckeOp M q f) = heckeTransform M q ⇑f :=
  (exists_heckeOpLinear_total M q).choose_spec hM hq f

end HeckeOperator

/-! ### `S₂(Γ₀(1)) = 0`

**HOISTED HERE FROM `Modularity/Interface.lean` on 2026-07-28**, unchanged
except for its position.  The block used to sit inside `Interface.lean`'s
`LevelTwoEmptiness` section, which is *downstream* of
`ModularCurve/X0.lean`; it is needed *upstream*, by
`Fermat.cuspForm_eq_zero_of_properDivisor_oneSixtyNine` in `X0.lean`, whose
`M ∣ 169`, `M ≠ 169` splits as `M = 1` (this theorem) and `M = 13` (a leaf).
`Interface.lean` keeps `weightTwoEigenform_level_one_false`, which is stated
with `qCoeff` and cannot move; it names `cuspForm_level_one_coe_eq_zero` in
this same namespace, so nothing there changes.

This module is the right home rather than an accident of the hoist: the
`IsArithmetic` instance above already exists to feed exactly this
"norms/traces to level 1" theory, and its own docstring says so.

The argument (see `Interface.lean`'s section header for the level-2
companion, which is the same one at relative index `3`): the norm of
`f ∈ S₂(Γ₀(1))` over `SL(2, ℤ)` is a LEVEL-1 form of weight
`2 · [SL(2,ℤ) : Γ₀(1)] = 2`; every factor vanishes at `i∞`, so the norm has
positive `q`-expansion order, and the level-1 Sturm bound at weight `2`
(`2/12 = 0`) forces it to vanish — while a nonzero `f` has nonzero norm.

**Note for anyone extending this to another level.**  The route caps out
here.  At level `M` the norm has weight `2·[SL(2,ℤ) : Γ₀(M)]` and the
Sturm threshold is `⌊weight/12⌋`, while all this argument supplies is
`order ≥ 1` (the constant term).  That is enough exactly when
`2·[SL(2,ℤ):Γ₀(M)] < 24`, i.e. `[SL(2,ℤ):Γ₀(M)] ≤ 11` — true at `M = 1`
(index `1`) and `M = 2` (index `3`), FALSE at `M = 13` (index `14`,
weight `28`, threshold `2`).  So `S₂(Γ₀(13)) = 0` is genuinely out of
reach here and is a leaf in `X0.lean`, not an oversight. -/

section LevelOneEmptiness

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup

/-- `Γ₀(1) = SL(2, ℤ)`: the mod-1 congruence condition is vacuous
(`ZMod 1` is trivial). -/
theorem Gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext g
  simp [CongruenceSubgroup.Gamma0_mem, Subsingleton.elim (g.1 1 0 : ZMod 1) 0]

/-- The relative index of `Γ₀(1)` in `SL(2, ℤ)` (both viewed in
`GL(2, ℝ)`) is `1`: `Γ₀(1)` IS `SL(2, ℤ)`. -/
theorem Gamma0GL_one_relIndex : (Gamma0GL 1).relIndex 𝒮ℒ = 1 := by
  show ((CongruenceSubgroup.Gamma0 1).map (mapGL ℝ)).relIndex 𝒮ℒ = 1
  rw [Gamma0_one_eq_top, ← MonoidHom.range_eq_map, Subgroup.relIndex_self]

/-- Every `SL(2, ℤ)`-translate of a weight-2 cusp form on `Γ₀(1)`
vanishes at `i∞` — these are the factors of the norm form. -/
theorem quotientFunc_level_one_isZeroAtImInfty (f : CuspForm (Gamma0GL 1) 2)
    (q : 𝒮ℒ ⧸ (Gamma0GL 1).subgroupOf 𝒮ℒ) :
    IsZeroAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [SlashInvariantForm.quotientFunc_mk]
    have hinf : IsCusp OnePoint.infty 𝒮ℒ := isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩
    have hcusp : IsCusp ((r.val)⁻¹ • OnePoint.infty) (Gamma0GL 1) :=
      (hinf.smul_of_mem (inv_mem r.2)).of_isFiniteRelIndex
    exact CuspFormClass.zero_at_cusps f hcusp _ rfl

/-- The norm (over `SL(2, ℤ)`) of a weight-2 cusp form on `Γ₀(1)`
vanishes at `i∞`: it is a finite product of translates, each of which
vanishes there. -/
theorem norm_level_one_isZeroAtImInfty (f : CuspForm (Gamma0GL 1) 2) :
    IsZeroAtImInfty ⇑(ModularForm.norm 𝒮ℒ f) := by
  rw [ModularForm.coe_norm]
  letI := Fintype.ofFinite (𝒮ℒ ⧸ (Gamma0GL 1).subgroupOf 𝒮ℒ)
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  have hzero : (0 : ℂ) = ∏ _q : 𝒮ℒ ⧸ (Gamma0GL 1).subgroupOf 𝒮ℒ, (0 : ℂ) := by
    rw [Finset.prod_const, zero_pow]
    simp [Finset.card_univ, Fintype.card_ne_zero]
  rw [Finset.prod_fn, hzero]
  exact tendsto_finsetProd _ fun q _ => quotientFunc_level_one_isZeroAtImInfty f q

/-- **`S₂(Γ₀(1)) = 0`** — every weight-2 cusp form on `Γ₀(1)` (i.e. on
`SL(2, ℤ)`) vanishes identically: its norm to level 1 is a weight-2
level-1 form vanishing at `i∞`, killed by the level-1 Sturm bound
(`2/12 = 0`). -/
theorem cuspForm_level_one_coe_eq_zero (f : CuspForm (Gamma0GL 1) 2) : ⇑f = 0 := by
  by_contra hf
  refine ModularForm.norm_ne_zero 𝒮ℒ hf ?_
  apply sturm_bound_levelOne
  have hcoeff0 : (qExpansion 1 ⇑(ModularForm.norm 𝒮ℒ f)).coeff 0 = 0 := by
    rw [qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
    exact (norm_level_one_isZeroAtImInfty f).valueAtInfty_eq_zero
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at hcoeff0
  have horder : 1 ≤ (qExpansion 1 ⇑(ModularForm.norm 𝒮ℒ f)).order :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hcoeff0
  have hwt : ((2 * (Nat.card (𝒮ℒ ⧸ (Gamma0GL 1).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12) = 0 := by
    rw [show Nat.card (𝒮ℒ ⧸ (Gamma0GL 1).subgroupOf 𝒮ℒ) = 1 from Gamma0GL_one_relIndex]
    decide
  rw [hwt]
  exact lt_of_lt_of_le (by norm_num) horder

end LevelOneEmptiness

end GaloisRepresentation.Modularity
