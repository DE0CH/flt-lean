/-
Modularity/Interface.lean — own work for the Fermat project (not
vendored from the FLT project).

# The modularity interface: weight-2 eigenforms and their eigensystems

This file opens the MODULARITY SUBTREE: it provides the minimal sound
vocabulary needed to state, on this mathlib pin, that the eigensystem
of a hardly ramified `p`-adic Galois representation "comes from a
weight-2 cuspidal Hecke eigenform", together with the sorried automorphy
statements that the three modular-forms-blocked atoms of
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Family.lean` consume:

* `exists_finiteDimensional_trace_field_of_isIrreducible`,
* `exists_hardlyRamified_ringOfIntegers_realizations`,
* `exists_realization_at_two_generated`.

## Design (SOUNDNESS AUDIT, 2026-07-23)

The pin has analytic modular forms (`CuspForm`, congruence subgroups,
`q`-expansions) but NO Hecke operators, eigenforms, or attached Galois
representations. The carrier chosen here is therefore the
**coefficient characterization** of a normalized Hecke eigenform,
Diamond–Shurman *A First Course in Modular Forms* Proposition 5.8.5
(weight `k = 2`, trivial character): a normalized cusp form
`f = Σ aₙ qⁿ ∈ S₂(Γ₀(N))` is an eigenform for the FULL Hecke algebra
(all `Tₙ`, including the bad `U_q`, `q ∣ N`) if and only if

* `a₁ = 1`,
* `a_{mn} = a_m a_n` for coprime `m, n`,
* `a_{q^{r+2}} = a_q a_{q^{r+1}} − q · a_{q^r}` for primes `q ∤ N`,
* `a_{q^{r+1}} = a_q a_{q^r}` for primes `q ∣ N`.

This makes `IsWeightTwoEigenform` a REAL definition on the pin's actual
`CuspForm` type — no opaque carrier, nothing sorried in a definition —
and it is exactly inhabited by the classical normalized eigenforms:

* every newform satisfies it (Diamond–Shurman Theorem 5.8.2 +
  Proposition 5.8.5), so the intended modularity construction can
  inhabit it; and
* conversely every inhabitant IS a normalized full-Hecke eigenform
  (the other direction of 5.8.5), whose good-prime eigensystem arises
  from a newform of level dividing `N` — its conductor (Diamond–Shurman
  Proposition 5.8.4, via Strong Multiplicity One; Galois conjugates of
  newforms are newforms, Theorem 6.5.4), so the sorried attachment statements
  below quantify only over forms for which the classical theory
  genuinely provides attached Galois representations. The FULL set of
  relations (not just the good-prime ones) is deliberate: good-prime
  relations alone do not pin the bad coefficients and would let
  oldform-contaminated non-eigenforms inhabit the carrier, pushing an
  unproven eigensystem-rigidity argument into every attachment sorry.

The two attachment sorries are stated at level `N = 2` exactly: the
classical route (Wiles–Taylor–Wiles / Skinner–Wiles modularity plus
Ribet level lowering; equivalently the "hardly ramified ⇒ automorphic
of level `U₁({2})`" formulation of the FLT blueprint) produces from an
IRREDUCIBLE hardly ramified representation an eigenform of level
`Γ₀(2)` and weight `2` — Serre's conductor-2/weight-2 conditions
(Serre, Duke 1987, §4.1). Restricting the attachment statements to
level 2 is what makes them SOUND for every inhabitant: at level 2 the
attached `λ`-adic representations of the underlying newform (of level
dividing 2) are unramified outside `{2, ℓ}` and flat at odd `ℓ` — the
hardly ramified shape — whereas at a general level a wildly-ramified
inhabitant would falsify the hardly-ramifiedness clause of the odd-`ℓ`
attachment. (Since `S₂(Γ₀(2)) = 0` — the genus of `X₀(2)` is zero —
these level-2 statements are also reachable through the
dimension-formula route; see the DECOMPOSITION PLAN below.)

The REDUCIBLE branch of the three atoms does not run through cusp forms
at all (the eigensystem of a reducible hardly ramified representation
is the Eisenstein system `{1, χ_cyc}`, which no cusp form matches);
it is split off as separate sorried leaves
`*_of_not_isIrreducible` in `Family.lean` next to the atoms.

## DECOMPOSITION PLAN (next rounds of dispatches)

1. **Hecke action** (Diamond–Shurman ch. 5): define the double-coset
   operators `Tₙ` on `S₂(Γ₀(N))` on the pin's `CuspForm` (the abstract
   `Mathlib.NumberTheory.HeckeRing.Defs` double-coset modules carry no
   action on modular forms and no ring product on the pin — audited
   2026-07-23, wrong abstraction to build on); prove the
   `q`-expansion formulas `a_m(Tₙ f) = Σ_{d ∣ (m,n), (d,N)=1} d·a_{mn/d²}(f)`
   and derive Proposition 5.8.5 connecting eigenvectors to
   `IsWeightTwoEigenform`. STARTED (2026-07-24): the prime-index
   weight-2 slash-sum `heckeTransform` (with explicit coset
   representatives `heckeRep`/`heckeRepInf`) is defined below; its
   stability on cusp forms (`exists_cuspForm_heckeTransform`, via the
   `CuspForm.trace` identification) and its coefficient formula
   (`qExpansion_heckeTransform_coeff`, via `hasSum_qExpansion` and
   `qExpansion_coeff_unique`) are PROVEN (2026-07-24); the eigenform
   side of Proposition 5.8.5 at prime index is PROVEN
   (`hecke_eigen_coeff_identity`).
2. **Hecke field finiteness** (`heckeField_finiteDimensional`;
   Diamond–Shurman §6.5): the Hecke algebra preserves the integral
   homology lattice of `X₀(N)` (equivalently: `S₂(Γ₀(N))` has a basis
   of forms with integer coefficients and the eigenvalues are algebraic
   integers of degree ≤ dim), so the coefficients of an eigenform
   generate a number field.
3. **Dimension zero at level 2 — DONE (2026-07-23)**: `S₂(Γ₀(2)) = 0`
   is proven below (`cuspForm_level_two_coe_eq_zero`, via the norm to
   level 1, the index computation `[SL(2,ℤ) : Γ₀(2)] = 3`, and
   mathlib's level-1 Sturm bound — no `X₀(2)` geometry needed);
   together with `a₁ = 1 ≠ 0` (`weightTwoEigenform_level_two_false`)
   this DISCHARGES the two level-2 attachment statements
   (`exists_ringOfIntegers_realizations_of_weightTwoEigenform` in
   `Family.lean`, `exists_realization_at_two_of_weightTwoEigenform`
   here) by contradiction — their alternative, non-vacuous route
   (Eichler–Shimura/Deligne plus Carayol/Saito) is not needed.
4. **The residual modularity sorries** `exists_weightTwoEigenform_*`
   below (Wiles–Taylor–Wiles + Skinner–Wiles + Ribet, per the FLT
   blueprint's hardly-ramified formulation) — DECOMPOSED (2026-07-24)
   into five classical pillars (see the section "The classical pillars
   behind the two modularity sorries"): residual reduction, residual
   modularity (weak Serre / Khare–Wintenberger; at `ℓ = 3`
   dischargeable from `ModThree`), modularity lifting (R = T,
   residually irreducible case), the Skinner–Wiles residually
   reducible branch, and level optimization to `Γ₀(2)`
   (Carayol/Ribet). Both former sorries are now proven assemblies
   over those pillars. Pillar 3 (modularity lifting) was further
   decomposed (2026-07-24) into the Taylor–Wiles cut — the Hecke-side
   hardly ramified deformation 3a, the patching statement `R = 𝕋` 3b,
   and the modular-points leaf 3c (see the section "The Taylor–Wiles
   cut behind the modularity-lifting pillar") — and is itself now a
   proven assembly.
5. **Eisenstein branch** (`*_of_not_isIrreducible` in `Family.lean`):
   from the proven reducibility analysis
   (`exists_char_charpoly_map_eq_of_not_isIrreducible`) and the
   character-pair node, the eigensystem degenerates to
   `(X − 1)(X − q)`; realize it by the explicit representation
   `1 ⊕ χ_cyc,ℓ` over `ℤ_ℓ` (odd `ℓ`) resp. over the given `K`
   (`ℓ = 2`), whose hardly-ramifiedness is a direct check (flat:
   `μ_{ℓ^∞} × ℚ_ℓ/ℤ_ℓ`; tame at 2: unramified).
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.Data.Matrix.Mul
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Topology.Algebra.IntermediateField
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- Dual-space machinery for the rational-spanning descent
-- (`cuspForm_mem_span_rational`): the Sturm coefficient functionals
-- span the dual, a dual basis is extracted, and `Aut(ℂ)`-stability
-- forces its coordinates into the fixed field `ℚ`.
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
-- Field theory for the fixed-field computation
-- (`exists_ratCast_eq_of_forall_ringEquiv_fixed`): transcendence
-- bases, extension of subfield automorphisms through
-- `IsAlgClosure.equivOfEquiv`, the relative algebraic closure
-- `ℚ̄ ⊆ ℂ`, and conjugate-root embeddings.
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic
-- Finite commutative algebra for the pillar-3c point factorization
-- (proof-body use only, consumed by the proven assembly of
-- `exists_weightTwoEigenform_of_heckeDeformation_point`): the kernel
-- of a `ℚ̄_ℓ`-point is a prime of the local coefficient ring, the
-- quotient is a local domain, module-finite and torsion-free — hence
-- free — over the DVR `ℤ_ℓ`: an order in an `ℓ`-adic field.
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.NumberTheory.Padics.PadicIntegers
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Residual
-- `IsHardlyRamified.exists_residual_odd`, discharging the residual
-- reduction pillar `exists_residual_isHardlyRamified_odd` below
-- ℓ = 3 discharge of the residual-modularity pillar: an irreducible
-- hardly ramified mod-3 representation does not exist
-- (`IsHardlyRamified.mod_three_reducible`, the Fontaine/Odlyzko route),
-- so the ℓ = 3 instance holds by contradiction. Proof-body use only.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree
-- `Slop.OddRep.isIrreducible_iff_forall`, the elementary unpacking of
-- `Representation.IsIrreducible` (stable-submodule form), used to turn
-- `mod_three_reducible`'s stable submodule into `¬ IsIrreducible`.
import Fermat.FLT.Slop.RepresentationTheory.OddAbsIrredSlop
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
-- `IsHardlyRamified.mod_three` and the global triangular form
-- `exists_global_triangular_of_residual_trivial_quotient`, discharging
-- the `p = 3` instance of the residually reducible pillar below
-- `LinearMap.charpoly_baseChange`, for the `charFrob`/base-change
-- bridge of the conductor cut below
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- `globalFrob`, `dense_conjClasses_globalFrob`,
-- `exists_prime_toHeightOneSpectrum`,
-- `charFrob_eq_charpoly_globalFrob` and
-- `cyclotomicCharacter_globalFrob`: consumed by the determinant
-- normalization of the conductor cut and the Chebotarev-density
-- trace-gluing step of the Carayol cut behind pillar 3a (proof
-- bodies only)
-- PUBLIC since 2026-07-24: `globalFrob` appears in the SIGNATURES of
-- the Eichler–Shimura interface (`EichlerShimuraPackage.congruence`,
-- `det_frob`), not only in proof bodies.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- The Khare–Wintenberger cut (Family-free by construction): the
-- headline nonexistence theorem
-- `not_isIrreducible_of_isHardlyRamified_of_five_le` discharging the
-- `ℓ ≥ 5` residual-modularity leaf by contradiction. Proof-body use
-- only.
import Fermat.FLT.Modularity.KhareWintenberger
-- The deformation-theoretic pillars behind the Taylor–Wiles patching
-- statement 3b (Mazur representability, Carayol surjectivity,
-- Taylor–Wiles injectivity) and the `charFrob`/base-change bridge.
-- Proof-body use only (the 3b assembly).
import Fermat.FLT.Modularity.Patching

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain

open scoped MatrixGroups

universe u v

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

/-- **The Hecke field** of a weight-2 level-`N` cusp form: the subfield
of `ℂ` generated over `ℚ` by all `q`-expansion coefficients. For an
eigenform this is the classical Hecke field `K_f = ℚ({aₙ})`
(Diamond–Shurman §6.5), a number field — that finiteness is the sorried
`heckeField_finiteDimensional` below, not baked into the definition. -/
noncomputable def heckeField (N : ℕ) (f : CuspForm (Gamma0GL N) 2) :
    IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (qCoeff N f))

/-- The `n`-th coefficient `aₙ(f)`, seen inside the Hecke field (it is
a generator of `heckeField N f` by construction). -/
noncomputable def heckeCoeff (N : ℕ) (f : CuspForm (Gamma0GL N) 2) (n : ℕ) :
    heckeField N f :=
  ⟨qCoeff N f n, IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩⟩

/-- **Eigensystem matching**: the cusp form `f` matches the abstract
eigensystem `(E, S, Pv)` (a number-field-coefficient family of would-be
Frobenius characteristic polynomials, as produced by
`exists_numberField_eigensystem` in `Family.lean`) if some embedding
`ι : E →+* ℂ` carries `Pv` at each good place `v = (q)`, `q ∤ N`,
`v ∉ S`, to the Hecke polynomial `X² − a_q(f)·X + q` of `f`. This is
the precise sense in which "the eigensystem comes from the eigenform
`f`". -/
def MatchesEigensystem (N : ℕ) (f : CuspForm (Gamma0GL N) 2)
    {E : Type v} [Field E]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E) :
    Prop :=
  ∃ ι : E →+* ℂ, ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S → ¬ q ∣ N →
    (Pv hq.toHeightOneSpectrumRingOfIntegersRat).map ι =
      Polynomial.X ^ 2 - Polynomial.C (qCoeff N f q) * Polynomial.X +
        Polynomial.C (q : ℂ)

/-! ### `S₂(Γ₀(2)) = 0`: the dimension-formula discharge route

DECOMPOSITION PLAN item 3, executed (2026-07-23): there is no nonzero
weight-2 cusp form on `Γ₀(2)` (classically: the genus of `X₀(2)` is 0).
The Lean argument avoids the geometry of `X₀(2)` entirely:

* the norm of `f ∈ S₂(Γ₀(2))` over `SL(2, ℤ)` — the product of the
  translates `f ∣[2] r⁻¹` over the cosets `r` of `Γ₀(2)` in `SL(2, ℤ)`
  (mathlib's `ModularForm.norm`) — is a LEVEL-1 modular form of weight
  `2 · [SL(2,ℤ) : Γ₀(2)] = 6`;
* every factor vanishes at `i∞` (a cusp form vanishes at every cusp of
  its arithmetic group), so the norm does too; hence the constant term
  of its `q`-expansion vanishes and the expansion has positive order;
* the level-1 Sturm bound (mathlib's `sturm_bound_levelOne`; for
  weight 6 the bound is `6/12 = 0`) then forces the norm to vanish,
  while a nonzero `f` has nonzero norm (`ModularForm.norm_ne_zero`) —
  contradiction, so `f = 0` as a function;
* finally a normalized eigenform has `a₁ = 1 ≠ 0`, refuting `f = 0`.

The index `[SL(2,ℤ) : Γ₀(2)] = 3` is computed through the mod-2
reduction: `Γ₀(2)` is the preimage of the Borel subgroup of
`SL(2, 𝔽₂)` (order 2 inside a group of order 6, so index 3), and the
reduction map is surjective — witnessed by six explicit integral lifts,
one per element of `SL(2, 𝔽₂)`, checked by `decide`. -/

section LevelTwoEmptiness

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup

/-- The "Borel" subgroup of `SL(2, ℤ/2)`: matrices whose lower-left
entry vanishes. `Γ₀(2)` is its preimage under reduction mod 2; it has
order 2 inside the order-6 group `SL(2, ℤ/2)`, giving index 3. -/
def borelZModTwo : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) where
  carrier := { g | g.1 1 0 = 0 }
  one_mem' := by decide
  mul_mem' {a b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    simp [h, ha, hb]
  inv_mem' {a} ha := by
    simpa [Matrix.SpecialLinearGroup.SL2_inv_expl a] using ha

instance : DecidablePred (· ∈ borelZModTwo) :=
  fun g => inferInstanceAs (Decidable (g.1 1 0 = 0))

/-- Explicit integral lifts of the six elements of `SL(2, ℤ/2)`,
witnessing surjectivity of the reduction map `SL(2, ℤ) → SL(2, ℤ/2)`
(so that comapping `borelZModTwo` preserves the index). -/
def sl2zModTwoLift : Fin 6 → Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ![⟨!![1, 0; 0, 1], by decide⟩, ⟨!![0, -1; 1, 0], by decide⟩,
    ⟨!![1, 1; 0, 1], by decide⟩, ⟨!![1, 0; 1, 1], by decide⟩,
    ⟨!![0, -1; 1, 1], by decide⟩, ⟨!![1, 1; -1, 0], by decide⟩]

/-- `[SL(2, ℤ) : Γ₀(2)] = 3`: `Γ₀(2)` is the comap of the index-3
Borel subgroup of `SL(2, ℤ/2)` along the (surjective) reduction map. -/
theorem Gamma0_two_index : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod 2))) := by
    intro b
    have h : ∃ i : Fin 6,
        Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod 2))
          (sl2zModTwoLift i) = b := by
      revert b; decide
    obtain ⟨i, hi⟩ := h
    exact ⟨sl2zModTwoLift i, hi⟩
  have hcomap : CongruenceSubgroup.Gamma0 2 =
      borelZModTwo.comap (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))) := by
    ext g
    simp [borelZModTwo, CongruenceSubgroup.Gamma0_mem, Subgroup.mem_comap]
  have hidx : borelZModTwo.index = 3 := by
    have h1 : borelZModTwo.index * Nat.card borelZModTwo
        = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
      borelZModTwo.index_mul_card
    have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h3 : Nat.card borelZModTwo = 2 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [h2, h3] at h1
    omega
  rw [hcomap, Subgroup.index_comap_of_surjective _ hsurj, hidx]

/-- The relative index of `Γ₀(2)` in `SL(2, ℤ)`, both viewed in
`GL(2, ℝ)`, is 3 — the `mapGL`-transport of `Gamma0_two_index`. This
number is the coset count in the norm construction below, hence the
factor turning weight 2 into weight `2 · 3 = 6` at level 1. -/
theorem Gamma0GL_two_relIndex : (Gamma0GL 2).relIndex 𝒮ℒ = 3 := by
  show ((CongruenceSubgroup.Gamma0 2).map (mapGL ℝ)).relIndex 𝒮ℒ = 3
  rw [MonoidHom.range_eq_map, ← Subgroup.relIndex_comap,
    Subgroup.comap_map_eq_self_of_injective mapGL_injective,
    Subgroup.relIndex_top_right, Gamma0_two_index]

/-- Every `SL(2, ℤ)`-translate `f ∣[2] r⁻¹` of a weight-2 cusp form on
`Γ₀(2)` vanishes at `i∞`: `r⁻¹ • ∞` is a cusp of the arithmetic group
`Γ₀(2)`, and cusp forms vanish at every cusp. These are exactly the
factors of the norm form. -/
theorem quotientFunc_isZeroAtImInfty (f : CuspForm (Gamma0GL 2) 2)
    (q : 𝒮ℒ ⧸ (Gamma0GL 2).subgroupOf 𝒮ℒ) :
    IsZeroAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    rw [SlashInvariantForm.quotientFunc_mk]
    have hinf : IsCusp OnePoint.infty 𝒮ℒ := isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩
    have hcusp : IsCusp ((r.val)⁻¹ • OnePoint.infty) (Gamma0GL 2) :=
      (hinf.smul_of_mem (inv_mem r.2)).of_isFiniteRelIndex
    exact CuspFormClass.zero_at_cusps f hcusp _ rfl

/-- The norm (over `SL(2, ℤ)`) of a weight-2 cusp form on `Γ₀(2)`
vanishes at `i∞`: it is a finite product of translates, each of which
vanishes there by `quotientFunc_isZeroAtImInfty`. -/
theorem norm_isZeroAtImInfty (f : CuspForm (Gamma0GL 2) 2) :
    IsZeroAtImInfty ⇑(ModularForm.norm 𝒮ℒ f) := by
  rw [ModularForm.coe_norm]
  letI := Fintype.ofFinite (𝒮ℒ ⧸ (Gamma0GL 2).subgroupOf 𝒮ℒ)
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  have hzero : (0 : ℂ) = ∏ _q : 𝒮ℒ ⧸ (Gamma0GL 2).subgroupOf 𝒮ℒ, (0 : ℂ) := by
    rw [Finset.prod_const, zero_pow]
    simp [Finset.card_univ, Fintype.card_ne_zero]
  rw [Finset.prod_fn, hzero]
  exact tendsto_finsetProd _ fun q _ => quotientFunc_isZeroAtImInfty f q

/-- The `q`-expansion of the zero function vanishes identically (its
cusp function is the zero function, whose Taylor coefficients at `0`
all vanish). Used to turn `⇑f = 0` into `a₁(f) = 0`. -/
theorem qExpansion_zero_fn_coeff (h : ℝ) (n : ℕ) :
    (UpperHalfPlane.qExpansion h (0 : ℍ → ℂ)).coeff n = 0 := by
  rw [UpperHalfPlane.qExpansion_coeff]
  have hc : cuspFunction h (0 : ℍ → ℂ) = fun _ => (0 : ℂ) := by
    unfold UpperHalfPlane.cuspFunction
    have h0 : ((0 : ℍ → ℂ) ∘ ofComplex) = fun _ => (0 : ℂ) := rfl
    rw [h0]
    unfold Function.Periodic.cuspFunction
    have h1 : ((fun _ => (0 : ℂ)) ∘ Function.Periodic.invQParam h)
        = fun _ => (0 : ℂ) := rfl
    rw [h1, Filter.Tendsto.limUnder_eq tendsto_const_nhds]
    simp
  rw [hc]
  simp [iteratedDeriv]

/-- **`S₂(Γ₀(2)) = 0`** — every weight-2 cusp form on `Γ₀(2)` vanishes
identically. Proof: its norm to level 1 is a weight-6 level-1 form
vanishing at `i∞` (positive `q`-expansion order), so the level-1 Sturm
bound kills the norm; a nonzero form has nonzero norm. -/
theorem cuspForm_level_two_coe_eq_zero (f : CuspForm (Gamma0GL 2) 2) : ⇑f = 0 := by
  by_contra hf
  refine ModularForm.norm_ne_zero 𝒮ℒ hf ?_
  apply sturm_bound_levelOne
  have hcoeff0 : (qExpansion 1 ⇑(ModularForm.norm 𝒮ℒ f)).coeff 0 = 0 := by
    rw [qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
    exact (norm_isZeroAtImInfty f).valueAtInfty_eq_zero
  rw [PowerSeries.coeff_zero_eq_constantCoeff] at hcoeff0
  have horder : 1 ≤ (qExpansion 1 ⇑(ModularForm.norm 𝒮ℒ f)).order :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hcoeff0
  have hwt : ((2 * (Nat.card (𝒮ℒ ⧸ (Gamma0GL 2).subgroupOf 𝒮ℒ) : ℤ)).toNat / 12) = 0 := by
    rw [show Nat.card (𝒮ℒ ⧸ (Gamma0GL 2).subgroupOf 𝒮ℒ) = 3 from Gamma0GL_two_relIndex]
    decide
  rw [hwt]
  exact lt_of_lt_of_le (by norm_num) horder

/-- **There is no weight-2 level-2 normalized eigenform**: the carrier
`IsWeightTwoEigenform 2` is empty, since `S₂(Γ₀(2)) = 0` while a
normalized eigenform has `a₁ = 1`. This discharges both level-2
attachment statements (`exists_realization_at_two_of_weightTwoEigenform`
below and `exists_ringOfIntegers_realizations_of_weightTwoEigenform` in
`Family.lean`) by contradiction — the dimension-formula route of the
DECOMPOSITION PLAN. -/
theorem weightTwoEigenform_level_two_false (f : CuspForm (Gamma0GL 2) 2)
    (hf : IsWeightTwoEigenform 2 f) : False := by
  have h1 := hf.qCoeff_one
  rw [qCoeff, cuspForm_level_two_coe_eq_zero f, qExpansion_zero_fn_coeff] at h1
  exact one_ne_zero h1.symm

/-! #### The level-1 companion: `S₂(Γ₀(1)) = 0`

Added 2026-07-24 for the conductor leaf
`exists_eigenform_level_dvd_two_of_trace_eq` below, whose conclusion
produces an eigenform of level `M ∣ 2` — i.e. `M = 1` or `M = 2`. The
`M = 2` branch is refuted by `weightTwoEigenform_level_two_false`
above; the `M = 1` branch needs the (classical, easier) level-1
vanishing `S₂(SL(2, ℤ)) = 0`, proven here by the same norm/Sturm
route with relative index `1` in place of `3` (weight stays
`2·1 = 2 < 12`, so the level-1 Sturm bound is again `0`). -/

/-- `Γ₀(1) = SL(2, ℤ)`: the mod-1 congruence condition is vacuous
(`ZMod 1` is trivial). -/
theorem Gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext g
  simp [CongruenceSubgroup.Gamma0_mem, Subsingleton.elim (g.1 1 0 : ZMod 1) 0]

/-- The relative index of `Γ₀(1)` in `SL(2, ℤ)` (both viewed in
`GL(2, ℝ)`) is `1`: `Γ₀(1)` IS `SL(2, ℤ)`. The level-1 analogue of
`Gamma0GL_two_relIndex`. -/
theorem Gamma0GL_one_relIndex : (Gamma0GL 1).relIndex 𝒮ℒ = 1 := by
  show ((CongruenceSubgroup.Gamma0 1).map (mapGL ℝ)).relIndex 𝒮ℒ = 1
  rw [Gamma0_one_eq_top, ← MonoidHom.range_eq_map, Subgroup.relIndex_self]

/-- Every `SL(2, ℤ)`-translate of a weight-2 cusp form on `Γ₀(1)`
vanishes at `i∞` — the level-1 analogue of
`quotientFunc_isZeroAtImInfty`. -/
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
vanishes at `i∞` — the level-1 analogue of `norm_isZeroAtImInfty`. -/
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
(`2/12 = 0`). Level-1 analogue of `cuspForm_level_two_coe_eq_zero`. -/
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

/-- **There is no weight-2 level-1 normalized eigenform**: the carrier
`IsWeightTwoEigenform 1` is empty, since `S₂(Γ₀(1)) = 0` while a
normalized eigenform has `a₁ = 1`. Level-1 analogue of
`weightTwoEigenform_level_two_false`; together they refute both
branches `M ∈ {1, 2}` of the conductor leaf
`exists_eigenform_level_dvd_two_of_trace_eq` below. -/
theorem weightTwoEigenform_level_one_false (f : CuspForm (Gamma0GL 1) 2)
    (hf : IsWeightTwoEigenform 1 f) : False := by
  have h1 := hf.qCoeff_one
  rw [qCoeff, cuspForm_level_one_coe_eq_zero f, qExpansion_zero_fn_coeff] at h1
  exact one_ne_zero h1.symm

end LevelTwoEmptiness

/-! ### Hecke field finiteness: the single-finite-structure argument

DECOMPOSITION PLAN item 2, executed (2026-07-24), with the former
single geometric leaf `exists_heckeMatrix_eigenvector` DECOMPOSED
(2026-07-24, second round) along the analytic route of DECOMPOSITION
PLAN item 1. `heckeField_finiteDimensional` below is Diamond–Shurman
Theorem 6.5.1: the coefficients of a normalized weight-2 eigenform
generate a number field. The classical proof pivots on ONE finite
object: a Hecke-stable finite rational structure on `S₂(Γ₀(N))`. On
this pin neither Hecke operators on `CuspForm`, nor the modular curve,
nor even finite-dimensionality of `CuspForm (Gamma0GL N) 2` exist
(audited 2026-07-24: only the level-1 space carries a
`FiniteDimensional` instance, from the level-1 dimension formula;
`~/cs/FLT`'s Hecke material is quaternionic-automorphic, not connected
to the pin's analytic cusp forms). The Hecke action is therefore BUILT
here (the weight-2 slash-sum operator `heckeTransform`, over the
explicit coset representatives `heckeRep`/`heckeRepInf` of the
`q`-isogeny matrices), and `exists_heckeMatrix_eigenvector` is now a
PROVEN assembly over three sharply-stated leaves, of which the first
two are PROVEN (2026-07-24) and one remains sorried:

* `exists_cuspForm_heckeTransform` (PROVEN) — `T_q` preserves
  `S₂(Γ₀(N))` (Diamond–Shurman Propositions 5.1.5/5.2.1; here via the
  `CuspForm.trace` of the `α`-translate over the arithmetic conjugate
  group, with the coset space enumerated through the divisibility
  criterion `heckeRep_conj_mem_iff`);
* `qExpansion_heckeTransform_coeff` (PROVEN) — the classical
  coefficient formula
  `a_m(T_q f) = a_{qm}(f) + 1_{q ∤ N} · q · a_{m/q}(f)`
  (Diamond–Shurman Proposition 5.2.2 at weight 2; via
  `hasSum_qExpansion`, the additive character sum, and
  `qExpansion_coeff_unique`);
* `cuspForm_mem_span_rational` — the forms with rational
  `q`-expansions span `S₂(Γ₀(N))` (the rational structure;
  Diamond–Shurman §6.5, Shimura, *Introduction to the Arithmetic
  Theory*, Theorem 3.52). Finite dimensionality of `S₂(Γ₀(N))` and
  the general-level Sturm bound are PROVEN (2026-07-24,
  `exists_cuspForm_sturm_bound`/`cuspForm_finiteDimensional`), so the
  former leaf `exists_rational_qExpansion_basis` is now a proven
  assembly. `cuspForm_mem_span_rational` itself is now a PROVEN
  Galois-descent assembly (2026-07-24) whose single remaining sorried
  leaf is the arithmetic `Aut(ℂ)`-stability of the `q`-expansion image
  (`exists_cuspForm_ringEquiv_conj`, Shimura's rationality theorem);
  the field-theoretic fixed-field computation
  (`exists_ratCast_eq_of_forall_ringEquiv_fixed`) is PROVEN.

Everything else is proven:

* `exists_finiteDimensional_subalgebra_of_matrix_eigenvector` — the
  linear-algebra core: the simultaneous eigenvalues, on one common
  eigenvector, of any family of matrices with RATIONAL entries all lie
  in a single finite-dimensional `ℚ`-subalgebra of `ℂ` (the image of
  the generated matrix algebra under the eigenvalue character). This
  is the "single finite structure" argument: each `a_q` being
  individually algebraic would NOT bound `ℚ({a_q : q prime})`.
* `qCoeff_zero` and `qCoeff_mem_of_forall_prime_mem` — the eigenform
  recursions push membership in any `ℚ`-subalgebra from the prime
  coefficients to ALL coefficients: `a₀ = 0` (cusp vanishing),
  `a₁ = 1`, prime powers by the two Hecke recursions, composites by
  multiplicativity. This is the designated consumer of the four
  `IsWeightTwoEigenform` accessor fields.
* `heckeField_finiteDimensional` — assembly: the coefficient range
  lies in the finite-dimensional subalgebra, hence consists of
  elements integral over `ℚ`, so `heckeField N f` coincides with the
  algebra adjoin and inherits finite-dimensionality.
-/

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

/-- A trivial intersection of countably many subspaces of a
finite-dimensional space is trivial on a finite subfamily (finrank
descent). Feeds the finite-coordinate selection in
`exists_finset_restrict_linearIndependent`. -/
theorem exists_finset_iInf_eq_bot {k : ℕ} (W : ℕ → Submodule ℚ (Fin k → ℚ))
    (hW : (⨅ m, W m) = ⊥) :
    ∃ T : Finset ℕ, (⨅ m ∈ T, W m) = ⊥ := by
  classical
  suffices h : ∀ (d : ℕ) (T : Finset ℕ),
      Module.finrank ℚ ↥(⨅ m ∈ T, W m) ≤ d →
      ∃ T' : Finset ℕ, (⨅ m ∈ T', W m) = ⊥ by
    exact h (Module.finrank ℚ ↥(⨅ m ∈ (∅ : Finset ℕ), W m)) ∅ le_rfl
  intro d
  induction d with
  | zero =>
    intro T hT
    exact ⟨T, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hT)⟩
  | succ d ih =>
    intro T hT
    by_cases hbot : (⨅ m ∈ T, W m) = ⊥
    · exact ⟨T, hbot⟩
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      have hxall : ¬ ∀ m, x ∈ W m := fun hall =>
        hx0 (by simpa [hW] using (Submodule.mem_iInf W).mpr hall)
      obtain ⟨m₀, hm₀⟩ := not_forall.mp hxall
      refine ih (insert m₀ T) ?_
      have hlt : (⨅ m ∈ insert m₀ T, W m) < ⨅ m ∈ T, W m := by
        rw [Finset.iInf_insert]
        refine lt_of_le_of_ne inf_le_right fun heq => hm₀ ?_
        exact (heq.symm.le.trans inf_le_left) hx
      exact Nat.lt_succ_iff.mp
        (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hT)

/-- A `ℚ`-linearly independent finite family of rational sequences
stays independent after restriction to a suitable FINITE set of
coordinates (via the kernel intersection of the coordinate
functionals and `exists_finset_iInf_eq_bot`). This is the bridge to
mathlib's finite-coordinate base-change lemma
`linearIndependent_algebraMap_comp_iff`. -/
theorem exists_finset_restrict_linearIndependent {k : ℕ} {w : Fin k → ℕ → ℚ}
    (hw : LinearIndependent ℚ w) :
    ∃ T : Finset ℕ, LinearIndependent ℚ fun i => fun m : T => w i m := by
  classical
  set φ : ℕ → ((Fin k → ℚ) →ₗ[ℚ] ℚ) := fun m =>
    { toFun := fun c => ∑ i, c i * w i m
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun s a => by simp [Finset.mul_sum, mul_assoc] } with hφ
  have hker : (⨅ m, LinearMap.ker (φ m)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    rw [Submodule.mem_iInf] at hc
    have hc' : ∑ i, c i • w i = 0 := by
      funext m
      have hcm := hc m
      rw [LinearMap.mem_ker] at hcm
      simpa [hφ, Finset.sum_apply] using hcm
    exact funext (Fintype.linearIndependent_iff.mp hw c hc')
  obtain ⟨T, hT⟩ := exists_finset_iInf_eq_bot _ hker
  refine ⟨T, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcT : c ∈ ⨅ m ∈ T, LinearMap.ker (φ m) := by
    rw [Submodule.mem_iInf]
    intro m
    rw [Submodule.mem_iInf]
    intro hmT
    rw [LinearMap.mem_ker]
    have := congrFun hc ⟨m, hmT⟩
    simpa [hφ, Finset.sum_apply] using this
  rw [hT, Submodule.mem_bot] at hcT
  intro i
  exact congrFun hcT i

/-- **Base change for sequences**: a `ℚ`-linearly independent family
of rational sequences is `ℂ`-linearly independent after coercion.
Proven by restricting to a finite coordinate window
(`exists_finset_restrict_linearIndependent`), applying mathlib's
finite-coordinate `linearIndependent_algebraMap_comp_iff`, and
pulling back along the restriction map. -/
theorem linearIndependent_ratCast_of_linearIndependent {k : ℕ}
    {w : Fin k → ℕ → ℚ} (hw : LinearIndependent ℚ w) :
    LinearIndependent ℂ fun i => fun m : ℕ => (w i m : ℂ) := by
  obtain ⟨T, hT⟩ := exists_finset_restrict_linearIndependent hw
  have hTc : LinearIndependent ℂ fun i => algebraMap ℚ ℂ ∘ (fun m : T => w i m) :=
    linearIndependent_algebraMap_comp_iff.mpr hT
  refine LinearIndependent.of_comp
    (LinearMap.funLeft ℂ ℂ (Subtype.val : T → ℕ)) ?_
  have heq : (LinearMap.funLeft ℂ ℂ (Subtype.val : T → ℕ) ∘
      fun i => fun m : ℕ => (w i m : ℂ))
      = fun i => algebraMap ℚ ℂ ∘ (fun m : T => w i m) := by
    funext i m
    simp [LinearMap.funLeft, eq_ratCast]
  rw [heq]
  exact hTc

/-- **Rationality of coordinates**: if finitely many rational
sequences are `ℂ`-independent (after coercion) and a COMPLEX linear
combination of them is again a rational sequence, the coefficients
are rational. The classical content: a rational vector lying in the
`ℂ`-span of independent rational vectors already lies in their
`ℚ`-span (else `Fin.cons` extension plus base change contradicts the
span membership), and independence matches the two coordinate
systems. -/
theorem exists_ratCast_coords {k : ℕ} {w : Fin k → ℕ → ℚ} {b : Fin k → ℂ}
    {u : ℕ → ℚ}
    (hw : LinearIndependent ℂ fun i => fun m : ℕ => (w i m : ℂ))
    (hu : ∀ m : ℕ, ∑ i, b i * (w i m : ℂ) = (u m : ℂ)) :
    ∃ c : Fin k → ℚ, ∀ i, b i = (c i : ℂ) := by
  classical
  have hwq : LinearIndependent ℚ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hcc : ∑ j, ((c j : ℂ)) • (fun m : ℕ => (w j m : ℂ)) = 0 := by
      funext m
      have hcm := congrFun hc m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcm ⊢
      exact_mod_cast congrArg (Rat.cast (K := ℂ)) hcm
    exact_mod_cast Fintype.linearIndependent_iff.mp hw _ hcc i
  have humem : u ∈ Submodule.span ℚ (Set.range w) := by
    by_contra hnot
    have hcons : LinearIndependent ℚ (Fin.cons u w : Fin (k + 1) → ℕ → ℚ) :=
      linearIndependent_finCons.mpr ⟨hwq, hnot⟩
    have hconsC := linearIndependent_ratCast_of_linearIndependent hcons
    have hconseq :
        (fun i => fun m : ℕ => ((Fin.cons u w : Fin (k + 1) → ℕ → ℚ) i m : ℂ))
        = Fin.cons (fun m : ℕ => (u m : ℂ)) (fun i => fun m : ℕ => (w i m : ℂ)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [hconseq] at hconsC
    refine (linearIndependent_finCons.mp hconsC).2 ?_
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨b, funext fun m => by
      simpa [Finset.sum_apply, smul_eq_mul] using hu m⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at humem
  obtain ⟨c, hc⟩ := humem
  refine ⟨c, fun i => ?_⟩
  have hdiff : ∑ j, (b j - (c j : ℂ)) • (fun m : ℕ => (w j m : ℂ)) = 0 := by
    funext m
    have h2 : ∑ j, (c j : ℂ) * (w j m : ℂ) = (u m : ℂ) := by
      have hcm := congrFun hc m
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcm
      exact_mod_cast congrArg (Rat.cast (K := ℂ)) hcm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      sub_mul, Finset.sum_sub_distrib, hu m, h2, sub_self]
  have := Fintype.linearIndependent_iff.mp hw _ hdiff i
  exact sub_eq_zero.mp this

/-! #### Finite dimensionality of `S₂(Γ₀(N))`: the norm/Sturm route

Added 2026-07-24, cutting the former single geometric leaf
`exists_rational_qExpansion_basis` into its two genuinely different
contents. (i) FINITE DIMENSIONALITY of the weight-2 cusp space at
general level is PROVEN here in full, by upgrading the
level-1/level-2 emptiness technique (`cuspForm_level_two_coe_eq_zero`)
to a quantitative Sturm bound: the norm of `f` down to level 1 factors
as `f · g` where `g` — the product of the translates of `f` over the
NON-identity cosets of `Γ₀(N)` in `SL(2, ℤ)` — is itself
`Γ₀(N)`-slash-invariant (every element of `Γ₀(N)` stabilizes the
identity coset and permutes the rest), holomorphic and bounded at
`i∞`; hence both factors have width-1 `q`-expansions and
`ord(norm) ≥ ord(f)` (`PowerSeries.le_order_mul`), so if the first
`2·[SL(2,ℤ):Γ₀(N)]/12 + 1` coefficients of `f` vanish the norm beats
the level-1 Sturm threshold `weight/12` and dies, hence so does `f`.
A cusp form is therefore determined by finitely many coefficients and
`S₂(Γ₀(N))` embeds into `Fin B → ℂ`. (ii) The RATIONAL STRUCTURE —
a spanning set of forms with rational `q`-expansions, the genuinely
arithmetic-geometric fact (Shimura Thm 3.52) — is
`cuspForm_mem_span_rational` below, now itself a PROVEN Galois-descent
assembly (2026-07-24) whose single remaining sorried leaf is the
`Aut(ℂ)`-stability of the `q`-expansion image
(`exists_cuspForm_ringEquiv_conj`); the fixed-field computation
(`exists_ratCast_eq_of_forall_ringEquiv_fixed`) is PROVEN. -/

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

/-- **`Aut(ℂ)`-stability of `S₂(Γ₀(N))` on `q`-expansions** (sorry
node; THE residual arithmetic leaf of the rational-spanning node,
isolated 2026-07-24 when `cuspForm_mem_span_rational` was reduced to
it by the Galois-descent linear algebra below): for every field
automorphism `σ` of `ℂ` (as a ring automorphism — no continuity) and
every weight-2 level-`N` cusp form `f` there is a cusp form `f^σ`
whose `q`-expansion is the coefficientwise `σ`-conjugate of that of
`f`. This is Shimura's rationality theorem (*Introduction to the
Arithmetic Theory of Automorphic Functions*, Theorem 3.52 together
with the `Aut(ℂ)`-action of §3.5; equivalently Diamond–Shurman §6.5,
where the action `f ↦ f^σ` on `S₂(Γ₀(N))` is defined through the
`ℚ`-structure): the classical proofs go through the `ℤ`-structure of
`H₁(X₀(N), ℤ)` under the Eichler–Shimura isomorphism, or through the
`q`-expansion principle on the modular curve over `ℚ`, neither of
which exists on this pin. Note the equivalence with the rational-basis
form of the theorem: given a rational basis, `σ` acts coordinatewise
on the rational-coefficient span, and conversely (the direction proven
here in `cuspForm_mem_span_rational`) stability under all `σ` descends
the space to `ℚ`. -/
theorem exists_cuspForm_ringEquiv_conj {N : ℕ} (hN : 0 < N)
    (σ : ℂ ≃+* ℂ) (f : CuspForm (Gamma0GL N) 2) :
    ∃ g : CuspForm (Gamma0GL N) 2, ∀ m : ℕ, qCoeff N g m = σ (qCoeff N f m) :=
  sorry

/-- **Extension of subfield automorphisms to `Aut(ℂ)`** (PROVEN,
2026-07-24; the workhorse of the fixed-field computation below): every
ring automorphism `τ` of an intermediate field `K` of `ℂ/ℚ` extends to
a ring automorphism of `ℂ`. Proof: choose a transcendence basis `t` of
`ℂ` over `K` (`exists_isTranscendenceBasis`); `τ` acts coefficientwise
on `MvPolynomial t K ≃ adjoin K t` (`MvPolynomial.mapEquiv` conjugated
through `AlgebraicIndependent.aevalEquiv`), and `ℂ` is an algebraic
closure of `adjoin K t` (`IsTranscendenceBasis.isAlgebraic` plus
`Complex.isAlgClosed`), so `IsAlgClosure.equivOfEquiv` transports the
automorphism to all of `ℂ` compatibly with the inclusion of the
constants. -/
theorem exists_complex_ringEquiv_extension (K : IntermediateField ℚ ℂ)
    (τ : ↥K ≃+* ↥K) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a : ↥K, σ (a : ℂ) = ((τ a : ↥K) : ℂ) := by
  classical
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ↥K ℂ
  haveI halgC : Algebra.IsAlgebraic
      ↥(Algebra.adjoin ↥K (Set.range (Subtype.val : t → ℂ))) ℂ :=
    ht.isAlgebraic
  let ε : MvPolynomial t ↥K ≃ₐ[↥K]
      ↥(Algebra.adjoin ↥K (Set.range (Subtype.val : t → ℂ))) :=
    ht.1.aevalEquiv
  let μ : MvPolynomial t ↥K ≃+* MvPolynomial t ↥K := MvPolynomial.mapEquiv t τ
  let e := (ε.symm.toRingEquiv.trans μ).trans ε.toRingEquiv
  haveI : IsAlgClosure ↥(Algebra.adjoin ↥K (Set.range (Subtype.val : t → ℂ))) ℂ :=
    ⟨Complex.isAlgClosed, halgC⟩
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun a => ?_⟩
  have key : ∀ p : MvPolynomial t ↥K,
      algebraMap ↥(Algebra.adjoin ↥K (Set.range (Subtype.val : t → ℂ))) ℂ (ε p)
        = MvPolynomial.aeval (Subtype.val : t → ℂ) p :=
    ht.1.algebraMap_aevalEquiv
  have hconst : (a : ℂ) = algebraMap _ ℂ (ε (MvPolynomial.C a)) := by
    rw [key, MvPolynomial.aeval_C]
    rfl
  rw [hconst, IsAlgClosure.equivOfEquiv_algebraMap]
  have h1 : ε.symm.toRingEquiv (ε (MvPolynomial.C a)) = MvPolynomial.C a :=
    ε.symm_apply_apply (MvPolynomial.C a)
  have h2 : μ (MvPolynomial.C a) = MvPolynomial.C (τ a) := MvPolynomial.map_C _ a
  have he : e (ε (MvPolynomial.C a)) = ε (MvPolynomial.C (τ a)) := by
    show ε.toRingEquiv (μ (ε.symm.toRingEquiv (ε (MvPolynomial.C a)))) = _
    rw [h1, h2]
    rfl
  rw [he, key, MvPolynomial.aeval_C]
  rfl

/-- **The fixed field of `Aut(ℂ)` is `ℚ`** (PROVEN, 2026-07-24; the
field-theoretic half of the rational-spanning descent): a complex
number fixed by every ring automorphism of `ℂ` is rational. Proof:
(i) if `x` is transcendental over `ℚ`, extend `{x}` to a
transcendence basis `t` (`exists_isTranscendenceBasis_superset`); the
variable shift `X_x ↦ X_x + 1` is an automorphism of
`MvPolynomial t ℚ ≃ adjoin ℚ t` (`AlgebraicIndependent.aevalEquiv`),
and `ℂ` is an algebraic closure of `adjoin ℚ t`
(`IsTranscendenceBasis.isAlgebraic`), so `IsAlgClosure.equivOfEquiv`
extends it to `σ ∈ Aut(ℂ)` with `σ x = x + 1 ≠ x`. (ii) If `x` is
algebraic but irrational, its minimal polynomial has a second root
`y ≠ x` in the relative algebraic closure `ℚ̄ = algebraicClosure ℚ ℂ`
(separability, char 0); an embedding `ℚ⟮x⟯ →ₐ[ℚ] ℚ̄` sending `x ↦ y`
(`IntermediateField.algHomAdjoinIntegralEquiv`) extends to an
endomorphism of `ℚ̄` (`IntermediateField.exists_algHom_of_splits`),
bijective since `ℚ̄/ℚ` is algebraic
(`Algebra.IsAlgebraic.algHom_bijective`), and the resulting
automorphism of `ℚ̄` extends to `Aut(ℂ)` by
`exists_complex_ringEquiv_extension`, giving `σ ∈ Aut(ℂ)` with
`σ x = y ≠ x`. -/
theorem exists_ratCast_eq_of_forall_ringEquiv_fixed {x : ℂ}
    (hx : ∀ σ : ℂ ≃+* ℂ, σ x = x) : ∃ r : ℚ, x = (r : ℂ) := by
  classical
  -- Step 1: `x` is algebraic over `ℚ` — otherwise a shift of a
  -- transcendence basis through `{x}` yields `σ` with `σ x = x + 1`.
  have halg : IsAlgebraic ℚ x := by
    by_contra htr
    have hind : AlgebraicIndepOn ℚ id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set ℂ))).mpr htr
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    haveI halgC : Algebra.IsAlgebraic
        ↥(Algebra.adjoin ℚ (Set.range (Subtype.val : t → ℂ))) ℂ :=
      ht.isAlgebraic
    set R := Algebra.adjoin ℚ (Set.range (Subtype.val : t → ℂ))
    let ε : MvPolynomial t ℚ ≃ₐ[ℚ] ↥R := ht.1.aevalEquiv
    let i₀ : t := ⟨x, hxt rfl⟩
    let sh : MvPolynomial t ℚ ≃ₐ[ℚ] MvPolynomial t ℚ := by
      refine AlgEquiv.ofAlgHom
        (MvPolynomial.aeval fun i => MvPolynomial.X i + if i = i₀ then 1 else 0)
        (MvPolynomial.aeval fun i => MvPolynomial.X i - if i = i₀ then 1 else 0)
        ?_ ?_
      · refine MvPolynomial.algHom_ext fun i => ?_
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_X,
          AlgHom.id_apply]
        by_cases h : i = i₀ <;> simp [h]
      · refine MvPolynomial.algHom_ext fun i => ?_
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X, map_add, MvPolynomial.aeval_X,
          AlgHom.id_apply]
        by_cases h : i = i₀ <;> simp [h]
    let e : ↥R ≃+* ↥R := (ε.symm.trans (sh.trans ε)).toRingEquiv
    haveI : IsAlgClosure ↥R ℂ := ⟨Complex.isAlgClosed, halgC⟩
    let σ : ℂ ≃+* ℂ := IsAlgClosure.equivOfEquiv ℂ ℂ e
    have key : ∀ p : MvPolynomial t ℚ,
        algebraMap ↥R ℂ (ε p) = MvPolynomial.aeval (Subtype.val : t → ℂ) p :=
      ht.1.algebraMap_aevalEquiv
    have h1 : σ x = x + 1 := by
      have hxeq : algebraMap ↥R ℂ (ε (MvPolynomial.X i₀)) = x := by
        rw [key, MvPolynomial.aeval_X]
      have h2 := IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ e (ε (MvPolynomial.X i₀))
      have h3 : e (ε (MvPolynomial.X i₀)) = ε (MvPolynomial.X i₀ + 1) := by
        show (ε.symm.trans (sh.trans ε)) (ε (MvPolynomial.X i₀)) = _
        rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
        congr 1
        show MvPolynomial.aeval _ (MvPolynomial.X i₀) = _
        rw [MvPolynomial.aeval_X]
        simp
      rw [hxeq] at h2
      rw [h2, h3, key, map_add, MvPolynomial.aeval_X, map_one]
    have hcontra := hx σ
    rw [h1] at hcontra
    simp at hcontra
  -- Step 2: an irrational algebraic `x` is conjugated to a second
  -- root of its minimal polynomial by an automorphism of `ℚ̄ ⊆ ℂ`,
  -- extended to `Aut(ℂ)`.
  by_contra hirr
  haveI : Algebra.IsAlgebraic ℚ ↥(algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  haveI : IsAlgClosed ↥(algebraicClosure ℚ ℂ) :=
    (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  set xb : ↥(algebraicClosure ℚ ℂ) := ⟨x, mem_algebraicClosure_iff.mpr halg⟩
  have hint : IsIntegral ℚ xb := (Algebra.IsAlgebraic.isAlgebraic xb).isIntegral
  have hdeg : 1 < (minpoly ℚ xb).natDegree := by
    rcases Nat.lt_or_ge 1 (minpoly ℚ xb).natDegree with h | h
    · exact h
    · exfalso
      have hpos : 0 < (minpoly ℚ xb).natDegree := minpoly.natDegree_pos hint
      have h1 : (minpoly ℚ xb).natDegree = 1 := le_antisymm h hpos
      have hd1 : (minpoly ℚ xb).degree = 1 := by
        rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]
        rfl
      obtain ⟨r, hr⟩ := minpoly.degree_eq_one_iff.mp hd1
      refine hirr ⟨r, ?_⟩
      have h2 : (xb : ℂ) = ((algebraMap ℚ ↥(algebraicClosure ℚ ℂ) r :
          ↥(algebraicClosure ℚ ℂ)) : ℂ) := by rw [hr]
      simpa using h2
  have hcard : Fintype.card ((minpoly ℚ xb).rootSet ↥(algebraicClosure ℚ ℂ))
      = (minpoly ℚ xb).natDegree :=
    Polynomial.card_rootSet_eq_natDegree (K := ↥(algebraicClosure ℚ ℂ))
      (minpoly.irreducible hint).separable (IsAlgClosed.splits _)
  have hxbmem : xb ∈ (minpoly ℚ xb).rootSet ↥(algebraicClosure ℚ ℂ) :=
    Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, minpoly.aeval ℚ xb⟩
  obtain ⟨⟨y, hy⟩, hyne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [hcard]; exact hdeg)
    (⟨xb, hxbmem⟩ : ((minpoly ℚ xb).rootSet ↥(algebraicClosure ℚ ℂ)))
  have hy' : y ∈ (minpoly ℚ xb).aroots ↥(algebraicClosure ℚ ℂ) := by
    obtain ⟨hne, hev⟩ := Polynomial.mem_rootSet.mp hy
    exact Polynomial.mem_aroots.mpr ⟨hne, hev⟩
  let ψ₀ : ↥(IntermediateField.adjoin ℚ {xb}) →ₐ[ℚ] ↥(algebraicClosure ℚ ℂ) :=
    (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨y, hy'⟩
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩) ψ₀
  have hbij : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
  have hval : φ xb = y := by
    have h1 : φ ((IntermediateField.adjoin ℚ {xb}).val
        (IntermediateField.AdjoinSimple.gen ℚ xb)) =
        ψ₀ (IntermediateField.AdjoinSimple.gen ℚ xb) := by
      rw [← hφ]; rfl
    have h2 : ψ₀ (IntermediateField.AdjoinSimple.gen ℚ xb) = y :=
      IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint ⟨y, hy'⟩
    rw [h2] at h1
    simpa using h1
  obtain ⟨σ, hσ⟩ := exists_complex_ringEquiv_extension (algebraicClosure ℚ ℂ)
    (RingEquiv.ofBijective φ.toRingHom hbij)
  have h3 : ((φ xb : ↥(algebraicClosure ℚ ℂ)) : ℂ) = (xb : ℂ) := by
    have h1 := hσ xb
    have h2 : σ (xb : ℂ) = (xb : ℂ) := hx σ
    exact h1.symm.trans h2
  have h4 : φ xb = xb := Subtype.ext h3
  rw [hval] at h4
  exact hyne (Subtype.ext h4)

/-- **Rational spanning of `S₂(Γ₀(N))`** (PROVEN assembly, 2026-07-24,
over the sorried arithmetic leaf `exists_cuspForm_ringEquiv_conj` and
the PROVEN field-theory lemma
`exists_ratCast_eq_of_forall_ringEquiv_fixed`): every weight-2
level-`N` cusp form is a `ℂ`-linear combination of cusp forms ALL of
whose `q`-expansion coefficients are rational (Shimura Theorem 3.52 /
Diamond–Shurman §6.5). Proof — Galois descent through the Sturm
coordinates: (i) by the Sturm bound the coefficient functionals
`qCoeffL N m`, `m < B`, have trivial joint kernel, hence span the full
dual of the finite-dimensional space `S₂(Γ₀(N))`
(`Subspace.finrank_add_finrank_dualCoannihilator_eq`); (ii) extract a
dual-space basis `ψ` from this spanning family
(`exists_linearIndependent`) and take its predual basis
`E = ψ* ∘ evalEquiv⁻¹` of `S₂(Γ₀(N))`, characterized by
`ψⱼ (E k) = δⱼₖ`; (iii) for any `σ ∈ Aut(ℂ)` the `σ`-conjugate of
`E k` (the arithmetic leaf) has the same `ψ`-coordinates `σ(δⱼₖ) =
δⱼₖ`, hence EQUALS `E k` — so every `q`-coefficient of `E k` is fixed
by all of `Aut(ℂ)` and is rational by the field-theory leaf; (iv) the
basis `E` therefore lies in the rational-coefficient set and spans.
Combined with `cuspForm_finiteDimensional`, any maximal independent
subfamily of the rational-coefficient forms is a basis, which is how
`exists_rational_qExpansion_basis` consumes it. -/
theorem cuspForm_mem_span_rational {N : ℕ} (hN : 0 < N)
    (f : CuspForm (Gamma0GL N) 2) :
    f ∈ Submodule.span ℂ
      {g : CuspForm (Gamma0GL N) 2 | ∀ m : ℕ, ∃ r : ℚ, qCoeff N g m = (r : ℂ)} := by
  classical
  haveI := cuspForm_finiteDimensional N hN
  obtain ⟨B, hB⟩ := exists_cuspForm_sturm_bound N hN
  -- (i) the first `B` coefficient functionals span the full dual space
  have hspan : Submodule.span ℂ
      (Set.range fun i : Fin B => qCoeffL N (i : ℕ)) = ⊤ := by
    have hco : (Submodule.span ℂ
        (Set.range fun i : Fin B => qCoeffL N (i : ℕ))).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have hv0 : v = 0 := hB v fun m hm => by
        simpa using hv (qCoeffL N m) (Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩)
      simp [hv0]
    have hrank := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span ℂ (Set.range fun i : Fin B => qCoeffL N (i : ℕ)))
    rw [hco, finrank_bot, add_zero] at hrank
    exact Submodule.eq_top_of_finrank_eq (by rw [hrank, Subspace.dual_finrank_eq])
  -- (ii) a dual basis `ψ` from the spanning family, and its predual `E`
  obtain ⟨b, hbsub, hbspan, hbind⟩ :=
    exists_linearIndependent ℂ (Set.range fun i : Fin B => qCoeffL N (i : ℕ))
  rw [hspan] at hbspan
  have hbfin : b.Finite := hbind.setFinite
  letI := hbfin.fintype
  let ψ : Module.Basis b ℂ (Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) :=
    Module.Basis.mk hbind (le_of_eq (by rw [Subtype.range_coe]; exact hbspan.symm))
  let E : Module.Basis b ℂ (CuspForm (Gamma0GL N) 2) :=
    ψ.dualBasis.map (Module.evalEquiv ℂ (CuspForm (Gamma0GL N) 2)).symm
  have hEval : ∀ (j k : b),
      (j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) (E k) = if j = k then 1 else 0 := by
    intro j k
    have h2 : ψ j = (j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) :=
      Module.Basis.mk_apply _ _ j
    have h1 : (ψ j) (E k) = ψ.dualBasis k (ψ j) := by
      show (ψ j) ((ψ.dualBasis.map
        (Module.evalEquiv ℂ (CuspForm (Gamma0GL N) 2)).symm) k) = _
      rw [Module.Basis.map_apply]
      exact Module.apply_evalEquiv_symm_apply ℂ _ (ψ j) (ψ.dualBasis k)
    rw [← h2, h1, Module.Basis.dualBasis_apply_self]
  have hSep : ∀ u w : CuspForm (Gamma0GL N) 2,
      (∀ j : b, (j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) u =
        (j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) w) → u = w := by
    intro u w h
    have h3 : Module.evalEquiv ℂ (CuspForm (Gamma0GL N) 2) u =
        Module.evalEquiv ℂ (CuspForm (Gamma0GL N) 2) w := by
      refine ψ.ext fun i => ?_
      rw [Module.evalEquiv_apply, Module.Dual.eval_apply,
        Module.evalEquiv_apply, Module.Dual.eval_apply, Module.Basis.mk_apply]
      exact h i
    exact (Module.evalEquiv ℂ (CuspForm (Gamma0GL N) 2)).injective h3
  -- (iii) every coefficient of every `E k` is `Aut(ℂ)`-fixed, hence rational
  have hrat : ∀ k : b, ∀ m : ℕ, ∃ r : ℚ, qCoeff N (E k) m = (r : ℂ) := by
    intro k m
    refine exists_ratCast_eq_of_forall_ringEquiv_fixed fun σ => ?_
    obtain ⟨g, hg⟩ := exists_cuspForm_ringEquiv_conj hN σ (E k)
    have hgE : g = E k := by
      refine hSep g (E k) fun j => ?_
      obtain ⟨i, hi⟩ := hbsub j.2
      have h1 : (j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) g =
          σ ((j : Module.Dual ℂ (CuspForm (Gamma0GL N) 2)) (E k)) := by
        rw [← hi]; exact hg i
      rw [h1, hEval j k]
      split_ifs <;> simp
    rw [← hg m, hgE]
  -- (iv) the basis `E` lies in the rational-coefficient set and spans
  have hsub : Set.range (fun k : b => E k) ⊆
      {g : CuspForm (Gamma0GL N) 2 | ∀ m : ℕ, ∃ r : ℚ, qCoeff N g m = (r : ℂ)} := by
    rintro _ ⟨k, rfl⟩
    exact hrat k
  have hle := Submodule.span_mono (R := ℂ) hsub
  have hEtop : Submodule.span ℂ (Set.range fun k : b => E k) = ⊤ := E.span_eq
  rw [hEtop] at hle
  exact hle Submodule.mem_top

end SturmFiniteness

/-- **Rational basis of `S₂(Γ₀(N))`** (PROVEN assembly, 2026-07-24,
over the rational-spanning assembly `cuspForm_mem_span_rational` —
itself since PROVEN over the single remaining sorried leaf
`exists_cuspForm_ringEquiv_conj` — and the PROVEN
finite dimensionality `cuspForm_finiteDimensional`): the space of
weight-2 level-`N` cusp forms has a finite `ℂ`-independent family of
forms with RATIONAL `q`-expansion coefficients through which every
cusp form factors with explicit coordinates. Assembly: inside the
spanning set of rational-coefficient forms choose an independent
subfamily with the same span (`exists_linearIndependent`); it is
finite by `cuspForm_finiteDimensional`, and every `f` lies in its span
by `cuspForm_mem_span_rational`. Spanning is phrased with explicit
coordinates to keep consumers span-vocabulary-free. Note the statement
is sound for every `N ≥ 1` including genus-zero levels, where `n = 0`
and both clauses are vacuous. -/
theorem exists_rational_qExpansion_basis {N : ℕ} (hN : 0 < N) :
    ∃ (n : ℕ) (g : Fin n → CuspForm (Gamma0GL N) 2),
      LinearIndependent ℂ g ∧
      (∀ f : CuspForm (Gamma0GL N) 2, ∃ b : Fin n → ℂ, f = ∑ i, b i • g i) ∧
      (∀ i m, ∃ r : ℚ, qCoeff N (g i) m = (r : ℂ)) := by
  classical
  haveI := cuspForm_finiteDimensional N hN
  obtain ⟨b, hbR, hbspan, hbind⟩ := exists_linearIndependent ℂ
    {g : CuspForm (Gamma0GL N) 2 | ∀ m : ℕ, ∃ r : ℚ, qCoeff N g m = (r : ℂ)}
  have hbfin : b.Finite := hbind.setFinite
  letI := hbfin.fintype
  refine ⟨Fintype.card b,
    fun i => (((Fintype.equivFin b).symm i : b) : CuspForm (Gamma0GL N) 2),
    ?_, ?_, ?_⟩
  · exact hbind.comp (Fintype.equivFin b).symm (Equiv.injective _)
  · intro f
    have hrange : Set.range
        (fun i => (((Fintype.equivFin b).symm i : b) : CuspForm (Gamma0GL N) 2)) = b := by
      rw [show (fun i => (((Fintype.equivFin b).symm i : b) : CuspForm (Gamma0GL N) 2))
          = (Subtype.val ∘ (Fintype.equivFin b).symm) from rfl,
        Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe]
    have hf : f ∈ Submodule.span ℂ (Set.range
        (fun i => (((Fintype.equivFin b).symm i : b) : CuspForm (Gamma0GL N) 2))) := by
      rw [hrange, hbspan]
      exact cuspForm_mem_span_rational hN f
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
    exact ⟨c, hc.symm⟩
  · intro i m
    exact hbR ((Fintype.equivFin b).symm i).2 m

/-- Coercion to functions commutes with finite linear combinations of
cusp forms. -/
theorem coe_sum_smul {N n : ℕ} (c : Fin n → ℂ)
    (gs : Fin n → CuspForm (Gamma0GL N) 2) :
    ⇑(∑ i, c i • gs i) = ∑ i, c i • ⇑(gs i) := by
  classical
  suffices h : ∀ s : Finset (Fin n),
      ⇑(∑ i ∈ s, c i • gs i) = ∑ i ∈ s, c i • ⇑(gs i) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp [CuspForm.coe_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add,
      CuspForm.IsGLPos.coe_smul, ih]

/-- **Integral Hecke structure of an eigenform** (Diamond–Shurman
§6.5, the finite input to Theorem 6.5.1; PROVEN assembly, 2026-07-24,
over `exists_cuspForm_heckeTransform` and
`qExpansion_heckeTransform_coeff` — both since PROVEN — and, through
the now-proven assemblies `exists_rational_qExpansion_basis` and
`cuspForm_mem_span_rational`, the one remaining sorried leaf
`exists_cuspForm_ringEquiv_conj`): for a
normalized weight-2
level-`N` eigenform `f` there are a dimension `n`, a family of
RATIONAL `n × n` matrices `T q`, and a common nonzero complex
eigenvector `v` with `T q ⬝ v = a_q(f)·v` for every prime `q`. The
assembly instantiates the analytic route: `v` is the coordinate
vector of `f` in a rational basis `g` of `S₂(Γ₀(N))` (nonzero since
`a₁(f) = 1`), `T q` is the matrix of the Hecke slash-sum in that
basis — its entries are rational because `T_q` preserves rational
`q`-expansions (`qExpansion_heckeTransform_coeff`) and rational
coordinates against a rational basis are rational
(`exists_ratCast_coords`) — and the eigen-equation is the eigenform
coefficient identity `hecke_eigen_coeff_identity` transported through
the `q`-expansion principle `cuspForm_eq_of_forall_qCoeff_eq`. -/
theorem exists_heckeMatrix_eigenvector {N : ℕ} (hN : 0 < N)
    {f : CuspForm (Gamma0GL N) 2} (hf : IsWeightTwoEigenform N f) :
    ∃ (n : ℕ) (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℂ),
      v ≠ 0 ∧ ∀ q : ℕ, q.Prime →
        (T q).map (algebraMap ℚ ℂ) *ᵥ v = qCoeff N f q • v := by
  classical
  obtain ⟨n, g, hind, hspan, hrat⟩ := exists_rational_qExpansion_basis hN
  choose w hw using hrat
  -- the rational coefficient sequences of the basis are ℂ-independent
  have hseq : LinearIndependent ℂ fun i => fun m : ℕ => (w i m : ℂ) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hzero : (∑ i, c i • g i) = (0 : CuspForm (Gamma0GL N) 2) := by
      apply cuspForm_eq_of_forall_qCoeff_eq
      intro m
      have h1 : qCoeff N (∑ i, c i • g i) m = ∑ i, c i * qCoeff N (g i) m := by
        have hs := map_sum (qCoeffL N m) (fun i => c i • g i) Finset.univ
        simp only [map_smul, smul_eq_mul] at hs
        simp only [qCoeffL_apply] at hs
        exact hs
      rw [h1, qCoeff_zero_cuspForm]
      have hcm := congrFun hc m
      simpa [Finset.sum_apply, hw, smul_eq_mul] using hcm
    exact Fintype.linearIndependent_iff.mp hind c hzero
  -- coordinates of the eigenform
  obtain ⟨b, hb⟩ := hspan f
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hf0 : f = 0 := by simpa using hb
    have h1 := hf.qCoeff_one
    rw [hf0, qCoeff_zero_cuspForm] at h1
    exact zero_ne_one h1
  -- the rational Hecke matrices
  have hex : ∀ q : ℕ, q.Prime → ∃ M : Matrix (Fin n) (Fin n) ℚ,
      ∀ i, heckeTransform N q ⇑(g i) = ⇑(∑ j, ((M j i : ℚ) : ℂ) • g j) := by
    intro q hq
    have hstep : ∀ i : Fin n, ∃ col : Fin n → ℚ,
        heckeTransform N q ⇑(g i) = ⇑(∑ j, (col j : ℂ) • g j) := by
      intro i
      obtain ⟨h, hh⟩ := exists_cuspForm_heckeTransform hN hq (g i)
      obtain ⟨c, hc⟩ := hspan h
      have hu : ∀ m : ℕ, ∑ j, c j * (w j m : ℂ) =
          ((w i (q * m) +
            (if q ∣ N then 0 else if q ∣ m then (q : ℚ) * w i (m / q) else 0) : ℚ) : ℂ) := by
        intro m
        have h1 : qCoeff N h m = ∑ j, c j * qCoeff N (g j) m := by
          rw [hc]
          have hs := map_sum (qCoeffL N m) (fun j => c j • g j) Finset.univ
          simp only [map_smul, smul_eq_mul] at hs
          simp only [qCoeffL_apply] at hs
          exact hs
        have h2 : qCoeff N h m =
            (qExpansion 1 (heckeTransform N q ⇑(g i))).coeff m := by
          show (qExpansion 1 ⇑h).coeff m = _
          rw [hh]
        simp only [← hw]
        rw [← h1, h2, qExpansion_heckeTransform_coeff hN hq (g i) m]
        split_ifs <;> push_cast <;> simp [hw]
      obtain ⟨col, hcol⟩ := exists_ratCast_coords hseq hu
      refine ⟨col, ?_⟩
      rw [← hh, hc]
      exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [hcol j])
    choose cols hcols using hstep
    exact ⟨Matrix.of fun jj ii => cols ii jj, fun i => by simpa using hcols i⟩
  choose Mat hMat using hex
  refine ⟨n, fun q => if hq : q.Prime then Mat q hq else 0, b, hb0, ?_⟩
  intro q hq
  simp only [dif_pos hq]
  -- the transformed eigenform is its eigen-multiple
  obtain ⟨hF, hhF⟩ := exists_cuspForm_heckeTransform hN hq f
  have heig : hF = qCoeff N f q • f := by
    apply cuspForm_eq_of_forall_qCoeff_eq
    intro m
    have h1 : qCoeff N hF m =
        (qExpansion 1 (heckeTransform N q ⇑f)).coeff m := by
      show (qExpansion 1 ⇑hF).coeff m = _
      rw [hhF]
    rw [h1, qExpansion_heckeTransform_coeff hN hq f m,
      hecke_eigen_coeff_identity hf hq m]
    have h2 : qCoeff N (qCoeff N f q • f) m = qCoeff N f q * qCoeff N f m := by
      have hs := map_smul (qCoeffL N m) (qCoeff N f q) f
      simp only [qCoeffL_apply, smul_eq_mul] at hs
      exact hs
    exact h2.symm
  -- expand the Hecke transform of `f` over the basis
  have hL : heckeTransform N q ⇑f = ∑ i, b i • heckeTransform N q ⇑(g i) := by
    rw [hb, coe_sum_smul]
    let TL : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) :=
      { toFun := heckeTransform N q
        map_add' := heckeTransform_add N q
        map_smul' := heckeTransform_smul N q }
    have hTL : ∀ x : ℍ → ℂ, TL x = heckeTransform N q x := fun _ => rfl
    calc heckeTransform N q (∑ i, b i • ⇑(g i))
        = TL (∑ i, b i • ⇑(g i)) := (hTL _).symm
      _ = ∑ i, TL (b i • ⇑(g i)) := map_sum TL _ Finset.univ
      _ = ∑ i, b i • heckeTransform N q ⇑(g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, hTL]
  have hL2 : heckeTransform N q ⇑f =
      ⇑(∑ j, (∑ i, ((Mat q hq) j i : ℂ) * b i) • g j) := by
    rw [hL, coe_sum_smul]
    calc ∑ i, b i • heckeTransform N q ⇑(g i)
        = ∑ i, b i • ∑ j, ((Mat q hq) j i : ℂ) • ⇑(g j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hMat q hq i, coe_sum_smul]
      _ = ∑ i, ∑ j, (((Mat q hq) j i : ℂ) * b i) • ⇑(g j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ j, ∑ i, (((Mat q hq) j i : ℂ) * b i) • ⇑(g j) := Finset.sum_comm
      _ = ∑ j, (∑ i, ((Mat q hq) j i : ℂ) * b i) • ⇑(g j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_smul]
  -- match coefficients through independence
  have hRform : (∑ j, (qCoeff N f q * b j) • g j) = qCoeff N f q • f := by
    rw [hb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
  have hforms : (∑ j, (∑ i, ((Mat q hq) j i : ℂ) * b i) • g j)
      = qCoeff N f q • f := by
    apply DFunLike.coe_injective
    calc ⇑(∑ j, (∑ i, ((Mat q hq) j i : ℂ) * b i) • g j)
        = heckeTransform N q ⇑f := hL2.symm
      _ = ⇑hF := hhF.symm
      _ = ⇑(qCoeff N f q • f) := by rw [heig]
  have hzero2 : ∑ j, ((∑ i, ((Mat q hq) j i : ℂ) * b i)
      - qCoeff N f q * b j) • g j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hforms, hRform, sub_self]
  have hcoef := Fintype.linearIndependent_iff.mp hind _ hzero2
  funext j
  have hj := sub_eq_zero.mp (hcoef j)
  show ∑ i, (Mat q hq).map (algebraMap ℚ ℂ) j i * b i = qCoeff N f q * b j
  rw [← hj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, eq_ratCast]

end HeckeOperator

/-- **The single-finite-structure argument** (pure linear algebra):
if a family of matrices with RATIONAL entries has a common nonzero
eigenvector `v` (over `ℂ`) with eigenvalue system `a`, then all the
`a i` lie in a single finite-dimensional `ℚ`-subalgebra of `ℂ` —
namely the image, under the eigenvalue character `x ↦ (x ⬝ v)ᵢ / vᵢ`,
of the `ℚ`-algebra the family generates, which embeds in the
`n²`-dimensional algebra of rational matrices. Individually each
`a i` is merely algebraic of degree `≤ n`; it is the SINGLE generated
algebra that bounds the field they generate jointly. -/
theorem exists_finiteDimensional_subalgebra_of_matrix_eigenvector
    {n : ℕ} {ι : Type*} (T : ι → Matrix (Fin n) (Fin n) ℚ)
    {v : Fin n → ℂ} (a : ι → ℂ) (hv : v ≠ 0)
    (hT : ∀ i, (T i).map (algebraMap ℚ ℂ) *ᵥ v = a i • v) :
    ∃ B : Subalgebra ℚ ℂ, FiniteDimensional ℚ B ∧ ∀ i, a i ∈ B := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  -- the ℚ-algebra of complex matrices generated by the family
  set A : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
    Algebra.adjoin ℚ (Set.range fun i => (T i).map (algebraMap ℚ ℂ)) with hA
  -- the eigenvalue subalgebra: all eigenvalues on `v` of elements of `A`
  refine ⟨{ carrier := {c : ℂ | ∃ x ∈ A, x *ᵥ v = c • v}
            one_mem' := ⟨1, one_mem A, by rw [Matrix.one_mulVec, one_smul]⟩
            mul_mem' := by
              intro c d hc hd
              obtain ⟨x, hxA, hx⟩ := hc
              obtain ⟨y, hyA, hy⟩ := hd
              refine ⟨x * y, mul_mem hxA hyA, ?_⟩
              rw [← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, hx,
                smul_smul, mul_comm d c]
            zero_mem' := ⟨0, zero_mem A, by rw [Matrix.zero_mulVec, zero_smul]⟩
            add_mem' := by
              intro c d hc hd
              obtain ⟨x, hxA, hx⟩ := hc
              obtain ⟨y, hyA, hy⟩ := hd
              exact ⟨x + y, add_mem hxA hyA, by
                rw [Matrix.add_mulVec, hx, hy, add_smul]⟩
            algebraMap_mem' := fun r =>
              ⟨algebraMap ℚ _ r, algebraMap_mem A r, by
                rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
                  Matrix.one_mulVec, algebraMap_smul]⟩ }, ?_, ?_⟩
  · -- finite-dimensionality, through the rational matrix algebra
    -- `A` lies in the range of the entrywise algebra embedding
    -- `Matrix ℚ →ₐ Matrix ℂ`, whose domain is finite-dimensional
    have hrange : A ≤ ((Algebra.ofId ℚ ℂ).mapMatrix (m := Fin n)).range := by
      rw [hA]
      apply Algebra.adjoin_le
      rintro x ⟨i, rfl⟩
      refine ⟨T i, ?_⟩
      ext j k
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply]
    have hAle : Subalgebra.toSubmodule A ≤ LinearMap.range
        ((Algebra.ofId ℚ ℂ).mapMatrix (m := Fin n)).toLinearMap := by
      intro x hx
      obtain ⟨y, hy⟩ := hrange hx
      exact ⟨y, hy⟩
    haveI hAfd : FiniteDimensional ℚ (Subalgebra.toSubmodule A) :=
      Submodule.finiteDimensional_of_le hAle
    -- push finiteness through the eigenvalue functional
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℚ] ℂ :=
      { toFun := fun x => (v i₀)⁻¹ * (x *ᵥ v) i₀
        map_add' := fun x y => by
          simp only [Matrix.add_mulVec, Pi.add_apply, mul_add]
        map_smul' := fun r x => by
          simp only [Matrix.smul_mulVec, Pi.smul_apply, RingHom.id_apply,
            mul_smul_comm] }
    refine FiniteDimensional.of_subalgebra_toSubmodule
      (Submodule.finiteDimensional_of_le
        (?_ : _ ≤ (Subalgebra.toSubmodule A).map L))
    intro c hc
    obtain ⟨x, hxA, hx⟩ := hc
    refine ⟨x, hxA, ?_⟩
    show (v i₀)⁻¹ * (x *ᵥ v) i₀ = c
    rw [hx, Pi.smul_apply, smul_eq_mul, mul_comm c (v i₀),
      inv_mul_cancel_left₀ hi₀]
  · -- membership of the eigenvalues
    refine fun i => ⟨(T i).map (algebraMap ℚ ℂ), ?_, hT i⟩
    rw [hA]
    exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- **Coefficient closure**: for a normalized eigenform, membership of
the PRIME coefficients in a `ℚ`-subalgebra of `ℂ` propagates to all
coefficients — `a₀ = 0` by cusp vanishing (`qCoeff_zero`), `a₁ = 1` by
normalization, prime powers by the two Hecke recursions (good and bad
primes), and composites by multiplicativity. This is the designated
consumer of the four `IsWeightTwoEigenform` accessor fields. -/
theorem qCoeff_mem_of_forall_prime_mem {N : ℕ}
    {f : CuspForm (Gamma0GL N) 2} (hf : IsWeightTwoEigenform N f)
    {B : Subalgebra ℚ ℂ} (hB : ∀ q : ℕ, q.Prime → qCoeff N f q ∈ B) :
    ∀ m : ℕ, qCoeff N f m ∈ B := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    clear hk
    by_cases hdvd : p ∣ N
    · induction k with
      | zero => rw [pow_zero, hf.qCoeff_one]; exact one_mem B
      | succ r ih =>
        rw [hf.qCoeff_prime_pow_of_dvd p hp hdvd r]
        exact mul_mem (hB p hp) ih
    · induction k using Nat.twoStepInduction with
      | zero => rw [pow_zero, hf.qCoeff_one]; exact one_mem B
      | one => rw [pow_one]; exact hB p hp
      | more r ih ih' =>
        rw [hf.qCoeff_prime_pow_of_not_dvd p hp hdvd r]
        exact sub_mem (mul_mem (hB p hp) ih') (mul_mem (natCast_mem B p) ih)
  | zero => rw [qCoeff_zero]; exact zero_mem B
  | one => rw [hf.qCoeff_one]; exact one_mem B
  | coprime a b ha hb hab iha ihb =>
    rw [hf.qCoeff_mul_coprime a b hab]
    exact mul_mem iha ihb

/-- **Hecke field finiteness** (Diamond–Shurman §6.5, Theorem 6.5.1):
the coefficients of a normalized weight-2 eigenform of level `N ≥ 1`
generate a finite extension of `ℚ` inside `ℂ`. Proven by assembling
the pieces above: the sorried leaf `exists_heckeMatrix_eigenvector`
provides the finite rational structure with the prime coefficients as
simultaneous eigenvalues; the eigenvalue character lands them in one
finite-dimensional `ℚ`-subalgebra `B ⊆ ℂ`
(`exists_finiteDimensional_subalgebra_of_matrix_eigenvector`); the
eigenform recursions push all coefficients into `B`
(`qCoeff_mem_of_forall_prime_mem`); finally every element of `B` is
integral over `ℚ`, so `heckeField N f` — the intermediate field
adjoin — coincides with the algebra adjoin inside `B` and is
finite-dimensional. The level positivity hypothesis keeps the
statement inside the classical theory (`Γ₀(0)` is not a finite-index
subgroup and its "cusp forms" are not the classical space); the
consumers only ever instantiate `N ≥ 1`. -/
theorem heckeField_finiteDimensional {N : ℕ} (hN : 0 < N)
    {f : CuspForm (Gamma0GL N) 2} (hf : IsWeightTwoEigenform N f) :
    FiniteDimensional ℚ (heckeField N f) := by
  obtain ⟨n, T, v, hv, hT⟩ := exists_heckeMatrix_eigenvector hN hf
  obtain ⟨B, hBfin, hBmem⟩ :=
    exists_finiteDimensional_subalgebra_of_matrix_eigenvector
      (fun q : {q : ℕ // q.Prime} => T q)
      (fun q : {q : ℕ // q.Prime} => qCoeff N f q) hv
      (fun q => hT q q.2)
  have hall : ∀ m : ℕ, qCoeff N f m ∈ B :=
    qCoeff_mem_of_forall_prime_mem hf fun q hq => hBmem ⟨q, hq⟩
  have halg : ∀ x ∈ Set.range (qCoeff N f), IsAlgebraic ℚ x := by
    rintro x ⟨m, rfl⟩
    haveI := hBfin
    exact ((IsIntegral.of_finite ℚ
      (⟨qCoeff N f m, hall m⟩ : B)).map B.val).isAlgebraic
  have hto : (heckeField N f).toSubalgebra
      = Algebra.adjoin ℚ (Set.range (qCoeff N f)) :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
  have hle : Subalgebra.toSubmodule (heckeField N f).toSubalgebra
      ≤ Subalgebra.toSubmodule B := by
    rw [hto]
    exact Subalgebra.toSubmodule.monotone
      (Algebra.adjoin_le (by rintro x ⟨m, rfl⟩; exact hall m))
  haveI := hBfin
  exact FiniteDimensional.of_subalgebra_toSubmodule
    (Submodule.finiteDimensional_of_le hle)

end HeckeFieldFiniteness

/-- **Attachment at the even prime, from a level-2 eigenform** (PROVEN
via the dimension-formula route: `S₂(Γ₀(2)) = 0`, so the eigenform
hypothesis is contradictory — `weightTwoEigenform_level_two_false`;
DECOMPOSITION PLAN item 3): a weight-2 level-2 normalized eigenform matching the eigensystem
`(E, S, Pv)` yields, over any finite-dimensional `K ⊆ ℚ̄_2` generated
by an embedded copy `φ₀ : E →+* K` of the eigensystem field, a
2-dimensional representation of `Γ ℚ` with coefficients in `K` itself,
unramified with Frobenius characteristic polynomial `(Pv v).map φ₀`
away from a finite exceptional set. This is the `λ ∣ 2` member of
Eichler–Shimura/Deligne (Diamond–Shurman §9.5–9.6: the `λ`-adic
representation of the newform of level dividing 2 underlying `f` is
defined over the completion `E_λ = ℚ₂(φ₀(E))`, which the generation
hypothesis `hgen` makes equal to `K`) plus Carayol–Saito local–global
compatibility; equivalently — since `S₂(Γ₀(2)) = 0` — it is
dischargeable through the dimension-formula route (DECOMPOSITION PLAN
item 3: no `f` exists, and `qCoeff_one` refutes `f = 0`). No `ρ` and
no hardly-ramifiedness appear: the statement is purely about the
eigenform, which is what makes it a genuine interface node rather than
a restatement of the consuming atom. -/
theorem exists_realization_at_two_of_weightTwoEigenform
    {E : Type v} [Field E] [NumberField E]
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    {f : CuspForm (Gamma0GL 2) 2} (hf : IsWeightTwoEigenform 2 f)
    (_hmatch : MatchesEigensystem 2 f S Pv)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (φ₀ : E →+* K)
    (_hgen : K = IntermediateField.adjoin ℚ_[2]
      (Set.range fun x : E => (φ₀ x : AlgebraicClosure ℚ_[2]))) :
    ∃ (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (τ : GaloisRep ℚ K (Fin 2 → K)),
      ∀ v ∉ T, τ.IsUnramifiedAt v ∧ τ.charFrob v = (Pv v).map φ₀ :=
  (weightTwoEigenform_level_two_false f hf).elim

section ThreeadicDischarge

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- **Reducibility of `3`-adic hardly ramified representations over
`ℚ̄_3`** (PROVEN glue for the `p = 3` discharge of the residually
reducible pillar below, DERIVED from the 3-adic classification of
`Threeadic.lean`): a hardly ramified `3`-adic representation is globally
an extension of the trivial character by a character — the mod-3
classification (`IsHardlyRamified.mod_three`, `ModThree.lean`) produces
a residual trivial-quotient functional out of the given residual
package, and the equivariant-lifting machinery
(`IsHardlyRamified.exists_global_triangular_of_residual_trivial_quotient`,
`Threeadic.lean`) upgrades it to a global triangular basis
`!![χ g, c g; 0, 1]` — so its base change to `ℚ̄_3` has the invariant
line spanned by `1 ⊗ b 0` and is not irreducible. The freeness of the
coefficient ring over `ℤ_[3]` consumed by the triangularization is
derived from module-finiteness plus torsion-freeness (`hZinj` and the
domain hypothesis), as in `Family.lean`'s instance layer. -/
theorem not_isIrreducible_baseChange_of_isHardlyRamified_three
    {R : Type u} [CommRing R] [Algebra ℤ_[3] R] [IsDomain R]
    [Module.Finite ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    [Algebra R (AlgebraicClosure ℚ_[3])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[3])]
    (hZinj : Function.Injective (algebraMap ℤ_[3] R))
    (hρ : IsHardlyRamified (show Odd 3 by decide) hv ρ)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[3] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hVbar : Module.rank kk (kk ⊗[R] V) = 2)
    (hρbar : IsHardlyRamified (show Odd 3 by decide) hVbar
      (ρ.baseChange kk)) :
    ¬ (ρ.baseChange (AlgebraicClosure ℚ_[3])).IsIrreducible := by
  intro hirr
  -- the coefficient ring is free over `ℤ_[3]`: finite and torsion-free
  -- over a PID
  haveI : Module.IsTorsionFree ℤ_[3] R :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZinj
  haveI : Module.Free ℤ_[3] R := Module.free_of_finite_type_torsion_free'
  -- the mod-3 classification: a residual trivial-quotient functional
  obtain ⟨π, hπsurj, hπequiv⟩ :=
    IsHardlyRamified.mod_three (kk ⊗[R] V) hVbar hρbar
  -- the global triangular form
  obtain ⟨b, χ, cc, hb⟩ :=
    IsHardlyRamified.exists_global_triangular_of_residual_trivial_quotient
      V hv hρ kk hsurj π hπsurj hπequiv
  -- the stable line `R • b 0`
  have hbg : ∀ g : Field.absoluteGaloisGroup ℚ, ρ g (b 0) = χ g • b 0 := by
    intro g
    have h : ρ g = Matrix.toLin b b !![χ g, cc g; 0, 1] := by
      rw [← hb g, Matrix.toLin_toMatrix]
    rw [h, Matrix.toLin_self, Fin.sum_univ_two]
    simp
  -- its base change is invariant under `ρ ⊗ ℚ̄_3`
  have hstab : ∀ (g : Field.absoluteGaloisGroup ℚ)
      (w : AlgebraicClosure ℚ_[3] ⊗[R] V),
      w ∈ Submodule.span (AlgebraicClosure ℚ_[3])
        {(1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0} →
      ρ.baseChange (AlgebraicClosure ℚ_[3]) g w ∈
        Submodule.span (AlgebraicClosure ℚ_[3])
          {(1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0} := by
    intro g w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul]
    refine Submodule.smul_mem _ c ?_
    have hgen : ρ.baseChange (AlgebraicClosure ℚ_[3]) g
        ((1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0) =
        χ g • ((1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0) := by
      rw [GaloisRep.baseChange_tmul, hbg g, TensorProduct.tmul_smul]
    rw [hgen]
    exact Submodule.smul_of_tower_mem _ _
      (Submodule.mem_span_singleton_self _)
  -- the line is nonzero and proper: it is spanned by the first vector of
  -- the base-changed basis
  have hK0 : (b.baseChange (AlgebraicClosure ℚ_[3])) 0 =
      (1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0 := by
    simp
  have hne : (1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0 ≠ 0 := by
    rw [← hK0]
    exact (b.baseChange (AlgebraicClosure ℚ_[3])).ne_zero 0
  have hnot : (1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 1 ∉
      Submodule.span (AlgebraicClosure ℚ_[3])
        {(1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0} := by
    intro hmem
    refine (b.baseChange (AlgebraicClosure ℚ_[3])).linearIndependent
      |>.notMem_span_image (s := {(0 : Fin 2)}) (x := 1) (by simp) ?_
    rw [Set.image_singleton, hK0]
    simpa using hmem
  -- refute simplicity with the proper nonzero invariant line
  haveI : IsSimpleOrder (Subrepresentation
      (ρ.baseChange (AlgebraicClosure ℚ_[3])).toRepresentation) := hirr
  rcases eq_bot_or_eq_top
      (⟨Submodule.span (AlgebraicClosure ℚ_[3])
          {(1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0},
        fun g w hw => hstab g w hw⟩ :
        Subrepresentation
          (ρ.baseChange (AlgebraicClosure ℚ_[3])).toRepresentation)
    with hP | hP
  · exact hne (Submodule.span_singleton_eq_bot.mp
      (congrArg Subrepresentation.toSubmodule hP))
  · refine hnot ?_
    have htop : Submodule.span (AlgebraicClosure ℚ_[3])
        {(1 : AlgebraicClosure ℚ_[3]) ⊗ₜ[R] b 0} = ⊤ :=
      congrArg Subrepresentation.toSubmodule hP
    rw [htop]
    exact Submodule.mem_top

end ThreeadicDischarge

-- The hardly ramified representation whose eigensystem the modularity
-- statements below attach to an eigenform: same coefficient-ring
-- package as `Family.lean` (the integers in a finite extension of
-- `ℚ_p`).
variable {p : ℕ} (hpodd : Odd p) [hp : Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}

/-! ### The classical pillars behind the two modularity sorries

DECOMPOSITION PLAN item 4, executed (2026-07-24). The two automorphy
statements `exists_weightTwoEigenform_trace_eq_of_isIrreducible` and
`exists_weightTwoEigenform_of_isIrreducible` below are PROVEN
assemblies over five stated-and-sorried classical pillars, following
the shape of the classical argument (Wiles, Taylor–Wiles,
Skinner–Wiles, Khare–Wintenberger, Carayol/Ribet):

1. `exists_residual_isHardlyRamified_odd` — residual reduction: the
   reduction of a hardly ramified `p`-adic representation modulo the
   maximal ideal is mod-`p` hardly ramified over the finite residue
   field (general-`p` analogue of
   `IsHardlyRamified.exists_residual_isHardlyRamified`, whose `p = 3`
   instance is already assembled in `Threeadic.lean`).
2. `exists_weightTwoEigenform_residual_of_isIrreducible` — RESIDUAL
   MODULARITY (the Serre-conjecture shadow, weak form: some level
   `N ≥ 1`): an irreducible hardly ramified mod-`ℓ` representation
   arises, trace-by-trace modulo a prime over `ℓ`
   (`MatchesResidualTraces`), from a weight-2 eigenform. As of
   2026-07-24 itself a PROVEN assembly: the `ℓ = 3` instance is
   discharged by contradiction from
   `IsHardlyRamified.mod_three_reducible`, and the sorry moved into
   the `ℓ ≥ 5` leaf
   `exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`
   (the Khare–Wintenberger content).
3. `exists_weightTwoEigenform_trace_eq_of_matchesResidualTraces` —
   MODULARITY LIFTING (the R = T shadow): a hardly ramified `p`-adic
   lift of an irreducible, residually modular representation is
   modular. DECOMPOSED (2026-07-24) into the Taylor–Wiles cut —
   pillars 3a (Hecke-side deformation), 3b (patching, `R = 𝕋`), 3c
   (modular points); see the dedicated section below — and now itself
   a PROVEN assembly.
4. `exists_weightTwoEigenform_trace_eq_of_residually_reducible` — the
   RESIDUALLY REDUCIBLE branch (the Skinner–Wiles shadow).
5. `exists_weightTwoEigenform_level_two_of_trace_eq` — LEVEL
   OPTIMIZATION to `Γ₀(2)` (the Carayol-conductor/Ribet shadow).
   PROVEN 2026-07-24 as an assembly: the sorried conductor leaf
   `exists_eigenform_level_dvd_two_of_trace_eq` (level lowering to
   some `M ∣ 2`, the genuine Carayol/Ribet content — see its
   docstring for the audit of why the contradiction cannot be pushed
   past that boundary) plus the proven emptiness of both target
   spaces (`weightTwoEigenform_level_one_false` — new, level-1
   norm/Sturm route — and `weightTwoEigenform_level_two_false`).

Soundness audit (2026-07-24): since `S₂(Γ₀(2)) = 0` is proven above
(`weightTwoEigenform_level_two_false`), every statement in this
subtree whose hypotheses include an irreducible hardly ramified
representation is — classically — true both by its cited direct proof
and because the classical chain 2→3/4→5 shows those hypotheses are
unsatisfiable (that unsatisfiability IS the Wiles argument, and it is
where the mathematical depth of the remaining sorries lives). Each
pillar is nevertheless stated in the exact shape of its literature
theorem, so each can be attacked by following its citations without
reference to the collapse.

CIRCULARITY GUARD for future dispatches: pillar 2 (residual
modularity) must NOT be proven through the compatible-family machinery
of `Family.lean` — that machinery CONSUMES the two assemblies below,
so routing pillar 2 through it would close a dependency cycle. The
sound proof routes are the Khare–Wintenberger induction (Invent. Math.
178 (2009)) or the FLT blueprint's potential-modularity chain
(Moret–Bailly + dihedral residual modularity + modularity lifting over
totally real fields, blueprint ch. 4). At `ℓ = 3`, pillar 2 IS
discharged (2026-07-24) by contradiction from
`IsHardlyRamified.mod_three_reducible` (`ModThree.lean`: no hardly
ramified mod-3 representation is irreducible); the `ℓ ≥ 5` instances
carry the real content and live in the leaf
`exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`.
Pillar 4 at `p = 3` was similarly discharged
(2026-07-24) from the 3-adic classification (`Threeadic.lean`, via
`not_isIrreducible_baseChange_of_isHardlyRamified_three` above): the
pillar is now a PROVEN dichotomy assembly over the `p ≥ 5` leaf
`exists_weightTwoEigenform_trace_eq_of_residually_reducible_of_five_le`,
which carries the Skinner–Wiles content. -/

open scoped TensorProduct

omit [IsDomain R] in
/-- **Residual reduction** (pillar 1; PROVEN 2026-07-24 by delegation
to `IsHardlyRamified.exists_residual_odd` in
`HardlyRamified/Residual.lean`): the reduction of a hardly ramified
`p`-adic representation modulo the maximal ideal of its coefficient
ring is a mod-`p` hardly ramified representation over the finite
residue field. This is the general-odd-`p` analogue of
`IsHardlyRamified.exists_residual_isHardlyRamified` (`Threeadic.lean`),
whose `p = 3` route the proof follows: the residue field is finite and
of characteristic `p` because `R` is a module-finite local
`ℤ_p`-algebra and a nontrivial domain (`p ∈ 𝔪` by Nakayama, and `𝔪` is
open because a module-finiteness surjection `ℤ_p^n → R` is an open map
for the module topology, so `R ⧸ 𝔪` is a finite quotient of the
compact `R` by an open subgroup), the determinant and outside-`2p`
unramifiedness conditions pass to any base change, and flatness at `p`
resp. tameness at `2` transfer along the open-kernel residue quotient
by the general-place transfer leaves `isFlatAt_baseChange_residue_at`
and `isTameAtTwo_baseChange_residue_res`.  The domain hypothesis on `R`
is not needed (nontriviality, which is what the Nakayama step consumes,
already follows from `IsLocalRing R`), so it is omitted. -/
theorem exists_residual_isHardlyRamified_odd
    (hρ : IsHardlyRamified hpodd hv ρ) :
    ∃ (kk : Type u) (_ : Field kk) (_ : Finite kk) (_ : Algebra ℤ_[p] kk)
      (_ : TopologicalSpace kk) (_ : DiscreteTopology kk)
      (_ : IsTopologicalRing kk) (_ : Algebra R kk)
      (_ : ContinuousSMul R kk)
      (_ : Function.Surjective (algebraMap R kk))
      (hVbar : Module.rank kk (kk ⊗[R] V) = 2),
      IsHardlyRamified hpodd hVbar (ρ.baseChange kk) :=
  IsHardlyRamified.exists_residual_odd hpodd hv hρ

/-- **Residual eigensystem matching**: the residual representation
`ρbar` (over a coefficient ring `k`; in the intended use a finite
field of characteristic `ℓ`) *arises from the weight-2 eigenform `f`
modulo a prime over `ℓ`* if some ring homomorphism `φ` from the
algebraic integers of the Hecke field `K_f` to `k` — classically:
reduction modulo a prime `λ ∣ ℓ` of `𝒪_{K_f}` composed with an
embedding of its residue field — carries, away from a finite
exceptional set `S`, the Hecke eigenvalue `a_q` to the Frobenius trace
of `ρbar` at `q`. The eigenvalue is an algebraic integer classically,
but `IsWeightTwoEigenform` does not bake integrality in, so the
integrality witness `x` is part of the data. The trace convention
matches the pillar conclusions below: the linear coefficient of the
characteristic polynomial is `−a_q`. This is Serre's "`ρbar` arises
from a cusp form of weight 2 and level `N`" (Serre, Duke 1987, §3),
stated purely through `q`-expansion coefficients. -/
def MatchesResidualTraces (N : ℕ) (f : CuspForm (Gamma0GL N) 2)
    {k : Type*} [CommRing k] [TopologicalSpace k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) :
    Prop :=
  ∃ φ : integralClosure ℤ (heckeField N f) →+* k,
    ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      ∃ x : integralClosure ℤ (heckeField N f),
        (x : heckeField N f) = heckeCoeff N f q ∧
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
          - φ x

/-- **Residual modularity, `ℓ ≥ 5`** (the general-case leaf of pillar
2 — the Khare–Wintenberger content; DECOMPOSED and PROVEN as an
assembly 2026-07-24): an IRREDUCIBLE hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5` arises from a normalized weight-2
eigenform of some level `N ≥ 1`. This is the level-and-weight-free
("weak") form of Serre's modularity conjecture in the hardly ramified
case (Serre, Duke 1987 — the refined conductor-2 form is recovered
downstream by the level-optimization pillar, not consumed here), a
theorem of Khare–Wintenberger (*Serre's modularity conjecture (I),
(II)*, Invent. Math. 178 (2009)); the FLT blueprint (ch. 4) reaches
the same automorphy through potential modularity.

ROUTE AUDIT (2026-07-24, founder cut — see the module docstring of
`Modularity/KhareWintenberger.lean` for the full both-ways audit):
at the hardly ramified type BOTH literature routes (the KW induction
and the blueprint's potential-modularity chain) terminate in a
contradiction rather than an eigenform — any compatible system
attached to the representation has a `3`-adic member which this
project PROVES reducible with Eisenstein Frobenius traces `1 + q`
(`Threeadic.lean`), and no cusp form matches the Eisenstein system;
transporting those traces back through the family forces the residual
representation to be reducible (Chebotarev + Brauer–Nesbitt). That
nonexistence is exactly the blueprint's ch. 4 headline ("there is no
prime `ℓ ≥ 5` and hardly-ramified irreducible 2-dimensional Galois
representation"), and is what `S₂(Γ₀(2)) = 0` (proven above) demands.
The leaf is accordingly PROVEN by `absurd` from the headline theorem
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`), itself a PROVEN Family-free
assembly over three sorried literature pillars: α — KW minimal
`ℓ`-adic lifting (KW (I) Thm 4.1); β — the compatible system and its
hardly ramified `3`-adic member (KW (I) §5 / BLGGT Brauer trick /
potential modularity, the pillar carrying the genuine remaining
depth); γ — Chebotarev–Brauer–Nesbitt over a finite coefficient field
(mechanical transfer of the proven `ZMod ℓ` twin in `Lift.lean`).
CIRCULARITY GUARD (now enforced structurally): the pillars live in a
module importing neither `Family.lean` nor `Lift.lean` nor this file;
pillar β's docstring forbids discharging it by porting
`Family.lean`'s `mem_isCompatible` proof, which runs through this
interface's consumers. -/
theorem exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      MatchesResidualTraces N f ρbar S :=
  absurd hirr
    (not_isIrreducible_of_isHardlyRamified_of_five_le hℓodd hℓ5 hW hρbar)

/-- **Residual modularity** (pillar 2; DECOMPOSED 2026-07-24 — now a
PROVEN assembly over the `ℓ ≥ 5` leaf above): an IRREDUCIBLE hardly
ramified mod-`ℓ` representation arises from a normalized weight-2
eigenform of some level `N ≥ 1` (the level-and-weight-free "weak" form
of Serre's modularity conjecture in the hardly ramified case; see the
leaf's docstring for the literature). The assembly is the odd-prime
dichotomy `ℓ = 3 ∨ ℓ ≥ 5`:

* at `ℓ = 3` the hypotheses are contradictory —
  `IsHardlyRamified.mod_three_reducible` (`ModThree.lean`, the
  Fontaine/Odlyzko discriminant-bound route) produces a proper nonzero
  `Γ ℚ`-stable submodule of any hardly ramified mod-3 representation,
  refuting `hirr` through the elementary unpacking
  `Slop.OddRep.isIrreducible_iff_forall` — so no Langlands–Tunnell
  input is needed;
* at `ℓ ≥ 5` the statement is the sorried Khare–Wintenberger leaf
  `exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le`.

AUDIT (2026-07-24): the general-`ℓ` form (not just `ℓ = 3`) is what
the consumer chain needs — the sole consumer
`exists_weightTwoEigenform_trace_eq_of_isIrreducible` instantiates
`ℓ := p` with `p` the residue characteristic of the `p`-adic
representation, and the top-level route (`Frey.lean` →
`Reducible.lean` → `Lift.lean`'s `residual_charFrob_eq` →
`Family.lean`'s `mem_isCompatible`) invokes that chain at the Frey
prime `p`, arbitrary `≥ 5`; narrowing this pillar to `ℓ = 3` would
break the assembly, so the split records exactly which instance is
proven and which carries the remaining content. -/
theorem exists_weightTwoEigenform_residual_of_isIrreducible
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      MatchesResidualTraces N f ρbar S := by
  rcases Nat.lt_or_ge ℓ 5 with h5 | h5
  · -- `ℓ < 5`: primality and oddness force `ℓ = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    interval_cases ℓ
    · exact absurd hℓodd (by decide)
    · exact absurd (Fact.out : Nat.Prime 1) (by decide)
    · exact absurd hℓodd (by decide)
    · exfalso
      obtain ⟨W₀, hW₀0, hW₀top, hW₀stable⟩ :=
        IsHardlyRamified.mod_three_reducible W hW hρbar
      have hirr' : ρbar.toRepresentation.IsIrreducible := hirr
      obtain ⟨-, hsub⟩ :=
        (Slop.OddRep.isIrreducible_iff_forall ρbar.toRepresentation).mp hirr'
      rcases hsub W₀
          (fun g v hv => hW₀stable g (Submodule.mem_map_of_mem hv)) with
        hb | ht
      · exact hW₀0 hb
      · exact hW₀top ht
    · exact absurd hℓodd (by decide)
  · -- `ℓ ≥ 5`: the Khare–Wintenberger leaf
    exact exists_weightTwoEigenform_residual_of_isIrreducible_of_five_le
      hℓodd h5 hW hρbar hirr

/-! ### The Taylor–Wiles cut behind the modularity-lifting pillar

Pillar 3 (`exists_weightTwoEigenform_trace_eq_of_matchesResidualTraces`
below) DECOMPOSED, 2026-07-24, following the actual architecture of
the Wiles/Taylor–Wiles proof with the flat refinements of
Conrad–Diamond–Taylor and Kisin. The classical argument runs through
ONE auxiliary object — the localized Hecke algebra `𝕋_𝔪` with its
Galois representation — and splits into three statements, each stated
against the project's deformation vocabulary (`GaloisRep`,
`IsHardlyRamified`, `charFrob`, base change — from
`Fermat/FLT/Deformations/RepresentationTheory/` and
`HardlyRamified/Defs.lean`) and the interface's eigenform carrier:

* **3a — the Hecke-side deformation**
  (`exists_hardlyRamified_heckeDeformation_of_matchesResidualTraces`):
  residual modularity converts into a Galois-side package: a
  coefficient ring `T` of the exact shape this file's `R` has
  (module-finite local `ℤ_ℓ`-algebra with its module topology) that is
  moreover `ℤ_ℓ`-FREE — the finite-flatness of the classical `𝕋_𝔪`,
  which also excludes the degenerate torsion instantiations such as
  `T = k` itself — carrying a hardly ramified rank-2 representation
  `ρT` on `Fin 2 → T` that reduces trace-by-trace to `ρbar` through a
  surjection `π : T →+* k`.
* **3b — patching, `R = 𝕋`**
  (`exists_ringHom_charFrob_eq_of_heckeDeformation`): every hardly
  ramified `p`-adic lift `ρ` of `ρbar` factors through the Hecke-side
  deformation on Frobenius traces, via a ring homomorphism
  `Φ : T →+* R`.
* **3c — modular points**
  (`exists_weightTwoEigenform_of_heckeDeformation_point`): every
  `ℚ̄_ℓ`-point of the Hecke-side deformation carries the trace system
  of `ρT` to the coefficient system of a weight-2 eigenform.

The assembly (now pillar 3's proof) is: 3a on the residual data, 3b
against `ρ`, then 3c evaluated at the point
`(algebraMap R ℚ̄_p).comp Φ`.

Soundness of the abstract quantification (audit 2026-07-24): in 3b and
3c the package `(T, ρT, π)` ranges over ALL Hecke-side hardly ramified
deformations, not only the genuine localized Hecke algebra for which
the literature proves the statements. Both remain classically true
under the section audit above (their hypothesis sets include an
irreducible hardly ramified residual representation, which the
classical chain 2→3/4→5 shows to be unsatisfiable), and their intended
discharge instantiates the package produced by 3a, for which 3b is
verbatim Taylor–Wiles(–Kisin) `R = 𝕋` and 3c is the Deligne–Serre
eigensystem decomposition of `𝕋_𝔪 ⊗ ℚ̄_ℓ`.

CIRCULARITY GUARD (inherited from pillar 3, mandatory): none of 3a–3c
may be proven through `Family.lean`'s compatible-family machinery —
`Family.lean` imports this file and consumes the assemblies below, so
any such route is circular (and is structurally an import cycle). -/

/-! #### The Carayol cut behind pillar 3a

Pillar 3a DECOMPOSED, 2026-07-24, following the actual shape of
Carayol's construction (*Formes modulaires et représentations
galoisiennes à valeurs dans un anneau local complet*, Contemp. Math.
165 (1994)): the Hecke-side deformation is glued from the `λ`-adic
representations attached to the eigenform components of the localized
Hecke algebra. The cut isolated the geometric content in two leaves
and PROVED the Chebotarev-density step between them; the
Hecke-package leaf 3a-i is since PROVEN by its route audit (the same
odd-prime dichotomy that discharges pillar 2 — see its docstring),
leaving the Carayol descent 3a-ii as the one open leaf:

* **3a-i — the Hecke algebra with its realizations**
  (`exists_heckeAlgebra_realizations_of_matchesResidualTraces`,
  PROVEN 2026-07-24 by the route audit recorded on the theorem —
  no non-vacuous discharge exists, and the hypothesis class is
  refuted by the `ℓ = 3` / `ℓ ≥ 5` dichotomy over the
  separately-owned nonexistence nodes already carrying pillar 2):
  residual modularity produces the coefficient package
  `(T, t, π)` — the localized anemic weight-2 Hecke algebra with its
  prime-indexed Hecke elements `t q` and residual reduction `π` —
  together with finitely many jointly injective coordinates into
  local coefficient rings, each carrying a hardly ramified eigenform
  representation whose Frobenius traces interpolate the `t q`
  (the bundled `HardlyRamifiedRealization`).
* **PROVEN — the Chebotarev trace gluing**
  (`forall_exists_toFun_eq_charpoly_coeff_one`): at EVERY group
  element — not just at Frobenii — the joint trace tuple of the
  realizations lies in the image of `T`. Proof: the image of the
  compact `T` under the continuous joint coordinate map is closed;
  the joint trace function is continuous (the trace is a linear
  functional on the endomorphism algebra, hence continuous in the
  module topology — `charpoly.coeff 1` itself has no continuity
  API, whence the proven bridge
  `charpoly_coeff_one_eq_neg_trace`); the Frobenius conjugacy
  classes off the exceptional set land in the image by the
  interpolation hypothesis and conjugation-invariance of
  characteristic polynomials (`charpoly_conj_mul_inv`); and those
  classes are dense (`dense_conjClasses_globalFrob`,
  `Chebotarev.lean`). This is the exact glue Carayol's construction
  needs: it converts Frobenius-indexed trace data into a trace
  function on the whole group with values in `T`.
* **3a-ii — the Carayol descent**
  (`exists_hardlyRamified_galoisRep_of_realizations`, DECOMPOSED
  2026-07-24 — now a PROVEN assembly over the Nyssen–Rouquier cut
  below): the glued trace system over the local ring `T`, reducing
  through `π` to the traces of the residually IRREDUCIBLE `ρbar`, is
  the trace system of an actual hardly ramified representation on
  `Fin 2 → T`.

The assembly (now pillar 3a's proof) is 3a-i, then the proven gluing,
then 3a-ii, then the sign bookkeeping `π (t q) = −tr ρbar(Frob q)`.

Soundness audit (2026-07-24, inherited from the section docstring):
as with 3b/3c, the leaves quantify over data more general than the
honest localized Hecke algebra; both remain classically true because
their hypothesis sets include an irreducible hardly ramified residual
representation, which the classical chain 2→3/4→5 shows to be
unsatisfiable, and their non-vacuous intended discharge is the
classical construction recorded in their docstrings. -/

/-- **A hardly ramified realization of a Hecke-side coefficient ring**
`T`: one "eigenform component" of the would-be Hecke algebra — a local
coefficient ring `O` (intended: the integers of a finite extension of
`ℚ_ℓ`, the completion of the Hecke field of an eigenform component of
`T ⊗ ℚ_ℓ` at a place over `ℓ`), a `ℤ_ℓ`-algebra coordinate
`toFun : T →ₐ O`, and a hardly ramified representation over `O` (the
`λ`-adic representation attached to the eigenform by Eichler–Shimura,
integrally realized on a stable lattice — unique up to homothety when
the residual representation is irreducible). The instance fields
mirror the coefficient package of `Lift.lean`'s `HardlyRamifiedLift`
(which lives DOWNSTREAM of this file and cannot be imported), plus
`ℤ_ℓ`-freeness and Hausdorffness — both automatic for the intended `O`
and consumed by the compactness/closedness step of the Chebotarev
gluing below. -/
structure HardlyRamifiedRealization (ℓ : ℕ) [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    (T : Type u) [CommRing T] [Algebra ℤ_[ℓ] T] where
  /-- The local coefficient ring of the realization. -/
  O : Type u
  [commRing : CommRing O]
  [topologicalSpace : TopologicalSpace O]
  [isTopologicalRing : IsTopologicalRing O]
  [isLocalRing : IsLocalRing O]
  [t2Space : T2Space O]
  [algebra : Algebra ℤ_[ℓ] O]
  [moduleFinite : Module.Finite ℤ_[ℓ] O]
  [moduleFree : Module.Free ℤ_[ℓ] O]
  [isModuleTopology : IsModuleTopology ℤ_[ℓ] O]
  /-- The coordinate: a `ℤ_ℓ`-algebra map from the coefficient ring. -/
  toFun : T →ₐ[ℤ_[ℓ]] O
  /-- The realized representation, framed by the standard basis. -/
  ρ : GaloisRep ℚ O (Fin 2 → O)
  /-- The standard rank computation, fixed as a field so the
  hardly-ramifiedness field can be stated against it. -/
  hrank : Module.rank O (Fin 2 → O) = 2
  /-- The realized representation is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hℓodd hrank ρ

attribute [instance] HardlyRamifiedRealization.commRing
  HardlyRamifiedRealization.topologicalSpace
  HardlyRamifiedRealization.isTopologicalRing
  HardlyRamifiedRealization.isLocalRing
  HardlyRamifiedRealization.t2Space
  HardlyRamifiedRealization.algebra
  HardlyRamifiedRealization.moduleFinite
  HardlyRamifiedRealization.moduleFree
  HardlyRamifiedRealization.isModuleTopology

/-- The linear coefficient of the characteristic polynomial of an
endomorphism of the standard rank-2 free module is the negated trace
(`charpoly = X² − (tr φ)·X + det φ`). Bridge for the continuity step
of the Chebotarev gluing below: the trace is a linear functional on
the endomorphism algebra, hence continuous in the module topology,
while `charpoly.coeff 1` has no direct continuity API. -/
lemma charpoly_coeff_one_eq_neg_trace {A : Type*} [CommRing A]
    (φ : Module.End A (Fin 2 → A)) :
    φ.charpoly.coeff 1 = - LinearMap.trace A (Fin 2 → A) φ := by
  have h := Matrix.trace_eq_neg_charpoly_coeff
    (LinearMap.toMatrix (Pi.basisFun A (Fin 2)) (Pi.basisFun A (Fin 2)) φ)
  rw [LinearMap.charpoly_toMatrix] at h
  rw [LinearMap.trace_eq_matrix_trace A (Pi.basisFun A (Fin 2)), h]
  norm_num

/-- Characteristic polynomials of a Galois representation are constant
on conjugacy classes (the standalone form of the conjugation step
inside `Lift.lean`'s `not_isIrreducible_of_charFrob_eq`, restated here
because that file lives downstream). Feeds the Frobenius-classes step
of the Chebotarev gluing below. -/
lemma charpoly_conj_mul_inv {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M] (ρ : GaloisRep ℚ A M)
    (h g : Field.absoluteGaloisGroup ℚ) :
    (ρ (h * g * h⁻¹)).charpoly = (ρ g).charpoly := by
  have hgu : (ρ h).comp (ρ h⁻¹) = LinearMap.id := by
    have h1 : ρ h * ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact h1
  have hgu' : (ρ h⁻¹).comp (ρ h) = LinearMap.id := by
    have h1 : ρ h⁻¹ * ρ h = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    exact h1
  have heq : ρ (h * g * h⁻¹) =
      (LinearEquiv.ofLinear (ρ h) (ρ h⁻¹) hgu hgu').conj (ρ g) := by
    ext x
    simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
  rw [heq, LinearEquiv.charpoly_conj]

set_option backward.isDefEq.respectTransparency false in
/-- **The Chebotarev trace gluing** (PROVEN — the density step of
Carayol's construction): given finitely many hardly ramified
realizations of a compact coefficient ring `T` whose Frobenius traces
off a finite exceptional set jointly interpolate the elements `- t q`
of `T`, EVERY group element's joint trace tuple lies in the image of
`T`. The three ingredients are closedness of the image of the compact
`T` under the continuous joint coordinate map, continuity of the joint
trace function (via `charpoly_coeff_one_eq_neg_trace` and linearity of
the trace in the module topology), and density of the Frobenius
conjugacy classes off the exceptional set
(`dense_conjClasses_globalFrob`), on which the tuple is the image of
`- t q` by hypothesis and conjugation-invariance
(`charpoly_conj_mul_inv`). -/
theorem forall_exists_toFun_eq_charpoly_coeff_one
    {ℓ : ℕ} [Fact ℓ.Prime] {hℓodd : Odd ℓ}
    {T : Type u} [CommRing T] [TopologicalSpace T] [Algebra ℤ_[ℓ] T]
    [IsModuleTopology ℤ_[ℓ] T] [CompactSpace T]
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    {t : ℕ → T}
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q)) :
    ∀ g : Field.absoluteGaloisGroup ℚ, ∃ x : T,
      ∀ i, (real i).toFun x = ((real i).ρ g).charpoly.coeff 1 := by
  classical
  -- continuity of the joint trace function
  have hFcont : Continuous fun (g : Field.absoluteGaloisGroup ℚ)
      (i : Fin n) => ((real i).ρ g).charpoly.coeff 1 := by
    rw [continuous_pi_iff]
    intro i
    letI := moduleTopology (real i).O
      (Module.End (real i).O (Fin 2 → (real i).O))
    haveI : IsModuleTopology (real i).O
        (Module.End (real i).O (Fin 2 → (real i).O)) := ⟨rfl⟩
    have hρc : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
        (real i).ρ g := ContinuousMonoidHom.continuous_toFun ((real i).ρ)
    have htrc : Continuous fun φ : Module.End (real i).O
        (Fin 2 → (real i).O) =>
        LinearMap.trace (real i).O (Fin 2 → (real i).O) φ :=
      IsModuleTopology.continuous_of_linearMap _
    have hcoeff : (fun g : Field.absoluteGaloisGroup ℚ =>
        ((real i).ρ g).charpoly.coeff 1) =
        fun g => - LinearMap.trace (real i).O (Fin 2 → (real i).O)
          ((real i).ρ g) := by
      funext g
      exact charpoly_coeff_one_eq_neg_trace _
    rw [hcoeff]
    exact (htrc.comp hρc).neg
  -- the joint image of `T` is compact, hence closed
  have hΦcont : Continuous fun (x : T) (i : Fin n) => (real i).toFun x := by
    rw [continuous_pi_iff]
    intro i
    haveI := IsModuleTopology.toContinuousAdd ℤ_[ℓ] (real i).O
    exact IsModuleTopology.continuous_of_linearMap ((real i).toFun).toLinearMap
  have hclosed : IsClosed
      (Set.range fun (x : T) (i : Fin n) => (real i).toFun x) :=
    (isCompact_range hΦcont).isClosed
  -- the agreement set is closed …
  have hDclosed : IsClosed ((fun (g : Field.absoluteGaloisGroup ℚ)
      (i : Fin n) => ((real i).ρ g).charpoly.coeff 1) ⁻¹'
      Set.range fun (x : T) (i : Fin n) => (real i).toFun x) :=
    hclosed.preimage hFcont
  -- … and contains the dense set of Frobenius conjugates off `S_T`
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S_T ∧
        ∃ g : Field.absoluteGaloisGroup ℚ, x = g * globalFrob v * g⁻¹} ⊆
      (fun (g : Field.absoluteGaloisGroup ℚ) (i : Fin n) =>
        ((real i).ρ g).charpoly.coeff 1) ⁻¹'
        Set.range fun (x : T) (i : Fin n) => (real i).toFun x := by
    rintro x ⟨v, hvS, h, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    refine ⟨- t q, ?_⟩
    funext i
    have hconj := charpoly_conj_mul_inv (real i).ρ h
      (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
    have hval := htr i q hq hvS
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    show (real i).toFun (- t q) =
      ((real i).ρ (h * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * h⁻¹)).charpoly.coeff 1
    rw [hconj, ← hval]
  -- density: every group element's trace tuple comes from `T`
  intro g
  have hdense := dense_conjClasses_globalFrob (K := ℚ) S_T
  have hmem : (fun i => ((real i).ρ g).charpoly.coeff 1) ∈
      Set.range fun (x : T) (i : Fin n) => (real i).toFun x := by
    have huniv : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ g)
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, fun i => congrFun hx i⟩

/-- **The Hecke algebra with its hardly ramified realizations**
(pillar 3a-i; PROVEN 2026-07-24 by the odd-prime dichotomy — see the
ROUTE AUDIT below): residual modularity of the irreducible hardly
ramified `ρbar` at some level `N₀` produces the Hecke-side coefficient
package with its eigenform realizations. Classical construction
(recorded as the would-be non-vacuous discharge; the ROUTE AUDIT shows
it terminates in the PROVEN emptiness of the optimized level rather
than in a package): (1) optimize the
level to the Serre type of `ρbar` (Ribet, Invent. Math. 100 (1990);
Serre, Duke 1987 §4.1 — for the hardly ramified type the odd part of
the conductor is trivial and the weight is 2); (2) let `T₀` be the
ANEMIC weight-2 Hecke algebra `ℤ[T_q : q ∤ 2ℓN] ⊗ ℤ_ℓ` — good primes
only, so the algebra is reduced (the good `T_q` act semisimply on
`S₂`) and its traces are exactly what Carayol's gluing controls —
localized at the maximal ideal cut out by `ρbar`'s eigensystem
through the `φ` of `MatchesResidualTraces` (non-Eisenstein because
`ρbar` is irreducible): `T₀` is local, module-finite and torsion-free
over `ℤ_ℓ` (it acts faithfully on the `𝔪`-localized integral homology
of the modular curve `X₀(N)`), hence FREE over the PID `ℤ_ℓ`, and
compact in its module topology (quotient of `ℤ_ℓ^m`); (3) enlarge
coefficients unramifiedly, `T := (T₀ ⊗_{W(k₀)} W(k))_𝔪'`, so that the
residual reduction `π` is surjective onto the GIVEN `k` (not merely
onto the subfield its eigenvalues generate); (4) `t q` := the image
of the Hecke operator `T_q` (junk at the finitely many excluded
primes — absorbed into `S_T`), with `π (t q) = tr ρbar(Frob q)
= −charFrob.coeff 1` by the matching hypothesis; (5) `T` reduced and
finite flat makes `T ⊗ ℚ_ℓ` a finite product of finite extensions
`E_i/ℚ_ℓ`; the coordinates `λ_i : T →ₐ O_{E_i}` (integrality of `T`)
are JOINTLY INJECTIVE by torsion-freeness; (6) each factor is the
eigensystem of a Galois-conjugate newform component `f_i`, whose
attached `λ`-adic representation (Eichler–Shimura/Deligne, weight 2)
realizes it integrally on a residually irreducible — hence unique up
to homothety — lattice over `O_{E_i}`, hardly ramified by: determinant
cyclotomic (weight 2, trivial nebentypus), unramified outside `2ℓ`
(optimized level), flat at `ℓ` (weight 2, level prime to `ℓ`:
Fontaine–Laffaille; Conrad–Diamond–Taylor), tame at 2 with unramified
square-trivial rank-1 quotient (conductor exponent `≤ 1` at 2:
Carayol–Saito local–global compatibility); the Eichler–Shimura
congruence gives the interpolation `tr ρ_i(Frob q) = λ_i(t q)`.

ROUTE AUDIT (2026-07-24, following the precedent of pillar 2's `ℓ ≥ 5`
leaf): NO non-vacuous discharge of this statement is possible in this
repository. With `n = 0` realizations the joint-injectivity clause
degenerates to `∀ x y : T, x = y`, contradicting the nontriviality in
`IsLocalRing T`; and a realization (`n ≥ 1`) is classically the
attached representation of a weight-2 newform whose level equals its
conductor (Carayol), which hardly-ramifiedness forces to divide 2
(flat at `ℓ` at weight 2 makes the level prime to `ℓ`; tame at 2 with
conductor exponent `≤ 1` caps the even part) — while
`S₂(Γ₀(1)) = S₂(Γ₀(2)) = 0` are PROVEN above
(`weightTwoEigenform_level_one_false`,
`weightTwoEigenform_level_two_false`). The classical construction
recorded above thus terminates in the emptiness of the optimized
level — a refutation of the hypothesis class, never a package —
exactly as both literature routes in pillar 2's route audit. The
proof is accordingly the SAME odd-prime dichotomy that discharges
pillar 2 (`exists_weightTwoEigenform_residual_of_isIrreducible`),
over the same two separately-owned nonexistence nodes, adding no new
frontier: at `ℓ = 3`, `IsHardlyRamified.mod_three_reducible`
(`ModThree.lean`, the Fontaine/Odlyzko discriminant-bound route)
produces a `Γ ℚ`-stable proper nonzero submodule refuting `hirr`
through `Slop.OddRep.isIrreducible_iff_forall`; at `ℓ ≥ 5`, `hirr` is
refuted by the Family-free Khare–Wintenberger headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`, a PROVEN assembly over the three
sorried literature pillars α/β/γ recorded there — the nodes already
carrying pillar 2, so no NEW weight lands on them).
CIRCULARITY GUARD: respected — neither route touches `Family.lean`
(structurally: neither `ModThree.lean` nor `KhareWintenberger.lean`
imports it or this file). -/
theorem exists_heckeAlgebra_realizations_of_matchesResidualTraces
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {N₀ : ℕ} (_hN₀ : 0 < N₀) {f₀ : CuspForm (Gamma0GL N₀) 2}
    (_hf₀ : IsWeightTwoEigenform N₀ f₀)
    {S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hmatch₀ : MatchesResidualTraces N₀ f₀ ρbar S₀) :
    ∃ (T : Type u) (_ : CommRing T) (_ : TopologicalSpace T)
      (_ : IsTopologicalRing T) (_ : Algebra ℤ_[ℓ] T) (_ : IsLocalRing T)
      (_ : Module.Finite ℤ_[ℓ] T) (_ : Module.Free ℤ_[ℓ] T)
      (_ : IsModuleTopology ℤ_[ℓ] T) (_ : CompactSpace T)
      (t : ℕ → T) (π : T →+* k) (_ : Function.Surjective π)
      (S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
      (_ : ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
        π (t q) =
          - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
      (n : ℕ) (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
      (_ : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y),
      ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
        ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
          (real i).toFun (- t q) := by
  rcases Nat.lt_or_ge ℓ 5 with h5 | h5
  · -- `ℓ < 5`: primality and oddness force `ℓ = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    interval_cases ℓ
    · exact absurd hℓodd (by decide)
    · exact absurd (Fact.out : Nat.Prime 1) (by decide)
    · exact absurd hℓodd (by decide)
    · exfalso
      obtain ⟨W₀, hW₀0, hW₀top, hW₀stable⟩ :=
        IsHardlyRamified.mod_three_reducible W hW hρbar
      have hirr' : ρbar.toRepresentation.IsIrreducible := hirr
      obtain ⟨-, hsub⟩ :=
        (Slop.OddRep.isIrreducible_iff_forall ρbar.toRepresentation).mp hirr'
      rcases hsub W₀
          (fun g v hv => hW₀stable g (Submodule.mem_map_of_mem hv)) with
        hb | ht
      · exact hW₀0 hb
      · exact hW₀top ht
    · exact absurd hℓodd (by decide)
  · -- `ℓ ≥ 5`: the Family-free Khare–Wintenberger headline refutes
    -- irreducibility
    exact absurd hirr
      (not_isIrreducible_of_isHardlyRamified_of_five_le hℓodd h5 hW hρbar)

/-! #### The Nyssen–Rouquier cut behind pillar 3a-ii

Pillar 3a-ii DECOMPOSED, 2026-07-24, isolating the mathematical core
of Carayol's Théorème 2 (equivalently the pseudocharacter theory of
Nyssen and Rouquier) — a residually irreducible trace system over the
local ring `T` is the trace system of an actual representation on
`Fin 2 → T` — from the descent of hardly-ramifiedness along Théorème 1
uniqueness, which splits into its three nontrivial clauses:

* **the compatibility carrier** (`IsRealizationCompatible`,
  definition): the descended representation is tied to the
  realizations by trace AND determinant through every coordinate
  `toFun i` at EVERY group element — exactly the interface Théorème 1
  consumes.
* **3a-ii-α — the construction**
  (`exists_galoisRep_isRealizationCompatible`, sorry node): the
  Carayol/Nyssen–Rouquier core, producing the compatible `ρT`.
* **3a-ii-β — unramifiedness descent**
  (`isUnramifiedAt_of_isRealizationCompatible`, sorry node).
* **3a-ii-γ — flatness descent**
  (`isFlatAt_of_isRealizationCompatible`, sorry node).
* **3a-ii-δ — tameness-at-2 descent**
  (`isTameAtTwo_of_isRealizationCompatible`, sorry node).
* **PROVEN — the assembly** (now pillar 3a-ii's proof body): the rank
  computation, the cyclotomic-determinant clause of
  hardly-ramifiedness (joint injectivity, the realizations'
  determinant clauses, and `AlgHom.commutes` for the `ℤ_ℓ`-algebra
  normalization), and the Frobenius trace clause (joint injectivity
  and the interpolation hypothesis `htr`).

Soundness audit (2026-07-24, inherited from the section docstring):
every leaf keeps the full hypothesis package of 3a-ii — in particular
the irreducible hardly ramified residual `ρbar` — so each remains
classically true (the hypothesis set is classically unsatisfiable),
and the non-vacuous intended discharge is the classical construction
recorded in its docstring. CIRCULARITY GUARD: as everywhere in pillar
3, none of the leaves may be proven through `Family.lean`. -/

/-- **The compatibility carrier of the Nyssen–Rouquier cut**: `ρT` is
*realization-compatible* if through every coordinate `toFun i` its
characteristic-polynomial linear coefficient (`= −trace`,
`charpoly_coeff_one_eq_neg_trace`) and its determinant agree with
those of the `i`-th realization at EVERY element of `Γ ℚ`. This is
the exact interface between the construction leaf 3a-ii-α and the
three descent leaves: by Carayol's Théorème 1 (uniqueness over a
local ring with residually absolutely irreducible reduction), it pins
the `toFun i`-base-change of `ρT` up to conjugacy to `(real i).ρ`,
along which hardly-ramifiedness descends clause by clause. -/
def IsRealizationCompatible {ℓ : ℕ} [Fact ℓ.Prime] {hℓodd : Odd ℓ}
    {T : Type u} [CommRing T] [TopologicalSpace T] [Algebra ℤ_[ℓ] T]
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (ρT : GaloisRep ℚ T (Fin 2 → T)) : Prop :=
  ∀ (g : Field.absoluteGaloisGroup ℚ) (i : Fin n),
    (real i).toFun ((ρT g).charpoly.coeff 1) =
        ((real i).ρ g).charpoly.coeff 1 ∧
      (real i).toFun (LinearMap.det (ρT g)) = LinearMap.det ((real i).ρ g)

/-- **The Carayol/Nyssen–Rouquier construction** (pillar 3a-ii-α;
sorry node — Carayol, *Formes modulaires et représentations
galoisiennes à valeurs dans un anneau local complet*, Contemp. Math.
165 (1994), Théorème 2; Nyssen, Math. Ann. 306 (1996) 257–283;
Rouquier, J. Algebra 180 (1996) 571–586): the glued trace system over
`T` is the trace system of an actual representation on `Fin 2 → T`,
compatible with every realization. Intended construction:
(1) *the pseudocharacter*: `hglue` + `hinj` define `τ : Γ ℚ → T` with
`toFun i (τ g) = (charpoly (ρᵢ g)).coeff 1 = −tr ρᵢ(g)` for all `i`;
set `tr := −τ` and `d g := (tr(g)² − tr(g²))/2` (`2` is a unit: `T`
is a `ℤ_ℓ`-algebra, `ℓ` odd); all dimension-2 pseudocharacter
identities and continuity hold because they hold coordinatewise in
the honest traces of the `ρᵢ` and the joint coordinate map is
injective (`hinj`) — continuity via the closed embedding of the
compact `T` (module-finite free over `ℤ_ℓ` in the module topology)
into `∏ᵢ Oᵢ`;
(2) *residual absolute irreducibility*: `π ∘ tr` agrees with
`tr ρbar` at the Frobenii off `S_T` (`hred`, `htr`), hence everywhere
(Chebotarev density, continuity into the discrete `k`); `ρbar` is
irreducible and odd (its determinant is cyclotomic, evaluating to
`−1` at complex conjugation), hence absolutely irreducible for the
odd `ℓ` (the `OddRep` argument);
(3) *matrix coefficients over the local ring*: complex conjugation
`c` has `tr c = 0` and `d c = −1`, so its residual image has the
distinct eigenvalues `±1` (`ℓ` odd) and the trace system splits along
the lifted idempotent pair into diagonal corner functions
`a, d : Γ ℚ → T` and off-diagonal corner PRODUCTS
`x(g)·y(h) ∈ T` (pseudocharacter polarizations); residual absolute
irreducibility produces `g₀, h₀` with `x(g₀)·y(h₀) ∈ Tˣ` (`T` local —
otherwise the residual trace system would be a sum of two
characters), which normalizes the off-diagonal corners into honest
functions; the pseudocharacter identities are then exactly the `2×2`
multiplication law, yielding a continuous representation
`ρT : Γ ℚ → GL₂(T)` on `Fin 2 → T` with trace `tr` and
determinant `d`;
(4) *compatibility*: `toFun i ∘ tr = tr ρᵢ` by construction, and
`toFun i ∘ d = det ρᵢ` since a rank-2 determinant is determined by
the traces at `g` and `g²` when `2` is a unit — which is
`IsRealizationCompatible` in the `charpoly.coeff 1 = −tr` spelling.
Sound as stated by the section audit (vacuously; the non-vacuous
intended discharge is at the honest Hecke package of 3a-i).
CIRCULARITY GUARD: must not be proven through `Family.lean` (see the
section docstring). -/
theorem exists_galoisRep_isRealizationCompatible
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    (hglue : ∀ g : Field.absoluteGaloisGroup ℚ, ∃ x : T,
      ∀ i, (real i).toFun x = ((real i).ρ g).charpoly.coeff 1) :
    ∃ ρT : GaloisRep ℚ T (Fin 2 → T), IsRealizationCompatible real ρT :=
  sorry

/-- **Unramifiedness descent** (pillar 3a-ii-β; sorry node — Carayol
Théorème 1): the descended representation is unramified outside `2ℓ`.
Intended proof: fix `p ∉ {2, ℓ}` and `σ` in the inertia at `p`. Each
realization `ρᵢ` is unramified at `p` (its `isHardlyRamified` field),
so `ρᵢ(σ) = 1`. By Théorème 1 — over the local `Oᵢ`, a representation
with residually absolutely irreducible reduction is determined up to
conjugacy by its trace, and the residual reduction of `ρᵢ` is
identified with the odd irreducible (hence absolutely irreducible,
`OddRep`) `ρbar` through `hred`/`htr` and Brauer–Nesbitt — the
`toFun i`-base-change of `ρT` is conjugate to `ρᵢ`; hence for every
`i` the base change of `ρT(σ)` is `1`, i.e. `toFun i` maps every
standard-basis matrix entry of `ρT(σ)` to the corresponding entry of
`1`, and joint injectivity `hinj` gives `ρT(σ) = 1` entrywise. Sound
as stated by the section audit. CIRCULARITY GUARD: must not be proven
through `Family.lean` (see the section docstring). -/
theorem isUnramifiedAt_of_isRealizationCompatible
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hcomp : IsRealizationCompatible real ρT) :
    ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ ℓ →
      ρT.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

/-- **Flatness descent** (pillar 3a-ii-γ; sorry node — Raynaud's
closure properties of finite flat prolongations): the descended
representation is flat at `ℓ`. Intended proof: for an open ideal
`I ≤ T`, the finite `Γ ℚ_ℓ`-module `(Fin 2 → T)/I` embeds
`Γ`-equivariantly into a finite product `∏ᵢ (Fin 2 → Oᵢ)/Jᵢ` of
quotients of the realization lattices: the `toFun i`-base-changes of
`ρT` are conjugate to the `ρᵢ` (Théorème 1, as in 3a-ii-β), the joint
coordinate map is injective (`hinj`), and by linear compactness `I`
contains the preimage of a suitable open `∏ᵢ Jᵢ`. Each
`(Fin 2 → Oᵢ)/Jᵢ` has a finite flat prolongation (the `isFlat` field
of the realizations), finite flat group schemes over `ℤ_ℓ` are closed
under finite products, and — `ℓ` odd, absolute ramification `e = 1 <
ℓ − 1` — Raynaud's theorem provides the finite flat prolongation of
the generic-fiber subobject (schematic closure) realizing
`(Fin 2 → T)/I`, and transports it back along the quotient towers to
the given open `I`. Sound as stated by the section audit. CIRCULARITY
GUARD: must not be proven through `Family.lean` (see the section
docstring). -/
theorem isFlatAt_of_isRealizationCompatible
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hcomp : IsRealizationCompatible real ρT) :
    ρT.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) :=
  sorry

/-- **Tameness-at-2 descent** (pillar 3a-ii-δ; sorry node —
Carayol–Saito local–global compatibility, descended along Théorème 1):
the descended representation is upper-triangular at `2` with an
unramified square-trivial rank-1 quotient. Intended proof: each
realization carries a `G₂`-stable surjection `Fin 2 → Oᵢ → Oᵢ` with
unramified square-trivial quotient character `δᵢ` (its `isTameAtTwo`
field). When `ρbar|_{G₂}` has a UNIQUE unramified square-trivial
quotient character, the kernels of these surjections, pulled back
through the Théorème 1 conjugacies (as in 3a-ii-β), are the
`toFun i`-base-changes of one common `T`-line — the kernel of a
surjection `Fin 2 → T → T` glued by joint injectivity and linear
compactness of `T`; in the degenerate split case (`ρbar|_{G₂}` a sum
of two unramified square-trivial characters) choose the lines
compatibly across the realizations through their congruences before
gluing. The quotient action `δ` then satisfies `toFun i ∘ δ = δᵢ` for
every `i`, hence is unramified with `δ² = 1` by joint injectivity
`hinj`. Sound as stated by the section audit. CIRCULARITY GUARD: must
not be proven through `Family.lean` (see the section docstring). -/
theorem isTameAtTwo_of_isRealizationCompatible
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hcomp : IsRealizationCompatible real ρT) :
    ∃ (πq : (Fin 2 → T) →ₗ[T] T) (_ : Function.Surjective πq)
      (δ : GaloisRep ℚ_[2] T T),
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (x : Fin 2 → T),
        πq (ρT.map (algebraMap ℚ ℚ_[2]) g x) = δ g (πq x) ∧
        (AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
              AddSubgroup Z2bar)
            (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) :=
  sorry

/-- **The Carayol descent** (pillar 3a-ii; DECOMPOSED 2026-07-24 — now
a PROVEN assembly over the Nyssen–Rouquier cut above): a residually
irreducible trace system over the local ring `T` — here presented
through its realizations: the glued membership `hglue` (every joint
trace tuple of the realizations comes from `T`, supplied by the
PROVEN Chebotarev gluing above), joint injectivity (making the
`T`-valued trace function unique, i.e. a continuous pseudocharacter
of dimension 2), and `π`-reduction to the traces of the IRREDUCIBLE
`ρbar` (`hred` at Frobenii off `S_T`) — is the trace system of an
actual hardly ramified representation on `Fin 2 → T` (Carayol,
Contemp. Math. 165 (1994), Théorème 2; Nyssen; Rouquier). Assembly:
the construction leaf 3a-ii-α produces `ρT` compatible in trace and
determinant with every realization; the rank clause is the standard
computation; the cyclotomic-determinant clause of hardly-ramifiedness
is PROVEN here (joint injectivity + the realizations' determinant
clauses + `AlgHom.commutes`); the unramifiedness/flatness/tameness
clauses are the descent leaves 3a-ii-β/γ/δ (each descending along
Théorème 1 uniqueness, see their docstrings); and the Frobenius trace
clause is PROVEN from joint injectivity and the interpolation
hypothesis `htr`. Sound as stated by the section audit (vacuously;
the non-vacuous intended discharge is at the honest Hecke package of
3a-i). CIRCULARITY GUARD: must not be proven through `Family.lean`
(see the section docstring). -/
theorem exists_hardlyRamified_galoisRep_of_realizations
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    (hglue : ∀ g : Field.absoluteGaloisGroup ℚ, ∃ x : T,
      ∀ i, (real i).toFun x = ((real i).ρ g).charpoly.coeff 1) :
    ∃ (ρT : GaloisRep ℚ T (Fin 2 → T))
      (hrankT : Module.rank T (Fin 2 → T) = 2)
      (_ : IsHardlyRamified hℓodd hrankT ρT),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
          - t q := by
  classical
  obtain ⟨ρT, hcomp⟩ := exists_galoisRep_isRealizationCompatible hℓodd hW
    hρbar hirr hπ hred real hinj htr hglue
  have hrankT : Module.rank T (Fin 2 → T) = 2 := by simp
  have hdet : ∀ g : Field.absoluteGaloisGroup ℚ, ρT.det g =
      algebraMap ℤ_[ℓ] T
        (cyclotomicCharacter (AlgebraicClosure ℚ) ℓ g.toRingEquiv) := by
    intro g
    refine hinj _ _ fun i => ?_
    rw [GaloisRep.det_apply, (hcomp g i).2, ← GaloisRep.det_apply,
      (real i).isHardlyRamified.det g, AlgHom.commutes]
  refine ⟨ρT, hrankT,
    ⟨hdet,
      isUnramifiedAt_of_isRealizationCompatible hℓodd hW hρbar hirr hπ
        hred real hinj htr hcomp,
      isFlatAt_of_isRealizationCompatible hℓodd hW hρbar hirr hπ
        hred real hinj htr hcomp,
      isTameAtTwo_of_isRealizationCompatible hℓodd hW hρbar hirr hπ
        hred real hinj htr hcomp⟩,
    fun q hq hqS => ?_⟩
  refine hinj _ _ fun i => ?_
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
    (hcomp (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat) i).1,
    ← GaloisRep.charFrob_eq_charpoly_globalFrob, htr i q hq hqS]

/-- **The Hecke-side deformation** (pillar 3a; DECOMPOSED 2026-07-24 —
now a PROVEN assembly over the Carayol cut above: the geometric leaf
3a-i produces the Hecke algebra with its eigenform realizations, the
PROVEN Chebotarev gluing turns their Frobenius-indexed traces into a
`T`-valued trace system on the whole group, the descent leaf 3a-ii
produces the hardly ramified `ρT`, and the residual clause is the sign
bookkeeping `π (−t q) = charFrob.coeff 1`): an irreducible hardly
ramified mod-`ℓ` representation that arises from a weight-2 eigenform
of some level `N₀ ≥ 1` (in the `MatchesResidualTraces` sense) arises
from a whole Hecke-side hardly ramified DEFORMATION: a local
`ℤ_ℓ`-algebra `T`, module-finite and FREE over `ℤ_ℓ` (the classical
`𝕋_𝔪` is finite flat over `ℤ_ℓ`, acting faithfully on the
`𝔪`-localized integral homology of the modular curve; the freeness
component is what excludes degenerate torsion packages such as
`T = k`), with its module topology, together with a hardly ramified
representation `ρT` on `Fin 2 → T` reducing trace-by-trace to `ρbar`
through a surjective `π : T →+* k` away from a finite exceptional set.
Classical construction: optimize the level to the Serre type (Ribet,
*On modular representations of `Gal(ℚ̄/ℚ)` arising from modular
forms*, Invent. Math. 100 (1990); Serre, Duke 1987 §4.1 — for the
hardly ramified type the odd part of the Serre conductor is trivial
and the weight is 2), let `T = 𝕋_𝔪` be the weight-2 Hecke algebra at
the optimized level localized at the maximal ideal cut out by `ρbar`'s
eigensystem through `f₀` (non-Eisenstein because `ρbar` is
irreducible), and let `ρT` be Carayol's `𝕋_𝔪`-valued representation
(Carayol, *Formes modulaires et représentations galoisiennes à valeurs
dans un anneau local complet*, Contemp. Math. 165 (1994) — glued from
the eigenform representations by Chebotarev density plus residual
irreducibility). Hardly-ramifiedness of `ρT`: determinant cyclotomic
(weight 2, trivial nebentypus), unramified outside `2ℓ`, flat at `ℓ`
(weight 2 and level prime to `ℓ`: Fontaine–Laffaille theory;
Conrad–Diamond–Taylor for the general flat bookkeeping), tame at `2`
with unramified square-trivial rank-1 quotient (conductor exponent
`≤ 1` at `2`: Carayol–Saito local–global compatibility).
CIRCULARITY GUARD: must not be proven through `Family.lean` (see the
section docstring). -/
theorem exists_hardlyRamified_heckeDeformation_of_matchesResidualTraces
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {N₀ : ℕ} (hN₀ : 0 < N₀) {f₀ : CuspForm (Gamma0GL N₀) 2}
    (hf₀ : IsWeightTwoEigenform N₀ f₀)
    {S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hmatch₀ : MatchesResidualTraces N₀ f₀ ρbar S₀) :
    ∃ (T : Type u) (_ : CommRing T) (_ : TopologicalSpace T)
      (_ : IsTopologicalRing T) (_ : Algebra ℤ_[ℓ] T) (_ : IsLocalRing T)
      (_ : Module.Finite ℤ_[ℓ] T) (_ : Module.Free ℤ_[ℓ] T)
      (_ : IsModuleTopology ℤ_[ℓ] T)
      (ρT : GaloisRep ℚ T (Fin 2 → T))
      (hrankT : Module.rank T (Fin 2 → T) = 2)
      (_ : IsHardlyRamified hℓodd hrankT ρT)
      (π : T →+* k) (_ : Function.Surjective π)
      (S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
        π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := by
  classical
  -- 3a-i: the Hecke algebra with its eigenform realizations
  obtain ⟨T, iCR, iTop, iTR, iAlg, iLoc, iFin, iFree, iMT, iCpt, t, π, hπ,
    S_T, hred, n, real, hinj, htr⟩ :=
    exists_heckeAlgebra_realizations_of_matchesResidualTraces hℓodd hW hρbar
      hirr hN₀ hf₀ hmatch₀
  letI := iCR
  letI := iTop
  letI := iTR
  letI := iAlg
  letI := iLoc
  letI := iFin
  letI := iFree
  letI := iMT
  letI := iCpt
  -- the PROVEN Chebotarev gluing: the joint trace tuple of the
  -- realizations comes from `T` at EVERY group element
  have hglue := forall_exists_toFun_eq_charpoly_coeff_one real htr
  -- 3a-ii: Carayol descent to a hardly ramified representation over `T`
  obtain ⟨ρT, hrankT, hhr, htrT⟩ :=
    exists_hardlyRamified_galoisRep_of_realizations hℓodd hW hρbar hirr hπ
      hred real hinj htr hglue
  refine ⟨T, iCR, iTop, iTR, iAlg, iLoc, iFin, iFree, iMT, ρT, hrankT, hhr,
    π, hπ, S_T, fun q hq hqS => ?_⟩
  rw [htrT q hq hqS, map_neg, hred q hq hqS, neg_neg]

omit [IsDomain R] in
/-- **Patching: `R = 𝕋`** (pillar 3b; DECOMPOSED 2026-07-24 — now a
PROVEN assembly over the deformation-theoretic pillars of
`Modularity/Patching.lean`; the Taylor–Wiles theorem specialized to
the hardly ramified deformation problem): a
hardly ramified `p`-adic representation `ρ` over `R` whose residual
representation `ρ.baseChange kk` is irreducible and underlies a
Hecke-side hardly ramified deformation `(T, ρT, π)` factors through
that deformation on Frobenius traces: some ring homomorphism
`Φ : T →+* R` carries the trace system of `ρT` to that of `ρ` away
from a finite exceptional set (as everywhere in this file, the
`charFrob` linear coefficient — the trace up to sign — is the carried
quantity). Classically: the hardly ramified conditions are exactly a
deformation problem for `ρ.baseChange kk` over complete Noetherian
local `ℤ_p`-algebras with residue field `kk` — determinant cyclotomic,
unramified outside `2p`, flat at `p` (the `GaloisRep.IsFlatAt`
flat-prolongation condition of `Deformations/RepresentationTheory/`),
tame square-trivial at `2` — representable by a universal ring
`R_univ` (Mazur; residual irreducibility removes the framing); the
trace-generation property of the Hecke deformation gives a surjection
`R_univ ↠ T` (Carayol), which Taylor–Wiles patching — with the flat
condition at `p` handled after Conrad–Diamond–Taylor and Kisin
(*Moduli of finite flat group schemes, and modularity*, Ann. of Math.
170 (2009)) — proves to be an isomorphism; and `ρ` itself, a typed
deformation over the complete Noetherian local ring `R` (module-finite
local `ℤ_p`-algebra with residue field `kk` through `hsurj`), is
classified by a map `R_univ → R`, whose composite with `T ≅ R_univ`
is `Φ`. Literature: Wiles, *Modular elliptic curves and Fermat's Last
Theorem*, Ann. of Math. 141 (1995), ch. 2–3; Taylor–Wiles,
*Ring-theoretic properties of certain Hecke algebras*, ibid.; Diamond,
*The Taylor–Wiles construction and multiplicity one*, Invent. Math.
128 (1997). Abstract-quantification caveat: see the section docstring
— for a packet smaller than the full `𝕋_𝔪` the factorization is not
the literature statement; the leaf remains sound by the section audit,
and its intended discharge is at the full packet of pillar 3a.
CIRCULARITY GUARD: must not be proven through `Family.lean`.

The proof is exactly the recorded classical route, assembled over the
three sorried pillars of `Modularity/Patching.lean` (a module upstream
of this file — the guard is structural: `Lift.lean`'s parallel
deformation vocabulary sits BELOW `Family.lean` and is
import-unreachable): Mazur representability
(`exists_weaklyUniversal_hardlyRamifiedDeformation`) yields a weakly
universal package `(Runiv, ρuniv, πuniv)` with factorization clauses
at the two needed module universes; the `T`-side clause classifies the
Hecke packet (a `HardlyRamifiedFiniteDeformation` literal) by
`ψT : Runiv →+* T`, which Carayol surjectivity
(`surjective_ringHom_of_charFrob_eq`) and Taylor–Wiles injectivity
(`injective_ringHom_of_isWeaklyUniversal`) upgrade to a ring
isomorphism; the `V`-side clause classifies `ρ` itself by
`ψR : Runiv →+* R` — its reduction datum is the PROVEN
`charFrob`/base-change bridge (`charFrob_baseChange`), with empty
exceptional set; and `Φ := ψR ∘ ψT⁻¹`.  (The domain hypothesis on `R`
plays no role in the argument — the deformation vocabulary needs only
the module-finite local `ℤ_p`-algebra structure — so it is omitted.) -/
theorem exists_ringHom_charFrob_eq_of_heckeDeformation
    (hρ : IsHardlyRamified hpodd hv ρ)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[p] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hVbar : Module.rank kk (kk ⊗[R] V) = 2)
    (hρbar : IsHardlyRamified hpodd hVbar (ρ.baseChange kk))
    (hirrbar : (ρ.baseChange kk).IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* kk} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        ((ρ.baseChange kk).charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    ∃ (Φ : T →+* R)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
          Φ ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) := by
  classical
  -- Mazur representability (pillar 3b-i): the weakly universal hardly
  -- ramified deformation package of the residual representation, with
  -- factorization clauses at module universes `u` (the Fin-2-framed
  -- Hecke side) and `v` (the abstract module `V` carrying `ρ`)
  obtain ⟨Runiv, iCR, iTop, iTR, iLoc, iAlg, iNoeth, hadic, hcomplete,
    ρuniv, hranku, hρuniv, πuniv, hπuniv, Suniv, hunivred, hfactU,
    hfactV⟩ :=
    exists_weaklyUniversal_hardlyRamifiedDeformation.{u, v, u, max u v}
      hpodd hVbar hρbar hirrbar
  letI := iCR
  letI := iTop
  letI := iTR
  letI := iLoc
  letI := iAlg
  letI := iNoeth
  -- classify the Hecke-side deformation: `ψT : Runiv →+* T`
  obtain ⟨ψT, hψTalg, hψTπ, SψT, hψT⟩ := hfactU
    { A := T, Vd := Fin 2 → T, rank_eq := hrankT, ρ := ρT,
      isHardlyRamified := hρT, π := π, π_surjective := hπ, S := S_T,
      charFrob_compat := hred }
  -- recast the classification data at the bare Hecke package (the
  -- structure-literal projections reduce definitionally)
  have hψTalg' : ψT.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T :=
    hψTalg
  have hψTπ' : π.comp ψT = πuniv := hψTπ
  have hψT' : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ SψT →
      ψT ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 :=
    hψT
  -- classify `ρ` itself: `ψR : Runiv →+* R` (its reduction datum is
  -- the proven `charFrob`/base-change bridge, with empty exceptional
  -- set; the `ℤ_p`-structure and reduction-map compatibilities of the
  -- classifying map are not needed downstream)
  obtain ⟨ψR, -, -, SψR, hψR⟩ := hfactV
    { A := R, Vd := V, rank_eq := hv, ρ := ρ, isHardlyRamified := hρ,
      π := algebraMap R kk, π_surjective := hsurj, S := ∅,
      charFrob_compat := fun q hq _ => by
        rw [charFrob_baseChange, Polynomial.coeff_map] }
  have hψR' : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ SψR →
      ψR ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 :=
    hψR
  -- Carayol surjectivity (pillar 3b-ii) and Taylor–Wiles injectivity
  -- (pillar 3b-iii): the Hecke-side classifying map is a ring
  -- isomorphism `Runiv ≃+* T`
  have hsurjT : Function.Surjective ψT :=
    surjective_ringHom_of_charFrob_eq hpodd hVbar hρbar hirrbar hadic
      hcomplete hranku hρuniv hπuniv hunivred hrankT hρT hπ hred ψT
      hψTalg' hψTπ' hψT'
  have hinjT : Function.Injective ψT :=
    injective_ringHom_of_isWeaklyUniversal hpodd hVbar hρbar hirrbar
      hadic hcomplete hranku hρuniv hπuniv hunivred hfactU hrankT hρT hπ
      hred ψT hψTalg' hψTπ' hψT'
  -- assemble `Φ := ψR ∘ ψT⁻¹` and chase the traces through `Runiv`
  have hbijT : Function.Bijective ψT := ⟨hinjT, hsurjT⟩
  refine ⟨ψR.comp (RingEquiv.ofBijective ψT hbijT).symm.toRingHom,
    SψT ∪ SψR, fun q hq hqS => ?_⟩
  have hnotT : hq.toHeightOneSpectrumRingOfIntegersRat ∉ SψT :=
    fun h => hqS (Finset.mem_union_left _ h)
  have hnotR : hq.toHeightOneSpectrumRingOfIntegersRat ∉ SψR :=
    fun h => hqS (Finset.mem_union_right _ h)
  have hsymm : (RingEquiv.ofBijective ψT hbijT).symm
      ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
      (ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := by
    rw [RingEquiv.symm_apply_eq, RingEquiv.ofBijective_apply]
    exact (hψT' q hq hnotT).symm
  show (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
    ψR ((RingEquiv.ofBijective ψT hbijT).symm
      ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1))
  rw [hsymm]
  exact (hψR' q hq hnotR).symm

/-- **Points of the Hecke package are embedded eigensystems** (the
Deligne–Serre point leaf of the Carayol cut; sorry node): a
ring-homomorphism point `μ : T →+* ℚ̄_ℓ` of a Hecke-side coefficient
package — `T` with its prime-indexed Hecke elements `t q`, residual
reduction `π` matching the eigensystem of the irreducible hardly
ramified `ρbar`, and hardly ramified eigenform realizations with
jointly injective coordinates interpolating the `−t q` (the exact
output vocabulary of pillar 3a-i,
`exists_heckeAlgebra_realizations_of_matchesResidualTraces`) — carries
the Hecke elements to the embedded coefficient system of a normalized
weight-2 eigenform: `μ (t q) = ι (a_q(f))` away from a finite set.

Intended (non-vacuous) discharge, at the honest `T = 𝕋_𝔪` of 3a-i —
the Deligne–Serre eigensystem decomposition of `𝕋_𝔪 ⊗ ℚ̄_ℓ` read at
one point (Deligne–Serre, Ann. Sci. ÉNS 7 (1974), the Lemme 6.11
shape; Diamond–Shurman §5.8/§6.5):

1. `ker μ` is a prime of `T` (`ℚ̄_ℓ` is a domain); the coordinates
   `(real i).toFun =: λᵢ` are jointly injective, so
   `∏ᵢ ker λᵢ ⊆ ⋂ᵢ ker λᵢ = 0 ⊆ ker μ` and primality selects an `i`
   with `ker λᵢ ⊆ ker μ`: the point factors through the `i`-th
   eigenform component `λᵢ(T) ⊆ Oᵢ`.
2. The factored map is injective on `λᵢ(T)`: `μ` fixes `ℤ`, so `ℓ` is
   not in its kernel, while at the honest instantiation `λᵢ(T)` is an
   order in the `ℓ`-adic coefficient field `Eᵢ` and every nonzero
   prime of such an order contains `ℓ`. Hence the point extends to a
   field embedding `Eᵢ ↪ ℚ̄_ℓ`.
3. `Eᵢ` is the completed Hecke field of the newform component `fᵢ`
   attached to the `i`-th realization by the 3a-i construction, with
   `λᵢ(t q)` the image of `a_q(fᵢ)`; composing the embedding of step 2
   with `heckeField N fᵢ → Eᵢ` gives `ι`, and `μ (t q) = ι (a_q(fᵢ))`
   off the finitely many junk primes.

The abstract `HardlyRamifiedRealization` does not carry its eigenform,
so steps 2–3 are the eigenform-attachment strengthening of 3a-i's
interface: this leaf's discharge must be COORDINATED WITH
`exists_heckeAlgebra_realizations_of_matchesResidualTraces` (whose
classical construction produces the `fᵢ`), either by enriching that
leaf's conclusion or by discharging the two together over a common
construction — and must not duplicate the Hecke-operator development
above (`heckeTransform`/`exists_heckeMatrix_eigenvector`), which
supplies the `IsWeightTwoEigenform` certificates for the constructed
components. Soundness of the abstract quantification: the section
audit (the hypothesis set contains the classically unsatisfiable
irreducible hardly ramified `ρbar`; the construction above is the
non-vacuous intended discharge). CIRCULARITY GUARD: must not be proven
through `Family.lean` (see the section docstring). -/
theorem exists_weightTwoEigenform_of_heckeAlgebra_point
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T] [CompactSpace T]
    {t : ℕ → T} {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π (t q) =
        - (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {n : ℕ} (real : Fin n → HardlyRamifiedRealization ℓ hℓodd T)
    (hinj : ∀ x y : T, (∀ i, (real i).toFun x = (real i).toFun y) → x = y)
    (htr : ∀ (i : Fin n) (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      ((real i).ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (real i).toFun (- t q))
    (μ : T →+* AlgebraicClosure ℚ_[ℓ]) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[ℓ])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        μ (t q) = ι (heckeCoeff N f q) :=
  sorry

/-- **Order-valued points of the Hecke-side deformation are modular**
(the geometric half of pillar 3c; DECOMPOSED 2026-07-24 — now a PROVEN
assembly over the Deligne–Serre point leaf
`exists_weightTwoEigenform_of_heckeAlgebra_point` above, via the
Hecke-algebra route): a point of a Hecke-side hardly ramified
deformation `(T, ρT, π)` of an irreducible hardly ramified `ρbar` that
has been factored through an ORDER — a `ℤ_ℓ`-algebra surjection `φ` of
`T` onto a local domain `O`, module-finite and FREE over `ℤ_ℓ` (an
order in the `ℓ`-adic field `O ⊗ ℚ_ℓ`), followed by an embedding
`j : O ↪ ℚ̄_ℓ` — carries the Frobenius-trace system of `ρT` to the
coefficient system of a normalized weight-2 eigenform under an
embedding of its Hecke field (sign convention as everywhere in this
file: the `charFrob` linear coefficient is `−a_q`). The proven
finite-algebra half of pillar 3c
(`exists_weightTwoEigenform_of_heckeDeformation_point` below) shows
every `ℚ̄_ℓ`-point of `T` factors this way, with `O = T ⧸ ker lam`.

The abstract package `(T, ρT, π)` carries no Hecke structure of its
own, so the proof executes the recorded Deligne–Serre/Carayol route
at the `T = 𝕋_𝔪` instantiation of pillar 3a by RECONSTRUCTING the
honest Hecke package from the residual data and identifying it with
`T` through the universal deformation ring:

1. residual modularity (pillar 2, a proven assembly over the
   Khare–Wintenberger headline and `ModThree`) turns `(ρbar, hirr)`
   into an eigenform match `(N₀, f₀, hmatch₀)`;
2. the Carayol cut behind pillar 3a rebuilds the localized Hecke
   algebra: 3a-i (`exists_heckeAlgebra_realizations_of_...`) gives the
   coefficient package `(T₀, t, π₀)` with its eigenform realizations,
   and the PROVEN Chebotarev gluing plus the descent leaf 3a-ii give
   Carayol's hardly ramified `ρT₀` with `charFrob.coeff 1 = −t q`;
3. Mazur representability (`Patching.lean`, pillar 3b-i) classifies
   BOTH hardly ramified finite deformations of `ρbar` — the given
   abstract `(T, ρT, π)` by `ψ : Runiv →+* T` and the Hecke package
   `(T₀, ρT₀, π₀)` by `ψ₀ : Runiv →+* T₀` — and Carayol surjectivity
   (3b-ii) plus Taylor–Wiles injectivity (3b-iii) upgrade `ψ₀` to a
   ring isomorphism, exactly the `R = 𝕋` mechanism of the pillar-3b
   assembly above;
4. the order point `j ∘ φ` of `T` transports along `ψ ∘ ψ₀⁻¹` to a
   ring-homomorphism point `μ` of the Hecke package, with
   `μ (t q) = − j (φ ((charFrob ρT).coeff 1))` by the two trace
   compatibilities;
5. the Deligne–Serre point leaf evaluates `μ` to an embedded
   eigensystem `μ (t q) = ι (a_q(f))`, which is the required
   conclusion up to the file's sign convention.

The order structure (`O` a domain, `ℤ_ℓ`-free; `j` injective) is
consumed only in forming the point — it is exactly what the proven
finite-algebra half below produces, and the shape the classical
Deligne–Serre reading of a point uses. The alternative discharge for
the abstract package — Kisin's Fontaine–Mazur theorem (*The
Fontaine–Mazur conjecture for `GL₂`*, JAMS 22 (2009)) applied to the
pushforward of `ρT` along `φ`: geometric (hardly ramified), odd
(determinant cyclotomic), residually irreducible (`ker φ ⊆ 𝔪_T` since
`T` is local, so the residue field of `O` is `T ⧸ 𝔪_T ≅ k` and the
reduction is `ρbar`) — remains recorded as the route NOT taken: the
Hecke-algebra route consumes only leaves already in the tree plus the
sharply-scoped point leaf above.
CIRCULARITY GUARD: must not be proven through `Family.lean`. -/
theorem exists_weightTwoEigenform_of_heckeDeformation_order_point
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hℓodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {O : Type u} [CommRing O] [IsDomain O] [Algebra ℤ_[ℓ] O]
    [IsLocalRing O] [Module.Finite ℤ_[ℓ] O] [Module.Free ℤ_[ℓ] O]
    (φ : T →ₐ[ℤ_[ℓ]] O) (_hφ : Function.Surjective φ)
    (j : O →+* AlgebraicClosure ℚ_[ℓ]) (_hj : Function.Injective j) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[ℓ])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        j (φ ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)) =
          - ι (heckeCoeff N f q) := by
  classical
  -- pillar 2 (proven assembly): residual modularity of `ρbar`
  obtain ⟨N₀, hN₀, f₀, hf₀, S₀, hmatch₀⟩ :=
    exists_weightTwoEigenform_residual_of_isIrreducible hℓodd hW hρbar hirr
  -- 3a-i: the honest Hecke coefficient package with its realizations
  obtain ⟨T₀, iCR₀, iTop₀, iTR₀, iAlg₀, iLoc₀, iFin₀, iFree₀, iMT₀, iCpt₀,
    t, π₀, hπ₀, S_T₀, hred₀, n, real, hinj₀, htr₀⟩ :=
    exists_heckeAlgebra_realizations_of_matchesResidualTraces hℓodd hW hρbar
      hirr hN₀ hf₀ hmatch₀
  letI := iCR₀
  letI := iTop₀
  letI := iTR₀
  letI := iAlg₀
  letI := iLoc₀
  letI := iFin₀
  letI := iFree₀
  letI := iMT₀
  letI := iCpt₀
  -- the PROVEN Chebotarev gluing and the Carayol descent 3a-ii:
  -- Carayol's hardly ramified representation over the Hecke package
  have hglue := forall_exists_toFun_eq_charpoly_coeff_one real htr₀
  obtain ⟨ρT₀, hrankT₀, hρT₀, htrT₀⟩ :=
    exists_hardlyRamified_galoisRep_of_realizations hℓodd hW hρbar hirr hπ₀
      hred₀ real hinj₀ htr₀ hglue
  -- its reduction datum (sign bookkeeping, as in the pillar-3a assembly)
  have hred₀' : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T₀ →
      π₀ ((ρT₀.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := by
    intro q hq hqS
    rw [htrT₀ q hq hqS, map_neg, hred₀ q hq hqS, neg_neg]
  -- Mazur representability (Patching pillar 3b-i): the weakly universal
  -- package classifying both hardly ramified deformations of `ρbar`
  obtain ⟨Runiv, iuCR, iuTop, iuTR, iuLoc, iuAlg, iuNoeth, hadic, hcomplete,
    ρuniv, hranku, hρuniv, πuniv, hπuniv, Suniv, hunivred, hfactU,
    hfactV⟩ :=
    exists_weaklyUniversal_hardlyRamifiedDeformation hℓodd hW hρbar hirr
  letI := iuCR
  letI := iuTop
  letI := iuTR
  letI := iuLoc
  letI := iuAlg
  letI := iuNoeth
  -- classify the given abstract package: `ψ : Runiv →+* T` (only the
  -- trace clause is consumed downstream)
  obtain ⟨ψ, -, -, Sψ, hψ⟩ := hfactU
    { A := T, Vd := Fin 2 → T, rank_eq := hrankT, ρ := ρT,
      isHardlyRamified := hρT, π := π, π_surjective := hπ, S := S_T,
      charFrob_compat := hred }
  have hψ' : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := hψ
  -- classify the Hecke package: `ψ₀ : Runiv →+* T₀`
  obtain ⟨ψ₀, hψ₀alg, hψ₀π, Sψ₀, hψ₀⟩ := hfactV
    { A := T₀, Vd := Fin 2 → T₀, rank_eq := hrankT₀, ρ := ρT₀,
      isHardlyRamified := hρT₀, π := π₀, π_surjective := hπ₀, S := S_T₀,
      charFrob_compat := hred₀' }
  have hψ₀alg' : ψ₀.comp (algebraMap ℤ_[ℓ] Runiv) = algebraMap ℤ_[ℓ] T₀ :=
    hψ₀alg
  have hψ₀π' : π₀.comp ψ₀ = πuniv := hψ₀π
  have hψ₀' : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ₀ →
      ψ₀ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT₀.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := hψ₀
  -- Carayol surjectivity and Taylor–Wiles injectivity (Patching pillars
  -- 3b-ii/3b-iii): `ψ₀` is a ring isomorphism `Runiv ≃+* T₀`
  have hsurj₀ : Function.Surjective ψ₀ :=
    surjective_ringHom_of_charFrob_eq hℓodd hW hρbar hirr hadic hcomplete
      hranku hρuniv hπuniv hunivred hrankT₀ hρT₀ hπ₀ hred₀' ψ₀ hψ₀alg'
      hψ₀π' hψ₀'
  have hinjψ₀ : Function.Injective ψ₀ :=
    injective_ringHom_of_isWeaklyUniversal hℓodd hW hρbar hirr hadic
      hcomplete hranku hρuniv hπuniv hunivred hfactV hrankT₀ hρT₀ hπ₀
      hred₀' ψ₀ hψ₀alg' hψ₀π' hψ₀'
  have hbij₀ : Function.Bijective ψ₀ := ⟨hinjψ₀, hsurj₀⟩
  -- transport the order point `j ∘ φ` of `T` along `ψ ∘ ψ₀⁻¹` to a
  -- point of the Hecke package and evaluate the Deligne–Serre leaf
  obtain ⟨N, hN, f, hf, ι, S_f, hpt⟩ :=
    exists_weightTwoEigenform_of_heckeAlgebra_point hℓodd hW hρbar hirr hπ₀
      hred₀ real hinj₀ htr₀
      (((j.comp φ.toRingHom).comp ψ).comp
        (RingEquiv.ofBijective ψ₀ hbij₀).symm.toRingHom)
  refine ⟨N, hN, f, hf, ι, S_T₀ ∪ Sψ ∪ Sψ₀ ∪ S_f, fun q hq hqS => ?_⟩
  have hq₀ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T₀ := fun h =>
    hqS (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ h)))
  have hqψ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ := fun h =>
    hqS (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ h)))
  have hqψ₀ : hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ₀ := fun h =>
    hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqf : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_f := fun h =>
    hqS (Finset.mem_union_right _ h)
  -- `ψ₀⁻¹` carries `t q` to `−(charFrob coeff)` of the universal
  -- representation
  have hsymm : (RingEquiv.ofBijective ψ₀ hbij₀).symm (t q) =
      - ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) := by
    rw [RingEquiv.symm_apply_eq, map_neg, RingEquiv.ofBijective_apply,
      hψ₀' q hq hqψ₀, htrT₀ q hq hq₀, neg_neg]
  rw [← hpt q hq hqf]
  show j (φ ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)) =
    - (j (φ (ψ ((RingEquiv.ofBijective ψ₀ hbij₀).symm (t q)))))
  rw [hsymm, map_neg, map_neg, map_neg, hψ' q hq hqψ, neg_neg]

/-- **Modular points of the Hecke-side deformation** (pillar 3c;
DECOMPOSED 2026-07-24 — now a PROVEN assembly over the order-point
leaf above): every `ℚ̄_ℓ`-valued point `lam` of a Hecke-side hardly
ramified deformation `(T, ρT, π)` of an irreducible hardly ramified
`ρbar` carries the Frobenius-trace system of `ρT` to the coefficient
system of a normalized weight-2 eigenform under an embedding of its
Hecke field (sign convention as everywhere in this file: the
`charFrob` linear coefficient is `−a_q`).

The PROVEN finite-algebra half ("points factor through orders", the
points-as-projections content of the Deligne–Serre decomposition of
`𝕋_𝔪 ⊗ ℚ̄_ℓ` in kernel form): the kernel of `lam` is a prime of `T`
(`ℚ̄_ℓ` is a domain), so `O := T ⧸ ker lam` is a domain, local
(quotient of the local `T`), module-finite over `ℤ_ℓ`, and of
characteristic zero — any ring homomorphism from `ℤ_ℓ` to the
characteristic-zero field `ℚ̄_ℓ` is injective, since a nonzero
`z ∈ ℤ_ℓ` is a unit times `ℓ^n` (DVR) and `ℓ` maps to `ℓ ≠ 0` — so
`O` is `ℤ_ℓ`-torsion-free, hence FREE over the DVR `ℤ_ℓ`: an order
in an `ℓ`-adic field. `lam` factors through it as the kernel-lift
embedding `j : O ↪ ℚ̄_ℓ` composed with the quotient surjection
`φ : T ↠ O`. The remaining geometric half — order-valued points are
eigenform systems (Deligne–Serre on `𝕋_𝔪`, Kisin's Fontaine–Mazur
for the abstract package; see its docstring) — is the sorried leaf
`exists_weightTwoEigenform_of_heckeDeformation_order_point` above,
evaluated at `(O, φ, j)`.
CIRCULARITY GUARD: must not be proven through `Family.lean`. -/
theorem exists_weightTwoEigenform_of_heckeDeformation_point
    {ℓ : ℕ} (hℓodd : Odd ℓ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hℓodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[ℓ] T] [IsLocalRing T] [Module.Finite ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [IsModuleTopology ℤ_[ℓ] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hℓodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (lam : T →+* AlgebraicClosure ℚ_[ℓ]) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[ℓ])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        lam ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          - ι (heckeCoeff N f q) := by
  -- The finite-algebra half, proven here: `lam` factors through the
  -- order `O := T ⧸ ker lam`.
  -- `ker lam` is prime since `ℚ̄_ℓ` is a domain, so `O` is a domain.
  haveI : (RingHom.ker lam).IsPrime := RingHom.ker_isPrime lam
  -- `O` is local as a nontrivial quotient of the local ring `T`.
  haveI : IsLocalRing (T ⧸ RingHom.ker lam) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective
  -- `ℤ_ℓ → O` is injective: composed with the kernel-lift embedding
  -- into `ℚ̄_ℓ` it is a ring homomorphism from the DVR `ℤ_ℓ` to a
  -- characteristic-zero field, which kills no unit multiple of `ℓ^n`.
  have hinj : Function.Injective
      (algebraMap ℤ_[ℓ] (T ⧸ RingHom.ker lam)) := by
    have hcomp : Function.Injective
        ((RingHom.kerLift lam).comp
          (algebraMap ℤ_[ℓ] (T ⧸ RingHom.ker lam))) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      by_contra hz0
      obtain ⟨n, u, hu⟩ :=
        IsDiscreteValuationRing.associated_pow_irreducible hz0
          PadicInt.prime_p.irreducible
      have hpn : ((RingHom.kerLift lam).comp
          (algebraMap ℤ_[ℓ] (T ⧸ RingHom.ker lam))) ((ℓ : ℤ_[ℓ]) ^ n) = 0 := by
        rw [← hu, map_mul, hz, zero_mul]
      rw [map_pow, map_natCast] at hpn
      exact Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
        (pow_eq_zero_iff'.mp hpn).1
    exact fun a b hab => hcomp (by simp [RingHom.comp_apply, hab])
  -- Hence `O` is `ℤ_ℓ`-torsion-free (it is a domain), hence free
  -- over the DVR `ℤ_ℓ`: an order in an `ℓ`-adic field.
  haveI : Module.IsTorsionFree ℤ_[ℓ] (T ⧸ RingHom.ker lam) := by
    refine ⟨fun r hr => ?_⟩
    have hr0 : algebraMap ℤ_[ℓ] (T ⧸ RingHom.ker lam) r ≠ 0 :=
      fun h0 => hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    intro a b hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hr0 hab
  haveI : Module.Free ℤ_[ℓ] (T ⧸ RingHom.ker lam) :=
    Module.free_of_finite_type_torsion_free'
  -- The geometric half: evaluate the order-point leaf at
  -- `(T ⧸ ker lam, quotient map, kernel-lift embedding)`.
  obtain ⟨N, hN, f, hf, ι, S, hpt⟩ :=
    exists_weightTwoEigenform_of_heckeDeformation_order_point hℓodd hW hρbar
      hirr hrankT hρT hπ hred
      (Ideal.Quotient.mkₐ ℤ_[ℓ] (RingHom.ker lam))
      (Ideal.Quotient.mkₐ_surjective _ _)
      (RingHom.kerLift lam) (RingHom.kerLift_injective lam)
  refine ⟨N, hN, f, hf, ι, S, fun q hq hqS => ?_⟩
  simpa [Ideal.Quotient.mkₐ_eq_mk, RingHom.kerLift_mk] using hpt q hq hqS

omit [IsDomain R] in
/-- **Modularity lifting** (pillar 3; DECOMPOSED 2026-07-24 — now a
PROVEN assembly over the Taylor–Wiles cut of the section above; the
R = T shadow, residually irreducible case): a hardly ramified `p`-adic
representation whose residual representation is irreducible and
modular (in the `MatchesResidualTraces` sense) is itself modular: its
Frobenius traces arise, away from a finite set of places, from a
single weight-2 eigenform under a single embedding of its Hecke field.
The hardly ramified hypotheses on `ρ` instantiate exactly the
classical deformation conditions of the FLT blueprint's lifting
theorem (ch. 4, "`S`-good" with `S = {2}`): determinant cyclotomic,
unramified outside `2p`, flat at `p` (weight 2), tame at `2` with
unramified square-trivial rank-1 quotient. Literature: Wiles, *Modular
elliptic curves and Fermat's Last Theorem*, Ann. of Math. 141 (1995),
ch. 3 and 5; Taylor–Wiles, *Ring-theoretic properties of certain Hecke
algebras*, ibid. (the patching input); Conrad–Diamond–Taylor and
Diamond's refinements for the flat deformation condition at `p`; in
the "geometric odd irreducible 2-dimensional `p`-adic representations
of `Γ ℚ` are modular" formulation this is the relevant case of the
Fontaine–Mazur conjecture (Kisin, *The Fontaine–Mazur conjecture for
GL₂*, JAMS 22 (2009); Pan for the `p = 3` corners). The decomposition
aligns the deformation-problem bookkeeping with
`Fermat/FLT/Deformations/` (`GaloisRep`, `IsFlatAt`/flat
prolongations) as planned: the proof runs pillar 3a on the residual
data, pillar 3b against `ρ` itself, and evaluates pillar 3c at the
`ℚ̄_p`-point `(algebraMap R ℚ̄_p).comp Φ` of the Hecke-side
deformation; the residual hardly-ramifiedness and the surjectivity of
the residue map are consumed by 3a/3b exactly as the Taylor–Wiles
hypotheses. -/
theorem exists_weightTwoEigenform_trace_eq_of_matchesResidualTraces
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (_hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (_hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[p] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hVbar : Module.rank kk (kk ⊗[R] V) = 2)
    (hρbar : IsHardlyRamified hpodd hVbar (ρ.baseChange kk))
    (hirrbar : (ρ.baseChange kk).IsIrreducible)
    {N₀ : ℕ} (hN₀ : 0 < N₀) {f₀ : CuspForm (Gamma0GL N₀) 2}
    (hf₀ : IsWeightTwoEigenform N₀ f₀)
    {S₀ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hmatch₀ : MatchesResidualTraces N₀ f₀ (ρ.baseChange kk) S₀) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - ι (heckeCoeff N f q) := by
  classical
  -- pillar 3a: the Hecke-side hardly ramified deformation of the
  -- residual representation
  obtain ⟨T, iCR, iTop, iTR, iAlg, iLoc, iFin, iFree, iMT, ρT, hrankT, hρT,
    π, hπ, S_T, hredT⟩ :=
    exists_hardlyRamified_heckeDeformation_of_matchesResidualTraces hpodd
      hVbar hρbar hirrbar hN₀ hf₀ hmatch₀
  letI := iCR
  letI := iTop
  letI := iTR
  letI := iAlg
  letI := iLoc
  letI := iFin
  letI := iFree
  letI := iMT
  -- pillar 3b: patching — `ρ` factors through the Hecke-side
  -- deformation on Frobenius traces
  obtain ⟨Φ, SΦ, hΦ⟩ :=
    exists_ringHom_charFrob_eq_of_heckeDeformation hpodd hv hρ hsurj hVbar
      hρbar hirrbar hrankT hρT hπ hredT
  -- pillar 3c: the resulting `ℚ̄_p`-point of the deformation is an
  -- eigenform system
  obtain ⟨N, hN, f, hf, ι, Sf, hpt⟩ :=
    exists_weightTwoEigenform_of_heckeDeformation_point hpodd hVbar hρbar
      hirrbar hrankT hρT hπ hredT
      ((algebraMap R (AlgebraicClosure ℚ_[p])).comp Φ)
  refine ⟨N, hN, f, hf, ι, SΦ ∪ Sf, fun q hq hqS => ?_⟩
  rw [Polynomial.coeff_map,
    hΦ q hq fun h => hqS (Finset.mem_union_left _ h)]
  exact hpt q hq fun h => hqS (Finset.mem_union_right _ h)

/-! ### The Eisenstein cut behind the residually reducible branch

Pillar 4's `p ≥ 5` leaf DECOMPOSED (2026-07-24), following the audit
below, into the LEVEL-2 EISENSTEIN CONTRADICTION (Mazur) — not into
Skinner–Wiles patching machinery.

AUDIT (2026-07-24, both directions):

* *Reachability.* The leaf IS genuinely reachable with formally
  unrefuted hypotheses: the dichotomy in
  `exists_weightTwoEigenform_trace_eq_of_isIrreducible` performs
  `by_cases` on residual irreducibility with NO information about
  which branch obtains — pillar 1's residue field is abstract, and
  `Family.lean`'s trace atoms invoke the chain on arbitrary hardly
  ramified `p`-adic representations (compatible-family members) with
  no residual data. Nor can `Reducible.lean`'s B5
  (`not_isIrreducible_of_isHardlyRamified`, which makes every hardly
  ramified residual representation at `ℓ ≥ 5` reducible) be invoked
  to trivialize either branch: B5 is DOWNSTREAM of this file (its
  proof runs through `Lift.lean` and `Family.lean`, which consume the
  assemblies here), so any such route is circular. A
  hypothesis-narrowing redesign (threading residual irreducibility of
  the `Lift.lean` lift through the chain so the reducible branch is
  never taken) would rewrite proven consumers' signatures across
  three files and is rejected.

* *Content.* The leaf's hypothesis set — hardly ramified `p`-adic
  `ρ`, irreducible over `ℚ̄_p`, residually REDUCIBLE, `p ≥ 5` — is
  classically EMPTY, and, unlike the residually irreducible branch
  (where emptiness is the full Wiles chain), its emptiness has a
  classical proof strictly shallower than Skinner–Wiles: Mazur's
  level-2 Eisenstein argument. The residual Jordan–Hölder characters
  are `1` and `ω = χ̄_cyc` (pillar E1 below); Ribet's lattice lemma
  converts irreducibility over `ℚ̄_p` into a NONSPLIT hardly ramified
  extension with trivial sub-character (pillar E2); and that
  extension group vanishes at `p ≥ 5` (pillar E3 — Herbrand's theorem
  at `B₂ = 1/6` plus the triviality of the conductor-2 ray; in
  Hecke-algebra language, the index of the level-`N` Eisenstein ideal
  is `num((N−1)/12)`, which is `1` at `N = 2`). Full Skinner–Wiles
  (Publ. Math. IHÉS 89, 1999) or Pan (JAMS 35, 2022) is needed only
  at general conductor; at conductor dividing `2` any honest
  modularity conclusion is contradiction-shaped anyway
  (`S₂(Γ₀(2)) = 0` is proven above) — the same boundary phenomenon
  audited at pillar 5. The leaf is therefore discharged by
  contradiction, exactly like its `p = 3` instance (3-adic
  classification), with the depth living in the three sorried
  Eisenstein pillars E1–E3.

* *`p ≥ 5` is load-bearing:* pillar E3 is FALSE at `p = 3` — there
  `ω^{−1} = ω`, and the Kummer class of `2` (the extension cut out by
  `ℚ(μ₃, 2^{1/3})`: unramified outside `{2, 3}`, tame at `2` since
  the degree `3` is odd, flat at `3`) is a nonsplit hardly ramified
  inhabitant; it is the same class `ModThree.lean`'s classification
  lives with. The `2`-ramified escape closes exactly when
  `p ∤ 2² − 1 = 3`.

CIRCULARITY GUARD (inherited, mandatory): E1–E3 must not be proven
through `Family.lean` (it consumes this file's assemblies) nor
through `Reducible.lean`'s B5 (downstream of this file through
`Lift.lean` and `Family.lean`). -/

/-- **Residual Eisenstein classification** (Eisenstein pillar E1;
sorry node — the conductor-`2p` character pinning): a REDUCIBLE
hardly ramified mod-`p` representation over a finite field `k` is
triangular in a suitable basis with diagonal CHARACTERS, one of which
— the sub-character or the quotient character — is TRIVIAL. Classical
proof (the residual instance of the character analysis proven one
level up in `Family.lean`, which the circularity guard forbids
consuming): reducibility over the field `k` yields a stable line,
hence a triangular basis with diagonal characters `χsub, χquo`; at
`2` the hardly ramified quotient-line character is unramified and
`det = χ̄_cyc` is unramified, so BOTH diagonal characters are
unramified at `2` (the local Jordan–Hölder multiset at `2` is
`{κ, δ}` with `δ` unramified and `κ·δ = det` unramified on inertia);
a character of `Gal(ℚ̄/ℚ)` with values in `k^×` (order prime to `p`)
unramified outside `p` factors through `Gal(ℚ(μ_p)/ℚ)` — the ray
class group of `ℚ` of conductor `2p^k∞` is `(ℤ/2p^k)^× ≅ (ℤ/p^k)^×`
(Kronecker–Weber; Neukirch, *Algebraic Number Theory*, VI §6–7), and
the `p`-part dies in `k^×` — so each diagonal character is a power
`ω^i` of the mod-`p` cyclotomic character; flatness at `p` restricts
the inertia weights of the Jordan–Hölder characters of the generic
fibre of a finite flat group scheme over `ℤ_p` (`e = 1 < p − 1`) to
`{ω⁰, ω¹}` (Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull.
Soc. Math. France 102 (1974), 3.3.2; Serre, Duke Math. J. 54 (1987),
§2.4, 4.1), while `det = χ̄_cyc` forces `i + j ≡ 1 mod (p − 1)`;
hence `{χsub, χquo} = {1, ω}` and in particular one of the two is
trivial. Soundness (audit 2026-07-24): the hypothesis set is
genuinely inhabited (`1 ⊕ χ̄_cyc` itself), and the conclusion holds
for every inhabitant by the argument cited; `p ≥ 5` is NOT needed —
oddness gives `e = 1 < p − 1`. -/
theorem exists_residual_triangular_of_not_isIrreducible
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hred : ¬ ρbar.IsIrreducible) :
    ∃ (b : Module.Basis (Fin 2) k W)
      (χsub χquo : Field.absoluteGaloisGroup ℚ →* k)
      (cc : Field.absoluteGaloisGroup ℚ → k),
      (∀ g, LinearMap.toMatrix b b (ρbar g) = !![χsub g, cc g; 0, χquo g]) ∧
      ((∀ g, χsub g = 1) ∨ (∀ g, χquo g = 1)) :=
  sorry

/-- **The Eisenstein lattice** (Eisenstein pillar E2; sorry node —
Ribet's lemma with prescribed order, plus integral transfer of the
hardly ramified conditions): a hardly ramified `p`-adic
representation that is irreducible over `ℚ̄_p` but residually
reducible — with the residual triangular data of pillar E1 — reduces,
on a suitable stable lattice over the valuation ring of `Frac R`
(finite over `ℚ_p` since `R` is a module-finite `ℤ_p`-domain), to a
NONSPLIT hardly ramified extension with TRIVIAL sub-character: in
matrix form `!![1, cc g; 0, χ g]` on the standard basis of `kk'²`,
with no `a` satisfying `∀ g, cc g = (χ g − 1) a` (the coboundary
criterion: such an `a` marks a stable complement `e₁ + a·e₀`).
Classical construction: `E := Frac R` is a finite extension of `ℚ_p`;
`ρ ⊗ E` is irreducible (irreducibility descends from `ℚ̄_p`); its
residual semisimplification is `1 ⊕ ω` by the E1 data on the given
reduction (independence of the reduction: Brauer–Nesbitt); the two
characters are DISTINCT (`ω ≠ 1` for odd `p`), so Ribet's lemma in
its prescribed-order form — Ribet, *A modular construction of
unramified `p`-extensions of `ℚ(μ_p)`*, Invent. Math. 34 (1976),
Prop. 2.1; Bellaïche–Chenevier, *Families of Galois representations
and Selmer groups*, Astérisque 324 (2009), ch. 1: for an irreducible
generic representation BOTH orderings are realized by suitable stable
lattices — produces a stable `𝒪_E`-lattice whose reduction is
nonsplit with sub-character `1`. The reduction is hardly ramified by
the same residual-transfer arguments as pillar 1 (`Residual.lean`):
determinant and outside-`2p` unramifiedness pass to any reduction;
flatness at `p` passes to stable lattices and their reductions
(scheme-theoretic closure — sub- and quotient objects of finite flat
group schemes over `ℤ_p` are finite flat; Raynaud, loc. cit.; Tate in
Cornell–Silverman–Stevens ch. V); the tame quotient line at `2`
saturates inside the new lattice with the same unramified
square-trivial character. Soundness (audit 2026-07-24): the
hypothesis set is classically empty (section audit), but the cited
derivation is hypothesis-honest — every step consumes exactly the
listed hypotheses and none consumes the emptiness; `p ≥ 5` is not
consumed (oddness gives `ω ≠ 1`), so it is not demanded. -/
theorem exists_eisenstein_nonsplit_lattice_of_residually_reducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[p] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (b : Module.Basis (Fin 2) kk (kk ⊗[R] V))
    (χsub χquo : Field.absoluteGaloisGroup ℚ →* kk)
    (cc₀ : Field.absoluteGaloisGroup ℚ → kk)
    (htri₀ : ∀ g, LinearMap.toMatrix b b ((ρ.baseChange kk) g) =
      !![χsub g, cc₀ g; 0, χquo g])
    (hdisj : (∀ g, χsub g = 1) ∨ (∀ g, χquo g = 1)) :
    ∃ (kk' : Type u) (_ : Field kk') (_ : Finite kk')
      (_ : Algebra ℤ_[p] kk') (_ : TopologicalSpace kk')
      (_ : DiscreteTopology kk') (_ : IsTopologicalRing kk')
      (ρE : GaloisRep ℚ kk' (Fin 2 → kk'))
      (hrankE : Module.rank kk' (Fin 2 → kk') = 2)
      (_ : IsHardlyRamified hpodd hrankE ρE)
      (χ : Field.absoluteGaloisGroup ℚ →* kk')
      (cc : Field.absoluteGaloisGroup ℚ → kk'),
      (∀ g, LinearMap.toMatrix (Pi.basisFun kk' (Fin 2))
          (Pi.basisFun kk' (Fin 2)) (ρE g) = !![1, cc g; 0, χ g]) ∧
      ¬ ∃ a : kk', ∀ g, cc g = (χ g - 1) * a :=
  sorry

/-- **Level-2 Eisenstein vanishing** (Eisenstein pillar E3; sorry node
— Mazur/Herbrand, the deep arithmetic input of the residually
reducible branch): a hardly ramified mod-`p` extension with TRIVIAL
sub-character SPLITS when `p ≥ 5` — some `a : kk'` writes the
upper-right entry as the coboundary `cc g = (χ g − 1) a`. Classical
proof: the extension class lives in `H¹(ℚ, ω^{−1})` (the determinant
field of `IsHardlyRamified` pins the quotient character `χ` to
`ω = χ̄_cyc`, and the twist `Hom(χ, 1)` is `ω^{−1}`), subject to:
unramified outside `{2, p}` (the hardly ramified hypothesis); LOCALLY
TRIVIAL at `p` — the flat model is an extension of the connected
`μ_p` by the étale `ℤ/p` over `ℤ_p`, split by its own connected–étale
sequence (Tate, in Cornell–Silverman–Stevens ch. V; equivalently
`ω^{−1} = ω^{p−2}` has inertia weight `p − 2 ∉ {0, 1}` for `p ≥ 5`,
outside Raynaud's flat range); and UNRAMIFIED at `2` — for
`ℓ = 2 ≠ p` the ramified quotient of `H¹(ℚ_2, ω^{−1})` is controlled
by `Frob₂`-equivariance on tame inertia, nonzero only when
`ω²(Frob₂) = 1`, i.e. `p ∣ 2² − 1 = 3`, excluded by `hp5` (see the
section audit for the genuine `p = 3` counterexample, the Kummer
class of `2`). The surviving group is `Hom_{Gal}` out of the
`ω^{−1}`-eigenspace of `Cl(ℚ(μ_p)) ⊗ 𝔽_p`, which VANISHES by
Herbrand's theorem: `ω^{−1} = ω^{1−2}` and
`p ∤ num(B₂) = num(1/6) = 1` (Herbrand 1932; Washington,
*Introduction to Cyclotomic Fields*, Thm. 6.17; Ribet, Invent. Math.
34 (1976) is the unused converse). Equivalently, in Hecke-algebra
language: the index of the Eisenstein ideal at prime level `N` is
`num((N−1)/12)` (Mazur, *Modular curves and the Eisenstein ideal*,
Publ. Math. IHÉS 47 (1977)), which is `1` at `N = 2` — no Eisenstein
congruence exists at conductor `2`, which is why the Skinner–Wiles
congruence machinery has nothing to produce here and the residually
reducible branch terminates in this vanishing instead. Soundness
(audit 2026-07-24): the hypothesis set is inhabited (split extensions
`1 ⊕ ω` in triangular form), the conclusion is true of every
inhabitant by the vanishing just cited, and the statement is exactly
`H¹_{hardly ramified}(ℚ, ω^{−1}) = 0` in matrix coordinates. -/
theorem eisenstein_trivial_sub_extension_splits_of_five_le
    (hp5 : 5 ≤ p)
    {kk' : Type u} [Field kk'] [Finite kk'] [Algebra ℤ_[p] kk']
    [TopologicalSpace kk'] [DiscreteTopology kk'] [IsTopologicalRing kk']
    {ρE : GaloisRep ℚ kk' (Fin 2 → kk')}
    (hrankE : Module.rank kk' (Fin 2 → kk') = 2)
    (hρE : IsHardlyRamified hpodd hrankE ρE)
    (χ : Field.absoluteGaloisGroup ℚ →* kk')
    (cc : Field.absoluteGaloisGroup ℚ → kk')
    (htri : ∀ g, LinearMap.toMatrix (Pi.basisFun kk' (Fin 2))
      (Pi.basisFun kk' (Fin 2)) (ρE g) = !![1, cc g; 0, χ g]) :
    ∃ a : kk', ∀ g, cc g = (χ g - 1) * a :=
  sorry

/-- **The residually reducible branch at `p ≥ 5`** (pillar 4 leaf;
PROVEN 2026-07-24 as an assembly over the Eisenstein cut E1–E3 above
— see the section docstring for the full audit): a hardly ramified
`p`-adic representation, `p ≥ 5`, irreducible over `ℚ̄_p` with
REDUCIBLE residual representation is modular in the trace sense of
pillar 3 — vacuously: the hypotheses are contradictory, and the
contradiction is Mazur's level-2 Eisenstein argument. E1 pins the
residual triangular characters to `{1, ω}`; E2 (Ribet's lemma)
produces a nonsplit hardly ramified extension with trivial
sub-character; E3 (Herbrand/Mazur) splits every such extension at
`p ≥ 5`. This mirrors the `p = 3` discharge in the pillar-4 assembly
below (3-adic classification), with the Skinner–Wiles/Pan citations
of the former leaf docstring now localized in the E2/E3 pillars where
their conductor-2 content actually lives (Skinner–Wiles, Publ. Math.
IHÉS 89 (1999); Pan, JAMS 35 (2022); Mazur, Publ. Math. IHÉS 47
(1977)). -/
theorem exists_weightTwoEigenform_trace_eq_of_residually_reducible_of_five_le
    (hp5 : 5 ≤ p)
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (_hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[p] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hVbar : Module.rank kk (kk ⊗[R] V) = 2)
    (hρbar : IsHardlyRamified hpodd hVbar (ρ.baseChange kk))
    (hred : ¬ (ρ.baseChange kk).IsIrreducible) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - ι (heckeCoeff N f q) := by
  -- E1: the residual triangular characters, one of them trivial
  obtain ⟨b, χsub, χquo, cc₀, htri₀, hdisj⟩ :=
    exists_residual_triangular_of_not_isIrreducible hpodd hVbar hρbar hred
  -- E2: Ribet's lemma — a nonsplit hardly ramified extension with
  -- trivial sub-character
  obtain ⟨kk', hF, hFin, hAlg, hTop, hDisc, hTR, ρE, hrankE, hρE, χ, cc,
    htri, hnonsplit⟩ :=
    exists_eisenstein_nonsplit_lattice_of_residually_reducible hpodd hv
      hZinj hρ hirr hsurj b χsub χquo cc₀ htri₀ hdisj
  letI := hF
  letI := hFin
  letI := hAlg
  letI := hTop
  letI := hDisc
  letI := hTR
  -- E3: at `p ≥ 5` every such extension splits — contradiction
  exact (hnonsplit
    (eisenstein_trivial_sub_extension_splits_of_five_le hpodd hp5 hrankE
      hρE χ cc htri)).elim

/-! ### The founder cut behind the conductor leaf (2026-07-24)

The conductor leaf `exists_eigenform_level_dvd_two_of_trace_eq` below
was a single sorry carrying the whole of steps 1–4 of its classical
route (newform descent, Eichler–Shimura attachment, trace rigidity,
Carayol's conductor theorem). The pin has NONE of that vocabulary
(audited in the leaf's docstring), so this section founds it, and the
leaf is now a PROVEN assembly over:

* `IsWeightTwoNewform` +
  `exists_weightTwoNewform_of_weightTwoEigenform` — the newform
  carrier (minimal-level coefficient characterization) and the PROVEN
  descent: behind every normalized eigenform of level `N` lies a
  minimal-level eigenform of some level `M ∣ N` with the same
  eigensystem away from `N` (Diamond–Shurman Prop. 5.8.4; the
  classical content — that the inhabitants are exactly the newforms —
  is the carrier's soundness audit, not a Lean obligation).
* `exists_ringHom_heckeField_of_qCoeff_eq` — PROVEN glue: the given
  `p`-adic embedding of the old form's Hecke field transports to an
  embedding of the newform's Hecke field agreeing on the shared good
  coefficients (extension of embeddings into the algebraically closed
  `ℚ̄_p` along an algebraic extension).
* `exists_galoisRep_charFrob_of_weightTwoNewform` — the
  Eichler–Shimura attachment at general level, the REAL geometric
  leaf (unlike the level-`∣ 2` attachment statements, which are
  discharged by the proven emptiness of their carriers). DECOMPOSED
  2026-07-24 into the Eichler–Shimura cut (see its own section
  docstring below) and now a PROVEN assembly over the single sorried
  inhabitation leaf `nonempty_eichlerShimuraPackage` — the
  modular-Jacobian interface carrier.
* `charFrob_baseChange` and
  `charFrob_map_coeff_zero_of_isHardlyRamified` and
  `eq_quadratic_of_monic_natDegree_two` — PROVEN bookkeeping that
  upgrades the trace matching `hmatch` to FULL characteristic
  polynomial matching: `charFrob` commutes with coefficient base
  change, is monic quadratic, and has constant Frobenius coefficient
  `q` by `det ρ = χ_cyc` (through the Frobenius value of the
  cyclotomic character, `Chebotarev.lean`'s
  `cyclotomicCharacter_globalFrob`).
* `exists_linearEquiv_of_charFrob_eq` — PROVEN (2026-07-24): trace
  rigidity, Chebotarev density + characteristic-zero Brauer–Nesbitt
  over `ℚ̄_p` (density half `trace_eq_of_charFrob_eq`, module-theoretic
  half `nonempty_linearEquiv_of_trace_eq` via mathlib's Jacobson
  density theorem).
* `weightTwoNewform_level_dvd_two_of_isHardlyRamified` — Carayol's
  conductor theorem evaluated on the hardly ramified class; as of
  2026-07-24 itself a PROVEN per-place assembly (see its docstring):
  the hardly-ramified side — transport of `ρ`'s unramifiedness,
  flatness and tame-at-2 structure through the rigidity equivalence
  `e` to `τ`, the fixed-line linear algebra, and the `M ∣ 2`
  arithmetic — is fully PROVEN here, and the literature content is
  isolated in three per-place conductor leaves
  (`weightTwoNewform_not_dvd_level_of_isUnramifiedAt`,
  `weightTwoNewform_not_dvd_level_p_of_isFlatAt`,
  `weightTwoNewform_not_four_dvd_level_of_inertia_two` — Carayol
  1986/Saito 1997 per place) plus the local-arithmetic leaf
  `cyclotomicCharacter_eq_one_of_inertia_two` (the `p`-adic
  cyclotomic character is unramified at `2`, generalizing the PROVEN
  mod-3 instance in `ModThree.lean`). -/

section ConductorCut

/-- **The newform carrier** (Diamond–Shurman §5.8, coefficient-level):
`g ∈ S₂(Γ₀(M))` is a normalized full-Hecke eigenform
(`IsWeightTwoEigenform`, Prop. 5.8.5) whose away-from-`M` prime
eigensystem does not arise from any normalized eigenform of a strictly
smaller level dividing `M` — the *minimal-level* characterization of
newform-ness, the only spelling available on a pin with no newform
theory, no Petersson product and no oldform degeneracy maps.

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

Consequently the two sorried leaves below that quantify over this
carrier (`exists_galoisRep_charFrob_of_weightTwoNewform` and
`weightTwoNewform_level_dvd_two_of_isHardlyRamified`) quantify exactly
over the forms for which the classical theory provides attached
representations and conductor control. -/
structure IsWeightTwoNewform (M : ℕ) (g : CuspForm (Gamma0GL M) 2) : Prop
    extends IsWeightTwoEigenform M g where
  /-- The away-from-`M` eigensystem of `g` occurs at no strictly
  smaller level dividing `M`. -/
  eigensystem_minimal : ∀ M' : ℕ, M' ∣ M → M' ≠ M →
    ∀ g' : CuspForm (Gamma0GL M') 2, IsWeightTwoEigenform M' g' →
      ¬ ∀ (q : ℕ), q.Prime → ¬ q ∣ M → qCoeff M' g' q = qCoeff M g q

/-- **Newform descent** (Diamond–Shurman Prop. 5.8.4 in the
minimal-level spelling; PROVEN): behind every normalized weight-2
eigenform of level `N ≥ 1` lies an inhabitant of the minimal-level
newform carrier `IsWeightTwoNewform`, of some level `M ∣ N`, with the
same eigensystem at every prime `q ∤ N`. With the carrier as defined
this is a strong induction on the level: either `f` is already
minimal, or some strictly smaller divisor level realizes its
away-from-`N` eigensystem and the induction hypothesis applies to
that realization; agreement sets compose because a prime not dividing
`N` divides no divisor of `N`. (The analytic content of 5.8.4 — that
the minimal realization is a genuine newform with multiplicity-one
rigidity — lives in the carrier's soundness audit, where it belongs:
no Lean consumer needs more than minimality plus the agreement.) -/
theorem exists_weightTwoNewform_of_weightTwoEigenform :
    ∀ {N : ℕ}, 0 < N → ∀ {f : CuspForm (Gamma0GL N) 2},
      IsWeightTwoEigenform N f →
      ∃ (M : ℕ) (_ : M ∣ N) (_ : 0 < M) (g : CuspForm (Gamma0GL M) 2)
        (_ : IsWeightTwoNewform M g),
        ∀ (q : ℕ), q.Prime → ¬ q ∣ N → qCoeff M g q = qCoeff N f q := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN f hf
    by_cases hmin : ∀ M' : ℕ, M' ∣ N → M' ≠ N →
        ∀ g' : CuspForm (Gamma0GL M') 2, IsWeightTwoEigenform M' g' →
          ¬ ∀ (q : ℕ), q.Prime → ¬ q ∣ N → qCoeff M' g' q = qCoeff N f q
    · exact ⟨N, dvd_rfl, hN, f, ⟨hf, hmin⟩, fun q _ _ => rfl⟩
    · push Not at hmin
      obtain ⟨M', hM'dvd, hM'ne, g', hg', hagree⟩ := hmin
      have hM'pos : 0 < M' := Nat.pos_of_dvd_of_pos hM'dvd hN
      have hM'lt : M' < N := lt_of_le_of_ne (Nat.le_of_dvd hN hM'dvd) hM'ne
      obtain ⟨M, hMdvd, hMpos, g, hgnew, hagree'⟩ := ih M' hM'lt hM'pos hg'
      refine ⟨M, hMdvd.trans hM'dvd, hMpos, g, hgnew, fun q hq hqN => ?_⟩
      exact (hagree' q hq fun h => hqN (h.trans hM'dvd)).trans (hagree q hq hqN)

/-- **Transport of the `p`-adic Hecke-field embedding to the newform**
(PROVEN; step 5 of the classical route in the conductor leaf's
docstring): if the eigenform `g` (level `M ≥ 1`) shares the
away-from-`N` prime coefficients of `f`, then any embedding
`ι : K_f → ℚ̄_p` yields an embedding `κ : K_g → ℚ̄_p` agreeing with
`ι` on the shared good coefficients. Pure field theory: the good
coefficients generate a common subfield `E₀` of `ℂ` contained in both
Hecke fields; `K_g` is a number field (`heckeField_finiteDimensional`),
hence algebraic over `E₀`, so the restriction of `ι` to `E₀` extends
to `K_g` because `ℚ̄_p` is algebraically closed (`IsAlgClosed.lift`). -/
theorem exists_ringHom_heckeField_of_qCoeff_eq {N M : ℕ} (hM : 0 < M)
    {f : CuspForm (Gamma0GL N) 2} {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoEigenform M g)
    (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
    (hagree : ∀ (q : ℕ), q.Prime → ¬ q ∣ N → qCoeff M g q = qCoeff N f q) :
    ∃ κ : heckeField M g →+* AlgebraicClosure ℚ_[p],
      ∀ (q : ℕ), q.Prime → ¬ q ∣ N →
        κ (heckeCoeff M g q) = ι (heckeCoeff N f q) := by
  classical
  have hE₀f : IntermediateField.adjoin ℚ
      {x : ℂ | ∃ q : ℕ, q.Prime ∧ ¬ q ∣ N ∧ x = qCoeff N f q} ≤
        heckeField N f := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨q, -, -, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩
  have hE₀g : IntermediateField.adjoin ℚ
      {x : ℂ | ∃ q : ℕ, q.Prime ∧ ¬ q ∣ N ∧ x = qCoeff N f q} ≤
        heckeField M g := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro x ⟨q, hq, hqN, rfl⟩
    rw [← hagree q hq hqN]
    exact IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩
  set E₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ
    {x : ℂ | ∃ q : ℕ, q.Prime ∧ ¬ q ∣ N ∧ x = qCoeff N f q} with hE₀
  letI : Algebra E₀ (heckeField M g) :=
    (IntermediateField.inclusion hE₀g).toRingHom.toAlgebra
  letI : Algebra E₀ (AlgebraicClosure ℚ_[p]) :=
    (ι.comp (IntermediateField.inclusion hE₀f).toRingHom).toAlgebra
  haveI : IsScalarTower ℚ E₀ (heckeField M g) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : FiniteDimensional ℚ (heckeField M g) :=
    heckeField_finiteDimensional hM hg
  haveI : Algebra.IsAlgebraic ℚ (heckeField M g) :=
    Algebra.IsAlgebraic.of_finite ℚ _
  haveI : Algebra.IsAlgebraic E₀ (heckeField M g) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) E₀
  let κa : heckeField M g →ₐ[E₀] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  refine ⟨κa.toRingHom, fun q hq hqN => ?_⟩
  have hmem : qCoeff N f q ∈ E₀ :=
    IntermediateField.subset_adjoin ℚ _ ⟨q, hq, hqN, rfl⟩
  have hval : heckeCoeff M g q =
      algebraMap E₀ (heckeField M g) ⟨qCoeff N f q, hmem⟩ := by
    apply Subtype.ext
    exact hagree q hq hqN
  rw [hval]
  have hcomm := κa.commutes ⟨qCoeff N f q, hmem⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hcomm]
  show ι ((IntermediateField.inclusion hE₀f) ⟨qCoeff N f q, hmem⟩) =
    ι (heckeCoeff N f q)
  congr 1

/-- Quadratic decomposition of a monic degree-2 polynomial (PROVEN
glue): `P = X² + P₁·X + P₀`. Applied to the mapped Frobenius
characteristic polynomials to turn the coefficientwise information of
the conductor leaf (`hmatch` and the determinant normalization below)
into the polynomial identities the rigidity leaf consumes. -/
theorem eq_quadratic_of_monic_natDegree_two {A : Type*} [CommRing A]
    {P : Polynomial A} (hm : P.Monic) (hd : P.natDegree = 2) :
    P = Polynomial.X ^ 2 + Polynomial.C (P.coeff 1) * Polynomial.X
      + Polynomial.C (P.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have h2 : P.coeff 2 = 1 := by
      have hlc := hm.coeff_natDegree
      rwa [hd] at hlc
    simp [h2, Polynomial.coeff_X_pow]
  · have hzero : P.coeff (n + 3) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hzero, Polynomial.coeff_X_pow]

/-! ##### The Eichler–Shimura cut behind the attachment leaf (2026-07-24)

`exists_galoisRep_charFrob_of_weightTwoNewform` — the attachment of a
2-dimensional `ℚ̄_p`-representation to a weight-2 newform — was a
single sorry carrying the whole of Diamond–Shurman ch. 8–9. The pin
has NO modular curves, NO Jacobian varieties, NO abelian varieties
(audited 2026-07-24: `Mathlib/AlgebraicGeometry/EllipticCurve/*` is
Weierstrass-equation material — its `Jacobian/` folder is Jacobian
*coordinates*, not Jacobian varieties — and the reference Lean FLT
project likewise consumes its abelian-variety input, Mazur, as a
stated assumption). So the modular Jacobian enters as an INTERFACE
STRUCTURE (`EichlerShimuraPackage`), in the style of
`HardlyRamifiedRealization` above: its fields are exactly the
classically-true cited facts about the `p`-adic Tate module of
`J₀(M)` that the classical proof of the attachment consumes, and
everything from those facts to the attachment statement is PROVEN:

* `heckeEigenspace`, `compressEnd` — PROVEN linear algebra: the joint
  eigenspace of a prime-indexed operator family, and the compression
  of the endomorphism algebra onto a framed invariant subspace
  through a chosen projection. The compression is a LINEAR map on the
  whole endomorphism algebra (multiplicative only on the stabilizer
  of the subspace, `compressEnd_mul`) — the continuity-compatible
  substitute for restriction, since the module topology sees linear
  maps (`IsModuleTopology.continuous_of_linearMap`) while a bare
  restriction to an abstract submodule has no continuity API.
* `EichlerShimuraPackage` — the modular-Jacobian carrier: the
  Tate-module Galois module `Vp` with its continuous action `τJ`, the
  Hecke operators commuting with the action (`ℚ`-rationality of the
  Hecke correspondences), the Eichler–Shimura congruence at good
  primes, 2-dimensionality of the `κ`-eigenspace (multiplicity one),
  and the Weil-pairing determinant on it.
* `nonempty_eichlerShimuraPackage` — SORRY: the residual geometric
  leaf, inhabitation of the carrier (see its docstring for the
  classical construction, field by field).
* `exists_galoisRep_charFrob_of_weightTwoNewform` — now a PROVEN
  assembly: compress `τJ` to the eigenspace, transport congruence and
  determinant through the compression, and pin the Frobenius
  characteristic polynomial `X² − κ(a_q)·X + q` by Cayley–Hamilton
  against the congruence: the compressed Frobenius is invertible and
  is annihilated by two monic quadratics with equal constant terms
  (`det = q`), which forces equal linear terms. -/

/-- The joint eigenspace of the prime-indexed operator family `t` for
the eigenvalue system `a`: the intersection over all primes `q` of
`ker (t q − a q)`. For the Eichler–Shimura package below this carves
the `κ`-eigencomponent of the newform `g` out of the Tate module of
the modular Jacobian. -/
def heckeEigenspace {A : Type*} [CommRing A] {V₀ : Type*}
    [AddCommGroup V₀] [Module A V₀] (t : ℕ → Module.End A V₀)
    (a : ℕ → A) : Submodule A V₀ :=
  ⨅ (q : ℕ) (_ : q.Prime),
    LinearMap.ker (t q - a q • (1 : Module.End A V₀))

/-- Membership in `heckeEigenspace`: a simultaneous eigenvector at
every prime index. -/
theorem mem_heckeEigenspace_iff {A : Type*} [CommRing A] {V₀ : Type*}
    [AddCommGroup V₀] [Module A V₀] {t : ℕ → Module.End A V₀}
    {a : ℕ → A} {x : V₀} :
    x ∈ heckeEigenspace t a ↔
      ∀ (q : ℕ), q.Prime → t q x = a q • x := by
  simp [heckeEigenspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero]

section CompressEnd

variable {A : Type*} [CommRing A] {V₀ : Type*} [AddCommGroup V₀]
    [Module A V₀] {n : ℕ} (W : Submodule A V₀) (πW : V₀ →ₗ[A] W)
    (e : W ≃ₗ[A] (Fin n → A))

/-- Compression of an endomorphism of `V₀` to the standard frame of a
distinguished subspace `W`, through a chosen projection `πW` and a
chosen frame `e`. As a map of endomorphism ALGEBRAS it is only
multiplicative on the stabilizer of `W` (`compressEnd_mul`), but as a
LINEAR map it is everywhere defined — which is what makes the
compressed Galois representation of the Eichler–Shimura assembly
continuous for the module topologies. -/
def compressEnd :
    Module.End A V₀ →ₗ[A] Module.End A (Fin n → A) where
  toFun φ :=
    e.toLinearMap ∘ₗ πW ∘ₗ φ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

/-- Evaluation of the compression. -/
theorem compressEnd_apply (φ : Module.End A V₀) (x : Fin n → A) :
    compressEnd W πW e φ x = e (πW (φ ↑(e.symm x))) := rfl

/-- The compression sends the identity to the identity, given that
`πW` retracts the inclusion of `W`. -/
theorem compressEnd_one (hπ : ∀ w : W, πW (w : V₀) = w) :
    compressEnd W πW e 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [compressEnd_apply, Module.End.one_apply, hπ (e.symm x),
    LinearEquiv.apply_symm_apply, Module.End.one_apply]

/-- The compression is multiplicative when the right factor
stabilizes `W`. -/
theorem compressEnd_mul (hπ : ∀ w : W, πW (w : V₀) = w)
    (φ ψ : Module.End A V₀) (hψ : ∀ x ∈ W, ψ x ∈ W) :
    compressEnd W πW e (φ * ψ) =
      compressEnd W πW e φ * compressEnd W πW e ψ := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, compressEnd_apply,
    LinearEquiv.symm_apply_apply]
  have hmem : ψ ↑(e.symm x) ∈ W := hψ _ (SetLike.coe_mem (e.symm x))
  have hproj : πW (ψ ↑(e.symm x)) = ⟨ψ ↑(e.symm x), hmem⟩ :=
    hπ ⟨_, hmem⟩
  rw [hproj]

/-- The compression of an operator acting on `W` as the scalar `c` is
the scalar `c`. -/
theorem compressEnd_eq_smul_one (hπ : ∀ w : W, πW (w : V₀) = w)
    {φ : Module.End A V₀} {c : A} (hφ : ∀ x ∈ W, φ x = c • x) :
    compressEnd W πW e φ = c • 1 := by
  refine LinearMap.ext fun x => ?_
  rw [compressEnd_apply, hφ _ (SetLike.coe_mem (e.symm x)), map_smul,
    hπ (e.symm x), map_smul, LinearEquiv.apply_symm_apply,
    LinearMap.smul_apply, Module.End.one_apply]

/-- On the stabilizer of `W` the compression is conjugation of the
restriction by the frame — the bridge to `LinearMap.det_conj` for the
determinant transport of the Eichler–Shimura assembly. -/
theorem compressEnd_eq_conj_restrict (hπ : ∀ w : W, πW (w : V₀) = w)
    {φ : Module.End A V₀} (hφ : ∀ x ∈ W, φ x ∈ W) :
    compressEnd W πW e φ =
      (e : W →ₗ[A] (Fin n → A)) ∘ₗ φ.restrict hφ ∘ₗ
        (e.symm : (Fin n → A) →ₗ[A] W) := by
  refine LinearMap.ext fun x => ?_
  simp only [compressEnd_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.restrict_apply]
  exact congrArg e
    (hπ ⟨φ ↑(e.symm x), hφ _ (SetLike.coe_mem (e.symm x))⟩)

end CompressEnd

/-- **The Eichler–Shimura package of a weight-2 newform** `g` at the
`p`-adic embedding `κ` — the modular-Jacobian carrier. The intended
inhabitant (Diamond–Shurman ch. 8–9) is the rational `p`-adic Tate
module `Vp = V_p(J₀(M)) ⊗ ℚ̄_p` of the modular Jacobian
`J₀(M) = Jac X₀(M)`, with its continuous Galois action `τJ`, its
Hecke operators `hecke` (the correspondences `T_m`, resp. `U_q` at
`q ∣ M`), and the exceptional set `S = {v : v ∣ Mp}`. Each field is a
classically-true cited assertion about this inhabitant — the precise
citations are in the docstring of the inhabitation leaf
`nonempty_eichlerShimuraPackage`, the only sorried node of the cut. -/
structure EichlerShimuraPackage (M : ℕ) (g : CuspForm (Gamma0GL M) 2)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p]) where
  /-- The Galois module: intended `V_p(J₀(M)) ⊗ ℚ̄_p`. -/
  Vp : Type
  [addCommGroup : AddCommGroup Vp]
  [module : Module (AlgebraicClosure ℚ_[p]) Vp]
  [moduleFinite : Module.Finite (AlgebraicClosure ℚ_[p]) Vp]
  /-- The continuous Galois action on the Tate module. -/
  τJ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) Vp
  /-- The Hecke operators, base-changed to `ℚ̄_p`. -/
  hecke : ℕ → Module.End (AlgebraicClosure ℚ_[p]) Vp
  /-- The exceptional set (intended: the places over `Mp`). -/
  S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  /-- Hecke correspondences are defined over `ℚ`, so they commute
  with the whole Galois action. -/
  hecke_comm : ∀ (m : ℕ) (γ : Field.absoluteGaloisGroup ℚ),
    hecke m * τJ γ = τJ γ * hecke m
  /-- The Eichler–Shimura congruence relation at good primes:
  `Frob_q² − T_q·Frob_q + q = 0` on the Tate module. -/
  congruence : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat) ^ 2
      - hecke q *
        τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
      + (q : AlgebraicClosure ℚ_[p]) • 1 = 0
  /-- Multiplicity one: the joint `κ(a(g))`-eigenspace of the Hecke
  operators is 2-dimensional. -/
  rank_eigenspace :
    Module.rank (AlgebraicClosure ℚ_[p])
      (heckeEigenspace hecke (fun m => κ (heckeCoeff M g m))) = 2
  /-- The Weil-pairing determinant: the Galois determinant on the
  eigenspace is cyclotomic, with value `q` at the `q`-Frobenius. -/
  det_frob : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    ∀ (hst : ∀ x ∈ heckeEigenspace hecke
        (fun m => κ (heckeCoeff M g m)),
      τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat) x ∈
        heckeEigenspace hecke (fun m => κ (heckeCoeff M g m))),
    LinearMap.det
        ((τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).restrict hst) =
      (q : AlgebraicClosure ℚ_[p])

attribute [instance] EichlerShimuraPackage.addCommGroup
  EichlerShimuraPackage.module EichlerShimuraPackage.moduleFinite

/-- **Inhabitation of the Eichler–Shimura package** (sorry node — THE
residual geometric leaf of the attachment cut, and the only place
where the modular Jacobian itself is consumed): every weight-2
newform `g` of level `M ≥ 1` with a `p`-adic Hecke-field embedding
`κ` admits an Eichler–Shimura package.

Classical construction (Diamond–Shurman ch. 8–9): take
`Vp := V_p(J₀(M)) ⊗_{ℚ_p} ℚ̄_p`, the rational `p`-adic Tate module of
the modular Jacobian (dimension `2·dim S₂(Γ₀(M))`; D–S §6.1 and
ch. 8), with

* `τJ` the Galois action on the Tate module — continuous because the
  action on each `pⁿ`-torsion level factors through a finite
  quotient;
* `hecke m` the Hecke correspondence `T_m` (`U_q` at `q ∣ M`) acting
  through `End(J₀(M)) ⊗ ℚ̄_p`; the modular curve, its Hecke
  correspondences and the Jacobian all have `ℚ`-models (D–S §7.9,
  §8.5), so the operators commute with the Galois action —
  `hecke_comm`;
* `S := {v : v ∣ Mp}`;
* `congruence` — the EICHLER–SHIMURA RELATION (D–S Theorem 8.7.2): at
  a prime `q ∤ Mp` the curve `X₀(M)` has good reduction (Igusa, D–S
  Theorem 8.6.1), reduction identifies the `p`-adic Tate module with
  that of the special fiber (`q ≠ p`), and on the reduced Jacobian
  `T_q = Frob_q + q·⟨q⟩·Frob_q⁻¹` with `⟨q⟩ = 1` on `Γ₀(M)`, i.e.
  `Frob_q² − T_q·Frob_q + q = 0`;
* `rank_eigenspace` — MULTIPLICITY ONE: the joint eigenspace of the
  Hecke operators with eigensystem `κ(a(g))` is
  `V_p(A_g) ⊗_{K_g ⊗ ℚ_p, κ} ℚ̄_p` for the modular abelian variety
  `A_g = J₀(M)/I_g J₀(M)`: `V_p(A_g)` is free of rank 2 over
  `K_g ⊗ ℚ_p` (D–S Lemma 9.5.3), so each `κ`-component is
  2-dimensional, and no other isogeny component of `J₀(M)` carries
  the full eigensystem of the NEWFORM `g` (strong multiplicity one,
  D–S Theorem 5.8.2 with §6.6 — this is where the
  `IsWeightTwoNewform` hypothesis is consumed);
* `det_frob` — the WEIL PAIRING: the Galois determinant on the
  2-dimensional eigencomponent is the `p`-adic cyclotomic character
  (the determinant clause of D–S Theorem 9.5.4, from the Weil pairing
  on `J₀(M)` and triviality of the nebentypus), whose value at the
  `q`-Frobenius is `q`.

SOUNDNESS (2026-07-24): the statement quantifies over inhabitants of
`IsWeightTwoNewform` — exactly the classical newforms (the carrier's
audit above) — and over genuine embeddings `κ` of the Hecke field, so
the classical construction witnesses every instance. The
`hst`-quantified spelling of `det_frob` asserts the determinant
against EVERY stability proof; `LinearMap.restrict` does not depend
on that proof, so this is one fact, not a family. -/
theorem nonempty_eichlerShimuraPackage {M : ℕ} (hM : 0 < M)
    {g : CuspForm (Gamma0GL M) 2} (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p]) :
    Nonempty (EichlerShimuraPackage M g κ) :=
  sorry

/-- **The Eichler–Shimura attachment at general level** (DECOMPOSED
2026-07-24 into the Eichler–Shimura cut above and now a PROVEN
assembly over the inhabitation leaf
`nonempty_eichlerShimuraPackage`): a weight-2 newform `g` of level
`M ≥ 1`, together with an embedding `κ` of its Hecke field into
`ℚ̄_p`, has an attached 2-dimensional continuous
`ℚ̄_p`-representation of `Γ ℚ` whose Frobenius characteristic
polynomials away from a finite set of places are the Hecke
polynomials `X² − κ(a_q(g))·X + q`.

Assembly: the `κ`-eigenspace `W` of the package's Hecke operators is
Galois-stable (`hecke_comm`) and 2-dimensional (`rank_eigenspace`);
compressing `τJ` through a projection onto `W` and a frame
`W ≃ ℚ̄_p²` (`compressEnd`, multiplicative on the stabilizer, linear
hence continuous for the module topologies) yields the continuous
representation `τ`. At a good prime the compressed Frobenius `F` is
invertible, satisfies the compressed congruence
`F² − κ(a_q)·F + q = 0`, and has `det F = q` (`det_frob` through
`LinearMap.det_conj`); Cayley–Hamilton makes the characteristic
polynomial a second monic quadratic annihilating `F` with the same
constant term `q`, and subtracting the two relations forces the
linear coefficient `−κ(a_q)` — i.e. `charFrob = X² − κ(a_q)·X + q`.
SOUNDNESS: unchanged from the previous audit — the statement asserts
nothing about `τ` beyond the charpoly matching, precisely the input
shape the rigidity and Carayol leaves consume. -/
theorem exists_galoisRep_charFrob_of_weightTwoNewform
    {M : ℕ} (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p]) :
    ∃ (τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p]))
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          Polynomial.X ^ 2
            - Polynomial.C (κ (heckeCoeff M g q)) * Polynomial.X
            + Polynomial.C ((q : AlgebraicClosure ℚ_[p])) := by
  classical
  obtain ⟨P⟩ := nonempty_eichlerShimuraPackage hM hg κ
  set W : Submodule (AlgebraicClosure ℚ_[p]) P.Vp :=
    heckeEigenspace P.hecke (fun m => κ (heckeCoeff M g m)) with hWdef
  -- Galois stability of the eigenspace (Hecke rationality)
  have hstab : ∀ γ : Field.absoluteGaloisGroup ℚ,
      ∀ x ∈ W, P.τJ γ x ∈ W := by
    intro γ x hx
    rw [hWdef, mem_heckeEigenspace_iff] at hx ⊢
    intro q hq
    have hcomm := LinearMap.congr_fun (P.hecke_comm q γ) x
    rw [Module.End.mul_apply, Module.End.mul_apply, hx q hq,
      map_smul] at hcomm
    exact hcomm
  -- the eigenspace is 2-dimensional; frame it
  have hfrW : Module.finrank (AlgebraicClosure ℚ_[p]) W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast P.rank_eigenspace)
  let e : W ≃ₗ[AlgebraicClosure ℚ_[p]]
      (Fin 2 → AlgebraicClosure ℚ_[p]) :=
    (Module.finBasisOfFinrankEq (AlgebraicClosure ℚ_[p]) W
      hfrW).equivFun
  -- a projection onto the eigenspace
  obtain ⟨W', hWc⟩ := Submodule.exists_isCompl W
  let πW : P.Vp →ₗ[AlgebraicClosure ℚ_[p]] W :=
    Submodule.projectionOnto W W' hWc
  have hπ : ∀ w : W, πW (w : P.Vp) = w := fun w =>
    Submodule.projectionOnto_apply_left hWc w
  -- module topologies on the two endomorphism algebras
  letI : TopologicalSpace (Module.End (AlgebraicClosure ℚ_[p]) P.Vp) :=
    moduleTopology (AlgebraicClosure ℚ_[p]) _
  haveI : IsModuleTopology (AlgebraicClosure ℚ_[p])
      (Module.End (AlgebraicClosure ℚ_[p]) P.Vp) := ⟨rfl⟩
  letI : TopologicalSpace (Module.End (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p])) :=
    moduleTopology (AlgebraicClosure ℚ_[p]) _
  haveI : IsModuleTopology (AlgebraicClosure ℚ_[p])
      (Module.End (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p])) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AlgebraicClosure ℚ_[p])
    (Module.End (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]))
  have hτc : Continuous fun γ : Field.absoluteGaloisGroup ℚ =>
      P.τJ γ := ContinuousMonoidHom.continuous_toFun P.τJ
  have hΛc : Continuous (compressEnd W πW e) :=
    IsModuleTopology.continuous_of_linearMap _
  have hcont : Continuous fun γ : Field.absoluteGaloisGroup ℚ =>
      compressEnd W πW e (P.τJ γ) := hΛc.comp hτc
  -- the compressed representation
  let τmh : Field.absoluteGaloisGroup ℚ →*
      Module.End (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p]) :=
    { toFun := fun γ => compressEnd W πW e (P.τJ γ)
      map_one' := by
        show compressEnd W πW e (P.τJ 1) = 1
        rw [map_one]
        exact compressEnd_one W πW e hπ
      map_mul' := fun γ δ => by
        show compressEnd W πW e (P.τJ (γ * δ)) =
          compressEnd W πW e (P.τJ γ) * compressEnd W πW e (P.τJ δ)
        rw [map_mul]
        exact compressEnd_mul W πW e hπ _ _ (hstab δ) }
  let τ' : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]) := ⟨τmh, hcont⟩
  refine ⟨τ', P.S, fun q hq hqS => ?_⟩
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
  have happ : τ' (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat) =
      compressEnd W πW e
        (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)) := rfl
  rw [happ]
  -- the compressed Frobenius is invertible …
  have hinv : compressEnd W πW e
        (P.τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) *
      compressEnd W πW e
        (P.τJ ((globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹)) = 1 := by
    rw [← compressEnd_mul W πW e hπ _ _ (hstab _), ← map_mul,
      mul_inv_cancel, map_one]
    exact compressEnd_one W πW e hπ
  -- … acts as the Hecke scalar through the congruence …
  have hΛt : compressEnd W πW e (P.hecke q) =
      κ (heckeCoeff M g q) • 1 :=
    compressEnd_eq_smul_one W πW e hπ fun x hx =>
      mem_heckeEigenspace_iff.mp hx q hq
  have hcong := P.congruence q hq hqS
  have hQ : compressEnd W πW e
        (P.τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) ^ 2
      - κ (heckeCoeff M g q) • compressEnd W πW e
        (P.τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))
      + (q : AlgebraicClosure ℚ_[p]) • 1 = 0 := by
    have h₀ : compressEnd W πW e
          (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat) ^ 2)
        - compressEnd W πW e (P.hecke q *
          P.τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))
        + (q : AlgebraicClosure ℚ_[p]) • compressEnd W πW e 1 = 0 := by
      rw [← map_smul, ← map_sub, ← map_add, hcong, map_zero]
    rw [pow_two, compressEnd_mul W πW e hπ _ _ (hstab _),
      compressEnd_mul W πW e hπ _ _ (hstab _), hΛt,
      compressEnd_one W πW e hπ, smul_mul_assoc, one_mul,
      ← pow_two] at h₀
    exact h₀
  -- … and has determinant `q` by the Weil pairing
  have hdet : LinearMap.det (compressEnd W πW e
      (P.τJ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))) =
      (q : AlgebraicClosure ℚ_[p]) := by
    rw [compressEnd_eq_conj_restrict W πW e hπ (hstab _),
      LinearMap.det_conj]
    exact P.det_frob q hq hqS (hstab _)
  -- Cayley–Hamilton against the congruence pins the charpoly
  have hfr2 : Module.finrank (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]) = 2 := by simp
  have hmon : (compressEnd W πW e (P.τJ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.Monic :=
    LinearMap.charpoly_monic _
  have hdeg : (compressEnd W πW e (P.τJ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.natDegree =
      2 := by
    rw [LinearMap.charpoly_natDegree]
    exact hfr2
  have hP2 := eq_quadratic_of_monic_natDegree_two hmon hdeg
  have hc0 : (compressEnd W πW e (P.τJ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 0 =
      (q : AlgebraicClosure ℚ_[p]) := by
    have hsign := LinearMap.det_eq_sign_charpoly_coeff
      (compressEnd W πW e (P.τJ (globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)))
    rw [hfr2, hdet] at hsign
    have hpow : ((-1 : AlgebraicClosure ℚ_[p])) ^ 2 *
        (compressEnd W πW e (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 0 =
        (compressEnd W πW e (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 0
      := by ring
    rw [hpow] at hsign
    exact hsign.symm
  have hCH := LinearMap.aeval_self_charpoly
    (compressEnd W πW e (P.τJ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)))
  rw [hP2] at hCH
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] at hCH
  rw [hc0] at hCH
  have hsub : ((compressEnd W πW e (P.τJ (globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
      + κ (heckeCoeff M g q)) • compressEnd W πW e
        (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)) = 0 := by
    have hmod : ((compressEnd W πW e (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
        + κ (heckeCoeff M g q)) • compressEnd W πW e
          (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) =
        (compressEnd W πW e (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) ^ 2
          + (compressEnd W πW e (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
            • compressEnd W πW e (P.τJ (globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat))
          + (q : AlgebraicClosure ℚ_[p]) • 1)
        - (compressEnd W πW e (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) ^ 2
          - κ (heckeCoeff M g q) • compressEnd W πW e
            (P.τJ (globalFrob
              hq.toHeightOneSpectrumRingOfIntegersRat))
          + (q : AlgebraicClosure ℚ_[p]) • 1) := by
      rw [add_smul]
      abel
    rw [hmod, hCH, hQ, sub_zero]
  have hone : ((compressEnd W πW e (P.τJ (globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
      + κ (heckeCoeff M g q)) •
      (1 : Module.End (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p])) = 0 := by
    have h2 : ((compressEnd W πW e (P.τJ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
        + κ (heckeCoeff M g q)) •
        (compressEnd W πW e (P.τJ (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)) *
          compressEnd W πW e (P.τJ ((globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat)⁻¹))) = 0 := by
      rw [← smul_mul_assoc, hsub, zero_mul]
    rwa [hinv] at h2
  have hker : ((compressEnd W πW e (P.τJ (globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1
      + κ (heckeCoeff M g q)) •
      (Pi.single (0 : Fin 2) (1 : AlgebraicClosure ℚ_[p]) :
        Fin 2 → AlgebraicClosure ℚ_[p]) = 0 := by
    have h3 := congrArg (fun ψ : Module.End (AlgebraicClosure ℚ_[p])
        (Fin 2 → AlgebraicClosure ℚ_[p]) =>
      ψ (Pi.single (0 : Fin 2) (1 : AlgebraicClosure ℚ_[p]))) hone
    simpa using h3
  have hc1 : (compressEnd W πW e (P.τJ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly.coeff 1 =
      - κ (heckeCoeff M g q) := by
    rcases smul_eq_zero.mp hker with h | h
    · exact add_eq_zero_iff_eq_neg.mp h
    · have h4 : (1 : AlgebraicClosure ℚ_[p]) = 0 := by
        simpa using congrFun h 0
      exact absurd h4 one_ne_zero
  rw [hP2, hc1, hc0, map_neg]
  ring

omit [IsDomain R] [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] in
/-- **Determinant normalization of the Frobenius characteristic
polynomial** (PROVEN — the `det = χ_cyc` bookkeeping): for a hardly
ramified `ρ` and a prime `q ≠ p`, the constant coefficient of the
mapped Frobenius characteristic polynomial at `q` is `q`. Since that
polynomial is monic quadratic (`LinearMap.charpoly`), this upgrades
the trace matching hypothesis of the conductor leaf to FULL
characteristic polynomial matching — the honest input of
Brauer–Nesbitt. Proof: the constant coefficient of a rank-2
characteristic polynomial is the determinant
(`LinearMap.det_eq_sign_charpoly_coeff`), the determinant of `ρ` is
the cyclotomic character (the `det` field of `IsHardlyRamified`), and
the cyclotomic character evaluates to `q` at the global Frobenius of
`q ≠ p` (`cyclotomicCharacter_globalFrob`, `Chebotarev.lean`). -/
theorem charFrob_map_coeff_zero_of_isHardlyRamified
    [Algebra R (AlgebraicClosure ℚ_[p])]
    (hρ : IsHardlyRamified hpodd hv ρ) {q : ℕ} (hq : q.Prime)
    (hqp : q ≠ p) :
    ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
        (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 0 =
      (q : AlgebraicClosure ℚ_[p]) := by
  have hfr : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hv)
  rw [Polynomial.coeff_map, GaloisRep.charFrob_eq_charpoly_globalFrob]
  have hdet := LinearMap.det_eq_sign_charpoly_coeff
    (ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))
  rw [hfr] at hdet
  have hc0 : (ρ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly.coeff 0 =
      LinearMap.det (ρ (globalFrob
        hq.toHeightOneSpectrumRingOfIntegersRat)) := by
    rw [hdet]; ring
  rw [hc0]
  have hdet2 : LinearMap.det (ρ (globalFrob
      hq.toHeightOneSpectrumRingOfIntegersRat)) =
      algebraMap ℤ_[p] R
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          (globalFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).toRingEquiv : ℤ_[p]ˣ) :
          ℤ_[p]) :=
    hρ.det _
  rw [hdet2, cyclotomicCharacter_globalFrob hq hqp]
  simp [map_natCast]

/-!
#### Trace rigidity over `ℚ̄_p`: Chebotarev + characteristic-zero
Brauer–Nesbitt (PROVEN, 2026-07-24)

The rigidity leaf `exists_linearEquiv_of_charFrob_eq` is DERIVED here
from two proven halves:

* **Density half** (`trace_eq_of_charFrob_eq`): charpoly agreement at
  the Frobenius elements off a finite set upgrades to TRACE agreement
  at every group element — the agreement locus is closed (traces are
  continuous on the module-topology endomorphism space, `ℚ̄_p` is
  Hausdorff as a normed field) and contains the conjugates of the
  global Frobenius elements, dense by `dense_conjClasses_globalFrob`.
  Only the trace (linear coefficient) of the charpoly is consumed —
  the determinant is not needed anywhere in the argument.

* **Brauer–Nesbitt half** (`nonempty_linearEquiv_of_trace_eq` and its
  Galois-level wrapper `exists_linearEquiv_of_trace_eq`): the abstract
  characteristic-zero statement in dimension 2 — two 2-dimensional
  modules over a `k`-algebra with equal trace functions, the second
  simple, are isomorphic (Curtis–Reiner §30.16, hand-rolled at
  dimension 2). The proof avoids semisimplification bookkeeping: a
  nonzero `A`-hom `M₁ → M₂` is automatically bijective (simplicity of
  `M₂` gives surjectivity, rank–nullity over `k` gives injectivity);
  if no nonzero hom exists, mathlib's Jacobson density theorem
  (`jacobson_density`) applied to the semisimple companion
  (`M₁ × M₂` when `M₁` is simple, `(W × M₁/W) × M₂` for a stable
  line `W` otherwise) produces a ring element acting as the identity
  on `M₂` and as zero on the companion — its two traces are `2` and
  `0` (square-zero endomorphisms are traceless), contradicting
  `char k = 0`. Group-algebra bookkeeping (`MonoidAlgebra ℚ̄_p (Γ ℚ)`
  acting through `Representation.asAlgebraHom`) turns the equivariance
  statement into module language and back.
-/

/-- **Hom vanishing between simple modules of different dimensions**
(PROVEN glue for the Brauer–Nesbitt half): an `A`-linear map between
simple `A`-modules whose `k`-dimensions differ (`k` acting through
central scalars of `A`) is zero — a nonzero one would be bijective by
Schur (`LinearMap.bijective_or_eq_zero`), hence a `k`-linear dimension
isomorphism. -/
lemma linearMap_eq_zero_of_finrank_ne
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [IsSimpleModule A M] [IsSimpleModule A N]
    (h : Module.finrank k M ≠ Module.finrank k N)
    (f : M →ₗ[A] N) : f = 0 := by
  rcases LinearMap.bijective_or_eq_zero f with hbij | h0
  · exact absurd
      (LinearEquiv.finrank_eq
        ((LinearEquiv.ofBijective f hbij).restrictScalars k)) h
  · exact h0

/-- **Dimension-one modules are simple** (PROVEN glue): an `A`-module of
`k`-dimension one (with the `k`-action factoring through `A`) is a
simple `A`-module — every nonzero `A`-submodule contains a nonzero
vector, whose `k`-span is already everything. -/
lemma isSimpleModule_of_finrank_eq_one
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M]
    (h : Module.finrank k M = 1) : IsSimpleModule A M := by
  haveI : Nontrivial M := by
    rw [← Module.finrank_pos_iff (R := k)]
    omega
  haveI : Nontrivial (Submodule A M) := ⟨⊥, ⊤, fun hbt => by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have hxbot : x ∈ (⊥ : Submodule A M) := by rw [hbt]; trivial
    exact hx (by simpa using hxbot)⟩
  refine IsSimpleModule.mk (toIsSimpleOrder := ⟨fun P => ?_⟩)
  by_cases hP : P = ⊥
  · exact Or.inl hP
  refine Or.inr ?_
  obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hP
  have hspan : Submodule.span k {x} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hx0, h]
  rw [Submodule.eq_top_iff']
  intro y
  have hy : y ∈ Submodule.span k {x} := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  exact P.smul_of_tower_mem c hxP

/-- **Binary products of semisimple modules are semisimple** (PROVEN
glue; mathlib's finite-product instance is stated for `Π`-types only):
`P × Q` is the sup of the ranges of `inl` and `inr`, each isomorphic to
a semisimple factor. -/
lemma isSemisimpleModule_prod'
    {A : Type*} [Ring A]
    {P Q : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [IsSemisimpleModule A P] [IsSemisimpleModule A Q] :
    IsSemisimpleModule A (P × Q) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (ι := Bool)
    (p := fun b => bif b then LinearMap.range (LinearMap.inl A P Q)
      else LinearMap.range (LinearMap.inr A P Q)) ?_ ?_
  · rintro (_ | _)
    · exact .congr (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm
    · exact .congr (LinearEquiv.ofInjective _ LinearMap.inl_injective).symm
  · rw [iSup_bool_eq]
    exact LinearMap.sup_range_inl_inr

/-- **Jacobson-density projection extraction** (PROVEN — the density
core of the characteristic-zero Brauer–Nesbitt argument): given a
semisimple `A`-module `P` and a simple `A`-module `M`, both
finite-dimensional over central scalars `k`, with no nonzero `A`-homs
between `P` and `M` in either direction, some ring element acts as the
identity on `M` and as zero on `P`. The projection of `P × M` onto `M`
commutes with every `A`-endomorphism (hom vanishing kills the
off-diagonal blocks), so mathlib's Jacobson density theorem
(`jacobson_density`, `P × M` is semisimple) realizes it by a ring
element on a finite `k`-spanning set, hence — both sides being
`k`-linear — everywhere. -/
lemma exists_smul_id_and_smul_zero
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {P M : Type*}
    [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [Module.Finite k P]
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M]
    [IsSemisimpleModule A P] [IsSimpleModule A M]
    (hPM : ∀ f : P →ₗ[A] M, f = 0) (hMP : ∀ f : M →ₗ[A] P, f = 0) :
    ∃ r : A, (∀ m : M, r • m = m) ∧ (∀ x : P, r • x = 0) := by
  classical
  haveI hNss : IsSemisimpleModule A (P × M) := isSemisimpleModule_prod' (A := A)
  set π : (P × M) →ₗ[A] (P × M) :=
    (LinearMap.inr A P M).comp (LinearMap.snd A P M) with hπ
  have hcomm : ∀ φ : Module.End A (P × M), π ∘ₗ φ = φ ∘ₗ π := by
    intro φ
    have hb : (LinearMap.fst A P M) ∘ₗ φ ∘ₗ (LinearMap.inr A P M) = 0 :=
      hMP _
    have hc : (LinearMap.snd A P M) ∘ₗ φ ∘ₗ (LinearMap.inl A P M) = 0 :=
      hPM _
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply]
    have hxsplit : x = (x.1, (0 : M)) + ((0 : P), x.2) := by
      simp
    have hb' : (φ ((0 : P), x.2)).1 = 0 := by
      simpa using LinearMap.ext_iff.mp hb x.2
    have hc' : (φ (x.1, (0 : M))).2 = 0 := by
      simpa using LinearMap.ext_iff.mp hc x.1
    have hL : π (φ x) = ((0 : P), (φ x).2) := by simp [hπ]
    have hsnd : (φ x).2 = (φ ((0 : P), x.2)).2 := by
      conv_lhs => rw [hxsplit]
      rw [map_add]
      simp [hc']
    rw [hL, hsnd]
    have hR : φ (π x) = φ ((0 : P), x.2) := by simp [hπ]
    rw [hR]
    exact Prod.ext (by rw [hb']) rfl
  let f : Module.End (Module.End A (P × M)) (P × M) :=
    { toFun := π
      map_add' := map_add π
      map_smul' := fun φ x => by
        simpa [Module.End.smul_def] using LinearMap.ext_iff.mp (hcomm φ) x }
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := P × M)
  obtain ⟨r, hr⟩ := jacobson_density (R := A) (M := P × M) f s
  have hall : ∀ n : P × M, π n = r • n := by
    intro n
    have hn : n ∈ Submodule.span k (s : Set (P × M)) := by
      rw [hs]; trivial
    induction hn using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, smul_add]
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, hu, smul_comm]
  refine ⟨r, fun m => ?_, fun x => ?_⟩
  · have h0 := hall ((0 : P), m)
    have : ((0 : P), m) = (r • (0 : P), r • m) := by
      simpa [hπ] using h0
    simpa using (Prod.ext_iff.mp this).2.symm
  · have h0 := hall (x, (0 : M))
    have : ((0 : P), (0 : M)) = (r • x, r • (0 : M)) := by
      simpa [hπ] using h0
    simpa using (Prod.ext_iff.mp this).1.symm

/-- **Characteristic-zero Brauer–Nesbitt, dimension 2** (PROVEN — the
abstract module-theoretic core of the rigidity leaf; Curtis–Reiner
§30.16 hand-rolled at dimension 2): two 2-dimensional modules over a
`k`-algebra `A` (`k` a field of characteristic zero acting through
central scalars) with equal trace functions, the second simple, are
isomorphic as `A`-modules. Any nonzero `A`-hom `M → N` is bijective
(simplicity of `N` + rank–nullity over `k`); if none exists, the
Jacobson-density projector element has trace `2` on `N` and trace `0`
on `M` — zero either because it annihilates the simple `M`, or because
a stable line `W ≤ M` makes its action square-zero — contradicting the
trace equality in characteristic zero. -/
theorem nonempty_linearEquiv_of_trace_eq
    {k : Type*} [Field k] [CharZero k]
    {A : Type*} [Ring A] [Algebra k A]
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [Module.Finite k M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [Module.Finite k N]
    [IsSimpleModule A N]
    (hM : Module.finrank k M = 2) (hN : Module.finrank k N = 2)
    (htr : ∀ a : A,
      LinearMap.trace k M (Module.toModuleEnd k (S := A) M a) =
      LinearMap.trace k N (Module.toModuleEnd k (S := A) N a)) :
    Nonempty (M ≃ₗ[A] N) := by
  classical
  haveI : Nontrivial M := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  haveI : Nontrivial N := by
    rw [← Module.finrank_pos_iff (R := k)]; omega
  -- Any nonzero `A`-linear map `M →ₗ[A] N` is bijective.
  have key : ∀ f : M →ₗ[A] N, f ≠ 0 → Function.Bijective f := by
    intro f hf
    have hsurj : Function.Surjective f := by
      have hrange : LinearMap.range f = ⊤ := by
        rcases eq_bot_or_eq_top (LinearMap.range f) with h | h
        · exact absurd (LinearMap.range_eq_bot.mp h) hf
        · exact h
      exact LinearMap.range_eq_top.mp hrange
    have hinj : Function.Injective f := by
      have hres : Function.Surjective (f.restrictScalars k) := hsurj
      have h1 : Module.finrank k (LinearMap.range (f.restrictScalars k)) = 2 := by
        rw [LinearMap.range_eq_top.mpr hres, finrank_top, hN]
      have h2 := LinearMap.finrank_range_add_finrank_ker (f.restrictScalars k)
      rw [hM, h1] at h2
      have hker : LinearMap.ker (f.restrictScalars k) = ⊥ := by
        rw [← Submodule.finrank_eq_zero (R := k)]
        omega
      have hinj' : Function.Injective (f.restrictScalars k) :=
        LinearMap.ker_eq_bot.mp hker
      exact hinj'
    exact ⟨hinj, hsurj⟩
  by_cases hex : ∃ f : M →ₗ[A] N, f ≠ 0
  · obtain ⟨f, hf⟩ := hex
    exact ⟨LinearEquiv.ofBijective f (key f hf)⟩
  push Not at hex
  exfalso
  by_cases hsimp : IsSimpleModule A M
  · -- both simple, no homs in either direction: density + trace clash
    haveI := hsimp
    have hMP : ∀ g : N →ₗ[A] M, g = 0 := by
      intro g
      rcases LinearMap.bijective_or_eq_zero g with hbij | h0
      · exfalso
        set e := LinearEquiv.ofBijective g hbij
        have hzero := hex (e.symm : M ≃ₗ[A] N).toLinearMap
        obtain ⟨x, hx⟩ := exists_ne (0 : M)
        apply hx
        calc x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e 0 := by rw [show e.symm x = 0 from LinearMap.ext_iff.mp hzero x]
        _ = 0 := map_zero _
      · exact h0
    obtain ⟨r, hrN, hrM⟩ :=
      exists_smul_id_and_smul_zero (k := k) (P := M) (M := N) hex hMP
    have h0 : Module.toModuleEnd k (S := A) M r = 0 :=
      LinearMap.ext fun x => hrM x
    have h1 : Module.toModuleEnd k (S := A) N r = LinearMap.id :=
      LinearMap.ext fun x => hrN x
    have htr' := htr r
    rw [h0, h1, map_zero, LinearMap.trace_id, hN] at htr'
    exact two_ne_zero htr'.symm
  · -- `M` non-simple: a stable line makes the action of the projector
    -- element square-zero on `M`, clashing with trace `2` on `N`.
    haveI : Nontrivial (Submodule A M) := ⟨⊥, ⊤, fun hbt => by
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      have hxbot : x ∈ (⊥ : Submodule A M) := by rw [hbt]; trivial
      exact hx (by simpa using hxbot)⟩
    obtain ⟨W, hWbot, hWtop⟩ : ∃ W : Submodule A M, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hall
      push Not at hall
      exact hsimp
        (IsSimpleModule.mk
          (toIsSimpleOrder := ⟨fun P => or_iff_not_imp_left.mpr (hall P)⟩))
    -- the `A`-submodule `W` and its `k`-scalar restriction have the same
    -- carrier: the identity is a `k`-linear equivalence between them
    have eW : (W.restrictScalars k) ≃ₗ[k] W :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    -- dimensions of the line and the quotient line
    have hWr : Module.finrank k (W.restrictScalars k) = 1 := by
      have hne_top : W.restrictScalars k ≠ ⊤ := fun h => hWtop (by
        rw [Submodule.eq_top_iff']
        intro x
        have hx : x ∈ W.restrictScalars k := by rw [h]; trivial
        exact hx)
      have hlt : Module.finrank k (W.restrictScalars k) < 2 :=
        hM ▸ Submodule.finrank_lt hne_top
      have hne_bot : W.restrictScalars k ≠ ⊥ := fun h => hWbot (by
        rw [Submodule.eq_bot_iff]
        intro x hx
        have hx' : x ∈ W.restrictScalars k := hx
        rw [h] at hx'
        simpa using hx')
      have hpos : 0 < Module.finrank k (W.restrictScalars k) := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hne_bot
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) hpos
    have hWfin : Module.finrank k W = 1 := by
      rw [← hWr]
      exact (LinearEquiv.finrank_eq eW).symm
    have hQfin : Module.finrank k (M ⧸ W) = 1 := by
      have hq := (LinearEquiv.finrank_eq
        ((Submodule.Quotient.restrictScalarsEquiv k W))).symm
      have hadd := Submodule.finrank_quotient_add_finrank
        (W.restrictScalars k)
      rw [hM, hWr] at hadd
      rw [hq]
      omega
    haveI : Module.Finite k W := Module.Finite.equiv eW
    haveI : Module.Finite k (M ⧸ W) :=
      Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k W)
    haveI : IsSimpleModule A W :=
      isSimpleModule_of_finrank_eq_one (A := A) hWfin
    haveI : IsSimpleModule A (M ⧸ W) :=
      isSimpleModule_of_finrank_eq_one (A := A) hQfin
    -- no homs between `W × (M ⧸ W)` and `N` in either direction
    have hPM : ∀ f : (W × (M ⧸ W)) →ₗ[A] N, f = 0 := by
      intro f
      have h1 : f ∘ₗ (LinearMap.inl A W (M ⧸ W)) = 0 :=
        linearMap_eq_zero_of_finrank_ne (by rw [hWfin, hN]; omega) _
      have h2 : f ∘ₗ (LinearMap.inr A W (M ⧸ W)) = 0 :=
        linearMap_eq_zero_of_finrank_ne (by rw [hQfin, hN]; omega) _
      rw [← LinearMap.coprod_comp_inl_inr f, h1, h2]
      refine LinearMap.ext fun x => ?_
      simp
    have hMP : ∀ f : N →ₗ[A] (W × (M ⧸ W)), f = 0 := by
      intro f
      have h1 : (LinearMap.fst A W (M ⧸ W)) ∘ₗ f = 0 :=
        linearMap_eq_zero_of_finrank_ne (by rw [hWfin, hN]; omega) _
      have h2 : (LinearMap.snd A W (M ⧸ W)) ∘ₗ f = 0 :=
        linearMap_eq_zero_of_finrank_ne (by rw [hQfin, hN]; omega) _
      refine LinearMap.ext fun x => ?_
      refine Prod.ext ?_ ?_
      · simpa using LinearMap.ext_iff.mp h1 x
      · simpa using LinearMap.ext_iff.mp h2 x
    haveI : IsSemisimpleModule A (W × (M ⧸ W)) :=
      isSemisimpleModule_prod' (A := A)
    obtain ⟨r, hrN, hrP⟩ :=
      exists_smul_id_and_smul_zero (k := k) (P := W × (M ⧸ W)) (M := N)
        hPM hMP
    -- the action of `r` on `M` is square-zero …
    have hrW : ∀ w : M, w ∈ W → r • w = 0 := by
      intro w hw
      have h0 := hrP (⟨w, hw⟩, (0 : M ⧸ W))
      have h1 : r • (⟨w, hw⟩ : W) = 0 := (Prod.ext_iff.mp h0).1
      simpa using congrArg (Subtype.val) h1
    have hrQ : ∀ x : M, r • x ∈ W := by
      intro x
      have h0 := hrP ((0 : W), Submodule.Quotient.mk x)
      have h1 : r • (Submodule.Quotient.mk x : M ⧸ W) = 0 :=
        (Prod.ext_iff.mp h0).2
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    have hnil : IsNilpotent (Module.toModuleEnd k (S := A) M r) := by
      refine ⟨2, ?_⟩
      rw [pow_two]
      refine LinearMap.ext fun x => ?_
      exact hrW _ (hrQ x)
    -- … so its trace is zero, while the trace on `N` is `2 ≠ 0`.
    have hzero : LinearMap.trace k M (Module.toModuleEnd k (S := A) M r) = 0 :=
      (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have h1 : Module.toModuleEnd k (S := A) N r = LinearMap.id :=
      LinearMap.ext fun x => hrN x
    have htr' := htr r
    rw [hzero, h1, LinearMap.trace_id, hN] at htr'
    exact two_ne_zero htr'.symm

/-- **Conjugation invariance of the trace of a Galois representation**
(PROVEN glue): `tr τ(g·x·g⁻¹) = tr τ(x)`, by multiplicativity of `τ`
and `tr(ab) = tr(ba)`. -/
lemma trace_conj_eq {A : Type*} [CommRing A] [TopologicalSpace A]
    {V : Type*} [AddCommGroup V] [Module A V]
    (τ : GaloisRep ℚ A V) (g x : Field.absoluteGaloisGroup ℚ) :
    LinearMap.trace A V (τ (g * x * g⁻¹)) = LinearMap.trace A V (τ x) := by
  have e1 : τ (g * x * g⁻¹) = τ g * τ x * τ g⁻¹ := by
    rw [map_mul, map_mul]
  have hca : τ g⁻¹ * τ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [e1, LinearMap.trace_mul_comm, ← mul_assoc, hca, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **Trace agreement everywhere from Frobenius charpoly agreement off
a finite set** (PROVEN — the Chebotarev-density half of the rigidity
leaf): if two continuous 2-dimensional `ℚ̄_p`-representations of `Γ ℚ`
have equal Frobenius characteristic polynomials away from a finite set
of places, their traces agree at EVERY group element. The agreement
locus is closed — the trace is a continuous function on the
module-topology endomorphism space (`IsModuleTopology
.continuous_of_linearMap`) and `ℚ̄_p` is Hausdorff as a normed field —
conjugation-invariant (`trace_conj_eq`), and contains the global
Frobenius classes off the finite set, dense by the Chebotarev density
node `dense_conjClasses_globalFrob`. -/
theorem trace_eq_of_charFrob_eq
    {V₁ : Type*} [AddCommGroup V₁] [Module (AlgebraicClosure ℚ_[p]) V₁]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₁]
    [Module.Free (AlgebraicClosure ℚ_[p]) V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module (AlgebraicClosure ℚ_[p]) V₂]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₂]
    [Module.Free (AlgebraicClosure ℚ_[p]) V₂]
    (hfr₁ : Module.finrank (AlgebraicClosure ℚ_[p]) V₁ = 2)
    (hfr₂ : Module.finrank (AlgebraicClosure ℚ_[p]) V₂ = 2)
    {τ₁ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₁}
    {τ₂ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₂}
    {S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (h : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      τ₁.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        τ₂.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∀ γ : Field.absoluteGaloisGroup ℚ,
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ γ) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ γ) := by
  classical
  -- trace agreement at the global Frobenius elements off `S`
  have hFrob : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      v ∉ S →
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ (globalFrob v)) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ (globalFrob v)) := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hpoly := h q hq hv
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
      GaloisRep.charFrob_eq_charpoly_globalFrob,
      charpoly_eq_quadratic_of_finrank_two hfr₁,
      charpoly_eq_quadratic_of_finrank_two hfr₂] at hpoly
    have hc := congrArg (fun P => Polynomial.coeff P 1) hpoly
    simp only [coeff_one_quadratic] at hc
    exact neg_inj.mp hc
  -- the agreement locus is closed …
  letI : TopologicalSpace (Module.End (AlgebraicClosure ℚ_[p]) V₁) :=
    moduleTopology (AlgebraicClosure ℚ_[p]) _
  letI : TopologicalSpace (Module.End (AlgebraicClosure ℚ_[p]) V₂) :=
    moduleTopology (AlgebraicClosure ℚ_[p]) _
  haveI : IsModuleTopology (AlgebraicClosure ℚ_[p])
    (Module.End (AlgebraicClosure ℚ_[p]) V₁) := ⟨rfl⟩
  haveI : IsModuleTopology (AlgebraicClosure ℚ_[p])
    (Module.End (AlgebraicClosure ℚ_[p]) V₂) := ⟨rfl⟩
  have hc₁ : Continuous fun γ : Field.absoluteGaloisGroup ℚ =>
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ γ) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁)).comp
      (ContinuousMonoidHom.continuous_toFun τ₁)
  have hc₂ : Continuous fun γ : Field.absoluteGaloisGroup ℚ =>
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ γ) :=
    (IsModuleTopology.continuous_of_linearMap
      (LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂)).comp
      (ContinuousMonoidHom.continuous_toFun τ₂)
  have hclosed : IsClosed {γ : Field.absoluteGaloisGroup ℚ |
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ γ) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ γ)} :=
    isClosed_eq hc₁ hc₂
  -- … and contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {γ : Field.absoluteGaloisGroup ℚ |
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ γ) =
          LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ γ)} := by
    rintro x ⟨v, hv, g, rfl⟩
    simp only [Set.mem_setOf_eq]
    exact (trace_conj_eq τ₁ g (globalFrob v)).trans
      ((hFrob v hv).trans (trace_conj_eq τ₂ g (globalFrob v)).symm)
  intro γ
  have hγ : γ ∈ closure {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} := by
    rw [(dense_conjClasses_globalFrob (K := ℚ) S).closure_eq]
    trivial
  exact closure_minimal hsub hclosed hγ

set_option backward.isDefEq.respectTransparency false in
/-- **Char-0 Brauer–Nesbitt at the Galois level** (PROVEN): two
2-dimensional `ℚ̄_p`-representations of `Γ ℚ` with equal traces
everywhere, the second irreducible, are equivariantly linearly
equivalent. Derived from the abstract module-theoretic core
`nonempty_linearEquiv_of_trace_eq` by viewing both spaces as modules
over the group algebra `(ℚ̄_p)[Γ ℚ]` through
`Representation.asAlgebraHom`; irreducibility transfers to simplicity
via `Representation.irreducible_iff_isSimpleModule_asModule`, and the
trace hypothesis extends `ℚ̄_p`-linearly from group elements to the
whole group algebra. -/
theorem exists_linearEquiv_of_trace_eq
    {V₁ : Type*} [AddCommGroup V₁] [Module (AlgebraicClosure ℚ_[p]) V₁]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module (AlgebraicClosure ℚ_[p]) V₂]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₂]
    (hfr₁ : Module.finrank (AlgebraicClosure ℚ_[p]) V₁ = 2)
    (hfr₂ : Module.finrank (AlgebraicClosure ℚ_[p]) V₂ = 2)
    {τ₁ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₁}
    {τ₂ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₂}
    (hirr : τ₂.IsIrreducible)
    (htr : ∀ γ : Field.absoluteGaloisGroup ℚ,
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁ (τ₁ γ) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂ (τ₂ γ)) :
    ∃ e : V₁ ≃ₗ[AlgebraicClosure ℚ_[p]] V₂,
      ∀ (γ : Field.absoluteGaloisGroup ℚ) (w : V₁),
        e (τ₁ γ w) = τ₂ γ (e w) := by
  classical
  letI : Module (MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) V₁ :=
    Module.compHom V₁
      (Representation.asAlgebraHom τ₁.toRepresentation).toRingHom
  letI : Module (MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) V₂ :=
    Module.compHom V₂
      (Representation.asAlgebraHom τ₂.toRepresentation).toRingHom
  -- the group-algebra actions unfold to `asAlgebraHom` application
  have hsmul₁ : ∀ (x : MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) (v : V₁),
      x • v = Representation.asAlgebraHom τ₁.toRepresentation x v :=
    fun _ _ => rfl
  have hsmul₂ : ∀ (x : MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) (v : V₂),
      x • v = Representation.asAlgebraHom τ₂.toRepresentation x v :=
    fun _ _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ_[p])
      (MonoidAlgebra (AlgebraicClosure ℚ_[p])
        (Field.absoluteGaloisGroup ℚ)) V₁ := ⟨fun c x v => by
    rw [hsmul₁, hsmul₁, map_smul]
    rfl⟩
  haveI : IsScalarTower (AlgebraicClosure ℚ_[p])
      (MonoidAlgebra (AlgebraicClosure ℚ_[p])
        (Field.absoluteGaloisGroup ℚ)) V₂ := ⟨fun c x v => by
    rw [hsmul₂, hsmul₂, map_smul]
    rfl⟩
  -- irreducibility transfers to simplicity of the group-algebra module
  haveI hAs : IsSimpleModule (MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) τ₂.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
  haveI hsimple : IsSimpleModule (MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) V₂ :=
    IsSimpleModule.congr
      ({ toFun := id, invFun := id, map_add' := fun _ _ => rfl,
         map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
         right_inv := fun _ => rfl } :
        V₂ ≃ₗ[MonoidAlgebra (AlgebraicClosure ℚ_[p])
          (Field.absoluteGaloisGroup ℚ)] τ₂.toRepresentation.asModule)
  -- trace agreement extends linearly over the group algebra
  have htrA : ∀ x : MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ),
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁
          (Representation.asAlgebraHom τ₁.toRepresentation x) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂
          (Representation.asAlgebraHom τ₂.toRepresentation x) := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | single g a =>
      rw [Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, map_smul, map_smul]
      exact congrArg _ (htr g)
  have htrEnd : ∀ x : MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ),
      LinearMap.trace (AlgebraicClosure ℚ_[p]) V₁
          (Module.toModuleEnd (AlgebraicClosure ℚ_[p])
            (S := MonoidAlgebra (AlgebraicClosure ℚ_[p])
              (Field.absoluteGaloisGroup ℚ)) V₁ x) =
        LinearMap.trace (AlgebraicClosure ℚ_[p]) V₂
          (Module.toModuleEnd (AlgebraicClosure ℚ_[p])
            (S := MonoidAlgebra (AlgebraicClosure ℚ_[p])
              (Field.absoluteGaloisGroup ℚ)) V₂ x) := by
    intro x
    have hE₁ : Module.toModuleEnd (AlgebraicClosure ℚ_[p])
        (S := MonoidAlgebra (AlgebraicClosure ℚ_[p])
          (Field.absoluteGaloisGroup ℚ)) V₁ x =
        Representation.asAlgebraHom τ₁.toRepresentation x :=
      LinearMap.ext fun v => hsmul₁ x v
    have hE₂ : Module.toModuleEnd (AlgebraicClosure ℚ_[p])
        (S := MonoidAlgebra (AlgebraicClosure ℚ_[p])
          (Field.absoluteGaloisGroup ℚ)) V₂ x =
        Representation.asAlgebraHom τ₂.toRepresentation x :=
      LinearMap.ext fun v => hsmul₂ x v
    rw [hE₁, hE₂]
    exact htrA x
  -- the abstract char-0 Brauer–Nesbitt core
  obtain ⟨eA⟩ := nonempty_linearEquiv_of_trace_eq
    (k := AlgebraicClosure ℚ_[p])
    (A := MonoidAlgebra (AlgebraicClosure ℚ_[p])
      (Field.absoluteGaloisGroup ℚ)) hfr₁ hfr₂ htrEnd
  refine ⟨eA.restrictScalars (AlgebraicClosure ℚ_[p]), fun γ w => ?_⟩
  have h₁ : τ₁ γ w =
      (MonoidAlgebra.of (AlgebraicClosure ℚ_[p])
        (Field.absoluteGaloisGroup ℚ) γ) • w := by
    rw [hsmul₁, Representation.asAlgebraHom_of]
    rfl
  have h₂ : τ₂ γ (eA w) =
      (MonoidAlgebra.of (AlgebraicClosure ℚ_[p])
        (Field.absoluteGaloisGroup ℚ) γ) • (eA w) := by
    rw [hsmul₂, Representation.asAlgebraHom_of]
    rfl
  show eA (τ₁ γ w) = τ₂ γ (eA w)
  rw [h₁, h₂]
  exact map_smul eA _ w

/-- **Trace rigidity over `ℚ̄_p`** (PROVEN — Chebotarev +
characteristic-zero Brauer–Nesbitt, the char-0 analogue of the mod-`ℓ`
instance `not_isIrreducible_of_charpoly_eq` in `Chebotarev.lean`): two
continuous 2-dimensional representations of `Γ ℚ` over `ℚ̄_p` with
equal Frobenius characteristic polynomials away from a finite set of
places, the second irreducible, are equivalent. DERIVED from the
density half `trace_eq_of_charFrob_eq` (the trace-agreement locus is
closed and contains the dense Frobenius conjugates, so the traces
agree everywhere — only the linear coefficient of the charpoly is
consumed) and the Brauer–Nesbitt half `exists_linearEquiv_of_trace_eq`
(group-algebra modules with equal traces, the second simple, are
isomorphic; Curtis–Reiner §30.16 hand-rolled at dimension 2 via
mathlib's Jacobson density theorem). The conclusion is a bare
equivariant linear isomorphism — no continuity clause, since the
consumer (the Carayol leaf) transports only charpoly-visible and
inertia-theoretic data across it. -/
theorem exists_linearEquiv_of_charFrob_eq
    {V₁ : Type*} [AddCommGroup V₁] [Module (AlgebraicClosure ℚ_[p]) V₁]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₁]
    [Module.Free (AlgebraicClosure ℚ_[p]) V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module (AlgebraicClosure ℚ_[p]) V₂]
    [Module.Finite (AlgebraicClosure ℚ_[p]) V₂]
    [Module.Free (AlgebraicClosure ℚ_[p]) V₂]
    (hrank₁ : Module.rank (AlgebraicClosure ℚ_[p]) V₁ = 2)
    (hrank₂ : Module.rank (AlgebraicClosure ℚ_[p]) V₂ = 2)
    {τ₁ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₁}
    {τ₂ : GaloisRep ℚ (AlgebraicClosure ℚ_[p]) V₂}
    (hirr : τ₂.IsIrreducible)
    {S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (h : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      τ₁.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        τ₂.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : V₁ ≃ₗ[AlgebraicClosure ℚ_[p]] V₂,
      ∀ (γ : Field.absoluteGaloisGroup ℚ) (w : V₁),
        e (τ₁ γ w) = τ₂ γ (e w) := by
  have hfr₁ : Module.finrank (AlgebraicClosure ℚ_[p]) V₁ = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank₁)
  have hfr₂ : Module.finrank (AlgebraicClosure ℚ_[p]) V₂ = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank₂)
  exact exists_linearEquiv_of_trace_eq hfr₁ hfr₂ hirr
    (trace_eq_of_charFrob_eq hfr₁ hfr₂ h)

/-- **The `M ∣ 2` endgame arithmetic** (PROVEN glue for the Carayol
assembly below): a positive natural number all of whose prime factors
are `2` and which `4` does not divide is a divisor of `2`. Immediate
from `Nat.eq_prime_pow_of_unique_prime_dvd`: `M = 2 ^ k` with
`k ≤ 1`. -/
theorem dvd_two_of_forall_prime_eq_two {M : ℕ} (hM : 0 < M)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ M → q = 2) (h4 : ¬ (4 ∣ M)) : M ∣ 2 := by
  have hMpow : M = 2 ^ M.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hM.ne'
      fun {d} hd hdM => h2 d hd hdM
  rw [hMpow] at h4 ⊢
  rcases Nat.lt_or_ge M.primeFactorsList.length 2 with hk | hk
  · calc (2 : ℕ) ^ M.primeFactorsList.length ∣ 2 ^ 1 :=
          pow_dvd_pow 2 (by omega)
      _ = 2 := pow_one 2
  · exact absurd ((show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 hk) h4

/-- **The fixed-line criterion in dimension 2** (PROVEN glue — the
linear-algebra heart of the tame-at-2 transport): an endomorphism `T`
of a 2-dimensional space that preserves a surjective functional `π`
(`π ∘ T = π`) and has determinant `1` fixes the kernel line of `π`
pointwise. Proof: `ker π` is a line, `T`-stable since `π (T u) = π u`;
in the basis `(k₀, w₀)` with `k₀` spanning the kernel and `π w₀ = 1`
the matrix of `T` is upper triangular with diagonal `(c, 1)`, so
`det T = c = 1` and `T` is the identity on the kernel. -/
theorem end_apply_eq_self_of_det_one_of_comp_eq
    {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
    [Module.Finite F W]
    (hrank : Module.finrank F W = 2)
    (T : Module.End F W)
    (π : W →ₗ[F] F) (hπ : Function.Surjective π)
    (hcomm : ∀ u : W, π (T u) = π u)
    (hdet : LinearMap.det T = 1)
    {w : W} (hw : π w = 0) : T w = w := by
  classical
  have hker : Module.finrank F (LinearMap.ker π) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [hrank, LinearMap.range_eq_top.mpr hπ, finrank_top] at h
    simp only [Module.finrank_self] at h
    omega
  obtain ⟨k₀', hk₀ne, hk₀span⟩ := finrank_eq_one_iff'.mp hker
  have hk₀mem : π (k₀' : W) = 0 := k₀'.2
  have hk₀ne' : (k₀' : W) ≠ 0 := fun h => hk₀ne (Subtype.ext h)
  obtain ⟨w₀, hw₀⟩ := hπ 1
  have hTk₀mem : T (k₀' : W) ∈ LinearMap.ker π := by
    simp [LinearMap.mem_ker, hcomm, hk₀mem]
  obtain ⟨c, hc⟩ := hk₀span ⟨T (k₀' : W), hTk₀mem⟩
  have hc' : c • (k₀' : W) = T (k₀' : W) := congrArg Subtype.val hc
  have hTw₀mem : T w₀ - w₀ ∈ LinearMap.ker π := by
    simp [LinearMap.mem_ker, hcomm, hw₀]
  obtain ⟨x, hx⟩ := hk₀span ⟨T w₀ - w₀, hTw₀mem⟩
  have hx' : x • (k₀' : W) = T w₀ - w₀ := congrArg Subtype.val hx
  have hli : LinearIndependent F ![(k₀' : W), w₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : π (s • (k₀' : W) + t • w₀) = t := by
      simp [map_add, map_smul, hk₀mem, hw₀]
    rw [hst, map_zero] at h1
    subst h1
    simp only [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hk₀ne', rfl⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank F W := by
    simp [hrank]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![(k₀' : W), w₀] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hb0 : b 0 = (k₀' : W) := by rw [hb]; simp
  have hb1 : b 1 = w₀ := by rw [hb]; simp
  have hT0 : T (b 0) = c • b 0 := by rw [hb0, ← hc']
  have hT1 : T (b 1) = x • b 0 + b 1 := by
    rw [hb0, hb1]
    have h2 := hx'
    rw [eq_sub_iff_add_eq] at h2
    rw [h2]
  have e00 : (LinearMap.toMatrix b b) T 0 0 = c := by
    rw [LinearMap.toMatrix_apply, hT0, map_smul, b.repr_self]
    simp
  have e10 : (LinearMap.toMatrix b b) T 1 0 = 0 := by
    rw [LinearMap.toMatrix_apply, hT0, map_smul, b.repr_self]
    simp
  have e01 : (LinearMap.toMatrix b b) T 0 1 = x := by
    rw [LinearMap.toMatrix_apply, hT1, map_add, map_smul, b.repr_self,
      b.repr_self]
    simp
  have e11 : (LinearMap.toMatrix b b) T 1 1 = 1 := by
    rw [LinearMap.toMatrix_apply, hT1, map_add, map_smul, b.repr_self,
      b.repr_self]
    simp
  have hdet' := LinearMap.det_toMatrix b T
  rw [Matrix.det_fin_two, e00, e10, e01, e11, hdet] at hdet'
  have hcone : c = 1 := by linear_combination hdet'
  have hTfix : T (k₀' : W) = (k₀' : W) := by
    rw [← hc', hcone, one_smul]
  obtain ⟨t, ht⟩ := hk₀span ⟨w, by simpa [LinearMap.mem_ker] using hw⟩
  have ht' : t • (k₀' : W) = w := congrArg Subtype.val ht
  rw [← ht', map_smul, hTfix]

/-- **Transport of unramifiedness across an equivariant linear
equivalence** (PROVEN glue): if `e` intertwines `τ₁` with `τ₂` and
`τ₂` is unramified at `v`, so is `τ₁` — the local inertia acts through
`τ₁` by `e⁻¹ ∘ 1 ∘ e = 1`. Used to carry `hρ.isUnramified` (through
the base-change instance and the rigidity equivalence) to the attached
representation `τ` in the Carayol assembly below. -/
theorem isUnramifiedAt_of_linearEquiv
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module A W₁]
    [AddCommGroup W₂] [Module A W₂]
    {τ₁ : GaloisRep ℚ A W₁} {τ₂ : GaloisRep ℚ A W₂}
    (e : W₁ ≃ₗ[A] W₂)
    (he : ∀ (γ : Field.absoluteGaloisGroup ℚ) (w : W₁),
      e (τ₁ γ w) = τ₂ γ (e w))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    [τ₂.IsUnramifiedAt v] : τ₁.IsUnramifiedAt v := by
  letI := moduleTopology A (Module.End A W₁)
  letI := moduleTopology A (Module.End A W₂)
  constructor
  intro σ hσ
  have h2 := GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := τ₂) hσ
  rw [GaloisRep.ker, MonoidHom.mem_ker] at h2 ⊢
  have hx : (τ₂.toLocal v) σ = (1 : Module.End A W₂) := h2
  rw [GaloisRep.toLocal_apply] at hx
  show (τ₁.toLocal v) σ = (1 : Module.End A W₁)
  rw [GaloisRep.toLocal_apply]
  ext w
  apply e.injective
  rw [Module.End.one_apply, he, hx, Module.End.one_apply]

include hpodd in
/-- **The `p`-adic cyclotomic character is unramified at `2`** (sorry
node — the local-arithmetic leaf of the tame-at-2 transport; for odd
`p` the extension `ℚ_2(μ_{p^∞})/ℚ_2` is unramified): every element of
the inertia at `2` (in the `Z2bar` spelling of
`IsHardlyRamified.isTameAtTwo`) has trivial `p`-adic cyclotomic
character. This is the full-level generalization of the PROVEN mod-3
instance `cyclotomicCharacter_algebraMap_eq_one_of_inertia_two`
(`ModThree.lean`), whose argument is the intended proof at every
level: for each `n` the `p^n`-th roots of unity in `ℚ_[2]ᵃˡᵍ` are
units with pairwise differences of valuation `1` (as `p^n` is odd,
`X^{p^n} − 1` is separable modulo the maximal ideal of `Z2bar`), so an
inertia element — which acts trivially on the residue field — fixes
each of them; via the `lift_map` commuting square its image in `Γ ℚ`
fixes `μ_{p^n} ⊂ ℚᵃˡᵍ`, making the level-`n` cyclotomic character
trivial, and `χ = 1` in `ℤ_[p]ˣ` follows from triviality at every
finite level (`PadicInt.ext_of_toZModPow`). SOUNDNESS: this is the
standard fact that `χ_cyc,p` is unramified away from `p` (Serre,
*Abelian ℓ-adic representations*, I §1.2), specialized to the place
`2 ≠ p`. -/
theorem cyclotomicCharacter_eq_one_of_inertia_two
    {σ : Field.absoluteGaloisGroup ℚ_[2]}
    (hσ : σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ).toRingEquiv)
      = 1 :=
  sorry

/-- **Carayol's prime-to-`p` conductor bound, unramified case** (sorry
node — Carayol, *Sur les représentations `ℓ`-adiques associées aux
formes modulaires de Hilbert*, Ann. Sci. ÉNS 19 (1986), Théorème (A);
for weight 2 over `ℚ` the modular-curve cases are Deligne–Rapoport and
Langlands): if a 2-dimensional continuous `ℚ̄_p`-representation `τ`
matching the Hecke polynomials of the weight-2 newform `g` of level
`M ≥ 1` away from a finite set is unramified at a prime `q ≠ p`, then
`q ∤ M`. Classical proof: the attached representation `ρ_{g,λ}` is
irreducible (Ribet, 1977), so Chebotarev density plus Brauer–Nesbitt
identify `τ ≅ ρ_{g,λ} ⊗ ℚ̄_p` from the charpoly matching (both
representations are continuous); Carayol's theorem gives
`ord_q(M) = a_q(ρ_{g,λ})` (the prime-to-`p` Artin conductor exponent)
for `q ≠ p`, and `IsUnramifiedAt` is exactly `a_q = 0`. SOUNDNESS
AUDIT (2026-07-24): the hypotheses are non-vacuously satisfiable —
take any classical newform `g`, `τ := ρ_{g,λ}`, and any good prime `q`
— and the statement quantifies over the `IsWeightTwoNewform` carrier,
whose inhabitants are exactly the classical newforms (carrier
audit), so every instance is an instance of the cited theorems. -/
theorem weightTwoNewform_not_dvd_level_of_isUnramifiedAt
    {M : ℕ} (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
    {τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p])}
    {S_τ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hτ : ∀ (r : ℕ) (hr : r.Prime),
      hr.toHeightOneSpectrumRingOfIntegersRat ∉ S_τ →
      τ.charFrob hr.toHeightOneSpectrumRingOfIntegersRat =
        Polynomial.X ^ 2
          - Polynomial.C (κ (heckeCoeff M g r)) * Polynomial.X
          + Polynomial.C ((r : AlgebraicClosure ℚ_[p])))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hun : τ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) :
    ¬ q ∣ M :=
  sorry

include hpodd in
/-- **The conductor bound at `p`: flat implies `p ∤ M`** (sorry node —
Saito, *Modular forms and `p`-adic Hodge theory*, Invent. Math. 129
(1997), local–global compatibility at `p`, with the weight-2 flatness
input from Raynaud/Fontaine): if the representation `τ` attached (in
the charpoly-matching sense) to the weight-2 newform `g` of level `M`
is equivalent, through `e`, to the base change of an integral
representation `ρ` over the local pro-`p` coefficient ring `R` that is
FLAT at `p` (`GaloisRep.IsFlatAt` — finite flat prolongations of all
finite quotients), then `p ∤ M`. Classical proof: flatness makes
`ρ|_{G_p}` the generic fiber of a `p`-divisible group, hence
crystalline with Hodge–Tate weights in `{0, 1}` (Raynaud, Bull. SMF 102
(1974); Fontaine); by rigidity `τ ≅ ρ_{g,λ} ⊗ ℚ̄_p` (Ribet
irreducibility + Chebotarev/Brauer–Nesbitt as in the unramified leaf),
so `ρ_{g,λ}` is crystalline at `p`; but for `p ∥ M` the local
representation of a weight-2 newform at `p` is an unramified twist of
Steinberg — semistable non-crystalline (Deligne–Rapoport/Langlands,
Saito), and for `p² ∣ M` it is not even semistable. Hence `p ∤ M`.
The oddness of `p` keeps the flatness-to-crystalline dictionary in
its classical range (`e = 1 < p − 1`). SOUNDNESS AUDIT (2026-07-24):
non-vacuously satisfiable — any newform of level prime to `p` with
its stable lattice over `R = 𝒪_λ` realizes all hypotheses — and every
instance is covered by the cited theorems through the carrier
audit. -/
theorem weightTwoNewform_not_dvd_level_p_of_isFlatAt
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hflat : ρ.IsFlatAt
      (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat)
    {M : ℕ} (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
    {τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p])}
    {S_τ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hτ : ∀ (r : ℕ) (hr : r.Prime),
      hr.toHeightOneSpectrumRingOfIntegersRat ∉ S_τ →
      τ.charFrob hr.toHeightOneSpectrumRingOfIntegersRat =
        Polynomial.X ^ 2
          - Polynomial.C (κ (heckeCoeff M g r)) * Polynomial.X
          + Polynomial.C ((r : AlgebraicClosure ℚ_[p])))
    (e : (Fin 2 → AlgebraicClosure ℚ_[p]) ≃ₗ[AlgebraicClosure ℚ_[p]]
      (AlgebraicClosure ℚ_[p] ⊗[R] V))
    (he : ∀ (γ : Field.absoluteGaloisGroup ℚ)
        (w : Fin 2 → AlgebraicClosure ℚ_[p]),
      e (τ γ w) = ρ.baseChange (AlgebraicClosure ℚ_[p]) γ (e w)) :
    ¬ p ∣ M :=
  sorry

include hpodd in
/-- **The conductor bound at `2`: a tame fixed line implies `4 ∤ M`**
(sorry node — Carayol's theorem at the place `2 ≠ p` combined with the
Artin conductor exponent formula): if the representation `τ` attached
(in the charpoly-matching sense) to the weight-2 newform `g` of level
`M` admits a surjective functional `π₂` whose kernel line is fixed
POINTWISE by the inertia at `2` (`hfix`) and on whose quotient the
inertia at `2` acts trivially (`hquot`), then `4 ∤ M`. Classical
proof: by rigidity `τ ≅ ρ_{g,λ} ⊗ ℚ̄_p` (Ribet irreducibility +
Chebotarev/Brauer–Nesbitt); transporting the hypotheses, the inertia
`I₂` acts on `ρ_{g,λ}` through unipotent upper-triangular matrices
with an `I₂`-pointwise-fixed line, so `dim V^{I₂} ≥ 1`, and the wild
inertia — a pro-2 group acting continuously and unipotently over a
field of residue characteristic `p ≠ 2` (its image is simultaneously
pro-2 as a continuous quotient and pro-`p` as a compact subgroup of
the unipotent group `≅ (ℚ̄_p, +)`) — acts trivially, so the Swan
conductor vanishes; the Artin exponent is
`a₂ = (2 − dim V^{I₂}) + Sw₂ ≤ 1`, and Carayol gives
`ord_2(M) = a₂ ≤ 1`. The inertia here is spelled over `Γ ℚ_[2]` via
`Z2bar` exactly as in `IsHardlyRamified.isTameAtTwo` (the PROVEN
bridge `localInertia_two_eq_map_padic` of `ModThree.lean` converts to
the adic-completion spelling up to conjugacy when needed). SOUNDNESS
AUDIT (2026-07-24): non-vacuously satisfiable — any newform of odd
level or of level `2·(odd)` with its attached representation
realizes the hypotheses — and every instance follows from the cited
theorems through the carrier audit. -/
theorem weightTwoNewform_not_four_dvd_level_of_inertia_two
    {M : ℕ} (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
    {τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p])}
    {S_τ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hτ : ∀ (r : ℕ) (hr : r.Prime),
      hr.toHeightOneSpectrumRingOfIntegersRat ∉ S_τ →
      τ.charFrob hr.toHeightOneSpectrumRingOfIntegersRat =
        Polynomial.X ^ 2
          - Polynomial.C (κ (heckeCoeff M g r)) * Polynomial.X
          + Polynomial.C ((r : AlgebraicClosure ℚ_[p])))
    (π₂ : (Fin 2 → AlgebraicClosure ℚ_[p]) →ₗ[AlgebraicClosure ℚ_[p]]
      AlgebraicClosure ℚ_[p])
    (hπ₂ : Function.Surjective π₂)
    (hquot : ∀ σ ∈ AddSubgroup.inertia
        ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
        (Field.absoluteGaloisGroup ℚ_[2]),
      ∀ w : Fin 2 → AlgebraicClosure ℚ_[p],
        π₂ (τ.map (algebraMap ℚ ℚ_[2]) σ w) = π₂ w)
    (hfix : ∀ σ ∈ AddSubgroup.inertia
        ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
        (Field.absoluteGaloisGroup ℚ_[2]),
      ∀ w : Fin 2 → AlgebraicClosure ℚ_[p],
        π₂ w = 0 → τ.map (algebraMap ℚ ℚ_[2]) σ w = w) :
    ¬ (4 ∣ M) :=
  sorry

/-- **Carayol's conductor bound on the hardly ramified class**
(DECOMPOSED 2026-07-24 into the per-place cut above and now a PROVEN
assembly): let `g` be a weight-2 newform of level `M` (the
minimal-level carrier), `τ` a representation matching its Hecke
polynomials away from a finite set (the attachment shape produced by
`exists_galoisRep_charFrob_of_weightTwoNewform`), and suppose `τ` is
equivalent to the base change to `ℚ̄_p` of a HARDLY RAMIFIED integral
representation `ρ`. Then `M ∣ 2`. The assembly follows the classical
per-place conductor computation verbatim:

* at primes `q ∉ {2, p}`: `ρ` is unramified (`isUnramified`), the
  base-change instance and the PROVEN transport
  `isUnramifiedAt_of_linearEquiv` carry this through `e` to `τ`, and
  the Carayol leaf
  `weightTwoNewform_not_dvd_level_of_isUnramifiedAt` gives `q ∤ M`;
* at `p`: `ρ` is flat (`isFlat`), and the Saito/flatness leaf
  `weightTwoNewform_not_dvd_level_p_of_isFlatAt` gives `p ∤ M`;
* at `2`: the `isTameAtTwo` structure of `ρ` transports through `e`
  to `τ` (PROVEN here): the functional `π₂ := (lift of π) ∘ e` is
  surjective, inertia-equivariant with quotient character `δ` trivial
  on inertia, and its kernel line is fixed POINTWISE by the inertia
  at `2` — by the fixed-line criterion
  `end_apply_eq_self_of_det_one_of_comp_eq`, since
  `det τ = det ρ = χ_cyc` on inertia at `2` is `1` by the cyclotomic
  leaf `cyclotomicCharacter_eq_one_of_inertia_two` (odd `p`); the
  at-2 conductor leaf
  `weightTwoNewform_not_four_dvd_level_of_inertia_two` then gives
  `4 ∤ M`.

The endgame `M ∣ 2` is the PROVEN arithmetic
`dvd_two_of_forall_prime_eq_two` (every prime factor of `M` is `2`
since `p` is odd, and `4 ∤ M`). SOUNDNESS AUDIT (2026-07-24, carried
over): each per-place leaf is a non-vacuously satisfiable literature
statement (see the individual audits); the hypothesis-level
unsatisfiability that previous audits tracked (no irreducible hardly
ramified representation is modular — Wiles' final contradiction) is
no longer concentrated in any single leaf: the leaves are individually
true and satisfiable statements about newforms, and the collapse
lives, as it classically does, in the CONJUNCTION of the modularity
hypotheses upstream. -/
theorem weightTwoNewform_level_dvd_two_of_isHardlyRamified
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hρ : IsHardlyRamified hpodd hv ρ)
    {M : ℕ} (hM : 0 < M) {g : CuspForm (Gamma0GL M) 2}
    (hg : IsWeightTwoNewform M g)
    (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
    {τ : GaloisRep ℚ (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p])}
    {S_τ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hτ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_τ →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        Polynomial.X ^ 2
          - Polynomial.C (κ (heckeCoeff M g q)) * Polynomial.X
          + Polynomial.C ((q : AlgebraicClosure ℚ_[p])))
    (e : (Fin 2 → AlgebraicClosure ℚ_[p]) ≃ₗ[AlgebraicClosure ℚ_[p]]
      (AlgebraicClosure ℚ_[p] ⊗[R] V))
    (he : ∀ (γ : Field.absoluteGaloisGroup ℚ)
        (w : Fin 2 → AlgebraicClosure ℚ_[p]),
      e (τ γ w) = ρ.baseChange (AlgebraicClosure ℚ_[p]) γ (e w)) :
    M ∣ 2 := by
  classical
  -- transport of the tame-at-2 structure of `ρ` to `τ` through `e`
  obtain ⟨π, hπsurj, δ, hδ⟩ := hρ.isTameAtTwo
  set π₂ : (Fin 2 → AlgebraicClosure ℚ_[p]) →ₗ[AlgebraicClosure ℚ_[p]]
      AlgebraicClosure ℚ_[p] :=
    (LinearMap.liftBaseChange (AlgebraicClosure ℚ_[p])
      ((Algebra.linearMap R (AlgebraicClosure ℚ_[p])).comp π)).comp
      (e : (Fin 2 → AlgebraicClosure ℚ_[p]) →ₗ[AlgebraicClosure ℚ_[p]]
        AlgebraicClosure ℚ_[p] ⊗[R] V) with hπ₂def
  have hπ₂surj : Function.Surjective π₂ := by
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨e.symm (c ⊗ₜ[R] v₀), ?_⟩
    rw [hπ₂def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.apply_symm_apply, LinearMap.liftBaseChange_tmul,
      LinearMap.comp_apply, hv₀]
    simp
  -- the inertia at `2` preserves `π₂`-values: `δ` is unramified
  have hquot : ∀ σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2]),
      ∀ w : Fin 2 → AlgebraicClosure ℚ_[p],
        π₂ (τ.map (algebraMap ℚ ℚ_[2]) σ w) = π₂ w := by
    intro σ hσ w
    have hδσ : δ σ = 1 := by
      have h := (hδ σ 0).2.1 hσ
      rwa [GaloisRep.ker, MonoidHom.mem_ker] at h
    have hcommρ : ∀ x : (AlgebraicClosure ℚ_[p]) ⊗[R] V,
        LinearMap.liftBaseChange (AlgebraicClosure ℚ_[p])
          ((Algebra.linearMap R (AlgebraicClosure ℚ_[p])).comp π)
          (ρ.baseChange (AlgebraicClosure ℚ_[p])
            (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ) x) =
        LinearMap.liftBaseChange (AlgebraicClosure ℚ_[p])
          ((Algebra.linearMap R (AlgebraicClosure ℚ_[p])).comp π) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r v =>
          rw [GaloisRep.baseChange_tmul, LinearMap.liftBaseChange_tmul,
            LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
            LinearMap.comp_apply]
          have h := (hδ σ v).1
          rw [GaloisRep.map_apply] at h
          rw [h, hδσ, Module.End.one_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hmap : τ.map (algebraMap ℚ ℚ_[2]) σ =
        τ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ) :=
      GaloisRep.map_apply τ (algebraMap ℚ ℚ_[2]) σ
    rw [hmap, hπ₂def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he, hcommρ]
  -- the determinant of `τ` is trivial on the inertia at `2`:
  -- it is `χ_cyc` through `e`, and `χ_cyc` is unramified at `2`
  have hdet1 : ∀ σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2]),
      LinearMap.det (τ.map (algebraMap ℚ ℚ_[2]) σ) = 1 := by
    intro σ hσ
    have hmap : τ.map (algebraMap ℚ ℚ_[2]) σ =
        τ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ) :=
      GaloisRep.map_apply τ (algebraMap ℚ ℚ_[2]) σ
    have hconj : τ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ) =
        (e.symm : AlgebraicClosure ℚ_[p] ⊗[R] V →ₗ[AlgebraicClosure ℚ_[p]]
          (Fin 2 → AlgebraicClosure ℚ_[p])) ∘ₗ
        (ρ.baseChange (AlgebraicClosure ℚ_[p])
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ)) ∘ₗ
        (e.symm.symm : (Fin 2 → AlgebraicClosure ℚ_[p])
          →ₗ[AlgebraicClosure ℚ_[p]] AlgebraicClosure ℚ_[p] ⊗[R] V) := by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_symm]
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply]
    have hbc : ρ.baseChange (AlgebraicClosure ℚ_[p])
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ) =
        LinearMap.baseChange (AlgebraicClosure ℚ_[p])
          (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ)) := by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r v => rw [GaloisRep.baseChange_tmul, LinearMap.baseChange_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    have hdetρ : LinearMap.det
        (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ)) = 1 := by
      have h := hρ.det (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ)
      rw [GaloisRep.det_apply] at h
      rw [h, cyclotomicCharacter_eq_one_of_inertia_two hpodd hσ,
        Units.val_one, map_one]
    rw [hmap, hconj, LinearMap.det_conj, hbc, LinearMap.det_baseChange,
      hdetρ, map_one]
  -- the inertia at `2` fixes the kernel line of `π₂` pointwise
  have hfix : ∀ σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2]),
      ∀ w : Fin 2 → AlgebraicClosure ℚ_[p],
        π₂ w = 0 → τ.map (algebraMap ℚ ℚ_[2]) σ w = w := by
    intro σ hσ w hw
    exact end_apply_eq_self_of_det_one_of_comp_eq (by simp)
      (τ.map (algebraMap ℚ ℚ_[2]) σ) π₂ hπ₂surj (hquot σ hσ)
      (hdet1 σ hσ) hw
  -- the three per-place conductor bounds
  have h4 : ¬ (4 ∣ M) :=
    weightTwoNewform_not_four_dvd_level_of_inertia_two hpodd hM hg κ hτ
      π₂ hπ₂surj hquot hfix
  have hpM : ¬ p ∣ M :=
    weightTwoNewform_not_dvd_level_p_of_isFlatAt hpodd hρ.isFlat hM hg κ hτ
      e he
  have hprime : ∀ q : ℕ, q.Prime → q ∣ M → q = 2 := by
    intro q hq hqM
    by_contra hq2
    rcases eq_or_ne q p with rfl | hqp
    · exact hpM hqM
    · haveI := hρ.isUnramified q hq ⟨hq2, hqp⟩
      have hun : τ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
        isUnramifiedAt_of_linearEquiv (τ₂ := ρ.baseChange
          (AlgebraicClosure ℚ_[p])) e he
          hq.toHeightOneSpectrumRingOfIntegersRat
      exact weightTwoNewform_not_dvd_level_of_isUnramifiedAt hM hg κ hτ
        hq hqp hun hqM
  exact dvd_two_of_forall_prime_eq_two hM hprime h4

end ConductorCut

/-- **Level lowering to conductor level `M ∣ 2`** (pillar 5's heart —
the Carayol-conductor/Ribet content; DECOMPOSED 2026-07-24 into the
FOUNDER CUT of the section above and now a PROVEN assembly): if the
Frobenius traces of an irreducible hardly ramified `p`-adic
representation `ρ` arise (away from a finite set, in the `-a_q` trace
convention) from a weight-2 normalized eigenform `f` of some level
`N ≥ 1`, then they arise, in the same sense, from a weight-2
normalized eigenform of level `M` dividing `2`. The assembly follows
the classical route verbatim:

1. *Newform descent*
   (`exists_weightTwoNewform_of_weightTwoEigenform`, PROVEN): behind
   `f` lies a minimal-level eigenform `g` of level `M ∣ N` with the
   same eigensystem away from `N`; the `p`-adic embedding transports
   to its Hecke field (`exists_ringHom_heckeField_of_qCoeff_eq`,
   PROVEN).
2. *Attachment* (`exists_galoisRep_charFrob_of_weightTwoNewform`,
   sorry leaf): `g` has an attached 2-dimensional
   `ℚ̄_p`-representation `τ` with the Hecke characteristic
   polynomials at good primes (Eichler–Shimura).
3. *Rigidity* (`exists_linearEquiv_of_charFrob_eq`, PROVEN
   2026-07-24 — Chebotarev + char-0 Brauer–Nesbitt):
   `τ ≅ ρ ⊗ ℚ̄_p` — their Frobenius characteristic polynomials agree
   away from a finite set, because the trace matching `hmatch`
   upgrades to full charpoly matching through the determinant
   normalization (`charFrob_map_coeff_zero_of_isHardlyRamified`,
   PROVEN from `det = χ_cyc`) and the monic-quadratic shape, and
   `ρ ⊗ ℚ̄_p` is irreducible (`hirr`).
4. *Carayol's conductor bound*
   (`weightTwoNewform_level_dvd_two_of_isHardlyRamified`, since
   2026-07-24 itself a PROVEN per-place assembly over three conductor
   leaves and the cyclotomic-inertia leaf — see its docstring): the
   level of a newform whose attached representation is (through the
   rigidity equivalence) the base change of a hardly ramified
   representation divides `2` — Ribet's mod-`p` level lowering
   (Invent. Math. 100 (1990)) is the residual counterpart used when
   this content is reached through the Khare–Wintenberger induction
   instead.
5. The conclusion matches `ρ`'s traces with `g`'s coefficients
   through `κ` away from `S₁ ∪ {v : v ∣ N}` — bookkeeping, proven
   inline.

SOUNDNESS/DEPTH AUDIT (2026-07-24, carried over and sharpened): both
level-`M ∣ 2` spaces are proven empty in this file
(`weightTwoEigenform_level_one_false`,
`weightTwoEigenform_level_two_false`), so this theorem's conclusion is
unsatisfiable and it equivalently asserts that its hypotheses are
contradictory — that no irreducible hardly ramified `p`-adic
representation is modular of ANY level, which is exactly Wiles' final
contradiction. The previous audit predicted that a finer decomposition
must build the missing step 1–4 vocabulary rather than push the
contradiction out of this leaf; the section above does precisely
that. All remaining sorried leaves of this subtree — the attachment
and rigidity leaves here, and the per-place conductor leaves behind
the (now assembled) Carayol step — are non-vacuously satisfiable
literature statements; the hypothesis-level contradiction is no
longer concentrated in any single leaf but lives in the conjunction
of the modularity hypotheses, as it classically does (see the
Carayol assembly's audit). -/
theorem exists_eigenform_level_dvd_two_of_trace_eq
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (_hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (_hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {N : ℕ} (hN : 0 < N) {f : CuspForm (Gamma0GL N) 2}
    (hf : IsWeightTwoEigenform N f)
    (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
    {S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hmatch : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
      ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
        - ι (heckeCoeff N f q)) :
    ∃ (M : ℕ) (_ : M ∣ 2) (g : CuspForm (Gamma0GL M) 2)
      (_ : IsWeightTwoEigenform M g)
      (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
      (S₂ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₂ →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - κ (heckeCoeff M g q) := by
  classical
  -- step 1: the underlying newform and the transported embedding
  obtain ⟨M, hMN, hM0, g, hgnew, hagree⟩ :=
    exists_weightTwoNewform_of_weightTwoEigenform hN hf
  obtain ⟨κ, hκ⟩ := exists_ringHom_heckeField_of_qCoeff_eq hM0
    hgnew.toIsWeightTwoEigenform ι hagree
  -- step 2: the attached representation of the newform
  obtain ⟨τ, S_τ, hτ⟩ :=
    exists_galoisRep_charFrob_of_weightTwoNewform hM0 hgnew κ
  -- the places over the primes dividing `N`
  have hbadmem : ∀ (q : ℕ) (hq : q.Prime), q ∣ N →
      hq.toHeightOneSpectrumRingOfIntegersRat ∈
        N.primeFactors.attach.image fun t =>
          (Nat.prime_of_mem_primeFactors
            t.2).toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqN
    exact Finset.mem_image.mpr
      ⟨⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqN, hN.ne'⟩⟩,
        Finset.mem_attach _ _, rfl⟩
  -- full charpoly comparison of `τ` with `ρ ⊗ ℚ̄_p` off the union set
  have hcomp : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉
        ((S₁ ∪ S_τ) ∪
          ((N.primeFactors.attach.image fun t =>
              (Nat.prime_of_mem_primeFactors
                t.2).toHeightOneSpectrumRingOfIntegersRat) ∪
            {(Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat})) →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (ρ.baseChange (AlgebraicClosure ℚ_[p])).charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqS
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hqS
    obtain ⟨⟨hqS₁, hqSτ⟩, hqbad, hqvp⟩ := hqS
    have hqN : ¬ q ∣ N := fun hdvd => hqbad (hbadmem q hq hdvd)
    have hqp : q ≠ p := by
      intro hqp'
      subst hqp'
      exact hqvp rfl
    have hmon : ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
        (algebraMap R (AlgebraicClosure ℚ_[p]))).Monic := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
      exact (LinearMap.charpoly_monic _).map _
    have hdeg : ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
        (algebraMap R (AlgebraicClosure ℚ_[p]))).natDegree = 2 := by
      rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
        (LinearMap.charpoly_monic _).natDegree_map,
        LinearMap.charpoly_natDegree]
      exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hv)
    rw [hτ q hq hqSτ, charFrob_baseChange,
      eq_quadratic_of_monic_natDegree_two hmon hdeg,
      hmatch q hq hqS₁,
      charFrob_map_coeff_zero_of_isHardlyRamified hpodd hv hρ hq hqp,
      ← hκ q hq hqN, map_neg]
    ring
  -- step 3: rigidity — `τ` is equivalent to `ρ ⊗ ℚ̄_p`
  have hrank₁ : Module.rank (AlgebraicClosure ℚ_[p])
      (Fin 2 → AlgebraicClosure ℚ_[p]) = 2 := by simp
  have hrank₂ : Module.rank (AlgebraicClosure ℚ_[p])
      (AlgebraicClosure ℚ_[p] ⊗[R] V) = 2 := by
    rw [Module.rank_baseChange, hv]; simp
  obtain ⟨e, he⟩ :=
    exists_linearEquiv_of_charFrob_eq hrank₁ hrank₂ hirr hcomp
  -- step 4: Carayol's conductor bound
  have hM2 : M ∣ 2 :=
    weightTwoNewform_level_dvd_two_of_isHardlyRamified hpodd hv hρ hM0
      hgnew κ hτ e he
  -- step 5: the trace matching with `g` through `κ`
  refine ⟨M, hM2, g, hgnew.toIsWeightTwoEigenform, κ,
    S₁ ∪ (N.primeFactors.attach.image fun t =>
      (Nat.prime_of_mem_primeFactors
        t.2).toHeightOneSpectrumRingOfIntegersRat),
    fun q hq hqS => ?_⟩
  simp only [Finset.mem_union, not_or] at hqS
  obtain ⟨hqS₁, hqbad⟩ := hqS
  rw [hmatch q hq hqS₁, hκ q hq fun hdvd => hqbad (hbadmem q hq hdvd)]

/-- **The residually reducible branch** (pillar 4; DECOMPOSED
2026-07-24 into a PROVEN dichotomy on `p = 3` vs `p ≥ 5` — the AUDIT
of the consumers showed the general-odd-`p` statement is genuinely
needed, since `Family.lean`'s `mem_isCompatible` chain is instantiated
at every odd residue characteristic by `Lift.lean`, so no statement
narrowing is possible; instead the two instances are separated): a
hardly ramified `p`-adic representation that is irreducible over
`ℚ̄_p` but whose residual representation is REDUCIBLE is still
modular, in the same trace sense as pillar 3.

* At `p = 3` the hypotheses are contradictory: by the 3-adic
  classification (`Threeadic.lean`, through the helper
  `not_isIrreducible_baseChange_of_isHardlyRamified_three` above) a
  hardly ramified `3`-adic representation is a global extension of the
  trivial character by a character, hence never irreducible over
  `ℚ̄_3` — refuting `hirr`.
* At `p ≥ 5` the statement is the genuine Skinner–Wiles/Pan content,
  delegated to the sorried leaf
  `exists_weightTwoEigenform_trace_eq_of_residually_reducible_of_five_le`
  above. -/
theorem exists_weightTwoEigenform_trace_eq_of_residually_reducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {kk : Type u} [Field kk] [Finite kk] [Algebra ℤ_[p] kk]
    [TopologicalSpace kk] [DiscreteTopology kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hVbar : Module.rank kk (kk ⊗[R] V) = 2)
    (hρbar : IsHardlyRamified hpodd hVbar (ρ.baseChange kk))
    (hred : ¬ (ρ.baseChange kk).IsIrreducible) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - ι (heckeCoeff N f q) := by
  have hcase : p = 3 ∨ 5 ≤ p := by
    have h2 : 2 ≤ p := hp.out.two_le
    obtain ⟨k, hk⟩ := id hpodd
    revert h2
    omega
  rcases hcase with rfl | hp5
  · -- `p = 3`: the 3-adic classification refutes irreducibility over `ℚ̄_3`
    exact absurd hirr
      (not_isIrreducible_baseChange_of_isHardlyRamified_three hv hZinj hρ
        hsurj hVbar hρbar)
  · -- `p ≥ 5`: the Skinner–Wiles leaf
    exact exists_weightTwoEigenform_trace_eq_of_residually_reducible_of_five_le
      hpodd hv hp5 hZinj hRinj hρ hirr hsurj hVbar hρbar hred

/-- **Level optimization to `Γ₀(2)`** (pillar 5; PROVEN 2026-07-24 as
an assembly over the sorried conductor leaf
`exists_eigenform_level_dvd_two_of_trace_eq` just above, which now
carries the Carayol-conductor/Ribet content, plus the proven emptiness
of both level-`M ∣ 2` eigenform carriers —
`weightTwoEigenform_level_one_false`,
`weightTwoEigenform_level_two_false`; the eigensystem `(E, S, Pv)`
conclusion follows from the resulting contradiction): if the
eigensystem `(E, S, Pv)` of an
irreducible hardly ramified `p`-adic representation `ρ` arises, in the
trace convention of the pillars above, from a weight-2 eigenform `f`
of SOME level `N ≥ 1`, then it arises from a weight-2 eigenform of
level `Γ₀(2)` exactly, matching `Pv` in the `MatchesEigensystem`
sense. Classical route: the coefficient characterization
(`IsWeightTwoEigenform`, Diamond–Shurman Prop. 5.8.5) places behind
`f` a newform `g` of level `M ∣ N` with the same good-prime
eigensystem (D–S Prop. 5.8.4, strong multiplicity one); `ρ` and the
`λ`-adic representation of `g` agree on Frobenius traces, and the
Artin conductor of a hardly ramified representation divides `2`
(unramified outside `2p`; flatness at `p` kills the `p`-part; the
tame rank-1 unramified quotient at `2` bounds the conductor exponent
at `2` by `1`), so Carayol's theorem (*Sur les représentations
`ℓ`-adiques associées aux formes modulaires de Hilbert*, Ann. Sci.
ÉNS 19 (1986); Livné for the residual cases — "level of the newform =
conductor of the representation") forces `M ∣ 2`, and a newform of
level `M ∣ 2` is a normalized eigenform of `S₂(Γ₀(2))` (oldform
inclusion when `M = 1`). Mod-`p` level lowering (Ribet, *On modular
representations of `Gal(ℚ̄/ℚ)` arising from modular forms*, Invent.
Math. 100 (1990); Serre, Duke 1987, §4.1) is the residual counterpart
used when this content is instead reached through the
Khare–Wintenberger induction. Soundness under the collapse
(2026-07-24): `S₂(Γ₀(2)) = 0` is proven above
(`weightTwoEigenform_level_two_false`), so this pillar equivalently
asserts that its hypotheses are contradictory — that an irreducible
hardly ramified `p`-adic representation is never modular of any level
— which is the true classical content (Wiles' final contradiction),
derived in the literature exactly along the route just cited. -/
theorem exists_weightTwoEigenform_level_two_of_trace_eq
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {N : ℕ} (hN : 0 < N) {f : CuspForm (Gamma0GL N) 2}
    (hf : IsWeightTwoEigenform N f)
    (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
    {S₁ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hmatch : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₁ →
      ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
        - ι (heckeCoeff N f q))
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (_heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) =
        (Pv v).map ψ) :
    ∃ (f₂ : CuspForm (Gamma0GL 2) 2)
      (S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      IsWeightTwoEigenform 2 f₂ ∧ MatchesEigensystem 2 f₂ S' Pv := by
  obtain ⟨M, hM2, g, hg, -, -, -⟩ :=
    exists_eigenform_level_dvd_two_of_trace_eq hpodd hv hZinj hRinj hρ hirr hN
      hf ι hmatch
  rcases Nat.prime_two.eq_one_or_self_of_dvd M hM2 with rfl | rfl
  · exact (weightTwoEigenform_level_one_false g hg).elim
  · exact (weightTwoEigenform_level_two_false g hg).elim

/-- **Modularity of the trace system** (DECOMPOSED 2026-07-24 — now a
PROVEN assembly over the pillar section above: residual reduction
(pillar 1), then, according to whether the residual representation is
irreducible, residual modularity + modularity lifting (pillars 2–3) or
the Skinner–Wiles branch (pillar 4); the modularity input of the
trace-field atom
`exists_finiteDimensional_trace_field_of_isIrreducible`): the Frobenius
traces of an IRREDUCIBLE hardly ramified `p`-adic representation are,
away from a finite set of places, the images under a single embedding
`ι : K_f →+* ℚ̄_p` of the coefficients of a single normalized weight-2
eigenform `f` (the trace coefficient of the characteristic polynomial
is `−a_q`). This is Wiles–Taylor–Wiles/Skinner–Wiles modularity in its
weakest useful shadow: no level control is demanded (any `N ≥ 1`
serves — level lowering is NOT consumed here, only by the level-2
statement below), no local behaviour of an attached representation is
mentioned, and the conclusion touches `ρ` only through its traces.
Irreducibility is genuinely consumed (the reducible branch has
non-modular Eisenstein eigensystems and runs through
`exists_rat_trace_coeff_of_not_isIrreducible`). -/
theorem exists_weightTwoEigenform_trace_eq_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[p])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - ι (heckeCoeff N f q) := by
  obtain ⟨kk, hField, hFin, hAlg, hTop, hDisc, hTR, hAlgR, hCS, hsurj,
    hVbar, hρbar⟩ := exists_residual_isHardlyRamified_odd hpodd hv hρ
  letI := hField
  letI := hFin
  letI := hAlg
  letI := hTop
  letI := hDisc
  letI := hTR
  letI := hAlgR
  letI := hCS
  by_cases hirrbar : (ρ.baseChange kk).IsIrreducible
  · obtain ⟨N₀, hN₀, f₀, hf₀, S₀, hmatch₀⟩ :=
      exists_weightTwoEigenform_residual_of_isIrreducible hpodd hVbar
        hρbar hirrbar
    exact exists_weightTwoEigenform_trace_eq_of_matchesResidualTraces hpodd hv
      hZinj hRinj hρ hsurj hVbar hρbar hirrbar hN₀ hf₀ hmatch₀
  · exact exists_weightTwoEigenform_trace_eq_of_residually_reducible hpodd hv
      hZinj hRinj hρ hirr hsurj hVbar hρbar hirrbar

/-- **Modularity at level 2** (DECOMPOSED 2026-07-24 — now a PROVEN
assembly: the trace-system chain
`exists_weightTwoEigenform_trace_eq_of_isIrreducible` above followed by
the level-optimization pillar
`exists_weightTwoEigenform_level_two_of_trace_eq`; the modularity input
of the two realization atoms
`exists_hardlyRamified_ringOfIntegers_realizations`
and `exists_realization_at_two_generated`): the eigensystem `(E, S, Pv)`
of an IRREDUCIBLE hardly ramified `p`-adic representation arises from a
normalized weight-2 eigenform of level `Γ₀(2)` — matching away from a
finite exceptional set `S'` (in the intended construction,
`S ∪ {(p)}`). This is the full classical chain
Wiles–Taylor–Wiles/Skinner–Wiles modularity PLUS Ribet level lowering
to Serre's conductor-2 weight-2 target (Serre, Duke 1987, §4.1;
equivalently the FLT blueprint's "hardly ramified ⇒ automorphic of
level `U₁({2})`"). The level-2 pin-down is load-bearing for the
soundness of the attachment statements consuming this (see the file
docstring): only at level dividing 2 are the attached `λ`-adic
representations of the underlying newform automatically of the hardly
ramified shape at every odd `ℓ`. -/
theorem exists_weightTwoEigenform_of_isIrreducible
    [Algebra R (AlgebraicClosure ℚ_[p])]
    [ContinuousSMul R (AlgebraicClosure ℚ_[p])]
    (hZinj : Function.Injective (algebraMap ℤ_[p] R))
    (hRinj : Function.Injective (algebraMap R (AlgebraicClosure ℚ_[p])))
    (hρ : IsHardlyRamified hpodd hv ρ)
    (hirr : (ρ.baseChange (AlgebraicClosure ℚ_[p])).IsIrreducible)
    {E : Type v} [Field E] [NumberField E] (ψ : E →+* AlgebraicClosure ℚ_[p])
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (Pv : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial E)
    (heig : ∀ v ∉ S,
      (ρ.charFrob v).map (algebraMap R (AlgebraicClosure ℚ_[p])) = (Pv v).map ψ) :
    ∃ (f : CuspForm (Gamma0GL 2) 2)
      (S' : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      IsWeightTwoEigenform 2 f ∧ MatchesEigensystem 2 f S' Pv := by
  obtain ⟨N, hN, f, hf, ι, S₁, hmatch⟩ :=
    exists_weightTwoEigenform_trace_eq_of_isIrreducible hpodd hv hZinj hRinj
      hρ hirr
  exact exists_weightTwoEigenform_level_two_of_trace_eq hpodd hv hZinj hRinj
    hρ hirr hN hf ι hmatch ψ S Pv heig

end GaloisRepresentation.Modularity
