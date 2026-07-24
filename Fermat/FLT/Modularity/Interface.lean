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
   representatives `heckeRep`/`heckeRepInf`) is defined below, with
   its stability on cusp forms (`exists_cuspForm_heckeTransform`) and
   its coefficient formula (`qExpansion_heckeTransform_coeff`) as
   sorried leaves; the eigenform side of Proposition 5.8.5 at prime
   index is PROVEN (`hecke_eigen_coeff_identity`).
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
import Fermat.FLT.GaloisRepresentation.Chebotarev
-- The Khare–Wintenberger cut (Family-free by construction): the
-- headline nonexistence theorem
-- `not_isIrreducible_of_isHardlyRamified_of_five_le` discharging the
-- `ℓ ≥ 5` residual-modularity leaf by contradiction. Proof-body use
-- only.
import Fermat.FLT.Modularity.KhareWintenberger

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
PROVEN assembly over three sharply-stated sorried leaves:

* `exists_cuspForm_heckeTransform` — `T_q` preserves `S₂(Γ₀(N))`
  (Diamond–Shurman Propositions 5.1.5/5.2.1);
* `qExpansion_heckeTransform_coeff` — the classical coefficient
  formula `a_m(T_q f) = a_{qm}(f) + 1_{q ∤ N} · q · a_{m/q}(f)`
  (Diamond–Shurman Proposition 5.2.2 at weight 2);
* `exists_rational_qExpansion_basis` — `S₂(Γ₀(N))` has a finite
  `ℂ`-basis of forms with rational `q`-expansions (finite
  dimensionality plus the rational structure; Diamond–Shurman §6.5,
  Shimura, *Introduction to the Arithmetic Theory*, Theorem 3.52).

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
`q`-expansion is computed by the sorried leaf
`qExpansion_heckeTransform_coeff` below, and its stability on cusp
forms is the sorried leaf `exists_cuspForm_heckeTransform`. -/
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

/-- **Hecke stability of cusp forms** (sorry node; Diamond–Shurman
Propositions 5.1.5 and 5.2.1–5.2.2 for `Γ₀(N)`, weight 2): the Hecke
slash-sum of a weight-2 level-`N` cusp form is again a weight-2
level-`N` cusp form. Classical proof: right multiplication by `γ ∈
Γ₀(N)` permutes the right cosets `Γ₀(N)·heckeRep q j` (resp. the
extra coset at good primes), and `f∣[2](δγᵢ) = f∣[2]γᵢ` for `δ ∈
Γ₀(N)` by slash invariance, so the sum is `Γ₀(N)`-slash-invariant;
each summand is holomorphic on `ℍ` (a Möbius pullback times a nonzero
holomorphic factor); and each summand vanishes at every cusp because
`f` does (the representatives carry cusps to cusps), giving the
`zero_at_cusps` condition. The statement is an existential rather
than a definition because on this pin the bundled `CuspForm`
constructor needs exactly these three unproven facts. -/
theorem exists_cuspForm_heckeTransform {N : ℕ} (hN : 0 < N) {q : ℕ}
    (hq : q.Prime) (f : CuspForm (Gamma0GL N) 2) :
    ∃ g : CuspForm (Gamma0GL N) 2, ⇑g = heckeTransform N q ⇑f :=
  sorry

/-- **The `q`-expansion of the Hecke slash-sum** (sorry node;
Diamond–Shurman Proposition 5.2.2 at weight 2, trivial character):
`a_m(T_q f) = a_{qm}(f)` for `q ∣ N`, and
`a_m(T_q f) = a_{qm}(f) + q·a_{m/q}(f)` (second term only when
`q ∣ m`) for `q ∤ N`. Classical proof, entirely analytic on this
pin's `hasSum_qExpansion` API: substituting the width-1 `q`-expansion
of `f` into the finite slash-sum, the `q` upper-triangular
representatives average the additive character
(`Σ_{j<q} e^{2πimj/q} = q·1_{q ∣ m}`), reindexing `m ↦ qm`, while the
extra representative contributes `q·f(qτ)`, reindexing `m ↦ m/q`; the
resulting everywhere-convergent expansion is THE `q`-expansion by
`UpperHalfPlane.qExpansion_coeff_unique` (analyticity of the cusp
function coming from `exists_cuspForm_heckeTransform`). -/
theorem qExpansion_heckeTransform_coeff {N : ℕ} (hN : 0 < N) {q : ℕ}
    (hq : q.Prime) (f : CuspForm (Gamma0GL N) 2) (m : ℕ) :
    (qExpansion 1 (heckeTransform N q ⇑f)).coeff m =
      qCoeff N f (q * m) +
        (if q ∣ N then 0 else if q ∣ m then (q : ℂ) * qCoeff N f (m / q) else 0) :=
  sorry

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

/-- **Rational basis of `S₂(Γ₀(N))`** (sorry node; the irreducible
geometric leaf of the Hecke-field-finiteness node): the space of
weight-2 level-`N` cusp forms is finite-dimensional over `ℂ` and has
a basis of forms whose `q`-expansion coefficients are RATIONAL. This
combines two classical facts unavailable on this pin: (i) finite
dimensionality of `S₂(Γ₀(N))` (Diamond–Shurman ch. 3 dimension
formulas, `dim = genus X₀(N)`; only level 1 exists on the pin), and
(ii) the rational structure (Diamond–Shurman §6.5; Shimura,
*Introduction to the Arithmetic Theory of Automorphic Functions*,
Theorem 3.52: `S₂` has a basis with INTEGER coefficients — via the
`ℤ`-structure of `H₁(X₀(N), ℤ)` under the Eichler–Shimura
isomorphism, or via the `q`-expansion principle on the modular curve
over `ℚ`). Spanning is phrased with explicit coordinates to keep
consumers span-vocabulary-free. Note the statement is sound for every
`N ≥ 1` including genus-zero levels, where `n = 0` and both clauses
are vacuous. -/
theorem exists_rational_qExpansion_basis {N : ℕ} (hN : 0 < N) :
    ∃ (n : ℕ) (g : Fin n → CuspForm (Gamma0GL N) 2),
      LinearIndependent ℂ g ∧
      (∀ f : CuspForm (Gamma0GL N) 2, ∃ b : Fin n → ℂ, f = ∑ i, b i • g i) ∧
      (∀ i m, ∃ r : ℚ, qCoeff N (g i) m = (r : ℂ)) :=
  sorry

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
over the three sorried leaves `exists_cuspForm_heckeTransform`,
`qExpansion_heckeTransform_coeff` and
`exists_rational_qExpansion_basis`): for a normalized weight-2
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
Hecke algebra. The cut isolates the geometric content in two sorried
leaves and PROVES the Chebotarev-density step between them:

* **3a-i — the Hecke algebra with its realizations**
  (`exists_heckeAlgebra_realizations_of_matchesResidualTraces`, sorry
  node): residual modularity produces the coefficient package
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
  (`exists_hardlyRamified_galoisRep_of_realizations`, sorry node):
  the glued trace system over the local ring `T`, reducing through
  `π` to the traces of the residually IRREDUCIBLE `ρbar`, is the
  trace system of an actual hardly ramified representation on
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
(pillar 3a-i; sorry node — the geometric core of the Carayol cut):
residual modularity of the irreducible hardly ramified `ρbar` at some
level `N₀` produces the Hecke-side coefficient package with its
eigenform realizations. Classical construction: (1) optimize the
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
Soundness of the abstract statement: the section audit (the
hypothesis set is classically unsatisfiable, so the statement is true;
the construction above is its non-vacuous intended discharge).
CIRCULARITY GUARD: must not be proven through `Family.lean` (see the
section docstring). -/
theorem exists_heckeAlgebra_realizations_of_matchesResidualTraces
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
          (real i).toFun (- t q) :=
  sorry

/-- **The Carayol descent** (pillar 3a-ii; sorry node — Carayol,
*Formes modulaires et représentations galoisiennes à valeurs dans un
anneau local complet*, Contemp. Math. 165 (1994), Théorème 2;
equivalently the pseudocharacter theory of Nyssen and Rouquier): a
residually irreducible trace system over the local ring `T` — here
presented through its realizations: the glued membership `hglue`
(every joint trace tuple of the realizations comes from `T`, supplied
by the PROVEN Chebotarev gluing above), joint injectivity (making the
`T`-valued trace function unique and multiplicative-with-determinant,
i.e. a continuous pseudocharacter of dimension 2), and `π`-reduction
to the traces of the IRREDUCIBLE `ρbar` (`hred` at Frobenii off
`S_T`, which extends to all of `Γ ℚ` by the same Chebotarev/continuity
argument into the discrete `k`) — is the trace system of an actual
representation on `Fin 2 → T`: residual absolute irreducibility
(plain irreducibility suffices — hardly ramified representations are
odd, and odd irreducible mod-`ℓ` representations are absolutely
irreducible for odd `ℓ`, the `OddRep` argument) lets Carayol's
Théorème 2 descend the product representation of the realizations
along the jointly injective coordinates to the complete local
Noetherian `T` (module-finite local over `ℤ_ℓ` with finite residue
field `k = T/ker π`). Hardly-ramifiedness descends along the same
trace identification (by Théorème 1, the `λ_i`-base-changes of the
descended representation are conjugate to the realizations):
determinant cyclotomic by joint injectivity, unramifiedness outside
`2ℓ` by the pseudocharacter inflation argument, flatness at `ℓ` by
Raynaud's closure properties of finite flat prolongations (the
`T`-lattice embeds in the product of the realization lattices), and
tameness at 2 with the unramified square-trivial rank-1 quotient by
the same descent (Carayol–Saito). Sound as stated by the section
audit (vacuously; the non-vacuous intended discharge is at the honest
Hecke package of 3a-i). CIRCULARITY GUARD: must not be proven through
`Family.lean` (see the section docstring). -/
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
          - t q :=
  sorry

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

/-- **Patching: `R = 𝕋`** (pillar 3b; sorry node — the Taylor–Wiles
theorem specialized to the hardly ramified deformation problem): a
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
CIRCULARITY GUARD: must not be proven through `Family.lean`. -/
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
          Φ ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :=
  sorry

/-- **Order-valued points of the Hecke-side deformation are modular**
(the geometric half of pillar 3c; sorry node — the Deligne–Serre
eigensystem decomposition / Fontaine–Mazur for points of the Hecke
deformation): a point of a Hecke-side hardly ramified deformation
`(T, ρT, π)` of an irreducible hardly ramified `ρbar` that has been
factored through an ORDER — a `ℤ_ℓ`-algebra surjection `φ` of `T`
onto a local domain `O`, module-finite and FREE over `ℤ_ℓ` (an order
in the `ℓ`-adic field `O ⊗ ℚ_ℓ`), followed by an embedding
`j : O ↪ ℚ̄_ℓ` — carries the Frobenius-trace system of `ρT` to the
coefficient system of a normalized weight-2 eigenform under an
embedding of its Hecke field (sign convention as everywhere in this
file: the `charFrob` linear coefficient is `−a_q`). The proven
finite-algebra half of pillar 3c
(`exists_weightTwoEigenform_of_heckeDeformation_point` below) shows
every `ℚ̄_ℓ`-point of `T` factors this way, with `O = T ⧸ ker lam`.

For the intended instantiation `T = 𝕋_𝔪` (pillar 3a) this is the
modular interpretation of the factors: `𝕋_𝔪 ⊗ ℚ̄_ℓ` is a finite
product of copies of `ℚ̄_ℓ` (`𝕋_𝔪` is reduced and finite free over
`ℤ_ℓ`), the composite `j ∘ φ` is projection to one factor, `O` is the
`ℓ`-adic coefficient order generated by the Hecke eigenvalues of a
normalized eigenform `f` of the optimized level — the full-Hecke
eigenvector property of `f` is the coefficient characterization
`IsWeightTwoEigenform` (Diamond–Shurman Prop. 5.8.5), `ι` is the
induced embedding of `heckeField N f`, and
`j ∘ φ ∘ (tr ∘ ρT ∘ Frob) = ι ∘ a_•(f)` off the exceptional set is
the defining compatibility of Carayol's representation. For an
abstract package the statement is covered by the section audit; the
non-vacuous route is Kisin's Fontaine–Mazur theorem (*The
Fontaine–Mazur conjecture for `GL₂`*, JAMS 22 (2009)): pushing `ρT`
along `φ` gives a rank-2 representation with coefficients in the
order `O` — geometric (hardly ramified: flat at `ℓ`, unramified
outside `2ℓ`), odd (determinant cyclotomic), residually irreducible
(`ker φ ⊆ 𝔪_T` since `T` is local, so the residue field of `O` is
`T ⧸ 𝔪_T ≅ k` and the reduction is `ρbar`, irreducible by `hirr`) —
so Kisin makes `Frac(O) ⊗ ρT` modular of weight 2, and the
eigensystem lands in `j(O)` under the induced Hecke-field embedding.
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
    (φ : T →ₐ[ℤ_[ℓ]] O) (hφ : Function.Surjective φ)
    (j : O →+* AlgebraicClosure ℚ_[ℓ]) (hj : Function.Injective j) :
    ∃ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0GL N) 2)
      (_ : IsWeightTwoEigenform N f)
      (ι : heckeField N f →+* AlgebraicClosure ℚ_[ℓ])
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        j (φ ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)) =
          - ι (heckeCoeff N f q) :=
  sorry

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
* `exists_galoisRep_charFrob_of_weightTwoNewform` — SORRY: the
  Eichler–Shimura attachment at general level, the REAL geometric
  leaf (unlike the level-`∣ 2` attachment statements, which are
  discharged by the proven emptiness of their carriers).
* `charFrob_baseChange` and
  `charFrob_map_coeff_zero_of_isHardlyRamified` and
  `eq_quadratic_of_monic_natDegree_two` — PROVEN bookkeeping that
  upgrades the trace matching `hmatch` to FULL characteristic
  polynomial matching: `charFrob` commutes with coefficient base
  change, is monic quadratic, and has constant Frobenius coefficient
  `q` by `det ρ = χ_cyc` (through the Frobenius value of the
  cyclotomic character, `Chebotarev.lean`'s
  `cyclotomicCharacter_globalFrob`).
* `exists_linearEquiv_of_charFrob_eq` — SORRY: trace rigidity,
  Chebotarev density + Brauer–Nesbitt over `ℚ̄_p`.
* `weightTwoNewform_level_dvd_two_of_isHardlyRamified` — SORRY:
  Carayol's conductor theorem evaluated on the hardly ramified class
  (level of the newform = conductor of its attached representation,
  which divides `2`). -/

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

/-- **The Eichler–Shimura attachment at general level** (sorry node —
THE geometric leaf of the conductor cut, deliberately non-vacuous
unlike the level-`∣ 2` attachment statements discharged by emptiness
above): a weight-2 newform `g` of level `M ≥ 1`, together with an
embedding `κ` of its Hecke field into `ℚ̄_p`, has an attached
2-dimensional continuous `ℚ̄_p`-representation of `Γ ℚ` whose
Frobenius characteristic polynomials away from a finite set of places
are the Hecke polynomials `X² − a_q(g)·X + q` of `g` under `κ`.

Classical construction (Diamond–Shurman ch. 8–9, Theorem 9.5.1 at
weight 2; for weight 2 no étale cohomology beyond the Jacobian is
needed — Deligne's construction is the higher-weight generalization):
`ρ_{g,λ}` acts on the `λ`-adic Tate module of the modular abelian
variety `A_g = J₀(M)/I_g J₀(M)`, `λ` being the place of the Hecke
field `K_g` induced by `κ`; the Eichler–Shimura relation
`Frob_q² − T_q∘Frob_q + q⟨q⟩ = 0` on `J₀(M)` in characteristic
`q ∤ M` (Igusa good reduction) yields the stated characteristic
polynomials with exceptional set `{v : v ∣ Mp}`. SOUNDNESS: the
statement quantifies over inhabitants of `IsWeightTwoNewform`, which
are exactly the classical newforms (the carrier's audit), so the
classical construction witnesses every instance; and it asserts
nothing about `τ` beyond the charpoly matching — precisely the input
shape the rigidity and Carayol leaves consume. (An eigenform-level
statement would ALSO be classically true via the underlying newform,
but the newform hypothesis is what the Carayol leaf needs, so the
attachment is stated at the same carrier.) -/
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
            + Polynomial.C ((q : AlgebraicClosure ℚ_[p])) :=
  sorry

omit [IsDomain R] [IsTopologicalRing R] [IsLocalRing R] in
/-- `charFrob` commutes with coefficient base change (PROVEN glue):
the Frobenius characteristic polynomial of `ρ.baseChange B` is the
image of that of `ρ` — mathlib's `LinearMap.charpoly_baseChange`
transported through the definitional equality
`(ρ.baseChange B) σ = (ρ σ).baseChange B`. This connects the trace
hypothesis of the conductor leaf (stated via `.map`) to statements
about the representation `ρ.baseChange ℚ̄_p` itself, as consumed by
the rigidity leaf. -/
theorem charFrob_baseChange {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra R B] [ContinuousSMul R B]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    (ρ.baseChange B).charFrob v = (ρ.charFrob v).map (algebraMap R B) := by
  show ((ρ.baseChange B).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
    ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).map
      (algebraMap R B)
  rw [show (ρ.baseChange B).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      LinearMap.baseChange B (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) from rfl,
    LinearMap.charpoly_baseChange]

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

/-- **Trace rigidity over `ℚ̄_p`** (sorry node — Chebotarev +
Brauer–Nesbitt, the characteristic-zero analogue of the PROVEN
mod-`ℓ` instance `not_isIrreducible_of_charpoly_eq` in
`Chebotarev.lean`): two continuous 2-dimensional representations of
`Γ ℚ` over `ℚ̄_p` with equal Frobenius characteristic polynomials
away from a finite set of places, the second irreducible, are
equivalent. Intended proof, along the route already assembled for
`Lift.lean`'s `not_isIrreducible_of_charFrob_eq`: the locus
`{γ | charpoly (τ₁ γ) = charpoly (τ₂ γ)}` is closed (the coefficient
functions are polynomial in the matrix entries, hence continuous, and
`ℚ̄_p` is Hausdorff), conjugation-invariant, and contains the global
Frobenius classes off the finite set — dense by the Chebotarev
density node `dense_conjClasses_globalFrob` — hence is everything.
Brauer–Nesbitt in dimension 2 over a characteristic-0 field then
forces equivalence: the semisimplification of `τ₁` has the
characteristic polynomials of the irreducible 2-dimensional `τ₂`, so
it is isomorphic to `τ₂` (equality of characters of semisimple
modules; Curtis–Reiner §30, Serre *Abelian ℓ-adic representations*
I §2.3), and a representation with irreducible full-dimensional
semisimplification is itself irreducible and isomorphic to it. The
conclusion is a bare equivariant linear isomorphism — no continuity
clause, since the consumer (the Carayol leaf) transports only
charpoly-visible and inertia-theoretic data across it. -/
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
        e (τ₁ γ w) = τ₂ γ (e w) :=
  sorry

/-- **Carayol's conductor bound on the hardly ramified class** (sorry
node — the conductor comparison isolated; Carayol, *Sur les
représentations `ℓ`-adiques associées aux formes modulaires de
Hilbert*, Ann. Sci. ÉNS 19 (1986), with Deligne–Rapoport/Langlands for
the weight-2 modular-curve cases and Saito for the general
local–global compatibility; the `p`-part by weight-2 flatness theory):
let `g` be a weight-2 newform of level `M` (the minimal-level
carrier), `τ` a representation matching its Hecke polynomials away
from a finite set (the attachment shape produced by
`exists_galoisRep_charFrob_of_weightTwoNewform`), and suppose `τ` is
equivalent to the base change to `ℚ̄_p` of a HARDLY RAMIFIED integral
representation `ρ`. Then `M ∣ 2`.

Classical proof: by rigidity (Chebotarev + Brauer–Nesbitt — here part
of the classical argument for this leaf, not a Lean input) `τ` is
isomorphic to the base change of the attached representation
`ρ_{g,λ}` of the newform `g`, so `ρ_{g,λ} ⊗ ℚ̄_p ≅ ρ ⊗ ℚ̄_p`;
Carayol's theorem identifies the prime-to-`p` Artin conductor of
`ρ_{g,λ}` with the prime-to-`p` part of `M`, and local–global
compatibility at `p` handles the rest:

* at primes `q ∉ {2, p}`: `ρ` is unramified (`isUnramified`), so the
  conductor exponent of `ρ_{g,λ}` at `q` is `0`, i.e. `q ∤ M`;
* at `p`: `ρ` is flat (`isFlat`), so `ρ_{g,λ}` is crystalline with
  Hodge–Tate weights `{0, 1}` at `p`, and a weight-2 newform whose
  `λ ∣ p` representation is crystalline at `p` has `p ∤ M` (for
  `p ∥ M` the local representation is an unramified twist of
  Steinberg — semistable non-crystalline (Saito); for `p² ∣ M` not
  even semistable);
* at `2`: by `isTameAtTwo` the local representation at `2` is an
  extension of an unramified character `δ` by `χ_cyc·δ⁻¹` — also
  unramified at `2`, since `det = χ_cyc` is unramified at `2` for odd
  `p` — so inertia at `2` acts tamely and fixes a line: the conductor
  exponent at `2` is `dim V − dim V^{I₂} ≤ 1` with zero Swan
  conductor, i.e. `4 ∤ M`.

Hence `M ∣ 2`. SOUNDNESS AUDIT (2026-07-24): the leaf is stated in
the exact shape of the literature theorems just cited, and each cited
step is a true classical statement about the classical objects that
inhabit the hypotheses. As the previous audit of the conductor leaf
predicted, the hypothesis-level contradiction of the collapsed
endgame (no irreducible hardly ramified representation is modular)
now concentrates HERE: classically no configuration satisfies all
hypotheses at once — for irreducible `ρ` because the conclusion feeds
the proven emptiness downstream, for reducible `ρ` because a cuspidal
newform's eigensystem is never the Eisenstein system `1 ⊕ χ_cyc`
(so no `τ` can both match `g` and be equivalent to `ρ ⊗ ℚ̄_p`). That
does not make the leaf a restatement of the collapse: its intended
proof is the direct conductor computation above, attackable from
Carayol/Saito without reference to any contradiction. -/
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
    M ∣ 2 :=
  sorry

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
3. *Rigidity* (`exists_linearEquiv_of_charFrob_eq`, sorry leaf):
   `τ ≅ ρ ⊗ ℚ̄_p` — their Frobenius characteristic polynomials agree
   away from a finite set, because the trace matching `hmatch`
   upgrades to full charpoly matching through the determinant
   normalization (`charFrob_map_coeff_zero_of_isHardlyRamified`,
   PROVEN from `det = χ_cyc`) and the monic-quadratic shape, and
   `ρ ⊗ ℚ̄_p` is irreducible (`hirr`).
4. *Carayol's conductor bound*
   (`weightTwoNewform_level_dvd_two_of_isHardlyRamified`, sorry
   leaf): the level of a newform whose attached representation is
   (through the rigidity equivalence) the base change of a hardly
   ramified representation divides `2` — Ribet's mod-`p` level
   lowering (Invent. Math. 100 (1990)) is the residual counterpart
   used when this content is reached through the Khare–Wintenberger
   induction instead.
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
that. Of the three remaining sorried leaves, the attachment and
rigidity leaves are non-vacuously satisfiable literature statements,
and the hypothesis-level contradiction now concentrates in the
Carayol leaf (see its docstring), stated nevertheless in the exact
shape of Carayol's conductor theorem, attackable from its citations
without reference to the collapse. -/
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
