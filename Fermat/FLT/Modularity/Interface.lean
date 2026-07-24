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
   `IsWeightTwoEigenform`.
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

DECOMPOSITION PLAN item 2, executed (2026-07-24) up to one sorried
leaf. `heckeField_finiteDimensional` below is Diamond–Shurman
Theorem 6.5.1: the coefficients of a normalized weight-2 eigenform
generate a number field. The classical proof pivots on ONE finite
object: the Hecke operators act by integer matrices on the homology
lattice `H₁(X₀(N), ℤ)` (rank `2·dim S₂(Γ₀(N))`), and the eigenform's
coefficient system is the eigenvalue system of that action on a common
eigenvector (the `f`-isotypic period vector). On this pin none of the
ingredients exist — no Hecke operators on `CuspForm`, no modular
curve, no homology, and not even finite-dimensionality of
`CuspForm (Gamma0GL N) 2` (audited 2026-07-24: only the level-1 space
carries a `FiniteDimensional` instance, from the level-1 dimension
formula; `~/cs/FLT`'s Hecke material is quaternionic-automorphic, not
connected to the pin's analytic cusp forms) — so exactly that finite
object is isolated as the sorried leaf
`exists_heckeMatrix_eigenvector`. Everything else is proven:

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

/-- **Integral Hecke structure of an eigenform** (sorry node;
Diamond–Shurman §6.5, the geometric input to Theorem 6.5.1): for a
normalized weight-2 level-`N` eigenform `f` there are a dimension `n`,
a family of RATIONAL `n × n` matrices `T q` (only the values at prime
indices matter), and a common nonzero complex eigenvector `v` with
`T q ⬝ v = a_q(f) • v` for every prime `q`. Classical instantiation:
`n = 2g` with `g = dim S₂(Γ₀(N))` the genus of `X₀(N)`, `T q` the
matrix of the Hecke operator `T_q` (resp. `U_q` for `q ∣ N`) acting on
`H₁(X₀(N), ℚ)` in an integral basis — the Hecke correspondences are
defined over `ℤ` on homology (Diamond–Shurman Proposition 6.5.1 proves
exactly this lattice stability) — and `v` the period vector of `f`:
the coordinates of the `f`-component under the Eichler–Shimura
isomorphism `H₁(X₀(N), ℤ) ⊗ ℂ ≅ S₂ ⊕ S̄₂`, on which `T_q` acts by
`a_q(f)` (Prop 5.8.5 makes the coefficient relations of
`IsWeightTwoEigenform` equivalent to full-Hecke eigenvector-ness);
`v ≠ 0` because `f ≠ 0`, having `a₁ = 1`. An alternative analytic
route avoiding homology: `S₂(Γ₀(N))` is finite-dimensional with a
basis of integral `q`-expansions stable under the (yet to be
constructed, DECOMPOSITION PLAN item 1) Hecke action, and `v` the
coordinate vector of `f` itself. Neither Hecke operators, nor
`X₀(N)`, nor finite-dimensionality of `CuspForm (Gamma0GL N) 2`
exists on this pin (audited 2026-07-24), which makes this the
irreducible geometric leaf of the Hecke-field-finiteness node. -/
theorem exists_heckeMatrix_eigenvector {N : ℕ} (hN : 0 < N)
    {f : CuspForm (Gamma0GL N) 2} (hf : IsWeightTwoEigenform N f) :
    ∃ (n : ℕ) (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℂ),
      v ≠ 0 ∧ ∀ q : ℕ, q.Prime →
        (T q).map (algebraMap ℚ ℂ) *ᵥ v = qCoeff N f q • v :=
  sorry

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
2; sorry node — the Khare–Wintenberger content): an IRREDUCIBLE hardly
ramified mod-`ℓ` representation with `ℓ ≥ 5` arises from a normalized
weight-2 eigenform of some level `N ≥ 1`. This is the
level-and-weight-free ("weak") form of Serre's modularity conjecture
in the hardly ramified case (Serre, Duke 1987 — the refined
conductor-2 form is recovered downstream by the level-optimization
pillar, not consumed here), a theorem of Khare–Wintenberger (*Serre's
modularity conjecture (I), (II)*, Invent. Math. 178 (2009)) via
minimal lifting to strictly compatible families and induction on the
residue characteristic; the FLT blueprint (ch. 4) reaches the same
automorphy through potential modularity (Moret–Bailly plus dihedral
residual modularity from converse theorems plus modularity lifting
over totally real fields). Plain irreducibility suffices to state it:
hardly ramified representations are odd (`det = χ_cyc` and
`χ_cyc(c) = −1`), and an odd irreducible 2-dimensional representation
over a finite field of odd characteristic is absolutely irreducible
(the `OddRep` argument consumed by
`IsHardlyRamified.mod_three_reducible`). The `ℓ ≥ 5` hypothesis is
genuine slack for the Khare–Wintenberger induction, whose base cases
are `ℓ = 2, 3` — the induction bottoms out in representations with
solvable/dihedral image where automorphy is classical
(Langlands–Tunnell at 3, Tate's `ℓ = 2` argument); here the `ℓ = 3`
case is instead discharged by contradiction in the assembly below, so
this leaf never needs those base cases in their modular form — its
eventual proof may equally follow the blueprint's potential-modularity
chain, which needs no residue-characteristic induction at all.
CIRCULARITY GUARD (unchanged from the assembly): must not be proven
through `Family.lean`'s compatible-family machinery, which consumes
the assemblies below. -/
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
  sorry

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

/-- **The Hecke-side deformation** (pillar 3a; sorry node — Carayol's
Hecke-algebra-valued Galois representation): an irreducible hardly
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
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 :=
  sorry

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

/-- **Modular points of the Hecke-side deformation** (pillar 3c; sorry
node — the Deligne–Serre eigensystem decomposition): every
`ℚ̄_ℓ`-valued point `lam` of a Hecke-side hardly ramified deformation
`(T, ρT, π)` of an irreducible hardly ramified `ρbar` carries the
Frobenius-trace system of `ρT` to the coefficient system of a
normalized weight-2 eigenform under an embedding of its Hecke field
(sign convention as everywhere in this file: the `charFrob` linear
coefficient is `−a_q`). For the intended instantiation `T = 𝕋_𝔪`
(pillar 3a) this is finite commutative algebra plus the modular
interpretation: `𝕋_𝔪 ⊗ ℚ̄_ℓ` is a finite product of copies of `ℚ̄_ℓ`
(`𝕋_𝔪` is reduced and finite free over `ℤ_ℓ`), so `lam` is projection
to one factor, i.e. the eigensystem of a normalized eigenform `f` of
the optimized level — its full-Hecke eigenvector property is the
coefficient characterization `IsWeightTwoEigenform` (Diamond–Shurman
Prop. 5.8.5), `ι` is the induced embedding of `heckeField N f`, and
`lam ∘ (tr ∘ ρT ∘ Frob) = ι ∘ a_•(f)` off the exceptional set is the
defining compatibility of Carayol's representation. For an abstract
package the statement is covered by the section audit; the
non-vacuous route is Kisin's Fontaine–Mazur theorem (*The
Fontaine–Mazur conjecture for `GL₂`*, JAMS 22 (2009)): `lam ∘ ρT` is
a geometric, odd, residually irreducible rank-2 representation of
`Γ ℚ`. CIRCULARITY GUARD: must not be proven through `Family.lean`. -/
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
          - ι (heckeCoeff N f q) :=
  sorry

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

/-- **The residually reducible branch at `p ≥ 5`** (pillar 4 leaf;
sorry node — the Skinner–Wiles shadow): a hardly ramified `p`-adic
representation, `p ≥ 5`, that is irreducible over `ℚ̄_p` but whose
residual representation is REDUCIBLE is still modular, in the same
trace sense as pillar 3. Classically the residual semisimplification
is `1 ⊕ χ̄_cyc` — its two characters are unramified outside `2p` with
cyclotomic product, tame at `2`, flat-constrained at `p`, so
Minkowski-style arguments pin them (compare the proven character
analysis `char_add_char_eq_one_add_cyclotomicCharacter` in
`Family.lean`, the same classification one level up) — which is
exactly the Eisenstein-congruence situation of Skinner–Wiles,
*Residually reducible representations and modular forms*, Publ. Math.
IHÉS 89 (1999); the de Rham/Fontaine–Mazur formulation matching this
statement is Pan, *The Fontaine–Mazur conjecture in the residually
reducible case*, JAMS 35 (2022). The `p = 3` instance is NOT here: it
is discharged (AUDIT 2026-07-24) by contradiction from the 3-adic
classification — see the pillar-4 assembly below — so this leaf
carries exactly the `p ≥ 5` Skinner–Wiles/Pan content (`hp5` is
genuinely available to any future decomposition, e.g. for the
Eisenstein-ideal congruence arguments, which need `p ∤ 6`
corner-case-free room). -/
theorem exists_weightTwoEigenform_trace_eq_of_residually_reducible_of_five_le
    (hp5 : 5 ≤ p)
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
          - ι (heckeCoeff N f q) :=
  sorry

/-- **Level lowering to conductor level `M ∣ 2`** (the sorried heart of
pillar 5 — the Carayol-conductor/Ribet content, isolated 2026-07-24):
if the Frobenius traces of an irreducible hardly ramified `p`-adic
representation `ρ` arise (away from a finite set, in the `-a_q` trace
convention) from a weight-2 normalized eigenform `f` of some level
`N ≥ 1`, then they arise, in the same sense, from a weight-2 normalized
eigenform of level `M` dividing `2`. Classical route, following the
citations of the pillar docstring below:

1. *Newform descent* (Diamond–Shurman Prop. 5.8.4, via Strong
   Multiplicity One): behind the full-Hecke eigenform `f` (coefficient
   characterization, Prop. 5.8.5) lies a newform `g` of level
   `M₀ ∣ N` with the same eigenvalues at every prime `q ∤ N`.
2. *Attachment and rigidity*: the `λ`-adic Galois representation
   `ρ_{g,λ}` attached to `g` at a place `λ ∣ p` of its Hecke field
   (Eichler–Shimura/Deligne) has the same Frobenius traces as `ρ` away
   from a finite set (by the matching hypothesis), and both are
   irreducible, so `ρ ⊗ ℚ̄_p ≅ ρ_{g,λ} ⊗ ℚ̄_p` (Chebotarev density +
   Brauer–Nesbitt).
3. *Conductor bound*: the prime-to-`p` Artin conductor of a hardly
   ramified representation divides `2` — unramified outside `{2, p}`,
   and at `2` the ramification is tame with unramified rank-1 quotient,
   so the conductor exponent at `2` is at most `1`; flatness at `p` and
   `det = χ_cyc` put the pair (conductor, weight) in Serre's `(2, 2)`
   class (Serre, Duke 1987, §4.1).
4. *Carayol's theorem* (Ann. Sci. ÉNS 19 (1986); Livné for the
   residual statement; "level of the newform = conductor of its
   `λ`-adic representation"): hence `M₀ ∣ 2` — Ribet's mod-`p` level
   lowering (Invent. Math. 100 (1990)) is the residual counterpart
   used when this content is reached through the Khare–Wintenberger
   induction instead.
5. The eigensystem of `g` embeds into `ℚ̄_p` compatibly with `ι` (both
   generate the same coefficients at good primes), giving the stated
   `κ` with exceptional set `S₂ = S₁ ∪ {v : v ∣ 2Np}`.

SOUNDNESS/DEPTH AUDIT (2026-07-24): both level-`M ∣ 2` spaces are
proven empty in this file (`weightTwoEigenform_level_one_false`,
`weightTwoEigenform_level_two_false`), so this leaf's conclusion is
unsatisfiable and the leaf equivalently asserts that its hypotheses
are contradictory — that no irreducible hardly ramified `p`-adic
representation is modular of ANY level. That is not an artifact: it is
exactly where the classical proof's final contradiction (Wiles) lives,
and steps 1–4 above ARE its literature derivation. Every honest
intermediate past this point (existence of an eigenform of level
`∣ 2`) is unsatisfiable-conclusion-shaped, so no decomposition can
push the contradiction out of this boundary leaf; a genuinely finer
decomposition must instead build the step 1–4 vocabulary the pin
lacks — newforms/strong multiplicity one, attached `λ`-adic
representations at general level `N` (Eichler–Shimura/Deligne, a REAL
non-vacuous attachment sorry, unlike the level-2 one discharged by
emptiness), trace rigidity (Chebotarev + Brauer–Nesbitt for
`GaloisRep`), and the Artin conductor — and prove `M₀ ∣ 2` through
them. That vocabulary-building is the designated next dispatch for
this node. -/
theorem exists_eigenform_level_dvd_two_of_trace_eq
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
        - ι (heckeCoeff N f q)) :
    ∃ (M : ℕ) (_ : M ∣ 2) (g : CuspForm (Gamma0GL M) 2)
      (_ : IsWeightTwoEigenform M g)
      (κ : heckeField M g →+* AlgebraicClosure ℚ_[p])
      (S₂ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      ∀ (q : ℕ) (hq : q.Prime), hq.toHeightOneSpectrumRingOfIntegersRat ∉ S₂ →
        ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
            (algebraMap R (AlgebraicClosure ℚ_[p]))).coeff 1 =
          - κ (heckeCoeff M g q) :=
  sorry

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
