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
   blueprint's hardly-ramified formulation): decompose along the
   blueprint — residual modularity (Langlands–Tunnell at 3 via the
   `ModThree` classification), modularity lifting, level lowering.
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
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Topology.Algebra.IntermediateField

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

end LevelTwoEmptiness

/-- **Hecke field finiteness** (sorry node; Diamond–Shurman §6.5,
Theorem 6.5.1): the coefficients of a normalized weight-2 eigenform of
level `N ≥ 1` generate a finite extension of `ℚ` inside `ℂ`. The
classical proof: the Hecke algebra acts on the integral homology
lattice `H₁(X₀(N), ℤ)` (rank `2·dim S₂`), so each `aₙ` — an eigenvalue
of an integral matrix — is an algebraic integer of bounded degree, and
the whole system lies in a single number field (the eigensystem is a
`ℚ̄`-point of the finite `ℚ`-algebra `𝕋_ℚ`). The level positivity
hypothesis keeps the statement inside the classical theory (`Γ₀(0)` is
not a finite-index subgroup and its "cusp forms" are not the classical
space); the consumers only ever instantiate `N ≥ 1`. -/
theorem heckeField_finiteDimensional {N : ℕ} (hN : 0 < N)
    {f : CuspForm (Gamma0GL N) 2} (hf : IsWeightTwoEigenform N f) :
    FiniteDimensional ℚ (heckeField N f) :=
  sorry

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

/-- **Modularity of the trace system** (sorry node; the modularity
input of the trace-field atom
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
          - ι (heckeCoeff N f q) :=
  sorry

/-- **Modularity at level 2** (sorry node; the modularity input of the
two realization atoms `exists_hardlyRamified_ringOfIntegers_realizations`
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
      IsWeightTwoEigenform 2 f ∧ MatchesEigensystem 2 f S' Pv :=
  sorry

end GaloisRepresentation.Modularity
