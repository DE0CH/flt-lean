/-
Chebotarev.lean — own work for the Fermat project (not vendored from the
FLT project).

The decomposition of the Chebotarev–Brauer–Nesbitt node
(`not_isIrreducible_of_charFrob_eq`, `HardlyRamified/Lift.lean`) begins
here. This file provides:

* `GaloisRepresentation.globalFrob v : Γ K` — the global (arithmetic)
  Frobenius element at a finite place `v`: the image of the local
  arithmetic Frobenius `Frobᵥ ∈ Γ Kᵥ` under the map `Γ Kᵥ → Γ K` induced
  by `K → Kᵥ` (and the arbitrary-but-fixed embedding of algebraic closures
  built into `Field.absoluteGaloisGroup.map`). This is the group element
  at which `GaloisRep.charFrob` evaluates: `ρ.charFrob v =
  (ρ (globalFrob v)).charpoly` holds by definition
  (`charFrob_eq_charpoly_globalFrob`).

* **Chebotarev density** (`dense_conjClasses_globalFrob`): for any finite
  set `S` of finite places of `ℚ`, the union of the conjugacy classes of
  the global Frobenius elements at places outside `S` is dense in `Γ ℚ`.
  This is the topological form of the Chebotarev density theorem needed
  here (density of Frobenii); the full measure-theoretic statement is
  strictly stronger and not required. DERIVED (through
  `exists_frobenius_conj_mem_coset` and
  `exists_globalFrob_restrictNormalHom_conj`, both proven, and the
  PROVEN local–global bridge
  `exists_isArithFrobAt_restrictNormalHom_globalFrob`) from
  `infinite_setOf_isArithFrobAt`, the classical ideal-theoretic
  Chebotarev existence statement for a finite Galois extension of
  number fields — itself PROVEN by the classical Deuring reduction
  to the cyclic case over the fixed field of `⟨τ⟩`, using the PROVEN
  ramification-finiteness theorem `finite_setOf_exists_inertia_ne_bot`
  (via the different ideal). The cyclic case
  `infinite_setOf_isArithFrobAt_zpowers` is in turn PROVEN by
  Chebotarev's field-crossing reduction to the cyclotomic case (the
  auxiliary-prime input `exists_prime_dvd_sub_one_and_irreducible_cyclotomic`
  is PROVEN purely algebraically, by a subfield-pigeonhole against
  pairwise linearly disjoint prime cyclotomic fields — no ramification
  theory). The infinitude statement
  `infinite_setOf_natCard_quotient_prime_and_map_zeta_eq_pow` is PROVEN
  from the Dirichlet-density divergence statement
  `exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow`
  (unboundedness as `s → 1⁺` of the Dirichlet sum over the degree-one
  primes of a number field in a prescribed cyclotomic congruence
  class — Dirichlet's theorem over an arbitrary number-field base),
  itself PROVEN by Deuring's-route bookkeeping from
  `exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne` (the
  Dedekind-zeta half, a remaining sorry leaf: the full degree-one prime
  sum diverges as `s → 1⁺`) and
  `tsum_rpow_neg_natCard_quotient_prime_and_ne_le_mul_tsum_add` (the
  `L`-function half: the congruence class of `τ` carries the full sum
  up to `ℓ ×` and a bounded error) — the latter now itself PROVEN by
  Frobenius bookkeeping (`exists_algEquiv_map_zeta_eq_pow_natCard`
  covers the degree-one primes by the `≤ ℓ` congruence classes) from
  the pairwise-comparison statement
  `tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow_le_tsum_add`
  (any two congruence classes carry the same sum up to a uniformly
  bounded additive error), in turn PROVEN by Dirichlet-character
  orthogonality (`DirichletCharacter.sum_char_inv_mul_char_eq`, with
  the characters trivial on the image of `Gal(E/F)` cancelling exactly
  in the difference of two classes) from
  `tsum_rpow_neg_natCard_quotient_prime_and_ne_ne_top` (the degree-one
  prime sum converges for each fixed `s > 1` — itself PROVEN by
  injecting the degree-one places into the nonzero ideals, from the
  full-ideal-sum leaf `tsum_rpow_neg_absNorm_ne_top` of the
  Dedekind-zeta half) and
  `exists_forall_norm_tsum_dirichletCharacter_mul_rpow_neg_le` (the
  character sum `S_χ(s)` of a Dirichlet character mod `ℓ` nontrivial
  on the image of `Gal(E/F)` is bounded uniformly in `s > 1` — the
  minimal `L(1, χ) ≠ 0` statement) — itself now PROVEN by an
  exp/log-plus-mean-value assembly from
  `exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries`
  (the Euler product for the `χ`-twisted Dedekind zeta function in
  exponential form — itself PROVEN, through the proven norm-fibration
  `tsum_dirichletCharacter_mul_cpow_neg_absNorm_eq_LSeries` and
  `tprod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum`, the
  ideal-theoretic Euler product, now also PROVEN — pure unique
  factorization, mirroring mathlib's `ℕ`-indexed machinery on the
  ideal monoid; see its docstring) and
  `exists_forall_le_norm_LSeries_and_norm_deriv_LSeries_le` (good
  behaviour of the twisted ideal `L`-series on `(1, 2]` — itself
  PROVEN, with the away-from-`1` positivity supplied by the Euler
  identity, from
  `exists_forall_norm_LSeries_le_and_norm_deriv_le` (uniform bounds
  for `L` and `L'`: the analytic-continuation half — now itself
  DERIVED, through the PROVEN transfer lemmas
  `norm_LSeries_le_mul_div_of_forall_norm_sum_le` (integral
  representation), `exists_forall_norm_sum_log_mul_le_rpow` (Abel
  summation) and `sum_card_absNorm_isBigO` (linear coefficient
  growth), from the single sorried counting core
  `exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow`,
  the power-saving Weber–Landau Hecke count) and
  `exists_forall_le_norm_LSeries_near_one` (`L` bounded away from `0`
  just right of `1`: the `L(1,χ) ≠ 0` half — now itself DERIVED,
  through the PROVEN dominated-convergence continuation
  `tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le` and
  `lSeriesSummable_dirichletCharacter_mul_card`, from the same
  counting core plus the sorried arithmetic core
  `integral_sum_dirichletCharacter_mul_card_cpow_neg_two_ne_zero`,
  the nonvanishing of the continued value at `1` by the classical
  zeta-factorization argument)); the L-function half thus rests on
  exactly TWO deep sorried cores; see their docstrings for the
  intended proofs and the exact state of the mathlib pin.

The remaining pieces of the decomposition (Brauer–Nesbitt for
2-dimensional mod-`ℓ` representations, the mod-`ℓ` cyclotomic character as
a continuous character, and its value `q` at `globalFrob q`) follow in
later layers; see `PROGRESS.md`.
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- Kolchin (2-dim) and the commuting-split common-eigenvector lemma,
-- used in the proof of `not_isIrreducible_of_charpoly_eq`.
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.Frobenius
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Instances.ZMod
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

namespace GaloisRepresentation

open IsDedekindDomain
open scoped NumberField
open scoped ENNReal

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)

/-- The global arithmetic Frobenius element at a finite place `v` of a
number field `K`: the image in `Γ K` of the local arithmetic Frobenius
`Frobᵥ ∈ Γ Kᵥ` under the map induced by `K → Kᵥ` (with the same
arbitrary-but-fixed embedding of algebraic closures that
`GaloisRep.toLocal` uses, so that `charFrob` literally evaluates at this
element). Well-defined only up to conjugacy and up to inertia at `v`;
every statement below is conjugation-invariant and concerns places where
the representations at hand are unramified. -/
noncomputable def globalFrob (v : Ω K) : Γ K :=
  Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))
    (Field.AbsoluteGaloisGroup.adicArithFrob v)

/-- `charFrob` is the characteristic polynomial of the representation
evaluated at the global Frobenius element — by definition. -/
lemma GaloisRep.charFrob_eq_charpoly_globalFrob {A : Type*} [CommRing A]
    [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (v : Ω K) :
    ρ.charFrob v = (ρ (globalFrob v)).charpoly :=
  rfl

/-!
## Decomposition of the finite Galois-group Chebotarev node

The finite Galois-group form `exists_globalFrob_restrictNormalHom_conj`
is ASSEMBLED below from two sorried arithmetic leaves, both stated in
mathlib's finite-level Frobenius vocabulary
(`IsArithFrobAt`, `Mathlib.RingTheory.Frobenius`):

* `infinite_setOf_isArithFrobAt` — the arithmetic core: the classical
  Chebotarev existence statement for the finite Galois extension `L/K`
  in its finite, ideal-theoretic form (no completions): for every
  `τ ∈ Gal(L/K)` there are infinitely many places `v` of `K` carrying a
  prime `Q` of `𝓞 L` over `v`, with trivial inertia, at which `τ` is an
  arithmetic Frobenius.

* `finite_setOf_not_isArithFrobAt_restrictNormalHom_globalFrob` — the
  local–global bridge: for all but finitely many `v`, the restriction to
  `L` of the completion-theoretic `globalFrob v` is an arithmetic
  Frobenius at some prime of `𝓞 L` over `v`.

The assembly is pure Galois/ideal theory and is PROVEN: pick `v` in the
first (infinite) set avoiding both `S` and the second (finite bad) set;
the two Frobenius data at `v` live at primes `Q₁`, `Q₂` over `v`;
`Gal(L/K)` acts transitively on the primes over `v`
(`Algebra.IsInvariant.exists_smul_of_under_eq`), so conjugating by some
`g` moves `Q₂` to `Q₁` and makes `g · (Frob_v|_L) · g⁻¹` a Frobenius at
`Q₁` (`IsArithFrobAt.conj`); two Frobenii at the same prime differ by
inertia (`IsArithFrobAt.mul_inv_mem_inertia`), which is trivial at `Q₁`.
-/

/-- A finite-dimensional intermediate field of `K̄/K` is a number field. -/
instance (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    NumberField L :=
  NumberField.of_module_finite K L

/-- A normal finite-dimensional subextension of `K̄/K` is Galois:
separability is automatic in characteristic zero. -/
instance (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] : IsGalois K L :=
  ⟨⟩

/-- The Galois action on `𝓞 L` commutes with the `𝓞 K`-scalar action:
`e ∈ Gal(L/K)` fixes `K` pointwise, hence fixes the image of `𝓞 K`.
(Stated here against the ambient project action instance on `𝓞 L` —
the vendored `MulSemiringAction G (𝓞 K)` instance in
`Fermat.FLT.Deformations.Lemmas` shadows mathlib's, so mathlib's
`IsGaloisGroup`-derived instance does not apply.) -/
instance (L : IntermediateField K (AlgebraicClosure K)) :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm e r x := by
    refine NumberField.RingOfIntegers.ext ?_
    have hcoe : ∀ y : 𝓞 L, ((e • y : 𝓞 L) : L) = e (y : L) := fun _ => rfl
    have hsm : ∀ y : 𝓞 L, ((r • y : 𝓞 L) : L) =
        algebraMap K L (algebraMap (𝓞 K) K r) * (y : L) := by
      intro y
      rw [Algebra.smul_def]
      rfl
    rw [hcoe, hsm x, hsm (e • x), map_mul, AlgEquiv.commutes, hcoe]

/-- The fixed points of the Galois action on `𝓞 L` are exactly the image
of `𝓞 K`: a fixed integer is a fixed field element (hence in `K` by
Galois theory) that is integral over `ℤ`. -/
instance (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] : Algebra.IsInvariant (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) where
  isInvariant x hx := by
    have hfixL : ∀ e : L ≃ₐ[K] L, e • (x : L) = (x : L) := fun e =>
      congrArg (algebraMap (𝓞 L) L) (hx e)
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := K)
      (G := L ≃ₐ[K] L) (x : L) hfixL
    have hyint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (B := L) (algebraMap K L).injective, hy]
      exact x.2
    exact ⟨⟨y, hyint⟩, NumberField.RingOfIntegers.ext hy⟩

/-- The Galois action on `𝓞 E` commutes with the `𝓞 F`-scalar action, for
an arbitrary extension `E/F` of number fields — the general form of the
intermediate-field instance above, needed to state the cyclic Chebotarev
core over the fixed field of `⟨τ⟩` (which is an abstract number field,
not an intermediate field of `K̄/K`). -/
instance {F E : Type*} [Field F] [Field E] [Algebra F E] [NumberField E] :
    SMulCommClass (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) where
  smul_comm e r x := by
    refine NumberField.RingOfIntegers.ext ?_
    have hcoe : ∀ y : 𝓞 E, ((e • y : 𝓞 E) : E) = e (y : E) := fun _ => rfl
    have hsm : ∀ y : 𝓞 E, ((r • y : 𝓞 E) : E) =
        algebraMap F E (algebraMap (𝓞 F) F r) * (y : E) := by
      intro y
      show algebraMap (𝓞 E) E (r • y) = _
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
        IsScalarTower.algebraMap_apply (𝓞 F) F E]
    rw [hcoe, hsm x, hsm (e • x), map_mul, AlgEquiv.commutes, hcoe]

/-- **Residue fields of degree-one primes do not grow**: if a prime `P` of
`B` has residue field of prime cardinality `p`, then the residue field of
the prime `P ∩ A` below it also has cardinality `p`. (The residue field of
`P ∩ A` embeds into that of `P`, and a subgroup of a group of prime order
`p` that is not trivial has order `p`.) Used to transfer the arithmetic
Frobenius property `σ x ≡ x ^ #(residue field) (mod P)` from an
intermediate base field down to the bottom field at degree-one primes. -/
lemma natCard_quotient_under_eq_of_natCard_prime {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]
    (hp : (Nat.card (B ⧸ P)).Prime) :
    Nat.card (A ⧸ P.under A) = Nat.card (B ⧸ P) := by
  haveI hBfin : Finite (B ⧸ P) := Nat.finite_of_card_ne_zero hp.ne_zero
  set g : (A ⧸ P.under A) →+* (B ⧸ P) :=
    Ideal.quotientMap P (algebraMap A B) le_rfl
  have hginj : Function.Injective g := Ideal.quotientMap_injective' le_rfl
  haveI : Finite (A ⧸ P.under A) := Finite.of_injective g hginj
  have hdvd : Nat.card (A ⧸ P.under A) ∣ Nat.card (B ⧸ P) :=
    AddSubgroup.card_dvd_of_injective g.toAddMonoidHom hginj
  have hone : Nat.card (A ⧸ P.under A) ≠ 1 := by
    haveI : (P.under A).IsPrime := Ideal.IsPrime.under A P
    haveI : Nontrivial (A ⧸ P.under A) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
    have h2 : 1 < Nat.card (A ⧸ P.under A) := Finite.one_lt_card
    omega
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd h hone
  · exact h

/-- A Galois extension whose Galois group is generated by a single element
*as an abstract group* (not merely topologically) is finite-dimensional.
The Galois group of a Galois extension is a compact Hausdorff group in the
Krull topology; were the extension infinite, the group would be infinite,
yet countable — as `⟨τ⟩` is — so by Baire's theorem some singleton would
have nonempty interior, making the topology discrete (by homogeneity) and
the group finite (compact + discrete), a contradiction. Mechanically we
skip the contraposition: Baire gives an isolated point outright, hence
`{1}` is open, hence the fixing subgroup of `⊤` is open, which
characterizes finite subextensions (`InfiniteGalois.isOpen_iff_finite`). -/
theorem finiteDimensional_of_forall_mem_zpowers
    {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    (τ : E ≃ₐ[F] E) (hgen : ∀ σ : E ≃ₐ[F] E, σ ∈ Subgroup.zpowers τ) :
    FiniteDimensional F E := by
  haveI : Countable (E ≃ₐ[F] E) := by
    have hsurj : Function.Surjective (fun k : ℤ => τ ^ k) := fun σ => by
      obtain ⟨k, hk⟩ := hgen σ
      exact ⟨k, hk⟩
    exact hsurj.countable
  -- Baire: some singleton has nonempty interior
  obtain ⟨σ, hσ⟩ : ∃ σ : E ≃ₐ[F] E, (interior {σ}).Nonempty := by
    refine nonempty_interior_of_iUnion_of_closed (fun σ => isClosed_singleton) ?_
    exact Set.iUnion_of_singleton _
  have hσopen : IsOpen ({σ} : Set (E ≃ₐ[F] E)) := by
    have hint : interior ({σ} : Set (E ≃ₐ[F] E)) = {σ} :=
      (Set.Nonempty.subset_singleton_iff hσ).mp interior_subset
    exact hint ▸ isOpen_interior
  -- translate the isolated point to the identity
  have hone : IsOpen ({1} : Set (E ≃ₐ[F] E)) := by
    have himg : (Homeomorph.mulLeft σ⁻¹) '' {σ} = {1} := by
      simp [Homeomorph.mulLeft]
    exact himg ▸ (Homeomorph.mulLeft σ⁻¹).isOpen_image.mpr hσopen
  -- the fixing subgroup of `⊤` is `⊥`, whose carrier is `{1}`, so it is open
  haveI : FiniteDimensional F (⊤ : IntermediateField F E) := by
    rw [← InfiniteGalois.isOpen_iff_finite, IntermediateField.fixingSubgroup_top]
    show IsOpen (((⊥ : Subgroup (E ≃ₐ[F] E)) : Set (E ≃ₐ[F] E)))
    rw [Subgroup.coe_bot]
    exact hone
  exact (IntermediateField.topEquiv (F := F) (E := E)).toLinearEquiv.finiteDimensional

open Polynomial in
/-- Adjoining the `ℓ`-th roots of unity to a finite Galois extension keeps
it normal over the base field: if `E/F` is finite Galois and `Ω/E` is an
`ℓ`-th cyclotomic extension, then `Ω/F` is normal — `Ω` is the splitting
field over `F` of `(minpoly F α) * (X ^ ℓ - 1)`, where `α` is a primitive
element of `E/F`. -/
theorem Normal.of_isGalois_isCyclotomicExtension
    {F E N : Type*} [Field F] [Field E] [Field N] [Algebra F E] [Algebra E N]
    [Algebra F N] [IsScalarTower F E N] [IsGalois F E] [FiniteDimensional F E]
    (ℓ : ℕ) [NeZero ℓ] [IsCyclotomicExtension {ℓ} E N] :
    Normal F N := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hXne : (X ^ ℓ - 1 : F[X]) ≠ 0 := by
    have h1 : ((1 : F[X]) = C 1) := by simp
    rw [h1]
    exact X_pow_sub_C_ne_zero (NeZero.pos ℓ) 1
  have hqne : minpoly F α * (X ^ ℓ - 1) ≠ 0 :=
    mul_ne_zero (minpoly.ne_zero hint) hXne
  haveI : IsSplittingField F N (minpoly F α * (X ^ ℓ - 1)) := by
    constructor
    · -- both factors split in `N`
      rw [Polynomial.map_mul]
      refine Splits.mul ?_ ?_
      · exact (Normal.splits inferInstance α).of_isScalarTower N
      · have h2 := IsCyclotomicExtension.splits_X_pow_sub_one E N (Set.mem_singleton ℓ)
        have h3 : (X ^ ℓ - 1 : F[X]).map (algebraMap F N) =
            (X ^ ℓ - 1 : E[X]).map (algebraMap E N) := by
          simp
        rw [h3]
        exact h2
    · -- the roots generate `N` over `F`
      rw [eq_top_iff]
      rintro x -
      have hx := IsCyclotomicExtension.adjoin_roots (S := {ℓ}) (A := E) (B := N) x
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
      · -- roots of unity are roots of `X ^ ℓ - 1`
        rintro b ⟨n, hn, hn0, hb⟩
        rw [Set.mem_singleton_iff] at hn
        subst hn
        refine Algebra.subset_adjoin ?_
        rw [mem_rootSet]
        refine ⟨hqne, ?_⟩
        simp [hb]
      · -- elements of `E` land in the adjoin because `E = F⟮α⟯` and the
        -- image of `α` is a root of its minimal polynomial
        intro r
        have hmem : algebraMap E N α ∈
            Algebra.adjoin F ((minpoly F α * (X ^ ℓ - 1)).rootSet N) := by
          refine Algebra.subset_adjoin ?_
          rw [mem_rootSet]
          refine ⟨hqne, ?_⟩
          have : (aeval (algebraMap E N α)) (minpoly F α) = 0 := by
            rw [aeval_algebraMap_apply, minpoly.aeval, map_zero]
          simp [this]
        have htop : (Algebra.adjoin F {α} : Subalgebra F E) = ⊤ := by
          rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
            hint.isAlgebraic, hα, IntermediateField.top_toSubalgebra]
        have hle : (⊤ : Subalgebra F E) ≤
            (Algebra.adjoin F ((minpoly F α * (X ^ ℓ - 1)).rootSet N)).comap
              (IsScalarTower.toAlgHom F E N) := by
          rw [← htop]
          rw [Algebra.adjoin_le_iff]
          rintro _ rfl
          exact hmem
        exact hle (Algebra.mem_top (R := F) (A := E))
      · intro y z _ _ hy hz
        exact add_mem hy hz
      · intro y z _ _ hy hz
        exact mul_mem hy hz
  exact Normal.of_isSplittingField (minpoly F α * (X ^ ℓ - 1))

open Polynomial in
set_option maxHeartbeats 1000000 in
/-- **The field-crossing lift**: let `E/F` be finite Galois, `ℓ` a prime
with `orderOf τ ∣ ℓ - 1`, and `N = E(ζ_ℓ)` a cyclotomic extension with
`cyclotomic ℓ E` irreducible (so `Gal(N/E) ≃ (ZMod ℓ)ˣ` in full). Then
`τ ∈ Gal(E/F)` lifts to `σ ∈ Gal(N/F)` acting on `ζ_ℓ` through a
*generator* of `(ZMod ℓ)ˣ`: any (integer) power of `σ` fixing `ζ_ℓ` has
exponent divisible by `ℓ - 1`, hence by `orderOf τ`, hence is trivial —
the fixed field of `⟨σ⟩` therefore recovers all of `N` by adjoining
`ζ_ℓ`, which is Chebotarev's trick reducing the cyclic case to the
cyclotomic one. -/
theorem exists_algEquiv_lift_and_forall_zpow_eq_one
    {F E N : Type*} [Field F] [Field E] [Field N] [Algebra F E] [Algebra E N]
    [Algebra F N] [IsScalarTower F E N] [IsGalois F E] [FiniteDimensional F E]
    [Normal F N] {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} E N]
    (hirr : Irreducible (cyclotomic ℓ E)) (τ : E ≃ₐ[F] E)
    (hord : orderOf τ ∣ ℓ - 1) :
    ∃ σ : N ≃ₐ[F] N,
      (∀ x : E, σ (algebraMap E N x) = algebraMap E N (τ x)) ∧
      ∀ k : ℤ, (σ ^ k) (IsCyclotomicExtension.zeta ℓ E N) =
          IsCyclotomicExtension.zeta ℓ E N → σ ^ k = 1 := by
  haveI := Fact.mk hℓ
  set ζ : N := IsCyclotomicExtension.zeta ℓ E N with hζdef
  have hζ : IsPrimitiveRoot ζ ℓ := IsCyclotomicExtension.zeta_spec ℓ E N
  set χ : (N ≃ₐ[F] N) →* (ZMod ℓ)ˣ := hζ.autToPow F with hχdef
  -- two units acting identically on `ζ` are equal
  have key : ∀ u v : (ZMod ℓ)ˣ,
      ζ ^ ((u : ZMod ℓ)).val = ζ ^ ((v : ZMod ℓ)).val → u = v := by
    intro u v huv
    exact Units.ext (ZMod.val_injective ℓ
      (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv))
  -- the canonical lift of `τ` and a generator of `(ZMod ℓ)ˣ`
  set σ₀ : N ≃ₐ[F] N := τ.liftNormal N with hσ₀def
  have hσ₀ : ∀ x : E, σ₀ (algebraMap E N x) = algebraMap E N (τ x) := fun x =>
    AlgEquiv.liftNormal_commutes τ N x
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  -- correct `σ₀` by the `E`-automorphism with character `g * (χ σ₀)⁻¹`
  set he : N ≃ₐ[E] N :=
    (IsCyclotomicExtension.autEquivPow N hirr).symm (g * (χ σ₀)⁻¹) with hhedef
  have hheχ : χ (he.restrictScalars F) = g * (χ σ₀)⁻¹ := by
    refine key _ _ ?_
    rw [hχdef, IsPrimitiveRoot.autToPow_spec, AlgEquiv.restrictScalars_apply]
    have h1 := (IsCyclotomicExtension.autEquivPow N hirr).apply_symm_apply
      (g * (χ σ₀)⁻¹)
    rw [← hhedef] at h1
    rw [← h1, IsCyclotomicExtension.autEquivPow_apply]
    exact (IsPrimitiveRoot.autToPow_spec E (IsCyclotomicExtension.zeta_spec ℓ E N)
      he).symm
  set σ : N ≃ₐ[F] N := (he.restrictScalars F) * σ₀ with hσdef
  have hσE : ∀ x : E, σ (algebraMap E N x) = algebraMap E N (τ x) := by
    intro x
    rw [hσdef, AlgEquiv.mul_apply, hσ₀, AlgEquiv.restrictScalars_apply]
    exact he.commutes (τ x)
  have hχσ : χ σ = g := by
    rw [hσdef, map_mul, hheχ, inv_mul_cancel_right]
  -- the constructions above are now fully characterized by `hζ`, `hσE`, `hχσ`;
  -- make them opaque so later elaboration cannot unfold their large bodies
  clear hheχ hσ₀ hζdef hhedef hσ₀def hσdef
  clear_value ζ σ₀ he σ
  -- the order of `g` is `ℓ - 1`
  have hordg : orderOf g = ℓ - 1 := by
    have h1 : orderOf g = Nat.card (ZMod ℓ)ˣ :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    rw [h1, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hℓ]
  refine ⟨σ, hσE, ?_⟩
  intro k hk
  -- the character kills `σ ^ k`, so `ℓ - 1 ∣ k`, so `orderOf τ ∣ k`
  have h2 : χ (σ ^ k) = 1 := by
    refine key _ _ ?_
    rw [hχdef, IsPrimitiveRoot.autToPow_spec, hk, Units.val_one, ZMod.val_one ℓ,
      pow_one]
  have h3 : g ^ k = 1 := by
    rw [← hχσ, ← map_zpow]
    exact h2
  have h4 : ((ℓ - 1 : ℕ) : ℤ) ∣ k := by
    rw [← hordg]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h3
  have h5 : τ ^ k = 1 := by
    have h6 : ((orderOf τ : ℕ) : ℤ) ∣ k :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hord) h4
    exact orderOf_dvd_iff_zpow_eq_one.mp h6
  -- `σ ^ k` acts on the image of `E` through `τ ^ k`
  have hpow : ∀ m : ℕ, ∀ x : E,
      (σ ^ m) (algebraMap E N x) = algebraMap E N ((τ ^ m) x) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, hσE, ih, pow_succ, AlgEquiv.mul_apply]
  have hzpow : ∀ x : E, (σ ^ k) (algebraMap E N x) = algebraMap E N ((τ ^ k) x) := by
    intro x
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, zpow_natCast]
      exact hpow m x
    · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, AlgEquiv.aut_inv,
        AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hpow m,
        AlgEquiv.apply_symm_apply]
  -- `N` is generated over `F` by the image of `E` together with `ζ`:
  -- the `F`-subalgebra generated by them contains the image of `E`, hence is
  -- an `E`-subalgebra, and as such contains `adjoin E {ζ} = ⊤`
  have hgen_top : Algebra.adjoin F (Set.range (algebraMap E N) ∪ {ζ}) = ⊤ := by
    have hE : Algebra.adjoin E {ζ} = ⊤ :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    let T_E : Subalgebra E N :=
      { (Algebra.adjoin F (Set.range (algebraMap E N) ∪ {ζ})).toSubsemiring with
        algebraMap_mem' := fun r =>
          Algebra.subset_adjoin (Set.mem_union_left _ ⟨r, rfl⟩) }
    have h1 : Algebra.adjoin E {ζ} ≤ T_E :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr
        (Algebra.subset_adjoin (Set.mem_union_right _ rfl)))
    rw [hE] at h1
    rw [eq_top_iff]
    intro x _
    exact h1 (show x ∈ (⊤ : Subalgebra E N) from trivial)
  -- `σ ^ k` agrees with the identity on the generators, hence everywhere
  have hEqOn : Set.EqOn (↑(σ ^ k : N ≃ₐ[F] N) : N →ₐ[F] N) (AlgHom.id F N)
      (Set.range (algebraMap E N) ∪ {ζ}) := by
    rintro y (⟨x, rfl⟩ | rfl)
    · show (σ ^ k) (algebraMap E N x) = algebraMap E N x
      rw [hzpow, h5, AlgEquiv.one_apply]
    · exact hk
  have hAlgHom : ((σ ^ k : N ≃ₐ[F] N) : N →ₐ[F] N) = AlgHom.id F N :=
    AlgHom.ext_of_adjoin_eq_top hgen_top hEqOn
  refine AlgEquiv.ext fun x => ?_
  have := DFunLike.congr_fun hAlgHom x
  simpa using this

open Polynomial in
/-- The subfield generated over `ℚ` by a primitive `m`-th root of unity in
any characteristic-zero field of integral elements has degree `φ(m)`:
`cyclotomic m ℚ` is irreducible. -/
lemma finrank_adjoin_simple_of_isPrimitiveRoot {W : Type*} [Field W] [CharZero W]
    [Algebra.IsIntegral ℚ W] {m : ℕ} [NeZero m] {ζ : W} (hζ : IsPrimitiveRoot ζ m) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set W)) = m.totient := by
  haveI := hζ.adjoin_isCyclotomicExtension ℚ
  have h1 : Module.finrank ℚ (Algebra.adjoin ℚ ({ζ} : Set W)) = m.totient :=
    IsCyclotomicExtension.finrank (Algebra.adjoin ℚ ({ζ} : Set W))
      (cyclotomic.irreducible_rat (NeZero.pos m))
  have h2 : (IntermediateField.adjoin ℚ ({ζ} : Set W)).toSubalgebra =
      Algebra.adjoin ℚ ({ζ} : Set W) :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsIntegral.isIntegral ζ).isAlgebraic
  rw [← h1]
  exact (Subalgebra.equivOfEq _ _ h2).toLinearEquiv.finrank_eq

/-- Every `m`-th root of unity lies in the subfield generated by a primitive
one. -/
lemma mem_adjoin_simple_of_pow_eq_one {W : Type*} [Field W] (K : Type*) [Field K]
    [Algebra K W] {m : ℕ} [NeZero m] {ξ b : W} (hξ : IsPrimitiveRoot ξ m)
    (hb : b ^ m = 1) : b ∈ IntermediateField.adjoin K ({ξ} : Set W) := by
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hb
  exact pow_mem (IntermediateField.subset_adjoin K {ξ} rfl) i

open Polynomial IntermediateField in
/-- **Distinct prime cyclotomic subfields intersect trivially**: for distinct
primes `l ≠ l'`, the subfields of a characteristic-zero field generated over
`ℚ` by primitive `l`-th and `l'`-th roots of unity meet in `ℚ`. Degree
counting in the compositum, which is generated by a primitive `l*l'`-th root
of unity and has degree `φ(l)·φ(l')` — no ramification theory needed. -/
lemma adjoin_inf_adjoin_eq_bot_of_isPrimitiveRoot {W : Type*} [Field W]
    [CharZero W] [Algebra.IsIntegral ℚ W] {l l' : ℕ} (hl : l.Prime)
    (hl' : l'.Prime) (hne : l ≠ l') {ζ η : W} (hζ : IsPrimitiveRoot ζ l)
    (hη : IsPrimitiveRoot η l') :
    IntermediateField.adjoin ℚ ({ζ} : Set W) ⊓
      IntermediateField.adjoin ℚ ({η} : Set W) = ⊥ := by
  haveI : NeZero l := ⟨hl.pos.ne'⟩
  haveI : NeZero l' := ⟨hl'.pos.ne'⟩
  haveI : NeZero (l * l') := ⟨Nat.mul_ne_zero hl.pos.ne' hl'.pos.ne'⟩
  have hcop : Nat.Coprime l l' := (Nat.coprime_primes hl hl').mpr hne
  have hξ0 := hζ.pow_mul_pow_lcm hη hl.pos.ne' hl'.pos.ne'
  rw [Nat.Coprime.lcm_eq_mul hcop] at hξ0
  set ξ : W := ζ ^ (l / Nat.factorizationLCMLeft l l') *
    η ^ (l' / Nat.factorizationLCMRight l l')
  -- the compositum is the `l*l'`-th cyclotomic subfield
  have hsup : IntermediateField.adjoin ℚ ({ζ} : Set W) ⊔
      IntermediateField.adjoin ℚ ({η} : Set W) =
      IntermediateField.adjoin ℚ ({ξ} : Set W) := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      refine mem_adjoin_simple_of_pow_eq_one ℚ hξ0 ?_
      rw [pow_mul, hζ.pow_eq_one, one_pow]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      refine mem_adjoin_simple_of_pow_eq_one ℚ hξ0 ?_
      rw [mul_comm l l', pow_mul, hη.pow_eq_one, one_pow]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      refine mul_mem ?_ ?_
      · exact pow_mem (le_sup_left (α := IntermediateField ℚ W)
          (IntermediateField.subset_adjoin ℚ {ζ} rfl)) _
      · exact pow_mem (le_sup_right (α := IntermediateField ℚ W)
          (IntermediateField.subset_adjoin ℚ {η} rfl)) _
  -- degree counting gives linear disjointness
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({ζ} : Set W)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({η} : Set W)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral η)
  have hld : (IntermediateField.adjoin ℚ ({ζ} : Set W)).LinearDisjoint
      (IntermediateField.adjoin ℚ ({η} : Set W)) := by
    refine IntermediateField.LinearDisjoint.of_finrank_sup ?_
    rw [hsup, finrank_adjoin_simple_of_isPrimitiveRoot hξ0,
      finrank_adjoin_simple_of_isPrimitiveRoot hζ,
      finrank_adjoin_simple_of_isPrimitiveRoot hη, ← Nat.totient_mul hcop]
  exact hld.inf_eq_bot

open Polynomial IntermediateField in
/-- **Irreducibility criterion for `cyclotomic l E`**: if inside
`W = CyclotomicField l E` the image of `E` meets the `l`-th cyclotomic
subfield `ℚ(ζ_l)` trivially, then `cyclotomic l E` is irreducible. Linear
disjointness (the cyclotomic side is Galois over `ℚ`) forces
`[W : ℚ] = φ(l)·[E : ℚ]`, hence `[W : E] = φ(l)`, so the minimal polynomial
of `ζ_l` over `E` has full degree and equals `cyclotomic l E`, which is
therefore irreducible. -/
lemma irreducible_cyclotomic_of_inf_eq_bot {E : Type*} [Field E] [NumberField E]
    {l : ℕ} [NeZero l]
    (h : (IsScalarTower.toAlgHom ℚ E (CyclotomicField l E)).fieldRange ⊓
      IntermediateField.adjoin ℚ
        ({IsCyclotomicExtension.zeta l E (CyclotomicField l E)} :
          Set (CyclotomicField l E)) = ⊥) :
    Irreducible (cyclotomic l E) := by
  set W := CyclotomicField l E
  set ζ : W := IsCyclotomicExtension.zeta l E W
  have hζ : IsPrimitiveRoot ζ l := IsCyclotomicExtension.zeta_spec l E W
  set A : IntermediateField ℚ W := IntermediateField.adjoin ℚ {ζ}
  set E₀ : IntermediateField ℚ W :=
    (IsScalarTower.toAlgHom ℚ E W).fieldRange
  haveI hcycA : IsCyclotomicExtension {l} ℚ A :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  haveI hGalA : IsGalois ℚ A :=
    IsCyclotomicExtension.isGalois (S := {l}) (K := ℚ) (L := A)
  haveI hFDA : FiniteDimensional ℚ A :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI hFDE₀ : FiniteDimensional ℚ E₀ := (AlgEquiv.ofInjectiveField
    (IsScalarTower.toAlgHom ℚ E W)).toLinearEquiv.finiteDimensional
  have hld : A.LinearDisjoint E₀ :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot ℚ W _ _ _ A E₀ hGalA hFDA hFDE₀
      (by rwa [inf_comm] at h)
  -- the compositum is all of `W`: it is an `E`-subalgebra containing all
  -- `l`-th roots of unity
  have hsup : A ⊔ E₀ = ⊤ := by
    have hE : Algebra.adjoin E ({ζ} : Set W) = ⊤ :=
      IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    let T_E : Subalgebra E W :=
      { (A ⊔ E₀).toSubalgebra.toSubsemiring with
        algebraMap_mem' := fun r => le_sup_right (α := IntermediateField ℚ W)
          (show algebraMap E W r ∈ E₀ from ⟨r, rfl⟩) }
    have h1 : Algebra.adjoin E ({ζ} : Set W) ≤ T_E :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr
        (le_sup_left (α := IntermediateField ℚ W)
          (IntermediateField.subset_adjoin ℚ {ζ} rfl)))
    rw [hE] at h1
    rw [eq_top_iff]
    intro x _
    exact h1 (show x ∈ (⊤ : Subalgebra E W) from trivial)
  -- degree count: `[W : E] = φ(l)`
  have hcount : Module.finrank ℚ W = l.totient * Module.finrank ℚ E := by
    have h2 := hld.finrank_sup
    rw [hsup] at h2
    rw [IntermediateField.finrank_top', finrank_adjoin_simple_of_isPrimitiveRoot hζ]
      at h2
    have h3 : Module.finrank ℚ E₀ = Module.finrank ℚ E :=
      ((AlgEquiv.ofInjectiveField
        (IsScalarTower.toAlgHom ℚ E W)).toLinearEquiv.finrank_eq).symm
    rw [h3] at h2
    exact h2
  have hEW : Module.finrank E W = l.totient := by
    have h5 : Module.finrank ℚ E * Module.finrank E W = Module.finrank ℚ W :=
      Module.finrank_mul_finrank ℚ E W
    rw [hcount, mul_comm (l.totient)] at h5
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h5
  -- the minimal polynomial of `ζ` over `E` is `cyclotomic l E` itself
  have hζint : IsIntegral E ζ := (IsCyclotomicExtension.integral {l} E W).isIntegral ζ
  have hdvd : minpoly E ζ ∣ cyclotomic l E := by
    refine minpoly.dvd E ζ ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos l)
  have hdeg : (minpoly E ζ).natDegree = (cyclotomic l E).natDegree := by
    rw [natDegree_cyclotomic, ← hEW, (hζ.powerBasis E).finrank,
      IsPrimitiveRoot.powerBasis_dim]
  have hmono := minpoly.monic hζint
  obtain ⟨c, hc⟩ := hdvd
  have hcy0 : cyclotomic l E ≠ 0 := cyclotomic_ne_zero l E
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hcy0 hc
  have hdegc : c.natDegree = 0 := by
    have h6 : (cyclotomic l E).natDegree =
        (minpoly E ζ).natDegree + c.natDegree := by
      rw [hc, natDegree_mul hmono.ne_zero hc0]
    omega
  have heq : minpoly E ζ = cyclotomic l E := by
    have h7 : c = C (c.coeff 0) := eq_C_of_natDegree_eq_zero hdegc
    have h8 : c.coeff 0 = 1 := by
      have h9 := congrArg leadingCoeff hc
      rw [leadingCoeff_mul, hmono.leadingCoeff,
        (cyclotomic.monic l E).leadingCoeff, one_mul, h7,
        leadingCoeff_C] at h9
      exact h9.symm
    rw [hc, h7, h8, map_one, mul_one]
  rw [← heq]
  exact minpoly.irreducible hζint

open Polynomial in
/-- **Auxiliary primes for the Chebotarev field-crossing**: for every number
field `E` and every `n ≠ 0` there is a prime `ℓ` with `n ∣ ℓ - 1` (i.e.
`ℓ ≡ 1 (mod n)`) whose `ℓ`-th cyclotomic polynomial remains irreducible
over `E`.

DERIVED, purely algebraically — no density and no ramification theory:
primes `ℓ ≡ 1 (mod n)` exist in abundance by the elementary
cyclotomic-polynomial argument (`Nat.exists_prime_gt_modEq_one`). If
`cyclotomic ℓ E` were reducible for such an `ℓ`, the intersection
`M_ℓ = E ∩ ℚ(ζ_ℓ)` (computed inside `CyclotomicField ℓ E` and pulled back
to `E`) would be a NONTRIVIAL subfield of `E`
(`irreducible_cyclotomic_of_inf_eq_bot`). But `E` has only finitely many
subfields (primitive element theorem), while distinct primes give
`ℚ`-linearly disjoint cyclotomic fields
(`adjoin_inf_adjoin_eq_bot_of_isPrimitiveRoot`): a common nontrivial
subfield of `ℚ(ζ_ℓ)` and `ℚ(ζ_ℓ')` for `ℓ ≠ ℓ'` is impossible. Pigeonhole
on infinitely many bad primes yields a contradiction. -/
theorem exists_prime_dvd_sub_one_and_irreducible_cyclotomic
    (E : Type*) [Field E] [NumberField E] {n : ℕ} (hn : n ≠ 0) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ n ∣ ℓ - 1 ∧ Irreducible (cyclotomic ℓ E) := by
  classical
  by_contra hcon
  push Not at hcon
  -- the set of auxiliary primes is infinite, and all of them are "bad"
  set S : Set ℕ := {ℓ | ℓ.Prime ∧ n ∣ ℓ - 1}
  have hSinf : S.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨m, hm⟩
    obtain ⟨p, hp, hpgt, hpmod⟩ := Nat.exists_prime_gt_modEq_one (k := n) m hn
    exact absurd (hm ⟨hp, (Nat.modEq_iff_dvd' hp.one_lt.le).mp hpmod.symm⟩)
      (not_le.mpr hpgt)
  -- the nontrivial subfield of `E` cut out by a bad prime
  have key : ∀ ℓ : ℕ, ℓ.Prime → n ∣ ℓ - 1 →
      ∃ M : IntermediateField ℚ E, M ≠ ⊥ ∧
        ∀ m : ℕ, ∀ μ : CyclotomicField m E, IsPrimitiveRoot μ ℓ →
          IntermediateField.map (IsScalarTower.toAlgHom ℚ E (CyclotomicField m E))
              M ≤ IntermediateField.adjoin ℚ ({μ} : Set (CyclotomicField m E)) := by
    intro ℓ hℓ hℓn
    haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
    set W₀ := CyclotomicField ℓ E
    set ζ : W₀ := IsCyclotomicExtension.zeta ℓ E W₀
    have hζ : IsPrimitiveRoot ζ ℓ := IsCyclotomicExtension.zeta_spec ℓ E W₀
    -- the intersection is nontrivial since `cyclotomic ℓ E` is reducible
    have hbad : (IsScalarTower.toAlgHom ℚ E W₀).fieldRange ⊓
        IntermediateField.adjoin ℚ ({ζ} : Set W₀) ≠ ⊥ := by
      intro hbot
      exact hcon ℓ hℓ hℓn (irreducible_cyclotomic_of_inf_eq_bot hbot)
    -- pull it back to a subfield of `E`
    refine ⟨((IsScalarTower.toAlgHom ℚ E W₀).fieldRange ⊓
      IntermediateField.adjoin ℚ ({ζ} : Set W₀)).comap
        (IsScalarTower.toAlgHom ℚ E W₀), ?_, ?_⟩
    · -- nontriviality survives the pullback
      intro hbot
      apply hbad
      rw [eq_bot_iff]
      rintro x ⟨⟨y, rfl⟩, hxA⟩
      have hy : y ∈ ((IsScalarTower.toAlgHom ℚ E W₀).fieldRange ⊓
          IntermediateField.adjoin ℚ ({ζ} : Set W₀)).comap
            (IsScalarTower.toAlgHom ℚ E W₀) := ⟨⟨y, rfl⟩, hxA⟩
      rw [hbot] at hy
      obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact IntermediateField.mem_bot.mpr
        ⟨q, (IsScalarTower.algebraMap_apply ℚ E W₀ q).symm⟩
    · -- and the image lands in ANY `ℓ`-th cyclotomic subfield, via a lift
      -- of the splitting field
      intro m μ hμ
      -- `cyclotomic ℓ E` splits in `CyclotomicField m E`: it divides `X ^ ℓ - 1`
      have hXne : (X ^ ℓ - 1 : E[X]) ≠ 0 := by
        have h1 : ((1 : E[X]) = C 1) := by simp
        rw [h1]
        exact X_pow_sub_C_ne_zero (NeZero.pos ℓ) 1
      have hbig : Splits ((X ^ ℓ - 1 : E[X]).map
          (algebraMap E (CyclotomicField m E))) := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_one]
        exact X_pow_sub_one_splits hμ
      have hdvdX : cyclotomic ℓ E ∣ X ^ ℓ - 1 := by
        refine ⟨∏ i ∈ ℓ.properDivisors, cyclotomic i E, ?_⟩
        rw [(eq_cyclotomic_iff (NeZero.pos ℓ) _).1 rfl]
      have hsplits : Splits ((cyclotomic ℓ E).map
          (algebraMap E (CyclotomicField m E))) :=
        hbig.of_dvd (map_ne_zero hXne)
          ((map_dvd_map' (algebraMap E (CyclotomicField m E))).mpr hdvdX)
      -- lift the splitting field into `CyclotomicField m E`
      haveI := IsCyclotomicExtension.splitting_field_cyclotomic ℓ E W₀
      set j : W₀ →ₐ[E] CyclotomicField m E :=
        IsSplittingField.lift W₀ (cyclotomic ℓ E) hsplits
      rintro _ ⟨x, hx, rfl⟩
      obtain hxA : (IsScalarTower.toAlgHom ℚ E W₀) x ∈
          IntermediateField.adjoin ℚ ({ζ} : Set W₀) := hx.2
      -- push the membership through `j`
      have hmap : (IntermediateField.adjoin ℚ ({ζ} : Set W₀)).map
          (j.restrictScalars ℚ) =
          IntermediateField.adjoin ℚ ({j ζ} : Set (CyclotomicField m E)) := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
        rfl
      have h1 : j ((IsScalarTower.toAlgHom ℚ E W₀) x) ∈
          IntermediateField.adjoin ℚ ({j ζ} : Set (CyclotomicField m E)) := by
        rw [← hmap]
        exact ⟨_, hxA, rfl⟩
      have h2 : IntermediateField.adjoin ℚ ({j ζ} : Set (CyclotomicField m E)) ≤
          IntermediateField.adjoin ℚ ({μ} : Set (CyclotomicField m E)) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ rfl
        exact mem_adjoin_simple_of_pow_eq_one ℚ hμ
          (hζ.map_of_injective j.injective).pow_eq_one
      have h4 := h2 h1
      have h3 : (IsScalarTower.toAlgHom ℚ E (CyclotomicField m E)) x =
          j ((IsScalarTower.toAlgHom ℚ E W₀) x) := (j.commutes x).symm
      rw [← h3] at h4
      exact h4
  -- choose the subfield for each auxiliary prime and apply the pigeonhole
  haveI : Finite (IntermediateField ℚ E) :=
    (Field.exists_primitive_element_iff_finite_intermediateField
      (F := ℚ) (E := E)).mp ⟨inferInstance, Field.exists_primitive_element ℚ E⟩
  have key' : ∀ ℓ : ℕ, ℓ ∈ S → ∃ M : IntermediateField ℚ E, M ≠ ⊥ ∧
      ∀ m : ℕ, ∀ μ : CyclotomicField m E, IsPrimitiveRoot μ ℓ →
        IntermediateField.map (IsScalarTower.toAlgHom ℚ E (CyclotomicField m E))
            M ≤ IntermediateField.adjoin ℚ ({μ} : Set (CyclotomicField m E)) :=
    fun ℓ hℓ => key ℓ hℓ.1 hℓ.2
  choose! Mf hMne hMmap using key'
  obtain ⟨ℓ, hℓS, ℓ', hℓ'S, hℓne, hMeq⟩ :=
    hSinf.exists_ne_map_eq_of_mapsTo (f := Mf)
      (Set.mapsTo_univ Mf S) Set.finite_univ
  have hℓp := hℓS.1
  have hℓ'p := hℓ'S.1
  haveI : NeZero ℓ := ⟨hℓp.pos.ne'⟩
  haveI : NeZero ℓ' := ⟨hℓ'p.pos.ne'⟩
  haveI : NeZero (ℓ * ℓ') := ⟨Nat.mul_ne_zero hℓp.pos.ne' hℓ'p.pos.ne'⟩
  -- a nonzero element of the common subfield
  obtain ⟨y, hyM, hyB⟩ := SetLike.not_le_iff_exists.mp
    (fun hle => hMne ℓ hℓS (eq_bot_iff.mpr hle))
  -- the common cyclotomic home for the pair
  set W₂ := CyclotomicField (ℓ * ℓ') E
  set ξ : W₂ := IsCyclotomicExtension.zeta (ℓ * ℓ') E W₂
  have hξ : IsPrimitiveRoot ξ (ℓ * ℓ') := IsCyclotomicExtension.zeta_spec _ E W₂
  have hμℓ : IsPrimitiveRoot (ξ ^ ℓ') ℓ := by
    have := hξ.pow (NeZero.pos (ℓ * ℓ')) (mul_comm ℓ ℓ')
    exact this
  have hμℓ' : IsPrimitiveRoot (ξ ^ ℓ) ℓ' := hξ.pow (NeZero.pos (ℓ * ℓ')) rfl
  -- the image of `y` lies in both prime cyclotomic subfields
  have hy1 : (IsScalarTower.toAlgHom ℚ E W₂) y ∈
      IntermediateField.adjoin ℚ ({ξ ^ ℓ'} : Set W₂) :=
    hMmap ℓ hℓS (ℓ * ℓ') (ξ ^ ℓ') hμℓ ⟨y, hyM, rfl⟩
  have hy2 : (IsScalarTower.toAlgHom ℚ E W₂) y ∈
      IntermediateField.adjoin ℚ ({ξ ^ ℓ} : Set W₂) := by
    refine hMmap ℓ' hℓ'S (ℓ * ℓ') (ξ ^ ℓ) hμℓ' ⟨y, ?_, rfl⟩
    rw [← hMeq]
    exact hyM
  -- but those subfields intersect trivially
  have hbot := adjoin_inf_adjoin_eq_bot_of_isPrimitiveRoot hℓp hℓ'p hℓne hμℓ hμℓ'
  have hy3 : (IsScalarTower.toAlgHom ℚ E W₂) y ∈
      (⊥ : IntermediateField ℚ W₂) := by
    rw [← hbot]
    exact ⟨hy1, hy2⟩
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hy3
  apply hyB
  refine IntermediateField.mem_bot.mpr ⟨q, ?_⟩
  have h4 : (IsScalarTower.toAlgHom ℚ E W₂) (algebraMap ℚ E q) =
      (IsScalarTower.toAlgHom ℚ E W₂) y := by
    rw [show (IsScalarTower.toAlgHom ℚ E W₂) (algebraMap ℚ E q) =
      algebraMap ℚ W₂ q from ((IsScalarTower.algebraMap_apply ℚ E W₂ q).symm), hq]
  exact (IsScalarTower.toAlgHom ℚ E W₂).injective h4

/-!
### Analytic auxiliaries for the Dedekind-zeta half

The divergence leaf `exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne`
is ASSEMBLED below from seven strictly shallower pieces. Writing
`Z(t) = ∑_{I ≠ 0} N(I)^{-t}` (ideals of `𝓞 F`) and
`Π(s) = ∑_P N(P)^{-s}` (finite places), the chain is: were the
degree-one prime sum bounded by `C` for all `s > 1`, then `Π(s) ≤
C + B` uniformly (tail lemmas `tsum_not_prime_natCard_rpow_neg_one_ne_top`
and `finite_setOf_natCard_quotient_eq`), hence by the square-times-
squarefree decomposition (`tsum_rpow_neg_absNorm_le_mul_tsum_finset_prod`)
and the exponential bound over finite subsets
(`tsum_finset_prod_le_tsum_pow_div_factorial`,
`tsum_pow_div_factorial_ne_top`) the whole ideal sum satisfies
`Z(s) ≤ Z(2) · exp-series(C + B) < ⊤` uniformly in `s > 1` —
contradicting the divergence `Z(s) → ∞` as `s → 1⁺`
(`exists_one_lt_lt_tsum_rpow_neg_absNorm`, from the simple pole of the
Dedekind zeta function). No Euler product and no `ENNReal`
subtraction appear anywhere.
-/

/-- The `ℝ≥0∞`-valued exponential series `∑ S ^ k / k!` is finite for
finite `S`: each term is `ENNReal.ofReal (S.toReal ^ k / k!)` and the
series sums to `ENNReal.ofReal (Real.exp S.toReal)` by
`Real.summable_pow_div_factorial` and `ENNReal.ofReal_tsum_of_nonneg`. -/
theorem tsum_pow_div_factorial_ne_top (S : ℝ≥0∞) (hS : S ≠ ⊤) :
    ∑' k : ℕ, S ^ k / (Nat.factorial k : ℝ≥0∞) ≠ ⊤ := by
  have hterm : ∀ k : ℕ, S ^ k / (Nat.factorial k : ℝ≥0∞) =
      ENNReal.ofReal (S.toReal ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast k.factorial_pos),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hS,
      ENNReal.ofReal_natCast]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
    (fun k => by positivity) (Real.summable_pow_div_factorial S.toReal)]
  exact ENNReal.ofReal_ne_top

/-- **Exponential bound for sums of products over finite subsets**
(sorry leaf): for any family `x : ι → ℝ≥0∞`,
`∑_{T : Finset ι} ∏_{i ∈ T} x i ≤ ∑_k (∑ x)^k / k!`. Intended proof:
fibre the left side over `k = #T`; each `T` with `#T = k` arises from
exactly `k!` injections `Fin k ↪ ι` (with `∏_{j} x (f j) = ∏_{i ∈ T} x i`
for any injection with image `T`), and the sum over ALL functions
`Fin k → ι` of `∏_j x (f j)` is exactly `(∑ x)^k`
(`ENNReal.tsum_prod` and induction on `k`), so
`k! · ∑_{#T = k} ∏_{T} x ≤ (∑ x)^k`. -/
theorem tsum_finset_prod_le_tsum_pow_div_factorial {ι : Type*} (x : ι → ℝ≥0∞) :
    ∑' T : Finset ι, ∏ i ∈ T, x i ≤
      ∑' k : ℕ, (∑' i : ι, x i) ^ k / (Nat.factorial k : ℝ≥0∞) := by
  classical
  -- the `k`-th power of the sum is the sum over all `k`-tuples
  have hpow : ∀ k : ℕ, (∑' i : ι, x i) ^ k =
      ∑' v : Fin k → ι, ∏ j : Fin k, x (v j) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, tsum_eq_single (default : Fin 0 → ι) (fun b hb =>
        absurd (Subsingleton.elim b default) hb)]
      simp
    | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).tsum_eq
        (fun v : Fin (n + 1) → ι => ∏ j, x (v j))]
      calc (∑' i : ι, x i) ^ (n + 1)
          = (∑' i : ι, x i) * (∑' i : ι, x i) ^ n := pow_succ' _ _
        _ = ∑' i : ι, x i * ∑' v : Fin n → ι, ∏ j : Fin n, x (v j) := by
            rw [ih, ENNReal.tsum_mul_right]
        _ = ∑' p : ι × (Fin n → ι), ∏ j : Fin (n + 1),
              x ((Fin.consEquiv (fun _ : Fin (n + 1) => ι)) p j) := by
            rw [ENNReal.tsum_prod']
            refine tsum_congr fun a => ?_
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun v => ?_
            rw [Fin.prod_univ_succ]
            simp [Fin.consEquiv]
  -- fibre the left side over the cardinality
  rw [← ENNReal.tsum_fiberwise (fun T : Finset ι => ∏ i ∈ T, x i)
    (fun T : Finset ι => T.card)]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast k.factorial_ne_zero))
    (Or.inl (ENNReal.natCast_ne_top _)), hpow k]
  -- the embeddings of `Fin k`, fibered over their image
  have hΦmem : ∀ v : Fin k ↪ ι, Finset.univ.map v ∈
      ((fun T : Finset ι => T.card) ⁻¹' {k} : Set (Finset ι)) := by
    intro v
    simp [Finset.card_map]
  set Φ : (Fin k ↪ ι) →
      ((fun T : Finset ι => T.card) ⁻¹' {k} : Set (Finset ι)) :=
    fun v => ⟨Finset.univ.map v, hΦmem v⟩
  have hemb : (∑' T : ((fun T : Finset ι => T.card) ⁻¹' {k} : Set (Finset ι)),
      ∏ i ∈ (T : Finset ι), x i) * (Nat.factorial k : ℝ≥0∞) =
      ∑' v : Fin k ↪ ι, ∏ j : Fin k, x (v j) := by
    rw [← ENNReal.tsum_fiberwise (fun v : Fin k ↪ ι => ∏ j : Fin k, x (v j)) Φ,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun T => ?_
    -- each fiber element has product `∏_{i ∈ T} x i`
    have hconst : ∀ w : ↥(Φ ⁻¹' {T}),
        (∏ j : Fin k, x (w.1 j)) = ∏ i ∈ (T : Finset ι), x i := by
      intro w
      have huniv : Finset.univ.map w.1 = (T : Finset ι) :=
        congrArg Subtype.val w.2
      rw [← huniv, Finset.prod_map]
    -- the fiber is equivalent to the embeddings into `↥T`, of which
    -- there are exactly `k!`
    have e : ↥(Φ ⁻¹' {T}) ≃ (Fin k ↪ ↥(T : Finset ι)) :=
      { toFun := fun w =>
          ⟨fun j => ⟨w.1 j, by
            have huniv : Finset.univ.map w.1 = (T : Finset ι) :=
              congrArg Subtype.val w.2
            rw [← huniv]
            exact Finset.mem_map_of_mem _ (Finset.mem_univ j)⟩,
          fun a b hab => w.1.injective (congrArg Subtype.val hab)⟩
        invFun := fun w =>
          ⟨⟨fun j => (w j : ι),
            fun a b hab => w.injective (Subtype.ext hab)⟩, by
            have hsub : Finset.univ.map
                (⟨fun j => (w j : ι), fun a b hab =>
                  w.injective (Subtype.ext hab)⟩ : Fin k ↪ ι) ⊆
                (T : Finset ι) := by
              intro i hi
              obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
              exact (w j).2
            refine Subtype.ext (Finset.eq_of_subset_of_card_le hsub ?_)
            rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
            exact le_of_eq T.2⟩
        left_inv := fun w => Subtype.ext (DFunLike.ext _ _ fun j => rfl)
        right_inv := fun w => DFunLike.ext _ _ fun j => Subtype.ext rfl }
    haveI : Finite ↥(Φ ⁻¹' {T}) := Finite.of_equiv _ e.symm
    rw [tsum_congr hconst, ENNReal.tsum_const, ENat.card_eq_coe_natCard,
      Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_coe,
      show (T : Finset ι).card = k from T.2, Nat.descFactorial_self, mul_comm]
    norm_cast
  calc (∑' T : ((fun T : Finset ι => T.card) ⁻¹' {k} : Set (Finset ι)),
        ∏ i ∈ (T : Finset ι), x i) * (Nat.factorial k : ℝ≥0∞)
      = ∑' v : Fin k ↪ ι, ∏ j : Fin k, x (v j) := hemb
    _ ≤ ∑' v : Fin k → ι, ∏ j : Fin k, x (v j) :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun v : Fin k ↪ ι => (v : Fin k → ι))
          DFunLike.coe_injective (fun u => ∏ j : Fin k, x (u j))

open IsDedekindDomain in
/-- Finiteness of the set of finite places with prescribed residue
cardinality: `P ↦ P.asIdeal` embeds it into the finite set of ideals of
absolute norm `ℓ` (`Ideal.finite_setOf_absNorm_eq`). -/
theorem finite_setOf_natCard_quotient_eq (F : Type*) [Field F] [NumberField F]
    (ℓ : ℕ) :
    {P : HeightOneSpectrum (𝓞 F) | Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun P : HeightOneSpectrum (𝓞 F) => P.asIdeal)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) ℓ).subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩
    simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hP
  · intro P _ Q _ h
    exact HeightOneSpectrum.ext h

open IsDedekindDomain in
/-- **Uniform tail bound for the higher-degree places** (sorry leaf): the
sum of `#(𝓞 F / P)⁻¹` over the finite places whose residue cardinality
is NOT prime (residue degree `≥ 2` over `ℚ`) is finite. Intended proof:
such a place has `#(𝓞 F / P) = p ^ f ≥ p ^ 2` for `p` its residue
characteristic; at most `[F : ℚ]` places share a residue characteristic
(`Ideal.card_primesOverFinset_le_finrank`), so the sum is at most
`[F : ℚ] · ∑_p p⁻²  < ⊤`. -/
theorem tsum_not_prime_natCard_rpow_neg_one_ne_top
    (F : Type*) [Field F] [NumberField F] :
    ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
        (-(1 : ℝ)) ≠ ⊤ := by
  classical
  -- per-place data: the residue characteristic is prime, and its square
  -- is at most the residue cardinality (the residue degree is `≥ 2`)
  have hdata : ∀ P : {P : HeightOneSpectrum (𝓞 F) //
      ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
      (ringChar (𝓞 F ⧸ P.1.asIdeal)).Prime ∧
        ringChar (𝓞 F ⧸ P.1.asIdeal) ^ 2 ≤ Nat.card (𝓞 F ⧸ P.1.asIdeal) := by
    rintro ⟨P, hnp⟩
    have hcard0 : Nat.card (𝓞 F ⧸ P.asIdeal) ≠ 0 := by
      have h1 : Ideal.absNorm P.asIdeal ≠ 0 := fun h =>
        P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    haveI hfin : Finite (𝓞 F ⧸ P.asIdeal) := (Nat.card_ne_zero.mp hcard0).2
    haveI := P.isPrime.isMaximal P.ne_bot
    have hCharP := ringChar.charP (𝓞 F ⧸ P.asIdeal)
    haveI := Ideal.Quotient.field P.asIdeal
    haveI := Fintype.ofFinite (𝓞 F ⧸ P.asIdeal)
    obtain ⟨f, hp, hcard⟩ := @FiniteField.card (𝓞 F ⧸ P.asIdeal)
      (Ideal.Quotient.field P.asIdeal) _
      (ringChar (𝓞 F ⧸ P.asIdeal)) hCharP
    simp only [Nat.card_eq_fintype_card] at hnp ⊢
    refine ⟨hp, ?_⟩
    rcases Nat.lt_or_ge (f : ℕ) 2 with hf | hf
    · exfalso
      have hf1 : (f : ℕ) = 1 := by have := f.pos; omega
      apply hnp
      rw [hcard, hf1, pow_one]
      exact hp
    · rw [hcard]
      exact Nat.pow_le_pow_right hp.pos hf
  -- termwise bound by the inverse square of the residue characteristic
  have hbound : ∀ P : {P : HeightOneSpectrum (𝓞 F) //
      ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
      (Nat.card (𝓞 F ⧸ P.1.asIdeal) : ℝ≥0∞) ^ (-(1 : ℝ)) ≤
        ((ringChar (𝓞 F ⧸ P.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ))⁻¹ := by
    intro P
    rw [ENNReal.rpow_neg_one]
    refine ENNReal.inv_le_inv' ?_
    calc (ringChar (𝓞 F ⧸ P.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ)
        = ((ringChar (𝓞 F ⧸ P.1.asIdeal) ^ 2 : ℕ) : ℝ≥0∞) := by push_cast; rfl
      _ ≤ (Nat.card (𝓞 F ⧸ P.1.asIdeal) : ℝ≥0∞) :=
          Nat.cast_le.mpr (hdata P).2
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  -- group by the residue characteristic
  rw [← ENNReal.tsum_fiberwise
    (fun P : {P : HeightOneSpectrum (𝓞 F) //
      ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
      ((ringChar (𝓞 F ⧸ P.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ))⁻¹)
    (fun P => ringChar (𝓞 F ⧸ P.1.asIdeal))]
  -- each fiber has at most `[F : ℚ]` elements, and vanishes off primes
  have hfiber : ∀ p : ℕ,
      (∑' P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
          ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}),
        ((ringChar (𝓞 F ⧸ P.1.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ))⁻¹) ≤
      (Module.finrank ℚ F : ℝ≥0∞) * ENNReal.ofReal (1 / (p : ℝ) ^ 2) := by
    intro p
    by_cases hp : p.Prime
    · -- inject the fiber into the primes over `p`
      set 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)} with h𝔭
      have h𝔭0 : 𝔭 ≠ ⊥ := by
        rw [h𝔭, Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero
      haveI h𝔭max : 𝔭.IsMaximal := by
        rw [h𝔭]
        exact PrincipalIdealRing.isMaximal_of_irreducible
          (Nat.prime_iff_prime_int.mp hp).irreducible
      have hmem : ∀ P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
          ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}),
          P.1.1.asIdeal ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F) := by
        intro P
        rw [IsDedekindDomain.mem_primesOverFinset_iff h𝔭0]
        refine ⟨P.1.1.isPrime, ⟨?_⟩⟩
        have hchar : ringChar (𝓞 F ⧸ P.1.1.asIdeal) = p := P.2
        have hle : 𝔭 ≤ P.1.1.asIdeal.under ℤ := by
          rw [h𝔭, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
            Ideal.under, Ideal.mem_comap]
          have hdvd : ringChar (𝓞 F ⧸ P.1.1.asIdeal) ∣ p := by
            rw [hchar]
          have h0 : ((p : ℕ) : 𝓞 F ⧸ P.1.1.asIdeal) = 0 :=
            (CharP.cast_eq_zero_iff _ (ringChar _) p).mpr hdvd
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          push_cast
          rw [map_natCast]
          exact h0
        have hne : P.1.1.asIdeal.under ℤ ≠ ⊤ := by
          intro htop
          apply P.1.1.isPrime.ne_top
          rw [Ideal.eq_top_iff_one] at htop ⊢
          have := Ideal.mem_comap.mp htop
          simpa using this
        exact h𝔭max.eq_of_le hne hle
      have hinj : Function.Injective
          (fun P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
            ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
            ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}) =>
            (⟨P.1.1.asIdeal, hmem P⟩ :
              {I : Ideal (𝓞 F) //
                I ∈ IsDedekindDomain.primesOverFinset 𝔭 (𝓞 F)})) := by
        intro P Q h
        exact Subtype.ext (Subtype.ext (HeightOneSpectrum.ext
          (congrArg Subtype.val h)))
      haveI : Finite ((fun P : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
          ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}) :=
        Finite.of_injective _ hinj
      calc (∑' P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
              ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
              ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}),
            ((ringChar (𝓞 F ⧸ P.1.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ))⁻¹)
          = ∑' _P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
              ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
              ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}),
            (((p : ℝ≥0∞)) ^ (2 : ℕ))⁻¹ :=
            tsum_congr fun P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
                ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
                ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}) => by
              rw [show ringChar (𝓞 F ⧸ P.1.1.asIdeal) = p from P.2]
        _ = ENat.card ((fun P : {P : HeightOneSpectrum (𝓞 F) //
              ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
              ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}) *
            (((p : ℝ≥0∞)) ^ (2 : ℕ))⁻¹ := ENNReal.tsum_const _
        _ ≤ (Module.finrank ℚ F : ℝ≥0∞) * (((p : ℝ≥0∞)) ^ (2 : ℕ))⁻¹ := by
            gcongr
            rw [ENat.card_eq_coe_natCard]
            have hcardle : Nat.card ((fun P : {P : HeightOneSpectrum (𝓞 F) //
                ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
                ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}) ≤
                Module.finrank ℚ F := by
              refine le_trans (Nat.card_le_card_of_injective _ hinj) ?_
              rw [Nat.card_eq_fintype_card, Fintype.card_coe]
              exact Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F h𝔭0
            exact_mod_cast hcardle
        _ = (Module.finrank ℚ F : ℝ≥0∞) * ENNReal.ofReal (1 / (p : ℝ) ^ 2) := by
            congr 1
            rw [ENNReal.ofReal_div_of_pos
                (by exact_mod_cast pow_pos hp.pos 2),
              ENNReal.ofReal_one, ENNReal.ofReal_pow (by positivity),
              ENNReal.ofReal_natCast, one_div]
    · -- the fiber over a non-prime is empty
      have hzero : ∀ P : ((fun P : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
          ringChar (𝓞 F ⧸ P.1.asIdeal)) ⁻¹' {p}),
          ((ringChar (𝓞 F ⧸ P.1.1.asIdeal) : ℝ≥0∞) ^ (2 : ℕ))⁻¹ = 0 :=
        fun P => (hp (P.2 ▸ (hdata P.1).1)).elim
      rw [ENNReal.tsum_eq_zero.mpr hzero]
      positivity
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hfiber)
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => by positivity) (Real.summable_one_div_nat_pow.mpr one_lt_two)]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top

open IsDedekindDomain in
/-- **Square-times-squarefree decomposition** (sorry leaf): every
nonzero ideal `I` of `𝓞 F` factors as `I = J ^ 2 * ∏_{P ∈ T} P.asIdeal`
with `J ≠ ⊥` and `T` a finite set of finite places (halve each exponent
in the prime factorization; `T` collects the odd exponents), and `I` is
recoverable from `(J, T)`, so `I ↦ (J, T)` is injective and
multiplicativity of `Ideal.absNorm` bounds the ideal sum by the product
of the square sum and the squarefree sum
(`ENNReal.tsum_comp_le_tsum_of_injective`, `ENNReal.tsum_prod`). -/
theorem tsum_rpow_neg_absNorm_le_mul_tsum_finset_prod
    (F : Type*) [Field F] [NumberField F] (s : ℝ) :
    ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) ≤
      (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-(2 * s))) *
        ∑' T : Finset (HeightOneSpectrum (𝓞 F)),
          ∏ P ∈ T, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s) := by
  classical
  -- every nonzero ideal is a square times a product of distinct primes
  have hdecomp : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → ∃ J : Ideal (𝓞 F),
      ∃ T : Finset (HeightOneSpectrum (𝓞 F)),
      J ≠ ⊥ ∧ I = J ^ 2 * ∏ P ∈ T, P.asIdeal := by
    intro I
    refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
    · exact fun h => absurd Submodule.zero_eq_bot h
    · intro x hx _
      refine ⟨⊤, ∅, top_ne_bot, ?_⟩
      rw [Ideal.isUnit_iff.mp hx]
      simp [← Ideal.one_eq_top]
    · intro a p ha hp IH _
      obtain ⟨J, T, hJ, hIJ⟩ := IH (by rw [← Submodule.zero_eq_bot]; exact ha)
      have hpbot : p ≠ ⊥ := by rw [← Submodule.zero_eq_bot]; exact hp.ne_zero
      set 𝔓 : HeightOneSpectrum (𝓞 F) :=
        ⟨p, Ideal.isPrime_of_prime hp, hpbot⟩
      by_cases hmem : 𝔓 ∈ T
      · refine ⟨p * J, T.erase 𝔓, ?_, ?_⟩
        · rw [← Submodule.zero_eq_bot]
          exact mul_ne_zero hp.ne_zero
            (by rw [Submodule.zero_eq_bot]; exact hJ)
        · rw [hIJ, ← Finset.mul_prod_erase T _ hmem,
            show 𝔓.asIdeal = p from rfl]
          ring
      · refine ⟨J, insert 𝔓 T, hJ, ?_⟩
        rw [hIJ, Finset.prod_insert hmem, show 𝔓.asIdeal = p from rfl]
        ring
  choose Jf Tf hJf hIJf using hdecomp
  -- the recoverable (hence injective) decomposition map
  have hφinj : Function.Injective
      (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
        ((⟨Jf I.1 I.2, hJf I.1 I.2⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥}),
          Tf I.1 I.2)) := by
    intro I I' h
    have h1 : Jf I.1 I.2 = Jf I'.1 I'.2 :=
      congrArg (fun q : {I : Ideal (𝓞 F) // I ≠ ⊥} ×
        Finset (HeightOneSpectrum (𝓞 F)) => q.1.1) h
    have h2 : Tf I.1 I.2 = Tf I'.1 I'.2 := congrArg Prod.snd h
    refine Subtype.ext ?_
    rw [hIJf I.1 I.2, hIJf I'.1 I'.2, h1, h2]
  -- the term factors along the decomposition
  have hterm : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) =
        (Ideal.absNorm (Jf I.1 I.2) : ℝ≥0∞) ^ (-(2 * s)) *
          ∏ P ∈ Tf I.1 I.2, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s) := by
    intro I
    have habs : (Ideal.absNorm I.1 : ℝ≥0∞) =
        (Ideal.absNorm (Jf I.1 I.2) : ℝ≥0∞) ^ (2 : ℕ) *
          ∏ P ∈ Tf I.1 I.2, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) := by
      have h1 : Ideal.absNorm I.1 =
          Ideal.absNorm (Jf I.1 I.2) ^ 2 *
            ∏ P ∈ Tf I.1 I.2, Ideal.absNorm P.asIdeal := by
        conv_lhs => rw [hIJf I.1 I.2]
        rw [map_mul, map_pow, map_prod]
      rw [h1]
      push_cast
      refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [habs, ENNReal.mul_rpow_of_ne_top
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.prod_lt_top fun P _ => ENNReal.natCast_lt_top _).ne,
      ENNReal.prod_rpow_of_ne_top fun P _ => ENNReal.natCast_ne_top _]
    congr 1
    rw [← ENNReal.rpow_natCast (Ideal.absNorm (Jf I.1 I.2) : ℝ≥0∞) 2,
      ← ENNReal.rpow_mul,
      show ((2 : ℕ) : ℝ) * (-s) = -(2 * s) by push_cast; ring]
  rw [tsum_congr hterm]
  refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective hφinj
    (fun q : {I : Ideal (𝓞 F) // I ≠ ⊥} ×
        Finset (HeightOneSpectrum (𝓞 F)) =>
      (Ideal.absNorm q.1.1 : ℝ≥0∞) ^ (-(2 * s)) *
        ∏ P ∈ q.2, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s))) ?_
  rw [ENNReal.tsum_prod']
  refine le_of_eq ?_
  calc ∑' (J : {I : Ideal (𝓞 F) // I ≠ ⊥})
        (T : Finset (HeightOneSpectrum (𝓞 F))),
        (Ideal.absNorm J.1 : ℝ≥0∞) ^ (-(2 * s)) *
          ∏ P ∈ T, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s)
      = ∑' J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (Ideal.absNorm J.1 : ℝ≥0∞) ^ (-(2 * s)) *
          ∑' T : Finset (HeightOneSpectrum (𝓞 F)),
            ∏ P ∈ T, (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s) :=
        tsum_congr fun J => ENNReal.tsum_mul_left
    _ = _ := ENNReal.tsum_mul_right

/-- The `n`-th term of the Dedekind-zeta `L`-series of `F` at real
`s > 0` is the real number `#{I : N(I) = n} · n ^ (-s)` (both sides
vanish at `n = 0`). -/
theorem term_natCard_absNorm_eq (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
        s n =
      (((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n),
      Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rw [div_eq_mul_inv]

/-- Real summability of the Dedekind-zeta Dirichlet series of `F` at
real `s > 1`: the ideal-counting asymptotics
(`Ideal.tendsto_norm_le_div_atTop₀`) make the partial sums of the
coefficients `O(n)`, so `LSeriesSummable_of_sum_norm_bigO_and_nonneg`
applies. -/
theorem summable_natCard_absNorm_mul_rpow_neg (F : Type*) [Field F]
    [NumberField F] {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s)) := by
  classical
  -- Cesàro behaviour of the coefficients, as in `NumberField.dedekindZeta`
  obtain ⟨c, hces⟩ : ∃ c : ℝ, Filter.Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / n)
      Filter.atTop (nhds c) := by
    refine ⟨_, ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp
      tendsto_natCast_atTop_atTop).congr fun n ↦ ?_⟩
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1,
      ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  -- hence the partial sums of the (nonnegative) coefficients are `O(n)`
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
    simp_rw [Real.rpow_one]
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c hces
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (Nat.cast_ne_zero.mpr hn)
  have hsum := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (s : ℂ)) hO
    (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  have hsum₂ : Summable (fun n : ℕ => LSeries.term
      (fun n => ((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) : ℂ))
      (s : ℂ) n) := hsum
  simp only [Complex.ofReal_natCast] at hsum₂
  rw [funext (term_natCard_absNorm_eq F (by linarith : (0 : ℝ) < s))] at hsum₂
  exact Complex.summable_ofReal.mp hsum₂

/-- **Fibration of the ideal sum over the norm**: the `ℝ≥0∞`-valued
Dirichlet series of the nonzero ideals of `𝓞 F` equals the series of
its norm-counting coefficients (the `n = 0` term vanishes on both
sides, so the sums may run over all ideals and all of `ℕ`). -/
theorem tsum_rpow_neg_absNorm_eq (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 0 < s) :
    ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) =
      ∑' n : ℕ, ENNReal.ofReal
        ((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
          (n : ℝ) ^ (-s)) := by
  classical
  -- each term is `ofReal` of the real term
  have hterm : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) =
        ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ) ^ (-s)) := by
    intro I
    have h1 : Ideal.absNorm I.1 ≠ 0 := fun h =>
      I.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have h0 : (0 : ℝ) < (Ideal.absNorm I.1 : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h1
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos h0]
  rw [tsum_congr hterm]
  -- extend to all ideals: the `⊥` term vanishes
  have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
      ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s))) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥} := by
    intro I hI
    rintro rfl
    apply hI
    simp [Ideal.absNorm_bot, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  rw [show ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ) ^ (-s)) =
      ∑' I : Ideal (𝓞 F), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) from
    tsum_subtype_eq_of_support_subset hsupp]
  -- fibre over the norm
  rw [← ENNReal.tsum_fiberwise (fun I : Ideal (𝓞 F) =>
    ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)))
    (fun I : Ideal (𝓞 F) => Ideal.absNorm I)]
  refine tsum_congr fun n => ?_
  haveI : Finite ↥((fun I : Ideal (𝓞 F) => Ideal.absNorm I) ⁻¹' {n}) :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  calc ∑' I : ((fun I : Ideal (𝓞 F) => Ideal.absNorm I) ⁻¹' {n}),
        ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ) ^ (-s))
      = ∑' _I : ((fun I : Ideal (𝓞 F) => Ideal.absNorm I) ⁻¹' {n}),
        ENNReal.ofReal ((n : ℝ) ^ (-s)) :=
        tsum_congr fun I => by rw [show Ideal.absNorm I.1 = n from I.2]
    _ = ENat.card ((fun I : Ideal (𝓞 F) => Ideal.absNorm I) ⁻¹' {n}) *
        ENNReal.ofReal ((n : ℝ) ^ (-s)) := ENNReal.tsum_const _
    _ = (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) ^ (-s)) := by
        rw [ENat.card_eq_coe_natCard,
          Nat.card_congr (Equiv.subtypeEquivRight
            (fun I : Ideal (𝓞 F) => Iff.rfl))]
        simp
    _ = ENNReal.ofReal
        ((Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
          (n : ℝ) ^ (-s)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Finiteness of the full ideal sum `∑_{I ≠ 0} N(I)^{-s}` for `s > 1`:
combine the fibration over the norm with the real summability of the
coefficient series. -/
theorem tsum_rpow_neg_absNorm_ne_top (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) ≠ ⊤ := by
  rw [tsum_rpow_neg_absNorm_eq F (by linarith : (0 : ℝ) < s),
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_natCard_absNorm_mul_rpow_neg F hs)]
  exact ENNReal.ofReal_ne_top

/-- The Dedekind zeta function at real `s > 1` is dominated by the real
Dirichlet series of its (nonnegative) coefficients. -/
theorem norm_dedekindZeta_le (F : Type*) [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) :
    ‖NumberField.dedekindZeta F s‖ ≤
      ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) := by
  have hpos : (0 : ℝ) < s := by linarith
  have hnorm : ∀ n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
      (s : ℂ) n‖ =
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) := by
    intro n
    rw [term_natCard_absNorm_eq F hpos n, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hsummable : Summable (fun n : ℕ => ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
      (s : ℂ) n‖) :=
    (summable_natCard_absNorm_mul_rpow_neg F hs).congr fun n => (hnorm n).symm
  rw [show NumberField.dedekindZeta F s = ∑' n : ℕ, LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
      (s : ℂ) n from rfl]
  exact le_trans (norm_tsum_le_tsum_norm hsummable) (le_of_eq (tsum_congr hnorm))

/-- **Divergence of the ideal sum as `s → 1⁺`**: the `ℝ≥0∞`-valued
Dirichlet series of the ideals of `𝓞 F` exceeds any `C ≠ ⊤` for some
`s > 1`: were it bounded by `C` for all `s > 1`, the product
`(s-1) · ζ_F(s)` would be squeezed to `0` along `𝓝[>] 1`
(`norm_dedekindZeta_le` and the fibration), contradicting the simple
pole with positive residue
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`,
`NumberField.dedekindZeta_residue_pos`). -/
theorem exists_one_lt_lt_tsum_rpow_neg_absNorm (F : Type*) [Field F]
    [NumberField F] (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ s : ℝ, 1 < s ∧
      C < ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s) := by
  by_contra hcon
  push Not at hcon
  -- the eventual bound `‖(t-1) ζ_F(t)‖ ≤ (t-1) C.toReal` near `1⁺`
  have hbound : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Ioi 1),
      ‖((t : ℂ) - 1) * NumberField.dedekindZeta F t‖ ≤ (t - 1) * C.toReal := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht1 : (1 : ℝ) < t := ht
    rw [norm_mul, show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine le_trans (norm_dedekindZeta_le F ht1) ?_
    have hZ := hcon t ht1
    rw [tsum_rpow_neg_absNorm_eq F (by linarith : (0 : ℝ) < t),
      ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_natCard_absNorm_mul_rpow_neg F ht1)] at hZ
    have hmono := ENNReal.toReal_mono hC hZ
    rwa [ENNReal.toReal_ofReal
      (tsum_nonneg fun n => by positivity)] at hmono
  -- the bounding function tends to `0`
  have h0 : Filter.Tendsto (fun t : ℝ => (t - 1) * C.toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (t - 1) * C.toReal) (nhds 1)
        (nhds ((1 - 1) * C.toReal)) :=
      (Filter.tendsto_id.sub tendsto_const_nhds).mul_const C.toReal
    rw [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  -- compare with the limit `‖κ‖`, forcing `κ ≤ 0` — contradiction
  have hnorm := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have hle : ‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hnorm h0 hbound
  rw [Complex.norm_real, Real.norm_of_nonneg
    (NumberField.dedekindZeta_residue_pos F).le] at hle
  exact absurd hle (not_le.mpr (NumberField.dedekindZeta_residue_pos F))

open IsDedekindDomain in
/-- **Divergence of the degree-one prime sum of a number field** (sorry
node) — the Dedekind-zeta half of Deuring's route: for a number field
`F` and any excluded residue characteristic `ℓ`, the `ℝ≥0∞`-valued sum
`∑ #(𝓞 F / P) ^ (-s)` over the finite places `P` of `F` with prime
residue cardinality (degree one over `ℚ`) different from `ℓ` exceeds
any `C ≠ ⊤` for some `s > 1`. No Galois theory, no congruence classes:
this is the statement that `log ζ_F(s) → ∞` as `s → 1⁺` is carried by
the degree-one primes.

DERIVED from the seven analytic auxiliaries above (see the section
docstring for the chain): were the degree-one sum bounded by `C`, the
full prime sum would be uniformly bounded by `C + B` for `1 < s` (tail
lemmas), hence the whole ideal sum would satisfy
`Z(s) ≤ Z(2) · exp-series(C + B) < ⊤` uniformly (square-times-squarefree
plus the exponential bound), contradicting `Z(s) → ∞` as `s → 1⁺` (the
simple pole of the Dedekind zeta function). -/
theorem exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ s : ℝ, 1 < s ∧ C < ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `1 ≤ #(𝓞 F / P)` for every finite place
  have hone : ∀ P : HeightOneSpectrum (𝓞 F),
      1 ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) := by
    intro P
    have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h =>
      P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  -- the full prime sum is uniformly bounded for `1 < s`
  have htail : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ s : ℝ, 1 < s →
      (∑' P : HeightOneSpectrum (𝓞 F),
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s)) ≤ C + B := by
    have hfinℓ := finite_setOf_natCard_quotient_eq F ℓ
    haveI : Finite ↥{P : HeightOneSpectrum (𝓞 F) |
        Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ} := hfinℓ.to_subtype
    haveI := Fintype.ofFinite ↥{P : HeightOneSpectrum (𝓞 F) |
        Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ}
    refine ⟨(∑' P : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
          (-(1 : ℝ))) +
        (Nat.card ↥{P : HeightOneSpectrum (𝓞 F) |
          Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ} : ℝ≥0∞),
      ENNReal.add_ne_top.mpr ⟨tsum_not_prime_natCard_rpow_neg_one_ne_top F,
        ENNReal.natCast_ne_top _⟩, fun s hs => ?_⟩
    rw [← ENNReal.summable.tsum_add_tsum_compl
      (s := {P : HeightOneSpectrum (𝓞 F) |
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ})
      ENNReal.summable]
    refine add_le_add (hcon s hs) ?_
    refine le_trans (ENNReal.tsum_mono_subtype
      (fun P : HeightOneSpectrum (𝓞 F) =>
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s))
      (t := {P : HeightOneSpectrum (𝓞 F) |
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} ∪
        {P : HeightOneSpectrum (𝓞 F) | Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ}) ?_) ?_
    · intro P hP
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_not] at hP
      by_cases hp : (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime
      · exact Or.inr (hP hp)
      · exact Or.inl hp
    refine le_trans (ENNReal.tsum_union_le
      (fun P : HeightOneSpectrum (𝓞 F) =>
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s)) _ _) (add_le_add ?_ ?_)
    · -- monotone in the exponent down to the fixed `s = 1` tail
      exact ENNReal.tsum_le_tsum fun P =>
        ENNReal.rpow_le_rpow_of_exponent_le (hone _) (by linarith)
    · -- finitely many places of residue cardinality `ℓ`, each term `≤ 1`
      calc ∑' P : {P : HeightOneSpectrum (𝓞 F) |
              Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ},
            (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
              (-s)
          = ∑ P : ↥{P : HeightOneSpectrum (𝓞 F) |
              Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ},
            (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
              (-s) := tsum_fintype _
        _ ≤ ∑ _P : ↥{P : HeightOneSpectrum (𝓞 F) |
              Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ}, (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun P _ =>
            ENNReal.rpow_le_one_of_one_le_of_neg (hone _) (by linarith)
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            Nat.card_eq_fintype_card]
  obtain ⟨B, hBne, hB⟩ := htail
  -- the whole ideal sum is then uniformly bounded for `1 < s`
  have hchain : ∀ s : ℝ, 1 < s →
      (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s)) ≤
        (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-(2 : ℝ))) *
          ∑' k : ℕ, (C + B) ^ k / (Nat.factorial k : ℝ≥0∞) := by
    intro s hs
    refine le_trans (tsum_rpow_neg_absNorm_le_mul_tsum_finset_prod F s)
      (mul_le_mul' ?_ ?_)
    · refine ENNReal.tsum_le_tsum fun I =>
        ENNReal.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have h0 : Ideal.absNorm I.1 ≠ 0 := fun h =>
        I.2 (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    · refine le_trans (tsum_finset_prod_le_tsum_pow_div_factorial _) ?_
      refine ENNReal.tsum_le_tsum fun k => ?_
      gcongr
      exact hB s hs
  -- contradiction with the divergence of the ideal sum as `s → 1⁺`
  obtain ⟨s, hs1, hslt⟩ := exists_one_lt_lt_tsum_rpow_neg_absNorm F
    ((∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
      (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-(2 : ℝ))) *
      ∑' k : ℕ, (C + B) ^ k / (Nat.factorial k : ℝ≥0∞))
    (ENNReal.mul_ne_top (tsum_rpow_neg_absNorm_ne_top F one_lt_two)
      (tsum_pow_div_factorial_ne_top (C + B)
        (ENNReal.add_ne_top.mpr ⟨hC, hBne⟩)))
  exact absurd (hchain s hs1) (not_le.mpr hslt)

/-- The Galois group of a Galois extension of number fields acts
faithfully on the ring of integers: two automorphisms agreeing on `𝓞 E`
agree on `E = Frac(𝓞 E)`. -/
instance {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E] :
    FaithfulSMul (E ≃ₐ[F] E) (𝓞 E) where
  eq_of_smul_eq_smul {σ τ} h := by
    refine AlgEquiv.ext fun e => ?_
    obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hcoe : ∀ (g : E ≃ₐ[F] E) (a : 𝓞 E),
        g (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E (g • a) := fun _ _ => rfl
    rw [map_div₀, map_div₀, hcoe σ x, hcoe σ y, hcoe τ x, hcoe τ y, h x, h y]

/-- The fixed points of the Galois action on `𝓞 E` are exactly the image
of `𝓞 F`, for a Galois extension `E/F` of number fields (general form of
the intermediate-field instance above). -/
instance {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] : Algebra.IsInvariant (𝓞 F) (𝓞 E) (E ≃ₐ[F] E) where
  isInvariant x hx := by
    have hfixE : ∀ e : E ≃ₐ[F] E, e • (x : E) = (x : E) := fun e =>
      congrArg (algebraMap (𝓞 E) E) (hx e)
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := F)
      (G := E ≃ₐ[F] E) (x : E) hfixE
    have hyint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hy]
      exact x.2
    exact ⟨⟨y, hyint⟩, NumberField.RingOfIntegers.ext hy⟩

/-- The Galois group of a Galois extension of number fields is a Galois
group for the extension of rings of integers (with respect to the ambient
project action on `𝓞 E`). -/
instance {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := inferInstance

open IsDedekindDomain in
/-- **Frobenius existence at degree-one primes, cyclotomic form**: for a
cyclotomic extension `E = F(ζ_ℓ)` of a number field `F` (`ℓ` prime) and
any finite place `P` of `F` with prime residue cardinality different
from `ℓ`, some `σ ∈ Gal(E/F)` acts on `ζ` by `ζ ↦ ζ ^ #(𝓞 F / P)`. This
is the "`#(𝓞 F / P) mod ℓ` lies in the image of `Gal(E/F)` in
`(ZMod ℓ)ˣ`" step of Deuring's route: at any prime `Q` of `𝓞 E` above
`P` an arithmetic Frobenius exists
(`IsArithFrobAt.exists_of_isInvariant`), and it acts on the `ℓ`-th root
of unity `ζ` exactly by `ζ ↦ ζ ^ #(𝓞 F / P)`
(`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`), because `ℓ` is invertible
modulo `Q` (`#(𝓞 F / P)` is a prime different from `ℓ`) — the same
argument as in the proof of `infinite_setOf_isArithFrobAt_zpowers`,
without the descent to a fixed field. -/
theorem exists_algEquiv_map_zeta_eq_pow_natCard
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (P : HeightOneSpectrum (𝓞 F))
    (hcard : (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime)
    (hne : Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ) :
    ∃ σ : E ≃ₐ[F] E, σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  haveI : IsGalois F E := IsCyclotomicExtension.isGalois {ℓ} F E
  haveI : FiniteDimensional F E := IsCyclotomicExtension.finiteDimensional {ℓ} F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  -- a prime of `𝓞 E` over `P`, with finite residue field
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) P.asIdeal
  haveI := hQp
  haveI := hQo
  have hQunder : Q.under (𝓞 F) = P.asIdeal := hQo.over.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [hQo.over, h, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  haveI : Finite (𝓞 E ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQne
  -- a Frobenius element at `Q` over `F`
  obtain ⟨σQ, hσQ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (𝓞 F) (E ≃ₐ[F] E) Q
  -- `ζ` as an algebraic integer
  have hζint : IsIntegral ℤ ζ := by
    refine IsIntegral.of_pow hℓ.pos ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  set ζO : 𝓞 E := ⟨ζ, hζint⟩
  -- `ℓ` is invertible modulo `Q`
  have hℓQ : ((ℓ : ℕ) : 𝓞 E) ∉ Q := by
    intro hmem
    have h1 : ((ℓ : ℕ) : 𝓞 F) ∈ P.asIdeal := by
      rw [← hQunder, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmem
    haveI : Finite (𝓞 F ⧸ P.asIdeal) :=
      Nat.finite_of_card_ne_zero hcard.ne_zero
    haveI := Fintype.ofFinite (𝓞 F ⧸ P.asIdeal)
    have h2 : ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : 𝓞 F ⧸ P.asIdeal) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    have h3 : ((ℓ : ℕ) : 𝓞 F ⧸ P.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal),
        Ideal.Quotient.eq_zero_iff_mem]
      exact h1
    have hco : IsCoprime (Nat.card (𝓞 F ⧸ P.asIdeal) : ℤ) (ℓ : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr
        (by
          rw [Int.gcd_natCast_natCast]
          exact (Nat.coprime_primes hcard hℓ).mpr hne)
    obtain ⟨u, v, huv⟩ := hco
    have h4 : (1 : 𝓞 F ⧸ P.asIdeal) = 0 := by
      calc (1 : 𝓞 F ⧸ P.asIdeal)
          = ((u * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℤ) + v * (ℓ : ℤ) : ℤ) :
            𝓞 F ⧸ P.asIdeal) := by rw [huv, Int.cast_one]
        _ = (u : 𝓞 F ⧸ P.asIdeal) *
              ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : 𝓞 F ⧸ P.asIdeal) +
            (v : 𝓞 F ⧸ P.asIdeal) * ((ℓ : ℕ) : 𝓞 F ⧸ P.asIdeal) := by
            rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
              Int.cast_natCast]
        _ = 0 := by rw [h2, h3, mul_zero, mul_zero, add_zero]
    exact one_ne_zero h4
  -- the Frobenius acts on `ζ` exactly by `ζ ↦ ζ ^ #(𝓞 F / P)`
  have hζOpow : ζO ^ ℓ = 1 := by
    apply NumberField.RingOfIntegers.ext
    show algebraMap (𝓞 E) E (ζO ^ ℓ) = algebraMap (𝓞 E) E 1
    rw [map_pow, map_one]
    show ζ ^ ℓ = 1
    exact hζ.pow_eq_one
  have hσQζ : σQ • ζO = ζO ^ Nat.card (𝓞 F ⧸ P.asIdeal) := by
    have h1 := hσQ.apply_of_pow_eq_one hζOpow hℓQ
    rw [hQunder] at h1
    exact h1
  refine ⟨σQ, ?_⟩
  have h2 : (algebraMap (𝓞 E) E) (σQ • ζO) =
      (algebraMap (𝓞 E) E) (ζO ^ Nat.card (𝓞 F ⧸ P.asIdeal)) :=
    congrArg _ hσQζ
  rw [map_pow] at h2
  have h3 : (algebraMap (𝓞 E) E) (σQ • ζO) = σQ ζ := rfl
  have h4 : (algebraMap (𝓞 E) E) ζO = ζ := rfl
  rw [h3, h4] at h2
  exact h2

open IsDedekindDomain in
/-- **Convergence of the degree-one prime sum for `s > 1`** — the easy,
Euler-side half of the summability bookkeeping: for a number field `F`
and any `s > 1`, the `ℝ≥0∞`-valued sum `∑ #(𝓞 F / P) ^ (-s)` over the
finite places `P` of `F` of prime residue cardinality (away from any
excluded `ℓ`) is finite. DERIVED from the full-ideal-sum leaf
`tsum_rpow_neg_absNorm_ne_top`: `P ↦ P.asIdeal` injects the degree-one
places into the nonzero ideals with matching terms
(`#(𝓞 F / P) = N(P.asIdeal)`), so the prime sum is dominated by the
ideal sum (`ENNReal.tsum_comp_le_tsum_of_injective`). -/
theorem tsum_rpow_neg_natCard_quotient_prime_and_ne_ne_top
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) {s : ℝ} (hs : 1 < s) :
    (∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (tsum_rpow_neg_absNorm_ne_top F hs) ?_
  have h1 : ∀ P : {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) =
      (Ideal.absNorm (P : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ≥0∞) ^ (-s) := by
    intro P
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [tsum_congr h1]
  exact ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} =>
      (⟨(P : HeightOneSpectrum (𝓞 F)).asIdeal,
        (P : HeightOneSpectrum (𝓞 F)).ne_bot⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥}))
    (fun P Q h =>
      Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))
    (fun I => (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s))

open IsDedekindDomain in
/-- Every finite place of a number field has residue cardinality at
least `2`: the quotient is a finite nontrivial ring. -/
theorem two_le_natCard_quotient {F : Type*} [Field F] [NumberField F]
    (P : HeightOneSpectrum (𝓞 F)) : 2 ≤ Nat.card (𝓞 F ⧸ P.asIdeal) := by
  haveI : Finite (𝓞 F ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  haveI : Nontrivial (𝓞 F ⧸ P.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
  exact Finite.one_lt_card

open IsDedekindDomain in
/-- Real summability of the full place sum `∑_P #(𝓞 F / P)^{-s}` for
real `s > 1`, transferred from the `ℝ≥0∞`-valued ideal-sum leaf
`tsum_rpow_neg_absNorm_ne_top` through the injection `P ↦ P.asIdeal`. -/
theorem summable_rpow_neg_natCard_quotient {F : Type*} [Field F] [NumberField F]
    {s : ℝ} (hs : 1 < s) : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) := by
  have h1 : ∀ P : HeightOneSpectrum (𝓞 F),
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s) =
        (Ideal.absNorm P.asIdeal : ℝ≥0∞) ^ (-s) := by
    intro P
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h2 : (∑' P : HeightOneSpectrum (𝓞 F),
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (tsum_rpow_neg_absNorm_ne_top F hs) ?_
    rw [tsum_congr h1]
    exact ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun P : HeightOneSpectrum (𝓞 F) =>
        (⟨P.asIdeal, P.ne_bot⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥}))
      (fun P Q h => HeightOneSpectrum.ext (congrArg Subtype.val h))
      (fun I => (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-s))
  have h3 : ∀ P : HeightOneSpectrum (𝓞 F),
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s) =
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : NNReal) ^ (-s) : NNReal) : ℝ≥0∞) := by
    intro P
    rw [ENNReal.coe_rpow_of_ne_zero (by
        have h4 := two_le_natCard_quotient P
        exact_mod_cast (by omega : Nat.card (𝓞 F ⧸ P.asIdeal) ≠ 0)),
      ENNReal.coe_natCast]
  rw [tsum_congr h3] at h2
  have h4 := ENNReal.tsum_coe_ne_top_iff_summable.mp h2
  refine (NNReal.summable_coe.mpr h4).congr ?_
  intro P
  rw [NNReal.coe_rpow, NNReal.coe_natCast]

open IsDedekindDomain in
/-- Every ideal of a Dedekind domain other than `⊥` and `⊤` is divisible
by some height-one prime: pick an irreducible factor in the unique
factorization monoid of ideals. -/
theorem exists_heightOneSpectrum_dvd {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    ∃ Q : HeightOneSpectrum R, Q.asIdeal ∣ I := by
  obtain ⟨i, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor
    (fun h => h1 (Ideal.isUnit_iff.mp h)) (by rwa [Ideal.zero_eq_bot])
  exact ⟨HeightOneSpectrum.ofPrime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr), hdvd⟩

open IsDedekindDomain in
/-- Uniqueness of the `P`-power decomposition `I = P^e · J` with `P ∤ J`
in the ideal monoid of a Dedekind domain. -/
theorem eq_and_eq_of_pow_mul_eq_pow_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P₀ : HeightOneSpectrum R) {e e' : ℕ} {J J' : Ideal R}
    (hJ : ¬P₀.asIdeal ∣ J) (hJ' : ¬P₀.asIdeal ∣ J')
    (h : P₀.asIdeal ^ e * J = P₀.asIdeal ^ e' * J') : e = e' ∧ J = J' := by
  have hPne : P₀.asIdeal ≠ 0 := by rw [Ideal.zero_eq_bot]; exact P₀.ne_bot
  have key : ∀ {a a' : ℕ} {B B' : Ideal R}, a ≤ a' → ¬P₀.asIdeal ∣ B →
      P₀.asIdeal ^ a * B = P₀.asIdeal ^ a' * B' → a = a' ∧ B = B' := by
    intro a a' B B' hle hB hEq
    have h1 : P₀.asIdeal ^ a * B = P₀.asIdeal ^ a * (P₀.asIdeal ^ (a' - a) * B') := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
      exact hEq
    have h2 : B = P₀.asIdeal ^ (a' - a) * B' :=
      mul_left_cancel₀ (pow_ne_zero a hPne) h1
    have h3 : a' - a = 0 := by
      by_contra h4
      apply hB
      rw [h2]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ h4) B'
    refine ⟨by omega, ?_⟩
    rw [h3, pow_zero, one_mul] at h2
    exact h2
  rcases le_total e e' with hle | hle
  · exact key hle hJ h
  · obtain ⟨h1, h2⟩ := key hle hJ' h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- Complete multiplicativity in the `ℕ`-argument of the twisted power
term `k ↦ χ(k)·k^{-w}` (for `w ≠ 0`; at `k = 0` both sides vanish). -/
theorem dirichletCharacter_mul_cpow_natCast_mul {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : w ≠ 0) (m n : ℕ) :
    χ ((m * n : ℕ) : ZMod ℓ) * ((m * n : ℕ) : ℂ) ^ (-w) =
      (χ (m : ZMod ℓ) * (m : ℂ) ^ (-w)) * (χ (n : ZMod ℓ) * (n : ℂ) ^ (-w)) := by
  have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.zero_mul, Nat.cast_zero, Complex.zero_cpow hw']
    ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.mul_zero, Nat.cast_zero, Complex.zero_cpow hw']
    ring
  have hcast : ((m * n : ℕ) : ℂ) = ((m : ℝ) : ℂ) * ((n : ℝ) : ℂ) := by
    push_cast
    ring
  have hcpow : ((m * n : ℕ) : ℂ) ^ (-w) = (m : ℂ) ^ (-w) * (n : ℂ) ^ (-w) := by
    rw [hcast,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    norm_cast
  rw [Nat.cast_mul, map_mul, hcpow]
  ring

/-- Iterated form of `dirichletCharacter_mul_cpow_natCast_mul`: the
twisted power term at `m ^ e * n` splits off the `e`-th power of the
term at `m`. -/
theorem dirichletCharacter_mul_cpow_natCast_pow_mul {ℓ : ℕ}
    (χ : DirichletCharacter ℂ ℓ) {w : ℂ} (hw : w ≠ 0) (m n e : ℕ) :
    χ ((m ^ e * n : ℕ) : ZMod ℓ) * ((m ^ e * n : ℕ) : ℂ) ^ (-w) =
      (χ (m : ZMod ℓ) * (m : ℂ) ^ (-w)) ^ e *
        (χ (n : ZMod ℓ) * (n : ℂ) ^ (-w)) := by
  induction e with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ e ih =>
      have h1 : m ^ (e + 1) * n = m * (m ^ e * n) := by ring
      rw [h1, dirichletCharacter_mul_cpow_natCast_mul χ hw m (m ^ e * n), ih,
        pow_succ]
      ring

open IsDedekindDomain in
/-- Norm summability of the twisted ideal sum for `1 < re w`,
transferred from the `ℝ≥0∞`-valued full-ideal-sum leaf
`tsum_rpow_neg_absNorm_ne_top`. -/
theorem summable_norm_dirichletCharacter_mul_cpow_neg_absNorm
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : 1 < w.re) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      ‖χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w)‖) := by
  have habs : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-w.re)) := by
    have h2 := tsum_rpow_neg_absNorm_ne_top F hw
    have h3 : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-w.re) =
          (((Ideal.absNorm I.1 : NNReal) ^ (-w.re) : NNReal) : ℝ≥0∞) := by
      intro I
      rw [ENNReal.coe_rpow_of_ne_zero (by
          exact_mod_cast (fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h) :
            Ideal.absNorm I.1 ≠ 0)),
        ENNReal.coe_natCast]
    rw [tsum_congr h3] at h2
    have h4 := ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    refine (NNReal.summable_coe.mpr h4).congr ?_
    intro I
    rw [NNReal.coe_rpow, NNReal.coe_natCast]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_) habs
  have hNpos : 0 < Ideal.absNorm I.1 :=
    Nat.pos_of_ne_zero fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (DirichletCharacter.norm_le_one χ _)

open IsDedekindDomain in
/-- **Finite-level Euler product over the ideals of `𝓞 F`**: for a
finite set `S` of finite places, the product of the inverted Euler
factors at the places in `S` equals the twisted ideal sum restricted to
the ideals all of whose prime divisors lie in `S`. This is the
ideal-monoid mirror of mathlib's
`EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers`,
proven by induction on `S` along the unique `P`-power decomposition of
the `S`-factored ideals. -/
theorem prod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum_factored
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : 1 < w.re) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (∏ P ∈ S, (1 - χ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod ℓ) *
        (Ideal.absNorm P.asIdeal : ℂ) ^ (-w))⁻¹) =
      ∑' I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
          ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
        χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1.1 : ℂ) ^ (-w) := by
  classical
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; linarith
  have hTop : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by
    intro h
    exact one_ne_zero (Ideal.mem_bot.mp (h ▸ Submodule.mem_top (x := (1 : 𝓞 F))))
  induction S using Finset.induction_on with
  | empty =>
      have hset : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
          ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 →
            Q ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} =
          {(⟨⊤, hTop⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥})} := by
        ext I
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hI
          by_contra hne
          have hItop : I.1 ≠ ⊤ := fun h => hne (Subtype.ext h)
          obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_dvd I.2 hItop
          exact absurd (hI Q hQ) (Finset.notMem_empty Q)
        · rintro rfl Q hQ
          exact absurd (top_le_iff.mp (Ideal.le_of_dvd hQ)) Q.isPrime.ne_top
      rw [Finset.prod_empty, hset,
        tsum_singleton (⟨⊤, hTop⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥})
          (fun J => χ ((Ideal.absNorm J.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm J.1 : ℂ) ^ (-w))]
      simp [Ideal.absNorm_top, Complex.one_cpow]
  | @insert P₀ S hP₀ ih =>
      -- the Euler factor at `P₀` has norm `< 1`
      have hN2 : 2 ≤ Ideal.absNorm P₀.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        exact two_le_natCard_quotient P₀
      have hnormlt : ‖χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
          (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)‖ < 1 := by
        have hNpos : 0 < Ideal.absNorm P₀.asIdeal := by omega
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
        calc ‖χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ)‖ *
              (Ideal.absNorm P₀.asIdeal : ℝ) ^ (-w.re)
            ≤ (Ideal.absNorm P₀.asIdeal : ℝ) ^ (-w.re) :=
              mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
                (DirichletCharacter.norm_le_one χ _)
          _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg
              (by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hN2)
              (by linarith)
      have hPne0 : P₀.asIdeal ≠ 0 := fun h => P₀.ne_bot (h.trans Ideal.zero_eq_bot)
      have hPnotdvdmem : ∀ J : {I : Ideal (𝓞 F) // I ≠ ⊥},
          (∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ J.1 → Q ∈ S) →
          ¬P₀.asIdeal ∣ J.1 := fun J hJ hdvd => hP₀ (hJ P₀ hdvd)
      -- the unique `P₀`-power decomposition of the `insert P₀ S`-factored ideals
      have hmapmem : ∀ (e : ℕ) (J : {I : Ideal (𝓞 F) // I ≠ ⊥}),
          (∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ J.1 → Q ∈ S) →
          (P₀.asIdeal ^ e * J.1 ≠ ⊥ ∧
            ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ P₀.asIdeal ^ e * J.1 →
              Q ∈ insert P₀ S) := by
        intro e J hJ
        constructor
        · exact fun h => mul_ne_zero (pow_ne_zero e hPne0)
            (fun hh => J.2 (hh.trans Ideal.zero_eq_bot))
            (h.trans Ideal.zero_eq_bot.symm)
        · intro Q hQ
          rcases (Q.prime.dvd_mul).mp hQ with h | h
          · have hQP : Q.asIdeal ∣ P₀.asIdeal := Q.prime.dvd_of_dvd_pow h
            have hle : P₀.asIdeal ≤ Q.asIdeal := Ideal.le_of_dvd hQP
            have hQeq : Q = P₀ := HeightOneSpectrum.ext
              (P₀.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm
            rw [hQeq]
            exact Finset.mem_insert_self P₀ S
          · exact Finset.mem_insert_of_mem (hJ Q h)
      let f : ℕ × ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
          ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S} →
          ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
            ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ insert P₀ S} :=
        fun p => ⟨⟨P₀.asIdeal ^ p.1 * p.2.1.1, (hmapmem p.1 p.2.1 p.2.2).1⟩,
          (hmapmem p.1 p.2.1 p.2.2).2⟩
      have hbij : Function.Bijective f := by
        constructor
        · rintro ⟨e, J⟩ ⟨e', J'⟩ hEq
          have h1 : P₀.asIdeal ^ e * J.1.1 = P₀.asIdeal ^ e' * J'.1.1 :=
            congrArg (fun x => x.1.1) hEq
          obtain ⟨h2, h3⟩ := eq_and_eq_of_pow_mul_eq_pow_mul P₀
            (hPnotdvdmem J.1 J.2) (hPnotdvdmem J'.1 J'.2) h1
          exact Prod.ext h2 (Subtype.ext (Subtype.ext h3))
        · rintro ⟨⟨I, hI0⟩, hImem⟩
          obtain ⟨e, J, hJdvd, hIeq⟩ := WfDvdMonoid.max_power_factor
            (fun h => hI0 (h.trans Ideal.zero_eq_bot)) P₀.irreducible
          have hJ0 : J ≠ ⊥ := by
            intro h
            apply hI0
            rw [hIeq, h, Ideal.mul_bot]
          have hJmem : ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ J → Q ∈ S := by
            intro Q hQ
            have hQI : Q.asIdeal ∣ I := by
              rw [hIeq]
              exact hQ.mul_left _
            rcases Finset.mem_insert.mp (hImem Q hQI) with h | h
            · rw [h] at hQ
              exact absurd hQ hJdvd
            · exact h
          exact ⟨⟨e, ⟨⟨J, hJ0⟩, hJmem⟩⟩, Subtype.ext (Subtype.ext hIeq.symm)⟩
      -- the twisted term is completely multiplicative along the decomposition
      have hgf : ∀ p : ℕ × ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
          ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
          χ ((Ideal.absNorm (f p).1.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm (f p).1.1 : ℂ) ^ (-w) =
          (χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
            (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)) ^ p.1 *
          (χ ((Ideal.absNorm p.2.1.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm p.2.1.1 : ℂ) ^ (-w)) := by
        rintro ⟨e, J⟩
        show χ ((Ideal.absNorm (P₀.asIdeal ^ e * J.1.1) : ℕ) : ZMod ℓ) *
            (Ideal.absNorm (P₀.asIdeal ^ e * J.1.1) : ℂ) ^ (-w) = _
        rw [map_mul, map_pow]
        exact dirichletCharacter_mul_cpow_natCast_pow_mul χ hw0 _ _ e
      -- summability inputs for the product of the two series
      have hgeom : Summable (fun e : ℕ =>
          ‖(χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
            (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)) ^ e‖) :=
        (summable_geometric_of_lt_one (norm_nonneg _) hnormlt).congr
          fun e => (norm_pow _ _).symm
      have hsubnorm : Summable (fun I : ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
          ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S} =>
          ‖χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm I.1.1 : ℂ) ^ (-w)‖) :=
        (summable_norm_dirichletCharacter_mul_cpow_neg_absNorm F χ hw).subtype _
      -- the insert-step reindexing along the decomposition
      have hstep : (∑' I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
            ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ insert P₀ S},
          χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm I.1.1 : ℂ) ^ (-w)) =
          (∑' e : ℕ, (χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
            (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)) ^ e) *
          ∑' I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
            ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
          χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) *
            (Ideal.absNorm I.1.1 : ℂ) ^ (-w) := by
        calc (∑' I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
              ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ insert P₀ S},
            χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) *
              (Ideal.absNorm I.1.1 : ℂ) ^ (-w))
            = ∑' p : ℕ × ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
                ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
              χ ((Ideal.absNorm (f p).1.1 : ℕ) : ZMod ℓ) *
                (Ideal.absNorm (f p).1.1 : ℂ) ^ (-w) :=
              ((Equiv.ofBijective f hbij).tsum_eq _).symm
          _ = ∑' p : ℕ × ↥{I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
                ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
              (χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
                (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)) ^ p.1 *
              (χ ((Ideal.absNorm p.2.1.1 : ℕ) : ZMod ℓ) *
                (Ideal.absNorm p.2.1.1 : ℂ) ^ (-w)) := tsum_congr hgf
          _ = (∑' e : ℕ, (χ ((Ideal.absNorm P₀.asIdeal : ℕ) : ZMod ℓ) *
                (Ideal.absNorm P₀.asIdeal : ℂ) ^ (-w)) ^ e) *
              ∑' I : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
                ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S},
              χ ((Ideal.absNorm I.1.1 : ℕ) : ZMod ℓ) *
                (Ideal.absNorm I.1.1 : ℂ) ^ (-w) :=
              (tsum_mul_tsum_of_summable_norm hgeom hsubnorm).symm
      rw [Finset.prod_insert hP₀, ih, ← tsum_geometric_of_norm_lt_one hnormlt]
      exact hstep.symm

open IsDedekindDomain in
/-- **Euler product for the `χ`-twisted Dedekind zeta function**: for
`1 < re w`, the product of the inverted Euler factors
`(1 - χ(N P)·N P^{-w})⁻¹` over the finite places of `F` equals the
absolutely convergent sum of `χ(N I)·N I^{-w}` over the nonzero ideals
of `𝓞 F`. Pure unique factorization — no counting asymptotics, no
nonvanishing. PROVEN, mirroring mathlib's
`EulerProduct.eulerProduct_hasProd` (stated there only for `ℕ`) with
`Ideal (𝓞 F)` in place of `ℕ`: the finite-level identity
`prod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum_factored`
expands a partial product over a finite set `S` of places as the
twisted sum over the `S`-factored ideals (geometric series for each
factor, then the unique `P`-power decomposition
`eq_and_eq_of_pow_mul_eq_pow_mul` and complete multiplicativity
`dirichletCharacter_mul_cpow_natCast_pow_mul` along `Ideal.absNorm`),
and the difference from the full ideal sum is killed along the net of
finite `S` by `Summable.tsum_vanishing` for the absolutely convergent
twisted ideal sum
(`summable_norm_dirichletCharacter_mul_cpow_neg_absNorm`, from the
full-ideal-sum leaf `tsum_rpow_neg_absNorm_ne_top`). -/
theorem tprod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : 1 < w.re) :
    (∏' P : HeightOneSpectrum (𝓞 F),
        (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))⁻¹) =
      ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w) := by
  classical
  -- replace the residue cardinalities by absolute norms in the factors
  have hfac : ∀ P : HeightOneSpectrum (𝓞 F),
      (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))⁻¹ =
      (1 - χ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod ℓ) *
        (Ideal.absNorm P.asIdeal : ℂ) ^ (-w))⁻¹ := by
    intro P
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [tprod_congr hfac]
  -- the twisted ideal sum is (absolutely) summable
  have hsummable : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w)) :=
    (summable_norm_dirichletCharacter_mul_cpow_neg_absNorm F χ hw).of_norm
  -- `HasProd` towards the full twisted ideal sum
  refine HasProd.tprod_eq ?_
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  -- tail control: a finite set of ideals capturing the sum up to `ε`
  obtain ⟨T₀, hT₀⟩ := hsummable.tsum_vanishing (Metric.ball_mem_nhds 0 hε)
  refine ⟨T₀.biUnion (fun I =>
    (Ideal.finite_factors (fun h => I.2 (h.trans Ideal.zero_eq_bot))).toFinset),
    fun S hS => ?_⟩
  -- every ideal in `T₀` is `S`-factored
  have hT₀sub : ∀ I ∈ T₀, ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S := by
    intro I hI Q hQ
    refine hS (Finset.mem_biUnion.mpr ⟨I, hI, ?_⟩)
    rw [Set.Finite.mem_toFinset]
    exact hQ
  -- hence the complement of the `S`-factored ideals is disjoint from `T₀`
  have hdisj : Disjoint ({I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
      ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S}ᶜ) (↑T₀ : Set _) := by
    rw [Set.disjoint_left]
    intro I hIc hIT
    exact hIc (fun Q hQ => hT₀sub I hIT Q hQ)
  have htail := hT₀ _ hdisj
  rw [mem_ball_zero_iff] at htail
  -- split the full sum along the `S`-factored ideals
  have hkey := hsummable.tsum_subtype_add_tsum_subtype_compl
    {I : {I : Ideal (𝓞 F) // I ≠ ⊥} |
      ∀ Q : HeightOneSpectrum (𝓞 F), Q.asIdeal ∣ I.1 → Q ∈ S}
  have hprodS := prod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum_factored
    F χ hw S
  rw [dist_eq_norm, hprodS, ← hkey, sub_add_cancel_left, norm_neg]
  exact htail

open IsDedekindDomain in
/-- **Norm fibration of the twisted ideal sum**: grouping
the nonzero ideals of `𝓞 F` along `Ideal.absNorm` turns the twisted
ideal sum into the `L`-series of `k ↦ χ(k)·#{I : N(I) = k}`. PROVEN:
`Equiv.sigmaFiberEquiv` and `Summable.tsum_sigma'` fibre the sum
over `k = N(I)`; each fibre is finite (`Ideal.finite_setOf_absNorm_eq`)
with summand `χ(k)·k^{-w}` constant on the fibre, so its sum is
`#{I : N(I) = k} · χ(k)·k^{-w} = LSeries.term _ w k` (the `k = 0` fibre
is empty on nonzero ideals by `Ideal.absNorm_eq_zero_iff`; absolute
convergence for `1 < re w` from `tsum_rpow_neg_absNorm_ne_top`). -/
theorem tsum_dirichletCharacter_mul_cpow_neg_absNorm_eq_LSeries
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : 1 < w.re) :
    (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w)) =
      LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) w := by
  classical
  set G : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun I =>
    χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w) with hGdef
  -- summability of the twisted ideal sum (transfer from the `ℝ≥0∞` leaf)
  have habs : Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-w.re)) := by
    have h2 := tsum_rpow_neg_absNorm_ne_top F hw
    have h3 : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥},
        (Ideal.absNorm I.1 : ℝ≥0∞) ^ (-w.re) =
          (((Ideal.absNorm I.1 : NNReal) ^ (-w.re) : NNReal) : ℝ≥0∞) := by
      intro I
      rw [ENNReal.coe_rpow_of_ne_zero (by
          exact_mod_cast (fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h) :
            Ideal.absNorm I.1 ≠ 0)),
        ENNReal.coe_natCast]
    rw [tsum_congr h3] at h2
    have h4 := ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    refine (NNReal.summable_coe.mpr h4).congr ?_
    intro I
    rw [NNReal.coe_rpow, NNReal.coe_natCast]
  have hsum : Summable G := by
    refine Summable.of_norm_bounded habs ?_
    intro I
    have hNpos : 0 < Ideal.absNorm I.1 :=
      Nat.pos_of_ne_zero fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h)
    rw [hGdef, norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (DirichletCharacter.norm_le_one χ _)
  -- all norm fibres are finite
  have hfibfin : ∀ k : ℕ, Finite {c : {I : Ideal (𝓞 F) // I ≠ ⊥} //
      Ideal.absNorm c.1 = k} := by
    intro k
    haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = k} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) k).to_subtype
    refine Finite.of_injective
      (fun c => (⟨c.1.1, c.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = k}))
      fun a b h => ?_
    have h2 : a.1.1 = b.1.1 := by
      have h3 := congrArg Subtype.val h
      simpa using h3
    exact Subtype.ext (Subtype.ext h2)
  -- reindex along the fibres of the absolute norm
  calc (∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, G I)
      = ∑' σ : (Σ k : ℕ, {I : {I : Ideal (𝓞 F) // I ≠ ⊥} //
          Ideal.absNorm I.1 = k}),
        G ((Equiv.sigmaFiberEquiv
          (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1)) σ) :=
      ((Equiv.sigmaFiberEquiv _).tsum_eq G).symm
    _ = ∑' k : ℕ, ∑' c : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} //
          Ideal.absNorm I.1 = k},
        G ((Equiv.sigmaFiberEquiv
          (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1)) ⟨k, c⟩) := by
      refine Summable.tsum_sigma' (fun k => ?_) ?_
      · haveI := hfibfin k
        exact Summable.of_finite
      · exact hsum.comp_injective (Equiv.sigmaFiberEquiv _).injective
    _ = ∑' k : ℕ, LSeries.term (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) w k := by
      refine tsum_congr fun k => ?_
      have hconst : ∀ c : {I : {I : Ideal (𝓞 F) // I ≠ ⊥} //
          Ideal.absNorm I.1 = k},
          G ((Equiv.sigmaFiberEquiv
            (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => Ideal.absNorm I.1)) ⟨k, c⟩) =
          χ (k : ZMod ℓ) * (k : ℂ) ^ (-w) := by
        intro c
        show χ ((Ideal.absNorm (c : {I : Ideal (𝓞 F) // I ≠ ⊥}).1 : ℕ) : ZMod ℓ) *
          (Ideal.absNorm (c : {I : Ideal (𝓞 F) // I ≠ ⊥}).1 : ℂ) ^ (-w) = _
        rw [show Ideal.absNorm (c : {I : Ideal (𝓞 F) // I ≠ ⊥}).1 = k from c.2]
      rw [tsum_congr hconst]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · haveI : IsEmpty {c : {I : Ideal (𝓞 F) // I ≠ ⊥} //
            Ideal.absNorm c.1 = 0} :=
          ⟨fun c => c.1.2 (Ideal.absNorm_eq_zero_iff.mp c.2)⟩
        rw [tsum_empty, LSeries.term_zero]
      · haveI := hfibfin k
        haveI := Fintype.ofFinite {c : {I : Ideal (𝓞 F) // I ≠ ⊥} //
          Ideal.absNorm c.1 = k}
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
          LSeries.term_of_ne_zero hk.ne']
        have hcard : Fintype.card {c : {I : Ideal (𝓞 F) // I ≠ ⊥} //
            Ideal.absNorm c.1 = k} =
            Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} := by
          rw [← Nat.card_eq_fintype_card]
          exact Nat.card_congr
            ⟨fun c => ⟨c.1.1, c.2⟩,
             fun I => ⟨⟨I.1, fun h =>
               hk.ne' (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩,
             fun c => rfl, fun I => rfl⟩
        rw [hcard, nsmul_eq_mul, Complex.cpow_neg]
        ring
    _ = LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) w := rfl

open IsDedekindDomain in
/-- **Euler product for the `χ`-twisted Dedekind zeta function, in
exponential form**: for a number field `F`, a Dirichlet
character `χ mod ℓ` with values in `ℂ`, and complex `w` with
`1 < re w`, the exponential of the prime log-sum
`∑_P -log(1 - χ(N P) · N P ^ (-w))` over ALL finite places of `F`
equals the `L`-series of the coefficient function
`k ↦ χ(k) · #{I : N(I) = k}` (the `χ`-twisted ideal Dirichlet series;
same coefficient shape as `NumberField.dedekindZeta`).

DERIVED from the two strictly shallower sorried leaves above: each
factor is away from `0` and off the branch cut (`‖χ(N P) N P^{-w}‖ ≤
N P^{-re w} ≤ 1/2`), so `Complex.log_inv` and
`Complex.cexp_tsum_eq_tprod` (with the `3/2·N P^{-re w}` log bound and
`summable_rpow_neg_natCard_quotient`) turn the left side into
`∏_P (1 - χ(N P) N P^{-w})⁻¹`; the Euler-product leaf
`tprod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum` identifies
the product with the twisted ideal sum, and the fibration leaf
`tsum_dirichletCharacter_mul_cpow_neg_absNorm_eq_LSeries` regroups it
along `Ideal.absNorm` into the right side. -/
theorem exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {w : ℂ} (hw : 1 < w.re) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 F),
        -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))) =
      LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) w := by
  classical
  -- factor norms: `‖χ(N P)·N P^{-w}‖ ≤ N P^{-re w} ≤ 1/2`
  have hzb : ∀ P : HeightOneSpectrum (𝓞 F),
      ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ ≤
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-w.re) := by
    intro P
    have hNpos : 0 < Nat.card (𝓞 F ⧸ P.asIdeal) := by
      have h := two_le_natCard_quotient P
      omega
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (DirichletCharacter.norm_le_one χ _)
  have hb : ∀ P : HeightOneSpectrum (𝓞 F),
      ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ ≤ 1 / 2 := by
    intro P
    refine le_trans (hzb P) ?_
    have h2N : (2 : ℝ) ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
      exact_mod_cast two_le_natCard_quotient P
    calc (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-w.re)
        ≤ (2 : ℝ) ^ (-w.re) :=
          Real.rpow_le_rpow_of_nonpos two_pos h2N (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          (Real.rpow_le_rpow_left_iff one_lt_two).mpr (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  -- the factors are nonzero and have positive real part
  have hne : ∀ P : HeightOneSpectrum (𝓞 F),
      (1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w) ≠ 0 := by
    intro P h0
    have h1 := sub_eq_zero.mp h0
    have h2 := hb P
    rw [← h1, norm_one] at h2
    norm_num at h2
  have hre : ∀ P : HeightOneSpectrum (𝓞 F),
      0 < ((1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)).re := by
    intro P
    have h7 := le_trans (Complex.abs_re_le_norm _) (hb P)
    have h8 : ((1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)).re =
        1 - (χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)).re := by
      simp [Complex.sub_re, Complex.one_re]
    rw [h8]
    have h9 := abs_le.mp h7
    linarith [h9.2]
  -- inverting the factors negates the logs
  have hloginv : ∀ P : HeightOneSpectrum (𝓞 F),
      Complex.log (((1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))⁻¹) =
      -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)) := by
    intro P
    refine Complex.log_inv _ ?_
    intro harg
    have h10 := Complex.arg_eq_pi_iff.mp harg
    linarith [hre P, h10.1]
  -- summability of the negated logs
  have hlogsum : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))) := by
    refine Summable.of_norm_bounded
      ((summable_rpow_neg_natCard_quotient hw).mul_left (3 / 2 : ℝ)) ?_
    intro P
    rw [norm_neg]
    have h6 : ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖ ≤ 1 / 2 := by
      rw [norm_neg]
      exact hb P
    calc ‖Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖
        = ‖Complex.log (1 + -(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)))‖ := by
          rw [sub_eq_add_neg]
      _ ≤ 3 / 2 * ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖ :=
          Complex.norm_log_one_add_half_le_self h6
      _ = 3 / 2 * ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ := by rw [norm_neg]
      _ ≤ 3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-w.re) :=
          mul_le_mul_of_nonneg_left (hzb P) (by norm_num)
  -- assemble: exp-log, Euler product, norm fibration
  calc Complex.exp (∑' P : HeightOneSpectrum (𝓞 F),
        -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)))
      = Complex.exp (∑' P : HeightOneSpectrum (𝓞 F),
          Complex.log (((1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))⁻¹)) := by
        rw [tsum_congr hloginv]
    _ = ∏' P : HeightOneSpectrum (𝓞 F),
          ((1 : ℂ) - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))⁻¹ :=
        Complex.cexp_tsum_eq_tprod (fun P => inv_ne_zero (hne P))
          (hlogsum.congr fun P => (hloginv P).symm)
    _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
          χ ((Ideal.absNorm I.1 : ℕ) : ZMod ℓ) * (Ideal.absNorm I.1 : ℂ) ^ (-w) :=
        tprod_one_sub_dirichletCharacter_mul_cpow_neg_inv_eq_tsum F χ hw
    _ = LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) w :=
        tsum_dirichletCharacter_mul_cpow_neg_absNorm_eq_LSeries F χ hw

open Filter Asymptotics in
/-- **Linear growth of the ideal-count coefficient sums**: the partial
sums of `k ↦ #{I : N(I) = k}` are `O(n)`. Derived from mathlib's
equidistribution-free ideal counting
`NumberField.Ideal.tendsto_norm_le_div_atTop` (the count of ideals of
norm `≤ s` is `∼ κ·s`), by fibering the count over the norm. -/
theorem sum_card_absNorm_isBigO (F : Type*) [Field F] [NumberField F] :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  classical
  -- pointwise domination by the count of ideals of norm at most `n`
  have hle : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ) ≤
      (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ) := by
    intro n
    haveI hfin : ∀ k : ℕ, Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = k} :=
      fun k => (Ideal.finite_setOf_absNorm_eq k).to_subtype
    haveI hfin2 : Finite {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} := by
      have hset : {I : Ideal (𝓞 F) | (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} =
          {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n} := by
        ext I
        simp only [Set.mem_setOf_eq]
        exact Nat.cast_le
      have hf : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ n}.Finite :=
        Ideal.finite_setOf_absNorm_le n
      rw [← hset] at hf
      exact hf.to_subtype
    rw [← Nat.cast_sum]
    refine Nat.cast_le.mpr ?_
    -- reindex the sum as the cardinality of a sigma type
    have hsum : ∑ k ∈ Finset.Icc 1 n,
        Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} =
        Nat.card (Σ k : ↥(Finset.Icc 1 n),
          {I : Ideal (𝓞 F) // Ideal.absNorm I = (k : ℕ)}) := by
      rw [Nat.card_sigma, ← Finset.sum_coe_sort]
    rw [hsum]
    -- and inject it into the ideals of norm at most `n`
    have hmem : ∀ p : (Σ k : ↥(Finset.Icc 1 n),
        {I : Ideal (𝓞 F) // Ideal.absNorm I = (k : ℕ)}),
        (Ideal.absNorm p.2.1 : ℝ) ≤ (n : ℝ) := by
      intro p
      rw [p.2.2]
      exact_mod_cast (Finset.mem_Icc.mp p.1.2).2
    refine Nat.card_le_card_of_injective (fun p => ⟨p.2.1, hmem p⟩) ?_
    rintro ⟨⟨k, hk⟩, ⟨I, hI⟩⟩ ⟨⟨k', hk'⟩, ⟨I', hI'⟩⟩ h
    have hII : I = I' := congrArg Subtype.val h
    subst hII
    have hkk : k = k' := by
      rw [← show Ideal.absNorm I = k from hI, ← show Ideal.absNorm I = k' from hI']
    subst hkk
    rfl
  -- the ideal count is `O(s)` by the counting asymptotics
  have h2 : (fun s : ℝ =>
      (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ)) =O[atTop]
      (fun s : ℝ => s) := by
    have h5 : (fun s : ℝ =>
        ((Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s) * s)
        =O[atTop] (fun s : ℝ => (1 : ℝ) * s) :=
      ((NumberField.Ideal.tendsto_norm_le_div_atTop F).isBigO_one (F := ℝ)).mul
        (isBigO_refl _ _)
    have h4 : (fun s : ℝ =>
        ((Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ) / s) * s)
        =ᶠ[atTop] (fun s : ℝ =>
          (Nat.card {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ s} : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      rw [div_mul_cancel₀ _ hs.ne']
    exact h5.congr' h4 (Filter.Eventually.of_forall fun s => one_mul s)
  have h6 := h2.comp_tendsto tendsto_natCast_atTop_atTop
  refine (Asymptotics.isBigO_of_le _ fun n => ?_).trans h6
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _),
    Function.comp_apply, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact hle n

/-- **Abel summation transfer of power-saving cancellation to
log-weighted sums**: if the partial sums of `c` are `O(n^r)` with
`r < 1`, then the partial sums of `k ↦ log k · c k` are `O(n^{r'})` for
`r' = (1+r)/2`, with an explicit constant. Proven by Abel summation
(`sum_mul_eq_sub_integral_mul₀'`) against `t ↦ log t`, the bound
`log t ≤ t^{r'-r}/(r'-r)`, and `∫_1^n t^{r-1} ≤ n^r/r`. -/
theorem exists_forall_norm_sum_log_mul_le_rpow {c : ℕ → ℂ} {r C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) (hc0 : c 0 = 0)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C * (n : ℝ) ^ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, Complex.log (k : ℂ) * c k‖ ≤
        D * (n : ℝ) ^ ((1 + r) / 2) := by
  have hδ : 0 < (1 + r) / 2 - r := by linarith
  refine ⟨C / ((1 + r) / 2 - r) + C / r, by positivity, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by rfl, Finset.sum_empty, norm_zero,
      Nat.cast_zero, Real.zero_rpow (by positivity), mul_zero]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- the `Icc 0` sums shed their `k = 0` term
  have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hshift : ∀ m : ℕ, ∑ k ∈ Finset.Icc 0 m, c k = ∑ k ∈ Finset.Icc 1 m, c k := by
    intro m
    have hsplit' : Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit', Finset.sum_insert (by simp), hc0, zero_add]
  -- differentiability and derivative of the (complexified) logarithm
  have hlogD : ∀ t ∈ Set.Icc (1 : ℝ) (n : ℝ), DifferentiableAt ℝ
      (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    exact ((Real.hasDerivAt_log ht0).ofReal_comp).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) (n : ℝ),
      deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t = ((t⁻¹ : ℝ) : ℂ) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      have := ht.1
      intro h
      rw [h] at this
      linarith
    exact ((Real.hasDerivAt_log ht0).ofReal_comp).deriv
  have hinvint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) (Set.Icc (1 : ℝ) (n : ℝ)) := by
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).integrableOn_Icc
    refine continuousOn_id.inv₀ fun t ht => ?_
    intro h
    rw [id_eq] at h
    rw [h] at ht
    exact absurd ht.1 (by norm_num)
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ))) (Set.Icc (1 : ℝ) (n : ℝ)) :=
    hinvint.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  -- Abel summation against `log`
  have habel := sum_mul_eq_sub_integral_mul₀'
    (f := fun t : ℝ => ((Real.log t : ℝ) : ℂ)) c hc0 n hlogD hint
  -- pass from `Icc 0` to `Icc 1` and from `Real.log` to `Complex.log`
  have hlhs : ∑ k ∈ Finset.Icc 0 n, ((Real.log (k : ℝ) : ℝ) : ℂ) * c k =
      ∑ k ∈ Finset.Icc 1 n, Complex.log (k : ℂ) * c k := by
    rw [hsplit, Finset.sum_insert (by simp), hc0, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Complex.ofReal_log (Nat.cast_nonneg k)]
    norm_num
  rw [hlhs, hshift n] at habel
  rw [habel]
  -- bound the two terms
  have hterm1 : ‖((Real.log (n : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 n, c k‖ ≤
      C / ((1 + r) / 2 - r) * (n : ℝ) ^ ((1 + r) / 2) := by
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hn1)]
    calc Real.log (n : ℝ) * ‖∑ k ∈ Finset.Icc 1 n, c k‖
        ≤ ((n : ℝ) ^ ((1 + r) / 2 - r) / ((1 + r) / 2 - r)) * (C * (n : ℝ) ^ r) := by
          refine mul_le_mul (Real.log_le_rpow_div (Nat.cast_nonneg n) hδ)
            (hbound n) (norm_nonneg _) (by positivity)
      _ = C / ((1 + r) / 2 - r) * (n : ℝ) ^ ((1 + r) / 2) := by
          rw [div_mul_eq_mul_div,
            show (n : ℝ) ^ ((1 + r) / 2 - r) * (C * (n : ℝ) ^ r) =
              C * ((n : ℝ) ^ r * (n : ℝ) ^ ((1 + r) / 2 - r)) by ring,
            ← Real.rpow_add hn0,
            show r + ((1 + r) / 2 - r) = (1 + r) / 2 by ring]
          ring
  have hterm2 : ‖∫ t in Set.Ioc (1 : ℝ) (n : ℝ),
      deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C / r * (n : ℝ) ^ ((1 + r) / 2) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => C * t ^ (r - 1)) (Set.Ioc (1 : ℝ) (n : ℝ)) := by
      have hcont : ContinuousOn (fun t : ℝ => C * t ^ (r - 1))
          (Set.Icc (1 : ℝ) (n : ℝ)) := by
        refine ContinuousOn.mul continuousOn_const ?_
        refine continuousOn_id.rpow_const fun t ht => Or.inl ?_
        intro h
        rw [id_eq] at h
        rw [h] at ht
        exact absurd ht.1 (by norm_num)
      exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hbnd : ∀ t ∈ Set.Ioc (1 : ℝ) (n : ℝ),
        ‖deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C * t ^ (r - 1) := by
      intro t ht
      have ht1 : (1 : ℝ) < t := ht.1
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
      rw [norm_mul, hderiv t ⟨le_of_lt ht1, ht.2⟩, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr ht0.le), hshift ⌊t⌋₊]
      calc t⁻¹ * ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k‖
          ≤ t⁻¹ * (C * t ^ r) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht0.le)
            refine le_trans (hbound ⌊t⌋₊) ?_
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le) hr0.le)
              hC
        _ = C * t ^ (r - 1) := by
            rw [← Real.rpow_neg_one t, mul_comm (t ^ (-1 : ℝ)) _, mul_assoc,
              ← Real.rpow_add ht0, show r + -1 = r - 1 by ring]
    refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hdom
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall hbnd))) ?_
    rw [← intervalIntegral.integral_of_le hn1,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < r - 1)),
      show r - 1 + 1 = r by ring, Real.one_rpow]
    calc C * (((n : ℝ) ^ r - 1) / r) ≤ C * ((n : ℝ) ^ r / r) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          gcongr
          linarith
      _ ≤ C / r * (n : ℝ) ^ ((1 + r) / 2) := by
          rw [show C * ((n : ℝ) ^ r / r) = C / r * (n : ℝ) ^ r by ring]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  calc ‖((Real.log (n : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 n, c k -
        ∫ t in Set.Ioc (1 : ℝ) (n : ℝ),
          deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖
      ≤ ‖((Real.log (n : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.Icc 1 n, c k‖ +
        ‖∫ t in Set.Ioc (1 : ℝ) (n : ℝ),
          deriv (fun t : ℝ => ((Real.log t : ℝ) : ℂ)) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ := norm_sub_le _ _
    _ ≤ C / ((1 + r) / 2 - r) * (n : ℝ) ^ ((1 + r) / 2) +
        C / r * (n : ℝ) ^ ((1 + r) / 2) := add_le_add hterm1 hterm2
    _ = (C / ((1 + r) / 2 - r) + C / r) * (n : ℝ) ^ ((1 + r) / 2) := by ring

open Filter Asymptotics MeasureTheory in
/-- **Uniform bound for an `L`-series with power-saving coefficient
cancellation**: if the partial sums of `c` are `≤ C·n^r` with
`0 < r < 1`, then for real `s > 1` the `L`-series of `c` is bounded by
`s·C/(s-r)`. Via the integral representation `LSeries_eq_mul_integral`
(`L(s) = s·∫_{t>1} A(⌊t⌋)·t^{-s-1}`) and the dominated bound
`‖A(⌊t⌋)‖·t^{-s-1} ≤ C·t^{r-s-1}` with
`∫_{t>1} t^{r-s-1} = 1/(s-r)`. -/
theorem norm_LSeries_le_mul_div_of_forall_norm_sum_le {c : ℕ → ℂ} {r C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C * (n : ℝ) ^ r)
    {s : ℝ} (hs : 1 < s) (hsum : LSeriesSummable c (s : ℂ)) :
    ‖LSeries c (s : ℂ)‖ ≤ s * C / (s - r) := by
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
  have hsr : (0 : ℝ) < s - r := by linarith
  have hrs : r < ((s : ℂ)).re := by rw [Complex.ofReal_re]; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, c k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
    exact hbound n
  rw [LSeries_eq_mul_integral c hr0.le hrs hsum hO, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hs0.le, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hs0.le
  -- dominate the integrand
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (r - s - 1)) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
  have hbnd : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-((s : ℂ) + 1))‖ ≤
        C * t ^ (r - s - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have h1 : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k‖ ≤ C * t ^ r := by
      refine le_trans (hbound ⌊t⌋₊) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le) hr0.le) hC
    have h2 : (-((s : ℂ) + 1)).re = -(s + 1) := by simp
    rw [h2]
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k‖ * t ^ (-(s + 1))
        ≤ (C * t ^ r) * t ^ (-(s + 1)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (r - s - 1) := by
          rw [mul_assoc, ← Real.rpow_add ht0,
            show r + -(s + 1) = r - s - 1 by ring]
  refine le_trans (norm_integral_le_of_norm_le hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hbnd))) ?_
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
    Real.one_rpow]
  rw [show r - s - 1 + 1 = -(s - r) by ring, div_neg, neg_div, neg_neg,
    mul_one_div]

open IsDedekindDomain in
/-- **Power-saving cancellation in the twisted Hecke coefficient sums**
(sorry leaf) — THE deep counting input of the analytic-continuation
half, isolated: for `χ mod ℓ` nontrivial on the image of `Gal(E/F)`
(hypothesis `hχ`), the partial sums
`∑_{k ≤ n} χ(k)·#{I : N(I) = k}` are bounded by `C·n^r` for some
`r < 1`. This is the classical Weber–Landau ideal counting with error
term: `#{I : N(I) ≤ x, [I] = 𝔠} = κ₀·x + O(x^{1-1/d})` uniformly over
classes `𝔠` of the ray-type invariant `(class group, N mod ℓ)`, so the
character sum telescopes to the error terms since `χ` averages to zero
over the norm-residues hit by each fixed class — the nontriviality
`hχ` on the image of `Gal(E/F)` (which is generated by the Frobenius
norm-residues `N P mod ℓ`) is exactly what makes the main terms cancel.
The mathlib pin has the leading term
(`NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`) but no error
term; the lattice-point counting with Lipschitz-boundary error is the
missing ingredient. -/
theorem exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ 0 ≤ C ∧ ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)‖ ≤
        C * (n : ℝ) ^ r :=
  sorry

open IsDedekindDomain in
/-- **Uniform upper bounds for the twisted `L`-series and its derivative
on `(1, 2]`** — the analytic-continuation half of the good behaviour of
`L(s, χ)`, isolated from any nonvanishing: for `χ mod ℓ` nontrivial on
the image of `Gal(E/F)` (hypothesis `hχ`), the twisted ideal `L`-series
and its derivative are bounded uniformly on real `s ∈ (1, 2]`.

DERIVED from the single sorried counting core
`exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow`
(the power-saving Hecke cancellation `‖∑_{k ≤ n} χ(k)·#{I : N(I) =
k}‖ ≤ C·n^r`, `r < 1`) through three PROVEN transfer lemmas:
`norm_LSeries_le_mul_div_of_forall_norm_sum_le` (integral
representation `LSeries_eq_mul_integral` + dominated bound gives
`‖L(s)‖ ≤ s·C/(s-r) ≤ 2C/(1-r)`), `LSeries_deriv`/`logMul` with
`exists_forall_norm_sum_log_mul_le_rpow` (Abel summation transfers the
cancellation to the log-weighted sums with exponent `r' = (1+r)/2`),
and `sum_card_absNorm_isBigO` (linear norm-coefficient growth, giving
summability and the abscissa bound `≤ 1`). -/
theorem exists_forall_norm_LSeries_le_and_norm_deriv_le
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s‖ ≤ C ∧
      ‖deriv (LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))) s‖ ≤ C := by
  classical
  obtain ⟨r, C, hr0, hr1, hC, hbound⟩ :=
    exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow
      hℓ hζ χ hχ
  haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  have hc0 : (fun k : ℕ => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) 0 = 0 := by
    simp only [Nat.cast_zero]
    rw [MulChar.map_nonunit χ not_isUnit_zero, zero_mul]
  obtain ⟨D, hD, hlogbound⟩ :=
    exists_forall_norm_sum_log_mul_le_rpow hr0 hr1 hC hc0 hbound
  -- the norm-coefficient sums grow linearly
  have hOnorm : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ‖χ (k : ZMod ℓ) * (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)‖)
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    have h1 : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)‖‖ ≤
        ‖∑ k ∈ Finset.Icc 1 n,
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)‖ := by
      intro n
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _),
        Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (DirichletCharacter.norm_le_one χ _)
    refine (Asymptotics.isBigO_of_le _ h1).trans
      ((sum_card_absNorm_isBigO F).trans
        (Asymptotics.isBigO_of_le _ fun n => ?_))
    rw [Real.rpow_one]
  -- summability on `re > 1` and abscissa control
  have hsummable : ∀ s : ℝ, 1 < s → LSeriesSummable (fun k : ℕ => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) := by
    intro s hs
    refine LSeriesSummable_of_sum_norm_bigO hOnorm zero_le_one ?_
    rw [Complex.ofReal_re]
    exact hs
  have habs : LSeries.abscissaOfAbsConv (fun k : ℕ => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      fun y hy => hsummable y hy
  have hr'0 : 0 < (1 + r) / 2 := by linarith
  have hr'1 : (1 + r) / 2 < 1 := by linarith
  refine ⟨max (2 * C / (1 - r)) (2 * D / (1 - (1 + r) / 2)),
    fun s hs1 hs2 => ?_⟩
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs1
  have habs_lt : LSeries.abscissaOfAbsConv (fun k : ℕ => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) < (s : ℂ).re := by
    refine lt_of_le_of_lt habs ?_
    rw [Complex.ofReal_re]
    exact_mod_cast hs1
  constructor
  · calc ‖LSeries (fun k : ℕ => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖
        ≤ s * C / (s - r) :=
          norm_LSeries_le_mul_div_of_forall_norm_sum_le hr0 hr1 hC hbound hs1
            (hsummable s hs1)
      _ ≤ 2 * C / (1 - r) := by gcongr
      _ ≤ max (2 * C / (1 - r)) (2 * D / (1 - (1 + r) / 2)) := le_max_left _ _
  · rw [LSeries_deriv habs_lt, norm_neg]
    have hlogsum : LSeriesSummable (LSeries.logMul (fun k : ℕ => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))) (s : ℂ) :=
      LSeriesSummable_logMul_of_lt_re habs_lt
    have hlogbound' : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n,
        (LSeries.logMul (fun k : ℕ => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))) k‖ ≤
        D * (n : ℝ) ^ ((1 + r) / 2) := hlogbound
    calc ‖LSeries (LSeries.logMul (fun k : ℕ => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))) (s : ℂ)‖
        ≤ s * D / (s - (1 + r) / 2) :=
          norm_LSeries_le_mul_div_of_forall_norm_sum_le hr'0 hr'1 hD hlogbound'
            hs1 hlogsum
      _ ≤ 2 * D / (1 - (1 + r) / 2) := by gcongr
      _ ≤ max (2 * C / (1 - r)) (2 * D / (1 - (1 + r) / 2)) := le_max_right _ _

open Filter Asymptotics in
/-- Absolute convergence of the twisted ideal `L`-series for real
`s > 1`, from the linear growth of the coefficient sums
(`sum_card_absNorm_isBigO`). -/
theorem lSeriesSummable_dirichletCharacter_mul_card
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (χ : DirichletCharacter ℂ ℓ)
    {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun k : ℕ => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) := by
  have hOnorm : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      ‖χ (k : ZMod ℓ) * (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)‖)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    have h1 : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, ‖χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)‖‖ ≤
        ‖∑ k ∈ Finset.Icc 1 n,
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)‖ := by
      intro n
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _),
        Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (DirichletCharacter.norm_le_one χ _)
    refine (Asymptotics.isBigO_of_le _ h1).trans
      ((sum_card_absNorm_isBigO F).trans
        (Asymptotics.isBigO_of_le _ fun n => ?_))
    rw [Real.rpow_one]
  refine LSeriesSummable_of_sum_norm_bigO hOnorm zero_le_one ?_
  rw [Complex.ofReal_re]
  exact hs

open Filter MeasureTheory in
/-- **Right continuation of an `L`-series with power-saving coefficient
cancellation to `s = 1`**: if the partial sums of `c` are `≤ C·n^r`
with `0 < r < 1` and the `L`-series converges for real `s > 1`, then as
`s → 1⁺` the `L`-series tends to the extended value
`∫_{t > 1} A(⌊t⌋)·t^{-2}`. Via the integral representation on `(1, ∞)`
and dominated convergence with the `s`-independent dominator
`C·t^{r-2}`. -/
theorem tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le {c : ℕ → ℂ} {r C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C * (n : ℝ) ^ r)
    (hsum : ∀ s : ℝ, 1 < s → LSeriesSummable c (s : ℂ)) :
    Tendsto (fun s : ℝ => LSeries c (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(2 : ℂ)))) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, c k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
    exact hbound n
  -- the integral representation holds on the filter
  have heq : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      (s : ℂ) * ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-((s : ℂ) + 1)) =
      LSeries c (s : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    exact (LSeries_eq_mul_integral c hr0.le
      (by rw [Complex.ofReal_re]; linarith) (hsum s hs1) hO).symm
  -- dominated convergence for the integral factor
  have hDCT : Tendsto (fun s : ℝ => ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-((s : ℂ) + 1)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(2 : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => C * t ^ (r - 2)) ?_ ?_ ?_ ?_
    · -- a.e.-strong measurability of each integrand
      refine Filter.Eventually.of_forall fun s => ?_
      refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((Measurable.of_discrete
            (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, c k)).comp
          (Nat.measurable_floor (R := ℝ))).aestronglyMeasurable
      · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
        intro t ht
        have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
        exact ((continuousAt_cpow_const
          (Complex.ofReal_mem_slitPlane.mpr ht0)).comp
            Complex.continuous_ofReal.continuousAt).continuousWithinAt
    · -- uniform dominated bound near `1⁺`
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : (1 : ℝ) < s := hs
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => ?_)
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have h2 : (-((s : ℂ) + 1)).re = -(s + 1) := by simp
      rw [h2]
      calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k‖ * t ^ (-(s + 1))
          ≤ (C * t ^ r) * t ^ (-(2 : ℝ)) := by
            refine mul_le_mul ?_ ?_ (Real.rpow_nonneg ht0.le _) (by positivity)
            · refine le_trans (hbound ⌊t⌋₊) ?_
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le)
                  hr0.le) hC
            · exact Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
        _ = C * t ^ (r - 2) := by
            rw [mul_assoc, ← Real.rpow_add ht0, show r + -2 = r - 2 by ring]
    · exact (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
    · -- pointwise convergence of the integrand
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht => ?_)
      have ht1 : (1 : ℝ) < t := ht
      have htne : ((t : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (lt_trans one_pos ht1).ne'
      refine Filter.Tendsto.const_mul _ ?_
      have hc : Continuous fun s : ℝ => ((t : ℝ) : ℂ) ^ (-((s : ℂ) + 1)) := by
        refine Continuous.const_cpow ?_ (Or.inl htne)
        continuity
      have h3 := hc.tendsto (1 : ℝ)
      have hval : (-((((1 : ℝ) : ℂ)) + 1)) = (-2 : ℂ) := by norm_num
      rw [hval] at h3
      exact h3.mono_left nhdsWithin_le_nhds
  -- assemble: `s → 1` and `∫ → ∫`
  have hcoe : Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hmul := hcoe.mul hDCT
  rw [Complex.ofReal_one, one_mul] at hmul
  exact hmul.congr' heq

/-!
### Nonvanishing of `L(1, χ)`: the zeta-factorization pole argument

The arithmetic core
`integral_sum_dirichletCharacter_mul_card_cpow_neg_two_ne_zero` is
proven by contradiction through the product `∏_{j < ℓ-1} L(s, χ^j)` of
the twisted ideal `L`-series of ALL powers of `χ`:

* **lower bound** (no vanishing hypothesis): `log ∏_j L(s, χ^j)` is a
  sum over the finite places `P` of `F` whose per-place real part is
  `-(M/f)·log(1 - N P^{-f s}) ≥ 0` (`M = ℓ - 1`, `f` the order of
  `χ(N P)` — by the root-of-unity factorization
  `∏_{j<M} (1 - a^j x) = (1 - x^f)^{M/f}`), and is `≥ M·N P^{-s}` at
  places with `N P ≡ 1 (mod ℓ)`; so the product dominates
  `exp(M · ∑_{N P ≡ 1 (ℓ)} N P^{-s})`.  The congruence-class prime sum
  in turn dominates `1/[E:ℚ]` times the degree-one prime sum of `E`:
  each degree-one place `Q` of `E` away from `ℓ` pulls back to
  `P = Q ∩ 𝓞 F` with the SAME residue cardinality
  (`natCard_quotient_under_eq_of_natCard_prime`), the congruence
  `N Q ≡ 1 (mod ℓ)` holds because `ζ` reduces to a primitive `ℓ`-th
  root of unity in `𝓞 E ⧸ Q`, and the fibers of `Q ↦ P` have at most
  `[𝓞 E : ℤ]` elements (distinct primes of norm `q` have product
  dividing `(q)`, of norm `q^[𝓞 E : ℤ]`); the degree-one prime sum of
  `E` diverges as `s → 1⁺`
  (`exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne E ℓ`).
* **upper bound** (from the assumed vanishing): were the continued
  value `L(1, χ) = 0`, every factor would be controlled on a right
  neighbourhood of `1`: factors with `χ^j` TRIVIAL on the image of
  `Gal(E/F)` have the same `L`-series as the trivial character
  (`LSeries_dirichletCharacter_mul_card_congr`, through
  `exists_algEquiv_map_zeta_eq_pow_absNorm`: every achieved norm is a
  Galois norm-residue), bounded by `C/(s-1)` through the simple pole
  of `ζ_F`; factors with `χ^j` in the coset `χ·(trivial on the image)`
  have the same `L`-series as `χ` itself, bounded by `C'·(s-1)` by the
  vanishing continuation and the uniform derivative bound (mean value
  inequality); the two exponent classes are cosets of ONE subgroup of
  `ZMod (ℓ-1)`, hence have EQUAL cardinality, so the `(s-1)`-powers
  cancel exactly; all remaining factors are uniformly bounded by the
  continuation half `exists_forall_norm_LSeries_le_and_norm_deriv_le`.

`exp(divergent) ≤ bounded` is the contradiction. -/

open IsDedekindDomain in
/-- **Arithmetic Frobenius on `ζ` at an arbitrary place away from `ℓ`**
— the generalization of `exists_algEquiv_map_zeta_eq_pow_natCard` from
degree-one places to ALL finite places `P` of `F` with `ℓ ∤ #(𝓞 F/P)`:
some `σ ∈ Gal(E/F)` acts on `ζ` by `ζ ↦ ζ ^ #(𝓞 F / P)`.  Same proof:
at any prime `Q` of `𝓞 E` above `P` an arithmetic Frobenius exists
(`IsArithFrobAt.exists_of_isInvariant`), and it acts on the `ℓ`-th
root of unity `ζ` exactly by `ζ ↦ ζ ^ #(𝓞 F / P)`
(`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`), because `ℓ` is
invertible modulo `Q` (this is where `ℓ ∤ #(𝓞 F / P)` enters). -/
theorem exists_algEquiv_map_zeta_eq_pow_natCard_of_not_dvd
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (P : HeightOneSpectrum (𝓞 F))
    (hnd : ¬ ℓ ∣ Nat.card (𝓞 F ⧸ P.asIdeal)) :
    ∃ σ : E ≃ₐ[F] E, σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  haveI : IsGalois F E := IsCyclotomicExtension.isGalois {ℓ} F E
  haveI : FiniteDimensional F E := IsCyclotomicExtension.finiteDimensional {ℓ} F E
  haveI : Module.Finite (𝓞 F) (𝓞 E) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  -- a prime of `𝓞 E` over `P`, with finite residue field
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) P.asIdeal
  haveI := hQp
  haveI := hQo
  have hQunder : Q.under (𝓞 F) = P.asIdeal := hQo.over.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [hQo.over, h, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  haveI : Finite (𝓞 E ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQne
  -- a Frobenius element at `Q` over `F`
  obtain ⟨σQ, hσQ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (𝓞 F) (E ≃ₐ[F] E) Q
  -- `ζ` as an algebraic integer
  have hζint : IsIntegral ℤ ζ := by
    refine IsIntegral.of_pow hℓ.pos ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  set ζO : 𝓞 E := ⟨ζ, hζint⟩
  -- `ℓ` is invertible modulo `Q`
  have hℓQ : ((ℓ : ℕ) : 𝓞 E) ∉ Q := by
    intro hmem
    have h1 : ((ℓ : ℕ) : 𝓞 F) ∈ P.asIdeal := by
      rw [← hQunder, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmem
    haveI : Finite (𝓞 F ⧸ P.asIdeal) := by
      refine Nat.finite_of_card_ne_zero ?_
      have h := two_le_natCard_quotient P
      omega
    haveI := Fintype.ofFinite (𝓞 F ⧸ P.asIdeal)
    have h2 : ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : 𝓞 F ⧸ P.asIdeal) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    have h3 : ((ℓ : ℕ) : 𝓞 F ⧸ P.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P.asIdeal),
        Ideal.Quotient.eq_zero_iff_mem]
      exact h1
    have hco : IsCoprime (Nat.card (𝓞 F ⧸ P.asIdeal) : ℤ) (ℓ : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr
        (by
          rw [Int.gcd_natCast_natCast]
          exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd))
    obtain ⟨u, v, huv⟩ := hco
    have h4 : (1 : 𝓞 F ⧸ P.asIdeal) = 0 := by
      calc (1 : 𝓞 F ⧸ P.asIdeal)
          = ((u * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℤ) + v * (ℓ : ℤ) : ℤ) :
            𝓞 F ⧸ P.asIdeal) := by rw [huv, Int.cast_one]
        _ = (u : 𝓞 F ⧸ P.asIdeal) *
              ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : 𝓞 F ⧸ P.asIdeal) +
            (v : 𝓞 F ⧸ P.asIdeal) * ((ℓ : ℕ) : 𝓞 F ⧸ P.asIdeal) := by
            rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
              Int.cast_natCast]
        _ = 0 := by rw [h2, h3, mul_zero, mul_zero, add_zero]
    exact one_ne_zero h4
  -- the Frobenius acts on `ζ` exactly by `ζ ↦ ζ ^ #(𝓞 F / P)`
  have hζOpow : ζO ^ ℓ = 1 := by
    apply NumberField.RingOfIntegers.ext
    show algebraMap (𝓞 E) E (ζO ^ ℓ) = algebraMap (𝓞 E) E 1
    rw [map_pow, map_one]
    show ζ ^ ℓ = 1
    exact hζ.pow_eq_one
  have hσQζ : σQ • ζO = ζO ^ Nat.card (𝓞 F ⧸ P.asIdeal) := by
    have h1 := hσQ.apply_of_pow_eq_one hζOpow hℓQ
    rw [hQunder] at h1
    exact h1
  refine ⟨σQ, ?_⟩
  have h2 : (algebraMap (𝓞 E) E) (σQ • ζO) =
      (algebraMap (𝓞 E) E) (ζO ^ Nat.card (𝓞 F ⧸ P.asIdeal)) :=
    congrArg _ hσQζ
  rw [map_pow] at h2
  have h3 : (algebraMap (𝓞 E) E) (σQ • ζO) = σQ ζ := rfl
  have h4 : (algebraMap (𝓞 E) E) ζO = ζ := rfl
  rw [h3, h4] at h2
  exact h2

open IsDedekindDomain in
/-- **Every achieved ideal norm away from `ℓ` is a Galois
norm-residue**: for a nonzero ideal `I` of `𝓞 F` with `ℓ ∤ N(I)`, some
`σ ∈ Gal(E/F)` acts on `ζ` by `ζ ↦ ζ ^ N(I)`.  By strong induction on
the norm along the Dedekind factorization: split off a maximal divisor
`M ∣ I`, apply the per-place Frobenius lemma
`exists_algEquiv_map_zeta_eq_pow_natCard_of_not_dvd` to `M` and the
inductive hypothesis to `I/M`, and compose the two automorphisms
(`(σ₁σ₂)ζ = ζ^{N(M)·N(I/M)} = ζ^{N(I)}` by multiplicativity of the
absolute norm). -/
theorem exists_algEquiv_map_zeta_eq_pow_absNorm
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hnd : ¬ ℓ ∣ Ideal.absNorm I) :
    ∃ σ : E ≃ₐ[F] E, σ ζ = ζ ^ Ideal.absNorm I := by
  classical
  suffices H : ∀ n : ℕ, ∀ I : Ideal (𝓞 F), Ideal.absNorm I = n → I ≠ ⊥ →
      ¬ ℓ ∣ Ideal.absNorm I → ∃ σ : E ≃ₐ[F] E, σ ζ = ζ ^ Ideal.absNorm I from
    H (Ideal.absNorm I) I rfl hI hnd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro I hIn hIbot hInd
    rcases eq_or_ne I ⊤ with rfl | htop
    · refine ⟨1, ?_⟩
      rw [← Ideal.one_eq_top, map_one, pow_one]
      rfl
    · -- split off a maximal divisor
      obtain ⟨M, hMmax, hIM⟩ := Ideal.exists_le_maximal I htop
      have hMne : M ≠ ⊥ := by
        rintro rfl
        exact hIbot (le_bot_iff.mp hIM)
      obtain ⟨J, rfl⟩ := (Ideal.dvd_iff_le).mpr hIM
      have hJne : J ≠ ⊥ := by
        rintro rfl
        rw [Ideal.mul_bot] at hIbot
        exact hIbot rfl
      have hnMJ : Ideal.absNorm (M * J) =
          Ideal.absNorm M * Ideal.absNorm J := map_mul _ _ _
      have hM0 : Ideal.absNorm M ≠ 0 := fun h =>
        hMne (Ideal.absNorm_eq_zero_iff.mp h)
      have hM1 : Ideal.absNorm M ≠ 1 := fun h =>
        hMmax.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      have hJ0 : Ideal.absNorm J ≠ 0 := fun h =>
        hJne (Ideal.absNorm_eq_zero_iff.mp h)
      have hJlt : Ideal.absNorm J < n := by
        rw [← hIn, hnMJ]
        have hJpos : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero hJ0
        have h3 : 1 * Ideal.absNorm J < Ideal.absNorm M * Ideal.absNorm J :=
          mul_lt_mul_of_pos_right (by omega) hJpos
        omega
      have hndM : ¬ ℓ ∣ Ideal.absNorm M := fun h =>
        hInd (hnMJ ▸ h.mul_right _)
      have hndJ : ¬ ℓ ∣ Ideal.absNorm J := fun h =>
        hInd (hnMJ ▸ h.mul_left _)
      haveI := hMmax.isPrime
      set P : HeightOneSpectrum (𝓞 F) := ⟨M, hMmax.isPrime, hMne⟩ with hP
      have hcardM : Nat.card (𝓞 F ⧸ P.asIdeal) = Ideal.absNorm M := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      obtain ⟨σ₁, hσ₁⟩ :=
        exists_algEquiv_map_zeta_eq_pow_natCard_of_not_dvd hℓ hζ P
          (by rw [hcardM]; exact hndM)
      obtain ⟨σ₂, hσ₂⟩ := ih (Ideal.absNorm J) hJlt J rfl hJne hndJ
      refine ⟨σ₁ * σ₂, ?_⟩
      have hcomp : (σ₁ * σ₂) ζ = σ₁ (σ₂ ζ) := rfl
      rw [hcomp, hσ₂, map_pow, hσ₁, hcardM, ← pow_mul, hnMJ]

open IsDedekindDomain in
/-- **Congruence of twisted ideal `L`-series for characters agreeing on
the Galois norm-residues**: if `χ₁` and `χ₂` agree at every exponent
`n` through which `Gal(E/F)` acts on `ζ`, then the `χ₁`- and
`χ₂`-twisted ideal Dirichlet series of `F` are equal at every point.
Every `k ≥ 1` with a nonzero ideal count and `ℓ ∤ k` is a Galois
norm-residue (`exists_algEquiv_map_zeta_eq_pow_absNorm`); at `ℓ ∣ k`
both characters vanish, and at zero count both coefficients vanish. -/
theorem LSeries_dirichletCharacter_mul_card_congr
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ₁ χ₂ : DirichletCharacter ℂ ℓ)
    (h : ∀ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n →
      χ₁ (n : ZMod ℓ) = χ₂ (n : ZMod ℓ)) (s : ℂ) :
    LSeries (fun k => χ₁ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s =
      LSeries (fun k => χ₂ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s := by
  classical
  refine LSeries_congr (fun {k} hk => ?_) s
  rcases Nat.eq_zero_or_pos (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k})
    with hc | hc
  · rw [hc, Nat.cast_zero, mul_zero, mul_zero]
  · congr 1
    by_cases hdvd : ℓ ∣ k
    · have h0 : ((k : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff k ℓ).mpr hdvd
      haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
      have hnu : ¬ IsUnit ((k : ℕ) : ZMod ℓ) := by
        rw [h0]
        haveI := Fact.mk hℓ
        exact not_isUnit_zero
      rw [MulChar.map_nonunit χ₁ hnu, MulChar.map_nonunit χ₂ hnu]
    · haveI : Nonempty {I : Ideal (𝓞 F) // Ideal.absNorm I = k} :=
        (Nat.card_pos_iff.mp hc).1
      obtain ⟨I, hIk⟩ := ‹Nonempty {I : Ideal (𝓞 F) // Ideal.absNorm I = k}›.some
      have hIne : I ≠ ⊥ := by
        rintro rfl
        rw [Ideal.absNorm_bot] at hIk
        exact hk hIk.symm
      obtain ⟨σ, hσ⟩ := exists_algEquiv_map_zeta_eq_pow_absNorm hℓ hζ I hIne
        (by rw [hIk]; exact hdvd)
      rw [hIk] at hσ
      exact h σ k hσ

open Filter in
/-- **Universal pole-order bound for twisted ideal `L`-series near
`s = 1`**: on some right interval `(1, 1+δ]`, EVERY `χ mod ℓ`-twisted
ideal Dirichlet series of `F` is bounded by `C/(s-1)`.  Termwise the
twisted series is dominated by the untwisted one (`‖χ(k)‖ ≤ 1`), whose
value at real `s > 1` is `‖ζ_F(s)‖`; the simple pole
`(s-1)·ζ_F(s) → κ`
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) gives the
eventual bound with `C = ‖κ‖ + 1`. -/
theorem exists_forall_norm_LSeries_dirichletCharacter_mul_card_le_div
    (F : Type*) [Field F] [NumberField F] (ℓ : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (χ : DirichletCharacter ℂ ℓ) (s : ℝ),
      1 < s → s ≤ 1 + δ →
      ‖LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖ ≤
        C / (s - 1) := by
  classical
  have hnorm := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have hev := hnorm.eventually_le_const
    (lt_add_one ‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖)
  obtain ⟨u, hu, hIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨u - 1, ‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖ + 1,
    by linarith [Set.mem_Ioi.mp hu], by positivity, ?_⟩
  intro χ s hs1 hs2
  have hbound := hIoc ⟨hs1, by linarith⟩
  have hspos : (0 : ℝ) < s := by linarith
  -- the untwisted real sum equals `‖ζ_F(s)‖`
  have hζeq : NumberField.dedekindZeta F s =
      ((∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [show NumberField.dedekindZeta F s = ∑' n : ℕ, LSeries.term
        (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ))
        (s : ℂ) n from rfl,
      tsum_congr (term_natCard_absNorm_eq F hspos), Complex.ofReal_tsum]
  have hsumnn : (0 : ℝ) ≤ ∑' n : ℕ,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) :=
    tsum_nonneg fun n => by positivity
  have hζnorm : ‖NumberField.dedekindZeta F s‖ = ∑' n : ℕ,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
    rw [hζeq, Complex.norm_real, Real.norm_of_nonneg hsumnn]
  -- the twisted series is dominated termwise by the untwisted sum
  have htermnorm : ∀ n : ℕ, ‖LSeries.term (fun k => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) n‖ ≤
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (neg_ne_zero.mpr hspos.ne'), mul_zero]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hden : (0 : ℝ) < (n : ℝ) ^ s :=
        Real.rpow_pos_of_pos (by exact_mod_cast hnpos) s
      rw [LSeries.term_of_ne_zero hn, norm_div, norm_mul, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos hnpos, Complex.ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]
      gcongr
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (DirichletCharacter.norm_le_one χ _)
  have hsum := summable_natCard_absNorm_mul_rpow_neg F hs1
  have hnormsum : Summable (fun n : ℕ => ‖LSeries.term (fun k => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htermnorm hsum
  have hLle : ‖LSeries (fun k => χ (k : ZMod ℓ) *
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖ ≤
      ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) := by
    rw [show LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) =
        ∑' n : ℕ, LSeries.term (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) n
        from rfl]
    exact le_trans (norm_tsum_le_tsum_norm hnormsum)
      (hnormsum.tsum_le_tsum htermnorm hsum)
  -- conclude through the simple pole
  have hfin : (s - 1) * ‖NumberField.dedekindZeta F s‖ ≤
      ‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖ + 1 := by
    simp only [Set.mem_setOf_eq] at hbound
    rwa [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, norm_mul,
      Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ s - 1)] at hbound
  have hs1' : (0 : ℝ) < s - 1 := by linarith
  calc ‖LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖
      ≤ ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) := hLle
    _ = ‖NumberField.dedekindZeta F s‖ := hζnorm.symm
    _ ≤ (‖((NumberField.dedekindZeta_residue F : ℝ) : ℂ)‖ + 1) / (s - 1) := by
        rw [le_div_iff₀ hs1']
        linarith [hfin]

/-- The `(ℓ-1)`-st power of every `ℂ`-valued Dirichlet character mod a
prime `ℓ` is the trivial character (the unit group of `ZMod ℓ` has
order `ℓ - 1`). -/
theorem dirichletCharacter_pow_card_sub_one_eq_one {ℓ : ℕ} (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) : χ ^ (ℓ - 1) = 1 := by
  haveI := Fact.mk hℓ
  rw [← ZMod.card_units ℓ]
  exact χ.pow_card_eq_one

/-- Powers of a Dirichlet character mod a prime `ℓ` depend on the
exponent only through its residue mod `ℓ - 1`. -/
theorem dirichletCharacter_pow_mod {ℓ : ℕ} (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) (a : ℕ) : χ ^ a = χ ^ (a % (ℓ - 1)) := by
  conv_lhs => rw [← Nat.div_add_mod a (ℓ - 1)]
  rw [pow_add, pow_mul, dirichletCharacter_pow_card_sub_one_eq_one hℓ χ,
    one_pow, one_mul]

open Filter in
/-- **Vanishing rate of the twisted `L`-series under vanishing of the
continued value** (mean value inequality glue): if the continued value
`∫_{t>1} A(⌊t⌋)·t^{-2} = 0`, then `‖L(s,χ)‖ ≤ C·(s-1)` on `(1, 2]`.
From the continuation
`tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le` (the `L`-series
tends to the continued value — here `0` — as `s → 1⁺`), the uniform
derivative bound `exists_forall_norm_LSeries_le_and_norm_deriv_le`,
differentiability right of the abscissa (`LSeries_hasDerivAt`), and
the mean value inequality on `[t, s]` followed by `t → 1⁺`. -/
theorem exists_forall_norm_LSeries_le_mul_sub_one_of_integral_eq_zero
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1)
    (h0 : (∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) *
      (t : ℂ) ^ (-(2 : ℂ))) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖ ≤
        (C * (s - 1)) := by
  classical
  set c : ℕ → ℂ := fun k => χ (k : ZMod ℓ) *
    (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ) with hc
  obtain ⟨r, C₁, hr0, hr1, hC₁, hbound⟩ :=
    exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow hℓ hζ χ hχ
  have htend := tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le hr0 hr1 hC₁
    hbound (fun t ht => lSeriesSummable_dirichletCharacter_mul_card F χ ht)
  rw [h0] at htend
  obtain ⟨C₂, hC₂⟩ := exists_forall_norm_LSeries_le_and_norm_deriv_le hℓ hζ χ hχ
  have habs : LSeries.abscissaOfAbsConv c ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => lSeriesSummable_dirichletCharacter_mul_card F χ hy)
  have hderiv : ∀ t : ℝ, 1 < t →
      HasDerivAt (fun u : ℝ => LSeries c (u : ℂ))
        (deriv (LSeries c) ((t : ℝ) : ℂ)) t := by
    intro t ht
    have h1 : LSeries.abscissaOfAbsConv c < (((t : ℝ) : ℂ)).re := by
      refine lt_of_le_of_lt habs ?_
      rw [Complex.ofReal_re]
      exact_mod_cast ht
    exact (LSeries_hasDerivAt h1).differentiableAt.hasDerivAt.comp_ofReal
  refine ⟨max C₂ 0, le_max_right _ _, fun s hs1 hs2 => ?_⟩
  have hMVT : ∀ t : ℝ, 1 < t → t ≤ s →
      ‖LSeries c (s : ℂ) - LSeries c (t : ℂ)‖ ≤ max C₂ 0 * (s - t) := by
    intro t ht hts
    have hin : ∀ u ∈ Set.Icc t s, HasDerivWithinAt (fun u : ℝ => LSeries c (u : ℂ))
        (deriv (LSeries c) ((u : ℝ) : ℂ)) (Set.Icc t s) u :=
      fun u hu => (hderiv u (lt_of_lt_of_le ht hu.1)).hasDerivWithinAt
    have hbnd : ∀ u ∈ Set.Icc t s, ‖deriv (LSeries c) ((u : ℝ) : ℂ)‖ ≤ max C₂ 0 :=
      fun u hu => le_trans
        ((hC₂ u (lt_of_lt_of_le ht hu.1) (le_trans hu.2 hs2)).2)
        (le_max_left _ _)
    have h3 := (convex_Icc t s).norm_image_sub_le_of_norm_hasDerivWithin_le
      hin hbnd (Set.left_mem_Icc.mpr hts) (Set.right_mem_Icc.mpr hts)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)] at h3
  have h1 : Tendsto (fun t : ℝ => ‖LSeries c (s : ℂ) - LSeries c (t : ℂ)‖)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds ‖LSeries c (s : ℂ) - 0‖) :=
    (Filter.Tendsto.sub tendsto_const_nhds htend).norm
  have h2 : Tendsto (fun t : ℝ => max C₂ 0 * (s - t)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (max C₂ 0 * (s - 1))) := by
    have h4 : Tendsto (fun t : ℝ => max C₂ 0 * (s - t)) (nhds 1)
        (nhds (max C₂ 0 * (s - 1))) :=
      (tendsto_const_nhds.sub tendsto_id).const_mul _
    exact h4.mono_left nhdsWithin_le_nhds
  have hev2 : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Ioi 1),
      ‖LSeries c (s : ℂ) - LSeries c (t : ℂ)‖ ≤ max C₂ 0 * (s - t) := by
    filter_upwards [Ioo_mem_nhdsGT hs1] with t ht
    exact hMVT t ht.1 ht.2.le
  have hfin := le_of_tendsto_of_tendsto h1 h2 hev2
  rwa [sub_zero] at hfin

/-- **Root-of-unity factorization of the character-averaged Euler
factor**: for `a ∈ ℂ` with `a ^ M = 1` (`M > 0`) and any `x`,
`∏_{j<M} (1 - a^j·x) = (1 - x^f)^{M/f}` where `f` is the order of `a`.
Via `∏_{r<f} (y - a^r) = y^f - 1` (the `f`-th roots of unity are
exactly the powers of `a`, `Polynomial.X_pow_sub_one_eq_prod`)
evaluated at `y = x⁻¹`, and `f`-periodicity of `j ↦ a^j`. -/
theorem prod_range_one_sub_pow_mul {M : ℕ} (hM : 0 < M) {a : ℂ} (ha : a ^ M = 1)
    (x : ℂ) :
    ∏ j ∈ Finset.range M, (1 - a ^ j * x) =
      (1 - x ^ orderOf a) ^ (M / orderOf a) := by
  classical
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨M, hM, ha⟩
  have hfpos : 0 < orderOf a := hfin.orderOf_pos
  have hprim : IsPrimitiveRoot a (orderOf a) := IsPrimitiveRoot.orderOf a
  have hdvd : orderOf a ∣ M := orderOf_dvd_of_pow_eq_one ha
  -- the `f`-th roots of unity are exactly the powers of `a`
  have himg : (Finset.range (orderOf a)).image (a ^ ·) =
      Polynomial.nthRootsFinset (orderOf a) (1 : ℂ) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro μ hμ
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hμ
      refine (Polynomial.mem_nthRootsFinset hfpos 1).mpr ?_
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    · rw [hprim.card_nthRootsFinset,
        Finset.card_image_of_injOn hprim.injOn_pow, Finset.card_range]
  have hroots : ∀ y : ℂ, ∏ r ∈ Finset.range (orderOf a), (y - a ^ r) =
      y ^ orderOf a - 1 := by
    intro y
    calc ∏ r ∈ Finset.range (orderOf a), (y - a ^ r)
        = ∏ μ ∈ (Finset.range (orderOf a)).image (a ^ ·), (y - μ) :=
          (Finset.prod_image fun i hi j hj hij =>
            hprim.injOn_pow (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj)
              hij).symm
      _ = ∏ μ ∈ Polynomial.nthRootsFinset (orderOf a) (1 : ℂ), (y - μ) := by
          rw [himg]
      _ = Polynomial.eval y (∏ μ ∈ Polynomial.nthRootsFinset (orderOf a) (1 : ℂ),
            (Polynomial.X - Polynomial.C μ)) := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_congr rfl fun μ _ => by
            rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      _ = Polynomial.eval y (Polynomial.X ^ orderOf a - 1) := by
          rw [← Polynomial.X_pow_sub_one_eq_prod hfpos hprim]
      _ = y ^ orderOf a - 1 := by
          rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_one]
  -- one period of the product
  have hblock : ∏ r ∈ Finset.range (orderOf a), (1 - a ^ r * x) =
      1 - x ^ orderOf a := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp [zero_pow hfpos.ne']
    · have h1 := hroots x⁻¹
      have h2 : ∏ r ∈ Finset.range (orderOf a), (1 - a ^ r * x) =
          ∏ r ∈ Finset.range (orderOf a), (x * (x⁻¹ - a ^ r)) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        rw [mul_sub, mul_inv_cancel₀ hx, mul_comm x (a ^ r)]
      have hxf : x ^ orderOf a ≠ 0 := pow_ne_zero _ hx
      rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, h1,
        inv_pow, mul_sub, mul_inv_cancel₀ hxf, mul_one]
  -- periodicity glue
  have hper : ∀ m : ℕ, ∏ j ∈ Finset.range (orderOf a * m), (1 - a ^ j * x) =
      (1 - x ^ orderOf a) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ k ihk =>
        rw [Nat.mul_succ, Finset.prod_range_add, ihk, pow_succ]
        congr 1
        rw [← hblock]
        refine Finset.prod_congr rfl fun r _ => ?_
        rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  obtain ⟨m, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left m hfpos]
  exact hper m

/-- **Per-place positivity of the character-power averaged
log-factor**: for `u ∈ ZMod ℓ` and `0 < x ≤ 1/2`, the real part of
`∑_{j<ℓ-1} -log(1 - χ^j(u)·x)` is nonnegative, and is at least
`(ℓ-1)·x` when `u = 1`.  For a unit `u` the sum is
`-(M/f)·log(1 - x^f) ≥ 0` (`f` the order of `χ(u)`, via
`prod_range_one_sub_pow_mul` and `Re log = log ‖·‖`); for a nonunit
`u` every factor is `-log 1 = 0`. -/
theorem re_sum_range_neg_log_one_sub_nonneg {ℓ : ℕ} (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) (u : ZMod ℓ) {x : ℝ} (hx0 : 0 < x)
    (hx2 : x ≤ 1 / 2) :
    0 ≤ (∑ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) u * (x : ℂ))).re ∧
      (u = 1 → ((ℓ - 1 : ℕ) : ℝ) * x ≤
        (∑ j ∈ Finset.range (ℓ - 1),
          -Complex.log (1 - (χ ^ j) u * (x : ℂ))).re) := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  have hM1 : 0 < ℓ - 1 := by have := hℓ.two_le; omega
  by_cases hu : IsUnit u
  · -- unit case: closed form via the factorization
    have hb : ∀ j : ℕ, (χ ^ j) u = χ u ^ j := by
      intro j
      conv_lhs => rw [← hu.unit_spec]
      rw [MulChar.pow_apply_coe]
      rw [hu.unit_spec]
    have haM : χ u ^ (ℓ - 1) = 1 := by
      rw [← hb, dirichletCharacter_pow_card_sub_one_eq_one hℓ χ,
        MulChar.one_apply hu]
    have hfin : IsOfFinOrder (χ u) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hM1, haM⟩
    have hfpos : 0 < orderOf (χ u) := hfin.orderOf_pos
    -- `x ^ f` stays in `(0, 1)`
    have hxf1 : x ^ orderOf (χ u) ≤ x := by
      calc x ^ orderOf (χ u) ≤ x ^ 1 :=
            pow_le_pow_of_le_one hx0.le (by linarith) hfpos
        _ = x := pow_one x
    have hxfpos : 0 < x ^ orderOf (χ u) := pow_pos hx0 _
    -- each factor is away from zero
    have hne : ∀ j : ℕ, (1 : ℂ) - χ u ^ j * (x : ℂ) ≠ 0 := by
      intro j hzero
      have h1 : χ u ^ j * (x : ℂ) = 1 := (sub_eq_zero.mp hzero).symm
      have h2 : ‖χ u ^ j * (x : ℂ)‖ = 1 := by rw [h1, norm_one]
      have h3 : ‖χ u ^ j * (x : ℂ)‖ ≤ 1 / 2 := by
        rw [norm_mul, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hx0.le]
        calc ‖χ u‖ ^ j * x ≤ 1 ^ j * x := by
              gcongr
              exact DirichletCharacter.norm_le_one χ u
          _ = x := by rw [one_pow, one_mul]
          _ ≤ 1 / 2 := hx2
      rw [h2] at h3
      linarith
    -- the real part of the sum is `-log` of the norm of the product
    have hre : (∑ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) u * (x : ℂ))).re =
        -Real.log ‖∏ j ∈ Finset.range (ℓ - 1), (1 - χ u ^ j * (x : ℂ))‖ := by
      calc (∑ j ∈ Finset.range (ℓ - 1),
            -Complex.log (1 - (χ ^ j) u * (x : ℂ))).re
          = ∑ j ∈ Finset.range (ℓ - 1),
              (-Complex.log (1 - (χ ^ j) u * (x : ℂ))).re :=
            Complex.re_sum _ _
        _ = ∑ j ∈ Finset.range (ℓ - 1),
              -Real.log ‖1 - χ u ^ j * (x : ℂ)‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Complex.neg_re, Complex.log_re, hb j]
        _ = -∑ j ∈ Finset.range (ℓ - 1),
              Real.log ‖1 - χ u ^ j * (x : ℂ)‖ := by
            rw [Finset.sum_neg_distrib]
        _ = -Real.log (∏ j ∈ Finset.range (ℓ - 1),
              ‖1 - χ u ^ j * (x : ℂ)‖) := by
            rw [Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (hne j))]
        _ = -Real.log ‖∏ j ∈ Finset.range (ℓ - 1),
              (1 - χ u ^ j * (x : ℂ))‖ := by rw [norm_prod]
    have hnormval : ‖∏ j ∈ Finset.range (ℓ - 1), (1 - χ u ^ j * (x : ℂ))‖ =
        (1 - x ^ orderOf (χ u)) ^ ((ℓ - 1) / orderOf (χ u)) := by
      rw [prod_range_one_sub_pow_mul hM1 haM (x : ℂ),
        show ((1 : ℂ) - (x : ℂ) ^ orderOf (χ u)) =
          ((1 - x ^ orderOf (χ u) : ℝ) : ℂ) by push_cast; ring,
        norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x ^ orderOf (χ u))]
    constructor
    · rw [hre, hnormval]
      have hlogle : Real.log ((1 - x ^ orderOf (χ u)) ^
          ((ℓ - 1) / orderOf (χ u))) ≤ 0 := by
        refine Real.log_nonpos (pow_nonneg (by linarith) _) ?_
        exact pow_le_one₀ (by linarith) (by linarith)
      linarith
    · intro hu1
      have hf1 : orderOf (χ u) = 1 := by rw [hu1, map_one, orderOf_one]
      rw [hre, hnormval, hf1, pow_one, Nat.div_one, Real.log_pow]
      have hlog : Real.log (1 - x) ≤ -x := by
        have h4 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 - x)
        linarith
      have h5 := mul_le_mul_of_nonneg_left hlog
        (Nat.cast_nonneg (ℓ - 1) : (0 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ))
      nlinarith
  · -- nonunit: every term vanishes
    have hzero : ∀ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) u * (x : ℂ)) = 0 := by
      intro j _
      rw [MulChar.map_nonunit (χ ^ j) hu, zero_mul, sub_zero, Complex.log_one,
        neg_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero]
    exact ⟨le_refl _, fun hu1 => absurd isUnit_one (hu1 ▸ hu)⟩

open IsDedekindDomain in
/-- **Character-power averaged lower bound for the prime log-sums**:
for real `s > 1`, `(ℓ-1)` times the congruence-class prime sum
`∑_{N P ≡ 1 (mod ℓ)} N P^{-s}` (over degree-one places of `F`) is
dominated by the real part of `∑_{j<ℓ-1} 𝒮_{χ^j}(s)`, the sum of the
prime log-sums of ALL powers of `χ`.  Per place the real part is
nonnegative, and at the congruence-class places it is
`≥ (ℓ-1)·N P^{-s}` (`re_sum_range_neg_log_one_sub_nonneg`). -/
theorem mul_tsum_rpow_neg_le_sum_re_tsum_neg_log
    (F : Type*) [Field F] [NumberField F] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) {s : ℝ} (hs : 1 < s) :
    ((ℓ - 1 : ℕ) : ℝ) * ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) ≤
    ∑ j ∈ Finset.range (ℓ - 1),
      (∑' P : HeightOneSpectrum (𝓞 F),
        -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re := by
  classical
  have hNpos : ∀ P : HeightOneSpectrum (𝓞 F),
      (0 : ℝ) < (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
    intro P
    have h := two_le_natCard_quotient P
    exact_mod_cast (by omega : 0 < Nat.card (𝓞 F ⧸ P.asIdeal))
  have hxpos : ∀ P : HeightOneSpectrum (𝓞 F),
      (0 : ℝ) < (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) :=
    fun P => Real.rpow_pos_of_pos (hNpos P) _
  have hxhalf : ∀ P : HeightOneSpectrum (𝓞 F),
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) ≤ 1 / 2 := by
    intro P
    have h2N : (2 : ℝ) ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
      exact_mod_cast two_le_natCard_quotient P
    calc (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)
        ≤ (2 : ℝ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos two_pos h2N (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          (Real.rpow_le_rpow_left_iff one_lt_two).mpr (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hcpow : ∀ P : HeightOneSpectrum (𝓞 F),
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)) =
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro P
    rw [show ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ℂ) =
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ)) : ℂ) by push_cast; ring,
      show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (hNpos P).le]
  -- norm bound for the log terms, uniform in the power `j`
  have hlogb : ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 F)),
      ‖-Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ ≤
        3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) := by
    intro j P
    have hzb : ‖(χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))‖ ≤
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) := by
      rw [hcpow P, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hxpos P).le]
      exact mul_le_of_le_one_left (hxpos P).le
        (DirichletCharacter.norm_le_one (χ ^ j) _)
    have h6 : ‖-((χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
      rw [norm_neg]
      exact le_trans hzb (hxhalf P)
    rw [norm_neg]
    calc ‖Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖
        = ‖Complex.log (1 + -((χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))))‖ := by
          rw [sub_eq_add_neg]
      _ ≤ 3 / 2 * ‖-((χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ :=
          Complex.norm_log_one_add_half_le_self h6
      _ = 3 / 2 * ‖(χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))‖ := by rw [norm_neg]
      _ ≤ 3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_left hzb (by norm_num)
  have hsum_s : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) :=
    summable_rpow_neg_natCard_quotient hs
  have hlogsum : ∀ j : ℕ, Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))) := fun j =>
    Summable.of_norm (Summable.of_nonneg_of_le (fun P => norm_nonneg _)
      (hlogb j) (hsum_s.mul_left _))
  have hsumsum : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      ∑ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))) :=
    (hasSum_sum fun j _ => (hlogsum j).hasSum).summable
  -- swap the finite and infinite sums, take real parts inside
  have hswap : ∑ j ∈ Finset.range (ℓ - 1),
      (∑' P : HeightOneSpectrum (𝓞 F),
        -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re =
      ∑' P : HeightOneSpectrum (𝓞 F),
        (∑ j ∈ Finset.range (ℓ - 1),
          -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re := by
    rw [← Complex.re_sum, ← Summable.tsum_finsetSum (fun j _ => hlogsum j),
      Complex.re_tsum hsumsum]
  -- per-place bounds
  have hkey : ∀ P : HeightOneSpectrum (𝓞 F),
      0 ≤ (∑ j ∈ Finset.range (ℓ - 1),
          -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re ∧
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1 →
          ((ℓ - 1 : ℕ) : ℝ) * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) ≤
          (∑ j ∈ Finset.range (ℓ - 1),
            -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re) := by
    intro P
    have h := re_sum_range_neg_log_one_sub_nonneg hℓ χ
      ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) (hxpos P) (hxhalf P)
    rw [show ((((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) : ℝ)) : ℂ) =
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)) from (hcpow P).symm] at h
    exact h
  -- real-part family: nonnegative, dominated, summable
  have hrle : ∀ P : HeightOneSpectrum (𝓞 F),
      (∑ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re ≤
        ((ℓ - 1 : ℕ) : ℝ) * (3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) := by
    intro P
    refine le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) ?_
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ j ∈ Finset.range (ℓ - 1),
          ‖-Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖
        ≤ ∑ _j ∈ Finset.range (ℓ - 1),
            3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) :=
          Finset.sum_le_sum fun j _ => hlogb j P
      _ = ((ℓ - 1 : ℕ) : ℝ) *
            (3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrsum : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      (∑ j ∈ Finset.range (ℓ - 1),
        -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re) :=
    Summable.of_nonneg_of_le (fun P => (hkey P).1) hrle
      (((hsum_s.mul_left _).mul_left _))
  rw [hswap]
  -- restrict to the congruence-class places and use the per-place bound
  calc ((ℓ - 1 : ℕ) : ℝ) * ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
      = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        ((ℓ - 1 : ℕ) : ℝ) *
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :=
        (tsum_mul_left).symm
    _ ≤ ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        (∑ j ∈ Finset.range (ℓ - 1),
          -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸
              (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℂ) ^
              (-(s : ℂ)))).re :=
        ((hsum_s.mul_left _).subtype _).tsum_le_tsum
          (fun P => (hkey P.1).2 P.2.2) (hrsum.subtype _)
    _ ≤ ∑' P : HeightOneSpectrum (𝓞 F),
        (∑ j ∈ Finset.range (ℓ - 1),
          -Complex.log (1 - (χ ^ j) ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))).re :=
        Summable.tsum_subtype_le _ _ (fun P => (hkey P).1) hrsum

open IsDedekindDomain in
/-- **Degree-one places of a field with an `ℓ`-th root of unity lie
over split primes**: if `E` contains a primitive `ℓ`-th root of unity
(`ℓ` prime) and `Q` is a finite place of `E` of prime residue
cardinality `q ≠ ℓ`, then `q ≡ 1 (mod ℓ)`.  The reduction of `ζ`
mod `Q` is a nontrivial `ℓ`-th root of unity of the residue field
(nontrivial because `∑_{i<ℓ} ζ^i = 0` would otherwise reduce to
`ℓ = 0` in characteristic `q ≠ ℓ`), so its exact order `ℓ` divides
`q - 1`, the order of the unit group. -/
theorem natCast_natCard_quotient_eq_one_of_prime
    {E : Type*} [Field E] [NumberField E] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (Q : HeightOneSpectrum (𝓞 E))
    (hq : (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime)
    (hne : Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ) :
    ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : ZMod ℓ) = 1 := by
  classical
  haveI hQfin : Finite (𝓞 E ⧸ Q.asIdeal) := Nat.finite_of_card_ne_zero hq.ne_zero
  haveI := Fintype.ofFinite (𝓞 E ⧸ Q.asIdeal)
  letI : Field (𝓞 E ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  -- `ζ` as an algebraic integer, and its reduction mod `Q`
  have hζint : IsIntegral ℤ ζ := by
    refine IsIntegral.of_pow hℓ.pos ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  set ζO : 𝓞 E := ⟨ζ, hζint⟩ with hζO
  set ζbar : 𝓞 E ⧸ Q.asIdeal := Ideal.Quotient.mk Q.asIdeal ζO with hζbar
  have hζOpow : ζO ^ ℓ = 1 := by
    apply NumberField.RingOfIntegers.ext
    show algebraMap (𝓞 E) E (ζO ^ ℓ) = algebraMap (𝓞 E) E 1
    rw [map_pow, map_one]
    show ζ ^ ℓ = 1
    exact hζ.pow_eq_one
  have hζpow : ζbar ^ ℓ = 1 := by rw [hζbar, ← map_pow, hζOpow, map_one]
  -- the residue characteristic kills `q`
  have hqzero : ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : 𝓞 E ⧸ Q.asIdeal) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _
  -- `ζbar ≠ 1`: else the geometric sum `ℓ` would vanish mod `Q`
  have hζne1 : ζbar ≠ 1 := by
    intro h1
    have hgeom : ∑ i ∈ Finset.range ℓ, ζ ^ i = 0 :=
      hζ.geom_sum_eq_zero hℓ.one_lt
    have hgeomO : ∑ i ∈ Finset.range ℓ, ζO ^ i = 0 := by
      apply NumberField.RingOfIntegers.ext
      show algebraMap (𝓞 E) E (∑ i ∈ Finset.range ℓ, ζO ^ i) =
        algebraMap (𝓞 E) E 0
      rw [map_zero, map_sum]
      calc ∑ i ∈ Finset.range ℓ, algebraMap (𝓞 E) E (ζO ^ i)
          = ∑ i ∈ Finset.range ℓ, ζ ^ i :=
            Finset.sum_congr rfl fun i _ => by rw [map_pow]; rfl
        _ = 0 := hgeom
    have hsum0 : ∑ i ∈ Finset.range ℓ, ζbar ^ i = 0 := by
      rw [hζbar]
      calc ∑ i ∈ Finset.range ℓ, (Ideal.Quotient.mk Q.asIdeal ζO) ^ i
          = Ideal.Quotient.mk Q.asIdeal (∑ i ∈ Finset.range ℓ, ζO ^ i) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_pow]
        _ = 0 := by rw [hgeomO, map_zero]
    rw [h1] at hsum0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at hsum0
    -- Bezout: `ℓ` and `q` both vanish in the quotient, yet are coprime
    have hco : IsCoprime (ℓ : ℤ) ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr
        (by
          rw [Int.gcd_natCast_natCast]
          exact (Nat.coprime_primes hℓ hq).mpr fun h => hne h.symm)
    obtain ⟨u, v, huv⟩ := hco
    have h4 : (1 : 𝓞 E ⧸ Q.asIdeal) = 0 := by
      calc (1 : 𝓞 E ⧸ Q.asIdeal)
          = ((u * (ℓ : ℤ) + v * ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : ℤ) : ℤ) :
              𝓞 E ⧸ Q.asIdeal) := by rw [huv, Int.cast_one]
        _ = (u : 𝓞 E ⧸ Q.asIdeal) * ((ℓ : ℕ) : 𝓞 E ⧸ Q.asIdeal) +
            (v : 𝓞 E ⧸ Q.asIdeal) *
              ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : 𝓞 E ⧸ Q.asIdeal) := by
            push_cast
            ring
        _ = 0 := by rw [hsum0, hqzero, mul_zero, mul_zero, add_zero]
    exact one_ne_zero h4
  -- exact order `ℓ`, dividing the order of the unit group
  have horder : orderOf ζbar = ℓ := by
    have hdvd : orderOf ζbar ∣ ℓ := orderOf_dvd_of_pow_eq_one hζpow
    rcases hℓ.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hζne1
    · exact h1
  have hζbar_ne : ζbar ≠ 0 := by
    intro h0
    rw [h0, zero_pow hℓ.pos.ne'] at hζpow
    exact zero_ne_one hζpow
  have hpow1 : ζbar ^ (Nat.card (𝓞 E ⧸ Q.asIdeal) - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one ζbar hζbar_ne
  have hdvd1 : ℓ ∣ Nat.card (𝓞 E ⧸ Q.asIdeal) - 1 := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow1
  have hq2 : 2 ≤ Nat.card (𝓞 E ⧸ Q.asIdeal) := hq.two_le
  calc ((Nat.card (𝓞 E ⧸ Q.asIdeal) : ℕ) : ZMod ℓ)
      = (((Nat.card (𝓞 E ⧸ Q.asIdeal) - 1) + 1 : ℕ) : ZMod ℓ) := by
        congr 1
        omega
    _ = ((Nat.card (𝓞 E ⧸ Q.asIdeal) - 1 : ℕ) : ZMod ℓ) + 1 := by
        push_cast
        ring
    _ = 0 + 1 := by rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd1]
    _ = 1 := zero_add 1

open IsDedekindDomain in
/-- **Uniform fiber bound for places over a rational prime**: a number
field `E` has at most `[𝓞 E : ℤ]` finite places of residue cardinality
a given prime `q`.  Each such place contains `q`, so the product of
the (distinct, prime) ideals of the fiber divides `(q)`; taking
absolute norms gives `q ^ #fiber ∣ q ^ [𝓞 E : ℤ]`
(`Ideal.absNorm_span_singleton` with `Algebra.norm_algebraMap`). -/
theorem natCard_setOf_natCard_quotient_eq_le
    (E : Type*) [Field E] [NumberField E] {q : ℕ} (hq : q.Prime) :
    Nat.card {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q} ≤ Module.finrank ℤ (𝓞 E) := by
  classical
  haveI hfinset : Finite {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q} :=
    (finite_setOf_natCard_quotient_eq E q).to_subtype
  haveI := Fintype.ofFinite {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q}
  have hinj : Function.Injective (fun Q : {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q} =>
      (Q : HeightOneSpectrum (𝓞 E)).asIdeal) := by
    intro Q₁ Q₂ h
    exact Subtype.ext (HeightOneSpectrum.ext h)
  set T : Finset (Ideal (𝓞 E)) := Finset.univ.image
    (fun Q : {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q} =>
      (Q : HeightOneSpectrum (𝓞 E)).asIdeal) with hT
  have hTcard : T.card = Nat.card {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q} := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Nat.card_eq_fintype_card]
  -- each member divides `(q)`
  have hqmem : ∀ Q : {Q : HeightOneSpectrum (𝓞 E) //
      Nat.card (𝓞 E ⧸ Q.asIdeal) = q},
      (Q : HeightOneSpectrum (𝓞 E)).asIdeal ∣
        Ideal.span {((q : ℕ) : 𝓞 E)} := by
    intro Q
    rw [Ideal.dvd_iff_le, Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    haveI : Finite (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Q.2]
      exact hq.ne_zero
    haveI := Fintype.ofFinite (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal)
    have h0 : ((Nat.card (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) : ℕ) :
        𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    rw [Q.2, ← map_natCast (Ideal.Quotient.mk
      (Q : HeightOneSpectrum (𝓞 E)).asIdeal),
      Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  -- the product of the fiber divides `(q)`
  have hproddvd : ∏ P ∈ T, P ∣ Ideal.span {((q : ℕ) : 𝓞 E)} := by
    refine Finset.prod_primes_dvd _ ?_ ?_
    · intro P hP
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.prime_of_isPrime (Q : HeightOneSpectrum (𝓞 E)).ne_bot
        (Q : HeightOneSpectrum (𝓞 E)).isPrime
    · intro P hP
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
      exact hqmem Q
  -- take absolute norms
  have hnormprod : Ideal.absNorm (∏ P ∈ T, P) = q ^ T.card := by
    rw [map_prod, Finset.prod_congr rfl (fun P hP => ?_), Finset.prod_const]
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Q.2
  have hnormspan : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 E)}) =
      q ^ Module.finrank ℤ (𝓞 E) := by
    rw [Ideal.absNorm_span_singleton,
      show ((q : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) ((q : ℕ) : ℤ) from
        (map_natCast (algebraMap ℤ (𝓞 E)) q).symm,
      Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast]
  have hdvdnorm : q ^ T.card ∣ q ^ Module.finrank ℤ (𝓞 E) := by
    rw [← hnormprod, ← hnormspan]
    obtain ⟨K, hK⟩ := hproddvd
    rw [hK, map_mul]
    exact dvd_mul_right _ _
  rw [← hTcard]
  exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvdnorm

open IsDedekindDomain in
/-- **Pullback comparison of degree-one prime sums**: the degree-one
prime sum of `E ⊇ F(ζ_ℓ)` away from `ℓ` is at most `[𝓞 E : ℤ]` times
the congruence-class prime sum `∑_{N P ≡ 1 (mod ℓ)} N P^{-s}` of `F`.
Each degree-one place `Q` of `E` pulls back to `P = Q ∩ 𝓞 F` with the
same residue cardinality
(`natCard_quotient_under_eq_of_natCard_prime`), which is
`≡ 1 (mod ℓ)` (`natCast_natCard_quotient_eq_one_of_prime`); the fibers
of `Q ↦ P` embed into the places of `E` of one fixed prime residue
cardinality, so have at most `[𝓞 E : ℤ]` elements
(`natCard_setOf_natCard_quotient_eq_le`). -/
theorem tsum_rpow_neg_natCard_quotient_prime_and_ne_le_finrank_mul_tsum
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ)
    (s : ℝ) :
    (∑' Q : {Q : HeightOneSpectrum (𝓞 E) //
        (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ},
      (Nat.card (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) : ℝ≥0∞) ^ (-s)) ≤
    (Module.finrank ℤ (𝓞 E) : ℝ≥0∞) *
      ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) := by
  classical
  -- residue cardinality is preserved under pullback
  have hcard : ∀ Q : HeightOneSpectrum (𝓞 E),
      (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime →
      Nat.card (𝓞 F ⧸ Q.asIdeal.under (𝓞 F)) = Nat.card (𝓞 E ⧸ Q.asIdeal) := by
    intro Q hq
    haveI := Q.isPrime
    exact natCard_quotient_under_eq_of_natCard_prime (A := 𝓞 F) Q.asIdeal hq
  have hPrime : ∀ Q : HeightOneSpectrum (𝓞 E),
      (Q.asIdeal.under (𝓞 F)).IsPrime := by
    intro Q
    haveI := Q.isPrime
    exact Ideal.IsPrime.under (𝓞 F) Q.asIdeal
  have hne_bot : ∀ Q : HeightOneSpectrum (𝓞 E),
      (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime → Q.asIdeal.under (𝓞 F) ≠ ⊥ := by
    intro Q hq hbot
    haveI := Q.isPrime
    haveI hfin : Finite (𝓞 F ⧸ Q.asIdeal.under (𝓞 F)) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hcard Q hq]
      exact hq.ne_zero
    have hinj : Function.Injective
        (Ideal.Quotient.mk (Q.asIdeal.under (𝓞 F))) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]
      exact hbot
    haveI : Finite (𝓞 F) := Finite.of_injective _ hinj
    exact not_finite (𝓞 F)
  -- the pullback map on the index subtypes
  set Φ : {Q : HeightOneSpectrum (𝓞 E) //
      (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ} →
      {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1} :=
    fun Q => ⟨⟨(Q : HeightOneSpectrum (𝓞 E)).asIdeal.under (𝓞 F),
      hPrime (Q : HeightOneSpectrum (𝓞 E)),
      hne_bot (Q : HeightOneSpectrum (𝓞 E)) Q.2.1⟩,
      by
        constructor
        · rw [hcard (Q : HeightOneSpectrum (𝓞 E)) Q.2.1]
          exact Q.2.1
        · rw [hcard (Q : HeightOneSpectrum (𝓞 E)) Q.2.1]
          exact natCast_natCard_quotient_eq_one_of_prime hℓ hζ
            (Q : HeightOneSpectrum (𝓞 E)) Q.2.1 Q.2.2⟩ with hΦdef
  have hNeq : ∀ Q : {Q : HeightOneSpectrum (𝓞 E) //
      (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ},
      Nat.card (𝓞 F ⧸ ((Φ Q : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1}) :
          HeightOneSpectrum (𝓞 F)).asIdeal) =
      Nat.card (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) := by
    intro Q
    rw [hΦdef]
    exact hcard (Q : HeightOneSpectrum (𝓞 E)) Q.2.1
  -- fiber bound
  have hfib : ∀ p : {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
      Nat.card ↥(Φ ⁻¹' {p}) ≤ Module.finrank ℤ (𝓞 E) := by
    intro p
    haveI hfin2 : Finite {Q : HeightOneSpectrum (𝓞 E) //
        Nat.card (𝓞 E ⧸ Q.asIdeal) =
          Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal)} :=
      (finite_setOf_natCard_quotient_eq E _).to_subtype
    have hmap : ∀ Qf : ↥(Φ ⁻¹' {p}),
        Nat.card (𝓞 E ⧸ ((Qf : {Q : HeightOneSpectrum (𝓞 E) //
          (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
          Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ}) :
            HeightOneSpectrum (𝓞 E)).asIdeal) =
        Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal) := by
      intro Qf
      have h1 : Φ Qf.1 = p := Qf.2
      have h2 := hNeq Qf.1
      rw [h1] at h2
      exact h2.symm
    refine le_trans (Nat.card_le_card_of_injective
      (fun Qf : ↥(Φ ⁻¹' {p}) =>
        (⟨((Qf : {Q : HeightOneSpectrum (𝓞 E) //
          (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
          Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ}) : HeightOneSpectrum (𝓞 E)),
          hmap Qf⟩ : {Q : HeightOneSpectrum (𝓞 E) //
            Nat.card (𝓞 E ⧸ Q.asIdeal) =
              Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal)}))
      ?_) (natCard_setOf_natCard_quotient_eq_le E p.2.1)
    intro Qf₁ Qf₂ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  -- fiberwise decomposition of the `E`-side sum
  calc ∑' Q : {Q : HeightOneSpectrum (𝓞 E) //
        (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧ Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ},
      (Nat.card (𝓞 E ⧸ (Q : HeightOneSpectrum (𝓞 E)).asIdeal) : ℝ≥0∞) ^ (-s)
      = ∑' Q : {Q : HeightOneSpectrum (𝓞 E) //
          (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
          Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ},
        (Nat.card (𝓞 F ⧸ ((Φ Q : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1}) :
            HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) :=
        tsum_congr fun Q => by rw [hNeq Q]
    _ = ∑' p : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        ∑' Qf : ↥(Φ ⁻¹' {p}),
          (Nat.card (𝓞 F ⧸ ((Φ (Qf : {Q : HeightOneSpectrum (𝓞 E) //
            (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
            Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ}) :
              {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1}) :
              HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) :=
        (ENNReal.tsum_fiberwise _ Φ).symm
    _ ≤ ∑' p : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        (Module.finrank ℤ (𝓞 E) : ℝ≥0∞) *
          (Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
            (-s) := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        calc ∑' Qf : ↥(Φ ⁻¹' {p}),
              (Nat.card (𝓞 F ⧸ ((Φ (Qf : {Q : HeightOneSpectrum (𝓞 E) //
                (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
                Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ}) :
                  {P : HeightOneSpectrum (𝓞 F) //
                    (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                    ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1}) :
                  HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)
            = ∑' _Qf : ↥(Φ ⁻¹' {p}),
              (Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal) :
                ℝ≥0∞) ^ (-s) :=
              tsum_congr fun Qf => by
                rw [show Φ Qf.1 = p from Qf.2]
          _ = ENat.card ↥(Φ ⁻¹' {p}) *
              (Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal) :
                ℝ≥0∞) ^ (-s) := ENNReal.tsum_const _
          _ ≤ (Module.finrank ℤ (𝓞 E) : ℝ≥0∞) *
              (Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal) :
                ℝ≥0∞) ^ (-s) := by
              gcongr
              haveI hfibfin : Finite ↥(Φ ⁻¹' {p}) := by
                haveI : Finite {Q : HeightOneSpectrum (𝓞 E) //
                    Nat.card (𝓞 E ⧸ Q.asIdeal) =
                      Nat.card (𝓞 F ⧸ (p : HeightOneSpectrum (𝓞 F)).asIdeal)} :=
                  (finite_setOf_natCard_quotient_eq E _).to_subtype
                refine Finite.of_injective (fun Qf : ↥(Φ ⁻¹' {p}) =>
                  (⟨((Qf : {Q : HeightOneSpectrum (𝓞 E) //
                    (Nat.card (𝓞 E ⧸ Q.asIdeal)).Prime ∧
                    Nat.card (𝓞 E ⧸ Q.asIdeal) ≠ ℓ}) :
                      HeightOneSpectrum (𝓞 E)),
                    by
                      have h1 : Φ Qf.1 = p := Qf.2
                      have h2 := hNeq Qf.1
                      rw [h1] at h2
                      exact h2.symm⟩ :
                    {Q : HeightOneSpectrum (𝓞 E) //
                      Nat.card (𝓞 E ⧸ Q.asIdeal) =
                        Nat.card (𝓞 F ⧸
                          (p : HeightOneSpectrum (𝓞 F)).asIdeal)})) ?_
                intro Qf₁ Qf₂ h
                simp only [Subtype.mk.injEq] at h
                exact Subtype.ext (Subtype.ext h)
              rw [ENat.card_eq_coe_natCard]
              exact_mod_cast hfib p
    _ = (Module.finrank ℤ (𝓞 E) : ℝ≥0∞) *
        ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^
          (-s) := ENNReal.tsum_mul_left

open IsDedekindDomain in
/-- **Divergence of the congruence-class prime sum of `F` at `1⁺`**:
the sum `∑_{N P ≡ 1 (mod ℓ)} N P^{-s}` over degree-one places of `F`
in the split class exceeds any `C ≠ ⊤` for some `s > 1`.  DERIVED:
the degree-one prime sum of `E ⊇ F(ζ_ℓ)` away from `ℓ` diverges
(`exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne E ℓ`, through
the pole of `ζ_E`), and is at most `[𝓞 E : ℤ]` times the split-class
sum of `F`
(`tsum_rpow_neg_natCard_quotient_prime_and_ne_le_finrank_mul_tsum`). -/
theorem exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_one
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ s : ℝ, 1 < s ∧ C < ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) = 1},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) := by
  obtain ⟨s, hs1, hsgt⟩ :=
    exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne E ℓ
      ((Module.finrank ℤ (𝓞 E) : ℝ≥0∞) * C)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC)
  refine ⟨s, hs1, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  refine absurd hsgt (not_lt.mpr ?_)
  refine (tsum_rpow_neg_natCard_quotient_prime_and_ne_le_finrank_mul_tsum
    (F := F) hℓ hζ s).trans ?_
  gcongr

open IsDedekindDomain in
/-- **Nonvanishing of the continued twisted `L`-value at `s = 1`**
(sorry leaf) — the arithmetic core of `L(1, χ) ≠ 0`, isolated from all
continuation analysis: the extended value
`∫_{t > 1} A(⌊t⌋)·t^{-2}` of the twisted ideal `L`-series at `s = 1`
(`A(n) = ∑_{k ≤ n} χ(k)·#{I : N(I) = k}`, the continuation supplied by
`tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le`) is nonzero, for
`χ mod ℓ` nontrivial on the image of `Gal(E/F)`. Intended proof: the
classical factorization argument over the fixed field `E'` of
`ker(χ|_{Gal(E/F)})`: `ζ_{E'}(s) = ζ_F(s)·∏_ψ L(s, ψ)·(finitely many
ramified Euler corrections)`; were the continued value `0`, the simple
pole of `ζ_F` at `1` (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`,
`NumberField.dedekindZeta_residue_pos`, both in the pin) would be
cancelled by the zero, keeping `ζ_{E'}` bounded as `s → 1⁺`,
contradicting its own divergence (the zeta-half divergence machinery
proven in this file: `exists_one_lt_lt_tsum_rpow_neg_absNorm`). -/
theorem integral_sum_dirichletCharacter_mul_card_cpow_neg_two_ne_zero
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    (∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) *
      (t : ℂ) ^ (-(2 : ℂ))) ≠ 0 :=
  sorry

open IsDedekindDomain in
/-- **The twisted `L`-series is bounded away from `0` just right of
`s = 1`** — the `L(1, χ) ≠ 0` half of the good behaviour, isolated on
an interval `(1, 1 + η]`. DERIVED from two strictly shallower leaves:
the continuation
`tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le` (PROVEN: the
integral representation extends `L` continuously to `s = 1` by
dominated convergence, dominator `C·t^{r-2}`, given the power-saving
cancellation `exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow`)
and the sorried arithmetic core
`integral_sum_dirichletCharacter_mul_card_cpow_neg_two_ne_zero` (the
continued value `L(1) = ∫_{t > 1} A(⌊t⌋)·t^{-2}` is nonzero — the
classical zeta-factorization argument; see its docstring). With those,
the lower bound `‖L(1)‖/2` holds on some `(1, 1 + η]` by continuity. -/
theorem exists_forall_le_norm_LSeries_near_one
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ s : ℝ, 1 < s → s ≤ 1 + η →
      c ≤ ‖LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s‖ := by
  classical
  obtain ⟨r, C, hr0, hr1, hC, hbound⟩ :=
    exists_forall_norm_sum_dirichletCharacter_mul_card_absNorm_le_rpow
      hℓ hζ χ hχ
  -- the continued value at `s = 1` and its nonvanishing
  have hL1ne := integral_sum_dirichletCharacter_mul_card_cpow_neg_two_ne_zero
    hℓ hζ χ hχ
  have hL1pos : 0 < ‖∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) *
      (t : ℂ) ^ (-(2 : ℂ))‖ := norm_pos_iff.mpr hL1ne
  -- continuation to `1⁺`
  have htend := tendsto_LSeries_nhdsGT_one_of_forall_norm_sum_le hr0 hr1 hC
    hbound (fun s hs => lSeriesSummable_dirichletCharacter_mul_card F χ hs)
  -- eventually the norm exceeds half the limit norm
  have hev : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      ‖∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) *
        (t : ℂ) ^ (-(2 : ℂ))‖ / 2 ≤
      ‖LSeries (fun k : ℕ => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) (s : ℂ)‖ := by
    refine htend.norm.eventually ?_
    filter_upwards [lt_mem_nhds (half_lt_self hL1pos)] with x hx
    exact hx.le
  obtain ⟨u, hu, hIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨u - 1, _, by linarith [Set.mem_Ioi.mp hu], half_pos hL1pos,
    fun s hs1 hs2 => ?_⟩
  exact hIoc ⟨hs1, by linarith⟩

open IsDedekindDomain in
/-- **Good behaviour of the twisted `L`-series on `[1, 2]`** —
the analytic-continuation-plus-nonvanishing core, now separated
from all Euler-product and prime-sum bookkeeping: for a cyclotomic
extension `E = F(ζ_ℓ)` (`ℓ` prime) and a Dirichlet character `χ mod ℓ`
(values in `ℂ`) nontrivial on the image of `Gal(E/F)` in `(ZMod ℓ)ˣ`
(hypothesis `hχ`, phrased through the Galois action on `ζ`), the
`χ`-twisted ideal Dirichlet series `L(s) = ∑_k χ(k)·#{I : N(I) = k}/k^s`
is, uniformly for real `s ∈ (1, 2]`, bounded away from `0` (some
`0 < c ≤ ‖L(s)‖`) and bounded above together with its derivative
(`‖L(s)‖ ≤ C`, `‖L'(s)‖ ≤ C`).

DERIVED from the two strictly shallower sorried leaves above — the
continuation half `exists_forall_norm_LSeries_le_and_norm_deriv_le`
(uniform bounds for `L` and `L'` on `(1, 2]`) and the nonvanishing
half `exists_forall_le_norm_LSeries_near_one` (`c ≤ ‖L‖` on some
`(1, 1 + η]`) — with the away-from-`1` lower bound proven here: on
`[1 + η, 2]` the Euler identity
`exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries`
gives `‖L(s)‖ = exp(Re 𝒮(s)) ≥ exp(-‖𝒮(s)‖) ≥
exp(-3/2·∑_P N(P)^{-(1+η)})`, a positive constant; see the two leaves'
docstrings for the Hecke-counting and zeta-factorization routes and
the state of the mathlib pin. -/
theorem exists_forall_le_norm_LSeries_and_norm_deriv_LSeries_le
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    ∃ c C : ℝ, 0 < c ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      c ≤ ‖LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s‖ ∧
      ‖LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s‖ ≤ C ∧
      ‖deriv (LSeries (fun k => χ (k : ZMod ℓ) *
          (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))) s‖ ≤ C := by
  classical
  obtain ⟨C, hCb⟩ :=
    exists_forall_norm_LSeries_le_and_norm_deriv_le hℓ hζ χ hχ
  obtain ⟨η, c₁, hη, hc₁, hlow1⟩ :=
    exists_forall_le_norm_LSeries_near_one hℓ hζ χ hχ
  -- away from `1`, the Euler identity `L = exp 𝒮` keeps `L` away from `0`
  have hlow2 : ∀ s : ℝ, 1 + η ≤ s → s ≤ 2 →
      Real.exp (-(3 / 2 *
        ∑' P : HeightOneSpectrum (𝓞 F),
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + η)))) ≤
      ‖LSeries (fun k => χ (k : ZMod ℓ) *
        (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ)) s‖ := by
    intro s hs1 hs2
    have hs : (1 : ℝ) < s := by linarith
    have hsre : (1 : ℝ) < ((s : ℂ)).re := by
      rwa [Complex.ofReal_re]
    -- the log factors at `s`, and their norm sum
    have hzb : ∀ P : HeightOneSpectrum (𝓞 F),
        ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))‖ ≤
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) := by
      intro P
      have hNpos : 0 < Nat.card (𝓞 F ⧸ P.asIdeal) := by
        have h := two_le_natCard_quotient P
        omega
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re,
        Complex.ofReal_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (DirichletCharacter.norm_le_one χ _)
    have hlogb : ∀ P : HeightOneSpectrum (𝓞 F),
        ‖-Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ ≤
          3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) := by
      intro P
      have h2N : (2 : ℝ) ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
        exact_mod_cast two_le_natCard_quotient P
      have h6 : ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
        rw [norm_neg]
        refine le_trans (hzb P) ?_
        calc (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)
            ≤ (2 : ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos two_pos h2N (by linarith)
          _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
              (Real.rpow_le_rpow_left_iff one_lt_two).mpr (by linarith)
          _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
      rw [norm_neg]
      calc ‖Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖
          = ‖Complex.log (1 + -(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))))‖ := by
            rw [sub_eq_add_neg]
        _ ≤ 3 / 2 * ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ :=
            Complex.norm_log_one_add_half_le_self h6
        _ = 3 / 2 * ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))‖ := by rw [norm_neg]
        _ ≤ 3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_left (hzb P) (by norm_num)
    have hsum_s : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) :=
      summable_rpow_neg_natCard_quotient hs
    have hlogsum : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
        ‖-Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hlogb
        (hsum_s.mul_left _)
    -- `‖𝒮 s‖ ≤ 3/2 · ∑ N(P)^{-(1+η)}`
    have hSb : ‖∑' P : HeightOneSpectrum (𝓞 F),
        -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)))‖ ≤
        3 / 2 * ∑' P : HeightOneSpectrum (𝓞 F),
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + η)) := by
      refine le_trans (norm_tsum_le_tsum_norm hlogsum) ?_
      rw [← Summable.tsum_mul_left]
      · refine hlogsum.tsum_le_tsum ?_
          ((summable_rpow_neg_natCard_quotient
            (by linarith : (1 : ℝ) < 1 + η)).mul_left _)
        intro P
        refine le_trans (hlogb P) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        have hN1 : (1 : ℝ) < (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
          have h3 := two_le_natCard_quotient P
          exact_mod_cast (by omega : 1 < Nat.card (𝓞 F ⧸ P.asIdeal))
        exact (Real.rpow_le_rpow_left_iff hN1).mpr (by linarith)
      · exact summable_rpow_neg_natCard_quotient
          (by linarith : (1 : ℝ) < 1 + η)
    -- conclude through `L = exp 𝒮`
    rw [← exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries
      F χ hsre, Complex.norm_exp, Real.exp_le_exp]
    refine le_trans (neg_le_neg hSb) ?_
    have h12 := Complex.abs_re_le_norm (∑' P : HeightOneSpectrum (𝓞 F),
      -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ))))
    have h13 := abs_le.mp h12
    linarith [h13.1]
  refine ⟨min c₁ (Real.exp (-(3 / 2 *
      ∑' P : HeightOneSpectrum (𝓞 F),
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + η))))), C,
    lt_min hc₁ (Real.exp_pos _), ?_⟩
  intro s hs hs2
  obtain ⟨hup, hder⟩ := hCb s hs hs2
  refine ⟨?_, hup, hder⟩
  rcases le_or_gt s (1 + η) with hcase | hcase
  · exact le_trans (min_le_left _ _) (hlow1 s hs hcase)
  · exact le_trans (min_le_right _ _) (hlow2 s hcase.le hs2)

open IsDedekindDomain in
/-- **Boundedness near `s = 1` of the nontrivial Dirichlet character sums
over degree-one primes** — the `L(1, χ) ≠ 0` core of the
Chebotarev/Dirichlet argument, stripped of ALL bookkeeping: for a
cyclotomic extension `E = F(ζ_ℓ)` (`ℓ` prime) and a Dirichlet character
`χ mod ℓ` (with values in `ℂ`) that is nontrivial on the image of
`Gal(E/F)` in `(ZMod ℓ)ˣ` (hypothesis `hχ`, phrased through the Galois
action on `ζ`: some `ρ` acts by an exponent `n` with `χ n ≠ 1`), the sum
`S_χ(s) = ∑_P χ(N P) · N P ^ (-s)` over the degree-one places of `F`
away from `ℓ` is bounded uniformly in `s > 1`.

DERIVED from the two strictly shallower sorried leaves above — the
Euler-product identity
`exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries`
(`exp 𝒮 = L` on `re w > 1`, pure unique-factorization bookkeeping) and
the good-behaviour leaf
`exists_forall_le_norm_LSeries_and_norm_deriv_LSeries_le`
(`0 < c ≤ ‖L‖ ≤ C` and `‖L'‖ ≤ C` on real `(1, 2]` — the
continuation-plus-nonvanishing core; see its docstring for the Hecke
route and the state of the mathlib pin) — with all glue proven here:
for `s ≥ 3/2` the sum is dominated termwise by its value at `3/2`; on
`(1, 3/2]` the full prime log-sum `𝒮` is `ℂ`-differentiable on
`re w > 1` (Weierstrass, `Complex.differentiableOn_tsum_of_summable_norm`),
`exp ∘ 𝒮 = L` forces `𝒮' = L'/L`, so `‖𝒮'‖ ≤ C/c` and the mean value
inequality bounds `𝒮` on `[s, 3/2]` by its value at `3/2` plus `C/(2c)`;
finally `𝒮 - S_χ` is uniformly bounded by the log-Taylor remainders
(`≤ ∑ N(P)⁻²`) plus the higher-degree places (`≤ ∑_{N(P) not prime}
N(P)⁻¹`, the zeta-half tail leaf), the `ℓ`-power norms contributing `0`
through `χ`. -/
theorem exists_forall_norm_tsum_dirichletCharacter_mul_rpow_neg_le
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (χ : DirichletCharacter ℂ ℓ)
    (hχ : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :
    ∃ B : ℝ, ∀ s : ℝ, 1 < s →
      ‖∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
          (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) : ℝ) :
            ℂ)‖ ≤ B := by
  classical
  -- the degree-one character sum, the prime log-sum `𝒮` (complex
  -- variable), the twisted ideal `L`-series, and the tail constants
  set Sχ : ℝ → ℂ := fun t => ∑' P : {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
    χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
      (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-t) : ℝ) : ℂ)
  set 𝒮 : ℂ → ℂ := fun w => ∑' P : HeightOneSpectrum (𝓞 F),
    -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))
  set L : ℂ → ℂ := LSeries (fun k => χ (k : ZMod ℓ) *
    (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℂ))
  set B₀ : ℝ := ∑' P : {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
    (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-(3 / 2 : ℝ))
  set CR : ℝ := ∑' P : HeightOneSpectrum (𝓞 F),
    (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(2 : ℝ))
  set Cnp : ℝ := ∑' P : {P : HeightOneSpectrum (𝓞 F) //
      ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
    (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-(1 : ℝ))
  -- the two sorried analytic leaves
  have hEuler : ∀ w : ℂ, 1 < w.re → Complex.exp (𝒮 w) = L w := fun w hw =>
    exp_tsum_neg_log_one_sub_dirichletCharacter_mul_cpow_neg_eq_LSeries F χ hw
  obtain ⟨c, C, hc, hLbounds⟩ :=
    exists_forall_le_norm_LSeries_and_norm_deriv_LSeries_le hℓ hζ χ hχ
  -- `2 ≤ #(𝓞 F / P)` for every finite place
  have htwo : ∀ P : HeightOneSpectrum (𝓞 F), 2 ≤ Nat.card (𝓞 F ⧸ P.asIdeal) :=
    fun P => two_le_natCard_quotient P
  -- summability of the full place sum for every real `s > 1`
  have hAll : ∀ s : ℝ, 1 < s → Summable (fun P : HeightOneSpectrum (𝓞 F) =>
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) :=
    fun _ hs => summable_rpow_neg_natCard_quotient hs
  -- summability of the `N(P)⁻¹` sum over the higher-degree places
  have hnp : Summable (fun P : {P : HeightOneSpectrum (𝓞 F) //
      ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} =>
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-(1 : ℝ))) := by
    have h2 := tsum_not_prime_natCard_rpow_neg_one_ne_top F
    have h3 : ∀ P : {P : HeightOneSpectrum (𝓞 F) //
        ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-(1 : ℝ)) =
          (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : NNReal) ^
            (-(1 : ℝ)) : NNReal) : ℝ≥0∞) := by
      intro P
      rw [ENNReal.coe_rpow_of_ne_zero (by
          have h4 := htwo (P : HeightOneSpectrum (𝓞 F))
          exact_mod_cast (by omega :
            Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) ≠ 0)),
        ENNReal.coe_natCast]
    rw [tsum_congr h3] at h2
    have h4 := ENNReal.tsum_coe_ne_top_iff_summable.mp h2
    refine (NNReal.summable_coe.mpr h4).congr ?_
    intro P
    rw [NNReal.coe_rpow, NNReal.coe_natCast]
  -- termwise norm bound for the degree-one character sum
  have hterm : ∀ (t : ℝ) (P : HeightOneSpectrum (𝓞 F)),
      ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-t) : ℝ) : ℂ)‖ ≤
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-t) := by
    intro t P
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (DirichletCharacter.norm_le_one χ _)
  -- crude bound for `3/2 ≤ s`: absolute values, termwise monotone in `s`
  have hlarge : ∀ s : ℝ, (3 / 2 : ℝ) ≤ s → ‖Sχ s‖ ≤ B₀ := by
    intro s h32
    have hs : (1 : ℝ) < s := lt_of_lt_of_le (by norm_num) h32
    have hsub : Summable (fun P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} =>
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)) :=
      (hAll s hs).subtype _
    have hsub32 : Summable (fun P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} =>
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^
          (-(3 / 2 : ℝ))) :=
      (hAll (3 / 2) (by norm_num)).subtype _
    calc ‖Sχ s‖
        ≤ ∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :=
        tsum_of_norm_bounded hsub.hasSum fun P =>
          hterm s (P : HeightOneSpectrum (𝓞 F))
      _ ≤ B₀ := by
        refine hsub.tsum_le_tsum (fun P => ?_) hsub32
        have h2 : (1 : ℝ) <
            (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) := by
          have h3 := htwo (P : HeightOneSpectrum (𝓞 F))
          exact_mod_cast (by omega :
            1 < Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal))
        exact (Real.rpow_le_rpow_left_iff h2).mpr (by linarith)
  -- the norm of a factor `χ(N P)·N P^{-w}`, on `1 ≤ re w`, is at most
  -- `N P^{-re w} ≤ 1/2`
  have hzb : ∀ (P : HeightOneSpectrum (𝓞 F)) (w : ℂ),
      ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ ≤
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-w.re) := by
    intro P w
    have hNpos : 0 < Nat.card (𝓞 F ⧸ P.asIdeal) := by have h := htwo P; omega
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (DirichletCharacter.norm_le_one χ _)
  have hhalf : ∀ (P : HeightOneSpectrum (𝓞 F)) (x : ℝ), 1 ≤ x →
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-x) ≤ 1 / 2 := by
    intro P x hx
    have h2N : (2 : ℝ) ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
      exact_mod_cast htwo P
    calc (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-x)
        ≤ (2 : ℝ) ^ (-x) :=
          Real.rpow_le_rpow_of_nonpos two_pos h2N (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          (Real.rpow_le_rpow_left_iff one_lt_two).mpr (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  -- the prime log-sum is `ℂ`-differentiable on `re w > 1` (Weierstrass)
  have hdiff : ∀ w : ℂ, 1 < w.re → DifferentiableAt ℂ 𝒮 w := by
    intro w₀ hw₀
    have hε : 0 < (w₀.re - 1) / 2 := by linarith
    set ε : ℝ := (w₀.re - 1) / 2 with hεdef
    have hU : IsOpen {w : ℂ | 1 + ε < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hw₀U : w₀ ∈ {w : ℂ | 1 + ε < w.re} := by
      simp only [Set.mem_setOf_eq, hεdef]
      linarith
    have hsum : Summable (fun P : HeightOneSpectrum (𝓞 F) =>
        (3 / 2 : ℝ) * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + ε))) :=
      (hAll (1 + ε) (by linarith)).mul_left _
    -- on `U`, each factor norm is at most `N P^{-(1+ε)} ≤ 1/2`
    have hzU : ∀ (P : HeightOneSpectrum (𝓞 F)) (w : ℂ), w ∈ {w : ℂ | 1 + ε < w.re} →
        ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ ≤
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + ε)) := by
      intro P w hw
      simp only [Set.mem_setOf_eq] at hw
      have h5 : (1 : ℝ) < (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
        have h6 := htwo P
        exact_mod_cast (by omega : 1 < Nat.card (𝓞 F ⧸ P.asIdeal))
      exact le_trans (hzb P w) ((Real.rpow_le_rpow_left_iff h5).mpr (by linarith))
    -- each summand is differentiable on `U`
    have hdiffP : ∀ P : HeightOneSpectrum (𝓞 F), DifferentiableOn ℂ (fun w : ℂ =>
        -Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))) {w : ℂ | 1 + ε < w.re} := by
      intro P
      have hN0 : (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ≠ 0 := by
        have h6 := htwo P
        exact_mod_cast (by omega : Nat.card (𝓞 F ⧸ P.asIdeal) ≠ 0)
      have hinner : DifferentiableOn ℂ (fun w : ℂ =>
          1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)) {w : ℂ | 1 + ε < w.re} :=
        (differentiableOn_const _).sub
          (((differentiable_id.neg.const_cpow (Or.inl hN0)).differentiableOn).const_mul _)
      refine (DifferentiableOn.clog hinner ?_).neg
      intro w hw
      rw [Complex.mem_slitPlane_iff]
      left
      have h6 : ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ ≤ 1 / 2 := by
        refine le_trans (hzU P w hw) (hhalf P (1 + ε) (by linarith))
      have h7 := le_trans (Complex.abs_re_le_norm _) h6
      have h8 : (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)).re =
          1 - (χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)).re := by
        simp [Complex.sub_re, Complex.one_re]
      rw [h8]
      have h9 := abs_le.mp h7
      linarith [h9.2]
    -- uniform summable bound for the log factors on `U`
    have hlog : ∀ (P : HeightOneSpectrum (𝓞 F)) (w : ℂ), w ∈ {w : ℂ | 1 + ε < w.re} →
        ‖-Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖ ≤
          (3 / 2 : ℝ) * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + ε)) := by
      intro P w hw
      rw [norm_neg]
      have h6 : ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖ ≤ 1 / 2 := by
        rw [norm_neg]
        exact le_trans (hzU P w hw) (hhalf P (1 + ε) (by linarith))
      calc ‖Complex.log (1 - χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖
          = ‖Complex.log (1 + -(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)))‖ := by
            rw [sub_eq_add_neg]
        _ ≤ (3 / 2 : ℝ) * ‖-(χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w))‖ :=
            Complex.norm_log_one_add_half_le_self h6
        _ = (3 / 2 : ℝ) * ‖χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
              (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-w)‖ := by rw [norm_neg]
        _ ≤ (3 / 2 : ℝ) * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 + ε)) := by
            have h7 := hzU P w hw
            linarith
    exact (Complex.differentiableOn_tsum_of_summable_norm hsum hdiffP hU
      hlog).differentiableAt (hU.mem_nhds hw₀U)
  -- its derivative at real `t ∈ (1, 2]` is `L'/L`, hence bounded by `C/c`
  have hderiv : ∀ t : ℝ, 1 < t → t ≤ 2 → ‖deriv 𝒮 (t : ℂ)‖ ≤ C / c := by
    intro t ht ht2
    have hVopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have htV : (t : ℂ) ∈ {w : ℂ | 1 < w.re} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      exact ht
    -- `exp ∘ 𝒮` and `L` agree near `t`, so their derivatives agree
    have heq : (fun w => Complex.exp (𝒮 w)) =ᶠ[nhds (t : ℂ)] L :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds htV) fun w hw => hEuler w hw
    have h2 : HasDerivAt (fun w => Complex.exp (𝒮 w))
        (Complex.exp (𝒮 (t : ℂ)) * deriv 𝒮 (t : ℂ)) (t : ℂ) :=
      ((hdiff _ htV).hasDerivAt).cexp
    have h3 : deriv L (t : ℂ) = Complex.exp (𝒮 (t : ℂ)) * deriv 𝒮 (t : ℂ) :=
      (heq.deriv_eq).symm.trans h2.deriv
    obtain ⟨hlow, -, hder⟩ := hLbounds t ht ht2
    have h4 : c * ‖deriv 𝒮 (t : ℂ)‖ ≤ C := by
      calc c * ‖deriv 𝒮 (t : ℂ)‖
          ≤ ‖L (t : ℂ)‖ * ‖deriv 𝒮 (t : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hlow (norm_nonneg _)
        _ = ‖Complex.exp (𝒮 (t : ℂ))‖ * ‖deriv 𝒮 (t : ℂ)‖ := by
            rw [hEuler _ htV]
        _ = ‖deriv L (t : ℂ)‖ := by rw [h3, norm_mul]
        _ ≤ C := hder
    rw [le_div_iff₀ hc, mul_comm]
    exact h4
  -- mean value inequality on `[s, 3/2]`
  have hnear : ∀ s : ℝ, 1 < s → s ≤ 3 / 2 →
      ‖𝒮 (s : ℂ)‖ ≤ ‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (1 / 2) := by
    intro s hs hs32
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _)
      (hLbounds 2 (by norm_num) le_rfl).2.1
    have hg : ∀ x ∈ Set.Icc s (3 / 2 : ℝ),
        HasDerivWithinAt (fun u : ℝ => 𝒮 (u : ℂ)) (deriv 𝒮 ((x : ℝ) : ℂ))
          (Set.Icc s (3 / 2 : ℝ)) x := by
      intro x hx
      have hx1 : 1 < x := lt_of_lt_of_le hs hx.1
      have hxV : ((x : ℝ) : ℂ) ∈ {w : ℂ | 1 < w.re} := by
        simp only [Set.mem_setOf_eq, Complex.ofReal_re]
        exact hx1
      exact ((hdiff _ hxV).hasDerivAt).comp_ofReal.hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico s (3 / 2 : ℝ), ‖deriv 𝒮 ((x : ℝ) : ℂ)‖ ≤ C / c := by
      intro x hx
      exact hderiv x (lt_of_lt_of_le hs hx.1) (le_trans hx.2.le (by norm_num))
    have h1 := norm_image_sub_le_of_norm_deriv_le_segment' hg hbound (3 / 2 : ℝ)
      (Set.right_mem_Icc.mpr hs32)
    calc ‖𝒮 (s : ℂ)‖
        = ‖𝒮 ((3 / 2 : ℝ) : ℂ) - (𝒮 ((3 / 2 : ℝ) : ℂ) - 𝒮 (s : ℂ))‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + ‖𝒮 ((3 / 2 : ℝ) : ℂ) - 𝒮 (s : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ ‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (3 / 2 - s) := by
          gcongr
      _ ≤ ‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (1 / 2) := by
          have h2 : (0 : ℝ) ≤ C / c := div_nonneg hC0 hc.le
          have h3 : (3 / 2 : ℝ) - s ≤ 1 / 2 := by linarith
          gcongr
  -- uniform comparison of `𝒮` with the degree-one character sum: the
  -- log-Taylor remainders cost `CR`, the higher-degree places `Cnp`,
  -- and the places with `N(P) ∈ {ℓ, ℓ², …}` vanish under `χ`
  have htail : ∀ s : ℝ, 1 < s → ‖𝒮 (s : ℂ) - Sχ s‖ ≤ CR + Cnp := by
    intro s hs
    haveI : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
    -- the summands of `𝒮` at real `s`, in real-rpow form
    set z : HeightOneSpectrum (𝓞 F) → ℂ := fun P =>
      χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
        (((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) : ℝ) : ℂ) with hzdef
    have hcast : ∀ P : HeightOneSpectrum (𝓞 F),
        χ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ) *
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℂ) ^ (-(s : ℂ)) = z P := by
      intro P
      rw [hzdef]
      congr 1
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _) (-s), Complex.ofReal_neg,
        Complex.ofReal_natCast]
    have hzsum : Summable z := by
      refine Summable.of_norm_bounded (hAll s hs) ?_
      intro P
      exact hterm s P
    -- `𝒮 s` as the log-sum over `z`
    have h𝒮s : 𝒮 (s : ℂ) =
        ∑' P : HeightOneSpectrum (𝓞 F), -Complex.log (1 - z P) := by
      refine tsum_congr fun P => ?_
      rw [hcast P]
    -- `Sχ s` as the indicator sum of `z` over the degree-one places
    set T : Set (HeightOneSpectrum (𝓞 F)) :=
      {P | (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} with hTdef
    have hSχs : Sχ s = ∑' P : HeightOneSpectrum (𝓞 F), Set.indicator T z P :=
      tsum_subtype T z
    -- summability of the log factors and the indicator
    have hlogsum : Summable
        (fun P : HeightOneSpectrum (𝓞 F) => -Complex.log (1 - z P)) := by
      refine Summable.of_norm_bounded ((hAll s hs).mul_left (3 / 2 : ℝ)) ?_
      intro P
      have h6 : ‖-(z P)‖ ≤ 1 / 2 := by
        rw [norm_neg]
        exact le_trans (hterm s P) (hhalf P s hs.le)
      rw [norm_neg]
      calc ‖Complex.log (1 - z P)‖
          = ‖Complex.log (1 + -(z P))‖ := by rw [sub_eq_add_neg]
        _ ≤ 3 / 2 * ‖-(z P)‖ := Complex.norm_log_one_add_half_le_self h6
        _ = 3 / 2 * ‖z P‖ := by rw [norm_neg]
        _ ≤ 3 / 2 * (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_left (hterm s P) (by norm_num)
    have hindsum : Summable (Set.indicator T z) := hzsum.indicator T
    -- the difference as a single sum
    have hdiffsum : 𝒮 (s : ℂ) - Sχ s =
        ∑' P : HeightOneSpectrum (𝓞 F),
          (-Complex.log (1 - z P) - Set.indicator T z P) := by
      rw [h𝒮s, hSχs]
      exact (hlogsum.tsum_sub hindsum).symm
    -- the termwise bound
    set b : HeightOneSpectrum (𝓞 F) → ℝ := fun P =>
      (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(2 : ℝ)) +
        Set.indicator
          {P : HeightOneSpectrum (𝓞 F) | ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime}
          (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ))) P with hbdef
    have hnp' : Summable ((fun P : HeightOneSpectrum (𝓞 F) =>
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ))) ∘
        ((↑) : {P : HeightOneSpectrum (𝓞 F) //
          ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} → HeightOneSpectrum (𝓞 F))) := hnp
    have hind1 : Summable (Set.indicator
        {P : HeightOneSpectrum (𝓞 F) | ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime}
        (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ)))) :=
      summable_subtype_iff_indicator.mp hnp'
    have hbsum : Summable b := (hAll 2 (by norm_num)).add hind1
    have hpoint : ∀ P : HeightOneSpectrum (𝓞 F),
        ‖-Complex.log (1 - z P) - Set.indicator T z P‖ ≤ b P := by
      intro P
      have hz12 : ‖z P‖ ≤ 1 / 2 := le_trans (hterm s P) (hhalf P s hs.le)
      have hN1 : (1 : ℝ) < (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) := by
        have h3 := htwo P
        exact_mod_cast (by omega : 1 < Nat.card (𝓞 F ⧸ P.asIdeal))
      have hind_nonneg : 0 ≤ Set.indicator
          {P : HeightOneSpectrum (𝓞 F) | ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime}
          (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ))) P :=
        Set.indicator_apply_nonneg fun _ =>
          Real.rpow_nonneg (Nat.cast_nonneg _) _
      -- log-Taylor remainder bound
      have hrem : ‖-Complex.log (1 - z P) - z P‖ ≤
          (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(2 : ℝ)) := by
        have h7 : ‖-(z P)‖ < 1 := by rw [norm_neg]; linarith
        have h8 := Complex.norm_log_one_add_sub_self_le h7
        have h9 : -Complex.log (1 - z P) - z P =
            -(Complex.log (1 + -(z P)) - -(z P)) := by
          rw [sub_eq_add_neg (1 : ℂ) (z P)]
          ring
        rw [h9, norm_neg]
        refine le_trans h8 ?_
        rw [norm_neg]
        -- `‖z‖² (1-‖z‖)⁻¹ / 2 ≤ ‖z‖² ≤ N^{-s}·N^{-s} = N^{-2s} ≤ N^{-2}`
        have h10 : (1 - ‖z P‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) two_pos]
          linarith
        have h11 : ‖z P‖ ^ 2 * (1 - ‖z P‖)⁻¹ / 2 ≤ ‖z P‖ ^ 2 := by
          calc ‖z P‖ ^ 2 * (1 - ‖z P‖)⁻¹ / 2 ≤ ‖z P‖ ^ 2 * 2 / 2 := by
                gcongr
            _ = ‖z P‖ ^ 2 := by ring
        refine le_trans h11 ?_
        calc ‖z P‖ ^ 2
            ≤ ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) ^ 2 := by
              have h12 := hterm s P
              have h13 := norm_nonneg (z P)
              nlinarith
          _ = (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s + -s) := by
              rw [Real.rpow_add (by linarith : (0:ℝ) <
                (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ))]
              ring
          _ ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(2 : ℝ)) :=
              (Real.rpow_le_rpow_left_iff hN1).mpr (by linarith)
      by_cases hPT : P ∈ T
      · -- degree-one place away from `ℓ`: only the Taylor remainder remains
        rw [Set.indicator_of_mem hPT]
        refine le_trans hrem ?_
        rw [hbdef]
        exact le_add_of_nonneg_right hind_nonneg
      · rw [Set.indicator_of_notMem hPT, sub_zero]
        by_cases hprime : (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime
        · -- residue cardinality `ℓ`: the character kills the factor
          have hNℓ : Nat.card (𝓞 F ⧸ P.asIdeal) = ℓ := by
            by_contra hne
            exact hPT ⟨hprime, hne⟩
          have hz0 : z P = 0 := by
            rw [hzdef]
            simp only [hNℓ, ZMod.natCast_self]
            rw [MulChar.map_nonunit χ not_isUnit_zero, zero_mul]
          rw [hz0, sub_zero, Complex.log_one, neg_zero, norm_zero, hbdef]
          exact add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hind_nonneg
        · -- higher-degree place: remainder plus first-order term
          have hmem : P ∈ {P : HeightOneSpectrum (𝓞 F) |
              ¬ (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime} := hprime
          calc ‖-Complex.log (1 - z P)‖
              = ‖(-Complex.log (1 - z P) - z P) + z P‖ := by
                rw [sub_add_cancel]
            _ ≤ ‖-Complex.log (1 - z P) - z P‖ + ‖z P‖ := norm_add_le _ _
            _ ≤ (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(2 : ℝ)) +
                (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ)) := by
                refine add_le_add hrem (le_trans (hterm s P) ?_)
                exact (Real.rpow_le_rpow_left_iff hN1).mpr (by linarith)
            _ = b P := by
                rw [hbdef]
                congr 1
                exact (Set.indicator_of_mem hmem
                  (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-(1 : ℝ)))).symm
    -- assemble
    calc ‖𝒮 (s : ℂ) - Sχ s‖
        = ‖∑' P : HeightOneSpectrum (𝓞 F),
            (-Complex.log (1 - z P) - Set.indicator T z P)‖ := by rw [hdiffsum]
      _ ≤ ∑' P : HeightOneSpectrum (𝓞 F), b P :=
          tsum_of_norm_bounded hbsum.hasSum hpoint
      _ = CR + Cnp := by
          rw [hbdef]
          rw [(hAll 2 (by norm_num)).tsum_add hind1]
          congr 1
          exact (tsum_subtype _ _).symm
  -- assemble the uniform bound
  refine ⟨max B₀ ((CR + Cnp) + (‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (1 / 2))), ?_⟩
  intro s hs
  show ‖Sχ s‖ ≤ _
  rcases le_or_gt (3 / 2 : ℝ) s with h32 | h32
  · exact le_max_of_le_left (hlarge s h32)
  · refine le_max_of_le_right ?_
    calc ‖Sχ s‖ = ‖𝒮 (s : ℂ) - (𝒮 (s : ℂ) - Sχ s)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖𝒮 (s : ℂ)‖ + ‖𝒮 (s : ℂ) - Sχ s‖ := norm_sub_le _ _
      _ ≤ (‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (1 / 2)) + (CR + Cnp) :=
          add_le_add (hnear s hs h32.le) (htail s hs)
      _ = (CR + Cnp) + (‖𝒮 ((3 / 2 : ℝ) : ℂ)‖ + C / c * (1 / 2)) := by ring

open IsDedekindDomain in
/-- **Pairwise comparison of cyclotomic congruence classes of degree-one
primes** — the `L`-function core of Deuring's route: for a cyclotomic
extension `E = F(ζ_ℓ)` (`ℓ` prime) and ANY `σ, τ ∈ Gal(E/F)`, the
degree-one prime sum over the congruence class of `σ` (the places with
`σ ζ = ζ ^ #(𝓞 F / P)`) exceeds that over the class of `τ` by an error
bounded uniformly in `s > 1`. Both sums are `ℝ≥0∞`-valued, so no
summability side conditions appear, and the bounded error is additive —
no `ENNReal` subtraction.

DERIVED from the two strictly shallower sorried leaves above by
character orthogonality, all bookkeeping proven here: by
`tsum_rpow_neg_natCard_quotient_prime_and_ne_ne_top` the sums are finite
for fixed `s > 1`, so the claim is real-valued; the congruence class of
`ρ` is cut out of the degree-one primes by the condition
`N P ≡ autToPow ρ (mod ℓ)` (`IsPrimitiveRoot.autToPow_spec`), and the
second orthogonality relation for the Dirichlet characters mod `ℓ`
(`DirichletCharacter.sum_char_inv_mul_char_eq`, available in the pin
since `ℂ` has enough roots of unity) expresses `φ(ℓ) · ∑_{class ρ}` as
`∑_χ χ(a_ρ)⁻¹ S_χ(s)` with `a_ρ = autToPow ρ`; in the difference
`φ(ℓ) (∑_{class σ} - ∑_{class τ})` every character TRIVIAL on the image
of `Gal(E/F)` cancels exactly (`χ(a_σ)⁻¹ = χ(a_τ)⁻¹ = 1` — this is
where the unbounded `S_χ = S_1`-type terms disappear), and each
remaining character sum is uniformly bounded by the deep leaf
`exists_forall_norm_tsum_dirichletCharacter_mul_rpow_neg_le`. -/
theorem tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow_le_tsum_add
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (σ τ : E ≃ₐ[F] E) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ s : ℝ, 1 < s →
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) ≤
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) + B := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  -- the congruence-class condition forces the residue characteristic away from `ℓ`
  have hclassne : ∀ (ρ : E ≃ₐ[F] E) (P : HeightOneSpectrum (𝓞 F)),
      ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal) → Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ := by
    intro ρ P hρ hcontra
    rw [hcontra, hζ.pow_eq_one] at hρ
    exact hζ.ne_one hℓ.one_lt (ρ.injective (hρ.trans (map_one ρ).symm))
  -- the congruence-class condition, read in `ZMod ℓ` through `autToPow`
  have hcond : ∀ (ρ : E ≃ₐ[F] E) (m : ℕ),
      ρ ζ = ζ ^ m ↔ ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) = (m : ZMod ℓ) := by
    have hford : IsOfFinOrder ζ :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨ℓ, hℓ.pos, hζ.pow_eq_one⟩
    intro ρ m
    have hspec := hζ.autToPow_spec F ρ
    constructor
    · intro h
      have h1 : ζ ^ ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ).val = ζ ^ m := by
        rw [hspec, h]
      have h2 := hford.pow_eq_pow_iff_modEq.mp h1
      rw [← hζ.eq_orderOf] at h2
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
      rwa [ZMod.natCast_val, ZMod.cast_id] at h3
    · intro h
      have h2 : ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ).val ≡ m [MOD ℓ] := by
        rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.cast_id]
        exact h
      rw [← hspec]
      exact hford.pow_eq_pow_iff_modEq.mpr (hζ.eq_orderOf ▸ h2)
  -- the deep leaf, with a bound chosen uniformly for every character
  have hbdd : ∀ χ : DirichletCharacter ℂ ℓ, ∃ B : ℝ,
      (∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) →
      ∀ s : ℝ, 1 < s →
        ‖∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
            (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) : ℝ) :
              ℂ)‖ ≤ B := by
    intro χ
    by_cases h : ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1
    · obtain ⟨B, hB⟩ :=
        exists_forall_norm_tsum_dirichletCharacter_mul_rpow_neg_le hℓ hζ χ h
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun hc => absurd hc h⟩
  choose Bc hBc using hbdd
  refine ⟨ENNReal.ofReal
      ((∑ χ : DirichletCharacter ℂ ℓ, |Bc χ| * 2) / (ℓ.totient : ℝ)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro s hs
  -- the real degree-one family is summable (transfer from the finiteness leaf)
  have hsum : Summable (fun P : {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} =>
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)) := by
    have h1 := tsum_rpow_neg_natCard_quotient_prime_and_ne_ne_top F ℓ hs
    have h2 : ∀ P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) =
        (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : NNReal) ^ (-s) :
          NNReal) : ℝ≥0∞) := by
      intro P
      rw [ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast P.2.1.ne_zero),
        ENNReal.coe_natCast]
    rw [tsum_congr h2] at h1
    have h3 := ENNReal.tsum_coe_ne_top_iff_summable.mp h1
    refine (NNReal.summable_coe.mpr h3).congr ?_
    intro P
    rw [NNReal.coe_rpow, NNReal.coe_natCast]
  -- the complex character families are dominated by the real family
  have hsumχ : ∀ χ : DirichletCharacter ℂ ℓ,
      Summable (fun P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} =>
        χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
          (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) : ℝ) :
            ℂ)) := by
    intro χ
    refine Summable.of_norm_bounded hsum ?_
    intro P
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    calc ‖χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)‖ *
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
        ≤ 1 * (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) := by
          gcongr
          exact χ.norm_le_one _
      _ = (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :=
          one_mul _
  -- the `ℝ≥0∞`-valued class sums are finite
  have hSne : ∀ ρ : E ≃ₐ[F] E,
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) ≠ ⊤ := by
    intro ρ
    refine ne_top_of_le_ne_top
      (tsum_rpow_neg_natCard_quotient_prime_and_ne_ne_top F ℓ hs) ?_
    exact ENNReal.tsum_mono_subtype
      (fun P : HeightOneSpectrum (𝓞 F) =>
        (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s))
      (fun P hP => ⟨hP.1, hclassne ρ P hP.2⟩)
  -- their `toReal` is the real class sum
  have htoReal : ∀ ρ : E ≃ₐ[F] E,
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)).toReal =
      ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) := by
    intro ρ
    rw [ENNReal.tsum_toReal_eq (fun P => by
      refine ENNReal.rpow_ne_top_of_ne_zero ?_ (ENNReal.natCast_ne_top _)
      exact_mod_cast P.2.1.ne_zero)]
    exact tsum_congr fun P => by
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_natCast]
  -- the real class sum, as an indicator sum over all degree-one places
  have hindic : ∀ ρ : E ≃ₐ[F] E,
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)) =
      ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
            ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
          then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
          else 0) := by
    intro ρ
    calc (∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
            ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s))
        = ∑' P : HeightOneSpectrum (𝓞 F),
            Set.indicator {P : HeightOneSpectrum (𝓞 F) |
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}
              (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s)) P :=
          tsum_subtype {P : HeightOneSpectrum (𝓞 F) |
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
              ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}
            (fun P => (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s))
      _ = ∑' P : HeightOneSpectrum (𝓞 F),
            Set.indicator {P : HeightOneSpectrum (𝓞 F) |
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ}
              (fun P => if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) else 0) P := by
          refine tsum_congr fun P => ?_
          rw [Set.indicator_apply, Set.indicator_apply]
          by_cases h1 : P ∈ {P : HeightOneSpectrum (𝓞 F) |
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
              ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}
          · rw [if_pos h1,
              if_pos (show P ∈ {P : HeightOneSpectrum (𝓞 F) |
                  (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                  Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} from
                ⟨h1.1, hclassne ρ P h1.2⟩),
              if_pos ((hcond ρ _).mp h1.2)]
          · rw [if_neg h1]
            by_cases h2 : P ∈ {P : HeightOneSpectrum (𝓞 F) |
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
                Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ}
            · rw [if_pos h2,
                if_neg fun hcontra => h1 ⟨h2.1, (hcond ρ _).mpr hcontra⟩]
            · rw [if_neg h2]
      _ = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          (if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
              ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
            then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
            else 0) :=
          (tsum_subtype {P : HeightOneSpectrum (𝓞 F) |
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
              Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ}
            (fun P => if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ P.asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ) ^ (-s) else 0)).symm
  -- orthogonality: `φ(ℓ) ×` the indicator sum is the character-average
  have hkey : ∀ ρ : E ≃ₐ[F] E,
      ((ℓ.totient : ℕ) : ℂ) *
        ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          (if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
              ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
            then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
            else 0) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ ℓ,
        χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) *
          ∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
              (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                ℝ) : ℂ) := by
    intro ρ
    have hunit : IsUnit ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) :=
      (hζ.autToPow F ρ).isUnit
    symm
    calc ∑ χ : DirichletCharacter ℂ ℓ,
          χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) *
            ∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
                (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                  ℝ) : ℂ)
        = ∑ χ : DirichletCharacter ℂ ℓ,
            ∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) *
                (χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
                  (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                    ℝ) : ℂ)) :=
          Finset.sum_congr rfl fun χ _ => tsum_mul_left.symm
      _ = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            ∑ χ : DirichletCharacter ℂ ℓ,
              χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) *
                (χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
                  (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                    ℝ) : ℂ)) :=
          (Summable.tsum_finsetSum fun χ _ => (hsumχ χ).mul_left _).symm
      _ = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (∑ χ : DirichletCharacter ℂ ℓ,
              χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) *
                χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)) *
              (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                ℝ) : ℂ) :=
          tsum_congr fun P => by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
      _ = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then ((ℓ.totient : ℕ) : ℂ) else 0) *
              (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                ℝ) : ℂ) :=
          tsum_congr fun P => by
            rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit _]
      _ = ∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            ((ℓ.totient : ℕ) : ℂ) *
              ((if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0 : ℝ) : ℂ) :=
          tsum_congr fun P => by
            by_cases h : ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h, zero_mul, Complex.ofReal_zero, mul_zero]
      _ = ((ℓ.totient : ℕ) : ℂ) *
            ∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              ((if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0 : ℝ) : ℂ) :=
          tsum_mul_left
      _ = ((ℓ.totient : ℕ) : ℂ) *
            ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              (if ((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0) : ℝ) : ℂ) := by
          rw [Complex.ofReal_tsum]
  -- characters trivial on the image of the Galois group drop out of the difference
  have hcancel : ∀ χ : DirichletCharacter ℂ ℓ,
      ¬(∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) →
      ∀ ρ : E ≃ₐ[F] E, χ ((((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) = 1 := by
    intro χ hχ ρ
    push Not at hχ
    have h1 : ∀ ρ' : E ≃ₐ[F] E,
        χ ((hζ.autToPow F ρ' : (ZMod ℓ)ˣ) : ZMod ℓ) = 1 := by
      intro ρ'
      have h2 := hχ ρ' ((hζ.autToPow F ρ' : (ZMod ℓ)ˣ) : ZMod ℓ).val
        (hζ.autToPow_spec F ρ').symm
      rwa [ZMod.natCast_val, ZMod.cast_id] at h2
    have h3 : (((hζ.autToPow F ρ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹ =
        (((hζ.autToPow F ρ)⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ) :=
      ZMod.inv_coe_unit _
    rw [h3, ← map_inv (hζ.autToPow F) ρ]
    exact h1 ρ⁻¹
  -- the real comparison, from the difference of the two orthogonality identities
  have hreal :
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
            ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
          then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
          else 0)) ≤
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
            ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
          then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
          else 0)) +
      (∑ χ : DirichletCharacter ℂ ℓ, |Bc χ| * 2) / (ℓ.totient : ℝ) := by
    have htpos : (0 : ℝ) < (ℓ.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hℓ.pos
    -- the complex difference identity, filtered to the nontrivial characters
    have hdiff : ((ℓ.totient : ℕ) : ℂ) *
          ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0) : ℝ) : ℂ) -
        ((ℓ.totient : ℕ) : ℂ) *
          ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0) : ℝ) : ℂ) =
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ ℓ =>
            ∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1),
          (χ ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) -
              χ ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)) *
            ∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
                (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                  ℝ) : ℂ) := by
      rw [hkey σ, hkey τ, ← Finset.sum_sub_distrib]
      refine (Finset.sum_congr rfl fun χ _ => (sub_mul _ _ _).symm).trans ?_
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun χ _ hχ => ?_).symm
      have hc : ¬(∃ (ρ : E ≃ₐ[F] E) (n : ℕ), ρ ζ = ζ ^ n ∧ χ (n : ZMod ℓ) ≠ 1) :=
        fun h => hχ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rw [hcancel χ hc σ, hcancel χ hc τ, sub_self, zero_mul]
    -- the norm bound over the filtered characters
    have hbound : ‖((ℓ.totient : ℕ) : ℂ) *
          ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0) : ℝ) : ℂ) -
        ((ℓ.totient : ℕ) : ℂ) *
          ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0) : ℝ) : ℂ)‖ ≤
        ∑ χ : DirichletCharacter ℂ ℓ, |Bc χ| * 2 := by
      rw [hdiff]
      refine (norm_sum_le _ _).trans ?_
      refine le_trans (Finset.sum_le_sum fun χ hχ => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun χ _ _ => by positivity)
      have hc := (Finset.mem_filter.mp hχ).2
      rw [norm_mul]
      have h2 : ‖χ ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) -
          χ ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)‖ ≤ 2 := by
        have ha := χ.norm_le_one ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)
        have hb := χ.norm_le_one ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)
        calc ‖χ ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) -
              χ ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)‖
            ≤ ‖χ ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)‖ +
              ‖χ ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      have h3 : ‖∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
            (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
              ℝ) : ℂ)‖ ≤ |Bc χ| :=
        (hBc χ hc s hs).trans (le_abs_self _)
      calc ‖χ ((((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹) -
            χ ((((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ))⁻¹)‖ *
          ‖∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            χ ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ) *
              (((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s) :
                ℝ) : ℂ)‖
          ≤ 2 * |Bc χ| := mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
        _ = |Bc χ| * 2 := mul_comm _ _
    -- transfer the norm bound to the real difference
    have habs : (ℓ.totient : ℝ) *
        |(∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
              ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
            then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
            else 0)) -
          (∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0))| ≤
        ∑ χ : DirichletCharacter ℂ ℓ, |Bc χ| * 2 := by
      have h3 : ‖((ℓ.totient : ℕ) : ℂ) *
            ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0) : ℝ) : ℂ) -
          ((ℓ.totient : ℕ) : ℂ) *
            ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0) : ℝ) : ℂ)‖ =
          (ℓ.totient : ℝ) *
          |(∑' P : {P : HeightOneSpectrum (𝓞 F) //
              (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
            (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
              then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
              else 0)) -
            (∑' P : {P : HeightOneSpectrum (𝓞 F) //
                (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
              (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
                  ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
                then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
                else 0))| := by
        rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_natCast]
      rw [← h3]
      exact hbound
    -- conclude
    have h4 : (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (if ((hζ.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ) =
            ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
          then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
          else 0)) -
        (∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
          (if ((hζ.autToPow F τ : (ZMod ℓ)ˣ) : ZMod ℓ) =
              ((Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℕ) : ZMod ℓ)
            then (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)
            else 0)) ≤
        (∑ χ : DirichletCharacter ℂ ℓ, |Bc χ| * 2) / (ℓ.totient : ℝ) := by
      rw [le_div_iff₀ htpos]
      refine le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) htpos.le) ?_
      rw [mul_comm]
      exact habs
    linarith
  -- assemble: back to `ℝ≥0∞`
  have hofReal : ∀ ρ : E ≃ₐ[F] E,
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) =
      ENNReal.ofReal
        (∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
            ρ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ) ^ (-s)) := by
    intro ρ
    rw [← htoReal ρ, ENNReal.ofReal_toReal (hSne ρ)]
  rw [hofReal σ, hofReal τ, ← ENNReal.ofReal_add
    (tsum_nonneg fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (div_nonneg (Finset.sum_nonneg fun χ _ => by positivity) (Nat.cast_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hindic σ, hindic τ]
  exact hreal

open IsDedekindDomain in
/-- **Equidistribution of degree-one primes over the cyclotomic
congruence classes** — the `L`-function half of Deuring's route: for a
cyclotomic extension `E = F(ζ_ℓ)` (`ℓ` prime) and ANY `τ ∈ Gal(E/F)`,
the full degree-one prime sum away from `ℓ` is carried, up to an error
bounded uniformly in `s > 1`, by `ℓ` times the sub-sum over the
congruence class of `τ` (the places with `τ ζ = ζ ^ #(𝓞 F / P)`). Both
sums are `ℝ≥0∞`-valued, so no summability side conditions appear, and
the bounded error is additive — no `ENNReal` subtraction.

DERIVED from the pairwise-comparison leaf
`tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow_le_tsum_add`
(the remaining analytic sorry node; see its docstring) by Frobenius
bookkeeping, all proven: every degree-one `P` with `#(𝓞 F / P) ≠ ℓ`
lies in the congruence class of some `σ ∈ Gal(E/F)`
(`exists_algEquiv_map_zeta_eq_pow_natCard`), so the full sum is at most
`∑_{σ ∈ Gal(E/F)}` of the class sums (`ENNReal.tsum_iUnion_le` —
subadditivity suffices, no disjointness needed for an upper bound);
each class sum is at most the class sum of `τ` plus a bounded error
(the leaf), and there are at most `#(ZMod ℓ)ˣ = ℓ - 1 ≤ ℓ` classes
(`IsPrimitiveRoot.autToPow_injective`). -/
theorem tsum_rpow_neg_natCard_quotient_prime_and_ne_le_mul_tsum_add
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (τ : E ≃ₐ[F] E) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ s : ℝ, 1 < s →
      (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) ≤
      (ℓ : ℝ≥0∞) * (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) + B := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  haveI : FiniteDimensional F E := IsCyclotomicExtension.finiteDimensional {ℓ} F E
  -- the pairwise-comparison leaf, applied to each congruence class
  have hcompare := fun σ : E ≃ₐ[F] E =>
    tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow_le_tsum_add
      hℓ hζ σ τ
  choose Bf hBfne hBfle using hcompare
  refine ⟨∑ σ : E ≃ₐ[F] E, Bf σ,
    ENNReal.sum_ne_top.mpr fun σ _ => hBfne σ, ?_⟩
  intro s hs
  -- the Galois group has at most `ℓ` elements
  have hcardGal : (Fintype.card (E ≃ₐ[F] E) : ℝ≥0∞) ≤ (ℓ : ℝ≥0∞) := by
    have h1 : Fintype.card (E ≃ₐ[F] E) ≤ ℓ :=
      calc Fintype.card (E ≃ₐ[F] E)
          ≤ Fintype.card (ZMod ℓ)ˣ :=
            Fintype.card_le_of_injective _ (hζ.autToPow_injective F)
        _ = Nat.totient ℓ := ZMod.card_units_eq_totient ℓ
        _ ≤ ℓ := Nat.totient_le ℓ
    exact_mod_cast h1
  -- Frobenius existence: the degree-one primes are covered by the classes
  have hcover : {P : HeightOneSpectrum (𝓞 F) |
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ} ⊆
      ⋃ σ : E ≃ₐ[F] E, {P : HeightOneSpectrum (𝓞 F) |
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)} := by
    rintro P ⟨hP, hPne⟩
    obtain ⟨σ, hσ⟩ := exists_algEquiv_map_zeta_eq_pow_natCard hℓ hζ P hP hPne
    exact Set.mem_iUnion.mpr ⟨σ, hP, hσ⟩
  calc (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧ Nat.card (𝓞 F ⧸ P.asIdeal) ≠ ℓ},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s))
      ≤ ∑' P : (⋃ σ : E ≃ₐ[F] E, {P : HeightOneSpectrum (𝓞 F) |
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}),
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) :=
        ENNReal.tsum_mono_subtype
          (fun P : HeightOneSpectrum (𝓞 F) =>
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s)) hcover
    _ ≤ ∑ σ : E ≃ₐ[F] E, ∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) :=
        ENNReal.tsum_iUnion_le
          (fun P : HeightOneSpectrum (𝓞 F) =>
            (Nat.card (𝓞 F ⧸ P.asIdeal) : ℝ≥0∞) ^ (-s))
          (fun σ : E ≃ₐ[F] E => {P : HeightOneSpectrum (𝓞 F) |
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
            σ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)})
    _ ≤ ∑ σ : E ≃ₐ[F] E, ((∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) +
          Bf σ) :=
        Finset.sum_le_sum fun σ _ => hBfle σ s hs
    _ = Fintype.card (E ≃ₐ[F] E) •
          (∑' P : {P : HeightOneSpectrum (𝓞 F) //
            (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
            τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
          (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) +
          ∑ σ : E ≃ₐ[F] E, Bf σ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
    _ ≤ (ℓ : ℝ≥0∞) * (∑' P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)) +
          ∑ σ : E ≃ₐ[F] E, Bf σ := by
        rw [nsmul_eq_mul]
        gcongr

open IsDedekindDomain in
/-- **Divergence of the Dirichlet sum over a cyclotomic congruence class
of degree-one primes** — the analytic core of the
Chebotarev density theorem after the full field-crossing reduction, in
Dirichlet-density form: for a cyclotomic extension `E = F(ζ_ℓ)` of a
number field `F` (`ℓ` prime) and ANY `τ ∈ Gal(E/F)`, the sum
`∑ #(𝓞 F / P) ^ (-s)` over the finite places `P` of `F` with prime
residue cardinality (degree one over `ℚ`) in the congruence class of
`τ` (writing `τ ζ = ζ ^ a`, the condition `τ ζ = ζ ^ #(𝓞 F / P)` says
exactly `#(𝓞 F / P) = p ≡ a (mod ℓ)`) is unbounded as `s → 1⁺`: it
exceeds any given `C ≠ ⊤` for some `s > 1`. The sum is `ℝ≥0∞`-valued,
so no summability side conditions appear; the intended proof gives
divergence to `⊤` along `𝓝[>] 1`, of which this `∃`-form is the weakest
consequence the consumer needs. This makes the class infinite
(`infinite_setOf_natCard_quotient_prime_and_map_zeta_eq_pow`): a finite
class has sum bounded by its cardinality.

DERIVED (Deuring's route, real `s > 1` only, no analytic continuation)
from the two strictly shallower sorried leaves above:

* `exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne` (the
  Dedekind-zeta half): the FULL degree-one prime sum away from `ℓ`
  is unbounded as `s → 1⁺`;
* `tsum_rpow_neg_natCard_quotient_prime_and_ne_le_mul_tsum_add` (the
  `L`-function half): the full sum is at most `ℓ` times the sub-sum
  over the congruence class of `τ` plus a uniformly bounded error.

The assembly is pure `ℝ≥0∞` bookkeeping: pick `s > 1` with the full
sum exceeding `ℓ · C + B`; were the class sum `≤ C`, the comparison
would bound the full sum by `ℓ · C + B` — contradiction, with no
`ENNReal` subtraction anywhere. -/
theorem exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (τ : E ≃ₐ[F] E)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ s : ℝ, 1 < s ∧ C < ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) := by
  obtain ⟨B, hBne, hB⟩ :=
    tsum_rpow_neg_natCard_quotient_prime_and_ne_le_mul_tsum_add hℓ hζ τ
  obtain ⟨s, hs1, hsgt⟩ :=
    exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_ne F ℓ
      ((ℓ : ℝ≥0∞) * C + B)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top ℓ) hC, hBne⟩)
  refine ⟨s, hs1, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  refine absurd hsgt (not_lt.mpr ?_)
  refine (hB s hs1).trans ?_
  gcongr

open IsDedekindDomain in
/-- **Degree-one primes in cyclotomic Frobenius classes** — for a
cyclotomic extension `E = F(ζ_ℓ)` of a number field `F` (`ℓ` prime) and
ANY `τ ∈ Gal(E/F)`, infinitely many finite places `P` of `F` have prime
residue cardinality (degree one over `ℚ`) lying in the congruence class
of `τ`: writing `τ ζ = ζ ^ a`, the condition `τ ζ = ζ ^ #(𝓞 F / P)`
says exactly `#(𝓞 F / P) = p ≡ a (mod ℓ)`. No Frobenius elements, no
primes of `E`, no Galois action on ideals appear: this is pure prime
counting in `F`, the exact content of Dirichlet's theorem for the base
`F`.

DERIVED from the Dirichlet-density divergence leaf
`exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow`
(the remaining analytic sorry node; see its docstring for the state of
the mathlib pin): a finite class would have its `ℝ≥0∞`-valued Dirichlet
sum bounded by its cardinality (every term `#(𝓞 F / P) ^ (-s)` is at
most `1`), contradicting unboundedness. -/
theorem infinite_setOf_natCard_quotient_prime_and_map_zeta_eq_pow
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] {ℓ : ℕ} (hℓ : ℓ.Prime) [IsCyclotomicExtension {ℓ} F E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ ℓ) (τ : E ≃ₐ[F] E) :
    {P : HeightOneSpectrum (𝓞 F) | (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}.Infinite := by
  rw [← Set.infinite_coe_iff]
  by_contra hfin
  haveI : Finite {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)} := not_infinite_iff_finite.mp hfin
  haveI := Fintype.ofFinite {P : HeightOneSpectrum (𝓞 F) //
      (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}
  obtain ⟨s, hs1, hsC⟩ :=
    exists_lt_tsum_rpow_neg_natCard_quotient_prime_and_map_zeta_eq_pow hℓ hζ τ
      (Fintype.card {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)} : ℝ≥0∞)
      (ENNReal.natCast_ne_top _)
  refine absurd hsC (not_lt.mpr ?_)
  calc ∑' P : {P : HeightOneSpectrum (𝓞 F) //
        (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
        τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
      (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s)
      = ∑ P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)},
        (Nat.card (𝓞 F ⧸ (P : HeightOneSpectrum (𝓞 F)).asIdeal) : ℝ≥0∞) ^ (-s) :=
        tsum_fintype _
    _ ≤ ∑ _P : {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)}, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun P _ => ?_
        refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by linarith)
        exact_mod_cast P.2.1.one_lt.le
    _ = (Fintype.card {P : HeightOneSpectrum (𝓞 F) //
          (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
          τ ζ = ζ ^ Nat.card (𝓞 F ⧸ P.asIdeal)} : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

open IsDedekindDomain in
set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev, cyclic core**: let `E/F` be an extension of
number fields whose Galois group is generated by a single element `τ` (so
`E/F` is finite cyclic; finiteness of the extension is DERIVED in
`finiteDimensional_of_forall_mem_zpowers` — the Galois group of an
infinite Galois extension is an infinite compact Hausdorff group, never
countable, in particular never cyclic). Then infinitely many finite
places `P` of `F` have prime residue cardinality (residue degree one over
`ℚ`) and carry a prime `Q` of `𝓞 E` lying over `P` at which `τ` is an
arithmetic Frobenius (`τ x ≡ x ^ #(𝓞 F / P) (mod Q)`).

DERIVED by **Chebotarev's field-crossing reduction** to the cyclotomic
case, from two strictly shallower sorried leaves:

* `exists_prime_dvd_sub_one_and_irreducible_cyclotomic` (algebraic): an
  auxiliary prime `ℓ ≡ 1 (mod orderOf τ)` with `cyclotomic ℓ E`
  irreducible;
* `infinite_setOf_natCard_quotient_prime_and_map_zeta_eq_pow` (the
  analytic core): infinitude of degree-one primes of a number field in a
  prescribed cyclotomic congruence class.

The crossing: put `N = E(ζ_ℓ)` (`CyclotomicField ℓ E`), which is Galois
over `F` (`Normal.of_isGalois_isCyclotomicExtension`). By the crossing
lift (`exists_algEquiv_lift_and_forall_zpow_eq_one`) `τ` lifts to
`σ ∈ Gal(N/F)` acting on `ζ_ℓ` by a generator of `(ZMod ℓ)ˣ`, so that no
nontrivial power of `σ` fixes `ζ_ℓ`. Let `F'` be the fixed field of
`⟨σ⟩`: then `Gal(N/F')` is generated by `σ`, and `N = F'(ζ_ℓ)` by the
Galois correspondence — `N/F'` is CYCLOTOMIC. The analytic leaf then
provides infinitely many degree-one places `P'` of `F'` with residue
cardinality `p ≡ (exponent of σ on ζ_ℓ) (mod ℓ)`; at any prime `Q` of
`𝓞 N` over `P'` a Frobenius element exists
(`IsArithFrobAt.exists_of_isInvariant`), acts on `ζ_ℓ` by `ζ ↦ ζ^p`
exactly (`AlgHom.IsArithFrobAt.apply_of_pow_eq_one`), hence EQUALS `σ`
on `F'(ζ_ℓ) = N` — so `σ` itself is a Frobenius at `Q` over `F'`. The
congruence `σ y ≡ y^p (mod Q)` restricted to `y ∈ 𝓞 E` reads
`τ y ≡ y^p (mod Q ∩ 𝓞 E)` because `σ` lifts `τ`, and `p` is also the
residue cardinality of `P' ∩ F` (degree-one primes push down with the
same residue field, `natCard_quotient_under_eq_of_natCard_prime`).
Pushing the infinitely many `P'` down to `F` (finite fibers) yields the
claim.

Why this node cannot be narrowed to the base `F = ℚ` even though every
consumer of the Chebotarev chain instantiates `K = ℚ`: the consumers
need density of Frobenii in the full absolute Galois group `Γ ℚ`, and
the Deuring reduction passes through the fixed field `L^⟨τ⟩`, an
arbitrary number field. Likewise the surviving analytic leaf is
genuinely over an arbitrary base `F'` (the fixed field of the crossing
lift), so mathlib's Dirichlet theorem (base `ℚ`) alone cannot close it;
see the leaf's docstring for what the pin does and does not provide. -/
theorem infinite_setOf_isArithFrobAt_zpowers
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] (τ : E ≃ₐ[F] E)
    (hgen : ∀ σ : E ≃ₐ[F] E, σ ∈ Subgroup.zpowers τ) :
    {P : HeightOneSpectrum (𝓞 F) | (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧ Q.LiesOver P.asIdeal ∧
        IsArithFrobAt (𝓞 F) τ Q}.Infinite := by
  classical
  -- the extension is finite-dimensional, hence everything is finite Galois
  haveI hFD : FiniteDimensional F E := finiteDimensional_of_forall_mem_zpowers τ hgen
  -- the auxiliary prime of the crossing
  obtain ⟨ℓ, hℓ, hdvd, hirr⟩ :=
    exists_prime_dvd_sub_one_and_irreducible_cyclotomic E
      (n := orderOf τ) (orderOf_pos τ).ne'
  haveI : NeZero ℓ := ⟨hℓ.pos.ne'⟩
  haveI := Fact.mk hℓ
  -- the cyclotomic compositum `N = E(ζ_ℓ)`, Galois over `F`
  set N := CyclotomicField ℓ E
  letI : Algebra F N := ((algebraMap E N).comp (algebraMap F E)).toAlgebra
  haveI : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : FiniteDimensional F N := Module.Finite.trans E N
  haveI : Normal F N := Normal.of_isGalois_isCyclotomicExtension (E := E) ℓ
  haveI : IsGalois F N := ⟨⟩
  -- the crossing lift `σ` of `τ`
  obtain ⟨σ, hσE, hσpow⟩ :=
    exists_algEquiv_lift_and_forall_zpow_eq_one (F := F) (N := N) hℓ hirr τ hdvd
  set ζ : N := IsCyclotomicExtension.zeta ℓ E N
  have hζ : IsPrimitiveRoot ζ ℓ := IsCyclotomicExtension.zeta_spec ℓ E N
  -- the fixed field `F'` of `⟨σ⟩`, a number field with `Gal(N/F') = ⟨σ⟩`
  set F' : IntermediateField F N :=
    IntermediateField.fixedField (Subgroup.zpowers σ)
  haveI : NumberField F' := NumberField.of_module_finite F F'
  have hσmem : σ ∈ F'.fixingSubgroup :=
    (IntermediateField.le_iff_le (Subgroup.zpowers σ) F').mp le_rfl
      (Subgroup.mem_zpowers σ)
  set σ' : N ≃ₐ[F'] N :=
    IntermediateField.fixingSubgroupEquiv F' ⟨σ, hσmem⟩ with hσ'def
  have hgen' : ∀ ρ : N ≃ₐ[F'] N, ρ ∈ Subgroup.zpowers σ' := by
    intro ρ
    obtain ⟨g, hg⟩ := (IntermediateField.fixingSubgroupEquiv F').surjective ρ
    have hgmem : (g : N ≃ₐ[F] N) ∈ Subgroup.zpowers σ := by
      have h1 : F'.fixingSubgroup = Subgroup.zpowers σ :=
        IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)
      exact h1 ▸ g.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgmem
    refine ⟨k, ?_⟩
    show σ' ^ k = ρ
    rw [← hg, hσ'def, ← map_zpow]
    congr 1
    exact Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)
  -- powers of `σ'` act as the corresponding powers of `σ`
  have hσ'coe : ∀ (k : ℤ) (x : N), (σ' ^ k) x = (σ ^ k) x := by
    intro k x
    rw [hσ'def, ← map_zpow]
    show (((⟨σ, hσmem⟩ : F'.fixingSubgroup) ^ k :
      F'.fixingSubgroup) : N ≃ₐ[F] N) x = _
    rw [SubgroupClass.coe_zpow]
  -- `N = F'(ζ_ℓ)`: the Galois correspondence over `F'`
  have hadj' : IntermediateField.adjoin F' {ζ} = ⊤ := by
    have hfix : (IntermediateField.adjoin F' {ζ}).fixingSubgroup = ⊥ := by
      rw [eq_bot_iff]
      intro ρ hρ
      have hρζ : ρ ζ = ζ := hρ
        ⟨ζ, IntermediateField.subset_adjoin F' {ζ} rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen' ρ)
      have h2 : (σ ^ k) ζ = ζ := by
        rw [← hσ'coe k ζ, hk]
        exact hρζ
      have h3 : σ ^ k = 1 := hσpow k h2
      rw [Subgroup.mem_bot, ← hk]
      refine AlgEquiv.ext fun x => ?_
      rw [hσ'coe k x, h3, AlgEquiv.one_apply, AlgEquiv.one_apply]
    have h4 := IsGalois.fixedField_fixingSubgroup
      (IntermediateField.adjoin F' {ζ})
    rw [hfix, IntermediateField.fixedField_bot] at h4
    exact h4.symm
  have hζint' : IsIntegral F' ζ := Algebra.IsIntegral.isIntegral ζ
  have hadjalg : Algebra.adjoin F' ({ζ} : Set N) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      hζint'.isAlgebraic, hadj', IntermediateField.top_toSubalgebra]
  -- `N/F'` is a cyclotomic extension
  haveI hcyc' : IsCyclotomicExtension {ℓ} F' N := by
    refine ⟨fun {n'} hn' _ => ?_, fun x => ?_⟩
    · rw [Set.mem_singleton_iff] at hn'
      subst hn'
      exact ⟨ζ, hζ⟩
    · have h1 : x ∈ Algebra.adjoin F' ({ζ} : Set N) := by
        rw [hadjalg]; trivial
      refine Algebra.adjoin_mono ?_ h1
      rintro _ rfl
      exact ⟨ℓ, Set.mem_singleton ℓ, hℓ.pos.ne', hζ.pow_eq_one⟩
  -- the analytic leaf over `F'`
  have hinf := infinite_setOf_natCard_quotient_prime_and_map_zeta_eq_pow
    (F := F') (E := N) hℓ hζ σ'
  -- push the places of `F'` down to `F`: finitely many fibers
  haveI : Module.Finite (𝓞 F) (𝓞 F') :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 F')
  set π : HeightOneSpectrum (𝓞 F') → HeightOneSpectrum (𝓞 F) :=
    fun P' => P'.under (𝓞 F)
  have hfiber : ∀ v : HeightOneSpectrum (𝓞 F), {P' | π P' = v}.Finite := by
    intro v
    refine Set.Finite.of_finite_image
      (f := IsDedekindDomain.HeightOneSpectrum.asIdeal) ?_
      fun a _ b _ h => IsDedekindDomain.HeightOneSpectrum.ext h
    refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 F')).subset ?_
    rintro _ ⟨P', hP', rfl⟩
    exact ⟨P'.isPrime, ⟨by rw [← hP']; rfl⟩⟩
  set S' : Set (HeightOneSpectrum (𝓞 F')) :=
    {P' : HeightOneSpectrum (𝓞 F') |
      (Nat.card (𝓞 F' ⧸ P'.asIdeal)).Prime ∧
      σ' ζ = ζ ^ Nat.card (𝓞 F' ⧸ P'.asIdeal)}
  have himg : (π '' S').Infinite := by
    refine fun hfin => hinf ?_
    have hpre : (π ⁻¹' (π '' S')).Finite := by
      have hcover : π ⁻¹' (π '' S') = ⋃ v ∈ π '' S', {P' | π P' = v} := by
        ext P'
        simp [Set.mem_iUnion, eq_comm]
      rw [hcover]
      exact hfin.biUnion fun v _ => hfiber v
    exact hpre.subset (Set.subset_preimage_image π S')
  -- every pushed-down place carries the required Frobenius prime
  refine himg.mono ?_
  rintro _ ⟨P', ⟨hcard, hfrobζ⟩, rfl⟩
  -- a prime of `𝓞 N` over `P'`, with finite residue field
  haveI : Module.Finite (𝓞 F') (𝓞 N) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 F') (𝓞 N)
  obtain ⟨⟨Q, hQp, hQo⟩⟩ :=
    Ideal.nonempty_primesOver (S := 𝓞 N) P'.asIdeal
  haveI := hQp
  haveI := hQo
  have hQunder : Q.under (𝓞 F') = P'.asIdeal := hQo.over.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    apply P'.ne_bot
    rw [hQo.over, h, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F') (𝓞 N))
  haveI : Finite (𝓞 N ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQne
  -- a Frobenius element at `Q` over `F'`
  obtain ⟨σQ, hσQ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (𝓞 F') (N ≃ₐ[F'] N) Q
  -- `ζ` as an algebraic integer
  have hζint : IsIntegral ℤ ζ := by
    refine IsIntegral.of_pow hℓ.pos ?_
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  set ζO : 𝓞 N := ⟨ζ, hζint⟩
  -- the residue characteristic is not `ℓ`
  have hpℓ : Nat.card (𝓞 F' ⧸ P'.asIdeal) ≠ ℓ := by
    intro h
    have h1 : σ' ζ = 1 := by rw [hfrobζ, h, hζ.pow_eq_one]
    have h2 : ζ = 1 := σ'.injective (by rw [h1, map_one])
    exact hζ.ne_one hℓ.one_lt h2
  -- `ℓ` is invertible modulo `Q`
  have hℓQ : ((ℓ : ℕ) : 𝓞 N) ∉ Q := by
    intro hmem
    have h1 : ((ℓ : ℕ) : 𝓞 F') ∈ P'.asIdeal := by
      rw [← hQunder, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmem
    haveI : Finite (𝓞 F' ⧸ P'.asIdeal) :=
      Nat.finite_of_card_ne_zero hcard.ne_zero
    haveI := Fintype.ofFinite (𝓞 F' ⧸ P'.asIdeal)
    have h2 : ((Nat.card (𝓞 F' ⧸ P'.asIdeal) : ℕ) :
        𝓞 F' ⧸ P'.asIdeal) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.cast_card_eq_zero _
    have h3 : ((ℓ : ℕ) : 𝓞 F' ⧸ P'.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P'.asIdeal),
        Ideal.Quotient.eq_zero_iff_mem]
      exact h1
    have hco : IsCoprime (Nat.card (𝓞 F' ⧸ P'.asIdeal) : ℤ) (ℓ : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr
        (by
          rw [Int.gcd_natCast_natCast]
          exact (Nat.coprime_primes hcard hℓ).mpr hpℓ)
    obtain ⟨u, v, huv⟩ := hco
    have h4 : (1 : 𝓞 F' ⧸ P'.asIdeal) = 0 := by
      calc (1 : 𝓞 F' ⧸ P'.asIdeal)
          = ((u * (Nat.card (𝓞 F' ⧸ P'.asIdeal) : ℤ) + v * (ℓ : ℤ) : ℤ) :
            𝓞 F' ⧸ P'.asIdeal) := by rw [huv, Int.cast_one]
        _ = (u : 𝓞 F' ⧸ P'.asIdeal) *
              ((Nat.card (𝓞 F' ⧸ P'.asIdeal) : ℕ) : 𝓞 F' ⧸ P'.asIdeal) +
            (v : 𝓞 F' ⧸ P'.asIdeal) * ((ℓ : ℕ) : 𝓞 F' ⧸ P'.asIdeal) := by
            rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
              Int.cast_natCast]
        _ = 0 := by rw [h2, h3, mul_zero, mul_zero, add_zero]
    exact one_ne_zero h4
  -- the Frobenius at `Q` acts on `ζ` exactly by `ζ ↦ ζ ^ p`, hence equals `σ'`
  have hζOpow : ζO ^ ℓ = 1 := by
    apply NumberField.RingOfIntegers.ext
    show algebraMap (𝓞 N) N (ζO ^ ℓ) = algebraMap (𝓞 N) N 1
    rw [map_pow, map_one]
    show ζ ^ ℓ = 1
    exact hζ.pow_eq_one
  have hσQζ : σQ • ζO = ζO ^ Nat.card (𝓞 F' ⧸ P'.asIdeal) := by
    have h1 := hσQ.apply_of_pow_eq_one hζOpow hℓQ
    rw [hQunder] at h1
    exact h1
  have hσQσ' : σQ = σ' := by
    have h1 : σQ ζ = σ' ζ := by
      have h2 : (algebraMap (𝓞 N) N) (σQ • ζO) =
          (algebraMap (𝓞 N) N) (ζO ^ Nat.card (𝓞 F' ⧸ P'.asIdeal)) :=
        congrArg _ hσQζ
      rw [map_pow] at h2
      have h3 : (algebraMap (𝓞 N) N) (σQ • ζO) = σQ ζ := rfl
      have h4 : (algebraMap (𝓞 N) N) ζO = ζ := rfl
      rw [h3, h4] at h2
      rw [h2, hfrobζ]
    have h5 : Set.EqOn (σQ : N →ₐ[F'] N) (σ' : N →ₐ[F'] N) ({ζ} : Set N) := by
      rintro _ rfl
      exact h1
    have h6 := AlgHom.ext_of_adjoin_eq_top hadjalg h5
    refine AlgEquiv.ext fun x => ?_
    exact DFunLike.congr_fun h6 x
  have hfrob' : IsArithFrobAt (𝓞 F') σ' Q := hσQσ' ▸ hσQ
  -- push everything down to `F`
  refine ⟨?_, ?_⟩
  · -- degree one over `ℚ`: the residue field does not shrink
    show (Nat.card (𝓞 F ⧸ (π P').asIdeal)).Prime
    have h1 : (π P').asIdeal = P'.asIdeal.under (𝓞 F) := rfl
    rw [h1, natCard_quotient_under_eq_of_natCard_prime P'.asIdeal hcard]
    exact hcard
  · -- the Frobenius prime `Q ∩ 𝓞 E`
    refine ⟨Q.under (𝓞 E), Ideal.IsPrime.under (𝓞 E) Q, ?_, ?_⟩
    · constructor
      show (π P').asIdeal = (Q.under (𝓞 E)).under (𝓞 F)
      have h1 : (Q.under (𝓞 E)).under (𝓞 F) = Q.under (𝓞 F) :=
        Ideal.under_under Q
      have h2 : (Q.under (𝓞 F')).under (𝓞 F) = Q.under (𝓞 F) :=
        Ideal.under_under Q
      rw [h1, ← h2, hQunder]
      rfl
    · -- the Frobenius congruence descends from `F'` to `F` over `𝓞 E`
      intro x
      have hcard2 : Nat.card (𝓞 F ⧸ (Q.under (𝓞 E)).under (𝓞 F)) =
          Nat.card (𝓞 F' ⧸ P'.asIdeal) := by
        have h1 : (Q.under (𝓞 E)).under (𝓞 F) = P'.asIdeal.under (𝓞 F) := by
          have h2 : (Q.under (𝓞 E)).under (𝓞 F) = Q.under (𝓞 F) :=
            Ideal.under_under Q
          have h3 : (Q.under (𝓞 F')).under (𝓞 F) = Q.under (𝓞 F) :=
            Ideal.under_under Q
          rw [h2, ← h3, hQunder]
        rw [h1, natCard_quotient_under_eq_of_natCard_prime P'.asIdeal hcard]
      have hcomm : algebraMap (𝓞 E) (𝓞 N) (τ • x) =
          σ' • algebraMap (𝓞 E) (𝓞 N) x := by
        apply NumberField.RingOfIntegers.ext
        have h5 : σ' (algebraMap E N ((x : 𝓞 E) : E)) =
            σ (algebraMap E N ((x : 𝓞 E) : E)) := by
          have h7 := hσ'coe 1 (algebraMap E N ((x : 𝓞 E) : E))
          rwa [zpow_one, zpow_one] at h7
        show algebraMap E N ((τ • x : 𝓞 E) : E) =
          σ' (algebraMap E N ((x : 𝓞 E) : E))
        rw [h5, show ((τ • x : 𝓞 E) : E) = τ ((x : 𝓞 E) : E) from rfl, hσE]
      show τ • x - x ^ Nat.card (𝓞 F ⧸ (Q.under (𝓞 E)).under (𝓞 F)) ∈
        Q.under (𝓞 E)
      rw [hcard2, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow, hcomm]
      have h6 := hfrob' (algebraMap (𝓞 E) (𝓞 N) x)
      rw [hQunder] at h6
      exact h6

open IsDedekindDomain in
/-- **Finiteness of ramified places**: for a finite Galois extension `E/F`
of number fields, only finitely many places of `F` carry a prime of
`𝓞 E` with nontrivial inertia in `Gal(E/F)`. DERIVED: a prime with
nontrivial inertia has inertia group of order equal to the ramification
index (`Ideal.card_inertia_eq_ramificationIdxIn`), hence is not
unramified (`Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`), hence
divides the different ideal (`Ideal.dvd_differentIdeal_iff`), which is
nonzero (`differentIdeal_ne_bot`); and a nonzero ideal of the Dedekind
domain `𝓞 E` has only finitely many prime divisors
(`Ideal.finite_factors`), each contracting to a single place of `F`. -/
theorem finite_setOf_exists_inertia_ne_bot
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    {P : HeightOneSpectrum (𝓞 F) | ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧
      Q.LiesOver P.asIdeal ∧ Q.inertia (E ≃ₐ[F] E) ≠ ⊥}.Finite := by
  classical
  haveI : Module.Finite (𝓞 F) (𝓞 E) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  -- separability of the fraction-field extension, transported from `E/F`
  letI : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) :=
    FractionRing.liftAlgebra _ _
  haveI hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
      (FractionRing.algEquiv (𝓞 E) E).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 E) E).symm x
  -- the different ideal is nonzero, so it has finitely many prime divisors
  have h𝔡ne : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have h𝔡fin : {w : HeightOneSpectrum (𝓞 E) |
      w.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 E)}.Finite :=
    Ideal.finite_factors h𝔡ne
  -- reduce the bad set to the image of these prime divisors
  refine (h𝔡fin.image (fun w => w.under (𝓞 F))).subset ?_
  rintro P ⟨Q, hQprime, hQover, hQin⟩
  haveI := hQprime
  haveI : Q.LiesOver P.asIdeal := hQover
  -- `Q` is nonzero, hence a height-one prime of `𝓞 E`
  have hQne : Q ≠ ⊥ := by
    intro h
    apply P.ne_bot
    rw [hQover.over, h, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  -- nontrivial inertia forces ramification, i.e. `Q` divides the different
  have hQdvd : Q ∣ differentIdeal (𝓞 F) (𝓞 E) := by
    rw [dvd_differentIdeal_iff]
    intro hunram
    apply hQin
    haveI := hunram
    haveI : (Q.under (𝓞 F)).IsPrime := Ideal.IsPrime.under (𝓞 F) Q
    haveI : CharZero (FractionRing (𝓞 F)) :=
      charZero_of_injective_algebraMap
        (IsFractionRing.injective (𝓞 F) (FractionRing (𝓞 F)))
    have hcard : Nat.card (Q.inertia (E ≃ₐ[F] E)) =
        Ideal.ramificationIdxIn (Q.under (𝓞 F)) (𝓞 E) :=
      Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (Q.under (𝓞 F)) Q
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q (E ≃ₐ[F] E),
      Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  exact ⟨⟨Q, hQprime, hQne⟩, hQdvd, IsDedekindDomain.HeightOneSpectrum.ext
    hQover.over.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Chebotarev, arithmetic core**: for a finite Galois subextension `L`
of `K̄/K` and any `τ ∈ Gal(L/K)`, infinitely many finite places `v` of
`K` carry a prime `Q` of `𝓞 L` lying over `v`, with trivial inertia
(i.e. `v` unramified in `L`), at which `τ` is an arithmetic Frobenius
(`τ x ≡ x ^ #(𝓞 K / v) (mod Q)`). This is the classical existence form
of the Chebotarev density theorem in purely finite, ideal-theoretic
vocabulary; no completions or absolute Galois groups appear.

DERIVED by the classical **Deuring reduction** from the cyclic-case leaf
`infinite_setOf_isArithFrobAt_zpowers` and the ramification-finiteness
leaf `finite_setOf_exists_inertia_ne_bot`: let `F = L^⟨τ⟩` be the fixed
field of the cyclic subgroup generated by `τ`, so that `L/F` is cyclic
with Galois group generated by (the restriction-of-scalars lift of) `τ`.
The cyclic leaf produces infinitely many places `P` of `F` of residue
degree one over `ℚ` carrying a Frobenius prime `Q` for `τ` over `F`; at
such `P` the Frobenius congruence over `F` IS the Frobenius congruence
over `K` (the residue fields of `v = P ∩ K` and `P` coincide, both of
prime cardinality — `natCard_quotient_under_eq_of_natCard_prime`).
Discarding the finitely many places of `K` ramified in `L` (each carrying
only finitely many `P`, by finiteness of the fibers of `P ↦ P ∩ K`)
leaves infinitely many places of `K` with trivial inertia and the
required Frobenius prime. -/
theorem infinite_setOf_isArithFrobAt
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] (τ : L ≃ₐ[K] L) :
    {v : Ω K | ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧
      Q.inertia (L ≃ₐ[K] L) = ⊥ ∧ IsArithFrobAt (𝓞 K) τ Q}.Infinite := by
  classical
  -- the fixed field of the cyclic subgroup generated by `τ`
  set F : IntermediateField K L := IntermediateField.fixedField (Subgroup.zpowers τ)
  haveI : NumberField F := NumberField.of_module_finite K F
  -- `τ` fixes `F` pointwise, so it lifts to an `F`-automorphism `τ'` of `L`
  have hτmem : τ ∈ F.fixingSubgroup :=
    (IntermediateField.le_iff_le (Subgroup.zpowers τ) F).mp le_rfl
      (Subgroup.mem_zpowers τ)
  set τ' : L ≃ₐ[F] L := IntermediateField.fixingSubgroupEquiv F ⟨τ, hτmem⟩ with hτ'def
  -- `τ'` generates `Gal(L/F)`: Galois correspondence for the fixed field
  have hgen : ∀ σ : L ≃ₐ[F] L, σ ∈ Subgroup.zpowers τ' := by
    intro σ
    obtain ⟨g, hg⟩ := (IntermediateField.fixingSubgroupEquiv F).surjective σ
    have hgmem : (g : L ≃ₐ[K] L) ∈ Subgroup.zpowers τ := by
      have h1 : F.fixingSubgroup = Subgroup.zpowers τ :=
        IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers τ)
      exact h1 ▸ g.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgmem
    refine ⟨n, ?_⟩
    show τ' ^ n = σ
    rw [← hg, hτ'def, ← map_zpow]
    congr 1
    exact Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hn)
  -- the cyclic core over `F` and the ramification bound over `K`
  have hA := infinite_setOf_isArithFrobAt_zpowers τ' hgen
  have hB := finite_setOf_exists_inertia_ne_bot (F := K) (E := L)
  -- pushing places of `F` down to places of `K`: finite fibers
  set π : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Ω K :=
    fun P => P.under (𝓞 K)
  have hfiber : ∀ v : Ω K,
      {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | π P = v}.Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
      ?_ fun a _ b _ h => IsDedekindDomain.HeightOneSpectrum.ext h
    refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 F)).subset ?_
    rintro _ ⟨P, hP, rfl⟩
    exact ⟨P.isPrime, ⟨by rw [← hP]; rfl⟩⟩
  have hpreim : ∀ s : Set (Ω K), s.Finite → (π ⁻¹' s).Finite := by
    intro s hs
    have hcover : π ⁻¹' s = ⋃ v ∈ s, {P | π P = v} := by
      ext P
      simp [Set.mem_iUnion]
    rw [hcover]
    exact hs.biUnion fun v _ => hfiber v
  -- the good places of `F`: cyclic-core data, over a `K`-unramified place
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {P | (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver P.asIdeal ∧
        IsArithFrobAt (𝓞 F) τ' Q} \
      π ⁻¹' {v : Ω K | ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧
        Q.inertia (L ≃ₐ[K] L) ≠ ⊥} with hTdef
  have hTinf : T.Infinite := hA.sdiff (hpreim _ hB)
  have himg : (π '' T).Infinite := fun hfin =>
    hTinf ((hpreim _ hfin).subset (Set.subset_preimage_image π T))
  -- every pushed-down place carries the required Frobenius prime
  refine himg.mono ?_
  rintro _ ⟨P, hPmem, rfl⟩
  rw [hTdef] at hPmem
  obtain ⟨⟨hcard, Q, hQprime, hQover, hQfrob⟩, hgood⟩ := hPmem
  haveI := hQprime
  haveI : Q.LiesOver P.asIdeal := hQover
  haveI : P.asIdeal.LiesOver (π P).asIdeal := ⟨rfl⟩
  haveI hQoverv : Q.LiesOver (π P).asIdeal :=
    Ideal.LiesOver.trans Q P.asIdeal (π P).asIdeal
  refine ⟨Q, hQprime, hQoverv, ?_, ?_⟩
  · -- trivial inertia: `π P` avoids the ramified places
    by_contra hne
    exact hgood ⟨Q, hQprime, hQoverv, hne⟩
  · -- the Frobenius congruence descends from `F` to `K` at degree-one primes
    intro x
    have h1 := hQfrob x
    have h2 : Q.under (𝓞 F) = P.asIdeal := hQover.over.symm
    have hcardeq : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) =
        Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) := by
      have h3 : Q.under (𝓞 K) = P.asIdeal.under (𝓞 K) := by
        rw [← h2, Ideal.under_under]
      rw [h3, h2]
      exact natCard_quotient_under_eq_of_natCard_prime (A := 𝓞 K) P.asIdeal hcard
    have hact : τ • x = τ' • x := NumberField.RingOfIntegers.ext rfl
    show τ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q
    rw [hcardeq, hact]
    exact h1

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Local–global Frobenius compatibility, pointwise form**: at EVERY
finite place `v` of `K`, the restriction to `L` of the
completion-theoretic global Frobenius `globalFrob v` is an arithmetic
Frobenius at the prime `Q` of `𝓞 L` obtained by contracting the maximal
ideal of the integral closure of `𝒪ᵥ` in `K̄ᵥ` along the chosen
embedding `K̄ → K̄ᵥ`. No unramifiedness hypothesis is needed:
`IsArithFrobAt` is the raw congruence `σ x ≡ x ^ #(𝓞 K/v) (mod Q)`,
which the local arithmetic Frobenius satisfies at the big maximal ideal
(`Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob`) and which
contracts along `𝓞 L → IntegralClosure 𝒪ᵥ K̄ᵥ`. -/
theorem exists_isArithFrobAt_restrictNormalHom_globalFrob
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] (v : Ω K) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧
      IsArithFrobAt (𝓞 K)
        (AlgEquiv.restrictNormalHom L (globalFrob v)) Q := by
  classical
  -- the chosen embedding of algebraic closures
  set ι : AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K) :=
    AlgebraicClosure.map (algebraMap K (v.adicCompletion K)) with hιdef
  -- integral elements land in the integral closure of the completed integers
  have hint : ∀ x : 𝓞 L, ι (algebraMap L (AlgebraicClosure K) (x : L)) ∈
      integralClosure (v.adicCompletionIntegers K)
        (AlgebraicClosure (v.adicCompletion K)) := by
    intro x
    exact IsIntegral.map_of_comp_eq
      (algebraMap ℤ (v.adicCompletionIntegers K))
      (ι.comp (algebraMap L (AlgebraicClosure K)))
      (Subsingleton.elim _ _) (x.2 : IsIntegral ℤ (x : L))
  -- the contraction homomorphism into the big integral closure
  set j : 𝓞 L →+* IntegralClosure (v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K)) :=
    RingHom.codRestrict
      ((ι.comp (algebraMap L (AlgebraicClosure K))).comp
        (algebraMap (𝓞 L) L))
      (integralClosure (v.adicCompletionIntegers K)
        (AlgebraicClosure (v.adicCompletion K))).toSubring
      (fun x => hint x)
  set M : Ideal (IntegralClosure (v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K))) :=
    IsLocalRing.maximalIdeal _
  set Q : Ideal (𝓞 L) := M.comap j with hQdef
  -- the big maximal ideal contracts to the maximal ideal of `𝒪ᵥ`
  have hMunder : M.under (v.adicCompletionIntegers K) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under _ M)
  -- `j` intertwines the two algebra maps from `𝓞 K`
  have hcomm : ∀ a : 𝓞 K, j (algebraMap (𝓞 K) (𝓞 L) a) =
      algebraMap (v.adicCompletionIntegers K)
        (IntegralClosure (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) := by
    intro a
    apply Subtype.ext
    show ι (algebraMap L (AlgebraicClosure K)
        (algebraMap K L (algebraMap (𝓞 K) K a))) =
      algebraMap (IntegralClosure (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))
        (AlgebraicClosure (v.adicCompletion K))
        (algebraMap (v.adicCompletionIntegers K)
          (IntegralClosure (v.adicCompletionIntegers K)
            (AlgebraicClosure (v.adicCompletion K)))
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a))
    rw [← IsScalarTower.algebraMap_apply K L (AlgebraicClosure K),
      hιdef, AlgebraicClosure.map_algebraMap,
      ← IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (IntegralClosure (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))
        (AlgebraicClosure (v.adicCompletion K)),
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K)
        (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)),
      show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) =
        ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a :
          v.adicCompletionIntegers K) : v.adicCompletion K) from rfl,
      IsDedekindDomain.HeightOneSpectrum.algebraMap_completionIntegers K v a,
      IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
  -- `Q` lies over `v`
  have hover : v.asIdeal = (v.completionIdeal K).under (𝓞 K) :=
    Ideal.LiesOver.over
  have hQunder : Q.under (𝓞 K) = v.asIdeal := by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hQdef, Ideal.mem_comap, hcomm a,
      ← Ideal.mem_comap (f := algebraMap (v.adicCompletionIntegers K)
        (IntegralClosure (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))),
      show M.comap (algebraMap (v.adicCompletionIntegers K)
        (IntegralClosure (v.adicCompletionIntegers K)
          (AlgebraicClosure (v.adicCompletion K)))) = M.under _ from rfl,
      hMunder, hover, Ideal.under_def, Ideal.mem_comap]
  -- residue cardinalities agree
  have hcard : Nat.card ((v.adicCompletionIntegers K) ⧸
      M.under (v.adicCompletionIntegers K)) =
      Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    rw [hMunder, hQunder]
    exact (Nat.card_congr
      (IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
        K v).toEquiv).symm
  -- the Frobenius congruence upstairs
  have harith := Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := v)
  -- `j` intertwines the restricted global Frobenius with `adicArithFrob`
  have hfrob : ∀ x : 𝓞 L,
      MulSemiringAction.toAlgHom (v.adicCompletionIntegers K) _
        (Field.AbsoluteGaloisGroup.adicArithFrob v) (j x) =
      j ((MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L)
        (AlgEquiv.restrictNormalHom L (globalFrob v))) x) := by
    intro x
    apply Subtype.ext
    show Field.AbsoluteGaloisGroup.adicArithFrob v
        (ι (algebraMap L (AlgebraicClosure K) (x : L))) =
      ι (algebraMap L (AlgebraicClosure K)
        ((AlgEquiv.restrictNormalHom L (globalFrob v)) (x : L)))
    have hres : algebraMap L (AlgebraicClosure K)
        ((AlgEquiv.restrictNormalHom L (globalFrob v)) (x : L)) =
        globalFrob v (algebraMap L (AlgebraicClosure K) (x : L)) :=
      AlgEquiv.restrictNormal_commutes (globalFrob v) L (x : L)
    have hlift := Field.absoluteGaloisGroup.lift_map
      (algebraMap K (v.adicCompletion K))
      (Field.AbsoluteGaloisGroup.adicArithFrob v)
      (algebraMap L (AlgebraicClosure K) (x : L))
    rw [hres, hιdef]
    exact hlift.symm
  refine ⟨Q, Ideal.IsPrime.comap j, ⟨hQunder.symm⟩, fun x => ?_⟩
  have h1 := harith (j x)
  rw [hfrob x, ← map_pow, ← map_sub] at h1
  rw [hcard] at h1
  exact h1

/-- **Local–global Frobenius compatibility** (finite exceptional set —
in fact empty): away from finitely many places, the restriction to `L`
of the completion-theoretic global Frobenius `globalFrob v` is an
arithmetic Frobenius at some prime `Q` of `𝓞 L` over `v`. DERIVED from
the pointwise form `exists_isArithFrobAt_restrictNormalHom_globalFrob`,
which produces such a prime at every place. -/
theorem finite_setOf_not_isArithFrobAt_restrictNormalHom_globalFrob
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] :
    {v : Ω K | ¬ ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧
      IsArithFrobAt (𝓞 K)
        (AlgEquiv.restrictNormalHom L (globalFrob v)) Q}.Finite := by
  have hempty : {v : Ω K | ¬ ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧
      Q.LiesOver v.asIdeal ∧ IsArithFrobAt (𝓞 K)
        (AlgEquiv.restrictNormalHom L (globalFrob v)) Q} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro v hv
    exact hv (exists_isArithFrobAt_restrictNormalHom_globalFrob L v)
  rw [hempty]
  exact Set.finite_empty

open scoped Pointwise in
/-- **Chebotarev, finite Galois-group form**: for a finite Galois
subextension `L` of `K̄/K` and any element `τ` of the finite Galois
group `Gal(L/K)`, some global Frobenius at a place outside the given
finite set `S` restricts to a conjugate of `τ` on `L`. This is the
classical existence form of the Chebotarev density theorem for the
finite Galois extension `L/K`: every element of `Gal(L/K)` is the
Frobenius at infinitely many places of `K`. DERIVED from the arithmetic
core `infinite_setOf_isArithFrobAt` and the local–global bridge
`finite_setOf_not_isArithFrobAt_restrictNormalHom_globalFrob` by
transitivity of the Galois action on the primes over `v` and uniqueness
of Frobenius modulo (trivial) inertia. The profinite coset form
`exists_frobenius_conj_mem_coset` is DERIVED from this below (normal
closure + surjectivity of restriction). -/
theorem exists_globalFrob_restrictNormalHom_conj (S : Finset (Ω K))
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [Normal K L] (τ : L ≃ₐ[K] L) :
    ∃ v : Ω K, v ∉ S ∧ ∃ h : L ≃ₐ[K] L,
      h * AlgEquiv.restrictNormalHom L (globalFrob v) * h⁻¹ = τ := by
  obtain ⟨v, hv, hvS⟩ := ((infinite_setOf_isArithFrobAt L τ).sdiff
    (finite_setOf_not_isArithFrobAt_restrictNormalHom_globalFrob L)).exists_notMem_finset S
  obtain ⟨⟨Q₁, hQ₁prime, hQ₁over, hQ₁inert, hQ₁frob⟩, hgood⟩ := hv
  obtain ⟨Q₂, hQ₂prime, hQ₂over, hQ₂frob⟩ := not_not.mp hgood
  haveI := hQ₁prime
  haveI := hQ₂prime
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) Q₂ Q₁
    (hQ₂over.over.symm.trans hQ₁over.over)
  have hconj := hQ₂frob.conj g
  rw [← hg] at hconj
  have hmem := hQ₁frob.mul_inv_mem_inertia hconj
  rw [hQ₁inert, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact ⟨v, hvS, g, hmem.symm⟩

/-- **Chebotarev, finite level**: modulo the fixing subgroup
of any finite subextension `E` of `K̄/K`, every element of the absolute
Galois group is a conjugate of a global Frobenius at a place outside any
given finite set `S`, stated without finite-quotient vocabulary: the
coset `σ · Gal(K̄/E)` meets the Frobenius conjugates. DERIVED from the
finite Galois-group form `exists_globalFrob_restrictNormalHom_conj` at
the normal closure `L` of `E` in `K̄`: choose `v ∉ S` and `h ∈ Gal(L/K)`
with `h · (Frob_v|_L) · h⁻¹ = σ|_L`, lift `h` to `g ∈ Γ K` by
surjectivity of restriction (`K̄/K` is normal); then
`σ⁻¹ · (g · Frob_v · g⁻¹)` restricts to the identity of `Gal(L/K)`,
i.e. lies in `L.fixingSubgroup ≤ E.fixingSubgroup`. -/
theorem exists_frobenius_conj_mem_coset (S : Finset (Ω K))
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : Γ K) :
    ∃ v : Ω K, v ∉ S ∧ ∃ g : Γ K,
      σ⁻¹ * (g * globalFrob v * g⁻¹) ∈ E.fixingSubgroup := by
  set L : IntermediateField K (AlgebraicClosure K) :=
    IntermediateField.normalClosure K E (AlgebraicClosure K)
  obtain ⟨v, hvS, h, hh⟩ :=
    exists_globalFrob_restrictNormalHom_conj S L
      (AlgEquiv.restrictNormalHom L σ)
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := L) (AlgebraicClosure K) h
  refine ⟨v, hvS, g,
    IntermediateField.fixingSubgroup_le E.le_normalClosure ?_⟩
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker,
    map_mul, map_inv, map_mul, map_mul, map_inv, hg, hh, inv_mul_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev density, topological form**: for a finite set `S` of
finite places of a number field `K`, the union of the conjugacy classes
of the global Frobenius elements at the places outside `S` is dense in
the absolute Galois group. DERIVED from the finite-level node
`exists_frobenius_conj_mem_coset` by the profinite limit argument: the
cosets of fixing subgroups of finite subextensions form a neighborhood
basis of the Krull topology (`krullTopology_mem_nhds_one_iff`), and the
finite-level statement puts a Frobenius conjugate in every such coset. -/
theorem dense_conjClasses_globalFrob (S : Finset (Ω K)) :
    Dense {x : Γ K | ∃ v : Ω K, v ∉ S ∧ ∃ g : Γ K,
      x = g * globalFrob v * g⁻¹} := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨σ, hσ⟩
  open Pointwise in
  have hUnhds : (σ⁻¹ • U : Set (Γ K)) ∈ nhds (1 : Γ K) := by
    have hopen : IsOpen (σ⁻¹ • U : Set (Γ K)) := hU.smul σ⁻¹
    exact hopen.mem_nhds ⟨σ, hσ, by simp⟩
  obtain ⟨E, hEfin, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) _).mp hUnhds
  haveI := hEfin
  obtain ⟨v, hvS, g, hg⟩ := exists_frobenius_conj_mem_coset S E σ
  refine ⟨g * globalFrob v * g⁻¹, ?_, v, hvS, g, rfl⟩
  obtain ⟨u, hu, huv⟩ := hEsub hg
  have hue : u = g * globalFrob v * g⁻¹ :=
    mul_left_cancel (by rw [← smul_eq_mul]; exact huv)
  rwa [← hue]

/-!
## The mod-`ℓ` cyclotomic character as a continuous character of `Γ ℚ`

`cyclotomicCharacterModL ℓ` is mathlib's `modularCyclotomicCharacter`
(the action on the `ℓ`-th roots of unity, `g ζ = ζ ^ χ̄(g)`) precomposed
with `Γ ℚ → (ℚ̄ ≃+* ℚ̄)`. Its continuity (equivalently, openness of its
kernel) is PROVEN here: the character is trivial on the fixing subgroup
of the finite extension `ℚ(μ_ℓ)/ℚ`, which is open in the Krull topology,
so the map is locally constant.
-/

/-- The mod-`ℓ` cyclotomic character of the absolute Galois group of `ℚ`:
`g ζ = ζ ^ (cyclotomicCharacterModL ℓ g)` for every `ℓ`-th root of unity
`ζ ∈ ℚ̄`. -/
noncomputable def cyclotomicCharacterModL (ℓ : ℕ) [Fact ℓ.Prime] :
    Field.absoluteGaloisGroup ℚ →* (ZMod ℓ)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)).comp
    (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ) (AlgebraicClosure ℚ))

/-- The mod-`ℓ` cyclotomic character is trivial on the fixing subgroup of
the subfield generated by the `ℓ`-th roots of unity. -/
lemma cyclotomicCharacterModL_eq_one (ℓ : ℕ) [Fact ℓ.Prime]
    {τ : Field.absoluteGaloisGroup ℚ}
    (hτ : τ ∈ (IntermediateField.adjoin ℚ
      (((↑) : (AlgebraicClosure ℚ)ˣ → AlgebraicClosure ℚ) ''
        (rootsOfUnity ℓ (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ))).fixingSubgroup) :
    cyclotomicCharacterModL ℓ τ = 1 := by
  set L := AlgebraicClosure ℚ
  set S : Set L := ((↑) : Lˣ → L) '' (rootsOfUnity ℓ L : Set Lˣ)
  have hfix : ∀ x ∈ S, τ x = x := fun x hx =>
    ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ) x
      (IntermediateField.subset_adjoin ℚ S hx)
  have hone : (1 : ZMod ℓ) = modularCyclotomicCharacter L
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity L ℓ)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ) L τ) := by
    refine modularCyclotomicCharacter.unique L _ _ fun t ht => ?_
    rw [ZMod.val_one, pow_one]
    exact hfix (t : L) ⟨t, ht, rfl⟩
  exact Units.ext (by exact hone.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The mod-`ℓ` cyclotomic character is continuous (as a map into the
discrete space `ZMod ℓ`): it kills the open fixing subgroup of the finite
extension `ℚ(μ_ℓ)/ℚ`, so every fiber is a union of open cosets. -/
lemma continuous_cyclotomicCharacterModL (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite ((rootsOfUnity ℓ (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)) :=
    inferInstanceAs (Finite (rootsOfUnity ℓ (AlgebraicClosure ℚ)))
  have hSfin : (((↑) : (AlgebraicClosure ℚ)ˣ → AlgebraicClosure ℚ) ''
      (rootsOfUnity ℓ (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)).Finite :=
    Set.Finite.image _ (Set.toFinite _)
  haveI := hSfin.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ
      (((↑) : (AlgebraicClosure ℚ)ˣ → AlgebraicClosure ℚ) ''
        (rootsOfUnity ℓ (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hHopen : IsOpen ((IntermediateField.adjoin ℚ
      (((↑) : (AlgebraicClosure ℚ)ˣ → AlgebraicClosure ℚ) ''
        (rootsOfUnity ℓ (AlgebraicClosure ℚ) :
          Set (AlgebraicClosure ℚ)ˣ))).fixingSubgroup :
      Set (Field.absoluteGaloisGroup ℚ)) :=
    (IntermediateField.adjoin ℚ _).fixingSubgroup_isOpen
  refine continuous_def.mpr fun U _ => isOpen_iff_forall_mem_open.mpr fun σ hσ => ?_
  open Pointwise in
  refine ⟨σ • ((IntermediateField.adjoin ℚ
    (((↑) : (AlgebraicClosure ℚ)ˣ → AlgebraicClosure ℚ) ''
      (rootsOfUnity ℓ (AlgebraicClosure ℚ) :
        Set (AlgebraicClosure ℚ)ˣ))).fixingSubgroup :
    Set (Field.absoluteGaloisGroup ℚ)), ?_, hHopen.leftCoset σ, ?_⟩
  · rintro τ' ⟨u, hu, rfl⟩
    show (((cyclotomicCharacterModL ℓ (σ * u) : (ZMod ℓ)ˣ) : ZMod ℓ)) ∈ U
    rw [map_mul, cyclotomicCharacterModL_eq_one ℓ hu, mul_one]
    exact hσ
  · exact ⟨1, Subgroup.one_mem _, mul_one σ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Membership of a prime in a prime's place: `p` lies in the height-one
prime of `𝓞 ℚ` attached to `q` iff `p = q`. (Used for the
different-residue-characteristic side conditions of the compatible-family
compatibility in `residual_charFrob_eq_of_family`.) -/
lemma natCast_mem_toHeightOneSpectrum_iff {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    (p : NumberField.RingOfIntegers ℚ) ∈
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal ↔ p = q := by
  have h1 : (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm)
        (Ideal.span {(q : ℤ)}) := rfl
  rw [h1, Ideal.mem_comap, map_natCast, Ideal.mem_span_singleton,
    Int.natCast_dvd_natCast]
  exact ⟨fun hdvd => ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd).symm,
    fun h => h ▸ dvd_rfl⟩

/-- **Units away from the residue characteristic**: a prime
`p ≠ q` is a unit in the completed integers at the `q`-place of `ℚ` (its
`q`-adic valuation is `1`). Ensures `ℓ^k ∉ Q` in the Frobenius
roots-of-unity argument of `cyclotomicCharacter_globalFrob`. -/
theorem isUnit_natCast_adicCompletionIntegers {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) :
    IsUnit ((p : ℕ) : (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
  -- DERIVED (2026-07-16): a unit of the valuation subring is an element of
  -- valuation one; the completion's valuation restricts to the global
  -- `v`-adic valuation, which on the integer `p` is the `intValuation`,
  -- equal to one exactly when `p ∉ v` — i.e. `p ≠ q` by
  -- `natCast_mem_toHeightOneSpectrum_iff`.
  have hints : (Valued.v).Integers
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) :=
    Valuation.valuationSubring.integers _
  refine hints.isUnit_iff_valuation_eq_one.mpr ?_
  rw [map_natCast]
  have h2 := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
    (K := ℚ) (v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)
    ((p : ℕ) : NumberField.RingOfIntegers ℚ)
  push_cast at h2
  rw [h2, show ((p : ℕ) : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ
      ((p : ℕ) : NumberField.RingOfIntegers ℚ) from (map_natCast _ p).symm,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff,
    natCast_mem_toHeightOneSpectrum_iff hp hq]
  exact hne

/-- **The `ℓ`-adic cyclotomic character at Frobenius**: the
`ℓ`-adic cyclotomic character evaluates to `q` at the global arithmetic
Frobenius of a prime `q ≠ ℓ` — the arithmetic Frobenius at `q` acts on
all `ℓ`-power roots of unity by `ζ ↦ ζ^q` (`μ_{ℓ^∞}` is unramified at
`q`, and Frobenius reduces to the `q`-power map on the residue field).
The mod-`ℓ` statement `cyclotomicCharacterModL_globalFrob` is DERIVED
from this below. -/
theorem cyclotomicCharacter_globalFrob {ℓ q : ℕ} [Fact ℓ.Prime]
    (hq : q.Prime) (hne : q ≠ ℓ) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ
        (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          hq)).toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (q : ℤ_[ℓ]) := by
  -- Core: the global Frobenius raises every `ℓ^k`-th root of unity to
  -- its `q`-th power.
  have hfrob : ∀ (k : ℕ) (ζ : AlgebraicClosure ℚ), ζ ^ ℓ ^ k = 1 →
      globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) ζ =
        ζ ^ q := by
    intro k ζ hζ
    set v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq
    -- transport along the chosen embedding of algebraic closures
    have hι := Field.absoluteGaloisGroup.lift_map
      (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) _ _
        (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v))
      (Field.AbsoluteGaloisGroup.adicArithFrob v) ζ
    set η := AlgebraicClosure.map
      (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) _ _
        (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v))
      ζ with hηdef
    have hη : η ^ ℓ ^ k = 1 := by
      rw [hηdef, ← map_pow, hζ, map_one]
    -- the root of unity is integral over the completed integers
    have hint : IsIntegral
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) η := by
      refine IsIntegral.of_pow (n := ℓ ^ k)
        (pow_pos (Fact.out : ℓ.Prime).pos k) ?_
      rw [hη]
      exact isIntegral_one
    -- Frobenius action on the integral element
    have harith := Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := v)
    have hnotmem : ((ℓ ^ k : ℕ) : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∉
        IsLocalRing.maximalIdeal _ := by
      have hu : IsUnit ((ℓ : ℕ) :
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) :=
        isUnit_natCast_adicCompletionIntegers (Fact.out : ℓ.Prime) hq
          (fun h => hne h.symm)
      have hu2 : IsUnit ((ℓ ^ k : ℕ) : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
        rw [Nat.cast_pow]
        exact (hu.map (algebraMap _ _)).pow k
      exact fun hmem => ((IsLocalRing.mem_maximalIdeal _).mp hmem) hu2
    -- apply the Frobenius property to the integral root of unity
    have hpow : (⟨η, hint⟩ : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ^ ℓ ^ k
        = 1 := by
      apply Subtype.ext
      show η ^ ℓ ^ k = 1
      exact hη
    have happ := AlgHom.IsArithFrobAt.apply_of_pow_eq_one harith hpow hnotmem
    rw [natCard_residue_quotient_toHeightOneSpectrum hq] at happ
    have hcoord := congrArg Subtype.val happ
    have hact : Field.AbsoluteGaloisGroup.adicArithFrob v η = η ^ q :=
      hcoord
    -- descend through the injective embedding
    apply (AlgebraicClosure.map
      (@algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) _ _
        (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ v))).injective
    rw [map_pow]
    unfold globalFrob
    exact hι.trans hact
  -- conclude by `ℓ`-adic uniqueness across all levels
  haveI : ∀ i : ℕ, NeZero (ℓ ^ i) :=
    fun i => ⟨pow_ne_zero i (Fact.out : ℓ.Prime).ne_zero⟩
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  have huniq := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) (ℓ ^ k))
    (g := (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
      hq)).toRingEquiv) (c := ((q : ZMod (ℓ ^ k)))) ?_
  · exact huniq.symm
  · intro t ht
    have h1 : (t : AlgebraicClosure ℚ) ^ ℓ ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ t).mp ht,
        Units.val_one]
    have h2 : (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        hq)).toRingEquiv (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ q :=
      hfrob k (t : AlgebraicClosure ℚ) h1
    rw [h2, ZMod.val_natCast]
    exact pow_eq_pow_mod q h1

set_option backward.isDefEq.respectTransparency false in
/-- **The mod-`ℓ` cyclotomic character at Frobenius**: evaluates to `q`
at the global arithmetic Frobenius of a prime `q ≠ ℓ`. DERIVED from the
`ℓ`-adic statement `cyclotomicCharacter_globalFrob` by reduction: on an
`ℓ`-th root of unity `t`, `cyclotomicCharacter.spec` (at `n = 1`) makes
Frobenius act by the exponent `((q : ℤ_[ℓ]).toZModPow 1).val = q % ℓ`,
which is the defining property of the value `(q : ZMod ℓ)` of the
modular character (`modularCyclotomicCharacter.unique`). -/
theorem cyclotomicCharacterModL_globalFrob {ℓ q : ℕ} [Fact ℓ.Prime]
    (hq : q.Prime) (hne : q ≠ ℓ) :
    ((cyclotomicCharacterModL ℓ
        (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) :
      (ZMod ℓ)ˣ) : ZMod ℓ) = (q : ZMod ℓ) := by
  have hpadic := cyclotomicCharacter_globalFrob (ℓ := ℓ) hq hne
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)
    _ (c := (q : ZMod ℓ)) ?_).symm
  intro t ht
  have ht1 : (t : AlgebraicClosure ℚ) ^ ℓ ^ 1 = 1 := by
    rw [pow_one, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ t).mp ht,
      Units.val_one]
  have hspec := cyclotomicCharacter.spec ℓ
    (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
      hq)).toRingEquiv (t : AlgebraicClosure ℚ) ht1
  rw [hpadic] at hspec
  have hval : ((q : ℤ_[ℓ]).toZModPow 1).val = ((q : ZMod ℓ)).val := by
    rw [map_natCast, ZMod.val_natCast, ZMod.val_natCast, pow_one]
  rw [hval] at hspec
  exact hspec

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero proper invariant submodule refutes irreducibility. -/
lemma not_isIrreducible_of_invariant_submodule {ℓ : ℕ} [Fact ℓ.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    (ρbar : GaloisRep ℚ (ZMod ℓ) V) (W : Submodule (ZMod ℓ) V)
    (hne : W ≠ ⊥) (htop : W ≠ ⊤)
    (hinv : ∀ g v, v ∈ W → ρbar g v ∈ W) :
    ¬ ρbar.IsIrreducible := by
  intro hirr
  haveI : IsSimpleOrder (Subrepresentation
      ρbar.toRepresentation) := hirr
  rcases eq_bot_or_eq_top
    (⟨W, fun g v hv => hinv g v hv⟩ :
      Subrepresentation ρbar.toRepresentation) with hP | hP
  · exact hne (congrArg Subrepresentation.toSubmodule hP)
  · exact htop (congrArg Subrepresentation.toSubmodule hP)

set_option backward.isDefEq.respectTransparency false in
/-- **Stable-line extraction**: a non-irreducible 2-dimensional mod-`ℓ`
representation has a Galois-stable line. (Converse direction to
`not_isIrreducible_of_invariant_submodule`; the first step of the Serre
§4.1 analysis of the reducible Frey representation — the stable line is
the rational subgroup of order `ℓ`.) -/
lemma exists_stable_line_of_not_isIrreducible {ℓ : ℕ} [Fact ℓ.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Module.Finite (ZMod ℓ) V] [Module.Free (ZMod ℓ) V]
    (hdim : Module.rank (ZMod ℓ) V = 2)
    (ρbar : GaloisRep ℚ (ZMod ℓ) V) (hirr : ¬ ρbar.IsIrreducible) :
    ∃ W : Submodule (ZMod ℓ) V, Module.finrank (ZMod ℓ) W = 1 ∧
      ∀ g v, v ∈ W → ρbar g v ∈ W := by
  classical
  have hfr : Module.finrank (ZMod ℓ) V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  haveI : Nontrivial V := by
    rw [← rank_pos_iff_nontrivial (R := (ZMod ℓ)), hdim]
    norm_num
  -- the subrepresentation lattice is nontrivial …
  haveI : Nontrivial (Subrepresentation ρbar.toRepresentation) := by
    refine ⟨⊥, ⊤, fun hbt => ?_⟩
    have := congrArg Subrepresentation.toSubmodule hbt
    exact bot_ne_top (α := Submodule (ZMod ℓ) V) this
  -- … so non-simplicity produces a proper nonzero subrepresentation
  obtain ⟨P, hPbot, hPtop⟩ : ∃ P : Subrepresentation ρbar.toRepresentation,
      P ≠ ⊥ ∧ P ≠ ⊤ := by
    by_contra hall
    push Not at hall
    exact hirr ⟨fun P => or_iff_not_imp_left.mpr (hall P)⟩
  have hbot' : P.toSubmodule ≠ ⊥ := fun h =>
    hPbot (Subrepresentation.toSubmodule_injective
      (h.trans (rfl : (⊥ : Subrepresentation _).toSubmodule = ⊥).symm))
  have htop' : P.toSubmodule ≠ ⊤ := fun h =>
    hPtop (Subrepresentation.toSubmodule_injective
      (h.trans (rfl : (⊤ : Subrepresentation _).toSubmodule = ⊤).symm))
  refine ⟨P.toSubmodule, ?_, fun g v hv => P.apply_mem_toSubmodule g hv⟩
  -- the dimension sandwich forces a line
  have hlt : Module.finrank (ZMod ℓ) P.toSubmodule < 2 :=
    hfr ▸ Submodule.finrank_lt htop'
  have hpos : 0 < Module.finrank (ZMod ℓ) P.toSubmodule := by
    rw [Module.finrank_pos_iff]
    exact (Submodule.nontrivial_iff_ne_bot).mpr hbot'
  omega

set_option backward.isDefEq.respectTransparency false in
/-- **Brauer–Nesbitt, 2-dimensional mod-`ℓ` instance**: a 2-dimensional
mod-`ℓ` representation of `Γ ℚ` whose characteristic polynomials agree
*everywhere* with those of `1 ⊕ χ̄` is not irreducible.

DERIVED (elementary route, no semisimplification): Cayley–Hamilton turns
the charpoly hypothesis into `(ρ g − 1)(ρ g − χ̄ g) = 0`. On the kernel
`H` of `χ̄` every element is unipotent, so Kolchin's theorem in dimension
2 (`BrauerNesbitt.exists_fixed_of_unipotent`) gives a nonzero `H`-fixed
subspace `W`; `W` is Galois-stable because `H` is normal. If `W` is
proper, done. If `W = ⊤` then `ρ` kills `H`, hence has commuting image
(commutators land in `H`), each member annihilated by a split quadratic;
the common-eigenvector lemma
(`BrauerNesbitt.exists_common_eigenvector_of_commuting`) produces an
invariant line. -/
theorem not_isIrreducible_of_charpoly_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Module.Finite (ZMod ℓ) V] [Module.Free (ZMod ℓ) V]
    (hdim : Module.rank (ZMod ℓ) V = 2)
    (ρbar : GaloisRep ℚ (ZMod ℓ) V)
    (h : ∀ g, (ρbar g).charpoly =
      Polynomial.X ^ 2
        - Polynomial.C (((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1)
            * Polynomial.X
        + Polynomial.C ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)) :
    ¬ ρbar.IsIrreducible := by
  classical
  have hfr : Module.finrank (ZMod ℓ) V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  -- Cayley–Hamilton: `(ρ g − 1)(ρ g − χ̄ g) = 0`
  have hCH : ∀ g, (ρbar g - 1) * (ρbar g - algebraMap (ZMod ℓ)
      (Module.End (ZMod ℓ) V)
      ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)) = 0 := by
    intro g
    have hch := LinearMap.aeval_self_charpoly (ρbar g)
    rw [h g] at hch
    simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C] at hch
    have hcomm : Commute (ρbar g) (algebraMap (ZMod ℓ)
        (Module.End (ZMod ℓ) V)
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)) :=
      (Algebra.commute_algebraMap_right _ _)
    have hexp : (ρbar g - 1) * (ρbar g - algebraMap (ZMod ℓ)
        (Module.End (ZMod ℓ) V)
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)) =
        (ρbar g) ^ 2 - (algebraMap (ZMod ℓ) (Module.End (ZMod ℓ) V)
          ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)
          + algebraMap (ZMod ℓ) (Module.End (ZMod ℓ) V) 1) * ρbar g
        + algebraMap (ZMod ℓ) (Module.End (ZMod ℓ) V)
          ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
      have e1 : (ρbar g - 1) * (ρbar g - algebraMap (ZMod ℓ)
          (Module.End (ZMod ℓ) V)
          ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)) =
          ρbar g * ρbar g - ρbar g * algebraMap (ZMod ℓ)
            (Module.End (ZMod ℓ) V)
            ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)
          - ρbar g + algebraMap (ZMod ℓ) (Module.End (ZMod ℓ) V)
            ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
        noncomm_ring
      rw [e1, hcomm.eq, map_one]
      noncomm_ring
    rw [hexp]
    exact hch
  -- the kernel of the character acts unipotently
  by_cases hWtop : (⨅ hH : (cyclotomicCharacterModL ℓ).ker,
      LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) = ⊤
  · -- `ρ` kills the kernel of `χ̄`: commuting image, split quadratics
    have hker1 : ∀ hH : (cyclotomicCharacterModL ℓ).ker,
        ρbar (hH : Field.absoluteGaloisGroup ℚ) = 1 := by
      intro hH
      ext v
      have hv : v ∈ (⨅ hH : (cyclotomicCharacterModL ℓ).ker,
          LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1)) :=
        hWtop ▸ Submodule.mem_top
      have := (Submodule.mem_iInf _).mp hv hH
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      simpa using this
    have hcommim : ∀ g₁ g₂, Commute (ρbar g₁) (ρbar g₂) := by
      intro g₁ g₂
      have hc : g₁⁻¹ * g₂⁻¹ * g₁ * g₂ ∈ (cyclotomicCharacterModL ℓ).ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [mul_comm ((cyclotomicCharacterModL ℓ) g₁)⁻¹
          ((cyclotomicCharacterModL ℓ) g₂)⁻¹, mul_assoc, mul_assoc,
          ← mul_assoc ((cyclotomicCharacterModL ℓ) g₁)⁻¹,
          inv_mul_cancel, one_mul, inv_mul_cancel]
      have h1 := hker1 ⟨g₁⁻¹ * g₂⁻¹ * g₁ * g₂, hc⟩
      have h2 : ρbar (g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂)) = ρbar g₁ := by
        rw [map_mul]
        simp only at h1
        rw [h1, mul_one]
      have h3 : g₁ * (g₁⁻¹ * g₂⁻¹ * g₁ * g₂) = g₂⁻¹ * g₁ * g₂ := by
        group
      rw [h3, map_mul, map_mul] at h2
      unfold Commute SemiconjBy
      have hcancel : ρbar g₂ * ρbar g₂⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      calc ρbar g₁ * ρbar g₂
          = ρbar g₂ * ρbar g₂⁻¹ * (ρbar g₁ * ρbar g₂) := by
            rw [hcancel, one_mul]
      _ = ρbar g₂ * (ρbar g₂⁻¹ * ρbar g₁ * ρbar g₂) := by
            noncomm_ring
      _ = ρbar g₂ * ρbar g₁ := by rw [h2]
    obtain ⟨v, hv, heig⟩ :=
      BrauerNesbitt.exists_common_eigenvector_of_commuting hdim
        (Set.range fun g => ρbar g)
        (by rintro _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩; exact hcommim g₁ g₂)
        (by
          rintro _ ⟨g, rfl⟩
          exact ⟨1, ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ),
            by rw [map_one]; exact hCH g⟩)
    refine not_isIrreducible_of_invariant_submodule ρbar
      (Submodule.span (ZMod ℓ) {v}) ?_ ?_ ?_
    · simpa [Submodule.span_singleton_eq_bot] using hv
    · intro htop
      have h1 : Module.finrank (ZMod ℓ) (Submodule.span (ZMod ℓ) {v}) = 1 :=
        finrank_span_singleton hv
      rw [htop] at h1
      rw [finrank_top] at h1
      omega
    · intro g x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨c, hc⟩ := heig (ρbar g) ⟨g, rfl⟩
      rw [map_smul, hc]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self v))
  · -- the `H`-fixed space is nonzero (Kolchin), proper, and Galois-stable
    let ρH : (cyclotomicCharacterModL ℓ).ker →* Module.End (ZMod ℓ) V :=
      { toFun := fun hH => ρbar (hH : Field.absoluteGaloisGroup ℚ)
        map_one' := map_one ρbar
        map_mul' := fun x y => map_mul ρbar _ _ }
    have huni : ∀ hH : (cyclotomicCharacterModL ℓ).ker,
        (ρH hH - 1) ^ 2 = 0 := by
      intro hH
      have hχ1 : ((cyclotomicCharacterModL ℓ
          (hH : Field.absoluteGaloisGroup ℚ) : (ZMod ℓ)ˣ) : ZMod ℓ) = 1 := by
        rw [MonoidHom.mem_ker.mp hH.2]
        rfl
      have hthis := hCH (hH : Field.absoluteGaloisGroup ℚ)
      rw [hχ1, map_one] at hthis
      rw [pow_two]
      exact hthis
    obtain ⟨v₀, hv₀ne, hv₀fix⟩ :=
      BrauerNesbitt.exists_fixed_of_unipotent hdim ρH huni
    refine not_isIrreducible_of_invariant_submodule ρbar
      (⨅ hH : (cyclotomicCharacterModL ℓ).ker,
        LinearMap.ker (ρbar (hH : Field.absoluteGaloisGroup ℚ) - 1))
      ?_ hWtop ?_
    · refine Submodule.ne_bot_iff _ |>.mpr ⟨v₀, ?_, hv₀ne⟩
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact hv₀fix hH
    · intro g v hv
      refine (Submodule.mem_iInf _).mpr fun hH => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      have hconj : (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) ∈
          (cyclotomicCharacterModL ℓ).ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, MonoidHom.mem_ker.mp hH.2]
        rw [mul_one, inv_mul_cancel]
      have hfix := (Submodule.mem_iInf _).mp hv ⟨_, hconj⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
        Module.End.one_apply] at hfix
      have hrw : (hH : Field.absoluteGaloisGroup ℚ) * g =
          g * (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) := by group
      calc ρbar (hH : Field.absoluteGaloisGroup ℚ) (ρbar g v)
          = ρbar ((hH : Field.absoluteGaloisGroup ℚ) * g) v := by
            rw [map_mul]; rfl
      _ = ρbar g (ρbar (g⁻¹ * (hH : Field.absoluteGaloisGroup ℚ) * g) v) := by
            rw [hrw, map_mul]; rfl
      _ = ρbar g v := by rw [hfix]

/-!
## Bridge lemmas for the derivation of `not_isIrreducible_of_charFrob_eq`

Three fully-proven ingredients used to combine the nodes above:
the module topology on a finite module over a discrete ring is discrete
(so evaluation-and-coefficient maps out of a mod-`ℓ` representation are
continuous into discrete targets); every finite place of `ℚ` is the place
of a unique prime number; and monic quadratics are determined by their
two low coefficients.
-/

set_option backward.isDefEq.respectTransparency false in
/-- The module topology on a finite module over a discrete topological
ring is discrete: the module is a linear quotient of a finite power of
the ring, the power carries the (discrete) product topology, and the
module topology is coinduced along the surjection. -/
lemma discreteTopology_moduleTopology (R M : Type*) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    @DiscreteTopology M (moduleTopology R M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  refine @DiscreteTopology.mk M (moduleTopology R M) ?_
  rw [ModuleTopology.eq_coinduced_of_surjective hf,
    DiscreteTopology.eq_bot (α := Fin n → R), coinduced_bot]




set_option backward.isDefEq.respectTransparency false in
/-- Distinct primes give distinct finite places of `ℚ`: the associated
height-one primes of `ℤ` are the distinct span ideals. -/
lemma toHeightOneSpectrumRingOfIntegersRat_injective {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (h : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hp =
      Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) : p = q := by
  have h1 : Nat.Prime.toHeightOneSpectrumInt hp =
      Nat.Prime.toHeightOneSpectrumInt hq :=
    (Rat.ringOfIntegersEquiv.symm.heightOneSpectrum).injective h
  have h2 : (Nat.Prime.toHeightOneSpectrumInt hp).asIdeal =
      (Nat.Prime.toHeightOneSpectrumInt hq).asIdeal := congrArg _ h1
  have h3 : (Ideal.span {(p : ℤ)} : Ideal ℤ) = Ideal.span {(q : ℤ)} := h2
  have h4 : Associated (p : ℤ) (q : ℤ) :=
    (Ideal.span_singleton_eq_span_singleton).mp h3
  have h5 := Int.associated_iff_natAbs.mp h4
  simpa using h5

set_option backward.isDefEq.respectTransparency false in
/-- Every finite place of `ℚ` is the place of a prime number: the
corresponding height-one prime of `ℤ` is generated by a prime. -/
lemma exists_prime_toHeightOneSpectrum
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ (q : ℕ) (hq : q.Prime),
      v = Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq := by
  -- transport `v` to a height-one prime of `ℤ`
  set e : IsDedekindDomain.HeightOneSpectrum ℤ ≃
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    (Rat.ringOfIntegersEquiv.symm.heightOneSpectrum)
  obtain ⟨w, rfl⟩ := e.surjective v
  -- `w.asIdeal` is a nonzero prime ideal of the PID `ℤ`, hence generated
  -- by a prime integer
  set a : ℤ := Submodule.IsPrincipal.generator (w.asIdeal)
  have ha : Ideal.span {a} = w.asIdeal := Ideal.span_singleton_generator _
  have ha0 : a ≠ 0 := by
    intro h
    apply w.ne_bot
    rw [← ha, h]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hsp : (Ideal.span {a} : Ideal ℤ).IsPrime := ha ▸ w.isPrime
  have haprime : Prime a := (Ideal.span_singleton_prime ha0).mp hsp
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp haprime, ?_⟩
  show e w = e (Nat.Prime.toHeightOneSpectrumInt
    (Int.prime_iff_natAbs_prime.mp haprime))
  refine congrArg e ?_
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show w.asIdeal = Ideal.span {((a.natAbs : ℕ) : ℤ)}
  rw [← ha, Ideal.span_singleton_eq_span_singleton]
  exact Int.associated_natAbs a

section ComparisonQuadratic

open Polynomial

variable {R : Type*} [CommRing R]

/-- The degree of the sub-quadratic remainder `−(a+1)X + a` is below two. -/
private lemma degree_comparisonRest_lt (a : R) :
    (-(C (a + 1) * X) + C a : R[X]).degree < ((2 : ℕ) : WithBot ℕ) := by
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · rw [Polynomial.degree_neg]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

/-- The comparison quadratic `X² − (a+1)X + a` (the characteristic
polynomial of `diag(1, a)`) is monic. -/
lemma monic_comparisonQuadratic (a : R) :
    (X ^ 2 - C (a + 1) * X + C a).Monic := by
  have := Polynomial.monic_X_pow_add (n := 2) (degree_comparisonRest_lt a)
  have heq : X ^ 2 + (-(C (a + 1) * X) + C a) = X ^ 2 - C (a + 1) * X + C a := by
    ring
  rwa [heq] at this

/-- The comparison quadratic has `natDegree` two. -/
lemma natDegree_comparisonQuadratic [Nontrivial R] (a : R) :
    (X ^ 2 - C (a + 1) * X + C a).natDegree = 2 := by
  have heq : X ^ 2 - C (a + 1) * X + C a = X ^ 2 + (-(C (a + 1) * X) + C a) := by
    ring
  have hdeg : (X ^ 2 + (-(C (a + 1) * X) + C a) : R[X]).degree =
      ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact degree_comparisonRest_lt a),
      Polynomial.degree_X_pow]
  rw [heq]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- The linear coefficient of the comparison quadratic. -/
lemma coeff_one_comparisonQuadratic (a : R) :
    (X ^ 2 - C (a + 1) * X + C a).coeff 1 = -(a + 1) := by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

/-- The constant coefficient of the comparison quadratic. -/
lemma coeff_zero_comparisonQuadratic (a : R) :
    (X ^ 2 - C (a + 1) * X + C a).coeff 0 = a := by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

/-- The degree of a linear-plus-constant remainder is below two
(parametrized form). -/
private lemma degree_quadraticRest_lt (t d : R) :
    (-(C t * X) + C d : R[X]).degree < ((2 : ℕ) : WithBot ℕ) := by
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · rw [Polynomial.degree_neg]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

/-- The generic monic quadratic `X² − tX + d` is monic. -/
lemma monic_quadratic (t d : R) : (X ^ 2 - C t * X + C d).Monic := by
  have := Polynomial.monic_X_pow_add (n := 2) (degree_quadraticRest_lt t d)
  have heq : X ^ 2 + (-(C t * X) + C d) = X ^ 2 - C t * X + C d := by ring
  rwa [heq] at this

/-- The generic monic quadratic has `natDegree` two. -/
lemma natDegree_quadratic [Nontrivial R] (t d : R) :
    (X ^ 2 - C t * X + C d).natDegree = 2 := by
  have heq : X ^ 2 - C t * X + C d = X ^ 2 + (-(C t * X) + C d) := by ring
  have hdeg : (X ^ 2 + (-(C t * X) + C d) : R[X]).degree =
      ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact degree_quadraticRest_lt t d),
      Polynomial.degree_X_pow]
  rw [heq]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- The linear coefficient of the generic monic quadratic. -/
lemma coeff_one_quadratic (t d : R) :
    (X ^ 2 - C t * X + C d).coeff 1 = -t := by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

/-- The constant coefficient of the generic monic quadratic. -/
lemma coeff_zero_quadratic (t d : R) :
    (X ^ 2 - C t * X + C d).coeff 0 = d := by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C]

end ComparisonQuadratic


set_option backward.isDefEq.respectTransparency false in
/-- The residue map `PadicInt.toZMod` agrees with `toZModPow 1` composed
with the canonical `ZMod (p ^ 1) ≃+* ZMod p`: ring homomorphisms into
`ZMod p` are determined by their kernels, and both sides have kernel the
maximal ideal. This bridges the residue map used in the
`IsHardlyRamified` statements (via the `Algebra ℤ_[p] (ZMod p)` instance)
with the `toZModPow` tower of `cyclotomicCharacter.toZModPow`. -/
lemma toZMod_eq_ringEquivCongr_comp_toZModPow (p : ℕ) [Fact p.Prime] :
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p) =
      ((ZMod.ringEquivCongr (pow_one p)).toRingHom).comp
        (PadicInt.toZModPow 1) := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZMod]
  have hker : RingHom.ker (((ZMod.ringEquivCongr (pow_one p)).toRingHom).comp
      (PadicInt.toZModPow 1)) = RingHom.ker (PadicInt.toZModPow (p := p) 1) := by
    ext x
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      EmbeddingLike.map_eq_zero_iff]
  rw [hker, PadicInt.ker_toZModPow, pow_one]
  exact PadicInt.maximalIdeal_eq_span_p

/-- Two monic polynomials of degree `2` with equal linear and constant
coefficients are equal. -/
lemma monic_quadratic_ext {R : Type*} [CommRing R] {p q : Polynomial R}
    (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = 2) (hqd : q.natDegree = 2)
    (h1 : p.coeff 1 = q.coeff 1) (h0 : p.coeff 0 = q.coeff 0) : p = q := by
  ext n
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 =>
    have hp2 : p.coeff 2 = 1 := by rw [← hpd]; exact hp.coeff_natDegree
    have hq2 : q.coeff 2 = 1 := by rw [← hqd]; exact hq.coeff_natDegree
    rw [hp2, hq2]
  | (n + 3) =>
    rw [p.coeff_eq_zero_of_natDegree_lt (by omega),
      q.coeff_eq_zero_of_natDegree_lt (by omega)]

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
/-- **Characteristic polynomial of a 2-dimensional endomorphism**: on a
2-dimensional space, `charpoly f = X² − (tr f)·X + det f`. Bridges the
charpoly-level statements of the tree with trace/determinant data (used
by the compatibility bookkeeping of `residual_charFrob_eq_of_family`,
where B6c supplies traces and `IsHardlyRamified.det` supplies
determinants). -/
lemma charpoly_eq_quadratic_of_finrank_two {F : Type*} [CommRing F]
    [Nontrivial F] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] [Module.Free F V]
    (hfr : Module.finrank F V = 2) (f : V →ₗ[F] V) :
    f.charpoly = X ^ 2 - C (LinearMap.trace F V f) * X
      + C (LinearMap.det f) := by
  classical
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hfr
  have hM : (LinearMap.toMatrix b b f).charpoly = f.charpoly :=
    LinearMap.charpoly_toMatrix f b
  have htr : LinearMap.trace F V f = -(f.charpoly.coeff 1) := by
    rw [LinearMap.trace_eq_matrix_trace F b,
      Matrix.trace_eq_neg_charpoly_coeff, hM]
    norm_num
  have hdet : LinearMap.det f = f.charpoly.coeff 0 := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_eq_sign_charpoly_coeff, hM]
    norm_num
  refine monic_quadratic_ext (LinearMap.charpoly_monic f)
    (monic_quadratic _ _)
    (by rw [LinearMap.charpoly_natDegree, hfr]) (natDegree_quadratic _ _)
    ?_ ?_
  · rw [coeff_one_quadratic, htr, neg_neg]
  · rw [coeff_zero_quadratic, hdet]

end GaloisRepresentation
