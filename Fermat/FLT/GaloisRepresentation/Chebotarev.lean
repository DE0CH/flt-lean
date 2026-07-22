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
  number fields — itself now PROVEN by the classical Deuring reduction
  to the cyclic case over the fixed field of `⟨τ⟩`, using the PROVEN
  ramification-finiteness theorem `finite_setOf_exists_inertia_ne_bot`
  (via the different ideal). The single remaining sorry leaf of this
  module is `infinite_setOf_isArithFrobAt_zpowers`, the analytic core:
  Chebotarev for a cyclic extension of number fields, restricted to
  degree-one primes.

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

@[expose] public section

namespace GaloisRepresentation

open IsDedekindDomain
open scoped NumberField

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
    Ideal.quotientMap P (algebraMap A B) le_rfl with hgdef
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

open IsDedekindDomain in
/-- **Chebotarev, cyclic core** (sorry node): let `E/F` be an extension of
number fields whose Galois group is generated by a single element `τ` (so
`E/F` is finite cyclic; finiteness of the group, hence of the extension,
follows from topological finiteness of cyclic Galois groups — no
separate hypothesis is needed because `Gal(E/F)` of an infinite algebraic
extension is uncountable, never cyclic). Then infinitely many finite
places `P` of `F` have prime residue cardinality (residue degree one over
`ℚ`) and carry a prime `Q` of `𝓞 E` lying over `P` at which `τ` is an
arithmetic Frobenius (`τ x ≡ x ^ #(𝓞 F / P) (mod Q)`).

This is the analytic core of the Chebotarev density theorem after the
Deuring reduction (performed, PROVEN, in `infinite_setOf_isArithFrobAt`
below): only the cyclic case is stated, and only existence of infinitely
many degree-one primes is asked, exactly what the classical proof via
Hecke L-functions for the cyclic extension `E/F` produces (Neukirch VII
§13, or Lagarias–Odlyzko). The prime-residue-cardinality condition
encodes "residue degree one over `ℚ`", which is free density-wise (the
degree-`≥ 2` places of `F` have Dirichlet density zero) and is what makes
the statement push down through `F` to any subfield. Analytic base
available in mathlib for a future proof: Dirichlet's theorem on primes in
arithmetic progressions (`Mathlib.NumberTheory.LSeries.PrimesInAP`,
covering the case `F = ℚ`, `E` cyclotomic) and the L-series
nonvanishing machinery under it; the remaining mathematical content is
Chebotarev's field-crossing argument reducing the cyclic case to the
cyclotomic one, plus the zero-density estimate for degree-`≥ 2` places.

Why this leaf cannot be narrowed to the base `F = ℚ` even though every
consumer of the Chebotarev chain instantiates `K = ℚ`
(`dense_conjClasses_globalFrob (K := ℚ)` in `HardlyRamified/Lift.lean`
and `WeilPairing.lean`): the consumers need density of Frobenii in the
full absolute Galois group `Γ ℚ`, i.e. the finite-Galois-level statement
for EVERY finite Galois `L/ℚ` and every `τ ∈ Gal(L/ℚ)` — not only
abelian `L`. The Deuring reduction of that statement passes through the
fixed field `F = L^⟨τ⟩`, an arbitrary number field; so the cyclic core
is genuinely needed over arbitrary bases `F`, and mathlib's Dirichlet
theorem (base `ℚ`) alone cannot close it: the cyclotomic case over a
general base needs the Dedekind-zeta pole (or Hecke L-functions), which
is precisely the analytic content this leaf isolates. -/
theorem infinite_setOf_isArithFrobAt_zpowers
    {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] (τ : E ≃ₐ[F] E)
    (hgen : ∀ σ : E ≃ₐ[F] E, σ ∈ Subgroup.zpowers τ) :
    {P : HeightOneSpectrum (𝓞 F) | (Nat.card (𝓞 F ⧸ P.asIdeal)).Prime ∧
      ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧ Q.LiesOver P.asIdeal ∧
        IsArithFrobAt (𝓞 F) τ Q}.Infinite :=
  sorry

/-- The Galois group of a Galois extension of number fields acts
faithfully on the ring of integers: two automorphisms agreeing on `𝓞 E`
agree on `E = Frac(𝓞 E)`. -/
instance {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E] :
    FaithfulSMul (E ≃ₐ[F] E) (𝓞 E) where
  eq_of_smul_eq_smul {σ τ} h := by
    refine AlgEquiv.ext fun e => ?_
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
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
    with hFdef
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
    fun P => P.under (𝓞 K) with hπdef
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
  set S : Set L := ((↑) : Lˣ → L) '' (rootsOfUnity ℓ L : Set Lˣ) with hS
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

/-- **Units away from the residue characteristic** (sorry node): a prime
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

/-- **The `ℓ`-adic cyclotomic character at Frobenius** (sorry node): the
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
    set v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq with hv
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
  set a : ℤ := Submodule.IsPrincipal.generator (w.asIdeal) with hadef
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
