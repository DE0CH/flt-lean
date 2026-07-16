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

* **Chebotarev density** (`dense_conjClasses_globalFrob`, sorry node): for
  any finite set `S` of finite places of `ℚ`, the union of the conjugacy
  classes of the global Frobenius elements at places outside `S` is dense
  in `Γ ℚ`. This is the topological form of the Chebotarev density theorem
  needed here (density of Frobenii); the full measure-theoretic statement
  is strictly stronger and not required.

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
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Instances.ZMod

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

set_option warn.sorry false in
/-- **Chebotarev, finite level** (sorry node): modulo the fixing subgroup
of any finite subextension `E` of `K̄/K`, every element of the absolute
Galois group is a conjugate of a global Frobenius at a place outside any
given finite set `S`. This is the existence form of the Chebotarev
density theorem for the finite Galois closure of `E/K` (every element of
`Gal(E'/K)` is a Frobenius at infinitely many places), stated without
finite-quotient vocabulary: the coset `σ · Gal(K̄/E)` meets the Frobenius
conjugates. -/
theorem exists_frobenius_conj_mem_coset (S : Finset (Ω K))
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (σ : Γ K) :
    ∃ v : Ω K, v ∉ S ∧ ∃ g : Γ K,
      σ⁻¹ * (g * globalFrob v * g⁻¹) ∈ E.fixingSubgroup :=
  sorry

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

set_option warn.sorry false in
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
          hq)).toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (q : ℤ_[ℓ]) :=
  sorry

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
lemma charpoly_eq_quadratic_of_finrank_two {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
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
