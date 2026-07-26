/-
GaloisRepresentation/HardlyRamified/LevelLimit.lean — own work for the
Fermat project (not vendored from the FLT project).

# The profinite limit of a downward-directed system of finite levels

This module is the pure algebra/topology half of the 2026-07-26
construction cut of `Deformation.lean`'s
`exists_universalFrame_profinite_of_deformationCondition`. It contains no
arithmetic and no deformation theory: given a commutative ring `P` and a
family `𝒥` of ideals of `P` which is downward directed and all of whose
quotients `P ⧸ J` are FINITE, it builds

    lim_{J ∈ 𝒥} (P ⧸ J)

as a subring of the product `∏_{J ∈ 𝒥} (P ⧸ J)` of the levels, each
carrying its discrete topology, and establishes the facts the
deformation-theoretic assembly reads off it:

* `LevelLimit.compactSpace_limit`, `LevelLimit.t2Space_limit` — the limit
  is profinite, because the compatibility conditions are closed in a
  product of finite discrete rings;
* `LevelLimit.exists_ker_proj_subset` — the kernels of the projections
  `pr_J` are cofinal in the neighbourhood filter of `0`; this is where
  downward directedness of `𝒥` is used, and it is the clause that makes
  the topology of the limit LINEAR;
* `LevelLimit.exists_factor` — hence a CONTINUOUS ring map out of the
  limit into a finite DISCRETE ring factors through a single level, which
  is what turns a pro-object into a statement about one finite level;
* `LevelLimit.isUnit_of_forall_isUnit` — an element which is a unit at
  every level is a unit, the inverses at different levels being compatible
  by uniqueness of inverses. Together with a residue map to a field this
  is what makes the limit LOCAL.

Note that no compactness argument is needed for the projections to be
SURJECTIVE: the canonical map `LevelLimit.ofP : P → lim` already covers
each level, because the level maps `P ↠ P ⧸ J` are surjective. That is
what keeps this module elementary.

Mathlib has no "profinite ring as a filtered limit of finite rings"
(searched 2026-07-26: `Mathlib/Topology/Algebra/` has `ProfiniteGrp` but
nothing ring-theoretic of this shape, and `Mathlib/RingTheory/` has no
inverse-limit construction at all), and `~/cs/FLT` has no Schlessinger
material whatsoever, so this is written from scratch.

A second, independent section supplies the missing constructor
`LevelLimit.framedOfMatrices`: a continuous multiplicative family of
`2 × 2` matrices IS a framed Galois representation. Nothing in the
repository built a `GaloisRep` out of matrices before — every existing
representation is obtained from another one by `baseChange`/`conj` — and
an inverse limit has no choice but to assemble its representation out of
the level-wise matrices.
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep

@[expose] public section

open Topology

namespace LevelLimit

universe u

/-! ## Discrete coefficients -/

/-- A ring with the discrete topology is a topological ring. Stated as a
theorem rather than an instance so that this module cannot perturb
instance search anywhere else in the development. -/
theorem isTopologicalRing_of_discrete {A : Type*} [Ring A] [TopologicalSpace A]
    [DiscreteTopology A] : IsTopologicalRing A := by
  haveI : ContinuousAdd A := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousMul A := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousNeg A := ⟨continuous_of_discreteTopology⟩
  exact ⟨⟩

/-- **Over a DISCRETE coefficient ring the module topology is discrete.**
This is what makes a `GaloisRep` over a finite level a LOCALLY CONSTANT
function: its target `Module.End A A²` carries the module topology by the
definition of `GaloisRep`, and over a discrete `A` that topology is `⊥`.
Without this the level representations carry no usable continuity at
all. -/
theorem moduleTopology_eq_bot (A : Type*) [Ring A] [TopologicalSpace A]
    [DiscreteTopology A] (M : Type*) [AddCommGroup M] [Module A M] :
    moduleTopology A M = ⊥ := by
  refine le_antisymm ?_ bot_le
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  haveI : ContinuousSMul A M := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousAdd M := ⟨continuous_of_discreteTopology⟩
  exact moduleTopology_le A M

/-- **The matrix entries of a framed representation over a discrete ring
are continuous** — equivalently, such a representation is locally
constant.

BASE FIELD GENERALIZED 2026-07-26 (flt-lean-163): the base was the literal
`ℚ`; it is now an arbitrary number field `K`, because the `F`-level
Schlessinger construction in `HilbertModularity.lean` needs exactly this
statement over a totally real `F`. Every existing call site is at `ℚ` and
is unaffected — `K` is determined by the type of `ρ`. -/
theorem continuous_toMatrix' {K : Type*} [Field K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    [DiscreteTopology A] (ρ : FramedGaloisRep K A (Fin 2)) :
    Continuous (fun g => LinearMap.toMatrix' (ρ g)) := by
  letI : TopologicalSpace (Module.End A (Fin 2 → A)) :=
    moduleTopology A (Module.End A (Fin 2 → A))
  haveI : DiscreteTopology (Module.End A (Fin 2 → A)) :=
    ⟨moduleTopology_eq_bot A (Module.End A (Fin 2 → A))⟩
  have h : Continuous
      (fun g : Field.absoluteGaloisGroup K => (ρ g : Module.End A (Fin 2 → A))) :=
    ρ.continuous_toFun
  exact continuous_of_discreteTopology.comp h

/-! ## The limit of a family of levels -/

variable {P : Type u} [CommRing P]

/-- **The inverse limit `lim_{J ∈ 𝒥} P ⧸ J`**, as the subring of
compatible families inside the product of the levels. Compatibility is
imposed along every inclusion `J₁ ≤ J₂` of members of `𝒥`; no directedness
is needed to define it. -/
def levelSubring (𝒥 : Set (Ideal P)) : Subring (∀ J : 𝒥, P ⧸ (J : Ideal P)) where
  carrier := {x | ∀ (J₁ J₂ : 𝒥) (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P)),
    Ideal.Quotient.factor h (x J₁) = x J₂}
  mul_mem' := by
    intro a b ha hb J₁ J₂ h
    show Ideal.Quotient.factor h (a J₁ * b J₁) = a J₂ * b J₂
    rw [map_mul, ha J₁ J₂ h, hb J₁ J₂ h]
  one_mem' := by
    intro J₁ J₂ h
    show Ideal.Quotient.factor h 1 = 1
    rw [map_one]
  add_mem' := by
    intro a b ha hb J₁ J₂ h
    show Ideal.Quotient.factor h (a J₁ + b J₁) = a J₂ + b J₂
    rw [map_add, ha J₁ J₂ h, hb J₁ J₂ h]
  zero_mem' := by
    intro J₁ J₂ h
    show Ideal.Quotient.factor h 0 = 0
    rw [map_zero]
  neg_mem' := by
    intro a ha J₁ J₂ h
    show Ideal.Quotient.factor h (-(a J₁)) = -(a J₂)
    rw [map_neg, ha J₁ J₂ h]

/-- The underlying type of the inverse limit. -/
abbrev Limit (𝒥 : Set (Ideal P)) : Type u := ↥(levelSubring 𝒥)

/-- **The projection onto the level `J`.** -/
def proj (𝒥 : Set (Ideal P)) (J : 𝒥) : Limit 𝒥 →+* P ⧸ (J : Ideal P) where
  toFun x := (x : ∀ J : 𝒥, P ⧸ (J : Ideal P)) J
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The canonical map from `P` into its limit of levels**, sending `p` to
the constant family of its residues. Its existence is what makes every
projection surjective, with no compactness argument. -/
def ofP (𝒥 : Set (Ideal P)) : P →+* Limit 𝒥 where
  toFun p := ⟨fun J => Ideal.Quotient.mk (J : Ideal P) p,
    fun _ _ h => Ideal.Quotient.factor_mk h p⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

variable (𝒥 : Set (Ideal P))

@[simp] lemma proj_ofP (J : 𝒥) (p : P) :
    proj 𝒥 J (ofP 𝒥 p) = Ideal.Quotient.mk (J : Ideal P) p := rfl

-- (`proj 𝒥 J` is SURJECTIVE, with no compactness argument: it is already
-- surjective on the image of `ofP`, because `P ↠ P ⧸ J` is. No consumer needs
-- the statement in that form, so it is not recorded as a lemma — the
-- free-floating check forbids declarations outside the root's cone — but the
-- fact is used inline wherever a preimage is picked.)

lemma proj_compat (x : Limit 𝒥) (J₁ J₂ : 𝒥) (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P)) :
    Ideal.Quotient.factor h (proj 𝒥 J₁ x) = proj 𝒥 J₂ x := x.2 J₁ J₂ h

lemma ker_proj_le {J₁ J₂ : 𝒥} (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P)) :
    RingHom.ker (proj 𝒥 J₁) ≤ RingHom.ker (proj 𝒥 J₂) := by
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← proj_compat 𝒥 x J₁ J₂ h, hx, map_zero]

/-- An element of the limit killed by `pr_{J₁}` is killed by `pr_{J₂}` for
every larger `J₂`. -/
lemma proj_eq_zero_of_le {x : Limit 𝒥} {J₁ J₂ : 𝒥}
    (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P)) (hx : proj 𝒥 J₁ x = 0) :
    proj 𝒥 J₂ x = 0 := ker_proj_le 𝒥 h hx

/-! ### Directedness -/

/-- **Downward directedness extends to finite subfamilies.** -/
lemma exists_le_of_finset (hne : 𝒥.Nonempty)
    (hdir : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂)
    (s : Finset (Ideal P)) (hs : ∀ I ∈ s, I ∈ 𝒥) :
    ∃ J ∈ 𝒥, ∀ I ∈ s, J ≤ I := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨hne.choose, hne.choose_spec, by simp⟩
  | insert I s hIs ih =>
    have hI : I ∈ 𝒥 := hs I (Finset.mem_insert_self I s)
    obtain ⟨J₀, hJ₀, hJ₀le⟩ := ih fun K hK => hs K (Finset.mem_insert_of_mem hK)
    obtain ⟨J, hJ, hJle⟩ := hdir I hI J₀ hJ₀
    refine ⟨J, hJ, fun K hK => ?_⟩
    rcases Finset.mem_insert.mp hK with rfl | hK'
    · exact hJle.trans inf_le_left
    · exact (hJle.trans inf_le_right).trans (hJ₀le K hK')

/-! ### Units -/

/-- **An element which is a unit at every level is a unit.** The inverses
at the various levels are automatically compatible, inverses in a monoid
being unique. -/
theorem isUnit_of_forall_isUnit (x : Limit 𝒥)
    (h : ∀ J : 𝒥, IsUnit (proj 𝒥 J x)) : IsUnit x := by
  classical
  choose y hy using fun J : 𝒥 => (h J).exists_right_inv
  have hmem : (fun J : 𝒥 => y J) ∈ levelSubring 𝒥 := by
    intro J₁ J₂ hle
    have h1 : proj 𝒥 J₂ x * Ideal.Quotient.factor hle (y J₁) = 1 := by
      rw [← proj_compat 𝒥 x J₁ J₂ hle, ← map_mul, hy J₁, map_one]
    have h2 : proj 𝒥 J₂ x * y J₂ = 1 := hy J₂
    calc Ideal.Quotient.factor hle (y J₁)
        = (proj 𝒥 J₂ x * y J₂) * Ideal.Quotient.factor hle (y J₁) := by
          rw [h2, one_mul]
      _ = y J₂ * (proj 𝒥 J₂ x * Ideal.Quotient.factor hle (y J₁)) := by ring
      _ = y J₂ := by rw [h1, mul_one]
  have hprod : x * (⟨_, hmem⟩ : Limit 𝒥) = 1 :=
    Subtype.ext (funext fun J => hy J)
  exact ⟨⟨x, ⟨_, hmem⟩, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩

/-! ### Topology on the limit -/

section Topology

variable [∀ J : 𝒥, TopologicalSpace (P ⧸ (J : Ideal P))]

lemma continuous_proj (J : 𝒥) : Continuous (proj 𝒥 J) :=
  (continuous_apply J).comp continuous_subtype_val

variable [∀ J : 𝒥, DiscreteTopology (P ⧸ (J : Ideal P))]

/-- The ambient product of the levels is a topological ring. -/
theorem isTopologicalRing_pi :
    IsTopologicalRing (∀ J : 𝒥, P ⧸ (J : Ideal P)) := by
  haveI : ∀ J : 𝒥, IsTopologicalRing (P ⧸ (J : Ideal P)) :=
    fun _ => isTopologicalRing_of_discrete
  infer_instance

/-- The limit is a topological ring, being a subring of one. -/
theorem isTopologicalRing_limit : IsTopologicalRing (Limit 𝒥) := by
  haveI := isTopologicalRing_pi 𝒥
  infer_instance

theorem t2Space_limit : T2Space (Limit 𝒥) := by
  infer_instance

/-- **The compatibility conditions are closed.** -/
theorem isClosed_levelSubring :
    IsClosed ((levelSubring 𝒥 : Set (∀ J : 𝒥, P ⧸ (J : Ideal P)))) := by
  have hset : ((levelSubring 𝒥 : Set (∀ J : 𝒥, P ⧸ (J : Ideal P)))) =
      ⋂ (J₁ : 𝒥), ⋂ (J₂ : 𝒥), ⋂ (h : (J₁ : Ideal P) ≤ (J₂ : Ideal P)),
        {x : ∀ J : 𝒥, P ⧸ (J : Ideal P) |
          Ideal.Quotient.factor h (x J₁) = x J₂} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hset]
  refine isClosed_iInter fun J₁ => isClosed_iInter fun J₂ => isClosed_iInter fun h => ?_
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply J₁))
    (continuous_apply J₂)

/-- **The limit of a system of FINITE levels is compact.** -/
theorem compactSpace_limit [∀ J : 𝒥, Finite (P ⧸ (J : Ideal P))] :
    CompactSpace (Limit 𝒥) := by
  haveI : ∀ J : 𝒥, CompactSpace (P ⧸ (J : Ideal P)) := fun _ => Finite.compactSpace
  haveI : CompactSpace (∀ J : 𝒥, P ⧸ (J : Ideal P)) := Pi.compactSpace
  exact isCompact_iff_compactSpace.mp (isClosed_levelSubring 𝒥).isCompact

/-- The kernel of a projection is open. -/
theorem isOpen_ker_proj (J : 𝒥) :
    IsOpen ((RingHom.ker (proj 𝒥 J) : Ideal (Limit 𝒥)) : Set (Limit 𝒥)) := by
  have hpre : ((RingHom.ker (proj 𝒥 J) : Ideal (Limit 𝒥)) : Set (Limit 𝒥)) =
      (proj 𝒥 J) ⁻¹' {0} := by
    ext x
    simp [RingHom.mem_ker]
  rw [hpre]
  exact (isOpen_discrete _).preimage (continuous_proj 𝒥 J)

omit [∀ J : 𝒥, DiscreteTopology (P ⧸ (J : Ideal P))] in
/-- **The kernels of the projections are a neighbourhood basis of `0`.**
This is the clause that uses downward directedness, and it is what makes
the limit's topology linear.

(Discreteness of the levels is NOT needed: a basic neighbourhood of `0` in
the product constrains finitely many coordinates to lie in neighbourhoods
of `0`, and an element of `ker pr_J` has those coordinates equal to `0`
outright.) -/
theorem exists_ker_proj_subset (hne : 𝒥.Nonempty)
    (hdir : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂)
    {U : Set (Limit 𝒥)} (hU : U ∈ nhds (0 : Limit 𝒥)) :
    ∃ J : 𝒥, ((RingHom.ker (proj 𝒥 J) : Ideal (Limit 𝒥)) : Set (Limit 𝒥)) ⊆ U := by
  classical
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [show ((0 : Limit 𝒥) : ∀ J : 𝒥, P ⧸ (J : Ideal P)) = 0 from rfl, nhds_pi,
    Filter.mem_pi] at hV
  obtain ⟨I, hIfin, t, ht, htV⟩ := hV
  obtain ⟨J, hJ, hJle⟩ := exists_le_of_finset 𝒥 hne hdir
    (hIfin.toFinset.image (fun K : 𝒥 => (K : Ideal P)))
    (by
      intro K hK
      obtain ⟨K', _, rfl⟩ := Finset.mem_image.mp hK
      exact K'.2)
  refine ⟨⟨J, hJ⟩, fun x hx => hVU (htV ?_)⟩
  intro K hK
  have hKle : J ≤ (K : Ideal P) := by
    refine hJle (K : Ideal P) (Finset.mem_image.mpr ⟨K, ?_, rfl⟩)
    simpa using hK
  have hx0 : proj 𝒥 K x = 0 :=
    proj_eq_zero_of_le 𝒥 (J₁ := ⟨J, hJ⟩) (J₂ := K) hKle
      (by simpa [RingHom.mem_ker] using hx)
  have h0 : (0 : P ⧸ (K : Ideal P)) ∈ t K := mem_of_mem_nhds (ht K)
  show (x : ∀ J : 𝒥, P ⧸ (J : Ideal P)) K ∈ t K
  rw [show (x : ∀ J : 𝒥, P ⧸ (J : Ideal P)) K = proj 𝒥 K x from rfl, hx0]
  exact h0

omit [∀ J : 𝒥, DiscreteTopology (P ⧸ (J : Ideal P))] in
/-- **A continuous map out of the limit into a finite discrete ring
factors through a single level.** -/
theorem exists_factor (hne : 𝒥.Nonempty)
    (hdir : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂)
    {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (φ : Limit 𝒥 →+* A) (hφ : Continuous φ) :
    ∃ (J : 𝒥) (f : (P ⧸ (J : Ideal P)) →+* A),
      (∀ p : P, f (Ideal.Quotient.mk (J : Ideal P) p) = φ (ofP 𝒥 p)) ∧
      ∀ x : Limit 𝒥, f (proj 𝒥 J x) = φ x := by
  classical
  have hker : ((RingHom.ker φ : Ideal (Limit 𝒥)) : Set (Limit 𝒥)) ∈
      nhds (0 : Limit 𝒥) := by
    have hpre : ((RingHom.ker φ : Ideal (Limit 𝒥)) : Set (Limit 𝒥)) = φ ⁻¹' {0} := by
      ext x; simp [RingHom.mem_ker]
    rw [hpre]
    exact ((isOpen_discrete _).preimage hφ).mem_nhds (by simp)
  obtain ⟨J, hJ⟩ := exists_ker_proj_subset 𝒥 hne hdir hker
  have hkill : ∀ p ∈ (J : Ideal P), (φ.comp (ofP 𝒥)) p = 0 := by
    intro p hp
    have hmem : ofP 𝒥 p ∈ RingHom.ker (proj 𝒥 J) := by
      rw [RingHom.mem_ker, proj_ofP]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
    have := hJ hmem
    simpa [RingHom.mem_ker] using this
  refine ⟨J, Ideal.Quotient.lift (J : Ideal P) (φ.comp (ofP 𝒥)) hkill, fun _ => rfl, ?_⟩
  intro x
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (proj 𝒥 J x)
  have hsub : x - ofP 𝒥 p ∈ RingHom.ker (proj 𝒥 J) := by
    rw [RingHom.mem_ker, map_sub, proj_ofP, hp, sub_self]
  have hzero : φ x - φ (ofP 𝒥 p) = 0 := by
    have := hJ hsub
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub] at this
    exact this
  rw [← hp]
  show (φ.comp (ofP 𝒥)) p = φ x
  exact (sub_eq_zero.mp hzero).symm

/-- **The image of `P` is dense in the limit.** This is what makes a
continuous map out of the limit determined by its restriction along
`ofP`, which is how the universality and minimality clauses of the
deformation assembly are transported from `P` to the limit. -/
theorem dense_range_ofP (hne : 𝒥.Nonempty)
    (hdir : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, ∃ J ∈ 𝒥, J ≤ J₁ ⊓ J₂) :
    Dense (Set.range (ofP 𝒥 : P → Limit 𝒥)) := by
  haveI := isTopologicalRing_limit 𝒥
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  have hcont : Continuous (fun y : Limit 𝒥 => x + y) := continuous_const.add continuous_id
  have hU0 : (fun y : Limit 𝒥 => x + y) ⁻¹' U ∈ nhds (0 : Limit 𝒥) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rwa [add_zero]
  obtain ⟨J, hJ⟩ := exists_ker_proj_subset 𝒥 hne hdir hU0
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (proj 𝒥 J x)
  have hmem : ofP 𝒥 p - x ∈ RingHom.ker (proj 𝒥 J) := by
    rw [RingHom.mem_ker, map_sub, proj_ofP, hp, sub_self]
  refine ⟨ofP 𝒥 p, ?_, ⟨p, rfl⟩⟩
  have hin := hJ hmem
  simpa using hin

end Topology

/-! ## A framed representation out of a family of matrices -/

section Framed

variable {K : Type*} [Field K]
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **A continuous multiplicative family of `2 × 2` matrices is a framed
Galois representation.** The repository had no such constructor: every
`GaloisRep` in it is produced from another one by `baseChange`/`conj`, and
an inverse limit has nothing to base-change FROM — its representation has
to be assembled out of the level-wise matrices.

Continuity is the only real content. `Module.End A A²` carries the MODULE
topology by the definition of `GaloisRep`, `Matrix (Fin 2) (Fin 2) A`
carries the product topology, which is its module topology
(`IsModuleTopology.instPi` over `IsTopologicalSemiring.toIsModuleTopology`),
and `Matrix.toLin'` is `A`-linear, so
`IsModuleTopology.continuous_of_linearMap` applies. -/
noncomputable def framedOfMatrices
    (mat : Field.absoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) A)
    (hone : mat 1 = 1) (hmul : ∀ g h, mat (g * h) = mat g * mat h)
    (hcont : Continuous mat) : FramedGaloisRep K A (Fin 2) :=
  letI : TopologicalSpace (Module.End A (Fin 2 → A)) :=
    moduleTopology A (Module.End A (Fin 2 → A))
  haveI : IsModuleTopology A (Module.End A (Fin 2 → A)) := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End A (Fin 2 → A)) :=
    IsModuleTopology.toContinuousAdd A _
  haveI : IsModuleTopology A (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (IsModuleTopology A (Fin 2 → Fin 2 → A))
  { toFun := fun g => Matrix.toLin' (mat g)
    map_one' := by rw [hone]; exact Matrix.toLin'_one
    map_mul' := fun g h => by rw [hmul, Matrix.toLin'_mul]; rfl
    continuous_toFun := (IsModuleTopology.continuous_of_linearMap
      (Matrix.toLin' (R := A) (m := Fin 2) (n := Fin 2)).toLinearMap).comp hcont }

@[simp] lemma framedOfMatrices_apply
    (mat : Field.absoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) A)
    (hone : mat 1 = 1) (hmul : ∀ g h, mat (g * h) = mat g * mat h)
    (hcont : Continuous mat) (g : Field.absoluteGaloisGroup K) :
    framedOfMatrices mat hone hmul hcont g = Matrix.toLin' (mat g) := rfl

@[simp] lemma toMatrix'_framedOfMatrices
    (mat : Field.absoluteGaloisGroup K → Matrix (Fin 2) (Fin 2) A)
    (hone : mat 1 = 1) (hmul : ∀ g h, mat (g * h) = mat g * mat h)
    (hcont : Continuous mat) (g : Field.absoluteGaloisGroup K) :
    LinearMap.toMatrix' (framedOfMatrices mat hone hmul hcont g) = mat g := by
  rw [framedOfMatrices_apply, LinearMap.toMatrix'_toLin']

-- FLOATING CODE DELETED 2026-07-26: `toMatrix'_baseChange_conj` stood here.
-- flt-lean-99 added it to serve exactly one consumer — a SECOND hoist of
-- `Deformation.toMatrix'_pushforwardFrame`, which had to be dropped at
-- integration because `main` had already hoisted that same declaration
-- somewhere else. With the consumer gone nothing referenced this, so it fell
-- outside the used-constant cone of `fermat_last_theorem`. Recover from git
-- if a future reordering of `Deformation.lean` wants it back.

end Framed

/-! ## Conjugation bookkeeping

`GaloisRep.conj_trans` exists in `Deformation.lean`, but BELOW the node
this module serves, so it cannot be used there; these two are the same
facts under this module's namespace. -/

section Conj

variable {A : Type*} [CommRing A] [TopologicalSpace A]

theorem conj_trans {M N Q : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module A Q]
    (ρ : GaloisRep ℚ A M) (a : M ≃ₗ[A] N) (b : N ≃ₗ[A] Q) :
    (ρ.conj a).conj b = ρ.conj (a.trans b) := by
  refine GaloisRep.ext fun g => LinearMap.ext fun x => ?_
  simp only [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

theorem conj_refl {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep ℚ A M) : ρ.conj (LinearEquiv.refl A M) = ρ := by
  refine GaloisRep.ext fun g => LinearMap.ext fun x => ?_
  simp only [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.refl_apply, LinearEquiv.refl_symm]

end Conj

end LevelLimit
