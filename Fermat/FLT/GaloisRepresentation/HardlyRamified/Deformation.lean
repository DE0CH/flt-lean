/-
GaloisRepresentation/HardlyRamified/Deformation.lean — own work for the
Fermat project (not vendored from the FLT project).

# The Khare–Wintenberger lifting development, Family-free, over a general
finite coefficient field

This module is the proof-sharing refactor (2026-07-24) anticipated by
pillar α of `Modularity/KhareWintenberger.lean` and by `Lift.lean`'s
B6a: the deformation-theoretic lifting development formerly inlined in
`Lift.lean` — Mazur's category (`HardlyRamifiedDeformation`), the
universality strata, the finiteness and presentation strata with their
commutative-algebra leaves, the topology glue, the base-change /
conjugation transfer lemmas and the specialization-to-a-domain endgame
— extracted with exactly two deliberate changes:

1. **Family-freedom.** `Lift.lean` `public import`s `Family.lean`, which
   imports `Modularity/Interface.lean`, which imports
   `Modularity/KhareWintenberger.lean`; so nothing living in `Lift.lean`
   can be consumed by the Khare–Wintenberger cut without closing the
   interface's forbidden dependency cycle. The import audit (2026-07-24)
   showed the deformation development consumes NOTHING from
   `Family.lean` — only the B6bc compatibility chain, which stays in
   `Lift.lean`, does. This module imports only `Defs.lean`,
   `Chebotarev.lean` (proof-only, for `globalFrob`) and mathlib, so both
   `Lift.lean` (at `k = ZMod ℓ`) and `KhareWintenberger.lean` (pillar α)
   consume it. CIRCULARITY GUARD: no import from `Family.lean`,
   `Lift.lean` or `Modularity/*` may ever be added here.

2. **Coefficient generalization `ZMod ℓ` → `k`.** The residue
   coefficient field is an arbitrary finite field `k` carrying
   `Algebra ℤ_[ℓ] k` — which forces `char k = ℓ`
   (`natCast_self_eq_zero`) — as pillar α requires. Two statements
   changed shape relative to the historical `ZMod ℓ` development:
   * a reduction map `π : R →+* k` is no longer automatically surjective
     (over `ZMod ℓ` its image is a subring of the prime field), so
     surjectivity became a structure field of `HardlyRamifiedDeformation`
     (`π_surjective`) — matching Mazur's deformation category, where the
     residue identification is part of the data;
   * the presentation strata present the universal ring over a
     coefficient ring `Λ` — classically the Witt vectors `W(k)`, and
     just `ℤ_ℓ` at `k = ZMod ℓ` — pinned up to isomorphism by:
     complete Noetherian local domain, module-finite over `ℤ_ℓ`, maximal
     ideal `(ℓ)` (unramifiedness), residue field `k` (forced by the
     surjection onto the deformation ring). The pure
     commutative-algebra leaves (`isNoetherianRing_mvPowerSeries`, the
     prime-chain and height lemmas, the Krull glue) are correspondingly
     stated over an arbitrary Noetherian local domain base.

The sorried leaves (all SHARED by the two consumers; the names are those
of their historical `Lift.lean` twins): `exists_conj_of_charFrob_eq`,
`exists_isWeaklyUniversalOnIdentified`, `exists_isTraceGenerated_ringHom`,
`finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated`,
`exists_minimal_mvPowerSeries_presentation`,
`exists_relations_lt_of_minimal_mvPowerSeries_presentation`. Everything
else is proven glue, culminating in
`exists_hardlyRamified_lift_of_five_le` — verbatim the statement of
Khare–Wintenberger pillar α
(`exists_hardlyRamified_lift_residual_of_five_le`).
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- `IsAdic` / `IsAdicComplete`: they appear in the exposed field types of
-- the deformation-category structure `HardlyRamifiedDeformation`.
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
-- `MvPowerSeries` with its local-ring structure, and `Ideal.height`:
-- the vocabulary of the Böckle presentation stratum (exposed in the
-- presentation-leaf signatures).
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Height
-- single-variable power series: the variable-splitting leaf
-- `nonempty_ringEquiv_mvPowerSeries_powerSeries` is stated on them.
public import Mathlib.RingTheory.PowerSeries.Basic
-- proof-only: `globalFrob` (the Frobenius transport of
-- `charpoly_baseChange_conj`'s consumers) — Family-free, see the module
-- docstring.
import Fermat.FLT.GaloisRepresentation.Chebotarev
-- proof-only: the characteristic of a finite field, `ℤ_ℓ`-unit lemmas.
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
-- Krull's height theorem, consumed by the PROVEN Krull glue
-- `exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation`.
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
-- proof-only: the Hilbert-basis instance `IsNoetherianRing R⟦X⟧`, the
-- domain instances for (multivariate) power series.
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
-- proof-only imports for the topology glue
-- `isModuleTopology_of_isAdic_maximalIdeal`.
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Noetherian.Basic
-- proof-only: charpoly bridges and base-change linear algebra.
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open GaloisRepresentation Polynomial

namespace GaloisRepresentation

universe u v
/-- The standard rank-2 free module `Fin 2 → O` has rank 2. -/
lemma rank_finTwoFun (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

variable {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
variable {k : Type u} [Field k] [Finite k] [Algebra ℤ_[ℓ] k]

/-- **A finite field receiving `ℤ_ℓ` has characteristic `ℓ`** (PROVEN,
elementary): the characteristic of the finite field `k` is a prime `p`;
were `p ≠ ℓ`, then `p` would be a unit of `ℤ_ℓ` dying in `k` under the
structure map — impossible in the nontrivial `k`. Stated as the
vanishing of `(ℓ : k)`, the form the completeness bootstrap
`moduleFinite_of_finite_quotient_span` consumes (over `ZMod ℓ` this was
`ZMod.natCast_self`). -/
lemma natCast_self_eq_zero : ((ℓ : ℕ) : k) = 0 := by
  have hp : (ringChar k).Prime :=
    (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right
      (CharP.char_ne_zero_of_finite k (ringChar k))
  by_cases hne : ringChar k = ℓ
  · rw [← hne]
    exact ringChar.Nat.cast_ringChar
  · exfalso
    have hunit : IsUnit ((ringChar k : ℕ) : ℤ_[ℓ]) :=
      PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
        ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr
          (fun h => hne h.symm)))
    have hzero : algebraMap ℤ_[ℓ] k ((ringChar k : ℕ) : ℤ_[ℓ]) = 0 := by
      rw [map_natCast]
      exact ringChar.Nat.cast_ringChar
    have hu := hunit.map (algebraMap ℤ_[ℓ] k)
    rw [hzero] at hu
    exact not_isUnit_zero hu

variable [TopologicalSpace k] [DiscreteTopology k]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [Module.Finite k V] [Module.Free k V]
  (hdim : Module.rank k V = 2)
set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- Characteristic-polynomial transport through base change and framing:
the family-membership equation `(τ.baseChange B).conj e = σ_φ` identifies
the characteristic polynomials of the family member with the images of
those of `τ` under the coefficient map. (Ingredient of the proof of
`residual_charFrob_eq_of_family`.) -/
lemma charpoly_baseChange_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep ℚ A W) (e : (B ⊗[A] W) ≃ₗ[B] N)
    (g : Field.absoluteGaloisGroup ℚ) :
    (((τ.baseChange B).conj e) g).charpoly =
      ((τ g).charpoly).map (algebraMap A B) := by
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom A B W) (τ g)).charpoly = _
  rw [show (Module.End.baseChangeHom A B W) (τ g) =
    LinearMap.baseChange B (τ g) from rfl, LinearMap.charpoly_baseChange]

/-- A *hardly ramified deformation* of a mod-`ℓ` representation `ρbar`, in
Mazur's category: a coefficient ring `R` — a Noetherian local topological
`ℤ_ℓ`-algebra whose topology is the `𝔪`-adic one (`isAdic`) and which is
`𝔪`-adically complete and separated (`isAdicComplete`) — together with a
hardly ramified framed representation over `R` and a SURJECTIVE reduction
map to the coefficient field `k` matching the characteristic polynomials
of Frobenius of `ρbar` at all good primes.

Unlike `HardlyRamifiedLift`, the ring is *not* required to be a domain,
to be module-finite over `ℤ_ℓ`, or to have characteristic zero: the
universal deformation ring of the hardly ramified problem lives in this
category, and the three sorried strata below
(`exists_universal_hardlyRamifiedDeformation`,
`moduleFinite_of_isUniversal`, `algebraMap_injective_of_isUniversal`) pin
its finer properties down one at a time. The residue field is `k`: `π`
is surjective (`π_surjective` — automatic over `ZMod ℓ`, where the image
is a subring of the prime field, and part of Mazur's category data for
general `k`), so `ker π` is a maximal ideal of the local ring `R`,
necessarily the maximal ideal. -/
structure HardlyRamifiedDeformation (ρbar : GaloisRep ℚ k V) where
  /-- The coefficient ring of the deformation. -/
  R : Type u
  [commRing : CommRing R]
  [topologicalSpace : TopologicalSpace R]
  [isTopologicalRing : IsTopologicalRing R]
  [isLocalRing : IsLocalRing R]
  [algebra : Algebra ℤ_[ℓ] R]
  [isNoetherianRing : IsNoetherianRing R]
  /-- The topology of the coefficient ring is the maximal-adic one. -/
  isAdic : IsAdic (IsLocalRing.maximalIdeal R)
  /-- The coefficient ring is maximal-adically complete and separated. -/
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  /-- The deformation, framed by the standard basis. -/
  ρ : FramedGaloisRep ℚ R (Fin 2)
  /-- The deformation is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ
  /-- The reduction map to the residue characteristic-`ℓ` world. -/
  π : R →+* k
  /-- The reduction map is surjective onto the coefficient field: `k` IS
  the residue field of `R`. Automatic for `k = ZMod ℓ` (the image is a
  subring of the prime field, hence everything —
  `ZMod.ringHom_surjective`); for a general finite `k` it is part of
  Mazur's deformation-category data. -/
  π_surjective : Function.Surjective π
  /-- The deformation reduces to `ρbar`: the characteristic polynomials
  of Frobenius match at every prime `q ∉ {2, ℓ}`. -/
  charFrob_compat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- A hardly ramified deformation `D` of `ρbar` is *universal* if every
hardly ramified deformation `D'` of `ρbar` receives a **unique**
`ℤ_ℓ`-algebra homomorphism `f : D.R → D'.R` compatible with the two
reduction maps and with the characteristic polynomials of Frobenius at
all good primes.

This is Mazur universality expressed through the trace data rather than
through strict equivalence of representations, which keeps the statement
inside the repository's charpoly vocabulary. Both halves of the `∃!` are
load-bearing:

* *Existence* fails for proper quotients of the universal ring (composing
  `R^{univ} ↠ D.R → R^{univ}` would split the quotient, by uniqueness of
  compatible endomorphisms of `R^{univ}` — Carayol: for `ρbar` absolutely
  irreducible the universal ring is topologically generated by traces of
  Frobenii, which the compatibility clause pins).
* *Uniqueness* fails for inflations of the universal ring: `R^{univ}[[t]]`
  (deformation constant in `t`) maps to `R^{univ}[[t]]/(t²)` compatibly
  via both `t ↦ 0` and `t ↦ t̄`, and the square-zero extension
  `R^{univ} ⊕ 𝔽_ℓ ε` maps to itself compatibly via both `ε ↦ ε` and
  `ε ↦ 0`. Without the uniqueness clause the finiteness stratum
  `moduleFinite_of_isUniversal` below would be *false* (`R^{univ}[[t]]`
  would satisfy the mapping property); with it, any two universal data
  are canonically isomorphic, and any universal datum is isomorphic to
  the genuine universal deformation ring.

(For the truth of the strata below it also matters that divisible
square-zero inflations such as `R^{univ} ⊕ ℚ_ℓ ε` are excluded: there
`ε ↦ 0` *is* the unique compatible map to any Noetherian datum, since a
divisible submodule must die in a finite `ℤ_ℓ`-module — but such a ring
is not Noetherian (`ℓ` acts invertibly on the ideal `ℚ_ℓ ε`, so by
Nakayama it is not finitely generated), so the `isNoetherianRing` field
of `HardlyRamifiedDeformation` already rules it out.) -/
def HardlyRamifiedDeformation.IsUniversal {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    ∃! f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- The **existence half** of `IsUniversal`: every hardly ramified
deformation `D'` of `ρbar` receives at least one `ℤ_ℓ`-algebra
homomorphism from `D` compatible with the reduction maps and the
characteristic polynomials of Frobenius. This is what Mazur-style
representability (the framed functor with the hardly ramified conditions
cut in) produces directly; the uniqueness half is supplied separately by
trace generation (`IsTraceGenerated`) through the purely formal Carayol
argument `isUniversal_of_isWeaklyUniversal_isTraceGenerated` below. Weak
universality alone is strictly weaker than `IsUniversal`: the inflation
`R^{univ}[[t]]` (deformation constant in `t`) is weakly universal but
not universal. -/
def HardlyRamifiedDeformation.IsWeaklyUniversal
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    ∃ f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- **Trace generation** (Carayol): the coefficient ring of `D` is
topologically generated, as a `ℤ_ℓ`-algebra, by the coefficients of the
characteristic polynomials of Frobenius at the good primes — the closure
of the subring generated by the image of `ℤ_ℓ` together with all
`charFrob` coefficients is everything. For the genuine universal ring of
an absolutely irreducible `ρbar` this holds by Carayol's theorem (the
universal ring is topologically generated by traces of Frobenii, and the
trace at `Frob_q` is `−(coeff 1)` of the degree-2 `charFrob`); it is
exactly what makes compatible homomorphisms out of `D` unique, turning
weak universality into universality. -/
def HardlyRamifiedDeformation.IsTraceGenerated
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.algebra
  (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n})).topologicalClosure
    = ⊤

/-- The **trace-descent relation** (Carayol): `D'` is a trace-generated
hardly ramified deformation equipped with a ring homomorphism
`ι : D'.R → D.R` compatible with the `ℤ_ℓ`-structure maps, the
reduction maps, and the Frobenius characteristic polynomials —
abstractly, the descended datum over the closed subalgebra of `D.R`
topologically generated by the `charFrob` coefficients, together with
its inclusion. Bundled as a definition (rather than inlined in the
existential of `exists_isTraceGenerated_ringHom`) so that the instance
`letI`s live under plain parameters, following the pattern of
`IsUniversal`/`IsWeaklyUniversal`. -/
def HardlyRamifiedDeformation.IsTraceDescent {ρbar : GaloisRep ℚ k V}
    (D D' : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace
  letI := D.isTopologicalRing; letI := D.isLocalRing; letI := D.algebra
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  D'.IsTraceGenerated ∧
  ∃ ι : D'.R →+* D.R,
    ι.comp (algebraMap ℤ_[ℓ] D'.R) = algebraMap ℤ_[ℓ] D.R ∧
    D.π.comp ι = D'.π ∧
    ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map ι =
        D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- An adically-topologized, adically-separated ring is Hausdorff: `{0}`
is the intersection of the closed (open) subgroups `I ^ k`, hence closed
(PROVEN, elementary; extracted from the proof of
`isModuleTopology_of_isAdic_maximalIdeal` below for reuse in the
uniqueness half of universality). -/
lemma t2Space_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I : Ideal R} (hadic : IsAdic I)
    [IsHausdorff I R] : T2Space R := by
  have hclosed : IsClosed ({(0 : R)} : Set R) := by
    have h0 : ({(0 : R)} : Set R) = ⋂ k : ℕ, ((I ^ k : Ideal R) : Set R) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl k
        exact Submodule.zero_mem _
      · intro hx
        refine IsHausdorff.haus (inferInstance : IsHausdorff I R) x
          fun k => ?_
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        exact hx k
    rw [h0]
    refine isClosed_iInter fun k => ?_
    exact AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (I ^ k))
      ((isAdic_iff.mp hadic).1 k)
  haveI := IsTopologicalAddGroup.t1Space R hclosed
  infer_instance

open Topology in
/-- A **local homomorphism between adically-topologized local rings is
continuous** (PROVEN, elementary): if `f` carries the maximal ideal of
`R` into the maximal ideal of `S`, then `f (𝔪_R ^ k) ⊆ 𝔪_S ^ k` for
every `k`, which is continuity at `0`, hence continuity. (Formal
ingredient of the uniqueness half of `IsUniversal`: homomorphisms
compatible with the reduction maps are automatically local, hence
continuous, so agreement on a topologically generating subring forces
agreement everywhere.) -/
lemma continuous_of_map_maximalIdeal_le {R S : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [CommRing S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (hS : IsAdic (IsLocalRing.maximalIdeal S)) (f : R →+* S)
    (hloc : Ideal.map f (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal S) :
    Continuous f := by
  apply continuous_of_continuousAt_zero f
  unfold ContinuousAt
  rw [map_zero, hS.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  have hmem : ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) ∈
      𝓝 (0 : R) := hR.hasBasis_nhds_zero.mem_of_mem trivial
  filter_upwards [hmem] with x hx
  have hle : Ideal.map f (IsLocalRing.maximalIdeal R ^ k) ≤
      IsLocalRing.maximalIdeal S ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hloc k
  exact hle (Ideal.mem_map_of_mem f hx)

omit [Finite k] [Algebra ℤ_[ℓ] k] [DiscreteTopology k] in
/-- **Uniqueness from trace generation** (the formal Carayol argument,
PROVEN): a weakly universal, trace-generated hardly ramified deformation
is universal. Two compatible homomorphisms `f, f' : D.R → D'.R` agree on
the image of `ℤ_ℓ` (both restrict to the structure map) and on every
Frobenius-charpoly coefficient (both carry the `charFrob` of `D` to that
of `D'`); they are continuous, because compatibility with the reduction
maps makes them local (`ker π` is the maximal ideal on both sides: `π`
is surjective onto the prime field `ℤ/ℓℤ`, so its kernel is maximal) and
local homomorphisms of adic local rings are continuous; and the
equalizer of two continuous ring homomorphisms into a Hausdorff ring
(adic separatedness of `D'.R`) is a closed subring. A closed subring
containing the generating set contains its topological closure, which is
everything by trace generation. -/
theorem isUniversal_of_isWeaklyUniversal_isTraceGenerated
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    D.IsUniversal := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D'
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI := D'.isAdicComplete
  obtain ⟨f, hf⟩ := hw D'
  refine ⟨f, hf, fun f' hf' => ?_⟩
  -- compatible homomorphisms are local, hence continuous
  have hker : RingHom.ker D.π = IsLocalRing.maximalIdeal D.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D.π D.π_surjective)
  have hker' : RingHom.ker D'.π = IsLocalRing.maximalIdeal D'.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D'.π D'.π_surjective)
  have hcont : ∀ g : D.R →+* D'.R, D'.π.comp g = D.π → Continuous g := by
    intro g hg
    refine continuous_of_map_maximalIdeal_le D.isAdic D'.isAdic g ?_
    rw [Ideal.map_le_iff_le_comap, ← hker, ← hker']
    intro x hx
    show D'.π (g x) = 0
    rw [← RingHom.comp_apply, hg]
    exact hx
  -- the equalizer of `f'` and `f` is a closed subring …
  haveI : T2Space D'.R := t2Space_of_isAdic D'.isAdic
  have hclosed : IsClosed ((RingHom.eqLocus f' f : Subring D.R) : Set D.R) :=
    isClosed_eq (hcont f' hf'.2.1) (hcont f hf.2.1)
  -- … containing the trace-generating set
  have hgen : Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
      {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
        x = (D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n}) ≤
      RingHom.eqLocus f' f := by
    rw [Subring.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨q, hq, hq2, hqℓ, n, rfl⟩)
    · show f' (algebraMap ℤ_[ℓ] D.R c) = f (algebraMap ℤ_[ℓ] D.R c)
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, hf'.1, hf.1]
    · show f' ((D.ρ.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff n) =
        f ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff n)
      have hcf := (hf'.2.2 q hq hq2 hqℓ).trans (hf.2.2 q hq hq2 hqℓ).symm
      have hcoeff := congrArg (fun p : Polynomial D'.R => p.coeff n) hcf
      simpa [Polynomial.coeff_map] using hcoeff
  have htop : (⊤ : Subring D.R) ≤ RingHom.eqLocus f' f := by
    have hcl : (Subring.closure (Set.range (algebraMap ℤ_[ℓ] D.R) ∪
        {x : D.R | ∃ q, ∃ hq : q.Prime, q ≠ 2 ∧ q ≠ ℓ ∧ ∃ n : ℕ,
          x = (D.ρ.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff
              n})).topologicalClosure = ⊤ := ht
    rw [← hcl]
    exact Subring.topologicalClosure_minimal _ hgen hclosed
  exact RingHom.ext fun x => htop (Subring.mem_top x)

omit [Finite k] [Algebra ℤ_[ℓ] k] [DiscreteTopology k] in
/-- **Rigidity of universal data** (PROVEN, formal): any two universal
hardly ramified deformations have canonically isomorphic coefficient
rings, compatibly with the `ℤ_ℓ`-algebra structure. The two `∃!`-clauses
produce homomorphisms in both directions whose composites are compatible
endomorphisms, hence equal to the identity (the identity being the
unique compatible endomorphism). This is what lets the finiteness and
presentation strata, stated for an arbitrary universal datum, be
transported from the constructed universal deformation ring. -/
theorem exists_ringEquiv_of_isUniversal {ρbar : GaloisRep ℚ k V}
    (D D' : HardlyRamifiedDeformation hℓOdd ρbar)
    (hD : D.IsUniversal) (hD' : D'.IsUniversal) :
    letI := D.commRing; letI := D'.commRing
    letI := D.algebra; letI := D'.algebra
    ∃ e : D.R ≃+* D'.R, ∀ c : ℤ_[ℓ],
      e (algebraMap ℤ_[ℓ] D.R c) = algebraMap ℤ_[ℓ] D'.R c := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  obtain ⟨f, hf, _⟩ := hD D'
  obtain ⟨g, hg, _⟩ := hD' D
  have hgf : g.comp f = RingHom.id D.R := by
    obtain ⟨i, _, hiu⟩ := hD D
    have h1 : g.comp f = i := by
      refine hiu (g.comp f) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hf.1, hg.1]
      · rw [← RingHom.comp_assoc, hg.2.1, hf.2.1]
      · intro q hq hq2 hqℓ
        rw [← Polynomial.map_map, hf.2.2 q hq hq2 hqℓ,
          hg.2.2 q hq hq2 hqℓ]
    have h2 : RingHom.id D.R = i := by
      refine hiu (RingHom.id D.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro q hq _ _
        exact Polynomial.map_id
    rw [h1, h2]
  have hfg : f.comp g = RingHom.id D'.R := by
    obtain ⟨j, _, hju⟩ := hD' D'
    have h1 : f.comp g = j := by
      refine hju (f.comp g) ⟨?_, ?_, ?_⟩
      · rw [RingHom.comp_assoc, hg.1, hf.1]
      · rw [← RingHom.comp_assoc, hf.2.1, hg.2.1]
      · intro q hq hq2 hqℓ
        rw [← Polynomial.map_map, hg.2.2 q hq hq2 hqℓ,
          hf.2.2 q hq hq2 hqℓ]
    have h2 : RingHom.id D'.R = j := by
      refine hju (RingHom.id D'.R) ⟨?_, ?_, ?_⟩
      · rw [RingHom.id_comp]
      · rw [RingHom.comp_id]
      · intro q hq _ _
        exact Polynomial.map_id
    rw [h1, h2]
  refine ⟨RingEquiv.ofRingHom f g hfg hgf, fun c => ?_⟩
  show f (algebraMap ℤ_[ℓ] D.R c) = algebraMap ℤ_[ℓ] D'.R c
  rw [← RingHom.comp_apply, hf.1]

omit [Finite k] [Algebra ℤ_[ℓ] k] in
/-- **Continuity of the reduction map** (PROVEN, elementary): the
reduction map `π : D'.R → ℤ/ℓℤ` of a hardly ramified deformation is
continuous — its kernel is the maximal ideal (`π` is surjective onto
the prime field), which is open in the maximal-adic topology, so `π`
is locally constant. (Ingredient of the residual-identification
vocabulary below: it makes `ℤ/ℓℤ` a topological `D'.R`-algebra, so the
reduction of `D'.ρ` can be formed by `baseChange`.) -/
lemma HardlyRamifiedDeformation.continuous_pi
    {ρbar : GaloisRep ℚ k V}
    (D' : HardlyRamifiedDeformation hℓOdd ρbar) :
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing
    Continuous D'.π := by
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing
  have hker : RingHom.ker D'.π = IsLocalRing.maximalIdeal D'.R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective D'.π D'.π_surjective)
  have hopen : IsOpen ((RingHom.ker D'.π : Ideal D'.R) : Set D'.R) := by
    rw [hker]
    have h1 := (isAdic_iff.mp D'.isAdic).1 1
    rwa [pow_one] at h1
  apply continuous_of_continuousAt_zero D'.π
  unfold ContinuousAt
  rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
  filter_upwards [hopen.mem_nhds (Submodule.zero_mem _)] with x hx
  exact hx

open scoped TensorProduct in
/-- **Residual identification**: the reduction of `D'.ρ` along the
reduction map `D'.π` — the base change of `D'.ρ` to `ℤ/ℓℤ`, a
continuous `D'.R`-algebra via `continuous_pi` — is conjugate to `ρbar`
itself. This is the datum with which Mazur-style strict-deformation
universality can be applied to `D'`: the `HardlyRamifiedDeformation`
category matches `D'` with `ρbar` only through Frobenius characteristic
polynomials (`charFrob_compat`), and the Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq` upgrades that matching to an actual
conjugation whenever `ρbar` is irreducible. Bundled as a definition so
the instance `letI`s live under plain parameters (elaborator
constraint, cf. `IsTraceDescent`). -/
def HardlyRamifiedDeformation.IsResidualIdentified
    {ρbar : GaloisRep ℚ k V}
    (D' : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI : Algebra D'.R k := D'.π.toAlgebra
  letI : ContinuousSMul D'.R k :=
    continuousSMul_of_algebraMap D'.R k
      (by rw [RingHom.algebraMap_toAlgebra]; exact D'.continuous_pi)
  ∃ e : (k ⊗[D'.R] (Fin 2 → D'.R)) ≃ₗ[k] V,
    (D'.ρ.baseChange k).conj e = ρbar

/-- **Weak universality on residually identified deformations**: `D`
maps compatibly to every deformation `D'` that comes equipped with a
residual identification. This is what Mazur-style strict-deformation
representability produces directly — the classifying map exists for
deformations whose reduction is identified with `ρbar` — without the
Chebotarev–Brauer–Nesbitt input, which is exactly what upgrades this
property to full `IsWeaklyUniversal` in the assembly
`exists_isWeaklyUniversal`. -/
def HardlyRamifiedDeformation.IsWeaklyUniversalOnIdentified
    {ρbar : GaloisRep ℚ k V}
    (D : HardlyRamifiedDeformation hℓOdd ρbar) : Prop :=
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  ∀ D' : HardlyRamifiedDeformation hℓOdd ρbar,
    letI := D'.commRing; letI := D'.topologicalSpace
    letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
    D'.IsResidualIdentified →
    ∃ f : D.R →+* D'.R,
      f.comp (algebraMap ℤ_[ℓ] D.R) = algebraMap ℤ_[ℓ] D'.R ∧
      D'.π.comp f = D.π ∧
      ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map f =
          D'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

/-- **Chebotarev–Brauer–Nesbitt conjugacy leaf** (sorry node — the
identification half of the Mazur representability stratum): a
continuous mod-`ℓ` representation `τ` of `Gal(ℚ̄/ℚ)` on a 2-dimensional
space whose Frobenius characteristic polynomials at all primes
`q ∉ {2, ℓ}` agree with those of an *irreducible* `ρbar` is conjugate
to `ρbar`.

Mathematical content: by Chebotarev density
(`dense_conjClasses_globalFrob`) and continuity into the discrete
endomorphism spaces, the characteristic polynomials of `τ` and `ρbar`
agree on all of the Galois group; by Brauer–Nesbitt the
semisimplifications are then isomorphic; `ρbar` is irreducible and
2-dimensional, so the semisimplification of `τ` is the single
composition factor `ρbar` of full dimension — i.e. `τ` itself is
isomorphic to `ρbar`, and an intertwining isomorphism is the required
conjugation. (The proven machinery of `Chebotarev.lean` — the density
node, the closed-agreement-set argument of
`not_isIrreducible_of_charFrob_eq`, and the 2-dimensional
Brauer–Nesbitt tools of `BrauerNesbitt.lean` — is the intended
toolkit.) -/
theorem exists_conj_of_charFrob_eq
    (hdimV : Module.rank k V = 2)
    {W : Type*} [AddCommGroup W] [Module k W]
    [Module.Finite k W] [Module.Free k W]
    (hdimW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k V} (hirr : ρbar.IsIrreducible)
    (τ : GaloisRep ℚ k W)
    (hcf : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : W ≃ₗ[k] V, τ.conj e = ρbar :=
  sorry

/-- **Strict Mazur representability leaf** (sorry node — the
representability half of the Mazur stratum): the hardly ramified
deformation problem of an irreducible hardly ramified `ρbar` (`ℓ ≥ 5`)
admits a deformation `D` that maps compatibly to every *residually
identified* deformation `D'` — every `D'` equipped with a conjugation
of its reduction onto `ρbar`. The Chebotarev–Brauer–Nesbitt matching is
NOT part of this leaf (it is supplied by `exists_conj_of_charFrob_eq`
through the proven assembly `exists_isWeaklyUniversal`); this leaf is
Mazur/Ramakrishna representability proper.

Mathematical content: `ρbar` is odd (its determinant is the mod-`ℓ`
cyclotomic character, which sends complex conjugation to `−1 ≠ 1` for
odd `ℓ`), and an odd irreducible 2-dimensional representation over
the finite field `k` of characteristic `ℓ` odd is absolutely
irreducible. Hence by Schlessinger's criteria / Mazur's theorem the
framed deformation functor with the hardly ramified local conditions —
cyclotomic determinant, unramified outside `{2, ℓ}`, flat at `ℓ` (a
deformation condition by Ramakrishna), tame quadratic quotient at `2` —
is representable by a complete Noetherian local `ℤ_ℓ`-algebra
`R^{univ}` with residue field `k` (the de Smit–Lenstra
generators-and-relations construction presents `R^{univ}` as
`W(k)[[x₁,…,x_g]]/I`). Given `D'` with a residual
identification, conjugating the framing carries `D'.ρ` to a strict
deformation of `ρbar`, whose classifying map `R^{univ} → D'.R` is the
required compatible homomorphism: compatibility with the reduction
maps is strictness, and compatibility with `charFrob` is
conjugation-invariance of characteristic polynomials.

References: Mazur, *Deforming Galois representations*; Ramakrishna,
*On a variation of Mazur's deformation functor*; de Smit–Lenstra,
*Explicit construction of universal deformation rings* (Prop. 2.3);
Böckle's appendix to Khare's Serre-conjecture notes. -/
theorem exists_isWeaklyUniversalOnIdentified (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsWeaklyUniversalOnIdentified :=
  sorry

open scoped TensorProduct in
/-- **Mazur representability stratum** (DECOMPOSED 2026-07-23 into the
strict Mazur representability leaf
`exists_isWeaklyUniversalOnIdentified` — the classifying maps for
residually identified deformations — and the Chebotarev–Brauer–Nesbitt
conjugacy leaf `exists_conj_of_charFrob_eq` — which produces the
residual identification from the `charFrob_compat` matching; the
assembly below is proven): the hardly ramified deformation problem of
an irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a *weakly
universal* object — a deformation mapping compatibly to every
deformation. Trace generation is NOT part of this node (it is restored
by the Carayol descent stratum
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal`
below).

The proven glue: given any deformation `D'`, its reduction — the base
change of `D'.ρ` along the (continuous, by `continuous_pi`) reduction
map `D'.π` — is a 2-dimensional mod-`ℓ` representation
(`Module.rank_baseChange`) whose Frobenius characteristic polynomials
are the reductions of those of `D'.ρ` (`LinearMap.charpoly_baseChange`)
— i.e., by clause `charFrob_compat`, those of `ρbar`. The
Chebotarev–Brauer–Nesbitt leaf turns this matching into a residual
identification, and the strict leaf's classifying map is the required
compatible homomorphism. -/
theorem exists_isWeaklyUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar, D.IsWeaklyUniversal := by
  obtain ⟨D, hD⟩ :=
    exists_isWeaklyUniversalOnIdentified hℓOdd hdim hℓ5 h hirr
  refine ⟨D, ?_⟩
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  intro D'
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  letI : Algebra D'.R k := D'.π.toAlgebra
  letI : ContinuousSMul D'.R k :=
    continuousSMul_of_algebraMap D'.R k
      (by rw [RingHom.algebraMap_toAlgebra]; exact D'.continuous_pi)
  -- the reduction is 2-dimensional …
  have hrankW :
      Module.rank k (k ⊗[D'.R] (Fin 2 → D'.R)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  -- … and its Frobenius characteristic polynomials are those of `ρbar`
  have hcf : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (D'.ρ.baseChange k).charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hq2 hqℓ
    have hcp : ((D'.ρ.baseChange k)
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
        ((D'.ρ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly).map
          (algebraMap D'.R k) := by
      show ((Module.End.baseChangeHom D'.R k (Fin 2 → D'.R))
        (D'.ρ (globalFrob
          hq.toHeightOneSpectrumRingOfIntegersRat))).charpoly = _
      rw [show (Module.End.baseChangeHom D'.R k (Fin 2 → D'.R))
          (D'.ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) =
        LinearMap.baseChange k
          (D'.ρ (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat))
        from rfl, LinearMap.charpoly_baseChange]
    have hred := D'.charFrob_compat q hq hq2 hqℓ
    show ((D'.ρ.baseChange k)
      (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly = _
    rw [hcp, RingHom.algebraMap_toAlgebra]
    exact hred
  obtain ⟨e, he⟩ := exists_conj_of_charFrob_eq hdim hrankW hirr
    (D'.ρ.baseChange k) hcf
  exact hD D' ⟨e, he⟩

/-- **Carayol subring-descent leaf** (sorry node — the genuine content
of the trace-descent stratum): every hardly ramified deformation `D` of
an irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a
*trace-generated* deformation `D'` mapping compatibly INTO it. Weak
universality plays no role in this leaf: it is restored formally by the
composition glue in
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` below.

Mathematical content (Carayol's descent): let `R' ⊆ D.R` be the closed
`ℤ_ℓ`-subalgebra topologically generated by the coefficients of the
Frobenius characteristic polynomials of `D.ρ`. Since `ρbar` is
absolutely irreducible (odd irreducible 2-dimensional over the finite
field `k` of characteristic `ℓ`, `ℓ`
odd) and by Chebotarev the traces of the whole representation are
limits of traces of Frobenii, Carayol's lemma conjugates `D.ρ` into
`GL₂(R')`. The descended datum `D'` over `R'` inherits the structure
(a closed subring of a complete Noetherian local ring with the same
finite residue field is complete Noetherian local with the subspace
topology — the maximal-adic one) and the hardly ramified conditions
(along the conjugation and the inclusion), is trace-generated by
construction (its `charFrob` map to those of `D.ρ` under the inclusion
`ι`, and their coefficients topologically generate `R'`), and `ι` is
compatible with the `ℤ_ℓ`-structure maps, the reduction maps, and the
`charFrob` data — the three clauses of the conclusion.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Théorème 1 and Lemme 1);
Mazur, *Deforming Galois representations*, §1.8. -/
theorem exists_isTraceGenerated_ringHom (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) :
    ∃ D' : HardlyRamifiedDeformation hℓOdd ρbar, D.IsTraceDescent hℓOdd D' :=
  sorry

/-- **Carayol trace-descent stratum** (DECOMPOSED 2026-07-23 into the
Carayol subring-descent leaf `exists_isTraceGenerated_ringHom` above —
which produces the descended trace-generated datum `D'` *together with*
a compatible ring homomorphism `ι : D'.R → D.R` (the subring
inclusion), and does not mention weak universality at all — plus the
PROVEN composition glue below): a weakly universal hardly ramified
deformation can be replaced by one that is *also* trace-generated.

The glue: `D'` is weakly universal because any deformation `D''`
receives `f : D.R → D''.R` from weak universality of `D`, and
`f ∘ ι` is compatible since every piece of compatibility data — the
`ℤ_ℓ`-structure map, the reduction map, the `charFrob` coefficients —
composes.

References: Carayol, *Formes modulaires et représentations galoisiennes
à valeurs dans un anneau local complet* (Théorème 1 and Lemme 1);
Mazur, *Deforming Galois representations*, §1.8. -/
theorem exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hw : D.IsWeaklyUniversal) :
    ∃ D' : HardlyRamifiedDeformation hℓOdd ρbar,
      D'.IsWeaklyUniversal ∧ D'.IsTraceGenerated := by
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra
  obtain ⟨D', hdesc⟩ :=
    exists_isTraceGenerated_ringHom hℓOdd hdim hℓ5 h hirr D
  obtain ⟨ht', ι, hι1, hι2, hι3⟩ := (hdesc : _ ∧ _)
  refine ⟨D', ?_, ht'⟩
  letI := D'.commRing; letI := D'.topologicalSpace
  letI := D'.isTopologicalRing; letI := D'.isLocalRing; letI := D'.algebra
  intro D''
  letI := D''.commRing; letI := D''.topologicalSpace
  letI := D''.isTopologicalRing; letI := D''.isLocalRing; letI := D''.algebra
  obtain ⟨f, hf1, hf2, hf3⟩ := hw D''
  refine ⟨f.comp ι, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hι1, hf1]
  · rw [← RingHom.comp_assoc, hf2, hι2]
  · intro q hq hq2 hqℓ
    rw [← Polynomial.map_map, hι3 q hq hq2 hqℓ, hf3 q hq hq2 hqℓ]

/-- **Representability leaf** (DECOMPOSED 2026-07-23 into the Mazur
representability leaf `exists_isWeaklyUniversal` — the existence of
compatible maps — and the Carayol trace-descent leaf
`exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal` — the
replacement of a weakly universal datum by a trace-generated one; the
assembly below is proven): the hardly ramified deformation problem of an
irreducible hardly ramified `ρbar` (`ℓ ≥ 5`) admits a weakly universal,
trace-generated object. The uniqueness half of universality is NOT part
of this node: it is derived formally in
`isUniversal_of_isWeaklyUniversal_isTraceGenerated`. -/
theorem exists_isWeaklyUniversal_isTraceGenerated (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar,
      D.IsWeaklyUniversal ∧ D.IsTraceGenerated := by
  obtain ⟨D, hw⟩ := exists_isWeaklyUniversal hℓOdd hdim hℓ5 h hirr
  exact exists_isWeaklyUniversal_isTraceGenerated_of_isWeaklyUniversal hℓOdd
    hdim hℓ5 h hirr D hw

/-- **Representability stratum** (DECOMPOSED 2026-07-22 into the
arithmetic leaf `exists_isWeaklyUniversal_isTraceGenerated` — Mazur
representability producing the maps, Carayol trace generation — plus the
PROVEN formal uniqueness argument
`isUniversal_of_isWeaklyUniversal_isTraceGenerated`): the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
(`ℓ ≥ 5`) admits a universal object.

The assembly below is proven: the leaf produces a weakly universal,
trace-generated deformation, and the formal Carayol argument upgrades it
to a universal one. -/
theorem exists_universal_hardlyRamifiedDeformation (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ D : HardlyRamifiedDeformation hℓOdd ρbar, D.IsUniversal := by
  obtain ⟨D, hw, ht⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  exact ⟨D, isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D hw ht⟩

/-- **Mod-`ℓ` finiteness leaf** (sorry node — the arithmetic core of
the finiteness stratum, restated modulo `ℓ`): the weakly universal,
trace-generated hardly ramified deformation ring — i.e. the genuine
universal ring, as constructed by
`exists_isWeaklyUniversal_isTraceGenerated` — is *finite modulo `ℓ`*:
`D.R ⧸ (ℓ)` is a finite ring.

This is the potential-modularity / Taylor–Wiles–Kisin input of
Khare–Wintenberger — the single genuinely deep arithmetic node of the
lifting core, not decomposed further here: no principled intermediate
statement exists in the repository's current vocabulary (stating
"`R = T`" needs Hecke algebras; stating potential modularity needs
Hilbert modular forms over totally real fields). The
residual-modularity hypothesis is bypassed via potential modularity
(Taylor's Moret-Bailly argument), which after a solvable base change
`F/ℚ` (totally real, in which the deformation problem's conditions
remain balanced) proves an `R = T` theorem by the Taylor–Wiles–Kisin
patching method; `T` is a finite `ℤ_ℓ`-algebra, so `T/ℓT` — and with
it the mod-`ℓ` fibre of the `ℚ`-level ring, by Khare–Wintenberger's
descent — is finite. The mod-`ℓ` form is chosen over
`Module.Finite ℤ_[ℓ] D.R` because it is what the patching literature
produces directly (the "`R/λ` is Artinian" form of finiteness, cf. the
Böckle presentation stratum); the lift back to `ℤ_ℓ`-module finiteness
is the pure commutative-algebra completeness bootstrap
`moduleFinite_of_finite_quotient_span` below. The hypotheses
characterize `D` up to canonical isomorphism (weak universality +
trace generation = universality, by
`isUniversal_of_isWeaklyUniversal_isTraceGenerated` and the rigidity
theorem `exists_ringEquiv_of_isUniversal`), so a future proof may
construct its own universal datum, prove ITS mod-`ℓ` fibre finite, and
transport the result along the canonical isomorphism.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4, and *(II)*; Taylor, *Remarks on a conjecture of
Fontaine and Mazur* and *On the meromorphic continuation of degree two
L-functions*; Kisin, *Moduli of finite flat group schemes, and
modularity*; Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing
    Finite (D.R ⧸ Ideal.span {(ℓ : D.R)}) :=
  sorry

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- **Completeness bootstrap** (PROVEN 2026-07-23, pure commutative
algebra — no arithmetic content): a Noetherian local `ℤ_ℓ`-algebra `R`,
separated for its maximal-adic topology, with residue field `k` (it
maps ONTO the finite field `k`, of characteristic `ℓ` by
`natCast_self_eq_zero`) and finite modulo `ℓ`, is finite as a
`ℤ_ℓ`-module.

Proof (standard: Mazur, *Deforming Galois representations*, §1.1;
Matsumura, Thm. 8.4): `ℓ` lies in the maximal ideal (it dies under the
reduction map, whose kernel is the maximal ideal of the local ring, `π`
being surjective onto `k`), so `ℓ^t R ⊆ 𝔪^t`.
Choose representatives `x₁, …, x_s ∈ R` of the finitely many classes of
`R/(ℓ)`; every `r ∈ R` unwinds as `r = Σ_j ℓ^j a_j` with each `a_j`
among the `xᵢ`, the coordinatewise partial sums of the resulting
`ℤ_ℓ`-coefficients converge in the complete `ℤ_ℓ` (`IsPrecomplete`,
purely algebraically), and adic separatedness identifies `r` with the
limit combination — so the `xᵢ` generate `R` as a `ℤ_ℓ`-module.

(The `IsNoetherianRing` hypothesis is DELIBERATELY retained although
this proof does not consume it: it keeps the statement aligned with the
literature form of the bootstrap, and its sole use site — the
finiteness-stratum assembly `moduleFinite_of_isWeaklyUniversal_...`
below — discharges it with the `isNoetherianRing` field of
`HardlyRamifiedDeformation`, which keeps that structure field inside
the root theorem's dependency cone. Do not remove it.) -/
theorem moduleFinite_of_finite_quotient_span {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsHausdorff (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π)
    (hfin : Finite (R ⧸ Ideal.span {(ℓ : R)})) :
    Module.Finite ℤ_[ℓ] R := by
  classical
  -- `ℓ` lies in the maximal ideal: it dies under the reduction map (the
  -- target `k` has characteristic `ℓ`), whose kernel is the maximal ideal
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hℓm : (ℓ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hker, RingHom.mem_ker, map_natCast]
    exact natCast_self_eq_zero
  haveI := hfin
  haveI : Fintype (R ⧸ Ideal.span {(ℓ : R)}) := Fintype.ofFinite _
  -- a set-theoretic section of the reduction onto the finite quotient
  let s : (R ⧸ Ideal.span {(ℓ : R)}) → R :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hs : ∀ q, Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (s q) = q :=
    fun q => Function.surjInv_eq Ideal.Quotient.mk_surjective q
  -- division step: subtracting the representative of the class leaves a
  -- multiple of `ℓ`
  have hstep : ∀ x : R, ∃ c : R,
      x - s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) x) = (ℓ : R) * c := by
    intro x
    have hx : x - s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) x) ∈
        Ideal.span {(ℓ : R)} := by
      rw [← Ideal.Quotient.eq]
      exact (hs _).symm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose step hstepEq using hstep
  -- the `ℤ_ℓ`-span of the representatives is everything: unwind an
  -- arbitrary element into `ℓ`-adic digits, converge the coefficients in
  -- the complete `ℤ_ℓ`, and identify by adic separatedness
  have hspan : Submodule.span ℤ_[ℓ] (Set.range s) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro r
    -- remainders of the iterated division
    let rem : ℕ → R := fun t =>
      Nat.rec (motive := fun _ => R) r (fun _ prev => step prev) t
    have hremS : ∀ t, rem (t + 1) = step (rem t) := fun _ => rfl
    -- partial coefficient sums, one per representative
    set c : ℕ → (R ⧸ Ideal.span {(ℓ : R)}) → ℤ_[ℓ] := fun t q =>
      ∑ j ∈ Finset.range t,
        if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
        then (ℓ : ℤ_[ℓ]) ^ j else 0 with hcdef
    -- the partial sums are Cauchy for the `ℓ`-adic filtration of `ℤ_ℓ`
    have hcauchy : ∀ q, ∀ {a b : ℕ}, a ≤ b →
        c a q ≡ c b q [SMOD
          (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ a • ⊤ :
            Submodule ℤ_[ℓ] ℤ_[ℓ])] := by
      intro q a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have hsplit : c b q - c a q = ∑ j ∈ Finset.Ico a b,
          (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
           then (ℓ : ℤ_[ℓ]) ^ j else 0) := by
        simp only [hcdef]
        rw [← Finset.sum_range_add_sum_Ico _ hab]
        ring
      have hmem : ∑ j ∈ Finset.Ico a b,
          (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
           then (ℓ : ℤ_[ℓ]) ^ j else 0) ∈
          (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ a : Ideal ℤ_[ℓ]) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
        split_ifs
        · exact Ideal.mem_span_singleton.mpr (pow_dvd_pow _ hj.1)
        · exact Submodule.zero_mem _
      have hflip : c a q - c b q = -(c b q - c a q) := by ring
      rw [hflip, hsplit]
      exact neg_mem hmem
    -- converge the coefficients in the complete `ℤ_ℓ`
    have hex : ∀ q, ∃ Lq : ℤ_[ℓ], ∀ t, c t q ≡ Lq [SMOD
        (IsLocalRing.maximalIdeal ℤ_[ℓ] ^ t • ⊤ :
          Submodule ℤ_[ℓ] ℤ_[ℓ])] :=
      fun q => IsPrecomplete.prec inferInstance
        (fun {a b} hab => hcauchy q hab)
    choose L hL using hex
    -- the finite-stage identity: `r` is the digit combination plus an
    -- `ℓ^t`-divisible remainder
    have hA : ∀ t, r = (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
        s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
        (ℓ : R) ^ t * rem t := by
      intro t
      induction t with
      | zero =>
        rw [Finset.sum_range_zero, pow_zero, one_mul, zero_add]
        rfl
      | succ t ih =>
        have hdiv : rem t =
            s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem t)) +
              (ℓ : R) * rem (t + 1) := by
          have h1 := hstepEq (rem t)
          rw [← hremS t] at h1
          rw [← h1]
          ring
        calc r = (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
              (ℓ : R) ^ t * rem t := ih
          _ = (∑ j ∈ Finset.range (t + 1), (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) +
              (ℓ : R) ^ (t + 1) * rem (t + 1) := by
            conv_lhs => rw [hdiv]
            rw [Finset.sum_range_succ]
            ring
    -- regroup the digit combination by representative
    have hB : ∀ t, (∑ j ∈ Finset.range t, (ℓ : R) ^ j *
        s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j))) =
        ∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q := by
      intro t
      have hterm : ∀ q, algebraMap ℤ_[ℓ] R (c t q) * s q =
          ∑ j ∈ Finset.range t,
            (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
             then (ℓ : R) ^ j * s q else 0) := by
        intro q
        simp only [hcdef]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · rw [map_pow, map_natCast]
        · rw [map_zero, zero_mul]
      refine Eq.symm ?_
      calc ∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q
          = ∑ q, ∑ j ∈ Finset.range t,
              (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
               then (ℓ : R) ^ j * s q else 0) :=
            Finset.sum_congr rfl fun q _ => hterm q
        _ = ∑ j ∈ Finset.range t, ∑ q,
              (if Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j) = q
               then (ℓ : R) ^ j * s q else 0) :=
            Finset.sum_comm
        _ = ∑ j ∈ Finset.range t, (ℓ : R) ^ j *
              s (Ideal.Quotient.mk (Ideal.span {(ℓ : R)}) (rem j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_ite_eq]
            simp
    -- the limit combination differs from `r` by an element of every power
    -- of the maximal ideal …
    have hsmul : ∑ q, L q • s q = ∑ q, algebraMap ℤ_[ℓ] R (L q) * s q :=
      Finset.sum_congr rfl fun q _ => Algebra.smul_def _ _
    have hmemt : ∀ t : ℕ, r - ∑ q, L q • s q ∈
        (IsLocalRing.maximalIdeal R ^ t : Ideal R) := by
      intro t
      have hsub : r - ∑ q, L q • s q =
          (ℓ : R) ^ t * rem t +
          ∑ q, algebraMap ℤ_[ℓ] R (c t q - L q) * s q := by
        calc r - ∑ q, L q • s q
            = ((∑ q, algebraMap ℤ_[ℓ] R (c t q) * s q) +
                (ℓ : R) ^ t * rem t) -
                ∑ q, algebraMap ℤ_[ℓ] R (L q) * s q := by
              rw [← hB t, ← hA t, hsmul]
          _ = (ℓ : R) ^ t * rem t +
              ∑ q, (algebraMap ℤ_[ℓ] R (c t q) * s q -
                algebraMap ℤ_[ℓ] R (L q) * s q) := by
              rw [Finset.sum_sub_distrib]
              ring
          _ = (ℓ : R) ^ t * rem t +
              ∑ q, algebraMap ℤ_[ℓ] R (c t q - L q) * s q := by
              refine congrArg (fun z => (ℓ : R) ^ t * rem t + z) ?_
              exact Finset.sum_congr rfl fun q _ => by
                rw [map_sub, sub_mul]
      rw [hsub]
      refine Submodule.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hℓm t)
      · refine Submodule.sum_mem _ fun q _ => ?_
        have hLqt := hL q t
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
          PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] at hLqt
        obtain ⟨d, hd⟩ := hLqt
        rw [hd, map_mul, map_pow, map_natCast, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hℓm t)
    -- … hence vanishes by adic separatedness
    have hzero : r - ∑ q, L q • s q = 0 := by
      refine IsHausdorff.haus (inferInstance :
        IsHausdorff (IsLocalRing.maximalIdeal R) R) _ fun t => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact hmemt t
    rw [sub_eq_zero.mp hzero]
    exact Submodule.sum_mem _ fun q _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  -- conclude module finiteness from the finite generating set
  exact Module.finite_def.mpr
    ⟨(Set.finite_range s).toFinset, by
      rw [Set.Finite.coe_toFinset]; exact hspan⟩

/-- **Finiteness leaf** (DECOMPOSED 2026-07-23 into the mod-`ℓ`
finiteness leaf `finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated`
— the potential-modularity / Taylor–Wiles–Kisin content, producing
finiteness of `D.R ⧸ (ℓ)` — plus the pure commutative-algebra
completeness bootstrap `moduleFinite_of_finite_quotient_span`; the
assembly below is proven): the weakly universal, trace-generated hardly
ramified deformation ring is finite as a `ℤ_ℓ`-module. -/
theorem moduleFinite_of_isWeaklyUniversal_isTraceGenerated (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    Module.Finite ℤ_[ℓ] D.R := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  haveI := D.isNoetherianRing
  haveI : IsHausdorff (IsLocalRing.maximalIdeal D.R) D.R :=
    (D.isAdicComplete).toIsHausdorff
  have hfin : Finite (D.R ⧸ Ideal.span {(ℓ : D.R)}) :=
    finite_quotient_span_of_isWeaklyUniversal_isTraceGenerated hℓOdd hdim
      hℓ5 h hirr D hw ht
  exact moduleFinite_of_finite_quotient_span D.π D.π_surjective hfin

/-- **Finiteness stratum** (DECOMPOSED 2026-07-22 into the arithmetic
leaf `moduleFinite_of_isWeaklyUniversal_isTraceGenerated` — potential
modularity / Taylor–Wiles–Kisin — plus PROVEN formal transport): the
universal hardly ramified deformation ring is finite as a `ℤ_ℓ`-module.
The assembly below is proven: any universal `D` is canonically
isomorphic, as a `ℤ_ℓ`-algebra, to the trace-generated weakly universal
datum produced by the representability leaf
(`exists_ringEquiv_of_isUniversal`), whose finiteness is the leaf; the
isomorphism upgrades to a `ℤ_ℓ`-linear equivalence and finiteness
transfers along it. -/
theorem moduleFinite_of_isUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hD : D.IsUniversal) :
    letI := D.commRing; letI := D.algebra
    Module.Finite ℤ_[ℓ] D.R := by
  letI := D.commRing; letI := D.algebra
  obtain ⟨D₀, hw₀, ht₀⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  letI := D₀.commRing; letI := D₀.algebra
  have hD₀ : D₀.IsUniversal :=
    isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D₀ hw₀ ht₀
  obtain ⟨e, he⟩ := exists_ringEquiv_of_isUniversal hℓOdd D₀ D hD₀ hD
  have hfin₀ : Module.Finite ℤ_[ℓ] D₀.R :=
    moduleFinite_of_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
      D₀ hw₀ ht₀
  letI := hfin₀
  let elin : D₀.R ≃ₗ[ℤ_[ℓ]] D.R :=
    { e.toAddEquiv with
      map_smul' := fun c x => by
        show e (c • x) = c • e x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, he c] }
  exact Module.Finite.equiv elin

/-- **Minimal-presentation leaf** (sorry node, pure commutative algebra
— no arithmetic content; the structure-theoretic half of the
presentation stratum): every Noetherian local `ℤ_ℓ`-algebra which is
maximal-adically complete and separated and has finite residue field
`k` (it maps ONTO `k`) admits a *minimal* presentation by a power
series ring over a coefficient ring `Λ`: a compatible surjection
`φ : Λ[[x₁,…,x_g]] ↠ R` whose kernel lies in `𝔪² + (ℓ)` — i.e. `φ`
induces an isomorphism of mod-`ℓ` cotangent spaces
`𝔪_S/(𝔪_S² + ℓ) ≅ 𝔪_R/(𝔪_R² + ℓ)`, so `g` is the mod-`ℓ` cotangent
dimension of `R`.

The coefficient ring `Λ` is classically the Witt vectors `W(k)` — for
`k = ZMod ℓ` just `ℤ_ℓ` itself — and the clauses pin it up to
isomorphism: a local domain, Noetherian, module-finite over `ℤ_ℓ`
(hence complete), with maximal ideal `(ℓ)` (unramified over `ℤ_ℓ`); its
residue field is then forced to be `k` by the surjection `φ` onto the
local ring `R` with residue field `k`. (`k`-GENERALIZATION NOTE,
2026-07-24: over `ZMod ℓ` this leaf fixed `Λ = ℤ_ℓ`; the abstract `Λ`
is the correct base for a general finite residue field, since a
quotient of `ℤ_ℓ[[x₁,…,x_g]]` has residue field `𝔽_ℓ`.)

Proof sketch (de Smit–Lenstra, *Explicit construction of universal
deformation rings*, Prop. 2.3; Matsumura §29): take `Λ = W(k)` (a
complete unramified DVR with residue field `k`, free of rank `[k:𝔽_ℓ]`
over `ℤ_ℓ`); `R` is a `Λ`-algebra by formal étaleness of `W(k)/ℤ_ℓ`;
`𝔪_R/(𝔪_R² + ℓR)` is a finite-dimensional `k`-vector space
(Noetherianness); send `xᵢ` to lifts `tᵢ ∈ 𝔪_R` of a basis — the
substitution `xᵢ ↦ tᵢ` converges on all of `Λ[[x₁,…,x_g]]` because the
`tᵢ` are topologically nilpotent and `R` is complete; the image is a
closed subring containing `Λ + 𝔪_R`-generators, hence everything
(completeness again: `𝔪_S`-adic density plus closedness); the kernel
bound restates the choice of a *basis* (not merely a spanning set). -/
theorem exists_minimal_mvPowerSeries_presentation {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra ℤ_[ℓ] R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (π : R →+* k) (hπsurj : Function.Surjective π) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} ∧
      ∃ (g : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* R),
        Function.Surjective φ ∧
        φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
          algebraMap ℤ_[ℓ] R ∧
        RingHom.ker φ ≤
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
            Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} :=
  sorry

/-- **Böckle relation-bound leaf** (sorry node — the arithmetic core of
the presentation stratum): for EVERY minimal presentation
`φ : Λ[[x₁,…,x_g]] ↠ D.R` of the weakly universal, trace-generated
hardly ramified deformation ring, over ANY unramified coefficient ring
`Λ` (the clauses — local Noetherian domain, module-finite over `ℤ_ℓ`,
maximal ideal `(ℓ)` — pin `Λ ≅ W(k)`: the surjection `φ` onto the local
ring `D.R` with residue field `k` forces the residue field of `Λ`;
minimal: `ker φ ⊆ 𝔪² + (ℓ)`, so that `g` is the mod-`ℓ` tangent
dimension `dim H¹_{HR}(G_{ℚ,S}, ad ρbar)` of the deformation functor),
the kernel is generated by *strictly fewer than `g`* power series.

Mathematical content (Böckle; Khare–Wintenberger §4): obstruction
theory embeds the dual of the minimal relation space
`ker φ/(𝔪_S · ker φ)` into `H²_{HR}(G_{ℚ,S}, ad ρbar)`, so `ker φ` is
generated by `r ≤ dim H²` elements (Nakayama picks the generators); the
global Euler characteristic formula and Poitou–Tate duality, with the
balanced local conditions at `ℓ` (flat), `2` (tame quadratic) and `∞`
(`ρbar` is odd, so `dim H⁰(ℝ, ad) = 2`), give
`dim H¹ − dim H² ≥ 1`, i.e. `r < g`. The kernel is stated as the
*span* of the `fᵢ` (not its closure): finitely generated ideals of the
Noetherian complete local ring `Λ[[x₁,…,x_g]]` are closed. As with
the finiteness leaf, the hypotheses pin `D` down up to canonical
isomorphism, so a future proof may construct its own universal datum
and transport along `exists_ringEquiv_of_isUniversal` (minimality of a
presentation is preserved by composition with a `ℤ_ℓ`-algebra
isomorphism).

References: Böckle, *Presentations of universal deformation rings*
(and his appendix to Khare's Serre-conjecture notes);
Khare–Wintenberger, *Serre's modularity conjecture (I)*, §4;
Mazur, *Deforming Galois representations*, §1.6–1.7. -/
theorem exists_relations_lt_of_minimal_mvPowerSeries_presentation
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    ∀ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ),
      IsLocalRing.maximalIdeal Λ = Ideal.span {(ℓ : Λ)} →
      ∀ (g : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* D.R),
        Function.Surjective φ →
        φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
          algebraMap ℤ_[ℓ] D.R →
        RingHom.ker φ ≤
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ^ 2 ⊔
            Ideal.span {(ℓ : MvPowerSeries (Fin g) Λ)} →
        ∃ (r : ℕ) (f : Fin r → MvPowerSeries (Fin g) Λ),
          r < g ∧ RingHom.ker φ = Ideal.span (Set.range f) :=
  sorry

/-- **Böckle presentation leaf** (DECOMPOSED 2026-07-23 into the
minimal-presentation leaf `exists_minimal_mvPowerSeries_presentation` —
pure commutative algebra: every complete Noetherian local `ℤ_ℓ`-algebra
with finite residue field `k` is minimally presented by a power series
ring over the unramified coefficient ring `Λ ≅ W(k)` — and the Böckle
relation-bound leaf
`exists_relations_lt_of_minimal_mvPowerSeries_presentation` — the
Galois-cohomological count `r < g` for minimal presentations; the
assembly below is proven): the weakly universal, trace-generated hardly
ramified deformation ring admits a presentation
`D.R ≅ Λ[[x₁,…,x_g]]/(f₁,…,f_r)` with strictly fewer relations than
generators, `r < g`, compatibly with the `ℤ_ℓ`-structures, over a local
Noetherian domain `Λ` module-finite over `ℤ_ℓ`. -/
theorem exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.algebra
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsLocalRing Λ)
      (_ : IsNoetherianRing Λ) (_ : Algebra ℤ_[ℓ] Λ)
      (_ : Module.Finite ℤ_[ℓ] Λ)
      (g r : ℕ) (φ : MvPowerSeries (Fin g) Λ →+* D.R)
      (f : Fin r → MvPowerSeries (Fin g) Λ),
      r < g ∧ Function.Surjective φ ∧
      φ.comp (algebraMap ℤ_[ℓ] (MvPowerSeries (Fin g) Λ)) =
        algebraMap ℤ_[ℓ] D.R ∧
      RingHom.ker φ = Ideal.span (Set.range f) := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  haveI := D.isNoetherianRing
  haveI := D.isAdicComplete
  obtain ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, hΛℓ, g, φ, hφs, hφc, hφmin⟩ :=
    exists_minimal_mvPowerSeries_presentation (ℓ := ℓ) D.π D.π_surjective
  obtain ⟨r, f, hrg, hker⟩ :=
    exists_relations_lt_of_minimal_mvPowerSeries_presentation hℓOdd hdim hℓ5
      h hirr D hw ht Λ iΛ1 iΛ2 iΛ3 iΛ4 iΛ5 iΛ6 hΛℓ g φ hφs hφc hφmin
  exact ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, g, r, φ, f, hrg, hφs, hφc, hker⟩

/-- Auxiliary for the variable-splitting isomorphism: `Finsupp.tail` is
additive. -/
lemma finsupp_tail_add {n : ℕ} (p q : Fin (n + 1) →₀ ℕ) :
    Finsupp.tail (p + q) = Finsupp.tail p + Finsupp.tail q :=
  Finsupp.ext fun i => by simp [Finsupp.tail_apply]

/-- Auxiliary for the variable-splitting isomorphism: `Finsupp.cons` is
additive. -/
lemma finsupp_cons_add_cons {n : ℕ} (a b : ℕ) (s t : Fin n →₀ ℕ) :
    Finsupp.cons a s + Finsupp.cons b t = Finsupp.cons (a + b) (s + t) :=
  Finsupp.ext fun i => by
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp

/-- Auxiliary for the variable-splitting isomorphism: a sum over the
antidiagonal of `Finsupp.cons k m` is an iterated sum over the
antidiagonals of `k` and of `m` — the monomial-splitting rearrangement
underlying the Cauchy-product compatibility. -/
lemma sum_antidiagonal_cons {S : Type*} [AddCommMonoid S] {n : ℕ} (k : ℕ)
    (m : Fin n →₀ ℕ)
    (F : (Fin (n + 1) →₀ ℕ) × (Fin (n + 1) →₀ ℕ) → S) :
    ∑ p ∈ Finset.antidiagonal (Finsupp.cons k m), F p =
      ∑ ij ∈ Finset.antidiagonal k, ∑ ab ∈ Finset.antidiagonal m,
        F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2) := by
  calc ∑ p ∈ Finset.antidiagonal (Finsupp.cons k m), F p
      = ∑ x ∈ Finset.antidiagonal k ×ˢ Finset.antidiagonal m,
          F (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2) := ?_
    _ = ∑ ij ∈ Finset.antidiagonal k, ∑ ab ∈ Finset.antidiagonal m,
          F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2) :=
        Finset.sum_product' (Finset.antidiagonal k) (Finset.antidiagonal m)
          (fun ij ab => F (Finsupp.cons ij.1 ab.1, Finsupp.cons ij.2 ab.2))
  refine Finset.sum_nbij'
    (i := fun p => ((p.1 0, p.2 0), (Finsupp.tail p.1, Finsupp.tail p.2)))
    (j := fun x => (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hp
    rw [Finset.mem_antidiagonal] at hp
    rw [Finset.mem_product, Finset.mem_antidiagonal, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have h0 := DFunLike.congr_fun hp 0
      simpa using h0
    · rw [← finsupp_tail_add, hp, Finsupp.tail_cons]
  · rintro ⟨⟨i, j⟩, a, b⟩ hx
    rw [Finset.mem_product, Finset.mem_antidiagonal,
      Finset.mem_antidiagonal] at hx
    rw [Finset.mem_antidiagonal]
    show Finsupp.cons i a + Finsupp.cons j b = Finsupp.cons k m
    rw [finsupp_cons_add_cons, hx.1, hx.2]
  · rintro ⟨p, q⟩ -
    simp
  · rintro ⟨⟨i, j⟩, a, b⟩ -
    simp
  · rintro ⟨p, q⟩ -
    simp

/-- Auxiliary for the variable-splitting isomorphism: the splitting map
itself, carrying `f ∈ R[[x₀,…,x_n]]` to the single-variable power series
in `x₀` whose `k`-th coefficient is the `n`-variable series of
`x₀`-degree-`k` coefficients of `f`. -/
noncomputable def mvPowerSeriesSplit {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) :
    PowerSeries (MvPowerSeries (Fin n) R) :=
  PowerSeries.mk fun k =>
    (fun m => MvPowerSeries.coeff (Finsupp.cons k m) f :
      MvPowerSeries (Fin n) R)

/-- Auxiliary: coefficient formula for `mvPowerSeriesSplit`. -/
lemma coeff_coeff_mvPowerSeriesSplit {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) (k : ℕ) (m : Fin n →₀ ℕ) :
    MvPowerSeries.coeff m (PowerSeries.coeff k (mvPowerSeriesSplit n f)) =
      MvPowerSeries.coeff (Finsupp.cons k m) f := by
  rw [mvPowerSeriesSplit, PowerSeries.coeff_mk]
  rfl

/-- Auxiliary for the variable-splitting isomorphism: the merging map,
inverse to `mvPowerSeriesSplit`. -/
noncomputable def mvPowerSeriesUnsplit {R : Type*} [CommRing R] (n : ℕ)
    (G : PowerSeries (MvPowerSeries (Fin n) R)) :
    MvPowerSeries (Fin (n + 1)) R :=
  (fun p => MvPowerSeries.coeff (Finsupp.tail p)
      (PowerSeries.coeff (p 0) G) :
    MvPowerSeries (Fin (n + 1)) R)

/-- Auxiliary: coefficient formula for `mvPowerSeriesUnsplit`. -/
lemma coeff_mvPowerSeriesUnsplit {R : Type*} [CommRing R] (n : ℕ)
    (G : PowerSeries (MvPowerSeries (Fin n) R)) (p : Fin (n + 1) →₀ ℕ) :
    MvPowerSeries.coeff p (mvPowerSeriesUnsplit n G) =
      MvPowerSeries.coeff (Finsupp.tail p) (PowerSeries.coeff (p 0) G) :=
  rfl

/-- **Variable-splitting isomorphism for power series** (PROVEN
2026-07-23, pure commutative algebra — the missing mathlib bridge
between multivariate power series in `n + 1` variables and
single-variable power series over multivariate power series in `n`
variables): separating one variable. Proven by reindexing coefficients
along `Finsupp.cons`/`Finsupp.tail` (split off the exponent of `x₀`),
multiplicativity being the Cauchy-product rearrangement of the
convolution over split monomials (`sum_antidiagonal_cons`). Stated over
an arbitrary commutative base ring: both consumers below induct with a
changing base. -/
theorem nonempty_ringEquiv_mvPowerSeries_powerSeries {R : Type*}
    [CommRing R] (n : ℕ) :
    Nonempty (MvPowerSeries (Fin (n + 1)) R ≃+*
      PowerSeries (MvPowerSeries (Fin n) R)) := by
  refine ⟨{
    toFun := mvPowerSeriesSplit n
    invFun := mvPowerSeriesUnsplit n
    left_inv := fun f => ?_
    right_inv := fun G => ?_
    map_mul' := fun f g => ?_
    map_add' := fun f g => ?_ }⟩
  · -- left inverse: recombine the split exponents
    refine MvPowerSeries.ext fun p => ?_
    rw [coeff_mvPowerSeriesUnsplit, coeff_coeff_mvPowerSeriesSplit,
      Finsupp.cons_tail]
  · -- right inverse: split the recombined exponents
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, coeff_mvPowerSeriesUnsplit,
      Finsupp.tail_cons, Finsupp.cons_zero]
  · -- multiplicativity: the Cauchy product rearranges over split monomials
    classical
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, MvPowerSeries.coeff_mul,
      PowerSeries.coeff_mul, map_sum]
    simp only [MvPowerSeries.coeff_mul, coeff_coeff_mvPowerSeriesSplit]
    exact sum_antidiagonal_cons k m fun p =>
      MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g
  · -- additivity: coefficientwise
    refine PowerSeries.ext fun k => ?_
    refine MvPowerSeries.ext fun m => ?_
    rw [coeff_coeff_mvPowerSeriesSplit, map_add, map_add, map_add,
      coeff_coeff_mvPowerSeriesSplit, coeff_coeff_mvPowerSeriesSplit]

/-- **Noetherianness of multivariate power series** (PROVEN 2026-07-23
modulo the variable-splitting leaf above — a mathlib gap: the
single-variable instance `IsNoetherianRing R⟦X⟧` exists in the pin, the
finitely-many-variables version does not): power series in finitely
many variables over a Noetherian commutative ring form a Noetherian
ring, by induction on the number of variables along the splitting
isomorphism, the single-variable step being mathlib's
Hilbert-basis-style instance and the base case the constants
isomorphism `MvPowerSeries (Fin 0) R ≅ R`. Stated over an arbitrary
Noetherian base (rather than `ℤ_ℓ`) because the induction changes the
base at every step. -/
theorem isNoetherianRing_mvPowerSeries {R : Type*} [CommRing R]
    [IsNoetherianRing R] (g : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin g) R) := by
  induction g with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (RingEquiv.ofBijective
      (MvPowerSeries.C : R →+* MvPowerSeries (Fin 0) R)
      ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩)
  | succ n ih =>
    obtain ⟨e⟩ := nonempty_ringEquiv_mvPowerSeries_powerSeries (R := R) n
    haveI := ih
    exact isNoetherianRing_of_ringEquiv _ e.symm

/-- **Prime chain in `Λ[[x₁,…,x_g]]`, `Λ` a local domain** (PROVEN
2026-07-23 modulo the
variable-splitting leaf `nonempty_ringEquiv_mvPowerSeries_powerSeries`):
a strictly increasing chain of `g + 1` primes inside the maximal ideal
— morally `(0) ⊂ (x_g) ⊂ (x_{g−1}, x_g) ⊂ ⋯ ⊂ (x₁,…,x_g)`.

Proof, by induction on `g`: for `g = 0` the constant chain `(⊥)` works
(the ring is a domain by `MvPowerSeries`' `NoZeroDivisors` instance).
For the step, split off one variable: pull the chain of the `n`-variable
ring back along the (surjective) constant-coefficient map of the
single-variable power series ring over it — pullback along a surjection
is strictly monotone and preserves primality — and prepend `⊥` (prime:
power series over a domain form a domain; strictly below the pullback
of the bottom link, which contains `X` while `⊥` does not); transport
the resulting chain along the splitting isomorphism; the top link stays
inside the maximal ideal because a power series with non-unit constant
coefficient is a non-unit. -/
theorem exists_isPrime_chain_mvPowerSeries (Λ : Type*) [CommRing Λ]
    [IsDomain Λ] [IsLocalRing Λ] (g : ℕ) :
    ∃ c : Fin (g + 1) → Ideal (MvPowerSeries (Fin g) Λ),
      StrictMono c ∧ (∀ i, (c i).IsPrime) ∧
      c (Fin.last g) ≤
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) := by
  induction g with
  | zero =>
    haveI : IsDomain (MvPowerSeries (Fin 0) Λ) :=
      NoZeroDivisors.to_isDomain _
    exact ⟨fun _ => ⊥, fun i j hij => (hij.ne (Fin.ext (by omega))).elim,
      fun _ => Ideal.isPrime_bot, bot_le⟩
  | succ n ih =>
    obtain ⟨c, hmono, hprime, hle⟩ := ih
    obtain ⟨e⟩ :=
      nonempty_ringEquiv_mvPowerSeries_powerSeries (R := Λ) n
    haveI : IsDomain (MvPowerSeries (Fin n) Λ) :=
      NoZeroDivisors.to_isDomain _
    -- the pulled-back chain over the split ring, with `⊥` prepended
    let c' : Fin (n + 1 + 1) →
        Ideal (PowerSeries (MvPowerSeries (Fin n) Λ)) :=
      Fin.cases ⊥ fun i => (c i).comap
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ))
    have hc'zero : c' 0 = ⊥ := rfl
    have hc'succ : ∀ i : Fin (n + 1), c' i.succ = (c i).comap
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) :=
      fun i => rfl
    -- pulling back along the (surjective) constant-coefficient map is
    -- strictly monotone
    have hccSM : StrictMono
        fun I : Ideal (MvPowerSeries (Fin n) Λ) => I.comap
          (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) :=
      Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
        (Ideal.comap_injective_of_surjective _
          PowerSeries.constantCoeff_surj)
    have hSM : StrictMono c' := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [Fin.castSucc_zero, hc'zero, hc'succ 0]
        refine bot_lt_iff_ne_bot.mpr fun hbot => ?_
        have hX : PowerSeries.X ∈ (c 0).comap
            (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)) := by
          show PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)
            PowerSeries.X ∈ c 0
          rw [PowerSeries.constantCoeff_X]
          exact (c 0).zero_mem
        rw [hbot] at hX
        exact PowerSeries.X_ne_zero (Ideal.mem_bot.mp hX)
      | succ j _ =>
        rw [← Fin.succ_castSucc, hc'succ j.castSucc, hc'succ j.succ]
        exact hccSM (hmono (Fin.castSucc_lt_succ (i := j)))
    -- primality along the pulled-back chain
    have hprime' : ∀ i, (c' i).IsPrime := by
      intro i
      induction i using Fin.induction with
      | zero =>
        rw [hc'zero]
        exact Ideal.isPrime_bot
      | succ j _ =>
        rw [hc'succ j]
        haveI := hprime j
        exact Ideal.IsPrime.comap _
    -- transport along the splitting isomorphism
    have heSM : StrictMono
        fun I : Ideal (PowerSeries (MvPowerSeries (Fin n) Λ)) =>
          I.comap (e : MvPowerSeries (Fin (n + 1)) Λ →+*
            PowerSeries (MvPowerSeries (Fin n) Λ)) :=
      Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
        (Ideal.comap_injective_of_surjective _ e.surjective)
    refine ⟨fun i => (c' i).comap
      (e : MvPowerSeries (Fin (n + 1)) Λ →+*
        PowerSeries (MvPowerSeries (Fin n) Λ)),
      heSM.comp hSM, fun i => ?_, ?_⟩
    · haveI := hprime' i
      exact Ideal.IsPrime.comap _
    · intro x hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hx' : PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)
          (e x) ∈ c (Fin.last n) := by
        have hmem : e x ∈ c' (Fin.last (n + 1)) := hx
        rw [← Fin.succ_last, hc'succ (Fin.last n)] at hmem
        exact hmem
      have hnonu := hle hx'
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hnonu
      exact hnonu ((hu.map e).map
        (PowerSeries.constantCoeff (R := MvPowerSeries (Fin n) Λ)))

/-- **Height of the maximal ideal of `Λ[[x₁,…,x_g]]`, `Λ` a local
domain** (PROVEN
2026-07-23 modulo the prime-chain leaf above): at least `g`. Walking up
the chain raises the height by at least one per strict link
(`Ideal.height_add_one_le_of_lt_of_isPrime`), and the height is
monotone in the ideal (`Ideal.height_mono`). (The height is in fact
`g + 1`, the chain extending to `𝔪 = (ℓ, x₁,…,x_g)` on top, but `g`
is all the Krull glue below needs.) -/
theorem le_height_maximalIdeal_mvPowerSeries (Λ : Type*) [CommRing Λ]
    [IsDomain Λ] [IsLocalRing Λ] (g : ℕ) :
    (g : ℕ∞) ≤
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ)).height := by
  obtain ⟨c, hmono, hprime, hle⟩ :=
    exists_isPrime_chain_mvPowerSeries Λ g
  have hstep : ∀ i : Fin (g + 1), ((i : ℕ) : ℕ∞) ≤ (c i).height := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      haveI := hprime j.castSucc
      haveI := hprime j.succ
      have hlt := Ideal.height_add_one_le_of_lt_of_isPrime
        (hmono (Fin.castSucc_lt_succ (i := j)))
      have hcast : ((j.succ : ℕ) : ℕ∞) = ((j.castSucc : ℕ) : ℕ∞) + 1 := by
        simp
      rw [hcast]
      exact le_trans (add_le_add ih le_rfl) hlt
  have hlast := hstep (Fin.last g)
  rw [Fin.val_last] at hlast
  exact hlast.trans (Ideal.height_mono hle)

/-- **Krull glue for the presentation stratum** (PROVEN 2026-07-23
modulo the two commutative-algebra leaves above — no arithmetic
content): a local ring presented as a quotient of `Λ[[x₁,…,x_g]]` —
`Λ` a Noetherian local domain — by
an ideal generated by `r < g` elements has a prime strictly below its
maximal ideal.

Proof: if not, every prime of `R` equals the maximal ideal, so — the
prime correspondence along the surjection `φ` being elementary — the
maximal ideal of the power series ring is a *minimal* prime over
`ker φ`; Krull's height theorem
(`Ideal.height_le_card_of_mem_minimalPrimes_span`) then bounds its
height by `r`, contradicting the height lower bound `g > r`. -/
theorem exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ]
    [IsNoetherianRing Λ]
    {R : Type*} [CommRing R] [IsLocalRing R] {g r : ℕ} (hrg : r < g)
    (φ : MvPowerSeries (Fin g) Λ →+* R) (hφ : Function.Surjective φ)
    (f : Fin r → MvPowerSeries (Fin g) Λ)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    ∃ P : Ideal R, P.IsPrime ∧ P < IsLocalRing.maximalIdeal R := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : IsNoetherianRing (MvPowerSeries (Fin g) Λ) :=
    isNoetherianRing_mvPowerSeries g
  -- the kernel is proper, hence contained in the maximal ideal
  have hKtop : RingHom.ker φ ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPowerSeries (Fin g) Λ) ∈ RingHom.ker φ :=
      htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hKle : RingHom.ker φ ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) :=
    IsLocalRing.le_maximalIdeal hKtop
  -- were there no prime strictly below the maximal ideal of `R`, the
  -- maximal ideal of the power series ring would be a MINIMAL prime
  -- over the kernel
  have hmin : IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ∈
      (RingHom.ker φ).minimalPrimes := by
    refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, hKle⟩, ?_⟩
    rintro Q ⟨hQp, hKQ⟩ _
    haveI := hQp
    -- the image of `Q` is a prime of `R` not strictly below the maximal
    -- ideal, hence equal to it
    have hmapP : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hKQ
    have hmaple : Q.map φ ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hmapP.ne_top
    have hmapeq : Q.map φ = IsLocalRing.maximalIdeal R :=
      (eq_or_lt_of_le hmaple).resolve_right (hcon _ hmapP)
    -- the surjection is local: the maximal ideal lands in the maximal
    -- ideal (else a preimage of the inverse of a unit value writes `1`
    -- as an element of the maximal ideal)
    have hloc : IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) ≤
        (IsLocalRing.maximalIdeal R).comap φ := by
      intro x hx
      show φ x ∈ IsLocalRing.maximalIdeal R
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨y, hy⟩ := hφ (↑hu.unit⁻¹)
      have hxy : x * y - 1 ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hy, map_one, hu.mul_val_inv,
          sub_self]
      have h1 : (1 : MvPowerSeries (Fin g) Λ) ∈
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) Λ) := by
        have hsub := sub_mem (Ideal.mul_mem_right y _ hx) (hKle hxy)
        rwa [sub_sub_cancel] at hsub
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    -- and the pullback of the image of `Q` is `Q` itself
    have hpull : (IsLocalRing.maximalIdeal R).comap φ = Q := by
      rw [← hmapeq, Ideal.comap_map_of_surjective φ hφ,
        ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hKQ]
    exact hloc.trans hpull.le
  -- Krull's height theorem bounds the height of the maximal ideal by
  -- the number of generators of the kernel …
  rw [hker] at hmin
  have hkr := Ideal.height_le_card_of_mem_minimalPrimes_span
    (Set.finite_range f) hmin
  have hcard : (Set.range f).ncard ≤ r := by
    have himg := Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin r)))
      Set.finite_univ
    rw [Set.image_univ] at himg
    simpa [Set.ncard_univ] using himg
  -- … contradicting the height lower bound `g > r`
  have hgr : (g : ℕ∞) ≤ (r : ℕ∞) :=
    (le_height_maximalIdeal_mvPowerSeries Λ g).trans
      (hkr.trans (Nat.cast_le.mpr hcard))
  exact absurd (Nat.cast_le.mp hgr) (Nat.not_le.mpr hrg)

/-- **Dimension leaf** (DECOMPOSED 2026-07-23 into the Böckle
presentation leaf
`exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated`
— the Galois-cohomological generators-and-relations count `g − r ≥ 1` —
plus the Krull glue
`exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation`, itself
proven modulo the two pure commutative-algebra leaves
`isNoetherianRing_mvPowerSeries` and
`le_height_maximalIdeal_mvPowerSeries`; the assembly below is proven):
the weakly universal, trace-generated hardly ramified deformation ring
has Krull dimension `≥ 1` — some prime lies strictly below the maximal
ideal. -/
theorem exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated
    (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar)
    (hw : D.IsWeaklyUniversal) (ht : D.IsTraceGenerated) :
    letI := D.commRing; letI := D.isLocalRing
    ∃ P : Ideal D.R, P.IsPrime ∧ P < IsLocalRing.maximalIdeal D.R := by
  letI := D.commRing; letI := D.isLocalRing; letI := D.algebra
  obtain ⟨Λ, iΛ1, iΛ2, iΛ3, iΛ4, iΛ5, iΛ6, g, r, φ, f, hrg, hφ, -, hker⟩ :=
    exists_mvPowerSeries_presentation_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D hw ht
  letI := iΛ1; letI := iΛ2; letI := iΛ3; letI := iΛ4
  exact exists_isPrime_lt_maximalIdeal_of_mvPowerSeries_presentation hrg φ hφ
    f hker

/-- **A local ring of Krull dimension `≥ 1` is infinite** (PROVEN,
elementary): were `R` finite, the quotient by a prime `P` strictly below
the maximal ideal would be a finite integral domain, hence a field,
making `P` maximal — but the only maximal ideal of a local ring is the
maximal ideal, contradicting strictness. -/
lemma infinite_of_isPrime_lt_maximalIdeal {R : Type*} [CommRing R]
    [IsLocalRing R] {P : Ideal R} (hP : P.IsPrime)
    (hlt : P < IsLocalRing.maximalIdeal R) : Infinite R := by
  by_contra hinf
  rw [not_infinite_iff_finite] at hinf
  haveI := hinf
  haveI := hP
  haveI : Finite (R ⧸ P) :=
    Finite.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hmax : P.IsMaximal :=
    Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (R ⧸ P))
  exact absurd (IsLocalRing.eq_maximalIdeal hmax) (ne_of_lt hlt)

/-- **Kernel dichotomy for module-finite `ℤ_ℓ`-algebras** (PROVEN,
elementary): a `ℤ_ℓ`-algebra that is finite as a `ℤ_ℓ`-module and
infinite as a set has characteristic zero — the structure map is
injective. If some `x ≠ 0` died in `R`, then so would `ℓ ^ v(x)` (every
nonzero element of `ℤ_ℓ` is a unit times a power of `ℓ`), and reducing
the coordinates of the finitely many module generators mod `ℓ ^ v(x)`
would exhibit `R` as the image of the finite set `(ℤ/ℓ^{v(x)})^k`. -/
lemma algebraMap_injective_of_moduleFinite_of_infinite {R : Type*}
    [CommRing R] [Algebra ℤ_[ℓ] R] (hfin : Module.Finite ℤ_[ℓ] R)
    (hinf : Infinite R) : Function.Injective (algebraMap ℤ_[ℓ] R) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  by_contra hx0
  -- `ℓ ^ v(x)` is a unit multiple of `x`, hence also dies in `R`
  have hℓn : algebraMap ℤ_[ℓ] R ((ℓ : ℤ_[ℓ]) ^ x.valuation) = 0 := by
    have hprod : algebraMap ℤ_[ℓ] R ((PadicInt.unitCoeff hx0 : ℤ_[ℓ])) *
        algebraMap ℤ_[ℓ] R ((ℓ : ℤ_[ℓ]) ^ x.valuation) = 0 := by
      rw [← map_mul, ← PadicInt.unitCoeff_spec hx0, hx]
    exact ((PadicInt.unitCoeff hx0).isUnit.map
      (algebraMap ℤ_[ℓ] R)).mul_right_eq_zero.mp hprod
  -- so `R` is covered by a finite set: reduce coordinates mod `ℓ ^ v(x)`
  haveI := hfin
  haveI := hinf
  haveI : NeZero (ℓ ^ x.valuation) :=
    ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[ℓ] R
  have hsurj : Function.Surjective
      fun c : Fin k → ZMod (ℓ ^ x.valuation) =>
        φ fun i => ((c i).val : ℤ_[ℓ]) := by
    intro r
    obtain ⟨c, rfl⟩ := hφ r
    refine ⟨fun i => PadicInt.toZModPow x.valuation (c i), ?_⟩
    have hker : ∀ i, c i -
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ])) ∈
        Ideal.span {(ℓ : ℤ_[ℓ]) ^ x.valuation} := by
      intro i
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ZMod.natCast_val, ZMod.cast_id, sub_self]
    choose d hd using fun i => Ideal.mem_span_singleton'.mp (hker i)
    have hvec : (c - fun i =>
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ]))) =
        ((ℓ : ℤ_[ℓ]) ^ x.valuation) • d := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hd i, mul_comm]
    have hφd : φ c - φ (fun i =>
        (((PadicInt.toZModPow x.valuation (c i)).val : ℤ_[ℓ]))) = 0 := by
      rw [← map_sub, hvec, map_smul, Algebra.smul_def, hℓn, zero_mul]
    exact (sub_eq_zero.mp hφd).symm
  haveI := Finite.of_surjective _ hsurj
  exact not_finite R

/-- **Presentation stratum** (DECOMPOSED 2026-07-22 into the arithmetic
leaf `exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated`
— Böckle's presentation bound `g − r ≥ 1` giving Krull dimension `≥ 1` —
plus PROVEN formal glue): the universal hardly ramified deformation ring
has characteristic zero — `ℤ_ℓ` embeds.

The assembly below is proven: dimension `≥ 1` makes the constructed
universal ring infinite (`infinite_of_isPrime_lt_maximalIdeal`);
infiniteness transports to `D.R` along the canonical isomorphism of
universal data; and an infinite module-finite `ℤ_ℓ`-algebra (finiteness
by `moduleFinite_of_isUniversal`) has injective structure map
(`algebraMap_injective_of_moduleFinite_of_infinite` — a nonzero kernel
`(ℓ^n)` would make `R` a quotient of a finite set). -/
theorem algebraMap_injective_of_isUniversal (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible)
    (D : HardlyRamifiedDeformation hℓOdd ρbar) (hD : D.IsUniversal) :
    letI := D.commRing; letI := D.algebra
    Function.Injective (algebraMap ℤ_[ℓ] D.R) := by
  letI := D.commRing; letI := D.algebra
  have hfin : Module.Finite ℤ_[ℓ] D.R :=
    moduleFinite_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  obtain ⟨D₀, hw₀, ht₀⟩ :=
    exists_isWeaklyUniversal_isTraceGenerated hℓOdd hdim hℓ5 h hirr
  letI := D₀.commRing; letI := D₀.isLocalRing; letI := D₀.algebra
  have hD₀ : D₀.IsUniversal :=
    isUniversal_of_isWeaklyUniversal_isTraceGenerated hℓOdd D₀ hw₀ ht₀
  obtain ⟨P, hP, hlt⟩ :=
    exists_isPrime_lt_maximalIdeal_of_isWeaklyUniversal_isTraceGenerated
      hℓOdd hdim hℓ5 h hirr D₀ hw₀ ht₀
  have hinf₀ : Infinite D₀.R := infinite_of_isPrime_lt_maximalIdeal hP hlt
  obtain ⟨e, _⟩ := exists_ringEquiv_of_isUniversal hℓOdd D₀ D hD₀ hD
  have hinf : Infinite D.R := @Infinite.of_injective _ _ hinf₀ e e.injective
  exact algebraMap_injective_of_moduleFinite_of_infinite hfin hinf

open IsLocalRing Topology in
/-- **Topology glue** (PROVEN 2026-07-22, elementary — no arithmetic
content): on a module-finite local `ℤ_ℓ`-algebra whose topology is the
maximal-adic one and which is adically complete and separated, the
topology is the `ℤ_ℓ`-module topology.

Proof: (1) `ℓ` lands in the maximal ideal — otherwise the span chain of
the powers of its inverse violates Noetherian stabilization (morally:
`ℚ_ℓ` would embed as a finitely generated `ℤ_ℓ`-submodule); hence the
structure map `ℤ_ℓ → R` is continuous (`ℓ^k`-balls land in `𝔪^k`) and
`R` is a topological `ℤ_ℓ`-module, giving `moduleTopology ≤ τ_R` for
free (`moduleTopology_le`). (2) For the converse, the module topology is
compact — it is the coinduced topology along a surjection
`ℤ_ℓ^n ↠ R` from a compact space
(`ModuleTopology.eq_coinduced_of_surjective`) — while `τ_R` is Hausdorff
(adic separatedness: `{0} = ⋂ 𝔪^k` is an intersection of closed open
subgroups), so the continuous identity from the module topology to
`τ_R` is a homeomorphism (`Continuous.homeoOfEquivCompactToT2`), and
the two topologies agree (`IsModuleTopology.of_continuous_id`). -/
theorem isModuleTopology_of_isAdic_maximalIdeal {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R)) :
    IsModuleTopology ℤ_[ℓ] R := by
  classical
  -- Step 1: `ℓ` lands in the maximal ideal (else `ℚ_ℓ` would embed as a
  -- finitely generated `ℤ_ℓ`-submodule).
  have hℓm : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∈ maximalIdeal R := by
    by_contra hu
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
    obtain ⟨u, hu⟩ := hu
    haveI : IsNoetherian ℤ_[ℓ] R :=
      isNoetherian_of_isNoetherianRing_of_finite ℤ_[ℓ] R
    have hvu : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
    -- the ascending chain of spans of powers of the inverse stabilizes
    have hmono : Monotone fun n : ℕ =>
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} := by
      apply monotone_nat_of_le_succ
      intro n
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      refine ⟨(ℓ : ℤ_[ℓ]), ?_⟩
      calc (ℓ : ℤ_[ℓ]) • ((u⁻¹ : Rˣ) : R) ^ (n + 1)
          = (((u⁻¹ : Rˣ) : R) * (u : R)) * ((u⁻¹ : Rˣ) : R) ^ n := by
            rw [Algebra.smul_def, ← hu]; ring
        _ = ((u⁻¹ : Rˣ) : R) ^ n := by rw [hvu, one_mul]
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
      (inferInstance : IsNoetherian ℤ_[ℓ] R) ⟨_, hmono⟩
    have heq : Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} =
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ (n + 1)} :=
      hn (n + 1) (Nat.le_succ n)
    have hmem : ((u⁻¹ : Rˣ) : R) ^ (n + 1) ∈
        Submodule.span ℤ_[ℓ] {((u⁻¹ : Rˣ) : R) ^ n} := by
      rw [heq]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    -- multiply by `u^(n+1)`: `algebraMap (c * ℓ) = 1`
    have h1 : algebraMap ℤ_[ℓ] R (c * ℓ) = 1 := by
      have h := congrArg (· * ((u : R)) ^ (n + 1)) hc
      simp only [Algebra.smul_def] at h
      have hpow : ((u⁻¹ : Rˣ) : R) ^ n * ((u : R)) ^ (n + 1) = (u : R) := by
        calc ((u⁻¹ : Rˣ) : R) ^ n * ((u : R)) ^ (n + 1)
            = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ n * (u : R) := by ring
          _ = (u : R) := by rw [hvu, one_pow, one_mul]
      rw [map_mul, ← hu]
      calc algebraMap ℤ_[ℓ] R c * (u : R)
          = algebraMap ℤ_[ℓ] R c * ((u⁻¹ : Rˣ) : R) ^ n *
              ((u : R)) ^ (n + 1) := by rw [mul_assoc, hpow]
        _ = ((u⁻¹ : Rˣ) : R) ^ (n + 1) * ((u : R)) ^ (n + 1) := h
        _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ (n + 1) := by rw [mul_pow]
        _ = 1 := by rw [hvu, one_pow]
    -- but `1 - c * ℓ` is a unit of `ℤ_ℓ` in the kernel of `algebraMap`
    have hker : algebraMap ℤ_[ℓ] R (1 - c * ℓ) = 0 := by
      rw [map_sub, map_one, h1, sub_self]
    have hkne : RingHom.ker (algebraMap ℤ_[ℓ] R) ≠ ⊤ := by
      intro htop
      have h1mem : (1 : ℤ_[ℓ]) ∈ RingHom.ker (algebraMap ℤ_[ℓ] R) :=
        htop ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1mem
      exact one_ne_zero h1mem
    have hcl : c * (ℓ : ℤ_[ℓ]) ∈ maximalIdeal ℤ_[ℓ] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton.mpr ⟨c, mul_comm c _⟩
    have hone : (1 : ℤ_[ℓ]) ∈ maximalIdeal ℤ_[ℓ] := by
      have h := add_mem (IsLocalRing.le_maximalIdeal hkne
        (RingHom.mem_ker.mpr hker)) hcl
      rwa [sub_add_cancel] at h
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[ℓ]).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)
  -- Step 2: the structure map is continuous, so `R` is a topological
  -- `ℤ_ℓ`-module for its given topology.
  have hcont : Continuous (algebraMap ℤ_[ℓ] R) := by
    apply continuous_of_continuousAt_zero (algebraMap ℤ_[ℓ] R)
    unfold ContinuousAt
    rw [map_zero, hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    have hball : Metric.closedBall (0 : ℤ_[ℓ]) ((ℓ : ℝ) ^ (-(k : ℤ))) ∈
        𝓝 (0 : ℤ_[ℓ]) := by
      refine Metric.closedBall_mem_nhds 0 ?_
      exact zpow_pos (Nat.cast_pos.mpr (Fact.out : ℓ.Prime).pos) _
    filter_upwards [hball] with x hx
    have hx' : x ∈ Ideal.span {((ℓ : ℤ_[ℓ])) ^ k} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hx'
    show algebraMap ℤ_[ℓ] R x ∈ ((maximalIdeal R ^ k : Ideal R) : Set R)
    rw [← hd, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hℓm k)
  haveI hsmul : ContinuousSMul ℤ_[ℓ] R :=
    continuousSMul_of_algebraMap ℤ_[ℓ] R hcont
  -- Step 3: the given topology is Hausdorff (adic separatedness).
  haveI ht2 : T2Space R := by
    have hclosed : IsClosed ({(0 : R)} : Set R) := by
      have h0 : ({(0 : R)} : Set R) =
          ⋂ k : ℕ, ((maximalIdeal R ^ k : Ideal R) : Set R) := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
        constructor
        · rintro rfl k
          exact Submodule.zero_mem _
        · intro hx
          refine IsHausdorff.haus
            (inferInstance : IsHausdorff (maximalIdeal R) R) x fun k => ?_
          rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
          exact hx k
      rw [h0]
      refine isClosed_iInter fun k => ?_
      exact AddSubgroup.isClosed_of_isOpen
        (Submodule.toAddSubgroup (maximalIdeal R ^ k))
        ((isAdic_iff.mp hadic).1 k)
    haveI := IsTopologicalAddGroup.t1Space R hclosed
    infer_instance
  -- Step 4: the module topology is compact (continuous surjective image of
  -- `ℤ_ℓⁿ`) …
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[ℓ] R
  have hcoind : moduleTopology ℤ_[ℓ] R =
      TopologicalSpace.coinduced φ inferInstance :=
    ModuleTopology.eq_coinduced_of_surjective hφ
  have hφc : @Continuous (Fin n → ℤ_[ℓ]) R _ (moduleTopology ℤ_[ℓ] R) φ :=
    continuous_iff_coinduced_le.mpr (le_of_eq hcoind.symm)
  have hcompact : @CompactSpace R (moduleTopology ℤ_[ℓ] R) :=
    @Function.Surjective.compactSpace _ _ _ (moduleTopology ℤ_[ℓ] R) _ hφc
      inferInstance hφ
  -- … so the continuous identity from the (compact) module topology to the
  -- (Hausdorff) given topology is a homeomorphism, and the two agree.
  have hid : @Continuous R R (moduleTopology ℤ_[ℓ] R) _ id :=
    continuous_id_iff_le.mpr (moduleTopology_le ℤ_[ℓ] R)
  exact IsModuleTopology.of_continuous_id
    (@Homeomorph.continuous_symm R R (moduleTopology ℤ_[ℓ] R) _
      (@Continuous.homeoOfEquivCompactToT2 R R
        (moduleTopology ℤ_[ℓ] R) _ hcompact ht2 (Equiv.refl R) hid))

/-- **B6a-core**: the Khare–Wintenberger-style lifting core.
An irreducible hardly ramified mod-`ℓ` representation with `ℓ ≥ 5` lifts to
a hardly ramified representation over *some* coefficient ring `R` — a local
topological `ℤ_ℓ`-algebra, finite as a `ℤ_ℓ`-module, carrying the
`ℤ_ℓ`-module topology, of characteristic zero (`ℤ_ℓ` embeds) — with a
reduction map matching the characteristic polynomials of Frobenius of
`ρbar` at all good primes. `R` is *not* required to be a domain.

DECOMPOSED (2026-07-22) along the standard deformation-theoretic proof
into the three strata above — representability
(`exists_universal_hardlyRamifiedDeformation`: Mazur/Ramakrishna/Carayol),
`ℤ_ℓ`-module finiteness of the universal ring
(`moduleFinite_of_isUniversal`: potential modularity, Taylor–Wiles–Kisin,
Khare–Wintenberger), characteristic zero
(`algebraMap_injective_of_isUniversal`: Böckle's presentation bound
`g − r ≥ 1`) — plus the elementary topology glue
(`isModuleTopology_of_isAdic_maximalIdeal`). The assembly below is
proven: it takes the universal datum and repackages it with the three
pinned-down properties.

References: Khare–Wintenberger, *Serre's modularity conjecture (I)*,
Thm. 4.1 and §4; Böckle's appendix to Khare's *Serre's conjecture* notes;
Buzzard's 2026 EPSRC course, Lecture 4. -/
theorem exists_finite_lift (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLocalRing R) (_ : Algebra ℤ_[ℓ] R)
      (_ : Module.Finite ℤ_[ℓ] R) (_ : IsModuleTopology ℤ_[ℓ] R),
      Function.Injective (algebraMap ℤ_[ℓ] R) ∧
      ∃ ρ : FramedGaloisRep ℚ R (Fin 2),
        IsHardlyRamified hℓOdd (rank_finTwoFun R) ρ ∧
        ∃ π : R →+* k, Function.Surjective π ∧
          ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
          (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
            ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
  obtain ⟨D, hD⟩ :=
    exists_universal_hardlyRamifiedDeformation hℓOdd hdim hℓ5 h hirr
  letI := D.commRing; letI := D.topologicalSpace; letI := D.isTopologicalRing
  letI := D.isLocalRing; letI := D.algebra; letI := D.isNoetherianRing
  letI := D.isAdicComplete
  have hfin : Module.Finite ℤ_[ℓ] D.R :=
    moduleFinite_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  letI := hfin
  have hmt : IsModuleTopology ℤ_[ℓ] D.R :=
    isModuleTopology_of_isAdic_maximalIdeal D.isAdic
  have hinj : Function.Injective (algebraMap ℤ_[ℓ] D.R) :=
    algebraMap_injective_of_isUniversal hℓOdd hdim hℓ5 h hirr D hD
  exact ⟨D.R, D.commRing, D.topologicalSpace, D.isTopologicalRing,
    D.isLocalRing, D.algebra, hfin, hmt, hinj, D.ρ, D.isHardlyRamified,
    D.π, D.π_surjective, D.charFrob_compat⟩

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Flatness transfers along quotient specialization** (PROVEN
2026-07-22, mirroring the residue-field transfer
`IsHardlyRamified.isFlatAt_baseChange_residue` of `Threeadic.lean`): if
`ρ` is flat at `ℓ`, so is its base change to a quotient `R ⧸ P` of the
coefficient ring. The open ideals of `R ⧸ P` correspond to the open
ideals `J ⊇ P` of `R` (preimages along the continuous quotient map are
open), the double base change `((R ⧸ P) ⧸ I) ⊗ ((R ⧸ P) ⊗ M)` collapses
equivariantly to `(R ⧸ J) ⊗ M` (tensor cancellation
`AlgebraTensorModule.cancelBaseChange` plus the double-quotient
isomorphism `DoubleQuot.quotQuotEquivQuotOfLE` along
`I = J.map (Ideal.Quotient.mk P)`), and
`HasFlatProlongationAt.of_equiv` transports the Hopf-algebra witness. -/
theorem isFlatAt_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    {ρ : GaloisRep ℚ R M}
    (hflat : ρ.IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))) :
    (ρ.baseChange (R ⧸ P)).IsFlatAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)) := by
  constructor
  intro I hI
  -- the corresponding open ideal of `R`, lying over `P`
  let J : Ideal R := I.comap (Ideal.Quotient.mk P)
  have hPJ : P ≤ J := fun x hx => by
    show Ideal.Quotient.mk P x ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact I.zero_mem
  have hImap : I = J.map (Ideal.Quotient.mk P) :=
    (Ideal.map_comap_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective I).symm
  have hJopen : IsOpen (J : Set R) := by
    have hpre : (J : Set R) =
        (Ideal.Quotient.mk P) ⁻¹' (I : Set (R ⧸ P)) := rfl
    rw [hpre]
    exact hI.preimage (QuotientRing.isOpenQuotientMap_mk P).continuous
  -- the coefficient identification `((R ⧸ P) ⧸ I) ≃+* R ⧸ J`
  let φ : ((R ⧸ P) ⧸ I) ≃+* (R ⧸ J) :=
    (Ideal.quotEquivOfEq hImap).trans (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
  have hφalg : ∀ r : R,
      φ (algebraMap R ((R ⧸ P) ⧸ I) r) = algebraMap R (R ⧸ J) r := by
    intro r
    show (DoubleQuot.quotQuotEquivQuotOfLE hPJ)
        ((Ideal.quotEquivOfEq hImap)
          (Ideal.Quotient.mk I (Ideal.Quotient.mk P r))) =
      Ideal.Quotient.mk J r
    rw [Ideal.quotEquivOfEq_mk]
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hPJ
  -- its `R`-linear form
  let φlin : ((R ⧸ P) ⧸ I) ≃ₗ[R] (R ⧸ J) :=
    { φ.toAddEquiv with
      map_smul' := fun r x => by
        show φ (r • x) = r • φ x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφalg] }
  -- assemble: cancel the middle base change, then transport coefficients
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ P)
    ((R ⧸ P) ⧸ I) ((R ⧸ P) ⧸ I) M
  let e₂ := TensorProduct.congr φlin (LinearEquiv.refl R M)
  let eSp : ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space ≃+
      ((ρ.baseChange (R ⧸ J)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space) :=
    e₁.toAddEquiv.trans e₂.toAddEquiv
  have he : ∀ (g : Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))))
      (x : (((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : ℓ.Prime))).Space),
      eSp (g • x) = g • eSp x := by
    intro g x
    show (e₁.toAddEquiv.trans e₂.toAddEquiv)
        ((((ρ.baseChange (R ⧸ P)).baseChange ((R ⧸ P) ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      ((ρ.baseChange (R ⧸ J)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((e₁.toAddEquiv.trans e₂.toAddEquiv) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero =>
        rw [show (c ⊗ₜ[R ⧸ P] (0 : (R ⧸ P) ⊗[R] M)) =
          (0 : ((R ⧸ P) ⧸ I) ⊗[R ⧸ P] ((R ⧸ P) ⊗[R] M)) from
          TensorProduct.tmul_zero _ _]
        simp
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        simp only [map_add, ha, hb]
      | tmul d m => rfl
  refine (hflat.cond J hJopen).of_equiv _ eSp.symm ?_
  intro g x
  apply eSp.injective
  rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Tameness at `2` transfers along base change** (generalization of the
proven residue-field transfer `IsHardlyRamified.isTameAtTwo_baseChange_residue`
in `Threeadic.lean` from finite residue fields to arbitrary topological
coefficient algebras `B`, same proof): the rank-1 tame quadratic quotient
`(π, δ)` of `ρ` at `2` base-changes to `(rid ∘ (π ⊗ 1), (δ ⊗ 1)ᵉ)` for
`ρ ⊗ B`. -/
lemma isTameAtTwo_baseChange {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B]
    {ρ : GaloisRep ℚ R M}
    (htame : ∃ (π : M →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : M,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (B ⊗[R] M) →ₗ[B] B) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] B B),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : B ⊗[R] M,
        π ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  obtain ⟨π, hπsurj, δ, h⟩ := htame
  -- the canonical identification `B ⊗[R] R ≃ₗ[B] B`
  let e : (B ⊗[R] R) ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid R B B
  -- the base-changed projection and character
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange B π, ?_,
    (δ.baseChange B).conj e, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · intro g w
    refine ⟨?_, ?_, ?_⟩
    · -- equivariance, by linearity on simple tensors
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have h1 := (h g v).1
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [show ((ρ.baseChange B).map (algebraMap ℚ ℚ_[2])) g (c ⊗ₜ v) =
          c ⊗ₜ ((ρ.map (algebraMap ℚ ℚ_[2])) g v) from rfl,
          LinearMap.baseChange_tmul, h1,
          GaloisRep.conj_apply, LinearMap.baseChange_tmul]
        rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.rid_symm_apply,
          show ((δ.baseChange B) g : Module.End B (B ⊗[R] R)) =
            LinearMap.baseChange B (δ g) from rfl,
          LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [show (δ g) (π v) = π v • (δ g) 1 from by
          conv_lhs => rw [show (π v : R) = π v • (1 : R) from by
            rw [smul_eq_mul, mul_one]]
          rw [map_smul]]
        simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
          mul_comm]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    · -- unramifiedness: the kernel only grows under base change + conj
      intro σ hσ
      have hδσ : δ σ = 1 := (h 1 0).2.1 hσ
      have : (δ.baseChange B).conj e σ = 1 := by
        rw [GaloisRep.conj_apply]
        rw [show (δ.baseChange B) σ =
          LinearMap.baseChange B (δ σ) from rfl, hδσ]
        refine LinearMap.ext fun c => ?_
        simp
      exact this
    · -- the quadratic condition transfers through the monoid hom
      intro g'
      have hsq : δ g' * δ g' = 1 := (h 1 0).2.2 g'
      calc (δ.baseChange B).conj e g' * (δ.baseChange B).conj e g'
          = (δ.baseChange B).conj e (g' * g') := (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply]
            rw [show (δ.baseChange B) (g' * g') =
              LinearMap.baseChange B (δ (g' * g')) from rfl,
              map_mul δ, hsq]
            refine LinearMap.ext fun c => ?_
            simp

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along quotient specialization of the
coefficients** (DERIVED 2026-07-22, mirroring the proven residue-field
transfer `exists_residual_isHardlyRamified` of `Threeadic.lean`): the
determinant condition maps along `R → R ⧸ P` (`LinearMap.det_baseChange`),
unramifiedness passes to any base change (existing instance), tameness at
`2` and flatness at `ℓ` by the proven transfers above. -/
lemma isHardlyRamified_baseChange_quotient {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] {hdimM : Module.rank R M = 2}
    (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)]
    (hdimQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] M) = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ) :
    IsHardlyRamified hℓOdd hdimQ (ρ.baseChange (R ⧸ P)) := by
  constructor
  · -- the determinant condition maps along the quotient map
    intro g
    have hdet : (ρ.baseChange (R ⧸ P)).det g =
        algebraMap R (R ⧸ P) (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange (R ⧸ P)) g) = _
      rw [show ((ρ.baseChange (R ⧸ P)) g :
          Module.End (R ⧸ P) ((R ⧸ P) ⊗[R] M)) =
        LinearMap.baseChange (R ⧸ P) (ρ g) from rfl,
        LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro p hp hpp
    letI : ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat :=
      h.isUnramified p hp hpp
    infer_instance
  · -- flatness at ℓ (sorried transfer leaf)
    exact isFlatAt_baseChange_quotient P h.isFlat
  · -- tameness at 2 (proven transfer)
    exact isTameAtTwo_baseChange (R ⧸ P) h.isTameAtTwo

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **Hardly-ramifiedness transfers along conjugation** by a linear
isomorphism of the representation space (PROVEN 2026-07-22): the
determinant is conjugation-invariant, the kernels of the local
representations only grow, flatness transports through
`HasFlatProlongationAt.of_equiv` along the base-changed isomorphism, and
the tame quadratic quotient is composed with the inverse isomorphism. -/
lemma isHardlyRamified_conj {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hℓOdd hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsHardlyRamified hℓOdd hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness: the kernel of the local representation only grows
    intro p hp hpp
    have hun := h.isUnramified p hp hpp
    refine ⟨le_trans hun.localInertiaGroup_le ?_⟩
    intro σ hσ
    have h1 : ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1 := hσ
    show (ρ.conj e).toLocal hp.toHeightOneSpectrumRingOfIntegersRat σ = 1
    rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
      ← GaloisRep.toLocal_apply, h1]
    refine LinearMap.ext fun w => ?_
    simp
  · -- flatness: transport along the base-changed equivariant isomorphism
    constructor
    intro I hI
    refine (h.isFlat.cond I hI).of_equiv _
      (LinearEquiv.baseChange R (R ⧸ I) M N e).toAddEquiv ?_
    intro g x
    show (LinearEquiv.baseChange R (R ⧸ I) M N e)
        (((ρ.baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g) x) =
      (((ρ.conj e).baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : ℓ.Prime)) g)
        ((LinearEquiv.baseChange R (R ⧸ I) M N e) x)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [GaloisRep.toLocal_apply, GaloisRep.baseChange_tmul,
        LinearEquiv.baseChange_tmul, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · -- tameness at 2: compose the quotient with the inverse isomorphism
    obtain ⟨π, hπsurj, δ, hδ⟩ := h.isTameAtTwo
    refine ⟨π.comp (e.symm : N →ₗ[R] M), ?_, δ, ?_⟩
    · intro r
      obtain ⟨m, hm⟩ := hπsurj r
      exact ⟨e m, by simp [hm]⟩
    · intro g w
      refine ⟨?_, (hδ 1 0).2.1, (hδ 1 0).2.2⟩
      have h1 := (hδ g (e.symm w)).1
      show π (e.symm ((ρ.conj e).map (algebraMap ℚ ℚ_[2]) g w)) =
        δ g (π (e.symm w))
      rw [GaloisRep.map_apply, GaloisRep.conj_apply,
        LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
        ← GaloisRep.map_apply, h1]

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The Khare–Wintenberger lift, packaged** (generalized B6a): an
irreducible hardly ramified mod-`ℓ` representation over the finite
coefficient field `k`, `ℓ ≥ 5`, admits a hardly ramified `ℓ`-adic lift
over a characteristic-zero local topological domain `O` finite over
`ℤ_ℓ` with the `ℤ_ℓ`-module topology, together with a surjective
reduction `π : O →+* k` matching the Frobenius characteristic
polynomials at every prime `q ∉ {2, ℓ}`.

DERIVED from the Khare–Wintenberger core `exists_finite_lift` by
commutative algebra (this is the historical derivation of `Lift.lean`'s
`exists_hardlyRamifiedLift`, which now delegates here): `ℓ` is not
nilpotent in `R` (characteristic-zero injectivity), so some prime `P`
of `R` avoids it, and — every nonzero element of `ℤ_ℓ` being a unit
times a power of `ℓ` — `P` lies over `(0) ⊆ ℤ_ℓ`. The quotient
`O := R ⧸ P` is a characteristic-zero local topological domain, finite
over `ℤ_ℓ` with the `ℤ_ℓ`-module topology; the reduction map factors
through it (`P ⊆ 𝔪 = ker π`, the kernel being maximal because
`R/ker π` is a finite domain), and the characteristic polynomials of
Frobenius transport through the specialization by
`charpoly_baseChange_conj`. Hardly-ramifiedness specializes by
`isHardlyRamified_baseChange_quotient` + `isHardlyRamified_conj`.

This statement mirrors VERBATIM pillar α of
`Modularity/KhareWintenberger.lean`
(`exists_hardlyRamified_lift_residual_of_five_le`), which it
discharges; it lives here — in a module importing neither `Family.lean`
nor the modularity interface — so that both `Lift.lean` (at
`k = ZMod ℓ`) and the Khare–Wintenberger cut consume the SAME
deformation development without closing the interface's forbidden
cycle. -/
theorem exists_hardlyRamified_lift_of_five_le (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ k V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : TopologicalSpace O)
      (_ : IsTopologicalRing O) (_ : Algebra ℤ_[ℓ] O) (_ : IsLocalRing O)
      (_ : Module.Finite ℤ_[ℓ] O) (_ : IsModuleTopology ℤ_[ℓ] O)
      (_ : Function.Injective (algebraMap ℤ_[ℓ] O))
      (ρ : GaloisRep ℚ O (Fin 2 → O))
      (hrank : Module.rank O (Fin 2 → O) = 2)
      (_ : IsHardlyRamified hℓOdd hrank ρ)
      (π : O →+* k) (_ : Function.Surjective π),
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
        (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
          ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  obtain ⟨R, iR1, iR2, iR3, iR4, iR5, iR6, iR7, hinj, ρR, hρR, πR, hπRs,
    hπR⟩ := exists_finite_lift hℓOdd hdim hℓ5 h hirr
  letI := iR1; letI := iR2; letI := iR3; letI := iR4; letI := iR5
  letI := iR6; letI := iR7
  -- Step 1: a prime of `R` lying over `(0) ⊆ ℤ_ℓ`.
  obtain ⟨P, hPp, hP0⟩ : ∃ P : Ideal R, P.IsPrime ∧
      ∀ x : ℤ_[ℓ], algebraMap ℤ_[ℓ] R x ∈ P → x = 0 := by
    have hℓR : algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ nilradical R := by
      rw [mem_nilradical]
      rintro ⟨n, hn⟩
      rw [← map_pow] at hn
      exact pow_ne_zero n
        (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
        (hinj (hn.trans (map_zero (algebraMap ℤ_[ℓ] R)).symm))
    obtain ⟨P, hPp, hℓP⟩ : ∃ P : Ideal R, Ideal.IsPrime P ∧
        algebraMap ℤ_[ℓ] R (ℓ : ℤ_[ℓ]) ∉ P := by
      by_contra hcon
      push Not at hcon
      refine hℓR ?_
      rw [nilradical_eq_sInf]
      exact Submodule.mem_sInf.mpr fun J hJ => hcon J hJ
    refine ⟨P, hPp, fun x hx => by_contra fun hx0 => ?_⟩
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow] at hx
    rcases hPp.mem_or_mem hx with hu | hpow
    · exact hPp.ne_top (Ideal.eq_top_of_isUnit_mem P hu
        (IsUnit.map (algebraMap ℤ_[ℓ] R) (PadicInt.unitCoeff hx0).isUnit))
    · exact hℓP (hPp.mem_of_pow_mem _ hpow)
  haveI := hPp
  -- Step 2: `O := R ⧸ P` is a local topological domain of characteristic
  -- zero, finite over `ℤ_ℓ` with the `ℤ_ℓ`-module topology.
  have hloc : IsLocalRing (R ⧸ P) :=
    .of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := hloc
  have hfin : Module.Finite ℤ_[ℓ] (R ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
  letI := hfin
  have hmt : IsModuleTopology ℤ_[ℓ] (R ⧸ P) := by
    constructor
    have hquot :=
      (QuotientRing.isOpenQuotientMap_mk P).isQuotientMap.eq_coinduced
    have hmod := ModuleTopology.eq_coinduced_of_surjective
      (φ := (Ideal.Quotient.mkₐ ℤ_[ℓ] P).toLinearMap)
      (Ideal.Quotient.mkₐ_surjective ℤ_[ℓ] P)
    rw [hquot, hmod]
    rfl
  letI := hmt
  have hinjO : Function.Injective (algebraMap ℤ_[ℓ] (R ⧸ P)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx => hP0 x ?_
    rwa [IsScalarTower.algebraMap_apply ℤ_[ℓ] R (R ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hx
  -- Step 3: specialize the framed representation along `R → R ⧸ P`.
  let e : (R ⧸ P) ⊗[R] (Fin 2 → R) ≃ₗ[R ⧸ P] (Fin 2 → R ⧸ P) :=
    TensorProduct.piScalarRight R (R ⧸ P) (R ⧸ P) (Fin 2)
  let ρO : FramedGaloisRep ℚ (R ⧸ P) (Fin 2) := (ρR.baseChange (R ⧸ P)).conj e
  have hrankQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] (Fin 2 → R)) = 2 := by
    rw [Module.rank_baseChange, rank_finTwoFun]
    simp
  have hHRO : IsHardlyRamified hℓOdd (rank_finTwoFun (R ⧸ P)) ρO :=
    isHardlyRamified_conj hℓOdd (rank_finTwoFun (R ⧸ P))
      (isHardlyRamified_baseChange_quotient hℓOdd P hrankQ hρR) e
  -- Step 4: the reduction map factors through the quotient: `ker πR` is
  -- maximal (its quotient is a finite domain, hence a field), so it is the
  -- maximal ideal of the local ring `R`, which contains the prime `P`.
  have hPle : P ≤ RingHom.ker πR := by
    haveI : (RingHom.ker πR).IsPrime := RingHom.ker_isPrime πR
    haveI : Finite (R ⧸ RingHom.ker πR) :=
      Finite.of_equiv _ (RingHom.quotientKerEquivRange πR).symm.toEquiv
    calc P ≤ IsLocalRing.maximalIdeal R :=
          IsLocalRing.le_maximalIdeal hPp.ne_top
      _ = RingHom.ker πR := (IsLocalRing.eq_maximalIdeal
          (Ideal.Quotient.maximal_of_isField _
            (Finite.isField_of_domain (R ⧸ RingHom.ker πR)))).symm
  let πO : R ⧸ P →+* k :=
    Ideal.Quotient.lift P πR fun a ha => by
      rw [← RingHom.mem_ker]
      exact hPle ha
  have hπOs : Function.Surjective πO := by
    intro y
    obtain ⟨x, hx⟩ := hπRs y
    refine ⟨Ideal.Quotient.mk P x, ?_⟩
    rw [show πO (Ideal.Quotient.mk P x) = πR x from
      Ideal.Quotient.lift_mk P πR _]
    exact hx
  -- Step 5: assemble; the characteristic polynomials of Frobenius
  -- transport through the specialization.
  have hcompat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
      (ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map πO =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hq2 hqℓ
    have hcf : ρO.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (ρR.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map
          (algebraMap R (R ⧸ P)) :=
      charpoly_baseChange_conj ρR e
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)
    have hπcomp : πO.comp (algebraMap R (R ⧸ P)) = πR := by
      ext a
      rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.lift_mk P πR _
    rw [hcf, Polynomial.map_map, hπcomp]
    exact hπR q hq hq2 hqℓ
  exact ⟨R ⧸ P, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hloc, hfin, hmt, hinjO, ρO, rank_finTwoFun (R ⧸ P),
    hHRO, πO, hπOs, hcompat⟩

end GaloisRepresentation
