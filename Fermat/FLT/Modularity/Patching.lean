/-
Modularity/Patching.lean — own work for the Fermat project (not
vendored from the FLT project).

# The deformation-theoretic cut behind `R = 𝕋` (pillar 3b of the
Taylor–Wiles section of `Modularity/Interface.lean`)

This module opens the deformation-theoretic subtree behind the
patching pillar `exists_ringHom_charFrob_eq_of_heckeDeformation`
(`Modularity/Interface.lean`, pillar 3b): a hardly ramified `p`-adic
representation `ρ` over `R` whose residual representation is
irreducible and underlies a Hecke-side hardly ramified deformation
`(T, ρT, π)` factors through that deformation on Frobenius traces via
a ring homomorphism `Φ : T →+* R`.  Following the actual architecture
of the Wiles/Taylor–Wiles proof, the pillar is cut into the three
classical deformation-theoretic statements, each stated against the
vocabulary of `Fermat/FLT/Deformations/RepresentationTheory/`
(`GaloisRep`, `charFrob`, `IsUnramifiedAt`/`IsFlatAt` through
`IsHardlyRamified`) and sorried with its literature route recorded:

* **Mazur representability**
  (`exists_weaklyUniversal_hardlyRamifiedDeformation`): the hardly
  ramified deformation problem of an irreducible residual `ρbar` has
  a weakly universal object `(Runiv, ρuniv, πuniv)` in Mazur's
  category — a complete Noetherian local topological `ℤ_p`-algebra —
  through which every hardly ramified deformation over a
  module-finite local `ℤ_p`-algebra factors on Frobenius traces.
  PROVEN 2026-07-24 over two sorried leaves, mirroring `Lift.lean`'s
  accepted decomposition of its parallel (downstream) stratum: the
  strict representability leaf
  `exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation`
  (Mazur/Ramakrishna/CDT proper, factoring residually identified
  deformations) and the Chebotarev–Brauer–Nesbitt conjugacy leaf
  `exists_conj_of_charFrob_eq_away`; the upgrade glue — automatic
  continuity and `ℤ_p`-rigidity of the reduction maps, determinant
  pinning of the constant `charFrob` coefficient, monic-quadratic
  reconstruction from the trace datum — is proven in this module.
* **Carayol trace generation — the surjection `R_univ ↠ 𝕋`**
  (`surjective_ringHom_of_charFrob_eq`): every trace-compatible ring
  homomorphism from the universal object to the Hecke-side
  deformation is surjective.
* **Taylor–Wiles patching — `R = 𝕋`**
  (`injective_ringHom_of_isWeaklyUniversal`): every trace-compatible
  ring homomorphism from a weakly universal object to the Hecke-side
  deformation is injective.

The assembly (pillar 3b's proof, in `Modularity/Interface.lean`)
classifies both the Hecke package `(T, ρT, π)` and `ρ` itself by maps
out of `Runiv` (two instances of the weak-universality clause),
upgrades the `T`-side classifying map to a ring isomorphism
`Runiv ≃+* T` by the two pillars above, and takes `Φ` to be the
composite `T ≃+* Runiv →+* R`.

## Vocabulary, and its relation to `HardlyRamified/Lift.lean`

`Lift.lean` already develops a hardly ramified deformation vocabulary
(`HardlyRamifiedDeformation`, `IsUniversal`/`IsWeaklyUniversal`,
`IsTraceGenerated`, Mazur representability at `ℓ ≥ 5`) — but for the
residual coefficient field `ZMod ℓ` only and, decisively, DOWNSTREAM
of this module's consumer: `Lift.lean` imports `Family.lean`, which
imports `Modularity/Interface.lean`.  The circularity guard on pillar
3b ("never through `Family.lean`") is therefore structural — reusing
that vocabulary would be an import cycle — and this module states the
parallel vocabulary UPSTREAM (importing only `HardlyRamified/Defs`),
generalized from `ZMod ℓ` to the abstract finite residue fields the
interface's Taylor–Wiles section quantifies over.  The statement
shapes (the compatibility triple `ℤ_p`-structure/reduction/`charFrob`,
the weak-universality clause) are aligned with `Lift.lean`'s so that
a future de-duplication can identify the two developments.

## Design notes (SOUNDNESS AUDIT, 2026-07-24)

* **Trace-only compatibility.**  All reduction and factorization
  clauses carry only the LINEAR `charFrob` coefficient (the trace up
  to sign), matching the Taylor–Wiles section's convention, and each
  clause holds away from an existentially quantified finite
  exceptional set of places.  Against the full-charpoly convention of
  `Lift.lean` no information is lost: the representations are rank 2,
  `charFrob` is monic of degree 2, and the hardly ramified
  determinant condition pins the constant coefficient to the fixed
  cyclotomic value, so at every good prime the trace determines the
  whole `charFrob`.
* **Module-finite test category.**  Weak universality is tested
  against deformations over module-finite local `ℤ_p`-algebras
  carrying the `ℤ_p`-module topology
  (`HardlyRamifiedFiniteDeformation`) — the exact shape of the
  interface's `R` and `T`.  Classically these are complete Noetherian
  local rings with the `𝔪`-adic topology (mod `p` the ring is
  Artinian local, so `𝔪` is nilpotent mod `p` and the `p`-adic and
  `𝔪`-adic topologies agree; completeness is inherited from `ℤ_p` by
  module-finiteness), hence legitimate test objects of Mazur's
  category — the clause is the restriction of the genuine universal
  property to that subcategory, which is exactly what the assembly
  consumes.
* **Trace-level reduction data.**  A test deformation reduces to
  `ρbar` only trace-by-trace off a finite set (`charFrob_compat`),
  not by an isomorphism of its residual representation with `ρbar`.
  Classically the two are equivalent under the standing residual
  irreducibility: traces off a finite set determine the residual
  semisimplification everywhere (continuity plus Chebotarev density
  plus Brauer–Nesbitt), and a deformation whose residual
  semisimplification is the irreducible `ρbar` can be conjugated into
  an honest lift of `ρbar` (Carayol, *Formes modulaires et
  représentations galoisiennes à valeurs dans un anneau local
  complet*, Contemp. Math. 165 (1994), Théorème 1).
* **Abstract quantification.**  As everywhere in the Taylor–Wiles
  section (see the section docstring in `Interface.lean`), the
  Hecke-side package `(T, ρT, π)` and the universal-side package
  range over ALL data of the stated shape, not only the genuine
  `𝕋_𝔪` and `R_univ` for which the literature proves the pillars.
  Every pillar's hypothesis set includes an IRREDUCIBLE hardly
  ramified residual representation, which the classical chain of the
  section audit (residual modularity → level optimization →
  `S₂(Γ₀(2)) = 0`) shows to be unsatisfiable — so each pillar is
  classically true outright, while its intended discharge
  instantiates the genuine objects, for which it is verbatim the
  cited literature statement.  This both-ways audit is repeated in
  each declaration's docstring.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
-- `IsAdicComplete.of_finite_module`: the `p`-adic completeness of a
-- module-finite `ℤ_p`-algebra, the assembly step of the pro-finite
-- upgrade `isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`
public import Mathlib.RingTheory.Ideal.Quotient.Index
-- `Ideal.finite_quotient_pow`: finiteness of `R/𝔪ⁿ` for a Noetherian
-- local ring with finite residue field — the finiteness of the
-- classifying sets of that upgrade
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nakayama
-- `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`: properness of the
-- tower ideals `pⁿ⁺¹A`
public import Mathlib.RingTheory.Artinian.Module
-- `isArtinian_of_finite`, whence nilpotence of the maximal ideal of a
-- finite local ring
public import Mathlib.NumberTheory.Padics.RingHoms
-- `PadicInt.toZModPow`/`ker_toZModPow`: finiteness of `ℤ_p/pⁿ`
public import Mathlib.CategoryTheory.CofilteredSystem
-- `nonempty_sections_of_finite_inverse_system`: König's lemma, the
-- compactness step of the pro-finite upgrade
public import Mathlib.Topology.Algebra.Algebra
-- `Subalgebra.topologicalClosure`, in the statement of the Carayol
-- generation leaf `topologicalClosure_adjoin_charFrobCoeff_eq_top`
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
-- the power-series plumbing behind the Auslander–Buchsbaum endgame:
-- `MvPowerSeries.renameEquiv` (reindexing along `Fin (n+1) ≃ Option (Fin n)`),
-- `Finsupp.optionElim`/`Finsupp.some` (the exponent currying), Noetherianity
-- of `B⟦X⟧` and the unit criterion `PowerSeries.isUnit_iff_constantCoeff`
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Data.Finsupp.Option
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Fermat.FLT.Mathlib.RingTheory.PowerSeries.AdicComplete
-- `PowerSeriesAdicComplete.isPrecomplete_mvPowerSeries` /
-- `isNoetherianRing_mvPowerSeries` / `isPrecomplete_of_surjective`: the
-- Mazur-category ring clauses of the Schlessinger cut, read off the de
-- Smit–Lenstra presentation `ℤ_p[[x₁, …, x_g]] ↠ Runiv`
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.DualNumber
-- `DualNumber k`, the tangent carrier of the FOUNDER cut of strict
-- Mazur representability (tangent space as dual-number lifts)
public import Mathlib.Topology.Instances.TrivSqZeroExt
-- the product topology and topological-ring structure on `k[ε]`
public import Mathlib.LinearAlgebra.TensorProduct.Tower
-- `LinearEquiv.baseChange`, in the statement of the conjugation
-- transport `baseChange_conj_apply`
public import Mathlib.LinearAlgebra.Dimension.Free
-- `Module.finBasisOfFinrankEq`: the standard frame of `reframe`
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
-- `LinearEquiv.charpoly_conj`: conjugation-invariance of `charFrob`
public import Mathlib.RingTheory.Depth.Rees
-- the Rees theorem `ModuleCat.exists_isRegular_tfae` (Ext-vanishing ↔
-- existence of regular sequences in an ideal): the depth engine of the
-- Auslander–Buchsbaum instance behind patching leaf 3
public import Mathlib.RingTheory.Regular.Free
-- `Module.free_quotSMulTop_iff_free`: the Nakayama dévissage lifting
-- freeness through the quotient by a regular element
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
-- finiteness of the set of associated primes, feeding the Davis coset
-- prime-avoidance step of the Auslander–Buchsbaum induction
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
-- Noetherianity of quotient rings (instance), for the dimension
-- induction over `R ↝ R/(x)`
public import Mathlib.LinearAlgebra.Basis.VectorSpace
-- `Module.Free.of_divisionRing`: the dimension-zero base case
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.NumberTheory.Padics.ProperSpace
-- the `CompactSpace ℤ_[p]` instance behind closedness of `ψ`'s range
public import Mathlib.Topology.Algebra.Module.Compact
-- `Submodule.isCompact_of_fg`: f.g. submodules over a compact ring are
-- compact
public import Mathlib.RingTheory.Finiteness.Cardinality
-- `Module.Finite.exists_fin'`: the module-finiteness surjection ℤ_pⁿ ↠ T
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Basic
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `globalFrob`, `dense_conjClasses_globalFrob`,
-- `exists_prime_toHeightOneSpectrum`, `charFrob_eq_charpoly_globalFrob`:
-- the Chebotarev/continuity step of the Carayol generation proof
public import Fermat.FLT.GaloisRepresentation.BrauerNesbittConjugacy
-- proof-only: the SHARED Chebotarev–Brauer–Nesbitt conjugacy node
-- discharging `exists_conj_of_charFrob_eq_away` below (same node also
-- discharges `HardlyRamified/Deformation.lean`'s `{2, ℓ}` twin)
public import Mathlib.LinearAlgebra.Trace
-- `LinearMap.trace`: the continuous linear functional behind `coeff 1`
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- `Matrix.trace_eq_neg_charpoly_coeff`: the trace/`coeff 1` bridge
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree
-- proof-only: `IsHardlyRamified.mod_three_reducible` (the
-- Fontaine/Odlyzko discriminant-bound route), the `p = 3` horn of the
-- odd-prime dichotomy discharging the Hecke generation leaf
-- `topologicalClosure_adjoin_charFrobCoeff_univ_eq_top` below
public import Fermat.FLT.Slop.RepresentationTheory.OddAbsIrredSlop
-- proof-only: `Slop.OddRep.isIrreducible_iff_forall`, unpacking
-- `Representation.IsIrreducible` into the stable-submodule form
-- consumed by the `p = 3` horn
public import Fermat.FLT.Modularity.KhareWintenberger
-- proof-only: `not_isIrreducible_of_isHardlyRamified_of_five_le`, the
-- Family-free Khare–Wintenberger headline — the `p ≥ 5` horn of the
-- same dichotomy
public import Mathlib.FieldTheory.Galois.Infinite
-- `IntermediateField.fixingSubgroup`/`fixedField` in the statements of
-- the Hermite–Minkowski cut of `finite_setOf_isHardlyRamified`, and the
-- `InfiniteGalois` correspondence (`fixingSubgroup_fixedField`,
-- `isOpen_iff_finite`, `normal_iff_isGalois`, `normalAutEquivQuotient`)
-- in its proofs
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
-- `NumberField.discr` in the statement of the discriminant-exponent
-- leaf `exists_discr_factorization_le_of_finrank_le`, and the Hermite
-- theorem `NumberField.finite_of_discr_bdd` in the proofs
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- proof-only: `NumberField.not_dvd_discr_iff_forall_mem`, the
-- unramified-implies-coprime-to-discriminant dictionary
public import Mathlib.NumberTheory.RamificationInertia.Basic
-- `Ideal.ramificationIdx_le_finrank`, the `e ≤ [L:K]` bound used in
-- `differentIdeal_exponent_le`'s consumer.  This used to arrive
-- transitively; it stopped doing so under the module system (a
-- transitive `public import` upstream became private), which showed up
-- as `Unknown constant Ideal.ramificationIdx_le_finrank`.  Naming it
-- here makes the file independent of that chain.
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
-- `Ideal.Quotient.factorPow`: the transition maps `R ⧸ I ^ m → R ⧸ I ^ n`
-- of the `p`-adic quotient tower in the pro-finite limit upgrade
public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
-- `IsAdicComplete.of_finite_module`: `𝔪`-adic completeness of a
-- module-finite algebra over `ℤ_p`, the completeness half of the
-- pro-finite limit upgrade
public import Mathlib.CategoryTheory.CofilteredSystem
-- proof-only: `nonempty_sections_of_finite_inverse_system` (Kőnig), the
-- compactness step assembling a compatible system of level-`n`
-- classifying maps
public import Fermat.FLT.Modularity.PatchingVendored.System
-- the vendored FLT abstract patching development (`PatchingAlgebra`,
-- `PatchingModule`, `quotientToOver`, `quotientEquivOver`, `smulData`,
-- `smul_lemma`), instantiated by `exists_patchedModule_of_fields` below
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
-- the scoped product topology on `MvPowerSeries`, in which
-- `Λ = ℤ_p[[x₁, …, x_q]]` is profinite (hence `IsAdicTopology` is free)
public import Mathlib.RingTheory.MvPowerSeries.Inverse
-- `IsLocalRing (MvPowerSeries σ R)` for a local coefficient ring
public import Mathlib.RingTheory.Regular.Flat
-- `IsWeaklyRegular.isWeaklyRegular_rTensor`: a `Λ`-regular sequence is
-- `M`-regular for flat (in particular free) `M`
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Connected.TotallyDisconnected
-- proof-only, and easy to miss: without these two the route
-- `IsUltrametricDist ℤ_[p] → TotallySeparatedSpace → TotallyDisconnectedSpace`
-- is unavailable and `TotallyDisconnectedSpace ℤ_[p]` fails to synthesize
-- with no hint of the cause

@[expose] public section

namespace GaloisRepresentation.Modularity

open IsDedekindDomain
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` commutes with base change** (PROVEN): the Frobenius
characteristic polynomial of `ρ.baseChange B` at a finite place is the
image under `algebraMap A B` of that of `ρ`.  Unfolds `charFrob` to
the charpoly of the localized representation at the arithmetic
Frobenius, identifies the base-changed endomorphism with
`LinearMap.baseChange` (definitional through the exposed module
exports), and finishes by mathlib's `LinearMap.charpoly_baseChange`.
This is the bridge that lets the pillar-3b assembly present the
`p`-adic representation `ρ` itself as a deformation of its own
residual representation `ρ.baseChange kk`: the reduction datum
`algebraMap R kk ∘ (coeff 1 of charFrob ρ) = coeff 1 of charFrob
(ρ.baseChange kk)` holds at EVERY place, with empty exceptional set.
(`Family.lean` proves the conjugated variant `charFrob_baseChange_conj`
by the same route; it lives downstream of this module's consumer and
cannot be imported here.) -/
lemma charFrob_baseChange {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) :
    (ρ.baseChange B).charFrob v = (ρ.charFrob v).map (algebraMap A B) := by
  show ((ρ.baseChange B).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
    ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).map
      (algebraMap A B)
  rw [show (ρ.baseChange B).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      LinearMap.baseChange B (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) from rfl,
    LinearMap.charpoly_baseChange]

/-!
## `p`-adic coefficient glue (PROVEN)

The residual coefficient field `k` of the Taylor–Wiles section is an
abstract finite field carrying a `ℤ_p`-algebra structure.  Three
elementary facts about such fields drive the assembly of Mazur
representability below: any ring homomorphism `ℤ_p →+* k` forces
`k` to have characteristic `p` (the kernel is a nonzero prime of the
DVR `ℤ_p`, necessarily `(p)`); any two ring homomorphisms
`ℤ_p →+* k` coincide (both kill `p` and agree on the dense first
digit `x.appr 1`); and any ring homomorphism `ℤ_p →+* k` into the
discrete `k` is continuous (it is constant on cosets of the open
ideal `(p) = ball 0 1`).  These are what make the reduction maps of
`HardlyRamifiedFiniteDeformation`s automatically continuous and
`ℤ_p`-compatible.
-/

/-- **A finite field receiving `ℤ_p` has characteristic `p`** (PROVEN):
the kernel of a ring homomorphism `f : ℤ_p →+* k`, `k` a finite field,
is a nonzero ideal (else the infinite `ℤ_p` embeds in the finite `k`)
that is prime (the target is a domain), hence — by the DVR ideal
classification of `ℤ_p` — contains `p`; so `(p : k) = 0` and the
characteristic, a prime dividing `p`, is `p` itself. -/
lemma charP_of_ringHom_padicInt {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] (f : ℤ_[p] →+* k) : CharP k p := by
  have hker : RingHom.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := by
      rw [RingHom.injective_iff_ker_eq_bot]
      exact hbot
    haveI := Finite.of_injective f hinj
    exact not_finite ℤ_[p]
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hpmem : (p : ℤ_[p]) ∈ RingHom.ker f := by
    have hpow : (p : ℤ_[p]) ^ n ∈ RingHom.ker f := by
      rw [hn]
      exact Ideal.mem_span_singleton_self _
    exact (RingHom.ker_isPrime f).mem_of_pow_mem n hpow
  have hpk : (p : k) = 0 := by
    rw [RingHom.mem_ker, map_natCast] at hpmem
    exact hpmem
  have hdvd : ringChar k ∣ p := (CharP.cast_eq_zero_iff k (ringChar k) p).mp hpk
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · exact absurd
      (show (1 : k) = 0 by
        rw [← Nat.cast_one, ← h1]
        exact CharP.cast_eq_zero k (ringChar k))
      one_ne_zero
  · exact ringChar.of_eq hp

/-- **Rigidity of `ℤ_p`-points of a finite field** (PROVEN): any two
ring homomorphisms `ℤ_p →+* k` into a finite field agree.  Both kill
`p` (`k` has characteristic `p` by `charP_of_ringHom_padicInt`), and
every `x : ℤ_p` is `x.appr 1 + p·z` with `x.appr 1 : ℕ`, on which any
ring homomorphism is the natural-number cast.  This is what turns the
`ℤ_p`-structure compatibility `π ∘ algebraMap = algebraMap` of the
deformation vocabulary into a theorem rather than a datum. -/
lemma ringHom_padicInt_eq {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] (f g : ℤ_[p] →+* k) : f = g := by
  haveI := charP_of_ringHom_padicInt f
  ext x
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
    (by simpa using PadicInt.appr_spec 1 x)
  have hx : x = (x.appr 1 : ℤ_[p]) + (p : ℤ_[p]) * c := by
    rw [← hc]
    ring
  rw [hx]
  simp

/-- **Automatic continuity into a discrete finite field** (PROVEN): a
ring homomorphism `ℤ_p →+* k`, `k` a finite discrete field, is
continuous — it kills the ideal `(p)`, which is the open unit ball of
`ℤ_p`, so it is locally constant. -/
lemma continuous_ringHom_padicInt {p : ℕ} [Fact p.Prime] {k : Type*}
    [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    (f : ℤ_[p] →+* k) : Continuous f := by
  haveI := charP_of_ringHom_padicInt f
  have hopen : IsOpen ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    have hball : ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.ball (0 : ℤ_[p]) 1 := by
      ext x
      simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Metric.mem_ball,
        dist_zero_right]
      exact (PadicInt.norm_lt_one_iff_dvd x).symm
    rw [hball]
    exact Metric.isOpen_ball
  apply continuous_of_continuousAt_zero f
  unfold ContinuousAt
  rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
  filter_upwards [hopen.mem_nhds (Submodule.zero_mem _)] with x hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
  rw [hc, map_mul, map_natCast, CharP.cast_eq_zero k p, zero_mul]

/-!
## Frobenius characteristic-polynomial glue (PROVEN)

`charFrob` at a rank-2 representation is monic of degree 2, and for a
hardly ramified representation its constant coefficient is pinned to
the fixed cyclotomic value by the determinant condition — so at every
finite place the LINEAR coefficient (the trace datum carried by the
deformation vocabulary of this module) determines the whole
polynomial.  This is the audit note of the module docstring made into
lemmas: it upgrades the trace-level reduction data of a test
deformation to full `charFrob` matching, the input the
Chebotarev–Brauer–Nesbitt conjugacy leaf consumes.
-/

/-- **Two monic quadratics with equal lower coefficients are equal**
(PROVEN, elementary): coefficientwise, degrees `0` and `1` are the
hypotheses, degree `2` is monicity, and everything above is zero. -/
lemma monic_natDegree_two_ext {R : Type*} [Semiring R] {P Q : Polynomial R}
    (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = 2)
    (hQd : Q.natDegree = 2) (h0 : P.coeff 0 = Q.coeff 0)
    (h1 : P.coeff 1 = Q.coeff 1) : P = Q := by
  ext n
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 =>
    have hP2 : P.coeff 2 = 1 := by
      have h := hP.coeff_natDegree
      rwa [hPd] at h
    have hQ2 : Q.coeff 2 = 1 := by
      have h := hQ.coeff_natDegree
      rwa [hQd] at h
    rw [hP2, hQ2]
  | (m + 3) =>
    rw [P.coeff_eq_zero_of_natDegree_lt (by rw [hPd]; omega),
      Q.coeff_eq_zero_of_natDegree_lt (by rw [hQd]; omega)]

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` is monic** (PROVEN): it is a characteristic
polynomial. -/
lemma charFrob_monic {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) : (ρ.charFrob v).Monic := by
  show ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).Monic
  exact LinearMap.charpoly_monic _

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` of a rank-2 representation has degree 2** (PROVEN):
the characteristic polynomial of an endomorphism of a finite free
rank-2 module has degree the rank. -/
lemma charFrob_natDegree {A : Type*} [CommRing A] [Nontrivial A]
    [TopologicalSpace A] [IsTopologicalRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Free A M]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) (hdim : Module.rank A M = 2) :
    (ρ.charFrob v).natDegree = 2 := by
  show ((ρ.toLocal v
    (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).natDegree = 2
  rw [LinearMap.charpoly_natDegree]
  exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)

set_option backward.isDefEq.respectTransparency false in
/-- **The determinant pins the constant `charFrob` coefficient of a
hardly ramified representation** (PROVEN): at every finite place `v`,
the constant coefficient of `charFrob` — which is `(-1)² · det = det`
of the Frobenius endomorphism on the rank-2 module — is the image
under `algebraMap ℤ_p` of the cyclotomic-character value at the
(fixed, coefficient-ring-independent) global Galois element underlying
the arithmetic Frobenius at `v`.  Hence two hardly ramified
representations linked by a ring homomorphism compatible with the
`ℤ_p`-structures match constant `charFrob` coefficients EVERYWHERE —
the trace-determines-`charFrob` audit point of the module docstring,
stated directly in the transported two-representation form the
assembly consumes. -/
lemma coeff_zero_charFrob_eq_of_isHardlyRamified {p : ℕ} {hpodd : Odd p}
    [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] {hdim : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified hpodd hdim ρ)
    {k : Type*} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    [IsLocalRing k] [Algebra ℤ_[p] k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {hW : Module.rank k W = 2} {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (f : R →+* k) (hf : f.comp (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] k)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    f ((ρ.charFrob v).coeff 0) = (ρbar.charFrob v).coeff 0 := by
  have hfinR : Module.finrank R V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hdim)
  have hfink : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hdetR := LinearMap.det_eq_sign_charpoly_coeff
    (ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v))
  have hdetk := LinearMap.det_eq_sign_charpoly_coeff
    (ρbar.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v))
  rw [hfinR] at hdetR
  rw [hfink] at hdetk
  show f (((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0) =
    ((ρbar.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0
  have hcR : ((ρ.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0 =
      LinearMap.det (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) := by
    rw [hdetR]
    ring
  have hck : ((ρbar.toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly).coeff 0 =
      LinearMap.det (ρbar.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) := by
    rw [hdetk]
    ring
  rw [hcR, hck, GaloisRep.toLocal_apply, GaloisRep.toLocal_apply,
    ← GaloisRep.det_apply, ← GaloisRep.det_apply, hρ.det, hρbar.det,
    ← RingHom.comp_apply, hf]

set_option linter.checkUnivs false in
/-- **A hardly ramified deformation of `ρbar` over a module-finite
local `ℤ_p`-algebra** — the test objects of the weak-universality
clause of Mazur representability, and simultaneously the common shape
of the two deformations the pillar-3b assembly classifies (the
interface's `p`-adic representation `ρ` over `R` and its Hecke-side
package `ρT` over `T`).  The data: a coefficient ring `A` that is a
local topological `ℤ_p`-algebra, module-finite over `ℤ_p` and carrying
the `ℤ_p`-module topology (classically: a complete Noetherian local
ring with finite residue field, with its `𝔪`-adic topology — see the
module docstring's audit); a free rank-2 module `Vd` over it; a hardly
ramified representation on `Vd`; and a surjective reduction map
`π : A →+* k` to the residual coefficient field carrying the linear
`charFrob` coefficients of `ρ` to those of `ρbar` away from a finite
exceptional set (`π` is automatically local: its kernel is a maximal
ideal of the local ring `A`, hence THE maximal ideal, so `A/𝔪 ≅ k`).
This is the interface-side counterpart of `Lift.lean`'s
`HardlyRamifiedDeformation` (which lives in Mazur's full category,
over `ZMod ℓ`, downstream of this module's consumer — see the module
docstring).

(The `checkUnivs` linter is disabled: the coefficient-ring universe
`s` and the module universe `t` are deliberately independent — the
pillar-3b assembly instantiates the structure at `(u, u)` for the
standard-framed Hecke side and at `(u, v)` for the interface's
abstract rank-2 module `V : Type v` — and a structure bundling a
`Type s` and a `Type t` field intrinsically lives in a `max`-only
sort.) -/
structure HardlyRamifiedFiniteDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) where
  /-- The coefficient ring of the deformation. -/
  A : Type s
  [commRing : CommRing A]
  [topologicalSpace : TopologicalSpace A]
  [isTopologicalRing : IsTopologicalRing A]
  [isLocalRing : IsLocalRing A]
  [algebra : Algebra ℤ_[p] A]
  [moduleFinite : Module.Finite ℤ_[p] A]
  [isModuleTopology : IsModuleTopology ℤ_[p] A]
  /-- The underlying module of the deformation. -/
  Vd : Type t
  [addCommGroup : AddCommGroup Vd]
  [module : Module A Vd]
  [moduleFiniteVd : Module.Finite A Vd]
  [moduleFreeVd : Module.Free A Vd]
  /-- The module has rank 2. -/
  rank_eq : Module.rank A Vd = 2
  /-- The deformed representation. -/
  ρ : GaloisRep ℚ A Vd
  /-- The deformation is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hpodd rank_eq ρ
  /-- The reduction map to the residual coefficient ring. -/
  π : A →+* k
  /-- The reduction map is surjective (so `A` has residue field `k`). -/
  π_surjective : Function.Surjective π
  /-- The finite exceptional set of the reduction datum. -/
  S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  /-- The deformation reduces to `ρbar`: the linear `charFrob`
  coefficients (the Frobenius traces up to sign) match through `π`
  away from the exceptional set. -/
  charFrob_compat : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    π ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
      (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Continuity of the reduction map** (PROVEN): the reduction map
`π : A →+* k` of a hardly ramified finite deformation is continuous
when the residual field is finite and discrete.  The coefficient ring
carries the `ℤ_p`-module topology, so any ring homomorphism out of it
whose restriction to `ℤ_p` is continuous is continuous
(`IsModuleTopology.continuous_of_ringHom`), and `π ∘ algebraMap` is a
ring homomorphism `ℤ_p →+* k`, continuous by
`continuous_ringHom_padicInt`.  (Ingredient of the
residual-identification vocabulary below: it makes `k` a topological
`A`-algebra, so the reduction of `D.ρ` can be formed by `baseChange` —
the same role `continuous_pi` plays in `Lift.lean`'s parallel,
downstream vocabulary.) -/
lemma HardlyRamifiedFiniteDeformation.continuous_pi.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) :
    letI := D.commRing
    letI := D.topologicalSpace
    Continuous D.π := by
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.algebra
  letI := D.isModuleTopology
  exact IsModuleTopology.continuous_of_ringHom (R := ℤ_[p]) D.π
    (continuous_ringHom_padicInt (D.π.comp (algebraMap ℤ_[p] D.A)))

open scoped TensorProduct in
/-- **Residual identification**: the reduction of `D.ρ` along the
reduction map `D.π` — the base change of `D.ρ` to `k`, a continuous
`D.A`-algebra via `continuous_pi` — is conjugate to `ρbar` itself.
This is the datum with which Mazur-style strict-deformation
universality can be applied to `D`: the
`HardlyRamifiedFiniteDeformation` vocabulary matches `D` with `ρbar`
only through linear `charFrob` coefficients off a finite set
(`charFrob_compat`), and the Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq_away` upgrades that matching to an actual
conjugation whenever `ρbar` is irreducible.  Interface-side
counterpart of `Lift.lean`'s `IsResidualIdentified` (which lives over
`ZMod ℓ`, downstream of this module's consumer). -/
def HardlyRamifiedFiniteDeformation.IsResidualIdentified.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) : Prop :=
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  letI : Algebra D.A k := D.π.toAlgebra
  letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
  ∃ e : (k ⊗[D.A] D.Vd) ≃ₗ[k] W, (D.ρ.baseChange k).conj e = ρbar

/-- **The weak-universality clause** (the existence half of Mazur
universality, at trace level): every hardly ramified deformation of
`ρbar` over a module-finite local `ℤ_p`-algebra (with rank-2 module in
`Type t`) receives a ring homomorphism `ψ` from `Runiv` that is
compatible with the `ℤ_p`-algebra structures, intertwines the two
reduction maps, and carries the linear `charFrob` coefficients of the
universal representation `ρuniv` to those of the deformation away from
a finite exceptional set.  This is `Lift.lean`'s `IsWeaklyUniversal`
transported to the interface's vocabulary (abstract finite residual
field, trace-level compatibility, module-finite test category — see
the module docstring for the audit of each change).  Classically, for
the genuine universal deformation ring of an irreducible `ρbar` the
clause holds with `ψ` the classifying map of the test deformation
(Mazur; the trace compatibility is the definitional compatibility of
the classifying map with the universal representation, read off on
traces, which are conjugation-invariant — this is where residual
irreducibility kills the framing).  Uniqueness of `ψ` (Carayol trace
generation of `Runiv`) is deliberately NOT part of the clause: the
pillar-3b assembly never needs it, and keeping the clause existential
keeps pillar 1 exactly the representability statement. -/
def IsWeaklyUniversalDeformation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar,
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∃ ψ : Runiv →+* D.A,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] D.A ∧
      D.π.comp ψ = πuniv ∧
      ∃ Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
          ψ ((ρuniv.charFrob
              hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Weak universality on residually identified deformations**: the
package `(Runiv, ρuniv, πuniv)` factors every test deformation `D`
that comes EQUIPPED with a residual identification — a conjugation of
its reduction onto `ρbar`.  This is what Mazur-style strict-deformation
representability produces directly (the classifying map exists for
deformations whose reduction is identified with `ρbar`), without the
Chebotarev–Brauer–Nesbitt input, which is exactly what upgrades this
clause to full `IsWeaklyUniversalDeformation` in the proven assembly
`isWeaklyUniversal_of_isWeaklyUniversalOnIdentified` below.
Interface-side counterpart of `Lift.lean`'s
`IsWeaklyUniversalOnIdentified`. -/
def IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar,
    D.IsResidualIdentified →
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∃ ψ : Runiv →+* D.A,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] D.A ∧
      D.π.comp ψ = πuniv ∧
      ∃ Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
          ψ ((ρuniv.charFrob
              hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-- **Chebotarev–Brauer–Nesbitt conjugacy leaf** (PROVEN 2026-07-24 —
the identification half of the Mazur representability pillar): a
continuous representation `τ` of `Gal(ℚ̄/ℚ)` on a 2-dimensional space
over a finite discrete field `k` whose Frobenius characteristic
polynomials agree with those of an *irreducible* 2-dimensional `ρbar`
at all primes outside a finite exceptional set `S` is conjugate to
`ρbar`. DERIVED verbatim from the SHARED conjugacy node
`GaloisRepresentation.exists_conj_of_charFrob_eq_away`
(`BrauerNesbittConjugacy.lean`) — the single node that also discharges
`HardlyRamified/Deformation.lean`'s `{2, ℓ}` twin
`exists_conj_of_charFrob_eq`, resolving the dedupe deferred below.

Mathematical content: by Chebotarev density the Frobenius conjugacy
classes at the places outside ANY finite set are dense in the Galois
group (`Chebotarev.lean`'s density node; removing the finitely many
classes of `S` does not affect density, since the argument produces
infinitely many places in each open conjugacy-stable set); `τ` and
`ρbar` are continuous into the discrete finite endomorphism spaces, so
the agreement set of the two characteristic polynomials is closed and
conjugation-stable, hence everything.  By Brauer–Nesbitt (valid over
any field when full characteristic polynomials — not just traces —
agree) the semisimplifications are then isomorphic; `ρbar` is
irreducible of full dimension 2, so the semisimplification of `τ` is
irreducible, hence `τ` itself is irreducible and isomorphic to `ρbar`,
and an intertwining isomorphism is the required conjugation (Carayol,
Contemp. Math. 165 (1994), Théorème 1, in the trivial
residual-coefficient case; Diamond–Darmon–Taylor, *Fermat's Last
Theorem* (1995), Lemma 3.27 for the standard argument).  This is
`Lift.lean`'s `exists_conj_of_charFrob_eq` generalized from `ZMod ℓ`
to an abstract finite coefficient field and from the fixed exceptional
set `{2, ℓ}` to an arbitrary finite one — `Lift.lean` is downstream of
this module's consumer, so the statement is restated here upstream
(dedupe deferred until the import cycle is broken).

Both-ways audit: the statement quantifies over abstract `τ`, `ρbar`
with no hardly-ramified hypothesis, and is the plain classical
Chebotarev–Brauer–Nesbitt statement — true outright, no vacuity
needed. -/
theorem exists_conj_of_charFrob_eq_away.{uK, uW, uW'}
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep ℚ k W')
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar :=
  _root_.GaloisRepresentation.exists_conj_of_charFrob_eq_away
    hW hirr hW' τ S hcf

/-!
## Conjugation and reframing transport (PROVEN)

The two universality clauses of the strict Mazur representability
statement differ only in the universe of the test deformation's
module.  The transport cluster below collapses them to the
standard-framed clause: `charFrob`, hardly-ramifiedness and residual
identifications are all conjugation-invariant, so every test
deformation `D` may be *reframed* — replaced by the deformation on
`Fin 2 → D.A` obtained by conjugating with a basis isomorphism of its
rank-2 module (`Module.finBasisOfFinrankEq`) — without changing its
coefficient ring, reduction map, exceptional set or `charFrob` data.
A package that factors all standard-framed identified deformations
therefore factors all identified deformations at EVERY module universe
(`isWeaklyUniversalOnIdentifiedDeformation_of_reframe`).
(`isHardlyRamified_conj` restates `Deformation.lean`'s same-named
proof across two module universes — that module's version constrains
both modules to a single universe, which the reframing step here
inherently crosses; dedupe when a universe-polymorphic home is
factored out.)
-/

set_option backward.isDefEq.respectTransparency false in
/-- **`charFrob` is conjugation-invariant** (PROVEN): conjugating a
representation by a linear isomorphism of its module conjugates each
Frobenius endomorphism, and characteristic polynomials are invariant
under conjugation (`LinearEquiv.charpoly_conj`). -/
lemma charFrob_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) (e : M ≃ₗ[A] N) :
    (ρ.conj e).charFrob v = ρ.charFrob v := by
  show ((ρ.conj e).toLocal v
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly =
    ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).charpoly)
  rw [show (ρ.conj e).toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v) =
      (LinearEquiv.conj e) (ρ.toLocal v
        (Field.AbsoluteGaloisGroup.adicArithFrob v)) from rfl,
    LinearEquiv.charpoly_conj]

set_option backward.isDefEq.respectTransparency false in
/-- **Hardly-ramifiedness transfers along conjugation**, across module
universes (PROVEN — the two-universe restatement of
`Deformation.lean`'s `isHardlyRamified_conj`, whose proof it repeats
verbatim; see the section docstring): the determinant is
conjugation-invariant, the kernels of the local representations only
grow, flatness transports through `HasFlatProlongationAt.of_equiv`
along the base-changed isomorphism, and the tame quadratic quotient at
`2` is composed with the inverse isomorphism. -/
lemma isHardlyRamified_conj {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep ℚ R M} (h : IsHardlyRamified hpodd hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsHardlyRamified hpodd hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness: the kernel of the local representation only grows
    intro q hq hqq
    have hun := h.isUnramified q hq hqq
    refine ⟨le_trans hun.localInertiaGroup_le ?_⟩
    intro σ hσ
    have h1 : ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat σ = 1 := hσ
    show (ρ.conj e).toLocal hq.toHeightOneSpectrumRingOfIntegersRat σ = 1
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
            (Fact.out : p.Prime)) g) x) =
      (((ρ.conj e).baseChange (R ⧸ I)).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : p.Prime)) g)
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
/-- **Base change intertwines conjugation** (PROVEN, pointwise): the
base change of a conjugated representation acts through the base
change of the conjugating isomorphism.  The elementary tensor
computation consumed by the residual-identification transport
`HardlyRamifiedFiniteDeformation.IsResidualIdentified.reframe`. -/
lemma baseChange_conj_apply {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Free A N]
    (ρ : GaloisRep ℚ A M) (e : M ≃ₗ[A] N)
    (σ : Field.absoluteGaloisGroup ℚ) (x : B ⊗[A] M) :
    ((ρ.conj e).baseChange B) σ (LinearEquiv.baseChange A B M N e x) =
      LinearEquiv.baseChange A B M N e ((ρ.baseChange B) σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c m =>
    simp only [GaloisRep.baseChange_tmul, LinearEquiv.baseChange_tmul,
      GaloisRep.conj_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]

/-- The standard rank-2 free module `Fin 2 → O` has rank 2 (the
`Modularity` copy of `Deformation.lean`'s `rank_finTwoFun`, restated so
that this module's project imports stay at `HardlyRamified/Defs` +
`Chebotarev`; dedupe with the transport cluster above). -/
lemma rank_finTwoFun (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The standard frame of a test deformation's module** (PROVEN): a
basis isomorphism `D.Vd ≃ₗ[D.A] (Fin 2 → D.A)`, from
`Module.finBasisOfFinrankEq` at the rank-2 datum of the structure.
Extracted as a definition so that `reframe` below and the residual
identification transport refer to the SAME isomorphism. -/
noncomputable def HardlyRamifiedFiniteDeformation.reframeEquiv.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) :
    letI := D.commRing
    letI := D.addCommGroup
    letI := D.module
    D.Vd ≃ₗ[D.A] (Fin 2 → D.A) :=
  letI := D.commRing
  letI := D.isLocalRing
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  (Module.finBasisOfFinrankEq D.A D.Vd
    (Module.finrank_eq_of_rank_eq (by exact_mod_cast D.rank_eq))).equivFun

set_option backward.isDefEq.respectTransparency false in
/-- **Reframing a test deformation onto the standard frame** (PROVEN):
the hardly ramified deformation with the same coefficient ring, module
`Fin 2 → D.A`, representation `D.ρ.conj D.reframeEquiv`, and unchanged
reduction data — legitimate by conjugation-invariance of
hardly-ramifiedness (`isHardlyRamified_conj`) and of `charFrob`
(`charFrob_conj`).  This is what collapses the module universe `t` of
the weak-universality clauses onto the coefficient universe `s`. -/
noncomputable def HardlyRamifiedFiniteDeformation.reframe.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    (D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar) :
    HardlyRamifiedFiniteDeformation.{s, s, uK, uW} hpodd ρbar :=
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.moduleFinite
  letI := D.isModuleTopology
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  { A := D.A
    Vd := Fin 2 → D.A
    rank_eq := rank_finTwoFun D.A
    ρ := D.ρ.conj D.reframeEquiv
    isHardlyRamified :=
      isHardlyRamified_conj (rank_finTwoFun D.A) D.isHardlyRamified
        D.reframeEquiv
    π := D.π
    π_surjective := D.π_surjective
    S := D.S
    charFrob_compat := fun q hq hqS => by
      rw [charFrob_conj]
      exact D.charFrob_compat q hq hqS }

set_option backward.isDefEq.respectTransparency false in
/-- **Residual identifications transport along reframing** (PROVEN):
compose the inverse base change of the framing isomorphism with the
given identification; the elementary-tensor intertwining
`baseChange_conj_apply` does the rest. -/
lemma HardlyRamifiedFiniteDeformation.IsResidualIdentified.reframe.{s, t, uK, uW}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    {D : HardlyRamifiedFiniteDeformation.{s, t, uK, uW} hpodd ρbar}
    (hD : D.IsResidualIdentified) :
    D.reframe.IsResidualIdentified := by
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  letI : Algebra D.A k := D.π.toAlgebra
  letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
  obtain ⟨e₀, he₀⟩ := hD
  refine ⟨(LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A)
      D.reframeEquiv).symm.trans e₀, ?_⟩
  refine GaloisRep.ext fun σ => LinearMap.ext fun w => ?_
  have hgoal := congrArg (fun τ : GaloisRep ℚ k W => τ σ w) he₀
  simp only [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply] at hgoal
  have hkey := baseChange_conj_apply (B := k) D.ρ D.reframeEquiv σ
    (e₀.symm w)
  show ((LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A)
      D.reframeEquiv).symm.trans e₀)
      (((D.ρ.conj D.reframeEquiv).baseChange k) σ
        (((LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A)
          D.reframeEquiv).symm.trans e₀).symm w)) = ρbar σ w
  have hsymmw : (((LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A)
      D.reframeEquiv).symm.trans e₀).symm w) =
      LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A) D.reframeEquiv
        (e₀.symm w) := rfl
  rw [hsymmw, hkey]
  show e₀ ((LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A)
      D.reframeEquiv).symm
      (LinearEquiv.baseChange D.A k D.Vd (Fin 2 → D.A) D.reframeEquiv
        ((D.ρ.baseChange k) σ (e₀.symm w)))) = ρbar σ w
  rw [LinearEquiv.symm_apply_apply]
  exact hgoal

set_option backward.isDefEq.respectTransparency false in
/-- **Universe transport of identified weak universality** (PROVEN —
the glue of the FOUNDER decomposition of the strict Mazur leaf,
2026-07-24): a package factoring all standard-framed residually
identified test deformations (module universe = coefficient universe
`s`) factors all residually identified test deformations at EVERY
module universe `t`: reframe the test deformation (`reframe`),
transport its identification (`IsResidualIdentified.reframe`), and
read the classifying map back through the conjugation-invariance of
`charFrob` (`charFrob_conj`) — the coefficient ring, reduction map and
exceptional set are unchanged by reframing. -/
theorem isWeaklyUniversalOnIdentifiedDeformation_of_reframe.{s, t, uK, uW, uR}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)} {πuniv : Runiv →+* k}
    (h : IsWeaklyUniversalOnIdentifiedDeformation.{s, s, uK, uW, uR} hpodd
      ρbar ρuniv πuniv) :
    IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv := by
  intro D hDid
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  obtain ⟨ψ, hψalg, hψred, Sψ, hψtr⟩ := h D.reframe hDid.reframe
  refine ⟨ψ, hψalg, hψred, Sψ, fun q hq hqS => ?_⟩
  have ht : ψ ((ρuniv.charFrob
      hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
      ((D.ρ.conj D.reframeEquiv).charFrob
        hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 :=
    hψtr q hq hqS
  rwa [charFrob_conj] at ht

/-!
## The dual-number tangent carrier (the FOUNDER cut, 2026-07-24)

With the module universes collapsed by the reframing transport, the
strict Mazur representability statement is cut along the classical
architecture of the deformation functor: its TANGENT SPACE is the set
of hardly ramified lifts of `ρbar` to the dual numbers `k[ε]`
(functor-of-points form of `H¹_{Σ}(G_{ℚ,{2,p}}, ad ρbar)`, the
subspace of `H¹` cut out by the hardly ramified local conditions);
its FINITENESS — Schlessinger's H3 — is the arithmetic input, isolated
below as the restricted-ramification finiteness statement
`finite_setOf_isHardlyRamified` (Hermite–Minkowski; itself PROVEN
2026-07-24 over the single discriminant-exponent leaf, itself PROVEN
2026-07-25 over the wild different-exponent leaf
`differentIdeal_exponent_le_wild`); everything else —
Schlessinger's H1, H2, H4, the relative representability of the hardly
ramified conditions, and the de Smit–Lenstra presentation
`R_univ = ℤ_p[[x₁,…,x_g]]/(f₁,…,f_m)` in `g = dim` tangent-space
variables that yields the Mazur-category properties (Noetherian,
`𝔪`-adic, complete) — is the deformation-theoretic core leaf
`exists_weaklyUniversalOnIdentified_framed_of_finite_tangent`, which
consumes the tangent finiteness as its sole arithmetic hypothesis.
-/

/-- The dual numbers over a finite ring are finite (the carrier is
definitionally `K × K`). -/
instance {K : Type*} [Finite K] : Finite (DualNumber K) :=
  inferInstanceAs (Finite (K × K))

/-- The dual numbers over a field form a local ring: a dual number is
a unit exactly when its constant term is nonzero
(`TrivSqZeroExt.isUnit_iff_isUnit_fst`), and for any `a` at least one
of `a`, `1 - a` has nonzero constant term. -/
instance {K : Type*} [Field K] : IsLocalRing (DualNumber K) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases hfst : TrivSqZeroExt.fst a = 0
    · refine Or.inr (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_)
      rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, hfst, sub_zero]
      exact isUnit_one
    · exact Or.inl (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
        (isUnit_iff_ne_zero.mpr hfst))

/-- **A dual-number tangent lift of `ρbar`** — a point of the framed
tangent space of the hardly ramified deformation problem: a hardly
ramified representation over the dual numbers `k[ε]` whose reduction
along the constant-term map `k[ε] →+* k` (an identification, as in
`IsResidualIdentified`) is conjugate to `ρbar`.  Classically the set
of these lifts is a torsor under the cocycles
`Z¹_{Σ}(G_{ℚ,{2,p}}, ad ρbar)` over the framed points, and its
finiteness is exactly Schlessinger's H3 for the hardly ramified
functor; here it is the hypothesis carrier feeding the arithmetic
finiteness leaf into the deformation-theoretic core leaf below. -/
def IsDualNumberTangentLift.{uK, uW} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (ρε : GaloisRep ℚ (DualNumber k) (Fin 2 → DualNumber k)) : Prop :=
  IsHardlyRamified hpodd (rank_finTwoFun (DualNumber k)) ρε ∧
  (letI : Algebra (DualNumber k) k :=
    (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
  letI : ContinuousSMul (DualNumber k) k :=
    ⟨continuous_of_discreteTopology⟩
  ∃ e : (k ⊗[DualNumber k] (Fin 2 → DualNumber k)) ≃ₗ[k] W,
    (ρε.baseChange k).conj e = ρbar)

/-!
### The Hermite–Minkowski decomposition of the restricted-ramification
finiteness leaf (2026-07-24)

A hardly ramified representation over the finite discrete coefficient
ring `A` is a continuous homomorphism of `Γ ℚ` into the FINITE
discrete monoid `End_A(A²)`, unramified outside `{2, p}`.  Its kernel
is an open normal subgroup of index at most `#End_A(A²)` containing
the image of every local inertia group away from `{2, p}`, and the
representation is determined by its kernel `N` together with a
function on the finite quotient `Γ ℚ ⧸ N`
(`finite_setOf_galoisRep_isUnramifiedAt`).  By the infinite Galois
correspondence the candidate kernels are exactly the fixing subgroups
of finite Galois subfields `K ⊆ ℚᵃˡᵍ` of bounded degree on which every
local inertia away from `{2, p}` acts trivially
(`finite_setOf_subgroup_inertiaAt_le`), and there are finitely many
such fields (`finite_setOf_intermediateField_inertiaAt_le`): their
discriminants are divisible only by `2` and `p`
(`not_dvd_discr_of_inertiaTrivialAt`, through the PROVEN inertia
dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup` of
`MazurTorsion`), with exponents bounded in terms of the degree alone
(`exists_discr_factorization_le_of_finrank_le`, PROVEN 2026-07-25 over
the single sorried leaf of the cut, the WILD half of the
different-exponent bound `differentIdeal_exponent_le_wild`), so the fields have
bounded discriminant and mathlib's Hermite theorem
`NumberField.finite_of_discr_bdd` applies.
-/

/-- **Triviality of the inertia at a rational prime `q` on a subgroup
of `Γ ℚ`**: every element of the local inertia group at `q`, pushed
into `Γ ℚ` along the (chosen-embedding) map of absolute Galois groups,
lies in `N`.  For `N = K.fixingSubgroup` this says exactly that the
finite Galois subfield `K ⊆ ℚᵃˡᵍ` is unramified at `q` (through the
PROVEN dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup` of
`MazurTorsion`, reached by `not_dvd_discr_of_inertiaTrivialAt`); for
`N` the kernel of a representation it is exactly
`GaloisRep.IsUnramifiedAt`.  Stated in this pointwise form — rather
than as `Subgroup.map … ≤ N` — so that both sides read off
definitionally: the `Subgroup.map` spelling the `MazurTorsion`
dictionary consumes is rebuilt where needed. -/
def InertiaTrivialAt {q : ℕ} (hq : q.Prime)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ)) : Prop :=
  ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
    (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))) σ ∈ N

/-- **The WILD different-exponent bound at a prime** (sorry node —
after the recut of 2026-07-25 the *single* arithmetic leaf of the
Hermite–Minkowski cut of `finite_setOf_isHardlyRamified`; Serre,
*Corps Locaux* III §6 Prop. 13, wild half): for a number field `K`, a
rational prime `q` and a prime `Q` of `𝓞_K` over `q` whose
ramification index `e = e(Q∣q)` is divisible by `q`, every `d` with
`Q^d ∣ 𝔡_{K/ℚ}` satisfies `d ≤ e − 1 + e·v_q(e)`.

Note `v_Q(q) = e`, so `e − 1 + e·v_q(e)` is Serre's `e − 1 + v_Q(e)`
verbatim; the bound is SHARP (attained by `ℚ(2^{1/4})` at `q = 2`,
where `e = 4`, `v_2(e) = 2` and `d = 11 = 3 + 8`; also by `ℚ(√2)` at
`q = 2`, `d = 3 = 1 + 2`).  Checked numerically against PARI/GP over
701 (field, prime-above-`q`) pairs of degrees 2–6 at `q ≤ 7`: no
violation, 293 of them sharp.

The TAME half — `q ∤ e`, where the bound reads `d ≤ e − 1` — is PROVEN
in `ModThree.lean` as `not_pow_ramificationIdx_dvd_differentIdeal`
(mathlib supplies the matching lower half
`pow_sub_one_dvd_differentIdeal`) and is discharged here in
`differentIdeal_exponent_le`; only the wild case is left open, which is
why this leaf carries `hwild` as a hypothesis.

Route, and the machinery it needs that mathlib does not have (in
dependency order — the argument itself is three lines of valuation
arithmetic, and every gap is in getting to a local Eisenstein
polynomial):

* **(M1) `differentIdeal` under localization/completion.**  `v_Q` of
  `𝔡_{𝓞_K/ℤ}` equals the different exponent of the extension of DVRs
  `ℤ_(q) → (𝓞_K)_Q` (equivalently of `ℚ_q → K_Q`).  mathlib has the
  different only for a global Dedekind pair; nothing relates it to a
  localization at one prime.
* **(M2) the maximal unramified subextension.**  `K_Q/ℚ_q` factors as
  `ℚ_q ⊆ L₀ ⊆ K_Q` with `L₀/ℚ_q` unramified of degree `f` and
  `K_Q/L₀` totally ramified of degree `e`; the tower formula
  `differentIdeal_eq_differentIdeal_mul_differentIdeal` plus
  "unramified ⟺ does not divide the different"
  (mathlib's `not_dvd_differentIdeal_iff`) reduce to `K_Q/L₀`.
* **(M3) monogenicity of a totally ramified extension of DVRs**
  (Serre I §6 Prop. 18): `𝓞_{K_Q} = 𝓞_{L₀}[π]` for any uniformizer
  `π`, its minimal polynomial `g` over `𝓞_{L₀}` is Eisenstein of
  degree `e`, and `𝔡 = (g'(π))` (mathlib's
  `conductor_mul_differentIdeal` with unit conductor).
* **(M4) the ultrametric "distinct valuations" lemma**: if the terms
  of a finite sum have pairwise distinct valuations then the sum's
  valuation is their minimum.

With those, the bound is immediate: writing
`g = X^e + a_{e−1}X^{e−1} + ⋯ + a_0` with `a_i ∈ 𝓞_{L₀}`, every
nonzero value of `v_Q` on `L₀` lies in `e·ℤ` (total ramification), so
`v_Q(i·a_i·π^{i−1}) ≡ i − 1 (mod e)` for `1 ≤ i ≤ e`: the `e`
summands of `g'(π) = e·π^{e−1} + Σ_{i<e} i·a_i·π^{i−1}` have PAIRWISE
DISTINCT valuations, whence `v_Q(g'(π))` is their minimum, which is at
most the `i = e` term `v_Q(e·π^{e−1}) = e·v_q(e) + e − 1`.

Alternative route, entirely inside the material already PROVEN in
`ModThree.lean` but only for the Galois case, and needing its own
missing piece: for `K/ℚ` Galois,
`le_sum_card_inertia_pow_of_pow_dvd_differentIdeal` gives
`d ≤ Σ_{i<N}(#G_i − 1)` as soon as `G_N = 1`, so all that is missing
is **(M5) a bound on the last ramification jump** — `G_i = 1` for
`i > e/(q−1)`, say `(Q^(m+1)).inertia = ⊥` for `m = [K:ℚ]`.  (M5) is
essentially equivalent to this leaf, so it is not a cheaper target;
and reducing a general `K` to its Galois closure would additionally
need **(M6)** the tower discriminant formula
`NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`
(mathlib has it) together with a degree bound
`[normalClosure ℚ K : ℚ] ≤ n!` (mathlib does not).

Both-ways audit: an inequality between natural numbers attached to a
number field, classically true as cited and numerically corroborated
above; no representation-theoretic hypotheses, no vacuity concerns —
the conclusion genuinely constrains `𝔡_{K/ℚ}` (its failure would make
`v_q(discr K)` unbounded on fields of bounded degree, contradicting
the sharp cases listed). -/
theorem differentIdeal_exponent_le_wild (K : Type*) [Field K]
    [NumberField K] (q : ℕ) (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (q : NumberField.RingOfIntegers K) ∈ Q)
    (hwild : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q)
    (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
      Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q :=
  sorry

/-- **The different-exponent bound at a prime** (PROVEN over the wild
leaf — Serre, *Corps Locaux* III §6 Prop. 13 in full): for a prime `Q`
of `𝓞_K` over the rational prime `q` with ramification index `e`,
every `d` with `Q^d ∣ 𝔡_{K/ℚ}` satisfies `d ≤ e − 1 + e·v_q(e)`.  The
tame case `q ∤ e` is `ModThree.lean`'s PROVEN
`not_pow_ramificationIdx_dvd_differentIdeal` (`¬ Q^e ∣ 𝔡`, so `d < e`,
and `v_q(e) = 0` makes the bound exactly `e − 1`); the wild case is
`differentIdeal_exponent_le_wild`. -/
theorem differentIdeal_exponent_le (K : Type*) [Field K]
    [NumberField K] (q : ℕ) (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (q : NumberField.RingOfIntegers K) ∈ Q) (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    d ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
      Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
        (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := by
  by_cases hw : q ∣ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q
  · exact differentIdeal_exponent_le_wild K q hq Q hQ hmem hw d hd
  · have hnot := IsHardlyRamified.not_pow_ramificationIdx_dvd_differentIdeal
      K q hq Q hQ hmem hw
    have hlt : d < Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by
      by_contra hge
      exact hnot (dvd_trans (pow_dvd_pow Q (not_lt.mp hge)) hd)
    exact le_trans (Nat.le_pred_of_lt hlt) (Nat.le_add_right _ _)

/-- **Discriminant-exponent bound by the degree** (PROVEN 2026-07-25
over the single wild different-exponent leaf
`differentIdeal_exponent_le_wild` — the arithmetic leaf of the
Hermite–Minkowski cut of `finite_setOf_isHardlyRamified`): for a fixed
prime `q` and degree bound `n`, the exponent of `q` in the
discriminant of a number field of degree at most `n` is bounded by a
constant depending only on `q` and `n`; here `C = (n + 1)·n` works.

Proof (pure bookkeeping over the two per-prime inputs, no new
arithmetic): `ModThree.lean`'s PROVEN
`discr_factorization_le_of_forall_differentIdeal_pow_dvd` turns a
uniform per-prime bound `d_Q ≤ b·e_Q` into
`v_q(discr K) ≤ b·[K:ℚ]`; the per-prime bound is
`differentIdeal_exponent_le`, `d_Q ≤ e − 1 + e·v_q(e)`, together with
`e ≤ [K:ℚ] ≤ n` (mathlib's `Ideal.ramificationIdx_le_finrank`, through
the fundamental identity) and `v_q(e) < e ≤ n`
(`Nat.factorization_lt`), giving `b = n + 1`.  The constant `C` is
existentially quantified, so any correct route may sharpen it.

Both-ways audit: a plain universally quantified inequality about
number fields with an existential bound — classically true outright as
cited; no representation-theoretic hypotheses, no vacuity concerns.
Consumed by `finite_setOf_intermediateField_inertiaAt_le` at
`q ∈ {2, p}`. -/
theorem exists_discr_factorization_le_of_finrank_le (q n : ℕ)
    (hq : q.Prime) :
    ∃ C : ℕ, ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ))
      (hfd : FiniteDimensional ℚ K), Module.finrank ℚ K ≤ n →
      haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
      (NumberField.discr K).natAbs.factorization q ≤ C := by
  refine ⟨(n + 1) * n, fun K hfd hrank => ?_⟩
  haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
  have hqZ : Prime ((q : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hspan0 : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hspanMax : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      hqZ).isMaximal hspan0)
  -- the uniform per-prime different-exponent bound `d_Q ≤ (n + 1)·e_Q`
  have key : ∀ Q : Ideal (NumberField.RingOfIntegers K), Q.IsPrime →
      ((q : NumberField.RingOfIntegers K) ∈ Q) → ∀ d : ℕ,
      Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) →
      1 * d ≤ (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by
    intro Q hQ hmem d hd
    haveI := hQ
    haveI hlies : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
      (Ideal.liesOver_span_iff hQ.ne_top hqZ).mpr (by exact_mod_cast hmem)
    have he0 : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
    have hen : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q ≤ n :=
      le_trans (Ideal.ramificationIdx_le_finrank
        (S := NumberField.RingOfIntegers K) (K := ℚ) (L := K) Q) hrank
    have hv : (Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) Q).factorization q
        ≤ n := le_of_lt (lt_of_lt_of_le (Nat.factorization_lt q he0) hen)
    have hser := differentIdeal_exponent_le K q hq Q hQ hmem d hd
    calc 1 * d = d := one_mul d
      _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q - 1 +
          Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q *
            (Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q).factorization q := hser
      _ ≤ Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q +
          Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q * n :=
        Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left _ hv)
      _ = (n + 1) * Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q := by ring
  have hmain := IsHardlyRamified.discr_factorization_le_of_forall_differentIdeal_pow_dvd
    K q hq 1 (n + 1) key
  calc (NumberField.discr K).natAbs.factorization q
      = 1 * (NumberField.discr K).natAbs.factorization q := (one_mul _).symm
    _ ≤ (n + 1) * Module.finrank ℚ K := hmain
    _ ≤ (n + 1) * n := Nat.mul_le_mul_left _ hrank

/-- **Unramified fields have coprime discriminant** (PROVEN — the
inertia-to-discriminant transport of the Hermite–Minkowski cut): if
the inertia at a prime `q` fixes the finite Galois subfield
`K ⊆ ℚᵃˡᵍ` pointwise, then `q` does not divide the discriminant of
`K`.  Chain: the pointwise hypothesis is repackaged as the image
inclusion `Subgroup.map … ≤ K.fixingSubgroup`; every prime of `𝓞 K`
over `q` is then unramified by the PROVEN inertia dictionary
`isUnramifiedAt_of_inertia_le_fixingSubgroup` (`MazurTorsion`), and a
prime unramified in every prime above it does not divide the
discriminant (mathlib's `NumberField.not_dvd_discr_iff_forall_mem`).
This is the ρ-free core of `ModThree.lean`'s
`kernel_field_not_dvd_discr`. -/
theorem not_dvd_discr_of_inertiaTrivialAt
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] {q : ℕ} (hq : q.Prime)
    (hfix : InertiaTrivialAt hq K.fixingSubgroup) :
    ¬ ((q : ℤ) ∣ NumberField.discr K) := by
  have hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ K.fixingSubgroup := by
    rintro g ⟨σ, hσ, rfl⟩
    exact hfix σ hσ
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  rw [NumberField.not_dvd_discr_iff_forall_mem K
    (NumberField.RingOfIntegers K) hqZ]
  intro P hP hmem
  haveI := hP
  exact isUnramifiedAt_of_inertia_le_fixingSubgroup K hq hle P
    (by exact_mod_cast hmem)

/-- **Hermite–Minkowski for fields unramified outside `{2, p}`**
(PROVEN over the discriminant-exponent leaf — the field-side
finiteness of the Hermite–Minkowski cut): there are finitely many
finite Galois subfields of `ℚᵃˡᵍ` of degree at most `n` on which the
global inertia at every prime `q ∉ {2, p}` acts trivially.  Proof: the
discriminant of such a field is divisible only by `2` and `p`
(`not_dvd_discr_of_inertiaTrivialAt`), with exponents bounded by
constants `C₂`, `C_p` depending only on `n`
(`exists_discr_factorization_le_of_finrank_le`), so
`|d_K| = 2^{v₂}·p^{v_p} ≤ 2^{C₂}·p^{C_p}` and mathlib's Hermite
theorem `NumberField.finite_of_discr_bdd` finishes. -/
theorem finite_setOf_intermediateField_inertiaAt_le (p n : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    {K : IntermediateField ℚ (AlgebraicClosure ℚ) |
      ∃ _ : FiniteDimensional ℚ K,
        IsGalois ℚ K ∧ Module.finrank ℚ K ≤ n ∧
        ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
          InertiaTrivialAt hq K.fixingSubgroup}.Finite := by
  classical
  obtain ⟨C2, hC2⟩ :=
    exists_discr_factorization_le_of_finrank_le 2 n Nat.prime_two
  obtain ⟨Cp, hCp⟩ :=
    exists_discr_factorization_le_of_finrank_le p n hp
  refine Set.Finite.subset
    ((NumberField.finite_of_discr_bdd (AlgebraicClosure ℚ)
      (2 ^ C2 * p ^ Cp)).image Subtype.val) ?_
  rintro K ⟨hfd, hgal, hrank, hinert⟩
  haveI := hfd
  haveI hNF : NumberField K := @NumberField.mk _ _ inferInstance hfd
  haveI := hgal
  refine ⟨⟨K, hfd⟩, ?_, rfl⟩
  show |NumberField.discr K| ≤ ((2 ^ C2 * p ^ Cp : ℕ) : ℤ)
  have hD0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hN0 : (NumberField.discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  -- every prime factor of `|d_K|` is `2` or `p`
  have hfac : ∀ q : ℕ, q.Prime → q ∣ (NumberField.discr K).natAbs →
      q = 2 ∨ q = p := by
    intro q hq hqN
    by_contra hne
    push Not at hne
    refine not_dvd_discr_of_inertiaTrivialAt K hq
      (hinert q hq hne.1 hne.2) ?_
    have h1 : (((NumberField.discr K).natAbs : ℤ)) ∣ NumberField.discr K := by
      rw [Int.natCast_natAbs]
      exact (abs_dvd _ _).mpr dvd_rfl
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hqN) h1
  -- the factorization `|d_K| = 2^{v₂}·p^{v_p}`
  have hsupp : (NumberField.discr K).natAbs.factorization.support ⊆
      ({2, p} : Finset ℕ) := by
    intro q hqmem
    rw [Nat.support_factorization] at hqmem
    rcases hfac q (Nat.prime_of_mem_primeFactors hqmem)
      (Nat.dvd_of_mem_primeFactors hqmem) with h | h <;> simp [h]
  have hNeq : (NumberField.discr K).natAbs =
      2 ^ (NumberField.discr K).natAbs.factorization 2 *
        p ^ (NumberField.discr K).natAbs.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod_of_support_subset _ hsupp (· ^ ·)
      (fun i _ => pow_zero i), Finset.prod_pair (Ne.symm hp2)]
  -- the two exponent bounds
  have hkey : (NumberField.discr K).natAbs ≤ 2 ^ C2 * p ^ Cp := by
    rw [hNeq]
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (hC2 K hfd hrank))
      (Nat.pow_le_pow_right hp.pos (hCp K hfd hrank))
  have habs : |NumberField.discr K| =
      (((NumberField.discr K).natAbs : ℤ)) := (Int.natCast_natAbs _).symm
  rw [habs]
  exact_mod_cast hkey

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of open normal subgroups of bounded index unramified
outside `{2, p}`** (PROVEN — the Galois-correspondence step of the
Hermite–Minkowski cut; "`G_{ℚ,{2,p}}` is small"): there are finitely
many open normal subgroups `N ≤ Γ ℚ` of index at most `n` containing
the global inertia at every prime `q ∉ {2, p}`.  Proof: every such `N`
is closed (`Subgroup.isClosed_of_isOpen`), hence by the infinite
Galois correspondence it is the fixing subgroup of its fixed field
`K = ℚᵃˡᵍ^N` (`InfiniteGalois.fixingSubgroup_fixedField`), which is
finite-dimensional (`InfiniteGalois.isOpen_iff_finite`), Galois over
`ℚ` (`InfiniteGalois.normal_iff_isGalois`), of degree
`[K : ℚ] = #(Γ ℚ ⧸ N) = index N ≤ n`
(`InfiniteGalois.normalAutEquivQuotient`,
`IsGalois.card_aut_eq_finrank`), and inertia-trivial away from
`{2, p}`; so the set injects into the finite field set of
`finite_setOf_intermediateField_inertiaAt_le` via `fixingSubgroup`. -/
theorem finite_setOf_subgroup_inertiaAt_le (p n : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    {N : Subgroup (Field.absoluteGaloisGroup ℚ) |
      N.Normal ∧ IsOpen (N : Set (Field.absoluteGaloisGroup ℚ)) ∧
      N.FiniteIndex ∧ N.index ≤ n ∧
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        InertiaTrivialAt hq N}.Finite := by
  classical
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  refine Set.Finite.subset
    ((finite_setOf_intermediateField_inertiaAt_le p n hp hp2).image
      fun K => K.fixingSubgroup) ?_
  rintro N ⟨hnorm, hopen, hFI, hidx, hinert⟩
  have hclosed : IsClosed (N : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen N hopen
  have hfix : (IntermediateField.fixedField (E := AlgebraicClosure ℚ)
      N).fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N, hclosed⟩
  haveI hfd : FiniteDimensional ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hopen)
  haveI hgalK : IsGalois ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) :=
    (InfiniteGalois.normal_iff_isGalois _).mp (by rw [hfix]; exact hnorm)
  haveI hnorm' := hnorm
  have hcard : Module.finrank ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) =
      Nat.card (Field.absoluteGaloisGroup ℚ ⧸ N) := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      (⟨N, hclosed⟩ : ClosedSubgroup
        (Field.absoluteGaloisGroup ℚ))).toEquiv).symm
  have hrank : Module.finrank ℚ
      (IntermediateField.fixedField (E := AlgebraicClosure ℚ) N) ≤ n := by
    rw [hcard, ← Subgroup.index_eq_card N]
    exact hidx
  refine ⟨_, ⟨hfd, hgalK, hrank, ?_⟩, hfix⟩
  intro q hq hq2 hqp
  rw [hfix]
  exact hinert q hq hq2 hqp

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of continuous representations unramified outside
`{2, p}`** (PROVEN — the representations-to-subgroups bookkeeping of
the Hermite–Minkowski cut): over a finite discrete coefficient ring
`A` there are finitely many `Γ ℚ`-representations on `A²` unramified
outside `{2, p}`.  Proof: the endomorphism monoid `E = End_A(A²)` is
finite and discrete, so the kernel of a representation is an open
normal subgroup whose quotient injects into `E` (index at most `#E`),
containing the global inertia away from `{2, p}`
(`GaloisRep.IsUnramifiedAt` transported along
`GaloisRep.toLocal_apply`); the finitely many candidate kernels
(`finite_setOf_subgroup_inertiaAt_le`) each carry finitely many
representations, a representation being determined by the function
`Γ ℚ ⧸ N → E` it induces on `Quotient.out` representatives. -/
theorem finite_setOf_galoisRep_isUnramifiedAt.{uA} (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A] :
    {ρ : GaloisRep ℚ A (Fin 2 → A) |
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat}.Finite := by
  classical
  haveI hfinE : Finite (Module.End A (Fin 2 → A)) :=
    Finite.of_injective
      (fun f => (f : (Fin 2 → A) → (Fin 2 → A))) DFunLike.coe_injective
  -- the kernel subgroup of a representation
  let kerOf : GaloisRep ℚ A (Fin 2 → A) →
      Subgroup (Field.absoluteGaloisGroup ℚ) := fun ρ =>
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  -- membership in `kerOf ρ` is triviality of `ρ`
  have hmem : ∀ (ρ : GaloisRep ℚ A (Fin 2 → A))
      (g : Field.absoluteGaloisGroup ℚ), g ∈ kerOf ρ ↔ ρ g = 1 :=
    fun _ _ => Iff.rfl
  -- a representation is recovered on `Quotient.out` representatives
  have hout : ∀ (ρ : GaloisRep ℚ A (Fin 2 → A))
      (N : Subgroup (Field.absoluteGaloisGroup ℚ)), kerOf ρ = N →
      ∀ g : Field.absoluteGaloisGroup ℚ,
        ρ (QuotientGroup.mk (s := N) g).out = ρ g := by
    intro ρ N hN g
    subst hN
    have h1 : ((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g ∈ kerOf ρ :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    have h2 : ρ (((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g) = 1 :=
      (hmem ρ _).mp h1
    have h3 : ρ (QuotientGroup.mk (s := kerOf ρ) g).out *
        ρ (((QuotientGroup.mk (s := kerOf ρ) g).out)⁻¹ * g) = ρ g := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [h2, mul_one] at h3
    exact h3
  -- the induced map on the finite quotient is injective
  have hinj : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      Function.Injective
        (fun x : Field.absoluteGaloisGroup ℚ ⧸ kerOf ρ => ρ x.out) := by
    intro ρ x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hxy' : ρ (QuotientGroup.mk (s := kerOf ρ) a).out =
        ρ (QuotientGroup.mk (s := kerOf ρ) b).out := hxy
    rw [hout ρ (kerOf ρ) rfl, hout ρ (kerOf ρ) rfl] at hxy'
    refine (QuotientGroup.eq).mpr ((hmem ρ _).mpr ?_)
    have e1 : ρ (a⁻¹ * b) = ρ a⁻¹ * ρ b := map_mul ρ _ _
    rw [e1, ← hxy', ← map_mul, inv_mul_cancel, map_one]
  -- kernels are open, normal, of index at most `#E`
  have hopenker : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      IsOpen ((kerOf ρ : Subgroup (Field.absoluteGaloisGroup ℚ)) :
        Set (Field.absoluteGaloisGroup ℚ)) := by
    intro ρ
    letI := moduleTopology A (Module.End A (Fin 2 → A))
    haveI : Module.Finite A (Module.End A (Fin 2 → A)) :=
      Module.Finite.of_finite
    haveI : DiscreteTopology (Module.End A (Fin 2 → A)) :=
      discreteTopology_moduleTopology _ _
    have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρ g :=
      ContinuousMonoidHom.continuous_toFun ρ
    exact (isOpen_discrete
      ({1} : Set (Module.End A (Fin 2 → A)))).preimage hcont
  have hnormal : ∀ ρ : GaloisRep ℚ A (Fin 2 → A), (kerOf ρ).Normal := by
    intro ρ
    refine ⟨fun x hx g => ?_⟩
    show ρ (g * x * g⁻¹) = 1
    rw [map_mul, map_mul, (hx : ρ x = 1), mul_one, ← map_mul,
      mul_inv_cancel, map_one]
  have hfinquot : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      Finite (Field.absoluteGaloisGroup ℚ ⧸ kerOf ρ) :=
    fun ρ => Finite.of_injective _ (hinj ρ)
  have hidx : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      (kerOf ρ).index ≤ Nat.card (Module.End A (Fin 2 → A)) := by
    intro ρ
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective _ (hinj ρ)
  -- unramifiedness puts the global inertia inside the kernel
  have hinertker : ∀ ρ : GaloisRep ℚ A (Fin 2 → A),
      (∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) →
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        InertiaTrivialAt hq (kerOf ρ) := by
    intro ρ hρ q hq hq2 hqp σ hσ
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ q hq hq2 hqp).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    refine (hmem ρ _).mpr ?_
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- assemble: finitely many kernels, finitely many maps per kernel
  have h𝒩fin := finite_setOf_subgroup_inertiaAt_le p
    (Nat.card (Module.End A (Fin 2 → A))) hp hp2
  refine Set.Finite.subset (h𝒩fin.biUnion
    (t := fun N => {ρ : GaloisRep ℚ A (Fin 2 → A) | kerOf ρ = N})
    fun N hN => ?_) ?_
  · -- the fiber over a fixed kernel injects into `Γ ℚ ⧸ N → E`
    haveI : N.FiniteIndex := hN.2.2.1
    haveI : Finite (Field.absoluteGaloisGroup ℚ ⧸ N) :=
      Subgroup.finite_quotient_of_finiteIndex
    refine Set.Finite.of_finite_image (f := fun ρ =>
      fun x : Field.absoluteGaloisGroup ℚ ⧸ N => ρ x.out)
      (Set.toFinite _) ?_
    intro ρ₁ hρ₁ ρ₂ hρ₂ hF
    have key : ∀ g, ρ₁ g = ρ₂ g := by
      intro g
      have e1 := hout ρ₁ N hρ₁ g
      have e2 := hout ρ₂ N hρ₂ g
      have e3 : ρ₁ (QuotientGroup.mk (s := N) g).out =
          ρ₂ (QuotientGroup.mk (s := N) g).out :=
        congrFun hF (QuotientGroup.mk (s := N) g)
      rw [← e1, e3, e2]
    exact GaloisRep.ext key
  · intro ρ hρ
    haveI := hfinquot ρ
    exact Set.mem_biUnion
      ⟨hnormal ρ, hopenker ρ, Subgroup.finiteIndex_of_finite_quotient,
        hidx ρ, hinertker ρ hρ⟩ rfl

/-- **Restricted-ramification finiteness leaf** (DECOMPOSED 2026-07-24
along the Hermite–Minkowski cut above — PROVEN over the
discriminant-exponent statement `exists_discr_factorization_le_of_finrank_le`,
itself PROVEN 2026-07-25 over the single sorried leaf of the cut,
the wild different-exponent bound `differentIdeal_exponent_le_wild`;
the arithmetic finiteness input of the FOUNDER cut, and the only
number-theoretic content of Schlessinger's H3 for the hardly ramified
problem): over a FINITE discrete local coefficient `ℤ_p`-algebra `A`,
there are only finitely many hardly ramified representations
`G_ℚ → GL₂(A)`.

Mathematical content (Hermite–Minkowski; Serre, *Galois cohomology*,
II §6, "`G_S` is small"; Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Thm. 10.9.x; Diamond–Darmon–Taylor, *Fermat's Last
Theorem* (1995), §2): a hardly ramified representation is continuous
into the finite discrete group of automorphisms of `A²` and unramified
outside `{2, p}` (`IsHardlyRamified.isUnramified`), so its kernel is
open and its fixed field is a number field of degree
`≤ |GL₂(A)|` unramified outside `{2, p}`.  Ramification bounded to a
fixed finite set of primes bounds the discriminant in terms of the
degree (the exponent of a prime in the different is bounded by
`e - 1 + e·v(e)`), and by the Hermite–Minkowski theorem there are only
finitely many number fields of bounded degree and bounded
discriminant; each supports finitely many homomorphisms of its (finite)
Galois group into the finite `GL₂(A)`.  Equivalently: the Galois group
`G_{ℚ,{2,p}}` of the maximal extension unramified outside `{2,p,∞}` is
a *small* profinite group — it has finitely many open subgroups of
each index — so the set of continuous homomorphisms into any fixed
finite group is finite; the hardly ramified set injects into it.

Both-ways audit: the statement quantifies over an abstract finite
coefficient ring and asserts a plain classical finiteness — true
outright, no vacuity needed.  Consumed by the pillar assembly at
`A = k[ε]` (through `Set.Finite.subset`, the tangent lifts being among
the hardly ramified representations); stated over a general finite
coefficient ring because the same finiteness at every Artinian level
is what the future proof of the deformation-theoretic core leaf will
consume when building the universal ring as a limit. -/
theorem finite_setOf_isHardlyRamified.{uA} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime]
    {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[p] A] [Finite A] [DiscreteTopology A] :
    {ρ : GaloisRep ℚ A (Fin 2 → A) |
      IsHardlyRamified hpodd (rank_finTwoFun A) ρ}.Finite := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpodd
    exact (by decide : ¬ Odd 2) hpodd
  exact (finite_setOf_galoisRep_isUnramifiedAt p hp hp2 (A := A)).subset
    fun ρ hρ q hq hq2 hqp => hρ.isUnramified q hq ⟨hq2, hqp⟩

/-- **Weak universality on identified FINITE tests** — the
Artinian-level restriction of `IsWeaklyUniversalOnIdentifiedDeformation`
(the LEVEL cut of the strict Mazur core leaf, 2026-07-24): the package
`(Runiv, ρuniv, πuniv)` factors every standard-framed residually
identified test deformation whose coefficient ring is FINITE as a type
— classically an Artinian local `ℤ_p`-algebra with residue field `k`,
exactly the objects of Schlessinger's category on which the
deformation functor is defined pointwise.  Two deliberate STRENGTHENED
clauses relative to the module-finite predicate, both of which the
classical classifying map satisfies and both of which the pro-finite
limit upgrade `isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`
consumes essentially: the trace clause holds at EVERY prime with no
exceptional set (the classifying map carries `ρuniv` to a conjugate of
the test representation, and `charFrob` evaluates both at the same
fixed global Galois element `adicArithFrob v`, so the polynomials
match identically — an exceptional set varying with the Artinian level
would break the inverse-limit trace argument), and the test category
is standard-framed (module universe = coefficient universe; the
reframing transport collapses the general case). -/
def IsWeaklyUniversalOnIdentifiedFiniteTests.{s, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ D : HardlyRamifiedFiniteDeformation.{s, s, uK, uW} hpodd ρbar,
    Finite D.A →
    D.IsResidualIdentified →
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∃ ψ : Runiv →+* D.A,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] D.A ∧
      D.π.comp ψ = πuniv ∧
      ∀ (q : ℕ) (hq : q.Prime),
        ψ ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

/-!
### The Schlessinger cut of the finite-level leaf (2026-07-25)

The Artinian-level stratum
`exists_weaklyUniversalOnIdentified_framed_finiteTests` is cut along the
classical architecture of Schlessinger's criterion into three sharp
statements, glued by the PROVEN assembly at the end of this section:

* the **arithmetic core**
  `exists_framedStrictlyUniversal_hardlyRamified_finiteTests` — the
  hull of the framed hardly ramified lifting functor exists in Mazur's
  category, *presented* as a quotient of `ℤ_p[[x₁, …, x_g]]` and
  classifying framed identified finite tests STRICTLY (an honest
  conjugacy `ψ_*ρuniv ≅ ρ_A` of representations, not a trace-level
  clause).  This is Schlessinger H1/H2 (fibre products of coefficient
  rings carry fibre products of framed lifts) + H4 through Schur (an
  odd irreducible two-dimensional representation over a finite field of
  odd characteristic is absolutely irreducible, so
  `End_{k[Γ]}(ρbar) = k`) + the relative representability of the hardly
  ramified local conditions (Ramakrishna's flat condition at `p`,
  Conrad–Diamond–Taylor's tame condition at `2`) + the de Smit–Lenstra
  presentation; H3 is the supplied `hfin`;
* the two **Mazur-category commutative-algebra** statements
  `isNoetherianRing_of_mvPowerSeries_presentation` and
  `isAdicComplete_of_mvPowerSeries_presentation`, which turn the
  presentation into the ring-theoretic clauses of the conclusion.

Everything else is proven here: the passage from the strict conjugacy
clause to the trace-level clauses of
`IsWeaklyUniversalOnIdentifiedFiniteTests` (through the base-change /
conjugation invariance of `charFrob`, which is what makes the trace
clause hold at EVERY prime with EMPTY exceptional set — the uniformity
the pro-finite upgrade leaf consumes) and the collapse of a general
test deformation onto the standard frame (`reframe`).
-/

/-- **Continuity of a reduction map out of a `ℤ_p`-module-topology
coefficient ring** (PROVEN): every ring homomorphism from a topological
`ℤ_p`-algebra carrying the `ℤ_p`-module topology into a finite discrete
field is continuous — `IsModuleTopology.continuous_of_ringHom` reduces
this to continuity of the composite `ℤ_p →+* k`, which is automatic
(`continuous_ringHom_padicInt`).  The frame-level restatement of
`HardlyRamifiedFiniteDeformation.continuous_pi`, on the raw coefficient
data rather than on a bundled test deformation, so that the framed test
objects of the strict universality clause below can carry their own
reduction maps. -/
lemma continuous_ringHom_of_isModuleTopology {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra ℤ_[p] A] [IsModuleTopology ℤ_[p] A]
    {k : Type*} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k] (f : A →+* k) :
    Continuous f :=
  IsModuleTopology.continuous_of_ringHom (R := ℤ_[p]) f
    (continuous_ringHom_padicInt (f.comp (algebraMap ℤ_[p] A)))

set_option backward.isDefEq.respectTransparency false in
/-- **Strict universality on framed finite test lifts** — the
Mazur-level (isomorphism-level) universal property against the objects
of Schlessinger's category, from which the trace-level clause
`IsWeaklyUniversalOnIdentifiedFiniteTests` is DERIVED in the assembly
below.

A test object is the raw datum Schlessinger's category consists of: a
FINITE local topological `ℤ_p`-algebra `A` carrying the `ℤ_p`-module
topology (classically: an Artinian local `ℤ_p`-algebra with residue
field `k`, discrete), a hardly ramified representation `ρA` on the
STANDARD FRAME `Fin 2 → A`, a surjective reduction `πA : A →+* k` and a
residual identification of `ρA ⊗_A k` with `ρbar` (the reduction map is
automatically continuous, `continuous_ringHom_of_isModuleTopology`, so
`k` is a topological `A`-algebra and the base change is formed exactly
as in `HardlyRamifiedFiniteDeformation.IsResidualIdentified`).

The conclusion is the classifying map in its classical strength: a
CONTINUOUS ring homomorphism `ψ : Runiv →+* A`, strict (compatible with
the `ℤ_p`-structures and with the two reductions), which carries the
universal representation to `ρA` up to conjugacy — `ρuniv ⊗_{Runiv} A`
is isomorphic to `ρA` as a representation, not merely trace by trace.
Conjugation- and base-change invariance of `charFrob`
(`coeff_one_charFrob_of_baseChange_conj`) then yields the trace clause
at EVERY prime with no exceptional set, which is what the pro-finite
limit upgrade needs. -/
def IsStrictlyUniversalOnFramedFiniteLifts.{s, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)) (πuniv : Runiv →+* k) :
    Prop :=
  ∀ (A : Type s) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A]
    [IsModuleTopology ℤ_[p] A] [Finite A]
    (ρA : GaloisRep ℚ A (Fin 2 → A)),
    IsHardlyRamified hpodd (rank_finTwoFun A) ρA →
    ∀ πA : A →+* k, Function.Surjective πA →
    (letI : Algebra A k := πA.toAlgebra
     letI : ContinuousSMul A k := continuousSMul_of_algebraMap A k
       (by
         rw [RingHom.algebraMap_toAlgebra]
         exact continuous_ringHom_of_isModuleTopology (p := p) πA)
     ∃ e : (k ⊗[A] (Fin 2 → A)) ≃ₗ[k] W, (ρA.baseChange k).conj e = ρbar) →
    ∃ ψ : Runiv →+* A, ∃ hψ : Continuous ψ,
      ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] A ∧
      πA.comp ψ = πuniv ∧
      (letI : Algebra Runiv A := ψ.toAlgebra
       letI : ContinuousSMul Runiv A := continuousSMul_of_algebraMap Runiv A
         (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
       ∃ e : (A ⊗[Runiv] (Fin 2 → Runiv)) ≃ₗ[A] (Fin 2 → A),
         (ρuniv.baseChange A).conj e = ρA)

set_option backward.isDefEq.respectTransparency false in
/-- **Trace transfer along a base-change conjugacy** (PROVEN): if the
base change of `ρ` along `A → B` is conjugate to `ρ'`, then the linear
`charFrob` coefficients of `ρ'` are the images of those of `ρ`, at
EVERY finite place and with no exceptional set.  Both invariances are
already proven here: `charFrob_conj` (conjugation) and
`charFrob_baseChange` (base change), and `Polynomial.coeff_map` reads
the coefficient off the pushed-forward polynomial.  This is the
workhorse of the assembly below — it converts the isomorphism-level
clause of `IsStrictlyUniversalOnFramedFiniteLifts` into the trace-level
clauses of `IsWeaklyUniversalOnIdentifiedFiniteTests`, and the residual
identification of `ρuniv` into the reduction clause. -/
lemma coeff_one_charFrob_of_baseChange_conj {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra A B] [ContinuousSMul A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M]
    {N : Type*} [AddCommGroup N] [Module B N] [Module.Finite B N]
    [Module.Free B N]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (ρ : GaloisRep ℚ A M) {ρ' : GaloisRep ℚ B N}
    (e : (B ⊗[A] M) ≃ₗ[B] N) (he : (ρ.baseChange B).conj e = ρ') :
    (ρ'.charFrob v).coeff 1 = algebraMap A B ((ρ.charFrob v).coeff 1) := by
  subst he
  rw [charFrob_conj, charFrob_baseChange, Polynomial.coeff_map]

/-- **Schlessinger–Mazur arithmetic core of the finite-level leaf**
(sorry node — the arithmetic stratum of the Schlessinger cut of
2026-07-25): GIVEN the finiteness of the dual-number tangent space
(Schlessinger's H3), the framed hardly ramified lifting functor of an
irreducible hardly ramified `ρbar` has a hull in Mazur's category,
PRESENTED as a quotient of `ℤ_p[[x₁, …, x_g]]` and classifying the
objects of Schlessinger's category STRICTLY
(`IsStrictlyUniversalOnFramedFiniteLifts`: an honest conjugacy of
representations, not a trace clause).

Classical construction, stratum by stratum: (1) the framed hardly
ramified lifting functor on FINITE (Artinian) local `ℤ_p`-algebras
with residue field `k` satisfies Schlessinger's H1 and H2 — a fibre
product of coefficient rings carries the fibre product of the framed
lift sets, because a lift over `A₁ ×_{A₀} A₂` is exactly a compatible
pair of lifts (the frame rigidifies, so there is no gluing ambiguity),
and the local conditions are checked componentwise; its tangent space
is the dual-number lift set of `IsDualNumberTangentLift`, FINITE by the
hypothesis `hfin`, which is H3; `ρbar` is odd (cyclotomic determinant,
odd `p`), and an odd irreducible 2-dimensional representation over a
finite field of odd characteristic is absolutely irreducible, so
`End_{k[Γ]}(ρbar) = k` (Schur) and H4 holds — by Schlessinger's theorem
(Trans. AMS 130 (1968), Thm. 2.11) and Mazur (*Deforming Galois
representations*, MSRI Publ. 16 (1989), §1.2) the functor is
pro-representable and the framing is a torsor.  (2) The hardly ramified
conditions cut out a relatively representable closed subfunctor:
cyclotomic determinant and unramifiedness outside `2p` are limit-stable;
flatness at `p` in the `IsFlatAt` sense is Ramakrishna's flat condition
(Compositio 87 (1994)); the tame quadratic quotient at `2` is an
ordinary-type condition (Conrad–Diamond–Taylor, JAMS 12 (1999), §2; the
FLT blueprint's `S`-good theory at `S = {2}`).  (3) By de Smit–Lenstra
(*Explicit construction of universal deformation rings*, in
Cornell–Silverman–Stevens) the hull is a quotient of
`ℤ_p[[x₁, …, x_g]]`, `g = dim_k` of the tangent space (finite by
`hfin`) — the presentation surjection `pres` of the conclusion — and it
carries the `𝔪`-adic topology; the universal representation is hardly
ramified because each condition is, in the
`IsFlatAt`/inertia-kernel/quotient-character spelling, a limit of its
Artinian-quotient instances, and it is itself a lift of `ρbar` (the
residual identification clause).  (4) A residually identified framed
test lift over a FINITE local `ℤ_p`-algebra `A` is an object of
Schlessinger's category outright (Artinian local with nilpotent maximal
ideal, discrete), so it has a classifying map `ψ : Runiv →+* A`,
continuous and strict, with `ψ_*ρuniv ≅ ρA` (residual irreducibility
kills the framing ambiguity).

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability restricted to finite test
objects — WEAKER than the classical statement, which classifies the
whole complete-Noetherian category; abstractly the hypothesis set
contains an irreducible hardly ramified `ρbar`, which the section audit
of `Interface.lean` shows to be classically unsatisfiable, so the
statement is also classically true outright.  CIRCULARITY GUARD
(inherited): must not be proven through `Family.lean` or anything
downstream of it (`Lift.lean` included).

**VACUITY AUDIT** (2026-07-25 — the discharge actually formalized
below; read this before consuming the leaf).  This node is PROVEN
*vacuously* and carries NO deformation theory whatsoever.  The proof is
`exfalso` followed by the sanctioned odd-prime dichotomy already inlined
in this module for the Hecke generation leaf
`topologicalClosure_adjoin_charFrobCoeff_univ_eq_top` (proven the same
way a few hundred lines below, and whose ROUTE note carries the import
audit): the hypothesis package `Odd p` + `IsHardlyRamified hpodd hW
ρbar` + `ρbar.IsIrreducible` is REFUTABLE from material this module
already imports — at `p = 3` by `IsHardlyRamified.mod_three_reducible`
(`ModThree.lean`, the Fontaine/Odlyzko discriminant-bound route)
through `Slop.OddRep.isIrreducible_iff_forall`, and at `p ≥ 5` by the
Family-free Khare–Wintenberger headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`).  No new import is needed and no
new cycle is created; the circularity guard above is respected
(`Family.lean` and everything downstream of it is untouched).

WHICH HYPOTHESES THE PROOF USES.  Exactly the five that make up the
refuted package: `hpodd`, `[Fact p.Prime]`, `hW`, `hρbar`, `hirr`.
Schlessinger's H3 — the tangent finiteness — is NOT used, and is
underscore-prefixed (`_hfin`) so that the emptiness is mechanically
visible rather than merely asserted.  The consuming assembly still
supplies it positionally, so `finite_setOf_isHardlyRamified` and the
Hermite–Minkowski cone below it stay inside the root cone.

WHERE THE REAL MATHEMATICS LIVES — this node is a PARALLEL COPY.
`Fermat/FLT/GaloisRepresentation/HardlyRamified/Deformation.lean`
carries the same theorem in bundled vocabulary
(`IsStrictlyUniversalOnFrames` / `IsResidualIdentifiedFrame`,
`exists_isStrictlyUniversalOnFrames_of_finite_lifts`) and has ALREADY
been cut along the deformation-condition seam of Mazur §§18–23 and
Conrad–Diamond–Taylor §2: the arithmetic-free Schlessinger induction
plus de Smit–Lenstra presentation
(`exists_isStrictlyUniversalOnFrames_of_deformationCondition`), over
`isHardlyRamified_pushforwardFrame` (PROVEN — functoriality),
`isHardlyRamified_of_fibreProduct` (H1/H2),
`isHardlyRamified_of_forall_isOpen_quotient` (the pro-limit clause) and
`finite_setOf_isHardlyRamified_frames_of_discreteTopology` (H3).  That
copy is where the universal deformation ring is actually being built,
and it is IMPORTABLE from here — this module already reaches it through
`KhareWintenberger.lean`.  The intended endgame recorded in
`~/.flt-design-deformation-patching-dedup.md` is a module split that
makes the two statements one; a future NON-vacuous discharge of this
leaf should be that de-duplication, applying the imported twin, and NOT
a second Schlessinger development here.  Two gaps stand in the way of
applying the twin today, and they are the honest successor tasks:
(i) the twin carries `5 ≤ ℓ`, so `p = 3` would still need its own
input; (ii) the twin delivers `IsNoetherianRing` and `IsAdicComplete`
where this statement asks for the `ℤ_p[[x₁,…,x_g]]` presentation
surjection, so a Cohen-style "complete Noetherian local `ℤ_p`-algebra
with finite residue field is a quotient of a power series ring" bridge
is the missing commutative-algebra piece (the converse direction of the
two sibling leaves `isNoetherianRing_of_mvPowerSeries_presentation` and
`isAdicComplete_of_mvPowerSeries_presentation`). -/
theorem exists_framedStrictlyUniversal_hardlyRamified_finiteTests.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (_hfin : {ρε : GaloisRep ℚ (DualNumber k) (Fin 2 → DualNumber k) |
      IsDualNumberTangentLift hpodd ρbar ρε}.Finite) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (g : ℕ) (pres : MvPowerSeries (Fin g) ℤ_[p] →+* Runiv)
      (_ : Function.Surjective pres)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (_ : IsHardlyRamified hpodd (rank_finTwoFun Runiv) ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (hπcont : Continuous πuniv),
      (letI : Algebra Runiv k := πuniv.toAlgebra
       letI : ContinuousSMul Runiv k := continuousSMul_of_algebraMap Runiv k
         (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
       ∃ e : (k ⊗[Runiv] (Fin 2 → Runiv)) ≃ₗ[k] W,
         (ρuniv.baseChange k).conj e = ρbar) ∧
      IsStrictlyUniversalOnFramedFiniteLifts.{s, uK, uW, s} hpodd ρbar
        ρuniv πuniv := by
  exfalso
  -- the odd-prime dichotomy, inlined exactly as in the Hecke generation
  -- leaf `topologicalClosure_adjoin_charFrobCoeff_univ_eq_top` below
  -- (see the VACUITY AUDIT above)
  have hp := (Fact.out : p.Prime)
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · -- `p < 5`: primality and oddness force `p = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    have hp3 : p = 3 := by
      have := hp.two_le
      have := Nat.odd_iff.mp hpodd
      omega
    subst hp3
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
  · -- `p ≥ 5`: the Family-free Khare–Wintenberger headline
    exact absurd hirr
      (not_isIrreducible_of_isHardlyRamified_of_five_le hpodd h5 hW hρbar)

/-- **Noetherianity from a power-series presentation** (PROVEN
2026-07-25 — the first Mazur-category commutative-algebra stratum of
the Schlessinger cut of 2026-07-25): a surjective image of
`ℤ_p[[x₁, …, x_g]]` is Noetherian.  Pure commutative algebra with zero
arithmetic content: `ℤ_p` is Noetherian (a DVR), the power-series
Hilbert basis theorem gives `IsNoetherianRing (MvPowerSeries (Fin g)
ℤ_[p])` by induction on `g`, and Noetherianity passes to quotients
(`isNoetherianRing_of_surjective`).  DEDUPE NOTE (resolved 2026-07-25):
the induction was carried out in this file as
`isNoetherianRing_mvPowerSeries`, which is however declared far BELOW
this point (it belongs to the power-series section of the
Auslander–Buchsbaum endgame and depends on the `optionCurryEquiv`
machinery developed there); rather than relocate another owner's
section, the currying and the induction are now also available
UPSTREAM, in
`Fermat/FLT/Mathlib/RingTheory/PowerSeries/AdicComplete.lean`
(`PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries`), which the
adic-completeness stratum below needs anyway. -/
theorem isNoetherianRing_of_mvPowerSeries_presentation.{uR} {p : ℕ}
    [Fact p.Prime] {g : ℕ} {R : Type uR} [CommRing R]
    (pres : MvPowerSeries (Fin g) ℤ_[p] →+* R)
    (hpres : Function.Surjective pres) : IsNoetherianRing R := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin g) ℤ_[p]) :=
    PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries g
  exact isNoetherianRing_of_surjective _ _ pres hpres

/-- **Adic completeness from a power-series presentation** (PROVEN
2026-07-25 — the second Mazur-category commutative-algebra stratum of
the Schlessinger cut of 2026-07-25): a LOCAL ring that is a surjective
image of `ℤ_p[[x₁, …, x_g]]` is `𝔪`-adically complete.  Pure
commutative algebra with zero arithmetic content, and the classical
reason the de Smit–Lenstra presentation lands the universal ring in
Mazur's category.

The proof splits `IsAdicComplete` into its two halves.

*Hausdorff* is the cheap half and is mathlib's, once `R` is known
Noetherian: `IsHausdorff (maximalIdeal R) R` holds for every Noetherian
local ring (Krull intersection through `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`),
and `R` is Noetherian as a surjective image of the Noetherian
`ℤ_p[[x₁, …, x_g]]` (`isNoetherianRing_of_surjective` over
`PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries`, the
power-series Hilbert basis theorem by induction on the number of
variables).

*Precompleteness* is the substantial half and is NOT in mathlib —
mathlib knows only `IsAdicComplete (span (range X)) (MvPowerSeries σ R)`,
completeness for the ideal of the VARIABLES, whereas the maximal ideal
`(p, x₁, …, x_g)` induces a strictly finer topology.  It is developed in
`Fermat/FLT/Mathlib/RingTheory/PowerSeries/AdicComplete.lean` around the
exact coefficientwise description of the powers of the maximal ideal of
`B⟦X⟧` over a local `B`,
`f ∈ 𝔪_{B⟦X⟧}^n ↔ ∀ j < n, coeff j f ∈ 𝔪_B^(n-j)`
(`PowerSeriesAdicComplete.mem_maximalIdeal_pow_powerSeries`): the upper
bound is an induction on `n` over the Cauchy product, the lower bound
splits off the polynomial part of degree `< n` and divides the rest by
`X^n`.  Precompleteness of `B⟦X⟧` is then a coefficientwise limit
(`isPrecomplete_powerSeries`), the number of variables is stripped by
the currying isomorphism
`MvPowerSeries (Option σ) A ≃+* (MvPowerSeries σ A)⟦X⟧`
(`isPrecomplete_mvPowerSeries`), and precompleteness descends along a
surjection with the image ideal by lifting the successive differences of
a Cauchy sequence into `𝔪_S^n` (`isPrecomplete_of_surjective`).  Since
`pres` is a surjection of local rings it is automatically local, so
`𝔪_S` maps ONTO `𝔪_R` (`IsLocalRing.map_maximalIdeal_of_surjective`) and
the image filtration is the `𝔪_R`-adic one. -/
theorem isAdicComplete_of_mvPowerSeries_presentation.{uR} {p : ℕ}
    [Fact p.Prime] {g : ℕ} {R : Type uR} [CommRing R] [IsLocalRing R]
    (pres : MvPowerSeries (Fin g) ℤ_[p] →+* R)
    (hpres : Function.Surjective pres) :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin g) ℤ_[p]) :=
    PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries g
  haveI : IsNoetherianRing R := isNoetherianRing_of_surjective _ _ pres hpres
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) ℤ_[p]))
      (MvPowerSeries (Fin g) ℤ_[p]) :=
    PowerSeriesAdicComplete.isPrecomplete_mvPowerSeries g
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal R) R := by
    have h := PowerSeriesAdicComplete.isPrecomplete_of_surjective
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin g) ℤ_[p])) pres hpres
    rwa [IsLocalRing.map_maximalIdeal_of_surjective pres hpres] at h
  exact ⟨⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Schlessinger–Ramakrishna–CDT finite-level leaf** (DECOMPOSED
2026-07-25, SCHLESSINGER cut — the assembly below is PROVEN over the
arithmetic core `exists_framedStrictlyUniversal_hardlyRamified_finiteTests`
(Schlessinger H1/H2 on framed lifts, H3 = `hfin`, H4 through Schur,
Ramakrishna's flat condition at `p`, CDT's tame condition at `2`, de
Smit–Lenstra presentation) and the two Mazur-category
commutative-algebra leaves `isNoetherianRing_of_mvPowerSeries_presentation`
and `isAdicComplete_of_mvPowerSeries_presentation`): GIVEN the
finiteness of the dual-number tangent space (Schlessinger's H3), the
hardly ramified deformation problem of an irreducible hardly ramified
`ρbar` admits a Mazur-category package `(Runiv, ρuniv, πuniv)` —
complete Noetherian local topological `ℤ_p`-algebra with the `𝔪`-adic
topology, hardly ramified universal representation on the standard
frame, surjective reduction matching linear `charFrob` coefficients off
a finite set — that factors every residually identified
standard-framed test deformation with FINITE coefficient ring
(`IsWeaklyUniversalOnIdentifiedFiniteTests`; the pro-finite upgrade
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests` extends the
factorization to the full module-finite test category, so this leaf
carries no limit stratum: its test objects are the finite discrete
coefficient rings on which the lifting functor is finite
combinatorics).

The glue proven here is the passage from the classical
ISOMORPHISM-level universal property to the trace-level clauses of this
module's vocabulary, plus the collapse onto the standard frame.  (a)
The Mazur-category ring clauses `IsNoetherianRing` and
`IsAdicComplete` are read off the de Smit–Lenstra presentation
surjection `ℤ_p[[x₁, …, x_g]] ↠ Runiv` supplied by the core leaf, by
the two commutative-algebra leaves.  (b) The reduction clause holds
with EMPTY exceptional set: the core leaf's residual identification
exhibits `ρuniv ⊗_{Runiv} k` as conjugate to `ρbar`, and
`coeff_one_charFrob_of_baseChange_conj` (base-change and conjugation
invariance of `charFrob`) turns that isomorphism into equality of the
linear `charFrob` coefficients through `πuniv`, at every prime.  (c) A
residually identified test deformation `D` with `Finite D.A` is first
REFRAMED onto the standard frame `Fin 2 → D.A` (`reframe`, with
`IsResidualIdentified.reframe` transporting its identification and
`isHardlyRamified_conj` its local conditions), which makes it an object
of Schlessinger's category in the raw shape the core leaf's strict
clause quantifies over; the resulting classifying map `ψ` is already
`ℤ_p`-compatible and reduction-compatible, and its representation
clause `ψ_*ρuniv ≅ D.ρ.conj (reframeEquiv)` gives, again by
`coeff_one_charFrob_of_baseChange_conj` and `charFrob_conj`, the trace
clause at EVERY prime — the uniformity in the test object that the
pro-finite limit upgrade consumes essentially.

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability restricted to finite
test objects — WEAKER than the classical statement, which factors the
whole complete-Noetherian category; abstractly the hypothesis set
contains an irreducible hardly ramified `ρbar`, which the section
audit of `Interface.lean` shows to be classically unsatisfiable, so
the statement is also classically true outright.  CIRCULARITY GUARD
(inherited): must not be proven through `Family.lean` or anything
downstream of it (`Lift.lean` included). -/
theorem exists_weaklyUniversalOnIdentified_framed_finiteTests.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (hfin : {ρε : GaloisRep ℚ (DualNumber k) (Fin 2 → DualNumber k) |
      IsDualNumberTangentLift hpodd ρbar ρε}.Finite) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalOnIdentifiedFiniteTests.{s, uK, uW, s} hpodd ρbar
        ρuniv πuniv := by
  obtain ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, hadic, g, pres, hpres, ρuniv,
    hHRuniv, πuniv, hπsurj, hπcont, hiduniv, hstrict⟩ :=
    exists_framedStrictlyUniversal_hardlyRamified_finiteTests.{s, uK, uW}
      hpodd hW hρbar hirr hfin
  letI := iCR
  letI := iTS
  letI := iTR
  letI := iLR
  letI := iAlg
  -- (a) the Mazur-category ring clauses, from the de Smit–Lenstra presentation
  haveI hNoeth : IsNoetherianRing Runiv :=
    isNoetherianRing_of_mvPowerSeries_presentation pres hpres
  haveI hComplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv :=
    isAdicComplete_of_mvPowerSeries_presentation pres hpres
  letI : Algebra Runiv k := πuniv.toAlgebra
  letI : ContinuousSMul Runiv k := continuousSMul_of_algebraMap Runiv k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
  obtain ⟨euniv, heuniv⟩ := hiduniv
  refine ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, hNoeth, hadic, hComplete, ρuniv,
    rank_finTwoFun Runiv, hHRuniv, πuniv, hπsurj, ∅, ?_, ?_⟩
  · -- (b) the reduction clause, with EMPTY exceptional set
    intro q hq _
    have hred := coeff_one_charFrob_of_baseChange_conj
      hq.toHeightOneSpectrumRingOfIntegersRat ρuniv euniv heuniv
    rw [hred, RingHom.algebraMap_toAlgebra]
  · -- (c) the universality clause on identified FINITE tests
    intro D hDfin hDid
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.moduleFinite
    letI := D.isModuleTopology
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    haveI : Finite D.A := hDfin
    -- reframe the test deformation onto the standard frame `Fin 2 → D.A`
    obtain ⟨ψ, hψcont, hψalg, hψred, hψconj⟩ :=
      hstrict D.A (D.ρ.conj D.reframeEquiv)
        (isHardlyRamified_conj (rank_finTwoFun D.A) D.isHardlyRamified
          D.reframeEquiv)
        D.π D.π_surjective hDid.reframe
    refine ⟨ψ, hψalg, hψred, fun q hq => ?_⟩
    letI : Algebra Runiv D.A := ψ.toAlgebra
    letI : ContinuousSMul Runiv D.A := continuousSMul_of_algebraMap Runiv D.A
      (by rw [RingHom.algebraMap_toAlgebra]; exact hψcont)
    obtain ⟨e, he⟩ := hψconj
    have htr := coeff_one_charFrob_of_baseChange_conj
      hq.toHeightOneSpectrumRingOfIntegersRat ρuniv e he
    rw [charFrob_conj] at htr
    rw [htr, RingHom.algebraMap_toAlgebra]

/-!
## The `p`-adic tower of a module-finite local `ℤ_p`-algebra

The pro-finite upgrade
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests` below runs the
classical "continuity of the deformation functor" argument (Mazur §1.2)
over the `p`-adic filtration `pⁿ⁺¹A` of the coefficient ring `A = D.A`
of a test deformation, rather than over its `𝔪`-adic filtration: for a
module-finite `ℤ_p`-algebra the two are cofinal, and the `p`-adic one
comes with its completeness for free from `IsAdicComplete.of_finite_module`
over the complete discrete valuation ring `ℤ_p`.  This block develops
what the upgrade consumes, all of it pure commutative algebra:

* `padicTowerIdeal p A n = pⁿ⁺¹A` (indexed from `1` so that every step
  is a PROPER ideal — `padicTowerIdeal_ne_top`, Nakayama), with its
  antitonicity and its identification with the adic filtration
  `(𝔪_{ℤ_p})ⁿ⁺¹ • ⊤` in which mathlib phrases completeness;
* finiteness (`finite_quotient_padicTowerIdeal`) and locality
  (`isLocalRing_quotient_padicTowerIdeal`) of the quotients `A/pⁿ⁺¹A`,
  so that they are legitimate ARTINIAN test objects;
* Krull separatedness (`eq_zero_of_forall_mem_padicTowerIdeal`,
  `eq_of_forall_mk_padicTowerIdeal_eq`) and completeness
  (`exists_forall_sub_mem_padicTowerIdeal`) of the tower;
* finiteness of the classifying sets
  (`finite_setOf_ringHom_comp_eq`): a ring map out of a Noetherian
  local ring compatible with the residue maps kills `𝔪ᶜ` for the
  nilpotence exponent `c` of the finite target, hence factors through
  the FINITE ring `R/𝔪ᶜ`;
* König (`exists_tower_of_forall_nonempty_finite`) and the adic
  assembly (`exists_ringHom_of_tower`).
-/

section ProfinitePadicTower

open IsLocalRing

universe uTA uTR

/-- **The `p`-adic tower ideal** `pⁿ⁺¹·A` of a `ℤ_p`-algebra `A`,
presented as the extension of `(𝔪_{ℤ_p})ⁿ⁺¹` — the shape in which
mathlib's adic filtration `I ^ n • ⊤` appears, so that the
completeness of `A` as a `ℤ_p`-module transfers to the tower without
any translation.  The index is shifted by one so that EVERY step of
the tower is a proper ideal (`padicTowerIdeal_ne_top`): the `0`-th
unshifted step would be `⊤`, whose quotient is the zero ring and
carries no residue map to `k`. -/
noncomputable def padicTowerIdeal (p : ℕ) [Fact p.Prime] (A : Type uTA)
    [CommRing A] [Algebra ℤ_[p] A] (n : ℕ) : Ideal A :=
  Ideal.map (algebraMap ℤ_[p] A) (maximalIdeal ℤ_[p] ^ (n + 1))

variable {p : ℕ} [Fact p.Prime] {A : Type uTA} [CommRing A] [Algebra ℤ_[p] A]

/-- The tower is antitone: `pⁿ⁺¹A ⊆ pᵐ⁺¹A` for `m ≤ n`. -/
theorem padicTowerIdeal_antitone {m n : ℕ} (h : m ≤ n) :
    padicTowerIdeal p A n ≤ padicTowerIdeal p A m :=
  Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

/-- The tower ideal is the adic filtration step `(𝔪_{ℤ_p})ⁿ⁺¹ • ⊤`
of `A` as a `ℤ_p`-module (`Ideal.smul_top_eq_map`). -/
theorem mem_padicTowerIdeal_iff {n : ℕ} {x : A} :
    x ∈ padicTowerIdeal p A n ↔
      x ∈ (maximalIdeal ℤ_[p] ^ (n + 1)) • (⊤ : Submodule ℤ_[p] A) := by
  rw [Ideal.smul_top_eq_map]; exact Iff.rfl

/-- Membership in a tower ideal gives membership in every coarser
adic filtration step. -/
theorem mem_smul_top_of_mem_padicTowerIdeal {m n : ℕ} (h : m ≤ n + 1) {x : A}
    (hx : x ∈ padicTowerIdeal p A n) :
    x ∈ (maximalIdeal ℤ_[p] ^ m) • (⊤ : Submodule ℤ_[p] A) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (mem_padicTowerIdeal_iff.mp hx)

/-- **`ℤ_p/pᵐ` is finite**: it is the image of the surjection
`PadicInt.toZModPow m` onto `ZMod (pᵐ)`, whose kernel is `(p^m)`
(`PadicInt.ker_toZModPow`) and `𝔪_{ℤ_p} = (p)`. -/
theorem finite_quotient_padicInt_maximalIdeal_pow (p : ℕ) [Fact p.Prime] (m : ℕ) :
    Finite (ℤ_[p] ⧸ (maximalIdeal ℤ_[p]) ^ m) := by
  have h1 : (maximalIdeal ℤ_[p]) ^ m = RingHom.ker (PadicInt.toZModPow m) := by
    rw [PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, ← Ideal.span_singleton_pow]
  rw [h1]
  exact Finite.of_equiv _ (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow m))).symm.toEquiv

/-- **The tower quotients are finite**: `A/pⁿ⁺¹A` is a module-finite
algebra over the finite ring `ℤ_p/(comap of pⁿ⁺¹A)`, a quotient of the
finite `ℤ_p/pⁿ⁺¹`.  This is what makes each `A/pⁿ⁺¹A` an ARTINIAN test
object of Schlessinger's category. -/
instance finite_quotient_padicTowerIdeal [Module.Finite ℤ_[p] A] (n : ℕ) :
    Finite (A ⧸ padicTowerIdeal p A n) := by
  haveI := finite_quotient_padicInt_maximalIdeal_pow p (n + 1)
  set C : Ideal ℤ_[p] := Ideal.comap (algebraMap ℤ_[p] A) (padicTowerIdeal p A n)
  have hle : (maximalIdeal ℤ_[p]) ^ (n + 1) ≤ C := Ideal.le_comap_map
  haveI : Finite (ℤ_[p] ⧸ C) :=
    Finite.of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)
  haveI : Module.Finite ℤ_[p] (A ⧸ padicTowerIdeal p A n) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (ℤ_[p] ⧸ C) (A ⧸ padicTowerIdeal p A n) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  exact Module.finite_of_finite (ℤ_[p] ⧸ C)

/-- **The tower ideals are proper** — Nakayama over the local ring
`ℤ_p`: if `pA = A` then the finite `ℤ_p`-module `A` vanishes,
contradicting nontriviality. -/
theorem padicTowerIdeal_ne_top [Module.Finite ℤ_[p] A] [Nontrivial A] (n : ℕ) :
    padicTowerIdeal p A n ≠ ⊤ := by
  intro htop
  have hsm : (⊤ : Submodule ℤ_[p] A) ≤ (maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] A) := by
    intro x _
    have hx : x ∈ padicTowerIdeal p A n := by rw [htop]; trivial
    exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
      (mem_padicTowerIdeal_iff.mp hx)
  have hbot : (⊤ : Submodule ℤ_[p] A) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal ℤ_[p]) ⊤
      Module.Finite.fg_top hsm
      (le_of_eq (jacobson_eq_maximalIdeal (⊥ : Ideal ℤ_[p]) bot_ne_top).symm)
  have h1 : (1 : A) ∈ (⊥ : Submodule ℤ_[p] A) := hbot ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at h1
  exact one_ne_zero h1

/-- **The tower quotients are local rings**: quotients of a local ring
by a proper ideal. -/
instance isLocalRing_quotient_padicTowerIdeal [Module.Finite ℤ_[p] A] [IsLocalRing A]
    (n : ℕ) : IsLocalRing (A ⧸ padicTowerIdeal p A n) :=
  haveI : Nontrivial (A ⧸ padicTowerIdeal p A n) :=
    Ideal.Quotient.nontrivial_iff.mpr (padicTowerIdeal_ne_top n)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

section Complete

variable [Module.Finite ℤ_[p] A]

/-- **Krull separatedness of the tower**: `⋂ₙ pⁿA = 0`, by the
Hausdorffness half of `IsAdicComplete.of_finite_module`. -/
theorem eq_zero_of_forall_mem_padicTowerIdeal {x : A}
    (hx : ∀ n, x ∈ padicTowerIdeal p A n) : x = 0 := by
  haveI : IsAdicComplete (maximalIdeal ℤ_[p]) A := IsAdicComplete.of_finite_module
  refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal ℤ_[p]) A) x fun n => ?_
  rw [SModEq.sub_mem, sub_zero]
  exact mem_smul_top_of_mem_padicTowerIdeal (Nat.le_succ n) (hx n)

/-- Separatedness in the form the assembly uses: two elements with the
same image at every level of the tower are equal. -/
theorem eq_of_forall_mk_padicTowerIdeal_eq {x y : A}
    (h : ∀ n, Ideal.Quotient.mk (padicTowerIdeal p A n) x
      = Ideal.Quotient.mk (padicTowerIdeal p A n) y) : x = y :=
  sub_eq_zero.mp (eq_zero_of_forall_mem_padicTowerIdeal fun n =>
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (h n))

/-- **Completeness of the tower**: a sequence that is compatible along
the tower converges, by the precompleteness half of
`IsAdicComplete.of_finite_module`.  (The index shift between the tower
`pⁿ⁺¹A` and mathlib's filtration `(𝔪_{ℤ_p})ⁿ • ⊤` is absorbed by
reading the limit off one level further down.) -/
theorem exists_forall_sub_mem_padicTowerIdeal (f : ℕ → A)
    (hf : ∀ m n : ℕ, m ≤ n → f n - f m ∈ padicTowerIdeal p A m) :
    ∃ L : A, ∀ n, L - f n ∈ padicTowerIdeal p A n := by
  haveI : IsAdicComplete (maximalIdeal ℤ_[p]) A := IsAdicComplete.of_finite_module
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal ℤ_[p]) (M := A) inferInstance
    (f := f) (fun {m n} hmn => by
      rw [SModEq.sub_mem, ← neg_sub]
      exact Submodule.neg_mem _
        (mem_smul_top_of_mem_padicTowerIdeal (Nat.le_succ m) (hf m n hmn)))
  refine ⟨L, fun n => ?_⟩
  have h1 : f (n + 1) - L ∈ (maximalIdeal ℤ_[p] ^ (n + 1)) • (⊤ : Submodule ℤ_[p] A) :=
    (SModEq.sub_mem).mp (hL (n + 1))
  have h2 : f (n + 1) - f n ∈ padicTowerIdeal p A n := hf n (n + 1) (Nat.le_succ n)
  have h3 : L - f n = (f (n + 1) - f n) - (f (n + 1) - L) := by ring
  rw [h3, mem_padicTowerIdeal_iff]
  exact Submodule.sub_mem _ (mem_padicTowerIdeal_iff.mp h2) h1

end Complete

/-- **Finiteness of the classifying sets** — the König input: for a
NOETHERIAN local `R` and a FINITE local `S` with a common residue
field `k`, only finitely many ring maps `R →+* S` are compatible with
the two residue maps.  Indeed such a `ψ` is local (`πS ∘ ψ = πR` forces
`ψ(𝔪_R) ⊆ ker πS = 𝔪_S`), and `𝔪_S` is nilpotent (`S` is finite, hence
artinian), so `ψ` kills `𝔪_R ^ c` and factors through `R/𝔪_R^c`, which
is FINITE (`Ideal.finite_quotient_pow`, `R` Noetherian with finite
residue field). -/
theorem finite_setOf_ringHom_comp_eq {R : Type uTR} {S : Type uTA} {k : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [CommRing S] [Finite S] [IsLocalRing S] [Field k]
    {πR : R →+* k} (hπR : Function.Surjective πR) {πS : S →+* k}
    (hπS : Function.Surjective πS) :
    {ψ : R →+* S | πS.comp ψ = πR}.Finite := by
  classical
  haveI : IsArtinianRing S := isArtinian_of_finite
  have hkR : RingHom.ker πR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πR hπR)
  have hkS : RingHom.ker πS = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πS hπS)
  haveI : Finite k := Finite.of_surjective πS hπS
  haveI : Finite (R ⧸ maximalIdeal R) := by
    rw [← hkR]
    exact Finite.of_equiv _ (RingHom.quotientKerEquivOfSurjective hπR).symm.toEquiv
  obtain ⟨c, hc⟩ : IsNilpotent (maximalIdeal S) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := S)
    rwa [jacobson_eq_maximalIdeal (⊥ : Ideal S) bot_ne_top] at h
  haveI : Finite (R ⧸ (maximalIdeal R) ^ c) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) c
  haveI : Finite ((R ⧸ (maximalIdeal R) ^ c) →+* S) :=
    Finite.of_injective (fun f => (f : (R ⧸ (maximalIdeal R) ^ c) → S))
      fun _ _ h => DFunLike.coe_injective h
  have hkill : ∀ ψ : R →+* S, πS.comp ψ = πR → ∀ a ∈ (maximalIdeal R) ^ c, ψ a = 0 := by
    intro ψ hψ a ha
    have hmaple : Ideal.map ψ (maximalIdeal R) ≤ maximalIdeal S := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, ← hkS, RingHom.mem_ker, ← RingHom.comp_apply, hψ, ← RingHom.mem_ker,
        hkR]
      exact hx
    have h2 : (Ideal.map ψ (maximalIdeal R)) ^ c ≤ (maximalIdeal S) ^ c :=
      pow_le_pow_left' hmaple c
    have h4 : ψ a ∈ (maximalIdeal S) ^ c := by
      refine h2 ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    rw [hc] at h4
    simpa using h4
  have hinj : Function.Injective (fun ψ : {ψ : R →+* S | πS.comp ψ = πR} =>
      Ideal.Quotient.lift ((maximalIdeal R) ^ c) ψ.1 (hkill ψ.1 ψ.2)) := by
    intro ψ₁ ψ₂ h
    refine Subtype.ext (RingHom.ext fun r => ?_)
    have h' := RingHom.congr_fun h (Ideal.Quotient.mk ((maximalIdeal R) ^ c) r)
    simpa using h'
  haveI : Finite ↥{ψ : R →+* S | πS.comp ψ = πR} := Finite.of_injective _ hinj
  exact Set.toFinite _

/-- The transition map of the tower at a level is the identity. -/
theorem padicTowerIdeal_factor_self {n : ℕ}
    (H : padicTowerIdeal p A n ≤ padicTowerIdeal p A n) (y : A ⧸ padicTowerIdeal p A n) :
    Ideal.Quotient.factor H y = y := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  rw [← hx, Ideal.Quotient.factor_mk]

/-- The transition maps of the tower compose. -/
theorem padicTowerIdeal_factor_factor {l m n : ℕ}
    (H1 : padicTowerIdeal p A m ≤ padicTowerIdeal p A l)
    (H2 : padicTowerIdeal p A n ≤ padicTowerIdeal p A m)
    (H3 : padicTowerIdeal p A n ≤ padicTowerIdeal p A l)
    (y : A ⧸ padicTowerIdeal p A n) :
    Ideal.Quotient.factor H1 (Ideal.Quotient.factor H2 y) = Ideal.Quotient.factor H3 y := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  rw [← hx, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

section Tower

variable {R : Type uTR} [CommRing R]

open CategoryTheory in
/-- **König's lemma along the tower**: an inverse system of NONEMPTY
FINITE sets of level-wise ring maps, stable under the transition maps,
has a compatible section (`nonempty_sections_of_finite_inverse_system`
applied to the evident functor `ℕᵒᵖ ⥤ Type`). -/
theorem exists_tower_of_forall_nonempty_finite
    (X : ∀ n : ℕ, Set (R →+* A ⧸ padicTowerIdeal p A n))
    (hne : ∀ n, (X n).Nonempty) (hfin : ∀ n, (X n).Finite)
    (hstab : ∀ (m n : ℕ) (h : m ≤ n) (ψ : R →+* A ⧸ padicTowerIdeal p A n), ψ ∈ X n →
      (Ideal.Quotient.factor (padicTowerIdeal_antitone h)).comp ψ ∈ X m) :
    ∃ ψ : (n : ℕ) → (R →+* A ⧸ padicTowerIdeal p A n), (∀ n, ψ n ∈ X n) ∧
      ∀ (m n : ℕ) (h : m ≤ n),
        (Ideal.Quotient.factor (padicTowerIdeal_antitone h)).comp (ψ n) = ψ m := by
  let F : ℕᵒᵖ ⥤ Type (max uTA uTR) :=
    { obj := fun n => ↥(X n.unop)
      map := fun {m n} f => ↾ (fun ψ =>
        ⟨(Ideal.Quotient.factor (padicTowerIdeal_antitone (le_of_op_hom f))).comp ψ.1,
          hstab _ _ (le_of_op_hom f) ψ.1 ψ.2⟩)
      map_id := fun n => by
        ext ψ r
        exact padicTowerIdeal_factor_self (le_refl _) (ψ.1 r)
      map_comp := fun {l m n} f g => by
        ext ψ r
        exact (padicTowerIdeal_factor_factor (padicTowerIdeal_antitone (le_of_op_hom g))
          (padicTowerIdeal_antitone (le_of_op_hom f))
          (padicTowerIdeal_antitone ((le_of_op_hom g).trans (le_of_op_hom f)))
          (ψ.1 r)).symm }
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  exact ⟨fun n => (s (Opposite.op n)).1, fun n => (s (Opposite.op n)).2,
    fun m n h => congrArg Subtype.val (hs (Quiver.Hom.op (homOfLE h)))⟩

/-- **`p`-adic assembly of a compatible tower of ring maps**: a
compatible system of ring maps into the tower quotients comes from a
single ring map into `A`, by completeness (existence of the limit
value) and separatedness (its uniqueness, whence multiplicativity and
additivity of the assembled map). -/
theorem exists_ringHom_of_tower [Module.Finite ℤ_[p] A]
    (ψ : (n : ℕ) → (R →+* A ⧸ padicTowerIdeal p A n))
    (hcomp : ∀ (m n : ℕ) (h : m ≤ n),
      (Ideal.Quotient.factor (padicTowerIdeal_antitone h)).comp (ψ n) = ψ m) :
    ∃ Ψ : R →+* A, ∀ (n : ℕ) (r : R),
      Ideal.Quotient.mk (padicTowerIdeal p A n) (Ψ r) = ψ n r := by
  classical
  have huniq : ∀ x y : A, (∀ n, Ideal.Quotient.mk (padicTowerIdeal p A n) x
      = Ideal.Quotient.mk (padicTowerIdeal p A n) y) → x = y :=
    fun _ _ h => eq_of_forall_mk_padicTowerIdeal_eq h
  choose g hg using fun (r : R) (n : ℕ) =>
    Ideal.Quotient.mk_surjective (I := padicTowerIdeal p A n) (ψ n r)
  have hgstep : ∀ (r : R) (m n : ℕ), m ≤ n → g r n - g r m ∈ padicTowerIdeal p A m := by
    intro r m n h
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have h1 : Ideal.Quotient.mk (padicTowerIdeal p A m) (g r n)
        = Ideal.Quotient.factor (padicTowerIdeal_antitone h)
            (Ideal.Quotient.mk (padicTowerIdeal p A n) (g r n)) :=
      (Ideal.Quotient.factor_mk _ _).symm
    rw [h1, hg r n, hg r m, ← RingHom.comp_apply, hcomp m n h]
  choose L hL using fun r : R => exists_forall_sub_mem_padicTowerIdeal (g r) (hgstep r)
  have hLmk : ∀ (r : R) (n : ℕ),
      Ideal.Quotient.mk (padicTowerIdeal p A n) (L r) = ψ n r := by
    intro r n
    rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hL r n), hg r n]
  exact ⟨{ toFun := L
           map_one' := huniq _ _ fun n => by rw [hLmk, map_one, map_one]
           map_mul' := fun a b => huniq _ _ fun n => by
             rw [hLmk, map_mul, map_mul, hLmk, hLmk]
           map_zero' := huniq _ _ fun n => by rw [hLmk, map_zero, map_zero]
           map_add' := fun a b => huniq _ _ fun n => by
             rw [hLmk, map_add, map_add, hLmk, hLmk] }, fun n r => hLmk r n⟩

end Tower

end ProfinitePadicTower

/-- **Quotient-tower classifying maps** (sorry node — the ONLY
remaining stratum of the pro-finite upgrade
`isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests` below, whose
other three strata — finiteness of the classifying sets, König, and
the `p`-adic assembly with its clause passage — are PROVEN over the
tower vocabulary above): the finite-tests universality of
`(Runiv, ρuniv, πuniv)` produces a classifying map at every level of
the `p`-adic tower of a residually identified test deformation `D`,
compatible with the `ℤ_p`-structures, with the level-`n` reduction map
`A/pⁿ⁺¹A →+* k` induced by `D.π`, and with the linear `charFrob`
coefficients at EVERY prime.

Classical proof (step (1) of the upgrade's docstring, QUOTIENT TOWER,
together with the nonemptiness half of step (2)): base-change `D`
along the surjection `D.A ↠ D.A/pⁿ⁺¹D.A` onto a FINITE local
`ℤ_p`-algebra (finite by `finite_quotient_padicTowerIdeal`, local by
`isLocalRing_quotient_padicTowerIdeal`, and carrying the discrete
topology, which is its `ℤ_p`-module topology since it is finite and
`p`-power torsion).  The hardly ramified conditions push forward along
this surjective base change: the determinant clause and the tame
quotient at `2` transport by functoriality of `baseChange`
(`LinearMap.det_baseChange`, base change of the quotient character),
unramifiedness outside `2p` is the existing base-change instance
`GaloisRep.IsUnramifiedAt` of `baseChange`, and flatness at `p` is
preserved because the open ideals of the finite discrete quotient pull
back to open ideals of `D.A` — `IsFlatAt` is a condition on ALL
Artinian quotients, so it is inherited by any further quotient.  The
residual identification composes with the canonical isomorphism
`k ⊗_{A/pⁿ⁺¹A} ((A/pⁿ⁺¹A) ⊗_A V) ≅ k ⊗_A V`, and the residual
`charFrob` datum transports by `charFrob_baseChange`.  Applying the
finite-tests hypothesis `h` to the resulting Artinian test deformation
gives the classifying map, whose three clauses are exactly the three
clauses below (the trace clause holds at every prime with no
exceptional set, which is why
`IsWeaklyUniversalOnIdentifiedFiniteTests` is stated with that
strengthening).

Both-ways audit: a base-change statement about abstract packages, with
no arithmetic content beyond that of the finite-tests hypothesis it
consumes; classically true outright as stated.  CIRCULARITY GUARD
(inherited): must not be proven through `Family.lean` or anything
downstream of it (`Lift.lean` included). -/
theorem exists_ringHom_quotient_padicTower_of_finiteTests.{s, uK, uW, uR}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)} {πuniv : Runiv →+* k}
    (h : IsWeaklyUniversalOnIdentifiedFiniteTests.{s, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    (D : HardlyRamifiedFiniteDeformation.{s, s, uK, uW} hpodd ρbar)
    (hDid : D.IsResidualIdentified) (n : ℕ) :
    letI := D.commRing
    letI := D.topologicalSpace
    letI := D.isTopologicalRing
    letI := D.isLocalRing
    letI := D.algebra
    letI := D.addCommGroup
    letI := D.module
    letI := D.moduleFiniteVd
    letI := D.moduleFreeVd
    ∀ hker : ∀ a ∈ padicTowerIdeal p D.A n, D.π a = 0,
      ∃ ψ : Runiv →+* (D.A ⧸ padicTowerIdeal p D.A n),
        ψ.comp (algebraMap ℤ_[p] Runiv) =
            algebraMap ℤ_[p] (D.A ⧸ padicTowerIdeal p D.A n) ∧
          (Ideal.Quotient.lift (padicTowerIdeal p D.A n) D.π hker).comp ψ = πuniv ∧
          ∀ (q : ℕ) (hq : q.Prime),
            ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
              Ideal.Quotient.mk (padicTowerIdeal p D.A n)
                ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :=
  sorry

/-- **Pro-finite limit upgrade** (PROVEN 2026-07-25 over the single
quotient-tower leaf `exists_ringHom_quotient_padicTower_of_finiteTests`
— the limit stratum of the strict Mazur core, after the LEVEL cut of
2026-07-24): a
Noetherian package that factors every residually identified
standard-framed test deformation with FINITE coefficient ring factors
every one with module-finite coefficient ring.  This is the
"continuity of the deformation functor" half of the classical
representability proof (Mazur §1.2; Schlessinger's functors are
extended from Artinian test rings to complete local ones by passage to
the limit), isolated from the Artinian-level combinatorics.

Proof, stratum by stratum — run over the `p`-ADIC tower `pⁿ⁺¹A`
(`padicTowerIdeal`) rather than the `𝔪`-adic one: for a module-finite
`ℤ_p`-algebra the two filtrations are cofinal, and the `p`-adic one is
complete and separated for free, by `IsAdicComplete.of_finite_module`
over the complete discrete valuation ring `ℤ_p`.  Each quotient
`A/pⁿ⁺¹A` is a FINITE local ring (`finite_quotient_padicTowerIdeal`,
`isLocalRing_quotient_padicTowerIdeal`; properness of the tower ideals
is Nakayama), i.e. an Artinian test object, and the kernel of the
surjective `D.π` onto the field `k` is a maximal ideal, hence THE
maximal ideal, so every tower ideal is killed by `D.π` and induces a
level reduction map `πₙ : A/pⁿ⁺¹A →+* k`.

(1) QUOTIENT TOWER — the one remaining leaf,
`exists_ringHom_quotient_padicTower_of_finiteTests`: base-changing `D`
along `A →+* A/pⁿ⁺¹A` yields residually identified test deformations
`Dₙ` with finite coefficient rings (the hardly ramified conditions
push forward along surjective base change, and the residual
identification composes with the canonical isomorphism
`k ⊗[A] ((A/pⁿ⁺¹A) ⊗_{A/pⁿ⁺¹A} –) ≅ k ⊗[A] –`), whence by the
finite-tests hypothesis a level-`n` classifying map.  (2) FINITENESS
OF CLASSIFYING SETS (PROVEN, `finite_setOf_ringHom_comp_eq`): let `Xₙ`
be the set of `ψₙ : Runiv →+* A/pⁿ⁺¹A` satisfying the three clauses at
level `n`; each is nonempty by (1) and FINITE — any such `ψₙ` is local
(`πₙ ∘ ψₙ = πuniv` forces `ψₙ(𝔪_R) ⊆ ker πₙ = 𝔪_{A/pⁿ⁺¹A}`), and that
maximal ideal is nilpotent (a finite ring is artinian), so `ψₙ`
factors through `Runiv/𝔪_Runiv^c` — a FINITE ring by
`Ideal.finite_quotient_pow`, `Runiv` being Noetherian local with
finite residue field `k` via the surjective `πuniv` — and there are
only finitely many maps out of a finite ring.  (3) KÖNIG (PROVEN,
`exists_tower_of_forall_nonempty_finite`): the `Xₙ` with the
postcomposition transition maps form an inverse system of nonempty
finite sets (each clause is preserved by postcomposition — the trace
clause because it holds at EVERY prime, uniformly in `n`), so its
limit is nonempty (`nonempty_sections_of_finite_inverse_system`); a
compatible system `(ψₙ)` assembles to `Ψ : Runiv →+* A` by
completeness (`exists_ringHom_of_tower`), its ring-map axioms being
forced by separatedness.  (4) CLAUSE PASSAGE TO THE LIMIT (PROVEN):
the `ℤ_p`-clause and the trace clause for `Ψ` hold modulo `pⁿ⁺¹` for
every `n`, hence hold in `A` by Krull separatedness (`⋂ₙ pⁿA = 0`,
`eq_of_forall_mk_padicTowerIdeal_eq`), while the reduction clause is
read off a single level through `πₙ ∘ mk = D.π`; the exceptional set
of the conclusion's trace clause is `∅`.

Both-ways audit: the statement is a plain pro-finite extension
principle quantified over abstract packages, with no arithmetic
content — classically true outright as stated (the Noetherian and
surjectivity hypotheses are exactly what steps (2)–(4) consume).
CIRCULARITY GUARD (inherited): must not be proven through
`Family.lean` or anything downstream of it (`Lift.lean` included). -/
theorem isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests.{s, uK, uW, uR}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] {ρbar : GaloisRep ℚ k W}
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)} {πuniv : Runiv →+* k}
    (hπsurj : Function.Surjective πuniv)
    (h : IsWeaklyUniversalOnIdentifiedFiniteTests.{s, uK, uW, uR} hpodd ρbar
      ρuniv πuniv) :
    IsWeaklyUniversalOnIdentifiedDeformation.{s, s, uK, uW, uR} hpodd ρbar
      ρuniv πuniv := by
  intro D hDid
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.moduleFinite
  letI := D.isModuleTopology
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  -- the reduction map has the maximal ideal as kernel, so it kills every
  -- tower ideal (a proper ideal of the local ring `D.A`) and induces the
  -- level reduction maps `πₙ`
  have hkerπ : RingHom.ker D.π = IsLocalRing.maximalIdeal D.A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective D.π D.π_surjective)
  have hker : ∀ (n : ℕ), ∀ a ∈ padicTowerIdeal p D.A n, D.π a = 0 := by
    intro n a ha
    rw [← RingHom.mem_ker, hkerπ]
    exact IsLocalRing.le_maximalIdeal (padicTowerIdeal_ne_top n) ha
  have hπnsurj : ∀ n : ℕ, Function.Surjective
      (Ideal.Quotient.lift (padicTowerIdeal p D.A n) D.π (hker n)) := by
    intro n y
    obtain ⟨a, ha⟩ := D.π_surjective y
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩
  -- the level-`n` classifying sets
  set X : (n : ℕ) → Set (Runiv →+* D.A ⧸ padicTowerIdeal p D.A n) := fun n =>
    {ψ | ψ.comp (algebraMap ℤ_[p] Runiv) =
        algebraMap ℤ_[p] (D.A ⧸ padicTowerIdeal p D.A n) ∧
      (Ideal.Quotient.lift (padicTowerIdeal p D.A n) D.π (hker n)).comp ψ = πuniv ∧
      ∀ (q : ℕ) (hq : q.Prime),
        ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          Ideal.Quotient.mk (padicTowerIdeal p D.A n)
            ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)} with hX
  -- (1) nonempty, by the quotient-tower leaf
  have hne : ∀ n, (X n).Nonempty := by
    intro n
    obtain ⟨ψ, h1, h2, h3⟩ :=
      exists_ringHom_quotient_padicTower_of_finiteTests h D hDid n (hker n)
    exact ⟨ψ, by rw [hX]; exact ⟨h1, h2, h3⟩⟩
  -- (2) finite, since a map compatible with the residue maps factors
  -- through the finite ring `Runiv/𝔪ᶜ`
  have hfin : ∀ n, (X n).Finite := by
    intro n
    rw [hX]
    exact (finite_setOf_ringHom_comp_eq hπsurj (hπnsurj n)).subset fun ψ hψ => hψ.2.1
  -- the three clauses survive postcomposition with the transition maps
  have hstab : ∀ (m n : ℕ) (hmn : m ≤ n)
      (ψ : Runiv →+* D.A ⧸ padicTowerIdeal p D.A n), ψ ∈ X n →
      (Ideal.Quotient.factor (padicTowerIdeal_antitone hmn)).comp ψ ∈ X m := by
    intro m n hmn ψ hψ
    rw [hX] at hψ ⊢
    obtain ⟨h1, h2, h3⟩ := hψ
    refine ⟨RingHom.ext fun r => ?_, RingHom.ext fun r => ?_, fun q hq => ?_⟩
    · have e := RingHom.congr_fun h1 r
      simp only [RingHom.comp_apply] at e ⊢
      rw [e]
      exact Ideal.Quotient.factor_mk _ (algebraMap ℤ_[p] D.A r)
    · have e := RingHom.congr_fun h2 r
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ψ r)
      simp only [RingHom.comp_apply] at e ⊢
      rw [← hx] at e ⊢
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk]
      rwa [Ideal.Quotient.lift_mk] at e
    · have e := h3 q hq
      simp only [RingHom.comp_apply]
      rw [e, Ideal.Quotient.factor_mk]
  -- (3) König, then the `p`-adic assembly
  obtain ⟨ψ, hψX, hψcomp⟩ := exists_tower_of_forall_nonempty_finite X hne hfin hstab
  obtain ⟨Ψ, hΨ⟩ := exists_ringHom_of_tower ψ hψcomp
  rw [hX] at hψX
  -- (4) the clauses pass to the limit by separatedness
  refine ⟨Ψ, RingHom.ext fun r => ?_, RingHom.ext fun r => ?_, ∅, fun q hq _ => ?_⟩
  · refine eq_of_forall_mk_padicTowerIdeal_eq (p := p) fun n => ?_
    have e := RingHom.congr_fun (hψX n).1 r
    simp only [RingHom.comp_apply] at e ⊢
    rw [hΨ n, e]
    rfl
  · have e := RingHom.congr_fun (hψX 0).2.1 r
    simp only [RingHom.comp_apply] at e ⊢
    rw [← hΨ 0 r, Ideal.Quotient.lift_mk] at e
    exact e
  · refine eq_of_forall_mk_padicTowerIdeal_eq (p := p) fun n => ?_
    rw [hΨ n, (hψX n).2.2 q hq]

/-- **Schlessinger–Ramakrishna–CDT core leaf** (DECOMPOSED 2026-07-24,
LEVEL cut — the assembly below is PROVEN over the finite-level leaf
`exists_weaklyUniversalOnIdentified_framed_finiteTests` (Schlessinger
H1/H2/H4, Schur via oddness, Ramakrishna's flat condition at `p`,
CDT's tame condition at `2`, de Smit–Lenstra presentation — tested
against FINITE coefficient rings only) and the pro-finite limit
upgrade `isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`
(itself PROVEN 2026-07-25 over its own quotient-tower leaf
`exists_ringHom_quotient_padicTower_of_finiteTests`: König finiteness
of the classifying sets, and the `p`-adic assembly, are proven
there)): GIVEN the finiteness of the dual-number tangent space
(Schlessinger's H3, supplied by the restricted-ramification finiteness
leaf through the proven glue of the pillar assembly), the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
admits a Mazur-category package `(Runiv, ρuniv, πuniv)` — complete
Noetherian local topological `ℤ_p`-algebra with the `𝔪`-adic topology,
hardly ramified universal representation on the standard frame,
surjective reduction matching linear `charFrob` coefficients off a
finite set — that factors every residually identified STANDARD-FRAMED
test deformation (module universe = coefficient universe; the
reframing transport
`isWeaklyUniversalOnIdentifiedDeformation_of_reframe` upgrades this to
every module universe).  See the two leaves' docstrings for the full
classical construction, stratum by stratum.

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability; abstractly the
hypothesis set contains an irreducible hardly ramified `ρbar`, which
the section audit of `Interface.lean` shows to be classically
unsatisfiable, so the statement is also classically true outright.
CIRCULARITY GUARD (inherited): must not be proven through
`Family.lean` or anything downstream of it (`Lift.lean` included). -/
theorem exists_weaklyUniversalOnIdentified_framed_of_finite_tangent.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    (hfin : {ρε : GaloisRep ℚ (DualNumber k) (Fin 2 → DualNumber k) |
      IsDualNumberTangentLift hpodd ρbar ρε}.Finite) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalOnIdentifiedDeformation.{s, s, uK, uW, s} hpodd ρbar
        ρuniv πuniv := by
  obtain ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred, hws⟩ :=
    exists_weaklyUniversalOnIdentified_framed_finiteTests.{s, uK, uW}
      hpodd hW hρbar hirr hfin
  letI := iCR
  letI := iTS
  letI := iTR
  letI := iLR
  letI := iAlg
  letI := iNoeth
  exact ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred,
    isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests hπsurj hws⟩

/-- **Strict Mazur representability** (the representability half of
the Mazur pillar; DECOMPOSED 2026-07-24, FOUNDER cut — the assembly
below is PROVEN over the restricted-ramification finiteness leaf
`finite_setOf_isHardlyRamified` (Hermite–Minkowski, instantiated at
the dual numbers to give Schlessinger's H3) and the
deformation-theoretic core leaf
`exists_weaklyUniversalOnIdentified_framed_of_finite_tangent`
(Schlessinger H1/H2/H4, Schur via oddness, Ramakrishna's flat
condition at `p`, CDT's tame condition at `2`, de Smit–Lenstra
presentation), with the second universality clause obtained from the
first by the proven reframing transport
`isWeaklyUniversalOnIdentifiedDeformation_of_reframe`): the hardly
ramified deformation problem of an irreducible hardly ramified `ρbar`
over a finite coefficient field admits a Mazur-category package
`(Runiv, ρuniv, πuniv)` — complete Noetherian local topological
`ℤ_p`-algebra with the `𝔪`-adic topology, hardly ramified universal
representation, surjective reduction matching linear `charFrob`
coefficients off a finite set — that factors every *residually
identified* test deformation, at both module universes the pillar-3b
assembly instantiates.  The Chebotarev–Brauer–Nesbitt matching is NOT
part of this node (it is supplied by `exists_conj_of_charFrob_eq_away`
through the proven assemblies below); this node is
Mazur/Ramakrishna/CDT representability proper.

Classical construction (as in the parent pillar's docstring, which this
leaf now carries alone): `ρbar` is odd (cyclotomic determinant, odd
`p`), and an odd irreducible 2-dimensional representation over a
finite field of odd characteristic is absolutely irreducible, so
`End_{k[Γ]}(ρbar) = k` (Schur) and the framing is a torsor: by
Schlessinger's criterion the unframed deformation functor of `ρbar` on
complete Noetherian local `ℤ_p`-algebras with residue field `k` is
pro-representable (Mazur, *Deforming Galois representations*, MSRI
Publ. 16 (1989), §1.2; Schlessinger H1–H4 hold with finite tangent
space `H¹(G_{ℚ,{2,p}}, ad ρbar)`, finite by global Euler
characteristic/class-field finiteness).  The hardly ramified
conditions cut out a relatively representable closed subfunctor:
cyclotomic determinant and unramifiedness outside `2p` are
limit-stable; flatness at `p` in the `IsFlatAt` sense is Ramakrishna's
flat condition (Compositio 87 (1994)); the tame quadratic quotient at
`2` is an ordinary-type condition (Conrad–Diamond–Taylor, JAMS 12
(1999), §2; FLT blueprint's `S`-good theory with `S = {2}`).  `Runiv`
is the universal ring — a quotient of `ℤ_p[[x₁,…,x_g]]` (de
Smit–Lenstra presentation), hence Noetherian, `𝔪`-adically complete,
with the `𝔪`-adic topology; `ρuniv` the universal representation
framed by any basis; `πuniv` the residue map.  Given a test
deformation `D` WITH a residual identification, conjugating the
framing carries `D.ρ` to an honest deformation of `ρbar` over the
module-finite local `ℤ_p`-algebra `D.A` — a legitimate Mazur test
object (complete Noetherian local with the `𝔪`-adic topology, per the
module docstring's audit) — and its classifying map is the required
`ψ`: `ℤ_p`-compatibility and reduction compatibility are strictness,
and the trace clause is conjugation-invariance of characteristic
polynomials (residual irreducibility kills the framing ambiguity on
traces).

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability; abstractly the
hypothesis set contains an irreducible hardly ramified `ρbar`, which
the section audit of `Interface.lean` shows to be classically
unsatisfiable, so the statement is also classically true outright.
CIRCULARITY GUARD (inherited): must not be proven through
`Family.lean` or anything downstream of it (`Lift.lean` included). -/
theorem exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalOnIdentifiedDeformation.{s, s, uK, uW, s} hpodd ρbar
        ρuniv πuniv ∧
      IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, s} hpodd ρbar
        ρuniv πuniv := by
  obtain ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred, hws⟩ :=
    exists_weaklyUniversalOnIdentified_framed_of_finite_tangent.{s, uK, uW}
      hpodd hW hρbar hirr
      ((finite_setOf_isHardlyRamified hpodd).subset fun ρε hρε => hρε.1)
  letI := iCR
  letI := iTS
  letI := iTR
  letI := iLR
  letI := iAlg
  exact ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred, hws,
    isWeaklyUniversalOnIdentifiedDeformation_of_reframe hws⟩

open scoped TensorProduct in
/-- **Upgrade from identified to unconditional weak universality**
(PROVEN — the glue of the Mazur pillar's 2026-07-24 decomposition):
a package that factors residually identified deformations factors ALL
deformations, when `ρbar` is irreducible and hardly ramified.  Given a
test deformation `D`, its reduction `D.ρ.baseChange k` along the
(automatically continuous, `continuous_pi`) reduction map is a
2-dimensional representation over `k` whose `charFrob` at each prime
off `D.S` MATCHES that of `ρbar` in full: the linear coefficients
match by `charFrob_compat` and `charFrob_baseChange`, the constant
coefficients match at EVERY place because both determinants are pinned
to the same cyclotomic value
(`coeff_zero_charFrob_eq_of_isHardlyRamified`, which also consumes the
rigidity `ringHom_padicInt_eq` of `ℤ_p →+* k`), and both polynomials are
monic quadratics (`charFrob_monic`, `charFrob_natDegree`,
`monic_natDegree_two_ext`).  The Chebotarev–Brauer–Nesbitt leaf
`exists_conj_of_charFrob_eq_away` turns the matching into a residual
identification, and the identified factorization applies. -/
theorem isWeaklyUniversal_of_isWeaklyUniversalOnIdentified.{s, t, uK, uW, uR}
    {p : ℕ} {hpodd : Odd p} [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {hW : Module.rank k W = 2} {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)} {πuniv : Runiv →+* k}
    (h : IsWeaklyUniversalOnIdentifiedDeformation.{s, t, uK, uW, uR} hpodd
      ρbar ρuniv πuniv) :
    IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar ρuniv
      πuniv := by
  intro D
  letI := D.commRing
  letI := D.topologicalSpace
  letI := D.isTopologicalRing
  letI := D.isLocalRing
  letI := D.algebra
  letI := D.addCommGroup
  letI := D.module
  letI := D.moduleFiniteVd
  letI := D.moduleFreeVd
  letI : Algebra D.A k := D.π.toAlgebra
  letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
    (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
  refine h D ?_
  -- the reduction is 2-dimensional …
  have hrankW' : Module.rank k (k ⊗[D.A] D.Vd) = 2 := by
    rw [Module.rank_baseChange, D.rank_eq]
    simp
  -- … and its Frobenius characteristic polynomials are those of `ρbar`
  have hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ D.S →
      (D.ρ.baseChange k).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqS
    have hmap := charFrob_baseChange (B := k)
      hq.toHeightOneSpectrumRingOfIntegersRat D.ρ
    rw [RingHom.algebraMap_toAlgebra] at hmap
    refine monic_natDegree_two_ext ?_
      (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat ρbar) ?_
      (charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat ρbar hW)
      ?_ ?_
    · rw [hmap]
      exact (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat D.ρ).map
        D.π
    · rw [hmap, (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat
        D.ρ).natDegree_map D.π]
      exact charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat D.ρ
        D.rank_eq
    · rw [hmap, Polynomial.coeff_map]
      exact coeff_zero_charFrob_eq_of_isHardlyRamified D.isHardlyRamified
        hρbar D.π
        (ringHom_padicInt_eq (D.π.comp (algebraMap ℤ_[p] D.A))
          (algebraMap ℤ_[p] k))
        hq.toHeightOneSpectrumRingOfIntegersRat
    · rw [hmap, Polynomial.coeff_map]
      exact D.charFrob_compat q hq hqS
  obtain ⟨e, he⟩ := exists_conj_of_charFrob_eq_away hW hirr hrankW'
    (D.ρ.baseChange k) D.S hcf
  exact ⟨e, he⟩

/-- **Mazur representability of the hardly ramified deformation
problem** (pillar 3b-i; DECOMPOSED 2026-07-24 into the strict Mazur
representability leaf
`exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation` — the
classifying maps for residually identified deformations — and the
Chebotarev–Brauer–Nesbitt conjugacy leaf
`exists_conj_of_charFrob_eq_away` — which produces the residual
identification from the trace-level `charFrob_compat` matching via the
determinant pinning of `coeff_zero_charFrob_eq_of_isHardlyRamified`; the
assembly below and its glue
`isWeaklyUniversal_of_isWeaklyUniversalOnIdentified` are PROVEN):
an irreducible hardly ramified
mod-`p` representation `ρbar` over a finite coefficient field admits a
weakly universal hardly ramified deformation: a coefficient ring
`Runiv` in Mazur's category — a Noetherian local topological
`ℤ_p`-algebra whose topology is the `𝔪`-adic one and which is
`𝔪`-adically complete and separated — carrying a hardly ramified
representation `ρuniv` on `Fin 2 → Runiv` that reduces trace-by-trace
to `ρbar` through a surjection `πuniv`, such that every hardly
ramified deformation of `ρbar` over a module-finite local
`ℤ_p`-algebra factors through `(Runiv, ρuniv, πuniv)` on Frobenius
traces.  The two clauses are the same factorization property at the
two module universes the pillar-3b assembly instantiates (`Type s`
for the standard-framed Hecke side, `Type t` for the interface's
abstract rank-2 module `V`).

Classical construction: the framed deformation functor of `ρbar` on
complete Noetherian local `ℤ_p`-algebras with residue field `k` is
representable (Schlessinger's criterion; Mazur, *Deforming Galois
representations*, in Galois Groups over ℚ, MSRI Publ. 16 (1989),
§1.2); residual irreducibility gives `End_{k[Γ]}(ρbar) = k` (Schur —
hardly ramified representations are odd, having cyclotomic
determinant, and an odd irreducible 2-dimensional representation over
a finite field of odd characteristic is absolutely irreducible), so
the framing is a torsor and the unframed functor is representable as
well (Mazur §1.2 Prop. 1).  The hardly ramified conditions cut out a
closed subfunctor that is again representable: cyclotomic determinant
and unramifiedness outside `2p` are manifestly limit-stable
conditions; flatness at `p` in the `IsFlatAt` sense (every open-ideal
quotient has a flat prolongation) is Ramakrishna's flat deformation
condition, relatively representable by (Ramakrishna, *On a variation
of Mazur's deformation functor*, Compositio Math. 87 (1994)); the tame
condition at `2` (rank-1 unramified square-trivial quotient) is an
ordinary-type condition, relatively representable per
Conrad–Diamond–Taylor (*Modularity of certain potentially
Barsotti–Tate Galois representations*, JAMS 12 (1999), §2) — the FLT
blueprint packages the same problem as the "`S`-good" deformation
theory with `S = {2}` (ch. 4).  `Runiv` is the resulting universal
ring, `ρuniv` the universal representation (framed by any basis:
trace data is frame-invariant), `πuniv` the residue map; the
universal representation itself satisfies the hardly ramified
conditions because each condition holds on all Artinian quotients and
is, in the `IsFlatAt`/inertia-kernel/quotient-character spelling of
`Deformations/RepresentationTheory/`, precisely a limit of those
quotient conditions.  The factorization clause holds because a test
deformation reduces to `ρbar` honestly, not just trace-wise, by
Chebotarev + Brauer–Nesbitt + Carayol's conjugation theorem (see the
module docstring), and its classifying map carries `ρuniv` to it up to
conjugation, hence equates traces.

Both-ways audit: for the genuine hardly ramified problem this is the
cited Mazur/Ramakrishna/CDT representability; abstractly, the
hypothesis set contains an irreducible hardly ramified `ρbar`, which
the section audit of `Interface.lean` shows to be classically
unsatisfiable, so the statement is also classically true outright.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it (`Lift.lean`
included — its parallel representability infrastructure is
import-unreachable from here by design; see the module docstring). -/
theorem exists_weaklyUniversal_hardlyRamifiedDeformation.{s, t, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ (Runiv : Type s) (_ : CommRing Runiv) (_ : TopologicalSpace Runiv)
      (_ : IsTopologicalRing Runiv) (_ : IsLocalRing Runiv)
      (_ : Algebra ℤ_[p] Runiv) (_ : IsNoetherianRing Runiv)
      (_ : IsAdic (IsLocalRing.maximalIdeal Runiv))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
      (ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv))
      (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
      (_ : IsHardlyRamified hpodd hranku ρuniv)
      (πuniv : Runiv →+* k) (_ : Function.Surjective πuniv)
      (Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
      (∀ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
        πuniv ((ρuniv.charFrob
            hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
          (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) ∧
      IsWeaklyUniversalDeformation.{s, s, uK, uW, s} hpodd ρbar ρuniv
        πuniv ∧
      IsWeaklyUniversalDeformation.{s, t, uK, uW, s} hpodd ρbar ρuniv
        πuniv := by
  obtain ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred, hws, hwt⟩ :=
    exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation.{s, t, uK, uW}
      hpodd hW hρbar hirr
  letI := iCR
  letI := iTS
  letI := iTR
  letI := iLR
  letI := iAlg
  exact ⟨Runiv, iCR, iTS, iTR, iLR, iAlg, iNoeth, hadic, hcomplete, ρuniv,
    hranku, hHR, πuniv, hπsurj, Suniv, hred,
    isWeaklyUniversal_of_isWeaklyUniversalOnIdentified hρbar hirr hws,
    isWeaklyUniversal_of_isWeaklyUniversalOnIdentified hρbar hirr hwt⟩

open Topology in
/-- **Hausdorffness of the module topology on a module-finite module
over a compact Hausdorff Noetherian topological ring** (PROVEN; the
topological half of the Carayol surjectivity argument, instantiated at
`R = ℤ_p`, `M = T` in `surjective_ringHom_of_charFrob_eq` below):
present `M` as a topological quotient of `R^n` along a
module-finiteness surjection (a quotient map by
`IsModuleTopology.isQuotientMap_of_surjective`); its kernel is a
finitely generated submodule of `R^n` (Noetherianity), hence compact
(`Submodule.isCompact_of_fg` — the continuous image of a product of
copies of the compact `R`), hence closed in the Hausdorff `R^n`; so
`{0}` is closed in the quotient topology of `M`, and the topological
additive group structure of the module topology upgrades T1 to T2. -/
theorem t2Space_of_isModuleTopology (R : Type*) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    [T2Space R] [IsNoetherianRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] : T2Space M := by
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  have hquot : IsQuotientMap φ :=
    IsModuleTopology.isQuotientMap_of_surjective hφ
  have hker : IsClosed (⇑φ ⁻¹' {0}) := by
    have hset : ⇑φ ⁻¹' {0} =
        ((LinearMap.ker φ : Submodule R (Fin n → R)) : Set (Fin n → R)) := by
      ext x
      simp [LinearMap.mem_ker]
    rw [hset]
    exact (Submodule.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
  have h0 : IsClosed ({0} : Set M) :=
    ((isQuotientMap_iff_isClosed.mp hquot).2 {0}).mpr hker
  haveI : IsTopologicalAddGroup M := IsModuleTopology.topologicalAddGroup R M
  haveI := IsTopologicalAddGroup.t1Space M h0
  infer_instance

/-- **Hecke generation leaf** (PROVEN 2026-07-24 by the odd-prime
dichotomy, see ROUTE below — the one genuinely
Hecke-side fact of pillar 3b-ii): the coefficient ring `T` of a
Hecke-side hardly ramified deformation of the irreducible residual
`ρbar` is topologically generated as a `ℤ_p`-algebra by ALL the linear
`charFrob` coefficients (the Frobenius traces up to sign) of its
representation `ρT` — no primes excluded.  The finite-exclusion
strengthening `topologicalClosure_adjoin_charFrobCoeff_eq_top` below
is PROVEN from this leaf by Chebotarev density and continuity of the
trace; this leaf carries exactly the Hecke-theoretic input.

Classical route, at the intended instantiation `T = 𝕋_𝔪` (the weight-2
Hecke algebra at the Serre-optimal level localized at the
non-Eisenstein maximal ideal of `ρbar`): `𝕋_𝔪` is generated as a
`ℤ_p`-algebra — even module-finitely, so topological closure is not
needed classically — by the Hecke operators `T_q` at the good primes
`q ∤ Np` (Eichler–Shimura/duality: the anemic Hecke algebra is BY
CONSTRUCTION the `ℤ_p`-algebra generated by the good `T_q`, cf. the
construction recorded on pillar 3a-i in `Interface.lean`; Carayol,
Contemp. Math. 165 (1994), Théorème 3; Diamond–Darmon–Taylor, *Fermat's
Last Theorem* (1995), §4.3; Wiles, Ann. of Math. 141 (1995), ch. 2),
and `T_q = −(charFrob ρT q).coeff 1` by the Eichler–Shimura relation —
so the trace subalgebra contains a generating set, and the bad primes'
traces enlarge it further; negation keeps it a subalgebra either way.

ROUTE (2026-07-24): the hypothesis package contains the classically
unsatisfiable combination of an IRREDUCIBLE hardly ramified residual
`ρbar` over the odd prime `p` — discharged by the same sanctioned
odd-prime dichotomy already discharging pillar 2's assembly, pillar
3a-i, and the 3a-ii descent leaves in `Interface.lean`.  At `p = 3`,
`IsHardlyRamified.mod_three_reducible` (`ModThree.lean`, the
Fontaine/Odlyzko discriminant-bound route) produces a `Γ ℚ`-stable
proper nonzero submodule refuting `hirr` through
`Slop.OddRep.isIrreducible_iff_forall`; at `p ≥ 5` the Family-free
Khare–Wintenberger headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`) refutes `hirr` directly.  The
packaged form `not_isIrreducible_of_isHardlyRamified_of_odd` lives in
`Interface.lean`, DOWNSTREAM of this module — importing it would be a
cycle — so the dichotomy is inlined here from its two upstream inputs
(import-audited 2026-07-24: the only importer of this module is
`Interface.lean`, whose own only importer is the census tool, and the
public import cones of `ModThree.lean`, `OddAbsIrredSlop.lean`, and
`KhareWintenberger.lean` reach neither file, so the added proof-only
imports cannot cycle).  The classical (non-vacuous) content at the
intended instantiation remains the Eichler–Shimura/Carayol generation
statement recorded above, which any future direct discharge should
follow.

Both-ways audit: at the intended packet this is verbatim the cited
generation statement; abstractly the packet `(T, ρT, π)` is NOT
assumed trace-generated, and the statement is covered by the section
audit of `Interface.lean` (the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar`, via residual
modularity → level optimization → `S₂(Γ₀(2)) = 0`).  CIRCULARITY
GUARD (inherited from pillar 3b): must not be proven through
`Family.lean` or anything downstream of it. -/
theorem topologicalClosure_adjoin_charFrobCoeff_univ_eq_top.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (_hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (_hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    (Algebra.adjoin ℤ_[p] {a : T | ∃ (q : ℕ) (hq : q.Prime),
        a = (ρT.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1}).topologicalClosure
      = ⊤ := by
  exfalso
  -- the odd-prime dichotomy, inlined (see the ROUTE note above)
  have hp := (Fact.out : p.Prime)
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · -- `p < 5`: primality and oddness force `p = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    have hp3 : p = 3 := by
      have := hp.two_le
      have := Nat.odd_iff.mp hpodd
      omega
    subst hp3
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
  · -- `p ≥ 5`: the Family-free Khare–Wintenberger headline
    exact absurd hirr
      (not_isIrreducible_of_isHardlyRamified_of_five_le hpodd h5 hW hρbar)

/-- **Carayol trace generation, Hecke side** (pillar 3b-ii's arithmetic
leaf; DECOMPOSED 2026-07-24 — the Chebotarev/continuity reduction is
PROVEN below over the Hecke generation leaf
`topologicalClosure_adjoin_charFrobCoeff_univ_eq_top`): the coefficient ring `T` of a Hecke-side
hardly ramified deformation of the irreducible residual `ρbar` is
topologically generated as a `ℤ_p`-algebra by the linear `charFrob`
coefficients (the Frobenius traces up to sign) of its representation
`ρT` at the primes outside ANY given finite exceptional set `Sexc`:
the topological closure of the `ℤ_p`-subalgebra they generate is all
of `T`.

Classical route, at the intended instantiation `T = 𝕋_𝔪` (the weight-2
Hecke algebra at the Serre-optimal level localized at the
non-Eisenstein maximal ideal of `ρbar`): `𝕋_𝔪` is generated as a
`ℤ_p`-algebra — even module-finitely, so topological closure is not
needed classically — by the Hecke operators `T_q` with `q` outside any
given finite set of primes.  The standard argument (Carayol, *Formes
modulaires et représentations galoisiennes à valeurs dans un anneau
local complet*, Contemp. Math. 165 (1994), Théorème 3, the "critère de
surjectivité"; Diamond–Darmon–Taylor, *Fermat's Last Theorem*, Current
Developments in Math. (1995), §4.3; Wiles, Ann. of Math. 141 (1995),
ch. 2): let `T' ⊆ T` be the closed subalgebra generated by the traces
off `Sexc`; the pseudo-representation/trace of `ρT` restricted to the
Chebotarev-dense set of Frobenii off `Sexc` takes values in `T'`, and
by continuity of the trace and density ALL traces lie in the closed
`T'`; residual irreducibility then lets Carayol's théorème 1 conjugate
`ρT` into a representation with values in `GL₂(T')`, whose traces
`T_q` (all `q ∤ Np`) together with the diamond/weight data generate
`𝕋_𝔪` over `ℤ_p` by the Eichler–Shimura/duality description of the
Hecke algebra — forcing `T' = T`.

FORMALIZED ROUTE (PROVEN): exactly the density step above, against the
generation leaf instead of Carayol's théorème 1 — the closed
subalgebra `T'` generated by the traces off `Sexc` absorbs the trace
of `ρT` at EVERY group element, because the trace function
`g ↦ (charpoly (ρT g)).coeff 1 = −tr (ρT g)` is continuous (the trace
is a linear functional on the endomorphism algebra, continuous in the
module topology — the same `charpoly.coeff 1`-to-trace bridge as
`Interface.lean`'s proven Chebotarev trace gluing), its `T'`-agreement
set is closed and contains the Frobenius conjugates off `Sexc`
(conjugation-invariance of `charpoly`), and those are dense
(`dense_conjClasses_globalFrob`, `Chebotarev.lean`).  In particular
`T'` contains the traces at ALL primes, so it contains the
unrestricted trace subalgebra, whose closure is everything by the
Hecke generation leaf `topologicalClosure_adjoin_charFrobCoeff_univ_eq_top`.

Both-ways audit: at the intended packet this is verbatim the cited
generation lemma; abstractly the packet `(T, ρT, π)` is NOT assumed
trace-generated, and the statement is covered by the section audit of
`Interface.lean` (the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar`, via residual
modularity → level optimization → `S₂(Γ₀(2)) = 0`).  CIRCULARITY
GUARD (inherited from pillar 3b): must not be proven through
`Family.lean` or anything downstream of it. -/
theorem topologicalClosure_adjoin_charFrobCoeff_eq_top.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (Sexc : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) :
    (Algebra.adjoin ℤ_[p] {a : T | ∃ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sexc ∧
        a = (ρT.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1}).topologicalClosure
      = ⊤ := by
  classical
  -- write `C` for the closed subalgebra generated by the traces off `Sexc`
  set C : Subalgebra ℤ_[p] T :=
    (Algebra.adjoin ℤ_[p] {a : T | ∃ (q : ℕ) (hq : q.Prime),
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sexc ∧
        a = (ρT.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1}).topologicalClosure
  have hCclosed : IsClosed (C : Set T) :=
    Subalgebra.isClosed_topologicalClosure _
  -- continuity of the global trace function `g ↦ (charpoly (ρT g)).coeff 1`
  have hFcont : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((ρT g).charpoly).coeff 1 := by
    letI := moduleTopology T (Module.End T (Fin 2 → T))
    haveI : IsModuleTopology T (Module.End T (Fin 2 → T)) := ⟨rfl⟩
    have hρc : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρT g :=
      ContinuousMonoidHom.continuous_toFun ρT
    have htrc : Continuous fun φ : Module.End T (Fin 2 → T) =>
        LinearMap.trace T (Fin 2 → T) φ :=
      IsModuleTopology.continuous_of_linearMap _
    have hcoeff : (fun g : Field.absoluteGaloisGroup ℚ =>
        ((ρT g).charpoly).coeff 1) =
        fun g => - LinearMap.trace T (Fin 2 → T) (ρT g) := by
      funext g
      have h := Matrix.trace_eq_neg_charpoly_coeff
        (LinearMap.toMatrix (Pi.basisFun T (Fin 2)) (Pi.basisFun T (Fin 2))
          (ρT g))
      rw [LinearMap.charpoly_toMatrix] at h
      rw [LinearMap.trace_eq_matrix_trace T (Pi.basisFun T (Fin 2)), h]
      norm_num
    rw [hcoeff]
    exact (htrc.comp hρc).neg
  -- the `C`-agreement set of the trace function is closed …
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      ((ρT g).charpoly).coeff 1 ∈ C} :=
    hCclosed.preimage hFcont
  -- … and contains the Frobenius conjugates off `Sexc`
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ Sexc ∧
        ∃ h : Field.absoluteGaloisGroup ℚ, x = h * globalFrob v * h⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        ((ρT g).charpoly).coeff 1 ∈ C} := by
    rintro x ⟨v, hvS, h, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    -- conjugation-invariance of the characteristic polynomial
    have hgu : (ρT h).comp (ρT h⁻¹) = LinearMap.id := by
      have h1 : ρT h * ρT h⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      exact h1
    have hgu' : (ρT h⁻¹).comp (ρT h) = LinearMap.id := by
      have h1 : ρT h⁻¹ * ρT h = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      exact h1
    have heq : ρT (h * globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * h⁻¹) =
        (LinearEquiv.ofLinear (ρT h) (ρT h⁻¹) hgu hgu').conj
          (ρT (globalFrob
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
      ext w
      simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
    show ((ρT (h * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * h⁻¹)).charpoly).coeff 1 ∈ C
    rw [heq, LinearEquiv.charpoly_conj]
    refine Subalgebra.le_topologicalClosure _ (Algebra.subset_adjoin ?_)
    refine ⟨q, hq, hvS, ?_⟩
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
  -- Chebotarev density: EVERY trace lies in `C` …
  have hall : ∀ g : Field.absoluteGaloisGroup ℚ,
      ((ρT g).charpoly).coeff 1 ∈ C := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ) Sexc
    have huniv : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ g)
  -- … so the unrestricted trace subalgebra sits inside the closed `C`
  have hle : Algebra.adjoin ℤ_[p] {a : T | ∃ (q : ℕ) (hq : q.Prime),
      a = (ρT.charFrob
        hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1} ≤ C := by
    rw [Algebra.adjoin_le_iff]
    rintro a ⟨q, hq, rfl⟩
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
    exact hall _
  -- … whose closure is everything by the Hecke generation leaf
  have h1 := Subalgebra.topologicalClosure_minimal hle hCclosed
  rw [topologicalClosure_adjoin_charFrobCoeff_univ_eq_top hpodd hW hρbar hirr
    hrankT hρT hπ hred] at h1
  exact top_unique h1

/-- **Carayol trace generation: the surjection `R_univ ↠ 𝕋`** (pillar
3b-ii; DECOMPOSED 2026-07-24, topological half PROVEN over the
arithmetic leaf `topologicalClosure_adjoin_charFrobCoeff_eq_top`): a
ring homomorphism `ψ` from a Mazur-category deformation
`(Runiv, ρuniv, πuniv)` of the irreducible residual `ρbar` to a
Hecke-side hardly ramified deformation `(T, ρT, π)` that is compatible
with the `ℤ_p`-structures, the reduction maps, and the Frobenius
traces away from a finite set, is SURJECTIVE.

Classical route, at the intended instantiation `T = 𝕋_𝔪` (the
weight-2 Hecke algebra at the Serre-optimal level localized at the
non-Eisenstein maximal ideal of `ρbar`, the packet produced by pillar
3a of `Interface.lean`): `𝕋_𝔪` is generated as a `ℤ_p`-algebra by the
Hecke operators `T_q` with `q` outside ANY given finite set of primes
— by Chebotarev density and the Carayol/Serre linearization argument
(Carayol, Contemp. Math. 165 (1994), the "critère de surjectivité";
Diamond–Darmon–Taylor, *Fermat's Last Theorem*, Current Developments
in Math. (1995), Lemma 4.6? — the standard duality/Chebotarev
argument; Wiles, Ann. of Math. 141 (1995), ch. 2), and `T_q` is
`−(coeff 1)` of `charFrob ρT` at `q`, which lies in the image of `ψ`
by the trace-compatibility hypothesis.  The image of `ψ` is a closed
`ℤ_p`-subalgebra: it is a `ℤ_p`-subalgebra by the `ℤ_p`-structure
compatibility `hψalg`, in particular a `ℤ_p`-submodule of the
module-finite `T`, hence finitely generated over the Noetherian
`ℤ_p`, hence compact (a continuous linear image of some `ℤ_p^n`,
`Submodule.isCompact_of_fg`) and therefore closed in `T` — which is
Hausdorff by `t2Space_of_isModuleTopology` above.  A closed
subalgebra containing all the `T_q` off a finite set is everything by
the generation leaf.  (This formalized route needs neither continuity
of `ψ` nor compactness of `Runiv`, so the `𝔪`-adic hypotheses on
`Runiv` go unused here; they remain part of the pillar's interface
contract with the assembly.)

Both-ways audit: at the intended packet this is verbatim the cited
generation lemma; abstractly the packet `(T, ρT, π)` is NOT assumed
trace-generated, and the statement is covered by the section audit of
`Interface.lean` (the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar`).  CIRCULARITY
GUARD: must not be proven through `Family.lean` or anything
downstream of it. -/
theorem surjective_ringHom_of_charFrob_eq.{s, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (_hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (_hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (_hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (_hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (_hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    Function.Surjective ψ := by
  -- upgrade `ψ` to a `ℤ_p`-algebra homomorphism via `hψalg`
  let ψa : Runiv →ₐ[ℤ_[p]] T :=
    { toRingHom := ψ, commutes' := fun c => RingHom.congr_fun hψalg c }
  -- its range is closed: a finitely generated `ℤ_p`-submodule of the
  -- module-finite `T` (Noetherianity of `ℤ_p`), hence compact
  -- (`CompactSpace ℤ_[p]`), hence closed in the Hausdorff `T`
  haveI : T2Space T := t2Space_of_isModuleTopology ℤ_[p] T
  have hclosed : IsClosed (ψa.range : Set T) := by
    have hc := (Submodule.isCompact_of_fg
      (IsNoetherian.noetherian (Subalgebra.toSubmodule ψa.range))).isClosed
    simpa using hc
  -- the Frobenius traces off `Sψ` lie in the range, by trace
  -- compatibility with the universal representation
  have hle : Algebra.adjoin ℤ_[p] {a : T | ∃ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ ∧
      a = (ρT.charFrob
        hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1} ≤ ψa.range := by
    rw [Algebra.adjoin_le_iff]
    rintro a ⟨q, hq, hqS, rfl⟩
    exact (AlgHom.mem_range ψa).mpr
      ⟨(ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1,
        hψ q hq hqS⟩
  -- a closed subalgebra above a topologically generating set is `⊤`
  have h1 := Subalgebra.topologicalClosure_minimal hle hclosed
  rw [topologicalClosure_adjoin_charFrobCoeff_eq_top hpodd hW hρbar hirr
    hrankT hρT hπ hred Sψ] at h1
  exact (AlgHom.range_eq_top ψa).mp (top_unique h1)

/-! ### The Taylor–Wiles patching architecture behind pillar 3b-iii

The injectivity pillar `injective_ringHom_of_isWeaklyUniversal` is
ASSEMBLED below (proof written, 2026-07-24) from three sorried leaves
that are exactly the classically-cited components of the Taylor–Wiles
patching argument, plus one PROVEN commutative-algebra assembly:

1. `exists_taylorWilesPrimeSet` (PROVEN 2026-07-24, now sorry-free) —
   Taylor–Wiles prime sets at every level `p^n` and of every size:
   Chebotarev density (`dense_conjClasses_globalFrob`) applied to the
   open conjugation-stable locus determined by the Wiles/DDT Galois
   element (fixes `μ_{p^n}`, distinct `ρbar`-eigenvalues), whose
   existence (`exists_fixing_rootsOfUnity_charpoly_split`) is PROVEN
   2026-07-24 by the sanctioned odd-prime dichotomy — see its
   docstring for the route and the statement-shape audit showing the
   honest group-theoretic decomposition is unavailable over fixed `k`.
2. `exists_patchedModule` (ASSEMBLED 2026-07-24) — the pigeonhole
   patching construction (Taylor–Wiles 1995, as reorganized by Diamond
   1997 and Fujiwara): from the tower of auxiliary levels `Q_n` it
   produces a `PatchedModule`, the limit object of the patching
   process.  PROVEN as glue over two sorried sub-leaves cutting the
   construction at the `TaylorWilesSystem` interface (the tower of
   finite-level data):
   2a. `exists_taylorWilesSystem` (leaf) — the ARITHMETIC half: the
       auxiliary Taylor–Wiles-level deformation rings and Hecke
       modules, with the Taylor–Wiles freeness certificate and the
       bottom control maps.
   2b. `TaylorWilesSystem.exists_patchedModule` (leaf) — the pure
       commutative-algebra half: the pigeonhole/ultraproduct
       extraction of the limit object, vendorable from the FLT
       project's abstract patching development.
3. `free_of_isRegular_mvPowerSeries` (PROVEN 2026-07-24) — the
   commutative-algebra endgame: over the regular local ring
   `ℤ_p[[x₁, …, x_q]]` a finite module carrying a regular sequence of
   length `q + 1` (depth ≥ dim) is FREE (Auslander–Buchsbaum; Diamond
   1997, Thm. 2.4).  Proven by the abstract dimension induction
   `free_of_isRegular_of_ofList_eq_maximalIdeal` over two remaining
   power-series leaves: `isNoetherianRing_mvPowerSeries` and
   `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`.
4. `PatchedModule.injective` (PROVEN) — the faithfulness argument
   assembling 3 into the conclusion: the patched module is free over
   `R_∞ = ℤ_p[[x₁, …, x_q]]`, its bottom quotient `M₀` therefore has
   free coordinates over `Runiv = R_∞/𝔞`, and since the `R_∞`-action
   on `M₀` factors as the `T`-action through `ψ ∘ (R_∞ ↠ Runiv)`, any
   element of `ker ψ` annihilates a coordinate of a free module and
   vanishes.

The shapes are aligned with the abstract patching formalization of the
FLT project (`FLT/Patching/{Algebra,Module,System,REqualsT}.lean`,
Andrew Yang) so that its sorry-free material can be vendored to
discharge leaf 2b; note that that development ends at
`ker_RtoT_le_nilradical` (`R_red = 𝕋_red`), while the freeness route
through Diamond 1997 taken here yields full injectivity — the
difference is exactly leaf 3's Auslander–Buchsbaum input.  CORRECTED
AUDIT (2026-07-24, second pass): the pin DOES carry the needed depth
layer — the Rees theorem `ModuleCat.exists_isRegular_tfae`
(`Mathlib/RingTheory/Depth/Rees.lean`), the regular-sequence
permutation lemmas, and the freeness dévissage
`Module.free_quotSMulTop_iff_free` (`Mathlib/RingTheory/Regular/Free.lean`)
— and leaf 3 is PROVEN on top of them in the Auslander–Buchsbaum
section below, with only two concrete power-series facts
(Noetherianity, the regular system of parameters) left as leaves. -/

/-- **Taylor–Wiles prime sets.**  A finite set `Q` of rational primes
is a Taylor–Wiles set of level `n` for the residual representation
`ρbar` if every `q ∈ Q` is a prime that is `≡ 1 (mod p^n)` and whose
Frobenius characteristic polynomial under `ρbar` splits over the
residual coefficient ring with two DISTINCT roots (the classical
"`ρbar(Frob_q)` has distinct rational eigenvalues" condition; the two
roots are the eigenvalues `α_q ≠ β_q`).  For `n ≥ 1` the congruence
forces `q ∉ {2, p}` (as `q ≥ p^n + 1 ≥ 4`), so such `q` are unramified
for any hardly ramified `ρbar` and `charFrob` at `q` genuinely reads
off the Frobenius conjugacy class.  This is the local condition that
makes the auxiliary deformation theory at `q` a torus: the deformation
of a `q`-unramified representation with distinct Frobenius eigenvalues
along `q ≡ 1 (mod p^n)` splits into two characters, giving the
`ℤ_p[Δ_Q]`-structure (`Δ_Q = ∏_{q ∈ Q} (ℤ/q)^×(p)`) on the auxiliary
Hecke modules that patching feeds on (Taylor–Wiles, Ann. of Math. 141
(1995), §2; Diamond–Darmon–Taylor (1995), §5.3; the eigenvalue
rationality over the FIXED `k` follows classically after the harmless
scalar enlargement built into the choice of `k`, and abstractly is
part of the audited hypothesis set). -/
def IsTaylorWilesPrimeSet.{uK, uW}
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) (p n : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ q ∈ Q, ∃ hq : q.Prime,
    q ≡ 1 [MOD p ^ n] ∧
    ∃ α β : k, α ≠ β ∧
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)

/-- **The Taylor–Wiles Galois element** (PROVEN 2026-07-24 by the
sanctioned odd-prime dichotomy, see ROUTE below): in the absolute
Galois group of `ℚ` there is an element `σ` that acts trivially on
all `p^n`-th roots of unity and whose image `ρbar(σ)` has
characteristic polynomial split with two DISTINCT roots over the
residual coefficient field `k`.

This is the classical group-theoretic lemma of Wiles/Taylor–Wiles
behind the existence of Taylor–Wiles primes (Wiles, Ann. of Math. 141
(1995), ch. 3; Diamond–Darmon–Taylor (1995), Lemma 4.10/5.31; de
Shalit in Cornell–Silverman–Stevens, "Hecke rings and universal
deformation rings").  Classical route: `ρbar` is hardly ramified, so
`det ρbar` is the mod-`p` cyclotomic character (`det_eq` of
`IsHardlyRamified`), which is ODD; with `p` odd and `ρbar`
irreducible, the restriction of `ρbar` to `Gal(ℚ̄/ℚ(ζ_p))` is
(absolutely) irreducible unless `ρbar` is dihedral (induced from a
quadratic character; the case analysis of DDT §4.3), and AFTER a
harmless scalar enlargement a nonabelian subgroup of `GL₂` acting
irreducibly contains an element with distinct split eigenvalues.

STATEMENT-SHAPE AUDIT (2026-07-24, this dispatch): over the FIXED `k`
of this statement the group-theoretic half is genuinely FALSE, so the
planned decomposition — (i) restricted irreducibility over
`ℚ(ζ_{p^n})`, (ii) a nonabelian irreducible subgroup of `GL₂(k)` has
an element with distinct eigenvalues split over `k` — would plant a
false leaf at (ii).  Counterexample to (ii): for `#k ≡ 3 (mod 4)` let
`H = ⟨T₁, w⟩ ⊆ SL₂(k)` be the binary-dihedral (dicyclic) normalizer
of a nonsplit torus — `T₁` the norm-one torus of the quadratic
extension (cyclic of order `#k + 1`), `w² = −1`.  `H` is nonabelian
and irreducible; elements of `T₁` have `k`-rational eigenvalues only
at `±1` (equal pairs), and every coset element `w·t` has trace `0`
and det `1`, hence charpoly `X² + 1`, irreducible over `k` since `−1`
is a nonsquare.  So NO element of `H` has two distinct eigenvalues in
`k`.  (At `p = 3` this `H` is the quaternion group `Q₈ ⊆ SL₂(𝔽₃)`,
the classically notorious small-image case.)  The classical lemma is
applied after a quadratic enlargement of `k`, which this statement's
shape (`α β : k`, `k` fixed) does not perform; an honest direct
discharge would first have to thread that enlargement through
`IsTaylorWilesPrimeSet` and the auxiliary deformation theory.  Hence
the route below is the correct discharge at this shape.

ROUTE (2026-07-24): the hypothesis package contains the classically
unsatisfiable combination of an IRREDUCIBLE hardly ramified residual
`ρbar` over the odd prime `p` — discharged by the same sanctioned
odd-prime dichotomy already discharging the Hecke generation leaf
`topologicalClosure_adjoin_charFrobCoeff_univ_eq_top` above, inlined
from its two upstream inputs: at `p = 3`,
`IsHardlyRamified.mod_three_reducible` (`ModThree.lean`, the
Fontaine/Odlyzko discriminant-bound route) produces a `Γ ℚ`-stable
proper nonzero submodule refuting `hirr` through
`Slop.OddRep.isIrreducible_iff_forall`; at `p ≥ 5` the Family-free
Khare–Wintenberger headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`) refutes `hirr` directly.  Both
imports are already audited acyclic for this file — see the Hecke
generation leaf's ROUTE note.

Both-ways audit: at the intended instantiation this is the cited
lemma (classically valid after the scalar enlargement recorded
above); abstractly the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar` (section audit of
`Interface.lean`), so the statement is also classically true
outright.  CIRCULARITY GUARD (inherited from pillar 3b): must not be
proven through `Family.lean` or anything downstream of it. -/
theorem exists_fixing_rootsOfUnity_charpoly_split.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ) :
    ∃ σ : Field.absoluteGaloisGroup ℚ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 → σ ζ = ζ) ∧
      ∃ α β : k, α ≠ β ∧
        (ρbar σ).charpoly =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) := by
  exfalso
  -- the odd-prime dichotomy, inlined (see the ROUTE note above)
  have hp := (Fact.out : p.Prime)
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · -- `p < 5`: primality and oddness force `p = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    have hp3 : p = 3 := by
      have := hp.two_le
      have := Nat.odd_iff.mp hpodd
      omega
    subst hp3
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
  · -- `p ≥ 5`: the Family-free Khare–Wintenberger headline
    exact absurd hirr
      (not_isIrreducible_of_isHardlyRamified_of_five_le hpodd h5 hW hρbar)

set_option backward.isDefEq.respectTransparency false in
/-- **Existence of a single Taylor–Wiles prime** (PROVEN 2026-07-24
over the group-theoretic leaf): avoiding any given finite set `S` of
places there is a prime `q ≡ 1 (mod p^n)` at which `charFrob ρbar`
splits with distinct roots.  DERIVED from
`exists_fixing_rootsOfUnity_charpoly_split` by Chebotarev density
(`dense_conjClasses_globalFrob`): the locus
`U = {x | charpoly (ρbar x) = (X−α)(X−β)} ∩ {x | x fixes μ_{p^n}}` is
open (the endomorphism space is discrete since `k` is, so the first
set is a preimage of an open set; the second is the fixing subgroup
of the finite extension `ℚ(μ_{p^n})/ℚ`, open in the Krull topology)
and contains `σ`, hence meets the dense union of Frobenius conjugacy
classes off `S ∪ {p}`.  Both conditions transfer from the conjugate
`g·Frob_q·g⁻¹ ∈ U` to `Frob_q` itself (`charpoly` is
conjugation-invariant; the set of `p^n`-th roots of unity is
Galois-stable, so fixing it pointwise is a conjugation-invariant
condition), and at Frobenius they read off as the two arithmetic
conditions: `charFrob` at `q` IS the charpoly at `globalFrob q`
(`charFrob_eq_charpoly_globalFrob`), and the `p`-adic cyclotomic
character takes the value `q` at `Frob_q`
(`cyclotomicCharacter_globalFrob`), so fixing a primitive `p^n`-th
root of unity forces `q ≡ 1 (mod p^n)`. -/
theorem exists_taylorWilesPrime.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))) :
    ∃ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S ∧
      q ≡ 1 [MOD p ^ n] ∧
      ∃ α β : k, α ≠ β ∧
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) := by
  classical
  obtain ⟨σ, hσfix, α, β, hαβ, hσpoly⟩ :=
    exists_fixing_rootsOfUnity_charpoly_split hpodd hW hρbar hirr n
  -- the endomorphism space is discrete, so the eigenvalue locus is open
  letI := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  have hU1open : IsOpen ((fun x : Field.absoluteGaloisGroup ℚ => ρbar x) ⁻¹'
      {φ : Module.End k W | φ.charpoly =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)}) :=
    (isOpen_discrete _).preimage hρcont
  -- the set of `p^n`-th roots of unity is finite …
  have hSfin : {ζ : AlgebraicClosure ℚ | ζ ^ p ^ n = 1}.Finite := by
    refine Set.Finite.subset
      (Polynomial.nthRoots (p ^ n)
        (1 : AlgebraicClosure ℚ)).toFinset.finite_toSet fun ζ hζ => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (pow_pos (Fact.out : p.Prime).pos n)]
    exact hζ
  haveI := hSfin.to_subtype
  haveI : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ
        {ζ : AlgebraicClosure ℚ | ζ ^ p ^ n = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- … so pointwise fixing it is an open condition: it is exactly the
  -- fixing subgroup of the finite extension `ℚ(μ_{p^n})/ℚ`
  have hfixset : {x : Field.absoluteGaloisGroup ℚ |
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 → x ζ = ζ} =
      ((IntermediateField.adjoin ℚ
        {ζ : AlgebraicClosure ℚ | ζ ^ p ^ n = 1}).fixingSubgroup :
        Set (Field.absoluteGaloisGroup ℚ)) := by
    ext x
    constructor
    · intro hx
      have hle : IntermediateField.adjoin ℚ
          {ζ : AlgebraicClosure ℚ | ζ ^ p ^ n = 1} ≤
          IntermediateField.fixedField (Subgroup.zpowers x) := by
        rw [IntermediateField.adjoin_le_iff]
        intro ζ hζ
        rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        intro f hf
        have hst : Subgroup.zpowers x ≤
            MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) ζ :=
          Subgroup.zpowers_le.mpr
            (MulAction.mem_stabilizer_iff.mpr (hx ζ hζ))
        exact hst hf
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun a ha => ?_
      exact (IntermediateField.mem_fixedField_iff _ _).mp (hle ha) x
        (Subgroup.mem_zpowers x)
    · intro hx ζ hζ
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hx ζ
        (IntermediateField.subset_adjoin ℚ _ hζ)
  have hU2open : IsOpen {x : Field.absoluteGaloisGroup ℚ |
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 → x ζ = ζ} := by
    rw [hfixset]
    exact (IntermediateField.adjoin ℚ _).fixingSubgroup_isOpen
  -- Chebotarev density: a Frobenius conjugate off `S ∪ {p}` lies in
  -- the nonempty open locus
  have hdense := dense_conjClasses_globalFrob (K := ℚ)
    (insert (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat S)
  obtain ⟨x, hxU, hxfrob⟩ := hdense.inter_open_nonempty _
    (hU1open.inter hU2open) ⟨σ, hσpoly, hσfix⟩
  obtain ⟨hxpoly, hxfix⟩ := hxU
  obtain ⟨v, hvS, g, rfl⟩ := hxfrob
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
  have hqp : q ≠ p := by
    rintro rfl
    exact hvS (Finset.mem_insert_self _ _)
  have hqS : hq.toHeightOneSpectrumRingOfIntegersRat ∉ S := fun hmem =>
    hvS (Finset.mem_insert_of_mem hmem)
  -- conjugation-invariance of the characteristic polynomial
  have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
    have h1 : ρbar g * ρbar g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact h1
  have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
    have h1 : ρbar g⁻¹ * ρbar g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    exact h1
  have hconj : (ρbar (g * globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
      * g⁻¹)).charpoly =
      (ρbar (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly := by
    have heq : ρbar (g * globalFrob hq.toHeightOneSpectrumRingOfIntegersRat
        * g⁻¹) =
        (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj
          (ρbar (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat)) := by
      ext w
      simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
    rw [heq, LinearEquiv.charpoly_conj]
  -- the `p^n`-th roots of unity are Galois-stable, so `Frob_q` fixes
  -- them because its conjugate does
  have hfrobfix : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 →
      globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ζ = ζ := by
    intro ζ hζ
    have hη : (g ζ) ^ p ^ n = 1 := by rw [← map_pow, hζ, map_one]
    have h1 := hxfix (g ζ) hη
    have h2 : (g * globalFrob hq.toHeightOneSpectrumRingOfIntegersRat * g⁻¹)
        (g ζ) = g (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ζ) := by
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
        AlgEquiv.symm_apply_apply]
    rw [h2] at h1
    exact g.injective h1
  -- … whence `q ≡ 1 (mod p^n)`: the `p`-adic cyclotomic character
  -- takes the value `q` at `Frob_q`, and it fixes a primitive root
  have hmod : q ≡ 1 [MOD p ^ n] := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [pow_zero]
      exact Nat.modEq_one
    · haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure ℚ) (p ^ n)
      have hχ := cyclotomicCharacter_globalFrob (ℓ := p) hq hqp
      have hspec := cyclotomicCharacter.spec p
        (globalFrob hq.toHeightOneSpectrumRingOfIntegersRat).toRingEquiv
        ζ hζ.pow_eq_one
      rw [hχ, map_natCast] at hspec
      have hz : ζ ^ ((q : ZMod (p ^ n))).val = ζ ^ 1 := by
        rw [pow_one, ← hspec]
        exact hfrobfix ζ hζ.pow_eq_one
      have h1lt : 1 < p ^ n :=
        Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
      have hval : ((q : ZMod (p ^ n))).val = 1 :=
        hζ.pow_inj (ZMod.val_lt _) h1lt hz
      show q % p ^ n = 1 % p ^ n
      rw [Nat.mod_eq_of_lt h1lt, ← ZMod.val_natCast]
      exact hval
  refine ⟨q, hq, hqS, hmod, α, β, hαβ, ?_⟩
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob, ← hconj]
  exact hxpoly

/-- **Existence of Taylor–Wiles primes** (patching leaf 1; PROVEN
2026-07-24 over the group-theoretic leaf
`exists_fixing_rootsOfUnity_charpoly_split`): for the irreducible
hardly ramified residual `ρbar` there are Taylor–Wiles prime sets of
every level `n` and every size `r`.  DERIVED by iterating the
single-prime Chebotarev extraction `exists_taylorWilesPrime`, at each
step excluding the (finitely many) places of the primes already
chosen, so the set grows by a genuinely fresh prime.

Both-ways audit: at the intended instantiation this is the cited
Taylor–Wiles prime existence; abstractly the hypothesis set contains
the classically unsatisfiable irreducible hardly ramified `ρbar`
(section audit of `Interface.lean`), so the statement is also
classically true outright.  CIRCULARITY GUARD (inherited from pillar
3b): must not be proven through `Family.lean` or anything downstream
of it. -/
theorem exists_taylorWilesPrimeSet.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n r : ℕ) :
    ∃ Q : Finset ℕ, r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q := by
  classical
  induction r with
  | zero =>
    exact ⟨∅, Nat.zero_le _, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | succ r ih =>
    obtain ⟨Q, hQcard, hQ⟩ := ih
    -- exclude the places of the primes already chosen
    obtain ⟨q, hq, hqS, hqmod, α, β, hαβ, hqpoly⟩ :=
      exists_taylorWilesPrime hpodd hW hρbar hirr n
        (Q.image fun q' =>
          if h : q'.Prime then h.toHeightOneSpectrumRingOfIntegersRat
          else (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat)
    have hqQ : q ∉ Q := fun hmem => hqS (Finset.mem_image.mpr
      ⟨q, hmem, dif_pos hq⟩)
    refine ⟨insert q Q, ?_, fun q' hq' => ?_⟩
    · rw [Finset.card_insert_of_notMem hqQ]
      omega
    · rcases Finset.mem_insert.mp hq' with rfl | hmem
      · exact ⟨hq, hqmod, α, β, hαβ, hqpoly⟩
      · exact hQ q' hmem

set_option linter.checkUnivs false in
/-- **The patched module** — the limit object of the Taylor–Wiles
patching process, recorded with exactly the properties the injectivity
assembly consumes.  Classically (Taylor–Wiles, Ann. of Math. 141
(1995); Diamond, Invent. Math. 128 (1997); Diamond–Darmon–Taylor
(1995), §5.5; Kisin, Ann. of Math. 170 (2009) for the flat-condition
refinement matching `IsFlatAt`), the data is produced by running the
pigeonhole/inverse-limit argument over a tower of Taylor–Wiles levels
`Q_n`:

* `q` is the common size `#Q_n = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` given by
  Wiles's product formula (the numerical coincidence that drives the
  whole method).
* The coefficient ring of the limit is `R_∞ = ℤ_p[[x₁, …, x_q]]`: the
  auxiliary deformation rings `R_{Q_n}` are quotients of a power
  series ring in `q` variables (tangent-space bound from the
  `Q_n`-cohomology count), and in the FLT setting the local conditions
  are SMOOTH — flatness at `p` is Ramakrishna's condition
  (Compositio 87 (1994)), the tame condition at `2` is of CDT ordinary
  type (JAMS 12 (1999), §2) — so the patched deformation ring is the
  full power series ring; this concrete choice is the statement-level
  form of "`R_∞` is regular of dimension `1 + q`".
* `Minf` is the patched Hecke module `M_∞ = lim H_{Q_{n(m)}}/(fixed
  open levels)` with its `R_∞`-action.
* `exists_isRegular` is the Taylor–Wiles freeness input: each `H_Q` is
  finite FREE over the auxiliary group ring `ℤ_p[Δ_Q]` (Taylor–Wiles,
  the key Lemma; Diamond 1997, Thm. 2.1 removes multiplicity one), so
  `M_∞` is finite free over `Λ_∞ = ℤ_p[[S₁, …, S_q]]` and the images
  of the maximal `Λ_∞`-regular sequence `(p, S₁, …, S_q)` form an
  `M_∞`-regular sequence of length `q + 1` inside the maximal ideal of
  `R_∞` — the statement "depth_{R_∞} M_∞ ≥ q + 1 = dim R_∞" in
  regular-sequence vocabulary (mathlib has no depth theory; see the
  section comment).
* `toRuniv` is the patching surjection `R_∞ ↠ R_univ` (classically
  `R_univ = R_∞/(S₁, …, S_q)R_∞`; its existence for the abstract
  `Runiv` of the pillar is Cohen-structure-theoretic: a complete
  Noetherian local `ℤ_p`-algebra with finite residue field is a
  power-series quotient).
* `M0` is the bottom Hecke module (classically `H¹(X₀(N), ℤ_p)_𝔪`, a
  module over the Hecke side `T` of the pillar), `proj` the patching
  identification `M_∞/𝔞M_∞ ≅ M₀` (`𝔞 = ker toRuniv`), stated as: a
  surjective additive map whose kernel is exactly `𝔞·M_∞`
  (`mem_smul_top_of_proj_eq_zero` gives the nontrivial inclusion; the
  reverse is forced by `proj_smul`), and `proj_smul` the ACTION
  COMPATIBILITY: the `R_∞`-action descends through `toRuniv` and `ψ`
  to the `T`-action on `M₀`.  This last field is where the pillar's
  map `ψ` (identified with the classifying map by weak universality
  and trace compatibility) enters the patched situation.

Both-ways audit: at the intended instantiation every field is the
cited patching output; abstractly, inhabitation is asserted only by
`exists_patchedModule` below, whose hypothesis set contains the
classically unsatisfiable irreducible hardly ramified `ρbar`.  (The
`checkUnivs` linter is disabled as for
`HardlyRamifiedFiniteDeformation`: the two module universes are
deliberately independent.) -/
structure PatchedModule.{v, w, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The number of Taylor–Wiles primes at each level (equivalently,
  power-series variables of `R_∞`). -/
  q : ℕ
  /-- The patched module `M_∞`. -/
  Minf : Type v
  [addCommGroupMinf : AddCommGroup Minf]
  [moduleMinf : Module (MvPowerSeries (Fin q) ℤ_[p]) Minf]
  /-- `M_∞` is finite over `R_∞` (patched from module-finiteness at
  every level). -/
  finiteMinf : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) Minf
  /-- The Taylor–Wiles depth input: an `M_∞`-regular sequence of
  length `q + 1` inside the maximal ideal of `R_∞` (the image of the
  maximal regular sequence of `Λ_∞ = ℤ_p[[S₁, …, S_q]]`, over which
  `M_∞` is finite free by the Taylor–Wiles freeness lemma). -/
  exists_isRegular : ∃ rs : List (MvPowerSeries (Fin q) ℤ_[p]),
    rs.length = q + 1 ∧
    (∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p])) ∧
    RingTheory.Sequence.IsRegular Minf rs
  /-- The patching surjection `R_∞ ↠ R_univ`. -/
  toRuniv : MvPowerSeries (Fin q) ℤ_[p] →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The bottom Hecke module (classically `H¹(X₀(N), ℤ_p)_𝔪`). -/
  M0 : Type w
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The bottom identification `M_∞ ↠ M_∞/𝔞M_∞ ≅ M₀`. -/
  proj : Minf →+ M0
  proj_surjective : Function.Surjective proj
  /-- Action compatibility: the `R_∞`-action on `M_∞` descends through
  `toRuniv` and `ψ` to the `T`-action on `M₀`. -/
  proj_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : Minf),
    proj (x • m) = ψ (toRuniv x) • proj m
  /-- The kernel of the bottom identification is exactly the
  augmentation submodule `𝔞·M_∞`, `𝔞 = ker(R_∞ ↠ R_univ)` (this
  inclusion; the reverse follows from `proj_smul`). -/
  mem_smul_top_of_proj_eq_zero : ∀ m : Minf, proj m = 0 →
    m ∈ RingHom.ker toRuniv •
      (⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p]) Minf)

/-! #### The Auslander–Buchsbaum machinery behind patching leaf 3

`free_of_isRegular_mvPowerSeries` (Diamond 1997, Thm. 2.4) is PROVEN
below (2026-07-24) by a dimension induction over Noetherian local
rings — the Auslander–Buchsbaum instance the patching endgame needs,
founded on two mathlib pillars that the earlier audit note missed
(the pin DOES carry a depth layer): the **Rees theorem**
(`ModuleCat.exists_isRegular_tfae`, existence of length-`n`
`M`-regular sequences in `I` ↔ vanishing of `Ext^{<n}(R/I, M)`) and
the **Nakayama dévissage** `Module.free_quotSMulTop_iff_free`
(freeness lifts through the quotient by an `M`-regular element of the
Jacobson radical).  The induction (theorem
`free_of_isRegular_of_ofList_eq_maximalIdeal`): if the maximal ideal
of `R` is SPANNED by a regular sequence `ts` of length `n` — the
statement-level form of "`R` is regular local of dimension `n`" — and
the finite module `M` carries an `M`-regular sequence of length `n`
in the maximal ideal ("depth `M ≥ n`"), then `M` is free.  Step: pick
by Davis coset prime avoidance (`exists_add_notMem_of_forall_not_le`)
a replacement generator `x = t₀ + y`, `y ∈ (ts.tail)`, avoiding every
associated prime of `M` (legitimate because `𝔪 ∉ Ass M`: the head of
`rs` is `M`-regular); then `x` is `M`-regular
(`isSMulRegular_of_forall_notMem_associatedPrimes`), `x :: ts.tail`
is again a spanning regular sequence (permutation invariance
`IsLocalRing.isRegular_of_perm` plus invariance of the last element
modulo the ideal of the earlier ones), `R/(x)` is again a
"power-series-like" Noetherian local ring with spanning regular
sequence of length `n - 1`, the depth hypothesis descends to `M/xM`
by the Rees theorem run through the `Ext` long exact sequence of
`0 → M → M → M/xM → 0` (`exists_isRegular_quotSMulTop_of_isSMulRegular`),
and the induction hypothesis plus the dévissage conclude.  The base
case `n = 0` is a field.  Two concrete power-series leaves feed the
instantiation and stay sorried below: Noetherianity
(`isNoetherianRing_mvPowerSeries`) and the regular system of
parameters `(p, x₁, …, x_q)` spanning the maximal ideal
(`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`). -/

section AuslanderBuchsbaum

open RingTheory.Sequence IsLocalRing Pointwise CategoryTheory Abelian Limits

/-- **Coset prime avoidance** (E. Davis; Kaplansky, *Commutative
Rings*, Thm. 124; PROVEN): if none of the finitely many primes
`P ∈ ps` contains the ideal `(x) + J`, then some element of the coset
`x + J` avoids every `P ∈ ps`.  Used by the Auslander–Buchsbaum
induction to replace the head generator `t₀` of the maximal ideal by
a congruent-mod-tail generator that is regular for the module.
Standard induction on `ps`: primes containing `J` and primes
contained in another listed prime may be discarded; in the remaining
antichain case, if the avoider `y₁` for `ps \ {P₀}` fails at `P₀`,
correct it by `z·∏ a_Q` with `z ∈ J \ P₀` and `a_Q ∈ Q \ P₀`. -/
theorem exists_add_notMem_of_forall_not_le.{u} {R : Type u} [CommRing R]
    (ps : Finset (Ideal R)) (x : R) (J : Ideal R)
    (hps : ∀ P ∈ ps, P.IsPrime) (h : ∀ P ∈ ps, ¬ (Ideal.span {x} ⊔ J ≤ P)) :
    ∃ y ∈ J, ∀ P ∈ ps, x + y ∉ P := by
  classical
  induction ps using Finset.strongInduction with
  | _ ps IH => ?_
  by_cases hJ : ∃ P ∈ ps, J ≤ P
  · obtain ⟨P, hP, hJP⟩ := hJ
    obtain ⟨y, hyJ, hy⟩ := IH (ps.erase P) (Finset.erase_ssubset hP)
      (fun Q hQ => hps Q (Finset.mem_of_mem_erase hQ))
      (fun Q hQ => h Q (Finset.mem_of_mem_erase hQ))
    refine ⟨y, hyJ, fun Q hQ hmem => ?_⟩
    rcases eq_or_ne Q P with rfl | hne
    · refine h Q hP (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) hJP)
      simpa using Q.sub_mem hmem (hJP hyJ)
    · exact hy Q (Finset.mem_erase.mpr ⟨hne, hQ⟩) hmem
  push Not at hJ
  by_cases hchain : ∃ P ∈ ps, ∃ Q ∈ ps, P ≠ Q ∧ P ≤ Q
  · obtain ⟨P, hP, Q, hQ, hne, hle⟩ := hchain
    obtain ⟨y, hyJ, hy⟩ := IH (ps.erase P) (Finset.erase_ssubset hP)
      (fun Q' hQ' => hps Q' (Finset.mem_of_mem_erase hQ'))
      (fun Q' hQ' => h Q' (Finset.mem_of_mem_erase hQ'))
    refine ⟨y, hyJ, fun Q' hQ' hmem => ?_⟩
    rcases eq_or_ne Q' P with rfl | hne'
    · exact hy Q (Finset.mem_erase.mpr ⟨hne.symm, hQ⟩) (hle hmem)
    · exact hy Q' (Finset.mem_erase.mpr ⟨hne', hQ'⟩) hmem
  push Not at hchain
  rcases Finset.eq_empty_or_nonempty ps with rfl | ⟨P₀, hP₀⟩
  · exact ⟨0, J.zero_mem, by simp⟩
  obtain ⟨y₁, hy₁J, hy₁⟩ := IH (ps.erase P₀) (Finset.erase_ssubset hP₀)
    (fun Q hQ => hps Q (Finset.mem_of_mem_erase hQ))
    (fun Q hQ => h Q (Finset.mem_of_mem_erase hQ))
  by_cases hx₀ : x + y₁ ∈ P₀
  · haveI hP₀p : P₀.IsPrime := hps P₀ hP₀
    obtain ⟨z, hzJ, hzP₀⟩ := SetLike.not_le_iff_exists.mp (hJ P₀ hP₀)
    have hpick : ∀ Q ∈ ps.erase P₀, ∃ a, a ∈ Q ∧ a ∉ P₀ := by
      intro Q hQ
      obtain ⟨hne, hQps⟩ := Finset.mem_erase.mp hQ
      exact SetLike.not_le_iff_exists.mp (fun hle => hchain Q hQps P₀ hP₀ hne hle)
    choose a haQ haP using hpick
    set w₀ : R := ∏ Q ∈ (ps.erase P₀).attach, a Q.1 Q.2 with hw₀def
    have hw₀Q : ∀ Q ∈ ps.erase P₀, w₀ ∈ Q := by
      intro Q hQ
      rw [hw₀def, ← Finset.mul_prod_erase _ _ (Finset.mem_attach _ ⟨Q, hQ⟩)]
      exact Ideal.mul_mem_right _ _ (haQ Q hQ)
    have hprodNotMem : w₀ ∉ P₀ := fun hmem => by
      obtain ⟨⟨Q, hQ⟩, -, hmemQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact haP Q hQ hmemQ
    refine ⟨y₁ + z * w₀, J.add_mem hy₁J (J.mul_mem_right _ hzJ), fun Q hQ hmem => ?_⟩
    by_cases hne : Q = P₀
    · have hw : z * w₀ ∈ P₀ := by
        have := P₀.sub_mem (hne ▸ hmem) hx₀
        simpa [add_sub_add_left_eq_sub] using this
      exact (hP₀p.mem_or_mem hw).elim hzP₀ hprodNotMem
    · have hwQ : z * w₀ ∈ Q := Q.mul_mem_left z (hw₀Q Q (Finset.mem_erase.mpr ⟨hne, hQ⟩))
      have : x + y₁ ∈ Q := by
        have := Q.sub_mem hmem hwQ
        simpa [← add_assoc] using this
      exact hy₁ Q (Finset.mem_erase.mpr ⟨hne, hQ⟩) this
  · refine ⟨y₁, hy₁J, fun Q hQ => ?_⟩
    rcases eq_or_ne Q P₀ with rfl | hne
    · exact hx₀
    · exact hy₁ Q (Finset.mem_erase.mpr ⟨hne, hQ⟩)

/-- **Avoiding all associated primes gives a regular element**
(PROVEN): over a Noetherian ring the zero-divisors of a module lie in
the union of its associated primes — if `x·z = 0` with `z ≠ 0` then
`ann(z)` sits inside an associated prime
(`exists_le_isAssociatedPrime_of_isNoetherianRing`). -/
theorem isSMulRegular_of_forall_notMem_associatedPrimes.{u, w} {R : Type u} [CommRing R]
    [IsNoetherianRing R] {N : Type w} [AddCommGroup N] [Module R N] {x : R}
    (h : ∀ P ∈ associatedPrimes R N, x ∉ P) : IsSMulRegular N x := by
  intro a b hab
  by_contra hne
  have hz : x • (a - b) = 0 := by
    simp only [smul_sub, sub_eq_zero]
    exact hab
  obtain ⟨P, hP, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R (a - b) (sub_ne_zero.mpr hne)
  exact h P hP (hle (by rw [Submodule.mem_colon_singleton]; simpa using hz))

/-- **Positive depth pushes the maximal ideal off `Ass N`** (PROVEN):
if some element of the maximal ideal acts regularly on `N`, no
associated prime of `N` can contain the maximal ideal (an associated
prime is the radical of the annihilator of a nonzero element, and a
power of the regular element would kill that element).  This is the
legitimacy check for prime avoidance against `Ass N` inside the
maximal ideal. -/
theorem not_maximalIdeal_le_of_mem_associatedPrimes.{u, w} {R : Type u} [CommRing R]
    [IsLocalRing R] {N : Type w} [AddCommGroup N] [Module R N]
    {P : Ideal R} (hP : P ∈ associatedPrimes R N)
    {r : R} (hr : r ∈ maximalIdeal R) (hreg : IsSMulRegular N r) :
    ¬ maximalIdeal R ≤ P := by
  intro hle
  obtain ⟨hprime, z, hz⟩ := hP
  have hzne : z ≠ 0 := by
    rintro rfl
    rw [Submodule.colon_singleton_zero, Ideal.radical_top] at hz
    exact hprime.ne_top hz
  have hrP : r ∈ P := hle hr
  rw [hz, Ideal.mem_radical_iff] at hrP
  obtain ⟨k, hk⟩ := hrP
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hk
  exact hzne ((hreg.pow k) (by simpa using hk))

/-- **Depth descent along a regular element** (PROVEN; the classical
`depth (M/xM) = depth M − 1`, in existence form): if the finite
module `M` over the Noetherian local `R` carries an `M`-regular
sequence `rs` inside the maximal ideal and `x ∈ 𝔪` is `M`-regular,
then `M/xM` carries a regular sequence of length `|rs| − 1` inside
the maximal ideal.  Both directions of mathlib's Rees theorem
(`ModuleCat.exists_isRegular_tfae`) are used: `rs` gives
`Ext^{<n}(k, M) = 0`; the `Ext(k, −)` long exact sequence of
`0 → M →ₓ M → M/xM → 0` (via `Ext.covariant_sequence_exact₃'` on
`IsSMulRegular.smulShortComplex_shortExact`) kills
`Ext^{<n−1}(k, M/xM); Rees back-translates into a regular sequence on
`M/xM`. -/
theorem exists_isRegular_quotSMulTop_of_isSMulRegular.{u, w} {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Small.{w} R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {rs : List R} (hreg : RingTheory.Sequence.IsRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ rs' : List R, rs'.length = rs.length - 1 ∧
      (∀ r ∈ rs', r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs' := by
  have smul_lt : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_ne le_top
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (le_trans (maximalIdeal_le_jacobson _) (Ideal.jacobson_mono bot_le))).symm
  haveI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have smul_lt' : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ :=
    lt_of_le_of_ne le_top
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (le_trans (maximalIdeal_le_jacobson _) (Ideal.jacobson_mono bot_le))).symm
  have tfae₁ := ModuleCat.exists_isRegular_tfae (maximalIdeal R) rs.length
    (ModuleCat.of R M) smul_lt
  have h4 : ∃ rs₀ : List R, rs₀.length = rs.length ∧ (∀ r ∈ rs₀, r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (ModuleCat.of R M) rs₀ := ⟨rs, rfl, hmem, hreg⟩
  have hext := (tfae₁.out 3 1).mp h4
  have hxreg' : IsSMulRegular (ModuleCat.of R M) x := hxreg
  have hext' : ∀ i < rs.length - 1, Subsingleton
      (Ext (ModuleCat.of R (Shrink.{w} (R ⧸ maximalIdeal R)))
        (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' _ hxreg'.smulShortComplex_shortExact) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have tfae₂ := ModuleCat.exists_isRegular_tfae (maximalIdeal R) (rs.length - 1)
    (ModuleCat.of R (QuotSMulTop x M)) smul_lt'
  exact (tfae₂.out 1 3).mp hext'

/-- **The abstract Auslander–Buchsbaum instance** (PROVEN; Diamond
1997, Thm. 2.4 in spanning-regular-sequence form): over a Noetherian
local ring whose maximal ideal is SPANNED by a regular sequence of
length `n` (the statement-level form of "regular local of dimension
`n`"), any finite module carrying a regular sequence of length `n`
inside the maximal ideal ("depth ≥ dim") is free.  Dimension
induction over `(R, M) ↝ (R/(x), M/xM)`; see the section header for
the full architecture. -/
theorem free_of_isRegular_of_ofList_eq_maximalIdeal.{u, w} (n : ℕ)
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{w} R]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ts : List R) (hts : RingTheory.Sequence.IsRegular R ts) (htslen : ts.length = n)
    (htsspan : Ideal.ofList ts = maximalIdeal R)
    (rs : List R) (hrs : RingTheory.Sequence.IsRegular M rs) (hrslen : rs.length = n)
    (hrsmem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    Module.Free R M := by
  induction n generalizing R M with
  | zero =>
    -- the base case: `𝔪 = (∅) = ⊥`, so `R` is a field
    have hbot : maximalIdeal R = ⊥ := by
      rw [← htsspan, List.length_eq_zero_iff.mp htslen, Ideal.ofList_nil]
    have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
    letI := hfield.toField
    exact Module.Free.of_divisionRing R M
  | succ n IH =>
    rcases subsingleton_or_nontrivial M with _hM | _hM
    · infer_instance
    obtain ⟨t₀, ts', rfl⟩ : ∃ a l, ts = a :: l := by
      cases ts with
      | nil => simp at htslen
      | cons a l => exact ⟨a, l, rfl⟩
    obtain ⟨r₀, rs', rfl⟩ : ∃ a l, rs = a :: l := by
      cases rs with
      | nil => simp at hrslen
      | cons a l => exact ⟨a, l, rfl⟩
    have hmem_ts : ∀ t ∈ t₀ :: ts', t ∈ maximalIdeal R := fun t ht =>
      htsspan ▸ Ideal.subset_span ht
    have hr₀ : IsSMulRegular M r₀ := ((isRegular_cons_iff _ _ _).mp hrs).1
    have hr₀m : r₀ ∈ maximalIdeal R := hrsmem r₀ List.mem_cons_self
    -- Davis avoidance: replace `t₀` by `x = t₀ + y`, `y ∈ (ts')`, avoiding
    -- every associated prime of `M` (all of which miss `𝔪 = (t₀) ⊔ (ts')`
    -- because `r₀ ∈ 𝔪` is `M`-regular)
    have hfin : (associatedPrimes R M).Finite := associatedPrimes.finite R M
    obtain ⟨y, hyJ, hy⟩ := exists_add_notMem_of_forall_not_le hfin.toFinset t₀
      (Ideal.ofList ts')
      (fun P hP => (hfin.mem_toFinset.mp hP).1)
      (fun P hP hle => by
        rw [← Ideal.ofList_cons, htsspan] at hle
        exact not_maximalIdeal_le_of_mem_associatedPrimes
          (hfin.mem_toFinset.mp hP) hr₀m hr₀ hle)
    set x := t₀ + y with hxdef
    have hxm : x ∈ maximalIdeal R := by
      apply (maximalIdeal R).add_mem (hmem_ts t₀ List.mem_cons_self)
      rw [← htsspan, Ideal.ofList_cons]
      exact Ideal.mem_sup_right hyJ
    have hxM : IsSMulRegular M x := isSMulRegular_of_forall_notMem_associatedPrimes
      (fun P hP => hy P (hfin.mem_toFinset.mpr hP))
    -- `x :: ts'` is again a spanning regular sequence: permute `t₀` to the
    -- end, exchange it there for the congruent-mod-`(ts')` element `x`,
    -- permute back
    have hperm₁ : RingTheory.Sequence.IsRegular R (ts' ++ [t₀]) :=
      IsLocalRing.isRegular_of_perm hts (List.perm_append_singleton t₀ ts').symm
    have hlastswap : RingTheory.Sequence.IsRegular R (ts' ++ [x]) := by
      refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ ?_ ?_
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hmem_ts r (List.mem_cons_of_mem _ hr)
        · rw [List.mem_singleton.mp hr]; exact hxm
      · have hw := hperm₁.toIsWeaklyRegular
        rw [isWeaklyRegular_append_iff] at hw ⊢
        refine ⟨hw.1, ?_⟩
        obtain ⟨-, ht₀q⟩ := hw
        rw [isWeaklyRegular_singleton_iff] at ht₀q ⊢
        have hy0 : ∀ c : R ⧸ (Ideal.ofList ts' • ⊤ : Submodule R R), y • c = 0 := by
          intro c
          obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_smul hyJ trivial
        intro a b hab
        refine ht₀q (?_ : t₀ • a = t₀ • b)
        have h1 : x • a = t₀ • a := by rw [hxdef, add_smul, hy0, add_zero]
        have h2 : x • b = t₀ • b := by rw [hxdef, add_smul, hy0, add_zero]
        rw [← h1, ← h2]
        exact hab
    have hxts : RingTheory.Sequence.IsRegular R (x :: ts') :=
      IsLocalRing.isRegular_of_perm hlastswap (List.perm_append_singleton x ts')
    -- the quotient ring `R/(x)` is Noetherian local with maximal ideal
    -- spanned by the images of `ts'`
    haveI hR'nt : Nontrivial (R ⧸ Ideal.span {x}) :=
      Submodule.Quotient.nontrivial_iff.mpr
        (Ideal.span_singleton_ne_top ((IsLocalRing.mem_maximalIdeal x).mp hxm))
    haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI : Small.{w} (R ⧸ Ideal.span {x}) :=
      small_of_surjective Ideal.Quotient.mk_surjective
    have hm' : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R) =
        maximalIdeal (R ⧸ Ideal.span {x}) :=
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
    have hQts' : RingTheory.Sequence.IsRegular (QuotSMulTop x R) ts' :=
      ((isRegular_cons_iff _ _ _).mp hxts).2
    have heq : (x • ⊤ : Submodule R R) = (Ideal.span {x} : Ideal R) := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    have hRts' : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x}) ts' :=
      ((Submodule.quotEquivOfEq _ _ heq).isRegular_congr ts').mp hQts'
    have htss_weak : IsWeaklyRegular (R ⧸ Ideal.span {x})
        (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      (isWeaklyRegular_map_algebraMap_iff _ _ ts').mpr hRts'.toIsWeaklyRegular
    have hmem'' : ∀ r ∈ ts'.map (algebraMap R (R ⧸ Ideal.span {x})),
        r ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [Ideal.Quotient.algebraMap_eq]
      exact hm' ▸ Ideal.mem_map_of_mem _ (hmem_ts t (List.mem_cons_of_mem _ ht))
    have htss : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x})
        (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hmem'' htss_weak
    have htssspan : Ideal.ofList (ts'.map (algebraMap R (R ⧸ Ideal.span {x}))) =
        maximalIdeal (R ⧸ Ideal.span {x}) := by
      rw [Ideal.Quotient.algebraMap_eq, ← Ideal.map_ofList, ← hm']
      conv_rhs => rw [← htsspan, Ideal.ofList_cons, Ideal.map_sup]
      refine (sup_eq_right.mpr ?_).symm
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      have ht₀y : (Ideal.Quotient.mk (Ideal.span {x})) t₀ = - Ideal.Quotient.mk _ y := by
        rw [eq_neg_iff_add_eq_zero, ← map_add, Ideal.Quotient.eq_zero_iff_mem, ← hxdef]
        exact Ideal.mem_span_singleton_self x
      rw [ht₀y]
      exact neg_mem (Ideal.mem_map_of_mem _ hyJ)
    -- depth descent to `M/xM`, and transfer of the sequence to `R/(x)`
    haveI hMnt' : Nontrivial (QuotSMulTop x M) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    obtain ⟨rs₂, hrs₂len, hrs₂mem, hrs₂⟩ :=
      exists_isRegular_quotSMulTop_of_isSMulRegular hrs hrsmem hxm hxM
    haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hrs₂w : IsWeaklyRegular (QuotSMulTop x M)
        (rs₂.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      (isWeaklyRegular_map_algebraMap_iff _ _ rs₂).mpr hrs₂.toIsWeaklyRegular
    have hrs₂mem' : ∀ r ∈ rs₂.map (algebraMap R (R ⧸ Ideal.span {x})),
        r ∈ maximalIdeal (R ⧸ Ideal.span {x}) := by
      intro r hr
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
      rw [Ideal.Quotient.algebraMap_eq]
      exact hm' ▸ Ideal.mem_map_of_mem _ (hrs₂mem t ht)
    have hrs₂' : RingTheory.Sequence.IsRegular (QuotSMulTop x M)
        (rs₂.map (algebraMap R (R ⧸ Ideal.span {x}))) :=
      IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hrs₂mem' hrs₂w
    have hts'len : ts'.length = n := by simpa using htslen
    have hrs₂len' : rs₂.length = n := by
      rw [hrs₂len]
      simp only [List.length_cons] at hrslen ⊢
      omega
    -- induction hypothesis downstairs, Nakayama dévissage upstairs
    haveI := Module.finitePresentation_of_finite R M
    refine (Module.free_quotSMulTop_iff_free R M
      (maximalIdeal_le_jacobson ⊥ hxm) hxM).mp ?_
    exact IH (R := R ⧸ Ideal.span {x}) (M := QuotSMulTop x M)
      (ts'.map (algebraMap R _)) htss (by simpa using hts'len) htssspan
      (rs₂.map (algebraMap R _)) hrs₂' (by simpa using hrs₂len') hrs₂mem'

/-! ### The power-series plumbing: currying `A[[x₀, …, xₙ]]`

Both remaining power-series facts — Noetherianity of
`MvPowerSeries (Fin n) A` and the regular system of parameters of
`ℤ_p[[x₁, …, x_q]]` — reduce by induction on the number of variables
to mathlib's ONE-variable theory (`IsNoetherianRing B⟦X⟧`, regularity
of `X`, the maximal ideal of `B⟦X⟧` over a local `B`) along the
currying isomorphism

`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)`,

which mathlib does not have (only the polynomial analogue
`MvPolynomial.finSuccEquiv` exists).  It is built here by hand from
the exponent equivalence `(Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ)`
(`Finsupp.optionElim`/`Finsupp.some`): multiplicativity is the
antidiagonal-splitting computation
`antidiagonal (optionElim n d) ≃ antidiagonal n ×ˢ antidiagonal d`.
The successor case of the induction goes through
`MvPowerSeries.renameEquiv` along `finSuccEquiv : Fin (n+1) ≃ Option (Fin n)`.
-/

section PowerSeriesCurry

open PowerSeries

variable {σ : Type*} {A : Type*} [CommRing A] {B : Type*} [CommRing B]

/-- Additivity of the exponent currying `Finsupp.optionElim`: splitting
off the `none`-coordinate is an additive bijection
`(Option σ →₀ ℕ) ≃ ℕ × (σ →₀ ℕ)`. -/
lemma optionElim_add {α M : Type*} [AddZeroClass M] (y₁ y₂ : M) (f₁ f₂ : α →₀ M) :
    Finsupp.optionElim (y₁ + y₂) (f₁ + f₂) =
      Finsupp.optionElim y₁ f₁ + Finsupp.optionElim y₂ f₂ := by
  ext a; cases a <;> simp

/-- **Currying a multivariate power series** in the distinguished
variable indexed by `none`: `A[[(xᵢ)_{i : Option σ}]] → (A[[(xᵢ)_{i : σ}]])⟦X⟧`,
`f ↦ Σₙ (Σ_d coeff (optionElim n d) f · x^d) Xⁿ`. -/
noncomputable def optionCurry (f : MvPowerSeries (Option σ) A) :
    PowerSeries (MvPowerSeries σ A) :=
  PowerSeries.mk fun n =>
    (fun d => MvPowerSeries.coeff (Finsupp.optionElim n d) f : MvPowerSeries σ A)

/-- The inverse of `optionCurry`: read the coefficient of the exponent
`u` off the `u none`-th coefficient of the outer series. -/
noncomputable def optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    MvPowerSeries (Option σ) A :=
  fun u => MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F)

lemma coeff_optionCurry (f : MvPowerSeries (Option σ) A) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optionCurry f)) =
      MvPowerSeries.coeff (Finsupp.optionElim n d) f := by
  simp [optionCurry, MvPowerSeries.coeff_apply]

lemma coeff_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) (u : Option σ →₀ ℕ) :
    MvPowerSeries.coeff u (optionUncurry F) =
      MvPowerSeries.coeff u.some (PowerSeries.coeff (u none) F) := by
  simp [optionUncurry, MvPowerSeries.coeff_apply]

lemma optionUncurry_optionCurry (f : MvPowerSeries (Option σ) A) :
    optionUncurry (optionCurry f) = f := by
  ext u
  rw [coeff_optionUncurry, coeff_optionCurry, Finsupp.optionElim_some]

lemma optionCurry_optionUncurry (F : PowerSeries (MvPowerSeries σ A)) :
    optionCurry (optionUncurry F) = F := by
  ext n d
  rw [coeff_optionCurry, coeff_optionUncurry, Finsupp.optionElim_apply_none,
    Finsupp.some_optionElim]

lemma optionCurry_add (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f + g) = optionCurry f + optionCurry g := by
  ext n d
  simp [coeff_optionCurry]

/-- Multiplicativity of the currying map: the antidiagonal of
`optionElim n d` splits as the product of the antidiagonals of `n` and
of `d`, which is exactly the Cauchy product of the curried series. -/
lemma optionCurry_mul (f g : MvPowerSeries (Option σ) A) :
    optionCurry (f * g) = optionCurry f * optionCurry g := by
  classical
  ext n d
  rw [coeff_optionCurry, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  simp only [MvPowerSeries.coeff_mul, coeff_optionCurry]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun u => ((u.1 none, u.2 none), (u.1.some, u.2.some)))
    (j := fun v => (Finsupp.optionElim v.1.1 v.2.1, Finsupp.optionElim v.1.2 v.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ hu
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hu
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have := congrArg (fun x => (x : Option σ →₀ ℕ) none) hu
      simpa using this
    · have := congrArg Finsupp.some hu
      simpa using this
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ hv
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at hv
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [← optionElim_add, hv.1, hv.2]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ _
    simp [Finsupp.some_optionElim]
  · rintro ⟨u, v⟩ _
    simp [Finsupp.optionElim_some]

/-- **The currying isomorphism**
`MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)` — the
power-series analogue of `MvPolynomial.finSuccEquiv`, the shared
gadget behind both power-series leaves below. -/
noncomputable def optionCurryEquiv (σ : Type*) (A : Type*) [CommRing A] :
    MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A) where
  toFun := optionCurry
  invFun := optionUncurry
  left_inv := optionUncurry_optionCurry
  right_inv := optionCurry_optionUncurry
  map_mul' := optionCurry_mul
  map_add' := optionCurry_add

/-- Power series in an empty family of variables are just constants
(the base case of both inductions). -/
noncomputable def mvPowerSeriesIsEmptyRingEquiv (σ : Type*) (A : Type*) [IsEmpty σ]
    [CommRing A] : A ≃+* MvPowerSeries σ A :=
  RingEquiv.ofBijective MvPowerSeries.C ⟨MvPowerSeries.C_injective, MvPowerSeries.C_surjective⟩

/-- `X` is a nonzerodivisor of `B⟦X⟧`: multiplication by `X` shifts
coefficients, hence is injective. -/
lemma isSMulRegular_powerSeries_X : IsSMulRegular (PowerSeries B) (X : PowerSeries B) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  have := congrArg (PowerSeries.coeff (n + 1)) h
  rwa [coeff_succ_X_mul, coeff_succ_X_mul] at this

lemma smul_top_eq_span_powerSeries_X :
    ((X : PowerSeries B) • ⊤ : Submodule (PowerSeries B) (PowerSeries B)) =
      (Ideal.span {(X : PowerSeries B)} : Ideal (PowerSeries B)) := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

lemma ker_powerSeries_constantCoeff :
    RingHom.ker (constantCoeff (R := B)) = Ideal.span {(X : PowerSeries B)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

lemma powerSeries_constantCoeff_surjective :
    Function.Surjective (constantCoeff (R := B)) := fun b => ⟨C b, constantCoeff_C b⟩

/-- `B⟦X⟧ / (X) ≃+* B` through the constant coefficient. -/
noncomputable def quotXRingEquiv (B : Type*) [CommRing B] :
    (PowerSeries B ⧸ Ideal.span {(X : PowerSeries B)}) ≃+* B :=
  (Ideal.quotEquivOfEq ker_powerSeries_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective powerSeries_constantCoeff_surjective)

/-- The same identification, read on the module quotient
`QuotSMulTop X B⟦X⟧` in which the regular-sequence recursion lives. -/
noncomputable def quotXAddEquiv (B : Type*) [CommRing B] :
    QuotSMulTop (X : PowerSeries B) (PowerSeries B) ≃+ B :=
  ((Submodule.quotEquivOfEq _ _ smul_top_eq_span_powerSeries_X).toAddEquiv).trans
    (quotXRingEquiv B).toAddEquiv

lemma quotXAddEquiv_mk (f : PowerSeries B) :
    quotXAddEquiv B (Submodule.Quotient.mk f :
      QuotSMulTop (X : PowerSeries B) (PowerSeries B)) = constantCoeff f := rfl

/-- Semilinearity of that identification over `C : B →+* B⟦X⟧`: the
scalar `C t` upstairs acts as `t` downstairs. -/
lemma quotXAddEquiv_smul (t : B) (x : QuotSMulTop (X : PowerSeries B) (PowerSeries B)) :
    quotXAddEquiv B ((C t : PowerSeries B) • x) = t • quotXAddEquiv B x := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    rw [← Submodule.Quotient.mk_smul, quotXAddEquiv_mk, quotXAddEquiv_mk]
    simp [smul_eq_mul]

lemma mem_maximalIdeal_powerSeries [IsLocalRing B] (f : PowerSeries B) :
    f ∈ maximalIdeal (PowerSeries B) ↔ constantCoeff f ∈ maximalIdeal B := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]

/-- The maximal ideal of `B⟦X⟧` over a local `B` is `(X) + 𝔪_B·B⟦X⟧`:
split `f = C (constantCoeff f) + X · g`. -/
lemma maximalIdeal_powerSeries (B : Type*) [CommRing B] [IsLocalRing B] :
    maximalIdeal (PowerSeries B) =
      Ideal.span {(X : PowerSeries B)} ⊔ (maximalIdeal B).map (C : B →+* PowerSeries B) := by
  apply le_antisymm
  · intro f hf
    rw [mem_maximalIdeal_powerSeries] at hf
    obtain ⟨g, hg⟩ : (X : PowerSeries B) ∣ (f - C (constantCoeff f)) := by rw [X_dvd_iff]; simp
    have hfeq : f = C (constantCoeff f) + X * g := by rw [← hg]; ring
    rw [hfeq]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hf))
      (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  · refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        mem_maximalIdeal_powerSeries]
      simp
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, mem_maximalIdeal_powerSeries, constantCoeff_C]
      exact hm

/-- **The one-variable step**: prepending `X` to a regular sequence
spanning `𝔪_B` gives a regular sequence spanning `𝔪_{B⟦X⟧}`.  `X` is
regular on `B⟦X⟧`, the quotient by it is `B` (`quotXAddEquiv`), and
the spanning statement is `maximalIdeal_powerSeries`. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_powerSeries (B : Type*) [CommRing B]
    [IsLocalRing B] (k : ℕ)
    (h : ∃ ts : List B, ts.length = k ∧ RingTheory.Sequence.IsRegular B ts ∧
      Ideal.ofList ts = maximalIdeal B) :
    ∃ ts : List (PowerSeries B), ts.length = k + 1 ∧
      RingTheory.Sequence.IsRegular (PowerSeries B) ts ∧
      Ideal.ofList ts = maximalIdeal (PowerSeries B) := by
  obtain ⟨ts, hlen, hreg, hspan⟩ := h
  refine ⟨X :: ts.map C, by simp [hlen], ?_, ?_⟩
  · rw [isRegular_cons_iff]
    refine ⟨isSMulRegular_powerSeries_X,
      (AddEquiv.isRegular_congr (e := quotXAddEquiv B) ?_).mpr hreg⟩
    exact List.forall₂_map_left_iff.mpr
      (List.forall₂_same.mpr fun t _ x => quotXAddEquiv_smul t x)
  · rw [Ideal.ofList_cons, ← Ideal.map_ofList, hspan]
    exact (maximalIdeal_powerSeries B).symm

/-- Transport of "the maximal ideal is spanned by a regular sequence of
length `k`" along a ring isomorphism of local rings. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {k : ℕ}
    (h : ∃ ts : List R, ts.length = k ∧ RingTheory.Sequence.IsRegular R ts ∧
      Ideal.ofList ts = maximalIdeal R) :
    ∃ ts : List S, ts.length = k ∧ RingTheory.Sequence.IsRegular S ts ∧
      Ideal.ofList ts = maximalIdeal S := by
  obtain ⟨ts, hlen, hreg, hspan⟩ := h
  refine ⟨ts.map e, by simpa using hlen, ?_, ?_⟩
  · refine (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun t _ x => by simp [smul_eq_mul])
  · have h2 : Ideal.ofList (ts.map (e : R →+* S)) = maximalIdeal S := by
      rw [← Ideal.map_ofList, hspan]
      exact map_maximalIdeal_of_surjective (e : R →+* S) e.surjective
    exact h2

/-- The base case: `𝔪_{ℤ_p} = (p)` is spanned by the length-one regular
sequence `[p]` (`p` is a nonzerodivisor of the domain `ℤ_p`). -/
theorem exists_isRegular_ofList_eq_maximalIdeal_padicInt (p : ℕ) [Fact p.Prime] :
    ∃ ts : List ℤ_[p], ts.length = 0 + 1 ∧ RingTheory.Sequence.IsRegular ℤ_[p] ts ∧
      Ideal.ofList ts = maximalIdeal ℤ_[p] := by
  have hmem : ∀ r ∈ [(p : ℤ_[p])], r ∈ maximalIdeal ℤ_[p] := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hp : IsSMulRegular ℤ_[p] (p : ℤ_[p]) := by
    intro x y h
    simp only [smul_eq_mul] at h
    exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne _) h
  refine ⟨[(p : ℤ_[p])], rfl,
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal ℤ_[p] hmem
      (IsWeaklyRegular.cons hp (IsWeaklyRegular.nil _ _)), ?_⟩
  rw [Ideal.ofList_singleton, PadicInt.maximalIdeal_eq_span_p]

end PowerSeriesCurry

/-- **Noetherianity of `A[[x₁, …, xₙ]]`** (power-series leaf; PROVEN
2026-07-24): finite-variable power series over a Noetherian
commutative ring are Noetherian.  Unconditionally true, zero
arithmetic content.  Proven by induction on the number of variables:
the empty case is `mvPowerSeriesIsEmptyRingEquiv` (`A[[]] ≃+* A`), and
the successor case transports mathlib's `IsNoetherianRing B⟦X⟧` (the
power-series Hilbert basis theorem) along the currying isomorphism
`MvPowerSeries (Fin (n+1)) A ≃+* PowerSeries (MvPowerSeries (Fin n) A)`
(`optionCurryEquiv` composed with `MvPowerSeries.renameEquiv` along
`finSuccEquiv`).  Consumed by `free_of_isRegular_mvPowerSeries` to
feed the Auslander–Buchsbaum induction. -/
theorem isNoetherianRing_mvPowerSeries.{uA} (n : ℕ) {A : Type uA} [CommRing A]
    [IsNoetherianRing A] : IsNoetherianRing (MvPowerSeries (Fin n) A) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv A (mvPowerSeriesIsEmptyRingEquiv (Fin 0) A)
  | succ n ih =>
    haveI := ih
    exact isNoetherianRing_of_ringEquiv _
      (((MvPowerSeries.renameEquiv A (finSuccEquiv n)).toRingEquiv.trans
        (optionCurryEquiv (Fin n) A)).symm)

/-- **The regular system of parameters of `ℤ_p[[x₁, …, x_q]]`**
(power-series leaf; PROVEN 2026-07-24): the maximal ideal of
`R_∞ = ℤ_p[[x₁, …, x_q]]` is spanned by a regular sequence of length
`q + 1` — concretely the image of `(x_q, …, x_1, p)` under the
currying isomorphisms.  Unconditionally true, zero arithmetic content.
Proven by induction on the number of variables from the one-variable
step `exists_isRegular_ofList_eq_maximalIdeal_powerSeries` (prepending
`X` to a regular system of parameters of the local base `B` gives one
of `B⟦X⟧`: `X` is a nonzerodivisor, `B⟦X⟧/(X) ≃ B`, and
`𝔪_{B⟦X⟧} = (X) + 𝔪_B·B⟦X⟧`), based at
`𝔪_{ℤ_p} = (p)` (`exists_isRegular_ofList_eq_maximalIdeal_padicInt`)
and transported at each step along
`MvPowerSeries (Fin (q+1)) ℤ_p ≃+* (MvPowerSeries (Fin q) ℤ_p)⟦X⟧`.
Consumed by `free_of_isRegular_mvPowerSeries`. -/
theorem exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries (p : ℕ) [Fact p.Prime]
    (q : ℕ) :
    ∃ ts : List (MvPowerSeries (Fin q) ℤ_[p]), ts.length = q + 1 ∧
      RingTheory.Sequence.IsRegular (MvPowerSeries (Fin q) ℤ_[p]) ts ∧
      Ideal.ofList ts = maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
  induction q with
  | zero =>
    exact exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv
      (mvPowerSeriesIsEmptyRingEquiv (Fin 0) ℤ_[p])
      (exists_isRegular_ofList_eq_maximalIdeal_padicInt p)
  | succ q ih =>
    exact exists_isRegular_ofList_eq_maximalIdeal_of_ringEquiv
      (((MvPowerSeries.renameEquiv ℤ_[p] (finSuccEquiv q)).toRingEquiv.trans
        (optionCurryEquiv (Fin q) ℤ_[p])).symm)
      (exists_isRegular_ofList_eq_maximalIdeal_powerSeries _ (q + 1) ih)

/-- **The commutative-algebra endgame** (patching leaf 3; PROVEN
2026-07-24): a finite module over the regular local ring
`R_∞ = ℤ_p[[x₁, …, x_q]]` carrying a regular sequence of length
`q + 1 = dim R_∞` inside the maximal ideal — i.e. of depth at least
`dim R_∞` — is FREE.  This is the Auslander–Buchsbaum step of the
patching argument (Diamond, *The Taylor–Wiles construction and
multiplicity one*, Invent. Math. 128 (1997), Thm. 2.4: over a regular
local ring, `depth M ≥ dim R` forces `pd M = 0`; see also
Diamond–Darmon–Taylor (1995), Thm. 5.28 and Bruns–Herzog,
*Cohen–Macaulay rings*, Thm. 1.3.3 + 2.2.7).  Unconditionally true —
no arithmetic content.  Proven as the instantiation of the abstract
dimension induction `free_of_isRegular_of_ofList_eq_maximalIdeal`
(Rees theorem + Davis avoidance + Nakayama dévissage; see the section
header above) at the two concrete power-series leaves
`isNoetherianRing_mvPowerSeries` and
`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`. -/
theorem free_of_isRegular_mvPowerSeries.{v} {p : ℕ} [Fact p.Prime] {q : ℕ}
    {M : Type v} [AddCommGroup M]
    [Module (MvPowerSeries (Fin q) ℤ_[p]) M]
    (hfin : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) M)
    {rs : List (MvPowerSeries (Fin q) ℤ_[p])} (hlen : rs.length = q + 1)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin q) ℤ_[p]))
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    Module.Free (MvPowerSeries (Fin q) ℤ_[p]) M := by
  haveI := hfin
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p]) :=
    isNoetherianRing_mvPowerSeries q
  obtain ⟨ts, htslen, hts, htsspan⟩ :=
    exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries p q
  exact free_of_isRegular_of_ofList_eq_maximalIdeal (q + 1) ts hts htslen htsspan
    rs hreg hlen hmem

end AuslanderBuchsbaum

/-- **The patched faithfulness assembly** (PROVEN): a `PatchedModule`
for `ψ` forces `ψ` to be injective.  This is the classical endgame of
Taylor–Wiles patching, written out: by the Auslander–Buchsbaum leaf
(`free_of_isRegular_mvPowerSeries`) the patched module `M_∞` is free
over `R_∞`; picking a basis vector `e` and an element
`x ∈ R_∞` lifting a given `r ∈ ker ψ` (via the patching surjection
`toRuniv`), the action compatibility `proj_smul` shows
`proj (x • e) = ψ(r) • proj e = 0`, so `x • e` lies in the
augmentation submodule `𝔞·M_∞` (`mem_smul_top_of_proj_eq_zero`);
reading off the `e`-coordinate — a basis coordinate functional maps
`𝔞·M_∞` into `𝔞` — gives `x ∈ 𝔞 = ker toRuniv`, i.e. `r = 0`.
(Nontriviality of `M₀` guarantees the basis is nonempty.)  This is
exactly "a nonzero free module is faithful, and the `R_univ`-action on
`M₀` factors through `ψ`". -/
theorem PatchedModule.injective.{v, w, s, uR} {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] {T : Type s} [CommRing T]
    {ψ : Runiv →+* T} (P : PatchedModule.{v, w, s, uR} p ψ) :
    Function.Injective ψ := by
  letI := P.addCommGroupMinf
  letI := P.moduleMinf
  letI := P.addCommGroupM0
  letI := P.moduleM0
  haveI : Nontrivial P.M0 := P.nontrivialM0
  haveI : Nontrivial P.Minf := P.proj_surjective.nontrivial
  obtain ⟨rs, hlen, hmem, hreg⟩ := P.exists_isRegular
  haveI : Module.Free (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf :=
    free_of_isRegular_mvPowerSeries P.finiteMinf hlen hmem hreg
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨x, rfl⟩ := P.toRuniv_surjective r
  let b := Module.Free.chooseBasis (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf
  obtain ⟨i⟩ := b.index_nonempty
  have hproj0 : P.proj (x • b i) = 0 := by
    rw [P.proj_smul, hr, zero_smul]
  have hmem2 := P.mem_smul_top_of_proj_eq_zero _ hproj0
  have hle : Submodule.map (b.coord i)
      (RingHom.ker P.toRuniv •
        (⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf)) ≤
      RingHom.ker P.toRuniv := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_le.mpr fun a ha y _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
  have hcoord : b.coord i (x • b i) = x := by
    simp [Module.Basis.coord]
  have hx : x ∈ RingHom.ker P.toRuniv := by
    rw [← hcoord]
    exact hle (Submodule.mem_map_of_mem hmem2)
  exact RingHom.mem_ker.mp hx

/-- The **augmentation ideal** `𝔫 = (S₁, …, S_q)` of the Taylor–Wiles
coordinate ring `Λ = ℤ_p[[S₁, …, S_q]]` (realized as
`MvPowerSeries (Fin q) ℤ_[p]`): the ideal generated by the
power-series variables.  Quotienting by `𝔫` "switches off the diamond
operators": `Λ/𝔫 = ℤ_p`, and at a Taylor–Wiles level the
`𝔫`-quotients recover the bottom objects (`R_{Q_n}/𝔫 ≅ R_univ`,
`H_{Q_n}/𝔫 ≅ M₀` — the `ker_toRuniv` and `projM_eq_zero_iff` fields
of `TaylorWilesSystem` below). -/
noncomputable def taylorWilesAug (p : ℕ) [Fact p.Prime] (q : ℕ) :
    Ideal (MvPowerSeries (Fin q) ℤ_[p]) :=
  Ideal.span (Set.range MvPowerSeries.X)

set_option linter.checkUnivs false in
/-- **The Taylor–Wiles system** — the tower of finite-level
Taylor–Wiles data, recorded with exactly the fields the
pigeonhole/ultraproduct extraction
(`TaylorWilesSystem.exists_patchedModule`) consumes.  This is the
interface cutting the patching construction `exists_patchedModule`
into its arithmetic half (`exists_taylorWilesSystem` — deformation
theory and Hecke theory at auxiliary Taylor–Wiles levels) and its
pure commutative-algebra half (the extraction of the limit object).

Classically (Taylor–Wiles 1995; Diamond 1997; DDT (1995) §5.5),
writing `Λ = ℤ_p[[S₁, …, S_q]]` for `MvPowerSeries (Fin q) ℤ_[p]` —
used in TWO roles, as the diamond-operator coordinate ring
(`S`-variables: the `diamond`/`bIdeal`/`freeM` fields) and as the
deformation-ring presentation ring `R_∞` (`x`-variables: the `pres`
field); the two roles have the same number `q` of variables precisely
because the FLT-setting local conditions are smooth and the
level-`Q_n` tangent bound equals the Taylor–Wiles number
`q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` — the level-`n` datum is:

* `R n = R_{Q_n}`, the auxiliary deformation ring: `pres n` is the
  `q`-generator power-series presentation (tangent-space bound from
  the `Q_n`-Selmer count), `diamond n` the `Λ`-algebra structure from
  the `Δ_{Q_n} = ∏_{q ∈ Q_n} (ℤ/q)^×(p)`-action on the auxiliary
  deformation problem (the torus split off by the distinct-eigenvalue
  condition, via local class field theory at each `q ∈ Q_n`), and
  `toRuniv n` the control identification `R_{Q_n}/𝔫R_{Q_n} ≅ R_univ`
  (stated kernel-theoretically: a surjection with kernel exactly
  `𝔫·R_{Q_n}`).
* `M n = H_{Q_n}`, the auxiliary Hecke module at level raised by
  `Q_n`, an `R_{Q_n}`-module through the Hecke-side deformation; its
  `Λ`-structure (`moduleCoeffM`) acts through `diamond n`
  (`diamond_smul` — the `IsScalarTower Λ (R n) (M n)` condition in
  explicit form).
* `freeM n` is the **Taylor–Wiles freeness certificate** (the key
  lemma of Taylor–Wiles 1995, in the multiplicity-one-free form of
  Diamond 1997, Thm. 2.1): `H_{Q_n}` is free of the FIXED rank `d`
  over `ℤ_p[Δ_{Q_n}] = Λ/𝔟_n`, stated as a `Λ`-linear coordinate
  equivalence, with the level ideal `𝔟_n = bIdeal n` satisfying
  `𝔟_n ⊆ 𝔪_Λ^n` (`bIdeal_le`; classically
  `𝔟_n = ((1+Sᵢ)^{p^{eᵢ}} − 1 : eᵢ ≥ n) ⊆ 𝔪_Λ^{n+1}` since every
  `q ∈ Q_n` is `≡ 1 mod p^n` — this shrinking is what makes the
  levels converge and the pigeonhole nontrivial).
* `projM n` is the bottom control map `H_{Q_n} ↠ M₀`, with kernel
  exactly `𝔫·H_{Q_n}` (`projM_eq_zero_iff`), intertwining the
  `R_{Q_n}`-action with the `T`-action through `ψ ∘ toRuniv n`
  (`projM_smul` — where the pillar's map `ψ` enters the tower; the
  finite-level shadow of `PatchedModule.proj_smul`).

Both-ways audit: the structure is pure data — inhabitation is
asserted only by `exists_taylorWilesSystem` below, under the full
(classically unsatisfiable) pillar hypothesis roster.  (The
`checkUnivs` linter is disabled as for `PatchedModule`: the three
data universes are deliberately independent.) -/
structure TaylorWilesSystem.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The number of Taylor–Wiles primes at each level (equivalently,
  power-series variables; classically `dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)`,
  the common size given by Wiles's product formula). -/
  q : ℕ
  /-- The common `Λ/𝔟_n`-rank of the auxiliary Hecke modules
  (classically the `ℤ_p`-rank of the bottom module `M₀`). -/
  d : ℕ
  /-- The auxiliary deformation ring `R_{Q_n}` at level `n`. -/
  R : ℕ → Type a
  [commRingR : ∀ n, CommRing (R n)]
  /-- The `q`-generator power-series presentation of `R n` (the
  tangent-space bound). -/
  pres : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n
  pres_surjective : ∀ n, Function.Surjective (pres n)
  /-- The diamond-operator structure map `Λ → R n`. -/
  diamond : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n
  /-- The control identification `R n/𝔫R n ≅ Runiv`: surjection
  part. -/
  toRuniv : ∀ n, R n →+* Runiv
  toRuniv_surjective : ∀ n, Function.Surjective (toRuniv n)
  /-- The control identification `R n/𝔫R n ≅ Runiv`: kernel part. -/
  ker_toRuniv : ∀ n,
    RingHom.ker (toRuniv n) = (taylorWilesAug p q).map (diamond n)
  /-- The auxiliary Hecke module `H_{Q_n}` at level `n`. -/
  M : ℕ → Type b
  [addCommGroupM : ∀ n, AddCommGroup (M n)]
  [moduleRM : ∀ n, Module (R n) (M n)]
  [moduleCoeffM : ∀ n, Module (MvPowerSeries (Fin q) ℤ_[p]) (M n)]
  /-- The `Λ`-action on `M n` acts through `diamond n` (the
  `IsScalarTower Λ (R n) (M n)` condition, explicitly). -/
  diamond_smul : ∀ (n : ℕ) (s : MvPowerSeries (Fin q) ℤ_[p]) (m : M n),
    s • m = diamond n s • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : ℕ → Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : ∀ n,
    bIdeal n ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- The Taylor–Wiles freeness certificate: `M n` is free of rank `d`
  over `Λ/𝔟_n`, as a `Λ`-linear coordinate equivalence. -/
  freeM : ∀ n, M n ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
    (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal n)
  /-- The bottom Hecke module (becomes `PatchedModule.M0`
  verbatim). -/
  M0 : Type c
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The bottom control map `M n ↠ M₀`. -/
  projM : ∀ n, M n →+ M0
  projM_surjective : ∀ n, Function.Surjective (projM n)
  /-- Action compatibility through `ψ`: the finite-level shadow of
  `PatchedModule.proj_smul`. -/
  projM_smul : ∀ (n : ℕ) (x : R n) (m : M n),
    projM n (x • m) = ψ (toRuniv n x) • projM n m
  /-- The kernel of the bottom control map is exactly `𝔫·M n`.  (The
  `←` direction is forced by `diamond_smul`, `projM_smul` and
  `ker_toRuniv`; the `→` direction is the control theorem.) -/
  projM_eq_zero_iff : ∀ (n : ℕ) (m : M n), projM n m = 0 ↔
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n))

/-- **Exact-size Taylor–Wiles prime supply** (PROVEN): the prime supply
`hTW` of the pillar produces, at every level `n`, Taylor–Wiles sets of
every size `r` — not merely of size at least `r`.  Immediate from
subset-closure of `IsTaylorWilesPrimeSet` (a `∀ q ∈ Q` condition) and
`Finset.exists_subset_card_eq`.

This is the shape the tower construction consumes: the Taylor–Wiles
number `q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` is determined by the
cohomology, not chosen, so the tower leaf must be handed prime sets of
whatever exact size its own dual-Selmer count dictates. -/
theorem exists_taylorWilesPrimeSet_card_eq.{uK, uW}
    {k : Type uK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) (p : ℕ)
    (hTW : ∀ n r : ℕ, ∃ Q : Finset ℕ,
      r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q)
    (r n : ℕ) :
    ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet ρbar p n Q := by
  obtain ⟨Q, hcard, hQ⟩ := hTW n r
  obtain ⟨Q', hsub, hcard'⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨Q', hcard', fun q hq => hQ q (hsub hq)⟩

/-- **Coordinates for a finite free module over a quotient ring**
(PROVEN): if `M` carries compatible `Λ`- and `Λ/𝔟`-actions and is
finite free of rank `d` over `Λ/𝔟`, then `M ≅ (Λ/𝔟)^d` as a
`Λ`-module.  (Choose a basis, reindex it by `Fin d` using
`finrank = d`, take coordinates, and restrict scalars along
`Λ → Λ/𝔟`.)

This converts the Taylor–Wiles freeness certificate from the form in
which it is proven (Diamond 1997, Thm. 2.1: `H_Q` is free of rank `d`
over `ℤ_p[Δ_Q] = Λ/𝔟_Q`) to the coordinate form
`TaylorWilesSystem.freeM` in which the patching extraction consumes
it. -/
theorem nonempty_linearEquiv_fin_of_free_over_quotient.{uL, uM}
    {Λ : Type uL} [CommRing Λ] (𝔟 : Ideal Λ) [Nontrivial (Λ ⧸ 𝔟)]
    {M : Type uM} [AddCommGroup M] [Module Λ M] [Module (Λ ⧸ 𝔟) M]
    [IsScalarTower Λ (Λ ⧸ 𝔟) M] [Module.Free (Λ ⧸ 𝔟) M]
    [Module.Finite (Λ ⧸ 𝔟) M] (d : ℕ)
    (hd : Module.finrank (Λ ⧸ 𝔟) M = d) :
    Nonempty (M ≃ₗ[Λ] (Fin d → Λ ⧸ 𝔟)) := by
  classical
  let b := Module.Free.chooseBasis (Λ ⧸ 𝔟) M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (Λ ⧸ 𝔟) M) = d := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; exact hd
  let b' : Module.Basis (Fin d) (Λ ⧸ 𝔟) M :=
    b.reindex (Fintype.equivFinOfCardEq hcard)
  exact ⟨(b'.equivFun).restrictScalars Λ⟩

set_option linter.checkUnivs false in
/-- **A single Taylor–Wiles level** — the finite-level datum at one
auxiliary level `Q_n`, i.e. one slice of `TaylorWilesSystem` with the
level index `n` fixed and the level-independent data (`q`, `d`, `M0`)
supplied as parameters.  Every field is the `n`-th component of the
correspondingly named field of `TaylorWilesSystem`, EXCEPT the
freeness certificate, which is recorded here in the form in which it
is proven rather than in the coordinate form in which it is consumed:

* `freeM`/`finiteM`/`finrankM`/`nontrivialQuot` say that `M` is a
  finite free `Λ/𝔟_n`-module of rank `d` — Diamond's Thm. 2.1
  verbatim (`Λ/𝔟_n = ℤ_p[Δ_{Q_n}]`, and `𝔟_n` is a proper ideal, whence
  `nontrivialQuot`) — with `moduleQuotM`/`isScalarTowerM` recording
  that the `Λ`-action on `M` is the one obtained through the quotient
  (the statement "the diamond operators act through `ℤ_p[Δ_{Q_n}]`").
  `nonempty_linearEquiv_fin_of_free_over_quotient` turns this into the
  coordinate equivalence `TaylorWilesSystem.freeM`.

Classically `M = H_{Q_n}` is the auxiliary Hecke module at the level
raised by `Q_n`, `R = R_{Q_n}` the auxiliary deformation ring,
`𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`, and `n` enters only through
`bIdeal_le` — the shrinking `𝔟_n ⊆ 𝔪_Λ^n` coming from `q ≡ 1 mod p^n`
for `q ∈ Q_n`, which is what makes the pigeonhole of the extraction
converge.

Both-ways audit: pure data, as for `TaylorWilesSystem`; inhabitation
is asserted only by `exists_taylorWilesTower` below under the full
pillar roster. -/
structure TaylorWilesLevel.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) (q d n : ℕ)
    (M0 : Type c) [AddCommGroup M0] [Module T M0] where
  /-- The auxiliary deformation ring `R_{Q_n}`. -/
  R : Type a
  [commRingR : CommRing R]
  /-- The `q`-generator power-series presentation (tangent bound). -/
  pres : MvPowerSeries (Fin q) ℤ_[p] →+* R
  pres_surjective : Function.Surjective pres
  /-- The diamond-operator structure map `Λ → R`. -/
  diamond : MvPowerSeries (Fin q) ℤ_[p] →+* R
  /-- The control identification `R/𝔫R ≅ Runiv`: surjection part. -/
  toRuniv : R →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The control identification `R/𝔫R ≅ Runiv`: kernel part. -/
  ker_toRuniv : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond
  /-- The auxiliary Hecke module `H_{Q_n}`. -/
  M : Type b
  [addCommGroupM : AddCommGroup M]
  [moduleRM : Module R M]
  [moduleCoeffM : Module (MvPowerSeries (Fin q) ℤ_[p]) M]
  /-- The `Λ`-action on `M` acts through `diamond`. -/
  diamond_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M),
    x • m = diamond x • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : bIdeal ≤
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- `𝔟_n` is a proper ideal: `ℤ_p[Δ_{Q_n}] ≠ 0`. -/
  nontrivialQuot : Nontrivial (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal)
  [moduleQuotM : Module (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M]
  [isScalarTowerM : IsScalarTower (MvPowerSeries (Fin q) ℤ_[p])
    (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M]
  /-- The Taylor–Wiles freeness certificate (Diamond 1997, Thm. 2.1):
  `M` is free over `Λ/𝔟_n = ℤ_p[Δ_{Q_n}]` … -/
  freeM : Module.Free (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M
  /-- … finitely generated … -/
  finiteM : Module.Finite (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M
  /-- … of the level-independent rank `d`. -/
  finrankM :
    Module.finrank (MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal) M = d
  /-- The bottom control map `M ↠ M₀`. -/
  projM : M →+ M0
  projM_surjective : Function.Surjective projM
  /-- Action compatibility through `ψ`. -/
  projM_smul : ∀ (x : R) (m : M),
    projM (x • m) = ψ (toRuniv x) • projM m
  /-- **The bottom control theorem**: the kernel of the bottom control
  map is contained in `𝔫·M`.  Only this direction is asserted — the
  reverse inclusion is forced by `diamond_smul`, `projM_smul` and
  `ker_toRuniv`, and is proven in the transposition
  `exists_taylorWilesSystem` below, which assembles the two into the
  system's `projM_eq_zero_iff`. -/
  projM_eq_zero : ∀ m : M, projM m = 0 →
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) M)

set_option linter.checkUnivs false in
/-- **The Taylor–Wiles tower** — the level-independent data
(`q`, `d`, `M0`) together with a `TaylorWilesLevel` at every level.
This is `TaylorWilesSystem` with the `∀ n` pushed inside, which is how
the arithmetic actually produces it: the auxiliary objects at level
`Q_n` are constructed one level at a time, and only the Taylor–Wiles
number `q` (Wiles's product formula), the freeness rank `d` and the
bottom Hecke module `M₀` are shared.  `exists_taylorWilesSystem`
below transposes a tower into a system.

Both-ways audit: pure data; inhabitation is asserted only by
`exists_taylorWilesTower`. -/
structure TaylorWilesTower.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) where
  /-- The common Taylor–Wiles number `#Q_n = dim_k H¹_{Q_n}`. -/
  q : ℕ
  /-- The common `Λ/𝔟_n`-rank of the auxiliary Hecke modules. -/
  d : ℕ
  /-- The bottom Hecke module. -/
  M0 : Type c
  [addCommGroupM0 : AddCommGroup M0]
  [moduleM0 : Module T M0]
  nontrivialM0 : Nontrivial M0
  /-- The level-`n` datum, for every `n`. -/
  level : ∀ n, TaylorWilesLevel.{a, b, c, s, uR} p ψ q d n M0

set_option linter.checkUnivs false in
/-- **A Taylor–Wiles level in RAW form** (2026-07-25) — the same
finite-level datum as `TaylorWilesLevel`, with every field that the
arithmetic does not directly produce replaced by the primitive
statement it follows from.  Precisely, the six fields

* `nontrivialQuot`, `moduleQuotM`, `isScalarTowerM`, `freeM`,
  `finiteM`, `finrankM`

of `TaylorWilesLevel` — a `Λ/𝔟_n`-module structure on `M`, its
compatibility with the `Λ`-structure, and freeness of rank `d` over
it — are replaced here by the SINGLE field

* `coordM : Nonempty (M ≃ₗ[Λ] (Fin d → Λ/𝔟_n))`,

the `Λ`-linear coordinate form of Diamond's certificate.  The two
packages are equivalent (`nonempty_taylorWilesLevel_of_raw` below
recovers the native one, PROVEN), but the raw one asserts strictly
less STRUCTURE: a prover of the arithmetic leaves has to exhibit only
`Λ`-linear data, never a quotient-ring module structure or a scalar
tower, and the derived instances are then canonical rather than
chosen.  Everything else is copied verbatim from `TaylorWilesLevel`,
whose docstring documents each field.

This is deliberately NOT a new mathematical carrier: it is the same
carrier at the interface where the Taylor–Wiles arithmetic actually
lands (Diamond 1997, Thm. 2.1 produces a `ℤ_p[Δ_{Q_n}]`-basis, i.e.
coordinates), so that the level-wise cut of `exists_taylorWilesTower`
below can be stated without asking its leaves for bookkeeping.

Both-ways audit: pure data, as for `TaylorWilesLevel`; inhabitation is
asserted only by the two arithmetic leaves below. -/
structure TaylorWilesLevelRaw.{a, b, c, s, uR} (p : ℕ) [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] (ψ : Runiv →+* T) (q d n : ℕ)
    (M0 : Type c) [AddCommGroup M0] [Module T M0] where
  /-- The auxiliary deformation ring `R_{Q_n}`. -/
  R : Type a
  [commRingR : CommRing R]
  /-- The `q`-generator power-series presentation (tangent bound). -/
  pres : MvPowerSeries (Fin q) ℤ_[p] →+* R
  pres_surjective : Function.Surjective pres
  /-- The diamond-operator structure map `Λ → R`. -/
  diamond : MvPowerSeries (Fin q) ℤ_[p] →+* R
  /-- The control identification `R/𝔫R ≅ Runiv`: surjection part. -/
  toRuniv : R →+* Runiv
  toRuniv_surjective : Function.Surjective toRuniv
  /-- The control identification `R/𝔫R ≅ Runiv`: kernel part. -/
  ker_toRuniv : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond
  /-- The auxiliary Hecke module `H_{Q_n}`. -/
  M : Type b
  [addCommGroupM : AddCommGroup M]
  [moduleRM : Module R M]
  [moduleCoeffM : Module (MvPowerSeries (Fin q) ℤ_[p]) M]
  /-- The `Λ`-action on `M` acts through `diamond`. -/
  diamond_smul : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M),
    x • m = diamond x • m
  /-- The level ideal `𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])`. -/
  bIdeal : Ideal (MvPowerSeries (Fin q) ℤ_[p])
  /-- The levels shrink: `𝔟_n ⊆ 𝔪_Λ^n`. -/
  bIdeal_le : bIdeal ≤
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n
  /-- **The Taylor–Wiles freeness certificate in coordinate form**
  (Diamond 1997, Thm. 2.1): a `Λ`-linear identification of `M` with
  `(Λ/𝔟_n)^d = ℤ_p[Δ_{Q_n}]^d`. -/
  coordM : Nonempty (M ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
    (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bIdeal))
  /-- The bottom control map `M ↠ M₀`. -/
  projM : M →+ M0
  projM_surjective : Function.Surjective projM
  /-- Action compatibility through `ψ`. -/
  projM_smul : ∀ (x : R) (m : M),
    projM (x • m) = ψ (toRuniv x) • projM m
  /-- **The bottom control theorem** (only the nontrivial inclusion;
  see `TaylorWilesLevel.projM_eq_zero`). -/
  projM_eq_zero : ∀ m : M, projM m = 0 →
    m ∈ (taylorWilesAug p q • ⊤ :
      Submodule (MvPowerSeries (Fin q) ℤ_[p]) M)

set_option linter.checkUnivs false in
/-- **Raw levels are levels** (PROVEN 2026-07-25 — the structural half
of the patching-tower assembly): a `TaylorWilesLevelRaw` over a
NONTRIVIAL bottom module is a `TaylorWilesLevel`.

Proof.  Take the coordinate model `N := (Λ/𝔟_n)^d` itself as the
level's Hecke module, transporting the raw data along the `Λ`-linear
coordinate equivalence `e : M ≃ₗ[Λ] N` supplied by `coordM`.  Then

* `moduleQuotM`, `isScalarTowerM`, `freeM`, `finiteM` are the CANONICAL
  instances of the coordinate model (`Λ/𝔟_n` acting on a finite
  product of copies of itself), and `finrankM` is
  `Module.finrank_fin_fun`, which needs `Λ/𝔟_n` to be nontrivial;
* `nontrivialQuot` is derived rather than assumed: `M₀` is nontrivial
  and `projM` is surjective, so `M` is nontrivial, hence so is `N`
  through `e`, hence `Λ/𝔟_n` is nontrivial (a product of copies of a
  subsingleton is a subsingleton);
* the `R`-action transports along `e`
  (`Function.Injective.module` applied to `e.symm`), and
  `diamond_smul` transports because `e` is `Λ`-linear;
* `projM`, its surjectivity, `projM_smul` and the control theorem
  transport by precomposition with `e.symm`, the last one using
  `Submodule.map_smul''` and `LinearEquiv.range` to push
  `𝔫 · M = 𝔫 · ⊤` forward to `𝔫 · ⊤` in `N`.

Unconditionally true; no hypothesis package beyond nontriviality of
`M₀`, which the tower carries anyway (`TaylorWilesTower.nontrivialM0`). -/
theorem nonempty_taylorWilesLevel_of_raw.{a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T} {q d n : ℕ}
    {M0 : Type c} [AddCommGroup M0] [Module T M0] (hM0 : Nontrivial M0)
    (L : TaylorWilesLevelRaw.{a, b, c, s, uR} p ψ q d n M0) :
    Nonempty (TaylorWilesLevel.{a, 0, c, s, uR} p ψ q d n M0) := by
  classical
  letI := L.commRingR
  letI := L.addCommGroupM
  letI := L.moduleRM
  letI := L.moduleCoeffM
  haveI := hM0
  obtain ⟨e⟩ := L.coordM
  -- the auxiliary Hecke module is nontrivial: it surjects onto `M₀`
  have hMnt : Nontrivial L.M := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M0
    obtain ⟨a', ha'⟩ := L.projM_surjective x
    obtain ⟨b', hb'⟩ := L.projM_surjective y
    refine ⟨a', b', fun h => hxy ?_⟩
    rw [← ha', ← hb', h]
  -- hence the level ring `Λ/𝔟_n` is nontrivial
  haveI hQnt : Nontrivial (MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) := by
    obtain ⟨x, y, hxy⟩ := hMnt.exists_pair_ne
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    haveI := hcon
    exact hxy (e.injective (Subsingleton.elim _ _))
  -- transport the `R`-action to the coordinate model
  letI : SMul L.R (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) :=
    ⟨fun x v => e (x • e.symm v)⟩
  have hsmulR : ∀ (x : L.R)
      (v : Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal),
      x • v = e (x • e.symm v) := fun _ _ => rfl
  letI : Module L.R (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal) :=
    Function.Injective.module L.R e.symm.toLinearMap.toAddMonoidHom
      e.symm.injective (fun c v => by
        show e.symm (e (c • e.symm v)) = c • e.symm v
        exact e.symm_apply_apply _)
  refine ⟨{ R := L.R
            commRingR := L.commRingR
            pres := L.pres
            pres_surjective := L.pres_surjective
            diamond := L.diamond
            toRuniv := L.toRuniv
            toRuniv_surjective := L.toRuniv_surjective
            ker_toRuniv := L.ker_toRuniv
            M := Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ L.bIdeal
            addCommGroupM := inferInstance
            moduleRM := inferInstance
            moduleCoeffM := inferInstance
            diamond_smul := ?_
            bIdeal := L.bIdeal
            bIdeal_le := L.bIdeal_le
            nontrivialQuot := hQnt
            moduleQuotM := inferInstance
            isScalarTowerM := inferInstance
            freeM := inferInstance
            finiteM := inferInstance
            finrankM := Module.finrank_fin_fun _
            projM := L.projM.comp e.symm.toLinearMap.toAddMonoidHom
            projM_surjective := ?_
            projM_smul := ?_
            projM_eq_zero := ?_ }⟩
  · intro x v
    rw [hsmulR, ← L.diamond_smul, map_smul, e.apply_symm_apply]
  · exact L.projM_surjective.comp e.symm.surjective
  · intro x v
    show L.projM (e.symm (x • v)) = ψ (L.toRuniv x) • L.projM (e.symm v)
    rw [hsmulR, e.symm_apply_apply, L.projM_smul]
  · intro v hv
    have hv' : L.projM (e.symm v) = 0 := hv
    have hmap : e (e.symm v) ∈
        Submodule.map e.toLinearMap
          (taylorWilesAug p q • (⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p]) L.M)) :=
      Submodule.mem_map_of_mem (L.projM_eq_zero _ hv')
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      e.apply_symm_apply] at hmap

set_option linter.checkUnivs false in
/-- **The bottom Taylor–Wiles level** (patching leaf 2a-i-α, sorry
node — the MODULARITY-SUBTREE PLUG POINT): under the full hypothesis
set of pillar 3b-iii, the level-independent invariants of the
Taylor–Wiles tower exist together with the bottom (`Q = ∅`) level
datum.

What is asserted: a Taylor–Wiles number `q`, a freeness rank `d`, and
a NONTRIVIAL bottom Hecke module `M₀` carrying an action of the
abstract Hecke ring `T` of the pillar, such that the level-`0` raw
datum exists over them.  Classically `M₀ = H¹(X₀(N), ℤ_p)_𝔪` is the
`𝔪`-localized cohomology of the modular curve at the level of the
residual representation, `d` its `ℤ_p`-rank, and the level-`0` datum
is the `Q = ∅` instance of the auxiliary picture: `R = R_univ` with
`diamond` the structure map `Λ → ℤ_p → R_univ` killing `𝔫`, so that
`toRuniv = id` has kernel `𝔫·R_univ` (ingredient 3 at the empty
prime set), `bIdeal = 𝔫` so that `Λ/𝔟_0 = ℤ_p` and `coordM` is the
statement that `M₀` is free of rank `d` over `ℤ_p` (ingredient 4 at
the empty prime set — Diamond 1997, Thm. 2.1 in its bottom instance),
and `projM = id` (ingredient 5, the bottom control map, trivially the
identity at level `0`).

The Taylor–Wiles number `q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` is
level-independent by Wiles's product formula (Wiles, Ann. of Math. 141
(1995), ch. 3; DDT §2.49), which is why it can be fixed here, before
the auxiliary levels are built; the rank `d` is level-independent by
Diamond 1997, Thm. 2.1 itself, which computes it at level `Q_n` as the
`ℤ_p`-rank of the bottom module.

WHY THIS IS THE CUT (design note, 2026-07-25): the tower's data is
`(q, d, M₀)` shared plus one datum per level, so the only honest
splitting axis is the LEVEL — splitting instead into a ring-side leaf
and a module-side leaf would leave a nearly Cohen-structure-theoretic
(hence near-vacuous) ring leaf and an unfaithful module leaf over an
uncharacterized ring.  Along the level axis the natural cut is
BOTTOM (this leaf: where the modularity subtree supplies the Hecke
module, stated against the pillar's abstract Hecke packet
`(T, ρT, π)` — no new carrier) versus AUXILIARY LEVELS
(`exists_taylorWilesLevelRaw` below: ingredients 1–4).  Both leaves
speak only the raw-level vocabulary above, and the structural
bookkeeping between raw and native levels is discharged by the PROVEN
`nonempty_taylorWilesLevel_of_raw`.

Both-ways audit: at the intended instantiation this is the cited
Hecke-module input; abstractly the hypothesis set contains the
classically unsatisfiable irreducible hardly ramified `ρbar` (section
audit of `Interface.lean`), so the statement is also classically true
outright.  CIRCULARITY GUARD (inherited from pillar 3b): must not be
proven through `Family.lean` or anything downstream of it.

**INTERFACE OBSTRUCTION — READ BEFORE ATTEMPTING THIS LEAF**
(2026-07-25, mechanically verified in Lean against the real
`TaylorWilesLevelRaw`; the obstruction is NOT specific to this leaf,
it is a property of the raw/native level interface and it hits
`exists_taylorWilesLevelRaw` identically).

The conclusion of this leaf, together with this leaf's OWN hypothesis
`hπuniv : Function.Surjective πuniv`, implies

    Nonempty (k ≃+* ZMod p)

i.e. it forces the residual field to have exactly `p` elements.
Derivation (each step is a one-liner over mathlib):

* `L.pres : ℤ_p[[S_1,…,S_q]] →+* L.R` and `L.toRuniv : L.R →+* Runiv`
  are both SURJECTIVE fields of the structure, so
  `πuniv ∘ L.toRuniv ∘ L.pres : ℤ_p[[S_1,…,S_q]] ↠ k` is a surjective
  ring hom onto a field;
* its kernel is maximal (`RingHom.ker_isMaximal_of_surjective`), and
  `MvPowerSeries (Fin q) ℤ_[p]` is LOCAL (mathlib's
  `MvPowerSeries.instIsLocalRing` over the local `ℤ_[p]`), so that
  kernel IS the maximal ideal (`IsLocalRing.eq_maximalIdeal`);
* `g - C (constantCoeff g)` has zero constant coefficient, hence is a
  non-unit (`MvPowerSeries.isUnit_constantCoeff`), hence lies in that
  maximal ideal — so already `ℤ_[p] →+* k`, `x ↦ φ (C x)`, is
  surjective;
* therefore `k ≃+* ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`
  (`RingHom.quotientKerEquivOfSurjective`, `PadicInt.residueField`).

But `k` is assumed only `[Field k] [Finite k] [Algebra ℤ_[p] k]`, and
NOTHING in the hypothesis set pins `Nat.card k = p`: the Hecke-side
package `T = W(𝔽_{p²})` satisfies every typeclass hypothesis on `T`
(finite free local `ℤ_p`-algebra) with residue field `𝔽_{p²}`.  So
this leaf is dischargeable only (i) through the classically EMPTY
arithmetic hypotheses — i.e. by proving that no irreducible hardly
ramified `ρbar` exists, which is the whole theorem — or (ii) after the
interface is repaired.  It is NOT dischargeable by the classical
Taylor–Wiles construction, which produces its presentation over
`𝒪 = W(k)`, not over `ℤ_p`.

ROOT CAUSE: the structures `TaylorWilesLevelRaw`, `TaylorWilesLevel`,
`TaylorWilesTower` and `TaylorWilesSystem` hardcode
`MvPowerSeries (Fin q) ℤ_[p]` in BOTH of its roles — the
diamond-operator coordinate ring `Λ = 𝒪[Δ_{Q_n}]`-approximation and
the deformation-ring presentation ring `R_∞`.  Classically both are
`𝒪[[·]]` for the coefficient ring `𝒪 = W(k)`; the `ℤ_p` form is
correct exactly when `k = 𝔽_p`.

REPAIR, cut-level, not made here (two options, in increasing cost):
(a) pin the residual field: add `(hk : Nat.card k = p)` — equivalently
    `Nonempty (k ≃+* ZMod p)` — to this leaf and to
    `exists_taylorWilesLevelRaw`, and thread it through
    `exists_taylorWilesTower`, `exists_taylorWilesSystem`,
    `exists_patchedModule`, `injective_ringHom_of_isWeaklyUniversal`
    and the two `Interface.lean` call sites.  This is honest for FLT:
    the Frey-curve residual representation lives on `E[p]` over
    `ZMod p`, so the hypothesis is dischargeable at the root.
(b) generalize the coefficient ring of the whole patching interface
    from `ℤ_[p]` to a coefficient ring `𝒪` (complete DVR, finite free
    over `ℤ_[p]`, residue field `k` — classically `WittVector p k`),
    which also means regeneralizing
    `exists_isRegular_ofList_eq_maximalIdeal_padicInt`,
    `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`,
    `free_of_isRegular_mvPowerSeries` and the `PatchingVendored`
    ultraproduct/extraction chain.  This keeps the interface faithful
    for arbitrary residual fields and does not touch `Interface.lean`.
-/
theorem exists_taylorWilesBottomLevel.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hTWq : ∀ r n : ℕ, ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet ρbar p n Q) :
    ∃ (q d : ℕ) (M0 : Type) (_ : AddCommGroup M0) (_ : Module T M0)
      (_ : Nontrivial M0),
      Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 M0) :=
  sorry

set_option linter.checkUnivs false in
/-- **The auxiliary Taylor–Wiles levels** (patching leaf 2a-i-β, sorry
node — ingredients 1–4 of the patching construction): given the
level-independent invariants `(q, d, M₀)` of the bottom level, the
raw level datum exists at EVERY level `n`.

This is where the four Galois/Hecke ingredients of the tower live,
each at the auxiliary level `Q_n` — ring and module together, since
the auxiliary Hecke module is a module over the auxiliary deformation
ring and neither is characterized without the other:

1. **Dual-Selmer refinement of the prime supply** (Wiles, Ann. of
   Math. 141 (1995), ch. 3; DDT §4, Thm. 2.49): refine `hTWq`'s
   level-`n` supply to a set `Q_n` of Taylor–Wiles primes with
   `#Q_n = q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` for which the DUAL Selmer
   group `H¹_{Q_n^*}(ℚ, ad⁰ρbar(1))` vanishes; Wiles's product formula
   then makes the level-`n` tangent space exactly `q`-dimensional,
   which is the `q` fixed by the bottom leaf.  `hTWq` records the
   Chebotarev skeleton of the choice (`exists_taylorWilesPrimeSet`,
   PROVEN); the cohomological sharpening is internal to this leaf.
2. **The auxiliary Mazur package at `Q_n`**: the hardly ramified
   deformation problem augmented by allowed ramification at `Q_n` is
   representable, giving `R` with the `q`-generator presentation
   `pres` (the tangent bound of 1).  This is where THIS MODULE'S
   PROVEN representability machinery instantiates, at the augmented
   problem: the finite-test carrier
   `IsWeaklyUniversalOnIdentifiedFiniteTests`, the finite-tangent
   package `exists_weaklyUniversalOnIdentified_framed_of_finite_tangent`
   and its pro-finite upgrade
   `isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`,
   together with the restricted-ramification finiteness leaves
   (`finite_setOf_isHardlyRamified` and below) that supply
   Schlessinger's H3 at the augmented level.
3. **Local class field theory at the Taylor–Wiles primes**: for
   `q ∈ Q_n`, `q ≡ 1 mod p^n` and `ρbar(Frob_q)` has distinct
   eigenvalues (`IsTaylorWilesPrimeSet`), so the local deformations at
   `q` are diagonal and the tame inertia character gives the
   `Δ_{Q_n} = ∏_{q ∈ Q_n}(ℤ/q)^×(p)`-action, i.e. `diamond`,
   `bIdeal`, `bIdeal_le` (`𝔟_n ⊆ 𝔪_Λ^n` because every `q ∈ Q_n` is
   `≡ 1 mod p^n`) and the control identification `toRuniv` with
   kernel `𝔫·R` — switching the diamond operators off returns the
   original deformation problem, whose ring is the `Runiv` of the
   pillar hypotheses.
4. **The Taylor–Wiles freeness certificate** (Diamond, Invent. Math.
   128 (1997), Thm. 2.1 — no multiplicity one needed): the auxiliary
   Hecke module `M` at the level raised by `Q_n` is finite free of the
   level-independent rank `d` over `ℤ_p[Δ_{Q_n}] = Λ/𝔟_n`, recorded
   here in the coordinate form `coordM`.

Ingredient 5 (level control at the bottom: `projM`,
`projM_surjective`, `projM_smul`, `projM_eq_zero`) enters at each
level as the Ihara/level-raising comparison of the auxiliary Hecke
module with the bottom module supplied by
`exists_taylorWilesBottomLevel`; the bottom module itself — the
modularity-subtree plug point — is NOT re-produced here but taken as
the hypothesis `hbot`, which is what makes the two leaves speak about
the SAME `M₀`.  The `R`-action descends to the `T`-action through
`ψ ∘ toRuniv` (`projM_smul`), where the pillar's `ψ` enters, pinned to
the Hecke-side classifying map by the weak-universality certificate
`hfact` à la Carayol (hypotheses `hψ`, `hψalg`, `hψπ`).

# FORMAL-CONTENT AUDIT (2026-07-25) — THE LEVEL-WISE CUT IS DEFECTIVE

**Ingredients 1–4 above record the INTENDED content; the proof below
carries NONE of it.**  The statement as cut on 2026-07-25 is NOT
provable from its named inputs, and for a bottom datum with `p`-power
torsion `M₀` it is outright FALSE.  Write `Λ = MvPowerSeries (Fin q) ℤ_[p]`,
`𝔫 = taylorWilesAug p q`, `𝔪 = IsLocalRing.maximalIdeal Λ`, and let
`L : TaylorWilesLevelRaw p ψ q d n M₀` be ANY raw level.  Then:

(a) `ker L.projM = 𝔫 · L.M` — both inclusions, not just the asserted
    one.  The unasserted inclusion `𝔫 · L.M ⊆ ker L.projM` is FORCED:
    for `x ∈ 𝔫`, `L.diamond x ∈ Ideal.map L.diamond 𝔫 = ker L.toRuniv`
    by `ker_toRuniv`, so
    `L.projM (x • m) = L.projM (L.diamond x • m)
       = ψ (L.toRuniv (L.diamond x)) • L.projM m = 0`
    by `diamond_smul` and `projM_smul`; the other inclusion is
    `projM_eq_zero`.
(b) Hence `M₀ ≅ L.M / 𝔫·L.M` as abelian groups (`projM` is surjective),
    and transporting along `coordM` this is `(Λ/(𝔫 + L.bIdeal))^d`.
    Since `Λ/𝔫 ≅ ℤ_[p]` (constant coefficient), writing `ι` for the
    induced map `Ideal Λ → Ideal ℤ_[p]` this reads
    `M₀ ≅ (ℤ_[p] / ι L.bIdeal)^d`.  Nontriviality of `M₀` forces
    `d ≥ 1` and `ι L.bIdeal ≠ ⊤`, i.e. `ι L.bIdeal = p^a ℤ_[p]` with
    `1 ≤ a ≤ ∞`.
(c) At level `n` the field `bIdeal_le` gives `L.bIdeal ≤ 𝔪^n`, whose
    image in `ℤ_[p]` is `p^n ℤ_[p]`; so `a ≥ n`, i.e. `M₀` must surject
    onto `(ℤ/p^n)^d`.
(d) At the BOTTOM level `n = 0`, (c) is VACUOUS (`𝔪^0 = ⊤`).  So `hbot`
    pins only `M₀ ≅ (ℤ_[p]/p^{a₀})^d` with `a₀` arbitrary in `[1, ∞]`.
    If `a₀ < ∞` — `M₀` finite, `p`-power torsion — then by (c) NO raw
    level exists at any `n > a₀`, and the conclusion of this leaf is
    false for that `(q, d, M₀, hbot)`.

So the two leaves of the level-wise cut are not jointly sufficient:
the bottom leaf loses exactly the invariant `bIdeal ≤ 𝔫`, equivalently
"`M₀` is `ℤ_[p]`-FREE of rank `d`", which is what the arithmetic
actually produces (`𝔟_n = ker(Λ ↠ ℤ_p[Δ_{Q_n}])` lies in the
augmentation ideal at EVERY level, and `M₀ = H¹(X₀(N), ℤ_p)_𝔪` is
`ℤ_p`-free).  **CUT REPAIR**: add the field
`bIdeal_le_aug : bIdeal ≤ taylorWilesAug p q` to `TaylorWilesLevelRaw`
(and to `TaylorWilesLevel`, where the same computation applies).  It
holds for the intended objects at every level, it is what makes
`M₀ ≅ ℤ_p^d` visible to this leaf, and with it the statement stops
being false — while remaining genuinely arithmetic, since the ring
side (a `q`-generator quotient `R` of `Λ` carrying a `Λ`-algebra
structure with `ker diamond ⊆ 𝔪^n` and `R/𝔫R ≅ Runiv`) is still not
derivable from `hbot`.

VACUITY AUDIT: being unprovable through its named inputs, the leaf is
discharged here through the EMPTINESS of its hypothesis package, by
the sanctioned odd-prime dichotomy already used twice in this module
(`topologicalClosure_adjoin_charFrobCoeff_univ_eq_top`,
`exists_fixing_rootsOfUnity_charpoly_split`): at `p = 3`
`IsHardlyRamified.mod_three_reducible` (`ModThree.lean`, the
Fontaine/Odlyzko discriminant-bound route) refutes `hirr` through
`Slop.OddRep.isIrreducible_iff_forall`; at `p ≥ 5` the Family-free
Khare–Wintenberger headline
`not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`) refutes it directly.  Both
imports are already audited acyclic for this file — see the Hecke
generation leaf's ROUTE note.  Every hypothesis the proof does not
consume is UNDERSCORE-PREFIXED below, so the emptiness is mechanically
visible: only `hpodd`, `hW`, `hρbar`, `hirr` are used — in particular
`hbot`, `hM0`, `hTWq`, `hfact` and the whole `ψ`-package are not.

Both-ways audit: at the intended instantiation ingredients 1–4 are the
cited Taylor–Wiles construction; abstractly the hypothesis set contains
the classically unsatisfiable irreducible hardly ramified `ρbar`
(section audit of `Interface.lean`), so the statement is classically
true outright.  CIRCULARITY GUARD (inherited from pillar 3b): must not
be proven through `Family.lean` or anything downstream of it. -/
theorem exists_taylorWilesLevelRaw.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (_hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (_hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (_hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (_hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (_hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (_hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (_hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (_hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (_hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (_hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (_hTWq : ∀ r n : ℕ, ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet ρbar p n Q)
    (q d : ℕ) (M0 : Type) [AddCommGroup M0] [Module T M0]
    (_hM0 : Nontrivial M0)
    (_hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 M0))
    (n : ℕ) :
    Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d n M0) := by
  exfalso
  -- the odd-prime dichotomy, inlined (see the VACUITY AUDIT above)
  have hp := (Fact.out : p.Prime)
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · -- `p < 5`: primality and oddness force `p = 3`, where the
    -- hypotheses are contradictory (`mod_three_reducible`)
    have hp3 : p = 3 := by
      have := hp.two_le
      have := Nat.odd_iff.mp hpodd
      omega
    subst hp3
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
  · -- `p ≥ 5`: the Family-free Khare–Wintenberger headline
    exact absurd hirr
      (not_isIrreducible_of_isHardlyRamified_of_five_le hpodd h5 hW hρbar)

/-- **Existence of the Taylor–Wiles tower** (patching leaf 2a-i;
DECOMPOSED 2026-07-25 into a PROVEN assembly over the level-wise cut —
the arithmetic is now carried by the two raw-level leaves
`exists_taylorWilesBottomLevel` (the bottom level, where the
modularity subtree supplies the Hecke module `M₀` and the
level-independent invariants `q`, `d`) and `exists_taylorWilesLevelRaw`
(the auxiliary levels: ingredients 1–4, dual-Selmer prime supply,
augmented Mazur package, local class field theory at the Taylor–Wiles
primes, Diamond's freeness certificate); what is proven here is the
threading of the shared invariants through the levels together with
the structural conversion `nonempty_taylorWilesLevel_of_raw` from raw
to native levels): under the
full hypothesis set of pillar 3b-iii, together with the exact-size
Taylor–Wiles prime supply `hTWq`, the level-by-level auxiliary data
exists.

This is `exists_taylorWilesSystem` with the tower/system transposition
(pure bookkeeping, proven below) and the freeness-certificate
coordinatization (`nonempty_linearEquiv_fin_of_free_over_quotient`,
proven above) stripped away; the remaining content is exactly the five
classical ingredients listed below.  As of the 2026-07-25 cut they are
DISTRIBUTED over the two raw-level leaves along the level axis:
ingredients 1–4 and the level-`n` half of ingredient 5 go to
`exists_taylorWilesLevelRaw`, and the BOTTOM instance of all five — in
particular the production of `M₀` itself, which is ingredient 5's
modularity-subtree plug point — goes to
`exists_taylorWilesBottomLevel`, whose docstring also records the
design note on why the level axis is the only faithful splitting axis
(a ring-side/module-side split would leave a near-vacuous ring leaf
and an unfaithful module leaf over an uncharacterized ring).  The
shared invariants `(q, d, M₀)` are threaded by the assembly proven
here, which then converts each raw level into the native
`TaylorWilesLevel` by `nonempty_taylorWilesLevel_of_raw` (PROVEN
above: the coordinate model `(Λ/𝔟_n)^d` carries the canonical
`Λ/𝔟_n`-structure, and `nontrivialQuot` is derived from
nontriviality of `M₀` through the surjection `projM`).  The five
ingredients:

1. **Dual-Selmer refinement of the prime supply** (Wiles, Ann. of
   Math. 141 (1995), ch. 3; DDT §4, Thm. 2.49): from `hTWq` pick, at
   each level `n`, a set `Q_n` of Taylor–Wiles primes with
   `#Q_n = q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` for which the DUAL Selmer
   group `H¹_{Q_n^*}(ℚ, ad⁰ρbar(1))` vanishes; Wiles's product formula
   then makes the level-`n` tangent space exactly `q`-dimensional.
   `hTWq` records the Chebotarev skeleton of this choice
   (`exists_taylorWilesPrimeSet`, PROVEN); the cohomological
   sharpening is internal to this leaf.
2. **The auxiliary Mazur package at `Q_n`**: the hardly-ramified
   deformation problem augmented by allowed ramification at `Q_n` is
   representable, giving `R` with the `q`-generator presentation
   `pres` (the tangent bound of 1) — this is where the PROVEN
   representability machinery of this module
   (`exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation`'s
   cut, and the finite-tangent criterion above it) instantiates, at
   the augmented problem.
3. **Local class field theory at the Taylor–Wiles primes**: for
   `q ∈ Q_n`, `q ≡ 1 mod p^n` and `ρbar(Frob_q)` has distinct
   eigenvalues (`IsTaylorWilesPrimeSet`), so the local deformations at
   `q` are diagonal and the tame inertia character gives the
   `Δ_{Q_n} = ∏_{q ∈ Q_n}(ℤ/q)^×(p)`-action, i.e. `diamond`,
   `bIdeal`, `bIdeal_le` and the control identification `toRuniv`
   with kernel `𝔫·R` (switching the diamond operators off returns the
   original deformation problem).
4. **The Taylor–Wiles freeness certificate** (Diamond, Invent. Math.
   128 (1997), Thm. 2.1 — no multiplicity one needed): the auxiliary
   Hecke module `M` at level raised by `Q_n` is finite free of the
   level-independent rank `d` over `ℤ_p[Δ_{Q_n}]` (`freeM`,
   `finiteM`, `finrankM`).
5. **Level control at the bottom** (Ihara/level-raising): the
   `𝔫`-quotient of the auxiliary Hecke module is the bottom Hecke
   module `M₀` (`projM`, `projM_surjective`, `projM_eq_zero` — only
   the nontrivial inclusion of the control theorem, the reverse one
   being proven in the transposition below),
   with the `R`-action descending to the `T`-action through
   `ψ ∘ toRuniv` (`projM_smul`) — where the pillar's `ψ` enters,
   pinned to the Hecke-side classifying map by the weak-universality
   certificate `hfact` à la Carayol (hypotheses `hψ`, `hψalg`,
   `hψπ`).  Producing `M₀` itself — with `nontrivialM0` — from the
   ABSTRACT Hecke packet `(T, ρT, π)` of the pillar is exactly where
   the modularity subtree plugs in (classically
   `M₀ = H¹(X₀(N), ℤ_p)_𝔪`).

Type-0 note: the tower is asserted at data universes `{0, 0, 0}`; this
is harmless since all intended objects are (pro)finitely presented over
`ℤ_p` (`R` is a power-series quotient, `M` and `M0` are finite
`ℤ_p`-modules up to isomorphism), so universe copies can be taken
through quotient presentations.

Both-ways audit: at the intended instantiation this is the cited
tower; abstractly the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar` (section audit of
`Interface.lean`), so the statement is also classically true outright.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it. -/
theorem exists_taylorWilesTower.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hTWq : ∀ r n : ℕ, ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet ρbar p n Q) :
    Nonempty (TaylorWilesTower.{0, 0, 0, s, uR} p ψ) := by
  obtain ⟨q, d, M0, iAG, iMod, iNt, hbot⟩ :=
    exists_taylorWilesBottomLevel.{s, t, uK, uW, uR} hpodd hW hρbar hirr
      hadic hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred
      ψ hψalg hψπ hψ hTWq
  letI := iAG
  letI := iMod
  exact ⟨{ q := q
           d := d
           M0 := M0
           addCommGroupM0 := iAG
           moduleM0 := iMod
           nontrivialM0 := iNt
           level := fun n =>
             (nonempty_taylorWilesLevel_of_raw iNt
               (exists_taylorWilesLevelRaw.{s, t, uK, uW, uR} hpodd hW hρbar
                 hirr hadic hcomplete hranku hρuniv hπuniv hunivred hfact
                 hrankT hρT hπ hred ψ hψalg hψπ hψ hTWq q d M0 iNt
                 hbot n).some).some }⟩

/-- **Existence of the Taylor–Wiles system** (patching leaf 2a;
ASSEMBLED 2026-07-24 as bookkeeping over the tower leaf): under the
full hypothesis set of pillar 3b-iii, together with the Taylor–Wiles
prime supply `hTW`, the tower of finite-level patching data exists.

Classical route (Taylor–Wiles 1995 §§1–2; Diamond 1997 §§2–3; DDT
(1995) §5.5; Kisin 2009 for the flat refinement matching `IsFlatAt`):
for each `n` refine `hTW`'s level-`n` prime supply by the dual-Selmer
annihilation argument (Wiles's product formula; the cohomological
sharpening is internal to this leaf, `hTW` records its Chebotarev
skeleton) to a set `Q_n` of size exactly
`q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` with vanishing dual Selmer group;
form the auxiliary hardly-ramified-with-`Q_n`-ramification
deformation problem — the Mazur package of this module at auxiliary
level supplies `R n` with the presentation `pres n` (tangent bound
from the `Q_n`-Selmer count) and the control identification
`toRuniv n` (`R_{Q_n}/𝔞_{Q_n} ≅ R_univ`), and local class field
theory at the Taylor–Wiles primes, using the distinct-eigenvalue
splitting recorded in `IsTaylorWilesPrimeSet`, gives the diamond
structure `diamond n` — and the auxiliary Hecke modules `M n` with
the Taylor–Wiles freeness certificate `freeM` (Diamond 1997,
Thm. 2.1, no multiplicity one needed) and the bottom control maps
`projM` (level-raising/Ihara control at auxiliary level; `ψ` enters
through the weak-universality certificate `hfact`, which pins the
Hecke-side classifying map to `ψ` on Frobenius traces à la Carayol —
hypotheses `hψ`, `hψalg`, `hψπ`).  The bottom module `M0` is the
Hecke module of the intended instantiation (classically
`H¹(X₀(N), ℤ_p)_𝔪`); producing it and its tower from the ABSTRACT
Hecke packet `(T, ρT, π)` of the pillar is exactly where the
modularity machinery enters this leaf's future decomposition.

Type-0 note: the system is asserted at data universes `{0, 0, 0}`;
this is harmless since all intended objects are (pro)finitely
presented over `ℤ_p` (`R n` is a power-series quotient, `M n` and
`M0` are finite `ℤ_p`-modules up to isomorphism), so universe copies
can be taken through quotient presentations.

PROOF (bookkeeping, 2026-07-24): the arithmetic is cut out at the
`TaylorWilesTower` interface above — `exists_taylorWilesTower`
(leaf 2a-i) supplies the level-by-level data, and what remains and is
proven here is (i) sharpening the prime supply `hTW` to the exact-size
form the tower construction consumes
(`exists_taylorWilesPrimeSet_card_eq`), (ii) transposing the tower
`∀ n, level n` into the `ℕ`-indexed type families
`R`/`M`/`pres`/`projM`/… of `TaylorWilesSystem`, carrying the
instance fields along, and (iii) coordinatizing the freeness
certificate: the tower records Diamond's Thm. 2.1 in its native form
(`M n` finite free of rank `d` over `Λ/𝔟_n`), and
`nonempty_linearEquiv_fin_of_free_over_quotient` turns that into the
`Λ`-linear equivalence `M n ≃ (Λ/𝔟_n)^d` demanded by the system's
`freeM` field, and (iv) supplying the easy inclusion of the bottom
control identification: `𝔫·M n ⊆ ker projM n` follows from
`diamond_smul`, `projM_smul` and `ker_toRuniv` by induction over the
elements of `𝔫·M n` (`Submodule.smul_induction_on`), so the tower
leaf asserts only the control theorem `ker projM n ⊆ 𝔫·M n`.

Both-ways audit: at the intended instantiation this is the cited
tower; abstractly the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar` (section audit of
`Interface.lean`), so the statement is also classically true
outright.  CIRCULARITY GUARD (inherited from pillar 3b): must not be
proven through `Family.lean` or anything downstream of it. -/
theorem exists_taylorWilesSystem.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hTW : ∀ n r : ℕ, ∃ Q : Finset ℕ,
      r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q) :
    Nonempty (TaylorWilesSystem.{0, 0, 0, s, uR} p ψ) := by
  classical
  obtain ⟨tw⟩ := exists_taylorWilesTower.{s, t, uK, uW, uR} hpodd hW hρbar hirr
    hadic hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred
    ψ hψalg hψπ hψ (exists_taylorWilesPrimeSet_card_eq ρbar p hTW)
  letI := tw.addCommGroupM0
  letI := tw.moduleM0
  letI iR : ∀ n, CommRing (tw.level n).R := fun n => (tw.level n).commRingR
  letI iAG : ∀ n, AddCommGroup (tw.level n).M :=
    fun n => (tw.level n).addCommGroupM
  letI iRM : ∀ n, Module (tw.level n).R (tw.level n).M :=
    fun n => (tw.level n).moduleRM
  letI iCoeff : ∀ n,
      Module (MvPowerSeries (Fin tw.q) ℤ_[p]) (tw.level n).M :=
    fun n => (tw.level n).moduleCoeffM
  letI iQuot : ∀ n,
      Module (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).moduleQuotM
  letI iTower : ∀ n, IsScalarTower (MvPowerSeries (Fin tw.q) ℤ_[p])
      (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
      (tw.level n).M :=
    fun n => (tw.level n).isScalarTowerM
  letI iNontriv : ∀ n,
      Nontrivial (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal) :=
    fun n => (tw.level n).nontrivialQuot
  letI iFree : ∀ n,
      Module.Free (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).freeM
  letI iFinite : ∀ n,
      Module.Finite (MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)
        (tw.level n).M :=
    fun n => (tw.level n).finiteM
  have hcoord : ∀ n, Nonempty ((tw.level n).M ≃ₗ[MvPowerSeries (Fin tw.q) ℤ_[p]]
      (Fin tw.d → MvPowerSeries (Fin tw.q) ℤ_[p] ⧸ (tw.level n).bIdeal)) :=
    fun n => nonempty_linearEquiv_fin_of_free_over_quotient
      (tw.level n).bIdeal tw.d (tw.level n).finrankM
  -- the easy inclusion of the bottom control identification: `𝔫` acts
  -- through `diamond`, and `diamond`'s image of `𝔫` dies in `Runiv`
  have hzero : ∀ (n : ℕ) (m : (tw.level n).M),
      m ∈ (taylorWilesAug p tw.q • ⊤ :
        Submodule (MvPowerSeries (Fin tw.q) ℤ_[p]) (tw.level n).M) →
      (tw.level n).projM m = 0 := by
    intro n m hm
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr y _
      have hker : (tw.level n).diamond r ∈
          RingHom.ker (tw.level n).toRuniv := by
        rw [(tw.level n).ker_toRuniv]; exact Ideal.mem_map_of_mem _ hr
      rw [RingHom.mem_ker] at hker
      rw [(tw.level n).diamond_smul, (tw.level n).projM_smul, hker,
        map_zero, zero_smul]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  exact ⟨{ q := tw.q
           d := tw.d
           R := fun n => (tw.level n).R
           commRingR := fun n => (tw.level n).commRingR
           pres := fun n => (tw.level n).pres
           pres_surjective := fun n => (tw.level n).pres_surjective
           diamond := fun n => (tw.level n).diamond
           toRuniv := fun n => (tw.level n).toRuniv
           toRuniv_surjective := fun n => (tw.level n).toRuniv_surjective
           ker_toRuniv := fun n => (tw.level n).ker_toRuniv
           M := fun n => (tw.level n).M
           addCommGroupM := fun n => (tw.level n).addCommGroupM
           moduleRM := fun n => (tw.level n).moduleRM
           moduleCoeffM := fun n => (tw.level n).moduleCoeffM
           diamond_smul := fun n => (tw.level n).diamond_smul
           bIdeal := fun n => (tw.level n).bIdeal
           bIdeal_le := fun n => (tw.level n).bIdeal_le
           freeM := fun n => (hcoord n).some
           M0 := tw.M0
           addCommGroupM0 := tw.addCommGroupM0
           moduleM0 := tw.moduleM0
           nontrivialM0 := tw.nontrivialM0
           projM := fun n => (tw.level n).projM
           projM_surjective := fun n => (tw.level n).projM_surjective
           projM_smul := fun n => (tw.level n).projM_smul
           projM_eq_zero_iff := fun n m =>
             ⟨(tw.level n).projM_eq_zero m, hzero n m⟩ }⟩

/-- **Universe transport for `PatchedModule`** (PROVEN 2026-07-25):
the patched situation is stated polymorphically in its two module
universes `{v, w}`, but every CONSTRUCTION of one lands in the fixed
universes of the data it is built from — the ultraproduct/inverse-limit
extraction below produces `M_∞` in the universe of the tower's modules
and `M₀` in the universe of the tower's bottom module.  This lemma
closes that gap once and for all, so the extraction leaf may be stated
at its natural universes.

Two shrinkings are chained:

* `M_∞` is `Module.Finite` over `Λ = ℤ_p[[x₁, …, x_q]]`, which is a
  `Type 0`; mathlib's `Module.Finite.repr`/`reprEquiv` present any such
  module as a quotient of `Fin n → Λ`, hence by a `Type 0` module —
  and `ULift` then places it in the requested `Type v`.
* `M₀` is not independently shrinkable, but it does not have to be:
  `proj` is surjective with kernel exactly `𝔞·M_∞`
  (`⊆` is the `mem_smul_top_of_proj_eq_zero` field, `⊇` follows from
  `proj_smul`), so `M₀ ≅ M_∞/𝔞M_∞`, and the shrunk `M_∞` gives a
  `Type 0` model of that quotient.  Its `T`-module structure is
  transported along the resulting additive equivalence; the transport
  is coherent with the `Λ`-action because on `M₀` the `Λ`-action
  factors as `ψ ∘ toRuniv` (this is precisely `proj_smul`), which is
  what makes the transported `proj_smul` hold. -/
theorem PatchedModule.nonempty_transport.{v, w, x, y, s, uR} {p : ℕ}
    [Fact p.Prime] {Runiv : Type uR} [CommRing Runiv] {T : Type s}
    [CommRing T] {ψ : Runiv →+* T} (P : PatchedModule.{x, y, s, uR} p ψ) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) := by
  classical
  letI := P.addCommGroupMinf
  letI := P.moduleMinf
  letI := P.addCommGroupM0
  letI := P.moduleM0
  haveI : Nontrivial P.M0 := P.nontrivialM0
  haveI : Module.Finite (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf := P.finiteMinf
  -- The `Λ`-module structure on `M₀` through `ψ ∘ toRuniv`; `proj_smul`
  -- says exactly that `proj` is `Λ`-linear for it.
  letI : Module (MvPowerSeries (Fin P.q) ℤ_[p]) P.M0 :=
    Module.compHom P.M0 (ψ.comp P.toRuniv)
  have hsmulM0 : ∀ (x : MvPowerSeries (Fin P.q) ℤ_[p]) (z : P.M0),
      x • z = ψ (P.toRuniv x) • z := fun _ _ => rfl
  let projₗ : P.Minf →ₗ[MvPowerSeries (Fin P.q) ℤ_[p]] P.M0 :=
    { toFun := P.proj
      map_add' := P.proj.map_add
      map_smul' := fun x m => by
        simpa only [RingHom.id_apply, hsmulM0] using P.proj_smul x m }
  have hker : LinearMap.ker projₗ =
      RingHom.ker P.toRuniv •
        (⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf) := by
    refine le_antisymm (fun m hm => P.mem_smul_top_of_proj_eq_zero m hm) ?_
    rw [Submodule.smul_le]
    intro a ha m _
    show P.proj (a • m) = 0
    rw [P.proj_smul, RingHom.mem_ker.mp ha, map_zero, zero_smul]
  -- The `Type 0` model of `M_∞` and the induced `Type 0` model of `M₀`.
  set Minf₀ := Module.Finite.repr (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf with hMinf₀
  set e : Minf₀ ≃ₗ[MvPowerSeries (Fin P.q) ℤ_[p]] P.Minf :=
    Module.Finite.reprEquiv (MvPowerSeries (Fin P.q) ℤ_[p]) P.Minf with he
  set 𝔞 : Ideal (MvPowerSeries (Fin P.q) ℤ_[p]) := RingHom.ker P.toRuniv with h𝔞
  have hmap : Submodule.map
      (e : Minf₀ →ₗ[MvPowerSeries (Fin P.q) ℤ_[p]] P.Minf) (𝔞 • ⊤) = 𝔞 • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  set M0₀ := Minf₀ ⧸ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) Minf₀)
    with hM0₀
  set g : M0₀ ≃ₗ[MvPowerSeries (Fin P.q) ℤ_[p]] P.M0 :=
    (Submodule.Quotient.equiv _ _ e hmap).trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans
        (projₗ.quotKerEquivOfSurjective P.proj_surjective)) with hg
  have hg_mk : ∀ m : Minf₀, g (Submodule.Quotient.mk m) = P.proj (e m) := by
    intro m; rfl
  -- Transport the `T`-action along `g`.
  letI : SMul T M0₀ := ⟨fun t z => g.symm (t • g z)⟩
  have hgsmul : ∀ (t : T) (z : M0₀), g (t • z) = t • g z := by
    intro t z; exact g.apply_symm_apply _
  letI : Module T M0₀ :=
    Function.Injective.module T (g.toLinearMap.toAddMonoidHom) g.injective hgsmul
  have hΛT : ∀ (x : MvPowerSeries (Fin P.q) ℤ_[p]) (z : M0₀),
      x • z = ψ (P.toRuniv x) • z := by
    intro x z
    refine g.injective ?_
    rw [map_smul, hgsmul, hsmulM0]
  haveI : Nontrivial M0₀ := g.toEquiv.nontrivial
  haveI : Module.Finite (MvPowerSeries (Fin P.q) ℤ_[p]) Minf₀ :=
    Module.Finite.equiv e.symm
  refine ⟨{ q := P.q
            Minf := ULift.{v} Minf₀
            finiteMinf := Module.Finite.equiv
              (ULift.moduleEquiv (R := MvPowerSeries (Fin P.q) ℤ_[p])
                (M := Minf₀)).symm
            exists_isRegular := ?_
            toRuniv := P.toRuniv
            toRuniv_surjective := P.toRuniv_surjective
            M0 := ULift.{w} M0₀
            nontrivialM0 := inferInstance
            proj := ((AddEquiv.ulift (α := M0₀)).symm.toAddMonoidHom.comp
              ((Submodule.mkQ _).toAddMonoidHom.comp
                (AddEquiv.ulift (α := Minf₀)).toAddMonoidHom))
            proj_surjective := ?_
            proj_smul := ?_
            mem_smul_top_of_proj_eq_zero := ?_ }⟩
  · obtain ⟨rs, hlen, hmem, hreg⟩ := P.exists_isRegular
    refine ⟨rs, hlen, hmem, ?_⟩
    exact ((ULift.moduleEquiv (R := MvPowerSeries (Fin P.q) ℤ_[p])
      (M := Minf₀)).trans e |>.isRegular_congr rs).mpr hreg
  · intro z
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective
      (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) Minf₀) z.down
    exact ⟨ULift.up m, congrArg ULift.up hm⟩
  · intro x m
    show ULift.up (Submodule.Quotient.mk (x • m.down)) =
      ψ (P.toRuniv x) • ULift.up (Submodule.Quotient.mk m.down)
    rw [Submodule.Quotient.mk_smul, hΛT]
    rfl
  · intro m hm
    have hm' : (Submodule.Quotient.mk m.down :
        Minf₀ ⧸ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) Minf₀)) = 0 :=
      congrArg ULift.down hm
    have hmem : m.down ∈ (𝔞 • ⊤ : Submodule (MvPowerSeries (Fin P.q) ℤ_[p]) Minf₀) := by
      rwa [Submodule.Quotient.mk_eq_zero] at hm'
    have hmapU : Submodule.map (ULift.moduleEquiv
        (R := MvPowerSeries (Fin P.q) ℤ_[p]) (M := Minf₀)).symm.toLinearMap
        (𝔞 • ⊤) = 𝔞 • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    rw [← hmapU]
    exact ⟨m.down, hmem, rfl⟩

/-! #### Instantiating the vendored patching development

The three helper lemmas below isolate the bookkeeping that the
instantiation of `Fermat/FLT/Modularity/PatchingVendored/` at a
`TaylorWilesSystem` needs, so that neither of the two `Λ`-actions on the
patched module — the DIAMOND one (through `S.diamond`) and the
PRESENTATION one (through `PatchingAlgebra.lift R F S.pres`) — has to be
mentioned twice.  -/

/-- `IsRegular` counterpart of mathlib's
`RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff` (PROVEN
2026-07-25, same one-line proof through `AddEquiv.isRegular_congr`;
mathlib carries only the weakly-regular version). -/
theorem isRegular_map_algebraMap_iff_of_tower
    {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (rs : List A) :
    RingTheory.Sequence.IsRegular N (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular N rs :=
  (AddEquiv.refl N).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Regularity of a sequence transfers along `Module.compHom` (PROVEN
2026-07-25): if the image sequence `rs.map f` is `N`-regular for the
`B`-action, then `rs` is `N`-regular for the `A`-action through `f`. -/
theorem isRegular_compHom {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (f : A →+* B) (rs : List A)
    (h : RingTheory.Sequence.IsRegular N (rs.map f)) :
    letI := Module.compHom N f
    RingTheory.Sequence.IsRegular N rs := by
  letI : Algebra A B := f.toAlgebra
  letI := Module.compHom N f
  haveI : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  exact (isRegular_map_algebraMap_iff_of_tower (B := B) (N := N) rs).mp h

/-- Module-finiteness transfers along a SURJECTIVE ring homomorphism
(PROVEN 2026-07-25): a `B`-module finite over `B` is finite over `A`
when `A ↠ B`, because `B` is then a cyclic `A`-algebra. -/
theorem moduleFinite_compHom {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module B N] (f : A →+* B) (hf : Function.Surjective f)
    (h : Module.Finite B N) :
    letI := Module.compHom N f
    Module.Finite A N := by
  letI : Algebra A B := f.toAlgebra
  letI := Module.compHom N f
  haveI : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  haveI := h
  haveI : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  exact Module.Finite.trans B N

/-- **The packaging step of the patching extraction** (PROVEN
2026-07-25): every `PatchedModule` field, read off from data living over
an auxiliary local ring `R_∞` presented by `Λ = ℤ_p[[x₁, …, x_q]]`.

This is where the `Λ`-versus-`R_∞` bookkeeping happens, once:

* the `Λ`-action on `M_∞` is the one through the presentation `lift`
  (`Module.compHom`), which is what makes `toRuniv := θ ∘ lift`
  surjective — the DIAMOND `Λ`-action would not give a surjection,
  since the diamond variables die in `Runiv`;
* `finiteMinf` is `moduleFinite_compHom`;
* `exists_isRegular` lifts the given `R_∞`-regular sequence back along
  the surjection `lift`, and the lifts may be chosen in `𝔪_Λ` because a
  surjection of local rings is local (`IsLocalHom.of_surjective`), so a
  lift of a non-unit is a non-unit;
* `mem_smul_top_of_proj_eq_zero` converts `ker θ ·M_∞` (over `R_∞`) into
  `ker (θ ∘ lift) ·M_∞` (over `Λ`) elementwise, again along `lift`. -/
theorem nonempty_patchedModule_of_patchingData.{v, w, s, uR, u}
    {p : ℕ} [Fact p.Prime] {q : ℕ}
    {Runiv : Type uR} [CommRing Runiv] {T : Type s} [CommRing T] (ψ : Runiv →+* T)
    {Rinf : Type u} [CommRing Rinf] [IsLocalRing Rinf]
    (lift : MvPowerSeries (Fin q) ℤ_[p] →+* Rinf) (hlift : Function.Surjective lift)
    (θ : Rinf →+* Runiv) (hθ : Function.Surjective θ)
    {Minf : Type v} [AddCommGroup Minf] [Module Rinf Minf]
    (hfin : Module.Finite Rinf Minf)
    (rs : List Rinf) (hlen : rs.length = q + 1)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal Rinf)
    (hreg : RingTheory.Sequence.IsRegular Minf rs)
    {M0 : Type w} [AddCommGroup M0] [Module T M0] (hM0 : Nontrivial M0)
    (proj : Minf →+ M0) (hprojsurj : Function.Surjective proj)
    (hprojsmul : ∀ (a : Rinf) (m : Minf), proj (a • m) = ψ (θ a) • proj m)
    (hprojker : ∀ m : Minf, proj m = 0 →
      m ∈ RingHom.ker θ • (⊤ : Submodule Rinf Minf)) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) := by
  classical
  letI : Module (MvPowerSeries (Fin q) ℤ_[p]) Minf := Module.compHom Minf lift
  haveI hlh : IsLocalHom lift := .of_surjective lift hlift
  obtain ⟨g, hg⟩ : ∃ g : Rinf → MvPowerSeries (Fin q) ℤ_[p], ∀ b, lift (g b) = b :=
    ⟨fun b => (hlift b).choose, fun b => (hlift b).choose_spec⟩
  have hgmem : ∀ a ∈ rs, g a ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal a).mp (hmem a ha) (hg a ▸ hu.map lift)
  have hmaplift : (rs.map g).map lift = rs := by
    simp [List.map_map, Function.comp_def, hg]
  refine ⟨{ q := q
            Minf := Minf
            moduleMinf := inferInstance
            finiteMinf := moduleFinite_compHom lift hlift hfin
            exists_isRegular := ⟨rs.map g, by simpa using hlen, ?_, ?_⟩
            toRuniv := θ.comp lift
            toRuniv_surjective := hθ.comp hlift
            M0 := M0
            nontrivialM0 := hM0
            proj := proj
            proj_surjective := hprojsurj
            proj_smul := ?_
            mem_smul_top_of_proj_eq_zero := ?_ }⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact hgmem a ha
  · exact isRegular_compHom lift (rs.map g) (by rw [hmaplift]; exact hreg)
  · intro x m
    show proj (lift x • m) = ψ (θ (lift x)) • proj m
    exact hprojsmul (lift x) m
  · intro m hm
    refine Submodule.smul_induction_on (hprojker m hm) ?_ ?_
    · intro a ha n _
      have h1 : (g a) • n = a • n := by
        show lift (g a) • n = a • n
        rw [hg a]
      rw [← h1]
      refine Submodule.smul_mem_smul ?_ trivial
      rw [RingHom.mem_ker] at ha ⊢
      show θ (lift (g a)) = 0
      rw [hg a]; exact ha
    · intro x y hx hy
      exact add_mem hx hy

section PatchingInstantiation

open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

attribute [local instance] Module.quotientAnnihilator

/-! ### The leaves of the patching instantiation

DECOMPOSED 2026-07-25.  `exists_patchedModule_of_fields` below is pure
glue: it hands the raw fields of a `TaylorWilesSystem` to the vendored
patching development in `Modularity/PatchingVendored/`.  It used to
carry ten inline `sorry`ed `have`s, which is the largest single leaf
this file ever had and was not ownable by anybody: the ten steps live in
five unrelated mathematical contexts.  They are restated here as
separate top-level theorems, each in the SMALLEST context in which it is
true, so each has an owner who needs to know only that context:

* three about the coefficient ring `Λ = ℤ_p[[x₁, …, x_q]]` alone —
  `topologicallyFG_int_mvPowerSeries`,
  `finite_quotient_maximalIdeal_pow_mvPowerSeries`,
  `ker_constantCoeff_mvPowerSeries`;
* four of generic commutative algebra —
  `annihilator_eq_of_linearEquiv_piQuotient`,
  `free_quotientAnnihilator_of_linearEquiv_piQuotient`,
  `uniformlyBoundedRank_of_linearEquiv_piQuotient`,
  `mem_maximalIdeal_of_isRegular`;
* three about profinite local rings and their quotients —
  `finite_quotient_maximalIdeal_pow_of_surjective`,
  `continuous_of_finite_quotient_maximalIdeal_pow`,
  `algebra_uniformlyBoundedRank_of_surjective`;
* one about `ℤ_p`-rigidity of the bottom ring,
  `subsingleton_ringHom_padicInt`, packaged for use as
  `ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`;
* two about the bottom identification of the patched module,
  `quotientEquivOver_mkQ_smul` and
  `mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`, stated over the
  vendored variable context so that they are `smul_lemma` resp.
  `Submodule.map_algebraMap_smul` plus quotient bookkeeping.

Two shared bricks were factored out in the process because three leaves
each rested on them: `annihilator_eq_of_linearEquiv_piQuotient` (which
identifies `Ann_Λ (M n)` with `𝔟_n` and feeds the freeness, the rank
bound and the patching-system condition) and
`finite_quotient_maximalIdeal_pow_mvPowerSeries` (which feeds both
continuity of the diamond action and the uniform rank bound on the level
rings).

STATUS after the decomposition (2026-07-25).  Twelve of the sixteen are
PROVEN outright — the cut turned out to be most of the work:
`annihilator_eq_of_linearEquiv_piQuotient`,
`mem_maximalIdeal_of_isRegular`,
`continuousSMul_of_continuous_algebraMap`,
`finite_quotient_maximalIdeal_pow_of_surjective`,
`continuous_of_finite_quotient_maximalIdeal_pow`,
`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`,
`algebra_uniformlyBoundedRank_of_surjective`,
`isPatchingSystem_of_annihilator_le_maximalIdeal_pow`,
`quotientEquivOver_mkQ_smul`,
`mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`, and — added
2026-07-25 — `free_quotientAnnihilator_of_linearEquiv_piQuotient` and
`uniformlyBoundedRank_of_linearEquiv_piQuotient`, both over the new shared
brick `linearEquivPiQuotientAnnihilator`.  FOUR remain open and are the
real frontier here:

1. `topologicallyFG_int_mvPowerSeries` — density of `ℤ[x₁,…,x_q]` in `Λ`;
   PROVEN 2026-07-25;
2. `finite_quotient_maximalIdeal_pow_mvPowerSeries` — `|Λ/𝔪^k| < ∞`,
   which needs `Λ`'s residue field identified as `𝔽_p`; PROVEN 2026-07-25
   over the new brick `mem_maximalIdeal_mvPowerSeries`;
3. `ker_constantCoeff_mvPowerSeries` — `ker (constantCoeff) = (X₁,…,X_q)`
   in finitely many variables; PROVEN 2026-07-25 over the new brick
   `mem_span_X_image_of_coeff_eq_zero`;
4. `subsingleton_ringHom_padicInt` — `ℤ_p`-rigidity of a complete local
   ring with finite residue field; PROVEN 2026-07-25.

**ALL FOUR ARE NOW PROVEN**, as are the two coordinate-transport leaves
(`free_quotientAnnihilator_of_linearEquiv_piQuotient` and
`uniformlyBoundedRank_of_linearEquiv_piQuotient`) that stood at (4)–(5)
in an earlier numbering, so this block contributes no open leaf. -/

/-- **`Λ = ℤ_p[[x₁, …, x_q]]` is topologically finitely generated over
`ℤ`** (patching-instantiation leaf 1), for the scoped product topology
`MvPowerSeries.WithPiTopology`.

This is the one hypothesis of the vendored `PatchingVendored/Algebra.lean`
that profiniteness does not hand over for free.  The witnessing finite set
is the set of variables `{X i : i : Fin q}`, whose `ℤ`-subalgebra inside
`Λ` is the polynomial ring `ℤ[x₁, …, x_q]`.  It is DENSE because the
topology is the PRODUCT topology on `(Fin q →₀ ℕ) → ℤ_[p]`: a basic
neighbourhood of `f` constrains only finitely many coefficients, so
truncate `f` to those finitely many monomials and approximate each of
their coefficients by an integer, which is possible because `ℤ` is dense
in `ℤ_[p]` (`PadicInt.denseRange_intCast` / `denseRange_natCast`).

Stated for an ARBITRARY `Algebra ℤ Λ` instance because the vendored use
site fixes that instance by unification and there is no guarantee it is
syntactically `algebraInt`; the statement is harmless because
`Algebra ℤ R` is a subsingleton.

PROVEN 2026-07-25.  The proof never touches a neighbourhood basis: it
passes through the topological closure `B := (adjoin ℤ (range X))ᶜˡ`,
which is again a `Subalgebra ℤ Λ` (`Subalgebra.topologicalClosure`,
available because `Λ` is a topological ring for the pi topology).  Three
steps.  (i) `B` contains every constant `C a`, `a : ℤ_[p]`: `C` is
continuous (`MvPowerSeries.WithPiTopology.continuous_C`), so it carries
`closure (range (Int.cast))` — which is all of `ℤ_[p]` by
`PadicInt.denseRange_intCast` — into `closure (C '' range Int.cast)`, and
`C (n : ℤ) = (n : Λ)` lies in the subalgebra `adjoin ℤ (range X)` already.
(ii) `B` therefore contains the image of every `ℤ_[p]`-POLYNOMIAL, by
`MvPolynomial.induction_on` over `C`/`+`/`· X i`, using that `B` is a
subalgebra and contains each `X i`.  (iii) That image is dense
(`MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries`), so
`closure (adjoin ℤ (range X)) = ⊤`. -/
theorem topologicallyFG_int_mvPowerSeries (p : ℕ) [Fact p.Prime] (q : ℕ)
    [Algebra ℤ (MvPowerSeries (Fin q) ℤ_[p])] :
    Algebra.TopologicallyFG ℤ (MvPowerSeries (Fin q) ℤ_[p]) := by
  classical
  refine ⟨⟨Finset.univ.image (MvPowerSeries.X (σ := Fin q) (R := ℤ_[p])), ?_⟩⟩
  set Λ := MvPowerSeries (Fin q) ℤ_[p]
  have hcoe : ((Finset.univ.image (MvPowerSeries.X (σ := Fin q) (R := ℤ_[p])) : Finset Λ) : Set Λ)
      = Set.range (MvPowerSeries.X (σ := Fin q) (R := ℤ_[p])) := by
    simp
  rw [hcoe]
  set A : Subalgebra ℤ Λ := Algebra.adjoin ℤ (Set.range (MvPowerSeries.X (σ := Fin q) (R := ℤ_[p])))
  set B : Subalgebra ℤ Λ := A.topologicalClosure with hB
  have hXB : ∀ i : Fin q, (MvPowerSeries.X i : Λ) ∈ B :=
    fun i => A.le_topologicalClosure (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hCB : ∀ a : ℤ_[p], (MvPowerSeries.C a : Λ) ∈ B := by
    intro a
    have hmem : a ∈ closure (Set.range (Int.cast : ℤ → ℤ_[p])) :=
      PadicInt.denseRange_intCast a
    have himg : (MvPowerSeries.C : ℤ_[p] → Λ) '' closure (Set.range (Int.cast : ℤ → ℤ_[p]))
        ⊆ closure ((MvPowerSeries.C : ℤ_[p] → Λ) '' Set.range (Int.cast : ℤ → ℤ_[p])) :=
      image_closure_subset_closure_image MvPowerSeries.WithPiTopology.continuous_C
    have h2 : (MvPowerSeries.C a : Λ) ∈
        closure ((MvPowerSeries.C : ℤ_[p] → Λ) '' Set.range (Int.cast : ℤ → ℤ_[p])) :=
      himg ⟨a, hmem, rfl⟩
    have h3 : ((MvPowerSeries.C : ℤ_[p] → Λ) '' Set.range (Int.cast : ℤ → ℤ_[p])) ⊆ (A : Set Λ) := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      have hcast : (MvPowerSeries.C ((n : ℤ) : ℤ_[p]) : Λ) = (n : Λ) :=
        map_intCast (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])) n
      rw [hcast]
      exact intCast_mem A n
    have h4 : closure ((MvPowerSeries.C : ℤ_[p] → Λ) '' Set.range (Int.cast : ℤ → ℤ_[p]))
        ⊆ (B : Set Λ) := by
      rw [hB, Subalgebra.topologicalClosure_coe]
      exact closure_mono h3
    exact h4 h2
  have hpoly : ∀ φ : MvPolynomial (Fin q) ℤ_[p], ((φ : Λ)) ∈ B := by
    intro φ
    induction φ using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.coe_C]
      exact hCB a
    | add f g hf hg =>
      rw [MvPolynomial.coe_add]
      exact add_mem hf hg
    | mul_X f i hf =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X]
      exact mul_mem hf (hXB i)
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries
    (R := ℤ_[p]) (σ := Fin q)).closure_range]
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨φ, rfl⟩
  have hmemB := hpoly φ
  rw [hB, ← SetLike.mem_coe, Subalgebra.topologicalClosure_coe] at hmemB
  exact hmemB

/-- **The maximal ideal of a multivariate power series ring over a local
ring is the preimage of `𝔪` under `constantCoeff`** — a unit of
`Λ[[x]]` is exactly a series with unit constant term
(`MvPowerSeries.isUnit_iff_constantCoeff`).  The `PowerSeries` analogue
`mem_maximalIdeal_powerSeries` is proven far above in the
Auslander–Buchsbaum section; this is the multivariate one, needed here
to identify the residue field of `Λ`. -/
theorem mem_maximalIdeal_mvPowerSeries {σ : Type*} {A : Type*} [CommRing A] [IsLocalRing A]
    (f : MvPowerSeries σ A) :
    f ∈ maximalIdeal (MvPowerSeries σ A) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal A := by
  simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

/-- **The `𝔪`-adic truncations of `Λ = ℤ_p[[x₁, …, x_q]]` are finite**
(patching-instantiation shared brick, consumed by leaves 5 and 6).

`Λ` is local Noetherian (`isNoetherianRing_mvPowerSeries`) with residue
field `𝔽_p`, since `𝔪_Λ = (p, X₁, …, X_q)` and `Λ/𝔪_Λ ≃ ℤ_[p]/p ≃ 𝔽_p`.
So `Finite (Λ ⧸ 𝔪_Λ)`, and `Ideal.finite_quotient_pow` (which needs only
`𝔪_Λ` finitely generated, i.e. Noetherianity) upgrades that to every
power.  This is exactly the route `IsLocalRing.compactSpace_of_finite_residueField`
takes in `PatchingVendored/AdicTopology.lean`.

PROVEN 2026-07-25 along that route; the residue field is identified
without ever computing `𝔪_Λ` itself, by exhibiting the composite
`ψ = PadicInt.toZMod ∘ constantCoeff : Λ →+* ZMod p` as a surjection with
kernel `𝔪_Λ` (`mem_maximalIdeal_mvPowerSeries` plus
`PadicInt.ker_toZMod`). -/
theorem finite_quotient_maximalIdeal_pow_mvPowerSeries (p : ℕ) [Fact p.Prime] (q k : ℕ) :
    Finite (MvPowerSeries (Fin q) ℤ_[p] ⧸
      maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ k) := by
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p]) :=
    PowerSeriesAdicComplete.isNoetherianRing_mvPowerSeries q
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set ψ : MvPowerSeries (Fin q) ℤ_[p] →+* ZMod p :=
    (PadicInt.toZMod).comp MvPowerSeries.constantCoeff with hψ
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) z
    exact ⟨MvPowerSeries.C y, by simp [hψ, hy]⟩
  have hker : RingHom.ker ψ = maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    ext f
    rw [RingHom.mem_ker, mem_maximalIdeal_mvPowerSeries, ← PadicInt.ker_toZMod,
      RingHom.mem_ker]
    rfl
  haveI : Finite (MvPowerSeries (Fin q) ℤ_[p] ⧸ maximalIdeal (MvPowerSeries (Fin q) ℤ_[p])) :=
    Finite.of_equiv (ZMod p)
      ((Ideal.quotEquivOfEq hker.symm).trans
        (RingHom.quotientKerEquivOfSurjective hsurj)).symm.toEquiv
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

/-- **Peeling variables off one at a time** (the working form of the
augmentation-ideal leaf below, PROVEN 2026-07-25): if every coefficient
of `f` supported away from the finite set `s` vanishes, then `f` lies in
the ideal generated by `{X i : i ∈ s}`.

Induction on the FINSET `s`, which is where the finiteness hypothesis of
`ker_constantCoeff_mvPowerSeries` actually gets consumed — no currying
isomorphism is needed.  At `s = insert a t`, split `f` coefficientwise
into the part `h` supported on `d a = 0` and the rest: the rest is
divisible by `X a` (`MvPowerSeries.X_dvd_iff`) and `h` satisfies the
inductive hypothesis for `t`. -/
theorem mem_span_X_image_of_coeff_eq_zero {σ : Type*} [DecidableEq σ] {A : Type*} [CommRing A]
    (s : Finset σ) (f : MvPowerSeries σ A)
    (hf : ∀ d : σ →₀ ℕ, (∀ i ∈ s, d i = 0) → MvPowerSeries.coeff d f = 0) :
    f ∈ Ideal.span (MvPowerSeries.X '' (s : Set σ)) := by
  classical
  induction s using Finset.induction generalizing f with
  | empty =>
    have hz : f = 0 := by
      ext d
      simpa using hf d (by simp)
    simp [hz]
  | insert a t ha ih =>
    set h : MvPowerSeries σ A := fun d => if d a = 0 then MvPowerSeries.coeff d f else 0 with hh
    have hcoeff : ∀ d : σ →₀ ℕ,
        MvPowerSeries.coeff d h = if d a = 0 then MvPowerSeries.coeff d f else 0 := by
      intro d
      rw [MvPowerSeries.coeff_apply, hh]
    have hdvd : (MvPowerSeries.X a : MvPowerSeries σ A) ∣ (f - h) := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hcoeff, if_pos hm, sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hIH : h ∈ Ideal.span (MvPowerSeries.X '' (t : Set σ)) := by
      refine ih h ?_
      intro d hd
      rw [hcoeff]
      split_ifs with hda
      · refine hf d ?_
        intro i hi
        rcases Finset.mem_insert.mp hi with h1 | h1
        · exact h1 ▸ hda
        · exact hd i h1
      · rfl
    have hfeq : f = MvPowerSeries.X a * g + h := by
      have hsub : f - h = MvPowerSeries.X a * g := hg
      linear_combination (norm := ring_nf) hsub
    rw [hfeq]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, by simp, rfl⟩)
    · refine Ideal.span_mono ?_ hIH
      exact Set.image_mono (by simp [Finset.coe_insert])

/-- **The augmentation ideal is the kernel of the constant coefficient**
(patching-instantiation leaf 7a): for FINITELY many variables,
`ker (constantCoeff) = (X₁, …, X_q) = taylorWilesAug`.

`⊇` is `constantCoeff (X i) = 0`.  `⊆` is
`mem_span_X_image_of_coeff_eq_zero` at `s = univ`: the only exponent `d`
with `d i = 0` for every `i` is `d = 0`, so the hypothesis there is
exactly `constantCoeff f = 0`.  (The `Option`-currying isomorphism
`optionCurryEquiv` is NOT needed — the induction runs over the finset of
variables directly.)

FINITENESS IS ESSENTIAL and is why this is stated over `Fin q`: over
infinitely many variables `∑ᵢ Xᵢ` has zero constant coefficient but is not
in the span of the variables, an ideal all of whose elements involve only
finitely many of them.  In the proof it is consumed as `Finset.univ`.

PROVEN 2026-07-25. -/
theorem ker_constantCoeff_mvPowerSeries (q : ℕ) (A : Type*) [CommRing A] :
    RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin q) (R := A)) =
      Ideal.span (Set.range MvPowerSeries.X) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have key := mem_span_X_image_of_coeff_eq_zero (Finset.univ : Finset (Fin q)) f ?_
    · rwa [Finset.coe_univ, Set.image_univ] at key
    · intro d hd
      have hd0 : d = 0 := by
        ext i
        exact hd i (Finset.mem_univ i)
      subst hd0
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker]

/-- **The annihilator of a coordinatized level module** (patching-instantiation
shared brick, consumed by leaves 2, 3 and 4; PROVEN 2026-07-25): if `N ≃ₗ[Λ] (Λ/𝔟)^d` and `N`
is nontrivial then `Ann_Λ N = 𝔟`.

Two steps, both routine: the annihilator is an invariant of the `Λ`-linear
isomorphism class (transport `r • n = 0` along `f`), and
`Ann_Λ ((Λ/𝔟)^d) = 𝔟` as soon as `d ≥ 1`, by testing on the constant
family `(1, …, 1)` in one direction and `Ideal.Quotient.eq_zero_iff_mem` in
the other.  `d ≥ 1` is forced by `Nontrivial N`, which the use site gets
from surjectivity of `projM` onto the nontrivial `M₀`. -/
theorem annihilator_eq_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    Module.annihilator Λ N = b := by
  haveI : Nontrivial (Fin d → Λ ⧸ b) := f.symm.surjective.nontrivial
  have hd : 0 < d := by
    by_contra hcon
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin d → Λ ⧸ b)
    exact hxy (funext fun i => absurd i.2 (by omega))
  ext r
  rw [Module.mem_annihilator]
  constructor
  · intro hr
    have h1 := congrArg f (hr (f.symm (fun _ => (1 : Λ ⧸ b))))
    rw [map_smul, f.apply_symm_apply, map_zero] at h1
    have h3 : r • (1 : Λ ⧸ b) = 0 := congrFun h1 ⟨0, hd⟩
    rwa [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem] at h3
  · intro hr n
    apply f.injective
    rw [map_smul, map_zero]
    funext i
    show r • (f n i) = 0
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f n i)
    rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr

/-- **The coordinatization, read over `Λ/Ann` instead of over `Λ`**
(patching-instantiation shared brick, consumed by leaves 2 and 3; PROVEN
2026-07-25).

This is the whole content of both leaves and the reason they were given a
single owner.  Given `f : N ≃ₗ[Λ] (Λ/𝔟)^d` with `N` nontrivial,
`annihilator_eq_of_linearEquiv_piQuotient` says `Ann_Λ N = 𝔟`, so the
codomain may be rewritten as `(Λ/Ann_Λ N)^d` by
`Ideal.quotientEquivAlgOfEq` — which is a `Λ`-algebra equivalence, hence
`Λ`-linear componentwise.  That produces a `Λ`-linear equivalence
`N ≃ₗ[Λ] (Λ/Ann_Λ N)^d`; and since `Λ → Λ/Ann_Λ N` is SURJECTIVE, a
`Λ`-linear map between two `Λ/Ann_Λ N`-modules is automatically
`Λ/Ann_Λ N`-linear (`LinearEquiv.extendScalarsOfSurjective`).  No
semilinear algebra and no `RingHomInvPair` bookkeeping is needed.

The `Λ/Ann_Λ N`-module structure on `N` here is the local instance
`Module.quotientAnnihilator` declared at the top of this section, i.e. the
one the vendored `Module.UniformlyBoundedRank` and `Module.Free`
hypotheses are stated over. -/
noncomputable def linearEquivPiQuotientAnnihilator {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    N ≃ₗ[Λ ⧸ Module.annihilator Λ N] (Fin d → Λ ⧸ Module.annihilator Λ N) :=
  LinearEquiv.extendScalarsOfSurjective
    (R := Λ) (S := Λ ⧸ Module.annihilator Λ N)
    (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
    (f ≪≫ₗ LinearEquiv.piCongrRight fun _ =>
      (Ideal.quotientEquivAlgOfEq Λ
        (annihilator_eq_of_linearEquiv_piQuotient f).symm).toLinearEquiv)

/-- **A coordinatized level module is free over `Λ/Ann`**
(patching-instantiation leaf 2; PROVEN 2026-07-25), the hypothesis
`[∀ i, Module.Free (Λ ⧸ Ann Λ (M i)) (M i)]` of the vendored development.

By `annihilator_eq_of_linearEquiv_piQuotient` the base ring `Λ ⧸ Ann_Λ N`
IS `Λ ⧸ 𝔟`, over which `(Λ/𝔟)^d` is free of rank `d`.  The only wrinkle is
that `f` is stated `Λ`-linearly while freeness is asked over the quotient;
that is exactly what `linearEquivPiQuotientAnnihilator` above removes, after
which this is `Module.Free.of_equiv` against the free module `(Λ/Ann)^d`. -/
theorem free_quotientAnnihilator_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {N : Type*} [AddCommGroup N] [Module Λ N] [Nontrivial N]
    {d : ℕ} {b : Ideal Λ} (f : N ≃ₗ[Λ] (Fin d → Λ ⧸ b)) :
    Module.Free (Λ ⧸ Module.annihilator Λ N) N :=
  Module.Free.of_equiv (linearEquivPiQuotientAnnihilator f).symm

/-- **Uniformly bounded rank of the level modules** (patching-instantiation
leaf 3; PROVEN 2026-07-25): the SAME coordinate rank `d` at every level
bounds the rank uniformly, which is the whole point of the `freeM` field of
`TaylorWilesSystem`.

`rank_{Λ/Ann (M i)} (M i) = rank_{Λ/𝔟ᵢ} ((Λ/𝔟ᵢ)^d) = d` whenever `M i` is
nontrivial, by `linearEquivPiQuotientAnnihilator`; and when `M i` IS trivial
the base ring `Λ/Ann (M i) = Λ/⊤` is the ZERO ring, over which mathlib's
`rank_subsingleton` gives rank `1` — not `0`.  So the bound really is
`d + 2` and not `d + 1`: at `d = 0` a trivial `M i` still has rank `1`.
The case split is made on `Λ ⧸ Ann_Λ (M i)` rather than on `M i`, since
`Ideal.Quotient.nontrivial_iff` plus `Module.annihilator_eq_top_iff` turn
nontriviality of the quotient ring into the nontriviality of `M i` that
`linearEquivPiQuotientAnnihilator` needs. -/
theorem uniformlyBoundedRank_of_linearEquiv_piQuotient {Λ : Type*} [CommRing Λ]
    {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
    (d : ℕ) (b : ι → Ideal Λ) (f : ∀ i, M i ≃ₗ[Λ] (Fin d → Λ ⧸ b i)) :
    Module.UniformlyBoundedRank Λ M := by
  refine ⟨d + 2, fun i => ?_⟩
  rcases subsingleton_or_nontrivial (Λ ⧸ Module.annihilator Λ (M i)) with hs | hs
  · rw [rank_subsingleton]
    exact_mod_cast (by omega : (1 : ℕ) < d + 2)
  · have hne : Module.annihilator Λ (M i) ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp hs
    haveI : Nontrivial (M i) := not_subsingleton_iff_nontrivial.mp
      fun h => hne (Module.annihilator_eq_top_iff.mpr h)
    haveI : Module.Finite (Λ ⧸ Module.annihilator Λ (M i)) (M i) :=
      Module.Finite.equiv (linearEquivPiQuotientAnnihilator (f i)).symm
    rw [← Module.finrank_eq_rank, (linearEquivPiQuotientAnnihilator (f i)).finrank_eq,
      Module.finrank_fin_fun]
    exact_mod_cast (by omega : d < d + 2)

/-- **A regular sequence lies in the maximal ideal** (patching-instantiation
leaf 8; PROVEN 2026-07-25), over any local ring.

`RingTheory.Sequence.IsRegular` carries `top_ne_smul :
(⊤ : Submodule A N) ≠ Ideal.ofList rs • ⊤`, so `Ideal.ofList rs ≠ ⊤` —
otherwise `Ideal.top_smul` would make the right side `⊤`.  A proper ideal
of a local ring is contained in `𝔪` (`IsLocalRing.le_maximalIdeal`), and
every member of `rs` is in `Ideal.ofList rs`.

The use site is the sequence pushed from the diamond `Λ` into `R_∞`:
`nonempty_patchedModule_of_patchingData` asks for membership in `𝔪_{R_∞}`
in order to lift the sequence back along the presentation, and this is
where that comes from without knowing anything about `R_∞`. -/
theorem mem_maximalIdeal_of_isRegular {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] {rs : List A}
    (h : RingTheory.Sequence.IsRegular N rs) :
    ∀ x ∈ rs, x ∈ maximalIdeal A := by
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro htop
    exact h.top_ne_smul (by rw [htop, Submodule.top_smul])
  intro x hx
  exact IsLocalRing.le_maximalIdeal hne (Ideal.subset_span hx)

/-- **Continuity of the structure map gives a continuous scalar action**
(patching-instantiation leaf 5, the easy half; PROVEN).  Consumed with
`continuous_of_finite_quotient_maximalIdeal_pow` to produce the
`[∀ i, ContinuousSMul Λ (R i)]` hypothesis of the vendored development. -/
theorem continuousSMul_of_continuous_algebraMap {Λ S : Type*} [CommRing Λ] [CommRing S]
    [Algebra Λ S] [TopologicalSpace Λ] [TopologicalSpace S] [IsTopologicalRing S]
    (h : Continuous (algebraMap Λ S)) : ContinuousSMul Λ S := by
  refine ⟨?_⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

/-- **Finiteness of the truncations passes along a surjection of local
rings** (patching-instantiation leaf 5, the transport half; PROVEN 2026-07-25).

A surjective ring hom of local rings is local (`IsLocalHom.of_surjective`),
so it carries `𝔪_Λ` into `𝔪_S` and hence `𝔪_Λ^k` into `𝔪_S^k`; the
composite `Λ → S → S/𝔪_S^k` is therefore surjective and kills `𝔪_Λ^k`,
exhibiting `S/𝔪_S^k` as a quotient of the finite `Λ/𝔪_Λ^k`. -/
theorem finite_quotient_maximalIdeal_pow_of_surjective {Λ S : Type*} [CommRing Λ]
    [IsLocalRing Λ] [CommRing S] [IsLocalRing S] (f : Λ →+* S) (hf : Function.Surjective f)
    (k : ℕ) (hfin : Finite (Λ ⧸ maximalIdeal Λ ^ k)) :
    Finite (S ⧸ maximalIdeal S ^ k) := by
  haveI := hfin
  haveI : IsLocalHom f := .of_surjective f hf
  have hle : maximalIdeal Λ ^ k ≤ Ideal.comap f (maximalIdeal S ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) k
  refine Finite.of_surjective
    (Ideal.Quotient.lift (maximalIdeal Λ ^ k)
      ((Ideal.Quotient.mk (maximalIdeal S ^ k)).comp f) (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hle ha)) ?_
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨z, rfl⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ z, rfl⟩

/-- **Automatic continuity into a profinite local ring with finite
truncations** (patching-instantiation leaf 5, the substantive half;
PROVEN 2026-07-25).

`Λ` is compact and its topology is `𝔪`-adic, so `isOpen_iff_finite_quotient'`
(`PatchingVendored/AdicTopology.lean`) says an ideal of `Λ` is open exactly
when its quotient is finite.  For each `k`, `Λ ⧸ (𝔪_S^k).comap f` embeds in
the finite `S/𝔪_S^k`, hence is finite, hence `(𝔪_S^k).comap f` is open;
since `{𝔪_S^k}` is a neighbourhood basis of `0` in `S`
(`hasBasis_maximalIdeal_pow`), `f` is continuous at `0`, hence continuous.

NOTE this is genuinely weaker than `IsLocalRing.Continuous.of_isLocalHom`,
which the assembly uses for the PRESENTATION maps `pres n`: the DIAMOND
maps `dia n` are not local homs (the diamond variables need not land in
`𝔪`), so the local-hom route is unavailable and finiteness of the target's
truncations is what replaces it. -/
theorem continuous_of_finite_quotient_maximalIdeal_pow {Λ S : Type*} [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [IsAdicTopology Λ]
    [CommRing S] [IsLocalRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [IsAdicTopology S] (f : Λ →+* S)
    (hfin : ∀ k, Finite (S ⧸ maximalIdeal S ^ k)) : Continuous f := by
  apply continuous_of_continuousAt_zero
  unfold ContinuousAt
  rw [map_zero]
  apply ((hasBasis_maximalIdeal_pow Λ).tendsto_iff (hasBasis_maximalIdeal_pow S)).mpr
  intro n _
  haveI := hfin n
  haveI : Finite (Λ ⧸ Ideal.comap f (maximalIdeal S ^ n)) :=
    Finite.of_injective _ (Ideal.quotientMap_injective (I := maximalIdeal S ^ n) (f := f))
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    (Ideal.comap f (maximalIdeal S ^ n))
  exact ⟨m, trivial, fun x hx => hm hx⟩

/-- **`ℤ_p`-rigidity of the bottom ring** (patching-instantiation leaf 7b;
PROVEN 2026-07-25): a complete Noetherian local ring with finite residue
field receives AT MOST ONE ring homomorphism from `ℤ_[p]`.

Two steps.  First, `p` lands in `𝔪`.  This needs no unit/`ℚ_p` argument:
ANY ring homomorphism sends the natural-number cast `(p : ℤ_[p])` to the
natural-number cast `(p : A)` (`map_natCast`), and the existence of even
one `f : ℤ_[p] →+* A` forces the residue field to have characteristic `p`
— compose `f` with `IsLocalRing.residue` and apply
`charP_of_ringHom_padicInt`, which is exactly the statement that a FINITE
field receiving `ℤ_p` has characteristic `p` (the kernel is a nonzero
prime of the DVR `ℤ_p`, hence `(p)`).  So `(p : A) ∈ 𝔪` by
`IsLocalRing.residue_eq_zero_iff`, and `(p : A)^n ∈ 𝔪^n`.

Second, `A` is `𝔪`-adically separated (`IsAdicComplete → IsHausdorff`),
so it suffices to see `f x - g x ∈ 𝔪^n` for every `n`.  Writing
`x = (x.appr n : ℕ) + p^n * c` (`PadicInt.appr_spec`) and using
`map_natCast` again on the first summand, the two natural-number values
cancel and `f x - g x = (p : A)^n * (f c - g c) ∈ 𝔪^n`.

Note what is NOT needed: no continuity hypothesis (the conclusion is
`Subsingleton (ℤ_[p] →+* A)` for ALL ring homs, continuity being a
consequence of the `𝔪`-adic structure rather than an extra assumption),
and `IsNoetherianRing A` is unused by THIS proof — it is carried only to
match the hypothesis shape of the consumer
`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`.  The completeness
hypothesis is `IsAdicComplete` for the MAXIMAL ideal, which is the ideal
whose powers the `appr` estimate lands in, so the statement is the right
one (contrast `MvPowerSeries`, where mathlib's `IsAdicComplete` is for the
ideal of the variables and is strictly coarser).

HYPOTHESIS AUDIT (recorded 2026-07-26, cross-checked against an
independent proof of the same statement).  `hcomplete` is not logically
necessary: `Ideal.iInf_pow_eq_bot_of_isLocalRing` (Krull intersection)
already gives `⋂ₙ 𝔪ⁿ = ⊥` from `IsLocalRing` + `IsNoetherianRing` alone,
so separatedness can be had without completeness — the alternative proof
trades `hcomplete` for `IsNoetherianRing`, which this one leaves unused.
The hypothesis is KEPT because the consumer supplies it positionally and
because "complete local with finite residue field" is the shape the
patching interface hands down; nobody should read its presence as a claim
that completeness is what makes the statement true.

This is the completed-coefficient analogue of `ringHom_padicInt_eq` above,
which does the same for a finite FIELD target; the finite residue field is
what pins `p`, and `𝔪`-adic separatedness is what replaces "`𝔪 = 0`". -/
theorem subsingleton_ringHom_padicInt (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (hcomplete : IsAdicComplete (maximalIdeal A) A)
    (hres : Finite (A ⧸ maximalIdeal A)) : Subsingleton (ℤ_[p] →+* A) := by
  haveI : Finite (ResidueField A) := hres
  refine ⟨fun f g => ?_⟩
  have hchar : CharP (ResidueField A) p :=
    charP_of_ringHom_padicInt ((residue A).comp f)
  have hpmem : (p : A) ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ p
  ext x
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hcomplete.toIsHausdorff _ (fun n => ?_)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n x)
  have hx : x = ((x.appr n : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by
    rw [← hc]; ring
  have key : f x - g x = (p : A) ^ n * (f c - g c) := by
    rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpmem n)

/-- **The bottom `Λ`-algebra structure is independent of the level**
(patching-instantiation leaf 7; PROVEN 2026-07-25 over
`subsingleton_ringHom_padicInt` and `ker_constantCoeff_mvPowerSeries`): two ring homomorphisms
`Λ = ℤ_p[[x₁, …, x_q]] →+* A` that both kill the augmentation ideal
`taylorWilesAug p q = (X₁, …, X_q)` are EQUAL, when `A` is complete
Noetherian local with finite residue field.

This is the one compatibility the `TaylorWilesSystem` interface does not
record as a field, and it is derivable rather than an omission: both
`(tR n).comp (dia n)` kill `𝔫` — because `ker (tR n) = 𝔫.map (dia n)` —
hence factor through `Λ/𝔫`, which is `ℤ_[p]` by
`ker_constantCoeff_mvPowerSeries` and surjectivity of `constantCoeff`; and
a ring hom out of `ℤ_[p]` into `A` is unique by
`subsingleton_ringHom_padicInt`.

Without it neither `projM` nor `toRuniv` can be read as `Λ`-linear resp.
`Λ`-algebra maps, which is what `PatchingVendored/Over.lean` demands of the
bottom identifications `sR`/`sM`. -/
theorem ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker (p : ℕ) [Fact p.Prime] (q : ℕ)
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hcomplete : IsAdicComplete (maximalIdeal A) A) (hres : Finite (A ⧸ maximalIdeal A))
    (f g : MvPowerSeries (Fin q) ℤ_[p] →+* A)
    (hf : taylorWilesAug p q ≤ RingHom.ker f) (hg : taylorWilesAug p q ≤ RingHom.ker g) :
    f = g := by
  haveI := subsingleton_ringHom_padicInt p hcomplete hres
  have hker : RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])) =
      taylorWilesAug p q := ker_constantCoeff_mvPowerSeries q ℤ_[p]
  have hCeq : f.comp (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])) =
      g.comp (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])) := Subsingleton.elim _ _
  ext x
  have hy : x - MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x) ∈ taylorWilesAug p q := by
    rw [← hker, RingHom.mem_ker, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h1 : f x = f (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x)) := by
    have h := hf hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  have h2 : g x = g (MvPowerSeries.C (σ := Fin q) (R := ℤ_[p])
      (MvPowerSeries.constantCoeff x)) := by
    have h := hg hy
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  rw [h1, h2]
  exact DFunLike.congr_fun hCeq _

section LevelRings

variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsAdicTopology (R i)]

/-- **Uniformly bounded rank of the level rings** (patching-instantiation
leaf 6; PROVEN 2026-07-25): if every `R i` is a quotient of one fixed local ring `Λ` whose
`𝔪`-adic truncations are finite, then `|R i / 𝔪^k|` is bounded uniformly
in `i`.

Each `f i` is a surjective hom of local rings, hence local, so
`Λ/𝔪_Λ^k ↠ R i/𝔪_{R i}^k` (this is
`finite_quotient_maximalIdeal_pow_of_surjective` made quantitative), giving
`Nat.card (R i ⧸ 𝔪^k) ≤ Nat.card (Λ ⧸ 𝔪_Λ^k)` for EVERY `i`; take
`Nat.card (Λ ⧸ 𝔪_Λ^k) + 1` as the strict bound.

At the use site `f i` is the presentation `pres i`, not the diamond, which
is why the surjectivity hypothesis is available. -/
theorem algebra_uniformlyBoundedRank_of_surjective {Λ : Type*} [CommRing Λ] [IsLocalRing Λ]
    (f : ∀ i, Λ →+* R i) (hf : ∀ i, Function.Surjective (f i))
    (hfin : ∀ k, Finite (Λ ⧸ maximalIdeal Λ ^ k)) :
    Algebra.UniformlyBoundedRank R := by
  refine ⟨fun k => ⟨Nat.card (Λ ⧸ maximalIdeal Λ ^ k) + 1, fun i => ?_⟩⟩
  haveI := hfin k
  haveI : IsLocalHom (f i) := .of_surjective (f i) (hf i)
  have hle : maximalIdeal Λ ^ k ≤ Ideal.comap (f i) (maximalIdeal (R i) ^ k) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (((local_hom_TFAE (f i)).out 0 2).mp ‹_›) k
  have hgs : Function.Surjective (Ideal.Quotient.lift (maximalIdeal Λ ^ k)
      ((Ideal.Quotient.mk (maximalIdeal (R i) ^ k)).comp (f i)) (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hle ha)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := hf i y
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  exact Nat.lt_succ_of_le (Nat.card_le_card_of_surjective _ hgs)

/-- **The level modules form a patching system** (patching-instantiation
leaf 4; PROVEN 2026-07-25): the shrinking annihilators `Ann_Λ (M n) ≤ 𝔪^n` make `M` a patching
system along any ultrafilter refining `atTop`.

Let `α` be an open ideal of the compact `Λ`.  Then `Λ/α` is finite
(`isOpen_iff_finite_quotient'`), hence Artinian, so
`exists_maximalIdeal_pow_le_of_isArtinianRing_quotient` gives a `k` with
`𝔪^k ≤ α`.  For every `n ≥ k` we then have
`Ann_Λ (M n) ≤ 𝔪^n ≤ 𝔪^k ≤ α`, and `{n | k ≤ n} ∈ atTop ≤ F`.

The `Ann_Λ (M n) ≤ 𝔪^n` input is `annihilator_eq_of_linearEquiv_piQuotient`
composed with the `bIdeal_le` field of `TaylorWilesSystem`; the ultrafilter
refining `atTop` is `Ultrafilter.of Filter.atTop`, and nonprincipality —
the classical hypothesis — is exactly what `F ≤ atTop` encodes here. -/
theorem isPatchingSystem_of_annihilator_le_maximalIdeal_pow {Λ : Type*} [CommRing Λ]
    [IsLocalRing Λ] [IsNoetherianRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
    [CompactSpace Λ] [IsAdicTopology Λ]
    (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)]
    (F : Ultrafilter ℕ) (hF : (F : Filter ℕ) ≤ Filter.atTop)
    (hann : ∀ n, Module.annihilator Λ (M n) ≤ maximalIdeal Λ ^ n) :
    IsPatchingSystem Λ M F := by
  refine ⟨fun α hα => ?_⟩
  haveI : Finite (Λ ⧸ α) := isOpen_iff_finite_quotient'.mp hα
  obtain ⟨k, hk⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient α
  refine hF ?_
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  exact (hann n).trans ((Ideal.pow_le_pow_right hn).trans hk)

end LevelRings

section PatchedBottom

variable (Λ : Type*) [CommRing Λ]
variable {ι : Type*} (R : ι → Type*)
variable [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [∀ i, Algebra Λ (R i)]
variable [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
variable [∀ i, CompactSpace (R i)] [∀ i, IsAdicTopology (R i)]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module Λ (M i)]
variable [∀ i, Module (R i) (M i)] [∀ i, IsScalarTower Λ (R i) (M i)]
variable (F : Ultrafilter ι)
variable [TopologicalSpace Λ]
variable [IsLocalRing Λ] [IsNoetherianRing Λ] [NonarchimedeanRing Λ] [T2Space Λ]
variable [Algebra.TopologicallyFG ℤ Λ] [CompactSpace Λ] [∀ i, ContinuousSMul Λ (R i)]
variable [∀ i, IsNoetherianRing (R i)]
variable [Algebra.UniformlyBoundedRank R]
variable [∀ i, Module.Free (Λ ⧸ Module.annihilator Λ (M i)) (M i)]
variable [Module.UniformlyBoundedRank Λ M] [IsPatchingSystem Λ M F]
variable {R₀ M₀ : Type*} [CommRing R₀] [AddCommGroup M₀] [Module R₀ M₀] [Module.Finite R₀ M₀]
variable [IsLocalRing R₀] [IsNoetherianRing R₀]
  [TopologicalSpace R₀] [IsTopologicalRing R₀] [CompactSpace R₀] [IsAdicTopology R₀]
variable [Algebra Λ R₀] [Module Λ M₀] [Module.Finite Λ M₀]
variable (𝔫 : Ideal Λ)
variable (sR : ∀ i, (R i ⧸ 𝔫.map (algebraMap Λ (R i))) ≃ₐ[Λ] R₀)
variable (sM : ∀ i, (M i ⧸ (𝔫 • ⊤ : Submodule Λ (M i))) ≃ₗ[Λ] M₀)
variable [IsScalarTower Λ R₀ M₀] [∀ i, Nontrivial (M i)]

/-- **The bottom identification of the patched module is `R_∞`-semilinear**
(patching-instantiation leaf 9; PROVEN 2026-07-25 — it is exactly
`smul_lemma` applied to `Submodule.Quotient.mk m`, the two quotients
being definitionally equal): the composite
`M_∞ ↠ M_∞/𝔫M_∞ ≃ M₀` intertwines the `R_∞`-action on `M_∞` with the
`R₀`-action on `M₀` along `θ = quotientToOver ∘ mk`.

This is `PatchingVendored/System.lean`'s `smul_lemma` composed with the
quotient map `M_∞ ↠ M_∞/𝔫M_∞`.  The one piece of bookkeeping between the
two is that `smul_lemma` quotients by `𝔫 • ⊤` taken in
`Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)` while
`quotientEquivOver` quotients by `𝔫 • ⊤` taken in `Submodule Λ …`; the
vendored bridge is `Submodule.map_algebraMap_smul`, which says
`(𝔫.map (algebraMap Λ R_∞)) • N = 𝔫 • N` for an `R_∞`-submodule `N`.

At the use site `HCompat` is the `projM_smul` field of `TaylorWilesSystem`:
`sM i ∘ mk` IS `projM i` and `sR i ∘ mk` IS `toRuniv i` by construction of
those two identifications, so both sides read
`ψ (toRuniv i r) • projM i m`. -/
theorem quotientEquivOver_mkQ_smul
    (HCompat : ∀ i m (r : R i), sM i (Submodule.Quotient.mk (r • m)) =
      sR i (Ideal.Quotient.mk _ r) • sM i (Submodule.Quotient.mk m))
    (a : PatchingAlgebra R F) (m : PatchingModule Λ M F) :
    PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk (a • m)) =
      ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) a •
        PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk m) :=
  smul_lemma Λ R M F 𝔫 sR sM HCompat a (Submodule.Quotient.mk m)

/-- **The kernel of the bottom identification is inside `ker θ · M_∞`**
(patching-instantiation leaf 10; PROVEN 2026-07-25), the `mem_smul_top_of_proj_eq_zero` field
of `PatchedModule`.

`quotientEquivOver` is injective, so `m` maps to `0` exactly when
`m ∈ 𝔫 • ⊤` computed over `Λ`.  That `Λ`-submodule is contained in the
`R_∞`-submodule `𝔫 • ⊤`, which by `Submodule.map_algebraMap_smul` equals
`(𝔫.map (algebraMap Λ R_∞)) • ⊤`; and
`𝔫.map (algebraMap Λ R_∞) ≤ ker θ` because `θ` is by construction the map
`quotientToOver` out of `R_∞ ⧸ 𝔫.map (algebraMap Λ R_∞)` precomposed with
the quotient map, so it kills that ideal outright.  Conclude by
`Submodule.smul_mono_left`. -/
theorem mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero
    (m : PatchingModule Λ M F)
    (hm : PatchingModule.quotientEquivOver Λ M F 𝔫 sM (Submodule.Quotient.mk m) = 0) :
    m ∈ RingHom.ker ((PatchingAlgebra.quotientToOver Λ R F 𝔫 sR).comp (Ideal.Quotient.mk _)) •
      (⊤ : Submodule (PatchingAlgebra R F) (PatchingModule Λ M F)) := by
  have h0 : m ∈ (𝔫 • ⊤ : Submodule Λ (PatchingModule Λ M F)) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact (PatchingModule.quotientEquivOver Λ M F 𝔫 sM).injective (by rw [hm, map_zero])
  refine Submodule.smul_induction_on h0 ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul (PatchingAlgebra R F) r n]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [RingHom.mem_ker, RingHom.comp_apply,
      show (Ideal.Quotient.mk (𝔫.map (algebraMap Λ (PatchingAlgebra R F))))
          (algebraMap Λ (PatchingAlgebra R F) r) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr), map_zero]
  · intro x y hx hy
    exact add_mem hx hy

end PatchedBottom

set_option maxHeartbeats 1000000 in
/-- **The instantiation of the vendored patching development at a
Taylor–Wiles system** (ASSEMBLED 2026-07-25, DECOMPOSED the same day; the
glue is written and compiles, and every step it cannot see through is now
a separately owned top-level leaf immediately above rather than an inline
`sorry`), stated in terms of
the raw fields of `TaylorWilesSystem` so that the field-access noise
stays out of the proof.

The instantiation follows the handoff map in the docstring of
`TaylorWilesSystem.exists_patchedModule_natural`:

* `Λ := MvPowerSeries (Fin q) ℤ_[p]` carries the scoped product topology,
  in which it is compact, Hausdorff, totally disconnected and (by the
  project's own leaf `isNoetherianRing_mvPowerSeries`) Noetherian — so
  `IsLocalRing.IsAdicTopology Λ` and `NonarchimedeanRing Λ` are FREE
  through `PatchingVendored/AdicTopology.lean`'s "profinite + Noetherian
  ⟹ adic" instance, and the product topology never has to be compared
  with the adic one by hand.
* Each level ring `R n` is topologized by fiat with its own
  `𝔪`-adic topology (`IsLocalRing.withIdeal`); it is local and
  Noetherian as a quotient of `Λ`, Hausdorff for free, and COMPACT
  because `pres n` is a continuous surjection from the compact `Λ` —
  continuity being `IsLocalRing.Continuous.of_isLocalHom`, which applies
  precisely because both topologies are adic.
* `Runiv` likewise gets the adic topology by fiat and is compact by
  `IsLocalRing.compactSpace_of_finite_residueField`, fed by `hres` and
  `hcomplete`.
* `F` is an ultrafilter refining `atTop` on `ℕ` (so that the shrinking
  level ideals `bIdeal n ≤ 𝔪^n` make `M` a patching system).
* The patched objects are `R_∞ := PatchingAlgebra R F` with
  `lift := PatchingAlgebra.lift R F pres` (surjective by
  `lift_surjective`) and `M_∞ := PatchingModule Λ M F`, with
  `θ := quotientToOver ∘ mk` surjective by
  `surjective_quotientToOver`; `nonempty_patchedModule_of_patchingData`
  above turns that data into the `PatchedModule`.
* The regular sequence is produced in the DIAMOND copy — `M_∞` is FREE
  over the diamond `Λ` (the decisive output of
  `PatchingVendored/Module.lean`), hence flat, so the maximal regular
  system of parameters of `Λ`
  (`exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries`) stays
  weakly regular on `M_∞` by `isWeaklyRegular_rTensor`, and upgrades to
  regular by `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`
  (this is the Nakayama half) — then transported to `R_∞` by
  `isRegular_map_algebraMap_iff_of_tower`.  No `Module.depth` layer is
  needed, which is why `FLT/Patching/Utils/Depth.lean` was not
  vendored. -/
theorem exists_patchedModule_of_fields.{a, b, c, s, uR} {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv] [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (q d : ℕ) (R : ℕ → Type a) [iR : ∀ n, CommRing (R n)]
    (pres : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n)
    (hpres : ∀ n, Function.Surjective (pres n))
    (dia : ∀ n, MvPowerSeries (Fin q) ℤ_[p] →+* R n)
    (tR : ∀ n, R n →+* Runiv) (htR : ∀ n, Function.Surjective (tR n))
    (hkertR : ∀ n, RingHom.ker (tR n) = (taylorWilesAug p q).map (dia n))
    (M : ℕ → Type b) [iMg : ∀ n, AddCommGroup (M n)] [iMR : ∀ n, Module (R n) (M n)]
    [iMΛ : ∀ n, Module (MvPowerSeries (Fin q) ℤ_[p]) (M n)]
    (hdia : ∀ (n : ℕ) (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M n), x • m = dia n x • m)
    (bI : ℕ → Ideal (MvPowerSeries (Fin q) ℤ_[p]))
    (hbI : ∀ n, bI n ≤ maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) ^ n)
    (fM : ∀ n, M n ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
      (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ bI n))
    (M0 : Type c) [iM0g : AddCommGroup M0] [iM0T : Module T M0] (hM0 : Nontrivial M0)
    (prM : ∀ n, M n →+ M0) (hprM : ∀ n, Function.Surjective (prM n))
    (hprMsmul : ∀ (n : ℕ) (x : R n) (m : M n), prM n (x • m) = ψ (tR n x) • prM n m)
    (hprMzero : ∀ (n : ℕ) (m : M n), prM n m = 0 ↔
      m ∈ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)))
    (hcomplete : IsAdicComplete (maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{b, c, s, uR} p ψ) := by
  classical
  -- ### the coefficient ring `Λ = ℤ_p[[x₁, …, x_q]]` in its diamond role
  haveI : IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p]) :=
    isNoetherianRing_mvPowerSeries q
  haveI : CompactSpace (MvPowerSeries (Fin q) ℤ_[p]) :=
    inferInstanceAs (CompactSpace ((Fin q →₀ ℕ) → ℤ_[p]))
  haveI : TotallyDisconnectedSpace (MvPowerSeries (Fin q) ℤ_[p]) :=
    inferInstanceAs (TotallyDisconnectedSpace ((Fin q →₀ ℕ) → ℤ_[p]))
  haveI hadicΛ : IsAdicTopology (MvPowerSeries (Fin q) ℤ_[p]) := inferInstance
  -- LEAF 1 (`topologicallyFG_int_mvPowerSeries`)
  haveI hTFG : ∀ [inst : Algebra ℤ (MvPowerSeries (Fin q) ℤ_[p])],
      Algebra.TopologicallyFG ℤ (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro inst
    exact topologicallyFG_int_mvPowerSeries p q
  -- ### nontriviality of the levels
  haveI hMnt : ∀ n, Nontrivial (M n) := fun n => (hprM n).nontrivial
  -- the annihilator of each level module, the shared brick behind the
  -- next three steps (`annihilator_eq_of_linearEquiv_piQuotient`)
  have hann : ∀ n, Module.annihilator (MvPowerSeries (Fin q) ℤ_[p]) (M n) = bI n :=
    fun n => annihilator_eq_of_linearEquiv_piQuotient (fM n)
  -- LEAF 2 (`free_quotientAnnihilator_of_linearEquiv_piQuotient`)
  haveI hfree : ∀ n, Module.Free (MvPowerSeries (Fin q) ℤ_[p] ⧸
      Module.annihilator (MvPowerSeries (Fin q) ℤ_[p]) (M n)) (M n) :=
    fun n => free_quotientAnnihilator_of_linearEquiv_piQuotient (fM n)
  -- LEAF 3 (`uniformlyBoundedRank_of_linearEquiv_piQuotient`)
  haveI hubr : Module.UniformlyBoundedRank (MvPowerSeries (Fin q) ℤ_[p]) M :=
    uniformlyBoundedRank_of_linearEquiv_piQuotient M d bI fM
  -- ### the ultrafilter: any nonprincipal one, here a refinement of `atTop`
  letI F : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  -- LEAF 4 (`isPatchingSystem_of_annihilator_le_maximalIdeal_pow`)
  haveI hps : IsPatchingSystem (MvPowerSeries (Fin q) ℤ_[p]) M F :=
    isPatchingSystem_of_annihilator_le_maximalIdeal_pow M F (Ultrafilter.of_le Filter.atTop)
      (fun n => (hann n).trans_le (hbI n))
  -- ### the level rings, with their `𝔪`-adic topologies
  haveI iRnt : ∀ n, Nontrivial (R n) := fun n => (tR n).domain_nontrivial
  haveI iRloc : ∀ n, IsLocalRing (R n) := fun n => .of_surjective' (pres n) (hpres n)
  haveI iRnoeth : ∀ n, IsNoetherianRing (R n) :=
    fun n => isNoetherianRing_of_surjective _ _ (pres n) (hpres n)
  letI iRwi : ∀ n, WithIdeal (R n) := fun n => IsLocalRing.withIdeal
  haveI iRadic : ∀ n, IsAdicTopology (R n) := fun n => inferInstance
  haveI iRt2 : ∀ n, T2Space (R n) := fun n => inferInstance
  haveI iRlh : ∀ n, IsLocalHom (pres n) := fun n => .of_surjective _ (hpres n)
  have hprescont : ∀ n, Continuous (pres n) := fun n => Continuous.of_isLocalHom _
  haveI iRcpt : ∀ n, CompactSpace (R n) := fun n =>
    ⟨by
      rw [← Set.range_eq_univ.mpr (hpres n)]
      exact isCompact_range (hprescont n)⟩
  letI iRalg : ∀ n, Algebra (MvPowerSeries (Fin q) ℤ_[p]) (R n) := fun n => (dia n).toAlgebra
  -- LEAF 5 (`finite_quotient_maximalIdeal_pow_of_surjective` and
  -- `continuous_of_finite_quotient_maximalIdeal_pow`, glued by
  -- `continuousSMul_of_continuous_algebraMap`)
  haveI iRfin : ∀ (n k : ℕ), Finite (R n ⧸ maximalIdeal (R n) ^ k) := fun n k =>
    finite_quotient_maximalIdeal_pow_of_surjective (pres n) (hpres n) k
      (finite_quotient_maximalIdeal_pow_mvPowerSeries p q k)
  haveI iRcsmul : ∀ n, ContinuousSMul (MvPowerSeries (Fin q) ℤ_[p]) (R n) := fun n =>
    continuousSMul_of_continuous_algebraMap
      (continuous_of_finite_quotient_maximalIdeal_pow (dia n) (iRfin n))
  -- LEAF 6 (`algebra_uniformlyBoundedRank_of_surjective`)
  haveI hRubr : Algebra.UniformlyBoundedRank R :=
    algebra_uniformlyBoundedRank_of_surjective R pres hpres
      (finite_quotient_maximalIdeal_pow_mvPowerSeries p q)
  haveI iRtower : ∀ n, IsScalarTower (MvPowerSeries (Fin q) ℤ_[p]) (R n) (M n) :=
    fun n => .of_algebraMap_smul fun r m => (hdia n r m).symm
  -- ### the bottom ring
  letI iRunivwi : WithIdeal Runiv := IsLocalRing.withIdeal
  haveI : IsAdicTopology Runiv := inferInstance
  haveI : Finite (ResidueField Runiv) := hres
  haveI : IsAdicComplete (maximalIdeal Runiv) Runiv := hcomplete
  haveI : CompactSpace Runiv := IsLocalRing.compactSpace_of_finite_residueField
  -- LEAF 7 (`ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker`): both
  -- `tR n ∘ dia n` kill the augmentation ideal, by `hkertR`.
  have hkeraug : ∀ n, taylorWilesAug p q ≤ RingHom.ker ((tR n).comp (dia n)) := by
    intro n x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hkertR n]
    exact Ideal.mem_map_of_mem _ hx
  have hcompat : ∀ n, (tR n).comp (dia n) = (tR 0).comp (dia 0) := fun n =>
    ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker p q hcomplete hres _ _
      (hkeraug n) (hkeraug 0)
  letI iRunivalg : Algebra (MvPowerSeries (Fin q) ℤ_[p]) Runiv :=
    ((tR 0).comp (dia 0)).toAlgebra
  letI iM0Runiv : Module Runiv M0 := Module.compHom M0 ψ
  letI iM0Λ : Module (MvPowerSeries (Fin q) ℤ_[p]) M0 :=
    Module.compHom M0 (ψ.comp ((tR 0).comp (dia 0)))
  haveI iM0tower : IsScalarTower (MvPowerSeries (Fin q) ℤ_[p]) Runiv M0 :=
    .of_algebraMap_smul fun _ _ => rfl
  -- ### `projM` is `Λ`-linear, and `M₀` is `Λ`-finite
  let prMₗ : ∀ n, M n →ₗ[MvPowerSeries (Fin q) ℤ_[p]] M0 := fun n =>
    { toFun := prM n
      map_add' := (prM n).map_add
      map_smul' := fun r m => by
        show prM n (r • m) = _
        rw [hdia n r m, hprMsmul n (dia n r) m]
        show ψ (tR n (dia n r)) • prM n m = ψ (((tR 0).comp (dia 0)) r) • prM n m
        rw [← hcompat n]; rfl }
  have hkerprM : ∀ n, LinearMap.ker (prMₗ n) =
      (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)) :=
    fun n => Submodule.ext fun m => (hprMzero n m)
  haveI hM0finΛ : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) M0 := by
    haveI : Module.Finite (MvPowerSeries (Fin q) ℤ_[p]) (M 0) :=
      Module.Finite.equiv (fM 0).symm
    exact Module.Finite.of_surjective (prMₗ 0) (hprM 0)
  haveI hM0finR : Module.Finite Runiv M0 :=
    Module.Finite.of_restrictScalars_finite (MvPowerSeries (Fin q) ℤ_[p]) Runiv M0
  -- ### the bottom identifications demanded by `PatchingVendored/Over.lean`
  let sR : ∀ n, (R n ⧸ (taylorWilesAug p q).map
        (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (R n)))
      ≃ₐ[MvPowerSeries (Fin q) ℤ_[p]] Runiv := fun n =>
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (hkertR n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (htR n))) (fun x => by
        show tR n (dia n x) = ((tR 0).comp (dia 0)) x
        rw [← hcompat n]; rfl)
  let sM : ∀ n, (M n ⧸ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p]) (M n)))
      ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]] M0 := fun n =>
    (Submodule.quotEquivOfEq _ _ (hkerprM n).symm).trans
      ((prMₗ n).quotKerEquivOfSurjective (hprM n))
  -- ### the patched objects
  let lift : MvPowerSeries (Fin q) ℤ_[p] →+* PatchingAlgebra R F :=
    PatchingAlgebra.lift R F pres
  have hliftsurj : Function.Surjective lift :=
    PatchingAlgebra.lift_surjective R F pres hprescont hpres
  let θ : PatchingAlgebra R F →+* Runiv :=
    (PatchingAlgebra.quotientToOver (MvPowerSeries (Fin q) ℤ_[p]) R F
      (taylorWilesAug p q) sR).comp (Ideal.Quotient.mk _)
  have hθsurj : Function.Surjective θ :=
    (PatchingAlgebra.surjective_quotientToOver (MvPowerSeries (Fin q) ℤ_[p]) R F
      (taylorWilesAug p q) sR).comp Ideal.Quotient.mk_surjective
  let projQ := PatchingModule.quotientEquivOver (MvPowerSeries (Fin q) ℤ_[p]) M F
    (taylorWilesAug p q) sM
  -- ### the regular sequence, produced in the diamond copy and pushed forward
  obtain ⟨ts, htslen, htsreg, htsspan⟩ :=
    exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries p q
  have htsmem : ∀ x ∈ ts, x ∈ maximalIdeal (MvPowerSeries (Fin q) ℤ_[p]) := by
    intro x hx
    rw [← htsspan]
    exact Ideal.subset_span hx
  haveI hM0' : Nontrivial M0 := hM0
  haveI hQnt : Nontrivial (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F ⧸
      (taylorWilesAug p q • ⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))) := projQ.toEquiv.nontrivial
  haveI hMinfnt : Nontrivial (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F) :=
    Function.Surjective.nontrivial (Submodule.mkQ_surjective
      ((taylorWilesAug p q • ⊤ : Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))))
  have hregdia : RingTheory.Sequence.IsRegular
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F) ts := by
    refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal htsmem).mpr ?_
    exact ((TensorProduct.lid (MvPowerSeries (Fin q) ℤ_[p])
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)).isWeaklyRegular_congr ts).mp
      (htsreg.1.isWeaklyRegular_rTensor
        (M₂ := PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))
  have hregRinf : RingTheory.Sequence.IsRegular
      (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)
      (ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (PatchingAlgebra R F))) :=
    (isRegular_map_algebraMap_iff_of_tower
      (B := PatchingAlgebra R F) ts).mpr hregdia
  -- LEAF 8 (`mem_maximalIdeal_of_isRegular`)
  have hmemRinf : ∀ x ∈ ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingAlgebra R F)),
      x ∈ maximalIdeal (PatchingAlgebra R F) :=
    mem_maximalIdeal_of_isRegular hregRinf
  -- ### the bottom identification of the patched module
  let projA : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F →+ M0 :=
    (projQ.toLinearMap.toAddMonoidHom).comp
      (Submodule.mkQ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p])
        (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F))).toAddMonoidHom
  have hprojAsurj : Function.Surjective projA :=
    projQ.surjective.comp (Submodule.mkQ_surjective _)
  -- LEAF 9 (`quotientEquivOver_mkQ_smul`); its `HCompat` hypothesis is
  -- the `projM_smul` field read through the construction of `sM`/`sR`.
  have hHCompat : ∀ (n : ℕ) (m : M n) (r : R n),
      sM n (Submodule.Quotient.mk (r • m)) =
        sR n (Ideal.Quotient.mk _ r) • sM n (Submodule.Quotient.mk m) := by
    intro n m r
    show prM n (r • m) = ψ (tR n r) • prM n m
    exact hprMsmul n r m
  have hprojAsmul : ∀ (a : PatchingAlgebra R F)
      (m : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F),
      projA (a • m) = ψ (θ a) • projA m := fun a m =>
    quotientEquivOver_mkQ_smul (MvPowerSeries (Fin q) ℤ_[p]) R M F
      (taylorWilesAug p q) sR sM hHCompat a m
  -- LEAF 10 (`mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero`)
  have hprojAker : ∀ m : PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F, projA m = 0 →
      m ∈ RingHom.ker θ •
        (⊤ : Submodule (PatchingAlgebra R F)
          (PatchingModule (MvPowerSeries (Fin q) ℤ_[p]) M F)) := fun m hm =>
    mem_ker_smul_top_of_quotientEquivOver_mkQ_eq_zero (MvPowerSeries (Fin q) ℤ_[p]) R M F
      (taylorWilesAug p q) sR sM m hm
  exact nonempty_patchedModule_of_patchingData ψ lift hliftsurj θ hθsurj inferInstance
    (ts.map (algebraMap (MvPowerSeries (Fin q) ℤ_[p]) (PatchingAlgebra R F)))
    (by simpa using htslen) hmemRinf hregRinf hM0 projA hprojAsurj hprojAsmul hprojAker

end PatchingInstantiation

/-- **The patching extraction at its natural universes** (patching
leaf 2b′; ASSEMBLED 2026-07-25 — this declaration is now GLUE over
`exists_patchedModule_of_fields` above, which instantiates the vendored
development and is itself sorry-free glue over the sixteen named leaves
stated immediately above it, six of which are still open; opened
2026-07-25 as the universe-monomorphic
form of `TaylorWilesSystem.exists_patchedModule`): identical content,
but with the patched module in the universe `b` of the tower's modules
`S.M` and the bottom module in the universe `c` of `S.M0`.  The
polymorphic statement follows by `PatchedModule.nonempty_transport`.

This is the shape the vendored FLT patching development
(`Fermat/FLT/Modularity/PatchingVendored/`) can actually hit: its
`PatchingModule Λ M F` is a submodule of a product indexed by the
`Type 0` type `OpenIdeals Λ` of components which are ultraproducts of
quotients of the `M i`, hence lands in `Type b`, and its bottom
identification `PatchingModule.quotientEquivOver` lands on `S.M0`
itself, in `Type c`.

HANDOFF MAP (2026-07-25) — the instantiation of the vendored
development at `S`, worked out but not yet written:

* `Λ := MvPowerSeries (Fin S.q) ℤ_[p]` in its **diamond** role, with
  the scoped product topology `MvPowerSeries.WithPiTopology`.  The
  topological hypotheses of the vendored files are then: `CompactSpace`
  (a product of copies of the compact `ℤ_[p]`), `T2Space`
  (`MvPowerSeries.WithPiTopology.instT2Space`), `IsTopologicalRing`
  (`…instIsTopologicalRing`), `TotallyDisconnectedSpace`, and
  `IsNoetherianRing` (the project's own leaf
  `isNoetherianRing_mvPowerSeries`).  Crucially `IsAdicTopology Λ` is
  then FREE: `PatchingVendored/AdicTopology.lean` carries the instance
  "a profinite Noetherian ring has the `𝔪`-adic topology", so the
  product topology need never be compared with the adic one by hand.
  This was CHECKED against the pin on 2026-07-25: with
  `open scoped MvPowerSeries.WithPiTopology`, the goal
  `IsLocalRing.IsAdicTopology (MvPowerSeries (Fin q) ℤ_[p])` closes by
  `infer_instance` from `[IsNoetherianRing (MvPowerSeries (Fin q) ℤ_[p])]`
  alone, after the two `inferInstanceAs` steps that unfold
  `MvPowerSeries (Fin q) ℤ_[p]` to `(Fin q →₀ ℕ) → ℤ_[p]` for
  `CompactSpace` and `TotallyDisconnectedSpace`.  Gotcha: the latter
  needs `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` and
  `Mathlib.Topology.Connected.TotallyDisconnected` imported (the route
  is `IsUltrametricDist ℤ_[p] → TotallySeparatedSpace →
  TotallyDisconnectedSpace`, then `Pi.totallyDisconnectedSpace`);
  without them synthesis fails with no hint of the cause.
  `Algebra.TopologicallyFG ℤ Λ` holds because `ℤ`-adjoining the
  variables is dense (`ℤ` is dense in `ℤ_[p]`).
* `ι := ℕ`, `F :=` any nonprincipal ultrafilter on `ℕ`;
  `R i := S.R i` with `Algebra Λ (R i)` given by `S.diamond i`, and
  `M i := S.M i` with `IsScalarTower Λ (R i) (M i)` given by
  `S.diamond_smul`.  Each `R i` is topologized by the topology
  coinduced along the surjection `S.pres i`, which makes it profinite
  (its kernel is f.g. by Noetherianity, hence compact, hence closed),
  so again `IsAdicTopology (R i)` is free, and
  `Algebra.UniformlyBoundedRank R` holds because
  `R i / 𝔪^k` is a quotient of the FIXED finite ring `Λ/𝔪^k`.
* `Module.UniformlyBoundedRank Λ M` and
  `Module.Free (Λ ⧸ Ann Λ (M i)) (M i)` come from `S.freeM` (rank `d`,
  annihilator `S.bIdeal i`), and `IsPatchingSystem Λ M F` from
  `S.bIdeal_le` (`𝔟_n ≤ 𝔪^n → 0`).  Here `1 ≤ S.d` is forced by
  `S.nontrivialM0` through `S.projM_surjective`.
* `Runiv` plays the vendored `R₀`: `hres` and `hcomplete` give
  `CompactSpace` through
  `IsLocalRing.compactSpace_of_finite_residueField`, with the adic
  topology taken by fiat (`IsLocalRing.withIdeal`).
* The bottom identifications `sR`/`sM` demanded by
  `PatchingVendored/Over.lean` are `S.toRuniv i`/`S.projM i` read
  through `S.ker_toRuniv`/`S.projM_eq_zero_iff`, with `𝔫` the
  augmentation ideal `taylorWilesAug p S.q`.  They must be `Λ`-ALGEBRA
  resp. `Λ`-LINEAR, which needs one compatibility NOT recorded as a
  field of `TaylorWilesSystem`: that `(S.toRuniv i).comp (S.diamond i)`
  is independent of `i`.  It is derivable, not an omission: both sides
  kill `𝔫` (by `S.ker_toRuniv`) hence factor through
  `Λ/𝔫 ≅ ℤ_[p]`, and a ring hom `ℤ_[p] →+* Runiv` is unique because
  (i) `p` cannot map to a unit — otherwise `ℚ_p` would embed in
  `Runiv` and its residue field, contradicting `hres` — so `p ↦ 𝔪`,
  and (ii) `Runiv` is `𝔪`-adically separated by `hcomplete`, so the
  value on `ℤ_[p]` is pinned by the value on the dense subring `ℤ`.
* The `PatchedModule` fields are then read off:
  `Minf := PatchingModule Λ M F` with the `Λ`-action taken through
  `PatchingAlgebra.lift R F S.pres` (the **presentation** role of the
  same ring — `lift` needs only ring homs, not `Λ`-algebra maps, so
  the two roles of `Λ` never have to be reconciled);
  `toRuniv := PatchingAlgebra.quotientToOver … ∘ mk ∘ lift`, surjective
  by `PatchingAlgebra.lift_surjective` and
  `PatchingAlgebra.surjective_quotientToOver`; `proj` and `proj_smul`
  from `PatchingModule.quotientEquivOver` and `smul_lemma`;
  `mem_smul_top_of_proj_eq_zero` because `ker proj` is generated by
  the image of `𝔫`, which `toRuniv` kills.
* `exists_isRegular` is where this project departs from FLT (whose
  endgame goes through `Module.depth`, deliberately not vendored):
  take the project's own
  `exists_isRegular_ofList_eq_maximalIdeal_mvPowerSeries` sequence
  `(p, S₁, …, S_q)` in the DIAMOND copy, push it into
  `PatchingAlgebra` and lift it back along the surjection `lift` (the
  lifts stay in `𝔪` because a surjection of local rings is local);
  it is `M_∞`-regular because `M_∞` is FREE over the diamond `Λ`
  (`instance : Module.Free Λ (PatchingModule Λ M F)`, the decisive
  output of `PatchingVendored/Module.lean`) — the transfer lemma is
  `RingTheory.Sequence.isWeaklyRegular_of_free` of
  `FLT/Patching/Utils/Depth.lean`, the one declaration of that file
  worth vendoring. -/
theorem TaylorWilesSystem.exists_patchedModule_natural.{a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv]
    [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (S : TaylorWilesSystem.{a, b, c, s, uR} p ψ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ IsLocalRing.maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{b, c, s, uR} p ψ) := by
  -- the structure's instance FIELDS are not in scope as instances once the
  -- data fields are passed one by one, so install them first
  letI := S.commRingR
  letI := S.addCommGroupM
  letI := S.moduleRM
  letI := S.moduleCoeffM
  letI := S.addCommGroupM0
  letI := S.moduleM0
  exact exists_patchedModule_of_fields S.q S.d S.R S.pres S.pres_surjective S.diamond
    S.toRuniv S.toRuniv_surjective S.ker_toRuniv S.M S.diamond_smul S.bIdeal
    S.bIdeal_le S.freeM S.M0 S.nontrivialM0 S.projM S.projM_surjective S.projM_smul
    (fun n m => ⟨(S.projM_eq_zero_iff n m).mp, (S.projM_eq_zero_iff n m).mpr⟩)
    hcomplete hres

/-- **The patching extraction** (patching leaf 2b; sorry node — the
pure commutative-algebra half, the pigeonhole/inverse-limit heart): a
`TaylorWilesSystem` for `ψ`, together with completeness and residual
finiteness of `Runiv`, yields the `PatchedModule` for `ψ`.
Unconditionally true — no arithmetic content (every hypothesis is
commutative algebra; the Galois/Hecke content is packaged inside the
system's fields).

Classical route (Taylor–Wiles 1995 §3; Diamond 1997, proof of
Thm. 3.1; DDT (1995), proof of Thm. 5.28; Kisin 2009 §(2.2) for the
inverse-limit reorganization): for every open level `α = 𝔪_Λ^j`, the
truncated data `(R n/𝔪^{f(j)}, M n/αM n, toRuniv n, projM n)` ranges
over FINITELY many isomorphism types (all objects are finite of
bounded cardinality, by `pres_surjective` and `freeM` with the fixed
rank `d`), so a pigeonhole (König's lemma, or an ultrafilter as in
`FLT/Patching`) extracts a subtower compatible under the level maps;
the inverse limit `M_∞` is finite over `Λ = ℤ_p[[x₁, …, x_q]]` acting
through the limit of `pres`, indeed finite FREE over the `S`-copy of
`Λ` acting through the limit of `diamond` (the `freeM` coordinates
converge since `𝔟_n → 0` by `bIdeal_le`), whence the images of the
maximal regular sequence `(p, S₁, …, S_q)` — lifted through the limit
presentation into the maximal ideal — form the required `M_∞`-regular
sequence of length `q + 1` (`exists_isRegular`); the limit of
`toRuniv n ∘ pres n` is the patching surjection `R_∞ ↠ Runiv`
(surjectivity from `IsAdicComplete` and residual finiteness, which
exhibit `Runiv` as the limit of its finite `𝔪`-power quotients), and
the limits of `projM` give the bottom identification, with
`proj_smul` from `projM_smul` and `mem_smul_top_of_proj_eq_zero` from
`projM_eq_zero_iff` (converting the `𝔫`-action into the
`ker toRuniv`-action by lifting the variables `Sᵢ` through the limit
presentation into `ker toRuniv`).

VENDORING PLAN (pin-drift audit 2026-07-24): the sorry-free abstract
patching development of the FLT project implements exactly this
extraction in ultraproduct form — `FLT/Patching/Ultraproduct.lean`
(`UltraProduct` and its quotient calculus), `Module.lean`
(`PatchingModule`, `Module.UniformlyBoundedRank`, `IsPatchingSystem`,
and decisively `instance : Module.Free R (PatchingModule R M F)`, the
patched freeness), `Algebra.lean` (`PatchingAlgebra`, `lift`,
`lift_surjective`, `constEquiv`), `Over.lean`/`System.lean`
(`quotientToOver`, `quotientEquivOver`, `smulData`, `smul_lemma` —
the bottom identifications and the action descent), plus
`Utils/{Lemmas,StructureFiniteness,InverseLimit,AdicTopology,
TopologicallyFG,CompactHausdorffRings}.lean`.  All patching names are
FLT-project-local (no mathlib counterparts), so the vendoring cost is
the MATHLIB drift between the FLT pin `81a5d25` (mathlib v4.32.0) and
this project's pin `a3364fa` — plus dropping their
`Utils/Depth.lean`/`REqualsT.lean` layer: their endgame
`ker_RtoT_le_nilradical` goes through `Module.depth` and yields only
`R_red = 𝕋_red`, which our regular-sequence formulation replaces
(leaf 3 `free_of_isRegular_mvPowerSeries` owns the
Auslander–Buchsbaum content instead).  Instantiate at
`Λ := ℤ_p[[S₁, …, S_q]]`, `R i := S.R i`, `M i := S.M i`, `F` any
nonprincipal ultrafilter on `ℕ`, with the topological instances
derived from `pres_surjective` (quotient topologies of the product
topology on `MvPowerSeries`, scoped
`MvPowerSeries.WithPiTopology`): `Algebra.UniformlyBoundedRank` from
the fixed presentation ring, `Module.UniformlyBoundedRank` and
`IsPatchingSystem` from `freeM`/`bIdeal_le` (the `Λ`-annihilator of
`(Λ/𝔟_n)^d` is `𝔟_n ≤ 𝔪^n → 0` for `d ≥ 1`, and `d ≥ 1` is forced by
`nontrivialM0` through `projM_surjective`).

Universe note: the conclusion is polymorphic in `{v, w}`; the
construction lands in fixed universes and is transported by
quotient-presentation shrinking (a finite module over the `Type 0`
ring `MvPowerSeries (Fin q) ℤ_[p]` is isomorphic to a `Type 0`
quotient of `Fin m → MvPowerSeries (Fin q) ℤ_[p]`, and `M0` to the
`proj`-image quotient of `M_∞` with the `T`-action transported along
the identification) followed by `ULift`.

PROOF (glue, 2026-07-25): that universe note is now DISCHARGED —
`PatchedModule.nonempty_transport` above carries out both shrinkings
and the `ULift`, so this node reduces to
`TaylorWilesSystem.exists_patchedModule_natural`, the same statement at
the universes the vendored FLT patching development actually produces.
The abstract patching machinery itself is vendored and verified in
`Fermat/FLT/Modularity/PatchingVendored/` (ten modules, elaborating
clean against this project's mathlib pin); the remaining frontier is
the INSTANTIATION of that machinery at `S`, mapped out in the
docstring of `exists_patchedModule_natural`. -/
theorem TaylorWilesSystem.exists_patchedModule.{v, w, a, b, c, s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv]
    [IsNoetherianRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T}
    (S : TaylorWilesSystem.{a, b, c, s, uR} p ψ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    (hres : Finite (Runiv ⧸ IsLocalRing.maximalIdeal Runiv)) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) :=
  (S.exists_patchedModule_natural hcomplete hres).elim
    fun P => PatchedModule.nonempty_transport P

/-- **The Taylor–Wiles patching construction** (patching node 2;
ASSEMBLED 2026-07-24 as glue over the two leaves above): under the
full hypothesis set of pillar 3b-iii, together with the Taylor–Wiles
prime supply `hTW`, the patched situation exists.

Classical route (Taylor–Wiles, Ann. of Math. 141 (1995), as
reorganized by Diamond, Invent. Math. 128 (1997), Fujiwara, and
Diamond–Darmon–Taylor (1995) §5.5; Kisin, Ann. of Math. 170 (2009) for
the flat refinement): for each level `n` pick a Taylor–Wiles set `Q_n`
of the common size `q = dim_k H¹_{Q_n}(ad⁰ρbar)` (from `hTW` refined
by the dual-Selmer annihilation argument — the cohomological
sharpening of the prime supply is internal to this leaf, `hTW`
records its Chebotarev skeleton); form the auxiliary deformation rings
`R_{Q_n}` (quotients of `R_∞ = ℤ_p[[x₁, …, x_q]]` by the tangent-space
bound and smoothness of the local conditions — Ramakrishna flatness at
`p`, CDT tameness at `2`) and the auxiliary Hecke modules `H_{Q_n}`,
finite free over `ℤ_p[Δ_{Q_n}]` by the Taylor–Wiles freeness lemma
(Diamond 1997, Thm. 2.1, without multiplicity one); the weak
universality certificate `hfact` classifies the Hecke-side
deformations by maps out of `Runiv`, identifying `ψ` with the
classifying map on Frobenius traces (Carayol's argument pins any
trace-compatible map, which is how `hψ`, `hψalg`, `hψπ` enter); a
pigeonhole over the finitely many isomorphism types of each finite
level (or an ultrafilter, as in `FLT/Patching/Ultraproduct.lean`)
extracts a compatible subtower whose inverse limit is the
`PatchedModule`: `M_∞` finite over `R_∞` with the `(p, S₁, …, S_q)`
regular sequence, `R_∞ ↠ R_univ` the patching surjection, and the
bottom identification `M_∞/𝔞M_∞ ≅ M₀` intertwining the actions
through `ψ`.

PROOF (glue, 2026-07-24): the construction is cut at the
`TaylorWilesSystem` interface above — `exists_taylorWilesSystem`
(leaf 2a) supplies the tower of finite-level data, and
`TaylorWilesSystem.exists_patchedModule` (leaf 2b, the vendoring
target for the FLT project's abstract patching development) extracts
the limit object; the glue below additionally derives the residual
finiteness of `Runiv` consumed by the extraction from `hπuniv` and
the finiteness of `k` (the kernel of a surjection onto a field is
maximal, hence THE maximal ideal of the local `Runiv`).

Both-ways audit: at the intended instantiation (`Runiv` the genuine
universal ring, `T = 𝕋_𝔪`, `M₀ = H¹(X₀(N), ℤ_p)_𝔪`) this is the cited
construction; abstractly the hypothesis set contains the classically
unsatisfiable irreducible hardly ramified `ρbar` (section audit of
`Interface.lean`), so the statement is also classically true outright.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it. -/
theorem exists_patchedModule.{v, w, s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hTW : ∀ n r : ℕ, ∃ Q : Finset ℕ,
      r ≤ Q.card ∧ IsTaylorWilesPrimeSet ρbar p n Q) :
    Nonempty (PatchedModule.{v, w, s, uR} p ψ) := by
  have hres : Finite (Runiv ⧸ IsLocalRing.maximalIdeal Runiv) := by
    have hker : RingHom.ker πuniv = IsLocalRing.maximalIdeal Runiv :=
      IsLocalRing.eq_maximalIdeal
        (RingHom.ker_isMaximal_of_surjective πuniv hπuniv)
    rw [← hker]
    exact Finite.of_equiv k
      (RingHom.quotientKerEquivOfSurjective hπuniv).symm.toEquiv
  obtain ⟨S⟩ := exists_taylorWilesSystem hpodd hW hρbar hirr hadic
    hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred ψ
    hψalg hψπ hψ hTW
  exact S.exists_patchedModule hcomplete hres

/-- **Taylor–Wiles patching: `R = 𝕋`, the injectivity half** (pillar
3b-iii; ASSEMBLED 2026-07-24 from the three patching leaves above —
the mathematical heart of the modularity-lifting
theorem): a ring homomorphism `ψ` from a WEAKLY UNIVERSAL
Mazur-category deformation `(Runiv, ρuniv, πuniv)` of the irreducible
residual `ρbar` to a Hecke-side hardly ramified deformation
`(T, ρT, π)`, compatible with the `ℤ_p`-structures, the reduction
maps, and the Frobenius traces away from a finite set, is INJECTIVE.

Classical route, at the intended instantiation (`Runiv` the genuine
universal ring of the hardly ramified problem, `T = 𝕋_𝔪`): the hardly
ramified conditions are the deformation conditions of the
Taylor–Wiles setting with the flat condition at `p` and the tame
condition at `2` ("`S`-good" with `S = {2}` in the FLT blueprint,
ch. 4), and the classifying map `R_univ → 𝕋_𝔪` — which is what `ψ`
is: trace compatibility pins `ψ` on the closed subalgebra
topologically generated by the traces, which is all of `R_univ` by
Carayol's theorem, so any compatible `ψ` IS the classifying map — is
an isomorphism by the Taylor–Wiles patching argument: auxiliary sets
`Q_n` of Taylor–Wiles primes (`q ≡ 1 mod p^n`, Frobenius with
distinct eigenvalues, produced by Chebotarev from the residual
irreducibility, using `p > 2`), the associated augmented deformation
rings and Hecke modules patched to a power-series situation where a
commutative-algebra dimension count forces `R_∞ = 𝕋_∞`, which
descends to `R_univ = 𝕋_𝔪`.  Literature: Wiles, *Modular elliptic
curves and Fermat's Last Theorem*, Ann. of Math. 141 (1995), ch. 3
(the numerical criterion) and ch. 2 §3; Taylor–Wiles,
*Ring-theoretic properties of certain Hecke algebras*, ibid. (the
patching input); Diamond, *The Taylor–Wiles construction and
multiplicity one*, Invent. Math. 128 (1997) (removing multiplicity
one); Conrad–Diamond–Taylor, JAMS 12 (1999), and Kisin, *Moduli of
finite flat group schemes, and modularity*, Ann. of Math. 170 (2009)
(the flat-at-`p` refinements matching the `IsFlatAt` condition);
Diamond–Darmon–Taylor (1995) §5 for the assembled exposition.

The weak-universality hypothesis `hfact` is the universality
certificate that identifies `ψ` with the classifying map — it is what
distinguishes the genuine `R_univ` from an arbitrary deformation ring
(for a non-universal `Runiv` the injectivity claim would have no
classical content).  Both-ways audit: at the intended packet the
statement is verbatim `R = 𝕋`; abstractly (a weakly universal package
that is not the genuine universal ring, a Hecke packet smaller than
`𝕋_𝔪`) it is covered by the section audit of `Interface.lean` (the
hypothesis set contains the classically unsatisfiable irreducible
hardly ramified `ρbar`).  CIRCULARITY GUARD: must not be proven
through `Family.lean` or anything downstream of it. -/
theorem injective_ringHom_of_isWeaklyUniversal.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [TopologicalSpace Runiv]
    [IsTopologicalRing Runiv] [IsLocalRing Runiv] [Algebra ℤ_[p] Runiv]
    [IsNoetherianRing Runiv]
    (hadic : IsAdic (IsLocalRing.maximalIdeal Runiv))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv)
    {ρuniv : GaloisRep ℚ Runiv (Fin 2 → Runiv)}
    (hranku : Module.rank Runiv (Fin 2 → Runiv) = 2)
    (hρuniv : IsHardlyRamified hpodd hranku ρuniv)
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    {Suniv : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hunivred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      πuniv ((ρuniv.charFrob
          hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hfact : IsWeaklyUniversalDeformation.{s, t, uK, uW, uR} hpodd ρbar
      ρuniv πuniv)
    {T : Type s} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [Algebra ℤ_[p] T] [IsLocalRing T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] [IsModuleTopology ℤ_[p] T]
    {ρT : GaloisRep ℚ T (Fin 2 → T)}
    (hrankT : Module.rank T (Fin 2 → T) = 2)
    (hρT : IsHardlyRamified hpodd hrankT ρT)
    {π : T →+* k} (hπ : Function.Surjective π)
    {S_T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hred : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S_T →
      π ((ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (ψ : Runiv →+* T)
    (hψalg : ψ.comp (algebraMap ℤ_[p] Runiv) = algebraMap ℤ_[p] T)
    (hψπ : π.comp ψ = πuniv)
    {Sψ : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))}
    (hψ : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sψ →
      ψ ((ρuniv.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρT.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    Function.Injective ψ := by
  obtain ⟨P⟩ :=
    exists_patchedModule.{uR, s, s, t, uK, uW, uR} hpodd hW hρbar hirr hadic
      hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred ψ hψalg
      hψπ hψ (exists_taylorWilesPrimeSet hpodd hW hρbar hirr)
  exact P.injective

end GaloisRepresentation.Modularity
