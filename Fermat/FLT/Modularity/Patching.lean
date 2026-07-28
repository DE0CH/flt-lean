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

-- Was reached transitively through `ModThree.lean`'s `public import` of it until
-- 2026-07-27, when that edge was removed to take `MazurTorsion` off the critical
-- path (see `GaloisRepresentation/SubQuotCharacter.lean`).  Named explicitly here.
public import Fermat.FLT.FreyCurve.MazurTorsion
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- BUILD REPAIR (2026-07-26). This module was a HARD ERROR — 101 errors, the
-- `maxErrors` cap — which made every consumer of `Modularity/Interface.lean`
-- unbuildable, and which no sorry scan can see. Two independent causes:
-- (1) `Ideal.ramificationIdx_le_finrank`, used by the discriminant bound of
--     `exists_discr_factorization_le_of_finrank_le`, was not imported;
-- (2) the three `open IsLocalRing` below sit inside
--     `namespace GaloisRepresentation.Modularity`, and
--     `PatchingVendored/AdicTopology.lean` declares a namespace `IsLocalRing`
--     INSIDE that same namespace — so `open IsLocalRing` opened
--     `GaloisRepresentation.Modularity.IsLocalRing` and SHADOWED the root
--     one, making `maximalIdeal`, `ResidueField`, `local_hom_TFAE`,
--     `jacobson_eq_maximalIdeal`, … all unknown. They are now
--     `open _root_.IsLocalRing`.
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
-- `MvPowerSeries.instIsAdicComplete`: `O[[x_1,…,x_q]]` is complete for
-- the ideal of variables when there are finitely many of them.  This is
-- the whole limit half of `surjective_of_span_range_eq_maximalIdeal`
-- (complete Nakayama).  The module was ALREADY in this file's transitive
-- closure, so the import adds nothing to the cone — but it was reachable
-- only privately, so the instance was invisible here: a scratch module
-- importing `Patching` synthesised it while `Patching` itself could not.
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
public import Mathlib.LinearAlgebra.TensorProduct.Prod
-- `TensorProduct.prodRight`, the base-change identification
-- `B ⊗[R] (R × R) ≃ B × B` used by `isSplitTorusAt_baseChange` (the
-- split-torus clause of the raised-level condition)
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
-- `Ideal.ramificationIdx_le_finrank` (used in the different-ideal bound) and
-- `IsLocalRing.maximalIdeal` (the `p`-adic tower) were both reached only
-- transitively, hence not re-exported; both are used here directly.
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
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
-- the Hermite–Minkowski chain — `finite_setOf_isHardlyRamified` and the
-- `InertiaTrivialAt` / `finite_setOf_intermediateField_inertiaAt_le` /
-- `finite_setOf_subgroup_inertiaAt_le` / `finite_setOf_galoisRep_isUnramifiedAt`
-- decomposition below it. This block used to live in THIS file; it was
-- lifted out on 2026-07-25 because
-- `GaloisRepresentation/HardlyRamified/Deformation.lean` needs the very
-- same statement as its Schlessinger H3 stratum and cannot import this
-- file (this file imports `KhareWintenberger.lean`, which consumes
-- pillar α — the cycle `Deformation.lean`'s circularity guard forbids).
-- The chain uses nothing from Khare–Wintenberger, so it belongs upstream
-- of both consumers. Every reference here is unqualified and resolves
-- outward from `namespace GaloisRepresentation.Modularity` to
-- `GaloisRepresentation.*`, so nothing else in this file changed.
import Fermat.FLT.GaloisRepresentation.HardlyRamified.HermiteMinkowski
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- `IsDedekindDomain.HeightOneSpectrum.intValuation` and its
-- `WithZero.exp`-valued API, the `Q`-adic order used in the wild
-- different-exponent bound `differentIdeal_exponent_le_wild`
public import Mathlib.NumberTheory.RamificationInertia.Basic
-- `Ideal.ramificationIdx_le_finrank`, consumed by
-- `exists_discr_factorization_le_of_finrank_le`.  Explicit and PUBLIC
-- because as of 2026-07-26 it no longer arrives transitively as a
-- public name: the module system re-exports only public imports, and
-- the intermediate module that used to carry it now imports it
-- privately, which made the constant unknown here.
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
-- `IsLocalRing.maximalIdeal`, `IsLocalRing.ResidueField`,
-- `IsLocalRing.jacobson_eq_maximalIdeal`,
-- `IsLocalRing.map_maximalIdeal_of_surjective`,
-- `IsLocalRing.local_hom_TFAE`: the `open IsLocalRing` of section
-- `ProfinitePadicTower` below opens a namespace whose members were
-- reaching this file only through private imports, so every use read
-- as `Unknown identifier maximalIdeal`.  Same remedy as above.
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
-- `PatchedModule`, the Auslander–Buchsbaum development
-- (`free_of_isRegular_mvPowerSeries` and everything it is built from) and
-- `PatchedModule.injective`. These lived in THIS file until 2026-07-26 and
-- were hoisted VERBATIM into their own module because they mention no base
-- field, and the `R_F = T_F` theorem over a totally real field
-- (`HardlyRamified/HilbertModularity.lean`) needs exactly them — while being
-- UPSTREAM of this file, so it cannot import here. See that module's header.
public import Fermat.FLT.Modularity.PatchingCore
-- `IsLocalRing.maximalIdeal` / `IsLocalRing.ResidueField` and the local-hom
-- API, and `Ideal.ramificationIdx_le_finrank`. Both were reaching this file
-- only through the pre-module-system import leak of `PatchingVendored/`;
-- once that cluster became `module`s, names used in the bodies of this
-- file's `@[expose] public section` declarations must come from a PUBLIC
-- import here. Named explicitly (2026-07-26).
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
-- the vendored FLT abstract patching development (`PatchingAlgebra`,
-- `PatchingModule`, `quotientToOver`, `quotientEquivOver`, `smulData`,
-- `smul_lemma`), instantiated by `exists_patchedModule_of_fields` below
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
-- the scoped product topology on `MvPowerSeries`, in which
-- `Λ = ℤ_p[[x₁, …, x_q]]` is profinite (hence `IsAdicTopology` is free)
public import Mathlib.RingTheory.MvPowerSeries.Inverse
-- `IsLocalRing (MvPowerSeries σ R)` for a local coefficient ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- the finite-dimensional descent of `exists_taylorWilesPrimeSet_core`:
-- `Submodule.finiteDimensional_of_le`, `Submodule.finrank_lt_finrank_of_lt`,
-- `Submodule.finrank_eq_zero`, `Submodule.finrank_mono`.  PUBLIC because
-- they are used in the bodies of declarations inside this file's
-- `@[expose] public section`, where synthesis and name resolution range
-- over the PUBLIC import closure only.  Cone growth is nil:
-- `HardlyRamified/Deformation.lean`, already a `public import` below,
-- carries `Mathlib.LinearAlgebra.FiniteDimensional.Basic` and the
-- `Dimension` files under it.
public import Mathlib.RingTheory.Regular.Flat
-- `IsWeaklyRegular.isWeaklyRegular_rTensor`: a `Λ`-regular sequence is
-- `M`-regular for flat (in particular free) `M`
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Connected.TotallyDisconnected
-- proof-only, and easy to miss: without these two the route
-- `IsUltrametricDist ℤ_[p] → TotallySeparatedSpace → TotallyDisconnectedSpace`
-- is unavailable and `TotallyDisconnectedSpace ℤ_[p]` fails to synthesize
-- with no hint of the cause
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Deformation
-- ADDED 2026-07-28 by the decomposition of
-- `exists_taylorWilesPrime_locResDecomp_ne_zero` (DDT Lemma 2.48): the
-- INHOMOGENEOUS description of degree-one continuous cohomology, without
-- which a cohomology class cannot be evaluated at a Galois element and the
-- separating locus of DDT 2.48 cannot be written down at all.  `public`
-- because `survivingLocus` below mentions `ContinuousCohomology.eval₁` in
-- SIGNATURE position.
public import Fermat.FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegreeOne
-- PROMOTED TO `public import` 2026-07-27 by the `IsTaylorWilesPrimeSet`
-- dual-Selmer repair: that predicate's global clause is stated in the
-- Galois-cohomology vocabulary of this module (`adZeroTwist`,
-- `locResTwist1`, `hardlyRamifiedPlaces`), and a plain `import` does not
-- re-export, so the names would be unavailable in signature position.
-- No cycle: the import closure of `HardlyRamified/Deformation.lean`
-- contains no `Modularity/*` (re-checked 2026-07-27).
-- PROOF-ONLY (added 2026-07-25 for the quotient-tower leaf
-- `exists_ringHom_quotient_padicTower_of_finiteTests`):
-- `isHardlyRamified_baseChange_quotient`, the transfer of the four hardly
-- ramified conditions along a surjection of coefficient rings, together
-- with its already-proven ingredients `isFlatAt_baseChange_quotient`
-- (Ramakrishna's flat condition, the only deep one) and
-- `isTameAtTwo_baseChange`.  This module was ALREADY in this file's
-- transitive import cone through `Modularity/KhareWintenberger.lean`; the
-- import is made direct because a private import is not transitive.  The
-- circularity guard is respected: the import closure of
-- `HardlyRamified/Deformation.lean` contains no `Modularity/*`, no
-- `Family.lean` and no `Lift.lean` (checked 2026-07-25).

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
/-- **The determinant pins the constant `charFrob` coefficient** (PROVEN;
GENERALISED 2026-07-28 out of `coeff_zero_charFrob_eq_of_isHardlyRamified`
below, which is now one line over it).

At every finite place `v` the constant coefficient of `charFrob` — which is
`(-1)² · det = det` of the Frobenius endomorphism on the rank-2 module — is the
image under `algebraMap ℤ_p` of the cyclotomic-character value at the (fixed,
coefficient-ring-independent) global Galois element underlying the arithmetic
Frobenius at `v`.  Hence two representations whose DETERMINANTS are both the
`p`-adic cyclotomic character, linked by a ring homomorphism compatible with the
`ℤ_p`-structures, match constant `charFrob` coefficients EVERYWHERE.

Only the two `det` clauses are used — never `isFlat`, `isTameAtTwo` or
`isUnramified` — which is exactly why this form is worth having separately:
`IsTaylorWilesResidual` (below) carries `det` for `ρbar` WITHOUT the two clauses
that the tree refutes, so the raised-level leaf
`exists_auxDeformationDatum` can pin its constant coefficients without ever
holding `IsHardlyRamified hpodd hW ρbar` — which its CIRCULARITY GUARD bans. -/
lemma coeff_zero_charFrob_eq_of_det_eq {p : ℕ}
    [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hdim : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρdet : ∀ g, ρ.det g = algebraMap ℤ_[p] R
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv))
    {k : Type*} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    [IsLocalRing k] [Algebra ℤ_[p] k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbardet : ∀ g, ρbar.det g = algebraMap ℤ_[p] k
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv))
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
    ← GaloisRep.det_apply, ← GaloisRep.det_apply, hρdet, hρbardet,
    ← RingHom.comp_apply, hf]

set_option backward.isDefEq.respectTransparency false in
/-- **The determinant pins the constant `charFrob` coefficient of a
hardly ramified representation** (PROVEN): the `IsHardlyRamified` special case
of `coeff_zero_charFrob_eq_of_det_eq` above, in the transported
two-representation form the Mazur-representability assembly consumes.  This is
the trace-determines-`charFrob` audit point of the module docstring. -/
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
    f ((ρ.charFrob v).coeff 0) = (ρbar.charFrob v).coeff 0 :=
  coeff_zero_charFrob_eq_of_det_eq hdim hρ.det hW hρbar.det f hf v

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

-- The `Modularity` copy of `rank_finTwoFun` used to be declared HERE. It
-- was deleted on 2026-07-25 in favour of the single
-- `GaloisRepresentation.rank_finTwoFun` in `HardlyRamified/Defs.lean`,
-- which this file already imports; the uses below are unqualified and
-- resolve outward from `namespace GaloisRepresentation.Modularity`, so
-- they are unchanged. The move was forced by the lifted
-- `HardlyRamified/HermiteMinkowski.lean`, which is upstream of both
-- former copies and could reach neither.

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
2026-07-25 over the wild different-exponent bound
`differentIdeal_exponent_le_wild`, itself PROVEN 2026-07-26 over the
local Eisenstein leaf `exists_eisensteinDerivative_dvd_of_wild`);
everything else —
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

open _root_.IsLocalRing

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

/-- **Conjugation composes** (PROVEN 2026-07-25): conjugating a Galois
representation by `e₁` and then by `e₂` is conjugating it by
`e₁.trans e₂`.  Both sides evaluate to `e₂ ∘ e₁ ∘ ρ σ ∘ e₁.symm ∘ e₂.symm`
definitionally, so the proof is `rfl` after `GaloisRep.conj_apply`.

(`GaloisRep.conj_trans` in `HardlyRamified/Deformation.lean` is the same
statement carrying `Module.Finite`/`Module.Free` hypotheses on all three
spaces, which the tensor products of the residual-identification
transport below would force one to synthesize for no reason; this
hypothesis-free form is stated here rather than generalizing the other
copy, since that copy is under an active owner.  Whoever unifies them
should keep THIS statement.) -/
lemma conj_trans {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (ρ : GaloisRep ℚ A M) (e₁ : M ≃ₗ[A] N) (e₂ : N ≃ₗ[A] P) :
    (ρ.conj e₁).conj e₂ = ρ.conj (e₁.trans e₂) := by
  refine GaloisRep.ext fun σ => LinearMap.ext fun x => ?_
  rw [GaloisRep.conj_apply, GaloisRep.conj_apply, GaloisRep.conj_apply]
  rfl

open scoped TensorProduct in
/-- **An intermediate base change cancels** (PROVEN 2026-07-25): for a
tower `A → B → kk` of topological algebras, the double base change
`kk ⊗_B (B ⊗_A M)` of `ρ` is, through the canonical cancellation
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, the single base
change `kk ⊗_A M` — as GALOIS REPRESENTATIONS, not merely as modules.

Checked on pure tensors, where both sides send `c ⊗ (1 ⊗ m)` to
`c ⊗ ρ σ m` (`cancelBaseChange` multiplies the middle coefficient into
`c`, and here it is `1`).  This is what transports a residual
identification along a quotient of the coefficient ring: the
identification of `D` lives on `k ⊗_A Vd`, while the base-changed
deformation's lives on `k ⊗_{A/I} ((A/I) ⊗_A Vd)`. -/
lemma baseChange_baseChange_conj_cancel
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra A B] [ContinuousSMul A B]
    {kk : Type*} [CommRing kk] [TopologicalSpace kk] [IsTopologicalRing kk]
    [Algebra A kk] [Algebra B kk] [IsScalarTower A B kk]
    [ContinuousSMul A kk] [ContinuousSMul B kk]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free A M] (ρ : GaloisRep ℚ A M) :
    ((ρ.baseChange B).baseChange kk).conj
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A B kk kk M) =
      ρ.baseChange kk := by
  refine GaloisRep.ext fun σ => LinearMap.ext fun x => ?_
  rw [GaloisRep.conj_apply, LinearEquiv.conj_apply_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        GaloisRep.baseChange_tmul, GaloisRep.baseChange_tmul,
        GaloisRep.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Quotient-tower classifying maps** (PROVEN 2026-07-25 — with it the
pro-finite upgrade `isWeaklyUniversalOnIdentifiedDeformation_of_finiteTests`
below, whose
other three strata — finiteness of the classifying sets, König, and
the `p`-adic assembly with its clause passage — were already proven over the
tower vocabulary above, is complete): the finite-tests universality of
`(Runiv, ρuniv, πuniv)` produces a classifying map at every level of
the `p`-adic tower of a residually identified test deformation `D`,
compatible with the `ℤ_p`-structures, with the level-`n` reduction map
`A/pⁿ⁺¹A →+* k` induced by `D.π`, and with the linear `charFrob`
coefficients at EVERY prime.

Proof (step (1) of the upgrade's docstring, QUOTIENT TOWER, together
with the nonemptiness half of step (2)): base-change `D` along the
surjection `D.A ↠ D.A/pⁿ⁺¹D.A` onto a FINITE local `ℤ_p`-algebra
(finite by `finite_quotient_padicTowerIdeal`, local by
`isLocalRing_quotient_padicTowerIdeal`) and feed the resulting Artinian
test deformation `Dₙ` to `h`.  Its three clauses are literally the three
clauses below, once `Dₙ.ρ = D.ρ ⊗ (D.A/pⁿ⁺¹)`'s `charFrob` is computed
by `charFrob_baseChange` (`Polynomial.coeff_map` and
`Ideal.Quotient.algebraMap_eq` turn the third clause into the asserted
`Ideal.Quotient.mk`), and `Dₙ.π := Ideal.Quotient.lift _ D.π hker` is
definitionally the map named in the statement.

WHAT THE PROOF ACTUALLY DOES, where it differs from the sketch this
docstring used to carry.

* TOPOLOGY.  The level ring carries the QUOTIENT topology
  (`topologicalRingQuotientTopology`), not an asserted discrete one: it
  is again the `ℤ_p`-module topology because the module topology
  pushes forward along a surjective linear map
  (`ModuleTopology.eq_coinduced_of_surjective` applied to
  `Ideal.Quotient.mkₐ ℤ_[p] _`, which is exactly how mathlib's
  `IsModuleTopology.instQuot` handles a submodule quotient — that
  instance does not apply verbatim, the ideal quotient and the
  `ℤ_p`-submodule quotient being different `HasQuotient` instances).
  Discreteness is TRUE here but never needed, so it is not proven; what
  the structure demands is `IsModuleTopology`, and continuity of the
  level reduction map then comes from
  `continuous_ringHom_of_isModuleTopology` rather than from
  `continuous_of_discreteTopology`.
* HARDLY RAMIFIED CLAUSES.  All four transfer in ONE step, by the
  imported `GaloisRepresentation.isHardlyRamified_baseChange_quotient`
  (`HardlyRamified/Deformation.lean`) — determinant by
  `LinearMap.det_baseChange`, unramifiedness by the base-change instance
  of `GaloisRep.IsUnramifiedAt`, tameness at `2` by
  `isTameAtTwo_baseChange`, and flatness at `p` by the PROVEN
  `isFlatAt_baseChange_quotient` (open ideals of the quotient pull back
  to open ideals of `D.A`, and the double base change collapses by
  tensor cancellation).  Note this is the QUOTIENT transfer, which is
  sorry-free; the general-coefficient-map transfer
  `isHardlyRamified_baseChange` in the same module rests on the open
  Raynaud leaf `hasFlatProlongationAt_of_pi_surjection` and is NOT used.
  That module was already in this file's import cone through
  `Modularity/KhareWintenberger.lean`; only the directness of the import
  is new.
* RESIDUAL IDENTIFICATION.  `Dₙ`'s identification is `D`'s composed with
  the tensor cancellation
  `k ⊗_{A/pⁿ⁺¹A} ((A/pⁿ⁺¹A) ⊗_A Vd) ≅ k ⊗_A Vd`, which is equivariant by
  `baseChange_baseChange_conj_cancel` above; `conj_trans` then collapses
  the two conjugations into one.  The scalar tower
  `IsScalarTower D.A (D.A/pⁿ⁺¹) k` needed to form the cancellation is
  `Ideal.Quotient.lift_mk`, i.e. `rfl`.

Both-ways audit: a base-change statement about abstract packages, with
no arithmetic content beyond that of the finite-tests hypothesis it
consumes; classically true outright as stated.  CIRCULARITY GUARD
(inherited, and RE-CHECKED at the new import 2026-07-25): must not be
proven through `Family.lean` or anything downstream of it (`Lift.lean`
included) — the import closure of `HardlyRamified/Deformation.lean`
contains neither, nor any `Modularity/*`. -/
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
                ((D.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) := by
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
  intro hker
  -- the level-`n` coefficient ring: a finite local `ℤ_p`-algebra whose
  -- QUOTIENT topology is again the `ℤ_p`-module topology
  haveI : Module.Finite ℤ_[p] (D.A ⧸ padicTowerIdeal p D.A n) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : IsModuleTopology ℤ_[p] (D.A ⧸ padicTowerIdeal p D.A n) := by
    constructor
    rw [ModuleTopology.eq_coinduced_of_surjective
      (φ := (Ideal.Quotient.mkₐ ℤ_[p] (padicTowerIdeal p D.A n)).toLinearMap)
      Ideal.Quotient.mk_surjective]
    rfl
  have hrank : Module.rank (D.A ⧸ padicTowerIdeal p D.A n)
      ((D.A ⧸ padicTowerIdeal p D.A n) ⊗[D.A] D.Vd) = 2 := by
    rw [Module.rank_baseChange, D.rank_eq]
    simp
  set πn : (D.A ⧸ padicTowerIdeal p D.A n) →+* k :=
    Ideal.Quotient.lift (padicTowerIdeal p D.A n) D.π hker
  have hπnmk : ∀ a : D.A, πn (Ideal.Quotient.mk _ a) = D.π a := fun _ => rfl
  -- the level-`n` test deformation: `D` base-changed to the tower quotient
  let Dn : HardlyRamifiedFiniteDeformation.{s, s, uK, uW} hpodd ρbar :=
    { A := D.A ⧸ padicTowerIdeal p D.A n
      Vd := (D.A ⧸ padicTowerIdeal p D.A n) ⊗[D.A] D.Vd
      rank_eq := hrank
      ρ := D.ρ.baseChange (D.A ⧸ padicTowerIdeal p D.A n)
      isHardlyRamified := isHardlyRamified_baseChange_quotient hpodd
        (padicTowerIdeal p D.A n) hrank D.isHardlyRamified
      π := πn
      π_surjective := fun y => by
        obtain ⟨a, ha⟩ := D.π_surjective y
        exact ⟨Ideal.Quotient.mk _ a, by rw [hπnmk]; exact ha⟩
      S := D.S
      charFrob_compat := by
        intro q hq hqS
        rw [charFrob_baseChange, Polynomial.coeff_map,
          Ideal.Quotient.algebraMap_eq, hπnmk]
        exact D.charFrob_compat q hq hqS }
  have hfin : Finite Dn.A :=
    inferInstanceAs (Finite (D.A ⧸ padicTowerIdeal p D.A n))
  -- its residual identification is `D`'s, moved along the tensor cancellation
  have hid : Dn.IsResidualIdentified := by
    letI : Algebra D.A k := D.π.toAlgebra
    letI : ContinuousSMul D.A k := continuousSMul_of_algebraMap D.A k
      (by rw [RingHom.algebraMap_toAlgebra]; exact D.continuous_pi)
    letI : Algebra (D.A ⧸ padicTowerIdeal p D.A n) k := πn.toAlgebra
    letI : ContinuousSMul (D.A ⧸ padicTowerIdeal p D.A n) k :=
      continuousSMul_of_algebraMap _ k
        (by
          rw [RingHom.algebraMap_toAlgebra]
          exact continuous_ringHom_of_isModuleTopology (p := p) πn)
    haveI : IsScalarTower D.A (D.A ⧸ padicTowerIdeal p D.A n) k :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨e₀, he₀⟩ := hDid
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange D.A
        (D.A ⧸ padicTowerIdeal p D.A n) k k D.Vd).trans e₀, ?_⟩
    rw [← conj_trans, baseChange_baseChange_conj_cancel]
    exact he₀
  -- the finite-tests hypothesis at `Dn` is the conclusion
  obtain ⟨ψ, h1, h2, h3⟩ := h Dn hfin hid
  refine ⟨ψ, h1, h2, fun q hq => ?_⟩
  rw [h3 q hq]
  show ((D.ρ.baseChange (D.A ⧸ padicTowerIdeal p D.A n)).charFrob
    hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 = _
  rw [charFrob_baseChange, Polynomial.coeff_map, Ideal.Quotient.algebraMap_eq]

/-- **Pro-finite limit upgrade** (PROVEN 2026-07-25, and SORRY-FREE
since its quotient-tower leaf
`exists_ringHom_quotient_padicTower_of_finiteTests` was proven the same
day — the limit stratum of the strict Mazur core, after the LEVEL cut of
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

(1) QUOTIENT TOWER (PROVEN,
`exists_ringHom_quotient_padicTower_of_finiteTests`): base-changing `D`
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
(itself PROVEN 2026-07-25, together with its quotient-tower leaf
`exists_ringHom_quotient_padicTower_of_finiteTests`: König finiteness
of the classifying sets, the `p`-adic assembly, and the level-wise
base change are all proven there)): GIVEN the finiteness of the dual-number tangent space
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

/-! ### The dual-Selmer vocabulary for `IsTaylorWilesPrimeSet`

Three short definitions, added 2026-07-27 as the CUT-LEVEL repair of the
interface defect recorded at `exists_taylorWilesAuxLevelPresentedDatum`
below: `IsTaylorWilesPrimeSet` was a conjunction of purely LOCAL
conditions, so it admitted prime sets for which the Taylor–Wiles method
does not work and the arithmetic leaves were quantified over all of them.

Everything the global clause needs already exists in
`HardlyRamified/Deformation.lean` (`adZeroTwist = ad⁰ρbar(1)`,
`adZeroTwistLocal`, `locResTwist1`, `hardlyRamifiedPlaces`, all
sorry-free); the ONLY thing missing was the *unramified at `v`*
condition, which is restriction along the inertia subgroup rather than
along the whole decomposition group.  That is what the three definitions
below supply, mirroring `adZeroLocal`/`locResTwist1` verbatim with
`decompHom v` replaced by its restriction to `localInertiaGroup v`.

**Why the unramifiedness clause is not optional.**  `Sha1Twist (S ∪ Q) = 0`
alone is unachievable over the full `Γ ℚ`: a class ramified at some large
auxiliary prime outside `S ∪ Q` is invisible to every localisation in the
family, so the source is infinite-dimensional and no finite `Q` can cut it
to zero.  (This is the phenomenon audited at length on `Sha1Twist` itself;
the `μ_ℓ` shadow is `H¹(Γ ℚ, μ_ℓ) ≅ ℚˣ/(ℚˣ)^ℓ`, infinite, against the
`S`-unit group of dimension 2 over `G_{ℚ,S}`.)  Restricting to classes
UNRAMIFIED OUTSIDE `{2, p}` is what replaces the missing `G_{ℚ,S}` here,
and it is statable today precisely because `localInertiaGroup` exists.

**The local Tate pairing is NOT needed.**  The classical clause is
`H¹_{Q*}(ℚ, ad⁰ρbar(1)) = 0`, whose `Q*` condition at `q ∈ Q` is the
ANNIHILATOR of the unramified local condition under the local pairing.
The clause written below drops the pairing and asks for the FULL local
restriction to vanish at each `q ∈ Q`, which is a SMALLER (indeed empty
at each `q`) local condition, hence a LARGER kernel: the group it kills
CONTAINS `H¹_{Q*}`.  So the clause is stronger than the classical one and
therefore sufficient for every consumer, while needing no duality theory
at all. -/

/-- **Inertia at `v` inside the global Galois group** — the composite
`I_v ↪ Γ ℚ_v → Γ ℚ` of the inclusion of `localInertiaGroup v` with
`decompHom v`, as a continuous group homomorphism.  Continuity of the
inclusion is `continuous_subtype_val`; `decompHom` is already continuous
by construction. -/
noncomputable def inertiaToGlobalHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ↥(localInertiaGroup v) →ₜ* Field.absoluteGaloisGroup ℚ :=
  (decompHom v).comp ⟨(localInertiaGroup v).subtype, continuous_subtype_val⟩

/-- `ad⁰ρbar(1)` restricted to the INERTIA group at `v` — the analogue of
`adZeroTwistLocal` along `inertiaToGlobalHom v` instead of
`decompHom v`. -/
noncomputable def adZeroTwistInertia.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    TopRep k ↥(localInertiaGroup v) :=
  TopRep.res (inertiaToGlobalHom v).toMonoidHom (adZeroTwist p ρbar)

/-- The restriction `H¹(ℚ, ad⁰ρbar(1)) → H¹(I_v, ad⁰ρbar(1))`.  A class in
its kernel is exactly a class UNRAMIFIED at `v`; that is the notion the
global clause of `IsTaylorWilesPrimeSet` below quantifies over. -/
noncomputable def locResInertiaTwist1.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    continuousCohomology 1 (adZeroTwist p ρbar) ⟶
      continuousCohomology 1 (adZeroTwistInertia p ρbar v) :=
  ContinuousCohomology.map (inertiaToGlobalHom v)
    (CategoryTheory.CategoryStruct.id (adZeroTwistInertia p ρbar v)) 1

/-- `ad⁰ρbar(1)` restricted to the DECOMPOSITION group at `v` — the analogue of
`adZeroTwistInertia` along `decompHom v` instead of `inertiaToGlobalHom v`.

INTEGRATION NOTE (2026-07-27).  The clause below used to call
`Deformation.lean`'s `locResTwist1`, which has since been RESTATED over
`G_{ℚ,S}`: it now takes the ramification set `S` and lives on
`adZeroTwistRestricted`, not on `adZeroTwist`.  That restatement is correct and
is not undone here — but this file deliberately works over the FULL `Γ ℚ` (see
the subsection docstring above: "restricting to classes unramified outside
`{2, p}` is what replaces the missing `G_{ℚ,S}` here"), so the right repair is
to give this file its own `Γ ℚ`-level decomposition restriction rather than to
thread an `S` it does not have.  These two definitions are the exact analogues
of `adZeroTwistInertia` / `locResInertiaTwist1` immediately above, with the
decomposition group in place of inertia. -/
noncomputable def adZeroTwistDecomp.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    TopRep k (Field.absoluteGaloisGroup
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
  TopRep.res (decompHom v).toMonoidHom (adZeroTwist p ρbar)

/-- The restriction `H¹(ℚ, ad⁰ρbar(1)) → H¹(ℚ_v, ad⁰ρbar(1))` — the FULL local
restriction the dual-Selmer clause of `IsTaylorWilesPrimeSet` asks to vanish at
each `q ∈ Q`. -/
noncomputable def locResDecompTwist1.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    continuousCohomology 1 (adZeroTwist p ρbar) ⟶
      continuousCohomology 1 (adZeroTwistDecomp p ρbar v) :=
  ContinuousCohomology.map (decompHom v)
    (CategoryTheory.CategoryStruct.id (adZeroTwistDecomp p ρbar v)) 1

/-- **The source of the dual-Selmer clause, as a submodule** (ADDED
2026-07-27 by the decomposition of `exists_taylorWilesPrimeSet`'s core):
the classes in `H¹(ℚ, ad⁰ρbar(1))` that are UNRAMIFIED OUTSIDE `{2, p}`,
i.e. that die under restriction to the inertia group at every place off
`hardlyRamifiedPlaces p`.

This is the same condition the global clause of `IsTaylorWilesPrimeSet`
below states pointwise; packaging it as a `Submodule` is what makes the
Taylor–Wiles descent (`exists_taylorWilesPrimeSet_core`) expressible as a
finite-dimensional dimension count, one prime cutting at least one
dimension.  It is canonically `H¹(G_{ℚ,{2,p}}, ad⁰ρbar(1))`: `ad⁰ρbar(1)`
is unramified outside `{2, p}`, so `M^{I_v} = M` off `S` and a class in
the kernel of restriction to `I_v` restricts to `I_v` as an honest ZERO
cocycle rather than merely a coboundary; hence it vanishes on the closed
normal subgroup generated by those inertia groups and inflates from
`G_{ℚ,{2,p}}`.  That identification is what makes
`finite_h1TwistUnramified` below TRUE and is its intended route. -/
noncomputable def h1TwistUnramified.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) :
    Submodule k (continuousCohomology 1 (adZeroTwist p ρbar)) :=
  ⨅ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
    ⨅ _ : v ∉ hardlyRamifiedPlaces p,
      LinearMap.ker (locResInertiaTwist1 p ρbar v).hom.toLinearMap

/-- **The local conditions imposed at a Taylor–Wiles set, as a
submodule**: the classes in `H¹(ℚ, ad⁰ρbar(1))` killed by the FULL local
restriction at every prime of `Q`.  Written as an intersection of
kernels, verbatim as `Sha1Twist`/`Sha2` in
`HardlyRamified/Deformation.lean`, and for the same reason — same
submodule, no product object to build.

ANTITONE in `Q` (`h1TwistLocalKer_anti` below), which is the shape that
makes the descent terminate: `h1TwistUnramified ⊓ h1TwistLocalKer Q` can
only shrink as primes are adjoined, and the dual-Selmer clause of
`IsTaylorWilesPrimeSet` says exactly that this meet is `⊥`. -/
noncomputable def h1TwistLocalKer.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (Q : Finset ℕ) :
    Submodule k (continuousCohomology 1 (adZeroTwist p ρbar)) :=
  ⨅ q : ℕ, ⨅ _ : q ∈ Q, ⨅ hq : q.Prime,
    LinearMap.ker (locResDecompTwist1 p ρbar
      hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap

section DualSelmerVocabulary

variable {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]

/-- Membership in `h1TwistUnramified` unfolded (PROVEN): it is exactly
the antecedent of the global clause of `IsTaylorWilesPrimeSet`. -/
lemma mem_h1TwistUnramified (ρbar : GaloisRep ℚ k W)
    {c : continuousCohomology 1 (adZeroTwist p ρbar)} :
    c ∈ h1TwistUnramified p ρbar ↔
      ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ hardlyRamifiedPlaces p →
        c ∈ LinearMap.ker (locResInertiaTwist1 p ρbar v).hom.toLinearMap := by
  simp [h1TwistUnramified, Submodule.mem_iInf]

/-- Membership in `h1TwistLocalKer` unfolded (PROVEN). -/
lemma mem_h1TwistLocalKer (ρbar : GaloisRep ℚ k W) (Q : Finset ℕ)
    {c : continuousCohomology 1 (adZeroTwist p ρbar)} :
    c ∈ h1TwistLocalKer p ρbar Q ↔
      ∀ q ∈ Q, ∀ hq : q.Prime,
        c ∈ LinearMap.ker (locResDecompTwist1 p ρbar
          hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap := by
  simp [h1TwistLocalKer, Submodule.mem_iInf]

/-- **`h1TwistLocalKer` is antitone** (PROVEN): adjoining primes imposes
more vanishing, so the submodule can only shrink.  This is the submodule
form of the MONOTONICITY recorded on `IsTaylorWilesPrimeSet` below — the
global clause is monotone INCREASING in `Q` precisely because this meet
is antitone. -/
lemma h1TwistLocalKer_anti (ρbar : GaloisRep ℚ k W) {Q Q' : Finset ℕ}
    (h : Q ⊆ Q') :
    h1TwistLocalKer p ρbar Q' ≤ h1TwistLocalKer p ρbar Q := by
  intro c hc
  rw [mem_h1TwistLocalKer] at hc ⊢
  exact fun q hq => hc q (h hq)

end DualSelmerVocabulary

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
part of the audited hypothesis set).

# THE GLOBAL CLAUSE (ADDED 2026-07-27 — THE CUT-LEVEL REPAIR)

The second conjunct is the DUAL-SELMER VANISHING condition, and without
it this predicate is not the Taylor–Wiles hypothesis at all.  The
Taylor–Wiles construction does not work for an arbitrary set of primes
satisfying the local conditions: it works for a `Q` chosen so that

    H¹_{Q*}(ℚ, ad⁰ρbar(1)) = 0 ,

which by Greenberg–Wiles is exactly what forces
`dim_k H¹_Q(ℚ, ad⁰ρbar) = #Q`, hence what makes the auxiliary
deformation ring `R_Q` generated by `#Q` elements over `𝒪` — i.e. what
makes the presentation `pres` exist at all.  With only the local
conjunct, the arithmetic leaves below were universally quantified over
sets `Q` for which `dim_k H¹_Q > #Q` and for which NO such presentation
exists, so they were STRICTLY STRONGER than the classical theorem and
unreachable by any classical route.  That defect is what this clause
removes; see the INTERFACE REPAIR section of
`exists_taylorWilesAuxLevelPresentedDatum` below for the full history,
including the weaker "thread the supply down" repair that was tried
first and does not suffice (the supply's members are not known to kill
the dual Selmer group, so the freedom it grants is empty).

As written the clause says: every class in `H¹(ℚ, ad⁰ρbar(1))` that is
UNRAMIFIED OUTSIDE `{2, p}` and dies under restriction to every `q ∈ Q`
is zero.  Two deliberate deviations from the classical `H¹_{Q*}`, both
recorded in the section note above and both making the clause STRONGER,
hence safe for every consumer: the local condition imposed at `q ∈ Q` is
the full restriction rather than the annihilator of the unramified
condition under the local Tate pairing (so no duality theory is needed),
and the unramified-outside-`{2, p}` restriction stands in for the
missing `G_{ℚ,S}` (without it the clause is unachievable — see the
section note).

**MONOTONICITY.**  Both conjuncts are monotone in `Q` in the direction
that matters: the local one is a `∀ q ∈ Q` condition and so is
ANTI-monotone, while the global one is MONOTONE INCREASING (a larger `Q`
imposes more vanishing on `c`, so the antecedent is harder and the
implication easier).  Consequently the predicate is preserved by
ENLARGING `Q` with further primes satisfying the local conditions — that
is `IsTaylorWilesPrimeSet.exists_insert` below — and is NOT preserved by
shrinking.  The old proof of `exists_taylorWilesPrimeSet_card_eq`, which
cut a supplied `Q` down to an exact cardinality with
`Finset.exists_subset_card_eq`, is therefore unsound under this
definition and has been removed; that is why the exact-cardinality supply
now carries a lower bound `q0 ≤ r`. -/
def IsTaylorWilesPrimeSet.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) (n : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, ∃ hq : q.Prime,
    q ≡ 1 [MOD p ^ n] ∧
    ∃ α β : k, α ≠ β ∧
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) ∧
  ∀ c : continuousCohomology 1 (adZeroTwist p ρbar),
    (∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ hardlyRamifiedPlaces p →
        c ∈ LinearMap.ker (locResInertiaTwist1 p ρbar v).hom.toLinearMap) →
    (∀ q ∈ Q, ∀ hq : q.Prime,
        c ∈ LinearMap.ker
          (locResDecompTwist1 p ρbar
            hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap) →
    c = 0

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

/-- **Enlarging a Taylor–Wiles set by one prime** (PROVEN 2026-07-27):
given a Taylor–Wiles set `Q` of level `n`, a fresh Taylor–Wiles prime
adjoined to it is again one.  This is the monotonicity recorded in
`IsTaylorWilesPrimeSet`'s docstring, made usable: the local conjunct is
checked at the new prime by `exists_taylorWilesPrime` and inherited on
`Q`, and the global conjunct transfers because the antecedent for
`insert q Q` implies the antecedent for `Q`.

It is what lets the supply leaf below pad a dual-Selmer-killing core of
the level-independent size `q0` up to any exact cardinality `r ≥ q0` —
the direction that *is* sound, as against the shrinking the old
`exists_taylorWilesPrimeSet_card_eq` performed. -/
theorem IsTaylorWilesPrimeSet.exists_insert.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ) {Q : Finset ℕ}
    (hQ : IsTaylorWilesPrimeSet p ρbar n Q) :
    ∃ Q' : Finset ℕ, Q'.card = Q.card + 1 ∧ IsTaylorWilesPrimeSet p ρbar n Q' := by
  classical
  obtain ⟨q, hq, hqS, hqmod, α, β, hαβ, hqpoly⟩ :=
    exists_taylorWilesPrime hpodd hW hρbar hirr n
      (Q.image fun q' =>
        if h : q'.Prime then h.toHeightOneSpectrumRingOfIntegersRat
        else (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat)
  have hqQ : q ∉ Q := fun hmem => hqS (Finset.mem_image.mpr
    ⟨q, hmem, dif_pos hq⟩)
  refine ⟨insert q Q, Finset.card_insert_of_notMem hqQ, ?_, ?_⟩
  · intro q' hq'
    rcases Finset.mem_insert.mp hq' with rfl | hmem
    · exact ⟨hq, hqmod, α, β, hαβ, hqpoly⟩
    · exact hQ.1 q' hmem
  · intro c hunr hloc
    exact hQ.2 c hunr fun q' hq' => hloc q' (Finset.mem_insert_of_mem hq')

/-- **Exact cardinality by padding** (PROVEN 2026-07-27): a Taylor–Wiles
set may be enlarged to ANY prescribed cardinality at or above its own,
one fresh Taylor–Wiles prime at a time.  An immediate induction on `r`
over `IsTaylorWilesPrimeSet.exists_insert`.

This is the ENLARGING direction and the only one the dual-Selmer clause
permits: the global conjunct is monotone INCREASING in `Q`, so the
`Finset.exists_subset_card_eq` shrinking that the pre-2026-07-27
`exists_taylorWilesPrimeSet_card_eq` performed is unsound (see the
history recorded there).  Taking the hypothesis as `Q.card ≤ r` rather
than as an exact size is what lets `exists_taylorWilesPrimeSet_core`
below return a set of size AT MOST the Taylor–Wiles number — which is
all a dimension count can deliver, since a single prime may cut more
than one dimension. -/
theorem IsTaylorWilesPrimeSet.exists_card_eq.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ) :
    ∀ (r : ℕ) (Q : Finset ℕ), IsTaylorWilesPrimeSet p ρbar n Q → Q.card ≤ r →
      ∃ Q' : Finset ℕ, Q'.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q' := by
  intro r
  induction r with
  | zero => exact fun Q hQ hcard => ⟨Q, Nat.le_zero.mp hcard, hQ⟩
  | succ r ih =>
    intro Q hQ hcard
    rcases eq_or_lt_of_le hcard with h | h
    · exact ⟨Q, h, hQ⟩
    · obtain ⟨Q'', hcard'', hQ''⟩ := ih Q hQ (Nat.lt_succ_iff.mp h)
      obtain ⟨Q', hcard', hQ'⟩ :=
        IsTaylorWilesPrimeSet.exists_insert hpodd hW hρbar hirr n hQ''
      exact ⟨Q', by rw [hcard', hcard''], hQ'⟩

/-! #### The Hermite–Minkowski input, in the form `finite_h1TwistUnramified` needs it

Added 2026-07-28 by the decomposition of `finite_h1TwistUnramified` below.

`HardlyRamified/HermiteMinkowski.lean` — which **is** in this file's import
cone, contrary to what the docstring of `finite_h1TwistUnramified` used to say
(the `import` is on the header line above, non-public, which is enough for the
proof bodies here) — proves `finite_setOf_subgroup_inertiaAt_le`: finitely many
open normal subgroups of `Γ ℚ` of bounded index into which the inertia at every
`q ∉ {2, p}` maps.  That is hard-wired to the two-element set `{2, p}`, and the
cut below needs the same statement for an ARBITRARY finite set `T` of rational
primes.

**Why an arbitrary `T`, and not `{2, p}`.**  `finite_h1TwistUnramified` carries
NO hypothesis on `ρbar`, so `ad⁰ρbar(1)` need not be unramified outside
`{2, p}`: the cocycle bookkeeping below cuts out a field `K/ℚ` which is
unramified outside `{2, p} ∪ ram(ρbar)`, and `ram(ρbar)` is finite but not
bounded in advance.  (This is the same phenomenon as the classical proof going
through `L = ℚ(M)` rather than through `ℚ` directly.)  The generalisation is
pure bookkeeping over the SAME per-prime input
`exists_discr_factorization_le_of_finrank_le`, which is already stated for a
general prime `q`; only the assembly `|d_K| = 2^{v₂}·p^{v_p}` had to become
`|d_K| = ∏_{q ∈ T} q^{v_q}`.

**Follow-up worth recording**: the identical generalisation is what
`HardlyRamified/Deformation.lean`'s `finiteDimensional_h1_adZeroTwistRestricted`
needs, and that module also imports `HermiteMinkowski.lean` — but it is
UPSTREAM of this one, so it cannot consume the version below.  Hoisting
`finite_inertiaOutsideSubgroups` into `HermiteMinkowski.lean` (upstream of both)
is what would make it shared; it is not done here only because that file is a
different owner's and a change there rebuilds `Deformation.lean`. -/

/-- **Open normal subgroups of `Γ ℚ` of bounded index, unramified outside a
finite set `T` of rational primes** (ADDED 2026-07-28): the subgroups `N` that
are normal, open, of index at most `n`, and into which the inertia at every
prime `q ∉ T` maps.

Under the infinite Galois correspondence these are exactly the finite Galois
subfields `K ⊆ ℚᵃˡᵍ` of degree at most `n` unramified outside `T`; the set is
FINITE, which is `finite_inertiaOutsideSubgroups` below.

Written with this module's own `inertiaToGlobalHom` rather than with
`HermiteMinkowski.lean`'s `InertiaTrivialAt`.  The two conditions are the same
up to the subtype packaging of `localInertiaGroup` — the bridge is the one line
`hinert q hq hqT ⟨σ, hσ⟩` at the end of the proof below — and keeping
`InertiaTrivialAt` out of the signature is what lets the `HermiteMinkowski`
import on this file's header stay non-public. -/
def inertiaOutsideSubgroups (T : Finset ℕ) (n : ℕ) :
    Set (Subgroup (Field.absoluteGaloisGroup ℚ)) :=
  {N | N.Normal ∧ IsOpen (N : Set (Field.absoluteGaloisGroup ℚ)) ∧
    N.FiniteIndex ∧ N.index ≤ n ∧
    ∀ (q : ℕ) (hq : q.Prime), q ∉ T →
      ∀ σ : ↥(localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat),
        inertiaToGlobalHom hq.toHeightOneSpectrumRingOfIntegersRat σ ∈ N}

set_option backward.isDefEq.respectTransparency false in
/-- **Hermite–Minkowski for an arbitrary finite set of ramified primes**
(PROVEN 2026-07-28 — the arithmetic input of `finite_h1TwistUnramified` below):
`inertiaOutsideSubgroups T n` is finite.

This is `HermiteMinkowski.lean`'s `finite_setOf_subgroup_inertiaAt_le` with the
hard-wired `{2, p}` replaced by an arbitrary `T : Finset ℕ`, and the proof is
that file's two steps run again over `T`:

* the FIELD step.  A field `K` in the set has `q ∤ d_K` for every prime
  `q ∉ T` (`not_dvd_discr_of_inertiaTrivialAt`), so the support of the
  factorisation of `|d_K|` lies in `T.filter Nat.Prime`; the exponent at each
  `q` is bounded by a constant `C q` depending only on `q` and `n`
  (`exists_discr_factorization_le_of_finrank_le`, already general in `q`), so
  `|d_K| ≤ ∏_{q ∈ T, q prime} q^{C q}` and mathlib's Hermite theorem
  `NumberField.finite_of_discr_bdd` applies.  Only this step differs from the
  `{2, p}` original, and only in replacing `Finset.prod_pair` by a `Finset`
  product over `T`.
* the SUBGROUP step, verbatim: such an `N` is closed (open ⟹ closed), hence the
  fixing subgroup of its fixed field, which is finite-dimensional
  (`InfiniteGalois.isOpen_iff_finite`), Galois (`normal_iff_isGalois`), of
  degree `= [Γ ℚ : N] ≤ n`, and inertia-trivial off `T`; so the set injects into
  the finite field set along `fixingSubgroup`.

Both-ways audit: a plain classical finiteness statement with no
representation-theoretic hypotheses.  It is not vacuous — `⊤` is a member for
every `T` and every `n ≥ 1`, and for `T = {2, 3}`, `n = 2` the members are `⊤`
and the fixing subgroups of `ℚ(i)`, `ℚ(√±3)`, `ℚ(√±2)`, `ℚ(√6)`, `ℚ(√-6)`. -/
theorem finite_inertiaOutsideSubgroups (T : Finset ℕ) (n : ℕ) :
    (inertiaOutsideSubgroups T n).Finite := by
  classical
  -- per-prime discriminant-exponent bounds; at a non-prime `q` the exponent is `0`
  have hex : ∀ q : ℕ, ∃ C : ℕ, ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ))
      (hfd : FiniteDimensional ℚ K), Module.finrank ℚ K ≤ n →
      haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
      (NumberField.discr K).natAbs.factorization q ≤ C := by
    intro q
    by_cases hq : q.Prime
    · exact exists_discr_factorization_le_of_finrank_le q n hq
    · refine ⟨0, fun K hfd hr => ?_⟩
      haveI : NumberField K := @NumberField.mk _ _ inferInstance hfd
      simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  choose C hC using hex
  set T' : Finset ℕ := T.filter Nat.Prime with hT'def
  -- STEP A: finitely many fields of degree `≤ n` unramified outside `T`
  have hfield : {K : IntermediateField ℚ (AlgebraicClosure ℚ) |
      ∃ _ : FiniteDimensional ℚ K,
        IsGalois ℚ K ∧ Module.finrank ℚ K ≤ n ∧
        ∀ (q : ℕ) (hq : q.Prime), q ∉ T →
          InertiaTrivialAt hq K.fixingSubgroup}.Finite := by
    refine Set.Finite.subset
      ((NumberField.finite_of_discr_bdd (AlgebraicClosure ℚ)
        (∏ q ∈ T', q ^ C q)).image Subtype.val) ?_
    rintro K ⟨hfd, hgal, hrank, hinert⟩
    haveI := hfd
    haveI hNF : NumberField K := @NumberField.mk _ _ inferInstance hfd
    haveI := hgal
    refine ⟨⟨K, hfd⟩, ?_, rfl⟩
    show |NumberField.discr K| ≤ ((∏ q ∈ T', q ^ C q : ℕ) : ℤ)
    have hD0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
    have hN0 : (NumberField.discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
    have hsupp : (NumberField.discr K).natAbs.factorization.support ⊆ T' := by
      intro q hqmem
      rw [Nat.support_factorization] at hqmem
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
      have hqd : q ∣ (NumberField.discr K).natAbs := Nat.dvd_of_mem_primeFactors hqmem
      refine Finset.mem_filter.mpr ⟨?_, hqp⟩
      by_contra hqT
      refine not_dvd_discr_of_inertiaTrivialAt K hqp (hinert q hqp hqT) ?_
      have h1 : (((NumberField.discr K).natAbs : ℤ)) ∣ NumberField.discr K := by
        rw [Int.natCast_natAbs]
        exact (abs_dvd _ _).mpr dvd_rfl
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hqd) h1
    have hNeq : (NumberField.discr K).natAbs =
        ∏ q ∈ T', q ^ (NumberField.discr K).natAbs.factorization q := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
      exact Finsupp.prod_of_support_subset _ hsupp (· ^ ·) (fun i _ => pow_zero i)
    have hkey : (NumberField.discr K).natAbs ≤ ∏ q ∈ T', q ^ C q := by
      rw [hNeq]
      refine Finset.prod_le_prod' ?_
      intro q hq
      exact Nat.pow_le_pow_right (Finset.mem_filter.mp hq).2.pos (hC q K hfd hrank)
    have habs : |NumberField.discr K| =
        (((NumberField.discr K).natAbs : ℤ)) := (Int.natCast_natAbs _).symm
    rw [habs]
    exact_mod_cast hkey
  -- STEP B: transport to subgroups along the infinite Galois correspondence
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  refine Set.Finite.subset (hfield.image fun K => K.fixingSubgroup) ?_
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
  intro q hq hqT σ hσ
  rw [hfix]
  exact hinert q hq hqT ⟨σ, hσ⟩

/-- The inclusion `N ↪ Γ ℚ` of a subgroup, as a continuous group homomorphism —
the restriction datum of `resSubgroupTwist1` below. -/
noncomputable def subgroupToGlobalHom (N : Subgroup (Field.absoluteGaloisGroup ℚ)) :
    ↥N →ₜ* Field.absoluteGaloisGroup ℚ :=
  ⟨N.subtype, continuous_subtype_val⟩

/-- `ad⁰ρbar(1)` restricted to a subgroup `N ≤ Γ ℚ` — the analogue of
`adZeroTwistInertia` / `adZeroTwistDecomp` along `subgroupToGlobalHom N`. -/
noncomputable def adZeroTwistSubgroup.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ)) :
    TopRep k ↥N :=
  TopRep.res (subgroupToGlobalHom N).toMonoidHom (adZeroTwist p ρbar)

/-- The restriction `H¹(ℚ, ad⁰ρbar(1)) → H¹(N, ad⁰ρbar(1))` along the inclusion
of a subgroup `N ≤ Γ ℚ`.  Its KERNEL is the inflation image from `Γ ℚ ⧸ N`
whenever `N` is closed normal, which is why it is finite for open `N` of finite
index (`finite_ker_resSubgroupTwist1` below). -/
noncomputable def resSubgroupTwist1.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ)) :
    continuousCohomology 1 (adZeroTwist p ρbar) ⟶
      continuousCohomology 1 (adZeroTwistSubgroup p ρbar N) :=
  ContinuousCohomology.map (subgroupToGlobalHom N)
    (CategoryTheory.CategoryStruct.id (adZeroTwistSubgroup p ρbar N)) 1

/-- **A continuous representation of `Γ ℚ` over a finite coefficient field is
unramified outside a finite set of primes** (SORRY LEAF, cut out 2026-07-28 as
the first of the three inputs of `finite_h1TwistUnramified` below).

This is the classical "a number field is ramified at only finitely many
primes", transported through the kernel of `ρbar`.  Route, all of whose steps
already have their tooling in this tree: `k` is `Finite` and `W` is a finite
`k`-module, so `Module.End k W` is finite discrete and the continuity of `ρbar`
makes `ker ρbar` an OPEN normal subgroup of `Γ ℚ`; its fixed field `K` is a
finite Galois number field (`InfiniteGalois.isOpen_iff_finite`,
`normal_iff_isGalois`, exactly as in the second half of
`finite_inertiaOutsideSubgroups` above); take
`T = (NumberField.discr K).natAbs.primeFactors`.  For `q ∉ T` mathlib's
`NumberField.not_dvd_discr_iff_forall_mem` says every prime of `𝓞 K` over `q`
is unramified, and the inertia at `q` therefore lands in `K.fixingSubgroup =
ker ρbar`, i.e. `ρbar` is unramified at `q`.

**What is genuinely missing and is this leaf's content**: the last step is the
CONVERSE of `MinkowskiUnramified.lean`'s PROVEN
`isUnramifiedAt_of_inertia_le_fixingSubgroup` (which runs
inertia-trivial ⟹ unramified).  `grep -rn "isUnramifiedAt_of_inertia_le_fixingSubgroup"
Fermat/` finds only that direction, and
`open_normal_subgroup_eq_top_of_inertia_le` in the same file is a Minkowski
statement about ALL primes at once, so it does not supply it either.  That
converse — "`q` unramified in the finite Galois `K` ⟹ the image of `I_q` fixes
`K` pointwise" — is the one new dictionary lemma this leaf costs.

Both-ways audit: a plain classical finiteness with no hypothesis on `ρbar`
beyond its type, hence non-vacuous and not discharge-able by refuting any
package.  It is stated for the FULL prime set rather than for a bound so that
the consumer may enlarge `T` freely (it adds `2` and `p` itself). -/
theorem exists_finset_isUnramifiedAt_of_notMem.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) :
    ∃ T : Finset ℕ, ∀ (q : ℕ) (hq : q.Prime), q ∉ T →
      ρbar.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := sorry

/-- **An unramified-outside-`{2, p}` class dies on a small open subgroup**
(SORRY LEAF, cut out 2026-07-28 as the second of the three inputs of
`finite_h1TwistUnramified` below — this is the cocycle bookkeeping, and the only
one of the three that touches the cochain model).

Given a finite set `T` of primes containing `2`, `p` and every prime at which
`ρbar` ramifies, there is a bound `n` such that EVERY class `c` unramified
outside `{2, p}` restricts to zero on SOME `N ∈ inertiaOutsideSubgroups T n`.

# ROUTE (this is `finite_setOf_galoisRep_isUnramifiedAt`'s argument, run on
cocycles instead of on representations)

Write `M = ad⁰ρbar(1)`, a finite discrete `Γ ℚ`-module, and let `z` be a
continuous `1`-cocycle representing `c`.

* `N₁ := ker(Γ ℚ → Aut_k M)` is open normal of index at most `#Aut_k M`, since
  `M` is finite discrete and the action is continuous.
* `N := {g ∈ N₁ | z g = 0}` is again OPEN (preimage of `{0}` under a continuous
  map into a discrete space) and NORMAL in `Γ ℚ` — not merely in `N₁`: for
  `g ∈ Γ ℚ` and `x ∈ N₁` one computes `z (g x g⁻¹) = g · z x`, using
  `z (g⁻¹) = −g⁻¹ · z g` and that `x` acts trivially on `M`.  Its index is at
  most `#Aut_k M · #M`, which is the `n` to take.
* `N ∈ inertiaOutsideSubgroups T n`: for a prime `q ∉ T` the module `M` is
  unramified at `q` (`hT` for the `ad⁰` factor; the mod-`p` cyclotomic
  character is unramified away from `p ∈ T`), so `I_q ⊆ N₁`; and `c` unramified
  at `q` means `z|_{I_q}` is a coboundary `σ ↦ σ·m − m` on `I_q`, which VANISHES
  because `I_q` acts trivially.  Hence `I_q ⊆ N`.  (This is the "honest zero
  cocycle, not merely a coboundary" step recorded on `h1TwistUnramified`.)
* `res^{Γ ℚ}_N c = 0` because `z` restricts to the zero cocycle on `N`.

# WHAT IT COSTS

The degree-`1` INHOMOGENEOUS cochain dictionary, which neither our pin nor
`~/cs/FLT` has: our pin's `ContCohomology/LowDegree.lean` computes `H⁰` only,
and the vendored
`Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`
supplies `cocycleClass` / `cocycleClass_eq_zero_iff` for the HOMOGENEOUS model
`(homogeneousCochains X).X 1 = (C(G, C(G, M)))^G`.  What is needed is the
identification of that with `C(G, M)` — `F ↦ (y ↦ F 1 y)`, inverse
`z ↦ (x, y) ↦ x · z (x⁻¹ y)` — carrying `d` to the usual cocycle condition, plus
the compatibility of `ContinuousCohomology.map` with it.  Everything after that
is the four bullets above.

Both-ways audit: `T` and `n` are existentially/universally placed so that the
statement is a genuine assertion about every class; it is not vacuous, since
`h1TwistUnramified` contains `0` and the hypotheses on `T` are satisfiable
(`exists_finset_isUnramifiedAt_of_notMem` above supplies one).  No hypothesis on
`ρbar` beyond its type, so no circular discharge is available. -/
theorem exists_mem_inertiaOutsideSubgroups_resSubgroup_eq_zero.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (T : Finset ℕ)
    (h2T : 2 ∈ T) (hpT : p ∈ T)
    (hT : ∀ (q : ℕ) (hq : q.Prime), q ∉ T →
      ρbar.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ n : ℕ, ∀ c ∈ h1TwistUnramified p ρbar,
      ∃ N ∈ inertiaOutsideSubgroups T n,
        c ∈ LinearMap.ker (resSubgroupTwist1 p ρbar N).hom.toLinearMap := sorry

/-- **Inflation–restriction: the kernel of restriction to an open normal
subgroup is finite** (SORRY LEAF, cut out 2026-07-28 as the third of the three
inputs of `finite_h1TwistUnramified` below).

For `N ≤ Γ ℚ` open, normal and of finite index, the kernel of
`res : H¹(Γ ℚ, ad⁰ρbar(1)) → H¹(N, ad⁰ρbar(1))` is finite.

# ROUTE

The inflation–restriction sequence in degree `1`,
`0 → H¹(Γ ℚ ⧸ N, M^N) → H¹(Γ ℚ, M) → H¹(N, M)`, identifies the kernel with
`H¹(Γ ℚ ⧸ N, M^N)`; `Γ ℚ ⧸ N` is a FINITE discrete group (`N` open of finite
index) and `M^N ⊆ M` is finite, so that group is a subquotient of the finite set
of functions `Γ ℚ ⧸ N → M` and hence finite.

Only the INJECTIVITY half of inflation–restriction is needed, and it can be had
directly rather than through the exact sequence: a class in the kernel is
represented by a cocycle vanishing on `N` after adjusting by a coboundary, and
such a cocycle is constant on the left cosets `gN` (`z (g x) = z g + g · z x =
z g`), so the map "kernel → functions `Γ ℚ ⧸ N → M`" is well defined and
injective modulo the finite group of coboundaries `B¹ ≅ M / M^{Γ ℚ}`.  Both
routes need the same missing input as
`exists_mem_inertiaOutsideSubgroups_resSubgroup_eq_zero` above — the degree-`1`
inhomogeneous cochain dictionary — which is why the two leaves are natural
companions and are best given to ONE owner.

Both-ways audit: `hnorm`, `hopen` and `hFI` are all load-bearing.  Dropping
`hopen` makes the statement FALSE as a matter of continuous cohomology: a
non-closed `N` of finite index has no inflation–restriction sequence, and
dropping `hFI` makes `Γ ℚ ⧸ N` infinite and the kernel infinite-dimensional
(this is exactly the `dim_k H¹(Γ ℚ, ad⁰(1)) = ℵ₀` computation recorded on
`Sha1Twist` in `HardlyRamified/Deformation.lean`, at `N = 1`). -/
theorem finite_ker_resSubgroupTwist1.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (N : Subgroup (Field.absoluteGaloisGroup ℚ)) (hnorm : N.Normal)
    (hopen : IsOpen (N : Set (Field.absoluteGaloisGroup ℚ)))
    (hFI : N.FiniteIndex) :
    Finite ↥(LinearMap.ker (resSubgroupTwist1 p ρbar N).hom.toLinearMap) := sorry

/-- **Finiteness of the unramified-outside-`{2, p}` part of
`H¹(ℚ, ad⁰ρbar(1))`** (cut out 2026-07-27 as the first of the two inputs of
DDT Thm. 2.49, see `exists_taylorWilesPrimeSet_core` below; **PROVEN
2026-07-28** over the three named leaves immediately above —
`exists_finset_isUnramifiedAt_of_notMem`,
`exists_mem_inertiaOutsideSubgroups_resSubgroup_eq_zero` and
`finite_ker_resSubgroupTwist1` — together with the newly PROVEN
Hermite–Minkowski input `finite_inertiaOutsideSubgroups`).

# THE ASSEMBLY, IN ONE LINE

`h1TwistUnramified` is covered by the union, over the FINITELY many `N` in
`inertiaOutsideSubgroups T n`, of the kernels of restriction to `N`; each such
kernel is finite; a finite union of finite sets is finite; and a finite module
over a field is `Module.Finite`.

# WHY IT IS TRUE, AND THE ROUTE

`h1TwistUnramified p ρbar` is canonically `H¹(G_{ℚ,S}, ad⁰ρbar(1))` for
`S = hardlyRamifiedPlaces p = {2, p}` — see that definition's docstring
for the inflation identification, which is where the argument starts —
and the assertion is that this `k`-vector space is FINITE-dimensional.

`ad⁰ρbar(1)` is a FINITE discrete `Γ ℚ`-module (`k` is `Finite` and
`dim_k ad⁰ = 3`).  A class in `H¹(G_{ℚ,S}, M)` is a continuous cocycle, hence
factors through a finite quotient of `G_{ℚ,S}`, and the extension of `ℚ(M)` it
cuts out is unramified outside `S ∪ ram(ρbar)` of degree bounded by
`#Aut M · #M`.  Hermite–Minkowski bounds the number of such fields, so there are
finitely many cocycles up to coboundary.

**CORRECTION 2026-07-28 — the previous version of this docstring said the
Hermite–Minkowski module "is NOT currently in this file's import cone — wiring
it in is part of this leaf".  That was FALSE when written**: the header of this
file has carried `import Fermat.FLT.GaloisRepresentation.HardlyRamified.HermiteMinkowski`
since before the leaf was cut, and `finite_setOf_isHardlyRamified` from that
module is already consumed in a proof body here.  The import is non-public,
which is enough for proof-body use and is why nothing had to change.  What was
genuinely missing was not the import but the GENERALITY: that module's
`finite_setOf_subgroup_inertiaAt_le` is hard-wired to `{2, p}`, and this leaf
needs an arbitrary finite prime set because it carries no hypothesis on `ρbar`.
That generalisation is `finite_inertiaOutsideSubgroups` above, now proven.

CIRCULARITY GUARD (inherited from pillar 3b, and it binds this leaf):
must not be proven through `Family.lean` or anything downstream of it,
and not through `not_isIrreducible_of_isHardlyRamified_of_five_le` or
`IsHardlyRamified.mod_three_reducible` — the point is moot here, since
this statement carries NO hypothesis on `ρbar` beyond its type and so
cannot be discharged by refuting the hardly ramified package.  The proof below
and the three leaves it rests on all satisfy this: none of them mentions
`IsHardlyRamified` at all. -/
theorem finite_h1TwistUnramified.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) :
    Module.Finite k ↥(h1TwistUnramified p ρbar) := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finset_isUnramifiedAt_of_notMem p ρbar
  set T : Finset ℕ := insert 2 (insert p T₀) with hTdef
  obtain ⟨n, hcov⟩ := exists_mem_inertiaOutsideSubgroups_resSubgroup_eq_zero p ρbar T
    (Finset.mem_insert_self 2 _)
    (Finset.mem_insert_of_mem (Finset.mem_insert_self p _))
    (fun q hq hqT => hT₀ q hq fun hq0 =>
      hqT (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq0)))
  have hfin : (⋃ N ∈ inertiaOutsideSubgroups T n,
      (LinearMap.ker (resSubgroupTwist1 p ρbar N).hom.toLinearMap :
        Set (continuousCohomology 1 (adZeroTwist p ρbar)))).Finite := by
    refine (finite_inertiaOutsideSubgroups T n).biUnion fun N hN => ?_
    haveI := finite_ker_resSubgroupTwist1 p ρbar N hN.1 hN.2.1 hN.2.2.1
    exact Set.toFinite _
  have hsub : (h1TwistUnramified p ρbar :
      Set (continuousCohomology 1 (adZeroTwist p ρbar))) ⊆
      ⋃ N ∈ inertiaOutsideSubgroups T n,
        (LinearMap.ker (resSubgroupTwist1 p ρbar N).hom.toLinearMap :
          Set (continuousCohomology 1 (adZeroTwist p ρbar))) := by
    intro c hc
    obtain ⟨N, hN, hres⟩ := hcov c hc
    exact Set.mem_biUnion hN hres
  haveI : Finite ↥(h1TwistUnramified p ρbar) := (hfin.subset hsub).to_subtype
  exact Module.Finite.of_finite

/-! #### Record: what the leaf's original docstring claimed, superseded 2026-07-28

# WHY IT WAS THOUGHT CHEAP

`Fermat/FLT/GaloisRepresentation/HardlyRamified/HermiteMinkowski.lean`
proves `finite_setOf_subgroup_inertiaAt_le` (finitely many open normal
subgroups of `Γ ℚ` of bounded index containing the global inertia at
every `q ∉ {2, p}`) and, over it, `finite_setOf_galoisRep_isUnramifiedAt`
and `finite_setOf_isHardlyRamified`.  The first of those is exactly the
"`G_{ℚ,{2,p}}` is small" statement this leaf needs; what remains is the
cocycle-to-subgroup bookkeeping, of which
`finite_setOf_galoisRep_isUnramifiedAt`'s proof is a worked model in the
same file (a representation is determined by the induced function
`Γ ℚ ⧸ N → E` on `Quotient.out` representatives; a cocycle is determined
the same way, and coboundaries are a subspace of a finite space).

That estimate was right about the SHAPE and wrong about two costs, both now
itemised as leaves above: the generality of the prime set (fixed by
`finite_inertiaOutsideSubgroups`, proven) and the absence of a degree-`1`
inhomogeneous cochain dictionary (still open, and it is what
`exists_mem_inertiaOutsideSubgroups_resSubgroup_eq_zero` and
`finite_ker_resSubgroupTwist1` both cost).

This is the finiteness that `Sha1Twist`'s docstring in
`HardlyRamified/Deformation.lean` records, and that
`finiteDimensional_h1_adZeroTwistRestricted` in that module states over
`G_{ℚ,S}` rather than over `Γ ℚ` with the unramifiedness condition — the same
group in degree `1`.  A proof here does NOT literally discharge that leaf (this
module is DOWNSTREAM of `Deformation.lean`, which therefore cannot import it),
but the arithmetic input is shared and is available to both; see the section
header above `inertiaOutsideSubgroups` for what hoisting it would take. -/

/-! ### The Taylor–Wiles locus, and the Chebotarev extraction factored out of it

Added 2026-07-28 as the decomposition of
`exists_taylorWilesPrime_locResDecomp_ne_zero` (DDT Lemma 2.48) below.

`exists_taylorWilesPrime` above proves its existence statement by putting
the two LOCAL Taylor–Wiles conditions into one open set and hitting it
with Chebotarev density.  The strengthened statement needs a THIRD,
cohomological condition, and the argument is the same one: the third
condition also cuts out an open, conjugation-stable locus, and Chebotarev
produces a Frobenius in the intersection.

So the two halves are separated here: the conditions on the Galois
element are packaged as the `Set` `taylorWilesLocus`, whose three
relevant properties (open, conjugation-stable, nonempty) are PROVEN
below, and the extraction of a prime from an open conjugation-stable
locus is the proof of `exists_taylorWilesPrime_locResDecomp_ne_zero`
itself, also proven.  What remains open is one leaf,
`exists_separatingOpen_locResDecomp`: the existence of the cohomological
locus.  That is exactly the arithmetic content of DDT 2.48 and nothing
else.

Nothing here changes `exists_taylorWilesPrime` above; it keeps its own
inline copies of the openness arguments so that the two declarations stay
independently owned. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Fixing the `m`-th roots of unity is an open condition** (PROVEN):
the set of absolute Galois elements of `ℚ` acting trivially on every
`m`-th root of unity is open, being the fixing subgroup of the FINITE
extension `ℚ(μ_m)/ℚ`.

This is the second of the two open loci of `exists_taylorWilesPrime`'s
proof, hoisted so that `isOpen_taylorWilesLocus` below can reuse it.
The `set_option` is not decoration: without it the
`IntermediateField.adjoin ℚ {ζ | ζ ^ m = 1}` in the statement of the
auxiliary `FiniteDimensional` instance elaborates against
`DivisionRing.toRatAlgebra` rather than `AlgebraicClosure.instAlgebra ℚ`,
and the two are not defeq at `instances` transparency. -/
lemma isOpen_setOf_fixes_rootsOfUnity (m : ℕ) (hm : 0 < m) :
    IsOpen {x : Field.absoluteGaloisGroup ℚ |
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → x ζ = ζ} := by
  classical
  -- the `m`-th roots of unity are finite …
  have hSfin : {ζ : AlgebraicClosure ℚ | ζ ^ m = 1}.Finite := by
    refine Set.Finite.subset
      (Polynomial.nthRoots m (1 : AlgebraicClosure ℚ)).toFinset.finite_toSet fun ζ hζ => ?_
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hm]
    exact hζ
  haveI := hSfin.to_subtype
  haveI : FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ {ζ : AlgebraicClosure ℚ | ζ ^ m = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- … so fixing them pointwise is exactly the fixing subgroup of `ℚ(μ_m)`
  have hfixset : {x : Field.absoluteGaloisGroup ℚ |
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ m = 1 → x ζ = ζ} =
      ((IntermediateField.adjoin ℚ
        {ζ : AlgebraicClosure ℚ | ζ ^ m = 1}).fixingSubgroup :
        Set (Field.absoluteGaloisGroup ℚ)) := by
    ext x
    constructor
    · intro hx
      have hle : IntermediateField.adjoin ℚ {ζ : AlgebraicClosure ℚ | ζ ^ m = 1} ≤
          IntermediateField.fixedField (Subgroup.zpowers x) := by
        rw [IntermediateField.adjoin_le_iff]
        intro ζ hζ
        rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        intro f hf
        have hst : Subgroup.zpowers x ≤
            MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) ζ :=
          Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (hx ζ hζ))
        exact hst hf
      refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun a ha => ?_
      exact (IntermediateField.mem_fixedField_iff _ _).mp (hle ha) x (Subgroup.mem_zpowers x)
    · intro hx ζ hζ
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hx ζ
        (IntermediateField.subset_adjoin ℚ _ hζ)
  rw [hfixset]
  exact (IntermediateField.adjoin ℚ _).fixingSubgroup_isOpen

/-- **The Taylor–Wiles locus at level `n`** (ADDED 2026-07-28): the set of
absolute Galois elements of `ℚ` satisfying the two LOCAL Taylor–Wiles
conditions — acting trivially on the `p^n`-th roots of unity, and having
characteristic polynomial split with two DISTINCT roots over `k`.

This is precisely the set that `exists_taylorWilesPrime` above intersects
with the dense union of Frobenius conjugacy classes, written down as a
`Set` so that the cohomological condition of DDT 2.48 can be intersected
with it.  Its three relevant properties are proven immediately below:
`isOpen_taylorWilesLocus`, `taylorWilesLocus_conj` (conjugation
stability, which is what lets a Frobenius CONJUGATE in the locus be
traded for the Frobenius itself) and `nonempty_taylorWilesLocus` (which
is `exists_fixing_rootsOfUnity_charpoly_split`, restated).

A prime `q ≠ p` whose `globalFrob` lies here is a Taylor–Wiles prime of
level `n`: the roots-of-unity clause forces `q ≡ 1 (mod p^n)` through
`cyclotomicCharacter_globalFrob`, and the charpoly clause IS the split
condition through `charFrob_eq_charpoly_globalFrob`.  Both derivations
are carried out in `exists_taylorWilesPrime_locResDecomp_ne_zero`'s
proof below. -/
def taylorWilesLocus.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (n : ℕ) :
    Set (Field.absoluteGaloisGroup ℚ) :=
  {x | (∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 → x ζ = ζ) ∧
    ∃ α β : k, α ≠ β ∧
      (ρbar x).charpoly =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)}

/-- **Membership in `taylorWilesLocus` unfolded** (PROVEN, definitional). -/
lemma mem_taylorWilesLocus.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (n : ℕ)
    {x : Field.absoluteGaloisGroup ℚ} :
    x ∈ taylorWilesLocus p ρbar n ↔
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p ^ n = 1 → x ζ = ζ) ∧
      ∃ α β : k, α ≠ β ∧
        (ρbar x).charpoly =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) :=
  Iff.rfl

/-- **The Taylor–Wiles locus is OPEN** (PROVEN): the charpoly clause is
the `ρbar`-preimage of a set in the DISCRETE endomorphism space (`k` is
finite discrete, so `Module.End k W` carries the discrete module
topology), and the roots-of-unity clause is
`isOpen_setOf_fixes_rootsOfUnity`. -/
lemma isOpen_taylorWilesLocus.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (n : ℕ) :
    IsOpen (taylorWilesLocus p ρbar n) := by
  classical
  letI := moduleTopology k (Module.End k W)
  haveI : DiscreteTopology (Module.End k W) := discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  have hsplit : IsOpen ((fun x : Field.absoluteGaloisGroup ℚ => ρbar x) ⁻¹'
      {φ : Module.End k W | ∃ α β : k, α ≠ β ∧ φ.charpoly =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)}) :=
    (isOpen_discrete _).preimage hρcont
  have hfix := isOpen_setOf_fixes_rootsOfUnity (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n)
  exact hfix.inter hsplit

/-- **The Taylor–Wiles locus is stable under conjugation** (PROVEN): the
set of `p^n`-th roots of unity is Galois-stable, so fixing it pointwise
is a conjugation-invariant condition; and the characteristic polynomial
is a conjugation invariant (`LinearEquiv.charpoly_conj`).

This is what lets the Chebotarev extraction below trade the conjugate
`g · Frob_q · g⁻¹` that density supplies for `Frob_q` itself. -/
lemma taylorWilesLocus_conj.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) (n : ℕ)
    (g : Field.absoluteGaloisGroup ℚ) {x : Field.absoluteGaloisGroup ℚ}
    (hx : x ∈ taylorWilesLocus p ρbar n) :
    g * x * g⁻¹ ∈ taylorWilesLocus p ρbar n := by
  obtain ⟨hfix, α, β, hαβ, hpoly⟩ := hx
  refine ⟨?_, α, β, hαβ, ?_⟩
  · intro ζ hζ
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      hfix (g.symm ζ) (by rw [← map_pow, hζ, map_one]), AlgEquiv.apply_symm_apply]
  · have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
      have h1 : ρbar g * ρbar g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact h1
    have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
      have h1 : ρbar g⁻¹ * ρbar g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact h1
    have heq : ρbar (g * x * g⁻¹) =
        (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj (ρbar x) := by
      ext w
      simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
    rw [heq, LinearEquiv.charpoly_conj, hpoly]

/-- **The Taylor–Wiles locus is NONEMPTY** (PROVEN): this is
`exists_fixing_rootsOfUnity_charpoly_split` above, restated as
membership. -/
lemma nonempty_taylorWilesLocus.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ) :
    (taylorWilesLocus p ρbar n).Nonempty := by
  obtain ⟨σ, hσfix, α, β, hαβ, hσpoly⟩ :=
    exists_fixing_rootsOfUnity_charpoly_split hpodd hW hρbar hirr n
  exact ⟨σ, hσfix, α, β, hαβ, hσpoly⟩

/-- **The surviving locus of a continuous `1`-cocycle** (ADDED 2026-07-28):
the set of Galois elements `x` at which the cocycle `z` is NOT a local
coboundary, i.e. `z x ∉ (ρ x - 1) · ad⁰ρbar(1)`.

This is the classical `V` of DDT Lemma 2.48, written down.  Writing it
down at all is what the new module
`Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/LowDegreeOne.lean`
supplies: our pin computes `continuousCohomology` from HOMOGENEOUS
cochains and gives no way to evaluate a class at a group element, so
before that module the phrase "`c(σ) ∉ (σ - 1)·M`" was not expressible in
this tree at all.

Three facts make it the right object:

* it depends only on the COHOMOLOGY CLASS of `z`, since changing `z` by a
  coboundary moves `z x` inside `(ρ x - 1) · M`;
* it is CONJUGATION-STABLE (`survivingLocus_conj` below, proven from the
  crossed-homomorphism identity), which is what makes it usable with
  Chebotarev density — only Frobenius CONJUGACY CLASSES are available
  there;
* at a prime `q` where the class is unramified, `Frob_q ∈ survivingLocus`
  is exactly the statement that the class survives the local restriction
  at `q`, because the unramified local `H¹` is `M / (Frob_q - 1) M` under
  evaluation at `Frob_q`.  That last one is the content of
  `notMem_ker_locResDecompTwist1_of_mem_survivingLocus` below. -/
def survivingLocus.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (z : ContinuousCohomology.cocycles₁ (adZeroTwist p ρbar)) :
    Set (Field.absoluteGaloisGroup ℚ) :=
  {x | ContinuousCohomology.eval₁ (adZeroTwist p ρbar) z.1 x ∉
    Set.range fun m : ↥(adZeroTwist p ρbar) => (adZeroTwist p ρbar).ρ x m - m}

/-- **The surviving locus is stable under conjugation** (PROVEN): immediate
from `ContinuousCohomology.cocycles₁_eval₁_mem_range_sub_conj`, which is in
turn the crossed-homomorphism identity
`z (g x g⁻¹) = ρ g (z x) + z g - ρ (g x g⁻¹) (z g)` together with the fact
that `ρ g` carries `(ρ x - 1) · M` bijectively onto
`(ρ (g x g⁻¹) - 1) · M`. -/
lemma survivingLocus_conj.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (z : ContinuousCohomology.cocycles₁ (adZeroTwist p ρbar))
    (g x : Field.absoluteGaloisGroup ℚ) (hx : x ∈ survivingLocus p ρbar z) :
    g * x * g⁻¹ ∈ survivingLocus p ρbar z :=
  fun hmem => hx (ContinuousCohomology.cocycles₁_eval₁_mem_range_sub_conj z g x hmem)

/-- **The GLOBAL half of DDT Lemma 2.48** (SORRY LEAF, cut out 2026-07-28):
for a cocycle `z` representing a nonzero class `c` unramified outside
`{2, p}`, the surviving locus of `z` is OPEN and MEETS the Taylor–Wiles
locus at level `n`.  (The representative itself is supplied by
`ContinuousCohomology.exists_cocycleClass_eq`, in the consumer.)

This is the deep half — the "nonemptiness step" of DDT §2 — and it is
where `ρbar|_{ℚ(ζ_p)}` absolutely irreducible is used classically.

# ROUTE

Let `M = ad⁰ρbar(1)` and `L = ℚ(M, μ_{p^n})`, a finite Galois extension of
`ℚ`.

*Openness.*  `M` is a finite discrete `k`-module and `z` is continuous
(`ContinuousCohomology.continuous_eval₁`), so `x ↦ z x` is continuous into
a discrete space; `x ↦ ρ x` is likewise continuous into the discrete
`End_k M`, because `ρbar` is.  So `x ↦ (z x, ρ x)` is continuous into a
discrete space and the surviving locus is the preimage of a subset of it.
Concretely the locus is a union of cosets of the open normal subgroup
`Γ_{L_z}`, where `L_z/L` is the extension cut out by `z|_{Γ L}`.

*Nonemptiness.*  `Γ L` acts trivially on `M`, so `z|_{Γ L}` is a
HOMOMORPHISM `Γ L → M`, and `Γ L` is normal, so `taylorWilesLocus`
contains the whole coset `σ · Γ L` of any `σ` in it
(`nonempty_taylorWilesLocus` supplies one).  Restriction
`H¹(Γ ℚ, M) → Hom(Γ L, M)` is injective on classes unramified outside
`{2, p}` because `H¹(Gal(L/ℚ), M) = 0` — this is the step needing absolute
irreducibility of `ρbar|_{ℚ(ζ_p)}`, which for odd `p` follows from `hρbar`
together with `hirr` — so `z|_{Γ L} ≠ 0`.  Now `ρ σ` has two DISTINCT
eigenvalues, so `(ρ σ - 1) · M` is a PROPER subspace of `M`; if
`z σ ∈ (ρ σ - 1) · M`, pick `τ ∈ Γ L` with `z τ` outside it and use
`z (σ τ) = z σ + ρ σ (z τ)` (`ContinuousCohomology.cocycles₁_eval₁_mul`)
to move out.  Either `σ` or `σ τ` then lies in the intersection.

Both-ways audit: at the intended instantiation this is the cited
Taylor–Wiles separation step; abstractly the hypothesis set contains the
classically unsatisfiable irreducible hardly ramified `ρbar`, so the
statement is classically true outright and CANNOT be false as stated.
CIRCULARITY GUARD: for that very reason it must not be discharged through
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible`, `Family.lean` or anything
downstream of them — a proof ending in `exfalso` on `hirr` is the circular
discharge and is BANNED. -/
theorem isOpen_survivingLocus_and_meets_taylorWilesLocus.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ)
    (z : ContinuousCohomology.cocycles₁ (adZeroTwist p ρbar))
    {c : continuousCohomology 1 (adZeroTwist p ρbar)}
    (hzc : ContinuousCohomology.cocycleClass (adZeroTwist p ρbar) 1 z = c)
    (hcunr : c ∈ h1TwistUnramified p ρbar) (hc0 : c ≠ 0) :
    IsOpen (survivingLocus p ρbar z) ∧
      (survivingLocus p ρbar z ∩ taylorWilesLocus p ρbar n).Nonempty := sorry

/-- **The LOCAL half of DDT Lemma 2.48** (SORRY LEAF, cut out 2026-07-28):
at a prime `q ∉ {2, p}` where the class `c` is unramified, membership of
`Frob_q` in the surviving locus of a cocycle representative implies that
`c` does not die under the full local restriction at `q`.

# ROUTE

`hcunr` says `c` dies under restriction to the inertia group at every place
off `hardlyRamifiedPlaces p = {2, p}`, and `q` is such a place (this is
what `hq2` and `hqp` are for; the identification of "`q ∉ {2, p}` as a
number" with "the place of `q` is not in `hardlyRamifiedPlaces p`" goes
through the injectivity of `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`
proven in `Chebotarev.lean`).

So the restriction of `c` to the decomposition group `G_q` is INFLATED from
the procyclic quotient `G_q / I_q`, topologically generated by `Frob_q`.
For a procyclic group `⟨F⟩^` acting on a finite module `M`, evaluation at
`F` is an isomorphism `H¹(⟨F⟩^, M) ≅ M / (ρ F - 1) M`: a cocycle is
determined by its value at `F` by the crossed-homomorphism identity
(`ContinuousCohomology.cocycles₁_eval₁_mul`), and it is a coboundary
exactly when that value lies in `(ρ F - 1) M`.  Hence

    loc_q c = 0  ↔  z (Frob_q) ∈ (ρ Frob_q - 1) · M  ↔  Frob_q ∉ survivingLocus ,

and `hmem` is the right-hand negation.

The `↔` in the last display is stronger than needed: only the direction
"`Frob_q ∈ survivingLocus ⟹ loc_q c ≠ 0`" is asserted here, and it needs
only the EASY half — that a class dying locally has a representative whose
value at `Frob_q` is a `(ρ Frob_q - 1)`-boundary, obtained by inflating a
coboundary witness back along `G_q ↠ ⟨Frob_q⟩^`.  `cocycleClass_eq_zero_iff`
in the vendored `ContCohomology/Basic.lean` is the handle that turns the
vanishing of a class into the cocycle being a coboundary.

Note that no local Tate duality is needed, in keeping with the deviation
note on `IsTaylorWilesPrimeSet`.

Both-ways audit and CIRCULARITY GUARD: as for the global half above. -/
theorem notMem_ker_locResDecompTwist1_of_mem_survivingLocus.{uK, uW}
    (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W)
    (z : ContinuousCohomology.cocycles₁ (adZeroTwist p ρbar))
    {c : continuousCohomology 1 (adZeroTwist p ρbar)}
    (hzc : ContinuousCohomology.cocycleClass (adZeroTwist p ρbar) 1 z = c)
    (hcunr : c ∈ h1TwistUnramified p ρbar)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hmem : globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ∈
      survivingLocus p ρbar z) :
    c ∉ LinearMap.ker (locResDecompTwist1 p ρbar
      hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap := sorry

/-- **The separating locus of a nonzero dual-Selmer class — the
arithmetic core of DDT Lemma 2.48** (cut out 2026-07-28 by
the decomposition of `exists_taylorWilesPrime_locResDecomp_ne_zero`
below, and **PROVEN the same day** over the two halves
`isOpen_survivingLocus_and_meets_taylorWilesLocus` (global) and
`notMem_ker_locResDecompTwist1_of_mem_survivingLocus` (local), with the
conjugation stability supplied by `survivingLocus_conj`): a nonzero class
`c ∈ H¹(ℚ, ad⁰ρbar(1))` unramified outside
`{2, p}` has an OPEN, CONJUGATION-STABLE locus `V ⊆ Γ ℚ` which
(a) meets the Taylor–Wiles locus at level `n`, and (b) is such that
`c` survives locally at every prime `q ∉ {2, p}` whose Frobenius lies in
it.

Everything else in DDT 2.48 — Chebotarev density, the congruence
`q ≡ 1 (mod p^n)`, and the identification of `charFrob` with the
characteristic polynomial at `globalFrob` — is discharged in
`exists_taylorWilesPrime_locResDecomp_ne_zero` below, which is PROVEN
over this leaf.  So this statement is the whole arithmetic content and
nothing else.

# THE CLASSICAL `V`, AND WHY IT HAS EACH OF THESE PROPERTIES

Write `M = ad⁰ρbar(1)`, let `z` be a continuous 1-cocycle representing
`c`, and take

    V = {x ∈ Γ ℚ | z x ∉ (ρ x - 1) • M} .

* **Well defined.**  Changing `z` by a coboundary `x ↦ (ρ x - 1) b`
  changes `z x` inside `(ρ x - 1) • M`, so `V` depends only on `c`.
* **Open.**  `M` is finite discrete and `z`, `ρ` are continuous, so
  `x ↦ (z x, ρ x)` is a continuous map into a discrete space and `V` is
  the preimage of a subset of it.
* **Conjugation-stable.**  The crossed-homomorphism identity gives
  `z (g x g⁻¹) = ρ g (z x) + (1 - ρ (g x g⁻¹)) (z g)`, while
  `(ρ (g x g⁻¹) - 1) • M = ρ g ((ρ x - 1) • M)` because `ρ g` is
  bijective on `M`; the correction term
  `(1 - ρ (g x g⁻¹)) (z g) = -ρ g ((ρ x - 1) (ρ g⁻¹ (z g)))` already lies
  in `ρ g ((ρ x - 1) • M)`, so membership is unchanged.
* **(b), the local computation.**  For `q ∉ {2, p}` the class `c` is
  unramified at `q` (that is `hcunr`), so its restriction to the
  decomposition group at `q` is inflated from the procyclic
  `G_q / I_q = ⟨Frob_q⟩^`, whose `H¹` with coefficients in `M` is
  `M / (ρ Frob_q - 1) M` under evaluation at `Frob_q`.  Hence
  `loc_q c = 0` iff `z (Frob_q) ∈ (ρ Frob_q - 1) • M`, i.e. iff
  `Frob_q ∉ V`.
* **(a), the nonemptiness — this is the only deep step.**  Let
  `L = ℚ(M, μ_{p^n})`, a finite Galois extension of `ℚ`, and let
  `σ ∈ Γ ℚ` be a Taylor–Wiles element (`nonempty_taylorWilesLocus`).
  Since `Γ L` acts trivially on `M`, `z|_{Γ L}` is a HOMOMORPHISM
  `Γ L → M`, and `Γ L` is normal, so `taylorWilesLocus` contains the
  whole coset `σ · Γ L`.  Restriction
  `H¹(Γ ℚ, M) → H¹(Γ L, M) = Hom(Γ L, M)` is injective on classes
  unramified outside `{2, p}` because `H¹(Gal(L/ℚ), M) = 0`, which is
  where `ρbar|_{ℚ(ζ_p)}` absolutely irreducible is used (DDT §2, and for
  `p` odd it follows from `hρbar` together with `hirr`).  So
  `z|_{Γ L} ≠ 0`; picking `τ ∈ Γ L` with `z τ ∉ (ρ σ - 1) • M` when
  `z σ ∈ (ρ σ - 1) • M` — possible because `ρ σ` has distinct
  eigenvalues, so `(ρ σ - 1) • M` is a PROPER subspace of `M` and
  `z (σ τ) = z σ + ρ σ (z τ)` moves out of it — gives an element of
  `V ∩ taylorWilesLocus`.

# HOW IT IS PROVEN, AND WHAT HAD TO BE BUILT (2026-07-28)

The obstruction was NOT the arithmetic above; it was that
`continuousCohomology 1` had no INHOMOGENEOUS cocycle description in this
tree, so `z x` could not be written at all.  What existed was
`Fermat/FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean`
(vendored 2026-07-27): `ContinuousCohomology.cocycleClass`, turning a
cocycle in the KERNEL MODEL into a class, and `cocycleClass_eq_zero_iff`,
turning vanishing into being a coboundary.  Mathlib's own
`ContCohomology/LowDegree.lean` stops at degree `0` (`zeroIso`).

That gap is now closed by the new module
`.../ContCohomology/LowDegreeOne.lean`, which is sorry-free:

* a degree-`1` homogeneous cochain is an element `f` of
  `↥((homogeneousCochains X).X 1)` — the `G`-invariants of
  `C(G, C(G, M))` — and `eval₁ X f x := f 1 x` is the inhomogeneous
  cochain, continuous by `continuous_eval₁`;
* the differentials unfold to `(d X 1 F) g h = F h - F g` and
  `(d X 2 f) g h l = f h l - f g l + f g h`
  (`homogeneousCochains_d_one_two_apply`), so the cocycle relation at
  `g₀ = 1` gives `f h l = eval₁ f l - eval₁ f h` (`cocycle_apply`);
* `G`-invariance reads `f (σ x) (σ y) = ρ σ (f x y)`
  (`homogeneousCochains_apply_smul`), and the two together give the
  CROSSED-HOMOMORPHISM IDENTITY
  `eval₁ f (g h) = eval₁ f g + ρ g (eval₁ f h)` (`eval₁_mul`), with
  `eval₁_one`, `eval₁_inv`, `eval₁_conj` as consequences;
* `eval₁_mem_range_sub_conj` is the conjugation stability of the
  surviving locus, and `exists_cocycleClass_eq` is surjectivity of
  `cocycleClass` (from `TopModuleCat.cokerπ_surjective` upstream).

That module is reusable beyond this leaf: `Sha1Twist`'s docstring in
`HardlyRamified/Deformation.lean` records the same gap.

With it, `survivingLocus` above is definable, its conjugation stability is
PROVEN (`survivingLocus_conj`), and what remains open is exactly the two
halves of DDT 2.48 — the global nonemptiness step and the local
computation at `q` — as the two named leaves above.

Both-ways audit, inherited verbatim from
`exists_taylorWilesPrime_locResDecomp_ne_zero`: at the intended
instantiation this is the cited Taylor–Wiles separation lemma;
abstractly the hypothesis set contains the classically unsatisfiable
irreducible hardly ramified `ρbar`, so the statement is classically true
outright and CANNOT be false as stated.  CIRCULARITY GUARD: for that very
reason it must not be discharged through
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible`, `Family.lean` or anything
downstream of them — a proof ending in `exfalso` on `hirr` is the
circular discharge and is BANNED. -/
theorem exists_separatingOpen_locResDecomp.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ)
    {c : continuousCohomology 1 (adZeroTwist p ρbar)}
    (hcunr : c ∈ h1TwistUnramified p ρbar) (hc0 : c ≠ 0) :
    ∃ V : Set (Field.absoluteGaloisGroup ℚ),
      IsOpen V ∧
      (∀ g x : Field.absoluteGaloisGroup ℚ, x ∈ V → g * x * g⁻¹ ∈ V) ∧
      (V ∩ taylorWilesLocus p ρbar n).Nonempty ∧
      ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
        globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ∈ V →
        c ∉ LinearMap.ker (locResDecompTwist1 p ρbar
          hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap := by
  obtain ⟨z, hzc⟩ :=
    ContinuousCohomology.exists_cocycleClass_eq (X := adZeroTwist p ρbar) 1 c
  obtain ⟨hzopen, hzmeet⟩ :=
    isOpen_survivingLocus_and_meets_taylorWilesLocus hpodd hW hρbar hirr n z hzc hcunr hc0
  exact ⟨survivingLocus p ρbar z, hzopen,
    fun g x hx => survivingLocus_conj p ρbar z g x hx, hzmeet,
    fun q hq hq2 hqp hmem =>
      notMem_ker_locResDecompTwist1_of_mem_survivingLocus p ρbar z hzc hcunr q hq hq2 hqp hmem⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev separation of a single dual-Selmer class by a
Taylor–Wiles prime — DDT Lemma 2.48** (cut out 2026-07-27 as the second
of the two inputs of DDT Thm. 2.49; **PROVEN 2026-07-28** over the single
leaf `exists_separatingOpen_locResDecomp` above): given a NONZERO class
`c ∈ H¹(ℚ, ad⁰ρbar(1))` unramified outside `{2, p}` and a level `n`,
there is a Taylor–Wiles prime `q` at that level — `q ≡ 1 (mod p^n)` with
`ρbar(Frob_q)` having two distinct eigenvalues — at which `c` does NOT
die locally.

This is the exact strengthening of `exists_taylorWilesPrime` above by the
one cohomological clause it lacks, and it is the only genuinely arithmetic
input of the descent: everything else in
`exists_taylorWilesPrimeSet_core` below is a dimension count.

# WHAT IS PROVEN HERE, AND WHAT MOVED TO THE LEAF (2026-07-28)

The proof below is the CHEBOTAREV EXTRACTION and nothing else, in the
shape `exists_taylorWilesPrime` above already uses:

* the leaf supplies an open, conjugation-stable `V` meeting
  `taylorWilesLocus p ρbar n`, at whose Frobenii `c` survives;
* `isOpen_taylorWilesLocus` makes `V ∩ taylorWilesLocus` open and the
  leaf makes it nonempty, so `dense_conjClasses_globalFrob` — applied
  away from the two places `2` and `p` — puts a Frobenius CONJUGATE
  `g · Frob_q · g⁻¹` inside it;
* conjugating back by `g⁻¹` (both `V` and `taylorWilesLocus` are
  conjugation-stable, the latter by `taylorWilesLocus_conj`) puts
  `Frob_q` itself inside it — which is what makes this proof shorter
  than `exists_taylorWilesPrime`'s, where the two conditions had to be
  transported one at a time;
* membership in `taylorWilesLocus` then reads off as the two arithmetic
  conditions exactly as there: `cyclotomicCharacter_globalFrob` plus
  `hζ.pow_inj` turn "fixes `μ_{p^n}`" into `q ≡ 1 (mod p^n)`, and
  `charFrob_eq_charpoly_globalFrob` turns the charpoly clause into the
  `charFrob` one.

The two excluded places are `2` and `p`: `p` because Chebotarev's
Frobenius must be unramified for the cyclotomic character, and `2`
because the leaf's local computation needs `q ∉ hardlyRamifiedPlaces p`,
i.e. needs `c` to be unramified at `q`.  Excluding them costs nothing —
they are two places out of a dense family.

# ROUTE (Wiles, Ann. of Math. 141 (1995) ch. 3; DDT §2, Lemma 2.48)

Let `L = ℚ(ad⁰ρbar(1), μ_{p^n})` be the field cut out by `ρbar` and the
`p^n`-th roots of unity, and let `L_c/L` be the extension cut out by the
restriction of `c` (which is a HOMOMORPHISM on `Γ L`, since the action
there is trivial).  `c ≠ 0` and the unramifiedness make `L_c ≠ L`.  One
shows the set of `σ ∈ Γ ℚ` with (i) `σ` fixing `μ_{p^n}`, (ii) `ρbar(σ)`
regular semisimple with distinct eigenvalues, and (iii)
`c(σ) ∉ (σ − 1)·ad⁰ρbar(1)` is a nonempty union of conjugacy classes in
`Gal(L_c/ℚ)`; Chebotarev then produces infinitely many `q` with `Frob_q`
in it, and at such a `q` the local restriction of `c` is nonzero because
the unramified local cohomology at `q` is `M/(Frob_q − 1)M`.  The
nonemptiness step is where `ρbar|_{ℚ(ζ_p)}` absolutely irreducible is
used classically (it forces `H¹(Gal(L/ℚ), ad⁰ρbar(1)) = 0`, so `c` does
not already vanish on `Γ L`); at the intended instantiation the hardly
ramified package supplies it, and deriving it from
`IsHardlyRamified hpodd hW ρbar` together with `hirr` for odd `p` is part
of this leaf's obligation.

Everything the SHAPE of the argument needs is already proven in this
file: `exists_fixing_rootsOfUnity_charpoly_split` supplies (i) + (ii) at
a single Galois element, `dense_conjClasses_globalFrob` is the Chebotarev
density input, and `exists_taylorWilesPrime` above is the assembly of
exactly those two.  What is new here is the third, cohomological
condition and the local computation at `q` — and those two, and ONLY
those two, are what `exists_separatingOpen_locResDecomp` above now
carries.

Both-ways audit, verbatim from `exists_taylorWilesPrimeSet` below: at the
intended instantiation this is the cited Taylor–Wiles separation lemma;
abstractly the hypothesis set contains the classically unsatisfiable
irreducible hardly ramified `ρbar`, so the statement is classically true
outright and CANNOT be false as stated.  CIRCULARITY GUARD: for that very
reason it must not be discharged through
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible`, `Family.lean` or anything
downstream of them — a proof ending in `exfalso` on `hirr` is the
circular discharge and is BANNED. -/
theorem exists_taylorWilesPrime_locResDecomp_ne_zero.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ)
    {c : continuousCohomology 1 (adZeroTwist p ρbar)}
    (hcunr : c ∈ h1TwistUnramified p ρbar) (hc0 : c ≠ 0) :
    ∃ (q : ℕ) (hq : q.Prime),
      q ≡ 1 [MOD p ^ n] ∧
      (∃ α β : k, α ≠ β ∧
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) ∧
      c ∉ LinearMap.ker (locResDecompTwist1 p ρbar
        hq.toHeightOneSpectrumRingOfIntegersRat).hom.toLinearMap := by
  classical
  -- the separating locus, and the Taylor–Wiles locus it meets
  obtain ⟨V, hVopen, hVconj, ⟨σ, hσV, hσT⟩, hVsep⟩ :=
    exists_separatingOpen_locResDecomp hpodd hW hρbar hirr n hcunr hc0
  have hUopen : IsOpen (V ∩ taylorWilesLocus p ρbar n) :=
    hVopen.inter (isOpen_taylorWilesLocus p ρbar n)
  -- Chebotarev density away from the two bad places `2` and `p`
  have hdense := dense_conjClasses_globalFrob (K := ℚ)
    (insert Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
      (insert (Fact.out : p.Prime).toHeightOneSpectrumRingOfIntegersRat (∅ : Finset _)))
  obtain ⟨x, hxU, hxfrob⟩ := hdense.inter_open_nonempty _ hUopen ⟨σ, hσV, hσT⟩
  obtain ⟨v, hvS, g, rfl⟩ := hxfrob
  obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hvS (Finset.mem_insert_self _ _)
  have hqp : q ≠ p := by
    rintro rfl
    exact hvS (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hxV, hxT⟩ := hxU
  -- conjugating back by `g⁻¹` moves the CONJUGATE that density supplies
  -- to `Frob_q` itself, in both loci at once
  have hconjinv : g⁻¹ * (g * globalFrob hq.toHeightOneSpectrumRingOfIntegersRat * g⁻¹)
      * g⁻¹⁻¹ = globalFrob hq.toHeightOneSpectrumRingOfIntegersRat := by group
  have hFV : globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ∈ V := by
    have h := hVconj g⁻¹ _ hxV
    rwa [hconjinv] at h
  have hFT : globalFrob hq.toHeightOneSpectrumRingOfIntegersRat ∈
      taylorWilesLocus p ρbar n := by
    have h := taylorWilesLocus_conj p ρbar n g⁻¹ hxT
    rwa [hconjinv] at h
  obtain ⟨hfrobfix, α, β, hαβ, hpoly⟩ := hFT
  -- `q ≡ 1 (mod p^n)`: the `p`-adic cyclotomic character takes the value
  -- `q` at `Frob_q`, and `Frob_q` fixes a primitive `p^n`-th root of unity
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
      have h1lt : 1 < p ^ n := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
      have hval : ((q : ZMod (p ^ n))).val = 1 := hζ.pow_inj (ZMod.val_lt _) h1lt hz
      show q % p ^ n = 1 % p ^ n
      rw [Nat.mod_eq_of_lt h1lt, ← ZMod.val_natCast]
      exact hval
  refine ⟨q, hq, hmod, ⟨α, β, hαβ, ?_⟩, hVsep q hq hq2 hqp hFV⟩
  rw [GaloisRep.charFrob_eq_charpoly_globalFrob]
  exact hpoly

/-- **The dual-Selmer-killing core — DDT Thm. 2.49** (PROVEN 2026-07-27
over the two leaves above, replacing the internal sorried `have hcore` of
`exists_taylorWilesPrimeSet` below): at every level `n` there is a
Taylor–Wiles set `Q` of at most `dim_k H¹_{unr outside {2,p}}(ℚ,
ad⁰ρbar(1))` primes for which that whole space dies, i.e. satisfying the
dual-Selmer clause.  The bound is LEVEL-INDEPENDENT because
`h1TwistUnramified` does not mention `n`, which is exactly what the
tower downstream needs (it consumes one `q` at every level).

# THE ARGUMENT, AND WHY IT IS A DIMENSION COUNT

Write `U = h1TwistUnramified p ρbar` and `K Q = h1TwistLocalKer p ρbar Q`.
The dual-Selmer clause of `IsTaylorWilesPrimeSet` says exactly
`U ⊓ K Q = ⊥`.  Descend on `dim_k (U ⊓ K Q)`, which is finite by
`finite_h1TwistUnramified`:

* if `U ⊓ K Q = ⊥` we are done;
* otherwise pick `0 ≠ c ∈ U ⊓ K Q` and let
  `exists_taylorWilesPrime_locResDecomp_ne_zero` produce a Taylor–Wiles
  prime `q` at level `n` with `loc_q c ≠ 0`.  Then `q ∉ Q` — for free,
  since `c` dies at every prime of `Q` and not at `q`, so no bookkeeping
  of an avoid-set is needed — and `U ⊓ K (insert q Q) < U ⊓ K Q`
  strictly, because `c` lies in the right side and not the left.  The
  dimension therefore drops by at least one and the recursion terminates
  after at most `dim_k U` steps.

`≤`, not `=`: a single prime may cut more than one dimension, so the core
can come out SMALLER than `dim_k U`.  That is why
`IsTaylorWilesPrimeSet.exists_card_eq` above takes `Q.card ≤ r`, and it
is the only place the two differ. -/
theorem exists_taylorWilesPrimeSet_core.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) (n : ℕ) :
    ∃ Q : Finset ℕ,
      Q.card ≤ Module.finrank k ↥(h1TwistUnramified p ρbar) ∧
      IsTaylorWilesPrimeSet p ρbar n Q := by
  classical
  haveI hfin : Module.Finite k ↥(h1TwistUnramified p ρbar) :=
    finite_h1TwistUnramified p ρbar
  suffices H : ∀ d : ℕ, ∀ Q : Finset ℕ,
      (∀ q ∈ Q, ∃ hq : q.Prime, q ≡ 1 [MOD p ^ n] ∧ ∃ α β : k, α ≠ β ∧
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) →
      Module.finrank k ↥(h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q) ≤ d →
      ∃ Q' : Finset ℕ, Q'.card ≤ Q.card + d ∧ IsTaylorWilesPrimeSet p ρbar n Q' by
    obtain ⟨Q, hcard, hQ⟩ :=
      H (Module.finrank k ↥(h1TwistUnramified p ρbar)) ∅ (by simp)
        (Submodule.finrank_mono inf_le_left)
    exact ⟨Q, by simpa using hcard, hQ⟩
  intro d
  induction d with
  | zero =>
    intro Q hQloc hrank
    refine ⟨Q, by omega, hQloc, ?_⟩
    haveI : FiniteDimensional k ↥(h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have hbot : h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q = ⊥ :=
      Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
    intro c hunr hloc
    have hc : c ∈ h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q :=
      Submodule.mem_inf.mpr ⟨(mem_h1TwistUnramified ρbar).mpr hunr,
        (mem_h1TwistLocalKer ρbar Q).mpr hloc⟩
    rw [hbot, Submodule.mem_bot] at hc
    exact hc
  | succ d ih =>
    intro Q hQloc hrank
    by_cases hbot : h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q = ⊥
    · refine ⟨Q, by omega, hQloc, ?_⟩
      intro c hunr hloc
      have hc : c ∈ h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q :=
        Submodule.mem_inf.mpr ⟨(mem_h1TwistUnramified ρbar).mpr hunr,
          (mem_h1TwistLocalKer ρbar Q).mpr hloc⟩
      rw [hbot, Submodule.mem_bot] at hc
      exact hc
    · obtain ⟨c, hcmem, hc0⟩ := (Submodule.ne_bot_iff _).mp hbot
      obtain ⟨hcU, hcQ⟩ := Submodule.mem_inf.mp hcmem
      obtain ⟨q, hq, hqmod, hqsplit, hqne⟩ :=
        exists_taylorWilesPrime_locResDecomp_ne_zero hpodd hW hρbar hirr n hcU hc0
      -- `q ∉ Q` for free: `c` dies at every prime of `Q` and not at `q`
      have hqQ : q ∉ Q := fun hmem =>
        hqne ((mem_h1TwistLocalKer ρbar Q).mp hcQ q hmem hq)
      have hloc' : ∀ q' ∈ insert q Q, ∃ hq' : q'.Prime, q' ≡ 1 [MOD p ^ n] ∧
          ∃ α β : k, α ≠ β ∧
            ρbar.charFrob hq'.toHeightOneSpectrumRingOfIntegersRat =
              (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) := by
        intro q' hq'
        rcases Finset.mem_insert.mp hq' with rfl | hmem
        · exact ⟨hq, hqmod, hqsplit⟩
        · exact hQloc q' hmem
      haveI : FiniteDimensional k ↥(h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q) :=
        Submodule.finiteDimensional_of_le inf_le_left
      have hlt : h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar (insert q Q)
          < h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar Q := by
        refine lt_of_le_of_ne
          (inf_le_inf_left _ (h1TwistLocalKer_anti ρbar (Finset.subset_insert q Q))) ?_
        intro heq
        have hcmem' : c ∈ h1TwistUnramified p ρbar ⊓ h1TwistLocalKer p ρbar (insert q Q) := by
          rw [heq]; exact hcmem
        exact hqne ((mem_h1TwistLocalKer ρbar _).mp (Submodule.mem_inf.mp hcmem').2 q
          (Finset.mem_insert_self q Q) hq)
      have hdrop := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨Q', hcard', hQ'⟩ := ih (insert q Q) hloc' (by omega)
      refine ⟨Q', ?_, hQ'⟩
      rw [Finset.card_insert_of_notMem hqQ] at hcard'
      omega

/-- **Existence of Taylor–Wiles prime sets** (patching leaf 1; RE-OPENED
2026-07-27 by the dual-Selmer repair of `IsTaylorWilesPrimeSet` above and
**RE-CLOSED the same day** by the decomposition immediately above — it is
again sorry-free, now over the two named leaves `finite_h1TwistUnramified`
and `exists_taylorWilesPrime_locResDecomp_ne_zero`): for the irreducible hardly
ramified residual `ρbar` there is a LEVEL-INDEPENDENT `q0` such that at
every level `n` and every size `r ≥ q0` there is a Taylor–Wiles set of
exactly `r` primes.

# WHAT CHANGED, AND WHY THE STATEMENT NEEDED A LOWER BOUND

The old statement produced sets of size at least `r` for EVERY `r`,
including `r = 0`.  Under the repaired predicate that is FALSE at small
`r`: no set of fewer than `dim_k` of the unramified-outside-`{2, p}` part
of `H¹(ℚ, ad⁰ρbar(1))` primes can cut a group of that dimension to zero,
one prime killing at most one dimension.  So the lower bound `q0 ≤ r` is
not a convenience, it is what makes the statement true; and `q0` must be
independent of `n` because the tower consumes ONE `q` at every level.

# HOW IT IS PROVEN, AND WHERE THE OPEN WORK NOW LIVES

The value taken for `q0` is `dim_k H¹_{unr outside {2,p}}(ℚ, ad⁰ρbar(1))`
= `Module.finrank k ↥(h1TwistUnramified p ρbar)`, the Taylor–Wiles number,
and the proof is two lines:

* `exists_taylorWilesPrimeSet_core` (DDT Thm. 2.49) builds, at each level
  `n`, a Taylor–Wiles set of at most `q0` primes satisfying the
  dual-Selmer clause, by descending on the dimension of
  `h1TwistUnramified ⊓ h1TwistLocalKer Q` one prime at a time;
* `IsTaylorWilesPrimeSet.exists_card_eq` pads it up to the exact size
  `r ≥ q0` by `IsTaylorWilesPrimeSet.exists_insert`, i.e. by adjoining
  fresh Taylor–Wiles primes from the Chebotarev extraction
  `exists_taylorWilesPrime`.  This is the old (2026-07-24) proof's
  content, in the only direction that remains sound: ENLARGING preserves
  the predicate, SHRINKING does not.

The internal sorried `have hcore` this declaration carried between those
two dates has been HOISTED into two named, separately dispatchable leaves
— an unnamed `have` can be owned by nobody — and they are exactly the two
inputs DDT Thm. 2.49 needs and this tree lacked:

* `finite_h1TwistUnramified` — finiteness of the unramified-outside-`S`
  part of `H¹(ℚ, ad⁰ρbar(1))` (Hermite–Minkowski; the "`G_{ℚ,{2,p}}` is
  small" half of it is ALREADY PROVEN here, as
  `finite_setOf_subgroup_inertiaAt_le` in
  `HardlyRamified/HermiteMinkowski.lean`);
* `exists_taylorWilesPrime_locResDecomp_ne_zero` — the Chebotarev
  separation of a single class, DDT Lemma 2.48.

Note that neither needs Poitou–Tate or the local Tate pairing — see the
deviation note on `IsTaylorWilesPrimeSet`.  Note also that this
declaration is `≤ q0`-shaped through the core rather than `= q0`-shaped:
one prime may cut more than one dimension of the dual-Selmer source.

Both-ways audit: at the intended instantiation this is the cited
Taylor–Wiles prime existence; abstractly the hypothesis set contains
the classically unsatisfiable irreducible hardly ramified `ρbar`
(section audit of `Interface.lean`), so the statement is also
classically true outright.  CIRCULARITY GUARD (inherited from pillar
3b, and INHERITED IN TURN BY THE TWO LEAVES ABOVE): must not be proven
through `Family.lean` or anything downstream of it. -/
theorem exists_taylorWilesPrimeSet.{uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hρbar : IsHardlyRamified hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible) :
    ∃ q0 : ℕ, ∀ n r : ℕ, q0 ≤ r →
      ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q := by
  classical
  -- `q0` is the TAYLOR–WILES NUMBER, level-independent by construction.
  refine ⟨Module.finrank k ↥(h1TwistUnramified p ρbar), fun n r hr => ?_⟩
  -- the dual-Selmer-killing CORE, of size at most `q0` (DDT Thm. 2.49) …
  obtain ⟨Q, hcard, hQ⟩ := exists_taylorWilesPrimeSet_core hpodd hW hρbar hirr n
  -- … padded up to the exact size `r ≥ q0 ≥ #Q`.
  exact IsTaylorWilesPrimeSet.exists_card_eq hpodd hW hρbar hirr n r Q hQ
    (hcard.trans hr)

/-- **Exact-size Taylor–Wiles prime supply, in the order the tower
consumes it** (PROVEN): the argument order of the supply produced by
`exists_taylorWilesPrimeSet` is `(n, r)`; the tower's `hTWq` is written
`(r, n)`.  This adapter is the swap, and nothing else.

# WHAT THIS DECLARATION USED TO DO, AND WHY THAT IS NOW UNSOUND

Until 2026-07-27 it converted a supply of sets of size AT LEAST `r` into
one of size EXACTLY `r`, by `Finset.exists_subset_card_eq` — it SHRANK a
supplied `Q`.  That was sound while `IsTaylorWilesPrimeSet` was a
`∀ q ∈ Q` condition, hence subset-closed.  With the dual-Selmer clause it
is not: the global conjunct is MONOTONE INCREASING in `Q`, so a subset of
a Taylor–Wiles set is in general not one, and the shrunk statement is
outright FALSE for `r` below the Taylor–Wiles number.  The supply
therefore carries the lower bound `q0 ≤ r` instead, and the exact size is
reached by ENLARGING (`IsTaylorWilesPrimeSet.exists_insert`) rather than
by cutting down.

This is the same `q0` the standing hazard on
`exists_taylorWilesBottomPresentation` prescribes: Cohen's number of
generators may sit BELOW the Taylor–Wiles number, and the correct value
is `max` of the two.  Threading `q0` from here is what finally makes that
`max` expressible. -/
theorem exists_taylorWilesPrimeSet_card_eq.{uK, uW} (p : ℕ) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W)
    (hTW : ∃ q0 : ℕ, ∀ n r : ℕ, q0 ≤ r →
      ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
    ∃ q0 : ℕ, ∀ r n : ℕ, q0 ≤ r →
      ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q := by
  obtain ⟨q0, h⟩ := hTW
  exact ⟨q0, fun r n hr => h n r hr⟩

/-- **The residual input of Taylor–Wiles patching** (ADDED 2026-07-26
as the cut-level repair of the circular discharge recorded at
`exists_taylorWilesBottomLevel` below): the properties of the residual
representation `ρbar` that the Taylor–Wiles argument actually consumes,
separated from the FLT-specific hardly ramified package.

Two fields, both taken verbatim from `IsHardlyRamified` (whose
projections `det` and `isUnramified` supply them directly, which is how
`exists_taylorWilesTower` below instantiates this):

* `det` — the determinant is the `p`-adic cyclotomic character.  This is
  the ODDNESS input: it is what makes `dim H¹ − dim H¹_dual` come out
  right in Wiles's product formula, and what makes the Taylor–Wiles
  primes exist at all (`exists_fixing_rootsOfUnity_charpoly_split`).
* `isUnramified` — `ρbar` is unramified outside `{2, p}`, so the Selmer
  and dual Selmer groups of `ad⁰ρbar` are finite and the numerology of
  ingredient 1 is available.

**WHAT IS DELIBERATELY ABSENT, AND WHY** (this is the whole point of the
definition).  `IsHardlyRamified` has two further fields, `isFlat` (at
`p`) and `isTameAtTwo`.  Together with irreducibility those two are
exactly what the tree REFUTES, for every odd prime — at `p = 3` through
`IsHardlyRamified.mod_three_reducible`, at `p ≥ 5` through
`not_isIrreducible_of_isHardlyRamified_of_five_le`.  A patching leaf
carrying the full package therefore has an unsatisfiable hypothesis set
and can be discharged from `False`; see the RE-OPENING section of
`exists_taylorWilesBottomLevel`.  The Taylor–Wiles method does not use
either field — the local conditions at `2` and `p` enter only through
the deformation problem, which the patching leaves receive abstractly
through `IsWeaklyUniversalDeformation` — so dropping them costs the
leaves nothing mathematically and removes the free proof.

This weakening is CLASSICALLY EMPTY, which is why it is safe: in the
hypothesis package of either leaf, `ρT` is hardly ramified over `T` and
reduces to `ρbar` on Frobenius traces away from a finite set, so any
`ρbar` to which the leaves are ever applied is hardly ramified anyway.
What changes is only that the leaf can no longer HELP ITSELF to that
fact, since deriving it needs Brauer–Nesbitt/Chebotarev plus a
reduction-descent theorem for flatness and tameness that this tree does
not have.

Instances mirror `IsHardlyRamified`'s, so `hres := ⟨h.det, fun q hq h2
hp => h.isUnramified q hq ⟨h2, hp⟩⟩` typechecks for any
`h : IsHardlyRamified hpodd hdim ρbar`. -/
structure IsTaylorWilesResidual {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type*} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    [IsLocalRing k] [Algebra ℤ_[p] k]
    {W : Type*} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (hdim : Module.rank k W = 2)
    (ρbar : GaloisRep ℚ k W) : Prop where
  /-- The determinant is the `p`-adic cyclotomic character (oddness). -/
  det : ∀ g, ρbar.det g =
    algebraMap ℤ_[p] k
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv)
  /-- `ρbar` is unramified outside `{2, p}`. -/
  isUnramified : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ p →
    ρbar.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat

/-
HOISTED 2026-07-27 to `Modularity/PatchingCore.lean` (immediately after
`taylorWilesAug`, VERBATIM and at unchanged fully qualified names):
`taylorWilesLevelIdeal`, `taylorWilesLevelIdeal_le_aug`,
`onePlus_pow_prime_sub_one_mem`, `onePlus_pow_primePow_sub_one_mem` and
`taylorWilesLevelIdeal_le_maximalIdeal_pow`.

They are pure commutative algebra over `Λ = ℤ_p[[S₁,…,S_q]]` — no base field,
no Galois representation, no Hecke algebra — and the `F`-level twin of the
level-wise cut (`exists_hilbertTaylorWilesLevelRaw` in
`HardlyRamified/HilbertModularity.lean`) needs exactly the same two `bIdeal`
bounds.  That file is a transitive IMPORT of this one
(`Patching → KhareWintenberger → Deformation → HilbertModularity`), so the
copies here were out of its reach; `PatchingCore` sits below both.  This file
imports `PatchingCore`, so every consumer below sees the names unchanged.
-/

open scoped Classical in
/-- **A padded finite generating family for `𝔪_R`** (PROVEN 2026-07-27;
helper for the Cohen decomposition below): in a Noetherian local ring,
for EVERY `q₀` there is a `q ≥ q₀` and a family `t : Fin q → R` whose
range spans `𝔪_R`.

The padding is the whole point and it is free: `𝔪_R` is finitely
generated because `R` is Noetherian (`Ideal.fg_of_isNoetherianRing`), and
extra generators may be taken to be `0`, which changes neither the span
(`Submodule.span_insert_zero`) nor anything downstream.  This is what
makes the `q₀ ≤ q` clause of
`exists_taylorWilesCoefficientsPresentation` — the Taylor–Wiles padding
hazard recorded in the FORMAL-CONTENT AUDIT of
`exists_taylorWilesBottomPresentation` — cost nothing to honour: one
never has to return the MINIMAL number of generators of `𝔪_R`. -/
theorem exists_fin_span_range_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (q₀ : ℕ) :
    ∃ (q : ℕ) (t : Fin q → R), q₀ ≤ q ∧
      Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R := by
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)
  refine ⟨q₀ + s.card, fun i => if h : (i : ℕ) < s.card then
    ((s.equivFin.symm ⟨(i : ℕ), h⟩ : { x // x ∈ s }) : R) else 0, Nat.le_add_right _ _, ?_⟩
  set t : Fin (q₀ + s.card) → R := fun i => if h : (i : ℕ) < s.card then
    ((s.equivFin.symm ⟨(i : ℕ), h⟩ : { x // x ∈ s }) : R) else 0 with ht
  have hsub : Set.range t ⊆ insert (0 : R) (s : Set R) := by
    rintro _ ⟨i, rfl⟩
    by_cases h : (i : ℕ) < s.card
    · exact Set.mem_insert_of_mem _ (by simp only [ht, dif_pos h]; exact
        (s.equivFin.symm ⟨(i : ℕ), h⟩).2)
    · simp [ht, dif_neg h]
  have hsup : (s : Set R) ⊆ Set.range t := by
    intro x hx
    refine ⟨⟨(s.equivFin ⟨x, hx⟩ : ℕ), ?_⟩, ?_⟩
    · exact lt_of_lt_of_le (s.equivFin ⟨x, hx⟩).2 (Nat.le_add_left _ _)
    · have h : ((s.equivFin ⟨x, hx⟩ : Fin s.card) : ℕ) < s.card := (s.equivFin ⟨x, hx⟩).2
      simp only [ht, dif_pos h]
      have : (⟨((s.equivFin ⟨x, hx⟩ : Fin s.card) : ℕ), h⟩ : Fin s.card) =
          s.equivFin ⟨x, hx⟩ := rfl
      rw [this, Equiv.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · rw [← hs]
    calc Ideal.span (Set.range t) ≤ Ideal.span (insert (0 : R) (s : Set R)) :=
          Ideal.span_mono hsub
      _ = Ideal.span (s : Set R) := Submodule.span_insert_zero
  · rw [← hs]
    exact Ideal.span_mono hsup

/-- **The substitution homomorphism into a complete local ring exists**
(PROVEN 2026-07-27; the CONVERGENCE half of Cohen's structure theorem,
and it turned out to need no new theory at all): for `R` local and
`𝔪_R`-adically complete, ANY ring map `ι : O →+* R` and ANY family
`t : Fin q → R` of elements of `𝔪_R` extend to a ring homomorphism
`φ : O[[x_1, …, x_q]] →+* R` with `φ (C a) = ι a` and `φ (X i) = t i`.

Note there is NO topological hypothesis on `O`: the proof gives `O` the
DISCRETE uniformity, which makes `ι` continuous for free
(`continuous_of_discreteTopology`), and that is legitimate because a
power series in the `t_i` converges on the strength of the `t_i` alone.
This is why the leaf is stated for an arbitrary `O` rather than for the
`TaylorWilesCoefficients` bundle: the coefficient ring's own topology
plays no role here.

PROOF (as written).  `WithIdeal R := ⟨𝔪_R⟩` installs the `𝔪`-adic
topology on `R` together with its uniformity, `NonarchimedeanRing`,
`IsUniformAddGroup` and `IsLinearTopology` instances (all of them
`priority 100` instances of `WithIdeal` in
`Mathlib/Topology/Algebra/Nonarchimedean/AdicTopology.lean`).
`IsAdic.isAdicComplete_iff` — the bridge added in
`Mathlib/RingTheory/AdicCompletion/Topology.lean` — turns `hcomplete`
into `CompleteSpace R` and `T2Space R`, which is exactly the hypothesis
package of `MvPowerSeries.eval₂Hom`.  `HasEval t` needs each `t i`
topologically nilpotent — `WithIdeal.isTopologicallyNilpotent_of_mem`
applied to `ht i` — and `t → 0` along the cofinite filter, which is
vacuous because `Fin q` is finite.  The two defining identities are then
`MvPowerSeries.eval₂_C` and `MvPowerSeries.eval₂_X` transported through
`MvPowerSeries.coe_eval₂Hom`.

CORRECTION to the earlier MISSING MACHINERY note (which said to reuse
`MvPowerSeries.subst`): `subst` maps into another power series ring,
never into an abstract complete ring, so it is the wrong tool.
`MvPowerSeries.eval₂Hom` is the right one, and it is `subst`'s own
underlying construction. -/
theorem exists_ringHom_mvPowerSeries_of_isAdicComplete
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {O : Type*} [CommRing O] (ι : O →+* R)
    {q : ℕ} (t : Fin q → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ∃ φ : MvPowerSeries (Fin q) O →+* R,
      (∀ a : O, φ (MvPowerSeries.C a) = ι a) ∧
      (∀ i, φ (MvPowerSeries.X i) = t i) := by
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  letI : UniformSpace O := ⊥
  have hadicR : IsAdic (R := R) (IsLocalRing.maximalIdeal R) := rfl
  obtain ⟨hcs, ht2⟩ := hadicR.isAdicComplete_iff.mp hcomplete
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hev : MvPowerSeries.HasEval t := by
    constructor
    · intro s
      exact WithIdeal.isTopologicallyNilpotent_of_mem (ht s)
    · simp
  refine ⟨MvPowerSeries.eval₂Hom hcont hev, ?_, ?_⟩
  · intro a
    rw [MvPowerSeries.coe_eval₂Hom hcont hev]
    exact MvPowerSeries.eval₂_C _ _ _
  · intro i
    rw [MvPowerSeries.coe_eval₂Hom hcont hev]
    exact MvPowerSeries.eval₂_X _ _ _

/-- **Cohen's COEFFICIENT RING, with its map into `R`** (sorry node,
LEAF B1a-i of the 2026-07-27 decomposition of
`exists_taylorWilesCoefficientsPresentation`; this is the substantial
half): for `R` local and `𝔪_R`-adically complete with finite residue
field `k`, there is a `TaylorWilesCoefficients` `𝒪` and a ring map
`ι : 𝒪 →+* R` lifting the residue field, i.e. with `π ∘ ι` surjective.

Classically `𝒪 = W(k)`, the Witt vectors of `k` (Cohen 1946; Matsumura,
*Commutative Ring Theory*, Thm. 29.1–29.4; Eisenbud, *Commutative
Algebra*, Thm. 7.7).  `k` is finite hence perfect of characteristic `p`,
so `W(k)` is the unique absolutely unramified complete DVR with residue
field `k`, and it is formally smooth over `ℤ_p`; since `R` is
`𝔪_R`-adically complete and `p ∈ 𝔪_R`, the map `W(k) → R` is built by
lifting `k = R/𝔪_R` successively through `R/𝔪_R^{n+1} ↠ R/𝔪_R^n` and
passing to the limit.  Equivalently, and this is usually the cheaper
formalisation: the Teichmüller section `k → R` obtained from
`x ↦ lim_n (x̃_n)^{p^n}` (well defined by completeness and perfectness)
is multiplicative, and `W(k)`'s universal property in the OTHER
direction from `WittVector.lift` — a multiplicative section of
`R ↠ k` induces `W(k) → R` — is what has to be written.

WHAT IS OWED, precisely.  Two independent obligations:

1. **The bundle.** `W(k)` must be exhibited as a `TaylorWilesCoefficients`.
   `carrier` is declared `Type`, so a universe-`0` copy of `k` is needed
   first; `k` is finite, so `k ≃ Fin (Nat.card k)` transports the field
   structure into `Type 0` and this costs nothing.  Then:
   `IsLocalRing`, `IsNoetherianRing` and `exists_isRegular_maximalIdeal`
   come from `WittVector.isDiscreteValuationRing`
   (`Mathlib/RingTheory/WittVector/DiscreteValuationRing.lean:149`) —
   copy the pattern of `exists_isRegular_ofList_eq_maximalIdeal_padicInt`
   in `PatchingCore.lean`, which discharges exactly this field for
   `ℤ_[p]`.  `finite_residueField` is `W(k)/p ≃ k`.  The TOPOLOGICAL
   half (`TopologicalSpace`, `IsTopologicalRing`, `CompactSpace`,
   `T2Space`, `TotallyDisconnectedSpace`) should be taken to be the
   `p`-adic i.e. `𝔪`-adic topology — `WithIdeal (W k) := ⟨𝔪⟩` supplies
   the first two instantly — and compactness/total disconnectedness
   follow from `W(k) = lim W_n(k)` being an inverse limit of FINITE
   rings (`WittVector.TruncatedWittVector` is finite for `k` finite).
   `Algebra.TopologicallyFG ℤ (W k)` holds because `W(k) = ℤ_p[ζ]` is
   the closure of `ℤ[ζ]` for `ζ` a Teichmüller lift of a generator of
   `kˣ`; compare `topologicallyFG_int_padicInt`.
2. **The lift `ι : W(k) →+* R`.** This is the genuinely missing theorem.
   Mathlib's `WittVector.lift` maps *into* `𝕎 k` and is therefore the
   wrong direction, as the earlier note correctly recorded.

MISSING MACHINERY (re-checked 2026-07-27 against our pin, `~/cs/FLT` and
`Fermat/FLT/Mathlib/`; the refuting check for each is a grep for the
name):

* **Cohen's structure theorem is absent from mathlib.** The only file
  matching `Cohen` is `Mathlib/RingTheory/Noetherian/OfPrime.lean`,
  which is Cohen's *other* theorem ("Noetherian iff every prime is
  finitely generated") and is unrelated.
  `grep -rln 'Cohen' .lake/packages/mathlib/Mathlib ~/cs/FLT Fermat`
* The coefficient-ring map `W(k) → R` is absent from all three trees.

WHAT IS **NOT** OWED ANY MORE, and this is the correction that shrank
this leaf.  The convergence and surjectivity halves of Cohen have been
split off and are NOT part of this leaf:
`exists_ringHom_mvPowerSeries_of_isAdicComplete` (PROVEN above) builds
the substitution homomorphism, and
`surjective_of_span_range_eq_maximalIdeal` (below) is its surjectivity.
Neither needs Witt vectors.

FAITHFULNESS.  The statement asks only for SOME coefficient ring lifting
the residue field; it does not pin `𝒪 = W(k)`, and it must not, because
`TaylorWilesCoefficients` is a bundle rather than a characterisation.  A
prover is free to return any DVR bundle that maps to `R` and hits `k`.
Note the leaf would be FALSE if `[Finite k]` were dropped: the
`finite_residueField` field of `TaylorWilesCoefficients` forces `𝒪` to
have a finite residue field, and `π ∘ ι` surjective then forces `k`
itself to be finite.

CIRCULARITY GUARD: none applies — this leaf mentions no `ρbar`, no
deformation functor and no Hecke algebra, so no route to the odd-prime
dichotomy can even be stated against it. -/
theorem exists_taylorWilesCoefficients_ringHom
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {k : Type*} [Field k] [Finite k] {π : R →+* k}
    (hπ : Function.Surjective π) :
    ∃ (coeff : TaylorWilesCoefficients) (ι : coeff.carrier →+* R),
      Function.Surjective (π.comp ι) :=
  sorry

/-- **Complete Nakayama: the substitution homomorphism is surjective**
(PROVEN 2026-07-27; was LEAF B1a-ii of the 2026-07-27 decomposition of
`exists_taylorWilesCoefficientsPresentation`): if `ι : O →+* R` hits the
residue field and `t : Fin q → R` spans `𝔪_R`, then ANY ring
homomorphism `φ : O[[x_1, …, x_q]] →+* R` with `φ (C a) = ι a` and
`φ (X i) = t i` is surjective.

# WHY IT IS SAFE TO QUANTIFY OVER AN ARBITRARY `φ`

This looked at first like a faithfulness hazard — `φ` is a BARE
`RingHom` with no continuity hypothesis, so how can it be forced to hit
the limits that surjectivity needs?  The answer is that CONTINUITY IS
AUTOMATIC here, for a purely algebraic reason, and it is the load-bearing
observation of this leaf:

> in finitely many variables, the set of power series all of whose terms
> have total degree `≥ n` is exactly the ideal `(X_1, …, X_q)^n`.

That is an algebraic characterisation, so `φ` — being a ring
homomorphism — must map it into `(φ X_1, …, φ X_q)^n · R = (t_1, …,
t_q)^n · R = 𝔪_R^n` by `hspan`.  So every such `φ` is automatically
`𝔪`-adically continuous, and no continuity hypothesis is needed or
would add anything.

# ROUTE, and it cuts cleanly in two if a successor wants that

* **(a) The approximation step.**  For every `n` and every `r ∈ 𝔪_R^n`
  there is `f ∈ (X_1, …, X_q)^n` with `r - φ f ∈ 𝔪_R^{n+1}`.  Reason:
  `𝔪_R^n` is generated by the degree-`n` monomials in the `t_i`
  (`hspan` plus `Ideal.span_pow`-style bookkeeping), and modulo
  `𝔪_R^{n+1}` the coefficients may be taken in the image of `ι`, since
  `ι` hits `R/𝔪_R ≅ k` by `hι`.  Take `f` to be the corresponding
  degree-`n` polynomial.  Note the refinement `f ∈ (X)^n` — plain
  density `∃ f, r - φ f ∈ 𝔪^n` is NOT enough, because the successive
  approximations must agree to higher and higher order for the limit to
  exist.
* **(b) The limit.**  Iterate (a) from `r₀ := r` to get `f_n ∈ (X)^n`
  with `r - φ (f_0 + ⋯ + f_{n-1}) ∈ 𝔪_R^n`.  The partial sums are
  coefficientwise eventually constant (each `f_n` has no term of degree
  `< n`), so they converge to some `f : O[[x]]`, with
  `f - (f_0 + ⋯ + f_{n-1}) ∈ (X)^n`; applying the observation above,
  `r - φ f ∈ 𝔪_R^n` for every `n`, and `IsHausdorff` — the other half of
  `hcomplete` — gives `r = φ f`.

Both halves are pure commutative algebra over an arbitrary `O`; neither
mentions Witt vectors, so this leaf is independent of
`exists_taylorWilesCoefficients_ringHom` and the two can be worked
concurrently.

# PROOF AS WRITTEN, and the one place it departs from the route above

The whole `X`-degree apparatus of the ROUTE — "order `≥ n` is exactly
`(X_1,…,X_q)^n`", the coefficientwise limit, the eventual constancy of
the partial sums — turned out to be **entirely unnecessary**, and none
of it is in the proof.  It is superseded by a single mathlib instance,

    MvPowerSeries.instIsAdicComplete :
      [Finite σ] → IsAdicComplete (.span (.range X)) (MvPowerSeries σ R)

(`Mathlib/RingTheory/AdicCompletion/Completeness.lean`, and it is
already in this module's import cone — no new `import` was needed).
Its `IsPrecomplete` half hands over the limit `L` of the partial sums
*abstractly*, together with `L - (f_0 + ⋯ + f_{n-1}) ∈ J^n` for
`J := span (range X)`, which is precisely the membership the degree
argument was going to establish by hand.  So a successor must NOT read
the ROUTE above as recording missing machinery: the only genuinely
load-bearing algebraic facts in the finished proof are

* `Ideal.map φ J = 𝔪_R` (from `Ideal.map_span` and `hX`, `hspan`), hence
  `Ideal.map φ (J^n) = 𝔪_R^n` by `Ideal.map_pow` — this is the
  "continuity is automatic" observation in its usable form, and it gives
  `φ '' J^n ⊆ 𝔪_R^n` for free;
* step (a), proved by `Submodule.span_induction` over
  `𝔪_R^n = Ideal.map φ (J^n) = span (φ '' J^n)`: the base case is `φ g`
  itself, and the `R`-scalar case is where `hι` is consumed — a
  coefficient `c` is replaced by `ι a` at the cost of
  `(c - ι a) · φ g ∈ 𝔪_R · 𝔪_R^n = 𝔪_R^{n+1}`;
* `IsHausdorff` (the other half of `hcomplete`) to finish from
  `r - φ L ∈ 𝔪_R^n` for every `n`.

The iteration itself is a `Nat.rec` over pairs `(partial sum, residue)`
whose approximation step is `Classical.choice` applied to (a), guarded
by a `dite` on the invariant so that the recursion is total.

FAITHFULNESS.  `hπ` and `hι` are used only through their consequence
"`ι` hits `R/𝔪_R`"; `k` being a field with `π` surjective is what forces
`RingHom.ker π = 𝔪_R` (`IsLocalRing.ker_eq_maximalIdeal`: the kernel is
maximal, and `R` is local).  `[Finite k]` is deliberately NOT assumed —
it plays no role in this half.  Every hypothesis is consumed; `#print
axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

CIRCULARITY GUARD: none applies, as for the sibling. -/
theorem surjective_of_span_range_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {k : Type*} [Field k] {π : R →+* k} (hπ : Function.Surjective π)
    {O : Type*} [CommRing O] {ι : O →+* R}
    (hι : Function.Surjective (π.comp ι))
    {q : ℕ} {t : Fin q → R}
    (hspan : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal R)
    {φ : MvPowerSeries (Fin q) O →+* R}
    (hC : ∀ a : O, φ (MvPowerSeries.C a) = ι a)
    (hX : ∀ i, φ (MvPowerSeries.X i) = t i) :
    Function.Surjective φ := by
  classical
  set 𝔪 : Ideal R := _root_.IsLocalRing.maximalIdeal R
  set J : Ideal (MvPowerSeries (Fin q) O) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin q → MvPowerSeries (Fin q) O)) with hJ
  -- `φ` carries the ideal of variables onto `𝔪_R`; this is the whole of
  -- "continuity is automatic", in the form the proof actually uses.
  have hmapJ : Ideal.map φ J = 𝔪 := by
    rw [hJ, Ideal.map_span, ← hspan, ← Set.range_comp]
    simp only [Function.comp_def, hX]
  have hmapJn : ∀ n : ℕ, Ideal.map φ (J ^ n) = 𝔪 ^ n := fun n => by
    rw [Ideal.map_pow, hmapJ]
  -- `ι` hits every residue class, because `ker π = 𝔪_R`.
  have hker : RingHom.ker π = 𝔪 := _root_.IsLocalRing.ker_eq_maximalIdeal π hπ
  have hres : ∀ x : R, ∃ a : O, x - ι a ∈ 𝔪 := by
    intro x
    obtain ⟨a, ha⟩ := hι (π x)
    refine ⟨a, ?_⟩
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa using ha.symm
  -- (a) THE APPROXIMATION STEP.
  have approx : ∀ (n : ℕ) (x : R), x ∈ 𝔪 ^ n →
      ∃ g, g ∈ J ^ n ∧ x - φ g ∈ 𝔪 ^ (n + 1) := by
    intro n x hx
    rw [← hmapJn n] at hx
    have hx' : x ∈ Ideal.span (⇑φ ''
        ((J ^ n : Ideal (MvPowerSeries (Fin q) O)) : Set (MvPowerSeries (Fin q) O))) := hx
    refine Submodule.span_induction
      (p := fun y _ => ∃ g, g ∈ J ^ n ∧ y - φ g ∈ 𝔪 ^ (n + 1)) ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, hg, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, by simp⟩
    · rintro y z - - ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
      refine ⟨g₁ + g₂, add_mem hg₁ hg₂, ?_⟩
      have hrw : y + z - φ (g₁ + g₂) = (y - φ g₁) + (z - φ g₂) := by rw [map_add]; ring
      rw [hrw]; exact add_mem h₁ h₂
    · rintro c y - ⟨g, hg, h⟩
      obtain ⟨a, hca⟩ := hres c
      refine ⟨MvPowerSeries.C a * g, Ideal.mul_mem_left _ _ hg, ?_⟩
      have hφg : φ g ∈ 𝔪 ^ n := by
        rw [← hmapJn n]; exact Ideal.mem_map_of_mem φ hg
      have hrw : c • y - φ (MvPowerSeries.C a * g)
          = c * (y - φ g) + φ g * (c - ι a) := by
        rw [map_mul, hC, smul_eq_mul]; ring
      rw [hrw]
      refine add_mem (Ideal.mul_mem_left _ _ h) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul hφg hca
  intro r
  -- (b) THE LIMIT: iterate (a), then use precompleteness of `O[[x_1,…,x_q]]`.
  let A : ℕ → R → MvPowerSeries (Fin q) O := fun n x =>
    if h : x ∈ 𝔪 ^ n then (approx n x h).choose else 0
  have hA1 : ∀ (n : ℕ) (x : R) (h : x ∈ 𝔪 ^ n), A n x ∈ J ^ n := by
    intro n x h; simp only [A, dif_pos h]; exact (approx n x h).choose_spec.1
  have hA2 : ∀ (n : ℕ) (x : R) (h : x ∈ 𝔪 ^ n), x - φ (A n x) ∈ 𝔪 ^ (n + 1) := by
    intro n x h; simp only [A, dif_pos h]; exact (approx n x h).choose_spec.2
  -- `(P n).1` is the `n`-th partial sum, `(P n).2 = r - φ ((P n).1)` the residue.
  let P : ℕ → MvPowerSeries (Fin q) O × R := fun n =>
    Nat.rec ((0 : MvPowerSeries (Fin q) O), r)
      (fun m p => (p.1 + A m p.2, p.2 - φ (A m p.2))) n
  have hP0 : P 0 = ((0 : MvPowerSeries (Fin q) O), r) := rfl
  have hPs : ∀ n, P (n + 1) = ((P n).1 + A n (P n).2, (P n).2 - φ (A n (P n).2)) :=
    fun _ => rfl
  have key : ∀ n, (P n).2 ∈ 𝔪 ^ n ∧ r - φ ((P n).1) = (P n).2 := by
    intro n
    induction n with
    | zero => exact ⟨by simp [hP0], by simp [hP0]⟩
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [hPs m]
      refine ⟨hA2 m _ ih1, ?_⟩
      simp only [map_add]
      rw [← ih2]; ring
  have hstep : ∀ n, (P (n + 1)).1 - (P n).1 ∈ J ^ n := by
    intro n
    rw [hPs n]
    simpa using hA1 n _ (key n).1
  have hmono : ∀ m n, m ≤ n → (P n).1 - (P m).1 ∈ J ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : (P (n + 1)).1 - (P n).1 ∈ J ^ m :=
        Ideal.pow_le_pow_right hn (hstep n)
      have hrw : (P (n + 1)).1 - (P m).1
          = ((P (n + 1)).1 - (P n).1) + ((P n).1 - (P m).1) := by ring
      rw [hrw]; exact add_mem h1 ih
  have hprec : IsPrecomplete J (MvPowerSeries (Fin q) O) := by rw [hJ]; infer_instance
  obtain ⟨L, hL⟩ := hprec.prec (f := fun n => (P n).1) (by
    intro m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    have := neg_mem (hmono m n hmn)
    rwa [neg_sub] at this)
  refine ⟨L, ?_⟩
  have hfin : ∀ n : ℕ, r - φ L ∈ 𝔪 ^ n := by
    intro n
    have hLn : L - (P n).1 ∈ J ^ n := by
      have h := hL n
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
      have h' := neg_mem h
      rwa [neg_sub] at h'
    have hφLn : φ L - φ ((P n).1) ∈ 𝔪 ^ n := by
      rw [← map_sub, ← hmapJn n]
      exact Ideal.mem_map_of_mem φ hLn
    have hrw : r - φ L = (r - φ ((P n).1)) - (φ L - φ ((P n).1)) := by ring
    rw [hrw, (key n).2]
    exact sub_mem (key n).1 hφLn
  have hzero : r - φ L = 0 :=
    hcomplete.toIsHausdorff.haus (r - φ L) (fun n => by
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, sub_zero]
      exact hfin n)
  exact (sub_eq_zero.mp hzero).symm

/-- **Cohen's structure theorem, in exactly the form the bottom ring leaf
consumes** (PROVEN 2026-07-27 from the two leaves above; was the whole of
LEAF B1a of the 2026-07-27 decomposition of
`exists_taylorWilesBottomPresentation`): a complete Noetherian local ring
with finite residue field is a quotient of a power series ring in finitely
many variables over a `TaylorWilesCoefficients` — and the number of
variables may be taken ARBITRARILY LARGE.

WHAT THIS LEAF IS AND IS NOT.  It is PURE COMMUTATIVE ALGEBRA: there is
no Galois representation, no deformation functor, no Hecke algebra and no
elliptic curve anywhere in its statement, and the CIRCULARITY GUARD of
the patching subtree therefore cannot even be stated against it.  It is
also the ENTIRE remaining content of `exists_taylorWilesBottomPresentation`
— see the FORMAL-CONTENT AUDIT there.

# THE `q₀` PARAMETER IS THE TAYLOR–WILES PADDING REPAIR (2026-07-27)

The FORMAL-CONTENT AUDIT of `exists_taylorWilesBottomPresentation`
records a hazard that no compiler and no axiom audit can see: `q` is
chosen HERE and consumed by `exists_taylorWilesAuxLevelData`, where it
must be at least the Taylor–Wiles number
`dim_k H¹_{∅^*}(ℚ, ad⁰ρbar(1))`.  A proof of this leaf returning Cohen's
`q` — the minimal number of generators of `𝔪_R` — satisfies this leaf
while making the auxiliary leaf FALSE.

The repair implemented here is the strongest thing statable at an
interface that has no vocabulary for Galois cohomology: the leaf takes a
LOWER BOUND `q₀` and returns a presentation with `q₀ ≤ q`.  Padding
upward is free — `exists_fin_span_range_eq_maximalIdeal` simply sends the
extra variables to `0` — so what this delivers is
`max(Cohen's q, q₀)` for whatever `q₀` a consumer can supply, never the
minimal `q`.

**DISCHARGED 2026-07-27 — the bound is now supplied.**  The paragraph
that stood here said the Taylor–Wiles number is nameable only where
Galois cohomology is in scope, that `exists_taylorWilesBottomPresentation`
lacked that vocabulary, and that its call site therefore passed
`q₀ := 0`.  All three are now stale.  The dual-Selmer repair of
`IsTaylorWilesPrimeSet` made exact-size Taylor–Wiles sets exist only
above a level-independent `q0`, `exists_taylorWilesPrimeSet` returns that
`q0`, and it is threaded down the chain; the consumer passes it here as
`q₀`.  So this leaf now really does deliver `max(Cohen's q, q0)`, which is
the value the auxiliary levels need — exactly what this parameter was
added for.

# THE CUT

Three pieces, of which the first two are PROVEN:

* `exists_fin_span_range_eq_maximalIdeal` (PROVEN) — `q₀`-padded finite
  generators of `𝔪_R`, from Noetherianness.
* `exists_ringHom_mvPowerSeries_of_isAdicComplete` (PROVEN) — the
  substitution homomorphism, from `MvPowerSeries.eval₂Hom` and the adic
  topology.  This needed no new theory.
* `exists_taylorWilesCoefficients_ringHom` (LEAF) — the coefficient ring
  `W(k)` and its map into `R`.  The substantial half.
* `surjective_of_span_range_eq_maximalIdeal` (PROVEN 2026-07-27) —
  complete Nakayama, from `MvPowerSeries.instIsAdicComplete` plus a
  `Submodule.span_induction` approximation step; it needed no new
  theory either. -/
theorem exists_taylorWilesCoefficientsPresentation
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {k : Type*} [Field k] [Finite k] {π : R →+* k}
    (hπ : Function.Surjective π) (q₀ : ℕ) :
    ∃ (q : ℕ) (coeff : TaylorWilesCoefficients)
      (φ : MvPowerSeries (Fin q) coeff.carrier →+* R),
      q₀ ≤ q ∧ Function.Surjective φ := by
  obtain ⟨coeff, ι, hι⟩ := exists_taylorWilesCoefficients_ringHom hcomplete hπ
  obtain ⟨q, t, hq, hspan⟩ := exists_fin_span_range_eq_maximalIdeal (R := R) q₀
  have ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R := fun i =>
    hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨φ, hC, hX⟩ := exists_ringHom_mvPowerSeries_of_isAdicComplete hcomplete ι t ht
  exact ⟨q, coeff, φ, hq, surjective_of_span_range_eq_maximalIdeal hcomplete hπ hι hspan hC hX⟩

set_option linter.checkUnivs false in
/-- **The Taylor–Wiles presentation of the universal deformation ring**
(PROVEN 2026-07-27 from `exists_taylorWilesCoefficientsPresentation`;
was LEAF B1 of the 2026-07-27 decomposition of
`exists_taylorWilesBottomLevel`): the RING half of the bottom level —
the coefficient ring `𝒪` and the `q`-generator power-series presentation
of `Runiv` over it, in a universe-`0` model.

Three things are asserted, and they are exactly the three the bottom
level's ring side consumes:

1. **The coefficient ring `𝒪`** exists as a `TaylorWilesCoefficients`.
   Classically `𝒪 = WittVector p k`; this is the obligation the REPAIR
   block of `exists_taylorWilesBottomLevel` records as genuinely owed —
   mathlib's pin supplies `WittVector.isDiscreteValuationRing`, hence
   `isLocalRing`, `isNoetherianRing` and `exists_isRegular_maximalIdeal`
   nearly directly; the topological half (`IsTopologicalRing`,
   `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace` for the
   coefficientwise product topology, plus `Algebra.TopologicallyFG ℤ`)
   is what has to be built.
2. **Mazur's tangent-space bound**: `Runiv` is a quotient of
   `𝒪[[x_1, …, x_q]]`, i.e. topologically generated over `𝒪` by
   `q = dim_k H¹_{Q_n}(ℚ, ad⁰ρbar)` elements.  This is where `hfact`
   (weak universality) and the residual hypotheses enter: the minimal
   number of generators is the `k`-dimension of the tangent space
   `Hom_k(𝔪_R/(𝔪_R² + 𝔪_𝒪), k) = H¹_f(ℚ, ad⁰ρbar)`.
3. **A universe-`0` model**: the presentation is required to land in a
   ring `R : Type` isomorphic to `Runiv`, which is the "Type-0 note" of
   `exists_taylorWilesTower` made into an obligation.

   **CORRECTED 2026-07-27: obligation 3 is NOT an obligation at all — it
   is free, and this docstring previously overstated it.**  The earlier
   text argued that a universe-`0` model exists because `Runiv` is an
   inverse limit of finite rings of cardinality at most the continuum.
   That argument is sound but entirely unnecessary, and formalising it
   would have been days of wasted work.  Given ANY surjection
   `φ : 𝒪[[x_1, …, x_q]] ↠ Runiv`, the ring
   `𝒪[[x_1, …, x_q]] / ker φ` is ALREADY in `Type`, because
   `TaylorWilesCoefficients.carrier` is declared `Type` and both
   `MvPowerSeries` and `Ideal.Quotient` preserve the universe; and it is
   isomorphic to `Runiv` by the first isomorphism theorem
   (`RingHom.quotientKerEquivOfSurjective`).  So obligation 3 is
   discharged by obligation 2 with no cardinality argument whatsoever,
   and that is exactly how the proof below reads.

# FORMAL-CONTENT AUDIT (2026-07-27) — THIS LEAF CARRIES NO GALOIS CONTENT

Its proof consumes exactly TWO of its hypotheses: `hcomplete` and
`hπuniv`.  Seven others — `hres`, `hirr`, `hadic`, `hρuniv`, `hunivred`,
`hfact` and `hTWq` — are entirely unused, and the seven
`unusedVariables` warnings this declaration emits are that fact made
mechanically visible rather than merely asserted.  They are EXPECTED and
must not be silenced: they are the audit.  (`hpodd` and `hW` draw no
warning only because they appear in the TYPES of `hres` and `hρuniv`, so
they are referenced implicitly; the proof does not use them either.)

The reason is structural, not an artefact of how the proof was written.
`pres` is quantified as a BARE `RingHom` — no continuity, no
`𝒪`-algebra structure, and no minimality on `q` — so the statement asks
only that `Runiv` be *some* quotient of *some* power series ring over
*some* coefficient ring.  That is Cohen's structure theorem, which needs
nothing beyond "local, Noetherian, complete, finite residue field".  In
particular **obligation 2 above is NOT Mazur's tangent-space bound**: the
bound says `q` may be taken to be `dim_k H¹_f(ℚ, ad⁰ρbar)`, and nothing
in this statement asks for the minimal `q`, so `hfact` is not needed and
cannot be needed.

**THE `q` HAZARD — RECORDED HERE SINCE 2026-07-27, AND NOW DISCHARGED BY
THE STATEMENT ITSELF.**  `q` is chosen here and consumed by
`exists_taylorWilesAuxLevelData` at every level, where it must be at
least the Taylor–Wiles number `dim_k H¹_{∅^*}(ℚ, ad⁰ρbar(1))`.  A proof
of this leaf returning Cohen's `q` — the minimal number of generators of
`𝔪_Runiv` — would satisfy the old statement while making the auxiliary
leaf FALSE, with no compiler warning and no axiom-audit signal.  The
interface could not prevent it, because the Taylor–Wiles number is a
Galois-cohomological quantity and this statement has no vocabulary for
it.

**That gap is closed at the interface rather than left to a prover's
discipline.**  The repaired supply carries a LOWER BOUND: since the
dual-Selmer clause was added to `IsTaylorWilesPrimeSet`, exact-size
Taylor–Wiles sets exist only above a level-independent `q0`, and
`exists_taylorWilesPrimeSet` returns that `q0`.  It is now an explicit
argument here, `hTWq` is stated relative to it, and the CONCLUSION
asserts `q0 ≤ q`.  Padding `q` UPWARD is safe on both sides — extra
variables may be sent to `0`, and each extra Taylor–Wiles prime raises
`dim H¹_Q` by one while keeping the dual Selmer group zero — so the
proof simply passes `q0` as the lower bound to
`exists_taylorWilesCoefficientsPresentation`, which already accepted one.
The returned `q` is therefore `max(Cohen's q, q0)` by construction, and
**a prover of a downstream leaf may rely on `hq0 : q0 ≤ q`** instead of
on an instruction in prose.

`hTWq` is still carried here unused (see the audit above): with `q0`
explicit, the bound rather than the supply is what this statement
consumes.  It is kept for shape uniformity along the chain and because it
is the only handle the hypothesis package offers on the Taylor–Wiles
primes.  (At `Q = ∅` nothing else in the bottom datum consumes it.)

CIRCULARITY GUARD: inherited unchanged from
`exists_taylorWilesBottomLevel`.  `not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` and `Slop.OddRep.isIrreducible_iff_forall`
used against `hirr`, any reduction-descent producing
`IsHardlyRamified hpodd hW ρbar` from `hρuniv`, and `Family.lean` with
everything downstream of it, are BANNED as inputs.  A proof ending in
`exfalso` is the circular discharge again and must be rejected. -/
theorem exists_taylorWilesBottomPresentation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
    ∃ (q : ℕ), q0 ≤ q ∧
      ∃ (coeff : TaylorWilesCoefficients) (R : Type) (_ : CommRing R)
      (pres : MvPowerSeries (Fin q) coeff.carrier →+* R),
      Function.Surjective pres ∧ Nonempty (R ≃+* Runiv) := by
  -- LEAF B1a: Cohen's structure theorem supplies the coefficient ring and
  -- a surjection from a power series ring over it onto `Runiv`.
  -- **THE TAYLOR–WILES PADDING HAZARD IS DISCHARGED HERE (2026-07-27).**
  -- `exists_taylorWilesCoefficientsPresentation` takes a LOWER BOUND on the
  -- number of variables and returns `q₀ ≤ q`.  Until the dual-Selmer repair
  -- of `IsTaylorWilesPrimeSet` this declaration had no way to name the
  -- Taylor–Wiles number, so `0` was passed and Cohen's `q` — the number of
  -- minimal generators of `𝔪_Runiv` — could silently sit BELOW it, which
  -- makes the auxiliary levels unconstructible.  The supply now carries the
  -- bound `q0` explicitly, so `q0` is what is passed, and the returned `q`
  -- satisfies `max(Cohen's q, q0) ≥ q0` by construction.  That bound is
  -- propagated all the way to the arithmetic leaves as `hq0`.
  obtain ⟨q, coeff, φ, hq₀, hφ⟩ :=
    exists_taylorWilesCoefficientsPresentation hcomplete hπuniv q0
  -- The universe-`0` model is then FREE: `MvPowerSeries (Fin q) coeff.carrier`
  -- already lives in `Type`, because `TaylorWilesCoefficients.carrier` does,
  -- and so does its quotient by `ker φ`, which the first isomorphism theorem
  -- identifies with `Runiv`.
  refine ⟨q, hq₀, coeff, MvPowerSeries (Fin q) coeff.carrier ⧸ RingHom.ker φ,
    inferInstance, Ideal.Quotient.mk _, Ideal.Quotient.mk_surjective, ?_⟩
  exact ⟨RingHom.quotientKerEquivOfSurjective hφ⟩

set_option linter.checkUnivs false in
/-- **The bottom Hecke module** (sorry node, LEAF B2 of the 2026-07-27
decomposition of `exists_taylorWilesBottomLevel`): the MODULE half of the
bottom level — the modularity-subtree plug point.

Classically `M₀ = H¹(X₀(N), ℤ_p)_𝔪`, the `𝔪`-localized cohomology of the
modular curve at the level of the residual representation: a nontrivial
`T`-module, free of rank `d` over `ℤ_p`, on which the diamond coordinate
ring `Λ = ℤ_p[[S_1,…,S_q]]` acts through its augmentation
`Λ ↠ Λ/𝔫 ≅ ℤ_p → T` (that is the content of `aug_smul`, and it is what
makes `bIdeal := 𝔫` the correct bottom level ideal).  The freeness is
recorded in the `Λ`-linear coordinate form the level interface consumes,
`M₀ ≃ₗ[Λ] (Λ/𝔫)^d`, rather than as `Module.Free ℤ_[p] M₀`, so that no
identification `Λ/𝔫 ≅ ℤ_[p]` is needed on the consuming side.

# VACUITY AUDIT — CONFIRMED MECHANICALLY, AND REPAIRED BY PINNING (2026-07-27)

The earlier audit of this leaf said it was vacuous, gave `M₀ := T` as the
junk witness, and told a prover not to discharge it.  All three parts have
now been checked against the elaborator rather than by reading, and the
outcome is: **the vacuity is REAL, the witness as written does NOT
typecheck, and the vacuity is not removable by any statement in this
leaf's vocabulary.**  The statement has therefore been RESTATED to pin
`M₀` to the correct isomorphism class, and then PROVEN.

## 1.  The vacuity, verified

The previous statement — everything below except the clause
`Nonempty (M0 ≃ₗ[T] (Fin 2 → T))` — is derivable from the FIVE instance
hypotheses `[CommRing T] [Algebra ℤ_[p] T] [IsLocalRing T]
[Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T]` alone.  Not one of
`hpodd`, `hW`, `hres`, `hirr`, `hrankT`, `hρT`, `hπ`, `hred` is consumed;
they are underscore-prefixed below so that this is mechanically visible.
No modular curve, no Hecke correspondence, nothing arithmetic.

**The old audit's witness `M₀ := T` does not typecheck**, and an agent
checking the audit rather than trusting it would be stopped by the
elaborator and could wrongly conclude the leaf has content.  It does not:
this leaf binds `{T : Type s}` at a universe VARIABLE while the conclusion
demands `M0 : Type`, so the witness has to be a universe-`0` MODEL of a
`T`-module, obtained by transporting the `T`-action along a `ℤ_[p]`-linear
coordinatization.  That is exactly what the proof below does.

## 2.  The restatement: `M₀` is now pinned to `T²`

Added clause, and it is the whole of the change:

    Nonempty (M0 ≃ₗ[T] (Fin 2 → T))

Classically this is Eichler–Shimura together with Mazur's multiplicity-one
/ Gorenstein theorem for a NON-EISENSTEIN maximal ideal: for `ρbar`
irreducible (`hirr`, which is exactly non-Eisensteinness) and `p` odd and
prime to the level — the situation throughout the Taylor–Wiles tower here,
since every auxiliary prime `q ∈ Q_n` satisfies `q ≡ 1 mod p^n`, so `p`
never divides a level — the module `H¹_ét(X₀(N)_{ℚ̄}, ℤ_p)_𝔪` is FREE OF
RANK 2 over `𝕋_𝔪`, and as a `𝕋_𝔪[Γ_ℚ]`-module it realizes `ρ_𝔪 = ρT`.
See DDT §3 (Thm. 3.31), Wiles Ann. of Math. 141 (1995) §2.1, and Mazur,
Eisenstein ideal, for the Gorenstein input.

What it buys: the old statement let a prover hand back ANY `ℤ_[p]`-free
`T`-module — `T`, `T³`, or a module on which `T` acts through some
unrelated quotient — and the sibling `exists_taylorWilesAuxLevelData` must
then build, for that very `M₀`, a tower of `Λ/𝔟_n`-free modules with
`𝔫`-quotient `M₀`.  For a badly chosen `M₀` no such tower exists, so a
junk discharge here turns the sibling FALSE with no signal a compiler or
an axiom audit can emit.  With the clause, `M₀` is determined up to
`T`-isomorphism, and it is determined to be the object the sibling is
actually about.

If a future owner prefers the `±`-eigenspace normalization — `M₀` free of
rank ONE over `T`, which is the other standard choice and equally
classical — the clause to write is `Nonempty (M0 ≃ₗ[T] T)` and the proof
below adapts by replacing `Fin 2 → T` with `T` throughout.  What must NOT
happen is leaving the rank unpinned: "free of some positive rank over `T`"
is satisfied by `T` itself and reinstates the whole hazard.

## 3.  Why the leaf is still vacuous, and why that is not a defect here

The pin does not make the leaf hard, and **no clause in this vocabulary
could**: multiplicity one is precisely the statement that the bottom Hecke
module is determined, up to isomorphism, by `(T, ρT)` — both of which are
HYPOTHESES here.  So every faithful assertion about `M₀` expressible in
terms of `T`, `ρT`, `π`, `ρbar` is satisfiable by an object built from
those hypotheses, and the leaf is dischargeable no matter how it is
stated.  The arithmetic of the Taylor–Wiles method is unavoidably at the
AUXILIARY level, where the level-raised Hecke rings `𝕋_{Q_n}` are not
among the hypotheses and have to be constructed.

Following the vacuity doctrine — prove it, then make the emptiness
manifest — the leaf is now PROVEN, with every arithmetic hypothesis
underscore-prefixed.  `hpodd`, `hW` and `hrankT` keep their names only
because the types of `_hres` and `_hρT` mention them; they are equally
unconsumed.

## 4.  THE REPAIR — DONE 2026-07-27, and it was one line

The pin protects the sibling only where it is visible to it, and it was
not: `exists_taylorWilesBottomLevel` below re-existentially-quantified
`M0` WITHOUT the clause, so `exists_taylorWilesTower` handed
`exists_taylorWilesAuxLevelData` an unpinned `M0` characterized only by
`hbot`.  All three steps of that propagation are now made:

1. `Nonempty (M0 ≃ₗ[T] (Fin 2 → T))` is a conjunct of the conclusion of
   `exists_taylorWilesBottomLevel` (its proof already had the term — it
   was the component dropped by `-` in its `obtain`, now bound `hM0T`);
2. `(hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))` is a hypothesis of
   `exists_taylorWilesAuxLevelData` — and, since that statement is now a
   PROVEN assembly over `exists_taylorWilesAuxLevelPresentedDatum`, of
   that leaf too, which is where the weakening actually has to land if it
   is to reach a prover.  This WEAKENS both, and is what makes them true
   rather than merely open;
3. `exists_taylorWilesLevelRaw` carries it as a hypothesis and
   `exists_taylorWilesTower` threads it, instead of dropping it.

So an owner of A2/A2′ may now assume `M₀ ≅ T²` — which, combined with
the ROUTE NOTE recorded at A2′ (`hbot` forces `M₀ ≅ ℤ_p^d`), pins
`d = rank_{ℤ_p} T²` and identifies the bottom module completely.

CIRCULARITY GUARD: inherited unchanged from
`exists_taylorWilesBottomLevel`; see the guard recorded there.  It is
satisfied vacuously — the proof below is pure commutative algebra and
touches no deformation-theoretic input at all. -/
theorem exists_taylorWilesBottomHeckeModule.{s, uK, uW}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (_hres : IsTaylorWilesResidual hpodd hW ρbar)
    (_hirr : ρbar.IsIrreducible)
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
    (q : ℕ) :
    ∃ (d : ℕ) (M0 : Type) (_ : AddCommGroup M0) (_ : Module T M0)
      (_ : Nontrivial M0) (_ : Module (MvPowerSeries (Fin q) ℤ_[p]) M0),
      (∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M0),
        x • m = algebraMap ℤ_[p] T
          (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x) • m) ∧
      Nonempty (M0 ≃ₗ[T] (Fin 2 → T)) ∧
      Nonempty (M0 ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
        (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ taylorWilesAug p q)) := by
  classical
  -- `Fin 2 → T` is a finite free `ℤ_[p]`-module; coordinatize it, which is
  -- what produces the universe-`0` model demanded by `M0 : Type`.
  set d : ℕ := Module.finrank ℤ_[p] (Fin 2 → T) with _hd
  let E : (Fin 2 → T) ≃ₗ[ℤ_[p]] (Fin d → ℤ_[p]) :=
    (Module.finBasis ℤ_[p] (Fin 2 → T)).equivFun
  -- the `T`-action, transported along `E`
  letI : SMul T (Fin d → ℤ_[p]) := ⟨fun t m => E (t • E.symm m)⟩
  have hsmul : ∀ (t : T) (m : Fin d → ℤ_[p]), t • m = E (t • E.symm m) :=
    fun _ _ => rfl
  letI : Module T (Fin d → ℤ_[p]) :=
    Function.Injective.module T E.symm.toLinearMap.toAddMonoidHom
      E.symm.injective (fun c x => by
        show E.symm (E (c • E.symm x)) = c • E.symm x
        exact E.symm_apply_apply _)
  -- the transported `T`-action restricts to the canonical `ℤ_[p]`-action
  have hscalar : ∀ (c : ℤ_[p]) (m : Fin d → ℤ_[p]),
      (algebraMap ℤ_[p] T c) • m = c • m := by
    intro c m
    rw [hsmul, algebraMap_smul, map_smul, E.apply_symm_apply]
  -- THE PIN: `M₀ ≃ₗ[T] T²` is the transport equivalence itself
  let eT : (Fin d → ℤ_[p]) ≃ₗ[T] (Fin 2 → T) :=
    { toFun := E.symm
      map_add' := fun x y => map_add _ _ _
      map_smul' := fun c x => E.symm_apply_apply _
      invFun := E
      left_inv := fun x => E.apply_symm_apply x
      right_inv := fun y => E.symm_apply_apply y }
  -- nontriviality, transported from `T² ≠ 0`
  have hnt : Nontrivial (Fin d → ℤ_[p]) := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin 2 → T)
    exact ⟨E x, E y, fun h => hxy (E.injective h)⟩
  -- the `Λ`-action through the augmentation `Λ ↠ ℤ_p → T`
  letI : Module (MvPowerSeries (Fin q) ℤ_[p]) (Fin d → ℤ_[p]) :=
    Module.compHom _ ((algebraMap ℤ_[p] T).comp
      (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])))
  have haug : ∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : Fin d → ℤ_[p]),
      x • m = algebraMap ℤ_[p] T
        (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x) • m :=
    fun _ _ => rfl
  -- `Λ/𝔫 ≃+* ℤ_[p]`, the augmentation quotient
  have hsurj : Function.Surjective
      (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])) := by
    intro c
    exact ⟨MvPowerSeries.C (σ := Fin q) (R := ℤ_[p]) c, by simp⟩
  have hker : RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]))
      = taylorWilesAug p q := ker_constantCoeff_mvPowerSeries q ℤ_[p]
  let γ : (MvPowerSeries (Fin q) ℤ_[p] ⧸ taylorWilesAug p q) ≃+* ℤ_[p] :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  have hγ : ∀ x : MvPowerSeries (Fin q) ℤ_[p],
      γ (Ideal.Quotient.mk (taylorWilesAug p q) x) =
        MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x := by
    intro x
    simp [γ, RingHom.quotientKerEquivOfSurjective_apply_mk]
  -- `Λ` acts on `Λ/𝔫` by multiplication through the quotient map
  have hsmulQ : ∀ (x : MvPowerSeries (Fin q) ℤ_[p])
      (z : MvPowerSeries (Fin q) ℤ_[p] ⧸ taylorWilesAug p q),
      x • z = (Ideal.Quotient.mk (taylorWilesAug p q) x) * z := by
    intro x z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  -- Diamond's certificate in coordinate form, at the bottom level
  let coord : (Fin d → ℤ_[p]) ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
      (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ taylorWilesAug p q) :=
    { toFun := fun v i => γ.symm (v i)
      invFun := fun w i => γ (w i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun x v => by
        ext i
        show γ.symm ((x • v) i) = x • γ.symm (v i)
        rw [haug, hscalar, hsmulQ]
        show γ.symm (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x * v i)
          = _
        rw [map_mul]
        congr 1
        exact γ.symm_apply_eq.mpr (hγ x).symm
      left_inv := fun v => by ext i; simp
      right_inv := fun w => by ext i; simp }
  exact ⟨d, Fin d → ℤ_[p], inferInstance, inferInstance, hnt, inferInstance,
    haug, ⟨eT⟩, ⟨coord⟩⟩

/-- **The coordinate model of an auxiliary Taylor–Wiles level module**
at the CONSTANT exponent vector `e ≡ n`:

    (Λ/𝔟_n)^d ,   Λ = ℤ_p[[S_1, …, S_q]] ,
    𝔟_n = ((1 + S_i)^{p^n} − 1)_{i} ,

so that `Λ/𝔟_n ≅ ℤ_p[(ℤ/p^n)^q]` — the group ring of the level-`n`
diamond group in its standard `p^n`-truncated form.

This is the type that `TaylorWilesLevelRaw.coordM` identifies the
auxiliary Hecke module with.  Naming it as a CONCRETE `Type` is what
lets the arithmetic leaf `exists_taylorWilesAuxLevelPresentedDatum`
below avoid producing a carrier and a coordinate equivalence at all;
see the reduction audit recorded there. -/
abbrev taylorWilesCoordModel (p : ℕ) [Fact p.Prime] (q d n : ℕ) : Type :=
  Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸
    taylorWilesLevelIdeal p (fun _ : Fin q => n)

/-! ### The RING/HECKE cut of the auxiliary Taylor–Wiles level over `ℚ` -/

/-- **The RAISED-LEVEL local condition over `ℚ`** (2026-07-27; piece 1 of the
three the RING/HECKE cut needs stated).

`IsHardlyRamified hpodd hdim ρ` (`HardlyRamified/Defs.lean`) with the level
RAISED at a finite set `Q` of rational primes: the four hardly-ramified clauses
are kept VERBATIM except that `isUnramified` is now asked only away from `Q`,
and a fifth clause pins what happens AT `Q`.

* **`det`, `isFlat`, `isTameAtTwo`** — unchanged.  Raising the level at a
  Taylor–Wiles prime set touches neither the determinant nor the primes `2` and
  `p`.
* **`isUnramified`** — asked away from `2`, `p` **and `Q`**.  This is the whole
  "raising": ramification is newly permitted exactly at `Q`.
* **`isSplitTorusAt`** — the new clause.  At each `q ∈ Q` the local
  representation is DIAGONAL: an `R`-linear identification `V ≃ R × R` under
  which `ρ|_{G_{ℚ_q}}` acts by a pair of characters `(χ, δ)`, with `δ`
  UNRAMIFIED.

**Why the split-torus clause has this shape, and why it may not be weakened to
"unrestricted at `Q`".**  At a Taylor–Wiles prime the residual `ρbar(Frob_q)`
has two DISTINCT eigenvalues (the local clause of `IsTaylorWilesPrimeSet`), so
the local deformation functor at `q` splits as a product of two
character-deformation functors — Wiles ch. 3 — and that is what makes the
condition representable at all.  Two things depend on it:

* the DIAMOND action.  `χ|_{I_q}` factors through the tame quotient of `I_q`,
  i.e. through `(ℤ/q)ˣ`, whose `p`-Sylow is `Δ_q`; the diamond structure map
  `Λ → R_Q` of `TaylorWilesLevelRaw` is nothing but this action.  Drop the
  clause and there are no diamond operators, hence no `diamond` field and no
  control identification `R_Q/𝔫 ≅ R_univ`;
* the CONTROL identification itself.  `δ` unramified together with `χ` trivial
  on `I_q` is precisely "level not actually raised at `q`", which is the
  condition `𝔫 · R_Q` cuts out.

**FORMAL-CONTENT NOTE (deliberate weakness, stated rather than hidden).**  The
clause asks the split to exist over `R` with `δ` unramified; it does NOT ask
that `χ`, `δ` reduce to the two distinct residual eigenvalues in a prescribed
order, nor that `χ|_{I_q}` factor through the `p`-Sylow `Δ_q`.  Both are
consequences of residual distinctness in the intended instantiation, and both
are properties of the CONSTRUCTION rather than of the local condition; a
consumer that needs them must DERIVE them from the datum's `charFrob_compat`
together with `hQ`, not read them off here.  This mirrors, verbatim, the same
note on the Hilbert twin `IsHilbertRaisedLevelHardlyRamified`.

`isRaisedLevelHardlyRamified_empty_iff` below records that at `Q = ∅` nothing
has changed, which is the one-command refutation of "the new clause altered the
base-level problem".

References: Wiles, Ann. of Math. 141 (1995), ch. 3; Taylor–Wiles, ibid. §2;
Darmon–Diamond–Taylor §5.3. -/
structure IsRaisedLevelHardlyRamified {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ)
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) : Prop where
  /-- The determinant is the `p`-adic cyclotomic character.  Verbatim
  `IsHardlyRamified.det`. -/
  det : ∀ g, ρ.det g = algebraMap ℤ_[p] R
    (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv)
  /-- Unramified at every prime other than `2`, `p` **and the primes of `Q`**.
  This single change from `IsHardlyRamified.isUnramified` is the level
  raising. -/
  isUnramified : ∀ q (hq : q.Prime), q ∉ Q → q ≠ 2 → q ≠ p →
    ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat
  /-- Flat at `p`.  Verbatim `IsHardlyRamified.isFlat`. -/
  isFlat : ρ.IsFlatAt
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
  /-- A square-trivial unramified quotient character at `2`.  Verbatim
  `IsHardlyRamified.isTameAtTwo`. -/
  isTameAtTwo : ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
    ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : V,
      π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
      (AddSubgroup.inertia ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
        AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1)
  /-- **The SPLIT-TORUS condition at the raised primes.**  At each `q ∈ Q` the
  restriction `ρ|_{G_{ℚ_q}}` is DIAGONAL in some `R`-basis — `V ≃ₗ[R] R × R`
  carrying it to `(χ, δ)` — with the second character `δ` UNRAMIFIED.

  Written as a linear equivalence to `R × R` rather than as a sub/quotient
  pair on purpose: a sub together with a splitting quotient forces the two
  characters to COINCIDE, which is not the split torus but its diagonal.  The
  equivalence says exactly `ρ|_{G_{ℚ_q}} ≅ χ ⊕ δ` and nothing more. -/
  isSplitTorusAt : ∀ q ∈ Q, ∀ hq : q.Prime,
    ∃ (e : V ≃ₗ[R] R × R)
      (χ δ : GaloisRep
        ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) R R),
      (∀ (g : Field.absoluteGaloisGroup
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
          (v : V),
        e (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat g v) =
          (χ g (e v).1, δ g (e v).2)) ∧
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker

/-- **At `Q = ∅` the raised-level condition IS the hardly ramified condition**
(PROVEN — the consistency check that the new predicate is a genuine extension
of the old one and not a differently-shaped junk condition).

Both directions are immediate: the split-torus clause quantifies over an empty
set, and the `q ∉ ∅` hypothesis of `isUnramified` is discharged by
`Finset.notMem_empty`.  Kept because a raised-level predicate that failed to
specialise back would be a silent restatement. -/
theorem isRaisedLevelHardlyRamified_empty_iff {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] {hdim : Module.rank R V = 2}
    {ρ : GaloisRep ℚ R V} :
    IsRaisedLevelHardlyRamified hpodd ∅ hdim ρ ↔ IsHardlyRamified hpodd hdim ρ :=
  ⟨fun h => ⟨h.det, fun q hq h2 => h.isUnramified q hq (Finset.notMem_empty q)
      h2.1 h2.2, h.isFlat, h.isTameAtTwo⟩,
    fun h => ⟨h.det, fun q hq _ h2 hp => h.isUnramified q hq ⟨h2, hp⟩, h.isFlat,
      h.isTameAtTwo, fun q hq => absurd hq (Finset.notMem_empty q)⟩⟩

set_option linter.checkUnivs false in
/-- **Mazur's deformation category over `ℚ` AT RAISED LEVEL `Q`** (2026-07-27;
piece 2 of the three the RING/HECKE cut needs stated).

The Mazur-category shape already used for `Runiv` in this file — complete
Noetherian local topological `ℤ_p`-algebra with the maximal-adic topology,
framed rank-2 representation, surjective reduction onto the residual
coefficient ring, and trace-level residual compatibility away from a finite set
— with `IsHardlyRamified` replaced by the raised-level
`IsRaisedLevelHardlyRamified hpodd Q`.

The whole point of this interface is that the raised-level ring `R_Q` is pinned
by a UNIVERSAL PROPERTY, so that the HECKE leaf of the cut below receives a
ring it can RECOGNISE instead of an abstract carrier satisfying four structural
equations.  See the CUT-SAFETY note on `exists_auxHeckeModuleData` for the
explicit junk-ring counterexample that makes this necessary.

**Why `charFrob_compat` and not a charpoly identity at every `g`.**  The
Hilbert twin `HilbertAuxDeformationDatum` asks `((ρ g).charpoly).map π =
(ρbar g).charpoly` at every `g ∈ G_F`.  That shape is NOT available here: the
whole `ℚ`-side chain — `HardlyRamifiedFiniteDeformation`,
`IsWeaklyUniversalDeformation`, `hunivred`, `hred`, `hψ` — carries only the
linear `charFrob` coefficients away from a finite exceptional set, and
`exists_auxDeformationDatum` below has to BUILD a datum out of exactly those.
Asking the stronger form would make that leaf unreachable from its own
hypotheses; this is the same "a datum handed across a seam can only be
constrained by what already saw it" discipline that the INTERFACE REPAIR
section of the assembly records, applied in the other direction.

`Q = ∅` gives back the unraised Mazur category up to the propositional
identification `isRaisedLevelHardlyRamified_empty_iff` above; the two are not
made definitionally equal, since a `structure` with a differently-typed field
cannot be. -/
structure AuxDeformationDatum.{a, vK, vW} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime] (Q : Finset ℕ)
    {k : Type vK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type vW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (ρbar : GaloisRep ℚ k W) where
  /-- The raised-level deformation ring `R_Q`. -/
  R : Type a
  [commRing : CommRing R]
  [topologicalSpace : TopologicalSpace R]
  [isTopologicalRing : IsTopologicalRing R]
  [isLocalRing : IsLocalRing R]
  [algebra : Algebra ℤ_[p] R]
  [isNoetherianRing : IsNoetherianRing R]
  /-- The topology of `R_Q` is the maximal-adic one.  Carried per the standing
  rule that an algebraic pin never constrains a topological conclusion: `ρ` is
  a `GaloisRep` and therefore continuous, so dropping this would make the datum
  satisfiable by a discrete ring. -/
  isAdic : IsAdic (IsLocalRing.maximalIdeal R)
  /-- `R_Q` is maximal-adically complete and separated. -/
  isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R
  /-- The deformation, framed by the standard basis. -/
  ρ : GaloisRep ℚ R (Fin 2 → R)
  /-- The framing module has rank `2`. -/
  rank_eq : Module.rank R (Fin 2 → R) = 2
  /-- The deformation satisfies the RAISED-LEVEL local conditions. -/
  isRaisedLevelHardlyRamified : IsRaisedLevelHardlyRamified hpodd Q rank_eq ρ
  /-- The reduction map onto the residual coefficient ring. -/
  π : R →+* k
  /-- `k` IS the residue field of `R_Q`. -/
  π_surjective : Function.Surjective π
  /-- The finite exceptional set of the reduction datum. -/
  S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
  /-- The deformation reduces to `ρbar`: the linear `charFrob` coefficients
  (the Frobenius traces up to sign) match through `π` away from `S`.  Same
  shape as `HardlyRamifiedFiniteDeformation.charFrob_compat` above. -/
  charFrob_compat : ∀ (q : ℕ) (hq : q.Prime),
    hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
    π ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
      (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

attribute [instance] AuxDeformationDatum.commRing
  AuxDeformationDatum.topologicalSpace
  AuxDeformationDatum.isTopologicalRing
  AuxDeformationDatum.isLocalRing
  AuxDeformationDatum.algebra
  AuxDeformationDatum.isNoetherianRing

set_option linter.checkUnivs false in
/-- **Weak universality of a RAISED-LEVEL deformation datum** — the
raised-level analogue of `IsWeaklyUniversalDeformation` above, and the property
that makes `R_Q` recognisable rather than arbitrary.

Only the EXISTENCE half is asked, exactly as in `IsWeaklyUniversalDeformation`
(uniqueness — Carayol trace generation — is never needed by the consumers here,
and keeping the clause existential keeps this statement at the representability
strength and no more).

The test category is the raised-level Mazur category itself rather than a
separate finite test category.  That is the Hilbert twin's choice
(`HilbertAuxDeformationDatum.IsWeaklyUniversal`) and it is enough for the two
consumers below, each of which needs one classifying map out of `R_Q`, never a
comparison of two. -/
def AuxDeformationDatum.IsWeaklyUniversal.{a, vK, vW} {p : ℕ} {hpodd : Odd p}
    [Fact p.Prime] {Q : Finset ℕ}
    {k : Type vK} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k]
    {W : Type vW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    {ρbar : GaloisRep ℚ k W}
    (𝒟 : AuxDeformationDatum.{a, vK, vW} hpodd Q ρbar) : Prop :=
  ∀ 𝒟' : AuxDeformationDatum.{a, vK, vW} hpodd Q ρbar,
    ∃ f : 𝒟.R →+* 𝒟'.R,
      f.comp (algebraMap ℤ_[p] 𝒟.R) = algebraMap ℤ_[p] 𝒟'.R ∧
      𝒟'.π.comp f = 𝒟.π ∧
      ∃ Sf : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
        ∀ (q : ℕ) (hq : q.Prime),
          hq.toHeightOneSpectrumRingOfIntegersRat ∉ Sf →
          f ((𝒟.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
            (𝒟'.ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1

set_option linter.checkUnivs false in
/-- **The raised-level deformation category at `Q` is NONEMPTY** (PROVEN
2026-07-28 — was LEAF A2′-1 of the 2026-07-27 RING/HECKE cut of
`exists_taylorWilesAuxLevelPresentedDatum` below; closed over the Hilbert-side
split-torus package after two interface repairs recorded below, and over the
Chebotarev–Brauer–Nesbitt leaf `exists_conj_of_charFrob_eq_away`).

`ρuniv` ITSELF is the witness.  Four of the five clauses of
`IsRaisedLevelHardlyRamified` are handed over by `hρuniv` — `det`, `isFlat`,
`isTameAtTwo` verbatim, and `isUnramified` is strictly WEAKER than
`IsHardlyRamified.isUnramified` — and the whole content of this leaf is the
fifth, `isSplitTorusAt` at each `q ∈ Q`.

**Why that is a real but SMALL statement, and the route.**  At `q ∈ Q` the
representation `ρuniv` is unramified (a Taylor–Wiles prime is prime to `2p`;
see the note below on how that is obtained), and the local clause of `hQ` says
`ρbar.charFrob q` splits with two DISTINCT roots `α ≠ β` in `k`.  So:

1. the Frobenius matrix `ρuniv(Frob_q)` reduces mod `𝔪_{Runiv}` to a matrix
   with distinct eigenvalues, and Hensel's lemma over the complete local
   `Runiv` (`hcomplete`) lifts that residual eigenbasis to an `R`-basis of
   eigenvectors;
2. an UNRAMIFIED local representation COMMUTES with the arithmetic Frobenius —
   two arithmetic Frobenii at the same prime differ by inertia — so the whole
   of `ρuniv|_{G_{ℚ_q}}` is diagonal in that basis, the eigenvalue gap being a
   unit;
3. the second diagonal character is unramified because the whole local
   representation is.

**This exact route is FULLY PROVEN on the Hilbert side and is CONSUMED here,
not copied** (2026-07-28 — the answer to the "can they be hoisted?" question
this docstring used to ask).  `commute_toLocal_adicArithFrob_of_isUnramifiedAt`,
`exists_frobEigenBasis_of_charFrob_map_eq` (which was labelled the single open
piece and had in fact been closed over
`exists_matrix_eigenBasis_of_charpoly_map_eq`) and
`exists_splitTorus_of_frobDiagonal` all live in
`HardlyRamified/HilbertModularity.lean`, assembled there as
`exists_isSplitTorusAt_of_isUnramifiedAt`, and they are stated over an arbitrary
place of an arbitrary number field — `ℚ` is one.

**No hoisting was needed: that file is ALREADY a public transitive import of
this one** (`Patching → …HardlyRamified.Deformation → HilbertModularity`), so
the names were visible here all along.  What actually blocked reuse was a
UNIVERSE clash and nothing else: the section had `R`, `F` and `k` all in one
`Type u`, while here `F = ℚ` is `Type 0` and the coefficient ring and residual
field are this leaf's own `uR`, `uK`.  The repair was to make the three
universes independent in place (`Type*`), which is strictly weaker than hoisting
and moves no declaration.  Record for the next reader: when a lemma "cannot be
reused across files", check the universes before concluding it must be moved or
duplicated.

**WHY `hQ` IS ASKED AT LEVEL `n` AND THE ASSEMBLY SUPPLIES LEVEL `n + 1`.**
The `ℚ`-level `IsTaylorWilesPrimeSet`, unlike its Hilbert twin, does NOT carry
the exclusions `q ≠ 2` and `q ≠ p`; its local conjunct is only
`q ≡ 1 [MOD p^n]` plus the split distinct-eigenvalue clause.  At `n = 0` that
congruence is vacuous, so `q ∈ {2, p}` is not excluded and step 1 above has no
unramifiedness to start from.  At `n ≥ 1` both exclusions follow (`q ≡ 1 mod p`
with `p` odd forces `q ≠ 2` and `q ≠ p`), which is why the assembly below calls
`hTWq q (n + 1)` rather than `hTWq q n` — a level-`(n+1)` Taylor–Wiles set is a
level-`n` one a fortiori, so nothing is lost and the degenerate case is gone.

**INTERFACE REPAIR 1 (2026-07-28): `hn : 1 ≤ n` IS A HYPOTHESIS, NOT A THING A
PROVER CAN READ OFF `hQ`.**  The paragraph above used to end "a prover of this
leaf may therefore assume `1 ≤ n` whenever it is needed, by reading the
congruence off `hQ`".  That is a non-sequitur and it made the leaf FALSE as
stated: at `n = 0` the congruence `q ≡ 1 [MOD p^0]` is `q ≡ 1 [MOD 1]`, which
every `q` satisfies, so it carries no information at all — least of all
`1 ≤ n`.  A level-`0` Taylor–Wiles set may therefore contain `q = 2` or `q = p`,
where `ρuniv` is only tame resp. flat, and the split-torus clause fails.  The
bound is now an explicit hypothesis.  It costs the assembly nothing: it already
supplies `n + 1`, so it discharges `hn` by `omega`.

**INTERFACE REPAIR 2 (2026-07-28): `hres` — the missing hypothesis was already
in the caller's hand.**  Step 1 needs the RESIDUAL Frobenius charpoly of
`ρuniv` at `q ∈ Q`, i.e. `(ρuniv.charFrob q).map πuniv`, and `hunivred` supplies
only its LINEAR coefficient, only away from `Suniv`.  Two gaps, both closed by
`hres : IsTaylorWilesResidual hpodd hW ρbar`, which the assembly already holds
and was discarding:

* the CONSTANT coefficient is the determinant, and `hres.det` pins `ρbar`'s to
  the same cyclotomic value `hρuniv.det` pins `ρuniv`'s to
  (`coeff_zero_charFrob_eq_of_det_eq`); with monicity and degree `2` that
  upgrades `hunivred` to FULL `charFrob` matching off `Suniv`;
* which is exactly the input of the Chebotarev–Brauer–Nesbitt leaf
  `exists_conj_of_charFrob_eq_away`, and a conjugacy makes the matching hold at
  EVERY place — in particular at the primes of `Q` that lie IN `Suniv`, which
  no hypothesis of this leaf reaches otherwise.

`IsTaylorWilesResidual` is deliberately NOT `IsHardlyRamified` (see its own
docstring): it drops `isFlat` and `isTameAtTwo`, the two clauses that together
with irreducibility the tree REFUTES.  So adding it does not reopen the
circularity the guard below closes — it is the weakened residual package this
whole section is stated against, and every sibling leaf already carries it.

`hadic`, `hπuniv`, `hunivred` are what make the datum's `π`, `S` and
`charFrob_compat` fields; `hadic` is used a second time to prove `πuniv`
CONTINUOUS (the maximal ideal is open in the `𝔪`-adic topology and is
`ker πuniv`), which is what lets `ρuniv` be base-changed along `πuniv` at all.
`hirr` is what the Chebotarev–Brauer–Nesbitt step consumes.

CIRCULARITY GUARD: inherited from the assembly —
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` and
`Slop.OddRep.isIrreducible_iff_forall` against `hirr`, any reduction-descent
lemma producing `IsHardlyRamified hpodd hW ρbar` from `hρuniv`, and
`Family.lean` with everything downstream of it, are BANNED as inputs.  A proof
ending in `exfalso` is the circular discharge again and must be rejected. -/
theorem exists_auxDeformationDatum.{uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (n : ℕ) (hn : 1 ≤ n) (Q : Finset ℕ)
    (hQ : IsTaylorWilesPrimeSet p ρbar n Q) :
    Nonempty (AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar) := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Runiv) Runiv := hcomplete
  -- `πuniv` is continuous: its kernel is the maximal ideal, which is open in
  -- the `𝔪`-adic topology, and `k` is discrete.  This is what makes the
  -- residual representation `ρuniv.baseChange k` exist at all.
  have hker : RingHom.ker πuniv = IsLocalRing.maximalIdeal Runiv :=
    IsLocalRing.ker_eq_maximalIdeal πuniv hπuniv
  have hmopen : IsOpen ((IsLocalRing.maximalIdeal Runiv : Ideal Runiv) :
      Set Runiv) := by
    have h := (isAdic_iff.mp hadic).1 1
    simpa using h
  have hπcont : Continuous πuniv := by
    apply continuous_of_continuousAt_zero πuniv
    unfold ContinuousAt
    rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
    filter_upwards [hmopen.mem_nhds (Submodule.zero_mem _)] with x hx
    exact RingHom.mem_ker.mp (by rw [hker]; exact hx)
  letI : Algebra Runiv k := πuniv.toAlgebra
  letI : ContinuousSMul Runiv k := continuousSMul_of_algebraMap Runiv k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
  -- FULL `charFrob` matching away from `Suniv`: the linear coefficients by
  -- `hunivred`, the constant ones by the two determinant conditions, degree and
  -- monicity because both are `charFrob`s of rank-2 representations.
  have hrankW' : Module.rank k (k ⊗[Runiv] (Fin 2 → Runiv)) = 2 := by
    rw [Module.rank_baseChange, hranku]
    simp
  have hcf : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ Suniv →
      (ρuniv.baseChange k).charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat := by
    intro q hq hqS
    have hmap := charFrob_baseChange (B := k)
      hq.toHeightOneSpectrumRingOfIntegersRat ρuniv
    rw [RingHom.algebraMap_toAlgebra] at hmap
    refine monic_natDegree_two_ext ?_
      (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat ρbar) ?_
      (charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat ρbar hW) ?_ ?_
    · rw [hmap]
      exact (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat
        ρuniv).map πuniv
    · rw [hmap, (charFrob_monic hq.toHeightOneSpectrumRingOfIntegersRat
        ρuniv).natDegree_map πuniv]
      exact charFrob_natDegree hq.toHeightOneSpectrumRingOfIntegersRat ρuniv
        hranku
    · rw [hmap, Polynomial.coeff_map]
      exact coeff_zero_charFrob_eq_of_det_eq hranku hρuniv.det hW hres.det πuniv
        (ringHom_padicInt_eq (πuniv.comp (algebraMap ℤ_[p] Runiv))
          (algebraMap ℤ_[p] k))
        hq.toHeightOneSpectrumRingOfIntegersRat
    · rw [hmap, Polynomial.coeff_map]
      exact hunivred q hq hqS
  -- … which Chebotarev–Brauer–Nesbitt upgrades to a residual identification …
  obtain ⟨e0, he0⟩ := exists_conj_of_charFrob_eq_away hW hirr hrankW'
    (ρuniv.baseChange k) Suniv hcf
  -- … hence to `charFrob` matching at EVERY place.  This last step is what the
  -- primes of `Q` lying INSIDE `Suniv` need: no hypothesis of this leaf
  -- constrains `ρuniv` at those places directly.
  have hall : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (ρuniv.charFrob v).map πuniv = ρbar.charFrob v := by
    intro v
    have h1 := charFrob_conj v (ρuniv.baseChange k) e0
    rw [he0] at h1
    have hmap := charFrob_baseChange (B := k) v ρuniv
    rw [RingHom.algebraMap_toAlgebra] at hmap
    rw [h1, hmap]
  have hpprime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have h2 := hpprime.two_le
    have hne : p ≠ 2 := by
      intro h
      rw [h] at hpodd
      simp [Nat.odd_iff] at hpodd
    omega
  -- THE CONTENT: the split-torus clause at each `q ∈ Q`.
  have hsplit : ∀ q ∈ Q, ∀ hq : q.Prime,
      ∃ (e : (Fin 2 → Runiv) ≃ₗ[Runiv] Runiv × Runiv)
        (χ δ : GaloisRep
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ)
          Runiv Runiv),
        (∀ (g : Field.absoluteGaloisGroup
            ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
            (v : Fin 2 → Runiv),
          e (ρuniv.toLocal hq.toHeightOneSpectrumRingOfIntegersRat g v) =
            (χ g (e v).1, δ g (e v).2)) ∧
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker := by
    intro q hqQ hq
    obtain ⟨hq', hcong, α, β, hαβ, hpoly⟩ := hQ.1 q hqQ
    -- `q ≡ 1 mod p^n` with `1 ≤ n` and `p` odd excludes `q = 2` and `q = p`,
    -- which is the ONLY place `hn` is used — and the reason it is a hypothesis.
    have hdvdpow : p ^ n ∣ q - 1 :=
      (Nat.modEq_iff_dvd' hq.one_lt.le).mp hcong.symm
    have hpd : p ∣ q - 1 :=
      dvd_trans (dvd_pow_self p (by omega : n ≠ 0)) hdvdpow
    have hq2 : q ≠ 2 := by
      intro h
      rw [h] at hpd
      have := Nat.le_of_dvd (by norm_num) hpd
      omega
    have hqp : q ≠ p := by
      intro h
      rw [h] at hpd
      have := Nat.le_of_dvd (by omega) hpd
      omega
    exact exists_isSplitTorusAt_of_isUnramifiedAt
      hq.toHeightOneSpectrumRingOfIntegersRat πuniv hπuniv ρuniv
      (hρuniv.isUnramified q hq ⟨hq2, hqp⟩) α β hαβ ((hall _).trans hpoly)
  exact ⟨{ R := Runiv
           isAdic := hadic
           isAdicComplete := hcomplete
           ρ := ρuniv
           rank_eq := hranku
           isRaisedLevelHardlyRamified :=
             { det := hρuniv.det
               isUnramified := fun q hq _ h2 hp =>
                 hρuniv.isUnramified q hq ⟨h2, hp⟩
               isFlat := hρuniv.isFlat
               isTameAtTwo := hρuniv.isTameAtTwo
               isSplitTorusAt := hsplit }
           π := πuniv
           π_surjective := hπuniv
           S := Suniv
           charFrob_compat := hunivred }⟩

/-! #### The RAISED-LEVEL deformation-condition clauses, and the machine

(New 2026-07-28, the cut of `exists_isWeaklyUniversal_auxDeformationDatum`
below.)

The cut mirrors the one already taken on the Hilbert twin
(`exists_isWeaklyUniversal_hilbertAuxDeformationDatum_of_clauses` in
`HardlyRamified/HilbertModularity.lean`, 2026-07-27) rather than inventing a
second architecture for the same node: the Schlessinger machine is separated
from the ARITHMETIC of the local conditions, which enters it only through the
clauses saying that `IsRaisedLevelHardlyRamified hpodd Q` is a deformation
condition in Mazur's sense — functoriality, gluing along fibre products,
finiteness at every finite level, and detection on the finite levels.

## THREE PLACES THE MIRROR IS NOT VERBATIM, AND WHY

**1. The residual pinning is TRACE-LEVEL with a finite exceptional set.**  The
Hilbert clauses pin `((ρ g).charpoly).map π = (ρbar g).charpoly` at every
`g ∈ G_F`.  That shape is not available on the `ℚ` side — the whole `ℚ` chain
carries only the linear `charFrob` coefficients away from a finite set, which
is exactly why `AuxDeformationDatum.charFrob_compat` has the shape it has (see
its docstring).  So the pinning carried here is `(πB, S, hπB)` in the
`charFrob_compat` shape, which every object of the raised-level category
supplies verbatim.

That is not a weakening.  The determinant clause of
`IsRaisedLevelHardlyRamified` pins `det ρ` to the cyclotomic character for
every object, so trace **plus** determinant is the whole rank-2 charpoly; and
`exists_conj_of_charFrob_eq_away` above (PROVEN) upgrades "charFrob agrees away
from a finite set, `ρbar` irreducible" to an actual conjugacy, hence to
agreement at EVERY prime — in particular at the `q ∈ Q`, which is where the
gluing and pro-limit clauses need residual distinctness.  A prover of those two
leaves should reach for that lemma first; it is what makes the exceptional set
harmless.

**2. The functoriality clause is the QUOTIENT one.**  The Hilbert twin proves
functoriality along an ARBITRARY continuous `ℤ_ℓ`-algebra map into a finite
local ring, using `isFlatAt_baseChange_of_numberField`.  On the `ℚ` side the
general-coefficient flat transfer `isHardlyRamified_baseChange` rests on the
OPEN Raynaud leaf `hasFlatProlongationAt_of_pi_surjection`, while the quotient
transfer `isHardlyRamified_baseChange_quotient` is sorry-free — and the `ℚ`
chain only ever pushes a deformation forward along a quotient map (the
`p`-adic tower of `exists_ringHom_quotient_padicTower_of_finiteTests`, whose
own docstring records exactly this) followed by a conjugation (the reframing
transport).  So `IsAuxFunctorialityClause` carries those two operations, both
of which are PROVEN below, and no dependence on the Raynaud leaf is created.

**3. The fibre-product clause asks `B` to be the fibre product ALGEBRAICALLY.**
The Hilbert twin also asks `Topology.IsEmbedding (fun b => (p₁ b, p₂ b))`.
Here the pairing is asked to be injective instead; the coefficient rings of the
clause are `Finite`, and the gluing argument uses only the ring-theoretic
universal property.  Recorded rather than silently dropped.

## THE ONE FAITHFULNESS POINT, INHERITED FROM THE TWIN

**The naive fibre-product clause is FALSE**, and so is the naive pro-limit
clause; both are repaired by the residual pinning.  The counterexample is
elementary and is worth having in front of a prover of either leaf.  Let `k` be
a field, `A₁ = A₂ = k[ε]`, `A₀ = k`, so that `B = A₁ ×_{A₀} A₂ ≅ k[u,v]/(u,v)²`
with `u = (ε,0)`, `v = (0,ε)`.  Let `σ` act by

    ρ₁(σ) = diag(1+ε, 1)                  over `A₁`,
    ρ₂(σ) = [[1+ε, -ε], [0, 1]]           over `A₂`,

the second being `g · diag(1+ε,1) · g⁻¹` for `g = [[1,1],[0,1]]` and therefore
also split.  Both reduce to the identity over `A₀`, so the pair glues to

    ρ(σ) = [[1+u+v, -v], [0, 1]]          over `B`,

which is NOT diagonalisable over `B`: an eigenvector for the eigenvalue `1`
would need `(u+v)x₁ = v x₂`, impossible modulo `(u,v)²` for an `x` that is part
of a basis.  So both projections satisfy the split-torus clause and `ρ` does
not — the clause is not a deformation condition on its own.

What kills the counterexample is residual DISTINCTNESS: once the two residual
characters differ, the idempotent cutting out the `χ`-line is determined by its
residue (idempotents lifting along a nilpotent ideal are unique once their
residue is fixed), so the decompositions over `A₀` cannot disagree and the glue
exists.  In the example both residual characters are trivial, the excluded
case.  This is Wiles, Ann. of Math. 141 (1995), ch. 3, and it is the honest
form of "the local deformation functor at a Taylor–Wiles prime is
representable BECAUSE `ρbar(Frob_q)` has distinct eigenvalues".

References: Schlessinger, *Functors of Artin rings*; Mazur, *Deforming Galois
representations*, §§18–23; Ramakrishna, Compositio 87 (1993);
Darmon–Diamond–Taylor §§2, 5.3; Wiles, ch. 3. -/

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The split-torus clause transfers along base change** (PROVEN
2026-07-28): a decomposition `V ≃ₗ[R] R × R` carrying `ρ|_{G_{ℚ_q}}` to
`(χ, δ)` base-changes to `B ⊗[R] V ≃ₗ[B] B × B` carrying `(ρ ⊗ B)|_{G_{ℚ_q}}`
to `(χ ⊗ B, δ ⊗ B)`.

The `ℚ`-side twin of `isHilbertSplitTorusAt_baseChange`, and the proof is that
one's: the identification is `TensorProduct.prodRight` followed by
`TensorProduct.AlgebraTensorModule.rid` on each factor, equivariance is checked
on simple tensors, and the kernel of a character only GROWS under base change
followed by conjugation, so `δ ⊗ B` is still trivial on
`localInertiaGroup`. -/
lemma isSplitTorusAt_baseChange
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B]
    {q : ℕ} (hq : q.Prime) {ρ : GaloisRep ℚ R V}
    (hs : ∃ (e : V ≃ₗ[R] R × R)
      (χ δ : GaloisRep
        ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) R R),
      (∀ (g : Field.absoluteGaloisGroup
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
          (v : V),
        e (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat g v) =
          (χ g (e v).1, δ g (e v).2)) ∧
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker) :
    ∃ (e : (B ⊗[R] V) ≃ₗ[B] B × B)
      (χ δ : GaloisRep
        ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) B B),
      (∀ (g : Field.absoluteGaloisGroup
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
          (v : B ⊗[R] V),
        e ((ρ.baseChange B).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
            g v) =
          (χ g (e v).1, δ g (e v).2)) ∧
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker := by
  obtain ⟨e, χ, δ, hint, hδker⟩ := hs
  set rid : (B ⊗[R] R) ≃ₗ[B] B := TensorProduct.AlgebraTensorModule.rid R B B
  set τ : (B ⊗[R] (R × R)) ≃ₗ[B] B × B :=
    (TensorProduct.prodRight R B B R R).trans (rid.prodCongr rid) with hτ
  refine ⟨(LinearEquiv.baseChange R B V (R × R) e).trans τ,
    (χ.baseChange B).conj rid, (δ.baseChange B).conj rid, ?_, ?_⟩
  · intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp [Prod.ext_iff]
    | add a b ha hb => simp only [map_add, ha, hb, Prod.fst_add, Prod.snd_add,
        Prod.mk_add_mk]
    | tmul c m =>
      have hkey : ∀ (η : GaloisRep
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) R R)
          (r : R),
          ((η.baseChange B).conj rid) g (rid (c ⊗ₜ[R] r)) =
            rid (c ⊗ₜ[R] (η g r)) := by
        intro η r
        rw [GaloisRep.conj_apply, LinearEquiv.conj_apply, LinearMap.comp_apply,
          LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply,
          show ((η.baseChange B) g : Module.End B (B ⊗[R] R)) =
            LinearMap.baseChange B (η g) from rfl,
          LinearMap.baseChange_tmul]
      have hloc : ((ρ.baseChange B).toLocal
          hq.toHeightOneSpectrumRingOfIntegersRat) g (c ⊗ₜ[R] m) =
          c ⊗ₜ[R] ((ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) g m) :=
        rfl
      simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, hloc,
        hτ, LinearEquiv.trans_apply, TensorProduct.prodRight_tmul,
        LinearEquiv.prodCongr_apply]
      rw [hint g m, Prod.mk.injEq]
      exact ⟨(hkey χ (e m).1).symm, (hkey δ (e m).2).symm⟩
  · intro σ hσ
    have hδσ : δ σ = 1 := hδker hσ
    show (δ.baseChange B).conj rid σ = 1
    rw [GaloisRep.conj_apply,
      show (δ.baseChange B) σ = LinearMap.baseChange B (δ σ) from rfl, hδσ]
    refine LinearMap.ext fun c => ?_
    simp

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The RAISED-LEVEL condition transfers along quotient specialization of the
coefficients** (PROVEN 2026-07-28; the raised-level twin of the imported
`isHardlyRamified_baseChange_quotient`).

Four of the five clauses are that lemma's proofs verbatim — the determinant
maps along the structure morphism (`LinearMap.det_baseChange`), unramifiedness
(now only away from `Q`) passes by the existing instance on
`GaloisRep.IsUnramifiedAt`, flatness at `p` is `isFlatAt_baseChange_quotient`
and tameness at `2` is `isTameAtTwo_baseChange` — and the fifth is
`isSplitTorusAt_baseChange` immediately above.  The lemma is NOT deduced from
its base-level twin: the raised predicate neither implies nor is implied by the
base-level one.

**Why the QUOTIENT and not a general coefficient map** — see the section
preamble: the general-coefficient flat transfer on the `ℚ` side rests on the
open Raynaud leaf `hasFlatProlongationAt_of_pi_surjection`, and the `ℚ` chain
only ever needs the quotient case. -/
lemma isRaisedLevelHardlyRamified_baseChange_quotient {p : ℕ} [Fact p.Prime]
    {hpodd : Odd p} (Q : Finset ℕ)
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] {hdimV : Module.rank R V = 2}
    (P : Ideal R) [IsLocalRing (R ⧸ P)]
    (hdimQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] V) = 2)
    {ρ : GaloisRep ℚ R V} (h : IsRaisedLevelHardlyRamified hpodd Q hdimV ρ) :
    IsRaisedLevelHardlyRamified hpodd Q hdimQ (ρ.baseChange (R ⧸ P)) := by
  constructor
  · -- the determinant condition maps along the quotient map
    intro g
    have hdet : (ρ.baseChange (R ⧸ P)).det g =
        algebraMap R (R ⧸ P) (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange (R ⧸ P)) g) = _
      rw [show ((ρ.baseChange (R ⧸ P)) g :
          Module.End (R ⧸ P) ((R ⧸ P) ⊗[R] V)) =
        LinearMap.baseChange (R ⧸ P) (ρ g) from rfl,
        LinearMap.det_baseChange]
      rfl
    rw [hdet, h.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness away from `Q` passes to the base change
    intro q hq hqQ hq2 hqp
    letI : ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
      h.isUnramified q hq hqQ hq2 hqp
    infer_instance
  · -- flatness at `p`
    exact isFlatAt_baseChange_quotient P h.isFlat
  · -- tameness at `2`
    exact isTameAtTwo_baseChange (R ⧸ P) h.isTameAtTwo
  · -- the split torus at every `q ∈ Q`
    intro q hqQ hq
    exact isSplitTorusAt_baseChange (R ⧸ P) hq (h.isSplitTorusAt q hqQ hq)

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- **The RAISED-LEVEL condition is invariant under an isomorphism of the
representation space** (PROVEN 2026-07-28; the raised-level twin of
`isHardlyRamified_conj` above, with the same four proofs plus the split-torus
clause, whose decomposition is precomposed with the inverse isomorphism). -/
lemma isRaisedLevelHardlyRamified_conj {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
    (Q : Finset ℕ)
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Free R N]
    {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
    {ρ : GaloisRep ℚ R M} (h : IsRaisedLevelHardlyRamified hpodd Q hdimM ρ)
    (e : M ≃ₗ[R] N) :
    IsRaisedLevelHardlyRamified hpodd Q hdimN (ρ.conj e) := by
  constructor
  · -- determinant: conjugation-invariant
    intro g
    rw [GaloisRep.det_apply, GaloisRep.conj_apply, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
    exact h.det g
  · -- unramifiedness away from `Q`: the kernel of the local rep only grows
    intro q hq hqQ hq2 hqp
    have hun := h.isUnramified q hq hqQ hq2 hqp
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
  · -- tameness at `2`: compose the quotient with the inverse isomorphism
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
  · -- the split torus at `q ∈ Q`: precompose the decomposition with `e⁻¹`
    intro q hqQ hq
    obtain ⟨f, χ, δ, hint, hδker⟩ := h.isSplitTorusAt q hqQ hq
    refine ⟨e.symm.trans f, χ, δ, ?_, hδker⟩
    intro g v
    have h1 := hint g (e.symm v)
    show f (e.symm (((ρ.conj e).toLocal
      hq.toHeightOneSpectrumRingOfIntegersRat) g v)) = _
    rw [GaloisRep.toLocal_apply, GaloisRep.conj_apply,
      LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      ← GaloisRep.toLocal_apply, h1]
    rfl

set_option linter.checkUnivs false in
open scoped TensorProduct in
/-- **RAISED-LEVEL functoriality clause** — the two coefficient operations the
`ℚ` Schlessinger chain performs on a deformation: specialization along a
QUOTIENT of the coefficient ring (the `p`-adic tower of
`exists_ringHom_quotient_padicTower_of_finiteTests`) and conjugation by a
linear isomorphism of the representation space (the reframing transport).

Both conjuncts are PROVEN immediately below, so this clause costs the machine
nothing; it is carried as a hypothesis rather than used directly so that the
machine leaf genuinely consumes the two raised-level transfers — a sorried body
contributes no dependency edges, so a transfer the machine merely *could* use
would be free-floating until the machine is proven.

See the section preamble for why this is the quotient clause and not the
Hilbert twin's general-coefficient one. -/
def IsAuxFunctorialityClause.{a} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ) : Prop :=
  (∀ {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[p] R]
      {V : Type a} [AddCommGroup V] [Module R V] [Module.Finite R V]
      [Module.Free R V] {hdimV : Module.rank R V = 2}
      (P : Ideal R) [IsLocalRing (R ⧸ P)]
      (hdimQ : Module.rank (R ⧸ P) ((R ⧸ P) ⊗[R] V) = 2)
      {ρ : GaloisRep ℚ R V},
      IsRaisedLevelHardlyRamified hpodd Q hdimV ρ →
      IsRaisedLevelHardlyRamified hpodd Q hdimQ (ρ.baseChange (R ⧸ P))) ∧
  (∀ {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLocalRing R] [Algebra ℤ_[p] R]
      {M : Type a} [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Free R M]
      {N : Type a} [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Module.Free R N]
      {hdimM : Module.rank R M = 2} (hdimN : Module.rank R N = 2)
      {ρ : GaloisRep ℚ R M},
      IsRaisedLevelHardlyRamified hpodd Q hdimM ρ →
      ∀ e : M ≃ₗ[R] N,
        IsRaisedLevelHardlyRamified hpodd Q hdimN (ρ.conj e))

set_option linter.checkUnivs false in
/-- **Functoriality of the RAISED-LEVEL condition** (PROVEN 2026-07-28): the
two transfers proven above, packaged as the clause the machine consumes. -/
theorem isAuxFunctorialityClause.{a} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ) : IsAuxFunctorialityClause.{a} hpodd Q := by
  refine ⟨?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ P _ hdimQ _ h
    exact isRaisedLevelHardlyRamified_baseChange_quotient Q P hdimQ h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdimN _ h e
    exact isRaisedLevelHardlyRamified_conj Q hdimN h e

set_option linter.checkUnivs false in
open scoped TensorProduct in
/-- **RAISED-LEVEL fibre-product clause** (Schlessinger's H1 and H2), with the
RESIDUAL PINNING that the section preamble's `k[u,v]/(u,v)²` counterexample
forces.

`B` is the fibre product `A₁ ×_{A₀} A₂` in the category of rings: the pairing
`b ↦ (p₁ b, p₂ b)` is injective and hits every compatible pair.  Given that the
base changes of `ρ` to `A₁` and to `A₂` satisfy the raised-level condition, so
does `ρ`.

**The pinning is the triple `(πB, S, hπB)`** — a reduction to `k` under which
the linear `charFrob` coefficients of `ρ` are those of `ρbar` away from a
finite set of primes, i.e. exactly `AuxDeformationDatum.charFrob_compat`.
**Without it the statement is FALSE**; do not "simplify" it away.  With it, and
with `hQ`, `exists_conj_of_charFrob_eq_away` makes the residual representation
a conjugate of `ρbar`, hence its charpoly at `Frob_q` for `q ∈ Q` is
`(X - α)(X - β)` with `α ≠ β`; the idempotent cutting out the `χ`-line is then
determined by its residue, so the two decompositions over `A₀` agree up to
swapping the factors and glue.

The pinning is discharged for free at every use site: the machine applies this
clause only to objects of the raised-level deformation category, each of which
carries `π`, `S` and `charFrob_compat` by definition. -/
def IsAuxFibreProductClause.{a, uK, uW} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ)
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) : Prop :=
  ∀ {A₀ : Type a} [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀]
    [IsLocalRing A₀] [Algebra ℤ_[p] A₀] [Finite A₀]
    {A₁ : Type a} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLocalRing A₁] [Algebra ℤ_[p] A₁] [Finite A₁]
    {A₂ : Type a} [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂]
    [IsLocalRing A₂] [Algebra ℤ_[p] A₂] [Finite A₂]
    {B : Type a} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Algebra ℤ_[p] B] [Finite B]
    (f₁ : A₁ →+* A₀) (f₂ : A₂ →+* A₀), Function.Surjective f₂ →
    ∀ (p₁ : B →+* A₁) (p₂ : B →+* A₂) (hp₁ : Continuous p₁)
      (hp₂ : Continuous p₂),
    p₁.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] A₁ →
    p₂.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] A₂ →
    f₁.comp p₁ = f₂.comp p₂ →
    Function.Injective (fun b : B => (p₁ b, p₂ b)) →
    (∀ (a₁ : A₁) (a₂ : A₂), f₁ a₁ = f₂ a₂ → ∃ b : B, p₁ b = a₁ ∧ p₂ b = a₂) →
    ∀ {V : Type a} [AddCommGroup V] [Module B V] [Module.Finite B V]
      [Module.Free B V] {hdimV : Module.rank B V = 2}
      {ρ : GaloisRep ℚ B V} (πB : B →+* k)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
    (∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      πB ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) →
    (letI : Algebra B A₁ := p₁.toAlgebra
     letI : ContinuousSMul B A₁ := continuousSMul_of_algebraMap B A₁
       (by rw [RingHom.algebraMap_toAlgebra]; exact hp₁)
     ∀ hdim₁ : Module.rank A₁ (A₁ ⊗[B] V) = 2,
       IsRaisedLevelHardlyRamified hpodd Q hdim₁ (ρ.baseChange A₁)) →
    (letI : Algebra B A₂ := p₂.toAlgebra
     letI : ContinuousSMul B A₂ := continuousSMul_of_algebraMap B A₂
       (by rw [RingHom.algebraMap_toAlgebra]; exact hp₂)
     ∀ hdim₂ : Module.rank A₂ (A₂ ⊗[B] V) = 2,
       IsRaisedLevelHardlyRamified hpodd Q hdim₂ (ρ.baseChange A₂)) →
    IsRaisedLevelHardlyRamified hpodd Q hdimV ρ

set_option linter.checkUnivs false in
/-- **RAISED-LEVEL finiteness clause** (Schlessinger's H3) — the `ℚ`-side twin
of `IsHilbertAuxFiniteFramesClause`.

No residual pinning: this is Hermite–Minkowski with `Q` adjoined to the bad
set, and it mentions `ρbar` nowhere. -/
def IsAuxFiniteFramesClause.{a} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ) : Prop :=
  ∀ (A : Type a) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLocalRing A] [Algebra ℤ_[p] A] [Finite A] [DiscreteTopology A],
    {ρ : GaloisRep ℚ A (Fin 2 → A) |
      IsRaisedLevelHardlyRamified hpodd Q (rank_finTwoFun A) ρ}.Finite

set_option linter.checkUnivs false in
open scoped TensorProduct in
/-- **RAISED-LEVEL pro-limit clause** — the `ℚ`-side twin of
`IsHilbertAuxProLimitClause`, with the same RESIDUAL PINNING as the
fibre-product clause and for the same reason.

The four base-level clauses are detected on the finite levels
unconditionally.  The split-torus clause is not: the decompositions supplied at
the finite levels need not be COMPATIBLE with the transition maps, and without
compatibility there is nothing to pass to the limit.  The pinning repairs it
exactly as it repairs the gluing clause — residual distinctness at `q ∈ Q`
(through `exists_conj_of_charFrob_eq_away`, see the section preamble) makes the
decomposition at each level unique once the residual eigenvalue attached to `χ`
is fixed, so the levels form a compatible system and adic completeness
assembles it.

(An alternative repair, recorded because it may be cheaper and needs no
pinning: the decompositions at a level with FINITE quotient ring form a finite
nonempty set, and an inverse system of finite nonempty sets over a cofiltered
index has a section — `nonempty_sections_of_finite_cofiltered_system`, already
in this module's import cone through `Mathlib.CategoryTheory.CofilteredSystem`.
That route needs `Finite (R ⧸ I)`, which the clause as stated does not give,
which is why the pinning is the form carried here.) -/
def IsAuxProLimitClause.{a, uK, uW} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ)
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W] (ρbar : GaloisRep ℚ k W) : Prop :=
  ∀ {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R],
    IsAdic (IsLocalRing.maximalIdeal R) →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ {ρ : GaloisRep ℚ R (Fin 2 → R)} (πR : R →+* k)
      (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ))),
    (∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      πR ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) →
    (∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) →
    IsRaisedLevelHardlyRamified hpodd Q (rank_finTwoFun R) ρ

set_option linter.checkUnivs false in
/-- **The RAISED-LEVEL gluing clause** (sorry node, LEAF A2′-2a of the
2026-07-28 clause cut of `exists_isWeaklyUniversal_auxDeformationDatum`).

The four base-level clauses glue exactly as at the base level — `Q` is disjoint
from `{2, p}` by the congruence clause of `hQ` at level `n ≥ 1` (`q ≡ 1 mod pⁿ`
with `p` odd forces `q ≠ 2` and `q ≠ p`), so the tame-at-`2` and flat-at-`p`
residues are untouched by the raising.

**The new content is the split-torus clause, and it is where `hQ` is spent.**
Given decompositions of `ρ ⊗ A₁` and `ρ ⊗ A₂`, their images over `A₀` are two
decompositions of the same local representation.  `hQ` gives `α ≠ β` in the
residual charpoly at `Frob_q`, and the pinning `(πB, S, hπB)` transports that
to `ρ`: by `exists_conj_of_charFrob_eq_away` (PROVEN above) the residual
representation of `ρ` is a conjugate of `ρbar`, so its charpoly at `Frob_q`
agrees with `ρbar`'s at EVERY prime — the finite exceptional set `S` costs
nothing — and the two residual characters of any decomposition at `q` are
`{α, β}`, hence distinct.  An idempotent of `End(A₀²)` commuting with the local
action is then determined by its residue (idempotents lift uniquely along a
nilpotent ideal), so the two decompositions over `A₀` agree up to swapping the
two factors; swap `e₂` if necessary and glue the two idempotents into one over
`B`, which is a decomposition of `ρ` because `B` is the fibre product.

**This leaf is FALSE without the pinning** — see the section preamble's
`k[u,v]/(u,v)²` counterexample.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above; in particular a
proof ending in `exfalso` against `hirr` is the circular discharge and must be
rejected.

References: Wiles, Ann. of Math. 141 (1995), ch. 3; Darmon–Diamond–Taylor
§5.3; Mazur, *Deforming Galois representations*, §§18–23. -/
theorem isAuxFibreProductClause.{a, uK, uW} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (n : ℕ) (Q : Finset ℕ) (hQ : IsTaylorWilesPrimeSet p ρbar n Q) :
    IsAuxFibreProductClause.{a, uK, uW} hpodd Q ρbar :=
  sorry

set_option linter.checkUnivs false in
/-- **The RAISED-LEVEL finiteness clause** (sorry node, LEAF A2′-2b of the
2026-07-28 clause cut).

Hermite–Minkowski with `Q` adjoined to the bad set.  The base-level finiteness
input of this file — the dual-number tangent finiteness `_hfin` of
`exists_framedStrictlyUniversal_hardlyRamified_finiteTests` — is cut out by
unramifiedness away from `{2, p}` ONLY, and the raised-level set is not
contained in it, so it does not apply verbatim.  What is needed is the same
Hermite–Minkowski chain with the bad set `{2, p} ∪ Q` in place of `{2, p}`
throughout; `Q` is a `Finset`, so the enlarged bad set is still finite and
every step goes through unchanged.  This is a mirror of proven material rather
than new mathematics, and it is stated as one leaf because the steps are
mechanical and share one binder list.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem isAuxFiniteFramesClause.{a} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    (Q : Finset ℕ) : IsAuxFiniteFramesClause.{a} hpodd Q :=
  sorry

/-! #### `isAuxProLimitClause`, decomposed field by field

Added 2026-07-28.  `IsRaisedLevelHardlyRamified` is a five-field structure, and the
limit passage is proven field by field: the first four are the four fields of
`IsHardlyRamified`, whose limit passage `isHardlyRamified_of_forall_isOpen_quotient`
is already PROVEN in `HardlyRamified/Deformation.lean`, and only the fifth — the split
torus at `q in Q` — is new.  The five leaves below are those five fields; the clause
itself is their assembly and carries no `sorry` of its own.

**Why this decomposition is safe where the fibre-product one is not.**  The
`isAuxFibreProductClause` ROUTE AUDIT records that the base-level fibre-product gluing
carries `5 <= l` and spends it on the tame clause, whose `l = 3` case was refuted.  The
base-level LIMIT passage carries no such hypothesis — checked against the two
signatures on 2026-07-28 — so `Odd p` suffices here and the obstruction does not
transfer.  See `raisedLevelIsTameAtTwo_of_forall_isOpen_quotient` below. -/

set_option linter.checkUnivs false in
/-- **The cyclotomic determinant passes to the adic limit** (PROVEN 2026-07-28;
LEAF A2'-2c-i of the decomposition of `isAuxProLimitClause` below).

`R` is `𝔪`-adically complete, hence `𝔪`-adically separated, so two elements agreeing
in every `R ⧸ 𝔪^(n+1)` are equal.  At each level the determinant condition is handed
over by the level datum, and `LinearMap.det_baseChange` says the base-changed
determinant is the image of `ρ.det g` — the exact bridge
`isRaisedLevelHardlyRamified_baseChange_quotient` above uses in the other direction.

This is the `det` half of `isHardlyRamified_of_forall_isOpen_quotient`
(`HardlyRamified/Deformation.lean`, PROVEN), transcribed from the framed
`pushforwardFrame` setting into the `baseChange` setting this clause is stated in.
It uses NO hypothesis on `Q`, on `ρbar` or on the pinning: the determinant clause is
verbatim the base-level one, and level raising does not touch it. -/
theorem raisedLevelDet_of_forall_isOpen_quotient.{a} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime] (Q : Finset ℕ)
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)}
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) :
    ∀ g, ρ.det g = algebraMap ℤ_[p] R
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv) := by
  classical
  have hsep : ∀ x y : R,
      (∀ n : ℕ, x - y ∈ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) → x = y := by
    intro x y hxy
    have h0 : x - y = 0 := by
      refine IsHausdorff.haus (hcomplete.toIsHausdorff) _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      cases n with
      | zero => simp
      | succ m => exact hxy m
    exact sub_eq_zero.mp h0
  have hpow : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) :=
    (isAdic_iff.mp hadic).1
  have hnetop : ∀ n : ℕ, (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≠ ⊤ := by
    intro n htop
    have hle : (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R) ≤
        IsLocalRing.maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero n)
    rw [htop, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle
  have hlocal : ∀ J : Ideal R, J ≠ ⊤ → IsLocalRing (R ⧸ J) := by
    intro J hJt
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJt
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hrk : ∀ (J : Ideal R) [IsLocalRing (R ⧸ J)],
      Module.rank (R ⧸ J) ((R ⧸ J) ⊗[R] (Fin 2 → R)) = 2 := by
    intro J _
    simp
  intro g
  refine hsep _ _ fun n => ?_
  haveI := hlocal _ (hnetop n)
  have hd := (hlev (IsLocalRing.maximalIdeal R ^ (n + 1)) (hpow (n + 1)) (hrk _)).det g
  have hdet : (ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R))).det g =
      algebraMap R (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R)) (ρ.det g) := by
    show LinearMap.det
      ((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R))) g) = _
    rw [show ((ρ.baseChange (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R))) g :
        Module.End _ _) = LinearMap.baseChange _ (ρ g) from rfl,
      LinearMap.det_baseChange]
    rfl
  rw [hdet, IsScalarTower.algebraMap_apply ℤ_[p] R
    (R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) : Ideal R))] at hd
  exact Ideal.Quotient.eq.mp hd

set_option linter.checkUnivs false in
/-- **Unramifiedness outside `Q ∪ {2, p}` passes to the adic limit** (SORRY LEAF, cut
out 2026-07-28; LEAF A2'-2c-ii of the decomposition of `isAuxProLimitClause` below).

# ROUTE

The `isUnramified` half of `isHardlyRamified_of_forall_isOpen_quotient`
(`HardlyRamified/Deformation.lean`, PROVEN) with `intro q hq hqQ` in place of
`intro q hq`, the extra `q ∉ Q` being passed straight to the level datum.  The
argument is the separation argument already written out in
`raisedLevelDet_of_forall_isOpen_quotient` above: for `σ` in the inertia group, the
entries of `ρ.toLocal v σ x - x` lie in `𝔪^(n+1)` for every `n`, because they vanish
in the level quotient; adic separatedness makes them zero.

# WHAT IT COSTS BEYOND THE TRANSCRIPTION

The base-level proof is written in the FRAMED setting and reads the level-`J` value
off `pushforwardFrame (Ideal.Quotient.mk J) hmk ρ`, where the level representation
acts on `Fin 2 → (R ⧸ J)` and the comparison is the pointwise `fun i => mk (x i)`.
This clause is stated with `ρ.baseChange (R ⧸ J)`, acting on `(R ⧸ J) ⊗[R] (Fin 2 → R)`.
The bridge is the one named in this leaf's parent audit:
`pushforwardFrame ψ hψ ρ = (ρ.baseChange A).conj (TensorProduct.piScalarRight R A A (Fin 2))`,
together with `isRaisedLevelHardlyRamified_conj` (PROVEN above) to move the predicate
across it.  Converting `hlev` into the framed form ONCE, at the top of the proof, is
expected to discharge this leaf and the two below together.

Both-ways audit: `hadic` and `hcomplete` are both load-bearing — they are exactly what
makes `⋂_n 𝔪^n = 0`, and without separatedness a representation trivial at every finite
level need not be trivial.  No hypothesis on `ρbar`, `Q` or the pinning is used or
needed; in particular this leaf cannot be discharged circularly against `hirr`. -/
theorem raisedLevelIsUnramified_of_forall_isOpen_quotient.{a} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime] (Q : Finset ℕ)
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)}
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) :
    ∀ q (hq : q.Prime), q ∉ Q → q ≠ 2 → q ≠ p →
      ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := sorry

set_option linter.checkUnivs false in
/-- **Flatness at `p` passes to the adic limit** (SORRY LEAF, cut out 2026-07-28;
LEAF A2'-2c-iii of the decomposition of `isAuxProLimitClause` below).

# ROUTE

The `isFlat` half of `isHardlyRamified_of_forall_isOpen_quotient`
(`HardlyRamified/Deformation.lean`, PROVEN), which is the easiest of the four at the
base level because `IsFlatAt` is *already* a condition on the open quotients — the
proof is a re-indexing, plus the separate treatment of `I = ⊤` (the unit ideal carries
no level datum, and both sides are subsingletons there).

The same framed-vs-`baseChange` bridge noted on
`raisedLevelIsUnramified_of_forall_isOpen_quotient` above applies, and
`isFlatAt_baseChange_quotient` (PROVEN, used in
`isRaisedLevelHardlyRamified_baseChange_quotient` above) is the level-wise half.

Both-ways audit: as for the previous leaf.  Verbatim the base-level clause — level
raising does not touch flatness at `p`, since `Q` is disjoint from `{2, p}`. -/
theorem raisedLevelIsFlat_of_forall_isOpen_quotient.{a} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime] (Q : Finset ℕ)
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)}
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) :
    ρ.IsFlatAt (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
      (Fact.out : p.Prime)) := sorry

set_option linter.checkUnivs false in
/-- **The tame quotient character at `2` passes to the adic limit** (SORRY LEAF, cut
out 2026-07-28; LEAF A2'-2c-iv of the decomposition of `isAuxProLimitClause` below).

# ROUTE

The `isTameAtTwo` half of `isHardlyRamified_of_forall_isOpen_quotient`
(`HardlyRamified/Deformation.lean`, PROVEN), whose base-level ingredient is
`isTameAtTwo_of_forall_isOpen_quotient` in the same file.

**This is the leaf on which the `p = 3` obstruction recorded on
`isAuxFibreProductClause` does NOT bite, and that is worth stating explicitly because
the two leaves look symmetric and are not.**  The base-level *fibre-product* gluing
`isHardlyRamified_of_fibreProduct` carries `(hℓ5 : 5 ≤ ℓ)` and spends it entirely on
`isTameAtTwo_of_fibreProduct`, whose `ℓ = 3` case was REFUTED on 2026-07-26.  The
base-level *limit* passage `isHardlyRamified_of_forall_isOpen_quotient` carries **no**
such hypothesis, and neither does `isTameAtTwo_of_forall_isOpen_quotient`: both are
proven for every odd `ℓ`.  Verified against the source on 2026-07-28 by reading the
two signatures.  So `Odd p` genuinely suffices here.

Both-ways audit: as for the two leaves above; the same framed-vs-`baseChange` bridge
is the only work beyond transcription. -/
theorem raisedLevelIsTameAtTwo_of_forall_isOpen_quotient.{a} {p : ℕ} (hpodd : Odd p)
    [Fact p.Prime] (Q : Finset ℕ)
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)}
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) :
    ∃ (π : (Fin 2 → R) →ₗ[R] R) (_ : Function.Surjective π)
        (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2], ∀ v : Fin 2 → R,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
          AddSubgroup Z2bar) (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) := sorry

/-! ### The TRACE-ONLY conjugacy bridge (flt-lean-397, 2026-07-28)

**AUDIT CORRECTION.**  The docstrings of `isAuxFibreProductClause`,
`IsAuxProLimitClause` and `raisedLevelIsSplitTorusAt_of_forall_isOpen_quotient`
below all say that "by `exists_conj_of_charFrob_eq_away` the residual
representation of `ρ` is a conjugate of `ρbar`".  **That theorem does not apply
from the hypotheses these clauses carry.**  `exists_conj_of_charFrob_eq_away`
(above, and its shared node in `BrauerNesbittConjugacy.lean`) demands FULL
`charFrob` agreement away from `S`; the residual pinning actually carried — by
`IsAuxProLimitClause`, by `IsAuxFibreProductClause` and by
`AuxDeformationDatum.charFrob_compat` — supplies only `coeff 1`, the Frobenius
trace up to sign.  The missing coefficient is `coeff 0`, the determinant, and the
usual repair `coeff_zero_charFrob_eq_of_isHardlyRamified` above needs
`det ρbar` to be the mod-`p` cyclotomic character — which neither `hirr` nor
`hQ` supplies, and which these statements deliberately do not carry (the module
docstring's own note: the `ℚ`-side chain "carries only the linear `charFrob`
coefficients").

The gap is quantitative, not a technicality.  Take `p = 5`, `k = 𝔽₅`, `α = 1`,
`β = 2`, and `q ≡ 1 [MOD 5]` as `IsTaylorWilesPrimeSet` requires.  Then
`ρbar.charFrob q = (X - C 1) * (X - C 2) = X² - 3X + 2` has DISTINCT roots, while
the polynomial with the same linear coefficient and the cyclotomic constant term
forced on `ρ` by `raisedLevelDet_of_forall_isOpen_quotient` above is
`X² - 3X + C (q : 𝔽₅) = X² - 3X + 1`, of discriminant `9 - 4 = 5 = 0`: a DOUBLE
root.  So place-by-place, trace agreement genuinely fails to transport residual
distinctness, which is the one fact the split-torus clauses need.

`exists_conj_of_charFrobCoeffOne_eq_away` below closes the gap and needs NO new
hypothesis.  `p` is odd, so `2` is a unit in `k`; propagate the trace agreement
from the Frobenius conjugacy classes to all of `Gal(ℚ̄/ℚ)` by Chebotarev density
FIRST, and only then recover the determinant, by rank-two Cayley–Hamilton
(`two_mul_det_eq_of_finrank_two`, `2 · det f = (tr f)² - tr (f²)`).  That is
exactly the route `exists_conj_of_charFrob_eq_away_of_two_ne_zero`
(`BrauerNesbittConjugacy.lean`, PROVEN) already takes; the only change is that
trace agreement becomes the hypothesis instead of a consequence of charpoly
agreement.  Stated in the general form, so `isAuxFibreProductClause` — which has
the identical gap — can consume it unchanged.
-/

/-- **A ring homomorphism from a LOCAL ring to a FINITE field is local** (PROVEN):
its kernel is the maximal ideal.  `R ⧸ ker π` injects into `k` by `kerLift`, hence
is a finite integral domain, hence a field (`Finite.isField_of_domain`), so `ker π`
is maximal — and in a local ring the maximal ideal is unique.

This is what makes the residual pinning `πR : R →+* k` of `IsAuxProLimitClause`
automatically CONTINUOUS, without continuity being carried as a datum: the maximal
ideal is open because the topology is maximal-adic, `k` is discrete, so `πR` is
locally constant.  Continuity is what the base change `ρ.baseChange k` along `πR`
needs (`GaloisRep.baseChange` asks for `ContinuousSMul`), and the base change is
how the abstract residual representation of `ρ` is formed at all. -/
lemma ker_eq_maximalIdeal_of_ringHom_finiteField
    {R : Type*} [CommRing R] [IsLocalRing R] {kk : Type*} [Field kk] [Finite kk]
    (π : R →+* kk) : RingHom.ker π = IsLocalRing.maximalIdeal R := by
  have hne : RingHom.ker π ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ RingHom.ker π := htop ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R ⧸ RingHom.ker π) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : Finite (R ⧸ RingHom.ker π) :=
    Finite.of_injective (RingHom.kerLift π) (RingHom.kerLift_injective π)
  haveI : IsDomain (R ⧸ RingHom.ker π) :=
    Function.Injective.isDomain (RingHom.kerLift π) (RingHom.kerLift_injective π)
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _))

set_option backward.isDefEq.respectTransparency false in
set_option linter.checkUnivs false in
/-- **Chebotarev–Brauer–Nesbitt conjugacy from FROBENIUS TRACES ALONE** (PROVEN
2026-07-28, flt-lean-397): a continuous representation `τ` of `Gal(ℚ̄/ℚ)` on a
2-dimensional space over a finite discrete field `k` in which `2 ≠ 0`, whose
Frobenius `charFrob` LINEAR COEFFICIENTS agree with those of an *irreducible*
2-dimensional `ρbar` at all primes outside a finite set `S`, is conjugate to
`ρbar`.

This is the exact input the residual pinnings of this module carry
(`AuxDeformationDatum.charFrob_compat`, `IsAuxFibreProductClause`,
`IsAuxProLimitClause`), and `exists_conj_of_charFrob_eq_away` above — which asks
for the whole `charFrob` — is NOT reachable from it; see the section preamble for
the `p = 5`, `α = 1`, `β = 2` witness showing that the determinant really is not
determined place by place.

Route: `coeff 1` of the charpoly of a rank-two endomorphism is minus its trace
(`charpoly_eq_quadratic_of_finrank_two`), so the hypothesis is trace agreement at
the Frobenius elements; the trace-agreement locus is closed (both representations
are continuous into DISCRETE finite endomorphism spaces,
`discreteTopology_moduleTopology`) and conjugation-stable
(`charpoly_conj_mul_inv`), hence everything by Chebotarev density
(`dense_conjClasses_globalFrob`); rank-two Cayley–Hamilton
(`two_mul_det_eq_of_finrank_two`) with `2` a unit turns traces everywhere back
into determinants everywhere, hence charpolys everywhere; and the abstract
dimension-2 Brauer–Nesbitt core `exists_linearEquiv_of_charpoly_eq` produces the
intertwining isomorphism.  The ORDER matters and is the whole point: the
determinant is recovered only after density has been used, never place by place.

Both-ways audit: `h2` is load-bearing — in characteristic `2` the trace does not
determine the determinant (`tr = 0` for every element of a nonsplit torus of
`SL₂`), and the theorem is false there.  `hirr` is load-bearing for the same
reason it is in `exists_conj_of_charFrob_eq_away`: without it only the
semisimplifications agree.  No hypothesis on `ρbar`'s determinant is needed, and
adding one would be redundant.

Home note: this belongs beside its charpoly twin in
`BrauerNesbittConjugacy.lean`; it is stated here to keep the edit inside this
module's raised-level section.  Dedupe when that file is next touched. -/
theorem exists_conj_of_charFrobCoeffOne_eq_away.{uK, uW, uW'}
    {k : Type uK} [Field k] [Finite k] [TopologicalSpace k]
    [DiscreteTopology k] [IsTopologicalRing k] (h2 : (2 : k) ≠ 0)
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2)
    {ρbar : GaloisRep ℚ k W} (hirr : ρbar.IsIrreducible)
    {W' : Type uW'} [AddCommGroup W'] [Module k W'] [Module.Finite k W']
    [Module.Free k W']
    (hW' : Module.rank k W' = 2)
    (τ : GaloisRep ℚ k W')
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hc1 : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (τ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) :
    ∃ e : W' ≃ₗ[k] W, τ.conj e = ρbar := by
  classical
  have hfrW : Module.finrank k W = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)
  have hfrW' : Module.finrank k W' = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hW')
  have hc1W : ∀ f : Module.End k W,
      (LinearMap.charpoly f).coeff 1 = -(LinearMap.trace k W f) := by
    intro f
    have h := congrArg (fun P : Polynomial k => P.coeff 1)
      (charpoly_eq_quadratic_of_finrank_two hfrW f)
    simpa using h
  have hc1W' : ∀ f : Module.End k W',
      (LinearMap.charpoly f).coeff 1 = -(LinearMap.trace k W' f) := by
    intro f
    have h := congrArg (fun P : Polynomial k => P.coeff 1)
      (charpoly_eq_quadratic_of_finrank_two hfrW' f)
    simpa using h
  letI : TopologicalSpace (Module.End k W) :=
    moduleTopology k (Module.End k W)
  letI : TopologicalSpace (Module.End k W') :=
    moduleTopology k (Module.End k W')
  haveI : DiscreteTopology (Module.End k W) :=
    discreteTopology_moduleTopology _ _
  haveI : DiscreteTopology (Module.End k W') :=
    discreteTopology_moduleTopology _ _
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      ((τ g : Module.End k W'), (ρbar g : Module.End k W)) :=
    (ContinuousMonoidHom.continuous_toFun τ).prodMk
      (ContinuousMonoidHom.continuous_toFun ρbar)
  have hclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρbar g)} := by
    have hpre : {g : Field.absoluteGaloisGroup ℚ |
        LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρbar g)} =
        (fun g : Field.absoluteGaloisGroup ℚ =>
          ((τ g : Module.End k W'), (ρbar g : Module.End k W))) ⁻¹'
        {pp : Module.End k W' × Module.End k W |
          LinearMap.trace k W' pp.1 = LinearMap.trace k W pp.2} := rfl
    rw [hpre]
    exact (isClosed_discrete _).preimage hcont
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), v ∉ S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρbar g)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hval := hc1 q hq hvS
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob,
      GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    show LinearMap.trace k W' (τ _) = LinearMap.trace k W (ρbar _)
    rw [← neg_inj, ← hc1W', ← hc1W, charpoly_conj_mul_inv τ,
      charpoly_conj_mul_inv ρbar]
    exact hval
  have halltr : ∀ g : Field.absoluteGaloisGroup ℚ,
      LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρbar g) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ) S
    have huniv : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆
        {g : Field.absoluteGaloisGroup ℚ |
          LinearMap.trace k W' (τ g) = LinearMap.trace k W (ρbar g)} :=
      hdense.closure_eq ▸ hclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ g)
  have hall : ∀ g : Field.absoluteGaloisGroup ℚ,
      LinearMap.charpoly (τ g) = LinearMap.charpoly (ρbar g) := by
    intro g
    have hsq : LinearMap.trace k W' (τ g * τ g) =
        LinearMap.trace k W (ρbar g * ρbar g) := by
      rw [← map_mul, ← map_mul]
      exact halltr (g * g)
    have hdet : LinearMap.det (τ g) = LinearMap.det (ρbar g) := by
      refine mul_left_cancel₀ h2 ?_
      rw [two_mul_det_eq_of_finrank_two hfrW' (τ g),
        two_mul_det_eq_of_finrank_two hfrW (ρbar g), halltr g, hsq]
    rw [charpoly_eq_quadratic_of_finrank_two hfrW' (τ g),
      charpoly_eq_quadratic_of_finrank_two hfrW (ρbar g), halltr g, hdet]
  obtain ⟨e, he⟩ := exists_linearEquiv_of_charpoly_eq hfrW hfrW'
    ρbar.toRepresentation τ.toRepresentation hirr hall
  refine ⟨e, GaloisRep.ext fun σ => LinearMap.ext fun x => ?_⟩
  have h1 : e (τ σ (e.symm x)) = ρbar σ (e (e.symm x)) := he σ (e.symm x)
  rw [e.apply_symm_apply] at h1
  calc (τ.conj e) σ x = (e.conj (τ σ)) x := by rw [GaloisRep.conj_apply]
    _ = e (τ σ (e.symm x)) := by rw [LinearEquiv.conj_apply]; rfl
    _ = ρbar σ x := h1

set_option linter.checkUnivs false in
/-- **The split torus at a raised prime, GIVEN residual distinctness** (SORRY LEAF,
cut out 2026-07-28 by flt-lean-397 from
`raisedLevelIsSplitTorusAt_of_forall_isOpen_quotient` below, which is now an
ASSEMBLY over it).

Everything in the ambient leaf that mentions `ρbar` — `hW`, `hirr`, `hQ`, `S` and
the pinning `hπR` — is spent producing exactly ONE fact, and it is `hdist`: the
residual `charFrob` of `ρ` at `q` splits with DISTINCT roots.  This leaf is the
remainder, and it mentions `ρbar` nowhere.

# ROUTE

Let `v` be the place of `q` and `σ` the arithmetic Frobenius of `Γ ℚ_v`, so that
`M := ρ.toLocal v σ` has `charpoly = ρ.charFrob v`, whose reduction has distinct
roots by `hdist`.  `R` is `𝔪`-adically complete, so Hensel's lemma factors that
charpoly as `(X - C a) * (X - C b)` over `R` with `a - b` a UNIT (its residue is
`α - β ≠ 0`, and a non-unit of a local ring is exactly an element of `𝔪`).  By
Cayley–Hamilton `(M - a)(M - b) = 0`, so

    ε := (a - b)⁻¹ • (M - b)

is an IDEMPOTENT of `End R (Fin 2 → R)` — `(M - b)² = (a - b) * (M - b)` — with
`ε` and `1 - ε` each cutting out a free rank-one direct summand.  What remains is
that `ε` COMMUTES with the whole local action, and that is where `hlev` and
`hcomplete` enter: at each open `I` the level datum splits `ρ ⊗ (R ⧸ I)` at `q`
into `χ_I ⊕ δ_I`, in which basis the image of `M` is diagonal with residually
distinct entries, so the image of `ε` is the projection onto the `χ_I`-line and
commutes with everything; hence every entry of `ε * ρ.toLocal v g - ρ.toLocal v g * ε`
lies in `𝔪^(n+1)` for every `n`, and adic SEPARATEDNESS makes it zero — the same
separation argument written out in full in
`raisedLevelDet_of_forall_isOpen_quotient` above.  `δ` is unramified for the same
reason, one level at a time.

Note this route builds the splitting DIRECTLY over `R` and never forms an inverse
limit of level-wise decompositions: uniqueness of the idempotent is used only to
identify the level-wise splittings with the reduction of `ε`, not to construct a
compatible system.  The cofiltered-system alternative recorded on
`IsAuxProLimitClause` remains available and still needs `Finite (R ⧸ I)`, which is
not given.

# BOTH-WAYS AUDIT

`hdist` is load-bearing and is the ONLY thing the ambient arithmetic supplies: with
`α = β` the level-wise decompositions need not be compatible (the section
preamble's `k[u,v]/(u,v)²` counterexample), the idempotent is not determined by its
residue, and Hensel gives no factorization with a unit difference.  `hcomplete` is
load-bearing twice — for Hensel and for separatedness — and `hadic` is what makes
`𝔪^n` open so that `hlev` can be applied to it at all.  `hqQ` is load-bearing:
`hlev` says nothing about `q ∉ Q`.  No hypothesis on `ρbar` is used or needed, so
the circularity guard of `exists_auxDeformationDatum` is satisfied structurally
here: `hirr` is not even in scope, and a proof of this leaf CANNOT end in
`exfalso` against it. -/
theorem raisedLevelSplitTorusAt_of_charFrob_residually_distinct.{a, uK} {p : ℕ}
    (hpodd : Odd p) [Fact p.Prime] (Q : Finset ℕ)
    {k : Type uK} [Field k]
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)} (πR : R →+* k)
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I)))
    (q : ℕ) (hqQ : q ∈ Q) (hq : q.Prime)
    (hdist : ∃ α β : k, α ≠ β ∧
      (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map πR =
        (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    ∃ (e : (Fin 2 → R) ≃ₗ[R] R × R)
      (χ δ : GaloisRep
        ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) R R),
      (∀ (g : Field.absoluteGaloisGroup
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
          (v : Fin 2 → R),
        e (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat g v) =
          (χ g (e v).1, δ g (e v).2)) ∧
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker := sorry

set_option linter.checkUnivs false in
/-- **The split torus at the raised primes passes to the adic limit** (ASSEMBLY —
recut 2026-07-28 by flt-lean-397 over
`raisedLevelSplitTorusAt_of_charFrob_residually_distinct` above; was LEAF A2'-2c-v
of the decomposition of `isAuxProLimitClause` below, and the ONLY one of the five
that is not a transcription of an already-proven base-level clause).

This is the genuinely new content of the pro-limit clause, and it is where `hQ` and the
residual pinning `(πR, S, hπR)` are spent.  **All of that arithmetic is spent HERE**, and
it produces exactly one fact, the `hdist` fed to the leaf above: the residual `charFrob`
of `ρ` at `q` splits with distinct roots.

# WHAT THIS ASSEMBLY DOES

1. `πR` is LOCAL — `ker πR = 𝔪` because `k` is finite
   (`ker_eq_maximalIdeal_of_ringHom_finiteField` above) — hence continuous, `𝔪` being
   open by `hadic` and `k` discrete.  So the residual representation of `ρ` may be
   formed as `ρ.baseChange k` along `πR`.
2. `hπR` and `charFrob_baseChange` give `coeff 1` agreement between
   `(ρ.baseChange k).charFrob` and `ρbar.charFrob` away from `S`.
3. `exists_conj_of_charFrobCoeffOne_eq_away` (PROVEN above, and NEW — see the section
   preamble for why `exists_conj_of_charFrob_eq_away` is NOT usable here) turns that
   into an honest conjugacy `ρ.baseChange k ≃ ρbar`, using `hirr` and `2 ≠ 0` in `k`
   (which is `hpodd`).
4. Conjugacy plus `charFrob_conj` gives FULL `charFrob` agreement at EVERY prime — this
   is where the finite exceptional set `S` stops costing anything — and `hQ`'s
   `(X - α)(X - β)` with `α ≠ β` at `q ∈ Q` transports across it.

# STALE CLAIM CORRECTED (2026-07-28)

The previous docstring said the transport is "by `exists_conj_of_charFrob_eq_away`
(PROVEN above)".  It is not: that theorem needs the whole `charFrob`, and the pinning
carries only `coeff 1`.  See the section preamble above for the explicit `p = 5`,
`α = 1`, `β = 2`, `q ≡ 1 [MOD 5]` witness that the determinant is NOT recoverable place
by place, and for the density-first repair.  It said, too, that
`isHilbertSplitTorusAt_of_forall_isOpen_quotient` "is the model to copy": that
declaration is itself a bare `sorry`
(`HardlyRamified/HilbertModularity.lean`), so there was no model to copy — and its
pinning is the STRONGER charpoly-at-every-`g` shape, so the gap repaired here does not
even arise on the Hilbert side.  Its `ℚ`-side twin is this assembly, not the reverse.

# BOTH-WAYS AUDIT

`hQ`, `hirr` and the pinning `(πR, S, hπR)` are ALL load-bearing, and this is the only
one of the five sub-leaves for which that is true — the other four use none of them.
Without residual distinctness the level-wise decompositions need not be compatible
(the two residual characters could coincide, and then the idempotent is not determined
by its residue).  `hirr` is used only through
`exists_conj_of_charFrobCoeffOne_eq_away`, to turn trace agreement away from `S` into
an honest conjugacy.  `hpodd` is now load-bearing twice: through `hlev`'s type, and as
the source of `2 ≠ 0` in `k` that step 3 needs.

CIRCULARITY GUARD (inherited from `exists_auxDeformationDatum`): a proof ending in
`exfalso` against `hirr` is the circular discharge and must be rejected.  This assembly
uses `hirr` only positively, through Brauer–Nesbitt. -/
theorem raisedLevelIsSplitTorusAt_of_forall_isOpen_quotient.{a, uK, uW} {p : ℕ}
    (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (n : ℕ) (Q : Finset ℕ) (hQ : IsTaylorWilesPrimeSet p ρbar n Q)
    {R : Type a} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [Algebra ℤ_[p] R] [IsNoetherianRing R]
    (hadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    {ρ : GaloisRep ℚ R (Fin 2 → R)} (πR : R →+* k)
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hπR : ∀ (q : ℕ) (hq : q.Prime),
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      πR ((ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1) =
        (ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1)
    (hlev : ∀ (I : Ideal R), IsOpen (I : Set R) → ∀ [IsLocalRing (R ⧸ I)]
      (hdimI : Module.rank (R ⧸ I) ((R ⧸ I) ⊗[R] (Fin 2 → R)) = 2),
      IsRaisedLevelHardlyRamified hpodd Q hdimI (ρ.baseChange (R ⧸ I))) :
    ∀ q ∈ Q, ∀ hq : q.Prime,
      ∃ (e : (Fin 2 → R) ≃ₗ[R] R × R)
        (χ δ : GaloisRep
          ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ) R R),
        (∀ (g : Field.absoluteGaloisGroup
            ((hq.toHeightOneSpectrumRingOfIntegersRat).adicCompletion ℚ))
            (v : Fin 2 → R),
          e (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat g v) =
            (χ g (e v).1, δ g (e v).2)) ∧
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤ δ.ker := by
  classical
  intro q hqQ hq
  -- Step 1: `πR` is local, hence continuous, so `ρ` may be reduced along it.
  have hker : RingHom.ker πR = IsLocalRing.maximalIdeal R :=
    ker_eq_maximalIdeal_of_ringHom_finiteField πR
  have hmopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
    have h := (isAdic_iff.mp hadic).1 1
    simpa using h
  have hπcont : Continuous πR := by
    apply continuous_of_continuousAt_zero πR
    unfold ContinuousAt
    rw [map_zero, nhds_discrete k, Filter.tendsto_pure]
    filter_upwards [hmopen.mem_nhds (Submodule.zero_mem _)] with x hx
    have hxk : x ∈ RingHom.ker πR := by rw [hker]; exact hx
    exact hxk
  letI : Algebra R k := πR.toAlgebra
  haveI : ContinuousSMul R k := continuousSMul_of_algebraMap R k
    (by rw [RingHom.algebraMap_toAlgebra]; exact hπcont)
  -- Step 2: `2 ≠ 0` in `k`, because `p` is odd and `k` is a `ℤ_p`-algebra.
  haveI hchar : CharP k p := charP_of_ringHom_padicInt (algebraMap ℤ_[p] k)
  have h2 : (2 : k) ≠ 0 := by
    intro h20
    have hcast : ((2 : ℕ) : k) = 0 := by exact_mod_cast h20
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).mp hcast
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
    rw [hp2] at hpodd
    exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  -- Step 3: trace-level pinning of the residual representation, then conjugacy.
  have hrk' : Module.rank k (k ⊗[R] (Fin 2 → R)) = 2 := by simp
  have hc1 : ∀ (q' : ℕ) (hq' : q'.Prime),
      hq'.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      ((ρ.baseChange k).charFrob
          hq'.toHeightOneSpectrumRingOfIntegersRat).coeff 1 =
        (ρbar.charFrob hq'.toHeightOneSpectrumRingOfIntegersRat).coeff 1 := by
    intro q' hq' hq'S
    rw [charFrob_baseChange, Polynomial.coeff_map, RingHom.algebraMap_toAlgebra]
    exact hπR q' hq' hq'S
  obtain ⟨e₀, he₀⟩ := exists_conj_of_charFrobCoeffOne_eq_away h2 hW hirr hrk'
    (ρ.baseChange k) S hc1
  -- Step 4: conjugacy upgrades the pinning to FULL `charFrob` agreement everywhere.
  have hcf : ∀ (q' : ℕ) (hq' : q'.Prime),
      (ρ.charFrob hq'.toHeightOneSpectrumRingOfIntegersRat).map πR =
        ρbar.charFrob hq'.toHeightOneSpectrumRingOfIntegersRat := by
    intro q' hq'
    have h1 := charFrob_conj hq'.toHeightOneSpectrumRingOfIntegersRat
      (ρ.baseChange k) e₀
    rw [he₀, charFrob_baseChange, RingHom.algebraMap_toAlgebra] at h1
    exact h1.symm
  -- Step 5: `hQ` gives distinct residual Frobenius eigenvalues at `q ∈ Q`.
  obtain ⟨hq', _hcong, α, β, hαβ, hfact⟩ := hQ.1 q hqQ
  have hfact' : ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
      (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β) := hfact
  exact raisedLevelSplitTorusAt_of_charFrob_residually_distinct
    hpodd Q hadic hcomplete πR hlev q hqQ hq
    ⟨α, β, hαβ, by rw [hcf q hq, hfact']⟩

set_option linter.checkUnivs false in
/-- **The RAISED-LEVEL pro-limit clause** (sorry node, LEAF A2′-2c of the
2026-07-28 clause cut).

The four base-level clauses pass to the limit as at the base level.  The new
content is the split-torus clause at `q ∈ Q`, and it is where `hQ` and the
residual pinning are spent: residual distinctness makes the decomposition at
each finite level unique once the residual eigenvalue attached to `χ` is fixed,
so the levels form a compatible system, and adic completeness assembles it into
a decomposition over `R`.  See the section preamble, and
`IsAuxProLimitClause`'s docstring for the alternative cofiltered-system route.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem isAuxProLimitClause.{a, uK, uW} {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (n : ℕ) (Q : Finset ℕ) (hQ : IsTaylorWilesPrimeSet p ρbar n Q) :
    IsAuxProLimitClause.{a, uK, uW} hpodd Q ρbar := by
  intro R _ _ _ _ _ _ hadic hcomplete ρ πR S hπR hlev
  exact
    { det := raisedLevelDet_of_forall_isOpen_quotient hpodd Q hadic hcomplete hlev
      isUnramified :=
        raisedLevelIsUnramified_of_forall_isOpen_quotient hpodd Q hadic hcomplete hlev
      isFlat := raisedLevelIsFlat_of_forall_isOpen_quotient hpodd Q hadic hcomplete hlev
      isTameAtTwo :=
        raisedLevelIsTameAtTwo_of_forall_isOpen_quotient hpodd Q hadic hcomplete hlev
      isSplitTorusAt :=
        raisedLevelIsSplitTorusAt_of_forall_isOpen_quotient hpodd hW hirr n Q hQ
          hadic hcomplete πR S hπR hlev }

set_option linter.checkUnivs false in
/-- **The RAISED-LEVEL Schlessinger machine** (sorry node, LEAF A2′-2d of the
2026-07-28 clause cut): the arithmetic-free half of
`exists_isWeaklyUniversal_auxDeformationDatum` below.

Nothing here is specific to the raised level.  The base-level `ℚ` chain of this
file — `HardlyRamifiedFiniteDeformation`,
`IsStrictlyUniversalOnFramedFiniteLifts`,
`IsWeaklyUniversalOnIdentifiedFiniteTests`, the `p`-adic tower
`exists_ringHom_quotient_padicTower_of_finiteTests`, the tangent-finiteness
upgrade `exists_weaklyUniversalOnIdentified_framed_of_finite_tangent` and the
limit passage `exists_weaklyUniversalOnIdentified_hardlyRamifiedDeformation` —
consumes `IsHardlyRamified` ONLY through the operations packaged as the clauses
above: pushforward along a quotient, conjugation, gluing along a fibre product,
finiteness at each Artinian level, and detection on the finite levels.  So the
intended discharge is that chain with `IsRaisedLevelHardlyRamified hpodd Q` in
place of `IsHardlyRamified hpodd`, plus the extra bookkeeping that the raised
gluing and pro-limit clauses also demand the residual pinning
`(π, S, charFrob_compat)`, which every object of the category carries by
definition.

**The right way to discharge it is probably to make the base-level chain
PREDICATE-GENERIC and instantiate it twice**, rather than to transcribe ~1300
lines a second time.  That refactor was not attempted at the cut because it
edits proven declarations belonging to other owners; a successor holding the
whole chain should consider it before transcribing.  The Hilbert twin
`exists_isWeaklyUniversal_hilbertAuxDeformationDatum_of_clauses` records the
same recommendation, and a single predicate-generic machine serving both sides
is the outcome worth aiming at.

**WHAT THIS LEAF MAY NOT DO.**  The base-level `ℚ` chain bottoms out in
`exists_framedStrictlyUniversal_hardlyRamified_finiteTests`, which is
discharged by `exfalso` from the odd-prime dichotomy
(`IsHardlyRamified.mod_three_reducible` at `p = 3`,
`not_isIrreducible_of_isHardlyRamified_of_five_le` at `p ≥ 5`) against an
irreducible hardly ramified `ρbar`.  That route is BANNED here: this statement
deliberately does not carry `IsHardlyRamified hpodd hW ρbar`, and deriving it
from `𝒟₀` by reduction descent is banned by the circularity guard.  A proof of
this leaf ending in `exfalso` must be rejected.  So the transcription must
follow the chain ABOVE that bottom leaf — the part that is genuine Schlessinger
machinery — and take the finite-level representability from `hglue`, `hfin` and
`hfunc` instead.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem exists_isWeaklyUniversal_auxDeformationDatum_of_clauses.{uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (Q : Finset ℕ)
    (𝒟₀ : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (hfunc : IsAuxFunctorialityClause.{uR} hpodd Q)
    (hglue : IsAuxFibreProductClause.{uR, uK, uW} hpodd Q ρbar)
    (hfin : IsAuxFiniteFramesClause.{uR} hpodd Q)
    (hlim : IsAuxProLimitClause.{uR, uK, uW} hpodd Q ρbar) :
    ∃ 𝒟 : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar,
      𝒟.IsWeaklyUniversal :=
  sorry

set_option linter.checkUnivs false in
/-- **The raised-level deformation problem is weakly representable** (ASSEMBLY
— cut 2026-07-28 into the four clause leaves above; was LEAF A2′-2 of the
2026-07-27 RING/HECKE cut): Mazur representability at raised level.

This is `exists_weaklyUniversal_hardlyRamifiedDeformation` above with the local
condition raised at `Q`, and the same Schlessinger/Ramakrishna machinery is
what proves it: the raised-level functor is pro-representable because it is
relatively representable (the local condition at `q ∈ Q` is a product of two
character-deformation problems, by the DISTINCT residual Frobenius eigenvalues
that `hQ` supplies) and has finite-dimensional tangent space over the FINITE
residue field `k`.

**THE CUT (2026-07-28).**  This is now an ASSEMBLY over the raised-level
Schlessinger machine `exists_isWeaklyUniversal_auxDeformationDatum_of_clauses`
and the clauses above, mirroring the Hilbert twin
`exists_isWeaklyUniversal_hilbertAuxDeformationDatum`'s assembly one for one.
`isAuxFunctorialityClause` is PROVEN — over the two new raised-level transfers
`isRaisedLevelHardlyRamified_baseChange_quotient` and
`isRaisedLevelHardlyRamified_conj`, themselves over the new
`isSplitTorusAt_baseChange`, all three PROVEN.  Three clause leaves and the
machine leaf remain.  `n` and `hQ` are consumed by the gluing and pro-limit
clauses, which is exactly where residual distinctness at `q ∈ Q` is needed —
see the section preamble for the `k[u,v]/(u,v)²` counterexample that forces the
residual pinning on both of them, and for why the `ℚ`-side pinning is
trace-level with a finite exceptional set (and why that costs nothing, through
`exists_conj_of_charFrob_eq_away`).

**`𝒟₀` IS A GENUINE HYPOTHESIS AND MUST NOT BE DROPPED.**  An existential over
a category is FALSE as soon as the category is EMPTY, and the raised-level
category is empty for two independent reasons — dimension (`rank_eq` forces
`finrank k W = 2`) and arithmetic (no deformation exists unless `ρbar` itself
satisfies the local conditions).  This is the FAITHFULNESS REPAIR already
recorded on the Hilbert twin
`exists_isWeaklyUniversal_hilbertAuxDeformationDatum`; restating this leaf
without `𝒟₀` would reproduce a refuted statement.  The assembly discharges
`𝒟₀` from `exists_auxDeformationDatum` above.

References: Mazur, in *Galois Groups over ℚ* (1989); Ramakrishna, Compositio
87 (1993); Darmon–Diamond–Taylor §2; Wiles ch. 3 for the local condition at
`Q`.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem exists_isWeaklyUniversal_auxDeformationDatum.{uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hirr : ρbar.IsIrreducible)
    (n : ℕ) (Q : Finset ℕ) (hQ : IsTaylorWilesPrimeSet p ρbar n Q)
    (𝒟₀ : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar) :
    ∃ 𝒟 : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar,
      𝒟.IsWeaklyUniversal :=
  exists_isWeaklyUniversal_auxDeformationDatum_of_clauses.{uK, uW, uR}
    hpodd hW hirr Q 𝒟₀
    (isAuxFunctorialityClause.{uR} hpodd Q)
    (isAuxFibreProductClause.{uR, uK, uW} hpodd hW hirr n Q hQ)
    (isAuxFiniteFramesClause.{uR} hpodd Q)
    (isAuxProLimitClause.{uR, uK, uW} hpodd hW hirr n Q hQ)

set_option linter.checkUnivs false in
/-- **The `q`-generator bound for the raised-level deformation ring** (sorry
node, LEAF A2'-3a of the 2026-07-28 cut of
`exists_auxDeformationRingPresentation` below): Greenberg-Wiles, in the one
shape the presentation needs — a SURJECTION
`Λ_𝒪 = 𝒪[[x_1, …, x_q]] ↠ R_Q`.

From such a `pres` the presented form asked by
`exists_auxDeformationRingPresentation` is one line
(`I := RingHom.ker pres`, `RingHom.quotientKerEquivOfSurjective`), which is
exactly what the PROVEN glue below does.

Mathematically this is the Greenberg-Wiles formula
`dim_k H¹_Q(ℚ, ad⁰ρbar) = #Q = q`, which holds **because the DUAL Selmer group
vanishes** — the global conjunct of `IsTaylorWilesPrimeSet` (see the INTERFACE
REPAIR section of `exists_taylorWilesAuxLevelPresentedDatum` below for why that
conjunct is load-bearing and what breaks without it).  `hQcard : Q.card = q`
ties `#Q` to the number of variables; `hq0 : q0 ≤ q` is what makes `q` at least
the Taylor-Wiles number rather than merely Cohen's `μ(𝔪_Runiv)`.

`𝒟Q` arrives WEAKLY UNIVERSAL, so `𝒟Q.R` really is `R_Q` and its tangent space
really is `H¹_Q(ℚ, ad⁰ρbar)`.  Without `h𝒟Q` the bound would be a statement
about an arbitrary carrier and no cohomological input could reach it.

# WHY `hcoeff` IS HERE — A FAITHFULNESS REPAIR (2026-07-28)

`hcoeff` says the coefficient ring is the right one: some surjection
`Λ_𝒪 ↠ Runiv` exists.  It is not decoration, and it was ABSENT from
`exists_auxDeformationRingPresentation` as that leaf was cut on 2026-07-27.

Reason.  `MvPowerSeries (Fin q) 𝒪` is local with residue field `𝒪/𝔪_𝒪`, and so
is every nonzero quotient of it.  `𝒟Q.R` is local and carries
`𝒟Q.π : 𝒟Q.R ↠ k` onto a FIELD, so `ker 𝒟Q.π` is maximal, hence is
`𝔪_{𝒟Q.R}`, hence the residue field of `𝒟Q.R` is `k`.  A surjection
`Λ_𝒪 ↠ 𝒟Q.R` therefore FORCES `𝒪/𝔪_𝒪 ≅ k`.  Nothing else in the hypothesis
package mentions `coeff` at all — it was a free `TaylorWilesCoefficients` — so
the leaf was universally quantified over coefficient rings with the wrong
residue field (take `coeff := TaylorWilesCoefficients.padicInt p`, whose
residue field is `𝔽_p`, against any `k` with more than `p` elements) and no
proof of it could exist.  Same failure mode as the `Q` and `q` defects already
recorded on the assembly: a datum chosen by a statement that cannot see the
constraint on it.

The repair costs the assembly nothing.
`exists_taylorWilesAuxLevelPresentedDatum` holds `hbot`, and
`hbot.some.toRuniv.comp hbot.some.pres` IS such a surjection
(`TaylorWilesLevelRaw.pres_surjective` composed with
`TaylorWilesLevelRaw.toRuniv_surjective`).  `hbot` was simply never threaded
into the RING half of the cut.  A prover may read `hcoeff` as "`𝒪 = W(k)`, as
in the classical statement".

*The refuting check for this section*, so the next reader need not redo it:
`grep -n 'structure TaylorWilesCoefficients' -A 30 Fermat/FLT/Modularity/PatchingCore.lean`
— no field of that structure ties `𝒪` to any residue field beyond
`finite_residueField`, so nothing else can supply this.

References: Wiles, Ann. of Math. 141 (1995), Prop. 1.6 and ch. 3;
Darmon-Diamond-Taylor Thm. 2.49 and §3; Greenberg, *Iwasawa theory and p-adic
deformations*; Mazur, in *Galois Groups over ℚ* (1989).

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above —
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` and
`Slop.OddRep.isIrreducible_iff_forall` against `hirr`, any reduction-descent
lemma producing `IsHardlyRamified hpodd hW ρbar`, and `Family.lean` with
everything downstream of it, are BANNED as inputs.  A proof ending in `exfalso`
is the circular discharge again and must be rejected. -/
theorem exists_auxDeformationPresSurjection.{uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
    (hirr : ρbar.IsIrreducible)
    {Runiv : Type uR} [CommRing Runiv] [IsLocalRing Runiv]
    {πuniv : Runiv →+* k} (hπuniv : Function.Surjective πuniv)
    (q0 q : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (hcoeff : ∃ c : MvPowerSeries (Fin q) coeff.carrier →+* Runiv,
      Function.Surjective c)
    (n : ℕ) (Q : Finset ℕ) (hQcard : Q.card = q)
    (hQ : IsTaylorWilesPrimeSet p ρbar (n + 1) Q)
    (𝒟Q : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (h𝒟Q : 𝒟Q.IsWeaklyUniversal) :
    ∃ pres : MvPowerSeries (Fin q) coeff.carrier →+* 𝒟Q.R,
      Function.Surjective pres :=
  sorry

set_option linter.checkUnivs false in
/-- **The diamond operators and the control map on `R_Q`** (sorry node, LEAF
A2'-3b of the 2026-07-28 cut of `exists_auxDeformationRingPresentation`
below): local class field theory at the Taylor-Wiles primes, together with the
control identification `R_Q ⧸ 𝔫 ≅ R_univ`.

1. **`diamond`**, from `Λ = ℤ_p[[S_1, …, S_q]]`.  The split-torus clause of
   `IsRaisedLevelHardlyRamified` gives at each `q_i ∈ Q` a character `χ_i`
   whose restriction to `I_{q_i}` factors through the tame quotient
   `(ℤ/q_i)ˣ`, whose `p`-Sylow is `Δ_{q_i} ≅ ℤ/p^{e_i}` with
   `e_i = v_p(q_i − 1) ≥ n`.  `taylorWilesLevelIdeal p (fun _ => n) ≤
   RingHom.ker diamond` says `diamond` factors through `Λ ⧸ 𝔟_{(n)}`, i.e.
   that the diamonds have the stated orders; that `e_i ≥ n` is precisely the
   congruence clause of `hQ` (see the EXPONENT AUDIT of the assembly for why
   the constant exponent vector is the standard formulation and not a
   weakening).
2. **`toRuniv`**, the control map: surjective with
   `ker toRuniv = 𝔫 · R_Q` for `𝔫 = taylorWilesAug p q`.  Killing the diamonds
   is killing the level raising, so `R_Q ⧸ 𝔫 ≅ R_∅ = R_univ`.

Two weaknesses of `isSplitTorusAt` that a prover must DERIVE, not read off
(recorded at the predicate and repeated here because this is the leaf that
needs them): the clause does not pin `χ`/`δ` to reduce to the two residual
eigenvalues in a prescribed order, and does not pin `χ|_{I_q}` to factor
through the `p`-Sylow `Δ_q`.  Both follow from `𝒟Q.charFrob_compat` together
with the distinct-eigenvalue clause of `hQ`; item 1 is where they are needed.

# WHY THE DIAMOND AND THE CONTROL MAP MAY NOT BE SPLIT APART

Both directions of the vacuity check, run before this cut was taken, because a
future dispatcher will otherwise propose exactly the split that was ruled out:

* **`diamond` alone is JUNK-SATISFIABLE.**  Take
  `diamond := (algebraMap ℤ_[p] 𝒟Q.R).comp (MvPowerSeries.constantCoeff …)`,
  the map killing every variable `S_i`.  Then
  `taylorWilesAug p q ≤ RingHom.ker diamond`, hence
  `taylorWilesLevelIdeal p (fun _ => n) ≤ RingHom.ker diamond` by
  `taylorWilesLevelIdeal_le_aug` — so the level clause carries no arithmetic on
  its own.  This is the same junk map that the CUT-SAFETY counterexample of
  `exists_auxHeckeModuleData` below is built from.
* **`toRuniv` alone is NOT junk-satisfiable** but is also not the theorem: a
  surjection `R_Q ↠ Runiv` with no kernel clause says only that `Runiv` is a
  quotient of `R_Q`.

What makes the pair non-vacuous is `ker toRuniv = (taylorWilesAug p q).map
diamond`, which ties the two: with the junk diamond above the right-hand side
is `⊥`, so the clause would demand `toRuniv` INJECTIVE, i.e. `R_Q ≅ R_univ` —
"the level was never raised".  So the two clauses must stay in one leaf, and
that is a proof rather than a preference.

# WHAT PINS `Runiv` AS THE `Q = ∅` RING — READ THIS BEFORE ATTEMPTING CLAUSE 2

Clause 2 is only the control theorem if `Runiv` is the raised-level universal
ring at the EMPTY prime set.  The Hilbert twin
`exists_hilbertAuxDeformationRingPresentation` gets that as an explicit
hypothesis `h𝒟e : 𝒟.toAuxEmpty.IsWeaklyUniversal`.  Here it arrives instead as
`hfact : IsWeaklyUniversalDeformation`, which is weak universality over the
FINITE test category (`HardlyRamifiedFiniteDeformation`), not over
`AuxDeformationDatum ∅`.  The two are the same ring classically and are not the
same statement here, and no bridge between them exists in this file.

**The obstruction is sharper than that, and it is UPSTREAM.**  The natural
route to `toRuniv` does not go through `hfact` at all: `h𝒟Q` says `𝒟Q` is
weakly universal in `AuxDeformationDatum hpodd Q ρbar`, so it yields a
classifying map `𝒟Q.R →+* 𝒟'.R` for ANY level-`Q` datum `𝒟'` — and
`exists_auxDeformationDatum` above proves exactly that such a datum exists,
with `ρuniv` over `Runiv` as its witness ("`ρuniv` ITSELF is the witness", its
own docstring).  But its CONCLUSION is
`Nonempty (AuxDeformationDatum hpodd Q ρbar)`, which throws the carrier away:
the datum it hands back is not known to have `R = Runiv`, `ρ = ρuniv`,
`π = πuniv`.  That is a witness-forgetting existential, and the information it
discards is precisely what clause 2 needs.

So the repair belongs to `exists_auxDeformationDatum` (a different owner as of
2026-07-28), whose own proof already knows the answer: strengthen its
conclusion to name the carrier, e.g.

    ∃ 𝒟 : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar, ∃ e : 𝒟.R ≃+* Runiv,
      e.toRingHom.comp (algebraMap ℤ_[p] 𝒟.R) = algebraMap ℤ_[p] Runiv ∧
      πuniv.comp e.toRingHom = 𝒟.π

after which clause 2's surjection is `h𝒟Q` applied to that datum, composed with
`e`, and only its SURJECTIVITY and the kernel identity remain as mathematics.
The alternative recorded on `exists_auxDeformationRingPresentation` — adding
`(𝒟univ : AuxDeformationDatum hpodd ∅ ρbar)` with `𝒟univ.IsWeaklyUniversal` —
is a second, independent new leaf; the strengthening above is not, because it
is already proved by the material `exists_auxDeformationDatum` contains.

**A prover who finds clause 2 unreachable has found this reason, not a gap in
the mathematics.**  Report it; do not paper over it, and do not restate the
clause to make it provable.

References: Wiles, Ann. of Math. 141 (1995), ch. 3; Taylor-Wiles, ibid. §2;
Darmon-Diamond-Taylor §2.49 and §5.3; Fujiwara §3; Kisin, Ann. of Math. 170
(2009), §3.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above; in particular a
proof ending in `exfalso` against `hirr` must be rejected. -/
theorem exists_auxDeformationDiamondControl.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q : ℕ) (n : ℕ) (Q : Finset ℕ) (hQcard : Q.card = q)
    (hQ : IsTaylorWilesPrimeSet p ρbar (n + 1) Q)
    (𝒟Q : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (h𝒟Q : 𝒟Q.IsWeaklyUniversal) :
    ∃ (diamond : MvPowerSeries (Fin q) ℤ_[p] →+* 𝒟Q.R)
      (toRuniv : 𝒟Q.R →+* Runiv),
      Function.Surjective toRuniv ∧
      RingHom.ker toRuniv = (taylorWilesAug p q).map diamond ∧
      taylorWilesLevelIdeal p (fun _ : Fin q => n) ≤ RingHom.ker diamond :=
  sorry

set_option linter.checkUnivs false in
/-- **The auxiliary deformation ring in PRESENTED form** (**PROVEN GLUE since
2026-07-28** over the two sub-leaves above; formerly LEAF A2′-3 — the RING half
of the 2026-07-27 RING/HECKE cut of
`exists_taylorWilesAuxLevelPresentedDatum` below).

**NO ARITHMETIC HAPPENS HERE ANY MORE.**  The two steps are: obtain the
Greenberg-Wiles surjection `pres : Λ_𝒪 ↠ 𝒟Q.R`
(`exists_auxDeformationPresSurjection`) and the diamonds with the control map
on `𝒟Q.R` itself (`exists_auxDeformationDiamondControl`); then TRANSPORT the
latter two along `I := RingHom.ker pres` and
`RingHom.quotientKerEquivOfSurjective`, which is pure `Ideal` bookkeeping
(`RingHom.comap_ker`, `Ideal.map_map`, `Ideal.map_symm`,
`RingHom.ker_coe_equiv`) and is what the proof below does.

The cut is along the axis the two halves genuinely differ on: clause 1 is
GLOBAL Galois cohomology (Greenberg-Wiles for the Selmer group of `ad⁰ρbar`)
and clauses 2-3 are LOCAL class field theory at `Q` plus the control theorem.
Clauses 2 and 3 may NOT be split from each other — see the both-directions
vacuity check on `exists_auxDeformationDiamondControl` above, which exhibits
the junk `diamond` that satisfies the level clause alone.

Given the weakly universal raised-level datum `𝒟Q` — so `𝒟Q.R` IS `R_Q`, not a
carrier that happens to satisfy some equations — the three pieces are:

1. **the presentation.**  The conclusion asks for an ideal `I` of
   `Λ_𝒪 = 𝒪[[x_1, …, x_q]]` TOGETHER WITH a ring isomorphism
   `Λ_𝒪 ⧸ I ≃+* 𝒟Q.R`.  That is the `q`-generator bound in the shape the
   assembly consumes, and it is exactly as strong as "there is a surjection
   `Λ_𝒪 ↠ R_Q`": from such a `pres` take `I := RingHom.ker pres` and the
   isomorphism is `RingHom.quotientKerEquivOfSurjective`, one line.  It is
   asked in the presented shape only so that the assembly needs no transport.
   Mathematically it is the Greenberg–Wiles formula:
   `dim_k H¹_Q(ℚ, ad⁰ρbar) = #Q = q` **because the DUAL Selmer group vanishes**,
   which is the global conjunct of `IsTaylorWilesPrimeSet` (see the INTERFACE
   REPAIR section of the assembly for why that conjunct is load-bearing and
   what breaks without it).  `hQcard : Q.card = q` is what ties `#Q` to the
   number of variables, and `hq0 : q0 ≤ q` is what makes `q` at least the
   Taylor–Wiles number rather than merely Cohen's `μ(𝔪_Runiv)`;
2. **`diamond`**, from `Λ = ℤ_p[[S_1, …, S_q]]`.  This is local class field
   theory at the primes of `Q`: the split-torus clause of
   `IsRaisedLevelHardlyRamified` gives at each `q_i ∈ Q` a character `χ_i`
   whose restriction to `I_{q_i}` factors through the tame quotient
   `(ℤ/q_i)ˣ`, whose `p`-Sylow is `Δ_{q_i} ≅ ℤ/p^{e_i}` with
   `e_i = v_p(q_i − 1) ≥ n`.  The clause
   `taylorWilesLevelIdeal p (fun _ => n) ≤ RingHom.ker diamond` says `diamond`
   factors through `Λ ⧸ 𝔟_{(n)}`, i.e. that the diamonds have the stated
   orders; that `e_i ≥ n` — hence that the constant exponent vector `n` is
   admissible — is precisely the congruence clause of `hQ` (see the EXPONENT
   AUDIT of the assembly for why the constant vector is the standard
   formulation and not a weakening);
3. **`toRuniv`**, the control map: surjective with `ker toRuniv = 𝔫 · R_Q` for
   the augmentation ideal `𝔫 = taylorWilesAug p q`.  Killing the diamonds is
   killing the level raising, so `R_Q ⧸ 𝔫 ≅ R_∅ = R_univ`.

**FAITHFULNESS REPAIR (2026-07-28) — `hcoeff` WAS MISSING AND THE LEAF WAS
UNPROVABLE WITHOUT IT.**  Clause 1's isomorphism `Λ_𝒪 ⧸ I ≃+* 𝒟Q.R` forces the
residue field of `coeff.carrier` to be `k` (both sides are local rings; a
nonzero quotient of `𝒪[[x_1, …, x_q]]` has residue field `𝒪/𝔪_𝒪`, and
`𝒟Q.π : 𝒟Q.R ↠ k` onto a field makes `k` the residue field of `𝒟Q.R`).  Until
2026-07-28 nothing in the hypothesis package mentioned `coeff` at all, so the
statement was universally quantified over coefficient rings with the wrong
residue field — `coeff := TaylorWilesCoefficients.padicInt p` against any `k`
with more than `p` elements — and no proof could exist.  The repair is the new
hypothesis

    hcoeff : ∃ c : MvPowerSeries (Fin q) coeff.carrier →+* Runiv,
      Function.Surjective c

which the assembly below discharges from `hbot` in one line
(`hbot.some.toRuniv.comp hbot.some.pres`); `hbot` was simply never threaded
into the RING half of the cut.  Full argument on
`exists_auxDeformationPresSurjection` above, which is where it is consumed.

**WHAT PINS `Runiv` AS THE `Q = ∅` RING, AND THE AVAILABLE STRENGTHENING.**
Clause 3 is only the control theorem if `Runiv` is the raised-level universal
ring at the EMPTY prime set.  The Hilbert twin
`exists_hilbertAuxDeformationRingPresentation` gets that as an explicit
hypothesis `h𝒟e : 𝒟.toAuxEmpty.IsWeaklyUniversal`.  Here it arrives instead as
`hfact : IsWeaklyUniversalDeformation`, which is weak universality over the
FINITE test category (`HardlyRamifiedFiniteDeformation`), not over
`AuxDeformationDatum ∅`.  The two are the same ring classically but are not the
same statement here, and no bridge between them exists in this file.

**So the available strengthening, stated rather than left to be rediscovered:**
add `(𝒟univ : AuxDeformationDatum.{uR, uK, uW} hpodd ∅ ρbar)` whose `R` is
`Runiv` (constructible from `hρuniv` through
`isRaisedLevelHardlyRamified_empty_iff`) together with
`𝒟univ.IsWeaklyUniversal`, and thread it from the assembly.  The second half is
NOT derivable from `hfact` and would itself become a new leaf, which is why it
is recorded here rather than done: it is a decision about the interface, not
about this proof.  A prover who finds clause 3 unreachable without it has found
the reason, not a gap in the mathematics.

**A CHEAPER REPAIR OF THE SAME OBSTRUCTION, FOUND 2026-07-28** and written out
in full on `exists_auxDeformationDiamondControl` above, which now owns clause
3: the classifying map `𝒟Q.R →+* Runiv` is available from `h𝒟Q` alone as soon
as some level-`Q` datum is known to have carrier `Runiv` — and
`exists_auxDeformationDatum` above PROVES exactly that, with `ρuniv` as its
witness, but returns `Nonempty (AuxDeformationDatum hpodd Q ρbar)` and so
DISCARDS the carrier.  Strengthening that leaf's conclusion to name `Runiv`
costs its prover nothing (its proof already knows it) and is not a new leaf,
unlike the `𝒟univ` route above.  See the sub-leaf's docstring for the exact
strengthened statement.

References: Wiles, Ann. of Math. 141 (1995), ch. 3; Taylor–Wiles, ibid. §2;
Darmon–Diamond–Taylor §2.49 and §5.3; Fujiwara §3; Kisin, Ann. of Math. 170
(2009), §3.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above; in particular a
proof ending in `exfalso` against `hirr` must be rejected. -/
theorem exists_auxDeformationRingPresentation.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 q : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (hcoeff : ∃ c : MvPowerSeries (Fin q) coeff.carrier →+* Runiv,
      Function.Surjective c)
    (n : ℕ) (Q : Finset ℕ) (hQcard : Q.card = q)
    (hQ : IsTaylorWilesPrimeSet p ρbar (n + 1) Q)
    (𝒟Q : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (h𝒟Q : 𝒟Q.IsWeaklyUniversal) :
    ∃ (I : Ideal (MvPowerSeries (Fin q) coeff.carrier))
      (_ : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) ≃+* 𝒟Q.R)
      (diamond : MvPowerSeries (Fin q) ℤ_[p] →+*
        (MvPowerSeries (Fin q) coeff.carrier ⧸ I))
      (toRuniv : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) →+* Runiv),
      Function.Surjective toRuniv ∧
      RingHom.ker toRuniv = (taylorWilesAug p q).map diamond ∧
      taylorWilesLevelIdeal p (fun _ : Fin q => n) ≤ RingHom.ker diamond := by
  -- LEAF A2′-3a (Greenberg–Wiles): the `q`-generator surjection onto `R_Q` …
  obtain ⟨pres, hpres⟩ :=
    exists_auxDeformationPresSurjection.{uK, uW, uR} hpodd hW hres hirr hπuniv
      q0 q hq0 coeff hcoeff n Q hQcard hQ 𝒟Q h𝒟Q
  -- LEAF A2′-3b (local CFT + control): the diamonds and `R_Q ↠ R_univ` …
  obtain ⟨diamond, toRuniv, htoRuniv, hker, hbn⟩ :=
    exists_auxDeformationDiamondControl.{s, t, uK, uW, uR} hpodd hW hres hirr
      hadic hcomplete hranku hρuniv hπuniv hunivred hfact q n Q hQcard hQ 𝒟Q h𝒟Q
  -- … and transport the latter two onto the presented carrier `Λ_𝒪 ⧸ ker pres`.
  refine ⟨RingHom.ker pres, pres.quotientKerEquivOfSurjective hpres,
    (pres.quotientKerEquivOfSurjective hpres).symm.toRingHom.comp diamond,
    toRuniv.comp (pres.quotientKerEquivOfSurjective hpres).toRingHom, ?_, ?_,
    ?_⟩
  · exact htoRuniv.comp (pres.quotientKerEquivOfSurjective hpres).surjective
  · have hbridge : ∀ J : Ideal 𝒟Q.R,
        Ideal.map (pres.quotientKerEquivOfSurjective hpres).symm.toRingHom J =
          Ideal.map (pres.quotientKerEquivOfSurjective hpres).symm J :=
      fun _ => rfl
    rw [← RingHom.comap_ker, hker, ← Ideal.map_map, hbridge, Ideal.map_symm]
    rfl
  · have hk : RingHom.ker
        ((pres.quotientKerEquivOfSurjective hpres).symm.toRingHom.comp
          diamond) = RingHom.ker diamond := by
      rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe,
        RingHom.ker_coe_equiv, RingHom.ker]
    rw [hk]
    exact hbn

set_option linter.checkUnivs false in
/-- **The bottom Hecke module IS the augmentation quotient of the level-`n`
coordinate model** (sorry node, LEAF A2'-4a of the 2026-07-28 cut of
`exists_auxHeckeModuleData` below): the ROUTE NOTE of
`exists_taylorWilesAuxLevelPresentedDatum` below, turned from prose into a
statement a prover can be dispatched at.

Both sides are `ℤ_p^d`, and the argument is pure module algebra over what is
already PROVEN — no automorphic input, no Galois input, nothing about `ρbar`.
Writing `L := hbot.some` and `𝔫 := taylorWilesAug p q`:

* `L.projM_eq_zero` gives `ker L.projM ⊆ 𝔫 • ⊤`;
* the reverse inclusion is forced: for `x ∈ 𝔫` and any `m`,
  `L.projM (x • m) = L.projM (L.diamond x • m) = ψ (L.toRuniv (L.diamond x))
  • L.projM m` by `L.diamond_smul` and `L.projM_smul`, and
  `L.diamond x ∈ (taylorWilesAug p q).map L.diamond = RingHom.ker L.toRuniv` by
  `L.ker_toRuniv`, so the scalar is `ψ 0 = 0`;
* hence `ker L.projM = 𝔫 • ⊤` exactly, and with `L.projM_surjective`,
  `M₀ ≅ L.M ⧸ 𝔫 · L.M`;
* `L.coordM` identifies `L.M ≃ₗ[Λ] (Λ ⧸ L.bIdeal)^d` and `L.bIdeal_le_aug`
  gives `L.bIdeal ≤ 𝔫`, so `L.M ⧸ 𝔫 · L.M ≅ (Λ ⧸ 𝔫)^d`;
* the level-`n` coordinate model has the SAME `𝔫`-quotient, by
  `taylorWilesLevelIdeal_le_aug` (`𝔟_{(n)} ≤ 𝔫`, PROVEN unconditionally):
  `(Λ ⧸ 𝔟_{(n)})^d ⧸ 𝔫 · (…) ≅ (Λ ⧸ 𝔫)^d`.

Note the level-`0` ideal `L.bIdeal` is NOT assumed to be
`taylorWilesLevelIdeal p (fun _ => 0)` — `TaylorWilesLevelRaw` carries an
abstract `bIdeal` with the two bounds — which is exactly why the third bullet
uses only `bIdeal_le_aug`.  `hM0` is not needed for the isomorphism itself and
is carried because every consumer has it and because a prover may want
`Nontrivial` while transporting.

Only additive structure is asked for, because that is all the consumer uses:
the `T`-action on `M₀` is compared with the ring action in the SEMILINEARITY
clause of `exists_auxHeckeCoordModuleData` below, which is the genuinely
automorphic half and is deliberately not part of this statement.  Making this
leaf `≃ₗ` over anything would drag the intertwining back into it and undo the
cut.

*The refuting check*: if `taylorWilesLevelIdeal_le_aug` were ever removed or
weakened, the last bullet fails and this leaf becomes false; that lemma is in
`Modularity/PatchingCore.lean` and is proven unconditionally.

References: none needed — this is `Submodule`/`LinearEquiv` bookkeeping.  The
substance it replaces is recorded at
`exists_taylorWilesAuxLevelPresentedDatum`'s ROUTE NOTE, which called it "a
clean, self-contained next step" that "consumes nothing that is not already
proven". -/
theorem nonempty_augQuotEquiv_of_taylorWilesBottom.{s, uR}
    {p : ℕ} [Fact p.Prime]
    {Runiv : Type uR} [CommRing Runiv]
    {T : Type s} [CommRing T] {ψ : Runiv →+* T} {q d : ℕ}
    {coeff : TaylorWilesCoefficients}
    {M0 : Type} [AddCommGroup M0] [Module T M0] (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (n : ℕ) :
    Nonempty ((taylorWilesCoordModel p q d n ⧸
        (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) ≃+ M0) :=
  sorry

set_option linter.checkUnivs false in
/-- **The auxiliary Hecke module: the `R_Q`-action on the coordinate model and
its semilinear comparison with the bottom** (sorry node, LEAF A2'-4b of the
2026-07-28 cut of `exists_auxHeckeModuleData` below — the AUTOMORPHIC content,
and all of it).

This is `exists_auxHeckeModuleData` with the two clauses that are not
arithmetic removed.  Its conclusion asks for

1. the `Λ_𝒪 ⧸ I = R_Q`-module structure on `taylorWilesCoordModel p q d n =
   (Λ ⧸ 𝔟_{(n)})^d`, extending the canonical `Λ`-action through `diamond` —
   **Diamond's freeness theorem** (Invent. Math. 128 (1997), Thm. 2.1) in
   coordinate form.  `hbn` is what makes the `Λ`-action factor through
   `Λ ⧸ 𝔟_{(n)}`, so the clause is not vacuous;
2. an additive identification `θ` of the augmentation quotient with `M₀` that
   is SEMILINEAR over `ψ ∘ toRuniv` — **Ihara's lemma / the level-raising
   comparison with the bottom level**.

Everything else that `exists_auxHeckeModuleData` asks for is derived from these
two, by the PROVEN glue below: `projM := θ ∘ (quotient map)`, whose
surjectivity is `θ.surjective.comp Submodule.mkQ_surjective` and whose control
clause `projM m = 0 → m ∈ 𝔫 · ⊤` is injectivity of `θ` followed by
`Submodule.Quotient.mk_eq_zero`.  The two forms are EQUIVALENT, not merely
comparable: in the other direction, clause 1 plus the intertwining force
`ker projM = 𝔫 · ⊤` exactly (for `a ∈ 𝔫`,
`projM (a • m) = ψ (toRuniv (diamond a)) • projM m = 0` since
`diamond a ∈ (taylorWilesAug p q).map diamond = ker toRuniv`), so a surjective
`projM` with that kernel IS such a `θ`.  Nothing is strengthened and nothing is
weakened; the reshaping just moves two clauses out of the arithmetic.

`hθ` hands the prover the ADDITIVE identification for free — it is
`nonempty_augQuotEquiv_of_taylorWilesBottom` above, pure module algebra over
already-proven material — so that the only thing left to construct is the
SEMILINEARITY.  That is the honest statement of what is missing: `M₀` is pinned
twice over (by `hbot` and by `hM0T`; see the ROUTE NOTE of
`exists_taylorWilesAuxLevelPresentedDatum` below), and the genuine content of
the comparison was never the identification of `M₀` but the intertwining.

# CUT-SAFETY: WHY `𝒟Q`, `h𝒟Q` AND `φ` ARE STILL HYPOTHESES

Inherited verbatim from `exists_auxHeckeModuleData` below, and it is what keeps
this leaf from being the refutable one: the naive split of the parent node —
hand the module leaf only `(I, diamond, toRuniv)` with the structural clauses —
plants a FALSE leaf, because `diamond` may then be the junk map killing every
variable (see the explicit counterexample below, and the both-directions
vacuity check on `exists_auxDeformationDiamondControl` above).  The ring must
arrive as THE weakly universal raised-level deformation ring.

# WHY CLAUSES 1 AND 2 MAY NOT BE SPLIT FROM EACH OTHER

Clause 2 mentions the module structure of clause 1, so a split would have to
quantify clause 2 over module structures satisfying only the `Λ`-compatibility
of clause 1.  That is not enough to pin the action: `R_Q` is not generated by
`diamond`'s image over `ℤ_p` in general — the coefficient ring `𝒪` and the
trace generators are outside it — so a junk extension of the `Λ`-action to
`R_Q` is not excluded by clause 1, and for such an extension no semilinear `θ`
exists.  This is the same shape as the parent's CUT-SAFETY counterexample, one
level down, and it is why the automorphic content stays in one leaf.

The reduction that WOULD split them is the one the parent's "WHAT IS STILL
MISSING" section names and declines: state the `ℚ` analogue of
`HilbertAuxHeckeAlgebra` — a raised-level Hecke algebra CARRYING its module —
and derive the `R_Q`-action from weak universality, as
`exists_module_of_hilbertAuxHeckeAlgebra` does on the Hilbert side.  That
relocates the automorphic burden onto a named sibling rather than removing it,
and the Hilbert twin's own FORMAL-CONTENT AUDIT records that the existence leaf
for that structure was discharged **without any level raising happening**.  The
decision not to take it is deliberate and is restated here so that it is not
mistaken for an oversight.

References: Diamond, Invent. Math. 128 (1997), Thm. 2.1; Taylor-Wiles, Ann. of
Math. 141 (1995), §2; Wiles, ibid. ch. 3; Darmon-Diamond-Taylor §3 (Ihara's
lemma and the level-raising comparison); Ribet, Invent. Math. 100 (1990).

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem exists_auxHeckeCoordModuleData.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 q d : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (M0 : Type) [AddCommGroup M0] [Module T M0]
    (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))
    (n : ℕ) (Q : Finset ℕ) (hQcard : Q.card = q)
    (hQ : IsTaylorWilesPrimeSet p ρbar (n + 1) Q)
    (𝒟Q : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (h𝒟Q : 𝒟Q.IsWeaklyUniversal)
    (I : Ideal (MvPowerSeries (Fin q) coeff.carrier))
    (φ : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) ≃+* 𝒟Q.R)
    (diamond : MvPowerSeries (Fin q) ℤ_[p] →+*
      (MvPowerSeries (Fin q) coeff.carrier ⧸ I))
    (toRuniv : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) →+* Runiv)
    (htoRuniv : Function.Surjective toRuniv)
    (hker : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond)
    (hbn : taylorWilesLevelIdeal p (fun _ : Fin q => n) ≤ RingHom.ker diamond)
    (hθ : Nonempty ((taylorWilesCoordModel p q d n ⧸
        (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) ≃+ M0)) :
    ∃ (_ : Module (MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (taylorWilesCoordModel p q d n))
      (θ : (taylorWilesCoordModel p q d n ⧸
        (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) ≃+ M0),
      (∀ (x : MvPowerSeries (Fin q) ℤ_[p])
        (m : taylorWilesCoordModel p q d n), x • m = diamond x • m) ∧
      (∀ (x : MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (m : taylorWilesCoordModel p q d n),
        θ (Submodule.Quotient.mk (x • m)) =
          ψ (toRuniv x) • θ (Submodule.Quotient.mk m)) :=
  sorry

set_option linter.checkUnivs false in
/-- **The auxiliary Hecke module on the coordinate model, with its bottom
control** (**PROVEN GLUE since 2026-07-28** over the two sub-leaves above;
formerly LEAF A2′-4 — the HECKE half of the 2026-07-27
RING/HECKE cut of `exists_taylorWilesAuxLevelPresentedDatum` below).

**NO ARITHMETIC HAPPENS HERE ANY MORE.**  The two steps are: identify `M₀`
with the augmentation quotient of the coordinate model
(`nonempty_augQuotEquiv_of_taylorWilesBottom` above — pure module algebra over
already-proven material, and the ROUTE NOTE of
`exists_taylorWilesAuxLevelPresentedDatum` below turned into a statement); then
obtain the `R_Q`-action together with the SEMILINEAR comparison
(`exists_auxHeckeCoordModuleData` above — Diamond freeness and Ihara, the whole
automorphic content).  `projM` is then `θ` after the quotient map, and its
surjectivity and control clauses are surjectivity and injectivity of that
composite.  The two forms are equivalent — see the sub-leaf's docstring for the
converse direction, which uses only the `Λ`-compatibility clause and `hker`.

Everything about the RING has already happened: `𝒟Q` is the weakly universal
raised-level deformation datum, `φ` records that the presented ring `Λ_𝒪 ⧸ I`
IS `𝒟Q.R`, and `diamond`/`toRuniv` with their three clauses are the RING leaf's
output.  What is left — and is now owned by the two sub-leaves above — is the
automorphic side:

1. **Diamond's freeness theorem** (Invent. Math. 128 (1997), Thm. 2.1) in
   coordinate form.  The auxiliary Hecke module `M_Q` — classically
   `H¹(X_1(N·∏Q), ℤ_p)_𝔪` — is finite free of the LEVEL-INDEPENDENT rank `d`
   over `ℤ_p[Δ_Q] = Λ ⧸ 𝔟_{(n)}`.  The conclusion asks for the module STRUCTURE
   on `taylorWilesCoordModel p q d n = (Λ ⧸ 𝔟_{(n)})^d` itself rather than for
   a carrier plus a coordinate equivalence, so the freeness certificate is
   discharged by producing the action on the coordinates: the `Λ`-action is the
   canonical one and `hbn` is what makes it factor through `Λ ⧸ 𝔟_{(n)}`, so
   the statement is not vacuous;
2. **the Ihara / level-raising comparison with the bottom level** — `projM`
   onto the level-`0` module `M₀` handed in by `hbot`, surjective, killed
   exactly on `𝔫 · M_Q`, and intertwining the `R_Q`-action with the `T`-action
   through `ψ ∘ toRuniv`.

# CUT-SAFETY: WHY `𝒟Q` AND `φ` ARE HYPOTHESES AND NOT AN ABSTRACT RING

The naive RING/HECKE split of this node — hand the module leaf only
`(I, diamond, toRuniv)` with the structural clauses — **plants a FALSE leaf**,
and here is the explicit counterexample, so that nobody has to redo the survey.

Take `pres : Λ_𝒪 ↠ Runiv` the Cohen presentation supplied by
`exists_taylorWilesCoefficientsPresentation` above, `I := RingHom.ker pres`,
and let `diamond : Λ → Λ_𝒪 ⧸ I` be the composite `Λ ↠ ℤ_p → 𝒪 → Λ_𝒪 ⧸ I` that
kills every variable `S_i`.  Then `taylorWilesAug p q` maps to `0`, so
`ker toRuniv = 0` with `toRuniv` the isomorphism `Λ_𝒪 ⧸ I ≃ Runiv`, which is
surjective; and each generator `(1 + S_i)^{p^n} − 1` of
`taylorWilesLevelIdeal p (fun _ => n)` maps to `1^{p^n} − 1 = 0`, so `hbn`
holds too.  **Every structural clause is satisfied.**  But the demanded module
structure on `(Λ ⧸ 𝔟_{(n)})^d` would force
`S_i • m = diamond (S_i) • m = 0` for every `m`, while `S_i` acts on
`Λ ⧸ 𝔟_{(n)} = ℤ_p[(ℤ/p^n)^q]` as `[γ_i] − 1 ≠ 0` for `n ≥ 1`.  So the naive
module leaf is refutable, not merely hard.

`𝒟Q` together with `h𝒟Q` and `φ` is exactly what excludes this: the ring is not
a carrier satisfying four equations, it is THE weakly universal raised-level
deformation ring, for which the auxiliary Hecke module genuinely exists.  This
is the same repair the CUT AUDIT of `exists_hilbertTaylorWilesLevels` asked for
and that `exists_hilbertAuxHeckeModuleData` took on the Hilbert side.

# `M0` IS ALREADY PINNED — TWICE — SO THE CONTENT IS THE INTERTWINING

Not obvious from the statement, and it removes a whole degree of freedom.
Writing `L := hbot.some`:

* `L.projM_eq_zero` gives `ker L.projM ⊆ 𝔫 • ⊤`;
* the reverse inclusion is forced by `L.diamond_smul`, `L.projM_smul` and
  `L.ker_toRuniv`, so `ker L.projM = 𝔫 • ⊤` exactly;
* hence with `L.coordM` and `L.bIdeal_le_aug`,
  `M₀ ≅ (Λ ⧸ 𝔫)^d ≅ ℤ_p^d`.

And `hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T))` — Eichler–Shimura plus Mazur
multiplicity one — pins it a second, independent way, which also fixes the rank
(`ℤ_p^d ≅ M₀ ≅ T²`, so `d = 2 · rank_{ℤ_p} T`).  So the genuine content of the
three `projM` clauses is the INTERTWINING, not the identification of `M₀`.

# WHAT IS STILL MISSING FROM THE TREE FOR THIS LEAF

Confirmed absent from `Fermat/`, from our mathlib pin and from `~/cs/FLT`; each
is a grep for the name, and each is a statement of the AUTOMORPHIC side only —
the Galois-cohomological vocabulary the RING leaf needs is present and is
listed there:

* **Ihara's lemma** and the level-raising comparison between level `N` and
  level `N·∏Q` — the source of `projM` and of the control theorem;
* **Diamond's freeness theorem** — the source of the coordinate freeness of
  rank `d`;
* a Hecke algebra at RAISED level carrying its module.  The Hilbert side states
  one (`HilbertAuxHeckeAlgebra`) and derives the `R_Q`-action on it from weak
  universality (`exists_module_of_hilbertAuxHeckeAlgebra`); note its
  FORMAL-CONTENT AUDIT, which records that the existence leaf for that
  structure was discharged **without any level raising happening**.  Stating
  the `ℚ` analogue is a legitimate next reduction of THIS leaf and would move
  the automorphic burden onto a named sibling; it is deliberately not done here
  so that the burden stays visible rather than being relocated onto a
  vacuously dischargeable statement.

CIRCULARITY GUARD: as for `exists_auxDeformationDatum` above. -/
theorem exists_auxHeckeModuleData.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 q d : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (M0 : Type) [AddCommGroup M0] [Module T M0]
    (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))
    (n : ℕ) (Q : Finset ℕ) (hQcard : Q.card = q)
    (hQ : IsTaylorWilesPrimeSet p ρbar (n + 1) Q)
    (𝒟Q : AuxDeformationDatum.{uR, uK, uW} hpodd Q ρbar)
    (h𝒟Q : 𝒟Q.IsWeaklyUniversal)
    (I : Ideal (MvPowerSeries (Fin q) coeff.carrier))
    (φ : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) ≃+* 𝒟Q.R)
    (diamond : MvPowerSeries (Fin q) ℤ_[p] →+*
      (MvPowerSeries (Fin q) coeff.carrier ⧸ I))
    (toRuniv : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) →+* Runiv)
    (htoRuniv : Function.Surjective toRuniv)
    (hker : RingHom.ker toRuniv = (taylorWilesAug p q).map diamond)
    (hbn : taylorWilesLevelIdeal p (fun _ : Fin q => n) ≤ RingHom.ker diamond) :
    ∃ (_ : Module (MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (taylorWilesCoordModel p q d n))
      (projM : taylorWilesCoordModel p q d n →+ M0),
      (∀ (x : MvPowerSeries (Fin q) ℤ_[p])
        (m : taylorWilesCoordModel p q d n), x • m = diamond x • m) ∧
      Function.Surjective projM ∧
      (∀ (x : MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (m : taylorWilesCoordModel p q d n),
        projM (x • m) = ψ (toRuniv x) • projM m) ∧
      (∀ m : taylorWilesCoordModel p q d n, projM m = 0 →
        m ∈ (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) := by
  -- LEAF A2′-4a: `M₀` IS the augmentation quotient of the coordinate model …
  obtain ⟨θ0⟩ := nonempty_augQuotEquiv_of_taylorWilesBottom.{s, uR} hM0 hbot n
  -- LEAF A2′-4b (Diamond freeness + Ihara): the `R_Q`-action and the
  -- semilinear comparison — the automorphic content, and all of it.
  obtain ⟨inst, θ, hlam, hint⟩ :=
    exists_auxHeckeCoordModuleData.{s, t, uK, uW, uR} hpodd hW hres hirr hadic
      hcomplete hranku hρuniv hπuniv hfact hrankT hρT hπ hred ψ hψalg hψπ hψ
      q0 q d hq0 coeff M0 hM0 hbot hM0T n Q hQcard hQ 𝒟Q h𝒟Q I φ diamond
      toRuniv htoRuniv hker hbn ⟨θ0⟩
  -- `projM` is `θ` after the augmentation quotient map; the remaining two
  -- clauses are surjectivity and injectivity of that composite.
  refine ⟨inst, θ.toAddMonoidHom.comp
      (Submodule.mkQ (taylorWilesAug p q • ⊤ :
        Submodule (MvPowerSeries (Fin q) ℤ_[p])
          (taylorWilesCoordModel p q d n))).toAddMonoidHom,
    hlam, ?_, ?_, ?_⟩
  · exact θ.surjective.comp (Submodule.mkQ_surjective _)
  · intro x m
    exact hint x m
  · intro m hm
    have h0 : (Submodule.Quotient.mk m :
        taylorWilesCoordModel p q d n ⧸ (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) = 0 := by
      apply θ.injective
      simpa using hm
    exact (Submodule.Quotient.mk_eq_zero _).mp h0

set_option linter.checkUnivs false in
/-- **The auxiliary Taylor–Wiles level in PRESENTED form** (**PROVEN GLUE
since 2026-07-27** over the RING/HECKE cut above; formerly LEAF A2′ of the
2026-07-27 reduction of `exists_taylorWilesAuxLevelData` below): the
arithmetic core of the Taylor–Wiles construction with every carrier and
every piece of coordinate bookkeeping already fixed.

**NO ARITHMETIC HAPPENS HERE ANY MORE.**  The four steps are: choose the
Taylor–Wiles prime set from the supply `hTWq` (at level `n + 1`, for the
reason recorded on `exists_auxDeformationDatum` — the `ℚ`-level
`IsTaylorWilesPrimeSet` carries no `q ≠ 2` / `q ≠ p` clause and its
congruence is vacuous at `n = 0`); obtain a raised-level deformation datum
at `Q` (`exists_auxDeformationDatum`); make it weakly universal
(`exists_isWeaklyUniversal_auxDeformationDatum`); run the RING leaf
(`exists_auxDeformationRingPresentation`) and then the HECKE leaf
(`exists_auxHeckeModuleData`).  The witnesses handed back are the RING
leaf's own `I`, `diamond`, `toRuniv` and the HECKE leaf's module structure
and `projM` — the assembly reshapes nothing, which is why the RING leaf is
asked for its presentation ALREADY in quotient form together with the
isomorphism `Λ_𝒪 ⧸ I ≃+* R_Q` (see clause 1 of its docstring: that is one
line for its prover and saves the assembly a transport).

**UPDATED 2026-07-28: both halves of the RING/HECKE cut are themselves
PROVEN GLUE now, and the four open leaves below them are the six named
above** — `exists_auxDeformationDatum`,
`exists_isWeaklyUniversal_auxDeformationDatum`,
`exists_auxDeformationPresSurjection`,
`exists_auxDeformationDiamondControl`,
`nonempty_augQuotEquiv_of_taylorWilesBottom` and
`exists_auxHeckeCoordModuleData`.  Dispatch at those, not at
`exists_auxDeformationRingPresentation` or `exists_auxHeckeModuleData`.

The remaining arithmetic is split along the RING/HECKE axis, mirroring the
cut taken the same day on the Hilbert side
(`exists_hilbertAuxDeformationRingPresentation` /
`exists_hilbertAuxHeckeModuleData`).  **The naive form of that split is
UNSAFE and plants a FALSE leaf** — the explicit junk-ring counterexample is
written out in the CUT-SAFETY section of `exists_auxHeckeModuleData` — and
what makes it safe is that the HECKE leaf receives its ring as a WEAKLY
UNIVERSAL `AuxDeformationDatum`, not as a carrier satisfying four
structural equations.  Everything below in this docstring describes the
hypothesis package, which is unchanged; the audits it records are now
audits of the cut's inputs rather than of a single leaf.

Relative to `exists_taylorWilesAuxLevelData`, four obligations have been
discharged in the assembly below rather than asked of a prover:

1. **the exponent vector `e`** — fixed to the constant vector `e ≡ n`
   (EXPONENT AUDIT below);
2. **the carrier of the auxiliary deformation ring** — the ring is
   produced as an explicit quotient `Λ_𝒪/I` of the power-series ring
   `Λ_𝒪 = 𝒪[[x_1, …, x_q]]`, which is ALREADY in `Type` because
   `TaylorWilesCoefficients.carrier` is, so no universe-`0` model has to
   be exhibited;
3. **`pres` and its surjectivity** — `Ideal.Quotient.mk I`, free;
4. **the carrier of the Hecke module and `coordM`** — the module is
   produced ON the coordinate model `taylorWilesCoordModel p q d n`
   itself, so `coordM` is `LinearEquiv.refl` and the `Λ`-module
   structure is the canonical one.

This is exactly the manoeuvre already sanctioned one leaf above, in the
2026-07-27 correction to `exists_taylorWilesBottomPresentation`'s
obligation 3 ("it is free, and this docstring previously overstated
it"): a quotient of a `Type`-valued power-series ring is a `Type`, and a
free module in coordinates is its own coordinate model.  The two
statements are equivalent — any ring with a surjection from `Λ_𝒪` is
isomorphic to a quotient of it, and any module with a `Λ`-linear
coordinate equivalence may be transported onto the coordinate model —
so nothing is weakened, and what remains is the arithmetic and only the
arithmetic.

# EXPONENT AUDIT (2026-07-27) — `∃ e, ∀ i, n ≤ e i` CARRIES NO CONTENT

`exists_taylorWilesAuxLevelData`'s exponent existential looks like the
local class field theory at the Taylor–Wiles primes — classically
`e_i = v_p(q_i − 1)`, so that `Δ_Q = ∏_i ℤ/p^{e_i}`.  It is not: the
constant vector `e ≡ n` discharges it, and doing so is not a dodge but
the standard formulation.

Reason.  `n ≤ e_i` gives `(1 + S_i)^{p^{e_i}} − 1 =
((1 + S_i)^{p^n})^{p^{e_i − n}} − 1`, which `sub_dvd_pow_sub_pow` makes
divisible by `(1 + S_i)^{p^n} − 1`; hence `𝔟_{(e_i)} ⊆ 𝔟_{(n)}` and
`Λ/𝔟_{(n)}` is a QUOTIENT of `Λ/𝔟_{(e_i)} = ℤ_p[Δ_Q]`, namely
`ℤ_p[Δ_Q/Δ_Q^{p^n}] = ℤ_p[(ℤ/p^n)^q]`.  A module free of rank `d` over
`ℤ_p[Δ_Q]` therefore has free rank-`d` reduction over `ℤ_p[(ℤ/p^n)^q]`,
with the same augmentation quotient because `𝔟_{(n)} ⊆ 𝔫`.  This is how
Taylor–Wiles, Diamond and DDT set the tower up in the first place (the
levels are indexed by `n`, not by the individual valuations), so the
classical construction proves the constant-exponent form directly.

Consequence for dispatch: **do not send anyone at "compute
`v_p(q_i − 1)`".**  That computation is not in this leaf and never was.

# INTERFACE REPAIR — THE PRIME SET IS NOW CHOSEN HERE, NOT HANDED IN
# (2026-07-27; supersedes the INTERFACE DEFECT section this replaces)

**What the defect was.**  The Taylor–Wiles construction does not work
for an arbitrary set of Taylor–Wiles primes.  It works for a set `Q`
chosen so that the DUAL Selmer group vanishes,

    H¹_{Q*}(ℚ, ad⁰ρbar(1)) = 0 ,

which by Greenberg–Wiles is exactly what forces
`dim_k H¹_Q(ℚ, ad⁰ρbar) = #Q` and hence what makes `R_Q` generated by
`#Q = q` elements over `𝒪` — i.e. what makes `pres` exist at all.
`IsTaylorWilesPrimeSet` does not say this; unfolded (its definition is
above, in this file) it is

    ∀ q ∈ Q, ∃ hq : q.Prime, q ≡ 1 [MOD p^n] ∧
      ∃ α β : k, α ≠ β ∧ ρbar.charFrob … = (X − C α) * (X − C β) ,

a conjunction of purely LOCAL conditions at each `q ∈ Q`, with no global
cohomological clause anywhere.  This leaf used to receive `Q` as a FIXED
hypothesis satisfying only that, so it was universally quantified over
sets for which `dim_k H¹_Q > #Q` and for which no `q`-generator
presentation exists — a statement strictly stronger than the classical
theorem, and one no classical route can reach.  That is the "a datum
handed across a seam can only be constrained by what already saw it"
failure mode.

**The repair taken.**  `Q` does not occur in this leaf's CONCLUSION.  So
the fixed `(Q) (hQcard) (hQ)` have been replaced by the SUPPLY

    hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q ,

threaded down from `exists_taylorWilesTower` through
`exists_taylorWilesLevelRaw` (which no longer consumes it) and
`exists_taylorWilesAuxLevelData`.  This mirrors the shape already
working on the Hilbert side and at `exists_taylorWilesBottomPresentation`
in this file, and it touches no predicate and no other construction site.
The statement changes from `∀ Q, local(Q) → C` to `(∀ r n, ∃ Q, …) → C`,
which is the classical shape: a prover now MAKES the choice, at the
cardinality `q` the ring side forces, and is free to refine within the
supply.

**Why the supply, and not `hres`/`hirr`, is what has to be threaded.**
This leaf cannot manufacture prime sets for itself.  The tree's supplier
`exists_taylorWilesPrimeSet` needs `IsHardlyRamified hpodd hW ρbar`, and
this leaf deliberately carries only `IsTaylorWilesResidual` (see that
structure's WHAT IS DELIBERATELY ABSENT section — the full package is
classically unsatisfiable and would hand the leaf a free discharge).  So
without `hTWq` there is no way to obtain even one admissible `Q`, and the
existential form would be unreachable rather than merely open.

**Threading alone would NOT have sufficed, and that is why the predicate
was repaired too.**  Before 2026-07-27 `hTWq`'s payload was the purely
local predicate, universally quantified over sizes.  Dual-Selmer
vanishing is not implied by those conditions: the primes detecting a
given nonzero class `c ∈ H¹(ℚ, ad⁰ρbar(1))` form a proper (positive
density) subset of those satisfying `q ≡ 1 mod p^n` with split distinct
Frobenius eigenvalues, so the supply provably contains sets of EVERY size
whose dual Selmer group does not vanish.  Threading such a supply moves
the leaf from "no freedom" to EMPTY freedom — it builds green and the
leaf stays unprovable.  So both halves were done: the supply is threaded
(above) **and** `IsTaylorWilesPrimeSet` now carries the dual-Selmer
clause (see its docstring).  With both, the `Q` this leaf picks is one
for which the classical `q`-generator presentation exists.

*The refuting check for this section*, so the next reader need not redo
the survey: `grep -n 'def IsTaylorWilesPrimeSet' -A 40` on this file.  The
second conjunct is the global clause; if it is ever removed, this leaf
becomes unprovable again and this section is the reason.

# THE `q` HAZARD IS NOW DISCHARGED TOO — `hq0 : q0 ≤ q` (2026-07-27)

`exists_taylorWilesBottomPresentation`'s FORMAL-CONTENT AUDIT records the
hazard that `q` may be returned as Cohen's `μ(𝔪_Runiv)`, BELOW the
Taylor–Wiles number, and instructs a prover to return
`max(Cohen's q, the Taylor–Wiles number)`.  That instruction used to be
unimplementable: `exists_taylorWilesCoefficientsPresentation`'s signature
is

    {R} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hcomplete : IsAdicComplete (maximalIdeal R) R)
    {k} [Field k] [Finite k] {π : R →+* k} (hπ : Surjective π) (q₀ : ℕ) →
    ∃ q coeff φ, q₀ ≤ q ∧ Surjective φ

— there is no `ρbar` and no Galois object of any kind in scope, so the
Taylor–Wiles number was not nameable there.  It takes a LOWER BOUND `q₀`,
though, and the repaired supply now carries exactly such a bound:
`exists_taylorWilesPrimeSet` returns a level-independent `q0` below which
no exact-size Taylor–Wiles set exists at all.  That `q0` is threaded down
this chain, passed to Cohen's presentation as `q₀`, and arrives here as

    hq0 : q0 ≤ q

so `q` really is `max(Cohen's q, the Taylor–Wiles number)`.  **This is one
repair with the `Q` one, not two**: both defects were "a datum chosen by a
statement that cannot see the cohomology constraining it", and both are
fixed by making the cohomology part of `IsTaylorWilesPrimeSet` and letting
the supply carry the bound.  A prover of this leaf may and should use
`hq0`; it is what makes the `q` variables enough.

# ROUTE NOTE FOR THE NEXT OWNER — `M0` IS PINNED BY `hbot`

Not obvious from the statement, and it removes a whole degree of
freedom: `hbot` already determines `M0` up to additive isomorphism.
Writing `L := hbot.some`,

* `L.projM_eq_zero` gives `ker L.projM ⊆ 𝔫 • ⊤`;
* the reverse inclusion is forced: for `x ∈ 𝔫` and any `m`,
  `L.projM (x • m) = L.projM (L.diamond x • m) = ψ (L.toRuniv
  (L.diamond x)) • L.projM m` by `L.diamond_smul` and `L.projM_smul`,
  and `L.diamond x ∈ (taylorWilesAug p q).map L.diamond =
  RingHom.ker L.toRuniv` by `L.ker_toRuniv`, so the scalar is `ψ 0 = 0`;
* hence `ker L.projM = 𝔫 • ⊤` exactly, and with `L.coordM` and
  `L.bIdeal_le_aug` (`𝔟_0 ⊆ 𝔫`),

      M0 ≅ L.M / 𝔫·L.M ≅ (Λ/𝔟_0)^d / 𝔫·(…) ≅ (Λ/𝔫)^d ≅ ℤ_p^d .

So `M0` is free of rank `d` over `ℤ_p`, and the coordinate model of THIS
leaf has the same `𝔫`-quotient by `taylorWilesLevelIdeal_le_aug`.  The
only genuine content left in the three `projM` clauses is therefore the
INTERTWINING — that the `Λ_𝒪/I`-action on `(Λ/𝔟_n)^d` reduces mod `𝔫`
to the given `T`-action on `M0` through `ψ ∘ toRuniv`.  Surjectivity and
the control theorem follow from any additive identification realising
the display above.  **ACTED ON 2026-07-28**: the display is now the named
leaf `nonempty_augQuotEquiv_of_taylorWilesBottom` above, and
`exists_auxHeckeModuleData` is PROVEN GLUE over it together with
`exists_auxHeckeCoordModuleData`, whose only remaining content is the
`R_Q`-action and the intertwining.  (It was left as a route note rather
than a proven reduction only because the
quotient-of-a-product-of-quotients transport is a substantial `Submodule`
exercise; it is a clean, self-contained next step, and it consumes
nothing that is not already proven.)

**And `M0` is pinned a second, independent way: `hM0T` (added 2026-07-27).**
`hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T))` is Eichler–Shimura plus Mazur's
multiplicity one, propagated down from
`exists_taylorWilesBottomHeckeModule` through
`exists_taylorWilesBottomLevel`, `exists_taylorWilesTower`,
`exists_taylorWilesLevelRaw` and `exists_taylorWilesAuxLevelData` (see §4
of that leaf's VACUITY AUDIT).  It is a WEAKENING of this leaf, and a
load-bearing one: without it a discharge of the bottom leaf was free to
hand over `T`, `T³`, or a module on which `T` acts through an unrelated
quotient, and for such an `M₀` no tower of `Λ/𝔟_n`-free modules with
`𝔫`-quotient `M₀` exists — i.e. this leaf was FALSE for those witnesses,
with no signal a compiler or an axiom audit could emit.

Combined with the `hbot` route note above (`M0 ≅ ℤ_p^d`) it also fixes
the rank: `ℤ_p^d ≅ M₀ ≅ T²` forces `d = 2 · rank_{ℤ_p} T`, so `d` is not
a free parameter of this leaf either.  Both pins constrain only `M₀`;
the ring side — a `q`-generator quotient of `Λ_𝒪` with the control
identification — remains the genuine arithmetic, and it is now owned by
`exists_auxDeformationRingPresentation` above.

# MISSING MACHINERY, AND WHICH SUB-LEAF NOW OWNS EACH PIECE

Kept here because it is the map of the whole node, but **this is no
longer a list of what a prover of THIS statement needs** — each item now
has a named owner among the SIX open sub-leaves of the RING/HECKE cut
above (four cut 2026-07-27, re-cut into six on 2026-07-28 when both
halves became PROVEN GLUE), and a dispatcher should send work at the
owner, not here:

* **Ihara's lemma** and the level-raising comparison between level `N`
  and level `N·∏Q` — the source of `projM` and of the control theorem.
  Owner: `exists_auxHeckeCoordModuleData`, its semilinearity clause.
  The purely algebraic half of the comparison — that `M₀` IS the
  augmentation quotient of the coordinate model — is split off as
  `nonempty_augQuotEquiv_of_taylorWilesBottom` and needs no automorphic
  input at all;
* **Diamond's freeness theorem** (Invent. Math. 128 (1997), Thm. 2.1) —
  freeness of the auxiliary Hecke module over `ℤ_p[Δ_Q]` of the
  level-independent rank `d`, here in the coordinate form.  Owner:
  `exists_auxHeckeCoordModuleData`, its module-structure clause;
* **the auxiliary deformation ring `R_Q`** — Mazur representability for
  the hardly-ramified-outside-`Q` problem, its tangent-space bound over
  `𝒪`, and the control theorem `R_Q/𝔞_Q ≅ R_univ`.  Owners:
  `exists_auxDeformationDatum` (non-emptiness of the category, i.e. the
  split-torus clause at `Q`),
  `exists_isWeaklyUniversal_auxDeformationDatum` (representability),
  `exists_auxDeformationPresSurjection` (the `q`-generator bound) and
  `exists_auxDeformationDiamondControl` (the control map);
* **local class field theory at the Taylor–Wiles primes** — the tame
  characters at `q ∈ Q` giving the `Δ_Q`-action, hence `diamond`.
  Owner: `exists_auxDeformationDiamondControl`, clause 1;
* **Galois cohomology of `ad⁰ρbar`** — the Greenberg–Wiles formula
  relating `dim H¹_Q` to `dim H¹_{Q*}`.  **CORRECTED 2026-07-27: the
  VOCABULARY is no longer missing** and this bullet used to send
  dispatchers at a subtree that already exists.
  `HardlyRamified/Deformation.lean` carries `AdZero`, `adZeroTopRep`,
  `adZeroCycloChar`, `adZeroTwistRep`, `adZeroTwist = ad⁰(1)`,
  `adZeroTwistLocal`, `locRes`, `locResTwist1`, `Sha2`, `Sha1Twist` and
  `hardlyRamifiedPlaces`, all sorry-free, over mathlib's
  `continuousCohomology` at every degree; this file `public import`s it,
  and the *unramified at `v`* condition it lacked is supplied above by
  `locResInertiaTwist1`.  What is still missing is the THEORY, not the
  language: finiteness of the unramified-outside-`S` part of
  `H¹(ℚ, ad⁰ρbar(1))`, the Chebotarev separation of a single class by a
  Taylor–Wiles prime (DDT Lemma 2.48), and Greenberg–Wiles itself.  The
  first two are now the NAMED leaves `finite_h1TwistUnramified` and
  `exists_taylorWilesPrime_locResDecomp_ne_zero` above (hoisted
  2026-07-27 out of the internal `have hcore` of
  `exists_taylorWilesPrimeSet`, which is again sorry-free); the third is
  what a prover of THIS leaf needs.

CIRCULARITY GUARD: inherited verbatim from
`exists_taylorWilesAuxLevelData` and hence from
`exists_taylorWilesLevelRaw` —
`not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` and
`Slop.OddRep.isIrreducible_iff_forall` against `hirr`, any
reduction-descent lemma producing `IsHardlyRamified hpodd hW ρbar` from
`hρT`/`hρuniv`, and `Family.lean` with everything downstream of it, are
BANNED as inputs.  A proof ending in `exfalso` is the circular discharge
again and must be rejected. -/
theorem exists_taylorWilesAuxLevelPresentedDatum.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q)
    (q d : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (M0 : Type) [AddCommGroup M0] [Module T M0]
    (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))
    (n : ℕ) :
    ∃ (I : Ideal (MvPowerSeries (Fin q) coeff.carrier))
      (diamond : MvPowerSeries (Fin q) ℤ_[p] →+*
        (MvPowerSeries (Fin q) coeff.carrier ⧸ I))
      (toRuniv : (MvPowerSeries (Fin q) coeff.carrier ⧸ I) →+* Runiv)
      (_ : Module (MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (taylorWilesCoordModel p q d n))
      (projM : taylorWilesCoordModel p q d n →+ M0),
      Function.Surjective toRuniv ∧
      RingHom.ker toRuniv = (taylorWilesAug p q).map diamond ∧
      (∀ (x : MvPowerSeries (Fin q) ℤ_[p])
        (m : taylorWilesCoordModel p q d n), x • m = diamond x • m) ∧
      Function.Surjective projM ∧
      (∀ (x : MvPowerSeries (Fin q) coeff.carrier ⧸ I)
        (m : taylorWilesCoordModel p q d n),
        projM (x • m) = ψ (toRuniv x) • projM m) ∧
      (∀ m : taylorWilesCoordModel p q d n, projM m = 0 →
        m ∈ (taylorWilesAug p q • ⊤ :
          Submodule (MvPowerSeries (Fin q) ℤ_[p])
            (taylorWilesCoordModel p q d n))) := by
  -- The Taylor–Wiles prime set, asked at level `n + 1` rather than `n`: the
  -- `ℚ`-level `IsTaylorWilesPrimeSet` does not carry `q ≠ 2` / `q ≠ p`, and at
  -- `n = 0` its congruence is vacuous, so the split-torus clause of
  -- `exists_auxDeformationDatum` would have no unramifiedness to start from.
  -- A level-`(n+1)` set is a level-`n` set a fortiori, so nothing is lost.
  obtain ⟨Q, hQcard, hQ⟩ := hTWq q (n + 1) hq0
  -- LEAF A2′-1: the raised-level deformation category at `Q` is nonempty …
  obtain ⟨𝒟₀⟩ := exists_auxDeformationDatum.{uK, uW, uR} hpodd hW hres hirr hadic
    hcomplete hranku hρuniv hπuniv hunivred (n + 1) (by omega) Q hQ
  -- LEAF A2′-2: … and has a weakly universal object `R_Q`
  obtain ⟨𝒟Q, h𝒟Q⟩ := exists_isWeaklyUniversal_auxDeformationDatum.{uK, uW, uR}
    hpodd hW hirr (n + 1) Q hQ 𝒟₀
  -- The coefficient ring is the right one: `hbot` already presents `Runiv` over
  -- `Λ_coeff`, which is what pins `coeff`'s residue field to `k` (see the
  -- FAITHFULNESS REPAIR section of `exists_auxDeformationRingPresentation`).
  have hcoeff : ∃ c : MvPowerSeries (Fin q) coeff.carrier →+* Runiv,
      Function.Surjective c := by
    obtain ⟨L⟩ := hbot
    letI := L.commRingR
    exact ⟨L.toRuniv.comp L.pres,
      L.toRuniv_surjective.comp L.pres_surjective⟩
  -- LEAF A2′-3 (RING): the presentation of `R_Q`, the diamonds, the control map
  obtain ⟨I, φ, diamond, toRuniv, htoRuniv, hker, hbn⟩ :=
    exists_auxDeformationRingPresentation.{s, t, uK, uW, uR} hpodd hW hres hirr
      hadic hcomplete hranku hρuniv hπuniv hunivred hfact q0 q hq0 coeff hcoeff
      n Q hQcard hQ 𝒟Q h𝒟Q
  -- LEAF A2′-4 (HECKE): the auxiliary Hecke module on the coordinate model
  obtain ⟨actR, projM, hlam, hsurj, hint, hctrl⟩ :=
    exists_auxHeckeModuleData.{s, t, uK, uW, uR} hpodd hW hres hirr hadic
      hcomplete hranku hρuniv hπuniv hfact hrankT hρT hπ hred ψ hψalg hψπ hψ
      q0 q d hq0 coeff M0 hM0 hbot hM0T n Q hQcard hQ 𝒟Q h𝒟Q I φ diamond
      toRuniv htoRuniv hker hbn
  exact ⟨I, diamond, toRuniv, actR, projM, htoRuniv, hker, hlam, hsurj, hint,
    hctrl⟩

set_option linter.checkUnivs false in
/-- **The auxiliary Taylor–Wiles level at a GIVEN prime set** (sorry
node, LEAF A2 of the 2026-07-27 decomposition of
`exists_taylorWilesLevelRaw`): the arithmetic core of the Taylor–Wiles
construction — ingredients 2, 3 and 4, at a prime set `Q` that this leaf
(and not the assembly) chooses from the supply `hTWq`.

What has been stripped off relative to the parent leaf, and where it
went:

* the CHOICE of the level-`n` prime set `Q` with `#Q = q` — **kept here**
  since the 2026-07-27 interface repair: the SUPPLY `hTWq` is threaded in
  rather than consumed above, because a `Q` chosen in the assembly
  arrives fixed and the leaf would have nothing to re-choose from.  The
  bound `hq0 : q0 ≤ q` is what makes `hTWq q n` applicable;
* the SHAPE of the level ideal — instead of an arbitrary
  `bIdeal : Ideal Λ`, this leaf produces only the exponent vector
  `e : Fin q → ℕ` (classically `e i = v_p(q_i − 1)` for the `i`-th prime
  of `Q`, which is `≥ n` exactly because `q_i ≡ 1 mod p^n`), and the
  ideal itself is `taylorWilesLevelIdeal p e`;
* the two `bIdeal` bounds — now `taylorWilesLevelIdeal_le_maximalIdeal_pow`
  (from `∀ i, n ≤ e i`, which this leaf still asserts) and
  `taylorWilesLevelIdeal_le_aug` (PROVEN unconditionally).

What remains here is exactly ingredients 2–4 plus the level-`n` half of
ingredient 5, in the raw-level vocabulary and with no bookkeeping:

2. the augmented Mazur package at `Q` — representability of the
   hardly-ramified problem with allowed ramification at `Q`, giving `R`
   with the `q`-generator presentation `pres` over `coeff`, and the
   control identification `toRuniv : R ↠ Runiv` with kernel `𝔫·R`
   (switching the diamond operators off returns the original problem);
3. local class field theory at the Taylor–Wiles primes — the tame
   inertia characters at `q ∈ Q` give the `Δ_Q`-action, i.e. `diamond`
   and the exponents `e`;
4. Diamond's freeness certificate (Invent. Math. 128 (1997), Thm. 2.1) —
   `M` is free of the level-independent rank `d` over
   `Λ/𝔟_n = ℤ_p[Δ_Q]`, here in the coordinate form;
5. the Ihara/level-raising comparison with the bottom module: `projM`
   onto `M₀`, intertwining through `ψ ∘ toRuniv`, with the control
   theorem `projM m = 0 → m ∈ 𝔫·M`.

WHY THE RING AND THE MODULE STAY IN ONE LEAF.  They are not separable
here: a module leaf receiving the ring datum as a hypothesis would
quantify over ALL ring data with those properties, and for junk ones no
free Hecke module of rank `d` with the right `𝔫`-quotient exists — the
"unfaithful module leaf over an uncharacterized ring" of the design note
in `exists_taylorWilesBottomLevel`.  The level ideal is separable only
because `taylorWilesLevelIdeal` pins it completely.

Everything is stated at universe `0` for `R` and `M` (the Type-0 note of
`exists_taylorWilesTower`).

CIRCULARITY GUARD: inherited unchanged from `exists_taylorWilesLevelRaw`
— `not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` and
`Slop.OddRep.isIrreducible_iff_forall` against `hirr`, any
reduction-descent lemma producing `IsHardlyRamified hpodd hW ρbar` from
`hρT`/`hρuniv`, and `Family.lean` with everything downstream of it, are
BANNED as inputs.  A proof ending in `exfalso` is the circular discharge
again and must be rejected.

**REDUCED 2026-07-27 — no longer a leaf.**  This statement is now PROVEN
from `exists_taylorWilesAuxLevelPresentedDatum` above (itself PROVEN GLUE
since later the same day, over the four sub-leaves of the RING/HECKE cut),
which carries the same hypothesis package and the same arithmetic while
having four obligations discharged here instead: the exponent vector
(taken constant, `e ≡ n` — see that leaf's EXPONENT AUDIT for why this
is the standard formulation and not a weakening), the universe-`0`
carrier of the auxiliary deformation ring (an explicit quotient of
`𝒪[[x_1, …, x_q]]`), `pres` with its surjectivity
(`Ideal.Quotient.mk_surjective`), and the carrier of the Hecke module
together with `coordM` (the module is produced ON the coordinate model
`taylorWilesCoordModel`, so `coordM` is `LinearEquiv.refl`).

**Read that leaf's INTERFACE REPAIR section before dispatching anyone at
it.**  Until 2026-07-27 its prime set arrived FIXED and
`IsTaylorWilesPrimeSet` contained only LOCAL conditions at each `q ∈ Q`,
so the classical Taylor–Wiles route did not apply and the leaf was
unprovable in principle.  Both halves are now repaired at the cut: the
predicate carries the dual-Selmer vanishing clause, and the supply
`hTWq` (with its bound `hq0 : q0 ≤ q`) is threaded down so the leaf makes
the choice itself.  What remains there is missing mathematics, not a
broken interface.

**MULTIPLICITY-ONE PIN THREADED 2026-07-27.**  The hypothesis
`hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T))` — Eichler–Shimura plus Mazur
multiplicity one, `hirr` supplying non-Eisensteinness — now arrives here
from `exists_taylorWilesBottomHeckeModule` via
`exists_taylorWilesBottomLevel`, `exists_taylorWilesTower` and
`exists_taylorWilesLevelRaw`, and is passed on to the leaf above.  It is
a WEAKENING, and it is what makes this statement true rather than merely
open: without it `M0` was quantified over every `T`-module admitting a
level-`0` raw datum, including `T`, `T³` and modules with an unrelated
`T`-action, and for those no tower of `Λ/𝔟_n`-free modules with
`𝔫`-quotient `M0` exists.  See §4 of the VACUITY AUDIT on
`exists_taylorWilesBottomHeckeModule`. -/
theorem exists_taylorWilesAuxLevelData.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q)
    (q d : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (M0 : Type) [AddCommGroup M0] [Module T M0]
    (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))
    (n : ℕ) :
    ∃ e : Fin q → ℕ, (∀ i, n ≤ e i) ∧
      ∃ (R : Type) (_ : CommRing R)
        (pres : MvPowerSeries (Fin q) coeff.carrier →+* R)
        (diamond : MvPowerSeries (Fin q) ℤ_[p] →+* R)
        (toRuniv : R →+* Runiv)
        (M : Type) (_ : AddCommGroup M) (_ : Module R M)
        (_ : Module (MvPowerSeries (Fin q) ℤ_[p]) M)
        (projM : M →+ M0),
        Function.Surjective pres ∧
        Function.Surjective toRuniv ∧
        RingHom.ker toRuniv = (taylorWilesAug p q).map diamond ∧
        (∀ (x : MvPowerSeries (Fin q) ℤ_[p]) (m : M), x • m = diamond x • m) ∧
        Nonempty (M ≃ₗ[MvPowerSeries (Fin q) ℤ_[p]]
          (Fin d → MvPowerSeries (Fin q) ℤ_[p] ⧸ taylorWilesLevelIdeal p e)) ∧
        Function.Surjective projM ∧
        (∀ (x : R) (m : M), projM (x • m) = ψ (toRuniv x) • projM m) ∧
        (∀ m : M, projM m = 0 →
          m ∈ (taylorWilesAug p q • ⊤ :
            Submodule (MvPowerSeries (Fin q) ℤ_[p]) M)) := by
  -- LEAF A2′ (`exists_taylorWilesAuxLevelPresentedDatum`): the arithmetic
  -- core, with the auxiliary deformation ring produced as an explicit
  -- quotient `Λ_𝒪/I` and the Hecke module produced on the coordinate
  -- model `(Λ/𝔟_n)^d` itself.
  obtain ⟨I, diamond, toRuniv, actR, projM, htoR, hker, hlam, hsurj, hint,
      hctrl⟩ :=
    exists_taylorWilesAuxLevelPresentedDatum.{s, t, uK, uW, uR} hpodd hW hres
      hirr hadic hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ
      hred ψ hψalg hψπ hψ q0 hTWq q d hq0 coeff M0 hM0 hbot hM0T n
  -- The exponent vector is the constant one; `pres` is the quotient map and
  -- `coordM` is the identity, both free at the presented shape.
  exact ⟨fun _ => n, fun _ => le_rfl,
    MvPowerSeries (Fin q) coeff.carrier ⧸ I, inferInstance,
    Ideal.Quotient.mk I, diamond, toRuniv,
    taylorWilesCoordModel p q d n, inferInstance, actR, inferInstance, projM,
    Ideal.Quotient.mk_surjective, htoR, hker, hlam,
    ⟨LinearEquiv.refl _ _⟩, hsurj, hint, hctrl⟩

set_option linter.checkUnivs false in
/-- **The bottom Taylor–Wiles level** (patching leaf 2a-i-α, sorry
node — the MODULARITY-SUBTREE PLUG POINT): under the full hypothesis
set of pillar 3b-iii, the level-independent invariants of the
Taylor–Wiles tower exist together with the bottom (`Q = ∅`) level
datum.

What is asserted: a Taylor–Wiles number `q`, a freeness rank `d`, and
a NONTRIVIAL bottom Hecke module `M₀` carrying an action of the
abstract Hecke ring `T` of the pillar, such that `M₀ ≃ₗ[T] T²` (the
MULTIPLICITY-ONE PIN, propagated 2026-07-27 from
`exists_taylorWilesBottomHeckeModule`, whose §4 explains why it must be
carried here rather than dropped) and the level-`0` raw datum exists
over them.  Classically `M₀ = H¹(X₀(N), ℤ_p)_𝔪` is the
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

REPAIR — DECIDED 2026-07-26, ROUTE (b): GENERALIZE THE COEFFICIENT
RING.  The two candidates were:

(a) pin the residual field: add `(hk : Nat.card k = p)` — equivalently
    `Nonempty (k ≃+* ZMod p)` — to this leaf and to
    `exists_taylorWilesLevelRaw`, and thread it through
    `exists_taylorWilesTower`, `exists_taylorWilesSystem`,
    `exists_patchedModule`, `injective_ringHom_of_isWeaklyUniversal`
    and the two `Interface.lean` call sites.
(b) generalize the coefficient ring of the patching interface from
    `ℤ_[p]` to a coefficient ring `𝒪` (complete DVR with residue field
    `k` — classically `WittVector p k`), which does not touch
    `Interface.lean`.

**(a) was rejected because its call sites cannot supply the
hypothesis.**  This is not a matter of cost: `hk` speaks about `k`,
and at BOTH `Interface.lean` call sites
(`exists_ringHom_charFrob_eq_of_heckeDeformation`,
`exists_weightTwoEigenform_of_heckeDeformation_order_point`) the
residual field is an abstract variable, so `hk` can only be threaded
further up.  Following it up: those two feed
`exists_weightTwoEigenform_trace_eq_of_matchesResidualTraces`, which
feeds `exists_weightTwoEigenform_trace_eq_of_isIrreducible`, where the
residual field is no longer even a variable — it is produced
EXISTENTIALLY by `exists_residual_isHardlyRamified_odd` as the residue
field of the abstract coefficient ring `R`.  So `hk` would have to be
restated there as a restriction on `R` ("`R` has residue field of
order `p`") and pushed on into `Family.lean`'s
`exists_finiteDimensional_trace_field_of_isIrreducible`, i.e. into the
automorphy core itself.  Route (a) therefore does not repair the
defect, it RELOCATES it — as a permanent narrowing of the modularity
statement, in files owned by other cuts.  (It would be dischargeable
at the FLT root, where `R = ℤ_[p]`; that is not the point.  The
narrowing is not a property of the Taylor–Wiles construction, which
presents over `𝒪 = W(k)`, and hypotheses that a caller cannot supply
locally are how unfaithful interfaces spread.)

**(b) is much cheaper than the 2026-07-25 survey recorded.**  Two
things that survey got wrong, both checked mechanically:

* the `PatchingVendored/` chain — `Ultraproduct`, `InverseLimit`,
  `Module`, `Over`, `System`, `Algebra`, `Lemmas`, `AdicTopology`,
  `StructureFiniteness`, `TopologicallyFG` — contains **zero**
  occurrences of `ℤ_[p]`.  It is already coefficient-generic and needs
  no regeneralization at all;
* no `WittVector` theory is needed HERE.  `𝒪` does not have to be
  literally `WittVector p k`: it is produced EXISTENTIALLY by this
  leaf, exactly like `M₀`, so "for a finite field `k` there is a
  complete DVR with residue field `k`, finite free over `ℤ_[p]`" stays
  inside the sorried arithmetic where it belongs — it is part of the
  classical Taylor–Wiles construction, not a new commutative-algebra
  obligation on the proven side.

The properties of `𝒪` the PROVEN side actually consumes are, in
dependency order: local, Noetherian, `𝔪_𝒪` spanned by a length-one
regular sequence (`𝒪` a DVR), finite residue field, compact and
totally disconnected in its topology, and topologically finitely
generated over `ℤ`.  All hold for `W(k)` with `k` finite.

THE REPAIR AS MADE (2026-07-26) — `𝒪` IN THE PRESENTATION ROLE ONLY.

`𝒪` is carried by `TaylorWilesCoefficients` (a bundle: local
Noetherian DVR, compact totally disconnected Hausdorff, finite residue
field, topologically finitely generated over `ℤ`) as a field of
`PatchedModule`, `TaylorWilesSystem` and `TaylorWilesTower` and as a
parameter of `TaylorWilesLevel`/`TaylorWilesLevelRaw`.  It replaces
`ℤ_[p]` in exactly ONE role — the presentation ring of `pres`, hence
also `PatchedModule`'s `R_∞` (whose `Λ` is purely a presentation ring:
the vendored `PatchingAlgebra.lift` already takes the presentation ring
`Rₒₒ` decoupled from the patching base).  **The DIAMOND role keeps
`ℤ_[p]`** — `taylorWilesAug`, `bIdeal`, `diamond`, `coordM`/`freeM`,
`projM_eq_zero` are unchanged.

Why that is enough, and honest: the freeness certificate over
`𝒪[Δ_{Q_n}]` implies freeness over `ℤ_p[Δ_{Q_n}]` of rank
`[k:𝔽_p]·d_𝒪`, since `𝒪` is finite free over `ℤ_[p]`; the bottom module
is correspondingly `ℤ_p`-free; and the patching endgame consumes only
that `dim 𝒪[[x₁,…,x_q]] = q + 1 = dim ℤ_p[[S₁,…,S_q]]`, the depth
bound coming from the DIAMOND side and the dimension bound from the
PRESENTATION side.  So the interface records a true, slightly weaker
form of Diamond's Thm. 2.1, and the obstruction is gone: the only
surjection onto `k` the interface forces is `𝒪 ↠ k`, satisfied by
`𝒪 = W(k)`.

Keeping the diamond role over `ℤ_[p]` also avoids a new structure
field: `ringHom_mvPowerSeries_eq_of_taylorWilesAug_le_ker` (LEAF 7 of
`exists_patchedModule_of_fields`) derives the level-independence of
`toRuniv ∘ diamond` from the UNIQUENESS of `ℤ_[p] →+* Runiv`
(`subsingleton_ringHom_padicInt`), which FAILS over a general `𝒪`; had
the diamond role moved too, the interface would have had to carry a
shared `structMap : 𝒪 →+* Runiv` together with
`((toRuniv n).comp (diamond n)).comp C = structMap`.

WHAT THIS LEAF OWES, beyond the arithmetic already listed: the
existence of `𝒪` itself, i.e. `WittVector p k` presented as a
`TaylorWilesCoefficients`.  That is deliberate — it is part of the
classical Taylor–Wiles construction, not a commutative-algebra
obligation on the proven side.  This obligation is GENUINELY OWED again
as of the re-opening below (while the leaf was discharged from `False`
it was not: the witness `coeff` came out of the empty context and no
Witt-vector theory was consumed anywhere in the cone).  The survey has
been done, so do not repeat it: mathlib's pin DOES carry
`WittVector.isDiscreteValuationRing` (for `k` a perfect field of
characteristic `p`), which supplies `isLocalRing`, `isNoetherianRing`
and `exists_isRegular_maximalIdeal` nearly directly.  What is genuinely
missing is the TOPOLOGICAL half — `IsTopologicalRing (𝕎 k)`,
`CompactSpace`, `T2Space` and `TotallyDisconnectedSpace` for the
coefficientwise product topology (reachable through
`WittVector.wittAdd_vars` / `wittMul_vars`, which bound each structure
polynomial's variables by `Finset.range (n+1)`, hence give continuity
coordinate by coordinate) — together with
`Algebra.TopologicallyFG ℤ (𝕎 k)`.  Note the bundle needs NEITHER
`Algebra ℤ_[p] (𝕎 k)` NOR `ResidueField (𝕎 k) ≃+* k`, only a FINITE
residue field; an earlier version of this note said otherwise and was
wrong.  `TaylorWilesCoefficients.padicInt` witnesses that the bundle is
INHABITED, so the leaf is not vacuously unstatable.

# RE-OPENED 2026-07-26 — THE PREVIOUS DISCHARGE WAS CIRCULAR IN SUBSTANCE

**This leaf was PROVEN on 2026-07-26 and has been deliberately restated
and re-sorried.  The proof was correct and the vacuity doctrine
sanctioned it; the defect was at the CUT level, and it is worth
recording in full so nobody re-derives it.**

What the proof did.  The hypothesis package contained an irreducible
hardly ramified `ρbar` over `ℚ`, which the tree refutes for every odd
prime: at `p = 3` through `IsHardlyRamified.mod_three_reducible`
(`ModThree.lean`) and `Slop.OddRep.isIrreducible_iff_forall`; at
`p ≥ 5` through `not_isIrreducible_of_isHardlyRamified_of_five_le`
(`Modularity/KhareWintenberger.lean`).  `Odd p` plus `p.Prime` leaves no
third case, so both this leaf and its sibling `exists_taylorWilesLevelRaw`
were discharged from `False`, with every unconsumed hypothesis
underscored and a vacuity audit recorded.

Why that had to be reversed.  These two are the ONLY arithmetic inputs
of `exists_taylorWilesTower`, so the whole Taylor–Wiles patching stack
of this module asserted nothing beyond `ModThree.lean` and
`KhareWintenberger.lean`.  And
`not_isIrreducible_of_isHardlyRamified_of_five_le` is itself an OPEN
leaf whose eventual proof runs THROUGH modularity lifting — that is,
through patching.  Discharging the patching leaves from it proves
patching from its own consequence.  Lean cannot see this: the build
stays green and `#print axioms` stays honest, because the dependency is
in the intended proof of an open leaf, not in any elaborated term.  Only
a human reading catches it.

**The vacuity doctrine is NOT repealed.**  It is right in general —
nobody should spend a cycle proving something unsatisfiable.  It goes
wrong at exactly this spot, where the refuting fact is DOWNSTREAM of the
thing being discharged.

# THE REPAIR: WHAT CHANGED IN THE STATEMENT

`hρbar : IsHardlyRamified hpodd hW ρbar` has been replaced by
`hres : IsTaylorWilesResidual hpodd hW ρbar` (defined immediately above): the
determinant is the cyclotomic character, and `ρbar` is unramified
outside `{2, p}`.  The two dropped fields — `isFlat` at `p` and
`isTameAtTwo` — are precisely the ones the two refutations consume, and
the Taylor–Wiles method does not use them: the local conditions enter
only through the deformation problem, which this leaf receives
abstractly through `hfact : IsWeaklyUniversalDeformation`.  `hirr` is
KEPT, because residual irreducibility is a genuine Taylor–Wiles input
(representability, and Diamond's freeness certificate) and dropping it
would risk making the leaf false — which is worse than leaving it open.

So the statement is now formally STRONGER on the residual side and the
odd-prime dichotomy can no longer reach it.  The strengthening is
classically empty: `hρT` still says `ρT` is hardly ramified over `T` and
`hred` still says it reduces to `ρbar`, so every `ρbar` this leaf is
ever applied to is hardly ramified in fact.  What the leaf has lost is
only the ability to HELP ITSELF to that fact.

**CIRCULARITY GUARD — read this before attempting a proof.**  The
following are BANNED as inputs to this leaf and to
`exists_taylorWilesLevelRaw`, whatever route reaches them:

* `not_isIrreducible_of_isHardlyRamified_of_five_le` and anything that
  consumes it;
* `IsHardlyRamified.mod_three_reducible` and
  `Slop.OddRep.isIrreducible_iff_forall` used to contradict `hirr`;
* any lemma deriving `IsHardlyRamified hpodd hW ρbar` from `hρT`/`hρuniv`
  by reduction-descent, which would restore the dichotomy through the
  back door;
* `Family.lean` and anything downstream of it (the inherited pillar-3b
  guard).

A proof of this leaf must construct the auxiliary deformation ring and
Hecke module of the Taylor–Wiles construction.  If it instead ends in
`exfalso`, it is the circular discharge again and must be rejected.

# DECOMPOSED 2026-07-27 — THIS IS NOW A PROVEN ASSEMBLY OVER TWO LEAVES

The body below is complete: it constructs the level-`0` raw datum from
the two halves of the bottom level, which are the new sorry nodes.

* **`exists_taylorWilesBottomPresentation`** (RING half): the coefficient
  ring `𝒪 = W(k)` as a `TaylorWilesCoefficients`, the Taylor–Wiles number
  `q`, and a `q`-generator power-series presentation of `Runiv` over `𝒪`
  in a universe-`0` model.  This carries the Witt-vector obligation the
  REPAIR block above records as owed, Mazur's tangent-space bound, and
  the Type-0 note of `exists_taylorWilesTower`.
* **`exists_taylorWilesBottomHeckeModule`** (MODULE half): the bottom
  Hecke module `M₀`, nontrivial over `T`, `Λ`-free of rank `d` through
  the augmentation `Λ ↠ Λ/𝔫`, and — since 2026-07-27 — pinned by
  `M₀ ≃ₗ[T] T²`.  **PROVEN, and still VACUOUS**: read its VACUITY AUDIT.
  The vacuity is a property the present leaf already had, which the split
  makes visible rather than introduces, and which NO statement in that
  vocabulary can remove (multiplicity one determines `M₀` up to
  isomorphism from `(T, ρT)`, and both are hypotheses there).  What the
  pin removes is the SOUNDNESS hazard: an unpinned `M₀` can make the
  sibling `exists_taylorWilesAuxLevelData` false.  §4 of that audit
  records the propagation still owed, here and in the sibling, which has
  a separate owner.

What the assembly proves, so that neither leaf has to: at `Q = ∅` the
deformation ring IS `Runiv`, so `toRuniv` is the isomorphism supplied by
the ring half and `diamond` is `Λ ↠ ℤ_p → Runiv`, whence
`ker toRuniv = ⊥ = 𝔫·R` (the diamond map kills every variable);
`bIdeal := 𝔫`, for which `bIdeal_le` is vacuous (`𝔪^0 = ⊤`) and
`bIdeal_le_aug` is `le_refl`; `projM` is the identity, so
`projM_surjective` and the control theorem `projM_eq_zero` are trivial
and `projM_smul` is the definition of the `Runiv`-action through `ψ`;
and `diamond_smul` is `hψalg` applied to the augmentation action.

Two hypotheses of this leaf are deliberately NOT threaded into either
half, and Lean's `unusedVariables` linter says so: `hψπ` and `hψ`.  They
pin `ψ` against `π` and against the Frobenius traces of `ρuniv`/`ρT`, and
at `Q = ∅` no field of the bottom datum sees them — `projM` is the
identity and `projM_smul` is the definition of the `Runiv`-action.  They
ARE consumed at the auxiliary levels, where they reach
`exists_taylorWilesAuxLevelData`.  Threading them here would mean giving
the module half the whole deformation-side package for nothing, so the
two warnings are accepted as the honest signal that the bottom level does
not need them.
-/
theorem exists_taylorWilesBottomLevel.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
    ∃ (q d : ℕ) (coeff : TaylorWilesCoefficients) (M0 : Type)
      (_ : AddCommGroup M0) (_ : Module T M0) (_ : Nontrivial M0),
      q0 ≤ q ∧
      Nonempty (M0 ≃ₗ[T] (Fin 2 → T)) ∧
      Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0) := by
  classical
  -- LEAF B1 (`exists_taylorWilesBottomPresentation`): the coefficient
  -- ring `𝒪 = W(k)`, the Taylor–Wiles number `q`, and the `q`-generator
  -- presentation of `Runiv` over `𝒪` in a universe-`0` model.
  -- `hq0q : q0 ≤ q` is the Taylor–Wiles padding bound; it is propagated
  -- into this leaf's conclusion so the auxiliary levels can consume it.
  obtain ⟨q, hq0q, coeff, R, instR, pres, hpres, ⟨eR⟩⟩ :=
    exists_taylorWilesBottomPresentation.{s, t, uK, uW, uR} hpodd hW hres hirr
      hadic hcomplete hranku hρuniv hπuniv hunivred hfact q0 hTWq
  -- LEAF B2 (`exists_taylorWilesBottomHeckeModule`): the bottom Hecke
  -- module `M₀ = H¹(X₀(N), ℤ_p)_𝔪`, `Λ`-free of rank `d` through the
  -- augmentation.
  -- (the multiplicity-one pin `M₀ ≃ₗ[T] T²` is `hM0T`; it is PROPAGATED
  -- into this leaf's own conclusion and threaded down the tower, which is
  -- step 1 of the repair §4 of that leaf's VACUITY AUDIT records)
  obtain ⟨d, M0, instM0add, instM0T, instM0nt, instM0L, haug, hM0T, ⟨coord⟩⟩ :=
    exists_taylorWilesBottomHeckeModule.{s, uK, uW} hpodd hW hres hirr hrankT
      hρT hπ hred q
  -- The level-`0` deformation ring is `Runiv` itself, acting on `M₀`
  -- through `ψ`; the diamond map kills `𝔫` (at `Q = ∅` the diamond group
  -- is trivial), so it is `Λ ↠ ℤ_p → Runiv`.
  letI : Module R M0 := Module.compHom M0 (ψ.comp eR.toRingHom)
  have hRsmul : ∀ (x : R) (m : M0), x • m = ψ (eR x) • m := fun _ _ => rfl
  refine ⟨q, d, coeff, M0, instM0add, instM0T, instM0nt, hq0q, hM0T, ⟨?_⟩⟩
  refine { R := R
           commRingR := instR
           pres := pres
           pres_surjective := hpres
           diamond := eR.symm.toRingHom.comp
             ((algebraMap ℤ_[p] Runiv).comp
               (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])))
           toRuniv := eR.toRingHom
           toRuniv_surjective := eR.surjective
           ker_toRuniv := ?_
           M := M0
           addCommGroupM := instM0add
           moduleRM := inferInstance
           moduleCoeffM := instM0L
           diamond_smul := ?_
           bIdeal := taylorWilesAug p q
           bIdeal_le := ?_
           bIdeal_le_aug := le_refl _
           coordM := ⟨coord⟩
           projM := AddMonoidHom.id M0
           projM_surjective := Function.surjective_id
           projM_smul := ?_
           projM_eq_zero := ?_ }
  · -- `ker toRuniv = 𝔫 · R`: both sides are `⊥`, since `toRuniv` is an
    -- isomorphism and `diamond` kills every variable.
    have hmap : (taylorWilesAug p q).map (eR.symm.toRingHom.comp
        ((algebraMap ℤ_[p] Runiv).comp
          (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p])))) = ⊥ := by
      unfold taylorWilesAug
      rw [Ideal.map_span]
      refine le_antisymm ?_ bot_le
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      simp
    rw [hmap]
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_bot]
    exact ⟨fun hx => by simpa using congrArg eR.symm hx, fun hx => by simp [hx]⟩
  · -- `diamond_smul`: the `Λ`-action on `M₀` is the augmentation action,
    -- which is the `R`-action along `diamond` because of `hψalg`.
    intro x m
    have hz : ψ ((algebraMap ℤ_[p] Runiv)
        (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x)) =
        algebraMap ℤ_[p] T
          (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x) := by
      rw [← hψalg]; rfl
    have hsym : eR (eR.symm.toRingHom ((algebraMap ℤ_[p] Runiv)
        (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x))) =
        (algebraMap ℤ_[p] Runiv)
          (MvPowerSeries.constantCoeff (σ := Fin q) (R := ℤ_[p]) x) :=
      eR.apply_symm_apply _
    rw [haug x m, hRsmul]
    simp only [RingHom.coe_comp, Function.comp_apply, hsym, hz]
  · -- `bIdeal_le` is vacuous at the bottom level (`𝔪^0 = ⊤`).
    simp
  · -- `projM_smul`: the bottom control map is the identity.
    intro x m
    simp only [AddMonoidHom.id_apply]
    exact hRsmul x m
  · -- `projM_eq_zero`: the control theorem is trivial at level `0`.
    intro m hm
    simp only [AddMonoidHom.id_apply] at hm
    subst hm
    exact Submodule.zero_mem _

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
   which is the `q` fixed by the bottom leaf.  Since 2026-07-27 `hTWq`
   supplies sets satisfying the dual-Selmer clause too — it is
   `exists_taylorWilesPrimeSet`, again sorry-free since 2026-07-27 over
   the two leaves `finite_h1TwistUnramified` and
   `exists_taylorWilesPrime_locResDecomp_ne_zero` — so what is internal here is
   only the choice of size and level, made against `hq0 : q0 ≤ q`.
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

# FORMAL-CONTENT AUDIT (2026-07-25) — THE LEVEL-WISE CUT WAS DEFECTIVE; REPAIRED 2026-07-26

**Ingredients 1–4 above record the INTENDED content; the proof below
carries NONE of it.**  The statement as cut on 2026-07-25 was NOT
provable from its named inputs, and for a bottom datum with `p`-power
torsion `M₀` it was outright FALSE.  Write `Λ = MvPowerSeries (Fin q) ℤ_[p]`,
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
`ℤ_p`-free).  **CUT REPAIR, MADE 2026-07-26**: the field
`bIdeal_le_aug : bIdeal ≤ taylorWilesAug p q` was added to
`TaylorWilesLevelRaw` (and to `TaylorWilesLevel`, where the same
computation applies; `nonempty_taylorWilesLevel_of_raw` carries it
across).  It holds for the intended objects at every level, it is what
makes `M₀ ≅ ℤ_p^d` visible to this leaf, and with it the statement
stops being false — while remaining genuinely arithmetic, since the
ring side (a `q`-generator quotient `R` of `Λ` carrying a `Λ`-algebra
structure with `ker diamond ⊆ 𝔪^n` and `R/𝔫R ≅ Runiv`) is still not
derivable from `hbot`.

Note this defect is INDEPENDENT of the residual-field obstruction
recorded at `exists_taylorWilesBottomLevel` above, which hit this leaf
identically and was repaired the same day by route (b) — the
presentation ring of `pres` is now `MvPowerSeries (Fin q) coeff.carrier`
for a `TaylorWilesCoefficients` supplied by the bottom leaf, so this
leaf no longer forces `k ≃+* ZMod p` either.  Both defects are fixed;
what remains open here is the arithmetic of ingredients 1–4.

# RE-OPENED 2026-07-26 — SAME CIRCULAR DISCHARGE AS THE BOTTOM LEAF

This leaf was PROVEN on 2026-07-26 by the odd-prime dichotomy, from the
emptiness of a hypothesis package containing an irreducible hardly
ramified `ρbar` over `ℚ`, and has been deliberately restated and
re-sorried.  The full account — what the proof did, why it is circular
in substance even though Lean cannot see it, and why the vacuity
doctrine is not being repealed — is recorded once, in the RE-OPENING
section of `exists_taylorWilesBottomLevel` above.  Read it there.

The statement change is the same one: `hρbar : IsHardlyRamified hpodd
hW ρbar` has become `hres : IsTaylorWilesResidual hpodd hW ρbar`, keeping the
cyclotomic determinant and unramifiedness outside `{2, p}` and dropping
`isFlat` and `isTameAtTwo`, which are exactly what the two refutations
consume and what the Taylor–Wiles method does not use.  `hirr` is kept.
The underscore prefixes have been removed from the hypotheses, since
the intended proof consumes all of them.

**CIRCULARITY GUARD.**  Identical to the bottom leaf's, and it is the
operative constraint here: `not_isIrreducible_of_isHardlyRamified_of_five_le`,
`IsHardlyRamified.mod_three_reducible` against `hirr`, any
reduction-descent lemma producing `IsHardlyRamified hpodd hW ρbar` from
`hρT`/`hρuniv`, and `Family.lean` with everything downstream of it, are
all banned as inputs.  A proof that ends in `exfalso` is the circular
discharge again and must be rejected.

Both-ways audit: at the intended instantiation ingredients 1–4 are the
cited Taylor–Wiles construction.  The hypothesis package is no longer
the classically unsatisfiable one — `ρbar` is now only required to be
irreducible, odd and unramified outside `{2, p}`, which real residual
representations satisfy — so the statement is not classically true
outright and carries the arithmetic listed above.

# DECOMPOSED 2026-07-27 — THIS IS NOW A PROVEN ASSEMBLY OVER TWO LEAVES

The body below is complete.  It does two things and leaves the rest to
the arithmetic leaf:

* it THREADS ingredient 1's supply `hTWq` (with its bound `hq0 : q0 ≤ q`)
  down to the arithmetic leaf rather than consuming it.  **Until
  2026-07-27 it made the choice here** — `obtain ⟨Q, hQcard, hQ⟩ :=
  hTWq q n` — and handed the leaf a FIXED `Q`, with a comment claiming
  the leaf could still "re-choose within the same supply".  It could not:
  `hTWq` was not among its hypotheses, so the choice was final and the
  leaf was quantified over prime sets the Taylor–Wiles method does not
  work for.  The choice now happens inside the leaf, against a predicate
  that carries the dual-Selmer clause;
* it fixes the SHAPE of the level ideal.  Instead of an arbitrary
  `bIdeal : Ideal Λ` the arithmetic leaf now produces only the exponent
  vector `e : Fin q → ℕ` with `∀ i, n ≤ e i` — classically
  `e i = v_p(q_i − 1)` — and `bIdeal` is `taylorWilesLevelIdeal p e`,
  generated by `(1 + S_i)^{p^{e_i}} − 1`.  Both `bIdeal` bounds are then
  discharged here: `bIdeal_le` by
  `taylorWilesLevelIdeal_le_maximalIdeal_pow` and `bIdeal_le_aug` by
  `taylorWilesLevelIdeal_le_aug`, BOTH of which are PROVEN unconditionally
  (the first was still a sorry node when this note was first written; it was
  closed the same day).  Both now live in `Modularity/PatchingCore.lean`,
  hoisted there 2026-07-27 so that the `F`-level twin of this cut can reuse
  them; see the note at the hoist site above.

Pinning the ideal is what keeps the remaining leaf faithful: an
abstract `𝔟` constrained only by `𝔟 ≤ 𝔪^n` and `𝔟 ≤ 𝔫` is satisfied by
`⊥`, over which no finite Hecke module is free — so a cut handing an
under-determined ideal to the module side would plant a FALSE sub-leaf.
For the same reason the ring and the module are NOT split from each
other; see the design note in `exists_taylorWilesBottomLevel` and the
docstring of `exists_taylorWilesAuxLevelData`.

The remaining arithmetic — ingredients 2, 3, 4 and the level-`n` half of
ingredient 5 — is **`exists_taylorWilesAuxLevelData`**. -/
theorem exists_taylorWilesLevelRaw.{s, t, uK, uW, uR}
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {k : Type uK} [Field k] [Finite k] [Algebra ℤ_[p] k]
    [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
    {W : Type uW} [AddCommGroup W] [Module k W] [Module.Finite k W]
    [Module.Free k W]
    (hW : Module.rank k W = 2) {ρbar : GaloisRep ℚ k W}
    (hres : IsTaylorWilesResidual hpodd hW ρbar)
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q)
    (q d : ℕ) (hq0 : q0 ≤ q) (coeff : TaylorWilesCoefficients)
    (M0 : Type) [AddCommGroup M0] [Module T M0]
    (hM0 : Nontrivial M0)
    (hbot : Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d 0 coeff M0))
    (hM0T : Nonempty (M0 ≃ₗ[T] (Fin 2 → T)))
    (n : ℕ) :
    Nonempty (TaylorWilesLevelRaw.{0, 0, 0, s, uR} p ψ q d n coeff M0) := by
  classical
  -- LEAF A2 (`exists_taylorWilesAuxLevelData`): ingredients 2–4 and the
  -- level-`n` half of ingredient 5.  Ingredient 1's prime-set CHOICE is
  -- made inside that leaf, not here: the supply `hTWq` is handed down
  -- rather than consumed, because the cohomological sharpening
  -- (dual-Selmer vanishing) is the leaf's own business and a set chosen
  -- here would arrive there fixed, with nothing to re-choose from.  See
  -- the INTERFACE REPAIR section of
  -- `exists_taylorWilesAuxLevelPresentedDatum`.
  obtain ⟨e, he, R, instR, pres, diamond, toRuniv, M, instMadd, instMR, instML,
    projM, hpres, htoRuniv, hker, hdsmul, ⟨coord⟩, hprojsurj, hprojsmul,
    hprojzero⟩ :=
    exists_taylorWilesAuxLevelData.{s, t, uK, uW, uR} hpodd hW hres hirr hadic
      hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred ψ hψalg
      hψπ hψ q0 hTWq q d hq0 coeff M0 hM0 hbot hM0T n
  -- The two level-ideal bounds are discharged off the arithmetic leaf,
  -- from the explicit shape of `𝔟_n`.
  exact ⟨{ R := R
           commRingR := instR
           pres := pres
           pres_surjective := hpres
           diamond := diamond
           toRuniv := toRuniv
           toRuniv_surjective := htoRuniv
           ker_toRuniv := hker
           M := M
           addCommGroupM := instMadd
           moduleRM := instMR
           moduleCoeffM := instML
           diamond_smul := hdsmul
           bIdeal := taylorWilesLevelIdeal p e
           bIdeal_le := taylorWilesLevelIdeal_le_maximalIdeal_pow p e he
           bIdeal_le_aug := taylorWilesLevelIdeal_le_aug p e
           coordM := ⟨coord⟩
           projM := projM
           projM_surjective := hprojsurj
           projM_smul := hprojsmul
           projM_eq_zero := hprojzero }⟩

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

# STATUS OF THE ARITHMETIC INPUTS (2026-07-26)

**Both arithmetic inputs of this assembly are GENUINELY OPEN.**  They
were briefly proven — on 2026-07-26, by the odd-prime dichotomy, from
the emptiness of a hypothesis package containing an irreducible hardly
ramified `ρbar` over `ℚ` — and were deliberately restated and
re-sorried the same day, because that discharge is circular in
substance: `not_isIrreducible_of_isHardlyRamified_of_five_le` is itself
an open leaf whose intended proof runs through modularity lifting, i.e.
through patching.  The full account is in the RE-OPENING section of
`exists_taylorWilesBottomLevel`.

So this theorem is a PROVEN assembly over two OPEN leaves, and the
Taylor–Wiles patching stack of this module is once again carrying its
own arithmetic rather than borrowing it from `ModThree.lean` and
`KhareWintenberger.lean`.  Anything reading a claim that the tower is
discharged is reading a stale note.

What the assembly now does at the leaf interface: it derives
`hres : IsTaylorWilesResidual hpodd hW ρbar` from `hρbar` (the two structure
projections `det` and `isUnramified`) and passes THAT, not `hρbar`, to
both leaves — so neither leaf can see the `isFlat`/`isTameAtTwo` fields
that the odd-prime refutations consume.

Both-ways audit: at the intended instantiation this is the cited
tower.  The hypothesis set of THIS theorem still contains the
classically unsatisfiable irreducible hardly ramified `ρbar` (section
audit of `Interface.lean`), so this statement is still classically true
outright — but it is PROVEN by the assembly, so nobody will be
dispatched at it, and its leaves no longer share that defect.
CIRCULARITY GUARD (inherited from pillar 3b): must not be proven
through `Family.lean` or anything downstream of it, and — added
2026-07-26 — must not be re-proven by the odd-prime dichotomy, which
would reintroduce at this node exactly the circularity just removed
from its leaves. -/
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
    (q0 : ℕ)
    (hTWq : ∀ r n : ℕ, q0 ≤ r → ∃ Q : Finset ℕ,
      Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
    Nonempty (TaylorWilesTower.{0, 0, 0, s, uR} p ψ) := by
  -- the two arithmetic leaves take only the Taylor–Wiles residual input,
  -- not the full hardly ramified package (see their RE-OPENING sections)
  have hres : IsTaylorWilesResidual hpodd hW ρbar :=
    ⟨hρbar.det, fun q hq h2 hpne => hρbar.isUnramified q hq ⟨h2, hpne⟩⟩
  obtain ⟨q, d, coeff, M0, iAG, iMod, iNt, hq0, hM0T, hbot⟩ :=
    exists_taylorWilesBottomLevel.{s, t, uK, uW, uR} hpodd hW hres hirr
      hadic hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred
      ψ hψalg hψπ hψ q0 hTWq
  letI := iAG
  letI := iMod
  exact ⟨{ q := q
           d := d
           coeff := coeff
           M0 := M0
           addCommGroupM0 := iAG
           moduleM0 := iMod
           nontrivialM0 := iNt
           level := fun n =>
             (nonempty_taylorWilesLevel_of_raw iNt
               (exists_taylorWilesLevelRaw.{s, t, uK, uW, uR} hpodd hW hres
                 hirr hadic hcomplete hranku hρuniv hπuniv hunivred hfact
                 hrankT hρT hπ hred ψ hψalg hψπ hψ q0 hTWq q d hq0 coeff M0
                 iNt hbot hM0T n).some).some }⟩

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
    (hTW : ∃ q0 : ℕ, ∀ n r : ℕ, q0 ≤ r →
      ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
    Nonempty (TaylorWilesSystem.{0, 0, 0, s, uR} p ψ) := by
  classical
  obtain ⟨q0, hTWq⟩ := exists_taylorWilesPrimeSet_card_eq p ρbar hTW
  obtain ⟨tw⟩ := exists_taylorWilesTower.{s, t, uK, uW, uR} hpodd hW hρbar hirr
    hadic hcomplete hranku hρuniv hπuniv hunivred hfact hrankT hρT hπ hred
    ψ hψalg hψπ hψ q0 hTWq
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
           coeff := tw.coeff
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
    (hTW : ∃ q0 : ℕ, ∀ n r : ℕ, q0 ≤ r →
      ∃ Q : Finset ℕ, Q.card = r ∧ IsTaylorWilesPrimeSet p ρbar n Q) :
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
